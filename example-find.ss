;;; example-find.ss — a higher-order, recursive list function with a Maybe result,
;;; proved for ALL inputs by z3 via the (plutuss compile) UPLC->SMT symbolic compiler.
;;;
;;;   find :: (a -> Bool) -> [a] -> Maybe a       -- first element satisfying p,
;;;   find p []        = Nothing                  --   or Nothing
;;;   find p (x:xs)    = if p x then Just x else find p xs
;;;
;;; List and Maybe use the SOP encoding (UPLC `constr`/`case`), NOT the Data
;;; encoding, because the symbolic compiler takes a `case` on a concrete `constr`
;;; directly, and keeps symbolic branches as guarded outcomes. This compiles a
;;; symbolic predicate over a concrete list spine into SMT conditions that z3
;;; discharges.
;;;
;;; This is the v2 port, built FFI-free (a tiny name->de-Bruijn helper; no
;;; parser/DSL, so no native crypto is loaded).
;;;
;;; Run:  chez --script example-find.ss

(import (chezscheme))
(library-directories (list "src"))
(import (plutuss smt) (plutuss compile))

;;; ---- name -> de-Bruijn term builder (FFI-free) ------------------------------
;; Named terms: a bare symbol is a variable; (lam x B); (app F A ...); (force T);
;; (delay T); (blt name); (int n)/(bool b); (constr tag E ...); (kase S A ...); err.
(define (idx name scope)
  (let loop ((s scope) (i 0))
    (cond ((null? s) (error 'n->db "unbound variable" name))
          ((eq? (car s) name) i) (else (loop (cdr s) (fx+ i 1))))))
(define (n->db t scope)
  (cond
   ((symbol? t) (vector 'var (fx+ 1 (idx t scope))))
   ((not (pair? t)) (error 'n->db "bad term" t))
   (else
    (case (car t)
      ((lam) (vector 'lam '_ (n->db (caddr t) (cons (cadr t) scope))))
      ((app) (let loop ((acc (n->db (cadr t) scope)) (as (cddr t)))
               (if (null? as) acc (loop (vector 'app acc (n->db (car as) scope)) (cdr as)))))
      ((force) (vector 'force (n->db (cadr t) scope)))
      ((delay) (vector 'delay (n->db (cadr t) scope)))
      ((blt) (vector 'builtin (cadr t)))
      ((int) (vector 'con (cons 'integer (cadr t))))
      ((bool) (vector 'con (cons 'bool (cadr t))))
      ((constr) (vector 'constr (cadr t) (map (lambda (e) (n->db e scope)) (cddr t))))
      ((kase) (vector 'case (n->db (cadr t) scope) (map (lambda (e) (n->db e scope)) (cddr t))))
      ((err) (vector 'uerror))
      (else (error 'n->db "bad form" t))))))

;; Compile a body whose free variables are `names` (names[0] = Var 1), bound as
;; symbolic integer inputs, and run `goal` through z3, returning the verdict.
(define (open-run fuel names body goal)
  (let* ((wrapped (fold-left (lambda (acc nm) (list 'lam nm acc)) body names))
         (db (let loop ((t (n->db wrapped '())) (k (length names)))
               (if (fx=? k 0) t (loop (vector-ref t 2) (fx- k 1)))))
         (inputs (map (lambda (nm) (cons (symbol->string nm) 'integer)) names))
         (c (uplc-symbolic-compile fuel inputs db)))
    (verdict (run-z3 (compiled->smtlib c goal)))))

;;; ---- z3 verdict -------------------------------------------------------------
(define (split-lines s)
  (let ((n (string-length s)))
    (let loop ((i 0) (start 0) (acc '()))
      (cond ((fx=? i n) (reverse (cons (substring s start i) acc)))
            ((char=? (string-ref s i) #\newline) (loop (fx+ i 1) (fx+ i 1) (cons (substring s start i) acc)))
            (else (loop (fx+ i 1) start acc))))))
(define (trim s)
  (let ((n (string-length s)))
    (let l ((i 0) (j n))
      (cond ((and (fx<? i j) (char-whitespace? (string-ref s i))) (l (fx+ i 1) j))
            ((and (fx<? i j) (char-whitespace? (string-ref s (fx- j 1)))) (l i (fx- j 1)))
            (else (substring s i j))))))
(define (has-substr? hay needle)
  (let ((hn (string-length hay)) (nn (string-length needle)))
    (let loop ((i 0))
      (cond ((fx>? (fx+ i nn) hn) #f)
            ((string=? (substring hay i (fx+ i nn)) needle) #t) (else (loop (fx+ i 1)))))))
(define (line-after lines target)
  (cond ((null? lines) "") ((string=? (car lines) target) (if (null? (cdr lines)) "" (cadr lines)))
        (else (line-after (cdr lines) target))))
(define (verdict z3out)
  (let ((lines (map trim (split-lines z3out))))
    (cond ((member "unsat" lines) 'proved)
          ((member "sat" lines) 'counterexample) (else 'unknown))))

;;; ---- SOP datatypes: List (Nil | Cons head tail), Maybe (Nothing | Just value) =
(define mk-nil '(constr 0))
(define (mk-cons h t) `(constr 1 ,h ,t))
(define mk-nothing '(constr 0))
(define (mk-just v) `(constr 1 ,v))
;; matchMaybe m  [Nothing -> nothingB] [Just v -> justFn]   (justFn binds the field)
(define (match-maybe m nothingB justFn) `(kase ,m ,nothingB ,justFn))
;; lazy if over Bool: lite c e t = case c [False -> t, True -> e]
(define (lite c e t) `(kase ,c ,t ,e))

;;; ---- building blocks --------------------------------------------------------
;; call-by-value one-arg Z combinator
(define zfix
  '(lam f (app (lam h (app f (lam a (app (app h h) a))))
               (lam h (app f (lam a (app (app h h) a)))))))
;; find p = Z (λself. λxs. case xs [Nil -> Nothing] [Cons h t -> if p h then Just h else self t])
(define (find-of p)
  `(app ,zfix
        (lam self
          (lam xs
            (kase xs
              ,mk-nothing                                ; Nil      -> Nothing
              (lam h (lam t ,(lite `(app ,p h)           ; Cons h t -> if p h
                                   (mk-just 'h)          ;   then Just h
                                   '(app self t)))))))))  ;   else find p t
;; the predicate (== x): λy. y == x   (x free; supplied as a symbolic input)
(define pred-eq-x '(lam y (app (blt equalsInteger) y x)))

;;; ---- the prover harness -----------------------------------------------------
(define passes 0) (define fails 0)
(define (prove title names body expected)
  (let ((got (open-run 1000 names body (lambda (r) (goal-returns-bool r #f)))))
    (cond ((eq? got expected) (set! passes (+ passes 1)) (printf "  [ ok ] ~a  => ~a\n" title got))
          (else (set! fails (+ fails 1)) (printf "  [FAIL] ~a  => got ~a, expected ~a\n" title got expected)))))

(display "find :: (a -> Bool) -> [a] -> Maybe a   over ALL inputs (refute \"returns false\")\n")
(display (make-string 72 #\-)) (newline)

;; (1) forall x. find (==x) [] == Nothing
;;     matchMaybe (find (==x) []) [Nothing -> True, Just _ -> False]; refute false => proved.
(prove "(1) forall x.  find (==x) [] == Nothing"
       '(x)
       (match-maybe `(app ,(find-of pred-eq-x) ,mk-nil) '(bool #t) '(lam v (bool #f)))
       'proved)

;; (2) forall x. find (==x) [x] == Just x
(prove "(2) forall x.  find (==x) [x] == Just x"
       '(x)
       (match-maybe `(app ,(find-of pred-eq-x) ,(mk-cons 'x mk-nil))
                    '(bool #f) '(lam v (app (blt equalsInteger) v x)))
       'proved)

;; (3) forall a b x. find (==x) [a,b] is Just h => h == x
(prove "(3) forall a b x.  find (==x) [a,b] is Just h => h == x"
       '(a b x)
       (match-maybe `(app ,(find-of pred-eq-x) ,(mk-cons 'a (mk-cons 'b mk-nil)))
                    '(bool #t) '(lam v (app (blt equalsInteger) v x)))
       'proved)

;; (4) forall a x. find (==x) [a] is always Just   (FALSE: counterexample a != x)
(prove "(4) forall a x.  find (==x) [a] is always Just   (FALSE)"
       '(a x)
       (match-maybe `(app ,(find-of pred-eq-x) ,(mk-cons 'a mk-nil))
                    '(bool #f) '(lam v (bool #t)))
       'counterexample)

(display (make-string 72 #\-)) (newline)
(printf "~a passed, ~a failed   ((1)-(3) proved for ALL inputs; (4) counterexample found)\n" passes fails)
(when (> fails 0) (exit 1))
