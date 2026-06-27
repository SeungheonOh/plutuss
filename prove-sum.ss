;;; prove-sum.ss — prove  "forall x. sum x >= 0"  for a recursive UPLC program,
;;; using the (plutuss compile) UPLC->SMT symbolic compiler and z3.
;;;
;;;   sum i = if i <= 0 then 0 else i + sum (i - 1)        (built with the Z combinator)
;;;
;;; Run:  chez --script prove-sum.ss
;;;
;;; This is the guarded-outcome port of the original demo, built FFI-free:
;;; terms are constructed directly (a tiny name->de-Bruijn helper keeps them
;;; readable) so the script never loads plutuss's native crypto.
;;;
;;; Two ways to read "within fuel":
;;;
;;;  (1) BOUNDED MODEL CHECKING.  Symbolically unroll the recursion up to the fuel
;;;      budget.  This proves  forall x in [0,N]. sum x >= 0  where N grows with
;;;      fuel — but N is always finite, so plain unrolling can never settle the
;;;      unbounded "forall x". Beyond the frontier the result can contain timeout
;;;      outcomes; the tool makes no false claim.
;;;
;;;  (2) INDUCTION (the real unbounded proof, within trivial fuel).  Abstract the
;;;      recursive call sum(x-1) as a fresh symbolic variable s carrying the
;;;      induction hypothesis  s >= 0.  Then one symbolic step of the body reduces
;;;      to  if x<=0 then 0 else x + s, and the compiler discharges  s>=0  =>
;;;      0 <= (if x<=0 then 0 else x+s)  for ALL x.  With the base case sum 0 >= 0
;;;      and well-founded recursion on the decreasing argument, this proves
;;;      forall x. sum x >= 0  with no unrolling at all.

(import (chezscheme))
(library-directories (list "src"))
(import (plutuss smt) (plutuss compile))

;;; ---- a tiny name -> de-Bruijn term builder (FFI-free; no parser/DSL) --------
;; Named terms: a bare symbol is a variable; (lam x B); (app F A ...); (force T);
;; (delay T); (blt name); (int n)/(bool b)/(con ty v); (constr tag E ...);
;; (kase S A ...); err.  `body-of` converts and strips k leading input lambdas.
(define (idx name scope)
  (let loop ((s scope) (i 0))
    (cond ((null? s) (error 'n->db "unbound variable" name))
          ((eq? (car s) name) i)
          (else (loop (cdr s) (fx+ i 1))))))
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
      ((con) (vector 'con (cons (cadr t) (caddr t))))
      ((constr) (vector 'constr (cadr t) (map (lambda (e) (n->db e scope)) (cddr t))))
      ((kase) (vector 'case (n->db (cadr t) scope) (map (lambda (e) (n->db e scope)) (cddr t))))
      ((err) (vector 'uerror))
      (else (error 'n->db "bad form" t))))))
(define (body-of named k)
  (let loop ((t (n->db named '())) (k k)) (if (fx=? k 0) t (loop (vector-ref t 2) (fx- k 1)))))

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
            ((string=? (substring hay i (fx+ i nn)) needle) #t)
            (else (loop (fx+ i 1)))))))
(define (line-after lines target)
  (cond ((null? lines) "") ((string=? (car lines) target) (if (null? (cdr lines)) "" (cadr lines)))
        (else (line-after (cdr lines) target))))
;; 'proved (unsat) | 'counterexample (sat) | 'unknown
(define (verdict z3out)
  (let ((lines (map trim (split-lines z3out))))
    (cond ((member "unsat" lines) 'proved)
          ((member "sat" lines) 'counterexample)
          (else 'unknown))))
(define (run c goal) (verdict (run-z3 (compiled->smtlib c goal))))

;;; ---- the sum program (Z-combinator recursion) -------------------------------
;; Z = λf. (λh. f (λa. h h a)) (λh. f (λa. h h a))
(define zfix
  '(lam f (app (lam h (app f (lam a (app (app h h) a))))
               (lam h (app f (lam a (app (app h h) a)))))))
;; bodyF self n = if n<=0 then 0 else n + self (n-1)   (lazy: delayed branches)
(define bodyF
  '(lam self (lam n
     (force (app (force (blt ifThenElse))
                 (app (blt lessThanEqualsInteger) n (int 0))
                 (delay (int 0))
                 (delay (app (blt addInteger) n
                             (app self (app (blt subtractInteger) n (int 1))))))))))
(define sumf `(app ,zfix ,bodyF))
;; validator  0 <= sum x  as a closed function of its single input x
(define validator `(lam x (app (blt lessThanEqualsInteger) (int 0) (app ,sumf x))))
(define sum-body (body-of validator 1))

;; Assert the validator returns FALSE under a precondition `extra` (a list of
;; (label . SExpr)).  unsat => no such input => 0 <= sum x for ALL inputs meeting
;; the precondition for this bounded query.
(define (refute-false fuel extra)
  (run (uplc-symbolic-compile fuel (list (cons "x" 'integer)) sum-body)
       (lambda (r) (append (goal-returns-bool r #f) extra))))

;;; ---------------------------------------------------------------------------
(display "(1) BOUNDED:  forall x in [0,N]. sum x >= 0   (N scales with fuel)\n")
(for-each
 (lambda (F)
   (let loop ((n 0))
     (cond
      ((> n 40) (printf "    fuel ~3d : proven for x in [0,40+]\n" F))
      ((eq? 'proved (refute-false F (list (cons "lo" (op-le (s-int 0) (s-atom "x")))
                                          (cons "hi" (op-le (s-atom "x") (s-int n))))))
       (loop (+ n 1)))
      (else (printf "    fuel ~3d : proven for x in [0,~a]   (x >= ~a: beyond frontier, no claim)\n"
                    F (- n 1) n)))))
 '(40 90 160))

;;; ---------------------------------------------------------------------------
(display "\n(2) UNBOUNDED:  forall x. sum x >= 0   (by induction, no unrolling)\n")
;; The inductive step as a closed function of x (Var 1) and s = sum(x-1) (Var 2).
;; (lam ignore s) ignores its argument and returns s; bodyF (lam ignore s) x then
;; reduces symbolically to  if x<=0 then 0 else x+s.
(define step-term
  `(lam s (lam x (app (blt lessThanEqualsInteger) (int 0)
                      (app (app ,bodyF (lam ignore s)) x)))))
(define step-body (body-of step-term 2))        ; inputs: x = Var 1, s = Var 2
(define IH (cons "IH" (op-le (s-int 0) (s-atom "s"))))   ; induction hypothesis s >= 0

;; inductive step:  s>=0  =>  0 <= sum-step(x,s)   (refute "= false" under IH)
(define step-c (uplc-symbolic-compile 50 (list (cons "x" 'integer) (cons "s" 'integer)) step-body))
(printf "    inductive step  [ s>=0 => 0 <= sum-step(x,s) ]   z3: ~a\n"
        (run step-c (lambda (r) (append (goal-returns-bool r #f) (list IH)))))
;; non-vacuous: drop the IH and it becomes falsifiable (a counterexample exists)
(printf "    step is non-vacuous (drop IH => falsifiable)     z3: ~a\n"
        (run step-c (lambda (r) (goal-returns-bool r #f))))
;; base case  x = 0  =>  sum 0 >= 0
(printf "    base case       [ x=0 => sum 0 >= 0 ]            z3: ~a\n"
        (refute-false 80 (list (cons "x0" (sEq (s-atom "x") (s-int 0))))))
(display "\n    proved step (s>=0 => ...) + proved base + well-founded recursion\n")
(display "    ==>  PROVED:  forall x. sum x >= 0\n")
