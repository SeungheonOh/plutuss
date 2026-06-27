;;; example-advanced-symbolic.ss -- richer z3-backed symbolic compiler examples.
;;;
;;; These are intentionally direct UPLC ASTs: no parser/DSL and no native crypto
;;; FFI.  Each case compiles to SMT-LIB with (plutuss compile), runs z3, and
;;; checks the expected bounded verdict.
;;;
;;; Run:  chez --script example-advanced-symbolic.ss
;;;       chez --script example-advanced-symbolic.ss --emit

(import (chezscheme))
(library-directories (list "src"))
(import (plutuss smt) (plutuss compile))

;;; ---- Direct UPLC builders -------------------------------------------------
(define (intC n)      (vector 'con (cons 'integer n)))
(define (boolC b)     (vector 'con (cons 'bool b)))
(define (bsC bytes)   (vector 'con (cons 'bytestring (u8-list->bytevector bytes))))
(define (listC ty xs) (vector 'con (cons (list 'list ty) xs)))
(define unitC         (vector 'con (cons 'unit '())))
(define (var k)       (vector 'var k))
(define (bi name)     (vector 'builtin name))
(define (app f a)     (vector 'app f a))
(define (force t)     (vector 'force t))
(define (delay t)     (vector 'delay t))
(define (lam body)    (vector 'lam '_ body))
(define (constr tag fields) (vector 'constr tag fields))
(define (kase scrut alts)   (vector 'case scrut alts))

(define (b1 b a)       (app (bi b) a))
(define (b2 b a c)     (app (app (bi b) a) c))
(define (b3 b a c d)   (app (app (app (bi b) a) c) d))
(define (fb1 b a)      (app (force (bi b)) a))
(define (fb2 b a c)    (app (app (force (bi b)) a) c))
(define (ite3 c t e)   (app (app (app (force (bi 'ifThenElse)) c) t) e))

;; Call-by-value fixed point combinator, used by the recursive examples.
(define zComb
  (let ((m (lam (app (var 2) (lam (app (app (var 2) (var 2)) (var 1)))))))
    (lam (app m m))))

(define emit? (and (> (length (command-line)) 1)
                   (string=? (cadr (command-line)) "--emit")))

;;; ---- z3 verdict -----------------------------------------------------------
(define (split-lines s)
  (let ((n (string-length s)))
    (let loop ((i 0) (start 0) (acc '()))
      (cond ((fx=? i n) (reverse (cons (substring s start i) acc)))
            ((char=? (string-ref s i) #\newline)
             (loop (fx+ i 1) (fx+ i 1) (cons (substring s start i) acc)))
            (else (loop (fx+ i 1) start acc))))))

(define (trim s)
  (let ((n (string-length s)))
    (let loop ((i 0) (j n))
      (cond ((and (fx<? i j) (char-whitespace? (string-ref s i))) (loop (fx+ i 1) j))
            ((and (fx<? i j) (char-whitespace? (string-ref s (fx- j 1)))) (loop i (fx- j 1)))
            (else (substring s i j))))))

(define (verdict z3out)
  (let ((lines (map trim (split-lines z3out))))
    (cond ((member "unsat" lines) 'unsat)
          ((member "sat" lines) 'sat)
          (else 'unknown))))

(define passes 0)
(define fails 0)
(define (demo title fuel inputs term goal expected)
  (let* ((c (uplc-symbolic-compile fuel inputs term))
         (smt (compiled->smtlib c goal)))
    (when emit?
      (printf "~a\n~a\n~a\n" (make-string 72 #\=) title (make-string 72 #\=))
      (display smt)
      (display "---- z3 ----\n"))
    (let ((got (verdict (run-z3 smt))))
      (cond ((eq? got expected)
             (set! passes (+ passes 1))
             (printf "  [ ok ] ~a  => ~a\n" title got))
            (else
             (set! fails (+ fails 1))
             (printf "  [FAIL] ~a  => got ~a, expected ~a\n" title got expected))))))

(define (with-assumptions base . assumptions)
  (lambda (r) (append (base r) assumptions)))

;;; ---- Example 1: symbolic constructor fields flow through Case --------------
;; if x < 0 then C0[x] else C1[x+x]; case both constructors with identity alts.
;; Solving for result 6 forces the else branch and x = 3.
(define ex-constr-fields
  (let ((x (var 1)))
    (kase (ite3 (b2 'lessThanInteger x (intC 0))
                (constr 0 (list x))
                (constr 1 (list (b2 'addInteger x x))))
          (list (lam (var 1)) (lam (var 1))))))

(demo "constructor fields through symbolic if/case produce 6"
      24 (list (cons "x" 'integer)) ex-constr-fields
      (lambda (r) (goal-returns-int r 6)) 'sat)

;;; ---- Example 2: Data injection/destruction round-trip ----------------------
;; Refute: unIData (iData x) differs from x.  z3 proves no counterexample.
(define ex-idata-roundtrip
  (b2 'equalsInteger (b1 'unIData (b1 'iData (var 1))) (var 1)))

(demo "forall x. unIData (iData x) == x"
      16 (list (cons "x" 'integer)) ex-idata-roundtrip
      (lambda (r) (goal-returns-bool r #f)) 'unsat)

;;; ---- Example 3: Data branch selection by chooseData ------------------------
;; chooseData (iData x) picks the integer branch, here literal 40.
;; Application order is: data, constrCase, mapCase, listCase, intCase, bytesCase.
(define ex-choose-data-int
  (app (app (app (app (app (app (force (bi 'chooseData))
                              (b1 'iData (var 1)))
                         (intC 10))
                    (intC 20))
               (intC 30))
          (intC 40))
     (intC 50)))

(demo "chooseData on iData takes the integer branch"
      16 (list (cons "x" 'integer)) ex-choose-data-int
      (lambda (r) (goal-returns-int r 40)) 'sat)

;;; ---- Example 4: bytestring sequence constraints ----------------------------
;; consByteString n tail == #[42, 1, 2] has a witness: n = 42 and tail = #[1,2].
(define ex-byte-packet
  (b2 'equalsByteString
      (b2 'consByteString (var 1) (var 2))
      (bsC '(42 1 2))))

(demo "solve a byte packet header and tail"
      18 (list (cons "n" 'integer) (cons "tail" 'bytestring)) ex-byte-packet
      (lambda (r) (goal-returns-bool r #t)) 'sat)

;; If n is outside 0..255, consByteString must error.
(demo "consByteString rejects an out-of-byte header"
      18 (list (cons "n" 'integer) (cons "tail" 'bytestring)) ex-byte-packet
      (with-assumptions goal-errors (cons "n_gt_255" (op-gt (s-atom "n") (s-int 255))))
      'sat)

;;; ---- Example 5: arrays from lists -----------------------------------------
;; listToArray [7,9,13], then indexArray i.  Solving for 13 finds i = 2.
(define const-list-ints (listC 'integer '(7 9 13)))
(define ex-array-index
  (fb2 'indexArray (fb1 'listToArray const-list-ints) (var 1)))

(demo "indexArray (listToArray [7,9,13]) i == 13"
      18 (list (cons "i" 'integer)) ex-array-index
      (lambda (r) (goal-returns-int r 13)) 'sat)

;; The same array access is out of range at i = 3.
(demo "indexArray errors exactly beyond the array length"
      18 (list (cons "i" 'integer)) ex-array-index
      (with-assumptions goal-errors (cons "i_eq_3" (sEq (s-atom "i") (s-int 3))))
      'sat)

;;; ---- Example 6: dynamic Val case dispatch ---------------------------------
;; With a symbolic Val input, `case v [false, true]` can return true.
(define ex-dyn-bool-case
  (kase (var 1) (list (boolC #f) (boolC #t))))

(demo "case over a dynamic Val can take the Bool true branch"
      18 (list (cons "v" 'anyV)) ex-dyn-bool-case
      (lambda (r) (goal-returns-bool r #t)) 'sat)

;; But if v is explicitly VBool false, returning true is impossible.
(demo "case VBool false cannot return the true branch"
      18 (list (cons "v" 'anyV)) ex-dyn-bool-case
      (with-assumptions (lambda (r) (goal-returns-bool r #t))
        (cons "v_false" (sEq (s-atom "v") (v-bool (s-bool #f)))))
      'unsat)

;;; ---- Example 7: uninterpreted hash congruence ------------------------------
;; Even with opaque hashing, congruence proves sha2_256 msg == sha2_256 msg.
(define ex-sha-refl
  (b2 'equalsByteString (b1 'sha2_256 (var 1)) (b1 'sha2_256 (var 1))))

(demo "forall msg. sha2_256 msg == sha2_256 msg"
      18 (list (cons "msg" 'bytestring)) ex-sha-refl
      (lambda (r) (goal-returns-bool r #f)) 'unsat)

;;; ---- Example 8: recursive sum needs fuel unrolling -------------------------
;; sum x = if x < 0 then 0 else x + sum (x - 1)
;;
;; Because UPLC is strict, the branches are delayed and only the selected branch
;; is forced.  Solving sum x = 15 needs the compiler to unroll through
;; x = 5,4,3,2,1,0,-1, so this is a real fuel-sensitive example.
(define sum-below-zero-F
  (lam (lam (force (ite3 (b2 'lessThanInteger (var 1) (intC 0))
                         (delay (intC 0))
                         (delay (b2 'addInteger
                                    (var 1)
                                    (app (var 2)
                                         (b2 'subtractInteger (var 1) (intC 1))))))))))

(define ex-sum-below-zero
  (app (app zComb sum-below-zero-F) (var 1)))

(demo "recursive sum x<0 base: solve sum x = 15"
      260 (list (cons "x" 'integer)) ex-sum-below-zero
      (lambda (r) (goal-returns-int r 15)) 'sat)

;; At very low fuel, some inputs are beyond the unrolled horizon.
(demo "recursive sum x<0 base: low fuel has timeout paths"
      28 (list (cons "x" 'integer)) ex-sum-below-zero
      goal-indeterminate 'sat)

(printf "\n~a passed, ~a failed\n" passes fails)
(when (> fails 0) (exit 1))
