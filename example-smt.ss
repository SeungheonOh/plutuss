;;; example-smt.ss — compile a UPLC validator all the way to SMT-LIB *text*.
;;;
;;; (plutuss compile) turns a UPLC term into an `smt` value (a deep-embedded
;;; SMT expression); (plutuss smt) renders that to actual SMT-LIB.  This shows
;;; the whole pipeline: a `uplc` term  ->  compile to the success formula  ->
;;; that formula as an SMT s-expression  ->  the COMPLETE SMT-LIB script (logic
;;; + Data datatype + division preamble + const declarations + assert +
;;; check-sat) — the exact text you would pipe to z3.
;;;
;;; Run:  chez --script example-smt.ss

(import (chezscheme))
(library-directories (list "src"))
(import (plutuss smt) (plutuss compile) (plutuss dsl) (plutuss frontend))

;; Convert a closed DSL validator to de-Bruijn and strip its `k` leading input
;; lambdas, exposing the body whose free de-Bruijn vars index the symbolic
;; environment (innermost binder = Var 1 = head of make-sym-env).
(define (body-of term k)
  (let loop ((t (name->debruijn term)) (k k))
    (if (fx=? k 0) t (loop (vector-ref t 2) (fx- k 1)))))

(define (rule) (display (make-string 72 #\-)) (newline))

;; Compile `validator` (a closed term whose `k` leading lambdas are the symbolic
;; inputs bound by `env`), under precondition `pre`, and print: the success
;; formula as an SMT s-expression, the full SMT-LIB script for the negated
;; property, and z3's verdict.
(define (show title validator k env pre)
  (rule)
  (printf "~a\n" title)
  (rule)
  (let ((success (compile-success (body-of validator k) env)))
    (printf "\nsuccess formula (defined AND value), as an SMT s-expression:\n  ~a\n"
            (smt->sexpr success))
    (let ((prop (encode-property pre success)))
      (display "\nfull SMT-LIB script for the negated property  assert NOT(pre => success):\n\n")
      (display (smt->smtlib prop))
      (printf "\nz3 verdict: ~a   (unsat => the property holds for ALL inputs)\n\n"
              (z3-check prop)))))

;; Example 1:  0 <= x*x   for every integer x.
(show "0 <= x*x        (one symbolic integer input x)"
      (uplc (lam x ((builtin lessThanEqualsInteger) (con integer 0)
                    ((builtin multiplyInteger) x x))))
      1
      (make-sym-env (symbolic-input "x" smt-sort-int))
      smt-true)

;; Example 2:  (x*y)/y = x   under the precondition  y != 0.
;; Shows the floored-division preamble (pl_fdiv) being used, the definedness
;; guard divideInteger contributes, and how a precondition enters the script.
(show "(x*y)/y = x     under  y != 0   (two symbolic integer inputs x, y)"
      (uplc (lam y (lam x ((builtin equalsInteger)
                           ((builtin divideInteger)
                            ((builtin multiplyInteger) x y) y)
                           x))))
      2
      (make-sym-env (symbolic-input "x" smt-sort-int)
                    (symbolic-input "y" smt-sort-int))
      (smt-ne-zero (smt-var "y" smt-sort-int)))
