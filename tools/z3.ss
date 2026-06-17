;;; tools/z3.ss — a direct z3 runner and a self-testing demo of the
;;; UPLC -> SMT compiler.
;;;
;;; Usage:
;;;   chez --script tools/z3.ss --smt2 <file.smt2>   run z3 on a raw SMT-LIB
;;;                                                   script; print the verdict
;;;   chez --script tools/z3.ss --demo               compile a suite of example
;;;                                                   validators and prove them
;;;   chez --script tools/z3.ss --help
;;;
;;; The example validators are built with the (plutuss dsl) `uplc` macro, so this
;;; loads plutuss's native crypto libraries like the rest of the system; the
;;; (plutuss smt) and (plutuss compile) layers it exercises remain FFI-free.
(import (chezscheme))
(library-directories (list "src"))
(import (plutuss smt) (plutuss compile) (plutuss dsl) (plutuss frontend))

(define (usage)
  (display "Usage:\n")
  (display "  chez --script tools/z3.ss --smt2 <file.smt2>   run z3 on a raw script\n")
  (display "  chez --script tools/z3.ss --demo               run the compiler demo\n"))

(define (read-file path) (call-with-input-file path get-string-all))

(define (first-token s)
  (let ((n (string-length s)))
    (let skip ((i 0))
      (cond ((fx>=? i n) "")
            ((char-whitespace? (string-ref s i)) (skip (fx+ i 1)))
            (else (let loop ((j i))
                    (if (or (fx>=? j n) (char-whitespace? (string-ref s j)))
                        (substring s i j) (loop (fx+ j 1)))))))))

(define (run-smt2 file)
  (let* ((raw (run-z3 (read-file file)))
         (tok (first-token raw)))
    (printf "verdict: ~a\n" (if (string=? tok "") "(no output)" tok))
    (display raw)))

;;; ----------------------------------------------------------------------
;;; Demo: compile example validators and prove them with z3.
;;; ----------------------------------------------------------------------
;; Builtins/constants/control flow as DSL term fragments (,a splices a subterm).
(define (ci n) (uplc (con integer ,n)))
(define (cb v) (uplc (con bool ,v)))
(define (le a b)  (uplc ((builtin lessThanEqualsInteger) ,a ,b)))
(define (lt a b)  (uplc ((builtin lessThanInteger) ,a ,b)))
(define (mul a b) (uplc ((builtin multiplyInteger) ,a ,b)))
(define (add a b) (uplc ((builtin addInteger) ,a ,b)))
(define (sub a b) (uplc ((builtin subtractInteger) ,a ,b)))
(define (eqi a b) (uplc ((builtin equalsInteger) ,a ,b)))
(define (divi a b) (uplc ((builtin divideInteger) ,a ,b)))
(define (unI e)   (uplc ((builtin unIData) ,e)))
(define (lite c t e) (uplc (force ((force (builtin ifThenElse)) ,c (delay ,t) (delay ,e)))))

;; The symbolic inputs, as named free variables: x1 = Var 1, x2 = Var 2.
(define x1 (uplc x))
(define x2 (uplc y))
(define xv (smt-var "x" smt-sort-int))
(define yv (smt-var "y" smt-sort-int))
(define dv (smt-var "d" smt-sort-data))
(define symX  (make-sym-env (symbolic-input "x" smt-sort-int)))
(define symXY (make-sym-env (symbolic-input "x" smt-sort-int) (symbolic-input "y" smt-sort-int)))
(define symD  (make-sym-env (symbolic-input "d" smt-sort-data)))

;; Convert a DSL term with free input variables to the de-Bruijn body the
;; compiler expects.  `names` lists the inputs innermost-first (first = Var 1),
;; matching make-sym-env: wrap the term in one lambda per input, run the standard
;; name->debruijn, then strip those lambdas back off.
(define (body-with names t)
  (let* ((wrapped (fold-left (lambda (acc nm) (vector 'lam nm acc)) t names))
         (db (name->debruijn wrapped)))
    (let peel ((u db) (k (length names)))
      (if (fx=? k 0) u (peel (vector-ref u 2) (fx- k 1))))))

;; The demo's inputs are always x1 = Var 1 ("x") and (when present) x2 = Var 2 ("y").
(define (input-names k) (if (fx=? k 2) '("x" "y") '("x")))

(define pass-count 0)
(define fail-count 0)

;; prove that `t` (compiled in `env`, under precondition `pre`) meets `expect`
;; ('unsat = always-true ; 'sat = counterexample exists).
(define (expect-case label t env pre expect)
  (let ((s (compile-success (body-with (input-names (length env)) t) env)))
    (if (not s)
        (begin (set! fail-count (+ fail-count 1))
               (printf "  [FAIL] ~a : compile refused\n" label))
        (let ((got (z3-check (encode-property pre s))))
          (if (eq? got expect)
              (begin (set! pass-count (+ pass-count 1))
                     (printf "  [ ok ] ~a : ~a\n" label got))
              (begin (set! fail-count (+ fail-count 1))
                     (printf "  [FAIL] ~a : got ~a expected ~a\n" label got expect)))))))

;; Z-combinator recursion: sum(i) = if i<=0 then 0 else i + sum(i-1)
(define rec-bodyF
  (uplc
   (lam rec
     (lam n
       (force ((force (builtin ifThenElse))
               ((builtin lessThanEqualsInteger) n (con integer 0))
               (delay (con integer 0))
               (delay ((builtin addInteger)
                       n
                       (rec ((builtin subtractInteger) n (con integer 1)))))))))))
(define rec-zfix
  (uplc (lam f ((lam h (f (lam a (h h a)))) (lam h (f (lam a (h h a))))))))
(define rec-validator (le (ci 0) (uplc ((,rec-zfix ,rec-bodyF) ,x1))))

;; (lam a. 0 <= a*a) — reused as a directly-applied lambda and a case branch.
(define sq-nonneg (uplc (lam a ,(le (ci 0) (mul (uplc a) (uplc a))))))

(define (demo)
  (display "=== UPLC -> SMT compiler demo (z3-backed) ===\n")
  (display "Arithmetic:\n")
  (expect-case "0 <= x*x                      (always true)" (le (ci 0) (mul x1 x1)) symX smt-true 'unsat)
  (expect-case "0 <= x*x-(2x-1)  i.e. (x-1)^2  (always true)"
               (le (ci 0) (sub (mul x1 x1) (sub (add x1 x1) (ci 1)))) symX smt-true 'unsat)
  (expect-case "x < 5                         (has counterexample)" (lt x1 (ci 5)) symX smt-true 'sat)
  (display "Partiality (divideInteger guard y != 0):\n")
  (expect-case "(x*y)/y = x  | no precondition (y=0 undefined)" (eqi (divi (mul x1 x2) x2) x1) symXY smt-true 'sat)
  (expect-case "(x*y)/y = x  | y != 0          (always true)" (eqi (divi (mul x1 x2) x2) x1) symXY (smt-ne-zero yv) 'unsat)
  (display "Control flow (ifThenElse, symbolic boolean):\n")
  (expect-case "ite(0<=x, T, F) | 0<=x         (always true)"
               (lite (le (ci 0) x1) (cb #t) (cb #f)) symX (smt-bin 'le (smt-int 0) xv) 'unsat)
  (expect-case "ite(0<=x, T, F) | no pre       (has counterexample)"
               (lite (le (ci 0) x1) (cb #t) (cb #f)) symX smt-true 'sat)
  (display "Higher-order / data (lambda, constr/case, Data destructure):\n")
  (expect-case "[(lam a. 0<=a*a) x]            (always true)"
               (uplc (,sq-nonneg ,x1)) symX smt-true 'unsat)
  (expect-case "case(constr0[x]){0->0<=a*a}    (always true)"
               (uplc (case (constr 0 ,x1) ,sq-nonneg)) symX smt-true 'unsat)
  (expect-case "unI d == unI d | isI d         (always true)"
               (eqi (unI x1) (unI x1)) symD (smt-uop 'isi dv) 'unsat)
  (display "Bounded recursion (sum i = if i<=0 then 0 else i+sum(i-1)):\n")
  (expect-case "0 <= sum(i) | 0<=i<=3          (proven in unrolled range)"
               rec-validator (make-sym-env (symbolic-input "i" smt-sort-int))
               (smt-and (smt-bin 'le (smt-int 0) (smt-var "i" smt-sort-int))
                        (smt-bin 'le (smt-var "i" smt-sort-int) (smt-int 3)))
               'unsat)
  (expect-case "0 <= sum(i) | 0<=i (unbounded)  (beyond depth: no claim)"
               rec-validator (make-sym-env (symbolic-input "i" smt-sort-int))
               (smt-bin 'le (smt-int 0) (smt-var "i" smt-sort-int))
               'sat)
  (printf "\n~a passed, ~a failed\n" pass-count fail-count)
  (when (> fail-count 0) (exit 1)))

(define (main args)
  (cond
   ((null? args) (usage) (exit 1))
   ((string=? (car args) "--demo") (demo))
   ((string=? (car args) "--smt2")
    (when (null? (cdr args)) (usage) (exit 1))
    (run-smt2 (cadr args)))
   (else (usage) (exit (if (or (string=? (car args) "-h") (string=? (car args) "--help")) 0 1)))))

(main (cdr (command-line)))
