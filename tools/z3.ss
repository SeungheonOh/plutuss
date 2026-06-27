;;; tools/z3.ss — a direct z3 runner and a small self-checking demo of the
;;; UPLC -> SMT symbolic compiler (v2: universal value sort, three-outcome SymR).
;;;
;;; Usage:
;;;   chez --script tools/z3.ss --smt2 <file.smt2>   run z3 on a raw SMT-LIB script
;;;                                                   and print its verdict + output
;;;   chez --script tools/z3.ss --demo               compile a few example validators
;;;                                                   and check them with z3
;;;   chez --script tools/z3.ss --help
;;;
;;; The demo builds UPLC terms DIRECTLY (no parser/DSL), so it stays FFI-free and
;;; needs none of plutuss's native crypto libraries.  For the full worked suites
;;; see example-symbolic.ss, prove-sum.ss, and example-find.ss.
(import (chezscheme))
(library-directories (list "src"))
(import (plutuss smt) (plutuss compile))

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
  (let* ((raw (run-z3 (read-file file))) (tok (first-token raw)))
    (printf "verdict: ~a\n" (if (string=? tok "") "(no output)" tok))
    (display raw)))

;;; ---- demo: build a few validators directly and check them -------------------
(define (intC n) (vector 'con (cons 'integer n)))
(define (var k) (vector 'var k))
(define (bi name) (vector 'builtin name))
(define (app f a) (vector 'app f a))
(define (b2 name x y) (app (app (bi name) x) y))

(define pass 0) (define fail 0)
(define (expect-case label c goal want)
  (let ((got (z3-check (compiled->smtlib c goal))))
    (cond ((eq? got want) (set! pass (+ pass 1)) (printf "  [ ok ] ~a : ~a\n" label got))
          (else (set! fail (+ fail 1)) (printf "  [FAIL] ~a : got ~a expected ~a\n" label got want)))))

(define (demo)
  (display "=== UPLC -> SMT symbolic compiler demo (z3-backed) ===\n")
  ;; equalsInteger 10 (addInteger 5 x) = true  has a witness (x = 5)
  (expect-case "equalsInteger 10 (addInteger 5 x) = true   (sat, x=5)"
               (uplc-symbolic-compile 10 (list (cons "x" 'integer))
                 (b2 'equalsInteger (intC 10) (b2 'addInteger (intC 5) (var 1))))
               (lambda (r) (goal-returns-bool r #t)) 'sat)
  ;; 0 <= x*x  for ALL x: refute "returns false" => unsat
  (expect-case "0 <= x*x   (unsat: holds for all x)"
               (uplc-symbolic-compile 10 (list (cons "x" 'integer))
                 (b2 'lessThanEqualsInteger (intC 0) (b2 'multiplyInteger (var 1) (var 1))))
               (lambda (r) (goal-returns-bool r #f)) 'unsat)
  ;; divideInteger x y can ERROR (at y = 0): partiality is tracked, not silent
  (expect-case "divideInteger x y errors        (sat: at y=0)"
               (uplc-symbolic-compile 10 (list (cons "x" 'integer) (cons "y" 'integer))
                 (b2 'divideInteger (var 1) (var 2)))
               goal-errors 'sat)
  (printf "\n~a passed, ~a failed\n" pass fail)
  (when (> fail 0) (exit 1)))

(define (main args)
  (cond
   ((null? args) (usage) (exit 1))
   ((string=? (car args) "--demo") (demo))
   ((string=? (car args) "--smt2")
    (when (null? (cdr args)) (usage) (exit 1))
    (run-smt2 (cadr args)))
   ((or (string=? (car args) "-h") (string=? (car args) "--help")) (usage) (exit 0))
   (else (usage) (exit 1))))

(main (cdr (command-line)))
