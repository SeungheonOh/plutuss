;;; tools/smt.ss — compile a UPLC validator to SMT and prove it with z3.
;;;
;;; Reads a .uplc program, strips its leading lambdas (the validator's inputs),
;;; binds each to a fresh symbolic SMT variable of a declared sort, symbolically
;;; evaluates the body via (plutuss compile), extracts the success formula
;;; `defined AND value`, and asks z3 whether the validator can ever fail to
;;; return `true`.
;;;
;;;   z3 says unsat  => the validator is defined and returns true for ALL inputs
;;;                     of the declared sorts (within the fuel-unrolled depth).
;;;   z3 says sat    => a counterexample input exists (printed with --model);
;;;                     either the validator returns false/errors there, or the
;;;                     property lies beyond the unrolled recursion depth.
;;;
;;; Usage:
;;;   chez --script tools/smt.ss [options] <file.uplc>
;;;
;;; Options:
;;;   --in SORT     declare the sort of the next leading lambda argument, in
;;;                 lambda order (outermost lambda first).  Repeatable; each --in
;;;                 strips one leading lambda.  SORT in {int bool data bytes}.
;;;   --fuel N      recursion/evaluation fuel (default 5000).
;;;   --emit        print the generated SMT-LIB script.
;;;   --no-z3       do not run z3 (implies --emit).
;;;   --model       on sat, print z3's counterexample model.
;;;   -h, --help    this help.
;;;
;;; Note: this path goes through the full UPLC parser, which loads plutuss's
;;; native crypto/BLS libraries (libsodium/secp256k1/blst) like the rest of the
;;; system.  For solver work that needs no parser, use the Scheme API in
;;; (plutuss compile) / (plutuss smt) directly, or tools/z3.ss.
(import (chezscheme))
(library-directories (list "src"))
(import (plutuss smt) (plutuss compile)
        (plutuss frontend) (plutuss output))

(define (usage)
  (display "Usage: chez --script tools/smt.ss [options] <file.uplc>\n")
  (display "  --in SORT    sort of next leading-lambda input (int|bool|data|bytes),\n")
  (display "               outermost lambda first; each --in strips one lambda\n")
  (display "  --fuel N     evaluation fuel (default 5000)\n")
  (display "  --emit       print the SMT-LIB script\n")
  (display "  --no-z3      skip z3 (implies --emit)\n")
  (display "  --model      print a counterexample model on sat\n"))

(define (read-file path) (call-with-input-file path get-string-all))

(define (sort-of-name s)
  (cond ((string=? s "int") smt-sort-int)
        ((string=? s "bool") smt-sort-bool)
        ((string=? s "data") smt-sort-data)
        ((string=? s "bytes") smt-sort-bytes)
        (else (error 'smt-tool "unknown sort (want int|bool|data|bytes)" s))))

;; strip k leading lambdas, returning the body (de-Bruijn term)
(define (strip-lams t k)
  (if (fx=? k 0) t
      (if (eq? (vector-ref t 0) 'lam)
          (strip-lams (vector-ref t 2) (fx- k 1))
          (error 'smt-tool "expected a leading lambda to bind an --in, but found" (vector-ref t 0)))))

;; Build the symbolic env for k inputs whose sorts are given outermost-first.
;; Var 1 is the innermost binder (= the LAST --in), so the env is the reverse.
(define (build-env sorts)
  (let loop ((ss sorts) (idx 0) (acc '()))
    (if (null? ss)
        acc  ; acc already innermost-first because we prepend
        (loop (cdr ss) (fx+ idx 1)
              (cons (symbolic-input (string-append "in" (number->string idx)) (car ss)) acc)))))

(define (main args)
  (let loop ((args args) (file #f) (in-sorts '()) (fuel 5000)
             (emit #f) (run #t) (model #f))
    (cond
     ((null? args)
      (unless file (usage) (exit 1))
      (do-prove file (reverse in-sorts) fuel emit run model))
     ((or (string=? (car args) "-h") (string=? (car args) "--help")) (usage) (exit 0))
     ((string=? (car args) "--in")
      (when (null? (cdr args)) (error 'smt-tool "--in needs a sort"))
      (loop (cddr args) file (cons (sort-of-name (cadr args)) in-sorts) fuel emit run model))
     ((string=? (car args) "--fuel")
      (when (null? (cdr args)) (error 'smt-tool "--fuel needs a number"))
      (loop (cddr args) file in-sorts (string->number (cadr args)) emit run model))
     ((string=? (car args) "--emit") (loop (cdr args) file in-sorts fuel #t run model))
     ((string=? (car args) "--no-z3") (loop (cdr args) file in-sorts fuel #t #f model))
     ((string=? (car args) "--model") (loop (cdr args) file in-sorts fuel emit run #t))
     (else (loop (cdr args) (car args) in-sorts fuel emit run model)))))

(define (do-prove file in-sorts fuel emit run model)
  (let* ((prog (parse-program (read-file file)))
         (named (vector-ref prog 2))
         (db (name->debruijn named))
         (body (strip-lams db (length in-sorts)))
         (env (build-env in-sorts))
         (out (compile-term body env fuel)))
    (cond
     ((not out)
      (display "compile: REFUSED — the term uses a construct outside the supported\n")
      (display "first-order fragment, or fuel was exhausted before a value.\n")
      (exit 2))
     (else
      (let ((success (extract out)))
        (cond
         ((not success)
          (display "compile: term does not reduce to a first-order (boolean) value;\n")
          (display "its result sort is not directly checkable.\n")
          (exit 2))
         (else
          (let ((prop (encode-property smt-true success)))
            (printf "success formula sort : ~a\n" (smt-sort-of success))
            (when emit
              (display "--- SMT-LIB (negated property: assert NOT(true => success)) ---\n")
              (display (smt->smtlib prop)))
            (when run
              (let ((verdict (z3-check prop)))
                (printf "z3 verdict           : ~a  " verdict)
                (case verdict
                  ((unsat) (display "=> validator is defined and returns true for ALL inputs\n"))
                  ((sat)   (display "=> a counterexample input exists\n")
                           (when model
                             (let ((m (z3-model prop)))
                               (when m (display "--- model ---\n") (display m)))))
                  (else    (display "=> z3 could not decide\n")))))))))))))

(main (cdr (command-line)))
