;;; plutuss.ss — UPLC CEK evaluator CLI.
;;;
;;; Usage:
;;;   chez --script plutuss.ss [options] <file.uplc>
;;; Options:
;;;   -p, --pretty   parse and pretty-print only (no evaluation)
;;;   -b, --budget   print consumed execution budget after the result
;;;   -h, --help     show this help
;;;
;;; Output: the evaluated program, or `evaluation failure` / `parse error`.
(import (chezscheme))
(library-directories (list "src"))
(import (plutuss))

(define (usage)
  (display "Usage: chez --script plutuss.ss [options] <file>\n")
  (display "  -p/--pretty  pretty-print parsed program (no eval)\n")
  (display "  -b/--budget  print consumed budget after result\n")
  (display "  -f/--flat    emit the flat (binary) encoding as hex\n")
  (display "  -u/--unflat  decode a .flat file and print textual UPLC\n"))

(define (read-file path) (call-with-input-file path get-string-all))
(define (read-file-bytes path) (call-with-port (open-file-input-port path) get-bytevector-all))
(define (bv->hex bv)
  (let ((o (open-output-string)))
    (do ((i 0 (+ i 1))) ((= i (bytevector-length bv)) (get-output-string o))
      (let ((b (bytevector-u8-ref bv i)))
        (when (< b 16) (write-char #\0 o)) (display (number->string b 16) o)))))

(define (main args)
  (let loop ((args args) (file #f) (pretty #f) (budget #f) (flat #f) (unflat #f))
    (cond
     ((null? args)
      (unless file (usage) (exit 1))
      (cond (unflat (run-unflat file))
            (flat (run-flat file))
            (else (run file pretty budget))))
     ((or (string=? (car args) "-h") (string=? (car args) "--help")) (usage) (exit 0))
     ((or (string=? (car args) "-p") (string=? (car args) "--pretty")) (loop (cdr args) file #t budget flat unflat))
     ((or (string=? (car args) "-b") (string=? (car args) "--budget")) (loop (cdr args) file pretty #t flat unflat))
     ((or (string=? (car args) "-f") (string=? (car args) "--flat")) (loop (cdr args) file pretty budget #t unflat))
     ((or (string=? (car args) "-u") (string=? (car args) "--unflat")) (loop (cdr args) file pretty budget flat #t))
     (else (loop (cdr args) (car args) pretty budget flat unflat)))))

(define (run-flat file)
  (call/cc (lambda (k)
    (with-exception-handler
     (lambda (e) (cond ((parse-err? e) (display "parse error\n") (k (void)))
                       ((eval-fail? e) (display "evaluation failure\n") (k (void)))
                       (else (raise e))))
     (lambda ()
       (let ((p (parse-program (read-file file))))
         (display (bv->hex (flat-encode-program (vector-ref p 1) (name->debruijn (vector-ref p 2)))))
         (newline)))))))

(define (run-unflat file)
  (call-with-values (lambda () (flat-decode-program (read-file-bytes file)))
    (lambda (ver term) (display (pretty-program ver term)) (newline))))

(define (run file pretty budget)
  (let ((src (read-file file)))
    (call/cc
     (lambda (k)
       (with-exception-handler
        (lambda (e)
          (cond
           ((parse-err? e) (display "parse error\n") (k (void)))
           ((eval-fail? e) (display "evaluation failure\n") (k (void)))
           (else (raise e))))
        (lambda ()
          (let* ((prog (parse-program src))
                 (version (vector-ref prog 1)))
            (if pretty
                (begin (display (pretty-program version (name->debruijn (vector-ref prog 2)))) (newline))
                (let* ((term (name->debruijn (vector-ref prog 2)))
                       (result (machine-run term)))
                  (display (pretty-program version result)) (newline)
                  (when budget
                    (printf "({cpu: ~a\n| mem: ~a})\n"
                            (min (get-cpu-spent) i64-max) (min (get-mem-spent) i64-max))))))))))))

(main (cdr (command-line)))
