;;; (plutuss cost) — ExMem sizing, costing algebra, the variant-E cost table,
;;; and machine step costs.  Builtin arity/force counts are declared alongside
;;; each builtin by the define-builtin macro in (plutuss builtins).
(library (plutuss cost)
  (export integer-ex-mem bytestring-ex-mem string-ex-mem size-ex-mem
          integer-costed-literally data-ex-mem data-node-count
          g1-ex-mem g2-ex-mem ml-ex-mem
          builtin-cost-fns
          machine-startup-cpu machine-startup-mem machine-step-cpu machine-step-mem)
  (import (chezscheme) (plutuss base))

  ;;; ---- ExMem sizing ----
  (define (integer-ex-mem n)
    (let ((bits (integer-length (abs n))))
      (if (fx=? bits 0) 1 (fx+ (fxquotient (fx- bits 1) 64) 1))))
  (define (bytestring-ex-mem bv)
    (let ((len (bytevector-length bv)))
      (if (fx=? len 0) 1 (fx+ (fxquotient (fx- len 1) 8) 1))))
  (define (string-ex-mem s) (fxquotient (bytevector-length (string->utf8 s)) 4))
  (define (size-ex-mem v) (if (fx<=? v 0) 0 (fx+ (fxquotient (fx- v 1) 8) 1)))
  (define (integer-costed-literally n)
    (let ((a (abs n))) (if (> a i64-max) i64-max a)))
  (define (data-ex-mem d)
    (let loop ((stack (list d)) (total 0))
      (if (null? stack) total
          (let ((cur (car stack)) (rest (cdr stack)))
            (case (car cur)
              ((Constr) (loop (append (caddr cur) rest) (fx+ total 4)))
              ((Map) (loop (fold-left (lambda (acc p) (cons (car p) (cons (cdr p) acc))) rest (cadr cur)) (fx+ total 4)))
              ((List) (loop (append (cadr cur) rest) (fx+ total 4)))
              ((I) (loop rest (fx+ total 4 (integer-ex-mem (cadr cur)))))
              ((B) (loop rest (fx+ total 4 (bytestring-ex-mem (cadr cur)))))
              (else (loop rest (fx+ total 4))))))))
  (define (data-node-count d)
    (let loop ((stack (list d)) (total 0))
      (if (null? stack) total
          (let ((cur (car stack)) (rest (cdr stack)))
            (case (car cur)
              ((Constr) (loop (append (caddr cur) rest) (fx+ total 1)))
              ((Map) (loop (fold-left (lambda (acc p) (cons (car p) (cons (cdr p) acc))) rest (cadr cur)) (fx+ total 1)))
              ((List) (loop (append (cadr cur) rest) (fx+ total 1)))
              (else (loop rest (fx+ total 1))))))))
  (define (g1-ex-mem) 18)
  (define (g2-ex-mem) 36)
  (define (ml-ex-mem) 72)

  ;;; ---- costing algebra (each cost fn is (lambda (x y z) -> i64)) ----
  (define (k-const c) (lambda (x y z) c))
  (define (k-linear i s) (lambda (x y z) (sat-add i (sat-mul s x))))
  (define (k-linear-y i s) (lambda (x y z) (sat-add i (sat-mul s y))))
  (define (k-linear-z i s) (lambda (x y z) (sat-add i (sat-mul s z))))
  (define (k-added i s) (lambda (x y z) (sat-add i (sat-mul s (sat-add x y)))))
  (define (k-subtracted i s mn) (lambda (x y z) (max mn (sat-add i (sat-mul s (- x y))))))
  (define (k-multiplied i s) (lambda (x y z) (sat-add i (sat-mul s (sat-mul x y)))))
  (define (k-min-size i s) (lambda (x y z) (sat-add i (sat-mul s (min x y)))))
  (define (k-max-size i s) (lambda (x y z) (sat-add i (sat-mul s (max x y)))))
  (define (k-linear-on-diag i s c) (lambda (x y z) (if (= x y) (sat-add i (sat-mul s x)) c)))
  (define (k-quadratic c0 c1 c2)
    (lambda (x y z) (sat-add (sat-add c0 (sat-mul c1 x)) (sat-mul c2 (sat-mul x x)))))
  (define (k-quadratic-in-y c0 c1 c2)
    (lambda (x y z) (sat-add (sat-add c0 (sat-mul c1 y)) (sat-mul c2 (sat-mul y y)))))
  (define (k-quadratic-in-z c0 c1 c2)
    (lambda (x y z) (sat-add (sat-add c0 (sat-mul c1 z)) (sat-mul c2 (sat-mul z z)))))
  (define (two-var-quad mn c00 c10 c01 c20 c11 c02)
    (lambda (x y)
      (let ((raw (sat-add
                  (sat-add (sat-add c00 (sat-mul c10 x))
                           (sat-add (sat-mul c01 y) (sat-mul c20 (sat-mul x x))))
                  (sat-add (sat-mul c11 (sat-mul x y)) (sat-mul c02 (sat-mul y y))))))
        (max mn raw))))
  (define (two-var-lin intercept s1 s2)
    (lambda (x y) (sat-add intercept (sat-add (sat-mul s1 x) (sat-mul s2 y)))))
  (define (k-const-above-diag c model) (lambda (x y z) (if (< x y) c (model x y))))
  (define (k-const-below-diag c model) (lambda (x y z) (if (> x y) c (model x y))))
  (define (k-with-interaction c00 c10 c01 c11)
    (lambda (x y z) (sat-add (sat-add c00 (sat-mul c10 x)) (sat-add (sat-mul c01 y) (sat-mul c11 (sat-mul x y))))))
  (define (k-literal-y-or-linear-z i s) (lambda (x y z) (max y (sat-add i (sat-mul s z)))))
  (define (k-linear-in-yz i sy sz) (lambda (x y z) (sat-add i (sat-add (sat-mul sy y) (sat-mul sz z)))))
  (define (k-linear-max-yz i s) (lambda (x y z) (sat-add i (sat-mul s (max y z)))))
  (define (k-above-below model) (lambda (x y z) (model (max x y) (min x y))))
  (define (k-exp-mod c00 c11 c12)
    (lambda (x y z)
      (let* ((yz (sat-mul y z))
             (base (sat-add c00 (sat-add (sat-mul c11 yz) (sat-mul c12 (sat-mul yz z))))))
        (if (> x z) (sat-add base (fxquotient base 2)) base))))

  ;;; ---- builtin cost table (variant E, generated; keyed by builtin name) ----
  (define builtin-cost-table (make-hashtable string-hash string=?))
  (define (def-cost-by-name! name cpu mem)
    (hashtable-set! builtin-cost-table name (cons cpu mem)))
  (define (builtin-cost-fns name)
    (let ((p (hashtable-ref builtin-cost-table name #f)))
      (unless p (assertion-violation 'builtin-cost-fns "no cost model for builtin" name))
      (values (car p) (cdr p))))

  ;;; ---- machine step costs ----
  (define machine-startup-cpu 100)
  (define machine-startup-mem 100)
  (define machine-step-cpu 16000)
  (define machine-step-mem 100)

  ;;; ---- populate the cost table (expressions, after all defines) ----
  (include "cost-table.ss"))
