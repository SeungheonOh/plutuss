;;; value-builtins.ss — Value batch builtins. Mirrors plutuz cek/builtins/value.zig.

(define (value-builtins fn args)
  (define (a i) (list-ref args i))
  (case fn
    ((insert_coin)
     (let ((ccy (as-bytes (a 0))) (tok (as-bytes (a 1))) (qty (as-int (a 2))) (v (as-value (a 3))))
       (unless (zero? qty) (value-check-qty-range qty))
       (if (or (> (bytevector-length ccy) 32) (> (bytevector-length tok) 32))
           (if (zero? qty) (vvalue v) (eval-failure "insertCoin key too long"))
           (vvalue (value-insert-coin ccy tok qty v)))))
    ((lookup_coin)
     (vint (value-lookup-coin (as-value (a 2)) (as-bytes (a 0)) (as-bytes (a 1)))))
    ((union_value) (vvalue (value-union (as-value (a 0)) (as-value (a 1)))))
    ((value_contains) (vbool (value-contains? (as-value (a 0)) (as-value (a 1)))))
    ((value_data) (vdata (value->data (as-value (a 0)))))
    ((un_value_data) (vvalue (data->value (as-data (a 0)))))
    ((scale_value) (vvalue (value-scale (as-int (a 0)) (as-value (a 1)))))
    (else #f)))

(define apply-builtin-extra-prev3 apply-builtin-extra)
(set! apply-builtin-extra
  (lambda (fn args)
    (or (value-builtins fn args)
        (apply-builtin-extra-prev3 fn args))))
