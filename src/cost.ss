;;; cost.ss — ExMem sizing, costing algebra, default cost model.
;;; Mirrors plutuz cek/ex_mem.zig, cek/costing.zig, cek/cost_model*.zig.

(define i64-max 9223372036854775807)
(define i64-min -9223372036854775808)

(define (sat-mul a b)
  (let ((r (* a b))) (if (or (> r i64-max) (< r i64-min)) i64-max r)))
(define (sat-add a b)
  (let ((r (+ a b))) (if (or (> r i64-max) (< r i64-min)) i64-max r)))

;;; ---------------------------------------------------------------------------
;;; ExMem sizing
;;; ---------------------------------------------------------------------------

(define (integer-ex-mem n)
  (let ((bits (integer-length (abs n))))
    (if (fx=? bits 0) 1 (fx+ (fxquotient (fx- bits 1) 64) 1))))

(define (bytestring-ex-mem bv)
  (let ((len (bytevector-length bv)))
    (if (fx=? len 0) 1 (fx+ (fxquotient (fx- len 1) 8) 1))))

(define (string-ex-mem s) (fxquotient (bytevector-length (string->utf8 s)) 4))

(define (size-ex-mem v)
  (if (fx<=? v 0) 0 (fx+ (fxquotient (fx- v 1) 8) 1)))

(define (integer-costed-literally n)
  (let ((a (abs n))) (if (> a i64-max) i64-max a)))

;; PlutusData recursive sizing (weighted): +4 per node, +intMem/+bsMem at leaves.
(define (data-ex-mem d)
  (let loop ((stack (list d)) (total 0))
    (if (null? stack)
        total
        (let ((cur (car stack)) (rest (cdr stack)))
          (case (car cur)
            ((Constr) (loop (append (caddr cur) rest) (fx+ total 4)))
            ((Map) (loop (fold-left (lambda (acc p) (cons (car p) (cons (cdr p) acc)))
                                    rest (cadr cur))
                         (fx+ total 4)))
            ((List) (loop (append (cadr cur) rest) (fx+ total 4)))
            ((I) (loop rest (fx+ total 4 (integer-ex-mem (cadr cur)))))
            ((B) (loop rest (fx+ total 4 (bytestring-ex-mem (cadr cur)))))
            (else (loop rest (fx+ total 4))))))))

;; DataNodeCount: +1 per node.
(define (data-node-count d)
  (let loop ((stack (list d)) (total 0))
    (if (null? stack)
        total
        (let ((cur (car stack)) (rest (cdr stack)))
          (case (car cur)
            ((Constr) (loop (append (caddr cur) rest) (fx+ total 1)))
            ((Map) (loop (fold-left (lambda (acc p) (cons (car p) (cons (cdr p) acc)))
                                    rest (cadr cur))
                         (fx+ total 1)))
            ((List) (loop (append (cadr cur) rest) (fx+ total 1)))
            (else (loop rest (fx+ total 1))))))))

(define (g1-ex-mem) 18)
(define (g2-ex-mem) 36)
(define (ml-ex-mem) 72)

;;; ---------------------------------------------------------------------------
;;; Costing algebra — each cost fn is (lambda (x y z) -> i64)
;;; ---------------------------------------------------------------------------

(define (k-const c) (lambda (x y z) c))
(define (k-linear i s) (lambda (x y z) (sat-add i (sat-mul s x))))          ; linear in x
(define (k-linear-y i s) (lambda (x y z) (sat-add i (sat-mul s y))))
(define (k-linear-z i s) (lambda (x y z) (sat-add i (sat-mul s z))))
(define (k-added i s) (lambda (x y z) (sat-add i (sat-mul s (sat-add x y)))))
(define (k-subtracted i s mn)
  (lambda (x y z) (max mn (sat-add i (sat-mul s (- x y))))))
(define (k-multiplied i s) (lambda (x y z) (sat-add i (sat-mul s (sat-mul x y)))))
(define (k-min-size i s) (lambda (x y z) (sat-add i (sat-mul s (min x y)))))
(define (k-max-size i s) (lambda (x y z) (sat-add i (sat-mul s (max x y)))))
(define (k-linear-on-diag i s c)
  (lambda (x y z) (if (= x y) (sat-add i (sat-mul s x)) c)))
(define (k-quadratic c0 c1 c2)   ; quadratic in x
  (lambda (x y z) (sat-add (sat-add c0 (sat-mul c1 x)) (sat-mul c2 (sat-mul x x)))))
(define (k-quadratic-in-y c0 c1 c2)
  (lambda (x y z) (sat-add (sat-add c0 (sat-mul c1 y)) (sat-mul c2 (sat-mul y y)))))
(define (k-quadratic-in-z c0 c1 c2)
  (lambda (x y z) (sat-add (sat-add c0 (sat-mul c1 z)) (sat-mul c2 (sat-mul z z)))))

;; two-variable quadratic with minimum
(define (two-var-quad mn c00 c10 c01 c20 c11 c02)
  (lambda (x y)
    (let ((raw (sat-add
                (sat-add (sat-add c00 (sat-mul c10 x))
                         (sat-add (sat-mul c01 y) (sat-mul c20 (sat-mul x x))))
                (sat-add (sat-mul c11 (sat-mul x y)) (sat-mul c02 (sat-mul y y))))))
      (max mn raw))))

(define (two-var-lin intercept s1 s2)
  (lambda (x y) (sat-add intercept (sat-add (sat-mul s1 x) (sat-mul s2 y)))))

(define (k-const-above-diag c model)
  (lambda (x y z) (if (< x y) c (model x y))))
(define (k-const-below-diag c model)
  (lambda (x y z) (if (> x y) c (model x y))))
(define (k-with-interaction c00 c10 c01 c11)
  (lambda (x y z)
    (sat-add (sat-add c00 (sat-mul c10 x))
             (sat-add (sat-mul c01 y) (sat-mul c11 (sat-mul x y))))))
(define (k-literal-y-or-linear-z i s)
  (lambda (x y z) (max y (sat-add i (sat-mul s z)))))
(define (k-linear-in-yz i sy sz)
  (lambda (x y z) (sat-add i (sat-add (sat-mul sy y) (sat-mul sz z)))))
(define (k-linear-max-yz i s)
  (lambda (x y z) (sat-add i (sat-mul s (max y z)))))
(define (k-above-below model)   ; model is (lambda (x y)) ; eval at (max,min)
  (lambda (x y z) (model (max x y) (min x y))))
(define (k-exp-mod c00 c11 c12)
  (lambda (x y z)
    (let* ((yz (sat-mul y z))
           (base (sat-add c00 (sat-add (sat-mul c11 yz) (sat-mul c12 (sat-mul yz z))))))
      (if (> x z) (sat-add base (fxquotient base 2)) base))))

;;; ---------------------------------------------------------------------------
;;; Builtin cost table: fnsym -> (cpu-fn . mem-fn)
;;; ---------------------------------------------------------------------------

(define builtin-cost-table (make-eq-hashtable))
(define (def-cost! sym cpu mem) (hashtable-set! builtin-cost-table sym (cons cpu mem)))
(define (builtin-cost sym) (hashtable-ref builtin-cost-table sym #f))

(define (def-cost-by-name! name cpu mem)
  (let ((sym (builtin-lookup name)))
    (when sym (hashtable-set! builtin-cost-table sym (cons cpu mem)))))
(load "src/cost-table.ss")


;;; ---------------------------------------------------------------------------
;;; Machine step costs  (mem cpu)
;;; ---------------------------------------------------------------------------
;; startup + 9 step kinds; all step kinds cost {mem 100, cpu 16000}.
(define machine-startup-cpu 100)
(define machine-startup-mem 100)
(define machine-step-cpu 16000)
(define machine-step-mem 100)

;;; ---------------------------------------------------------------------------
;;; Arity / force-count tables
;;; ---------------------------------------------------------------------------
(define builtin-arity-table (make-eq-hashtable))
(define builtin-force-table (make-eq-hashtable))
(define (builtin-arity sym) (hashtable-ref builtin-arity-table sym 0))
(define (builtin-force-count sym) (hashtable-ref builtin-force-table sym 0))

(for-each (lambda (s) (hashtable-set! builtin-arity-table s 1))
  '(sha2_256 sha3_256 blake2b_224 blake2b_256 keccak_256 length_of_byte_string
    encode_utf8 decode_utf8 fst_pair snd_pair head_list tail_list null_list
    map_data list_data i_data b_data un_constr_data un_map_data un_list_data
    un_i_data un_b_data serialise_data mk_nil_data mk_nil_pair_data
    bls12_381_g1_neg bls12_381_g1_compress bls12_381_g1_uncompress
    bls12_381_g2_neg bls12_381_g2_compress bls12_381_g2_uncompress
    complement_byte_string count_set_bits find_first_set_bit ripemd_160
    length_of_array list_to_array value_data un_value_data))
(for-each (lambda (s) (hashtable-set! builtin-arity-table s 2))
  '(add_integer subtract_integer multiply_integer divide_integer quotient_integer
    remainder_integer mod_integer equals_integer less_than_integer
    less_than_equals_integer append_byte_string cons_byte_string index_byte_string
    equals_byte_string less_than_byte_string less_than_equals_byte_string
    append_string equals_string choose_unit trace mk_cons constr_data equals_data
    mk_pair_data bls12_381_g1_add bls12_381_g1_scalar_mul bls12_381_g1_equal
    bls12_381_g1_hash_to_group bls12_381_g2_add bls12_381_g2_scalar_mul
    bls12_381_g2_equal bls12_381_g2_hash_to_group bls12_381_miller_loop
    bls12_381_mul_ml_result bls12_381_final_verify byte_string_to_integer read_bit
    replicate_byte shift_byte_string rotate_byte_string drop_list index_array
    union_value value_contains scale_value bls12_381_g1_multi_scalar_mul
    bls12_381_g2_multi_scalar_mul))
(for-each (lambda (s) (hashtable-set! builtin-arity-table s 3))
  '(slice_byte_string if_then_else choose_list verify_ed25519_signature
    verify_ecdsa_secp256k1_signature verify_schnorr_secp256k1_signature
    integer_to_byte_string and_byte_string or_byte_string xor_byte_string
    write_bits exp_mod_integer lookup_coin))
(hashtable-set! builtin-arity-table 'insert_coin 4)
(hashtable-set! builtin-arity-table 'choose_data 6)

(for-each (lambda (s) (hashtable-set! builtin-force-table s 1))
  '(if_then_else choose_unit trace mk_cons head_list tail_list null_list
    choose_data drop_list length_of_array list_to_array index_array))
(for-each (lambda (s) (hashtable-set! builtin-force-table s 2))
  '(fst_pair snd_pair choose_list))
