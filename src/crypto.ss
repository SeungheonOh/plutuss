;;; crypto.ss — cryptographic hash + signature builtins.
;;; FFI: libsodium (sha256, blake2b, ed25519), libsecp256k1 (ecdsa, schnorr).
;;; Pure Scheme: keccak-256, sha3-256, ripemd-160.

(define libsodium-path "/opt/homebrew/opt/libsodium/lib/libsodium.dylib")
(define libsecp-path "/opt/homebrew/opt/secp256k1/lib/libsecp256k1.dylib")
(load-shared-object libsodium-path)
(load-shared-object libsecp-path)

(define mask64 #xFFFFFFFFFFFFFFFF)
(define mask32 #xFFFFFFFF)

;;; ---------------------------------------------------------------------------
;;; libsodium FFI
;;; ---------------------------------------------------------------------------
(define c-sodium-init (foreign-procedure "sodium_init" () int))
(c-sodium-init)
(define c-sha256 (foreign-procedure "crypto_hash_sha256" (u8* u8* size_t) int))
(define c-generichash
  (foreign-procedure "crypto_generichash" (u8* size_t u8* size_t void* size_t) int))
(define c-ed25519-verify
  (foreign-procedure "crypto_sign_verify_detached" (u8* u8* size_t u8*) int))

(define (ffi-ptr bv) (if (fx=? (bytevector-length bv) 0) (make-bytevector 1 0) bv))

(define (sha2-256 bv)
  (let ((out (make-bytevector 32 0)))
    (c-sha256 out (ffi-ptr bv) (bytevector-length bv)) out))

(define (blake2b bv outlen)
  (let ((out (make-bytevector outlen 0)))
    (c-generichash out outlen (ffi-ptr bv) (bytevector-length bv) 0 0) out))

(define (ed25519-verify pk msg sig)        ; pk 32, sig 64 -> bool
  (fx=? 0 (c-ed25519-verify sig (ffi-ptr msg) (bytevector-length msg) pk)))

;;; ---------------------------------------------------------------------------
;;; libsecp256k1 FFI
;;; ---------------------------------------------------------------------------
(define c-ctx-create (foreign-procedure "secp256k1_context_create" (unsigned-int) void*))
(define c-ec-pubkey-parse
  (foreign-procedure "secp256k1_ec_pubkey_parse" (void* u8* u8* size_t) int))
(define c-ecdsa-parse-compact
  (foreign-procedure "secp256k1_ecdsa_signature_parse_compact" (void* u8* u8*) int))
(define c-ecdsa-verify
  (foreign-procedure "secp256k1_ecdsa_verify" (void* u8* u8* u8*) int))
(define c-xonly-parse
  (foreign-procedure "secp256k1_xonly_pubkey_parse" (void* u8* u8*) int))
(define c-schnorr-verify
  (foreign-procedure "secp256k1_schnorrsig_verify" (void* u8* u8* size_t u8*) int))
(define secp-ctx (c-ctx-create 1))       ; SECP256K1_CONTEXT_NONE

(define secp-n  #xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141)
(define secp-half #x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0)

(define (be->int bv start len)
  (let loop ((i start) (n 0) (k 0))
    (if (fx=? k len) n (loop (fx+ i 1) (+ (* n 256) (bytevector-u8-ref bv i)) (fx+ k 1)))))

(define (ecdsa-verify pk msg sig)        ; pk 33, msg 32, sig 64
  (let ((pkobj (make-bytevector 64 0)))
    (when (fx=? 0 (c-ec-pubkey-parse secp-ctx pkobj pk 33)) (eval-failure "ecdsa bad pubkey"))
    (let ((r (be->int sig 0 32)) (s (be->int sig 32 32)))
      (when (or (= r 0) (>= r secp-n) (= s 0) (>= s secp-n)) (eval-failure "ecdsa r/s range"))
      (if (> s secp-half) #f
          (let ((sigobj (make-bytevector 64 0)))
            (c-ecdsa-parse-compact secp-ctx sigobj sig)
            (fx=? 1 (c-ecdsa-verify secp-ctx sigobj msg pkobj)))))))

(define (schnorr-verify pk msg sig)      ; pk 32, sig 64, msg arbitrary
  (let ((xo (make-bytevector 64 0)))
    (when (fx=? 0 (c-xonly-parse secp-ctx xo pk)) (eval-failure "schnorr bad pubkey"))
    (fx=? 1 (c-schnorr-verify secp-ctx sig (ffi-ptr msg) (bytevector-length msg) xo))))

;;; ---------------------------------------------------------------------------
;;; Pure Keccak-f[1600] -> sha3-256 / keccak-256
;;; ---------------------------------------------------------------------------
(define keccak-rc
  (vector #x0000000000000001 #x0000000000008082 #x800000000000808A #x8000000080008000
          #x000000000000808B #x0000000080000001 #x8000000080008081 #x8000000000008009
          #x000000000000008A #x0000000000000088 #x0000000080008009 #x000000008000000A
          #x000000008000808B #x800000000000008B #x8000000000008089 #x8000000000008003
          #x8000000000008002 #x8000000000000080 #x000000000000800A #x800000008000000A
          #x8000000080008081 #x8000000000008080 #x0000000080000001 #x8000000080008008))
(define keccak-rotc (vector 1 3 6 10 15 21 28 36 45 55 2 14 27 41 56 8 25 43 62 18 39 61 20 44))
(define keccak-piln (vector 10 7 11 17 18 3 5 16 8 21 24 4 15 23 19 13 12 2 20 14 22 9 6 1))

(define (rotl64 x n)
  (logand (logior (ash x n) (ash x (fx- n 64))) mask64))

(define (keccak-f! st)
  (let ((bc (make-vector 5 0)))
    (do ((round 0 (fx+ round 1))) ((fx=? round 24))
      ;; theta
      (do ((i 0 (fx+ i 1))) ((fx=? i 5))
        (vector-set! bc i (logxor (vector-ref st i) (vector-ref st (fx+ i 5))
                                  (vector-ref st (fx+ i 10)) (vector-ref st (fx+ i 15))
                                  (vector-ref st (fx+ i 20)))))
      (do ((i 0 (fx+ i 1))) ((fx=? i 5))
        (let ((t (logxor (vector-ref bc (fxmod (fx+ i 4) 5))
                         (rotl64 (vector-ref bc (fxmod (fx+ i 1) 5)) 1))))
          (do ((j 0 (fx+ j 5))) ((fx=? j 25))
            (vector-set! st (fx+ j i) (logxor (vector-ref st (fx+ j i)) t)))))
      ;; rho + pi
      (let loop ((i 0) (t (vector-ref st 1)))
        (when (fx<? i 24)
          (let ((j (vector-ref keccak-piln i)))
            (let ((tmp (vector-ref st j)))
              (vector-set! st j (rotl64 t (vector-ref keccak-rotc i)))
              (loop (fx+ i 1) tmp)))))
      ;; chi
      (do ((j 0 (fx+ j 5))) ((fx=? j 25))
        (do ((i 0 (fx+ i 1))) ((fx=? i 5)) (vector-set! bc i (vector-ref st (fx+ j i))))
        (do ((i 0 (fx+ i 1))) ((fx=? i 5))
          (vector-set! st (fx+ j i)
            (logxor (vector-ref st (fx+ j i))
                    (logand (logxor (vector-ref bc (fxmod (fx+ i 1) 5)) mask64)
                            (vector-ref bc (fxmod (fx+ i 2) 5)))))))
      ;; iota
      (vector-set! st 0 (logxor (vector-ref st 0) (vector-ref keccak-rc round))))))

(define (keccak-hash bv domain)          ; rate 136, output 32 bytes
  (let ((st (make-vector 25 0)) (rate 136) (n (bytevector-length bv))
        (padded #f))
    ;; build padded message
    (let* ((nblocks (fx+ 1 (fxquotient n rate)))
           (plen (fx* nblocks rate))
           (msg (make-bytevector plen 0)))
      (bytevector-copy! bv 0 msg 0 n)
      (bytevector-u8-set! msg n domain)
      (bytevector-u8-set! msg (fx- plen 1)
        (fxior (bytevector-u8-ref msg (fx- plen 1)) #x80))
      ;; absorb
      (do ((off 0 (fx+ off rate))) ((fx>=? off plen))
        (do ((i 0 (fx+ i 1))) ((fx=? i (fxquotient rate 8)))
          (let ((lane (be->le8 msg (fx+ off (fx* i 8)))))
            (vector-set! st i (logxor (vector-ref st i) lane))))
        (keccak-f! st))
      ;; squeeze 32 bytes (lanes 0..3, little-endian)
      (let ((out (make-bytevector 32 0)))
        (do ((i 0 (fx+ i 1))) ((fx=? i 4) out)
          (le8->bytes! (vector-ref st i) out (fx* i 8)))))))

(define (be->le8 bv off)                 ; read 8 bytes little-endian as integer
  (let loop ((i 7) (n 0))
    (if (fx<? i 0) n (loop (fx- i 1) (+ (* n 256) (bytevector-u8-ref bv (fx+ off i)))))))
(define (le8->bytes! lane bv off)
  (do ((i 0 (fx+ i 1))) ((fx=? i 8))
    (bytevector-u8-set! bv (fx+ off i) (logand (ash lane (fx* -8 i)) #xFF))))

(define (sha3-256 bv) (keccak-hash bv #x06))
(define (keccak-256 bv) (keccak-hash bv #x01))

;;; ---------------------------------------------------------------------------
;;; Pure RIPEMD-160
;;; ---------------------------------------------------------------------------
(define rmd-left-r
  (vector 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
          7 4 13 1 10 6 15 3 12 0 9 5 2 14 11 8
          3 10 14 4 9 15 8 1 2 7 0 6 13 11 5 12
          1 9 11 10 0 8 12 4 13 3 7 15 14 5 6 2
          4 0 5 9 7 12 2 10 14 1 3 8 11 6 15 13))
(define rmd-left-s
  (vector 11 14 15 12 5 8 7 9 11 13 14 15 6 7 9 8
          7 6 8 13 11 9 7 15 7 12 15 9 11 7 13 12
          11 13 6 7 14 9 13 15 14 8 13 6 5 12 7 5
          11 12 14 15 14 15 9 8 9 14 5 6 8 6 5 12
          9 15 5 11 6 8 13 12 5 12 13 14 11 8 5 6))
(define rmd-right-r
  (vector 5 14 7 0 9 2 11 4 13 6 15 8 1 10 3 12
          6 11 3 7 0 13 5 10 14 15 8 12 4 9 1 2
          15 5 1 3 7 14 6 9 11 8 12 2 10 0 4 13
          8 6 4 1 3 11 15 0 5 12 2 13 9 7 10 14
          12 15 10 4 1 5 8 7 6 2 13 14 0 3 9 11))
(define rmd-right-s
  (vector 8 9 9 11 13 15 15 5 7 7 8 11 14 14 12 6
          9 13 15 7 12 8 9 11 7 7 12 7 6 15 13 11
          9 7 15 11 8 6 6 14 12 13 5 14 13 13 7 5
          15 5 8 11 14 14 6 14 6 9 12 9 12 5 15 8
          8 5 12 9 12 5 14 6 8 13 6 5 15 13 11 11))
(define rmd-left-k (vector #x00000000 #x5A827999 #x6ED9EBA1 #x8F1BBCDC #xA953FD4E))
(define rmd-right-k (vector #x50A28BE6 #x5C4DD124 #x6D703EF3 #x7A6D76E9 #x00000000))

(define (rotl32 x n) (logand (logior (ash x n) (ash x (fx- n 32))) mask32))
(define (u32+ . xs) (logand (apply + xs) mask32))
(define (rmd-f j b c d)
  (let ((blk (fxquotient j 16)))
    (case blk
      ((0) (logxor b c d))
      ((1) (logand mask32 (logior (logand b c) (logand (logxor b mask32) d))))
      ((2) (logxor (logior b (logxor c mask32)) d))
      ((3) (logand mask32 (logior (logand b d) (logand c (logxor d mask32)))))
      ((4) (logxor b (logior c (logxor d mask32)))))))
(define (rmd-fl j b c d) (rmd-f j b c d))
(define (rmd-fr j b c d) (rmd-f (fx- 79 j) b c d))  ; right uses reversed block order: 4,3,2,1,0

(define (ripemd-160 bv)
  (let ((state (vector #x67452301 #xEFCDAB89 #x98BADCFE #x10325476 #xC3D2E1F0))
        (n (bytevector-length bv)))
    (define (process block off)          ; block: bytevector, off start of 64-byte block
      (let ((x (make-vector 16 0)))
        (do ((i 0 (fx+ i 1))) ((fx=? i 16))
          (vector-set! x i (le32 block (fx+ off (fx* i 4)))))
        (let loop ((j 0)
                   (al (vector-ref state 0)) (bl (vector-ref state 1)) (cl (vector-ref state 2))
                   (dl (vector-ref state 3)) (el (vector-ref state 4))
                   (ar (vector-ref state 0)) (br (vector-ref state 1)) (cr (vector-ref state 2))
                   (dr (vector-ref state 3)) (er (vector-ref state 4)))
          (if (fx=? j 80)
              (let ((t (u32+ (vector-ref state 1) cl dr)))
                (vector-set! state 1 (u32+ (vector-ref state 2) dl er))
                (vector-set! state 2 (u32+ (vector-ref state 3) el ar))
                (vector-set! state 3 (u32+ (vector-ref state 4) al br))
                (vector-set! state 4 (u32+ (vector-ref state 0) bl cr))
                (vector-set! state 0 t))
              (let ((tl (u32+ (rotl32 (u32+ al (rmd-fl j bl cl dl)
                                           (vector-ref x (vector-ref rmd-left-r j))
                                           (vector-ref rmd-left-k (fxquotient j 16)))
                                      (vector-ref rmd-left-s j))
                              el))
                    (tr (u32+ (rotl32 (u32+ ar (rmd-fr j br cr dr)
                                           (vector-ref x (vector-ref rmd-right-r j))
                                           (vector-ref rmd-right-k (fxquotient j 16)))
                                      (vector-ref rmd-right-s j))
                              er)))
                (loop (fx+ j 1)
                      el tl bl (rotl32 cl 10) dl
                      er tr br (rotl32 cr 10) dr))))))
    ;; build padded message
    (let* ((total-bits (* n 8))
           (padlen (let ((r (fxmod (fx+ n 1) 64))) (if (fx<=? r 56) (fx- 56 r) (fx- 120 r))))
           (mlen (fx+ n 1 padlen 8))
           (msg (make-bytevector mlen 0)))
      (bytevector-copy! bv 0 msg 0 n)
      (bytevector-u8-set! msg n #x80)
      (do ((i 0 (fx+ i 1))) ((fx=? i 8))
        (bytevector-u8-set! msg (fx+ (fx- mlen 8) i) (logand (ash total-bits (fx* -8 i)) #xFF)))
      (do ((off 0 (fx+ off 64))) ((fx>=? off mlen))
        (process msg off))
      (let ((out (make-bytevector 20 0)))
        (do ((i 0 (fx+ i 1))) ((fx=? i 5) out)
          (let ((w (vector-ref state i)))
            (do ((k 0 (fx+ k 1))) ((fx=? k 4))
              (bytevector-u8-set! out (fx+ (fx* i 4) k) (logand (ash w (fx* -8 k)) #xFF)))))))))

(define (le32 bv off)
  (logior (bytevector-u8-ref bv off)
          (ash (bytevector-u8-ref bv (fx+ off 1)) 8)
          (ash (bytevector-u8-ref bv (fx+ off 2)) 16)
          (ash (bytevector-u8-ref bv (fx+ off 3)) 24)))

;;; ---------------------------------------------------------------------------
;;; Builtin dispatch
;;; ---------------------------------------------------------------------------
(define (crypto-builtins fn args)
  (define (a i) (list-ref args i))
  (case fn
    ((sha2_256) (vbytes (sha2-256 (as-bytes (a 0)))))
    ((sha3_256) (vbytes (sha3-256 (as-bytes (a 0)))))
    ((keccak_256) (vbytes (keccak-256 (as-bytes (a 0)))))
    ((blake2b_256) (vbytes (blake2b (as-bytes (a 0)) 32)))
    ((blake2b_224) (vbytes (blake2b (as-bytes (a 0)) 28)))
    ((ripemd_160) (vbytes (ripemd-160 (as-bytes (a 0)))))
    ((verify_ed25519_signature)
     (let ((pk (as-bytes (a 0))) (msg (as-bytes (a 1))) (sig (as-bytes (a 2))))
       (unless (fx=? (bytevector-length pk) 32) (eval-failure "ed25519 pk len"))
       (unless (fx=? (bytevector-length sig) 64) (eval-failure "ed25519 sig len"))
       (vbool (ed25519-verify pk msg sig))))
    ((verify_ecdsa_secp256k1_signature)
     (let ((pk (as-bytes (a 0))) (msg (as-bytes (a 1))) (sig (as-bytes (a 2))))
       (unless (fx=? (bytevector-length pk) 33) (eval-failure "ecdsa pk len"))
       (unless (fx=? (bytevector-length msg) 32) (eval-failure "ecdsa msg len"))
       (unless (fx=? (bytevector-length sig) 64) (eval-failure "ecdsa sig len"))
       (vbool (ecdsa-verify pk msg sig))))
    ((verify_schnorr_secp256k1_signature)
     (let ((pk (as-bytes (a 0))) (msg (as-bytes (a 1))) (sig (as-bytes (a 2))))
       (unless (fx=? (bytevector-length pk) 32) (eval-failure "schnorr pk len"))
       (unless (fx=? (bytevector-length sig) 64) (eval-failure "schnorr sig len"))
       (vbool (schnorr-verify pk msg sig))))
    (else #f)))

(define apply-builtin-extra-prev4 apply-builtin-extra)
(set! apply-builtin-extra
  (lambda (fn args)
    (or (crypto-builtins fn args)
        (apply-builtin-extra-prev4 fn args))))
