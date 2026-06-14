;;; (plutuss base) — shared low-level helpers used across the system:
;;; error conditions, the `match` destructuring macro for tagged vectors,
;;; hex/byte utilities, the saturating i64 arithmetic used by costing,
;;; ffi-ptr, and the UTF-8 validator.
(library (plutuss base)
  (export match
          make-parse-err parse-err? parse-err-msg
          make-eval-fail eval-fail? eval-fail-msg
          parse-error eval-failure
          hex-digit-val hex->bytevector
          bv-compare bv<? bv=?
          i64-max i64-min sat-mul sat-add
          ffi-ptr utf8-decode-checked fxlength* write-string)
  (import (chezscheme))

  ;; write a string to a port (Chez has put-string, not write-string)
  (define (write-string s port) (put-string port s))

  ;; ---- match: destructuring case over tagged vectors #(tag slot1 slot2 ...) ----
  ;; (match e ((tag field ...) body ...) ... (else body ...))
  ;; Each clause binds field names to slots 1..n positionally; `_` skips a slot.
  ;; A clause head may also be ((tag1 tag2 ...) field ...) to share one body
  ;; across several tags (fields bind positionally for all of them).
  ;; Without an else clause, an unmatched tag is an assertion violation.
  (define-syntax match
    (lambda (stx)
      (define (syntax->list s)
        (syntax-case s ()
          (() '())
          ((x . rest) (cons #'x (syntax->list #'rest)))))
      (syntax-case stx ()
        ((_ e clause ...)
         (with-syntax (((subj) (generate-temporaries '(subj))))
           (letrec ((bind-fields
                     (lambda (fields i)
                       (syntax-case fields ()
                         (() '())
                         ((f . rest)
                          (if (eq? (syntax->datum #'f) '_)
                              (bind-fields #'rest (fx+ i 1))
                              (cons (list #'f #`(vector-ref subj #,i))
                                    (bind-fields #'rest (fx+ i 1))))))))
                    (expand-clause
                     (lambda (cl)
                       (syntax-case cl (else)
                         ((else body ...) cl)
                         (((head field ...) body ...)
                          (with-syntax (((b ...) (bind-fields #'(field ...) 1))
                                        ((tag ...) (if (identifier? #'head)
                                                       (list #'head)
                                                       (syntax->list #'head))))
                            #'((tag ...) (let (b ...) body ...)))))))
                    (else-clause?
                     (lambda (cl)
                       (syntax-case cl (else)
                         ((else body ...) #t)
                         (_ #f)))))
             (let ((cls (syntax->list #'(clause ...))))
               (with-syntax (((c ...) (map expand-clause cls)))
                 (if (exists else-clause? cls)
                     #'(let ((subj e)) (case (vector-ref subj 0) c ...))
                     #'(let ((subj e))
                         (case (vector-ref subj 0)
                           c ...
                           (else (assertion-violation 'match "no matching clause" subj)))))))))))))

  ;; ---- error conditions ----
  (define-record-type parse-err (fields msg))
  (define-record-type eval-fail (fields msg))
  (define (parse-error msg) (raise (make-parse-err msg)))
  (define (eval-failure msg) (raise (make-eval-fail msg)))

  ;; ---- hex ----
  (define (hex-digit-val c)
    (cond ((and (char>=? c #\0) (char<=? c #\9)) (fx- (char->integer c) 48))
          ((and (char>=? c #\a) (char<=? c #\f)) (fx+ 10 (fx- (char->integer c) 97)))
          ((and (char>=? c #\A) (char<=? c #\F)) (fx+ 10 (fx- (char->integer c) 65)))
          (else (parse-error "bad hex"))))
  (define (hex->bytevector hex)
    (let* ((len (string-length hex)) (nb (fxquotient len 2)) (bv (make-bytevector nb 0)))
      (do ((i 0 (fx+ i 1))) ((fx=? i nb) bv)
        (bytevector-u8-set! bv i
          (fx+ (fx* 16 (hex-digit-val (string-ref hex (fx* i 2))))
               (hex-digit-val (string-ref hex (fx+ (fx* i 2) 1))))))))

  ;; ---- bytevector lexicographic compare ----
  (define (bv-compare a b)
    (let ((la (bytevector-length a)) (lb (bytevector-length b)))
      (let loop ((i 0))
        (cond ((and (fx=? i la) (fx=? i lb)) 0)
              ((fx=? i la) -1)
              ((fx=? i lb) 1)
              (else
               (let ((x (bytevector-u8-ref a i)) (y (bytevector-u8-ref b i)))
                 (cond ((fx<? x y) -1) ((fx>? x y) 1) (else (loop (fx+ i 1))))))))))
  (define (bv<? a b) (fx<? (bv-compare a b) 0))
  (define (bv=? a b) (and (fx=? (bytevector-length a) (bytevector-length b))
                          (fx=? (bv-compare a b) 0)))

  ;; ---- saturating i64 arithmetic (costing) ----
  (define i64-max 9223372036854775807)
  (define i64-min -9223372036854775808)
  (define (sat-mul a b) (let ((r (* a b))) (if (or (> r i64-max) (< r i64-min)) i64-max r)))
  (define (sat-add a b) (let ((r (+ a b))) (if (or (> r i64-max) (< r i64-min)) i64-max r)))

  ;; floor(log2 n) for n>=1
  (define (fxlength* n) (fx- (fxlength n) 1))

  ;; pass a non-null pointer for empty bytevectors to C
  (define (ffi-ptr bv) (if (fx=? (bytevector-length bv) 0) (make-bytevector 1 0) bv))

  ;; UTF-8 decode with validation; raises eval-failure on invalid bytes.
  (define (utf8-decode-checked bv)
    (let ((n (bytevector-length bv)) (out (open-output-string)))
      (let loop ((i 0))
        (if (fx>=? i n)
            (get-output-string out)
            (let ((b0 (bytevector-u8-ref bv i)))
              (define (cont k) (and (fx<? (fx+ i k) n)
                                    (let ((b (bytevector-u8-ref bv (fx+ i k))))
                                      (and (fx=? (fxand b #xC0) #x80) b))))
              (cond
               ((fx<? b0 #x80) (write-char (integer->char b0) out) (loop (fx+ i 1)))
               ((fx=? (fxand b0 #xE0) #xC0)
                (let ((b1 (cont 1)))
                  (unless b1 (eval-failure "bad utf8"))
                  (let ((cp (fxior (fxsll (fxand b0 #x1F) 6) (fxand b1 #x3F))))
                    (when (fx<? cp #x80) (eval-failure "overlong utf8"))
                    (write-char (integer->char cp) out) (loop (fx+ i 2)))))
               ((fx=? (fxand b0 #xF0) #xE0)
                (let ((b1 (cont 1)) (b2 (cont 2)))
                  (unless (and b1 b2) (eval-failure "bad utf8"))
                  (let ((cp (fxior (fxsll (fxand b0 #x0F) 12) (fxsll (fxand b1 #x3F) 6) (fxand b2 #x3F))))
                    (when (fx<? cp #x800) (eval-failure "overlong utf8"))
                    (when (and (fx>=? cp #xD800) (fx<=? cp #xDFFF)) (eval-failure "surrogate"))
                    (write-char (integer->char cp) out) (loop (fx+ i 3)))))
               ((fx=? (fxand b0 #xF8) #xF0)
                (let ((b1 (cont 1)) (b2 (cont 2)) (b3 (cont 3)))
                  (unless (and b1 b2 b3) (eval-failure "bad utf8"))
                  (let ((cp (fxior (fxsll (fxand b0 #x07) 18) (fxsll (fxand b1 #x3F) 12)
                                   (fxsll (fxand b2 #x3F) 6) (fxand b3 #x3F))))
                    (when (or (fx<? cp #x10000) (fx>? cp #x10FFFF)) (eval-failure "bad utf8 range"))
                    (write-char (integer->char cp) out) (loop (fx+ i 4)))))
               (else (eval-failure "bad utf8 lead")))))))))
