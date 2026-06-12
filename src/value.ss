;;; value.ss — Plutus multi-asset Value (sorted map of maps) and its builtins.
;;; Mirrors plutuz ast/value.zig.
;;;
;;; Value representation: (vector 'V entries size)
;;;   entries : list of (ccy . tokens)   ccy a bytevector (<=32)
;;;   tokens  : list of (tok . qty)       tok a bytevector (<=32), qty nonzero exact int
;;;   Both levels sorted ascending by key; size = total token count.

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

;; 128-bit signed range check: -(2^127) .. 2^127-1 ; raises eval-failure if out.
(define value-max (- (expt 2 127) 1))
(define value-min (- (expt 2 127)))
(define (value-check-qty-range q)
  (when (or (> q value-max) (< q value-min))
    (eval-failure "value quantity out of range")))

;; Merge a sorted-by-name token alist that may have duplicates: add quantities, drop zeros.
(define (merge-token-dups sorted)
  (let loop ((lst sorted) (acc '()))
    (cond
     ((null? lst) (reverse acc))
     ((and (pair? acc) (bv=? (caar acc) (caar lst)))
      (let ((sum (+ (cdar acc) (cdar lst))))
        (value-check-qty-range sum)
        (if (zero? sum)
            (loop (cdr lst) (cdr acc))
            (loop (cdr lst) (cons (cons (caar acc) sum) (cdr acc))))))
     ((zero? (cdar lst)) (loop (cdr lst) acc))    ; drop standalone zero token
     (else (loop (cdr lst) (cons (car lst) acc))))))

;; Build normalized value from raw entries: list of (ccy . token-alist).
;; token-alist entries are (tok . qty); may have dup toks/ccys and zeros.
(define (value-normalize raw)
  ;; normalize each currency's tokens
  (let* ((per-ccy
          (map (lambda (e)
                 (let* ((ccy (car e))
                        (toks (cdr e))
                        (sorted (list-sort (lambda (a b) (bv<? (car a) (car b))) toks))
                        (merged (merge-token-dups sorted)))
                   (cons ccy merged)))
               raw))
         ;; sort currencies
         (sorted-ccy (list-sort (lambda (a b) (bv<? (car a) (car b))) per-ccy))
         ;; merge duplicate currencies (concat token lists, re-merge), drop empties
         (merged-ccy
          (let loop ((lst sorted-ccy) (acc '()))
            (cond
             ((null? lst)
              (reverse acc))
             ((and (pair? acc) (bv=? (caar acc) (caar lst)))
              ;; merge token lists of same currency
              (let* ((combined (append (cdar acc) (cdar lst)))
                     (sorted (list-sort (lambda (a b) (bv<? (car a) (car b))) combined))
                     (merged (merge-token-dups sorted)))
                (loop (cdr lst) (cons (cons (caar acc) merged) (cdr acc)))))
             (else (loop (cdr lst) (cons (car lst) acc)))))))
    (let* ((nonempty (filter (lambda (e) (not (null? (cdr e)))) merged-ccy))
           (size (fold-left (lambda (n e) (fx+ n (length (cdr e)))) 0 nonempty)))
      (vector 'V nonempty size))))

(define (value-entries v) (vector-ref v 1))
(define (value-size v) (vector-ref v 2))
(define value-empty (vector 'V '() 0))

(define (value-lookup-coin v ccy tok)
  (let cloop ((es (value-entries v)))
    (cond
     ((null? es) 0)
     ((bv=? (caar es) ccy)
      (let tloop ((ts (cdar es)))
        (cond ((null? ts) 0)
              ((bv=? (caar ts) tok) (cdar ts))
              ((fx>? (bv-compare (caar ts) tok) 0) 0)
              (else (tloop (cdr ts))))))
     ((fx>? (bv-compare (caar es) ccy) 0) 0)
     (else (cloop (cdr es))))))

;; insert/update coin; qty=0 deletes. Returns new value. (No range check here —
;; matches plutuz insertCoin which assumes caller-provided qty.)
(define (value-insert-coin ccy tok qty v)
  ;; rebuild via normalize over modified raw form
  (let* ((entries (value-entries v))
         ;; convert to raw: drop the target then re-add
         (raw0 (map (lambda (e) (cons (car e) (cdr e))) entries))
         (raw1 (if (zero? qty)
                   ;; remove (ccy,tok)
                   (map (lambda (e)
                          (if (bv=? (car e) ccy)
                              (cons (car e) (filter (lambda (t) (not (bv=? (car t) tok))) (cdr e)))
                              e))
                        raw0)
                   ;; set (ccy,tok)=qty : drop existing then add
                   (let ((without (map (lambda (e)
                                         (if (bv=? (car e) ccy)
                                             (cons (car e) (filter (lambda (t) (not (bv=? (car t) tok))) (cdr e)))
                                             e))
                                       raw0)))
                     (if (exists (lambda (e) (bv=? (car e) ccy)) without)
                         (map (lambda (e)
                                (if (bv=? (car e) ccy)
                                    (cons (car e) (cons (cons tok qty) (cdr e)))
                                    e))
                              without)
                         (cons (cons ccy (list (cons tok qty))) without))))))
    (value-normalize raw1)))

;; union: add quantities of two values; range-checked; drop zeros.
(define (value-union v1 v2)
  (let ((raw (append (map (lambda (e) (cons (car e) (cdr e))) (value-entries v1))
                     (map (lambda (e) (cons (car e) (cdr e))) (value-entries v2)))))
    ;; value-normalize merges & checks range via merge-token-dups
    (value-normalize raw)))

;; valueContains v1 v2 : v1 >= v2 componentwise; both must be nonnegative.
(define (value-contains? v1 v2)
  (define (check-nonneg v)
    (for-each (lambda (e)
                (for-each (lambda (t) (when (< (cdr t) 0) (eval-failure "negative qty")))
                          (cdr e)))
              (value-entries v)))
  (check-nonneg v1)
  (check-nonneg v2)
  (let cloop ((es (value-entries v2)))
    (cond
     ((null? es) #t)
     (else
      (let ((ccy (caar es)))
        (let tloop ((ts (cdar es)))
          (cond
           ((null? ts) (cloop (cdr es)))
           (else
            (let ((have (value-lookup-coin v1 ccy (caar ts))))
              (if (< have (cdar ts)) #f (tloop (cdr ts))))))))))))

;; scaleValue scalar v : multiply quantities; scalar=0 -> empty; range-checked.
(define (value-scale scalar v)
  (if (zero? scalar)
      value-empty
      (begin
        (value-check-qty-range scalar)
        (let ((raw
               (map (lambda (e)
                      (cons (car e)
                            (filter-map (lambda (t)
                                          (let ((p (* (cdr t) scalar)))
                                            (value-check-qty-range p)
                                            (and (not (zero? p)) (cons (car t) p))))
                                        (cdr e))))
                    (value-entries v))))
          (value-normalize raw)))))

(define (filter-map f lst)
  (let loop ((l lst) (acc '()))
    (cond ((null? l) (reverse acc))
          ((f (car l)) => (lambda (x) (loop (cdr l) (cons x acc))))
          (else (loop (cdr l) acc)))))

;; valueData v -> PlutusData : Map [(B ccy, Map [(B tok, I qty)])]
(define (value->data v)
  (list 'Map
        (map (lambda (e)
               (cons (list 'B (car e))
                     (list 'Map
                           (map (lambda (t) (cons (list 'B (car t)) (list 'I (cdr t))))
                                (cdr e)))))
             (value-entries v))))

;; unValueData d -> value, with strict validation (sorted, no zeros, nonempty inner,
;; keys<=32, qty in range). Raises eval-failure on any violation.
(define (data->value d)
  (unless (and (pair? d) (eq? (car d) 'Map)) (eval-failure "unValueData: not a map"))
  (let ((outer (cadr d)))
    (let cloop ((pairs outer) (prev-ccy #f) (entries '()) (size 0))
      (if (null? pairs)
          (vector 'V (reverse entries) size)
          (let* ((pr (car pairs))
                 (kd (car pr)) (vd (cdr pr)))
            (unless (and (pair? kd) (eq? (car kd) 'B)) (eval-failure "unValueData: ccy not B"))
            (let ((ccy (cadr kd)))
              (when (fx>? (bytevector-length ccy) 32) (eval-failure "ccy too long"))
              (when (and prev-ccy (fx>=? (bv-compare prev-ccy ccy) 0)) (eval-failure "ccy unsorted"))
              (unless (and (pair? vd) (eq? (car vd) 'Map)) (eval-failure "inner not map"))
              (let ((inner (cadr vd)))
                (when (null? inner) (eval-failure "empty inner map"))
                (let tloop ((ts inner) (prev-tok #f) (toks '()) (cnt 0))
                  (if (null? ts)
                      (cloop (cdr pairs) ccy
                             (cons (cons ccy (reverse toks)) entries)
                             (fx+ size cnt))
                      (let* ((tp (car ts)) (tkd (car tp)) (tvd (cdr tp)))
                        (unless (and (pair? tkd) (eq? (car tkd) 'B)) (eval-failure "tok not B"))
                        (let ((tok (cadr tkd)))
                          (when (fx>? (bytevector-length tok) 32) (eval-failure "tok too long"))
                          (when (and prev-tok (fx>=? (bv-compare prev-tok tok) 0)) (eval-failure "tok unsorted"))
                          (unless (and (pair? tvd) (eq? (car tvd) 'I)) (eval-failure "qty not I"))
                          (let ((qty (cadr tvd)))
                            (when (zero? qty) (eval-failure "zero qty"))
                            (value-check-qty-range qty)
                            (tloop (cdr ts) tok (cons (cons tok qty) toks) (fx+ cnt 1))))))))))))))

;; ValueMaxDepth: log2(outer)+1 + log2(maxInner)+1
(define (value-max-depth v)
  (let* ((entries (value-entries v))
         (outer (length entries))
         (max-inner (fold-left (lambda (m e) (fxmax m (length (cdr e)))) 0 entries))
         (log-outer (if (fx>? outer 0) (fx+ 1 (fxlength* outer)) 0))
         (log-inner (if (fx>? max-inner 0) (fx+ 1 (fxlength* max-inner)) 0)))
    (fx+ log-outer log-inner)))

;; floor(log2 n) for n>=1
(define (fxlength* n) (fx- (fxlength n) 1))
