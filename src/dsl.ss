;;; dsl.ss — build UPLC ASTs directly from Scheme syntax (a macro front-end).
;;;
;;; Where frontend.ss tokenizes and parses a STRING, this builds the very same
;;; named-AST vectors at macro-expansion time from s-expression syntax — UPLC's
;;; textual grammar is already list-shaped, so it maps almost 1:1.
;;;
;;;   (uplc (lam x [ [ (builtin addInteger) x ] (con integer 1) ]))
;;;   ≡ (parse a string) → produces #(lam "x" ...), feeds name->debruijn + CEK.
;;;
;;; Grammar (Scheme syntax):
;;;   term  := name                              variable
;;;          | (lam name term)                   lambda
;;;          | (delay term) | (force term)
;;;          | (con type value)                  constant
;;;          | (builtin Name)                    Name is camelCase, e.g. addInteger
;;;          | (error)
;;;          | (constr tag term ...)             tag is any Scheme expr
;;;          | (case term term ...)
;;;          | (f a b ...)                        application (also [f a b])
;;;          | ($ expr)                           splice a Scheme-built AST term
;;;   type  := integer | bytestring | string | bool | unit | data
;;;          | (list type) | (pair type type)
;;;   value := for each type, the natural Scheme value (see up-cval below);
;;;            constant values may be arbitrary Scheme expressions.
;;;   data  := (I n) | (B bv) | (List data ...) | (Map (k v) ...) | (Constr t data ...)
;;;            (or any Scheme expr evaluating to a data rep)
;;;
;;; Public entry points:
;;;   (uplc term)                  -> named AST (pre de-Bruijn)
;;;   (uplc-program (maj min pat) term) -> #(program #(maj min pat) named-ast)
;;;   (uplc-eval term)             -> result term (de-Bruijn), via the CEK machine
;;;   (uplc-run  term)             -> pretty-printed result program (string)
;;; Helpers:
;;;   (hex "deadbeef")             -> bytevector, for (con bytestring ...)

(define hex hex->bytevector)

;; Bytestring literal coercion: a hex string ("deadbeef"), a bytevector
;; (#vu8(...)), or a list of byte values are all accepted. This lets you write
;; (con bytestring "76") — the reader-legal stand-in for textual `#76`.
(define (->bytes v)
  (cond ((string? v) (hex->bytevector v))
        ((bytevector? v) v)
        ((list? v) (apply bytevector v))
        (else (error 'uplc "bytestring expects a hex string or bytevector" v))))

(define (dsl-builtin sym)
  (or (builtin-lookup (symbol->string sym))
      (error 'uplc "unknown builtin" sym)))

;; A type form is already its own rep — just quote it.
(define-syntax uplc-type (syntax-rules () ((_ t) (quote t))))

;; PlutusData builder.
(define-syntax up-data
  (syntax-rules (I B List Map Constr)
    ((_ (I n))         (list 'I n))
    ((_ (B bv))        (list 'B (->bytes bv)))
    ((_ (List d ...))  (list 'List (list (up-data d) ...)))
    ((_ (Map (k v) ...)) (list 'Map (list (cons (up-data k) (up-data v)) ...)))
    ((_ (Constr t d ...)) (list 'Constr t (list (up-data d) ...)))
    ((_ e)             e)))                ; splice a precomputed data rep

;; Constant value of a given type (no `con` wrapper). Used at top level by
;; (con type value) and recursively for list/pair element values.
(define-syntax up-cval
  (syntax-rules (integer bytestring string bool unit data list pair)
    ((_ integer v)    (list 'int v))
    ((_ bytestring v) (list 'bytes (->bytes v)))
    ((_ string v)     (list 'str v))
    ((_ bool v)       (list 'bool v))
    ((_ unit v)       (list 'unit))
    ((_ data v)       (list 'data (up-data v)))
    ((_ (list t) (e ...))
     (list 'plist (uplc-type t) (list (up-cval t e) ...)))
    ((_ (pair a b) (x y))
     (list 'ppair (uplc-type a) (uplc-type b) (up-cval a x) (up-cval b y)))
    ((_ (pair a b) (x . y))
     (list 'ppair (uplc-type a) (uplc-type b) (up-cval a x) (up-cval b y)))))

;; Term builder.
(define-syntax uplc
  (syntax-rules (lam delay force con builtin error constr case $)
    ((_ ($ e))            e)
    ((_ (lam x body))     (vector 'lam (symbol->string 'x) (uplc body)))
    ((_ (delay t))        (vector 'delay (uplc t)))
    ((_ (force t))        (vector 'force (uplc t)))
    ((_ (con type val))   (vector 'con (up-cval type val)))
    ((_ (builtin name))   (vector 'builtin (dsl-builtin 'name)))
    ((_ (error))          (vector 'uerror))
    ((_ (constr tag f ...)) (vector 'constr tag (list (uplc f) ...)))
    ((_ (case s b ...))   (vector 'case (uplc s) (list (uplc b) ...)))
    ((_ (f a))            (vector 'app (uplc f) (uplc a)))
    ((_ (f a b ...))      (uplc ((f a) b ...)))      ; left-assoc application
    ((_ x)                (vector 'var (symbol->string 'x)))))

(define-syntax uplc-program
  (syntax-rules ()
    ((_ (maj min pat) term) (vector 'program (vector maj min pat) (uplc term)))))

;; Evaluate an already-built AST (the value produced by `uplc`). These are
;; FUNCTIONS, not macros: pass a term value, e.g. (uplc-eval (uplc (lam x x)))
;; or, when the term is already bound, (uplc-eval my-term).
(define (uplc-eval ast) (machine-run (name->debruijn ast)))

;; Evaluate and pretty-print the result as a 1.1.0 program string.
(define (uplc-run ast) (pretty-program (vector 1 1 0) (uplc-eval ast)))
