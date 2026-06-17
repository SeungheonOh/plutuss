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
;;;          | ,expr                              splice a Scheme-built AST term
;;;          | (lam ,name-expr term)              computed binder name (a string)
;;;   In the list-shaped positions — case branches, constr fields, application
;;;   arguments — ,@expr splices a Scheme list of terms in place.
;;;   type  := integer | bytestring | string | bool | unit | data
;;;          | (list type) | (pair type type)
;;;   value := for each type, the natural Scheme value (see up-cval below);
;;;            constant values may be arbitrary Scheme expressions, and ,expr
;;;            escapes to Scheme here too; ,@expr splices into (list t) elements.
;;;   data  := (I n) | (B bv) | (List data ...) | (Map (k v) ...) | (Constr t data ...)
;;;            (or any Scheme expr evaluating to a data rep); ,expr escapes to
;;;            Scheme, ,@expr splices into List/Map/Constr element lists.
;;;
;;; Public entry points:
;;;   (uplc term)                  -> named AST (pre de-Bruijn)
;;;   (uplc-program (maj min pat) term) -> #(program #(maj min pat) named-ast)
;;;   (uplc-eval term)             -> result term (de-Bruijn), via the CEK machine
;;;   (uplc-run  term)             -> pretty-printed result program (string)
;;; Helpers:
;;;   (hex "deadbeef")             -> bytevector, for (con bytestring ...)

(library (plutuss dsl)
  (export uplc uplc-program uplc-pretty uplc-eval uplc-run hex ->bytes
          ;; auxiliary keywords (so syntax-rules literals match at the use site;
          ;; delay/force/case/error/list/string and unquote/unquote-splicing
          ;; match via (chezscheme); pair is bound nowhere else, so it must be
          ;; defined and exported here or it never matches across the library
          ;; boundary).
          lam con builtin constr I B List Map Constr
          integer bytestring bool unit data pair)
  (import (chezscheme) (plutuss base) (plutuss builtins)
          (plutuss frontend) (plutuss machine) (plutuss output))

  ;; Auxiliary keyword bindings — used only as syntax-rules literals below.
  (define-syntax lam (syntax-rules ()))
  (define-syntax con (syntax-rules ()))
  (define-syntax builtin (syntax-rules ()))
  (define-syntax constr (syntax-rules ()))
  (define-syntax I (syntax-rules ()))
  (define-syntax B (syntax-rules ()))
  (define-syntax List (syntax-rules ()))
  (define-syntax Map (syntax-rules ()))
  (define-syntax Constr (syntax-rules ()))
  (define-syntax integer (syntax-rules ()))
  (define-syntax bytestring (syntax-rules ()))
  (define-syntax bool (syntax-rules ()))
  (define-syntax unit (syntax-rules ()))
  (define-syntax data (syntax-rules ()))
  (define-syntax pair (syntax-rules ()))

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

;; ---- splicing -------------------------------------------------------------
;; ,e (unquote) escapes to Scheme wherever a term, constant value, or data
;; node is expected; ,@e (unquote-splicing) splices a Scheme list into the
;; list-shaped positions (case branches, constr fields, application arguments,
;; (list t) constant elements, data List/Map/Constr elements).

;; Scheme-expression slots (constr tags, I/B payloads) take their argument
;; verbatim; unq additionally tolerates a redundant leading unquote there.
(define-syntax unq
  (syntax-rules (unquote)
    ((_ (unquote e)) e)
    ((_ e) e)))

;; (uplc-list (t ...)) -> expression yielding the list of term values,
;; honoring ,@ splices among the elements.
(define-syntax uplc-list
  (syntax-rules (unquote-splicing)
    ((_ ()) '())
    ((_ ((unquote-splicing e) . rest)) (append e (uplc-list rest)))
    ((_ (t . rest)) (cons (uplc t) (uplc-list rest)))))

;; Left-associated application spine over the argument forms; a ,@ splice
;; folds its (runtime) list into the spine at that point.
(define-syntax uplc-app
  (syntax-rules (unquote-splicing)
    ((_ acc ()) acc)
    ((_ acc ((unquote-splicing e) . rest))
     (uplc-app (fold-left (lambda (f a) (vector 'app f a)) acc e) rest))
    ((_ acc (a . rest)) (uplc-app (vector 'app acc (uplc a)) rest))))

;; No-rules marker: expanding (uplc ,@e) outside a list position is an error.
(define-syntax uplc-unquote-splicing-outside-list (syntax-rules ()))

;; PlutusData builder.
(define-syntax up-data
  (syntax-rules (I B List Map Constr unquote)
    ((_ (unquote e))   e)
    ((_ (I n))         (list 'I (unq n)))
    ((_ (B bv))        (list 'B (->bytes (unq bv))))
    ((_ (List d ...))  (list 'List (up-data-list (d ...))))
    ((_ (Map e ...))   (list 'Map (up-data-map (e ...))))
    ((_ (Constr t d ...)) (list 'Constr (unq t) (up-data-list (d ...))))
    ((_ e)             e)))                ; splice a precomputed data rep

(define-syntax up-data-list
  (syntax-rules (unquote-splicing)
    ((_ ()) '())
    ((_ ((unquote-splicing e) . rest)) (append e (up-data-list rest)))
    ((_ (d . rest)) (cons (up-data d) (up-data-list rest)))))

(define-syntax up-data-map
  (syntax-rules (unquote-splicing)
    ((_ ()) '())
    ((_ ((unquote-splicing e) . rest)) (append e (up-data-map rest)))
    ((_ ((k v) . rest)) (cons (cons (up-data k) (up-data v)) (up-data-map rest)))))

;; Bare constant value of a given type (constants are (type . value); the
;; `con` rule pairs this with the quoted type). Used at top level by
;; (con type value) and recursively for list/pair element values.
(define-syntax up-cval
  (syntax-rules (integer bytestring string bool unit data list pair unquote)
    ((_ t (unquote e)) e)                 ; ,expr escapes to Scheme at any type
    ((_ integer v)    v)
    ((_ bytestring v) (->bytes v))
    ((_ string v)     v)
    ((_ bool v)       v)
    ((_ unit v)       '())
    ((_ data v)       (up-data v))
    ((_ (list t) (e ...))
     (up-cval-list t (e ...)))
    ((_ (pair a b) (x y))
     (cons (up-cval a x) (up-cval b y)))
    ((_ (pair a b) (x . y))
     (cons (up-cval a x) (up-cval b y)))))

(define-syntax up-cval-list
  (syntax-rules (unquote-splicing)
    ((_ t ()) '())
    ((_ t ((unquote-splicing e) . rest)) (append e (up-cval-list t rest)))
    ((_ t (x . rest)) (cons (up-cval t x) (up-cval-list t rest)))))

;; Term builder.
(define-syntax uplc
  (syntax-rules (lam delay force con builtin error constr case
                 unquote unquote-splicing)
    ((_ (unquote e))      e)
    ((_ (unquote-splicing e)) (uplc-unquote-splicing-outside-list))
    ((_ (lam (unquote x) body)) (vector 'lam x (uplc body)))
    ((_ (lam x body))     (vector 'lam (symbol->string 'x) (uplc body)))
    ((_ (delay t))        (vector 'delay (uplc t)))
    ((_ (force t))        (vector 'force (uplc t)))
    ((_ (con type val))   (vector 'con (cons (uplc-type type) (up-cval type val))))
    ((_ (builtin name))   (vector 'builtin (dsl-builtin 'name)))
    ((_ (error))          (vector 'uerror))
    ((_ (constr tag f ...)) (vector 'constr (unq tag) (uplc-list (f ...))))
    ((_ (case s b ...))   (vector 'case (uplc s) (uplc-list (b ...))))
    ((_ (f a as ...))     (uplc-app (uplc f) (a as ...)))  ; left-assoc application
    ((_ x)                (vector 'var (symbol->string 'x)))))

(define-syntax uplc-program
  (syntax-rules ()
    ((_ (maj min pat) term) (vector 'program (vector maj min pat) (uplc term)))))

;; Evaluate an already-built AST (the value produced by `uplc`). These are
;; FUNCTIONS, not macros: pass a term value, e.g. (uplc-eval (uplc (lam x x)))
;; or, when the term is already bound, (uplc-eval my-term).
(define (uplc-eval ast) (machine-run (name->debruijn ast)))

(define (string->sexp s)
  (let ([p (open-input-string s)])
    (read p)))

(define (uplc-pretty ast) (pretty-print (string->sexp (pretty-term ast))))

;; Evaluate and pretty-print the result as a 1.1.0 program string.
(define (uplc-run ast) (pretty-program (vector 1 1 0) (uplc-eval ast))))
