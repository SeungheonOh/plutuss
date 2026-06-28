;;; (plutuss refine) -- refinement checking over UPLC predicates.
;;;
;;; Predicates are ordinary UPLC terms.  A predicate holds only when symbolic
;;; evaluation succeeds with Bool true; Bool false, UPLC error, timeout, and
;;; non-Bool success are all refinement violations.
(library (plutuss refine)
  (export
   ;; registries and syntax
   current-refinement-fuel clear-refinements!
   define-upred define/refined define-refined verify/refine
   register-upred! lookup-upred upred?
   register-refined! lookup-refined refined-function?
   refined-function-term refined-function-body
   ;; predicate evaluation
   eval-predicate eval-predicate-call
   predicate-true-cond predicate-false-cond predicate-error-cond
   predicate-timeout-cond predicate-non-bool-cond predicate-violation-cond
   ;; verification
   check-refinement verify-refined-function
   refinement-verification? refinement-verification-name refinement-verification-ok?
   refinement-verification-obligations refinement-verification-compiled
   refinement-obligation? refinement-obligation-name refinement-obligation-kind
   refinement-obligation-expected refinement-obligation-actual
   refinement-obligation-ok? refinement-obligation-smtlib
   refinement-report display-refinement-report
   ;; utility exposed for advanced callers
   term->debruijn/free normalize-refinement-spec normalize-return-spec)
  (import (chezscheme)
          (plutuss base)
          (plutuss smt)
          (plutuss compile))

  (define current-refinement-fuel (make-parameter 5000))

  (define upreds (make-eq-hashtable))
  (define refined-functions (make-eq-hashtable))

  (define (clear-refinements!)
    (hashtable-clear! upreds)
    (hashtable-clear! refined-functions))

  ;;; ---- small helpers ----------------------------------------------------
  (define (filter-map f xs)
    (let loop ((xs xs) (acc '()))
      (cond ((null? xs) (reverse acc))
            ((f (car xs)) => (lambda (v) (loop (cdr xs) (cons v acc))))
            (else (loop (cdr xs) acc)))))
  (define (append-map f xs) (apply append (map f xs)))
  (define (string-join xs sep)
    (cond ((null? xs) "")
          ((null? (cdr xs)) (car xs))
          (else
           (let ((out (open-output-string)))
             (put-string out (car xs))
             (for-each (lambda (x) (put-string out sep) (put-string out x)) (cdr xs))
             (get-output-string out)))))
  (define (->symbol x who)
    (cond ((symbol? x) x)
          ((string? x) (string->symbol x))
          (else (error who "expected a symbol/string name" x))))
  (define (name->string x)
    (cond ((symbol? x) (symbol->string x))
          ((string? x) x)
          (else (error 'name->string "expected symbol/string" x))))
  (define (where-marker? x)
    (and (symbol? x) (string=? (symbol->string x) "where")))
  (define (fuel-arg maybe)
    (if (null? maybe) (current-refinement-fuel) (car maybe)))

  ;;; ---- small FFI-free UPLC syntax for refinement declarations ----------
  ;; This intentionally emits builtin names as symbols instead of descriptor
  ;; records, so refinement checking does not load native crypto libraries.
  (define (->bytes-lite v)
    (cond ((bytevector? v) v)
          ((list? v) (apply bytevector v))
          (else (error 'refine-uplc "bytestring expects a bytevector or byte list" v))))

  (define-syntax runq
    (syntax-rules (unquote)
      ((_ (unquote e)) e)
      ((_ e) e)))

  (define-syntax ruplc-type
    (syntax-rules () ((_ t) (quote t))))

  (define-syntax ruplc-cval
    (syntax-rules (integer bytestring string bool unit data list pair unquote)
      ((_ t (unquote e)) e)
      ((_ integer v) v)
      ((_ bytestring v) (->bytes-lite v))
      ((_ string v) v)
      ((_ bool v) v)
      ((_ unit v) '())
      ((_ data v) v)
      ((_ (list t) (e ...)) (list (ruplc-cval t e) ...))
      ((_ (pair a b) (x y)) (cons (ruplc-cval a x) (ruplc-cval b y)))
      ((_ (pair a b) (x . y)) (cons (ruplc-cval a x) (ruplc-cval b y)))))

  (define-syntax ruplc-list
    (syntax-rules (unquote-splicing)
      ((_ ()) '())
      ((_ ((unquote-splicing e) . rest)) (append e (ruplc-list rest)))
      ((_ (t . rest)) (cons (ruplc t) (ruplc-list rest)))))

  (define-syntax ruplc-app
    (syntax-rules (unquote-splicing)
      ((_ acc ()) acc)
      ((_ acc ((unquote-splicing e) . rest))
       (ruplc-app (fold-left (lambda (f a) (vector 'app f a)) acc e) rest))
      ((_ acc (a . rest)) (ruplc-app (vector 'app acc (ruplc a)) rest))))

  (define-syntax ruplc
    (lambda (stx)
      (define (literal datum ctx) (datum->syntax ctx datum))
      (define (head-name x)
        (and (identifier? x)
             (let ((d (syntax->datum x))) (and (symbol? d) d))))
      (define (unquote-form? x)
        (syntax-case x ()
          ((h e) (let ((h* (head-name #'h)))
                   (and h* (eq? h* 'unquote))))
          (_ #f)))
      (define (unquote-expr x)
        (syntax-case x () ((_ e) #'e)))
      (define (binder-expr x)
        (if (unquote-form? x)
            (unquote-expr x)
            (let ((d (syntax->datum x)))
              (unless (symbol? d) (syntax-error x "lambda binder must be an identifier"))
              (literal (symbol->string d) x))))
      (define (cval-expr ty val)
        (if (unquote-form? val)
            (unquote-expr val)
            (let ((td (syntax->datum ty)))
              (cond
               ((eq? td 'bytestring) #`(->bytes-lite #,val))
               ((eq? td 'unit) #''())
               ((and (pair? td) (eq? (car td) 'list))
                (let ((items (syntax->list val)))
                  (if items
                      #`(list #,@(map (lambda (x) (cval-expr (literal (cadr td) ty) x)) items))
                      val)))
               ((and (pair? td) (eq? (car td) 'pair))
                (syntax-case val ()
                  ((a b) #`(cons #,(cval-expr (literal (cadr td) ty) #'a)
                                  #,(cval-expr (literal (caddr td) ty) #'b)))
                  ((a . b) #`(cons #,(cval-expr (literal (cadr td) ty) #'a)
                                    #,(cval-expr (literal (caddr td) ty) #'b)))
                  (_ val)))
               (else val)))))
      (define (term-list-expr xs)
        #`(list #,@(map parse xs)))
      (define (app-chain f args)
        (if (null? args)
            f
            (app-chain #`(vector 'app #,f #,(parse (car args))) (cdr args))))
      (define (parse x)
        (if (unquote-form? x)
            (unquote-expr x)
            (syntax-case x ()
              (id
               (identifier? #'id)
               (let ((d (syntax->datum #'id)))
                 #`(vector 'var #,(literal (symbol->string d) #'id))))
              ((h . rest)
               (let ((h* (head-name #'h))
                     (parts (syntax->list #'rest)))
                 (case h*
                   ((lam)
                    (unless (and parts (= (length parts) 2))
                      (syntax-error x "lam expects a binder and a body"))
                    #`(vector 'lam #,(binder-expr (car parts)) #,(parse (cadr parts))))
                   ((delay)
                    (unless (and parts (= (length parts) 1))
                      (syntax-error x "delay expects one term"))
                    #`(vector 'delay #,(parse (car parts))))
                   ((force)
                    (unless (and parts (= (length parts) 1))
                      (syntax-error x "force expects one term"))
                    #`(vector 'force #,(parse (car parts))))
                   ((con)
                    (unless (and parts (= (length parts) 2))
                      (syntax-error x "con expects a type and a value"))
                    #`(vector 'con
                              (cons '#,(literal (syntax->datum (car parts)) (car parts))
                                    #,(cval-expr (car parts) (cadr parts)))))
                   ((builtin)
                    (unless (and parts (= (length parts) 1))
                      (syntax-error x "builtin expects one name"))
                    #`(vector 'builtin '#,(literal (syntax->datum (car parts)) (car parts))))
                   ((error)
                    (unless (null? parts) (syntax-error x "error expects no arguments"))
                    #`(vector 'uerror))
                   ((constr)
                    (unless (and parts (>= (length parts) 1))
                      (syntax-error x "constr expects a tag"))
                    #`(vector 'constr #,(car parts) #,(term-list-expr (cdr parts))))
                   ((case)
                    (unless (and parts (>= (length parts) 1))
                      (syntax-error x "case expects a scrutinee"))
                    #`(vector 'case #,(parse (car parts)) #,(term-list-expr (cdr parts))))
                   (else
                    (unless parts (syntax-error x "empty application"))
                    (app-chain (parse #'h) parts)))))
              (_ (syntax-error x "bad UPLC term")))))
      (syntax-case stx ()
        ((_ body) (parse #'body)))))

  ;;; ---- named/free variable conversion ----------------------------------
  ;; Like frontend:name->debruijn, but starts with a caller-supplied free scope.
  ;; Scope order matches the symbolic compiler environment: first name is Var 1.
  (define (term->debruijn/free free-names term)
    (define initial-scope (map name->string free-names))
    (define (index-of name scope)
      (let loop ((s scope) (i 1))
        (cond ((null? s) #f)
              ((string=? (car s) name) i)
              (else (loop (cdr s) (fx+ i 1))))))
    (define (conv t scope)
      (case (vector-ref t 0)
        ((var)
         (let ((v (vector-ref t 1)))
           (cond ((integer? v) t)
                 ((string? v)
                  (let ((idx (index-of v scope)))
                    (unless idx (eval-failure (string-append "free variable: " v)))
                    (vector 'var idx)))
                 (else (error 'term->debruijn/free "bad variable" t)))))
        ((lam)
         (let ((nm (vector-ref t 1)))
           (vector 'lam nm (conv (vector-ref t 2) (cons nm scope)))))
        ((app) (vector 'app (conv (vector-ref t 1) scope) (conv (vector-ref t 2) scope)))
        ((delay) (vector 'delay (conv (vector-ref t 1) scope)))
        ((force) (vector 'force (conv (vector-ref t 1) scope)))
        ((con builtin uerror) t)
        ((case) (vector 'case (conv (vector-ref t 1) scope)
                        (map (lambda (b) (conv b scope)) (vector-ref t 2))))
        ((constr) (vector 'constr (vector-ref t 1)
                          (map (lambda (f) (conv f scope)) (vector-ref t 2))))
        (else (error 'term->debruijn/free "bad node" t))))
    (conv term initial-scope))

  (define (wrap-named-lams names body)
    (let loop ((names (reverse names)) (body body))
      (if (null? names)
          body
          (loop (cdr names) (vector 'lam (name->string (car names)) body)))))

  ;;; ---- specs ------------------------------------------------------------
  (define (make-rspec name kind preds) (vector 'rspec name kind preds))
  (define (rspec-name s)  (vector-ref s 1))
  (define (rspec-kind s)  (vector-ref s 2))
  (define (rspec-preds s) (vector-ref s 3))

  (define (normalize-pred-call p)
    (unless (and (pair? p) (symbol? (car p)))
      (error 'normalize-pred-call "predicate call must be (name arg ...)" p))
    p)

  (define (parse-pred-rest rest)
    (let loop ((xs rest) (acc '()))
      (cond
       ((null? xs) (reverse acc))
       ((where-marker? (car xs))
        (when (null? (cdr xs)) (error 'normalize-refinement-spec "missing predicate after #:where"))
        (loop (cddr xs) (cons (normalize-pred-call (cadr xs)) acc)))
       ((pair? (car xs))
        (loop (cdr xs) (cons (normalize-pred-call (car xs)) acc)))
       (else (error 'normalize-refinement-spec "expected #:where or predicate call" (car xs))))))

  (define (normalize-refinement-spec spec)
    (unless (and (pair? spec) (pair? (cdr spec)))
      (error 'normalize-refinement-spec "expected (name kind ...)" spec))
    (make-rspec (->symbol (car spec) 'normalize-refinement-spec)
                (cadr spec)
                (parse-pred-rest (cddr spec))))

  (define normalize-return-spec normalize-refinement-spec)
  (define (normalize-specs specs) (map normalize-refinement-spec specs))
  (define (spec-names specs) (map rspec-name specs))
  (define (spec-inputs specs)
    (map (lambda (s) (cons (symbol->string (rspec-name s)) (rspec-kind s))) specs))

  ;;; ---- records ----------------------------------------------------------
  (define (make-upred name args body-named body-db fuel)
    (vector 'upred name args body-named body-db fuel))
  (define (upred? x) (and (vector? x) (eq? (vector-ref x 0) 'upred)))
  (define (upred-name p)       (vector-ref p 1))
  (define (upred-args p)       (vector-ref p 2))
  (define (upred-body-named p) (vector-ref p 3))
  (define (upred-body p)       (vector-ref p 4))
  (define (upred-fuel p)       (vector-ref p 5))

  (define (register-upred! name arg-specs body . maybe-fuel)
    (let* ((nm (->symbol name 'register-upred!))
           (args (normalize-specs arg-specs))
           (fuel (fuel-arg maybe-fuel))
           (body-db (term->debruijn/free (spec-names args) body))
           (p (make-upred nm args body body-db fuel)))
      (hashtable-set! upreds nm p)
      p))

  (define (lookup-upred name)
    (let ((p (hashtable-ref upreds (->symbol name 'lookup-upred) #f)))
      (unless p (error 'lookup-upred "unknown refinement predicate" name))
      p))

  (define (make-refined name inputs ret body-named body-db fuel)
    (vector 'refined name inputs ret body-named body-db fuel))
  (define (refined-function? x) (and (vector? x) (eq? (vector-ref x 0) 'refined)))
  (define (refined-name f)       (vector-ref f 1))
  (define (refined-inputs f)     (vector-ref f 2))
  (define (refined-return f)     (vector-ref f 3))
  (define (refined-body-named f) (vector-ref f 4))
  (define (refined-function-body f) (vector-ref f 5))
  (define (refined-fuel f)       (vector-ref f 6))

  (define (refined-function-term f)
    (let ((rf (if (refined-function? f) f (lookup-refined f))))
      (wrap-named-lams (spec-names (refined-inputs rf)) (refined-body-named rf))))

  (define (register-refined! name input-specs return-spec body . maybe-fuel)
    (let* ((nm (->symbol name 'register-refined!))
           (inputs (normalize-specs input-specs))
           (ret (normalize-return-spec return-spec))
           (fuel (fuel-arg maybe-fuel))
           (body-db (term->debruijn/free (spec-names inputs) body))
           (f (make-refined nm inputs ret body body-db fuel)))
      (hashtable-set! refined-functions nm f)
      f))

  (define (lookup-refined name)
    (let ((f (hashtable-ref refined-functions (->symbol name 'lookup-refined) #f)))
      (unless f (error 'lookup-refined "unknown refined function" name))
      f))

  ;;; ---- macro front-end --------------------------------------------------
  (define-syntax define-upred
    (syntax-rules ()
      ((_ name ((arg kind) ...) body)
       (define name
         (register-upred! 'name '((arg kind) ...) (ruplc body))))))

  (define-syntax define/refined
    (syntax-rules ()
      ((_ name (spec ...) returns ret body)
       (define name
         (register-refined! 'name '(spec ...) 'ret (ruplc body))))))

  (define-syntax define-refined
    (syntax-rules ()
      ((_ . rest) (define/refined . rest))))

  (define-syntax verify/refine
    (syntax-rules ()
      ((_ f) (verify-refined-function f))))

  ;;; ---- symbolic env -----------------------------------------------------
  (define (syminput-value i)  (vector-ref i 0))
  (define (syminput-consts i) (vector-ref i 1))
  (define (syminput-sides i)  (vector-ref i 2))

  (define (symbolic-env specs)
    (let* ((seeded (map (lambda (s) (mk-input (symbol->string (rspec-name s)) (rspec-kind s))) specs))
           (entries (map cons (spec-names specs) (map syminput-value seeded))))
      entries))

  (define (env-ref env name)
    (let ((p (assq (->symbol name 'env-ref) env)))
      (unless p (error 'env-ref "unknown symbolic variable" name))
      (cdr p)))

  (define (literal->symval x)
    (cond ((integer? x) (sv-const (sc-integer (s-int x))))
          ((boolean? x) (sv-const (sc-bool (s-bool x))))
          ((string? x) (sv-const (sc-string (s-str x))))
          (else #f)))

  (define (resolve-predicate-arg env x)
    (cond ((symbol? x) (env-ref env x))
          ((literal->symval x) => (lambda (v) v))
          (else (error 'resolve-predicate-arg "unsupported predicate argument" x))))

  ;;; ---- predicate evaluation --------------------------------------------
  (define (eval-predicate pred args . maybe-fuel)
    (let* ((p (if (upred? pred) pred (lookup-upred pred)))
           (fuel (if (null? maybe-fuel) (upred-fuel p) (car maybe-fuel))))
      (unless (= (length args) (length (upred-args p)))
        (error 'eval-predicate "predicate arity mismatch" (upred-name p)))
      (eval-sym fuel args (upred-body p))))

  (define (eval-predicate-call call env . maybe-fuel)
    (let* ((p (lookup-upred (car call)))
           (args (map (lambda (a) (resolve-predicate-arg env a)) (cdr call)))
           (fuel (if (null? maybe-fuel) (upred-fuel p) (car maybe-fuel))))
      (eval-predicate p args fuel)))

  (define (proj-guard* p) (vector-ref p 1))

  (define (predicate-true-cond outs) (okBoolCond outs #t))
  (define (predicate-false-cond outs) (okBoolCond outs #f))
  (define predicate-error-cond errorCond)
  (define predicate-timeout-cond timeoutCond)
  (define (predicate-non-bool-cond outs)
    (sAny
     (filter-map
      (lambda (o)
        (and (eq? (outcome-tag o) 'ok)
             (let ((b (as-bool (outcome-val o))))
               (sAll (list (outcome-pc o) (sNot (proj-guard* b)))))))
      outs)))
  (define (predicate-violation-cond outs)
    (sAny (list (predicate-false-cond outs)
                (predicate-error-cond outs)
                (predicate-timeout-cond outs)
                (predicate-non-bool-cond outs))))

  (define (input-assumptions inputs env)
    (append-map
     (lambda (s)
       (map (lambda (call)
              (predicate-true-cond (eval-predicate-call call env)))
            (rspec-preds s)))
     inputs))

  ;;; ---- type checks ------------------------------------------------------
  (define (const-unit? v)
    (and (eq? (symv-tag v) 'const)
         (eq? (vector-ref (vector-ref v 1) 0) 'unit)))

  (define (value-kind-guard v kind)
    (case kind
      ((integer) (proj-guard* (as-int v)))
      ((bool) (proj-guard* (as-bool v)))
      ((bytes bytestring) (proj-guard* (as-bytes v)))
      ((string str) (proj-guard* (as-string v)))
      ((data) (proj-guard* (as-data v)))
      ((list) (proj-guard* (as-const-list v)))
      ((unit)
       (cond ((const-unit? v) (s-bool #t))
             ((eq? (symv-tag v) 'dyn) (v-is-con "VUnit" (vector-ref v 1)))
             (else (s-bool #f))))
      ((anyV val)
       (if (encode-val? v) (s-bool #t) (s-bool #f)))
      (else (s-bool #t))))

  (define (return-type-violation outs ret)
    (sAny
     (filter-map
      (lambda (o)
        (and (eq? (outcome-tag o) 'ok)
             (sAll (list (outcome-pc o)
                         (sNot (value-kind-guard (outcome-val o) (rspec-kind ret)))))))
      outs)))

  (define (return-predicate-violation outs input-env ret)
    (let ((rname (rspec-name ret)))
      (sAny
       (append-map
        (lambda (call)
          (filter-map
           (lambda (o)
             (and (eq? (outcome-tag o) 'ok)
                  (predicate-violation-cond
                   (map-pc (outcome-pc o)
                           (eval-predicate-call call
                                                (cons (cons rname (outcome-val o)) input-env))))))
           outs))
        (rspec-preds ret)))))

  ;;; ---- obligations ------------------------------------------------------
  (define (make-obligation name kind expected actual smtlib)
    (vector 'refinement-obligation name kind expected actual smtlib))
  (define (refinement-obligation? x)
    (and (vector? x) (eq? (vector-ref x 0) 'refinement-obligation)))
  (define (refinement-obligation-name o)     (vector-ref o 1))
  (define (refinement-obligation-kind o)     (vector-ref o 2))
  (define (refinement-obligation-expected o) (vector-ref o 3))
  (define (refinement-obligation-actual o)   (vector-ref o 4))
  (define (refinement-obligation-smtlib o)   (vector-ref o 5))
  (define (refinement-obligation-ok? o)
    (eq? (refinement-obligation-expected o) (refinement-obligation-actual o)))

  (define (make-verification name ok? obligations compiled)
    (vector 'refinement-verification name ok? obligations compiled))
  (define (refinement-verification? x)
    (and (vector? x) (eq? (vector-ref x 0) 'refinement-verification)))
  (define (refinement-verification-name v)        (vector-ref v 1))
  (define (refinement-verification-ok? v)         (vector-ref v 2))
  (define (refinement-verification-obligations v) (vector-ref v 3))
  (define (refinement-verification-compiled v)    (vector-ref v 4))

  (define (labeled name cond) (cons name cond))
  (define (query-smtlib c label cond)
    (smt-script->smtlib
     (make-smt-script (compiled-consts c)
                      (compiled-sides c)
                      (list (labeled label cond)))))
  (define (run-obligation c name kind expected cond)
    (let* ((smtlib (query-smtlib c name cond))
           (actual (z3-check smtlib)))
      (make-obligation name kind expected actual smtlib)))

  (define (with-assumptions assumptions cond)
    (sAll (append assumptions (list cond))))

  (define (run-refinement-check name inputs ret body-db fuel)
    (let* ((c (uplc-symbolic-compile fuel (spec-inputs inputs) body-db))
           (outs (compiled-result c))
           (env (symbolic-env inputs))
           (assumptions (input-assumptions inputs env))
           (assume-cond (sAll assumptions)))
      (let ((obligations
             (list
              (run-obligation c "assumptions-satisfiable" 'vacuity 'sat assume-cond)
              (run-obligation c "body-does-not-error" 'safety 'unsat
                              (with-assumptions assumptions (errorCond outs)))
              (run-obligation c "body-does-not-timeout" 'fuel 'unsat
                              (with-assumptions assumptions (timeoutCond outs)))
              (run-obligation c "return-has-declared-type" 'return-type 'unsat
                              (with-assumptions assumptions (return-type-violation outs ret)))
              (run-obligation c "return-predicates-hold" 'return-refinement 'unsat
                              (with-assumptions assumptions
                                (return-predicate-violation outs env ret))))))
        (make-verification name
                           (andmap refinement-obligation-ok? obligations)
                           obligations
                           c))))

  (define (check-refinement name input-specs return-spec body . maybe-fuel)
    (let* ((inputs (normalize-specs input-specs))
           (ret (normalize-return-spec return-spec))
           (fuel (fuel-arg maybe-fuel))
           (body-db (term->debruijn/free (spec-names inputs) body)))
      (run-refinement-check (->symbol name 'check-refinement) inputs ret body-db fuel)))

  (define (verify-refined-function f)
    (let ((rf (if (refined-function? f) f (lookup-refined f))))
      (run-refinement-check (refined-name rf)
                            (refined-inputs rf)
                            (refined-return rf)
                            (refined-function-body rf)
                            (refined-fuel rf))))

  ;;; ---- reporting --------------------------------------------------------
  (define (obligation-line o)
    (string-append
     "  [" (if (refinement-obligation-ok? o) " ok " "FAIL") "] "
     (refinement-obligation-name o)
     " expected " (symbol->string (refinement-obligation-expected o))
     ", got " (symbol->string (refinement-obligation-actual o))))

  (define (refinement-report v)
    (let ((lines
           (cons
            (string-append
             "refinement " (symbol->string (refinement-verification-name v))
             ": " (if (refinement-verification-ok? v) "ok" "failed"))
            (map obligation-line (refinement-verification-obligations v)))))
      (string-append (string-join lines "\n") "\n")))

  (define (display-refinement-report v)
    (display (refinement-report v))))
