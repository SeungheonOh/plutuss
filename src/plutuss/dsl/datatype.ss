#| dsl/datatype.ss - create datatype related operations for uplc.

This module defines macros for handling datatype creation and matching.

(define-plutus-type <name> (SOP|Data)
  (<constructor-name> <field-name-1> <field-name-2> ...)
  (<constructor-name> <field-name-1> <field-name-2> ...)
  ...)

This will generate
(make-<name> (constructor-name field1 field2 ...)) which returns a UPLC node
(match-<name> <uplc-term>
  [(constructor-name1 field1 field2) body]
  [(constructor-name2 field1 field2) body]
  [else body])
which takes uplc term that's assumed to return defined type and handlers for each constructors and
return uplc node that handles according to the handlers.

|#

(library (plutuss dsl datatype)
  (export define-plutus-type define-plutus-type-Data define-plutus-type-SOP)
  (import (chezscheme) (plutuss base) (plutuss dsl))

(meta define (indexp f lst)
  (let loop ((rest-lst lst) (index 0))
    (cond
     ((null? rest-lst) #f)
     ((f (car rest-lst)) index)
     (else (loop (cdr rest-lst) (+ index 1))))))

(meta define (prefix-id prefix id)
  (datum->syntax id
                 (string->symbol
                  (string-append prefix
                                 (symbol->string (syntax->datum id))))))

(define (single-fixed-arity p)
  (let ([mask (procedure-arity-mask p)])
    (unless (and (> mask 0)
                 (= (bitwise-and mask (- mask 1)) 0))
      (assertion-violation 'single-fixed-arity
                           "procedure does not have exactly one fixed arity"
                           p))
    (let loop ([n 0] [m mask])
      (if (= m 1)
          n
          (loop (+ n 1)
                (quotient m 2))))))

(meta define (mkDataMatchHandler ctors val handler)
      (syntax-case handler ()
        [(ctor ((binder fieldname) ...) body)
         (let* ([ctor-idx (indexp (lambda (x) (eq? (syntax->datum (car x)) (syntax->datum #'ctor))) ctors)]
                [_ (unless ctor-idx (syntax-error #'ctor "Unknown constructor:"))]
                [ctor-fields (cdr (list-ref ctors ctor-idx))]
                [bs
                 (sort
                  (lambda (x y) (< (cadr x) (cadr y)))
                  (map
                   (lambda (b f)
                     (let ([i (indexp (lambda (x) (eq? (syntax->datum x) (syntax->datum f))) ctor-fields)])
                       (unless i (syntax-error f "Try to match unknown field:"))
                       (list b i)))
                   #'(binder ...) #'(fieldname ...)))]
                [h
                 (let loop ([idx 0]
                            [lastBindIdx 0]
                            [lastBindTerm val]
                            [bs bs]
                            [acc '()])
                   (cond
                    [(null? bs)
                     (with-syntax ([(binder ...)
                                    (map car (reverse acc))]
                                   [(corres ...)
                                    (map cadr (reverse acc))])
                       #'(,(let ([binder corres] ...)
                             (uplc body))))]
                    [(eq? (cadar bs) idx)
                     (let* ([current-term
                             (let loop ([n (- idx lastBindIdx)] [expr lastBindTerm])
                               (if (zero? n)
                                   expr
                                   (loop (- n 1) #`(case #,expr (lam x (lam xs xs))))))
                             ]
                            [new-bind-name (car (generate-temporaries #'(newBinds)))])
                       (cond
                        [(null? (cdr bs))
                         (loop
                          (+ idx 1) idx new-bind-name (cdr bs)
                          (cons (list (caar bs) #`(uplc (case #,current-term (lam x (lam xs x))))) acc))]
                        [(= 0 idx)
                         (loop
                          (+ idx 1) idx current-term (cdr bs)
                          (cons
                           (list
                            (caar bs)
                            #`(uplc (case #,current-term (lam x (lam xs x))))
                            ) acc))
                         ]
                        [else
                         #`([(lam #,new-bind-name
                                  #,@(loop
                                      (+ idx 1) idx new-bind-name (cdr bs)
                                      (cons
                                       (list
                                        (caar bs)
                                        #`(uplc (case #,new-bind-name (lam x (lam xs x))))
                                        ) acc)))
                             #,current-term])]))]
                    [else (loop (+ idx 1) lastBindIdx lastBindTerm bs acc)])
                   )])
           #`(#,ctor-idx #,@h)
           )
         ]))

(define-syntax define-plutus-type-Data
  (lambda (stx)
    (define (normalize ctor)
      (syntax-case ctor ()
        [name
         (identifier? #'name)
         #'(name)]
        [(name fields ...)
         #'(name fields ...)]))

    (define (constructorDef ctor i)
      (syntax-case ctor ()
        [(ctor-name fields ...)
         (with-syntax ([mk-name (prefix-id "mk" #'ctor-name)])
           (if (null? (syntax->list #'(fields ...)))
               #`(define-syntax mk-name
                   (lambda stx
                     (syntax-case stx ()
                         [_ #'(uplc (con data (Constr #,i)))]
                         [(_) #'(uplc (con data (Constr #,i)))]
                       )))
               (with-syntax
                   ([field-list
                     (fold-right
                      (lambda (field acc)
                        #`[(force (builtin mkCons)) #,field #,acc])
                      #'(con (list data) ())
                      (syntax->list #'(fields ...)))])
                 #`(define-syntax mk-name
                     (syntax-rules ()
                       [(_ fields ...)
                        (uplc [(builtin constrData) (con integer #,i) field-list])]
                       )))))]))

    (define (constructorDefs ctors)
      (let loop ([ctors ctors] [i 0])
        (if (null? ctors)
            '()
            (cons (constructorDef (car ctors) i)
                  (loop (cdr ctors) (+ i 1))))))

    (define (mkMatch match-name ctors)
      #`(define-syntax #,match-name
          (lambda (stx)
            (define ctors '(#,@(map (lambda (ctor) #`(#,@ctor)) ctors)))
            (syntax-case stx ()
              [(_ val handlers (... ...))
               (with-syntax ([(constr-d idx) (generate-temporaries #'(constr-d idx))])
                 (let* ([expanded-handlers
                         (sort
                          (lambda (x y) (< (car x) (car y)))
                          (map (lambda (h)
                                 (mkDataMatchHandler ctors #'constr-d h))
                               (syntax->list #'(handlers (... ...)))))]
                        [expanded-handlers-complete
                         (let loop ([is (iota (length ctors))] [hs expanded-handlers] [acc '()])
                           (cond
                            [(null? is) (reverse acc)]
                            [(and (pair? hs) (= (car is) (caar hs))) (loop (cdr is) (cdr hs) (cons (cadar hs) acc))]
                            [else (loop (cdr is) hs (cons #'(error) acc))]
                            ))])
                   #`(uplc (case [(builtin unConstrData) val]
                             (lam idx
                                  (lam constr-d
                                       (case idx #,@expanded-handlers-complete)
                                       ))))))]))))

    (syntax-case stx ()
      [(_ name ctor ...)
       (with-syntax ([match-name (prefix-id "match" #'name)])
         (let* ([ctors (map normalize (syntax->list #'(ctor ...)))])
           #`(begin
               #,@(constructorDefs ctors)
               #,(mkMatch #'match-name ctors)
               )))])))

;|#--------------------------------------------------------------------------------#|

(define-syntax define-plutus-type-SOP
  (lambda (stx)
    (define (normalize ctor)
      (syntax-case ctor ()
        [name
         (identifier? #'name)
         #'(name)]
        [(name fields ...)
         #'(name fields ...)]))

    (define (constructorDef ctor i)
      (syntax-case ctor ()
        [(ctor-name fields ...)
         (with-syntax ([mk-name (prefix-id "mk" #'ctor-name)])
           (if (null? (syntax->list #'(fields ...)))
               #`(define-syntax mk-name
                   (lambda (stx)
                     (syntax-case stx ()
                         [_ #'(uplc (constr #,i))]
                         [(_) #'(uplc (constr #,i))]
                       )))
               #`(define-syntax mk-name
                    (lambda (stx)
                     (syntax-case stx ()
                         [(_ fields ...) #'(uplc (constr #,i fields ...))]
                       )))
               ))]))

    (define (constructorDefs ctors)
      (let loop ([ctors ctors] [i 0])
        (if (null? ctors)
            '()
            (cons (constructorDef (car ctors) i)
                  (loop (cdr ctors) (+ i 1))))))

    (define (mkMatch match-name ctors)
      #`(define-syntax #,match-name
          (lambda (stx)
            (define ctors '(#,@(map (lambda (ctor) #`(#,@ctor)) ctors)))
            (syntax-case stx ()
              [(_ val handlers (... ...))
               (let* ([hs
                       (map
                        (lambda (h)
                          (syntax-case h ()
                            [(ctor ((binder fieldname) (... ...)) body)
                             (with-syntax ([(ubinder (... ...))
                                            (generate-temporaries #'(binder (... ...)))])
                               (let* ([ctor-idx
                                       (indexp
                                        (lambda (x)
                                          (eq? (syntax->datum (car x)) (syntax->datum #'ctor)))
                                        ctors)]
                                      [_ (unless ctor-idx (syntax-error #'ctor "Unknown constructor:"))]
                                      [ctor-fields (cdr (list-ref ctors ctor-idx))]
                                      [bwi
                                       (sort
                                        (lambda (x y) (< (cadr x) (cadr y)))
                                        (map
                                         (lambda (b f)
                                           (let ([i (indexp
                                                     (lambda (x)
                                                       (eq? (syntax->datum x) (syntax->datum f)))
                                                     ctor-fields)])
                                             (unless i (syntax-error f "Try to match unknown field:"))
                                             (list b i)))
                                         #'(ubinder (... ...)) #'(fieldname (... ...))))])
                                 (list ctor-idx (let loop ([is (iota (length ctor-fields))] [bs bwi])
                                          (cond
                                           [(null? is)
                                            (with-syntax ([(corres (... ...))
                                                           (map (lambda (x) #`(uplc #,(car x))) bwi)])
                                              #',(let ([binder corres] (... ...))
                                                   (uplc body))
                                              )
                                            ]
                                           [(null? bs)
                                            #`(lam
                                               unused
                                               #,(loop (cdr is) bs))]
                                           [(= (car is) (cadar bs))
                                            #`(lam #,(caar bs) #,(loop (cdr is) (cdr bs)))])
                                          ))
                                 ))]))
                        (syntax->list #'(handlers (... ...)))
                        )]
                      [hs (sort (lambda (x y) (< (car x) (car y))) hs)]
                      [hsall
                       (let loop ([cs (iota (length ctors))] [hs hs])
                         (cond
                          [(null? cs) #'()]
                          [(null? hs) #`((error) #,@(loop (cdr cs) hs))]
                          [(= (car cs) (caar hs)) #`(#,(cadar hs) #,@(loop (cdr cs) (cdr hs)))]
                          [else #`((error) #,@(loop (cdr cs) hs))])
                         )]
                      )
                 #`(uplc (case val #,@hsall))
                 )]))))

    (syntax-case stx ()
      [(_ name ctor ...)
       (with-syntax ([match-name (prefix-id "match" #'name)])
         (let* ([ctors (map normalize (syntax->list #'(ctor ...)))])
           #`(begin
               #,@(constructorDefs ctors)
               #,(mkMatch #'match-name ctors)
               )))])))

(define-syntax define-plutus-type
  (syntax-rules (SOP Data)
    [(_ SOP (ctor field ...) ...) #'(40)]
    ))

)  ; library (plutuss dsl datatype)

;; Worked demos live in the examples; see:
;;   src/plutuss/dsl/example-option.ss   — the original Option smoke test
;;   src/plutuss/dsl/example-interval.ss — PlutusLedgerApi.V1.Interval port
