;;; (plutuss smt) — a deep-embedded SMT-LIB expression language, its sort
;;; checker, an SMT-LIB serializer, and a z3 bridge.
;;;
;;; This is the *target* of the UPLC->SMT denotational compiler in
;;; (plutuss compile).  It is a faithful Scheme port of the verified Lean
;;; development `Moist/Smt/{Syntax,Print}.lean` (utxo-company/moist): the shapes,
;;; the sort classifier, the SMT-LIB rendering, the `Data` datatype declaration,
;;; and the four Plutus integer division/modulo `define-fun`s are all reproduced
;;; verbatim, so the meaning is exactly the one those proofs are stated against.
;;;
;;; A *deep* embedding: an `smt` value is a first-order term (a tagged vector,
;;; like the rest of plutuss).  Its SMT-LIB rendering is `smt->smtlib`; trust is
;;; split there — everything up to the printed string is ordinary code, and z3's
;;; verdict on that string is the one accepted external oracle.
;;;
;;; Sorts.  Base sorts are 'int 'bool 'data 'bytes; the two builtin polymorphic
;;; type constructors are `(list S)` and `(pair A B)` — the same s-expression
;;; shape the UPLC parser already uses for list/pair constant types.  Integer
;;; arithmetic is *total* here: the partiality of divide/modulo (division by
;;; zero) and of partial projections (unIData on a non-I, headList on []) is
;;; carried separately as a definedness guard by (plutuss compile), never as a
;;; partial meaning.
;;;
;;; AST (constructors are the `smt-*` functions; tags are the leading symbols):
;;;   #(var name sort)        a free SMT variable (a symbolic input)
;;;   #(lit-i n) #(lit-b b)   integer / boolean literals
;;;   #(neg e)                integer negation
;;;   #(bnot e)               boolean negation
;;;   #(bin op a b)           binary op (op: add sub mul fdiv fmod tdiv tmod
;;;                                          le lt eq and or)
;;;   #(uop op e)             unary data/bytes op (see unop-sorts)
;;;   #(ite c a b)            if-then-else (polymorphic result)
;;;   #(mkpair a b) #(fstp e) #(sndp e)            builtin Pair ops
;;;   #(nill s) #(consl h t) #(headl s e) #(taill e) #(nulll e)   builtin Lst ops
(library (plutuss smt)
  (export
   ;; sort constructors / predicates
   smt-sort-int smt-sort-bool smt-sort-data smt-sort-bytes
   smt-sort-list smt-sort-pair smt-sort=?
   ;; expression constructors
   smt-var smt-int smt-bool smt-neg smt-not smt-bin smt-uop smt-ite
   smt-mkpair smt-fst smt-snd smt-nil smt-cons smt-head smt-tail smt-null
   ;; smart constructors / helpers
   smt-true smt-false smt-and smt-or smt-eq smt-imp smt-ne-zero smt-conj
   ;; introspection
   smt-tag smt-sort-of smt-well-sorted-bool? smt-collect-vars
   ;; serialization
   smt->sexpr smt->smtlib smt-preamble smt-data-preamble
   ;; z3 bridge
   run-z3 z3-check z3-model z3-raw)
  (import (chezscheme) (plutuss base))

  ;;; ======================================================================
  ;;; Sorts.  A sort is a symbol ('int 'bool 'data 'bytes) or one of
  ;;; (list S) / (pair A B).
  ;;; ======================================================================
  (define smt-sort-int  'int)
  (define smt-sort-bool 'bool)
  (define smt-sort-data 'data)
  (define smt-sort-bytes 'bytes)
  (define (smt-sort-list s) (list 'list s))
  (define (smt-sort-pair a b) (list 'pair a b))
  (define (smt-sort=? a b) (equal? a b))
  (define (sort-list? s) (and (pair? s) (eq? (car s) 'list)))
  (define (sort-pair? s) (and (pair? s) (eq? (car s) 'pair)))

  ;;; ======================================================================
  ;;; Expression constructors (tagged vectors).
  ;;; ======================================================================
  (define (smt-var name sort) (vector 'var name sort))
  (define (smt-int n)         (vector 'lit-i n))
  (define (smt-bool b)        (vector 'lit-b b))
  (define (smt-neg e)         (vector 'neg e))
  (define (smt-not e)         (vector 'bnot e))
  (define (smt-bin op a b)    (vector 'bin op a b))
  (define (smt-uop op e)      (vector 'uop op e))
  (define (smt-ite c a b)     (vector 'ite c a b))
  (define (smt-mkpair a b)    (vector 'mkpair a b))
  (define (smt-fst e)         (vector 'fstp e))
  (define (smt-snd e)         (vector 'sndp e))
  (define (smt-nil s)         (vector 'nill s))
  (define (smt-cons h t)      (vector 'consl h t))
  (define (smt-head s e)      (vector 'headl s e))
  (define (smt-tail e)        (vector 'taill e))
  (define (smt-null e)        (vector 'nulll e))

  (define (smt-tag e) (vector-ref e 0))

  ;;; ---- smart constructors (readability for the builtins table) ----
  (define smt-true  (smt-bool #t))
  (define smt-false (smt-bool #f))
  (define (smt-and a b) (smt-bin 'and a b))
  (define (smt-or  a b) (smt-bin 'or  a b))
  (define (smt-eq  a b) (smt-bin 'eq  a b))
  (define (smt-imp a b) (smt-bin 'or (smt-not a) b))
  (define (smt-ne-zero e) (smt-not (smt-bin 'eq e (smt-int 0))))
  (define (smt-conj es)
    (cond ((null? es) smt-true)
          ((null? (cdr es)) (car es))
          (else (smt-and (car es) (smt-conj (cdr es))))))

  ;;; ======================================================================
  ;;; Sort classification.  `(smt-sort-of e)` returns the sort of `e`, or #f
  ;;; if `e` is ill-sorted.  Everything (plutuss compile) emits is well-sorted
  ;;; by construction; `smt-sort-of` is what the builtin table consults to
  ;;; refuse on a sort mismatch.  Mirrors `SmtExpr.sortOf`.
  ;;; ======================================================================

  ;; result sort of a binary op given its (common) operand sort, or #f
  (define (binop-result op s)
    (case op
      ((add sub mul fdiv fmod tdiv tmod) (and (eq? s 'int) 'int))
      ((le lt) (and (eq? s 'int) 'bool))
      ((eq) (and (memq s '(int bool data bytes)) 'bool))
      ((and or) (and (eq? s 'bool) 'bool))
      (else #f)))

  ;; (operand-sort . result-sort) of a unary op
  (define (unop-sorts op)
    (case op
      ((idata) (cons 'int 'data))     ((bdata) (cons 'bytes 'data))
      ((unidata) (cons 'data 'int))   ((unbdata) (cons 'data 'bytes))
      ((constr-tag) (cons 'data 'int)) ((len-bytes) (cons 'bytes 'int))
      ((isi isb isconstr islist ismap) (cons 'data 'bool))
      ((dargs) (cons 'data (list 'list 'data)))
      ((ditems) (cons 'data (list 'list 'data)))
      ((dentries) (cons 'data (list 'list (list 'pair 'data 'data))))
      (else (cons #f #f))))

  (define (smt-sort-of e)
    (match e
      ((var _ s) s)
      ((lit-i _) 'int)
      ((lit-b _) 'bool)
      ((neg a) (and (eq? (smt-sort-of a) 'int) 'int))
      ((bnot a) (and (eq? (smt-sort-of a) 'bool) 'bool))
      ((bin op a b)
       (let ((sa (smt-sort-of a)) (sb (smt-sort-of b)))
         (and sa sb (smt-sort=? sa sb) (binop-result op sa))))
      ((uop op a)
       (let ((s (smt-sort-of a)) (io (unop-sorts op)))
         (and s (car io) (smt-sort=? s (car io)) (cdr io))))
      ((ite c a b)
       (let ((sc (smt-sort-of c)) (sa (smt-sort-of a)) (sb (smt-sort-of b)))
         (and (eq? sc 'bool) sa sb (smt-sort=? sa sb) sa)))
      ((mkpair a b)
       (let ((sa (smt-sort-of a)) (sb (smt-sort-of b)))
         (and sa sb (list 'pair sa sb))))
      ((fstp a) (let ((s (smt-sort-of a))) (and (sort-pair? s) (cadr s))))
      ((sndp a) (let ((s (smt-sort-of a))) (and (sort-pair? s) (caddr s))))
      ((nill s) (list 'list s))
      ((consl h t)
       (let ((sh (smt-sort-of h)) (st (smt-sort-of t)))
         (and sh (sort-list? st) (smt-sort=? sh (cadr st)) (list 'list sh))))
      ((headl s a)
       (let ((sa (smt-sort-of a)))
         (and (sort-list? sa) (smt-sort=? s (cadr sa)) s)))
      ((taill a) (let ((sa (smt-sort-of a))) (and (sort-list? sa) sa)))
      ((nulll a) (let ((sa (smt-sort-of a))) (and (sort-list? sa) 'bool)))
      (else #f)))

  (define (smt-well-sorted-bool? e) (eq? (smt-sort-of e) 'bool))

  ;;; ======================================================================
  ;;; Serialization to SMT-LIB.  Mirrors `toSMTLIB`.
  ;;; ======================================================================
  (define (sort-name s)
    (cond
     ((eq? s 'int) "Int") ((eq? s 'bool) "Bool")
     ((eq? s 'data) "Data") ((eq? s 'bytes) "String")
     ((sort-list? s) (string-append "(Lst " (sort-name (cadr s)) ")"))
     ((sort-pair? s) (string-append "(Pair " (sort-name (cadr s)) " " (sort-name (caddr s)) ")"))
     (else "?")))

  (define (bin-head op)
    (case op
      ((add) "+") ((sub) "-") ((mul) "*")
      ((fdiv) "pl_fdiv") ((fmod) "pl_fmod") ((tdiv) "pl_tdiv") ((tmod) "pl_tmod")
      ((le) "<=") ((lt) "<") ((eq) "=")
      ((and) "and") ((or) "or")
      (else (error 'smt "bad binop" op))))

  (define (uop-render op s)
    (case op
      ((idata) (string-append "(mkI " s ")"))
      ((bdata) (string-append "(mkB " s ")"))
      ((unidata) (string-append "(iVal " s ")"))
      ((unbdata) (string-append "(bVal " s ")"))
      ((constr-tag) (string-append "(cTag " s ")"))
      ((len-bytes) (string-append "(str.len " s ")"))
      ((isi) (string-append "((_ is mkI) " s ")"))
      ((isb) (string-append "((_ is mkB) " s ")"))
      ((isconstr) (string-append "((_ is mkConstr) " s ")"))
      ((islist) (string-append "((_ is mkDList) " s ")"))
      ((ismap) (string-append "((_ is mkMap) " s ")"))
      ((dargs) (string-append "(cArgs " s ")"))
      ((ditems) (string-append "(lItems " s ")"))
      ((dentries) (string-append "(mEntries " s ")"))
      (else (error 'smt "bad uop" op))))

  (define (smt->sexpr e)
    (match e
      ((var x _) x)
      ((lit-i n) (if (< n 0) (string-append "(- " (number->string (- n)) ")") (number->string n)))
      ((lit-b b) (if b "true" "false"))
      ((neg a) (string-append "(- " (smt->sexpr a) ")"))
      ((bnot a) (string-append "(not " (smt->sexpr a) ")"))
      ((bin op a b) (string-append "(" (bin-head op) " " (smt->sexpr a) " " (smt->sexpr b) ")"))
      ((uop op a) (uop-render op (smt->sexpr a)))
      ((ite c a b) (string-append "(ite " (smt->sexpr c) " " (smt->sexpr a) " " (smt->sexpr b) ")"))
      ((mkpair a b) (string-append "(mkPair " (smt->sexpr a) " " (smt->sexpr b) ")"))
      ((fstp a) (string-append "(pFst " (smt->sexpr a) ")"))
      ((sndp a) (string-append "(pSnd " (smt->sexpr a) ")"))
      ((nill s) (string-append "(as lnil (Lst " (sort-name s) "))"))
      ((consl h t) (string-append "(lcons " (smt->sexpr h) " " (smt->sexpr t) ")"))
      ((headl _ a) (string-append "(lhead " (smt->sexpr a) ")"))
      ((taill a) (string-append "(ltail " (smt->sexpr a) ")"))
      ((nulll a) (string-append "((_ is lnil) " (smt->sexpr a) ")"))
      (else (error 'smt "bad expr" e))))

  ;; Collect (name . sort) of free variables, de-duplicated, first-seen order.
  (define (smt-collect-vars e)
    (let ((seen '()) (acc '()))
      (let go ((e e))
        (match e
          ((var x s) (unless (member x seen) (set! seen (cons x seen)) (set! acc (cons (cons x s) acc))))
          ((lit-i _) #t) ((lit-b _) #t) ((nill _) #t)
          ((neg a) (go a)) ((bnot a) (go a)) ((uop _ a) (go a))
          ((fstp a) (go a)) ((sndp a) (go a)) ((headl _ a) (go a))
          ((taill a) (go a)) ((nulll a) (go a))
          ((bin _ a b) (go a) (go b)) ((mkpair a b) (go a) (go b)) ((consl a b) (go a) (go b))
          ((ite a b c) (go a) (go b) (go c))
          (else (error 'smt "bad expr in collect-vars" e))))
      (reverse acc)))

  ;; The fixed preamble: the four Plutus division/modulo operators (floored
  ;; fdiv/fmod for divideInteger/modInteger, truncated tdiv/tmod for
  ;; quotientInteger/remainderInteger), built from real `to_int`.  Emitted
  ;; unconditionally (z3 ignores unused definitions).
  (define smt-preamble
    (string-append
     "(define-fun pl_fdiv ((x Int) (y Int)) Int (to_int (/ (to_real x) (to_real y))))\n"
     "(define-fun pl_fmod ((x Int) (y Int)) Int (- x (* y (pl_fdiv x y))))\n"
     "(define-fun pl_tdiv ((x Int) (y Int)) Int "
     "(ite (= (>= x 0) (>= y 0)) (to_int (/ (to_real (abs x)) (to_real (abs y)))) "
     "(- (to_int (/ (to_real (abs x)) (to_real (abs y)))))))\n"
     "(define-fun pl_tmod ((x Int) (y Int)) Int (- x (* y (pl_tdiv x y))))\n"))

  ;; The Plutus `Data` type as an SMT-LIB recursive datatype (with its `Lst`
  ;; and `Pair` companions).  ByteString fields are SMT `String`s.
  (define smt-data-preamble
    (string-append
     "(declare-datatypes ((Pair 2)) ((par (A B) ((mkPair (pFst A) (pSnd B))))))\n"
     "(declare-datatypes ((Lst 1)) ((par (A) ((lnil) (lcons (lhead A) (ltail (Lst A)))))))\n"
     "(declare-datatypes ((Data 0)) (((mkConstr (cTag Int) (cArgs (Lst Data))) "
     "(mkMap (mEntries (Lst (Pair Data Data)))) (mkDList (lItems (Lst Data))) "
     "(mkI (iVal Int)) (mkB (bVal String)))))\n"))

  ;; Serialize an `smt` expression to a complete SMT-LIB script: logic, the
  ;; Data datatype + division preambles, variable declarations, the assertion,
  ;; and (check-sat).  An `unsat` verdict certifies the expression has no model.
  (define (smt->smtlib e)
    (let* ((vars (smt-collect-vars e))
           (decls (apply string-append
                         (map (lambda (p)
                                (string-append "(declare-const " (car p) " " (sort-name (cdr p)) ")\n"))
                              vars))))
      (string-append "(set-logic ALL)\n" smt-data-preamble smt-preamble decls
                     "(assert " (smt->sexpr e) ")\n" "(check-sat)\n")))

  ;;; ======================================================================
  ;;; z3 bridge (no proof weight; for actually running the solver).  Pipes the
  ;;; script to `z3 -smt2 -in` over stdin and reads stdout.
  ;;; ======================================================================
  (define z3-command (make-parameter "z3 -smt2 -in"))

  (define (run-z3 script)
    (let-values (((stdin stdout stderr pid)
                  (open-process-ports (z3-command) 'block (native-transcoder))))
      (put-string stdin script)
      (close-port stdin)
      (let ((out (let loop ((acc '()))
                   (let ((l (get-line stdout)))
                     (if (eof-object? l)
                         (apply string-append (reverse acc))
                         (loop (cons (string-append l "\n") acc))))))
            (err (let loop ((acc '()))
                   (let ((l (get-line stderr)))
                     (if (eof-object? l)
                         (apply string-append (reverse acc))
                         (loop (cons (string-append l "\n") acc)))))))
        (close-port stdout)
        (close-port stderr)
        (when (and (= (string-length out) 0) (> (string-length err) 0))
          (eval-failure (string-append "z3 error: " err)))
        out)))

  (define (first-token s)
    (let ((n (string-length s)))
      (let skip ((i 0))
        (cond ((fx>=? i n) "")
              ((char-whitespace? (string-ref s i)) (skip (fx+ i 1)))
              (else (let loop ((j i))
                      (if (or (fx>=? j n) (char-whitespace? (string-ref s j)))
                          (substring s i j)
                          (loop (fx+ j 1)))))))))

  ;; Run z3 on the raw text of `(smt->smtlib e)` (optionally with extra
  ;; trailing commands), returning z3's full stdout.
  (define (z3-raw e . extra)
    (run-z3 (apply string-append (smt->smtlib e) extra)))

  ;; Check `e` for satisfiability: 'unsat | 'sat | 'unknown.
  ;; 'unsat means `e` has no model (the property/negation is valid).
  (define (z3-check e)
    (let ((tok (first-token (run-z3 (smt->smtlib e)))))
      (cond ((string=? tok "unsat") 'unsat)
            ((string=? tok "sat") 'sat)
            (else 'unknown))))

  ;; Ask z3 for a satisfying model of `e` (the counterexample direction).
  ;; Returns the model text on `sat`, else #f.
  (define (z3-model e)
    (let ((raw (run-z3 (string-append (smt->smtlib e) "(get-model)\n"))))
      (if (string=? (first-token raw) "sat") raw #f))))
