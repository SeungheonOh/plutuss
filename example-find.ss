;;; example-find.ss — a more involved UPLC->SMT proof: a higher-order, recursive
;;; list function with a Maybe result, proved for ALL inputs by z3.
;;;
;;;   find :: (a -> Bool) -> [a] -> Maybe a       -- first element satisfying p,
;;;   find p []        = Nothing                  --   or Nothing
;;;   find p (x:xs)    = if p x then Just x else find p xs
;;;
;;; (This is the function whose signature is `(a -> Bool) -> [a] -> Maybe a`;
;;;  in Haskell that is `Data.List.find`.)  We prove, among others, the headline
;;;  property the request asks for:
;;;
;;;       forall x.  find (== x) []  ==  Nothing
;;;
;;; `List` and `Maybe` are declared with `define-plutus-type-SOP` from
;;; (plutuss dsl datatype): it generates the `mkNil`/`mkCons`/`mkNothing`/`mkJust`
;;; constructors and the `matchList`/`matchMaybe` matchers used below.  We use the
;;; SOP encoding (UPLC `constr`/`case`), NOT the `Data` encoding, because the
;;; symbolic compiler takes a `case` whose scrutinee is a concrete constructor
;;; directly, and pushes a `case` whose scrutinee is a *deferred* symbolic choice
;;; (an `ifThenElse` over a symbolic boolean — e.g. the predicate `(== x)` applied
;;; to a symbolic element) through that choice, compiling a symbolic predicate
;;; over a concrete list spine to nested SMT `ite`s that z3 then discharges.  The
;;; `Data` matcher would instead `case` on a symbolic integer tag (recovered by
;;; `unConstrData`), which the compiler soundly refuses.
;;;
;;; The symbolic inputs are declared up front with `(mkEnv ("x" int) ...)` and
;;; then used as *free variables* in the term — no leading lambdas to wrap and
;;; strip.  `prove` binds them (see `compile-open`).
;;;
;;; Run:  chez --script example-find.ss

(import (chezscheme))
(library-directories (list "src"))
(import (plutuss smt) (plutuss compile)
        (plutuss dsl) (plutuss dsl datatype) (plutuss frontend))

;;; ---- datatypes (via (plutuss dsl datatype)) -------------------------------

(define-plutus-type-SOP List  (Nil) (Cons head tail))
(define-plutus-type-SOP Maybe (Nothing) (Just value))

;; The mk-constructors take their fields as UPLC syntax, so a precomputed
;; sub-term is passed by splicing it: (mkCons a ,(mkNil)) builds [a], etc.

;;; ---- declaring symbolic inputs as free variables --------------------------

;; sort keyword -> SMT sort
(define (sort-of kw)
  (case kw
    ((int) smt-sort-int) ((bool) smt-sort-bool)
    ((data) smt-sort-data) ((bytes) smt-sort-bytes)
    (else (error 'mkEnv "unknown sort (want int|bool|data|bytes)" kw))))

;; (mkEnv ("x" int) ("y" bool) ...) declares the symbolic inputs by NAME and
;; sort; each name may then appear as a free variable in the term given to
;; `prove`/`compile-open`.  Yields an alist ((name . sort-keyword) ...).
(define-syntax mkEnv
  (syntax-rules ()
    ((_ (name sort) ...) (list (cons name 'sort) ...))))

;; Compile a term whose free variables are exactly the names declared in `decls`
;; down to its success formula.  A UPLC variable is bound either by a lambda
;; INSIDE the term or by a declared input; there is no third case, so we simply
;; wrap the term in one lambda per declared name and run the ordinary
;; name->debruijn — a free occurrence of a declared name resolves to its wrapper,
;; an undeclared one is rejected (typo protection).  The wrappers are then
;; stripped, and the symbolic environment lists the same inputs in the same order
;; (first declared = Var 1 = head), so the two stay in lockstep.
(define (compile-open decls term . opt)
  (let* ((fuel    (if (null? opt) 1000 (car opt)))
         (names   (map car decls))
         (senv    (apply make-sym-env
                         (map (lambda (d) (symbolic-input (car d) (sort-of (cdr d)))) decls)))
         (wrapped (fold-left (lambda (acc nm) (vector 'lam nm acc)) term names))
         (body    (let strip ((u (name->debruijn wrapped)) (k (length names)))
                    (if (fx=? k 0) u (strip (vector-ref u 2) (fx- k 1))))))
    (compile-success body senv fuel)))

;;; ---- building blocks ------------------------------------------------------

;; call-by-value one-arg Z combinator (the same fixpoint used by prove-sum.ss).
(define zfix
  (uplc (lam f ((lam h (f (lam a (h h a)))) (lam h (f (lam a (h h a))))))))

;; lazy if: delayed branches, so a symbolic guard defers the choice the compiler
;; then pushes `case` through (and so the unused branch is never evaluated).
;; (define (lite c t e)
;;   (uplc (force ((force (builtin ifThenElse)) ,c (delay ,t) (delay ,e)))))

(define (lite c e t)
  (uplc (case ,c ,t ,e)))
  ;; (uplc (force ((force (builtin ifThenElse)) ,c (delay ,t) (delay ,e)))))

;; find p  =  Z (lam self. lam xs.
;;              matchList xs of  Nil      -> Nothing
;;                               Cons h t -> if p h then Just h else find p t)
;; p is spliced in, so its free variables (e.g. x) bind in the enclosing scope;
;; `self` is the Z-combinator recursive reference (a UPLC var); `h`/`t` are the
;; matchList field binders.
(define (find-of p)
  (uplc (,zfix
         (lam self
              (lam xs
		   ,(matchList xs
			       (Nil  ()				     ; []    ->
				     ,(mkNothing))		     ;   Nothing
			       (Cons ([h head] [t tail])	     ; (h:t) ->
				     ,(lite (uplc (,p ,h))	     ;   if p h
					    (mkJust ,h)		     ;     then Just h
					    (uplc (self ,t))))))))))     ;     else find p t

;; the predicate (== x):  lam y. y == x   (x is free here; bound by the outer
;; validator lambda and supplied as a symbolic input).
(define predEqX (uplc (lam y ((builtin equalsInteger) y x))))

;;; ---- the prover harness ---------------------------------------------------

(define (rule) (display (make-string 72 #\-)) (newline))

;; Prove `term` — whose free variables are the inputs declared by `decls`
;; (an `(mkEnv ...)`) — under precondition `pre`; print the success formula and
;; z3's verdict.  `expect` is the verdict we claim ('unsat = holds for all inputs;
;; 'sat = a counterexample exists).  On a 'sat we print z3's model.
(define (prove title decls term expect . opt)
  (let ((pre (if (null? opt) smt-true (car opt))))
    (printf "~a\n" title)
    (let ((s (compile-open decls term)))
      (cond
       ((not s) (printf "  COMPILE REFUSED (outside the first-order fragment)\n\n"))
       (else
        (let* ((prop (encode-property pre s))
               (got (z3-check prop)))
          (printf "  success formula: ~a\n" (smt->sexpr s))
          (printf "  z3: ~a  (expected ~a)  ~a\n" got expect
                  (if (eq? got expect) "OK" "*** MISMATCH ***"))
          (when (and (eq? got 'sat) (eq? expect 'sat))
            (let ((m (z3-model prop)))
              (when m (display "  counterexample:\n")
                    (for-each (lambda (l) (printf "    ~a\n" l))
                              (cdr (remp (lambda (s) (string=? s ""))
                                         (split-lines m)))))))
          (newline)))))))

(define (split-lines s)
  (let loop ((i 0) (start 0) (acc '()))
    (cond ((fx=? i (string-length s)) (reverse (cons (substring s start i) acc)))
          ((char=? (string-ref s i) #\newline)
           (loop (fx+ i 1) (fx+ i 1) (cons (substring s start i) acc)))
          (else (loop (fx+ i 1) start acc)))))

;;; ---- the proofs -----------------------------------------------------------

(rule)
(display "find :: (a -> Bool) -> [a] -> Maybe a   proved over ALL inputs by z3\n")
(rule)
(newline)

;; HEADLINE (the requested property):  forall x. find (== x) [] == Nothing.
;; The list is empty, so the predicate is never called; find hits the Nil branch
;; and returns Nothing, which we confirm by matching: Nothing -> True else False.
;; `x` is a free variable, declared as a symbolic int by (mkEnv ("x" int)).
(define v-empty
  (matchMaybe (,(find-of predEqX) ,(mkNil))
    (Nothing ()       (con bool #t))      ; Nothing -> True
    (Just ([v value]) (con bool #f))))    ; Just _  -> False

(uplc-pretty v-empty)
(name->debruijn (uplc (lam x x)))
(uplc-pretty (name->debruijn (uplc (lam x ,(matchMaybe
					    ,mkNil
					    (Nothing () (con bool #t))
					    (Just () x))))))

(prove "(1)  forall x.  find (== x) [] == Nothing"
       (mkEnv ("x" int)) v-empty 'unsat)

;; The full SMT-LIB script the compiler emits for property (1) — the exact text
;; piped to z3 (logic, the Data/Lst/Pair datatypes, the division preamble,
;; const declarations, the negated-property assertion, check-sat).
(rule)
(display "SMT-LIB script emitted for property (1):\n")
(rule)
(let ((s (compile-open (mkEnv ("x" int)) v-empty)))
  (display (smt->smtlib (encode-property smt-true s))))
(newline)

(prove "(2)  forall x.  find (== x) [x] == Just x"
       (mkEnv ("x" int))
       (matchMaybe (,(find-of predEqX) ,(mkCons x ,(mkNil)))
         (Nothing ()       (con bool #f))
         (Just ([v value]) ((builtin equalsInteger) ,v x)))
       'unsat)
;;  z3: unsat  (expected unsat)  OK

(prove "(3)  forall a b x.  find (== x) [a,b] is Just h  =>  h == x"
       (mkEnv ("a" int) ("b" int) ("x" int))
       (matchMaybe (,(find-of predEqX) ,(mkCons a ,(mkCons b ,(mkNil))))
		   (Nothing ()       (con bool #t))
		   (Just ([v value]) ((builtin equalsInteger) ,v x)))
       'unsat)
;;  z3: unsat  (expected unsat)  OK

(prove "(4)  forall a x.  find (== x) [a] is always Just     (FALSE)"
       (mkEnv ("a" int) ("x" int))
       (matchMaybe (,(find-of predEqX) ,(mkCons a ,(mkNil)))
		   (Nothing ()       (con bool #f)) ; Nothing -> False (claim: impossible)
		   (Just ([v value]) (con bool #t))) ; Just _  -> True
       'sat)

(prove "(4)  forall a x.  find (== x) [a] is always Just     (FALSE)"
       (mkEnv)
       (uplc (case (con bool #t) (con bool #f) (con bool #t)))
       'unsat)

(define-syntax pand
  (syntax-rules ()
    [(_ x y) (uplc (case x (con bool #f) y))]))

(uplc-pretty (uplc ,(pand (con bool #f) (con bool #f))))
(pand (con bool #f) (con bool #f))

(define-plutus-type-Data Optional (None) (Some value))

(define genMaybe
  (lambda ()
    (let ([i (symbol->string (gensym))]
	  [j (symbol->string (gensym))])
      (values
       (uplc
	(case ,(vector 'var i)
	  ,mkNone
	  ,(mkSome [(builtin iData),(vector 'var j)])
	  ))
       (mkEnv (i int) (j int))
       (lambda (t)
	 (uplc
	  (case ,(pand
		  [(builtin lessThanInteger) ,(vector 'var i) (con integer 2)]
		  [(builtin lessThanEqualsInteger) (con integer 0) ,(vector 'var i)])
	    (con bool #t)
	    ,t
	    )))
       )
      )))

(let-values ([(t env p) (genMaybe)])
  (uplc-pretty t)
  (display env)
  (printf "~%")
  (uplc-pretty (p (uplc (con bool #t))))
  (uplc-pretty (p (matchOptional
	      ,t
	      (None () (con bool #t))
	      (Some () (con bool #t))
	      )))
  (prove "(genMaybe) guard restricts the partial int-tag Maybe to {0,1} => total => provable"
	 (append env (mkEnv ("x" int)))
	 (p (matchOptional
	     ,t
	     (None () (con bool #t))
	     (Some () (con bool #t))
	     ))
	 'sat)
  )


(uplc-pretty
 (matchOptional
  ,mkNone
  (None () (con bool #t))
  (Some () (con bool #t))
  ))

(uplc-pretty mkNone)

(call-with-values genMaybe (lambda (t env p) (uplc-pretty t)))

(uplc-pretty (mkNothing)
	     )

(genMaybe)

;;  z3: sat  (expected sat)  OK
;; counterexample:
;;   (
;;     (define-fun a () Int
;;       1)
;;     (define-fun x () Int
;;       0))

(prove "(3)  forall a b.  "
       (mkEnv ("a" bytes) ("b" bytes))
       (uplc (case [(builtin equalsByteString) a b]
	       (con bool #t)
	       [(builtin equalsByteString) [(builtin sha2_256) a] [(builtin sha2_256) b]]
	       ))
       'unsat)


(rule)
(display "(1)(2)(3) unsat => proved for ALL inputs;  (4) sat => counterexample found\n")
(rule)
