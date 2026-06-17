;;; (plutuss compile) — a denotational UPLC -> SMT compiler.
;;;
;;; This is a symbolic CEK evaluator: it runs the very same machine as
;;; (plutuss machine), but over a *symbolic* value domain in which a constant is
;;; an `smt` expression (from (plutuss smt)) rather than a concrete datum.  A
;;; symbolic integer/boolean input is a free SMT variable, so evaluating a term
;;; with symbolic inputs yields an `smt` expression denoting the term's result
;;; as a function of those inputs — together with a *definedness* guard that is
;;; true exactly at inputs for which the concrete CEK evaluation would not error.
;;;
;;; It is a faithful Scheme port of the verified Lean development
;;; `Moist/Compile/{SymValue,Builtins,Compile}.lean` (utxo-company/moist).  The
;;; five mutually-recursive functions (sym-eval/sym-apply/sym-force/
;;; sym-eval-list/sym-apply-list, plus sym-case) mirror the machine's
;;; compute/return/force/apply transitions one-for-one, defunctionalized exactly
;;; as the CEK does (closures are applied by the evaluator, never reified into
;;; SMT).  Bounded recursion is handled by `fuel`: when fuel runs out the result
;;; is a sound *refusal* (#f) or, on a symbolic branch, a `defined = false` leaf
;;; — never a silent under-approximation.
;;;
;;; Soundness posture (R1): every construct the symbolic domain cannot represent
;;; first-order — a genuinely symbolic non-arithmetic builtin, a symbolic-constant
;;; case scrutinee, an unsupported builtin — returns #f (refuse), never a wrong
;;; answer.  The supported first-order fragment is: integer arithmetic/comparison,
;;; ifThenElse (concrete or symbolic-boolean control flow), trace/chooseUnit
;;; (pass-through), the Data injections/projections (iData/bData/unIData/unBData/
;;; unConstrData/unListData), fstPair/sndPair, headList/tailList/nullList,
;;; lengthOfByteString, and equalsData/equalsByteString.  constr/case and
;;; lambda/delay/force/apply are fully supported (defunctionalized).
;;;
;;; Builtins are identified by their UPLC name.  A `#(builtin desc)` node may
;;; carry either a real (plutuss builtins) descriptor record (from the parser or
;;; the `uplc` DSL) or, for FFI-free programmatic use, a plain string/symbol;
;;; both are accepted.  Reading a descriptor's name/arity/forces uses Chez's
;;; record reflection, so this library does NOT import (plutuss builtins) and
;;; never triggers its native-crypto FFI — the first-order fragment it targets
;;; needs none of those builtins.
(library (plutuss compile)
  (export
   ;; symbolic value constructors / introspection
   sym-vtag sval-con sval-const sval-lam sval-delay sval-constr sval-builtin sval-ite
   sout sout-value sout-defined
   ;; environment / inputs
   empty-sym-env sym-env-extend sym-env-lookup make-sym-env
   symbolic-input fresh-input
   ;; the evaluator
   sym-eval sym-apply sym-force extract encode-property
   default-fuel
   ;; high-level interface
   compile-term compile-success compile-property
   ;; concrete-fold hook (off by default; see notes)
   current-concrete-builtin
   ;; FFI-free term constructors (for building ASTs without the parser/DSL)
   t-var t-con t-builtin t-lam t-delay t-force t-app t-app* t-constr t-case t-error
   ;; constant helpers
   c-integer c-bool c-bytestring c-unit c-data const->sym
   ;; builtin metadata
   builtin-name builtin-arity builtin-forces builtin-spec)
  (import (chezscheme) (plutuss base) (plutuss smt))

  ;;; ======================================================================
  ;;; Symbolic values.  One-for-one with (plutuss machine)'s runtime values,
  ;;; except a concrete constant `#(vcon c)` becomes either `#(scon e)` (an
  ;;; arithmetic-capable `smt` expression) or `#(sconst c)` (any other constant,
  ;;; carried concretely).  `#(site c a b)` is the deferred symbolic choice
  ;;; produced by a symbolic-boolean ifThenElse (mirrors moist's `sIte`).
  ;;; ======================================================================
  (define (sval-con e)              (vector 'scon e))
  (define (sval-const c)            (vector 'sconst c))
  (define (sval-lam nm body env)    (vector 'slam nm body env))
  (define (sval-delay body env)     (vector 'sdelay body env))
  (define (sval-constr tag fields)  (vector 'sconstr tag fields))
  (define (sval-builtin b f a n)    (vector 'sbuiltin b f a n))
  (define (sval-ite cnd a b)        (vector 'site cnd a b))

  (define (sym-vtag v) (vector-ref v 0))
  (define (scon-e v)   (vector-ref v 1))
  (define (sconst-c v) (vector-ref v 1))
  (define (slam-body v) (vector-ref v 2))   (define (slam-env v) (vector-ref v 3))
  (define (sdelay-body v) (vector-ref v 1)) (define (sdelay-env v) (vector-ref v 2))
  (define (sconstr-tag v) (vector-ref v 1)) (define (sconstr-fields v) (vector-ref v 2))
  (define (sbuiltin-fn v) (vector-ref v 1)) (define (sbuiltin-forces v) (vector-ref v 2))
  (define (sbuiltin-args v) (vector-ref v 3)) (define (sbuiltin-nargs v) (vector-ref v 4))
  (define (site-cond v) (vector-ref v 1)) (define (site-a v) (vector-ref v 2)) (define (site-b v) (vector-ref v 3))

  ;; A symbolic output: the value together with its definedness `smt` formula.
  ;; `#f` is the `none`/refusal result; a valid output is `(cons value defined)`.
  (define (sout value defined) (cons value defined))
  (define (sout-value o) (car o))
  (define (sout-defined o) (cdr o))

  ;;; ======================================================================
  ;;; Symbolic environment: a list with the same 1-based de-Bruijn convention
  ;;; as (plutuss machine) (Var 1 = head).
  ;;; ======================================================================
  (define empty-sym-env '())
  (define (sym-env-extend env v) (cons v env))
  (define (sym-env-lookup env k)
    (cond ((null? env) #f)
          ((fx=? k 0) #f)
          ((fx=? k 1) (car env))
          (else (sym-env-lookup (cdr env) (fx- k 1)))))
  ;; Build an env from inputs given innermost-first (so the first listed is Var 1).
  (define (make-sym-env . inputs) inputs)

  ;; A symbolic input of the given sort, bound to a fresh SMT variable `name`.
  (define (symbolic-input name sort)
    (sval-con (smt-var (if (symbol? name) (symbol->string name) name) sort)))
  ;; Counter-free fresh inputs: caller supplies distinct names.
  (define (fresh-input name sort) (symbolic-input name sort))

  (define (nth? lst n)
    (cond ((null? lst) #f)
          ((fx=? n 0) (car lst))
          (else (nth? (cdr lst) (fx- n 1)))))

  (define (sort-pair? s) (and (pair? s) (eq? (car s) 'pair)))

  ;;; ======================================================================
  ;;; Constants.  A UPLC constant is (type . value).  Integer/Bool become an
  ;;; arithmetic-capable `scon`; everything else is carried concretely as
  ;;; `sconst`.  Mirrors `constToSym`.
  ;;; ======================================================================
  (define (const->smt c)
    (case (car c)
      ((integer) (smt-int (cdr c)))
      ((bool) (smt-bool (cdr c)))
      (else #f)))
  (define (const->sym c)
    (let ((e (const->smt c))) (if e (sval-con e) (sval-const c))))

  ;; constant builders (type . value), matching the (plutuss) constant rep.
  (define (c-integer n) (cons 'integer n))
  (define (c-bool b) (cons 'bool b))
  (define (c-bytestring bv) (cons 'bytestring bv))
  (define (c-unit) (cons 'unit '()))
  (define (c-data d) (cons 'data d))

  ;;; ======================================================================
  ;;; Builtin metadata.  Identified by UPLC name; arity/forces from a real
  ;;; descriptor record (via reflection) or from the static spec table.
  ;;; ======================================================================
  ;; (name forces arity) for every Plutus builtin (DefaultFunction order).
  (define builtin-specs
    '(("addInteger" 0 2) ("subtractInteger" 0 2) ("multiplyInteger" 0 2)
      ("divideInteger" 0 2) ("quotientInteger" 0 2) ("remainderInteger" 0 2)
      ("modInteger" 0 2) ("equalsInteger" 0 2) ("lessThanInteger" 0 2)
      ("lessThanEqualsInteger" 0 2)
      ("appendByteString" 0 2) ("consByteString" 0 2) ("sliceByteString" 0 3)
      ("lengthOfByteString" 0 1) ("indexByteString" 0 2) ("equalsByteString" 0 2)
      ("lessThanByteString" 0 2) ("lessThanEqualsByteString" 0 2)
      ("sha2_256" 0 1) ("sha3_256" 0 1) ("blake2b_256" 0 1)
      ("verifyEd25519Signature" 0 3)
      ("appendString" 0 2) ("equalsString" 0 2) ("encodeUtf8" 0 1) ("decodeUtf8" 0 1)
      ("ifThenElse" 1 3) ("chooseUnit" 1 2) ("trace" 1 2)
      ("fstPair" 2 1) ("sndPair" 2 1) ("chooseList" 2 3) ("mkCons" 1 2)
      ("headList" 1 1) ("tailList" 1 1) ("nullList" 1 1)
      ("chooseData" 1 6) ("constrData" 0 2) ("mapData" 0 1) ("listData" 0 1)
      ("iData" 0 1) ("bData" 0 1)
      ("unConstrData" 0 1) ("unMapData" 0 1) ("unListData" 0 1)
      ("unIData" 0 1) ("unBData" 0 1)
      ("equalsData" 0 2) ("mkPairData" 0 2) ("mkNilData" 0 1) ("mkNilPairData" 0 1)
      ("serialiseData" 0 1)
      ("verifyEcdsaSecp256k1Signature" 0 3) ("verifySchnorrSecp256k1Signature" 0 3)
      ("bls12_381_G1_add" 0 2) ("bls12_381_G1_neg" 0 1) ("bls12_381_G1_scalarMul" 0 2)
      ("bls12_381_G1_equal" 0 2) ("bls12_381_G1_compress" 0 1) ("bls12_381_G1_uncompress" 0 1)
      ("bls12_381_G1_hashToGroup" 0 2)
      ("bls12_381_G2_add" 0 2) ("bls12_381_G2_neg" 0 1) ("bls12_381_G2_scalarMul" 0 2)
      ("bls12_381_G2_equal" 0 2) ("bls12_381_G2_compress" 0 1) ("bls12_381_G2_uncompress" 0 1)
      ("bls12_381_G2_hashToGroup" 0 2)
      ("bls12_381_millerLoop" 0 2) ("bls12_381_mulMlResult" 0 2) ("bls12_381_finalVerify" 0 2)
      ("keccak_256" 0 1) ("blake2b_224" 0 1)
      ("integerToByteString" 0 3) ("byteStringToInteger" 0 2)
      ("andByteString" 0 3) ("orByteString" 0 3) ("xorByteString" 0 3)
      ("complementByteString" 0 1) ("readBit" 0 2) ("writeBits" 0 3) ("replicateByte" 0 2)
      ("shiftByteString" 0 2) ("rotateByteString" 0 2) ("countSetBits" 0 1) ("findFirstSetBit" 0 1)
      ("ripemd_160" 0 1) ("expModInteger" 0 3)
      ("dropList" 1 2) ("lengthOfArray" 1 1) ("listToArray" 1 1) ("indexArray" 1 2)
      ("insertCoin" 0 4) ("lookupCoin" 0 3) ("unionValue" 0 2) ("valueContains" 0 2)
      ("valueData" 0 1) ("unValueData" 0 1) ("scaleValue" 0 2)
      ("bls12_381_G1_multiScalarMul" 0 2) ("bls12_381_G2_multiScalarMul" 0 2)))

  (define (builtin-spec name) (assoc name builtin-specs))

  ;; Read a named field of a record without importing the defining library.
  (define (record-field r fname)
    (let* ((rtd (record-rtd r)) (names (record-type-field-names rtd)))
      (let loop ((i 0))
        (cond ((fx>=? i (vector-length names)) (error 'compile "record has no field" fname))
              ((eq? (vector-ref names i) fname) ((record-accessor rtd i) r))
              (else (loop (fx+ i 1)))))))

  (define (builtin-name b)
    (cond ((string? b) b)
          ((symbol? b) (symbol->string b))
          ((record? b) (record-field b 'name))
          (else (error 'compile "bad builtin descriptor" b))))
  (define (builtin-arity b)
    (cond ((record? b) (record-field b 'arity))
          (else (let ((s (builtin-spec (builtin-name b))))
                  (if s (caddr s) (error 'compile "unknown builtin (arity)" (builtin-name b)))))))
  (define (builtin-forces b)
    (cond ((record? b) (record-field b 'forces))
          (else (let ((s (builtin-spec (builtin-name b))))
                  (if s (cadr s) (error 'compile "unknown builtin (forces)" (builtin-name b)))))))

  ;;; ======================================================================
  ;;; Symbolic builtin denotations.  Mirrors smtBuiltin / symBuiltinPassThrough
  ;;; / symEvalBuiltin.  Arguments arrive newest-first (most recent first),
  ;;; matching the machine's consed-argument convention; for a 2-ary builtin
  ;;; that means (ey ex) = (second-arg first-arg).
  ;;; ======================================================================

  ;; first-order builtin: argument `smt` exprs -> (value-expr . definedness-guard) | #f
  (define (sort-bin op grd need ex ey)
    (and (smt-sort=? (smt-sort-of ex) need) (smt-sort=? (smt-sort-of ey) need)
         (cons (smt-bin op ex ey) grd)))
  (define (uop-build op grd need e)
    (and (smt-sort=? (smt-sort-of e) need) (cons (smt-uop op e) grd)))
  (define (unconstr-build e)
    (and (smt-sort=? (smt-sort-of e) 'data)
         (cons (smt-mkpair (smt-uop 'constr-tag e) (smt-uop 'dargs e)) (smt-uop 'isconstr e))))
  (define (pair-proj mk e)
    (and (sort-pair? (smt-sort-of e)) (cons (mk e) smt-true)))
  (define (list-op-ne mk e)
    (and (smt-sort=? (smt-sort-of e) (smt-sort-list 'data)) (cons (mk e) (smt-not (smt-null e)))))
  (define (list-op-t mk e)
    (and (smt-sort=? (smt-sort-of e) (smt-sort-list 'data)) (cons (mk e) smt-true)))

  (define (smt-builtin name args)
    (case (length args)
      ((1)
       (let ((e (car args)))
         (cond
          ((string=? name "iData") (uop-build 'idata smt-true 'int e))
          ((string=? name "bData") (uop-build 'bdata smt-true 'bytes e))
          ((string=? name "unIData") (uop-build 'unidata (smt-uop 'isi e) 'data e))
          ((string=? name "unBData") (uop-build 'unbdata (smt-uop 'isb e) 'data e))
          ((string=? name "unConstrData") (unconstr-build e))
          ((string=? name "unListData") (uop-build 'ditems (smt-uop 'islist e) 'data e))
          ((string=? name "fstPair") (pair-proj smt-fst e))
          ((string=? name "sndPair") (pair-proj smt-snd e))
          ((string=? name "headList") (list-op-ne (lambda (x) (smt-head 'data x)) e))
          ((string=? name "tailList") (list-op-ne smt-tail e))
          ((string=? name "nullList") (list-op-t smt-null e))
          ((string=? name "lengthOfByteString") (uop-build 'len-bytes smt-true 'bytes e))
          (else #f))))
      ((2)
       (let ((ey (car args)) (ex (cadr args)))
         (cond
          ((string=? name "addInteger")            (sort-bin 'add smt-true 'int ex ey))
          ((string=? name "subtractInteger")       (sort-bin 'sub smt-true 'int ex ey))
          ((string=? name "multiplyInteger")       (sort-bin 'mul smt-true 'int ex ey))
          ((string=? name "divideInteger")         (sort-bin 'fdiv (smt-ne-zero ey) 'int ex ey))
          ((string=? name "modInteger")            (sort-bin 'fmod (smt-ne-zero ey) 'int ex ey))
          ((string=? name "quotientInteger")       (sort-bin 'tdiv (smt-ne-zero ey) 'int ex ey))
          ((string=? name "remainderInteger")      (sort-bin 'tmod (smt-ne-zero ey) 'int ex ey))
          ((string=? name "equalsInteger")         (sort-bin 'eq smt-true 'int ex ey))
          ((string=? name "lessThanInteger")       (sort-bin 'lt smt-true 'int ex ey))
          ((string=? name "lessThanEqualsInteger") (sort-bin 'le smt-true 'int ex ey))
          ((string=? name "equalsData")            (sort-bin 'eq smt-true 'data ex ey))
          ((string=? name "equalsByteString")      (sort-bin 'eq smt-true 'bytes ex ey))
          (else #f))))
      (else #f)))

  ;; pass-through builtins whose result is one of their value arguments; they
  ;; must NOT be routed through the concrete fold.  Mirrors isPassthroughBuiltin.
  (define (passthrough-builtin? name)
    (member name '("ifThenElse" "chooseUnit" "trace" "chooseData" "chooseList" "mkCons")))

  ;; ifThenElse / trace / chooseUnit.  ifThenElse with a concrete boolean picks
  ;; the branch; with a symbolic boolean and first-order branches it becomes an
  ;; SMT `ite`, otherwise a deferred `site`.  trace s v = v ; chooseUnit u v = v.
  (define (sym-builtin-passthrough b args)
    (let ((name (builtin-name b)))
      (cond
       ((string=? name "ifThenElse")
        (and (fx=? (length args) 3)
             (let ((elseV (car args)) (thenV (cadr args)) (condV (caddr args)))
               (and (eq? (sym-vtag condV) 'scon)
                    (let ((condE (scon-e condV)))
                      (cond
                       ((eq? (smt-tag condE) 'lit-b)
                        (if (vector-ref condE 1) (sout thenV smt-true) (sout elseV smt-true)))
                       ((eq? (smt-sort-of condE) 'bool)
                        (if (and (eq? (sym-vtag thenV) 'scon) (eq? (sym-vtag elseV) 'scon))
                            (sout (sval-con (smt-ite condE (scon-e thenV) (scon-e elseV))) smt-true)
                            (sout (sval-ite condE thenV elseV) smt-true)))
                       (else #f)))))))
       ((string=? name "trace")
        (and (fx=? (length args) 2) (sout (car args) smt-true)))      ; (trace s v) -> v
       ((string=? name "chooseUnit")
        (and (fx=? (length args) 2) (sout (car args) smt-true)))      ; (chooseUnit u v) -> v
       (else #f))))

  ;; extract argument exprs from `scon`-wrapped values; #f if any is not scon.
  (define (sym-extract-cons args)
    (cond ((null? args) '())
          ((eq? (sym-vtag (car args)) 'scon)
           (let ((rest (sym-extract-cons (cdr args))))
             (and rest (cons (scon-e (car args)) rest))))
          (else #f)))

  (define (sym-builtin-symbolic b args)
    (let ((exprs (sym-extract-cons args)))
      (and exprs
           (let ((r (smt-builtin (builtin-name b) exprs)))
             (and r (sout (sval-con (car r)) (cdr r)))))))

  ;; extract fully concrete consts ((type . value)) from symbolic args, for the
  ;; optional concrete fold; #f if any argument is genuinely symbolic.
  (define (sym-concrete args)
    (cond
     ((null? args) '())
     (else
      (let ((a (car args)))
        (cond
         ((eq? (sym-vtag a) 'sconst)
          (let ((r (sym-concrete (cdr args)))) (and r (cons (sconst-c a) r))))
         ((and (eq? (sym-vtag a) 'scon) (eq? (smt-tag (scon-e a)) 'lit-i))
          (let ((r (sym-concrete (cdr args)))) (and r (cons (cons 'integer (vector-ref (scon-e a) 1)) r))))
         ((and (eq? (sym-vtag a) 'scon) (eq? (smt-tag (scon-e a)) 'lit-b))
          (let ((r (sym-concrete (cdr args)))) (and r (cons (cons 'bool (vector-ref (scon-e a) 1)) r))))
         (else #f))))))

  ;; Optional concrete-fold hook.  A procedure (name reversed-consts) -> const | #f
  ;; that evaluates a fully-concrete builtin application (consts newest-first,
  ;; matching the machine's reversed-arg convention) and returns the resulting
  ;; (type . value) constant, or #f to decline.  Default declines (sound: the
  ;; builtin is then refused).  A (plutuss machine)-backed implementation can be
  ;; installed for full concrete coverage; kept out of the core so this library
  ;; stays free of the native-crypto FFI.
  (define current-concrete-builtin
    (make-parameter (lambda (name rev-consts) #f)))

  ;; Evaluate a saturated builtin symbolically: pass-through, then the symbolic
  ;; table, then the concrete fold.  Mirrors symEvalBuiltin.
  (define (sym-eval-builtin b args)
    (or (sym-builtin-passthrough b args)
        (sym-builtin-symbolic b args)
        (and (not (passthrough-builtin? (builtin-name b)))
             (let ((consts (sym-concrete args)))
               (and consts
                    (let ((c ((current-concrete-builtin) (builtin-name b) consts)))
                      (and c (sout (sval-const c) smt-true))))))))

  ;;; ======================================================================
  ;;; combine-ite: merge the two branches of a deferred `site` after both have
  ;;; been forced/applied/cased, emitting an SMT `ite`.  A branch that failed
  ;;; (fuel/refusal) makes that path undefined.  Mirrors combineIte.
  ;;; ======================================================================
  (define (combine-ite cnd oa ob)
    (cond
     ((and oa ob)
      (let ((va (sout-value oa)) (ad (sout-defined oa))
            (vb (sout-value ob)) (bd (sout-defined ob)))
        (if (and (eq? (sym-vtag va) 'scon) (eq? (sym-vtag vb) 'scon))
            (sout (sval-con (smt-ite cnd (scon-e va) (scon-e vb))) (smt-ite cnd ad bd))
            (sout (sval-ite cnd va vb) (smt-ite cnd ad bd)))))
     (oa (sout (sout-value oa) (smt-ite cnd (sout-defined oa) smt-false)))
     (ob (sout (sout-value ob) (smt-ite cnd smt-false (sout-defined ob))))
     (else #f)))

  ;;; ======================================================================
  ;;; The symbolic evaluator.  Five mutually-recursive functions + sym-case,
  ;;; mirroring symEval/symApply/symForce/symEvalList/symApplyList/symCase.
  ;;; `fuel` bounds the recursion; 0 => refuse (#f).
  ;;; ======================================================================
  (define (sym-eval fuel env t)
    (if (fx=? fuel 0) #f
        (let ((n (fx- fuel 1)))
          (match t
            ((var k)
             (let ((v (sym-env-lookup env k))) (and v (sout v smt-true))))
            ((con c) (sout (const->sym c) smt-true))
            ((builtin b) (sout (sval-builtin b 0 '() 0) smt-true))
            ((lam nm body) (sout (sval-lam nm body env) smt-true))
            ((delay body) (sout (sval-delay body env) smt-true))
            ((app f a)
             (let ((of (sym-eval n env f)))
               (and of
                    (let ((oa (sym-eval n env a)))
                      (and oa
                           (let ((oap (sym-apply n (sout-value of) (sout-value oa))))
                             (and oap
                                  (sout (sout-value oap)
                                        (smt-and (sout-defined of)
                                                 (smt-and (sout-defined oa) (sout-defined oap)))))))))))
            ((force tt)
             (let ((ot (sym-eval n env tt)))
               (and ot
                    (let ((ofo (sym-force n (sout-value ot))))
                      (and ofo
                           (sout (sout-value ofo) (smt-and (sout-defined ot) (sout-defined ofo))))))))
            ((constr tag ms)
             (let ((r (sym-eval-list n env ms)))
               (and r (sout (sval-constr tag (car r)) (cdr r)))))
            ((case scrut alts)
             (let ((osc (sym-eval n env scrut)))
               (and osc
                    (let ((sv (sout-value osc)))
                      (cond
                       ((eq? (sym-vtag sv) 'sconstr)
                        (let ((alt (nth? alts (sconstr-tag sv))))
                          (and alt
                               (let ((oalt (sym-eval n env alt)))
                                 (and oalt
                                      (let ((oap (sym-apply-list n (sout-value oalt) (sconstr-fields sv))))
                                        (and oap
                                             (sout (sout-value oap)
                                                   (smt-and (sout-defined osc)
                                                            (smt-and (sout-defined oalt) (sout-defined oap)))))))))))
                       ((eq? (sym-vtag sv) 'site)
                        (let ((oc (sym-case n env sv alts)))
                          (and oc (sout (sout-value oc) (smt-and (sout-defined osc) (sout-defined oc))))))
                       (else #f))))))         ; symbolic-constant scrutinee => refuse (R1)
            ((uerror) #f)
            (else (error 'sym-eval "bad term" t))))))

  (define (sym-apply fuel vf va)
    (if (fx=? fuel 0) #f
        (let ((n (fx- fuel 1)))
          (case (sym-vtag vf)
            ((slam) (sym-eval n (sym-env-extend (slam-env vf) va) (slam-body vf)))
            ((sbuiltin)
             (let ((b (sbuiltin-fn vf)) (forces (sbuiltin-forces vf))
                   (args (sbuiltin-args vf)) (nargs (sbuiltin-nargs vf)))
               (if (and (fx>=? forces (builtin-forces b)) (fx<? nargs (builtin-arity b)))
                   (let ((args2 (cons va args)) (nargs2 (fx+ nargs 1)))
                     (if (fx=? nargs2 (builtin-arity b))
                         (sym-eval-builtin b args2)
                         (sout (sval-builtin b forces args2 nargs2) smt-true)))
                   #f)))
            ((site) (combine-ite (site-cond vf) (sym-apply n (site-a vf) va) (sym-apply n (site-b vf) va)))
            (else #f)))))

  (define (sym-force fuel vf)
    (if (fx=? fuel 0) #f
        (let ((n (fx- fuel 1)))
          (case (sym-vtag vf)
            ((sdelay) (sym-eval n (sdelay-env vf) (sdelay-body vf)))
            ((sbuiltin)
             (let ((b (sbuiltin-fn vf)) (forces (sbuiltin-forces vf))
                   (args (sbuiltin-args vf)) (nargs (sbuiltin-nargs vf)))
               (if (fx<? forces (builtin-forces b))
                   (let ((forces2 (fx+ forces 1)))
                     (if (and (fx=? forces2 (builtin-forces b)) (fx=? nargs (builtin-arity b)))
                         (sym-eval-builtin b args)
                         (sout (sval-builtin b forces2 args nargs) smt-true)))
                   #f)))
            ((site) (combine-ite (site-cond vf) (sym-force n (site-a vf)) (sym-force n (site-b vf))))
            (else #f)))))

  (define (sym-eval-list fuel env ts)
    (if (null? ts) (cons '() smt-true)
        (let ((o (sym-eval fuel env (car ts))))
          (and o
               (let ((r (sym-eval-list fuel env (cdr ts))))
                 (and r (cons (cons (sout-value o) (car r))
                              (smt-and (sout-defined o) (cdr r)))))))))

  (define (sym-apply-list fuel vf args)
    (if (null? args) (sout vf smt-true)
        (let ((o (sym-apply fuel vf (car args))))
          (and o
               (let ((o2 (sym-apply-list fuel (sout-value o) (cdr args))))
                 (and o2 (sout (sout-value o2) (smt-and (sout-defined o) (sout-defined o2)))))))))

  (define (sym-case fuel env sv alts)
    (if (fx=? fuel 0) #f
        (let ((n (fx- fuel 1)))
          (case (sym-vtag sv)
            ((sconstr)
             (let ((alt (nth? alts (sconstr-tag sv))))
               (and alt
                    (let ((oalt (sym-eval n env alt)))
                      (and oalt
                           (let ((oap (sym-apply-list n (sout-value oalt) (sconstr-fields sv))))
                             (and oap (sout (sout-value oap)
                                            (smt-and (sout-defined oalt) (sout-defined oap))))))))))
            ((site)
             (combine-ite (site-cond sv)
                          (sym-case fuel env (site-a sv) alts)
                          (sym-case fuel env (site-b sv) alts)))
            (else #f)))))

  ;;; ======================================================================
  ;;; Top-level interface.
  ;;; ======================================================================
  (define default-fuel (make-parameter 5000))

  ;; Compile a term in a symbolic environment; returns a SymOut or #f.
  (define (compile-term t env . opt)
    (sym-eval (if (null? opt) (default-fuel) (car opt)) env t))

  ;; The top-level success formula `defined AND value` of a validator whose
  ;; result is a first-order (boolean) `scon`; #f otherwise.  Mirrors `extract`.
  (define (extract o)
    (and o (eq? (sym-vtag (sout-value o)) 'scon)
         (smt-and (sout-defined o) (scon-e (sout-value o)))))

  (define (compile-success t env . opt)
    (let ((o (apply compile-term t env opt))) (and o (extract o))))

  ;; Negation of "precondition `pre` implies success" — assert this and an
  ;; `unsat` from z3 proves the validator is defined and returns true for all
  ;; inputs satisfying `pre`.  Mirrors `encodeProperty`.
  (define (encode-property pre success) (smt-not (smt-imp pre success)))

  ;; Compile to the z3-ready property formula, given a precondition `pre`.
  (define (compile-property t env pre . opt)
    (let ((s (apply compile-success t env opt)))
      (and s (encode-property pre s))))

  ;;; ======================================================================
  ;;; FFI-free term constructors (build de-Bruijn ASTs directly; builtins by
  ;;; name string).  Match (plutuss machine)'s term shapes exactly.
  ;;; ======================================================================
  (define (t-var k) (vector 'var k))
  (define (t-con c) (vector 'con c))
  (define (t-builtin name) (vector 'builtin name))   ; name is a string/symbol
  (define (t-lam body) (vector 'lam "_" body))        ; de-Bruijn: binder name is cosmetic
  (define (t-delay body) (vector 'delay body))
  (define (t-force body) (vector 'force body))
  (define (t-app f a) (vector 'app f a))
  (define (t-app* f . args) (fold-left (lambda (g a) (vector 'app g a)) f args))
  (define (t-constr tag fields) (vector 'constr tag fields))
  (define (t-case scrut branches) (vector 'case scrut branches))
  (define (t-error) (vector 'uerror)))
