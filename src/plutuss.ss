;;; (plutuss) — convenience aggregate: re-exports the public API so callers can
;;; just (import (plutuss)) instead of importing each sub-library.
(library (plutuss)
  (export ;; front-end / machine
          parse-program name->debruijn machine-run
          ;; output
          pretty-program pretty-term term-alpha-eq? const-eq? bytevector->hex
          ;; flat / cbor codecs
          flat-encode-program flat-decode-program cbor-encode cbor-decode
          ;; syntax DSL (+ auxiliary keywords)
          uplc uplc-program uplc-eval uplc-run hex ->bytes
          define-uplc-syntax
          lam con builtin constr I B List Map Constr
          integer bytestring bool unit data pair
          ;; budget + errors + misc
          get-cpu-spent get-mem-spent get-mach-logs i64-max i64-min
          parse-err? eval-fail? parse-err-msg eval-fail-msg
          parse-error eval-failure builtin-lookup hex->bytevector
          ;; SMT-LIB v2 target (universal value sort V + z3 bridge)
          s-int s-bool s-str s-atom s-app s-tag
          sNot sAnd sOr sImplies sIte sEq sNe sAll sAny sOrs s-beq s-render
          ssort-render sanitize
          v-int v-as-int v-bool v-as-bool v-bs v-as-bs v-str v-as-str v-unit
          v-data v-as-data v-list v-as-list v-dlist v-as-dl v-pdlist v-as-dm
          v-arr v-as-arr v-pair v-fst v-snd v-paird v-fst-d v-snd-d
          v-constr v-ctag v-cargs v-g1 v-as-g1 v-g2 v-as-g2 v-ml v-as-ml
          v-is-con v-con-name v-sis-con
          d-constr d-map d-list d-i d-b d-tag d-args d-entries d-elems d-ival d-bval
          vl-nil vl-cons vl-hd vl-tl vl-is-nil vl-of-list vl-sis-nil vl-shd vl-stl
          dl-nil dl-cons dl-hd dl-tl dl-is-nil dl-of-list dl-sis-nil dl-shd dl-stl
          dm-nil dm-cons dm-key dm-val dm-tl dm-is-nil dm-of-list
          seq-empty seq-empty-sort seq-unit seq-len seq-nth seq-append seq-extract seq-of-bytes
          str-append op-add op-sub op-mul op-div op-mod op-lt op-le op-gt op-ge op-neg
          prelude datatype-preamble opaque-ufs ufdecl-render
          make-smt-script smt-script-consts smt-script-side smt-script-asserts
          smt-script->smtlib z3-command run-z3 z3-check z3-model
          ;; UPLC -> SMT denotational symbolic compiler
          sv-const sv-dyn sv-fo sv-pair sv-lam sv-delay sv-constr sv-builtin sv-choice symv-tag
          sc-integer sc-bytes sc-string sc-bool sc-unit sc-data sc-const-list
          sc-data-list sc-pair-data-list sc-pair-data sc-array sc-g1 sc-g2 sc-ml
          outcome-tag outcome-pc outcome-val ok err timeout bind-out map-pc
          encode-val? as-int as-bytes as-string as-bool as-data as-const-list
          symr symr-inc symr-err symr-val junk
          merge-val sym-merge reify-fo reify-v reify-err
          const->sexpr data->sexpr const-literal sym-lookup
          builtin-name builtin-spec expected-args
          sym-eval eval-sym sym-apply apply-sym sym-force force-sym sym-case case-sym
          eval-builtin-sym
          mk-input uplc-symbolic-compile default-fuel
          compiled-result compiled-consts compiled-sides
          okBoolTrueCond okBoolCond okIntEqCond okValEqCond errorCond timeoutCond
          goal-equals-v goal-returns-bool goal-returns-int
          goal-errors goal-succeeds goal-indeterminate
          compiled->script compiled->smtlib
          ;; UPLC-predicate refinement checker
          current-refinement-fuel clear-refinements!
          define-upred define/refined define-refined verify/refine
          register-upred! lookup-upred upred?
          register-refined! lookup-refined refined-function?
          refined-function-term refined-function-body
          eval-predicate eval-predicate-call
          predicate-true-cond predicate-false-cond predicate-error-cond
          predicate-timeout-cond predicate-non-bool-cond predicate-violation-cond
          check-refinement verify-refined-function
          refinement-verification? refinement-verification-name refinement-verification-ok?
          refinement-verification-obligations refinement-verification-compiled
          refinement-obligation? refinement-obligation-name refinement-obligation-kind
          refinement-obligation-expected refinement-obligation-actual
          refinement-obligation-ok? refinement-obligation-smtlib
          refinement-report display-refinement-report
          term->debruijn/free normalize-refinement-spec normalize-return-spec)
  (import (plutuss base) (plutuss value) (plutuss cbor) (plutuss cost)
          (plutuss state) (plutuss builtins) (plutuss machine)
          (plutuss frontend) (plutuss output) (plutuss flat) (plutuss dsl)
          (plutuss smt) (plutuss compile) (plutuss refine)))
