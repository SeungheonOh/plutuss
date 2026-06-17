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
          lam con builtin constr I B List Map Constr
          integer bytestring bool unit data pair
          ;; budget + errors + misc
          get-cpu-spent get-mem-spent get-mach-logs i64-max i64-min
          parse-err? eval-fail? parse-err-msg eval-fail-msg
          parse-error eval-failure builtin-lookup hex->bytevector
          ;; SMT layer (deep-embedded SMT-LIB + z3 bridge)
          smt-sort-int smt-sort-bool smt-sort-data smt-sort-bytes
          smt-sort-list smt-sort-pair
          smt-var smt-int smt-bool smt-neg smt-not smt-bin smt-uop smt-ite
          smt-mkpair smt-fst smt-snd smt-nil smt-cons smt-head smt-tail smt-null
          smt-true smt-false smt-and smt-or smt-eq smt-imp smt-ne-zero smt-conj
          smt-sort-of smt->smtlib run-z3 z3-check z3-model z3-raw
          ;; UPLC -> SMT denotational compiler
          symbolic-input make-sym-env sym-env-extend empty-sym-env
          sym-eval extract encode-property default-fuel
          compile-term compile-success compile-property current-concrete-builtin
          t-var t-con t-builtin t-lam t-delay t-force t-app t-app* t-constr t-case t-error
          c-integer c-bool c-bytestring c-unit c-data
          builtin-name builtin-arity builtin-forces)
  (import (plutuss base) (plutuss value) (plutuss cbor) (plutuss cost)
          (plutuss state) (plutuss builtins) (plutuss machine)
          (plutuss frontend) (plutuss output) (plutuss flat) (plutuss dsl)
          (plutuss smt) (plutuss compile)))
