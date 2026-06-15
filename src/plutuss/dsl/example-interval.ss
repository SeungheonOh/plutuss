;;; example-interval.ss — a port of PlutusLedgerApi.V1.Interval to the
;;; `define-plutus-type-Data` DSL.
;;;
;;; Run from the repo root:
;;;   chez --script src/plutuss/dsl/example-interval.ss
;;;
;;; This mirrors plutus/plutus-ledger-api/src/PlutusLedgerApi/V1/Interval.hs.
;;; Each Haskell datatype is reproduced with its *exact* Data constructor
;;; indices (the `makeIsDataIndexed`/`makeIsDataSchemaIndexed` splices at the
;;; bottom of that module):
;;;
;;;   data Extended a = NegInf | Finite a | PosInf      -- 0 | 1 | 2
;;;   type Closure    = Bool                            -- False=0 | True=1
;;;   data LowerBound a = LowerBound (Extended a) Closure   -- 0
;;;   data UpperBound a = UpperBound (Extended a) Closure   -- 0
;;;   data Interval  a  = Interval (LowerBound a) (UpperBound a)  -- 0
;;;
;;; and `member :: a -> Interval a -> Bool` is implemented over Integer.
;;; This is the workhorse of real validators ("is the current time inside the
;;; transaction's validity range?").

(import (chezscheme))
(library-directories (list "src"))
(import (plutuss base) (plutuss dsl) (plutuss dsl datatype))

;; ---------------------------------------------------------------------------
;; Datatypes (Data-encoded, indices match plutus-ledger-api exactly)
;; ---------------------------------------------------------------------------

(define-plutus-type-Data Extended
  (NegInf)
  (Finite val)
  (PosInf))

;; Closure = Bool, and PlutusTx encodes Bool as  False -> Constr 0 | True -> Constr 1.
(define-plutus-type-Data PBool
  (PFalse)
  (PTrue))

(define-plutus-type-Data LowerBound
  (LowerBound ext closed))

(define-plutus-type-Data UpperBound
  (UpperBound ext closed))

(define-plutus-type-Data Interval
  (Interval lo hi))

;; ---------------------------------------------------------------------------
;; Smart constructors — Scheme helpers that build UPLC `data` terms.
;;
;; Nested values are passed through the `,`-splicing helpers (`lower`/`upper`/
;; `mk-iv`), so each argument is an ordinary Scheme expression. The nullary
;; constructors (`mkPTrue`, `mkNegInf`, …) are identifier macros, so the bare
;; name works there directly — no `(mkPTrue)` call, no intermediate binding.
;; ---------------------------------------------------------------------------

(define (finite n) (mkFinite (con data (I ,n))))           ; Extended from a Scheme int

(define (lower e c) (mkLowerBound ,e ,c))
(define (upper e c) (mkUpperBound ,e ,c))
(define (mk-iv lo hi) (mkInterval ,lo ,hi))

;; lowerBound n / upperBound n         -> inclusive   [n , …
;; strictLowerBound / strictUpperBound -> exclusive   (n , …
(define (lowerBound n)       (lower (finite n) mkPTrue))
(define (strictLowerBound n) (lower (finite n) mkPFalse))
(define (upperBound n)       (upper (finite n) mkPTrue))
(define (strictUpperBound n) (upper (finite n) mkPFalse))

(define (interval a b)     (mk-iv (lowerBound a) (upperBound b)))             ; [a , b]
(define (open-interval a b)(mk-iv (strictLowerBound a) (strictUpperBound b))) ; (a , b)
(define (singleton a)      (interval a a))                                    ; [a , a]
(define (from a)           (mk-iv (lowerBound a) (upper mkPosInf mkPTrue)))   ; [a , +inf]
(define (to a)             (mk-iv (lower mkNegInf mkPTrue) (upperBound a)))   ; [-inf , a]
(define always-iv          (mk-iv (lower mkNegInf mkPTrue) (upper mkPosInf mkPTrue)))
(define never-iv           (mk-iv (lower mkPosInf mkPTrue) (upper mkNegInf mkPTrue)))

;; ---------------------------------------------------------------------------
;; member :: Integer -> Interval Integer -> Bool
;;
;;   member x i  =  (x is above i's lower bound)  &&  (x is below i's upper bound)
;;
;; matching the meaning of `i `contains` singleton x` for an Enum (Integer).
;; ---------------------------------------------------------------------------

;; logical AND of two UPLC bool terms (both pure, so eager ifThenElse is fine)
(define (uand a b)
  (uplc [[[ (force (builtin ifThenElse)) ,a ] ,b ] (con bool #f)]))

;; is the integer term `xt` at/above the lower bound term `lb`?
(define (above-lower xt lb)
  (matchLowerBound ,lb
    (LowerBound ([e ext] [c closed])
      ,(matchExtended ,e
         (NegInf () (con bool #t))                 ; -inf: everything is above
         (PosInf () (con bool #f))                 ; +inf: nothing is above
         (Finite ([v val])
           ,(matchPBool ,c
              ;; closed: x >= v   (v <= x)
              (PTrue  () [[ (builtin lessThanEqualsInteger) [(builtin unIData) ,v] ] ,xt])
              ;; open:   x >  v   (v <  x)
              (PFalse () [[ (builtin lessThanInteger)       [(builtin unIData) ,v] ] ,xt])))))))

;; is the integer term `xt` at/below the upper bound term `ub`?
(define (below-upper xt ub)
  (matchUpperBound ,ub
    (UpperBound ([e ext] [c closed])
      ,(matchExtended ,e
         (PosInf () (con bool #t))                 ; +inf: everything is below
         (NegInf () (con bool #f))                 ; -inf: nothing is below
         (Finite ([v val])
           ,(matchPBool ,c
              ;; closed: x <= v
              (PTrue  () [[ (builtin lessThanEqualsInteger) ,xt ] [(builtin unIData) ,v]])
              ;; open:   x <  v
              (PFalse () [[ (builtin lessThanInteger)       ,xt ] [(builtin unIData) ,v]])))))))

(define member
  (uplc
   (lam x
     (lam iv
       ,(matchInterval iv
          (Interval ([lo lo] [hi hi])
            ,(uand (above-lower (uplc x) lo)
                   (below-upper (uplc x) hi))))))))

;; ---------------------------------------------------------------------------
;; Demo
;; ---------------------------------------------------------------------------

(define (member? n iv)
  (uplc-eval (uplc [[ ,member (con integer ,n) ] ,iv])))

(define T "#(con (bool . #t))")
(define F "#(con (bool . #f))")

(define fails 0)
(define (check label iv n want)
  (let* ([got (format "~a" (member? n iv))]
         [ok  (string=? got want)])
    (unless ok (set! fails (+ fails 1)))
    (printf "  ~a member ~a ~a => ~a\n"
            (if ok "ok  " "FAIL") n label
            (cond [(not ok) (format "~a (want ~a)" got want)]
                  [(string=? want T) "in"]
                  [else "out"]))))

(printf "closed [10,20]:\n")
(check "[10,20]" (interval 10 20)  9 F)
(check "[10,20]" (interval 10 20) 10 T)   ; lower endpoint included
(check "[10,20]" (interval 10 20) 15 T)
(check "[10,20]" (interval 10 20) 20 T)   ; upper endpoint included
(check "[10,20]" (interval 10 20) 21 F)

(printf "open (10,20):\n")
(check "(10,20)" (open-interval 10 20) 10 F) ; endpoints excluded
(check "(10,20)" (open-interval 10 20) 11 T)
(check "(10,20)" (open-interval 10 20) 19 T)
(check "(10,20)" (open-interval 10 20) 20 F)

(printf "from 5  = [5,+inf):\n")
(check "[5,+inf)" (from 5)       4 F)
(check "[5,+inf)" (from 5)       5 T)
(check "[5,+inf)" (from 5) 1000000 T)

(printf "to 5    = (-inf,5]:\n")
(check "(-inf,5]" (to 5)        6 F)
(check "(-inf,5]" (to 5)        5 T)
(check "(-inf,5]" (to 5)    -1000 T)

(printf "always / never / singleton:\n")
(check "always"    always-iv  -100 T)
(check "always"    always-iv   999 T)
(check "never"     never-iv      0 F)
(check "never"     never-iv      5 F)
(check "{7}"       (singleton 7) 6 F)
(check "{7}"       (singleton 7) 7 T)
(check "{7}"       (singleton 7) 8 F)

;; A real validator check: "is slot 1000 inside the tx validity range
;; [950,+inf)?" — the canonical on-chain deadline test.
(printf "validator: slot inside [950,+inf)?\n")
(check "[950,+inf)" (from 950) 1000 T)
(check "[950,+inf)" (from 950)  900 F)

(printf "\nData encoding of [10,20] (== PlutusTx toBuiltinData):\n  ~a\n"
        (uplc-run (interval 10 20)))

(printf "\n~a\n" (if (= fails 0) "all interval checks passed"
                     (format "~a CHECK(S) FAILED" fails)))
