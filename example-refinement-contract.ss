;;; example-refinement-contract.ss -- contract-shaped refinement examples.
;;;
;;; These examples model the shape of common validator checks without depending
;;; on Cardano's full ScriptContext encoding.  Bytestrings stand in for
;;; PubKeyHash/token names, and integers stand in for POSIX time, lovelace, and
;;; token quantities.
;;;
;;; Run:  chez --script example-refinement-contract.ss
;;;       chez --script example-refinement-contract.ss --verbose

(import (chezscheme))
(library-directories (list "src"))
(import (plutuss refine))

(define verbose? (and (> (length (command-line)) 1)
                      (string=? (cadr (command-line)) "--verbose")))

;;; ---- UPLC predicates ------------------------------------------------------

(define-upred signedBy
  ((expected bytestring) (actual bytestring))
  [(builtin equalsByteString) expected actual])

(define-upred beforeOrAt
  ((now integer) (deadline integer))
  [(builtin lessThanEqualsInteger) now deadline])

(define-upred afterDeadline
  ((deadline integer) (now integer))
  [(builtin lessThanInteger) deadline now])

(define-upred positive
  ((x integer))
  [(builtin lessThanInteger) (con integer 0) x])

(define-upred nonNegative
  ((x integer))
  [(builtin lessThanEqualsInteger) (con integer 0) x])

(define-upred atLeast
  ((required integer) (actual integer))
  [(builtin lessThanEqualsInteger) required actual])

(define-upred atMost
  ((actual integer) (limit integer))
  [(builtin lessThanEqualsInteger) actual limit])

(define-upred nonEmptyBytes
  ((bs bytestring))
  [(builtin lessThanInteger)
   (con integer 0)
   [(builtin lengthOfByteString) bs]])

;;; ---- Escrow release -------------------------------------------------------

;; Seller can release before the deadline only if the seller signs and the
;; paid lovelace covers the agreed price.  The body is written as direct UPLC:
;; each check selects the delayed continuation or delayed error.
(define/refined release-escrow
  ((seller bytestring)
   (signer bytestring #:where (signedBy seller signer))
   (deadline integer)
   (now integer #:where (beforeOrAt now deadline))
   (price integer #:where (positive price))
   (paid integer #:where (atLeast price paid)))
  #:returns (ok bool)
  (force
   [[[(force (builtin ifThenElse))
      [(builtin equalsByteString) seller signer]]
     (delay
      (force
       [[[(force (builtin ifThenElse))
          [(builtin lessThanEqualsInteger) now deadline]]
        (delay
         (force
          [[[(force (builtin ifThenElse))
             [(builtin lessThanInteger) (con integer 0) price]]
            (delay
             (force
              [[[(force (builtin ifThenElse))
                 [(builtin lessThanEqualsInteger) price paid]]
                (delay (con bool #t))]
               (delay (error))]))]
           (delay (error))]))]
       (delay (error))]))]
    (delay (error))]))

(define/refined release-without-signature
  ((seller bytestring)
   (signer bytestring)
   (deadline integer)
   (now integer #:where (beforeOrAt now deadline))
   (price integer #:where (positive price))
   (paid integer #:where (atLeast price paid)))
  #:returns (ok bool)
  (force
   [[[(force (builtin ifThenElse))
      [(builtin equalsByteString) seller signer]]
     (delay
      (force
       [[[(force (builtin ifThenElse))
          [(builtin lessThanEqualsInteger) now deadline]]
        (delay
         (force
          [[[(force (builtin ifThenElse))
             [(builtin lessThanInteger) (con integer 0) price]]
            (delay
             (force
              [[[(force (builtin ifThenElse))
                 [(builtin lessThanEqualsInteger) price paid]]
                (delay (con bool #t))]
               (delay (error))]))]
           (delay (error))]))]
       (delay (error))]))]
    (delay (error))]))

;;; ---- Refund path ----------------------------------------------------------

;; Buyer can refund only after the deadline and only with the buyer's signature.
(define/refined refund-escrow
  ((buyer bytestring)
   (signer bytestring #:where (signedBy buyer signer))
   (deadline integer)
   (now integer #:where (afterDeadline deadline now))
   (price integer #:where (positive price)))
  #:returns (ok bool)
  (force
   [[[(force (builtin ifThenElse))
      [(builtin equalsByteString) buyer signer]]
     (delay
      (force
       [[[(force (builtin ifThenElse))
          [(builtin lessThanInteger) deadline now]]
        (delay
         (force
          [[[(force (builtin ifThenElse))
             [(builtin lessThanInteger) (con integer 0) price]]
            (delay (con bool #t))]
           (delay (error))]))]
       (delay (error))]))]
    (delay (error))]))

(define/refined refund-before-deadline
  ((buyer bytestring)
   (signer bytestring #:where (signedBy buyer signer))
   (deadline integer)
   (now integer)
   (price integer #:where (positive price)))
  #:returns (ok bool)
  (force
   [[[(force (builtin ifThenElse))
      [(builtin equalsByteString) buyer signer]]
     (delay
      (force
       [[[(force (builtin ifThenElse))
          [(builtin lessThanInteger) deadline now]]
        (delay
         (force
          [[[(force (builtin ifThenElse))
             [(builtin lessThanInteger) (con integer 0) price]]
            (delay (con bool #t))]
           (delay (error))]))]
       (delay (error))]))]
    (delay (error))]))

;;; ---- Minting policy -------------------------------------------------------

;; A minting policy normally requires an authority signature, a non-empty token
;; name, and a positive mint amount.
(define/refined mint-policy
  ((authority bytestring)
   (signer bytestring #:where (signedBy authority signer))
   (tokenName bytestring #:where (nonEmptyBytes tokenName))
   (amount integer #:where (positive amount)))
  #:returns (ok bool)
  (force
   [[[(force (builtin ifThenElse))
      [(builtin equalsByteString) authority signer]]
     (delay
      (force
       [[[(force (builtin ifThenElse))
          [(builtin lessThanInteger)
           (con integer 0)
           [(builtin lengthOfByteString) tokenName]]]
        (delay
         (force
          [[[(force (builtin ifThenElse))
             [(builtin lessThanInteger) (con integer 0) amount]]
            (delay (con bool #t))]
           (delay (error))]))]
       (delay (error))]))]
    (delay (error))]))

(define/refined mint-with-empty-token-name
  ((authority bytestring)
   (signer bytestring #:where (signedBy authority signer))
   (tokenName bytestring)
   (amount integer #:where (positive amount)))
  #:returns (ok bool)
  (force
   [[[(force (builtin ifThenElse))
      [(builtin equalsByteString) authority signer]]
     (delay
      (force
       [[[(force (builtin ifThenElse))
          [(builtin lessThanInteger)
           (con integer 0)
           [(builtin lengthOfByteString) tokenName]]]
        (delay
         (force
          [[[(force (builtin ifThenElse))
             [(builtin lessThanInteger) (con integer 0) amount]]
            (delay (con bool #t))]
           (delay (error))]))]
       (delay (error))]))]
    (delay (error))]))

;;; ---- Fee-adjusted payout --------------------------------------------------

;; Model a payout calculation: seller receives price - fee.  The refinement
;; proves the payout remains non-negative when fee is bounded by price.
(define/refined fee-adjusted-payout
  ((price integer #:where (nonNegative price))
   (fee integer #:where (nonNegative fee) #:where (atMost fee price)))
  #:returns (payout integer #:where (nonNegative payout))
  [(builtin subtractInteger) price fee])

(define/refined unsafe-fee-adjusted-payout
  ((price integer #:where (nonNegative price))
   (fee integer #:where (nonNegative fee)))
  #:returns (payout integer #:where (nonNegative payout))
  [(builtin subtractInteger) price fee])

;;; ---- Test harness ---------------------------------------------------------

(define passes 0)
(define fails 0)

(define (expect title verification want-ok?)
  (let ((got (refinement-verification-ok? verification)))
    (when verbose? (display-refinement-report verification))
    (cond ((eq? got want-ok?)
           (set! passes (+ passes 1))
           (printf "  [ ok ] ~a => ~a\n" title got))
          (else
           (set! fails (+ fails 1))
           (printf "  [FAIL] ~a => got ~a, expected ~a\n" title got want-ok?)
           (display-refinement-report verification)))))

(expect "escrow release: seller signed, before deadline, paid enough"
        (verify/refine release-escrow)
        #t)

(expect "escrow release without signer precondition is rejectable"
        (verify/refine release-without-signature)
        #f)

(expect "refund: buyer signed and deadline passed"
        (verify/refine refund-escrow)
        #t)

(expect "refund without deadline precondition is rejectable"
        (verify/refine refund-before-deadline)
        #f)

(expect "mint policy: authority signed, token name non-empty, amount positive"
        (verify/refine mint-policy)
        #t)

(expect "mint policy without token-name refinement is rejectable"
        (verify/refine mint-with-empty-token-name)
        #f)

(expect "fee-adjusted payout remains non-negative when fee <= price"
        (verify/refine fee-adjusted-payout)
        #t)

(expect "fee-adjusted payout without fee bound can go negative"
        (verify/refine unsafe-fee-adjusted-payout)
        #f)

(printf "\n~a passed, ~a failed\n" passes fails)
(when (> fails 0) (exit 1))
