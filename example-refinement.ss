;;; example-refinement.ss -- UPLC-predicate refinement checks solved by z3.
;;;
;;; Run:  chez --script example-refinement.ss
;;;       chez --script example-refinement.ss --verbose

(import (chezscheme))
(library-directories (list "src"))
(import (plutuss refine))

(define verbose? (and (> (length (command-line)) 1)
                      (string=? (cadr (command-line)) "--verbose")))

(define-upred nonNegative
  ((x integer))
  [[[(force (builtin ifThenElse))
     [[(builtin lessThanInteger) x] (con integer 0)]]
    (con bool #f)]
   (con bool #t)])

(define-upred negative
  ((x integer))
  [[(builtin lessThanInteger) x] (con integer 0)])

(define-upred notZero
  ((x integer))
  [[[(force (builtin ifThenElse))
     [[(builtin equalsInteger) x] (con integer 0)]]
    (con bool #f)]
   (con bool #t)])

;; A UPLC predicate over symbolic Val constructors:
;;   Nothing = constr 0 []
;;   Just x  = constr 1 [x]
(define-upred isJust
  ((m anyV))
  (case m
    (con bool #f)
    (lam v (con bool #t))))

(define/refined id-nonneg
  ((x integer #:where (nonNegative x)))
  #:returns (r integer #:where (nonNegative r))
  x)

(define/refined composed-id-nonneg
  ((x integer #:where (nonNegative x)))
  #:returns (r integer #:where (nonNegative r))
  [(unquote (refined-function-term id-nonneg)) x])

(define/refined badDec
  ((x integer #:where (nonNegative x)))
  #:returns (r integer #:where (nonNegative r))
  [[(builtin subtractInteger) x] (con integer 1)])

(define/refined safeDiv
  ((x integer)
   (y integer #:where (notZero y)))
  #:returns (r integer)
  [[(builtin divideInteger) x] y])

(define/refined unsafeDiv
  ((x integer)
   (y integer))
  #:returns (r integer)
  [[(builtin divideInteger) x] y])

(define/refined fromJust
  ((m anyV #:where (isJust m)))
  #:returns (v anyV)
  (case m
    (error)
    (lam v v)))

(define/refined unsafeFromJust
  ((m anyV))
  #:returns (v anyV)
  (case m
    (error)
    (lam v v)))

(define/refined impossible-input
  ((x integer #:where (nonNegative x) #:where (negative x)))
  #:returns (r integer)
  x)

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

(expect "identity preserves nonNegative"
        (verify/refine id-nonneg)
        #t)

(expect "refined functions compose by inlining their UPLC term"
        (verify/refine composed-id-nonneg)
        #t)

(expect "decrement does not preserve nonNegative"
        (verify/refine badDec)
        #f)

(expect "notZero precondition proves divideInteger cannot error"
        (verify/refine safeDiv)
        #t)

(expect "divideInteger without notZero can error"
        (verify/refine unsafeDiv)
        #f)

(expect "isJust precondition proves fromJust cannot error"
        (verify/refine fromJust)
        #t)

(expect "fromJust without isJust can error"
        (verify/refine unsafeFromJust)
        #f)

(expect "contradictory input predicates are rejected as vacuous"
        (verify/refine impossible-input)
        #f)

(printf "\n~a passed, ~a failed\n" passes fails)
(when (> fails 0) (exit 1))
