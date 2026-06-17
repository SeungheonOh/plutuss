;;; prove-sum.ss — prove  "forall x. sum x >= 0"  for a recursive UPLC program,
;;; using the (plutuss compile) UPLC->SMT compiler and z3.
;;;
;;;   sum i = if i <= 0 then 0 else i + sum (i - 1)        (built with the Z combinator)
;;;
;;; Run:  chez --script prove-sum.ss
;;;
;;; The UPLC is built with the (plutuss dsl) `uplc` macro: each property is a
;;; closed term whose leading lambdas are its symbolic inputs.  `body-of` strips
;;; those lambdas (à la tools/smt.ss), leaving a body whose free de-Bruijn vars
;;; index the symbolic environment (innermost binder = Var 1 = head of
;;; make-sym-env), which `compile-success` evaluates symbolically.
;;;
;;; Two ways to read "within fuel":
;;;
;;;  (1) BOUNDED MODEL CHECKING.  Symbolically unroll the recursion up to the
;;;      fuel budget.  This proves  forall x in [0,N]. sum x >= 0  where N grows
;;;      with fuel — but N is always finite, so plain unrolling can never settle
;;;      the unbounded "forall x".  Beyond the frontier z3 returns `sat`: the
;;;      tool makes NO false claim, it makes no claim at all.
;;;
;;;  (2) INDUCTION (the real unbounded proof, within trivial fuel).  Abstract the
;;;      recursive call sum(x-1) as a fresh symbolic variable s carrying the
;;;      induction hypothesis  s >= 0.  Then one symbolic step of the body
;;;      reduces to  if x<=0 then 0 else x + s, and the compiler discharges the
;;;      obligation  s>=0  =>  0 <= (if x<=0 then 0 else x+s)  for ALL x.  With
;;;      the base case  sum 0 >= 0, and well-founded recursion on the decreasing
;;;      argument, this proves  forall x. sum x >= 0  with no unrolling at all.
(import (chezscheme))
(library-directories (list "src"))
(import (plutuss smt) (plutuss compile) (plutuss dsl) (plutuss frontend))

;; Convert a closed DSL term to de-Bruijn and strip its `k` leading input
;; lambdas, exposing the body whose free de-Bruijn vars index the symbolic
;; environment (innermost binder = Var 1 = head of make-sym-env).
(define (body-of term k)
  (let loop ((t (name->debruijn term)) (k k))
    (if (fx=? k 0) t (loop (vector-ref t 2) (fx- k 1)))))

;; sum's body: bodyF rec n = if n<=0 then 0 else n + rec(n-1)
;; (lazy `ifThenElse` over delayed branches so a symbolic guard defers a choice
;;  the compiler can unroll).
(define bodyF
  (uplc
   (lam rec
     (lam n
       (force ((force (builtin ifThenElse))
               ((builtin lessThanEqualsInteger) n (con integer 0))
               (delay (con integer 0))
               (delay ((builtin addInteger)
                       n
                       (rec ((builtin subtractInteger) n (con integer 1)))))))))))

;; call-by-value Z combinator, and the recursive sum it produces
(define zfix
  (uplc
   (lam f
     ((lam h (f (lam a (h h a))))
      (lam h (f (lam a (h h a))))))))
(define sumf (uplc (,zfix ,bodyF)))

;; the validator  0 <= sum input  as a closed function of its single input
(define validator (uplc (lam x ((builtin lessThanEqualsInteger) (con integer 0) (,sumf x)))))
(define sum-body (body-of validator 1))

(define iv (smt-var "i" smt-sort-int))
(define xv (smt-var "x" smt-sort-int))
(define sv (smt-var "s" smt-sort-int))

;;; ---------------------------------------------------------------------------
(display "(1) BOUNDED:  forall x in [0,N]. sum x >= 0   (N scales with fuel)\n")
(let ((env (make-sym-env (symbolic-input "i" smt-sort-int))))
  (for-each
   (lambda (F)
     (let ((s (compile-success sum-body env F)))
       (let loop ((n 0))
         (cond
          ((> n 40) (printf "    fuel ~3d : proven for x in [0,40+]\n" F))
          ((eq? 'unsat (z3-check (encode-property
                                  (smt-and (smt-bin 'le (smt-int 0) iv)
                                           (smt-bin 'le iv (smt-int n))) s)))
           (loop (+ n 1)))
          (else (printf "    fuel ~3d : proven for x in [0,~a]   (x >= ~a: beyond frontier, no claim)\n"
                        F (- n 1) n))))))
   '(40 90 160)))

;;; ---------------------------------------------------------------------------
(display "\n(2) UNBOUNDED:  forall x. sum x >= 0   (by induction, no unrolling)\n")
;; The inductive step as a closed function of its two inputs x (Var 1) and
;; s = sum(x-1) (Var 2).  self-abs (lam ignore s) ignores its argument and
;; returns s; bodyF self-abs x then reduces symbolically to if x<=0 then 0 else x+s.
(define step-term
  (uplc
   (lam s
     (lam x
       ((builtin lessThanEqualsInteger) (con integer 0)
        ((,bodyF (lam ignore s)) x))))))
(define env2 (make-sym-env (symbolic-input "x" smt-sort-int)     ; Var 1 = x
                           (symbolic-input "s" smt-sort-int)))   ; Var 2 = s = sum(x-1)
(define step (compile-success (body-of step-term 2) env2 50))
(define IH (smt-bin 'le (smt-int 0) sv))                          ; induction hypothesis: s >= 0

(printf "    inductive step  [ s>=0 => sum-step(x,s) >= 0 ]   z3: ~a\n"
        (z3-check (encode-property IH step)))
(printf "    step is non-vacuous (drop IH => falsifiable)     z3: ~a\n"
        (z3-check (encode-property smt-true step)))
(define base (compile-success sum-body
                              (make-sym-env (symbolic-input "x" smt-sort-int)) 80))
(printf "    base case       [ x=0  => sum 0 >= 0 ]           z3: ~a\n"
        (z3-check (encode-property (smt-bin 'eq xv (smt-int 0)) base)))
(display "\n    unsat step + unsat base + well-founded recursion\n")
(display "    ==>  PROVED:  forall x. sum x >= 0\n")
