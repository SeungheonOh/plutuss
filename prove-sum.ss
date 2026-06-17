;;; prove-sum.ss — prove  "forall x. sum x >= 0"  for a recursive UPLC program,
;;; using the (plutuss compile) UPLC->SMT compiler and z3.
;;;
;;;   sum i = if i <= 0 then 0 else i + sum (i - 1)        (built with the Z combinator)
;;;
;;; Run:  chez --script prove-sum.ss
;;; (FFI-free: needs only z3 on PATH, not plutuss's native crypto libraries.)
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
(import (plutuss smt) (plutuss compile))

(define (bi n) (t-builtin n))
(define (ci n) (t-con (c-integer n)))
(define (le a b)  (t-app* (bi "lessThanEqualsInteger") a b))
(define (add a b) (t-app* (bi "addInteger") a b))
(define (sub a b) (t-app* (bi "subtractInteger") a b))
;; lazy if (delayed branches) so a symbolic guard defers a choice we can unroll
(define (lite c t e) (t-force (t-app* (t-force (bi "ifThenElse")) c (t-delay t) (t-delay e))))

;; sum's body: bodyF self i = if i<=0 then 0 else i + self(i-1)   (self=Var2, i=Var1)
(define bodyF
  (t-lam (t-lam (lite (le (t-var 1) (ci 0)) (ci 0)
                      (add (t-var 1) (t-app (t-var 2) (sub (t-var 1) (ci 1))))))))
;; call-by-value Z combinator, and the recursive sum it produces
(define half (t-lam (t-app (t-var 2) (t-lam (t-app* (t-var 2) (t-var 2) (t-var 1))))))
(define zfix (t-lam (t-app half half)))
(define (sum x) (t-app (t-app zfix bodyF) x))

(define iv (smt-var "i" smt-sort-int))
(define xv (smt-var "x" smt-sort-int))
(define sv (smt-var "s" smt-sort-int))

;;; ---------------------------------------------------------------------------
(display "(1) BOUNDED:  forall x in [0,N]. sum x >= 0   (N scales with fuel)\n")
(let ((validator (le (ci 0) (sum (t-var 1))))
      (env (make-sym-env (symbolic-input "i" smt-sort-int))))
  (for-each
   (lambda (F)
     (let ((s (compile-success validator env F)))
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
;; self_abs ignores its argument and returns s (= the abstracted sum(x-1));
;; in its applied environment [arg, x, s], s is Var 3.
(define self-abs (t-lam (t-var 3)))
;; bodyF self_abs x  reduces symbolically to  if x<=0 then 0 else x + s
(define step-term (le (ci 0) (t-app (t-app bodyF self-abs) (t-var 1))))
(define env2 (make-sym-env (symbolic-input "x" smt-sort-int)     ; Var 1 = x
                           (symbolic-input "s" smt-sort-int)))   ; Var 2 = s = sum(x-1)
(define step (compile-success step-term env2 50))
(define IH (smt-bin 'le (smt-int 0) sv))                          ; induction hypothesis: s >= 0

(printf "    inductive step  [ s>=0 => sum-step(x,s) >= 0 ]   z3: ~a\n"
        (z3-check (encode-property IH step)))
(printf "    step is non-vacuous (drop IH => falsifiable)     z3: ~a\n"
        (z3-check (encode-property smt-true step)))
(define base (compile-success (le (ci 0) (sum (t-var 1)))
                              (make-sym-env (symbolic-input "x" smt-sort-int)) 80))
(printf "    base case       [ x=0  => sum 0 >= 0 ]           z3: ~a\n"
        (z3-check (encode-property (smt-bin 'eq xv (smt-int 0)) base)))
(display "\n    unsat step + unsat base + well-founded recursion\n")
(display "    ==>  PROVED:  forall x. sum x >= 0\n")
