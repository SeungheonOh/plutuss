;;; example-symbolic.ss — worked examples for the UPLC->SMT symbolic compiler,
;;; solved by z3.  A Scheme port of `Test/Symbolic/Examples.lean` (moist).
;;;
;;; Each example builds a UPLC `Term` directly (no parser/DSL, so this stays
;;; FFI-free), compiles it to SMT-LIB with (plutuss compile), and shells out to z3
;;; to actually solve for the inputs.  Every example asserts an *expected* verdict
;;; so this doubles as a regression test.
;;;
;;; Run:  chez --script example-symbolic.ss          (concise: pass/fail per case)
;;;       chez --script example-symbolic.ss --emit    (also print each SMT script)

(import (chezscheme))
(library-directories (list "src"))
(import (plutuss smt) (plutuss compile))

;;; ===== Term builders (de Bruijn; Var 1 = innermost / first symbolic input) =====
(define (intC n)  (vector 'con (cons 'integer n)))
(define (boolC b) (vector 'con (cons 'bool b)))
(define (bsC bytes) (vector 'con (cons 'bytestring (u8-list->bytevector bytes))))
(define unitC (vector 'con (cons 'unit '())))
(define (var k) (vector 'var k))
(define (bi name) (vector 'builtin name))
(define (app f a) (vector 'app f a))
(define (force t) (vector 'force t))
(define (delay t) (vector 'delay t))
(define (lam body) (vector 'lam '_ body))            ; de Bruijn: the name is irrelevant
(define (constr tag fields) (vector 'constr tag fields))
(define (kase scrut alts) (vector 'case scrut alts)) ; `case` is a Chez keyword
(define uerror (vector 'uerror))
(define (b1 b a) (app (bi b) a))
(define (b2 b x y) (app (app (bi b) x) y))
;; ifThenElse c t e (polymorphic builtin: one force + three values)
(define (ite3 c t e) (app (app (app (force (bi 'ifThenElse)) c) t) e))

;;; ===== z3 verdict (mirror Examples.lean `verdict`) =====
(define (string-split-lines s)
  (let ((n (string-length s)))
    (let loop ((i 0) (start 0) (acc '()))
      (cond ((fx=? i n) (reverse (cons (substring s start i) acc)))
            ((char=? (string-ref s i) #\newline) (loop (fx+ i 1) (fx+ i 1) (cons (substring s start i) acc)))
            (else (loop (fx+ i 1) start acc))))))
(define (string-trim s)
  (let ((n (string-length s)))
    (let l ((i 0) (j n))
      (cond ((and (fx<? i j) (char-whitespace? (string-ref s i))) (l (fx+ i 1) j))
            ((and (fx<? i j) (char-whitespace? (string-ref s (fx- j 1)))) (l i (fx- j 1)))
            (else (substring s i j))))))
(define (substring? hay needle)
  (let ((hn (string-length hay)) (nn (string-length needle)))
    (let loop ((i 0))
      (cond ((fx>? (fx+ i nn) hn) #f)
            ((string=? (substring hay i (fx+ i nn)) needle) #t)
            (else (loop (fx+ i 1)))))))
(define (line-after lines target)
  (cond ((null? lines) "")
        ((string=? (car lines) target) (if (null? (cdr lines)) "" (cadr lines)))
        (else (line-after (cdr lines) target))))

;; Interpret z3's answer.  Moist-style scripts are unlabelled, so unsat means
;; there is no witness for the asserted bounded query.
(define (verdict z3out)
  (let ((lines (map string-trim (string-split-lines z3out))))
    (cond
     ((member "unsat" lines) 'unsat-genuine)
     ((member "sat" lines) 'sat)
     (else 'unknown))))

(define emit? (and (> (length (command-line)) 1) (string=? (cadr (command-line)) "--emit")))
(define passes 0)
(define fails 0)
(define (demo title c goal expected)
  (let ((smt (compiled->smtlib c goal)))
    (when emit?
      (printf "~a\n~a\n~a\n" (make-string 64 #\=) title (make-string 64 #\=))
      (display smt) (display "---- z3 ----\n"))
    (let ((v (verdict (run-z3 smt))))
      (cond
       ((eq? v expected) (set! passes (+ passes 1)) (printf "  [ ok ] ~a  => ~a\n" title v))
       (else (set! fails (+ fails 1)) (printf "  [FAIL] ~a  => got ~a, expected ~a\n" title v expected))))))

;;; ===== Example 1 — symbolic equalsInteger/addInteger =====
;; equalsInteger 10 (addInteger 5 x), solve result = true (expect x = 5).
(define ex1 (b2 'equalsInteger (intC 10) (b2 'addInteger (intC 5) (var 1))))
(demo "Ex1: equalsInteger 10 (addInteger 5 x) = true   (expect x = 5)"
      (uplc-symbolic-compile 10 (list (cons "x" 'integer)) ex1)
      (lambda (r) (goal-returns-bool r #t)) 'sat)

;;; ===== Example 2 — symbolic builtin Case on an Integer =====
;; case x [error, error, true]; the only non-erroring branch is index 2 (expect x = 2).
(define ex2 (kase (var 1) (list uerror uerror (boolC #t))))
(demo "Ex2: case x [error, error, true] = true   (expect x = 2)"
      (uplc-symbolic-compile 10 (list (cons "x" 'integer)) ex2)
      (lambda (r) (goal-returns-bool r #t)) 'sat)

;;; ===== Example 3 — ifThenElse building a Constr, then Case on it =====
;; case (if x==10 then Constr0[] else Constr1[]) [error, true]: errors exactly when x = 10.
(define ex3 (kase (ite3 (b2 'equalsInteger (var 1) (intC 10)) (constr 0 '()) (constr 1 '()))
                  (list uerror (boolC #t))))
(demo "Ex3: case (if x==10 then C0 else C1) [error, true] ERRORS   (expect x = 10)"
      (uplc-symbolic-compile 12 (list (cons "x" 'integer)) ex3) goal-errors 'sat)
(demo "Ex3b: same term returns true   (expect any x != 10)"
      (uplc-symbolic-compile 12 (list (cons "x" 'integer)) ex3)
      (lambda (r) (goal-returns-bool r #t)) 'sat)

;;; ===== Example 4 — force/delay interacting with symbolic data (lazy branch) =====
;; force (if x<0 then delay 100 else delay (x+x)); only the selected thunk is forced.
;; Solve x+x = 6 (expect x = 3).
(define ex4 (force (ite3 (b2 'lessThanInteger (var 1) (intC 0))
                         (delay (intC 100))
                         (delay (b2 'addInteger (var 1) (var 1))))))
(demo "Ex4: force (if x<0 then delay 100 else delay (x+x)) = 6   (expect x = 3)"
      (uplc-symbolic-compile 14 (list (cons "x" 'integer)) ex4)
      (lambda (r) (goal-returns-int r 6)) 'sat)

;;; ===== Example 5 — hashing via uninterpreted functions =====
;; equalsByteString (sha2_256 a) (sha2_256 b): the reference CEK does not implement
;; sha2_256 is modelled as an uninterpreted SMT function with precise type guards,
;; so congruence lets z3 find witnesses without native crypto.
(define ex5 (b2 'equalsByteString (b1 'sha2_256 (var 1)) (b1 'sha2_256 (var 2))))
(demo "Ex5: equalsByteString (sha2_256 a) (sha2_256 b) = true   (UF congruence)"
      (uplc-symbolic-compile 12 (list (cons "a" 'bytestring) (cons "b" 'bytestring)) ex5)
      (lambda (r) (goal-returns-bool r #t)) 'sat)

;;; ===== Example 6 — bounded recursion (the fueled sum) =====
;; sum n = if n < 1 then 0 else n + sum (n-1), via the call-by-value Z-combinator.
;; Z = λf. (λx. f (λv. x x v)) (λx. f (λv. x x v))
(define zComb
  (let ((m (lam (app (var 2) (lam (app (app (var 2) (var 2)) (var 1)))))))
    (lam (app m m))))
;; F = λself. λn. force (if n<1 then delay 0 else delay (n + self (n-1)))
(define sumF
  (lam (lam (force (ite3 (b2 'lessThanInteger (var 1) (intC 1))
                         (delay (intC 0))
                         (delay (b2 'addInteger (var 1)
                                    (app (var 2) (b2 'subtractInteger (var 1) (intC 1))))))))))
(define (ex6) (app (app zComb sumF) (var 1)))
(demo "Ex6: bounded recursion  sum n = 10   (expect n = 4)"
      (uplc-symbolic-compile 200 (list (cons "n" 'integer)) (ex6))
      (lambda (r) (goal-returns-int r 10)) 'sat)

;;; ===== Partiality / bidirectionality checks (tight error condition) =====
;; For Ex2, x = 2 must be the UNIQUE non-erroring input: assert succeeds AND x != 2
;; (expect unsat, genuine).
(demo "Partiality 2: (succeeds AND x != 2) for `case x [err,err,true]`   (expect UNSAT genuine)"
      (uplc-symbolic-compile 10 (list (cons "x" 'integer)) ex2)
      (lambda (r) (append (goal-succeeds r) (list (cons "assume_xne2" (sNot (sEq (s-atom "x") (s-int 2)))))))
      'unsat-genuine)
;; For Ex3, x = 10 must always error: assert succeeds AND x = 10 (expect unsat, genuine).
(demo "Partiality 3: (succeeds AND x = 10) for Ex3   (expect UNSAT genuine — must error)"
      (uplc-symbolic-compile 12 (list (cons "x" 'integer)) ex3)
      (lambda (r) (append (goal-succeeds r) (list (cons "assume_xeq10" (sEq (s-atom "x") (s-int 10))))))
      'unsat-genuine)

;;; ===== Builtin type-checking matches the CEK (the MkCons concern) =====
(define mkNilD (app (bi 'mkNilData) unitC))            ; an empty list(data)
(define (mkConsT head tail) (app (app (force (bi 'mkCons)) head) tail))
;; Ill-typed: cons the INTEGER x onto a list(data) — the CEK errors for every x.
(define exConsBad (mkConsT (var 1) mkNilD))
(demo "MkCons: cons Int onto list(data) can succeed?   (expect UNSAT genuine)"
      (uplc-symbolic-compile 12 (list (cons "x" 'integer)) exConsBad) goal-succeeds 'unsat-genuine)
(demo "MkCons: cons Int onto list(data) errors          (expect SAT)"
      (uplc-symbolic-compile 12 (list (cons "x" 'integer)) exConsBad) goal-errors 'sat)
;; Well-typed: cons (iData x) (a Data) onto a list(data) — succeeds.
(define exConsGood (mkConsT (b1 'iData (var 1)) mkNilD))
(demo "MkCons: cons (iData x) onto list(data) succeeds   (expect SAT)"
      (uplc-symbolic-compile 12 (list (cons "x" 'integer)) exConsGood) goal-succeeds 'sat)

;;; ===== Diagnosing recursion and fuel =====
;; sum n = 55 needs n = 10 (~10 unrollings).  With too little fuel the witness is
;; beyond the horizon, so this bounded query is unsat at that fuel.
(demo "Recursion diag: sum n = 55 at LOW fuel   (expect bounded UNSAT)"
      (uplc-symbolic-compile 70 (list (cons "n" 'integer)) (ex6))
      (lambda (r) (goal-returns-int r 55)) 'unsat-genuine)
;; Enough fuel: the same query now finds n = 10.
(demo "Recursion diag: sum n = 55 at HIGH fuel   (expect SAT, n = 10)"
      (uplc-symbolic-compile 130 (list (cons "n" 'integer)) (ex6))
      (lambda (r) (goal-returns-int r 55)) 'sat)
;; Fuel coverage: is any n beyond this fuel horizon? sat => bound not total.
(demo "Recursion diag: is any n beyond the fuel horizon?   (expect SAT)"
      (uplc-symbolic-compile 200 (list (cons "n" 'integer)) (ex6)) goal-indeterminate 'sat)

(printf "\n~a passed, ~a failed\n" passes fails)
(when (> fails 0) (exit 1))
