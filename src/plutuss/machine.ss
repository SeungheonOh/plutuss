;;; (plutuss machine) — the CEK abstract machine.
;;;
;;; compute and return are mutually tail-recursive: Scheme's proper tail calls
;;; make the machine transitions direct calls, so there is no reified state
;;; vector and no driver loop.  The continuation is still an explicit chain of
;;; context frames (tagged vectors), matching the spec presentation:
;;;
;;;   #(no-frame)
;;;   #(await-fun-term env arg-term next)   evaluating the function of an app
;;;   #(await-arg fun-value next)           evaluating the argument of an app
;;;   #(await-fun-value arg-value next)     applying to an already-known value
;;;   #(force-frame next)
;;;   #(constr-frame env tag rest resolved next)
;;;   #(cases-frame env branches next)
;;;
;;; A partially applied builtin is #(vbuiltin desc forces args nargs) where
;;; desc is the bdesc descriptor, args holds the applied arguments newest-first
;;; (consed, reversed once at saturation), and nargs counts them.
(library (plutuss machine)
  (export machine-run)
  (import (chezscheme) (plutuss base) (plutuss cost)
          (plutuss state) (plutuss builtins))

  (define frame-done (vector 'no-frame))

  (define (machine-run term)
    (parameterize ((current-run-state (new-run-state)))
      (spend! machine-startup-cpu machine-startup-mem)
      (let ((v (compute frame-done empty-env term)))
        (finish-run!)
        (discharge-value v))))

  (define (compute ctx env term)
    (match term
      ((var idx)
       (step!)
       (let ((v (env-lookup env idx)))
         (unless v (eval-failure "open term evaluated"))
         (return ctx v)))
      ((delay body) (step!) (return ctx (vector 'vdelay body env)))
      ((lam nm body) (step!) (return ctx (vector 'vlam nm body env)))
      ((app fun arg) (step!) (compute (vector 'await-fun-term env arg ctx) env fun))
      ((con c) (step!) (return ctx (vector 'vcon c)))
      ((force body) (step!) (compute (vector 'force-frame ctx) env body))
      ((uerror) (eval-failure "error term"))
      ((builtin desc) (step!) (return ctx (vector 'vbuiltin desc 0 '() 0)))
      ((constr tag fields)
       (step!)
       (if (null? fields)
           (return ctx (vector 'vconstr tag '()))
           (compute (vector 'constr-frame env tag (cdr fields) '() ctx) env (car fields))))
      ((case scrut branches)
       (step!)
       (compute (vector 'cases-frame env branches ctx) env scrut))
      (else (error 'compute "bad term" term))))

  (define (return ctx val)
    (match ctx
      ((await-arg fn-val next) (apply-evaluate next fn-val val))
      ((await-fun-term env arg next) (compute (vector 'await-arg val next) env arg))
      ((await-fun-value arg next) (apply-evaluate next val arg))
      ((force-frame next) (force-evaluate next val))
      ((constr-frame env tag fields resolved next)
       (let ((resolved2 (cons val resolved)))
         (if (null? fields)
             (return next (vector 'vconstr tag (reverse resolved2)))
             (compute (vector 'constr-frame env tag (cdr fields) resolved2 next)
                      env (car fields)))))
      ((cases-frame env branches next)
       (match val
         ((vconstr tag cfields)
          (when (>= tag (length branches)) (eval-failure "missing case branch"))
          (compute (transfer-arg-stack cfields next) env (list-ref branches tag)))
         ((vcon c) (case-on-constant c env branches next))
         (else (eval-failure "non-constr scrutinee"))))
      ((no-frame) val)
      (else (error 'return "bad ctx" ctx))))

  (define (force-evaluate ctx val)
    (match val
      ((vdelay body env) (compute ctx env body))
      ((vbuiltin desc forces args nargs)
       (if (fx>? (bdesc-forces desc) forces)
           (return ctx (saturate (vector 'vbuiltin desc (fx+ forces 1) args nargs)))
           (eval-failure "builtin term argument expected")))
      (else (eval-failure "non-polymorphic instantiation"))))

  (define (apply-evaluate ctx fn-val arg)
    (match fn-val
      ((vlam _ body env) (compute ctx (env-extend env arg) body))
      ((vbuiltin desc forces args nargs)
       (if (and (fx<=? (bdesc-forces desc) forces) (fx>? (bdesc-arity desc) nargs))
           (return ctx (saturate (vector 'vbuiltin desc forces (cons arg args) (fx+ nargs 1))))
           (eval-failure "unexpected builtin term argument")))
      (else (eval-failure "non-function application"))))

  (define (saturate val)
    (match val
      ((vbuiltin desc forces args nargs)
       (if (and (fx=? nargs (bdesc-arity desc)) (fx=? forces (bdesc-forces desc)))
           (call-builtin desc args)
           val))))

  ;; push fields so the first one is applied first
  (define (transfer-arg-stack fields ctx)
    (let loop ((fs (reverse fields)) (c ctx))
      (if (null? fs) c (loop (cdr fs) (vector 'await-fun-value (car fs) c)))))

  ;; case over a constant scrutinee, (type . value)
  (define (case-on-constant con env branches rest-ctx)
    (let* ((nb (length branches)) (ty (car con)) (v (cdr con)))
      (case (if (pair? ty) (car ty) ty)
        ((bool)
         (when (or (fx<? nb 1) (fx>? nb 2)) (eval-failure "missing case branch"))
         (let ((tag (if v 1 0)))
           (when (>= tag nb) (eval-failure "missing case branch"))
           (compute rest-ctx env (list-ref branches tag))))
        ((unit)
         (unless (fx=? nb 1) (eval-failure "missing case branch"))
         (compute rest-ctx env (list-ref branches 0)))
        ((integer)
         (when (or (< v 0) (>= v nb)) (eval-failure "missing case branch"))
         (compute rest-ctx env (list-ref branches v)))
        ((list)
         (if (pair? v)
             (begin
               (when (fx<? nb 1) (eval-failure "missing case branch"))
               (let* ((head-val (vector 'vcon (cons (cadr ty) (car v))))
                      (tail-val (vector 'vcon (cons ty (cdr v))))
                      (ctx (transfer-arg-stack (list head-val tail-val) rest-ctx)))
                 (compute ctx env (list-ref branches 0))))
             (if (fx>=? nb 2)
                 (compute rest-ctx env (list-ref branches 1))
                 (eval-failure "missing case branch"))))
        ((pair)
         (unless (fx=? nb 1) (eval-failure "missing case branch"))
         (let* ((fst (vector 'vcon (cons (cadr ty) (car v))))
                (snd (vector 'vcon (cons (caddr ty) (cdr v))))
                (ctx (transfer-arg-stack (list fst snd) rest-ctx)))
           (compute ctx env (list-ref branches 0))))
        (else (eval-failure "non-constr scrutinee")))))

  (define (discharge-value val)
    (match val
      ((vcon c) (vector 'con c))
      ((vbuiltin desc forces args _)
       (let ((forced (let loop ((k forces) (t (vector 'builtin desc)))
                       (if (fx=? k 0) t (loop (fx- k 1) (vector 'force t))))))
         ;; args are newest-first; reversing applies them in application order
         (fold-left (lambda (t a) (vector 'app t (discharge-value a)))
                    forced (reverse args))))
      ((vdelay body env) (vector 'delay (with-env 0 env body)))
      ((vlam nm body env) (vector 'lam nm (with-env 1 env body)))
      ((vconstr tag fields) (vector 'constr tag (map discharge-value fields)))
      (else (error 'discharge "bad value" val))))

  (define (with-env lam-cnt env term)
    (match term
      ((var idx)
       (if (fx>=? lam-cnt idx) term
           (let ((v (env-lookup env (fx- idx lam-cnt))))
             (if v (discharge-value v) term))))
      ((lam nm body) (vector 'lam nm (with-env (fx+ lam-cnt 1) env body)))
      ((app f a) (vector 'app (with-env lam-cnt env f) (with-env lam-cnt env a)))
      ((delay body) (vector 'delay (with-env lam-cnt env body)))
      ((force body) (vector 'force (with-env lam-cnt env body)))
      ((constr tag fields)
       (vector 'constr tag (map (lambda (f) (with-env lam-cnt env f)) fields)))
      ((case scrut branches)
       (vector 'case (with-env lam-cnt env scrut)
               (map (lambda (b) (with-env lam-cnt env b)) branches)))
      (((con builtin uerror)) term)
      (else (error 'with-env "bad term" term)))))
