;;; (plutuss state) — per-run machine state: execution budget, trace logs, and
;;; the value environment.  The budget lives in a run-state record bound to the
;;; current-run-state parameter, so machine runs are reentrant: machine-run
;;; parameterizes a fresh record and captures it via finish-run! so the
;;; get-*-spent getters keep working after the run returns.
(library (plutuss state)
  (export current-run-state new-run-state finish-run!
          get-cpu-spent get-mem-spent get-mach-logs
          spend! step! flush-steps! log-trace!
          env-extend env-lookup empty-env)
  (import (chezscheme) (plutuss cost))

  (define-record-type run-state
    (fields (mutable cpu) (mutable mem) (mutable steps) (mutable logs)))
  (define (new-run-state) (make-run-state 0 0 0 '()))

  (define current-run-state (make-parameter (new-run-state)))

  ;; last finished run, for reading budget/logs after machine-run returns
  (define last-run (new-run-state))
  (define (finish-run!)
    (flush-steps!)
    (set! last-run (current-run-state)))

  (define (get-cpu-spent) (run-state-cpu last-run))
  (define (get-mem-spent) (run-state-mem last-run))
  (define (get-mach-logs) (run-state-logs last-run))   ; reversed list of trace strings

  (define (spend! cpu mem)
    (let ((rs (current-run-state)))
      (run-state-cpu-set! rs (+ (run-state-cpu rs) cpu))
      (run-state-mem-set! rs (+ (run-state-mem rs) mem))))
  (define (step!)
    (let* ((rs (current-run-state)) (n (fx+ (run-state-steps rs) 1)))
      (run-state-steps-set! rs n)
      (when (fx>=? n 200) (flush-run-steps! rs))))
  (define (flush-steps!) (flush-run-steps! (current-run-state)))
  (define (flush-run-steps! rs)
    (let ((n (run-state-steps rs)))
      (when (fx>? n 0)
        (run-state-cpu-set! rs (+ (run-state-cpu rs) (* n machine-step-cpu)))
        (run-state-mem-set! rs (+ (run-state-mem rs) (* n machine-step-mem)))
        (run-state-steps-set! rs 0))))
  (define (log-trace! s)
    (let ((rs (current-run-state)))
      (run-state-logs-set! rs (cons s (run-state-logs rs)))))

  (define empty-env '())
  (define (env-extend env v) (cons v env))
  (define (env-lookup env i)             ; i is 1-based
    (let loop ((e env) (k (fx- i 1)))
      (cond ((null? e) #f)
            ((fx=? k 0) (car e))
            (else (loop (cdr e) (fx- k 1)))))))
