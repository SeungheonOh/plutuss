;;; load.ss — load the full pluscheme implementation (interpreted).
(define src-dir
  (let ((p (car (command-line))))
    ;; fall back to "src" relative to cwd
    "src"))
(load (string-append src-dir "/frontend.ss"))
(load (string-append src-dir "/value.ss"))
(load (string-append src-dir "/cost.ss"))
(load (string-append src-dir "/machine.ss"))
(load (string-append src-dir "/builtins.ss"))
(load (string-append src-dir "/data.ss"))
(load (string-append src-dir "/bitwise.ss"))
(load (string-append src-dir "/value-builtins.ss"))
(load (string-append src-dir "/crypto.ss"))
(load (string-append src-dir "/bls.ss"))
(load (string-append src-dir "/output.ss"))
(load (string-append src-dir "/flat.ss"))
(load (string-append src-dir "/dsl.ss"))
