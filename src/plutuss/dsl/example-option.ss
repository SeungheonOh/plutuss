;;; example-option.ss — the original `define-plutus-type-Data` smoke test.
;;;
;;; Run from the repo root:
;;;   chez --script src/plutuss/dsl/example-option.ss
;;;
;;; Models a Data-encoded Maybe/Option and shows construction + matching.

(import (chezscheme))
(library-directories (list "src"))
(import (plutuss base) (plutuss dsl) (plutuss dsl datatype))

(define (pr label x) (display label) (display x) (newline))

(define-plutus-type-Data Option
  (None)
  (Some foo bar))

;; Construction: mkSome a b  ->  (con data (Constr 1 [a, b]))
(pr "mkSome 1 3      => "
    (uplc-run (mkSome (con data (I 1)) (con data (I 3)))))

;; Matching a Some: sum the two integer fields.
(pr "match Some(1,3) => "
    (uplc-run
     (matchOption
      ,(mkSome (con data (I 1)) (con data (I 3)))
      (Some ([x foo] [y bar])
            [(builtin addInteger) [(builtin unIData) ,x] [(builtin unIData) ,y]])
      (None () (con integer 42)))))

(pr "match Some(1,3) => "
    (uplc-run
     (matchOption
      ,(mkSome (con data (I 1)) (con data (I 3)))
      (Some ([x foo] [y bar])
            ((builtin addInteger) ((builtin unIData) ,x) ((builtin unIData) ,y)))
      (None () (con integer 42)))))

;; Matching a None: take the default branch.
(pr "match None      => "
    (uplc-run
     (matchOption
      ,mkNone
      (Some ([x foo] [y bar])
            [(builtin addInteger) [(builtin unIData) ,x] [(builtin unIData) ,y]])
      (None () (con integer 42)))))
