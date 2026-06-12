(import (chezscheme))
(load "src/load.ss")

(define (set-3bytevector-at! bv pos n)
  (bytevector-u8-set! bv pos (bitwise-and (bitwise-arithmetic-shift-right n 16) #xff))
  (bytevector-u8-set! bv (+ 1 pos) (bitwise-and (bitwise-arithmetic-shift-right n 8)  #xff))
  (bytevector-u8-set! bv (+ 2 pos) (bitwise-and n #xff)))

(define (fibo n)
  (let loop ([n n] [x 0] [y 1])
    (case n
      [0 x]
      [1 y]
      [else (loop (- n 1) y (+ x y))])))

(define fibo-packed
  (uplc
   (con
    bytestring
    (let* ([n 26]
           [pack (make-bytevector (* n 3))])
      (let loop ([i 0])
        (when (< i n)
          (set-3bytevector-at! pack (* i 3) (fibo i))
          (loop (+ i 1))))
      pack)
    )))

(define fibo
  (uplc
   (lam
    i-0
    (force
     (case
         (constr
          0
          [ [ (builtin lessThanEqualsInteger) i-0 ] (con integer 0) ]
          (delay i-0)
          (delay
            [
             [ (builtin byteStringToInteger) (con bool 'true) ]
             (case
                 (constr
                  0
                  [ [ (builtin multiplyInteger) i-0 ] (con integer 3) ]
                  (con integer 3)
                  ($ fibo-packed)
                  )
               (builtin sliceByteString)
               )
             ]
            )
          )
       (force (builtin ifThenElse))
       )
     )
    )
   ))

(uplc-eval (uplc [($ fibo) (con integer 10)] ))
(uplc-eval (uplc [($ fibo) (con integer 15)] ))
