(define (a [x : Integer]) : Integer
  (let ([x (+ x 4)])
    (- x 100)))

(define (b [y : Integer]) : Integer
  (let ([x (+ y 100)])
    (let ([y (+ y (- x 12))])
      (let ([z (vector 10 23 y)])
        (let ([y 0])
          (+ x (+ y (+ (vector-ref z 2) (vector-ref z
                                                    0)))))))))

(+ (a 10) (b 100))
