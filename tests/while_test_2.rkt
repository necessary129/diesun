(let ([x2 10])
  (let ([y3 0])
    (+ (+ (begin
            (set! y3 (read))
            x2)
          (begin
            (set! x2 (read))
            y3))
       x2)))
