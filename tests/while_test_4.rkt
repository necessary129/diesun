(if 
  (>= (let ([x 0])
        (let ([sum 0])
          (begin 
            (while (or (eq? x 0) (or (eq? x 1) (eq? x 2)))
                   (begin
                     (set! sum (+ sum x))
                     (set! x (read))))
            sum)))
      8)
  (begin
    (while (eq? 1 0)
           (let ([x 0])
             (begin
               (while (eq? x 0)
                      (begin
                        (set! x 0)
                        (set! x 1)
                        (set! x 2)
                        (set! x 0)))
               x)))
    3)
  (if (or (<= 1 2) (>= 1 3)) 1 2)
  )
