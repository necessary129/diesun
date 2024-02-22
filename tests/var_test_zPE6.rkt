(let ([x (read)])
  (let ([y x])
    (let ([z (+ y (read))])
      (+ 10 (+ 20 (+ 30 (- (+ 12 (read)))))))))
