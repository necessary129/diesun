(let ([x (read)])
  (+ x (+ x (let ([y (read)])
              (+ x (- y (let ([z (read)])
                          (+ z (- (read) (- (read)))))))))))
