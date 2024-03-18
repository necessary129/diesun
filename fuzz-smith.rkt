#lang clotho
(require xsmith
         xsmith/app
         racr
         racket/pretty
         racket/string
         racket/port
         racket/fixnum)
(require-clotho-wrapped math)
(define-spec-component arith)

(add-to-grammar
 arith
 [Definition #f (name type Expression)
             #:prop binder-info ()]
 [Expression #f ()
             #:prop may-be-generated #f]
 [LetStar Expression ([definitions : Definition *]

                      Expression)
          #:prop strict-child-order? #t]
 [VariableReference Expression (name)
                    #:prop reference-info (read)]
 ;; [SetBangRet Expression (name Expression)
 ;;             #:prop reference-info (write)]
 [LiteralInt Expression ([v = (random-bits 40)])]
 [Addition Expression ([es : Expression * = 2])
           #:prop choice-weight 25]
 [Subtraction Expression ([es : Expression * = 2])
              #:prop choice-weight 25]
 [PrimRead Expression ()]
 [LiteralBool Expression ([v = (random-bool)])]
 [Comparison Expression () #:prop may-be-generated #f]
 [EqComparison Comparison ([l : Expression] [r : Expression])]
 [LteComparison Comparison ([l : Expression] [r : Expression])]
 [LtComparison Comparison ([l : Expression] [r : Expression])]
 [GteComparison Comparison ([l : Expression] [r : Expression])]
 [GtComparison Comparison ([l : Expression] [r : Expression])]
 [OpAnd Expression ([l : Expression] [r : Expression])]
 [OpOr Expression ([l : Expression] [r : Expression])]
 [OpNot Expression ([e : Expression])]
 [IfStmt Expression ([cond : Expression] [then : Expression] [else : Expression])]
 )


(define int (base-type 'int))
(define bool (base-type 'bool))

(add-property
 arith
 type-info
 [Definition [(fresh-type-variable) (λ (n t) (hash 'Expression t))]]
 [LetStar [(fresh-type-variable)
           (λ (n t) (hash 'definitions (λ (cn) (fresh-type-variable))
                          'sideEs (λ (cn) (fresh-type-variable))
                          'Expression t))]]
 [LiteralInt [int (λ (n t) (hash))]]
 [PrimRead [int (λ (n t) (hash))]]
 [VariableReference [(fresh-type-variable) (λ (n t) (hash))]]
 ;; [SetBangRet [(fresh-type-variable) (λ (n t) (hash 'Expression t))]]
 [Addition [int (λ (n t) (hash 'es t))]]
 [EqComparison [bool (lambda (n t)
                       (define arg-type (fresh-type-variable))
                       (hash 'l arg-type
                             'r (λ (r-node) arg-type)))]]
 [LteComparison [bool (lambda (n t)
                        (hash 'l int
                              'r int))]]
[LtComparison [bool (lambda (n t)
                        (hash 'l int
                              'r int))]]
 [GtComparison [bool (lambda (n t)
                       (hash 'l int
                             'r int))]]
 [GteComparison [bool (lambda (n t)
                        (hash 'l int
                              'r int))]]
 [OpAnd [bool (lambda (n t)
                (hash 'l bool
                      'r bool))]]
 [OpOr [bool (lambda (n t)
               (hash 'l bool
                     'r bool))]]
 [OpNot [bool (lambda (n t)
                (hash 'e bool))]]
 [IfStmt [(fresh-type-variable) (lambda (n t)
                                  (hash 'cond bool
                                        'then t
                                        'else t))]]
 [LiteralBool [bool (lambda (n t) (hash))]]


 [Subtraction [int (λ (n t) (hash 'es t))]])

(add-property
 arith
 render-node-info
 ;; Note that we've imported xsmith/app, so our #%app allows quoted
 ;; symbols to be used in function position as a shorthand for
 ;; using `att-value`.
 ;; [LetStar
 ;;  (λ (n)
 ;;    `(let* (,@(map (λ (d)
 ;;                     `[,(string->symbol (ast-child 'name d))
 ;;                       ,($xsmith_render-node
 ;;                         (ast-child 'Expression d))])
 ;;                   (ast-children (ast-child 'definitions n))))
 ;;       ,@(map (λ (c) ($xsmith_render-node c))
 ;;              (ast-children (ast-child 'sideEs n)))
 ;;       ,($xsmith_render-node (ast-child 'Expression n))))]
 [LetStar (lambda (n)
            (foldr (lambda (d res)
                     `(let ([,(string->symbol (ast-child 'name d))
                             ,($xsmith_render-node (ast-child 'Expression d))])
                        ,res)) `(
                                 ,@($xsmith_render-node (ast-child 'Expression n)))
                               (ast-children (ast-child 'definitions n))))]
 [LiteralInt (λ (n) (ast-child 'v n))]
 [VariableReference (λ (n) (string->symbol (ast-child 'name n)))]
 ;; [SetBangRet (λ (n) `(begin (set! ,(string->symbol (ast-child 'name n))
 ;;                                  ,($xsmith_render-node
 ;;                                    (ast-child 'Expression n)))
 ;;                            ,(string->symbol (ast-child 'name n))))]
 [Addition (λ (n) `(+ ,@(map (λ (c) ($xsmith_render-node c))
                             (ast-children (ast-child 'es n)))))]
 [Subtraction (λ (n) `(- ,@(map (λ (c) ($xsmith_render-node c))
                                (ast-children (ast-child 'es n)))))]
 [PrimRead (lambda (n) `(read))]
 [LiteralBool (lambda (n) (ast-child 'v n))]
 [EqComparison (lambda (n) `(eq? ,($xsmith_render-node (ast-child 'l n))
                                 ,($xsmith_render-node (ast-child 'r n))))]
 [LteComparison (lambda (n) `(<= ,($xsmith_render-node (ast-child 'l n))
                                 ,($xsmith_render-node (ast-child 'r n))))]
 [LtComparison (lambda (n) `(< ,($xsmith_render-node (ast-child 'l n))
                                 ,($xsmith_render-node (ast-child 'r n))))]
 [GteComparison (lambda (n) `(>= ,($xsmith_render-node (ast-child 'l n))
                                 ,($xsmith_render-node (ast-child 'r n))))]
 [GtComparison (lambda (n) `(> ,($xsmith_render-node (ast-child 'l n))
                                 ,($xsmith_render-node (ast-child 'r n))))]
 [OpAnd (lambda (n) `(and ,($xsmith_render-node (ast-child 'l n))
                                 ,($xsmith_render-node (ast-child 'r n))))]
 [OpOr (lambda (n) `(or ,($xsmith_render-node (ast-child 'l n))
                                 ,($xsmith_render-node (ast-child 'r n))))]
 [OpNot (lambda (n) `(not ,($xsmith_render-node (ast-child 'e n))))]
 [IfStmt (lambda (n) `(if ,($xsmith_render-node (ast-child 'cond n))
                          ,($xsmith_render-node (ast-child 'then n))
                          ,($xsmith_render-node (ast-child 'else n))))])



;; This line defines `arith-command-line`.
(define-xsmith-interface-functions
  [arith]
  #:program-node LetStar
  #:type-thunks (list (λ () int) (lambda () bool))
  #:comment-wrap (λ (lines)
                   (string-join
                    (map (λ (x) (format ";; ~a" x)) lines)
                    "\n"))
  #:format-render (λ (ast)
                    (with-output-to-string
                      (λ ()
                        (pretty-print ast (current-output-port) 1)))))

(module+ main (arith-command-line))
