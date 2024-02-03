#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require racket/set)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))


(define (uniquify-exp env)    ;; TODO: this function currently does nothing. Your code goes here
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body) (let* ([newvar (gensym x)]
                             [newexp ((uniquify-exp env) e)]
                             [newenv (dict-set env x newvar)]
                             [newbody ((uniquify-exp newenv) body)])
                        (Let newvar newexp newbody))]
      [(Prim op es) (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [_ e])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (accumulate_aexps es)
  (foldr
   (lambda (e flist)
     (match-let ([(list oldes oldbinds) flist])
       (let-values
           ([(newe newbinds) (rco_atom e)])
         (list (cons newe oldes) (append newbinds oldbinds)))))
   '(() ())
   es)
  )
  
(define (rco_atom e)
  (match e
    [(Var _) (values e '())]
    [(Int _) (values e '())]
    [(Let x e body) (let ([tmpvar (gensym 'tmp)]
                          [newe (rco_exp e)]
                          [newbody (rco_exp body)])
                      (values (Var tmpvar) `((,tmpvar . ,(Let x newe newbody)))))]
    [(Prim op es) (match-let ([(list aexps binds) (accumulate_aexps es)])
                    (let ([tmpvar (gensym 'tmp)])
                      (values (Var tmpvar) `((,tmpvar . ,(Prim op aexps)) ,@binds))))]))

(define (makeMultiLet binds body)
  (foldl (lambda (bind body)
           (Let (car bind) (cdr bind) body)) body binds))

(define (rco_exp e)
  (match e
    [(Let x e body) (let* ([newexp (rco_exp e)]
                           [newbody (rco_exp body)])
                      (Let x newexp newbody))]
    [(Prim op es) (match-let ([(list aexps binds) (accumulate_aexps es)])
                    (makeMultiLet binds (Prim op aexps)))]
    [_ e]))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco_exp e))]))


(define (pe_add r1 r2)
  (match* (r1 r2)
    [((Int 0) _) r2]
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [((Int n1) (Prim '- (list (Int n2)))) (Int (fx- n1 n2))]
    [((Int n1) (Prim (? (or/c '+ '-) op) (list  (Int n2) e)))
     (pe_exp (Prim '+ (list (Int ((if (eq? op '+) fx+ fx-) n1 n2)) e)))]
    [(_ (Int _)) (pe_add r2 r1)]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe_sub r1 r2)
  (pe_add r1 (pe_neg r2)))

(define (pe_neg r1)
  (match r1
    [(Int n) (Int (fx- 0 n))]
    [(Prim '+ (list e1 e2)) (pe_add (pe_neg e1) (pe_neg e2))]
    [(Prim '- (list e1 e2)) (pe_add (pe_neg e1) e2)]
    [(Prim '- (list e)) e]
    ;; [(Prim (? (or/c '+ '-) op) (list (Int n1) e)) (Prim op (list (Int ((if (eq? op '+) fx- fx+) 0 n1)) (Prim (if (eq? op '+) '+ '-) (list (pe_exp e)))))]
    [_ (Prim '- (list r1))]))

(define (pe_exp e)
  (match e
    [(Prim '+ (list e1 e2)) (pe_add (pe_exp e1) (pe_exp e2))]
    [(Prim '- (list e1 e2)) (pe_sub (pe_exp e1) (pe_exp e2))]
    [(Prim '- (list e1)) (pe_neg (pe_exp e1))]
    [(Let x e body) (Let x (pe_exp e) (pe_exp body))]
    [_ e]))

(define (partial-eval p)
  (match p
    [(Program info e) (Program info (pe_exp e))]))

;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (error "TODO: code goes here (explicate-control)"))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (error "TODO: code goes here (select-instructions)"))

;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ;; Uncomment the following passes as you finish them.
    ("Partial eval" ,partial-eval ,interp-Lvar ,type-check-Lvar)
    ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ;; ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ;; ("instruction selection" ,select-instructions ,interp-x86-0)
    ;; ("assign homes" ,assign-homes ,interp-x86-0)
    ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
    ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
    ))
