
#lang racket
(require racket/set)
(require racket/fixnum)
(require racket/set)
(require racket/promise)
(require graph)
(require data/queue)
(require "interp.rkt")
(require "interp-Cvec.rkt")
(require "interp-Lvec.rkt")
(require "interp-Lvec-prime.rkt")
(require "type-check-Lvec.rkt")
(require "type-check-Cvec.rkt")
(require "type-check-Lvecof.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(require "runtime-config.rkt")

(provide (all-defined-out))
(define (uniquify-exp env)
  (lambda (e)
    (define recur (uniquify-exp env))
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool _) e]
      [(If c t e) (If (recur c) (recur t) (recur e))]
      [(SetBang var exp) (SetBang (dict-ref env var) (recur exp))]
      [(Begin exp* exp) (Begin (for/list ([ex exp*]) (recur ex)) (recur exp))]
      [(WhileLoop con body) (WhileLoop (recur con) (recur body))]
      [(Let x e body)
       (let* ([newvar (gensym x)]
              [newexp (recur e)]
              [newenv (dict-set env x newvar)]
              [newbody ((uniquify-exp newenv) body)])
         (Let newvar newexp newbody))]
      [(Prim op es)
       (Prim op
             (for/list ([e es])
               (recur e)))]
      [_ e])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (collect-set! e)
  (match e
    [(Var _) (set)]
    [(Int _) (set)]
    [(Let _ rhs body) (set-union (collect-set! rhs) (collect-set! body))]
    [(SetBang var rhs) (set-union (set var) (collect-set! rhs))]
    [(Bool _) (set)]
    [(If c t e) (set-union (collect-set! c) (collect-set! t) (collect-set! e))]
    [(Begin exp* exp) (set-union (foldl (lambda (firEl collEl) (set-union (collect-set! firEl) collEl)) (set) exp*) (collect-set! exp))]
    [(WhileLoop con body) (set-union (collect-set! con) (collect-set! body))]
    [(Prim op es) (foldl (lambda (firEl collEl) (set-union (collect-set! firEl) collEl)) (set) es)]
    [_ (set)]))

(define ((uncover-get!-exp set!-vars) e)
  (define recur (uncover-get!-exp set!-vars))
  (match e
    [(Var x) (if (set-member? set!-vars x)
                 (GetBang x)
                 (Var x))]
    [(Let x rhs body) (Let x (recur rhs) (recur body))]
    [(Int _) e]
    [(Bool _) e]
    [(Void) e]
    [(SetBang var rhs) (SetBang var (recur rhs))]
    [(If c t e) (If (recur c) (recur t) (recur e))]
    [(Begin e* e) (Begin (for/list ([e e*]) (recur e)) (recur e))]
    [(WhileLoop con body) (WhileLoop (recur con) (recur body))]
    [(Prim op es) (Prim op (for/list ([e es]) (recur e)))]))

(define (uncover-get! p)
  (match p
    [(Program info body) (let ([set!-vars (collect-set! body)])
                           (Program info ((uncover-get!-exp set!-vars) body)))]))

(define (expose_allocation-hastype es type)
  (let ([binds (reverse (map (lambda (e) (cons (gensym 'vx) e)) es))]
        [len (length es)]
        [vecname (gensym 'alloc)])
    (define sz (8n+1 len))
    (makeMultiLet binds (Begin (list (If (Prim '< (list
                                                   (Prim '+ (list
                                                             (GlobalValue 'free_ptr)
                                                             (Int sz)))
                                                   (GlobalValue 'fromspace_end)))
                                         (Void)
                                         (Collect sz)))
                               (Let vecname (Allocate len type)
                                    (Begin (for/list ([i (in-naturals)]
                                                      [b binds])
                                             (Prim 'vector-set! (list (Var vecname) (Int i) (Var (car b)))))
                                           (Var vecname)))))))
(define (8n+1 b)
  (* 8 (add1 b)))

(define (expose_allocation-exp e)
  (match e
    [(Let x rhs body) (Let x (expose_allocation-exp rhs) (expose_allocation-exp body))]
    [(SetBang var rhs) (SetBang var (expose_allocation-exp rhs))]
    [(If c t e) (If (expose_allocation-exp c) (expose_allocation-exp t) (expose_allocation-exp e))]
    [(Begin e* e) (Begin (for/list ([e e*]) (expose_allocation-exp e)) (expose_allocation-exp e))]
    [(WhileLoop con body) (WhileLoop (expose_allocation-exp con) (expose_allocation-exp body))]
    [(Prim op es) (Prim op (for/list ([e es]) (expose_allocation-exp e)))]
    [(HasType (Prim 'vector es) type) (let ([newes (map expose_allocation-exp es)])
                                        (expose_allocation-hastype newes type))]
    [_ ;; (printf "~a~n" e)
     e]))

(define (expose_allocation p)
  (match p
    [(Program info body) (Program info (expose_allocation-exp body))]))

(define (accumulate_aexps es)
  (foldr (lambda (e flist)
           (match-let ([(list oldes oldbinds) flist])
             (let-values ([(newe newbinds) (rco_atom e)])
               (list (cons newe oldes) (append oldbinds newbinds)))))
         '(() ())
         es))

(define (maketmp e)
  (let ([tmpvar (gensym 'tmp)])
    (values (Var tmpvar) `((,tmpvar . ,e)))))

(define (rco_atom e)
  (match e
    [(Var _) (values e '())]
    [(Void) (values e '())]
    [(Int i) #:when(> (abs i) 2147483647) (let ([tmpvar (gensym 'tmp)])
                                            (values (Var tmpvar) `((,tmpvar . ,(Int i)))))]
    [(Int _) (values e '())]
    [(Bool _) (values e '())]
    [(Collect _) (maketmp e)]
    [(Allocate _ _) (maketmp e)]
    [(GlobalValue _) (maketmp e)]
    [(If c t e) (let ([tmpvar (gensym 'tmp)])
                  (values (Var tmpvar) `((,tmpvar . ,(If (rco_exp c) (rco_exp t) (rco_exp e))))))]
    [(Let x e body)
     (let ([tmpvar (gensym 'tmp)] [newe (rco_exp e)] [newbody (rco_exp body)])
       (values (Var tmpvar) `((,tmpvar . ,(Let x newe newbody)))))]
    [(Prim op es)
     (match-let ([(list aexps binds) (accumulate_aexps es)])
       (let ([tmpvar (gensym 'tmp)])
         (values (Var tmpvar) `((,tmpvar . ,(Prim op aexps)) ,@binds))))]
    [(WhileLoop con body) (let ([tmpvar (gensym 'tmp)])
                            (values (Var tmpvar) `((,tmpvar . ,(WhileLoop (rco_exp con) (rco_exp body))))))]
    [(GetBang var) (let ([tmpvar (gensym 'tmp)])
                     (values (Var tmpvar) `((,tmpvar . ,(Var var)))))]
    [(Begin e* e) (let ([tmpvar (gensym 'tmp)])
                    (values (Var tmpvar) `((,tmpvar . ,(Begin (map rco_exp e*) (rco_exp e))))))]
    [(SetBang var rhs) (let ([tmpvar (gensym 'tmp)])
                         (values (Var tmpvar) `((,tmpvar . ,(SetBang var (rco_exp rhs))))))]))

(define (makeMultiLet binds body)
  (foldl (lambda (bind body) (Let (car bind) (cdr bind) body)) body binds))

(define (rco_exp e)
  (match e
    [(Let x e body) (let* ([newexp (rco_exp e)] [newbody (rco_exp body)]) (Let x newexp newbody))]
    [(Prim op es)
     (match-let ([(list aexps binds) (accumulate_aexps es)])
       (makeMultiLet binds (Prim op aexps)))]
    [(If c t e) (If (rco_exp c) (rco_exp t) (rco_exp e))]
    [(WhileLoop con body) (WhileLoop (rco_exp con) (rco_exp body))]
    [(SetBang var rhs) (SetBang var (rco_exp rhs))]
    [(GetBang var) (Var var)]
    [(Collect _) e]
    [(Allocate _ _) e]
    [(GlobalValue _) e]
    [(Begin e* e) (Begin (map rco_exp e*) (rco_exp e))]
    [_ e]))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco_exp e))]))

(define (explicate_effect e cont)
  (lazy
   (match e
     [(Prim 'vector-set! _) (Seq e (force cont))]
     [(Collect _) (Seq e (force cont))]
     [(If c t e) (let ([contblock (create_block cont)])
                   (explicate_pred c (explicate_effect t contblock) (explicate_effect e contblock)))]
     [(SetBang v rhs) (explicate_assign rhs v cont)]
     [(Prim 'read _) (Seq e (force cont))]
     [(WhileLoop cnd body) (let* ([label (gensym 'loop)]
                                  [newbody (force (explicate_effect body (Goto label)))]
                                  [newblock (force (explicate_pred cnd newbody cont))])
                             (get-basic-blocks (cons (cons label newblock) (get-basic-blocks)))
                             (Goto label))]
     [(Begin es body) (for/fold ([cont (force (explicate_effect body cont))])
                                ([e es])
                        (force (explicate_effect e cont)))]
     [_ cont])))

(define (explicate_tail e)
  (lazy
   (match e
     [(Var x) (Return (Var x))]
     [(Int n) (Return (Int n))]
     [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
     [(Prim op es) (Return (Prim op es))]
     [(Bool b) (Return (Bool b))]
     [(Void) (Return (Void))]
     [(Begin es body) (for/fold ([cont (force (explicate_tail body))])
                                ([e es])
                        (force (explicate_effect e cont)))]
     [(SetBang _ _) (explicate_effect e (explicate_tail (Void)))]
     [(WhileLoop _ _) (explicate_effect e (explicate_tail (Void)))]
     [(If cnd thn els) (explicate_pred cnd (explicate_tail thn) (explicate_tail els))]
     [_ (error "explicate_tail unhandled case" e)])))

(define (explicate_assign e x cont)
  (lazy
    (match e
      [(Collect _) (Seq (Assign (Var x) e) (force cont))]
      [(Var y) (Seq (Assign (Var x) (Var y)) (force cont))]
      [(Allocate _ _) (Seq (Assign (Var x) e) (force cont))]
      [(GlobalValue _) (Seq (Assign (Var x) e) (force cont))]
      [(Int n) (Seq (Assign (Var x) (Int n)) (force cont))]
      [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
      [(Prim op es) (Seq (Assign (Var x) (Prim op es)) (force cont))]
      [(Bool b) (Seq (Assign (Var x) (Bool b)) (force cont))]
      [(If cnd thn els) (explicate_pred cnd (explicate_assign thn x cont) (explicate_assign els x cont))]
      [(Void) (Seq (Assign (Var x) (Void)) (force cont))]
      [(SetBang _ _) (explicate_effect e (explicate_assign (Void) x cont))]
      [(WhileLoop _ _) (explicate_effect e (explicate_assign (Void) x cont))]
      [(Begin es body) (for/fold ([cont (force (explicate_assign body x cont))])
                                 ([e es])
                         (force (explicate_effect e cont)))]
      [_ (error "explicate_assign unhandled case" e)])))

(define (create_block tail)
  (lazy
    (define t (force tail))
    (match t
      [(Goto label) (Goto label)]
      [else
       (let ([label (gensym 'block)])
         (get-basic-blocks (cons (cons label t) (get-basic-blocks)))
         (Goto label))])))

(define (explicate_pred cnd thn els)
  (lazy
    (let ([thnblock (create_block thn)] [elsblock (create_block els)])
      (match cnd
        [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (force thnblock) (force elsblock))]
        [(Let x rhs body) (explicate_assign rhs x (explicate_pred body thnblock elsblock))]
        [(Prim 'not (list e)) (explicate_pred e elsblock thnblock)]
        [(Prim (? (or/c 'eq? '< '> '<= '>=) op) es) (IfStmt (Prim op es) (force thnblock) (force elsblock))]
        [(Bool b) (if b thnblock elsblock)]
        [(If ncnd nthn nels) (explicate_pred ncnd
                                             (explicate_pred nthn thnblock elsblock)
                                             (explicate_pred nels thnblock elsblock))]
        [(Begin es body) (for/fold ([cont (force (explicate_pred body thnblock elsblock))])
                                ([e es])
                        (force (explicate_effect e cont)))]
        [else (error "explicate_pred unhandled case " cnd)]))))

(define (explicate-control p)
  (parameterize ([get-basic-blocks '()])
    (match p
      [(Program info body) (let ([startblock (force (explicate_tail body))])
                             (get-basic-blocks (cons `(start . ,startblock) (get-basic-blocks)))
                             (CProgram info (get-basic-blocks)))])))

(define (shrink p)
  (match p
    [(Program info e) (Program info (shrink-exp e))]))

(define (shrink-exp p)
  (match p
    [(Prim 'and (list t1 t2)) (If (shrink-exp t1) (shrink-exp t2) (Bool #f))]
    [(Prim 'or (list t1 t2)) (If (shrink-exp t1) (Bool #t) (shrink-exp t2))]
    [(Var _) p]
    [(Int _) p]
    [(Bool _) p]
    [(Void) p]
    [(Let y rhs body) (Let y (shrink-exp rhs) (shrink-exp body))]
    [(Prim op es) (Prim op (map shrink-exp es))]
    [(If c t e) (If (shrink-exp c) (shrink-exp t) (shrink-exp e))]
    [(Begin e* e) (Begin (for/list ([e e*]) (shrink-exp e)) (shrink-exp e))]
    [(WhileLoop cnd body) (WhileLoop (shrink-exp cnd) (shrink-exp body))]
    [(SetBang var rhs) (SetBang var (shrink-exp rhs))]
    [_ (error "shrink-exp unhandled case" p)]
    )
)

(define (pe_add env)
  (lambda (r1 r2)
    (match* (r1 r2)
      [((Int 0) _) r2]
      [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
      [((Int n1) (Prim '- (list (Int n2)))) (Int (fx- n1 n2))]
      [((Int n1) (Prim (? (or/c '+ '-) op) (list (Int n2) e)))
       ((pe_exp env) (Prim '+ (list (Int ((if (eq? op '+) fx+ fx-) n1 n2)) e)))]
      [(_ (Int _)) ((pe_add env) r2 r1)]
      [(_ _) (Prim '+ (list r1 r2))])))

(define (pe_sub env)
  (lambda (r1 r2) ((pe_add env) r1 ((pe_neg env) r2))))

(define (pe_neg env)
  (lambda (r1)
    (match r1
      [(Int n) (Int (fx- 0 n))]
      [(Prim '+ (list e1 e2)) ((pe_add env) ((pe_neg env) e1) ((pe_neg env) e2))]
      [(Prim '- (list e1 e2)) ((pe_add env) ((pe_neg env) e1) e2)]
      [(Prim '- (list e)) e]

      ;; [(Prim (? (or/c '+ '-) op) (list (Int n1) e)) (Prim op (list (Int ((if (eq? op '+) fx- fx+) 0 n1)) (Prim (if (eq? op '+) '+ '-) (list (pe_exp e)))))]
      [_ (Prim '- (list r1))])))

(define (pe_pred env)
  (lambda (cnd thn els)
    (match cnd
      [(Bool #t) thn]
      [(Bool #f) els]
      [_ (If cnd thn els)])))

(define (pe_cmp->f cmp)
  (match cmp
    ['eq? eq?]
    ['> >]
    ['>= >=]
    ['< <]
    ['<= <=]))

(define (pe_cmp env)
  (lambda (cmp e1 e2)
    (match* (cmp e1 e2)
      [('eq? (Bool b1) (Bool b2)) (Bool (eq? b1 b2))]
      [(_ (Int n1) (Int n2)) (Bool ((pe_cmp->f cmp) n1 n2))]
      [(_ _ _) (Prim cmp (list e1 e2))])))

(define (pe_not env)
  (lambda (e)
    (match e
      [(Bool b) (Bool (not b))]
      [_ (Prim 'not (list e))])))

(define (pe_exp env)
  (lambda (e)
    (match e
      [(Var x) (dict-ref env x e)]
      [(Prim '+ (list e1 e2)) ((pe_add env) ((pe_exp env) e1) ((pe_exp env) e2))]
      [(Prim '- (list e1 e2)) ((pe_sub env) ((pe_exp env) e1) ((pe_exp env) e2))]
      [(Prim '- (list e1)) ((pe_neg env) ((pe_exp env) e1))]
      [(Prim 'not (list e)) ((pe_not env) ((pe_exp env) e))]
      [(Prim (? (or/c 'eq? '< '> '<= '>=) cmp) (list e1 e2))
       ((pe_cmp env) cmp ((pe_exp env) e1) ((pe_exp env) e2))]
      [(Let x e body)
       (let ([rhs ((pe_exp env) e)])
         (if (atm? rhs) ((pe_exp (dict-set env x rhs)) body) (Let x rhs ((pe_exp env) body))))]
      [(If cnd thn els) ((pe_pred env) ((pe_exp env) cnd) ((pe_exp env) thn) ((pe_exp env) els))]
      [_ e])))

(define (partial-eval p)
  (match p
    [(Program info e) (Program info ((pe_exp '()) e))]))

;; explicate-control : Lvar^mon -> Cvar

(define (get-op-name p)
  (match p
    [(Prim '+ (list e1 e2)) 'addq]
    [(Prim '- (list e1 e2)) 'subq]
    [(Prim '- (list e1)) 'negq]
    [(Prim 'not (list e1)) 'xorq]
    ; read
    ))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (match p
    [(CProgram info body)
     (X86Program info
                 (for/list ([block body])
                   (cons (car block) (Block '() (select-inst-tail (cdr block))))))]))

(define (select-inst-atom p)
  (match p
    [(Int n) (Imm n)]
    [(Var v) (Var v)]
    [(Void) (Imm 0)]
    [(GlobalValue n) (Global n)]
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]))

(define (get-set-flag cmp)
  (match cmp
    ['eq? 'sete]
    ['< 'setl]
    ['<= 'setle]
    ['> 'setg]
    ['>= 'setge]
  )
)

(define (compute_mask types [mask 0])
  (match types
    [(list (list 'Vector more ...) res ...) (compute_mask res (bitwise-ior 1 (arithmetic-shift mask 1)))]
    [(cons _ res) (compute_mask res (arithmetic-shift mask 1))]
    ['() mask]))

(define (vec->tag type)
  (bitwise-ior (arithmetic-shift (compute_mask (cdr type)) 7) ;; pointer mask
               (arithmetic-shift (length (cdr type)) 1) ;; length tag
               1                                        ;; forwarding pointer
               ))

(define (select-inst-assgn v e)
  (match e
    [(? atm? e) (list (Instr 'movq (list (select-inst-atom e) v)))]
    [(Prim 'read '()) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) v)))]
    [(GlobalValue n) (list
                      (Instr 'movq (list (Global n) v)))]
    [(Allocate n type) (list
                        (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
                        (Instr 'addq (list (Imm (8n+1 n)) (Global 'free_ptr)))
                        (Instr 'movq (list (Imm (vec->tag type)) (Deref 'r11 0)))
                        (Instr 'movq (list (Reg 'r11) v)))]
    [(Prim 'vector-ref (list tup (Int n))) (list
                                            (Instr 'movq (list (select-inst-atom tup) (Reg 'r11)))
                                            (Instr 'movq (list (Deref 'r11 (8n+1 n)) v)))]
    [(Prim 'vector-set! _) (append (select-inst-stmt e) (list (Instr 'movq (list (Imm 0) v))))]
    [(Prim (? (or/c 'eq? '< '> '<= '>=) cmp) (list e1 e2))
     (list (Instr 'cmpq (list (select-inst-atom e2) (select-inst-atom e1)))
           (Instr 'set (list (get-flag-name cmp) (ByteReg 'al)))
           (Instr 'movzbq (list (ByteReg 'al) v)))]
    [(Prim op (list e1 e2))
     (list (Instr 'movq (list (select-inst-atom e1) v))
           (Instr (get-op-name e) (list (select-inst-atom e2) v)))]
    [(Prim 'not (list e1))
     (list (Instr 'movq (list (select-inst-atom e1) v))
           (Instr 'xorq (list (Imm 1) v)))]
    [(Prim op (list e1))
     (list (Instr 'movq (list (select-inst-atom e1) v))
           (Instr (get-op-name e) (list v)))]))

(define (select-inst-stmt s)
  (match s
    [(Assign (Var v) (Prim '+ (list a1 (Var v2))))
     #:when (equal? v v2)
     (list (Instr 'addq (list (select-inst-atom a1) (Var v))))]
    [(Assign (Var v) (Prim '+ (list (Var v1) a2)))
     #:when (equal? v v1)
     (list (Instr 'addq (list (select-inst-atom a2) (Var v))))]
    [(Assign (Var v) (Prim 'not (list (Var v1))))
     #:when (equal? v v1)
     (list (Instr 'xorq (list (Int 1) (Var v1))))]
    [(Assign v e) (select-inst-assgn v e)]
    [(Prim 'read _) (list (Callq 'read_int 0))]
    [(Prim 'vector-set! (list v (Int n) d)) (list
                                             (Instr 'movq (list (select-inst-atom v) (Reg 'r11)))
                                             (Instr 'movq (list (select-inst-atom d) (Deref 'r11 (8n+1 n)))))]
    [(Collect n) (list
                  (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
                  (Instr 'movq (list (Imm n) (Reg 'rsi)))
                  (Callq 'collect 2))]))

(define (select-inst-tail tail)
  (match tail
    [(Return e) (append (select-inst-assgn (Reg 'rax) e) (list (Jmp 'conclusion)))]
    [(Seq s t) (append (select-inst-stmt s) (select-inst-tail t))]
    [(Goto l) (list (Jmp l))]
    [(IfStmt (Prim cmp (list arg1 arg2)) (Goto l1) (Goto l2)) 
     (list 
     (Instr 'cmpq (list (select-inst-atom arg2) (select-inst-atom arg1)))
     (JmpIf (get-flag-name cmp) l1)
     (Jmp l2))]
    ))

(define (get-flag-name cmp)
  (match cmp
    ['eq? 'e]
    ['< 'l]
    ['<= 'le]
    ['> 'g]
    ['>= 'ge]
))

(define arg-regs '(rdi rsi rdx rcx r8 r9))
(define second-read-instr (set 'addq 'subq 'cmpq))

(define (second-read? op) (set-member? second-read-instr op))

(define is-loc? (or/c Var Reg))

(define (uncover_read_secondread instr)
  (match instr
    [(Instr (? second-read? op) (list _ (Var v))) (set v)]
    [(Instr (? second-read? op) (list _ (Reg v))) (set v)]
    [_ (set)]))

(define (uncover_read instr lbl->live)
  (let ([sset (uncover_read_secondread instr)])
    (match instr
      [(Instr _ (cons (Var v) _)) (set-add sset v)]
      [(Instr _ (cons (Reg v) _)) (set-add sset v)]
      [(Callq _ arity) (list->set (take arg-regs arity))]
      [(Jmp label) lbl->live]
      [(JmpIf _ label) lbl->live]
      [_ sset])))

(define (uncover_write instr)
  (match instr
    [(Instr 'cmpq _) (set)]
    [(Instr 'set (list _ (ByteReg b))) (set (byte-reg->full-reg b))]
    [(Instr _ (list _ (Var v))) (set v)]
    [(Instr _ (list _ (Reg v))) (set v)]
    [(Instr _ (list (Var v))) (set v)]
    [(Instr _ (list (Reg v))) (set v)]
    [(Callq _ _) caller-save]
    [_ (set)]))

(define (get_live code ini lbl->live)
  (foldr (lambda (instr lset)
           (cons
            (set-union (set-subtract (car lset) (uncover_write instr)) (uncover_read instr lbl->live))
            lset))
         (list ini) code))

(define (uncover_block b lbl->live [ini (set)])
  (match b
    [(Block info code) (let ([livesets (get_live code ini lbl->live)])
                         (Block (dict-set* info 'lbefore (car livesets) 'lafter (cdr livesets)) code))]))


(define (transfer label lafter)
  (if (eq? label 'conclusion)
      (set 'rax 'rsp)
      (match (dict-ref (get-basic-blocks) label)
        [(Block info code)
         (let ([livesets (get_live code lafter lafter)])
           (get-basic-blocks (dict-set (get-basic-blocks) label (Block (dict-set* info 'lbefore (car livesets) 'lafter (cdr livesets)) code)))
           (car livesets))])))

(define (analyze_dataflow G transfer bottom join)
  (define mapping (make-hash))
  (for ([v (in-vertices G)])
    (dict-set! mapping v bottom))
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
    (define node (dequeue! worklist))
    (define input (for/fold ([state bottom])
                            ([pred (in-neighbors trans-G node)])
                    (join state (dict-ref mapping pred))))
    (define output (transfer node input))
    (cond [(not (equal? output (dict-ref mapping node)))
           (dict-set! mapping node output)
           (for ([v (in-neighbors G node)])
             (enqueue! worklist v))]))
  mapping)

(define (uncover_live p)
  (match p
    [(X86Program info blocks)
     (parameterize ([get-basic-blocks blocks])
       (let ([cfg (build_cfg blocks)])
         (analyze_dataflow (transpose cfg) transfer (set) set-union)
         (X86Program info (get-basic-blocks))))]))

;; (define (uncover_live p)
;;   (match p
;;     [(X86Program info blocks)
;;      (let* ([cfg (build_cfg blocks)]
;;             ;; [vert-list (tsort (transpose cfg))]
;;             ;; [label->live (dict-set '() 'conclusion (set 'rax 'rsp))]
;;             )
;;        ;; (printf "cfg: ~a vert: ~a~n" cfg vert-list)
;;        ;; (print-graph cfg)
;;        (define uncover (lambda (vlist nblocks lbl->live)
;;                          (match vlist
;;                            [`(conclusion . ,rest) (uncover rest nblocks lbl->live)]
;;                            [`(,v . ,rest) (let ([newblock (uncover_block (dict-ref blocks v) lbl->live)])
;;                                             (uncover rest (cons (cons v newblock) nblocks) (dict-set lbl->live v (dict-ref (Block-info newblock) 'lbefore))))]
;;                            ['() (values nblocks lbl->live)])))
;;        ;; (for ([v vert-list])
;;        ;;   (unless (equal? v 'conclusion)
;;        ;;     (let ([newblock (uncover_block (dict-ref blocks v) label->live)])
;;        ;;       (dict-set! label->live v (dict-ref (Block-info newblock) 'lbefore))
;;        ;;       (dict-set! newblocks v newblock))))
;;        ;; (define-values (nblocks lbl-live) (uncover vert-list '() label->live))
;;        (define (transfer label lafter)
;;          label)
;;        (X86Program (dict-set info 'label->live ;; lbl-live
;;                              '()) ;; nblocks
;;                     '()
;;                    ))]))


(define (build_cfg blocks)
  (let* ([get_succ (lambda (code)
                     (foldl (lambda (instr succset)
                              (match instr
                                [(Jmp label) ;; #:when (not (equal? label 'conclusion))
                                 (set-add succset label)
                                 ]
                                [(JmpIf _ label) (set-add succset label)]
                                [_ succset]))
                            (set) code))]
         [get_edge_list (lambda (blockpair)
                          (let ([label (car blockpair)] [block (cdr blockpair)])
                            (for/list ([v (set->list (get_succ (Block-instr* block)))])
                              (list label v))))])
    ;; (printf "gra: ~a~n" (append-map get_edge_list blocks))
    (make-multigraph (append-map get_edge_list blocks))))

(define (get-val loc)
  (match loc
    [(Var v) v]
    [(Reg v) v]
    [(ByteReg b) (byte-reg->full-reg b)]
    [_ #f]))

(define (is-vector ltypes var)
  (match (dict-ref ltypes var (void))
    [(list 'Vector _ ...) #t]
    [_ #f]))

(define (get_edge_instr instr lafter ltypes)
  (define (get_norm)
    (let ([Wset (uncover_write instr)])
      (for*/list ([v lafter] [d (set->list Wset)] #:unless (equal? d v))
        `(,v ,d))))
  (match instr
    [(Instr 'movq (list (app get-val s) (app get-val d))) (for/list ([v lafter] #:unless ((or/c s d) v))
                                `(,v ,d))]
    [(Instr 'movzbq (list (app get-val s) (app get-val d))) (for/list ([v lafter] #:unless ((or/c s d) v))
                                `(,v ,d))]
    [_ (let ([Wset (uncover_write instr)])
         (for*/list ([v lafter] [d (set->list Wset)] #:unless (equal? d v))
           `(,v ,d)))]))

(define (loc-hack code)
  (for/list ([v (set->list (foldr (lambda (ins varset)
									(define s (set-union (uncover_read ins '()) (uncover_write ins) varset))
									;; (printf "ins ~a ~a ~n" ins s)
                                    s) (set) code))])
    `(,v ,v)))

(define (build_interblock code lbefore lafterlist ltypes)
  ;; (define s (append (loc-hack code) (append-map get_edge_instr code lafterlist)))
  ;; (printf "AAA ~a ~a~n" s code)
  ;; (undirected-graph s)
  (append-map (lambda (x y) (get_edge_instr x y ltypes)) code lafterlist))

(define (build_interference_block block ltypes)
  (match block
    [(Block info code) (Block
                        (dict-set info 'conflict-edges (build_interblock code (dict-ref info 'lbefore) (dict-ref info 'lafter) ltypes)) code)]))

(define (build_interference p)
  (match p
    [(X86Program info blocks) (let ([newblocks (for/list ([block blocks]) `(,(car block) . ,(build_interference_block (cdr block) (dict-ref info 'locals-types))))])
                                (X86Program (dict-set info 'conflicts (undirected-graph (append-map (lambda (b)
                                                                                                      (dict-ref (Block-info (cdr b)) 'conflict-edges)) newblocks)))
                                            newblocks))]))

(define (get_mov_related instr)
  (match instr
    [(Instr 'movq (list (app get-val (? (not/c #f) s)) (app get-val (? (not/c #f) d)))) `((,s ,d))]
    [_ '()]))

(define (build_mov_graph_block block)
  (match block
    [(Block info code) (Block (dict-set info 'mov-rel (append-map get_mov_related code)) code)]))

(define (build_mov_graph p)
  (match p
    [(X86Program info blocks) (let ([newblocks (for/list ([block blocks]) `(,(car block) . ,(build_mov_graph_block (cdr block))))])
                                (X86Program (dict-set info 'mov-graph (undirected-graph (append-map (lambda (b)
                                                                                                      (dict-ref (Block-info (cdr b)) 'mov-rel)) newblocks)))
                                            newblocks))]))


(define (assign-home-atm e locs)
  ;; (printf "a-atm: e: ~a~n" e)
  (match e
    [(Reg _) e]
    [(Imm _) e]
    [(ByteReg _) e]
    [(Global _) e]
    [(Deref _ _) e]
    [(Var v) (dict-ref locs v)]))

(define (assign-homes-aexps es locs)
  (foldr (lambda (e l) (cons (assign-home-atm e locs) l)) '() es))

(define (assign-homes-instr e locs)
  (match e
    [(Instr 'set (cons cc args)) (Instr 'set (cons cc (assign-homes-aexps args locs)))]
    [(Instr op es) (Instr op (assign-homes-aexps es locs))]
    [_ e]))

(define (assign-homes-block block locs)
  (match block
    [(Block info es)
     ;; (define-values (stackspace used-callee locs) (get-locs info))
     (Block info ;; (dict-set* info 'stack-space stackspace 'used-callee used-callee)
      (for/list ([e es])
        (assign-homes-instr e locs)))]))



(define (color->loc c callee-len)
  (let* ([nreg (num-registers-for-alloc)])
    (cond
      [(>= c nreg) (Deref 'rbp (* -8 (+ callee-len (- c nreg))))]
      [(<= c -6) (Deref 'r15 (* -8 (add1 (- (+ c 6)))))]
      [else (Reg (color->register c))])))

(define callee-colors (list->set (map register->color (set->list callee-save))))

(define (get-locs info)
  (let* ([colors (dict-ref info 'colors)]
         [ltypes (hash-keys colors)]
         [nreg (num-registers-for-alloc)]
         [nloc (argmax identity (hash-values colors))]
         [nstack (max 0 (- nloc nreg))]
         [nroot (max 0 (- (+ 5 (argmin identity (hash-values colors)))))]
         ;; [used-callee (filter-map (lambda (v) (if (set-member? callee-colors v) (color->register v) #f)) (hash-values colors))]
         [used-callee (list->set (filter (not/c #f) (hash-map colors (lambda (k v)
                                                                       (if (and (set-member? callee-colors v) (not (set-member? registers k)))
                                                                           (color->register v)
                                                                           #f)))))]
         [locs (for/list ([var ltypes])
                 (cons var (color->loc (dict-ref colors var) (set-count used-callee))))]
         )
    ;; (printf "nreg: ~a nloc: ~a nstack: ~a used-callee: ~a locs: ~a~n" nreg nloc nstack used-callee locs)
    (values nroot nstack used-callee locs)))
;; assign-homes : x86var -> x86var
;; (define (assign-homes p)
;;  (match p
;;     [(X86Program info body)
;;      (let-values ([(stackspace locs) (get-locs info)])
;;        (X86Program (dict-set info 'stack-space stackspace)
;;                    (for/list ([block body])
;;                      (cons (car block) (assign-homes-block (cdr block) locs)))))]))

;; (define (assign-homes p)
;;   (match p
;;     [(X86Program info body)
;;      (let* ([newblocks (for/list ([block body])
;;                          (cons (car block) (assign-homes-block (cdr block))))]
;;             [stackspace (foldr (lambda (block stack)
;;                                  (+ (dict-ref (Block-info (cdr block)) 'stack-space) stack)) 0 newblocks)]
;;             [used-callee (foldr (lambda (block callees)
;;                                   (set-union callees (dict-ref (Block-info (cdr block)) 'used-callee))) (set) newblocks)])
;;        (X86Program (dict-set* info 'stack-space stackspace 'used-callee (set->list used-callee)) newblocks))]))

(define (assign-homes p)
  (match p
    [(X86Program info blocks) (let-values ([(nroot nstack used-calle locs) (get-locs info)])
                                (X86Program (dict-set* info 'num-root-spills nroot 'stack-space nstack 'used-callee (set->list used-calle)) (for/list ([b blocks]) (cons (car b) (assign-homes-block (cdr b) locs)))))]))

(define (patch-instr e)
  (match e
    [(Instr 'movq (list v v)) '()]
    [(Instr 'cmpq (list e1 (Imm e2)))
     (list (Instr 'movq (list (Imm e2) (Reg 'rax)))
           (Instr 'cmpq (list e1 (Reg 'rax))))]
    [(Instr 'cmpq (list (Deref r1 o1) (Deref r2 o2)))
     (list (Instr 'movq (list (Deref r2 o2) (Reg 'rax)))
           (Instr 'cmpq (list (Deref r1 o1) (Reg 'rax))))]
    [(Instr 'movzbq (list e1 (Deref r2 o2)))
     (list (Instr 'movzbq (list e1 (Reg 'rax)))
           (Instr 'movq (list (Reg 'rax) (Deref r2 o2))))]
    ;; [(Instr op (list (Imm n1) r)) #:when (and (> (abs n1) 2147483647) (not (equal? op 'movq)))
    ;;                               (assert (format "gt32 op: ~a" e) #f)
    ;;                               (list (Instr 'movq (list (Imm n1) (Reg 'r11))) (Instr op (list (Reg 'r11) r)))]
    [(Instr op (list (Deref r1 o1) (Deref r2 o2)))
     (list (Instr 'movq (list (Deref r1 o1) (Reg 'rax))) (Instr op (list (Reg 'rax) (Deref r2 o2))))]
    [(Instr op (list (Imm n1) (Deref r1 o1))) #:when (> (abs n1) 2147483647)
                                              (list (Instr 'movq (list (Imm n1) (Reg 'rax))) (Instr op (list (Reg 'rax) (Deref r1 o1))))]
    [(Instr op (list (Deref r1 o1) (Imm n1))) #:when (> (abs n1) 2147483647)
                                              (list (Instr 'movq (list (Imm n1) (Reg 'rax))) (Instr op (list (Deref r1 o1) (Reg 'rax))))]
    [_ (list e)]))

(define (patch-block block)
  (match block
    [(Block info es) (Block info (append-map patch-instr es))]))
;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (match p
    [(X86Program info body)
     (X86Program info
                 (for/list ([block body])
                   (cons (car block) (patch-block (cdr block)))))]))

(define (generate-prelude info)
  (let* ([S (dict-ref info 'stack-space)]
         [used-callee (dict-ref info 'used-callee)]
         [C (identity (length used-callee))]
         [fsize (- (align (* 8 (+ S C)) 16) (* 8 C))]
         [rsize (align (* 8 (dict-ref info 'num-root-spills)) 16)])
    (Block '()
           `(,(Instr 'pushq (list (Reg 'rbp)))
             ,(Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
             ,@(if (not (eq? fsize 0)) (list (Instr 'subq (list (Imm fsize) (Reg 'rsp)))) '())
             ,@(map (lambda (v) (Instr 'pushq (list (Reg v)))) used-callee)
             ,(Instr 'movq (list (Imm (rootstack-size)) (Reg 'rdi)))
             ,(Instr 'movq (list (Imm (heap-size)) (Reg 'rsi)))
             ,(Callq 'initialize 2)
             ,(Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15)))
             ,(Instr 'movq (list (Imm 0) (Deref 'r15 0)))
             ,(Instr 'addq (list (Imm rsize) (Reg 'r15)))
             ,(Jmp 'start)))))

(define (generate-conclusion info)
  (let* ([S (dict-ref info 'stack-space)]
         [used-callee (dict-ref info 'used-callee)]
         [C (identity (length used-callee))]
         [fsize (- (align (* 8 (+ S C)) 16) (* 8 C))]
         [rsize (align (* 8 (dict-ref info 'num-root-spills)) 16)])
    (Block '()
           `(,@(map (lambda (v) (Instr 'popq (list (Reg v)))) (reverse used-callee))
             ,(Instr 'subq (list (Imm rsize) (Reg 'r15)))
             ,@(if (not (eq? fsize 0)) (list (Instr 'addq (list (Imm fsize) (Reg 'rsp)))) '())
             ,(Instr 'popq (list (Reg 'rbp)))
             ,(Retq)))))
;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info body)
     (X86Program
      info
      (dict-set* body 'main (generate-prelude info) 'conclusion (generate-conclusion info)))]))


(define (get-color-nonvec satset)
  (define (get_color t)
    (if (set-member? satset t)
        (get_color (add1 t))
        t))
  (get_color 0))

(define (get-color-vec satset)
  (define (get_color t)
    (if (set-member? satset t)
        (get_color (cond
                     [(= t 10) -6]
                     [(< -5) (sub1 t)]
                     [else (add1 t)]))
        t))
  (get_color 0))

(define reg-set (list->set (range 0 (num-registers-for-alloc))))
(define (dsatur g m ltypes)
  (let* ([colors (make-hash (reg-colors))]
         [get-satur (lambda (v)
                      (list->set (filter-map (lambda (d) (dict-ref colors d #f)) (sequence->list (in-neighbors g v)))))]
         [get-mov-color (lambda (v)
                          (if (has-vertex? m v)
                              (list->set (filter-map (lambda (d) (let ([color (dict-ref colors d -1)])
                                                              (if (= color -1) #f color))) (sequence->list (in-neighbors m v))))
                              (set))
                          )]
         [get-color (lambda (var sat-set)
                      (if (is-vector ltypes var)
                          (get-color-vec sat-set)
                          (get-color-nonvec sat-set)))]
         [get-avail-mov-color (lambda (v [satur (get-satur v)] )
                                ;; (printf "AVAIL MOV: ~a ~a ~a~n" v (get-mov-color v) satur)
                                (set-subtract (get-mov-color v) satur))]
         [cmp (lambda (x y)
                (let* ([saturx (get-satur x)]
                       [satury (get-satur y)]
                       [lx (set-count saturx)]
                       [ly (set-count satury)])
                  (if (equal? lx ly)
                      (>= (set-count (get-avail-mov-color x saturx)) (set-count (get-avail-mov-color y satury)))
                      (> lx ly))))]
         [set-color! (lambda (loc color)
                       (dict-set! colors loc color))]
         [pq (make-pqueue cmp)]
         [handles (for/list ([v (in-vertices g)]  ;; #:unless (dict-has-key? colors v)
                             )
                    (cons v (pqueue-push! pq v)))]
         [get-handle (lambda (v) (dict-ref handles v #f))])
    (begin
      (for ([_ (in-range (pqueue-count pq))])
        (let* ([most (pqueue-pop! pq)]
               [satur (get-satur most)]
               ;; [maxloc (add1 (argmax identity satur))]
               ;; [availregset (set-subtract reg-set (list->set satur))]
               ;; [color (if (> (set-count availregset) 0) (argmin identity (set->list availregset)) maxloc)]
               [color (let* ([naivecolor (get-color most satur)]
                             [movcolors (get-avail-mov-color most satur)])
                        (if (= (set-count movcolors) 0)
                            naivecolor
                            (let ([movcolor (argmin identity (set->list movcolors))])
                              (if (> movcolor (num-registers-for-alloc))
                                  (min movcolor naivecolor)
                                  movcolor))))])
          ;; (debug 'most most)
          ;; (if (set-member? satur color)
          ;;     (printf "ERROR EROOR ~a ~a~n" color satur)
          ;;     (void))
          ;; (if (not (equal? color (get-color satur)))
          ;;     (printf "NOT EQ ~a ~a ~a~n" most color (get-color satur))
          ;;     (void))
          ;;
           ;; (printf "most ~a: ~a: color: ~a~n" most satur color)
          ;; (printf "maxloc: ~a color: ~a availregset: ~a~n" maxloc color availregset)
          (unless (dict-has-key? colors most)
            (set-color! most color)
            (for ([u (in-neighbors g most)] )
              (pqueue-decrease-key! pq (get-handle u))))))
      colors)))

(define (reg-color-block b ltypes)
  (match b
    [(Block info code) (Block (dict-set info 'colors (dsatur (dict-ref info 'conflicts) (dict-ref info 'mov-graph) ltypes)) code)]))

;; (define (reg-color p)
;;   (match p
;;     [(X86Program info blocks) (X86Program info (for/list ([block blocks]) (cons
;;                                                                            (car block)
;;                                                                            (reg-color-block (cdr block)))))]))
(define (reg-color p)
  (match p
    [(X86Program info blocks) (X86Program (dict-set info 'colors (dsatur (dict-ref info 'conflicts) (dict-ref info 'mov-graph) (dict-ref info 'locals-types))) blocks)]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  ;; Uncomment the following passes as you finish them.
  `(
    ("Shrink" ,shrink ,interp-Lvec ,type-check-Lvec)
    ;; ("Partial eval" ,partial-eval ,interp-Lif ,type-check-Lif)
    ("uniquify" ,uniquify ,interp-Lvec ,type-check-Lvec)
    ("uncover-get!" ,uncover-get! ,interp-Lvec ,type-check-Lvec-has-type )
    ("expose allocation" ,expose_allocation ,interp-Lvec-prime)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvec-prime)
    ("explicate control" ,explicate-control ,interp-Cvec ,type-check-Cvec)
    ("select instructions" , select-instructions ,interp-pseudo-x86-2)
    ("uncover live" ,uncover_live ,interp-pseudo-x86-2)
    ("build interference" ,build_interference ,interp-pseudo-x86-2)
    ("build mov graph" ,build_mov_graph ,interp-pseudo-x86-2)
    ("reg-color" ,reg-color ,interp-pseudo-x86-2)
    ("assign homes" ,assign-homes ,interp-x86-2)
    ("patch instructions" ,patch-instructions ,interp-x86-2)
    ("patch instructions 2" ,patch-instructions ,interp-x86-2)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-2)
    ))
