#lang racket
(require racket/set
         racket/stream)
(require racket/fixnum)
(require racket/set)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))
(define reserved-registers (set 'rax 'r11 'r15 'rsp 'rbp))
(define (uniquify-exp env)
  (lambda (e)
    (define recur (uniquify-exp env))
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool _) e]
      [(If c t e) (If (recur c) (recur t) (recur e))]
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

(define (accumulate_aexps es)
  (foldr (lambda (e flist)
           (match-let ([(list oldes oldbinds) flist])
             (let-values ([(newe newbinds) (rco_atom e)])
               (list (cons newe oldes) (append oldbinds newbinds)))))
         '(() ())
         es))

(define (rco_atom e)
  (match e
    [(Var _) (values e '())]
    [(Int _) (values e '())]
    [(Bool _) (values e '())]
    [(If c t e) (let ([tmpvar (gensym 'tmp)])
                  (values (Var tmpvar) `((,tmpvar . ,(If (rco_exp c) (rco_exp t) (rco_exp e))))))]
    [(Let x e body)
     (let ([tmpvar (gensym 'tmp)] [newe (rco_exp e)] [newbody (rco_exp body)])
       (values (Var tmpvar) `((,tmpvar . ,(Let x newe newbody)))))]
    [(Prim op es)
     (match-let ([(list aexps binds) (accumulate_aexps es)])
       (let ([tmpvar (gensym 'tmp)])
         (values (Var tmpvar) `((,tmpvar . ,(Prim op aexps)) ,@binds))))]))

(define (makeMultiLet binds body)
  (foldl (lambda (bind body) (Let (car bind) (cdr bind) body)) body binds))

(define (rco_exp e)
  (match e
    [(Let x e body) (let* ([newexp (rco_exp e)] [newbody (rco_exp body)]) (Let x newexp newbody))]
    [(Prim op es)
     (match-let ([(list aexps binds) (accumulate_aexps es)])
       (makeMultiLet binds (Prim op aexps)))]
    [(If c t e) (If (rco_exp c) (rco_exp t) (rco_exp e))]
    [_ e]))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco_exp e))]))

(define (explicate_tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_tail body))]
    [(Prim op es) (Return (Prim op es))]
    [(Bool b) (Return (Bool b))]
    [(If cnd thn els) (explicate_pred cnd (explicate_tail thn) (explicate_tail els))]
    [_ (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
    [(If cnd thn els) (explicate_pred cnd (explicate_assign thn x cont) (explicate_assign els x cont))]
    [_ (error "explicate_assign unhandled case" e)]))

(define (create_block tail)
  (match tail
    [(Goto _) tail]
    [else
     (let ([label (gensym 'block)])
       (get-basic-blocks (cons (cons label tail) (get-basic-blocks)))
       (Goto label))]))

(define (explicate_pred cnd thn els)
  (match cnd
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (create_block thn) (create_block els))]
    [(Let x rhs body) (explicate_assign rhs x (explicate_pred body thn els))]
    [(Prim 'not (list e)) (explicate_pred e els thn)]
    [(Prim (? (or/c 'eq? '< '> '<= '>=) op) es) (IfStmt (Prim op es) (create_block thn) (create_block els))]
    [(Bool b) (if b thn els)]
    [(If ncnd nthn nels) (let ([thnblock (create_block thn)] [elsblock (create_block els)])
                           (explicate_pred ncnd
                                           (explicate_pred nthn thnblock elsblock)
                                           (explicate_pred nels thnblock elsblock)))]
    [else (error "explicate_pred unhandled case " cnd)]))

(define (explicate-control p)
  (parameterize ([get-basic-blocks '()])
    (match p
      [(Program info body) (let ([startblock (explicate_tail body)])
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
    [(Let y rhs body) (Let y (shrink-exp rhs) (shrink-exp body))]
    [(Prim op es) (Prim op (map shrink-exp es))]
    [(If c t e) (If (shrink-exp c) (shrink-exp t) (shrink-exp e))]
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

(define (pe_exp env)
  (lambda (e)
    (match e
      [(Var x) (dict-ref env x e)]
      [(Prim '+ (list e1 e2)) ((pe_add env) ((pe_exp env) e1) ((pe_exp env) e2))]
      [(Prim '- (list e1 e2)) ((pe_sub env) ((pe_exp env) e1) ((pe_exp env) e2))]
      [(Prim '- (list e1)) ((pe_neg env) ((pe_exp env) e1))]
      [(Let x e body)
       (let ([rhs ((pe_exp env) e)])
         (if (atm? rhs) ((pe_exp (dict-set env x rhs)) body) (Let x rhs ((pe_exp env) body))))]
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

(define (select-inst-assgn v e)
  (match e
    [(? atm? e) (list (Instr 'movq (list (select-inst-atom e) v)))]
    [(Prim 'read '()) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) v)))]
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
    [(Assign v e) (select-inst-assgn v e)]))

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
      [(Jmp label) (dict-ref lbl->live label)]
      [(JmpIf _ label) (dict-ref lbl->live label)]
      [_ (set)])))

(define (uncover_write instr)
  (match instr
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
                         (Block (dict-set* info 'lbefore (car livesets) 'lafter (cdr livesets))))]))

(define (uncover_live p)
  (match p
    [(X86Program info blocks)
     (let* ([cfg (build_cfg blocks)]
            [vert-list (tsort (transpose cfg))]
            [label->live `((conclusion . ,(set 'rax 'rsp)))]
            [newblocks '()])
       (for ([v vert-list])
         (let ([newblock (uncover_block (dict-ref blocks v) label->live)])
           (dict-set! label->live v (dict-ref (Block-info newblock) 'lbefore))
           (dict-set! newblocks v newblock)))
       (X86Program (dict-set info 'label->live label->live) newblocks))]))

(define (build_cfg blocks)
  (let* ([get_succ (lambda (code)
                     (foldl (lambda (instr succset)
                              (match instr
                                [(Jmp label) (set-add succset label)]
                                [(JmpIf _ label) (set-add succset label)]
                                [_ succset]))
                            (set) code))]
         [get_edge_list (lambda (blockpair)
                          (let ([label (car blockpair)] [block (cdr blockpair)])
                            (for/list ([v (set->list (get_succ (Block-instr* block)))])
                              (cons label v))))])
    (make-multigraph (append-map get_edge_list blocks))))

(define (get-val loc)
  (match loc
    [(Var v) v]
    [(Reg v) v]
    [_ #f]))

(define (get_edge_instr instr lafter)
  (match instr
    [(Instr 'movq (list (app get-val s) (app get-val d))) (for/list ([v lafter] #:unless (and (equal? s d) ((or/c s d) v)))
                                `(,v ,d))]
    [_ (let ([Wset (uncover_write instr)])
         (for*/list ([v lafter] [d (set->list Wset)] #:unless (equal? d v))
           `(,v ,d)))]))

(define (build_interblock code lafterlist)
  (undirected-graph (append-map get_edge_instr code lafterlist)))

(define (build_interference_block block)
  (match block
    [(Block info code) (Block
                        (dict-set info 'conflicts (build_interblock code (dict-ref info 'lafter))) code)]))

(define (build_interference p)
  (match p
    [(X86Program info blocks) (X86Program info (for/list ([block blocks]) `(,(car block) . ,(build_interference_block (cdr block)))))]))

(define (get_mov_related instr)
  (match instr
    [(Instr 'movq (list (app get-val (? (not/c #f) s)) (app get-val (? (not/c #f) d)))) `((,s ,d))]
    [_ '()]))

(define (build_mov_graph_block block)
  (match block
    [(Block info code) (Block (dict-set info 'mov-graph (undirected-graph (append-map get_mov_related code))) code)]))

(define (build_mov_graph p)
  (match p
    [(X86Program info blocks) (X86Program info (for/list ([block blocks]) `(,(car block) . ,(build_mov_graph_block (cdr block)))))]))


(define (assign-home-atm e locs)
  (match e
    [(Reg _) e]
    [(Imm _) e]
    [(Var v) (dict-ref locs v)]))

(define (assign-homes-aexps es locs)
  (foldr (lambda (e l) (cons (assign-home-atm e locs) l)) '() es))

(define (assign-homes-instr e locs)
  (match e
    [(Instr op es) (Instr op (assign-homes-aexps es locs))]
    [_ e]))

(define (assign-homes-block block)
  (match block
    [(Block info es)
     (define-values (stackspace used-callee locs) (get-locs info))
     (Block (dict-set* info 'stack-space stackspace 'used-callee used-callee)
      (for/list ([e es])
        (assign-homes-instr e locs)))]))



(define (color->loc c callee-len)
  (let* ([nreg (num-registers-for-alloc)])
    (if (>= c nreg)
        (Deref 'rbp (* -8 (+ callee-len (- c nreg))))
        (Reg (color->register c)))))

(define callee-colors (list->set (map register->color (set->list callee-save))))

(define (get-locs info)
  (let* ([colors (dict-ref info 'colors)]
         [ltypes (hash-keys colors)]
         [nreg (num-registers-for-alloc)]
         [nloc (argmax identity (hash-values colors))]
         [nstack (max 0 (- nloc nreg))]
         ;; [used-callee (filter-map (lambda (v) (if (set-member? callee-colors v) (color->register v) #f)) (hash-values colors))]
         [used-callee (list->set (filter (not/c #f) (hash-map colors (lambda (k v)
                                                            (if (and (set-member? callee-colors v) (not (set-member? registers k)))
                                                                (color->register v)
                                                                #f)))))]
         [locs (for/list ([var ltypes])
                 (cons var (color->loc (dict-ref colors var) (set-count used-callee))))]
         )
    ;; (printf "nreg: ~a nloc: ~a nstack: ~a used-callee: ~a locs: ~a~n" nreg nloc nstack used-callee locs)
    (values nstack used-callee locs)))
;; assign-homes : x86var -> x86var
;; (define (assign-homes p)
;;  (match p
;;     [(X86Program info body)
;;      (let-values ([(stackspace locs) (get-locs info)])
;;        (X86Program (dict-set info 'stack-space stackspace)
;;                    (for/list ([block body])
;;                      (cons (car block) (assign-homes-block (cdr block) locs)))))]))

(define (assign-homes p)
  (match p
    [(X86Program info body)
     (let* ([newblocks (for/list ([block body])
                         (cons (car block) (assign-homes-block (cdr block))))]
            [stackspace (foldr (lambda (block stack)
                                 (+ (dict-ref (Block-info (cdr block)) 'stack-space) stack)) 0 newblocks)]
            [used-callee (foldr (lambda (block callees)
                                  (set-union callees (dict-ref (Block-info (cdr block)) 'used-callee))) (set) newblocks)])
       (X86Program (dict-set* info 'stack-space stackspace 'used-callee (set->list used-callee)) newblocks))]))

(define (patch-instr e)
  (match e
    [(Instr 'movq (list v v)) '()]
    [(Instr op (list (Imm n1) r)) #:when (and (> (abs n1) 2147483647) (not (equal? op 'movq)))
                                  (list (Instr 'movq (list (Imm n1) (Reg 'r11))) (Instr op (list (Reg 'r11) r)))]
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
         [fsize (- (align (* 8 (+ S C)) 16) (* 8 C))])
    (Block '()
           `(,(Instr 'pushq (list (Reg 'rbp)))
             ,(Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
             ,(Instr 'subq (list (Imm fsize) (Reg 'rsp)))
             ,@(map (lambda (v) (Instr 'pushq (list (Reg v)))) used-callee)
             ,(Jmp 'start)))))

(define (generate-conclusion info)
  (let* ([S (dict-ref info 'stack-space)]
         [used-callee (dict-ref info 'used-callee)]
         [C (identity (length used-callee))]
         [fsize (- (align (* 8 (+ S C)) 16) (* 8 C))])
    (Block '()
           `(,@(map (lambda (v) (Instr 'popq (list (Reg v)))) (reverse used-callee))
             ,(Instr 'addq (list (Imm fsize) (Reg 'rsp)))
             ,(Instr 'popq (list (Reg 'rbp)))
             ,(Retq)))))
;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info body)
     (X86Program
      info
      (dict-set* body 'main (generate-prelude info) 'conclusion (generate-conclusion info)))]))

(define reg-set (list->set (range 0 (num-registers-for-alloc))))
(define (dsatur g m)
  (let* ([colors (make-hash (reg-colors))]
         [get-satur (lambda (v)
                      (list->set (filter-map (lambda (d) (dict-ref colors d #f)) (sequence->list (in-neighbors g v)))))]
         [get-mov-color (lambda (v)
                          (if (has-vertex? m v)
                              (list->set (filter-map (lambda (d) (let ([color (dict-ref colors d -1)])
                                                              (if (< color 0) #f color))) (sequence->list (in-neighbors m v))))
                              (set))
                          )]
         [get-color (lambda (sat-set)
                      (define (get-n lst n)
                        (match lst
                          [`(,x . ,rest) #:when (> n x) (get-n rest n)]
                          [`(,x . ,rest) #:when (= x n) (get-n rest (add1 n))]
                          [_ n]))
                      (get-n (sort (set->list sat-set) <) 0))]
         [get-avail-mov-color (lambda (v [satur (get-satur v)] )
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
               [color (let* ([naivecolor (get-color satur)]
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

(define (reg-color-block b)
  (match b
    [(Block info code) (Block (dict-set info 'colors (dsatur (dict-ref info 'conflicts) (dict-ref info 'mov-graph))) code)]))

(define (reg-color p)
  (match p
    [(X86Program info blocks) (X86Program info (for/list ([block blocks]) (cons
                                                                           (car block)
                                                                           (reg-color-block (cdr block)))))]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  ;; Uncomment the following passes as you finish them.
  `(
    ("Shrink" ,shrink ,interp-Lif ,type-check-Lif)
    ; ("Partial eval" ,partial-eval ,interp-Lvar ,type-check-Lvar)
    ("uniquify" ,uniquify ,interp-Lif ,type-check-Lif)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lif ,type-check-Lif)
    ("explicate control" ,explicate-control ,interp-Cif ,type-check-Cif)
    ("select instructions" , select-instructions ,interp-pseudo-x86-1)
    ; ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
    ; ("uncover live" ,uncover_live ,interp-pseudo-x86-0)
    ; ("build interference" ,build_interference ,interp-pseudo-x86-0)
    ; ("build mov graph" ,build_mov_graph ,interp-pseudo-x86-0)
    ; ("reg-color" ,reg-color ,interp-pseudo-x86-0)
    ; ("assign homes" ,assign-homes ,interp-x86-0)
    ; ("patch instructions" ,patch-instructions ,interp-x86-0)
    ; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
    ))
