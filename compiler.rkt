#lang racket
(require racket/set
         racket/stream)
(require racket/fixnum)
(require racket/set)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
(provide (all-defined-out))
(define reserved-registers (set 'rax 'r11 'r15 'rsp 'rbp))
(define (uniquify-exp env) ;; TODO: this function currently does nothing. Your code goes here
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let* ([newvar (gensym x)]
              [newexp ((uniquify-exp env) e)]
              [newenv (dict-set env x newvar)]
              [newbody ((uniquify-exp newenv) body)])
         (Let newvar newexp newbody))]
      [(Prim op es)
       (Prim op
             (for/list ([e es])
               ((uniquify-exp env) e)))]
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
    [_ (error "explicate_tail unhandled case" e)]))

(define (explicate_assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) (explicate_assign rhs y (explicate_assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [_ (error "explicate_assign unhandled case" e)]))

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
(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info `((start . ,(explicate_tail body))))]))

(define (get-op-name p)
  (match p
    [(Prim '+ (list e1 e2)) 'addq]
    [(Prim '- (list e1 e2)) 'subq]
    [(Prim '- (list e1)) 'negq]
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
    [(Var v) (Var v)]))

(define (select-inst-assgn v e)
  (match e
    [(? atm? e) (list (Instr 'movq (list (select-inst-atom e) v)))]
    [(Prim 'read '()) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) v)))]
    [(Prim op (list e1 e2))
     (list (Instr 'movq (list (select-inst-atom e1) v))
           (Instr (get-op-name e) (list (select-inst-atom e2) v)))]
    [(Prim op (list e1))
     (list (Instr 'movq (list (select-inst-atom e1) v)) (Instr (get-op-name e) (list v)))]))

(define (select-inst-stmt s)
  (match s
    [(Assign (Var v) (Prim '+ (list a1 (Var v2))))
     #:when (equal? v v2)
     (list (Instr 'addq (list (select-inst-atom a1) (Var v))))]
    [(Assign (Var v) (Prim '+ (list (Var v1) a2)))
     #:when (equal? v v1)
     (list (Instr 'addq (list (select-inst-atom a2) (Var v))))]
    [(Assign v e) (select-inst-assgn v e)]))

(define (select-inst-tail tail)
  (match tail
    [(Return e) (append (select-inst-assgn (Reg 'rax) e) (list (Jmp 'conclusion)))]
    [(Seq s t) (append (select-inst-stmt s) (select-inst-tail t))]))

(define arg-regs '(rdi rsi rdx rcx r8 r9))
(define second-read-instr (set 'addq 'subq))

(define (second-read? op) (set-member? second-read-instr op))

(define is-loc? (or/c Var Reg))

(define (uncover_read_secondread instr)
  (match instr
    [(Instr (? second-read? op) (list _ (Var v))) (set v)]
    [(Instr (? second-read? op) (list _ (Reg v))) (set v)]
    [_ (set)]))

(define (uncover_read instr)
  (let ([sset (uncover_read_secondread instr)])
    (match instr
      [(Instr _ (cons (Var v) _)) (set-add sset v)]
      [(Instr _ (cons (Reg v) _)) (set-add sset v)]
      [(Callq _ arity) (list->set (take arg-regs arity))]
      [(Jmp 'conclusion) (set 'rax 'rsp)]
      [_ (set)])))

(define (uncover_write instr)
  (match instr
    [(Instr _ (list _ (Var v))) (set v)]
    [(Instr _ (list _ (Reg v))) (set v)]
    [(Instr _ (list (Var v))) (set v)]
    [(Instr _ (list (Reg v))) (set v)]
    [(Callq _ _) caller-save]
    [_ (set)]))

(define (get_live code ini)
  (foldr (lambda (instr lset)
           (cons
            (set-union (set-subtract (car lset) (uncover_write instr)) (uncover_read instr))
            lset))
         (list ini) code))

(define (uncover_block b)
  (match b
    [(Block info code) (Block (dict-set info 'lafter (cdr (get_live code (set)))) code)]))

(define (uncover_live p)
  (match p
    [(X86Program info blocks)
     (X86Program info
                 (for/list ([block blocks]) `(,(car block) . ,(uncover_block (cdr block)))))]))

(define (get-val loc)
  (match loc
    [(Var v) v]
    [(Reg v) v]
    [_ void]))

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
         [used-callee (filter (not/c #f) (hash-map colors (lambda (k v)
                                                            (if (and (set-member? callee-colors v) (not (set-member? registers k)))
                                                                (color->register v)
                                                                #f))))]
         [locs (for/list ([var ltypes])
                 (cons var (color->loc (dict-ref colors var) (length used-callee))))]
         )
    (values nstack (list->set used-callee) locs)))
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
(define (dsatur g)
  (let* ([colors (make-hash (reg-colors))]
         [get-satur (lambda (v)
                      (filter-map (lambda (d) (dict-ref colors d #f)) (sequence->list (in-neighbors g v))))]
         [cmp (lambda (x y)
                (<= (length (get-satur x)) (length (get-satur y))))]
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
               [maxloc (add1 (argmax identity satur))]
               [availregset (set-subtract reg-set (list->set satur))]
               [color (if (> 0 (set-count availregset)) (argmin identity (set->list availregset)) maxloc)])
          (unless (dict-has-key? colors most)
            (set-color! most color)
            (for ([u (in-neighbors g most)] )
              (pqueue-decrease-key! pq (get-handle u)))
            )))
      colors)))

(define (reg-color-block b)
  (match b
    [(Block info code) (Block (dict-set info 'colors (dsatur (dict-ref info 'conflicts))) code)]))

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
    ;; ("Partial eval" ,partial-eval ,interp-Lvar ,type-check-Lvar)
    ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
    ("uncover live" ,uncover_live ,interp-pseudo-x86-0)
    ("build interference" ,build_interference ,interp-pseudo-x86-0)
    ("reg-color" ,reg-color ,interp-pseudo-x86-0)
    ("assign homes" ,assign-homes ,interp-x86-0)
    ("patch instructions" ,patch-instructions ,interp-x86-0)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)))
