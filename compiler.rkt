#lang nanopass

(require graph)
(require racket/set)
(require racket/match)
(require nanopass/base)

(define datum? number?)
(define identifier? symbol?)

; Surface syntax:
;
; Program ::= (defun (Identfier Identfier...) Expr...)...
;
; Expr ::= Identifier
;        | Number
;        | (var Identifier Expr)
;        | (set Identifier Expr)
;        | (if Expr Expr Expr)
;        | (Identifier|Primitive Expr...)
;        | (begin Expr...)
(define-language L0
  (entry Program)
  (terminals
   (datum (d))
   (identifier (id)))
  (Expr (e)
        id
        d
        (var id e)
        (set id e)
        (if e0 e1 e2)
        (id e* ...)
        (begin e* ...)
        (return e))
  (Defun (def)
         (defun (id0 id* ...) e* ...))
  (Program (prog)
           (def* ...)))

; Generate a sexpr->L0 parser
(define-parser parse-L0 L0)

; Example:
; (parse-L0 `((defun (f x) (if (> x 0) (return (- x 1)) (begin (var y 1) (return (* x y)))))))

; Remove e ... forms and replace with (begin e ...)
(define-language L1
  (extends L0)
  (Defun (def)
         (- (defun (id0 id* ...) e* ...))
         (+ (defun (id0 id* ...) e))))

; Un-nested version of surface syntax:
; Removes all nested expressions (except for if expressions)
(define-language L2
  (extends L1)
  (Expr (e)
        (- (if e0 e1 e2)
           (id e* ...))
        (+ (if id e1 e2)
           (id id* ...))))

; L2 with jumps instead of if expressions
(define-language L3
  (extends L2)
  (Expr (e)
        (- (if id e1 e2))
        (+ (jnz id0 id1)
           (jmp id)
           (label id))))

; Linear syntax (no arbitrary nesting)
(define-language L4
  (extends L3)
  (Expr (e)
        (- (begin e* ...)))
  (Defun (def)
         (- (defun (id0 id* ...) e))
         (+ (defun (id0 id* ...) e* ...))))

; List of registers available to the register allocation algorithm
(define registers '(eax ebx ecx edx esi edi))
(define (register? reg)
  (member reg registers))
(define stack-ref? number?)

; Register-allocated version of L4 (replace variable identifiers with registers/stack-ref)
(define-language L5
  (extends L4)
  (terminals
   (+ (register (reg))
      (stack-ref (stk))))
  (Ref (r)
       (+ (register reg)
          (stack-ref stk)))
  (Expr (e)
        (- id
           (var id e)
           (set id e)
           (id id* ...)
           (jnz id0 id1))
        (+ (ref r)
           (set r e)
           (id r* ...)
           (jnz r id1)))
  (Defun (def)
         (- (defun (id0 id* ...) e* ...))
         (+ (defun (id0 r* ...) e* ...))))

; Replace bare expressions with (begin ...) to ease flattening and un-nesting
(define-pass group-exprs : L0 (src) -> L1 ()
  (Expr : Expr (e) -> Expr ()
        [(if ,[e0] (begin ,[e1*] ...) (begin ,[e2*] ...))
         `(if ,e0 (begin ,e1* ...) (begin ,e2* ...))]
        [(if ,[e0] (begin ,[e1*] ...) ,[e2])
         `(if ,e0 (begin ,e1* ...) (begin ,e2))]
        [(if ,[e0] ,[e1] (begin ,[e2*] ...))
         `(if ,e0 (begin ,e1) (begin ,e2* ...))]
        [(if ,[e0] ,[e1] ,[e2])
         `(if ,e0 (begin ,e1) (begin ,e2))])
  (Defun : Defun (def) -> Defun ()
         [(defun (,id0 ,id* ...) ,[e*] ...)
          `(defun (,id0 ,id* ...) (begin ,e* ...))]))

; Convert functions and conditionals to A-normal form (remove nested expressions and replace with variable references where possible without side-effects)
(define-pass un-nest : L1 (src) -> L2 ()
  (definitions
    (define (make-binding e)
      (let ([s (gensym)])
        (with-output-language (L2 Expr) 
          (cons `(var ,s ,e) `,s)))))
  (Expr : Expr (e) -> Expr ()
        [(if ,[e0] ,[e1] ,[e2])
         (let ([s (gensym)])
           `(begin
              (var ,s ,e0)
              (if ,s ,e1 ,e2)))]
        [(,id ,[e*] ...)
         (let ([vars (map make-binding e*)])
           `(begin
              ,(map car vars) ...
              (,id ,(map cdr vars) ...)))]))

; Replace the if expression syntax with jump-based conditionals to create a linear AST without any nested expressions
(define-pass expand-if : L2 (src) -> L3 ()
  (Expr : Expr (e) -> Expr ()
        [(if ,id ,[e0] ,[e1])
         (let ([lblTrue (gensym)]
               [lblDone (gensym)])
         `(begin
            (jnz ,id ,lblTrue)
            ,e1
            (jmp ,lblDone)
            (label ,lblTrue)
            ,e0
            (label ,lblDone)))]))

; Flatten `var`/`set`/`return` expressions before flattening `begin`s
(define-pass flatten-assignments : L3 (src) -> L3 ()
  (Expr : Expr (e) -> Expr ()
        [(var ,id (begin ,[e*] ... ,[e]))
         `(begin
            ,e* ...
            (var ,id ,e))]
        [(set ,id (begin ,[e*] ... ,[e]))
         `(begin
            ,e* ...
            (set ,id ,e))]
        [(return (begin ,[e*] ... ,[e]))
         `(begin
            ,e* ...
            (return ,e))]))

; Remove (some) redundant `begin`s (e.g. (begin (begin x...) y...) => (begin x... y...))
(define-pass flatten : L3 (src) -> L3 ()
  (definitions
    (define (flatten-expr expr)
      (nanopass-case (L3 Expr) expr
                     [(begin ,e* ...)
                      (foldr append '() (map flatten-expr e*))]
                     [else (list expr)])))
    (Defun : Defun (def) -> Defun ()
           [(defun (,id0 ,id* ...) (begin ,e* ...))
            `(defun (,id0 ,id* ...) (begin ,(foldr append '() (map flatten-expr e*)) ...))]))

; Replace the (begin e* ...) of a function body with e* ...
(define-pass unwrap-fn-body : L3 (src) -> L4 ()
  (Defun : Defun (def) -> Defun ()
         [(defun (,id0 ,id* ...) (begin ,[e*] ...))
          `(defun (,id0 ,id* ...) ,e* ...)]
         [(defun (,id0 ,id* ...) ,e)
          `(defun (,id0 ,id* ...) ,e)]))

; Collect the list of all variables in an expression
(define (expr-vars varset expr)
  (nanopass-case (L4 Expr) expr
                 [,id
                  (set-add varset id)]
                 [,d
                  varset]
                 [(var ,id ,e)
                  (let ([varset* (set-add varset id)])
                    (expr-vars varset* e))]
                 [(set ,id ,e)
                  (let ([varset* (set-add varset id)])
                    (expr-vars varset* e))]
                 [(,id ,id* ...)
                  (foldr (lambda (e s) (set-add s e)) varset id*)]
                 [(label ,id)
                  varset]
                 [(return ,e)
                  (expr-vars varset e)]
                 [(jmp ,id)
                  varset]
                 [(jnz ,id0 ,id1)
                  varset]))

; Collect all variables in a list of expressions
(define (vars exprs)
  (foldr (lambda (e s) (expr-vars s e)) (set) exprs))

; Get the live variables upon entering (car exprs)
(define (in exprs)
  (if (null? exprs)
      (set)
      (set-union (use (car exprs)) (set-subtract (out exprs) (def (car exprs))))))

; Get the live variables upon exiting (car exprs)
(define (out exprs)
  (in (cdr exprs)))

; Get the set of variables assigned in expr
(define (def expr)
  (nanopass-case (L4 Expr) expr
                 [(var ,id ,e)
                  (set id)]
                 [(set ,id ,e)
                  (set id)]
                 [else
                  (set)]))

; Get the set of variables used in expr
(define (use expr)
  (nanopass-case (L4 Expr) expr
                 [,id
                  (set id)]
                 [(var ,id ,e)
                  (use e)]
                 [(set ,id ,e)
                  (use e)]
                 [(,id ,id* ...)
                  (apply set id*)]
                 [(return ,e)
                  (use e)]
                 [(jnz ,id0 ,id1)
                  (set id0)]
                 [else
                  (set)]))

; Split a list of vertices into a complete graph of those edges
; E.g.: (pairs '(a b c d e)) => '((a b) (a c) (a d) (a e) (b c) (b d) (b e) (c d) (c e) (d e))
(define (pairs verts)
  (combinations verts 2))

; Get the edges of an interference graph of a list of expressions
; Interference is defined as the state in which 2 variables a, b are members of (in e)
; Such that any set of variables live upon entering an expression form a complete induced subgraph of the register interference graph
(define (exprs->edges exprs)
  (if (null? exprs)
      '()
      (append (pairs (set->list (in exprs))) (exprs->edges (cdr exprs)))))

; Count the number of times the identifier `var` is used in a list of expressions
(define (count-uses var exprs)
  (match exprs
    ['() 0]
    [(cons x xs)
     (+ (count-uses var xs)
        (nanopass-case (L4 Expr) x
                       [,id
                        (if (equal? id var) 1 0)]
                       [,d
                        0]
                       [(var ,id ,e)
                        (+ (if (equal? id var) 1 0) (count-uses var (list e)))]
                       [(set ,id ,e)
                        (+ (if (equal? id var) 1 0) (count-uses var (list e)))]
                       [(,id ,id* ...)
                        (length (filter (lambda (id) (equal? id var)) id*))]
                       [(return ,e)
                        (count-uses var (list e))]
                       [(label ,id)
                        0]
                       [(jmp ,id)
                        0]
                       [(jnz ,id0 ,id1)
                        (if (equal? id0 var) 1 0)]))]))

; Sum the weights of each color used in the register interference graph
; Weight is defined as the number of uses of a variable, such that the color with the greatest weight represents the color that is accessed/assigned to more than any other color
(define (color-weights coloring exprs)
  (let ([*weights* (make-hash)])
    (hash-for-each coloring
                   (lambda (var color)
                     (hash-set! *weights* color (+ (hash-ref *weights* color 0) (count-uses var exprs)))))
    *weights*))

; Convert an index `i` of a color into a valid reference (register name or stack reference)
; Either registers[i] or -(4 * (i - #registers)) if i >= #registers
(define (index->ref i)
  (with-output-language (L5 Ref)
    (if (< i (length registers))
        `(register ,(list-ref registers i))
        `(stack-ref ,(- (* 4 (- i (length registers))))))))

; Map the set of colors to valid references (using index->ref), favoring the colors with the greatest weight first
; Variables with the most uses get priority, so the more times a color is used the more likely it is to be placed in a register
(define (map-colors weights)
  (let ([order (sort weights > #:key cdr)])
    (for/list ([color order]
               [index (length order)])
      (cons (car color) (index->ref index)))))

; Allocate registers based on variable->color and color->reference mappings
; Applies each individual algorithm to and then replace the variables with actual references
(define-pass reg-alloc : L4 (src) -> L5 ()
  (definitions
    (define (col id coloring mapping)
      (cdr (assoc (hash-ref coloring id) mapping)))
    (define (apply-colors e coloring mapping)
      (nanopass-case (L4 Expr) e
                     [,id
                      (with-output-language (L5 Expr)
                        `(ref ,(col id coloring mapping)))]
                     [,d
                      (with-output-language (L5 Expr)
                        `,d)]
                     [(var ,id ,e)
                      (with-output-language (L5 Expr)
                        `(set ,(col id coloring mapping) ,(apply-colors e coloring mapping)))]
                     [(set ,id ,e)
                      (with-output-language (L5 Expr)
                        `(set ,(col id coloring mapping) ,(apply-colors e coloring mapping)))]
                     [(,id ,id* ...)
                      (with-output-language (L5 Expr)
                        `(,id ,(map (lambda (id) (col id coloring mapping)) id*) ...))]
                     [(return ,e)
                      (with-output-language (L5 Expr)
                        `(return ,(apply-colors e coloring mapping)))]
                     [(label ,id)
                      (with-output-language (L5 Expr)
                        `(label ,id))]
                     [(jmp ,id)
                      (with-output-language (L5 Expr)
                        `(jmp ,id))]
                     [(jnz ,id0 ,id1)
                      (with-output-language (L5 Expr)
                        `(jnz ,(col id0 coloring mapping) ,id1))])))
  (Defun : Defun (def) -> Defun ()
         [(defun (,id0 ,id* ...) ,e* ...)
          (let* ([graph (unweighted-graph/undirected (exprs->edges e*))]
                 [vars (set->list (vars e*))]
                 [num-vars (length vars)]
                 [colors (coloring graph num-vars)]
                 [weights (color-weights colors e*)]
                 [mapped (map-colors (hash->list weights))]
                 [alloced (map (lambda (e) (apply-colors e colors mapped)) e*)]
                 [params (map (lambda (id) (col id colors mapped)) id*)])
            `(defun (,id0 ,params ...) ,alloced ...))]))

; Apply all compilation passes to an s-expression
(define (compile program)
  (reg-alloc
   (unwrap-fn-body
    (flatten
     (flatten-assignments
      (expand-if
       (un-nest
        (group-exprs
         (parse-L0 program)))))))))

; Read/Eval/Print/Loop that calls out to compile to evaluate input
(define (repl)
  (display "Regalloc> ")
  (let ([input (read (current-input-port))])
    (println (compile input))
    (repl)))

; Run a REPL
(repl)

; Example program to paste into REPL:
; ((defun (f x) (if (> x 0) (return (- x 1)) (begin (var y 1) (return (* x y))))))