#lang nanopass

(require racket/set)
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
        (begin e* ...))
  (Defun (def)
         (defun (id0 id* ...) e* ...))
  (Program (prog)
           (def* ...)))

(define-parser parse-L0 L0)

; Example:
; (parse-L0 `((defun (f x) (if (> x 0) (- x 1) (begin (var y 1) (* x y))))))

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

(define (register? reg)
  (member reg '(eax ebx ecx edx esi edi ebp esp)))

(define (stack-ref? stk)
  (and (number? stk)
       (< stk 0)))

; Register-allocated version of L4
(define-language L5
  (extends L4)
  (terminals
   (+ (register (reg))
      (stack-ref (stk))))
  (Expr (e)
        (- id
           (var id e)
           (set id e))
        (+ (val reg)
           (val stk)
           (var reg e)
           (var stk e)
           (set reg e)
           (set stk e))))

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

; Flatten `var`/`set` expressions before flattening `begin`s
(define-pass flatten-assignments : L3 (src) -> L3 ()
  (Expr : Expr (e) -> Expr ()
        [(var ,id (begin ,e* ... ,e))
         `(begin
            ,e* ...
            (var ,id ,e))]
        [(set ,id (begin ,e* ... ,e))
         `(begin
            ,e* ...
            (set ,id ,e))]))

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
                 [(jmp ,id)
                  varset]
                 [(jnz ,id0 ,id1)
                  varset]))

; Collect all variables in a list of expressions
(define (vars exprs)
  (foldr (lambda (e s) (expr-vars s e)) (set) exprs))

(define (in exprs)
  (if (null? exprs)
      (set)
      (set-union (use (car exprs)) (set-subtract (out exprs) (def (car exprs))))))

(define (out exprs)
  (in (cdr exprs)))

(define (def expr)
  (nanopass-case (L4 Expr) expr
                 [(var ,id ,e)
                  (set id)]
                 [else
                  (set)]))

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
                 [(jnz ,id0 ,id1)
                  (set id0)]
                 [else
                  (set)]))

; Print the set of variables in each function
(define-pass print-vars : L4 (src) -> L4 ()
  (Defun : Defun (def) -> Defun ()
         [(defun (,id0 ,id* ...) ,e* ...)
          (writeln (vars e*))
          def]))

(define-pass print-in : L4 (src) -> L4 ()
  (definitions
    (define (loop exprs)
      (if (null? exprs)
          '()
          (begin
            (writeln (in exprs))
            (loop (cdr exprs))))))
  (Defun : Defun (def) -> Defun ()
         [(defun (,id0 ,id* ...) ,e* ...)
          (writeln (loop e*))
          def]))

(print-in
 (print-vars
  (unwrap-fn-body
   (flatten
    (flatten-assignments
     (expand-if
      (un-nest
       (group-exprs
        (parse-L0
         `((defun (f x)
             (if (> x 0)
                 (- x 1)
                 (begin
                   (var y 1)
                   (* x y))))))))))))))