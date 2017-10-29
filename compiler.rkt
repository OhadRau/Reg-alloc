#lang nanopass

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

; SSA version of L2 (removes `set`)
(define-language L3
  (extends L2)
  (Expr (e)
        (+ (phi id0 id1 id2))
        (- (set id e))))

; Register-allocated version of L3
;(define-language L4
;  (extends L3)
;  (terminals
;   (+ (register (reg))
;      (stack-ref (stk))))
;  (Expr (e)
;        (- id)
;        (+ reg)
;        (+ stk)))

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

; Remove (some) redundant `begin`s (e.g. (begin (begin x...) y...) => (begin x... y...))
(define-pass flatten : L2 (src) -> L2 ()
  (definitions
    (define (flatten-expr expr)
      (nanopass-case (L2 Expr) expr
                     [(begin ,e* ...)
                      (foldr append '() (map flatten-expr e*))]
                     [(var ,id (begin ,e* ...))
                      (list (with-output-language (L2 Expr)
                              `(var ,id (begin ,(foldr append '() (map flatten-expr e*)) ...))))]
                     [(var ,id ,e)
                      (list (with-output-language (L2 Expr)
                              `(var ,id (begin ,(flatten-expr e) ...))))]
                     [(set ,id (begin ,e* ...))
                      (list (with-output-language (L2 Expr)
                              `(set ,id (begin ,(foldr append '() (map flatten-expr e*)) ...))))]
                     [(set ,id ,e)
                      (list (with-output-language (L2 Expr)
                              `(set ,id (begin ,(flatten-expr e) ...))))]
                     [(if ,id (begin ,e1* ...) (begin ,e2* ...))
                      (list (with-output-language (L2 Expr)
                        `(if ,id (begin ,(foldr append '() (map flatten-expr e1*)) ...) (begin ,(foldr append '() (map flatten-expr e2*)) ...))))]
                     [(if ,id (begin ,e1* ...) ,e2)
                      (list (with-output-language (L2 Expr)
                              `(if ,id (begin ,(foldr append '() (map flatten-expr e1*)) ...) (begin ,(flatten-expr e2) ...))))]
                     [(if ,id ,e1 (begin ,e2* ...))
                      (list (with-output-language (L2 Expr)
                              `(if ,id (begin ,(flatten-expr e1) ...) (begin ,(foldr append '() (map flatten-expr e2*)) ...))))]
                     [(if ,id ,e1 ,e2)
                      (list (with-output-language (L2 Expr)
                              `(if ,id (begin ,(flatten-expr e1) ...) (begin ,(flatten-expr e2) ...))))]
                     [else (list expr)])))
    (Defun : Defun (def) -> Defun ()
           [(defun (,id0 ,id* ...) (begin ,e* ...))
            `(defun (,id0 ,id* ...) (begin ,(foldr append '() (map flatten-expr e*)) ...))]))

(define-pass ssa : L2 (src) -> L3 ()
  (definitions
    (define (extend-env var env)
      (cons (cons var (gensym)) env))
    (define (create-env vars)
      (foldr (lambda (x lst) (cons (cons x x) lst)) '() vars))
    (define (lookup var env)
      (let ([assoc (assq var env)])
        (if (list? assoc)
            (cdr assoc)
            '__undefined-identifier)))
    (define (apply-ssa env expr)
      (nanopass-case (L2 Expr) expr
                     [,id
                      (cons env `,(lookup id env))]
                     [(var ,id ,e)
                      (let ([env* (extend-env id env)])
                      (cons env* `(var ,(lookup id env*) ,(cdr (apply-ssa env e)))))]
                     [(set ,id ,e)
                      (let ([env* (extend-env id env)])
                        (cons env* `(var ,(lookup id env*) ,(cdr (apply-ssa env e)))))]
                     [else (cons env expr)])))
  (Defun : Defun (def) -> Defun ()
         [(defun (,id0 ,id* ...) ,e)
          `(defun (,id0 ,id* ...) ,(apply-ssa (create-env id*) e))]))

; Collect the list of all variables defined in an expr
(define (vars expr)
  '())

; Check if a variable is live in an expr
(define (live? id expr)
  #t)

(flatten
 (un-nest
  (group-exprs
   (parse-L0
    `((defun (f x)
        (if (> x 0)
            (- x 1)
            (begin
              (var y 1)
              (* x y)))))))))