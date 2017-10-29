#lang nanopass

(require nanopass/base)

(define *state* 0)

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

(un-nest
 (group-exprs
  (parse-L0
   `((defun (f x)
       (if (> x 0)
           (- x 1)
           (begin
             (var y 1)
             (* x y))))))))