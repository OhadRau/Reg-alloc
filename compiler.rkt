#lang nanopass

(require nanopass/base)

(define *state* 0)

(define (unique)
  (set! *state* (+ *state* 1))
  (string->symbol (string-append "__unique__" (number->string *state*))))

(define (last-unique)
  (string->symbol (string-append "__unique__" (number->string *state*))))

(define datum? number?)
(define (primitive? x)
  (and
   (symbol? x)
   (memq x '(+ - * /))))
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
(define-language L0
  (entry Program)
  (terminals
   (datum (d))
   (primitive (pr))
   (identifier (id)))
  (Expr (e)
        id
        d
        (var id e)
        (set id e)
        (if e0 e1 e2)
        (pr e* ...)
        (id e* ...))
  (Defun (def)
         (defun (id0 id* ...) e* ...))
  (Program (prog)
           (def* ...)))

(define-parser parse-L0 L0)

; Example:
; (parse-L0 `((defun (f x) (+ x 1))))

(define-language L1
  (extends L0)
  (Exprs (es)
         (+ (begin e* ...)))
  (Defun (def)
         (- (defun (id0 id* ...) e* ...))
         (+ (defun (id0 id* ...) es))))

; Un-nested version of surface syntax:
; Removes all nested expressions (except for if expressions)
(define-language L2
  (extends L1)
  (Expr (e)
        (- (if e0 e1 e2)
           (pr e* ...)
           (id e* ...))
        (+ (if pr e1 e2)
           (pr id* ...)
           (id id* ...))))

; SSA version of L2 (removes `set`)
(define-language L3
  (extends L2)
  (Expr (e)
        (- (set id e))))

; L3 with jumps instead of if expressions
(define-language L4
  (extends L3)
  (Expr (e)
        (+ (label id)
           (jump-if-zero id e))
        (- (if pr e1 e2))))

(define-pass group-exprs : L0 (src) -> L1 ()
  (Defun : Defun (def) -> Defun ()
         [(defun (,id0 ,id* ...) ,[e*] ...)
          `(defun (,id0 ,id* ...) (begin ,e* ...))]))

;(define-pass un-nest : L1 (src) -> L2 ()
;  (expand : Expr (e) -> Exprs ()
;          [(if ,[e0] ,[e1] ,[e2])
;           `(begin
;              (var ,(unique) ,e0)
;              (if ,(last-unique) ,e1 ,e2))]))