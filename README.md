# Reg-alloc
Register allocation using graph coloring with Racket + Nanopass

> **[Overview/Outline](https://www.sharelatex.com/project/59ee8ba4e744fa228f2f3964)**

## Examples

```lisp
 (
 (defun (f x)
   (if (> x 0) 
     (return (- x 1))
     (begin
       (var y 1)
       (return (* x y)))))
 (defun (g x)
   (var m 0)
   (var n 5)
   (var l 7)
   (var x n)
   (set n (+ m 1))
   (set l (+ n m))
   (if (> 5 l)
     (begin
       (set x (+ x 1))
       (var p 7)
       (set n (* x p))
       (return (+ p n m l)))
     (return (* x m))))
 )
```

```lisp
(
(defun (f x)
  (set (register eax) (ref (register ebx)))
  (set (register ecx) 0)
  (set (register eax) (> (register eax) (register ecx)))
  (jnz (register eax) g520499)
  (set (register eax) 1)
  (set (register ecx)
  (ref (register ebx)))
  (set (register eax) (ref (register eax)))
  (return (* (register ecx) (register eax)))
  (jmp g520500)
  (label g520499)
  (set (register eax) (ref (register ebx)))
  (set (register ebx) 1)
  (return (- (register eax) (register ebx))) 
  (label g520500))

(defun (g x)
  (set (register esi) 0)
  (set (register eax) 5)
  (set (register edx) 7)
  (set (register ecx) (ref (register eax)))
  (set (register ebx) (ref (register esi)))
  (set (register eax) 1)
  (set (register eax) (+ (register ebx) (register eax)))
  (set (register eax) (ref (register eax)))
  (set (register ebx) (ref (register esi)))
  (set (register edx) (+ (register eax) (register ebx)))
  (set (register ebx) 5)
  (set (register eax) (ref (register edx)))
  (set (register ebx) (> (register ebx) (register eax)))
  (jnz (register ebx) g520501)
  (set (register eax) (ref (register ecx)))
  (set (register ebx) (ref (register esi)))
  (return (* (register eax) (register ebx)))
  (jmp g520502)
  (label g520501)
  (set (register ebx) (ref (register ecx)))
  (set (register eax) 1)
  (set (register ecx) (+ (register ebx) (register eax)))
  (set (register edi) 7)
  (set (register ebx) (ref (register ecx)))
  (set (register eax) (ref (register edi)))
  (set (register eax) (* (register ebx) (register eax)))
  (set (register ebx) (ref (register edi)))
  (set (register eax) (ref (register eax)))
  (set (register ecx) (ref (register esi)))
  (set (register edx) (ref (register edx)))
  (return (+ (register ebx) (register eax) (register ecx) (register edx)))
  (label g520502))
)
```
