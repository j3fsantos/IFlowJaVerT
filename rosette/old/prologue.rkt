#lang s-exp rosette

(require "functions.rkt")
(require "objects.rkt")
(require "assertions.rkt")
(require "operations.rkt")

(define Function$ctor
  (list
   (list
    (list 3 'create 2))))

(define-function "Function-ctor" Function$ctor)
(add-constructor! "Function$ctor" 2 'Function)  

(define Object$ctor
  (list
   (list
    (list 3 (op-object "Object")))))

(define-function "Object$ctor" Object$ctor)
(add-constructor! "Object$ctor" 1 'Object)

(define Array$ctor
  (list
   (list
    (list 3 (op-object "Array")))))

(define-function "Array$ctor" Array$ctor)
(add-constructor! "Array$ctor" 1 'Array)

(define assert$function
  (list
   (list
    (list null op-assert 3)
    (list 4 op-id 2))))

(define-function "assert$function" assert$function)


(define-function "String$contains"
  (list
   (list
    (list 4 op-string-contains? 2 3))))

(define-function "String$replace"
  (list
   (list
    (list 5 op-string-replace 2 3 4))))
    
(define (initialize-state)
  (let ((String ((op-object "String"))))
    (op-object-put String "contains" (materialize-function "String$contains" '()))
  
    (op-object-put String "replace" (materialize-function "String$replace" '()))
    
    (set-global! '$$WALA$$int3rnal$$global '($$WALA$$int3rnal$$global))
    (set-global! '$$undefined '($$undefined))
    (set-global! 'Object '(Object))
    (set-global! 'Array '(Array))
    (set-global! 'Function '(Function))
    (set-global! 'assert '(assert$function))
    (set-global! 'String String)))
  
(provide initialize-state)
