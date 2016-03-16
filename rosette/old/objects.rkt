#lang s-exp rosette

(require (file "util.rkt"))
(require (file "functions.rkt"))

;; an object is just a list of pairs
(define state null)
(define id 0)

(define (reset-state!)
  (set! globals null)
  (set! state null)
  (set! id 0))

;; allocate object
(define (op-object type)
  (lambda ()
    (set! id (+ id 1))
    (set! state (append state (list (list id))))
    (op-object-put id 'type type)
    id))


;; all property names are strings in JavaScript
(define (property-as-string property) 
  (if (number? property)
      (int-to-str property)
      property))

(define (primitive-to-prototype object)
  (if (string? object)
      (lookup 'String globals)
      object))

(define (op-in object property) 
  (not (null? (read-state object property state))))

;; search an object for a property, checking the prototype if appropriate
(define (op-object-get object property) 
  (letrec ((opg (lambda (object property) 
		  (let ((mine (read-state object property state)))
		  (print mine)
		  (newline)	  
		    (if (not (null? mine))
			mine
			(let ((proto (read-state object 'prototype state)))
		  (print proto)
		  (newline)	  
			  (if (not (null? proto))
			      (opg proto property)
			      (lookup '$$undefined globals))))))))
    (opg (primitive-to-prototype object) (property-as-string property))))
	      
;; assign a property in an object
(define (op-object-put object property value)
  (set! state (update-state object (property-as-string property) value state))
  (newline))

;; the operator that iterates through an object's property names
(define (op-next-property object property)
  (let ((obj (lookup object state)))
    (print obj)
    (newline)
    (print property)
    (newline)
    (if (or (null? property) (equal? property (lookup '$$undefined globals)))
	(if (null? obj)
	    '()
	    (caar obj))
	(letrec ((find 
		  (lambda (lst)		    
		    (cond ((null? lst) '())
			  ((equal? property (caar lst))
			   (print property)
			   (newline)
			   (print (caar lst))
			   (newline)
			   (print (cdr lst))
			   (newline)
			   (if (null? (cdr lst))
			       '()
			       (car (cadr lst))))
			  (#t (find (cdr lst)))))))
	  (find obj)))))

(define globals '())

(define (set-global! lval rval)
  (set! globals
	(cons (cons lval rval)
	      (filter
	       (lambda (x) (not (equal? (car x) lval)))
	       globals))))

(provide op-object op-object-get op-in op-object-put op-next-property globals set-global! reset-state!)
