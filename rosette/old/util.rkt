#lang s-exp rosette

(provide symbolic? count lookup NaN Infinity read-state update-state)

;; hacks.  figure out what Racket uses
(define NaN 'NaN)
(define Infinity 'Infinity)

(define (symbolic? x) 
  (or (union? x) (term? x)))
        
(define (count v lst)
  (length (filter (lambda (x) (equal? x v)) lst)))

(define (lookup x lst)
  (letrec ((iter
	    (lambda (stuff)
	      (cond ((null? stuff) null)
		    ((equal? (car (car stuff)) x) (cdr (car stuff)))
		    (#t (iter (cdr stuff)))))))
    (iter lst)))

(define (read-state id name state)
  (lookup name (lookup id state)))

(define (update-state id name value state)
  (letrec
      ([bash-or-add-elt
	(lambda (p f lst)
	  (cond ((null? lst)
		 (list (cons p (f null))))
		((equal? (car (car lst)) p)
		 (cons (cons (car (car lst)) (f (cdr (car lst)))) (cdr lst)))
		(#t
		 (cons (car lst) (bash-or-add-elt p f (cdr lst))))))])
    (bash-or-add-elt
     id
     (lambda (current-obj)
       (bash-or-add-elt name (lambda (old-v) value) current-obj))
     state)))
