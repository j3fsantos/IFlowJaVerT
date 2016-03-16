#lang s-exp rosette

(require rosette/solver/smt/cvc4)
(current-solver (new cvc4%))
(current-bitwidth 32)

(require (file "util.rkt"))
(require (file "operations.rkt"))
(require (file "objects.rkt"))
(require (file "frame.rkt"))
(require (file "functions.rkt"))
(require (file "prologue.rkt"))
(require (file "assertions.rkt"))

(define (locals instructions)
  (make-vector (+ 2 (apply max (filter number? (flatten instructions))))))

(define (make-registers prog inputs)
  (define n (length inputs)) 
  (let ((x (locals prog)))
    (letrec ((setup
              (lambda (inputs idx)
                (cond ((not (null? inputs))
                       (vector-set! x idx (car inputs))
                       (setup (cdr inputs) (+ idx 1)))))))
      (setup inputs 0)
      x)))

(define depth-limit 10)

(define (make-parameter val)
  (let ([cell val])
    (case-lambda [() cell]
                 [(new-val) (set! cell new-val)])))

(define-syntax-rule
  (parameterize ([param val]) body ...)
  (let ([old (param)])
    (param val)
    (let ([out (begin body ...)])
      (param old)
      out)))
      
(define control-stack (make-parameter '()))

(define (kill x)
  (letrec ((iter (lambda (l)
		   (assert (not (car l)))
		   (cond ((not (null? (cdr l)))
			  (iter (cdr l)))))))
    (iter (union-guards x))))

(define (count-stmt stmt stack)
  (if (symbolic? stmt)
      (letrec ((rec (lambda (lst)
		      (if (null? lst)
			  0
			  (let ((max (rec (cdr lst)))
				(me (count-stmt (car lst) stack)))
			    (if (> me max) me max))))))
	(rec (union-values stmt)))
      (letrec ((iter (lambda (lst)
		       (if (null? lst)
			   0
			   (+ (iter (cdr lst))
			      (if (or (equal? (car lst) stmt)
				      (and (union? (car lst))
					   (member stmt (union-values (car lst)))))
				  1
				  0))))))
	(iter stack))))

(define (sym->datum v)
  (cond [(term? v) (term->datum v)]
	[(union? v) (map sym->datum (union-values v))]
	[(list? v) (map sym->datum v)]
	[else v]))

(define (interpret f caller-frame inputs)
  (letrec ((rec (lambda (lst)
		  (if (null? lst)
		      (if (symbolic? f)
			  (kill f)
			  '())
		      (if (equal? (function-id f) (car lst))
			  (interpret-function (car lst) (function-code (car lst)) (function-creator f) caller-frame inputs)
			  (rec (cdr lst)))))))
    (rec (functions))))

(define (interpret-function id prog creator caller-frame inputs)
  (let ((last -1)
	(regs (make-registers prog inputs))
	(this-frame (frame id caller-frame creator)))

    (define (load n)
      (cond ((number? n)
	     (vector-ref regs n))
	    ((symbol? n)
	     (lookup n globals))
	    ((cons? n)
	     (lexical-ref (car n) (cdr n)))
	    (#t n)))
    
    (define (store regs lval rval)
      (cond ((null? lval)
	     rval)
	    ((number? lval)
	     (vector-set! regs lval rval))
	    ((cons? lval)
	     (lexical-set! (car lval) (cdr lval) rval))
	    (#t
	     (set-global! lval rval))))
    
    (define (goto n) (interp (list-ref prog n)))
    
    (define (call callee-function . args)
      (interpret callee-function this-frame (cons null (cons callee-function args))))
    
    (define (method-call callee-receiver callee-function . args)
      (apply call (op-object-get callee-receiver callee-function) args))
    
    (define (new receiver . args)
      (interpret (materialize-function (get-constructor (function-id receiver) (+ 1 (length args))) this-frame) this-frame (cons null (cons receiver args))))
    
    (define (create id)
      (materialize-function id this-frame))
    
    (define (lexical-ref id name)
      (lexical-get id name this-frame))
    
    (define (lexical-set! id name value)
      (lexical-put! id name this-frame value))
    
    (define (interp block)
      (letrec ((iter
		(lambda (block)
		  (let* ((stmt (first block))
			 (op (first stmt)))
		    (print stmt) (newline)
		    (parameterize ([control-stack (cons stmt (control-stack))])
		      (cond
		       ((equal? op 'goto)
			(goto (cadr stmt)))
          
		       ((equal? op 'if-goto)
			(let ((x (load (cadr stmt))))
			  (if (and (symbolic? x)
				   (> (count-stmt stmt (control-stack)) depth-limit))
			      ;; cut off loop by asserting all guards false
			      (kill x)
			      (if x
				  (goto (list-ref stmt 2))
				  (goto (list-ref stmt 3))))))
		       
		       ((equal? op 'return)
			(set! last (- (vector-length regs) 1))
			(vector-set! regs (- (vector-length regs) 1) (load (cadr stmt))))
		       
		       (#t
			(let ((op (cadr stmt))
			      (lval (car stmt)))
			  (if
			   (and
			    (or (equal? op 'call)
				(equal? op 'new)	    
				(equal? op 'method-call))
			    (> (count-stmt stmt (control-stack)) depth-limit)
			    (or (symbolic? (load (caddr stmt)))
				(and (equal? op 'method-call)
				     (symbolic? (load (cadddr stmt))))))
			   (begin
			     (print "killing") (newline)
			     (print stmt) (newline)
			     (kill (load (car (cdr (cdr stmt)))))
			     (cond
			      ((equal? op 'method-call)
			       (kill (load (car (cdr (cdr (cdr stmt)))))))))
			   (begin
			    (set! last lval)
			    (store 
			     regs 
			     lval
			     (apply 
			      (cond ((equal? op 'call) call)
				    ((equal? op 'new) new)	
				    ((equal? op 'method-call) method-call)	
				    ((equal? op 'lexical-ref) lexical-ref)
				    ((equal? op 'lexical-set) lexical-set!)
				    ((equal? op 'create) create)
				    (#t op)) 
			      (map load (cddr stmt)))))))))))
		  (cond ((not (null? (cdr block)))
			 (iter (cdr block)))))))
	(cond ((not (null? block))
	       (iter block)))))
    (goto 0)
    (vector-ref regs last)))

(provide interpret
	 (all-from-out (file "util.rkt"))	 
	 (all-from-out (file "functions.rkt"))
	 (all-from-out (file "operations.rkt"))
	 (all-from-out (file "frame.rkt"))
	 (all-from-out (file "assertions.rkt"))
	 (all-from-out (file "prologue.rkt"))
	 (all-from-out (file "objects.rkt")))
