#lang s-exp rosette

(require (file "util.rkt"))

(define (frame id parent creator)
  (cons id (cons parent creator)))

(define (frame-id frame)
  (car frame))

(define (frame-parent frame)
  (car (cdr frame)))

(define (frame-creator frame)
  (cdr (cdr frame)))

(define (find-frame id frame)
  (letrec ((find
	    (lambda (f id f-next)
	      (if (equal? (frame-id f) id)
		  f
		  (let ((n (f-next f)))
		    (if (null? n)
			#f
			(find n id f-next)))))))
    (let ((f (find frame id frame-parent)))
      (if f f (find-frame id (frame-creator frame))))))

(define lexical-state '())

(define (lexical-get id name current)
  (read-state (find-frame id current) name lexical-state))

(define (lexical-put! id name current value)
  (set! lexical-state
	(update-state (find-frame id current) name value lexical-state)))

(provide frame frame-id lexical-get lexical-put!)

