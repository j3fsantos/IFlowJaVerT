#lang s-exp rosette


(define (make-number-symbol var)
  (make-symbolic var number?))

(define (make-string-symbol var)
  (make-symbolic var string?))

(provide make-number-symbol make-string-symbol) 

(define (symbolic? x) 
  (or (union? x) (term? x)))

(provide symbolic?)

(define logic-state #t)

(define (reset-logic-state)
  (set! logic-state #t))

(define (get-logic-state)
  logic-state)

(define (update-logic-state expr)
  (set! logic-state (and logic-state expr)))

(define (jsil-assert expr)
  (solve (assert (and logic-state expr))))

(define (jsil-assume expr)
  (update-logic-state expr))

(define jsil-discharge reset-logic-state)

(provide jsil-assume jsil-assert jsil-discharge)
