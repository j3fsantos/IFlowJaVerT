#lang rosette

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
  (displayln "")
  (displayln "")
  (displayln "Asserting this:")
  (displayln expr)
  (displayln "Printing logic state!")
  (displayln logic-state)
  (displayln "End of logic state!")
  (let ((mdl (solve (assert (and logic-state expr)))))
    (displayln "Model:")
    (displayln mdl)
    (displayln "")
    (if (equal? mdl (unsat)) (raise "UNSAT assertion") #t)))

(define (jsil-assume expr)
  (update-logic-state expr)
  #t)

(define (equivalent-to-true? expr)
  (let ((mdl (solve (assert (and logic-state (eq? expr #f))))))
    (equal? mdl (unsat))))

(define (equivalent-to-false? expr)
  (let ((mdl (solve (assert (and logic-state (eq? expr #t))))))
    (equal? mdl (unsat))))

(define jsil-discharge (lambda () #t))

(provide jsil-assume jsil-assert jsil-discharge equivalent-to-true? equivalent-to-false? get-logic-state)

