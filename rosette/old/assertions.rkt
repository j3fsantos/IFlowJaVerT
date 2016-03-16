#lang s-exp rosette

(require "util.rkt")

(define current-assertions #t)

(define (clear-assertions!) (set! current-assertions #t))

(define (get-assertions) current-assertions)

(define (op-assert e) 
  (print e)
  (newline)
  (set! current-assertions (and current-assertions e))
  #t)
  
(provide clear-assertions! get-assertions op-assert)
