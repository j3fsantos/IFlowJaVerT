#lang s-exp rosette

(require "util.rkt")

(define current-assertions #t)

(define current-assumptions #t)

(define (clear-assertions!) (set! current-assertions #t))

(define (get-assertions) current-assertions)

(define (get-assumptions) current-assertions)

(define (op-assert e) 
  (print e)
  (newline)
  (set! current-assertions (and current-assertions e))
  #t)

(define (op-assume e)
  (print e)
  (newline)
  (set! current-assumptions (and current-assumptions e)))
  
(provide clear-assertions! get-assertions get-assumptions op-assert op-assume)
