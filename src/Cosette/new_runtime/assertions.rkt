#lang s-exp rosette

(require "util.rkt")

(define current-assertions #t)

(define current-assumptions #t)

(define (clear-assertions!) (set! current-assertions #t))

(define (get-assertions) current-assertions)

(define (get-assumptions) current-assumptions)

(define (op-assert e) 
  (set! current-assertions (and current-assertions e))
  (println (format "Assertions: ~v" current-assertions))
  #t)

(define (op-assume e)
  (set! current-assumptions (and current-assumptions e))
  (println (format "Assumptions: ~v" current-assumptions))
  #t)
  
(provide clear-assertions! get-assertions get-assumptions op-assert op-assume)
