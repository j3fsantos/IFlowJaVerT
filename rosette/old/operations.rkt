#lang s-exp rosette

;; the operator that returns its argument: an assignment
(define (op-id x) x)

;; a constant is created by an operator that returns it
(define (op-constant x)
  (lambda () x))

;; if as an expression
(define (op-if condition yes no)
  (if condition yes no))

(define (op-!= x y)
  (not (op-== x y)))

(define (op-! x) 
  (not x))

(define (op-=== x y)
  (op-== x y))

(define (op-== x y)
  (if (and (number? x) (number? y))
      (= x y)
      (equal? x y)))

(define (op-- x y)
  (- x y))

(define (op-+ x y)
  (if (string? x)
      (if (string? y)
	  (string-append x y)
	  (string-append x (int-to-str y)))
      (if (string? y)
	  (string-append (int-to-str x) y)
	  (+ x y))))

(define (op-< x y)
  (< x y))

(define (op-<= x y)
  (<= x y))

(define (op-> x y)
  (> x y))

(define (op->= x y)
  (>= x y))

(define (op-* x y)
  (* x y))

(define (op-/ x y)
  (/ x y))

(define (op-string-prefix? x y)
  (string-prefix? x y))

(define (op-string-suffix? x y)
  (string-suffix? x y))

(define (op-string-contains? x y)
  (string-contains? x y))

(define (op-string-replace x y z)
  (string-replace x y z))

(provide (all-defined-out))
