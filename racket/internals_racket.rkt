#lang rosette

(require (file "mem_model.rkt"))

(define (starts-with? s1 s2)
  (list 'normal (string-prefix? s1 s2)))

(define (toUpperCase s)
  (list 'normal (string-upcase s)))

(define (replace str from to)
  (list 'normal (string-replace str from to #:all? #f)))

(define (includes? str stuff)
  (list 'normal (string-contains? str stuff)))

(define (register-racket-methods hp)
  (register-js-builtin-method "String" "includes" includes? hp)
  (register-js-builtin-method "String" "startsWith" starts-with? hp)
  (register-js-builtin-method "String" "toUpperCase" toUpperCase hp)
  (register-js-builtin-method "String" "replace" replace hp))


(provide register-racket-methods)
