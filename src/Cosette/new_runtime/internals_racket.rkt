#lang rosette

(require (file "mem_model.rkt"))
(require (file "util.rkt"))

(define (starts-with? s1 s2)
  (list 'normal (string-prefix? s1 s2)))

(define (toUpperCase s)
  (list 'normal (string-upcase s)))

(define (replace str from to)
  (list 'normal (string-replace str from to #:all? #f)))

(define (includes? str stuff)
  (list 'normal (string-contains? str stuff)))

(define (sub-string str l r)
  (list 'normal (substring str l r)))

(define (str-index-of str x)
  (list 'normal (string-index-of str x)))

(define (register-racket-methods hp)
  (register-js-builtin-method "String" "indexOf" str-index-of hp)
  (register-js-builtin-method "String" "includes" includes? hp)
  (register-js-builtin-method "String" "startsWith" starts-with? hp)
  (register-js-builtin-method "String" "toUpperCase" toUpperCase hp)
  (register-js-builtin-method "String" "substring" sub-string hp)
  (register-js-builtin-method "String" "replace" replace hp))


(provide register-racket-methods)
