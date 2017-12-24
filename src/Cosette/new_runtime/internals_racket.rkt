#lang rosette

(require (file "mem_model.rkt"))
(require (file "util.rkt"))

(define (starts-with? s1 s2)
  (cons 'normal (string-prefix? s1 s2)))

(define (toUpperCase s)
  (cons 'normal (string-upcase s)))

(define (replace str from to)
  (cons 'normal (string-replace str from to #:all? #f)))

(define (includes? str stuff)
  (cons 'normal (string-contains? str stuff)))

(define (sub-string str l r)
  (cons 'normal (substring str l r)))

(define (str-index-of str x)
  (cons 'normal (string-index-of str x)))

(define (register-racket-methods hp)
  ;; (displayln "register-racket-methods")
  (let* ((hp (register-js-builtin-method "String" "indexOf" str-index-of hp))
         (hp (register-js-builtin-method "String" "includes" includes? hp))
         (hp (register-js-builtin-method "String" "startsWith" starts-with? hp))
         (hp (register-js-builtin-method "String" "toUpperCase" toUpperCase hp))
         (hp (register-js-builtin-method "String" "substring" sub-string hp))
         (hp (register-js-builtin-method "String" "replace" replace hp)))
    hp))


(provide register-racket-methods)
