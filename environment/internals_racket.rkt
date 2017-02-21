#lang rosette

(require (file "mem_model.rkt"))

(define (starts-with? s1 s2)
  (let ((len-s1 (string-length s1))
        (len-s2 (string-length s2)))
    (if (> len-s2 len-s1)
        #f
        (eq? s2 (substring s1 0 len-s2)))))

(define (register-racket-methods hp)
  (println "inside register-racket-methods")
  (register-js-builtin-method "String" "startsWith" starts-with? hp))

(provide register-racket-methods)