#lang rosette

(require (file "mem_model.rkt"))

(define (starts-with? s1 s2)
  (let ((len-s1 (string-length s1))
        (len-s2 (string-length s2)))
    ;(println (format "INSIDE starts-with? - FINALLY!!!! with s1:~v, len-s1:~v and s2:~v, len-s2:~v" s1 len-s1 s2 len-s2))
    (let ((ret
           (if (> len-s2 len-s1)
               #f
               (let* ((s1-prefix (substring s1 0 len-s2))
                      (ret (equal? s2 s1-prefix)))
                 ;(println (format "s1-prefix: ~v. s1-prefix=s2: ~v" s1-prefix ret))
                 ret))))
      (list 'normal ret))))


(define (toUpperCase s)
  (list 'normal (string-upcase s)))


(define (register-racket-methods hp)
  (register-js-builtin-method "String" "startsWith" starts-with? hp)
  (register-js-builtin-method "String" "toUpperCase" toUpperCase hp))


(provide register-racket-methods)