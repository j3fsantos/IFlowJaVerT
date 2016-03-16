#lang s-exp rosette

(require (file "util.rkt"))

(define (bash-name id)
  (string->symbol
   (string-replace
    (string-replace
     (string-replace
      (string-replace id "/" "$" )
      "-" "$")
     "." "$")
    "_" "$")))

(define all-constructors '())

(define (add-constructor! ctor arguments type)
  (set! all-constructors (update-state type arguments ctor all-constructors)))

(define (get-constructor type arguments)
  (read-state type arguments all-constructors))
			  
(define all-code '())

(define (add-code! name body)
 (define-function name body))
 
(define (define-function name body)
  (set! all-code (cons (cons (bash-name name) body) all-code)))

(define (functions)
  (map car all-code))

(define (function id creator-frame)
  (cons id creator-frame))

(define (function-id f)
  (car f))

(define (function-code id)
  (lookup id all-code))

(define (function-creator f)
  (cdr f))

(define (materialize-function id this-frame)
  (print id)
  (newline)
  (function (bash-name id) this-frame))

(provide add-code! functions function function-id function-code function-creator define-function materialize-function add-constructor! get-constructor)
