#lang rosette

;;
;; Support for list "hash-tables"
;;

;; Sane list membership
(define (list-mem? lst mem)
  (if (eq? (member mem lst) #f) #f #t))

;; Does the key exist in an lht?
(define (lht-has-key? lht key)
  (letrec ((iter
            (lambda (lst)
              (cond [(null? lst) #f]
                    [(equal? (car (car lst)) key) #t]
                    [#t (iter (cdr lst))]))))
    (iter lht)))

;; The value associated with a key in an lht
(define (lht-value lht key)
  (letrec ((iter
            (lambda (lst)
              (cond [(null? lst) empty]
                    [(equal? (car (car lst)) key) (cdr (car lst))]
                    [#t (iter (cdr lst))]))))
    (iter lht)))

;; Keys of an lht - this will have duplicates
(define (lht-keys lht)
  (map (lambda (x) (car x)) lht))

;; Values of an lht - this will have duplicates
(define (lht-values lht)
  (map (lambda (x) (cdr x)) lht))

;; 
;; Literals - constants and types
;;
(define jempty     '$$empty)
(define jnull      '$$null)
(define jundefined '$$undefined)
(define jsglobal   '$lg)

(define undefined-type '$$undefined_type)
(define null-type      '$$null_type)
(define empty-type     '$$empty_type)
(define boolean-type   '$$boolean_type)
(define number-type    '$$number_type)
(define string-type    '$$string_type)
(define obj-type       '$$object_type)
(define ref-a-type     '$$reference_type)
(define ref-v-type     '$$v-reference_type)
(define ref-o-type     '$$o-reference_type)
(define list-type      '$$list_type)

;; Math constants
(define mc-minval '$$min_value)
(define mc-maxval '$$max_value)
(define mc-random '$$random)
(define mc-pi     '$$pi)
(define mc-e      '$$e)
(define mc-ln10   '$$ln10)
(define mc-ln2    '$$ln2)
(define mc-log2e  '$$log2e)
(define mc-log10e '$$log10e)
(define mc-sqrt12 '$$sqrt1_2)
(define mc-sqrt2  '$$sqrt2)

;; List of non-math constants
(define jsil-constants
   (list
      jempty          jnull        jundefined
      undefined-type  null-type    empty-type
      boolean-type    number-type  string-type
      obj-type        ref-a-type   ref-v-type
      ref-o-type      list-type))

;; List of math constants
(define jsil-math-constants
   (list
      mc-minval mc-maxval mc-random
      mc-pi     mc-e      mc-ln10
      mc-ln2    mc-log2e  mc-log10e
      mc-sqrt12 mc-sqrt2))

;; Is something a literal?
(define (literal? val)
  (let (( ret
          (or
           (number? val)
           (boolean? val)
           (string? val)
           (is-loc? val)
           (is-llist? val)
           (list-mem? jsil-constants val)
           (list-mem? jsil-math-constants val))))
    ;;(println (format "literal? with ~v produced ~v" val ret))
    ret))

;; Evaluating a literal
(define (eval_literal lit)
  (if (list-mem? jsil-math-constants lit)
      (cond
        [(eq? lit mc-minval) 5e-324]
        [(eq? lit mc-maxval) 1.7976931348623158e+308]
        [(eq? lit mc-random) (random)]
        [(eq? lit mc-pi)     pi]
        [(eq? lit mc-e)      (exp 1.)]
        [(eq? lit mc-ln10)   (log 10.)]
        [(eq? lit mc-ln2)    (log 2.)]
        [(eq? lit mc-log2e)  (/ 1 (log 2.))]
        [(eq? lit mc-log10e) (/ 1 (log 10.))]
        [(eq? lit mc-sqrt12) (sqrt 0.5)]
        [(eq? lit mc-sqrt2)  (sqrt 2.)]
      )
      (cond
      	[(is-llist? lit)
      		(let* ((tail (cdr lit))
      		       (mtail (map eval_literal tail)))
      		  (cons 'jsil-list mtail))]
      	[#t lit]
      )
  )
)

;; Type operations
(define (jsil-type-of val)
  (cond
    ((number? val) number-type)
    ((string? val) string-type)
    ((boolean? val) boolean-type)
    ((is-loc? val) obj-type)
    ((eq? val jnull) null-type)
    ((eq? val jundefined) undefined-type)
    ((eq? val jempty) empty-type)
    ((eq? val mc-minval) number-type)
    ((eq? val mc-maxval) number-type)
    ((eq? val mc-random) number-type)
    ((eq? val mc-pi)     number-type)
    ((eq? val mc-e)      number-type)
    ((eq? val mc-ln10)   number-type)
    ((eq? val mc-ln2)    number-type)
    ((eq? val mc-log2e)  number-type)
    ((eq? val mc-log10e) number-type)
    ((eq? val mc-sqrt12) number-type)
    ((eq? val mc-sqrt2)  number-type)
    ((is-llist? val) list-type)
    (#t (error (format "Wrong argument to typeof: ~a" val)))))

;; Subtyping
(define (jsil-subtype type1 type2)
  (or 
   (eq? type1 type2) 
   (and
    (eq? ref-a-type type2)
    (or (eq? ref-v-type type1)
        (eq? ref-o-type type1)))))

;; Special properties
(define protop "@proto")
(define larguments '$larguments)
(define parguments "args")

(provide jempty jnull jundefined literal? protop larguments parguments jsil-type-of ref-v-type ref-o-type lht-values)

;;
;; binary operators 
;;

;; Shift left and right
(define (shl n m) (arithmetic-shift n    m))
(define (shr n m) (arithmetic-shift n (- m)))

(define (jsil_string_to_number str)
  (let ((str_num (string->number str)))
    (if (eq? str_num #f)
        +nan.0
        str_num)))

(define (jsil_num_to_int num)
  (if (nan? num) 0
      (if (infinite? num) num
          (if (eq? num 0) num
              (* (sgn num) (floor (abs num)))
          )
      )
  )
)

(define (jsil_num_to_int_32 num)
  (if (nan? num) 0
      (if (infinite? num) 0
          (if (eq? num 0) 0
              (let* ((two-32 (expt 2 32))
                     (two-31 (expt 2 31))
                     (pos-int (* (sgn num) (floor (abs num))))
                     (smod (modulo pos-int two-32)))
                (if (>= smod two-31)
                   (- smod two-32)
                   smod
                )
              )
          )
      )
  )
)

(define (jsil_num_to_uint_16 num)
  (if (nan? num) 0
      (if (infinite? num) 0
          (if (eq? num 0) 0
              (let* ((two-16 (expt 2 16))
                     (pos-int (* (sgn num) (floor (abs num))))
                     (smod (modulo pos-int two-16)))
                (if (< smod 0)
                   (+ smod two-16)
                   smod
                )
              )
          )
      )
  )
)

(define (jsil_num_to_uint_32 num)
  (if (nan? num) 0
      (if (infinite? num) 0
          (if (eq? num 0) 0
              (let* ((two-32 (expt 2 32))
                     (pos-int (* (sgn num) (floor (abs num))))
                     (smod (modulo pos-int two-32)))
                (if (< smod 0)
                   (+ smod two-32)
                   smod
                )
              )
          )
      )
  )
)

(define (unsigned_right_shift lhs rhs)
  (let* ((lhs-32 (jsil_num_to_uint_32 lhs))
         (rhs-32 (jsil_num_to_uint_32 rhs)))
    (shr (inexact->exact (truncate lhs-32)) (inexact->exact (truncate rhs-32)))
  )
)

(define (jsil-number-to-string n)
  (cond
    [(eq? n +nan.0) "NaN"]
    [#t (integer->string n)]))


(define (check-logic-variable var )
  (if (not (symbol? var))
      #f
      (let ((var-string (symbol->string var)))
        (or (and (> (string-length var-string) 5) (string=? (substring var-string 0 5) "_lvar"))
            (and (> (string-length var-string) 1) (string=? (substring var-string 0 1) "#"))
            (and (> (string-length var-string) 4) (string=? (substring var-string 0 4) "_$l_"))))))


;;'= '< '<= '<s '+ '- '* '/ '% '<:  '++  '@ 'and 'or '& '^  '<< '>> ':: '** 'm_atan2 'bor 'bnot '>>> 'not 'num_to_string 'string_to_num '!
;;'is_primitive 'length 'car 'cdr 'm_abs 'm_acos 'm_asin 'm_atan 'm_cos 'm_sin 'm_tan 'm_sgn 'm_sqrt 'm_exp 'm_log 'm_ceil 'm_floor 'm_round
;;'num_to_int 'num_to_int32 'num_to_unint16 'num_to_unint32 's-len 'l-len


(define (is-operator? arg)
  (let ((operator-list
         (list '= '< '<= '<s '+ '- '* '/ '% '<:  '++  '@ 'and 'or '& '^  '<< '>> ':: '**
               'm_atan2 'bor 'bnot '>>> 'not 'num_to_string 'string_to_num '!'is_primitive
               'length 'car 'cdr 'm_abs 'm_acos 'm_asin 'm_atan 'm_cos 'm_sin 'm_tan 'm_sgn
               'm_sqrt 'm_exp 'm_log 'm_ceil 'm_floor 'm_round 'num_to_int 'num_to_int32
               'num_to_unint16 'num_to_unint32 's-len 'l-len)))
    (member arg operator-list)))


(define (expr-lvars expr)
  (cond
    ;; literal
    [(literal? expr) (set)]
    ;; lvar
    [(check-logic-variable expr)
     (begin 
       (println (format "found the lvar ~v" expr))
       (set expr))]
    ;; pvar
    [(symbol? expr)
     (begin 
       (println (format "found the pvar ~v" expr))
       (set))]
    ;; binop 
    [(and (list? expr) (eq? (length expr) 3) (is-operator? (car expr)))
     (begin 
       (println (format "found the binop expr ~v" expr))
       (set-union (expr-lvars (second expr)) (expr-lvars (third expr))))]
    ;; unop
    [(and (list? expr) (eq? (length expr) 2) (is-operator? (car expr)))
     (expr-lvars (second expr))]
    ;; type-of
    [(and (list? expr) (eq? (first expr) 'typeof))
     (expr-lvars (second expr))]
    ;; lst-nth
    [(and (list? expr) (eq? (first expr) 'l-nth))
     (set-union (expr-lvars (second expr)) (expr-lvars (third expr)))]
    ;; s-nth
    [(and (list? expr) (eq? (first expr) 's-nth))
     (set-union (expr-lvars (second expr)) (expr-lvars (third expr)))]
    ;; {{ le_1, ..., le_n }}
    [(and (list? expr) (eq? (first expr) 'jsil-list))
     (let ((le-sets (map expr-lvars (cdr expr))))
       (foldl (lambda (elem v) (set-union elem v)) (set) le-sets))]
    ;; -{ le_1, ..., le_n }-
    [(and (list? expr) (eq? (first expr) 'jsil-set))
     (let ((le-sets (map expr-lvars (cdr expr))))
       (foldl (lambda (elem v) (set-union elem v)) (set) le-sets))]
    ;; set-union 
    [(and (list? expr) (eq? (first expr) 'set-union))
     (let ((le-sets (map expr-lvars (cdr expr))))
       (foldl (lambda (elem v) (set-union elem v)) (set) le-sets))]
    ;; set-inter 
    [(and (list? expr) (eq? (first expr) 'set-inter))
     (let ((le-sets (map expr-lvars (cdr expr))))
       (foldl (lambda (elem v) (set-union elem v)) (set) le-sets))]
    ;;
    [else (set)]))



(define (lexpr-substitution lexpr subst)
  (cond
    ;; literal
    [(literal? lexpr) lexpr]
    ;; lvar
    [(check-logic-variable lexpr)
     (if (hash-has-key? subst lexpr)
         (hash-ref subst lexpr)
         (error "Incomplete substitution"))]
    ;; pvar var
    [(symbol? lexpr) lexpr]
    ;; binop 
    [(and (list? lexpr) (eq? (length lexpr) 3) (is-operator? (car lexpr)))
     (list (first lexpr) (lexpr-substitution (second lexpr) subst) (lexpr-substitution (third lexpr) subst))]
    ;; unop 
    [(and (list? lexpr) (eq? (length lexpr) 2) (is-operator? (car lexpr)))
     (list (first lexpr) (lexpr-substitution (second lexpr) subst))]
    ;; type-of
    [(and (list? lexpr) (eq? (first lexpr) 'typeof))
     (list 'typeof (lexpr-substitution (second lexpr) subst))]
    ;; lst-nth
    [(and (list? lexpr) (eq? (first lexpr) 'l-nth))
     (list 'l-nth (lexpr-substitution (second lexpr) subst) (lexpr-substitution (third lexpr) subst))]
    ;; s-nth
    [(and (list? lexpr) (eq? (first lexpr) 's-nth))
      (list 's-nth (lexpr-substitution (second lexpr) subst) (lexpr-substitution (third lexpr) subst))]
    ;; {{ le_1, ..., le_n }}
    [(and (list? lexpr) (eq? (first lexpr) 'jsil-list))
     (let ((sles (map (lambda (le) (lexpr-substitution le subst)) (cdr lexpr))))
       (cons 'jsil-list sles))]
    ;; -{ le_1, ..., le_n }-
    [(and (list? lexpr) (eq? (first lexpr) 'jsil-set))
     (let ((sles (map (lambda (le) (lexpr-substitution le subst)) (cdr lexpr))))
       (cons 'jsil-set sles))]
    ;; set-union
    [(and (list? lexpr) (eq? (first lexpr) 'set-union))
     (list 'set-union (lexpr-substitution (second lexpr) subst) (lexpr-substitution (third lexpr) subst))]
    ;; set-inter 
    [(and (list? lexpr) (eq? (first lexpr) 'set-inter))
     (list 'set-inter (lexpr-substitution (second lexpr) subst) (lexpr-substitution (third lexpr) subst))]
     ;;
    [else (error "DEATH. lexpr-substitution")]))


(define operators-list
  (list
    (cons '= 
    	(lambda (x y)
        (if (and (integer? x) (integer? y))
    		  (eq? x y)
          (cond 
    		    [(and (eq? x +nan.0) (eq? y +nan.0)) #f]
    		    [else (eq? x y)]))))

    (cons '<
          (lambda (x y)
            (if (and (number? x) (number? y)) (< x y) jundefined)))

    (cons '<=
          (lambda (x y)
            (if (and (number? x) (number? y)) (<= x y) jundefined)))

    (cons '<s
          (lambda (x y)
            (if (and (string? x) (string? y)) (string<? x y) jundefined)))

    (cons '+
          (lambda (x y)
            (if (and (number? x) (number? y)) (+ x y) jundefined)))

    (cons '-
          (lambda (x . rest)
            (if (eq? (length rest) 0)
                (if (number? x) (- x) jundefined)
                (let ((y (first rest)))
                  (if (and (number? x) (number? y)) (- x y) jundefined)))))
    
    (cons '*
          (lambda (x y)
            (if (and (number? x) (number? y)) (* x y) jundefined)))

    (cons '/
          (lambda (x y)
            (cond 
            [(and (number? x) (number? y)) 
            	(let* ((ix (exact->inexact x))
            	       (iy (exact->inexact y)))
            		(cond
            		[(and (eq? y 0) (< ix 0)) -inf.0]
            		[(and (eq? y 0) (> ix 0)) +inf.0]
            		[(and (eq? y 0) (eq? ix 0)) +nan.0]
            		[#t (/ ix iy)] 
            		))]
            [else jundefined])))

    (cons '%
          (lambda (x y)
            (if (and (number? x) (number? y)) 
            (cond
            [(or (eq? x +nan.0) (eq? y +nan.0)) +nan.0]
            [#t (modulo x y)]) 
            jundefined)))
          
    (cons '<: jsil-subtype)

    (cons '++
          (lambda (x y)
            (if (and (string? x) (string? y)) (string-append x y) jundefined)))
          
    (cons '@
          (lambda (x y)
            (if (and (is-llist? x) (is-llist? y)) (append x (cdr y)) jundefined)))
    
    (cons 'and (lambda (x y) (error "and operator called illegally")))
    
    (cons 'or (lambda (x y) (error "or operator called illegally")))

    (cons '& (lambda (x y)
                (if (and (number? x) (number? y))
                    (bitwise-and (inexact->exact (truncate x)) (inexact->exact (truncate y)))
                    jundefined)))

    (cons '^ (lambda (x y)
                (if (and (number? x) (number? y))
                    (bitwise-xor (inexact->exact (truncate x)) (inexact->exact (truncate y)))
                    jundefined)))
    
    (cons '<< (lambda (x y)
                 (if (and (number? x) (number? y))
                     (shl (inexact->exact (truncate x)) (inexact->exact (truncate y)))
                     jundefined)))

    (cons '>> (lambda (x y)
                (if (and (number? x) (number? y))
                    (shr (inexact->exact (truncate x)) (inexact->exact (truncate y)))
                    jundefined)))

    (cons ':: (lambda (x y)
               (if (is-llist? y)
                   (append (list 'jsil-list x) (cdr y))
                   jundefined)))

    (cons '** (lambda (x y) (if (and (number? x) (number? y)) (expt x y) jundefined)))

    (cons 'm_atan2 (lambda (x y)
                     (if (and (number? x) (number? y)) (atan y x) jundefined)))

    (cons 'bor (lambda (x y)
                 (if (and (number? x) (number? y))
                      (bitwise-ior (inexact->exact (truncate x)) (inexact->exact (truncate y)))
                      jundefined)))
    
    (cons 'bnot (lambda (x)
                 (if (and (number? x))
                      (bitwise-not (inexact->exact (truncate x)))
                      jundefined)))              

    (cons '>>> (lambda (x y) (if (number? x) (unsigned_right_shift x y) jundefined)))

    (cons 'not (lambda (x) (if (boolean? x) (not x) #f)))

    (cons 'num_to_string (lambda (x) (if (number? x) (jsil-number-to-string x) jundefined)))

    (cons 'string_to_num (lambda (x) (if (string? x) (jsil_string_to_number x) jundefined)))

    (cons '! (lambda (x) (if (number? x) (bitwise-not (inexact->exact x)) jundefined)))  

    (cons 'is_primitive (lambda (x) (or (number? x) (string? x) (boolean? x) (eq? x jnull) (eq? x jundefined))))

    (cons 'length (lambda (x) (if (is-llist? x) (- (length x) 1) (string-length x))))

    (cons 'car (lambda (x) (if (is-llist? x) (car (cdr x)) jundefined)))

    (cons 'cdr (lambda (x) (if (is-llist? x) (cons 'jsil-list (cdr (cdr x))) jundefined)))

    (cons 'm_abs (lambda (x) (if (number? x) (abs x) jundefined)))
    
    (cons 'm_acos (lambda (x) (if (number? x) (acos x) jundefined)))

    (cons 'm_asin (lambda (x) (if (number? x) (asin x) jundefined)))

    (cons 'm_atan (lambda (x) (if (number? x) (atan x) jundefined)))

    (cons 'm_cos (lambda (x) (if (number? x) (cos x) jundefined)))

    (cons 'm_sin (lambda (x) (if (number? x) (sin x) jundefined)))

    (cons 'm_tan (lambda (x) (if (number? x) (tan x) jundefined)))

    (cons 'm_sgn (lambda (x) (if (number? x) (sgn x) jundefined)))

    (cons 'm_sqrt (lambda (x) (if (number? x) (sqrt x) jundefined)))
    
    (cons 'm_exp (lambda (x) (if (number? x) (exp x) jundefined)))

    (cons 'm_log (lambda (x) (if (number? x) (log x) jundefined)))

    (cons 'm_ceil (lambda (x) (if (number? x) (ceiling x) jundefined)))

    (cons 'm_floor (lambda (x) (if (number? x) (floor x) jundefined)))

    (cons 'm_round (lambda (x) (if (number? x) (round x) jundefined)))

    (cons 'num_to_int (lambda (x) (if (number? x) (jsil_num_to_int x) jundefined)))

    (cons 'num_to_int32 (lambda (x) (if (number? x) (jsil_num_to_int_32 x) jundefined)))

    (cons 'num_to_uint16 (lambda (x) (if (number? x) (jsil_num_to_uint_16 x) jundefined)))
    
    (cons 'num_to_uint32 (lambda (x) (if (number? x) (jsil_num_to_uint_32 x) jundefined)))

    (cons 's-len (lambda (x) (if (string? x) (string-length x) jundefined)))
    
    (cons 'l-len (lambda (x) (if (is-llist? x) (- (length x) 1) jundefined)))))

;; Obtaining the operator
(define (to-interp-op op)
  (cond
    [(lht-has-key? operators-list op) (lht-value operators-list op)]
    [else (error "Operator not supported" op)]))

;; Applying binary operators
(define (apply-binop op arg1 arg2)
  (apply op (list arg1 arg2)))

;; Applying unary operators
(define (apply-unop op arg)
  (apply op (list arg)))

(provide to-interp-op apply-binop apply-unop expr-lvars lexpr-substitution check-logic-variable)

;; heaps that can be handled by rosette - God help us all

(define (new-heap)
  '())

(define (new-object)
  '())

;;
;; Mutate the object at location 'loc' with property 'prop' and value 'val'
;;
(define (mutate-object object prop val)
  (cond
    [(null? object)
     (list (cons prop val))]
    [(equal? (car (car object)) prop)
     (cons (cons prop val) (cdr object))]
    [ else
     (cons (car object) (mutate-object (cdr object) prop val))]))

;; 
;; Mutate the heap 'heap' at location 'loc' with property 'prop' and value 'val'
;;
(define (mutate-heap heap object prop val)
  (cond
    [(null? heap)
     (list (cons object (list (cons prop val))))]
    [(equal? (car (car heap)) object)
     (cons (cons object (mutate-object (cdr (car heap)) prop val)) (cdr heap))]
    [ else
      (cons (car heap) (mutate-heap (cdr heap) object prop val))]))

;;
;; Get object from heap
;;
(define (heap-get-obj heap object)
  (let*
      ((obj (lht-value heap object)))
    (if (eq? obj empty) (error (format "Error: ~v is not in the heap." object)) obj)))

;;
;; Get property value from heap
;;
(define (heap-get heap object prop)
  (let*
      ((obj (heap-get-obj heap object))
       (val (lht-value obj prop)))
    (if (eq? val empty) (error (format "Error: (~v, ~v) is not in the heap." object prop)) val)))

;;
;; Get obj fields
;;
(define (petar-get-obj-fields object)
  (let loop ((object object)
             (result '()))
    (cond
      [(null? object) result]
      [(and (pair? (car object)) (not (equal? (string-at (caar object) 0) #\@)))
        (loop (cdr object) (cons (caar object) result))]
      [else (loop (cdr object) result)])))  

;;
;; I don't know what this is
;;
(define (get-obj-fields object)
  (let loop ((object object)
             (result '()))
    (if (null? object)
        result
        (loop (cdr object) (cons (car (car object)) result)))))

;;
;; Get all named fields of an object in the heap
;;
(define (petar-get-fields heap object)
  (let loop ((heap heap))
    (cond
      [(null? heap) jempty]
      [(and (pair? (car heap)) (equal? (car (car heap)) object))
       (let* ((obj (cdr (car heap)))
              (props (petar-get-obj-fields obj)))
         ;; (println (format "Internal get-fields: igf (~a) = ~a" loc props))
         props)]
      [ else (loop (cdr heap))])))

;;
;; Get all fields of an object in the heap
;;
(define (get-fields heap object)
  (let loop ((heap heap))
    (cond
      [(null? heap) jempty]
      [(and (pair? (car heap)) (equal? (car (car heap)) object))
       (let* ((obj (cdr (car heap)))
              (props (get-obj-fields obj)))
         ;; (println (format "Internal get-fields: igf (~a) = ~a" loc props))
         props)]
      [ else (loop (cdr heap))])))

;;
;; Delete cell from an object
;;
(define (object-delete-prop object prop)
  (cond [(null? object) '()]
        [(equal? (car (car object)) prop) (cdr object)]
        [ else (cons (car object) (object-delete-prop (cdr object) prop))]))

;;
;; Delete cell from the heap
;;
(define (heap-delete-prop heap object prop)
  (cond
    [(null? heap) '()]
    [(equal? (car (car heap)) object)
     (cons (cons object (object-delete-prop (cdr (car heap)) prop)) (cdr heap))]
    [ else
      (cons (car heap) (heap-delete-prop (cdr heap) object prop))]))


;; Delete object
(define (heap-delete-object heap object)
  (cond
    [(null? heap) '()]
    [(equal? (car (car heap)) object)
     ;; (println (format "Deleting the object ~v" (cdr (car h-pulp))))
     (cdr heap)]
    [ else
      (cons (car heap) (heap-delete-object (cdr heap) object))]))


;; Replace object at loc with new-obj
(define (heap-replace-object heap loc new-obj)
  (cond
    [(null? heap) (list (cons loc new-obj))]
    [(equal? (car (car heap)) loc)
     ;; (println (format "Deleting the object ~v" (cdr (car h-pulp))))
     (cons (cons loc new-obj) (cdr heap))]
    [ else
      (cons (car heap) (heap-replace-object (cdr heap) loc new-obj))]))


;;
;;
;;
(define (make-heap) '())

;;
;; Heap cell
;;
(define (cell loc prop val)
  (list loc prop val))

;;
;; Construct a heap from given cells
;;
(define (heap . cells)
  (let loop ((new-heap (make-heap))
             (cells cells))
    (if (not (null? cells))
        (let* ((cur-cell (first cells))
               (new-heap (mutate-heap new-heap (first cur-cell) (second cur-cell) (third cur-cell))))
          (loop new-heap (cdr cells)))
        new-heap)))
  

;;
;; Fresh location generator
;;
(define (get-new-loc)
  (gensym "$loc")) 

(define (is-loc? loc)
  (if (not (symbol? loc))
      #f
      (let* ((expr-str (symbol->string loc))
             (expr-str-len (string-length expr-str)))
        (and
         (> expr-str-len 1)
         (equal? (substring (symbol->string loc) 0 2) "$l")))))


;(define (is-a-list? l)
;  (and
;   (list? l)
;   (not (eq? l '()))
;   (eq? (first l) 'jsil-list)
;  )
;)

(define (is-llist? l)
  (define (is-literal-list? l)
    (cond
       [(null? l) #t]
       [else
        (if (not (literal? (car l)))
            #f
            (is-literal-list? (cdr l)))]))
  (and
   (list? l)
   (eq? (first l) 'jsil-list)
   (is-literal-list? (cdr l))))

(define (is-a-list? l)
  (and
   (list? l)
   (eq? (first l) 'jsil-list)
  )
)

(define (make-jsil-list l)
  (cons 'jsil-list l))

(provide is-a-list? make-heap mutate-heap heap-get heap cell get-new-loc make-jsil-list heap-delete-prop heap-delete-object is-loc? is-operator? heap-replace-object) ;; heap-contains?


;; stores - my stuff
;;(define (make-store)
;;  (make-hash)) 

;;(define (store-get store var)
;;  (hash-ref store var))

;;(define (mutate-store store var val)
;;  (hash-set! store var val))
  

;; stores - Julian Dolby
(define (make-store)'())

(define (store-get store var)
  (lht-value store var))

(define (mutate-store store var val)
  (cond ((null? store) (list (cons var val)))
        ((equal? (car (car store)) var)
         (cons (cons (car (car store)) val) (cdr store)))
        (#t
         (cons (car store) (mutate-store (cdr store) var val)))))

(define (store . mappings)
  (let ((new-store (make-store)))
    (let loop ((cur-mappings mappings))
      (when (not (null? cur-mappings))
        (let ((cur-var (first (first cur-mappings)))
              (cur-val (second (first cur-mappings))))
          (mutate-store new-store cur-var cur-val) 
          (loop (rest cur-mappings)))))
    new-store))

(define (var? expr)
  (if (not (symbol? expr))
      #f
      (let* ((expr-str (symbol->string expr))
             (expr-str-len (string-length expr-str)))
         (and (> expr-str-len 0) (not (eq? (substring expr-str 0 1) "$"))))))

(provide make-store mutate-store store-get var? store)

;;
;; Contexts
;;
(define (create-context proc-name ret-var normal-index err-index)
  (list proc-name ret-var normal-index err-index))

(define (is-ctx-entry? ctx-entry)
  (and (list ctx-entry) (eq? (length ctx-entry) 5)))

(define (get-proc-name-from-ctx ctx)
  (cond
    [ (null? ctx) (error (format "Empty context: ~v." ctx))]
    [ (is-ctx-entry? (car ctx)) (caar ctx) ]
    [ else (error (format "Invalid context: ~v." ctx))] ))

(define (is-top-ctx? ctx)
  (eq? (length ctx) 1))

(define (get-top-ctx-entry ctx)
  (if (> (length ctx) 0)
      (first ctx)
      (error (format "Invalid context: ~v." ctx))))


(define (pop-ctx-entry ctx)
  (if (> (length ctx) 1)
      (cdr ctx)
      (error (format "Invalid context: ~v." ctx))))


(define (push-ctx-entry ctx store proc-name ret-var n-index e-index)
  (let ((new-entry (list store proc-name ret-var n-index e-index)))
    ;(displayln (format "new-entry: ~v" new-entry))
    (cons new-entry ctx)))

(provide create-context is-ctx-entry? get-proc-name-from-ctx is-top-ctx? get-top-ctx-entry pop-ctx-entry push-ctx-entry)
  


;;
;; Programs supported by Rosette
;;

(define (program . procs)
  (box
   (map
    (lambda (x)
     (let*
         ((proc-name (get-proc-name x))
          (new-proc (cons proc-name x)))
       new-proc))
      procs)))

(define (get-proc program proc-name)
  (let*
      ((program-pulp (unbox program))
       (proc (lht-value program-pulp proc-name)))
    (if (eq? proc empty) (error (format "Error: procedure ~v is not in the program." proc-name)) proc)))

(define (has-proc? program proc-name)
  (lht-has-key? (unbox program) proc-name))

(define (get-procs prog)
  (lht-values (unbox prog)))

(define (add-proc program proc)
  (let* ((prog-pulp (unbox program))
         (proc-name (get-proc-name proc)))
    (if (lht-has-key? prog-pulp proc-name)
        (error (format "Error: procedure ~a is already defined" proc-name))
        (let ((new-program-pulp (append prog-pulp (list (cons proc-name proc)))))
          (set-box! program new-program-pulp)))))

(define (program-append prog1 prog2)
  (let ((procs2 (get-procs prog2)))
    (let loop ((procs procs2))
      (if (null? procs)
          prog1
          (let ((proc (car procs)))
            (when (not (has-proc? prog1 (get-proc-name proc)))
              (add-proc prog1 proc))
            (loop (cdr procs)))))))

(provide program get-proc program-append)

;; (proc-name proc-params (ret-var ret-label err-var err-label) vector)
(define (procedure proc-name proc-args proc-body ret-info err-info)
  (let* ((cmds-list (rest proc-body))
         (number-of-cmds (length cmds-list))
         (cmds-vec (make-vector number-of-cmds))
         (cur-index 0)
         (ret-var (if (null? ret-info) null (second ret-info)))
         (ret-label (if (null? ret-info) null (third ret-info)))
         (err-var (if (null? err-info) null (second err-info)))
         (err-label (if (null? err-info) null (third err-info))))
    (map (lambda (cmd)
           (vector-set! cmds-vec cur-index cmd)
           (set! cur-index (+ cur-index 1)))
         cmds-list)
    (list proc-name proc-args (list ret-var ret-label err-var err-label) cmds-vec)))

(define (which-pred list-pred)
  (let ((wp-table (make-hash)))
    (let loop ((wp-list list-pred))
      (if (null? wp-list)
          wp-table
          (begin
            (hash-set! wp-table (list (caar wp-list) (cadar wp-list) (caddar wp-list)) (car (cdddar wp-list)))
            (loop (cdr wp-list)))))
  ))    

(define (get-ret-var proc)
  (first (third proc)))

(define (get-err-var proc)
  (third (third proc)))

(define (get-ret-index proc)
  (second (third proc)))

(define (get-err-index proc)
  (fourth (third proc)))

(define (get-proc-name proc)
  (first proc))

(define (get-params proc)
  (second proc))

(define (get-cmd proc index)
  (vector-ref (fourth proc) index))

(define (get-number-of-cmds proc)
  (vector-length (fourth proc)))

(define (proc-init-store proc args)
  (let loop ((params (get-params proc))
             (args args)
             (store (make-store)))
    (if (null? params)
        store
        (if (null? args)
            (loop (cdr params) args (cons (cons (car params) jundefined) store))
            (loop (cdr params) (cdr args) (cons (cons (car params) (car args)) store))))))


(define (args . lst)
  lst)

(define (body . lst)
  (cons 'body lst))

(define (ret-ctx . lst)
  (cons 'return lst))

(define (err-ctx . lst)
  (cons 'error lst))

(provide procedure which-pred eval_literal petar-get-fields get-fields heap-get-obj get-ret-var get-err-var get-ret-index get-err-index get-proc-name get-params get-cmd get-number-of-cmds proc-init-store args body ret-ctx err-ctx)



;;
;; Internal / Builtin Procedure Implemented in Racket 
;;

(define racket-js-implementations (make-hash))

(define (has-racket-implementation? proc-name)
  (hash-has-key? racket-js-implementations proc-name))

(define (get-racket-implementation proc-name)
  (hash-ref racket-js-implementations proc-name))

(define (create-new-function-obj heap function-name)
  (let* ((fun-loc (get-new-loc))
         (heap (mutate-heap heap fun-loc "@call" function-name))        
         (heap (mutate-heap heap fun-loc "@construct" function-name))
         (heap (mutate-heap heap fun-loc "@scope" '(jsil-list)))
         (heap (mutate-heap heap fun-loc "@proto" '$lfun_proto))
         (heap (mutate-heap heap fun-loc "@class" "Function"))
         (heap (mutate-heap heap fun-loc "@extensible" #t)))
    (cons heap fun-loc)))

(define (register-js-builtin-method builtin-obj-name method-name racket-method heap)
  ;;(println "inside register-js-builtin-method")
  ;(println (format "checking the object at ~v" jsglobal))
  (let* ((builtin-obj-desc (heap-get heap jsglobal builtin-obj-name))
         (builtin-obj-loc (third builtin-obj-desc))
         (builtin-obj-proto-loc (third (heap-get heap builtin-obj-loc "prototype")))
         (builtin-obj-proto (heap-get-obj heap builtin-obj-proto-loc))
         (method-obj-desc (lht-value builtin-obj-proto method-name))
         (fresh-function-name (symbol->string (gensym "internal-function-"))))
    ;; put the racket method in the hashtable
    (hash-set! racket-js-implementations fresh-function-name racket-method)
    ;;
    (if (eq? method-obj-desc empty)

        ;; the method does not exist - we need to create it - returning the heap
        (let* ((result (create-new-function-obj heap fresh-function-name))
               (heap (car result))
               (method-obj-loc (cdr result))
               (method-obj-desc (list 'jsil-list "d" method-obj-loc #t #f #t)))
          (mutate-heap heap builtin-obj-proto-loc method-name method-obj-desc))

        ;; the method already exists and we are just going to override it with a racket implementation
        (let* ((method-obj-loc (third method-obj-desc))
               (heap (mutate-heap heap method-obj-loc "@call" fresh-function-name))
               (heap (mutate-heap heap method-obj-loc "@construct" fresh-function-name)))
          ;;(println (format "I am registering a method that already exists with name: ~v at location ~v. fresh-function-name: ~v!!!"
          ;;                 method-name method-obj-loc fresh-function-name))
          heap))))

(provide racket-js-implementations has-racket-implementation? get-racket-implementation register-js-builtin-method)
    




