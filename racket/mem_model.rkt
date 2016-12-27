#lang s-exp rosette

;;
;; Support for list "hash-tables"
;;

;; Sane list membership
(define (list-mem? lst mem)
  (if (eq? (member mem lst) #f) #f #t))

;; Creating an empty lht
(define (box-lht lht)
  (box lht))

(define (new-lht)
  '())

;; Does the key exist in an lht?
(define (lht-has-key? lht key)
  (letrec ((iter
            (lambda (lst)
              (cond [(null? lst) #f]
                    [(equal? (car (car lst)) key) #t]
                    [#t (iter (cdr lst))]))))
    (iter lht)))

;; The value associated with a key in an lht
(define (lht-ref lht key)
  (letrec ((iter
            (lambda (lst)
              (cond [(null? lst) empty]
                    [(equal? (car (car lst)) key) (cdr (car lst))]
                    [#t (iter (cdr lst))]))))
    (iter lht)))

;; Keys of an lht
(define (lht-keys lht)
  (map (lambda (x) (car x)) lht))

;; Values of an lht
(define (lht-values lht)
  (map (lambda (x) (cdr x)) lht))

;; 
;; Literals - constants and types
;;
(define jempty     '$$empty)
(define jnull      '$$null)
(define jundefined '$$undefined)

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
           (is-ref? val)
           (list-mem? jsil-constants val)
           (list-mem? jsil-math-constants val))))
    ;(println (format "literal? with ~v produced ~v" val ret))
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
      lit
  )
)

;; Type operations
(define (jsil-type-of val)
  (cond
    ((number? val) number-type)
    ((string? val) string-type)
    ((boolean? val) boolean-type)
    ((is-loc? val) obj-type)
    ((is-ref? val) (ref-type val))
    ((eq? val jnull) null-type)
    ((eq? val jundefined) undefined-type)
    ((eq? val jempty) empty-type)
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

;(define (jsil-number-to-string n)
;  (cond
;    ((integer? n) (int-to-str n))
;    (#t (number->string n))))

(define (jsil-number-to-string n) "0")

(define operators-list
  (list
    (cons '= eq?)
    (cons '< <)
    (cons '<= <=)
    (cons '<s string<?)
    (cons '+ +)
    (cons '- -)
    (cons '* *)
    (cons '/ /)
    (cons '% modulo)
    (cons '<: jsil-subtype)
    (cons 'concat string-append)
    (cons '++ (lambda (x y) (append x (cdr y))))
    (cons 'and (lambda (x y) (and x y)))
    (cons 'or  (lambda (x y) (or  x y)))
    (cons '& (lambda (x y) (bitwise-and (inexact->exact (truncate x)) (inexact->exact (truncate y)))))
    (cons '^ (lambda (x y) (bitwise-xor (inexact->exact (truncate x)) (inexact->exact (truncate y)))))
    (cons '<< (lambda (x y) (shl (inexact->exact (truncate x)) (inexact->exact (truncate y)))))
    (cons '>> (lambda (x y) (shr (inexact->exact (truncate x)) (inexact->exact (truncate y)))))
    (cons ':: (lambda (x y)
               (if (eq? x '(jsil-list))
                y
                (append (list 'jsil-list x) (cdr y)))))
    (cons '** expt)
    (cons 'm_atan2 (lambda (x y) (atan y x)))
    (cons 'bor (lambda (x y) (bitwise-ior (inexact->exact (truncate x)) (inexact->exact (truncate y)))))
    (cons '>>> unsigned_right_shift)
    (cons 'not not)
    (cons 'num_to_string jsil-number-to-string)
    (cons 'string_to_num jsil_string_to_number)
    (cons '! (lambda (x) (bitwise-not (inexact->exact x))))
    (cons 'is_primitive (lambda (x) (or (number? x) (string? x) (boolean? x) (eq? x jnull) (eq? x jundefined))))
    (cons 'length (lambda (x) (if (is-llist? x) (- (length x) 1) (string-length x))))
    (cons 'car (lambda (x) (car (cdr x))))
    (cons 'cdr (lambda (x) (cons 'jsil-list (cdr (cdr x)))))
    (cons 'm_abs abs)
    (cons 'm_acos acos)
    (cons 'm_asin asin)
    (cons 'm_atan atan)
    (cons 'm_cos cos)
    (cons 'm_sin sin)
    (cons 'm_tan tan)
    (cons 'm_sgn sgn)
    (cons 'm_sqrt sqrt)
    (cons 'm_exp exp)
    (cons 'm_log log)
    (cons 'm_ceil ceiling)
    (cons 'm_floor floor)
    (cons 'm_round round)
    (cons 'num_to_int jsil_num_to_int)
    (cons 'num_to_int32 jsil_num_to_int_32)
    (cons 'num_to_uint16 jsil_num_to_uint_16)
    (cons 'num_to_uint32 jsil_num_to_uint_32)
    (cons 's-len string-length)
    (cons 'l-len (lambda (x) (- (length x) 1)))))

;; Obtaining the operator
(define (to-interp-op op)
  (cond
    [(lht-has-key? operators-list op) (lht-ref operators-list op)]
    [else (error "Operator not supported" op)]))

;; Applying binary operators
(define (apply-binop op arg1 arg2)
  (apply op (list arg1 arg2)))

;; Applying unary operators
(define (apply-unop op arg)
  (apply op (list arg)))

(provide to-interp-op apply-binop apply-unop)

;; heaps that can be handled by rosette - God help us all

(define (make-heap)
  (box '()))

(define (new-prop-val-list)
  '())

(define (mutate-prop-val-list prop-val-list prop new-val)
  (cond
    [(null? prop-val-list)
     (list (cons prop new-val))]
    [(equal? (car (car prop-val-list)) prop)
     (cons (cons prop new-val) (cdr prop-val-list))]
    [ else
     (cons (car prop-val-list) (mutate-prop-val-list (cdr prop-val-list) prop new-val))]))

;; 
;; Mutate the heap 'heap' at location 'loc' with property 'prop' and value 'val'
;;
(define (mutate-heap heap loc prop val)
  (define (mutate-heap-pulp h-pulp loc prop val)
    (cond
      [(null? h-pulp)
       (list (cons loc (list (cons prop val))))]
      [(equal? (car (car h-pulp)) loc)
       (cons (cons loc (mutate-prop-val-list (cdr (car h-pulp)) prop val)) (cdr h-pulp))]
      [ else
       (cons (car h-pulp) (mutate-heap-pulp (cdr h-pulp) loc prop val))]))
  (let ((new-heap-pulp (mutate-heap-pulp (unbox heap) loc prop val)))
    (set-box! heap new-heap-pulp)))

;; Get object from heap
(define (heap-get-obj heap loc)
  (let*
      ((heap-pulp (unbox heap))
       (obj (lht-ref heap-pulp loc)))
    (if (eq? obj empty) (error (format "Error: ~v is not in the heap." loc)) obj)))

;; Get property value from heap
(define (heap-get heap loc prop)
  (let*
      ((obj (heap-get-obj heap loc))
       (val (lht-ref obj prop)))
    (if (eq? val empty) (error (format "Error: (~v, ~v) is not in the heap." loc prop)) val)))

;; get obj fields
(define (petar-get-obj-fields fv-list)
  (let loop ((fv-list fv-list)
             (f-list '()))
    (cond
      [(null? fv-list) f-list]
      [(and (pair? (car fv-list)) (is-llist? (cdr (car fv-list))))
        (loop (cdr fv-list) (cons (car (car fv-list)) f-list))]
      [else (loop (cdr fv-list) f-list)])))  

(define (get-obj-fields fv-list)
  (let loop ((fv-list fv-list)
             (f-list '()))
    (if (null? fv-list)
        f-list
        (loop (cdr fv-list) (cons (car (car fv-list)) f-list)))))


;; Get all fields of an object in the heap
(define (petar-get-fields heap loc)
  (let loop ((heap-pulp (unbox heap)))
    (cond
      [(null? heap-pulp) jempty]
      [(and (pair? (car heap-pulp)) (equal? (car (car heap-pulp)) loc))
       (let* ((obj (cdr (car heap-pulp)))
              (props (petar-get-obj-fields obj)))
         (println (format "Internal get-fields: igf (~a) = ~a" loc props))
         props)]
      [ else (loop (cdr heap-pulp))])))


(define (get-fields heap loc)
  (let loop ((heap-pulp (unbox heap)))
    (cond
      [(null? heap-pulp) jempty]
      [(and (pair? (car heap-pulp)) (equal? (car (car heap-pulp)) loc))
       (let* ((obj (cdr (car heap-pulp)))
              (props (get-obj-fields obj)))
         (println (format "Internal get-fields: igf (~a) = ~a" loc props))
         props)]
      [ else (loop (cdr heap-pulp))])))


;; Delete cell from the heap
(define (heap-delete-cell heap loc prop)
  (define (delete-cell-pulp h-pulp loc prop)
    (cond
      [(null? h-pulp) '()]
      [(equal? (car (car h-pulp)) loc)
       (cons (cons loc (delete-prop-val (cdr (car h-pulp)) prop)) (cdr h-pulp))]
      [ else
        (cons (car h-pulp) (heap-delete-cell (cdr h-pulp) loc prop))]))
   (let ((new-heap-pulp (delete-cell-pulp (unbox heap) loc prop)))
     (set-box! heap new-heap-pulp)))

(define (delete-prop-val prop-val-list prop)
  (cond [(null? prop-val-list) '()]
        [(equal? (car (car prop-val-list)) prop) (cdr prop-val-list)]
        [ else (cons (car prop-val-list) (delete-prop-val (cdr prop-val-list) prop))]))

;;
;; Heap cell
;;
(define (cell loc prop val)
  (list loc prop val))

;;
;; Construct a heap from given cells
;;
(define (heap . cells)
  (let ((new-heap (make-heap)))
    (let loop ((cells cells))
      (when (not (null? cells))
        (let ((cur-cell (first cells)))
          (mutate-heap new-heap (first cur-cell) (second cur-cell) (third cur-cell))
          (loop (cdr cells)))))
    new-heap))

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

(define (is-llist? l)
  (and
   (list? l)
   (eq? (first l) 'jsil-list)
   (foldl (lambda (x ac)
             (and ac (literal? x)))
           #t
           (cdr l))
  )
)

(define (is-a-list? l)
  (and
   (list? l)
   (eq? (first l) 'jsil-list)
  )
)

(define (make-jsil-list l)
  (cons 'jsil-list l))

(provide is-a-list? make-heap mutate-heap heap-get heap-delete-cell heap cell get-new-loc make-jsil-list heap-delete-object) ;; heap-contains?


;; stores - my stuff
;;(define (make-store)
;;  (make-hash)) 

;;(define (store-get store var)
;;  (hash-ref store var))

;;(define (mutate-store store var val)
;;  (hash-set! store var val))
  

;; stores - Julian Dolby
(define (make-store)
  (box '()))

(define (store-get store var)
  (lht-ref (unbox store) var))

(define (mutate-store store var val)
  (define (mutate-store-aux store var val)
    (cond ((null? store) (list (cons var val)))
          ((equal? (car (car store)) var)
           (cons (cons (car (car store)) val) (cdr store)))
          (#t
           (cons (car store) (mutate-store-aux (cdr store) var val)))))
  (let ((new-store-pulp (mutate-store-aux (unbox store) var val)))
    (set-box! store new-store-pulp)))

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

;; refs
(define (make-ref base field reftype)
  (list 'ref base field reftype))

(define (ref-base ref) (second ref))

(define (ref-field ref) (third ref))

(define (ref-type ref) (fourth ref))

(define (is-ref? arg)
  (and
   (list? arg)
   (not (null? arg))
   (equal? (first arg) 'ref)))

(provide make-ref ref-base ref-field ref-type)

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
       (proc (lht-ref program-pulp proc-name)))
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
  (define (proc-init-store-iter params args cur-store)
    (if (not (null? params))
        (cond
          [(null? args)
           (mutate-store cur-store (first params) jundefined)
           (proc-init-store-iter (rest params) args cur-store)]
          [else
           (mutate-store cur-store (first params) (first args))
           (proc-init-store-iter (rest params) (rest args) cur-store)])
        cur-store))
  (proc-init-store-iter (get-params proc) args (make-store)))

(define (args . lst)
  lst)

(define (body . lst)
  (cons 'body lst))

(define (ret-ctx . lst)
  (cons 'return lst))

(define (err-ctx . lst)
  (cons 'error lst))

(provide procedure which-pred eval_literal petar-get-fields get-fields heap-get-obj get-ret-var get-err-var get-ret-index get-err-index get-proc-name get-params get-cmd get-number-of-cmds proc-init-store args body ret-ctx err-ctx)

;;(define (heap-contains? heap loc prop)
;;  (not (equal? jempty (heap-get heap loc prop))))


;; heaps
;;(define (make-heap)
;;  (make-hash))

;;(define (mutate-heap heap loc prop val)
;;  (hash-set! heap (cons loc prop) val))

;;(define (heap-get heap loc prop)
;;  (hash-ref heap (cons loc prop)))

;;(define (heap-delete-cell heap loc prop)
;;  (when (heap-contains? heap loc prop)
;;      (hash-remove! heap (cons loc prop))))
      
;;(define (heap-contains? heap loc prop)
;;  (hash-has-key? heap (cons loc prop)))