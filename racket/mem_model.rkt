#lang s-exp rosette

;; 
;; literals - constants
;;
(define jempty     '$$empty)
(define jnull      '$$null)
(define jundefined '$$undefined)

;; types
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

(define jsil-constants
  (let ((table (mutable-set)))
    (set-add! table jempty)
    (set-add! table jnull)
    (set-add! table jundefined)
    (set-add! table undefined-type)
    (set-add! table null-type)
    (set-add! table empty-type)
    (set-add! table boolean-type)
    (set-add! table number-type)
    (set-add! table string-type)
    (set-add! table obj-type)
    (set-add! table ref-a-type)
    (set-add! table ref-v-type)
    (set-add! table ref-o-type)
    (set-add! table list-type)
    table))

;; math constants
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

(define jsil-math-constants
  (let ((table (mutable-set)))
    (set-add! table mc-minval)
    (set-add! table mc-maxval)
    (set-add! table mc-random)
    (set-add! table mc-pi)
    (set-add! table mc-e)
    (set-add! table mc-ln10)
    (set-add! table mc-ln2)
    (set-add! table mc-log2e)
    (set-add! table mc-log10e)
    (set-add! table mc-sqrt12)
    (set-add! table mc-sqrt2)
    table))

;; evaluation
(define (literal? val)
  (or
   (number? val)
   (boolean? val)
   (string? val)
   (set-member? jsil-constants val)
   (set-member? jsil-math-constants val)
   (is-loc? val)
   (is-llist? val)
   (is-ref? val)
  )
)

(define (eval_literal lit)
  (if (set-member? jsil-math-constants lit)
      (cond
        ((eq? lit mc-minval) 5e-324)
        ((eq? lit mc-maxval) 1.7976931348623158e+308)
        ((eq? lit mc-random) (random))
        ((eq? lit mc-pi)       pi)
        ((eq? lit mc-e)      (exp 1.))
        ((eq? lit mc-ln10)   (log 10.))
        ((eq? lit mc-ln2)    (log 2.))
        ((eq? lit mc-log2e)  (/ 1 (log 2.)))
        ((eq? lit mc-log10e) (/ 1 (log 10.)))
        ((eq? lit mc-sqrt12) (sqrt 0.5))
        ((eq? lit mc-sqrt2)  (sqrt 2.))
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

(define (jsil-subtype type1 type2)
  (or 
   (eq? type1 type2) 
   (and
    (eq? ref-a-type type2)
    (or (eq? ref-v-type type1)
        (eq? ref-o-type type1)))))

;; special properties
(define protop "@proto")
(define larguments '$larguments)
(define parguments "args")

(provide jempty jnull jundefined literal? protop larguments parguments jsil-type-of ref-v-type ref-o-type)

;;
;; binary operators 
;; missing: shift left, shift right, unsigned shift right
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
              (let* (
                     (two-32 (expt 2 32))
                     (two-31 (expt 2 31))
                     (pos-int (* (sgn num) (floor (abs num))))
                     (smod (modulo pos-int two-32))
                    )
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
              (let* (
                     (two-16 (expt 2 16))
                     (pos-int (* (sgn num) (floor (abs num))))
                     (smod (modulo pos-int two-16))
                    )
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
              (let* (
                     (two-32 (expt 2 32))
                     (pos-int (* (sgn num) (floor (abs num))))
                     (smod (modulo pos-int two-32))
                    )
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
  (let* (
          (lhs-32 (jsil_num_to_uint_32 lhs))
          (rhs-32 (jsil_num_to_uint_32 rhs))
        )
    (shr (inexact->exact (truncate lhs-32)) (inexact->exact (truncate rhs-32)))
  )
)

(define (jsil-number-to-string n)
  (cond
    ((integer? n) (int-to-str n))
    (#t (number->string n))))

(define operators-table
  (let* ((table-aux (make-hash))
         (add (lambda (jsil-op interp-op) (hash-set! table-aux jsil-op interp-op))))
    ;; What does this mean for symbolic values?
    (add '= eq?)
    (add '< <)
    (add '<= <=)
    (add '<s string<?)
    (add '+ +)
    (add '- -)
    (add '* *)
    (add '/ /)
    (add '% modulo)
    (add '<: jsil-subtype)
    (add 'concat string-append)
    (add '++ (lambda (x y) (append x (cdr y))))
    (add 'and (lambda (x y) (and x y)))
    (add 'or  (lambda (x y) (or  x y)))
    (add '& (lambda (x y) (bitwise-and (inexact->exact (truncate x)) (inexact->exact (truncate y)))))
    (add '^ (lambda (x y) (bitwise-xor (inexact->exact (truncate x)) (inexact->exact (truncate y)))))
    (add '<< (lambda (x y) (shl (inexact->exact (truncate x)) (inexact->exact (truncate y)))))
    (add '>> (lambda (x y) (shr (inexact->exact (truncate x)) (inexact->exact (truncate y)))))
    (add ':: (lambda (x y)
               (if (eq? x '(jsil-list))
                y
                (append (list 'jsil-list x) (cdr y)))))
    (add '** expt)
    (add 'm_atan2 (lambda (x y) (atan y x)))
    (add 'bor (lambda (x y) (bitwise-ior (inexact->exact (truncate x)) (inexact->exact (truncate y)))))
    (add '>>> unsigned_right_shift)
    (add 'not not)
    (add 'num_to_string jsil-number-to-string)
    (add 'string_to_num jsil_string_to_number)
    (add '! (lambda (x) (bitwise-not (inexact->exact x))))
    (add 'is_primitive (lambda (x) (or (number? x) (string? x) (boolean? x) (eq? x jnull) (eq? x jundefined))))
    (add 'length (lambda (x) (if (is-llist? x) (- (length x) 1) (string-length x))))
    (add 'car (lambda (x) (car (cdr x))))
    (add 'cdr (lambda (x) (cons 'jsil-list (cdr (cdr x)))))
    (add 'm_abs abs)
    (add 'm_acos acos)
    (add 'm_asin asin)
    (add 'm_atan atan)
    (add 'm_cos cos)
    (add 'm_sin sin)
    (add 'm_tan tan)
    (add 'm_sgn sgn)
    (add 'm_sqrt sqrt)
    (add 'm_exp exp)
    (add 'm_log log)
    (add 'm_ceil ceiling)
    (add 'm_floor floor)
    (add 'm_round round)
    (add 'num_to_int jsil_num_to_int)
    (add 'num_to_int32 jsil_num_to_int_32)
    (add 'num_to_uint16 jsil_num_to_uint_16)
    (add 'num_to_uint32 jsil_num_to_uint_32)
    table-aux))

(define (to-interp-op op)
  (cond
    [(hash-has-key? operators-table op) (hash-ref operators-table op)]
    [else (error "Operator not supported" op)]))

(define (apply-binop op arg1 arg2)
  (apply op (list arg1 arg2)))

(define (apply-unop op arg)
  (apply op (list arg)))

(provide to-interp-op apply-binop apply-unop)

;; heaps that can be handled by rosette

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

(define (heap-get heap loc prop)
  (let loop ((heap-pulp (unbox heap)))
    (cond
      [(null? heap-pulp) jempty]
      [(equal? (car (car heap-pulp)) loc)
       (find-prop-val (cdr (car heap-pulp)) prop)]
      [ else (loop (cdr heap-pulp))])))

(define (heap-get-obj heap loc)
  (let loop ((heap-pulp (unbox heap)))
    (cond
      [(null? heap-pulp) jempty]
      [(equal? (car (car heap-pulp)) loc)
       (cdr (car heap-pulp))]
      [ else (loop (cdr heap-pulp))])))

(define (find-prop-val prop-val-lst prop)
  (cond
    [(null? prop-val-lst) jempty]
    [(equal? (car (car prop-val-lst)) prop) (cdr (car prop-val-lst))]
    [ else (find-prop-val (cdr prop-val-lst) prop)]))


(define (get-fields heap loc)
  (let loop ((heap-pulp (unbox heap)))
    (cond
      [(null? heap-pulp) jempty]
      [(equal? (car (car heap-pulp)) loc)
       (let* ((obj (cdr (car heap-pulp)))
              (props (foldl (lambda (x ac)
                       (if (is-a-list? (cdr x))
                       (append ac (list (car x)))
                       ac)
                       )
                       (list ) obj))
              (sprops (sort props string<?)))
         ;; (println (format "Internal get-fields: igf (~a) = ~a" loc sprops))
         sprops)]
      [ else (loop (cdr heap-pulp))])))
     
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
         (eq? (substring (symbol->string loc) 0 2) "$l")))))

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

(provide is-a-list? make-heap mutate-heap heap-get heap-delete-cell heap cell get-new-loc make-jsil-list) ;; heap-contains?

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
  (lookup var (unbox store)))

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


;; auxiliary functions
(define (lookup x lst-param)
  (letrec ((iter
            (lambda (lst)
              (cond ((null? lst) null)
                    ((equal? (car (car lst)) x) (cdr (car lst)))
                    (#t (iter (cdr lst)))))))
    (iter lst-param)))



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

;; programs and procedures  
(define (program . procs)
  (let ((procs-table (make-hash)))
    (map (lambda (proc)
           (let ((proc-name (get-proc-name proc)))
             (hash-set! procs-table proc-name proc)))
         procs)
    procs-table))

(define (get-proc program proc-name)
  (if (hash-has-key? program proc-name)
      (hash-ref program proc-name)
      (error (format "Error: procedure ~a is missing" proc-name))))

(define (has-proc? program proc-name)
  (hash-has-key? program proc-name))

(define (get-proc-names prog)
  (hash-values prog))

(define (add-proc program proc)
  (let ((proc-name (get-proc-name proc)))
    (if (hash-has-key? program (get-proc-name proc))
        (error (format "Error: procedure ~a is already defined" proc-name))
        (hash-set! program proc-name proc))))

(define (program-append prog1 prog2)
  (let ((procs2 (get-proc-names prog2)))
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

(provide procedure which-pred eval_literal get-fields heap-get-obj get-ret-var get-err-var get-ret-index get-err-index get-proc-name get-params get-cmd get-number-of-cmds proc-init-store args body ret-ctx err-ctx)

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