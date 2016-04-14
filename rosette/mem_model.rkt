#lang s-exp rosette

;; 
;; literals - constants
;;
(define jempty '$$empty)
(define jnull '$$null)
(define jundefined '$$undefined)
;; types
(define boolean-type '$$boolean_type)
(define number-type '$$string_type)
(define string-type '$$number_type)
(define obj-type '$$object_type)
(define ref-a-type '$$reference_type)
(define ref-v-type '$$v_reference_type)
(define ref-o-type '$$o_reference_type)

(define jsil-constants
  (let ((table (mutable-set)))
    (set-add! table jempty)
    (set-add! table jnull)
    (set-add! table jundefined)
    (set-add! table boolean-type)
    (set-add! table number-type)
    (set-add! table string-type)
    (set-add! table obj-type)
    (set-add! table ref-a-type)
    (set-add! table ref-v-type)
    (set-add! table ref-o-type)
    table))

(define (literal? val)
  (or
   (number? val)
   (boolean? val)
   (string? val)
   (set-member? jsil-constants val)
   (is-loc? val)))

;; Type operations
(define (jsil-type-of val)
  (cond
    ((number? val) boolean-type)
    ((string? val) string-type)
    ((boolean? val) boolean-type)
    ((is-loc? val) obj-type)
    ((is-ref? val) (ref-type val))
    ((eq? val jnull) jnull)
    ((eq? val jundefined) jundefined)
    ((eq? val empty) jempty)
    (#t (error (format "Wrong argument to typeof: ~a" val)))))

(define (jsil-subtype type1 type2)
  (println (format "computing a subtype with types ~a and ~a" type1 type2))
  (and
   (eq? ref-a-type type2)
   (or (eq? ref-v-type type1)
       (eq? ref-o-type type1))))

;; special properties
(define protop "proto")

(provide jempty jnull jundefined literal? protop jsil-type-of ref-v-type ref-o-type)

;;
;; binary operators 
;; missing: shift left, shift right, unsigned shift right
;;

;; Shift left and right
(define (shl n m) (arithmetic-shift n    m))
(define (shr n m) (arithmetic-shift n (- m)))

(define operators-table
  (let* ((table-aux (make-hash))
    (add (lambda (jsil-op interp-op) (hash-set! table-aux jsil-op interp-op))))
    (add 'and (lambda (x y) (and x y)))
    (add 'or  (lambda (x y) (or  x y)))
    (add '+ +)
    (add '- -)
    (add '* *)
    (add '/ /)
    (add '~ bitwise-not)
    (add '& bitwise-and)   
    (add '@ bitwise-ior)
    (add '<< shl)
    (add '>> shr)
    (add '^ string-append)
    (add 'not not)
    (add 'num_to_string number->string)
    (add 'string_to_num string->number)
    (add '= eq?)
    (add '< <)
    (add '> >)
    (add '>= >=)
    (add '<= <=)
    (add 'equal? equal?)
    (add '<: jsil-subtype)
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

(define (find-prop-val prop-val-lst prop)
  (cond
    [(null? prop-val-lst) jempty]
    [(equal? (car (car prop-val-lst)) prop) (cdr (car prop-val-lst))]
    [ else (find-prop-val (cdr prop-val-lst) prop)]))

(define (heap-contains? heap loc prop)
  (not (equal? jempty (heap-get heap loc prop))))
     
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
        [ else (cons (cons prop-val-list) (delete-prop-val (cdr prop-val-list) prop))]))

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
  (and
   (symbol? loc)
   (eq? (substring (symbol->string loc) 0 2) "$l")))

(provide make-heap mutate-heap heap-get heap-delete-cell heap-contains? heap cell get-new-loc)

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
        (or
         (eq? (string-ref expr-str 0) #\r)
         (and (> expr-str-len 2) (eq? (substring expr-str 0 2) "x_"))
         (and (> expr-str-len 4) (eq? (substring expr-str 0 4) "arg_"))))))

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
         (ret-var (second ret-info))
         (ret-label (third ret-info))
         (err-var (second err-info))
         (err-label (third err-info)))
    (map (lambda (cmd)
           (vector-set! cmds-vec cur-index cmd)
           (set! cur-index (+ cur-index 1)))
         cmds-list)
    (list proc-name proc-args (list ret-var ret-label err-var err-label) cmds-vec)))

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

(provide procedure get-ret-var get-err-var get-ret-index get-err-index get-proc-name get-params get-cmd proc-init-store args body ret-ctx err-ctx)
