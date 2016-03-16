#lang racket

;; constants
(define empty 'emtpy)
(define jnull 'null)
(define jundefined 'undefined)
(define jtrue 'true)
(define jfalse 'jfalse)
;;
;; special properties
(define protop 'proto)

;; heaps
(define (make-heap)
  (make-hash))

(define (mutate-heap heap loc prop val)
  (hash-set! heap (cons loc prop) val))

(define (heap-get heap loc prop)
   (hash-ref heap (cons loc prop)))

(define (heap-contains? heap loc prop)
  (hash-has-key? heap (cons loc prop)))

;; store
(define (make-store)
  (make-hash))

(define (mutate-store store var val)
  (hash-set! store var val))

(define (store-get store var)
  (hash-ref store var))

;; refs
(define (make-ref base field reftype)
  (list base field reftype))

(define (ref-base ref) (first ref))

(define (ref-field ref) (second ref))

(define (ref-type ref) (third ref))

;; programs and procedures  
(define (program . procs)
  (let ((procs-table (make-hash))
        (found-main #f))
    (map (lambda (proc)
           (let ((proc-name (get-proc-name proc)))
             (hash-set! procs-table proc-name proc)
             (when (eq? proc-name 'main)
               (set! found-main #t))))
         procs)
    (if found-main
        procs-table
        (error "Missing main"))))

(define (get-proc program proc-name)
  (hash-ref program proc-name))

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
         (mutate-store cur-store (first params) jempty)
         (proc-init-store-iter (rest params) args cur-store)]
        [else
         (mutate-store cur-store (first params) (first args))
         (proc-init-store-iter (rest params) (rest args) cur-store)])
      cur-store))
  (proc-init-store-iter (get-params proc) args (make-store)))
  
(define (to-interp-bool jbool)
  (cond
    [(eq? jbool jtrue) #t]
    [(eq? jbool jfalse) #f]))

(define (to-interp-op op)
  (cond
    [(eq? op '+) +]
    [(eq? op '-) -]))

    


