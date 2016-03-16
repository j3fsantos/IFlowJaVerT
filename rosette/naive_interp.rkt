#lang racket

(define (run-bcmd prog bcmd heap store)
  (let ((cmd-type (first cmd)))
    (cond
      ;; ('skip)
      [(eq' cmd-type 'skip) empty]
      ;;
      ;; ('mutation e1 e2 e3)
      [(eq' cmd-type 'mutation)
       (let* ((loc-expr (second cmd))
              (prop-expr (third cmd))
              (rhs-expr (fourth cmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (rhs-val (run-expr rhs-expr store)))
         (mutate-heap heap loc-val prop-val rhs-val)
         rhs-val)]
      ;;
      ;; ('var_assign lhs-var e)
      [(eq' cmd-type 'var_assign)
       (let* ((lhs-var (second cmd))
              (rhs-expr (third cmd))
              (rhs-val (run-expr rhs-expr store)))
         (mutate-store store lhs-var rhs-val)
         rhs-val)]
      ;;
      ;; ('new lhs-var)
      [(eq' cmd-type 'new)
       (let ((lhs-var (second cmd))
             (loc-val (get-new-loc heap)))
         (mutate-store store lhs-var loc-val)
         (mutate-heap heap loc-val protop jnull)
         loc-val)]
      ;;
      ;; ('hasField lhs-var e1 e2)
      [(eq' cmd-type 'hasField)
       (let* ((lhs-var (second cmd))
              (loc-expr (third cmd))
              (prop-expr (fourth cmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (contains (heap-contains? heap loc-val prop-val)))
         (mutate-store store lhs-var (to-interp-bool contains))
         (to-interp-bool contains))] 
      ;;
      ;; ('lookup lhs-var e1 e2)
      [(eq' cmd-type 'lookup)
       (let* ((lhs-var (second cmd))
              (loc-expr (third cmd))
              (prop-expr (fourth cmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (result (heap-get heap loc-val prop-val)))
         (mutate-store store lhs-var result)
         result)] 
      ;;
      ;; ('delete lhs-var e1 e2)
      [(eq' cmd-type 'delete)
       (let* ((lhs-var (second cmd))
              (loc-expr (third cmd))
              (prop-expr (fourth cmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store)))
         (delete-cell heap loc-val prop-val)
         (mutate-store store lhs-var (to-interp-bool #t))
         (to-interp-bool #t))]
      ;;
      ;; ('proto_field lhs-var e1 e2)
      [(eq' cmd-type 'proto_field)
       (let* ((lhs-var (second cmd))
              (loc-expr (third cmd))
              (prop-expr (fourth cmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (result (proto-lookup-val heap loc prop)))
         (mutate-store store lhs-var result)
         result)]
      ;;
      ;; ('proto_obj lhs-var e1 e2)
      [(eq' cmd-type 'proto_obj)
       (let* ((lhs-var (second cmd))
              (loc-expr (third cmd))
              (prop-expr (fourth cmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (result (proto-lookup-obj heap loc prop)))
         (mutate-store store lhs-var result)
         result)]
      ;;
      [else (error "Illegal Basic Command")])))

(define (run-cmds-iter prog proc-name heap store cur-index)
  (let* ((proc (get-proc prog proc-name))
         (cmd (get-cmd proc cur-index))
         (cmd-type (first cmd)))
    (cond
      ;;
      ;; ('goto i)
      [(and (eq' cmd-type 'goto) (= (length cmd) 2))
       (run-cmds-iter prog proc_name heap store (second cmd))]
      ;;
      ;; ('goto e i j)
      [(and (eq' cmd-type 'goto) (= (length cmd) 3))
       (let* ((expr (second cmd))
              (then-label (third cmd))
              (else-label (fourth cmd))
              (expr-val (run-expr expr store)))
         (cond
           [(eq? expr-val jtrue) (run-cmds-iter prog proc-name heap store then-label)]
           [(eq? expr-val jfalse) (run-cmds-iter prog proc-name heap store else-label)]
           [else (error "Illegal Conditional Goto Guard")]))]
      ;;
      ;; ('call lhs-var e (e1 ... en) i)
      [(eq' cmd-type 'call)
       (let* ((lhs-var (second cmd))
              (proc-name-expr (third cmd))
              (arg-exprs (fourth cmd))
              (err-label (fifth cmd))
              (proc-name (run-expr proc-name-expr store))
              (arg-vals (map (lambda (expr) (run-expr prop-expr store)) arg-exprs)))
         (let ((outcome (run-proc prog proc-name heap arg-vals)))
           (cond
             [(eq? (first outcome) 'error)
              (run-cmds-iter prog proc-name heap store err-label)]
             [(eq? (first outcome) 'normal)
              (run-cmds-iter prog proc-name heap store (+ cur-index 1))]
             [else (error "Illegal Procedure Outcome")])))]
      ;;
      ;; basic command
      [else
       (let* ((cur-outcome (run-bcmd prog cmd heap store))
              (ret-var (get-ret-var proc))
              (err-var (get-err-var proc)))
         (cond
           [(eq? cur-index (get-ret-index proc)) (cons 'normal (store-get store ret-var))]
           [(eq? cur-index (get-err-index proc)) (cons 'err (store-get store err-var))]
           [else (run-cmds-iter prog proc-name heap store (+ cur-index 1))]))])))
           
(define (run-expr expr store)
  (cond
    [(literal? expr) expr]
    [(var? expr) (store-get store expr)]
    [(list? expr)
     (cond
       ;; 
       ;;('ref e1 e2 e3)
       [(eq? (first expr) 'ref)
        (let* ((base-expr (second expr))
               (field-expr (third expr))
               (type-expr (fourth expr))
               (base-val (run-expr base-expr store))
               (field-val (run-expr field-expr store))
               (type-val (run-expr type-expr store)))
          (make-ref base-val field-val type-val))]
       ;;
       ;; ('base e)
       [(eq? (first expr) 'base) 
        (let* ((ref-expr (second expr))
               (ref-val (run-expr ref-expr store)))
          (ref-base ref-val))]
       ;;
       ;; ('field e)
       [(eq? (first expr) 'field) 
        (let* ((ref-expr (second expr))
               (ref-val (run-expr ref-expr store)))
          (ref-field ref-val))]
       ;;
       ;; ('typeof e)
       [(eq? (first expr) 'field) 
        (let* ((ref-expr (second expr))
               (ref-val (run-expr ref-expr store)))
          (ref-type ref-val))]
       ;;
       ;; (binop e e)
       [(= (length expr) 3) 
        (let* ((binop (to-interp-op (first expr)))
               (larg (run-expr (second expr) store))
               (rarg (run-expr (third expr) store)))
          (apply-binop binop larg rarg))]
       ;;
       ;; (unop e)
       [(= (length expr) 2) 
        (let* ((unop (to-interp-op (first expr)))
               (arg (run-expr (second expr) store)))
          (apply-unop unop arg))])]))

(define (run-proc prog proc-name heap arg-vals)
  (let* ((proc (get-proc prog proc-name))
         (initial-store (proc-init-store proc arg-vals)))
    (run-cmds-iter prog proc-name heap initial-store 0)))

(define (proto-lookup-obj heap loc prop)
  (cond
    [(eq? loc jnull) jempty]
    [(heap-contains? heap loc prop) loc]
    [else
     (let ((loc-proto (heap-get heap loc protop)))
       (proto-lookup-obj heap loc-proto prop))]))

(define (proto-lookup-val heap loc prop)
  (let ((proto-prop-loc (proto-lookup-obj heap loc prop)))
    (if (eq? proto-prop-loc jempty)
        jundefined
        (heap-get heap proto-prop-loc prop))))
        
    

