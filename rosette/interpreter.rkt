#lang s-exp rosette

(require (file "mem_model.rkt"))
(require (file "util.rkt"))

(define (run-bcmd prog bcmd heap store)
  (let ((cmd-type (first bcmd)))
    (cond
      ;; ('skip)
      [(eq? cmd-type 'skip) empty]
      ;;
      ;; ('h-assign e1 e2 e3)
      [(eq? cmd-type 'h-assign)
       (let* ((loc-expr (second bcmd))
              (prop-expr (third bcmd))
              (rhs-expr (fourth bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (rhs-val (run-expr rhs-expr store)))
         (mutate-heap heap loc-val prop-val rhs-val)
         rhs-val)]
      ;;
      ;; ('v-assign lhs-var e)
      [(eq? cmd-type 'v-assign)
       (let* ((lhs-var (second bcmd))
              (rhs-expr (third bcmd))
              (rhs-val (run-expr rhs-expr store)))
         (print rhs-expr)
         (print "you are a banana?")
         (print rhs-val)
         (mutate-store store lhs-var rhs-val)
         rhs-val)]
      ;;
      ;; ('new lhs-var)
      [(eq? cmd-type 'new)
       (let ((lhs-var (second bcmd))
             (loc-val (get-new-loc)))
         (mutate-store store lhs-var loc-val)
         (mutate-heap heap loc-val protop jnull)
         loc-val)]
      ;;
      ;; ('has-field lhs-var e1 e2)
      [(eq? cmd-type 'has-field)
       (let* ((lhs-var (second bcmd))
              (loc-expr (third bcmd))
              (prop-expr (fourth bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (contains (heap-contains? heap loc-val prop-val)))
         (mutate-store store lhs-var (to-jsil-bool contains))
         (to-jsil-bool contains))] 
      ;;
      ;; ('h-read lhs-var e1 e2)
      [(eq? cmd-type 'h-read)
       (let* ((lhs-var (second bcmd))
              (loc-expr (third bcmd))
              (prop-expr (fourth bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (result (heap-get heap loc-val prop-val)))
         (mutate-store store lhs-var result)
         result)] 
      ;;
      ;; ('h-delete lhs-var e1 e2)
      [(eq? cmd-type 'h-delete)
       (let* ((lhs-var (second bcmd))
              (loc-expr (third bcmd))
              (prop-expr (fourth bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store)))
         (heap-delete-cell heap loc-val prop-val)
         (mutate-store store lhs-var (to-jsil-bool #t))
         (to-jsil-bool #t))]
      ;;
      ;; ('proto-field lhs-var e1 e2)
      [(eq? cmd-type 'proto-field)
       (let* ((lhs-var (second bcmd))
              (loc-expr (third bcmd))
              (prop-expr (fourth bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (result (proto-lookup-val heap loc-val prop-val)))
         (mutate-store store lhs-var result)
         result)]
      ;;
      ;; ('proto-obj lhs-var e1 e2)
      [(eq? cmd-type 'proto-obj)
       (let* ((lhs-var (second bcmd))
              (loc-expr (third bcmd))
              (prop-expr (fourth bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (result (proto-lookup-obj heap loc-val prop-val)))
         (mutate-store store lhs-var result)
         result)]
      ;;
      [else (print cmd-type) (error "Illegal Basic Command")])))

(define (run-cmds-iter prog proc-name heap store cur-index)
  (let* ((proc (get-proc prog proc-name))
         (cmd (get-cmd proc cur-index))
         (cmd-type (first cmd)))
    (cond
      ;;
      ;; ('goto i)
      [(and (eq? cmd-type 'goto) (= (length cmd) 2))
       (run-cmds-iter prog proc-name heap store (second cmd))]
      ;;
      ;; ('goto e i j)
      [(and (eq? cmd-type 'goto) (= (length cmd) 4))
       (let* ((expr (second cmd))
              (then-label (third cmd))
              (else-label (fourth cmd))
              (expr-val (run-expr expr store)))
         (cond
           [(eq? expr-val #t) (run-cmds-iter prog proc-name heap store then-label)]
           [(eq? expr-val #f) (run-cmds-iter prog proc-name heap store else-label)]
           [else (error "Illegal Conditional Goto Guard")]))]
      ;;
      ;; ('call lhs-var e (e1 ... en) i)
      [(eq? cmd-type 'call)
       (let* ((lhs-var (second cmd))
              (proc-name-expr (third cmd))
              (arg-exprs (fourth cmd))
              (err-label (fifth cmd))
              (proc-name (run-expr proc-name-expr store))
              (arg-vals (map (lambda (expr) (run-expr expr store)) arg-exprs)))
         (let ((outcome (run-proc prog proc-name heap arg-vals)))
           (cond
             [(eq? (first outcome) 'error)
              (mutate-store store lhs-var (second outcome))
              (run-cmds-iter prog proc-name heap store err-label)]
             [(eq? (first outcome) 'normal)
              (mutate-store store lhs-var (second outcome))
              (run-cmds-iter prog proc-name heap store (+ cur-index 1))]
             [else (error "Illegal Procedure Outcome")])))]
      ;;
      ;; basic command
      [else
       (let* ((cur-outcome (run-bcmd prog cmd heap store))
              (ret-var (get-ret-var proc))
              (err-var (get-err-var proc)))
         (cond
           [(eq? cur-index (get-ret-index proc)) (list 'normal (store-get store ret-var))]
           [(eq? cur-index (get-err-index proc)) (list 'err (store-get store err-var))]
           [else (run-cmds-iter prog proc-name heap store (+ cur-index 1))]))])))


(define (run-cmds prog cmds heap store cur-index)
  (if (or (>= cur-index (vector-length cmds))
          (< cur-index 0))
      (begin
        (print cur-index)
        (error "Illegal Index"))
      (let* ((cmd (vector-ref cmds cur-index))
             (cmd-type (first cmd)))
        (cond
          ;;
          ;; ('goto i)
          [(and (eq? cmd-type 'goto) (= (length cmd) 2))
           (run-cmds prog cmds heap store (+ cur-index (second cmd)))]
          ;;
          ;; ('goto e i j)
          [(and (eq? cmd-type 'goto) (= (length cmd) 4))
           (let* ((expr (second cmd))
                  (then-index (third cmd))
                  (else-index (fourth cmd))
                  (expr-val (run-expr expr store)))
             (cond
               [(eq? expr-val #t) (run-cmds prog cmds heap store (+ cur-index then-index))]
               [(eq? expr-val #f) (run-cmds prog cmds heap store (+ cur-index else-index))]
               [else (print expr-val) (error "Illegal Conditional Goto Guard")]))]
          ;;
          ;; ('call lhs-var e (e1 ... en) i)
          [(eq? cmd-type 'call)
           (let* ((lhs-var (second cmd))
                  (proc-name-expr (third cmd))
                  (arg-exprs (fourth cmd))
                  (err-index (fifth cmd))
                  (proc-name (run-expr proc-name-expr store))
                  (arg-vals (map (lambda (expr) (run-expr expr store)) arg-exprs)))
             (let ((outcome (run-proc prog proc-name heap arg-vals)))
               (cond
                 [(eq? (first outcome) 'error)
                  (mutate-store store lhs-var (second outcome))
                  (run-cmds prog cmds heap store (+ cur-index err-index))]
                 [(eq? (first outcome) 'normal)
                  (mutate-store store lhs-var (second outcome))
                  (run-cmds prog cmds heap store (+ cur-index 1))]
                 [else (error "Illegal Procedure Outcome")])))]
          ;;
          ;; basic command
          [else
           (let* ((cur-outcome (run-bcmd prog cmd heap store)))
             (cond
               [(= cur-index (- (vector-length cmds) 1)) cur-outcome]
               [else (run-cmds prog cmds heap store (+ cur-index 1))]))]))))

(define (run-expr expr store)
  (print (symbolic? expr))
  (cond
    ;;
    ;; literals
    [(literal? expr) expr]
    ;;
    ;; variables
    [(var? expr) (store-get store expr)]
    ;;
    ;; symbolic value
    [(symbolic? expr) expr]
    ;;
    ;; 
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
       [(eq? (first expr) 'typeof) 
        (let* ((ref-expr (second expr))
               (ref-val (run-expr ref-expr store)))
          (ref-type ref-val))]
       ;;
       ;; (make-symbol symbol-type)
       [(eq? (first expr) 'make-symbol)
        (if (eq? (second expr) 'number)
            (make-number-symbol)
            (make-string-symbol))]
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

(define (run-program prog heap)
  (run-proc prog "main" heap '()))
  
(provide run-program run-proc run-cmds program procedure heap cell store args body ret-ctx err-ctx jempty jnull jundefined jtrue jfalse protop)

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


  