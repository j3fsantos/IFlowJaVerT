#lang s-exp rosette

(require (file "mem_model.rkt"))
(require (file "wp.rkt"))
(require (file "util.rkt"))

;;
;; SSkip      ()                  'skip       DONE
;; Assignment (var, expr)         'v-assign   DONE
;; SNew       (var)               'new        DONE
;; SLookup    (var, loc, field)   'h-read     DONE
;; SMutation  (loc, field, value) 'h-assign   DONE
;; SDelete    (loc, field)        'h-delete   DONE
;; SHasField  (var, loc, field)   'has-field  DONE
;; SGetFields (var, loc)          'get-fields 
;; SArguments (var)               'arguments
;;
;; +
;;
;; 'assume
;; 'assert
;; 'discharge
;;
(define (run-bcmd prog bcmd heap store)
  (let ((cmd-type (first bcmd)))
    (cond
      ;;
      ;; ('skip)
      [(eq? cmd-type 'skip) empty]
      ;;
      ;; ('discharge)
      [(eq? cmd-type 'discharge) (jsil-discharge)]
      ;;
      ;; ('h-assign e1 e2 e3)
      [(eq? cmd-type 'h-assign)
       (let* ((loc-expr (second bcmd))
              (prop-expr (third bcmd))
              (rhs-expr (fourth bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (rhs-val (run-expr rhs-expr store)))
         (println (format "Mutation: [~a, ~a] = ~a" loc-val prop-val rhs-val))
         (mutate-heap heap loc-val prop-val rhs-val)
         rhs-val)]
      ;;
      ;; ('v-assign lhs-var e)
      [(eq? cmd-type 'v-assign)
       (let* ((lhs-var (second bcmd))
              (rhs-expr (third bcmd))
              (rhs-val  (run-expr rhs-expr store)))
         (println (format "Assignment: ~a = ~a" lhs-var rhs-val))
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
         (mutate-store store lhs-var contains) ;; (to-jsil-bool contains))
         contains)] ;; (to-jsil-bool contains))]
      ;;
      ;; ('get-fields lhs-var e1 e2)
      [(eq? cmd-type 'get-fields)
       (let* ((lhs-var (second bcmd))
              (loc-expr (third bcmd))
              (loc-val (run-expr loc-expr store))
              (obj (heap-get-obj heap loc-val))
              (props (foldl (lambda (x ac)
                       (displayln (cdr x))
                       (if (is-a-list? (cdr x))
                       (append ac (list (car x)))
                       ac)
                       )
                       (list ) obj))
              (sprops (sort props string<?))
             )
         (mutate-store store lhs-var (cons 'jsil-list sprops)) ;; (to-jsil-bool contains))
         (cons 'jsil-list sprops))] ;; (to-jsil-bool contains))]
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
      ;; ('arguments lhs-var)
      [(eq? cmd-type 'arguments)
       (let* ((lhs-var (second bcmd))
              (result (heap-get heap larguments parguments)))
         ;;(displayln "you called arguments")
         ;;(displayln result) 
         (mutate-store store lhs-var result)
         result)] 
      ;;
      ;; ('h-delete lhs-var e1 e2)
      [(eq? cmd-type 'h-delete)
       (let* (
              (loc-expr (second bcmd))
              (prop-expr (third bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store)))
         (heap-delete-cell heap loc-val prop-val)
         #t)] ;; (to-jsil-bool #t))]
      ;;
      [else (print cmd-type) (error "Illegal Basic Command")])))

(define goto-limit 10)

(define goto-stack (make-parameter '()))

(define (count-goto proc-name cur-index)
  (let ((key (cons proc-name cur-index)))
    ;; (print (goto-stack))
    (count (lambda (x) (equal? x key)) (goto-stack))))

(define (kill x)
  (letrec ((iter (lambda (l)
		   (assert (not (car l)))
		   (cond ((not (null? (cdr l)))
			  (iter (cdr l)))))))
    (iter (union-guards x))))


(define (find-prev-phi-cmd proc cur-index)
  (cond
    ((< cur-index 0) (error "Misplaced PSI node - every PSI node must have a PHI predecessor"))
    ((eq? (first (get-cmd proc cur-index)) 'v-phi-assign) cur-index)
    ((eq? (first (get-cmd proc cur-index)) 'v-psi-assign)
     (find-prev-phi-cmd proc (- cur-index 1)))
    (#t (error "A Psi node must have always have a PHI node between itself and the other commands"))))

(define (compute-next-prev proc cur-index prev-index)
  (cond
    ((eq? (first (get-cmd proc (+ cur-index 1))) 'v-psi-assign) prev-index)
    (#t cur-index)))

(define (run-cmds-iter prog proc-name heap store cur-index prev-index)
  (let* ((proc (get-proc prog proc-name))
         (cmd (get-cmd proc cur-index))
         (cmd-type (first cmd)))
    ;; (displayln cmd)
    ;; (println (format "Running the command ~a" cmd))
    (cond
      ;;
      ;; ('print e) 
      [(eq? cmd-type 'print)
       (let* ((expr (second cmd))
              (expr-val (run-expr expr store)))
         (println (format "Program Print:: ~a" expr-val))
         (run-cmds-iter prog proc-name heap store (+ cur-index 1) cur-index))]
      ;;
      ;; ('goto i)
      [(and (eq? cmd-type 'goto) (= (length cmd) 2))
       (run-cmds-iter prog proc-name heap store (second cmd) cur-index)]
      ;;
      ;; ('goto e i j)
      [(and (eq? cmd-type 'goto) (= (length cmd) 4))
       (let* ((expr (second cmd))
              (then-label (third cmd))
              (else-label (fourth cmd))
              (expr-val (run-expr expr store)))
         (parameterize ([goto-stack
                         (cons (cons proc-name cur-index) (goto-stack))])
           ;; (print expr-val)
           (cond
             [(and (symbolic? expr-val)
                   (> (count-goto proc-name cur-index) goto-limit))
              (kill expr-val)]
             
             [(eq? expr-val #t)
              (run-cmds-iter prog proc-name heap store then-label cur-index)]
             
             [(eq? expr-val #f)
              (run-cmds-iter prog proc-name heap store else-label cur-index)]
             
             [else
              (error "Illegal Conditional Goto Guard")])))]
      ;;
      ;; ('v-phi-assign x v1 v2 ... vn)
         [(eq? cmd-type 'v-phi-assign)
         (let* ((lhs-var (second cmd))
                (var-list (cddr cmd))
                (var-index (hash-ref wp (list proc-name prev-index cur-index)))
                (target-var (list-ref var-list var-index))
                (val (run-expr target-var store))
                (next-prev (compute-next-prev proc cur-index prev-index)))
          (mutate-store store lhs-var val)
          (run-cmds-iter prog proc-name heap store (+ cur-index 1) next-prev))]
      ;;
      ;;  ('v-psi-assign var var_1 var_2 ... var_n)
         [(eq? cmd-type 'v-psi-assign)
          (let* ((lhs-var (second cmd))
                 (var-list (cddr cmd))
                 (ac-cur-index (find-prev-phi-cmd proc (- cur-index 1)))
                 (var-index (hash-ref wp (list proc-name prev-index ac-cur-index)))
                 (target-var (list-ref var-list var-index))
                 (val (run-expr target-var store))
                 (next-prev (compute-next-prev proc cur-index prev-index)))
            (mutate-store store lhs-var val)
            (run-cmds-iter prog proc-name heap store (+ cur-index 1) next-prev))]
                              
      ;; ('call lhs-var e (e1 ... en) i)
      [(eq? cmd-type 'call)
       (let* ((lhs-var (second cmd))
              (proc-name-expr (third cmd))
              (arg-exprs (fourth cmd))
              (err-label (if (>= (length cmd) 5) (fifth cmd) -1))
              (call-proc-name (run-expr proc-name-expr store))
              (arg-vals (map (lambda (expr) (run-expr expr store)) arg-exprs)))
         (println (format "Procedure call: ~a (~a)" call-proc-name arg-vals))
         (let ((outcome (car (run-proc prog call-proc-name heap arg-vals))))
           ;;(display
            ;;(format "Finished running procedure ~a with arguments ~a and obtained the outcome ~a\n"
                  ;;  call-proc-name arg-vals outcome)) 
           (println (format "Procedure call: ~a = ~a (~a) returned ~a" lhs-var call-proc-name arg-vals outcome)) 
           (cond
             [(and (eq? (first outcome) 'err) (not (eq? err-label -1)))
              (mutate-store store lhs-var (second outcome))
              (run-cmds-iter prog proc-name heap store err-label cur-index)]

             [ (eq? (first outcome) 'err) (error "Procedures that throw errors must be called with error labels")]
             
             [(eq? (first outcome) 'normal)
              (mutate-store store lhs-var (second outcome))
              (run-cmds-iter prog proc-name heap store (+ cur-index 1) cur-index)]
             
             [else
              (display outcome)
              (error "Illegal Procedure Outcome")])))]
      ;;
      ;; basic command
      [else
       (let* ((cur-outcome (run-bcmd prog cmd heap store))
              (ret-var (get-ret-var proc))
              (err-var (get-err-var proc)))
         (cond
           [(eq? cur-index (get-ret-index proc))
            (list 'normal (store-get store ret-var))]
           [(eq? cur-index (get-err-index proc)) (list 'err (store-get store err-var))]
           [else (run-cmds-iter prog proc-name heap store (+ cur-index 1) cur-index)]))])))

(define (run-expr expr store)
  (cond
    ;;
    ;; literals
    [(literal? expr) (eval_literal expr)]
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
       ;;('ref-v e1 e2)
       [(eq? (first expr) 'ref-v)
        (let* ((base-expr (second expr))
               (field-expr (third expr))
               (base-val (run-expr base-expr store))
               (field-val (run-expr field-expr store)))
          (make-ref base-val field-val ref-v-type))]
       ;; 
       ;;('ref-o e1 e2)
       [(eq? (first expr) 'ref-o)
        (let* ((base-expr (second expr))
               (field-expr (third expr))
               (base-val (run-expr base-expr store))
               (field-val (run-expr field-expr store)))
          (make-ref base-val field-val ref-o-type))]
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
        (let* ((arg (second expr))
               (val (run-expr arg store)))
          (jsil-type-of val))]
       ;;
       ;; ('jsil-list l)
       [(eq? (first expr) 'jsil-list)
        (let* (
               (elist (cdr expr))
               (lexpr (foldl (lambda (x ac)
                        (append ac (list (run-expr x store))))
                        (list ) elist))
               )
          (cons 'jsil-list lexpr)
        )]
       ;;
       ;; ('nth l e)
       [(eq? (first expr) 'nth)
        (let* ((elist (second expr))
               (vlist (run-expr elist store))
               (eidx  (third expr))
               (vidx  (run-expr eidx store)))
          ;; branch-string!
          (if (list? vlist)
              (list-ref vlist (inexact->exact (+ vidx 1)))
              (make-string 1 (string-ref vlist (inexact->exact vidx))))
         )]
       ;;
       ;; (make-symbol-number symb-name)
       [(eq? (first expr) 'make-symbol-number)
        (make-number-symbol (second expr))]
       ;;
       ;; (make-symbol-string symb-name)
       [(eq? (first expr) 'make-symbol-string)
        (make-string-symbol (second expr))]
      ;;
      ;; ('assert e)
      [(eq? (first expr) 'assert)
       (let* ((expr-arg (second expr))
              (expr-val (run-expr expr-arg store)))
         (jsil-assert expr-val))]
      ;;
      ;; ('assume e)
      [(eq? (first expr) 'assume)
       (let* ((expr-arg (second expr))
              (expr-val (run-expr expr-arg store)))
         (jsil-assume expr-val))]
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
          (apply-unop unop arg))]
     

       )]))

(define (run-proc prog proc-name heap arg-vals)
  (let* ((proc (get-proc prog proc-name))
         (store (proc-init-store proc arg-vals)))
    (mutate-heap heap larguments parguments (make-jsil-list arg-vals))
    ;;(println (format "About to run procedure ~a with arguments ~a" proc-name arg-vals))
    (let ((res (run-cmds-iter prog proc-name heap store 0 0)))
      ;;(println (format "About to return from procedure ~a with return value ~a" proc-name res))
      (cons res store))))

(define (run-program prog heap)
  (jsil-discharge)
  (run-proc prog "main" heap '()))
  
(provide run-program run-proc program procedure heap cell store args body ret-ctx err-ctx jempty jnull jundefined protop) ;; jtrue jfalse protop)

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


  
