#lang rosette

(require (file "mem_model.rkt"))
(require (file "wp.rkt"))
(require (file "util.rkt"))
(require (file "assertions.rkt"))

(define depth 0)
(define success #f)
(define print-cmds #t)
(define call-stack-depth 0)
(define max-depth 5)

(define (generate-tabs n)
  (let ((tab "    "))
    (let loop ((i n)
               (new-tabs ""))
      (if (eq? i 0)
          new-tabs
          (loop (- i 1) (string-append tab new-tabs))))))

(define (print-info proc-name str)
  (when (and print-cmds (<= call-stack-depth max-depth))
    (let* ((tabs (generate-tabs call-stack-depth))
           (new-str (string-append tabs proc-name ": " str)))
    (println new-str))))

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
(define (run-bcmd prog proc-name bcmd heap store)
  (let ((cmd-type (first bcmd)))
    (cond
      ;;
      ;; ('skip)
      [(eq? cmd-type 'skip)
       (print-info proc-name "skip")
       empty]
      ;;
      ;; ('discharge)
      [(eq? cmd-type 'discharge)
       (print-info proc-name "discharge")
       (jsil-discharge)]
      ;;
      ;; ('h-assign e1 e2 e3)
      [(eq? cmd-type 'h-assign)
       (let* ((loc-expr (second bcmd))
              (prop-expr (third bcmd))
              (rhs-expr (fourth bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (rhs-val (run-expr rhs-expr store)))
	      ;; (println (format "Mutation: [~v, ~v] = ~v" loc-val prop-val rhs-val))
         (print-info proc-name (format "[~v, ~v] := ~v" loc-expr prop-expr rhs-expr))
         (mutate-heap heap loc-val prop-val rhs-val)
         rhs-val)]
      ;;
      ;; ('v-assign lhs-var e)
      [(eq? cmd-type 'v-assign)
       (let* ((lhs-var (second bcmd))
              (rhs-expr (third bcmd))
              (rhs-val  (run-expr rhs-expr store)))
         ;; (println (format "Assignment: ~v = ~v" lhs-var rhs-val))
         (print-info proc-name (format "~v := ~v" lhs-var rhs-val))
         (mutate-store store lhs-var rhs-val)
         rhs-val)]
      ;;
      ;; ('new lhs-var)
      [(eq? cmd-type 'new)
       (let ((lhs-var (second bcmd))
             (loc-val (get-new-loc)))
         (print-info proc-name (format "~v := new()" lhs-var))
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
              (prop-list (get-fields heap loc-val))
              (is-js-field (member prop-val prop-list))
              (result (not (eq? is-js-field #f))))
         ;; (println (format "Has-field: ~v = hf [~v, ~v] : ~v, ~v" lhs-var loc-val prop-val is-js-field result))
         ;; (println (format "object: ~v" (heap-get-obj heap loc-val)))
         ;; (println (format "proplist: ~v" prop-list))
         (print-info proc-name (format "~v := has-field(~v, ~v)" lhs-var loc-val prop-val))
         (mutate-store store lhs-var result) ;; (to-jsil-bool contains))
         result)] ;; (to-jsil-bool contains))]
      ;;
      ;; ('get-fields lhs-var e)
      [(eq? cmd-type 'get-fields)
       (let* ((lhs-var (second bcmd))
              (loc-expr (third bcmd))
              (loc-val (run-expr loc-expr store))
              (obj (heap-get-obj heap loc-val))
              (prop-list (petar-get-fields heap loc-val))
              (result (cons 'jsil-list prop-list)))
         ;; (println (format "Get-fields: ~v = gf (~v) : ~v" lhs-var loc-val result))
         (print-info proc-name (format "~v := get-fields(~v)" lhs-var loc-val))
         (mutate-store store lhs-var result) ;; (to-jsil-bool contains))
         result)] ;; (to-jsil-bool contains))]
      ;;
      ;; ('h-read lhs-var e1 e2)
      [(eq? cmd-type 'h-read)
       (let* ((lhs-var (second bcmd))
              (loc-expr (third bcmd))
              (prop-expr (fourth bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (result (heap-get heap loc-val prop-val)))
         ;; (println (format "Lookup: ~v = [~v, ~v] : ~v" lhs-var loc-val prop-val result))
         (print-info proc-name (format "~v := [~v, ~v]" lhs-var loc-val prop-val))
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
      ;; ('h-delete e1 e2)
      [(eq? cmd-type 'h-delete)
       (let* (
              (loc-expr (second bcmd))
              (prop-expr (third bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store)))
         ;;(println (format "the current heap: ~v" heap))
         (print-info proc-name (format "delete(~v, ~v)" loc-val prop-val))
         (heap-delete-cell heap loc-val prop-val)
         #t)] ;; (to-jsil-bool #t))]
      ;;
      ;; ('delete-object e)
      [(eq? cmd-type 'delete-object)
       (let* ((loc-expr (second bcmd))
              (loc-val (run-expr loc-expr store)))
         ;; (println (format "deleting the object: ~v" loc-val))
         (print-info proc-name (format "delete-object(~v)" loc-val))
         (heap-delete-object heap loc-val)
         #t)]
      ;;
      ;; ('success)
      [(eq? cmd-type 'success)
        ;; (println (format "terminating success"))
        (set! success #t) #t] 
      ;;
      [else (print cmd-type) (error "Illegal Basic Command")])))

(define goto-limit 100)

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
    ((>= (+ cur-index 1) (get-number-of-cmds proc)) '())
    ((eq? (first (get-cmd proc (+ cur-index 1))) 'v-psi-assign) prev-index)
    (#t cur-index)))

(define (print-cmd cmd)
  (if (union? cmd)
      (let*
          (
           (uc (union-contents cmd))
           (values (lht-values uc))
          )
        (println "Union command, yippie woo hoo hoo")
        (letrec ((iter (lambda (l)
		   (println (format "  ~v" l))
		   (cond ((not (null? (cdr l)))
			  (iter (cdr l)))))))
          (iter values)))
      (println cmd))
)


(define (run-cmds-iter prog proc-name heap store cur-index prev-index)
  (let* ((proc (get-proc prog proc-name))
         (cmd (get-cmd proc cur-index))
         (cmd-type (first cmd)))
    ;;(print-cmd cmd)
    ;;(println (format "Run-cmds-iter: procedure: ~v, index ~v, command ~v" proc-name cur-index cmd))
    (cond
      ;;
      ;; ('print e) 
      [(eq? cmd-type 'print)
       (let* ((expr (second cmd))
              (expr-val (run-expr expr store)))
         ;; (println (format "Program Print:: ~v" expr-val))
         (run-cmds-iter prog proc-name heap store (+ cur-index 1) cur-index))]
      ;;
      ;; ('goto i)
      [(and (eq? cmd-type 'goto) (= (length cmd) 2))
       (print-info proc-name (format "goto ~v" (second cmd)))
       (run-cmds-iter prog proc-name heap store (second cmd) cur-index)]
      ;;
      ;; ('goto e i j)
      [(and (eq? cmd-type 'goto) (= (length cmd) 4))
       (let* ((expr (second cmd))
              (then-label (third cmd))
              (else-label (fourth cmd))
              (expr-val (run-expr expr store)))
         (print-info proc-name (format "goto [~v] ~v ~v" expr-val then-label else-label))
         (parameterize ([goto-stack
                         (cons (cons proc-name cur-index) (goto-stack))])

           ; (println (format "branching on ~v" expr-val))
           (cond
             ;[(and (symbolic? expr-val) (equivalent-to-true? expr-val))
             ; (run-cmds-iter prog proc-name heap store then-label cur-index)]

             ;[(and (symbolic? expr-val) (equivalent-to-false? expr-val))
             ; (run-cmds-iter prog proc-name heap store else-label cur-index)]
             
             [(and (symbolic? expr-val)
                   (> (count-goto proc-name cur-index) goto-limit))
              (println "I am killing an execution because I reached the goto limit")
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
          (run-cmds-iter-next prog proc-name heap store cur-index next-prev))]
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
            (run-cmds-iter-next prog proc-name heap store cur-index next-prev))]
                              
      ;; ('call lhs-var e (e1 ... en) i)
      [(eq? cmd-type 'call)
       (let* ((lhs-var (second cmd))
              (proc-name-expr (third cmd))
              (arg-exprs (fourth cmd))
              (err-label (if (>= (length cmd) 5) (fifth cmd) null))
              (call-proc-name (run-expr proc-name-expr store))
              (arg-vals (map (lambda (expr) (run-expr expr store)) arg-exprs)))
         ;; (newline (current-output-port))
         ;; (println (format "~v : Procedure call: ~v (~v)" depth call-proc-name arg-vals))
         (set! depth (+ depth 1))
         (print-info proc-name (format "~v :=~v~v -> ?" lhs-var call-proc-name arg-vals))
         (let ((outcome (car (run-proc prog call-proc-name heap arg-vals))))
           (set! depth (- depth 1))
           ;; (println (format "~v : Procedure return: ~v = ~v (~v) -> ~v" depth lhs-var call-proc-name arg-vals outcome)) 
           ;; (newline (current-output-port))
           
           (cond
             [(and (eq? (first outcome) 'err) (not (null? err-label)))
              (print-info proc-name (format "~v :=~v~v -> (error, ~v)" lhs-var call-proc-name arg-vals (second outcome)))
              (mutate-store store lhs-var (second outcome))
              (run-cmds-iter prog proc-name heap store err-label cur-index)]

             [(eq? (first outcome) 'err)
              (print-info proc-name (format "~v :=~v~v -> (error, ~v)" lhs-var call-proc-name arg-vals (second outcome)))
              (error "Procedures that throw errors must be called with error labels")]
             
             [(eq? (first outcome) 'normal)
              (print-info proc-name (format "~v :=~v~v -> (normal, ~v)" lhs-var call-proc-name arg-vals (second outcome)))
              (mutate-store store lhs-var (second outcome))
              (run-cmds-iter-next prog proc-name heap store cur-index cur-index)]
             
             [else
              (display outcome)
              (error "Illegal Procedure Outcome")])))]
      ;;
      ;; basic command
      [else
       (let* ((cur-outcome (run-bcmd prog proc-name cmd heap store)))
         (run-cmds-iter-next prog proc-name heap store cur-index cur-index))])))


(define (run-cmds-iter-next prog proc-name heap store cur-index next-prev-index)
  (let* ((proc (get-proc prog proc-name))
         (ret-var (get-ret-var proc))
         (err-var (get-err-var proc)))
    ;;(displayln "I am in a marvellous phi")
    ;;(displayln (format "cur_index: ~v, err_index: ~v" cur-index (get-err-index proc)))
    ;; (println (format "So, proc: ~v, cur: ~v, ret: ~v, err: ~v" proc-name cur-index (get-ret-index proc) (get-err-index proc)))
    (cond
      [(eq? cur-index (get-ret-index proc))
       (list 'normal (store-get store ret-var))]
      [(eq? cur-index (get-err-index proc))
       (list 'err (store-get store err-var))]
      [else (run-cmds-iter prog proc-name heap store (+ cur-index 1) next-prev-index)])))


(define (run-expr expr store)
  ;;(println (format "run-expr: ~v" expr))
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
       ;; ('typeof e)
       [(eq? (first expr) 'typeof) 
        (let* ((arg (second expr))
               (val (run-expr arg store))
               (type-of
                (begin
                  ;; (println (format "argument of typeof ~v" val))
                  (jsil-type-of val))))
          ;; (println (format "typeOf: typeof ~v -> ~v = ~v" arg val type-of))
          type-of)]
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
       ;; ('l-nth l e)
       [(eq? (first expr) 'l-nth)
        (let* ((elist (second expr))
               (vlist (run-expr elist store))
               (eidx  (third expr))
               (vidx  (run-expr eidx store)))
          (if (list? vlist)
              (list-ref vlist (inexact->exact (+ vidx 1)))
              (begin
                (println (format "Illegal l-nth. l:~v; e:~v" vlist vidx))
                (error "Illegal list given to l-nth"))))]
       ;;
       ;; ('s-nth s e)
       [(eq? (first expr) 's-nth)
        (let* ((estr (second expr))
               (vstr (run-expr estr store))
               (eidx  (third expr))
               (vidx  (run-expr eidx store)))
          (if (string? vstr)
              (string-at vstr (inexact->exact vidx))
              (error "Illegal string given to s-nth")))]


       ;;
       ;; (make-symbol-number symb-name)
       [(eq? (first expr) 'make-symbol-number)
        (constant (second expr) integer?)]

       ;;
       ;; (make-symbol-string symb-name)
       [(eq? (first expr) 'make-symbol-string)
        (constant (second expr) string?)]

      ;;
      ;; ('assert e)
      [(eq? (first expr) 'assert)
       (let* ((expr-arg (second expr))
              (expr-val (run-expr expr-arg store)))
         (op-assert expr-val))]

      ;;
      ;; ('assume e)
      [(eq? (first expr) 'assume)
       (let* ((expr-arg (second expr))
              (expr-val (run-expr expr-arg store)))
         (op-assume expr-val))]
      ;;
      ;; (binop e e)
      [(= (length expr) 3) 
       (let ((binop (first expr)))
         (cond
           [(eq? binop 'and)
            (let ((larg (run-expr (second expr) store)))
              (if (not (eq? larg #t))
                  #f
                  (let ((rarg (run-expr (third expr) store)))
                    (eq? rarg #t))))]
           [(eq? binop 'or)
            (let ((larg (run-expr (second expr) store)))
              (if (eq? larg #t)
                  #t
                  (let ((rarg (run-expr (third expr) store)))
                    (eq? rarg #t))))]
           [else
            (let ((binop (to-interp-op binop))
                  (larg (run-expr (second expr) store))
                  (rarg (run-expr (third expr) store)))
              (apply-binop binop larg rarg))]))]
       ;;
       ;; (unop e)
       [(= (length expr) 2) 
        (let* ((unop (to-interp-op (first expr)))
               (arg (run-expr (second expr) store)))
          (apply-unop unop arg))]
     

       )]))

(define (run-proc prog proc-name heap arg-vals)
  (if (has-racket-implementation? proc-name)
      ;; Procedure Implemented in Racket
      (let* ((racket-proc (get-racket-implementation proc-name))
             (outcome (apply racket-proc (cdr arg-vals))))
        (cons outcome '()))
      ;; Procedure Implemented in JSIL
      (let* ((proc (get-proc prog proc-name))
             (store (proc-init-store proc arg-vals)))
        (mutate-heap heap larguments parguments (make-jsil-list arg-vals))
        (set! call-stack-depth (+ call-stack-depth 1))
        ;;(println (format "About to run procedure ~v with arguments ~v" proc-name arg-vals))
        (let ((res (run-cmds-iter prog proc-name heap store 0 0)))
          (set! call-stack-depth (- call-stack-depth 1))
          ;;(println (format "About to return from procedure ~v with return value ~v" proc-name res))
          (cons res store)))))

(define (run-program prog heap)
  (jsil-discharge)
  (run-proc prog "main" heap '()))
  
(provide run-program run-proc program procedure heap cell store args body ret-ctx err-ctx jempty jnull jundefined protop get-assertions get-assumptions success) ;; jtrue jfalse protop)



  
