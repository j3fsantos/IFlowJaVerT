#lang rosette

(require (file "mem_model.rkt"))
(require (file "wp.rkt"))
(require (file "util.rkt"))
(require (file "assertions.rkt"))

(define depth 0)
(define success #f)
(define global-outcome '())
(define failure #f)
(define print-cmds #t)
(define call-stack-depth 0)
(define max-depth 3)

(define (generate-tabs n)
  (let ((tab "    "))
    (let loop ((i n)
               (new-tabs ""))
      (if (eq? i 0)
          new-tabs
          (loop (- i 1) (string-append tab new-tabs))))))

(define (print-info proc-name str) ;;42)
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
;; !!!!! RETURNS A HEAP AND A STORE !!!!!
(define (run-bcmd prog proc-name bcmd heap store)
  (let ((cmd-type (first bcmd)))
    (cond
      ;;
      ;; ('skip)
      [(eq? cmd-type 'skip)
       (print-info proc-name "skip")
       (cons heap store)]
      ;;
      ;; ('discharge)
      [(eq? cmd-type 'discharge)
       (print-info proc-name "discharge")
       (jsil-discharge)
       (cons heap store)]
      ;;
      ;; ('h-assign e1 e2 e3)
      [(eq? cmd-type 'h-assign)
       (let* ((loc-expr  (second bcmd))
              (prop-expr (third bcmd))
              (rhs-expr  (fourth bcmd))
              (loc-val   (run-expr loc-expr store))
              (prop-val  (run-expr prop-expr store))
              (rhs-val   (run-expr rhs-expr store))
              (heap      (mutate-heap heap loc-val prop-val rhs-val)))
        ;; (println (format "Mutation: [~v, ~v] = ~v" loc-val prop-val rhs-val))
         (print-info proc-name (format "[~v, ~v] := ~v" loc-expr prop-expr rhs-expr))
         (cons heap store))]
      ;;
      ;; ('v-assign lhs-var e)
      [(eq? cmd-type 'v-assign)
       (let* ((lhs-var  (second bcmd))
              (rhs-expr (third bcmd))
              (rhs-val  (run-expr rhs-expr store))
              (store    (mutate-store store lhs-var rhs-val)))
         ;; (println (format "Assignment: ~v = ~v" lhs-var rhs-val))
         (print-info proc-name (format "~v := ~v" lhs-var rhs-val))
         (cons heap store))]
      ;;
      ;; ('new lhs-var)
      [(eq? cmd-type 'new)
       (let* ((lhs-var (second bcmd))
              (loc-val (get-new-loc))
              (store (mutate-store store lhs-var loc-val))
              (heap  (mutate-heap  heap  loc-val protop jnull)))
         (print-info proc-name (format "~v := new()" lhs-var))
         (cons heap store))]
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
              (result (not (eq? is-js-field #f)))
              ;; (println (format "Has-field: ~v = hf [~v, ~v] : ~v, ~v" lhs-var loc-val prop-val is-js-field result))
              ;; (println (format "object: ~v" (heap-get-obj heap loc-val)))
              ;; (println (format "proplist: ~v" prop-list))
              (store (mutate-store store lhs-var result)))
         (print-info proc-name (format "~v := has-field(~v, ~v)" lhs-var loc-val prop-val))
         (cons heap store))] 
      ;;
      ;; ('get-fields lhs-var e)
      [(eq? cmd-type 'get-fields)
       (let* ((lhs-var (second bcmd))
              (loc-expr (third bcmd))
              (loc-val (run-expr loc-expr store))
              (obj (heap-get-obj heap loc-val))
              (prop-list (petar-get-fields heap loc-val))
              (result (cons 'jsil-list prop-list))
              (store (mutate-store store lhs-var result)))
         (print-info proc-name (format "~v := get-fields(~v)" lhs-var loc-val))
         (cons heap store))] 
      ;;
      ;; ('h-read lhs-var e1 e2)
      [(eq? cmd-type 'h-read)
       (let* ((lhs-var (second bcmd))
              (loc-expr (third bcmd))
              (prop-expr (fourth bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              (result (heap-get heap loc-val prop-val))
              ;; (println (format "Lookup: ~v = [~v, ~v] : ~v" lhs-var loc-val prop-val result))
              (store (mutate-store store lhs-var result)))
         (print-info proc-name (format "~v := [~v, ~v]" lhs-var loc-val prop-val))
         (cons heap store))]
      ;;
      ;; ('arguments lhs-var)
      [(eq? cmd-type 'arguments)
       (let* ((lhs-var (second bcmd))
              (result (heap-get heap larguments parguments))
              ;;(displayln "you called arguments")
              ;;(displayln result) 
              (store (mutate-store store lhs-var result)))
         (cons heap store))] 
      ;;
      ;; ('h-delete e1 e2)
      [(eq? cmd-type 'h-delete)
       (let* ((loc-expr (second bcmd))
              (prop-expr (third bcmd))
              (loc-val (run-expr loc-expr store))
              (prop-val (run-expr prop-expr store))
              ;;(println (format "the current heap: ~v" heap))
              (heap (heap-delete-prop heap loc-val prop-val)))
         (print-info proc-name (format "delete(~v, ~v)" loc-val prop-val))
         (cons heap store))]
      ;;
      ;; ('delete-object e)
      [(eq? cmd-type 'delete-object)
       (let* ((loc-expr (second bcmd))
              (loc-val (run-expr loc-expr store))
              (heap (heap-delete-object heap loc-val)))
         (print-info proc-name (format "delete-object(~v)" loc-val))
         (cons heap store))]

      ;;
      ;; ('assert e)
      [(eq? cmd-type 'assert)
       (let* ((expr-arg (second bcmd))
              (expr-val (run-expr expr-arg store)))
         (print-info proc-name (format "assert(~v)" expr-val))
         (op-assert expr-val)
         (cons heap store))]

      ;;
      ;; ('assume e)
      [(eq? cmd-type 'assume)
       (let* ((expr-arg (second bcmd))
              (expr-val (run-expr expr-arg store)))
         (print-info proc-name (format "assume(~v)" expr-val))
         (op-assume expr-val)
         (cons heap store))]
      
      ;;
      ;; ('success)
      [(eq? cmd-type 'success)
        (println (format "Terminated: success"))
        ;(println (format "Success was: ~v" success))
        (set! success #t)
        ;(println (format "And now it is: ~v" success))
        (cons heap store)] 
      ;;

      ;;
      ;; ('failure)
      [(eq? cmd-type 'failure)
        (println (format "Terminated: failure"))
        ;(println (format "Failure was: ~v" failure))
        (set! failure #t)
        ;(println (format "And now it is: ~v" failure))
        (cons heap store)]

      ;;
      ;; ('assert-* a)
      [(eq? cmd-type 'assert-*)
        (println (format "assert-*(~v)" (second bcmd)))
        (sep-assert (second bcmd) heap store)
        (cons heap store)] 
      
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



(define (process-proc-outcome outcome ctx)
  (let* ((ctx-entry (get-top-ctx-entry ctx))
         (proc-name (first ctx-entry))
         (store (second ctx-entry))
         (lhs-var (third ctx-entry))
         (cur-index (fourth ctx-entry))
         (err-label (fifth ctx-entry)))
    ;;(displayln (format "process-proc-outcome ~v" outcome))
    (cond
      [(and (eq? (car outcome) 'err) (not (null? err-label)))
       (print-info proc-name (format "ret: (error, ~v)" (cdr outcome)))
       (let ((store (mutate-store store lhs-var (cdr outcome))))
         (list store err-label (- cur-index 1)))]
    
      [(eq? (car outcome) 'err)
       (print-info proc-name (format "ret: (error, ~v)" (cdr outcome)))
       (error "Procedures that throw errors must be called with error labels")]
             
      [(eq? (car outcome) 'normal)
       (print-info proc-name (format "ret: (normal, ~v)" (cdr outcome)))
       (let ((store (mutate-store store lhs-var (cdr outcome))))
         (list store cur-index (- cur-index 1)))]
       
      [else
       (display outcome)
       (error "Illegal Procedure Outcome")])))


(define (run-proc prog proc-name heap store ctx lhs-var arg-vals cur-index err-label)
  (if (has-racket-implementation? proc-name)
      ;; Procedure Implemented in Racket
      (begin
        (displayln "encontrei um rosette model!!!")
        (let* ((racket-proc (get-racket-implementation proc-name))
               (outcome (apply racket-proc (cdr arg-vals)))
               (new-store (mutate-store store lhs-var (cdr outcome))))
          (run-cmds-iter prog heap new-store ctx (+ cur-index 1) cur-index)))
      ;; 
      ;; Procedure Implemented in JSIL
      (let* ((proc (get-proc prog proc-name))
             (new-store (proc-init-store proc arg-vals))
             (new-heap  (mutate-heap heap larguments parguments (make-jsil-list arg-vals)))
             (new-ctx
              (begin ;(displayln "I am going to create a context!!!")
                     (push-ctx-entry ctx proc-name store lhs-var (+ cur-index 1) err-label))))
        (set! call-stack-depth (+ call-stack-depth 1))
        ;(displayln (format "New ctx: ~v. New store: ~v. arg-vals: ~v" new-ctx new-store arg-vals))
        (run-cmds-iter prog new-heap new-store new-ctx 0 -1))))


(define (run-cmds-iter-next prog heap store ctx cur-index next-prev-index)
  (let* ((proc-name (get-proc-name-from-ctx ctx))
         (proc (get-proc prog proc-name))
         (ret-var (get-ret-var proc))
         (err-var (get-err-var proc)))
    ;;(displayln "I am in a marvellous phi")
    ;;(displayln (format "cur_index: ~v, err_index: ~v" cur-index (get-err-index proc)))
    ;;(println (format "So, proc: ~v, cur: ~v, ret: ~v, err: ~v" proc-name cur-index (get-ret-index proc) (get-err-index proc)))
    (cond
      [(eq? cur-index (get-ret-index proc))
       (let ((outcome (cons 'normal (store-get store ret-var))))
         ;(displayln (format "about to finish executing proc ~v with store: ~v. ctx: ~v" proc-name store ctx))
         (if (is-top-ctx? ctx)
             outcome 
             (let* ((next-state (process-proc-outcome outcome ctx))
                    (new-ctx (pop-ctx-entry ctx))
                    (new-store (first next-state))
                    (cur-index (second next-state))
                    (prev-index (third next-state)))
               (set! call-stack-depth (- call-stack-depth 1))
               (run-cmds-iter prog heap new-store new-ctx cur-index prev-index))))]
                      
      [(eq? cur-index (get-err-index proc))
        (let ((outcome (cons 'err (store-get store err-var))))
         (if (is-top-ctx? ctx)
             outcome 
             (let* ((next-state (process-proc-outcome outcome ctx))
                    (new-ctx (pop-ctx-entry ctx))
                    (new-store (first next-state))
                    (cur-index (second next-state))
                    (prev-index (third next-state)))
                (set! call-stack-depth (- call-stack-depth 1))
               (run-cmds-iter prog heap new-store new-ctx cur-index prev-index))))]

      [else (run-cmds-iter prog heap store ctx (+ cur-index 1) next-prev-index)])))


(define (run-cmds-iter prog heap store ctx cur-index prev-index)
  (let* ((proc-name (get-proc-name-from-ctx ctx))
         (proc (get-proc prog proc-name))
         (cmd (get-cmd proc cur-index))
         (cmd-type (first cmd)))
    ;;(println (pc))
    ;;(print-cmd cmd)
    ;;(println (format "Run-cmds-iter: procedure: ~v, index ~v, command ~v, ctx: ~v" proc-name cur-index cmd  ctx))
    (cond
      ;;
      ;; ('print e) 
      [(eq? cmd-type 'print)
       (let* ((expr (second cmd))
              (expr-val (run-expr expr store)))
         ;; (println (format "Program Print:: ~v" expr-val))
         (run-cmds-iter prog heap store ctx (+ cur-index 1) cur-index))]
      ;;
      ;; ('goto i)
      [(and (eq? cmd-type 'goto) (= (length cmd) 2))
       (print-info proc-name (format "goto ~v" (second cmd)))
       (run-cmds-iter prog heap store ctx (second cmd) cur-index)]
      ;;
      ;; ('goto e i j)
      [(and (eq? cmd-type 'goto) (= (length cmd) 4))
       (let* ((expr (second cmd))
              (then-label (third cmd))
              (else-label (fourth cmd))
              (expr-val (run-expr expr store)))
         (print-info proc-name (format "goto [~v] ~v ~v --> ~v" expr then-label else-label expr-val))
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
                (run-cmds-iter prog heap store ctx then-label cur-index)]
             
             [(eq? expr-val #f)
                (run-cmds-iter prog heap store ctx else-label cur-index)]
             
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
                (next-prev (compute-next-prev proc cur-index prev-index))
                (store (mutate-store store lhs-var val)))
          (run-cmds-iter-next prog heap store ctx cur-index next-prev))]
      ;;
      ;;  ('v-psi-assign var var_1 var_2 ... var_n)
         [(eq? cmd-type 'v-psi-assign)
          (let* ((lhs-var (second cmd))
                 (var-list (cddr cmd))
                 (ac-cur-index (find-prev-phi-cmd proc (- cur-index 1)))
                 (var-index (hash-ref wp (list proc-name prev-index ac-cur-index)))
                 (target-var (list-ref var-list var-index))
                 (val (run-expr target-var store))
                 (next-prev (compute-next-prev proc cur-index prev-index))
                 (store (mutate-store store lhs-var val)))
            (run-cmds-iter-next prog heap store ctx cur-index next-prev))]
                              
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
         (run-proc prog call-proc-name heap store ctx lhs-var arg-vals cur-index err-label))]
             
      ;;
      ;; basic command
      [else
       (let* ((result (run-bcmd prog proc-name cmd heap store))
              (heap  (car result))
              (store (cdr result)))
         (run-cmds-iter-next prog heap store ctx cur-index cur-index))])))



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
               (val (run-expr arg store)))
           ;; for*/all ([val val])
              (let* ((type-of (jsil-type-of val))
                     (tabs (generate-tabs call-stack-depth))
                     (new-str (string-append tabs ": " (format "typeOf: typeof ~v -> ~v = ~v" arg val type-of))))
                ;; (println new-str)
                type-of))]
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
               (eidx (third expr))
               (vlist (run-expr elist store))
               (vidx (run-expr eidx store)))
           ;; for*/all ([vlist vlist])
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
       ;; (make-untyped-symbol symb-name)
       [(eq? (first expr) 'make-untyped-symbol)
        (second expr)]

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

(define (terminate outcome)
  (cond 
  	[(eq? (car outcome) 'err) (exit 1)]
  	[else (exit 0)]))

(define (run-program prog heap)
  (jsil-discharge)
  (let* ((outcome (run-proc prog "main" heap '() '() '() '() -1 -1))
         (outcome-success (solve (assert (or (and (get-assumptions) (not success)) (and (get-assumptions) success (not (get-assertions))))))))
         ;;(outcome-failure (solve (assert failure)))
         ;;(outcome-success-assume (solve (assert (and (get-assumptions) success))))
         ;;(outcome-failure-assume (solve (assert (and (get-assumptions) failure))))
    ;;(print "Assumptions: ")
    ;;(println (get-assumptions))
    ;;(print "Assertions: ")
    ;;(println (get-assertions))
    ;;(print "Success: ")
    ;;(println success)
    ;;(print "Failure: ")
    ;;(println success)
    ;;(println (format "Outcome Success: ~v" outcome-success))
    ;;(println (format "Outcome Failure: ~v" outcome-failure))
    ;;(println (format "Outcome Success with assumptions: ~v" outcome-success-assume))
    ;;(println (format "Outcome Failure with assumptions: ~v" outcome-failure-assume))
    (set! global-outcome outcome)
    (println outcome-success)
    (terminate outcome)))

  
(provide run-program run-proc program procedure heap cell store args body ret-ctx err-ctx jempty jnull jundefined protop get-assertions get-assumptions success failure global-outcome) ;; jtrue jfalse protop)

;; (assertions-outcome (verify #:assume (assert (get-assumptions)) #:guarantee (assert success))))