#lang s-exp rosette

(require "util.rkt")
(require "mem_model.rkt")

(define current-assertions #t)

(define current-assumptions #t)

(define (clear-assertions!) (set! current-assertions #t))

(define (get-assertions) current-assertions)

(define (get-assumptions) current-assumptions)

(define (op-assert e) 
  (set! current-assertions (and current-assertions e))
  #t)

(define (op-assume e)
  (set! current-assumptions (and current-assumptions e))
  #t)



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
              (let* ((type-of (jsil-type-of val)))
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



(struct partitioned-assertion (types cells none-cells empty-fields pure-asses))


(define (pass-to-list n-ass)
  (let ((p-ass-types (partitioned-assertion-types n-ass))
        (p-ass-cells (partitioned-assertion-cells n-ass))
        (p-ass-none-cells (partitioned-assertion-none-cells n-ass))
        (p-ass-empty-fields (partitioned-assertion-empty-fields n-ass))
        (p-ass-pure-asses (partitioned-assertion-pure-asses n-ass)))
    (list p-ass-types p-ass-cells p-ass-none-cells p-ass-empty-fields p-ass-pure-asses)))
        

(define (combine-assertion n-ass1 n-ass2)
  (let ((n-ass1-types (partitioned-assertion-types n-ass1))
        (n-ass1-cells (partitioned-assertion-cells n-ass1))
        (n-ass1-none-cells (partitioned-assertion-cells n-ass1))
        (n-ass1-empty-fields (partitioned-assertion-empty-fields n-ass1))
        (n-ass1-pure-asses (partitioned-assertion-pure-asses n-ass1))
        (n-ass2-types (partitioned-assertion-types n-ass2))
        (n-ass2-cells (partitioned-assertion-cells n-ass2))
        (n-ass2-none-cells (partitioned-assertion-cells n-ass2))
        (n-ass2-empty-fields (partitioned-assertion-empty-fields n-ass2))
        (n-ass2-pure-asses (partitioned-assertion-pure-asses n-ass2)))
    ;; 
    (println (format "n-asss1-cells ~v" n-ass1-cells))
    (partitioned-assertion
     (append n-ass1-types n-ass2-types)
     (append n-ass1-cells n-ass2-cells)
     (append n-ass1-none-cells n-ass2-none-cells)
     (append n-ass1-empty-fields n-ass2-empty-fields)
     (append n-ass1-pure-asses n-ass2-pure-asses))))


(define (partition-assertion ass)
  (cond
    ;; error cases - the one I am taking care off 
    [(not (list? ass)) (error "DEATH. partition-assertion")]
    ;; and, or, not -> they must be pure or else it's wrong
    [(or (eq? (car ass) 'and) (eq? (car ass) 'or) (eq? (car ass) 'not))
      (partitioned-assertion '() '() '() '() (list ass))]
    ;; none-cell
    [(and (eq? (car ass) 'cell) (eq? (fourth ass) 'none))
     (partitioned-assertion '() '() (list ass) '() '())]
    ;; cell
    [(eq? (car ass) 'cell)
     (partitioned-assertion '() (list ass) '() '() '())]
    ;; empty-fields
    [(eq? (car ass) 'empty-fields)
     (partitioned-assertion '() '() '() (list ass) '())]
    ;; true
    [(eq? (car ass) 'true)
     (partitioned-assertion '() '() '() '() '())]
    ;; false
    [(eq? (car ass) 'false)
     (partitioned-assertion '() '() '() '() '(#f))]
    ;; star
    [(eq? (car ass) 'star)
     (let ((n-ass1 (partition-assertion (second ass)))
           (n-ass2 (partition-assertion (third ass))))
       (combine-assertion n-ass1 n-ass2))]
    ;; types
    ;; star
    [(eq? (car ass) 'types)
     (partitioned-assertion (list ass) '() '() '() '())]
    ;; pure formulae: eq?, <, <=, string-less-eq, set-mem, set-sub
    [else (partitioned-assertion '() '() '() '() (list ass))]))


(define (conflate-types type-asses)
  (let loop ((type-asses type-asses)
             (ret-type-asses '()))
    (cond
      [(null? type-asses) ret-type-asses]
      [else
       (loop (cdr type-asses) (append (cdr (car type-asses)) ret-type-asses))])))


(struct normalised-assertion (ntypes ncells nnone-cells nempty-fields npure-asses nlvars))


(define (nass-to-list n-ass)
  (let ((p-ass-types (normalised-assertion-ntypes n-ass))
        (p-ass-cells (normalised-assertion-ncells n-ass))
        (p-ass-none-cells (normalised-assertion-nnone-cells n-ass))
        (p-ass-empty-fields (normalised-assertion-nempty-fields n-ass))
        (p-ass-pure-asses (normalised-assertion-npure-asses n-ass))
        (p-ass-lvars (set->list (normalised-assertion-nlvars n-ass))))
    (list p-ass-types p-ass-cells p-ass-none-cells p-ass-empty-fields p-ass-pure-asses p-ass-lvars)))


(define (normalised-assertion-replace-ncells nass new-ncells)
  (let ((na-ntypes (normalised-assertion-ntypes nass))
        (na-nnone-cells (normalised-assertion-nnone-cells nass))
        (na-nempty-fields (normalised-assertion-nempty-fields nass))
        (na-npure-asses (normalised-assertion-npure-asses nass))
        (na-nlvars (normalised-assertion-nlvars nass)))
    (normalised-assertion na-ntypes new-ncells na-nnone-cells na-nempty-fields na-npure-asses na-nlvars)))


(define (pure-ass-lvars pass)
  (println (format "pure-ass-lvars ~v" pass))
  (cond
    ;; = 
    [(and (list? pass) (> (length pass) 0) (eq? (first pass) 'eq?))
     (set-union (expr-lvars (second pass)) (expr-lvars (third pass)))]
    ;; <
    [(and (list? pass) (> (length pass) 0) (eq? (first pass) '<))
     (set-union (expr-lvars (second pass)) (expr-lvars (third pass)))]
    ;; <=
    [(and (list? pass) (> (length pass) 0) (eq? (first pass) '<=))
     (set-union (expr-lvars (second pass)) (expr-lvars (third pass)))]
    ;; string-less
    [(and (list? pass) (> (length pass) 0) (eq? (first pass) 'string-less))
     (set-union (expr-lvars (second pass)) (expr-lvars (third pass)))]
    ;; set-mem
    [(and (list? pass) (> (length pass) 0) (eq? (first pass) 'set-mem))
     (set-union (expr-lvars (second pass)) (expr-lvars (third pass)))]
    ;; set-sub
    [(and (list? pass) (> (length pass) 0) (eq? (first pass) 'set-sub))
     (set-union (expr-lvars (second pass)) (expr-lvars (third pass)))]))


(define (pure-ass-subst pass subst)
  (println (format "pure-ass-subst ~v" pass))
  (cond
    ;; = 
    [(and (list? pass) (> (length pass) 0) (eq? (first pass) 'eq?))
     (list 'eq? (lexpr-substitution (second pass) subst) (lexpr-substitution (third pass) subst))]
    ;; <
    [(and (list? pass) (> (length pass) 0) (eq? (first pass) '<))
     (list '< (lexpr-substitution (second pass) subst) (lexpr-substitution (third pass) subst))]
    ;; <=
    [(and (list? pass) (> (length pass) 0) (eq? (first pass) '<=))
     (list '<= (lexpr-substitution (second pass) subst) (lexpr-substitution (third pass) subst))]
    ;; string-less
    [(and (list? pass) (> (length pass) 0) (eq? (first pass) 'string-less))
     (list 'string-less (lexpr-substitution (second pass) subst) (lexpr-substitution (third pass) subst))]
    ;; set-mem
    [(and (list? pass) (> (length pass) 0) (eq? (first pass) 'set-mem))
     (list 'set-mem (lexpr-substitution (second pass) subst) (lexpr-substitution (third pass) subst))]
    ;; set-sub
    [(and (list? pass) (> (length pass) 0) (eq? (first pass) 'set-sub))
     (list 'set-sub (lexpr-substitution (second pass) subst) (lexpr-substitution (third pass) subst))]))

  
    
(define (normalise-assertion ass)
  (let ((n-ass (partition-assertion ass))) 
    (let ((n-ass-types (partitioned-assertion-types n-ass))
          (n-ass-cells (partitioned-assertion-cells n-ass))
          (n-ass-none-cells (partitioned-assertion-cells n-ass))
          (n-ass-empty-fields (partitioned-assertion-empty-fields n-ass))
          (n-ass-pure-asses (partitioned-assertion-pure-asses n-ass)))
      (let ((ret-ass-types (conflate-types n-ass-types))
            (ret-ass-cells (map (lambda (x) (cdr x)) n-ass-cells))
            (ret-ass-none-cells (map (lambda (x) (cdr x)) n-ass-none-cells))
            (ret-ass-empty-fields (map (lambda (x) (cdr x)) n-ass-empty-fields)))
        (println (format "BANANAS: ~v ~v ~v ~v" ret-ass-types ret-ass-cells ret-ass-none-cells ret-ass-empty-fields))
        (let ((cell-lvars
               (foldl (lambda (cell ac)
                        (let ((loc-lvars (expr-lvars (first cell)))
                              (field-lvars (expr-lvars (second cell)))
                              (val-lvars (expr-lvars (third cell))))
                          (println (format "CHECKING LVARS IN CELLS. GOT the sets ~v ~v ~v" loc-lvars field-lvars val-lvars))
                          (set-union loc-lvars (set-union field-lvars (set-union val-lvars ac)))))
                      (set)
                      ret-ass-cells))
              (none-cell-lvars
               (foldl (lambda (cell ac)
                        (let ((loc-lvars (expr-lvars (first cell)))
                              (field-lvars (expr-lvars (second cell)))
                              (val-lvars (expr-lvars (third cell))))
                          (set-union loc-lvars (set-union field-lvars (set-union val-lvars ac)))))
                      (set)
                      ret-ass-none-cells))
              (empty-fields-lvars
               (foldl (lambda (cell ac)
                        (let ((loc-lvars (expr-lvars (first cell)))
                              (domain-lvars (expr-lvars (second cell))))
                          (set-union loc-lvars (set-union domain-lvars ac))))
                      (set)
                      ret-ass-empty-fields))
              (pass-lvars
               (begin 
                 (println "GOING to check the PASS LVARS")
                 (foldl (lambda (pass ac)
                          (set-union (pure-ass-lvars pass) ac))
                      (set)
                      n-ass-pure-asses))))
          (println (format "GOT the following PASS LVARS ~v" pass-lvars))
          (let ((n-ass-lvars (set-union cell-lvars (set-union none-cell-lvars (set-union empty-fields-lvars pass-lvars)))))   
            (normalised-assertion ret-ass-types ret-ass-cells ret-ass-none-cells ret-ass-empty-fields n-ass-pure-asses n-ass-lvars)))))))     



(define (unify-lexprs lexpr pat-lexpr subst store)
  (if (and (check-logic-variable pat-lexpr) (not (hash-has-key? subst pat-lexpr)))
      (list #t '() (list (cons pat-lexpr (run-expr lexpr store))))
      ;; the pat-lexpr is not an existentially quantified variable
      (let* ((s-pat-lexpr (lexpr-substitution pat-lexpr subst))
             (pat-val (run-expr s-pat-lexpr store))
             (val (run-expr lexpr store)))
           (if (unsat? (solve (assert (eq? lexpr pat-val))))
               (list #f)
               (list #t (list (list 'eq? lexpr pat-val)) '())))))


;; returns a list of candidate unifications.
;; each candidate unification is composed of three elements: (framed-heap, positive-constraints, substitution-list)
(define (unify-cell heap cell subst store)

  (println (format "The cell: ~v" cell))
  
  (let ((pat-loc (first cell))
        (pat-field (second cell))
        (pat-val (third cell)))

    (let* ((s-pat-loc
            (if (is-loc? pat-loc)
                pat-loc
                (if (hash-has-key? subst pat-loc)
                    (hash-ref subst pat-loc)
                    (error "DEATH. unify-cell"))))

           (obj (heap-get-obj heap s-pat-loc)))

      (let loop ((fv-pairs obj)
                 (visited-fv-pairs '())
                 (viable-unifications '()))

        (if (null? fv-pairs)
            viable-unifications
            (let* ((field (caar fv-pairs))
                   (val (cdar fv-pairs))
                   (u-fields (unify-lexprs field pat-field subst store))
                   (u-vals (unify-lexprs val pat-val subst store)))
              
              (if (and (car u-fields) (car u-vals))
                  (let ((unification
                         (let* ((new-obj (append visited-fv-pairs (cdr fv-pairs)))
                                (new-heap (heap-replace-object heap s-pat-loc new-obj)))                     
                           (list
                            new-heap
                            (append (second u-fields) (second u-vals))
                            (append (third u-fields) (third u-vals))))))
                    (loop (cdr fv-pairs) (cons (car fv-pairs) visited-fv-pairs) (cons unification viable-unifications)))
                  (loop (cdr fv-pairs) (cons (car fv-pairs) visited-fv-pairs) viable-unifications)))))))) 
                  

(define (unify-pure-assertions pure-asses additional-constraints subst store)
  (let* ((s-pure-asses (map (lambda (x) (pure-ass-subst x subst)) pure-asses))
         (pure-constraints (append s-pure-asses additional-constraints)))
    (let ((pure-constraint (foldl (lambda (x ac) (and x ac)) #t pure-constraints)))
      (if (unsat? (solve (assert (not pure-constraint))))
          (cons #t '())
          (cons #f pure-constraints)))))


(define (extend-substitution subst subst-list) 
  (let loop ((subst (hash-copy subst))
             (subst-list subst-list)
             (subst-constraints '()))
    (if (null? subst-list)
        (cons subst subst-constraints)
        (let ((var (caar subst-list))
              (lexpr (cdar subst-list))) 
          (if (hash-has-key? subst var)
              ;; the var already exists in the substitution
              ;;    - we have to test the corresponding lexprs are equal.
              (loop subst (cdr subst-list) (cons (eq? lexpr (hash-ref subst var)) subst-constraints))
              ;; the var does not exist in the substitution
              ;;   - we simply extend the substitution
              (begin
                (hash-set! subst var lexpr)
                (loop subst (cdr subst-list) subst-constraints)))))))


(define (unify-ass heap n-ass store)
  ;; frame -> heap, n-ass, subst, positive-constraints 
  (let loop ((cur-frames (list (list heap n-ass (make-hash) '())))
             (failing-constraints '()))

    (println "inside unify assertions!!!")
    
    (if (null? cur-frames)
        ;; we have collected all the failing constraints 
        (cons #f failing-constraints)
        (let* ((cur-frame (first cur-frames))
               (f-cells
                (begin
                  ;;(println (format "cur-frame: ~v" cur-frame))
                  (normalised-assertion-ncells (second cur-frame)))))
          (if (null? f-cells)

              ;; successfully unified all the spation resource
              (begin
                (println "Unified all postitive spatial resource")
                (let ((unification (unify-pure-assertions (normalised-assertion-npure-asses (second cur-frame)) (fourth cur-frame) (third cur-frame) store)))
                  (if (first unification)
                      (cons #t '())
                      (loop (cdr cur-frames) (cons (second unification) failing-constraints)))))

              ;; we have once cell to unify
              (begin
                (println "Cell assertions still need to be unified")
                (let* ((cur-cell (first f-cells))
                       (cur-cell-unifications (unify-cell (first cur-frame) cur-cell (third cur-frame) store))
                       ;; cell-unifications -> ((list quotient-heap subst-list discharges))
                       (next-n-ass (normalised-assertion-replace-ncells (second cur-frame) (cdr f-cells)))
                       
                       (new-frames
                        (begin
                          (map (lambda (x)
                                 (println (format "computing the new frames: ~v!!!" x))
                                 (let* ((new-heap (first x))
                                        (new-constraints (second x))
                                        (subst-list (third x))
                                        (new-subst-plus-constraints
                                         (begin
                                           (println (format "REACHED extend-substitution!"))
                                           (extend-substitution (third cur-frame) subst-list)))
                                        (new-subst (car new-subst-plus-constraints))
                                        (subst-constraints (cdr new-subst-plus-constraints)))
                                   (list new-heap next-n-ass new-subst (append (append subst-constraints new-constraints) (fourth cur-frame)))))
                               cur-cell-unifications))))
                  (loop (append new-frames (cdr cur-frames)) failing-constraints))))))))


   
(define (sep-assert ass heap store)
  (let ((n-ass (normalise-assertion ass)))
    (println (format "sep-assert(~v)" (nass-to-list n-ass)))
    (let ((res (unify-ass heap n-ass store)))
      (if (not (car res))
          (begin
            (println "The sep-assert failed!!!!"))
          (begin
            (println "one symbolic execution terminated successfully"))))))
  
(provide clear-assertions! get-assertions get-assumptions op-assert op-assume sep-assert)
