#lang s-exp rosette

(require "util.rkt")

(define current-assertions #t)

(define current-assumptions #t)

(define (clear-assertions!) (set! current-assertions #t))

(define (get-assertions) current-assertions)

(define (get-assumptions) current-assumptions)

(define (op-assert e) 
  (set! current-assertions (and current-assertions e))
  (println (format "Assertions: ~v" current-assertions))
  #t)

(define (op-assume e)
  (set! current-assumptions (and current-assumptions e))
  (println (format "Assumptions: ~v" current-assumptions))
  #t)


(struct partitioned-assertion (types cells none-cells empty-fields pure-asses))


(define (nass-to-list n-ass)
  (let ((n-ass-types (partitioned-assertion-types n-ass))
        (n-ass-cells (partitioned-assertion-cells n-ass))
        (n-ass-none-cells (partitioned-assertion-cells n-ass))
        (n-ass-empty-fields (partitioned-assertion-empty-fields n-ass))
        (n-ass-pure-asses (partitioned-assertion-pure-asses n-ass)))
    (list n-ass-types n-ass-cells n-ass-none-cells n-ass-empty-fields n-ass-pure-asses)))
        

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
        (partitioned-assertion ret-ass-types ret-ass-cells ret-ass-none-cells ret-ass-empty-fields n-ass-pure-asses)))))     


(define (sep-assert ass heap store)
  (let ((n-ass (normalise-assertion ass)))
    (println (format "sep-assert(~v)" (nass-to-list n-ass)))))
  
(provide clear-assertions! get-assertions get-assumptions op-assert op-assume sep-assert)
