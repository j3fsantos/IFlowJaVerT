#lang rosette

(define n (constant 'n integer?))

(define global-limit 1)

(define check-pc 
  (let ((counter 0))
    (lambda (cur-pc)
      (if (eq? counter global-limit)
          (begin
            (set! counter 0)
            (not (unsat? ((solve+) cur-pc))))
          (begin
            (set! counter (+ counter 1))
            #t)))))
    

(if (> n 0)
    (if (check-pc (pc))
        (begin
          (println (format "FEASIBLE THEN OF OUTER IF: ~v" (pc)))
          (if (< n 0)
              (if (check-pc (pc))
                  (println (format "FEASIBLE THEN OF INNER IF: ~v" (pc)))
                  (println (format "INFEASIBLE THEN OF INNER IF: ~v" (pc))))
              (if (check-pc (pc))
                  (println (format "FEASIBLE ELSE OF INNER IF: ~v" (pc)))
                  (println (format "INFEASIBLE ELSE OF INNER IF: ~v" (pc))))))
        (println (format "INFEASIBLE THEN OF OUTER IF" (pc))))
    (if (not (unsat? ((solve+) (pc))))
        (println (format "FEASIBLE ELSE OF OUTER IF: ~v" (pc)))
        (println (format "INFEASIBLE ELSE OF OUTER IF: ~v" (pc)))))   