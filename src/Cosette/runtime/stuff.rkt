#lang rosette

(define n (constant 'n integer?))

(define global-solver (solve+))

(define (check-pc cur-pc)
   (not (unsat? ((solve+) cur-pc))))


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