(define-sort Set () (Array Real Bool))

(define-fun singleton ((x Real)) Set
  (store 
    ((as const (Array Real Bool)) false)
    x
    true))

(define-fun set-union ((x Set) (y Set)) Set
  ((_ map (or (Bool Bool) Bool)) x y)) 


(declare-const head Real)
(declare-const tail Set)
(declare-const result Set)
(declare-const value Real)

(assert 
  (forall ((x Real))
    (=> (select tail x) (> x head))))

(assert (< value head))

(assert
(forall ((result Set))
  (let ((phi1 
          (forall ((x Real)) (=> (select result x) (not (<= x value)))))
        (phi2
          (= result (union (singleton head) tail))))
    (not (and phi1 phi2)))))

(check-sat)