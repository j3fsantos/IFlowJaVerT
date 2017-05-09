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
  (not (forall ((x Real)) (=> (select (union (singleton head) tail) x) (not (<= x value))))))

(check-sat)