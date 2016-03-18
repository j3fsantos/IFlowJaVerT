#lang s-exp rosette

;; creating the symbols to use during symbolic execution 
(define-symbolic $banana1 number?)
(define-symbolic $banana2 number?)
(define-symbolic $banana3 number?)
(define-symbolic $banana4 number?)
(define-symbolic $banana5 number?)

;; adding numeric symbols to the num-symbol-table
(define num-symbol-table (mutable-set))
(set-add! num-symbol-table $banana1)
(set-add! num-symbol-table $banana2)
(set-add! num-symbol-table $banana3)
(set-add! num-symbol-table $banana4)
(set-add! num-symbol-table $banana5)

;;(define-symbolic $apple1 string?)
;;(define-symbolic $apple2 string?)
;;(define-symbolic $apple3 string?)
;;(define-symbolic $apple4 string?)
;
;; adding string symbols to the string-symbol-table
;;(define string-symbol-table (mutable-set))
;;(set-add! string-symbol-table $apple1)
;;(set-add! string-symbol-table $apple2)
;;(set-add! string-symbol-table $apple3)
;;(set-add! string-symbol-table $apple4)
;;(set-add! string-symbol-table $apple5)(define-symbolic $apple5 string?)

(define (symbolic? x) 
  (or (union? x) (term? x)))

(define (make-number-symbol)
  (if (set-empty? num-symbol-table)
      (error "No more numeric symbols available")     
      (let ((new-symbol (set-first num-symbol-table)))
        (set-remove! num-symbol-table new-symbol)
        new-symbol)))

(define (make-string-symbol)
  (error "String symbols not supported yet"))

;;(define (make-string-symbol)
;;  (if (set-empty? string-symbol-table)
;;      (error "No more numeric symbols available")     
;;      (let ((new-symbol (set-first string-symbol-table)))
;;        (set-remove! string-symbol-table new-symbol)
;;        (new-symbol))))

(provide symbolic? make-number-symbol make-string-symbol) 
       
