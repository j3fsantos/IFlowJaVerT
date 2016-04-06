#lang racket

(require racket/set)

;; todos: there should be a deep version of the tests
(define (get-new-loc-dom)
  (gensym "#loc-dom")) 

;; ((ldoc doc) ... )
;; the document is the first one
;; TODO: we need consistency checks 
(define (make-dom-heap document)
  (let ((dom-loc (get-new-loc-dom)))
    (list (list dom-loc document null))))

;; dom string
(define dom-empty-string '(dom-string))

(define (dom-string-from-char c)
  (list 'dom-string c))

(define (dom-string-plus ds1 ds2)
  (append ds1 (cdr ds2)))

(define (dom-string? arg)
  (and (list? arg) (eq? (car arg) 'dom-string)))

;; dom attributes
(define (dom-attr name loc value fs)
  (list 'dom-attr name loc value fs))

(define (dom-empty-attr-group)
 (list 'dom-attr-group))

(define (dom-attr-group-from-attr da)
  (list 'dom-attr-group da))

(define (dom-attr-group-plus dag1 dag2)
  (append dag1 (cdr dag2)))

(define (dom-attr? arg)
  (and (list? arg) (eq? (car arg) 'dom-attr)))

(define (dom-attr-group? arg)
  (and (list? arg) (eq? (car arg) 'dom-attr-group)))

;; dom elements
(define (dom-element name loc dag dforest ts fs)
  (list 'dom-element name loc dag dforest ts fs))

(define (dom-element? arg)
  (and (list? arg) (eq? (car arg) 'dom-element)))

;; text nodes
(define (dom-text loc value fs)
  (list 'dom-text loc value fs))

(define (dom-text? arg)
  (and (list? arg) (eq? (car arg) 'dom-text)))

;; dom forests
(define (dom-forest-from-element element)
  (list 'dom-forest element))

(define (dom-forest-from-text text)
  (list 'dom-forest text))

(define (dom-empty-forest)
  (list 'dom-forest))

(define (dom-forest-plus df1 df2)
  (append df1 (cdr df2)))

(define (dom-forest? arg)
  (and (list? arg) (eq? (car arg) 'dom-forest)))

;; dom groves
(define (dom-grove-from-element element)
  (list 'dom-grove element))

(define (dom-grove-from-text text)
  (list 'dom-grove text))

(define (dom-grove-from-attr attr)
  (list 'dom-grove attr))

(define (dom-empty-grove)
  (list 'dom-grove))

(define (dom-grove-plus df1 df2)
  (append df1 (cdr df2)))

(define (dom-grove? arg)
  (and (list? arg) (eq? (car arg) 'dom-grove)))

;; document
(define (dom-document loc ele ts fs g)
  (list 'document loc ele ts fs g))

(define (dom-document? arg)
  (and (list? arg) (eq? (car arg) 'document)))

;; Operation Axioms


;; CreateElement: n.createElement(string)
;;
(define (createElement doc-loc name dheap)
  (if (and (eq? (caar dheap) doc-loc)
           (safe-name name))
      (let ((new-loc (get-new-loc-dom))
            (dom-name (string->dom-string name))
            (elem (dom-element dom-name new-loc (dom-empty-attr-group) (dom-empty-forest) '())))
        
  




