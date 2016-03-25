#lang s-exp rosette

(require rosette/solver/smt/cvc4)
(current-solver (new cvc4%))
(current-bitwidth 32)

(define-symbolic @s string?)

(require (file "interpreter.rkt"))

(define-symbolic $banana number?)

(define empty-prog
  (program
   (procedure "main" (args 'rthis 'rscope) (body 'body) (ret-ctx 'r1 0) (err-ctx 'r1 0))))      

(define cmds-1
  #(
    (v-assign r1 1)
    (v-assign r2 2)
    (v-assign r3 (+ r1 r2))))

(define cmds-2
  #(
    (v-assign r1 1)
    (new r2)
    (h-assign r2 "foo" 2)
    (h-read r3 r2 "foo")
    (v-assign r4 (+ r3 2))))

(define cmds-3
  #(
    (v-assign r1 1)
    (new r2)
    (h-assign r2 "foo" 2)
    (has-field r3 r2 "foo")))

(define cmds-4
  #(
    (v-assign r1 1)
    (new r2)
    (h-assign r2 "foo" 2)
    (h-delete r3 r2 "foo")
    (has-field r4 r2 "foo")))

(define cmds-5
  #(
    (v-assign r1 1)
    (new r2)
    (h-assign r2 "foo" 2)
    (h-delete r3 r2 "bar")
    (has-field r4 r2 "foo")))

(define cmds-6
  #(
    (v-assign r1 1)
    (new r2)
    (h-assign r2 "foo" 2)
    (h-delete r3 r2 "bar")
    (has-field r4 r2 "foo")))

(define cmds-7
  #(
    (new r1)
    (new r2)
    (h-assign r1 "foo" 1111)
    (h-assign r1 "foo" 2222)
    (h-assign r1 protop r2)
    (h-read r3 r1 protop)))

(define cmds-8
  #(
    (new r2)
    (new r3)
    (new r4)
    (h-assign r2 "proto" r3)))

(define cmds-9
  #(
    (new r2)
    (new r3)
    (new r4)
    (h-assign r2 "foo" 2222)
    (h-assign r2 "proto" r3)
    (h-assign r3 "proto" r4)
    (h-assign r3 "bar" 3333)
    (h-assign r4 "baz" 4444)
    (proto-field r5 r2 "baz")))

(define cmds-10
  #(
    (new r2)
    (new r3)
    (new r4)
    (h-assign r2 "foo" 2222)
    (h-assign r2 "proto" r3)
    (h-assign r3 "proto" r4)
    (h-assign r3 "bar" 3333)
    (h-assign r4 "baz" 4444)
    (proto-obj r5 r2 "baz")))

(define cmds-11
  #(
    (goto 2)
    (v-assign r1 3)
    (skip)))

(define cmds-12
  #(
    (goto (> 3 2) 2 1)
    (v-assign r1 3)
    (skip)))

(define cmds-13
  #(
    (v-assign r-x 5)
    (v-assign r-y 1)
    (goto (> r-x 0) 1 4)
    (v-assign r-y (* r-x r-y))
    (v-assign r-x (- r-x 1))
    (goto -3)
    (skip)))

(define prog1
  (program
   (procedure "main" (args 'rthis 'rscope) (body 'body) (ret-ctx 'r1 0) (err-ctx 'r1 0))
   (procedure "factorial" (args 'r-x)
              (body
                '(v-assign r-y 1)
                '(goto (> r-x 0) 2 5)
                '(v-assign r-y (* r-x r-y))
                '(v-assign r-x (- r-x 1))
                '(goto 1)
                '(skip)
               ) (ret-ctx 'r-y 5) (err-ctx 'r-err 666))))      

(define cmds-14
  #(
    (v-assign r-1 6)
    (call r-2 "factorial" (r-1) 666)
    (skip)))

(define cmds-15
  #(
    (v-assign r1 (make-symbol number))
    (assert (= r1 3))
    (check (> r1 0))))

(define cmds-16
  #(
    (v-assign r1 (make-symbol number))
    (assert (> r1 2))
    (new r2)
    (h-assign r2 "foo" r1)
    (h-read r3 r2 "foo")
    (v-assign r4 (+ r3 2))
    (check (> r4 4))))

(define cmds-17
  #(
    (v-assign r1 (make-symbol string))
    (new r2)
    (h-assign r2 "foo" r1)
    (h-read r3 r2 "foo")
    (check (not (equal? r3 "zigzag")))))

(define cmds-18
  #(
    (v-assign r1 (make-symbol string))
    (new r2)
    (h-assign r2 "foo" r1)
    (h-read r3 r2 "foo")))

(define hp (heap))
(define st (store))
(run-cmds empty-prog cmds-17 hp st 0)
