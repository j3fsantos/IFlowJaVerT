#lang s-exp rosette

(require (file "mem_model.rkt"))

; Get rid of gotos that go to gotos
;
; Hypothesis: Every goto that goes to another goto can be eliminated
;             (unless circular, but then this (and the program will not terminate)
;
(define (where-does-it-really-go cmds line)
  (let* (
         (cmd (second (vector-ref cmds (- line 1))))
         (cmd-type (first cmd))
        )
    (cond
      [(and (eq? cmd-type 'goto) (= (length cmd) 2))
         (where-does-it-really-go cmds (second cmd))]
      [else line])))

; Update gotos to reflect final destinations of jumps
(define (propagate-gotos cmds)
  (let* (
         (cmds-num  (vector-length cmds))
         (cmds-ppg  (make-vector cmds-num))
         (cur-index 0)
        )
    (map (lambda (cmd-plus)
           (let* (
                  (cmd (second cmd-plus))
                  (cmd-type (first cmd))
                  (cmd-ppg (cond
                             [(and (eq? cmd-type 'goto) (= (length cmd) 2))
                              (let* (
                                     (wg (where-does-it-really-go cmds (second cmd)))
                                    )
                                (quasiquote (goto (unquote wg))))]
                             [(and (eq? cmd-type 'goto) (= (length cmd) 4))
                              (let* (
                                     (wgt (where-does-it-really-go cmds (third  cmd)))
                                     (wgf (where-does-it-really-go cmds (fourth cmd)))
                                    )
                              (quasiquote (goto (second (second cmd)) (unquote wgt) (unquote wgf))))]
                             [else cmd-plus]))
                  )
             (vector-set! cmds-ppg cur-index cmd-ppg)
             (set! cur-index (+ cur-index 1))))
           (vector->list cmds))
    cmds-ppg))

(provide propagate-gotos)