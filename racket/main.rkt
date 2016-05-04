#lang racket

;; parsing command line arguments + sets
(require racket/cmdline)
(require racket/set)

;; jsil interpreter
(require (file "interpreter.rkt"))
(require (file "util.rkt"))

;; verbosity controls
(define g-v-mode #f)
(define verbose-mode
  (lambda (v-mode)
    (set! g-v-mode v-mode)))

;; command line parsing
(define dir-arg
  (command-line
   #:once-each
   [("-v" "--verbose") "symbocally run with verbose messages"
                       (verbose-mode #t)]
   #:args (dir-arg)
   dir-arg))

;; traverse directory and loads the two files: functions.scm and heap.scm
(define (dir-name->full-path-str dir-name)
  (let* ((cur-path (current-directory))
         (cur-path-string (path->string cur-path))
         (new-path-string
          (string-append cur-path-string dir-name "/")))
    new-path-string))

;; functions.scm -> the procedures
;; heap.scm -> the initial heap
;; meta.scm -> meta info about the procedure - to be done
(define target 'not-processed)

(define (load-state file-names)
  (define cur-dir-str (dir-name->full-path-str dir-arg)) 
  ;;
  (define (load-state-iter files-to-process processed-files-table)
    (if (null? files-to-process)
        processed-files-table
        (begin
          (process-file (car files-to-process) processed-files-table)
          (load-state-iter (cdr files-to-process) processed-files-table))))
  ;;
  (define (process-file file-name processed-files-table)
    (let ((full-file-path-str (string-append cur-dir-str file-name)))
      (load full-file-path-str)
      (if (eq? target 'not-processed)
          (error "The file was not loaded")
          (hash-set! processed-files-table file-name target))))
   ;;
  (load-state-iter file-names (make-hash)))
         
(printf "You selected the folder:~a\n" dir-arg)
(define state (load-state (list "functions.rkt" "heap.rkt")))




