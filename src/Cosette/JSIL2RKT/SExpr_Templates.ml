let (template_hp_racket:  ('a -> 'b, unit, string) format) = "
#lang rosette

(current-bitwidth #f)

(require (file \"mem_model.rkt\"))

(define hp
	(heap
		%s
	)
)

(provide hp)
"

let (template_internal_procs_racket:  ('a -> 'b, unit, string) format) = "
#lang rosette

(require (file \"mem_model.rkt\"))

(define internal-procs
  	(program
		%s
	)
)

(provide internal-procs)
"

let (template_procs_racket: ('a -> 'b, unit, string) format) = "
#lang rosette

(require (file \"mem_model.rkt\"))
(require (file \"interpreter.rkt\"))

(require (file \"hp.rkt\"))
(require (file \"internals_builtins_procs.rkt\"))

(require (file \"internals_racket.rkt\"))

(define prog
	(program
		%s
	)
)

(let ((prog-full (program-append prog internal-procs)))
  (run-program prog-full (register-racket-methods hp)))
"


let (template_procs_jsil_racket: ('a -> 'b, unit, string) format) = "
#lang rosette

(require (file \"mem_model.rkt\"))
(require (file \"interpreter.rkt\"))

(define prog
	(program
		%s
	)
)

(run-program prog (make-heap))
"



let (template_wp_racket:  ('a -> 'b, unit, string) format) = "
#lang rosette

(require (file \"mem_model.rkt\"))

(define wp
	(which-pred '(
%s
	))
)

(provide wp)
"

(* FOR TESTS *)

let (template_internal_procs_racket_for_tests:  ('a -> 'b, unit, string) format) = "
#lang rosette

(require (file \"mem_model.rkt\"))

(define internal-procs
  	(program
		%s
	)
)

(provide internal-procs)
"

let (template_procs_racket_for_tests: ('a -> 'b, unit, string) format) = "
#lang rosette

(require (file \"mem_model.rkt\"))
(require (file \"interpreter.rkt\"))

(require (file \"hp.rkt\"))
(require (file \"internals_builtins_procs.rkt\"))

(require (file \"internals_racket.rkt\"))

(define prog
	(program
		%s
	)
)

(let ((prog-full (program-append prog internal-procs)))
  (run-program prog-full (register-racket-methods hp)))
"

let (template_wp_racket_for_tests:  ('a -> 'b, unit, string) format) = "
#lang rosette

(require (file \"mem_model.rkt\"))

(define wp
	(which-pred '(
%s
	))
)

(provide wp)
"