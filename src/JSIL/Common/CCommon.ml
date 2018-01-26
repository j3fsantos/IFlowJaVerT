(* Exceptions *)
exception Syntax_error of string

(* Hashtbl sizes *)
let small_tbl_size  = 31
let medium_tbl_size = 101 
let big_tbl_size    = 1021

(* Debugging *)
let output_file               = open_out "normalOutput.txt"
let output_file_debug         = open_out "debugOutput.txt"
let output_file_normalisation = open_out "normalisationOutput.txt"
let output_file_njsil         = open_out "normalisedSpecsPreds.njsil"

let close_output_files () =
	close_out output_file;
  close_out output_file_debug;
  close_out output_file_normalisation

let im_petar    = ref true
let newencoding = ref false
let debug       = ref false

let print_debug  msg  = let msg = Printf.sprintf "%s\n%!" msg in output_string output_file_debug msg 
let print_normal msg  = output_string output_file (msg ^ "\n"); print_debug msg 
let print_normalisation msg = output_string output_file_normalisation (msg ^ "\n") 
let print_njsil_file msg  = output_string output_file_njsil (msg ^ "\n") 

let print_debug_petar msg =
	if (!im_petar) then (print_debug msg) else ()

(* Timing *)
let print_time msg =
	let time = Sys.time () in
	print_normal (msg ^ (Printf.sprintf " Time: %f" time))

let print_time_debug msg =
  if (!im_petar) then
		let time = Sys.time () in
			print_debug (msg ^ (Printf.sprintf " Time: %f" time))
		else ()
