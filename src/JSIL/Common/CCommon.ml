open Stdio.Out_channel

(**************
 * Exceptions *
 **************)

exception Syntax_error of string

(**************
 * Hashtables *
 **************)

let small_tbl_size  = 31
let medium_tbl_size = 101 
let big_tbl_size    = 1021

(*************
 * Debugging *
 *************)

let output_file               = create "normalOutput.txt"
let output_file_debug         = create "debugOutput.txt"
let output_file_normalisation = create "normalisationOutput.txt"
let output_file_njsil         = create "normalisedSpecsPreds.njsil"

let close_output_files () =
	close output_file;
  close output_file_debug;
  close output_file_normalisation

let im_petar    = ref true
let newencoding = ref false
let debug       = ref false

let print_debug  msg  = let msg = Printf.sprintf "%s\n%!" msg in output_string output_file_debug msg 
let print_normal msg  = output_string output_file (msg ^ "\n"); print_debug msg 
let print_normalisation msg = output_string output_file_normalisation (msg ^ "\n") 
let print_njsil_file msg  = output_string output_file_njsil (msg ^ "\n") 

let print_debug_petar msg =
	if (!im_petar) then (print_debug msg) else ()

(**********
 * Timing *
 **********)

let print_time msg =
	let time = Caml.Sys.time () in
	print_normal (msg ^ (Printf.sprintf " Time: %f" time))

let print_time_debug msg =
  if (!im_petar) then
		let time = Caml.Sys.time () in
			print_debug (msg ^ (Printf.sprintf " Time: %f" time))
		else ()

(************
 * Printing *
 ************)

let escape_string   = ref false 
let specs_on        = ref true
let line_numbers_on = ref false

let rec tabs_to_str (i : int) : string  =
	if i = 0 then "" else "\t" ^ (tabs_to_str (i - 1))

(** Auxiliary function for printing floating-point numbers *)
let string_of_float (x : float) : string =
  if (x == nan)
  		then "nan"
  		else if (x == neg_infinity)
  			then "-inf"
  			else if (x == infinity)
  				then "inf"
  				else Batteries.Float.to_string x