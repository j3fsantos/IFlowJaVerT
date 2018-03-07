(**************
 * Exceptions *
 **************)

exception Syntax_error of string

(**************
 * Hashtables *
 **************)

let small_tbl_size  = 53
let medium_tbl_size = 211 
let big_tbl_size    = 557

(*************
 * Debugging *
 *************)

let time = Unix.localtime (Unix.gettimeofday ())
let time_str = Printf.sprintf "%d%.2d%.2d_%.2dh%.2dm%.2ds"
                  (time.tm_year+1900) (time.tm_mon+1) time.tm_mday
                  time.tm_hour time.tm_min time.tm_sec

let output_file               = open_out ("normalOutput_" ^ time_str ^ ".txt")
let output_file_debug         = open_out ("debugOutput_" ^ time_str ^ ".txt")
let output_file_normalisation = open_out ("normalisationOutput_" ^ time_str ^ ".txt")
let output_file_njsil         = open_out ("normalisedSpecsPreds_" ^ time_str ^ ".njsil")

let close_output_files () =
	close_out output_file;
  close_out output_file_debug;
  close_out output_file_normalisation;
  close_out output_file_njsil

let im_petar    = ref true
let newencoding = ref false
let debug       = ref false
let sanity      = ref true
let output      = ref true

let print_debug  msg  = 
  if !output then
    output_string output_file_debug (Printf.sprintf "%s\n%!" msg)

let print_normal msg  = 
  if !output then
    output_string output_file (msg ^ "\n%!"); print_debug msg

let print_normalisation msg = 
  if !output then
    output_string output_file_normalisation (msg ^ "\n%!") 
let print_njsil_file msg  = 
  if !output then
    output_string output_file_njsil (msg ^ "\n%!") 

let print_debug_petar msg =
	if (!im_petar) then (print_debug msg) else ()

(**********************
 * Sets and multisets *
 **********************)

module SS = Set.Make(String)
module MS = CCMultiSet.Make(String)

(*************************)
(** Generic fresh names **)
(*************************)

let fresh_sth (name : string) : (unit -> string) =
  let counter = ref 0 in
  let rec f () =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f

(*******************************************)
(** Literal locations / Program variables **)
(*******************************************)

let lloc_prefix = "$"                   (* Literal location prefix  *)
let pvar_prefix = "_pvar_"              (* Program variable prefix  *)

let fresh_loc   = fresh_sth lloc_prefix (* Literal location counter *)
let fresh_pvar  = fresh_sth pvar_prefix (* Program variable counter *)

(* Literal location recogniser *)
let is_lloc_name (name : string) : bool =
  try (String.sub name 0 1 = lloc_prefix) with | _ -> false

(* Program variable recogniser *)
let is_pvar_name (name : string) : bool =
  (String.length name > 0) && (let first = String.sub name 0 1 in (first <> "_" && first <> "#" && first <> "$"))

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
          