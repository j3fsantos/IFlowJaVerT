(** ********** **)
(** Exceptions **)
(** ********** **)

exception Syntax_error of string

(** ********** **)
(** Hashtables **)
(** ********** **)

let small_tbl_size = 101
let medium_tbl_size = 203
let big_tbl_size = 1021

(*************************************)
(** Fresh identifiers               **)
(*************************************)

let fresh_sth (name : string) : (unit -> string) =
  let counter = ref 0 in
  let rec f () =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f

(** ****************** **)
(** Logging (of sorts) **)
(** ****************** **)

let im_petar = ref true
let debug = ref false
let newencoding = ref false

let output_file = open_out "normalOutput.txt"
let output_file_debug = open_out "debugOutput.txt"
let output_file_normalisation = open_out "normalisationOutput.txt"

let print_debug  msg  = output_string output_file_debug (msg ^ "\n")
let print_normal msg  = output_string output_file (msg ^ "\n"); print_debug msg
let print_normalisation msg  = output_string output_file_normalisation (msg ^ "\n")

let close_output_files () =
	close_out output_file;
	close_out output_file_debug;
	close_out output_file_normalisation

let print_debug_petar msg =
	if (!im_petar) then (print_debug msg) else ()

let print_time msg =
	let time = Sys.time () in
	print_normal (msg ^ (Printf.sprintf " Time: %f" time))

let print_time_debug msg =
  if (!im_petar) then
		let time = Sys.time () in
			print_debug (msg ^ (Printf.sprintf " Time: %f" time))
		else ()

(** ********** **)
(** Statistics **)
(** ********** **)

let statistics = Hashtbl.create 511

(* Updates the value of the fname statistic in the table, or adds it if not present *)
let update_statistics (fname : string) (time : float) =
	if (Hashtbl.mem statistics fname)
		then 
			let stat = Hashtbl.find statistics fname in
			Hashtbl.replace statistics fname (time :: stat)
		else Hashtbl.add statistics fname [ time ]

let process_statistics () =
	print_normal "\n STATISTICS \n ========== \n";
	Hashtbl.iter (fun f lt ->
		(* Calculate average, min, max *)
		let min = ref infinity in
		let max = ref 0. in
		let tot = ref 0. in
		let avg = ref 0. in
		let std = ref 0. in
		let len = float_of_int (List.length lt) in
		tot := List.fold_left (fun ac t ->
			(if t < !min then min := t); (if t > !max then max := t);
			ac +. t) 0. lt;
		avg := !tot/.len;
		std := ((List.fold_left (fun ac t -> ac +. (!avg -. t) ** 2.) 0. lt) /. len) ** 0.5;
		print_normal (Printf.sprintf "\t%s\n" f);
		print_normal (Printf.sprintf "Tot: %f\tCll: %d\nMin: %f\tMax: %f\nAvg: %f\tStd: %f\n" !tot (int_of_float len) !min !max !avg !std)) statistics