(**
	Common - JaVerT
*)

open CCommon
open JSIL_Syntax

(*********************)
(** Fresh Variables **)
(*********************)

let lloc_prefix = "$l"                  (* Literal location prefix  *)
let pvar_prefix = "_pvar_"              (* Program variable prefix  *)

let fresh_loc   = fresh_sth lloc_prefix (* Literal location counter *)
let fresh_pvar  = fresh_sth pvar_prefix (* Program variable counter *)

(* Program variable recogniser *)
let is_pvar_name (name : string) : bool =
  try (let first = String.sub name 0 1 in (first <> "_" && first <> "#" && first <> "$")) with _ -> false

let aloc_prefix = "_$l_"               (* Abstract location prefix  *)
let lvar_prefix = "_lvar_"             (* Logical  variable prefix  *)

let fresh_aloc = fresh_sth aloc_prefix (* Abstract location counter *)
let fresh_lvar = fresh_sth lvar_prefix (* Logical  variable counter *)

(* Abstract location recogniser *)
let is_aloc_name (name : string) : bool =
  try (String.sub name 0 4 = aloc_prefix) with _ -> false

(* Logical variable recogniser *)
let is_lvar_name (name : string) : bool =
  try ((String.sub name 0 1 = "#") || (String.sub name 0 6 = lvar_prefix)) with _ -> false

(* Spec variables *)
let is_spec_var_name (name : string) : bool =
  try (String.sub name 0 1 = "#") with _ -> false

(**************************)
(** Satisfiability cache **)
(**************************)

(* Maps each assertion to true or false (if it's sasisfiable) *)
let sat_cache : (SA.t, bool) Hashtbl.t = Hashtbl.create 513
let encoding_cache : (SA.t, Z3.Expr.expr list) Hashtbl.t = Hashtbl.create 513

(* Default values *)
let initialise_caches =
	Hashtbl.add sat_cache (SA.singleton LTrue) true;
	Hashtbl.add sat_cache (SA.singleton LFalse) false;
	Hashtbl.add encoding_cache (SA.singleton LTrue) [];
  Hashtbl.add encoding_cache (SA.singleton LFalse) []

(* Performance statistics *)
let statistics = Hashtbl.create 511

(* Update the value of the fname statistic in the table, or add it if not present *)
let update_statistics (fname : string) (time : float) =
	if (Hashtbl.mem statistics fname)
		then let stat = Hashtbl.find statistics fname in
		Hashtbl.replace statistics fname (time :: stat)
		else Hashtbl.add statistics fname [ time ]

let process_statistics () =
	print_normal "\n STATISTICS \n ========== \n";
	print_normal (Printf.sprintf "Check sat cache: %d\n" (Hashtbl.length sat_cache)); 
	(* Process each item in statistics table *)
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

(* Interactive mode *)
let interactive = ref false