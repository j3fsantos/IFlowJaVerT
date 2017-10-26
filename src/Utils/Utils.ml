(* ./src/utils/utils.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Batteries
open List
open BatResult
open Option.Monad

let flat_map f l = flatten (BatList.map f l)

(* This exception is raised when Gareth thinks something is impossible,
   but it happens anyway. *)
exception ThereAreMorePossibilitiesThanYouThink of string
exception NotImplemented
exception CannotHappen
exception InvalidArgument of string * string
exception NotAFunction

(* For some reason, ocaml doesn't seem to have a boolean implication operator. Weird. *)

let (==>) a b = (! a) || b

(* Apparently data constructors can't /quite/ be used as
   functions. They can't be composed, for example. *)
let some x = Some x

let escape_html s =
  Str.global_substitute
    (Str.regexp "<\\|>\\|&\\|\"")
    (fun s ->
      match Str.matched_string s with
          "<" -> "&lt;"
        | ">" -> "&gt;"
        | "&" -> "&amp;"
        | "\"" -> "&quot;"
        | _ -> assert false)
    s
    
let (>>=) = bind                        (* This SHOULD be in batteries dammit. *)

(* This should always be "false" in checked-in code. Use it to check
   if you should be printing debug messages in other modules. *)
let debug = false
  
let debugPrint (s:string) =
  if debug then
    Printf.printf "\nDEBUG:\n%s\n\n" s
  else
    ()
   
(* This is very tricky, -0 has to not be an int *)
let is_int (f : float) : bool =
	let f' = float_of_int (int_of_float f) in
	f = f' && (copysign 1.0 f = copysign 1.0 f')

let is_normal (f : float) =
	let fc = Float.classify f in
		not ((fc = FP_infinite) || (fc = FP_nan))

let precision = 1e-6

(* This is intended to work on positive floats! *)
let string_of_pos_float num =
	  (* Is the number an integer? *)
		let inum = int_of_float num in
    if (is_int num) then string_of_int inum
		(* It is not an integer *)
    else 
		(*
		begin
			let n   = ref 0   in
			let k   = ref 0   in
			let s   = ref 0   in
			let str = ref ""  in
			let aux = ref num in
			let (below, above) = Float.modf num in
			Printf.printf "Above: %s Below: %s\n" (Float.to_string above) (Float.to_string below); 
			if (above = 0.0) then
			begin
				while (!aux < 1.) do
					n := !n + 1; 
					aux := Float.mul !aux 10.;
				done;
				while ((!aux < 10.0 -. precision) && (!aux <> 0.0)) do
					let (fmod, fdiv) = Float.modf !aux in
					Printf.printf "%s %s " (Float.to_string fdiv) (Float.to_string fmod);
					aux := Float.mul fmod 10.; 
					let fdiv = (if (!aux >= 10.0 -. precision) then (fdiv +. 1.) else fdiv) in
					let digit = (string_of_int (int_of_float fdiv)) in
					str := !str ^ digit; 
					Printf.printf "%s %s\n" (Float.to_string !aux) !str;
					k := !k + 1;
				done;
				s := int_of_string !str;
			end;
			
			Printf.printf "%d %d %d %s\n" !n !k !s (Float.to_string !aux); *)
			if num > 1e+9 && num < 1e+21 
				then Printf.sprintf "%.0f" num
			else
			if ((1e-5 <= num) && (num < 1e-4)) 
			then
			begin
				let s = (string_of_float (num *. 10.)) in
				let len = String.length s in
				"0.0" ^ (String.sub s 2 (len - 2))
			end
			else
			if ((1e-6 <= num) && (num < 1e-5)) 
			then
			begin
				let s = (string_of_float (num *. 100.)) in
				let len = String.length s in
				"0.00" ^ (String.sub s 2 (len - 2))
			end
			else
			let re = Str.regexp "e\\([-+]\\)0" in (* e+0 -> e+ *)
      				Str.replace_first re "e\\1" (string_of_float num)
			(*
			  if num > 1e+9 && num < 1e+21 
				then Printf.sprintf "%.0f" num
				else 
					if num < 0.1 && num > 1e-7 
						then Printf.sprintf "%f" num
    				else
      				let re = Str.regexp "e\\([-+]\\)0" in (* e+0 -> e+ *)
      				Str.replace_first re "e\\1" (string_of_float num) *)
	(* end *)
	
let rec float_to_string_inner n =
  if Float.is_nan n then "NaN"
  else if ((n = 0.0) || (n = -0.0)) then "0"
  else if (n < 0.0) then "-" ^ (float_to_string_inner (-. n))
  else if (n = Float.infinity) then "Infinity"
  else string_of_pos_float n
  
let safe_mkdir path = 
   if (not (Sys.file_exists path)) then Unix.mkdir path 0o777
  
let rec create_dir path =
   let dir = Filename.dirname path in
   let _ = if (not (Sys.file_exists dir)) then create_dir dir in
   safe_mkdir path
  
let create_dir_for_file filename = 
   let dir = Filename.dirname filename in
   if (not (Sys.file_exists dir)) then create_dir dir  

let try_find table entry = 
	let value = try
		Some (Hashtbl.find table entry)
	with _ -> None in
	value
	
let try_find_with_error table entry =
	let value = try
		Hashtbl.find table entry
	with _ -> print_endline (Printf.sprintf "Entry %s not found" entry); raise Not_found in
	value

let split3 (lst : ('a * 'b * 'c) list) : ('a list) * ('b list) * ('c list) =   
	List.fold_left 
		(fun (ass, bs, cs) (a, b, c) -> a :: ass, b :: bs, c :: cs) 
		([], [], [])
		lst  

