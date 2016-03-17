(* ./src/pulp/interpreter/interpreter_Print.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Memory_Model
open Pulp_Syntax
open Pulp_Syntax_Print

let string_of_loc l =
  match l with
    | BLoc bl -> string_of_builtin_loc bl
    | Loc l -> "l"^ (string_of_int l)

let string_of_heap_value hv =
  match hv with
    | HVLiteral lit -> string_of_literal lit
    | HVObj l -> string_of_loc l

let string_of_value v =
  match v with
    | VHValue hv -> string_of_heap_value hv
    | VType t -> string_of_pulp_type t
    | VRef (hv, x, rt) -> 
      Printf.sprintf "(%s .%s %s)" 
      (string_of_heap_value hv)
      (match rt with
        | MemberReference -> "_o"
        | VariableReference -> "_v")
      x

let print_initial_heap_sexpr_aux h = 
	Memory_Model.Heap.fold 
		(fun loc obj printed_heap -> 
			let printed_loc = string_of_loc loc in 
			let printed_obj = 
					Memory_Model.Object.fold
						(fun prop prop_val printed_partial_obj ->
							 let printed_prop = prop in 
							 let printed_val = string_of_heap_value prop_val in 
							 let printed_cell = Printf.sprintf "\n\t(cell %s \"%s\" %s)"  printed_loc printed_prop printed_val in
								 printed_partial_obj ^ printed_cell)
						obj
						"" in 
			printed_heap ^ printed_obj)
			h
			""
(* ('heap ('cell loc prop val) ('cell loc prop val) ... ) *)
let serialize_heap_sexpr h = 
	"(heap" ^ (print_initial_heap_sexpr_aux h) ^ "\n)"

