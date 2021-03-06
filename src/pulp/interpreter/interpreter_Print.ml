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

let string_of_field f =
  match f with
    | BuiltinField f -> string_of_builtin_field f
    | UserField x -> x

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
      (string_of_field x)