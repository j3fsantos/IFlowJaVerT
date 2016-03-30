(* ./src/pulp/interpreter/memory_Model.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Pulp_Syntax 

(* Stack *)

module Stack = Map.Make ( 
  struct 
    type t = variable
    let compare = compare
  end
)

(* Heap *)

type loc =
  | BLoc of builtin_loc
  | Loc of int

module Heap = Map.Make ( 
  struct 
    type t = loc
    let compare = compare
  end
)

let fresh_int =
  let counter = ref 0 in
  let rec f () =
    let v = !counter in
    counter := !counter + 1;
    v
  in f
  
let fresh_loc () : int =
  fresh_int ()
  
(* Object *)

type field = 
  | BuiltinField of builtin_field
  | UserField of string

module Object = Map.Make ( 
  struct 
    type t = field
    let compare = compare
  end
)

(* Values *)

type heap_value =
  | HVLiteral of literal
  | HVObj of loc

type value =
  | VHValue of heap_value
  | VType of pulp_type
  | VRef of heap_value * field * reference_type

(* Do I still need this if I always evaluate literal builtin location to hbobj builtin location? Doesn't feel clean to have same things at different places *)
let heap_value_eq v1 v2 =
  match v1, v2 with
    | HVLiteral lit1, HVLiteral lit2 -> 0 = (compare lit1 lit2)
    | HVObj l1, HVObj l2 -> l1 = l2
    | HVLiteral (LLoc l1), HVObj (BLoc l2) -> l1 = l2
    | _, _ -> false

let value_eq v1 v2 =
  match v1, v2 with
    | VHValue hv1, VHValue hv2 -> heap_value_eq hv1 hv2
    | VRef (l1, s1, rt1), VRef (l2, s2, rt2) -> l1 = l2 && s1 = s2 && rt1 = rt2
    | VType t1, VType t2 -> t1 = t2
    | _, _ -> false

type heap_type = (heap_value Object.t) Heap.t
type stack_type = value Stack.t