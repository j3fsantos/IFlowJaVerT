(* logic *)
open Pulp_Syntax
open Utils

exception NotAConstant
exception Non_Existing_Field

type logical_var = 
  | AVar of string  (* ?X, ?Y, ?Z, ...*)
  | EVar of string  (* _X, _Y, _Z, ... *)

type variable_types = 
  | LogicalVariable of logical_var
  | ProgramVariable of variable
                                                     
module LogicalVarMap = Map.Make ( 
  struct 
    type t = logical_var
    let compare = compare
  end
)

module VarMap = Map.Make ( 
  struct 
    type t = variable_types
    let compare = compare
  end
)

type codename = string

type logical_exp =
  | Le_Var of logical_var
  | Le_PVar of variable
  | Le_None
  | Le_Literal of literal
  | Le_UnOp of unary_op * logical_exp
  | Le_BinOp of logical_exp * bin_op * logical_exp 
  | Le_Ref of logical_exp * logical_exp * reference_type   
  | Le_Base of logical_exp
  | Le_Field of logical_exp
  | Le_TypeOf of logical_exp

module ExpMap = Map.Make (
  struct
    type t = logical_exp
    let compare = compare
  end
)
  
let le_lit (le : logical_exp) : literal =
  match le with
    | Le_Literal lit -> lit
    | _ -> raise (InvalidArgument ("logic", "le_lit"))

type formula =
  | Star of formula list           (* F * ... * F *)
  | Heaplet of logical_exp * logical_exp * logical_exp      (* (l,x) |-> E *)
  | Eq of logical_exp * logical_exp        (* (E = E) ^ emp *)
  | NEq of logical_exp * logical_exp       (* (E != E) ^ emp *) 
  | REq of logical_exp                 (* (r = E) ^ emp *)
  | ObjFootprint of logical_exp * logical_exp list


let empty_f = Star []

type annot_body = formula list

type spec_pre_post =
{
  spec_pre  : formula;
  spec_post : formula list;
}

let mk_spec pre post = 
  { spec_pre = pre; spec_post = post }

type formula_antiframe = 
  {
    af_formula : formula;
    af_antiframe : formula option
  }










