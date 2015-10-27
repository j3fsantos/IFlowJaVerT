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

module ProgramVarMap = Map.Make ( 
  struct 
    type t = variable
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

type pi_predicate =
  {
    pi_list : logical_exp; (* TODO :What if I want to have a logical variable here? To represent the whole list. Does it mean I need list in my logic? *)
    pi_obj : logical_exp;
    pi_field : logical_exp;
    pi_loc : logical_exp;
    pi_value : logical_exp  
  } 
  

let mk_pi_pred list obj field loc value =
  {
    pi_list = list;
    pi_obj = obj;
    pi_field = field;
    pi_loc = loc;
    pi_value = value  
  }
    
type formula =
  | Star of formula list           (* F * ... * F *)
  | Heaplet of logical_exp * logical_exp * logical_exp      (* (l,x) |-> E *)
  | Eq of logical_exp * logical_exp        (* (E = E) ^ emp *)
  | NEq of logical_exp * logical_exp       (* (E != E) ^ emp *) 
  | REq of logical_exp                 (* (r = E) ^ emp *)
  | ObjFootprint of logical_exp * logical_exp list
  | Pi of pi_predicate
  | ProtoChain of logical_exp * logical_exp * logical_exp


let empty_f = Star []

let eq_true le = Eq (le, Le_Literal (Bool true))

let false_f = eq_true (Le_Literal (Bool false))

let eq_pvars_f x1 x2 = Eq (Le_PVar x1, Le_PVar x2)

let type_of_f x t = Eq (Le_TypeOf (Le_PVar x), Le_Literal (Type t))
let not_type_of_f x t = NEq (Le_TypeOf (Le_PVar x), Le_Literal (Type t))

let type_of_mref_f x = type_of_f x (ReferenceType (Some MemberReference))
let type_of_vref_f x = type_of_f x (ReferenceType (Some VariableReference))
let not_type_of_mref_f x = not_type_of_f x (ReferenceType (Some MemberReference))
let not_type_of_vref_f x = not_type_of_f x (ReferenceType (Some VariableReference))

let type_of_obj_f x = eq_true (Le_BinOp (Le_TypeOf x, Comparison LessThan, Le_Literal (Type (ObjectType None))))
let type_of_ref_f x = eq_true (Le_BinOp (Le_TypeOf x, Comparison LessThan, Le_Literal (Type (ReferenceType None))))
let proto_heaplet_f le1 le2 = Heaplet (le1, Le_Literal (String (string_of_builtin_field FProto)), le2)
let class_heaplet_f le1 le2 = Heaplet (le1, Le_Literal (String (string_of_builtin_field FClass)), (Le_Literal (String le2)))

type annot_body = formula list

type spec_pre_post =
{
  spec_pre  : formula;
  spec_post : formula list;
  spec_excep_post : formula list;
}

let mk_spec_with_excep pre post excep_post = 
  { spec_pre = pre; spec_post = post; spec_excep_post = excep_post }
  
let mk_spec pre post = 
  { spec_pre = pre; spec_post = post; spec_excep_post = [] }  

type formula_antiframe = 
  {
    af_formula : formula;
    af_antiframe : formula option
  }










