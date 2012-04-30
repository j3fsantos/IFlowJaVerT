open Syntax
open List
open Logic
open Logic_Utils
open Utils

exception No_Spec_In_Code of string
exception No_Invariant_In_Code

let locMap : loc LocMap.t ref = ref (LocMap.empty)

let parse_formula f = 
  let lexbuf = Lexing.from_string f in
  (* TODO: report parsing errors in a nicer way, catch exceptions such as Invalid_argument("index out of bounds") *)
  Formula_parser.main Formula_lexer.token lexbuf
  
let get_annots_from_code exp annot_type = 
  let annots = List.filter (fun annot -> annot.atype = annot_type) exp.exp_annot in
  List.map (fun annot -> parse_formula annot.aformula) annots
  
let get_spec_from_code exp annot_type = 
  let res = get_annots_from_code exp annot_type in
  match res with
    | [] -> raise (No_Spec_In_Code (PrintSyntax.string_of_annot_type annot_type))
    | hd :: tl -> hd
  
let get_inv_from_code exp = 
  let res = get_annots_from_code exp Invariant in
  match res with
    | [] -> raise No_Invariant_In_Code
    | _ -> map (subs_locs !locMap) res
  
let get_pre_from_code exp = get_spec_from_code exp Requires
  
let get_post_from_code exp = get_spec_from_code exp Ensures

let get_annots exp =
  get_annots_from_code exp Requires @ 
  get_annots_from_code exp Ensures @ 
  get_annots_from_code exp Invariant

let rec get_all_annots_no_fun exp =
  let f = get_all_annots_no_fun in
  let annots = get_annots exp in
  let rec_annots = 
	  match exp.stx with 
	    | Seq (e1, e2) -> (f e1) @ (f e2)
	    | If (e1, e2, e3) -> (f e1) @ (f e2) @ (f e3)
	    | While (e1, e2) -> (f e1) @ (f e2)
	    | Delete e -> f e
	    | BinOp (e1, _, e2) -> (f e1) @ (f e2)
	    | Access (e, _) -> f e
	    | Call (e1, e2s) -> (f e1) @ (flat_map (fun e2 -> f e2) e2s)
	    | Assign (e1, e2) -> (f e1) @ (f e2)
	    | New (e1, e2s) -> (f e1) @ (flat_map (fun e2 -> f e2) e2s)
	    | Obj xs -> flatten (map (fun (_,e) -> f e) xs)
	    | CAccess (e1, e2) -> (f e1) @ (f e2)
	    | With (e1, e2) -> (f e1) @ (f e2)
	    | _ -> [] in
  annots @ rec_annots