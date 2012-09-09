open Syntax
open List
open Logic
open Logic_Utils
open Utils

exception No_Spec_In_Code of string
exception No_Codename
exception No_Invariant_In_Code

let locMap : loc LocMap.t ref = ref (LocMap.empty)

let parse_formulas f = 
  
  let lexbuf = Lexing.from_string f in
  (* TODO: report parsing errors in a nicer way, catch exceptions such as Invalid_argument("index out of bounds") *)
  match Formula_parser.main Formula_lexer.token lexbuf with
    | ABFormulas formulas -> formulas
    | ABPredDefn _ -> raise (Failure "Predicate definition found when formula was expected")

let parse_defns f = 

  let lexbuf = Lexing.from_string (unescape_html f) in      (* Possibly this unescape should be done elsewhere? *)
  
  match Formula_parser.main Formula_lexer.token lexbuf with
    | ABFormulas _ -> raise (Failure "Formula(e) found when predicate definition was expected")
    | ABPredDefn defns -> defns

let get_defns_from_code exp =
	try
    let xs = List.find (fun annot -> annot.atype = PredDefn) exp.exp_annot in
      parse_defns xs.aformula
	with
		| Not_found -> []

let get_annots_from_code exp annot_type = 
  let annots = List.filter (fun annot -> annot.atype = annot_type) exp.exp_annot in
  List.map (fun annot -> parse_formulas annot.aformula) annots
  
let get_spec_from_code exp annot_type = 
  let res = get_annots_from_code exp annot_type in
  match res with
    | [] -> raise (No_Spec_In_Code (PrintSyntax.string_of_annot_type annot_type))
    | hd :: tl -> hd
  
let get_inv_from_code exp = 
  let res = get_annots_from_code exp Invariant in
  match res with
    | [] -> raise No_Invariant_In_Code
    | _ -> map (subs_locs !locMap) (flatten res)


let get_pre_from_code exp = get_spec_from_code exp Requires

let get_post_from_code exp = get_spec_from_code exp Ensures


let get_preposts_from_code exp = 
  let pres  = get_annots_from_code exp Requires in
  let posts = get_annots_from_code exp Ensures  in
  try
    List.map2
      (fun pre post ->
        match pre with
          | [formula] ->  { spec_pre = formula; spec_post = post }
          | _ ->  raise (Failure "Found a disjunctive precondition when non-disjunctive formula expected")
      )
      pres posts
  with
     | Invalid_argument "map2: Different_list_size" -> 
         raise (Failure "Number of preconditions differs from number of postconditions")


let get_codename exp =
  let codenames = filter (fun annot -> annot.atype = Codename) exp.exp_annot in
  match codenames with
    | [codename] -> codename.aformula
    | _ -> raise No_Codename

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
	    | Unary_op (_, e) -> f e
	    | BinOp (e1, _, e2) -> (f e1) @ (f e2)
	    | Access (e, _) -> f e
	    | Call (e1, e2s) -> (f e1) @ (flat_map (fun e2 -> f e2) e2s)
	    | Assign (e1, e2) 
      | AssignOp (e1, _, e2) -> (f e1) @ (f e2)
	    | New (e1, e2s) -> (f e1) @ (flat_map (fun e2 -> f e2) e2s)
	    | Obj xs -> flatten (map (fun (_,e) -> f e) xs)
	    | CAccess (e1, e2) -> (f e1) @ (f e2)
	    | With (e1, e2) -> (f e1) @ (f e2)
	    | Throw e 
	    | Return (Some e) -> f e
      | ForIn (e1, e2, e3) -> (f e1) @ (f e2) @ (f e3)
      | Comma (e1, e2) -> (f e1) @ (f e2)
      | Label (_, e) -> f e
      | Try (e1, Some (_, e2), Some e3) -> (f e1) @ (f e2) @ (f e3)
      | Try (e1, Some (_, e2), None)
      | Try (e1, None, Some e2) -> (f e1) @ (f e2)
      | Try (e1, None, None) -> raise CannotHappen
	    | RegExp _
	    | Num _
	    | String _
	    | Undefined
	    | Null
	    | Bool _
	    | Var _
	    | VarDec _
	    | This
	    | AnnonymousFun _
	    | NamedFun _
	    | Skip
      | Return None 
      | Break _
      | Continue _ -> [] in
  annots @ rec_annots
