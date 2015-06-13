open Parser_syntax
open List
open Pulp_Logic
open Pulp_Logic_Utils
open Utils

exception No_Spec_In_Code of string
exception No_Codename
exception No_Invariant_In_Code

let parse_formulas f = 
  let lexbuf = Lexing.from_string f in
  Pulp_Formula_Parser.main Pulp_Formula_Lexer.token lexbuf

let get_annots_from_code annots annot_type = 
  let annots = List.filter (fun annot -> annot.annot_type = annot_type) annots in
  List.map (fun annot -> parse_formulas annot.annot_formula) annots
  
let get_spec_from_code annots annot_type = 
  let res = get_annots_from_code annots annot_type in
  match res with
    | [] -> raise (No_Spec_In_Code (Pretty_print.string_of_annot_type annot_type))
    | hd :: tl -> hd
  
let get_inv_from_code annots = 
  let res = get_annots_from_code annots Invariant in
  match res with
    | [] -> raise No_Invariant_In_Code
    | _ -> res

let get_function_spec annots = 
  let pres  = get_annots_from_code annots Requires in
  let posts = get_annots_from_code annots Ensures  in
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


let get_codename annots =
  let codenames = filter (fun annot -> annot.annot_type = Codename) annots in
  match codenames with
    | [codename] -> codename.annot_formula
    | _ -> raise No_Codename

let get_annots annots =
  flat_map (get_annots_from_code annots) [Requires; Ensures; Invariant]
