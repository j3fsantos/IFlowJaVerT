open Syntax
open Logic
open Logic_Utils

exception No_Spec_In_Code

let parse_formula f = 
  let lexbuf = Lexing.from_string f in
  Formula_parser.main Formula_lexer.token lexbuf
  
let get_annot_from_code exp annot_type = 
    let rec get_annot annots =
    match annots with
      | [] -> raise No_Spec_In_Code
      | annot :: tl -> 
        if (annot.atype = annot_type) then annot
        else get_annot tl in
  let annot = get_annot exp.exp_annot in
  parse_formula annot.aformula
  
let get_pre_from_code exp = get_annot_from_code exp Requires
  
let get_post_from_code exp = get_annot_from_code exp Ensures