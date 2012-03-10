open Syntax

exception No_Spec_In_Code

let parse_formula f = 
  let lexbuf = Lexing.from_string f in
  Formula_parser.main Formula_lexer.token lexbuf
  
let get_pre_from_code exp =
  let rec get_req annots =
    match annots with
      | [] -> raise No_Spec_In_Code
      | annot :: tl -> 
        if (is_requires_annot annot) then annot
        else get_req tl in
  let req_annot = get_req exp.exp_annot in
  parse_formula req_annot.aformula 