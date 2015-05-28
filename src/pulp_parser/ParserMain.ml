
open Pulp_Syntax
open List

let pulp_from_string s = Pulp_Parser.parse_pulp Pulp_Lexer.lex (Lexing.from_string s)

(* TODO: implement *)
let pulp_lit_to_string l =
  match l with
    | Num n -> "(Num " ^ (string_of_float n) ^ ")"
    | Bool b -> "(Bool " ^ (string_of_bool b) ^ ")"
    | String s -> "(String " ^ s ^ ")"
    | Undefined -> "Undefined"
    | Null -> "Null"

let pulp_comparison_op_to_string c =
  match c with
  | Equal -> "Equal"
  | LessThan -> "LessThan"

let pulp_arith_op_to_string c =
  match c with
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Times -> "Times"
  | Div -> "Div"
  | Mod -> "Mod"

let pulp_boolean_op_to_string c =
  match c with
  | And -> "And"
  | Or -> "Or"

let pulp_bitwise_op_to_string c =
  match c with
  | BitwiseAnd -> "BitwiseAnd"
  | BitwiseOr -> "BitwiseOr"
  | BitwiseXor -> "BitwiseXor"
  | LeftShift -> "LeftShift"
  | SignedRightShift -> "SignedRightShift"
  | UnsignedRightShift -> "UnsignedRightShift"

let pulp_BinOp_to_string op =
  match op with
    | Comparison c -> "(Comparison " ^ (pulp_comparison_op_to_string c) ^ ")"
    | Arith a -> "(Arith " ^ (pulp_arith_op_to_string a) ^ ")"
    | Concat -> "Concat"
    | Boolean b -> "(Boolean " ^ (pulp_boolean_op_to_string b) ^ ")"
    | Bitwise b -> "(Bitwise " ^ (pulp_bitwise_op_to_string b) ^ ")"

let pulp_UnaryOp_to_string op =
  match op with
    | Not -> "Not"
    | Negative -> "Negative"
    | ToStringOp -> "ToStringOp"
    | ToNumberOp -> "ToNumberOp"
    | ToInt32Op -> "ToInt32Op"
    | ToUint32Op -> "ToUint32Op"
    | BitwiseNot -> "BitwiseNot"


(* TODO: implement *)
let rec pulp_exp_to_string e =
  match e with
    | Var v -> "(Var " ^ v ^ ")"
    | Literal l -> "(Literal " ^ (pulp_lit_to_string l) ^ ")"
    | BinOp (e,op,f) -> "(BinOp (" ^ (pulp_exp_to_string e) ^ "," ^ (pulp_BinOp_to_string op) ^ "," ^ (pulp_exp_to_string f) ^ "))"
    | UnaryOp (op,e) -> "(UnaryOp (" ^ (pulp_UnaryOp_to_string op) ^ "," ^ (pulp_exp_to_string e) ^ "))"


(* TODO: implement *)
let pulp_ass_right_exp_to_string e =
  match e with
    | Expression e -> "(Expression " ^ (pulp_exp_to_string e) ^ ")"

(* TODO: implement *)
let pulp_basic_to_string b =
  match b with
    | Assignment a -> "(Assignment { assign_left=" ^ a.assign_left ^ "; assign_right=" ^ (pulp_ass_right_exp_to_string a.assign_right) ^ " })";;

(* TODO: implement *)
let pulp_stmt_to_string p =
  match p with
    | Pulp_Syntax.Basic b -> "(Basic "^(pulp_basic_to_string b)^")";;

let rec pulp_to_string l =
  begin match l with
    | [] -> "[]"
    | head::tail -> (pulp_stmt_to_string head) ^ "::" ^ (pulp_to_string tail)
  end


(* Read input file and display the first line *)
(*
let read_file filename =
  let ic = open_in filename in
  try 
    let line = input_line ic in  (* read line from in_channel and discard \n *)
    flush stdout;                (* write on the underlying device now *)
    close_in ic;                 (* close the input channel *) 
    line
  
  with e ->                      (* some unexpected exception occurs *)
    close_in_noerr ic;           (* emergency closing *)
    raise e                      (* exit with error: files are closed but
                                    channels are not flushed *)
*)

let read_file filename = 
  let buffer = ref "" in
    let chan = open_in filename in
      try
        while true; do
          buffer := !buffer ^ (input_line chan) ^ "\n"
        done; !buffer
      with End_of_file ->
        close_in chan;
        !buffer;;


let parse filename =
    let buffer = read_file filename in
      print_endline ("parsing '"^buffer^"'");
      print_endline (pulp_to_string (pulp_from_string buffer))    (* write the result to stdout *)

let _ = parse Sys.argv.(1)

