open WISL_Lexer
open Lexing
open WISL_Printer
open WISL_Syntax
open Format
open WISL2JSIL_Compiler


let burn_to_disk path data =
	let oc = open_out path in
		output_string oc data;
		close_out oc

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try WISL_Parser.prog read lexbuf with
  | SyntaxError msg ->
    Printf.fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | WISL_Parser.Error ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

(* part 1 *)
let rec parse_and_compile lexbuf =
  match parse_with_error lexbuf with
  | Some value -> begin
                   let cprog = compile_program value in
                    let str = JSIL_Print.string_of_ext_program cprog in
                    burn_to_disk "test.jsil" str
                  end
  | None -> Printf.fprintf stdout "No program"

let loop filename =
  let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_compile lexbuf;
  close_in inx

(* part 2: this needs to parse *)
let _ = loop "test.wisl"
