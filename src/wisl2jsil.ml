open WISL_Lexer
open Lexing
open WISL_Printer
open Format

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
let rec parse_and_print lexbuf =
  match parse_with_error lexbuf with
  | Some value -> pp_prog std_formatter value
  | None -> Printf.fprintf stdout "No program"

let loop filename =
  let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf;
  close_in inx

(* part 2: this needs to parse *)
let _ = loop "test.wisl"
