{
  open Batteries
  open Pulp_Parser
  open Printf
  
  exception Lexing_failed of char      

}

let digit = ['0'-'9']

let float = digit+ ('.' digit*)?

let letter = ['a'-'z''A'-'Z']

let id = letter+(letter|digit|'_')*

let lid = (letter|digit)+

let prid = '$'+(letter|'_')*

let string_char = [^'"''\\']

let string_char_quote = [^''''\\']

rule lex = parse
  | [' ' '\t' '\n']     { lex lexbuf }  (* eat up whitespaces *)
  | id as text          { ID text }
  | float as f          { NUM (float_of_string f) }
  | "label"             { LABEL }
  | "goto"              { GOTO }
  | "Skip"              { SKIP }
  | "if"                { IF }
  | "then"              { THEN }
  | "else"              { ELSE }
  | "end"               { END }
  | ":="                { DEFEQ }
  | '['                 { LBRACKET }
  | ']'                 { RBRACKET }
  | ';'                 { SEMICOLON }
  | ','                 { COMMA }
  | _ as c              { printf "Unrecognized character: %c\n" c; lex lexbuf }  (* DEBUG *)
  | eof                 { EOF }

