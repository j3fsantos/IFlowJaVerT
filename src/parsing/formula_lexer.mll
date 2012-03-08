{
open Formula_parser  
exception Lexing_failed of char      
}

let digit = ['0'-'9']

let letter = ['a'-'z''A'-'Z']

rule token = parse
  | [' ' '\t' '\n']     { token lexbuf }
  | digit+ as lxm   { NUM(int_of_string lxm) }
  | '+'             { PLUS }
  | '-'             { MINUS }
  | '*'             { STAR }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | "|->"           { POINTSTO }
  | '|'             { VBAR }
  | "empty"         { EMPTY }
  | '='             { EQ }
  | ','             { COMMA }
  | "lg"            { LG }
  | "lop"           { LOP }
  | "lfp"           { LFP }
  | "l" digit+ as n { LOC (int_of_string (String.sub n 1 (String.length n- 1))) }
  | letter+ as s    { ID s }
  | _ as c          { raise (Lexing_failed c) } (* Return position *)
  | eof             { EOF }