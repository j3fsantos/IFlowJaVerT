{
open Formula_parser  
open Batteries_uni
exception Lexing_failed of char      
}

let digit = ['0'-'9']

let letter = ['a'-'z''A'-'Z']

let id = letter+(letter|digit)*

let string_char = [^'"''\\']

rule token = parse
  | [' ' '\t' '\n']     { token lexbuf }
  | digit+ as lxm       { NUM(int_of_string lxm) }
  | '+'                 { PLUS }
  | '-'                 { MINUS }
  | '*'                 { STAR }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | '['                 { LBRACKET }
  | ']'                 { RBRACKET }
  | "|->"               { POINTSTO }
  | '|'                 { VBAR }
  | "@empty"            { EMPTY }
  | "@r"                { RETURN }
  | '='                 { EQ }
  | "!="                { NEQ }
  | ','                 { COMMA }
  | ':'                 { COLON }
  | ';'                 { SEMICOLON }
  | '.'                 { DOT }
  | "@lg"               { LG }
  | "@lop"              { LOP }
  | "@lfp"              { LFP }
  | "@l" digit+ as n    { LOC (int_of_string (String.tail n 2)) }
  | "@ahl" digit+ as n  { AHLOC (int_of_string (String.tail n 4)) }
  | "@aheaplets"        { AHEAPLETS }
  | "@plist"            { PLIST }
  | "@store"            { STORE }
  | "@apl" digit+ as n  { PLLOC (int_of_string (String.tail n 4)) }
  | "@sl" digit+ as n   { STORELOC (int_of_string (String.tail n 4)) }
  | "@obj"             { OBJFOOTPRINT }
  | "undefined"         { UNDEFINED }
  | "null"              { NULL }
  | "@null"             { LOC_NULL }
  | "true"              { TRUE }
  | "false"             { FALSE }
  | "@IsTrue"           { ISTRUE }
  | "@IsFalse"          { ISFALSE }
  | "@CScope"           { CSCOPE }
  | '?' id as n         { LE_VAR (String.tail n 1) }
  | id as s             { ID s }
  | '"' ((string_char|('\\' _))* as s) '"' { STRING s }
  | _ as c              { raise (Lexing_failed c) } (* Return position *)
  | eof                 { EOF }