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
  | '('                 { LBRACE }
  | ')'                 { RBRACE }
  | "true"              { TRUE }
  | "false"             { FALSE }
  | "null"              { NULL }
  | "undefined"         { UNDEFINED }
  | '='                 { EQUAL }
  | '<'                 { LT }
  | '+'                 { PLUS }
  | '-'                 { MINUS }
  | '*'                 { TIMES }
  | '/'                 { DIV }
  | '%'                 { MOD }
  | "and"               { AND }
  | "or"                { OR }
  | '&'                 { BITWISE_AND }
  | '^'                 { BITWISE_OR } (*TODO: same character as CONCAT *)
  | '|'                 { BITWISE_XOR }  
  | "<<"                { LEFT_SHIFT }
  | ">>"                { UNSIGNED_RIGHT_SHIFT }
  | ">>>"               { SIGNED_RIGHT_SHIFT }
(*  | "^"                 { CONCAT } *)
  | "not"               { NOT }
  | "num_to_string"     { TO_STRING }
  | "string_to_num"     { TO_NUM }
  | "num_to_int32"      { TO_INT32 }
  | "num_to_uint32"     { TO_UINT32 }
  | '!'                 { BITWISE_NOT }
  | ';'                 { SEMICOLON }
  | ','                 { COMMA }
  | "ref"               { REF }
  | "field"             { FIELD }
  | "base"              { BASE }
  | "typeOf"            { TYPEOF }
  | "\"o\""             { MEM_REF }
  | "\"v\""             { VAR_REF }
  | float as f          { NUM (float_of_string f) }
  | '"' ('\\'_ | [^ '\\' '"' ] )* '"' as text   { STRING text }
  | id as text          { ID text }
  | _ as c              { printf "Unrecognized character: %c\n" c; lex lexbuf }  (* DEBUG *)
  | eof                 { EOF }

