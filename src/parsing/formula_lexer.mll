{
  open Batteries_uni
  open Formula_parser  
  
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

rule token = parse
  | [' ' '\t' '\n']     { token lexbuf }
  | float as lxm       { NUM (float_of_string lxm) }
  | ":="                { DEFEQ }
  | '+'                 { PLUS }
  | '-'                 { MINUS }
  | '*'                 { STAR }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | '['                 { LBRACKET }
  | ']'                 { RBRACKET }
  | "|->"               { POINTSTO }
  | '|'                 { VBAR }
  | "\\/"               { OR }
  | "#(/)"              { EMPTY }
  | "#r"                { RETURN }
  | '='                 { EQ }
  | "!="                { NEQ }
  | ','                 { COMMA }
  | ':'                 { COLON }
  | ';'                 { SEMICOLON }
  | '.'                 { DOT }
  | "<="                { LE }
  | '<'                 { LT }
  | "#lg"               { LG }
  | "#lop"              { LOP }
  | "#lfp"              { LFP }
  | "_#l" (lid as n)    { LOC (Logic.EVar n) }
  | "#l" (lid as n)     { LOC (Logic.AVar n) }
  | "_#stl" (lid as n)  { AHLOC (Logic.EVar n) }
  | "#stl" (lid as n)   { AHLOC (Logic.AVar n) }
  | "#storelet"         { AHEAPLETS }
  | "#plist"            { PLIST }
  | "#store"            { STORE }
  | "_#pl" (lid as n)   { PLLOC (Logic.EVar n) }
  | "#pl" (lid as n)    { PLLOC (Logic.AVar n) }
  | "_#sl" (lid as n)   { STORELOC (Logic.EVar n) }
  | "#sl" (lid as n)    { STORELOC (Logic.AVar n) }
  | "#footprint"        { OBJFOOTPRINT }
  | "#obj"              { OBJECT }
  | "#undefined"         { UNDEFINED }
  | "null"              { NULL }
  | "#null"             { LOC_NULL }
  | "true"              { TRUE }
  | "false"             { FALSE }
  | "#isTrue"           { ISTRUE }
  | "#isFalse"          { ISFALSE }
  | "#cScope"           { CSCOPE }
  | "#proto"            { ID "#proto" }
  | "#this"             { ID "#this" }
  | "#body"             { ID "#body" }
  | "#scope"            { ID "#scope" }
  | "#fun"              { FUN }
  | "define"            { DEFINE }
  | '?' id as n         { LE_VAR (Logic.AVar (String.tail n 1)) }
  | '_' id as n         { LE_VAR (Logic.EVar (String.tail n 1)) }
  | id as s             { ID s }
  | prid as s           { PNAME (Logic.pname_from_string s) }
  | '"' ((string_char|('\\' _))* as s) '"'       { STRING s }
  | ''' ((string_char_quote|('\\' _))* as s) ''' { STRING s }
  | _ as c              { raise (Lexing_failed c) } (* Return position *) (* TODO : return a proper error message *)
  | eof                 { EOF }
