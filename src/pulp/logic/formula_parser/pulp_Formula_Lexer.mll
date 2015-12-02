{
  open Batteries
  open Pulp_Formula_Parser  
  
  exception Lexing_failed of string      
}

let digit = ['0'-'9']

let float = digit+ ('.' digit*)?

let letter = ['a'-'z''A'-'Z']

let id = letter+(letter|digit|'_')*

let lid = (letter|digit)+

let string_char = [^'"''\\']

let string_char_quote = [^''''\\']

rule token = parse
  | [' ' '\t' '\n']     { token lexbuf }
  | float as lxm        { NUM (float_of_string lxm) }
  | '+'                 { PLUS }
  | '^'                 { CONCAT }
  | '-'                 { MINUS }
  | '*'                 { STAR }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | '['                 { LBRACKET }
  | ']'                 { RBRACKET }
  | "|->"               { POINTSTO }
  | '|'                 { VBAR }
  | "\\/"               { OR }
  | "#(/)"              { NONE }
  | "#r"                { RETURN }
  | '='                 { EQ }
  | "!="                { NEQ }
  | "!"                 { NOT }
  | ','                 { COMMA }
  | ':'                 { COLON }
  | ';'                 { SEMICOLON }
  | '.'                 { DOT }
  | "<="                { LE }
  | '<'                 { LT }
  | "#GlobalObject"     { LG }
  | "#LObject"          { LOBJECT }
  | "#LString"          { LSTRING }
  | "#ObjectPrototype"  { LOP }
  | "#FunctionPrototype"{ LFP }
  | "#ReferenceErrorPrototype"{ LREP }
  | "#TypeErrorPrototype"{ LTEP }
  | "#footprint"        { OBJFOOTPRINT }
  | "#obj"              { OBJECT }
  | "#protoValue"       { PROTO_VALUE }
  | "#protoChain"       { PROTO_CHAIN }
  | "#protoPred"        { PROTO_PRED }
  | "#undefined"        { UNDEFINED }
  | "#empty"            { EMPTY }
  | "#ref"              { REF }
  | "#v"                { VREF }
  | "#o"                { OREF }
  | "#base"             { BASE }
  | "#field"            { FIELD }
  | "#typeof"           { TYPEOF }
  | "#Null"             { NULLTYPE }
  | "#Undefined"        { UNDEFINEDTYPE }
  | "#Boolean"          { BOOLEANTYPE }
  | "#String"           { STRINGTYPE }
  | "#Number"           { NUMBERTYPE }
  | "#Object"           { OBJECTTYPE }
  | "#NObject"          { OBJECTTYPENORMAL }
  | "#BObject"          { OBJECTTYPEBUILTIN }
  | "#Reference"        { REFERENCETYPE }
  | "#VReference"       { VREFERENCETYPE }
  | "#OReference"       { OREFERENCETYPE }
  | "null"              { NULL }
  | "true"              { TRUE }
  | "false"             { FALSE }
  | "#proto"            { STRING "#proto" }
  | "#fid"              { STRING "#fid" }
  | "#constructid"      { STRING "#constructid" }
  | "#scope"            { STRING "#scope" }
  | "#class"            { STRING "#class" }
  | "#object_construct"  { STRING "#object_construct" }
  | "#string_call"  { STRING "#string_call" }
  | '?' id as n         { LE_VAR (Pulp_Logic.AVar (String.tail n 1)) }
  | '_' id as n         { LE_VAR (Pulp_Logic.EVar (String.tail n 1)) }
  | id as s             { ID s }
  | '"' ((string_char|('\\' _))* as s) '"'       { STRING s }
  | ''' ((string_char_quote|('\\' _))* as s) ''' { STRING s }
  | "#" id as s              { raise (Lexing_failed ("Unknown Keyword : " ^ s)) }
  | _ as c              { raise (Lexing_failed ("Unknown Character : " ^ (Char.escaped c))) } 
  | eof                 { EOF }
