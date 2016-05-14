{
open Lexing

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }

exception SyntaxError of string

}

let digit = ['0'-'9']
let int = '-'? digit+
let float = digit+ ('.' digit*)?
let letter = ['a'-'z''A'-'Z']
let var = letter+(letter|digit|'_')*
let loc = "$l"(letter|digit|'_')*
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read = parse
  | white       	       { read lexbuf }
	|	newline	             { next_line lexbuf; read lexbuf }
(* type literals *)	
	| "$$boolean_type"     { SJSIL_Parser.BOOLTYPELIT }
	| "$$number_type"      { SJSIL_Parser.NUMTYPELIT }
	| "$$string_type"      { SJSIL_Parser.STRTYPELIT }
	| "$$object_type"      { SJSIL_Parser.OBJTYPELIT }
	| "$$reference_type"   { SJSIL_Parser.REFTYPELIT }
	| "$$v-reference_type" { SJSIL_Parser.VREFTYPELIT }
	| "$$o-reference_type" { SJSIL_Parser.OREFTYPELIT }
(* procedure keywords *)
	| "proc"     					 { SJSIL_Parser.PROC }
	| "ret"                { SJSIL_Parser.RET }
	| "err"                { SJSIL_Parser.ERR }
(* command keywords *)
	| "goto"               { SJSIL_Parser.GOTO }
  | "skip"               { SJSIL_Parser.SKIP }
	| ":="                 { SJSIL_Parser.DEFEQ }
	| "new"                { SJSIL_Parser.NEW }
	| "delete"             { SJSIL_Parser.DELETE }
	| "hasField"           { SJSIL_Parser.HASFIELD }
	| "protoField"         { SJSIL_Parser.PROTOFIELD }
	| "protoObj"           { SJSIL_Parser.PROTOOBJ }
	| "with"               { SJSIL_Parser.WITH }
(* expression keywords *)
	| "v-ref"              { SJSIL_Parser.VREF }
	| "o-ref"              { SJSIL_Parser.OREF }
	| "base"               { SJSIL_Parser.BASE }
	| "field"              { SJSIL_Parser.FIELD }
	| "typeOf"             { SJSIL_Parser.TYPEOF }
(* binary operators *)
	| "="                  { SJSIL_Parser.EQUAL }
	| "<"                  { SJSIL_Parser.LESSTHAN }
	| "<="                 { SJSIL_Parser.LESSTHANEQUAL }
	| "+"                  { SJSIL_Parser.PLUS }
	| "-"                  { SJSIL_Parser.MINUS }
	| "*"                  { SJSIL_Parser.TIMES }
	| "/"                  { SJSIL_Parser.DIV }
	| "%"                  { SJSIL_Parser.MOD }
	| "<:"                 { SJSIL_Parser.SUBTYPE }
	| "concat"             { SJSIL_Parser.CONCAT }
	| "and"                { SJSIL_Parser.AND }
	| "or"                 { SJSIL_Parser.OR }
	| "&"                  { SJSIL_Parser.BITWISEAND }
	| "|"                  { SJSIL_Parser.BITWISEOR }
	| "^"                  { SJSIL_Parser.BITWISEXOR }
	| "<<"                 { SJSIL_Parser.LEFTSHIFT }
	| ">>"                 { SJSIL_Parser.SIGNEDRIGHTSHIFT }
	| ">>>"                { SJSIL_Parser.UNSIGNEDRIGHTSHIFT }
(* unary operators *)
	| "not"                { SJSIL_Parser.NOT }
	| "num_to_string"      { SJSIL_Parser.TOSTRING }
	| "string_to_num"      { SJSIL_Parser.TONUMBER }
	| "num_to_int32"       { SJSIL_Parser.TOINT32 }
	| "num_to_uint32"      { SJSIL_Parser.TOUINT32 }
	| "!"                  { SJSIL_Parser.BITWISENOT }
(* separators *)
  | "(*"                 { read_comment lexbuf }
	| ':'                  { SJSIL_Parser.COLON }
	| ','                  { SJSIL_Parser.COMMA }
	| ';'                  { SJSIL_Parser.SCOLON }
	| '('                  { SJSIL_Parser.LBRACE }
	| ')'                  { SJSIL_Parser.RBRACE }
	| '['                  { SJSIL_Parser.LBRACKET }
	| ']'                  { SJSIL_Parser.RBRACKET }
	| '{'                  { SJSIL_Parser.CLBRACKET }
	| '}'                  { SJSIL_Parser.CRBRACKET }
	| '"'                  { read_string (Buffer.create 17) lexbuf }
(*literals*)
 	| "$$t"                { SJSIL_Parser.TRUE }
  | "$$f"                { SJSIL_Parser.FALSE }
	| "$$null"             { SJSIL_Parser.NULL }
	| "$$undefined"        { SJSIL_Parser.UNDEFINED }
	| "$$empty"            { SJSIL_Parser.EMPTY } 
	| var                  { SJSIL_Parser.VAR (Lexing.lexeme lexbuf) }
	| loc                  { SJSIL_Parser.LOC (Lexing.lexeme lexbuf) }
  | int                  { SJSIL_Parser.INT (int_of_string (Lexing.lexeme lexbuf)) }
  | float                { SJSIL_Parser.FLOAT (float_of_string (Lexing.lexeme lexbuf)) }
	| eof                  { SJSIL_Parser.EOF }
	| _   { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
(* read strings *)
and 
read_string buf =
  parse
  | '"'                  { SJSIL_Parser.STRING (Buffer.contents buf) }
  | '\\' '/'             { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\'            { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'             { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'             { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'             { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'             { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'             { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+        { 
		                       Buffer.add_string buf (Lexing.lexeme lexbuf);
    											 read_string buf lexbuf
    			               }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }
and 
read_comment =
  parse
	| "*)"                 { SJSIL_Parser.COMMENT }
	| eof { raise (SyntaxError ("Comment is not terminated")) }
	| _                    { read_comment lexbuf }
	