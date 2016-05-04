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
let loc = "$l"(letter|digit|'_')*
let pvar = letter(letter|digit|'_')*
let lvar = '_' letter(letter|digit|'_')*
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read = parse
  | white       	       { read lexbuf }
	|	newline	             { next_line lexbuf; read lexbuf }
(* type literals *)	
	| "$$boolean_type"     { JSIL_Logic_Parser.BOOLTYPELIT }
	| "$$number_type"      { JSIL_Logic_Parser.NUMTYPELIT }
	| "$$string_type"      { JSIL_Logic_Parser.STRTYPELIT }
	| "$$object_type"      { JSIL_Logic_Parser.OBJTYPELIT }
	| "$$reference_type"   { JSIL_Logic_Parser.REFTYPELIT }
	| "$$v-reference_type" { JSIL_Logic_Parser.VREFTYPELIT }
	| "$$o-reference_type" { JSIL_Logic_Parser.OREFTYPELIT }
(* procedure keywords *)
	| "spec"     					 { JSIL_Logic_Parser.SPEC }
	| "normal"             { JSIL_Logic_Parser.NORMAL }
	| "error"              { JSIL_Logic_Parser.ERR }
	| "pre"								 { JSIL_Logic_Parser.PRE }
	| "post"							 { JSIL_Logic_Parser.POST }
	| "flag"							 { JSIL_Logic_Parser.FLAG }
(* expression keywords *)
	| "v-ref"              { JSIL_Logic_Parser.VREF }
	| "o-ref"              { JSIL_Logic_Parser.OREF }
	| "base"               { JSIL_Logic_Parser.BASE }
	| "field"              { JSIL_Logic_Parser.FIELD }
	| "typeOf"             { JSIL_Logic_Parser.TYPEOF }
	| "::"								 { JSIL_Logic_Parser.LCONS }
(* assertion keywords *)
	| "/\\"								 { JSIL_Logic_Parser.LAND }
	| "\\/"								 { JSIL_Logic_Parser.LOR }
	| "~"									 { JSIL_Logic_Parser.LNOT }
	| "true"							 { JSIL_Logic_Parser.LTRUE }
	| "false"							 { JSIL_Logic_Parser.LFALSE }
	| "=="								 { JSIL_Logic_Parser.LEQUAL }
	| "<=="								 { JSIL_Logic_Parser.LLESSTHANEQUAL }
	| "->"								 { JSIL_Logic_Parser.LARROW }
	| "emp"								 { JSIL_Logic_Parser.LEMP }
	| "exists"						 { JSIL_Logic_Parser.LEXISTS }
	| "forall"						 { JSIL_Logic_Parser.LFORALL }
(* binary operators *)
	| "="                  { JSIL_Logic_Parser.EQUAL }
	| "<"                  { JSIL_Logic_Parser.LESSTHAN }
	| "<="                 { JSIL_Logic_Parser.LESSTHANEQUAL }
	| "+"                  { JSIL_Logic_Parser.PLUS }
	| "-"                  { JSIL_Logic_Parser.MINUS }
	| "*"                  { JSIL_Logic_Parser.TIMES }
	| "/"                  { JSIL_Logic_Parser.DIV }
	| "%"                  { JSIL_Logic_Parser.MOD }
	| "<:"                 { JSIL_Logic_Parser.SUBTYPE }
	| "concat"             { JSIL_Logic_Parser.CONCAT }
	| "and"                { JSIL_Logic_Parser.AND }
	| "or"                 { JSIL_Logic_Parser.OR }
	| "&"                  { JSIL_Logic_Parser.BITWISEAND }
	| "|"                  { JSIL_Logic_Parser.BITWISEOR }
	| "^"                  { JSIL_Logic_Parser.BITWISEXOR }
	| "<<"                 { JSIL_Logic_Parser.LEFTSHIFT }
	| ">>"                 { JSIL_Logic_Parser.SIGNEDRIGHTSHIFT }
	| ">>>"                { JSIL_Logic_Parser.UNSIGNEDRIGHTSHIFT }
(* unary operators *)
	| "not"                { JSIL_Logic_Parser.NOT }
	| "num_to_string"      { JSIL_Logic_Parser.TOSTRING }
	| "string_to_num"      { JSIL_Logic_Parser.TONUMBER }
	| "num_to_int32"       { JSIL_Logic_Parser.TOINT32 }
	| "num_to_uint32"      { JSIL_Logic_Parser.TOUINT32 }
	| "!"                  { JSIL_Logic_Parser.BITWISENOT }
(* separators *)
	| ':'                  { JSIL_Logic_Parser.COLON }
	| ','                  { JSIL_Logic_Parser.COMMA }
	| ';'                  { JSIL_Logic_Parser.SCOLON }
	| '.'									 { JSIL_Logic_Parser.DOT }
	| '('                  { JSIL_Logic_Parser.LBRACE }
	| ')'                  { JSIL_Logic_Parser.RBRACE }
	| '['                  { JSIL_Logic_Parser.LBRACKET }
	| ']'                  { JSIL_Logic_Parser.RBRACKET }
	| '"'                  { read_string (Buffer.create 17) lexbuf }
(*literals*)
 	| "$$t"                { JSIL_Logic_Parser.TRUE }
  | "$$f"                { JSIL_Logic_Parser.FALSE }
	| "$$null"             { JSIL_Logic_Parser.NULL }
	| "$$undefined"        { JSIL_Logic_Parser.UNDEFINED }
	| "$$empty"            { JSIL_Logic_Parser.EMPTY }
	| "none"							 { JSIL_Logic_Parser.LNONE }
	| loc                  { JSIL_Logic_Parser.LOC (Lexing.lexeme lexbuf) }
	| pvar                 { JSIL_Logic_Parser.PVAR (Lexing.lexeme lexbuf) }
	| lvar                 { JSIL_Logic_Parser.LVAR (Lexing.lexeme lexbuf) }
  | int                  { JSIL_Logic_Parser.INT (int_of_string (Lexing.lexeme lexbuf)) }
  | float                { JSIL_Logic_Parser.FLOAT (float_of_string (Lexing.lexeme lexbuf)) }
	| eof                  { JSIL_Logic_Parser.EOF }
	| _   { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
(* read strings *)
and 
read_string buf =
  parse
  | '"'                  { JSIL_Logic_Parser.STRING (Buffer.contents buf) }
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
