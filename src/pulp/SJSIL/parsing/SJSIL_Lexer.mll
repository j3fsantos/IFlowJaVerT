{
open Lexing

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }

}

let digit = ['0'-'9']
let float = '-'? digit+ ('.' digit*)?
let letter = ['a'-'z''A'-'Z']
let var = (letter|'_')(letter|digit|'_')*
let lvar = '#' (letter|digit|'_'|'$')*
let loc = "$l" (letter|digit|'_')*
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read = parse
  | white       	       { read lexbuf }
	|	newline	             { next_line lexbuf; read lexbuf }
(* Type literals *)
  | "$$undefined_type"   { SJSIL_Parser.UNDEFTYPELIT }
	| "$$null_type"        { SJSIL_Parser.NULLTYPELIT }
	| "$$empty_type"       { SJSIL_Parser.EMPTYTYPELIT }
	| "$$boolean_type"     { SJSIL_Parser.BOOLTYPELIT }
	| "$$number_type"      { SJSIL_Parser.NUMTYPELIT }
	| "$$string_type"      { SJSIL_Parser.STRTYPELIT }
	| "$$object_type"      { SJSIL_Parser.OBJTYPELIT }
	| "$$reference_type"   { SJSIL_Parser.REFTYPELIT }
	| "$$o-reference_type" { SJSIL_Parser.OREFTYPELIT }
	| "$$v-reference_type" { SJSIL_Parser.VREFTYPELIT }
	| "$$list_type"        { SJSIL_Parser.LISTTYPELIT }
	| "$$type_type"        { SJSIL_Parser.TYPETYPELIT }
(* Constants *)
  | "$$min_float"        { SJSIL_Parser.MIN_FLOAT }
	| "$$max_float"        { SJSIL_Parser.MAX_FLOAT }
	| "$$random"           { SJSIL_Parser.RANDOM } 
	| "$$e"                { SJSIL_Parser.E }
	| "$$ln10"             { SJSIL_Parser.LN10 }
	| "$$ln2"              { SJSIL_Parser.LN2 }
	| "$$log2e"            { SJSIL_Parser.LOG2E }
	| "$$log10e"           { SJSIL_Parser.LOG10E }
	| "$$pi"               { SJSIL_Parser.PI }
	| "$$sqrt1_2"          { SJSIL_Parser.SQRT1_2 }
	| "$$sqrt2"            { SJSIL_Parser.SQRT2 }
(* Literals (scroll down for more) *)
	| "$$undefined"        { SJSIL_Parser.UNDEFINED }
	| "$$null"             { SJSIL_Parser.NULL }
	| "$$empty"            { SJSIL_Parser.EMPTY } 
 	| "$$t"                { SJSIL_Parser.TRUE }
  | "$$f"                { SJSIL_Parser.FALSE }
	| "nan"                { SJSIL_Parser.NAN }
	| "inf"                { SJSIL_Parser.INFINITY }
	| ".v."                { SJSIL_Parser.VREFLIT }
  | ".o."                { SJSIL_Parser.OREFLIT }
  | "$$nil"              { SJSIL_Parser.LSTNIL }
  | "{{"                 { SJSIL_Parser.LSTOPEN }
  | "}}"                 { SJSIL_Parser.LSTCLOSE }
(* Binary operators *)
	| "="                  { SJSIL_Parser.EQUAL }
	| "<"                  { SJSIL_Parser.LESSTHAN }
	| "<s"                 { SJSIL_Parser.LESSTHANSTRING }
	| "<="                 { SJSIL_Parser.LESSTHANEQUAL }
	| "+"                  { SJSIL_Parser.PLUS }
	| "-"                  { SJSIL_Parser.MINUS }
	| "*"                  { SJSIL_Parser.TIMES }
	| "/"                  { SJSIL_Parser.DIV }
	| "%"                  { SJSIL_Parser.MOD }
	| "and"                { SJSIL_Parser.AND }
	| "or"                 { SJSIL_Parser.OR }
	| "&"                  { SJSIL_Parser.BITWISEAND }
	| "|"                  { SJSIL_Parser.BITWISEOR }
	| "^"                  { SJSIL_Parser.BITWISEXOR }
	| "<<"                 { SJSIL_Parser.LEFTSHIFT }
	| ">>"                 { SJSIL_Parser.SIGNEDRIGHTSHIFT }
	| ">>>"                { SJSIL_Parser.UNSIGNEDRIGHTSHIFT }
	| "m_atan2"            { SJSIL_Parser.M_ATAN2 }
	| "**"                 { SJSIL_Parser.M_POW }
	| "<:"                 { SJSIL_Parser.SUBTYPE }
	| "::"                 { SJSIL_Parser.LSTCONS }
	| "@"                  { SJSIL_Parser.LSTCAT }
	| "++"                 { SJSIL_Parser.STRCAT }
(* Unary operators *)
	(* Unary minus uses the same symbol as binary minus, token MINUS *)
	| "not"                { SJSIL_Parser.NOT }
	| "~"                  { SJSIL_Parser.BITWISENOT }
	| "m_abs"              { SJSIL_Parser.M_ABS }
	| "m_acos"             { SJSIL_Parser.M_ACOS }
	| "m_asin"             { SJSIL_Parser.M_ASIN }
	| "m_atan"             { SJSIL_Parser.M_ATAN }
	| "m_ceil"             { SJSIL_Parser.M_CEIL }
	| "m_cos"              { SJSIL_Parser.M_COS }
	| "m_exp"              { SJSIL_Parser.M_EXP }
	| "m_floor"            { SJSIL_Parser.M_FLOOR }
	| "m_log"              { SJSIL_Parser.M_LOG }
	| "m_round"            { SJSIL_Parser.M_ROUND }
  | "m_sgn"              { SJSIL_Parser.M_SGN }
	| "m_sin"              { SJSIL_Parser.M_SIN }
	| "m_sqrt"             { SJSIL_Parser.M_SQRT }
	| "m_tan"              { SJSIL_Parser.M_TAN }
	| "is_primitive"       { SJSIL_Parser.ISPRIMITIVE }
	| "num_to_string"      { SJSIL_Parser.TOSTRING }
	| "num_to_int"         { SJSIL_Parser.TOINT }
	| "num_to_uint16"      { SJSIL_Parser.TOUINT16 }
	| "num_to_int32"       { SJSIL_Parser.TOINT32 }
	| "num_to_uint32"      { SJSIL_Parser.TOUINT32 }
	| "string_to_num"      { SJSIL_Parser.TONUMBER }
	| "car"                { SJSIL_Parser.CAR }
	| "cdr"                { SJSIL_Parser.CDR }
  | "l-len"              { SJSIL_Parser.LSTLEN }
	| "s-len"              { SJSIL_Parser.STRLEN }
(* Expression keywords *)
	| "v-ref"              { SJSIL_Parser.VREF }
	| "o-ref"              { SJSIL_Parser.OREF }
	| "base"               { SJSIL_Parser.BASE }
	| "field"              { SJSIL_Parser.FIELD }
	| "typeOf"             { SJSIL_Parser.TYPEOF }
  |	"assume"             { SJSIL_Parser.ASSUME }
	| "assert"             { SJSIL_Parser.ASSERT }
	| "make-symbol-number" { SJSIL_Parser.RNUMSYM }
	| "make-symbol-string" { SJSIL_Parser.RSTRSYM }
	| "l-nth"              { SJSIL_Parser.LSTNTH }
	| "s-nth"              { SJSIL_Parser.STRNTH }
(* Command keywords *)
  | "skip"               { SJSIL_Parser.SKIP }
	| ":="                 { SJSIL_Parser.DEFEQ }
	| "new"                { SJSIL_Parser.NEW }
	| "delete"             { SJSIL_Parser.DELETE }
	| "hasField"           { SJSIL_Parser.HASFIELD }
	| "getFields"          { SJSIL_Parser.GETFIELDS }
	| "args"               { SJSIL_Parser.ARGUMENTS }
	| "goto"               { SJSIL_Parser.GOTO }
	| "with"               { SJSIL_Parser.WITH }
	| "apply"              { SJSIL_Parser.APPLY }
  | "PHI"                { SJSIL_Parser.PHI }
  | "PSI"                { SJSIL_Parser.PSI }
(* Logical expressions: most match with the program expressions *)
	| "None"							 { SJSIL_Parser.LNONE }
(* Logic assertions *)
	| "[["                 { SJSIL_Parser.OASSERT }
  | "]]"                 { SJSIL_Parser.CASSERT }
	| "/\\"								 { SJSIL_Parser.LAND }
	| "\\/"								 { SJSIL_Parser.LOR }
	| "!"									 { SJSIL_Parser.LNOT }
	| "true"							 { SJSIL_Parser.LTRUE }
	| "false"							 { SJSIL_Parser.LFALSE }
	| "=="								 { SJSIL_Parser.LEQUAL }
	| "<=="								 { SJSIL_Parser.LLESSTHANEQUAL }
	| "->"								 { SJSIL_Parser.LARROW }
	| "emp"								 { SJSIL_Parser.LEMP }
	| "exists"						 { SJSIL_Parser.LEXISTS }
	| "forall"						 { SJSIL_Parser.LFORALL }
  | "types"              { SJSIL_Parser.LTYPES }
(* Logic predicates *)
	| "pred"							 { SJSIL_Parser.PRED }
(* Procedure specification keywords *)
	| "spec"     					 { SJSIL_Parser.SPEC }
	| "normal"             { SJSIL_Parser.NORMAL }
	| "error"              { SJSIL_Parser.ERROR }
(* Procedure definition keywords *)
	| "proc"     					 { SJSIL_Parser.PROC }
	| "ret"                { SJSIL_Parser.RET }
	| "err"                { SJSIL_Parser.ERR }
(* Others *)
	| "import"     				 { SJSIL_Parser.IMPORT }
(* Separators *)
  | "(*"                 { read_comment lexbuf }
	| ','                  { SJSIL_Parser.COMMA }
	| ':'                  { SJSIL_Parser.COLON }
	| ';'                  { SJSIL_Parser.SCOLON }
	| '.'									 { SJSIL_Parser.DOT }
	| '('                  { SJSIL_Parser.LBRACE }
	| ')'                  { SJSIL_Parser.RBRACE }
	| '['                  { SJSIL_Parser.LBRACKET }
	| ']'                  { SJSIL_Parser.RBRACKET }
	| '{'                  { SJSIL_Parser.CLBRACKET }
	| '}'                  { SJSIL_Parser.CRBRACKET }
(* Literals (cont.) *)
  | float                { SJSIL_Parser.FLOAT (float_of_string (Lexing.lexeme lexbuf)) }
  | '"'                  { read_string (Buffer.create 17) lexbuf }
	| loc                  { SJSIL_Parser.LOC (Lexing.lexeme lexbuf) }
(* Variables *)
	| var                  { SJSIL_Parser.VAR (Lexing.lexeme lexbuf) }
(* Logic variables *)
	| lvar                 { SJSIL_Parser.LVAR (Lexing.lexeme lexbuf) }
(* EOF *)
	| eof                  { SJSIL_Parser.EOF }
	| _                    { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
and
(* Read strings *)
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
  | '\\' '\"'            { Buffer.add_char buf '\"'; read_string buf lexbuf }
  | [^ '"' '\\']+        { 
		                       Buffer.add_string buf (Lexing.lexeme lexbuf);
    											 read_string buf lexbuf
    			               }
  | _                    { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof                  { raise (SyntaxError ("String is not terminated")) }
and
(* Read comments *)
read_comment =
  parse
	| "*)"                 { read lexbuf }
	| eof                  { raise (SyntaxError ("Comment is not terminated")) }
	| _                    { read_comment lexbuf }
	