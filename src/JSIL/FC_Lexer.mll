{
open Lexing
}

let digit = ['0'-'9']
let letter = ['a'-'z''A'-'Z']
let var = letter(letter|digit|'_')*
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read = parse
	| white       	       { read lexbuf }
	| newline	             { new_line lexbuf; read lexbuf }
	| var                  { FC_Parser.VAR (Lexing.lexeme lexbuf) }
	| ','                  { FC_Parser.COMMA }
	| eof                  { FC_Parser.EOF }
	| _                    { raise (JSIL_Syntax.Syntax_error ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }