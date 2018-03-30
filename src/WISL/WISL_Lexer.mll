{
  open Lexing
  open WISL_Parser

  exception SyntaxError of string
  
  let _ = ()
}


let digit = ['0'-'9']
let letter = ['a'-'z''A'-'Z']
let identifier = letter(letter|digit|'_')*
let int = digit+
let float = digit+ '.' digit*
let loc = "$l" (letter|digit|'_')*
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"


rule read =
  parse
  | white    { read lexbuf }
  | newline  { new_line lexbuf; read lexbuf }
  | int      { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | float    { FLOAT (float_of_string (Lexing.lexeme lexbuf)) }
  | "true"   { TRUE }
  | "false"  { FALSE }
  | "null"   { NULL }
  | "while"  { WHILE }
  | "if"     { IF }
  | "else"   { ELSE }
  | "skip"   { SKIP }
  | "new"    { NEW }
  | "delete" { DELETE }
  | "function" { FUNCTION }
  | "return" { RETURN }
  | identifier { IDENTIFIER (Lexing.lexeme lexbuf) }
  | '"'      { read_string (Buffer.create 17) lexbuf }
  | '{'      { LCBRACE }
  | '}'      { RCBRACE }
  | '('      { LBRACE }
  | ')'      { RBRACE }
  | ":="     { ASSIGN }
  | ':'      { COLON }
  | '.'      { DOT }
  | ','      { COMMA }
  | ';'      { SEMICOLON }
  | '='      { EQUAL }
  | ">="     { GREATEREQUAL }
  | '>'      { GREATERTHAN }
  | '<'      { LESSTHAN }
  | "<="     { LESSEQUAL }
  | '+'      { PLUS }
  | '-'      { MINUS }
  | '*'      { TIMES }
  | '/'      { DIV }
  | '%'      { MOD }
  | "&&"     { AND }
  | "||"     { OR }
  | "!="     { NEQ }
  | '!'      { NOT }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof      { EOF }


and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }