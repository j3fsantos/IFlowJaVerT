{
open Lexing
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
	|	newline	             { new_line lexbuf; read lexbuf }
(* js logic tokens *)
	| "scope"                       { JSIL_Parser.SCOPE     }
	| "this"                        { JSIL_Parser.THIS      }
	| "fun_obj"                     { JSIL_Parser.FUNOBJ    }
	| "closure"                     { JSIL_Parser.CLOSURE   }
	| "sc_scope"                    { JSIL_Parser.SCSCOPE   }
	| "o_chains"                    { JSIL_Parser.OCHAINS   }
	| "overlaps_with_current_scope" { JSIL_Parser.OCS       }
(* Type literals *)
	| "$$undefined_type"   { JSIL_Parser.UNDEFTYPELIT  }
	| "$$null_type"        { JSIL_Parser.NULLTYPELIT   }
	| "$$empty_type"       { JSIL_Parser.EMPTYTYPELIT  }
	| "$$none_type"        { JSIL_Parser.NONETYPELIT   }
	| "$$boolean_type"     { JSIL_Parser.BOOLTYPELIT   }
	| "$$number_type"      { JSIL_Parser.NUMTYPELIT    }
	| "$$string_type"      { JSIL_Parser.STRTYPELIT    }
	| "$$object_type"      { JSIL_Parser.OBJTYPELIT    }
	| "$$list_type"        { JSIL_Parser.LISTTYPELIT   }
	| "$$type_type"        { JSIL_Parser.TYPETYPELIT   }
	| "$$set_type"         { JSIL_Parser.SETTYPELIT    }
(* Constants *)
	| "$$min_float"        { JSIL_Parser.MIN_FLOAT     }
	| "$$max_float"        { JSIL_Parser.MAX_FLOAT     }
	| "$$random"           { JSIL_Parser.RANDOM        }
	| "$$e"                { JSIL_Parser.E             }
	| "$$ln10"             { JSIL_Parser.LN10          }
	| "$$ln2"              { JSIL_Parser.LN2           }
	| "$$log2e"            { JSIL_Parser.LOG2E         }
	| "$$log10e"           { JSIL_Parser.LOG10E        }
	| "$$pi"               { JSIL_Parser.PI            }
	| "$$sqrt1_2"          { JSIL_Parser.SQRT1_2       }
	| "$$sqrt2"            { JSIL_Parser.SQRT2         }
	| "$$UTCTime"          { JSIL_Parser.UTCTIME       }
	| "$$LocalTime"        { JSIL_Parser.LOCALTIME     }
(* Literals (scroll down for more) *)
	| "$$undefined"        { JSIL_Parser.UNDEFINED     }
	| "$$null"             { JSIL_Parser.NULL          }
	| "$$empty"            { JSIL_Parser.EMPTY         }
 	| "$$t"                { JSIL_Parser.TRUE          }
	| "$$f"                { JSIL_Parser.FALSE         }
	| "nan"                { JSIL_Parser.NAN           }
	| "inf"                { JSIL_Parser.INFINITY      }
	| "$$nil"              { JSIL_Parser.LSTNIL        }
	| "{{"                 { JSIL_Parser.LSTOPEN       }
	| "}}"                 { JSIL_Parser.LSTCLOSE      }
(* Binary operators *)
	| "="                  { JSIL_Parser.EQUAL         }
	| "<"                  { JSIL_Parser.LESSTHAN      }
	| "<="                 { JSIL_Parser.LESSTHANEQUAL }
	| "<s"                 { JSIL_Parser.LESSTHANSTRING}
	| "+"                  { JSIL_Parser.PLUS          }
	| "-"                  { JSIL_Parser.MINUS         }
	| "*"                  { JSIL_Parser.TIMES         }
	| "/"                  { JSIL_Parser.DIV           }
	| "%"                  { JSIL_Parser.MOD           }
	| "and"                { JSIL_Parser.AND           }
	| "or"                 { JSIL_Parser.OR            }
	| "&"                  { JSIL_Parser.BITWISEAND    }
	| "|"                  { JSIL_Parser.BITWISEOR     }
	| "^"                  { JSIL_Parser.BITWISEXOR    }
	| "<<"                 { JSIL_Parser.LEFTSHIFT     }
	| ">>"                 { JSIL_Parser.SIGNEDRIGHTSHIFT }
	| ">>>"                { JSIL_Parser.UNSIGNEDRIGHTSHIFT }
	| "m_atan2"            { JSIL_Parser.M_ATAN2       }
	| "**"                 { JSIL_Parser.M_POW         }
	| "::"                 { JSIL_Parser.LSTCONS       }
	| "@"                  { JSIL_Parser.LSTCAT        }
	| "++"                 { JSIL_Parser.STRCAT        }
	| "-u-"                { JSIL_Parser.SETUNION      }
	| "-i-"                { JSIL_Parser.SETINTER      }
	| "-d-"                { JSIL_Parser.SETDIFF       }
	| "-e-"                { JSIL_Parser.SETMEM        }
	| "-s-"                { JSIL_Parser.SETSUB        }
	| "--e--"              { JSIL_Parser.LSETMEM       }
	| "--s--"              { JSIL_Parser.LSETSUB       }
	| "-{"                 { JSIL_Parser.SETOPEN       }
	| "}-"                 { JSIL_Parser.SETCLOSE      }
(* Unary operators *)
	(* Unary minus uses the same symbol as binary minus, token MINUS *)
	| "not"                { JSIL_Parser.NOT           }
	| "~"                  { JSIL_Parser.BITWISENOT    }
	| "m_abs"              { JSIL_Parser.M_ABS         }
	| "m_acos"             { JSIL_Parser.M_ACOS        }
	| "m_asin"             { JSIL_Parser.M_ASIN        }
	| "m_atan"             { JSIL_Parser.M_ATAN        }
	| "m_ceil"             { JSIL_Parser.M_CEIL        }
	| "m_cos"              { JSIL_Parser.M_COS         }
	| "m_exp"              { JSIL_Parser.M_EXP         }
	| "m_floor"            { JSIL_Parser.M_FLOOR       }
	| "m_log"              { JSIL_Parser.M_LOG         }
	| "m_round"            { JSIL_Parser.M_ROUND       }
	| "m_sgn"              { JSIL_Parser.M_SGN         }
	| "m_sin"              { JSIL_Parser.M_SIN }
	| "m_sqrt"             { JSIL_Parser.M_SQRT }
	| "m_tan"              { JSIL_Parser.M_TAN }
	| "is_primitive"       { JSIL_Parser.ISPRIMITIVE }
	| "num_to_string"      { JSIL_Parser.TOSTRING }
	| "num_to_int"         { JSIL_Parser.TOINT }
	| "num_to_uint16"      { JSIL_Parser.TOUINT16 }
	| "num_to_int32"       { JSIL_Parser.TOINT32 }
	| "num_to_uint32"      { JSIL_Parser.TOUINT32 }
	| "string_to_num"      { JSIL_Parser.TONUMBER }
	| "car"                { JSIL_Parser.CAR }
	| "cdr"                { JSIL_Parser.CDR }
	| "l-len"              { JSIL_Parser.LSTLEN }
	| "s-len"              { JSIL_Parser.STRLEN }
(* Expression keywords *)
	| "typeOf"             { JSIL_Parser.TYPEOF }
	| "assume"             { JSIL_Parser.ASSUME }
	| "assert"             { JSIL_Parser.ASSERT }
	| "make-symbol-number" { JSIL_Parser.RNUMSYM }
	| "make-symbol-string" { JSIL_Parser.RSTRSYM }
	| "l-nth"              { JSIL_Parser.LSTNTH }
	| "s-nth"              { JSIL_Parser.STRNTH }
(* Command keywords *)
	| "skip"               { JSIL_Parser.SKIP }
	| ":="                 { JSIL_Parser.DEFEQ }
	| "new"                { JSIL_Parser.NEW }
	| "delete"             { JSIL_Parser.DELETE }
	| "deleteObject"       { JSIL_Parser.DELETEOBJ }
	| "hasField"           { JSIL_Parser.HASFIELD }
	| "getFields"          { JSIL_Parser.GETFIELDS }
	| "args"               { JSIL_Parser.ARGUMENTS }
	| "goto"               { JSIL_Parser.GOTO }
	| "with"               { JSIL_Parser.WITH }
	| "apply"              { JSIL_Parser.APPLY }
	| "PHI"                { JSIL_Parser.PHI }
	| "PSI"                { JSIL_Parser.PSI }
(* Logical expressions: most match with the program expressions *)
	| "None"               { JSIL_Parser.LNONE }
(* Logic assertions *)
	| "[["                 { JSIL_Parser.OASSERT }
	| "]]"                 { JSIL_Parser.CASSERT }
	| "/\\"                { JSIL_Parser.LAND }
	| "\\/"                { JSIL_Parser.LOR }
	| "!"                  { JSIL_Parser.LNOT }
	| "true"               { JSIL_Parser.LTRUE }
	| "false"              { JSIL_Parser.LFALSE }
	| "=="                 { JSIL_Parser.LEQUAL }
	| "<#"                 { JSIL_Parser.LLESSTHAN       }
	| "<=#"                { JSIL_Parser.LLESSTHANEQUAL  }
	| "<s#"                { JSIL_Parser.LLESSTHANSTRING }
	(* Separating conjunction uses the same symbol as product, token TIMES *)
	| "->"                 { JSIL_Parser.LARROW      }
	| "emp"                { JSIL_Parser.LEMP        }
	| "types"              { JSIL_Parser.LTYPES      }
	| "forall"             { JSIL_Parser.LFORALL     }
	| "empty_fields"       { JSIL_Parser.EMPTYFIELDS }
(* Logic predicates *)
	| "pred"               { JSIL_Parser.PRED }
(* Logic commands *)
	| "[*"                 { JSIL_Parser.OLCMD     }
	| "*]"                 { JSIL_Parser.CLCMD     }
	| "[+"                 { JSIL_Parser.OOLCMD    }
	| "+]"                 { JSIL_Parser.CCLCMD    }
	| "unfold*"            { JSIL_Parser.RECUNFOLD }
	| "fold"               { JSIL_Parser.FOLD      }
	| "unfold"             { JSIL_Parser.UNFOLD    }
	| "callspec"           { JSIL_Parser.CALLSPEC  }
	| "if"                 { JSIL_Parser.LIF       }
	| "then"               { JSIL_Parser.LTHEN     }
	| "else"               { JSIL_Parser.LELSE     }
(* Procedure specification keywords *)
  | "only"               { JSIL_Parser.ONLY      }
	| "spec"               { JSIL_Parser.SPEC      }
	| "normal"             { JSIL_Parser.NORMAL    }
	| "error"              { JSIL_Parser.ERROR     }
(* JS only spec specifics *)
	| "js_only_spec"       { JSIL_Parser.JSOS      }
	| "pre:"               { JSIL_Parser.JSOSPRE   }
	| "post:"              { JSIL_Parser.JSOSPOST  }
	| "outcome:"           { JSIL_Parser.JSOSOUT   }
(* Procedure definition keywords *)
	| "proc"               { JSIL_Parser.PROC      }
	| "ret"                { JSIL_Parser.RET       }
	| "err"                { JSIL_Parser.ERR       }
(* Others *)
	| "import"             { JSIL_Parser.IMPORT    }
	| "macro"              { JSIL_Parser.MACRO     }
(* Separators *)
	| "(*"                 { read_comment lexbuf   }
	| '.'                  { JSIL_Parser.DOT       }
	| ','                  { JSIL_Parser.COMMA     }
	| ':'                  { JSIL_Parser.COLON     }
	| ';'                  { JSIL_Parser.SCOLON    }
	| '('                  { JSIL_Parser.LBRACE    }
	| ')'                  { JSIL_Parser.RBRACE    }
	| '['                  { JSIL_Parser.LBRACKET  }
	| ']'                  { JSIL_Parser.RBRACKET  }
	| '{'                  { JSIL_Parser.CLBRACKET }
	| '}'                  { JSIL_Parser.CRBRACKET }
(* Literals (cont.) *)
	| float                { let n = float_of_string (Lexing.lexeme lexbuf) in
	                           JSIL_Parser.FLOAT n }
	| '"'                  { read_string (Buffer.create 17) lexbuf }
	| loc                  { JSIL_Parser.LOC (Lexing.lexeme lexbuf) }
(* Variables *)
	| var                  { JSIL_Parser.VAR (Lexing.lexeme lexbuf) }
(* Logic variables *)
	| lvar                 { JSIL_Parser.LVAR (Lexing.lexeme lexbuf) }
(* EOF *)
	| eof                  { JSIL_Parser.EOF }
	| _                    { raise (JSIL_Syntax.Syntax_error ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
and
(* Read strings *)
read_string buf =
  parse
  | '"'                  { JSIL_Parser.STRING (Buffer.contents buf) }
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
  | _                    { raise (JSIL_Syntax.Syntax_error ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof                  { raise (JSIL_Syntax.Syntax_error ("String is not terminated")) }
and
(* Read comments *)
read_comment =
  parse
	| "*)"                 { read lexbuf }
	| eof                  { raise (JSIL_Syntax.Syntax_error ("Comment is not terminated")) }
	| _                    { read_comment lexbuf }
