open WISL_Utils
open WISL_Syntax
(* This is a very simple compiler *)


let compile_binop b = match b with
  | EQUAL -> BinOp.Equal
  | LESSTHAN -> BinOp.LessThan
	| LESSEQUAL -> BinOp.LessThanEqual
	| PLUS -> BinOp.Plus
	| MINUS -> BinOp.Minus
	| TIMES -> BinOp.Times
	| DIV -> BinOp.Div
	| MOD -> BinOp.Mod
	| AND -> BinOp.And
	| OR -> BinOp.Or
  | _ -> failwith "compile_binop should not be used to compile this operator"

let compile_unop u = match u with
  | NOT -> UnOp.Not

let compile_value v = match v with
  | Bool b -> Literal.Bool b
  | Null -> Literal.Null
  | Loc l -> Literal.Loc l
  | Num n -> Literal.Num (float_of_num n)
  | Str s -> Literal.String s

let is_special_binop b = match b with
  | NEQ | GREATERTHAN | GREATEREQUAL -> true
  | _ -> false

let rec compile_expression expr = match expr with
  | Val v -> JSIL_Syntax.Literal (compile_value v)
  | Var x -> JSIL_Syntax.Var x
  | BinOp (e1, b, e2) when is_special_binop b ->
    compile_special_binop (e1, b, e2)
  | BinOp (e1, b, e2) -> JSIL_Syntax.BinOp (compile_expression e1,
                         compile_binop b, compile_expression e2)
  | UnOp (u, e) -> JSIL_Syntax.UnOp (compile_unop u, compile_expression e)
and compile_special_binop (e1, b, e2) =
  let comp_e1 = compile_expression e1 in
  let comp_e2 = compile_expression e2 in
  match b with
  | NEQ -> 
      JSIL_Syntax.UnOp (
        UnOp.Not,
        JSIL_Syntax.BinOp (comp_e1, BinOp.Equal, comp_e2)
      )
  | GREATERTHAN ->
      JSIL_Syntax.UnOp (
        UnOp.Not,
        JSIL_Syntax.BinOp (comp_e1, BinOp.LessThanEqual, comp_e2)
      )
  | GREATEREQUAL ->
      JSIL_Syntax.UnOp (
        UnOp.Not,
        JSIL_Syntax.BinOp (comp_e1, BinOp.LessThan, comp_e2)
      )
  | _ -> failwith (Format.sprintf "This is not a special binary operator : %a"
            WISL_Printer.pp_binop b)
            
  