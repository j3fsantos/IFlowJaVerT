open SSyntax

type jsil_logic_var = string

type jsil_logic_val =
	| LLit				of jsil_lit
	| LNone
	| LListEmpty

type jsil_return_flag =
	| Normal
	| Error

type jsil_logic_expr =
	| LVal				of jsil_logic_val
	| LVar				of jsil_logic_var
	| PVar				of jsil_var
	| LBinOp			of jsil_logic_expr * bin_op * jsil_logic_expr
	| LUnOp				of unary_op * jsil_logic_expr
	| LVRef				of jsil_logic_expr * jsil_logic_expr
	| LORef				of jsil_logic_expr * jsil_logic_expr
	| LBase				of jsil_logic_expr
	| LField			of jsil_logic_expr
	| LTypeOf			of jsil_logic_expr
	| LCons				of jsil_logic_expr * jsil_logic_expr

type jsil_logic_assertion =
	| LAnd				of jsil_logic_assertion * jsil_logic_assertion
	| LOr					of jsil_logic_assertion * jsil_logic_assertion
	| LNot				of jsil_logic_assertion
	| LTrue
	| LFalse
	| LEq					of jsil_logic_expr * jsil_logic_expr
	| LLessEq			of jsil_logic_expr * jsil_logic_expr
	| LStar				of jsil_logic_assertion * jsil_logic_assertion
	| LPointTo		of jsil_logic_expr * jsil_logic_expr * jsil_logic_expr
	| LEmp
	| LExists			of (jsil_logic_var list) * jsil_logic_assertion
	| LForAll			of (jsil_logic_var list) * jsil_logic_assertion

type jsil_single_spec = {
	  pre : jsil_logic_assertion; 
		post : jsil_logic_assertion; 
		ret_flag : jsil_return_flag 
}

type jsil_spec = { 
    spec_name : string;
    spec_params : jsil_var list; 
		proc_specs : jsil_single_spec list
}
