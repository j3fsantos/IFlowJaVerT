open SSyntax

type jsil_logic_var = string

type jsil_logic_expr =
	| LLit				of jsil_lit
	| LNone
	| LListEmpty
	| LVar				of jsil_logic_var
	| LLVar				of jsil_logic_var
	| PVar				of jsil_var
	| LBinOp			of jsil_logic_expr * bin_op * jsil_logic_expr
	| LUnOp				of unary_op * jsil_logic_expr
	| LEVRef			of jsil_logic_expr * jsil_logic_expr
	| LEORef			of jsil_logic_expr * jsil_logic_expr
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
	| LPointsTo		of jsil_logic_expr * jsil_logic_expr * jsil_logic_expr
	| LEmp
	| LExists			of (jsil_logic_var list) * jsil_logic_assertion
	| LForAll			of (jsil_logic_var list) * jsil_logic_assertion

type jsil_return_flag =
	| Normal
	| Error


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

type jsil_n_single_spec = {
	  n_pre :  ((string, ((jsil_logic_expr * jsil_logic_expr) list)) Hashtbl.t) * ((string, jsil_logic_expr) Hashtbl.t) * (jsil_logic_assertion DynArray.t); 
		n_post : ((string, ((jsil_logic_expr * jsil_logic_expr) list)) Hashtbl.t) * ((string, jsil_logic_expr) Hashtbl.t) * (jsil_logic_assertion DynArray.t); 
		n_ret_flag : jsil_return_flag 
}

type jsil_n_spec = { 
    n_spec_name : string;
    n_spec_params : jsil_var list; 
		n_proc_specs : jsil_n_single_spec list
}



(** 
 * We use integers to represent both abstract and concrete locations
*)

type abstract_heap = {
	aheap: (string, ((jsil_logic_expr * jsil_logic_expr) list)) Hashtbl.t; 
	mutable count: int; 
	parent: abstract_heap option  
}


