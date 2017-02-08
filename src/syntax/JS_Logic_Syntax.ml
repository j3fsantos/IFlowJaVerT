open Set
open JSIL_Syntax

module SS = Set.Make(String)

(* JS_Logic - Assertions *)

let small_tbl_size = 31
let medium_tbl_size = 101

let main_fid                      = "main"
let pi_pred_name                  = "Pi"
let object_class                  = "Object"
let syntax_error_pred_name        = "isSyntaxError"
let type_error_pred_name          = "isTypeError"
let initial_heap_pre_pred_name    = "initialHeapPre"
let initial_heap_post_pred_name   = "initialHeapPost"
let function_object_pred_name     = "function_object"
let standard_object_pred_name     = "standardObject"

let errors_assertion = 
	LStar (
		LPred (type_error_pred_name,   [ (PVar Js2jsil_constants.var_te) ]), 
		LPred (syntax_error_pred_name, [ (PVar Js2jsil_constants.var_se) ])
	)

let fid_to_lvar fid = "#fid_" ^ fid

let counter = ref 0

let fresh_lvar () =
	let v = "#lvar_" ^ (string_of_int !counter) in
   counter := !counter + 1;
   v


type js_logic_expr =
	| JSLLit				of jsil_lit
	| JSLNone
	| JSLVar				of string
	| JSALoc				of string
	| JSPVar				of string
	| JSLBinOp			of js_logic_expr * jsil_binop * js_logic_expr
	| JSLUnOp				of jsil_unop * js_logic_expr
	| JSLTypeOf			of js_logic_expr
	| JSLEList      of js_logic_expr list
	| JSLLstNth     of js_logic_expr * js_logic_expr
	| JSLStrNth     of js_logic_expr * js_logic_expr
	| JSLUnknown
	| JSLThis

type js_logic_assertion =
	| JSLAnd				of js_logic_assertion * js_logic_assertion
	| JSLOr					of js_logic_assertion * js_logic_assertion
	| JSLNot				of js_logic_assertion
	| JSLTrue
	| JSLFalse
	| JSLEq					of js_logic_expr * js_logic_expr
	| JSLLess	   		of js_logic_expr * js_logic_expr
	| JSLLessEq	   	of js_logic_expr * js_logic_expr
	| JSLStrLess    of js_logic_expr * js_logic_expr
	| JSLStar				of js_logic_assertion * js_logic_assertion
	| JSLPointsTo		of js_logic_expr * js_logic_expr * js_logic_expr
	| JSLEmp
	| JSLPred				of string  * (js_logic_expr list)
	| JSLTypes      of (string * jsil_type) list
	| JSLScope      of string  * js_logic_expr
	(* JSFunObj (f_id, f_loc, f_prototype) *)
	| JSFunObj      of string  * js_logic_expr * js_logic_expr


type js_logic_predicate = {
	js_name        : string;
	js_num_params  : int;
	js_params      : js_logic_expr list;
	js_definitions : js_logic_assertion list;
}


let rec js2jsil_lexpr le =
	let fe = js2jsil_lexpr in
	match le with
	| JSLLit lit              -> LLit lit
	| JSLNone                 -> LNone
	| JSLVar x                -> LVar x
	| JSALoc l                -> ALoc l
	| JSPVar x                -> PVar x
	| JSLBinOp (le1, op, le2) -> LBinOp (fe le1, op, fe le2)
	| JSLUnOp (op, le)        -> LUnOp (op, fe le)
	| JSLTypeOf le            -> LTypeOf (fe le)
	| JSLEList les            -> LEList (List.map fe les)
	| JSLLstNth (le1, le2)    -> LLstNth (fe le1, fe le2)
	| JSLStrNth (le1, le2)    -> LStrNth (fe le1, fe le2)
	| JSLUnknown              -> LUnknown
	| JSLThis                 -> PVar Js2jsil_constants.var_this


let rec js2jsil_logic_cmds logic_cmds = 
	let fe = js2jsil_lexpr in
	match logic_cmds with 
	| [] -> []
	| (Parser_syntax.Fold, (JSLPred (s, les))) :: rest -> (Fold (LPred (s, List.map fe les))) :: (js2jsil_logic_cmds rest)
	| (Parser_syntax.Unfold, (JSLPred (s, les))) :: rest -> (Unfold (LPred (s, List.map fe les))) :: (js2jsil_logic_cmds rest) 
	| _ -> raise (Failure "DEATH.")


let make_simple_scope_chain_logic_expression vis_list = 
	let vis_list = 
		match vis_list with 
		| cur :: rest_vis_list -> rest_vis_list 
		| [] -> raise (Failure "DEATH: make_simple_scope_chain_logic_expression") in 
	let le_vis_list = 
		List.map 
			(fun x -> if (x = main_fid) then LLit (Loc Js2jsil_constants.locGlobName) else LVar (fid_to_lvar x))
			vis_list in 
	LEList le_vis_list


let rec js2jsil_logic cur_fid (var_to_fid_tbl : ((string, string) Hashtbl.t) option) vis_tbl fun_tbl (a : js_logic_assertion) : JSIL_Syntax.jsil_logic_assertion =
	let f = js2jsil_logic cur_fid var_to_fid_tbl vis_tbl fun_tbl in
	let fe = js2jsil_lexpr in
	match a with
	| JSLAnd (a1, a2)                     -> LAnd ((f a1), (f a2))
	| JSLOr (a1, a2)                      -> LOr ((f a1), (f a2))
	| JSLNot a                            -> LNot (f a)
	| JSLTrue                             -> LTrue
	| JSLFalse                            -> LFalse
	| JSLEq (le1, le2)                    -> LEq ((fe le1), (fe le2))
	| JSLLess (le1, le2)                  -> LLess ((fe le1), (fe le2))
	| JSLLessEq (le1, le2)                -> LLessEq ((fe le1), (fe le2))
	| JSLStrLess (le1, le2)               -> LStrLess ((fe le1), (fe le2))
	| JSLStar (a1, a2)                    -> LStar ((f a1), (f a2))
	| JSLPointsTo	(le1, le2, le3)         -> LPointsTo ((fe le1), (fe le2), (fe le3))
	| JSLEmp                              -> LEmp
	| JSLPred (s, les)                    -> LPred (s, (List.map fe les))
	| JSLTypes (vts)                      -> LTypes (List.map (fun (v, t) -> (LVar v, t)) vts)
	
	| JSLScope (x, le)                    ->
		let var_to_fid_tbl = 
			(match var_to_fid_tbl with 
			| Some var_to_fid_tbl -> var_to_fid_tbl 
			| None -> raise (Failure "DEATH: js2jsil_logic")) in 
		if (Hashtbl.mem var_to_fid_tbl x) then (
			let fid = Hashtbl.find var_to_fid_tbl x in
			if (fid = main_fid) 
				then LPointsTo (
							LLit (Loc Js2jsil_constants.locGlobName), 
							LLit (String x), 
							LEList [ LLit (String "d"); (fe le); LLit (Bool true); LLit (Bool true); LLit (Bool false) ])
			 	else (if (fid = cur_fid) 
					then LPointsTo (PVar Js2jsil_constants.var_er, LLit (String x), fe le) 
					else LPointsTo (LVar (fid_to_lvar fid), LLit (String x), fe le)))
			else (
			let msg = Printf.sprintf "scope predicate misuse: %s needs to be in the scope!\n" x in
			raise (Failure msg))
			
	|	JSFunObj (id, f_loc, f_prototype) -> 
		let f_loc' = fe f_loc in 
		let f_prototype' = fe f_prototype in 
		let id_vis_list = try Hashtbl.find vis_tbl id with _ -> raise (Failure (Printf.sprintf "Function %s not found in the visibility table." id)) in 
		let _, args, _, (_, _, _) = try Hashtbl.find fun_tbl id with _ -> raise (Failure (Printf.sprintf "Function %s not found in the fun table." id)) in
		let n_args = List.length args in
		let le_scope_chain = make_simple_scope_chain_logic_expression id_vis_list in
		let st_obj_fproto = LPred (standard_object_pred_name, [f_prototype']) in
		let obj_fproto_cstr = 
			LPointsTo (
				f_prototype', 
				LLit (String "constructor"), 
				LEList [ LLit (String "d"); f_loc'; LLit (Bool true); LLit (Bool false); LLit (Bool true) ]) in
		LStar (
			LPred (function_object_pred_name, [ f_loc'; le_scope_chain; LLit (String id); LLit (String id); LLit (Integer n_args); f_prototype'] ), 
			LStar (st_obj_fproto, obj_fproto_cstr))


let translate_predicate_def pred_def vis_tbl fun_tbl = 
	let jsil_params = List.map js2jsil_lexpr pred_def.js_params in 
	let jsil_definitions = List.map (fun a -> js2jsil_logic "" None vis_tbl fun_tbl a) pred_def.js_definitions in 
	{ name = pred_def.js_name; num_params = pred_def.js_num_params; params = jsil_params; definitions = jsil_definitions }


let make_scope_chain_assertion vis_list is_pre =
	print_debug (Printf.sprintf "Inside make_scope_chain_assertion with\n\tvis_list:%s" (String.concat ", " vis_list));
	
	let cur, vis_list = 
		match vis_list with 
		| cur :: rest_vis_list -> cur, rest_vis_list 
		| [] -> raise (Failure "DEATH: make_scope_chain_assertion - 1") in 
	
	(* x_sc == {{ #id1, ..., #idn, $lg }} *)
	let le_vis_list = 
		List.map 
			(fun x -> if (x = main_fid) then LLit (Loc Js2jsil_constants.locGlobName) else LVar (fid_to_lvar x))
			vis_list in 
	let le_vis_list = 
		if is_pre then le_vis_list 
		else if (cur = main_fid) 
			then (LLit (Loc Js2jsil_constants.locGlobName)) :: le_vis_list
			else (PVar Js2jsil_constants.var_er) :: le_vis_list in 
	let xsc_ass = LEq (PVar Js2jsil_constants.var_scope, LEList le_vis_list) in 
	
	(* types(#id1: $$object_type, ..., #idn: $$objtect_type) *)
	let type_pairs = 
		List.fold_left 
			(fun ac le -> 
				match le with 
				| LLit _ -> ac 
				| LVar _ 
				| PVar _ -> (le, ObjectType) :: ac
				| _      -> raise (Failure "DEATH: make_scope_chain_assertion - 2"))
			[]
			le_vis_list in 
	let types_assertion = 
		if (List.length type_pairs > 0) 
			then LTypes type_pairs 
			else LEmp in 
	
	(* !(#id1 == $lg) * ... * !(#idn == $lg) *) 
	let not_lg_assertions = 
		List.fold_left 
			(fun ac le -> 
				match le with 
				| LLit _ -> ac 
				| LVar _  
				| PVar _ ->
					let a = LNot (LEq (le, LLit (Loc Js2jsil_constants.locGlobName))) in 
					if (ac = LEmp) then a else LStar (a, ac)
				| _      -> raise (Failure "DEATH: make_scope_chain_assertion - 3"))
			LEmp
			le_vis_list in 			
	
	JSIL_Logic_Utils.star_asses [ xsc_ass; types_assertion; not_lg_assertions ] 


let rec js2jsil_logic_top_level_pre a (var_to_fid_tbl : (string, string) Hashtbl.t) (vis_tbl : (string, string list) Hashtbl.t) (fun_tbl : Js2jsil_constants.pre_fun_tbl_type) fid =
	print_debug (Printf.sprintf "Inside js2jsil_logic_top_level_pre for procedure %s\n" fid);
	let vis_list = try Hashtbl.find vis_tbl fid with _ -> raise (Failure "js2jsil_logic_top_level_pre - fid not found") in 
	let is_global = (fid = main_fid) in
	let a_scope_chain = make_scope_chain_assertion vis_list true in
	let a_pre_js_heap = 
		if (is_global)
			then LPred (initial_heap_pre_pred_name, [])
			else LPred (initial_heap_post_pred_name, []) in
	let a' = js2jsil_logic fid (Some var_to_fid_tbl) vis_tbl fun_tbl a in
	print_debug (Printf.sprintf "J2JPre: \n\t%s\n\t%s\n\t%s"
		(JSIL_Print.string_of_logic_assertion a' false)
		(JSIL_Print.string_of_logic_assertion a_scope_chain false) 
		(JSIL_Print.string_of_logic_assertion a_pre_js_heap false));
	if (is_global) 
		then JSIL_Logic_Utils.star_asses [a'; a_pre_js_heap ]
		else JSIL_Logic_Utils.star_asses [a'; a_pre_js_heap; a_scope_chain ]


let rec js2jsil_logic_top_level_post a (var_to_fid_tbl : (string, string) Hashtbl.t) (vis_tbl : (string, string list) Hashtbl.t) fun_tbl fid =
	let vis_list = try Hashtbl.find vis_tbl fid with _ -> raise (Failure "js2jsil_logic_top_level_pre - fid not found") in 
	let is_global = (fid = main_fid) in
	let a_scope_chain = make_scope_chain_assertion vis_list false in
	let a_post_js_heap = LPred (initial_heap_post_pred_name, []) in
	let a' = js2jsil_logic fid (Some var_to_fid_tbl) vis_tbl fun_tbl a in
	print_debug (Printf.sprintf "J2JPost: \n\t%s\n\t%s\n\t%s"
		(JSIL_Print.string_of_logic_assertion a' false) 
		(JSIL_Print.string_of_logic_assertion a_scope_chain false) 
		(JSIL_Print.string_of_logic_assertion a_post_js_heap false));	
	JSIL_Logic_Utils.star_asses [a'; a_scope_chain; a_post_js_heap ]
			

