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

let fid_to_lvar fid = "#fid_" ^ fid

let counter = ref 0

let fresh_lvar () =
	let v = "#lvar_" ^ (string_of_int !counter) in
   counter := !counter + 1;
   v


let make_simple_scope_chain_assertion sc_loc vis_list = 
	let var_scope_proto_null = LPointsTo (sc_loc, LLit (String Js2jsil_constants.internalProtoFieldName), LLit Null) in
	let rec loop fids assertions targets = 
		match fids with 
		| [] -> assertions, targets
		| fid :: rest_fids -> 
			if (fid = main_fid) then (
				let a_cur_fid = LPointsTo (sc_loc, LLit (String fid), LLit (Loc Js2jsil_constants.locGlobName)) in 
				loop rest_fids (a_cur_fid :: assertions) targets 
			) else (
				let target = (LVar (fid_to_lvar fid)) in 
				let a_cur_fid = LPointsTo (sc_loc, LLit (String fid), target) in
				loop rest_fids (a_cur_fid :: assertions) targets 
			) in 
	let sc_assertions, _ = loop vis_list [] [] in 
	let a_sc = JSIL_Logic_Utils.star_asses (var_scope_proto_null :: sc_assertions) in 
	a_sc  
			


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


let filter_var_to_fid_tbl var_to_fid_tbl scope_vars cur_fid = 
	let new_var_to_fid_tbl = Hashtbl.create small_tbl_size in 
	Hashtbl.iter
		(fun x fid -> 
			if ((fid = cur_fid) || (SS.mem x scope_vars))  
				then Hashtbl.replace new_var_to_fid_tbl x fid)
		var_to_fid_tbl; 
	new_var_to_fid_tbl  


let rec get_scope_vars a =
	let rec loop (a : js_logic_assertion) (svars : string list) : string list = 
		match a with 
		| JSLNot a -> loop a svars
		| JSLAnd (a1, a2) | JSLOr (a1, a2) | JSLStar (a1, a2) -> loop a2 (loop a1 svars) 
		| JSLScope (x, le)  -> x :: svars 
		| _ -> svars in 
	let svars = loop a [] in 
	let svars_set = SS.of_list svars in 
	svars_set


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


let rec js2jsil_logic (js_var_to_lvar : ((string, JSIL_Syntax.jsil_logic_expr) Hashtbl.t) option) vis_tbl fun_tbl (a : js_logic_assertion) : JSIL_Syntax.jsil_logic_assertion =
	let f = js2jsil_logic js_var_to_lvar vis_tbl fun_tbl in
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
		let js_var_to_lvar = 
			(match js_var_to_lvar with 
			| Some js_var_to_lvar -> js_var_to_lvar 
			| None -> raise (Failure "DEATH: js2jsil_logic")) in 
		if (Hashtbl.mem js_var_to_lvar x) then (
			let x_lvar = Hashtbl.find js_var_to_lvar x in
			LEq (x_lvar, (fe le))
		) else (
			let msg = Printf.sprintf "scope predicate misuse: %s needs to be in the scope!\n" x in
			raise (Failure msg))
	|	JSFunObj (id, f_loc, f_prototype) -> 
		try 
			let sc_loc = LVar (fresh_lvar ()) in 
			let f_loc' = fe f_loc in 
			let f_prototype' = fe f_prototype in 
			let id_vis_list = Hashtbl.find vis_tbl id in 
			let _, args, _, (_, _, _) = Hashtbl.find fun_tbl id in
			let n_args = List.length args in
			let a_scope_chain = make_simple_scope_chain_assertion sc_loc id_vis_list in
			let st_obj_fproto = LPred (standard_object_pred_name, [f_prototype']) in
			let obj_fproto_cstr = 
				LPointsTo (
					f_prototype', 
					LLit (String "constructor"), 
					LEList [ LLit (String "d"); f_loc'; LLit (Bool true); LLit (Bool false); LLit (Bool true) ]) in
			LStar (
				LPred (function_object_pred_name, [ f_loc'; sc_loc; LLit (String id); LLit (String id); LLit (Integer n_args); f_prototype'] ), 
				LStar (st_obj_fproto, LStar (obj_fproto_cstr, a_scope_chain)))
		with _ -> raise (Failure "js2jsil_logic. JSFunObj - not found business")



let var_fid_tbl_to_assertion (var_to_fid_tbl : (string, string) Hashtbl.t) current (exceptions : string list) is_global is_pre =
	let js_var_to_lvar = Hashtbl.create small_tbl_size in
	let (a, locs) = Hashtbl.fold 
		(fun x fid (ac, locs) ->
			if (not (List.mem fid exceptions) && (not (fid = current) || (fid = current && not is_pre))) then (
				let target = if (fid = main_fid)
					then LLit (Loc Js2jsil_constants.locGlobName)
					else if (fid = current && not is_pre)
							then (PVar Js2jsil_constants.var_er)
							else (LVar (fid_to_lvar fid)) in
				let x_fid = if (is_global) then LLit (Loc Js2jsil_constants.locGlobName) else target in
				let x_val_name = fresh_lvar () in
				let x_val = LVar x_val_name in
				let le_val =
					if (fid = main_fid)
						then LEList [ LLit (String "d"); x_val; LLit (Bool true); LLit (Bool true); LLit (Bool false) ]
						else x_val in
				let a_new = LPointsTo (x_fid, LLit (String x), le_val) in
				Hashtbl.add js_var_to_lvar x x_val;
				let nlocs = SS.add (fid_to_lvar fid) locs in
				if (ac = LEmp) then (a_new, nlocs) else (LStar (ac, a_new), nlocs))
			else (ac, locs))
		var_to_fid_tbl
		(LEmp, SS.empty) in
	a, js_var_to_lvar


let translate_predicate_def pred_def vis_tbl fun_tbl = 
	let jsil_params = List.map js2jsil_lexpr pred_def.js_params in 
	let jsil_definitions = List.map (fun a -> js2jsil_logic None vis_tbl fun_tbl a) pred_def.js_definitions in 
	{ name = pred_def.js_name; num_params = pred_def.js_num_params; params = jsil_params; definitions = jsil_definitions }



let make_scope_chain_assertion vis_list current exceptions is_pre =
	print_debug (Printf.sprintf "Inside make_scope_chain_assertion with\n\tvis_list:%s\nexceptions:%s"
	(String.concat ", " vis_list) (String.concat ", " exceptions));

	let var_scope_proto_null = LPointsTo (PVar Js2jsil_constants.var_scope, LLit (String Js2jsil_constants.internalProtoFieldName), LLit Null) in

	let rec loop a fids =
	match fids with
	| [] -> a
	| fid :: rest ->
		let target = if (fid = main_fid)
			then LLit (Loc Js2jsil_constants.locGlobName)
			else LVar (fid_to_lvar fid) in 
		if (not (List.mem fid exceptions)) then
		begin
			let a_new = LPointsTo (PVar Js2jsil_constants.var_scope, LLit (String fid), target) in
			let a_type = LTypes [ target, ObjectType ] in
			let a_not_lg = LNot (LEq (target, LLit (Loc Js2jsil_constants.locGlobName))) in
			let a_er_flag = LPointsTo (target, LLit (String Js2jsil_constants.erFlagPropName), LLit (Bool true)) in 
			(* a_new, a_type, a_proto_new, a_not_lg *)
			print_debug (Printf.sprintf "%s %s %s : %b %b %b" fid main_fid current (fid = main_fid) (fid = current) is_pre);
			let to_add = (match (fid = main_fid, fid = current, is_pre) with
			 | true, _,     _     -> a_new
			 | _,    false, true  -> LStar (a_er_flag, LStar (a_new, LStar (a_type, a_not_lg)))
			 | _,    false, false -> LStar (a_er_flag, a_new)
			 | _,    true,  false -> a_new
			 (* why dont I need the proto field in this case? *)
			 | _,    true,  true  -> a_new
			) in
			let a = if (a = LEmp) then to_add else LStar (a, to_add) in
			loop a rest
		end else loop a rest in
		let a' = loop LEmp vis_list in
		if (a' <> LEmp) then LStar (a', var_scope_proto_null) else var_scope_proto_null


let rec js2jsil_logic_top_level_pre a (var_to_fid_tbl : (string, string) Hashtbl.t) (vis_tbl : (string, string list) Hashtbl.t) (fun_tbl : Js2jsil_constants.pre_fun_tbl_type) fid =
	print_debug (Printf.sprintf "Inside js2jsil_logic_top_level_pre for procedure %s\n" fid);
	let vis_list = try Hashtbl.find vis_tbl fid with _ -> raise (Failure "js2jsil_logic_top_level_pre - fid not found") in 
	let is_global = (fid = main_fid) in
	let a_env_records, js_var_to_lvar = var_fid_tbl_to_assertion var_to_fid_tbl fid [ ] is_global true in
	let a_scope_chain = make_scope_chain_assertion vis_list fid [ ] true in
	let a_pre_js_heap = 
		if (is_global)
			then LPred (initial_heap_pre_pred_name, [])
			else LPred (initial_heap_post_pred_name, []) in
		let a' = js2jsil_logic (Some js_var_to_lvar) vis_tbl fun_tbl a in
		print_debug (Printf.sprintf "J2JPre: \n\t%s\n\t%s\n\t%s\n\t%s"
			(JSIL_Print.string_of_logic_assertion a' false) (JSIL_Print.string_of_logic_assertion a_env_records false)
			(JSIL_Print.string_of_logic_assertion a_scope_chain false) (JSIL_Print.string_of_logic_assertion a_pre_js_heap false));
	if (is_global) 
		then JSIL_Logic_Utils.star_asses [a'; a_pre_js_heap ]
		else JSIL_Logic_Utils.star_asses [a'; a_env_records; a_scope_chain; a_pre_js_heap ]


let rec js2jsil_logic_top_level_post a (var_to_fid_tbl : (string, string) Hashtbl.t) (vis_tbl : (string, string list) Hashtbl.t) fun_tbl fid =
	let vis_list = try Hashtbl.find vis_tbl fid with _ -> raise (Failure "js2jsil_logic_top_level_pre - fid not found") in 
	let is_global = (fid = main_fid) in
	let a_env_records, js_var_to_lvar = var_fid_tbl_to_assertion var_to_fid_tbl fid [ ] is_global false in
	let a_scope_chain = make_scope_chain_assertion vis_list fid [ ] false in
	let a_post_js_heap = LPred (initial_heap_post_pred_name, []) in
	let a' = js2jsil_logic (Some js_var_to_lvar) vis_tbl fun_tbl a in
	print_debug (Printf.sprintf "J2JPost: \n\t%s\n\t%s\n\t%s\n\t%s"
		(JSIL_Print.string_of_logic_assertion a' false) (JSIL_Print.string_of_logic_assertion a_env_records false)
		(JSIL_Print.string_of_logic_assertion a_scope_chain false) (JSIL_Print.string_of_logic_assertion a_post_js_heap false));	
	let a_er_flag = LPointsTo (PVar Js2jsil_constants.var_er, LLit (String Js2jsil_constants.erFlagPropName), LLit (Bool true)) in 
	let a_er_proto = LPointsTo (PVar Js2jsil_constants.var_er, LLit (String Js2jsil_constants.internalProtoFieldName), LLit Null) in
		
	if (is_global)
		then JSIL_Logic_Utils.star_asses [a'; a_env_records; a_scope_chain; a_post_js_heap ]
		else JSIL_Logic_Utils.star_asses [a'; a_env_records; a_er_flag; a_scope_chain; a_post_js_heap; a_er_proto]
