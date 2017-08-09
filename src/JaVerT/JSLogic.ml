open Set
open JSIL_Syntax
open JS2JSIL_Constants

module SS = Set.Make(String)
let small_tbl_size = 31
let medium_tbl_size = 101



(************)
(* Utils    *)
(************)





(************)
(************)
(* JSLogic  *)
(************)
(************)


type js_logic_expr =
	| JSLLit				of jsil_lit
	| JSLNone
	| JSLVar				of string
	| JSALoc				of string
	| JSPVar				of string
	| JSLBinOp				of js_logic_expr * jsil_binop * js_logic_expr
	| JSLUnOp				of jsil_unop * js_logic_expr
	| JSLTypeOf				of js_logic_expr
	| JSLEList      		of js_logic_expr list
	| JSLESet       		of js_logic_expr list
	| JSLLstNth     		of js_logic_expr * js_logic_expr
	| JSLStrNth     		of js_logic_expr * js_logic_expr
	| JSLSetUnion   		of js_logic_expr list
	| JSLSetInter   		of js_logic_expr list
	| JSLThis 
	| JSLScope         


module MyJSLExpr = 
	struct
		type t = js_logic_expr
		let compare = Pervasives.compare
	end

module JSSExpr = Set.Make(MyJSLExpr)


type js_logic_assertion =
	| JSLAnd				of js_logic_assertion * js_logic_assertion
	| JSLOr					of js_logic_assertion * js_logic_assertion
	| JSLNot				of js_logic_assertion
	| JSLTrue
	| JSLFalse
	| JSLEq					of js_logic_expr * js_logic_expr
	| JSLLess	   			of js_logic_expr * js_logic_expr
	| JSLLessEq	   			of js_logic_expr * js_logic_expr
	| JSLStrLess    		of js_logic_expr * js_logic_expr
	| JSLStar				of js_logic_assertion * js_logic_assertion
	| JSLPointsTo			of js_logic_expr * js_logic_expr * js_logic_expr
	| JSLEmp
	| JSLPred				of string  * (js_logic_expr list)
	| JSLForAll             of (jsil_var * jsil_type) list * js_logic_assertion
	| JSLTypes  		    of (string * jsil_type) list
	| JSLScope      		of string  * js_logic_expr
	| JSLVarSChain          of string * string * js_logic_expr * js_logic_expr
	| JSOSChains            of string * js_logic_expr * string * js_logic_expr
	| JSOCS                 of string * js_logic_expr 
	| JSFunObj      		of string  * js_logic_expr * js_logic_expr * (js_logic_expr option) 
	| JSClosure     		of ((string * js_logic_expr) list) * ((string * js_logic_expr) list)
	| JSEmptyFields			of js_logic_expr * js_logic_expr 
	| JSLSetMem  	        of js_logic_expr * js_logic_expr              
	| JSLSetSub  	        of js_logic_expr * js_logic_expr 


type js_logic_command =
	| JSFold             of js_logic_assertion                                                        
	| JSUnfold           of js_logic_assertion * ((string * ((string * js_logic_expr) list)) option)  
	| JSFlash            of js_logic_assertion                                                                                                     (** Single unfold *)
	| JSCallSpec		 of string * string * (js_logic_expr list)                                     (** Spec calling *)
	| JSRecUnfold        of string                                                                     (** Recursive unfold of everything *)
	| JSLogicIf          of js_logic_expr * (js_logic_command list) * (js_logic_command list)          (** If-then-else *)
	| JSMacro            of string * (js_logic_expr list)                                              (** Macro *)
	| JSAssert           of js_logic_assertion                                                         (** Assert *)


type js_logic_predicate = {
	js_name        : string;
	js_num_params  : int;
	js_params      : js_logic_expr list;
	js_definitions : ((string option) * js_logic_assertion) list;
}

type js_single_spec = {
	js_pre      : js_logic_assertion;   
	js_post     : js_logic_assertion;  
	js_ret_flag : jsil_return_flag      
}

type js_spec = {
	js_spec_name    : string;               
	js_spec_params  : string list;        
	js_proc_specs   : js_single_spec list
}


(******************)
(******************)
(* JS2JSIL Logic  *)
(******************)
(******************)

let main_fid                      = "main"
let pi_pred_name                  = "Pi"
let object_class                  = "Object"
let syntax_error_pred_name        = "isSyntaxError"
let type_error_pred_name          = "isTypeError"
let initial_heap_pre_pred_name    = "initialHeapPre"
let initial_heap_post_pred_name   = "initialHeapPost"
let function_object_pred_name     = "function_object"
let standard_object_pred_name     = "standardObject"
let this_logic_var_name           = "#this"

let js_obj_internal_fields        = [ "@proto"; "@class"; "@extensible" ]

let errors_assertion = 
	LStar (
		LPred (type_error_pred_name,   [ (PVar JS2JSIL_Constants.var_te) ]), 
		LPred (syntax_error_pred_name, [ (PVar JS2JSIL_Constants.var_se) ])
	)

let fid_to_lvar fid = "#fid_" ^ fid

let fid_to_lvar_fresh = 
	let fids_tbl = Hashtbl.create 31 in 
	fun fid -> 
		let fid_count = 
			try 
				Hashtbl.find fids_tbl fid 
			with Not_found -> 0 in 
		Hashtbl.replace fids_tbl fid (fid_count + 1); 
		"#fid_" ^ (string_of_int fid_count) ^ "_" ^ fid

let counter = ref 0

let fresh_lvar () =
	let v = "#lvar_" ^ (string_of_int !counter) in
   counter := !counter + 1;
   v
      



let rec js2jsil_lexpr scope_var le =
	let fe = js2jsil_lexpr scope_var in
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
	| JSLESet les             -> LESet (List.map fe les)
	| JSLSetUnion les         -> LSetUnion (List.map fe les)
	| JSLSetInter les         -> LSetInter (List.map fe les)
	| JSLLstNth (le1, le2)    -> LLstNth (fe le1, fe le2)
	| JSLStrNth (le1, le2)    -> LStrNth (fe le1, fe le2)
	| JSLThis                 -> LVar this_logic_var_name
	| JSLScope                -> 
		(match scope_var with 
		| None           -> raise (Failure "DEATH: js2jsil_lexpr")
		| Some scope_var -> PVar scope_var)




let rec js2jsil_assertion	
		(cur_fid    : string option) 
		(cc_tbl     : cc_tbl_type)
		(vis_tbl    : vis_tbl_type) 
		(fun_tbl    : pre_fun_tbl_type) 
		(scope_var  : string option)
		(a          : js_logic_assertion) : JSIL_Syntax.jsil_logic_assertion = 

	let f = js2jsil_logic cur_fid cc_tbl vis_tbl fun_tbl scope_var in
	let fe = js2jsil_lexpr scope_var in
	
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
	| JSLPointsTo	(le1, le2, le3)       -> LPointsTo ((fe le1), (fe le2), (fe le3))
	| JSLEmp                              -> LEmp
	| JSLPred (s, les)                    -> LPred (s, (List.map fe les))
	| JSLForAll (s, a)                    -> LForAll (s, f a)
	| JSLTypes (vts)                      -> LTypes (List.map (fun (v, t) -> (LVar v, t)) vts)
	| JSLSetMem (le1, le2) 	              -> LSetMem (fe le1, fe le2)
	| JSLSetSub (le1, le2)                -> LSetSub (fe le1, fe le2)
	| JSEmptyFields (e, domain) 		  -> LEmptyFields (fe e, fe domain) 


	| JSLScope (x, le)                    -> 
		let fid  = try Option.get cur_fid with No_value -> raise (Failure "DEATH: js2jsil_assertion") in 
		let a'   = JSLVarSChain (fid, x, le, le_sc) in 
		

	
	
	| JSClosure (var_les, fid_sc_les) -> 
		let vis_lists = 
			List.map (fun (fid, _) -> 
				 try Hashtbl.find vis_tbl fid with Not_found -> 
					raise (Failure (Printf.sprintf "Function %s not found in the visibility table." fid)))
			fid_sc_les in 
		let shared_vis_list = compute_common_suffix vis_lists in 
		let shared_vis_list_les_tbl = Hashtbl.create 31 in 
		List.iter	
			(fun fid -> Hashtbl.replace shared_vis_list_les_tbl fid (LVar (fid_to_lvar_fresh fid))) 
			shared_vis_list; 
		let scope_chain_assertions = 
			List.map (fun (fid, x_scope_chain) -> let a, _ = make_overlapping_scope_ass fid x_scope_chain (Some shared_vis_list_les_tbl) in a) fid_sc_les in 
		
		let just_one_arbitrary_fid =
			match fid_sc_les with 
			| [] -> raise (Failure "DEATH! just_one_arbitrary_fid") 
			| (fid, _) :: _ -> fid in 
		let scope_var_assertions = 
			List.map 
				(fun (x, le) -> 
					let var_to_fid_tbl = get_scope_table cc_tbl just_one_arbitrary_fid in 
					let fid = 
						try Hashtbl.find var_to_fid_tbl x
							with Not_found -> raise (Failure "DEATH var_to_fid_tbl") in
					let le_fid = 
						try Hashtbl.find shared_vis_list_les_tbl fid 
							with Not_found -> raise (Failure "DEATH shared_vis_list_les_tbl") in 
					let le' = fe le in 
					if (fid = main_fid) 
						then LPointsTo (
							LLit (Loc JS2JSIL_Constants.locGlobName), 
							LLit (String x), 
							LEList [ LLit (String "d"); le'; LLit (Bool true); LLit (Bool true); LLit (Bool false) ])
			 			else LPointsTo (le_fid, LLit (String x), le'))
				var_les in 	
		JSIL_Logic_Utils.star_asses (scope_chain_assertions @ scope_var_assertions) 

	| JSLVarSChain (fid, x, le_x, le_sc) -> 
		let var_to_fid_tbl = get_scope_table cc_tbl fid in 
		let vis_list       = get_vis_list vis_tbl fid in 
				
		if (Hashtbl.mem var_to_fid_tbl x) then (
			let fid_x = Hashtbl.find var_to_fid_tbl x in
			if (fid_x = main_fid) 
				then LPointsTo (
							LLit (Loc JS2JSIL_Constants.locGlobName), 
							LLit (String x), 
							LEList [ LLit (String "d"); (fe le_x); LLit (Bool true); LLit (Bool true); LLit (Bool false) ])
			 	else (
			 		let scope_chain_a, les_pairs_vis_list = make_overlapping_scope_ass fid le_sc None in 
					let fid_x_var = List.assoc fid_x les_pairs_vis_list in 
			 		LStar (LPointsTo (fid_x_var, LLit (String x), fe le_x), scope_chain_a)
			 	)
			) else (
				LPointsTo (
					LLit (Loc JS2JSIL_Constants.locGlobName), 
					LLit (String x), 
					LEList [ LLit (String "d"); (fe le_x); LLit (Bool true); LLit (Bool true); LLit (Bool false) ])
			)

	| JSOSChains (fid1, sc1, fid2, sc2) -> 
			overlapping_scope_assertion fid1 sc1 fid2 sc2

	| _ -> raise (Failure "js2jsil_logic: new assertions not implemented")



let rec js2jsil_logic_cmds 
		(cc_tbl     : cc_tbl_type)
		(vis_tbl    : vis_tbl_type) 
		(fun_tbl    : pre_fun_tbl_type) 
		(logic_cmds : js_logic_command list) =
	let f = js2jsil_logic_cmds cc_tbl vis_tbl fun_tbl in 
	let fe = js2jsil_lexpr in

	let translate_unfold_info unfold_info = 
		match unfold_info with 
		| None -> None 
		| Some (def_id, var_le_list) -> 
			Some (def_id, List.map (fun (x, le) -> (x, fe le)) var_le_list) in 

	match logic_cmds with 
	| [] -> []

	| (JSFold (JSLPred (s, les))) :: rest -> (Fold (LPred (s, List.map fe les))) :: (f rest)

	| (JSFlash (JSLPred (s, les))) :: rest -> 
		let flash_arg = LPred (s, List.map fe les) in 
		Unfold (flash_arg, None) :: ((Fold flash_arg) :: (f rest))

	| (JSUnfold ((JSLPred (s, les)), unfold_info)) :: rest ->
		(Unfold ((LPred (s, List.map fe les)), (translate_unfold_info unfold_info))) :: (f rest) 
	| (JSCallSpec (spec_name, x, les)) :: rest -> 
		(*Printf.printf "I am translating a callspec for function %s with retvar %s" s ret_var;*)
		let args = (PVar JS2JSIL_Constants.var_scope) :: ((PVar JS2JSIL_Constants.var_this) :: (List.map fe les)) in 
		CallSpec (spec_name, x, args) :: (f rest)
	| (JSAssert assertion) :: rest -> 
		let a' = js2jsil_logic None cc_tbl vis_tbl fun_tbl assertion in 
		(Assert a') :: (f rest)

	| (JSRecUnfold pred_name) :: rest -> (RecUnfold pred_name) :: (f rest)
	| (JSMacro (s, les)) :: rest -> (Macro (s, List.map fe les)) :: (f rest)
	| (JSLogicIf (le, lcthen, lcelse)) :: rest -> (LogicIf (fe le, f lcthen, f lcelse)) :: (f rest)

	| _ -> raise (Failure "DEATH: No such logic command")



let translate_predicate_def pred_def cc_tbl vis_tbl fun_tbl = 
	let jsil_params = List.map js2jsil_lexpr pred_def.js_params in 
	let jsil_definitions = List.map (fun (os, a) -> os, (js2jsil_logic None cc_tbl vis_tbl fun_tbl a)) pred_def.js_definitions in
	{ name = pred_def.js_name; num_params = pred_def.js_num_params; params = jsil_params; definitions = jsil_definitions }


let rec js2jsil_logic_top_level_pre a cc_tbl (vis_tbl : JS2JSIL_Constants.vis_tbl_type) (fun_tbl : JS2JSIL_Constants.pre_fun_tbl_type) fid =
	print_debug (Printf.sprintf "Inside js2jsil_logic_top_level_pre for procedure %s\n" fid);
	let vis_list = try Hashtbl.find vis_tbl fid with _ -> raise (Failure "js2jsil_logic_top_level_pre - fid not found") in 
	let is_global = (fid = main_fid) in
	let a_scope_chain = make_scope_chain_assertion vis_list in
	let a_pre_js_heap = 
		if (is_global)
			then LPred (initial_heap_pre_pred_name, [])
			else LPred (initial_heap_post_pred_name, []) in
	let a' = js2jsil_logic (Some fid) cc_tbl vis_tbl fun_tbl a in
	let a_this = LEq (PVar JS2JSIL_Constants.var_this, LVar this_logic_var_name) in  
	
	print_debug (Printf.sprintf "J2JPre: \n\t%s\n\t%s\n\t%s"
		(JSIL_Print.string_of_logic_assertion a' false)
		(JSIL_Print.string_of_logic_assertion a_scope_chain false) 
		(JSIL_Print.string_of_logic_assertion a_pre_js_heap false));
	if (is_global) 
		then JSIL_Logic_Utils.star_asses [a'; a_pre_js_heap ]
	 	else JSIL_Logic_Utils.star_asses [ a'; a_pre_js_heap; a_scope_chain; a_this ]
		


let rec js2jsil_logic_top_level_post a cc_tbl (vis_tbl : JS2JSIL_Constants.vis_tbl_type) fun_tbl fid =
	let vis_list = try Hashtbl.find vis_tbl fid with _ -> raise (Failure "js2jsil_logic_top_level_pre - fid not found") in 
	let is_global = (fid = main_fid) in
	let a_scope_chain = make_scope_chain_assertion vis_list in 
	let a_post_js_heap = LPred (initial_heap_post_pred_name, []) in
	let a' = js2jsil_logic (Some fid) cc_tbl vis_tbl fun_tbl a in
	let a_this = LEq (PVar JS2JSIL_Constants.var_this, LVar this_logic_var_name) in 
	print_debug (Printf.sprintf "J2JPost: \n\t%s\n\t%s"
		(JSIL_Print.string_of_logic_assertion a' false) 
		(JSIL_Print.string_of_logic_assertion a_post_js_heap false));	
	if (is_global) 
		then JSIL_Logic_Utils.star_asses [a'; a_post_js_heap ]
	 	else JSIL_Logic_Utils.star_asses [ a'; a_post_js_heap; a_scope_chain; a_this ]
		



