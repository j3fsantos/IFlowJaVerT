open Set
open JSIL_Syntax
open JS2JSIL_Constants

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
let this_logic_var_name           = "#this"

let js_obj_internal_fields        = [ "@proto"; "@class"; "@extensible" ]

let errors_assertion = 
	LStar (
		LPred (type_error_pred_name,   [ (PVar JS2JSIL_Constants.var_te) ]), 
		LPred (syntax_error_pred_name, [ (PVar JS2JSIL_Constants.var_se) ])
	)



(**
		[ a ; a ; a; b; c; d ]
		[ a; b; c; d ]
		[ d; e; c; d ]  -> [ c; d ]
*)
let compute_common_suffix vis_lists = 
	let temp_shortest_length = 
		match vis_lists with 
		| [] -> raise (Failure "DEATH: compute_common_suffix")
		| lst :: _ -> List.length lst in 
	
	let shortest_lst_length = 
		List.fold_left 
			(fun min_so_far lst ->
				let lst_len = List.length lst in 
				if (lst_len < min_so_far) 
					then lst_len 
					else min_so_far)
		temp_shortest_length
		vis_lists in  
	
	let rec loop i common_suffix =
		if (i > shortest_lst_length) then common_suffix else (		 
			let is_len_minus_i_th_char_common, c = 
				List.fold_left 
					(fun (ac_bool, char) vis_list ->	
						if (not ac_bool) then (ac_bool, None) else ( 
							let c = List.nth vis_list ((List.length vis_list) - i) in 
							match char with 
							| None -> (true, Some c)
							| Some c' -> (c = c', Some c)))
					(true, None)
					vis_lists in 
					
			if (is_len_minus_i_th_char_common) 
				then (
					match c with 
					| Some c -> loop (i + 1) (c :: common_suffix) 
					| None   -> common_suffix)
				else common_suffix) in 
			
	loop 1 [] 	


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
	| JSLUnknown
	| JSLThis 

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
	| JSFunObj      		of string  * js_logic_expr * js_logic_expr * (js_logic_expr option) 
	| JSClosure     		of ((string * js_logic_expr) list) * ((string * js_logic_expr) list)
	| JSEmptyFields			of js_logic_expr * js_logic_expr 
	| JSLSetMem  	        of js_logic_expr * js_logic_expr              
	| JSLSetSub  	        of js_logic_expr * js_logic_expr       


type js_logic_predicate = {
	js_name        : string;
	js_num_params  : int;
	js_params      : js_logic_expr list;
	js_definitions : js_logic_assertion list;
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
	| JSLESet les             -> LESet (List.map fe les)
	| JSLSetUnion les         -> LSetUnion (List.map fe les)
	| JSLSetInter les         -> LSetInter (List.map fe les)
	| JSLLstNth (le1, le2)    -> LLstNth (fe le1, fe le2)
	| JSLStrNth (le1, le2)    -> LStrNth (fe le1, fe le2)
	| JSLUnknown              -> LUnknown
	| JSLThis                 -> LVar this_logic_var_name



let make_simple_scope_chain_logic_expression cur_fid vis_list = 
	let vis_list = 
		match vis_list with 
		| cur :: rest_vis_list -> rest_vis_list 
		| [] -> raise (Failure "DEATH: make_simple_scope_chain_logic_expression") in 
	
	let rec loop vis_list processed_vis_list past_cur_fid lg_assertions = 
		(match vis_list with 
		| [] -> (List.rev processed_vis_list), lg_assertions
		| fid :: rest_vis_list -> 
			let past_cur_fid = past_cur_fid || (cur_fid = fid) in 
			let le_fid, lg_assertions = 
				if (fid = main_fid) 
					then LLit (Loc JS2JSIL_Constants.locGlobName), lg_assertions 
					else (
						let le_fid = if past_cur_fid then LVar (fid_to_lvar fid) else LVar (fid_to_lvar_fresh fid) in 
						let new_lg_assertion = LNot (LEq (le_fid, LLit (Loc JS2JSIL_Constants.locGlobName))) in 
						let lg_assertions = 
							if (lg_assertions = LEmp)
								then new_lg_assertion
								else LStar (lg_assertions, new_lg_assertion) in  
						le_fid, lg_assertions
					) in 
			loop rest_vis_list (le_fid :: processed_vis_list) past_cur_fid lg_assertions) in 
	
	let le_vis_list, lg_assertions = loop vis_list [] false LEmp in 
	let types_list = List.map (fun x -> (x, ObjectType)) (List.filter (fun x -> match x with | LLit (Loc _) -> false | _ -> true) le_vis_list) in
	LEList le_vis_list, LStar (LTypes types_list, lg_assertions) 





let make_scope_chain_assertion (vis_list : string list) =
	print_debug (Printf.sprintf "Inside make_scope_chain_assertion with\n\tvis_list:%s" (String.concat ", " vis_list));
	
	let cur, vis_list = 
		match vis_list with 
		| cur :: rest_vis_list -> cur, rest_vis_list 
		| [] -> raise (Failure "DEATH: make_scope_chain_assertion - 1") in 
	
	(* x_sc == {{ #id1, ..., #idn, $lg }} *)
	let le_vis_list = 
		List.map 
			(fun x -> if (x = main_fid) then LLit (Loc JS2JSIL_Constants.locGlobName) else LVar (fid_to_lvar x))
			vis_list in 

	let xsc_ass = LEq (PVar JS2JSIL_Constants.var_scope, LEList le_vis_list) in 
	
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
					let a = LNot (LEq (le, LLit (Loc JS2JSIL_Constants.locGlobName))) in 
					if (ac = LEmp) then a else LStar (a, ac)
				| _      -> raise (Failure "DEATH: make_scope_chain_assertion - 3"))
			LEmp
			le_vis_list in 			
	
	JSIL_Logic_Utils.star_asses [ xsc_ass; types_assertion; not_lg_assertions ] 


let rec js2jsil_logic 	
		(cur_fid    : string option) 
		(cc_tbl     : cc_tbl_type)
		(vis_tbl    : vis_tbl_type) 
		(fun_tbl    : pre_fun_tbl_type) 
		(a          : js_logic_assertion) : JSIL_Syntax.jsil_logic_assertion = 

	let f = js2jsil_logic cur_fid cc_tbl vis_tbl fun_tbl in
	let fe = js2jsil_lexpr in
	let get_fid fid = 
		match fid with 
		| Some fid -> fid 
		| None     -> 
			let msg = Printf.sprintf "Cannot compile assertion due to absence of fid"  in 
			raise (Failure msg) in 

	let make_overlapping_scope_ass fid x_scope_chain fid_vars_tbl =  
		let fid_vars_tbl = 
			match fid_vars_tbl with 
			| None -> Hashtbl.create 1
			| Some fid_vars_tbl -> fid_vars_tbl in 

		let fid_vis_list = 
			try Hashtbl.find vis_tbl fid with Not_found ->
				raise (Failure (Printf.sprintf "Function %s not found in the visibility table." fid)) in 
			
		let fid_vis_list = 
			match fid_vis_list with 
			| [] -> raise (Failure "DEATH! fid_vis_list")
			| _ :: rest -> rest in  
		
		let fid_vis_list_les_pairs = 
			List.map 
				(fun fid -> 
					if (fid = main_fid) 
						then fid, LLit (Loc JS2JSIL_Constants.locGlobName) 
						else fid, (try Hashtbl.find fid_vars_tbl fid with Not_found -> LVar (fid_to_lvar_fresh fid)))
				fid_vis_list in 
		let _, fid_vis_list_les = List.split fid_vis_list_les_pairs in 
		let x_scope_chain' = fe x_scope_chain in 
		LEq (x_scope_chain', LEList fid_vis_list_les), fid_vis_list_les_pairs in 

	
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
	| JSLForAll (s, a)                    -> LForAll (s, f a)
	| JSLTypes (vts)                      -> LTypes (List.map (fun (v, t) -> (LVar v, t)) vts)
	| JSLSetMem (le1, le2) 	              -> LSetMem (fe le1, fe le2)
	| JSLSetSub (le1, le2)                -> LSetSub (fe le1, fe le2)
	
	| JSLScope (x, le)                    ->
		let cur_fid = get_fid cur_fid in 
		let var_to_fid_tbl = get_scope_table cc_tbl cur_fid in 
		if (Hashtbl.mem var_to_fid_tbl x) then (
			let fid = Hashtbl.find var_to_fid_tbl x in
			if (fid = main_fid) 
				then LPointsTo (
							LLit (Loc JS2JSIL_Constants.locGlobName), 
							LLit (String x), 
							LEList [ LLit (String "d"); (fe le); LLit (Bool true); LLit (Bool true); LLit (Bool false) ])
			 	else (if (fid = cur_fid) 
					then LPointsTo (PVar JS2JSIL_Constants.var_er, LLit (String x), fe le) 
					else LPointsTo (LVar (fid_to_lvar fid), LLit (String x), fe le)))
			else (
				LPointsTo (
					LLit (Loc JS2JSIL_Constants.locGlobName), 
					LLit (String x), 
					LEList [ LLit (String "d"); (fe le); LLit (Bool true); LLit (Bool true); LLit (Bool false) ]))
	
	| JSEmptyFields (e, domain) ->
		let js_nones = List.map (fun f_name -> LLit (String f_name)) js_obj_internal_fields in 
		LEmptyFields (fe e, LSetUnion [ fe domain; (LESet js_nones) ] ) 
	
	| JSFunObj (id, f_loc, f_prototype, f_sc) -> 
		let cur_fid = get_fid (Some (Option.default main_fid cur_fid)) in 
		let f_loc' = fe f_loc in 
		let f_prototype' = fe f_prototype in 
		let id_vis_list = try Hashtbl.find vis_tbl id with _ -> raise (Failure (Printf.sprintf "Function %s not found in the visibility table." id)) in 
		let _, args, _, (_, _, _) = try Hashtbl.find fun_tbl id with _ -> raise (Failure (Printf.sprintf "Function %s not found in the fun table." id)) in
		let n_args = List.length args in
		let le_scope_chain, scope_chain_types = make_simple_scope_chain_logic_expression cur_fid id_vis_list in
		let a_scope_chain = 
			match f_sc with 
			| None -> scope_chain_types 
			| Some f_sc -> LStar (LEq (fe f_sc, le_scope_chain), scope_chain_types) in 
		(* Before we included the prototype in the footprint                        *)
		(* let st_obj_fproto = LPred (standard_object_pred_name, [f_prototype']) in *)
		let obj_fproto_cstr = 
			LPointsTo (
				f_prototype', 
				LLit (String "constructor"), 
				LEList [ LLit (String "d"); f_loc'; LLit (Bool true); LLit (Bool false); LLit (Bool true) ]) in
		LStar (
			LPred (function_object_pred_name, [ f_loc'; le_scope_chain; LLit (String id); LLit (String id); LLit (Num (float_of_int n_args)); f_prototype'] ), 
			LStar (a_scope_chain, obj_fproto_cstr))
	
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
		let vis_list_1 = try Hashtbl.find vis_tbl fid1 with _ 
			-> raise (Failure (Printf.sprintf "Function %s not found in the visibility table." fid1)) in 
		let vis_list_2 = try Hashtbl.find vis_tbl fid2 with _ 
			-> raise (Failure (Printf.sprintf "Function %s not found in the visibility table." fid2)) in 

		let shared_vis_list = compute_common_suffix [ vis_list_1; vis_list_2 ] in 
		let shared_vis_list_les_tbl = Hashtbl.create 31 in 
		List.iter	
			(fun fid -> Hashtbl.replace shared_vis_list_les_tbl fid (LVar (fid_to_lvar_fresh fid))) 
			shared_vis_list; 
		
		let a_sc1, _ = make_overlapping_scope_ass fid1 sc1 (Some shared_vis_list_les_tbl) in 
		let a_sc2, _ = make_overlapping_scope_ass fid2 sc2 (Some shared_vis_list_les_tbl) in 

		LStar (a_sc1, a_sc2)
				

	| _ -> raise (Failure "js2jsil_logic: new assertions not implemented")



let rec js2jsil_logic_cmds 
		(cc_tbl     : cc_tbl_type)
		(vis_tbl    : vis_tbl_type) 
		(fun_tbl    : pre_fun_tbl_type) 
		(logic_cmds : (Parser_syntax.annotation_type * js_logic_assertion) list) =
	let f = js2jsil_logic_cmds cc_tbl vis_tbl fun_tbl in 
	let fe = js2jsil_lexpr in
	match logic_cmds with 
	| [] -> []
	| (Parser_syntax.Fold, (JSLPred (s, les))) :: rest -> (Fold (LPred (s, List.map fe les))) :: (f rest)
	| (Parser_syntax.Unfold, (JSLPred (s, les))) :: rest -> (Unfold ((LPred (s, List.map fe les)), None)) :: (f rest) 
	| (Parser_syntax.CallSpec, (JSLPred (s, les))) :: rest -> 
		(match les with 
		| (JSLVar ret_var) :: rest_les -> 
			(*Printf.printf "I am translating a callspec for function %s with retvar %s" s ret_var;*)
			if (is_lvar_name ret_var)
			 	then ( 
			 		let args' = List.map fe rest_les in 
			 		let args' = (PVar JS2JSIL_Constants.var_scope) :: ((PVar JS2JSIL_Constants.var_this) :: args') in 
			 		CallSpec (s, ret_var, args') :: (f rest)
			 	)
			 	else raise (Failure "DEATH: js2jsil_logic_cmds")
		| _ ->  raise (Failure "DEATH: js2jsil_logic_cmds"))

	| (Parser_syntax.Assert, assertion) :: rest -> 
		let a' = js2jsil_logic None cc_tbl vis_tbl fun_tbl assertion in 
		(Assert a') :: (f rest)

	| _ -> raise (Failure "DEATH: No such logic command")



let translate_predicate_def pred_def cc_tbl vis_tbl fun_tbl = 
	let jsil_params = List.map js2jsil_lexpr pred_def.js_params in 
	let jsil_definitions = List.map (fun a -> None, (js2jsil_logic None cc_tbl vis_tbl fun_tbl a)) pred_def.js_definitions in
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
		



