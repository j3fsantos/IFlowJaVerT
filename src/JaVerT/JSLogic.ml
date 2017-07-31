open Set
open JSIL_Syntax
open JS2JSIL_Constants

module SS = Set.Make(String)



(**********************)
(*  JS Logic Grammar  *)
(**********************)

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
	| JSLId                   
	| PSI                   of string * string
	| OPSI                  of string * string 


module MyJSLExpr = 
	struct
		type t = js_logic_expr
		let compare = Pervasives.compare
	end

module JSSExpr = Set.Make(MyJSLExpr)


type js_logic_assertion =
    (**********************)
	(* first order logic  *)
	(**********************)
	| JSLTrue
	| JSLFalse
	| JSLAnd				of js_logic_assertion * js_logic_assertion
	| JSLOr					of js_logic_assertion * js_logic_assertion
	| JSLNot				of js_logic_assertion
	| JSLEq					of js_logic_expr * js_logic_expr
	| JSLLess	   			of js_logic_expr * js_logic_expr
	| JSLLessEq	   			of js_logic_expr * js_logic_expr
	| JSLStrLess    		of js_logic_expr * js_logic_expr
	| JSLSetMem  	        of js_logic_expr * js_logic_expr              
	| JSLSetSub  	        of js_logic_expr * js_logic_expr       
	| JSLForAll             of (jsil_var * jsil_type) list * js_logic_assertion
	| JSLTypes  		    of (string * jsil_type) list
	(**********************)
	(* spatial assertions *)
	(**********************)
	| JSLStar				of js_logic_assertion * js_logic_assertion
	| JSLPointsTo			of js_logic_expr * js_logic_expr * js_logic_expr
	| JSLEmp
	| JSLPred				of string * (js_logic_expr list)
	| JSEmptyFields			of js_logic_expr * js_logic_expr 
	(**********************)
	(* Iteration          *)
	(**********************)
	| JSLStartIter          of js_logic_assertion * string * js_logic_expr * js_logic_expr 



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




(**********************)
(*  JS2JSIL Logic     *)
(**********************)


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

let find_in_list (lst : string list) (x : string) = 
	let rec loop lst i = 
		match lst with 
		| []        -> raise (Failure "DEATH")
		| y :: rest -> if (x = y) then i else loop rest (i+1) in 
	loop lst 0 

let list_overlap (lst_1 : string list) (lst_2 : string list) = 
	let rec loop lst_1 lst_2 i = 
		match lst_1, lst_2 with 
		| [], [] -> i
		| x1 :: rest_1, x2 :: rest_2 -> 
			if (x1 = x2) then loop rest_1 rest_2 (i+1) else i in 
	loop lst_1 lst_2 0  


let psi (cc_tbl : cc_tbl_type) (vis_tbl : vis_tbl_type) (fid : string) (x : string) = 
	let var_to_fid_tbl = get_scope_table cc_tbl fid in 
	let fid' = try Hashtbl.find var_to_fid_tbl x 
		with Not_found -> raise (Failure "DEATH. psi: var_to_fid_tbl") in
	let vis_list = try get_vis_list vis_tbl x 
		with Not_found -> raise (Failure "DEATH. psi: get_vis_list") in	
	let i    = try find_in_list vis_list fid' 
		with Not_found -> raise (Failure "DEATH. psi: find_in_list") in 
	i 

let o_psi (vis_tbl : vis_tbl_type) (fid1 : string) (fid2 : string) = 
	let vis_list_1 = try get_vis_list vis_tbl fid1 
		with Not_found -> raise (Failure "DEATH. o_psi: get_vis_list") in	
	let vis_list_2 = try get_vis_list vis_tbl fid2
		with Not_found -> raise (Failure "DEATH. o_psi: get_vis_list") in
	let i_overlap = list_overlap vis_list_1 vis_list_2 in 
	i_overlap


let rec js2jsil_lexpr (id : string option) (scope_var : string option) (cc_tbl : cc_tbl_type) 
		(vis_tbl : vis_tbl_type) (le : js_logic_expr) :  jsil_logic_expr =
	
	let fe le = js2jsil_lexpr id scope_var cc_tbl vis_tbl le in
	
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
	| JSLScope                -> (match scope_var with 
									| Some scope_var -> PVar scope_var
									| None           -> raise (Failure "scope lexpr"))
	| JSLId                   -> (match id with 
									| Some id    -> LLit (String id) 
									| None       -> raise (Failure "id lexpr"))

	| PSI (fid, x)            -> LLit (Num (float_of_int (psi cc_tbl vis_tbl fid x)))

	| OPSI (fid1, fid2)       -> LLit (Num (float_of_int (o_psi vis_tbl fid1 fid2)))


let rec js2jsil_assertion 	
		(fid        : string option) 
		(scope_var  : string option)
		(cc_tbl     : cc_tbl_type)
		(vis_tbl    : vis_tbl_type) 
		(fun_tbl    : pre_fun_tbl_type) 
		(a          : js_logic_assertion) : JSIL_Syntax.jsil_logic_assertion = 

	let f = js2jsil_assertion fid scope_var cc_tbl vis_tbl fun_tbl in
	let fe = js2jsil_lexpr fid scope_var cc_tbl vis_tbl in
	
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
	
	| JSEmptyFields (e, domain) ->
		let js_nones = List.map (fun f_name -> LLit (String f_name)) js_obj_internal_fields in 
		LEmptyFields (fe e, LSetUnion [ fe domain; (LESet js_nones) ] ) 
	
	| _ -> raise (Failure "js2jsil_logic: new assertions not implemented")


let rec js2jsil_logic_cmd
		(cc_tbl     : cc_tbl_type)
		(vis_tbl    : vis_tbl_type) 
		(fun_tbl    : pre_fun_tbl_type) 
		(logic_cmd : js_logic_command) =
	let f = js2jsil_logic_cmd cc_tbl vis_tbl fun_tbl in 
	let fe = js2jsil_lexpr None None cc_tbl vis_tbl in

	let translate_unfold_info unfold_info = 
		match unfold_info with 
		| None -> None 
		| Some (def_id, var_le_list) -> 
			Some (def_id, List.map (fun (x, le) -> (x, fe le)) var_le_list) in 

	match logic_cmd with 

	| JSFold (JSLPred (s, les)) -> [ Fold (LPred (s, List.map fe les)) ] 

	| JSFlash (JSLPred (s, les)) -> 
		let flash_arg = LPred (s, List.map fe les) in 
		[ Unfold (flash_arg, None); Fold flash_arg ]

	| JSUnfold ((JSLPred (s, les)), unfold_info) ->
		[ Unfold ((LPred (s, List.map fe les)), (translate_unfold_info unfold_info)) ]  
	
	| JSCallSpec (spec_name, x, les) -> 
		(*Printf.printf "I am translating a callspec for function %s with retvar %s" s ret_var;*)
		let args = (PVar JS2JSIL_Constants.var_scope) :: ((PVar JS2JSIL_Constants.var_this) :: (List.map fe les)) in 
		[ CallSpec (spec_name, x, args) ] 

	| JSAssert assertion -> 
		let a' = js2jsil_assertion None None cc_tbl vis_tbl fun_tbl assertion in 
		[ Assert a' ] 

	| JSRecUnfold pred_name -> [ RecUnfold pred_name ] 

	| JSMacro (s, les) -> [ Macro (s, List.map fe les) ] 

	| JSLogicIf (le, lcthen, lcelse) -> [ LogicIf (fe le, List.concat (List.map f lcthen), List.concat (List.map f lcelse)) ] 

	| _ -> raise (Failure "DEATH: No such logic command")



let js2jsil_predicate_def pred_def cc_tbl vis_tbl fun_tbl = 
	let jsil_params = List.map (js2jsil_lexpr None None cc_tbl vis_tbl) pred_def.js_params in 
	let jsil_definitions = List.map (fun (os, a) -> os, (js2jsil_assertion None None cc_tbl vis_tbl fun_tbl a)) pred_def.js_definitions in
	{ name = pred_def.js_name; num_params = pred_def.js_num_params; params = jsil_params; definitions = jsil_definitions }



let rec js2jsil_spec_assertion (a : js_logic_assertion) (cc_tbl : cc_tbl_type) 
		(vis_tbl : vis_tbl_type) (fun_tbl : pre_fun_tbl_type) (fid : string) (is_pre : bool) : jsil_logic_assertion =
	
	print_debug (Printf.sprintf "Inside js2jsil_logic_top_level_pre for procedure %s\n" fid);
	let vis_list = try Hashtbl.find vis_tbl fid with _ -> raise (Failure "js2jsil_logic_top_level_pre - fid not found") in 
	let vis_list_len = if (is_pre) then (List.length vis_list) else (List.length vis_list) - 1 in 

	let is_global = (fid = main_fid) in
	let a'        = js2jsil_assertion (Some fid) (Some JS2JSIL_Constants.var_scope) cc_tbl vis_tbl fun_tbl a in
	
	(*  x__this == #this             *)
	let a_this    = LEq (PVar JS2JSIL_Constants.var_this, LVar this_logic_var_name) in  
	(*  l-len(x__scope) == list_size *)
	let a_scope   = LEq (LUnOp (LstLen, PVar JS2JSIL_Constants.var_scope), LLit (Num (float_of_int vis_list_len))) in 

	if (is_global) then a' else JSIL_Logic_Utils.star_asses [ a'; a_scope; a_this ]
		