open JSIL_Syntax

(* JS_Logic - Assertions *)

let small_tbl_size = 31 

let pi_pred_name = "Pi"
let object_class = "Object"

let fid_to_lvar fid = "_lvar_fid_" ^ fid

type js_logic_expr =
	| JSLLit				of jsil_lit
	| JSLNone
	| JSLVar				of jsil_logic_var
	| JSALoc				of string
	| JSPVar				of jsil_var
	| JSLBinOp			of js_logic_expr * bin_op * js_logic_expr
	| JSLUnOp				of unary_op * js_logic_expr
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
	| JSLPred				of string * (js_logic_expr list)
	| JSLTypes      of (string * jsil_type) list
	| JSLScope      of string * js_logic_expr 


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


let rec js2jsil_logic (js_var_to_lvar : (string, JSIL_Syntax.jsil_logic_expr) Hashtbl.t) (a : js_logic_assertion) : JSIL_Syntax.jsil_logic_assertion = 
	let f = js2jsil_logic js_var_to_lvar in 
	let fe = js2jsil_lexpr in 
	match a with 
	| JSLAnd (a1, a2)             -> LAnd ((f a1), (f a2))
	| JSLOr (a1, a2)              -> LOr ((f a1), (f a2)) 
	| JSLNot a                    -> LNot (f a)
	| JSLTrue                     -> LTrue
	| JSLFalse                    -> LFalse
	| JSLEq (le1, le2)            -> LEq ((fe le1), (fe le2)) 
	| JSLLessEq (le1, le2)        -> LLessEq ((fe le1), (fe le2)) 
	| JSLStrLess (le1, le2)       -> LStrLess ((fe le1), (fe le2))
	| JSLStar (a1, a2)            -> LStar ((f a1), (f a2)) 
	| JSLPointsTo	(le1, le2, le3) -> LPointsTo ((fe le1), (fe le2), (fe le3))
	| JSLEmp                      -> LEmp
	| JSLPred (s, les)            -> LPred (s, (List.map fe les))
	| JSLTypes (vts)              -> LTypes (List.map (fun (v, t) -> (LVar v, t)) vts)
	| JSLScope (x, le) -> 
		if (Hashtbl.mem js_var_to_lvar x) then (
			let x_lvar = Hashtbl.find js_var_to_lvar x in
			LEq (x_lvar, (fe le))
		) else (
			let msg = Printf.sprintf "scope predicate misuse: %s needs to be in the scope!\n" x in 
			raise (Failure msg)
			(* let le_desc = LEList [ LLit (String "d"); le; LLit (Bool true); LLit (Bool true); LLit (Bool false) ] in
			let ls_name = fresh_lvar () in 
			let ltf_name = fresh_lvar () in 
			let lpv_name = fresh_lvar () in 
			let lvar_ls = LVar ls_name in 
			let lvar_ltf = LVar ltf_name in 
			let lvar_lpv = LVar lpv_name in 
			let pi_args = [
				LLit (Loc Js2jsil.locGlobName); 
				LLit (String x); 
				LLit (String object_class); 
				le_desc; 
				lvar_ls; 
				lvar_ltf; 
				lvar_lpv
			] in 
			let a_pi = LPred (pi_pred_name, pi_args) in 
			let a_types = LTypes [ (ls_name, ListType); (ltf_name, ListType); (lpv_name, ListType); ] in 
			LStar (a_pi, a_types) *)
		) 
	

let var_fid_tbl_to_assertion var_to_fid_tbl = 
	let js_var_to_lvar = Hashtbl.create small_tbl_size in 
	let a = Hashtbl.fold 
		(fun x fid ac ->
			let x_fid = LVar (fid_to_lvar fid) in 
			let x_val_name = JSIL_Memory_Model.fresh_lvar () in 
			let x_val = LVar x_val_name in 
			let le_desc = LEList [ LLit (String "d"); x_val; LLit (Bool true); LLit (Bool true); LLit (Bool false) ] in 
			let a_new = LPointsTo (x_fid, LLit (String x), le_desc) in
			Hashtbl.add js_var_to_lvar x x_val;
			if (ac = LEmp) then a_new else LStar (ac, a_new))
		var_to_fid_tbl
		LEmp in 
	a, js_var_to_lvar
	
	
let make_scope_chain_assertion vis_list = 
	let rec loop a fids =
		match fids with 
		| [] -> a 
		| fid :: rest -> 
			let a_new = LPointsTo (PVar Js2jsil_constants.var_scope, LLit (String fid), LVar (fid_to_lvar fid)) in 
			let a = if (a = LEmp) then a_new else (LStar (a, a_new)) in 
			loop a rest in 
	loop LEmp vis_list 
	

let rec js2jsil_logic_top_level a (var_to_fid_tbl : (string, string) Hashtbl.t) (vis_list : string list) =
	let a_env_records, js_var_to_lvar = var_fid_tbl_to_assertion var_to_fid_tbl in 
	let a_scope_chain = make_scope_chain_assertion vis_list in 
	let a' = js2jsil_logic js_var_to_lvar a in 
	LStar (a', (LStar (a_env_records, a_scope_chain))) 
	
	
	


		
