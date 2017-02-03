open JSIL_Syntax

let setup_macros () = 
	
	(* GPVFold *)
	let params_fold = [ "x"; "pi1"; "pi2"; "pi3"; "pi4"; "pi5" ] in
	let params_unfold = [ "x" ] in
	let fold_args = [ LLstNth (LVar "x", LLit (Integer 1)); LLstNth (LVar "x", LLit (Integer 2)); LVar "pi1"; LVar "pi2"; LVar "pi3"; LVar "pi4"; LVar "pi5" ] in
	let folding_guard_l = LBinOp (LLstNth (LVar "x", LLit (Integer 0)), Equal, LLit (String "o")) in
	let folding_guard_r = LBinOp (LLstNth (LVar "x", LLit (Integer 0)), Equal, LLit (String "v")) in
	let folding_guard_r = LBinOp (folding_guard_r, And, (LBinOp (LLstNth (LVar "x", LLit (Integer 1)), Equal, LLit (Loc Js2jsil_constants.locGlobName)))) in
	let folding_guard = LBinOp (folding_guard_l, Or, folding_guard_r) in
	let pre_l_if_inner = LogicIf (folding_guard, [ Fold (LPred (JS_Logic_Syntax.pi_pred_name, fold_args)) ], []) in
	let pre_l_if_outer = LogicIf ( LBinOp (LTypeOf (LVar "x"), Equal, LLit (Type ListType)), [ pre_l_if_inner ], []) in
	let post_l_if_inner = LogicIf (folding_guard, [ RecUnfold JS_Logic_Syntax.pi_pred_name ], []) in
	let post_l_if_outer = LogicIf ( LBinOp (LTypeOf (LVar "x"), Equal, LLit (Type ListType)), [ post_l_if_inner ], []) in

	let gpvf = { mname = Js2jsil_constants.macro_GPVF_name; mparams = params_fold; mdefinition = pre_l_if_outer } in
	let gpvu = { mname = Js2jsil_constants.macro_GPVU_name; mparams = params_unfold; mdefinition = post_l_if_outer } in
	Hashtbl.add macro_table Js2jsil_constants.macro_GPVF_name gpvf;
	Hashtbl.add macro_table Js2jsil_constants.macro_GPVU_name gpvu