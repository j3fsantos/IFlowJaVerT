open SSyntax
open JSIL_Logic_Syntax

let symb_evaluate_bcmd (bcmd : basic_jsil_cmd) heap store pure_formulae which_pred = 
	match bcmd with 
	| SSkip -> Empty

	| SAssignment (x, e) -> 
		let nle = symb_evaluate_expr e store in 
		update_abs_store store x nle; 
		nle
	
	| SPhiAssignment (x, x_arr) -> 
		let x_live = x_arr.(which_pred) in 
		let nle = abs_store_find store x_live in 
		update_abs_store store x nle
	
	| SNew x -> 
		let new_loc = fresh_loc () in 
		update_abs_heap heap new_loc (LLit (String proto_f)) (LLit Null); 
		LLVar new_loc 
	
	| SLookup (x, e1, e2) -> 
		let nle1 = symb_evaluate_expr e1 store in
		let nle2 = symb_evaluate_expr e2 store in 	
		let nle_lu = abs_heap_find heap nle1 nle2 in 
		update_abs_store store x nle_lu; 
		nle_lu
	
	| SMutation (e1, e2, e3) ->
		let nle1 = symb_evaluate_expr e1 store in
		let nle2 = symb_evaluate_expr e2 store in 	
		let nle3 = symb_evaluate_expr e3 store in
		update_abs_heap heap nle1 nle2 nle3;
		nle3
	
	| SDelete (e1, e2) -> 
		let nle1 = symb_evaluate_expr e1 store in
		let nle2 = symb_evaluate_expr e2 store in 
		remove_cell_abs_heap heap nle1 nle2
										
		| SHasField (x, e1, e2) -> 
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in 	
		(match v_e1, v_e2 with 
		| Loc l, String f -> 
			let v = Bool (SHeap.mem heap (l, f)) in 
			Hashtbl.replace store x v; 
			v
		| _, _ -> raise (Failure "Illegal Field Check"))
	
		
	
	| _, _ -> raise (Failure "Illegal field inspection"))	
	
	