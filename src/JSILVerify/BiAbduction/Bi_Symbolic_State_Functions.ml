open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils
open Symbolic_State_Basics
open Symbolic_State_Functions

let update_abs_heap (heap : symbolic_heap) (anti_heap: symbolic_heap) loc e_field e_val p_formulae gamma =
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	let unchanged_fv_list, field_val_pair, i_am_sure_the_field_does_not_exist = find_field loc fv_list e_field p_formulae gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist, default_val with
	| Some _, _, _ 
	| None, true, LNone -> 
		LHeap.replace heap loc ((e_field, e_val) :: unchanged_fv_list, default_val)
	| None, true, _ -> 
		let v = LVar (fresh_lvar ()) in 
		Printf.printf "Updtate-abs-heap. loc: %s. field:%s. v:%s"
			loc
			(JSIL_Print.string_of_logic_expression e_field false)
			(JSIL_Print.string_of_logic_expression e_val false);
		heap_put_fv_pair heap loc e_field e_val;
		heap_put_fv_pair anti_heap loc e_field v;
	| None, false, _ ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e_field false) loc in
			raise (Failure msg)

let abs_heap_find (symb_state : symbolic_state) (anti_frame : symbolic_state) loc e_field  =
	let heap, _, pure_formulae, gamma, _ = symb_state in
	let anti_heap, _, anti_pure_formulae, _, _ = anti_frame in
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	let _, field_val_pair, i_am_sure_the_field_does_not_exist = find_field loc fv_list e_field pure_formulae gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist, default_val with
	| Some (_, f_val), _, _
		when (not (f_val = LNone)) -> 
		(f_val, false)
	| None, true, def when (not (def = LNone))  -> 
		let v = LVar (fresh_lvar ()) in 
		heap_put_fv_pair heap loc e_field v;
		heap_put_fv_pair anti_heap loc e_field v;
		(v, true)
	| Some (_, LNone), _, _
	| None, true, LNone  -> 
		let msg = Printf.sprintf "Looking up the field %s which does not exist in object %s" (JSIL_Print.string_of_logic_expression e_field false) loc in
			raise (Failure msg)
	| None, false, _ ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e_field false) loc in
			raise (Failure msg)

let abs_heap_check_field_existence  (symb_state : symbolic_state) (anti_frame : symbolic_state) loc e_field p_formulae gamma =
	let heap, _, pure_formulae, gamma, _ = symb_state in
	let anti_heap, _, anti_pure_formulae, _, _ = anti_frame in

	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	let _, field_val_pair, i_am_sure_the_field_does_not_exist = find_field loc fv_list e_field pure_formulae gamma in
	
	match field_val_pair, i_am_sure_the_field_does_not_exist, default_val with
	| Some (_, f_val), _, _ -> 
		if (Pure_Entailment.is_equal f_val LNone pure_formulae gamma) then
			(Some f_val, Some false)
			else (if (Pure_Entailment.is_different f_val LNone pure_formulae gamma) then
				(Some f_val, Some true)
				else (Some f_val, None))

	| None, true, def when (not (def = LNone))  -> 
		let v = LVar (fresh_lvar ()) in 
		heap_put_fv_pair heap loc e_field v;
		heap_put_fv_pair anti_heap loc e_field v;
		(Some v, None)

	| Some (_, LNone), _, _
	| None, true, LNone  ->	
		(Some LNone, Some false)

	| None, false, _ ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e_field false) loc in
			raise (Failure msg)