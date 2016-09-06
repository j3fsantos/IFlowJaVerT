open JSIL_Syntax
open JSIL_Memory_Model
open JSIL_Print

(***
 Generate strings from JSIL memory types
*)

let string_of_symb_fv_list fv_list = 
	List.fold_left
		(fun ac (field, value) ->
				let field_str = string_of_logic_expression field false in 
				let value_str = string_of_logic_expression value false in 
				let field_value_str = "(" ^ field_str ^ ": " ^ value_str ^ ")"  in 
				if (ac = "") 
					then field_value_str 
					else ac ^ ", " ^ field_value_str)
		""
		fv_list 

let string_of_shallow_symb_heap heap = 
	LHeap.fold
		(fun loc (fv_pairs, default_value) ac -> 
			let str_fv_pairs = string_of_symb_fv_list fv_pairs in 
			let default_value_str = "(default: " ^ (string_of_logic_expression default_value false) ^ ")" in
			let symb_obj_str = 
				(if (str_fv_pairs = "") 
					then loc ^ " |-> [" ^  default_value_str ^ "]" 
					else loc ^ " |-> [" ^  str_fv_pairs ^ ", " ^ default_value_str ^ "]") in 
			if (ac = "") then symb_obj_str else ac ^ ", " ^ symb_obj_str)
		heap
		""
		
		
let string_of_shallow_symb_store store = 
	Hashtbl.fold 
		(fun var v_val ac ->
			 let v_val_str = string_of_logic_expression v_val false in 
			 let var_val_str = "(" ^ var ^ ": " ^ v_val_str ^ ")" in 
			if (ac = "") then var_val_str else ac ^ ", " ^ var_val_str )
		store
		""


let string_of_shallow_p_formulae p_formulae = 
	DynArray.fold_left
		(fun ac cur_ass -> 
			let cur_ass_str = string_of_logic_assertion cur_ass false in 
			if (ac = "") then cur_ass_str else ac ^ ", " ^ cur_ass_str)
		""
		p_formulae

let string_of_gamma (gamma : (string, jsil_type) Hashtbl.t) : string = 
	let gamma_str = 
		Hashtbl.fold 
			(fun var var_type ac ->
				let var_type_pair_str = Printf.sprintf "(%s: %s)" var (string_of_type var_type) in 
				if (ac = "") 
					then var_type_pair_str
					else ac ^ ", " ^ var_type_pair_str)
			gamma 
			"" in
	gamma_str 

let string_of_pred pred = 
	let cur_pred_name, cur_pred_args = pred in 
	let args_str = 
			List.fold_left
				(fun ac le -> 
					let le_str = string_of_logic_expression le false in 
					if (ac = "") then 
						le_str 
					else (ac ^ ", " ^ le_str))
				""
				cur_pred_args in
	cur_pred_name ^ "(" ^ args_str ^ ")" 
	
let string_of_preds preds = 
	DynArray.fold_left
		(fun ac pred ->
			let cur_pred_str = string_of_pred pred in 
			if (ac = "") then cur_pred_str else ac ^ ", " ^ cur_pred_str)
		""
		preds

let string_of_shallow_symb_state symb_state =
	let heap, store, p_formulae, gamma, preds = symb_state in  
	let str_heap = "Heap: " ^ (string_of_shallow_symb_heap heap) ^ "\n" in 
	let str_store = "Store: " ^ (string_of_shallow_symb_store store) ^ "\n" in 
	let str_p_formulae = "Pure Formulae: " ^ (string_of_shallow_p_formulae p_formulae) ^ "\n" in 
	let str_gamma = "Gamma: " ^ (string_of_gamma gamma) ^ "\n" in
	let str_preds = "Preds: " ^ (string_of_preds preds) ^ "\n" in  
	str_heap ^ str_store ^ str_p_formulae ^ str_gamma ^ str_preds

let string_of_single_spec s_spec = 
	let ret_flag = s_spec.n_ret_flag in 
	let pre_str = string_of_shallow_symb_state s_spec.n_pre in 
	let post_str = string_of_shallow_symb_state s_spec.n_post in 
	let ret_flag_str = 
		(match ret_flag with 
		| Normal -> "normal"
		| Error -> "error") in 
	"Single Spec - " ^ ret_flag_str ^ "\nPre " ^ pre_str ^ "Post " ^ post_str 

(* spec xpto (x, y) pre: assertion, post: assertion, flag: NORMAL|ERROR *) 
let string_of_n_spec spec = 
	let spec_name = spec.n_spec_name in 
	let spec_params = spec.n_spec_params in 
	let pre_post_list = spec.n_proc_specs in
	let params_str = 
		List.fold_left
			(fun ac param -> if (ac = "") then param else ac ^ ", " ^ param)
			""
			spec_params in
	let str = "Specs for " ^ spec_name ^ " (" ^ params_str ^ "): \n" in 
	let pre_post_list_str =
		List.fold_left
			(fun ac single_spec -> 
				let single_spec_str = string_of_single_spec single_spec in 
				if (ac = "") then single_spec_str else ac ^ single_spec_str)
			""
			pre_post_list in
		str ^ pre_post_list_str 


let string_of_n_spec_table spec_table = 
	Hashtbl.fold 
		(fun spec_name spec ac -> 
			let spec_str = string_of_n_spec spec in 
			if ac = "" then spec_str else ac ^ "----------\n" ^ spec_str)
		spec_table
		""

let string_of_store store = 
	Hashtbl.fold 
		(fun (var : string) (v_val : jsil_lit) (ac : string) ->
			let v_val_str = string_of_literal v_val true in 
			let var_val_str = var ^ ": " ^ v_val_str  in 
			if (ac = "") then var_val_str else ac ^ "; " ^ var_val_str)
		store
		"Store: "

let string_of_substitution substitution = 
	let str = 
		(Hashtbl.fold 
			(fun (var : string) (le : jsil_logic_expr) (ac : string) ->
				let le_str = string_of_logic_expression le false in 
				let var_le_str = var ^ ": " ^ le_str  in 
				if (ac = "") then var_le_str else ac ^ "; " ^ var_le_str)
			substitution
			"") in 
	"Substitution: " ^ str ^ "\n"


let string_of_symb_exe_result result = 
	let proc_name, pre_post, success, msg = result in 
	let str = "Proc " ^ proc_name ^ "  - " ^ (string_of_single_spec pre_post) ^ " -- " in 
	let str = 
		if (success) then 
			str ^ "VERIFIED\n\n" 
		else
			(match msg with 
			| None ->  str ^ "FAILED\n\n"
			| Some msg -> str ^ "FAILED with msg: " ^ msg ^ "\n\n") in 
	str

let string_of_symb_exe_results results = 
	let str = List.fold_left
		(fun ac result -> 
			let result_str = string_of_symb_exe_result result in 
			ac ^ result_str)
		""
		results in 
 	str