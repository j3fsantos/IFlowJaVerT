open SJSIL_Syntax
open SJSIL_Memory_Model
open JSIL_Print

(***
 Generate strings from JSIL memory types
*)

let string_of_shallow_symb_heap heap = 
	LHeap.fold
		(fun loc (fv_pairs, default_value) ac -> 
			let str_fv_pairs = 
				List.fold_left
					(fun ac (field, value) ->
						let field_str = string_of_logic_expression field false in 
						let value_str = string_of_logic_expression value false in 
						let field_value_str = "(" ^ field_str ^ ": " ^ value_str ^ ")"  in 
						if (ac = "") 
							then field_value_str 
							else ac ^ ", " ^ field_value_str)
					""
					fv_pairs in 
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


let string_of_shallow_symb_state heap store p_formulae gamma = 
	let str = "Symbolic State: \n" in 
	let str_heap = "\t Heap: " ^ (string_of_shallow_symb_heap heap) ^ "\n" in 
	let str_store = "\t Store: " ^ (string_of_shallow_symb_store store) ^ "\n" in 
	let str_p_formulae = "\t Pure Formulae: " ^ (string_of_shallow_p_formulae p_formulae) ^ "\n" in 
	let str_gamma = "\t Gamma: " ^ (string_of_gamma gamma) ^ "\n" in 
	str ^ str_heap ^ str_store ^ str_p_formulae

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
				let pre_heap, pre_store, pre_p_formulae, pre_gamma = single_spec.n_pre in 
				let post_heap, post_store, post_p_formulae, post_gamma = single_spec.n_post in 
				let ret_flag = single_spec.n_ret_flag in 
				let pre_str = string_of_shallow_symb_state pre_heap pre_store pre_p_formulae pre_gamma in 
				let post_str = string_of_shallow_symb_state post_heap post_store post_p_formulae post_gamma in 
				let ret_flag_str = 
					(match ret_flag with 
					| Normal -> "normal"
					| Error -> "error") in 
				let single_spec_str = "Single Spec - " ^ ret_flag_str ^ "\n Pre " ^ pre_str ^ "Post " ^ post_str in 
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
			if (ac != "") then var_val_str else ac ^ "; " ^ var_val_str)
		store
		"Store: "
