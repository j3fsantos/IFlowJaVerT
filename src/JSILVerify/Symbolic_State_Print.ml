open JSIL_Syntax
open Symbolic_State
open JSIL_Print

(***
 Generate strings from JSIL memory types
*)
let string_of_heap (h : jsil_lit SHeap.t SHeap.t) =
	SHeap.fold
		(fun loc obj printed_heap ->
			  let printed_props =
					(SHeap.fold
						(fun prop hval printed_obj ->
							let printed_hval = string_of_literal hval in
							let printed_cell = Printf.sprintf "\n\"%s\": %s" prop printed_hval in
							if (printed_obj = "") then printed_cell else printed_obj ^ ", " ^ printed_cell)
						obj
						"") in
				let printed_obj = loc ^ "-> [" ^ printed_props ^ "]\n" in
				printed_heap ^ printed_obj)
		h
		""

let string_of_fv_list (fv_list : symbolic_field_value_list) : string =
	List.fold_left
		(fun ac (field, value) ->
				let field_str = string_of_logic_expression field in
				let value_str = string_of_logic_expression value in
				let field_value_str = "(" ^ field_str ^ ": " ^ value_str ^ ")"  in
				if (ac = "")
					then field_value_str
					else ac ^ ", " ^ field_value_str)
		""
		fv_list

let string_of_symb_heap (heap : symbolic_heap) : string=
	LHeap.fold
		(fun loc (fv_pairs, domain) ac ->
			let str_fv_pairs = string_of_fv_list fv_pairs in
			let domain_str = Option.map_default string_of_logic_expression "" domain in
			let symb_obj_str = loc ^ " |-> [" ^  str_fv_pairs ^ " | " ^ domain_str ^ "]" in
			if (ac = "\n\t") then (ac ^ symb_obj_str) else ac ^ "\n\t" ^ symb_obj_str)
		heap
		"\n\t"


let string_of_symb_store (store : symbolic_store) : string =
	Hashtbl.fold
		(fun var le ac ->
			 let le_str = string_of_logic_expression le in
			 let var_le_str = "(" ^ var ^ ": " ^ le_str ^ ")" in
			if (ac = "") then var_le_str else ac ^ "\n\t" ^ var_le_str )
		store
		"\t"


let string_of_pfs (p_formulae : pure_formulae) : string =
	DynArray.fold_left
		(fun ac cur_ass ->
			let cur_ass_str = string_of_logic_assertion cur_ass in
			if (ac = "") then cur_ass_str else ac ^ "\n\t" ^ cur_ass_str)
		"\t"
		p_formulae

let string_of_gamma (gamma : typing_environment) : string =
	let gamma_str =
		Hashtbl.fold
			(fun var var_type ac ->
				let var_type_pair_str = Printf.sprintf "(%s: %s)" var (string_of_type var_type) in
				if (ac = "")
					then var_type_pair_str
					else ac ^ "\n\t" ^ var_type_pair_str)
			gamma
			"\t" in
	gamma_str

let string_of_pred (pred : (string * (jsil_logic_expr list))) : string =
	let cur_pred_name, cur_pred_args = pred in
	let args_str =
			List.fold_left
				(fun ac le ->
					let le_str = string_of_logic_expression le in
					if (ac = "") then
						le_str
					else (ac ^ ", " ^ le_str))
				""
				cur_pred_args in
	cur_pred_name ^ "(" ^ args_str ^ ")"

let string_of_preds (pred_set : predicate_set) : string =
	DynArray.fold_left
		(fun ac pred ->
			let cur_pred_str = string_of_pred pred in
			if (ac = "") then cur_pred_str else ac ^ ", " ^ cur_pred_str)
		""
		pred_set


let string_of_symb_state (symb_state : symbolic_state) : string =
	(* let heap, store, p_formulae, gamma, preds = symb_state in *)
	let str_heap       = "Heap: " ^ (string_of_symb_heap (ss_heap symb_state)) ^ "\n" in
	let str_store      = "Store: " ^ (string_of_symb_store (ss_store symb_state)) ^ "\n" in
	let str_p_formulae = "Pure Formulae: " ^ (string_of_pfs (ss_pfs symb_state)) ^ "\n" in
	let str_gamma      = "Gamma: " ^ (string_of_gamma (ss_gamma symb_state)) ^ "\n" in
	let str_preds      = "Preds: " ^ (string_of_preds (ss_preds symb_state)) ^ "\n" in
	str_heap ^ str_store ^ str_p_formulae ^ str_gamma ^ str_preds


let string_of_symb_state_list (symb_states : symbolic_state list) : string =
	let ret_str, _ =
		List.fold_left
			(fun (ac_str, index) post ->
				let cur_str = string_of_symb_state post in
				let cur_str = ("Post " ^ (string_of_int index) ^ ": \n" ^ cur_str ^ ";\n") in
				if (ac_str = "")
					then (cur_str, (index + 1))
					else ((ac_str ^ cur_str), (index + 1)))
			("", 0)
			symb_states in
	ret_str

let string_of_specs (specs : jsil_single_spec list) : string =
	List.fold_left
		(fun ac x ->
			let pre = x.pre in
			let post = x.post in
			let flag = (match x.ret_flag with | Normal -> "Normal" | Error -> "Error") in
			ac ^ (Printf.sprintf "[[ %s ]]\n[[ %s ]]\n%s\n\n"
				 (string_of_logic_assertion pre)
				 (String.concat "; " (List.map string_of_logic_assertion post))
				 flag
			))
		""
		specs

let string_of_jsil_spec (spec : JSIL_Syntax.jsil_spec) : string =
	let name = spec.spec_name in
	let params = spec.spec_params in
	let specs = spec.proc_specs in
	let ret = name ^ " ( " in
	let ret = ret ^
		List.fold_left (fun ac x -> ac ^ (Printf.sprintf "%s " x)) "" params in
	let ret = ret ^ ")\n\n" in
	let ret = ret ^ (string_of_specs specs) in
	ret

let string_of_single_spec (s_spec : jsil_n_single_spec) : string =
	let ret_flag = s_spec.n_ret_flag in
	let pre_str  = string_of_symb_state s_spec.n_pre in
	let post_str = string_of_symb_state_list s_spec.n_post in
	let ret_flag_str =
		(match ret_flag with
		| Normal -> "normal"
		| Error -> "error") in
	"Single Spec - " ^ ret_flag_str ^ "\n\nPrecondition\n" ^ pre_str ^ "\nPostconditions\n" ^ post_str

(* spec xpto (x, y) pre: assertion, post: assertion, flag: NORMAL|ERROR *)
let string_of_n_spec (spec : jsil_n_spec) : string =
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

let string_of_n_spec_table (spec_table : specification_table) : string =
	Hashtbl.fold
		(fun spec_name spec ac ->
			let spec_str = string_of_n_spec spec in
			if ac = "" then spec_str else ac ^ "----------\n" ^ spec_str)
		spec_table
		""


let string_of_discharges (discharges : discharge_list) : string = 
	let discharge_strs = 
		List.map 
			(fun (le_pat, le) -> "(" ^ (string_of_logic_expression le_pat) ^ ", " ^ (string_of_logic_expression le) ^ ")")
			discharges in 
	"[" ^ (String.concat ", " discharge_strs) ^ "]" 


let string_of_unification_plan (up : jsil_logic_assertion list) : string = 
	let up_strs = List.map string_of_logic_assertion up in 
	"[ " ^ (String.concat "; " up_strs) ^ " ]"


let string_of_unification_step 
			(a : jsil_logic_assertion) (pat_subst : substitution) 
			(heap_frame : symbolic_heap) (preds_frame : predicate_set) 
			(discharges : discharge_list) : string = 
	Printf.sprintf "Following UP. Unifying the pat assertion %s\npat_subst: %s\nheap frame: %s\npreds_frame:%s\ndischarges:%s\n"
		(JSIL_Print.string_of_logic_assertion a)
		(string_of_substitution pat_subst)
		(string_of_symb_heap heap_frame)
		(string_of_preds preds_frame)
		(string_of_discharges discharges)


let string_of_symb_exe_result result =
	let proc_name, i, pre_post, success, msg, dot_graph = result in
	let str = "Proc " ^ proc_name ^ "  - " ^ (string_of_single_spec pre_post) ^ " -- " in
	let str =
		if (success) then
			str ^ "VERIFIED\n\n"
		else
			(match msg with
			| None ->  str ^ "FAILED\n\n"
			| Some msg -> str ^ "FAILED with msg: " ^ msg ^ "\n\n") in
	str, (proc_name, i, dot_graph)

let string_of_symb_exe_results results =
	let dot_graphs = Hashtbl.create 31 in
	let str_console = List.fold_left
		(fun ac_console result ->
			let result_console, (proc_name, i, dot_graph) = string_of_symb_exe_result result in
			Hashtbl.add dot_graphs (proc_name, i) dot_graph;
			ac_console ^ result_console)
		""
		results in
 	str_console, dot_graphs


let dot_of_search_info search_info proof_name =
	let start_time = Sys.time () in
	let string_of_search_node node =
		let cmd_info_str  = if (not (node.cmd_index = (-1))) then
			Printf.sprintf "CMD %d: %s\n" node.cmd_index node.cmd_str
			else node.cmd_str in
		let heap_str  = "HEAP: " ^ node.heap_str ^ "\n" in
		let store_str = "STORE: " ^ node.store_str ^ "\n" in
		let pfs_str = "PFs: " ^ node.pfs_str ^ "\n" in
		let gamma_str = "TYPEs: " ^ node.gamma_str ^ "\n" in
		let preds_str = "PREDs: " ^ node.preds_str ^ "\n" in
		let dashes = "-----------------------------------------\n" in
		heap_str ^ store_str ^ pfs_str ^ gamma_str ^ preds_str ^ dashes ^ cmd_info_str in


	(**
		return: 0[shape=box, label=cmd_0]; ...;n[shape=box, label=cmd_n];
	*)
	let dot_of_search_nodes nodes len =
		let rec loop ac_str i =
			if (i >= len) then ac_str
			else begin
				try
					let node = Hashtbl.find nodes i in
					let node_str = string_of_search_node node in
					let ac_str = (ac_str ^ "\t" ^ (string_of_int i) ^ "[shape=box, label=\"" ^ node_str ^ "\"];\n") in
					loop ac_str (i + 1)
				with _ -> loop ac_str (i + 1)
			end in
		loop "" 0 in


	(**
    node_i -> node_j; where j \in succ(i)
  *)
	let dot_of_edges edges len =
		let rec loop ac_str i =
			(if (i >= len) then ac_str
			else begin
				try
					let succs = Hashtbl.find edges i in
					let ac_str = ac_str ^
						(List.fold_left
							(fun i_ac_str succ -> i_ac_str ^ "\t" ^ (string_of_int i) ^ " -> " ^ (string_of_int succ) ^ ";\n")
							""
							succs) in
					loop ac_str (i + 1)
				with _ -> loop ac_str (i + 1)
				end) in
		loop "" 0 in

	let str = "digraph " ^ proof_name ^ "{\n" in
	let len = !(search_info.next_node) in
	let str_nodes = dot_of_search_nodes search_info.info_nodes len in
	let str_edges = dot_of_edges search_info.info_edges len in
	(* Printf.printf "I finish printing the edges\n";  *)
	let str = str ^ str_nodes ^ str_edges ^ "}" in
	let end_time = Sys.time () in
	JSIL_Syntax.update_statistics "unify_stores" (end_time -. start_time);
	str

let print_symb_state_and_cmd (proc : jsil_procedure) (i : int) (symb_state : symbolic_state) : unit =
	let symb_state_str = string_of_symb_state symb_state in
	let cmd = get_proc_cmd proc i in
	let cmd_str = JSIL_Print.string_of_cmd 0 0 cmd in
	let time = Sys.time() in
	print_normal (Printf.sprintf
		"----------------------------------\n--%i--\nTIME: %f\nSTATE:\n%sCMD: %s\n----------------------------------"
		i time symb_state_str cmd_str)




(**
 * ERROR MESSAGES
 **)

let string_of_US_error us_error =
	let print_lexpr = string_of_logic_expression in  
	match us_error with
	| VariableNotInStore s ->          Printf.sprintf "Variable %s not found in store" s
	| ValueMismatch (s, pat_le, le) -> Printf.sprintf "Value mismatch on variable %s: expected %s, got %s" s (print_lexpr pat_le) (print_lexpr le)
	| NoSubstitution ->                Printf.sprintf "There is no substitution"

let string_of_UH_error uh_error =
	let print_lexpr = string_of_logic_expression in  
	match uh_error with
	| CannotResolvePatLocation s ->                       Printf.sprintf "Cannot find location %s in pattern heap" s
	| CannotResolveLocation s ->                          Printf.sprintf "Cannot find location %s in symbolic heap" s
	| CannotResolveField (s, le) ->                       Printf.sprintf "Cannot resolve field (%s, %s)" s (print_lexpr le)
	| FieldValueMismatch (s, lef, lev, s', lef', lev') -> Printf.sprintf "Field value mismatch (%s, %s, %s) vs. (%s, %s, %s)" s (print_lexpr lef) (print_lexpr lev) s' (print_lexpr lef') (print_lexpr lev')
	| ValuesNotNone (s, lfv) ->                           Printf.sprintf "Non-none values in location %s: %s" s (String.concat ", " (List.map (fun (f, v) -> Printf.sprintf "(%s, %s)" (print_lexpr f) (print_lexpr v)) lfv))
	| FloatingLocations ls ->                             Printf.sprintf "Floating locations %s" (String.concat ", " ls)
	| IllegalDefaultValue le ->                           Printf.sprintf "Illegal default value %s" (print_lexpr le)
	| PatternHeapWithDefaultValue ->                      Printf.sprintf "Pattern heap has default values"
	| GeneralHeapUnificationFailure ->                    Printf.sprintf "General heap unification failure"

let string_of_UG_error ug_error =
	let print_lexpr = string_of_logic_expression in  
	let print_type = string_of_type in 
	match ug_error with
	| NoTypeForVariable s         -> Printf.sprintf "No type found for variable %s" s
	| VariableNotInSubstitution s -> Printf.sprintf "Variable %s not in substitution" s
	| TypeMismatch (pv, pt, v, t) -> Printf.sprintf "Type mismatch: (%s, %s) vs (%s, %s)" pv (print_type pt) (print_lexpr v) (print_type t)

let string_of_USS_error uss_error =
	match uss_error with
	| CannotDischargeSpecVars -> Printf.sprintf "Cannot discharge spec vars"
	| CannotUnifyPredicates   -> Printf.sprintf "Cannot unify predicates"
	| ContradictionInPFS      -> Printf.sprintf "Contradiction in pure formulae"

let string_of_USF_error usf_error =
	match usf_error with
	| CannotSubtractPredicate s -> Printf.sprintf "Cannot subtract predicate %s" s
	| CannotUnifyPredicates     -> Printf.sprintf "Cannot unify predicates"

let string_of_FSS_error fss_error =
	match fss_error with
	| ResourcesRemain       -> Printf.sprintf "Symbolic states unified, but additional resources remain"
	| CannotUnifySymbStates -> Printf.sprintf "Cannot unify symbolic states, entailment false"

let print_failure error =
	let error_message =
	(match error with
		| US  us_error  -> let us_error_str  = string_of_US_error  us_error  in "Unify stores: "                 ^ us_error_str
		| UH  uh_error  -> let uh_error_str  = string_of_UH_error  uh_error  in "Unify heaps: "                  ^ uh_error_str
		| UG  ug_error  -> let ug_error_str  = string_of_UG_error  ug_error  in "Unify gamma: "                  ^ ug_error_str
		| USS uss_error -> let uss_error_str = string_of_USS_error uss_error in "Unify symbolic states: "        ^ uss_error_str
		| USF usf_error -> let usf_error_str = string_of_USF_error usf_error in "Unify symbolic states fold: "   ^ usf_error_str
		| FSS fss_error -> let fss_error_str = string_of_FSS_error fss_error in "Fully unify symbolic states: "  ^ fss_error_str
		| Impossible s ->  Printf.sprintf "Impossible: %s" s (* MORE INFO *)
	) in "SYMB_EXEC_FAIL: " ^ error_message

