open JSIL_Syntax
open JSIL_Memory_Model
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
							let printed_hval = string_of_literal hval false in
							let printed_cell = Printf.sprintf "\n\"%s\": %s" prop printed_hval in
							if (printed_obj = "") then printed_cell else ", " ^ printed_cell)
						obj 
						"") in 
				let printed_obj = loc ^ "-> [" ^ printed_props ^ "]\n" in
				printed_heap ^ printed_obj)
		h
		""

let string_of_symb_fv_list fv_list escape_string =
	List.fold_left
		(fun ac (field, value) ->
				let field_str = string_of_logic_expression field escape_string in
				let value_str = string_of_logic_expression value escape_string in
				let field_value_str = "(" ^ field_str ^ ": " ^ value_str ^ ")"  in
				if (ac = "")
					then field_value_str
					else ac ^ ", " ^ field_value_str)
		""
		fv_list

let string_of_shallow_symb_heap heap escape_string =
	LHeap.fold
		(fun loc (fv_pairs, default_value) ac ->
			let str_fv_pairs = string_of_symb_fv_list fv_pairs escape_string in
			let default_value_str = "(default: " ^ (string_of_logic_expression default_value escape_string) ^ ")" in
			let symb_obj_str =
				(if (str_fv_pairs = "")
					then loc ^ " |-> [" ^  default_value_str ^ "]"
					else loc ^ " |-> [" ^  str_fv_pairs ^ ", " ^ default_value_str ^ "]") in
			if (ac = "\n\t") then (ac ^ symb_obj_str) else ac ^ "\n\t" ^ symb_obj_str)
		heap
		"\n\t"


let string_of_shallow_symb_store store escape_string =
	Hashtbl.fold
		(fun var le ac ->
			 let le_str = string_of_logic_expression le escape_string in
			 let var_le_str = "(" ^ var ^ ": " ^ le_str ^ ")" in
			if (ac = "") then var_le_str else ac ^ "\n\t" ^ var_le_str )
		store
		"\t"


let string_of_shallow_p_formulae p_formulae escape_string =
	DynArray.fold_left
		(fun ac cur_ass ->
			let cur_ass_str = string_of_logic_assertion cur_ass escape_string in
			if (ac = "") then cur_ass_str else ac ^ "\n\t" ^ cur_ass_str)
		"\t"
		p_formulae

let string_of_gamma (gamma : (string, jsil_type) Hashtbl.t) : string =
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

let string_of_pred pred escape_string =
	let cur_pred_name, cur_pred_args = pred in
	let args_str =
			List.fold_left
				(fun ac le ->
					let le_str = string_of_logic_expression le escape_string in
					if (ac = "") then
						le_str
					else (ac ^ ", " ^ le_str))
				""
				cur_pred_args in
	cur_pred_name ^ "(" ^ args_str ^ ")"

let string_of_preds preds escape_string =
	DynArray.fold_left
		(fun ac pred ->
			let cur_pred_str = string_of_pred pred escape_string in
			if (ac = "") then cur_pred_str else ac ^ ", " ^ cur_pred_str)
		""
		preds


let string_of_normalised_predicate (pred : Logic_Predicates.normalised_predicate) =
    let params = List.fold_left (fun ac param -> ac ^ param ^ " ") "" pred.params in
    "*** Normalised predicate ***\n" ^
    "Name : " ^ pred.name ^ "\n" ^
    "Parameters : " ^ params ^ "\n" ^
    (Printf.sprintf "Recursive : %b\n" pred.is_recursive)

let string_of_normalised_predicates (preds : (string, Logic_Predicates.normalised_predicate) Hashtbl.t) =
    Hashtbl.fold (fun pname pred ac -> ac ^ string_of_normalised_predicate pred) preds ""


let string_of_shallow_symb_state (symb_state : symbolic_state) =
	(* let heap, store, p_formulae, gamma, preds = symb_state in *)
	let str_heap       = "Heap: " ^ (string_of_shallow_symb_heap (get_heap symb_state) true) ^ "\n" in
	let str_store      = "Store: " ^ (string_of_shallow_symb_store (get_store symb_state) true) ^ "\n" in
	let str_p_formulae = "Pure Formulae: " ^ (string_of_shallow_p_formulae (get_pf symb_state) true) ^ "\n" in
	let str_gamma      = "Gamma: " ^ (string_of_gamma (get_gamma symb_state)) ^ "\n" in
	let str_preds      = "Preds: " ^ (string_of_preds (get_preds symb_state) true) ^ "\n" in
	str_heap ^ str_store ^ str_p_formulae ^ str_gamma ^ str_preds


let string_of_symb_state_list symb_states =
	let ret_str, _ =
		List.fold_left
			(fun (ac_str, index) post ->
				let cur_str = string_of_shallow_symb_state post in
				let cur_str = ("Post " ^ (string_of_int index) ^ ": " ^ cur_str ^ ";\n") in
				if (ac_str = "")
					then (cur_str, (index + 1))
					else ((ac_str ^ cur_str), (index + 1)))
			("", 0)
			symb_states in
	ret_str

let string_of_specs specs =
	List.fold_left
		(fun ac x ->
			let pre = x.pre in
			let post = x.post in
			let flag = (match x.ret_flag with | Normal -> "Normal" | Error -> "Error") in
			ac ^ (Printf.sprintf "[[ %s ]]\n[[ %s ]]\n%s\n\n"
				 (string_of_logic_assertion pre false)
				 (string_of_logic_assertion post false)
				 flag
			))
		""
		specs

let string_of_jsil_spec (spec : JSIL_Syntax.jsil_spec) =
	let name = spec.spec_name in
	let params = spec.spec_params in
	let specs = spec.proc_specs in
	let ret = name ^ " ( " in
	let ret = ret ^
		List.fold_left (fun ac x -> ac ^ (Printf.sprintf "%s " x)) "" params in
	let ret = ret ^ ")\n\n" in
	let ret = ret ^ (string_of_specs specs) in
	ret

let string_of_single_spec s_spec =
	let ret_flag = s_spec.n_ret_flag in
	let pre_str = string_of_shallow_symb_state s_spec.n_pre in
	let post_str = string_of_symb_state_list s_spec.n_post in
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
				if (ac = "\n\t") then (ac ^ var_le_str) else ac ^ ";\n\t " ^ var_le_str)
			substitution
			"\n\t") in
	"Substitution: " ^ str ^ "\n"


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
