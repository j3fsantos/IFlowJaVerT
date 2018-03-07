open CCommon
open JSIL_Syntax
open Symbolic_State
open JSIL_Print

let escape_string = ref false

(***
 Generate strings from JSIL memory types
*)
let string_of_heap (h : jsil_heap) =
	Heap.fold
		(fun loc (obj, metadata, ext) printed_heap ->
      	let meta_str = MetaData.str metadata in
      	let ext_str  = Extensibility.str ext in
			  let printed_props =
					(Heap.fold
						(fun prop (perm, hval) printed_obj ->
							let printed_hval = Literal.str hval in
							let printed_perm = Permission.str perm in
							let printed_cell = 
								if (!escape_string) 
									then Printf.sprintf "\n\\\"%s\\\": %s" prop printed_hval 
									else Printf.sprintf "\n\"%s\": %s" prop printed_hval  in
							if (printed_obj = "") then printed_cell else printed_obj ^ ", " ^ printed_cell)
						obj
						"") in
				let printed_obj = loc ^ " |-> [" ^ printed_props ^ "] " ^ ext_str ^ " with metadata " ^ meta_str ^ "\n"  in
				printed_heap ^ printed_obj)
		h
		""

let string_of_pfs (p_formulae : PFS.t) : string =
	DynArray.fold_left
		(fun ac cur_ass ->
			let cur_ass_str = string_of_logic_assertion cur_ass in
			if (ac = "") then cur_ass_str else ac ^ "\n\t" ^ cur_ass_str)
		"\t"
		p_formulae

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
	let str_heap       = "Heap: " ^ (SHeap.str (ss_heap symb_state)) ^ "\n" in
	let str_store      = "Store: " ^ (SStore.str (ss_store symb_state)) ^ "\n" in
	let str_p_formulae = "Pure Formulae: " ^ (string_of_pfs (ss_pfs symb_state)) ^ "\n" in
	let str_gamma      = "Gamma:\n" ^ (TypEnv.str (ss_gamma symb_state)) ^ "\n" in
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


let string_of_pre_unification_plan (up : jsil_logic_assertion list) : string = 
	let up_strs = List.map string_of_logic_assertion up in 
	"[ " ^ (String.concat "; " up_strs) ^ " ]"

let string_of_unification_plan (up : unification_plan) : string = 
	let up_strs = List.map (fun (asrt, unify_as_is) ->
		let unify_str = Option.map_default (fun b -> Printf.sprintf "(unify_as_is: %s)" (string_of_bool b)) "" unify_as_is in
		Printf.sprintf "%s %s" (string_of_logic_assertion asrt) unify_str
		) up in 
	"[ " ^ (String.concat "; " up_strs) ^ " ]"


let string_of_unification_step 
			(a : jsil_logic_assertion) (pat_subst : substitution) 
			(heap_frame : SHeap.t) (preds_frame : predicate_set) 
			(pfs : PFS.t) (gamma : TypEnv.t)
			(discharges : discharge_list) : string = 
	Printf.sprintf "Following UP. Unifying the pat assertion %s\npat_subst: %s\nheap frame: %s\npreds_frame:%s\nPure formulae: %s\nGamma:%s\ndischarges:%s\n"
		(JSIL_Print.string_of_logic_assertion a)
		(string_of_substitution pat_subst)
		(SHeap.str heap_frame)
		(string_of_preds preds_frame)
		(string_of_pfs pfs)
		(TypEnv.str gamma)
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


let print_symb_state_and_cmd (proc : jsil_procedure) (i : int) (symb_state : symbolic_state) : unit =
	let symb_state_str = string_of_symb_state symb_state in
	let cmd = get_proc_cmd proc i in
	let cmd_str = JSIL_Print.string_of_cmd 0 0 cmd in
	let time = Sys.time() in
	print_normal (Printf.sprintf
		"----------------------------------\n--%i--\nTIME: %f\nSTATE:\n%sCMD: %s\n----------------------------------"
		i time symb_state_str cmd_str)


(* INCORRECT!!! -> THESE 3 FUNCTIONS NEED TO BE DELETED ASAP!!!!!! *)
let string_of_single_spec_table_assertion (single_spec : jsil_n_single_spec) : string =
	let pre = assertion_of_symb_state single_spec.n_pre in
	let post = assertion_of_symb_state (List.hd single_spec.n_post) in
	let flag = (match single_spec.n_ret_flag with | Normal -> "normal" | Error -> "error") in
	(Printf.sprintf "[[ %s ]]\n[[ %s ]]\n%s\n"
	 (JSIL_Print.string_of_logic_assertion pre)
	 (JSIL_Print.string_of_logic_assertion post)
	 flag)

let string_of_n_single_spec_assertion (spec : jsil_n_spec) : string = 
	List.fold_left(
		fun ac single_spec ->
			let single_spec_str = string_of_single_spec_table_assertion single_spec in
			ac ^ single_spec_str
	) "" spec.n_proc_specs


let string_of_n_spec_table_assertions 
		(spec_table : specification_table) 
		(procs_to_verify : string list) : string =
	Hashtbl.fold
		(fun spec_name spec ac ->
			if (List.mem spec_name procs_to_verify) then  
				let spec_str =  string_of_n_single_spec_assertion spec in
				ac ^ "\n" ^ spec_name ^ "\n----------\n" ^ spec_str
			else 
				ac )
		spec_table
		""




