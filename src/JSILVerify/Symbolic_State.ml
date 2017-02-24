open JSIL_Syntax
open Z3

(********************************************************)
(** Auxiliar functions for generating new program/logical
    variable names and new abstract locations          **)
(********************************************************)

let fresh_sth (name : string) : (unit -> string) =
  let counter = ref 0 in
  let rec f () =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f

let abs_loc_prefix = "_$l_"
let lvar_prefix = "_lvar_"
let pvar_prefix = "_pvar_"

let fresh_aloc = fresh_sth abs_loc_prefix
let fresh_lvar = fresh_sth lvar_prefix
let fresh_pvar = fresh_sth pvar_prefix

let fresh_lvar_from_lvar_name =
	let lvar_tbl = Hashtbl.create small_tbl_size in
	(fun (pred_name : string) (var : string) ->
		if (Hashtbl.mem lvar_tbl (pred_name, var))
			then (
				let i = Hashtbl.find lvar_tbl (pred_name, var) in
				Hashtbl.replace lvar_tbl (pred_name, var) (i + 1);
				var ^ "_" ^ (string_of_int i)
			) else
			(
				(* Printf.printf  "Could not find the pair (%s, %s) in the pred_lvar_tbl\n" pred_name var; *)
				Hashtbl.replace lvar_tbl (pred_name, var) 1;
				var ^ "_" ^ (string_of_int 0)
			))

let is_abs_loc_name (name : string) : bool =
	if ((String.length name) < 4)
		then false
		else ((String.sub name 0 4) = abs_loc_prefix)

let is_lvar_name (name : string) : bool =
	((String.sub name 0 1) = "#") || (((String.length name) > 6) && ((String.sub name 0 6) = lvar_prefix))

let is_pvar_name (name : string) : bool =
	(not ((is_abs_loc_name name) || (is_lvar_name name)))

(* A substitution type                                 *)
type substitution = ((string, jsil_logic_expr) Hashtbl.t)

(* Symbolic State Error                                *)
exception Symb_state_error of string;;

(*************************************)
(** Symbolic States                 **)
(*************************************)
module LHeap = Hashtbl.Make(
	struct
		type t = string
		let equal = (=)
		let hash = Hashtbl.hash
	end)

type symbolic_heap      = (((jsil_logic_expr * jsil_logic_expr) list) * jsil_logic_expr)  LHeap.t
type symbolic_store     = (string, jsil_logic_expr) Hashtbl.t
type pure_formulae      = (jsil_logic_assertion DynArray.t)
type typing_environment = ((string, jsil_type) Hashtbl.t)
type predicate_set      = ((string * (jsil_logic_expr list)) DynArray.t)


type symbolic_state = symbolic_heap * symbolic_store * pure_formulae * typing_environment * predicate_set (* * (((Solver.solver * smt_translation_ctx) option) ref) *)



(*************************************)
(** Abstract Heap functions         **)
(*************************************)

let abs_heap_get heap loc =
	try Some (LHeap.find heap loc) with _ -> None

let get_heap_domain heap subst =
	let domain =
		LHeap.fold
			(fun l _ ac -> l :: ac)
			heap
			[] in

	let rec loop locs matched_abs_locs free_abs_locs concrete_locs =
		match locs with
		| [] -> concrete_locs @ matched_abs_locs @ free_abs_locs
		| loc :: rest_locs ->
			if (is_abs_loc_name loc)
				then (
					if (Hashtbl.mem subst loc)
						then loop rest_locs (loc :: matched_abs_locs) free_abs_locs concrete_locs
						else loop rest_locs matched_abs_locs (loc :: free_abs_locs) concrete_locs)
				else loop rest_locs matched_abs_locs free_abs_locs (loc :: concrete_locs) in

	loop domain [] [] []


let extend_abs_heap (heap : symbolic_heap) (loc : string) (field : jsil_logic_expr) (value : jsil_logic_expr) = 
	let fv_list, def_val = try LHeap.find heap loc with _ -> 
		raise (Failure "loc does not exist in the heap") in  
	LHeap.replace heap loc (((field, value) :: fv_list), def_val)


(*************************************)
(** Abstract Store functions        **)
(*************************************)
let store_get_var_val store x =
	try
		Some (Hashtbl.find store x)
	with Not_found -> None

let store_get_var store var =
	(try
		Hashtbl.find store var
	with _ ->
		let msg = Printf.sprintf "store_get_var: fatal error. var: %s" var in
		raise (Failure msg))

let update_abs_store store x ne =
	Hashtbl.replace store x ne

let copy_store store =
	let new_store = Hashtbl.copy store in
	new_store

let extend_abs_store x store gamma =
	let new_l_var_name = fresh_lvar () in
	let new_l_var = LVar new_l_var_name in
	(try
		let x_type = Hashtbl.find gamma x in
		Hashtbl.add gamma new_l_var_name x_type
	with _ -> ());
	Hashtbl.add store x new_l_var;
	new_l_var

let get_store_domain store =
	Hashtbl.fold
		(fun x _ ac -> x :: ac)
		store
		[]





(*************************************)
(** Pure Formulae functions         **)
(*************************************)

let pfs_to_list (pfs : pure_formulae) =
	DynArray.to_list pfs


let add_pure_assertion (pfs : pure_formulae) (a : jsil_logic_assertion) = 
	DynArray.add pfs a
	


(*************************************)
(** Typing Environment functions    **)
(*************************************)
let mk_gamma () = Hashtbl.create small_tbl_size

let gamma_get_type gamma var =
	try Some (Hashtbl.find gamma var) with Not_found -> None

let update_gamma (gamma : typing_environment) x te =
	(match te with
	| None -> Hashtbl.remove gamma x
	| Some te -> Hashtbl.replace gamma x te)

let weak_update_gamma (gamma : typing_environment) x te =
	(match te with
	| None -> ()
	| Some te -> Hashtbl.replace gamma x te)

let copy_gamma gamma =
	let new_gamma = Hashtbl.copy gamma in
	new_gamma

let extend_gamma gamma new_gamma =
	Hashtbl.iter
		(fun v t ->
			if (not (Hashtbl.mem gamma v))
				then Hashtbl.add gamma v t)
		new_gamma

let filter_gamma gamma vars =
	let new_gamma = Hashtbl.create small_tbl_size in
	Hashtbl.iter
		(fun v v_type ->
			(if (List.mem v vars) then
				Hashtbl.replace new_gamma v v_type))
		gamma;
	new_gamma

let filter_gamma_with_subst gamma vars subst =
	let new_gamma = Hashtbl.create small_tbl_size in
	Hashtbl.iter
		(fun v v_type ->
			(if (List.mem v vars) then
				try
					match (Hashtbl.find subst v) with
					| LVar new_v -> Hashtbl.replace new_gamma new_v v_type
					| _ -> ()
				with Not_found -> ()))
		gamma;
	new_gamma

let get_gamma_vars gamma =
	Hashtbl.fold
		(fun var t ac_vars -> (var :: ac_vars))
		gamma
		[]

let get_gamma_var_type_pairs gamma =
	Hashtbl.fold
		(fun var t ac_vars -> ((var, t) :: ac_vars))
		gamma
		[]


(*************************************)
(** Predicate Set functions         **)
(*************************************)
let copy_pred_set preds =
	let new_preds = DynArray.copy preds in
	new_preds

let extend_pred_set preds pred_assertion =
	match pred_assertion with
	| (pred_name, args) ->
		DynArray.add preds (pred_name, args)
	| _ -> raise (Symb_state_error "Illegal Predicate Assertion")

let preds_add_predicate_assertion preds (pred_name, args) = DynArray.add preds (pred_name, args)

let preds_to_list preds = DynArray.to_list preds

let preds_of_list list_preds = DynArray.of_list list_preds

let find_predicate_assertion_index preds (pred_name, args) =
	let len = DynArray.length preds in
	let rec loop i =
		if (i >= len) then None else (
			let cur_pred_name, cur_args = DynArray.get preds i in
			if (not (cur_pred_name = pred_name)) then loop (i+1) else (
				let equal_args = List.fold_left2 (fun ac a1 a2 -> if (not ac) then ac else a1 = a2) true args cur_args in
				if (equal_args) then Some i else loop (i+1))) in
	loop 0

let remove_predicate_assertion preds (pred_name, args) =
	let index = find_predicate_assertion_index preds (pred_name, args) in
	match index with
	| Some index -> DynArray.delete preds index
	| None -> ()


(*************************************)
(** Symbolic State functions        **)
(*************************************)
let get_heap symb_state =
	let heap, _, _, _, _ (*, _ *) = symb_state in
	heap

let get_store symb_state =
	let _, store, _, _, _ (*, _ *) = symb_state in
	store

let get_pf symb_state =
	let _, _, pf, _, _ (*, _ *) = symb_state in
	pf

let get_gamma symb_state =
	let _, _, _, gamma, _ (*, _ *) = symb_state in
	gamma

let get_preds symb_state =
	let _, _, _, _, preds (*, _ *) = symb_state in
	preds

(* let get_solver symb_state =
	let _, _, _, _, _, solver = symb_state in
	solver *)

let get_pf_list symb_state =
	let pf = get_pf symb_state in
	pfs_to_list pf

let symb_state_add_predicate_assertion symb_state pred_assertion =
	let preds = get_preds symb_state in
	extend_pred_set preds pred_assertion

let symb_state_replace_store symb_state new_store =
	let heap, _, pfs, gamma, preds, solver = symb_state in
	(heap, new_store, pfs, gamma, preds, solver)

(****************************************)
(** Normalised Specifications          **)
(****************************************)
type jsil_n_single_spec = {
	n_pre         : symbolic_state;
	n_post        : symbolic_state list;
	n_ret_flag    : jsil_return_flag;
	n_lvars       : string list;
	n_post_lvars  : string list list;
	n_subst       : substitution
}

type jsil_n_spec = {
    n_spec_name   : string;
    n_spec_params : jsil_var list;
	n_proc_specs  : jsil_n_single_spec list
}

type specification_table = (string, jsil_n_spec) Hashtbl.t

type pruning_table = (string, bool array) Hashtbl.t

let init_post_pruning_info () = Hashtbl.create small_tbl_size

let update_post_pruning_info_with_spec pruning_info n_spec =
	let spec_post_pruning_info =
		List.map
			(fun spec ->
				let number_of_posts = List.length spec.n_post in
				Array.make number_of_posts false)
			n_spec.n_proc_specs in
	Hashtbl.replace pruning_info n_spec.n_spec_name spec_post_pruning_info

let filter_useless_posts_in_single_spec	spec pruning_array =
	let rec loop posts i processed_posts =
		(match posts with
		| [] -> processed_posts
		| post :: rest_posts ->
			if (pruning_array.(i))
				then loop rest_posts (i + 1) (post :: processed_posts)
				else loop rest_posts (i + 1) processed_posts) in
	let useful_posts = loop spec.n_post 0 [] in
	{ spec with n_post = useful_posts }

let filter_useless_posts_in_multiple_specs proc_name specs pruning_info =
	try
		let pruning_info = Hashtbl.find pruning_info proc_name in
		let new_specs = List.map2 filter_useless_posts_in_single_spec specs pruning_info in
		new_specs
	with Not_found -> specs


(****************************************)
(** Normalised Predicate Definitions   **)
(****************************************)
type n_jsil_logic_predicate = {
	n_pred_name        : string;
	n_pred_num_params  : int;
	n_pred_params      : jsil_logic_var list;
	n_pred_definitions : symbolic_state list;
	n_pred_is_rec      : bool
}

let get_pred pred_tbl pred_name =
	try
		Hashtbl.find pred_tbl pred_name
	with _ ->
		let msg = Printf.sprintf "Predicate %s does not exist" pred_name in
		raise (Failure msg)

(***************************************************)
(** JSIL Program Annotated for Symbolic Execution **)
(***************************************************)
type symb_jsil_program = {
	program    	: jsil_program;
	spec_tbl   	: specification_table;
	which_pred 	: (string * int * int, int) Hashtbl.t;
	pred_defs  	: (string, n_jsil_logic_predicate) Hashtbl.t
}


(*********************************************************)
(** Information to keep track during symbolic exeuction **)
(*********************************************************)
type search_info_node = {
	heap_str    : string;
	store_str   : string;
	pfs_str     : string;
	gamma_str   : string;
	preds_str   : string;
	(* cmd index *)
	cmd_index   : int;
	cmd_str     : string;
	(* node number *)
	node_number : int
}

type symbolic_execution_search_info = {
	vis_tbl    		      : (int, int) Hashtbl.t;
	cur_node_info       :	search_info_node;
	info_nodes 		      : (int, search_info_node) Hashtbl.t;
	info_edges          : (int, int list) Hashtbl.t;
	next_node           : int ref;
	post_pruning_info   : (string, (bool array) list) Hashtbl.t;
	spec_number         : int
}

let make_symb_exe_search_info node_info post_pruning_info spec_number =
	if (not (node_info.node_number = 0)) then
		raise (Failure "the node number of the first node must be 0")
	else begin
		let new_search_info =
			{
				vis_tbl             = Hashtbl.create small_tbl_size;
				cur_node_info       = node_info;
				info_nodes          = Hashtbl.create small_tbl_size;
				info_edges          = Hashtbl.create small_tbl_size;
				next_node           = ref 1;
				post_pruning_info   = post_pruning_info;
				spec_number         = spec_number
			} in
		Hashtbl.replace new_search_info.info_edges 0 [];
		Hashtbl.replace new_search_info.info_nodes 0 node_info;
		new_search_info
	end

let update_search_info search_info info_node vis_tbl =
	{
		search_info with cur_node_info = info_node; vis_tbl = vis_tbl
	}

let copy_vis_tbl vis_tbl = Hashtbl.copy vis_tbl

let update_vis_tbl search_info vis_tbl =
	{	search_info with vis_tbl = vis_tbl }

let activate_post_in_post_pruning_info symb_exe_info proc_name post_number =
	try
		let post_pruning_info_array_list =
			Hashtbl.find (symb_exe_info.post_pruning_info) proc_name in
		let post_pruning_info_array = List.nth post_pruning_info_array_list (symb_exe_info.spec_number) in
		post_pruning_info_array.(post_number) <- true
	with Not_found -> ()
