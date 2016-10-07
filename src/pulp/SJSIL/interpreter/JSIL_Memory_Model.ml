open JSIL_Syntax

let small_tbl_size = 31

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
(** JSIL Heaps                      **)
(*************************************)
 module SHeap = Hashtbl.Make(
	struct
		type t = string
		let equal = (=)
		let hash = Hashtbl.hash
	end)


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
type symbolic_state     = symbolic_heap * symbolic_store * pure_formulae * typing_environment * predicate_set


(*************************************)
(** Abstract Heap functions         **)
(*************************************)


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





(*************************************)
(** Pure Formulae functions         **)
(*************************************)
let copy_p_formulae pfs =
	let new_pfs = DynArray.copy pfs in
	new_pfs

let extend_pf pfs pfs_to_add =
	let is_pf_fresh pf_to_add =
		(DynArray.fold_left
			(fun ac pf -> (ac && (not (pf = pf_to_add))))
			true
			pfs) in

	let is_pf_sensible pf_to_add =
		(match pf_to_add with
		| LEq (le1, le2) -> (not (le1 = le2))
		| LTrue          -> false
		| _              -> true) in

	let rec loop pfs_to_add fresh_pfs_to_add =
		match pfs_to_add with
		| [] -> fresh_pfs_to_add
		| pf_to_add :: rest_pfs_to_add ->
			if ((is_pf_sensible pf_to_add) && (is_pf_fresh pf_to_add))
				then loop rest_pfs_to_add (pf_to_add :: fresh_pfs_to_add)
				else loop rest_pfs_to_add fresh_pfs_to_add in
	DynArray.append (DynArray.of_list (loop pfs_to_add [])) pfs

let pfs_to_list pfs = DynArray.to_list pfs

let pf_of_store store subst =
	Hashtbl.fold
		(fun var le pfs ->
			try
				let sle = Hashtbl.find subst var in
				((LEq (sle, le)) :: pfs)
			with _ -> pfs)
		store
		[]

let pf_of_store2 store =
	Hashtbl.fold
		(fun var le pfs -> ((LEq (PVar var, le)) :: pfs))
		store
		[]

let pf_of_substitution subst =
	Hashtbl.fold
		(fun var le pfs ->
			if (is_lvar_name var)
				then ((LEq (LVar var, le)) :: pfs)
				else pfs)
		subst
		[]


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


(*************************************)
(** Symbolic State functions        **)
(*************************************)
let get_heap symb_state =
	let heap, _, _, _, _ = symb_state in
	heap

let get_store symb_state =
	let _, store, _, _, _ = symb_state in
	store

let get_pf symb_state =
	let _, _, pf, _, _ = symb_state in
	pf

let get_gamma symb_state =
	let _, _, _, gamma, _ = symb_state in
	gamma

let get_preds symb_state =
	let _, _, _, _, preds = symb_state in
	preds

let get_pf_list symb_state =
	let pf = get_pf symb_state in
	pfs_to_list pf

let symb_state_add_predicate_assertion symb_state pred_assertion =
	let preds = get_preds symb_state in
	extend_pred_set preds pred_assertion

let symb_state_replace_store symb_state new_store =
	let heap, _, pfs, gamma, preds = symb_state in
	(heap, new_store, pfs, gamma, preds)

let rec extend_symb_state_with_pfs symb_state pfs_to_add =
	extend_pf (get_pf symb_state) pfs_to_add

let copy_symb_state symb_state =
	let heap, store, p_formulae, gamma, preds = symb_state in
	let c_heap      = LHeap.copy heap in
	let c_store     = copy_store store in
	let c_pformulae = copy_p_formulae p_formulae in
	let c_gamma     = copy_gamma gamma in
	let c_preds     = copy_pred_set preds in
	(c_heap, c_store, c_pformulae, c_gamma, c_preds)

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

type prunning_table = (string, bool array) Hashtbl.t

let copy_single_spec s_spec =
	let copy_pre  = copy_symb_state s_spec.n_pre in
	let copy_post = List.map copy_symb_state s_spec.n_post in
	{
		n_pre        = copy_pre;
		n_post       = s_spec.n_post;
		n_ret_flag   = s_spec.n_ret_flag;
		n_lvars      = s_spec.n_lvars;
		n_post_lvars = s_spec.n_post_lvars;
		n_subst      = s_spec.n_subst
	}

let init_post_prunning_info () = Hashtbl.create small_tbl_size

let update_post_prunning_info_with_spec prunning_info n_spec =
	let spec_post_prunning_info =
		List.map
			(fun spec ->
				let number_of_posts = List.length spec.n_post in
				Array.make number_of_posts false)
			n_spec.n_proc_specs in
	Hashtbl.replace prunning_info n_spec.n_spec_name spec_post_prunning_info

let filter_useless_posts_in_single_spec	spec prunning_array =
	let rec loop posts i processed_posts =
		(match posts with
		| [] -> processed_posts
		| post :: rest_posts ->
			if (prunning_array.(i))
				then loop rest_posts (i + 1) (post :: processed_posts)
				else loop rest_posts (i + 1) processed_posts) in
	let useful_posts = loop spec.n_post 0 [] in
	{ spec with n_post = useful_posts }

let filter_useless_posts_in_multiple_specs proc_name specs prunning_info =
	try
		let prunning_info = Hashtbl.find prunning_info proc_name in
		let new_specs = List.map2 filter_useless_posts_in_single_spec specs prunning_info in
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
	post_prunning_info  : (string, (bool array) list) Hashtbl.t;
	spec_number         : int
}

let make_symb_exe_search_info node_info post_prunning_info spec_number =
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
				post_prunning_info  = post_prunning_info;
				spec_number         = spec_number
			} in
		Hashtbl.replace new_search_info.info_edges 0 [];
		Hashtbl.replace new_search_info.info_nodes 0 node_info;
		new_search_info
	end

let udpdate_search_info search_info info_node vis_tbl =
	{
		search_info with cur_node_info = info_node; vis_tbl = vis_tbl
	}

let copy_vis_tbl vis_tbl = Hashtbl.copy vis_tbl

let update_vis_tbl search_info vis_tbl =
	{	search_info with vis_tbl = vis_tbl }

let activate_post_in_post_prunning_info symb_exe_info proc_name post_number =
	try
		let post_prunning_info_array_list =
			Hashtbl.find (symb_exe_info.post_prunning_info) proc_name in
		let post_prunning_info_array = List.nth post_prunning_info_array_list (symb_exe_info.spec_number) in
		post_prunning_info_array.(post_number) <- true
	with Not_found -> ()
