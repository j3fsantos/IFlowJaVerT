open JSIL_Syntax
open Z3

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

type symbolic_field_value_list = ((jsil_logic_expr * jsil_logic_expr) list)
type symbolic_discharge_list   = ((jsil_logic_expr * jsil_logic_expr) list)
type symbolic_heap             = (symbolic_field_value_list * jsil_logic_expr) LHeap.t
type symbolic_store            = (string, jsil_logic_expr) Hashtbl.t
type pure_formulae             = (jsil_logic_assertion DynArray.t)
type predicate_set             = ((string * (jsil_logic_expr list)) DynArray.t)
type predicate_assertion       = (string * (jsil_logic_expr list))

type symbolic_state = symbolic_heap * symbolic_store * pure_formulae * typing_environment * predicate_set 

(*************************************)
(** Field Value Lists               **)
(*************************************)

let is_empty_fv_list fv_list js =
	let rec loop fv_list empty_so_far =
		match fv_list with
		| [] -> empty_so_far
		| (f_name, f_val) :: rest ->
			if ((f_name = (LLit (String Js2jsil_constants.erFlagPropName))) && js) 
				then true 
				else ( if (f_val = LNone) then loop rest empty_so_far else loop rest false ) in 
	loop fv_list true


let fv_list_substitution fv_list subst partial =
	List.map
		(fun (le_field, le_val) ->
			let s_le_field = JSIL_Logic_Utils.lexpr_substitution le_field subst partial in
			let s_le_val = JSIL_Logic_Utils.lexpr_substitution le_val subst partial in
			(s_le_field, s_le_val))
		fv_list

let selective_fv_list_substitution fv_list subst partial =
	List.map
		(fun (le_field, le_val) ->
			let s_le_val = JSIL_Logic_Utils.lexpr_substitution le_val subst partial in
			(le_field, s_le_val))
		fv_list

(*************************************)
(** Heap functions                  **)
(*************************************)

let heap_init () = 
	LHeap.create 1021

let heap_get (heap : symbolic_heap) (loc : string) =
	try Some (LHeap.find heap loc) with _ -> None

let heap_put (heap : symbolic_heap) (loc : string) (fv_list : symbolic_field_value_list) (def : jsil_logic_expr) =
	LHeap.replace heap loc (fv_list, def)   

let heap_put_fv_pair (heap : symbolic_heap) (loc : string) (field : jsil_logic_expr) (value : jsil_logic_expr) = 
	let fv_list, def_val = try LHeap.find heap loc with _ -> ([], LUnknown) in  
	LHeap.replace heap loc (((field, value) :: fv_list), def_val)

let heap_remove (heap : symbolic_heap) (loc : string) =
	LHeap.remove heap loc  

let heap_domain (heap : symbolic_heap) subst =
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

let heap_copy heap = LHeap.copy heap 

let heap_substitution (heap : symbolic_heap) (subst : substitution) (partial : bool) =
	let new_heap = LHeap.create 1021 in
	LHeap.iter
		(fun loc (fv_list, def) ->
			let s_loc =
				(try Hashtbl.find subst loc
					with _ ->
						if (is_abs_loc_name loc)
							then
								(if (partial) then (ALoc loc) else
									(let new_aloc = ALoc (fresh_aloc ()) in
									JSIL_Logic_Utils.extend_subst subst loc new_aloc;
									new_aloc))
							else (LLit (Loc loc))) in
			let s_loc =
				(match s_loc with
					| LLit (Loc loc) -> loc
					| ALoc loc -> loc
					| _ ->
						raise (Failure (Printf.sprintf "Heap substitution failed miserably: %s" (JSIL_Print.string_of_logic_expression s_loc false)))) in
			let s_fv_list = fv_list_substitution fv_list subst partial in
			let s_def = JSIL_Logic_Utils.lexpr_substitution def subst partial in
			LHeap.add new_heap s_loc (s_fv_list, s_def))
		heap;
	new_heap

let heap_substitution_in_place (heap : symbolic_heap) (subst : substitution) =
  LHeap.iter
  	(fun loc (fv_list, def) ->
  		let s_loc =
  			(try Hashtbl.find subst loc
  				with _ ->
  					if (is_abs_loc_name loc)
  						then ALoc loc
  						else (LLit (Loc loc))) in
  		let s_loc =
  			(match s_loc with
  				| LLit (Loc loc) -> loc
  				| ALoc loc -> loc
  				| _ ->
  					raise (Failure "Heap substitution failed miserably!!!")) in
  		let s_fv_list = fv_list_substitution fv_list subst true in
  		let s_def = JSIL_Logic_Utils.lexpr_substitution def subst true in
  		LHeap.replace heap s_loc (s_fv_list, s_def))
  	heap
		
let selective_heap_substitution_in_place (heap : symbolic_heap) (subst : substitution) =
  LHeap.iter
  	(fun loc (fv_list, def) ->
  		let s_loc =
  			(try Hashtbl.find subst loc
  				with _ ->
  					if (is_abs_loc_name loc)
  						then ALoc loc
  						else (LLit (Loc loc))) in
  		let s_loc =
  			(match s_loc with
  				| LLit (Loc loc) -> loc
  				| ALoc loc -> loc
  				| _ ->
  					raise (Failure "Heap substitution failed miserably!!!")) in
  		let s_fv_list = selective_fv_list_substitution fv_list subst true in
  		let s_def = JSIL_Logic_Utils.lexpr_substitution def subst true in
  		LHeap.replace heap s_loc (s_fv_list, s_def))
  	heap

let heap_vars catch_pvars heap : SS.t =
	LHeap.fold
		(fun _ (fv_list, e_def) ac ->
			let v_fv = List.fold_left
				(fun ac (e_field, e_val) ->
					let v_f = JSIL_Logic_Utils.get_expr_vars catch_pvars e_field in
					let v_v = JSIL_Logic_Utils.get_expr_vars catch_pvars e_val in
						SS.union ac (SS.union v_f v_v))
				SS.empty fv_list in
			let v_def = JSIL_Logic_Utils.get_expr_vars catch_pvars e_def in
			SS.union ac (SS.union v_fv v_def))
		heap SS.empty

let heap_as_list (heap : symbolic_heap) = 
	LHeap.fold 
		(fun loc (fv_list, def) heap_as_list -> 
			((loc, (fv_list, def)) :: heap_as_list))
		heap
		[]
		
let heap_iterator (heap: symbolic_heap) (f : string -> (symbolic_field_value_list * jsil_logic_expr) -> unit) = 
	LHeap.iter f heap

let is_heap_empty (heap : symbolic_heap) (js : bool) : bool =
	LHeap.fold
		(fun loc (fv_list, def) ac -> if (not ac) then ac else is_empty_fv_list fv_list js)
		heap
		true



	
(*************************************)
(** Abstract Store functions        **)
(*************************************)

let store_init vars les =
	let store = Hashtbl.create 31 in

	let rec loop vars les =
		match vars, les with
		| [], _ -> ()
		| var :: rest_vars, le :: rest_les ->
				Hashtbl.replace store var le; loop rest_vars rest_les
		| var :: rest_vars, [] ->
				Hashtbl.replace store var (LLit Undefined); loop rest_vars [] in

	loop vars les;
	store

let store_get_safe store x =
	try
		Some (Hashtbl.find store x)
	with Not_found -> None

let store_get store var =
	(try
		Hashtbl.find store var
	with _ ->
		let msg = Printf.sprintf "store_get_var: fatal error. var: %s" var in
		raise (Failure msg))

let store_put store x ne =
	Hashtbl.replace store x ne

let store_remove store x = 
	Hashtbl.remove store x 

let store_domain store =
	Hashtbl.fold
		(fun x _ ac -> x :: ac)
		store
		[]

let store_copy store =
	let new_store = Hashtbl.copy store in
	new_store

(** why are the types being treated here? **)
let store_substitution store gamma subst partial =
	let vars, les =
		Hashtbl.fold
			(fun pvar le (vars, les) ->
				let s_le = JSIL_Logic_Utils.lexpr_substitution le subst partial in
				let s_le_type, is_typable, _ = JSIL_Logic_Utils.type_lexpr gamma s_le in
				(match s_le_type with
					| Some s_le_type -> Hashtbl.replace gamma pvar s_le_type
					| None -> ());
				(pvar :: vars), (s_le :: les))
			store
			([], []) in
	let store = store_init vars les in
	store

let store_substitution_in_place store gamma subst =
	Hashtbl.iter
		(fun pvar le ->
			let s_le = JSIL_Logic_Utils.lexpr_substitution le subst true in
			Hashtbl.replace store pvar s_le;
			
			let s_le_type, is_typable, _ = JSIL_Logic_Utils.type_lexpr gamma s_le in
			(match s_le_type with
				| Some s_le_type -> Hashtbl.replace gamma pvar s_le_type
				| None -> ()))
		store

let store_vars catch_pvars store =
	Hashtbl.fold (fun _ e ac -> 
		let v_e = JSIL_Logic_Utils.get_expr_vars catch_pvars e in
		SS.union ac v_e) store SS.empty

let store_merge_left (store_l : symbolic_store) (store_r : symbolic_store) =
	Hashtbl.iter
		(fun var expr ->
			if (not (Hashtbl.mem store_l var))
				then Hashtbl.add store_l var expr)
		store_r

let store_filter store filter_fun =
	Hashtbl.fold
		(fun var le (filtered_vars, unfiltered_vars) ->
			if (filter_fun le)
				then ((var :: filtered_vars), unfiltered_vars)
				else (filtered_vars, (var :: unfiltered_vars)))
		store
		([], [])

let store_projection store vars =
	let vars, les = 
		List.fold_left 
			(fun (vars, les) v ->
				if (Hashtbl.mem store v) 
					then (v :: vars), ((Hashtbl.find store v) :: les) 
					else vars, les)
			([], []) 
			vars in
	store_init vars les


(*************************************)
(** Pure Formulae functions         **)
(*************************************)

let pfs_to_list (pfs : pure_formulae) =
	DynArray.to_list pfs

let pfs_of_list (pfs : jsil_logic_assertion list) =
	DynArray.of_list pfs

let add_pure_assertion (pfs : pure_formulae) (a : jsil_logic_assertion) = 
	DynArray.add pfs a
	
let copy_p_formulae pfs =
	let new_pfs = DynArray.copy pfs in
	new_pfs

(* let extend_pfs pfs solver pfs_to_add =
	print_time_debug "extend_pfs:";
	(match solver with
	 | None -> ()
	 | Some solver -> solver := None);
	DynArray.append (DynArray.of_list pfs_to_add) pfs *)

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

let merge_pfs pfs_l pfs_r =
	DynArray.append pfs_r pfs_l

let pf_substitution pf_r subst partial =
	let new_pf = DynArray.create () in
	let len = (DynArray.length pf_r) - 1 in
	for i=0 to len do
		let a = DynArray.get pf_r i in
		let s_a = JSIL_Logic_Utils.assertion_substitution a subst partial in
		DynArray.add new_pf s_a
	done;
	new_pf

let pf_substitution_in_place pfs subst =
	DynArray.iteri (fun i a ->
		let s_a = JSIL_Logic_Utils.assertion_substitution a subst true in
		DynArray.set pfs i s_a) pfs

let get_pf_vars catch_pvars pfs =
	DynArray.fold_left (fun ac a ->
		let v_a = JSIL_Logic_Utils.get_assertion_vars catch_pvars a in
		SS.union ac v_a) SS.empty pfs


(*************************************)
(** Predicate Set functions         **)
(*************************************)
let copy_pred_set preds =
	let new_preds = DynArray.copy preds in
	new_preds

let pred_substitution pred subst partial =
	let pred_name, les = pred in
	let s_les = List.map (fun le -> JSIL_Logic_Utils.lexpr_substitution le subst partial)  les in
	(pred_name, s_les)

let preds_substitution preds subst partial =
	let len = DynArray.length preds in
	let new_preds = DynArray.create () in
	for i=0 to len - 1 do
		let pred = DynArray.get preds i in
		let s_pred = pred_substitution pred subst partial in
		DynArray.add new_preds s_pred
	done;
	new_preds

let preds_substitution_in_place preds subst =
	DynArray.iteri (fun i pred ->
		let s_pred = pred_substitution pred subst true in
		DynArray.set preds i s_pred) preds

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

let find_predicate_assertion preds pred_name =
	let len = DynArray.length preds in
	let rec loop preds args =
		match preds with
		| [] -> args
		| cur_pred :: rest_preds ->
			let cur_pred_name, cur_pred_args = cur_pred in
			if (cur_pred_name = pred_name)
				then loop rest_preds (cur_pred_args :: args)
				else loop rest_preds args  in
	loop (DynArray.to_list preds) []

let is_preds_empty preds =
	(DynArray.length preds) = 0
	

let simple_subtract_pred preds pred_name = 
	let pred_asses = DynArray.to_list preds in 
	let rec loop pred_asses cur = 
		(match pred_asses with 
		| [] -> None
		| (cur_pred_name, les) :: rest -> 
			if (cur_pred_name = pred_name) 
			then Some (cur, les)
			else loop rest (cur + 1)) in 
	match (loop pred_asses 0) with 
	| None -> None
	| Some (cur, les) -> (DynArray.delete preds cur); Some (pred_name, les)
		
let get_preds_vars catch_pvars preds : SS.t =
	DynArray.fold_left (fun ac (_, les) ->
		let v_les = List.fold_left (fun ac e ->
			let v_e = JSIL_Logic_Utils.get_expr_vars catch_pvars e in
			SS.union ac v_e) SS.empty les in
		SS.union ac v_les) SS.empty preds


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

let init_symb_state () : symbolic_state =
	(* Heap, Store, Pure Formula, Gamma, Preds *)
	(LHeap.create 1, Hashtbl.create 1, DynArray.create (), Hashtbl.create 1, DynArray.create ())

let copy_symb_state symb_state =
	let heap, store, p_formulae, gamma, preds (*, solver*) = symb_state in
	let c_heap      = LHeap.copy heap in
	let c_store     = store_copy store in
	let c_pformulae = copy_p_formulae p_formulae in
	let c_gamma     = copy_gamma gamma in
	let c_preds     = copy_pred_set preds in
	(* (match !solver with
	| Some (solver, _) -> Z3.Solver.reset solver
	| None -> ()); *)
	(c_heap, c_store, c_pformulae, c_gamma, c_preds (*, ref None *))

let rec extend_symb_state_with_pfs symb_state pfs_to_add =
	merge_pfs (get_pf symb_state) pfs_to_add

let symb_state_add_subst_as_equalities new_symb_state subst pfs spec_vars =
	Hashtbl.iter
		(fun var le ->
			match le with
			| LLit _
			| ALoc _ ->
				if (List.mem var spec_vars)
					then DynArray.add pfs (LEq (LVar var, le))
					else ()
			| _ -> DynArray.add pfs (LEq (LVar var, le)))
		subst

(* 
let is_empty_symb_state symb_state =
	(is_symb_heap_empty (get_heap symb_state)) && (is_preds_empty (get_preds symb_state)) *)


let symb_state_replace_store symb_state new_store =
	let heap, _, pfs, gamma, preds (*, solver *) = symb_state in
	(heap, new_store, pfs, gamma, preds (*, solver *))

let symb_state_replace_heap symb_state new_heap =
	let _, store, pfs, gamma, preds (*, solver *) = symb_state in
	(new_heap, store, pfs, gamma, preds (*, solver *))

let symb_state_replace_preds symb_state new_preds =
	let heap, store, pfs, gamma, _ (*, solver *) = symb_state in
	(heap, store, pfs, gamma, new_preds (*, solver *))

let symb_state_replace_gamma symb_state new_gamma =
	let heap, store, pfs, _, preds (*, solver *) = symb_state in
	(heap, store, pfs, new_gamma, preds (*, solver *))

let symb_state_replace_pfs symb_state new_pfs =
	let heap, store, _, gamma, preds (*, solver *) = symb_state in
	(heap, store, new_pfs, gamma, preds (*, solver *))

let remove_concrete_values_from_the_store symb_state = 
	Hashtbl.filter_map_inplace (fun x le -> 
		match le with 
		| LLit lit ->
			let new_l_var = fresh_lvar () in
			add_pure_assertion (get_pf symb_state) (LEq (LVar new_l_var, le));
			Some (LVar new_l_var)
		| _ -> 
			Some le) (get_store symb_state)

let symb_state_substitution (symb_state : symbolic_state) subst partial =
	let heap, store, pf, gamma, preds (*, _ *) = symb_state in
	let s_heap = heap_substitution heap subst partial in
	let s_store = store_substitution store gamma subst partial in
	let s_pf = pf_substitution pf subst partial  in
	let s_gamma = gamma_substitution gamma subst partial in
	let s_preds = preds_substitution preds subst partial in
	(s_heap, s_store, s_pf, s_gamma, s_preds (* ref None *))

let symb_state_substitution_in_place_no_gamma (symb_state : symbolic_state) subst =
	let heap, store, pf, gamma, preds = symb_state in
		heap_substitution_in_place heap subst;
		store_substitution store gamma subst; 
		pf_substitution_in_place pf subst;
		preds_substitution_in_place preds subst

let selective_symb_state_substitution_in_place_no_gamma (symb_state : symbolic_state) subst =
	let heap, store, pf, gamma, preds = symb_state in
		pf_substitution_in_place pf subst;
		store_substitution store gamma subst; 
		preds_substitution_in_place preds subst;
		selective_heap_substitution_in_place heap subst

let get_symb_state_vars catch_pvars symb_state =
	let heap, store, pfs, gamma, preds = symb_state in
	let v_h  : SS.t = heap_vars catch_pvars heap in
	let v_s  : SS.t = store_vars catch_pvars store in
	let v_pf : SS.t = get_pf_vars catch_pvars pfs in
	let v_g  : SS.t = get_gamma_vars catch_pvars gamma in
	let v_pr : SS.t = get_preds_vars catch_pvars preds in
		SS.union v_h (SS.union v_s (SS.union v_pf (SS.union v_g v_pr)))

let get_symb_state_vars_no_gamma catch_pvars symb_state =
	let heap, store, pfs, gamma, preds = symb_state in
	let v_h  : SS.t = heap_vars catch_pvars heap in
	let v_s  : SS.t = store_vars catch_pvars store in
	let v_pf : SS.t = get_pf_vars catch_pvars pfs in
	let v_pr : SS.t = get_preds_vars catch_pvars preds in
		SS.union v_h (SS.union v_s (SS.union v_pf v_pr))

let extend_abs_store x store gamma =
	let new_l_var_name = fresh_lvar () in
	let new_l_var = LVar new_l_var_name in
	(try
		let x_type = Hashtbl.find gamma x in
		Hashtbl.add gamma new_l_var_name x_type
	with _ -> ());
	Hashtbl.add store x new_l_var;
	new_l_var

let check_store store gamma =

	let placeholder pvar le target_type =
		if (Hashtbl.mem gamma pvar) then
		begin
		  let _type = Hashtbl.find gamma pvar in
		  	(target_type = _type)
		end
		else
		begin
		   Hashtbl.add gamma pvar target_type;
		   true
		end in

	Hashtbl.fold
		(fun pvar le ac -> ac &&
			(match le with
			 | LNone -> placeholder pvar le NoneType
			 | ALoc _ -> placeholder pvar le ObjectType
			 | LLit lit -> placeholder pvar le (evaluate_type_of lit)
			 | _ -> true
			)
		) store true


(****************************************)
(** Normalised Specifications          **)
(****************************************)
type jsil_n_single_spec = {
	n_pre         : symbolic_state;
	n_post        : symbolic_state list;
	n_ret_flag    : jsil_return_flag;
	n_lvars       : SS.t;
	n_post_lvars  : SS.t list;
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
