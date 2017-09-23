open JSIL_Syntax
open JSIL_Logic_Utils
open Z3

(* Symbolic State Error                                *)
exception Symb_state_error of string;;

(*************************************)
(** Symbolic States                 **)
(*************************************)

type symbolic_field_value_list = ((jsil_logic_expr * jsil_logic_expr) list)
type symbolic_discharge_list   = ((jsil_logic_expr * jsil_logic_expr) list)
type symbolic_heap             = (symbolic_field_value_list * (jsil_logic_expr option)) LHeap.t
type symbolic_store            = (string, jsil_logic_expr) Hashtbl.t
type pure_formulae             = jsil_logic_assertion DynArray.t
type predicate_set             = ((string * (jsil_logic_expr list)) DynArray.t)
type predicate_assertion       = (string * (jsil_logic_expr list))

type symbolic_state       = symbolic_heap * symbolic_store * pure_formulae * typing_environment * predicate_set
type symbolic_state_frame = symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * typing_environment 
type discharge_list       = ((jsil_logic_expr * jsil_logic_expr) list)

(*************************************)
(** Cached symbolic state           **)
(*************************************)

type cached_symbolic_state =
	  (string * ((jsil_logic_expr * jsil_logic_expr) list * jsil_logic_expr option)) list
	* (string * jsil_logic_expr) list
	* jsil_logic_assertion list
	* (string * jsil_type) list
	* (string * jsil_logic_expr list) list

let cache_ss (ss : symbolic_state) : cached_symbolic_state =
	let sort = List.sort compare in
	let heap, store, pfs, gamma, preds = ss in
	let lheap = lheap_to_list heap in
	let lstore = hash_to_list store in
	let lpfs   = List.sort compare (DynArray.to_list pfs) in
	let lgamma = hash_to_list gamma in
	let lpreds = List.sort compare (DynArray.to_list preds) in
	lheap, lstore, lpfs, lgamma, lpreds

let uncache_ss (css : cached_symbolic_state) : symbolic_state =
	let start_time = Sys.time() in
	let lheap, lstore, lpfs, lgamma, lpreds = css in
	let heap = lheap_of_list lheap in
	let store = hash_of_list lstore in
	let pfs   = DynArray.of_list lpfs in
	let gamma = hash_of_list lgamma in
	let preds = DynArray.of_list lpreds in
	let result = (heap, store, pfs, gamma, preds) in
	let end_time = Sys.time() in
	JSIL_Syntax.update_statistics "uncache_ss" (end_time -. start_time);
	result

let ss_cache :
	(SS.t option option * jsil_logic_assertion list * SS.t * cached_symbolic_state,
	 cached_symbolic_state * (string * jsil_logic_expr) list * jsil_logic_assertion list * SS.t) Hashtbl.t = Hashtbl.create 21019

let ss_encache_key vts ots exs ss =
	let start_time = Sys.time() in
	let cots = List.sort compare (DynArray.to_list ots) in
	let css = cache_ss ss in
	let end_time = Sys.time() in
	JSIL_Syntax.update_statistics "simpl_encache_key" (end_time -. start_time);
	vts, cots, exs, css

let ss_encache_value ss subst ots exs =
	let start_time = Sys.time() in
	let css = cache_ss ss in
	let csubst = hash_to_list subst in
	let cots = List.sort compare (DynArray.to_list ots) in
	let end_time = Sys.time() in
	JSIL_Syntax.update_statistics "simpl_encache_value" (end_time -. start_time);
	css, csubst, cots, exs

let ss_uncache_value css csubst cots exs =
	let start_time = Sys.time() in
	let ss = uncache_ss css in
	let subst = hash_of_list csubst in
	let ots = DynArray.of_list cots in
	let end_time = Sys.time() in
	JSIL_Syntax.update_statistics "simpl_uncache_value" (end_time -. start_time);
	ss, subst, ots, exs

(*************************************)
(** Cached pfs state                **)
(*************************************)

let pfs_cache :
	(jsil_logic_assertion list * (string * jsil_type) list * SS.t option option,
	 jsil_logic_assertion list * (string * jsil_type) list) Hashtbl.t = Hashtbl.create 21019

let pfs_cache_key pfs gamma lexs =
	let start_time = Sys.time() in
	let lpfs   = List.sort compare (DynArray.to_list pfs) in
	let lgamma = hash_to_list gamma in
	let result = (lpfs, lgamma, lexs) in
	let end_time = Sys.time() in
	JSIL_Syntax.update_statistics "pfs_cache_key" (end_time -. start_time);
	result

let pfs_cache_value pfs gamma =
	let start_time = Sys.time() in
	let lpfs   = List.sort compare (DynArray.to_list pfs) in
	let lgamma = hash_to_list gamma in
	let result = (lpfs, lgamma) in
	let end_time = Sys.time() in
	JSIL_Syntax.update_statistics "pfs_cache_value" (end_time -. start_time);
	result

let pfs_uncache_value value =
	let start_time = Sys.time() in
	let lpfs, lgamma = value in
	let pfs   = DynArray.of_list lpfs in
	let gamma = hash_of_list lgamma in
	let result = (pfs, gamma) in
	let end_time = Sys.time() in
	JSIL_Syntax.update_statistics "pfs_uncache_value" (end_time -. start_time);
	result

(*************************************)
(** Field Value Lists               **)
(*************************************)

let fv_list_substitution 
		(subst   : substitution) (partial : bool) 
		(fv_list : symbolic_field_value_list) : symbolic_field_value_list =
	let f_subst = lexpr_substitution subst partial in 
	List.map (fun (le_field, le_val) -> f_subst le_field, f_subst le_val) fv_list

let selective_fv_list_substitution 
		(subst   : substitution) (partial : bool) 
		(fv_list : symbolic_field_value_list) : symbolic_field_value_list =
	let f_subst = JSIL_Logic_Utils.lexpr_selective_substitution subst partial in 
	List.map (fun (le_field, le_val) -> (le_field, f_subst le_val)) fv_list

(*************************************)
(** Heap functions                  **)
(*************************************)

(** Returns an empty symbolic heap *)
let heap_init () : symbolic_heap =
	LHeap.create big_tbl_size

(** Symbolic heap read heap(loc) *)
let heap_get (heap : symbolic_heap) (loc : string) =
	try Some (LHeap.find heap loc) with _ -> None

(** Symbolic heap put heap(loc) is assigned to fv_list *)
let heap_put (heap : symbolic_heap) (loc : string) (fv_list : symbolic_field_value_list) (dom : jsil_logic_expr option) =
	LHeap.replace heap loc (fv_list, dom)

(** Symbolic heap put heap(loc, field) is assgined to value. 
    The domain remains unchanged *) 
let heap_put_fv_pair (heap : symbolic_heap) (loc : string) (field : jsil_logic_expr) (value : jsil_logic_expr) =
	let fv_list, domain = try LHeap.find heap loc with _ -> ([], None) in
	LHeap.replace heap loc (((field, value) :: fv_list), domain)

(** Removes the fv-list associated with --loc-- in --heap-- *)
let heap_remove (heap : symbolic_heap) (loc : string) =
	LHeap.remove heap loc

(** Removes the domain of --heap-- *)
let heap_domain (heap : symbolic_heap) : SS.t =
	SS.of_list (LHeap.fold (fun l _ ac -> l :: ac) heap [])

(** Returns a copie of --heap-- *)
let heap_copy (heap : symbolic_heap) : symbolic_heap = LHeap.copy heap

(** Returns subst(heap) *)
let heap_substitution (subst : substitution) (partial : bool) (heap : symbolic_heap)  : symbolic_heap =
	let new_heap = LHeap.create 1021 in
	LHeap.iter
		(fun loc (fv_list, domain) ->
			let s_loc = if (is_lit_loc_name loc) then LLit (Loc loc) else (
				try Hashtbl.find subst loc with _ -> 
					if (partial) then (ALoc loc) else (
						let new_aloc = ALoc (fresh_aloc ()) in
						extend_substitution subst [ loc ] [ new_aloc ];
						new_aloc)) in 
			let s_loc = match s_loc with LLit (Loc loc) -> loc | ALoc loc -> loc 
				| _ -> raise (Failure (Printf.sprintf "Heap substitution fail for loc: %s" (JSIL_Print.string_of_logic_expression s_loc))) in 
			let s_fv_list = fv_list_substitution subst partial fv_list in
			let s_domain = Option.map (fun le -> lexpr_substitution subst partial le) domain in
			LHeap.add new_heap s_loc (s_fv_list, s_domain))			
		heap;
	new_heap

(** Modifies --heap-- in place updating it to subst(heap) *)
let heap_substitution_in_place (subst : substitution) (heap : symbolic_heap) : unit =
  LHeap.iter
  	(fun loc (fv_list, domain) ->
  		let s_loc = if (is_lit_loc_name loc) then LLit (Loc loc) else (
			try Hashtbl.find subst loc with _ -> ALoc loc) in 
  		let s_loc = match s_loc with LLit (Loc loc) -> loc | ALoc loc -> loc 
			| _ -> raise (Failure (Printf.sprintf "Heap substitution fail for loc: %s" (JSIL_Print.string_of_logic_expression s_loc))) in 		
  		let s_fv_list = fv_list_substitution subst true fv_list in
  		let s_domain = Option.map (fun le -> JSIL_Logic_Utils.lexpr_substitution subst true le) domain in
  		LHeap.replace heap s_loc (s_fv_list, s_domain))
  	heap

(** Returns the logical variables occuring in --heap-- *)
let heap_lvars (heap : symbolic_heap) : SS.t =
	LHeap.fold
		(fun _ (fv_list, domain) ac ->
			let v_fv = List.fold_left
				(fun ac (e_field, e_val) -> SS.union ac (SS.union (get_lexpr_lvars e_field) (get_lexpr_lvars e_val)))
				SS.empty fv_list in
			let v_domain = Option.map_default (fun domain -> get_lexpr_lvars domain) SS.empty domain in
			SS.union ac (SS.union v_fv v_domain))
		heap SS.empty

(** Returns the abstract locations occuring in --heap-- *)
let heap_alocs (heap : symbolic_heap) : SS.t =
	LHeap.fold
		(fun _ (fv_list, _) ac ->
			let v_fv = List.fold_left
				(fun ac (e_field, e_val) -> SS.union ac (SS.union (get_lexpr_alocs e_field) (get_lexpr_alocs e_val)))
				SS.empty fv_list in
			SS.union ac v_fv)
		heap SS.empty

(** Returns the serialization of --heap-- as a list *)
let heap_to_list (heap : symbolic_heap) : (string * (symbolic_field_value_list * (jsil_logic_expr option))) list =
	LHeap.fold (fun loc obj ac -> ((loc, obj) :: ac)) heap []

(** Calls --f-- on all objects of --heap--; f(loc, (fv_list, dom)) *)
let heap_iterator (heap: symbolic_heap) (f : string -> (symbolic_field_value_list * (jsil_logic_expr option) -> unit)) =
	LHeap.iter f heap

(** Returns true if --heap-- is empty *)
let is_heap_empty (heap : symbolic_heap) : bool =
	LHeap.fold
		(fun loc (fv_list, dom) ac -> if (not ac) then ac else (fv_list = []) && (dom = None))
		heap
		true


(*************************************)
(** Abstract Store functions        **)
(*************************************)

(** Returns a new symbolic store where the variables in vars are 
    mapped to the logical expressions in --les--. 
    When |les| > |vars|, the additional les are ignored. 
    When |les| < |vars|, the vars for which we do not have le are
    set to undefined *)  
let store_init (vars : string list) (les : jsil_logic_expr list) : symbolic_store =
	let store = Hashtbl.create medium_tbl_size in
	let rec loop vars les =
		match vars, les with
		| [], _ -> ()
		| var :: rest_vars, le :: rest_les ->
				Hashtbl.replace store var le; loop rest_vars rest_les
		| var :: rest_vars, [] ->
				Hashtbl.replace store var (LLit Undefined); loop rest_vars [] in
	loop vars les;
	store

(** Returns Some store(x) if defined and None otherwise *)
let store_get_safe (store : symbolic_store) (x : string) : jsil_logic_expr option =
	try
		Some (Hashtbl.find store x)
	with Not_found -> None

(** Returns Some store(x) if defined and throws an error otherwise *)
let store_get (store : symbolic_store) (x : string) : jsil_logic_expr =
	(try
		Hashtbl.find store x
	with _ ->
		let msg = Printf.sprintf "DEATH. store_get_var. var: %s" x in
		raise (Failure msg))

(** Returns Some --x-- for which store(x) = --y-- *)
let store_get_rev (store : symbolic_store) (le : jsil_logic_expr) : string option =
	Hashtbl.fold
		(fun x le' ac -> if (le = le') then Some x else ac)
		store
		None

(** Updates store(x) with --le-- *)
let store_put (store : symbolic_store) (x : string) (le : jsil_logic_expr) : unit =
	Hashtbl.replace store x le

(** Removes the binding of --x-- from --store-- *)
let store_remove (store : symbolic_store) (x : string) : unit =
	Hashtbl.remove store x

(** Removes the domian of --store-- *)
let store_domain (store : symbolic_store) : SS.t =
	SS.of_list (Hashtbl.fold (fun x _ ac -> x :: ac) store [])

(** Returns a copie of --store-- *)
let store_copy (store : symbolic_store) : symbolic_store = Hashtbl.copy store 

(** Returns subst(store) *)
let store_substitution 
		(subst : substitution) (partial : bool) (store : symbolic_store) : symbolic_store =
	let vars, les =
		Hashtbl.fold
			(fun pvar le (vars, les) -> (pvar :: vars), ((lexpr_substitution subst partial le) :: les))
			store
			([], []) in
	let store = store_init vars les in
	store

(** Updates --store-- to subst(store) *)
let store_substitution_in_place (subst : substitution) (store : symbolic_store) : unit =
	Hashtbl.iter
		(fun x le ->
			let s_le = lexpr_substitution subst true le in
			Hashtbl.replace store x s_le)
		store

(** Returns the set containing all the lvars occurring in --store-- *)
let store_lvars (store : symbolic_store) : SS.t =
	Hashtbl.fold (fun _ le ac -> SS.union ac (get_lexpr_lvars le)) store SS.empty

(** Returns the set containing all the alocs occurring in --store-- *)
let store_alocs (store : symbolic_store) : SS.t =
	Hashtbl.fold (fun _ le ac -> SS.union ac (get_lexpr_alocs le)) store SS.empty

(** Extend store_l with store_r *)
let store_merge_left (store_l : symbolic_store) (store_r : symbolic_store) : unit =
	Hashtbl.iter 
		(fun x le -> if (not (Hashtbl.mem store_l x)) then Hashtbl.replace store_l x le)
		store_r

(** Partitions the variables in the domain of --store-- into two groups: 
    - the group containing the variables mapped onto lexprs satisfying --pred--
    - the rest *)
let store_partition (store : symbolic_store) (pred_fun : jsil_logic_expr -> bool) : (string list) * (string list) =
	Hashtbl.fold
		(fun x le (pred_xs, npred_xs) ->
			if (pred_fun le) then ((x :: pred_xs), npred_xs) else (pred_xs, (x :: npred_xs)))
		store
		([], [])

(** Returns the projection of --store-- onto --xs-- *)
let store_projection (store : symbolic_store) (xs : string list) : symbolic_store =
	let xs, les =
		List.fold_left
			(fun (xs, les) x ->
				if (Hashtbl.mem store x)
					then (x :: xs), ((Hashtbl.find store x) :: les)
					else xs, les)
			([], [])
			xs in
	store_init xs les

(** Converts --store-- into a list of assertions *)
let asrts_of_store (store : symbolic_store) : jsil_logic_assertion list =
	Hashtbl.fold (fun x le asrts -> ((LEq (PVar x, le)) :: asrts)) store []

(** Calls --f-- on all variables of --store--; f(x, le_x) *)
let store_iter (store: symbolic_store) (f : string -> jsil_logic_expr -> unit) : unit =
	Hashtbl.iter f store

let store_fold (store: symbolic_store) (f : string -> jsil_logic_expr -> 'a  -> 'a) (init : 'a) : 'a =
	Hashtbl.fold f store init 


(*************************************)
(** Pure Formulae functions         **)
(*************************************)

(** Returns a new (empty) predicate set *)
let pfs_init () : pure_formulae = DynArray.make medium_tbl_size

(** Returns the serialization of --pfs-- as a list *)
let pfs_to_list (pfs : pure_formulae) : jsil_logic_assertion list = DynArray.to_list pfs

(** Returns a pure_formulae array given a list of assertions *)
let pfs_of_list (pfs : jsil_logic_assertion list) : pure_formulae = DynArray.of_list pfs

(** Extends --pfs-- with --a-- *)
let pfs_extend (pfs : pure_formulae) (a : jsil_logic_assertion) : unit = DynArray.add pfs a

(** Returns a copie of --pfs-- *)
let pfs_copy (pfs : pure_formulae) : pure_formulae = DynArray.copy pfs

(** Extend --pfs_l-- with --pfs_r-- *)
let pfs_merge (pfs_l : pure_formulae) (pfs_r : pure_formulae) : unit = DynArray.append pfs_r pfs_l

(** Returns subst(pf) *)
let pfs_substitution (subst : substitution) (partial : bool) (pf : pure_formulae) : pure_formulae =
	let asrts   = pfs_to_list pf in 
	let s_asrts = List.map (asrt_substitution subst partial) asrts in 
	pfs_of_list s_asrts

(** Updates pfs to subst(pfs) *)
let pfs_substitution_in_place (subst : substitution) (pfs : pure_formulae) : unit =
	DynArray.iteri (fun i a ->
		let s_a = JSIL_Logic_Utils.asrt_substitution subst true a in
		DynArray.set pfs i s_a) pfs

(** Returns the set containing all the lvars occurring in --pfs-- *)
let pfs_lvars (pfs : pure_formulae) : SS.t  =
	DynArray.fold_left (fun ac a -> SS.union ac (get_asrt_lvars a)) SS.empty pfs

(** Returns the set containing all the alocs occurring in --pfs-- *)
let pfs_alocs (pfs : pure_formulae) : SS.t =
	DynArray.fold_left (fun ac a -> SS.union ac (get_asrt_alocs a)) SS.empty pfs


(*************************************)
(** Predicate Set functions         **)
(*************************************)

(** Returns a new (empty) predicate set *)
let preds_init () : predicate_set = DynArray.make small_tbl_size

(** Returns the serialization of --preds-- as a list of predicate_assertions *)
let preds_to_list (preds : predicate_set) : predicate_assertion list = DynArray.to_list preds

(** Returns a pred_set given a list of predicate_assertions. *)
let preds_of_list (list_preds : predicate_assertion list) : predicate_set = DynArray.of_list list_preds

(** Returns a copie of --preds-- *)
let preds_copy (preds : predicate_set) : predicate_set = DynArray.copy preds 

(** Returns subst(preds) *)
let preds_substitution (subst : substitution) (partial : bool) (preds : predicate_set) : predicate_set =
	let preds  = preds_to_list preds in 
	let preds' = List.map (fun (s, les) -> (s, List.map (fun le -> lexpr_substitution subst partial le) les)) preds in 
	preds_of_list preds' 

(** Updates --preds-- to subst(preds) *)
let preds_substitution_in_place (subst : substitution) (preds : predicate_set) : unit =
	let pred_substitution subst (s, les) = (s, List.map (fun le -> lexpr_substitution subst true le) les) in 
	DynArray.iteri (fun i pred ->
		let s_pred = pred_substitution subst pred in
		DynArray.set preds i s_pred) preds

(** Extends --preds-- with --pred_asrt-- *)
let preds_extend (preds : predicate_set) (pred_asrt : predicate_assertion) : unit = DynArray.add preds pred_asrt

(** Finds the index of --pred_asrt-- in --preds-- *)
let preds_find_index (preds : predicate_set) (pred_asrt : predicate_assertion) : int option =
	try Some (DynArray.index_of (fun pa -> pa = pred_asrt) preds) with _ -> None 

(** Removes the binding of --pa-- from --preds-- *)
let preds_remove (preds : predicate_set) (pred_asrt : predicate_assertion) : unit =
	match preds_find_index preds pred_asrt with Some i -> DynArray.delete preds i | _ -> () 

(** Removes the i-th predicate of --preds-- *)
let preds_remove_by_index (preds : predicate_set) (i : int) : unit = DynArray.delete preds i  

(** Find predicate_assertion via pred_name. 
    Returns a list with all the predicate assertions whose pred_name is --pred_name-- *)
let find_predicate_assertion_by_name (preds : predicate_set) (pred_name : string) : (jsil_logic_expr list) list =
	let preds_l = preds_to_list preds in 
	let preds_l = List.filter (fun (pn, _) -> pn = pred_name) preds_l in 
	List.map (fun (_, les) -> les) preds_l 

(** Returns true if --preds-- is empty *)
let is_preds_empty (preds : predicate_set) : bool =
	(DynArray.length preds) = 0

(** Removes the first occurrence of a pred_asrt with name --pred_name-- 
    and returns its list of arguments *)
let preds_remove_by_name (preds : predicate_set) (pred_name : string) : (string * jsil_logic_expr list) option =
	try (
		let i              = DynArray.index_of (fun (pname, _) -> pname = pred_name) preds in 
		let pname, les     = DynArray.get preds i in 
		DynArray.delete preds i; 
		Some (pname, les))
	with _ -> None 		 

(** Return the set containing all the lvars occurring in --preds-- *)
let preds_lvars (preds : predicate_set) : SS.t =
	DynArray.fold_left 
		(fun ac (_, les) -> List.fold_left (fun ac le -> SS.union ac (get_lexpr_lvars le)) ac les) 
		SS.empty 
		preds

(** Return the set containing all the alocs occurring in --preds-- *)
let preds_alocs (preds : predicate_set) : SS.t =
	DynArray.fold_left 
		(fun ac (_, les) -> List.fold_left (fun ac le -> SS.union ac (get_lexpr_alocs le)) ac les)
		SS.empty 
		preds

(*************************************)
(** Symbolic State functions        **)
(*************************************)

(** Symbolic state first projection *)
let ss_heap (symb_state : symbolic_state) : symbolic_heap =
	let heap, _, _, _, _ = symb_state in heap

(** Symbolic state second projection *)
let ss_store (symb_state : symbolic_state) : symbolic_store =
	let _, store, _, _, _ = symb_state in store

(** Symbolic state third projection *)
let ss_pfs (symb_state : symbolic_state) : pure_formulae =
	let _, _, pfs, _, _ = symb_state in pfs

(** Symbolic state fourth projection *)
let ss_gamma (symb_state : symbolic_state) : typing_environment =
	let _, _, _, gamma, _ = symb_state in gamma

(** Symbolic state fifth projection *)
let ss_preds (symb_state : symbolic_state) : predicate_set =
	let _, _, _, _, preds = symb_state in preds

let ss_pfs_list (symb_state : symbolic_state) : jsil_logic_assertion list =
	pfs_to_list (ss_pfs symb_state)

let ss_extend_preds (symb_state : symbolic_state) (pred_assertion : predicate_assertion) : unit =
	preds_extend (ss_preds symb_state) pred_assertion

let ss_extend_pfs (symb_state : symbolic_state) (pfs_to_add : pure_formulae) : unit =
	pfs_merge (ss_pfs symb_state) pfs_to_add

(** Replaces the --symb_state-- heap with --heap--   *)
let ss_replace_heap (symb_state : symbolic_state) (heap : symbolic_heap) : symbolic_state =
	let _, store, pfs, gamma, preds  = symb_state in (heap, store, pfs, gamma, preds)

(** Replaces the --symb_state-- store with --store-- *)
let ss_replace_store (symb_state : symbolic_state) (store : symbolic_store) : symbolic_state =
	let heap, _, pfs, gamma, preds   = symb_state in (heap, store, pfs, gamma, preds)

(** Replaces the --symb_state-- pfs with --pfs--     *)
let ss_replace_pfs (symb_state : symbolic_state) (pfs : pure_formulae) : symbolic_state =
	let heap, store, _, gamma, preds = symb_state in (heap, store, pfs, gamma, preds)

(** Replaces the --symb_state-- gamma with --gamma-- *)
let ss_replace_gamma (symb_state : symbolic_state) (gamma : typing_environment) : symbolic_state =
	let heap, store, pfs, _, preds   = symb_state in (heap, store, pfs, gamma, preds)

(** Replaces the --symb_state-- preds with --preds-- *)
let ss_replace_preds (symb_state : symbolic_state) (preds : predicate_set) : symbolic_state =
	let heap, store, pfs, gamma, _   = symb_state in (heap, store, pfs, gamma, preds)

(** Returns a new empty symbolic state *)
let ss_init () : symbolic_state = (heap_init (), (store_init [] []), pfs_init (), gamma_init (), preds_init ())

(** Returns a copy of the symbolic state *)
let ss_copy (symb_state : symbolic_state) : symbolic_state =
	let heap, store, pfs, gamma, preds = symb_state in
	let c_heap   = heap_copy heap in
	let c_store  = store_copy store in
	let c_pfs    = pfs_copy pfs in
	let c_gamma  = gamma_copy gamma in
	let c_preds  = preds_copy preds in
	(c_heap, c_store, c_pfs, c_gamma, c_preds)

(** Returns subst(symb_state) *)
let ss_substitution 
		(subst : substitution) (partial : bool) (symb_state : symbolic_state) : symbolic_state =
	let heap, store, pf, gamma, preds = symb_state in
	let s_heap  = heap_substitution subst partial heap in
	let s_store = store_substitution subst partial store in
	let s_pf    = pfs_substitution subst partial pf in
	let s_gamma = gamma_substitution gamma subst partial in
	let s_preds = preds_substitution subst partial preds in
	(s_heap, s_store, s_pf, s_gamma, s_preds)

let ss_substitution_in_place_no_gamma
		(subst : substitution) (symb_state : symbolic_state) : unit =
	let heap, store, pfs, gamma, preds = symb_state in
	heap_substitution_in_place  subst heap;		
	store_substitution_in_place subst store;
	pfs_substitution_in_place   subst pfs;	
	preds_substitution_in_place subst preds

(** Return the set containing all the lvars occurring in --symb_state-- *)
let ss_lvars (symb_state : symbolic_state) : SS.t =
	let heap, store, pfs, gamma, preds = symb_state in
	let v_h  : SS.t = heap_lvars heap in
	let v_s  : SS.t = store_lvars store in
	let v_pf : SS.t = pfs_lvars pfs in
	let v_g  : SS.t = gamma_lvars gamma in
	let v_pr : SS.t = preds_lvars preds in
		SS.union v_h (SS.union v_s (SS.union v_pf (SS.union v_g v_pr)))

(** Return the set containing all the lvars occurring in --symb_state-- 
    except for those that only appear in the gamma + all the program 
    variables in the store *)
let ss_vars_no_gamma (symb_state : symbolic_state) : SS.t =
	let heap, store, pfs, gamma, preds = symb_state in
	let v_h  = heap_lvars heap in
	let v_s  = store_lvars store in
	let v_sp = store_domain store in 
	let v_pf = pfs_lvars pfs in
	let v_pr = preds_lvars preds in
		SS.union v_h (SS.union v_s (SS.union v_sp (SS.union v_pf v_pr)))




(****************************************)
(** TO REFACTOR                        **)
(****************************************)

let selective_heap_substitution_in_place (subst : substitution) (heap : symbolic_heap) =
  LHeap.iter
  	(fun loc (fv_list, domain) ->
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
  		let s_fv_list = selective_fv_list_substitution subst true fv_list in
  		let s_domain = Option.map (fun le -> JSIL_Logic_Utils.lexpr_substitution subst true le) domain in
  		LHeap.replace heap s_loc (s_fv_list, s_domain))
  	heap

let selective_symb_state_substitution_in_place_no_gamma 
		(subst : substitution) (symb_state : symbolic_state) : unit =
	let lexpr_subst = JSIL_Logic_Utils.lexpr_selective_substitution in
	let heap, store, pfs, gamma, preds = symb_state in
	store_substitution_in_place          subst store;
	preds_substitution_in_place          subst preds;
	pfs_substitution_in_place            subst pfs;
	selective_heap_substitution_in_place subst heap 


(****************************************)
(** Normalised Specifications          **)
(****************************************)
type jsil_n_single_spec = {
	n_pre              : symbolic_state;
	n_post             : symbolic_state list;
	n_ret_flag         : jsil_return_flag;
	n_lvars            : SS.t; 
	n_subst            : substitution; 
	n_unification_plan : jsil_logic_assertion list; 
}

type jsil_n_spec = {
	n_spec_name   : string;
  	n_spec_params : jsil_var list;
	n_proc_specs  : jsil_n_single_spec list
}

type specification_table = (string, jsil_n_spec) Hashtbl.t
type lemma_table         = (string, jsil_lemma) Hashtbl.t
type pruning_table       = (string, (bool array) list) Hashtbl.t
type which_predecessor   = (string * int * int, int) Hashtbl.t

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
	n_pred_name             : string;
	n_pred_num_params       : int;
	n_pred_params           : jsil_logic_var list;
	n_pred_definitions      : ((string option) * symbolic_state * (jsil_logic_assertion list)) list;
	n_pred_is_rec           : bool; 
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
	lemma_tbl   : lemma_table;
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
	vis_tbl    		    : (int, int) Hashtbl.t;
	cur_node_info       : search_info_node;
	info_nodes 		    : (int, search_info_node) Hashtbl.t;
	info_edges          : (int, int list) Hashtbl.t;
	next_node           : int ref;
	post_pruning_info   : pruning_table; 
	spec_number         : int;
	pred_info           : (string, int Stack.t) Hashtbl.t
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
				spec_number         = spec_number;
				pred_info           = Hashtbl.create small_tbl_size;
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


let reset_vis_tbl (search_info : symbolic_execution_search_info) : symbolic_execution_search_info = 
	{ search_info with vis_tbl = Hashtbl.create small_tbl_size }

let activate_post_in_post_pruning_info symb_exe_info proc_name post_number =
	try
		let post_pruning_info_array_list =
			Hashtbl.find (symb_exe_info.post_pruning_info) proc_name in
		let post_pruning_info_array = List.nth post_pruning_info_array_list (symb_exe_info.spec_number) in
		post_pruning_info_array.(post_number) <- true
	with Not_found -> ()


let get_pred_index_from_search_info 
		(search_info : symbolic_execution_search_info) 
		(pred_name   : string) : symbolic_execution_search_info * int =
	
	let pred_info = search_info.pred_info in
	(match Hashtbl.mem pred_info pred_name with
	| false -> search_info, -1
	| true ->
		let s = Hashtbl.find pred_info pred_name in
		(match Stack.is_empty s with
		| true -> search_info, -1
		| false ->
			let pred_info = Hashtbl.copy pred_info in
			let s         = Stack.copy s in
			let cmf       = Stack.pop s in
			Hashtbl.replace pred_info pred_name s;
			{ search_info with pred_info = pred_info }, cmf)) 

let add_pred_def_index_to_search_info 
		(search_info    : symbolic_execution_search_info) 
		(pred_name      : string)
		(pred_def_index : int) : symbolic_execution_search_info = 

	let s = Hashtbl.copy search_info.pred_info in
	(* Add the queue to table if necessary *)
	(match (Hashtbl.mem s pred_name) with
		| true -> ()
		| false ->
			print_debug (Printf.sprintf "Adding %s to the predicate unfolding cache, definition %d." pred_name pred_def_index);
			Hashtbl.add s pred_name (Stack.create()));
	
	(* Add definition to stack *)
	let stack = Stack.copy (Hashtbl.find s pred_name) in
	Stack.push pred_def_index stack;
	Hashtbl.replace s pred_name stack;
	let stack_str = Stack.fold (fun ac e -> ac ^ (Printf.sprintf "%d " e)) "" stack in
	print_debug (Printf.sprintf "Current stack for predicate %s: %s" pred_name stack_str);
	{ search_info with pred_info = s } 


let mark_node_as_visited (search_info : symbolic_execution_search_info) (i : int) : unit =
	let cur_node_info = search_info.cur_node_info in
	Hashtbl.replace search_info.vis_tbl i cur_node_info.node_number 

 let check_if_visited (search_info : symbolic_execution_search_info) (i : int) : bool = 
 	Hashtbl.mem search_info.vis_tbl i


let compute_verification_statistics 
	(pruning_info     : pruning_table) 
	(procs_to_verify  : string list) 
	(spec_table       : specification_table) : int * int  = 

	Hashtbl.fold
		(fun proc_name spec (count_prunings, count_verified) ->
			let should_we_verify = (List.mem proc_name procs_to_verify) in
			if (should_we_verify) then (
				let pruning_info_list = Hashtbl.find pruning_info proc_name in
				List.fold_left 
					(fun (count_prunings, count_verified) arr -> 
						Array.fold_left 
							(fun (count_prunings, count_verified) b -> if b then (count_prunings, (count_verified + 1)) else ((count_prunings + 1),  count_verified))
							(count_prunings, count_verified)
							arr)
					(count_prunings, count_verified)
					pruning_info_list
			) else (
				(count_prunings, count_verified)
			))
		spec_table
		(0, 0)
	


(* Hierarchy of failures *)

type unify_stores_fail =
	| VariableNotInStore of string
	| ValueMismatch of string * jsil_logic_expr * jsil_logic_expr
	| NoSubstitution

type unify_heaps_fail =
	| CannotResolvePatLocation of string
	| CannotResolveLocation of string
	| CannotResolveField of string * jsil_logic_expr
	| FieldValueMismatch of string * jsil_logic_expr * jsil_logic_expr * string * jsil_logic_expr * jsil_logic_expr
	| ValuesNotNone of string * (jsil_logic_expr * jsil_logic_expr) list
	| FloatingLocations of string list
	| IllegalDefaultValue of jsil_logic_expr
	| PatternHeapWithDefaultValue
	| GeneralHeapUnificationFailure

type unify_gamma_fail =
	| NoTypeForVariable of string
	| VariableNotInSubstitution of string
	| TypeMismatch of string * jsil_type * jsil_logic_expr * jsil_type

type unify_symb_states_fail =
	| CannotDischargeSpecVars
	| CannotUnifyPredicates
	| ContradictionInPFS

type fully_unify_symb_states_fail =
	| ResourcesRemain
	| CannotUnifySymbStates

type unify_symb_states_fold_fail =
	| CannotSubtractPredicate of string
	| CannotUnifyPredicates

type symb_exec_fail =
	| US  of unify_stores_fail
	| UH  of unify_heaps_fail
	| UG  of unify_gamma_fail
	| USS of unify_symb_states_fail
	| FSS of fully_unify_symb_states_fail
	| USF of unify_symb_states_fold_fail
	| Impossible of string

exception SymbExecFailure of symb_exec_fail

(* Hierarchy of recoveries *)

type unify_gamma_recovery =
	| Flash of string * (jsil_logic_expr list)

type recovery =
	| GR of unify_gamma_recovery
	| NoRecovery

exception SymbExecRecovery of recovery
