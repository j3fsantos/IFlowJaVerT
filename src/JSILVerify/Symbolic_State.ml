open CCommon
open SCommon
open JSIL_Syntax
open JSIL_Logic_Utils
open Z3

(*************************************)
(** Types                           **)
(*************************************)

(** The rest is as-is *)
type predicate_set             = ((string * (jsil_logic_expr list)) DynArray.t)
type predicate_assertion       = (string * (jsil_logic_expr list))

(**
	Symbolic discharge list: a list of the form
		symbolic expression * symbolic expression,
*)
type symbolic_discharge_list   = ((jsil_logic_expr * jsil_logic_expr) list)

type symbolic_state       = SHeap.t * SStore.t * PFS.t * TypEnv.t * predicate_set
type symbolic_state_frame = SHeap.t * predicate_set * substitution * (jsil_logic_assertion list) * TypEnv.t 
type discharge_list       = ((jsil_logic_expr * jsil_logic_expr) list)

(* For each assertion, we have [None] if it's not a predicate; if it is one,  *)
(* [Some true] if we should try to unify the predicate as it is, and          *)
(* [Some false] if we have to unfold it before unifying.                      *)
type unification_plan = (jsil_logic_assertion * bool option) list

let head_unification_plan = function
	| [] -> raise (Failure "DEATH head_unification_plan: empty unification plan")
	| (asrt, _) :: _ -> asrt

type jsil_n_single_spec = {
	n_pre              : symbolic_state;
	n_post             : symbolic_state list;
	n_ret_flag         : jsil_return_flag;
	n_lvars            : SS.t; 
	n_subst            : substitution; 
	n_unification_plan : unification_plan; 
}

type jsil_n_spec = {
	n_spec_name   : string;
  	n_spec_params : jsil_var list;
	n_proc_specs  : jsil_n_single_spec list
}

type n_jsil_logic_predicate = {
	n_pred_name             : string;
	n_pred_num_params       : int;
	n_pred_params           : jsil_logic_var list;
	n_pred_ins              : int list;
	n_pred_definitions      : ((string option) * symbolic_state * unification_plan) list;
	n_pred_is_rec           : bool; 
  n_pred_is_pure          : bool;
}

type specification_table = (string, jsil_n_spec) Hashtbl.t

(** {b Pruning table}. A table mapping each spec_name to a list of 
arrays - one per possible precondition. Each precondtion is associated 
with an array of booleans, one per postcondition, denoting whether or 
not that postcondition is reachable from the precondition.
For instance, suppose:
 pruning_table ("foo") = [ [| false, true |], [| true, true |] ] 
Then the procedure foo has two pre-conditions, each with two 
possible postconditions. The first postcondtion associated with 
the first precondition is unreachable and therefore needs to be 
eliminated. *)
type pruning_table       = (string, (bool array) list) Hashtbl.t

type symb_jsil_program = {
	program    	: jsil_program;
	spec_tbl   	: specification_table;
	lemma_tbl   : lemma_table;
	which_pred 	: (string * int * int, int) Hashtbl.t;
	pred_defs  	: (string, n_jsil_logic_predicate) Hashtbl.t
}

(*********************************************************)
(** Lemma Dependency Graph **)
(** Used for detecting cyclic dependencies **)
(*********************************************************)
type lemma_depd_graph = {
  lemma_depd_names_ids       : (string, int) Hashtbl.t; (* mapping lemma names to node id's *)
  lemma_depd_ids_names       : (int, string) Hashtbl.t; (* and the reverse.. *)
  lemma_depd_edges           : (int, int list) Hashtbl.t; (* lemma_depd_edges.find(x) = list of all dependencies of x *)
}

type symb_graph_node_type = 
	| SGCmdNode    of jsil_cmd * int
	| SGLCmdNode   of jsil_logic_command
	| SGPreNode 
	| SGPostNode 
	| SGErrorNode  of string 

type symb_graph_node = {
	symb_state  : symbolic_state option; 
	(* cmd index *)
	node_type   : symb_graph_node_type; 
	node_number : int 
}

type symbolic_graph = { 
	root                : symb_graph_node; 
	info_nodes 		    : (int, symb_graph_node) Hashtbl.t;
	info_edges          : (int, int list) Hashtbl.t;
}

type symbolic_execution_context = {
	vis_tbl    		    : (int, int) Hashtbl.t;
	cur_node_info       : symb_graph_node;
	symb_graph          : symbolic_graph; 
	next_node           : int ref;
	post_pruning_info   : pruning_table; 
	spec_number         : int;
	proc_name           : string; 
	pred_info           : (string, int Stack.t) Hashtbl.t
}

(*************************************)
(** Pure Formulae functions         **)
(*************************************)

let pfs_mem (pfs : PFS.t) (a : jsil_logic_assertion) : bool = 
	Array.mem a (DynArray.to_array pfs)

(** Extends --pfs-- with --a-- *)
let pfs_extend (pfs : PFS.t) (a : jsil_logic_assertion) : unit = DynArray.add pfs a

(** Returns a copie of --pfs-- *)
let pfs_copy (pfs : PFS.t) : PFS.t = DynArray.copy pfs

(** Extend --pfs_l-- with --pfs_r-- *)
let pfs_merge (pfs_l : PFS.t) (pfs_r : PFS.t) : unit = DynArray.append pfs_r pfs_l

(** Returns subst(pf) *)
let pfs_substitution (subst : substitution) (partial : bool) (pf : PFS.t) : PFS.t =
	let asrts   = PFS.to_list pf in 
	let s_asrts = List.map (asrt_substitution subst partial) asrts in 
	PFS.of_list s_asrts

(** Updates pfs to subst(pfs) *)
let pfs_substitution_in_place (subst : substitution) (pfs : PFS.t) : unit =
	DynArray.iteri (fun i a ->
		let s_a = JSIL_Logic_Utils.asrt_substitution subst true a in
		DynArray.set pfs i s_a) pfs

(** Returns the set containing all the lvars occurring in --pfs-- *)
let pfs_lvars (pfs : PFS.t) : SS.t  =
	DynArray.fold_left (fun ac a -> SS.union ac (get_asrt_lvars a)) SS.empty pfs

(** Returns the set containing all the alocs occurring in --pfs-- *)
let pfs_alocs (pfs : PFS.t) : SS.t =
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

(** Return the set containing all the alocs occurring in --preds-- *)
let preds_clocs (preds : predicate_set) : SS.t =
	DynArray.fold_left 
		(fun ac (_, les) -> List.fold_left (fun ac le -> SS.union ac (get_lexpr_clocs le)) ac les) 
		SS.empty 
		preds

(** Return the set containing all the alocs occurring in --preds-- *)
let preds_alocs (preds : predicate_set) : SS.t =
	DynArray.fold_left 
		(fun ac (_, les) -> List.fold_left (fun ac le -> SS.union ac (get_lexpr_alocs le)) ac les)
		SS.empty 
		preds

(** conversts a predicate set to a list of assertions *)
let assertions_of_preds (preds : predicate_set) : jsil_logic_assertion list = 
	let preds = preds_to_list preds in 
	let rec loop preds assertions = 
		match preds with 
		| [] -> assertions 
		| (pred_name, args) :: rest -> 
			loop rest ((LPred (pred_name, args)) :: assertions) in 
	loop preds [] 


(*************************************)
(** Symbolic State functions        **)
(*************************************)

(** Symbolic state first projection *)
let ss_heap (symb_state : symbolic_state) : SHeap.t =
	let heap, _, _, _, _ = symb_state in heap

(** Symbolic state second projection *)
let ss_store (symb_state : symbolic_state) : SStore.t =
	let _, store, _, _, _ = symb_state in store

(** Symbolic state third projection *)
let ss_pfs (symb_state : symbolic_state) : PFS.t =
	let _, _, pfs, _, _ = symb_state in pfs

(** Symbolic state fourth projection *)
let ss_gamma (symb_state : symbolic_state) : TypEnv.t =
	let _, _, _, gamma, _ = symb_state in gamma

(** Symbolic state fifth projection *)
let ss_preds (symb_state : symbolic_state) : predicate_set =
	let _, _, _, _, preds = symb_state in preds

let ss_pfs_list (symb_state : symbolic_state) : jsil_logic_assertion list =
	PFS.to_list (ss_pfs symb_state)

let ss_extend_preds (symb_state : symbolic_state) (pred_assertion : predicate_assertion) : unit =
	preds_extend (ss_preds symb_state) pred_assertion

let ss_extend_pfs (symb_state : symbolic_state) (pfs_to_add : PFS.t) : unit =
	pfs_merge (ss_pfs symb_state) pfs_to_add

(** Replaces the --symb_state-- heap with --heap--   *)
let ss_replace_heap (symb_state : symbolic_state) (heap : SHeap.t) : symbolic_state =
	let _, store, pfs, gamma, preds  = symb_state in (heap, store, pfs, gamma, preds)

(** Replaces the --symb_state-- store with --store-- *)
let ss_replace_store (symb_state : symbolic_state) (store : SStore.t) : symbolic_state =
	let heap, _, pfs, gamma, preds   = symb_state in (heap, store, pfs, gamma, preds)

(** Replaces the --symb_state-- pfs with --pfs--     *)
let ss_replace_pfs (symb_state : symbolic_state) (pfs : PFS.t) : symbolic_state =
	let heap, store, _, gamma, preds = symb_state in (heap, store, pfs, gamma, preds)

(** Replaces the --symb_state-- gamma with --gamma-- *)
let ss_replace_gamma (symb_state : symbolic_state) (gamma : TypEnv.t) : symbolic_state =
	let heap, store, pfs, _, preds   = symb_state in (heap, store, pfs, gamma, preds)

(** Replaces the --symb_state-- preds with --preds-- *)
let ss_replace_preds (symb_state : symbolic_state) (preds : predicate_set) : symbolic_state =
	let heap, store, pfs, gamma, _   = symb_state in (heap, store, pfs, gamma, preds)

(** Returns a new empty symbolic state *)
let ss_init () : symbolic_state = (SHeap.init (), (SStore.init [] []), PFS.init (), TypEnv.init (), preds_init ())

(** Returns a copy of the symbolic state *)
let ss_copy (symb_state : symbolic_state) : symbolic_state =
	let heap, store, pfs, gamma, preds = symb_state in
	let c_heap   = SHeap.copy heap in
	let c_store  = SStore.copy store in
	let c_pfs    = pfs_copy pfs in
	let c_gamma  = TypEnv.copy gamma in
	let c_preds  = preds_copy preds in
	(c_heap, c_store, c_pfs, c_gamma, c_preds)

(** Returns subst(symb_state) *)
let ss_substitution 
		(subst : substitution) (partial : bool) (symb_state : symbolic_state) : symbolic_state =
	let heap, store, pf, gamma, preds = symb_state in
	let s_heap  = SHeap.substitution subst partial heap in
	let s_store = SStore.substitution subst partial store in
	let s_pf    = pfs_substitution subst partial pf in
	let s_gamma = TypEnv.substitution gamma subst partial in
	let s_preds = preds_substitution subst partial preds in
	(s_heap, s_store, s_pf, s_gamma, s_preds)

let ss_substitution_in_place_no_gamma
		(subst : substitution) (symb_state : symbolic_state) : unit =
	let heap, store, pfs, gamma, preds = symb_state in
	SHeap.substitution_in_place subst heap;		
	SStore.substitution_in_place subst store;
	pfs_substitution_in_place   subst pfs;	
	preds_substitution_in_place subst preds

(** Return the set containing all the lvars occurring in --symb_state-- *)
let ss_lvars (symb_state : symbolic_state) : SS.t =
	let heap, store, pfs, gamma, preds = symb_state in
	let v_h  : SS.t = SHeap.lvars heap in
	let v_s  : SS.t = SStore.lvars store in
	let v_pf : SS.t = pfs_lvars pfs in
	let v_g  : SS.t = TypEnv.lvars gamma in
	let v_pr : SS.t = preds_lvars preds in
		SS.union v_h (SS.union v_s (SS.union v_pf (SS.union v_g v_pr)))

(** Return the set containing all the lvars occurring in --symb_state-- *)
let ss_alocs (symb_state : symbolic_state) : SS.t =
	let heap, store, pfs, gamma, preds = symb_state in
	let v_h  : SS.t = SHeap.alocs heap in
	let v_s  : SS.t = SStore.alocs store in
	let v_pf : SS.t = pfs_alocs pfs in
	let v_pr : SS.t = preds_alocs preds in
		SS.union v_h (SS.union v_s (SS.union v_pf v_pr))

(** Return the set containing all the lvars occurring in --symb_state-- 
    except for those that only appear in the gamma + all the program 
    variables in the store *)
let ss_vars_no_gamma (symb_state : symbolic_state) : SS.t =
	let heap, store, pfs, gamma, preds = symb_state in
	let v_h  = SHeap.lvars heap in
	let v_s  = SStore.lvars store in
	let v_sp = SStore.domain store in 
	let v_pf = pfs_lvars pfs in
	let v_pr = preds_lvars preds in
		SS.union v_h (SS.union v_s (SS.union v_sp (SS.union v_pf v_pr)))

(** conversts a symbolic state to an assertion *)
let assertion_of_symb_state (symb_state : symbolic_state) : jsil_logic_assertion = 
	let heap, store, pfs, gamma, preds = symb_state in
	let heap_asrts  = SHeap.assertions heap in
	let store_asrts = SStore.assertions store in
	let gamma_asrt  = TypEnv.assertions gamma in
	let pure_asrts  = PFS.to_list pfs in
	let pred_asrts  = assertions_of_preds preds in 
	let asrts       = heap_asrts @ store_asrts @ pure_asrts @ [ gamma_asrt ] @ pred_asrts in
	JSIL_Logic_Utils.star_asses asrts 


(****************************************)
(** Normalised Predicate Definitions   **)
(****************************************)

let get_pred (pred_tbl : (string, n_jsil_logic_predicate) Hashtbl.t) (pred_name : string) : n_jsil_logic_predicate =
	try
		Hashtbl.find pred_tbl pred_name
	with _ ->
		let msg = Printf.sprintf "Predicate %s does not exist" pred_name in
		raise (Failure msg)


(*********************************************************)
(** Pruning Info                                        **)
(*********************************************************)

(** Returns a new (empty) pruning info table *)
let pruning_info_init () : pruning_table = Hashtbl.create small_tbl_size

(** Extends --pi-- with a new array for each single spec in --n_spec-- *)
let pruning_info_extend (pi : pruning_table) (spec : jsil_n_spec) : unit =
	let spec_pi =
		List.map (fun ss -> Array.make (List.length ss.n_post) false) spec.n_proc_specs in
	Hashtbl.replace pi spec.n_spec_name spec_pi

(** Removes unreachable posts in --spec-- using --pi_arr-- *)
let prune_posts_sspec (pi_arr : bool array) (spec : jsil_n_single_spec) : jsil_n_single_spec =
	let posts = List.filter (fun (post, b) -> b) (List.combine spec.n_post (Array.to_list pi_arr)) in
	{ spec with n_post = (List.map (fun (post, _) -> post) posts) }

(** Removes unreachable posts in --spec-- using --pi-- *)
let prune_posts (pi : pruning_table) (spec : jsil_n_spec) (proc_name : string) : jsil_n_spec =
	try
		let new_sspecs = List.map2 prune_posts_sspec (Hashtbl.find pi proc_name) (spec.n_proc_specs) in
		{ spec with n_proc_specs = new_sspecs }
	with Not_found -> spec

(** Activates the postcondition number --post_number-- in the pruning info 
    of the spec number --si.spec_number-- of the procedure --si.proc_name--  *)
let turn_on_post (post_number : int) (sec : symbolic_execution_context) : unit =
	try
		let pi     = Hashtbl.find (sec.post_pruning_info) sec.proc_name in
		let pi_arr = List.nth pi (sec.spec_number) in
		pi_arr.(post_number) <- true
	with Not_found -> ()


(*********************************************************)
(** Symbolic Execution Context (SEC)                    **)
(*********************************************************)

let symb_graph_init (root_node : symb_graph_node) : symbolic_graph = 
	{ 
	  root         = root_node; 
	  info_nodes   = Hashtbl.create small_tbl_size;
	  info_edges   = Hashtbl.create small_tbl_size }

(** Returns a new sec node - initialised as the code shows                *)
let sec_init 
		(node_info : symb_graph_node) (pi : pruning_table) 
		(proc_name : string) (spec_number : int) : symbolic_execution_context = 
	
	if (not (node_info.node_number = 0)) then
		raise (Failure "the node number of the first node must be 0")
	else begin
		let new_sec =
			{
				vis_tbl             = Hashtbl.create small_tbl_size;
				cur_node_info       = node_info;
				symb_graph          = symb_graph_init node_info; 
				next_node           = ref 1;
				post_pruning_info   = pi;
				spec_number         = spec_number;
				pred_info           = Hashtbl.create small_tbl_size;
				proc_name           = proc_name 
			} in
		Hashtbl.replace new_sec.symb_graph.info_edges 0 [];
		Hashtbl.replace new_sec.symb_graph.info_nodes 0 node_info;
		new_sec
	end

(** Duplicates the current --sec--. Only the elements of --sec-- that 
    cannot be shared between different symbolic executions are deep 
    copied                                                             *)
let sec_duplicate (sec : symbolic_execution_context) : symbolic_execution_context = 
	let new_vis_tbl   = Hashtbl.copy sec.vis_tbl in 
	let new_pred_info = Hashtbl.copy sec.pred_info in 	
	Hashtbl.iter (fun pred_name pred_stack -> 
		Hashtbl.replace new_pred_info pred_name (Stack.copy pred_stack)
	) sec.pred_info; 
	{ sec with vis_tbl = new_vis_tbl; pred_info = new_pred_info }

(** Sets --sec.vis_tbl-- to the empty table                            *)
let sec_reset_vis_tbl (sec : symbolic_execution_context) : symbolic_execution_context = 
	{ sec with vis_tbl = Hashtbl.create small_tbl_size }

(** Marks node --i-- has visited in --sec--                            *)
let sec_visit_node (sec : symbolic_execution_context) (i : int) : unit =
	let cur_node_info = sec.cur_node_info in
	Hashtbl.replace sec.vis_tbl i cur_node_info.node_number 

(** Checks if node --i-- has visited using the information in --sec--  *)
 let sec_is_visited_node (sec : symbolic_execution_context) (i : int) : bool = 
 	Hashtbl.mem sec.vis_tbl i

(** Gets the index of the last unfolded definition of --pred_name--    *)
let sec_fold_pred_def 
		(sec         : symbolic_execution_context) 
		(pred_name   : string) : symbolic_execution_context * int =
	
	let pred_info = sec.pred_info in
	(match Hashtbl.mem pred_info pred_name with
	| false -> sec, -1
	| true ->
		let s = Hashtbl.find pred_info pred_name in
		(match Stack.is_empty s with
		| true -> sec, -1
		| false ->
			let pred_info = Hashtbl.copy pred_info in
			let s         = Stack.copy s in
			let cmf       = Stack.pop s in
			Hashtbl.replace pred_info pred_name s;
			{ sec with pred_info = pred_info }, cmf)) 

(** Extend --sec-- with the index of definition of --pred_name-- to 
    be unfolded next                                                   *)
let sec_unfold_pred_def 
		(sec         : symbolic_execution_context) 
		(pred_name   : string)
		(def_index   : int) : unit = 

	let pred_stack = try Hashtbl.find sec.pred_info pred_name with Not_found -> (
		let pred_stack = Stack.create () in 
		Hashtbl.replace sec.pred_info pred_name pred_stack; 
		pred_stack 	
	) in 
	Stack.push def_index pred_stack; () 	

(** Extends sec with a new node_info, updating all the structures that 
    maintain the symbolic execution graphy                            *)
let sec_create_new_info_node 
		(sec            : symbolic_execution_context)
		(new_node_info  : symb_graph_node) : symbolic_execution_context = 

	let new_node_number  = !(sec.next_node) in
	let new_node_info    = { new_node_info with node_number = new_node_number } in 
	let parent_node_info = sec.cur_node_info in
	
	sec.next_node := new_node_number + 1;
	Hashtbl.add (sec.symb_graph.info_nodes) new_node_number new_node_info;
	Hashtbl.replace sec.symb_graph.info_edges new_node_number []; 

	(try 
 		let parent_children = Hashtbl.find sec.symb_graph.info_edges parent_node_info.node_number in
 		Hashtbl.replace sec.symb_graph.info_edges parent_node_info.node_number (new_node_number :: parent_children); 
	with _ -> Printf.printf "DEATH. sec_create_new_info_node"); 

	{ sec with cur_node_info = new_node_info }


(****************************************)
(** TO REFACTOR                        **)
(****************************************)

let selective_heap_substitution_in_place (subst : substitution) (heap : SHeap.t) =
	let le_subst = lexpr_substitution subst true in
  Heap.iter
  	(fun loc ((fv_list, domain), metadata, ext) ->
  		let s_loc =
  			(try Hashtbl.find subst loc
  				with _ ->
  					if (is_aloc_name loc)
  						then ALoc loc
  						else (LLit (Loc loc))) in
  		let s_loc =
  			(match s_loc with
  				| LLit (Loc loc) -> loc
  				| ALoc loc -> loc
  				| _ ->
  					raise (Failure "Heap substitution failed miserably!!!")) in
  		let s_fv_list = SFVL.selective_substitution subst true fv_list in
  		let s_domain = Option.map le_subst domain in
			let s_metadata = Option.map le_subst metadata in
  		Heap.replace heap s_loc ((s_fv_list, s_domain), s_metadata, ext))
  	heap

let selective_symb_state_substitution_in_place_no_gamma 
		(subst : substitution) (symb_state : symbolic_state) : unit =
	let lexpr_subst = JSIL_Logic_Utils.lexpr_selective_substitution in
	let heap, store, pfs, gamma, preds = symb_state in
	SStore.substitution_in_place         subst store;
	preds_substitution_in_place          subst preds;
	pfs_substitution_in_place            subst pfs;
	selective_heap_substitution_in_place subst heap 

(*********************************************************)
(** Information to keep track during symbolic exeuction **)
(*********************************************************)


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