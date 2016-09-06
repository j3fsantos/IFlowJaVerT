open JSIL_Syntax
open JSIL_Logic_Utils

(* SJSIL Heaps *)
 module SHeap = Hashtbl.Make(
	struct
		type t = string	
		let equal = (=)
		let hash = Hashtbl.hash
	end)

(* Abstract Heaps and stores *)
module LHeap = Hashtbl.Make(
	struct
		type t = string	
		let equal = (=)
		let hash = Hashtbl.hash
	end)

type substitution = ((string, jsil_logic_expr) Hashtbl.t)
type symbolic_heap = (((jsil_logic_expr * jsil_logic_expr) list) * jsil_logic_expr)  LHeap.t 
type symbolic_store = (string, jsil_logic_expr) Hashtbl.t
type typing_environment = ((string, jsil_type) Hashtbl.t)
type predicate_set = ((string * (jsil_logic_expr list)) DynArray.t)
type pure_formulae = (jsil_logic_assertion DynArray.t)
type symbolic_state = symbolic_heap * symbolic_store * pure_formulae * typing_environment * predicate_set

type jsil_n_single_spec = {
	  n_pre : symbolic_state; 
		n_post : symbolic_state; 
		n_ret_flag : jsil_return_flag; 
		n_lvars: string list; 
		n_subst: substitution
}

type jsil_n_spec = { 
    n_spec_name : string;
    n_spec_params : jsil_var list; 
		n_proc_specs : jsil_n_single_spec list
}

type specification_table = (string, jsil_n_spec) Hashtbl.t


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
	DynArray.to_list pf

let symb_state_add_predicate_assertion symb_state (pred_name, args) = 
	let preds = get_preds symb_state in 
	DynArray.add preds (pred_name, args); 
	symb_state 
	

let symb_state_replace_store symb_state new_store = 
	let heap, _, pfs, gamma, preds = symb_state in 
	(heap, new_store, pfs, gamma, preds)

let copy_p_formulae pfs = 
	let new_pfs = DynArray.copy pfs in 
	new_pfs
	
let copy_gamma gamma = 
	let new_gamma = Hashtbl.copy gamma in 
	new_gamma

let copy_store store = 
	let new_store = Hashtbl.copy store in
	new_store

let copy_symb_state symb_state = 
	let heap, store, p_formulae, gamma, preds = symb_state in 
	let c_heap = LHeap.copy heap in 
	let c_store = Hashtbl.copy store in 
	let c_pformulae = DynArray.copy p_formulae in 
	let c_gamma = Hashtbl.copy gamma in 
	let c_preds = DynArray.copy preds in 
	(c_heap, c_store, c_pformulae, c_gamma, c_preds)

let copy_single_spec s_spec = 
	let copy_pre = copy_symb_state s_spec.n_pre in 
	{
		n_pre = copy_pre; 
		n_post = s_spec.n_post; 
		n_ret_flag = s_spec.n_ret_flag; 
		n_lvars = s_spec.n_lvars; 
		n_subst = s_spec.n_subst
	}

let pfs_to_list pfs = DynArray.to_list pfs 

let rec extend_symb_state_with_pfs symb_state pfs = 
	match pfs with 
	| [] -> () 
	| pf :: rest_pfs -> 
		DynArray.add (get_pf symb_state) pf; 
		extend_symb_state_with_pfs symb_state rest_pfs 
	
(* JSIL logic predicates *)
type n_jsil_logic_predicate = {
	n_pred_name        : string;
	n_pred_num_params  : int;
	n_pred_params      : jsil_logic_var list;
	n_pred_definitions : symbolic_state list;
}
		
type symb_jsil_program = {
	program    : jsil_program; 
	spec_tbl   : specification_table; 
	which_pred : (string * int * int, int) Hashtbl.t; 
	pred_defs  : (string, n_jsil_logic_predicate) Hashtbl.t
}


let update_gamma (gamma : typing_environment) x te = 
	(match te with 
	| None -> Hashtbl.remove gamma x
	| Some te -> Hashtbl.replace gamma x te)


let update_abs_store store x ne = 
	(* Printf.printf "I am in the update store\n"; 
	let str_store = "\t Store: " ^ (JSIL_Memory_Print.string_of_shallow_symb_store store) ^ "\n" in 
	Printf.printf "%s" str_store;  *)
	Hashtbl.replace store x ne


let extend_abs_store x store gamma = 
	let new_l_var_name = fresh_lvar () in 
	let new_l_var = LVar new_l_var_name in 
	(try 
		let x_type = Hashtbl.find gamma x in 
		Hashtbl.add gamma new_l_var_name x_type
	with _ -> ()); 
	Hashtbl.add store x new_l_var;
	new_l_var
	


