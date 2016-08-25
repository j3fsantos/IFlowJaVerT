open SJSIL_Syntax

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

type symbolic_heap = (((jsil_logic_expr * jsil_logic_expr) list) * jsil_logic_expr)  LHeap.t 
type symbolic_store = (string, jsil_logic_expr) Hashtbl.t
type symbolic_state = symbolic_heap * symbolic_store * (jsil_logic_assertion DynArray.t) * ((string, jsil_type) Hashtbl.t) * ((string * (jsil_logic_expr list)) DynArray.t)
type substitution = ((string, jsil_logic_expr) Hashtbl.t)


type jsil_n_single_spec = {
	  n_pre : symbolic_state; 
		n_post : symbolic_state; 
		n_ret_flag : jsil_return_flag 
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

let copy_symb_state symb_state = 
	let heap, store, p_formulae, gamma, preds = symb_state in 
	let c_heap = LHeap.copy heap in 
	let c_store = Hashtbl.copy store in 
	let c_pformulae = DynArray.copy p_formulae in 
	let c_gamma = Hashtbl.copy gamma in 
	let c_preds = DynArray.copy preds in 
	(c_heap, c_store, c_pformulae, c_gamma, c_preds)

	

