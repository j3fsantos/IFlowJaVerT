open JSIL_Syntax

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
type symbolic_state = symbolic_heap * symbolic_store * (jsil_logic_assertion DynArray.t) * ((string, jsil_type) Hashtbl.t) 

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
