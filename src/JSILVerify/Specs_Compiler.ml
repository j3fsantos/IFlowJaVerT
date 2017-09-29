open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils


let __UNFOLDING_LIMIT__ = 2 


let make_unfoldings_record 
		(pred_defs : (string, n_jsil_logic_predicate) Hashtbl.t) : (string, int) Hashtbl.t = 

	let unfoldings_record = Hashtbl.create small_tbl_size in 
	Hashtbl.iter (fun pred_name _ -> Hashtbl.replace unfoldings_record pred_name __UNFOLDING_LIMIT__) pred_defs; 
	unfoldings_record


let rec concretise_symb_state 
		(spec_vars         : SS.t)
		(pred_defs  	   : (string, n_jsil_logic_predicate) Hashtbl.t)
		(unfoldings_record : (string, int) Hashtbl.t) 
		(symb_state        : symbolic_state) : symbolic_state list = 

	let preds = preds_to_list (ss_preds symb_state) in 
	let f_rec = concretise_symb_state spec_vars pred_defs in 

	(match preds with 
	| [] -> [ symb_state ]

	| (pname, les) :: _ -> 
		if ((Hashtbl.find unfoldings_record pname) >= __UNFOLDING_LIMIT__) then [] else (
			let n_pred        = get_pred pred_defs pname in
			let unfold_store  = store_init n_pred.n_pred_params les in 	
			
			let unfolded_symb_states_and_limits = 
				List.concat (List.map (fun (_, pred_def, _) -> 
					let new_symb_state      = ss_copy symb_state in 
					let unfold_store        = store_copy unfold_store in 
					let subst               = init_substitution [] in 
					let pat_subst           = init_substitution [] in 
					preds_remove (ss_preds new_symb_state) (pname, les); 
					let unfolded_symb_state = Spatial_Entailment.unfold_predicate_definition unfold_store subst pat_subst SS.empty spec_vars pred_def symb_state in 
					(match unfolded_symb_state with 
					| None                     -> [] 
					| Some unfolded_symb_state -> 
						let new_unfoldings_record = Hashtbl.copy unfoldings_record in 
						Hashtbl.replace new_unfoldings_record pname ((Hashtbl.find unfoldings_record pname) + 1); 
						[ (unfolded_symb_state, new_unfoldings_record) ])
				) n_pred.n_pred_definitions) in 

			List.concat (List.map (fun (ss, unfoldings_rec) -> f_rec unfoldings_rec ss) unfolded_symb_states_and_limits)))



let concretise_single_spec 
		(n_spec         : jsil_n_single_spec)
		(pred_defs  	: (string, n_jsil_logic_predicate) Hashtbl.t) : jsil_n_single_spec list = 

	let new_unfoldings_record = make_unfoldings_record pred_defs in  
	let new_pres              = concretise_symb_state n_spec.n_lvars pred_defs new_unfoldings_record n_spec.n_pre in 
	List.concat (List.map (fun new_pre -> 
		[]
	) new_pres)



(* 

type jsil_n_single_spec = {
	n_pre              : symbolic_state;
	n_post             : symbolic_state list;
	n_ret_flag         : jsil_return_flag;
	n_lvars            : SS.t; 
	n_subst            : substitution; 
	n_unification_plan : jsil_logic_assertion list; 
}

*)


(*
	unfold_predicate_definition 
		(unfold_store   : symbolic_store)
		(subst          : substitution)
		(pat_subst      : substitution)
		(existentials   : SS.t)
		(spec_vars      : SS.t)
		(pat_symb_state : symbolic_state)
		(symb_state     : symbolic_state) : s

	(pred_name       : string)
		(pred_args       : jsil_logic_expr list)
		
*)