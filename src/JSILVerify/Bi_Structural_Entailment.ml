open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils
open Symbolic_State_Basics
open Structural_Entailment


(** 
	Unify two logical field-value lists

	@param pat_fv_list      Field-value list in the pattern heap
	@param fv_list          Field-value list in the current heap
	@param def_val   	      Default value of the object corresponding to fv_list
	@param p_formulae       Pure formulae of the current heap 
	@param gamma            Typing environment of the current heap
	@param subst            Substitution mapping the pattern symb_state to the current symb_state
		
	
*)
let bi_unify_symb_fv_lists (pat_fv_list : symbolic_field_value_list)
				    							 (fv_list     : symbolic_field_value_list)
												   (def_val     : jsil_logic_expr) 
												   (p_formulae  : pure_formulae)
											   	 (gamma       : typing_environment) 
												   (subst       : substitution) 
															: (symbolic_field_value_list * symbolic_field_value_list) option =

	let rec loop (fv_list             : symbolic_field_value_list) 
							 (pat_list            : symbolic_field_value_list) 
							 (matched_fv_list     : symbolic_field_value_list)
							 (anti_frame_fv_list  : symbolic_field_value_list)  =
		match pat_list with
		| [] -> Some (fv_list, matched_fv_list)
		| (pat_field, pat_val) :: rest_pat_list ->
			let may_be_unifiable, res = unify_fv_pair (pat_field, pat_val) fv_list p_formulae gamma subst in
			(match may_be_unifiable, res with
		  (* The algorithm found the field but the value expressions do not unify                            *)
			| false, _ -> None 
			(* Illegal case                                                                                    *)
			| true, None ->
				print_debug (Printf.sprintf "I could NOT unify an fv-pair. pat_val: %s. def_val: %s" (JSIL_Print.string_of_logic_expression pat_val false) (JSIL_Print.string_of_logic_expression def_val false));
				(match def_val with
				| LUnknown -> None
				| _ ->
					let (bv, unifier) = unify_lexprs pat_val def_val p_formulae gamma subst in
					if (bv && (Symbolic_State_Functions.update_subst1 subst unifier))
						then loop fv_list rest_pat_list matched_fv_list
						else None)
			| true, Some (rest_fv_list, matched_fv_pair) ->
				loop rest_fv_list rest_pat_list (matched_fv_pair :: matched_fv_list)) in
	let order_pat_list = order_fv_list pat_fv_list in
	loop fv_list order_pat_list []

