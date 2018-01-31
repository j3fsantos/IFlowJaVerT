(** JSIL symbolic field-value list *)

open JSIL_Syntax
open JSIL_Print

(* Definition *)
type t = (jsil_logic_expr * (Permission.t * jsil_logic_expr)) list

(* Printing *)
let str (sfvl : t) : string = 
	List.fold_left
		(fun ac (field, (perm, value)) ->
				let field_str = string_of_logic_expression field in
				let perm_str  = Permission.str perm in
				let value_str = string_of_logic_expression value in
				let field_value_str = "(" ^ field_str ^ " :" ^ perm_str ^ " " ^ value_str ^ ")"  in
				if (ac = "")
					then field_value_str
					else ac ^ ", " ^ field_value_str)
		""
		sfvl
		
(*************************************)
(** Field Value List Functions      **)
(*************************************)

(* Substitution *)
let substitution 
		(subst   : substitution) 
		(partial : bool) 
		(fv_list : t) : t =
	let f_subst = JSIL_Logic_Utils.lexpr_substitution subst partial in 
	List.map (fun (le_field, (perm, le_val)) -> f_subst le_field, (perm, f_subst le_val)) fv_list

(* Selective substitution *)
let selective_substitution 
		(subst   : substitution) 
		(partial : bool) 
		(fv_list : t) : t =
	let f_subst = JSIL_Logic_Utils.lexpr_selective_substitution subst partial in 
	List.map (fun (le_field, (perm, le_val)) -> (le_field, (perm, f_subst le_val))) fv_list