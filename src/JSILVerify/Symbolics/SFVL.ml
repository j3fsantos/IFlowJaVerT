(** JSIL symbolic field-value list *)

open CCommon
open JSIL_Syntax
open JSIL_Print

(* Symbolic field names *)
type field_name = jsil_logic_expr

(* Symbolic field values *)
type field_value = 
	{ permission : Permission.t; 
	       value : jsil_logic_expr }

(* Symbolic field name-value lists *)
type t = (field_name, field_value) Hashtbl.t

(* Printing *)
let str (sfvl : t) : string = 
	Hashtbl.fold
		(fun fn fv ac ->
				let  name_str = string_of_logic_expression fn in
				let  perm_str = Permission.str fv.permission in
				let value_str = string_of_logic_expression fv.value in
				let field_value_str = "(" ^ name_str ^ " :" ^ perm_str ^ " " ^ value_str ^ ")"  in
				let sep = if (ac = "") then "" else ", " in
					ac ^ sep ^ field_value_str)
		sfvl ""
		
(*************************************)
(** Field Value List Functions      **)
(*************************************)

let empty () : t = Hashtbl.create medium_tbl_size

let get (sfvl : t) (name : field_name) : field_value option = 
	Hashtbl.find_opt sfvl name

let set (sfvl : t) (name : field_name) (value : field_value) : unit =
	Hashtbl.replace sfvl name value

(* Copy *)
let copy (sfvl : t) : t = 
	Hashtbl.copy sfvl

let merge_left (sfvl_l : t) (sfvl_r : t) : unit =
	Hashtbl.iter
	(fun name value ->
		if (Hashtbl.mem sfvl_l name) then print_debug ("WARNING: Merge overwrites existing field.");
		Hashtbl.replace sfvl_l name value )
	sfvl_r

(* Substitution *)
let substitution ?(partial: bool option) (subst : substitution) (fv_list : t) : unit =
	let is_partial = Option.default true partial in
	let le_subst = JSIL_Logic_Utils.lexpr_substitution subst is_partial in 
	Hashtbl.iter
		(fun name value -> 
			let new_name  = le_subst name in
			let new_value = le_subst value.value in
			if (Hashtbl.mem fv_list new_name) then print_debug ("WARNING: Substitution overwrites existing field.");
			Hashtbl.replace fv_list new_name { value with value = new_value }
		)
	fv_list

(* Selective substitution *)
let selective_substitution 
		(subst   : substitution) 
		(partial : bool) 
		(fv_list : t) : unit =
	let f_subst = JSIL_Logic_Utils.lexpr_selective_substitution subst partial in 
	Hashtbl.iter
		(fun name value -> 
			let new_value = f_subst value.value in
			Hashtbl.replace fv_list name { value with value = new_value }
		)
	fv_list

let get_lvars (sfvl : t) : SS.t = 
	let gllv = JSIL_Logic_Utils.get_lexpr_lvars in 
	Hashtbl.fold (fun name value ac -> SS.union ac (SS.union (gllv name) (gllv value.value))) sfvl SS.empty

(** Returns the abstract locations occuring in --heap-- *)
let get_alocs (sfvl : t) : SS.t =
	let gla = JSIL_Logic_Utils.get_lexpr_alocs in
	Hashtbl.fold (fun name value ac -> SS.union ac (SS.union (gla name) (gla value.value))) sfvl SS.empty 

let to_list (sfvl : t) = 
	Hashtbl.fold (fun name value ac -> ac @ [ (name, (value.permission, value.value)) ]) sfvl []