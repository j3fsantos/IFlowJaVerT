(** JSIL symbolic field-value list *)

open CCommon
open JSIL_Syntax
open JSIL_Print

type field_name  = jsil_logic_expr
type field_value = Permission.t * jsil_logic_expr

(* Definition *)
type t = (Permission.t * jsil_logic_expr) MLExpr.t

let str_of_fv (fv : field_value) : string =
	let perm, value = fv in
	let perm_str  = Permission.str perm in
	let value_str = string_of_logic_expression value in
		perm_str ^ " " ^ value_str

(* Printing *)
let str (sfvl : t) : string = 
	MLExpr.fold
		(fun field value ac ->
			let field_str = string_of_logic_expression field in
			let value_str = str_of_fv value in
			let field_value_str = "(" ^ field_str ^ " :" ^ value_str ^ ")"  in
			if (ac = "")
				then field_value_str
				else ac ^ ", " ^ field_value_str)
		sfvl
		""
		
(*************************************)
(** Field Value List Functions      **)
(*************************************)

(* The Map interface exposed *)

let add         = MLExpr.add
let empty       = MLExpr.empty
let field_names = (fun t -> let result, _ = List.split (MLExpr.bindings t) in result)
let fold        = MLExpr.fold
let get_first   = MLExpr.find_first_opt
let get         = MLExpr.find_opt
let iter        = MLExpr.iter
let partition   = MLExpr.partition
let remove      = MLExpr.remove
let union       = MLExpr.union (fun k fvl fvr -> print_debug_petar (Printf.sprintf "WARNING: SFVL.union: merging with field %s in both lists with values %s and %s, choosing left." (JSIL_Print.string_of_logic_expression k) (str_of_fv fvl) (str_of_fv fvr)); Some fvl)

(** Returns the logical variables occuring in --sfvl-- *)
let lvars (sfvl : t) : SS.t =
	let gllv = JSIL_Logic_Utils.get_lexpr_lvars in
	MLExpr.fold (fun e_field (_, e_val) ac -> SS.union ac (SS.union (gllv e_field) (gllv e_val))) sfvl SS.empty 

(** Returns the abstract locations occuring in --sfvl-- *)
let alocs (sfvl : t) : SS.t =
	let gla = JSIL_Logic_Utils.get_lexpr_alocs in
	MLExpr.fold (fun e_field (_, e_val) ac -> SS.union ac (SS.union (gla e_field) (gla e_val))) sfvl SS.empty 

let assertions (loc : jsil_logic_expr) (sfvl : t) : jsil_logic_assertion list = 
	List.rev (MLExpr.fold (fun field (perm, value) ac -> (LPointsTo (loc, field, (perm, value)) :: ac)) sfvl [])

(* Substitution *)
let substitution 
		(subst   : substitution) 
		(partial : bool) 
		(fv_list : t) : t =
	let f_subst = JSIL_Logic_Utils.lexpr_substitution subst partial in 
	MLExpr.fold (fun le_field (perm, le_val) ac -> MLExpr.add (f_subst le_field) (perm, f_subst le_val) ac) fv_list MLExpr.empty

(* Selective substitution *)
let selective_substitution 
		(subst   : substitution) 
		(partial : bool) 
		(fv_list : t) : t =
	let f_subst = JSIL_Logic_Utils.lexpr_selective_substitution subst partial in 
	MLExpr.map (fun (perm, le_val) -> (perm, f_subst le_val)) fv_list