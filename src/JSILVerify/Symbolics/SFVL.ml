(** JSIL symbolic field-value list *)

open CCommon
open SCommon
open JSIL_Syntax
open JSIL_Print

type field_name  = jsil_logic_expr
type field_value = Permission.t * jsil_logic_expr

let gsbsts = JSIL_Logic_Utils.get_lexpr_substitutables

(* Definition *)
type t = (field_value * SS.t) MLExpr.t

let str_of_fv (fv : field_value) : string =
	let perm, value = fv in
	let perm_str  = Permission.str perm in
	let value_str = string_of_logic_expression value in
		perm_str ^ " " ^ value_str

(* Printing *)
let str (sfvl : t) : string = 
	MLExpr.fold
		(fun field (value, _) ac ->
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

(* Map functions to be reused *)

let add         = (fun fn (perm, fv) -> MLExpr.add fn ((perm, fv), (SS.union (gsbsts fn) (gsbsts fv))))
let empty       = MLExpr.empty
let copy        = (fun sfvl -> sfvl)
let field_names = (fun sfvl -> let result, _ = List.split (MLExpr.bindings sfvl) in result)
let fold        = (fun f sfvl ac -> MLExpr.fold (fun fn (fv, _) -> f fn fv) sfvl ac)
let get         = (fun fn sfvl -> Option.map (fun (fv, _) -> fv) (MLExpr.find_opt fn sfvl))
let is_empty    = (fun sfvl -> sfvl = empty)
let iter        = (fun f sfvl -> MLExpr.iter (fun fn (fv, _) -> f fn fv) sfvl)
let partition   = (fun f sfvl -> MLExpr.partition (fun fn (fv, _) -> f fn fv) sfvl)
let remove      = MLExpr.remove
let union       = MLExpr.union (fun k fvl fvr -> print_debug_petar "WARNING: SFVL.union: merging with field in both lists, choosing left."; Some fvl)

(** Gets a first key-value pair that satisfies a predicate *)
let get_first (f : field_name -> bool) (sfvl : t) : (field_name * field_value) option = 
	let found = ref false in
	MLExpr.fold (fun fn (fv, _) ac -> 
		if !found then ac
		else 
			if (f fn) 
				then (found := true; Some (fn, fv))
				else ac) sfvl None

(** Returns the logical variables occuring in --sfvl-- *)
let lvars (sfvl : t) : SS.t =
	let gllv = JSIL_Logic_Utils.get_lexpr_lvars in
	MLExpr.fold (fun e_field ((_, e_val), _) ac -> SS.union ac (SS.union (gllv e_field) (gllv e_val))) sfvl SS.empty 

(** Returns the abstract locations occuring in --sfvl-- *)
let alocs (sfvl : t) : SS.t =
	let gla = JSIL_Logic_Utils.get_lexpr_alocs in
	MLExpr.fold (fun e_field ((_, e_val), _) ac -> SS.union ac (SS.union (gla e_field) (gla e_val))) sfvl SS.empty 

let assertions (loc : jsil_logic_expr) (sfvl : t) : jsil_logic_assertion list = 
	List.rev (MLExpr.fold (fun field ((perm, value), _) ac -> (LPointsTo (loc, field, (perm, value)) :: ac)) sfvl [])

(* Substitution *)
let substitution 
		(subst   : substitution) 
		(partial : bool) 
		(fv_list : t) : t =
	let f_subst = JSIL_Logic_Utils.lexpr_substitution subst partial in 
	let subst_dom = substitution_domain subst in 
	MLExpr.fold (fun le_field ((perm, le_val), substs) ac -> 
		let sf, sv, substs = 
			if partial && (SS.inter substs subst_dom = SS.empty) 
				then le_field, le_val, substs
				else (			
					let sf = f_subst le_field in
					let sv = f_subst le_val in 
						sf, sv, SS.union (gsbsts sf) (gsbsts sv)
				) in 
			MLExpr.add sf ((perm, sv), substs) ac) fv_list MLExpr.empty

(* Selective substitution *)
let selective_substitution 
		(subst   : substitution) 
		(partial : bool) 
		(fv_list : t) : t =
	let f_subst = JSIL_Logic_Utils.lexpr_substitution subst partial in 
	MLExpr.fold (fun le_field ((perm, le_val), _) ac -> 
		let sf = le_field in
		let sv = f_subst le_val in
			MLExpr.add sf ((perm, sv), (SS.union (gsbsts sf) (gsbsts sv))) ac) fv_list MLExpr.empty

(* Correctness of field-value lists *)
let is_well_formed (sfvl : t) : bool =
	MLExpr.fold (fun k ((perm, value), substs) ac -> if (ac = false) then false 
		else (
			let fn = gsbsts k in
			let fv = gsbsts value in
			print_debug_petar (Printf.sprintf "\t\tField: %s\n\t\tCurrent: %s\n\t\tName: %s\n\t\tValue:%s"
				(JSIL_Print.string_of_logic_expression k)
				(String.concat ", " (SS.elements substs))
				(String.concat ", " (SS.elements fn))
				(String.concat ", " (SS.elements fv)));
			substs = SS.union fn fv
		)) sfvl true
		
