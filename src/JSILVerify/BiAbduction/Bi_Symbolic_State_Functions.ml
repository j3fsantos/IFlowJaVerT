open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils
open Symbolic_State_Utils

let update_abs_heap (heap : symbolic_heap) (anti_heap: symbolic_heap) loc e_field e_val p_formulae gamma =
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	let unchanged_fv_list, field_val_pair, i_am_sure_the_field_does_not_exist = find_field loc fv_list e_field p_formulae gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist, default_val with
	| Some _, _, _ 
	| None, true, LNone -> 
		LHeap.replace heap loc ((e_field, e_val) :: unchanged_fv_list, default_val)
	| None, true, _ -> 
		let v = LVar (fresh_lvar ()) in 
		Printf.printf "Updtate-abs-heap. loc: %s. field:%s. v:%s"
			loc
			(JSIL_Print.string_of_logic_expression e_field false)
			(JSIL_Print.string_of_logic_expression e_val false);
		heap_put_fv_pair heap loc e_field e_val;
		heap_put_fv_pair anti_heap loc e_field v;
	| None, false, _ ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e_field false) loc in
			raise (Failure msg)

let abs_heap_find (symb_state : symbolic_state) (anti_frame : symbolic_state) loc e_field  =
	let heap, _, pure_formulae, gamma, _ = symb_state in
	let anti_heap, _, anti_pure_formulae, _, _ = anti_frame in
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	let _, field_val_pair, i_am_sure_the_field_does_not_exist = find_field loc fv_list e_field pure_formulae gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist, default_val with
	| Some (_, f_val), _, _
		when (not (f_val = LNone)) -> 
		(f_val, false)
	| None, true, def when (not (def = LNone))  -> 
		let v = LVar (fresh_lvar ()) in 
		heap_put_fv_pair heap loc e_field v;
		heap_put_fv_pair anti_heap loc e_field v;
		(v, true)
	| Some (_, LNone), _, _
	| None, true, LNone  -> 
		let msg = Printf.sprintf "Looking up the field %s which does not exist in object %s" (JSIL_Print.string_of_logic_expression e_field false) loc in
			raise (Failure msg)
	| None, false, _ ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e_field false) loc in
			raise (Failure msg)

let abs_heap_check_field_existence  (symb_state : symbolic_state) (anti_frame : symbolic_state) loc e_field p_formulae gamma =
	let heap, _, pure_formulae, gamma, _ = symb_state in
	let anti_heap, _, anti_pure_formulae, _, _ = anti_frame in

	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	let _, field_val_pair, i_am_sure_the_field_does_not_exist = find_field loc fv_list e_field pure_formulae gamma in
	
	match field_val_pair, i_am_sure_the_field_does_not_exist, default_val with
	| Some (_, f_val), _, _ -> 
		if (Pure_Entailment.is_equal f_val LNone pure_formulae gamma) then
			(Some f_val, Some false)
			else (if (Pure_Entailment.is_different f_val LNone pure_formulae gamma) then
				(Some f_val, Some true)
				else (Some f_val, None))

	| None, true, def when (not (def = LNone))  -> 
		let v = LVar (fresh_lvar ()) in 
		heap_put_fv_pair heap loc e_field v;
		heap_put_fv_pair anti_heap loc e_field v;
		(Some v, None)

	| Some (_, LNone), _, _
	| None, true, LNone  ->	
		(Some LNone, Some false)

	| None, false, _ ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e_field false) loc in
			raise (Failure msg)

exception Non_reversable_type of unit

let rec bi_reverse_type_lexpr_aux pfs_af pfs gamma new_gamma le le_type =
	let f = bi_reverse_type_lexpr_aux pfs_af pfs gamma new_gamma in
	let check_type t = 
		match le_type with 
		| None -> ()
		| Some t' -> if( t = t') then () else raise (Non_reversable_type ()) in 

	let check_and_update_type () = 
		match le_type with 
			| Some t -> 
					let new_lvar = fresh_lvar () in
					weak_update_gamma new_gamma new_lvar le_type;
					add_pure_assertion pfs (LEq ((LVar new_lvar), le));
					add_pure_assertion pfs_af (LEq ((LVar new_lvar), le));
					()
			| None -> () in
 
	(match le with
	(* Literals are always typable *)
	| LLit lit -> check_type (evaluate_type_of lit)

	(* Variables are reverse-typable if they are already typable *)
	(* with the target type or if they are not typable           *)
	| LVar var
	| PVar var ->
		(match (gamma_get_type gamma var), (gamma_get_type new_gamma var) with
		| Some t, None
		| None, Some t     -> check_type t
		| None, None       -> (match le_type with 
								| Some t -> weak_update_gamma new_gamma var le_type ;()
								| None -> ()) 
		| Some t1, Some t2 -> (if (t1 = t2) then 
								check_type t1
							  else 
								raise (Failure "DEATH bi_reverse_type_lexpr_aux")))

	(* Abstract locations are reverse-typable if the target type is ObjectType *)
	| ALoc _ ->  check_type ObjectType

    (* LEList is not reverse typable because we lose type information *)
	| LEList les -> List.iter (fun le -> f le None; ()) les; check_type ListType

	| LUnOp (unop, le) ->
		(match unop with
		| Not 		-> f le (Some BooleanType); check_type BooleanType
		| UnaryMinus | BitwiseNot	| M_sgn	| M_abs		| M_acos	| M_asin	| M_atan	
		| M_ceil | M_cos	| M_exp	| M_floor	| M_log		| M_round	| M_sin		| M_sqrt
		| M_tan  | ToIntOp			| ToUint16Op			| ToInt32Op			| ToUint32Op
					->	f le le_type; check_type NumberType

		| ToStringOp ->	f le (Some NumberType); check_type StringType

		| ToNumberOp ->	f le (Some StringType); check_type NumberType

		| IsPrimitive -> raise (Failure "DEATH bi_reverse_type_lexpr_aux IsPrimitive")

		| Cdr -> f le (Some ListType); check_type ListType 
		| Car -> f le (Some ListType); check_and_update_type ()
		| LstLen -> f le (Some ListType); check_type NumberType

		| StrLen -> f le (Some StringType); check_type NumberType)


	| LBinOp (le1, op, le2) ->
		(match op with
		| Equal	-> f le1 None; f le2 None; check_type BooleanType
		| LessThan 
		| LessThanEqual -> f le1 (Some NumberType); f le2 (Some NumberType); check_type BooleanType
		| LessThanString -> f le1 (Some StringType); f le2 (Some StringType); check_type BooleanType

		| Plus	| Minus	| Times	| Mod | Div  ->
			f le1 (Some NumberType); f le2 (Some NumberType); check_type NumberType

		| And | Or ->
			f le1 (Some BooleanType); f le2 (Some BooleanType); check_type BooleanType

		| BitwiseAnd	| BitwiseOr	| BitwiseXor	| LeftShift	| SignedRightShift
		| UnsignedRightShift			| M_atan2			| M_pow		
		-> 	raise (Non_reversable_type ()) 

		| LstCons -> 
			f le1 None; f le2 (Some ListType); check_type ListType

		| LstCat ->
			f le1 (Some ListType); f le2 (Some ListType); check_type ListType

		| StrCat ->
			f le1 (Some StringType); f le2 (Some StringType); check_type StringType

		| _ ->
			raise (Failure "ERROR bi_reverse_type_lexpr_aux unsupported binop"))

	| LLstNth (le1, le2) -> 
		f le1 (Some ListType); f le2 (Some NumberType); check_and_update_type ()

	| LStrNth (le1, le2) -> 
		f le1 (Some StringType); f le2 (Some NumberType); check_and_update_type ()

	| LNone    -> check_type NoneType
	| LUnknown -> raise (Non_reversable_type ()) )

let bi_reverse_type_lexpr pfs_af pfs gamma le le_type : typing_environment option =
	let new_gamma : typing_environment = mk_gamma () in
	try
		bi_reverse_type_lexpr_aux pfs_af pfs gamma new_gamma le le_type;
		Some new_gamma
	with Non_reversable_type () -> None

(* L-Var Check *)
let l_vars_in_spec_check anti_frame spec_lvars le = 
	let af_l_vars = get_symb_state_vars false anti_frame in
	let le_l_vars = get_logic_expression_lvars le in
	let lvars_not_in_spec_or_af = List.filter 
		(fun var ->
				let in_anti_frame = SS.mem var af_l_vars in
				let in_spec = SS.mem var spec_lvars in
				((not in_anti_frame) && (not in_spec))
			) 
		(SS.elements le_l_vars) in
	List.length lvars_not_in_spec_or_af > 0

let create_new_spec () : jsil_n_single_spec =
	let empty_post = init_symb_state () in
	{
		n_pre        = init_symb_state ();
		n_post       = [empty_post];
		n_ret_flag   = Normal;
		n_lvars      = SS.empty;
		n_post_lvars = [];
		n_subst      = Hashtbl.create small_tbl_size
	}