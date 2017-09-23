open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils



(**
	le -> non - normalised logical expression
	subst -> table mapping variable and logical variable
	gamma -> table mapping logical variables + variables to types

	the store is assumed to contain all the program variables in le
*)
let rec normalise_lexpr ?(store : symbolic_store option) ?(subst : substitution option) 
		(gamma : typing_environment) (le : jsil_logic_expr) =

	let store = Option.default (store_init [] []) store in 
	let subst = Option.default (init_substitution []) subst in 

	let f = normalise_lexpr ~store:store ~subst:subst gamma in

	(* print_debug (Printf.sprintf "Normalising %s" (JSIL_Print.print_lexpr le)); *)

	let start_time = Sys.time() in
	
	try (
	let result = match le with
	| LLit _
	| LNone -> le
	| LVar lvar -> (try Hashtbl.find subst lvar with _ -> LVar lvar)
	| ALoc aloc -> ALoc aloc (* raise (Failure "Unsupported expression during normalization: ALoc") Why not ALoc aloc? *)
	| PVar pvar ->
		(try Hashtbl.find store pvar with
			| _ ->
				(let new_lvar = fresh_lvar () in 
				store_put store pvar (LVar new_lvar); 
				Hashtbl.add subst pvar (LVar new_lvar);
				LVar new_lvar))

	| LBinOp (le1, bop, le2) ->
		let nle1 = f le1 in
		let nle2 = f le2 in
		(match nle1, nle2 with
			| LLit lit1, LLit lit2 ->
				let lit = JSIL_Interpreter.evaluate_binop bop (Literal lit1) (Literal lit2) (Hashtbl.create 1) in
					LLit lit
			| _, _ -> LBinOp (nle1, bop, nle2))

	| LUnOp (uop, le1) ->
		let nle1 = f le1 in
		(match nle1 with
			| LLit lit1 ->
				let lit = JSIL_Interpreter.evaluate_unop uop lit1 in
				LLit lit
			| _ -> LUnOp (uop, nle1))

	| LTypeOf (le1) ->
		let nle1 = f le1 in
		(match nle1 with
			| LLit llit -> LLit (Type (evaluate_type_of llit))
			| LNone -> raise (Failure "Illegal Logic Expression: TypeOf of None")
			| LVar lvar ->
				(try LLit (Type (Hashtbl.find gamma lvar)) with _ -> LTypeOf (LVar lvar))
					(* raise (Failure (Printf.sprintf "Logical variables always have a type, in particular: %s." lvar))) *)
			| ALoc _ -> LLit (Type ObjectType)
			| PVar _ -> raise (Failure "This should never happen: program variable in normalised expression")
			| LBinOp (_, _, _)
			| LUnOp (_, _) -> LTypeOf (nle1)
			| LTypeOf _ -> LLit (Type TypeType)
			| LEList _ -> LLit (Type ListType)
			| LLstNth (list, index) ->
				(match list, index with
					| LLit (LList list), LLit (Num n) when (Utils.is_int n) ->
						let lit_n = (try List.nth list (int_of_float n) with _ ->
							raise (Failure "List index out of bounds")) in
						LLit (Type (evaluate_type_of lit_n))
					| LLit (LList list), LLit (Num n) -> raise (Failure "Non-integer list index")
					| LEList list, LLit (Num n) when (Utils.is_int n) ->
						let le_n = (try List.nth list (int_of_float n) with _ ->
							raise (Failure "List index out of bounds")) in
						f (LTypeOf le_n)
					| LEList list, LLit (Num n) -> raise (Failure "Non-integer list index")
					| _, _ -> LTypeOf (nle1))
			| LStrNth (str, index) ->
				(match str, index with
					| LLit (String s), LLit (Num n) when (Utils.is_int n) ->
						let _ = (try (String.get s (int_of_float n)) with _ ->
							raise (Failure "String index out of bounds")) in
						LLit (Type StringType)
					| LLit (String s), LLit (Num n) -> raise (Failure "Non-integer string index")
					| _, _ -> LTypeOf (nle1)))

	| LEList le_list ->
		let n_le_list = List.map (fun le -> f le) le_list in
		let all_literals, lit_list =
			List.fold_left
				(fun (ac, list) le ->
					match le with
					| LLit lit -> (ac, (list @ [ lit ]))
					| _ -> (false, list))
				(true, [])
				n_le_list in
		if (all_literals)
		then LLit (LList lit_list)
		else LEList n_le_list
		
	| LESet le_list ->
		let n_le_list = List.map (fun le -> f le) le_list in
		LESet n_le_list
		
	| LSetUnion le_list ->
		(* this can be better!!!! *)
		let n_le_list = List.map (fun le -> f le) le_list in
		LSetUnion n_le_list
		
		
	| LSetInter le_list ->
		let n_le_list = List.map (fun le -> f le) le_list in
		LSetInter n_le_list

	| LLstNth (le1, le2) ->
		let nle1 = f le1 in
		let nle2 = f le2 in
		(match nle1, nle2 with
			| LLit (LList list), LLit (Num n) when (Utils.is_int n) -> 
					(try LLit (List.nth list (int_of_float n)) with _ ->
						raise (Failure "List index out of bounds"))
			| LLit (LList list), LLit (Num n) -> raise (Failure "Non-integer list index")
			| LEList list, LLit (Num n) when (Utils.is_int n) -> 
					let le = (try (List.nth list (int_of_float n)) with _ ->
						raise (Failure "List index out of bounds")) in
					f le
			| LEList list, LLit (Num n) -> raise (Failure "Non-integer list index")
			| _, _ -> LLstNth (nle1, nle2))

	| LStrNth (le1, le2) ->
		let nle1 = f le1 in
		let nle2 = f le2 in
		(match nle1, nle2 with
			| LLit (String s), LLit (Num n) ->
				(try LLit (String (String.make 1 (String.get s (int_of_float n))))
				with _ -> raise (Failure "String index out of bounds"))
			| _, _ -> LStrNth (nle1, nle2)) in
		let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "normalise_lexpr" (end_time -. start_time);
		(* print_debug_petar (Printf.sprintf "normalise_lexpr: %f : %s -> %s" 
			(end_time -. start_time) (JSIL_Print.string_of_logic_expression le false) 
			(JSIL_Print.string_of_logic_expression result false)); *)
		result)
	with
	| Failure msg -> let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "normalise_lexpr" (end_time -. start_time);
		print_debug_petar (Printf.sprintf "normalise_lexpr: %f : %s -> Failure" 
			(end_time -. start_time) (JSIL_Print.string_of_logic_expression le));
		raise (Failure msg)


(*************************************)
(** Substitution Functions          **)
(*************************************)


(**
  find_field fv_list e p_formulae = fv_list', (e1, e2)
	   st:
		    fv_list = fv_list' U (e1, e2)
				and
				pure_formulae |=

*)
let find_field loc fv_list e p_formulae gamma =
	let rec find_field_rec fv_list traversed_fv_list i_am_sure_the_field_does_not_exist =
		match fv_list with
		| [] -> traversed_fv_list, None, i_am_sure_the_field_does_not_exist
		| (e_field, e_value) :: rest ->
			(if (Pure_Entailment.is_equal e e_field p_formulae gamma)
				then traversed_fv_list @ rest, Some (e_field, e_value), false
				else
					(if (i_am_sure_the_field_does_not_exist && (Pure_Entailment.is_different e e_field p_formulae gamma))
						then find_field_rec rest ((e_field, e_value) :: traversed_fv_list) true
						else find_field_rec rest ((e_field, e_value) :: traversed_fv_list) false)) in
	find_field_rec fv_list [] true

let update_abs_heap_default (heap : symbolic_heap) loc dom =
	let fv_list, domain = try LHeap.find heap loc with _ -> [], None in
	match domain with
	| None -> LHeap.replace heap loc (fv_list, dom)
 	| _ -> raise (Failure "the default value for the fields of a given object cannot be changed once set")


let heap_domain_with_subst (heap : symbolic_heap) (subst : substitution) : string list = 
	
	let rec loop locs matched_abs_locs free_abs_locs concrete_locs =
		match locs with
		| [] -> concrete_locs @ matched_abs_locs @ free_abs_locs
		| loc :: rest_locs ->
			if (is_abs_loc_name loc)
				then (
					if (Hashtbl.mem subst loc)
						then loop rest_locs (loc :: matched_abs_locs) free_abs_locs concrete_locs
						else loop rest_locs matched_abs_locs (loc :: free_abs_locs) concrete_locs)
				else loop rest_locs matched_abs_locs free_abs_locs (loc :: concrete_locs) in

	loop (SS.elements (heap_domain heap)) [] [] []


(*************************************)
(** Symbolic Heap Functions         **)
(*************************************)

let update_abs_heap (heap : symbolic_heap) (loc : string) (e_field : jsil_logic_expr) 
		(e_val : jsil_logic_expr) (p_formulae : pure_formulae) (gamma : typing_environment) =
	let fv_list, domain = try LHeap.find heap loc with _ -> [], None in
	let unchanged_fv_list, field_val_pair, i_am_sure_the_field_does_not_exist = find_field loc fv_list e_field p_formulae gamma in

	match field_val_pair, i_am_sure_the_field_does_not_exist with
	| Some _, _
	| None, true -> 
		let new_domain = (match domain with 
		| None -> None 
		| Some domain -> 
			print_debug (Printf.sprintf "UAH: My domain is: %s" (JSIL_Print.string_of_logic_expression domain));
			let new_domain = LSetUnion [ domain; LESet [ e_field ]] in 
			let new_domain = normalise_lexpr gamma new_domain in
			let new_domain = Simplifications.reduce_expression_no_store gamma p_formulae new_domain in 
			Some new_domain) in 
		LHeap.replace heap loc ((e_field, e_val) :: unchanged_fv_list, new_domain)
	| None, false ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e_field) loc in
			raise (Failure msg)			

let abs_heap_find (heap : symbolic_heap) (l : string) (e : jsil_logic_expr) 
		(p_formulae : pure_formulae) (gamma : typing_environment) =
	let fv_list, domain = try LHeap.find heap l with _ -> [], None in
	let _, field_val_pair, i_am_sure_the_field_does_not_exist = find_field l fv_list e p_formulae gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist, domain with
	| Some (_, f_val), _, _-> f_val
	| _, _, Some domain -> 
		let a_set_inclusion = LNot (LSetMem (e, domain)) in 
		if (Pure_Entailment.check_entailment SS.empty (pfs_to_list p_formulae) [ a_set_inclusion ] gamma) 
			then LNone
			else (
				let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e) l in
				raise (Failure msg)
			)
	| _ -> 
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e) l in
			raise (Failure msg)

let abs_heap_check_field_existence (heap : symbolic_heap) (l : string) (e : jsil_logic_expr)
		(p_formulae : pure_formulae) (gamma : typing_environment) =
	let f_val = abs_heap_find heap l e p_formulae gamma in
	match f_val with
	| LNone -> None, Some false
	|	_ ->
		if (Pure_Entailment.is_equal f_val LNone p_formulae gamma) then
			(Some f_val, Some false)
			else (if (Pure_Entailment.is_different f_val LNone p_formulae gamma) then
				(Some f_val, Some true)
				else (Some f_val, None))

let abs_heap_delete (heap : symbolic_heap) (l : string) (e : jsil_logic_expr) 
		(p_formulae : pure_formulae) (gamma : typing_environment) =
	let fv_list, default_val = try LHeap.find heap l with _ -> [], None in
	let rest_fv_pairs, del_fv_pair, _ = find_field l fv_list e p_formulae gamma in
	match del_fv_pair with
	| Some (_, _) -> LHeap.replace heap l (rest_fv_pairs, default_val)
	| None -> raise (Failure "Trying to delete an inexistent field")


let combine_domains (domain_l : jsil_logic_expr option) (domain_r : jsil_logic_expr option) (gamma : typing_environment) = 
	match domain_l, domain_r with 
	| None, None -> None
	| None, Some domain 
	| Some domain, None -> Some domain 
	| Some set1, Some set2 -> 
		let set = LSetUnion [ set1; set2 ] in
		let set = normalise_lexpr gamma set in  
		Some set 

let merge_heaps (heap : symbolic_heap) (new_heap : symbolic_heap) (p_formulae : pure_formulae) 
			(gamma : typing_environment) =
	print_debug_petar (Printf.sprintf "-------------------------------------------------------------------\n");
	print_debug_petar (Printf.sprintf "-------------INSIDE MERGE HEAPS------------------------------------\n");
	print_debug_petar (Printf.sprintf "-------------------------------------------------------------------\n");

	print_debug_petar (Printf.sprintf "heap: %s\n" (Symbolic_State_Print.string_of_symb_heap heap));
	print_debug_petar (Printf.sprintf "pat_heap: %s\n" (Symbolic_State_Print.string_of_symb_heap new_heap));
	print_debug_petar (Printf.sprintf "p_formulae: %s\n" (Symbolic_State_Print.string_of_pfs p_formulae));
	print_debug_petar (Printf.sprintf "gamma: %s\n" (Symbolic_State_Print.string_of_gamma gamma));

	LHeap.iter
		(fun loc (n_fv_list, n_domain) ->
			print_debug_petar (Printf.sprintf "Object: %s" loc);
			try 
				let fv_list, domain = LHeap.find heap loc in				
				LHeap.replace heap loc (n_fv_list @ fv_list, (combine_domains domain n_domain gamma))
			with Not_found -> LHeap.add heap loc (n_fv_list, n_domain))
		new_heap;
	print_debug "Finished merging heaps."

(** 
(** JSIL logic assertions *)
let rec string_of_logic_assertion a escape_string =
**)

let assertion_of_abs_heap (h : symbolic_heap) : jsil_logic_assertion list= 
	let make_loc_lexpr loc = 
		if (is_abs_loc_name loc) then ALoc loc else LLit (Loc loc) in 
	
	let rec assertions_of_object (loc, (fv_list, set)) =
	 	let le_loc = make_loc_lexpr loc in
		let fv_assertions = List.map (fun (field, value) -> LPointsTo (le_loc, field, value)) fv_list in 
		Option.map_default (fun set -> (LEmptyFields (le_loc, set)) :: fv_assertions) fv_assertions set in 

	List.concat (List.map assertions_of_object (heap_to_list h))

			
(*************************************)
(** Store functions                 **)
(*************************************)

let assertions_of_abs_store s : jsil_logic_assertion list= 
	Hashtbl.fold
		(fun x le assertions -> 
			(LEq (PVar x, le)) :: assertions) s []


(*************************************)
(** Gamma functions                 **)
(*************************************)

let assertions_of_gamma gamma : jsil_logic_assertion= 
	let le_type_pairs = 
		Hashtbl.fold
			(fun x t pairs -> 
				(if (is_lvar_name x) 
					then (LVar x, t) :: pairs
					else (PVar x, t) :: pairs)) gamma [] in 
	LTypes le_type_pairs 


(*************************************)
(** Predicate functions             **)
(*************************************)

let predicate_assertion_equality pred pat_pred pfs gamma (spec_vars : SS.t) (existentials : string list) =
	print_debug_petar (Printf.sprintf "Entering predicate_assertion_equality.\n");

	let subst = init_substitution [] in
	let extss = SS.of_list existentials in

	let rec unify_pred_args les pat_les =
		(match les, pat_les with
		| [], [] -> Some subst
		| le :: rest_les, pat_le :: rest_pat_les ->
			print_debug_petar (Printf.sprintf "I am going to test if %s CAN BE equal to %s\n" (JSIL_Print.string_of_logic_expression le) (JSIL_Print.string_of_logic_expression pat_le));
			let _, sbt = Simplifications.simplify_pfs_with_subst (DynArray.of_list [ LEq (pat_le, le) ]) gamma in
			(match sbt with
			| Some sbt ->
					(Hashtbl.iter (fun v le -> (match le with
					| LVar v' when ((SS.mem v' extss) && not (SS.mem v extss)) -> 
							Hashtbl.remove sbt v; Hashtbl.add sbt v' (LVar v)
					| _ -> ())) sbt); 
					Hashtbl.filter_map_inplace (fun v le -> if ((SS.mem v extss && not (Hashtbl.mem subst v))) then Some le else None) sbt;
					Hashtbl.iter (fun v le -> Hashtbl.add subst v le) sbt;
					let s_pfs = pfs_substitution subst true pfs in
					let s_le  = lexpr_substitution subst true le in
					let s_pat_le = lexpr_substitution subst true pat_le in
					print_debug_petar (Printf.sprintf "I am going to test if %s CAN BE equal to %s\n" (JSIL_Print.string_of_logic_expression s_le) (JSIL_Print.string_of_logic_expression s_pat_le));
					if (Pure_Entailment.is_equal s_le s_pat_le s_pfs gamma) 
						then unify_pred_args rest_les rest_pat_les
						else None
			| None -> None)) in

	match pred, pat_pred with
	| (name, les), (pat_name, pat_les) ->
		if (name = pat_name) then
			unify_pred_args les pat_les
		else None
	| _, _ -> raise (Failure "predicate_assertion_equality: FATAL ERROR")


let subtract_pred 
		(pred_name    : string)
		(args         : jsil_logic_expr list)
		(pred_set     : predicate_set)
		(pfs          : pure_formulae)
		(gamma        : typing_environment)
		(spec_vars    : SS.t)
		(existentials : string list) 
		(delete_pred  : bool) : substitution option =
	let pred_list = preds_to_list pred_set in
	let rec loop pred_list index =
		(match pred_list with
		| [] -> None
		| pred :: rest_pred_list ->
			(match (predicate_assertion_equality pred (pred_name, args) pfs gamma spec_vars existentials) with
			| None -> loop rest_pred_list (index + 1)
			| Some subst -> Some (index, subst))) in

	match loop pred_list 0 with 
	| None -> None 
	| Some (index, subst) -> 
		if(delete_pred) then DynArray.delete pred_set index; Some subst

	
let assertions_of_pred_set pred_set = 
	let preds = preds_to_list pred_set in 
	let rec loop preds assertions = 
		match preds with 
		| [] -> assertions 
		| (pred_name, args) :: rest -> 
			loop rest ((LPred (pred_name, args)) :: assertions) in 
	loop preds [] 


(*************************************)
(** Symbolic State functions        **)
(*************************************)


let get_symb_state_lvars symb_state =
	let symb_vars = ss_lvars symb_state in 
	let symb_lvars = SS.filter(
						fun var -> 
							(* print_normal ("Spec Var: " ^ var); *)
							is_lvar_name var)
					symb_vars in 
	symb_lvars 

let remove_abstract_locations (heap : symbolic_heap) (store : symbolic_store) (pfs : pure_formulae) : substitution  =
	let subst = init_substitution [] in
	LHeap.iter 
		(fun loc (fv_list, def) -> 
			(try 
				Hashtbl.find subst loc; ()
			with Not_found -> 
				(if (is_abs_loc_name loc) then
					let s_loc = store_get_rev store (ALoc loc) in
					(match s_loc with
					| Some l ->
						Hashtbl.add subst loc (PVar l)
					| None -> 
						let p_loc = Simplifications.find_me_in_the_pi pfs (ALoc loc) in
						match p_loc with 
						| Some l -> 
							Hashtbl.add subst loc (LVar l)
						| None -> 
							let n_lvar = fresh_lvar () in 
							Hashtbl.add subst loc (LVar n_lvar))
				)
			)
		) heap;
	subst

let convert_symb_state_to_assertion (symb_state : symbolic_state) : jsil_logic_assertion = 
	let heap, store, pfs, gamma, preds = symb_state in
	let subst = remove_abstract_locations heap store pfs in
	let heap_assert = assertion_of_abs_heap heap in
	let store_assert = assertions_of_abs_store store in
	let gamma_assert = assertions_of_gamma gamma in
	let pure_assert = DynArray.to_list pfs in
	let assertions = heap_assert @ store_assert @ pure_assert @ [gamma_assert] in
	let assertion = List.fold_left (fun ac assertion -> 
						if (ac = LEmp) then assertion else LStar(ac , assertion)) 
		LEmp 
		assertions in
	asrt_substitution subst true assertion 


let merge_symb_states
		(symb_state_l : symbolic_state)
		(symb_state_r : symbolic_state)
		(subst : substitution) : symbolic_state =
	(* Printf.printf "gamma_r: %s\n." (Symbolic_State_Print.string_of_gamma (get_gamma symb_state_r)); *)
	let aux_symb_state = (ss_copy symb_state_r) in
	let symb_state_r = ss_substitution subst false aux_symb_state in
	let heap_l, store_l, pf_l, gamma_l, preds_l = symb_state_l in
	let heap_r, store_r, pf_r, gamma_r, preds_r = symb_state_r in
	pfs_merge pf_l pf_r;
	merge_gammas gamma_l gamma_r;
	merge_heaps heap_l heap_r pf_l gamma_l;
	DynArray.append preds_r preds_l;
	print_debug ("Finished merge_symb_states");
	(heap_l, store_l, pf_l, gamma_l, preds_l)


(**
  * Check if the pfs of symb_state are compatible with those of pat_symb_state 
  * when they are connected via subst *)
let compatible_pfs 
	(symb_state     : symbolic_state) 
	(pat_symb_state : symbolic_state) 
	(subst          : substitution) : bool =
	
	let pfs = ss_pfs symb_state in
	let gamma = ss_gamma symb_state in
	let pat_pfs = ss_pfs pat_symb_state in
	let pat_gamma = ss_gamma pat_symb_state in
	
	let pat_pfs = pfs_substitution subst false pat_pfs in
	let pat_gamma = gamma_substitution pat_gamma subst false in
	let gamma = gamma_copy gamma in
	merge_gammas gamma pat_gamma;
	
	let pf_list = (pfs_to_list pat_pfs) @ (pfs_to_list pfs) in
	let is_sat = Pure_Entailment.check_satisfiability pf_list gamma in

	(if (not is_sat) then 
		print_debug (Printf.sprintf "These pfs are not compatible: %s"
			(String.concat "\n" (List.map (fun a -> JSIL_Print.string_of_logic_assertion a) pf_list)))
	); 

	is_sat 


let merge_symb_state_with_posts  
	(proc              : jsil_procedure)
	(spec              : jsil_n_single_spec) 
	(caller_symb_state : symbolic_state) 
	(symb_state_frame  : symbolic_state_frame) : (symbolic_state * jsil_return_flag * jsil_logic_expr) list = 

	let framed_heap, framed_preds, subst, pf_discharges, new_gamma = symb_state_frame in 
	let symb_state_frame = ss_replace_heap  caller_symb_state framed_heap in
	let symb_state_frame = ss_replace_preds symb_state_frame framed_preds in
	let symb_state_frame = ss_replace_gamma symb_state_frame new_gamma in
	
	let ret_flag = spec.n_ret_flag in
	let ret_var  = proc_get_ret_var proc ret_flag in

	let f_post (post : symbolic_state) : (symbolic_state * jsil_return_flag * jsil_logic_expr) list =
		let post_makes_sense = compatible_pfs symb_state_frame post subst in
		if (post_makes_sense) then (
			let new_symb_state = ss_copy symb_state_frame in
			let new_symb_state = merge_symb_states new_symb_state post subst in
			ss_extend_pfs new_symb_state (pfs_of_list pf_discharges);
			let ret_lexpr      = store_get_safe (ss_store post) ret_var in
			let ret_lexpr      =
				Option.map_default (fun x -> JSIL_Logic_Utils.lexpr_substitution subst false x)
					(print_debug_petar "Warning: Store return variable not present; implicitly empty"; LLit Empty) ret_lexpr in
			[ (new_symb_state, ret_flag, ret_lexpr) ]
		) else [] in 

	List.concat (List.map f_post spec.n_post) 
			

let enrich_pure_part 
	(symb_state     : symbolic_state)
	(symb_state_pat : symbolic_state)
	(subst          : substitution) : bool * symbolic_state =
	
	let pre_gamma = gamma_copy (ss_gamma symb_state_pat)     in
	let pre_pfs   = pfs_copy (ss_pfs symb_state_pat)         in	
	let pfs       = pfs_substitution subst false pre_pfs     in
	let gamma     = gamma_substitution pre_gamma subst false in
	
	merge_gammas gamma (ss_gamma symb_state);
	pfs_merge pfs (ss_pfs symb_state);
	let store          = store_copy (ss_store symb_state) in
	let heap           = ss_heap symb_state               in
	let preds          = ss_preds symb_state              in
	let new_symb_state = (heap, store, pfs, gamma, preds) in
	
	let is_sat = Pure_Entailment.check_satisfiability (ss_pfs_list new_symb_state) (ss_gamma new_symb_state) in
	(is_sat, new_symb_state)


(*************************************)
(** Spec Table Functions            **)
(*************************************)

let string_of_single_spec_table_assertion single_spec =
	let pre = convert_symb_state_to_assertion single_spec.n_pre in
	let post = convert_symb_state_to_assertion (List.hd single_spec.n_post) in
	let flag = (match single_spec.n_ret_flag with | Normal -> "normal" | Error -> "error") in
	(Printf.sprintf "[[ %s ]]\n[[ %s ]]\n%s\n"
	 (JSIL_Print.string_of_logic_assertion pre)
	 (JSIL_Print.string_of_logic_assertion post)
	 flag)

let string_of_n_single_spec_assertion spec = 
	List.fold_left(
		fun ac single_spec ->
			let single_spec_str = string_of_single_spec_table_assertion single_spec in
			ac ^ single_spec_str
	) "" spec.n_proc_specs

let string_of_n_spec_table_assertions spec_table procs_to_verify =
	Hashtbl.fold
		(fun spec_name spec ac ->
			if (List.mem spec_name procs_to_verify) then  
				let spec_str =  string_of_n_single_spec_assertion spec in
				ac ^ "\n" ^ spec_name ^ "\n----------\n" ^ spec_str
			else 
				ac )
		spec_table
		""

(*************************************)
(** Normalised Spec functions       **)
(*************************************)
let copy_single_spec s_spec =
	let copy_pre  = ss_copy s_spec.n_pre in
	let copy_post = List.map ss_copy s_spec.n_post in
	{
		n_pre              = copy_pre;
		n_post             = s_spec.n_post;
		n_ret_flag         = s_spec.n_ret_flag;
		n_lvars            = s_spec.n_lvars; 
		n_subst            = s_spec.n_subst; 
		n_unification_plan = s_spec.n_unification_plan
	}
	
(*************************************)
(** Garbage collection              **)
(*************************************)

let get_locs_symb_state symb_state =
	let heap, store, pfs, gamma, preds = symb_state in 
	let lheap  = heap_alocs  heap  in
	let lstore = store_alocs store in
	let lpfs   = pfs_alocs   pfs   in
	let lpreds = preds_alocs preds in
	SS.union lheap (SS.union lstore (SS.union lpfs lpreds))
	
let collect_garbage (symb_state : symbolic_state) = 
	let heap, store, pfs, gamma, preds = symb_state in
	let dangling_locations = 	LHeap.fold
		(fun loc (fv_list, default) locs ->
			match (is_abs_loc_name loc), default, fv_list with
			| true, None, [] 
			| true, Some (LESet []), [] -> SS.add loc locs
			| _ -> locs
  	)
		heap
		SS.empty in
	if (dangling_locations = SS.empty) then symb_state else (
	let ss_vars = get_locs_symb_state symb_state in
	let collectable_locs = SS.diff dangling_locations ss_vars in
	SS.iter (fun loc -> LHeap.remove heap loc) collectable_locs;
		print_debug (Printf.sprintf "GCOL: Found locations: %s"
			(String.concat ", " (SS.elements ss_vars)));
		print_debug (Printf.sprintf "GCOL: Dangling locations: %s"
			(String.concat ", " (SS.elements dangling_locations)));
		print_debug (Printf.sprintf "GCOL: Collectable locations: %s"
			(String.concat ", " (SS.elements collectable_locs)));
	symb_state)