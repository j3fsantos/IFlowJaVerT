open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils

(*************************************)
(** Substitution Functions          **)
(*************************************)

let small_tbl_size = 31

let update_subst1 subst unifier =
	(match unifier with
	 | Some unifier -> List.iter (fun (var, le) -> Hashtbl.replace subst var le) unifier;
	 | None -> ());
	true

let convert_lvars_to_spec_vars symb_vars =
	let subst = Hashtbl.create big_tbl_size in 
	SS.iter (fun var ->
			if (not (is_spec_var_name var) && (is_lvar_name var))
				then (
					let new_var = fresh_spec_var () in
					Hashtbl.add subst var (LVar new_var)
				);
				if (is_abs_loc_name var) then (
					Hashtbl.add subst var (ALoc var)
				)) symb_vars;
	subst
	

let symb_state_lvars_to_svars symb_state_pre symb_state_post =
	let symb_vars_pre = get_symb_state_vars false symb_state_pre in 
	let symb_vars_post = get_symb_state_vars false symb_state_post in 
	let subst = convert_lvars_to_spec_vars (SS.union symb_vars_pre symb_vars_post) in
	let pre = symb_state_substitution symb_state_pre subst true in
	let post = symb_state_substitution symb_state_post subst true in
	(pre, post)

let get_symb_state_lvars symb_state =
	let symb_vars = get_symb_state_vars false symb_state in 
	let symb_lvars = SS.filter(
						fun var -> 
							print_endline ("Spec Var: " ^ var);
							is_lvar_name var)
					symb_vars in 
	symb_lvars 

let update_subst2 subst (unifier1 : (string * jsil_logic_expr) list option)
                        (unifier2 : (string * jsil_logic_expr) list option) p_formulae (* solver *) gamma =
	match unifier1, unifier2 with
	| None, None -> true
	| Some _, None -> update_subst1 subst unifier1
	| None, Some _ -> update_subst1 subst unifier2
	| Some unifier1, Some unifier2 ->
	  print_debug_petar (Printf.sprintf "Unifier lengths: %d, %d" (List.length unifier1) (List.length unifier2));
	  print_debug_petar (Printf.sprintf "U1 : %s\nU2 : %s"
	  	(List.fold_left (fun ac (s, x) -> ac ^ (Printf.sprintf "(%s: %s) " s (JSIL_Print.string_of_logic_expression x false))) "" unifier1)
		(List.fold_left (fun ac (s, x) -> ac ^ (Printf.sprintf "(%s: %s) " s (JSIL_Print.string_of_logic_expression x false))) "" unifier2));
	  let u2vs, u2les = List.split unifier2 in
	  let inter, diff = List.partition (fun (v, _) -> List.mem v u2vs) unifier1 in
	  print_debug_petar (Printf.sprintf "Intersection: %d\tDifference: %d" (List.length inter) (List.length diff));
	  if (List.length inter = 0)
	  	then update_subst1 subst (Some (unifier1 @ unifier2))
		else
		  List.fold_left2 (fun ac (var1, le1) (var2, le2) ->
			if (var1 = var2)
				then
					begin
						if (Pure_Entailment.is_equal le1 le2 p_formulae (* solver *) gamma)
							then (Hashtbl.add subst var1 le1; ac)
							else false
					end
				else
					begin
						Hashtbl.add subst var1 le1;
						Hashtbl.add subst var2 le2;
						ac
					end) true unifier1 unifier2

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

let update_abs_heap_default (heap : symbolic_heap) loc e =
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	match default_val with
	| LUnknown -> LHeap.replace heap loc (fv_list, e)
 	| _ -> raise (Failure "the default value for the fields of a given object cannot be changed once set")


let update_abs_heap (heap : symbolic_heap) loc e_field e_val p_formulae (* solver *) gamma =
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	let unchanged_fv_list, field_val_pair, i_am_sure_the_field_does_not_exist = find_field loc fv_list e_field p_formulae (* solver *) gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist with
	| Some _, _
	| None, true -> LHeap.replace heap loc ((e_field, e_val) :: unchanged_fv_list, default_val)
	| None, false ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e_field false) loc in
			raise (Failure msg)			

let abs_heap_find heap l e p_formulae gamma =
	let fv_list, default_val = try LHeap.find heap l with _ -> [], LUnknown in
	let _, field_val_pair, i_am_sure_the_field_does_not_exist = find_field l fv_list e p_formulae gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist with
	| Some (_, f_val), _ -> f_val
	| None, true -> default_val
	| None, false ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e false) l in
			raise (Failure msg)

let abs_heap_check_field_existence heap l e p_formulae (* solver *) gamma =
	let f_val = abs_heap_find heap l e p_formulae (* solver *) gamma in
	match f_val with
	| LUnknown -> None, None
	| LNone -> None, Some false
	|	_ ->
		if (Pure_Entailment.is_equal f_val LNone p_formulae (* solver *) gamma) then
			(Some f_val, Some false)
			else (if (Pure_Entailment.is_different f_val LNone p_formulae (* solver *) gamma) then
				(Some f_val, Some true)
				else (Some f_val, None))

let abs_heap_delete heap l e p_formulae (* solver *) gamma =
	let fv_list, default_val = try LHeap.find heap l with _ -> [], LUnknown in
	let rest_fv_pairs, del_fv_pair, _ = find_field l fv_list e p_formulae (* solver *) gamma in
	match del_fv_pair with
	| Some (_, _) -> LHeap.replace heap l (rest_fv_pairs, default_val)
	| None -> raise (Failure "Trying to delete an inexistent field")

let merge_heaps heap new_heap p_formulae  gamma =
	print_debug_petar (Printf.sprintf "-------------------------------------------------------------------\n");
	print_debug_petar (Printf.sprintf "-------------INSIDE MERGE HEAPS------------------------------------\n");
	print_debug_petar (Printf.sprintf "-------------------------------------------------------------------\n");

	print_debug_petar (Printf.sprintf "heap: %s\n" (Symbolic_State_Print.string_of_shallow_symb_heap heap false));
	print_debug_petar (Printf.sprintf "pat_heap: %s\n" (Symbolic_State_Print.string_of_shallow_symb_heap new_heap false));
	print_debug_petar (Printf.sprintf "p_formulae: %s\n" (Symbolic_State_Print.string_of_shallow_p_formulae p_formulae false));
	print_debug_petar (Printf.sprintf "gamma: %s\n" (Symbolic_State_Print.string_of_gamma gamma));

	LHeap.iter
		(fun loc (n_fv_list, n_def) ->
			print_debug_petar (Printf.sprintf "Object: %s" loc);
			match n_def with
			| LUnknown
			| LNone ->
				(try
					let fv_list, def = LHeap.find heap loc in
					let rec loop q_fv_list n_fv_list =
						(match n_fv_list with
						| [] -> q_fv_list
						| (le_field, le_val) :: rest_n_fv_list ->
							print_debug_petar (Printf.sprintf "  Field: (%s, %s)" (JSIL_Print.string_of_logic_expression le_field false) (JSIL_Print.string_of_logic_expression le_val false));
							let _, fv_pair, i_am_sure_the_field_does_exist = find_field loc fv_list le_field p_formulae gamma in
							(match fv_pair, i_am_sure_the_field_does_exist with
							| None, true 
							| Some (_, LUnknown), _ -> loop ((le_field, le_val) :: q_fv_list) rest_n_fv_list
							| None, false -> raise (Failure "heaps non-mergeable")
							| Some (f, v), _ -> raise (Failure "heaps non-mergeable"))) in
					let q_fv_list = loop [] n_fv_list in
					LHeap.replace heap loc (q_fv_list @ fv_list, def)
				with Not_found ->
					LHeap.add heap loc (n_fv_list, n_def))
			| _ -> raise (Failure "heaps non-mergeable: the default field is not unknown!!!"))
		new_heap;
	print_debug "Finished merging heaps."


let make_all_different_assertion_from_fvlist (f_list : jsil_logic_expr list) : jsil_logic_assertion list =

	let rec make_all_different_assertion_from_field_and_flist field flist =
		let rec loop flist constraints =
			match flist with
			| [] -> constraints
			| f_name :: rest -> 
				(match List.mem f_name rest with
				| true -> 
						print_debug_petar "Horror: Overlapping resources";
						[ LFalse ]
				| false -> loop rest ((LNot (LEq (field, f_name))) :: constraints)) in
		loop flist [] in

	let rec loop fields_to_cover fields_covered constraints =
		match fields_to_cover with
		| [] -> constraints
		| f_name :: rest ->
			let new_constraints = make_all_different_assertion_from_field_and_flist f_name rest in
			(match new_constraints with
			| [ LFalse ] -> [ LFalse ]
			| _ -> loop rest (f_name :: fields_covered) (new_constraints @ constraints)) in

	let result = loop f_list [] [] in
	
	print_debug_petar
		(Printf.sprintf "Make all different: %s\n" 
			(String.concat " " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) f_list)));
	
	result

let get_heap_well_formedness_constraints heap =
	LHeap.fold
		(fun field (fv_list, _) constraints ->
			(match constraints with
			| [ LFalse ] -> [ LFalse ]
			| _ -> 
  			print_debug_petar (Printf.sprintf "Object: %s" field);
				print_debug_petar "Field-value list:";
				print_debug_petar (String.concat "\n" 
					(List.map (fun (field, value) -> Printf.sprintf "(%s, %s)" 
						(JSIL_Print.string_of_logic_expression field false)
						(JSIL_Print.string_of_logic_expression value false)) fv_list));
				let f_list, _ = List.split fv_list in
  			let new_constraints = make_all_different_assertion_from_fvlist f_list in
  			new_constraints @ constraints))
		heap
		[]

(** 
(** JSIL logic assertions *)
let rec string_of_logic_assertion a escape_string =
**)

let assertion_of_abs_heap h : jsil_logic_assertion list= 
	let make_loc_lexpr loc = 
		if (is_abs_loc_name loc) then ALoc loc else LLit (Loc loc) in 
	
	let rec get_fields fv_list fields_so_far = 
		match fv_list with 
		| [] -> fields_so_far 
		| (f_name, f_val) :: rest -> get_fields rest (f_name :: fields_so_far) in 

	let rec assertions_of_fv_list loc_expr fv_list assertions =
		match fv_list with 
		| [] -> assertions 
		| (f_name, f_val) :: rest ->
			assertions_of_fv_list loc_expr rest ((LPointsTo (loc_expr, f_name, f_val)) :: assertions) in 
	
	LHeap.fold 
		(fun loc (fv_list, def) assertions -> 
			let loc_lexpr = make_loc_lexpr loc in 
			let new_assertions = assertions_of_fv_list loc_lexpr fv_list [] in 
			match def with 
			| LUnknown -> List.append new_assertions assertions
			| LNone -> 
				let fields = get_fields fv_list [] in 
				let ef_assertion = LEmptyFields (loc_lexpr, fields) in 
				List.append (ef_assertion :: new_assertions) assertions) h [] 

let bi_merge_symb_states (symb_state_1 : symbolic_state) (symb_state_2 : symbolic_state)  =
	let heap_1, store_1, pf_1, gamma_1, preds_1  = symb_state_1 in
	let heap_2, store_2, pf_2, gamma_2, preds_2 = symb_state_2 in
 	merge_pfs pf_1 pf_2;
	merge_gammas gamma_1 gamma_2;
	store_merge_left store_1 store_2;
	merge_heaps heap_1 heap_2 pf_1 gamma_1;
	DynArray.append preds_2 preds_1;
	(heap_1, store_1, pf_1, gamma_1, preds_1)
			
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

	let subst = JSIL_Logic_Utils.init_substitution [] in
	let extss = SS.of_list existentials in

	let rec unify_pred_args les pat_les =
		(match les, pat_les with
		| [], [] -> Some subst
		| le :: rest_les, pat_le :: rest_pat_les ->
			print_debug_petar (Printf.sprintf "I am going to test if %s CAN BE equal to %s\n" (JSIL_Print.string_of_logic_expression le false) (JSIL_Print.string_of_logic_expression pat_le false));
			let _, sbt = Simplifications.simplify_pfs_with_subst (DynArray.of_list [ LEq (pat_le, le) ]) gamma in
			(match sbt with
			| Some sbt ->
					(Hashtbl.iter (fun v le -> (match le with
					| LVar v' when ((SS.mem v' extss) && not (SS.mem v extss)) -> 
							Hashtbl.remove sbt v; Hashtbl.add sbt v' (LVar v)
					| _ -> ())) sbt); 
					print_debug_petar (Symbolic_State_Print.string_of_substitution subst);
					print_debug_petar (Symbolic_State_Print.string_of_substitution sbt); 
					Hashtbl.filter_map_inplace (fun v le -> if ((SS.mem v extss && not (Hashtbl.mem subst v))) then Some le else None) sbt;
					Hashtbl.iter (fun v le -> Hashtbl.add subst v le) sbt;
					print_debug_petar (Symbolic_State_Print.string_of_substitution subst);
					print_debug_petar (Symbolic_State_Print.string_of_substitution sbt);
					let s_pfs = pf_substitution pfs subst true in
					let s_le  = lexpr_substitution le subst true in
					let s_pat_le = lexpr_substitution pat_le subst true in
					print_debug_petar (Printf.sprintf "I am going to test if %s CAN BE equal to %s\n" (JSIL_Print.string_of_logic_expression s_le false) (JSIL_Print.string_of_logic_expression s_pat_le false));
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
		(pred_name : string)
		(args      : jsil_logic_expr list)
		(pred_set  : predicate_set)
		(pfs       : pure_formulae)
		(gamma     : typing_environment)
		(spec_vars : SS.t)
		(existentials : string list) =
	let pred_list = preds_to_list pred_set in
	let rec loop pred_list index =
		(match pred_list with
		| [] -> raise (Failure (Printf.sprintf "Predicate %s not found in the predicate set!!!" pred_name))
		| pred :: rest_pred_list ->
			(match (predicate_assertion_equality pred (pred_name, args) pfs gamma spec_vars existentials) with
			| None -> loop rest_pred_list (index + 1)
			| Some subst -> index, subst)) in

	let index, subst = loop pred_list 0 in
	DynArray.delete pred_set index;
	subst
	
let assertions_of_pred_set pred_set = 
	let preds = preds_to_list pred_set in 
	let rec loop preds assertions = 
		match preds with 
		| [] -> assertions 
		| (pred_name, args) :: rest -> 
			loop rest ((LPred (pred_name, args)) :: assertions) in 
	loop preds [] 

let remove_abstract_locations heap store pfs : substitution  =
	let subst = Hashtbl.create small_tbl_size in
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
	assertion_substitution assertion subst true


let string_of_single_spec_table_assertion single_spec =
	let pre = convert_symb_state_to_assertion single_spec.n_pre in
	let post = convert_symb_state_to_assertion (List.hd single_spec.n_post) in
	let flag = (match single_spec.n_ret_flag with | Normal -> "normal" | Error -> "error") in
	(Printf.sprintf "[[ %s ]]\n[[ %s ]]\n%s\n"
	 (JSIL_Print.string_of_logic_assertion pre false)
	 (JSIL_Print.string_of_logic_assertion post false)
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
	let copy_pre  = copy_symb_state s_spec.n_pre in
	let copy_post = List.map copy_symb_state s_spec.n_post in
	{
		n_pre        = copy_pre;
		n_post       = s_spec.n_post;
		n_ret_flag   = s_spec.n_ret_flag;
		n_lvars      = s_spec.n_lvars;
		n_post_lvars = s_spec.n_post_lvars;
		n_subst      = s_spec.n_subst
	}