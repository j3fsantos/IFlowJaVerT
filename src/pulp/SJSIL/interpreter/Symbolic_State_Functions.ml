open JSIL_Syntax
open JSIL_Memory_Model
open JSIL_Logic_Utils
open Symbolic_State_Basics

(*************************************)
(** Substitution Functions          **)
(*************************************)

let small_tbl_size = 31

let update_subst1 subst unifier =
	(match unifier with
	 | Some unifier -> List.iter (fun (var, le) -> Hashtbl.add subst var le) unifier;
	 | None -> ());
	true


let update_subst2 subst (unifier1 : (string * jsil_logic_expr) list option)
                        (unifier2 : (string * jsil_logic_expr) list option) p_formulae solver gamma =
	match unifier1, unifier2 with
	| None, None -> true
	| Some _, None -> update_subst1 subst unifier1
	| None, Some _ -> update_subst1 subst unifier2
	| Some unifier1, Some unifier2 ->
	  print_debug (Printf.sprintf "Unifier lengths: %d, %d" (List.length unifier1) (List.length unifier2));
	  print_debug (Printf.sprintf "U1 : %s\nU2 : %s"
	  	(List.fold_left (fun ac (s, x) -> ac ^ (Printf.sprintf "(%s: %s) " s (JSIL_Print.string_of_logic_expression x false))) "" unifier1)
		(List.fold_left (fun ac (s, x) -> ac ^ (Printf.sprintf "(%s: %s) " s (JSIL_Print.string_of_logic_expression x false))) "" unifier2));
	  let u2vs, u2les = List.split unifier2 in
	  let inter, diff = List.partition (fun (v, _) -> List.mem v u2vs) unifier1 in
	  print_debug (Printf.sprintf "Intersection: %d\tDifference: %d" (List.length inter) (List.length diff));
	  if (List.length inter = 0)
	  	then update_subst1 subst (Some (unifier1 @ unifier2))
		else
		  List.fold_left2 (fun ac (var1, le1) (var2, le2) ->
			if (var1 = var2)
				then
					begin
						if (Pure_Entailment.is_equal le1 le2 p_formulae solver gamma)
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
let find_field loc fv_list e p_formulae solver gamma =
	(* Printf.printf "Searching for field: %s\n" (JSIL_Print.string_of_logic_expression e false); *)
	let rec find_field_rec fv_list traversed_fv_list i_am_sure_the_field_does_not_exist =
		match fv_list with
		| [] -> traversed_fv_list, None, i_am_sure_the_field_does_not_exist
		| (e_field, e_value) :: rest ->
			(if (Pure_Entailment.is_equal e e_field p_formulae solver gamma)
				then traversed_fv_list @ rest, Some (e_field, e_value), false
				else
					(if (i_am_sure_the_field_does_not_exist && (Pure_Entailment.is_different e e_field p_formulae solver gamma))
						then find_field_rec rest ((e_field, e_value) :: traversed_fv_list) true
						else find_field_rec rest ((e_field, e_value) :: traversed_fv_list) false)) in
	find_field_rec fv_list [] true

let update_abs_heap_default (heap : symbolic_heap) loc e =
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	match default_val with
	| LUnknown -> LHeap.replace heap loc (fv_list, e)
 	| _ -> raise (Failure "the default value for the fields of a given object cannot be changed once set")


let update_abs_heap (heap : symbolic_heap) loc e_field e_val p_formulae solver gamma =
	(* Printf.printf "Update Abstract Heap\n"; *)
	let fv_list, default_val = try LHeap.find heap loc with _ -> [], LUnknown in
	let unchanged_fv_list, field_val_pair, i_am_sure_the_field_does_not_exist = find_field loc fv_list e_field p_formulae solver gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist with
	| Some _, _
	| None, true -> LHeap.replace heap loc ((e_field, e_val) :: unchanged_fv_list, default_val)
	| None, false ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e_field false) loc in
			raise (Failure msg)


let abs_heap_find heap l e p_formulae solver gamma =
	let fv_list, default_val = try LHeap.find heap l with _ -> [], LUnknown in
	let _, field_val_pair, i_am_sure_the_field_does_not_exist = find_field l fv_list e p_formulae solver gamma in
	match field_val_pair, i_am_sure_the_field_does_not_exist with
	| Some (_, f_val), _ -> f_val
	| None, true -> default_val
	| None, false ->
		let msg = Printf.sprintf "Cannot decide if %s exists in object %s" (JSIL_Print.string_of_logic_expression e false) l in
			raise (Failure msg)

let abs_heap_check_field_existence heap l e p_formulae solver gamma =
	let f_val = abs_heap_find heap l e p_formulae solver gamma in
	match f_val with
	| LUnknown -> None
	| LNone -> Some false
	|	_ ->
		if (Pure_Entailment.is_equal f_val LNone p_formulae solver gamma) then
			(Some false)
			else (if (Pure_Entailment.is_different f_val LNone p_formulae solver gamma) then
				(Some true)
				else None)

let abs_heap_delete heap l e p_formulae solver gamma =
	let fv_list, default_val = try LHeap.find heap l with _ -> [], LUnknown in
	let rest_fv_pairs, del_fv_pair, _ = find_field l fv_list e p_formulae solver gamma in
	match del_fv_pair with
	| Some (_, _) -> LHeap.replace heap l (rest_fv_pairs, default_val)
	| None -> raise (Failure "Trying to delete an inexistent field")

let merge_heaps heap new_heap p_formulae solver gamma =
    print_debug (Printf.sprintf "-------------------------------------------------------------------\n");
	print_debug (Printf.sprintf "-------------INSIDE MERGE HEAPS------------------------------------\n");
	print_debug (Printf.sprintf "-------------------------------------------------------------------\n");

	print_debug (Printf.sprintf "heap: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap heap false));
	print_debug (Printf.sprintf "pat_heap: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap new_heap false));
	print_debug (Printf.sprintf "p_formulae: %s\n" (JSIL_Memory_Print.string_of_shallow_p_formulae p_formulae false));
	print_debug (Printf.sprintf "gamma: %s\n" (JSIL_Memory_Print.string_of_gamma gamma));

	LHeap.iter
		(fun loc (n_fv_list, n_def) ->
			match n_def with
			| LUnknown
			| LNone ->
				(try
					let fv_list, def = LHeap.find heap loc in
					let rec loop q_fv_list n_fv_list =
						(match n_fv_list with
						| [] -> q_fv_list
						| (le_field, le_val) :: rest_n_fv_list ->
							(* Printf.printf "le_field: %s, le_val: %s\n" (JSIL_Print.string_of_logic_expression le_field false) (JSIL_Print.string_of_logic_expression le_val false); *)
							let _, fv_pair, i_am_sure_the_field_does_exist = find_field loc fv_list le_field p_formulae solver gamma in
							(match fv_pair, i_am_sure_the_field_does_exist with
							| None, true -> loop ((le_field, le_val) :: q_fv_list) rest_n_fv_list
							| None, false ->
								(* Printf.printf "i_am_sure_the_field_does_exist: %b\n" i_am_sure_the_field_does_exist; *)
								raise (Failure "heaps non-mergeable")
							| Some (f, v), _ ->
								(* Printf.printf "i_am_sure_the_field_does_exist: %b, (%s, %s)\n"
									i_am_sure_the_field_does_exist (JSIL_Print.string_of_logic_expression f false) (JSIL_Print.string_of_logic_expression v false); *)
								raise (Failure "heaps non-mergeable"))) in
					let q_fv_list = loop [] n_fv_list in
					LHeap.replace heap loc (q_fv_list @ fv_list, def)
				with Not_found ->
					LHeap.add heap loc (n_fv_list, n_def))
			| _ -> raise (Failure "heaps non-mergeable: the default field is not unknown!!!"))
		new_heap

	(* Printf.printf "-------------------------------------------------------------------\n";
	Printf.printf "-------------DONE MERGING HEAPS------------------------------------\n";
	Printf.printf "-------------------------------------------------------------------\n";

	Printf.printf "heap: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap heap false);
	Printf.printf "pat_heap: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap new_heap false);
	Printf.printf "p_formulae: %s\n" (JSIL_Memory_Print.string_of_shallow_p_formulae p_formulae false);
	Printf.printf "gamma: %s\n" (JSIL_Memory_Print.string_of_gamma gamma);

	Printf.printf "-------------------------------------------------------------------\n";
	Printf.printf "-------------NOW WE CONTINUE --------------------------------------\n";
	Printf.printf "-------------------------------------------------------------------\n" *)


let make_all_different_assertion_from_fvlist fv_list : jsil_logic_assertion list =

	let rec make_all_different_assertion_from_field_and_fvlist field fv_list =
		let rec loop fv_list constraints =
			match fv_list with
			| [] -> constraints
			| (f_name, f_val) :: rest ->
				loop rest ((LNot (LEq (field, f_name))) :: constraints) in
		loop fv_list [] in

	let rec loop fields_to_cover fields_covered constraints =
		match fields_to_cover with
		| [] -> constraints
		| (f_name, f_val) :: rest ->
			let new_constraints = make_all_different_assertion_from_field_and_fvlist f_val (fields_covered @ rest) in
			loop rest ((f_name, f_val) :: fields_covered) (new_constraints @ constraints) in

	loop fv_list [] []


let get_heap_well_formedness_constraints heap =
	LHeap.fold
		(fun _ (fv_list, _) constraints ->
			let new_constraints = make_all_different_assertion_from_fvlist fv_list in
			new_constraints @ constraints)
		heap
		[]

(*************************************)
(** Predicate functions             **)
(*************************************)

let predicate_assertion_equality pred pat_pred pfs solver gamma spec_vars =
	print_debug (Printf.sprintf "Entering predicate_assertion_equality.\n");

	let spec_vars_str = List.fold_left (fun ac v -> if (ac = "") then v else (ac ^ ", " ^ v)) "" spec_vars in
	let subst = JSIL_Logic_Utils.init_substitution [] in

	let rec unify_pred_args les pat_les =
		(match les, pat_les with
		| [], [] -> Some subst
		| le :: rest_les, pat_le :: rest_pat_les ->
			print_debug (Printf.sprintf "I am going to test if %s CAN BE equal to %s\n" (JSIL_Print.string_of_logic_expression le false) (JSIL_Print.string_of_logic_expression pat_le false));
			(match pat_le with
			| LVar l2 when (not (List.mem l2 spec_vars)) ->
				JSIL_Logic_Utils.extend_subst subst l2 le;
				unify_pred_args rest_les rest_pat_les
			| _ ->
				if (Pure_Entailment.is_equal le pat_le pfs solver gamma)
					then unify_pred_args rest_les rest_pat_les
					else None)) in

	match pred, pat_pred with
	| (name, les), (pat_name, pat_les) ->
		if (name = pat_name) then
			unify_pred_args les pat_les
		else None
	| _, _ -> raise (Failure "predicate_assertion_equality: FATAL ERROR")

let subtract_pred pred_name args pred_set pfs solver gamma spec_vars =
	let pred_list = preds_to_list pred_set in
	let rec loop pred_list index =
		(match pred_list with
		| [] -> raise (Failure (Printf.sprintf "Predicate %s not found in the predicate set!!!" pred_name))
		| pred :: rest_pred_list ->
			(match (predicate_assertion_equality pred (pred_name, args) pfs solver gamma spec_vars) with
			| None -> loop rest_pred_list (index + 1)
			| Some subst -> index, subst)) in

	let index, subst = loop pred_list 0 in
	DynArray.delete pred_set index;
	subst

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
