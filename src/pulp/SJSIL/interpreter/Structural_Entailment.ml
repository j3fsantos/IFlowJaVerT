open JSIL_Syntax
open JSIL_Memory_Model
open JSIL_Logic_Utils

(***************************)
(** Unification Algorithm **)
(***************************)
(*				(match subst with
					| Some subst ->
						let new_aloc = ALoc (fresh_aloc ()) in
						extend_subst subst lvar new_aloc;
						extend_subst pat_subst pat_aloc new_aloc;
						discharges
					| None -> if (Pure_Entailment.check_entailment [] pfs [ (LEq (LVar lvar, ALoc pat_aloc)) ] gamma)
								then discharges
								else raise (Failure (Printf.sprintf "ALoc %s, LVar %s : the pattern store is not normalized." pat_aloc lvar))) *)


let unify_stores (pat_store : symbolic_store) (store : symbolic_store) (pat_subst : substitution) (subst: substitution option) (pfs : jsil_logic_assertion list) solver (gamma : typing_environment) : ((jsil_logic_expr * jsil_logic_expr) list) option  =
	try
	(* Printf.printf "Let's unify the stores first:\nStore: %s. \nPat_store: %s.\n\n" (JSIL_Memory_Print.string_of_shallow_symb_store store false) (JSIL_Memory_Print.string_of_shallow_symb_store pat_store false); *)
	(* let str_subst = (match subst with
	         | None -> "Our substitution doesn't exist. Fantastic.\n"
			 | Some subst -> "Our substitution: " ^(JSIL_Memory_Print.string_of_substitution subst)) in*)
	(* Printf.printf "%s" str_subst;*)

	let discharges =
		Hashtbl.fold
			(fun var pat_lexpr discharges ->
				let lexpr = try Hashtbl.find store var with _ -> raise (Failure "the stores are not unifiable") in
				let rec spin_me_round pat_lexpr lexpr discharges =
				(*Printf.printf "(%s, %s)\n" (JSIL_Print.string_of_logic_expression pat_lexpr false) (JSIL_Print.string_of_logic_expression lexpr false);*)
				(match pat_lexpr, lexpr with

				| LLit (Num n), LLit (Integer i)
				| LLit (Integer i), LLit (Num n) ->
					if ((n = (snd (modf n))) && (i = (int_of_float n)))
						then discharges
						else raise (Failure "Numbers : the stores are not unifiable")

				| LLit pat_lit, LLit lit ->
					if (lit = pat_lit)
						then discharges
						else raise (Failure "Other literals: the stores are not unifiable")

				| ALoc pat_aloc, ALoc aloc ->
					extend_subst pat_subst pat_aloc (ALoc aloc);
					discharges

				| ALoc pat_aloc, (LLit (Loc loc)) ->
					extend_subst pat_subst pat_aloc (LLit (Loc loc));
					discharges

				| LVar lvar, _ ->
					extend_subst pat_subst lvar lexpr;
					discharges

				| ALoc pat_aloc, LVar lvar ->
					(* Printf.printf "So, Aloc %s, Lvar %s\n" pat_aloc lvar; *)
					let loc = Symbolic_State_Functions.resolve_location lvar pfs in
					(match loc with
					| Some loc -> extend_subst pat_subst pat_aloc loc; discharges
					| None     ->
						(match subst with
						| None -> raise (Failure "Variable store against abstract location")
						| Some subst ->
							let new_aloc = fresh_aloc () in
							extend_subst subst lvar (ALoc new_aloc);
							extend_subst pat_subst pat_aloc (ALoc new_aloc);
							discharges))

				| LLit lit, LVar lvar ->
					(match subst with
					| Some subst ->
						extend_subst subst lvar (LLit lit);
						discharges
					| None ->
						if (Pure_Entailment.check_entailment solver [] pfs [ (LEq (LVar lvar, LLit lit)) ] gamma)
							then discharges
							else raise (Failure (Printf.sprintf "LLit %s, LVar %s : the pattern store is not normalized." (JSIL_Print.string_of_literal lit false) lvar)))

				| LEList el1, LEList el2 ->
					(* Printf.printf ("Two lists of lengths: %d %d") (List.length el1) (List.length el2); *)
					if (List.length el1 = List.length el2) then
					begin
						(List.fold_left2
						(fun ac x y ->
							let new_ones = spin_me_round x y [] in
							new_ones @ ac)
						[] el1 el2) @ discharges
					end
					else
					begin
						[ (LLit (Bool true), LLit (Bool false)) ]
					end

				| le_pat, le -> if (le_pat = le) then discharges
				                                 else ((le_pat, le) :: discharges)) in
				spin_me_round pat_lexpr lexpr discharges)
			pat_store
			[] in
	Some discharges
	with (Failure msg) -> (* Printf.printf "Cannot unify, filha. Sorry: %s\n" msg;*) None


let unify_lexprs le_pat (le : jsil_logic_expr) p_formulae solver (gamma: typing_environment) (subst : (string, jsil_logic_expr) Hashtbl.t) : (bool * ((string * jsil_logic_expr) option)) =
	(*  Printf.printf "le_pat: %s. le: %s\n" (JSIL_Print.string_of_logic_expression le_pat false)  (JSIL_Print.string_of_logic_expression le false); *)
	match le_pat with
	| LVar var
	| ALoc var ->
		(try
			let le_pat_subst = (Hashtbl.find subst var) in
			if (Pure_Entailment.is_equal le_pat_subst le p_formulae solver gamma)
				then
					( (* Printf.printf "I managed to UNIFY BABY!!!"; *)
					(true, None))
				else (false, None)
		with _ ->	(true, Some (var, le)))

	| LLit lit ->
		if (Pure_Entailment.is_equal le_pat le p_formulae solver gamma)
			then ( (* Printf.printf "I managed to UNIFY BABY!!!"; *)  (true, None))
			else (false, None)

	| LNone ->
		if (Pure_Entailment.is_equal LNone le p_formulae solver gamma)
			then ( (true, None))
			else (false, None)

	| LUnknown ->
		if (Pure_Entailment.is_equal LUnknown le p_formulae solver gamma)
			then (true, None)
			else (false, None)

	| _ ->
		let msg = Printf.sprintf "Illegal expression in pattern to unify. le_pat: %s. le: %s."
			(JSIL_Print.string_of_logic_expression le_pat false) (JSIL_Print.string_of_logic_expression le false) in
		raise (Failure msg)




let unify_fv_pair (pat_field, pat_value) (fv_list : (jsil_logic_expr * jsil_logic_expr) list) p_formulae solver gamma subst :  (((jsil_logic_expr * jsil_logic_expr) list) * (jsil_logic_expr * jsil_logic_expr)) option =
	(* Printf.printf "unify_fv_pair. pat_field: %s, pat_value: %s\n" (JSIL_Print.string_of_logic_expression pat_field false) (JSIL_Print.string_of_logic_expression pat_value false);
	Printf.printf "fv_list: %s\n" (JSIL_Memory_Print.string_of_symb_fv_list fv_list false); *)
	let rec loop fv_list traversed_fv_list =
		match fv_list with
		| [] -> None
		| (e_field, e_value) :: rest ->
			let field_unifier = unify_lexprs pat_field e_field p_formulae solver gamma subst in
			let value_unifier = unify_lexprs pat_value e_value p_formulae solver gamma subst in
			if (Symbolic_State_Functions.update_subst2 subst field_unifier value_unifier p_formulae solver gamma)
				then
					Some ((traversed_fv_list @ rest), (e_field, e_value))
				else
					loop rest ((e_field, e_value) :: traversed_fv_list) in
	loop fv_list []


let unify_symb_fv_lists pat_fv_list fv_list def_val p_formulae solver gamma subst : (((jsil_logic_expr * jsil_logic_expr) list) * ((jsil_logic_expr * jsil_logic_expr) list)) option =
	(**
		let error_msg pat_field pat_val =
		let pat_field_str = JSIL_Print.string_of_logic_expression pat_field false in
		let pat_val_str = JSIL_Print.string_of_logic_expression pat_val false in
			Printf.sprintf "Field-val pair (%s, %s) in pattern has not been matched" pat_field_str pat_val_str in
	*)

	(* Printf.printf "Inside unify_symb_fv_lists. pat_fv_list: %s. fv_list: %s.\n" (JSIL_Memory_Print.string_of_symb_fv_list pat_fv_list false) (JSIL_Memory_Print.string_of_symb_fv_list fv_list false); *)

	let rec loop (fv_list : (jsil_logic_expr * jsil_logic_expr) list) (pat_list : (jsil_logic_expr * jsil_logic_expr) list) (matched_fv_list : (jsil_logic_expr * jsil_logic_expr) list) =
		match pat_list with
		| [] -> Some (fv_list, matched_fv_list)
		| (pat_field, pat_val) :: rest_pat_list ->
			let res = unify_fv_pair (pat_field, pat_val) fv_list p_formulae solver gamma subst in
			(match res with
			| None ->
				(* Printf.printf "I could NOT unify an fv-pair. pat_val: %s. def_val: %s\n" (JSIL_Print.string_of_logic_expression pat_val false) (JSIL_Print.string_of_logic_expression def_val false); *)
				(match def_val with
				| LUnknown -> None
				| _ ->
					let unifier = unify_lexprs pat_val def_val p_formulae solver gamma subst in
					if (Symbolic_State_Functions.update_subst1 subst unifier)
						then loop fv_list rest_pat_list matched_fv_list
						else None)
			| Some (rest_fv_list, matched_fv_pair) -> loop rest_fv_list rest_pat_list (matched_fv_pair :: matched_fv_list)) in
	loop fv_list pat_fv_list []


let unify_symb_heaps (pat_heap : symbolic_heap) (heap : symbolic_heap) pure_formulae solver gamma (subst : substitution) : (symbolic_heap option) * ((jsil_logic_assertion list) option)  =
	let quotient_heap = LHeap.create 1021 in
	try
		let pfs : jsil_logic_assertion list =
			LHeap.fold
				(fun pat_loc (pat_fv_list, pat_def) pfs ->
					(match pat_def with
					| LUnknown ->
						let loc = try
							(match (Hashtbl.find subst pat_loc) with
							| LLit (Loc loc) -> loc
							| ALoc loc -> loc
				  		| _ -> pat_loc)
							with _ -> pat_loc in
						let fv_list, (def : jsil_logic_expr) =
							(try LHeap.find heap loc with _ ->
								let msg = Printf.sprintf "Location %s in pattern has not been matched" loc in
								raise (Failure msg)) in
						let fv_lists = unify_symb_fv_lists pat_fv_list fv_list def pure_formulae solver gamma subst in
						(match fv_lists with
						| Some (new_fv_list, matched_fv_list) ->
							LHeap.replace quotient_heap loc (new_fv_list, def);
							let new_pfs : jsil_logic_assertion list = make_all_different_pure_assertion new_fv_list matched_fv_list in
							new_pfs @ pfs
						| None -> raise (Failure ("Pattern heaps cannot have default values")))
					| _ -> raise (Failure ("Pattern heaps cannot have default values"))))
				pat_heap
				[] in
		LHeap.iter
			(fun loc (fv_list, def) ->
				try
					let _ = LHeap.find quotient_heap loc in
					()
				with _ ->
					LHeap.add quotient_heap loc (fv_list, def))
			heap;
		LHeap.iter
			(fun loc (fv_list, def) ->
				match def with
				| LUnknown ->
					if ((List.length fv_list) = 0)
						then LHeap.remove quotient_heap loc
				| _ -> ())
			quotient_heap;
		(Some quotient_heap), (Some pfs)
	with _ ->
		(* Printf.printf "unify_symb_heaps FAILED BABYYYY\n"; *)
		None, None


let unify_pred_against_pred (pat_pred : (string * (jsil_logic_expr list))) (pred : (string * (jsil_logic_expr list))) p_formulae solver gamma (subst : substitution) : substitution option =
	let pat_pred_name, pat_pred_args = pat_pred in
	let pred_name, pred_args = pred in

	(* Printf.printf "Trying to unify %s against %s\n" (JSIL_Memory_Print.string_of_pred pat_pred false) (JSIL_Memory_Print.string_of_pred pred false); *)
	let rec unify_expr_lists pat_list list subst =
		(match pat_list, list with
		| [], [] -> ( (* Printf.printf "Success in predicate set unification\n"; *) true)
		| (pat_le :: rest_pat_list), (le :: rest_list) ->
			let unifier = unify_lexprs pat_le le p_formulae solver gamma subst in
			(* Printf.printf "pat_le: %s. le: %s\n" (JSIL_Print.string_of_logic_expression pat_le false) (JSIL_Print.string_of_logic_expression le false); *)
			if (Symbolic_State_Functions.update_subst1 subst unifier)
				then unify_expr_lists rest_pat_list rest_list subst
				else ( (* Printf.printf "Tremendous failure in predicate set unification\n"; *) false)
		| _, _ -> false) in

	if (pat_pred_name = pred_name) then
		begin
		let new_subst = Hashtbl.copy subst in
		if (unify_expr_lists pat_pred_args pred_args new_subst)
			then Some new_subst
			else None
		end
		else None


let unify_pred_against_pred_set (pat_pred : (string * (jsil_logic_expr list))) (preds : (string * (jsil_logic_expr list)) list) p_formulae solver gamma (subst : substitution) =
	let rec loop preds quotient_preds =
		(match preds with
		| [] -> None, quotient_preds
		| pred :: rest_preds ->
			let new_subst = unify_pred_against_pred pat_pred pred p_formulae solver gamma subst in
			(match new_subst with
			| None -> loop rest_preds (pred :: quotient_preds)
			| Some new_subst -> Some new_subst, (quotient_preds @ rest_preds))) in
	loop preds []


let unify_pred_list_against_pred_list (pat_preds : (string * (jsil_logic_expr list)) list) (preds : (string * (jsil_logic_expr list)) list) p_formulae solver gamma (subst : substitution) =
	let rec loop pat_preds preds subst =
		(match pat_preds with
		| [] -> Some subst, preds
		| pat_pred :: rest_pat_preds ->
			let new_subst, rest_preds = unify_pred_against_pred_set pat_pred preds p_formulae solver gamma subst in
			(match new_subst with
			| None -> None, []
			| Some new_subst -> loop rest_pat_preds rest_preds new_subst)) in
	loop pat_preds preds subst


let unify_pred_arrays (pat_preds : predicate_set) (preds : predicate_set) p_formulae solver gamma (subst : substitution) =
	let pat_preds = DynArray.to_list pat_preds in
	let preds = DynArray.to_list preds in
	let new_subst, quotient_preds = unify_pred_list_against_pred_list pat_preds preds p_formulae solver gamma subst in
	new_subst, (DynArray.of_list quotient_preds)


let unify_gamma pat_gamma gamma pat_store subst ignore_vars =
  (* Printf.printf "I am about to unify two gammas\n";
	 	Printf.printf "pat_gamma: %s.\ngamma: %s.\nsubst: %s\n"
		(JSIL_Memory_Print.string_of_gamma pat_gamma) (JSIL_Memory_Print.string_of_gamma gamma)
		(JSIL_Memory_Print.string_of_substitution subst); *)
	let res = (Hashtbl.fold
		(fun var v_type ac ->
			(* (not (is_lvar_name var)) *)
			(if ((not ac) || (List.mem var ignore_vars))
				then ac
				else
					try
						let le =
							(if (is_lvar_name var)
								then Hashtbl.find subst var
								else
									(match (store_get_var_val pat_store var) with
									| Some le -> JSIL_Logic_Utils.lexpr_substitution le subst true
									| None -> (PVar var))) in
						let le_type, is_typable, _ = JSIL_Logic_Utils.type_lexpr gamma le in
						match le_type with
						| Some le_type ->
							 (* Printf.printf "unify_gamma. pat gamma var: %s. le: %s. v_type: %s. le_type: %s\n"
								var
								(JSIL_Print.string_of_logic_expression le false)
								(JSIL_Print.string_of_type v_type)
								(JSIL_Print.string_of_type le_type); *)
							(le_type = v_type)
						| None ->
							(* Printf.printf "failed unify_gamma. pat gamma var: %s. le: %s. v_type: %s\n"
								var
								(JSIL_Print.string_of_logic_expression le false)
								(JSIL_Print.string_of_type v_type); *)
							false
					with _ ->
						true))
		pat_gamma
		true) in
	(* Printf.printf "\nEXITING unify_gamma: res: %b\n\n" res; *)
	res


let spec_logic_vars_discharge subst lvars pfs solver gamma =
	let pf_list = (JSIL_Memory_Model.pfs_to_list pfs) in
	let pfs_to_prove =
		List.fold_left
			(fun ac var ->
				try
					let le = Hashtbl.find subst var in
					let new_pa =	(LEq ((LVar var), le)) in
					new_pa :: ac
				with _ ->  ac)
			[]
			lvars in
	let ret = Pure_Entailment.check_entailment solver [] pf_list pfs_to_prove gamma in
	(* Printf.printf "check if (%s) entails (%s) - ret: %b\n" (JSIL_Print.str_of_assertion_list pf_list) (JSIL_Print.str_of_assertion_list pfs_to_prove) ret;	*)
	ret


let pf_list_of_discharges discharges subst =
	let rec loop discharges pfs =
		match discharges with
		| [] -> pfs
		| (le_pat, le) :: rest_discharges ->
			let s_le_pat = JSIL_Logic_Utils.lexpr_substitution le_pat subst true in
			loop rest_discharges ((LEq (s_le_pat, le)) :: pfs) in
	loop discharges []


let unify_symb_states lvars pat_symb_state (symb_state : symbolic_state) : (symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * bool) option  =
	let pat_heap, pat_store, pat_pf, pat_gamma, pat_preds, _ = pat_symb_state in
	let heap, store, pf, gamma, preds, solver = symb_state in
	let subst = init_substitution lvars in


	(* Printf.printf "Unify Symbolic States:\n";

	Printf.printf "OUR symbolic state: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state);
	Printf.printf "PRED symbolic state: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state pat_symb_state); *)


	let discharges = unify_stores pat_store store subst None (pfs_to_list pf) solver gamma in
	match discharges with
	| Some discharges ->
		let spec_vars_check = spec_logic_vars_discharge subst lvars (get_pf symb_state) (get_solver symb_state) (get_gamma symb_state) in
	  (* Printf.printf "the PAT symbolic state after computing quotient heap:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state pat_symb_state); *)


		let (quotient_heap, new_pfs) : (symbolic_heap option) * ((jsil_logic_assertion list) option) = unify_symb_heaps pat_heap heap pf solver gamma subst in
		(* print_endline (Printf.sprintf "Substitution after heap unification baby!!!\n%s" (JSIL_Memory_Print.string_of_substitution subst)); *)
		let new_subst, quotient_preds = unify_pred_arrays pat_preds preds pf solver gamma subst in
		(match spec_vars_check, new_subst, quotient_heap, new_pfs with
		| true, Some new_subst, Some quotient_heap, Some new_pfs ->
			let s_new_subst = copy_substitution new_subst in

			(* Printf.printf "Substitution afert predicate set unification baby!!!\n%s" (JSIL_Memory_Print.string_of_substitution new_subst);
			Printf.printf "I computed a quotient heap but I also need to check an entailment\n";
			Printf.printf "The quotient heap that I just computed:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false); *)

			let pat_pf_existentials = get_subtraction_vars (get_pf_list pat_symb_state) s_new_subst in
			let new_pat_pf_existentials = (List.map (fun v -> fresh_lvar ()) pat_pf_existentials) in
			let existential_substitution = init_substitution2 pat_pf_existentials (List.map (fun v -> LVar v) new_pat_pf_existentials) in
			extend_substitution s_new_subst pat_pf_existentials (List.map (fun v -> LVar v) new_pat_pf_existentials);
			let new_gamma =
				if ((List.length pat_pf_existentials) > 0)
					then (
						let new_gamma = copy_gamma gamma in
						let new_pat_gamma = filter_gamma_with_subst pat_gamma pat_pf_existentials existential_substitution in
						extend_gamma new_gamma new_pat_gamma;
						new_gamma)
				else gamma in

			(* print_endline (Printf.sprintf "new_pfs: %s" (JSIL_Print.str_of_assertion_list new_pfs)); *)
			Symbolic_State_Functions.extend_pf pf solver new_pfs;
			let pf_discharges = pf_list_of_discharges discharges s_new_subst in
			let pat_pf_list = List.map (fun a -> assertion_substitution a s_new_subst true) (pfs_to_list pat_pf) in
			let pf_list = pfs_to_list pf in

			let existentials_str = print_var_list new_pat_pf_existentials in

			(*print_endline (Printf.sprintf "Discharges: %s" (JSIL_Print.str_of_assertion_list pf_discharges)); *)

		  	print_endline (Printf.sprintf "About to check if\n (\n%s\n)	\nENTAILS\n (Exists %s.\n(\n%s\n))\n given the gamma:\n%s"
					(JSIL_Print.str_of_assertion_list pf_list)
					existentials_str
					(JSIL_Print.str_of_assertion_list (pat_pf_list @ pf_discharges))
				(	JSIL_Memory_Print.string_of_gamma new_gamma));

			let unify_gamma_check = (unify_gamma pat_gamma new_gamma pat_store s_new_subst pat_pf_existentials) in
			let entailment_check_ret = Pure_Entailment.check_entailment solver new_pat_pf_existentials pf_list (pat_pf_list @ pf_discharges) new_gamma in
			(* Printf.printf "Unify gamma: %b Entailment check: %b\n" unify_gamma_check entailment_check_ret; *)
			(if (entailment_check_ret & unify_gamma_check) then
					(  (* Printf.printf "I could check the entailment!!!\n"; *)
					Some (quotient_heap, quotient_preds, s_new_subst, pf_discharges, true))
				else
					(
					(* Printf.printf "I could NOT check the entailment!!!\n";
					Printf.printf "entailment_check_ret: %b. unify_gamma_check: %b.\n" entailment_check_ret unify_gamma_check; *)
					Some (quotient_heap, quotient_preds, new_subst, pf_discharges, false)))
		| _ -> (* Printf.printf "One of the four things failed.\n";*) None)
	| None -> (* Printf.printf "Sweet Jesus, broken discharges.\n";*) None

let fully_unify_symb_state pat_symb_state symb_state lvars =
	(* Printf.printf "Fully_unify_symb_state.\nFinal symb_state:\n%s.\nPost symb_state:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state) (JSIL_Memory_Print.string_of_shallow_symb_state pat_symb_state); *)
	let unifier = unify_symb_states lvars pat_symb_state symb_state in
	match unifier with
	| Some (quotient_heap, quotient_preds, subst, pf_discharges, true) ->
		if ((Symbolic_State_Functions.is_symb_heap_empty quotient_heap) && (Symbolic_State_Functions.is_preds_empty quotient_preds)) then
			(Some subst, "")
		else (None, "incomplete match")
	| Some (_, _, _, _, false)
	| None -> (None, "sorry, non_unifiable heaps")


let unify_symb_state_against_post proc_name spec symb_state flag symb_exe_info =
	let print_error_to_console msg =
		(if (msg = "")
			then Printf.printf "Failed to verify a spec of proc %s\n" proc_name
			else Printf.printf "Failed to verify a spec of proc %s -- %s\n" proc_name msg);
		let final_symb_state_str = JSIL_Memory_Print.string_of_shallow_symb_state symb_state in
		let post_symb_state_str = JSIL_Memory_Print.string_of_symb_state_list spec.n_post in
		Printf.printf "Final symbolic state: %s\n" final_symb_state_str;
		Printf.printf "Post condition: %s\n" post_symb_state_str in

	let rec loop posts post_vars_lists i =
		(match posts, post_vars_lists with
		| [], [] -> print_error_to_console "Non_unifiable heaps";  raise (Failure "post condition is not unifiable")
		| post :: rest_posts, post_lvars :: rest_posts_lvars ->
			let subst = fully_unify_symb_state post symb_state spec.n_lvars in
			(match subst with
			| Some subst, _ ->
				activate_post_in_post_pruning_info symb_exe_info proc_name i;
				Printf.printf "Verified one spec of proc %s\n" proc_name
			| None, msg       -> Printf.printf "No go: %s\n" msg; loop rest_posts rest_posts_lvars (i + 1))) in

	loop spec.n_post spec.n_post_lvars 0
