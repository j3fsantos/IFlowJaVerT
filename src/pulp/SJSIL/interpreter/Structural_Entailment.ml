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
	(* Printf.printf "Let's unify the stores first:\nStore: %s. \nPat_store: %s.\n\n" (JSIL_Memory_Print.string_of_shallow_symb_store store false) (JSIL_Memory_Print.string_of_shallow_symb_store pat_store false); 
	let str_subst = (match subst with
	         | None -> "Our substitution doesn't exist. Fantastic.\n"
			 | Some subst -> "Our substitution: " ^(JSIL_Memory_Print.string_of_substitution subst)) in
	Printf.printf "%s" str_subst; *)

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
	with (Failure msg) -> (* Printf.printf "Cannot unify, filha. Sorry: %s\n" msg; *) None


let rec unify_lexprs le_pat (le : jsil_logic_expr) p_formulae solver (gamma: typing_environment) (subst : (string, jsil_logic_expr) Hashtbl.t) : (bool * ((string * jsil_logic_expr) option)) =
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

	| LEList ple ->
		(* Printf.printf "Now, are these lists equal?\n";*)
		let list_eq lx ly = List.fold_left2
			(fun ac x y ->
				(* Printf.printf "%s == %s? " (JSIL_Print.string_of_logic_expression x false) (JSIL_Print.string_of_logic_expression y false); *)
				let (ch, oops) = unify_lexprs x y p_formulae solver gamma subst in
				(* Printf.printf "%b\n" ch; *)
				match oops with
				 | None -> ac && ch
				 | Some _ -> false ) true lx ly in
		match le with
		| LLit (LList le') ->
	   		let lle = List.length ple in
			let lle' = List.length le' in
			if (lle = lle') then
				let le'' = List.map (fun x -> LLit x) le' in
				let is_eq = list_eq ple le'' in
				(* Printf.printf "And they aaaare: %b\n" is_eq; *)
					(is_eq, None)
			else (false, None)
		| LEList le' ->
	   		let lle = List.length ple in
			let lle' = List.length le' in
			if (lle = lle') then
				let is_eq = list_eq ple le' in
				(* Printf.printf "And they aaaare: %b\n" is_eq; *)
					(is_eq, None)
			else (false, None)
		| le' -> let le'' = find_me_baby le' (Hashtbl.create 1) p_formulae in
			let (is_eq, whatever) = unify_lexprs le_pat le'' p_formulae solver gamma subst in
			(* Printf.printf "And they aaaare: %b\n" is_eq; *)
			(is_eq, whatever)
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
								Printf.printf "%s\n" msg; 
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
	with (Failure msg) ->
		Printf.printf "unify_symb_heaps FAILED BABYYYY with message: %s\n" msg; 
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
		(JSIL_Memory_Print.string_of_substitution subst);  *)
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


let pf_list_of_discharges discharges subst partial =
	let rec loop discharges pfs =
		match discharges with
		| [] -> pfs
		| (le_pat, le) :: rest_discharges ->
			let s_le_pat = JSIL_Logic_Utils.lexpr_substitution le_pat subst partial in
			loop rest_discharges ((LEq (s_le_pat, le)) :: pfs) in
	loop discharges []


let unify_symb_states lvars pat_symb_state (symb_state : symbolic_state) : (symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * bool) option  =
	let pat_heap, pat_store, pat_pf, pat_gamma, pat_preds, _ = pat_symb_state in
	let heap, store, pf, gamma, preds, solver = symb_state in
	let subst = init_substitution lvars in


	(* Printf.printf "Unify Symbolic States HERE HERE HERE:\n";

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

			(* Printf.printf "I computed a quotient heap but I also need to check an entailment\n";
			Printf.printf "The quotient heap that I just computed:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false); *)
		
			let pat_pf_existentials = get_subtraction_vars (Symbolic_State_Functions.get_symb_state_vars_as_list false pat_symb_state) s_new_subst in
			(* Printf.printf "Substitution after preset unification baby!!!\n%s\nExistentials:\n%s\n" 
				(JSIL_Memory_Print.string_of_substitution s_new_subst)
				(print_var_list pat_pf_existentials); *)
			
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
			
			let pf_discharges = pf_list_of_discharges discharges s_new_subst false in
			let pat_pf_list = List.map (fun a -> assertion_substitution a s_new_subst true) (pfs_to_list pat_pf) in
			let pf_list = pfs_to_list pf in

			let existentials_str = print_var_list new_pat_pf_existentials in

			print_endline (Printf.sprintf "Discharges: %s" (JSIL_Print.str_of_assertion_list pf_discharges));

			let pf_list = List.map (fun x -> JSIL_Logic_Utils.reduce_assertion x) pf_list in
			let pat_pf_list = List.map (fun x -> JSIL_Logic_Utils.reduce_assertion x) pat_pf_list in
			let pf_discharges = List.map (fun x -> JSIL_Logic_Utils.reduce_assertion x) pf_discharges in

		  	(* print_endline (Printf.sprintf "About to check if\n (\n%s\n)	\nENTAILS\n (Exists %s.\n(\n%s\n))\n given the gamma:\n%s"
					(JSIL_Print.str_of_assertion_list pf_list)
					existentials_str
					(JSIL_Print.str_of_assertion_list (pat_pf_list @ pf_discharges))
				(	JSIL_Memory_Print.string_of_gamma new_gamma)); *)

			let unify_gamma_check = (unify_gamma pat_gamma new_gamma pat_store s_new_subst pat_pf_existentials) in
			let entailment_check_ret = Pure_Entailment.check_entailment solver new_pat_pf_existentials pf_list (pat_pf_list @ pf_discharges) new_gamma in
			(if (entailment_check_ret & unify_gamma_check) then
					( (*  Printf.printf "I could check the entailment!!!\n"; *)
					Some (quotient_heap, quotient_preds, s_new_subst, pf_discharges, true))
				else
					(
					(* Printf.printf "I could NOT check the entailment!!!\n";
					Printf.printf "entailment_check_ret: %b. unify_gamma_check: %b.\n" entailment_check_ret unify_gamma_check; *)
					Some (quotient_heap, quotient_preds, new_subst, pf_discharges, false)))
		| _ -> (* Printf.printf "One of the four things failed.\n"; *) None)
	| None -> (* Printf.printf "Sweet Jesus, broken discharges.\n"; *) None




let unify_symb_states_fold existentials pat_symb_state (symb_state : symbolic_state)  : (symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * bool) option  =
	let pat_heap, pat_store, pat_pf, pat_gamma, pat_preds, _ = pat_symb_state in
	let heap, store, pf, gamma, preds, solver = symb_state in
	let subst = init_substitution [] in
	
	let find_existentials_types existentials filtered_vars store gamma pat_gamma = 
		let gamma_existentials = mk_gamma () in 
		List.iter 
			(fun x ->
				let le_x = store_get_var_val store x in 
				let x_type = gamma_get_type pat_gamma x in 
				match le_x, x_type with
				| Some le_x, Some x_type -> let _ = JSIL_Logic_Utils.reverse_type_lexpr_aux gamma gamma_existentials le_x x_type in ()
				|	_, _ -> ())
			filtered_vars; 
		let gamma_existentials = filter_gamma gamma_existentials existentials in 
		gamma_existentials in 
				 
	Printf.printf "Unify Symbolic States FOLD:\n";
	Printf.printf "OUR symbolic state: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state);
	Printf.printf "PRED symbolic state: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state pat_symb_state);
	
	let filtered_vars, unfiltered_vars = 
		Symbolic_State_Functions.filter_store 
			store 
			(fun (le : jsil_logic_expr) -> 
				let le_vars : (string, bool) Hashtbl.t = JSIL_Logic_Utils.get_expr_vars_tbl le false in 
				let existentials_in_le = List.filter (fun var -> Hashtbl.mem le_vars var) existentials in 
				(List.length existentials_in_le > 0)) in 
	
	let gamma_existentials = find_existentials_types existentials filtered_vars store gamma pat_gamma in 
	
	let discharges_0 = 
		try 
			Some 
				(List.fold_left 
					(fun ac x -> 
						let le_x = store_get_var_val store x in 
						let pat_le_x = store_get_var_val pat_store x in 
						match le_x, pat_le_x with 
						| Some le_x, Some pat_le_x -> (pat_le_x, le_x) :: ac 
						| _ -> raise (Failure ""))
					[]
					filtered_vars)
		with _ -> None in 
	
	let store = Symbolic_State_Functions.store_projection store unfiltered_vars in 
	let old_pat_store = pat_store in 
	let pat_store = Symbolic_State_Functions.store_projection pat_store unfiltered_vars in 
	
	let discharges = unify_stores pat_store store subst None (pfs_to_list pf) solver gamma in
	match discharges, discharges_0 with
	| Some discharges, Some discharges_0 ->
		let (quotient_heap, new_pfs) : (symbolic_heap option) * ((jsil_logic_assertion list) option) = unify_symb_heaps pat_heap heap pf solver gamma subst in
		(* print_endline (Printf.sprintf "Substitution after heap unification baby!!!\n%s" (JSIL_Memory_Print.string_of_substitution subst)); *)
		let new_subst, quotient_preds = unify_pred_arrays pat_preds preds pf solver gamma subst in
		(match new_subst, quotient_heap, new_pfs with
		| Some new_subst, Some quotient_heap, Some new_pfs ->
			let s_new_subst = copy_substitution new_subst in

			Printf.printf "Substitution after predicate set unification baby!!!\n%s" (JSIL_Memory_Print.string_of_substitution new_subst);
			
			(*Printf.printf "I computed a quotient heap but I also need to check an entailment\n";
			Printf.printf "The quotient heap that I just computed:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false); *)

			let pat_pf_existentials = get_subtraction_vars (Symbolic_State_Functions.get_symb_state_vars_as_list false pat_symb_state) s_new_subst in
			let new_pat_pf_existentials = (List.map (fun v -> fresh_lvar ()) pat_pf_existentials) in
			let existential_substitution = init_substitution2 pat_pf_existentials (List.map (fun v -> LVar v) new_pat_pf_existentials) in
			extend_substitution s_new_subst pat_pf_existentials (List.map (fun v -> LVar v) new_pat_pf_existentials);
			
			let new_gamma =
				if ((List.length pat_pf_existentials) > 0)
					then (
						let new_gamma = copy_gamma gamma in
						let new_pat_gamma = filter_gamma_with_subst pat_gamma pat_pf_existentials existential_substitution in
						extend_gamma new_gamma new_pat_gamma;
						extend_gamma new_gamma gamma_existentials; 
						new_gamma)
				else gamma in

			(* print_endline (Printf.sprintf "new_pfs: %s" (JSIL_Print.str_of_assertion_list new_pfs)); *)
			Symbolic_State_Functions.extend_pf pf solver new_pfs;
			let pf_discharges = pf_list_of_discharges (discharges @ discharges_0) s_new_subst false in
			let pat_pf_list = List.map (fun a -> assertion_substitution a s_new_subst true) (pfs_to_list pat_pf) in
			let pf_list = pfs_to_list pf in

			let existentials_str = print_var_list (existentials @ new_pat_pf_existentials) in 

			print_endline (Printf.sprintf "Discharges: %s" (JSIL_Print.str_of_assertion_list pf_discharges)); 

			let pf_list = List.map (fun x -> JSIL_Logic_Utils.reduce_assertion x) pf_list in
			let pat_pf_list = List.map (fun x -> JSIL_Logic_Utils.reduce_assertion x) pat_pf_list in
			let pf_discharges = List.map (fun x -> JSIL_Logic_Utils.reduce_assertion x) pf_discharges in

		  print_endline (Printf.sprintf "In unify_symb_states FOLD!!!! - About to check if\n (\n%s\n)	\nENTAILS\n (Exists %s.\n(\n%s\n))\n given the gamma:\n%s"
					(JSIL_Print.str_of_assertion_list pf_list)
					existentials_str
					(JSIL_Print.str_of_assertion_list (pat_pf_list @ pf_discharges))
				(	JSIL_Memory_Print.string_of_gamma new_gamma)); 

			let unify_gamma_check = (unify_gamma pat_gamma new_gamma old_pat_store s_new_subst pat_pf_existentials) in
			let entailment_check_ret = Pure_Entailment.check_entailment solver (existentials @ new_pat_pf_existentials) pf_list (pat_pf_list @ pf_discharges) new_gamma in
			(if (entailment_check_ret & unify_gamma_check) then
					(  (* Printf.printf "I could check the entailment!!!\n"; *)
					Some (quotient_heap, quotient_preds, s_new_subst, pf_discharges, true))
				else
					(
					 Printf.printf "I could NOT check the entailment!!!\n";
					Printf.printf "entailment_check_ret: %b. unify_gamma_check: %b.\n" entailment_check_ret unify_gamma_check; 
					Some (quotient_heap, quotient_preds, new_subst, pf_discharges, false)))
		| _ -> (* Printf.printf "One of the four things failed.\n"; *) None)
	| _, _ -> (* Printf.printf "Sweet Jesus, broken discharges.\n"; *) None




let fully_unify_symb_state pat_symb_state symb_state lvars =
	(* Printf.printf "Fully_unify_symb_state.\nFinal symb_state:\n%s.\nPost symb_state:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state) (JSIL_Memory_Print.string_of_shallow_symb_state pat_symb_state); *)
	let unifier = unify_symb_states lvars pat_symb_state symb_state in
	match unifier with
	| Some (quotient_heap, quotient_preds, subst, pf_discharges, true) ->
		let emp_heap = (Symbolic_State_Functions.is_symb_heap_empty quotient_heap) in
		let emp_preds = (Symbolic_State_Functions.is_preds_empty quotient_preds) in
		if (emp_heap && emp_preds) then
			(Some subst, "")
		else
			(* let _ = if (emp_heap) then begin Printf.printf "Quotient heap empty.\n" end
					else begin Printf.printf "Quotient heap left: \n%s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false) end in
			let _ = if (emp_preds) then begin Printf.printf "Quotient predicates empty.\n" end
					else begin Printf.printf "Quotient predicates left: \n%s\n" (JSIL_Memory_Print.string_of_preds quotient_preds false) end in *)
			(None, "incomplete match")
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


let merge_symb_states (symb_state_l : symbolic_state) (symb_state_r : symbolic_state) subst  : symbolic_state =
	(* Printf.printf "gamma_r: %s\n." (JSIL_Memory_Print.string_of_gamma (get_gamma symb_state_r)); *)
	(* Printf.printf "substitution: %s\n" (JSIL_Memory_Print.string_of_substitution subst); *)
	let symb_state_r = Symbolic_State_Functions.symb_state_substitution symb_state_r subst false in
	let heap_l, store_l, pf_l, gamma_l, preds_l, solver_l = symb_state_l in
	let heap_r, store_r, pf_r, gamma_r, preds_r, _ = symb_state_r in
	let pf_l = DynArray.map (fun x -> JSIL_Logic_Utils.reduce_assertion x) pf_l in
	let pf_r = DynArray.map (fun x -> JSIL_Logic_Utils.reduce_assertion x) pf_r in
	Symbolic_State_Functions.merge_pfs pf_l pf_r;
	Symbolic_State_Functions.merge_gammas gamma_l gamma_r;
	Symbolic_State_Functions.merge_heaps heap_l heap_r pf_l solver_l gamma_l;

	(* Printf.printf "AFTER MERGING HEAPS\n\n"; *)
	DynArray.append preds_r preds_l;
	(heap_l, store_l, pf_l, gamma_l, preds_l, (ref None))


let safe_merge_symb_states (symb_state_l : symbolic_state) (symb_state_r : symbolic_state) (subst : substitution) : symbolic_state option =
	(* *)

	(* Printf.printf "gamma_r: %s\n." (JSIL_Memory_Print.string_of_gamma (get_gamma symb_state_r)); *)
	(* Printf.printf "substitution: %s\n" (JSIL_Memory_Print.string_of_substitution subst); *)

	let pf_r_existentials = get_subtraction_vars (Symbolic_State_Functions.get_symb_state_vars_as_list false symb_state_r) subst in
	let gammas_unifiable = unify_gamma (get_gamma symb_state_r) (get_gamma symb_state_l) (get_store symb_state_r) (subst : substitution) (pf_r_existentials : string list) in

	let symb_state_r = Symbolic_State_Functions.symb_state_substitution symb_state_r subst false in
	let heap_l, store_l, pf_l, gamma_l, preds_l, solver_l = symb_state_l in
	let heap_r, store_r, pf_r, gamma_r, preds_r, _ = symb_state_r in
	let pf_l = DynArray.map (fun x -> JSIL_Logic_Utils.reduce_assertion x) pf_l in
	let pf_r = DynArray.map (fun x -> JSIL_Logic_Utils.reduce_assertion x) pf_r in

	(* DynArray.append pf_r pf_l; *)
	Symbolic_State_Functions.merge_pfs pf_l pf_r;
	Symbolic_State_Functions.merge_gammas gamma_l gamma_r;


	let satisfiability_check = gammas_unifiable && (Pure_Entailment.check_satisfiability (pfs_to_list pf_l) gamma_l []) in

	if (satisfiability_check)
		then (
			(* Printf.printf "BEFORE MERGING HEAPS. pfs_l: %s\n. pfs_r: %s\n." (JSIL_Memory_Print.string_of_shallow_p_formulae pf_l false)
				(JSIL_Memory_Print.string_of_shallow_p_formulae pf_r false); *)
			Symbolic_State_Functions.merge_heaps heap_l heap_r pf_l solver_l gamma_l;
			(* Printf.printf "AFTER MERGING HEAPS\n\n"; *)
			DynArray.append preds_r preds_l;
			(* *)
			(* Printf.printf "s_heap_l after merge: %s.\ns_preds_l: %s.\ns_store_l: %s.\n" (JSIL_Memory_Print.string_of_shallow_symb_heap heap_l)
					(JSIL_Memory_Print.string_of_preds preds_l) (JSIL_Memory_Print.string_of_shallow_symb_store store_l); *)
			(* *)
			Some (heap_l, store_l, pf_l, gamma_l, preds_l, (ref None)))
		else None


(** 
  symb_state        - the current symbolic state minus the predicate that is to be unfolded
	pat_symb_state    - the symbolic state corresponding to the definition of the predicate that we are trying to unfold
	calling_store     - a mapping from the parameters of the predicate to the arguments given in the unfolding
	subst_unfold_args - substitution that matches the arguments of the unfold logical command with the arguments of 
	                    the predicate as it appears in the current symbolic state 
	existentials      - new variables introduced in the unfold 
	spec_vars         - logical variables that appear in the precondition 
*)
let unfold_predicate_definition symb_state pat_symb_state calling_store subst_unfold_args spec_vars = 
	
	(* PREAMBLE                                                                                                            *)
	let store_0 = calling_store in
	let store_1 = get_store pat_symb_state in
	let gamma_0 = get_gamma symb_state in 
	let gamma_1 = get_gamma pat_symb_state in 
	let store_vars = get_store_domain store_0 in 
	
	let find_store_var_type store gamma x = 
		let x_type = gamma_get_type gamma x in
		match x_type with 
		| Some x_type -> Some x_type 
		| None -> 
			let le_x = store_get_var_val store x in
			(match le_x with 
			| Some le_x -> 
				let x_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le_x in
				x_type
			| None -> None) in  
	
	
	(* STEP 1 - Unify(store_0, store_1, pi_0) = subst, pat_subst, discharges                                               *)
	(* subst (store_0) =_{pi_0} pat_subst (store_1) provided that the discharges hold                                      *)  
	(* we start by unifying the stores - this unification will produce two substituions: pat_subst and subst               *)
	(* pat_subst is to applied in the pat_symb_state and subst is to be applied in the symb_state                          *)
	(* The store unification also generates a list of discharges - discharges - which need to hold for the stores to match *)
	let step_1 () = 
		let pat_subst = init_substitution [] in
		let subst = init_substitution [] in
		let discharges = unify_stores store_1 store_0 pat_subst (Some subst) (pfs_to_list (get_pf symb_state)) (get_solver symb_state) (get_gamma symb_state) in
		Printf.printf "substitutions after store unification.\nSubst:\n%s\nPat_Subst:\n%s\n"
			(JSIL_Memory_Print.string_of_substitution subst)
			(JSIL_Memory_Print.string_of_substitution pat_subst);
		discharges, subst, pat_subst in 	
	
	
	(* STEP 2 - the store must agree on the types                                                                         *)
	(* forall x \in domain(store_0) = domain(store_1) :                                                                    *)
	(*   ((Gamma_1(x) = tau_1) \/ (Gamma_1 |- store_1(x) : tau_1)  /\ (Gamma_0 |- store_0(x) : tau_0)) => tau_1 = tau_0    *)
	let step_2 () = 
		let store_0_var_types = List.map (fun x -> find_store_var_type store_0 gamma_0 x) store_vars in 
		let store_1_var_types = List.map (fun x -> find_store_var_type store_1 gamma_1 x) store_vars in 
		let stores_are_type_compatible = 
			List.fold_left2 
				(fun ac t1 t2 ->
					if (not ac) then false else 
					match t1, t2 with 
					| Some t1, Some t2 -> t1 = t2 
					| _, _ -> true) true store_0_var_types store_1_var_types in
		store_0_var_types, store_1_var_types, stores_are_type_compatible in 
			
					
	(* STEP 3 - the substitutions need to make sense wrt the gammas                                                        *)
	(* forall x \in subst : subst(x) = le /\ Gamma_0(x) = tau =>  \Gamma_1 |- le : tau                                     *)
	(* forall x \in pat_subst : pat_subst (x) = le /\ Gamma_1(x) = tau => \Gamma_0                                         *)
	let step_3 subst pat_subst = 
		let subst_is_sensible = Symbolic_State_Functions.is_sensible_subst subst gamma_0 gamma_1 in
		let pat_subst_is_sensible = Symbolic_State_Functions.is_sensible_subst pat_subst gamma_1 gamma_0 in
		subst_is_sensible, pat_subst_is_sensible in 
		
	
	(* STEP 4 - complete gamma_0 with unfolding info - gamma_0' st dom(gamma_0') \subseteq existentials                    *)
	(* forall x \in domain(store_0) :                                                                                      *)
	(* 	!(gamma_0 |- store_0(x) : _) /\ (gamma_1 |- store_1(x) : tau_1) => (gamma_0 + gamma_0' |- store_0(x) : tau_0       *)
	let step_4 store_0_var_types = 
		let untyped_store_0_vars = 
			List.fold_left2
				(fun ac v t ->
					match t with 
					| None -> v :: ac 
					| Some _ -> ac) [] store_vars store_0_var_types in 
		let gamma_0' = mk_gamma () in 
		List.iter 
			(fun x ->
				let le_x = store_get_var_val store_0 x in 
				let x_type = find_store_var_type store_1 gamma_1 x in 
				match le_x, x_type with
				| Some le_x, Some x_type -> let _ = JSIL_Logic_Utils.reverse_type_lexpr_aux gamma_0 gamma_0' le_x x_type in ()
				|	_, _ -> ())
				untyped_store_0_vars;
		Printf.printf "Inferred typing information given the unfolding:\n%s\n" (JSIL_Memory_Print.string_of_gamma gamma_0'); 
		gamma_0' in
	
	
	(* STEP 5 - check whether the pure formulae make sense together - new_pat_subst = subst (pat_subst (.))                 *)
	(* pi_0' = subst(pi_0),  pi_1' = new_pat_subst (pi_1)                                                                   *)
	(* pi_discharges = new_pat_subst ( discharges ); pi_unfold_args = pf_of_subst ( subst_unfold_args )                     *)
	(* pi_spec_vars = pf_of_subst ( spec_vars_subst ), where spec_vars_subst = subst|_{spec_vars}                           *)
	(* pi = pi_0' + pi_1' + pi_discharges + pi_spec_vars + pi_unfold_args                                                   *)
	(* gamma_0'' = subst (gamma_0 (.)) + subst( gamma_0' (.))   gamma_1'' = new_pat_subst (gamma_1 (.))                     *)
	(* gamma = gamma_0'' + gamma_1''                                                                                        *)
	(* |-_{gamma} pi                                                                                                        *)
	let step_5 subst pat_subst discharges gamma_0' = 
		let pi_0 = get_pf symb_state in 
		let pi_1 = get_pf pat_symb_state in 
		let new_pat_subst = compose_partial_substitutions subst pat_subst in
		let spec_vars_subst = filter_substitution subst spec_vars in	
		let pi_0' = pfs_to_list (Symbolic_State_Functions.pf_substitution pi_0 subst true) in
		let pi_1' = pfs_to_list (Symbolic_State_Functions.pf_substitution pi_1 new_pat_subst false) in
		let pi_discharges = pf_list_of_discharges discharges new_pat_subst false in
		let pi_spec_vars = Symbolic_State_Functions.pf_of_substitution spec_vars_subst in
		let pi_unfold_args = Symbolic_State_Functions.pf_of_substitution subst_unfold_args in 
		let pi_subst = Symbolic_State_Functions.pf_of_substitution subst in
		let pi' = pi_discharges @ pi_spec_vars @ pi_unfold_args @ pi_subst in 
		let pi = pi' @ pi_1' @ pi_0' in 
		let gamma_0 = Symbolic_State_Functions.gamma_substitution gamma_0 subst true in 
		let gamma_0' = Symbolic_State_Functions.gamma_substitution gamma_0' subst true in 
		extend_gamma gamma_0 gamma_0';
		let gamma_1'' = Symbolic_State_Functions.gamma_substitution gamma_1 new_pat_subst false in
		extend_gamma gamma_0 gamma_1''; 
		let gamma = gamma_0 in 
		JSIL_Logic_Normalise.extend_typing_env_using_assertion_info pi gamma;
		Printf.printf "substitutions immediately before sat check.\nSubst:\n%s\nPat_Subst:\n%s\n"
			(JSIL_Memory_Print.string_of_substitution subst)
			(JSIL_Memory_Print.string_of_substitution new_pat_subst);
		print_endline (Printf.sprintf "About to check if the following is SATISFIABILITY of:\n%s\nGiven the GAMMA:\n%s\n"
			(JSIL_Print.str_of_assertion_list pi)
			(	JSIL_Memory_Print.string_of_gamma gamma));
		let sat_check = Pure_Entailment.check_satisfiability pi gamma [] in 
	  sat_check, pi', gamma_0', new_pat_subst in
	
	
	(* STEP 6 - Finally unfold: Sigma_0, Sigma_1, subst, pat_subst, pi, gamma                              *)
	(* subst(Sigma_0) + pat_subst(Sigma_1) + (_, _, pi, gamma, _)                                          *)
	let step_6 subst pat_subst new_pfs new_gamma = 
		let symb_state = Symbolic_State_Functions.symb_state_substitution symb_state subst true in
		let unfolded_symb_state = merge_symb_states symb_state pat_symb_state pat_subst in
		Symbolic_State_Functions.extend_pf (get_pf unfolded_symb_state) (get_solver unfolded_symb_state) new_pfs;
		extend_gamma (get_gamma unfolded_symb_state) new_gamma;
		JSIL_Logic_Normalise.extend_typing_env_using_assertion_info new_pfs (get_gamma unfolded_symb_state);
		unfolded_symb_state in 
		
	(** Now DOING IT **)
	let discharges, subst, pat_subst = step_1 () in 
	match discharges with 
	| Some discharges -> 
		let store_0_var_types, store_1_var_types, stores_are_type_compatible = step_2 () in 
		if (stores_are_type_compatible) 
			then ( 
				let subst_is_sensible, pat_subst_is_sensible = step_3 subst pat_subst in 
				if (subst_is_sensible && pat_subst_is_sensible) 
					then (
						let new_gamma = step_4 store_0_var_types in 
						let sat_check, new_pi, new_gamma, pat_subst = step_5 subst pat_subst discharges new_gamma in 
						if (sat_check) 
							then (
								let unfolded_symb_state = step_6 subst pat_subst new_pi new_gamma in 
								Some unfolded_symb_state  
							) else  ((* Printf.printf "Failed unfolding in step 5\n"; *)None)
					) else  ((* Printf.printf "Failed unfolding in step 3\n"; *)  None) 
			) else ((* Printf.printf "Failed unfolding in step 2\n"; *)  None)
	| None -> (* Printf.printf "Failed unfolding in step 1\n"; *) None
	
	 
	
	
	
	
	
(* OLD UNFOLD - let's pray we never need it again - 

	let update_gamma_from_unfolded_predicate store gamma symb_state =
	let symb_gamma = get_gamma symb_state in
		Hashtbl.iter
		(fun pvar lexpr ->
			let str_lexpr = (JSIL_Print.string_of_logic_expression lexpr false) in
			(match lexpr with
			| LVar lvar ->
			  if (Hashtbl.mem gamma pvar) then
			  begin
			    let ltype = Hashtbl.find gamma pvar in
					if (not (Hashtbl.mem symb_gamma lvar))
						then update_gamma symb_gamma lvar (Some ltype)
			  end
			| _ -> () )) store;
		symb_gamma in


let pat_subst = init_substitution [] in
			let subst = init_substitution [] in
			let pat_store = get_store pred_symb_state in
			
			let symb_state = Symbolic_State_Functions.symb_state_replace_gamma symb_state (update_gamma_from_unfolded_predicate store (get_gamma pred_symb_state) symb_state) in
			Printf.printf "\nUnfolding the predicate.\n\nSymb_State: %s\n\nPat_Symb_State: %s\n\n" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state) (JSIL_Memory_Print.string_of_shallow_symb_state pred_symb_state);
			Printf.printf "Calling store: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_store store false); 
			let discharges = Structural_Entailment.unify_stores pat_store store pat_subst (Some subst) (pfs_to_list (get_pf symb_state)) (get_solver symb_state) (get_gamma symb_state) in
			
			let sensible_subst = Symbolic_State_Functions.is_sensible_subst subst (get_gamma symb_state) (get_gamma pred_symb_state) in
			
			(match sensible_subst, discharges with
			| true, Some discharges ->
					(* Printf.printf "Current pred symbolic state: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state pred_symb_state); *)
					(* Printf.printf "I need to apply the following subst in the current symbolic store: %s\n"
						(JSIL_Memory_Print.string_of_substitution subst);
					Printf.printf "I need to apply the following subst in the pattern symbolic store: %s\n"*)
					(JSIL_Memory_Print.string_of_substitution pat_subst);
					let new_symb_state : symbolic_state = Symbolic_State_Functions.copy_symb_state symb_state in
					let (new_symb_state : symbolic_state) = Symbolic_State_Functions.symb_state_substitution new_symb_state subst true in
					Symbolic_State_Functions.symb_state_add_subst_as_equalities new_symb_state subst (get_pf new_symb_state) spec_vars;
					(* Printf.printf "Symbolic state after substitution: \n%s\n" (JSIL_Memory_Print.string_of_shallow_symb_state new_symb_state);
					Printf.printf "Pred Symb_sate:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state pred_symb_state); *)
					let pat_subst = compose_partial_substitutions subst pat_subst in
					let unfolded_symb_state = Structural_Entailment.safe_merge_symb_states new_symb_state pred_symb_state pat_subst in
					(match unfolded_symb_state with
					| Some unfolded_symb_state ->
						(*Printf.printf "pred symbolic state at the middle: %s\n" (JSIL_Memory_Print.string_of_shallow_symb_state pred_symb_state);*)
						let spec_vars_subst = filter_substitution subst spec_vars in

						let pf = get_pf unfolded_symb_state in
						let solver = get_solver unfolded_symb_state in
						let gamma =  (get_gamma unfolded_symb_state) in
						let new_pfs = Symbolic_State_Functions.pf_of_substitution spec_vars_subst in
						let new_pfs_subst0 = Symbolic_State_Functions.pf_of_substitution subst0 in
						let pf_discharges = Structural_Entailment.pf_list_of_discharges discharges pat_subst false in
						
						Printf.printf "The discharges to prove are: %s\n" (JSIL_Print.str_of_assertion_list pf_discharges);

						Symbolic_State_Functions.extend_pf pf solver new_pfs;
						Symbolic_State_Functions.extend_pf pf solver new_pfs_subst0;
						Symbolic_State_Functions.extend_pf pf solver pf_discharges;

						JSIL_Logic_Normalise.extend_typing_env_using_assertion_info new_pfs gamma;
						JSIL_Logic_Normalise.extend_typing_env_using_assertion_info new_pfs_subst0 gamma;
						JSIL_Logic_Normalise.extend_typing_env_using_assertion_info pf_discharges gamma;

						(* Printf.printf "\nJust before substitution.\n\nSymb_State: %s\n\nPat_Symb_State: %s\n\n" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state) (JSIL_Memory_Print.string_of_shallow_symb_state pred_symb_state); *)
						(* Printf.printf " subst: %s pat_subst: %s\n" (JSIL_Memory_Print.string_of_substitution subst) (JSIL_Memory_Print.string_of_substitution pat_subst); *)

						let pat_pf_existentials = get_subtraction_vars (get_pf_list pred_symb_state) pat_subst in
						let gammas_unifiable = Structural_Entailment.unify_gamma (get_gamma pred_symb_state) gamma pat_store pat_subst pat_pf_existentials in
						(* Printf.printf "Are gammas unifiable? Answer, bitch! %b\n" gammas_unifiable;
						Printf.printf "\n\nSymb_State before simplification: %s\n\n" (JSIL_Memory_Print.string_of_shallow_symb_state unfolded_symb_state);*)

						(* Go through the pure formulae. Look for l-nth and ways to simplify it. Add types to gamma. *)
						let unfolded_symb_state = simplify_symb_state unfolded_symb_state in
						(* Printf.printf "\n\nSymb_State after simplification: %s\n\n" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state); *)

						Printf.printf "I unfolded the following symbolic state:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state unfolded_symb_state);
						let satisfiability_check = Pure_Entailment.check_satisfiability (get_pf_list unfolded_symb_state) gamma [] in
						(* let discharges_check = Entailment_Engine.check_entailment [] pf pf_discharges gamma in *)
						if (satisfiability_check)
							then (
								Printf.printf "Checked the pure part of the unfolding!!\n";
								loop rest_pred_defs (unfolded_symb_state :: symb_states))
							else (
								Printf.printf "Could NOT check the pure part of the unfolding. satisfiability_check: %b.\n" satisfiability_check;
								Printf.printf "pf_discharges: %s\n" (JSIL_Print.str_of_assertion_list pf_discharges);
								loop rest_pred_defs symb_states)
					| None -> loop rest_pred_defs symb_states)
			| _, _ -> loop rest_pred_defs symb_states)
*)
	
	
	
	
			
			
					
	
	
	
	
	


