open JSIL_Syntax
open JSIL_Print
open Symbolic_State
open JSIL_Logic_Utils

(***************************)
(** Unification Algorithm **)
(***************************)

let must_be_equal le_pat le pi gamma subst =
	let le_pat = lexpr_substitution le_pat subst true in
		print_debug_petar (Printf.sprintf "Must be equal: %s = %s" (JSIL_Print.string_of_logic_expression le_pat false) (JSIL_Print.string_of_logic_expression le false));
		let result = Pure_Entailment.is_equal le_pat le pi gamma in
		result

let must_be_different le_pat le pi gamma subst =
	let le_pat = lexpr_substitution le_pat subst true in
	let result = Pure_Entailment.is_different le_pat le pi gamma in
	result

let more_lenient_must_be_equal le_pat le pi gamma subst =
	let eq_ass_red = Simplifications.reduce_assertion_no_store gamma pi (LEq (le_pat, le)) in
	(match eq_ass_red with
	| LTrue -> true
	| LFalse -> false
	| LEq (le_pat, le) ->
		(match le_pat with
		| LVar v ->
				(match Hashtbl.mem subst v with
				| false -> extend_subst subst v le; true
				| true -> must_be_equal le_pat le pi gamma subst)
		| _ -> must_be_equal le_pat le pi gamma subst))

(*
 * Substitution must maintain types
 *)
let gamma_subst_test lvar lexpr pat_gamma gamma source =
	try (
		(* Get the type of lvar in pat_gamma *)
		let t = Hashtbl.find pat_gamma lvar in
		(* Get the corresponding type in gamma *)
		let t', _, _ = JSIL_Logic_Utils.type_lexpr gamma lexpr in
			print_debug_petar (Printf.sprintf "GST: %s\n\tVariable %s is in pat_gamma with type %s" source lvar (JSIL_Print.string_of_type t));
			print_debug_petar (Printf.sprintf "\tIts substitute is of type %s" (Option.map_default (fun x -> JSIL_Print.string_of_type x) "Not yet typable" t'));
			(match t' with
			(* Both are typable and types are not equal *)
			| Some t' when (t' <> t) -> print_debug_petar "\tType mismatch. Cannot unify"; false
			(* Both are typable and types are equal, or the expression cannot be typed for the moment *)
			| _ -> print_debug_petar "\tCan proceed."; true)
	) with | _ -> true

let unify_stores (pat_store : symbolic_store) (store : symbolic_store) (pat_subst : substitution) (subst: substitution option) (pfs : jsil_logic_assertion list) (pat_gamma : typing_environment) (gamma : typing_environment) : (jsil_logic_expr * jsil_logic_expr) list  =
	let start_time = Sys.time () in
	try (
	print_debug (Printf.sprintf "Unifying stores:\nStore: %s\nPat_store: %s"
		(Symbolic_State_Print.string_of_shallow_symb_store store false)
		(Symbolic_State_Print.string_of_shallow_symb_store pat_store false));
	let discharges =
		Hashtbl.fold
			(fun var pat_lexpr discharges ->
				let lexpr = try Hashtbl.find store var with _ -> raise (SymbExecFailure (US (VariableNotInStore var))) in
				let rec spin_me_round pat_lexpr lexpr discharges =
				(match pat_lexpr, lexpr with

				| LLit pat_lit, LLit lit ->
					if ((compare lit pat_lit) = 0)
						then discharges
						else raise (SymbExecFailure (US (ValueMismatch (var, pat_lexpr, lexpr))))

				| ALoc pat_aloc, ALoc aloc ->
					extend_subst pat_subst pat_aloc (ALoc aloc);
					discharges

				| ALoc pat_aloc, (LLit (Loc loc)) ->
					extend_subst pat_subst pat_aloc (LLit (Loc loc));
					discharges

				| LVar lvar, le ->
					if (Hashtbl.mem pat_subst lvar)
						then (
							let current = Hashtbl.find pat_subst lvar in
							if ((current = le) && (Option.is_none subst)) then discharges else (
							(match current with
							| LVar _ -> ((LVar lvar, lexpr) :: discharges)
							| _ ->
								if Pure_Entailment.is_equal current lexpr (DynArray.of_list pfs) gamma
									then discharges
									else raise (SymbExecFailure (US (ValueMismatch (var, pat_lexpr, lexpr)))))))
						else (
								extend_subst pat_subst lvar lexpr;
								let subst_ok = gamma_subst_test lvar lexpr pat_gamma gamma "unify_stores" in
								(match subst_ok with
								| true -> discharges
								| false -> raise (SymbExecFailure (US (ValueMismatch (var, pat_lexpr, lexpr))))))

				| ALoc pat_aloc, LVar lvar ->
					print_debug_petar (Printf.sprintf "So, in unify_stores: Aloc %s, Lvar %s" pat_aloc lvar);
					let loc = Simplifications.resolve_location lvar (DynArray.of_list pfs) in
					
					print_debug_petar (Printf.sprintf "Location resolution for %s with pfs %s finished: %s" 
					lvar 
					(Symbolic_State_Print.string_of_shallow_p_formulae (DynArray.of_list pfs) false)
					(match loc with
					| Some loc -> JSIL_Print.string_of_logic_expression loc false
					| None -> "None"));
					
					(match loc with
					| Some loc ->
						print_debug_petar (Printf.sprintf "I managed to resolve location and I know that %s = %s\n" lvar (JSIL_Print.string_of_logic_expression loc false));
						extend_subst pat_subst pat_aloc loc; discharges
					| None     ->
						(match subst with
						| None ->
								print_debug_petar (Printf.sprintf "No substitution, cannot unify stores.");
								raise (SymbExecFailure (US NoSubstitution))
						| Some subst ->
							print_debug_petar (Printf.sprintf "I could not resolve the location and I am creating a new location.");
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
						if (Pure_Entailment.check_entailment SS.empty pfs [ (LEq (LVar lvar, LLit lit)) ] gamma)
							then discharges
							else raise (SymbExecFailure (US (ValueMismatch (var, pat_lexpr, lexpr)))))

				| LEList el1, LEList el2 ->
					if (List.length el1 = List.length el2) then
					begin
						(List.fold_left2
						(fun ac x y ->
							let new_ones = spin_me_round x y [] in
							new_ones @ ac)
						[] el1 el2) @ discharges
					end
					else raise (SymbExecFailure (US (ValueMismatch (var, pat_lexpr, lexpr))))

				| le_pat, le -> (le_pat, le) :: discharges) in
				spin_me_round pat_lexpr lexpr discharges)
			pat_store
			[] in
	let end_time = Sys.time () in
	JSIL_Syntax.update_statistics "unify_stores" (end_time -. start_time);
	discharges)
	with
	| e -> (match e with
		| SymbExecFailure (US _) ->
				let end_time = Sys.time () in
				JSIL_Syntax.update_statistics "unify_stores" (end_time -. start_time);
				raise e)


let rec unify_lexprs le_pat (le : jsil_logic_expr) p_formulae (gamma: typing_environment) (subst : (string, jsil_logic_expr) Hashtbl.t) : (bool * ((string * jsil_logic_expr) list option)) =
	let start_time = Sys.time () in
	print_debug_petar (Printf.sprintf ": %s versus %s" (JSIL_Print.string_of_logic_expression le_pat false)  (JSIL_Print.string_of_logic_expression le false));
	let result = (match le_pat with

	| LVar var
	| ALoc var ->
		(try
			let le_pat_subst = (Hashtbl.find subst var) in
			if (Pure_Entailment.is_equal le_pat_subst le p_formulae (* solver *) gamma)
				then (true,  None)
				else (false, None)
		with _ -> (* print_debug_petar (Printf.sprintf "Abstract location or variable not in subst: %s %s" var (JSIL_Print.string_of_logic_expression le false)); *)
			(true, Some [ (var, le) ]))

	| LLit _
	| LNone ->
		if (Pure_Entailment.is_equal le_pat le p_formulae gamma)
			then (true, None)
			else (false, None)

	| le_pat when (isList le_pat && isList le && (match le with | LVar _ -> false | _ -> true)) ->
			print_debug_petar (Printf.sprintf " ULEXPRLIST: %s %s" (JSIL_Print.print_lexpr le_pat) (JSIL_Print.print_lexpr le)); 
			let osubst = Simplifications.unify_lists le_pat le false in
			(match osubst with
			| None, _ 
			| Some false, _ -> 
				let le_pat' = lexpr_substitution le_pat subst false in
				if Pure_Entailment.is_equal le le_pat' p_formulae gamma 
					then (true, None)
					else (false, None)
			
			| Some true, sb ->

				let rec loop sb outcome constraints =
					(match sb with
					| [] -> (outcome, constraints)
					| (le1, le2) :: rest ->
						let olf, cl = unify_lexprs le1 le2 p_formulae gamma subst in
						(match olf with
						| false -> (false, None)
						| true ->
								let org, cr = loop rest true None in
								(match org with
								| false -> (false, None)
								| true -> (true, Some (Option.default [] cl @ Option.default [] cr))))
					) in

				loop sb true None)

	| LEList ple ->
		(* Printf.printf "Now, are these lists equal?\n"; *)
		let list_eq lx ly = List.fold_left2
			(fun (ac1, ac2) x y ->
				(* Printf.printf "%s == %s? " (JSIL_Print.string_of_logic_expression x false) (JSIL_Print.string_of_logic_expression y false); *)
				let (ch, oops) = unify_lexprs x y p_formulae (* solver *) gamma subst in
				(* Printf.printf "%b\n" ch; *)
				match oops with
				 | None -> (ac1 && ch, ac2)
				 | Some formulae -> (ac1 && ch,
					 (match ac2 with
					  | None -> Some formulae
					  | Some fs -> Some (fs @ formulae)))) (true, None) lx ly in
		(match le with
		| LLit (LList le') ->
	   		let lle = List.length ple in
			let lle' = List.length le' in
			if (lle = lle') then
				let le'' = List.map (fun x -> LLit x) le' in
				list_eq ple le''
			else (false, None)
		| LEList le' ->
	   		let lle = List.length ple in
			let lle' = List.length le' in
			if (lle = lle')
				then list_eq ple le'
				else (false, None)
		| le' ->
			(* print_debug_petar "Second thingy not a list."; *)
			let le'' = Simplifications.find_me_Im_a_list (Hashtbl.create 1) p_formulae le' in
			let le''' = (match le'' with
			| LVar v ->
					let simpl_pfs, _ = Simplifications.simplify_pfs p_formulae gamma (Some None) in
					let subst = List.filter (fun pf -> (match pf with
					| LEq (LVar w, _) -> v = w
					| _ -> false)) (DynArray.to_list simpl_pfs) in
					assert (List.length subst <= 1);
					(match subst with
					| [] -> None
					| [ (LEq (_, le''')) ] -> Some le''')
			| _ -> None) in
			let le'' =
				if (le'' == le')
					then (if (le''' == None) then le' else (Option.get le'''))
					else le'' in
			(* print_debug_petar (Printf.sprintf "Search says: %s\n" (JSIL_Print.string_of_logic_expression le'' false)); *)
			if (le'' == le') then (false, None)
			else
			begin
				let (is_eq, whatever) = unify_lexprs le_pat le'' p_formulae (* solver *) gamma subst in
				(* Printf.printf "And they aaaare: %b\n" is_eq; *)
				(is_eq, whatever)
			end)

	| _ ->
		more_lenient_must_be_equal le_pat le p_formulae gamma subst, None
	) in
	let end_time = Sys.time () in
	JSIL_Syntax.update_statistics "unify_lexprs" (end_time -. start_time);
	let b, _ = result in print_debug (Printf.sprintf "Result: %b" b);
	result




(**
	Unify a logical field-value pair with the appropriate logical field-value pair in a given field-value list
	@param (pat_field, pat_value)        Field-value pair in the pattern heap
	@param fv_list                       Field-value list in the current heap
	@param p_formulae                    Pure formulae of the current heap
	@param gamma                         Typing environment of the current heap
	@param subst                         Substitution mapping the pattern symb_state to the current symb_state

	@return b1  boolean - the pat_field is for sure equal to one of the fields in fv_list
	@return b2  boolean - the pat_field is for sure different from all the fields in fv_list
    @return (fv_pair, rest_fv_list) option - the pair in fv_list that matches (pat_field, pat_value) and the rest of fv_list
*)
let unify_fv_pair (pat_loc                : string)
                  (loc                    : string)
                  ((pat_field, pat_value) : (jsil_logic_expr * jsil_logic_expr))
				  (fv_list                : symbolic_field_value_list)
				  (p_formulae             : pure_formulae)
				  (gamma                  : typing_environment)
				  (subst                  : substitution)
									: bool * bool * ((symbolic_field_value_list * (jsil_logic_expr * jsil_logic_expr)) option) =

	let rec loop fv_list traversed_fv_list i_have_not_found_the_field_for_sure =

		(* Before trying to unify (pat_field, pat_val) with the rest of the     *)
		(* fv_list, check if the current field and pat_field must be the same.  *)
		(* If they must be the same, the unification fails immediately, because *)
		(* the pat_field is equal to the current field but their expressions    *)
		(* do not coincide.                                                     *)

		let guarded_loop_next_2 e_field e_value rest =
			let new_traversed_field_list = (e_field, e_value) :: traversed_fv_list in
			if (not i_have_not_found_the_field_for_sure)
				then loop rest new_traversed_field_list false
				else loop rest new_traversed_field_list (must_be_different pat_field e_field p_formulae gamma subst) in

		let guarded_loop_next_1 e_field e_value rest =
			if (must_be_equal pat_field e_field p_formulae gamma subst)
				then raise (SymbExecFailure (UH (FieldValueMismatch (pat_loc, pat_field, pat_value, loc, e_field, e_value))))
				else guarded_loop_next_2 e_field e_value rest in

		match fv_list with
		| [] -> (false, i_have_not_found_the_field_for_sure, None)
		| (e_field, e_value) :: rest ->
			(* Unify the field name expressions *)
			let (bf, fu) = unify_lexprs pat_field e_field p_formulae gamma subst in
			(match bf with
			| true ->
			  (* Unify the field value expressions *)
			  let (bv, vu) = unify_lexprs pat_value e_value p_formulae gamma subst in
			  (match bv with
				| true ->
					(* check if the unifiers for the field and value are compatible *)
					if (Symbolic_State_Utils.update_subst2 subst fu vu p_formulae gamma)
						then (false, false, Some ((traversed_fv_list @ rest), (e_field, e_value)))
						else guarded_loop_next_1 e_field e_value rest
				(* Value not unified *)
				| false -> guarded_loop_next_1 e_field e_value rest)
			(* Name not unified *)
			| false -> guarded_loop_next_2 e_field e_value rest) in
	loop fv_list [] true



(** Order the field-value pairs in pat_fv_lists putting:
	 		- first : concrete field names and concrete values
	 		- second: concrete field names and non-concrete values
  		- third : non-concrete field names and concrete values
	  	- fourth: the rest

	@param fv_list        Field-value pair in the pattern heap
	@return ordered_list
*)
let order_fv_list fv_list =
	let rec loop fv_list props_and_values props values other =
		match fv_list with
		| [] ->  props_and_values @ props @ values @ other
		| (prop_name, prop_value) :: rest ->
			(match prop_name, prop_value with
			| LLit _, LLit _ -> loop rest ((prop_name, prop_value) :: props_and_values) props values other
			| LLit _, _  -> loop rest props_and_values ((prop_name, prop_value) :: props) values other
			| _, LLit _ -> loop rest props_and_values props ((prop_name, prop_value) :: values) other
			| _, _ -> loop rest props_and_values props values ((prop_name, prop_value) :: other)) in
	loop fv_list [] [] [] []



(**
	Unify two logical field-value lists

	@param pat_fv_list      Field-value list in the pattern heap
	@param fv_list          Field-value list in the current heap
	@param def_val   	      Default value of the object corresponding to fv_list
	@param p_formulae       Pure formulae of the current heap
	@param gamma            Typing environment of the current heap
	@param subst            Substitution mapping the pattern symb_state to the current symb_state
*)
let unify_symb_fv_lists (pat_loc     : string)
                        (loc         : string)
                        (pat_fv_list : symbolic_field_value_list)
						(fv_list     : symbolic_field_value_list)
						(domain      : jsil_logic_expr option)
						(p_formulae  : pure_formulae)
						(gamma       : typing_environment)
						(subst       : substitution)
								: (symbolic_field_value_list * symbolic_field_value_list * symbolic_discharge_list * (jsil_logic_expr option)) option =

	print_time_debug ("unify_symb_fv_lists");

	let unify_explicit_none_against_default_none (pat_field : jsil_logic_expr)
		(pat_val : jsil_logic_expr) (domain : jsil_logic_expr option) =
		print_time_debug ("unify_explicit_none_against_default_none");
		let (b_pv, unifier) = unify_lexprs pat_val LNone p_formulae gamma subst in
		match b_pv, domain with
		| true, Some domain
			when Symbolic_State_Utils.update_subst1 subst unifier ->
			let a_set_inclusion = LNot (LSetMem (pat_field, domain)) in
			if (Pure_Entailment.check_entailment SS.empty (pfs_to_list p_formulae) [ a_set_inclusion ] gamma)
				then (
					print_debug (Printf.sprintf "USFVL: My domain is: %s" (print_lexpr domain));
					let new_domain = LSetUnion [ domain; LESet [ pat_field ] ] in
					let new_domain = Symbolic_State_Utils.normalise_lexpr gamma new_domain in
					let new_domain = Simplifications.reduce_expression_no_store gamma p_formulae new_domain in
					Some new_domain
				) else raise (SymbExecFailure (Impossible (Printf.sprintf "Could not prove none-cell not in domain : #1 : %s not in %s with pat_val %s" (print_lexpr pat_field) (print_lexpr domain) (print_lexpr pat_val))))
		| _, _ -> raise (SymbExecFailure (Impossible (Printf.sprintf "Could not prove none-cell not in domain : #2 : %s not in %s with pat_val %s" (print_lexpr pat_field) (Option.map_default print_lexpr "No domain" domain) (print_lexpr pat_val)))) in

	let rec loop (fv_list : symbolic_field_value_list) (pat_list : symbolic_field_value_list)
		(matched_fv_list : symbolic_field_value_list) (discharges : symbolic_discharge_list) (cur_domain : jsil_logic_expr option) =
		print_time_debug ("unify_symb_fv_lists : loop");
		match pat_list with
		| [] -> Some (fv_list, matched_fv_list, discharges, cur_domain)
		| (pat_field, pat_val) :: rest_pat_list ->
			let pf_equal, pf_different, res = unify_fv_pair pat_loc loc (pat_field, pat_val) fv_list p_formulae gamma subst in

			(match pf_equal, pf_different, res with
			| false, _,  None ->
				let s_pat_field = lexpr_substitution pat_field subst true in
				let new_domain = unify_explicit_none_against_default_none s_pat_field pat_val cur_domain in
				loop fv_list rest_pat_list matched_fv_list discharges new_domain

			| _, _, Some (rest_fv_list, matched_fv_pair) ->
				loop rest_fv_list rest_pat_list (matched_fv_pair :: matched_fv_list) discharges cur_domain

			| _, _, _ -> raise (SymbExecFailure (Impossible "unify_symb_fv_lists: impossible matching case"))) in
	let order_pat_list = order_fv_list pat_fv_list in
	loop fv_list order_pat_list [] [] domain


let unify_domains (dom : jsil_logic_expr option) (pat_dom : jsil_logic_expr option)
	(q_fv_list : symbolic_field_value_list) (subst : substitution)
	(pfs : pure_formulae) (gamma : typing_environment)
		: symbolic_field_value_list * (jsil_logic_expr option) =

	print_time_debug ("unify_domains");

	let q_fv_list_strs = List.map
		(fun (field, value) ->
			let field_str = JSIL_Print.string_of_logic_expression field false in
			let value_str = JSIL_Print.string_of_logic_expression value false in
			"(" ^ field_str ^ ", " ^ value_str ^ ")") q_fv_list in
	let q_fv_list_str = String.concat ", " q_fv_list_strs in
	print_debug (Printf.sprintf "unify_domains: q_fv_list: %s\n" q_fv_list_str);


	let rec find_missing_none (missing_field : jsil_logic_expr)
			(none_q_v_list : symbolic_field_value_list) (traversed_none_q_v_list : symbolic_field_value_list) =
		(match none_q_v_list with
		| []                      -> raise (SymbExecFailure (Impossible "this is quite possible - but for the moment, it stays like this. unify_domains - find_missing_none failed"))
		| (f_name, f_val) :: rest_none_q_v_list ->
			if (Pure_Entailment.is_equal f_name missing_field pfs gamma)
				then rest_none_q_v_list @ traversed_none_q_v_list
				else find_missing_none missing_field rest_none_q_v_list ((f_name, f_val) :: traversed_none_q_v_list)) in

	let rec find_missing_nones (fields_to_find : jsil_logic_expr list) (none_q_v_list : symbolic_field_value_list) =
		(match fields_to_find with
		| [] -> none_q_v_list
		| f_name :: rest_fields ->
			print_debug (Printf.sprintf "I need to find %s caralho\n" (JSIL_Print.string_of_logic_expression f_name false));
			let rest_none_q_v_list = find_missing_none f_name none_q_v_list [] in
			find_missing_nones rest_fields (rest_none_q_v_list @ none_q_v_list)) in

	let rec unify_some_domains dom pat_dom =
		let none_q_v_list, new_q_v_list = List.partition (fun (field, value) -> (value = LNone)) q_fv_list in
		let s_pat_dom = lexpr_substitution pat_dom subst true in
		let domain_difference = Symbolic_State_Utils.normalise_lexpr gamma (LBinOp (dom, SetDiff, s_pat_dom)) in
		let domain_difference = Simplifications.reduce_expression_using_pfs_no_store gamma pfs domain_difference in

		let domain_frame_difference = Symbolic_State_Utils.normalise_lexpr gamma (LBinOp (s_pat_dom, SetDiff, dom)) in
		let domain_frame_difference = Simplifications.reduce_expression_using_pfs_no_store gamma pfs domain_frame_difference in
		let domain_difference, domain_frame_difference =
		(match domain_difference, domain_frame_difference with
			| LESet domain_difference, LESet domain_frame_difference -> domain_difference, domain_frame_difference
			| ooga, booga ->
					raise (SymbExecFailure (Impossible (Printf.sprintf "Cannot currently handle: DD %s, DFD %s" (print_lexpr ooga) (print_lexpr booga))))) in

		let none_q_v_list_strs = List.map (fun (field, value) -> JSIL_Print.string_of_logic_expression field false) none_q_v_list in
		let none_q_v_list_str = String.concat ", " none_q_v_list_strs in
		print_debug (Printf.sprintf "caralho none_q_v_list: %s\n" none_q_v_list_str);

		let non_matched_none_fields = find_missing_nones domain_difference none_q_v_list in
		let new_none_q_v_list = List.map (fun le -> (le, LNone)) domain_frame_difference in

		new_q_v_list @ non_matched_none_fields @ new_none_q_v_list in

	match dom, pat_dom with
	| None, None             -> q_fv_list, None
	| None, Some _           -> raise (SymbExecFailure (Impossible "empty fields in the pat heap but no empty fields in the calling heap"))
	| Some _, None           -> q_fv_list, dom
	| Some dom, Some pat_dom ->
		unify_some_domains dom pat_dom, None



let unify_symb_heaps (pat_heap : symbolic_heap) (heap : symbolic_heap) pure_formulae pat_pfs pat_gamma gamma (subst : substitution) : symbolic_heap * (jsil_logic_assertion list) * symbolic_discharge_list =
	print_debug (Printf.sprintf "Unify heaps %s \nand %s \nwith substitution: %s\nwith pure formulae: %s\nwith gamma: %s"
		(Symbolic_State_Print.string_of_shallow_symb_heap pat_heap false)
		(Symbolic_State_Print.string_of_shallow_symb_heap heap false)
		(Symbolic_State_Print.string_of_substitution subst)
		(Symbolic_State_Print.string_of_shallow_p_formulae pure_formulae false)
		(Symbolic_State_Print.string_of_gamma gamma));

	let start_time = Sys.time () in
	let quotient_heap = LHeap.create 1021 in
	let pat_heap_domain : string list = heap_domain pat_heap subst in
	print_debug_petar (Printf.sprintf "PatHeapDomain: %s" (String.concat ", " pat_heap_domain));

	Hashtbl.iter 
		(fun k v -> 
			let loc = Simplifications.resolve_location k pat_pfs in
			(match loc with
			| None -> ()
			| Some loc -> (match loc with
				| ALoc loc
				| LLit (Loc loc) -> Hashtbl.replace subst loc v
				| _ -> ()))
		) subst;

	let rec pick_loc_that_exists_in_both_heaps locs traversed_locs  =
		match locs with
		| [] ->
			let msg = Printf.sprintf "DEATH. pick_pat_loc failed to pick next. Remaining locs: %s." (String.concat ", " traversed_locs) in
			print_debug (msg);
			raise (SymbExecFailure (UH (FloatingLocations traversed_locs)))
		| loc :: rest ->
			if (LHeap.mem heap loc)
				then
					(Hashtbl.add subst loc (ALoc loc);
					loc, (traversed_locs @ rest))
				else pick_loc_that_exists_in_both_heaps rest (traversed_locs @ [ loc ]) in

	let pick_pat_loc (locs_to_visit : string list) subst : string * (string list) =
		print_debug_petar "pick_pat_loc\n";

		let rec loop (remaining_locs : string list) (traversed_locs : string list) : string * (string list) =
			match remaining_locs with
			(* | [] -> raise (SymbExecFailure (UH (FloatingLocations remaining_locs))) *)
			| [] -> pick_loc_that_exists_in_both_heaps traversed_locs []
			| loc :: rest ->
				if ((not (is_abs_loc_name loc)) || (Hashtbl.mem subst loc))
					then loc, (traversed_locs @ rest)
					else loop rest (traversed_locs @ [ loc ]) in
		loop locs_to_visit [] in

	try

		let rec loop locs_to_visit pfs discharges =
			(match locs_to_visit with
			| [] -> (pfs, discharges)
			| _ ->
				let pat_loc, rest_locs = pick_pat_loc locs_to_visit subst in
				print_debug (Printf.sprintf "Location: %s" pat_loc);
				if (Hashtbl.mem subst pat_loc) then
					(
						let subst_val = Hashtbl.find subst pat_loc in
						print_debug (Printf.sprintf "Substitution: %s" (print_lexpr subst_val))
					);
				(match heap_get pat_heap pat_loc with
				| Some (pat_fv_list, pat_domain) ->
						let loc = (match (is_lit_loc_name pat_loc) with
						| true -> pat_loc
						| false -> (match (Hashtbl.mem subst pat_loc) with
							| false -> raise (SymbExecFailure (UH (CannotResolvePatLocation pat_loc)))
							| true ->
								let le = Hashtbl.find subst pat_loc in
								(match le with
								| LLit (Loc loc) -> loc
								| ALoc loc -> loc
								| LVar v ->
									print_debug (Printf.sprintf "matched a pattern loc with the logical variable %s!\n" v);

									let loc = try Simplifications.resolve_location_loc v pure_formulae with _ -> None in
									(match loc with
									| Some loc ->
										(print_debug (Printf.sprintf "find_me_Im_a_loc returned: %s!\n" loc);
										Hashtbl.replace subst pat_loc (ALoc loc);
										loc)
									| None ->
										(print_debug "find_me_Im_a_loc failed!\n";
										raise (SymbExecFailure (UH (CannotResolvePatLocation pat_loc)))))
					  		| _ -> raise (SymbExecFailure (UH (CannotResolvePatLocation pat_loc)))))) in
						let fv_list, (domain : jsil_logic_expr option) =
							(try LHeap.find heap loc with _ -> raise (SymbExecFailure (UH (CannotResolveLocation loc)))) in


						let fv_lists = unify_symb_fv_lists pat_loc loc pat_fv_list fv_list domain pure_formulae gamma subst in
						(match fv_lists with
						| Some (new_fv_list, matched_fv_list, new_discharges, new_domain) ->
							let new_pfs : jsil_logic_assertion list = make_all_different_pure_assertion new_fv_list matched_fv_list in
							let new_fv_list, new_domain = unify_domains new_domain pat_domain new_fv_list subst pure_formulae gamma in 
							LHeap.replace quotient_heap loc (new_fv_list, new_domain);
							print_debug_petar (Printf.sprintf "fv_lists unified successfully");
							print_debug_petar (Printf.sprintf "QH: %s" (Symbolic_State_Print.string_of_shallow_symb_heap quotient_heap false));
							loop rest_locs (new_pfs @ pfs) (new_discharges @ discharges)
						| None -> raise (SymbExecFailure (Impossible "unify_symb_heaps: unify_symb_fv_lists returned None")))
					| _ -> raise (SymbExecFailure (UH PatternHeapWithDefaultValue)))) in

		let (pfs : (jsil_logic_assertion list)), (discharges: (symbolic_discharge_list)) = loop pat_heap_domain [] [] in

		LHeap.iter
			(fun loc (fv_list, def) ->
				try
					let (fv_list, domain) = LHeap.find quotient_heap loc in
					if (fv_list = [] && (domain = None || domain = Some (LESet []))) then 
							while (LHeap.mem quotient_heap loc) do LHeap.remove quotient_heap loc done
				with _ ->
					LHeap.add quotient_heap loc (fv_list, def))
			heap;


		let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "unify_symb_heaps" (end_time -. start_time);
		print_debug_petar (Printf.sprintf "End of unify_symb_heaps: do enjoy the quotient_heap: %s" (Symbolic_State_Print.string_of_shallow_symb_heap quotient_heap false));
		quotient_heap, pfs, discharges
	with
	| e ->
		(match e with
		| SymbExecFailure _ ->
				let end_time = Sys.time () in
				JSIL_Syntax.update_statistics "unify_symb_heaps" (end_time -. start_time);
				raise e
		| _ -> raise e)

(*******************************************************************)
(*******************************************************************)
(*******************************************************************)

(* Generating substitutions for predicate lists *)
let get_unification_candidates
			(pat_preds : (string * (jsil_logic_expr list)) DynArray.t)
			(preds : (string * (jsil_logic_expr list)) DynArray.t)
			p_formulae
			gamma
			(subst : substitution) =
	print_debug ("Entering fully_unify_pred_list_against_pred_list");
	let pat_pred_len = DynArray.length pat_preds in
	(* A queue of so-far-unified + remaining-to-be-unified predicates *)
	let ps :
		(((string * (jsil_logic_expr list)) option) DynArray.t *
		 ((string * (jsil_logic_expr list))) DynArray.t *
		 ((string * (jsil_logic_expr list))) list) Queue.t = Queue.create() in
	(* We start from an empty unified DynArray and all pat_preds remaining *)
	if (pat_pred_len > 0) then Queue.add (DynArray.create(), preds, []) ps;
	for i = 0 to (pat_pred_len - 1) do
		(* Get the current pat_pred to unify *)
		let cpp_name, cpp_params = DynArray.get pat_preds i in
		while (let unified_preds, _, _ = Queue.peek ps in DynArray.length unified_preds = i) do
			let unified_preds, preds_to_unify, non_unified_preds = Queue.pop ps in
			let pred_len = DynArray.length preds_to_unify in
			let found = ref false in
			for j = 0 to (pred_len - 1) do
				let cp_name, cp_params = DynArray.get preds_to_unify j in
				if (cp_name = cpp_name) then
					begin
						found := true;
						let new_up = DynArray.copy unified_preds in
						let new_pu = DynArray.copy preds_to_unify in
							DynArray.add new_up (Some (cp_name, cp_params));
							DynArray.delete new_pu j;
							Queue.push (new_up, new_pu, non_unified_preds) ps;
					end
			done;
			if (not !found) then
				begin
					let new_up = DynArray.copy unified_preds in
					let new_pu = DynArray.copy preds_to_unify in
					DynArray.add new_up None;
					Queue.push (new_up, new_pu, (cpp_name, cpp_params) :: non_unified_preds) ps;
				end
		done;
	done;

	print_debug_petar "----------------------------";
	print_debug_petar (Printf.sprintf "Unification options: %d" (Queue.length ps));
	print_debug_petar (Symbolic_State_Print.string_of_substitution subst);
	Queue.iter (fun (unified, remaining, unmatched) ->
		print_debug_petar "-------\nOption:\n-------";
		List.iter2 (fun (pat_name, pat_params) unified ->
			let unified_str = (match unified with
			| None -> "None"
			| Some (uni_name, uni_params) -> Printf.sprintf "%s(%s)"
				uni_name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) uni_params))) in
			print_debug_petar (Printf.sprintf "%s(%s) \t\t vs.\t\t%s"
				pat_name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) pat_params))
				unified_str
				)
			) (DynArray.to_list pat_preds) (DynArray.to_list unified);
			print_debug_petar "Unmatched predicates:";
			DynArray.iter (fun (name, params) -> print_debug_petar (Printf.sprintf "\t%s(%s)"
				name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) params)))) remaining;
			print_debug_petar "Unmatched pat predicates:";
			List.iter (fun (name, params) -> print_debug_petar (Printf.sprintf "\t%s(%s)"
				name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) params)))) unmatched;

		) ps;
	print_debug_petar "----------------------------";

	let result = Array.of_list
		(List.rev
			(Queue.fold (fun ac (x, y, z) ->
				assert (DynArray.length pat_preds = DynArray.length x);
				let x = List.combine (DynArray.to_list pat_preds) (DynArray.to_list x) in
				let x = List.filter (fun (_, x) -> x <> None) x in
				let x = Array.of_list (List.map (fun (x, y) -> (x, Option.get y)) x) in
				(Hashtbl.copy subst, x, y, z) :: ac) [] ps)) in
		result

(*******************************************************************)

let rec unify_expr_lists pat_list list p_formulae gamma subst =
	(match pat_list, list with
	| [], [] -> true
	| (pat_le :: rest_pat_list), (le :: rest_list) ->
		let (bv, unifier) = unify_lexprs pat_le le p_formulae gamma subst in
		print_debug (Printf.sprintf "Unification: %s vs. %s --> %b" (JSIL_Print.string_of_logic_expression pat_le false) (JSIL_Print.string_of_logic_expression le false) bv);
		if (bv && Symbolic_State_Utils.update_subst1 subst unifier)
			then unify_expr_lists rest_pat_list rest_list p_formulae gamma subst
			else false
	| _, _ -> false)

(*******************************************************************)

let unify_preds subst unifier p_formulae pat_gamma gamma =
	let i = ref 0 in
	let n = Array.length unifier in
	let ok = ref true in
		while (!ok && (!i < n)) do
			let ((pat_pred_name, pat_pred_params), (cand_pred_name, cand_pred_params)) = Array.get unifier !i in
			assert (pat_pred_name = cand_pred_name);
			assert (List.length pat_pred_params = List.length cand_pred_params);
			ok := unify_expr_lists pat_pred_params cand_pred_params p_formulae gamma subst;
			print_debug (Printf.sprintf "Predicate unification: %b" !ok);
			i := !i + 1;
		done;
		if (not !ok)
			then None
			else (
				print_debug (Symbolic_State_Print.string_of_substitution subst);
				try (
				Hashtbl.iter (fun v le ->
					let tv = (match Hashtbl.mem pat_gamma v with
					| true -> Some (Hashtbl.find pat_gamma v)
					| false -> None) in
					let tle, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
					(match tv, tle with
					| Some t1, Some t2 -> if (t1 <> t2) then (
							print_debug (Printf.sprintf "Subst %s with %s of %s, but in gamma it's %s."
								v (JSIL_Print.string_of_logic_expression le false) (JSIL_Print.string_of_type t1) (JSIL_Print.string_of_type t2));
							raise (Failure "!!!"))
					| _, _ -> ())) subst;
					Some subst) with
					| Failure _ -> None)

(*******************************************************************)

(**
 * Returns a list of triples of the form (substitution, preds that haven't been unified, pat_preds that haven't been unified)
 *)
let unify_pred_arrays (pat_preds : predicate_set) (preds : predicate_set) p_formulae pat_gamma gamma (subst : substitution) =
	print_debug "Entering unify_pred_arrays.";

	let result = (match (DynArray.length pat_preds) with
	| 0 -> subst, preds, []
	| _ ->
		let pat_preds = DynArray.to_list pat_preds in
		let preds = DynArray.to_list preds in
		let p_formulae = DynArray.copy p_formulae in
		let gamma = Hashtbl.copy gamma in
		let subst = Hashtbl.copy subst in

		let ps = get_unification_candidates (DynArray.of_list pat_preds) (DynArray.of_list preds) p_formulae gamma subst in

		let i = ref 0 in
		let n = Array.length ps in
		let substs = ref SSS.empty in
		let options = DynArray.create() in
		while (!i < n) do
			let (subst, unifier, unmatched_preds, unmatched_pat_preds) = Array.get ps !i in
			let result = unify_preds subst unifier p_formulae pat_gamma gamma in
			print_debug (Printf.sprintf "Candidate is %s" (Option.map_default (fun x -> "viable.") "not viable." result));
			(match result with
			| None -> ()
			| Some subst ->
				(match (SSS.mem subst !substs) with
				| true -> ()
				| false ->
						let continue = try (
							Hashtbl.iter (fun v le ->
								let (ok : bool) = gamma_subst_test v le pat_gamma gamma "unify_pred_arrays" in
								(match ok with
								| true -> ()
								| false -> raise (Failure ""))) subst;
							true
						) with | Failure _ -> false in
						(match continue with
						| false -> ()
						| true ->
								substs := SSS.add subst !substs;
								DynArray.add options (subst, unmatched_preds, unmatched_pat_preds))));
			i := !i + 1;
		done;

		let options = List.sort
			(fun (_, _, upp1) (_, _, upp2) ->
				let len1 = List.length upp1 in
				let len2 = List.length upp2 in
					compare len1 len2)
					(DynArray.to_list options) in

		print_debug_petar (Printf.sprintf "--------\nActual Outcomes: %d\n--------" (List.length options));
		List.iter (fun (subst, unmatched_preds, unmatched_pat_preds) ->
				print_debug_petar (Printf.sprintf "Substitution: %s" (Symbolic_State_Print.string_of_substitution subst));
				print_debug_petar "Unmatched predicates:";
				DynArray.iter (fun (name, params) -> print_debug_petar (Printf.sprintf "\t%s(%s)"
					name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) params)))) unmatched_preds;
				print_debug_petar "Unmatched pat predicates:";
				List.iter (fun (name, params) -> print_debug_petar (Printf.sprintf "\t%s(%s)"
					name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) params)))) unmatched_pat_preds;
			) options;
		print_debug_petar "-------------------------";

		(match options with
		| [] -> subst, DynArray.of_list preds, pat_preds
		| [ op ] -> op
		| op :: (_ :: _) ->
			(match !interactive with
			| false -> (* THIS IS CRAZY AD-HOC *) op
		  | true ->
				print_debug "Choose branch (0 = None): ";
				let n = read_int() in
				print_debug (Printf.sprintf "The user has chosen the branch: %d" n);
				if (n = 0)
					then (subst, DynArray.of_list preds, pat_preds)
					else (DynArray.get (DynArray.of_list options) (n - 1)))
		)) in

		result

(*******************************************************************)
(*******************************************************************)
(*******************************************************************)

let unify_gamma pat_gamma gamma pat_store subst (ignore_vars : SS.t) : unit =

	print_debug (Printf.sprintf "I am about to unify two gammas\n");
 	print_debug (Printf.sprintf "pat_gamma: %s.\ngamma: %s.\nsubst: %s\n"
		(Symbolic_State_Print.string_of_gamma pat_gamma) (Symbolic_State_Print.string_of_gamma gamma)
		(Symbolic_State_Print.string_of_substitution subst));
	let start_time = Sys.time () in

	try (
		Hashtbl.iter
			(fun var v_type ->
				print_debug_petar (Printf.sprintf "pat_var: (%s : %s) " var (JSIL_Print.string_of_type v_type));
				(match (SS.mem var ignore_vars) with
				| true -> ()
				| false ->
				    print_debug_petar (Printf.sprintf "Substitution! %s" (Symbolic_State_Print.string_of_substitution subst));
						let le = (match (is_lvar_name var) with
							| true -> (match (Hashtbl.mem subst var) with
								| false -> raise (SymbExecFailure (UG (VariableNotInSubstitution var)))
								| true -> Hashtbl.find subst var)
							| false -> (match (store_get_safe pat_store var) with
								| Some le -> JSIL_Logic_Utils.lexpr_substitution le subst true
								| None -> PVar var)) in
						print_debug_petar (Printf.sprintf "Found value: %s" (JSIL_Print.string_of_logic_expression le false));
            print_debug_petar (Printf.sprintf "Substitution! %s" (Symbolic_State_Print.string_of_substitution subst));
						let le_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
						(match le_type with
						| Some le_type ->
							  print_debug_petar (Printf.sprintf "unify_gamma. pat gamma var: %s. le: %s. v_type: %s. le_type: %s"
								var (JSIL_Print.string_of_logic_expression le false) (JSIL_Print.string_of_type v_type) (JSIL_Print.string_of_type le_type));
								if (le_type <> v_type) then raise (SymbExecFailure (UG (TypeMismatch (var, v_type, le, le_type))))
						| None ->
								print_debug_petar (Printf.sprintf "failed unify_gamma. pat gamma var: %s. le: %s. v_type: %s. le_type: None"
								var (JSIL_Print.string_of_logic_expression le false) (JSIL_Print.string_of_type v_type));
								raise (SymbExecFailure (UG (NoTypeForVariable var))))
				)
			)
			pat_gamma;
		print_debug "I unified the gammas successfully.\n";
		let end_time = Sys.time () in
			JSIL_Syntax.update_statistics "unify_gamma" (end_time -. start_time);
	) with
	| e -> (match e with
		| SymbExecFailure (UG g) ->
				let end_time = Sys.time () in
				JSIL_Syntax.update_statistics "unify_gamma" (end_time -. start_time);
				raise e)

(*******************************************************************)
(*******************************************************************)
(*******************************************************************)

let spec_logic_vars_discharge subst (lvars : SS.t) pfs gamma =
	let pf_list = (Symbolic_State.pfs_to_list pfs) in
	let pfs_to_prove : jsil_logic_assertion list =
		SS.fold
			(fun var ac ->
				try
					let le = Hashtbl.find subst var in
					let new_pa = (LEq ((LVar var), le)) in
					new_pa :: ac
				with _ ->
					Hashtbl.add subst var (LVar var);
					ac) lvars [] in

	print_debug_petar (Printf.sprintf "Check if \n (%s) \n entails \n (%s) \n with gamma \n (%s)" (JSIL_Print.str_of_assertion_list pf_list) (JSIL_Print.str_of_assertion_list pfs_to_prove) (Symbolic_State_Print.string_of_gamma gamma));
	let ret = Pure_Entailment.check_entailment SS.empty pf_list pfs_to_prove gamma in
	print_debug_petar (Printf.sprintf "Return value: %b\n" ret);
	ret


let pf_list_of_discharges discharges subst partial =
	let rec loop discharges pfs =
		match discharges with
		| [] -> pfs
		| (le_pat, le) :: rest_discharges ->
			let s_le_pat = JSIL_Logic_Utils.lexpr_substitution le_pat subst partial in
			loop rest_discharges ((LEq (s_le_pat, le)) :: pfs) in
	loop discharges []

(*******************************************************************)
(*******************************************************************)
(*******************************************************************)

(*
let unify_symb_heaps_single_pass
	(pat_heap   : symbolic_heap)      (heap           : symbolic_heap)       (q_heap : symbolic_heap)
  (pat_gamma  : typing_environment) (gamma          : typing_environment)
	(p_formulae : pure_formulae)
	(subst      : substitution)
	(locs       : string list) :
	(**
			Pattern heap and heap remain unchanged. Quotient heap is changed IN PLACE.
			Pattern gamma and gamma remain unchanged.
			Pure formulae remain unchanged. New pure formulae are changed IN PLACE.
			Substitution is changed IN PLACE.

			We return:
				1) the list of locations that still need to be unified
				2) any new pure formulae that come up
				3) any discharges that came up
	*)
	string list * pure_formulae * symbolic_discharge_list =

	(* DEBUG *)
	print_debug "Unify symbolic heaps: single pass : start";
	print_debug (Printf.sprintf "Pattern heap: %s \n Actual heap: %s \n Quotient heap: %s \n Remaining locations: %s \n Substitution: %s"
		(Symbolic_State_Print.string_of_shallow_symb_heap pat_heap false)
		(Symbolic_State_Print.string_of_shallow_symb_heap heap false)
		(Symbolic_State_Print.string_of_shallow_symb_heap q_heap false)
		(String.concat ", " locs)
		(Symbolic_State_Print.string_of_substitution subst));
  (* DEBUG *)

	(* This should totally not be there - for the time being, it stays... *)
	let rec pick_loc_that_exists_in_both_heaps locs traversed_locs  =
		match locs with
		| [] ->
				(* DEBUG *) print_debug (Printf.sprintf "pick_pat_loc failed to pick next location. Remaining locs: %s." (String.concat ", " traversed_locs));
				(None, traversed_locs)
		| loc :: rest ->
			(match LHeap.mem heap loc with
			| true ->
					Hashtbl.add subst loc (ALoc loc);
					(Some loc, traversed_locs @ rest)
			| false -> pick_loc_that_exists_in_both_heaps rest (traversed_locs @ [ loc ])) in

	(* This picks the next location *)
	let pick_pat_loc (locs_to_visit : string list) subst : string option * (string list) =
		let rec loop (remaining_locs : string list) (traversed_locs : string list) : string option * (string list) =
			match remaining_locs with
			| [] -> pick_loc_that_exists_in_both_heaps traversed_locs []
			| loc :: rest ->
				if ((not (is_abs_loc_name loc)) || (Hashtbl.mem subst loc))
					then Some loc, (traversed_locs @ rest)
					else loop rest (traversed_locs @ [ loc ]) in
		loop locs_to_visit [] in

	(* Main loop *)
	let rec loop locs_to_visit pfs discharges =
		print_debug (Printf.sprintf "\nQuotient heap: %s\n" (Symbolic_State_Print.string_of_shallow_symb_heap q_heap false));
		(match locs_to_visit with
		| [] -> ([], pfs, discharges)
		| _ ->
			let pat_loc, rest_locs = pick_pat_loc locs_to_visit subst in
			(match pat_loc with
			(* We are done, we cannot unify more locations *)
			| None -> (rest_locs, pfs, discharges)
			(* We continue, bravely *)
			| Some pat_loc ->
				(* DEBUG *) print_debug (Printf.sprintf "Location: %s" pat_loc);
				(* DEBUG *) if (Hashtbl.mem subst pat_loc) then (let subst_val = Hashtbl.find subst pat_loc in print_debug (Printf.sprintf "Substitution: %s" (print_lexpr subst_val)));
				(match heap_get pat_heap pat_loc with
				| Some (pat_fv_list, pat_def) ->
			  	(if ((pat_def <> LNone) && (pat_def <> LUnknown)) then raise (SymbExecFailure (UH (IllegalDefaultValue pat_def))) else (
						let loc = (match (is_lit_loc_name pat_loc) with
						| true -> pat_loc
						| false -> (match (Hashtbl.mem subst pat_loc) with
							| false -> raise (SymbExecFailure (UH (CannotResolvePatLocation pat_loc)))
							| true ->
								let le = Hashtbl.find subst pat_loc in
								(match le with
								| LLit (Loc loc) -> loc
								| ALoc loc -> loc
								| LVar v ->
									(* DEBUG *) print_debug (Printf.sprintf "Matched a pattern loc with the logical variable %s!\n" v);
									let loc = try Simplifications.aux_find_me_Im_a_loc p_formulae gamma v with _ -> None in
									(match loc with
									| Some loc ->
										(* DEBUG *) (print_debug (Printf.sprintf "find_me_Im_a_loc returned: %s!\n" loc);
										Hashtbl.replace subst pat_loc (ALoc loc);
										loc)
									| None ->
										(* DEBUG *) (print_debug "find_me_Im_a_loc failed!\n";
										raise (SymbExecFailure (UH (CannotResolvePatLocation pat_loc)))))
					  		| _ -> raise (SymbExecFailure (UH (CannotResolvePatLocation pat_loc)))))) in
						let fv_list, (def : jsil_logic_expr) =
							(try LHeap.find heap loc with _ -> raise (SymbExecFailure (UH (CannotResolveLocation loc)))) in
						let fv_lists = unify_symb_fv_lists pat_loc loc pat_fv_list fv_list def p_formulae gamma subst in
						(match fv_lists with
						| Some (new_fv_list, matched_fv_list, new_discharges) when ((pat_def = LNone) && ((List.length new_fv_list) > 0)) ->
							print_debug_petar (Printf.sprintf "fv_lists unified successfully");
							let non_none_fields = List.filter (fun (_, v) -> (v <> LNone)) new_fv_list in
							if (List.length non_none_fields = 0) then
								(LHeap.replace q_heap loc ([], def);
								loop rest_locs pfs (new_discharges @ discharges))
							else raise (SymbExecFailure (UH (ValuesNotNone (loc, non_none_fields))))
						| Some (new_fv_list, matched_fv_list, new_discharges) ->
							LHeap.replace q_heap loc (new_fv_list, def);
							let new_pfs : jsil_logic_assertion list = make_all_different_pure_assertion new_fv_list matched_fv_list in
							loop rest_locs (new_pfs @ pfs) (new_discharges @ discharges)
						| None -> raise (SymbExecFailure (Impossible "unify_symb_heaps: unify_symb_fv_lists returned None")))))
					| _ -> raise (SymbExecFailure (UH PatternHeapWithDefaultValue))))) in

	let remaining_locs, new_pfs, new_discharges = loop locs [] [] in

	(* DEBUG *)
	print_debug "Unify symbolic heaps: single pass : end";
	print_debug (Printf.sprintf "Pattern heap: %s \n Actual heap: %s \n Quotient heap: %s \n Remaining locations: %s \n %s"
		(Symbolic_State_Print.string_of_shallow_symb_heap pat_heap false)
		(Symbolic_State_Print.string_of_shallow_symb_heap heap false)
		(Symbolic_State_Print.string_of_shallow_symb_heap q_heap false)
		(String.concat ", " remaining_locs)
		(Symbolic_State_Print.string_of_substitution subst));
  (* DEBUG *)

	(remaining_locs, DynArray.of_list new_pfs, new_discharges)
*)


(**
 *
 * Returns a list of triples of the form (substitution, preds that haven't been unified, pat_preds that haven't been unified)
 *
 *)

 (*)
let unify_pred_arrays_single_pass (pat_preds : predicate_set) (preds : predicate_set) p_formulae pat_gamma gamma (subst : substitution) =
	print_debug "Entering unify_pred_arrays.";

	let result = (match (DynArray.length pat_preds) with
	| 0 -> [ (subst, preds, []) ]
	| _ ->
		let pat_preds = DynArray.to_list pat_preds in
		let preds = DynArray.to_list preds in
		let p_formulae = DynArray.copy p_formulae in
		let gamma = Hashtbl.copy gamma in
		let subst = Hashtbl.copy subst in

		let ps = get_unification_candidates (DynArray.of_list pat_preds) (DynArray.of_list preds) p_formulae gamma subst in

		let i = ref 0 in
		let n = Array.length ps in
		let substs = ref SSS.empty in
		let options = DynArray.create() in
		while (!i < n) do
			let (subst, unifier, unmatched_preds, unmatched_pat_preds) = Array.get ps !i in
			let result = unify_preds subst unifier p_formulae pat_gamma gamma in
			print_debug (Printf.sprintf "Candidate is %s" (Option.map_default (fun x -> "viable.") "not viable." result));
			(match result with
			| None -> ()
			| Some subst ->
				(match (SSS.mem subst !substs) with
				| true -> ()
				| false ->
						let continue = try (
							Hashtbl.iter (fun v le ->
								let (ok : bool) = gamma_subst_test v le pat_gamma gamma "unify_pred_arrays" in
								(match ok with
								| true -> ()
								| false -> raise (Failure ""))) subst;
							true
						) with | Failure _ -> false in
						(match continue with
						| false -> ()
						| true ->
								substs := SSS.add subst !substs;
								DynArray.add options (subst, unmatched_preds, unmatched_pat_preds))));
			i := !i + 1;
		done;

		let options = List.sort
			(fun (_, _, upp1) (_, _, upp2) ->
				let len1 = List.length upp1 in
				let len2 = List.length upp2 in
					compare len1 len2)
					(DynArray.to_list options) in

		print_debug_petar (Printf.sprintf "--------\nActual Outcomes: %d\n--------" (List.length options));
		List.iter (fun (subst, unmatched_preds, unmatched_pat_preds) ->
				print_debug_petar (Printf.sprintf "Substitution: %s" (Symbolic_State_Print.string_of_substitution subst));
				print_debug_petar "Unmatched predicates:";
				DynArray.iter (fun (name, params) -> print_debug_petar (Printf.sprintf "\t%s(%s)"
					name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) params)))) unmatched_preds;
				print_debug_petar "Unmatched pat predicates:";
				List.iter (fun (name, params) -> print_debug_petar (Printf.sprintf "\t%s(%s)"
					name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) params)))) unmatched_pat_preds;
			) options;
		print_debug_petar "-------------------------";
		options) in

		result

(**
		Unifying the heaps and predicates together, in iterations.
		We maintain a queue, with each element of the queue containing
		  1) a substitution
			2) the list of locations that still need to be unified; and
			3) the list of predicates that still need to be unified.
		We take a substitution out of the queue and into the solutions if all locations and all pattern predicates have been unified.
		If no changes to the substitution were made during an iteration, the substitution is not a solution.
		We stop when the queue is empty.
*)


let unify_symb_heaps_and_predicates
	(pat_heap   : symbolic_heap)      (heap : symbolic_heap)
	(pat_preds  : predicate_set)      (preds : predicate_set)
	(pat_gamma  : typing_environment) (gamma : typing_environment)
	(p_formulae : pure_formulae)
	(subst : substitution) =

	let candidates : (string list * symbolic_heap * pure_formulae * symbolic_discharge_list * predicate_set * predicate_set * substitution) Queue.t = Queue.create() in
	let solutions = ref [] in

	let locs   = heap_domain pat_heap subst in (* H  : Remaining locations *)
	let qheap  = LHeap.create 51  in           (* H  : Quotient heap       *)
	let npfs   = DynArray.create() in          (* H  : New pure formulae   *)
	let dschgs = [] in                         (* H  : Discharges          *)
	let qpreds = DynArray.copy preds in        (* P  : Quotient predicates *)
	let rpp    = DynArray.copy pat_preds in    (* P  : Remaining pat preds *)
	let subst  = Hashtbl.copy subst in         (* HP : Substitution        *)

	let starting_point = (locs, qheap, npfs, dschgs, qpreds, rpp, subst) in

	Queue.push starting_point candidates;

	while (not (Queue.is_empty candidates)) do
		print_debug "******************";
		print_debug "* NEXT ITERATION *";
		print_debug "******************\n";
		let (locs, qheap, npfs, dschrg, qpreds, rpp, subst) = Queue.pop candidates in

		(* Keep the subst *)
		let old_subst = Hashtbl.copy subst in
		(* Go for heap unification *)
		try (
			let remaining_locs, new_pfs, new_discharges = unify_symb_heaps pat_heap heap qheap pat_gamma gamma p_formulae subst locs in
			(* Go for predicate unification *)
			let potential_solutions (* (subst, qpreds, rpp) *) = unify_pred_arrays_single_pass rpp qpreds p_formulae pat_gamma gamma subst in

			(* Stabilise *)
			DynArray.append new_pfs npfs;
			let dschgs = dschgs @ new_discharges in

			let potential_solutions = List.map (fun (subst, qpreds, rpp) ->
				(remaining_locs, LHeap.copy qheap, DynArray.copy npfs, dschgs, DynArray.copy qpreds, DynArray.copy (DynArray.of_list rpp), Hashtbl.copy subst)) potential_solutions in

			List.iter (fun (remaining_locs, qheap, npfs, dschgs, qpreds, rpp, subst) ->
			(* How to detect if we've made progress? *)
			(match remaining_locs with
			| [] ->
					(* Solution *)
					solutions := (qheap, npfs, dschgs, qpreds, rpp, subst) :: !solutions;
			| _ ->
					(* Not a solution *)
					(match (subst = old_subst) with
					| true ->
							(* We were not able to go further *)
							()
					| false ->
							(* We did make a change *)
							let new_candidate = (remaining_locs, qheap, npfs, dschgs, qpreds, rpp, subst) in
							Queue.push new_candidate candidates
					))) potential_solutions;
		)
		with
		| SymbExecFailure _ -> ()
		| Failure _ -> ()
		| e -> raise e
	done;

	(* Polish the quotient heap *)
	List.iter (fun (qheap, _, _ ,_, _, _) ->
		LHeap.iter (fun loc (fv_list, def) ->
			if (not (LHeap.mem qheap loc)) then LHeap.add qheap loc (fv_list, def);
			if ((def = LUnknown) && (List.length fv_list = 0)) then LHeap.remove qheap loc)
		heap)
	!solutions;

	print_debug (Printf.sprintf "We have %d solutions after unifying heaps and predicates." (List.length !solutions));

	(match !solutions with
	| [] -> None
	| _  -> Some (List.hd !solutions))

*)


(*******************************************************************)
(*******************************************************************)
(*******************************************************************)



(*


let unify_symb_states pat_symb_state (symb_state : symbolic_state) lvars : bool * symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * typing_environment =

	print_debug (Printf.sprintf "unify_symb_states with the following specvars: %s" (String.concat ", " (SS.elements lvars)));

	let start_time = Sys.time () in try (

	let heap_0, store_0, pf_0, gamma_0, preds_0 (*, solver *) = symb_state in
	let heap_1, store_1, pf_1, gamma_1, preds_1 (*, _  *) = copy_symb_state pat_symb_state in
	let subst = init_substitution [] in
	SS.iter (fun var -> Hashtbl.replace subst var (LVar var)) lvars;

	(* Grab object locations *)
	Hashtbl.iter (fun l r ->
		let loc_l = try Simplifications.aux_find_me_Im_a_loc pf_1 gamma_1 l with _ -> None in
		(match loc_l with
		| None -> ()
		| Some loc_l ->
				Hashtbl.remove subst l;
				Hashtbl.replace subst loc_l r
		)) subst;

	print_debug (Printf.sprintf "Current substitution: %s" (Symbolic_State_Print.string_of_substitution subst));


	(* STEP 0 - Unify stores, heaps, and predicate sets                                                                                                  *)
	(* subst = empty substitution                                                                                                                        *)
	(* discharges_0 = unify_stores (store_1, store_0, subst, pi_0, gamma_0)	                                                                             *)
	(* discharges_1, heap_f, new_pfs = unify_heaps (heap_1, heap_0, subst, pi_0)                                                                         *)
	(* discharges_2, preds_f = unify_predicate_sets (preds_1, preds_0, subst, pi_0)                                                                      *)
	(* if discharges_i != None for i \in {0, 1, 2} => return Some ((disharches_0 @ discharges_1 @ discharges_2), subst, heap_f, preds_f, new_pfs)        *)
	(* if exists i \in {0, 1, 2} . discharges_i = None => return None                                                                                    *)
	(* If Step 0 returns a list of discharges and a substitution then the following implication holds:                                                   *)
	(*    pi_0 |- discharges  => store_0 =_{pi_0} subst(store_1)  /\ heap_0 =_{pi_0} subst(heap_1) + heap_f /\ preds_0 =_{pi_0} subst(preds_1) + preds_f *)

	let step_0 subst =
		let start_time = Sys.time() in
		let discharges_0 = unify_stores store_1 store_0 subst None (pfs_to_list pf_0) gamma_1 gamma_0 in
		let result = (
			print_debug_petar (Printf.sprintf "Discharges: %d\n" (List.length discharges_0));
			List.iter (fun (x, y) -> print_debug_petar (Printf.sprintf "\t%s : %s\n" (JSIL_Print.string_of_logic_expression x false) (JSIL_Print.string_of_logic_expression y false))) discharges_0;
			let keep_subst = Hashtbl.copy subst in

			let uhp = unify_symb_heaps_and_predicates heap_1 heap_0 preds_1 preds_0 gamma_1 gamma_0 pf_0 subst in
			(match uhp with
			| None -> raise (SymbExecFailure (UH GeneralHeapUnificationFailure))
			| Some (qheap, npfs, dschgs, qpreds, rpp, subst) ->
					(match (DynArray.length rpp) with
					| 0 -> ()
					| _ -> raise (SymbExecFailure (USS CannotUnifyPredicates)));
					let spec_vars_check = spec_logic_vars_discharge subst lvars pf_0 gamma_0 in
						(match spec_vars_check with
						| true -> discharges_0 @ dschgs, subst, qheap, qpreds, DynArray.to_list npfs
						| false -> raise (SymbExecFailure (USS CannotDischargeSpecVars))))) in
			let end_time = Sys.time() in
			JSIL_Syntax.update_statistics "USS: Step 0" (end_time -. start_time);
			result in

	(* STEP 1 - Pure entailment and gamma unification                                                                                                    *)
	(* existentials = vars(Sigma_pat) \ dom(subst)                                                                                                       *)
	(* subst' = subst + [ x_i \in existentials -> fresh_lvar() ]                                                                                         *)
	(* gamma_0' = gamma_0 + gamma_existentials, where gamma_existentials(x) = gamma_1(y) iff x = subst'(y)                                               *)
	(* unify_gamma(gamma_1, gamma_0', store_1, subst, existentials) = true                                                                               *)
	(* pf_0 + new_pfs |-_{gamma_0'} Exists_{existentials} subst'(pf_1) + pf_list_of_discharges(discharges)                                               *)
	let step_1 discharges subst new_pfs =

		print_debug (Printf.sprintf "Current substitution again: %s" (Symbolic_State_Print.string_of_substitution subst));

		let existentials = get_subtraction_vars (get_symb_state_vars false pat_symb_state) subst in
		let lexistentials = SS.elements existentials in
		let fresh_names_for_existentials = (List.map (fun v -> fresh_lvar ()) lexistentials) in
		let subst_existentials = init_substitution2 lexistentials (List.map (fun v -> LVar v) fresh_names_for_existentials) in
		extend_substitution subst lexistentials (List.map (fun v -> LVar v) fresh_names_for_existentials);
		let gamma_0' =
			if ((List.length lexistentials) > 0)
				then (
					let gamma_0' = copy_gamma gamma_0 in
					let gamma_1_existentials = filter_gamma_with_subst gamma_1 lexistentials subst_existentials in
					extend_gamma gamma_0' gamma_1_existentials;
					gamma_0')
				else gamma_0 in
		unify_gamma gamma_1 gamma_0' store_1 subst existentials;

		let result =
			merge_pfs pf_0 (DynArray.of_list new_pfs);

		  let pf_1_subst_list = List.map (fun a -> assertion_substitution a subst true) (pfs_to_list pf_1) in
			let pf_discharges = pf_list_of_discharges discharges subst false in
			let pfs = pf_1_subst_list @ pf_discharges in

			print_debug (Printf.sprintf "Checking if %s\n entails %s\n with existentials\n%s\nand gamma %s "
				(Symbolic_State_Print.string_of_shallow_p_formulae pf_0 false)
				(Symbolic_State_Print.string_of_shallow_p_formulae (DynArray.of_list pfs) false)
				(List.fold_left (fun ac x -> ac ^ " " ^ x) "" fresh_names_for_existentials)
				(Symbolic_State_Print.string_of_gamma gamma_0'));

			let entailment_check_ret = Pure_Entailment.check_entailment (SS.of_list fresh_names_for_existentials) (pfs_to_list pf_0) pfs gamma_0' in
			print_debug (Printf.sprintf "entailment_check: %b" entailment_check_ret);
			entailment_check_ret, pf_discharges, pf_1_subst_list, gamma_0' in
		result in

	(* Actually doing it!!! *)
	let result = (
		let discharges, subst, heap_f, preds_f, new_pfs = step_0 subst in
		let entailment_check_ret, pf_discharges, pf_1_subst_list, gamma_0' = step_1 discharges subst new_pfs in
		entailment_check_ret, heap_f, preds_f, subst, (pf_1_subst_list @ pf_discharges), gamma_0') in
	let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "unify_symb_states" (end_time -. start_time);
		result)
	with
		| e -> (match e with
			| SymbExecFailure failure ->
				let end_time = Sys.time () in
				JSIL_Syntax.update_statistics "unify_symb_states" (end_time -. start_time);
				raise e
			| _ -> raise e)

*)




let unify_symb_states pat_symb_state (symb_state : symbolic_state) lvars : bool * symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * typing_environment =

	print_debug (Printf.sprintf "unify_symb_states with the following specvars: %s" (String.concat ", " (SS.elements lvars)));

	let start_time = Sys.time () in try (

	let heap_0, store_0, pf_0, gamma_0, preds_0 (*, solver *) = symb_state in
	let heap_1, store_1, pf_1, gamma_1, preds_1 (*, _  *) = copy_symb_state pat_symb_state in
	let subst = init_substitution [] in
	SS.iter (fun var -> Hashtbl.replace subst var (LVar var)) lvars;

	print_debug (Printf.sprintf "Current substitution: %s" (Symbolic_State_Print.string_of_substitution subst));

	(* STEP 0 - Unify stores, heaps, and predicate sets                                                                                                  *)
	(* subst = empty substitution                                                                                                                        *)
	(* discharges_0 = unify_stores (store_1, store_0, subst, pi_0, gamma_0)	                                                                             *)
	(* discharges_1, heap_f, new_pfs = unify_heaps (heap_1, heap_0, subst, pi_0)                                                                         *)
	(* discharges_2, preds_f = unify_predicate_sets (preds_1, preds_0, subst, pi_0)                                                                      *)
	(* if discharges_i != None for i \in {0, 1, 2} => return Some ((disharches_0 @ discharges_1 @ discharges_2), subst, heap_f, preds_f, new_pfs)        *)
	(* if exists i \in {0, 1, 2} . discharges_i = None => return None                                                                                    *)
	(* If Step 0 returns a list of discharges and a substitution then the following implication holds:                                                   *)
	(*    pi_0 |- discharges  => store_0 =_{pi_0} subst(store_1)  /\ heap_0 =_{pi_0} subst(heap_1) + heap_f /\ preds_0 =_{pi_0} subst(preds_1) + preds_f *)

	let step_0 subst =
		let start_time = Sys.time() in
		let discharges_0 = unify_stores store_1 store_0 subst None (pfs_to_list pf_0) gamma_1 gamma_0 in
		let result = (
			print_debug_petar (Printf.sprintf "Discharges: %d\n" (List.length discharges_0));
			List.iter (fun (x, y) -> print_debug_petar (Printf.sprintf "\t%s : %s\n" (JSIL_Print.string_of_logic_expression x false) (JSIL_Print.string_of_logic_expression y false))) discharges_0;
			let keep_subst = Hashtbl.copy subst in
			(* First try to unify heaps, then predicates *)
			let ret_1, failure = try (Some (unify_symb_heaps heap_1 heap_0 pf_0 pf_1 gamma_1 gamma_0 subst), None) with | SymbExecFailure failure -> None, Some failure in
			(match ret_1 with
			| Some (heap_f, new_pfs, negative_discharges) ->
				print_debug_petar (Printf.sprintf "Heaps unified successfully. Unifying predicates.\n");
				let subst, preds_f, remaining_preds = unify_pred_arrays preds_1 preds_0 pf_0 gamma_1 gamma_0 subst in
				(match remaining_preds with
				| [] ->
					let spec_vars_check = spec_logic_vars_discharge subst lvars pf_0 gamma_0 in
					(match spec_vars_check with
					| true -> discharges_0, subst, heap_f, preds_f, new_pfs
					| false -> raise (SymbExecFailure (USS CannotDischargeSpecVars)))
				| _ -> raise (SymbExecFailure (USS CannotUnifyPredicates)))
			| None ->
					print_debug_petar (Printf.sprintf "Could not unify heaps before predicates, unifying predicates first instead.");
					let ret_2 = if (DynArray.length preds_0 > 0) then (Some (unify_pred_arrays preds_1 preds_0 pf_0 gamma_1 gamma_0 subst)) else None in
					(match ret_2 with
					| Some (subst, preds_f, []) ->
						print_debug_petar "Unified predicates successfully. Extracting additional knowledge";

						(***** EXPERIMENTAL - PUT INTO SEPARATE FUNCTION *****)

						let pat_pfs = pf_substitution pf_1 subst true in
						let _, pf_subst = Simplifications.simplify_pfs_with_subst pf_0 gamma_0 in
						(match pf_subst with
						| None -> raise (SymbExecFailure (USS ContradictionInPFS))
						| Some pf_subst ->
							(let pat_pfs = pf_substitution pat_pfs pf_subst true in
							print_debug_petar (Printf.sprintf "Original pat_pfs:\n%s" (Symbolic_State_Print.string_of_shallow_p_formulae pf_1 false));
							print_debug_petar (Printf.sprintf "Substituted pat_pfs:\n%s" (Symbolic_State_Print.string_of_shallow_p_formulae pat_pfs false));
							let new_pfs, _ = Simplifications.simplify_pfs pat_pfs gamma_0 (Some None) in
							(match (DynArray.to_list new_pfs) with
							| [ LFalse ] -> raise (SymbExecFailure (USS ContradictionInPFS))
							| _ ->
									print_debug_petar (Printf.sprintf "More pfs: %s" (Symbolic_State_Print.string_of_shallow_p_formulae new_pfs false));

									(* Now we can extract two things: more subst and more alocs *)
									let hd = SS.of_list (heap_domain heap_1 subst) in
									print_debug_petar (Printf.sprintf "Domain of the pat_heap: %s" (String.concat ", " (SS.elements hd)));
									DynArray.iter (fun pf ->
										(match pf with
										| LEq (ALoc al, LLit (Loc l))
										| LEq (LLit (Loc l), ALoc al) ->
												(match (SS.mem al hd) with
												| false -> ()
												| true -> extend_substitution subst [ al ] [ LLit (Loc l) ])

										| LEq (ALoc al1, ALoc al2) ->
											let m1 = SS.mem al1 hd in
											let m2 = SS.mem al2 hd in
											(match m1, m2 with
											| true, false -> extend_substitution subst [ al1 ] [ ALoc al2 ]
											| false, true -> extend_substitution subst [ al2 ] [ ALoc al1 ]
											| _, _ -> ()
											)

										| _ -> ()
										)
									) new_pfs;

							(***** EXPERIMENTAL - PUT INTO SEPARATE FUNCTION *****)

									print_debug_petar "Now unifying heaps again.";
									print_debug_petar (Printf.sprintf "%s" (Symbolic_State_Print.string_of_substitution subst));
									let heap_f, new_pfs, negative_discharges = unify_symb_heaps heap_1 heap_0 pf_0 pf_1 gamma_1 gamma_0 subst in
										print_debug_petar (Printf.sprintf "Heaps unified successfully.\n");
										let spec_vars_check = spec_logic_vars_discharge subst lvars pf_0 gamma_0 in
										(match spec_vars_check with
										| true -> discharges_0, subst, heap_f, preds_f, new_pfs
										| false -> raise (SymbExecFailure (USS CannotDischargeSpecVars)))
									)))
					| _ -> (match failure with | Some failure -> raise (SymbExecFailure failure))))) in
		let end_time = Sys.time() in
		JSIL_Syntax.update_statistics "USS: Step 0" (end_time -. start_time);
		result in

	(* STEP 1 - Pure entailment and gamma unification                                                                                                    *)
	(* existentials = vars(Sigma_pat) \ dom(subst)                                                                                                       *)
	(* subst' = subst + [ x_i \in existentials -> fresh_lvar() ]                                                                                         *)
	(* gamma_0' = gamma_0 + gamma_existentials, where gamma_existentials(x) = gamma_1(y) iff x = subst'(y)                                               *)
	(* unify_gamma(gamma_1, gamma_0', store_1, subst, existentials) = true                                                                               *)
	(* pf_0 + new_pfs |-_{gamma_0'} Exists_{existentials} subst'(pf_1) + pf_list_of_discharges(discharges)                                               *)
	let step_1 discharges subst new_pfs =

		print_debug (Printf.sprintf "Current substitution again: %s" (Symbolic_State_Print.string_of_substitution subst));

		let existentials = get_subtraction_vars (get_symb_state_vars false pat_symb_state) subst in
		let lexistentials = SS.elements existentials in
		let fresh_names_for_existentials = (List.map (fun v -> fresh_lvar ()) lexistentials) in
		let subst_existentials = init_substitution2 lexistentials (List.map (fun v -> LVar v) fresh_names_for_existentials) in
		extend_substitution subst lexistentials (List.map (fun v -> LVar v) fresh_names_for_existentials);
		let gamma_0' =
			if ((List.length lexistentials) > 0)
				then (
					let gamma_0' = copy_gamma gamma_0 in
					let gamma_1_existentials = filter_gamma_with_subst gamma_1 lexistentials subst_existentials in
					extend_gamma gamma_0' gamma_1_existentials;
					gamma_0')
				else gamma_0 in
		unify_gamma gamma_1 gamma_0' store_1 subst existentials;
		let result =
			merge_pfs pf_0 (DynArray.of_list new_pfs);
		  let pf_1_subst_list = List.map (fun a -> assertion_substitution a subst true) (pfs_to_list pf_1) in
			let pf_discharges = pf_list_of_discharges discharges subst false in
			let pfs = pf_1_subst_list @ pf_discharges in

			print_debug (Printf.sprintf "Checking if %s\n entails %s\n with existentials\n%s\nand gamma %s"
				(Symbolic_State_Print.string_of_shallow_p_formulae pf_0 false)
				(Symbolic_State_Print.string_of_shallow_p_formulae (DynArray.of_list pfs) false)
				(List.fold_left (fun ac x -> ac ^ " " ^ x) "" fresh_names_for_existentials)
				(Symbolic_State_Print.string_of_gamma gamma_0'));

			let entailment_check_ret = Pure_Entailment.check_entailment (SS.of_list fresh_names_for_existentials) (pfs_to_list pf_0) pfs gamma_0' in
			print_debug (Printf.sprintf "entailment_check: %b" entailment_check_ret);
			entailment_check_ret, pf_discharges, pf_1_subst_list, gamma_0' in
		result in

	(* Actually doing it!!! *)
	let result = (
		let discharges, subst, heap_f, preds_f, new_pfs = step_0 subst in
		let entailment_check_ret, pf_discharges, pf_1_subst_list, gamma_0' = step_1 discharges subst new_pfs in
		entailment_check_ret, heap_f, preds_f, subst, (pf_1_subst_list @ pf_discharges), gamma_0') in
	let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "unify_symb_states" (end_time -. start_time);
		result)
	with
		| e -> (match e with
			| SymbExecFailure failure ->
				let end_time = Sys.time () in
				JSIL_Syntax.update_statistics "unify_symb_states" (end_time -. start_time);
				raise e
			| _ -> raise e)



let unify_symb_states_fold (pred_name : string) (existentials : SS.t) (pat_symb_state : symbolic_state) (symb_state : symbolic_state) : bool * symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * typing_environment * SS.t * ((string * (jsil_logic_expr list)) list)  =
	let heap_0, store_0, pf_0, gamma_0, preds_0 (*, solver_0 *) = symb_state in
	let heap_1, store_1, pf_1, gamma_1, preds_1 (*, _ *) = pat_symb_state in
	(** Auxiliary Functions **)

 	print_debug (Printf.sprintf "store_0: %s.\nstore_1: %s"
		(Symbolic_State_Print.string_of_shallow_symb_store store_0 false)
		(Symbolic_State_Print.string_of_shallow_symb_store store_1 false));

	try (

	(* existentials -> new variables introduced by the fold                                      *)
	(* store_vars -> vars in the store which are mapped to logical expressions with existentials *)
	let find_existentials_types (existentials : SS.t) store_vars (store : symbolic_store) gamma pat_gamma =
		let gamma_existentials = gamma_init () in
		List.iter
			(fun x ->
				let le_x : jsil_logic_expr option = store_get_safe store x in
				let x_type = gamma_get_type pat_gamma x in
				match le_x, x_type with
				| Some le_x, Some x_type -> let _ = JSIL_Logic_Utils.reverse_type_lexpr_aux gamma gamma_existentials le_x x_type in ()
				|	_, _ -> ())
			store_vars;
		let gamma_existentials = filter_gamma gamma_existentials existentials in
		gamma_existentials in

	(* STEP 0 -                                                                                                              *)
	(*  1 - find the store variables that are mapped to expressions with new logical variables                               *)
	(*  2 - find the types of the new logical variables introduced in the fold                                               *)
	(*  3 - unify the stores except for the variables that are mapped to expressions that contain new logical variables      *)
	(*  let filtered_vars = { x : x \in dom(store_0) /\ ((lvars (store_0(x)) \cap existentials) \neq \emptyset }             *)
	(*  let unfiltered_vars = \dom(store_0) \ filtered_vars                                                                  *)
	(*  let new_store_0 = store_0|_{unfiltered_vars}                                                                         *)
	(*  let new_store_1 = store_1|_{unfiltered_vars}                                                                         *)
	(*  let discharges_0 = { (le_0, le_1) | x \in filtered_vars /\ le_0 = store_0(x) /\ le_1 = store_1(x)                    *)
	(*  let subst = new_subst ()                                                                                             *)
	(*  let discharges_1 = unify_stores (new_store_0, new_store_1, subst, pi_0, gamma_0)	                                 *)
	(*  Find gamma_existentials st                                                                                           *)
	(*   dom(gamma_existentials) \subseteq existentials                                                                      *)
	(*    forall x \in filtered_vars :                                                                                       *)
	(* 	     (gamma_1 |- store_1(x) : tau) => (gamma_0 + gamma_existentials |- store_0(x) : tau                              *)
	(*  filtered_vars, unfiltered_vars, gamma_existentials, discharges_0 @ discharges_1            *)
	let step_0 () =
		print_debug "\tEntering step 0.";
		let subst = init_substitution [] in
		let filtered_vars, unfiltered_vars =
			store_filter
				store_0
				(fun (le : jsil_logic_expr) ->
					let le_vars : SS.t = get_expr_vars false le in
					let existentials_in_le = SS.filter (fun var -> SS.mem var le_vars) existentials in
					(SS.cardinal existentials_in_le > 0)) in
		let gamma_existentials = find_existentials_types existentials filtered_vars store_0 gamma_0 gamma_1 in
	 	let discharges_0 =
			(List.fold_left
				(fun ac x ->
					let le_0 = store_get_safe store_0 x in
					let le_1 = store_get_safe store_1 x in
					match le_0, le_1 with
					| Some le_0, Some le_1 -> (le_1, le_0) :: ac
					| _, None -> ac
					| _ -> raise (SymbExecFailure (Impossible "unify_symb_states_fold, step 0: variable not found in store")))
				[]
				filtered_vars) in
		print_debug_petar (Printf.sprintf "\t\tGot the discharges of length: %d" (List.length discharges_0));
		let store_0' = store_projection store_0 unfiltered_vars in
		let store_1' = store_projection store_1 unfiltered_vars in

		print_debug_petar (Printf.sprintf "store_0: %s.\nstore_1: %s"
			(Symbolic_State_Print.string_of_shallow_symb_store store_0 false)
			(Symbolic_State_Print.string_of_shallow_symb_store store_1 false));

		print_debug_petar (Printf.sprintf "store_0': %s.\nstore_1': %s"
			(Symbolic_State_Print.string_of_shallow_symb_store store_0' false)
			(Symbolic_State_Print.string_of_shallow_symb_store store_1' false));

		let discharges_1 = unify_stores store_1' store_0' subst None (pfs_to_list pf_0) gamma_1 gamma_0 in
		subst, filtered_vars, unfiltered_vars, gamma_existentials, (discharges_0 @ discharges_1) in

	(* STEP 1 *)
	let step_1 subst =
		print_debug "\tEntering step 1.";
		let heap_f, new_pfs, negative_discharges = unify_symb_heaps heap_1 heap_0 pf_0 pf_1 gamma_1 gamma_0 subst in
		let new_subst, preds_f, unmatched_pat_preds = unify_pred_arrays preds_1 preds_0 pf_0 gamma_1 gamma_0 subst in
			print_debug (Printf.sprintf "subst after unify_heaps: %s" (Symbolic_State_Print.string_of_substitution subst));
			print_debug (Printf.sprintf "subst after unify_preds: %s" (Symbolic_State_Print.string_of_substitution new_subst));
			heap_f, preds_f, subst, new_subst, new_pfs, unmatched_pat_preds in


	(* STEP 2 *)
	let step_2 subst filtered_vars gamma_existentials new_pfs discharges =
		let pat_existentials = get_subtraction_vars (get_symb_state_vars false pat_symb_state) subst in
		let lpat_existentials = SS.elements pat_existentials in
		let new_pat_existentials = (List.map (fun v -> fresh_lvar ()) lpat_existentials) in
		let existential_substitution = init_substitution2 lpat_existentials (List.map (fun v -> LVar v) new_pat_existentials) in
		extend_substitution subst lpat_existentials (List.map (fun v -> LVar v) new_pat_existentials);
		let gamma_0' =
			if (((List.length filtered_vars) > 0) || ((List.length lpat_existentials) > 0))
				then (
					let gamma_0' = copy_gamma gamma_0 in
					let gamma_1' = filter_gamma_with_subst gamma_1 lpat_existentials existential_substitution in
					extend_gamma gamma_0' gamma_1';
					extend_gamma gamma_0' gamma_existentials;
					gamma_0')
				else gamma_0 in
		let new_existentials = SS.union existentials (SS.of_list new_pat_existentials) in
		merge_pfs pf_0 (DynArray.of_list new_pfs);
		let unify_gamma_check =
			try (unify_gamma gamma_1 gamma_0' store_0 subst pat_existentials; true) with | SymbExecFailure _ -> false in
		if (unify_gamma_check) then
		begin
			let pf_discharges = pf_list_of_discharges discharges subst false in
			let pf_discharges_str = String.concat ", "
				(List.map (fun a -> JSIL_Print.string_of_logic_assertion a false) pf_discharges) in

			print_debug (Printf.sprintf "Ooga booga Original pfs %s\nand subs %s\ndischarges: %s.\npf_discharges: %s\n"
				(Symbolic_State_Print.string_of_shallow_p_formulae pf_1 false)
				(Symbolic_State_Print.string_of_substitution subst)
				(Symbolic_State_Print.print_string_of_discharge discharges)
				pf_discharges_str);


			let pf_1_subst_list = List.map (fun a -> assertion_substitution a subst true) (pfs_to_list pf_1) in


			let pfs = DynArray.of_list (pf_1_subst_list @ pf_discharges) in
			let pf0 = DynArray.copy pf_0 in


			Simplifications.sanitise_pfs_no_store gamma_0' pfs;
			(* Moving formulae on the left which contain existentials to the right *)


			let to_delete = SI.empty in
			let i = ref 0 in
			while (!i < DynArray.length pf0) do
				let pf = DynArray.get pf0 !i in
				let vpf = get_assertion_vars false pf in
				let ixt = SS.inter existentials vpf in
				if (not (ixt = SS.empty)) then
				begin
					DynArray.delete pf0 !i;
					DynArray.add pfs pf
				end
				else i := !i + 1
			done;


			print_debug_petar (Printf.sprintf "Checking if %s\n entails %s\n with existentials\n%s\nand gamma %s"
				(Symbolic_State_Print.string_of_shallow_p_formulae pf0 false)
				(Symbolic_State_Print.string_of_shallow_p_formulae pfs false)
				(List.fold_left (fun ac x -> ac ^ " " ^ x) "" (SS.elements new_existentials))
				(Symbolic_State_Print.string_of_gamma gamma_0'));

			let entailment_check = Pure_Entailment.check_entailment new_existentials (pfs_to_list pf0) (pfs_to_list pfs) gamma_0' in
			(* (if (not entailment_check) then Pure_Entailment.understand_error new_existentials (pfs_to_list pf0) (pfs_to_list pfs) gamma_0'); *)
			(entailment_check, pf_discharges, pf_1_subst_list, gamma_0', new_existentials)
		end
		else
		 	(false, [], [], gamma_0', new_existentials) in

	let recovery_step heap_f subst filtered_vars gamma_existentials new_pfs discharges =
		(* take the predicate out of the pat_preds *)
		(* unify the preds *)
		(* call step 2 *)

		print_debug (Printf.sprintf "subst in recovery before re-unification of preds: %s" (Symbolic_State_Print.string_of_substitution subst));

		let copied_preds_1 = copy_pred_set preds_1 in
		let subtracted_pred_ass = simple_subtract_pred copied_preds_1 pred_name in
		match subtracted_pred_ass with
		| None -> raise (SymbExecFailure (USF (CannotSubtractPredicate pred_name)))
		| Some subtracted_pred_ass ->
			print_debug
				(Printf.sprintf "In the middle of the recovery!!! the pat_preds as they are now:\n%s\n"
					(Symbolic_State_Print.string_of_preds copied_preds_1 false));
			let subst, preds_f, remaining_preds = unify_pred_arrays copied_preds_1 preds_0 pf_0 gamma_1 gamma_0 subst in
			(match remaining_preds with
			| [] ->
				print_debug (Printf.sprintf "subst in recovery after re-unify_preds: %s" (Symbolic_State_Print.string_of_substitution subst));
				let entailment_check_ret, pf_discharges, pf_1_subst_list, gamma_0', new_existentials = step_2 subst filtered_vars gamma_existentials new_pfs discharges in
				entailment_check_ret, heap_f, preds_f, subst, (pf_1_subst_list @ pf_discharges), gamma_0', new_existentials, [ subtracted_pred_ass ]
			| _ -> raise (SymbExecFailure (USF CannotUnifyPredicates)) ) in

	(* Actually doing it!!! *)
	let subst, filtered_vars, _, gamma_existentials, discharges = step_0 () in
		print_debug "Passed step 0.";
		let heap_f, preds_f, old_subst, subst, new_pfs, unmatched_pat_preds = step_1 subst in
		  print_debug "Passed step 1.";
		  let entailment_check_ret, pf_discharges, pf_1_subst_list, gamma_0', new_existentials = step_2 subst filtered_vars gamma_existentials new_pfs discharges in
			(match entailment_check_ret with
			| true  -> entailment_check_ret, heap_f, preds_f, subst, (pf_1_subst_list @ pf_discharges), gamma_0', new_existentials, unmatched_pat_preds
			| false -> (match pred_name with
				| "AVL" -> raise (SymbExecFailure (USF CannotUnifyPredicates))
				| _ -> recovery_step heap_f old_subst filtered_vars gamma_existentials new_pfs discharges))
	)
	with
		| e -> (match e with
			| SymbExecFailure failure -> raise e
			| _ -> raise e)




(* get rid of the js flag here ASAP *)
let fully_unify_symb_state pat_symb_state symb_state lvars (js : bool) =
	print_debug (Printf.sprintf "Fully_unify_symb_state.\nSymb_state:\n%s.\nPAT symb_state:\n%s"
		(Symbolic_State_Print.string_of_shallow_symb_state symb_state)
		(Symbolic_State_Print.string_of_shallow_symb_state pat_symb_state));

	try (
		let outcome, quotient_heap, quotient_preds, subst, pf_discharges, _ = unify_symb_states pat_symb_state symb_state lvars in
		(match outcome with
		| true ->
			let emp_heap = (is_heap_empty quotient_heap js) in
			let emp_preds = (is_preds_empty quotient_preds) in
			if (emp_heap && emp_preds) then
				subst
			else
				let _ = if (emp_heap) then begin print_debug "Quotient heap empty.\n" end
						else begin print_debug (Printf.sprintf "Quotient heap left: \n%s\n" (Symbolic_State_Print.string_of_shallow_symb_heap quotient_heap false)) end in
				let _ = if (emp_preds) then begin print_debug "Quotient predicates empty.\n" end
						else begin print_debug (Printf.sprintf "Quotient predicates left: \n%s\n" (Symbolic_State_Print.string_of_preds quotient_preds false))  end in
				raise (SymbExecFailure (FSS ResourcesRemain))
		| false -> raise (SymbExecFailure (FSS CannotUnifySymbStates))))
	with
		| e -> (match e with
			| SymbExecFailure failure ->
				raise e)

(* RECOVERY (TODO - MOVE FROM HERE) *)

let get_index x lst =
	let rec get_index_rec x lst c = match lst with
    | [] -> raise (Failure "Not Found")
    | hd :: tl -> if (hd = x) then c else get_index_rec x tl (c+1) in
	get_index_rec x lst 0

let understand_single_recovery s_prog symb_state recovery_option : recovery =
	let heap, store, pfs, gamma, preds = symb_state in
	try (
		(match recovery_option with

		(* Untyped variable that needs to be typed *)
		| UG (NoTypeForVariable var) ->
			let var = (match (real_is_pvar_name var) with
			| true -> let var = store_get_safe store var in
				(match var with
				| None -> raise (Failure "")
				| Some var ->
					(match var with
					| LVar var -> var
					| _ -> raise (Failure "")))
			| false -> var) in
			print_debug_petar (Printf.sprintf "Understood that target var is: %s" var);
			let preds = DynArray.to_list preds in
			let preds = List.filter (fun (_, params) -> List.mem (LVar var) params) preds in
			print_debug_petar (Printf.sprintf "Candidate predicates:\n\t%s"
				(String.concat "\n\t"
					(List.map (fun (pn, pp) -> Printf.sprintf "%s(%s)" pn (String.concat ", " (List.map (fun x -> print_lexpr x) pp))) preds)));
			let idxs = List.map (fun (_, params) -> get_index (LVar var) params) preds in
			let ovars = List.map2
				(fun (pn, _) idx ->
					let pred = get_pred s_prog.pred_defs pn in
					let params = pred.n_pred_params in
					List.nth params idx) preds idxs in
			print_debug_petar (Printf.sprintf "Original variables:\n\t%s" (String.concat "\n\t" ovars));
			let do_we_have_types = List.map2
				(fun (pn, _) ovar ->
					let pred = get_pred s_prog.pred_defs pn in
					let defs = pred.n_pred_definitions in
					List.fold_left (fun ac (_, ss) -> let gamma = get_gamma ss in (Hashtbl.mem gamma ovar) && ac) true defs
				) preds ovars in
			print_debug_petar (Printf.sprintf "Are they typed?\n\t%s" (String.concat "\n\t" (List.map (fun x -> Printf.sprintf "%b" x) do_we_have_types)));
			let flash_candidates = List.combine preds do_we_have_types in
			let flash_candidates = List.filter (fun (_, x) -> x) flash_candidates in
			let flash_candidates, _ = List.split flash_candidates in
			(match flash_candidates with
			| [] -> NoRecovery
			| (pn, pp) :: _ -> GR (Flash (pn, pp)))

		| _ -> NoRecovery)
	) with Failure _ -> NoRecovery


let understand_recovery s_prog symb_state recovery_options : recovery list =
	print_debug_petar "Attempting to recover.";
	let result = List.map (fun x -> understand_single_recovery s_prog symb_state x) recovery_options in
	let result = List.filter (fun x -> x <> NoRecovery) result in
	print_debug_petar "----------------------";
	result


(* This is one place to try and do recovery *)
let unify_symb_state_against_post s_prog proc_name spec symb_state flag symb_exe_info js =

	let print_error_to_console msg =
		(if (msg = "")
			then Printf.printf "Failed to verify a spec of proc %s\n" proc_name
			else Printf.printf "Failed to verify a spec of proc %s -- %s\n" proc_name msg);
		let final_symb_state_str = Symbolic_State_Print.string_of_shallow_symb_state symb_state in
		let post_symb_state_str = Symbolic_State_Print.string_of_symb_state_list spec.n_post in
		Printf.printf "Final symbolic state: %s\n" final_symb_state_str;
		Printf.printf "Post condition: %s\n" post_symb_state_str in

	let rec loop posts i recovery_options : unit =
		(match posts with
		| [] ->
				print_debug "----------------------";
				let can_we_recover : recovery list = understand_recovery s_prog symb_state recovery_options in
				(match can_we_recover with
				| [] -> print_error_to_console "Non_unifiable symbolic states"; raise (Failure "Post condition is not unifiable")
				| rop :: _ ->
					(match rop with
					| GR (Flash (pred_name, pred_params)) ->
						print_debug_petar (Printf.sprintf "I can try to flash the predicate %s(%s)" pred_name (String.concat ", " (List.map (fun x -> print_lexpr x) pred_params)));
						print_debug "----------------------";
						raise ( SymbExecRecovery rop))
				)
		| post :: rest_posts ->
			let unification_function p ss lv = (match js with
				| true ->  let (success, _, _, _, _, _) = unify_symb_states p ss lv in success
				| false -> let _ = fully_unify_symb_state p ss lv false in true) in
				try (
				let is_unifiable = unification_function post symb_state spec.n_lvars in
					(match is_unifiable with
					| true ->
							activate_post_in_post_pruning_info symb_exe_info proc_name i;
							print_normal (Printf.sprintf "Verified one spec of proc %s" proc_name)
					| false -> loop rest_posts (i + 1) recovery_options)) with
				| SymbExecFailure failure ->
						print_debug "Failure in unify_symb_state_against_post";
						print_debug (Symbolic_State_Print.print_failure failure);
						loop rest_posts (i + 1) (recovery_options @ [ failure ])) in
			loop spec.n_post 0 []


let safe_merge_symb_states (symb_state_l : symbolic_state) (symb_state_r : symbolic_state) (subst : substitution) : symbolic_state option =

	try (
		let pf_r_existentials = get_subtraction_vars (get_symb_state_vars false symb_state_r) subst in
		unify_gamma (get_gamma symb_state_r) (get_gamma symb_state_l) (get_store symb_state_r) subst pf_r_existentials;

		let symb_state_r = symb_state_substitution symb_state_r subst false in
		let heap_l, store_l, pf_l, gamma_l, preds_l (*, solver_l *) = symb_state_l in
		let heap_r, store_r, pf_r, gamma_r, preds_r (*, _ *) = symb_state_r in
		merge_pfs pf_l pf_r;
		merge_gammas gamma_l gamma_r;

		let satisfiability_check = Pure_Entailment.check_satisfiability (pfs_to_list pf_l) gamma_l in

		if (satisfiability_check)
			then (
				Symbolic_State_Utils.merge_heaps heap_l heap_r pf_l gamma_l;
				DynArray.append preds_r preds_l;
				Some (heap_l, store_l, pf_l, gamma_l, preds_l))
			else None)
	with
		| e -> (match e with
			| SymbExecFailure failure ->
				print_debug (Symbolic_State_Print.print_failure failure);
				None)


(**
  symb_state        - the current symbolic state minus the predicate that is to be unfolded
	pat_symb_state    - the symbolic state corresponding to the definition of the predicate that we are trying to unfold
	calling_store     - a mapping from the parameters of the predicate to the arguments given in the unfolding
	subst_unfold_args - substitution that matches the arguments of the unfold logical command with the arguments of
	                    the predicate as it appears in the current symbolic state
	existentials      - new variables introduced in the unfold
	spec_vars         - logical variables that appear in the precondition
	pat_subst         - pat_subst given by the unfolding info
*)
let unfold_predicate_definition symb_state pat_symb_state calling_store subst_unfold_args spec_vars pat_subst =

	(* PREAMBLE                                                                                                            *)
	let gamma_old = get_gamma symb_state in
	let symb_state = copy_symb_state symb_state in
	let store_0 = calling_store in
	let store_1 = get_store pat_symb_state in
	let gamma_0 = get_gamma symb_state in
	let gamma_1 = get_gamma pat_symb_state in
	let store_vars = store_domain store_0 in

	let find_store_var_type store gamma x =
		(match gamma_get_type gamma x with 
		| Some t_x -> Some t_x 
		| None     -> 
			let le_x = store_get_safe store x in
			(match le_x with
			| Some le_x ->
				let x_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le_x in
				x_type
			| None -> None)) in

	print_debug "Unfold predicate definition.";
	print_debug (Printf.sprintf "Store_0:\n%s.\n Store_1:\n%s."
		(Symbolic_State_Print.string_of_shallow_symb_store store_0 false)
		(Symbolic_State_Print.string_of_shallow_symb_store store_1 false));

	try (

	(* STEP 1 - Unify(store_0, store_1, pi_0) = subst, pat_subst, discharges                                               *)
	(* subst (store_0) =_{pi_0} pat_subst (store_1) provided that the discharges hold                                      *)
	(* we start by unifying the stores - this unification will produce two substituions: pat_subst and subst               *)
	(* pat_subst is to applied in the pat_symb_state and subst is to be applied in the symb_state                          *)
	(* The store unification also generates a list of discharges - discharges - which need to hold for the stores to match *)
	let step_1 () =
		let pat_subst =
			match pat_subst with
			| None -> init_substitution []
			| Some pat_subst -> pat_subst in
		let subst = init_substitution [] in
		let discharges = unify_stores store_1 store_0 pat_subst (Some subst) (pfs_to_list (get_pf symb_state)) gamma_1 gamma_0 in
		print_debug(Printf.sprintf "substitutions after store unification.\nSubst:\n%s\nPat_Subst:\n%s\n. Discharges:\n%s\n"
			(Symbolic_State_Print.string_of_substitution subst)
			(Symbolic_State_Print.string_of_substitution pat_subst)
			(Symbolic_State_Print.print_string_of_discharge discharges));
		(* Printf.printf "GAMMA_OLD - STEP 1:\n%s\n" (Symbolic_State_Print.string_of_gamma gamma_old); *)
		discharges, subst, pat_subst in


	(* STEP 2 - the store must agree on the types                                                                          *)
	(* forall x \in domain(store_0) = domain(store_1) :                                                                    *)
	(*   ((Gamma_1(x) = tau_1) \/ (Gamma_1 |- store_1(x) : tau_1))  /\ (Gamma_0 |- store_0(x) : tau_0) => tau_1 = tau_0    *)
	let step_2 () =
		let store_0_var_types = List.map (fun x -> find_store_var_type store_0 gamma_0 x) store_vars in
		let store_1_var_types = List.map (fun x -> find_store_var_type store_1 gamma_1 x) store_vars in
		print_debug (Printf.sprintf "Step 2:\n%s\n%s"
			(List.fold_left2 (fun ac y x -> ac ^ (Printf.sprintf "%s: %s\n" y (match x with | None -> "None" | Some t -> (JSIL_Print.string_of_type t)))) "" store_vars store_0_var_types)
			(List.fold_left2 (fun ac y x -> ac ^ (Printf.sprintf "%s: %s\n" y (match x with | None -> "None" | Some t -> (JSIL_Print.string_of_type t)))) "" store_vars store_1_var_types));
		let stores_are_type_compatible =
			List.fold_left2
				(fun ac t1 t2 ->
					if (not ac) then false else
					match t1, t2 with
					| Some t1, Some t2 -> t1 = t2
					| _, _ -> true) true store_0_var_types store_1_var_types in
		(* Printf.printf "GAMMA_OLD - STEP 2:\n%s\n" (Symbolic_State_Print.string_of_gamma gamma_old);	*)
		store_0_var_types, store_1_var_types, stores_are_type_compatible in


	(* STEP 3 - the substitutions need to make sense wrt the gammas                                                        *)
	(* forall x \in subst : subst(x) = le /\ Gamma_0(x) = tau =>  \Gamma_1 |- le : tau                                     *)
	(* forall x \in pat_subst : pat_subst (x) = le /\ Gamma_1(x) = tau => \Gamma_0 |- le : tau                             *)
	let step_3 subst pat_subst =
		let subst_is_sensible = is_sensible_subst subst gamma_0 gamma_1 in
		let pat_subst_is_sensible = is_sensible_subst pat_subst gamma_1 gamma_0 in
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
		let gamma_0' = gamma_init () in
		List.iter
			(fun x ->
				let le_x = store_get_safe store_0 x in
				let x_type = find_store_var_type store_1 gamma_1 x in
				match le_x, x_type with
				| Some le_x, Some x_type -> 
					print_debug (Printf.sprintf "Completing the gamma: %s %s\n" 
						(JSIL_Print.string_of_logic_expression le_x false)
						(JSIL_Print.string_of_type x_type)); 
					let _ = JSIL_Logic_Utils.reverse_type_lexpr_aux gamma_0 gamma_0' le_x x_type in ()
				|	_, _ -> ())
				untyped_store_0_vars;
		print_debug (Printf.sprintf "GAMMA_OLD - STEP 4:\n%s\n" (Symbolic_State_Print.string_of_gamma gamma_old));
		print_debug (Printf.sprintf "Inferred typing information given the unfolding:\n%s\n" (Symbolic_State_Print.string_of_gamma gamma_0')); 
		gamma_0' in


	(* STEP 5 - check whether the pure formulae make sense together - new_pat_subst = subst (pat_subst (.))                 *)
	(* pi_0' = subst(pi_0),  pi_1' = new_pat_subst (pi_1)                                                                   *)
	(* pi_discharges = new_pat_subst ( discharges ); pi_unfold_args = pf_of_subst ( subst_unfold_args )                     *)
	(* pi_subst = pf_of_subst ( subst )                                                                                     *)
	(* pi = pi_0' + pi_1' + pi_discharges + pi_spec_vars + pi_unfold_args                                                   *)
	(* gamma_0'' = subst (gamma_0 (.)) + subst( gamma_0' (.))   gamma_1'' = new_pat_subst (gamma_1 (.))                     *)
	(* gamma = gamma_0'' + gamma_1''                                                                                        *)
	(* |-_{gamma} pi                                                                                                        *)
	let step_5 subst pat_subst discharges gamma_0' =
		let pi_0 = get_pf symb_state in
		let pi_1 = get_pf pat_symb_state in
		let new_pat_subst = compose_partial_substitutions subst pat_subst in
		let spec_vars_subst = filter_substitution subst spec_vars in
		let pi_0' = pfs_to_list (pf_substitution pi_0 subst true) in
		let pi_1' = pfs_to_list (pf_substitution pi_1 new_pat_subst false) in
		let pi_discharges = pf_list_of_discharges discharges new_pat_subst false in
		let pi_spec_vars = pf_of_substitution spec_vars_subst in
		let pi_unfold_args = pf_of_substitution subst_unfold_args in
		let pi_subst = pf_of_substitution subst in
		let pi' = pi_discharges @ pi_spec_vars @ pi_unfold_args @ pi_subst in
		let pi = pi' @ pi_1' @ pi_0' in
		let gamma_0 = gamma_substitution gamma_0 subst true in
		let gamma_0' = gamma_substitution gamma_0' subst true in
		extend_gamma gamma_0 gamma_0';
		let gamma_1'' = gamma_substitution gamma_1 new_pat_subst false in
		(* Printf.printf "gamma_1'' is:\n%s\n" (Symbolic_State_Print.string_of_gamma gamma_1''); *)
		extend_gamma gamma_0 gamma_1'';
		let gamma = gamma_0 in
		Normaliser.extend_typing_env_using_assertion_info gamma pi;
		print_debug (Printf.sprintf "substitutions immediately before sat check.\nSubst:\n%s\nPat_Subst:\n%s"
			(Symbolic_State_Print.string_of_substitution subst)
			(Symbolic_State_Print.string_of_substitution new_pat_subst));
		print_debug (Printf.sprintf "About to check if the following is SATISFIABLE:\n%s\nGiven the GAMMA:\n%s"
			(JSIL_Print.str_of_assertion_list pi)
			(	Symbolic_State_Print.string_of_gamma gamma));
		let sat_check = Pure_Entailment.check_satisfiability pi gamma in
		(* Printf.printf "GAMMA_OLD - STEP 5:\n%s\n" (Symbolic_State_Print.string_of_gamma gamma_old); *)
	    sat_check, pi', gamma_0', new_pat_subst in


	(* STEP 6 - Finally unfold: Sigma_0, Sigma_1, subst, pat_subst, pi, gamma                              *)
	(* subst(Sigma_0) + pat_subst(Sigma_1) + (_, _, pi, gamma, _)                                          *)
	let step_6 subst pat_subst new_pfs new_gamma =
		print_debug ("Entering step 6 of safe_merge_symb_states");
		let symb_state = symb_state_substitution symb_state subst true in
		let unfolded_symb_state = Symbolic_State_Utils.merge_symb_states symb_state pat_symb_state pat_subst in
		merge_pfs (get_pf unfolded_symb_state) (DynArray.of_list new_pfs);
		extend_gamma (get_gamma unfolded_symb_state) new_gamma;
		Normaliser.extend_typing_env_using_assertion_info (get_gamma unfolded_symb_state) new_pfs;
		print_debug ("Finished step 6 of safe_merge_symb_states");
		unfolded_symb_state in

	(** Now DOING IT **)
	let discharges, subst, pat_subst = step_1 () in
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
							) else  ( print_debug (Printf.sprintf "Failed unfolding in step 5") ; None)
					) else  ( print_debug (Printf.sprintf "Failed unfolding in step 3");    None)
			) else ( print_debug (Printf.sprintf "Failed unfolding in step 2");  None))
	with
		| e -> (match e with
			| SymbExecFailure failure ->
				print_debug (Symbolic_State_Print.print_failure failure);
				None
			| _ -> raise e)


let grab_resources symb_state pat_symb_state lvars existentials =
	print_debug (Printf.sprintf "grab_resources.\nSymb_state:\n%s.\nAssert symb_state:\n%s"
		(Symbolic_State_Print.string_of_shallow_symb_state symb_state)
		(Symbolic_State_Print.string_of_shallow_symb_state pat_symb_state));
	try (
		let outcome, quotient_heap, quotient_preds, subst, pf_discharges, _ = unify_symb_states pat_symb_state symb_state lvars in
		match outcome with
		| true ->
				extend_symb_state_with_pfs symb_state (DynArray.of_list pf_discharges);
				let symb_state = symb_state_replace_heap symb_state quotient_heap in
				let symb_state = symb_state_replace_preds symb_state quotient_preds in
				let new_symb_state = Symbolic_State_Utils.merge_symb_states symb_state pat_symb_state subst in
				let subst_pfs = assertions_of_substitution subst in
				extend_symb_state_with_pfs symb_state (DynArray.of_list subst_pfs);
				let start_time = Sys.time() in
				let symb_state = Simplifications.simplify_ss symb_state (Some (Some (SS.union lvars existentials))) in
				let end_time = Sys.time() in
				JSIL_Syntax.update_statistics "simplify_ss: grab_resources" (end_time -. start_time);
				Some symb_state
		| false -> None)
	with
		| e -> (match e with
			| SymbExecFailure failure ->
				print_debug (Symbolic_State_Print.print_failure failure);
				None)
