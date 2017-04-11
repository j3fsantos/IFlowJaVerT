open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils
open Symbolic_State_Basics

(***************************)
(** Unification Algorithm **)
(***************************)

(*
	| LLit				of jsil_lit
	| LNone
	| LVar				of jsil_logic_var
	| ALoc				of string
	| PVar				of jsil_var
	| LBinOp			of jsil_logic_expr * bin_op * jsil_logic_expr
	| LUnOp				of unary_op * jsil_logic_expr
	| LTypeOf			of jsil_logic_expr
	| LEList      of jsil_logic_expr list
	| LLstNth     of jsil_logic_expr * jsil_logic_expr
	| LStrNth     of jsil_logic_expr * jsil_logic_expr
	| LUnknown
*)

let must_be_equal le_pat le pi gamma subst =
	let le_pat = lexpr_substitution le_pat subst true in
	print_debug (Printf.sprintf "Must be equal: %s = %s" (JSIL_Print.string_of_logic_expression le_pat false) (JSIL_Print.string_of_logic_expression le false));
	let result = 
	(match le_pat = le with
	| true -> true
	| false -> 
		(match le_pat, le with
		| LLit pat_lit, LLit lit -> pat_lit = lit
		| LLit pat_lit, _ ->
			Pure_Entailment.is_equal le_pat le pi (* solver *) gamma
		| LNone, LEList _
		| LEList _, LNone -> false
		| _, _ -> false)) in
	result


let must_be_different le_pat le pi gamma subst =
	let le_pat = lexpr_substitution le_pat subst true in
	let result = 
	(match le_pat = le with
	| true -> true
	| false -> 
		(match le_pat, le with
		| LLit pat_lit, LLit lit -> not (pat_lit = lit)
		| LLit pat_lit, _ ->
			Pure_Entailment.is_different le_pat le pi (* solver *) gamma
		| LNone, LEList _
		| LEList _, LNone -> false
		| _, _ -> false)) in
	result




let unify_stores (pat_store : symbolic_store) (store : symbolic_store) (pat_subst : substitution) (subst: substitution option) (pfs : jsil_logic_assertion list) (* solver *) (gamma : typing_environment) : ((jsil_logic_expr * jsil_logic_expr) list) option  =
	let start_time = Sys.time () in
	try
	print_debug (Printf.sprintf "Unifying stores:\nStore: %s\nPat_store: %s" 
		(JSIL_Memory_Print.string_of_shallow_symb_store store false) 
		(JSIL_Memory_Print.string_of_shallow_symb_store pat_store false)); 
	let discharges =
		Hashtbl.fold
			(fun var pat_lexpr discharges ->
				let lexpr = try Hashtbl.find store var with _ -> raise (Failure "The stores are not unifiable") in
				let rec spin_me_round pat_lexpr lexpr discharges =
				(*Printf.printf "(%s, %s)\n" (JSIL_Print.string_of_logic_expression pat_lexpr false) (JSIL_Print.string_of_logic_expression lexpr false);*)
				(match pat_lexpr, lexpr with

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
					if (Hashtbl.mem pat_subst lvar)
						then (let current = Hashtbl.find pat_subst lvar in
							if Pure_Entailment.is_equal current lexpr (DynArray.of_list pfs) (* solver *) gamma
								then discharges
								else raise (Failure "No no no no NO."))
						else (extend_subst pat_subst lvar lexpr;
								discharges)

				| ALoc pat_aloc, LVar lvar ->
					print_debug (Printf.sprintf "So, in unify_stores: Aloc %s, Lvar %s\n" pat_aloc lvar); 
					let loc = resolve_location lvar pfs in
					(match loc with
					| Some loc ->
						(* Printf.printf "I managed to resolve location and I know that %s = %s\n" lvar (JSIL_Print.string_of_logic_expression loc false);  *)
						extend_subst pat_subst pat_aloc loc; discharges
					| None     ->
						(match subst with
						| None -> raise (Failure "Variable store against abstract location")
						| Some subst ->
							(* Printf.printf "I could not resolve the location and I am creating a new location\n"; *)
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
						if (Pure_Entailment.old_check_entailment SS.empty pfs [ (LEq (LVar lvar, LLit lit)) ] gamma)
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
	let end_time = Sys.time () in
	JSIL_Syntax.update_statistics "unify_stores" (end_time -. start_time);
	Some discharges
	with (Failure msg) -> 
		let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "unify_stores" (end_time -. start_time); None


let rec unify_lexprs le_pat (le : jsil_logic_expr) p_formulae (* solver *) (gamma: typing_environment) (subst : (string, jsil_logic_expr) Hashtbl.t) : (bool * ((string * jsil_logic_expr) list option)) =
	let start_time = Sys.time () in
	print_debug (Printf.sprintf ": %s versus %s" (JSIL_Print.string_of_logic_expression le_pat false)  (JSIL_Print.string_of_logic_expression le false));
	try (
	let result = (match le_pat with
	
	| LVar var
	| ALoc var ->
		(try
			let le_pat_subst = (Hashtbl.find subst var) in
			if (Pure_Entailment.is_equal le_pat_subst le p_formulae (* solver *) gamma)
				then (true,  None)
				else (false, None)
		with _ -> print_debug (Printf.sprintf "Abstract location or variable not in subst: %s %s" var (JSIL_Print.string_of_logic_expression le false));
				 	(true, Some [ (var, le) ]))

	| LLit _
	| LNone ->
		if (Pure_Entailment.is_equal le_pat le p_formulae gamma)
			then (true, None)
			else (false, None)

  | LUnknown -> (false, None)

	| le_pat when (isList le_pat && isList le && (match le with | LVar _ -> false | _ -> true)) ->
			print_debug (Printf.sprintf "ULEXPRLIST: %s %s" (print_lexpr le_pat) (print_lexpr le));
			let osubst = unify_lists le_pat le false in
			(match osubst with
			| None, _ -> (false, None)
			| Some _, sb ->
				
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
			print_debug "Second thingy not a list.";
			let le'' = find_me_Im_a_list (Hashtbl.create 1) p_formulae le' in
			let le''' = (match le'' with
			| LVar v ->
					let fake_symb_state = (LHeap.create 1, Hashtbl.create 1, (DynArray.copy p_formulae), (copy_gamma gamma), DynArray.create ()) in
					let simpl_pfs, _ = simplify_pfs p_formulae gamma true in
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
			print_debug (Printf.sprintf "Search says: %s\n" (JSIL_Print.string_of_logic_expression le'' false));
			if (le'' == le') then (false, None)
			else
			begin
				let (is_eq, whatever) = unify_lexprs le_pat le'' p_formulae (* solver *) gamma subst in
				(* Printf.printf "And they aaaare: %b\n" is_eq; *)
				(is_eq, whatever)
			end)			
	
	| _ ->
		let le_pat' = lexpr_substitution le_pat subst false in 
		 if (must_be_equal le_pat' le p_formulae gamma subst) 
		 	then (true, None) 
		 	else (
		 		let msg = Printf.sprintf "Illegal expression in pattern to unify. le_pat: %s. le: %s."
					(JSIL_Print.string_of_logic_expression le_pat false) (JSIL_Print.string_of_logic_expression le false) in
				raise (Failure msg)) 
		) in
	let end_time = Sys.time () in
	JSIL_Syntax.update_statistics "unify_lexprs" (end_time -. start_time);
	let b, _ = result in print_debug (Printf.sprintf "Result: %b" b);
	result) 
	with
		| Failure msg -> 
			let end_time = Sys.time () in
			JSIL_Syntax.update_statistics "unify_lexprs" (end_time -. start_time);
			raise (Failure msg)



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
let unify_fv_pair ((pat_field, pat_value) : (jsil_logic_expr * jsil_logic_expr)) 
									(fv_list                : symbolic_field_value_list) 
									(p_formulae             : pure_formulae) 
									(gamma                  : typing_environment) 
									(subst                  : substitution)  
										: bool * bool * ((symbolic_field_value_list * (jsil_logic_expr * jsil_logic_expr)) option) =
	
	(* Printf.printf "unify_fv_pair. pat_field: %s, pat_value: %s\n" (JSIL_Print.string_of_logic_expression pat_field false) (JSIL_Print.string_of_logic_expression pat_value false);
	Printf.printf "fv_list: %s\n" (JSIL_Memory_Print.string_of_symb_fv_list fv_list false); *)
	let rec loop fv_list traversed_fv_list i_have_not_found_the_field_for_sure =
		
		(* Before trying to unify (pat_field, pat_val) with the rest of the    *)
		(* fv_list, check if the current field and pat_field must be the same. *)
		(* If they must be the same, the unfication fails immediately, because *)
		(* the pat_field is equal to the current field but their expressions   *)
		(* do not coincide.                                                    *)
		
		let guarded_loop_next_2 e_field e_value rest = 
			let new_traversed_field_list = (e_field, e_value) :: traversed_fv_list in 
			if (not i_have_not_found_the_field_for_sure) 
				then loop rest new_traversed_field_list false 
				else loop rest new_traversed_field_list (must_be_different pat_field e_field p_formulae gamma subst) in 
		
		let guarded_loop_next_1 e_field e_value rest =
			if (must_be_equal pat_field e_field p_formulae gamma subst)
				then (true, false, None)
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
					if (Symbolic_State_Functions.update_subst2 subst fu vu p_formulae gamma)
						then (false, false, Some ((traversed_fv_list @ rest), (e_field, e_value)))
						else guarded_loop_next_1 e_field e_value rest
				| false -> guarded_loop_next_1 e_field e_value rest)
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
let unify_symb_fv_lists (pat_fv_list : symbolic_field_value_list)
												(fv_list     : symbolic_field_value_list)
												(def_val     : jsil_logic_expr) 
												(p_formulae  : pure_formulae)
												(gamma       : typing_environment) 
												(subst       : substitution) 
													: (symbolic_field_value_list * symbolic_field_value_list * symbolic_discharge_list) option =

	(* Printf.printf "Inside unify_symb_fv_lists.\npat_fv_list: \n%s.\nfv_list: \n%s.\n" (JSIL_Memory_Print.string_of_symb_fv_list pat_fv_list false) (JSIL_Memory_Print.string_of_symb_fv_list fv_list false); *)

	let rec loop (fv_list : symbolic_field_value_list) (pat_list : symbolic_field_value_list) (matched_fv_list : symbolic_field_value_list) (discharges : symbolic_discharge_list) =
		match pat_list with
		| [] -> Some (fv_list, matched_fv_list, discharges)
		| (pat_field, pat_val) :: rest_pat_list ->
			let pf_equal, pf_different, res = unify_fv_pair (pat_field, pat_val) fv_list p_formulae gamma subst in
			
			(match pf_equal, pf_different, res with
			| true,  true,  _    -> raise (Failure "Death: unify_symb_fv_lists")
			| true,  false, None -> None
			| false, _,  None ->
				print_debug (Printf.sprintf "I could NOT unify an fv-pair. pat_val: %s. def_val: %s" (JSIL_Print.string_of_logic_expression pat_val false) (JSIL_Print.string_of_logic_expression def_val false));
				(match def_val with
				| LUnknown -> None
				| _ ->
					let (bv, unifier) = unify_lexprs pat_val def_val p_formulae gamma subst in
					if (bv && (Symbolic_State_Functions.update_subst1 subst unifier))
						then (
							if (pf_different) 
								then loop fv_list rest_pat_list matched_fv_list discharges
								else (
									let new_discharges = List.map (fun (field, _) -> (field, pat_field)) fv_list in 
									loop fv_list rest_pat_list matched_fv_list (new_discharges @ discharges)			
						)) else None)
			| _, _, Some (rest_fv_list, matched_fv_pair) ->
				loop rest_fv_list rest_pat_list (matched_fv_pair :: matched_fv_list) discharges) in
	let order_pat_list = order_fv_list pat_fv_list in
	loop fv_list order_pat_list [] []





let unify_symb_heaps (pat_heap : symbolic_heap) (heap : symbolic_heap) pure_formulae (* solver *) gamma (subst : substitution) : (symbolic_heap * (jsil_logic_assertion list) * symbolic_discharge_list) option =
	print_debug (Printf.sprintf "Unify heaps %s \nand %s \nwith substitution: %s\nwith pure formulae: %s\nwith gamma: %s"
		(JSIL_Memory_Print.string_of_shallow_symb_heap pat_heap false)
		(JSIL_Memory_Print.string_of_shallow_symb_heap heap false)
		(JSIL_Memory_Print.string_of_substitution subst)
		(JSIL_Memory_Print.string_of_shallow_p_formulae pure_formulae false)
		(JSIL_Memory_Print.string_of_gamma gamma));
	let start_time = Sys.time () in
	let quotient_heap = LHeap.create 1021 in
	let pat_heap_domain : string list = heap_domain pat_heap subst in
	print_debug (Printf.sprintf "PatHeapDomain: %s" (String.concat ", " pat_heap_domain));
	
	let just_pick_the_first locs = 
		match locs with 
		| [] -> print_debug "DEATH. just_pick_the_first\n"; raise (Failure "DEATH: unify_symb_heaps")
		| loc :: rest -> loc, rest in 
	
	
	let rec pick_loc_that_exists_in_both_heaps locs traversed_locs  = 
		match locs with 
		| [] -> just_pick_the_first traversed_locs
		| loc :: rest -> 
			if (LHeap.mem heap loc) 
				then loc, (traversed_locs @ rest) 
				else pick_loc_that_exists_in_both_heaps rest (traversed_locs @ [ loc ]) in 
	
	let pick_pat_loc (locs_to_visit : string list) subst : string * (string list) = 
		print_debug "pick_pat_loc\n";
		
		let rec loop (remaining_locs : string list) (traversed_locs : string list) : string * (string list) = 
			match remaining_locs with 
			| [] -> pick_loc_that_exists_in_both_heaps traversed_locs []
			| loc :: rest -> 
				if ((not (is_abs_loc_name loc)) || (Hashtbl.mem subst loc)) 
					then loc, (traversed_locs @ rest) 
					else loop rest (traversed_locs @ [ loc ]) in 
		loop locs_to_visit [] in 	
		
	try
		(* let pfs : jsil_logic_assertion list =
			List.fold_left
				(fun pfs pat_loc -> *)
					
		let rec loop locs_to_visit pfs discharges = 
			(match locs_to_visit with 
			| [] -> (pfs, discharges)
			| _ ->  
				let pat_loc, rest_locs = pick_pat_loc locs_to_visit subst in  
				print_debug (Printf.sprintf "Location: %s" pat_loc);
				print_debug (Printf.sprintf "Substitution: %s" (JSIL_Memory_Print.string_of_substitution subst));
				(match heap_get pat_heap pat_loc with
				| Some (pat_fv_list, pat_def) ->
			  	(if ((pat_def <> LNone) && (pat_def <> LUnknown)) then raise (Failure "Illegal Default Value")  else (
						let loc = try
							let le = Hashtbl.find subst pat_loc in
							(match le with
							| LLit (Loc loc) -> loc
							| ALoc loc -> loc
							| LVar v -> 
								let loc = find_me_Im_a_loc (pfs_to_list pure_formulae) le in 
								(match loc with 
								| Some loc -> loc
								| None -> raise (Failure "I cannot unify this"))
				  		| _ ->
								(* I really think this case is wrong!!!*)
								pat_loc)
							with _ -> (* this case is very interesting *) pat_loc in
						let fv_list, (def : jsil_logic_expr) =
							(try LHeap.find heap loc with _ ->
								let msg = Printf.sprintf "Location %s in pattern has not been matched" loc in
								Printf.printf "%s\n" msg;
								raise (Failure msg)) in
						let fv_lists = unify_symb_fv_lists pat_fv_list fv_list def pure_formulae (* solver *) gamma subst in
						(match fv_lists with
						| Some (new_fv_list, matched_fv_list, new_discharges) when ((pat_def = LNone) && ((List.length new_fv_list) > 0)) ->
							print_debug (Printf.sprintf "fv_lists unified successfully");
							print_debug (Printf.sprintf "QH: %s" (JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false));
							let all_fields_in_new_fv_list_are_none =
								List.fold_left (fun ac (_, field_val) -> if (not ac) then ac else (field_val = LNone)) true new_fv_list in
							if all_fields_in_new_fv_list_are_none then
								(LHeap.replace quotient_heap loc ([], def); 
								loop rest_locs pfs (new_discharges @ discharges))
							else raise (Failure "LNone in precondition")
						| Some (new_fv_list, matched_fv_list, new_discharges) ->
							LHeap.replace quotient_heap loc (new_fv_list, def);
							print_debug (Printf.sprintf "Adding sth to QH.");
							print_debug (Printf.sprintf "QH: %s" (JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false));
							let new_pfs : jsil_logic_assertion list = make_all_different_pure_assertion new_fv_list matched_fv_list in
							loop rest_locs (new_pfs @ pfs) (new_discharges @ discharges)
						| None -> print_debug "fv_lists not unifiable!"; raise (Failure ("fv_lists not unifiable")))))
					| _ -> raise (Failure ("Pattern heaps cannot have default values")))) in 
			
		let (pfs : (jsil_logic_assertion list)), (discharges: (symbolic_discharge_list)) = loop pat_heap_domain [] [] in 
				
		print_debug (Printf.sprintf "Heap again %s" (JSIL_Memory_Print.string_of_shallow_symb_heap heap false));
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
		let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "unify_symb_heaps" (end_time -. start_time);
		print_debug (Printf.sprintf "End of unify_symb_heaps: do enjoy the quotient_heap: %s" (JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false));
		Some (quotient_heap, pfs, discharges)
	with (Failure msg) ->
		let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "unify_symb_heaps" (end_time -. start_time);
		None



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
	
	print_debug "----------------------------";
	print_debug (Printf.sprintf "Unification options: %d" (Queue.length ps));
	print_debug (JSIL_Memory_Print.string_of_substitution subst);
	Queue.iter (fun (unified, remaining, unmatched) ->
		print_debug "-------\nOption:\n-------";
		List.iter2 (fun (pat_name, pat_params) unified ->
			let unified_str = (match unified with
			| None -> "None"
			| Some (uni_name, uni_params) -> Printf.sprintf "%s(%s)" 
				uni_name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) uni_params))) in
			print_debug (Printf.sprintf "%s(%s) \t\t vs.\t\t%s"
				pat_name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) pat_params))
				unified_str
				)
			) (DynArray.to_list pat_preds) (DynArray.to_list unified);
			print_debug "Unmatched predicates:";
			DynArray.iter (fun (name, params) -> print_debug (Printf.sprintf "\t%s(%s)" 
				name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) params)))) remaining;
			print_debug "Unmatched pat predicates:";
			List.iter (fun (name, params) -> print_debug (Printf.sprintf "\t%s(%s)" 
				name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) params)))) unmatched;
		
		) ps;
	print_debug "----------------------------";
	
	let result = Array.of_list 
		(List.rev 
			(Queue.fold (fun ac (x, y, z) -> 
				assert (DynArray.length pat_preds = DynArray.length x);
				let x = List.combine (DynArray.to_list pat_preds) (DynArray.to_list x) in
				let x = List.filter (fun (_, x) -> x <> None) x in
				let x = Array.of_list (List.map (fun (x, y) -> (x, Option.get y)) x) in
				(Hashtbl.copy subst, x, y, z) :: ac) [] ps)) in result
	
(*******************************************************************)

let rec unify_expr_lists pat_list list p_formulae gamma subst =
	(match pat_list, list with
	| [], [] -> true
	| (pat_le :: rest_pat_list), (le :: rest_list) ->
		let (bv, unifier) = unify_lexprs pat_le le p_formulae gamma subst in
		if (bv && Symbolic_State_Functions.update_subst1 subst unifier)
			then unify_expr_lists rest_pat_list rest_list p_formulae gamma subst
			else false
	| _, _ -> false)

(*******************************************************************)

let unify_preds subst unifier p_formulae gamma =
	let i = ref 0 in
	let n = Array.length unifier in
	let ok = ref true in
		while (!ok && (!i < n)) do
			let ((pat_pred_name, pat_pred_params), (cand_pred_name, cand_pred_params)) = Array.get unifier !i in
			assert (pat_pred_name = cand_pred_name);
			assert (List.length pat_pred_params = List.length cand_pred_params);
			let result = unify_expr_lists pat_pred_params cand_pred_params p_formulae gamma subst in
			ok := result;
			i := !i + 1;
		done;
		if (not !ok) 
			then None
			else Some subst

(*******************************************************************)

(**
 * Returns a list of triples of the form (substitution, preds that haven't been unified, pat_preds that haven't been unified)
 *)
let unify_pred_arrays (pat_preds : predicate_set) (preds : predicate_set) p_formulae gamma (subst : substitution) =
	print_debug "Entering unify_pred_arrays.";
	
	let result = (match (DynArray.length pat_preds) with
	| 0 -> Some (subst, preds, [])
	| _ -> 
		let pat_preds = DynArray.to_list pat_preds in
		let preds = DynArray.to_list preds in
		let p_formulae = DynArray.copy p_formulae in
		let gamma = Hashtbl.copy gamma in
		let subst = Hashtbl.copy subst in
		
		let ps = get_unification_candidates (DynArray.of_list pat_preds) (DynArray.of_list preds) p_formulae gamma subst in
		
		let i = ref 0 in
		let n = Array.length ps in
		let options = DynArray.create() in
		let unified = ref false in
		while ((not !unified) && (!i < n)) do
			let (subst, unifier, unmatched_preds, unmatched_pat_preds) = Array.get ps !i in
			let result = unify_preds subst unifier p_formulae gamma in
			let result = (match result with
			| None -> None
			| Some subst -> Some (subst, unmatched_preds, unmatched_pat_preds)) in
			DynArray.add options result;
			i := !i + 1;
		done;
			
		let reasonable_options = List.map (fun x -> Option.get x) (List.filter (fun x -> x <> None) (DynArray.to_list options)) in
		let reasonable_options = List.sort 
			(fun (_, _, upp1) (_, _, upp2) -> 
				let len1 = List.length upp1 in
				let len2 = List.length upp2 in
					compare len1 len2) 
					reasonable_options in
					
		print_debug (Printf.sprintf "--------\nOutcomes: %d\n--------" (List.length reasonable_options));
		List.iter (fun (subst, unmatched_preds, unmatched_pat_preds) -> 
				print_debug (Printf.sprintf "Substitution: %s" (JSIL_Memory_Print.string_of_substitution subst));
				print_debug "Unmatched predicates:";
				DynArray.iter (fun (name, params) -> print_debug (Printf.sprintf "\t%s(%s)" 
					name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) params)))) unmatched_preds;
				print_debug "Unmatched pat predicates:";
				List.iter (fun (name, params) -> print_debug (Printf.sprintf "\t%s(%s)" 
					name (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) params)))) unmatched_pat_preds;
			) reasonable_options;
		print_debug "-------------------------";
		
		
		(match reasonable_options with
		| [] -> None  
		| [ op ] -> Some op
		| _ :: (op :: _) -> 
			(match !interactive with
			| false -> Some op
		  | true -> 
				print_debug "Choose branch (0 = None): ";
				let n = read_int() in
				print_debug (Printf.sprintf "The user has chosen the branch: %d" n);
				if (n = 0) 
					then Some (subst, DynArray.of_list preds, pat_preds) 
					else Some (DynArray.get (DynArray.of_list reasonable_options) (n - 1)))
		)) in
		
		result

(*******************************************************************)
(*******************************************************************)
(*******************************************************************)



let unify_gamma pat_gamma gamma pat_store subst (ignore_vars : SS.t) =
	print_debug (Printf.sprintf "I am about to unify two gammas\n");
 	print_debug (Printf.sprintf "pat_gamma: %s.\ngamma: %s.\nsubst: %s\n"
	(JSIL_Memory_Print.string_of_gamma pat_gamma) (JSIL_Memory_Print.string_of_gamma gamma)
	(JSIL_Memory_Print.string_of_substitution subst));
	let start_time = Sys.time () in
	let res = (Hashtbl.fold
		(fun var v_type ac ->
			print_debug (Printf.sprintf "pat_var: (%s : %s) " var (JSIL_Print.string_of_type v_type));
			(* (not (is_lvar_name var)) *)
			(if ((not ac) || (SS.mem var ignore_vars))
				then ac
				else
					try
						let le =
							(if (is_lvar_name var)
								then Hashtbl.find subst var
								else
									(match (store_get_safe pat_store var) with
									| Some le -> JSIL_Logic_Utils.lexpr_substitution le subst true
									| None -> (PVar var))) in
						print_debug (Printf.sprintf "found value: %s" (JSIL_Print.string_of_logic_expression le false));
						let le_type, is_typable, _ = JSIL_Logic_Utils.type_lexpr gamma le in
						match le_type with
						| Some le_type ->
							  print_debug (Printf.sprintf "unify_gamma. pat gamma var: %s. le: %s. v_type: %s. le_type: %s"
								var (JSIL_Print.string_of_logic_expression le false) (JSIL_Print.string_of_type v_type) (JSIL_Print.string_of_type le_type));
							(le_type = v_type)
						| None ->
								print_debug (Printf.sprintf "failed unify_gamma. pat gamma var: %s. le: %s. v_type: %s"
								var (JSIL_Print.string_of_logic_expression le false) (JSIL_Print.string_of_type v_type));
							false
					with _ ->
						true))
		pat_gamma
		true) in
	print_debug (Printf.sprintf "\nEXITING unify_gamma: res: %b\n\n" res);
	let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "unify_gamma" (end_time -. start_time);
		res


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
	let ret = Pure_Entailment.old_check_entailment SS.empty pf_list pfs_to_prove gamma in
	(* Printf.printf "Check if \n (%s) \n entails \n (%s) \n with gamma \n (%s) \nret: %b\n" (JSIL_Print.str_of_assertion_list pf_list) (JSIL_Print.str_of_assertion_list pfs_to_prove) (JSIL_Memory_Print.string_of_gamma gamma) ret; *)
	ret


let pf_list_of_discharges discharges subst partial =
	let rec loop discharges pfs =
		match discharges with
		| [] -> pfs
		| (le_pat, le) :: rest_discharges ->
			let s_le_pat = JSIL_Logic_Utils.lexpr_substitution le_pat subst partial in
			loop rest_discharges ((LEq (s_le_pat, le)) :: pfs) in
	loop discharges []



let unify_symb_states lvars pat_symb_state (symb_state : symbolic_state) : (bool * symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * typing_environment) option  =

	print_debug (Printf.sprintf "LVARS: %s" (String.concat ", " (SS.elements lvars)));

	let start_time = Sys.time () in

	let heap_0, store_0, pf_0, gamma_0, preds_0 (*, solver *) = symb_state in
	let heap_1, store_1, pf_1, gamma_1, preds_1 (*, _  *) = copy_symb_state pat_symb_state in
	let subst = init_substitution [] in
	SS.iter (fun var -> Hashtbl.replace subst var (LVar var)) lvars;

	print_debug (Printf.sprintf "Current substitution: %s" (JSIL_Memory_Print.string_of_substitution subst));

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
		let discharges_0 = unify_stores store_1 store_0 subst None (pfs_to_list pf_0) (* solver *) gamma_0 in
		let result = (match discharges_0 with
		| Some discharges_0 ->
			print_debug (Printf.sprintf "Discharges: %d\n" (List.length discharges_0));
			List.iter (fun (x, y) -> print_debug (Printf.sprintf "\t%s : %s\n" (JSIL_Print.string_of_logic_expression x false) (JSIL_Print.string_of_logic_expression y false))) discharges_0;
			let keep_subst = Hashtbl.copy subst in
			(* First try to unify heaps, then predicates *)
			let ret_1 = unify_symb_heaps heap_1 heap_0 pf_0 (* solver *) gamma_0 subst in
			(match ret_1 with
			| Some (heap_f, new_pfs, negative_discharges) ->
				print_debug (Printf.sprintf "Heaps unified successfully. Unifying predicates.\n");
				let ret_2 = unify_pred_arrays preds_1 preds_0 pf_0 (* solver *) gamma_0 subst in
				(match ret_2 with
				| Some (subst, preds_f, []) ->
					let spec_vars_check = spec_logic_vars_discharge subst lvars pf_0 gamma_0 in
					Some (discharges_0, subst, heap_f, preds_f, new_pfs)
				| _ -> ( print_debug (Printf.sprintf "Failed to unify predicates\n"); None))
			| None -> 
					print_debug (Printf.sprintf "Could not unify heaps before predicates, unifying predicates first instead."); 
					let ret_2 = unify_pred_arrays preds_1 preds_0 pf_0 gamma_0 subst in
					(match ret_2 with
					| Some (subst, preds_f, []) ->
						let spec_vars_check = spec_logic_vars_discharge subst lvars pf_0 gamma_0 in
						print_debug "Unified predicates successfully. Extracting additional knowledge";
						
						(***** EXPERIMENTAL - PUT INTO SEPARATE FUNCTION *****)

						let pat_pfs = pf_substitution pf_1 subst true in
						let _, pf_subst = simplify_pfs_with_subst pf_0 gamma_0 in
						(match pf_subst with
						| None -> print_debug (Printf.sprintf "Failed to unify heaps definitively. Contradiction in pat_pfs." ); None
						| Some pf_subst -> 
							(let pat_pfs = pf_substitution pat_pfs pf_subst true in
							print_debug (Printf.sprintf "Original pat_pfs:\n%s" (JSIL_Memory_Print.string_of_shallow_p_formulae pf_1 false));
							print_debug (Printf.sprintf "Substituted pat_pfs:\n%s" (JSIL_Memory_Print.string_of_shallow_p_formulae pat_pfs false));
							let new_pfs, _ = simplify_pfs pat_pfs gamma_0 true in
							(match (DynArray.to_list new_pfs) with
							| [ LFalse ] -> print_debug (Printf.sprintf "Failed to unify heaps definitively. Contradiction in pat_pfs." ); None
							| _ -> 
									print_debug (Printf.sprintf "More pfs: %s" (JSIL_Memory_Print.string_of_shallow_p_formulae new_pfs false));
									
									(* Now we can extract two things: more subst and more alocs *)
									let hd = SS.of_list (heap_domain heap_1 subst) in
									print_debug (Printf.sprintf "Domain of the pat_heap: %s" (String.concat ", " (SS.elements hd)));
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
	
									print_debug "Now unifying heaps again.";
									print_debug (Printf.sprintf "%s" (JSIL_Memory_Print.string_of_substitution subst));
									let ret_1 = unify_symb_heaps heap_1 heap_0 pf_0 gamma_0 subst in
									(match ret_1 with
									| Some (heap_f, new_pfs, negative_discharges) ->
										print_debug (Printf.sprintf "Heaps unified successfully.\n");
										Some (discharges_0, subst, heap_f, preds_f, new_pfs)
									| None -> print_debug (Printf.sprintf "Failed to unify heaps and predicates definitively."); None ))))
					| _ -> print_debug (Printf.sprintf "Failed to unify predicates and heaps definitively.\n"); None ))
		| None -> print_debug (Printf.sprintf "Failed to unify stores\n" ); None) in
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
		let start_time = Sys.time() in
		
		print_debug (Printf.sprintf "Current substitution again: %s" (JSIL_Memory_Print.string_of_substitution subst));
		
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
		let unify_gamma_check = (unify_gamma gamma_1 gamma_0' store_1 subst existentials) in
		let result = if (unify_gamma_check) then
		begin
			merge_pfs pf_0 (DynArray.of_list new_pfs);
		  let pf_1_subst_list = List.map (fun a -> assertion_substitution a subst true) (pfs_to_list pf_1) in
			let pf_discharges = pf_list_of_discharges discharges subst false in
			let pfs = pf_1_subst_list @ pf_discharges in

			print_debug (Printf.sprintf "Checking if %s\n entails %s\n with existentials\n%s\nand gamma %s"
				(JSIL_Memory_Print.string_of_shallow_p_formulae pf_0 false)
				(JSIL_Memory_Print.string_of_shallow_p_formulae (DynArray.of_list pfs) false)
				(List.fold_left (fun ac x -> ac ^ " " ^ x) "" fresh_names_for_existentials)
				(JSIL_Memory_Print.string_of_gamma gamma_0'));

			let entailment_check_ret = Pure_Entailment.old_check_entailment (SS.of_list fresh_names_for_existentials) (pfs_to_list pf_0) pfs gamma_0' in
			print_debug (Printf.sprintf "unify_gamma_check: %b. entailment_check: %b" unify_gamma_check entailment_check_ret);
			Some (entailment_check_ret, pf_discharges, pf_1_subst_list, gamma_0')
		end else (print_debug "Gammas not unifiable."; None) in
		let end_time = Sys.time() in
		JSIL_Syntax.update_statistics "USS: Step 1" (end_time -. start_time);
		result in

	(* Actually doing it!!! *)
	let result = (match step_0 subst with
	| Some (discharges, subst, heap_f, preds_f, new_pfs) ->
		(match (step_1 discharges subst new_pfs) with
		| Some (entailment_check_ret, pf_discharges, pf_1_subst_list, gamma_0') -> Some (entailment_check_ret, heap_f, preds_f, subst, (pf_1_subst_list @ pf_discharges), gamma_0')
		| None -> None)
	| None -> None) in
	let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "unify_symb_states" (end_time -. start_time);
		result




let unify_symb_states_fold (pred_name : string) (existentials : SS.t) (pat_symb_state : symbolic_state) (symb_state : symbolic_state) : (bool * symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * typing_environment * SS.t * ((string * (jsil_logic_expr list)) list)) option  =
	let heap_0, store_0, pf_0, gamma_0, preds_0 (*, solver_0 *) = symb_state in
	let heap_1, store_1, pf_1, gamma_1, preds_1 (*, _ *) = pat_symb_state in
	(** Auxiliary Functions **)

 	print_debug (Printf.sprintf "store_0: %s.\nstore_1: %s" 
		(JSIL_Memory_Print.string_of_shallow_symb_store store_0 false)
		(JSIL_Memory_Print.string_of_shallow_symb_store store_1 false)); 
				
	(* existentials -> new variables introduced by the fold                                      *)
	(* store_vars -> vars in the store which are mapped to logical expressions with existentials *)
	let find_existentials_types (existentials : SS.t) store_vars (store : symbolic_store) gamma pat_gamma =
		let gamma_existentials = mk_gamma () in
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
	(*  let discharges_1 = unify_stores (new_store_0, new_store_1, subst, pi_0, gamma_0)	                                   *)
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
			try
				Some
					(List.fold_left
						(fun ac x ->
							let le_0 = store_get_safe store_0 x in
							let le_1 = store_get_safe store_1 x in
							match le_0, le_1 with
							| Some le_0, Some le_1 -> (le_1, le_0) :: ac
							| _, None -> ac
							| _ -> raise (Failure ""))
						[]
						filtered_vars)
			with _ -> None in
		print_debug (Printf.sprintf "\t\tGot the discharges: %d" (if_some discharges_0 (fun x -> List.length x) (-1)));
		let store_0' = store_projection store_0 unfiltered_vars in
		let store_1' = store_projection store_1 unfiltered_vars in
		
		print_debug (Printf.sprintf "store_0: %s.\nstore_1: %s" 
			(JSIL_Memory_Print.string_of_shallow_symb_store store_0 false)
			(JSIL_Memory_Print.string_of_shallow_symb_store store_1 false)); 
		
		print_debug (Printf.sprintf "store_0': %s.\nstore_1': %s" 
			(JSIL_Memory_Print.string_of_shallow_symb_store store_0' false)
			(JSIL_Memory_Print.string_of_shallow_symb_store store_1' false)); 
		
		let discharges_1 = unify_stores store_1' store_0' subst None (pfs_to_list pf_0) (* solver_0 *) gamma_0 in
		match discharges_0, discharges_1 with
		| Some discharges_0, Some discharges_1 ->
			Some (subst, filtered_vars, unfiltered_vars, gamma_existentials, (discharges_0 @ discharges_1))
		| _, _ -> None in


	(* STEP 1 *)
	let step_1 subst =
		print_debug "\tEntering step 1.";
		let ret_1 = unify_symb_heaps heap_1 heap_0 pf_0 (* solver_0 *) gamma_0 subst in
		(match ret_1 with
		| Some (heap_f, new_pfs, negative_discharges) ->
			let ret_2 = unify_pred_arrays preds_1 preds_0 pf_0 (* solver_0 *) gamma_0 subst in
			(match ret_2 with
			| Some (new_subst, preds_f, unmatched_pat_preds) -> 
				print_debug 
					(Printf.sprintf "subst after unify_heaps: %s" (JSIL_Memory_Print.string_of_substitution subst));
				print_debug 
					(Printf.sprintf "subst after unify_preds: %s" (JSIL_Memory_Print.string_of_substitution new_subst));
				Some (heap_f, preds_f, subst, new_subst, new_pfs, unmatched_pat_preds)
			| None -> None)
		| None -> None) in


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
		let unify_gamma_check = (unify_gamma gamma_1 gamma_0' store_0 subst pat_existentials) in
		if (unify_gamma_check) then
		begin
			let pf_1_subst_list = List.map (fun a -> assertion_substitution a subst true) (pfs_to_list pf_1) in
			let pf_discharges = pf_list_of_discharges discharges subst false in
			let pfs = DynArray.of_list (pf_1_subst_list @ pf_discharges) in
			sanitise_pfs_no_store gamma_0' pfs;
			(* Moving formulae on the left which contain existentials to the right *)
			let pf0 = DynArray.copy pf_0 in
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

			print_debug (Printf.sprintf "Checking if %s\n entails %s\n with existentials\n%s\nand gamma %s"
				(JSIL_Memory_Print.string_of_shallow_p_formulae pf0 false)
				(JSIL_Memory_Print.string_of_shallow_p_formulae pfs false)
				(List.fold_left (fun ac x -> ac ^ " " ^ x) "" (SS.elements new_existentials))
				(JSIL_Memory_Print.string_of_gamma gamma_0'));

			let entailment_check = Pure_Entailment.old_check_entailment new_existentials (pfs_to_list pf0) (pfs_to_list pfs) gamma_0' in
			(* (if (not entailment_check) then Pure_Entailment.understand_error new_existentials (pfs_to_list pf0) (pfs_to_list pfs) gamma_0'); *)
			(entailment_check, pf_discharges, pf_1_subst_list, gamma_0', new_existentials)
		end
		else
		 	(false, [], [], gamma_0', new_existentials) in

	let recovery_step heap_f subst filtered_vars gamma_existentials new_pfs discharges = 
		(* take the predicate out of the pat_preds *)
		(* unify the preds *)
		(* call step 2 *) 
		
		print_debug (Printf.sprintf "subst in recovery before re-unification of preds: %s" (JSIL_Memory_Print.string_of_substitution subst));
		
		let copied_preds_1 = copy_pred_set preds_1 in 
		let subtracted_pred_ass = simple_subtract_pred copied_preds_1 pred_name in 
		match subtracted_pred_ass with 
		| None -> None 
		| Some subtracted_pred_ass -> 
			print_debug 
				(Printf.sprintf "In the middle of the recovery biaaaattccchhhh!!! the pat_preds as they are now:\n%s\n" 
					(JSIL_Memory_Print.string_of_preds copied_preds_1 false)); 
			let ret = unify_pred_arrays copied_preds_1 preds_0 pf_0 (* solver_0 *) gamma_0 subst in
			(match ret with
			| Some (subst, preds_f, []) -> 
				print_debug (Printf.sprintf "subst in recovery after re-unify_preds: %s" (JSIL_Memory_Print.string_of_substitution subst));
				let entailment_check_ret, pf_discharges, pf_1_subst_list, gamma_0', new_existentials = step_2 subst filtered_vars gamma_existentials new_pfs discharges in
				Some (entailment_check_ret, heap_f, preds_f, subst, (pf_1_subst_list @ pf_discharges), gamma_0', new_existentials, [ subtracted_pred_ass ])
			| _ -> None) in 
	
	(* Actually doing it!!! *)
	match step_0 () with
	| Some (subst, filtered_vars, _, gamma_existentials, discharges) ->
		print_debug "Passed step 0.";
		(match step_1 subst with
		| Some (heap_f, preds_f, old_subst, subst, new_pfs, unmatched_pat_preds) ->
		  print_debug "Passed step 1.";
		  let entailment_check_ret, pf_discharges, pf_1_subst_list, gamma_0', new_existentials = step_2 subst filtered_vars gamma_existentials new_pfs discharges in
			(match entailment_check_ret with 
			| true  -> Some (entailment_check_ret, heap_f, preds_f, subst, (pf_1_subst_list @ pf_discharges), gamma_0', new_existentials, unmatched_pat_preds)
			| false -> recovery_step heap_f old_subst filtered_vars gamma_existentials new_pfs discharges)
		| None -> print_debug "Failed in step 1!"; None)
	| None -> print_debug "Failed in step 0!"; None



(* get rid of the js flag here ASAP *) 
let fully_unify_symb_state pat_symb_state symb_state lvars (js : bool) =
	print_debug (Printf.sprintf "Fully_unify_symb_state.\nSymb_state:\n%s.\nPAT symb_state:\n%s" (JSIL_Memory_Print.string_of_shallow_symb_state symb_state) (JSIL_Memory_Print.string_of_shallow_symb_state pat_symb_state)); 
	
	let unifier = unify_symb_states lvars pat_symb_state symb_state in
	match unifier with
	| Some (true, quotient_heap, quotient_preds, subst, pf_discharges, _) ->
		let emp_heap = (is_heap_empty quotient_heap js) in
		let emp_preds = (is_preds_empty quotient_preds) in
		if (emp_heap && emp_preds) then
			(Some subst, "")
		else
			let _ = if (emp_heap) then begin Printf.printf "Quotient heap empty.\n" end
					else begin Printf.printf "Quotient heap left: \n%s\n" (JSIL_Memory_Print.string_of_shallow_symb_heap quotient_heap false) end in
			let _ = if (emp_preds) then begin Printf.printf "Quotient predicates empty.\n" end
					else begin Printf.printf "Quotient predicates left: \n%s\n" (JSIL_Memory_Print.string_of_preds quotient_preds false) end in
			(None, "Oops, incomplete match")
	| Some (false, _, _, _, _,_)
	| None -> (None, "sorry, non_unifiable heaps")


let unify_symb_state_against_post proc_name spec symb_state flag symb_exe_info js =
	let print_error_to_console msg =
		(if (msg = "")
			then Printf.printf "Failed to verify a spec of proc %s\n" proc_name
			else Printf.printf "Failed to verify a spec of proc %s -- %s\n" proc_name msg);
		let final_symb_state_str = JSIL_Memory_Print.string_of_shallow_symb_state symb_state in
		let post_symb_state_str = JSIL_Memory_Print.string_of_symb_state_list spec.n_post in
		Printf.printf "Final symbolic state: %s\n" final_symb_state_str;
		Printf.printf "Post condition: %s\n" post_symb_state_str in

	let rec loop posts i =
		(match posts with
		| [] -> print_error_to_console "Non_unifiable symbolic states";  raise (Failure "post condition is not unifiable")
		| post :: rest_posts ->
			let is_unifiable, msg = 
				if (js) then (
					let subst = unify_symb_states spec.n_lvars post symb_state in
					match subst with
					| Some (true, _, _, _, _, _) -> true, ""
					| _                          -> false, ""
				) else (
					let subst = fully_unify_symb_state post symb_state spec.n_lvars false in 
					match subst with 
					| Some _, _ -> true, ""
					| None, msg -> false, msg) in 
			if (is_unifiable) 	
				then (
					activate_post_in_post_pruning_info symb_exe_info proc_name i;
					print_endline (Printf.sprintf "Verified one spec of proc %s" proc_name)
				) else (
					print_debug (Printf.sprintf "No go: %s" msg); 
					loop rest_posts (i + 1)
				)) in 
					
	loop spec.n_post 0


let merge_symb_states 
		(symb_state_l : symbolic_state) 
		(symb_state_r : symbolic_state) 
		(subst : substitution) : symbolic_state =
	(* Printf.printf "gamma_r: %s\n." (JSIL_Memory_Print.string_of_gamma (get_gamma symb_state_r)); *)
	(* Printf.printf "substitution: %s\n" (JSIL_Memory_Print.string_of_substitution subst); *)
	let aux_symb_state = (copy_symb_state symb_state_r) in
	let symb_state_r = symb_state_substitution aux_symb_state subst false in
	let heap_l, store_l, pf_l, gamma_l, preds_l = symb_state_l in
	let heap_r, store_r, pf_r, gamma_r, preds_r = symb_state_r in
	merge_pfs pf_l pf_r;
	merge_gammas gamma_l gamma_r;
	Symbolic_State_Functions.merge_heaps heap_l heap_r pf_l gamma_l;
	DynArray.append preds_r preds_l;
	print_debug ("Finished merge_symb_states");
	(heap_l, store_l, pf_l, gamma_l, preds_l)

let safe_merge_symb_states (symb_state_l : symbolic_state) (symb_state_r : symbolic_state) (subst : substitution) : symbolic_state option =
	(* *)

	(* Printf.printf "gamma_r: %s\n." (JSIL_Memory_Print.string_of_gamma (get_gamma symb_state_r)); *)
	(* Printf.printf "substitution: %s\n" (JSIL_Memory_Print.string_of_substitution subst); *)

	let pf_r_existentials = get_subtraction_vars (get_symb_state_vars false symb_state_r) subst in
	let gammas_unifiable = unify_gamma (get_gamma symb_state_r) (get_gamma symb_state_l) (get_store symb_state_r) subst pf_r_existentials in

	let symb_state_r = symb_state_substitution symb_state_r subst false in
	let heap_l, store_l, pf_l, gamma_l, preds_l (*, solver_l *) = symb_state_l in
	let heap_r, store_r, pf_r, gamma_r, preds_r (*, _ *) = symb_state_r in
	merge_pfs pf_l pf_r;
	merge_gammas gamma_l gamma_r;


	let satisfiability_check = gammas_unifiable && (Pure_Entailment.check_satisfiability (pfs_to_list pf_l) gamma_l) in

	if (satisfiability_check)
		then (
			(* Printf.printf "BEFORE MERGING HEAPS. pfs_l: %s\n. pfs_r: %s\n." (JSIL_Memory_Print.string_of_shallow_p_formulae pf_l false)
				(JSIL_Memory_Print.string_of_shallow_p_formulae pf_r false); *)
			Symbolic_State_Functions.merge_heaps heap_l heap_r pf_l (* solver_l *) gamma_l;
			(* Printf.printf "AFTER MERGING HEAPS\n\n"; *)
			DynArray.append preds_r preds_l;
			(* *)
			(* Printf.printf "s_heap_l after merge: %s.\ns_preds_l: %s.\ns_store_l: %s.\n" (JSIL_Memory_Print.string_of_shallow_symb_heap heap_l)
					(JSIL_Memory_Print.string_of_preds preds_l) (JSIL_Memory_Print.string_of_shallow_symb_store store_l); *)
			(* *)
			Some (heap_l, store_l, pf_l, gamma_l, preds_l (*, (ref None) *)))
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
	let gamma_old = get_gamma symb_state in
	let symb_state = copy_symb_state symb_state in
	let store_0 = calling_store in
	let store_1 = get_store pat_symb_state in
	let gamma_0 = get_gamma symb_state in
	let gamma_1 = get_gamma pat_symb_state in
	let store_vars = store_domain store_0 in

	let find_store_var_type store gamma x =
		let le_x = store_get_safe store x in
		(match le_x with
		| Some le_x ->
			let x_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le_x in
			x_type
		| None -> None) in

	print_debug "Unfold predicate definition.";
	print_debug (Printf.sprintf "Store_0:\n%s.\n Store_1:\n%s."
		(JSIL_Memory_Print.string_of_shallow_symb_store store_0 false)
		(JSIL_Memory_Print.string_of_shallow_symb_store store_1 false));

	(* STEP 1 - Unify(store_0, store_1, pi_0) = subst, pat_subst, discharges                                               *)
	(* subst (store_0) =_{pi_0} pat_subst (store_1) provided that the discharges hold                                      *)
	(* we start by unifying the stores - this unification will produce two substituions: pat_subst and subst               *)
	(* pat_subst is to applied in the pat_symb_state and subst is to be applied in the symb_state                          *)
	(* The store unification also generates a list of discharges - discharges - which need to hold for the stores to match *)
	let step_1 () =
		let pat_subst = init_substitution [] in
		let subst = init_substitution [] in
		let discharges = unify_stores store_1 store_0 pat_subst (Some subst) (pfs_to_list (get_pf symb_state)) (* (get_solver symb_state) *) gamma_0 in
		(* Printf.printf "substitutions after store unification.\nSubst:\n%s\nPat_Subst:\n%s\n"
			(JSIL_Memory_Print.string_of_substitution subst)
			(JSIL_Memory_Print.string_of_substitution pat_subst);
		 Printf.printf "GAMMA_OLD - STEP 1:\n%s\n" (JSIL_Memory_Print.string_of_gamma gamma_old); *)
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
		(* Printf.printf "GAMMA_OLD - STEP 2:\n%s\n" (JSIL_Memory_Print.string_of_gamma gamma_old);	*)
		store_0_var_types, store_1_var_types, stores_are_type_compatible in


	(* STEP 3 - the substitutions need to make sense wrt the gammas                                                        *)
	(* forall x \in subst : subst(x) = le /\ Gamma_0(x) = tau =>  \Gamma_1 |- le : tau                                     *)
	(* forall x \in pat_subst : pat_subst (x) = le /\ Gamma_1(x) = tau => \Gamma_0                                         *)
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
		let gamma_0' = mk_gamma () in
		List.iter
			(fun x ->
				let le_x = store_get_safe store_0 x in
				let x_type = find_store_var_type store_1 gamma_1 x in
				match le_x, x_type with
				| Some le_x, Some x_type -> let _ = JSIL_Logic_Utils.reverse_type_lexpr_aux gamma_0 gamma_0' le_x x_type in ()
				|	_, _ -> ())
				untyped_store_0_vars;
		(* Printf.printf "GAMMA_OLD - STEP 4:\n%s\n" (JSIL_Memory_Print.string_of_gamma gamma_old);
		Printf.printf "Inferred typing information given the unfolding:\n%s\n" (JSIL_Memory_Print.string_of_gamma gamma_0'); *)
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
		(* Printf.printf "gamma_1'' is:\n%s\n" (JSIL_Memory_Print.string_of_gamma gamma_1''); *)
		extend_gamma gamma_0 gamma_1'';
		let gamma = gamma_0 in
		JSIL_Logic_Normalise.extend_typing_env_using_assertion_info pi gamma;
		print_debug (Printf.sprintf "substitutions immediately before sat check.\nSubst:\n%s\nPat_Subst:\n%s"
			(JSIL_Memory_Print.string_of_substitution subst)
			(JSIL_Memory_Print.string_of_substitution new_pat_subst));
		print_debug (Printf.sprintf "About to check if the following is SATISFIABLE:\n%s\nGiven the GAMMA:\n%s"
			(JSIL_Print.str_of_assertion_list pi)
			(	JSIL_Memory_Print.string_of_gamma gamma));
		let sat_check = Pure_Entailment.check_satisfiability pi gamma in
		(* Printf.printf "GAMMA_OLD - STEP 5:\n%s\n" (JSIL_Memory_Print.string_of_gamma gamma_old); *)
	    sat_check, pi', gamma_0', new_pat_subst in


	(* STEP 6 - Finally unfold: Sigma_0, Sigma_1, subst, pat_subst, pi, gamma                              *)
	(* subst(Sigma_0) + pat_subst(Sigma_1) + (_, _, pi, gamma, _)                                          *)
	let step_6 subst pat_subst new_pfs new_gamma =
		print_debug ("Entering step 6 of safe_merge_symb_states");
		let symb_state = symb_state_substitution symb_state subst true in
		let unfolded_symb_state = merge_symb_states symb_state pat_symb_state pat_subst in
		merge_pfs (get_pf unfolded_symb_state) (DynArray.of_list new_pfs);
		extend_gamma (get_gamma unfolded_symb_state) new_gamma;
		JSIL_Logic_Normalise.extend_typing_env_using_assertion_info new_pfs (get_gamma unfolded_symb_state);
		print_debug ("Finished step 6 of safe_merge_symb_states");
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
							) else  ( print_debug (Printf.sprintf "Failed unfolding in step 5") ; None)
					) else  ( print_debug (Printf.sprintf "Failed unfolding in step 3");    None)
			) else ( print_debug (Printf.sprintf "Failed unfolding in step 2");  None)
	| None -> print_debug (Printf.sprintf "Failed unfolding in step 1");  None



let unify_symb_state_against_invariant symb_state inv_symb_state lvars = 
	print_debug (Printf.sprintf "unify_symb_state_against_invariant.\nSymb_state:\n%s.\INVARIANT symb_state:\n%s" 
		(JSIL_Memory_Print.string_of_shallow_symb_state symb_state) 
		(JSIL_Memory_Print.string_of_shallow_symb_state inv_symb_state)); 	
	let unifier = unify_symb_states lvars inv_symb_state symb_state in
	match unifier with
	| Some (true, quotient_heap, quotient_preds, subst, pf_discharges, _) ->
		extend_symb_state_with_pfs symb_state (DynArray.of_list pf_discharges);
		let symb_state = symb_state_replace_heap symb_state quotient_heap in
		let symb_state = symb_state_replace_preds symb_state quotient_preds in
		let new_symb_state = merge_symb_states symb_state inv_symb_state subst in
		let subst_pfs = assertions_of_substitution subst in 
		extend_symb_state_with_pfs symb_state (DynArray.of_list subst_pfs); 
		let new_symb_state = Symbolic_State_Basics.simplify_symbolic_state symb_state in 
		Some new_symb_state 
	| _ -> None  




