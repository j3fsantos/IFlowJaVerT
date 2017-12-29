open JSIL_Syntax
open Symbolic_State


let make_counter (n : int) (depth : int) : (unit -> int array) * (bool -> bool) = 
	let cur_digit  = ref 0 in 
	let arr        = Array.make n 0 in 

	let rec inc_arr (carrier_increment : bool) : bool = 
		let digit_val = arr.(!cur_digit) in 
		if (digit_val < depth) 
			then ( 
				arr.(!cur_digit) <- (digit_val + 1); 
				if (carrier_increment) then (
					for i = 0 to (!cur_digit - 1) do 
						arr.(i) <- 0 
					done; 
					cur_digit := 0; 
					true
				) else true 
			) else (
				if (!cur_digit < (n-1)) 
					then ( 
						cur_digit := !cur_digit + 1;  
						inc_arr true
					) else false 
			) in  

	let get_arr () : int array =  arr in 

	get_arr, inc_arr


let filter_symb_state_with_domain_info (ss : symbolic_state) : bool = 
	let heap, store, pfs, gamma, preds = ss in 

	let heap_list = heap_to_list heap in 
	
	let asrts_per_object = 
		List.map (fun (_, (fv_list, _)) ->  
			let fields = List.map (fun (f_name, f_val) -> f_name) fv_list in 
			Normaliser.make_all_different_assertion_from_fvlist fields 
		) heap_list in 

	let extended_pfs = (List.concat asrts_per_object) @ (pfs_to_list pfs) in 

	if (Pure_Entailment.check_satisfiability extended_pfs gamma) then (
		Printf.printf "EXTENDED PFS ARE OK\n";
		true
	) else (
		Printf.printf "EXTENDED PFS ARE !!!WRONG!!!\n"; 
		false
	)


let filter_pre_post_with_domain_info (pre : symbolic_state) (post : symbolic_state) : bool = 
	let heap_pre,  store_pre,  pfs_pre,  gamma_pre,  preds_pre  = pre in 
	let heap_post, store_post, pfs_post, gamma_post, preds_post = post in 

	let gamma = merge_gammas_copy gamma_pre gamma_post in 

	let pfs_post_lst = pfs_to_list pfs_post in 

	let has_sets = (List.length (List.concat (List.map JSIL_Logic_Utils.get_asrt_sets pfs_post_lst))) > 0 in 
	if (not has_sets) then true else (

		let heap_list = (heap_to_list heap_pre) @ (heap_to_list heap_post) in
		let asrts_per_object = 
			List.map (fun (_, (fv_list, _)) ->  
				let fields = List.map (fun (f_name, f_val) -> f_name) fv_list in 
				Normaliser.make_all_different_assertion_from_fvlist fields 
			) heap_list in 

		let extended_pfs = (List.concat asrts_per_object) @ (pfs_to_list pfs_pre) @ (pfs_to_list pfs_post) in 

		if (Pure_Entailment.check_satisfiability extended_pfs gamma) then (
			Printf.printf "EXTENDED PFS PRE-POST ARE OK for %s\n"
				(JSIL_Print.str_of_assertion_list extended_pfs);
			true
		) else (
			Printf.printf "EXTENDED PFS PRE-POST ARE !!!WRONG!!! for %s\n"
				(JSIL_Print.str_of_assertion_list extended_pfs); 
			false
		))


let clean_typing_environment (ss : symbolic_state) : symbolic_state = 
	let gamma           = ss_gamma ss in
	let gamma_vars      = gamma_lvars gamma in 
	let other_ss_vars   = ss_lvars_no_gamma ss in 
	let only_gamma_vars = 
		SS.filter (fun elem -> not (SS.mem elem other_ss_vars)) gamma_vars in 
	SS.iter (fun elem -> update_gamma gamma elem None) only_gamma_vars; 
	ss 


let process_prepost 
		(ss_pre    : symbolic_state) 
		(ss_post   : symbolic_state) 
		(spec_vars : SS.t) : symbolic_state list = 

	let pfs_pre   = (ss_pfs ss_pre) in 
	let pfs_post  = (ss_pfs ss_post) in 
	let pfs_list  = (pfs_to_list pfs_pre) @ (pfs_to_list pfs_post) in 
	let pfs       = (pfs_of_list pfs_list) in


	Printf.printf "process_prepost with:\n%s\n%s\n"
		(Symbolic_State_Print.string_of_symb_state ss_pre) (Symbolic_State_Print.string_of_symb_state ss_post);

	if (Pure_Entailment.check_satisfiability pfs_list (ss_gamma ss_post)) then (
		Printf.printf "COMPATIBLE PRE and POST - no work needed\n";
		let ss_post      = ss_replace_pfs ss_post pfs in 
		let ss_post      = Simplifications.simplify_ss ss_post (Some (Some spec_vars)) in
		let ss_post      = clean_typing_environment ss_post in 

		if (filter_pre_post_with_domain_info ss_pre ss_post) then [ ss_post ] else []  	
	) else (
		Printf.printf "SPEC with inconsistent alocs was found.\npre_pfs:\n%s\npost_pfs:\n%s\n"
			(Symbolic_State_Print.string_of_pfs pfs_pre) (Symbolic_State_Print.string_of_pfs pfs_post); 

		let alocs_post         = ss_alocs ss_post in 
		let alocs_pre          = ss_alocs ss_pre  in 
		let new_alocs_post     = SS.filter (fun aloc -> (not (SS.mem aloc alocs_pre))) alocs_post in 
		let constrained_alocs  = pfs_alocs pfs in 
		let relevant_new_alocs = SS.inter constrained_alocs new_alocs_post in 

		Printf.printf "relevant_new_alocs: %s\n" 
			(String.concat ", " (SS.elements relevant_new_alocs)); 

		Printf.printf "pfs_list: %s\n" (Symbolic_State_Print.string_of_pfs (pfs_of_list pfs_list));

		let aloc_subst = init_substitution [] in 
		SS.iter (fun aloc -> 
			match Normaliser.is_overlapping_aloc pfs_list aloc with 
			| None       -> () 
			| Some aloc' -> Hashtbl.replace aloc_subst aloc (ALoc aloc'); ()
		) relevant_new_alocs; 
		
		Printf.printf "post_substitution: %s\n" (JSIL_Print.string_of_substitution aloc_subst); 

		let new_pfs_post = pfs_substitution aloc_subst true (ss_pfs ss_post) in 
		let new_pfs_post = pfs_of_list ((pfs_to_list pfs_pre) @ (pfs_to_list new_pfs_post)) in 
		let ss_post      = ss_replace_pfs ss_post new_pfs_post in  
		let ss_post      = ss_substitution aloc_subst true ss_post in 
		let ss_post      = Simplifications.simplify_ss ss_post (Some (Some spec_vars)) in

		Printf.printf "new post pfs: %s\n"
			(Symbolic_State_Print.string_of_pfs new_pfs_post); 

		if (Pure_Entailment.check_satisfiability (pfs_to_list new_pfs_post) (ss_gamma ss_post)) then (
			Printf.printf "COMPATIBLE PRE and POST - with some work\n";
			let ss_post = clean_typing_environment ss_post in 
			if (filter_pre_post_with_domain_info ss_pre ss_post) then [ ss_post ] else [] 
		) else (
			Printf.printf "INCOMPATIBLE PRE and POST\n";
			[]
		)
	)



let unfold_symb_state_with_counter 

			(symb_state : symbolic_state) 
			(counter    : int array)
			(pred_tbl   : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t)
			(spec_vars  : SS.t) : symbolic_state list = 

	let heap, store, pfs, gamma, preds = symb_state in	 
	let new_preds                      = preds_init () in 
	let counter                        = Array.to_list counter in 
	let preds_list                     = DynArray.to_list preds in 
	let symb_state'                    = heap, store, pfs, gamma, new_preds in 
	
	Printf.printf "inside unfold_symb_state_with_counter with counter: %s and with symb_state:\n%s\n"
	 	("[" ^ (String.concat ", " (List.map string_of_int counter)) ^ "]")
		(Symbolic_State_Print.string_of_symb_state symb_state); 


	if ((List.length counter) <> (List.length preds_list)) then (
		raise (Failure "DEATH. unfold_symb_state_with_counter")
	) else (

		let rec loop 
				(to_do_list                 : (((int * string * (jsil_logic_expr list)) list) * symbolic_state) list)
				(fully_unfolded_symb_states : symbolic_state list) : symbolic_state list =
			(match to_do_list with 
			| []  -> 
				Printf.printf "Done looping in unfold_symb_state_with_counter\n"; 
				fully_unfolded_symb_states  
			
			| ([], symb_state) :: rest_todo_lst -> 
				Printf.printf "FULLY unfolded one symb_state with counter iupi!. Result:\n%s\n"
					(Symbolic_State_Print.string_of_symb_state symb_state); 

				loop rest_todo_lst (symb_state :: fully_unfolded_symb_states)

			| (((counter, p_name, args) :: rest_preds), symb_state) :: rest_todo_lst -> 
				try (
					print_debug (Printf.sprintf "In the unfolding loop with the predicate %s with counter %d and state\n%s\n"
						p_name counter (Symbolic_State_Print.string_of_symb_state symb_state)); 

					let unfolded_p_name  = Normaliser.get_new_pred_name p_name counter in 
					let n_pred           = Hashtbl.find pred_tbl unfolded_p_name in 
					let caller_store     = store_init n_pred.n_pred_params args in 
					let subst_e          = init_substitution3 [] in 
					let pat_subst        = init_substitution3 [] in

					let spec_vars_aux    = SS.union (ss_lvars symb_state) spec_vars in

					let new_symb_states : (symbolic_state * substitution) option list = 
						List.map 
							(fun (_, pred_symb_state, _) -> 
								(Spatial_Entailment.unfold_predicate_definition caller_store subst_e 
									pat_subst SS.empty spec_vars_aux pred_symb_state symb_state) 
							) n_pred.n_pred_definitions in 

					let new_symb_states = List.filter 
						(fun sso -> match sso with Some ss -> true | _ -> false) new_symb_states in 

					let new_symb_states =  List.map Option.get new_symb_states in 

					Printf.sprintf "DONE one iteration of the unfoding loop. Got the states\n%s\n"
						(String.concat ", " 
							(List.mapi 
								(fun i (ss, _) -> 
									Printf.sprintf "Symb State %d:\n%s\n"
										i (Symbolic_State_Print.string_of_symb_state ss))
								new_symb_states)); 

					(if ((List.length new_symb_states) = 0) then 
						Printf.printf "the unfolding of %s did NOT produce results!!\n"
							(unfolded_p_name ^ "(" ^ (String.concat ", " (List.map JSIL_Print.string_of_logic_expression args)) ^ ")"));

					(* If there are set operations in the pure formulae, we need to be careful! 
					   In particular, the symbolic heap entails that, for each object, all its properties 
					   are different from each other *)
					let new_symb_states = 
						List.filter 
							(fun (ss, _) -> 
								let pfs      = (pfs_to_list (ss_pfs ss)) in 
								let has_sets = (List.length (List.concat (List.map JSIL_Logic_Utils.get_asrt_sets pfs))) > 0 in 
								if (not has_sets) then true else (
									filter_symb_state_with_domain_info ss	
								)
							) new_symb_states in 

					let new_todo_list = 
						List.map (fun (ss, subst) -> 
							let ss_rest_preds = 
								List.map (fun (counter, pname, args) ->
									let new_args = List.map (JSIL_Logic_Utils.lexpr_substitution subst true) args in  
									counter, pname, new_args) rest_preds in 
							ss_rest_preds, ss) new_symb_states in 
				
					loop (new_todo_list @ rest_todo_lst) fully_unfolded_symb_states

				) with Not_found -> raise (Failure "DEATH. unfold_symb_state_with_counter")) in 

		let original_todo_list = [ (List.map2 (fun i (p_name, args) -> (i, p_name, args)) counter preds_list), symb_state' ] in 

		loop original_todo_list []
	)


let unfold_symb_state 
		(symb_state : symbolic_state)
		(pred_set   : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t)
		(depth      : int) 
		(spec_vars  : SS.t) : symbolic_state list = 
	
	let preds      = ss_preds symb_state in	 

	Printf.printf "inside unfold_symb_state with symb_state:\n%s\n"
		(Symbolic_State_Print.string_of_symb_state symb_state); 

	if ((DynArray.length preds) = 0)
		then [ symb_state ]  
		else (
			let get_counter, inc_counter = make_counter (DynArray.length preds) depth in 	
			
			let rec loop (counter : int array) (unfolded_states : symbolic_state list) = 
				Printf.printf "Looping in unfold_symb_state with counter: %s\n"
					("[" ^ (String.concat ", " (List.map string_of_int (Array.to_list counter))) ^ "]"); 

				let new_unfolded_symb_states = unfold_symb_state_with_counter symb_state counter pred_set spec_vars in 
				(if ((List.length new_unfolded_symb_states) = 0) 
					then Printf.printf "the unfold_symb_state_with_counter output was EMPTY\n"); 
				if (inc_counter false) then (
					loop (get_counter ()) (new_unfolded_symb_states @ unfolded_states)
				) else (
					Printf.printf "Done looping in unfold_symb_state\n";
					new_unfolded_symb_states @ unfolded_states 
				) in 

			loop (get_counter ()) [ ]
		)


let unfold_spec
		(s_name    : string)
		(s_params  : string list)
		(s_spec    : jsil_n_single_spec)
		(preds     : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t) 
		(depth     : int)
			: Symbolic_State.jsil_n_single_spec list = 

	Printf.printf "Processing an s-spec of %s for depth %d\n" s_name depth; 

	let process_pre_posts 
			(pre       : symbolic_state)
			(posts     : symbolic_state list) 
			(subst     : substitution)
			(ret_flag  : jsil_return_flag) : jsil_n_single_spec = 	

		Printf.printf "process_pre_posts. symb_state PRE:\n%s\n"
			(Symbolic_State_Print.string_of_symb_state pre);


		print_debug (Printf.sprintf "process_pre_posts. symb_state PRE:\n%s\n"
			(Symbolic_State_Print.string_of_symb_state pre));

		(* STEP 1 - simplify the pre-condition and apply resulting 
		   substitution to posts                                             *)
		let pre', pre_subst = Simplifications.simplify_ss_with_subst pre None in
		let pre'            = clean_typing_environment pre' in 
		let spec_vars       = ss_lvars pre' in
		let posts           = List.map (ss_substitution pre_subst true) posts in  

		Printf.printf "pre_subst:\n%s\n" (JSIL_Print.string_of_substitution pre_subst); 

		Printf.printf "process_pre_posts in the middle of step 1.\n POSTS:\n"; 
		List.iteri (fun i ss -> 
			Printf.printf  "POST %d:\n%s\n" i (Symbolic_State_Print.string_of_symb_state ss)
		) posts; 

		Printf.printf "process_pre_posts. symb_state PRE' and subst:\n%s\n%s\n"
			(Symbolic_State_Print.string_of_symb_state pre')
			(JSIL_Print.string_of_substitution pre_subst);


		(* STEP 2 - the new spec vars and the new subst *)
		let spec_vars_lst' = SS.elements spec_vars in 
		let svars_subst    = init_substitution3 [] in 
		let gamma_pre      = ss_gamma pre' in 
		List.iter (fun lvar -> 
			if (not (is_spec_var_name lvar)) then (
				Printf.printf "RENAMING a SPEC VAR!!!!!!!!!\n"; 
				let new_lvar_name = 
					(match gamma_get_type gamma_pre lvar with 
					| None        -> fresh_spec_var ()
					| Some j_type -> fresh_spec_var_with_type j_type) in 
				Hashtbl.replace svars_subst lvar (LVar new_lvar_name)
			)
		) spec_vars_lst'; 
		let spec_vars_lst = 
			List.map 
				(fun x -> 
					if (Hashtbl.mem svars_subst x) 
						then (
							match Hashtbl.find svars_subst x with 
							| LVar new_x -> new_x 
							| _ -> raise (Failure "DEATH. unfold_spec")
						) else x)
				spec_vars_lst' in 
		let spec_vars = SS.of_list spec_vars_lst in 
		let pre' = ss_substitution svars_subst true pre' in  

		Printf.printf "process_pre_posts. symb_state PRE' and svars_subst:\n%s\n%s\n"
			(Symbolic_State_Print.string_of_symb_state pre')
			(JSIL_Print.string_of_substitution svars_subst);

		(* STEP 3 - simplify and process the post conditions *)
		let posts   = List.map (ss_substitution svars_subst true) posts in 

		Printf.printf "process_pre_posts. Posts to consider:\n%s\n" 
			(String.concat "\n"  
				(List.mapi  
					(fun i post -> 
						Printf.sprintf "POST %d:\n%s\n" 
							i (Symbolic_State_Print.string_of_symb_state post))
					posts)); 

		let post'   = List.concat (List.map (fun post -> process_prepost pre' post spec_vars) posts) in 

		{
			n_pre              = pre'; 
			n_post             = post'; 
			n_ret_flag         = ret_flag;  
			n_lvars            = spec_vars; 
			n_subst            = subst; 
			n_unification_plan = (Normaliser.create_unification_plan pre' SS.empty)
		} in 

	Printf.printf "Unfolding the PRE-conditions\n"; 
	let new_pres  = unfold_symb_state s_spec.n_pre preds depth s_spec.n_lvars in 
	Printf.printf "Unfolding the POST-conditions with spec vars: %s\n"
		(String.concat ", " (SS.elements s_spec.n_lvars));
	let new_posts = List.concat (List.map (fun ss -> unfold_symb_state ss preds depth s_spec.n_lvars) s_spec.n_post) in
	let pre_posts = List.map (fun ss -> (ss, new_posts)) new_pres in 
	Printf.printf "Connecting PRES and POSTS\n"; 
	List.map (fun (pre, posts) -> process_pre_posts pre posts s_spec.n_subst s_spec.n_ret_flag) pre_posts 


let unfold_pred_in_specs 
		(preds       : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t)
		(specs       : Symbolic_State.specification_table) 
		(depth       : int)
			: Symbolic_State.specification_table = 
	let new_specs = Hashtbl.create big_tbl_size in 
	Hashtbl.iter 
		(fun s_name spec -> 
			Printf.printf "going to unfold the spec: %s\n" s_name; 
			let s_params : string list = spec.n_spec_params in 
			let s_specs : jsil_n_single_spec list = 
				List.concat (List.map (fun s_spec -> unfold_spec s_name s_params s_spec preds depth) spec.n_proc_specs) in 
			let new_spec : Symbolic_State.jsil_n_spec = 
				{
					n_spec_name   = s_name; 
					n_spec_params = s_params; 
					n_proc_specs  = s_specs
				} in 
			Hashtbl.replace new_specs s_name new_spec) specs; 

	new_specs  


let simplify_preds 
		(preds : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t) : 
			(string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t = 

	let new_pred_tbl : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t =  
		Hashtbl.create (Hashtbl.length preds) in 

	Hashtbl.iter 
		(fun pred_name pred ->
			let new_defs = List.map 
				(fun (os, def, up) ->
					let new_def = Simplifications.simplify_ss def None in 
					(os, new_def, up)	
				) pred.n_pred_definitions in 
			let new_pred : n_jsil_logic_predicate = { pred with n_pred_definitions = new_defs } in 
			Hashtbl.replace new_pred_tbl pred_name new_pred
		) 
		preds; 

	new_pred_tbl



let generate_test 
		(i           : int)
		(spec_name   : string)
		(spec_params : string list)
		(spec        : jsil_n_single_spec) : jsil_procedure list =
	[ ] 


let make_symbolic_tests 
		(procs : (string, jsil_procedure) Hashtbl.t)
		(specs : Symbolic_State.specification_table)  
		(preds : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t)
		(depth : int) : unit = 

	Hashtbl.iter
		(fun s_name spec -> 
			let s_params : string list = spec.n_spec_params in 
			let new_procs : jsil_procedure list = List.concat (List.mapi (fun i s_spec -> generate_test i s_name s_params s_spec) spec.n_proc_specs) in 
			List.iter (fun (new_proc : jsil_procedure) -> 
				Hashtbl.replace procs new_proc.proc_name new_proc
			) new_procs)
		specs 


(*
let single_spec_to_test 
		(s_name    : string)
		(s_params  : string list)
		(s_spec    : jsil_n_single_spec)

*)

	