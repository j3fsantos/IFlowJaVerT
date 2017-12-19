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
					true
				) else true 
			) else (
				if (!cur_digit < n) 
					then ( 
						cur_digit := !cur_digit + 1;  
						inc_arr true
					) else false 
			) in  

	let get_arr () : int array =  arr in 

	get_arr, inc_arr



let process_prepost 
		(ss_pre    : symbolic_state) 
		(ss_post   : symbolic_state) 
		(spec_vars : SS.t) : symbolic_state list = 
	
	let pfs_pre  = (ss_pfs ss_pre) in 
	let pfs_post = (ss_pfs ss_post) in 
	let pfs_list = (pfs_to_list pfs_pre) @ (pfs_to_list pfs_post) in 
	let pfs      = (pfs_of_list pfs_list) in 

	let ss_post  = ss_replace_pfs ss_post pfs in  
	let ss_post  = Simplifications.simplify_ss ss_post (Some (Some spec_vars)) in

	if (Pure_Entailment.check_satisfiability (pfs_to_list (ss_pfs ss_post)) (ss_gamma ss_post)) then (
		[ ss_post ] 	
	) else (
		print_normal (Printf.sprintf "SPEC with inconsistent alocs was found.\npre_pfs:\n%s\npost_pfs:\n%s\n"
			(Symbolic_State_Print.string_of_pfs pfs_pre) (Symbolic_State_Print.string_of_pfs pfs_post)
		); 

		let alocs_post         = ss_alocs ss_post in 
		let alocs_pre          = ss_alocs ss_pre  in 
		let new_alocs_post     = SS.filter (fun aloc -> (not (SS.mem aloc alocs_pre))) alocs_post in 
		let constrained_alocs  = pfs_alocs pfs in 
		let relevant_new_alocs = SS.inter constrained_alocs new_alocs_post in 

		(* print_debug (Printf.sprintf "relevant_new_alocs: %s\n" 
			(String.concat ", " (SS.elements relevant_new_alocs))); *)

		let aloc_subst = init_substitution [] in 
		SS.iter (fun aloc -> 
			match Normaliser.is_overlapping_aloc pfs_list aloc with 
			| None       -> () 
			| Some aloc' -> Hashtbl.replace aloc_subst aloc (ALoc aloc'); ()
		) relevant_new_alocs; 
		
		let new_pfs_post = pfs_substitution aloc_subst true (ss_pfs ss_post) in 

		if (Pure_Entailment.check_satisfiability (pfs_to_list new_pfs_post) (ss_gamma ss_post)) then (
			[ ss_substitution aloc_subst true ss_post ]
		) else (
			[]
		)
	)



let unfold_symb_state_with_counter 

			(symb_state : symbolic_state) 
			(counter    : int array)
			(preds      : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t)
			(spec_vars  : SS.t) : symbolic_state list = 

	let heap, store, pfs, gamma, preds = symb_state in	 
	let new_preds                      = DynArray.create () in 
	let counter                        = Array.to_list counter in 
	let preds_list                     = DynArray.to_list preds in 
	[] 

	(* if ((List.length counter) <> (List.lenght preds_list)) then (
		raise (Failure "DEATH. unfold_symb_state_with_counter")
	) else (
		 let new_states = 
			List.map2 (fun i (p_name, args) ->
				try 
					let unfolded_p_name = get_new_pred_name p_name i in 
					let n_pred          = Hashtbl.find preds unfolded_p_name in 
					let caller_store    = store_init n_pred.n_pred_params args in 
					let subst_e         = init_substitution3 [] in 
					let pat_subst       = init_substitution3 [] in

					let new_symb_states = List.map (fun _ pred_symb_state _ -> 
						Spatial_Entailment.unfold_predicate_definition caller_store subst_e pat_subst SS.empty spec_vars pred_symb_state symb_state in 
					) n_pred.n_pred_definitions
				with Not_found -> raise (Failure "DEATH. unfold_symb_state_with_counter") 
			) counter preds_list in 
		new_states 
		[]
	) *) 


let unfold_symb_state 
		(symb_state : symbolic_state)
		(preds      : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t)
		(depth      : int) : symbolic_state list = 
	
	let heap, store, pfs, gamma, preds = symb_state in	 

	if ((DynArray.length preds) = 0)
		then [ symb_state ]  
		else (
			let get_counter, inc_counter = make_counter (DynArray.length preds) depth in 
			let continue                 = ref true in 
			let unfolded_symb_states     = ref [] in  
			
			(* 
			while !continue do 
				let counter = get_counter () in 
  				let new_unfolded_symb_states = unfold_symb_state_with_counter symb_state counter preds in 
  				unfolded_symb_states := new_unfolded_symb_states @ (!unfolded_symb_states); 
  				continue := inc_counter false
			done; *)

			!unfolded_symb_states
		)


let unfold_spec
		(s_name    : string)
		(s_params  : string list)
		(s_spec    : jsil_n_single_spec)
		(preds     : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t) 
		(depth     : int)
			: Symbolic_State.jsil_n_single_spec list = 

	let process_pre_posts 
			(pre       : symbolic_state)
			(posts     : symbolic_state list) 
			(spec_vars : SS.t) 
			(subst     : substitution)
			(ret_flag  : jsil_return_flag) : jsil_n_single_spec = 	

		(* STEP 1 - determine the mappings of spec-vars in the precondition  *)
		let subst'  = JSIL_Logic_Utils.filter_substitution_set spec_vars subst in

		(* STEP 2 - after unfolding, some spec vars become locations and this 
		   needs to be reflected in the post-condition                       *)
		Symbolic_Interpreter.extend_spec_vars_subst spec_vars (ss_pfs pre) subst';

		(* STEP 3 - simplify the pre-condition                               *)
		let pre'    = Simplifications.simplify_ss pre (Some (Some spec_vars)) in

		(* STEP 4 - simplify and process the post conditions                 *)
		let post'   = List.concat (List.map (fun post -> process_prepost pre' post spec_vars) posts) in 

		{
			n_pre              = pre'; 
			n_post             = post'; 
			n_ret_flag         = ret_flag;  
			n_lvars            = spec_vars; 
			n_subst            = subst; 
			n_unification_plan = (Normaliser.create_unification_plan pre' SS.empty)
		} in 

	let new_pres  = unfold_symb_state s_spec.n_pre preds depth in 
	let new_posts = List.concat (List.map (fun ss -> unfold_symb_state ss preds depth) s_spec.n_post) in
	let pre_posts = List.map (fun ss -> (ss, new_posts)) new_pres in 
	List.map (fun (pre, posts) -> process_pre_posts pre posts s_spec.n_lvars s_spec.n_subst s_spec.n_ret_flag) pre_posts 


let unfold_pred_in_specs 
		(preds       : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t)
		(specs       : Symbolic_State.specification_table) 
		(depth       : int)
			: Symbolic_State.specification_table = 
	let new_specs = Hashtbl.create big_tbl_size in 
	Hashtbl.iter 
		(fun s_name spec -> 
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


	