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


let get_call_hash_tbl program =
	let procs_tbl = Hashtbl.create small_tbl_size in
	Hashtbl.iter (fun proc_name proc -> 
						let procs_called = (Array.fold_left (fun ac (_, cmd) -> 
												(match cmd with 
												| SCall (x, e, e_args, j) -> 
													(match e with 
													| (Literal (String name)) -> 
														name :: ac
													| _ -> print_debug "Call Graph: While creating the call graph found a non-string procedure expression"; 
														   ac)
												| _ -> ac)
											) [] proc.proc_body) in
						Hashtbl.add procs_tbl proc_name procs_called
				 ) program;
	procs_tbl

exception Recursive_call_graph of unit
exception Procedure_does_not_exist of unit

let create_call_graph procs_tbl =
	(* Could check for main *)

	(* Contains the procedures not called from any other procedures *)
	let roots = Hashtbl.create small_tbl_size in
	let partial = Hashtbl.create small_tbl_size in
	(* Spec which we should include and not infer as they 
	   include functions that don't have a given spec for example defaultValue *)
	let include_specs =  DynArray.create () in
	(* List of all the functions that include recursion *)
	let recursive_functions =  DynArray.create () in

	let rec detect_cycles (proc_name : string) (visited : SS.t ) : (string list) =
		if SS.mem proc_name visited then raise (Recursive_call_graph ());

		Hashtbl.remove roots proc_name;

		try Hashtbl.find partial proc_name
		with Not_found ->
			(let visited = SS.add proc_name visited in
			try 
				let procs_called = Hashtbl.find procs_tbl proc_name in
				
				let ordered_procs = List.fold_left (fun ac cproc_name -> 
														try 
															let cproc_list = detect_cycles cproc_name visited in
															cproc_list @ ac
														with Procedure_does_not_exist () ->
															DynArray.add include_specs proc_name; 
															ac
													) [proc_name] procs_called in
				Hashtbl.add partial proc_name ordered_procs;
				ordered_procs
			with Not_found -> 
				raise (Procedure_does_not_exist ());
			) in

	Hashtbl.iter (fun proc_name _ -> 
						try Hashtbl.find partial proc_name; () 
						with Not_found ->
							(try 
								let ordered_procs = detect_cycles proc_name SS.empty in
								Hashtbl.add partial proc_name ordered_procs;
								Hashtbl.add roots proc_name ordered_procs;
							with Recursive_call_graph () -> 
								DynArray.add recursive_functions proc_name)
				 ) procs_tbl;
	(roots, include_specs, recursive_functions)

let construct_call_graph program =
	let proc_tbl = get_call_hash_tbl program in
	let roots, include_specs, recursive_functions = create_call_graph proc_tbl in
	let include_specs = DynArray.to_list include_specs in
	let reverse_order = Hashtbl.fold (fun proc_name procs ac -> 
								List.fold_left (fun ac proc -> 
										if (List.mem proc ac or List.mem proc include_specs) then
											ac 
										else 
											proc :: ac
					 			) ac procs
				 ) roots [] in
	((List.rev reverse_order), recursive_functions)

let internal_functions_preprocessing program spec_tbl =
	let (procs_to_verify,recursive_functions) = construct_call_graph program in
	let new_spec_tbl = Hashtbl.create small_tbl_size in
	(* Simply removes specs so I don't have to, shouldn't happen 
	   with non-internal functions as it will remove partial specs *)
	Hashtbl.iter (fun spec_name spec ->	
						if (not (List.mem spec_name procs_to_verify)) then 
							Hashtbl.add new_spec_tbl spec_name spec
				 ) spec_tbl; 	
	(procs_to_verify, new_spec_tbl, recursive_functions)


let process_bi_results new_spec_tbl bi_res norm_res rec_funcs verbose = 
	(*let specs_str = Symbolic_State_Utils.string_of_n_spec_table_assertions new_spec_tbl procs_to_verify in 
	let results_str = Symbolic_State_Print.string_of_bi_symb_exe_results bi_res in
	let results_str = "Generated specifications: \n " ^ specs_str ^ "\n" ^ results_str in *)
	let generated_spec_set = SS.empty in

	let results_str = "BI-ABDUCTIVE RESULTS: \n\n" in

	(* Recursive Functions *)
	let rec_funcs_str =	DynArray.fold_left (
							fun rec_func ac -> 
								rec_func ^ "\n" ^ ac
						) "" rec_funcs in

	let rec_funcs_str = 
		(if (not ((String.length rec_funcs_str) = 0)) then 
			"\n--------------\nRECURSIVE PROCEDURES:  \n--------------\n" ^ rec_funcs_str
		else 
			"") in

	(* Failed to generate specification string *)
	let bi_fail_str, generated_spec_set = 	
		List.fold_left (
	 		fun (ac,generated_spec_set) (proc_name, _, _, success, msg, _) -> 
	 			if (not success) then
	 				(if (verbose) then
						let failed_msg_str = (match msg with
						| None ->  "\n" ^ proc_name ^ "\n----------\n Failed without a message. \n\n"
						| Some msg -> "\n" ^ proc_name ^ "\n----------\n " ^ msg ^ "\n\n") in 
						(failed_msg_str ^ ac, generated_spec_set)
					else 
						(proc_name ^ "\n" ^ ac, generated_spec_set))
				else 
					let generated_spec_set = SS.add proc_name generated_spec_set in
					(ac,generated_spec_set)
	 	) ("",generated_spec_set) bi_res in

	let bi_fail_str = 
		(if (not ((String.length bi_fail_str) = 0)) then 
			"\n--------------\nFAILED TO GENERATE SPEC:  \n--------------\n" ^ bi_fail_str
		else 
			"") in

	(* Failed to verify specifiaction string *)
	let norm_fail_str, generated_spec_set = 
		List.fold_left (
	 		fun (ac,generated_spec_set) (proc_name, _, _, success, msg, _) -> 
	 			(if (not success) then
	 				(let generated_spec_set = SS.remove proc_name generated_spec_set in
	 				if (verbose) then
						(let failed_msg_str = (match msg with
						| None ->  "\n" ^ proc_name ^ "\n----------\n Failed without a message. \n\n"
						| Some msg -> "\n" ^ proc_name ^ "\n----------\n" ^ msg ^ "\n\n") in 
						(failed_msg_str ^ ac,generated_spec_set))
					else 
						(proc_name ^ "\n" ^ ac, generated_spec_set))
				else 
					(ac,generated_spec_set))
	 	) ("",generated_spec_set) norm_res in

	let norm_fail_str = 
		(if (not ((String.length norm_fail_str) = 0)) then 
			"\n--------------\nFAILED TO VERIFY SPEC:  \n--------------\n" ^ norm_fail_str
		else 
			"") in

 	let succ_str = 	SS.fold (
 						fun proc_name ac -> 
 							if (verbose) then 
 								(try 
 									let spec = Hashtbl.find new_spec_tbl proc_name in
 									let spec_str = string_of_n_single_spec_assertion spec in
 									"\n" ^ proc_name ^ "\n----------\n" ^ spec_str ^ ac
 								with Not_found -> 
 									"\n" ^ proc_name ^ "\n----------\n Could not find the specification. Very odd." ^ ac)	
 							else
 								proc_name ^ "\n" ^ ac
 					) generated_spec_set "" in 

 	let succ_str = 
		(if (not ((String.length succ_str) = 0)) then 
			"\n--------------\nSUCCESSFUL SPEC GENERATION AND VERIFICATION \n--------------\n" ^ succ_str
		else 
			"") in

	print_endline (results_str ^ rec_funcs_str ^ bi_fail_str ^ norm_fail_str ^ succ_str)