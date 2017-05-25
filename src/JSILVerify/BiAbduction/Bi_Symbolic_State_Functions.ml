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

exception Command_unsupported of unit
exception Recursive_call_graph of unit
exception Procedure_does_not_exist of unit

let get_call_hash_tbl program =
	let procs_tbl = Hashtbl.create small_tbl_size in
	Hashtbl.iter (fun proc_name proc -> 
						try 
							let procs_called = (
								Array.fold_left (
									fun ac (_, cmd) -> 
										(match cmd with 
										| SCall (x, e, e_args, j) -> 
											(match e with 
											| (Literal (String name)) -> 
												name :: ac
											| _ -> print_debug "Call Graph: While creating the call graph found a non-string procedure expression"; 
												   ac)
										| SBasic bcmd -> 
											(match bcmd with 
											| SGetFields (_, _) ->
												raise (Command_unsupported ())
											| SArguments var -> 
												raise (Command_unsupported ())
											| _ -> ac)
										| _ -> ac)
									) [] proc.proc_body) in
							Hashtbl.add procs_tbl proc_name procs_called
						with Command_unsupported () -> ()
				 ) program;
	procs_tbl

let create_call_graph procs_to_verify procs_tbl =
	(* Could check for main *)

	(* Contains the procedures not called from any other procedures *)
	let roots = Hashtbl.create small_tbl_size in
	(* Spec which we should include and not infer as they 
	   include functions that don't have a given spec for example defaultValue *)
	let include_specs =  DynArray.create () in
	(* List of all the functions that include recursion *)
	let recursive_functions =  DynArray.create () in

	let rec detect_cycles (proc_name : string) (visited : SS.t ) : (string list) =
		if SS.mem proc_name visited then 
			[] (*raise (Recursive_call_graph ());*)
		else 
			(let procs_called = 
				(try
					Hashtbl.find procs_tbl proc_name
				with Not_found -> 
					raise (Procedure_does_not_exist ())) in

			let visited = SS.add proc_name visited in
			List.fold_left 
				(fun ac cproc_name -> 
					try 
						let cproc_list = detect_cycles cproc_name visited in
						cproc_list @ ac
					with Procedure_does_not_exist () -> 
						DynArray.add include_specs proc_name;
						if (List.mem proc_name procs_to_verify) then
							print_debug (Printf.sprintf "%s CALLS %s, which does not exist." proc_name cproc_name);
						[]
				) [proc_name] procs_called)
	in

	Hashtbl.iter (fun proc_name _ -> 
							(try 
								let ordered_procs = detect_cycles proc_name SS.empty in
								Hashtbl.add roots proc_name ordered_procs;
							with _ -> 
								(*DynArray.add recursive_functions proc_name*) ())
				 ) procs_tbl;
	(roots, include_specs, recursive_functions)

let construct_call_graph procs_to_verify program =
	let proc_tbl = get_call_hash_tbl program in
	let roots, include_specs, recursive_functions = create_call_graph procs_to_verify proc_tbl in
	let include_specs = DynArray.to_list include_specs in
	let reverse_order = Hashtbl.fold (fun proc_name procs ac -> 
								List.fold_left (fun ac proc -> 
										if (List.mem proc ac or List.mem proc include_specs) then
											ac 
										else 
											proc :: ac
					 			) ac procs
				 ) roots [] in
	print_endline "VERIFY ORDER:";
	List.iter print_endline (List.rev reverse_order);
	((List.rev reverse_order), recursive_functions,include_specs)

let internal_functions_preprocessing procs_to_verify program spec_tbl =
	let (procs_to_verify,recursive_functions,include_specs) = construct_call_graph procs_to_verify program in
	let new_spec_tbl = Hashtbl.create small_tbl_size in
	Hashtbl.iter (fun proc spec -> 
						if (List.mem proc include_specs) then
							Hashtbl.add new_spec_tbl proc spec
		) spec_tbl;
	(procs_to_verify, new_spec_tbl, recursive_functions)

let string_new_specs program results spec_table procs_to_verify = 
	(* Imports line *)
	let prog_str = (match program.imports with
	| [] -> ""
	| hd :: tl -> "import " ^ (String.concat ", " (hd :: tl)) ^ ";\n")
	^
	(* Predicates *)
	(Hashtbl.fold
		(fun _ pred acc_str -> acc_str ^ "\n" ^ (JSIL_Print.string_of_predicate pred))
		program.predicates
		"")
	^
	(* Onlyspecs *)
	(Hashtbl.fold
		(fun _ spec acc_str -> acc_str ^ "\n" ^ "only " ^ (JSIL_Print.string_of_jsil_spec spec))
		program.onlyspecs
		"") 
	^ 
	(Hashtbl.fold (fun name spec acc_str -> 
						if (not (List.mem name procs_to_verify)) then 
							(try 
								let proc = Hashtbl.find program.procedures name in
								acc_str ^ "\n" ^ (JSIL_Print.string_of_ext_procedure proc)
							with Not_found -> 
								acc_str)
						else 
							acc_str
				 ) spec_table "") in

	let proc_specs = Hashtbl.create small_tbl_size in
	List.iter (fun (proc_name, i, spec, success, msg, _) -> 
			if (success) then
				(let spec_str = string_of_single_spec_table_assertion spec in
				try 
					let proc_spec_str = Hashtbl.find proc_specs proc_name in 
					Hashtbl.replace proc_specs proc_name (proc_spec_str ^ ";\n\n" ^ spec_str)
				with Not_found -> 
					Hashtbl.add proc_specs proc_name spec_str)
		) results;

	let str = Hashtbl.fold
		(fun proc_name (proc:jsil_ext_procedure) acc_str -> 
			try 
				let spec_str = Hashtbl.find proc_specs proc_name in
				let spec_str = Printf.sprintf "spec %s (%s)\n %s\n" proc_name (String.concat ", " proc.lproc_params) spec_str in
				let proc_str = JSIL_Print.string_of_ext_procedure_body proc in
				acc_str ^ "\n" ^ spec_str ^ "\n" ^ proc_str
			with Not_found ->
				acc_str
		)
		program.procedures
		"" in
	print_endline (prog_str ^ str)

let process_bi_results procs_to_verify procs_list new_spec_tbl bi_res norm_res rec_funcs verbose = 
	let results_str = "BI-ABDUCTIVE RESULTS: \n\n" in

	(* Failed to generate specification string *)
	let bi_fail_str, gen_fail_num, procs_to_verify_num = 	
		List.fold_left (
	 		fun (ac,count, suc_count) (proc_name, i, _, success, msg, _) -> 
	 			let ver_spec = List.mem proc_name procs_to_verify in
	 			(if ver_spec then
	 				(if (not success) then
		 				(let proc_str = Printf.sprintf "%s %d" proc_name i in
		 				if (verbose) then
							(let failed_msg_str = (match msg with
							| None ->  "\n" ^ proc_str ^ "\n----------\n Failed without a message. \n\n"
							| Some msg -> "\n" ^ proc_str ^ "\n----------\n " ^ msg ^ "\n\n") in 
							(failed_msg_str ^ ac,count+1,suc_count+1))
						else 
							(proc_str ^ "\n" ^ ac,count+1,suc_count+1))
		 			else 
		 				(ac,count,suc_count+1))
				else 
					(ac,count,suc_count))
	 	) ("",0,0) bi_res in

	let bi_fail_str = 
		(if (not ((String.length bi_fail_str) = 0)) then 
			"\n--------------\nFAILED TO GENERATE SPEC:  \n--------------\n" ^ bi_fail_str
		else 
			"") in

	(* Failed to verify specifiaction string *)
	let norm_fail_str, succ_str, verify_fail_num, verify_succ_num = 
		List.fold_left (
	 		fun (ac,succ_str, fail_count, suc_count) (proc_name, i, spec, success, msg, _) -> 
	 			(if (List.mem proc_name procs_to_verify) then 
		 			(if (not success) then
		 				(let proc_str = Printf.sprintf "%s %d" proc_name i in
		 				if (verbose) then
							(let spec_str = string_of_single_spec_table_assertion spec in
							let failed_msg_str = (match msg with
							| None ->  "\n" ^ proc_str ^ "\n----------\n" ^ spec_str ^ " \n Failed without a message. \n\n"
							| Some msg -> "\n" ^ proc_str ^ "\n----------\n" ^ spec_str ^ "\n" ^ msg ^ "\n\n") in 
							(failed_msg_str ^ ac,succ_str,fail_count+1, suc_count))
						else 
							(proc_str ^ "\n" ^ ac,succ_str, fail_count+1, suc_count))
					else 
						(if (verbose) then
							let spec_str = string_of_single_spec_table_assertion spec in
							(ac,"\n" ^ proc_name ^ "\n----------\n" ^ spec_str ^ succ_str,fail_count, suc_count+1)
						else
							(ac,proc_name ^ "\n" ^ succ_str,fail_count, suc_count+1)))
	 			else
	 			(ac,succ_str, fail_count, suc_count))
	 	) ("", "", 0,0) norm_res in

	let norm_fail_str = 
		(if (not ((String.length norm_fail_str) = 0)) then 
			"\n--------------\nFAILED TO VERIFY SPEC:  \n--------------\n" ^ norm_fail_str
		else 
			"") in

	let succ_str = 
		(if (not ((String.length succ_str) = 0)) then 
			"\n--------------\nVERIFIED SPECS:  \n--------------\n" ^ succ_str
		else 
			"") in

	let stats = 
		Printf.sprintf 
			"\n PROCEDURES TO VERIFY: %d \n FAILED TO GENERATE SPECS: %d \n TOTAL NUMBER OF SPECS GENERATED: %d \n FAILED TO VERIFY SPECS:  %d" 
			procs_to_verify_num
			gen_fail_num
			(verify_succ_num + verify_fail_num)
			verify_fail_num in

	print_endline (results_str ^ bi_fail_str ^ norm_fail_str ^ succ_str ^ stats)	