open JSIL_Syntax
open Symbolic_State_Utils

exception Command_unsupported of unit
exception Recursive_call_graph of unit
exception Procedure_does_not_exist of unit

let get_call_hash_tbl program =
	let procs_tbl = Hashtbl.create small_tbl_size in
	let num_unsupported = 
					Hashtbl.fold (fun proc_name proc ac -> 
						try 
							let procs_called, num = (
								Array.fold_left (
									fun (ac,num) (_, cmd) -> 
										(match cmd with 
										| SCall (x, e, e_args, j) -> 
											(match e with 
											| (Literal (String name)) -> 
												(name :: ac,num+1)
											| _ -> print_debug "Call Graph: While creating the call graph found a non-string procedure expression"; 
												   (ac,num+1))
										| SBasic bcmd -> 
											(match bcmd with 
											| SGetFields (_, _) ->
												raise (Command_unsupported ())
											| SArguments var -> 
												raise (Command_unsupported ())
											| _ -> (ac,num+1))
										| _ -> (ac,num+1))
									) ([],0) proc.proc_body) in
							Hashtbl.add procs_tbl proc_name procs_called;
							ac
						with Command_unsupported () -> 
							print_endline (Printf.sprintf "Calls Unsupported op: %s" proc_name);
							(ac + 1)
				 ) program 0 in
	(procs_tbl, num_unsupported)

let create_call_graph procs_to_verify procs_tbl =
	let roots = Hashtbl.create small_tbl_size in
	(* Spec which we should include and not infer as they 
	   include functions that don't have a given spec for example defaultValue *)
	let include_specs =  DynArray.create () in

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
								())
				 ) procs_tbl;
	(roots, include_specs)

let construct_call_graph procs_to_verify program =
	let proc_tbl, num_unsupported = get_call_hash_tbl program in
	let roots, include_specs = create_call_graph procs_to_verify proc_tbl in
	let include_specs = DynArray.to_list include_specs in
	let unqiue = List.sort_uniq compare include_specs in
	print_endline (Printf.sprintf "Number of procedures which call procedures that don't exist: %d" (List.length unqiue));
	List.iter print_endline unqiue;
	let reverse_order = Hashtbl.fold (fun proc_name procs ac -> 
								List.fold_left (fun ac proc -> 
										if (List.mem proc ac or List.mem proc include_specs) then
											ac 
										else 
											proc :: ac
					 			) ac procs
				 ) roots [] in
	print_endline (Printf.sprintf "Number of procedures that include unsupported operations: %d" num_unsupported);
	print_endline "Order of procedures:";
	List.iter print_endline (List.rev reverse_order);
	((List.rev reverse_order),include_specs)

let internal_functions_preprocessing procs_to_verify program spec_tbl =
	let (procs_to_verify,include_specs) = construct_call_graph procs_to_verify program in
	let new_spec_tbl = Hashtbl.create small_tbl_size in
	Hashtbl.iter (fun proc spec -> 
						if (List.mem proc include_specs) then
							Hashtbl.add new_spec_tbl proc spec
		) spec_tbl;
	(procs_to_verify, new_spec_tbl)

let string_of_non_procs program =
	(* Imports line *)
	(match program.imports with
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

let string_of_required_specs program spec_table procs_to_verify =   
	(Hashtbl.fold (fun name spec acc_str -> 
						if (not (List.mem name procs_to_verify)) then 
							(try 
								let proc = Hashtbl.find program.procedures name in
								acc_str ^ "\n" ^ (JSIL_Print.string_of_ext_procedure proc)
							with Not_found -> 
								acc_str)
						else 
							acc_str
				 ) spec_table "")

let string_of_procs_with_new_specs results program = 
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

	Hashtbl.fold
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
		""

let string_for_new_jsil_file program results spec_table procs_to_verify = 
	string_of_non_procs program
	^ 
	string_of_required_specs program spec_table procs_to_verify
	^ 
	string_of_procs_with_new_specs results program

let failures_tbl = Hashtbl.create small_tbl_size

let update_failures (proc_name : string) (msg : string) = 
	if (Hashtbl.mem failures_tbl proc_name) then 
		(let msgs = Hashtbl.find failures_tbl proc_name in
		Hashtbl.replace failures_tbl proc_name (msg :: msgs))
	else 
		Hashtbl.add failures_tbl proc_name [msg]

let string_of_failures () =
	Hashtbl.fold (
		fun proc_name msgs (ac_s, ac_c) -> 
			let msg_str =
				List.fold_left (
					fun ac msg -> 
						ac ^ "\n" ^ msg ^ "\n" 
				) "" msgs in
			(ac_s ^ "\n" ^ proc_name ^ "\n----------\n " ^ msg_str ^ "\n\n", ac_c + 1)
	) failures_tbl ("",0)


(* Verbose - Prints specs *)
let string_of_bi_results_with_stats bi_res procs_to_verify verbose = 
	List.fold_left (
	 		fun (ac,count, suc_count) (proc_name, i, _, success, msg, _) -> 
	 			let ver_spec = List.mem proc_name procs_to_verify in
	 			let proc_str = Printf.sprintf "%s %d" proc_name i in
	 			let failed_msg_str = (match msg with
							| None ->  "\n" ^ proc_str ^ "\n----------\n Failed without a message. \n\n"
							| Some msg -> "\n" ^ proc_str ^ "\n----------\n " ^ msg ^ "\n\n") in 
	 			(if ver_spec then
	 				(if (not success) then
	 					(if (verbose) then
							(failed_msg_str ^ ac,count+1,suc_count+1)
						else 
							(proc_str ^ "\n" ^ ac,count+1,suc_count+1))
		 			else 
		 				(ac,count,suc_count+1))
				else 
					(ac,count,suc_count))
	 	) ("",0,0) bi_res

(* Verbose - Prints specs *)
let string_of_results_with_stats norm_res procs_to_verify verbose = 
	List.fold_left (
	 		fun (ac,succ_str, fail_count, suc_count) (proc_name, i, spec, success, msg, _) -> 
	 			let to_be_verified = List.mem proc_name procs_to_verify in
	 			let proc_str = Printf.sprintf "%s %d" proc_name i in
	 			let spec_str = string_of_single_spec_table_assertion spec in
	 			let failed_msg_str = (match msg with
							| None ->  "\n" ^ proc_str ^ "\n----------\n" ^ spec_str ^ " \n Failed without a message. \n\n"
							| Some msg -> "\n" ^ proc_str ^ "\n----------\n" ^ spec_str ^ "\n" ^ msg ^ "\n\n") in 
	 			(if (to_be_verified) then 
		 			(if (not success) then
		 				(if (verbose) then
							(failed_msg_str ^ ac,succ_str,fail_count+1, suc_count)
						else 
							(proc_str ^ "\n" ^ ac,succ_str, fail_count+1, suc_count))
					else 
						(if (verbose) then
							(ac,"\n" ^ proc_name ^ "\n----------\n" ^ spec_str ^ succ_str,fail_count, suc_count+1)
						else
							(ac,proc_name ^ "\n" ^ succ_str,fail_count, suc_count+1)))
	 			else
	 			(ac,succ_str, fail_count, suc_count))
	 	) ("", "", 0,0) norm_res

let process_bi_results procs_to_verify procs_list new_spec_tbl bi_res norm_res verbose = 
	let results_str = "BI-ABDUCTIVE RESULTS: \n\n" in

	let failure_str, gen_fail_num = 
		string_of_failures () in

	(* Failed to generate specification string *)
	let bi_fail_str, gen_bi_fail_num, procs_to_verify_num = 
		string_of_bi_results_with_stats bi_res procs_to_verify verbose in

		(* Failed to verify specifiaction string *)
	let norm_fail_str, succ_str, verify_fail_num, verify_succ_num = 
		string_of_results_with_stats norm_res procs_to_verify verbose in

	let failure_str = 
		(if (not ((String.length failure_str) = 0)) then 
			"\n--------------\nCAUGHT FAILED TO GENERATE SPEC:  \n--------------\n" ^ failure_str
		else 
			"") in

	let bi_fail_str = 
		(if (not ((String.length bi_fail_str) = 0)) then 
			"\n--------------\nUNCAUGHT FAILED TO GENERATE SPEC:  \n--------------\n" ^ bi_fail_str
		else 
			"") in

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
			"\n PROCEDURES TO VERIFY: %d \n CAUGHT FAILED TO GENERATE SPECS: %d \n UNCAUGHT FAILED TO GENERATE SPECS: %d \n TOTAL NUMBER OF SPECS GENERATED: %d \n FAILED TO VERIFY SPECS:  %d" 
			procs_to_verify_num
			gen_fail_num
			gen_bi_fail_num
			(verify_succ_num + verify_fail_num)
			verify_fail_num in

	print_endline (results_str ^ failure_str ^ bi_fail_str ^ norm_fail_str ^ succ_str ^ stats)