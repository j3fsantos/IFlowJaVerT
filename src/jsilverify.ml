open JSIL_Syntax

let file = ref ""
let spec_file = ref ""
let output_folder = ref ""
let stats = ref false 
let bi_abduction = ref false
let interactive = ref false

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [
			(* file containing the program to symbolically execute *)
			"-file", Arg.String(fun f -> file := f), "file to run";
			"-o", Arg.String(fun f -> output_folder := f), "output folder";
            "-debug", Arg.Unit (fun () -> debug := true), "debug";
            
			"-specs", Arg.String (fun f -> spec_file := f), "specification file";
			(* *)
			"-js", Arg.Unit (fun () -> Symb_Interpreter.js := true; 
										JSIL_Bi_Symb_Interpreter.js := true), "js2jsil output"; 
			(* *)
			"-stats", Arg.Unit (fun () -> stats := true), "stats";
			(* Flag to use symbolic execution file with bi-abduction *)
			"-bi", Arg.Unit (fun () -> bi_abduction  := true), "bi-abduction";
			(* "-encoding", Arg.String (fun f ->
				Printf.printf "I am here.\n";
				let enc = match f with
				| "ints" -> Pure_Entailment.WithInts
				| "reals" -> Pure_Entailment.WithReals
				| "fpa" -> Pure_Entailment.WithFPA
				| _ -> raise (Failure "Unrecognised encoding.") in
				Printf.printf "%s\t" (Pure_Entailment.string_of_enc (!Pure_Entailment.encoding));
				Pure_Entailment.encoding := enc;
				Printf.printf "%s\n" (Pure_Entailment.string_of_enc (!Pure_Entailment.encoding));), "encoding"; *)
			"-interactive", Arg.Unit (fun () -> JSIL_Syntax.interactive := true), "interactive predicate folding, enjoy";
	  ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg

let burn_to_disk path data =
	let oc = open_out path in
		output_string oc data;
		close_out oc

let register_dot_graphs (dot_graphs : (string * int, string option) Hashtbl.t) =
	let folder_name = !output_folder in
	if (folder_name = "") then ()
	else
		begin
			Utils.safe_mkdir folder_name;
			Hashtbl.iter
				(fun (proc_name, i) dot_graph ->
					(match dot_graph with
					| Some dot_graph -> burn_to_disk (folder_name ^ "/" ^ proc_name ^ "_" ^ (string_of_int i) ^ ".dot") dot_graph
					| None -> ()))
				dot_graphs
		end

let write_spec_file (file : string ref) =
	let result = "" in
	burn_to_disk (!file ^ ".spec") result

let symb_interpreter prog procs_to_verify spec_tbl which_pred norm_preds  = 
	let results_str, dot_graphs, complete_success =  
					Symb_Interpreter.sym_run_procs prog procs_to_verify spec_tbl which_pred norm_preds in
	Printf.printf "RESULTS\n%s" results_str;

	(if (complete_success) then
		begin
			Printf.printf "ALL Succeeded in %f\n" (Sys.time());
			if (not (!spec_file = "")) then write_spec_file spec_file
		end
		else (Printf.printf "There were Failures in %f\n" (Sys.time())));
	
	register_dot_graphs dot_graphs;
	if (!stats) 
		then JSIL_Syntax.process_statistics ()

let bi_symb_interpreter prog procs_to_verify spec_tbl which_pred norm_preds  = 
	(* Perform symbolic interpretation with bi-abduction then use the result to verify using the normal symbolic execution.*)
	print_endline ("\n*********** Starting bi-abduction symbolic execution. ***********\n") ;
	let results_str_bi, new_spec_tbl = 
			JSIL_Bi_Symb_Interpreter.sym_run_procs prog procs_to_verify spec_tbl which_pred norm_preds in
	print_endline ("\n********** Finished bi-abduction symbolic execution. **********\n") ;
	print_endline ("\n**********    Starting normal symbolic execution.    **********\n") ;
	symb_interpreter prog procs_to_verify new_spec_tbl which_pred norm_preds;
	print_endline ("\n**********     Ending normal symbolic execution.     **********\n") ;
	Printf.printf "RESULT SPECS \n%s" results_str_bi
	
let process_file path =
		print_debug "\n*** Prelude: Stage 1: Parsing program. ***\n";
		let ext_prog = JSIL_Utils.ext_program_of_path path in
		print_debug	
			("The procedures that we will be verifying are: " ^
				(String.concat ", " ext_prog.procedure_names) ^
				"\n");
		print_debug "\n*** Prelude: Stage 1: Parsing successfully completed. ***\n";
		print_debug "*** Prelude: Stage 2: Transforming the program.\n";
		let prog, which_pred = JSIL_Utils.prog_of_ext_prog path ext_prog in
		print_debug "\n*** Prelude: Stage 2: Done transforming the program.\n";
		print_debug "\n*** Prelude: Stage 3: Normalising predicates.\n";
		let norm_preds = Logic_Predicates.normalise ext_prog.predicates in 
		print_debug "\n*** Prelude: Stage 3: Normalisation of predicates completed successfully.";
		let str_of_norm_pred = Logic_Predicates.string_of_normalised_predicates norm_preds in
		print_debug (Printf.sprintf "\n%s\n" str_of_norm_pred);
		print_debug "*** Prelude: Stage 4: Building the spec table.\n";
		Normaliser.pre_normalise_invariants_prog norm_preds prog;
		let spec_tbl = Normaliser.build_spec_tbl norm_preds prog ext_prog.onlyspecs in
		print_debug "*** Prelude: Stage 4: Finished building the spec table\n";
		print_debug "*** Prelude: Stage 5: Add phantom procedures for only-specs.\n";
		Hashtbl.iter
			(fun spec_name spec ->
				let proc = { 	
					proc_name = spec_name; 
					proc_body = Array.make 0 (empty_metadata, SBasic SSkip); 
					proc_params = spec.spec_params;
					ret_label = None; ret_var = Some "ret";
					error_label = None; error_var = Some "err";
					spec = Some spec } in
				Hashtbl.replace prog spec_name proc
			)
			ext_prog.onlyspecs;
		print_debug "*** Prelude: Stage 5: Finished adding phantom procedures for only-specs\n";
		(if (!bi_abduction) then
			bi_symb_interpreter prog ext_prog.procedure_names spec_tbl which_pred norm_preds
		else 
			symb_interpreter prog ext_prog.procedure_names spec_tbl which_pred norm_preds);
		exit 0

let main () =
		arguments ();
		process_file !file


let _ = main()
