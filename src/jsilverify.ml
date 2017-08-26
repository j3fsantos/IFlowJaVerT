open JSIL_Syntax

let file = ref ""
let spec_file = ref ""
let output_folder = ref ""
let stats = ref false
let interactive = ref false

let str_bar = "-----------------------------"

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [
			(* file containing the program to symbolically execute *)
			"-file", Arg.String(fun f -> file := f), "file to run";
			"-o", Arg.String(fun f -> output_folder := f), "output folder";
      "-syntax", Arg.Unit(fun () -> JSIL_Syntax_Utils.syntax_checks_enabled := true), "syntax checks";
			"-specs", Arg.String (fun f -> spec_file := f), "specification file";
			(* *)
			"-js", Arg.Unit (fun () -> Symb_Interpreter.js := true; JSIL_Syntax_Utils.js := true)
									  (* Bi_Symb_Interpreter.js := true *), "js2jsil output";
			(* *)
			"-stats", Arg.Unit (fun () -> stats := true), "stats";
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

let symb_interpreter prog procs_to_verify spec_tbl lemma_tbl which_pred norm_preds  =
	let results_str, dot_graphs, complete_success, results =
					Symb_Interpreter.sym_run_procs prog procs_to_verify spec_tbl lemma_tbl which_pred norm_preds in
	print_normal (Printf.sprintf "RESULTS\n%s" results_str);

	(if (complete_success) then
		begin
			Printf.printf "ALL specs succeeded in %f\n" (Sys.time());
			print_normal (Printf.sprintf "ALL specs succeeded in %f\n" (Sys.time()));
			if (not (!spec_file = "")) then write_spec_file spec_file
		end
		else (
			Printf.printf "There were Failures in %f\n" (Sys.time());
			print_normal (Printf.sprintf "There were Failures in %f\n" (Sys.time()))));

	register_dot_graphs dot_graphs;
	if (!stats)
		then JSIL_Syntax.process_statistics ();
	results



let process_file path =

		(** Step 1: PARSING                                            *)
		(*  -----------------------------------------------------------*)
		print_debug "\n***Stage 1: Parsing program. ***\n";
		let ext_prog = JSIL_Syntax_Utils.ext_program_of_path path in

		print_debug
			("The procedures that we will be verifying are: " ^
				(String.concat ", " ext_prog.procedure_names) ^
				"\n");
		print_debug "\n*** Stage 1: DONE Parsing. ***\n";


		(** Step 2: Syntactic Checks + Program transformation          *)
		(*  -----------------------------------------------------------*)
		print_debug "*** Stage 2: Transforming the program.\n";
		let prog, which_pred = JSIL_Syntax_Utils.prog_of_ext_prog path ext_prog in
    JSIL_Syntax_Utils.syntax_checks ext_prog prog which_pred;
    print_debug "\n*** Stage 2: DONE transforming the program.\n";

		(** Step 3: Normalisation                                      *)
		(*     3.1 - auto-unfolding pred definitions                   *)
		(*     3.2 - auto-unfolding program invariants                 *)
		(*     3.3 - normalising specifications                        *)
    (*     3.4 - normalising pred definitions                      *)
    (*     3.5 - print result to file                              *)
		(*  -----------------------------------------------------------*)
		print_debug "*** Stage 3: Building the spec table.\n";
		let u_preds = Normaliser.auto_unfold_pred_defs ext_prog.predicates in
		Normaliser.pre_normalise_invariants_prog u_preds prog;
		let spec_tbl = Normaliser.build_spec_tbl prog u_preds ext_prog.onlyspecs ext_prog.lemmas in
		let n_pred_defs = Normaliser.normalise_predicate_definitions u_preds in
    print_debug (Printf.sprintf "%s\n%s\nSpec Table:\n%s" str_bar str_bar (Symbolic_State_Print.string_of_n_spec_table spec_tbl));
    Normaliser.print_normaliser_results_to_file spec_tbl n_pred_defs;
		print_debug "*** Stage 3: DONE building the spec table\n";

		(** Step 4: Proving                                            *)
		(*     4.1 - lemmas                                            *)
		(*     3.2 - specs                                             *)
		(*  -----------------------------------------------------------*)
   		print_debug "*** Stage 4: Proving lemmas and specifications.\n";
    	let _ = Symb_Interpreter.prove_all_lemmas ext_prog.lemmas prog spec_tbl which_pred n_pred_defs in ();
		let _ = symb_interpreter prog ext_prog.procedure_names spec_tbl ext_prog.lemmas which_pred n_pred_defs in ();
		close_output_files();
		exit 0

let main () =
		arguments ();
		process_file !file


let _ = main()
