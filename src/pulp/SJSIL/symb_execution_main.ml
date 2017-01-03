open JSIL_Syntax

let file = ref ""
let spec_file = ref ""
let output_folder = ref ""

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
			"-js", Arg.Unit (fun () -> JSIL_Symb_Interpreter.js := true), "js2jsil output"; 
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

let process_file path =
    print_debug "\n*** Prelude: Stage 1: Parsing program. ***\n";
    let ext_prog = JSIL_Utils.ext_program_of_path path in
	let procs_to_verify = Hashtbl.create 37 in
	Hashtbl.iter (fun k v -> Hashtbl.replace procs_to_verify k true) ext_prog.procedures;
	print_debug "The procedures that we will be verifying are:\n";
	Hashtbl.iter (fun k v -> print_debug (Printf.sprintf "\t%s\n" k)) procs_to_verify;
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
	let spec_tbl = JSIL_Logic_Normalise.build_spec_tbl norm_preds prog in
	print_debug "*** Prelude: Stage 4: Finished building the spec table\n";
	let results_str, dot_graphs, complete_success = JSIL_Symb_Interpreter.sym_run_procs procs_to_verify spec_tbl prog which_pred norm_preds in
	Printf.printf "RESULTS\n%s" results_str;
	
	(if (complete_success) then
		begin
			Printf.printf "ALL Succeeded in %f\n" (Sys.time());
			if (not (!spec_file = "")) then write_spec_file spec_file
		end
		else (Printf.printf "There were Failures in %f\n" (Sys.time())));
	
	register_dot_graphs dot_graphs;
	JSIL_Syntax.process_statistics ();
	
	exit 0

let main () =
		arguments ();
		process_file !file


let _ = main()
