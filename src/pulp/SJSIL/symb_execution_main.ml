open JSIL_Syntax

let file = ref ""
let output_folder = ref ""

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [
			(* file containing the program to symbolically execute *)
			"-file", Arg.String(fun f -> file := f), "file to run";
			"-o", Arg.String(fun f -> output_folder := f), "output folder";
      "-debug", Arg.Unit (fun () -> debug := true), "debug";
	  ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg

let burn_to_disk path data =
	let oc = open_out path in
		output_string oc data;
		close_out oc

let register_dot_graphs dot_graphs =
	let folder_name = !output_folder in
	if (folder_name = "") then ()
	else
		begin
			Utils.safe_mkdir folder_name;
			Hashtbl.iter
				(fun (proc_name, i) dot_graph ->
					burn_to_disk (folder_name ^ "/" ^ proc_name ^ "_" ^ (string_of_int i) ^ ".dot") dot_graph)
				dot_graphs
		end

let process_file path =
  print_debug "Parsing program.\n";
	let ext_prog = JSIL_Utils.ext_program_of_path path in
  print_debug "Normalising predicates.\n";
	let norm_preds = Logic_Predicates.normalise ext_prog.predicates in
  print_debug "Transforming the program.\n";
	let prog, which_pred = JSIL_Utils.prog_of_ext_prog path ext_prog in
  print_debug "Building the spec table.\n";
	let spec_tbl = JSIL_Logic_Normalise.build_spec_tbl norm_preds prog in
	print_debug "Finished computing the spec table!!!\n";
	let results, dot_graphs, complete_success = JSIL_Symb_Interpreter.sym_run_procs spec_tbl prog which_pred norm_preds in
	Printf.printf "RESULTS\n%s" results;
	(if (complete_success) then
		Printf.printf "ALL Succeeded!!!\n"
		else Printf.printf "There were Failures\n");
	register_dot_graphs dot_graphs;
	exit 0


let main () =
		arguments ();
		process_file !file


let _ = main()
