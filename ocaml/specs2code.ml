open JSIL_Syntax

let file = ref ""
let output_file_suffix = "_auto.jsil"

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [
		(* file containing the program to symbolically execute *)
		"-file", Arg.String(fun f -> file := f), "file to run";
	]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg

let burn_to_disk path data =
	let oc = open_out path in
		output_string oc data;
		close_out oc


let process_file path =
	print_debug "\n*** Prelude: Stage 1: Parsing program. ***\n";
	let ext_prog = JSIL_Utils.ext_program_of_path path in
	(* print_debug	("The procedures that we will be verifying are: " ^ 
		(String.concat ", " ext_prog.procedure_names) ^ "\n"); *)

	print_debug "\n*** Prelude: Stage 2: Generating the alternative code for each procedure. ***\n";
	let new_procs = SpecsCompiler.make_executable_specs ext_prog.procedures in 
	let new_ext_prog = { ext_prog with procedures = new_procs } in 

	print_debug "\n*** Prelude: Stage 3: Printing the generated procedures to a file ***\n";
	let output_file_name = String.sub path 0 (String.rindex path '.') in 
	let output_file_name = output_file_name ^ output_file_suffix in 
	burn_to_disk output_file_name (JSIL_Print.string_of_ext_program new_ext_prog) 




let main () =
		arguments ();
		process_file !file


let _ = main()