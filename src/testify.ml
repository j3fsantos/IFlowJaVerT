open JSIL_Syntax

let file = ref ""
let output_file_suffix = "_auto.jsil"
let depth = ref 2

let str_bar = "-----------------------------"


let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [
		(* file containing the program to symbolically execute *)
		"-file",  Arg.String(fun f -> file := f), "file to run";
		"-depth", Arg.String (fun s -> depth := int_of_string s), "depth";
	]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg

let burn_to_disk path data =
	let oc = open_out path in
		output_string oc data;
		close_out oc


let process_file path =
	print_debug "\n*** Prelude: Stage 1: Parsing program. ***\n";
	let ext_prog         = JSIL_Syntax_Utils.ext_program_of_path path in
	let prog, which_pred = JSIL_Syntax_Utils.prog_of_ext_prog path ext_prog in
	(* print_debug	("The procedures for which we will generate symbolic tests are: " ^ 
		(String.concat ", " ext_prog.procedure_names) ^ "\n"); *)

	print_debug "*** Prelude: Stage 2: building the spec table and pred table \n";
    let u_preds      = Normaliser.auto_unfold_pred_defs ext_prog.predicates in
	Normaliser.concretize_rec_predicates u_preds !depth;	
	Printf.printf "finished concretizing non-normalised rec predicates\n"; 
	let spec_tbl     = Normaliser.build_spec_tbl prog u_preds ext_prog.onlyspecs ext_prog.lemmas in
	Printf.printf "finished normalizing specs\n"; 
	let n_pred_defs  = Normaliser.normalise_predicate_definitions u_preds in
	let n_pred_defs  = Specs2tests.simplify_preds n_pred_defs in 
	Printf.printf "finished normalising predicate definitions\n"; 
    print_debug (Printf.sprintf "%s\n%s\nSpec Table:\n%s" str_bar str_bar (Symbolic_State_Print.string_of_n_spec_table spec_tbl));
   	let new_spec_tbl = Specs2tests.unfold_pred_in_specs n_pred_defs spec_tbl !depth in 
    Normaliser.print_normaliser_results_to_file new_spec_tbl n_pred_defs;
	print_debug "*** Stage 2: DONE building the spec table and pred table \n";

	

	print_debug "\n*** Prelude: Stage 3: compiling specs to tests. ***\n";
	Specs2tests.make_symbolic_tests prog new_spec_tbl n_pred_defs;  



	print_debug "\n*** Prelude: Stage 4: Printing the generated procedures to a file ***\n";
	let output_file_name = String.sub path 0 (String.rindex path '.') in 
	let output_file_name = output_file_name ^ output_file_suffix in 
	burn_to_disk output_file_name (JSIL_Print.string_of_program prog) 


let main () =
		arguments ();
		process_file !file


let _ = main()