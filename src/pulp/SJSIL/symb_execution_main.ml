open JSIL_Syntax

let file = ref ""

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
	let ext_prog = JSIL_Utils.ext_program_of_path path in 
	let norm_preds = Logic_Predicates.normalise ext_prog.predicates in
	let prog, which_pred = JSIL_Utils.prog_of_ext_prog path ext_prog in 
	let spec_tbl = JSIL_Logic_Normalise.build_spec_tbl norm_preds prog in 
	let results = JSIL_Symb_Interpreter.sym_run_procs spec_tbl prog which_pred norm_preds in 
	Printf.printf "RESULTS\n%s" results;
	exit 0


let main () = 
		arguments ();
		process_file !file
		
		
let _ = main()