open JSIL_Syntax
open JSIL_Memory_Model
open JSIL_Logic_Normalise
open JSIL_Symb_Interpreter

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

let sym_run_procs spec_table prog which_pred = 
	let s_prog = {
		program = prog; 
		which_pred = which_pred; 
		spec_tbl = spec_table
	} in 
	Hashtbl.iter 
		(fun proc_name spec ->
			let pre_post_list = spec.n_proc_specs in 
			List.iter 
				(fun pre_post ->
					(try
						symb_evaluate_proc s_prog proc_name pre_post 
					 with Failure msg -> 
						Printf.printf "Failure: %s\n" msg;
						exit 1
					))
			pre_post_list)
		spec_table


let process_file path = 
	let ext_prog = JSIL_Utils.ext_program_of_path path in 
	let prog, which_pred = JSIL_Utils.prog_of_ext_prog path ext_prog in 
	let spec_tbl = build_spec_tbl prog in 
	sym_run_procs spec_tbl prog which_pred;
	Printf.printf "Success";
	exit 0


let main () = 
		arguments ();
		process_file !file
		
		
let _ = main()