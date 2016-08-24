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

let build_spec_tbl prog = 
	let spec_table = Hashtbl.create 1021 in 
	let spec_list = 
		Hashtbl.fold
			(fun proc_name proc ac_spec_list ->
				match proc.spec with 
				| None -> ac_spec_list 
				| Some spec -> spec :: ac_spec_list)
			prog
			[] in 
	List.iter
		(fun spec -> 
			let spec_name = spec.spec_name in 
			let spec_params = spec.spec_params in 
			let pre_post_list = spec.proc_specs in 
	 		let normalized_pre_post_list = 
				List.map 
					(fun single_spec -> 
						let pre = single_spec.pre in 
						let post = single_spec.post in 
						let ret_flag = single_spec.ret_flag in 
						let pre_heap, pre_store, pre_p_formulae, pre_gamma = JSIL_Logic_Normalise.normalize_assertion_top_level pre in 
						(* Printf.printf "I managed to normalize the assertion: %s \n"  (string_of_logic_assertion pre false); *)
						let post_heap, post_store, post_p_formulae, post_gamma = JSIL_Logic_Normalise.normalize_assertion_top_level post in
						(* Printf.printf "I managed to normalize the assertion: %s \n"  (string_of_logic_assertion post false); *)
						{	
							n_pre = pre_heap, pre_store, pre_p_formulae, pre_gamma; 
							n_post = post_heap, post_store, post_p_formulae, post_gamma; 
							n_ret_flag = ret_flag
						})
					pre_post_list in 
			let new_spec = {
				n_spec_name = spec_name; 
				n_spec_params = spec_params; 
				n_proc_specs = normalized_pre_post_list
			} in 
			Hashtbl.replace spec_table spec_name new_spec)
		spec_list; 
	(* Printf.printf "before printing the spec table\n"; *)
	let spec_table_str : string = JSIL_Memory_Print.string_of_n_spec_table spec_table in 
	Printf.printf "Spec Table: \n%s" spec_table_str; 
  spec_table


let sym_run_procs spec_table prog which_pred = 
	Hashtbl.iter 
		(fun proc_name spec ->
			let pre_post_list = spec.n_proc_specs in 
			List.iter 
				(fun pre_post ->
					let pre_heap, pre_store, pre_p_formulae, pre_gamma = pre_post.n_pre in 
					let ret_flag = pre_post.n_ret_flag in 
					(try
						symb_evaluate_cmd spec_table pre_post.n_post ret_flag prog proc_name which_pred pre_heap pre_store pre_p_formulae pre_gamma 0 0
					 with Failure msg -> 
						let data = (Printf.sprintf "Failure: %s\n" msg) in 
						burn_to_disk "sym_execution_info.txt" data; 
						exit 1
					))
			pre_post_list)
		spec_table


let process_file path = 
	let ext_prog = JSIL_Utils.ext_program_of_path path in 
	let prog, which_pred = JSIL_Utils.prog_of_ext_prog path ext_prog in 
	let spec_tbl = build_spec_tbl prog in 
	sym_run_procs spec_tbl prog which_pred;
	burn_to_disk "sym_execution_info.txt" "Success"; 
	exit 0

let main () = 
		arguments ();
		process_file !file
		
		
let _ = main()