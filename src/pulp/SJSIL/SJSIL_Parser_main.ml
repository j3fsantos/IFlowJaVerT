open Lexing
open SSyntax
open SJSIL_Interpreter
open Js2jsil

let file = ref ""
let jsil_run = ref false
let do_ssa = ref false

let verbose = ref false

let compile_and_run = ref false

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  (s)

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [ 
			(* file to compile *)
			"-file", Arg.String(fun f -> file := f), "file to run";
			(* run *)
			"-run", Arg.Unit(fun () -> jsil_run := true), "run the program given as input";
			(* ssa normalise *)
			"-ssa", Arg.Unit(fun () -> do_ssa := true), "ssa normalise";
			(* verbositiness *)
			"-verbose", Arg.Unit(fun () -> verbose := true; SJSIL_Interpreter.verbose := true), "verbose output";
			(* compile js file and run *)
			"-from_javascript", Arg.String(fun f -> file := f; compile_and_run := true), "run from javascript";
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg


let burn_to_disk path data = 
	let oc = open_out path in 
		output_string oc data; 
		close_out oc 

let return_to_exit rettype =
  match rettype with
  | Error -> exit 1
  | _     -> ()

let run_jsil_prog prog which_pred = 
	let heap = SHeap.create 1021 in 
        let (rettype, retval) = evaluate_prog prog which_pred heap in
	let final_heap_str = SSyntax_Print.sexpr_of_heap heap in 
    if (!verbose) then Printf.printf "Final heap: \n%s\n" final_heap_str;
				Printf.printf "%s, %s\n" 
				  (match rettype with
					| Normal -> "Normal"
					| Error -> "Error")
					(match rettype with
					| Normal ->  (SSyntax_Print.string_of_literal retval false)
					| Error -> (match retval with
					| Loc loc ->
						(let obj = (try SHeap.find heap loc with
			                  | _ -> (raise (Failure "Error object without a prototype."))) in
			      let lproto = (try SHeap.find obj "@proto" with
						              | _ -> (raise (Failure "Error object without a prototype."))) in
						(match lproto with
						| Loc loc ->
							let objproto = (try SHeap.find heap loc with
							                 | _ -> (raise (Failure "Error object without a prototype."))) in
							let eType = (try SHeap.find objproto "name" with
						                | _ -> String "") in
						  let message = (try SHeap.find obj "message" with
						                | _ -> String "") in
							let eType = 
					      (match eType with
								| LList list -> List.nth list 1
								| _ -> eType) in
						  (SSyntax_Print.string_of_literal eType false) ^ " : " ^ (SSyntax_Print.string_of_literal message false)  
						| _ -> (raise (Failure "Prototype object not an object."))))
					| _ -> SSyntax_Print.string_of_literal retval false));
        return_to_exit rettype

let main () = 
	arguments ();
	if (!compile_and_run) then 
	begin
		Parser_main.js_to_xml_parser := "js_parser.jar";
  	Parser_main.verbose := false;
		let harness = load_file "harness.js" in
		let main = load_file (!file) in
		let all = harness ^ "\n" ^ main in
		let e = (try Parser_main.exp_from_string all with
      	       | Parser.ParserFailure file -> Printf.printf "\nParsing problems with the file '%s'.\n" file; exit 1) in
	  let (oimp, code) = js2jsil e in 
	  let imp = SSyntax_Utils.if_some oimp (fun x -> x) [] in
	  let prog, which_pred = SSyntax_Utils.prog_of_lprog (imp, code) in 
	  	run_jsil_prog prog which_pred
	end
	else
	begin
		let lprog = SSyntax_Utils.lprog_of_path !file in 
		let prog, which_pred = SSyntax_Utils.prog_of_lprog lprog in 
		let prog, which_pred = if (!do_ssa) then SSyntax_SSA.ssa_compile_prog prog else prog, which_pred in 
		if (!jsil_run) then run_jsil_prog prog which_pred else () 
	end
			
let _ = main()


(** 

let string_of_cmd cmd i proc specs dfs_num_table_f =
	let str_i = string_of_int i in
	let str_dfs_i = string_of_int dfs_num_table_f.(i) in
		str_i ^ "/" ^ str_dfs_i ^ ": " ^ 
		(if (i = proc.ret_label) 
			then ("RET: ") 
			else 
				(match proc.error_label with
				| None -> ""
				| Some lab -> if (i = lab) then ("ERR: ") else (""))) ^ 
		SSyntax_Print.string_of_cmd cmd 0 0 false specs true 


let show_init_graph = ref false
let show_dfs = ref false 
let show_dom = ref false 
let show_dom_frontiers = ref false 
let show_phi_placement = ref false
let show_ssa = ref false 



 print dfs
"-specs", Arg.String(fun f -> specs := (Some f)), "specs to check";
"-dfs", Arg.Unit(fun () -> show_dfs := true), "print dfs graph";
"-dom", Arg.Unit(fun () -> show_dom := true), "print dominator graph";
"-frontiers", Arg.Unit(fun () -> show_dom_frontiers := true), "print dominance frontiers";
"-phis", Arg.Unit(fun () -> show_phi_placement := true), "print phi nodes placement";
"-init", Arg.Unit(fun () -> show_init_graph := true), "print initial graph";		
		

let parse_with_error_logic lexbuf =
  try SJSIL_Parser.specs_target SJSIL_Lexer.read lexbuf with
  | SJSIL_Lexer.SyntaxError msg ->
    Printf.fprintf stderr "Lexer Error at position %a: %s\n" print_position lexbuf msg;
		[]
  | SJSIL_Parser.Error ->
    Printf.fprintf stderr "Syntax Error at position %a\n" print_position lexbuf;
    exit (-1)


let process_specs filename = 
	match filename with 
	| None -> () 
	| Some filename -> 
		let inx = open_in filename in
		let lexbuf = Lexing.from_channel inx in
		lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
		let specs = parse_and_print_logic lexbuf in 
		close_in inx

let parse_and_print_logic lexbuf = 
	let spec_list = parse_with_error_logic lexbuf in
	let spec_table = Hashtbl.create 1021 in 
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
						Printf.printf "About to normalize the beautiful assertion: %s \n" (JSIL_Logic_Print.string_of_logic_assertion pre false);
						let pre_heap, pre_store, pre_p_formulae = JSIL_Logic_Normalise.normalize_assertion_top_level pre in 
						Printf.printf "I managed to normalize this assertion\n";
						let post_heap, post_store, post_p_formulae = JSIL_Logic_Normalise.normalize_assertion_top_level post in 
						{	
							n_pre = pre_heap, pre_store, pre_p_formulae; 
							n_post = post_heap, post_store, post_p_formulae; 
							n_ret_flag = ret_flag
						}
					)
					pre_post_list in 
			let new_spec = 
				{
					n_spec_name = spec_name; 
					n_spec_params = spec_params; 
					n_proc_specs = normalized_pre_post_list
				} in 
			Hashtbl.replace spec_table spec_name new_spec 
		) 
		spec_list;  
	let spec_table_str : string = JSIL_Logic_Print.string_of_n_spec_table spec_table in 
	Printf.printf "Spec Table: \n %s" spec_table_str; 
  spec_table



let cond_print_graph test graph nodes string_of_node graph_name proc_folder = 
	if (test) 
		then 
			(let graph_str = Graph_Print.dot_of_graph graph nodes string_of_node graph_name in
			burn_to_disk (proc_folder ^ "/" ^ graph_name ^ ".dot") graph_str)
		else () 	


let ssa_normalise_proc proc output_folder_name = 
	let proc = remove_unreachable_code proc true in

	Printf.printf "Starting ssa pre-processing.\n";
	
	let proc_folder = (output_folder_name ^ "/" ^ proc.proc_name) in 
	Utils.safe_mkdir proc_folder; 
	
	let nodes, vars, succ_table, pred_table, tree_table, parent_table, dfs_num_table_f, dfs_num_table_r, which_pred = 
		SSyntax_Utils.get_proc_info proc in 
	let succ_table, pred_table = get_succ_pred proc.proc_body proc.ret_label proc.error_label in
	
	let string_of_cmd_ssa cmd i = SSyntax_Print.string_of_cmd cmd 0 0 false false true in 	
	let string_of_cmd_main cmd i = string_of_cmd cmd i proc true dfs_num_table_f in 
	
	cond_print_graph (!show_init_graph) succ_table nodes string_of_cmd_main "succ" proc_folder;	
	cond_print_graph (!show_dfs) tree_table nodes string_of_cmd_main "dfs" proc_folder;
	
	let dom_table, rev_dom_table = SSyntax_Utils_Graphs.lt_dom_algorithm succ_table pred_table parent_table dfs_num_table_f dfs_num_table_r in
	cond_print_graph (!show_dom) rev_dom_table nodes string_of_cmd_main "dom" proc_folder;
	
	let rev_dom_table, dominance_frontiers, phi_functions_per_node, new_proc = 
  	SSyntax_SSA.ssa_compile proc vars nodes succ_table pred_table parent_table dfs_num_table_f dfs_num_table_r which_pred in 
  let final_succ_table, final_pred_table = SSyntax_Utils_Graphs.get_succ_pred new_proc.proc_body new_proc.ret_label new_proc.error_label in   
  	
  cond_print_graph (!show_ssa) final_succ_table new_proc.proc_body string_of_cmd_ssa "ssa" proc_folder;
  			
  (if (!show_dom_frontiers) 
  	then 
  		let str_domfrontiers = Graph_Print.print_node_table dominance_frontiers Graph_Print.print_int_list in
  		burn_to_disk (proc_folder ^ "/dom_frontiers.txt") str_domfrontiers
  	else ()); 
  	
  (if (!show_phi_placement) 
  	then 
  		let phi_functions_per_node_str : string = SSyntax_SSA.print_phi_functions_per_node phi_functions_per_node in 
  		burn_to_disk (proc_folder ^ "/phi_placement.txt") phi_functions_per_node_str
  	else ());
  	
  let new_proc_str = SSyntax_Print.string_of_procedure new_proc false in 
  Printf.printf "\n%s\n" new_proc_str; 
  
  new_proc, which_pred

*)
