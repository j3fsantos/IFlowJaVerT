(* open Core.Std *)
open Js_pre_processing
open Js2jsil

let file = ref ""

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [ 
			(* file to compile *)
			"-file", Arg.String(fun f -> file := f), "file to run";
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg

let burn_to_disk path data = 
	let oc = open_out path in 
		output_string oc data; 
		close_out oc 

let process_file path = 
	let exp = 
    (try 
      Parser_main.exp_from_file path 
    with
      | Parser.ParserFailure file ->
        Printf.printf "\nParsing problems with the file '%s'.\n" file;
        exit 1) in
	let exp = add_codenames "main" exp in 
	let cc_tbl, fun_tbl = closure_clarification_top_level "main" exp in 
	let str = print_cc_tbl cc_tbl in 
	let jsil_proc_main = generate_main exp "main" cc_tbl in 
	Printf.printf "closure clarification table: %s\n" str; 
	let main_str = SSyntax_Print.string_of_lprocedure jsil_proc_main in 
	Printf.printf "main code:\n %s\n" main_str
	
let main () = 
	arguments ();
	Parser_main.js_to_xml_parser := "src/parser/lib/js_parser.jar"; 
	Parser_main.verbose := false;
	process_file !file

let _ = main()