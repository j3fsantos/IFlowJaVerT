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
	let e = 
    (try 
      Parser_main.exp_from_file path 
    with
      | Parser.ParserFailure file ->
        Printf.printf "\nParsing problems with the file '%s'.\n" file;
        exit 1) in
	let jsil_prog_e = js2jsil e in 
	let jsil_prog_str = SSyntax_Print.string_of_lprogram jsil_prog_e in 
	let file_name = Filename.chop_extension path in 
	burn_to_disk (file_name ^ ".jsil") jsil_prog_str
	
	
let main () = 
	arguments ();
	Parser_main.js_to_xml_parser := "src/parser/lib/js_parser.jar"; 
	Parser_main.verbose := false;
	process_file !file

let _ = main()