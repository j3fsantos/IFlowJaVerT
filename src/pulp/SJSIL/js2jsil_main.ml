(* open Core.Std *)
open Js_pre_processing
open Js2jsil

let harness_path = "harness.js"

let file = ref ""
let harnessing = ref false
let line_numbers = ref false 

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [ 
			(* file to compile *)
			"-file", Arg.String(fun f -> file := f), "file to run";
			(* harnessing *)
			"-harness", Arg.Unit(fun _ -> harnessing := true), "ES6 harness";
			(* show line numbers *) 
			"-line_numbers", Arg.Unit(fun () -> line_numbers := true), "show line numbers";
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  s

let burn_to_disk path data = 
	let oc = open_out path in 
		output_string oc data; 
		close_out oc 

let string_of_file path = 
	let sh = (if (!harnessing) 
	             then load_file harness_path
				 else "") in
	let sf = load_file path in
	sh ^ sf         

let process_file path = 
	let e_str = string_of_file path in 
	let offset_converter = Js_pre_processing.memoized_offsetchar_to_offsetline e_str in 
	let e = 
    (try 
      Parser_main.exp_from_string e_str
    with
      | Parser.ParserFailure file ->
        Printf.printf "\nParsing problems with the file '%s'.\n" file;
        exit 1) in
	let imports, jsil_prog_e, _, _ = js2jsil e offset_converter in 
	let jsil_prog_str = SSyntax_Print.string_of_lprogram (imports, jsil_prog_e) in 
	let file_name = Filename.chop_extension path in 
	burn_to_disk (file_name ^ ".jsil") jsil_prog_str
	
	
let main () = 
	arguments ();
	Parser_main.js_to_xml_parser := "js_parser.jar"; 
	Parser_main.verbose := false;
	process_file !file

let _ = main()