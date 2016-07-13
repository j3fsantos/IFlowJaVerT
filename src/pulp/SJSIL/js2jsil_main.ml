(* open Core.Std *)
open JSIL_Syntax
open Js_pre_processing
open Js2jsil

let harness_path = "harness.js"

let file = ref ""
let harnessing = ref false
let line_numbers = ref false 
let sep_procs = ref false 
let sexpr = ref false

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
			(* one procedure per file *) 
			"-sep_procs", Arg.Unit(fun () -> sep_procs := true), "one procedure per file";
      "-closure", Arg.Clear(Parser_main.use_json), "use closure parser";
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
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

let create_output ext_proc path =
  let content = JSIL_Print.string_of_ext_procedure ext_proc in
  let path = path ^ "/" ^ ext_proc.lproc_name ^ ".jsil" in
  let oc = open_out path in
  output_string oc content;
  close_out oc
    

let process_file path = 
  try
		let e_str = string_of_file path in 
		let offset_converter = Js_pre_processing.memoized_offsetchar_to_offsetline e_str in
    let e = Parser_main.exp_from_string ~force_strict:true e_str in
    let ext_prog, _, _ = js2jsil e offset_converter in
		let file_name = Filename.chop_extension path in
		(if (not (!sep_procs)) 
			then 
    	  (let jsil_prog_str = JSIL_Print.string_of_ext_program ext_prog in
    		burn_to_disk (file_name ^ ".jsil") jsil_prog_str)
			else 
				(let folder_name = file_name in 
				Utils.safe_mkdir folder_name; 
				Hashtbl.iter (fun p_name p_body -> create_output p_body folder_name) ext_prog.procedures));
		if (!line_numbers) 
			then 
				(let e_line_numbers_str = JSIL_Print.string_of_ext_prog_metadata ext_prog.procedures in
				let file_numbers_name = file_name ^ "_line_numbers.txt" in 
				burn_to_disk file_numbers_name e_line_numbers_str)
			else ()
  with
  | Parser.ParserFailure file -> Printf.printf "\nParsing problems with the file '%s'.\n" file; exit 1
  | Js_pre_processing.EarlyError e -> Printf.printf "\nParser post-processing threw an EarlyError: %s\n" e; exit 1

	
let main () =
        Parser_main.use_json := true;
	arguments ();
        Parser_main.init ();
	Parser_main.verbose := false;
	process_file !file

let _ = main()
