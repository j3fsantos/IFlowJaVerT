open Lexing
open JSIL_Syntax
open Symbolic_State
open JSIL_Interpreter

let file    = ref ""
let js      = ref false
let compile = ref false
let test262 = ref false


let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  (s)

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [
			(* file to compile *)
			"-file", Arg.String(fun f -> file := f), "file to run";
			
			(* access debugging information *)
			"-debug", Arg.Unit(fun () -> debug := true; verbose := true), "debug information";
			
			(* it is a compiled js program *)
			"-js", Arg.Unit(fun () -> js := true), "input is a compiled js program";
			
			(* compile and run *)
			"-js2jsil", Arg.Unit(fun () -> js := true; compile := true), "compile and run";
			
			(* use test262 harness *) 
			"-test262",  Arg.Unit(fun () -> js := true; compile := true; test262 := true), "use test262 harness";
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

let string_of_ret_val heap ret_flag v = 
	match ret_flag with 
	| Normal -> JSIL_Print.string_of_literal v false
	| Error -> if (!js) then Js2jsil_constants.string_of_js_error heap v else ""
	
let run_jsil_prog prog which_pred cc_tbl vis_tbl =
	let heap = SHeap.create 1021 in
  let (ret_flag, ret_val) = evaluate_prog prog which_pred heap cc_tbl vis_tbl  in
	let final_heap_str = JSIL_Memory_Print.string_of_heap heap in
  if (!debug) then Printf.printf "Final heap: \n%s\n" final_heap_str;
	Printf.printf "%s, %s\n"
		(JSIL_Print.string_of_return_flag ret_flag)			
		(string_of_ret_val heap ret_flag ret_val);
  return_to_exit ret_flag


let main () =
	Parser_main.use_json := true;
	arguments ();
  Parser_main.init ();
	if (!compile) then (
		try 
  		Parser_main.verbose := false;
    	let main = load_file (!file) in
			let all = if (!test262) then (load_file "harness.js") ^ "\n" ^ main else main in 
			let offset_converter = Js_pre_processing.memoized_offsetchar_to_offsetline all in
			let e = Parser_main.exp_from_string ~force_strict:true all in
			let (ext_prog, cc_tbl, vis_tbl) = Js2jsil_compiler.js2jsil e offset_converter false in
   		let prog, which_pred = JSIL_Utils.prog_of_ext_prog !file ext_prog in
      run_jsil_prog prog which_pred (Some cc_tbl) (Some vis_tbl)
    with 
    		Parser.ParserFailure file -> Printf.printf "\nParsing problems with the file '%s'.\n" file; exit 1
      | Parser.JS_To_XML_parser_failure
      | Parser.XmlParserException -> Printf.printf "\nXML parsing issues.\n"; exit 1
      | Js_pre_processing.EarlyError e -> Printf.printf "\nParser post-processing threw an EarlyError: %s\n" e; exit 1)
	else (
		let ext_prog = JSIL_Utils.ext_program_of_path !file in
		Printf.printf "I got the program to run:\n%s\n" (JSIL_Print.string_of_ext_program ext_prog);
		let prog, which_pred = JSIL_Utils.prog_of_ext_prog !file ext_prog in
		Printf.printf "I de-labeled the program to run\n";
		run_jsil_prog prog which_pred None None 
	)
		
let _ = main()
