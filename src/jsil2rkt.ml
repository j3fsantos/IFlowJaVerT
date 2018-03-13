open Lexing
open JSIL_Syntax
open JSIL_Interpreter

let file = ref ""
let js = ref false
let verbose = ref false

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
			(* js *)
			"-js", Arg.Unit(fun () -> js := true), "for js";
			(* test262 *)
			"-test262", Arg.Unit(fun () -> js := true; JS2JSIL_Compiler.test262 := true), "test262";
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

let generate_js_heap_and_internal_functions () = 				

  let template_internal_procs_racket = if !JS2JSIL_Compiler.test262 then SExpr_Templates_Racket.template_internal_procs_racket else SExpr_Templates.template_internal_procs_racket in
  let template_hp_racket             = if !JS2JSIL_Compiler.test262 then SExpr_Templates_Racket.template_hp_racket             else SExpr_Templates.template_hp_racket in
  
	let int_ext_prog = JSIL_Syntax_Utils.ext_program_of_path "internals_builtins_procs.jsil" in
	let int_prog, _ = JSIL_Syntax_Utils.prog_of_ext_prog "internals_builtins_procs.jsil" int_ext_prog in
	let sint_prog = SExpr_Print.sexpr_of_program int_prog false in
	let str_int_prog = Printf.sprintf template_internal_procs_racket sint_prog in
  let filename = if !JS2JSIL_Compiler.test262 then "internals_builtins_procs_racket.rkt" else "internals_builtins_procs.rkt" in
	burn_to_disk filename str_int_prog;
	
	let ih_ext_prog = JSIL_Syntax_Utils.ext_program_of_path "initial_heap.jsil" in
	let ih_prog, ih_which_pred = JSIL_Syntax_Utils.prog_of_ext_prog "initial_heap.jsil" ih_ext_prog in
	let ih_heap = make_initial_heap true in  
  	let _ = evaluate_prog ih_prog ih_which_pred ih_heap None None in
	let str_ih_heap = SExpr_Print.sexpr_of_heap ih_heap in
	let str_ih_heap = Printf.sprintf template_hp_racket str_ih_heap in
  let filename = if !JS2JSIL_Compiler.test262 then "hp_racket.rkt" else "hp.rkt" in
	burn_to_disk filename str_ih_heap; 
	int_prog
	

let main () =
	Parser_main.use_json := true;
	arguments ();
  Parser_main.init ();

  let template_wp_racket             = if !JS2JSIL_Compiler.test262 then SExpr_Templates_Racket.template_wp_racket             else SExpr_Templates.template_wp_racket in
  let template_procs_jsil_racket     = if !JS2JSIL_Compiler.test262 then SExpr_Templates_Racket.template_procs_jsil_racket     else SExpr_Templates.template_procs_jsil_racket in
  let template_procs_racket          = if !JS2JSIL_Compiler.test262 then SExpr_Templates_Racket.template_procs_racket          else SExpr_Templates.template_procs_racket in 

	try (
	
  	if (!file <> "") then (
  	
  	let prog, which_pred = (match !JS2JSIL_Compiler.test262 with
  	| false -> 
  			let ext_prog = JSIL_Syntax_Utils.ext_program_of_path !file in
  			JSIL_Syntax_Utils.prog_of_ext_prog !file ext_prog
  	| true -> 
  			let harness = load_file "harness.js" in
  			let main = load_file !file in
  			let main = JSIL_PreParser.stringify_assume_and_assert main in
  			let all = harness ^ "\n\n" ^ main in
  			let offset_converter = JS_Utils.memoized_offsetchar_to_offsetline all in
  			let e = Parser_main.exp_from_string ~force_strict:true all in
  			let (ext_prog, _, _) = JS2JSIL_Compiler.js2jsil e offset_converter false in
  			JSIL_Syntax_Utils.prog_of_ext_prog !file ext_prog) in
  	
  	(* serializing JS internal functions + JS initial heap *)
  	if (!js) then (
  		let int_prog = generate_js_heap_and_internal_functions () in 
  		let _ = Hashtbl.iter (fun k _ -> if (Hashtbl.mem int_prog k) then (Hashtbl.remove prog k)) prog in 
  		());
  	
  	(* serializing the which_pred table *)
  	let wp_array_str = SExpr_Print.print_which_pred which_pred in
  	let str_wp = Printf.sprintf template_wp_racket wp_array_str in 
    let filename = if !JS2JSIL_Compiler.test262 then "wp_racket.rkt" else "wp.rkt" in
  	burn_to_disk filename str_wp;
  	
  	(* I have to understand what this is doing *)
  	(* let _ = Hashtbl.iter (fun k _ -> if (Hashtbl.mem int_prog k) then (Hashtbl.remove prog k)) prog in *)
  	
  	let sprog = SExpr_Print.sexpr_of_program prog false in
  	let sprog_in_template =
      (match !js with
      | false -> Printf.sprintf template_procs_jsil_racket sprog
      | true  -> Printf.sprintf template_procs_racket sprog) in
  	let filename = Filename.chop_extension !file in
  	let just_the_filename = Filename.basename filename in
  	print_endline just_the_filename;
    burn_to_disk (filename ^ ".rkt") sprog_in_template;
  	
  	(match !JS2JSIL_Compiler.test262 with
  	| false -> ()
  	| true -> 
  			let exit_code = Sys.command ("cp " ^ filename ^ ".rkt .") in
    		let exit_code = Sys.command ("racket "^ just_the_filename ^ ".rkt") in
  			(* let _ = Sys.command ("rm "^ just_the_filename ^ ".rkt") in *)
    		exit(exit_code)
  	))
	)
  with
	|	Parser.ParserFailure file -> Printf.printf "\nParsing problems with the file '%s'.\n" file; exit 1
  | Parser.JS_To_XML_parser_failure
  | Parser.XmlParserException -> Printf.printf "\nXML parsing issues.\n"; exit 1
  | JS2JSIL_Preprocessing.EarlyError e -> Printf.printf "\nParser post-processing threw an EarlyError: %s\n" e; exit 1
	| JSIL_PreParser.Unparseable e -> Printf.printf "\nFile not parseable: %s\n" e; exit 1
	 

let _ = main()
