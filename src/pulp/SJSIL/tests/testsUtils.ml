open OUnit
open JSIL_Syntax
open JSIL_Print
open JSIL_Interpreter
open Js2jsil

let if_some p f d =
	(match p with
	| None -> d
	| Some p -> f p)

let string_of_outcome o =
	match o with
	| Normal -> "Normal"
	| Error -> "Error"

(**
	General test
*)
type test = 
{
	prelude: string list;
	main: string;
	expected_value: (jsil_return_flag option * jsil_lit option);
	description: string;
}

(**
	General test correctness
*)
let test_correct expected_value actual_value =
	let ertt, ertv = expected_value in
	let artt, artv = actual_value in
	let element_correct ev av =
		(match ev with
		| None -> true
		| Some ev -> ev = av) in
	(element_correct ertt artt) && (element_correct ertv artv)
	
(**
	General running of tests
*)
let run_test template test = 
  let result = template test in
	let ertt, ertv = test.expected_value in
	let artt, artv = result in
  assert_bool (Printf.sprintf "Test failed. Expected : (%s, %s), Got: (%s, %s)" 
	             (if_some ertt string_of_outcome "None") 
							 (if_some ertv (fun x -> string_of_literal x false) "None")
	             (string_of_outcome artt) (string_of_literal artv false)) (test_correct test.expected_value result)

(** ************
	   JSIL TESTS
    ************ **)

(**
	Adding prologue and epilogue to jsil tests
*)
let wrap_jsil_test test pro ep = 
	let main = test.main in
	{ test with main = pro ^ main ^ ep }
	
(**
	Convert a JSIL test into a JSIL program
*)
let string_of_jsil_test test = 
	let prelude = 
		(match test.prelude with
		| [] -> ""
		| _ -> let rec str_of_prelude (li : string list) = 
			     (match li with
					  | [] -> raise (Failure "string_of_test: this cannot happen.") 
					  | [i] -> i
					  | i :: li -> i ^ ", " ^ (str_of_prelude li)) in
					 "import " ^ (str_of_prelude test.prelude)) ^ ";\n" in
	prelude ^ test.main

(**
	Template for running JSIL tests
*)
let test_jsil_template test = 
	let str = string_of_jsil_test test in
	let _ = Printf.printf "%s\n" str in
	let ext_prog = JSIL_Utils.ext_program_of_string str in
	let prog, which_pred = JSIL_Utils.prog_of_ext_prog "" ext_prog in 
	let heap = JSIL_Memory_Model.SHeap.create 1021 in 
  evaluate_prog prog which_pred heap

(** ******************
	   JAVASCRIPT TESTS
    ****************** **)

let test_javascript_template test =
	Parser_main.js_to_xml_parser := "js_parser.jar";
  Parser_main.verbose := false;
	let str = test.main in 
	let offset_converter = Js_pre_processing.memoized_offsetchar_to_offsetline str in 
	let e = 
    (try 
      Parser_main.exp_from_string str
    with
      | Parser.ParserFailure file ->
        Printf.printf "\nParsing problems with the file '%s'.\n" file;
        exit 1) in
	let (ext_prog, cc_tbl, vis_tbl) = js2jsil e offset_converter in 
	let prog, which_pred = JSIL_Utils.prog_of_ext_prog "" ext_prog in 
	let heap = JSIL_Memory_Model.SHeap.create 1021 in 
  evaluate_prog prog which_pred heap (Some cc_tbl) (Some vis_tbl)
