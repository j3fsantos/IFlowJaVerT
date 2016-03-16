(* ./src/pulp/syntax/translate.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Pulp_Translate
open Interpreter
open Memory_Model
open Pulp_Syntax
open Interpreter_Print

let file = ref ""
let level = ref IVL_goto
let smart_simp = ref Simp_Common.Simp_Specs
let line_numbers_on = ref false

type simp_level =
  | Simp_On (* simplifications on *)
  | Simp_Off (* simplifications off *)

let simp = ref Simp_Off
let sexpr = ref false

let set_simp s = 
 simp := match s with
	| "on" -> Simp_On 
	| "off" -> Simp_Off 
	| _ -> raise (Arg.Bad("Shouldn't happen"))

let set_level s = 
 level := match s with
	| "bc" -> IVL_buitin_functions (* spec functions, conditionals *)
	| "b" -> IVL_goto (* spec functions, no conditionals *)
	| "c" -> IVL_conditionals (* no spec functions, conditionals *)
	| "g" -> IVL_goto_unfold_functions (* No spec functions, no conditionals *)
	| _ -> raise (Arg.Bad("Shouldn't happen"))

let set_smart_simp () = 
	smart_simp := Simp_Common.Simp_Unfold_Specs

let set_sexpr () = 
	sexpr := true

let set_numbers_on () = 
	line_numbers_on := true


let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [ 
			"-file", Arg.String(fun f -> file := f), "file to run";
      (* *)
			"-level", Arg.Symbol (["bc"; "b"; "c"; "g"], set_level), "level of IVL"; 
			(* *)
			"-simp", Arg.Symbol(["on"; "off"], set_simp), "enable simplifications"; 
			(* *)
			"-smartsimp", Arg.Unit(set_smart_simp), "try to simplify calls to builtin libraries";	
			(* *)
			"-sexpr", Arg.Unit(set_sexpr), "generate output in s-expression format";
			(* *)
			"-numbers", Arg.Unit(set_numbers_on), "show line numbers in procedures"
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg
						    
let create_output (fb : Pulp_Procedure.function_block) path = 
  let content = Pulp_Syntax_Print.string_of_func_block fb in	 
  let path = path ^ "/" ^ fb.Pulp_Procedure.func_name ^ ".pulp" in
  let oc = open_out path in
	print_string ("path: " ^ path ^ "\n"); 
  output_string oc content;
  close_out oc
    
let translate_exp path level =
  let exp = 
    try 
      Parser_main.exp_from_file path 
    with
      | Parser.ParserFailure file ->
        Printf.printf "\nParsing problems with the file '%s'.\n" file;
        exit 1 
  in
    
  let p_exp, env = 
    try 
      exp_to_pulp level exp Pulp_Syntax_Utils.main_fun_id [] (* TODO add option for built-in functions - what is this todo? *)
    with
      | PulpNotImplemented exp -> Printf.printf "\nTranslation of Javascript syntax does not support '%s' yet.\n" exp; exit 2
      | Invalid_argument arg -> Printf.printf "\nSomething wrong with the translation '%s'.\n" arg; exit 1
  in p_exp, env

let conditional_simplification p_exp = 
	match !simp with
	| Simp_On -> Simp_Main.simplify p_exp !smart_simp
	| Simp_Off -> p_exp

let serialize_sexpr folder_name procs built_ins specs = 
	let serialize_procs proc_map = 
		Pulp_Procedure.AllFunctions.fold
			(fun key  fb acc_str -> 
					acc_str ^ "\n" ^ 
					(Pulp_Syntax_Print.sexpr_of_func_block fb (!line_numbers_on)))
			proc_map
			"" in 
  let burn_to_disk path data = 
		let oc = open_out path in 
			output_string oc data; 
			close_out oc in
  (* serialize the three sets of procedures as strings*)   
	let procs_content = serialize_procs procs in 
	let built_ins_content = serialize_procs built_ins in 
	let specs_content = serialize_procs specs in
	let heap_initial_content = Interpreter_Print.serialize_heap_sexpr (Interpreter.initial_heap ()) in
	(* create a new directory*)
	Utils.safe_mkdir folder_name;
	(* burn to disk *)
	burn_to_disk (folder_name ^ "/functions.scm") (Printf.sprintf "('procedures \n %s\n)" procs_content); 
	burn_to_disk (folder_name ^ "/builtins.scm") (Printf.sprintf "('procedures \n %s\n)" built_ins_content);
  burn_to_disk (folder_name ^ "/specs.scm") (Printf.sprintf "('procedures \n %s\n)" specs_content); 
	burn_to_disk (folder_name ^ "/heap.scm") heap_initial_content

let serialize output_folder_name p_exp built_ins specs = 
	let functions_folder_name = "functions" in 
	let builtins_folder_name = "builtins" in 
	let specs_folder_name = "specs" in
	Utils.safe_mkdir output_folder_name;
	Utils.safe_mkdir (output_folder_name ^ "/" ^ functions_folder_name); 
	Utils.safe_mkdir (output_folder_name ^ "/" ^ builtins_folder_name);
	Utils.safe_mkdir (output_folder_name ^ "/" ^ specs_folder_name);
	(* print_string (" happy to be here: " ^ output_folder_name  ^ "/" ^ functions_folder_name ^ "\n"); *)
  Pulp_Procedure.AllFunctions.iter (fun fid fwc -> create_output fwc (output_folder_name  ^ "/" ^ functions_folder_name)) p_exp;
	Pulp_Procedure.AllFunctions.iter (fun fid fwc -> create_output fwc (output_folder_name ^ "/" ^ builtins_folder_name)) built_ins; 
	Pulp_Procedure.AllFunctions.iter (fun fid fwc -> create_output fwc (output_folder_name ^ "/" ^ specs_folder_name)) specs; 
	Pulp_Syntax_Print.get_all_line_numbers p_exp "line_numbers.txt"	

let translate path level = 
	let output_folder_name = Filename.chop_extension path in 
  let p_exp, env = translate_exp path level in
  let p_exp = conditional_simplification p_exp in
	let built_ins = env in 
	let specs = Spec_Fun_Specs.get_env_spec () in 
  (* TODO: Constructs cfg twice adding entry label twice *)
	(* Why do we need to construct the cfg twice? *)
  let _ = Control_Flow.mk_cfg p_exp (Filename.chop_extension path) in
	if (!sexpr) 
		then serialize_sexpr output_folder_name p_exp built_ins specs  
		else serialize output_folder_name p_exp built_ins specs 

let main () =
  Config.apply_config ();
  Parser_main.verbose := false;
  arguments ();
  translate !file !level
  

let _ = main()