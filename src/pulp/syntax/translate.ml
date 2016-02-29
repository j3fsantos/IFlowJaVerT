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

type simp_level =
  | Simp_On (* simplifications on *)
  | Simp_Off (* simplifications off *)

let simp = ref Simp_Off

let set_simp s = 
 simp := match s with
	| "on" -> Simp_On 
	| "off" -> Simp_Off 
	| _ -> raise (Arg.Bad("Shouldn't happen"))

let set_level s = 
 level := match s with
	| "bc" -> IVL_buitin_functions (* spec functions, conditionals *)
	| "b" -> IVL_goto (* spec functions, conditionals *)
	| "c" -> IVL_conditionals (* no spec functions, conditionals *)
	| "g" -> IVL_goto_unfold_functions (* No spec functions, no conditionals *)
	| _ -> raise (Arg.Bad("Shouldn't happen"))

let set_smart_simp () = 
	smart_simp := Simp_Common.Simp_Unfold_Specs

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
			"-smartsimp", Arg.Unit(set_smart_simp), "try to simplify calls to builtin libraries"	
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

let translate path level = 
  let p_exp, env = translate_exp path level in
  let p_exp = conditional_simplification p_exp in
	let functions_folder_name = "functions" in 
	let builtins_folder_name = "builtins" in 
	let specs_folder_name = "specs" in
	let output_folder_name = Filename.chop_extension path in 
	let built_ins = env in 
	let specs = Spec_Fun_Specs.get_env_spec () in 
  (* TODO: Constructs cfg twice adding entry label twice *)
	(* Why do we need to construct the cfg twice? *)
  let _ = Control_Flow.mk_cfg p_exp (Filename.chop_extension path) in
	Unix.mkdir output_folder_name 0o777;
	Unix.mkdir (output_folder_name ^ "/" ^ functions_folder_name) 0o777; 
	Unix.mkdir (output_folder_name ^ "/" ^ builtins_folder_name) 0o777;
	Unix.mkdir (output_folder_name ^ "/" ^ specs_folder_name) 0o777;
	print_string (" happy to be here: " ^ output_folder_name  ^ "/" ^ functions_folder_name ^ "\n"); 
  Pulp_Procedure.AllFunctions.iter (fun fid fwc -> create_output fwc (output_folder_name  ^ "/" ^ functions_folder_name)) p_exp;
	Pulp_Procedure.AllFunctions.iter (fun fid fwc -> create_output fwc (output_folder_name ^ "/" ^ builtins_folder_name)) built_ins; 
	Pulp_Procedure.AllFunctions.iter (fun fid fwc -> create_output fwc (output_folder_name ^ "/" ^ specs_folder_name)) specs; 
	Pulp_Syntax_Print.get_all_line_numbers p_exp "line_numbers.txt"

let main () =
  Config.apply_config ();
  Parser_main.verbose := false;
  arguments ();
  translate !file !level
  

let _ = main()