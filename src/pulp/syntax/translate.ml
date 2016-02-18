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

let set_level s = 
 level := match s with
	| "b" -> IVL_buitin_functions
	| "c" -> IVL_conditionals
	| "g" -> IVL_goto
	| _ -> raise (Arg.Bad("Shouldn't happen"))

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [ "-file",
      Arg.String(fun f -> file := f),
      "file to run";
      "-level",
      Arg.Symbol (["b"; "c"; "g"], set_level),
      "level of IVL"
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg
    
let create_output (fb : Pulp_Procedure.function_block) path = 
  let content = Pulp_Syntax_Print.string_of_func_block fb in	 
  let path = (Filename.chop_extension path) ^ "/" ^ (Filename.chop_extension path) ^ "." ^ fb.Pulp_Procedure.func_name ^ ".pulp" in
  let oc = open_out path in
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

let translate path level = 
  let p_exp, env = translate_exp path level in
  let p_exp = Simp_Main.simplify p_exp Simp_Common.Simp_Unfold_Specs in
	let functions_folder_name = "functions" in 
	let builtins_folder_name = "builtins" in 
	let specs_folder_name = "specs" in
	let output_folder_name = Filename.chop_extension path in 
  (* TODO: Constructs cfg twice adding entry label twice *)
	(* Why do we need to construct the cfg twice? *)
  let _ = Control_Flow.mk_cfg p_exp (Filename.chop_extension path) in
	Unix.mkdir output_folder_name 0o777;
	Unix.mkdir (output_folder_name ^ "/" ^ functions_folder_name) 0o777; 
	Unix.mkdir (output_folder_name ^ "/" ^ builtins_folder_name) 0o777;
	Unix.mkdir (output_folder_name ^ "/" ^ specs_folder_name) 0o777;
  Pulp_Procedure.AllFunctions.iter (fun fid fwc -> create_output fwc (path  ^ "/" ^ functions_folder_name)) p_exp;
	Pulp_Procedure.AllFunctions.iter (fun fid fwc -> create_output fwc (path ^ "/" ^ builtins_folder_name)) env

let main () =
  Config.apply_config ();
  Parser_main.verbose := false;
  arguments ();
  translate !file !level
  

let _ = main()