(* ./src/pulp/logic/pulp_Analysis_Main.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open State_Graph

type analysis_type =
  | SymbolicExec
  | BiAbduct

let analysis_type_map = ["symexec", SymbolicExec; 
                         "biabduct", BiAbduct]

let file = ref ""
let analysis_op = ref SymbolicExec
   
let parse_flags () =
  let usage_msg="Usage: [-s <strategy>] [-p <precondition>] -f <file_name>" in
  Arg.parse
    ["-f", 
     Arg.String(fun f -> file := f), 
    "JavaScript file name";
    
     "-s", 
     Arg.String(fun s -> 
       if (List.mem_assoc s analysis_type_map) 
         then analysis_op := List.assoc s analysis_type_map
         else Format.eprintf "WARNING: Ignored strategy %s.@." s
     ), 
     "The symbolic execution strategy. Choose one of: "^ (String.concat ", " (List.map (fun (s, _) -> s) analysis_type_map))]
  (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
  usage_msg
  
let initialize () =
  Config.apply_config ();
  Parser_main.verbose := false;
  CoreStar_Frontend_Pulp.initialize ()
  
let analyse_function current_fun all_funcs env =
    let path = (Filename.chop_extension !file) in
    match (!analysis_op) with
      | SymbolicExec -> Pulp_Sym_Exec.execute_all current_fun all_funcs env path
      | BiAbduct -> Pulp_Abduct.execute current_fun all_funcs env

let get_pexp () =
  let exp = 
    try 
      Parser_main.exp_from_file !file 
    with
      | Parser.ParserFailure file ->
        Printf.printf "\nParsing problems with the file '%s'.\n" file;
        exit 1 
  in
  let p_exp, p_env = Pulp_Translate.exp_to_pulp Pulp_Translate.IVL_goto_with_get_value exp Pulp_Syntax_Utils.main_fun_id [] in
  let p_exp = Simp_Main.simplify p_exp Simp_Common.Simp_Specs in
  p_exp, p_env

let main () = 
   initialize ();
   parse_flags ();
   
   let expression_map, env = get_pexp() in       
   Pulp_Procedure.AllFunctions.iter (fun fid f -> ignore (analyse_function f expression_map (Spec_Fun_Specs.get_env_spec()))) expression_map
      
let _ = main ()