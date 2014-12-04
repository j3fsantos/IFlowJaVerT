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
    
let create_output (content : string) path = 
  let path = (Filename.chop_extension path) ^ ".pulp" in
  let oc = open_out path in
  output_string oc content;
  close_out oc
    
let translate_exp path =
  let exp = 
    try 
      Parser_main.exp_from_file path 
    with
      | Parser.ParserFailure file ->
        Printf.printf "\nParsing problems with the file '%s'.\n" file;
        exit 1 
  in
    
  let p_exp = 
    try 
      exp_to_pulp (!level) exp 
    with
      | PulpNotImplemented exp -> Printf.printf "\nTranslation of Javascript syntax does not support '%s' yet.\n" exp; exit 2
      | Invalid_argument arg -> Printf.printf "\nSomething wrong with the translation '%s'.\n" arg; exit 1
  in p_exp

let translate path = 
  let p_exp = translate_exp path in
  create_output (Pulp_Syntax_Print.string_of_all_functions p_exp) path    

let main () =
  Config.apply_config ();
  Parser_main.verbose := false;
  arguments ();
  translate !file
  

let _ = main()