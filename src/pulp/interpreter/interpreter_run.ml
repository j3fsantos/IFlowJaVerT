open Pulp_Translate
open Interpreter
open Memory_Model
open Pulp_Syntax
open Interpreter_Print

let file = ref ""
let test_prelude = ref []

(* Borrowed from run_js.ml *)
let string_to_list str =
    let l = ref [] in
    let current = ref "" in
    String.iter (fun c ->
      if c = ',' then (
          l := !current :: !l ;
          current := ""
      ) else
        current := !current ^ String.make 1 c
    ) str ;
    !current :: List.rev !l

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [ "-file",
      Arg.String(fun f -> file := f),
      "file to run";
      "-test_prelude",
      Arg.String(fun f ->
         test_prelude := !test_prelude @ string_to_list f),
      "include the given files before runnning the specified file."
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg


let pr_test h =
  let lg_obj = Heap.find (BLoc Lg) h in
  try
     let error = Object.find "__$ERROR__" lg_obj in
     Printf.printf "\nA variable [__$ERROR__] is defined at global scope.  Its value is:\n\t %s \n" (string_of_heap_value error);
     exit 1
  with | Not_found ->
     Printf.printf "No variable [__$ERROR__] is defined at global scope.\n"

let run_program path = 
  let exp = 
    try 
      Parser_main.exp_from_file path 
    with
      | Parser.ParserFailure file ->
        Printf.printf "\nParsing problems with the file '%s'.\n" file;
        exit 1 
  in
  let prelude_exp = 
    try 
      Parser_main.exp_from_file (List.hd !test_prelude)
    with
      | Parser.ParserFailure file ->
        Printf.printf "\nParsing problems with the prelude file '%s'.\n" file;
        exit 1
  in 
  let exp = 
    match prelude_exp.Parser_syntax.exp_stx, exp.Parser_syntax.exp_stx with
      | Parser_syntax.Script (_, es1), Parser_syntax.Script (str, es2) -> {exp with Parser_syntax.exp_stx = Parser_syntax.Script (str, es1 @ es2)}
      | _ -> Printf.printf "\nSomething wrong with adding prelude.\n"; exit 1
  in
    
  let p_exp = 
    try 
      exp_to_pulp exp 
    with
      | PulpNotImplemented exp -> Printf.printf "\nTranslation of Javascript syntax does not support '%s' yet.\n" exp; exit 2
      | Invalid_argument arg -> Printf.printf "\nSomething wrong with the translation '%s'.\n" arg; exit 1
  in    
 
  let h = initial_heap () in
  let lop = Heap.find (BLoc Lop) h in
  let lop = Object.add ("__$ERROR__") (HVLiteral (String "")) lop in
  let h = Heap.add (BLoc Lop) lop h in
  
  let result = run_with_heap h p_exp in
  match result.fs_return_type with
    | FTReturn -> pr_test result.fs_heap
    | FTException -> pr_test result.fs_heap; exit 1 

let main () =
  Config.apply_config ();
  Parser_main.verbose := false;
  arguments ();
  run_program !file
  

let _ = main()