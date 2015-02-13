open Pulp_Translate
open Interpreter
open Memory_Model
open Pulp_Syntax
open Interpreter_Print

let file = ref ""
let test_prelude = ref []
let calculate_stats = ref false

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
      "include the given files before runnning the specified file.";
      "-stats",
      Arg.Unit(fun () -> calculate_stats := true),
      "to calculate stats";
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
      match !test_prelude with
        | [] -> None 
        | hd :: _ -> Some (Parser_main.exp_from_file (List.hd !test_prelude))
    with
      | Parser.ParserFailure file ->
        Printf.printf "\nParsing problems with the prelude file '%s'.\n" file;
        exit 1
  in 
  let exp = 
    match prelude_exp with
      | None -> exp
      | Some prelude_exp -> 
		    begin match prelude_exp.Parser_syntax.exp_stx, exp.Parser_syntax.exp_stx with
		      | Parser_syntax.Script (_, es1), Parser_syntax.Script (str, es2) -> {exp with Parser_syntax.exp_stx = Parser_syntax.Script (str, es1 @ es2)}
		      | _ -> Printf.printf "\nSomething wrong with adding prelude.\n"; exit 1 
        end
  in
    
  let p_exp = 
    try 
      exp_to_pulp IVL_goto exp Pulp_Syntax_Utils.main_fun_id
    with
      | PulpNotImplemented exp -> Printf.printf "\nTranslation of Javascript syntax does not support '%s' yet.\n" exp; exit 2
      | Invalid_argument arg -> Printf.printf "\nSomething wrong with the translation '%s'.\n" arg; exit 1
  in 
  
  let p_exp_simpl = (*Simp_Main.simplify*) p_exp in 
  
  if (!calculate_stats) then begin
	  let exp_string = Pretty_print.string_of_exp false exp in
	  let exp_string_lines = List.length (Str.split (Str.regexp "\n") exp_string) in
	  let p_exp_string = Pulp_Syntax_Print.string_of_all_functions p_exp in
	  let p_exp_string_lines = List.length (Str.split (Str.regexp "\n") p_exp_string) in 
	  
	  let p_exp_simpl_string = Pulp_Syntax_Print.string_of_all_functions p_exp_simpl in
	  let p_exp_simpl_string_lines = List.length (Str.split (Str.regexp "\n") p_exp_simpl_string) in
	  
	  let name = Filename.basename path in
	  Printf.printf "\nLine count: %s, %i, JS\n" name exp_string_lines;
	  Printf.printf "\nLine count: %s, %i, IVL\n" name p_exp_string_lines;
	  Printf.printf "\nLine count: %s, %i, IVL_SIMP\n" name p_exp_simpl_string_lines; exit 1;
  end;
 
  let h = initial_heap () in
  let lop = Heap.find (BLoc Lop) h in
  let lop = Object.add ("__$ERROR__") (HVLiteral (String "")) lop in
  let h = Heap.add (BLoc Lop) lop h in
  
  let result = run_with_heap h p_exp_simpl in
  match result.fs_return_type with
    | FTReturn -> pr_test result.fs_heap
    | FTException -> pr_test result.fs_heap; Printf.printf "\nException was thrown.\n";
      begin match result.fs_return_value with
        | VHValue (HVObj l) -> 
          begin
            let actual_excep_obj = Heap.find l result.fs_heap in
            let actual_excep_proto = Object.find (Pulp_Syntax_Print.string_of_builtin_field FProto) actual_excep_obj in
              begin match actual_excep_proto with
                | HVObj (BLoc l) -> Printf.printf "\n %s \n" (Pulp_Syntax_Print.string_of_builtin_loc l)
                | _ -> ()
              end
          end
        | _ -> ()
      end; exit 1

let main () =
  Config.apply_config ();
  Parser_main.verbose := false;
  arguments ();
  run_program !file
  

let _ = main()