open OUnit
open Pulp_Logic
open Pulp_Syntax
open Pulp_Sym_Exec
open Pulp_Procedure
open Control_Flow
open Pulp_Logic_Print
open Pulp_Logic_Utils
open CoreStar_Frontend_Pulp
open Pulp_Translate

let test_apply_spec_template formula cmd_pre cmd_post expected_post =
  Config.apply_config ();
  CoreStar_Frontend_Pulp.initialize ();
  let posts = CoreStar_Frontend_Pulp.apply_spec formula cmd_pre cmd_post in
  match posts with
    | Some posts -> assert_bool ("Symbolic Execution. Postcondition. 
       Expected :" ^ (String.concat "\n" (List.map string_of_formula expected_post)) ^ 
       " Actual: " ^ (String.concat "\n" (List.map string_of_formula posts))) 
      (List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) expected_post) posts)
    | _ -> assert_failure "Postcondition not found."

let test_function_call_name () =
  Config.apply_config ();
  CoreStar_Frontend_Pulp.initialize ();
  let e = Corestar.Vars.freshe_str "lv" in
  let x = Corestar.Vars.freshp_str "x" in
  let z = Corestar.Vars.freshp_str "z" in
  let f1 = Corestar.Psyntax.P_EQ (Corestar.Psyntax.Arg_var x, Corestar.Psyntax.Arg_var z) in
  let f2 = Corestar.Psyntax.P_EQ (Corestar.Psyntax.Arg_var z, Corestar.Psyntax.Arg_string "fid1") in
  let Some formula = Corestar.Sepprover.convert [f1; f2] in
  let pre = Corestar.Psyntax.P_EQ (Corestar.Psyntax.Arg_var x, Corestar.Psyntax.Arg_var e) in
  let post = Corestar.Psyntax.P_EQ (Corestar.Psyntax.Arg_var x, Corestar.Psyntax.Arg_var e) in
  let spec = Corestar.Spec.mk_spec [pre] [post] Corestar.Spec.ClassMap.empty in
  let posts = Corestar.Specification.jsr (!logic) (Corestar.Sepprover.lift_inner_form formula) spec false in
  begin match posts with
    | None -> (* Couldn't find any frames *) None 
    | Some posts -> Some (List.map (fun post -> 
      let post = Corestar.Sepprover.inner_form_af_to_form post in
      Format.fprintf (Format.std_formatter) "%a  \n" Corestar.Sepprover.string_inner_form post; Format.pp_print_flush(Format.std_formatter)();
      let pf = Corestar.Sepprover.convert_back post in
      Format.fprintf (Format.std_formatter) "After convert back %a \n" Corestar.Psyntax.string_form pf; Format.pp_print_flush(Format.std_formatter)();
      ) posts)
  end;
  assert_bool "testing" true
 
let test_apply_spec1 () =
  let formula = Heaplet (Le_PVar "x", Le_Literal (String "f"), Le_Literal (Num 1.0)) in
  let y = mk_assign "y" (Lookup (Var "x", (Literal (String "f")))) in
  let cmd_pre, cmd_post = Pulp_Logic_Rules.small_axiom_basic_stmt (Assignment y) in
  
  let expected_post = [Star [
    Eq (Le_Literal (Num 1.0), Le_PVar "y");
    Heaplet (Le_PVar "x", Le_Literal (String "f"), Le_PVar "y")
  ]] in
  test_apply_spec_template formula cmd_pre cmd_post expected_post
  
 
let make_and_print_cfg f fs path =
  let all_functions = AllFunctions.add f.func_name f fs in
  let cfg = fb_to_cfg f in
  let all_cfgs = AllFunctions.add f.func_name cfg AllFunctions.empty in
  print_cfg all_cfgs path;
  cfg, all_functions

let test_program_template f fs spec = 
  Config.apply_config ();
  CoreStar_Frontend_Pulp.initialize ();
  let path = "tests/dot/" ^ f.func_name; in
  let cfg, all_functions = make_and_print_cfg f fs path in 
  
  let sg, cmd_st_tbl = execute f cfg all_functions spec in
  let posts, throw_posts = get_posts f cfg sg cmd_st_tbl in
  
  State_Graph.print_state_graph sg cfg f.func_name path;
  
   assert_bool ("Symbolic Execution. Postcondition. 
     Expected :" ^ (String.concat "\n" (List.map string_of_formula spec.spec_post)) ^ "Excep" ^  (String.concat "\n" (List.map string_of_formula spec.spec_excep_post)) ^
   " Actual: " ^ (String.concat "\n" (List.map string_of_formula posts)) ^ "Excep" ^ (String.concat "\n Posts" (List.map string_of_formula throw_posts))) 
     ((List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) spec.spec_post) posts)
     && (List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) spec.spec_excep_post) throw_posts))

let test_empty_program () =
  let ctx = create_ctx [] in
  let p = [
      Basic Skip;       
      Goto ctx.label_return; 
      Label ctx.label_throw;
      Label ctx.label_return
  ] in
  let spec = mk_spec empty_f [empty_f] in
  let f = make_function_block_with_spec "fid1" p [] ctx [spec] in
  test_program_template f AllFunctions.empty spec
  
let test_empty_program_non_empty_pre () =
  let ctx = create_ctx [] in
  let p = [
      Basic Skip;       
      Goto ctx.label_return; 
      Label ctx.label_throw;
      Label ctx.label_return
  ] in
  let formula = Heaplet (Le_Var (fresh_a ()), Le_Var (fresh_a ()), Le_Var (fresh_a ())) in
  let spec = mk_spec formula [formula] in
  let f = make_function_block_with_spec "fid2" p [] ctx [spec] in
  test_program_template f  AllFunctions.empty spec
  
  let test_program1 () =
  let ctx = create_ctx [] in
  let x = mk_assign "x" Obj in
  let y = mk_assign "y" (Lookup (Var x.assign_left, (Literal (String "f")))) in
  let p = [
      Basic (Assignment x);    
      Basic (Mutation ((mk_mutation (Var x.assign_left) (Literal (String "f")) (Literal (Num 1.0)))));  
      Basic (Assignment y); 
      Goto ctx.label_return; 
      Label ctx.label_throw;
      Label ctx.label_return
  ] in
  let post = [Star [
    Eq (Le_PVar "y", Le_Literal (Num 1.0));
    ObjFootprint (Le_PVar "x", [Le_Literal (String "f")]);
    Heaplet (Le_PVar "x", Le_Literal (String "f"), Le_Literal (Num 1.0))
  ]] in 
  let spec = mk_spec empty_f post in
  let f = make_function_block_with_spec "fid3" p [] ctx [spec] in
  test_program_template f  AllFunctions.empty spec
  
let translate_jstools_example_person () =
  let ctx = create_ctx [] in
  let person0_scope = mk_assign "Person0_scope" Obj in
  let label_true = "label_true" in
  let label_false1 = "label_false1" in
  let label_false2 = "label_false2" in
  let label_false3 = "label_false3" in
  let label_false4 = "label_false4" in
  let label_false5 = "label_false5" in
  let p = [
      Basic (Assignment person0_scope);    
      Basic (Mutation ((mk_mutation (Var person0_scope.assign_left) (Literal (String "name")) (Var "name"))));  
      (*GuardedGoto (is_prim_value "rthis", label_true, label_false);*)
      GuardedGoto ((type_of_var "rthis" UndefinedType), label_true, label_false1);
      Label label_false1;     
      GuardedGoto ((type_of_var "rthis" NullType), label_true, label_false2);
      Label label_false2;  
      GuardedGoto ((type_of_var "rthis" BooleanType), label_true, label_false3);
      Label label_false3; 
      GuardedGoto ((type_of_var "rthis" StringType), label_true, label_false4);
      Label label_false4; 
      GuardedGoto ((type_of_var "rthis" NumberType), label_true, label_false5);
      Label label_false5; 
      Basic (Mutation ((mk_mutation (Var "rthis") (Literal (String "name")) (Var "name"))));  
      Basic (Assignment (mk_assign ctx.return_var (Expression (Literal Empty))));
      Goto ctx.label_return;
      Label label_true; ] 
   @  translate_error_throw Ltep ctx.throw_var ctx.label_throw 
   @ [
      Label ctx.label_throw;
      Label ctx.label_return
  ] in 
  let spec = mk_spec empty_f [] in
  let f = make_function_block_with_spec "Person0" p ["rthis"; "rscope"; "name"] ctx [spec] in
  f
 
let test_jstools_example_person_1 () =
  let p = translate_jstools_example_person () in
  let pre = Heaplet (Le_PVar "rthis", Le_Literal (String "name"), Le_Var (fresh_a())) in
  let spec = mk_spec_with_excep pre [Heaplet (Le_PVar "rthis", Le_Literal (String "name"), Le_PVar "name")] [] in
  test_program_template p  AllFunctions.empty spec
  
let get_excep_post throw_var = 
  let excep = fresh_e() in
  Star [
    Eq (Le_PVar throw_var, Le_Var excep);
    Heaplet (Le_Var excep, Le_Literal (String "#class"), Le_Literal (String "Error"));
    Heaplet (Le_Var excep, Le_Literal (String "#proto"), Le_Literal (LLoc Ltep));
  ]
  
let test_jstools_example_person_2 () =
  let p = translate_jstools_example_person () in
  let pre = Eq (Le_Literal (Type UndefinedType), Le_TypeOf (Le_PVar "rthis")) in
  let spec = mk_spec_with_excep pre [] [get_excep_post p.func_ctx.throw_var] in
  test_program_template p  AllFunctions.empty spec

  
let test_function_call_template fid_stmts fid_expr =
  let ctx = create_ctx [] in
  let with_label = "label_call_throw" in
  let x = mk_assign "x" (Call (mk_call fid_expr (Var "scope") (Literal Undefined) [] with_label))  in
  let p = fid_stmts @
  [  
      Basic (Assignment (x));
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var x.assign_left))));  
      Goto ctx.label_return;
      Label with_label;
      Goto ctx.label_throw;
      Label ctx.label_throw;
      Label ctx.label_return
  ] in
  let spec = mk_spec empty_f [] in
  let fid1 = make_function_block_with_spec "fid1" p ["rthis"; "rscope"] ctx [spec] in
  let spec = mk_spec_with_excep empty_f [false_f] [REq (Le_Literal (Bool false))] in
  
  let spec_f = mk_spec_with_excep (Eq (Le_PVar "rthis", Le_Literal Undefined)) [false_f] 
    [Star [Eq (Le_PVar "rthis", Le_Literal Undefined); REq (Le_Literal (Bool false))]] in
  let f = make_function_block_with_spec "f" p ["rthis"; "rscope"] ctx [spec_f] in
  
  let fs = AllFunctions.add f.func_name f AllFunctions.empty in
  
  test_program_template fid1 fs spec
  
let test_function_call () =
  let name = mk_assign "name" (Expression (Literal (String "f"))) in
  test_function_call_template [Basic (Assignment name)] (Var name.assign_left)

let test_function_call_fid_string () =
  test_function_call_template [] (Literal (String "f"))
   
let suite = "Testing_Sym_Exec" >:::
  [ "test_function_call_name" >:: test_function_call_name;
    "test_jsr" >:: test_apply_spec1;
    "running program1" >:: test_empty_program;
   "test_empty_program_non_empty_pre" >:: test_empty_program_non_empty_pre;
   "sym exec program1" >:: test_program1;
   "test_jstools_example_person_1" >:: test_jstools_example_person_1;
   "test_jstools_example_person_2" >:: test_jstools_example_person_2;
    "test_function_call" >:: test_function_call;
    "test_function_call_fid_string" >:: test_function_call_fid_string;
    ]