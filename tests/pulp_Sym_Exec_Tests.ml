open OUnit
open Pulp_Logic
open Pulp_Syntax
open Pulp_Sym_Exec
open Pulp_Procedure
open Control_Flow
open Pulp_Logic_Print
open Pulp_Logic_Utils
open CoreStar_Frontend_Pulp

let test_apply_spec_template formula cmd_pre cmd_post expected_post =
  Config.apply_config ();
  CoreStar_Frontend_Pulp.initialize ();
  let posts = CoreStar_Frontend_Pulp.apply_spec formula cmd_pre cmd_post in
  match posts with
    | Some posts -> assert_bool ("Symbolic Execution. Postcondition. 
       Expected :" ^ (String.concat "\n" (List.map string_of_formula expected_post)) ^ 
       " Actual: " ^ (String.concat "\n" (List.map string_of_formula posts))) 
       (List.map simplify posts=List.map simplify expected_post)
    | _ -> assert_failure "Postcondition not found."

let test_function_call_name () =
  Config.apply_config ();
  CoreStar_Frontend_Pulp.initialize ();
  let e = Corestar.Vars.freshe_str "lv" in
  let x = Corestar.Vars.freshp_str "x" in
  let z = Corestar.Vars.freshp_str "z" in
  let y = Corestar.Vars.freshe_str "lv" in
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
    NEq (Le_Literal (Num 1.0), Le_None);
    Heaplet (Le_PVar "x", Le_Literal (String "f"), Le_PVar "y")
  ]] in
  test_apply_spec_template formula cmd_pre cmd_post expected_post
  

let test_program_template f spec = 
  Config.apply_config ();
  CoreStar_Frontend_Pulp.initialize ();
  let all_functions = AllFunctions.add f.func_name f AllFunctions.empty in
  let cfg = fb_to_cfg f in
  let all_cfgs = AllFunctions.add f.func_name cfg AllFunctions.empty in
  print_cfg all_cfgs ("/Users/daiva/Documents/workspace/JS_Symbolic_Debugger/JS_Symbolic_Debugger/tests/dot/fid1");
  
  let sg, cmd_st_tbl = execute f cfg all_functions spec in
  let posts = get_posts f cfg sg cmd_st_tbl in
  
   assert_bool ("Symbolic Execution. Postcondition. 
     Expected :" ^ (String.concat "\n" (List.map string_of_formula spec.spec_post)) ^ 
   " Actual: " ^ (String.concat "\n" (List.map string_of_formula posts))) 
     (List.for_all (fun post -> CoreStar_Frontend_Pulp.implies_or_list (simplify post) spec.spec_post) posts)

let test_empty_program () =
  let ctx = create_ctx [] in
  let p = [
      Basic Skip;       
      Goto ctx.label_return; 
      Label ctx.label_return
  ] in
  let spec = mk_spec empty_f [empty_f] in
  let f = make_function_block_with_spec "fid1" p [] ctx [spec] in
  test_program_template f spec
  
let test_empty_program_non_empty_pre () =
  let ctx = create_ctx [] in
  let p = [
      Basic Skip;       
      Goto ctx.label_return; 
      Label ctx.label_return
  ] in
  let formula = Heaplet (Le_Var (fresh_a ()), Le_Var (fresh_a ()), Le_Var (fresh_a ())) in
  let spec = mk_spec formula [formula] in
  let f = make_function_block_with_spec "fid1" p [] ctx [spec] in
  test_program_template f spec
  
  let test_program1 () =
  let ctx = create_ctx [] in
  let x = mk_assign "x" Obj in
  let y = mk_assign "y" (Lookup (Var x.assign_left, (Literal (String "f")))) in
  let p = [
      Basic (Assignment x);    
      Basic (Mutation ((mk_mutation (Var x.assign_left) (Literal (String "f")) (Literal (Num 1.0)))));  
      Basic (Assignment y); 
      Goto ctx.label_return; 
      Label ctx.label_return
  ] in
  let post = [Star [
    Eq (Le_PVar "y", Le_Literal (Num 1.0));
    ObjFootprint (Le_PVar "x", [Le_Literal (String "f")]);
    Heaplet (Le_PVar "x", Le_Literal (String "f"), Le_Literal (Num 1.0))
  ]] in 
  let spec = mk_spec empty_f post in
  let f = make_function_block_with_spec "fid1" p [] ctx [spec] in
  test_program_template f spec
   
let suite = "Testing_Sym_Exec" >:::
  [ "test_function_call_name" >:: test_function_call_name;
    "test_jsr" >:: test_apply_spec1;
    "running program1" >:: test_empty_program;
   "test_empty_program_non_empty_pre" >:: test_empty_program_non_empty_pre;
   "sym exec program1" >:: test_program1]