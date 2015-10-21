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
open Pulp_Translate_Aux
open Tests_Utils

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

let get_pexp js_program =
  apply_config ();
  let exp = Parser_main.exp_from_string js_program in
  let p_exp = exp_to_pulp_no_builtin IVL_goto_unfold_functions exp "main" [] in
  let p_exp = Simp_Main.simplify p_exp in
  p_exp

let test_program_template name f fs = 
  apply_config ();
  List.iteri (fun i s -> check_single_spec name f fs s i) f.func_spec
  
let test_js_program_template name f fs =
  List.iteri (fun i s -> check_single_spec name f fs s i) f.func_spec

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
  test_program_template "test_empty_program" f (AllFunctions.add f.func_name f AllFunctions.empty)
  
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
  test_program_template "test_empty_program_non_empty_pre" f (AllFunctions.add f.func_name f AllFunctions.empty)
  
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
  test_program_template "test_program1" f  (AllFunctions.add f.func_name f AllFunctions.empty)
  
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
      GuardedGoto ((type_of_exp (Var "rthis") UndefinedType), label_true, label_false1);
      Label label_false1;     
      GuardedGoto ((type_of_exp (Var "rthis") NullType), label_true, label_false2);
      Label label_false2;  
      GuardedGoto ((type_of_exp (Var "rthis") BooleanType), label_true, label_false3);
      Label label_false3; 
      GuardedGoto ((type_of_exp (Var "rthis") StringType), label_true, label_false4);
      Label label_false4; 
      GuardedGoto ((type_of_exp (Var "rthis") NumberType), label_true, label_false5);
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
  let f = make_function_block "Person0" p ["rthis"; "rscope"; "name"] ctx  in
  f
 
let test_jstools_example_person_1 () =
  let p = translate_jstools_example_person () in
  let pre = Heaplet (Le_PVar "rthis", Le_Literal (String "name"), Le_Var (fresh_a())) in
  let spec = mk_spec_with_excep pre [Heaplet (Le_PVar "rthis", Le_Literal (String "name"), Le_PVar "name")] [] in
  let p = {p with func_spec = [spec]} in
  test_program_template "test_jstools_example_person_1" p (AllFunctions.add p.func_name p AllFunctions.empty)
  
let get_excep_post throw_var = 
  let excep = fresh_e() in
  Star [
    REq (Le_Var excep);
    Heaplet (Le_Var excep, Le_Literal (String "#class"), Le_Literal (String "Error"));
    Heaplet (Le_Var excep, Le_Literal (String "#proto"), Le_Literal (LLoc Ltep));
  ]
  
let test_jstools_example_person_2 () =
  let p = translate_jstools_example_person () in
  let pre = Eq (Le_Literal (Type UndefinedType), Le_TypeOf (Le_PVar "rthis")) in
  let spec = mk_spec_with_excep pre [] [get_excep_post p.func_ctx.throw_var] in
  let p = {p with func_spec = [spec]} in
  test_program_template "test_jstools_example_person_2" p (AllFunctions.add p.func_name p AllFunctions.empty)

  
let test_function_call_template name fid_stmts fid_expr =
  let ctx = create_ctx [] in
  let with_label = "label_call_throw" in
  let x = mk_assign "x" (Call (mk_call fid_expr (Var "scope") (Literal Undefined) [] with_label))  in
  let p = fid_stmts @
  [  
      Basic (Assignment x);
      Basic (Assignment (mk_assign ctx.return_var (Expression (Var x.assign_left))));  
      Goto ctx.label_return;
      Label with_label;
      Basic (Assignment (mk_assign ctx.throw_var (Expression (Var x.assign_left)))); 
      Goto ctx.label_throw;
      Label ctx.label_throw;
      Label ctx.label_return
  ] in
  
  let spec = mk_spec_with_excep empty_f [false_f] [REq (Le_Literal (Bool false))] in
  let fid = make_function_block_with_spec "fid" p ["rthis"; "rscope"] ctx [spec] in
  
  let spec_f = mk_spec_with_excep (Eq (Le_PVar "rthis", Le_Literal Undefined)) [false_f] 
    [Star [Eq (Le_PVar "rthis", Le_Literal Undefined); REq (Le_Literal (Bool false))]] in
  let f = make_function_block_with_spec "f" p ["rthis"; "rscope"] ctx [spec_f] in
  
  let fs = AllFunctions.add f.func_name f AllFunctions.empty in
  let fs = AllFunctions.add "fid" fid fs in
  
  test_program_template name fid fs
  
let test_function_call () =
  let name = mk_assign "name" (Expression (Literal (String "f"))) in
  test_function_call_template "test_function_call" [Basic (Assignment name)] (Var name.assign_left)

let test_function_call_fid_string () =
  apply_config ();
  test_function_call_template "test_function_call_fid_string" [] (Literal (String "f"))
  
let test_proto_field () =
  let ctx = create_ctx [] in
  let x = mk_assign "x" Obj  in
  let proto = mk_assign "proto" Obj in
  let p = 
  [  
      Basic (Assignment x);
      Basic (Assignment proto);
      add_proto x.assign_left (Var proto.assign_left);
      Basic (Mutation ((mk_mutation (Var proto.assign_left) (Literal (String "a")) (Literal (Num 4.0)))));  
      Basic (Assignment (mk_assign ctx.return_var (ProtoF (Var x.assign_left, (Literal (String "a"))))));  
      Goto ctx.label_return;
      Label ctx.label_throw;
      Label ctx.label_return
  ] in
  
  let spec = mk_spec empty_f [REq (Le_Literal (Num 4.0))] in
  let f = make_function_block_with_spec "f_proto_field" p ["rthis"; "rscope"] ctx [spec] in
  test_program_template "test_proto_field" f (AllFunctions.add f.func_name f AllFunctions.empty)
  
let test_proto_field_direct () =
  let ctx = create_ctx [] in
  let x = mk_assign "x" Obj  in
  let p = 
  [  
      Basic (Assignment x);
      Basic (Mutation ((mk_mutation (Var x.assign_left) (Literal (String "a")) (Literal Undefined))));  
      Basic (Assignment (mk_assign ctx.return_var (ProtoF (Var x.assign_left, (Literal (String "a"))))));  
      Goto ctx.label_return;
      Label ctx.label_throw;
      Label ctx.label_return
  ] in
  let spec = mk_spec empty_f [REq (Le_Literal Undefined)] in
  let f = make_function_block_with_spec "f_proto_field" p ["rthis"; "rscope"] ctx [spec] in
  
  test_program_template "test_proto_field_direct" f (AllFunctions.add f.func_name f AllFunctions.empty)
  
let test_proto_field_empty () =
  let ctx = create_ctx [] in
  let x = mk_assign "x" Obj  in
  let p = 
  [  
      Basic (Assignment x);
      add_proto x.assign_left (Literal Null);
      Basic (Assignment (mk_assign ctx.return_var (ProtoF (Var x.assign_left, (Literal (String "a"))))));  
      Goto ctx.label_return;
      Label ctx.label_throw;
      Label ctx.label_return
  ] in
  let spec = mk_spec empty_f [REq (Le_Literal Empty)] in
  let f = make_function_block_with_spec "f_proto_field" p ["rthis"; "rscope"] ctx [spec] in
  
  test_program_template "test_proto_field_empty" f (AllFunctions.add f.func_name f AllFunctions.empty)
  
let test_proto_field_last () =
  let ctx = create_ctx [] in
  let x = mk_assign "x" Obj  in
  let p = 
  [  
      Basic (Assignment x);
      add_proto x.assign_left (Literal Null);
      Basic (Mutation ((mk_mutation (Var x.assign_left) (Literal (String "a")) (Literal (Num 3.0)))));  
      Basic (Assignment (mk_assign ctx.return_var (ProtoF (Var x.assign_left, (Literal (String "a"))))));  
      Goto ctx.label_return;
      Label ctx.label_throw;
      Label ctx.label_return
  ] in
  let spec = mk_spec empty_f [REq (Le_Literal (Num 3.0))] in
  let f = make_function_block_with_spec "f_proto_field" p ["rthis"; "rscope"] ctx [spec] in
  
  test_program_template "test_proto_field_empty" f (AllFunctions.add f.func_name f AllFunctions.empty)
  
let test_proto_field_with_proto_in_spec () =
  let ctx = create_ctx [] in
  let ls = Le_Var (fresh_e()) in
  let l' = Le_Var (fresh_e()) in
  let pi = Pi (mk_pi_pred ls (Le_PVar "x") (Le_Literal (String "a")) l' (Le_Literal (Num 3.0))) in
  let p = 
  [   
      Basic (Assignment (mk_assign ctx.return_var (ProtoF (Var "x", (Literal (String "a"))))));  
      Goto ctx.label_return;
      Label ctx.label_throw;
      Label ctx.label_return
  ] in
  let spec = mk_spec (Star [pi; ProtoChain (Le_PVar "x", ls, l')]) [REq (Le_Literal (Num 3.0))] in
  let f = make_function_block_with_spec "f_proto_field" p ["rthis"; "rscope"] ctx [spec] in
  
  test_program_template "test_proto_field_in_spec" f (AllFunctions.add f.func_name f AllFunctions.empty)
 
(* Different part of prototype chain *)   
let test_proto_field_with_two_proto_in_spec () =
  let ctx = create_ctx [] in
  let ls = Le_Var (fresh_e()) in
  let l' = Le_Var (fresh_e()) in
  let xa = mk_assign_fresh (ProtoF (Var "x", (Literal (String "a")))) in
  let xb = mk_assign_fresh (ProtoF (Var "x", (Literal (String "b")))) in
  let pix = Pi (mk_pi_pred ls (Le_PVar "x") (Le_Literal (String "a")) l' (Le_Literal (Num 3.0))) in
  let piy = Pi (mk_pi_pred ls (Le_PVar "x") (Le_Literal (String "b")) l' (Le_Literal (Num 2.0))) in
  let p = 
  [   
      Basic (Assignment xa);
      Basic (Assignment xb);
      Basic (Assignment (mk_assign ctx.return_var (Expression (BinOp (Var xa.assign_left, Arith Plus, Var xb.assign_left)))));  
      Goto ctx.label_return;
      Label ctx.label_throw;
      Label ctx.label_return
  ] in
  let spec = mk_spec (Star [pix; piy; ProtoChain (Le_PVar "x", ls, l')]) [REq (Le_Literal (Num 5.0))] in
  let f = make_function_block_with_spec "f_proto_field" p ["rthis"; "rscope"] ctx [spec] in
  
  test_program_template "test_two_proto_field_in_spec" f (AllFunctions.add f.func_name f AllFunctions.empty)

let test_js_program_cav_example () =
  let js_program = "
    function Person (name) {
       this.name = name;
    }

    Person.prototype.sayHi = function () {
      return 'Hi ' + this.name
    }

    var alice = new Person ('Alice');
    alice.sayHi()" in
    
  let p_exp = get_pexp js_program in
  
  (* TODO spec parsing *)

  let p_exp = AllFunctions.mapi (fun id fb ->
    match id with
      | "main" -> 
        let person = Le_Var (fresh_e()) in
        let alice = Le_Var (fresh_e()) in
        let proto = Le_Var (fresh_e()) in
        let undefined = Le_Var (fresh_e()) in
        let pre = Star [
          Heaplet (Le_Literal (LLoc Lg), Le_Literal (String "#proto"), proto);
          Heaplet (Le_Literal (LLoc Lg), Le_Literal (String "undefined"), undefined);
          Heaplet (Le_Literal (LLoc Lg), Le_Literal (String "Person"), person);
          Heaplet (Le_Literal (LLoc Lg), Le_Literal (String "alice"), alice);
        ] in
        let spec_main = mk_spec pre [REq (Le_Literal (String "Hi Alice"))] in
        {fb with func_spec = [spec_main]}
      | "anonymous1" -> 
        let v = Le_Var (fresh_a()) in
        let pre = Star [
          Heaplet (Le_PVar "rscope", Le_Literal (String "main"), Le_Literal (LLoc Lg));
          Heaplet (Le_PVar "rthis", Le_Literal (String "name"), v);
          Eq (Le_TypeOf (v), Le_Literal (Type StringType));
        ] in
        let spec_anonymous0 = mk_spec pre [Star [pre; REq (Le_BinOp (Le_Literal (String "Hi "), Concat, v))]] in
			    {fb with func_spec = [spec_anonymous0]}
      | "Person0" ->
        let v = Le_Var (fresh_a()) in
        let pre = Star [
          Heaplet (Le_PVar "rscope", Le_Literal (String "main"), Le_Literal (LLoc Lg));
          Heaplet (Le_PVar "rthis", Le_Literal (String "name"), v)
        ] in
        let post = Star [Heaplet (Le_PVar "rthis", Le_Literal (String "name"), Le_PVar "name"); REq (Le_Literal Undefined)] in
        let spec_person0 = mk_spec pre [post] in
          {fb with func_spec = [spec_person0]}
      | _ -> fb
  ) p_exp in
  
  Printf.printf "Specs %s" (String.concat "\n" (List.map (fun (id, fb) -> Printf.sprintf "%s : %s" id (Pulp_Logic_Print.string_of_spec_pre_post_list fb.func_spec "\n")) (AllFunctions.bindings p_exp)));
  
  AllFunctions.iter (fun id f -> test_js_program_template "test_js_program_cav_example" f p_exp) p_exp
    
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
    "test_proto_field" >:: test_proto_field;
    "test_proto_field_direct" >:: test_proto_field_direct;
    "test_proto_field_empty" >:: test_proto_field_empty;
    "test_proto_field_last" >:: test_proto_field_last;
    "test_proto_field_with_proto_in_spec" >:: test_proto_field_with_proto_in_spec;
    "test_proto_field_with_two_proto_in_spec" >:: test_proto_field_with_two_proto_in_spec;
    "test_js_program_cav_example" >:: test_js_program_cav_example
    ]