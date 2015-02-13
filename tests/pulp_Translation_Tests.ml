open OUnit
open Pulp_Syntax
open Pulp_Translate
open Pulp_Syntax_Utils
open Control_Flow
open Reaching_Defs

let test_template p name =
  Symb_execution.initialize ();
  Parser_main.verbose := true;
  let exp = Parser_main.exp_from_string p in
  let _ = Printf.printf "%s \n" (Pretty_print.string_of_exp_syntax exp.Parser_syntax.exp_stx) in
  let p_exp = exp_to_pulp IVL_goto exp main_fun_id in
  let _ = AllFunctions.iter (fun fid fwc -> Printf.printf "%s \n\n" (Pulp_Syntax_Print.string_of_func_block fwc)) p_exp in
  (* TODO fix path *)
  let cfg = Control_Flow.mk_cfg p_exp ("/Users/daiva/Documents/workspace/JS_Symbolic_Debugger/JS_Symbolic_Debugger/tests/dot/"^name) in
  
  let cfg_bbs = AllFunctions.mapi (fun name cfg ->
    let fb = AllFunctions.find name p_exp in
    let cfg_bb = Simp_Main.basic_block_simplifications cfg fb.func_ctx in
    let stmts = Basic_Blocks.cfg_to_fb cfg_bb fb.func_ctx.label_throw fb.func_ctx.label_return in
    Printf.printf "Procedure %s \n %s \n" name (Pulp_Syntax_Print.string_of_statement_list stmts);
    cfg_bb
    ) cfg in
  
  Basic_Blocks.print_cfg_bb cfg_bbs ("/Users/daiva/Documents/workspace/JS_Symbolic_Debugger/JS_Symbolic_Debugger/tests/dot/bb/"^name);
  
  (*Reaching_Defs.debug_print_cfg_bb_with_defs cfg_bbs ("/Users/daiva/Documents/workspace/JS_Symbolic_Debugger/JS_Symbolic_Debugger/tests/dot/rd/cp/"^name);*)
  
  (* TODO clean up *)
  let cfg_bbs = AllFunctions.mapi (fun name cfg ->
    
      let fb = AllFunctions.find name p_exp in
      Simp_Main.constant_propagation cfg fb;
      Simp_Main.constant_propagation cfg fb;
        
      dead_code_elimination cfg fb.func_ctx.throw_var fb.func_ctx.return_var;
      
      let stmts = Basic_Blocks.cfg_to_fb cfg fb.func_ctx.label_throw fb.func_ctx.label_return in
      Printf.printf "Procedure %s \n %s \n" name (Pulp_Syntax_Print.string_of_statement_list stmts);
      
      cfg
  ) cfg_bbs in
    
  let _ = Basic_Blocks.print_cfg_bb cfg_bbs ("/Users/daiva/Documents/workspace/JS_Symbolic_Debugger/JS_Symbolic_Debugger/tests/dot/bb/bbsimp/"^name) in

  
  assert_bool "Incorrect Translation" true 
  
let test_simple () = 
  test_template ("var x = 1; x") "simple"  

let test_access () = 
  test_template ("x.y") "access"
  
let test_assign () =
  test_template ("x = y") "assign"
  
let test_obj () =
  test_template ("obj = {x : 1, y : null, z : false}") "obj"
  
let test_block () =
  test_template ("x = y; y = z") "block"
  
let test_fun_env () =
  Symb_execution.initialize ();
  Parser_main.verbose := true;
  let exp = Parser_main.exp_from_string "var x = 1; var f = function (g) {var z = 1; var c = function (d) {}}; var g = function z () {var x, a, b; }" in
  let _ = Printf.printf "%s \n" (Pretty_print.string_of_exp_syntax exp.Parser_syntax.exp_stx) in
  let exp = add_codenames main_fun_id exp in
  let _ = Printf.printf "Added codenames %s \n" (Pretty_print.string_of_exp true exp) in
  let all_functions = get_all_functions_with_env_in_fb [] exp in
  let _ = List.iter (fun (fexp, fnamed, fenv) -> 
  let fid = get_codename fexp in
  Printf.printf "Function id %s \n Function expression %s \n\n Function environment %s \n\n\n\n" 
     fid
     (Pretty_print.string_of_exp true fexp)
     (String.concat ";" (List.map Pulp_Syntax_Print.string_of_ctx_vars fenv)))
  all_functions in
  assert_bool "Incorrect Translation" true
  
let test_var_decl () = 
  test_template ("var x,y = 5; x.y") "vardecl"
  
let test_fun_def () =
  test_template ("var x = 1; var f = function (g) {var z = 1; x = 3; g = 4; var c = function (d) {}}; var g = function () {var x, a, b; }") "fundef"
  
let test_call () =
  test_template ("f (4, true)") "call"
  
let test_new () =
  test_template ("new f (1, \"a\")") "new"
  
let test_caccess () =
  test_template ("x[y]") "access"
  
let test_delete () =
  test_template ("delete x") "delete"
  
let test_bin_op_regular () =
  test_template ("y + z") "binopreg"
  
let test_bin_op_and () =
  test_template ("y && z") "binopand"
  
let test_bin_op_or () =
  test_template ("y || z") "binopor"
  
let test_if () =
  test_template ("if (x == true) {x = 1} else {x = 2; y = 2}") "if"
  
let test_if_no_else () =
  test_template ("if (x == true) {x = 1}") "ifnoelse"
  
let test_while () =
  test_template ("while (x == 5) {x = x - 1; z = z + 1}") "while"
  
let test_return () =
  test_template ("var f = function () {return}") "return"
  
let test_return_exp () =
  test_template ("var f = function () {var x; return x}") "returnexp"
  
let test_same_name_param_var () =
  test_template ("var f = function (b) {var b}") "samevar"
  
let test_popl12_example () =
  test_template ("var x = null, y = null, z = null; var f = function(w){x = v; v = 4; var v; y = v;}; v = 5; f(null); z = v;") "popl12"
  
let test_small_example () =
  test_template ("var x = {}; var f = function(field, value){x[field] = value}; f(\"a\", 1);") "small example"
  
let test_smaller_example () =
  test_template ("var x = {}; x.a = 1; x.b = 2") "smaller example"
  
let test_example () =
  test_template ("var s = function (n) { 
   var t = function (m) { 
      return {x : n} 
    }; 
   var d = t(n); 
   return d 
}; 

var r = s(3).x") "example"

 let test_eval_1 () =
   test_template ("eval ('1')") "eval"

let test_gamma () =
  let ctx = create_ctx [] in
  let gamma_stmts, r = translate_gamma "r" ctx in
  let gamma_stmts = to_ivl_goto gamma_stmts in
  let cfg = Cfg.fun_to_cfg (make_function_block "gamma" gamma_stmts [] ctx) in
  let cfgs = AllFunctions.add "gamma_id" cfg AllFunctions.empty in
  let _ = Cfg.print_cfg cfgs ("/Users/daiva/Documents/workspace/JS_Symbolic_Debugger/JS_Symbolic_Debugger/tests/dot/gamma") in
  assert_bool "Incorrect Translation" true

 (*"var s = function (v) { var t = function () { var a = {x : v}; return a }; var b = t (v); return b }; var r = s(3).x"*)

let cfg_anonymous2 () =
  let ctx = create_ctx [] in
  let proto_stmt = add_proto_null "anonymous2_scope" in
  let stmts = 
    [
	    Basic (Assignment (mk_assign ("anonymous1_scope") (Expression (Ref (Var "rscope", Literal (String "anonymous1"), MemberReference)))));
	    Basic (Assignment (mk_assign "anonymous2_scope" Obj));
      proto_stmt;
      Basic (Assignment (mk_assign "r1" Obj));
      add_proto_value "r1" Lop;
      Basic (Assignment (mk_assign "r2" (Lookup (Var "anonymous2_scope", Literal (String "n")))));
      Basic (Mutation (mk_mutation (Var "r1") (Literal (String "x")) (Var "r2")));
      Goto ctx.label_return
    ]
    in
  let stmts = to_ivl_goto stmts in
  let cfg = Cfg.fun_to_cfg (make_function_block "anonymous2" stmts [] ctx) in
  let cfgs = AllFunctions.add "anonymous2" cfg AllFunctions.empty in
  let _ = Cfg.print_cfg cfgs ("/Users/daiva/Documents/workspace/JS_Symbolic_Debugger/JS_Symbolic_Debugger/tests/dot/anonymous") in
  assert_bool "Incorrect Translation" true
  (* 
   anonymous1_scope := (rscope ._o "anonymous1")
   
   anonymous2_scope := new ()
   [anonymous2_scope."#proto"] := "#null"
  
   r4081 := new ()
   [r4081."#proto"] := "#ObjectPrototype"       
   r4084 := [anonymous1_scope."n"]
   [r4081."x"] := r4084    
   goto return.r4075
  
  *)
  
let test_invest_example () =
  test_template ("var r = 'To Store The Result';

var person = {
 name: 'David',
 sayHi: function() {
  return 'Hello ' + this.name;
 }
};

r = person.sayHi();") "invest example"

let test_cav_example_1 () =
  test_template ("var object = {
 property: 'some property',
 method: function() {
   return this.property;
 }
};

object.method()") "CAV example 1"

let test_cav_example_2 () =
  test_template ("var object = {
 property: 'some property',
 method: function() {
   return this.property;
 }
};

var f = object.method;
f() ") "CAV example 2"

let test_cav_example_3 () =
  test_template ("var MyObject = function(p) {
    this.property = p;
    this.method = function() {
      return this.property;
    }
};

var obj = new MyObject('some property');
obj.method();") "CAV example 3"

let test_cav_example_4 () =
  test_template ("var MyObject = function(p) {
    this.property = p;
    this.method = function() {
      return this.property;
    }
};

var obj = new MyObject('some property');
var f = obj.method;
f()") "CAV example 4"

let test_cav_example_5 () =
  test_template ("
  var prop = 'global';
var obj = {
  prop: 'local',
  m: function() {
    return this.prop === prop;
  }
};
obj.m()") "CAV example 5"

let test_instance_of_true () =
  test_template ("function C(){}; function D(){}; var o = new C(); o instanceof C")
  "intance of true"
  
let test_instance_of_false () =
  test_template ("function C(){}; function D(){}; var o = new C(); o instanceof D")
  "instance of false"

let suite = "Testing_Translation" >:::
  ["translating simple" >:: test_simple;
   "translating access" >:: test_access;
   "translating assignment" >:: test_assign;
   "translating obj literal" >:: test_obj;
   "translating block" >:: test_block;
   "translating function environments" >:: test_fun_env;
   "translating var declarations" >:: test_var_decl;
   "translating function definition" >:: test_fun_def;
   "translating function call" >:: test_call;
   "translating new" >:: test_new;
   "translating computed access" >:: test_caccess;
   "translating delete" >:: test_delete;
   "translating regular binary op" >:: test_bin_op_regular;
   "translating and" >:: test_bin_op_and;
   "translating or" >:: test_bin_op_or; 
   "translating if" >:: test_if;
   "translating if without else" >:: test_if_no_else;
   "translating while" >:: test_while;
   "testing return" >:: test_return;
   "testing return with expression" >:: test_return_exp;
   "testing function that has same name for one of the parameters and variable declaration" >:: test_same_name_param_var;
   "translating popl12 example" >:: test_popl12_example;
   "translating small explample" >:: test_small_example;
   "translating smaller explample" >:: test_smaller_example;
   "test_example" >:: test_example;
   "translating gamma" >:: test_gamma;
   "cfg_anonymous2" >:: cfg_anonymous2;
   "test_invest_example" >:: test_invest_example;
   "test_cav_example_1" >:: test_cav_example_1;
   "test_cav_example_2" >:: test_cav_example_2;
   "test_cav_example_3" >:: test_cav_example_3;
   "test_cav_example_4" >:: test_cav_example_4;
   "test_eval_1">::test_eval_1;
   "test_cav_example_5">::test_cav_example_5;
   "test_instance_of_true" >:: test_instance_of_true;
   "test_instance_of_false" >:: test_instance_of_false] 