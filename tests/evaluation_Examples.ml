open OUnit
open Tests_Utils
open Pulp_Procedure
open Pulp_Logic
open Pulp_Logic_Utils
open Pulp_Syntax

let test_js_program_template name f fs =
  List.iteri (fun i s -> check_single_spec name f fs s i "tests/dot/evaluation/") f.func_spec
  
  
(* ch08/8.7/8.7.2/8.7.2-1-s.js *)  
let test_8_7_2_1_s () =
  (* Simplifying the program to exclude eval for a moment *)
  let js_program = "
    /**
    @toprequires #protoPred(_LS, #ObjectPrototype,'_8_7_2_1', _L, #empty) *
                 #obj[#GlobalObject]('_8_7_2_1'|#proto:_P,'undefined':#undefined) 
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    _8_7_2_1 = 11;" in
  (*  *)  
  let p_exp, p_env = get_pexp js_program in
  
  Printf.printf "Specs %s" (String.concat "\n" (List.map (fun (id, fb) -> Printf.sprintf "%s : %s" id (Pulp_Logic_Print.string_of_spec_pre_post_list fb.func_spec "\n")) (AllFunctions.bindings p_exp)));
  
  AllFunctions.iter (fun id f -> test_js_program_template "test_8_7_2_1_s" f p_exp) p_exp
  
(* ch11/11.1/11.1.2/S11.1.2_A1_T2.js *)  
let test_S11_1_2_A1_T2 () =
  let js_program = "/**
    @toprequires #protoPred(_LS, #ObjectPrototype,'z', _L, #empty) *
                 #obj[#GlobalObject]('z'|#proto:_P,'undefined':#undefined) *
                 rthis = #GlobalObject
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    this.z; z;" in
    
  let p_exp, p_env = get_pexp js_program in
  
  Printf.printf "Specs %s" (String.concat "\n" (List.map (fun (id, fb) -> Printf.sprintf "%s : %s" id (Pulp_Logic_Print.string_of_spec_pre_post_list fb.func_spec "\n")) (AllFunctions.bindings p_exp)));
  
  AllFunctions.iter (fun id f -> test_js_program_template "test_S11_1_2_A1_T2" f p_exp) p_exp
  
 let suite = "Testing_Evaluation_Examples" >:::
  [ "test_8_7_2_1_s" >:: test_8_7_2_1_s;
    "test_S11_1_2_A1_T2" >:: test_S11_1_2_A1_T2 ]