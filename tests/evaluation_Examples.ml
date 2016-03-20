(* ./tests/evaluation_Examples.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open OUnit
open Tests_Utils
open Pulp_Procedure
open Pulp_Logic
open Pulp_Logic_Utils
open Pulp_Syntax

let test_js_program_template name f fs =
  List.iteri (fun i s -> check_single_spec name f fs s i "tests/dot/evaluation/") f.func_spec
  
let test_template js name = 
  let p_exp, p_env = get_pexp js in
  
  Printf.printf "Specs %s" (String.concat "\n" (List.map (fun (id, fb) -> Printf.sprintf "%s : %s" id (Pulp_Logic_Print.string_of_spec_pre_post_list fb.func_spec "\n")) (AllFunctions.bindings p_exp)));
  
  AllFunctions.iter (fun id f -> test_js_program_template name f p_exp) p_exp
  
(* ch08/8.7/8.7.2/8.7.2-1-s.js *)  
let test_8_7_2_1_s () =
  (* Simplifying the program to exclude eval for a moment *)
  let js_program = "
    /**
     @toprequires #protoPred(?LS, ?P,'_8_7_2_1', ?L, ?V) *
                 #obj[#GlobalObject]('_8_7_2_1'| #class:'Object', #proto:?P) 
    @topensures #r = 11 * #obj[#GlobalObject](|'_8_7_2_1': 11, #proto:?P)
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')
    
    @toprequires #obj[#GlobalObject](|'_8_7_2_1':?X, #proto:?P, #class:'Object') * ?X != #(/) * ?X != #empty
    @topensures #r = 11 * #obj[#GlobalObject](|'_8_7_2_1': 11, #proto:?P)
    */
    _8_7_2_1 = 11;" in
  
  test_template js_program "test_8_7_2_1_s" 
  
(* ch11/11.1/11.1.2/S11.1.2_A1_T2.js *)  
let test_S11_1_2_A1_T2 () =
  let js_program = "/**
    @toprequires #protoPred(?LS, ?P,'z', ?L, #empty) *
                 #obj[#GlobalObject]('z'|#proto:?P) *
                 rthis = #GlobalObject
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    this.z; z;" in
    
  test_template js_program "test_S11_1_2_A1_T2"
  
(* ch11/11.10/11.10.1/S11.10.1_A2.1_T2.js *)
let test_S11_10_1_A2_1_T2 () =
  let js_program = "/**
    @toprequires #protoPred(?LS, ?P,'x', ?L, #empty) *
                 #obj[#GlobalObject]('x'|#proto:?P)
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    x & 1;" in
    
  test_template js_program "test_S11_10_1_A2_1_T2"
  
(* ch11/11.10/11.10.1/S11.10.1_A2.1_T3.js *)
let test_S11_10_1_A2_1_T3 () =
  let js_program = "/**
    @toprequires #protoPred(?LS, ?P,'y', ?L, #empty) *
                 #obj[#GlobalObject]('y'|#proto:?P)
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    1 & y;" in
    
  test_template js_program "test_S11_10_1_A2_1_T3"
  
(* ch11/11.10/11.10.2/S11.10.2_A2.1_T2.js *)
let test_S11_10_2_A2_1_T2 () =
  let js_program = "/**
    @toprequires #protoPred(?LS, ?P,'x', ?L, #empty) *
                 #obj[#GlobalObject]('x'|#proto:?P)
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    x ^ 1;" in
    
  test_template js_program "test_S11_10_2_A2_1_T2"
  
(* ch11/11.10/11.10.2/S11.10.2_A2.1_T3.js *)
let test_S11_10_2_A2_1_T3 () =
  let js_program = "/**
    @toprequires #protoPred(?LS, ?P,'y', _L, #empty) *
                 #obj[#GlobalObject]('y'|#proto:?P)
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    1 ^ y;" in
    
  test_template js_program "test_S11_10_2_A2_1_T3"
  
(* ch11/11.10/11.10.3/S11.10.3_A2.1_T2.js *)
let test_S11_10_3_A2_1_T2 () =
  let js_program = "/**
    @toprequires #protoPred(?LS, ?P,'x', ?L, #empty) *
                 #obj[#GlobalObject]('x'|#proto:?P,'undefined':#undefined)
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    x | 1;" in
    
  test_template js_program "test_S11_10_3_A2_1_T2"
  
(* ch11/11.10/11.10.3/S11.10.3_A2.1_T3.js *)
let test_S11_10_3_A2_1_T3 () =
  let js_program = "/**
    @toprequires #protoPred(?LS, ?P,'y', ?L, #empty) *
                 #obj[#GlobalObject]('y'|#proto:?P)
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    1 | y;" in
    
  test_template js_program "test_S11_10_3_A2_1_T3"
  
(* ch11/11.2/11.2.1/S11.2.1_A2.js *)  
let test_S11_2_1_A2_part1 () =
  let js_program = "/**
    @toprequires #protoPred(?LS, ?P,'object', ?L, #empty) *
                 #obj[#GlobalObject]('object'|#proto:?P)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    object[1];" in
    
  test_template js_program "test_S11_2_1_A2_part1"
  
(* ch11/11.2/11.2.1/S11.2.1_A2.js *)  
let test_S11_2_1_A2_part2 () =
  let js_program = "/**
    @toprequires #protoPred(?LS, ?P,'object', ?L, #empty) *
                 #obj[#GlobalObject]('object'|#proto:?P)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    object.prop;" in
    
    test_template js_program "test_S11_2_1_A2_part2"
    
(* ch11/11.2/11.2.1/S11.2.1_A3_T4.js *)  
let test_S11_2_1_A3_T4_part1 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|'undefined':#undefined)
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    undefined.toString();" in
    
    test_template js_program "test_S11_2_1_A3_T4_part1"
    
(* ch11/11.2/11.2.1/S11.2.1_A3_T4.js *)  
let test_S11_2_1_A3_T4_part2 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    undefined['toString']();" in
    
    test_template js_program "test_S11_2_1_A3_T4_part2"
    
(* ch11/11.2/11.2.1/S11.2.1_A3_T5.js *)  
let test_S11_2_1_A3_T5_part1 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    null.toString();" in
    
    test_template js_program "test_S11_2_1_A3_T5_part1"
    
(* ch11/11.2/11.2.1/S11.2.1_A3_T5.js *)  
let test_S11_2_1_A3_T5_part2 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    null['toString']();" in
    
    test_template js_program "test_S11_2_1_A3_T5_part2"
    
(* ch11/11.2/11.2.2/S11.2.2_A2.js *)  
let test_S11_2_2_A2_part1 () =
  let js_program = "/**
    @toprequires  #protoPred(?LS, ?P,'x', ?L, #empty) *
                  #obj[#GlobalObject]('x'|#proto:?P)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    new x;" in
    
    test_template js_program "test_S11_2_2_A2_part1"
    
(* ch11/11.2/11.2.2/S11.2.2_A2.js *)  
let test_S11_2_2_A2_part2 () =
  let js_program = "/**
    @toprequires  #protoPred(?LS, ?P,'x', ?L, #empty) *
                  #obj[#GlobalObject]('x'|#proto:?P)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    new x();" in
    
    test_template js_program "test_S11_2_2_A2_part2"
    
(* ch11/11.2/11.2.2/S11.2.2_A3_T1.js *)  
let test_S11_2_2_A3_T1_part1 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    new true;" in
    
    test_template js_program "test_S11_2_2_A3_T1_part1"
    
(* ch11/11.2/11.2.2/S11.2.2_A3_T1.js *)  
let test_S11_2_2_A3_T1_part2 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#class:'Object','x':?X)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    var x = true;
    new x;" in
    
    test_template js_program "test_S11_2_2_A3_T1_part2"
    
(* ch11/11.2/11.2.2/S11.2.2_A3_T1.js *)  
let test_S11_2_2_A3_T1_part3 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#class:'Object','x':?X)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    var x = true;
    new x();" in
    
    test_template js_program "test_S11_2_2_A3_T1_part3"

(* ch11/11.8/11.8.7/S11.8.7_A3.js *)
let test_S11_8_7_A3_part1 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    'toString' in true;" in
    
    test_template js_program "test_S11_8_7_A3_part1"
    
 (* ch11/11.8/11.8.7/S11.8.7_A3.js *)
let test_S11_8_7_A3_part2 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    'MAX_VALUE' in 1;" in
    
    test_template js_program "test_S11_8_7_A3_part2"
    
 (* ch11/11.8/11.8.7/S11.8.7_A3.js *)
let test_S11_8_7_A3_part3 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    'length' in 'string';" in
    
    test_template js_program "test_S11_8_7_A3_part3"
    
 (* ch11/11.8/11.8.7/S11.8.7_A3.js *)
let test_S11_8_7_A3_part4 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    'toString' in undefined;" in
    
    test_template js_program "test_S11_8_7_A3_part4"
    
 (* ch11/11.8/11.8.7/S11.8.7_A3.js *)
let test_S11_8_7_A3_part5 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    'toString' in null;" in
    
    test_template js_program "test_S11_8_7_A3_part5"
    
 (* ch11/11.2/11.2.3/11.2.3-3_2.js *)
let test_11_2_3_3_2 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#class:'Object','fooCalled':?FC, 'foo': ?F, 'o' : ?O) * 
                 #protoPred(?LS, #ObjectPrototype,'bar', ?L, #empty)
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    var fooCalled = false;
    var foo = 
      /** @requires #obj[rscope](|'main':#GlobalObject) * #obj[#GlobalObject](|#class:'Object','fooCalled':?FC1) 
          @ensures #r = #undefined *  #obj[#GlobalObject](|'fooCalled':true) */
      function (){ fooCalled = true; } 
    var o = { }; 
    o.bar( foo() );" in
    
    test_template js_program "test_11_2_3_3_2"
    
(* ch13/13.0/S13_A17_T2.js *)
let test_S13_A17_T2_part () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|'result':?R, '__func': ?F)
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    var result = __func();
    var __func = 
      /** @requires #obj[rscope](|'main':#GlobalObject) 
          @ensures #r = 'ONE' */
      function (){ return 'ONE'; };" in
    
    test_template js_program "test_S13_A17_T2_part"
    
(* ch13/13.2/S13.2.2_A2.js *)
let test_S13_2_2_A2 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#class:'Object','__PLANT':?P, '__ROSE': ?R, '__PROTO' : ?PR, '__FACTORY' : ?F, '__rose' : ?r)
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    
    var __PLANT= 'flower';
    var __ROSE='rose';

    /** @requires #obj[rscope](|'main':#GlobalObject) 
        @ensures #r = #undefined */
    function __PROTO(){};

    try {
       __PROTO.type = __PLANT;
    }
    catch(e){
      $ERROR('#0: __PROTO.type=__PLANT does not lead to throwing exception')
    }

    /** @requires #obj[rscope](|'main':#GlobalObject) * #protoPred(?LS, #GlobalObject,'__ROSE', ?L, ?R) * ?R != #empty * ?R != #(/) * false = (#typeof(?R) <: #Reference) * #obj[rthis](|#class:'Object','name': ?N)
        @ensures #r = #undefined * (rthis,'name') |-> ?R */
    function __FACTORY(){this.name=__ROSE};

   __FACTORY.prototype=__PROTO;

    var __rose = new __FACTORY();
      
     __rose();" in
    
    test_template js_program "test_S13_2_2_A2"
    
(* ch11/11.2/11.2.3/S11.2.3_A3_T2.js *)
let test_S11_2_3_A3_T2_part1 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    1();" in
    
    test_template js_program "test_S11_2_3_A3_T2_part1"
    
(* ch11/11.2/11.2.3/S11.2.3_A3_T2.js *)
let test_S11_2_3_A3_T2_part2 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#class:'Object','x':?X)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    var x = 1;
    x();" in
    
    test_template js_program "test_S11_2_3_A3_T2_part2"
    
(* ch11/11.2/11.2.3/S11.2.3_A4_T1.js *)
let test_S11_2_3_A4_T1_part1 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|'Boolean':#LBoolean) * #obj[#LBoolean](|#constructid:#boolean_construct) * #typeof(#LBoolean) = #BObject
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    new Boolean(true)();" in
    
    test_template js_program "test_S11_2_3_A4_T1_part1"
    
(* ch11/11.2/11.2.3/S11.2.3_A4_T1.js *)
let test_S11_2_3_A4_T1_part2 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#class:'Object','Boolean':#LBoolean,'x': ?X) * #obj[#LBoolean](|#constructid:#boolean_construct) * #typeof(#LBoolean) = #BObject
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
      var x = new Boolean(true);
      x();" in
    
    test_template js_program "test_S11_2_3_A4_T1_part2"
    
(* ch11/11.2/11.2.2/S11.2.2_A4_T3.js *)
let test_S11_2_2_A4_T3_part1 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|'String':#LString) * #obj[#LString](|#constructid:#string_construct) * #typeof(#LString) = #BObject
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
      new new String('1');" in
    
    test_template js_program "test_S11_2_2_A4_T3_part1"
    
(* ch11/11.2/11.2.2/S11.2.2_A4_T3.js *)
let test_S11_2_2_A4_T3_part2 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#class:'Object','x':?X,'String':#LString) * #obj[#LString](|#constructid:#string_construct) * #typeof(#LString) = #BObject
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
      var x = new String('1');
      new x;" in
    
    test_template js_program "test_S11_2_2_A4_T3_part2"
    
(* ch11/11.2/11.2.2/S11.2.2_A4_T3.js *)
let test_S11_2_2_A4_T3_part3 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#class:'Object','x':?X,'String':#LString) * #obj[#LString](|#constructid:#string_construct) * #typeof(#LString) = #BObject
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
      var x = new String('1');
      new x();" in
    
    test_template js_program "test_S11_2_2_A4_T3_part3"

let test_while () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#class:'Object','x':?X) * #typeof(?X) = #Number
    @topensures #obj[#GlobalObject](|'x': 4)             
    */
      var x = 1; /**@invariant #obj[#GlobalObject](|'x':_X) * (_X <= 4) = true * #typeof(_X) = #Number * _X != #nan * (0 < _X) = true */ 
        while (x < 4) { x++ } ;" in
    
    test_template js_program "test_do_while"
    
let testing_le_lt2 () = 
  apply_config ();
  (*let f_string = "(?X <= 4) = true * (?X < 4) = true * (0 <= ?X) = true * (?X + 1) = ?Y" in*)
  let f_string = "(0 < ?Y) = true" in
  let f = Pulp_Formula_Parser_Utils.parse_formulas f_string in
  (*let f1_string = "(?Y <= 4) = true * (0 < ?Y) = true" in*)
  let f1_string = "?Y != 0" in
  let f1 = Pulp_Formula_Parser_Utils.parse_formulas f1_string in
  let a = CoreStar_Frontend_Pulp.implies f f1 in
  assert_bool "Testing Z3" a
    
let testing_z3_le () = 
  apply_config ();
  let a = CoreStar_Frontend_Pulp.implies empty_f (Eq (Le_BinOp (Le_Literal (Num 2.0), Comparison LessThanEqual, Le_Literal (Num 4.0)), (Le_Literal (Bool true)))) in
  assert_bool "Testing LE" a
  
let testing_z3_le_lt () = 
  apply_config ();
  let f_string = "(?X < 4) = true" in
  let f = Pulp_Formula_Parser_Utils.parse_formulas f_string in
  let f1_string = "((?X + 1) <= 4) = true" in
  let f1 = Pulp_Formula_Parser_Utils.parse_formulas f1_string in
  let a = CoreStar_Frontend_Pulp.implies f f1 in
  assert_bool "Testing LE_LT" a
  
let testing_z3 () = 
  apply_config ();
  let f_string = "
?R0 = #empty * #typeof(?X) = #Number * (#typeof (?RTHIS) <: #Reference) = false * (#typeof (?RTHIS) <: #Reference) = (#typeof (?RSCOPE) <: #Reference) * ?R106 = 4.0 * ?R80 = 4.0 * ?R105 = 1.0 * ?R55 = 1.0 * ?R20 = 1.0 * ?RSCOPE != #(/) * ?RTHIS != ?R0 * ?RTHIS != #(/) * ?RSCOPE != ?R0 * #obj[#GlobalObject](|'x':?R20) * (?R20 <= ?R80) = true" in
  let f = Pulp_Formula_Parser_Utils.parse_formulas f_string in
  let f1_string = "?R106 = 0.0 * ?R105 = 0.0" in
  let f1 = Pulp_Formula_Parser_Utils.parse_formulas f1_string in
  let a = CoreStar_Frontend_Pulp.implies f f1 in
  assert_bool "Testing Z3" a
   
    
(* ch08/8.12/8.12.8/S8.12.8_A1.js *)
(* TODO : need higher order assertions *)
let test_S8_12_8_A1 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|'__obj':?X, 'Object':#LObject, 'String' : #LString) *
                 #obj[#LObject](|#constructid:#object_construct) *
                 #obj[#LString](|#fid:#string_call)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    var __obj = {
      toString: 
        /** @requires #obj[rscope](|'main':#GlobalObject) * #obj[#GlobalObject](|'Object':#LObject) * #obj[#LObject](|#constructid:#object_construct) * #typeof(#LObject) = #BObject
            @ensures #r = _L * #footprint[_L](#proto,#class) * #obj[_L](|#proto:#ObjectPrototype, #class:'Object') */
        function() {return new Object();}
      }  
    String(__obj);" in
    
    test_template js_program "test_S8_12_8_A1"
  
let test_paper_example_1 () =
  let js_program = " 
  
    /** @toprequires 
          #obj[#GlobalObject](|#class:'Object','f':?F, 'o1': ?O1, 'o2' : ?O2, 'y' : ?Y) 
          
        @topensures 
          #obj[#GlobalObject](|'f':_F1, 'o1': _O11, 'o2' : _O21, 'y' : 2) *
          #obj[_F1](|'prototype': _LFP) *
          #obj[_LFP](|#proto : #ObjectPrototype, 'q' : 2) *
          #obj[_O11](|#proto: _LFP, 'p' : 0) *
          #obj[_O21](|#proto: _LFP, 'p' : 1)
    */
            
    var f, o1, o2, y;
    
    f = 
      /** 
          @requires #obj[rscope](|'main':#GlobalObject) *
          #obj[rthis](|#class:'Object','p': _V)
          
          @ensures #obj[rscope](|'main':#GlobalObject) *
          (rthis,'p') |-> x * #r = #undefined
          
      */
      
      function(x) {
        this.p = x;
    }
    
    
    f.prototype.q = 2;
    o1 = new f(0);
    o2 = new f(1);
    y = o1.q" in
  test_template js_program "test_example_1"
 
(* TODO : Work in progress. *)   
let test_paper_example_2 () =
  let js_program = "
    var w, h;
    Object.prototype.z = 1;
    w = 1;
    h =
      /** 
          @requires #obj[rscope](|'main':#GlobalObject, #proto : #ObjectPrototype) *
          #obj[#ObjectPrototype](|'z' : 1) *
          #obj[#GlobalObject]( | 'w' : ?W ) *
          #typeof(x) = #Number *
          #typeof(?W) = #Number
          
          @ensures #obj[rscope](|'main':#GlobalObject,  #proto : #ObjectPrototype) *
          #obj[#ObjectPrototype](|'z' : 1) *
          #obj[#GlobalObject]( | 'w' : ?W) *
          #typeof(x) = #Number *
          #typeof(?W) = #Number
                
      */
    
     function (x) {
      var f1, f2;
      f1 = 
         /** 
          @requires #obj[rscope](|'main':#GlobalObject,'anonymous0':?L) * u = ?W * u != 0 * ?L != #(/) * #typeof(u) = #Number * u != #nan *
          #obj[?L]( | 'f2': ?F2, 'x' : ?X ) * #typeof(?X) = #Number * ?L != #GlobalObject * #typeof(?F2) = #NObject *
          #obj[?F2] ( | '#fid' : 'anonymous2', '#scope' : ?F2S) *
          #obj[?F2S] ( | 'main':#GlobalObject,'anonymous0':?L) *
          #obj[#GlobalObject]( | 'w' : ?W) * #typeof(?W) = #Number
          
          @ensures #obj[rscope](|'main':#GlobalObject,'anonymous0':?L) * u = ?W * u != 0 * ?L != #(/) * #typeof(u) = #Number *
          #obj[?L]( | 'x' : ?X ) * #typeof(?X) = #Number *
          #obj[#GlobalObject]( | 'w' : ?W) * #typeof(?W) = #Number * #r = ?X
          

         */
        function (u) {
          var x = 0;
          if (u == 0) { return x }
          else { return f2(u - w) }
        }
      
      f2 = 
      /** 
          @codename = 'anonymous2'
          @requires #obj[rscope](|'main':#GlobalObject,'anonymous0':?L) * u != 0 * u != #nan *
          ?L != #(/) * ?L != #GlobalObject * 
          #obj[#GlobalObject]( | 'w' : ?W) * #typeof(?W) = #Number *
          #typeof(u) = #Number
          
          @ensures #obj[rscope](|'main':#GlobalObject, 'anonymous0':?L) * u != 0 *
          ?L != #(/) * ?L != #GlobalObject *
          #obj[#GlobalObject]( | 'w' : ?W) *
          #r = (u - ?W)
          
          @requires #obj[rscope](|'main':#GlobalObject,'anonymous0':?L) *
          ?L != #(/) * ?L != #GlobalObject * #typeof(?X) = #Number * u != #nan *
          #obj[?L]( | 'x' : ?X ) * u = 0
          
          @ensures #obj[rscope](|'main':#GlobalObject, 'anonymous0':?L) *
          ?L != #(/) * ?L != #GlobalObject * #typeof(?X) = #Number *
          #obj[?L]( | 'x' : ?X ) *
          #r = ?X
          
      */
      
      function (u) {
        if (u == 0) { return x }
        else { return u - w }
      }
      
      return f1(z)
    }
    h(1);" in
   
  (*let p_exp, p_env = get_pexp js_program in   
  AllFunctions.iter (fun id f -> (Printf.printf "id is %s" id); if id = "anonymous1" then test_js_program_template "test_example_2" f p_exp) p_exp*)  
  test_template js_program "test_example_2"
  
  let test_cav_example_exception () =
    let js_program = "
    
    /** @toprequires #obj[#GlobalObject](|#class:'Object','Person':?P, 'alice': ?A, 'f' : ?F) 
        @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')  */
        
    var alice, f;    
    
    /** @requires #obj[rscope](|'main':#GlobalObject) * #obj[rthis](|#class:'Object', 'name' : ?V) 
        @ensures (rthis,'name') |-> name * #r = #undefined
        
        @requires #obj[rscope](|'main':#GlobalObject) * rthis = #undefined
        @ensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error') 
        
*/
    function Person (name) {
       this.name = name;
    }

    Person.prototype.sayHi = 
       /** @requires #obj[rscope](|'main':#GlobalObject) * #obj[rthis](|#class:'Object','name':?V) * #typeof(?V) = #String 
           @ensures  #obj[rscope](|'main':#GlobalObject) * (rthis,'name') |-> ?V * #typeof(?V) = #String * #r = ('Hi ' ^ ?V)
          
           @requires #obj[rscope](|'main':#GlobalObject) * rthis = #undefined 
           @ensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error') 
*/
      function () {
        return 'Hi ' + this.name
      }

    alice = new Person ('Alice');
    f = alice.sayHi;
    f();
    " in
 
   test_template js_program "test_cav_example_exception"
  
 let suite = "Testing_Evaluation_Examples" >:::
  [ "test_8_7_2_1_s" >:: test_8_7_2_1_s;
    "test_S11_1_2_A1_T2" >:: test_S11_1_2_A1_T2;
    "test_S11_10_1_A2_1_T2" >:: test_S11_10_1_A2_1_T2;
    "test_S11_10_1_A2_1_T3" >:: test_S11_10_1_A2_1_T3;
    "test_S11_10_2_A2_1_T2" >:: test_S11_10_2_A2_1_T2;
    "test_S11_10_2_A2_1_T3" >:: test_S11_10_2_A2_1_T3;
    "test_S11_10_3_A2_1_T2" >:: test_S11_10_3_A2_1_T2;
    "test_S11_10_3_A2_1_T3" >:: test_S11_10_3_A2_1_T3;
    "test_S11_2_1_A2_part1" >:: test_S11_2_1_A2_part1;
    "test_S11_2_1_A2_part2" >:: test_S11_2_1_A2_part2;
    "test_S11_2_1_A3_T4_part1" >:: test_S11_2_1_A3_T4_part1;
    "test_S11_2_1_A3_T4_part2" >:: test_S11_2_1_A3_T4_part2;
    "test_S11_2_1_A3_T5_part1" >:: test_S11_2_1_A3_T5_part1;
    "test_S11_2_1_A3_T5_part2" >:: test_S11_2_1_A3_T5_part2;
    "test_S11_2_2_A2_part1" >:: test_S11_2_2_A2_part1;
    "test_S11_2_2_A2_part2" >:: test_S11_2_2_A2_part2;
    "test_S11_2_2_A3_T1_part1" >:: test_S11_2_2_A3_T1_part1;
    "test_S11_2_2_A3_T1_part2" >:: test_S11_2_2_A3_T1_part2;
    "test_S11_2_2_A3_T1_part3" >:: test_S11_2_2_A3_T1_part3;
    "test_S11_8_7_A3_part1" >:: test_S11_8_7_A3_part1;
    "test_S11_8_7_A3_part2" >:: test_S11_8_7_A3_part2;
    "test_S11_8_7_A3_part3" >:: test_S11_8_7_A3_part3;
    "test_S11_8_7_A3_part4" >:: test_S11_8_7_A3_part4;
    "test_S11_8_7_A3_part5" >:: test_S11_8_7_A3_part5;
    "test_11_2_3_3_2" >:: test_11_2_3_3_2;
    "test_S13_A17_T2_part" >:: test_S13_A17_T2_part;
    "test_S13_2_2_A2" >:: test_S13_2_2_A2;
    "test_S11_2_3_A3_T2_part1" >:: test_S11_2_3_A3_T2_part1;
    "test_S11_2_3_A3_T2_part2" >:: test_S11_2_3_A3_T2_part2;
    "test_S11_2_3_A4_T1_part1" >:: test_S11_2_3_A4_T1_part1;
    "test_S11_2_3_A4_T1_part2" >:: test_S11_2_3_A4_T1_part2;
    "test_S11_2_2_A4_T3_part1" >:: test_S11_2_2_A4_T3_part1;
    "test_S11_2_2_A4_T3_part2" >:: test_S11_2_2_A4_T3_part2;
    "test_S11_2_2_A4_T3_part3" >:: test_S11_2_2_A4_T3_part3;
    "test_paper_example_1" >:: test_paper_example_1;
    "test_cav_example_exception" >:: test_cav_example_exception;
    
    (*"testing_le_lt2" >:: testing_le_lt2;*)
    "test_do_while" >:: test_while;
    (*"testing_z3_le" >:: testing_z3_le;
    "testing_z3_nan" >:: testing_z3_nan;*)
    (*"testing_z3" >:: testing_z3*)
    (*"testing_z3_le_lt" >:: testing_z3_le_lt*)
    
    (*"test_paper_example_2" >:: test_paper_example_2*)
    (*"test_S8_12_8_A1" >:: test_S8_12_8_A1;*)]