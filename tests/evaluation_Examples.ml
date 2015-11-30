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
    @toprequires #protoPred(_LS, #ObjectPrototype,'_8_7_2_1', _L, #empty) *
                 #obj[#GlobalObject]('_8_7_2_1'|#proto:_P,'undefined':#undefined) 
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    _8_7_2_1 = 11;" in
  
  test_template js_program "test_8_7_2_1_s" 
  
(* ch11/11.1/11.1.2/S11.1.2_A1_T2.js *)  
let test_S11_1_2_A1_T2 () =
  let js_program = "/**
    @toprequires #protoPred(_LS, #ObjectPrototype,'z', _L, #empty) *
                 #obj[#GlobalObject]('z'|#proto:_P,'undefined':#undefined) *
                 rthis = #GlobalObject
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    this.z; z;" in
    
  test_template js_program "test_S11_1_2_A1_T2"
  
(* ch11/11.2/11.2.1/S11.2.1_A2.js *)  
let test_S11_2_1_A2_part1 () =
  let js_program = "/**
    @toprequires #protoPred(_LS, #ObjectPrototype,'object', _L, #empty) *
                 #obj[#GlobalObject]('object'|#proto:_P,'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    object[1];" in
    
  test_template js_program "test_S11_2_1_A2_part1"
  
(* ch11/11.2/11.2.1/S11.2.1_A2.js *)  
let test_S11_2_1_A2_part2 () =
  let js_program = "/**
    @toprequires #protoPred(_LS, #ObjectPrototype,'object', _L, #empty) *
                 #obj[#GlobalObject]('object'|#proto:_P,'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    object.prop;" in
    
    test_template js_program "test_S11_2_1_A2_part2"
    
(* ch11/11.2/11.2.1/S11.2.1_A3_T4.js *)  
let test_S11_2_1_A3_T4_part1 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#proto:_P,'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    undefined.toString();" in
    
    test_template js_program "test_S11_2_1_A3_T4_part1"
    
(* ch11/11.2/11.2.1/S11.2.1_A3_T4.js *)  
let test_S11_2_1_A3_T4_part2 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#proto:_P,'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    undefined['toString']();" in
    
    test_template js_program "test_S11_2_1_A3_T4_part2"
    
(* ch11/11.2/11.2.1/S11.2.1_A3_T5.js *)  
let test_S11_2_1_A3_T5_part1 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#proto:_P,'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    null.toString();" in
    
    test_template js_program "test_S11_2_1_A3_T5_part1"
    
(* ch11/11.2/11.2.1/S11.2.1_A3_T5.js *)  
let test_S11_2_1_A3_T5_part2 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#proto:_P,'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    null['toString']();" in
    
    test_template js_program "test_S11_2_1_A3_T5_part2"
    
(* ch11/11.2/11.2.2/S11.2.2_A2.js *)  
let test_S11_2_2_A2_part1 () =
  let js_program = "/**
    @toprequires  #protoPred(_LS, #ObjectPrototype,'x', _L, #empty) *
                  #obj[#GlobalObject]('x'|#proto:_P,'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    new x;" in
    
    test_template js_program "test_S11_2_2_A2_part1"
    
(* ch11/11.2/11.2.2/S11.2.2_A2.js *)  
let test_S11_2_2_A2_part2 () =
  let js_program = "/**
    @toprequires  #protoPred(_LS, #ObjectPrototype,'x', _L, #empty) *
                  #obj[#GlobalObject]('x'|#proto:_P,'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#ReferenceErrorPrototype, #class:'Error')             
    */
    new x();" in
    
    test_template js_program "test_S11_2_2_A2_part2"
    
(* ch11/11.2/11.2.2/S11.2.2_A3_T1.js *)  
let test_S11_2_2_A3_T1_part1 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|#proto:_P,'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    new true;" in
    
    test_template js_program "test_S11_2_2_A3_T1_part1"
    
(* ch11/11.2/11.2.2/S11.2.2_A3_T1.js *)  
let test_S11_2_2_A3_T1_part2 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|'x':_X, #proto:_P,'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    var x = true;
    new x;" in
    
    test_template js_program "test_S11_2_2_A3_T1_part2"
    
(* ch11/11.2/11.2.2/S11.2.2_A3_T1.js *)  
let test_S11_2_2_A3_T1_part3 () =
  let js_program = "/**
    @toprequires #obj[#GlobalObject](|'x':_X, #proto:_P,'undefined':#undefined)
        
    
    @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error')             
    */
    var x = true;
    new x();" in
    
    test_template js_program "test_S11_2_2_A3_T1_part3"
  
let test_paper_example_1 () =
  let js_program = " 
  
    /** @toprequires 
          #obj[#GlobalObject](|'f':_F, 'o1': _O1, 'o2' : _O2, 'y' : _Y, #proto:_P,'undefined':#undefined) 
          
        @topensures 
          #obj[#GlobalObject](|'f':_F1, 'o1': _O11, 'o2' : _O21, 'y' : 2, #proto:#ObjectPrototype,'undefined':#undefined) *
          #obj[_F1](|'prototype': _LFP) *
          #obj[_LFP](|#proto : #ObjectPrototype, 'q' : 2) *
          #obj[_O11](|#proto: _LFP, 'p' : 0) *
          #obj[_O21](|#proto: _LFP, 'p' : 1)
    */
            
    var f, o1, o2, y;
    
    f = 
      /** 
          @requires #obj[rscope](|'main':#GlobalObject) *
          (rthis,'p') |-> _V
          
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
    var w, g, f;
    this.z = 1;
    w = 1;
    f =
      /** 
          @requires #obj[rscope](|'main':#GlobalObject) *
          #obj[#GlobalObject]( | 'w' : ?W, 'z' : ?Z ) *
          #typeof(x) = #Number *
          #typeof(?W) = #Number *
          #typeof(?Z) = #Number
          
          @ensures #obj[rscope](|'main':#GlobalObject) *
          #obj[#GlobalObject]( | 'w' : ?W, 'z' : ?Z ) *
          #typeof(x) = #Number *
          #typeof(?W) = #Number *
          #typeof(?Z) = #Number 
                
      */
    
     function (x) {
      var g, h;
      g = 
         /** 
          @requires #obj[rscope](|'main':#GlobalObject,'anonymous0':?L) *
          #obj[#GlobalObject]( | 'w' : ?W, 'z' : ?Z ) *
          #obj[?L]( | 'x' : ?X ) *
          #typeof(u) = #Number
          
          @ensures #obj[rscope](|'main':#GlobalObject, 'anonymous0':?L) *
          #obj[#GlobalObject]( | 'w' : ?W, 'z' : ?Z) *
          #obj[?L]( | 'x' : ?X ) *
          #r = (((u + ?X) + ?W) + ?Z)
          
         */
        function (u) {
          return u + x + w + z
        }
      
      h = 
      /** 
          @requires #obj[rscope](|'main':#GlobalObject,'anonymous0':?L) *
          #obj[#GlobalObject]( | 'w' : ?W, 'z' : ?Z) *
          #obj[?L]( | 'x' : ?X ) *
          #typeof(u) = #Number
          
          @ensures #obj[rscope](|'main':#GlobalObject, 'anonymous0':?L) *
          #obj[#GlobalObject]( | 'w' : ?W, 'z' : ?Z) *
          #obj[?L]( | 'x' : ?X ) *
          #r = ((((u + 1) + ?X) + ?W) + ?Z)
          
      */
      
      function (u) {
        var x;
        x = 0;
        return x + u + g(1)
      }
      return h(1)
    }
    f(1);" in
  test_template js_program "test_example_2"
  
  let test_cav_example_exception () =
    let js_program = "
    
    /** @toprequires #obj[#GlobalObject](|'Person':_P, 'alice': _A, 'f' : _F, #proto:_P,'undefined':#undefined) 
        @topensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error') */
        
    var alice, f;    
    
    /** @requires #obj[rscope](|'main':#GlobalObject) * (rthis,'name') |-> _V 
        @ensures (rthis,'name') |-> name * #r = #undefined
        
        @requires #obj[rscope](|'main':#GlobalObject) * rthis = #undefined
        @ensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error') */
    function Person (name) {
       this.name = name;
    }

    Person.prototype.sayHi = 
       /** @requires #obj[rscope](|'main':#GlobalObject) * (rthis,'name') |-> ?V * #typeof(?V) = #String 
           @ensures  #obj[rscope](|'main':#GlobalObject) * (rthis,'name') |-> ?V * #typeof(?V) = #String * #r = ('Hi ' ^ ?V)
          
           @requires #obj[rscope](|'main':#GlobalObject) * rthis = #undefined 
           @ensureserr #r = _E * #obj[_E](|#proto:#TypeErrorPrototype, #class:'Error') */
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
    "test_paper_example_1" >:: test_paper_example_1;
    "test_cav_example_exception" >:: test_cav_example_exception;
    (*"test_paper_example_2" >:: test_paper_example_2*) ]