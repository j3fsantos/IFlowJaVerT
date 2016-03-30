(* ./tests/spec_Functions_Tests.ml
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
open Spec_Fun_Specs
open Pulp_Syntax

let test_program_template name f fs = 
  apply_config ();
  List.iteri (fun i s -> check_single_spec name f fs s i "tests/dot/spec/") f.func_spec
  
let test_get_value () =
  let env = get_env_spec () in
  let get_value_fb = AllFunctions.find (get_value_fn ()) env in
  test_program_template "test_get_value" get_value_fb env

let test_put_value () =
  let env = get_env_spec () in
	let dummy_exp1 = (Literal Undefined) in
	let dummy_exp2 = (Literal Undefined) in
  let put_value_fb = AllFunctions.find (Pulp_Syntax_Print.string_of_spec_fun_id (PutValue (dummy_exp1, dummy_exp2))) env in
  test_program_template "test_put_value" put_value_fb env

let test_has_property () =
  let env = get_env_spec () in
	let dummy_exp1 = (Literal Undefined) in
	let dummy_exp2 = (Literal Undefined) in
  let has_property_fb = AllFunctions.find (Pulp_Syntax_Print.string_of_spec_fun_id (HasProperty (dummy_exp1, dummy_exp2))) env in
  test_program_template "test_has_property" has_property_fb env

let test_has_property () =
  let env = get_env_spec () in
	let dummy_exp1 = (Literal Undefined) in
  let to_boolean_fb = AllFunctions.find (Pulp_Syntax_Print.string_of_spec_fun_id (ToBoolean (dummy_exp1))) env in
  test_program_template "test_to_boolean" to_boolean_fb env

let test_bool_construct () =
  let env = get_env () in
  let boolean_constructor = AllFunctions.find ((string_of_builtin_function Boolean_Construct)) env in
  test_program_template "test_boolean_constructor" boolean_constructor env




let suite = "Spec_Functions_Tests" >::: [
  (* "test_get_value" >:: test_get_value; *)
	(* "test_put_value" >:: test_put_value; *)
	(* "test_has_property" >:: test_has_property; *)
	(* "test_has_property" >:: test_has_property; *)
	"test_bool_construct" >:: test_bool_construct
  ]