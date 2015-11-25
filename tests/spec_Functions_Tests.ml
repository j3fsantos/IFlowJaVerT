open OUnit
open Tests_Utils
open Pulp_Procedure
open Spec_Fun_Specs

let test_program_template name f fs = 
  apply_config ();
  List.iteri (fun i s -> check_single_spec name f fs s i) f.func_spec
  
let test_get_value () =
  let env = get_env_spec () in
  let get_value_fb = AllFunctions.find (get_value_fn ()) env in
  test_program_template "test_get_value" get_value_fb env

let suite = "Spec_Functions_Tests" >::: [
  "test_get_value" >:: test_get_value;
  ]