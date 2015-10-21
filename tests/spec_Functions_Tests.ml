open OUnit
open Tests_Utils
open Pulp_Procedure

let test_program_template name f fs = 
  apply_config ();
  List.iteri (fun i s -> check_single_spec name f fs s i) f.func_spec

let suite = "Spec_Functions_Tests" >::: [
  ]