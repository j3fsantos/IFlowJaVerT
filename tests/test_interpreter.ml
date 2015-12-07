(* Testing frontend that only pulls in tests that don't depend on Corestar *)
open OUnit

let suite = "Test_Translation" >:::
  [Pulp_Translation_Tests.suite; Pulp_Interpreter_Tests.suite]

let _ =
  run_test_tt_main suite
