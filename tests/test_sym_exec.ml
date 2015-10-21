open OUnit

let test_translation = "Test_Symbolic_Execution" >:::
  [Pulp_Sym_Exec_Tests.suite; Spec_Functions_Tests.suite]

let _ = run_test_tt_main test_translation
