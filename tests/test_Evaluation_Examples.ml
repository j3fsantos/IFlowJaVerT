open OUnit

let test = "Test_Evaluation_Examples" >:::
  [Evaluation_Examples.suite]

let _ = run_test_tt_main test
