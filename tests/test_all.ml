open OUnit

let parsing_suite = "Test_Parsing" >:::
  [ Parser_tests.suite;
    Formula_parser_tests.suite
  ]

let suite = "Test_Main" >:::
  [ Paper_examples_tests.suite;
    Logictests.suite;
    Utils_tests.suite;
    Examples_tests.suite;
    Rec_examples.suite;
    Bin_op_tests.suite;
  ]

(* If we can test the graphing or other outputs, they might go here? *)
let outputs = "Test_Outputs" >:::
  [
    Assert_Gen_Tests.suite
  ]

let all_suite = "Test_All" >:::
  [parsing_suite; suite ; outputs]


let _ = run_test_tt_main all_suite
