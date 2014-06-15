open OUnit

let parsing_suite = "Test_Parsing" >:::
  [ 
    Formula_parser_tests.suite
  ]

let suite = "Test_Main" >:::
  [ Paper_examples_tests.suite;
    Logictests.suite;
    Examples_tests.suite;
    Rec_examples.suite;
    Bin_op_tests.suite;
  ]

(* If we can test the graphing or other outputs, they might go here? *)
let outputs = "Test_Outputs" >:::
  [
    Assert_Gen_Tests.suite
  ]
  
let test_translation = "Test_Translation" >:::
  [Pulp_Translation_Tests.suite]

let all_suite = "Test_All" >:::
  [parsing_suite; suite ; outputs; test_translation]


let _ = run_test_tt_main all_suite
