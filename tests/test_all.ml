open OUnit

let suite = "Test The Lot" >:::
  [ Paper_examples_tests.suite;
    Logictests.suite;
    Parsing_tests.suite;
    Utils_tests.suite;
    Examples_tests.suite;
    Rec_examples.suite
  ]

let _ = run_test_tt_main suite
