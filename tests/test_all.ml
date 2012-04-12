open OUnit

let suite = "Test The Lot" >:::
  [ Logictests.suite;
    Parsing_tests.suite;
    Utils_tests.suite;
    Examples_tests.suite;
    Paper_examples_tests.suite;
  ]

let _ = run_test_tt_main suite
