open OUnit

let suite = "Test The Lot" >:::
  [Logictests.suite]

let _ = run_test_tt_main suite
