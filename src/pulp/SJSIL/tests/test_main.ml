open OUnit

let main_suite = "Test_Main" >:::
  [ 
		TestsJS.suite;
  ]

let _ = run_test_tt_main main_suite
