open OUnit

let main_suite = "Test_Main" >:::
  [ 
		TestsJS.suite;
  ]

let _ = 
	TestsJS.print_test_list TestsJS.test_list;
	run_test_tt_main main_suite
