open OUnit
open TestsUtils

let sample_test = 
	{
		prelude = [""];
		main = "var x; x = 2;";
		
		expected_value = (Some Normal, Some (Num 2.));
		description = "";
	}

let test_sample_test () = 
	run_test test_javascript_template (sample_test)

let suite = "Testing JavaScript" >::: 
[
	sample_test.description >:: test_sample_test
]