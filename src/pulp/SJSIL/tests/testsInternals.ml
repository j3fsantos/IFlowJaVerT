open OUnit
open TestsUtils

let prologue = "
proc main () {
		xret := \"setupInitialHeap\" ();
"

let epilogue = "

 	rlab:	skip;
 	elab:	skip
}
with
{
	ret:	xret, rlab;
	err:	xret, elab;
}"

let sample_test = 
	{
		prelude = ["Init"; "Internals"; "Errors"];
		main = 
"
		xret := 2;";
		
		expected_value = (Some Normal, None);
		description = "";
	}

let test_sample_test () = 
	run_test test_jsil_template (wrap_jsil_test sample_test prologue epilogue)

let suite = "Testing Internal Functions" >::: 
[
	sample_test.description >:: test_sample_test
]