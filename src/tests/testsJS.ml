open OUnit
open TestsUtils

let read_file filename =
  let chan = open_in filename in
  Std.input_list chan

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = String.create n in
  really_input ic s 0 n;
  close_in ic;
  (s)

let test_folder = "tests/"
let test_file = "test_list"
let harness = load_file "harness.js"

let test_list = 
	let file_list = read_file test_file in
	List.map (fun s -> test_folder ^ s) file_list

let rec print_test_list list = 
  (match list with
   | [] -> ()
   | s :: list -> (Printf.printf "%s\n" s; print_test_list list))

let test_from_file file = 
	let file_contents = load_file file in
	{
		prelude = [""];
		main = harness ^ "\n" ^ file_contents;
		expected_value = (Some Normal, None);
		description = file;
	}

let tests = List.map (fun file -> test_from_file file) test_list

let run_js_test test = 
	Printf.printf "\nRunning test: %s\n" test.description;
	run_test test_javascript_template test

let run_test_list = List.map (fun test -> test.description >:: (fun () -> run_js_test test)) tests 

let suite = "Testing JavaScript" >::: run_test_list