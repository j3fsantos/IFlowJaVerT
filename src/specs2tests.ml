open JSIL_Syntax
open Specs_Compiler

let file = ref "" 

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [
		(* file containing the program to symbolically execute *)
		"-file", Arg.String(fun f -> file := f), "file to run";
	  ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg



let main () =
	arguments ()

let _ = main()