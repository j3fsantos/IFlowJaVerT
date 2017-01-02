open Lexing
open JSIL_Syntax
open JSIL_Memory_Model
open JSIL_Interpreter

let file = ref ""
let js = ref false
let verbose = ref false

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  (s)

let arguments () =
  let usage_msg="Usage: -file <path>" in
  Arg.parse
    [
			(* file to compile *)
			"-file", Arg.String(fun f -> file := f), "file to run";
			(* verbositiness *)
			"-verbose", Arg.Unit(fun () -> verbose := true; JSIL_Interpreter.verbose := true), "verbose output";
			(* js *)
			"-js", Arg.Unit(fun () -> js := true), "for js";
    ]
    (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
    usage_msg


let burn_to_disk path data =
	let oc = open_out path in
		output_string oc data;
		close_out oc

let return_to_exit rettype =
  match rettype with
  | Error -> exit 1
  | _     -> ()


let generate_js_heap_and_internal_functions () = 				
	let int_ext_prog = JSIL_Utils.ext_program_of_path "internals_builtins_procs.jsil" in
	let int_prog, _ = JSIL_Utils.prog_of_ext_prog "internals_builtins_procs.jsil" int_ext_prog in
	let sint_prog = SExpr_Print.sexpr_of_program int_prog false in
	let str_int_prog = Printf.sprintf SExpr_Templates.template_internal_procs_racket sint_prog in
	burn_to_disk ("internals_builtins_procs.rkt") str_int_prog;
	
	let ih_ext_prog = JSIL_Utils.ext_program_of_path "initial_heap.jsil" in
	let ih_prog, ih_which_pred = JSIL_Utils.prog_of_ext_prog "initial_heap.jsil" ih_ext_prog in
	let ih_heap = make_initial_heap true in  
  let _ = evaluate_prog ih_prog ih_which_pred ih_heap None None in
	let str_ih_heap = SExpr_Print.sexpr_of_heap ih_heap in
	let str_ih_heap = Printf.sprintf SExpr_Templates.template_hp_racket str_ih_heap in
	burn_to_disk ("hp.rkt") str_ih_heap; 
	int_prog
	

let main () =
	arguments ();
	if (!file <> "") then (
	let ext_prog = JSIL_Utils.ext_program_of_path !file in
	let prog, which_pred = JSIL_Utils.prog_of_ext_prog !file ext_prog in
	
	(* serializing JS internal functions + JS initial heap *)
	if (!js) then (
		let int_prog = generate_js_heap_and_internal_functions () in 
		let _ = Hashtbl.iter (fun k _ -> if (Hashtbl.mem int_prog k) then (Hashtbl.remove prog k)) prog in 
		());
	
	(* serializing the which_pred table *)
	let wp_array_str = JSIL_Utils.print_which_pred which_pred in
	let str_wp = Printf.sprintf SExpr_Templates.template_wp_racket wp_array_str in
	burn_to_disk ("wp.rkt") str_wp;
	
	(* I have to understand what this is doing *)
	(* let _ = Hashtbl.iter (fun k _ -> if (Hashtbl.mem int_prog k) then (Hashtbl.remove prog k)) prog in *)
	
	let sprog = SExpr_Print.sexpr_of_program prog false in
	let sprog_in_template = Printf.sprintf SExpr_Templates.template_procs_racket sprog in
	let file_name = Filename.chop_extension !file in
  burn_to_disk (file_name ^ ".rkt") sprog_in_template)
	 

let _ = main()
