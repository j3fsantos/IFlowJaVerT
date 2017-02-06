open Lexing
open JSIL_Syntax
open JSIL_Memory_Model
open JSIL_Interpreter

let file = ref ""
let spec_file = ref ""
let jsil_run = ref false
let do_ssa = ref false
let do_sexpr = ref false
let empty_heap = ref false
let specs = ref false

let verbose = ref false

let compile_and_run = ref false

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
			(* run *)
			"-run", Arg.Unit(fun () -> jsil_run := true), "run the program given as input";
			(* ssa normalise
			"-ssa", Arg.Unit(fun () -> do_ssa := true), "ssa normalise"; *)
			(* verbositiness *)
			"-verbose", Arg.Unit(fun () -> verbose := true; JSIL_Interpreter.verbose := true), "verbose output";
			(* compile js file and run *)
			"-from_javascript", Arg.String(fun f -> file := f; compile_and_run := true), "run from javascript";
			(* sexpr sexpr sexpr *)
			"-sexpr",      Arg.Unit(fun () -> do_sexpr      := true), "generate output in s-expression format";
			(* empty heap *)
			"-empty_heap",      Arg.Unit(fun () -> empty_heap    := true), "empty heap";
      "-closure", Arg.Clear(Parser_main.use_json), "use closure parser";
      (* specs *)
      "-specs", Arg.String(fun f -> spec_file := f; specs := true), "specs_file";
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

let run_jsil_prog prog which_pred cc_tbl vis_tbl =
	let heap = SHeap.create 1021 in
        let (rettype, retval) = evaluate_prog prog which_pred heap cc_tbl vis_tbl  in
	let final_heap_str = JSIL_Print.string_of_heap heap in
    if (!verbose) then Printf.printf "Final heap: \n%s\n" final_heap_str;
				Printf.printf "%s, %s\n"
				  (match rettype with
					| Normal -> "Normal"
					| Error -> "Error")
					(match rettype with
					| Normal ->  (JSIL_Print.string_of_literal retval false)
					| Error -> (match retval with
					| Loc loc ->
						(let obj = (try SHeap.find heap loc with
			                  | _ -> (raise (Failure "Error object without a prototype."))) in
			      let lproto = (try SHeap.find obj "@proto" with
						              | _ -> (raise (Failure "Error object without a prototype."))) in
						(match lproto with
						| Loc loc ->
							let objproto = (try SHeap.find heap loc with
							                 | _ -> (raise (Failure "Error object without a prototype."))) in
							let eType = (try SHeap.find objproto "name" with
						                | _ -> String "") in
						  let message = (try SHeap.find obj "message" with
						                | _ -> String "") in
							let eType =
					      (match eType with
								| LList list -> List.nth list 1
								| _ -> eType) in
						  (JSIL_Print.string_of_literal eType false) ^ " : " ^ (JSIL_Print.string_of_literal message false)
						| _ -> (raise (Failure "Prototype object not an object."))))
					| _ -> JSIL_Print.string_of_literal retval false));
        return_to_exit rettype

let main () =
    Parser_main.use_json := true;
	arguments ();
    Parser_main.init ();
	if (!compile_and_run) then
          begin try
            Parser_main.verbose := false;
            let harness = load_file "harness.js" in
            let main = load_file (!file) in
            let offset_converter = Js_pre_processing.memoized_offsetchar_to_offsetline main in
            let all = harness ^ "\n" ^ main in
            let e = Parser_main.exp_from_string ~force_strict:true all in

			let e_annot_str e = Pretty_print.string_of_annots e.Parser_syntax.exp_annot in
			Printf.printf "Top-level annotations:\n%s\n" (e_annot_str e);
			(match e.exp_stx with
			| Script (_, le) -> List.iter (fun x -> Printf.printf "Annotations:\n%s\n" (e_annot_str x)) le
			| _ -> Printf.printf "Top-level tag is not Script.\n");

            let (ext_prog, cc_tbl, vis_tbl) = Js2jsil.js2jsil e offset_converter false in
                let prog, which_pred = JSIL_Utils.prog_of_ext_prog !file ext_prog in
                run_jsil_prog prog which_pred (Some cc_tbl) (Some vis_tbl)
              with
                | Parser.ParserFailure file -> Printf.printf "\nParsing problems with the file '%s'.\n" file; exit 1
                | Parser.JS_To_XML_parser_failure
                | Parser.XmlParserException -> Printf.printf "\nXML parsing issues.\n"; exit 1
                | Js_pre_processing.EarlyError e -> Printf.printf "\nParser post-processing threw an EarlyError: %s\n" e; exit 1
              end
(*
let main () =
	arguments ();
	if (!compile_and_run) then
  begin try
  	Parser_main.js_to_xml_parser := "js_parser.jar";
    Parser_main.verbose := false;
    let harness = load_file "harness.js" in
    let main = load_file (!file) in
		let offset_converter = Js_pre_processing.memoized_offsetchar_to_offsetline main in
    let all = harness ^ "\n" ^ main in
    let e = Parser_main.exp_from_string all in
    let (ext_prog, cc_tbl, vis_tbl) = Js2jsil.js2jsil e offset_converter in
    let prog, which_pred = JSIL_Utils.prog_of_ext_prog !file ext_prog in
    run_jsil_prog prog which_pred (Some cc_tbl) (Some vis_tbl)
  with
    | Parser.ParserFailure file -> Printf.printf "\nParsing problems with the file '%s'.\n" file; exit 1
    | Parser.JS_To_XML_parser_failure
    | Parser.XmlParserException -> Printf.printf "\nXML parsing issues.\n"; exit 1
    | Js_pre_processing.EarlyError e -> Printf.printf "\nParser post-processing threw an EarlyError: %s\n" e; exit 1
  end
*)
	else
	begin
		let ext_prog = JSIL_Utils.ext_program_of_path !file in
		let prog, which_pred = JSIL_Utils.prog_of_ext_prog !file ext_prog in
		(* let prog, which_pred = if (!do_ssa) then JSIL_SSA.ssa_compile_prog prog else prog, which_pred in *)

    let preds, specs =
      if (!specs) then
        JSIL_Utils.specs_of_path !spec_file
      else ([], []) in

    if (!jsil_run) then run_jsil_prog prog which_pred None None else ()
	end

let _ = main()
