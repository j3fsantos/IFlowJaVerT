open Lexing
open JSIL_Syntax

let verbose = ref false

let get_proc_variables proc =

	let var_table = Hashtbl.create 1021 in
	let cmds = proc.proc_body in
	let number_of_cmds = Array.length cmds in

	let rec loop u vars =
		if (u >= number_of_cmds)
			then vars
			else
				let spec, cmd = cmds.(u) in
				(match cmd with
				| SBasic (SAssignment (var, _))
				| SBasic (SLookup (var, _, _))
				| SBasic (SNew var)
				| SBasic (SHasField (var, _, _))
				| SBasic (SGetFields (var, _))
				| SBasic (SArguments var)
				| SCall (var, _, _, _) when (not (Hashtbl.mem var_table var)) ->
						Hashtbl.add var_table var true;
						loop (u+1) (var :: vars)) in

	loop 0 []

let get_proc_nodes cmd_list = Array.of_list cmd_list

let get_proc_info proc =
	(*  computing successors and predecessors *)
	let succ_table, pred_table = JSIL_Utils_Graphs.get_succ_pred proc.proc_body proc.ret_label proc.error_label in
	(* compute which_pred table *)
	let which_pred = JSIL_Utils_Graphs.compute_which_preds pred_table in
	(*  get an array of nodes instead of a list *)
	let nodes = proc.proc_body in
	(* perform a dfs on the graph *)
	let tree_table, parent_table, _, _, dfs_num_table_f, dfs_num_table_r = JSIL_Utils_Graphs.dfs succ_table in
	(* get the variables defined in proc *)
	let vars = get_proc_variables proc in
	nodes, vars, succ_table, pred_table, tree_table, parent_table, dfs_num_table_f, dfs_num_table_r, which_pred

	(***** Desugar me silly *****)

let desugar_labs lproc =

	let ln,               lb,               lp,                 lrl,              lrv,            lel,                lev,              lspec =
		  lproc.lproc_name, lproc.lproc_body, lproc.lproc_params, lproc.lret_label, lproc.lret_var, lproc.lerror_label, lproc.lerror_var, lproc.lspec in

	let nc = Array.length lb in

	let map_labels_to_numbers =
		let mapping = Hashtbl.create nc in
		for i = 0 to (nc - 1) do
			(match lb.(i) with
			  | (_, Some str, _) -> Hashtbl.add mapping str i
				| _ -> ());
		done;
		mapping in

	let convert_to_sjsil mapping =
		let cmds_nolab = Array.map (fun x -> (match x with | (spec, _, cmd) -> (spec, cmd))) lb in
		let cmds = Array.map (fun x ->
			match x with | spec, x ->
				let x = match x with
						| SLBasic cmd -> SBasic cmd
			            | SLGoto lab -> SGoto (Hashtbl.find mapping lab)
			            | SLGuardedGoto (e, lt, lf) -> SGuardedGoto (e, Hashtbl.find mapping lt, Hashtbl.find mapping lf)
			            | SLCall (x, e, le, ol) -> SCall (x, e, le, match ol with | None -> None | Some lab -> Some (Hashtbl.find mapping lab))
						| SLApply (x, le, ol) -> SApply (x, le, match ol with | None -> None | Some lab -> Some (Hashtbl.find mapping lab))
						| SLPhiAssignment (x, args) -> SPhiAssignment (x, args)
						| SLPsiAssignment (x, args) -> SPsiAssignment (x, args) in
				(spec, x)
			) cmds_nolab in

		cmds, (match lrl with | None -> None | Some lab -> Some (Hashtbl.find mapping lab)), (match lel with | None -> None | Some lab -> Some (Hashtbl.find mapping lab)) in

	let mapping = map_labels_to_numbers in
	let b, rl, el = convert_to_sjsil mapping in
	let proc =
		{
			proc_name = ln;
    	proc_body = b;
    	proc_params = lp;
			ret_label = rl;
			ret_var = lrv;
			error_label = el;
			error_var = lev;
			spec = lspec;
		} in
	print_debug_petar (Printf.sprintf "%s" (JSIL_Print.string_of_procedure proc false));
	proc

let rec desugar_labs_list lproc_list =
	match lproc_list with
	| [] -> []
	| lproc :: rest -> (desugar_labs lproc) :: desugar_labs_list rest


let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Format.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

type token = [%import: JSIL_Parser.token] [@@deriving show]

(** Parse contents in 'lexbuf' from the starting symbol 'start'. Terminates if an error occurs. *)
let parse start lexbuf =
	let module JPMI = JSIL_Parser.MenhirInterpreter in

  let last_token = ref JSIL_Parser.EOF
  in let lexer lexbuf =
    let token = JSIL_Lexer.read lexbuf in
      last_token := token; token
  in
    JPMI.loop_handle (fun result -> result)
      (function JPMI.Rejected -> failwith "Parser rejected input"
         | JPMI.HandlingError e ->
             let csn = JPMI.current_state_number e in
               Format.eprintf "%a, last token: %s: %s.@."
                 print_position lexbuf
                 (show_token !last_token)
                 "Error message found"
                 ;
               raise JSIL_Parser.Error
         | _ -> failwith "Unexpected state in failure handler!"
      )
      (JPMI.lexer_lexbuf_to_supplier lexer lexbuf)
      (start lexbuf.Lexing.lex_curr_p)
	
  (* try
  	start JSIL_Lexer.read lexbuf
  with
  | Syntax_error msg ->
    Printf.fprintf stderr "%a: %s\n" print_position lexbuf msg;
		exit (-1)
  | JSIL_Parser.Error ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1) *)

(** Open the file given by 'path' and run the parser on its contents. *)
let ext_program_of_path path =
  let inx = open_in path in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = path };
  let prog = parse JSIL_Parser.Incremental.main_target lexbuf in
  close_in inx;
  prog

let specs_of_path path =
		let inx = open_in path in
	  let lexbuf = Lexing.from_channel inx in
	  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = path };
	  let preds, specs = parse JSIL_Parser.Incremental.pred_spec_target lexbuf in
		close_in inx;
		preds, specs

(** Run the parser on the given string. *)
let ext_program_of_string str =
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
	let prog = parse JSIL_Parser.Incremental.main_target lexbuf in
	prog

let jsil_assertion_of_string str =
	Printf.printf "going to parse the following jsil assertion: %s\n" str; 
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
	parse JSIL_Parser.Incremental.top_level_assertion_target lexbuf

let js_assertion_of_string str =
	Printf.printf "going to parse the following js assertion: %s\n" str; 
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
	parse JSIL_Parser.Incremental.top_level_js_assertion_target lexbuf

let js_logic_pred_def_of_string str : JS2JSIL_Logic.js_logic_predicate =
	Printf.printf "going to parse the following pred def: %s\n" str; 
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
	parse JSIL_Parser.Incremental.js_pred_target lexbuf

let js_only_spec_from_string str : JS2JSIL_Logic.js_spec =
	Printf.printf "going to parse the following only spec: %s\n" str; 
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
	parse JSIL_Parser.Incremental.js_only_spec_target lexbuf

let js_logic_commands_of_string str =
  Printf.printf "going to parse the following logic commands: %s\n" str; 
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
	parse JSIL_Parser.Incremental.js_logic_cmds_target lexbuf



(** Add the declarations in 'program_from' to 'program_to'. *)
let extend_declarations program_to program_from =
	(* Extend the predicates *)
	print_debug_petar (Printf.sprintf "Predicates To:\n");
	Hashtbl.iter (fun k v -> print_debug_petar (Printf.sprintf "\t%s\n" k)) program_to.predicates;
	print_debug_petar (Printf.sprintf "Procedures To:\n");
	Hashtbl.iter (fun k v -> print_debug_petar (Printf.sprintf "\t%s\n" k)) program_to.procedures;
	print_debug_petar (Printf.sprintf "Predicates From:\n");
	Hashtbl.iter (fun k v -> print_debug_petar (Printf.sprintf "\t%s\n" k)) program_from.predicates;
	print_debug_petar (Printf.sprintf "Procedures From:\n");
	Hashtbl.iter (fun k v -> print_debug_petar (Printf.sprintf "\t%s\n" k)) program_from.procedures;
	Hashtbl.iter
	  (fun pred_name pred ->
		  (if (Hashtbl.mem program_to.predicates pred_name)
		   then print_debug_petar (Printf.sprintf "*** WARNING: Predicate %s already exists.\n" pred_name)
		   else print_debug_petar (Printf.sprintf "*** MESSAGE: Adding predicate %s.\n" pred_name));
		  Hashtbl.add program_to.predicates pred_name pred)
		program_from.predicates;
	(* Extend the procedures, except where a procedure with the same name already exists *)
	Hashtbl.iter
		(fun proc_name proc ->
			if (not (Hashtbl.mem program_to.procedures proc_name))
				then (print_debug_petar (Printf.sprintf "*** MESSAGE: Adding procedure: %s.\n" proc_name); Hashtbl.add program_to.procedures proc_name proc)
				else (print_debug_petar (Printf.sprintf "*** WARNING: Procedure %s already exists.\n" proc_name)))
		program_from.procedures

(** Load the programs imported in 'program' and add its declarations to 'program' itself. *)
let resolve_imports filename program =
	(* 'added_imports' keeps track of the loaded files *)
	let added_imports = Hashtbl.create 32 in
	Hashtbl.add added_imports filename true;
	let rec resolve_imports_iter imports =
		(match imports with
		| [] -> ()
		| file :: rest_imports ->
			print_debug_petar (Printf.sprintf "File: %s\n" file);
			if (not (Hashtbl.mem added_imports file))
				then
					(Hashtbl.replace added_imports file true;
					let imported_program = ext_program_of_path (file ^ ".jsil") in
					extend_declarations program imported_program;
					resolve_imports_iter (rest_imports @ imported_program.imports))) in
	print_debug_petar (Printf.sprintf "Predicates Program:\n");
	Hashtbl.iter (fun k v -> print_debug_petar (Printf.sprintf "\t%s\n" k)) program.predicates;
	print_debug_petar (Printf.sprintf "Procedures Program:\n");
	Hashtbl.iter (fun k v -> print_debug_petar (Printf.sprintf "\t%s\n" k)) program.procedures;
	resolve_imports_iter program.imports

(** Converts an extended JSIL program into a set of basic procedures.
		@param filename Name of the file the program was loaded from.
    @param ext_program Program to be processed.
*)
let prog_of_ext_prog filename ext_program =
	let epreds = ext_program.predicates in
	let eprocs = ext_program.procedures in
	(* Add the declarations from the imported files *)
	print_debug_petar (Printf.sprintf "Entering resolve_imports.\n");
	resolve_imports filename ext_program;
	print_debug_petar (Printf.sprintf "Exiting resolve_imports.\n");
	(* Desugar the labels in the procedures, etc. *)
	let prog = Hashtbl.create 101 in
	let global_which_pred = Hashtbl.create 101 in
	Hashtbl.iter
		(fun proc_name ext_proc ->
			print_debug_petar (Printf.sprintf "Going to desugar procedure %s baby!!!\n" proc_name);
			let proc = desugar_labs ext_proc in
			(* Removing dead code and recalculating everything
			let proc = JSIL_Utils_Graphs.remove_unreachable_code proc false in
			let proc = JSIL_Utils_Graphs.remove_unreachable_code proc true in *)

			let succ_table, pred_table = JSIL_Utils_Graphs.get_succ_pred proc.proc_body proc.ret_label proc.error_label in
			
			print_debug_petar "after succ and pred tables!!!\n";
			
			let which_pred = JSIL_Utils_Graphs.compute_which_preds pred_table in
			
			print_debug_petar "after which pred computation!!!\n";
			
			Hashtbl.iter
				(fun (prev_cmd, cur_cmd) i ->
					Hashtbl.replace global_which_pred (proc_name, prev_cmd, cur_cmd) i)
				which_pred;

			Hashtbl.replace prog proc_name proc)
	ext_program.procedures;
	prog, global_which_pred


let extend_which_pred global_which_pred proc =
	let succ_table, pred_table = JSIL_Utils_Graphs.get_succ_pred proc.proc_body proc.ret_label proc.error_label in
	let which_pred = JSIL_Utils_Graphs.compute_which_preds pred_table in
	let proc_name = proc.proc_name in
	Hashtbl.iter
		(fun (prev_cmd, cur_cmd) i ->
			Hashtbl.replace global_which_pred (proc_name, prev_cmd, cur_cmd) i)
		which_pred

let print_which_pred wp =
	Hashtbl.fold
	  (fun k v ac ->
		 ac ^
		 (match k with
			| (pn : string), (pc : int), (cc : int) -> Printf.sprintf "    (\"%s\" %d %d %d)\n" pn pc cc v))
		wp ""
