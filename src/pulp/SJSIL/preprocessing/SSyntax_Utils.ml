open SSyntax
open Lexing

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
				| SBasic (SProtoField (var, _, _))
				| SBasic (SProtoObj (var, _, _))
				| SCall (var, _, _, _) when (not (Hashtbl.mem var_table var)) ->	
						Hashtbl.add var_table var true;  
						loop (u+1) (var :: vars)
				| _ -> loop (u+1) vars) in 
	
	loop 0 [] 			

let get_proc_nodes cmd_list = Array.of_list cmd_list

let get_proc_info proc = 
	(*  computing successors and predecessors *)
	let succ_table, pred_table = SSyntax_Utils_Graphs.get_succ_pred proc.proc_body proc.ret_label proc.error_label in 
	(* compute which_pred table *)
	let which_pred = SSyntax_Utils_Graphs.compute_which_preds pred_table in  
	(*  get an array of nodes instead of a list *)
	let nodes = proc.proc_body in 
	(* perform a dfs on the graph *) 
	let tree_table, parent_table, _, _, dfs_num_table_f, dfs_num_table_r = SSyntax_Utils_Graphs.dfs succ_table in 
	(* get the variables defined in proc *)
	let vars = get_proc_variables proc in 
	nodes, vars, succ_table, pred_table, tree_table, parent_table, dfs_num_table_f, dfs_num_table_r, which_pred
	
	(***** Desugar me silly *****)

let desugar_labs (lproc : lprocedure) = 
	
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
			            | SLCall (x, e, le, ol) -> SCall (x, e, le, match ol with | None -> None | Some lab -> Some (Hashtbl.find mapping lab)) in
				(spec, x)
			) cmds_nolab in
			
		cmds, (Hashtbl.find mapping lrl), (match lel with | None -> None | Some lab -> Some (Hashtbl.find mapping lab)) in
	
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
	Printf.printf "%s" (SSyntax_Print.string_of_procedure proc false);
	proc
	 
let rec desugar_labs_list lproc_list =
	match lproc_list with
	| [] -> []
	| lproc :: rest -> (desugar_labs lproc) :: desugar_labs_list rest


let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)


let parse_with_error lexbuf =
  try SJSIL_Parser.prog_target SJSIL_Lexer.read lexbuf with
  | SJSIL_Lexer.SyntaxError msg ->
    Printf.fprintf stderr "%a: %s\n" print_position lexbuf msg;
		exit (-1)
  | SJSIL_Parser.Error ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)


let lprog_of_path path = 
	let inx = open_in path in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = path };
  let (imports, lproc_list) : (string list option * lprocedure list) = parse_with_error lexbuf in	
	close_in inx;
	
	let lprocs : lprocedure SLProgram.t = SLProgram.create 1021 in 
	List.iter 
		(fun (lproc : lprocedure) -> 
			let proc_name = lproc.lproc_name in 
			SLProgram.replace lprocs proc_name lproc
		) 
		lproc_list;
		 
	match imports with 
	| None -> [], lprocs
	| Some imports -> imports, lprocs


let extend_lprocs lprocs_to lprocs_from =
	SLProgram.iter
		(fun proc_name proc -> 
			if (not (SLProgram.mem lprocs_to proc_name))
				then SLProgram.add lprocs_to proc_name proc
				else ())
		lprocs_from	


let add_imports lprocs imports = 
	let added_imports = Hashtbl.create 101 in 
	let rec add_imports_iter imports = 
		(match imports with 
		| [] -> () 
		| file :: rest_imports -> 
			if (Hashtbl.mem added_imports file) 
				then () 
				else 
					(Hashtbl.add added_imports file true;
					let (new_imports, new_lprocs) : (string list * lprocedure SLProgram.t) = lprog_of_path (file ^ ".jsil") in 
					extend_lprocs lprocs new_lprocs; 
					add_imports_iter (rest_imports @ new_imports))) in
	add_imports_iter imports


let prog_of_lprog lprog =
	let imports, lproc_list = (match lprog with imports, lproc_list -> imports, lproc_list) in 
	add_imports lproc_list imports; 
	 
	let prog = SProgram.create 1021 in 
	let global_which_pred = Hashtbl.create 1021 in 
	
	SLProgram.iter 
		(fun proc_name lproc -> 
			let proc = desugar_labs lproc in 
			(* Removing dead code and recalculating everything *)
			let proc = SSyntax_Utils_Graphs.remove_unreachable_code proc true in
			
			let succ_table, pred_table = SSyntax_Utils_Graphs.get_succ_pred proc.proc_body proc.ret_label proc.error_label in 
			let which_pred = SSyntax_Utils_Graphs.compute_which_preds pred_table in  
			Hashtbl.iter 
				(fun (prev_cmd, cur_cmd) i ->
					Hashtbl.replace global_which_pred (proc_name, prev_cmd, cur_cmd) i)
				which_pred;
			
			SProgram.replace prog proc_name proc)
	lproc_list; 
	
	prog, global_which_pred


		
	 