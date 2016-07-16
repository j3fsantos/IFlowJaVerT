open SSyntax
open Lexing

let verbose = ref false

let if_some p f d =
	(match p with
	| None -> d
	| Some p -> f p)

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
	if (!verbose) then Printf.printf "%s" (SSyntax_Print.string_of_procedure proc false);
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

let parse_proc_with_error lexbuf = 
	try SJSIL_Parser.proc_target SJSIL_Lexer.read lexbuf with
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

let lprog_of_string str = 
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
  let (imports, lproc_list) : (string list option * lprocedure list) = parse_with_error lexbuf in	
	();
	
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


let proc_of_string str = 
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
  let lproc : lprocedure = parse_proc_with_error lexbuf in	
	desugar_labs lproc		

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
			(* Removing dead code and recalculating everything 
			let proc = SSyntax_Utils_Graphs.remove_unreachable_code proc false in
			let proc = SSyntax_Utils_Graphs.remove_unreachable_code proc true in *)
			
			let succ_table, pred_table = SSyntax_Utils_Graphs.get_succ_pred proc.proc_body proc.ret_label proc.error_label in 
			let which_pred = SSyntax_Utils_Graphs.compute_which_preds pred_table in  
			Hashtbl.iter 
				(fun (prev_cmd, cur_cmd) i ->
					Hashtbl.replace global_which_pred (proc_name, prev_cmd, cur_cmd) i)
				which_pred;
			
			SProgram.replace prog proc_name proc)
	lproc_list; 
	
	prog, global_which_pred



let extend_which_pred global_which_pred proc = 
	let succ_table, pred_table = SSyntax_Utils_Graphs.get_succ_pred proc.proc_body proc.ret_label proc.error_label in 
	let which_pred = SSyntax_Utils_Graphs.compute_which_preds pred_table in  
	let proc_name = proc.proc_name in 
	Hashtbl.iter 
		(fun (prev_cmd, cur_cmd) i ->
			Hashtbl.replace global_which_pred (proc_name, prev_cmd, cur_cmd) i)
		which_pred	


(**
		WHICH_PRED TRANSFORMATION

		1st: get the number of commands for each procedure
		     get the number of predecessors for each command
				
		2nd: construct the
*)

let to_array which_pred = 
	let wp_data : (string, (int, int) Hashtbl.t) Hashtbl.t = Hashtbl.create 1021 in
		Hashtbl.iter 
			(fun k v -> 
				match k with
				| (pn : string), (pc : int), (cc : int) -> 
					if (not (Hashtbl.mem wp_data pn)) then
						(let new_proc : (int, int) Hashtbl.t = Hashtbl.create 1021 in 
					    Hashtbl.add wp_data pn new_proc);
					let pwp : (int, int) Hashtbl.t = Hashtbl.find wp_data pn in
					let nmax = (try (Hashtbl.find pwp (-1)) with
					            | _ -> -1) in
						if (nmax < cc + 1) then (Hashtbl.replace pwp (-1) (cc + 1));
					let cmax = (try (Hashtbl.find pwp cc) with
					            | _ -> -1) in
 						if (cmax < v + 1) then (Hashtbl.replace pwp cc (v + 1))
				| _ -> raise (Failure "Incorrect which_pred structure."))
			which_pred;
	Hashtbl.iter 
	  (fun k v -> 
			let cnum = Hashtbl.find v (-1) in
			for n = 0 to (cnum - 1) do
				if (not (Hashtbl.mem v n)) then
					Hashtbl.add v n 0;
			done;) wp_data;
	let arr_wp : ((string, (int array) array) Hashtbl.t) = Hashtbl.create 1021 in
		Hashtbl.iter 
			(fun k v -> 
				match k with
				| (pn : string), (pc : int), (cc : int) -> 
					if (not (Hashtbl.mem arr_wp pn)) then
						(let pn_data = Hashtbl.find wp_data pn in
						 let cnum = Hashtbl.find pn_data (-1) in
						 let emp_arr : int array = Array.make 0 0 in
						 let pn_arr : (int array) array = Array.make cnum emp_arr in
						 for n = 0 to (cnum - 1) do
						   let pnum = Hashtbl.find pn_data n in
							 let arr : int array = Array.make pnum (-1) in
							 pn_arr.(n) <- arr;
						 done;
						 Hashtbl.add arr_wp pn pn_arr;
						);
					let pwp : (int array) array = Hashtbl.find arr_wp pn in
					  (pwp.(cc)).(v) <- pc; 
						Hashtbl.replace arr_wp pn pwp;
				| _ -> raise (Failure "Incorrect which_pred structure."))
			which_pred;
	arr_wp
	
let print_wp_array wp_array = 
	Hashtbl.iter 
	  (fun k v -> 
			Printf.printf "Procedure name: %s\n" k;
			let cnum = Array.length v in
			Printf.printf "Number of commands: %d\n" cnum;
			for n = 0 to (cnum - 1) do
				let npred = Array.length (v.(n)) in
				Printf.printf "CMD %d : Number of preds: %d : Preds : " n npred;
				for e = 0 to (npred - 1) do
					Printf.printf "%d " (v.(n)).(e);
				done;
				Printf.printf "\n";
			done;)
	  wp_array
		
