open JSIL_Syntax

let verbose_ssa = ref false 

let get_assignments_per_var cmds  = 
	
	let assignments_per_var = Hashtbl.create 1021 in 
	let num_vars = ref 0 in 
	let number_of_cmds = Array.length cmds in 
	
	for i=0 to number_of_cmds-1 do 
		let cmd = cmds.(i) in 
		match cmd with 
			| SBasic (SAssignment (var, _)) 
			| SBasic (SLookup (var, _, _))
			| SBasic (SNew var) 
			| SBasic (SHasField (var, _, _))
		  | SBasic (SGetFields (var, _))
			| SBasic (SArguments var)
			| SCall (var, _, _, _) ->	
				let var_assignments = SSyntax_Aux.try_find assignments_per_var var in 
					(match var_assignments with 
					| None -> 
							num_vars := (!num_vars) + 1;
							Hashtbl.add assignments_per_var var [ i ]
					| Some lst -> Hashtbl.replace assignments_per_var var (i :: lst))
			| _ -> ()
	done;		
	assignments_per_var, !num_vars
	
(** 
 Algorithm that finds where to insert the phi-nodes
 *)		
let get_phi_functions_per_var var (var_asses : int list) dom_frontiers phi_nodes_table number_of_nodes = 
	
	let work_list_flags : bool array = Array.make number_of_nodes false in
	let work_list = Stack.create () in 

	List.iter 
		(fun u ->  
			work_list_flags.(u) <- true; 
			Stack.push u work_list)
		var_asses;
	
	while (not (Stack.is_empty work_list)) do
		let u = Stack.pop work_list in 
			List.iter 
				(fun v -> 
					if (not (Hashtbl.mem phi_nodes_table (var, v)))
					then  
						(Hashtbl.add phi_nodes_table (var, v) true;  
						(if (not work_list_flags.(v)) 
							then 
								(work_list_flags.(v) <- true;
								Stack.push v work_list)
							else ()))
					else ())
			dom_frontiers.(u)
	done

let insert_phi_functions (nodes : (jsil_metadata * jsil_cmd) array) dom_frontiers number_of_nodes = 
	
	let phi_nodes_table = Hashtbl.create 1021 in 
	let nodes = Array.map (fun x -> match x with (_, cmd) -> cmd) nodes in
	let assignments_per_var, _ = get_assignments_per_var nodes in 
	let phi_functions_per_node = Array.make number_of_nodes [] in 
	
	Hashtbl.iter
		(fun var (var_ass_nodes : int list) -> 
			get_phi_functions_per_var var var_ass_nodes dom_frontiers phi_nodes_table number_of_nodes)
		assignments_per_var; 
	
	Hashtbl.iter 
		(fun (var, u) b -> 
			phi_functions_per_node.(u) <- var :: phi_functions_per_node.(u))
		phi_nodes_table; 
		
	phi_functions_per_node	 
				
		
(** 
 *
 * SSA main algorithm: phi-nodes insertion algorithm 
 *)
let rec rewrite_expr_ssa (expr : jsil_expr) var_stacks rename_var  = 
	match expr with 
	|	Literal l -> Literal l 
	| Var var -> 
		let var_stack = SSyntax_Aux.try_find var_stacks var in 
		(match var_stack with 
		| Some (i :: lst) -> Var (rename_var var i)
		| _ -> raise (Failure ("RE: Variable " ^ (Printf.sprintf("%s") var) ^ " not found in stack table during ssa transformation")))
 	| BinOp (e1, binop, e2) ->
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
		let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in 
		BinOp (new_e1, binop, new_e2)
	| UnaryOp (un_op, e1) -> 
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
		UnaryOp (un_op, new_e1) 
	| VRef (e1, e2) -> 
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
		let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in 
		VRef (new_e1, new_e2) 
	| ORef (e1, e2) -> 
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
		let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in 
		ORef (new_e1, new_e2)  
 	| Base e1 -> 
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in
		Base (new_e1)
	| Field e1 -> 
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in
		Field (new_e1)
	| TypeOf e1 -> 
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in
		TypeOf (new_e1)
  | EList ll -> 
			(match ll with
			| [] -> EList []
			| e1 :: ll ->
				let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in
				let new_ll = rewrite_expr_ssa (EList ll) var_stacks rename_var in
						(match new_ll with
						| EList new_ll -> EList (new_e1 :: new_ll)
						| _ -> raise (Failure "Non-list construct")))
	| LstNth (e1, n) ->
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in
		LstNth (new_e1, n)
	| StrNth (e1, n) ->
		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in
		StrNth (new_e1, n)

let rec rewrite_logic_expression (lexpr : jsil_logic_expr) var_stacks rename_var = 
	(match lexpr with
	| PVar var ->
		let var_stack = SSyntax_Aux.try_find var_stacks var in 
		(match var_stack with 
		| Some (i :: lst) -> PVar (rename_var var i)
		| _ -> raise (Failure ("RLE: Variable " ^ (Printf.sprintf("%s") var) ^ " not found in stack table during ssa transformation")))
	| LBinOp (lexpr1, binop, lexpr2) -> LBinOp	((rewrite_logic_expression lexpr1 var_stacks rename_var), binop, (rewrite_logic_expression lexpr2 var_stacks rename_var))
	| LUnOp	(unop, lexpr1) ->	LUnOp (unop, rewrite_logic_expression lexpr1 var_stacks rename_var)
	| LEVRef (lexpr1, lexpr2) -> LEVRef	((rewrite_logic_expression lexpr1 var_stacks rename_var), (rewrite_logic_expression lexpr2 var_stacks rename_var))
	| LEORef (lexpr1, lexpr2) -> LEORef	((rewrite_logic_expression lexpr1 var_stacks rename_var), (rewrite_logic_expression lexpr2 var_stacks rename_var))
	| LBase	lexpr -> LBase (rewrite_logic_expression lexpr var_stacks rename_var)
	| LField lexpr -> LField (rewrite_logic_expression lexpr var_stacks rename_var)
	| LTypeOf lexpr	-> LTypeOf (rewrite_logic_expression lexpr var_stacks rename_var)
	| x -> x)
		
let rec rewrite_logic_assertion lass var_stacks rename_var = 
	  (match lass with
	   | LAnd	(lass1, lass2) -> LAnd ((rewrite_logic_assertion lass1 var_stacks rename_var), (rewrite_logic_assertion lass2 var_stacks rename_var))
	   | LOr (lass1, lass2) ->	LOr ((rewrite_logic_assertion lass1 var_stacks rename_var), (rewrite_logic_assertion lass2 var_stacks rename_var))
	   | LNot	lass1 -> LNot (rewrite_logic_assertion lass1 var_stacks rename_var)
	   | LStar (lass1, lass2) ->	LStar ((rewrite_logic_assertion lass1 var_stacks rename_var), (rewrite_logic_assertion lass2 var_stacks rename_var))
	  (* | LExists (lvl, lass1) -> LExists (lvl, (rewrite_logic_assertion lass1 var_stacks rename_var))
	   | LForAll (lvl, lass1) ->	LForAll (lvl, (rewrite_logic_assertion lass1 var_stacks rename_var)) *)
	   | LEq (lexpr1, lexpr2) -> LEq ((rewrite_logic_expression lexpr1 var_stacks rename_var), (rewrite_logic_expression lexpr2 var_stacks rename_var))	
	   | LLessEq (lexpr1, lexpr2) -> LLessEq ((rewrite_logic_expression lexpr1 var_stacks rename_var), (rewrite_logic_expression lexpr2 var_stacks rename_var))
	   | LPointsTo (lexpr1, lexpr2, lexpr3) -> LPointsTo ((rewrite_logic_expression lexpr1 var_stacks rename_var), (rewrite_logic_expression lexpr2 var_stacks rename_var), (rewrite_logic_expression lexpr3 var_stacks rename_var))
	   | LTrue -> LTrue
	   | LFalse -> LFalse
	   | LEmp -> LEmp
		)	

let rewrite_option_logic_assertion (olass : jsil_logic_assertion option) var_stacks rename_var = 
	match olass with
	| None -> None
	| Some lass -> Some (rewrite_logic_assertion lass var_stacks rename_var)

let rewrite_non_assignment_ssa cmd var_stacks rename_var = 
	match cmd with 
	| SBasic (SSkip) -> SBasic (SSkip) 
	| SBasic (SMutation (e1, e2, e3)) ->
			let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
			let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in
			let new_e3 = rewrite_expr_ssa e3 var_stacks rename_var in
			SBasic (SMutation (new_e1, new_e2, new_e3))
	| SBasic (SDelete (e1, e2)) ->
	 		let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
			let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in
			SBasic (SDelete (new_e1, new_e2))
	| SGoto j -> SGoto j
	| SGuardedGoto (e, i, j) -> 
		let new_e = rewrite_expr_ssa e var_stacks rename_var in 
		SGuardedGoto (new_e, i, j) 
	| _ ->
		let cmd_str = (JSIL_Print.string_of_cmd (make_empty_metadata, cmd) 0 0 false false false) in  
		raise (Failure ("Cannot Rewrite the command " ^ cmd_str ^ " using in the non-assignment case of SSA Rewriting")) 

let rename_var = fun (var : string) (i : int) -> var ^ "_" ^ (string_of_int i) 

let rename_params params = 
	let rec loop params new_params = 
		match params with 
		| [] -> new_params 
		| param :: rest_params -> 
			let new_param = rename_var param 0 in 
			loop rest_params (new_param :: new_params) in 
	loop params [] 

let print_phi_functions_per_node phi_functions_per_node = 
		
	let number_of_nodes = Array.length phi_functions_per_node in 
	let str = "Phi-functions per node: \n" in 
	
	let rec loop u cur_str =  
		if u >= number_of_nodes 
			then cur_str
			else 
				let phi_functions_for_u = phi_functions_per_node.(u) in 
				let str_u = (match phi_functions_for_u with 
					| [] -> "" 
					| [ v ] -> v
					| v :: rest_phi_functions ->  
							List.fold_left (fun acc x -> acc ^ ", " ^ x) v rest_phi_functions) in 
				let str_u = Printf.sprintf "%d must have phi-nodes for: %s\n" u str_u in 
				loop (u+1) (cur_str ^ str_u) in 
	
	loop 0 str

let insert_phi_args args vars cmds (spec : jsil_spec option) (rvar : string option) (evar : string option) 
                    (ret_lab : int option) (err_lab : int option) succ pred idom_table idom_graph phi_functions_per_node which_pred = 
	
	let metadata = make_empty_metadata in 
	
	let var_counters : (string, int) Hashtbl.t  = Hashtbl.create 1021 in 
	let var_stacks :  (string, int list) Hashtbl.t = Hashtbl.create 1021 in 
	
	let number_of_nodes = Array.length succ in
	let new_cmds = Array.make number_of_nodes (metadata, SBasic SSkip) in 
	let new_phi_functions_per_node = Array.make number_of_nodes [] in 
	
	let new_ret_var = ref (match rvar with | None -> "" | Some rvar -> rvar) in
	let new_err_var = ref (match evar with | None -> "" | Some evar -> evar) in
	
	let spec_len = 
		(match spec with
		| None -> 0
		| Some spec -> List.length spec.proc_specs) in
	
	let new_pres  = Array.make spec_len (LTrue) in
	let new_posts = Array.make spec_len (LTrue) in
	let flags     = Array.make spec_len Normal in
	
	(if (!verbose_ssa) 
		then
			let which_pred_str = Graph_Print.string_of_which_pred which_pred in  
			Printf.printf "Computed which pred %s\n " which_pred_str 
		else ()); 
	
	List.iter 
		(fun var -> 
			Hashtbl.add var_counters var 0;
			Hashtbl.add var_stacks var [])
		vars;
	
	List.iter 
		(fun var -> 
			Hashtbl.add var_counters var 1;
			Hashtbl.add var_stacks var [ 0 ])
		args;
	
	
	for u = 0 to number_of_nodes - 1 do
		let u_number_of_pred = (List.length pred.(u)) in 
		let u_phi_functions = phi_functions_per_node.(u) in 
		let new_u_phi_functions = 
			(List.map 
				(fun v -> v, (Array.make u_number_of_pred (-1)), v)
		 		u_phi_functions) in 
		new_phi_functions_per_node.(u) <- new_u_phi_functions
	done;

	(* split specs into pre, post, normal *)
	
  if (!verbose_ssa) then
		Printf.printf "Rewriting pre-conditions.\n";
	
	(match spec with
	| None -> ()
	| Some spec ->
		let specs_array = Array.of_list spec.proc_specs in
		for u = 0 to (spec_len - 1) do
			new_pres.(u) <- (rewrite_logic_assertion specs_array.(u).pre var_stacks rename_var);
			new_posts.(u) <- specs_array.(u).post;
			flags.(u) <- specs_array.(u).ret_flag;
		done);
	
	 if (!verbose_ssa) then
		Printf.printf "Finished rewriting pre-conditions.\n";
	
	let new_params = 
		match spec with
		| None -> []
		| Some spec -> rename_params spec.spec_params in

	let rec ipa_rec u = 
		
 		let cmd = cmds.(u) in 
		
		let rec loop phi_nodes processed_phi_nodes = 
			match phi_nodes with 
			| [] -> 
				new_phi_functions_per_node.(u) <- processed_phi_nodes
			| (_, v_args, old_var) :: rest_phi_nodes -> 
				let var_index : int option = SSyntax_Aux.try_find var_counters old_var in
				let var_stack : int list option = SSyntax_Aux.try_find var_stacks old_var in 
				(match var_index, var_stack with 
 				| (Some index), (Some v_stack) ->
 					Hashtbl.replace var_counters old_var (index + 1);  
 					Hashtbl.replace var_stacks old_var (index :: v_stack);
					let new_var = rename_var old_var index in 
					loop rest_phi_nodes ((new_var, v_args, old_var) :: processed_phi_nodes)
 				| _ -> 
					let err_msg = Printf.sprintf "Variable %s not found in stack table during ssa transformation - 1st phase - phi assignment.\n" old_var in 
					raise (Failure err_msg)) in 
		
		let phi_nodes_for_u = new_phi_functions_per_node.(u) in 
		loop phi_nodes_for_u []; 
 		
		(if (!verbose_ssa) then Printf.printf "Finished processing the lhs for the phi-nodes in %d!\n" u else ()); 
		
		let v_stack_and_counter_update var = 
			let var_index : int option = SSyntax_Aux.try_find var_counters var in
 			let var_stack : int list option = SSyntax_Aux.try_find var_stacks var in 
			(if (!verbose_ssa) then Printf.printf "Processing an assignment to variable %s\n " var else ()); 
 			(match var_index, var_stack with 
 			| (Some index), (Some v_stack) ->
				let str_stack = 
					(match v_stack with 
					| [] -> "[]" 
					| [ v ] -> "[" ^ (string_of_int v) ^ "]"  
					| v :: rest_stack -> 
						(List.fold_left 
							(fun ac v -> ac ^ ", " ^ (string_of_int v)) 
							("[" ^ (string_of_int v))
							rest_stack) ^ "]") in 
				(if (!verbose_ssa) then Printf.printf "\t Index: %d, Stack: %s\n " index str_stack else ());
 				Hashtbl.replace var_counters var (index + 1);  
 				Hashtbl.replace var_stacks var (index :: v_stack); 
				index
			| _ ->
				let err_msg = Printf.sprintf "Variable %s not found in stack table during ssa transformation - 1st phase - ordinary assignment.\n" var in 
				raise (Failure err_msg)) in
		
		let metadata, command = cmd in
		let spec = metadata.pre_cond in 
		let new_spec = rewrite_option_logic_assertion spec var_stacks rename_var in
		let new_metadata = { metadata with pre_cond = new_spec } in 
 		let new_ass = (match command with 
 		| SBasic (SAssignment (var, expr)) -> 
 			let new_expr : jsil_expr = rewrite_expr_ssa expr var_stacks rename_var in
			let index = v_stack_and_counter_update var in
 			SBasic (SAssignment ((rename_var var index), new_expr)) 
			
 		| SBasic (SLookup (var, e1, e2)) ->
			let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
			let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in
			let index = v_stack_and_counter_update var in 
			SBasic (SLookup ((rename_var var index), new_e1, new_e2))
		
		| SBasic (SNew var) -> 
			let index = v_stack_and_counter_update var in 
			SBasic (SNew (rename_var var index)) 
		
		| SBasic (SHasField (var, e1, e2)) ->
			let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
			let new_e2 = rewrite_expr_ssa e2 var_stacks rename_var in
			let index = v_stack_and_counter_update var in
			SBasic (SHasField ((rename_var var index), new_e1, new_e2))	

		| SBasic (SGetFields (var, e1)) ->
			let new_e1 = rewrite_expr_ssa e1 var_stacks rename_var in 
			let index = v_stack_and_counter_update var in
			SBasic (SGetFields ((rename_var var index), new_e1))	
			
		| SBasic (SArguments var) ->
			let index = v_stack_and_counter_update var in
			SBasic (SArguments (rename_var var index))
			
		| SCall (var, e, le, j) ->
			let new_e = rewrite_expr_ssa e var_stacks rename_var in 
			let new_le = List.map 
				(fun e -> rewrite_expr_ssa e var_stacks rename_var)
				le in 
			let index = v_stack_and_counter_update var in
			SCall((rename_var var index), new_e, new_le, j)  
		
		| cmd -> rewrite_non_assignment_ssa cmd var_stacks rename_var) in 
		new_cmds.(u) <- (new_metadata, new_ass);
		
		(match ret_lab with
		| None -> ()
		| Some ret_lab ->
			if (u = ret_lab) then
			begin
  			new_ret_var := (let var_stack = SSyntax_Aux.try_find var_stacks !new_ret_var in
  		    (match var_stack with 
  		      | Some (i :: lst) -> (rename_var !new_ret_var i)
  		      | _ -> raise (Failure ("Return label: Variable " ^ (Printf.sprintf("%s") !new_ret_var) ^ " not found in stack table during ssa transformation"))));
  			for k = 0 to (spec_len - 1) do
  				if (flags.(k) = Normal) then
  					new_posts.(k) <- (rewrite_logic_assertion new_posts.(k) var_stacks rename_var);
  			done;
			end);

		(match err_lab with
		| None -> ()
		| Some err_lab -> 
	  	if (u = err_lab) then
			begin
  			new_err_var := (let var_stack = SSyntax_Aux.try_find var_stacks !new_err_var in
  		    (match var_stack with 
  		      | Some (i :: lst) -> (rename_var !new_err_var i)
  		      | _ -> raise (Failure ("Error label: Variable " ^ (Printf.sprintf("%s") !new_ret_var) ^ " not found in stack table during ssa transformation"))));
  			for k = 0 to (spec_len - 1) do
  				if (flags.(k) = Error) then
  					new_posts.(k) <- (rewrite_logic_assertion new_posts.(k) var_stacks rename_var);
  			done;
			end);
			

		(if (!verbose_ssa) then Printf.printf "Finished processing the lhs for the node %d!\n" u else ());
		
 		let u_successors = succ.(u) in
 		List.iter 
 			(fun k -> 
				Printf.printf "Processing statement: %s\n" (JSIL_Print.string_of_cmd cmds.(k) 0 0 false false false);
 				let j = SSyntax_Aux.try_find which_pred (u, k) in
				match j with 
				| Some j -> 
					(if (!verbose_ssa) then Printf.printf "%d is the %d^th predecessor of %d!\n" u k (j+1) else ()); 
 					List.iter 
 				  	(fun (v, args, old_v) -> 
 							let v_stack = SSyntax_Aux.try_find var_stacks old_v in 
 							(match v_stack with 
 							| Some (i :: rest) -> 
 								args.(j) <- i  
 							| _ -> 
								args.(j) <- -1)
 						)
 						new_phi_functions_per_node.(k)
				| None -> 
					let err_msg = Printf.sprintf  "%d is a predecessor of %d but I do not know which one.\n" u k in 
					raise (Failure err_msg))
 			u_successors; 
 		
		(if (!verbose_ssa) then Printf.printf "Finished processing the successors!\n" else ()); 
		
		List.iter 
			(fun v -> ipa_rec v)
			idom_graph.(u); 
		
		(let spec, command = cmd in
		match command with 
 		| SBasic (SAssignment (var, _)) 
		| SBasic (SLookup (var, _, _))
		| SBasic (SNew var) 
		| SBasic (SHasField (var, _, _))
		| SBasic (SGetFields (var, _))
	  | SBasic (SArguments var)
		| SCall (var, _, _, _) ->
			let var_stack = SSyntax_Aux.try_find var_stacks var in 
 			(match var_stack with 
 			| Some (hd :: rest_stack)  ->
 				Hashtbl.replace var_stacks var rest_stack; 
			| _ ->
				let err_msg = Printf.sprintf "Not sure where: Variable %s not found in stack table during ssa transformation.\n" var in 
				raise (Failure err_msg))
		| _ -> ()); 
		
		let rec loop phi_nodes = 
			match phi_nodes with 
			| [] -> ()
			| (var, v_args, old_var) :: rest_phi_nodes -> 
				let var_stack = SSyntax_Aux.try_find var_stacks old_var in 
 				(match var_stack with 
 				| Some (hd :: rest_stack)  ->
 					Hashtbl.replace var_stacks old_var rest_stack; 
				| _ ->
					let err_msg = Printf.sprintf "Variable %s has an empty stack...\n" old_var in   
					raise (Failure err_msg));
				loop rest_phi_nodes in
		
		let phi_nodes_for_u = new_phi_functions_per_node.(u) in 
		loop phi_nodes_for_u in 
			
	ipa_rec 0; 

	let new_spec : jsil_spec option =
	(match spec with
	| None -> None
	| Some spec -> Some
		{
			spec_name = spec.spec_name;
			spec_params = new_params;
			proc_specs =
				let new_specs = Array.make spec_len 
					{ 
						pre = LTrue;
						post = LTrue;
						ret_flag = Normal;
					} in 
				for u = 0 to (spec_len - 1) do
					new_specs.(u) <- 
						{
							pre = new_pres.(u);
							post = new_posts.(u);
							ret_flag = flags.(u);
						}
				done;
				(Array.to_list new_specs)
		}) in
	new_phi_functions_per_node, var_counters, new_cmds, new_spec, !new_ret_var, !new_err_var
 	
	
let create_phi_assignment var v_args old_var =
	let metadata = make_empty_metadata in  
	let len = Array.length v_args in 
	let new_v_args = Array.make len None in 
	for i=0 to len-1 do 
		if (not (v_args.(i) = -1))
			then new_v_args.(i) <- Some (rename_var old_var v_args.(i))
			else ()
	done; 
	(metadata, SPhiAssignment (var, new_v_args))

let adjust_goto cmd displacements = 
	let spec, command = cmd in
	let new_command = 
	(match command with 
	| SGoto j -> SGoto (j + displacements.(j)) 
	| SGuardedGoto (e, i, j) -> SGuardedGoto (e, (i + displacements.(i)), (j + displacements.(j)))
	| SCall (var, e, le, j) -> SCall (var, e, le, match j with | None -> None | Some j -> Some (j + displacements.(j)))
	| x -> x) in
	(spec, new_command)

let insert_phi_nodes proc phi_functions_per_node (nodes : (jsil_metadata * jsil_cmd) array) new_spec new_ret_var new_err_var var_counters = 
	
	let number_of_nodes : int = Array.length nodes in 
	let phi_assignments_per_node : ((jsil_metadata * jsil_cmd) list) array = Array.make	number_of_nodes [] in 
	let jump_displacements = Array.make number_of_nodes 0 in 
	
	let rec create_phi_assignments u phi_nodes_u n = 
		match phi_nodes_u with 
		| [] -> n
		| (var, v_args, old_var) :: rest_phi_nodes -> 
				let new_phi_assignment = create_phi_assignment var v_args old_var in 
				phi_assignments_per_node.(u) <- new_phi_assignment :: phi_assignments_per_node.(u); 
				create_phi_assignments u rest_phi_nodes (n + 1) in
	
	let ac_jump_displacement = ref 0 in 
	for u=0 to (number_of_nodes-1) do  
		jump_displacements.(u) <- (!ac_jump_displacement);
		(if (!verbose_ssa) then Printf.printf ("Displacement of node %s: %s\n") (string_of_int u) (string_of_int (!ac_jump_displacement)) else ()); 
		let u_displacement = create_phi_assignments u phi_functions_per_node.(u) 0 in 
		ac_jump_displacement := u_displacement + (!ac_jump_displacement);
	done;
	
	let rec loop u processed_cmds = 
		if (u >= number_of_nodes) 
			then List.rev processed_cmds
			else 
				(let processed_cmd = adjust_goto nodes.(u) jump_displacements in 
				let new_processed_cmds : (jsil_metadata * jsil_cmd) list = List.append (phi_assignments_per_node.(u)) processed_cmds in 
				let new_processed_cmds : (jsil_metadata * jsil_cmd) list = processed_cmd :: new_processed_cmds  in 
				loop (u + 1) new_processed_cmds) in 
	
	let new_cmds =  loop 0 [] in
	let new_cmds = Array.of_list new_cmds in
	let new_params = List.map
		(fun param -> rename_var param 0)
		proc.proc_params in 
	
	let ret_label = proc.ret_label in
	let new_ret_label = 
		(match ret_label with
		 | None -> None
		 | Some lab -> Some (lab + jump_displacements.(lab) + (List.length (phi_assignments_per_node.(lab))))) in
	let new_ret_var = 
		(match new_ret_var with
		  | "" -> None
			| x -> Some x) in
	
	let error_label = proc.error_label in
	let new_error_label = 
		(match error_label with
		 | None -> None
		 | Some lab -> Some (lab + jump_displacements.(lab) + (List.length (phi_assignments_per_node.(lab))))) in
	let new_error_var = 
		(match new_err_var with
		  | "" -> None
			| x -> Some x) in
	{ 
		proc_name = proc.proc_name; 
		proc_body = new_cmds; 
		proc_params = new_params; 
		ret_label = new_ret_label;
		ret_var = new_ret_var; 
		error_label = new_error_label; 
		error_var = new_error_var;
		spec = new_spec;
	}
 

let ssa_compile_proc proc (vars : string list) (nodes : (jsil_metadata * jsil_cmd) array) succ_table pred_table parent_table dfs_num_table_f dfs_num_table_r which_pred = 
	let args : string list = proc.proc_params in 
	let number_of_nodes = Array.length succ_table in
  (* compute dominators using the Lengauer Tarjan Algorithm *)
	let dom_table, rev_dom_table = JSIL_Utils_Graphs.lt_dom_algorithm succ_table pred_table parent_table dfs_num_table_f dfs_num_table_r in
	(* compute dominance frontiers using Cytron algorithm *) 
	let dominance_frontiers = JSIL_Utils_Graphs.find_dominance_frontiers succ_table dom_table rev_dom_table in 
	(* compute which nodes need phi variables *)
	let phi_functions_per_node_init = insert_phi_functions nodes dominance_frontiers number_of_nodes in 
	(* compute the arguments of the phi nodes and rewrite all the nodes *)
	let phi_functions_per_node, var_counters, new_cmds, new_spec, new_ret_var, new_err_var = insert_phi_args 
			args vars nodes proc.spec proc.ret_var proc.error_var proc.ret_label proc.error_label succ_table pred_table dom_table rev_dom_table phi_functions_per_node_init which_pred in
	(* insert the phi nodes in the program *)
	let new_proc = insert_phi_nodes proc phi_functions_per_node new_cmds new_spec new_ret_var new_err_var var_counters in
	rev_dom_table, dominance_frontiers, phi_functions_per_node_init, new_proc

(** Given a JSIL program 'prog' (Hashtbl: String --> Procedure), compiles its procedures into SSA form. *)
let ssa_compile_prog prog = 
	let ssa_prog = Hashtbl.create 1021 in 
	let global_which_pred = Hashtbl.create 1021 in 
	
	Hashtbl.iter 
		(fun proc_name proc -> 
			let nodes, vars, succ_table, pred_table, tree_table, parent_table, dfs_num_table_f, dfs_num_table_r, which_pred = 
				JSIL_Utils.get_proc_info proc in 
			let rev_dom_table, dominance_frontiers, phi_functions_per_node, new_proc = 
  			ssa_compile_proc proc vars nodes succ_table pred_table parent_table dfs_num_table_f dfs_num_table_r which_pred in 
			
			let new_succ_table, new_pred_table = JSIL_Utils_Graphs.get_succ_pred new_proc.proc_body new_proc.ret_label new_proc.error_label in 
			let new_which_pred = JSIL_Utils_Graphs.compute_which_preds new_pred_table in  
			Hashtbl.iter 
				(fun (prev_cmd, cur_cmd) i ->
					Hashtbl.replace global_which_pred (proc_name, prev_cmd, cur_cmd) i)
				new_which_pred;
			
			Hashtbl.replace ssa_prog proc_name proc)
		prog; 
	ssa_prog, global_which_pred
