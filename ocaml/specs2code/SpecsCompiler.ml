open JSIL_Syntax


let rec get_definable_vars le : string list =
	match le with 
	| LVar x -> [ x ]
	| LEList les -> List.concat (List.map get_definable_vars les) 
	| _ -> []


let partition_assertion a = 
	let rec partition_aux a def_as cons_as = 
		match a with 
		| LAnd  (a1, a2) 
		| LStar (a1, a2) -> 
			let def_as_1, cons_as_1 = partition_aux a1 def_as cons_as in 
			let def_as_2, cons_as_2 = partition_aux a2 def_as_1 cons_as_1 in 
			def_as_2, cons_as_2 

		| LOr (_, _) -> def_as, (a :: cons_as)

		| LNot _     -> def_as, (a :: cons_as)

		| LTrue      -> def_as, cons_as 

		| LFalse     -> raise (Failure "False cannot occur in the spec")

		| LEq (LVar x, le) 
		| LEq (le, LVar x) -> 
			let le_vars = JSIL_Logic_Utils.get_expr_vars_lst le false in 
			((x, le_vars, a) :: def_as), cons_as

		| LEq (LEList les, le) 
		| LEq (le, LEList les) ->
			let definable_vars = (get_definable_vars (LEList les)) in 
			if (definable_vars = []) then def_as, (a :: cons_as) else (
				let le_vars = JSIL_Logic_Utils.get_expr_vars_lst le false in 
				let new_def_as = List.map (fun x -> (x, le_vars, a)) definable_vars in 
				(new_def_as @ def_as), cons_as 
			)

		| LLess (_, _) 
		| LLessEq (_, _) 
		| LStrLess (_, _) 
		| LTypes _ 
		| LEmptyFields _ -> def_as, (a :: cons_as)

		| LEmp -> def_as, cons_as

		| LPointsTo (le1, le2, le3) -> 
			let definable_vars = (get_definable_vars le3) in 
			if (definable_vars = []) then def_as, (a :: cons_as) else (
				let le_vars = JSIL_Logic_Utils.get_expr_vars_lst (LBinOp (le1, Equal, le2)) false in 
				let new_def_as = List.map (fun x -> (x, le_vars, a)) definable_vars in 
				(new_def_as @ def_as), cons_as 
			) 

		| LPred (pred_name, les) -> 
			match les with 
			| le1 :: le2 :: rest_les -> 
				let definable_vars = List.concat (List.map get_definable_vars rest_les) in 
				if (definable_vars = []) then def_as, (a :: cons_as) else (
					let le_vars = JSIL_Logic_Utils.get_expr_vars_lst (LBinOp (le1, Equal, le2)) false in 
					let new_def_as = List.map (fun x -> (x, le_vars, a)) definable_vars in 
					(new_def_as @ def_as), cons_as
				)
			| _  -> 
				let msg = Printf.sprintf "I do not know how to treat the predicate %s yet!" pred_name in 
				raise (Failure msg) in 

	partition_aux a [] [] 
			



let make_resolve_logical_vars_code pre = []
	(* let def_as, cons_as = partition_assertion pre in 
    let def_as = order_partition def_as in *)


let make_ret_code post proc = []

let make_spec_executable proc spec = 
	let pre = spec.pre in 
	let post = spec.post in 
	let ret_flag = spec.ret_flag in 
	let pre_code = make_resolve_logical_vars_code pre in 
	let ret_code = make_ret_code post proc in 
	pre_code @ ret_code 


let make_final_code proc = []


let generate_proc_body_from_specs proc specs =
	let executable_specs = List.concat (List.map (fun spec -> make_spec_executable proc spec) specs) in  
	let executable_specs = executable_specs @ (make_final_code proc) in 
	Array.of_list executable_specs 


let make_executable_specs procs = 
	let new_procs = Hashtbl.create big_tbl_size in 
	Hashtbl.iter
		(fun proc_name proc -> 
			match proc.lspec with 
			| None -> Hashtbl.add new_procs proc_name proc
			| Some specs -> 
				let new_proc_body = generate_proc_body_from_specs proc specs.proc_specs in 
				let new_proc = { proc with lproc_body = new_proc_body } in 
				Hashtbl.add new_procs proc_name new_proc)
		procs; 
	new_procs 



	