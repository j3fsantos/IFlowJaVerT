open JSIL_Syntax


let rec get_definable_vars le : string list =
	match le with 
	| LVar x -> [ x ]
	| LEList les -> List.concat (List.map get_definable_vars les) 
	| _ -> []

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



	