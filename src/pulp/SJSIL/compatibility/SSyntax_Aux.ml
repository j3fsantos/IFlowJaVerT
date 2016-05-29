open Pulp_Syntax
open Pulp_Procedure

let register_labels cmd_list ret_label ex_label = 
	(* labels table *)
	let my_hash = Hashtbl.create 80021 in 
	
	(* retrieve label number from hashtable *)
	let label_to_number lab = 
		if (Hashtbl.mem my_hash lab)
			then (Hashtbl.find my_hash lab)
			else -1 in 
			
	(* associate labels with numbers *)
	let rec register_labels_rec cmd_list cur_len = 
		match cmd_list with 
		| [] -> ()
		| cmd :: cmd_list ->
			(match cmd.stmt_stx with 
				| Label l ->
						Hashtbl.add my_hash l cur_len;
					 	if ((l != ret_label) && (l != ex_label)) 
							then register_labels_rec cmd_list cur_len
							else register_labels_rec cmd_list (cur_len + 1)   		 
				| _ -> register_labels_rec cmd_list (cur_len + 1)) in 
		
		(* main code *)
		register_labels_rec cmd_list 0;
		label_to_number
		
let get_fresh_vars name =
  let counter = ref 0 in
  let f _ =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f

let try_find table entry = 
	let value = try
		Some (Hashtbl.find table entry)
	with _ -> None in
	value
	
let rec tabs_to_str i  = 
	if i == 0 then "" else "\t" ^ (tabs_to_str (i - 1))

let spec_function_get_args sf = match sf with
  | GetValue expr -> [expr]
  | PutValue (expr1, expr2) -> [expr1; expr2]
  | Get (expr1, expr2) -> [expr1; expr2]
  | HasProperty (expr1, expr2) -> [expr1; expr2]
  | DefaultValue _ ->  raise (Failure "Generated JSIL code should not contain calls to DefaultValue")
  | ToPrimitive (expr1, _) -> [ expr1 ]
  | ToBoolean expr -> [expr] 
  | ToNumber expr -> [expr]
  | ToNumberPrim expr -> [expr]
  | ToString expr -> [expr] 
  | ToStringPrim expr -> [expr]
  | ToObject expr -> [expr]
  | CheckObjectCoercible expr -> [expr]
  | IsCallable expr -> [expr]
  | AbstractRelation (expr1, expr2, _) ->  [expr1; expr2] 
  | StrictEquality (expr1, expr2) -> [expr1; expr2]
  | StrictEqualitySameType (expr1, expr2) -> [expr1; expr2]
