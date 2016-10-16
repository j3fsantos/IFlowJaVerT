open JSIL_Syntax

exception Non_unifiable of string

type normalised_predicate = {
	name         : string;
	num_params   : int;
	params       : jsil_var list;
	definitions  : jsil_logic_assertion list;
	is_recursive : bool;
}

let string_of_normalised_predicate (pred : normalised_predicate) =
    let params = List.fold_left (fun ac param -> ac ^ param ^ " ") "" pred.params in
    "\n*** Normalised predicate ***\n" ^
    "Name : " ^ pred.name ^ "\n" ^
    "Parameters : " ^ params ^ "\n" ^
    (Printf.sprintf "Recursive : %b\n" pred.is_recursive) ^
	List.fold_left (fun ac x -> ac ^ "\nDefinition:\n" ^ (JSIL_Print.string_of_logic_assertion x false) ^ "\n") "" pred.definitions

let string_of_normalised_predicates (preds : (string, normalised_predicate) Hashtbl.t) =
    Hashtbl.fold (fun pname pred ac -> ac ^ string_of_normalised_predicate pred) preds ""

let detect_trivia_and_nonsense norm_pred =
	let new_definitions = List.map
		(fun x ->
			let rx = JSIL_Logic_Utils.reduce_assertion x in
			(* Printf.printf "\nReduction:\n\n%s\n\nreduces to\n\n%s\n\n" (JSIL_Print.string_of_logic_assertion x false) (JSIL_Print.string_of_logic_assertion rx false); *)
			rx) norm_pred.definitions in
	let new_definitions = List.filter (fun x -> not (x = LFalse)) new_definitions in
	{ norm_pred with definitions = new_definitions }

(* Replaces the literals and None in the arguments of a predicate with logical variables,
   and adds constraints for those variables to its definitions.
*)
let replace_head_literals (pred : jsil_logic_predicate) =
	let norm_empty_pred =
		{ name         = pred.name;
		  num_params   = pred.num_params;
			params       = [];
			definitions  = pred.definitions;
			is_recursive = false             } in
	List.fold_right
		(fun cur_param norm_pred ->
			(* Check each parameter in reverse order! *)
			match cur_param with
			| LLit _ | LNone -> (* If the parameter is a JSIL literal or None... *)
			  (* Get a fresh program variable and add a constraint to each definition *)
				let new_pvar = JSIL_Memory_Model.fresh_pvar () in
				let new_assertions =
					List.map
						(fun prev_ass -> LStar (prev_ass, LEq (PVar new_pvar, cur_param)))
						norm_pred.definitions in
				{ name         = norm_pred.name;
				  num_params   = norm_pred.num_params;
					params       = new_pvar :: norm_pred.params;
					definitions  = new_assertions;
					is_recursive = false }
			| PVar var -> (* If the parameter is a program variable, add the parameter as it is *)
				{ name         = norm_pred.name;
				  num_params   = norm_pred.num_params;
					params       = var :: norm_pred.params;
					definitions  = norm_pred.definitions;
					is_recursive = false }
			| _        -> (* Otherwise, it's an error *)
				raise (Failure ("Error in predicate " ^ norm_pred.name ^ ": Unexpected parameter."))
		)
		pred.params
		norm_empty_pred

(* Given a list of logical expressions and a list of program variables,
   returns a substitution for the elements of the second list.
*)
let unify_list_pvars l1 l2 =
	let subst = Hashtbl.create 10 in
	(* Compute and return the substitution of logic variables *)
	List.iter2
		(fun lexpr pvar2 ->
			if Hashtbl.mem subst (PVar pvar2)
			  then raise (Non_unifiable ("Duplicated parameter."))
				else Hashtbl.add subst (PVar pvar2) lexpr)
		l1 l2;
	subst


(* Replaces the logic_expressions in asrt that have a substitute in the hashtable subst *)
let apply_substitution subst asrt =
	JSIL_Logic_Utils.assertion_map
	  (fun lexpr -> (* Replace the logic expression if it has a substitute, but do not recurse *)
		  try
	      (Hashtbl.find subst lexpr, false)
	    with Not_found -> (lexpr, true))
	  asrt


(* Join two normalised_predicate defining different cases of the same predicate in a single
   normalised_predicate
*)
let join_pred pred1 pred2 =
	if pred1.name <> pred2.name || pred1.num_params <> pred2.num_params
	  then raise (Non_unifiable ("Incompatible predicate definitions."))
		else
		  let subst = unify_list_pvars (List.map (fun var -> PVar var) pred1.params) pred2.params in
		  let definitions = pred1.definitions @ (List.map (apply_substitution subst) pred2.definitions) in
		  { pred1 with definitions = definitions; is_recursive = pred1.is_recursive || pred2.is_recursive; }

(* Returns a list with the names of the predicates that occur in an assertion *)
let rec get_predicate_names asrt =
	let gp = get_predicate_names in
	match asrt with
	| LAnd (a1, a2)          -> (gp a1) @ (gp a2)
	| LOr (a1, a2)           -> (gp a1) @ (gp a2)
	| LNot a                 -> (gp a)
	| LStar (a1, a2)         -> (gp a1) @ (gp a2)
	| LPred (s, le)          -> [s]
	| LTrue | LFalse | LEq _ | LLess _ | LLessEq _ | LStrLess _ | LPointsTo _ | LEmp | LTypes _-> []

(* Given a Hashtbl of normalised predicates, return a Hashtbl from predicate name
   to boolean meaning "recursive" or "not recursive"
*)
let find_recursive_preds preds =
	let count = ref 0 in
	let visited = Hashtbl.create (Hashtbl.length preds) in
	let rec_table = Hashtbl.create (Hashtbl.length preds) in
	(* Searches by (sort of) Tarjan's SCC algorithm the predicate 'pred_name';
	   if recursive, returns the index where recursion starts, otherwise None *)
	let rec explore exploration_trail pred_name =
		try
			let ci = Hashtbl.find visited pred_name in
			(* Already explored *)
			if List.mem pred_name exploration_trail then
				(* Part of the current component: recusivity detected *)
				Some ci
			else
				(* A previously explored component *)
				None
		with Not_found ->
			(* Exploring for the first time *)
			let index = !count in
			count := !count + 1;
			Hashtbl.add visited pred_name index;
			let pred =
				(try Hashtbl.find preds pred_name with
				| Not_found -> raise (Failure ("Undefined predicate " ^ pred_name))) in
			let neighbours = (* Find the names of all predicates that the current predicate uses *)
				List.fold_left
				  (fun list asrt -> list @ (get_predicate_names asrt))
					[]
					pred.definitions in
			let min_index = (* Compute recursively the smallest index reachable from its neighbours *)
				List.fold_left
			    (fun min_so_far neighbour_name ->
						match (explore (pred_name :: exploration_trail) neighbour_name) with
						| None -> min_so_far
						| Some index -> min min_so_far index
					)
				  99999
				  neighbours in
			(* This predicate is recursive if we have seen an index smaller or equal than its own *)
			if min_index <= index then
				(Hashtbl.replace visited pred_name min_index;
				Hashtbl.add rec_table pred_name true;
				Some min_index)
			else
				(Hashtbl.add rec_table pred_name false;
			  None)
	in
	(* Launch the exploration from each predicate, unless it's already been visited in a previous one *)
	Hashtbl.iter
	  (fun name _ ->
			if not (Hashtbl.mem visited name)
			  then ignore(explore [] name))
		preds;
	rec_table

(* Cross product of two lists, l1 and l2, combining its elements with function f *)
(* 'a list -> 'b list -> ('a -> 'b -> 'c) -> 'c list *)
let cross_product l1 l2 f =
	List.fold_left
	  (fun result e1 ->
			result @ (List.map (f e1) l2))
		[]
		l1


let rec auto_unfold predicates asrt =
	let au = auto_unfold predicates in
	match asrt with
	| LAnd (a1, a2)          -> cross_product (au a1) (au a2) (fun asrt1 asrt2 -> LAnd (asrt1, asrt2))
	| LOr (a1, a2)           -> cross_product (au a1) (au a2) (fun asrt1 asrt2 -> LOr (asrt1, asrt2))
	| LNot a                 -> List.map (fun asrt -> LNot asrt) (au a)
	| LStar (a1, a2)         -> cross_product (au a1) (au a2) (fun asrt1 asrt2 -> LStar (asrt1, asrt2))
	| LPred (name, args)     ->
		(try
		  let pred = Hashtbl.find predicates name in
			if pred.is_recursive then
				(* If the predicate is recursive, return the assertion unchanged. *)
				[asrt]
			else
				(* If it is not, unify the formal parameters with the actual parameters, *)
				(* apply the substitution to each definition of the predicate, and recurse. *)
				let subst = unify_list_pvars args pred.params in
				let new_asrts = List.map (apply_substitution subst) pred.definitions in
				List.fold_left
				  (fun list asrt -> list @ (au asrt))
					[]
				  new_asrts

		 (* If the predicate is not found, raise an error *)
		with Not_found -> raise (Failure ("Error: Can't auto_unfold predicate " ^ name)))
	| LTrue | LFalse | LEq _ | LLess _ | LLessEq _ | LStrLess _ | LPointsTo _ | LEmp | LTypes _-> [asrt]

let normalise preds =
	let norm_predicates = Hashtbl.create 100 in
	Hashtbl.iter
		(fun name pred ->
			(* Substitute literals in the head for logical variables *)
			let (norm_pred : normalised_predicate) = replace_head_literals pred in
			try
				(* Join the new predicate definition with all previous for the same predicate (if any) *)
				let current_pred = Hashtbl.find norm_predicates name in
				Hashtbl.replace norm_predicates name (join_pred current_pred norm_pred);
			with
			| Not_found -> Hashtbl.add norm_predicates name norm_pred
			| Non_unifiable reason -> raise (Failure ("Error in predicate " ^ name ^ ": " ^ reason)))
		preds;
	(* Detect recursive predicates *)
  	let rec_table = find_recursive_preds norm_predicates in
	(* Flag those that are recursive *)
	let norm_rec_predicates = Hashtbl.create (Hashtbl.length norm_predicates) in
	Hashtbl.iter
	  (fun name pred ->
			Hashtbl.add norm_rec_predicates pred.name
			  { pred with is_recursive =
					(try Hashtbl.find rec_table name with
					| Not_found -> raise (Failure ("Undefined predicate " ^ name))); })
		norm_predicates;
	(* Auto-unfold the predicates in the definitions of other predicates *)
	let norm_rec_unfolded_predicates = Hashtbl.create (Hashtbl.length norm_rec_predicates) in
	Hashtbl.iter
	  (fun name pred ->
			Hashtbl.add norm_rec_unfolded_predicates pred.name
			(let ret_pred = { pred with definitions = List.flatten (List.map (auto_unfold norm_rec_predicates) pred.definitions); } in
  		  	 let ret_pred = detect_trivia_and_nonsense ret_pred in
  		  	 ret_pred))
		norm_rec_predicates;
	norm_rec_unfolded_predicates


let to_string { name; num_params; params; definitions; is_recursive; } =
	"pred " ^ name ^ " (" ^ (String.concat ", " params) ^ ")" ^
	(match definitions with
	| [] -> ""
	| head :: tail ->
	  List.fold_left
	    (fun acc def -> acc ^ ",\n\t" ^ (JSIL_Print.string_of_logic_assertion def false))
		  (" :\n\t" ^ (JSIL_Print.string_of_logic_assertion head false))
		  tail)
	 ^ ";\n"
