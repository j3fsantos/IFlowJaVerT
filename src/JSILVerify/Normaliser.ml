open DynArray
open Set
open Stack
open JSIL_Syntax
open Symbolic_State
open Symbolic_State_Utils
open JSIL_Logic_Utils

exception InvalidTypeOfLiteral

let new_abs_loc_name var = abs_loc_prefix ^ var

let new_lvar_name var = lvar_prefix ^ var


(*  ------------------------------------------------------------------
 *  Auto-Unfolding Non-recursive Predicates in Assertions
 * 	------------------------------------------------------------------
 *	------------------------------------------------------------------
**)

type unfolded_predicate = {
	name         : string;
	num_params   : int;
	params       : jsil_var list;
	definitions  : ((string option) * jsil_logic_assertion) list;
  is_recursive : bool;
  previously_normalised_u_pred : bool
}

(* Cross product of two lists, l1 and l2, combining its elements with function f *)
let cross_product
		(l1 : 'a list) (l2 : 'b list)
		(f : 'a -> 'b -> 'c) : 'c list =
	List.fold_left (fun result e1 -> result @ (List.map (f e1) l2)) [] l1


let rec auto_unfold
		(predicates : (string, unfolded_predicate) Hashtbl.t)
		(asrt       : jsil_logic_assertion) : jsil_logic_assertion list =
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
				(* If the predicate is recursive, return the assertion unchanged.           *)
				[asrt]
			else
				(* If it is not, replace the predicate assertion for the list of its definitions
				   substituting the formal parameters of the predicate with the corresponding
				   logical expressions in the argument list *)
				let subst = init_substitution2 pred.params args  in
				let new_asrts  = List.map (fun (_, a) -> (assertion_substitution a subst false)) pred.definitions in
				List.concat (List.map au new_asrts)
		 (* If the predicate is not found, raise an error *)
		with Not_found -> raise (Failure ("Error: Can't auto_unfold predicate " ^ name)))
	| LTrue | LFalse | LEq _ | LLess _ | LLessEq _ | LStrLess _ | LPointsTo _ | LEmp
	| LTypes _ | LEmptyFields _ | LSetMem (_, _) | LSetSub (_, _) | LForAll (_, _) -> [asrt]


(*  ------------------------------------------------------------------
 *  Auto-Unfolding Non-recursive Predicates in Pred definitions
 * 	------------------------------------------------------------------
 *	------------------------------------------------------------------
**)
let detect_trivia_and_nonsense (u_pred : unfolded_predicate) : unfolded_predicate =
	print_time_debug "detect_trivia_and_nonsense";
	let new_definitions = List.map
		(fun (oc, x) -> oc, (Simplifications.reduce_assertion_no_store_no_gamma_no_pfs x)) u_pred.definitions in
	let new_definitions = List.filter (fun (oc, x) -> not (x = LFalse)) new_definitions in
	{ u_pred with definitions = new_definitions }

(*
   JSIL Predicates can have non-pvar parameters - to say that a given parameter
   always has a certain value...
*)
let replace_non_pvar_params (pred : jsil_logic_predicate) : unfolded_predicate =
	let new_params, new_asrts =
		List.fold_right
			(fun cur_param (params, new_asrts) ->
				match cur_param with
				| LLit _ | LNone ->
					(* If the parameter is a JSIL literal or None...     *)
			  		(* Get a fresh program variable a add an additional
			  		   constraint to each definition *)
			  		let new_pvar = fresh_pvar () in
			  		(new_pvar :: params), (LEq (PVar new_pvar, cur_param) :: new_asrts)
			  	| PVar x         ->
			  		(* If the parameter is a program variable, add the
			  		   parameter as it is *)
			  		(x :: params), new_asrts
			  	| _              ->
			  		(* Otherwise, it's an error *)
					raise (Failure ("Error in predicate " ^ pred.name ^ ": Unexpected parameter.")))
			pred.params ([], []) in
	let new_definitions = List.map (fun (oid, a) -> (oid, star_asses (a :: new_asrts))) pred.definitions in
	{ name	       = pred.name;
	  num_params   = pred.num_params;
	  params       = new_params;
	  definitions  = new_definitions;
    is_recursive = false;
    previously_normalised_u_pred = pred.previously_normalised_pred }


(* ----------------------------------------------------------------
   Joining predicate definitions together
   ----------------------------------------------------------------
   Joins two unfolded_predicates defining different cases of the
   same predicate in a single unfolded_predicate
   ----------------------------------------------------------------
*)
let join_pred (pred1 : unfolded_predicate) (pred2 : unfolded_predicate) : unfolded_predicate =
	if pred1.name <> pred2.name || pred1.num_params <> pred2.num_params
		then (
	  		let msg = Printf.sprintf "Incompatible predicate definitions for: %s" pred1.name in
	  		raise (Failure msg)
	  ) else (
	  		let subst = init_substitution2 pred2.params (List.map (fun var -> PVar var) pred1.params) in
		  	let definitions = pred1.definitions @
		  		(List.map (fun (oid, a) -> oid, (assertion_substitution a subst true)) pred2.definitions) in
		  	{ pred1 with definitions = definitions; is_recursive = pred1.is_recursive || pred2.is_recursive; }
	  )


(* Given a Hashtbl of predicates, return a Hashtbl from predicate name
   to boolean meaning "recursive" or "not recursive"
*)
let find_recursive_preds (preds : (string, unfolded_predicate) Hashtbl.t) =
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
				List.concat (List.map (fun (_, asrt) -> (get_predicate_names asrt)) pred.definitions) in
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


let auto_unfold_pred_defs (preds : (string, jsil_logic_predicate) Hashtbl.t) =
	let u_predicates = Hashtbl.create 100 in
	Hashtbl.iter
		(fun name pred ->
			(* Substitute literals in the head for logical variables *)
			let (u_pred : unfolded_predicate) = replace_non_pvar_params pred in
			try
				(* Join the new predicate definition with all previous for the same predicate (if any) *)
				let current_pred = Hashtbl.find u_predicates name in
				Hashtbl.replace u_predicates name (join_pred current_pred u_pred);
			with
			| Not_found -> Hashtbl.add u_predicates name u_pred
			| Failure reason -> raise (Failure ("Error in predicate " ^ name ^ ": " ^ reason)))
		preds;
	(* Detect recursive predicates *)
  	let rec_table = find_recursive_preds u_predicates in

	(* Flag those that are recursive *)
	let u_rec_predicates = Hashtbl.create (Hashtbl.length u_predicates) in
	Hashtbl.iter
	  (fun name pred ->
			Hashtbl.add u_rec_predicates pred.name
			  { pred with is_recursive =
					(try Hashtbl.find rec_table name with
					| Not_found -> raise (Failure ("Undefined predicate " ^ name))); })
		u_predicates;

	(* Auto-unfold the predicates in the definitions of other predicates *)
	let u_rec_predicates' = Hashtbl.create (Hashtbl.length u_rec_predicates) in
	Hashtbl.iter
	  (fun name pred ->
	  		let definitions' = List.flatten (List.map
	  			(fun (os, a) ->
	  				let as' = auto_unfold u_rec_predicates a in
	  				let as' = List.map (fun a -> (os, a)) as' in
	  				as') pred.definitions) in
			Hashtbl.add u_rec_predicates' pred.name
			(let ret_pred = { pred with definitions = definitions'; } in
  		  	 let ret_pred = detect_trivia_and_nonsense ret_pred in
  		  	 ret_pred))
		u_rec_predicates;
	u_rec_predicates'




(*  ------------------------------------------------------------------
 *  List Preprocessing
 * 	------------------------------------------------------------------
 *	Preprocess list logical expressions for which we know
 *	the length statically. If a |- l-len(le) = i, where i is
 *	a concrete number, we add the assertion le = {{ #x1, ..., #xi }}
 *	to a and replace all the occurrences of l-nth(le, j) for #xj in a
 *	------------------------------------------------------------------
**)
let pre_process_list_exprs (a : jsil_logic_assertion) =

	(* 1 - Find the lists for which we know the length *)
	let find_list_exprs_to_concretize (a : jsil_logic_assertion) : (jsil_logic_expr, (jsil_logic_expr list)) Hashtbl.t =
		let f_ac_1 a _ _ ac =
			(match a with
			| LEq (LEList _, LEList _) -> (List.concat ac)
			| LEq (le, LEList les)
			| LEq (LEList les, le) -> (le, les) :: (List.concat ac)
			| _ -> (List.concat ac)) in
		let lists1 = assertion_fold None f_ac_1 None None a in

		let f_ac_2 a _ _ ac =
			(match a with
			| LEq (LUnOp (LstLen, le), LLit (Num i)) ->
				let vars_le = Array.to_list (Array.init (int_of_float i) (fun j -> LVar (fresh_lvar ()))) in
				(le, vars_le) :: (List.concat ac)
			| _ -> (List.concat ac)) in
		let lists2 = assertion_fold None f_ac_2 None None a in

		let lst_exprs = lists2 @ lists1 in
		let lists_tbl = Hashtbl.create (List.length lst_exprs) in
		List.iter (fun (le, les) ->
			if (Hashtbl.mem lists_tbl le) then () else (
				Hashtbl.replace lists_tbl le les
		)) lst_exprs;
		lists_tbl in


	(* 2 - Replace expressions of the form l-nth(le, i) where le denotes a list for which
	       we know the length and i a concrete number with the newly created logical variable.
	       E.g. if we associated in 2) le with a the list of logical variables
	            {{ V1, ..., Vi, ..., Vn}}, l-nth(le, i) is replaced with Vi  *)
	let concretize_list_accesses
		(a : jsil_logic_assertion)
		(new_lists : (jsil_logic_expr, (jsil_logic_expr list)) Hashtbl.t) : jsil_logic_assertion =
		let f_e le =
			match le with
			| LLstNth (le', LLit (Num i)) ->
				(try
					let vs = Hashtbl.find new_lists le' in
					let le'' = List.nth vs (int_of_float i) in
					le'', false
				with _ -> le, false)
			| _ -> le, true  in
		assertion_map None f_e a in


	(* 3 - Generate the equalities relating the expressions that denote lists whose
	       length is statically known with the lists of the newly created logical variables *)
	let make_new_list_as
		(a : jsil_logic_assertion)
		(new_lists : (jsil_logic_expr, (jsil_logic_expr list)) Hashtbl.t) : jsil_logic_assertion  =
		let new_list_as =
			Hashtbl.fold
				(fun le les ac -> (LEq (le, LEList les)) :: ac)
				new_lists [ a ] in
		JSIL_Logic_Utils.star_asses new_list_as in

	(* Doing IT *)
	let new_lists = find_list_exprs_to_concretize a in
	let a'        = concretize_list_accesses a new_lists in
	make_new_list_as a' new_lists


(*  -----------------------------------------------------
	Normalise Pure Assertion (only one!)
	-----------------------------------------------------
	Invoke normalise_logic_expression on all the logic
	expressions of a
	_____________________________________________________
*)
let rec normalise_pure_assertion
		(store : symbolic_store)
		(gamma : typing_environment)
		(subst : substitution)
		(assertion : jsil_logic_assertion) : jsil_logic_assertion =
	let fa = normalise_pure_assertion store gamma subst in
	let fe = normalise_lexpr ~store:store ~subst:subst gamma in
	let start_time = Sys.time() in
	try (let result = (match assertion with
	| LEq (le1, le2) -> LEq((fe le1), (fe le2))
	| LLess (le1, le2) -> LLess((fe le1), (fe le2))
	| LLessEq (le1, le2) -> LLessEq ((fe le1), (fe le2))
	| LNot (LEq (le1, le2)) -> LNot (LEq((fe le1), (fe le2)))
	| LNot (LLessEq (le1, le2)) -> LNot (LLessEq((fe le1), (fe le2)))
	| LNot (LLess (le1, le2)) -> LNot (LLess((fe le1), (fe le2)))
	| LNot (LSetSub (le1, le2)) -> LNot (LSetSub ((fe le1), (fe le2)))
	| LNot (LSetMem (le1, le2)) -> LNot (LSetMem ((fe le1), (fe le2)))
	| LAnd (a1, a2) -> LAnd ((fa a1), (fa a2))
	| LOr (a1, a2) -> LOr ((fa a1), (fa a2))
	| LFalse -> LFalse
	| LTrue -> LTrue
	| LSetSub (le1, le2) -> LSetSub ((fe le1), (fe le2))
	| LSetMem (le1, le2) -> LSetMem ((fe le1), (fe le2))
	| LForAll (bt, a) -> LForAll (bt, fa a)

	| _ ->
			let msg = Printf.sprintf "normalise_pure_assertion can only process pure assertions: %s" (JSIL_Print.string_of_logic_assertion assertion false) in
			raise (Failure msg)) in
	let end_time = Sys.time () in
	JSIL_Syntax.update_statistics "normalise_pure_assertion" (end_time -. start_time);
	(* print_debug (Printf.sprintf "normalise_pure_assertion: %f : %s -> %s"
			(end_time -. start_time) (JSIL_Print.string_of_logic_assertion assertion false)
			(JSIL_Print.string_of_logic_assertion result false)); *)
		result)
	with
	| Failure msg -> let end_time = Sys.time () in
		JSIL_Syntax.update_statistics "normalise_pure_assertion" (end_time -. start_time);
		print_debug_petar (Printf.sprintf "normalise_pure_assertion: %f : %s -> Failure"
			(end_time -. start_time) (JSIL_Print.string_of_logic_assertion assertion false));
		raise (Failure msg)

(** -------------------------------------------------------------------
  * init_alocs: Generate the abstract locations for the normalised spec
  * -------------------------------------------------------------------
  * This function creates an abstract location for every program variable used in
  * a cell assertion or empty fields assertion.
  * Example: (x, "foo") -> _ => store(x)= $l_x, where $l_x is fresh
**)
let rec initialise_alocs
	(store : symbolic_store) (gamma : typing_environment)
	(subst : substitution) (ass : jsil_logic_assertion) : unit =
	let f = initialise_alocs store gamma subst in
	match ass with
	| LStar (a_left, a_right) ->
			f a_left; f a_right

	| LPointsTo (PVar var, _, _)
	| LEmptyFields (PVar var, _) ->
			if (not (Hashtbl.mem store var))
			then
				(let aloc = new_abs_loc_name var in
					Hashtbl.add store var (ALoc aloc);
					Hashtbl.add subst var (ALoc aloc);
					Hashtbl.replace gamma var ObjectType)

	| LPointsTo (LVar var, _, _)
	| LEmptyFields (LVar var, _) ->
			if (not (Hashtbl.mem subst var))
			then
				(let aloc = new_abs_loc_name var in
					Hashtbl.add subst var (ALoc aloc))
					(* Hashtbl.remove gamma var) *)

	| LPointsTo (ALoc _, _, _) -> ()
			(* raise (Failure "Unsupported assertion during normalization") *)

	| _ -> ()


(** -----------------------------------------------------
  * Normalise Pure Assertions
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_pure_assertions
		(store : symbolic_store)
		(gamma : typing_environment)
		(subst : substitution)
		(a     : jsil_logic_assertion) : pure_formulae =

	let pvar_equalities           = Hashtbl.create 31 in
	let non_store_pure_assertions = Stack.create () in

	(**
	 * Step 1 - Get equalities involving program variables
	 * -----------------------------------------------------------------------------------
	 * Returns the list of equalities in a involving program variables of the form x = E
	 * or E = x, for a logical expression E and a variable x
	 * -----------------------------------------------------------------------------------
	 *)
	let rec init_pvar_equalities a =
		(match a with
			| LStar (a_l, a_r) -> init_pvar_equalities a_l; init_pvar_equalities a_r

			| LEq (PVar x, le)
			| LEq (le, PVar x) ->
					if ((not (Hashtbl.mem pvar_equalities x)) && (not (Hashtbl.mem store x)))
					then Hashtbl.add pvar_equalities x le
					else Stack.push (LEq (PVar x, le)) non_store_pure_assertions

			| LEq (_, _) | LNot _ | LLessEq (_, _) | LLess (_, _) | LOr (_, _)
			| LAnd (_, _) | LSetSub (_, _) | LSetMem (_, _) | LForAll (_, _) -> Stack.push a non_store_pure_assertions

			| _ -> ()) in


	(**
	 * Step 2 - Build a table mapping pvars to integers
	 * ------------------------------------------------
	 *)
	let get_vars_tbl (vars : SS.t) : (string, int) Hashtbl.t =
  		let len = SS.cardinal vars in
  		let vars_tbl = Hashtbl.create len in
 		List.iteri (fun i var -> Hashtbl.add vars_tbl var i) (SS.elements vars);
  		vars_tbl in


	(**
	 * Step 3 - PVars Dependency Graph
	 * ------------------------------------------------------------------------
	 * Compute a dependency graph between PVar equalities (which are treated as
	 * definitions)
	 * ------------------------------------------------------------------------
	 *)
	let pvars_graph
			(p_vars : SS.t)
			(p_vars_tbl : (string, int) Hashtbl.t) : (int list) array =
		let len = SS.cardinal p_vars in
		let graph = Array.make len [] in

		List.iteri (fun u cur_var ->
			let cur_le = Hashtbl.find pvar_equalities cur_var in
			let cur_var_deps = get_expr_vars true cur_le in
			SS.iter (fun v ->
				(try
					let v_num = Hashtbl.find p_vars_tbl v in
					graph.(u) <- v_num :: graph.(u)
					with _ -> ())) cur_var_deps) (SS.elements p_vars);

		graph in


	(**
	 * Step 4 - Normalise PVar equalities
	 * ------------------------------------------------------------------------
	 * Normalise equalities involving pvars
	 * Detect cyclic dependencies between pvar definitions
	 * Break dependencies by introducing new logical variables
	 * E.g.
	 *      (x = y + 1) * (y = #z) ==> (x = #z + 1) * (y = #z)
	 *      (x = y + 1) * (y = (3 * x) - 2) ==>
	 				(x = #w + 1) * (y = #y) * (#y = (3 * (#y + 1)) - 2)
	 				where #y = new_lvar_name (y)
	 * ------------------------------------------------------------------------
	 *)
	let normalise_pvar_equalities
			(graph : int list array)
			(p_vars : SS.t)
			(p_vars_tbl : (string, int) Hashtbl.t) =

		let p_vars      = Array.of_list (SS.elements p_vars) in
		let len         = Array.length p_vars in
		let visited_tbl = Array.make len false in

		let is_searchable u =
			List.fold_left
				(fun ac v -> ac && (not visited_tbl.(v)))
				true
				graph.(u) in

		(** a pvar-equality that cannot be lifted to the abstract store
		    has to remain in the pure formulae *)
		let remove_assignment var =
			(try
				let le = Hashtbl.find pvar_equalities var in
				Stack.push (LEq (LVar (new_lvar_name var), le)) non_store_pure_assertions;
				Hashtbl.remove pvar_equalities var
			with _ ->
				let msg = Printf.sprintf "DEATH. normalise_pure_assertions -> normalise_pvar_equalities -> remove_assignment. Var: %s." var in
				raise (Failure msg)) in


		(** lifting an assignment to the abstract store *)
		let rewrite_assignment var =
			(try
				let le  = Hashtbl.find pvar_equalities var in
				let le' = normalise_lexpr ~store:store ~subst:subst gamma le in
				Hashtbl.replace store var le';
				Hashtbl.replace subst var le'
			with _ ->
				let msg = Printf.sprintf "DEATH. normalise_pure_assertions ->  normalise_pvar_equalities -> rewrite_assignment. Var: %s\n" var in
				raise (Failure msg)) in


		(** DFS on pvar dependency graph *)
		let rec search (u : int) =
			let u_var = p_vars.(u) in
			visited_tbl.(u) <- true;
			match (is_searchable u) with
			| false -> remove_assignment u_var
			| true ->
					List.iter
						(fun v ->
							(* Given that u is searchable this if is very strange *)
							if (visited_tbl.(v))
								then ()
								else search v)
						graph.(u);
					rewrite_assignment u_var in
		for i = 0 to (len - 1) do
			if (not (visited_tbl.(i)))
			then search i
			else ()
		done in

	(**
	 * Step 5 - The store is always full
	 * ------------------------------------------------------------------------
	 * PVars that were not associated with a logical expression in the store
	 * are mapped to a newly created logical variable
	 * ------------------------------------------------------------------------
	 *)
	let fill_store p_vars =
		SS.iter
			(fun var ->
				if (not (Hashtbl.mem store var))
					then (
						let new_l_var = new_lvar_name var in
						Hashtbl.add store var (LVar new_l_var);
						Hashtbl.add subst var (LVar new_l_var);
						try
							let var_type = Hashtbl.find gamma var in
							Hashtbl.add gamma new_l_var var_type
						with _ -> ()))
			p_vars	in


	(**
	 * Step 6 - Normalise Pure Assertions
	 * ------------------------------------------------------------------------
	 * The pure assertions that were not lifted to the store need to be
	 * normalised
	 * ------------------------------------------------------------------------
	 *)
	let normalise_pure_assertions () =
		let stack_size = Stack.length non_store_pure_assertions in
		let pi         = DynArray.make (stack_size * 2) in
		let cur_index  = ref 0 in

		while (not (Stack.is_empty non_store_pure_assertions)) do
			let p_assertion  = Stack.pop non_store_pure_assertions in
			let p_assertion' = normalise_pure_assertion store gamma subst p_assertion in
			DynArray.add pi p_assertion';
			cur_index := (!cur_index) + 1
		done;

		(* Prints *)
	 	(* print_debug_petar (Printf.sprintf "NPA: Pure formulae: %s" (Symbolic_State_Print.string_of_shallow_p_formulae non_store_pure_assertions_array false));
		print_debug_petar (Symbolic_State_Print.string_of_substitution subst); *)
		let pi, _ = Simplifications.simplify_pfs pi gamma (Some None) in
		pi in


	(* Doing IT *)
	(* 1 *) init_pvar_equalities a;
	let p_vars = Hashtbl.fold (fun var le ac -> SS.add var ac) pvar_equalities SS.empty in
	(* 2 *) let p_vars_tbl = get_vars_tbl p_vars in
	(* 3 *) let pvars_graph = pvars_graph p_vars p_vars_tbl in
	(* 4 *) normalise_pvar_equalities pvars_graph p_vars p_vars_tbl;
	(* 5 *) fill_store (get_assertion_vars true a);
	(* 6 *) normalise_pure_assertions ()


(** -----------------------------------------------------
  * Normalise Cell Assertions
  * (Initialise Symbolic Heap)
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let rec normalise_cell_assertions
		(heap : symbolic_heap) (store : symbolic_store)
		(p_formulae : pure_formulae) (gamma : typing_environment)
		(subst : substitution) (a : jsil_logic_assertion) : unit =
	let f = normalise_cell_assertions heap store p_formulae gamma subst in
	let fe = normalise_lexpr ~store:store ~subst:subst gamma in

	(* This needs to go. but I have to generate discharges in the heap
	   and predicate set unification *)
	let simplify_element_of_cell_assertion ele =
		(match ele with
			| LLit _
			| LVar _
			| ALoc _
			| LNone -> ele
			| _ ->
					let lvar = fresh_lvar () in
					(* I need to add the type of the new logical variable to the gamma *)
					DynArray.add p_formulae (LEq ((LVar lvar), ele));
					let te, _, _ = JSIL_Logic_Utils.type_lexpr gamma ele in
					update_gamma gamma lvar te;
					LVar lvar) in

	match a with
	| LStar (a1, a2) -> f a1; f a2

	| LPointsTo (LVar var, le2, le3)
	| LPointsTo (PVar var, le2, le3) ->
		let aloc = (try
			(match Hashtbl.find subst var with
			| ALoc aloc -> aloc
			| _ -> raise (Failure (Printf.sprintf "Not an ALoc in subst: %s" (JSIL_Print.string_of_logic_expression (Hashtbl.find subst var) false))))
			with _ -> raise (Failure (Printf.sprintf "Variable %s not found in subst table!" var))) in
		let nle2 = simplify_element_of_cell_assertion (fe le2) in
		let nle3 = simplify_element_of_cell_assertion (fe le3) in
		let field_val_pairs, default_val = (try LHeap.find heap aloc with _ -> ([], None)) in
		LHeap.replace heap aloc (((nle2, nle3) :: field_val_pairs), default_val)

	| LPointsTo (LLit (Loc loc), le2, le3) ->
		let nle2 = simplify_element_of_cell_assertion (fe le2) in
		let nle3 = simplify_element_of_cell_assertion (fe le3) in
		let field_val_pairs, default_val = (try LHeap.find heap loc with _ -> ([], None)) in
		LHeap.replace heap loc (((nle2, nle3) :: field_val_pairs), default_val)

	| LPointsTo (ALoc loc, le2, le3) ->
		let nle2 = simplify_element_of_cell_assertion (fe le2) in
		let nle3 = simplify_element_of_cell_assertion (fe le3) in
		let field_val_pairs, default_val = (try LHeap.find heap loc with _ -> ([], None)) in
		LHeap.replace heap loc (((nle2, nle3) :: field_val_pairs), default_val)

	| LPointsTo (_, _, _) ->
		let msg = Printf.sprintf "" in
		raise (Failure "Illegal PointsTo Assertion")

	| _ -> ()


(** -----------------------------------------------------
  * Normalise Type Assertions
  * (Initialise Typing Environment)
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let rec normalise_type_assertions
		(gamma : typing_environment)
		(a : jsil_logic_assertion) : unit =
	let f = normalise_type_assertions gamma in
	match a with
	| LTypes type_list ->
		List.iter
			(fun (v, t) ->
			match v with
				| LLit lit ->
					if (evaluate_type_of lit <> t) then raise InvalidTypeOfLiteral

				| LVar v -> Hashtbl.replace gamma v t
				| PVar v -> Hashtbl.replace gamma v t

				| LNone -> ()
				| _ ->
					let v_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma v in
					(match v_type with
					| Some v_type ->
						(if (v_type = t) then () else (
							let msg = Printf.sprintf "Only vars or lvars in the typing environment. PUTTING: %s with type %s when its type is %s"
										(JSIL_Print.string_of_logic_expression v false)
										(JSIL_Print.string_of_type t)
										(JSIL_Print.string_of_type v_type) in
							raise (Failure msg)))
					| None ->
						let new_gamma = JSIL_Logic_Utils.reverse_type_lexpr gamma v t in
						(match new_gamma with
						| None ->
							let msg = Printf.sprintf "Only vars or lvars in the typing environment. PUTTING: %s with type %s when it CANNOT be typed or reverse-typed"
											(JSIL_Print.string_of_logic_expression v false)
											(JSIL_Print.string_of_type t) in
							raise (Failure msg)
						| Some new_gamma ->	extend_gamma gamma new_gamma)))
				type_list
	| LStar	(al, ar) -> f al; f ar
	| _ -> ()


(** -----------------------------------------------------
  * Normalise Predicate Assertions
  * (Initialise Predicate Set)
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_pred_assertions
	(store : symbolic_store) (gamma : typing_environment)
	(subst : substitution) (a : jsil_logic_assertion) : predicate_set * (jsil_logic_assertion list) =
	let preds = pred_set_init () in

	(* TODO: REWRITE                               *)
	(* There are more elegant ways of writing this *)
	let make_normalised_pred_assertion name les =
		let new_les, new_assertions =
			List.fold_left
				(fun (new_les, new_equalities) le ->
					match le with
					| LNone	| LVar _ | LLit _ | ALoc _ -> ((le :: new_les), new_equalities)
					| PVar x ->
						let msg = Printf.sprintf "Program Variable %s in logical expression that was supposed to be normalised!!!\n" x in
						raise (Failure msg)
					| _ ->
						let x = fresh_lvar () in
						((LVar x) :: new_les), ((LEq ((LVar x), le)) :: new_equalities))
				([], [])
				les in
		let new_les = List.rev new_les in
		(name, new_les), new_assertions in

	let rec init_preds_aux preds a =
		let f = init_preds_aux preds in
		let fe = normalise_lexpr ~store:store ~subst:subst gamma in
		(match a with
			| LStar (a1, a2) ->
				let new_assertions1 = f a1 in
				let new_assertions2 = f a2 in
				new_assertions1 @ new_assertions2
			| LPred (name, les) ->
					let n_les =	List.map fe les in
					let normalised_pred_assertion, new_assertions = make_normalised_pred_assertion name n_les in
					DynArray.add preds normalised_pred_assertion;
					new_assertions
			| _ -> []) in
	let new_assertions = init_preds_aux preds a in
	let pfs = pfs_of_list new_assertions in
	Simplifications.sanitise_pfs store gamma pfs;
	preds, (pfs_to_list pfs)


(** -----------------------------------------------------
  * Normalise EmptyFields Assertions
  * (Initialise Symbolic Heap Domains)
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_ef_assertions
	(heap : symbolic_heap) (store : symbolic_store)
	(p_formulae : pure_formulae) (gamma : typing_environment)
	(subst : substitution) (a : jsil_logic_assertion) : unit =

	let rec get_all_empty_fields a =
		let f_ac a _ _ ac =
			match a with
			| LEmptyFields (le, domain) ->
				let le' = normalise_lexpr ~store:store ~subst:subst gamma le in
				let domain' = normalise_lexpr ~store:store ~subst:subst gamma domain in
				 (le', domain') :: (List.concat ac)
			| _ -> List.concat ac in
		assertion_fold None f_ac None None a in

	let add_domain (le_loc, domain)  =
		print_debug_petar (Printf.sprintf "Location: %s" (JSIL_Print.string_of_logic_expression le_loc false));
		let le_loc_name =
			match le_loc with
			| LLit (Loc loc_name)
			| ALoc loc_name -> loc_name
			| PVar x
			| LVar x ->
				let x_loc = try Hashtbl.find subst x with _ ->
					print_debug_petar "Variable not in subst."; raise (Failure "Illegal Emptyfields!!!") in
				(match x_loc with
				| ALoc loc
				| LLit (Loc loc) -> loc
				| _ -> print_debug_petar "Variable strange after subst."; raise (Failure "Illegal Emptyfields!!!"))
			| _ -> raise (Failure "Illegal Emptyfields!!!") in

		let fv_list, _ = try LHeap.find heap le_loc_name with Not_found -> [], None in
		LHeap.replace heap le_loc_name (fv_list, Some domain) in

	List.iter add_domain (get_all_empty_fields a)


let fill_store_with_gamma
	(store : symbolic_store) (gamma : typing_environment) (subst : substitution) : unit =
	Hashtbl.iter
		(fun var t ->
			if ((is_pvar_name var) && (not (Hashtbl.mem store var)))
				then (
					let new_l_var = new_lvar_name var in
					Hashtbl.add gamma new_l_var t;
					Hashtbl.add store var (LVar new_l_var);
					Hashtbl.add subst var (LVar new_l_var)))
		gamma


let extend_typing_env_using_assertion_info
	(gamma : typing_environment) (a_list : jsil_logic_assertion list) : unit =
	List.iter (fun a ->
		match a with
		| LEq (LVar x, le) | LEq (le, LVar x)
		| LEq (PVar x, le) | LEq (le, PVar x) ->
			let x_type = gamma_get_type gamma x in
			(match x_type with
			| None ->
				let le_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
				weak_update_gamma gamma x le_type
			| Some _ -> ())
		| _ -> ()
	) a_list


(**
  * ---------------------------------------------------------------------------
  * Symbolic state well-formedness checks
  * ---------------------------------------------------------------------------
  * 1. the type of each pvar is consistent with the type of the logical
  *    expression to which it is mapped by the store
  * 2. the underlying asusmption that all the fields of a give an object are
  *    different from each other does not create a contradiction
  * ---------------------------------------------------------------------------
 *)


let check_pvar_types (store : symbolic_store) (gamma : typing_environment) : bool =
	let placeholder pvar le target_type =
		if (Hashtbl.mem gamma pvar) then
		begin
		  let _type = Hashtbl.find gamma pvar in
		  	(target_type = _type)
		end
		else
		begin
		   Hashtbl.add gamma pvar target_type;
		   true
		end in

	Hashtbl.fold
		(fun pvar le ac -> ac &&
			(match le with
			 | LNone -> placeholder pvar le NoneType
			 | ALoc _ -> placeholder pvar le ObjectType
			 | LLit lit -> placeholder pvar le (evaluate_type_of lit)
			 | _ -> true
			)
		) store true


let make_all_different_assertion_from_fvlist (f_list : jsil_logic_expr list) : jsil_logic_assertion list =

	let rec make_all_different_assertion_from_field_and_flist field flist =
		let rec loop flist constraints =
			match flist with
			| [] -> constraints
			| f_name :: rest ->
				(match List.mem f_name rest with
				| true ->
					print_debug_petar (Printf.sprintf "Horror: Overlapping resources in %s"
						(String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le false) flist)));
					[ LFalse ]
				| false -> loop rest ((LNot (LEq (field, f_name))) :: constraints)) in
		loop flist [] in

	let rec loop fields_to_cover fields_covered constraints =
		match fields_to_cover with
		| [] -> constraints
		| f_name :: rest ->
			let new_constraints = make_all_different_assertion_from_field_and_flist f_name rest in
			(match new_constraints with
			| [ LFalse ] -> [ LFalse ]
			| _ -> loop rest (f_name :: fields_covered) (new_constraints @ constraints)) in

	let result = loop f_list [] [] in

	print_debug_petar
		(Printf.sprintf "Make all different: %s\n"
			(String.concat " " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) f_list)));

	result

let get_heap_well_formedness_constraints heap =
	print_debug (Printf.sprintf "get_heap_well_formedness_constraints of heap:\n%s\n"
		(Symbolic_State_Print.string_of_shallow_symb_heap heap false));

	LHeap.fold
		(fun field (fv_list, _) constraints ->
			(match constraints with
			| [ LFalse ] -> [ LFalse ]
			| _ ->
  				let f_list, _ = List.split fv_list in
  				let new_constraints = make_all_different_assertion_from_fvlist f_list in
  				new_constraints @ constraints)) heap []




(** -----------------------------------------------------
  * Normalise Assertion
  * Given an assertion creates a symbolic state and a
  * substitution
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_assertion
		(gamma : typing_environment option)
		(subst : substitution option)
		(a     : jsil_logic_assertion) : (symbolic_state * substitution) option =

	print_debug_petar (Printf.sprintf "Normalising assertion:\n\t%s" (JSIL_Print.string_of_logic_assertion a false));

	let falsePFs pfs =
		match pfs_to_list pfs with
		| [ LFalse ] -> true
		| _          -> false in

	(** Step 1 -- Preprocess list expressions - resolve l-nth(E, i) when possible  *)
	let a = pre_process_list_exprs a in

	(** Step 2 -- Create empty symbolic heap, symbolic store, typing environment, and substitution *)
	let heap  = heap_init () in
	let store = store_init [] [] in
	let gamma = Option.map_default copy_gamma (gamma_init ()) gamma in
	let subst = Option.map_default copy_substitution (init_substitution []) subst in

	(** Step 3 -- Normalise type assertions and pure assertions
	  * 3.1 - type assertions -> initialises gamma
	  * 3.2 - pure assertions -> initialises store and pfs
	  *)
	normalise_type_assertions gamma a;
	initialise_alocs store gamma subst a;
	let p_formulae = normalise_pure_assertions store gamma subst a in
	if (falsePFs p_formulae) then None else (
		(** The pure formulae are not completely bananas  *)

		(** Step 4 -- Add to the store the program variables that are not there yet, BUT
			for which we know the types *)
		fill_store_with_gamma store gamma subst;
		extend_typing_env_using_assertion_info gamma ((pfs_to_list p_formulae) @ (pf_of_store2 store));

		(** Step 5 -- Normalise cell assertions, pred assertions, and ef assertions
		  * 5.1 - cell assertions -> initialises heap
	      * 5.2 - pred assertions -> initialises pred set
	      * 5.3 - ef assertions   -> fills in the domain for the objects in the heap
		  *)
		normalise_cell_assertions heap store p_formulae gamma subst a;
		let preds, new_assertions = normalise_pred_assertions store gamma subst a in
		extend_typing_env_using_assertion_info gamma new_assertions;
		merge_pfs p_formulae (pfs_of_list new_assertions);
		normalise_ef_assertions heap store p_formulae gamma subst a;

		(** Step 6 -- Check if the symbolic state makes sense *)
		let heap_constraints = get_heap_well_formedness_constraints heap in
		if ((Pure_Entailment.check_satisfiability (heap_constraints @ (pfs_to_list p_formulae)) gamma) &&
				(check_pvar_types store gamma))
			then Some ((heap, store, p_formulae, gamma, preds), subst)
			else None)

(** -----------------------------------------------------
  * Normalise a Pre-Normalised Assertion
  * Given an assertion creates a symbolic state and a
  * substitution. However this won't actually do anything
  * as the work has already been done.
  * -----------------------------------------------------
  * -----------------------------------------------------
 **)
let normalise_normalised_assertion
    (a : jsil_logic_assertion) : symbolic_state =

  print_debug (Printf.sprintf "Normalising pre-normalised assertion:\n\t%s" (JSIL_Print.string_of_logic_assertion a false));

  (** Step 1 -- Create empty symbolic heap, symbolic store, typing environment, pred set and pfs *)
  let heap  : symbolic_heap      = heap_init () in
  let store : symbolic_store     = store_init [] [] in
  let gamma : typing_environment = gamma_init () in
  let pfs   : pure_formulae      = DynArray.make 0 in
  let preds : predicate_set      = DynArray.make 0 in

  print_debug (Printf.sprintf "PARSING NORMALISED ASSERTION");
     print_debug (JSIL_Print.string_of_logic_assertion a true);

  (* Step 2 - Map over assertion, populate gamma, store and heap *)
  let populate_state_from_assertion a =
    match a with
    | LTypes type_assertions ->
      List.map (fun (e, t) -> Hashtbl.replace gamma (JSIL_Print.string_of_logic_expression e false) t) type_assertions;
      (a, false)
    | LPointsTo ((PVar loc), le2, le3)
    | LPointsTo ((LLit (Loc loc)), le2, le3)
    | LPointsTo ((ALoc loc), le2, le3) ->
      let field_val_pairs, default_empty_fields = (try LHeap.find heap loc with _ -> ([], None)) in
      LHeap.replace heap loc (((le2, le3) :: field_val_pairs), default_empty_fields);
      (a, false)
    | LEmptyFields (obj, domain) ->
      let loc = JSIL_Print.string_of_logic_expression obj false in
      let field_val_pairs, _ = (try LHeap.find heap loc with _ -> ([], None)) in
      LHeap.replace heap loc ((field_val_pairs), (Some domain));
      (a, false)
    | LEq ((PVar v), le)
    | LEq (le, (PVar v)) ->
      Hashtbl.add store v le;
      (a, false)
    | LEq ((LVar _), _)
    | LEq (_, (LVar _)) ->
      DynArray.add pfs a;
      (a, false)
    | LNot _
    | LAnd _ (* TODO: correct? *)
    | LOr _ (* TODO: correct? *)
    | LLess _
    | LLessEq _
    | LStrLess _
    | LForAll _
    | LSetMem _
    | LSetSub _ ->
      DynArray.add pfs a;
      (a, false)
    | LPred (s, les) ->
      DynArray.add preds (s, les);
      (a, false)
    | _ ->
      (a, true)
  in
  assertion_map (Some populate_state_from_assertion) (fun e -> (e, false)) a;

  print_debug (Printf.sprintf "\n----- AFTER \"NORMALISATION\": -----\n");
  print_debug (Symbolic_State_Print.string_of_lexpr_store store);
  print_debug (Printf.sprintf "Gamma: %s" (Symbolic_State_Print.string_of_gamma gamma));
  print_debug (Printf.sprintf "Heap: %s" (Symbolic_State_Print.string_of_shallow_symb_heap heap false));
  print_debug (Printf.sprintf "Pure Formulae: %s" (Symbolic_State_Print.string_of_shallow_p_formulae pfs false));
  print_debug (Printf.sprintf "Preds: %s" (Symbolic_State_Print.string_of_preds preds false));
  (heap, store, pfs, gamma, preds)


(** Normalise Postcondition
	-----------------------
	Each normlised postcondition postcondition may map additional spec vars
	to alocs. In order not to lose the link between the newly generated alocs
	and the precondition spec vars, we need to introduce extra equalities    *)
let normalise_post
		(post_gamma_0  : typing_environment)
		(subst         : substitution)
		(spec_vars     : SS.t)
		(post          : jsil_logic_assertion) : symbolic_state option =
	(match (normalise_assertion (Some post_gamma_0) (Some subst) post) with
	| None -> None
	| Some (ss_post, post_subst) ->
		let post_new_spec_var_alocs =
			SS.elements (SS.filter (fun x -> (not (Hashtbl.mem subst x)) && (Hashtbl.mem post_subst x)) spec_vars) in
		print_debug (Printf.sprintf "post substitution:\n%s\npost_new_spec_var_alocs: %s\n"
			(Symbolic_State_Print.string_of_substitution post_subst)
			(String.concat ", " post_new_spec_var_alocs));
		let extra_post_pfs = List.map (fun x -> LEq (LVar x, Hashtbl.find post_subst x)) post_new_spec_var_alocs in
		extend_symb_state_with_pfs ss_post (pfs_of_list extra_post_pfs);
		Some (Simplifications.simplify_ss ss_post (Some (Some spec_vars))))

(** -----------------------------------------------------
  * Normalise Pre-Normalised Single Spec
  * -----------------------------------------------------
  * -----------------------------------------------------
 **)
let normalise_single_normalised_spec
    (spec_name  : string)
    (spec       : jsil_single_spec) : jsil_n_single_spec list =

  print_debug (Printf.sprintf "BANANAS. SPEC %S ALREADY NORMALISED: %s" spec_name
                 (JSIL_Print.string_of_single_spec "" spec));

  (** Step 1 - "Normalise" precondition                                     *)
  (* TODO: check: we always only have 1 pre as the specs are already unfolded? *)
  let pre : symbolic_state = normalise_normalised_assertion spec.pre in

  (** Step 2 - "Normalise" the posts *)
  let spec_vars = get_assertion_lvars spec.pre in
  let posts : symbolic_state list = List.map normalise_normalised_assertion spec.post in

  print_debug
    (Printf.sprintf "SAMOSAS. Normalised Pre: %s. Normalised Posts: %s\n"
      (Symbolic_State_Print.string_of_shallow_symb_state pre)
      (String.concat "; " (List.map Symbolic_State_Print.string_of_shallow_symb_state posts)));

  [{
      n_pre      = pre;
    	n_post     = posts;
    	n_ret_flag = spec.ret_flag;
    	n_lvars    = spec_vars;
      n_subst    = init_substitution [] (* TODO: is this correct? *)
    }]

(** -----------------------------------------------------
  * Normalise Single Spec
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_single_spec
	(predicates : (string, unfolded_predicate) Hashtbl.t)
	(spec_name  : string)
	(spec       : jsil_single_spec) : jsil_n_single_spec list =

	let oget_list lst = List.map Option.get (List.filter (fun x -> not (x = None)) lst) in

	let pre_normalise (a : jsil_logic_assertion) : jsil_logic_assertion list =
		List.map JSIL_Logic_Utils.push_in_negations (auto_unfold predicates a) in

	print_debug (Printf.sprintf "Normalising the following spec of %s:\n%s\n" spec_name
			(JSIL_Print.string_of_single_spec "" spec));

	(** Step 1 - Unfold non-recursive predicates + push-in negations *)
	let spec_vars = get_assertion_lvars spec.pre in
	let pres      = pre_normalise spec.pre in
	let posts     = List.concat (List.map pre_normalise spec.post) in

	(** Step 2 - Normalise preconditions                                     *)
	(** Spec vars mapped to alocs in the precondition MUST also be
	    substituted in the postcondition - so they cease to be spec vars     *)
	let ss_pres   = oget_list (List.map (normalise_assertion None None) pres) in
	let ss_pres'  = List.map (fun (ss_pre, subst) ->
		let subst'     = filter_substitution subst spec_vars in
		let spec_vars' = SS.filter (fun x -> not (Hashtbl.mem subst' x)) spec_vars in
		let ss_pre'    = Simplifications.simplify_ss ss_pre (Some (Some spec_vars')) in
		(ss_pre', subst', spec_vars')) ss_pres in

	let n_specs = List.map (fun (ss_pre, subst, spec_vars) ->
		let post_gamma_0  = get_gamma ss_pre in
		let post_gamma_0' = filter_gamma_f post_gamma_0 (fun x -> SS.mem x spec_vars) in

		(** Step 3 - Normalise the postconditions associated with each pre           *)
		let ss_posts = oget_list (List.map (normalise_post post_gamma_0' subst spec_vars) posts) in
		{	n_pre      = ss_pre;
			n_post     = ss_posts;
			n_ret_flag = spec.ret_flag;
			n_lvars    = spec_vars;
			n_subst    = subst	}) ss_pres' in

	let n_specs' = List.filter (fun n_spec -> (List.length n_spec.n_post) > 0) n_specs in
	if (n_specs' = []) then (
		(* TODO: print the invalid specification *)
		let failed_spec_msg = Printf.sprintf "INVALID SPECIFICATION for %s:\n%s\n" spec_name
			(JSIL_Print.string_of_single_spec "" spec) in
		raise (Failure failed_spec_msg)
	) else n_specs'


(** -----------------------------------------------------
  * Normalise JSIL Spec
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_spec
	(predicates : (string, unfolded_predicate) Hashtbl.t)
	(spec       : jsil_spec) : jsil_n_spec =
	let time = Sys.time () in
 	print_debug (Printf.sprintf "Going to process the SPECS of %s. The time now is: %f\n" spec.spec_name time);
 	print_debug (Printf.sprintf "Normalised spec? %b" spec.previously_normalised);

  (** Treat pre-normalised specs differently *)
  let normalised_pre_post_list =
    match spec.previously_normalised with
    | true -> List.concat (List.map (normalise_single_normalised_spec spec.spec_name) spec.proc_specs)
    | false -> List.concat (List.map (normalise_single_spec predicates spec.spec_name) spec.proc_specs)
  in
	{	n_spec_name = spec.spec_name;
		n_spec_params = spec.spec_params;
		n_proc_specs = normalised_pre_post_list
	}


(** -----------------------------------------------------
  * Normalise JSIL Spec
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let build_spec_tbl
		(prog       : jsil_program)
		(predicates : (string, unfolded_predicate) Hashtbl.t)
		(onlyspecs  : (string, jsil_spec) Hashtbl.t)
		(lemmas     : (string, JSIL_Syntax.jsil_lemma) Hashtbl.t) : specification_table =

	let spec_tbl = Hashtbl.create 511 in
	let get_tbl_rng tbl = Hashtbl.fold (fun k v ac -> v :: ac) tbl [] in

	(** 1 - Normalise specs from                      *)
	(** 1.1 - from JSIL procedures
        1.2 - only specs
        1.3 - lemmas                                  *)
    let proc_tbl_rng = get_tbl_rng prog in
    let proc_specs     = List.concat (List.map (fun proc -> Option.map_default (fun ospec -> [ ospec ]) [] proc.spec) proc_tbl_rng) in
   	let only_specs     = get_tbl_rng onlyspecs in
   	let lemma_specs    = List.map (fun lemma -> lemma.lemma_spec) (get_tbl_rng lemmas) in
   	let non_proc_specs = only_specs @ lemma_specs in
   	List.iter (fun spec ->
   		let n_spec = normalise_spec predicates spec in
		Hashtbl.replace spec_tbl n_spec.n_spec_name n_spec
   	) (proc_specs @ non_proc_specs);


   	(** 2 - Dummy procs for only specs and lemmas
   	 *      The point of doing this is to use the find_and_apply_specs for both
   	 *      the symbolic execution of procedure calls and the application of
   	 *      lemmas *)
   	 let create_dummy_proc spec =
   		let dummy_proc = {
   	 		proc_name   = spec.spec_name;
			proc_body   = Array.make 0 (empty_metadata, SBasic SSkip);
			proc_params = spec.spec_params;
			ret_label   = None; ret_var = Some "ret";
			error_label = None; error_var = Some "err";
			spec = Some spec } in
		Hashtbl.replace prog spec.spec_name dummy_proc in
	List.iter create_dummy_proc non_proc_specs;
	spec_tbl

(** -----------------------------------------------------
  * Normalise Predicate Definitions
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_predicate_definitions
	(pred_defs : (string, unfolded_predicate) Hashtbl.t)
		: (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t =

	print_debug "Normalising predicate definitions.\n";
	let n_pred_defs = Hashtbl.create 31 in
	Hashtbl.iter
		(fun pred_name (pred : unfolded_predicate)  ->
      let definitions : ((string option) * jsil_logic_assertion) list = pred.definitions in
      print_debug (Printf.sprintf "Predicate %s previously normalised? %b" pred_name pred.previously_normalised_u_pred);
			let n_definitions =  List.rev (List.concat (List.map
        (fun (os, a) ->
          print_debug (Printf.sprintf "Normalising predicate definitions of: %s.\n" pred_name);
          (* Only normalise the assertion if not already normalised *)
          match pred.previously_normalised_u_pred with
              | true ->
                [os, normalise_normalised_assertion a]
              | false ->
                let pred_vars = get_assertion_vars false a in
                let a' = JSIL_Logic_Utils.push_in_negations a in
                match (normalise_assertion None None a') with
                | Some (ss, _) ->
                  let ss', _ = Simplifications.simplify_ss_with_subst ss (Some (Some pred_vars)) in
                  [ (os, ss') ]
                | None -> []
      ) definitions)) in
			let n_pred = {
				n_pred_name        = pred.name;
				n_pred_num_params  = pred.num_params;
				n_pred_params      = pred.params;
				n_pred_definitions = n_definitions;
				n_pred_is_rec      = pred.is_recursive
			} in
			Hashtbl.replace n_pred_defs pred_name n_pred) pred_defs;
	n_pred_defs


(** -----------------------------------------------------
  * Pre-Normalise Invariants in JSIL Program
  *    - before symbolically executing a program we
  *      autounfold all the non-recursive predicates and
  *      push-in negations
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let pre_normalise_invariants_proc
		(predicates : (string, unfolded_predicate) Hashtbl.t)
		(body       : (jsil_metadata * jsil_cmd) array) : unit =
	let f_pre_normalise a_list = List.map (fun a -> push_in_negations a) a_list in
	let len = Array.length body in
	for i = 0 to (len - 1) do
		let metadata, cmd = body.(i) in
		match metadata.invariant with
		| None -> ()
		| Some a -> (
				let unfolded_a = f_pre_normalise (auto_unfold predicates a) in
				match unfolded_a with
				| [] -> raise (Failure "invariant unfolds to ZERO assertions")
				| [ a ] -> body.(i) <- { metadata with invariant = Some a }, cmd
				| _ -> raise (Failure "invariant unfolds to MORE THAN ONE assertion")
			)
	done

let pre_normalise_invariants_prog
	(predicates : (string, unfolded_predicate) Hashtbl.t)
	(prog       : (string, jsil_procedure) Hashtbl.t) : unit =
	Hashtbl.iter (fun proc_name proc -> pre_normalise_invariants_proc predicates proc.proc_body) prog


let normalise_invariant
	(a         : jsil_logic_assertion)
	(gamma     : typing_environment)
	(spec_vars : SS.t)
	(subst     : substitution) : symbolic_state =
	let gamma_inv = filter_gamma_f gamma (fun x -> SS.mem x spec_vars) in
	let new_symb_state = Option.get (normalise_post gamma_inv subst spec_vars a) in
	new_symb_state



(** -----------------------------------------------------
  * Printing the results of the normalisation to a file
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let print_normaliser_results_to_file
    (spec_tbl : specification_table)
    (pred_defs : (string, n_jsil_logic_predicate) Hashtbl.t) : unit =

  (** Printing the spec assertions and spec table *)
  let string_of_single_spec_assertions
      (spec : jsil_n_single_spec) : string =
    let string_of_single_symb_state_assertion
        (symbolic_state : symbolic_state) : string =
      (* print_normalisation ("PRINTNG STRING OF SYMBOLIC STATE FOR SPEC");
         print_normalisation (Symbolic_State_Print.string_of_shallow_symb_state symbolic_state); *)
      JSIL_Print.string_of_logic_assertion (Symbolic_State_Utils.convert_symb_state_to_assertion symbolic_state false) true
    in
    let pre_assrt_str = "Pre:  " ^ string_of_single_symb_state_assertion spec.n_pre in
    let post_assrt_str = "\nPost: " ^ List.fold_left (fun acc ss -> acc ^ (string_of_single_symb_state_assertion ss)) "" spec.n_post in
    pre_assrt_str ^ post_assrt_str ^ "\n"
  in
  let string_of_spec_assertions
      (specs: jsil_n_single_spec list) : string =
    List.fold_left
      (fun acc spec ->
        acc ^ (string_of_single_spec_assertions spec)
      ) "" specs
  in
  let string_of_spec_tbl_assertions =
    Hashtbl.fold
      (fun pred_name pred acc ->
         acc ^ pred_name ^ "\n" ^ (string_of_spec_assertions pred.n_proc_specs) ^ "\n\n"
      ) spec_tbl ""
  in
  print_normalisation (Printf.sprintf "----------- NORMALISED SPEC ASSERTIONS -----------\n\n%s" string_of_spec_tbl_assertions);
  print_normalisation ("----------- NORMALISED SPEC TABLE -----------\n");
  print_normalisation (Symbolic_State_Print.string_of_n_spec_table spec_tbl);

  (** Printing the predicate table *)
  let string_of_normalised_predicate (pred : n_jsil_logic_predicate) : string =
      let params = List.fold_left (fun ac param -> ac ^ param ^ " ") "" pred.n_pred_params in
      "\n*** Normalised predicate ***\n" ^
      "Name : " ^ pred.n_pred_name ^ "\n" ^
      "Parameters : " ^ params ^ "\n" ^
      (Printf.sprintf "Recursive : %b\n" pred.n_pred_is_rec) ^
      (Printf.sprintf "Number of definitions: %d\n" (List.length pred.n_pred_definitions)) ^
      List.fold_left (fun ac (_, x) -> ac ^ "Definition:\n" ^ (JSIL_Print.string_of_logic_assertion (Symbolic_State_Utils.convert_symb_state_to_assertion x false) false) ^ "\n") "" pred.n_pred_definitions
  in
  let string_of_normalised_predicates (preds : (string, n_jsil_logic_predicate) Hashtbl.t) : string =
    Hashtbl.fold (fun pname pred ac -> ac ^ string_of_normalised_predicate pred) preds ""
  in
  print_normalisation (Printf.sprintf "----------- NORMALISED PREDICATE TABLE -----------");
  print_normalisation (string_of_normalised_predicates pred_defs)

(** -----------------------------------------------------
  * Generate a .njsil file from the normalised specs (normalisedSpecsPreds.njsil)
  * NB - This does not print the procs, just the preds and the specs, so the result will not be a syntactically valid output
  * -----------------------------------------------------
  * -----------------------------------------------------
 **)
let generate_nsjil_file
    (spec_tbl : specification_table)
    (pred_defs : (string, n_jsil_logic_predicate) Hashtbl.t) : unit =

  (* Printing the predicates *)
  let predicate_output
      (pred : n_jsil_logic_predicate) : string =
    let params_string = String.concat ", " pred.n_pred_params in
    let definitions_string_list = List.map (fun (_, x) ->  (JSIL_Print.string_of_logic_assertion (Symbolic_State_Utils.convert_symb_state_to_assertion x false) false)) pred.n_pred_definitions in
    let definitions_string = String.concat ",\n " definitions_string_list in
    "pred " ^ pred.n_pred_name ^ " (" ^ params_string ^ "): \n" ^ definitions_string ^ ";\n\n"
  in

  let string_of_normalised_predicates (preds : (string, n_jsil_logic_predicate) Hashtbl.t) : string =
    Hashtbl.fold (fun pname pred ac -> ac ^ predicate_output pred) preds ""
  in

  print_njsil_file (string_of_normalised_predicates pred_defs);

  (* Printing the specs - NOT THE PROCS *)
  let string_of_single_spec_assertions
      (spec : jsil_n_single_spec) : string =
    let string_of_single_symb_state_assertion
        (symbolic_state : symbolic_state) : string =

      JSIL_Print.string_of_logic_assertion (Symbolic_State_Utils.convert_symb_state_to_assertion symbolic_state false) false
    in
    let pre_assrt_str = "[[ " ^ (string_of_single_symb_state_assertion spec.n_pre) ^ " ]]" in
    let post_assrt_str = "\n[[ " ^ (List.fold_left (fun acc ss -> acc ^ (string_of_single_symb_state_assertion ss)) "" spec.n_post) ^ " ]]" in
    let ret_flag_str = (match spec.n_ret_flag with
                        | Normal -> "normal"
                        | Error -> "error") in
    pre_assrt_str ^ post_assrt_str ^ "\n" ^ ret_flag_str
  in
  let string_of_spec_assertions
      (specs: jsil_n_single_spec list) : string =
    let string_of_spec_assertions_list = List.map string_of_single_spec_assertions specs in
    String.concat ";\n\n " string_of_spec_assertions_list
  in
  let string_of_spec_tbl_assertions =
    Hashtbl.fold
      (fun spec_name (spec : jsil_n_spec) acc ->
         let params_str = String.concat ", " spec.n_spec_params in
         acc ^ "spec " ^ spec_name ^ "(" ^ params_str ^ ")" ^ "\n" ^ (string_of_spec_assertions spec.n_proc_specs) ^ "\n\n"
      ) spec_tbl ""
  in
  print_njsil_file (string_of_spec_tbl_assertions);
