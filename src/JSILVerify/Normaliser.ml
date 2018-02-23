open CCommon
open SCommon
open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils

exception InvalidTypeOfLiteral

let new_aloc_name var = aloc_prefix ^ var

let new_lvar_name var = lvar_prefix ^ var

(**
	le -> non - normalised logical expression
	subst -> table mapping variable and logical variable
	gamma -> table mapping logical variables + variables to types

	the store is assumed to contain all the program variables in le
*)
let rec normalise_lexpr ?(store : SStore.t option) ?(subst : substitution option) 
		(gamma : TypEnv.t) (le : jsil_logic_expr) =

	let store = Option.default (SStore.init [] []) store in 
	let subst = Option.default (init_substitution []) subst in 

	let f = normalise_lexpr ~store:store ~subst:subst gamma in
	
	let result = match le with
	| LLit _
	| LNone -> le
	| LVar lvar -> Option.default (LVar lvar) (Hashtbl.find_opt subst lvar)
	| ALoc aloc -> ALoc aloc (* raise (Failure "Unsupported expression during normalization: ALoc") Why not ALoc aloc? *)
	| PVar pvar ->
		let value = SStore.get store pvar in
		(match value with
		| Some value -> value
		| None -> 
			let new_lvar = fresh_lvar () in 
				SStore.put store pvar (LVar new_lvar); 
				Hashtbl.add subst pvar (LVar new_lvar);
				LVar new_lvar
		)

	| LBinOp (le1, bop, le2) ->
		let nle1 = f le1 in
		let nle2 = f le2 in
		(match nle1, nle2 with
			| LLit lit1, LLit lit2 ->
				let lit = JSIL_Interpreter.evaluate_binop (Hashtbl.create 1) bop (Literal lit1) (Literal lit2) in
					LLit lit
			| _, _ -> LBinOp (nle1, bop, nle2))

	| LUnOp (uop, le1) ->
		let nle1 = f le1 in
		(match nle1 with
			| LLit lit1 ->
				let lit = JSIL_Interpreter.evaluate_unop uop lit1 in
				LLit lit

			| _ -> 
				(match uop with
				| TypeOf ->
					let nle1 = f le1 in
					(match nle1 with
						| LLit llit -> LLit (Type (Literal.type_of llit))
						| LNone -> raise (Failure "Illegal Logic Expression: TypeOf of None")
						| LVar lvar ->
							(try LLit (Type (Hashtbl.find gamma lvar)) with _ -> LUnOp (TypeOf, LVar lvar))
								(* raise (Failure (Printf.sprintf "Logical variables always have a type, in particular: %s." lvar))) *)
						| ALoc _ -> LLit (Type ObjectType)
						| PVar _ -> raise (Failure "This should never happen: program variable in normalised expression")
						| LBinOp (_, _, _)
						| LUnOp (_, _) -> LUnOp (TypeOf, nle1)
						| LEList _ -> LLit (Type ListType)
						| LLstNth (list, index) ->
							(match list, index with
								| LLit (LList list), LLit (Num n) when (Utils.is_int n) ->
									let lit_n = (try List.nth list (int_of_float n) with _ ->
										raise (Failure "List index out of bounds")) in
									LLit (Type (Literal.type_of lit_n))
								| LLit (LList list), LLit (Num n) -> raise (Failure "Non-integer list index")
								| LEList list, LLit (Num n) when (Utils.is_int n) ->
									let le_n = (try List.nth list (int_of_float n) with _ ->
										raise (Failure "List index out of bounds")) in
									f (LUnOp (TypeOf, le_n))
								| LEList list, LLit (Num n) -> raise (Failure "Non-integer list index")
								| _, _ -> LUnOp (TypeOf, nle1))
						| LStrNth (str, index) ->
							(match str, index with
								| LLit (String s), LLit (Num n) when (Utils.is_int n) ->
									let _ = (try (String.get s (int_of_float n)) with _ ->
										raise (Failure "String index out of bounds")) in
									LLit (Type StringType)
								| LLit (String s), LLit (Num n) -> raise (Failure "Non-integer string index")
								| _, _ -> LUnOp (TypeOf, nle1)))
				| _ -> LUnOp (uop, nle1)))



	| LEList le_list ->
		let n_le_list = List.map (fun le -> f le) le_list in
		let all_literals, lit_list =
			List.fold_left
				(fun (ac, list) le ->
					match le with
					| LLit lit -> (ac, (list @ [ lit ]))
					| _ -> (false, list))
				(true, [])
				n_le_list in
		if (all_literals)
		then LLit (LList lit_list)
		else LEList n_le_list
		
	| LESet le_list ->
		let n_le_list = List.map (fun le -> f le) le_list in
		LESet n_le_list
		
	| LSetUnion le_list ->
		(* this can be better!!!! *)
		let n_le_list = List.map (fun le -> f le) le_list in
		LSetUnion n_le_list
		
		
	| LSetInter le_list ->
		let n_le_list = List.map (fun le -> f le) le_list in
		LSetInter n_le_list

	| LLstNth (le1, le2) ->
		let nle1 = f le1 in
		let nle2 = f le2 in
		(match nle1, nle2 with
			| LLit (LList list), LLit (Num n) when (Utils.is_int n) -> 
					(try LLit (List.nth list (int_of_float n)) with _ ->
						raise (Failure "List index out of bounds"))
			| LLit (LList list), LLit (Num n) -> raise (Failure "Non-integer list index")
			| LEList list, LLit (Num n) when (Utils.is_int n) -> 
					let le = (try (List.nth list (int_of_float n)) with _ ->
						raise (Failure "List index out of bounds")) in
					f le
			| LEList list, LLit (Num n) -> raise (Failure "Non-integer list index")
			| _, _ -> LLstNth (nle1, nle2))

	| LStrNth (le1, le2) ->
		let nle1 = f le1 in
		let nle2 = f le2 in
		(match nle1, nle2 with
			| LLit (String s), LLit (Num n) ->
				(try LLit (String (String.make 1 (String.get s (int_of_float n))))
				with _ -> raise (Failure "String index out of bounds"))
			| _, _ -> LStrNth (nle1, nle2)) in


		JSIL_Logic_Utils.infer_types_expr gamma result;
		result


(*  ------------------------------------------------------------------
 *  Auto-Unfolding Non-recursive Predicates in Assertions
 * 	------------------------------------------------------------------
 *	------------------------------------------------------------------
**)

type unfolded_predicate = {
	name                         : string;
	num_params                   : int;
	params                       : (jsil_var * Type.t option) list;
	definitions                  : ((string option) * jsil_logic_assertion) list;
	is_recursive                 : bool;
  is_pure                      : bool;
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
		  let pred : unfolded_predicate = Hashtbl.find predicates name in
			if pred.is_recursive then (
				(* If the predicate is recursive, only add the types of the parameters.           *)
				let types_asrt = List.fold_left2 (fun ac (_, ot) x ->
					(match ot with
					| None -> ac
					| Some t -> (match ac with
						| LEmp -> LTypes [ (x, t) ]
						| _ -> LStar (LTypes [ (x, t) ], ac)))) LEmp pred.params args in
				let asrt = (match types_asrt with
					| LEmp -> asrt
					| _ -> LStar (asrt, types_asrt)) in
				[ asrt ]
			)
			else
				(* If it is not, replace the predicate assertion for the list of its definitions
				   substituting the formal parameters of the predicate with the corresponding
				   logical expressions in the argument list *)
				let param_names, _ = List.split pred.params in
				let subst = init_substitution2 param_names args  in
				let new_asrts  = List.map (fun (_, a) -> asrt_substitution subst false a) pred.definitions in
				List.concat (List.map au new_asrts)
		 (* If the predicate is not found, raise an error *)
		with Not_found -> raise (Failure ("Error: Can't auto_unfold predicate " ^ name)))

	| _ -> [asrt]


(*  ------------------------------------------------------------------
 *  Auto-Unfolding Non-recursive Predicates in Pred definitions
 * 	------------------------------------------------------------------
 *	------------------------------------------------------------------
**)
let detect_trivia_and_nonsense (u_pred : unfolded_predicate) : unfolded_predicate =
	let new_definitions = List.map
		(fun (oc, x) -> oc, (Simplifications.reduce_assertion x)) u_pred.definitions in
	let new_definitions = List.filter (fun (oc, x) -> not (x = LFalse)) new_definitions in
	{ u_pred with definitions = new_definitions }

(*
   JSIL Predicates can have non-pvar parameters - to say that a given parameter
   always has a certain value...
*)
let replace_non_pvar_params (pred : jsil_logic_predicate) : unfolded_predicate =
	let new_params, new_asrts =
		List.fold_right
			(fun (cur_param, cur_param_type) (params, new_asrts) ->
				match cur_param with
				| LLit _ | LNone ->
					(* If the parameter is a JSIL literal or None...     *)
			  		(* Get a fresh program variable a add an additional
			  		   constraint to each definition *)
			  		let new_pvar = fresh_pvar () in
						print_debug_petar (Printf.sprintf "Generated fresh PVar: %s" new_pvar); 
			  		((new_pvar, None) :: params), (LEq (PVar new_pvar, cur_param) :: new_asrts)
			  	| PVar x         ->
			  		(* If the parameter is a program variable, add the
			  		   parameter as it is *)
						let new_asrts = (match cur_param_type with
							| None -> new_asrts
							| Some t -> LTypes [ PVar x, t ] :: new_asrts) in
			  		((x, cur_param_type) :: params, new_asrts)
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
    is_pure      = false;
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
	  		let msg = Printf.sprintf "Incompatible predicate definitions for: %s\n\tName:%s\tName:%s\n\tParams:%d\tParams:%d" pred1.name pred1.name pred2.name pred1.num_params pred2.num_params in
	  		raise (Failure msg)
	  ) else (
			let pred1_param_names, _ = List.split pred1.params in
			let pred2_param_names, _ = List.split pred2.params in
	  		let subst = init_substitution2 pred2_param_names (List.map (fun var -> PVar var) pred1_param_names) in
		  	let definitions = pred1.definitions @
		  		(List.map (fun (oid, a) -> oid, (asrt_substitution subst true a)) pred2.definitions) in
		  	{ pred1 with
          definitions = definitions;
          is_recursive = pred1.is_recursive || pred2.is_recursive;
          is_pure = pred1.is_pure && pred2.is_pure
        }
	  )


(* Given a Hashtbl of predicates, return a Hashtbl from predicate name
   to boolean meaning "recursive" or "not recursive"
*)
let find_recursive_preds (preds : (string, unfolded_predicate) Hashtbl.t) =
	let count = ref 0 in
	let max_index = 100_000 in
	let visited = Hashtbl.create (Hashtbl.length preds) in
	(* mark visited predicates and remember the smallest index they can go to *)
	let is_recursive_pred = Hashtbl.create (Hashtbl.length preds) in
	let open_pred = Hashtbl.create (Hashtbl.length preds) in
	(* remember which predicates are still in our DFS stack (to detect cycles) *)
	let rec explore pred_name =
		(* Tarjan's SCC algorithm on predicate nodes; if recursive,
			 returns the index where recursion starts, otherwise None *)
		match Hashtbl.find_opt visited pred_name with
			| Some min_index ->
				(* Already explored *)
				if Hashtbl.find open_pred pred_name then
					(* Part of the current component: recursivity detected *)
					Some min_index
				else
					(* A previously explored component *)
					None
			| None ->
				(* Exploring for the first time *)
				let index = !count in
				incr count;
				Hashtbl.add visited pred_name index;
				Hashtbl.add open_pred pred_name true;
				assert (Hashtbl.mem preds pred_name);
				(* make sure that the hash table is well-formed *)
				let pred = Hashtbl.find preds pred_name in
				let neighbours = (* Find the names of all predicates that the current predicate uses *)
					List.concat (List.map (fun (_, asrt) -> (get_asrt_pred_names asrt)) pred.definitions) in
				let min_index = (* Compute the smallest index reachable from its neighbours *)
					List.fold_left
				    (fun min_so_far neighbour_name ->
							match explore neighbour_name with
							| None -> min_so_far
							| Some index -> min min_so_far index
						)
					  max_index
					  neighbours in
				Hashtbl.replace open_pred pred_name false;
				(* This predicate is recursive if we have seen an index smaller or equal than its own *)
				if min_index <= index then
					(Hashtbl.replace visited pred_name min_index;
					Hashtbl.add is_recursive_pred pred_name true;
					Some min_index)
				else
					(Hashtbl.add is_recursive_pred pred_name false;
				  None)
	in
	(* Launch the exploration from each predicate, unless it's already been visited in a previous one *)
	Hashtbl.iter
	  (fun name _ ->
			if not (Hashtbl.mem visited name)
			  then ignore(explore name))
		preds;
	is_recursive_pred

let find_pure_preds (preds : (string, unfolded_predicate) Hashtbl.t) =
  let is_pure_pred = Hashtbl.create (Hashtbl.length preds) in
  (* we mark visited predicates and remember their pureness at the same time *)
  let rec explore pred_name =
    match Hashtbl.find_opt is_pure_pred pred_name with
      | Some is_pure -> (* predicate already visited *)
          is_pure
      | None -> (* discovering new predicate *)
          let is_pure_assertion (a : jsil_logic_assertion) =
            let f_ac a _ _ ac =
            match a with
              | LPred (pred_name, _) -> explore pred_name
              | LPointsTo _ | LEmp | LEmptyFields _
              | LMetaData _ | LExtensible _ -> false
              | _  -> List.for_all (fun b -> b) ac in
            JSIL_Logic_Utils.assertion_fold None f_ac None None a
          in

          Hashtbl.add is_pure_pred pred_name true;
          (* assume predicates are pure until proven otherwise,
             for recursive calls *)
          let pred = Hashtbl.find preds pred_name in
          let is_pure = List.for_all
            (fun (_, asrt) -> is_pure_assertion asrt) pred.definitions in

          Hashtbl.replace is_pure_pred pred_name is_pure;
          is_pure
    in
  Hashtbl.iter (fun pred_name _ -> ignore (explore pred_name)) preds;
  is_pure_pred


let auto_unfold_pred_defs (preds : (string, jsil_logic_predicate) Hashtbl.t) =
	let u_predicates = Hashtbl.create big_tbl_size in
	
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
    
	(* Detect recursive and pure predicates *)
	let is_recursive_pred = find_recursive_preds u_predicates in
  let is_pure_pred = find_pure_preds u_predicates in

	(* Tag predicates *)
	let u_tagged_predicates = Hashtbl.create (Hashtbl.length u_predicates) in
	Hashtbl.iter
	  (fun name pred ->
			Hashtbl.add u_tagged_predicates pred.name
			  { pred with 
          is_recursive = Hashtbl.find is_recursive_pred name;
          is_pure = Hashtbl.find is_pure_pred name })
		u_predicates;

	(* Auto-unfold the predicates in the definitions of other predicates *)
	let u_unfolded_predicates = Hashtbl.create (Hashtbl.length u_predicates) in
	Hashtbl.iter
	  (fun name pred ->
	  		let definitions' = List.flatten (List.map
	  			(fun (os, a) ->
	  				let as' = auto_unfold u_tagged_predicates a in
	  				let as' = List.map (fun a -> (os, a)) as' in
	  				as') pred.definitions) in
			Hashtbl.add u_unfolded_predicates pred.name
			(let ret_pred = { pred with definitions = definitions'; } in
  		  	 let ret_pred = detect_trivia_and_nonsense ret_pred in
  		  	 ret_pred))
		u_tagged_predicates;
	u_unfolded_predicates




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
		assertion_map None None (Some (logic_expression_map f_e None)) a in


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


(** Tries to rewrite logical expressions involving lists is the form: 
	    n_list ::= {{ E_1,  ..., E_n }} @ E | {{ E_1, ..., E_n }}
	where E is not of the form {{ E_1,  ..., E_n }}
 **)
let rec normalise_list_expressions (le : jsil_logic_expr) : jsil_logic_expr =
	let f = normalise_list_expressions in 
	
	match le with 
	
	(** Literals **)
	| LLit (LList lst) -> lift_lit_list_to_logical_expr (LList lst)

	| LLit _ -> le 

	(** lvar, aloc, pvar **)
	| LVar _ | ALoc _ | PVar _ -> le 

	(** Binary Operators **)
	| LBinOp (hd, LstCons, tl) -> 
		let hd' = f hd in 
		(match f tl with 
		| LEList lst                       -> LEList (hd' :: lst)
		| LBinOp (LEList lst, LstCat, tl') -> LBinOp (LEList (hd' :: lst), LstCat, tl') 
		| tl                               -> LBinOp (LEList [ hd' ], LstCat, tl))
	
	| LBinOp (lst_l, LstCat, lst_r) ->    
		(match f lst_l with 
		| LEList lst_l ->
			if ((List.length lst_l) = 0) then lst_r else ( 
			(match f lst_r with 
			| LEList lst_r                            -> LEList (lst_l @ lst_r)
			| LBinOp (LEList lst_rl, LstCat, lst_rr)  -> LBinOp (LEList (lst_l @ lst_rl) , LstCat, lst_rr)
			| lst_r                                   -> LBinOp (LEList lst_l, LstCat, lst_r)))
		| lst_l -> LBinOp (lst_l, LstCat, f lst_r))

	| LBinOp (le1, op, le2) -> LBinOp (f le1, op, f le2)

	(** Unary Operators **)
	| LUnOp (Car, lst) -> 
		(match f lst with 
		| LEList lst -> 
			(try List.hd lst with Failure _ -> raise (Failure "Invalid List Expression"))
		| LBinOp (LEList lst_l, LstCat, tl) -> 
			(try List.hd lst_l with Failure _ -> raise (Failure "Invalid List Expression"))
		| lst -> LUnOp(Car, lst))

	| LUnOp (Cdr, lst) -> 
		(match f lst with 
		| LEList lst -> 
			(try LEList (List.tl lst) with Failure _ -> raise (Failure "Invalid List Expression"))
		| LBinOp (LEList lst_l, LstCat, tl) -> 
			(try LBinOp (LEList (List.tl lst_l), LstCat, tl) with Failure _ -> raise (Failure "Invalid List Expression"))
		| lst -> LUnOp(Cdr, lst))

	| LUnOp (LstLen, le) ->
		(match f le with 
		| LEList lst                      -> LLit (Num (float_of_int (List.length lst)))
		| LBinOp (LEList lst, LstCat, tl) -> LBinOp (LLit (Num (float_of_int (List.length lst))), Plus, f (LUnOp (LstLen, tl)))
		| le                              -> LUnOp (LstLen, le))

	| LUnOp (op, le) -> LUnOp (op, f le) 

	| LLstNth (le, n) -> 
		(match (f le), (f n) with 
			| LEList lst, LLit (Num n) ->	
				(try List.nth lst (int_of_float n) with Failure _ -> raise (Failure "Invalid List Expression"))
			| LBinOp (LEList lst, LstCat, tl), LLit (Num n) when (n < (float_of_int (List.length lst))) -> 
				(try List.nth lst (int_of_float n) with Failure _ -> raise (Failure "Invalid List Expression"))
			| LBinOp (LEList lst, LstCat, tl), LLit (Num n) when (n >= (float_of_int (List.length lst))) -> 
				(LLstNth(tl, LLit (Num (n -. (float_of_int (List.length lst))))))
			| le, n -> LLstNth (le, n))	

	(** Uninteresting cases **)
	| LStrNth (le, le') -> LStrNth (f le, f le')
	| LEList lst        -> LEList (List.map f lst)
	| LESet lst         -> LESet (List.map f lst)  
	| LSetUnion lst     -> LSetUnion (List.map f lst)
	| LSetInter lst     -> LSetInter (List.map f lst)
	| LNone             -> LNone 


let reshape_list (le_list : jsil_logic_expr) (len : int) : (jsil_logic_expr list) * jsil_logic_expr = 
	(match le_list with 
	| LEList lst -> 
		let lst_l = Array.to_list (Array.sub (Array.of_list lst) 0 len) in 
		let lst_r = Array.to_list (Array.sub (Array.of_list lst) len ((List.length lst) - len)) in 
		lst_l, LEList lst_r 
	| LBinOp (LEList lst_l, LstCat, lst_r) -> 
		let lst_l'   = Array.to_list (Array.sub (Array.of_list lst_l) 0 len) in 
		let lst_l''  = Array.to_list (Array.sub (Array.of_list lst_l) len ((List.length lst_l) - len)) in 
		if ((List.length lst_l'') > 0) 
			then lst_l', LBinOp (LEList lst_l'', LstCat, lst_r)
			else lst_l', lst_r 
	| _ -> raise (Failure "DEATH: List could not be reshaped"))



(*  -----------------------------------------------------
	Resolving locations and lists
	-----------------------------------------------------
	_____________________________________________________
*)


let resolve_list (le : jsil_logic_expr) (pfs : jsil_logic_assertion list) : jsil_logic_expr = 

	(* print_debug (Printf.sprintf "resolve_list with lexpr %s and pfs:\n%s\n" 
		(JSIL_Print.string_of_logic_expression le)
		(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion pfs))); *)

	let rec search x pfs =
		(match pfs with
		| [] -> None
		
		| LEq (LVar x', le) :: rest
		| LEq (le, LVar x') :: rest  when x' = x ->
		    print_debug (Printf.sprintf "I found the equality %s!!!!\n"
		    	(JSIL_Print.string_of_logic_assertion (List.hd pfs))); 
			let le' = normalise_list_expressions le in
			(match le' with 
			| LEList le_lst  
			| LBinOp (LEList le_lst, LstCat, _) -> Some le' 
			| _ -> search x rest)

		| _ :: rest -> search x rest) in 


	match normalise_list_expressions le with 
	| LVar x -> 
		(match search x pfs with 
		| Some le -> le 
		| None    -> LVar x)
	| le     -> le 


let resolve_location (lvar : string) (pfs : jsil_logic_assertion list) : (string * substitution) option =
	
	let original_pfs = 
		List.map (fun a -> 
			match a with 
			| LEq (le1, le2) -> 
				let le1' = normalise_list_expressions le1 in 
				(match le1' with 
				| LEList _ 
				| LBinOp (LEList _, LstCat, _) -> LEq (le1', le2)
				| _ -> 
					let le2' = normalise_list_expressions le2 in
					LEq (le2', le1'))
			| _ -> a 
		) pfs in 

	(* Printf.printf "resolve_location with var %s and pfs:\n%s\n" lvar
		(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion original_pfs)); *) 

	let subst = init_substitution3 [] in 

	let rec shallow_loop pfs traversed_pfs found_other_bindings =
		(match pfs with
		| [] -> None, found_other_bindings
		
		| LEq (LVar cur_lvar, ALoc loc) :: rest
		| LEq (ALoc loc, LVar cur_lvar) :: rest  ->
			if (cur_lvar = lvar) 
				then Some loc, found_other_bindings
				else (
					Hashtbl.replace subst cur_lvar (ALoc loc); 
					shallow_loop rest ((List.hd pfs) :: traversed_pfs) true
				)

		| LEq (LVar cur_lvar, LLit (Loc loc)) :: rest
		| LEq (LLit (Loc loc), LVar cur_lvar) :: rest ->
			if (cur_lvar = lvar) 
				then Some loc, found_other_bindings 
				else (
					shallow_loop rest ((List.hd pfs) :: traversed_pfs) true
				)
		
		| LEq (le1, le2) :: rest ->
			(match le1 with 
			| LEList le1_lst 
			| LBinOp (LEList le1_lst, LstCat, _) ->
				let le2' = resolve_list le2 (traversed_pfs @ rest) in 
				(match le2' with 
				| LEList le2_lst 
				| LBinOp (LEList le2_lst, LstCat, _) -> 
					let min_len              = min (List.length le2_lst) (List.length le1_lst) in
					let le1_lst_l, le1_lst_r = reshape_list le1 min_len in 
					let le2_lst_l, le2_lst_r = reshape_list le2' min_len in 
					if ((List.length le1_lst_l) <> (List.length le2_lst_l)) then raise (Failure "DEATH") else (
						match shallow_loop_lists le1_lst_l le2_lst_l found_other_bindings with 
						| None, new_found_other_bindings -> 
							shallow_loop rest ((List.hd pfs) :: traversed_pfs) new_found_other_bindings
						| Some loc, new_found_other_bindings -> 
							Some loc, new_found_other_bindings)
				| _ -> shallow_loop rest ((List.hd pfs) :: traversed_pfs) found_other_bindings)
			| _ -> shallow_loop rest ((List.hd pfs) :: traversed_pfs) found_other_bindings)

		| _ :: rest -> shallow_loop rest ((List.hd pfs) :: traversed_pfs) found_other_bindings) 
	
	and shallow_loop_lists lst_1 lst_2 found_other_bindings = 
		shallow_loop (List.map2 (fun le1 le2 -> LEq (le1, le2)) lst_1 lst_2) [] found_other_bindings in

	let rec loop pfs =
		match shallow_loop pfs [] false with 
		| Some loc, _ -> Some (loc, subst) 
		| None, false -> None
		| None, true  -> loop (List.map (asrt_substitution subst true) pfs) in

	loop original_pfs


let resolve_location_from_lexpr (pfs : PFS.t) (le : jsil_logic_expr) : string option = 
	match le with
	| LLit (Loc l)
	| ALoc l        -> Some l
	| LVar x        -> Option.map (fun (result, _) -> result) (resolve_location x (PFS.to_list pfs)) 
	| _             -> None


(*  -----------------------------------------------------
	Normalise Logic Expressions
	-----------------------------------------------------
	_____________________________________________________
*)
let normalise_logic_expression 
		(store : SStore.t) (gamma : TypEnv.t) (subst : substitution)
		(le    : jsil_logic_expr) : jsil_logic_expr = 
	let le'           = normalise_lexpr ~store:store ~subst:subst gamma le in 
	le' 


(*  -----------------------------------------------------
	Normalise Pure Assertion (only one!)
	-----------------------------------------------------
	Invoke normalise_logic_expression on all the logic
	expressions of a
	_____________________________________________________
*)
let rec normalise_pure_assertion
		(store : SStore.t)
		(gamma : TypEnv.t)
		(subst : substitution)
		(assertion : jsil_logic_assertion) : jsil_logic_assertion =
	let fa = normalise_pure_assertion store gamma subst in
	let fe = normalise_logic_expression store gamma subst in
	let result = (match assertion with
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
			let msg = Printf.sprintf "normalise_pure_assertion can only process pure assertions: %s" (JSIL_Print.string_of_logic_assertion assertion) in
			raise (Failure msg)) in
		infer_types_asrt gamma result;
		result

(** -------------------------------------------------------------------
  * init_alocs: Generate the abstract locations for the normalised spec
  * -------------------------------------------------------------------
  * This function creates an abstract location for every program variable used in
  * a cell assertion or empty fields assertion.
  * Example: (x, "foo") -> _ => store(x)= $l_x, where $l_x is fresh
**)
let initialise_alocs
	(store : SStore.t) (gamma : TypEnv.t) (subst : substitution) (la : jsil_logic_assertion list) : unit =

	List.iter
	(fun a -> (match a with
		| LEmp -> ()

		| LPointsTo (PVar var, _, _)
		| LEmptyFields (PVar var, _)
		| LMetaData (PVar var, _) 
		| LExtensible (PVar var, _) ->
			if (not (SStore.mem store var))
				then SStore.put store var (ALoc (new_aloc_name var))

		| LPointsTo (LVar var, _, _)
		| LEmptyFields (LVar var, _) 
		| LMetaData (LVar var, _) 
		| LExtensible (LVar var, _) ->
			if (not (Hashtbl.mem subst var))
				then Hashtbl.add subst var (ALoc (new_aloc_name var))

		| LPointsTo    (ALoc _, _, _) | LPointsTo    (LLit (Loc _), _, _) 
		| LEmptyFields (ALoc _, _)    | LEmptyFields (LLit (Loc _), _)    
		| LMetaData    (ALoc _, _)    | LMetaData    (LLit (Loc _), _)    
		| LExtensible  (ALoc _, _)    | LExtensible  (LLit (Loc _), _) -> ()

		| _ -> raise (Failure (Printf.sprintf "initialise_alocs: untreatable assertion: %s" (JSIL_Print.string_of_logic_assertion a))))
	) la



(** -----------------------------------------------------
  * Normalise Pure Assertions
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_pure_assertions
		(store  : SStore.t)
		(gamma  : TypEnv.t)
		(subst  : substitution)
		(args   : SS.t option)
		(a      : jsil_logic_assertion) : PFS.t =

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
					if ((not (Hashtbl.mem pvar_equalities x)) && (not (SStore.mem store x)))
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
			let cur_var_deps = get_lexpr_pvars cur_le in
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
				SStore.put store var le'
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
	let fill_store args =
		let p_vars = Option.default (get_asrt_pvars a) args in 
		SS.iter
			(fun var -> if (not (SStore.mem store var)) then (SStore.put store var (LVar (new_lvar_name var)); ()))
			p_vars in

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
	(* 5 *) fill_store args;
	(* 6 *) normalise_pure_assertions ()


(** -----------------------------------------------------
  * Normalise Cell Assertions
  * (Initialise Symbolic Heap)
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let rec normalise_cell_assertions
		(heap : SHeap.t) (store : SStore.t)
		(p_formulae : PFS.t) (gamma : TypEnv.t)
		(subst : substitution) (a : jsil_logic_assertion) : unit =
	let f = normalise_cell_assertions heap store p_formulae gamma subst in
	let fe = normalise_logic_expression store gamma subst in

	let normalise_cell_assertion (loc : string) (le_f : jsil_logic_expr) (perm : Permission.t) (le_v : jsil_logic_expr) : unit = 
		let (field_val_pairs, default_val), metadata, ext = Option.default ((SFVL.empty, None), None, None) (Heap.find_opt heap loc) in
		Heap.replace heap loc (((SFVL.add (fe le_f) (perm, fe le_v) field_val_pairs), default_val), Option.map fe metadata, ext) in 

	match a with
	| LStar (a1, a2) -> f a1; f a2

	| LPointsTo (LVar var, le2, (perm, le3)) -> 
		let aloc = (try
			(match Hashtbl.find subst var with
			| ALoc aloc -> aloc
			| _ -> print_debug_petar ("oopsie!"); raise (Failure (Printf.sprintf "Not an ALoc in subst: %s" (JSIL_Print.string_of_logic_expression (SStore.get_unsafe store var)))))
			with _ -> raise (Failure (Printf.sprintf "Variable %s not found in subst table: %s!" var (JSIL_Print.string_of_substitution subst)))) in
		normalise_cell_assertion aloc le2 perm le3

	| LPointsTo (PVar var, le2, (perm, le3)) ->
		let aloc =
			(match SStore.get store var with
			| Some (ALoc aloc) -> aloc
			| Some _ -> raise (Failure (Printf.sprintf "Not an ALoc in subst: %s" (JSIL_Print.string_of_logic_expression (Hashtbl.find subst var))))
			| None _ -> raise (Failure (Printf.sprintf "Variable %s not found in store!" var))) in
		normalise_cell_assertion aloc le2 perm le3

	| LPointsTo (LLit (Loc loc), le2, (perm, le3)) -> normalise_cell_assertion loc le2 perm le3

	| LPointsTo (ALoc loc, le2, (perm, le3)) -> normalise_cell_assertion loc le2 perm le3

	| LPointsTo (_, _, _) ->
		raise (Failure (Printf.sprintf "Illegal PointsTo Assertion: %s" (JSIL_Print.string_of_logic_assertion a)))

	| _ -> ()


(** -----------------------------------------------------
  * Normalise Type Assertions
  * (Initialise Typing Environment)
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_type_assertions
		(store     : SStore.t)
		(gamma     : TypEnv.t)
		(type_list : (jsil_logic_expr * Type.t) list) : bool =

	let type_check_lexpr (le : jsil_logic_expr) (t : Type.t) : bool = 
		let le_type, success, _ = JSIL_Logic_Utils.type_lexpr gamma le in
		if (not success) then 
			raise (Failure (Printf.sprintf "normalise_type_assertions: expression %s not typable" (JSIL_Print.string_of_logic_expression le)))
		else
			Option.map_default
			(fun tt -> t = tt)
			(let new_gamma = JSIL_Logic_Utils.reverse_type_lexpr false gamma le t in
				Option.map_default (fun new_gamma -> TypEnv.extend gamma new_gamma; true) false new_gamma) le_type in

	List.fold_left 
	(fun ac (x, t) -> if (not ac) then false else (
	match x with
		| LLit lit -> (Literal.type_of lit) = t 

		| LVar x ->
			(* if x is a lvar, we simply add (x, t) to gamma *) 
			Hashtbl.replace gamma x t; true 

		| PVar x -> 
			let le = SStore.get store x in 
			(match le with 
			| Some le -> 
				(* if x is a pvar in the store, its type must be consistent 
				   with the expression to which it's mapped *)
				type_check_lexpr le t
			| None ->	
				(* if x is a pvar not in the store, we create a new logical 
				   variable #x, whose type is going to be set in the gamma 
				   to the type of x *)
				let new_lvar = fresh_lvar () in 
				SStore.put store x (LVar new_lvar);
				TypEnv.weak_update gamma new_lvar (Some t); 
				true)

		| le -> type_check_lexpr le t)
	) true type_list

(** -----------------------------------------------------
  * Normalise Predicate Assertions
  * (Initialise Predicate Set)
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_pred_assertions
	(store : SStore.t) (gamma : TypEnv.t)
	(subst : substitution) (a : jsil_logic_assertion) : predicate_set * (jsil_logic_assertion list) =
	let preds = preds_init () in

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
		let fe = normalise_logic_expression store gamma subst in
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
	let pfs = PFS.of_list new_assertions in
	Simplifications.sanitise_pfs store gamma pfs;
	preds, (PFS.to_list pfs)


(** -----------------------------------------------------
  * Normalise EmptyFields Assertions
  * (Initialise Symbolic Heap Domains)
  * -----------------------------------------------------
	* ERROR: TO FIX: EF can be duplicated
  * -----------------------------------------------------
**)
let normalise_ef_assertions
	(heap : SHeap.t) (store : SStore.t)
	(p_formulae : PFS.t) (gamma : TypEnv.t)
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
		print_debug_petar (Printf.sprintf "Location: %s" (JSIL_Print.string_of_logic_expression le_loc));
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

		let (fv_list, old_domain), metadata, ext = try Heap.find heap le_loc_name with Not_found -> (SFVL.empty, None), None, None in
		(match old_domain with
		| None -> Heap.replace heap le_loc_name ((fv_list, Some domain), metadata, ext)
		| Some _ -> raise (Failure "Duplicate EF assertion!")) in

	List.iter add_domain (get_all_empty_fields a)


let extend_typing_env_using_assertion_info
	(gamma : TypEnv.t) (a_list : jsil_logic_assertion list) : unit =
	List.iter (fun a ->
		match a with
		| LEq (LVar x, le) | LEq (le, LVar x)
		| LEq (PVar x, le) | LEq (le, PVar x) ->
			let x_type = TypEnv.get_type gamma x in
			(match x_type with
			| None ->
				let le_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
				TypEnv.weak_update gamma x le_type
			| Some _ -> ())
		| _ -> ()
	) a_list

(** -----------------------------------------------------
  * Normalise Metadata
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_metadata
	(heap : SHeap.t) (store : SStore.t)
	(p_formulae : PFS.t) (gamma : TypEnv.t)
	(subst : substitution) (a : jsil_logic_assertion) : unit =

	let rec get_all_metadata a =
		let n_lexpr = normalise_lexpr ~store:store ~subst:subst gamma in
		let f_ac a _ _ ac =
			match a with
			| LMetaData (le, md) ->
				let nle = n_lexpr le in
				let nmd = n_lexpr md in
				 (nle, nmd) :: (List.concat ac)
			| _ -> List.concat ac in
		let result = assertion_fold None f_ac None None a in
			print_debug_petar (Printf.sprintf "Normalising metadata:\n\t%s"
				(String.concat "\n\t" (List.map (fun (le1, le2) -> "(" ^ (JSIL_Print.string_of_logic_expression le1) ^ ", " ^ (JSIL_Print.string_of_logic_expression le2) ^ ")") result)));
			result in
	
	let metadata = get_all_metadata a in
	
	let md_hash = Hashtbl.create small_tbl_size in
	let md_heqs = Hashtbl.create small_tbl_size in
	let metadata : (string * jsil_logic_expr) list = List.fold_left 
		(fun ac (l, md) ->
			let loc = (match l with
			| ALoc loc
			| LLit (Loc loc) -> loc
			| _ -> raise (Failure (Printf.sprintf "Unsupported: metadata for a non-defined object %s." (JSIL_Print.string_of_logic_expression l)))) in
			(match (Hashtbl.find_opt md_hash loc) with
			| None -> Hashtbl.add md_hash loc md
			| Some md' -> Hashtbl.add md_heqs md' md);
			(loc, md) :: ac
		) [] metadata in
	
	print_debug_petar "Metadata Hash:";
	Hashtbl.iter (fun loc md -> print_debug_petar (Printf.sprintf "\t%s : %s" loc (JSIL_Print.string_of_logic_expression md))) md_hash;
	print_debug_petar "MEQ Hash:";
	Hashtbl.iter (fun md' md -> print_debug_petar (Printf.sprintf "\t%s : %s" (JSIL_Print.string_of_logic_expression md') (JSIL_Print.string_of_logic_expression md))) md_heqs;
	
	(** 
			What should be done? Iterate on the list: (l, md)
			
			H1: If l doesn't exist in the heap, we have to create it (with which extensibility?)
	*)
	List.iter (fun (loc, md) -> 
		(match (Heap.mem heap loc) with
		| false -> 
				Heap.replace heap loc ((SFVL.empty, None), Some md, None)
		| true  -> 
				let ((fv_list, domain), _, ext) = Heap.find heap loc in
					Heap.replace heap loc ((fv_list, domain), Some md, ext))
		) metadata;
		
		(* Now, it's time to merge the duplicates *)
		Hashtbl.iter (fun md_you_stay md_away ->
			(match md_you_stay, md_away with
			| ALoc ls, ALoc la -> 
					print_debug_petar (Printf.sprintf "About to substitute: %s for %s" ls la);
					let aloc_subst = Hashtbl.create 3 in 
					Hashtbl.add aloc_subst la md_you_stay;
					SStore.substitution_in_place aloc_subst store;
					pfs_substitution_in_place aloc_subst p_formulae;
					
					(* Manual heap merge *)
					let ((fv_list, domain), md, ext) = SHeap.get_unsafe heap ls in
					let ((fv_list', domain'), _, ext') = SHeap.get_unsafe heap la in
					if (ext <> ext') then raise (Failure "Impossible metadata.")
					else (
							SHeap.remove heap la;
							let new_domain = Symbolic_State_Utils.merge_domains p_formulae gamma domain domain' in
							SHeap.put heap ls (SFVL.union fv_list fv_list') new_domain md ext
						)

			(* More cases to follow... or not *)
			| _, _ -> ())
			) md_heqs

(** -----------------------------------------------------
  * Normalise Extensibility
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_extensibility
	(heap : SHeap.t) (store : SStore.t)
	(p_formulae : PFS.t) (gamma : TypEnv.t)
	(subst : substitution) (a : jsil_logic_assertion) : unit =

	let rec get_all_extens a =
		let n_lexpr = normalise_lexpr ~store:store ~subst:subst gamma in
		let f_ac a _ _ ac =
			match a with
			| LExtensible (le, b) ->
				let nle = n_lexpr le in
				 (nle, b) :: (List.concat ac)
			| _ -> List.concat ac in
		let result = assertion_fold None f_ac None None a in
			print_debug_petar (Printf.sprintf "Normalising extensibility:\n\t%s"
				(String.concat "\n\t" (List.map (fun (le1, b) -> "(" ^ (JSIL_Print.string_of_logic_expression le1) ^ ", " ^ (Extensibility.str b) ^ ")") result)));
			result in
	
	let extens = get_all_extens a in
	
	(** 
			What should be done? Iterate on the list: (l, md)
			
			H1: The l has to exist in the heap already - we don't want only extensibility assertions for an object
			H2: If the md is an object, then its abstract location should be in the heap, we don't allocate a new object based on extensibility 
	*)
	List.iter (fun (l, ext) -> 
		let loc = (match l with
			| ALoc loc
			| LLit (Loc loc) -> loc
			| _ -> raise (Failure (Printf.sprintf "Unsupported: extensibility for a non-defined object %s." (JSIL_Print.string_of_logic_expression l)))) in
		match (Heap.mem heap loc) with
		| false -> raise (Failure (Printf.sprintf "Unsupported: object %s only defined through extensibility." (JSIL_Print.string_of_logic_expression l)))
		| true  -> 
				let ((fv_list, domain), metadata, _) = Heap.find heap loc in
					Heap.replace heap loc ((fv_list, domain), metadata, Some ext)
		) extens

(**
  * ---------------------------------------------------------------------------
  * Symbolic state well-formedness checks
  * ---------------------------------------------------------------------------
  * 1. the underlying assumption that all the fields of a give an object are
  *    different from each other does not create a contradiction
  * ---------------------------------------------------------------------------
 *)

let make_all_different_assertion_from_fvlist (f_list : jsil_logic_expr list) : jsil_logic_assertion list =

	let rec make_all_different_assertion_from_field_and_flist field flist =
		let rec loop flist constraints =
			match flist with
			| [] -> constraints
			| f_name :: rest ->
				(match List.mem f_name rest with
				| true ->
					print_debug_petar (Printf.sprintf "Horror: Overlapping resources in %s"
						(String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le) flist)));
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
			(String.concat " " (List.map (fun x -> JSIL_Print.string_of_logic_expression x) f_list)));

	result

let get_heap_well_formedness_constraints heap =
	(* print_debug (Printf.sprintf "get_heap_well_formedness_constraints of heap:\n%s\n"
		(Symbolic_State_Print.string_of_shallow_symb_heap heap false));*)

	Heap.fold
		(fun field ((fv_list, _), _, _) constraints ->
			(match constraints with
			| [ LFalse ] -> [ LFalse ]
			| _ ->
  				let new_constraints = make_all_different_assertion_from_fvlist (SFVL.field_names fv_list) in
  				new_constraints @ constraints)) heap []


(** -----------------------------------------------------
  * Separate an assertion into 
  *   spatial, pure, typing, predicates
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let rec separate_assertion (a : jsil_logic_assertion) : jsil_logic_assertion list * jsil_logic_assertion list * (jsil_logic_expr * Type.t) list * (string * jsil_logic_expr list) list = 
	let f = separate_assertion in
	(match a with
	| LStar (al, ar) ->
		let sl, pl, tl, prl = f al in
		let sr, pr, tr, prr = f ar in
			(sl @ sr, pl @ pr, tl @ tr, prl @ prr)

	(* Spatial *)
	| LEmp | LPointsTo _ | LEmptyFields _ | LMetaData _ | LExtensible _ -> ([ a ], [], [], [])

	(* Typing *)
	| LTypes lst -> ([], [], lst, [])

	(* Predicates *)
	| LPred (name, params) -> ([], [], [], [ (name, params) ])

	(* Pure *)
    | _ -> ([], [ a ], [], []))

(** -----------------------------------------------------
  * Normalise Assertion
  * Given an assertion creates a symbolic state and a
  * substitution
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_assertion
		(gamma : TypEnv.t option)
		(subst : substitution option)
		(pvars : SS.t option)
		(a     : jsil_logic_assertion) : (symbolic_state * substitution) option =

	print_debug (Printf.sprintf "Normalising assertion:\n\t%s" (JSIL_Print.string_of_logic_assertion a));

	let falsePFs pfs = (DynArray.length pfs = 1) && (DynArray.get pfs 0 = LFalse) in

	(** Step 1 -- Preprocess list expressions - resolve l-nth(E, i) when possible  *)
	let a = pre_process_list_exprs a in

	(** Step 2a -- Create empty symbolic heap, symbolic store, typing environment, and substitution *)
	let heap  = SHeap.init () in
	let store = SStore.init [] [] in
	let gamma = Option.map_default TypEnv.copy (TypEnv.init ()) gamma in
	let subst = Option.map_default copy_substitution (init_substitution []) subst in

	(** Step 2b -- Separate assertion *)
	let spatial, pure, typing, preds = separate_assertion a in

	(** Step 3 -- Normalise type assertions and pure assertions
		* 3.1 - type assertions -> initialises gamma
		* 3.2 - pure assertions -> initialises store and pfs
	*)
	initialise_alocs store gamma subst spatial;
	let success = normalise_type_assertions store gamma typing in
	(match success with
	| false -> print_debug "WARNING: normalise_assertion: type assertions could not be normalised"; None
	| true -> 
		let p_formulae = normalise_pure_assertions store gamma subst pvars a in
		(match falsePFs p_formulae with
		| true -> print_debug "WARNING: normalise_assertion: pure formulae false"; None
		| false -> 
			(** Step 4 -- Add to the store the program variables that are not there yet, BUT for which we know the types *)
			extend_typing_env_using_assertion_info gamma (PFS.to_list p_formulae);

			(** Step 5 -- Normalise cell assertions, pred assertions, and ef assertions
				* 5.1 - cell assertions -> initialises heap
				* 5.2 - pred assertions -> initialises pred set
				* 5.3 - ef assertions   -> fills in the domain for the objects in the heap
			*)
			normalise_cell_assertions heap store p_formulae gamma subst a;
			let preds, new_assertions = normalise_pred_assertions store gamma subst a in
			extend_typing_env_using_assertion_info gamma new_assertions;
			pfs_merge p_formulae (PFS.of_list new_assertions);
			normalise_ef_assertions heap store p_formulae gamma subst a;

			(* NEW *)
			normalise_metadata heap store p_formulae gamma subst a;
			normalise_extensibility heap store p_formulae gamma subst a;

			(** Step 6 -- Check if the symbolic state makes sense *)
			let heap_constraints = get_heap_well_formedness_constraints heap in
			if (Pure_Entailment.check_satisfiability (heap_constraints @ (PFS.to_list p_formulae)) gamma)
				then ( 
					let ret_ss = (heap, store, p_formulae, gamma, preds) in 
					print_debug ( Printf.sprintf "normalise_assertion returning:\n %s\n and subst: %s\n" (Symbolic_State_Print.string_of_symb_state ret_ss) (JSIL_Print.string_of_substitution subst));

					(* The following must hold *)

					(* STATEMENT: Normalised assertions do not have program variables in the typing environment *)
					it_must_hold_that 
						(lazy (let pvars = SS.elements (SStore.domain store) in List.for_all (fun v -> not (Hashtbl.mem gamma v)) pvars));

					Some (ret_ss, subst)
				) else (print_debug "WARNING: normalise_assertion: returning None"; None)))

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

  print_debug (Printf.sprintf "Normalising pre-normalised assertion:\n\t%s" (JSIL_Print.string_of_logic_assertion a));

  (** Step 1 -- Create empty symbolic heap, symbolic store, typing environment, pred set and pfs *)
  let heap  : SHeap.t            = SHeap.init () in
  let store : SStore.t           = SStore.init [] [] in
  let gamma : TypEnv.t           = TypEnv.init () in
  let pfs   : PFS.t      = DynArray.make 0 in
  let preds : predicate_set      = DynArray.make 0 in

  (* Step 2 - Map over assertion, populate gamma, store and heap *)
  let populate_state_from_assertion a =
    (match a with
    | LTypes type_assertions ->
      let _ = List.map (fun (e, t) -> Hashtbl.replace gamma (JSIL_Print.string_of_logic_expression e) t) type_assertions in 
      (a, false)
    | LPointsTo (PVar loc, le2, (perm, le3))
		| LPointsTo (ALoc loc, le2, (perm, le3))
    | LPointsTo (LLit (Loc loc), le2, (perm, le3)) ->
      (* TODO: prefix locations with _ ? *)
      let (field_val_pairs, default_val), metadata, ext = (try Heap.find heap loc with _ -> (SFVL.empty, None), None, None) in
      Heap.replace heap loc (((SFVL.add le2 (perm, le3) field_val_pairs), default_val), metadata, ext);
      (a, false)
			
		| LEmptyFields (obj, domain) ->
      let loc = JSIL_Print.string_of_logic_expression obj in
      let (field_val_pairs, _), metadata, ext = (try Heap.find heap loc with _ -> (SFVL.empty, None), None, None) in
      Heap.replace heap loc ((field_val_pairs, Some domain), metadata, ext);
			(a, false)
			
		| LMetaData (obj, md) ->
  			let loc = JSIL_Print.string_of_logic_expression obj in
        let (field_val_pairs, domain), _, ext = (try Heap.find heap loc with _ -> (SFVL.empty, None), None, None) in
        Heap.replace heap loc ((field_val_pairs, domain), Some md, ext);
  			(a, false)
			
		| LExtensible (obj, b) ->
				let loc = JSIL_Print.string_of_logic_expression obj in
        let (field_val_pairs, domain), metadata, _ = (try Heap.find heap loc with _ -> (SFVL.empty, None), None, None) in
        Heap.replace heap loc ((field_val_pairs, domain), metadata, Some b);
        (a, false)
			
    | LEq ((PVar v), le)
    | LEq (le, (PVar v)) ->
      SStore.put store v le;
      (a, false)
			
		| LEq _
    | LNot _
    | LLess _
    | LLessEq _
    | LStrLess _
    | LSetMem _
    | LSetSub _ ->
      DynArray.add pfs a;
      (a, false)
    | LPred (s, les) ->
      DynArray.add preds (s, les);
      (a, false)
    | LStar _ ->
      	(a, true)
		| _ -> Printf.printf "Unsupported: %s" (JSIL_Print.string_of_logic_assertion a); exit 1)
  in
  let _ = assertion_map (Some populate_state_from_assertion) None None a in 

  print_debug (Printf.sprintf "\n----- AFTER \"NORMALISATION\": -----\n");
  print_debug (Printf.sprintf "Store: %s" (SStore.str store));
  print_debug (Printf.sprintf "Gamma: %s" (TypEnv.str gamma));
  print_debug (Printf.sprintf "Heap: %s" (SHeap.str heap));
  print_debug (Printf.sprintf "Pure Formulae: %s" (Symbolic_State_Print.string_of_pfs pfs));
  print_debug (Printf.sprintf "Preds: %s" (Symbolic_State_Print.string_of_preds preds));
  (heap, store, pfs, gamma, preds)

(** -----------------------------------------------------
  * Unification Plan
  *    - build an unification plan from a normalised 
  *      state 
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let old_create_unification_plan 
		(symb_state      : symbolic_state)
		(reachable_alocs : SS.t) : (jsil_logic_assertion list) =
	let heap, store, pf, gamma, preds = symb_state in 
	
	let heap                    = Heap.copy heap in 
	let locs_to_visit           = Queue.create () in 
	let unification_plan        = Queue.create () in 
	let marked_alocs            = ref SS.empty in 
	let abs_locs, concrete_locs = List.partition is_aloc_name (SS.elements (SHeap.domain heap)) in 

	let search_for_new_alocs_in_lexpr (le : jsil_logic_expr) : unit = 
		let alocs = get_lexpr_alocs le in 
		SS.iter (fun aloc -> 
			if (not (SS.mem aloc !marked_alocs)) then (
				marked_alocs := SS.add aloc !marked_alocs;  	
				Queue.add aloc locs_to_visit; ())) alocs in 

	let inspect_aloc () = 
		if (Queue.is_empty locs_to_visit) then false else (
			let loc     = Queue.pop locs_to_visit in 
			let le_loc  = if (is_aloc_name loc) then ALoc loc else LLit (Loc loc) in 
			match SHeap.get heap loc with
			(* The aloc does not correspond to any cell - it is an argument for a predicate *) 
			| None -> true
				
			(* The aloc correspond to a cell - get the fv_list, domain, metadata, extensibility *)
			| Some ((fv_list, domain), metadata, ext) ->
				(* Partition the field-value list into concrete and symbolic properties *)
				let fv_list_c, fv_list_nc = 
					SFVL.partition (fun le _ -> 
						match le with 
						| LLit (String _) -> true 
						| _               -> false 
					) fv_list in 
				let f = (fun le_f (perm, le_v) -> 
 					Queue.add (LPointsTo (le_loc, le_f, (perm, le_v))) unification_plan; 
 					search_for_new_alocs_in_lexpr le_v) in
				SFVL.iter f fv_list_c; SFVL.iter f fv_list_nc;
 				Option.may (fun domain -> Queue.add (LEmptyFields (le_loc, domain)) unification_plan) domain;
				(* Now, metadata *)
				Option.may (fun metadata -> 
					Queue.add (LMetaData (le_loc, metadata)) unification_plan;
					search_for_new_alocs_in_lexpr metadata) metadata;
				(* Now, extensibility *)
				Option.may (fun ext -> 
					Queue.add (LExtensible (le_loc, ext)) unification_plan) ext;
 				Heap.remove heap loc; 
 				true) in 

	(** Step 1 -- add concrete locs and the reachable alocs to locs to visit *)
	List.iter (fun loc -> Queue.add loc locs_to_visit) (concrete_locs @ (SS.elements reachable_alocs)) ; 

	(** Step 2 -- which alocs are directly reachable from the store *)
	SStore.iter store (fun x le -> search_for_new_alocs_in_lexpr le);

	(** Step 3 -- inspect the alocs that are in the queue *)
	while (inspect_aloc ()) do () done; 

	(** Step 4 -- add pred assertions *)
	List.iter (fun (pred_name, les) -> 
		List.iter search_for_new_alocs_in_lexpr les; 
		Queue.add (LPred (pred_name, les)) unification_plan; 
	) (preds_to_list preds);

	(** Step 5 -- inspect the alocs that are in the queue coming from step 4 *)
	while (inspect_aloc ()) do () done; 

	(** Step 6 -- return *)
	let unification_plan_lst = Queue.fold (fun ac a -> a :: ac) [] unification_plan in 
	let unification_plan_lst = List.rev unification_plan_lst in 
	print_debug_petar (Printf.sprintf "Heap length is %d" (Heap.length heap));
	if ((Heap.length heap) = 0) then (
		(* We found all the locations in the symb_state - we are fine! *)
   Queue.clear unification_plan;
   print_debug "New unification plan successful!";
   print_debug "Unification plan:";
   List.iter (fun asrt -> print_debug (JSIL_Print.string_of_logic_assertion asrt)) unification_plan_lst;
   print_debug "";
		unification_plan_lst
	) else (
		let msg = Printf.sprintf "create_unification_plan FAILURE!\nInspected alocs: %s\nUnification plan:%s\nDisconnected Heap:%s\nOriginal symb_state:\n%s\n" 
			(String.concat ", " (SS.elements !marked_alocs))
			(Symbolic_State_Print.string_of_unification_plan unification_plan_lst)
			(SHeap.str heap)
			(Symbolic_State_Print.string_of_symb_state symb_state) in 
		print_debug msg;
		raise (Failure msg)) 


let new_create_unification_plan
    (symb_state      : symbolic_state)
    (reachable_alocs : SS.t) : (jsil_logic_assertion list) =
  let heap, store, pf, gamma, preds = symb_state in

  let heap                    = Heap.copy heap in
  let unification_plan        = Queue.create () in
  let abs_locs, concrete_locs = List.partition is_aloc_name (SS.elements (SHeap.domain heap)) in

  print_debug "Creating unification plan.";
  print_debug "Symbolic state :";
  print_debug (Symbolic_State_Print.string_of_symb_state symb_state);

  (* Step 1 -- find all the variables: Locs, PVars and LVars *)
  
  let get_pred_vars (pred: string * (jsil_logic_expr list)) : SS.t =
    let _, lexprs = pred in
    List.fold_right (fun le ac -> SS.union (get_lexpr_vars le) ac) lexprs SS.empty in

  let heap_vars = List.fold_right (fun asrt ac -> SS.union (get_asrt_vars asrt) ac) (SHeap.assertions heap) SS.empty in
  let store_vars = SStore.fold store (fun x v ac -> SS.union (SS.add x (get_lexpr_vars v)) ac) SS.empty in
  let pf_vars = DynArray.fold_right (fun asrt ac -> SS.union (get_asrt_vars asrt) ac) pf SS.empty in
  let gamma_vars = Hashtbl.fold (fun x v ac -> SS.add x ac) gamma SS.empty in
  let preds_vars = DynArray.fold_right (fun pred ac -> SS.union (get_pred_vars pred) ac) preds SS.empty in

  let all_vars = List.fold_right SS.union [heap_vars; store_vars; pf_vars; gamma_vars; preds_vars; reachable_alocs] SS.empty in
  let concrete_locs = SS.of_list (List.filter (fun n -> not (is_aloc_name n)) (SS.elements (SHeap.domain heap))) in
  let init_vars = List.fold_right SS.union [store_vars; concrete_locs; reachable_alocs] SS.empty in

  let print_ss (name, ss) =
    print_debug (name ^ " variables:");
    SS.iter (fun s -> print_debug ("\t" ^ s)) ss in
  List.iter print_ss ["Heap", heap_vars; "Store", store_vars; "PF", pf_vars;
                      "Gamma", gamma_vars; "Preds", preds_vars; "Reachable", reachable_alocs;
                      "Initial", init_vars];
  print_debug "";

  (* Step 2 -- find all assertions *)

  let type_to_asrt (x : string) (t : Type.t) =
    let x_var = if is_lvar_name x then (LVar x) else (PVar x) in
    LTypes [x_var, t] in

  let heap_asrts = SHeap.assertions heap in
  let pf_asrts = DynArray.to_list pf in
  let gamma_asrts = Hashtbl.fold (fun x v ac -> (type_to_asrt x v)::ac) gamma [] in
  let pred_asrts = DynArray.fold_right (fun (n, les) ac -> (LPred (n, les))::ac) preds [] in

  let all_asrts = List.concat [heap_asrts; pf_asrts; gamma_asrts; pred_asrts] in

  (* duplicate assertions with multiple in-var sets (for now, only LEq) *)
  let duplicate_asrt asrt ac = match asrt with
    | LEq (le1, le2) -> LEq (le1, le2) :: LEq (le2, le1) :: ac
    | _ -> asrt::ac in
  let all_asrts = List.fold_right duplicate_asrt all_asrts [] in
  
  let print_asrts (name, asrts) =
    print_debug (name ^ " assertions:");
    List.iter (fun asrt -> print_debug ("\t" ^ (JSIL_Print.string_of_logic_assertion asrt))) asrts in

  List.iter print_asrts ["Heap", heap_asrts; "PF", pf_asrts; "Gamma", gamma_asrts; "Preds", pred_asrts];
  print_debug "";

  (* Step 3 -- build the dependency graph
    There are two kinds of nodes: variables and assertions.
     Edges flow from the in-variables of assertions to their out-variables.
     If an assertion has several possible sets of in-vars (like LEq), we
     create one node for each of them (TODO: not implemented right now).
     Here, an assertion is a couple (SS.t, SS.t), which represents the in-vars
     and the out-vars for the assertion. *)

  let nb_vars = SS.cardinal all_vars in
  let var_asrts = Hashtbl.create nb_vars in (* for each variable, the list of asrts of which it is an in-var *)
  SS.iter (fun var -> Hashtbl.add var_asrts var []) all_vars; (* it's too tedious to have to check everywhere else *)
  let seen_vars = Hashtbl.create nb_vars in
  let seen_heap_asrts = ref 0 in (* we count the heap assertions that we see to make sure that we unify them all *)

  let nb_asrts = List.length all_asrts in
  let asrt_array = DynArray.of_list all_asrts in
  let seen_in_vars = DynArray.init nb_asrts (fun k -> 0) in (* the number*)

  let fill_asrt (asrt_i : int) : (SS.t * SS.t) =
    let asrt = DynArray.get asrt_array asrt_i in
    let in_vars, out_vars = match asrt with
      | LPointsTo (le_loc, le_f, (perm, le_v)) ->
        SS.union (get_lexpr_vars le_loc) (get_lexpr_vars le_f), get_lexpr_vars le_v
      | LMetaData (le_loc, metadata) ->
        get_lexpr_vars le_loc, get_lexpr_vars metadata
      | LExtensible (le_loc, ext) ->
        get_lexpr_vars le_loc, SS.empty
      | LPred (name, param_les) ->
        (* assume predicates only have in-vars for now *)
        List.fold_right (fun p_le ac -> SS.union (get_lexpr_vars p_le) ac) param_les SS.empty, SS.empty
      | LTypes type_exprs ->
        List.fold_right (fun (le, t) ac -> SS.union (get_lexpr_vars le) ac) type_exprs SS.empty, SS.empty
      | LEq (le1, le2) ->
        (* LEqs are duplicated before this, so we can assume in = lhs and out = rhs *)
        get_lexpr_vars le1, get_lexpr_vars le2
      | _ -> get_asrt_vars asrt, SS.empty in
    let update_var var =
      let cur_asrts = Hashtbl.find var_asrts var in
      Hashtbl.replace var_asrts var (asrt_i::cur_asrts) in
    SS.iter update_var in_vars;
    print_debug (Printf.sprintf "filling assertion %s:" (JSIL_Print.string_of_logic_assertion asrt));
    print_debug ("\tIn vars: " ^ (SS.fold (fun s ss -> s ^ " " ^ ss) in_vars ""));
    print_debug ("\tOut vars: " ^ (SS.fold (fun s ss -> s ^ " " ^ ss) out_vars ""));
    in_vars, out_vars in

  let asrt_nodes = DynArray.init nb_asrts fill_asrt in
  let unification_plan = ref [] in

  SS.iter (fun var ->
      print_debug ("assertions using variable " ^ var ^ ":");
      List.iter (fun asrt_i ->
          let asrt = DynArray.get asrt_array asrt_i in
          print_debug ("\t" ^ (JSIL_Print.string_of_logic_assertion asrt))
        ) (Hashtbl.find var_asrts var)
    ) all_vars;
  print_debug "";

  (* Step 4 -- visit the assertion graph *)
  
  let rec visit_var (var : string) : unit =
    if not (Hashtbl.mem seen_vars var) then (
      print_debug ("visiting variable " ^ var);
      Hashtbl.add seen_vars var true;
      let children_asrts = Hashtbl.find var_asrts var in
      List.iter visit_asrt children_asrts
    )
  and visit_asrt (asrt_i : int) : unit =
    let in_vars, out_vars = DynArray.get asrt_nodes asrt_i in
    let cur_seen_in = DynArray.get seen_in_vars asrt_i in
    let asrt = DynArray.get asrt_array asrt_i in
    print_debug (Printf.sprintf "visiting assertion %s..." (JSIL_Print.string_of_logic_assertion asrt)); 
    DynArray.set seen_in_vars asrt_i (cur_seen_in + 1);
    if DynArray.get seen_in_vars asrt_i = SS.cardinal in_vars then (
      print_debug (Printf.sprintf "assertion %s OK!" (JSIL_Print.string_of_logic_assertion asrt));
      begin match asrt with
      | LPointsTo _
      | LMetaData _
      | LExtensible _
      | LEmptyFields _-> incr seen_heap_asrts;
      | _ -> ();
      end;
      unification_plan := asrt::(!unification_plan);
      SS.iter visit_var out_vars
    )
  in

  print_debug "Starting dependency graph traversal...";
  SS.iter visit_var init_vars;
  unification_plan := List.rev (!unification_plan);
  print_debug "";

  (** Step 7 -- we're done! *)
  print_debug (Printf.sprintf "saw %d heap assertions (out of %d)" !seen_heap_asrts (List.length heap_asrts));
  if (!seen_heap_asrts = (List.length heap_asrts)) then (
    (* We found all the locations in the symb_state - we are fine! *)
    print_debug "Unification plan successful!";
    print_debug "Unification plan:";
    List.iter (fun asrt -> print_debug (JSIL_Print.string_of_logic_assertion asrt)) !unification_plan;
    print_debug "";
  ) else (
    let msg = Printf.sprintf "create_unification_plan FAILURE!\nUnification plan:%s\nOriginal symb_state:%s\n" 
        (Symbolic_State_Print.string_of_unification_plan !unification_plan)
        (Symbolic_State_Print.string_of_symb_state symb_state) in
    print_debug msg;
    (* raise (Failure msg) *)
  );

  !unification_plan


let create_unification_plan symb_state reachable_alocs =
  let t0 = Sys.time () in
  let old_res = old_create_unification_plan symb_state reachable_alocs in
  let t1 = Sys.time () in
  let new_res = new_create_unification_plan symb_state reachable_alocs in
  let t2 = Sys.time () in
  print_debug (Printf.sprintf "Old unif. plan: %fs, new: %fs" (t1 -. t0) (t2 -. t1));
  old_res

(* Create unification plans for multiple symbolic states at the same time
	 Returns a Hashtbl from logic assertions to the symbolic states they appear in*)
let create_multiple_unification_plan
		(states : (symbolic_state * SS.t) list) :
		((jsil_logic_assertion, SI.t) Hashtbl.t) =
		
	let unification_plan = Hashtbl.create 31 in
	
	(* add a new assertion to the set *)
	let update_unification_plan symb_state_id asrt =
		if Hashtbl.mem unification_plan asrt then
			let former_set = Hashtbl.find unification_plan asrt in
			Hashtbl.replace unification_plan asrt (SI.add symb_state_id former_set)
		else
			Hashtbl.add unification_plan asrt (SI.singleton symb_state_id) in

	let create_single_unification_plan
			(symb_state_id : int)
			(state : (symbolic_state * SS.t)) =
		let symb_state, reachable_alocs = state in
		let sorted_assertions = create_unification_plan symb_state reachable_alocs in
		List.iter (update_unification_plan symb_state_id) sorted_assertions in
	List.iteri create_single_unification_plan states;
	unification_plan


let is_overlapping_aloc (pfs_list : jsil_logic_assertion list) (aloc : string) : (string * substitution) option =

	let x         = fresh_lvar () in 
	let subst     = init_substitution3 [ (aloc, LVar x) ] in 
	let pfs_list' = List.map (asrt_substitution subst true) pfs_list in 

	print_debug (Printf.sprintf "is_overlapping_aloc with aloc: %s. new_var: %s. pfs:\n%s" aloc x
		(String.concat "; " (List.map JSIL_Print.string_of_logic_assertion pfs_list'))
	);

	let loc       = resolve_location x pfs_list' in	 
	match loc with 
	| Some (loc, subst) -> 
			print_debug (Printf.sprintf "Found the overlap %s" loc);
			print_debug (Printf.sprintf "Substitution: %s" (JSIL_Print.string_of_substitution subst)); 
			Some (loc, subst)
	| None        -> print_debug "Could NOT find the overlap\n"; None 


let collapse_alocs (ss_pre : symbolic_state) (ss_post : symbolic_state) : symbolic_state option = 
	let pfs_pre  = (ss_pfs ss_pre) in 
	let pfs_post = (ss_pfs ss_post) in 
	let pfs_list = (PFS.to_list pfs_pre) @ (PFS.to_list pfs_post) in 
	let pfs      = (PFS.of_list pfs_list) in 
	
	print_debug_petar (Printf.sprintf "ENTERING COLLAPSE_ALOCS with\n\nPrecondition:\n%s\nPostcondition:\n%s"
		(Symbolic_State_Print.string_of_symb_state ss_pre) (Symbolic_State_Print.string_of_symb_state ss_post));

	if (Pure_Entailment.check_satisfiability pfs_list (ss_gamma ss_post)) then Some ss_post else (
		print_normal (Printf.sprintf "SPEC with inconsistent alocs was found.\npre_pfs:\n%s\npost_pfs:\n%s\n"
			(Symbolic_State_Print.string_of_pfs pfs_pre) (Symbolic_State_Print.string_of_pfs pfs_post)
		); 

		let alocs_post         = ss_alocs ss_post in 
		let alocs_pre          = ss_alocs ss_pre  in 
		let new_alocs_post     = SS.filter (fun aloc -> (not (SS.mem aloc alocs_pre))) alocs_post in 
		let constrained_alocs  = pfs_alocs pfs in 
		let relevant_new_alocs = SS.inter constrained_alocs new_alocs_post in 

		(* print_debug (Printf.sprintf "relevant_new_alocs: %s\n" 
			(String.concat ", " (SS.elements relevant_new_alocs))); *)

		let aloc_subst = init_substitution [] in 
		SS.iter (fun aloc -> 
			match is_overlapping_aloc pfs_list aloc with 
			| None        -> () 
			| Some (aloc', subst) -> Hashtbl.replace aloc_subst aloc (ALoc aloc'); ()
		) relevant_new_alocs; 

		let new_pfs_post = pfs_substitution aloc_subst true pfs_post in 
		let new_pfs_list = (PFS.to_list pfs_pre) @ (PFS.to_list new_pfs_post) in 

		if (Pure_Entailment.check_satisfiability new_pfs_list (ss_gamma ss_post)) then (
			Some (ss_substitution aloc_subst true ss_post) 
		) else (
			print_normal(Printf.sprintf "Incompatible something inside collapse_alocs. new_pfs_list: %s\ngamma: %s\n" 
				(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion new_pfs_list))
				(TypEnv.str (ss_gamma ss_post))); 
			None
		)
	)



(** Normalise Postcondition
	-----------------------
	Each normalised postcondition postcondition may map additional spec vars
	to alocs. In order not to lose the link between the newly generated alocs
	and the precondition spec vars, we need to introduce extra equalities *)
let normalise_post
		(post_gamma_0  : TypEnv.t)
		(subst         : substitution)
		(spec_vars     : SS.t)
		(params        : SS.t)
		(post          : jsil_logic_assertion) : symbolic_state option =
	(match (normalise_assertion (Some post_gamma_0) (Some subst) (Some params) post) with
	| None -> None
	| Some (ss_post, post_subst) ->
		let post_new_spec_var_alocs =
			SS.elements (SS.filter (fun x -> (not (Hashtbl.mem subst x)) && (Hashtbl.mem post_subst x)) spec_vars) in
		print_debug (Printf.sprintf "post substitution:\n%s\npost_new_spec_var_alocs: %s\n"
			(JSIL_Print.string_of_substitution post_subst)
			(String.concat ", " post_new_spec_var_alocs));
		let extra_post_pfs = List.map (fun x -> LEq (LVar x, Hashtbl.find post_subst x)) post_new_spec_var_alocs in
		ss_extend_pfs ss_post (PFS.of_list extra_post_pfs);
		Some (Simplifications.simplify_ss ss_post (Some (Some spec_vars))))

(** -----------------------------------------------------
  * Normalise Pre-Normalised Single Spec
  * -----------------------------------------------------
  * -----------------------------------------------------
 **)
let normalise_single_normalised_spec
    (spec_name  : string)
    (spec       : jsil_single_spec) : jsil_n_single_spec list =

  (** Step 1 - "Normalise" precondition                                     *)
  (* TODO: check: we always only have 1 pre as the specs are already unfolded? *)
  let pre : symbolic_state = normalise_normalised_assertion spec.pre in

  (** Step 2 - "Normalise" the posts *)
  let spec_vars = get_asrt_lvars spec.pre in
  let posts : symbolic_state list = List.map normalise_normalised_assertion spec.post in
	
	[{
      n_pre              = pre;
  		n_post             = posts;
  		n_ret_flag         = spec.ret_flag;
  		n_lvars            = spec_vars;
      n_subst            = init_substitution []; 
      n_unification_plan = (create_unification_plan pre SS.empty)
	}]

(** -----------------------------------------------------
  * Normalise Single Spec
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_single_spec
	(predicates : (string, unfolded_predicate) Hashtbl.t)
	(spec_name  : string)
	(params     : SS.t)
	(spec       : jsil_single_spec) : jsil_n_single_spec list =

	let oget_list lst = List.map Option.get (List.filter (fun x -> not (x = None)) lst) in

	let pre_normalise (a : jsil_logic_assertion) : jsil_logic_assertion list =
		List.map JSIL_Logic_Utils.push_in_negations (auto_unfold predicates a) in

	print_debug (Printf.sprintf "Normalising the following spec of %s:\n%s\n" spec_name
			(JSIL_Print.string_of_single_spec "" spec));

	(** Step 1 - Unfold non-recursive predicates + push-in negations *)
	let spec_vars = get_asrt_lvars spec.pre in
	let pres      = pre_normalise spec.pre in
	let posts     = List.concat (List.map pre_normalise spec.post) in

	(** Step 2 - Normalise preconditions                                     *)
	(** Spec vars mapped to alocs in the precondition MUST also be
	    substituted in the postcondition - so they cease to be spec vars     *)
	let ss_pres   = oget_list (List.map (normalise_assertion None None (Some params)) pres) in
	let ss_pres'  = List.map (fun (ss_pre, subst) ->
		let subst'     = filter_substitution_set spec_vars subst in
		let spec_vars' = SS.filter (fun x -> not (Hashtbl.mem subst' x)) spec_vars in
		let ss_pre'    = Simplifications.simplify_ss ss_pre (Some (Some spec_vars')) in
		(ss_pre', subst', spec_vars')) ss_pres in

	let n_specs = List.map (fun (ss_pre, subst, spec_vars) ->
		let post_gamma_0  = ss_gamma ss_pre in
		let post_gamma_0' = TypEnv.filter post_gamma_0 (fun x -> SS.mem x spec_vars) in

		(** Step 3 - Normalise the postconditions associated with each pre           *)
		let ss_posts = oget_list (List.map (normalise_post post_gamma_0' subst spec_vars params) posts) in
		let ss_posts = oget_list (List.map (fun ss_post -> collapse_alocs ss_pre ss_post) ss_posts) in 
		let ss_posts = List.map (fun ss_post -> Simplifications.simplify_ss ss_post (Some (Some spec_vars))) ss_posts in 
		{	n_pre              = ss_pre;
			n_post             = ss_posts;
			n_ret_flag         = spec.ret_flag;
			n_lvars            = spec_vars;
			n_subst            = subst; 
			n_unification_plan = (create_unification_plan ss_pre SS.empty) }) ss_pres' in

	let n_specs' = List.filter (fun n_spec -> (List.length n_spec.n_post) > 0) n_specs in
	if (n_specs' = []) then (
		(* TODO: print the invalid specification *)
		let failed_spec_msg = Printf.sprintf "INVALID SPECIFICATION for %s:\n%s\n" spec_name
			(JSIL_Print.string_of_single_spec "" spec) in
		print_debug failed_spec_msg;
		raise (Failure failed_spec_msg)
	) else 
	(
		n_specs'
	)


(** -----------------------------------------------------
  * Normalise JSIL Spec
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_spec
	(predicates : (string, unfolded_predicate) Hashtbl.t)
	(spec       : jsil_spec) : jsil_n_spec =
	let time = Sys.time () in
 	print_debug (Printf.sprintf "Going to process the SPECS of %s. There are %d of them. The time now is: %f\n" spec.spec_name (List.length spec.proc_specs) time);
 	print_debug (Printf.sprintf "Normalised spec? %b" spec.previously_normalised);

  (** Treat pre-normalised specs differently *)
  let normalised_pre_post_list =
    match spec.previously_normalised with
    | true -> List.concat (List.map (normalise_single_normalised_spec spec.spec_name) spec.proc_specs)
    | false -> List.concat (List.map (normalise_single_spec predicates spec.spec_name (SS.of_list spec.spec_params)) spec.proc_specs)
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
	(* Collapses a hashtable into a list of values *)
	let get_tbl_rng tbl = Hashtbl.fold (fun k v ac -> v :: ac) tbl [] in

	(** 1 - Normalise specs from                      *)
	(** 1.1 - from JSIL procedures
        1.2 - only specs
        1.3 - lemmas                                  *)
    let proc_tbl_rng   = get_tbl_rng prog in
    let proc_specs     = List.concat (List.map (fun proc -> Option.map_default (fun ospec -> [ ospec ]) [] proc.spec) proc_tbl_rng) in
   	let only_specs     = get_tbl_rng onlyspecs in
   	(* Build a list of the lemma specs *)
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
			proc_body   = Array.make 0 (empty_metadata, Basic Skip);
			proc_params = spec.spec_params;
			ret_label   = None; ret_var = Some "xret";
			error_label = None; error_var = Some "xerr";
			spec = Some spec } in
		Hashtbl.replace prog spec.spec_name dummy_proc in
	List.iter create_dummy_proc (lemma_specs @ only_specs);
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
				let param_names, _ = List.split pred.params in 
    		let definitions : ((string option) * jsil_logic_assertion) list = pred.definitions in
    		print_debug (Printf.sprintf "Predicate %s previously normalised? %b" pred_name pred.previously_normalised_u_pred);
			let n_definitions =  List.rev (List.concat (List.map
    			(fun (os, a) ->
       				print_debug (Printf.sprintf "Normalising predicate definitions of: %s.\n" pred_name);
          			(* Only normalise the assertion if not already normalised *)
          			match pred.previously_normalised_u_pred with
           			| true ->
           				let ss = normalise_normalised_assertion a in  
                		[os, ss, (create_unification_plan ss SS.empty) ]
              		| false ->
                		let pred_vars = get_asrt_lvars a in
                		let a' = JSIL_Logic_Utils.push_in_negations a in
                		match (normalise_assertion None None (Some (SS.of_list param_names)) a') with
                		| Some (ss, _) ->
                  			let ss', _ = Simplifications.simplify_ss_with_subst ss (Some (Some pred_vars)) in
                  			[ (os, ss', (create_unification_plan ss' SS.empty)) ]
                		| None -> []
     			) definitions)) in
			let n_pred = {
				n_pred_name        = pred.name;
				n_pred_num_params  = pred.num_params;
				n_pred_params      = param_names;
				n_pred_definitions = n_definitions;
				n_pred_is_rec      = pred.is_recursive;
        n_pred_is_pure     = pred.is_pure 
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

	let f_pre_normalise_with_single_output a msg = 
		let unfolded_a = f_pre_normalise (auto_unfold predicates a) in
		match unfolded_a with
		| []    -> raise (Failure (msg ^ " unfolds to ZERO assertions"))
		| [ a ] -> a
		| _     -> raise (Failure (msg ^ " unfolds to MORE THAN ONE assertion")) in 

	let f_rewrite_lcmds lcmd = 
			match lcmd with 
			| Assert a -> Assert (f_pre_normalise_with_single_output a "assert")
			| _        -> lcmd in 

	let len = Array.length body in
	for i = 0 to (len - 1) do
		let metadata, cmd = body.(i) in
		let new_invariant  = Option.map_default (fun a -> Some (f_pre_normalise_with_single_output a "invariant")) None metadata.invariant in 
		let new_pre_lcmds  = List.map (logic_command_map (Some f_rewrite_lcmds) None None) metadata.pre_logic_cmds in 
		let new_post_lcmds = List.map (logic_command_map (Some f_rewrite_lcmds) None None) metadata.post_logic_cmds in 
		body.(i) <- { metadata with invariant = new_invariant; pre_logic_cmds = new_pre_lcmds; post_logic_cmds = new_post_lcmds }, cmd
	done

let pre_normalise_invariants_prog
	(predicates : (string, unfolded_predicate) Hashtbl.t)
	(prog       : (string, jsil_procedure) Hashtbl.t) : unit =
	Hashtbl.iter (fun proc_name proc -> pre_normalise_invariants_proc predicates proc.proc_body) prog


let normalise_invariant 
	(a         : jsil_logic_assertion)
	(gamma     : TypEnv.t)
	(spec_vars : SS.t)
	(subst     : substitution)
	(params    : SS.t) : symbolic_state = 
	let gamma_inv = TypEnv.filter gamma (fun x -> SS.mem x spec_vars) in
	let new_symb_state = Option.get (normalise_post gamma_inv subst spec_vars params a) in
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

      JSIL_Print.string_of_logic_assertion (assertion_of_symb_state symbolic_state)
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
      (Printf.sprintf "Pure : %b\n" pred.n_pred_is_pure) ^
      (Printf.sprintf "Number of definitions: %d\n" (List.length pred.n_pred_definitions)) ^
      List.fold_left (fun ac (_, x, _) -> ac ^ "Definition:\n" ^ (JSIL_Print.string_of_logic_assertion (assertion_of_symb_state x)) ^ "\n") "" pred.n_pred_definitions
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
		ext_prog
    (spec_tbl : specification_table)
    (pred_defs : (string, n_jsil_logic_predicate) Hashtbl.t) : unit =

  (* Printing the predicates *)
  let predicate_output
		(pred : n_jsil_logic_predicate) : string =
    let params_string = String.concat ", " pred.n_pred_params in
    let definitions_string_list = List.map (fun (_, x, _) ->  (JSIL_Print.string_of_logic_assertion (assertion_of_symb_state x))) pred.n_pred_definitions in
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
			JSIL_Print.string_of_logic_assertion (assertion_of_symb_state symbolic_state) 
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
				let spec_type, string_of_proc = (match Hashtbl.mem ext_prog.procedures spec_name with
				| false -> print_debug_petar (Printf.sprintf "Unable to find procedure: %s. Going with only spec." spec_name); "only spec ", ""
				| true -> 
					let proc = Hashtbl.find ext_prog.procedures spec_name in
					"spec ", JSIL_Print.string_of_ext_procedure_body proc) in  
				let params_str = String.concat ", " spec.n_spec_params in
				acc ^ spec_type ^ spec_name ^ "(" ^ params_str ^ ")" ^ "\n" ^ (string_of_spec_assertions spec.n_proc_specs) ^ "\n\n" ^ string_of_proc ^ "\n\n"
		) spec_tbl ""
  in
  print_njsil_file (string_of_spec_tbl_assertions)

(** -----------------------------------------------------
  * Generates the lemma cyclic dependency graph
  * -----------------------------------------------------
  * -----------------------------------------------------
 **)
let check_lemma_cyclic_dependencies 
	(lemmas : ((string, jsil_lemma) Hashtbl.t)) : unit =

	(* Initialise the graph *)
	let lemma_depd_graph : lemma_depd_graph = {
		lemma_depd_names_ids = Hashtbl.create 30;
		lemma_depd_ids_names = Hashtbl.create 30;
		lemma_depd_edges     = Hashtbl.create 30
	} in

	(* Map names to ID's, and intialise the edges lists *)
	Hashtbl.fold
		(fun lemma_name lemma count ->
			Hashtbl.replace lemma_depd_graph.lemma_depd_names_ids lemma_name count;
			Hashtbl.replace lemma_depd_graph.lemma_depd_ids_names count lemma_name;
			Hashtbl.replace lemma_depd_graph.lemma_depd_edges count [];
			count + 1
		) lemmas 0;

	(* Add all the ApplyLemma targets to the edges table *)
	Hashtbl.iter
		(fun curr_lemma lemma ->
			match lemma.lemma_proof with
			| None -> ()
			| Some proof ->
				List.iter
					(fun lcmd ->
						print_debug (JSIL_Print.string_of_lcmd lcmd);

						let f_l
							(lcmd : jsil_logic_command) : jsil_logic_command =

							match lcmd with
							| ApplyLem (applied_lemma, _) ->
							   (if (not (applied_lemma = curr_lemma)) then
							  
							   		(* Look up the ID's for the current and applied lemmas,
							   		   and add the applied lemma to the list of edges *)
									let curr_lemma_id    = Hashtbl.find lemma_depd_graph.lemma_depd_names_ids curr_lemma in
									let applied_lemma_id = Hashtbl.find lemma_depd_graph.lemma_depd_names_ids applied_lemma in
									let edges            = Hashtbl.find lemma_depd_graph.lemma_depd_edges curr_lemma_id in
							   		Hashtbl.replace lemma_depd_graph.lemma_depd_edges curr_lemma_id (List.cons applied_lemma_id edges));
							   lcmd
							| _ -> lcmd

						in

						logic_command_map (Some f_l) None None lcmd;
						()
					) proof
		) lemmas;

	(* Store our journey through the graph, and the start/end times for each node *)
	let visited_nodes    = Hashtbl.create 30 in
	let start_time_nodes = Hashtbl.create 30 in
	let end_time_nodes   = Hashtbl.create 30 in

	(* Returns the "clock" time at the end of the traversal *)
	let rec clockDFS
		(curr_node : int)
		(clock : int) : int =

		(* Recording start time for this node *)
		Hashtbl.replace start_time_nodes curr_node clock;
		let clock = clock + 1 in
		Hashtbl.replace visited_nodes curr_node true;

		(* Getting all the children *)
		let children : (int list) = Hashtbl.find lemma_depd_graph.lemma_depd_edges curr_node in

		(* Visiting each of the children, keeping track of the time *)
		let end_clock =	List.fold_left
			(fun clock child ->
				if (not (Hashtbl.mem visited_nodes child)) then
					clockDFS child clock
				else
					clock
			) clock children
		in

		(* Recording the end time for this node *)
		Hashtbl.replace end_time_nodes curr_node end_clock;
		end_clock + 1
	in

	(* Traverses the graph, recording the clock times at each node *)
	Hashtbl.fold
		(fun name id clock ->
			if (not (Hashtbl.mem visited_nodes id)) then
				clockDFS id clock
			else
				clock
		) lemma_depd_graph.lemma_depd_names_ids 0;

	(* Check all the edges for back-edges *)
	Hashtbl.iter
		(fun u vs ->
			List.iter
			(fun v ->
				(* Edge (u, v) is a back-edge if start[u] > start[v] and end[u] < end[v] *)
				let start_u = Hashtbl.find start_time_nodes u in
				let end_u   = Hashtbl.find end_time_nodes u in
				let start_v = Hashtbl.find start_time_nodes v in
				let end_v   = Hashtbl.find end_time_nodes v in
				if ((start_u > start_v) && (end_u < end_v)) then
					let name_u = Hashtbl.find lemma_depd_graph.lemma_depd_ids_names u in
					let name_v = Hashtbl.find lemma_depd_graph.lemma_depd_ids_names v in
					raise (Failure (Printf.sprintf "Lemma cyclic dependency detected: %s depends on %s, which depends on %s." name_v name_u name_v))
		    ) vs
		) lemma_depd_graph.lemma_depd_edges
