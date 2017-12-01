open DynArray
open Set
open Stack
open Queue
open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils

exception InvalidTypeOfLiteral

let new_abs_loc_name var = abs_loc_prefix ^ var

let new_lvar_name var = lvar_prefix ^ var

(**
	le -> non - normalised logical expression
	subst -> table mapping variable and logical variable
	gamma -> table mapping logical variables + variables to types

	the store is assumed to contain all the program variables in le
*)
let rec normalise_lexpr ?(store : symbolic_store option) ?(subst : substitution option) 
		(gamma : typing_environment) (le : jsil_logic_expr) =

	let store = Option.default (store_init [] []) store in 
	let subst = Option.default (init_substitution []) subst in 

	let f = normalise_lexpr ~store:store ~subst:subst gamma in
	
	let result = match le with
	| LLit _
	| LNone -> le
	| LVar lvar -> (try Hashtbl.find subst lvar with _ -> LVar lvar)
	| ALoc aloc -> ALoc aloc (* raise (Failure "Unsupported expression during normalization: ALoc") Why not ALoc aloc? *)
	| PVar pvar ->
		(try Hashtbl.find store pvar with
			| _ ->
				(let new_lvar = fresh_lvar () in 
				store_put store pvar (LVar new_lvar); 
				Hashtbl.add subst pvar (LVar new_lvar);
				LVar new_lvar))

	| LBinOp (le1, bop, le2) ->
		let nle1 = f le1 in
		let nle2 = f le2 in
		(match nle1, nle2 with
			| LLit lit1, LLit lit2 ->
				let lit = JSIL_Interpreter.evaluate_binop bop (Literal lit1) (Literal lit2) (Hashtbl.create 1) in
					LLit lit
			| _, _ -> LBinOp (nle1, bop, nle2))

	| LUnOp (uop, le1) ->
		let nle1 = f le1 in
		(match nle1 with
			| LLit lit1 ->
				let lit = JSIL_Interpreter.evaluate_unop uop lit1 in
				LLit lit
			| _ -> LUnOp (uop, nle1))

	| LTypeOf (le1) ->
		let nle1 = f le1 in
		(match nle1 with
			| LLit llit -> LLit (Type (evaluate_type_of llit))
			| LNone -> raise (Failure "Illegal Logic Expression: TypeOf of None")
			| LVar lvar ->
				(try LLit (Type (Hashtbl.find gamma lvar)) with _ -> LTypeOf (LVar lvar))
					(* raise (Failure (Printf.sprintf "Logical variables always have a type, in particular: %s." lvar))) *)
			| ALoc _ -> LLit (Type ObjectType)
			| PVar _ -> raise (Failure "This should never happen: program variable in normalised expression")
			| LBinOp (_, _, _)
			| LUnOp (_, _) -> LTypeOf (nle1)
			| LTypeOf _ -> LLit (Type TypeType)
			| LEList _ -> LLit (Type ListType)
			| LLstNth (list, index) ->
				(match list, index with
					| LLit (LList list), LLit (Num n) when (Utils.is_int n) ->
						let lit_n = (try List.nth list (int_of_float n) with _ ->
							raise (Failure "List index out of bounds")) in
						LLit (Type (evaluate_type_of lit_n))
					| LLit (LList list), LLit (Num n) -> raise (Failure "Non-integer list index")
					| LEList list, LLit (Num n) when (Utils.is_int n) ->
						let le_n = (try List.nth list (int_of_float n) with _ ->
							raise (Failure "List index out of bounds")) in
						f (LTypeOf le_n)
					| LEList list, LLit (Num n) -> raise (Failure "Non-integer list index")
					| _, _ -> LTypeOf (nle1))
			| LStrNth (str, index) ->
				(match str, index with
					| LLit (String s), LLit (Num n) when (Utils.is_int n) ->
						let _ = (try (String.get s (int_of_float n)) with _ ->
							raise (Failure "String index out of bounds")) in
						LLit (Type StringType)
					| LLit (String s), LLit (Num n) -> raise (Failure "Non-integer string index")
					| _, _ -> LTypeOf (nle1)))

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
	params                       : (jsil_var * jsil_type option) list;
	definitions                  : ((string option) * jsil_logic_assertion) list;
	is_recursive                 : bool;
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
				let new_asrts  = List.map (fun (_, a) -> (asrt_substitution subst false a)) pred.definitions in
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
				let pred1_param_names, _ = List.split pred1.params in
				let pred2_param_names, _ = List.split pred2.params in
	  		let subst = init_substitution2 pred2_param_names (List.map (fun var -> PVar var) pred1_param_names) in
		  	let definitions = pred1.definitions @
		  		(List.map (fun (oid, a) -> oid, (asrt_substitution subst true a)) pred2.definitions) in
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
				List.concat (List.map (fun (_, asrt) -> (get_asrt_pred_names asrt)) pred.definitions) in
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

	| LTypeOf le -> LTypeOf (f le) 

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
	| LCList lst        -> LCList lst
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
	| _ -> raise (Failure "DEATH"))



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


let resolve_location (lvar : string) (pfs : jsil_logic_assertion list) : string option =
	
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

	(* print_debug (Printf.sprintf "resolve_location with var %s and pfs:\n%s\n" lvar
		(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion original_pfs))); *)

	let rec loop pfs traversed_pfs =
		(match pfs with
		| [] -> None
		
		| LEq (LVar cur_lvar, ALoc loc) :: rest
		| LEq (ALoc loc, LVar cur_lvar) :: rest  ->
			if (cur_lvar = lvar) then Some loc else loop rest ((List.hd pfs) :: traversed_pfs)

		| LEq (LVar cur_lvar, LLit (Loc loc)) :: rest
		| LEq (LLit (Loc loc), LVar cur_lvar) :: rest ->
			if (cur_lvar = lvar) then Some loc else loop rest ((List.hd pfs) :: traversed_pfs)
		
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
						match loop_lists le1_lst_l le2_lst_l with 
						| None -> loop rest ((List.hd pfs) :: traversed_pfs)
						| Some loc -> Some loc)
				| _ -> loop rest ((List.hd pfs) :: traversed_pfs))
			| _ -> loop rest ((List.hd pfs) :: traversed_pfs))

		| _ :: rest -> loop rest ((List.hd pfs) :: traversed_pfs)) 
	
	and loop_lists lst_1 lst_2 = 
		loop (List.map2 (fun le1 le2 -> LEq (le1, le2)) lst_1 lst_2) [] in

	loop original_pfs [] 


let resolve_location_from_lexpr (pfs : pure_formulae) (le : jsil_logic_expr) : string option = 
	match le with
	| LLit (Loc l)
	| ALoc l        -> Some l
	| LVar x        -> resolve_location x (pfs_to_list pfs) 
	| _             -> None 


(*  -----------------------------------------------------
	Normalise Logic Expressions
	-----------------------------------------------------
	_____________________________________________________
*)
let normalise_logic_expression 
		(store : symbolic_store) (gamma : typing_environment) (subst : substitution)
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
		(store : symbolic_store)
		(gamma : typing_environment)
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
			then (Hashtbl.add store var (ALoc (new_abs_loc_name var)); ())

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
		(store  : symbolic_store)
		(gamma  : typing_environment)
		(subst  : substitution)
		(args   : SS.t option)
		(a      : jsil_logic_assertion) : pure_formulae =

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
				Hashtbl.replace store var le'
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
			(fun var -> if (not (Hashtbl.mem store var)) then (Hashtbl.add store var (LVar (new_lvar_name var)); ()))
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
		(heap : symbolic_heap) (store : symbolic_store)
		(p_formulae : pure_formulae) (gamma : typing_environment)
		(subst : substitution) (a : jsil_logic_assertion) : unit =
	let f = normalise_cell_assertions heap store p_formulae gamma subst in
	let fe = normalise_logic_expression store gamma subst in

	let normalise_cell_assertion (loc : string) (le_f : jsil_logic_expr) (le_v : jsil_logic_expr) : unit = 
		let field_val_pairs, default_val = (try LHeap.find heap loc with _ -> ([], None)) in
		LHeap.replace heap loc (((fe le_f, fe le_v) :: field_val_pairs), default_val) in 

	match a with
	| LStar (a1, a2) -> f a1; f a2

	| LPointsTo (LVar var, le2, le3) -> 
		let aloc = (try
			(match Hashtbl.find subst var with
			| ALoc aloc -> aloc
			| _ -> print_debug_petar ("oopsie!"); raise (Failure (Printf.sprintf "Not an ALoc in subst: %s" (JSIL_Print.string_of_logic_expression (Hashtbl.find store var)))))
			with _ -> raise (Failure (Printf.sprintf "Variable %s not found in subst table: %s!" var (JSIL_Print.string_of_substitution subst)))) in
		normalise_cell_assertion aloc le2 le3

	| LPointsTo (PVar var, le2, le3) ->
		let aloc = (try
			(match Hashtbl.find store var with
			| ALoc aloc -> aloc
			| _ -> raise (Failure (Printf.sprintf "Not an ALoc in subst: %s" (JSIL_Print.string_of_logic_expression (Hashtbl.find subst var)))))
			with _ -> raise (Failure (Printf.sprintf "Variable %s not found in store!" var))) in
		normalise_cell_assertion aloc le2 le3

	| LPointsTo (LLit (Loc loc), le2, le3) -> normalise_cell_assertion loc le2 le3

	| LPointsTo (ALoc loc, le2, le3) -> normalise_cell_assertion loc le2 le3

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
		(store : symbolic_store)
		(gamma : typing_environment)
		(a     : jsil_logic_assertion) : bool =

	let type_check_lexpr (le : jsil_logic_expr) (t : jsil_type) : bool = 
		let le_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
		(match le_type with
			| Some le_type ->
				(if (le_type = t) then true else (
					print_debug (Printf.sprintf "Only vars or lvars in the typing environment. PUTTING: %s with type %s when its type is %s"
								(JSIL_Print.string_of_logic_expression le)
								(JSIL_Print.string_of_type t)
								(JSIL_Print.string_of_type le_type)); 
					false))
			| None ->
				let new_gamma = JSIL_Logic_Utils.reverse_type_lexpr false gamma le t in
				(match new_gamma with
					| None ->
						print_debug (Printf.sprintf "Only vars or lvars in the typing environment. PUTTING: %s with type %s when it CANNOT be typed or reverse-typed"
									(JSIL_Print.string_of_logic_expression le)
									(JSIL_Print.string_of_type t)); 
						false 
					| Some new_gamma ->	extend_gamma gamma new_gamma; true)) in 


	let f = normalise_type_assertions store gamma in
	match a with
	| LTypes type_list ->
		List.fold_left 
			(fun ac (x, t) -> if (not ac) then ac else (
			match x with
				| LLit lit -> (evaluate_type_of lit) = t 

				| LVar x ->
					(* if x is a lvar, we simply add (x, t) to gamma *) 
					Hashtbl.replace gamma x t; true 

				| PVar x -> 
					let le = store_get_safe store x in 
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
						store_put store x (LVar new_lvar);
						weak_update_gamma gamma x (Some t); 
						true)

				| le -> type_check_lexpr le t))
				true
				type_list
	| LStar	(al, ar) -> (f al) && (f ar)
	| _ -> true


(** -----------------------------------------------------
  * Normalise Predicate Assertions
  * (Initialise Predicate Set)
  * -----------------------------------------------------
  * -----------------------------------------------------
**)
let normalise_pred_assertions
	(store : symbolic_store) (gamma : typing_environment)
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

		let fv_list, _ = try LHeap.find heap le_loc_name with Not_found -> [], None in
		LHeap.replace heap le_loc_name (fv_list, Some domain) in

	List.iter add_domain (get_all_empty_fields a)


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
		(pvars : SS.t option)
		(a     : jsil_logic_assertion) : (symbolic_state * substitution) option =

	print_debug (Printf.sprintf "Normalising assertion:\n\t%s" (JSIL_Print.string_of_logic_assertion a));

	let falsePFs pfs =
		match pfs_to_list pfs with
		| [ LFalse ] -> true
		| _          -> false in

	(** Step 1 -- Preprocess list expressions - resolve l-nth(E, i) when possible  *)
	let a = pre_process_list_exprs a in

	(** Step 2 -- Create empty symbolic heap, symbolic store, typing environment, and substitution *)
	let heap  = heap_init () in
	let store = store_init [] [] in
	let gamma = Option.map_default gamma_copy (gamma_init ()) gamma in
	let subst = Option.map_default copy_substitution (init_substitution []) subst in

	(** Step 3 -- Normalise type assertions and pure assertions
	  * 3.1 - type assertions -> initialises gamma
	  * 3.2 - pure assertions -> initialises store and pfs
	  *)
	initialise_alocs store gamma subst a;
	if (not (normalise_type_assertions store gamma a)) then None else (
	let p_formulae = normalise_pure_assertions store gamma subst pvars a in
	if (falsePFs p_formulae) then ( print_debug "Normalising assertion returns None\n"; None ) else (
		(** The pure formulae are not completely bananas  *)

		(** Step 4 -- Add to the store the program variables that are not there yet, BUT
			for which we know the types *)
		extend_typing_env_using_assertion_info gamma ((pfs_to_list p_formulae) @ (asrts_of_store store));

		(** Step 5 -- Normalise cell assertions, pred assertions, and ef assertions
		  * 5.1 - cell assertions -> initialises heap
	      * 5.2 - pred assertions -> initialises pred set
	      * 5.3 - ef assertions   -> fills in the domain for the objects in the heap
		  *)
		normalise_cell_assertions heap store p_formulae gamma subst a;
		let preds, new_assertions = normalise_pred_assertions store gamma subst a in
		extend_typing_env_using_assertion_info gamma new_assertions;
		pfs_merge p_formulae (pfs_of_list new_assertions);
		normalise_ef_assertions heap store p_formulae gamma subst a;

		(** Step 6 -- Check if the symbolic state makes sense *)
		let heap_constraints = get_heap_well_formedness_constraints heap in
		if ((Pure_Entailment.check_satisfiability (heap_constraints @ (pfs_to_list p_formulae)) gamma) &&
				(check_pvar_types store gamma))
			then ( 
				let ret_ss = (heap, store, p_formulae, gamma, preds) in 
				print_debug ( Printf.sprintf "normalise_assertion returning: %s\n and subst: %s\n" 
					(Symbolic_State_Print.string_of_symb_state ret_ss)
					(JSIL_Print.string_of_substitution subst)); 
				Some (ret_ss, subst)
			) else (
				print_debug ( Printf.sprintf "Normalising assertion returns None\n" ); 
				None)))

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
  let heap  : symbolic_heap      = heap_init () in
  let store : symbolic_store     = store_init [] [] in
  let gamma : typing_environment = gamma_init () in
  let pfs   : pure_formulae      = DynArray.make 0 in
  let preds : predicate_set      = DynArray.make 0 in

  (* Step 2 - Map over assertion, populate gamma, store and heap *)
  let populate_state_from_assertion a =
    (match a with
    | LTypes type_assertions ->
      let _ = List.map (fun (e, t) -> Hashtbl.replace gamma (JSIL_Print.string_of_logic_expression e) t) type_assertions in 
      (a, false)
    | LPointsTo (PVar loc, le2, le3)
		| LPointsTo (ALoc loc, le2, le3)
    | LPointsTo (LLit (Loc loc), le2, le3) ->
      (* TODO: prefix locations with _ ? *)
      let field_val_pairs, default_val = (try LHeap.find heap loc with _ -> ([], None)) in
      LHeap.replace heap loc (((le2, le3) :: field_val_pairs), default_val);
      (a, false)
		| LEmptyFields (obj, domain) ->
      let loc = JSIL_Print.string_of_logic_expression obj in
      let field_val_pairs, _ = (try LHeap.find heap loc with _ -> ([], None)) in
      LHeap.replace heap loc ((field_val_pairs), (Some domain));
			(a, false)
			
    | LEq ((PVar v), le)
    | LEq (le, (PVar v)) ->
      Hashtbl.add store v le;
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
  print_debug (Printf.sprintf "Store: %s" (Symbolic_State_Print.string_of_symb_store store));
  print_debug (Printf.sprintf "Gamma: %s" (Symbolic_State_Print.string_of_gamma gamma));
  print_debug (Printf.sprintf "Heap: %s" (Symbolic_State_Print.string_of_symb_heap heap));
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
let create_unification_plan 
		(symb_state      : symbolic_state)
		(reachable_alocs : SS.t) : (jsil_logic_assertion list) =
	let heap, store, pf, gamma, preds = symb_state in 
	
	let heap                    = LHeap.copy heap in 
	let locs_to_visit           = Queue.create () in 
	let unification_plan        = Queue.create () in 
	let marked_alocs            = ref SS.empty in 
	let abs_locs, concrete_locs = List.partition is_abs_loc_name (SS.elements (heap_domain heap)) in 

	let search_for_new_alocs_in_lexpr (le : jsil_logic_expr) : unit = 
		let alocs = get_lexpr_alocs le in 
		SS.iter (fun aloc -> 
			if (not (SS.mem aloc !marked_alocs)) then (
				marked_alocs := SS.add aloc !marked_alocs; 
				Queue.add aloc locs_to_visit; ())) alocs in 

	let inspect_aloc () = 
		if (Queue.is_empty locs_to_visit) then false else (
			let loc     = Queue.pop locs_to_visit in 
			let le_loc  = if (is_abs_loc_name loc) then ALoc loc else LLit (Loc loc) in 
			match heap_get heap loc with 
			| None                      -> 
				(* The aloc does not correspond to any cell - it is an argument for a predicate *)
				true
			| Some (fv_list, le_domain) ->
				let fv_list_c, fv_list_nc = 
					List.partition (fun (le, _) -> 
						match le with 
						| LLit (String _) -> true 
						| _               -> false 
					) fv_list in 
 				List.iter (fun (le_f, le_v) -> 
 					Queue.add (LPointsTo (le_loc, le_f, le_v)) unification_plan; 
 					search_for_new_alocs_in_lexpr le_v
 				) (fv_list_c @ fv_list_nc); 
 				Option.may (fun le_domain -> Queue.add (LEmptyFields (le_loc, le_domain)) unification_plan) le_domain;
 				LHeap.remove heap loc; 
 				true) in 

	(** Step 1 -- add concrete locs and the reachable alocs to locs to visit *)
	List.iter (fun loc -> Queue.add loc locs_to_visit) (concrete_locs @ (SS.elements reachable_alocs)) ; 

	(** Step 2 -- which alocs are directly reachable from the store *)
	Hashtbl.iter (fun x le ->  search_for_new_alocs_in_lexpr le ) store;

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
	if ((LHeap.length heap) = 0) then (
		(* We found all the locations in the symb_state - we are fine! *)
		let unification_plan_lst = Queue.fold (fun ac a -> a :: ac) [] unification_plan in 
		let unification_plan_lst = List.rev unification_plan_lst in 
		Queue.clear unification_plan; 
		unification_plan_lst
	) else (
		let unification_plan_lst = Queue.fold (fun ac a -> a :: ac) [] unification_plan in 
		let unification_plan_lst = List.rev unification_plan_lst in 

		let msg = Printf.sprintf "create_unification_plan FAILURE!\nInspected alocs: %s\nUnification plan:%s\nDisconnected Heap:%s\nOriginal symb_state:%s\n" 
			(String.concat ", " (SS.elements !marked_alocs))
			(Symbolic_State_Print.string_of_unification_plan unification_plan_lst)
			(Symbolic_State_Print.string_of_symb_heap heap)
			(Symbolic_State_Print.string_of_symb_state symb_state) in 
		raise (Failure msg)) 


let is_overlapping_aloc (pfs_list : jsil_logic_assertion list) (aloc : string) : string option =

	let x         = fresh_lvar () in 
	let subst     = init_substitution3 [ (aloc, LVar x) ] in 
	let pfs_list' = List.map (asrt_substitution subst true) pfs_list in 

	print_debug (Printf.sprintf "is_overlapping_aloc with aloc: %s. new_var: %s. pfs:\n%s" aloc x
		(String.concat "; " (List.map JSIL_Print.string_of_logic_assertion pfs_list'))
	);

	let loc       = resolve_location x pfs_list' in	 
	match loc with 
	| Some loc -> print_debug (Printf.sprintf "Found the overlap %s\n" loc); Some loc 
	| _        -> print_debug "Could NOT find the overlap\n"; None 


let collapse_alocs (ss_pre : symbolic_state) (ss_post : symbolic_state) : symbolic_state = 
	let pfs_pre  = (ss_pfs ss_pre) in 
	let pfs_post = (ss_pfs ss_post) in 
	let pfs_list = (pfs_to_list pfs_pre) @ (pfs_to_list pfs_post) in 
	let pfs      = (pfs_of_list pfs_list) in 

	if (Pure_Entailment.check_satisfiability pfs_list (ss_gamma ss_post)) then ss_post else (
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
			| None       -> () 
			| Some aloc' -> Hashtbl.replace aloc_subst aloc (ALoc aloc'); ()
		) relevant_new_alocs; 

		let new_pfs_post = pfs_substitution aloc_subst true pfs_post in 
		let new_pfs_list = (pfs_to_list pfs_pre) @ (pfs_to_list new_pfs_post) in 

		if (Pure_Entailment.check_satisfiability new_pfs_list (ss_gamma ss_post)) then (
			ss_substitution aloc_subst true ss_post 
		) else (
			print_normal(Printf.sprintf "I am dying here. new_pfs_list: %s\ngamma: %s\n" 
				(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion new_pfs_list))
				(Symbolic_State_Print.string_of_gamma (ss_gamma ss_post))); 
			raise (Failure "collapse_alocs FAILED!")
		)
	)



(** Normalise Postcondition
	-----------------------
	Each normlised postcondition postcondition may map additional spec vars
	to alocs. In order not to lose the link between the newly generated alocs
	and the precondition spec vars, we need to introduce extra equalities    *)
let normalise_post
		(post_gamma_0  : typing_environment)
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
		ss_extend_pfs ss_post (pfs_of_list extra_post_pfs);
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
		let post_gamma_0' = filter_gamma_f post_gamma_0 (fun x -> SS.mem x spec_vars) in

		(** Step 3 - Normalise the postconditions associated with each pre           *)
		let ss_posts = oget_list (List.map (normalise_post post_gamma_0' subst spec_vars params) posts) in
		let ss_posts = List.map (fun ss_post -> collapse_alocs ss_pre ss_post) ss_posts in 
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
    let proc_tbl_rng = get_tbl_rng prog in
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
			proc_body   = Array.make 0 (empty_metadata, SBasic SSkip);
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
	(gamma     : typing_environment)
	(spec_vars : SS.t)
	(subst     : substitution)
	(params    : SS.t) : symbolic_state = 
	let gamma_inv = filter_gamma_f gamma (fun x -> SS.mem x spec_vars) in
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
