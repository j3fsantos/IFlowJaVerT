open DynArray
open Set
open Stack
open JSIL_Syntax

(****************************************************************)
(****************************************************************)
(** JSIL Literals and Expressions - Generic AST functions      **)
(****************************************************************)
(****************************************************************)

let rec literal_fold 
	(f_ac    : jsil_lit -> 'b -> 'b -> 'a list -> 'a) 
	(f_state : (jsil_lit -> 'b -> 'b) option)
	(state   : 'b) 
	(lit     : jsil_lit) : 'a =

	let new_state = (Option.default (fun le x -> x) f_state) lit state in
	let fold_lit  = literal_fold f_ac f_state new_state in
	let f_ac      = f_ac lit new_state state in

  	match lit with
  	| Undefined  | Null   | Empty    | Constant _ 
  		| Bool _ | Num _  | String _ | Char _ 
  		| Loc _  | Type _ -> f_ac [] 
  	| LList lits | CList lits -> f_ac (List.map fold_lit lits)

(****************************************************************)
(****************************************************************)
(** Logical Expressions and Assertions - Generic AST functions **)
(****************************************************************)
(****************************************************************)

(** Apply function f to a logic expression, recursively when f returns (new_expr, true). *)
let rec logic_expression_map 
	(f_before : jsil_logic_expr  -> jsil_logic_expr * bool) 
	(f_after  : (jsil_logic_expr -> jsil_logic_expr) option)
	(lexpr    : jsil_logic_expr) : jsil_logic_expr =
	(* Apply the mapping *)
	let map_e   = logic_expression_map f_before f_after in
	let f_after = Option.default (fun x -> x) f_after in 
	
	let (mapped_lexpr, recurse) = f_before lexpr in
	if not recurse then
		mapped_lexpr
	else ( 
  	(* Map recursively to expressions *)
  		let mapped_lexpr = 
  			match mapped_lexpr with
  			| LLit _ | LNone | LVar _ | ALoc _ | PVar _ -> mapped_lexpr
  			| LBinOp (e1, op, e2) -> LBinOp (map_e e1, op, map_e e2)
  			| LUnOp (op, e)       -> LUnOp (op, map_e e)
  			| LTypeOf e           -> LTypeOf (map_e e)
  			| LEList le           -> LEList (List.map map_e le)
  			| LCList le           -> LCList (List.map map_e le)
			| LESet le            -> LESet  (List.map map_e le)
			| LSetUnion le        -> LSetUnion  (List.map map_e le)
			| LSetInter le        -> LSetInter  (List.map map_e le)
  			| LLstNth (e1, e2)    -> LLstNth (map_e e1, map_e e2)
  			| LStrNth (e1, e2)    -> LStrNth (map_e e1, map_e e2) in 
  		f_after mapped_lexpr)

(** Apply function f to the logic expressions in an assertion, recursively when f_a returns (new_asrt, true). *)
let rec assertion_map
    (f_a_before  : (jsil_logic_assertion -> jsil_logic_assertion * bool) option)
    (f_a_after   : (jsil_logic_assertion -> jsil_logic_assertion) option)
    (f_e         : (jsil_logic_expr -> jsil_logic_expr) option)
    (a           : jsil_logic_assertion) : jsil_logic_assertion =

	(* Map recursively to assertions and expressions *)
	let map_a      = assertion_map f_a_before f_a_after f_e in
  	let map_e      = Option.default (fun x -> x) f_e in
  	let f_a_before = Option.default (fun x -> x, true) f_a_before in 
  	let f_a_after  = Option.default (fun x -> x) f_a_after in 
	let (a', recurse) = f_a_before a in 

  	if not recurse then a' else ( 
  		let a'' =
  			match a' with
  			| LAnd (a1, a2)          -> LAnd (map_a a1, map_a a2)
  			| LOr (a1, a2)           -> LOr (map_a a1, map_a a2)
  			| LNot a                 -> LNot (map_a a)
  			| LTrue                  -> LTrue
  			| LFalse                 -> LFalse
  			| LEq (e1, e2)           -> LEq (map_e e1, map_e e2)
  			| LLess (e1, e2)         -> LLess (map_e e1, map_e e2)
  			| LLessEq (e1, e2)       -> LLessEq (map_e e1, map_e e2)
  			| LStrLess (e1, e2)      -> LStrLess (map_e e1, map_e e2)
  			| LStar (a1, a2)         -> LStar (map_a a1, map_a a2)
  			| LPointsTo (e1, e2, e3) -> LPointsTo (map_e e1, map_e e2, map_e e3)
  			| LEmp                   -> LEmp
  			| LPred (s, le)          -> LPred (s, List.map map_e le)
  			| LTypes lt              -> LTypes (List.map (fun (exp, typ) -> (map_e exp, typ)) lt)
  			| LEmptyFields (o, ls)   -> LEmptyFields (map_e o, map_e ls)
  			| LSetMem (e1, e2)       -> LSetMem (map_e e1, map_e e2)
  			| LSetSub (e1, e2)       -> LSetSub (map_e e1, map_e e2)
  			| LForAll (bt, a)        -> LForAll (bt, map_a a) in
  		f_a_after a''
  	)

let rec logic_expression_fold 
	(f_ac    : jsil_logic_expr -> 'b -> 'b -> 'a list -> 'a) 
	(f_state : (jsil_logic_expr -> 'b -> 'b) option)
	(state   : 'b) 
	(lexpr   : jsil_logic_expr) : 'a =

	let new_state = (Option.default (fun le x -> x) f_state) lexpr state in
	let fold_e    = logic_expression_fold f_ac f_state new_state in
	let f_ac      = f_ac lexpr new_state state in

  	match lexpr with
  	| LLit _ | LNone | LVar _ | ALoc _ | PVar _ -> f_ac []
  	| LBinOp (e1, op, e2)   -> f_ac [ (fold_e e1); (fold_e e2) ]
  	| LUnOp (op, e)         -> f_ac [ (fold_e e) ]
  	| LTypeOf e             -> f_ac [ (fold_e e) ]
  	| LEList les            -> f_ac (List.map fold_e les)
  	| LLstNth (e1, e2)      -> f_ac [ (fold_e e1); (fold_e e2) ]
  	| LStrNth (e1, e2)      -> f_ac [ (fold_e e1); (fold_e e2) ]
  	| LESet les
  	| LSetUnion les
  	| LSetInter les         -> f_ac (List.map fold_e les)


let rec assertion_fold 
	(feo      : (jsil_logic_expr -> 'a) option) 
	(f_ac     : jsil_logic_assertion -> 'b -> 'b -> 'a list -> 'a)
	(f_state  : (jsil_logic_assertion -> 'b -> 'b) option) 
	(state    : 'b)
	(asrt     : jsil_logic_assertion) : 'a =
	
	let new_state = (Option.default (fun a x -> x) f_state) asrt state in
	let fold_a    = assertion_fold feo f_ac f_state new_state in
	let f_ac      = f_ac asrt new_state state in
	let fes les   = Option.map_default (fun fe -> List.map fe les) [] feo in

	match asrt with
	| LTrue | LFalse | LEmp -> f_ac []

	| LEq (le1, le2) | LLess (le1, le2) | LLessEq (le1, le2)
		| LStrLess (le1, le2) |  LSetMem (le1, le2)
		| LSetSub (le1, le2)  | LEmptyFields (le1, le2) -> f_ac (fes [ le1; le2 ])

	| LPointsTo (le1, le2, le3) -> f_ac (fes [ le1; le2; le3 ])

	| LPred (_, les) -> f_ac (fes les)

	| LAnd (a1, a2)             -> f_ac [ (fold_a a1); (fold_a a2) ]
	| LOr (a1, a2)              -> f_ac [ (fold_a a1); (fold_a a2) ]
	| LStar (a1, a2)            -> f_ac [ (fold_a a1); (fold_a a2) ]
	| LNot a                    -> f_ac [ (fold_a a) ]
	| LForAll (_, a)            -> f_ac [ (fold_a a) ]

	| LTypes vts -> 
		let les, _ = List.split vts in 
		f_ac (fes les) 


(***************************************************************)
(***************************************************************)
(** Simple Filters - to get subexpressions of a certain form  **)
(***************************************************************)
(***************************************************************)

(* Returns all the non-list literals that occur in --le-- *)
let get_lexpr_non_list_lits (le : jsil_logic_expr) : jsil_lit list =
	let fe_ac le _ _ ac = match le with
		| LLit lit -> lit :: (List.concat ac)
		| _      -> List.concat ac in 

	let flit_ac lit _ _ ac = match lit with 
		| LList lst -> List.concat ac 
		| _        -> [ lit ] in 

	let lits : jsil_lit list = logic_expression_fold fe_ac None None le in
	List.concat (List.map (literal_fold flit_ac None None) lits) 

(* Returns all the non-list listerals that occur in --a-- *)
let get_asrt_non_list_lits (a : jsil_logic_assertion) : jsil_lit list =	
	let f_ac a _ _ ac = List.concat ac in
	assertion_fold (Some get_lexpr_non_list_lits) f_ac None None a


(* Get all the sub-expressions of --le-- of the form (LLit (LList lst)) and (LEList lst)  *)
let get_lexpr_lists (le : jsil_logic_expr) : jsil_logic_expr list =
	let fe_ac le _ _ ac =
		match le with
		| LLit (LList ls) -> [ (LEList (List.map (fun x -> LLit x) ls)) ]
		| LEList les      -> (LEList les) :: (List.concat ac)
		| _               -> List.concat ac in 
	logic_expression_fold fe_ac None None le 

(* Get all the logical expressions of --a-- of the form (LLit (LList lst)) and (LEList lst)  *)
let get_asrt_lists (a : jsil_logic_assertion) : jsil_logic_expr list =
	let f_ac a _ _ ac = List.concat ac in 
	assertion_fold (Some get_lexpr_lists) f_ac None None a

(* Get all the logical expressions of --a-- that denote a list 
   and are not logical variables *)
let get_asrt_list_lexprs (a : jsil_logic_assertion) : jsil_logic_expr list =

	let fe_ac le _ _ ac =
		match le with
		| LLit (LList _) | LEList _   | LBinOp (_, LstCons, _)
		| LBinOp (_, LstCat, _) | LUnOp (Car, _) | LUnOp (Cdr, _)
		| LUnOp (LstLen, _) -> le :: (List.concat ac)
		| _ -> List.concat ac in

	let fe = logic_expression_fold fe_ac None None in
	let f_ac a _ _ ac = List.concat ac in
	assertion_fold (Some fe) f_ac None None a


(* Get all the literal numbers and string occurring in --a-- *)
let get_asrt_strings_and_numbers (a : jsil_logic_assertion) : (string list) * (float list) =
	let lits    = get_asrt_non_list_lits a in
	List.fold_left (fun (strings, numbers) lit -> 
		match lit with 
		| Num n    -> (strings, n :: numbers)
		| String s -> (s :: strings, numbers)
		| _        ->  (strings, numbers)
	) ([], []) lits


(* Get all the logical variables in --le-- *)
let get_lexpr_lvars (le : jsil_logic_expr) : SS.t =
	let fe_ac le _ _ ac = match le with
		| LVar x -> [ x ]
		| _      -> List.concat ac in 
	SS.of_list (logic_expression_fold fe_ac None None le)

(* Get all the logical variables in a list of logical expressions *)
let get_lexpr_list_lvars (les : jsil_logic_expr list) : SS.t = 
	SS.of_list (List.concat (List.map SS.elements (List.map get_lexpr_lvars les)))

(* Get all the logical variables in --a-- *)
let get_asrt_lvars (a : jsil_logic_assertion) : SS.t =
	let fe_ac le _ _ ac = match le with
		| LVar x -> [ x ]
		| _      -> List.concat ac in 
	let fe = logic_expression_fold fe_ac None None in 
	let f_ac a _ _ ac = match a with 
		| LForAll (bt, a1) -> 
			(* Quantified variables need to be excluded *)
			let binders, _  = List.split bt in
			let ac_vars     = SS.of_list (List.concat ac) in 
			let binder_vars = SS.of_list binders in 
			SS.elements (SS.diff ac_vars binder_vars)
		| _ -> List.concat ac in
 	SS.of_list (assertion_fold (Some fe) f_ac None None a)


(* Get all the program variables in --le-- *)
let get_lexpr_pvars (le : jsil_logic_expr) : SS.t =
	let fe_ac le _ _ ac = match le with
		| PVar x -> [ x ]
		| _      -> List.concat ac in 
	SS.of_list (logic_expression_fold fe_ac None None le)

(* Get all the program variables in --a-- *)
let get_asrt_pvars (a : jsil_logic_assertion) : SS.t =
	let fe_ac le _ _ ac = match le with
		| PVar x -> [ x ]
		| _      -> List.concat ac in 
	let fe = logic_expression_fold fe_ac None None in 
	let f_ac a _ _ ac = List.concat ac in
 	SS.of_list (assertion_fold (Some fe) f_ac None None a)


(* Get all the abstract locations in --le-- *)
let rec get_lexpr_alocs (le : jsil_logic_expr) : SS.t =
	let fe_ac le _ _ ac =
		match le with
		| ALoc l -> l :: (List.concat ac)
		| _ -> List.concat ac in
	SS.of_list (logic_expression_fold fe_ac None None le)

(* Get all the abstract locations in --a-- *)
let rec get_asrt_alocs (a : jsil_logic_assertion) : SS.t =
	let fe_ac le _ _ ac =
		match le with
		| ALoc l -> l :: (List.concat ac)
		| _ -> List.concat ac in
	let fe = logic_expression_fold fe_ac None None in 
	let f_ac a _ _ ac = List.concat ac in
 	SS.of_list (assertion_fold (Some fe) f_ac None None a)


(* Get all the abstract locations in --a-- *)
let rec get_asrt_types (a : jsil_logic_assertion) : (jsil_logic_expr * jsil_type) list =
	let f_ac a _ _ ac =  match a with 
		| LTypes vts -> vts @ (List.concat ac)
		| _          -> (List.concat ac) in 
	assertion_fold None f_ac None None a


(* Returns a list with the names of the predicates that occur in --a-- *)
let get_asrt_pred_names (a : jsil_logic_assertion) : string list =
	let f_ac a _ _ ac =
		(match a with
		| LPred (s, _) -> s :: (List.concat ac)
		| _            -> List.concat ac) in
	assertion_fold None f_ac None None a


(***************************************************************)
(***************************************************************)
(** Pure Assertions                                           **)
(***************************************************************)
(***************************************************************)

(* Check if --a-- is a pure assertion *)
let is_pure_asrt (a : jsil_logic_assertion) : bool =
	let f_ac a _ _ ac =
		match a with
		| LPred _ | LPointsTo _ | LEmp | LEmptyFields _ -> false
		| _  -> not (List.exists (fun b -> not b) ac) in
	assertion_fold None f_ac None None a

(* Check if --a-- is a pure assertion & non-recursive assertion. 
   It assumes that only pure assertions are universally quantified *)
let is_pure_non_rec_asrt (a : jsil_logic_assertion) : bool =
	match a with
	| LTrue | LFalse | LEq (_, _) | LLess (_, _) | LLessEq (_, _) | LStrLess (_, _)
	| LSetMem (_, _) | LSetSub (_, _) | LForAll (_, _) -> true
	| _ -> false


(* Check if --a-- only contains pure & non-recursive assertions negated *)
let is_devoid_of_spatial_negations (a : jsil_logic_assertion) : bool =
	let f_ac a _ _ ac =
		match a with
		| LNot a -> is_pure_non_rec_asrt a
		| _      -> not (List.exists (fun b -> not b) ac) in
	assertion_fold None f_ac None None a


(* Eliminate LStar and LTypes assertions. 
   LTypes disappears. LStar is replaced by LAnd. 
   This function expects its argument to be a PURE assertion. *)
let make_pure (a : jsil_logic_assertion) : jsil_logic_assertion =
	let f_a_after a = 
		let ret = 
			(match a with 
			| LAnd (LTypes _, a) | LAnd (a, LTypes _)   -> a 
			| LOr (LTypes _, _) | LOr (_, LTypes _)     -> raise (Failure "Unsupported assertion")
			| LStar (LTypes _, a) | LStar (a, LTypes _) -> a 
			| LStar (a1, a2)                            -> LAnd (a1, a2)
			| LNot (LTypes _)                           -> raise (Failure "Unsupported assertion")
			| LPointsTo _ | LEmp | LEmptyFields _       -> raise (Failure "DEATH. make_pure with impure argument")
			| _                                         -> a) in 
		(match ret with 
		| LTypes _ -> LTrue 
		| _        -> ret) in 
	assertion_map None (Some f_a_after) None a 


let rec push_in_negations_off (a : jsil_logic_assertion) : jsil_logic_assertion =
	let f_off   = push_in_negations_off in
	let f_on    = push_in_negations_on in
	(match a with
	| LAnd (a1, a2)  -> LAnd ((f_off a1), (f_off a2))
	| LOr (a1, a2)   -> LOr ((f_off a1), (f_off a2))
	| LNot a1        ->
		let new_a1   = make_pure a1 in
		let types_a1 = get_asrt_types a1 in 
		if ((List.length types_a1) > 0) then LStar (f_on (new_a1), LTypes types_a1) else f_on new_a1
	| LStar (a1, a2) -> LStar ((f_off a1), (f_off a2))
	| LForAll (bt, a) -> LForAll (bt, f_off a)
	| _ -> a)
and push_in_negations_on (a : jsil_logic_assertion) : jsil_logic_assertion =
	let f_off   = push_in_negations_off in
	let f_on    = push_in_negations_on in
	(match a with
	| LAnd (a1, a2)       -> LOr ((f_on a1), (f_on a2))
	| LOr (a1, a2)        -> LAnd ((f_on a1), (f_on a2))
	| LTrue               -> LFalse
	| LFalse              -> LTrue
	| LNot a              -> (f_off a)
	| LEq _         | LLess _   | LLessEq _ | LStrLess _ 
		| LPred _ 	| LSetMem _ | LSetSub _ | LForAll _  
		| LSetMem _ | LSetSub _ -> LNot a
	| LStar _ | LEmp | LPointsTo _ 
		| LEmptyFields _ | LTypes _ ->  raise (Failure "Unsupported assertion"))

(* Rewrites --a-- in such a way that only non-recursive pure assertions are negated *)
let push_in_negations (a : jsil_logic_assertion) : jsil_logic_assertion =
	(match (is_devoid_of_spatial_negations a) with
	| true -> a
	| false -> push_in_negations_off a)


(***************************************************************)
(***************************************************************)
(** Substitutions                                             **)
(***************************************************************)
(***************************************************************)

let lexpr_substitution (subst : substitution) (partial : bool) (le : jsil_logic_expr) : jsil_logic_expr = 

	let find_in_subst (x : string) (le_x_old : jsil_logic_expr) 
			(make_new_x : unit -> jsil_logic_expr) : jsil_logic_expr = 
		try Hashtbl.find subst x with _ -> 
			if partial then le_x_old else (
				let new_le_x = make_new_x () in 
				Hashtbl.replace subst x new_le_x;
				new_le_x) in  

	let f_before le = match le with 
		| LVar x    -> find_in_subst x le (fun () -> LVar (fresh_lvar ())), false 
		| ALoc x    -> find_in_subst x le (fun () -> ALoc (fresh_aloc ())), false
		| PVar x    -> find_in_subst x le (fun () -> PVar (fresh_pvar ())), false 
		| _         -> le, true in 

	logic_expression_map f_before None le 		

let asrt_substitution (subst : substitution) (partial : bool) (a : jsil_logic_assertion) : jsil_logic_assertion = 
	let old_binders_substs : substitution_list ref = ref [] in 
	let f_before a = match a with 
		| LForAll (bt, _) -> 
			let binders, _     = List.split bt in
			let binders_substs = List.map (fun x -> try Some (x, Hashtbl.find subst x) with _ -> None) binders in 
			let binders_substs = try List.map Option.get (List.filter (fun x -> not (x = None)) binders_substs) 
				with _ -> raise (Failure "DEATH. asrt_substitution") in 
			old_binders_substs := binders_substs; 
			List.iter (fun x -> Hashtbl.replace subst x (LVar x)) binders;
			a, true 
		| _ -> a, true in 
	let f_after a = match a with 
		| LForAll _ -> List.iter (fun (x, le_x) -> Hashtbl.replace subst x le_x) !old_binders_substs; a 
		| _ -> a in 
	assertion_map (Some f_before) (Some f_after) (Some (lexpr_substitution subst partial)) a


(** Returns the set containing all the variable names in the domain of --subst-- 
    except those filtered out by --filter_out-- *)
let get_subst_vars (filter_out : string -> bool) (subst : substitution) : SS.t =
	(Hashtbl.fold
		(fun x le vars ->
			if (filter_out x)
				then vars
				else SS.add x vars)
		subst
		SS.empty)

(** Returns the projection of --subst-- onto the elements x of its domain 
    such that filter(x, subst(x)) = true *)
let filter_substitution (filter : string -> jsil_logic_expr -> bool) (subst : substitution) : substitution  =
	let new_subst = Hashtbl.copy subst in
	Hashtbl.filter_map_inplace (fun v le ->
		match (filter v le) with
		| true -> Some le
		| false -> None) new_subst;
	new_subst

(** Returns the projection of --subst-- onto the elements x of its domain 
    such that filter(x) = true *)
let filter_substitution_dom (filter : string -> bool) (subst : substitution) : substitution  =
	filter_substitution (fun x _ -> filter x) subst 

(** Returns the projection of --subst-- onto the elements x of its domain 
    such that x \in vars *)
let filter_substitution_set (vars : SS.t) (subst : substitution) : substitution =
	filter_substitution (fun x _ -> SS.mem x vars) subst 


(** Computes a substitution subst such that: subst(x) = subst1(subst2(x)) *)
let compose_partial_substitutions (subst1 : substitution) (subst2 : substitution) : substitution =
	let subst = Hashtbl.create small_tbl_size in
	Hashtbl.iter (fun x le -> Hashtbl.add subst x (lexpr_substitution subst1 true le)) subst2;
	subst

(** Serialises --subst-- as a list of assertions *)
let substitution_to_list (subst : substitution) : jsil_logic_assertion list =
	Hashtbl.fold
		(fun x le asrts -> if (is_lvar_name x) then ((LEq (LVar x, le)) :: asrts) else asrts)
		subst
		[]


(***************************************************************)
(***************************************************************)
(** Logic Commmands                                           **)
(***************************************************************)
(***************************************************************)

(* Map over the logic commands
	*)
let rec logic_command_map
	(f_l : (jsil_logic_command -> jsil_logic_command))
	(lcmd : jsil_logic_command) : jsil_logic_command =

	(* Functions to map over assertions and expressions *)
	let map_l                = logic_command_map f_l in
	match f_l lcmd with
	| LogicIf (le, lcmds_then, lcmds_else) -> LogicIf (le, (List.map map_l lcmds_then), (List.map map_l lcmds_else))
	| l_cmd -> l_cmd


(***************************************************************)
(***************************************************************)
(** JSIL Types                                                **)
(***************************************************************)
(***************************************************************)

let if_some (a : 'a option) (f : 'a -> 'b) (default : 'b) =
	match a with
	| Some x -> f x
	| None -> default

let if_some_val (a : 'a option) (default : 'a) =
match a with
	| Some x -> x
	| None -> default

let if_some_val_lazy (a : 'a option) (default : ('a lazy_t)) =
match a with
	| Some x -> x
	| None -> Lazy.force default


let rec type_lexpr gamma le =

	let f = type_lexpr gamma in
	let result = (match le with
	(* Literals are always typable *)
  	| LLit lit -> (Some (evaluate_type_of lit), true, [])

	(* Variables are typable if in gamma, otherwise no no *)
	| LVar var
	| PVar var ->
		(match gamma_get_type gamma var with
		| Some t -> Some t, true, []
		| None   -> None,   true, [])

	(* Abstract locations are always typable, by construction *)
	| ALoc _ -> Some ObjectType, true, []

  	(* If what we're trying to type is typable, we should get a type back.*)
	| LTypeOf le ->
		let tle, itle, constraints = f le in
		if (itle) then (Some TypeType, true, constraints) else (None, false, [])

  	(* LEList *)
	| LEList les ->
		let all_typable, constraints =
			(List.fold_left
				(fun (ac, ac_constraints) elem ->
					let (_, ite, constraints) = f elem in
						((ac && ite), (constraints @ ac_constraints)))
				(true, [])
				les) in
			if (all_typable) then (Some ListType, true, constraints) else (None, false, [])
	| LESet les ->
	let all_typable, constraints =
		(List.fold_left
			(fun (ac, ac_constraints) elem ->
				let (_, ite, constraints) = f elem in
					((ac && ite), (constraints @ ac_constraints)))
			(true, [])
			les) in
		if (all_typable) then (Some SetType, true, constraints) else (None, false, [])
	(* LCList *)
	| LCList les ->
		let all_typable, constraints =
			(List.fold_left
				(fun (ac, ac_constraints) elem ->
					let (_, ite, constraints) = f elem in
						((ac && ite), (constraints @ ac_constraints)))
				(true, [])
				les) in
			if (all_typable) then (Some StringType, true, constraints) else (None, false, [])

 	| LUnOp (unop, e) ->
		let (te, ite, constraints) = f e in
		(* Printf.printf "trying to type a not. got the following. te: %s. ite: %s."
			(match te with
  					| Some te -> JSIL_Print.string_of_type te
  					| None    -> "")
			(string_of_bool ite); *)
		let tt t1 t2 new_constraints =
			if_some te
				(fun t -> if (t = t1)
					then (Some t2, true, (new_constraints @ constraints))
					else (None, false, []))
				(None, false, []) in
		if (ite) then
  		(match unop with
			(* Boolean to Boolean  *)
  		| Not ->
  			(
  				(match te with
  					| Some te -> JSIL_Print.string_of_type te
  					| None    -> "");
  			tt BooleanType BooleanType [])
			(* Number to Number    *)
  		| UnaryMinus	| BitwiseNot	| M_sgn			| M_abs	| M_acos
 	    | M_asin			| M_atan			| M_ceil		| M_cos	| M_exp
      	| M_floor			| M_log				| M_round		| M_sin	| M_sqrt
		| M_tan  -> tt NumberType NumberType []
			(* Number to Int       *)
  		| ToIntOp			| ToUint16Op	| ToInt32Op	| ToUint32Op -> tt NumberType NumberType []
  		(* Number to String    *)
		| ToStringOp -> tt NumberType StringType []
			(* String to Number    *)
		| ToNumberOp -> tt StringType NumberType []
			(* Anything to Boolean *)
		| IsPrimitive -> (Some BooleanType, true, constraints)
			(* List to List -> generates constraint *)
		| Cdr ->
			let new_constraint = (LNot (LLess (LUnOp (LstLen, e), (LLit (Num 1.))))) in
			tt ListType ListType [ new_constraint ]
			(* List to Anything -> generates constraint *)
		| Car ->
				let new_constraint = (LNot (LLess (LUnOp (LstLen, e), (LLit (Num 1.))))) in
				(match te with
				| Some ListType -> (None, true, [ new_constraint ])
				| None          -> (None, false, [] ))
			(* List to Int         *)
		| LstLen -> tt ListType NumberType []
			(* String to Int       *)
			| StrLen -> tt StringType NumberType [])
		else
			(None, false, [])

	| LBinOp (e1, op, e2) ->
		let (te1, ite1, constraints1) = f e1 in
		let (te2, ite2, constraints2) = f e2 in
		let constraints = constraints1 @ constraints2 in

		let all_types = [ UndefinedType; NullType; EmptyType; BooleanType; NumberType; StringType; ObjectType; ListType; TypeType; NoneType; SetType ] in
		let check_valid_type t types ret_type new_constraints =
			let is_t_in_types = List.mem t types in
			if (is_t_in_types)
				then (Some ret_type, true, (new_constraints @ constraints))
				else (None, false, []) in

		(match te1, te2 with
		| (Some t1), (Some t2) ->
			let teq = (t1 = t2) in
			(match teq with
			| false ->
				(match op with
				| Equal -> (Some BooleanType, true, constraints)
				| LstCons -> check_valid_type t2 [ ListType ] ListType []
				| SetMem -> check_valid_type t2 [ SetType ] BooleanType []
				| _     -> Printf.printf "type_lexpr: op: %s, t: none\n"  (JSIL_Print.string_of_binop op); raise (Failure "ERROR"))
			| true ->
			(match op with
			| Equal ->
				(
					Printf.printf "typing the jsil equality. t1: %s. t2: %s.\n"
						(JSIL_Print.string_of_type t1) (JSIL_Print.string_of_type t2);
					check_valid_type t1 all_types BooleanType []
				)
			| LessThan | LessThanEqual -> check_valid_type t1 [ NumberType ] BooleanType []
			| LessThanString -> check_valid_type t1 [ StringType ] BooleanType []
			| Plus	| Minus	| Times	| Mod -> check_valid_type t1 [ NumberType ] t1 []
			| Div -> check_valid_type t1 [ NumberType ] NumberType []
			| And	| Or -> check_valid_type t1 [ BooleanType ] BooleanType []
			| BitwiseAnd	| BitwiseOr	| BitwiseXor	| LeftShift	| SignedRightShift
			| UnsignedRightShift	| M_atan2 -> check_valid_type t1 [ NumberType ] NumberType []
			| M_pow -> check_valid_type t1 [ NumberType ] t1 []
			| LstCons -> check_valid_type t2 [ ListType ] ListType []
			| LstCat -> check_valid_type t1 [ ListType ] ListType []
			| StrCat -> check_valid_type t1 [ StringType ] StringType []
			| SetDiff -> check_valid_type t1 [ SetType ] SetType     []
			| SetSub   -> check_valid_type t1 [ SetType ] BooleanType []
			| _ ->
				Printf.printf "type_lexpr: op: %s, t: %s\n"  (JSIL_Print.string_of_binop op) (JSIL_Print.string_of_type t1);
				raise (Failure "ERROR in type_lexpr")))
		| _, ot2 ->
			match op with
			| Equal when ite1 && ite2 -> (Some BooleanType, true, constraints)
			| LstCons when ite2 ->
				(match ot2 with
				| None -> (None, false, [])
				| Some t2 -> check_valid_type t2 [ ListType ] ListType [])
			| _ -> (None, false, []))

	| LLstNth (lst, index) ->
		let type_lst, _, constraints1 = f lst in
		let type_index, _, constraints2 = f index in
		(match (type_lst, type_index) with
		| Some ListType, Some NumberType ->
			let new_constraint1 = (LNot (LLess (index, LLit (Num 0.)))) in
			let new_constraint2 = (LLess (index, LUnOp (LstLen, lst))) in
			(None, true, (new_constraint1 :: (new_constraint2 :: constraints1 @ constraints2)))
		| _, _ -> (None, false, []))

	| LStrNth (str, index) ->
		let type_str, _, constraints1 = f str in
		let type_index, _, constraints2 = f index in
		(match (type_str, type_index) with
		| Some StringType, Some NumberType ->
			let new_constraint1 = (LNot (LLess (index, LLit (Num 0.)))) in
			let new_constraint2 = (LLess (index, LUnOp (StrLen, str))) in
			(* Printf.printf "Entailment: %b\n" entail; *)
			(Some StringType, true, (new_constraint1 :: (new_constraint2 :: constraints1 @ constraints2)))
		| _, _ -> (None, false, []))

  | LSetUnion le
	| LSetInter le ->
			let result = try (
				let constraints = List.fold_left
				(fun ac e ->
					let (te, ite, constraints_e) = f e in
					(match te with
					| Some SetType -> SA.union ac (SA.of_list constraints_e)
					| _ -> raise (Failure "Oopsie!"))
				) SA.empty le in
				(Some SetType, true, (SA.elements constraints))) with | _ -> (None, false, []) in
			result

	| LNone    -> (Some NoneType, true, [])) in

	let (tp, b, _) = result in

	result


let rec reverse_type_lexpr_aux gamma new_gamma le le_type =
	let f = reverse_type_lexpr_aux gamma new_gamma in
	(* Printf.printf "le: %s\n\n\n" (JSIL_Print.string_of_logic_expression le false); *)
	(match le with
	(* Literals are always typable *)
	| LLit lit -> (evaluate_type_of lit = le_type)

	(* Variables are reverse-typable if they are already typable *)
	(* with the target type or if they are not typable           *)
	| LVar var
	| PVar var ->
		(match (gamma_get_type gamma var), (gamma_get_type new_gamma var) with
		| Some t, None
		| None, Some t     -> (t = le_type)
		| None, None       -> (update_gamma new_gamma var (Some le_type)); true
		| Some t1, Some t2 -> if (t1 = t2) then true else false)

	(* Abstract locations are reverse-typable if the target type is ObjectType *)
	| ALoc _ -> if (le_type = ObjectType) then true else false

  	(* LEList and LESet are not reverse typable because we lose type information *)
	| LEList _
	| LESet  _ -> false

  	| LSetUnion les
	| LSetInter les ->
		if (le_type = SetType)
			then (List.fold_left (fun ac x -> ac && (f x SetType)) true les)
			else false

	| LUnOp (unop, le) ->
		(* Printf.printf "UNOP\n\n\n"; *)
		(match unop with
		| Not        -> if (le_type = BooleanType) then f le BooleanType else false
		| UnaryMinus -> if (le_type = NumberType)  then f le le_type     else false
		| BitwiseNot	| M_sgn	| M_abs		| M_acos	| M_asin	| M_atan	| M_ceil
		| M_cos				| M_exp	| M_floor	| M_log		| M_round	| M_sin		| M_sqrt
		| M_tan      -> if (le_type = NumberType) then f le le_type else false
		| ToIntOp			| ToUint16Op			| ToInt32Op					| ToUint32Op
								 ->	if (le_type = NumberType) then f le NumberType else false

		| ToStringOp ->	if (le_type = StringType) then f le NumberType else false

		| ToNumberOp ->	if (le_type = NumberType)	then f le StringType else false

		| IsPrimitive -> false

		| Cdr	| Car	| LstLen -> f le ListType

		| StrLen -> if (le_type = NumberType) then f le StringType else false)


	| LBinOp (le1, op, le2) ->
		(match op with
		| Equal	| LessThan	| LessThanEqual -> false
		| LessThanString -> (f le1 StringType) && (f le2 StringType)

		| Plus	| Minus	| Times	| Mod ->
			if (le_type = NumberType)
				then ((f le1 le_type) && (f le2 le_type))
				else false

		| Div -> false

		| And | Or ->
			if (le_type = BooleanType)
				then ((f le1 BooleanType) && (f le2 BooleanType))
				else false

		| BitwiseAnd	| BitwiseOr	| BitwiseXor	| LeftShift	| SignedRightShift
		| UnsignedRightShift			| M_atan2			| M_pow
		| LstCons -> false

		| LstCat ->
			if (le_type = ListType)
				then ((f le1 ListType) && (f le2 ListType))
				else false

		| StrCat ->
			if (le_type = StringType)
				then ((f le1 StringType) && (f le2 StringType))
				else false

		| _ ->
			Printf.printf "Horror: op: %s, t: %s"  (JSIL_Print.string_of_binop op) (JSIL_Print.string_of_type le_type);
			raise (Failure "ERROR"))

		| LLstNth (le1, le2) -> (f le1 ListType) && (f le2 NumberType)

		| LStrNth (le1, le2) -> (f le1 StringType) && (f le2 NumberType)

		| LNone    -> (NoneType = le_type))


let reverse_type_lexpr gamma le le_type : typing_environment option =
	let new_gamma : typing_environment = gamma_init () in
	let ret = reverse_type_lexpr_aux gamma new_gamma le le_type in
	if (ret)
		then Some new_gamma
		else None




(***************************************************************)
(***************************************************************)
(** Conversion between meta-types                             **)
(***************************************************************)
(***************************************************************)

(** Turns a logical expression into an assertions.
    Returns a logical expression option and an assertion option. *)
let rec lift_logic_expr lexpr =
	(* TODO: Think of how to structure this code better *)
	let f = lift_logic_expr in
	(match lexpr with
	| LBinOp (le1, op, le2) -> lift_binop_logic_expr op le1 le2
	| LUnOp (op, le) -> lift_unop_logic_expr op le
	| LLit (Bool true) -> Some (LLit (Bool true)), Some (LTrue, LFalse)
	| LLit (Bool false) -> Some (LLit (Bool false)), Some (LFalse, LTrue)
	| _ -> Some lexpr, Some (LEq (lexpr, LLit (Bool true)), (LEq (lexpr, LLit (Bool false)))))
and lift_binop_logic_expr op le1 le2 =
	let err_msg = (Printf.sprintf "logical expression: binop %s cannot be lifted to assertion" (JSIL_Print.string_of_binop op)) in
	let f = lift_logic_expr in
	let lexpr_to_ass_binop binop =
		(match binop with
		| Equal          -> (fun le1 le2 -> LEq (le1, le2))
		| LessThan       -> (fun le1 le2 -> LLess (le1, le2))
		| LessThanString -> (fun le1 le2 -> LStrLess (le1, le2))
		| LessThanEqual  -> (fun le1 le2 -> LLessEq (le1, le2))
		| SetMem         -> (fun le1 le2 -> LSetMem (le1, le2))
		| SetSub         -> (fun le1 le2 -> LSetSub (le1, le2))
		| _ -> raise (Failure "Error: lift_binop_expr")) in
	(match op with
	| Equal
	| LessThan
	| LessThanString
	| LessThanEqual
	| SetMem
	| SetSub ->
		let l_op_fun = lexpr_to_ass_binop op in
		(match ((f le1), (f le2)) with
		| ((Some le1, _), (Some le2, _)) -> None, Some ((l_op_fun le1 le2), LNot (l_op_fun le1 le2))
		| ((None    , _), (Some   _, _)) -> raise (Failure (err_msg ^ " : LEFT : " ^ (JSIL_Print.string_of_logic_expression le1) ^ " : right : " ^ (JSIL_Print.string_of_logic_expression le2)))
		| ((Some   _, _), (None    , _)) -> raise (Failure (err_msg ^ " : left : " ^ (JSIL_Print.string_of_logic_expression le1) ^ " : RIGHT : " ^ (JSIL_Print.string_of_logic_expression le2)))
		| ((None    , _), (None    , _)) -> raise (Failure (err_msg ^ " : left and right.")))
	| And ->
		(match ((f le1), (f le2)) with
		| ((_, Some (a1, a1')), (_, Some (a2, a2'))) -> None, Some (LAnd (a1, a2), LOr (a1', a2'))
		| (_, _) -> raise (Failure err_msg))
	| Or ->
		(match ((f le1), (f le2)) with
		| ((_, Some (a1, a1')), (_, Some (a2, a2'))) -> None, Some (LOr (a1, a2), LAnd (a1', a2'))
		| (_, _) -> raise (Failure err_msg))
	| _ -> Some (LBinOp (le1, op, le2)), None)
and lift_unop_logic_expr op le =
	let f = lift_logic_expr in
	let err_msg = "Logical expression unop cannot be lifted to assertion." in
	(match op with
	| Not ->
		(match (f le) with
		| (None, Some (a, a')) -> None, Some (a', a)
		| (_, _) -> raise (Failure (err_msg ^ " Not")))
	| _ -> Some (LUnOp (op, le)), None)


let rec expr_2_lexpr (e : jsil_expr) : jsil_logic_expr =
	let f = expr_2_lexpr in
	match e with
	| Literal l           -> LLit l
	| Var x               -> PVar x
	| BinOp (e1, op, e2)  -> LBinOp ((f e1), op, (f e2))
	| UnOp (op, e)     -> LUnOp (op, f e)
	| TypeOf e            -> LTypeOf (f e)
	| EList es            -> LEList (List.map f es)
	| LstNth (e1, e2)     -> LLstNth (f e1, f e2)
	| StrNth (e1, e2)     -> LStrNth (f e1, f e2)


let rec lift_lit_list_to_logical_expr (lit : jsil_lit) : jsil_logic_expr =
	let f = lift_lit_list_to_logical_expr in 
	match lit with 
	| Undefined  | Null   | Empty     | Constant _ 
		| Bool _ | Num _  | String _  | Char _         
		| Loc _  | Type _ | CList _ -> LLit lit    
	| LList lst -> LEList (List.map f lst)


(***************************************************************)
(***************************************************************)
(** Macros                                                    **)
(***************************************************************)
(***************************************************************)

let rec expand_macro (macro_name : string) (params_vals : jsil_logic_expr list) : jsil_logic_command =
	if (Hashtbl.mem macro_table macro_name) then
		(let macro = Hashtbl.find macro_table macro_name in
		let params = macro.mparams in
		let lparo = List.length params in
		let lparv = List.length params_vals in
		if (lparo <> lparv) then
			raise (Failure (Printf.sprintf "Macro %s called with incorrect number of parameters: %d instead of %d." macro.mname lparv lparo))
		else
			let subst = init_substitution2 params params_vals in 
			macro_subst macro.mdefinition subst)
		else
			raise (Failure (Printf.sprintf "Macro %s not found in macro table." macro_name))
and
(** Apply function f to the logic expressions in a logic command, recursively when it makes sense. *)
lcmd_map f unfold_macros lcmd =
	(* Map recursively to commands, assertions, and expressions *)
	let map_l = lcmd_map f unfold_macros in
	let map_a = assertion_map None None (Some (logic_expression_map f None)) in
	let map_e = logic_expression_map f None in
	match lcmd with
	| Fold      a                   -> Fold      (map_a a)
	| Unfold    (a, info)           -> Unfold    ((map_a a), info)
	| RecUnfold s                   -> RecUnfold s
	| LogicIf   (e, lcmds1, lcmds2) -> LogicIf   (map_e e, List.map (fun x -> map_l x) lcmds1, List.map (fun x -> map_l x) lcmds2)
	| Macro     (name, params_vals) ->
		let fparams_vals = List.map (fun x -> map_e x) params_vals in
		(match unfold_macros with
		| true  -> expand_macro name fparams_vals
		| false -> Macro (name, fparams_vals))
and
macro_subst (lcmd : jsil_logic_command) (subst : (string, jsil_logic_expr) Hashtbl.t) : jsil_logic_command =
	let substitute =
		(fun e ->
			((match e with
			| PVar v ->
				(match Hashtbl.mem subst v with
				| true  -> Hashtbl.find subst v
				| false -> e)
			| _ -> e), true)) in
	lcmd_map substitute true lcmd


(***************************************************************)
(***************************************************************)
(** Concretising Quantifiers                                  **)
(***************************************************************)
(***************************************************************)

(** cross product between lst1 and lst2 *)
let cross_product (lst1 : 'a list) (lst2 : 'b list) : ('a * 'b) list = 
	List.concat (List.map (fun e1 -> List.map (fun e2 -> (e1, e2)) lst2) lst1) 

let concretise (a : jsil_logic_assertion) (x: string) (les : jsil_logic_expr list) : jsil_logic_assertion list =
	List.map (fun le -> asrt_substitution (init_substitution2 [ x ] [ le ]) true a) les

let concretise2 (a : jsil_logic_assertion) (x: string) (y: string) (les : jsil_logic_expr list) : jsil_logic_assertion list =
	List.map 
		(fun (le1, le2) -> asrt_substitution (init_substitution2 [ x; y ] [ le1; le2 ]) true a) 
		(cross_product les les)


(***************************************************************)
(***************************************************************)
(** Miscellaneous                                             **)
(***************************************************************)
(***************************************************************)

(* What does it mean to be a list? *)
let rec isList (le : jsil_logic_expr) : bool =
(match le with
	| LVar _
	| LLit (LList _)
	| LEList _ -> true
	| LBinOp (_, LstCons, le) -> isList le
	| LBinOp (lel, LstCat, ler) -> isList lel && isList ler
	| _ -> false)

let get_string_hashtbl_keys ht =
	Hashtbl.fold
		(fun key _ ac -> key :: ac)
		ht
		[]

let print_var_list var_list =
	List.fold_left
		(fun ac var -> if (ac = "") then var else ac ^ "; " ^ var)
		""
		var_list

let remove_string_duplicates strings =
	let string_set = SS.of_list strings in
	SS.elements string_set

let remove_number_duplicates numbers =
	let number_set = SN.of_list numbers in
	SN.elements number_set

let remove_int_duplicates ints =
	let int_set = SI.of_list ints in
	SI.elements int_set

(* TO DELETE *)
let get_subtraction_vars vars subst =
	SS.filter (fun x -> not (Hashtbl.mem subst x)) vars

let filter_vars vars ignore_vars : SS.t =
	SS.diff vars ignore_vars

let star_asses asses =
	List.fold_left
		(fun ac a ->
			if (not (a = LEmp))
				then (if (ac = LEmp) then a else LStar (a, ac))
				else ac)
		 LEmp
		asses



(***************************************************************)
(***************************************************************)
(** TO MOVE                                                   **)
(***************************************************************)
(***************************************************************)

let replace_spec_keywords
    (spec : jsil_spec option)
    (ret_var : string option)
    (err_var : string option) : (jsil_spec option) =

  (** Step 1 - Create a substitution mapping err and ret to the appropriate variables *)
  let subst_lst = match ret_var with | None -> []         | Some x -> [ "ret", PVar x ] in
  let subst_lst = match err_var with | None -> subst_lst  | Some x -> ("err", PVar x) :: subst_lst in 
  let subst     = init_substitution3 subst_lst in 

  (** Step 2 - Construct a new spec with the return and error keywords replaced by 
    * the appropriate program variables *)
  match spec with
  | None      -> None
  | Some spec ->
    	Some {
      		spec_name   = spec.spec_name;
      		spec_params = spec.spec_params;
      		proc_specs  = List.map
          		(fun cur_spec ->
             		{ 	pre      = cur_spec.pre;
               			post     = List.map (asrt_substitution subst true) cur_spec.post;
                        ret_flag = cur_spec.ret_flag;
             		}
          		) spec.proc_specs;
       		previously_normalised = spec.previously_normalised
    	}


(** REFACTORING NEEDED *)
let rec lexpr_selective_substitution subst partial lexpr =
	let f = lexpr_selective_substitution subst partial in
	match lexpr with
	| LLit lit -> LLit lit
	| LNone -> LNone

	| LVar var ->
		(match Hashtbl.mem subst var with
		| true ->
				let new_val = Hashtbl.find subst var in
				(match new_val with
				| LVar _ -> lexpr
				| _ ->
					(match isList new_val with
					| true -> new_val
					| false -> lexpr
					)
				)
		| false -> (match partial with
			| true -> lexpr
			| false ->
					let new_var = fresh_lvar () in
					Hashtbl.replace subst var (LVar new_var);
					LVar new_var)
		)

	| ALoc aloc ->
			(try Hashtbl.find subst aloc with _ ->
				if (not partial)
					then
						let new_aloc = ALoc (fresh_aloc ()) in
						Hashtbl.replace subst aloc new_aloc;
						new_aloc
					else
						ALoc aloc)

	| PVar var -> (PVar var)
	| LBinOp (le1, op, le2) -> LBinOp ((f le1), op, (f le2))
	| LUnOp (op, le) -> LUnOp (op, (f le))
	| LTypeOf le -> LTypeOf (f le)

	| LEList les ->
			let s_les = List.map (fun le -> (f le)) les in
			LEList s_les

	| LESet les ->
			let s_les = List.map (fun le -> (f le)) les in
			LESet s_les

	| LSetUnion les ->
			let s_les = List.map (fun le -> (f le)) les in
			LSetUnion s_les

	| LSetInter les ->
			let s_les = List.map (fun le -> (f le)) les in
			LSetInter s_les

	| LCList les ->
			let s_les = List.map (fun le -> (f le)) les in
			LCList s_les

	| LLstNth (le1, le2) -> LLstNth ((f le1), (f le2))
	| LStrNth (le1, le2) -> LStrNth ((f le1), (f le2))