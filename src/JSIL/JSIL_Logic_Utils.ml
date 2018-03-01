open CCommon
open SCommon
open JSIL_Syntax

(****************************************************************)
(****************************************************************)
(** JSIL Literals and Expressions - Generic AST functions      **)
(****************************************************************)
(****************************************************************)

let rec literal_fold 
	(f_ac    : Literal.t -> 'b -> 'b -> 'a list -> 'a) 
	(f_state : (Literal.t -> 'b -> 'b) option)
	(state   : 'b) 
	(lit     : Literal.t) : 'a =

	let new_state = (Option.default (fun le x -> x) f_state) lit state in
	let fold_lit  = literal_fold f_ac f_state new_state in
	let f_ac      = f_ac lit new_state state in

  	match lit with
  	| Undefined  | Null   | Empty    | Constant _ 
  	| Bool _ | Num _  | String _ 
  	| Loc _  | Type _ -> f_ac [] 
  	| LList lits -> f_ac (List.map fold_lit lits)

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
  			| LEList le           -> LEList (List.map map_e le)
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
  			| LAnd (a1, a2)                  -> LAnd (map_a a1, map_a a2)
  			| LOr (a1, a2)                   -> LOr (map_a a1, map_a a2)
  			| LNot a                         -> LNot (map_a a)
  			| LTrue                          -> LTrue
  			| LFalse                         -> LFalse
  			| LEq (e1, e2)                   -> LEq (map_e e1, map_e e2)
  			| LLess (e1, e2)                 -> LLess (map_e e1, map_e e2)
  			| LLessEq (e1, e2)               -> LLessEq (map_e e1, map_e e2)
  			| LStrLess (e1, e2)              -> LStrLess (map_e e1, map_e e2)
  			| LStar (a1, a2)                 -> LStar (map_a a1, map_a a2)
  			| LPointsTo (e1, e2, (perm, e3)) -> LPointsTo (map_e e1, map_e e2, (perm, map_e e3))
				| LMetaData (e1, e2)             -> LMetaData (map_e e1, map_e e2)
				| LExtensible (e1, b)            -> LExtensible (map_e e1, b)
  			| LEmp                           -> LEmp
  			| LPred (s, le)                  -> LPred (s, List.map map_e le)
  			| LTypes lt                      -> LTypes (List.map (fun (exp, typ) -> (map_e exp, typ)) lt)
  			| LEmptyFields (o, ls)           -> LEmptyFields (map_e o, map_e ls)
  			| LSetMem (e1, e2)               -> LSetMem (map_e e1, map_e e2)
  			| LSetSub (e1, e2)               -> LSetSub (map_e e1, map_e e2)
  			| LForAll (bt, a)                -> LForAll (bt, map_a a) in
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

	(* Not convinced these are correct *)
	| LPointsTo (le1, le2, (_, le3)) -> f_ac (fes [ le1; le2; le3 ])
	| LMetaData (le1, le2) -> f_ac (fes [ le1; le2 ])
	| LExtensible (le1, _) -> f_ac (fes [ le1 ])

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
let get_lexpr_non_list_lits (le : jsil_logic_expr) : Literal.t list =
	let fe_ac le _ _ ac = match le with
		| LLit lit -> lit :: (List.concat ac)
		| _      -> List.concat ac in 

	let flit_ac (lit : Literal.t) _ _ ac = match lit with 
		| LList lst -> List.concat ac 
		| _        -> [ lit ] in 

	let lits : Literal.t list = logic_expression_fold fe_ac None None le in
	List.concat (List.map (literal_fold flit_ac None None) lits) 

(* Returns all the non-list listerals that occur in --a-- *)
let get_asrt_non_list_lits (a : jsil_logic_assertion) : Literal.t list =	
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
	List.fold_left (fun (strings, numbers) (lit : Literal.t) -> 
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

(* ********************************* *)
(* ********************************* *)
(* ********************************* *)

let get_lexpr_substitutables (le : jsil_logic_expr) : SS.t = 
	let fe_ac le _ _ ac = match le with
		| LVar x 
		| ALoc x -> [ x ]
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


(* Get all the concrete locations in [le] *)
let rec get_lexpr_clocs (le : jsil_logic_expr) : SS.t =
  let fe_ac le _ _ ac =
    match le with
    | LLit (Loc l) -> l :: (List.concat ac)
    | _ -> List.concat ac in
  SS.of_list (logic_expression_fold fe_ac None None le)

(* Get all the concrete locations in [a] *)
let rec get_asrt_clocs (a : jsil_logic_assertion) : SS.t =
  let fe_ac le _ _ ac =
    match le with
    | LLit (Loc l) -> l :: (List.concat ac)
    | _ -> List.concat ac in
  let fe = logic_expression_fold fe_ac None None in 
  let f_ac a _ _ ac = List.concat ac in
  SS.of_list (assertion_fold (Some fe) f_ac None None a)


(* Get all the variables in [le] *)
let get_lexpr_vars (le : jsil_logic_expr) : SS.t =
  let vars = [get_lexpr_alocs le; get_lexpr_clocs le; get_lexpr_lvars le; get_lexpr_pvars le] in
  List.fold_left SS.union SS.empty vars

(* Get all the variables in [a] *)
let get_asrt_vars (a : jsil_logic_assertion) : SS.t =
  let vars = [get_asrt_alocs a; get_asrt_clocs a; get_asrt_lvars a; get_asrt_pvars a] in
  List.fold_left SS.union SS.empty vars


(* Get all the types in --a-- *)
let rec get_asrt_types (a : jsil_logic_assertion) : (jsil_logic_expr * Type.t) list =
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

(* a bijective logical expression only performs bijective actions, ie if we
   know the structure of the expression, we can get back all the values *)
let rec is_bijective_lexpr (le : jsil_logic_expr) : bool =
  match le with
  | LLit _
  | LVar _
  | ALoc _
  | PVar _ ->
    true
  | LBinOp (le1, binop, le2) -> begin
    match binop with
      | LstCons ->
        let lhs_ok = is_bijective_lexpr le1 in
        let rhs_ok = is_bijective_lexpr le2 in
        lhs_ok && rhs_ok
      | _ ->
        false
    end
  | LUnOp _
  | LLstNth _
  | LStrNth _ ->
    false (* if we know x = 'c' and x = LStrNth(#foo, 3), we can't get back #foo *)
  | LEList les
  | LESet les ->
    List.for_all is_bijective_lexpr les
  | LSetUnion _
  | LSetInter _ ->
    false
  | LNone ->
    true

(***************************************************************)
(***************************************************************)
(** Pure Assertions                                           **)
(***************************************************************)
(***************************************************************)

(* Check if --a-- is a pure assertion *)
let is_pure_asrt (a : jsil_logic_assertion) : bool =
	let f_ac a _ _ ac =
		match a with
		| LPred _ | LPointsTo _ | LEmp | LEmptyFields _
		| LMetaData _ | LExtensible _ -> false
		| _  -> List.for_all (fun b -> b) ac in
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
		(match Hashtbl.find_opt subst x with 
		| Some v -> v
		| None -> 
			if partial then le_x_old else (
				let new_le_x = make_new_x () in 
				Hashtbl.replace subst x new_le_x;
				new_le_x)) in  

	let f_before le = match le with 
		| LVar x    -> find_in_subst x le (fun () -> LVar (fresh_lvar ())), false 
		| ALoc x    -> find_in_subst x le (fun () -> ALoc (fresh_aloc ())), false
		| PVar x    -> find_in_subst x le (fun () ->
				let pvar = fresh_pvar () in
				print_debug_petar (Printf.sprintf "Unable to find PVar %s in subst, generating fresh: %s" x pvar); 
				PVar (fresh_pvar ())), false 
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

(** Applies --subst'-- to --subst-- *)
let apply_subst_to_subst subst' subst = 
	Hashtbl.iter (fun k v -> 
		let v' = lexpr_substitution subst' true v in
		Hashtbl.replace subst k v')
	subst

(***************************************************************)
(***************************************************************)
(** Logic Commmands                                           **)
(***************************************************************)
(***************************************************************)

(* Map over the logic commands
	*)
let rec logic_command_map_old
	(f_l : (jsil_logic_command -> jsil_logic_command))
	(lcmd : jsil_logic_command) : jsil_logic_command =

	(* Functions to map over assertions and expressions *)
	let map_l                = logic_command_map_old f_l in
	match f_l lcmd with
	| LogicIf (le, lcmds_then, lcmds_else) -> LogicIf (le, (List.map map_l lcmds_then), (List.map map_l lcmds_else))
	| l_cmd -> l_cmd

(* Map over the logic commands,
	applying f_l (which should NON-RECURSIVE) to the logical commands,
			 f_a to the logical assertions
			 f_e to the logical expressions,
	recursing over lists of logical expressions.
	*)
let rec logic_command_map
	(f_l : (jsil_logic_command -> jsil_logic_command) option)
	(f_a : (jsil_logic_assertion -> jsil_logic_assertion * bool) option)
	(f_e : (jsil_logic_expr -> jsil_logic_expr * bool) option)
	(lcmd : jsil_logic_command) : jsil_logic_command =

	(* Functions to map over assertions and expressions *)
	let map_l    = logic_command_map f_l f_a f_e in
	let some_f_e = Option.default (fun e -> (e, true)) f_e in
	let map_a    = assertion_map f_a None None in
	let map_e    = logic_expression_map some_f_e None in

	(* Apply the given function to the logical command *)
	let some_f_l = Option.default (fun l -> l) f_l in
	let mapped_lcmd = some_f_l lcmd in

	(* Map over the elements of the command *)
	match mapped_lcmd with
		| Fold a -> Fold (map_a a)
		| Unfold (a, None) -> Unfold ((map_a a), None)
		| Unfold (a, (Some (s, l))) -> Unfold ((map_a a), (Some (s, (List.map (fun (x, e) -> (x, (map_e e))) l))))
		| ApplyLem (s, l) -> ApplyLem (s, (List.map map_e l))
		| RecUnfold s -> RecUnfold s
		| LogicIf (e, l1, l2) -> LogicIf ((map_e e), (List.map map_l l1), (List.map map_l l2))
		| Macro (s, l) -> Macro (s, (List.map map_e l))
		| Assert a -> Assert (map_a a)

(***************************************************************)
(***************************************************************)
(** JSIL Types                                                **)
(***************************************************************)
(***************************************************************)

(******************)
(* Type inference *)
(******************)

let rec infer_types_to_gamma flag gamma new_gamma le (tt : Type.t) : bool =

	let f = infer_types_to_gamma flag gamma new_gamma in
	
	(match le with
	(* Literals are always typable *)
	| LLit lit -> (Literal.type_of lit = tt)

	(* Variables are reverse-typable if they are already typable *)
	(* with the target type or if they are not typable           *)
	| LVar var
	| PVar var ->
		(match (TypEnv.get gamma var), (TypEnv.get new_gamma var) with
		| Some t, None
		| None, Some t     -> (t = tt)
		| None, None       -> (TypEnv.update new_gamma var (Some tt)); true
		| Some t1, Some t2 -> t1 = t2)

	(* Abstract locations are reverse-typable if the target type is ObjectType *)
	| ALoc _ -> tt = ObjectType

    (* LEList and LESet are not reverse typable because we lose type information *)
	| LEList _ -> if flag then (tt = ListType) else false			
	| LESet  _ -> if flag then (tt =  SetType) else false			

	(* Members of unions and intersections must all be sets *)
	| LSetUnion les
	| LSetInter les -> (tt = SetType) && (List.for_all (fun x -> f x SetType) les) 

	| LUnOp (unop, le) ->
		(match unop with
		| Not -> (tt = BooleanType) && (f le BooleanType)

		| UnaryMinus	| BitwiseNot	| M_sgn		| M_abs		
		| M_acos		| M_asin		| M_atan	| M_ceil
		| M_cos			| M_exp			| M_floor	| M_log		
		| M_round		| M_sin			| M_sqrt	| M_tan
		| ToIntOp		| ToUint16Op	| ToInt32Op	| ToUint32Op -> (tt = NumberType) && (f le NumberType)

		| ToStringOp ->	(tt = StringType) && (f le NumberType)
		| ToNumberOp ->	(tt = NumberType) && (f le StringType)

		| IsPrimitive -> (tt = BooleanType)
		| TypeOf      -> (tt = TypeType)

		| Cdr    -> (tt = ListType) && (f le ListType)
		| Car    -> f le ListType
		| LstLen -> (tt = NumberType) && (f le ListType)
		| StrLen -> (tt = NumberType) && (f le StringType))


	| LBinOp (le1, op, le2) ->
		let (rqt1 : Type.t option), (rqt2 : Type.t option), (rt : Type.t) =
			(match op with
			| Equal          ->             None,             None, BooleanType
			| LessThan            
			| LessThanEqual  ->  Some NumberType,  Some NumberType, BooleanType
			| LessThanString ->  Some StringType,  Some StringType, BooleanType
			| And            -> Some BooleanType, Some BooleanType, BooleanType
			| Or             -> Some BooleanType, Some BooleanType, BooleanType
			| LstCons        ->             None,    Some ListType, ListType   
			| LstCat         ->    Some ListType,    Some ListType, ListType   
			| StrCat         ->  Some StringType,  Some StringType, StringType
			| SetMem         ->             None,     Some SetType, BooleanType
			| SetDiff        ->     Some SetType,     Some SetType, SetType
			| SetSub         ->     Some SetType,     Some SetType, BooleanType    
			| _              ->  Some NumberType,  Some NumberType, NumberType
			) in
		(tt = rt) && 
		(Option.map_default (fun t -> f le1 t) true rqt1) &&
		(Option.map_default (fun t -> f le2 t) true rqt2)

		| LLstNth (le1, le2) -> (f le1 ListType)   && (f le2 NumberType)
		| LStrNth (le1, le2) -> (f le1 StringType) && (f le2 NumberType)

		| LNone -> (tt = NoneType))

let reverse_type_lexpr flag gamma le le_type : TypEnv.t option =
	let new_gamma : TypEnv.t = TypEnv.init () in
	let ret = infer_types_to_gamma flag gamma new_gamma le le_type in
		if (ret) then Some new_gamma else None

(*****************)
(* Type checking *)
(*****************)

let rec type_lexpr (gamma : TypEnv.t) (le : jsil_logic_expr) : Type.t option * bool * jsil_logic_assertion list =

	let f = type_lexpr gamma in
	let def_pos (ot : Type.t option) = (ot, true, []) in
	let def_neg = (None, false, []) in

	let infer_type le tt constraints = 
		let outcome = reverse_type_lexpr true gamma le tt in
			Option.map_default 
			(fun new_gamma -> 
				TypEnv.extend gamma new_gamma;
				(Some tt, true, constraints)
			) def_neg outcome in

	let typable_list ?(target_type : Type.t option) les = 
		(List.fold_left
			(fun (ac, ac_constraints) elem ->
				if (not ac) then (false, [])
				else 
					let (t, ite, constraints) = 
						let (t, ite, constraints) = f elem in
						(match t with 
						| Some _ -> (t, ite, constraints)
						| None -> (match target_type with 
							| None -> (t, ite, constraints)
							| Some tt -> infer_type elem tt constraints
							)
						) in 
					let correct_type = (target_type = None) || (t = target_type) in
					(ac && correct_type && ite, constraints @ ac_constraints))
			(true, [])
			les) in

	let result = (match le with

	(* Literals are always typable *)
  	| LLit lit -> def_pos (Some (Literal.type_of lit))

	(* Variables are typable if in gamma, otherwise no, but typing continues *)
	| LVar var
	| PVar var -> def_pos (TypEnv.get gamma var)

	(* Abstract locations are always typable, by construction *)
	| ALoc _ -> def_pos (Some ObjectType)

  	(* Lists are typable if no element breaks typing *)
	| LEList les -> 
		let all_typable, constraints = typable_list les in
			if (all_typable) then (Some ListType, true, constraints) else def_neg

	(* Sets are typable if no element breaks typing *)
	| LESet les ->
		let all_typable, constraints = typable_list les in
			if (all_typable) then (Some SetType, true, constraints) else def_neg

 	| LUnOp (unop, e) ->
		let (_, ite, constraints) = f e in

		(match ite with
		| false -> def_neg
		| true -> 
			let (tt : Type.t), new_constraints = 
			(match unop with
			| TypeOf      -> TypeType,    []
			| Not         -> BooleanType, []
			| ToStringOp  -> StringType,  []
			| IsPrimitive -> BooleanType, []
			| Car | Cdr   -> ListType,    [ (LLessEq (LLit (Num 1.), LUnOp (LstLen, e))) ]
			| _           -> NumberType,  []
			) in
			infer_type le tt (new_constraints @ constraints))

	| LBinOp (e1, op, e2) ->
		let (_, ite1, constraints1) = f e1 in
		let (_, ite2, constraints2) = f e2 in
		let constraints = constraints1 @ constraints2 in

		(* Both expressions must be typable *)
		(match ite1, ite2 with
		| true, true ->	
			let tt : Type.t =
			(match op with
			| Equal			| LessThan		| LessThanEqual	| LessThanString 
			| And			| Or			| SetMem		| SetSub -> BooleanType
			| LstCons		| LstCat -> ListType   
			| SetDiff -> SetType    
			| StrCat  -> StringType
			| _       -> NumberType
			) in
			infer_type le tt constraints

		| _, _ -> def_neg)


	(* List length is typable with constraints *)
	| LLstNth (lst, index) ->
		let _, _, constraints1 = f lst in
		let _, _, constraints2 = f index in
		let constraints = constraints1 @ constraints2 in
		let _, success, _ = infer_type lst ListType constraints in
		(match success with
		| false -> def_neg
		| true -> 
			let _, success, _ = infer_type index NumberType constraints in
			(match success with
			| false -> def_neg
			| true -> 
				let new_constraint1 = (LLessEq (LLit (Num 0.), index)) in
				let new_constraint2 = (LLess (index, LUnOp (LstLen, lst))) in
				(None, true, (new_constraint1 :: (new_constraint2 :: constraints)))
			)
		)

	(* String length is typable with constraints *)
	| LStrNth (str, index) ->
		let _, _, constraints1 = f str in
		let _, _, constraints2 = f index in
		let constraints = constraints1 @ constraints2 in
		let _, success, _ = infer_type str ListType constraints in
		(match success with
		| false -> def_neg
		| true -> 
			let _, success, _ = infer_type index NumberType constraints in
			(match success with
			| false -> def_neg
			| true -> 
				let new_constraint1 = (LLessEq (LLit (Num 0.), index)) in
				let new_constraint2 = (LLess (index, LUnOp (StrLen, str))) in
				(None, true, (new_constraint1 :: (new_constraint2 :: constraints)))
			)
		)
		
	| LSetUnion les
	| LSetInter les -> 
  		let all_typable, constraints = typable_list ?target_type:(Some SetType) les in
			if (all_typable) then (Some SetType, true, constraints) else def_neg

	| LNone -> (Some NoneType, true, [])) in

	result

(* ******************** *)
(* ** TYPE INFERENCE ** *)
(* ******************** *)

let safe_extend_gamma gamma le t = 
  let new_gamma = reverse_type_lexpr true gamma le t in
    (match new_gamma with
    | Some new_gamma -> TypEnv.extend gamma new_gamma
    | None -> 
		let msg = Printf.sprintf "SEG: Untypable expression: %s in %s" (JSIL_Print.string_of_logic_expression le) (TypEnv.str gamma) in
		print_debug_petar msg;
		raise (Failure msg)) 

(* Destructively extend gamma with typing information from logic expressions *)
let rec infer_types_expr gamma le : unit =
	let f = infer_types_expr gamma in
	let e = safe_extend_gamma gamma in

		(match le with
  	
		(* Do nothing, these cases do not provide additional information *)
		| LLit  _
		| ALoc  _
		| LVar  _
		| PVar  _
		| LNone   -> ()

		(* Set union and intersection - all members must be sets, plus any additional information from the members themselves *)
		| LSetUnion lle
		| LSetInter lle -> 
			e le SetType;
			List.iter (fun le -> f le) lle
				
		| LEList lle 
		| LESet  lle -> 
			List.iter (fun le -> f le) lle
			
		| LLstNth (lst, idx) ->
			e lst ListType;
			e idx NumberType
			
		| LLstNth (str, idx) ->
			e str StringType;
			e idx NumberType
  		
	  	(*
	  	| LBinOp   of jsil_logic_expr * BinOp.t * jsil_logic_expr (** Binary operators ({!type:BinOp.t}) *)
	  	| LUnOp    of UnOp.t * jsil_logic_expr                    (** Unary operators ({!type:UnOp.t}) *)
	  	| LTypeOf  of jsil_logic_expr	                               (** Typing operator *)
	  	| LCList   of jsil_logic_expr list                           (** Lists of logical chars *)
	  	*)
		
		| LBinOp (le1, op, le2) ->
			(match op with
			| Plus | Minus | Times | Div | Mod ->
					e le1 NumberType;
					e le2 NumberType;
			| LstCons ->
					f le1;
					e le2 ListType;
			| LstCat ->
					e le1 ListType;
					e le2 ListType
			| _ -> ())
  
  	| _ -> ())

(* Destructively extend gamma with typing information from logic assertions *)
let rec infer_types_asrt gamma (a : jsil_logic_assertion) : unit =
	let f = infer_types_asrt gamma in
	let fe = infer_types_expr gamma in
	let e = safe_extend_gamma gamma in

		(match a with
  
    | LTrue
    | LFalse
		| LEmp
		| LTypes _ -> ()

    | LNot a -> f a
		| LForAll (_, a) -> f a

		| LAnd  (a1, a2)	    
    | LOr   (a1, a2)		  	    
    | LStar	(a1, a2) -> f a1; f a2
		
		(* Why isn't le1 required to be an object type? *)
    | LPointsTo	(le1, le2, (_, le3)) -> fe le1; fe le2; fe le3
		| LMetaData (le1, le2) -> fe le1; fe le2
		| LExtensible (le1, _) -> fe le1
		
		| LLess	  (le1, le2)		
    | LLessEq	(le1, le2) -> 
				e le1 NumberType;
				e le2 NumberType
		
		| _ -> ()) 
    
		(*
		| LPred			    of string * (jsil_logic_expr list)                         (** Predicates *)
    
    | LTypes		    of (jsil_logic_expr * Type.t) list                      (** Typing assertion *)
    | LEmptyFields	    of jsil_logic_expr * jsil_logic_expr                       (** emptyFields assertion *)
    | LEq			    of jsil_logic_expr * jsil_logic_expr                       (** Expression equality *)
    | LStrLess	        of jsil_logic_expr * jsil_logic_expr                       (** Expression less-than for strings *)
    | LSetMem  	        of jsil_logic_expr * jsil_logic_expr                       (** Set membership *)
    | LSetSub  	        of jsil_logic_expr * jsil_logic_expr                       (** Set subsetness *) *)



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
	let err_msg = (Printf.sprintf "logical expression: binop %s cannot be lifted to assertion" (BinOp.str op)) in
	let f = lift_logic_expr in
	let lexpr_to_ass_binop (binop : BinOp.t) =
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
	| UnOp (op, e)        -> LUnOp (op, f e)
	| EList es            -> LEList (List.map f es)
	| LstNth (e1, e2)     -> LLstNth (f e1, f e2)
	| StrNth (e1, e2)     -> LStrNth (f e1, f e2)


let rec lift_lit_list_to_logical_expr (lit : Literal.t) : jsil_logic_expr =
	let f = lift_lit_list_to_logical_expr in 
	match lit with     
	| LList lst -> LEList (List.map f lst)
	| _ -> LLit lit


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

let all_literals les = List.for_all (fun x -> (match x with | LLit _ -> true | _ -> false)) les 

let rec isList (le : jsil_logic_expr) : bool =
	let f = isList in
	(match le with
	| PVar _
	| LVar _
	| LLit (LList _)
	| LEList _ -> true
	| LBinOp (_, LstCons, le) -> f le
	| LBinOp (lel, LstCat, ler) -> f lel && f ler
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
			  | ALoc _ -> new_val
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

	| LLstNth (le1, le2) -> LLstNth ((f le1), (f le2))
	| LStrNth (le1, le2) -> LStrNth ((f le1), (f le2))

