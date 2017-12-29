open DynArray
open Set
open Stack
open JSIL_Syntax
open JSIL_Print

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

	| LPred (_, les)            -> f_ac (fes les)

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


(* Get all the logical expressions denoting sets in --le-- *)
let rec get_lexpr_sets (le : jsil_logic_expr) : jsil_logic_expr list =
	let fe_ac le _ _ ac =
		match le with
		| LESet _                 
		| LSetUnion _             
		| LSetInter _             
		| LBinOp (_, SetDiff, _)   
		| LBinOp (_, SetMem, _)  
		| LBinOp (_, SetSub, _)  -> le :: (List.concat ac)
		| _ -> (List.concat ac) in 
	logic_expression_fold fe_ac None None le


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


(* Rewrites the occurrences of the predicate --p-- in --a-- as --p'-- *)
let rewrite_pred_name (p : string) (p' : string) (a : jsil_logic_assertion) : jsil_logic_assertion =
	let f_a_after a = 
		match a with 
		| LPred (s, les) -> if (s = p) then LPred(p', les) else a 
		| _              -> a in 
	assertion_map None (Some f_a_after) None a 


(* Get all the expressions denoting sets in --a-- *)
let rec get_asrt_sets (a : jsil_logic_assertion) : jsil_logic_expr list  =
	let f_ac a _ _ ac = List.concat ac in
 	assertion_fold (Some get_lexpr_sets) f_ac None None a


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

exception FoundIt of jsil_logic_expr
exception UnionInUnion of jsil_logic_expr list

(**
	List simplifications:

	Finding if the given logical expression is equal to a list.
	If yes, returning one of those lists
*)
let find_me_Im_a_list store pfs le =
	let found = ref [le] in
	let counter = ref 0 in
	try
	(
		while (!counter < List.length !found)
		do
			let lex = List.nth !found !counter in
			counter := !counter + 1;
			(match lex with
			| PVar var ->
				counter := !counter + 1;
				if (Hashtbl.mem store var) then
				(let value = Hashtbl.find store var in
				(match value with
				| LLit (LList _)
				| LEList _ -> raise (FoundIt value)
				| LBinOp (lcar, LstCons, lcdr) when (not (lcar = LUnOp (Car, PVar var) && (lcdr = LUnOp (Cdr, PVar var)))) -> raise (FoundIt (LBinOp (lcar, LstCons, lcdr)))
				| _ ->
					if (not (List.mem value !found)) then
					begin
						found := !found @ [value];
						DynArray.iter
							(fun x -> (match x with
								| LEq (PVar v, lexpr)
								| LEq (lexpr, PVar v) ->
									if (v = var) then
										if (not (List.mem lexpr !found)) then
											found := !found @ [lexpr];
								| _ -> ())) pfs;
					end))
			| LVar var ->
				DynArray.iter
					(fun x -> (match x with
						| LEq (LVar v, lexpr)
						| LEq (lexpr, LVar v) ->
							if (v = var) then
							(match lexpr with
							| LLit (LList _)
							| LEList _ -> raise (FoundIt lexpr)
							| LBinOp (lcar, LstCons, lcdr) when (not (lcar = LUnOp (Car, PVar var) && (lcdr = LUnOp (Cdr, LVar var)))) -> raise (FoundIt (LBinOp (lcar, LstCons, lcdr)))
							| _ ->
								if (not (List.mem lexpr !found)) then
									found := !found @ [lexpr])
						| _ -> ())) pfs;
			| _ -> ());
		done;
		let flist = List.filter
			(fun x -> match x with
				| LLit (LList _)
				| LEList _ -> true
				| _ -> false) !found in
		if (flist = [])
			then le
			else (List.hd flist)
	) with FoundIt result -> result

let rec find_me_Im_a_loc pfs lvar = 
	match pfs with 
	| [] -> None 
	| LEq (lvar', ALoc loc) :: rest
	| LEq (lvar', LLit (Loc loc))  :: rest
	| LEq (ALoc loc, lvar') :: rest
	| LEq ( LLit (Loc loc), lvar') :: rest ->
		if (lvar = lvar') 
			then Some loc 
			else find_me_Im_a_loc rest lvar
	| _ :: rest -> find_me_Im_a_loc rest lvar

let find_me_in_the_pi pfs nle =
	DynArray.fold_left (fun ac a -> 
			(match a with 
			| LEq (LVar lvar, le)
			| LEq (le, LVar lvar) -> 
				if (le = nle) 
					then Some lvar
					else ac
			| _ -> ac)
			) None pfs

let rec replace_nle_with_lvars pfs nle = 
	(match nle with 
	| LBinOp (le, op, le') -> 
		(match find_me_in_the_pi pfs nle with 
		| Some lvar -> (LVar lvar)
		| None -> 
			let lhs = replace_nle_with_lvars pfs le in
			let rhs = replace_nle_with_lvars pfs le' in
			let lhs_string = string_of_logic_expression lhs in
			(LBinOp (lhs, op, rhs)))
	| LUnOp (op, le) -> 
		(match find_me_in_the_pi pfs nle with 
		| Some lvar -> (LVar lvar)
		| None -> (LUnOp (op, (replace_nle_with_lvars pfs le))))
	| LTypeOf le -> 
		(match find_me_in_the_pi pfs nle with 
		| Some lvar -> (LVar lvar)
		| None -> (LTypeOf (replace_nle_with_lvars pfs le)))
	| LLstNth (le, le') -> 
		(match find_me_in_the_pi pfs nle with 
		| Some lvar -> (LVar lvar)
		| None -> 
			let lst = replace_nle_with_lvars pfs le in
			let num = replace_nle_with_lvars pfs le' in
			LLstNth (lst, num))
	| LStrNth (le, le') -> 
		(match find_me_in_the_pi pfs nle with 
		| Some lvar -> (LVar lvar)
		| None -> 
			let lst = replace_nle_with_lvars pfs le in
			let num = replace_nle_with_lvars pfs le' in
			LStrNth (lst, num))
	| LEList le ->
		(match find_me_in_the_pi pfs nle with 
		| Some lvar -> (LVar lvar)
		| None -> 
			let le_list = List.map (fun le' -> replace_nle_with_lvars pfs le') le in
			(LEList le_list))
	| LCList le -> 
		(match find_me_in_the_pi pfs nle with 
		| Some lvar -> (LVar lvar)
		| None -> 
			let le_list = List.map (fun le' -> replace_nle_with_lvars pfs le') le in
			(LCList le_list))
	| LESet le -> 
		(match find_me_in_the_pi pfs nle with 
		| Some lvar -> (LVar lvar)
		| None -> 
			let le_list = List.map (fun le' -> replace_nle_with_lvars pfs le') le in
			(LESet le_list))
	| LSetUnion le -> 
		(match find_me_in_the_pi pfs nle with 
		| Some lvar -> (LVar lvar)
		| None -> 
			let le_list = List.map (fun le' -> replace_nle_with_lvars pfs le') le in
			(LSetUnion le_list))
	| LSetInter le -> 
		(match find_me_in_the_pi pfs nle with 
			| Some lvar -> (LVar lvar)
			| None -> 
				let le_list = List.map (fun le' -> replace_nle_with_lvars pfs le') le in
				(LSetInter le_list))
	| _ -> nle)

(**
	Internal String representation conversions
*)
let internal_string_explode s =
	let rec exp i l =
		if i < 0 then l else exp (i - 1) ((Char s.[i]) :: l) in
	exp (String.length s - 1) []

let rec lit_string_to_list (sl : jsil_lit) : jsil_lit =
	match sl with
		| LList l ->
			LList (List.map lit_string_to_list l)
		| String s -> CList (internal_string_explode s)
		| _ -> sl

(* To go from String to an internal representation, requires the extra bool return to indicate whether to recurse *)
let rec le_string_to_list (se : jsil_logic_expr) : jsil_logic_expr * bool =
	let f s = 
		let res, _ = le_string_to_list s in 
		res in 
	(match se with
		| LLit l -> (LLit (lit_string_to_list l), false)
		| LBinOp (sel, StrCat, ser) ->
			(LBinOp ((f sel), CharCat, (f ser)), false)
		| LVar _ -> (se, false)
		| _ -> (se, true))

let rec lit_list_to_string (sl : jsil_lit) : jsil_lit =
	match sl with
		| CList l -> String (String.concat "" (List.map (fun (Char x) -> String.make 1 x) l))
		| LList l -> LList (List.map lit_list_to_string l)
		| _ -> sl

(* Reverse of the above, to return to String representation from internal representation *)
let rec le_list_to_string (se : jsil_logic_expr) : jsil_logic_expr * bool =
	let f s = 
		let res, _ = le_list_to_string s in 
		res in 
	(match se with
		| LVar _ -> (se, false)
		| LLit l -> (LLit (lit_list_to_string l), false)
		| LCList l -> 
				(try (
					let str = String.concat "" (List.map (fun x -> match x with | LLit (Char c) -> String.make 1 c) l) in
					(LLit (String str), false) 
				) with | _ -> print_debug_petar "String representation leftovers."; (se, false))
		| LBinOp (sel, CharCat, ser) -> (LBinOp ((f sel), StrCat, (f ser)), false)
		| _ -> (se, true))


let all_set_literals lset = List.fold_left (fun x le -> 
	let result = (match le with
		| LESet _ -> true
		| _ -> false) in
	(* print_debug (Printf.sprintf "All literals: %s -> %b" (string_of_logic_expression le) result); *)
	x && result
	) true lset 

(**
	Reduction of expressions: everything must be IMMUTABLE

	Binary operators - recursively
	TypeOf           - recursively
	LEList           - reduce each expression, then if we have all literals,
	                   transform into a literal list
	List nth         - try to get a list and then actually reduce
	String nth       - ------- || -------
	List length      - try to get a list and then actually calculate
	String length    - ------- || -------
*)
let rec reduce_expression (store : (string, jsil_logic_expr) Hashtbl.t)
                          (gamma : (string, jsil_type) Hashtbl.t)
						  (pfs   : jsil_logic_assertion DynArray.t)
						  (e     : jsil_logic_expr) =
	
	(* print_debug (Printf.sprintf "Reduce expression: %s" (string_of_logic_expression e)); *)
	
	let f = reduce_expression store gamma pfs in
	let orig_expr = e in
	let result = (match e with

	| LUnOp (M_sgn, LLit (Num n)) -> LLit (Num (copysign 1.0 n))

	| LBinOp (le1, LstCons, LEList []) -> LEList [ f le1 ]
	| LBinOp (le1, LstCons, LLit (LList [])) -> LEList [ f le1 ] 
	| LBinOp (le1, CharCons, LCList []) -> LCList [ f le1 ]
	| LBinOp (le1, CharCons, LLit (CList [])) -> LCList [ f le1 ]
	| LBinOp (LEList le1, LstCat,  LEList le2) -> f (LEList (le1 @ le2))
	| LBinOp (LLit (LList le1), LstCat, LLit (LList le2)) -> f (LLit (LList (le1 @ le2)))
	| LBinOp (LLit (LList le1), LstCat, LEList le2) -> 
			let le1 = List.map (fun x -> LLit x) le1 in
			f (LEList (le1 @ le2))
	| LBinOp (LEList le1, LstCat, LLit (LList le2)) -> 
			let le2 = List.map (fun x -> LLit x) le2 in
			f (LEList (le1 @ le2))
	| LBinOp (LLit (String s1), StrCat, LLit (String s2)) -> f (LLit (String (s1 ^ s2)))
	| LBinOp (LCList le1, CharCat, LCList le2) -> f (LCList (le1 @ le2))

  (* List equality *)
	| LBinOp (LUnOp (Car, PVar x), LstCons, LUnOp (Cdr, PVar y)) when (x = y) -> PVar x
	| LBinOp (LUnOp (Car, LVar x), LstCons, LUnOp (Cdr, LVar y)) when (x = y) -> LVar x
								
	| LUnOp (ToStringOp, LLit (Num n)) -> LLit (String (Utils.float_to_string_inner n))

	| LESet s -> 
			let s' = List.map f s in
			LESet (SLExpr.elements (SLExpr.of_list s'))
	
	| LSetUnion s ->
			let s' = SLExpr.elements (SLExpr.of_list (List.filter (fun x -> x <> LESet []) (List.map f s))) in
			(match (all_set_literals s') with
			| true ->
					let all_elems = List.fold_left (fun ac le -> 
						(match le with | LESet lst -> ac @ lst)) [] s' in
					let all_elems = SLExpr.elements (SLExpr.of_list all_elems) in
					f (LESet all_elems)
			| false ->
					try (
						let ss' = SLExpr.of_list s' in
						SLExpr.iter (fun x -> 
							(match x with
							| LSetUnion s'' ->
								let ss' = SLExpr.remove x ss' in
								let ss' = SLExpr.union ss' (SLExpr.of_list s'') in
								let ss' = SLExpr.elements ss' in
								raise (UnionInUnion ss')
							| _ -> ())
							) ss';
						LSetUnion s'
					) with
					| UnionInUnion e -> f (LSetUnion e))
				
	| LSetInter s ->
			let s' = List.map f s in
			let s' = SLExpr.of_list s' in
			let is_empty_there = SLExpr.mem (LESet []) s' in
			(match is_empty_there with
			| true -> LESet []
			| false -> LSetInter (SLExpr.elements s'))

	| LBinOp (le1, SetDiff, le2) when (f le1 = f le2) -> LESet []
	| LBinOp (le1, SetDiff, le2) ->
			let sle1 = f le1 in
			let sle2 = f le2 in
			(match sle1, sle2 with
			| _, LESet [] -> f sle1
			| LESet le1, LESet le2 -> f (LESet (SLExpr.elements (SLExpr.diff (SLExpr.of_list le1) (SLExpr.of_list le2))))
			| LSetUnion l1, LSetUnion l2 ->
					let sl1 = SLExpr.of_list l1 in
					let sl2 = SLExpr.of_list l2 in
					let inter = SLExpr.inter sl1 sl2 in
					let sl1 = SLExpr.diff sl1 inter in
					let sl2 = SLExpr.diff sl2 inter in
					let sle1 = LSetUnion (SLExpr.elements sl1) in
					let sle2 = LSetUnion (SLExpr.elements sl2) in
						f (LBinOp (sle1, SetDiff, sle2))
			| _, _ -> LBinOp (sle1, SetDiff, sle2))
			

	(* List append *)
	| LBinOp (le1, LstCat, le2) ->
		let fe1 = f le1 in 
		let fe2 = f le2 in
		let result = 
		(match fe1 with
		| LEList [] -> fe2
		| LLit (LList []) -> fe2
		| _ -> (match fe2 with
			| LEList [] -> fe1
			| LLit (LList []) -> fe1
			| _ -> LBinOp (fe1, LstCat, fe2))) in
		result
		
	(* String concat *)
	| LBinOp (le1, StrCat, le2) ->
		let fe1 = f le1 in 
		let fe2 = f le2 in
		let result = 
		(match fe1 with
		| LLit (String "") -> fe2
		| _ -> (match fe2 with
			| LLit (String "") -> fe1
			| _ -> LBinOp (fe1, StrCat, fe2))) in
		result

	(* Internal String concat *)
	| LBinOp (le1, CharCat, le2) ->
		let fe1 = f le1 in 
		let fe2 = f le2 in
		let result = 
		(match fe1 with
		| LCList []
		| LLit (CList []) -> fe2
		| _ -> (match fe2 with
			| LCList []
			| LLit (CList []) -> fe1
			| _ -> LBinOp (fe1, CharCat, fe2))) in
		result

		
	(* Binary operators *)
	| LBinOp (e1, bop, e2) ->
		let re1 = f e1 in
		let re2 = f e2 in
		(match bop with
		| Plus ->
			(match re1, re2 with
			(* n1 +J n2 ---> n1 + n2 *) 
			| LLit (Num n1), LLit (Num n2) -> LLit (Num (n1 +. n2))
			| re1, LLit (Num 0.) -> re1
			| LLit (Num 0.), re2 -> re2
			(* (_ +J n1) +J n2 ---> _ +J (n1 + n2) *)
			| LBinOp (re1, Plus, LLit (Num n1)), LLit (Num n2) -> f (LBinOp (re1, Plus, LLit (Num (n1 +. n2))))
			(* (n1 +J _) +J n2 ---> _ +J (n1 + n2) *)
			| LBinOp (LLit (Num n1), Plus, re2), LLit (Num n2) -> f (LBinOp (re2, Plus, LLit (Num (n1 +. n2))))
			| _, _ -> LBinOp (re1, bop, re2)) 
		| Minus ->
			(match re1, re2 with
			(* n1 -J n2 ---> n1 - n2 *) 
			| LLit (Num n1), LLit (Num n2) -> LLit (Num (n1 -. n2))
			| LBinOp (re1, Plus, LLit (Num n1)), LLit (Num n2) -> f (LBinOp (re1, Plus, LLit (Num (n1 -. n2))))
			| LBinOp (LLit (Num n1), Plus, re2), LLit (Num n2) -> f (LBinOp (re2, Plus, LLit (Num (n1 -. n2))))
			| _, _ -> LBinOp (re1, bop, re2)) 
		| _ -> LBinOp (re1, bop, re2))

	(* TypeOf *)
	| LTypeOf e1 ->
		let re1 = f e1 in
			LTypeOf re1

	(* Logical lists *)
	| LEList le ->
		let rle = List.map (fun x -> f x) le in
		let all_literals = List.fold_left
			(fun ac x -> ac && (match x with
			  | LLit _ -> true
			  | _ -> false)) true rle in
		if all_literals then
			LLit (LList (List.map (fun x -> (match x with
			  | LLit lit -> lit
			  | _ -> raise (Failure "List literal nonsense. This cannot happen."))) rle))
		else (LEList rle)

	(* List nth *)
	| LLstNth (e1, e2) ->
		let list = f e1 in
		let new_list = find_me_Im_a_list store pfs list in 
		let index = f e2 in
		(match list, index with
		| LLit (LList list), LLit (Num n) ->
			if (Utils.is_int n) then
			(try (LLit (List.nth list (int_of_float n))) with _ ->
					raise (Failure "List index out of bounds"))
			else
					raise (Failure (Printf.sprintf "Non-integer list index: %f" n))

		| LEList list, LLit (Num n) ->
			if (Utils.is_int n) then
			(try (List.nth list (int_of_float n)) with _ ->
					raise (Failure "List index out of bounds"))
			else
					raise (Failure (Printf.sprintf "Non-integer list index: %f" n))

		| LBinOp (le, LstCons, list), LLit (Num n) ->
			print_debug_petar (Printf.sprintf "Cons: %s %s %f" (string_of_logic_expression le) (string_of_logic_expression list) n);
			if (Utils.is_int n) then
		  let ni = int_of_float n in
			 (match (ni = 0) with
		   | true -> print_debug_petar (Printf.sprintf "ni = 0, calling recursively with %s" (string_of_logic_expression le)); f le
		   | false -> f (LLstNth (f list, LLit (Num (n -. 1.)))))
			else
					raise (Failure (Printf.sprintf "Non-integer list index: %f" n))

		| _, _ -> LLstNth (list, index))

	(* String nth *)
	| LStrNth (e1, e2) ->
		let str = f e1 in
		let index = f e2 in
		(match str, index with
		| LLit (String str), LLit (Num n) ->
			if (Utils.is_int n) then
			(try (LLit (String (String.sub str (int_of_float n) 1))) with _ ->
				raise (Failure "List index out of bounds"))
			else
				raise (Failure (Printf.sprintf "Non-integer string index: %f" n))
		| LLit (CList str), LLit (Num n) ->
			if (Utils.is_int n) then
			(try 
				let char = (List.nth str (int_of_float n)) in 
				(match char with
				| Char c -> LLit (String (String.make 1 c))
				| _ -> raise (Failure ("Unexpected construct in internal string representation"))) with _ ->
				raise (Failure "List index out of bounds"))
			else
				raise (Failure (Printf.sprintf "Non-integer string index: %f" n))
		| _, _ -> LStrNth (str, index))

    (* List and String length *)
	| LUnOp (op, e1) ->
		let re1 = f e1 in
		(match op with
		 | LstLen -> (match re1 with
				| LLit (LList list) -> (LLit (Num (float_of_int (List.length list))))
		    | LEList list -> (LLit (Num (float_of_int (List.length list))))
  			| LBinOp (le, LstCons, list) ->
  				let rlist = f (LUnOp (LstLen, list)) in
  				(match rlist with
  				| LLit (Num n) -> LLit (Num (n +. 1.))
  				| _ -> LBinOp (LLit (Num 1.), Plus, rlist))
				| LBinOp (l1, LstCat, l2) ->
						LBinOp (f (LUnOp (op, l1)), Plus, f (LUnOp (op, l2)))
  			| _ -> LUnOp (LstLen, e1))
		 | StrLen -> (match re1 with
		    | LLit (String str) -> (LLit (Num (float_of_int (String.length str))))
		    | _ -> LUnOp (StrLen, e1))
		 | _ -> LUnOp (op, re1))

	(* Everything else *)
	| _ -> e) in
	if (result <> orig_expr) then (print_debug_petar (Printf.sprintf "Reduce expression: %s ---> %s"
		(JSIL_Print.string_of_logic_expression e) 
		(JSIL_Print.string_of_logic_expression result)));
	result

let reduce_expression_no_store_no_gamma_no_pfs = reduce_expression (Hashtbl.create 1) (Hashtbl.create 1) (DynArray.create ())
let reduce_expression_no_store_no_gamma        = reduce_expression (Hashtbl.create 1) (Hashtbl.create 1)
let reduce_expression_no_store                 = reduce_expression (Hashtbl.create 1)

(* Reduction of assertions *)
let rec reduce_assertion store gamma pfs a =
	let f = reduce_assertion store gamma pfs in
	let fe = reduce_expression store gamma pfs in
	let result = (match a with
	| LAnd (LFalse, _)
	| LAnd (_, LFalse) -> LFalse
	| LAnd (LTrue, a1)
	| LAnd (a1, LTrue) -> f a1
	| LAnd (a1, a2) ->
		let ra1 = f a1 in
		let ra2 = f a2 in
		let a' = LAnd (ra1, ra2) in
		if ((ra1 = a1) && (ra2 = a2))
			then a' else f a'

	| LOr (LTrue, _)
	| LOr (_, LTrue) -> LTrue
	| LOr (LFalse, a1)
	| LOr (a1, LFalse) -> f a1
	| LOr (LAnd (a1, a2), a3) ->
			f (LAnd (LOr (a1, a3), LOr (a2, a3))) 
	(* | LOr (LNot (LEq (LVar x, e1)), a) ->
			let subst = Hashtbl.create 1 in
			Hashtbl.add subst x e1;
			let a = asrt_substitution subst true a in
				f a *)
	| LOr (LOr (a1, a2), a3) -> 
			f (LOr (a1, LOr (a2, a3)))
	| LOr (a1, a2) ->
		let ra1 = f a1 in
		let ra2 = f a2 in
		let a' = LOr (ra1, ra2) in
		if ((ra1 = a1) && (ra2 = a2))
			then a' else f a'

	| LNot LTrue -> LFalse
	| LNot LFalse -> LTrue
	| LNot (LNot a) -> f a
	| LNot (LOr (al, ar)) ->
			f (LAnd (LNot al, LNot ar))
	| LNot (LAnd (al, ar)) -> 
			f (LOr (LNot al, LNot ar))
	| LNot a1 ->
		let ra1 = f a1 in
		let a' = LNot ra1 in
		if (ra1 = a1)
			then a' else f a'

	| LStar (LFalse, _)
	| LStar (_, LFalse) -> LFalse
	| LStar (LTrue, a1)
	| LStar (a1, LTrue) -> f a1
	| LStar (a1, a2) ->
		let ra1 = f a1 in
		let ra2 = f a2 in
		let a' = LStar (ra1, ra2) in
		if ((ra1 = a1) && (ra2 = a2))
			then a' else f a'

	| LEq (e1, e2) ->
		let re1 = fe e1 in
		let re2 = fe e2 in
		(* Warning - NaNs, infinities, this and that, this is not good enough *)
		let eq = (re1 = re2) in
		if eq then LTrue
		else
		let ite a b = if (a = b) then LTrue else LFalse in
		let default e1 e2 re1 re2 = 
			let a' = LEq (re1, re2) in
				if ((re1 = e1) && (re2 = e2))
					then a' else f a' in
		(match e1, e2 with

			(* The alocs *)
			| ALoc al1, ALoc al2 -> ite al1 al2

			(* The empty business *)
			| _, LLit Empty -> (match e1 with
				| LLit l when (l <> Empty) -> LFalse
				
				| LEList _
				| LBinOp _ 
				| LUnOp _ -> LFalse
				
				| _ -> default e1 e2 re1 re2)

			| LLit l1, LLit l2 -> ite l1 l2
			| LNone, PVar x
			| PVar x, LNone
			| LNone, LVar x
			| LVar x, LNone -> 
				if (Hashtbl.mem gamma x) 
					then (let tx = Hashtbl.find gamma x in 
						if tx = NoneType then default e1 e2 re1 re2 else LFalse)
					else default e1 e2 re1 re2
			| LNone, e
			| e, LNone -> LFalse

			(* Abstract and concrete locations, bye bye *)
			| ALoc _, LLit (Loc _) 
			| LLit (Loc _), ALoc _ -> LFalse
			
			| LLit (String str), LVar x 
			| LVar x, LLit (String str) ->
				(* Specific string hack:
				      if we have a string starting with @, and also 
				      that the var-string doesn't start with @, we know it's false *)
				if (str <> "" && String.get str 0 = '@') 
					then
						let pfs = DynArray.to_list pfs in 
						if ((List.mem (LNot (LEq (LStrNth (LVar x, LLit (Num 0.)), LLit (String "@")))) pfs)  ||
							 (List.mem (LNot (LEq (LLit (String "@"), LStrNth (LVar x, LLit (Num 0.))))) pfs))
						then LFalse 
						else default e1 e2 re1 re2
					else default e1 e2 re1 re2

			| LLit (CList cl), LVar x
			| LVar x, LLit (CList cl) ->
				(* Same String hack as above, except over the internal String representation *)
				if (List.length cl <> 0 && List.hd cl = Char '@')
					then
						let pfs = DynArray.to_list pfs in
						if ((List.mem (LNot (LEq (LStrNth (LVar x, LLit (Num 0.)), LLit (CList ([Char '@']))))) pfs)  ||
							 (List.mem (LNot (LEq (LLit (CList ([Char '@'])), LStrNth (LVar x, LLit (Num 0.))))) pfs))
						then LFalse 
						else default e1 e2 re1 re2
					else default e1 e2 re1 re2

			| LLit (Bool true), LBinOp (e1, LessThan, e2) -> LLess (e1, e2)
			| LLit (Bool false), LBinOp (e1, LessThan, e2) -> LNot (LLess (e1, e2))

			(* Plus theory *)
			| LBinOp (re1', Plus, LLit (Num n1)), LBinOp (re2', Plus, LLit (Num n2))
			| LBinOp (re1', Plus, LLit (Num n1)), LBinOp (LLit (Num n2), Plus, re2')
			| LBinOp (LLit (Num n1), Plus, re1'), LBinOp (re2', Plus, LLit (Num n2))
			| LBinOp (LLit (Num n1), Plus, re1'), LBinOp (LLit (Num n2), Plus, re2') ->
					print_debug_petar "PLUS_ON_BOTH_SIDES";
					let isn1 = Utils.is_normal n1 in
					let isn2 = Utils.is_normal n2 in
					if (isn1 && isn2)
						then (
							if (n1 < n2) then f (LEq (re1', LBinOp (re2', Plus, LLit (Num (n2 -. n1))))) else
								if (n1 = n2) then f (LEq (re1', re2')) else
									f (LEq (LBinOp (re1', Plus, LLit (Num (n1 -. n2))), re2'))
						)
						else default e1 e2 re1 re2
						
			(* More Plus theory *)
			| LBinOp (re1', Plus, LLit (Num n1)), LLit (Num n2)
			| LLit (Num n2), LBinOp (re1', Plus, LLit (Num n1)) ->
					print_debug_petar "PLUS_ON_ONE, LIT_ON_OTHER";
					let isn1 = Utils.is_normal n1 in
					let isn2 = Utils.is_normal n2 in
					if (isn1 && isn2)
						then 
							f (LEq (re1', LLit (Num (n2 -. n1))))
						else default e1 e2 re1 re2

			(* Nil *)
			| LBinOp (l1, LstCat, l2), LLit (LList []) ->
				f (LAnd (LEq (l1, LLit (LList [])), LEq (l2, LLit (LList []))))

			(* Very special cases *)
			| LTypeOf (LBinOp (_, StrCat, _)), LLit (Type t) when (t <> StringType) -> LFalse
			| LTypeOf (LBinOp (_, SetMem, _)), LLit (Type t) when (t <> BooleanType) -> LFalse
			
			| _, _ -> default e1 e2 re1 re2
		)

	| LLess (e1, e2) ->
		let re1 = fe e1 in
		let re2 = fe e2 in
		(match re1, re2 with
		| LUnOp (LstLen, _), LLit (Num 0.) -> LFalse
		| LUnOp (LstLen, le), LLit (Num 1.) -> LEq (le, LEList [])
		| _ -> LLess (re1, re2))

	| LSetMem (leb, LSetUnion lle) -> 
		let rleb = fe leb in
		let formula = (match lle with
		| [] -> LFalse
		| le :: lle -> 
				let rle = fe le in
					List.fold_left (fun ac le -> 
						let rle = fe le in 
							LOr (ac, LSetMem (rleb, rle))
					) (LSetMem (rleb, rle)) lle) in
		let result = f formula in
			print_debug_petar (Printf.sprintf "SIMPL_SETMEM_UNION: from %s to %s" (JSIL_Print.string_of_logic_assertion a) (JSIL_Print.string_of_logic_assertion result)); 
			result

	| LSetMem (leb, LSetInter lle) -> 
		let rleb = fe leb in
		let formula = (match lle with
		| [] -> LFalse
		| le :: lle -> 
				let rle = fe le in
					List.fold_left (fun ac le -> 
						let rle = fe le in 
							LAnd (ac, LSetMem (rleb, rle))
					) (LSetMem (rleb, rle)) lle) in
		let result = f formula in
			print_debug_petar (Printf.sprintf "SIMPL_SETMEM_INTER: from %s to %s" (JSIL_Print.string_of_logic_assertion a) (JSIL_Print.string_of_logic_assertion result)); 
			result

	| LSetMem (leb, LBinOp(lel, SetDiff, ler)) -> 
		let rleb = fe leb in
		let rlel = fe lel in
		let rler = fe ler in
		let result = f (LAnd (LSetMem (rleb, rlel), LNot (LSetMem (rleb, rler)))) in
			print_debug_petar (Printf.sprintf "SIMPL_SETMEM_DIFF: from %s to %s" (JSIL_Print.string_of_logic_assertion a) (JSIL_Print.string_of_logic_assertion result)); 
			result
			
	| LSetMem (leb, LESet les) -> 
		let rleb = fe leb in
		let rles = List.map (fun le -> fe le) les in
		let result = List.map (fun le -> LEq (rleb, le)) rles in
		let result = List.fold_left (fun ac eq ->
			(match ac with
			| LFalse -> eq
			| _ -> LOr (ac, eq))) LFalse result in  
			print_debug_petar (Printf.sprintf "SET_MEM: from %s to %s" (JSIL_Print.string_of_logic_assertion a) 
				(JSIL_Print.string_of_logic_assertion result)); 
			f result

	| LForAll (bt, a) -> 
			let ra = f a in
			let vars = get_asrt_lvars a in
			let bt = List.filter (fun (b, _) -> SS.mem b vars) bt in
			(match bt with
			| [] -> ra
			| _ -> LForAll (bt, ra))

	| _ -> a) in
	(* print_debug (Printf.sprintf "Reduce assertion: %s ---> %s"
		(JSIL_Print.string_of_logic_assertion a false)
		(JSIL_Print.string_of_logic_assertion result false)); *)
	result

let reduce_assertion_no_store_no_gamma_no_pfs = reduce_assertion (Hashtbl.create 1) (Hashtbl.create 1) (DynArray.create ())
let reduce_assertion_no_store_no_gamma        = reduce_assertion (Hashtbl.create 1) (Hashtbl.create 1)
let reduce_assertion_no_store                 = reduce_assertion (Hashtbl.create 1)

let rec lexpr_substitution (subst : substitution) (partial : bool) (le : jsil_logic_expr) : jsil_logic_expr =
	
	let f = lexpr_substitution subst partial in 

	let find_in_subst (x : string) (le_x_old : jsil_logic_expr) 
			(make_new_x : unit -> jsil_logic_expr) : jsil_logic_expr = 
		try Hashtbl.find subst x with _ -> 
			if partial then le_x_old else (
				let new_le_x = make_new_x () in 
				Hashtbl.replace subst x new_le_x;
				new_le_x) in  

	let f_before le = (match le with 
		| LVar x    -> find_in_subst x le (fun () -> LVar (fresh_lvar ())), false 
		| ALoc x    -> find_in_subst x le (fun () -> ALoc (fresh_aloc ())), false
		| PVar x    -> find_in_subst x le (fun () ->
				let pvar = fresh_pvar () in
				print_debug_petar (Printf.sprintf "Unable to find PVar %s in subst, generating fresh: %s" x pvar); 
				PVar (fresh_pvar ())), false 
		| _         -> le, true) in 

	let result = logic_expression_map f_before None le in
	if (le = result) then result else
		reduce_expression_no_store_no_gamma_no_pfs result 		

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
				| _     -> raise (Failure "ERROR"))
			| true ->
			(match op with
			| Equal -> check_valid_type t1 all_types BooleanType []
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
			| _ -> raise (Failure "ERROR in type_lexpr")))
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
			(* Printf.printf "Horror: op: %s, t: %s"  (JSIL_Print.string_of_binop op) (JSIL_Print.string_of_type le_type); *)
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
	| UnOp (op, e)        -> LUnOp (op, f e)
	| TypeOf e            -> LTypeOf (f e)
	| EList es            -> LEList (List.map f es)
	| LstNth (e1, e2)     -> LLstNth (f e1, f e2)
	| StrNth (e1, e2)     -> LStrNth (f e1, f e2)
	| _  ->
		let msg = Printf.sprintf "DEATH. expr_2_lexpr. e: %s" (JSIL_Print.string_of_expression e) in 
		raise (Failure msg)


let rec lift_lit_list_to_logical_expr (lit : jsil_lit) : jsil_logic_expr =
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