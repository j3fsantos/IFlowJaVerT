open DynArray
open Set
open Stack
open JSIL_Syntax

(* What does it mean to be a list? *)
let rec isList (le : jsil_logic_expr) : bool =
(match le with
	| LVar _ 
	| LLit (LList _)
	| LEList _ -> true
	| LBinOp (_, LstCons, le) -> isList le
	| LBinOp (lel, LstCat, ler) -> isList lel && isList ler
	| _ -> false)

(************)
(* Monadics *)
(************)

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

(********)
(* Rest *)
(********)

let get_string_hashtbl_keys ht =
	Hashtbl.fold
		(fun key _ ac -> key :: ac)
		ht
		[]

(** !tbl_left /\ tbl_right **)
let tbl_intersection_false_true tbl_left tbl_right =
	Hashtbl.fold
		(fun var _ ac ->
			if (not (Hashtbl.mem tbl_left var))
				then var :: ac
				else ac)
		tbl_right
		[]



let small_tbl_size = 31

let print_var_list var_list =
	List.fold_left
		(fun ac var -> if (ac = "") then var else ac ^ "; " ^ var)
		""
		var_list

(** Apply function f to a logic expression, recursively when f returns (new_expr, true). *)
let rec logic_expression_map f lexpr =
	(* Apply the mapping *)
	let map_e = logic_expression_map f in
	let (mapped_lexpr, recurse) = f lexpr in
	if not recurse then
		mapped_lexpr
	else
  	(* Map recursively to expressions *)
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
  	| LStrNth (e1, e2)    -> LStrNth (map_e e1, map_e e2)


(** Apply function f to the logic expressions in an assertion, recursively when it makes sense. *)
let rec assertion_map f_a f_e asrt = 
	(* Map recursively to assertions and expressions *)
	let map_a = assertion_map f_a f_e in
	let map_e = logic_expression_map f_e in
	let a' = 
		match asrt with
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
	let f_a = Option.default (fun x -> x) f_a in
	f_a a' 
	

let rec logic_expression_fold f_ac f_state state lexpr =

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
	

let rec assertion_fold feo f_ac f_state state asrt =
	let new_state = (Option.default (fun le x -> x) f_state) asrt state in 
	let fold_a    = assertion_fold feo f_ac f_state new_state in 
	let f_ac      = f_ac asrt new_state state in 
	let fes les   = Option.map_default (fun fe -> List.map fe les) [] feo in 

	match asrt with
	| LTrue | LFalse | LEmp | LTypes _  -> f_ac [] 
	
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


let get_list_exprs (a : jsil_logic_assertion) : jsil_logic_expr list = 
	
	let fe_ac le _ _ ac = 
		match le with 
		| LLit (LList _) | LEList _   | LBinOp (_, LstCons, _) 
		| LBinOp (_, LstCat, _) | LUnOp (Car, _) | LUnOp (Cdr, _) 
		| LUnOp (LstLen, _) -> le :: (List.concat ac)
		| _ -> List.concat ac in 

	let fe = logic_expression_fold fe_ac None None in
	let f_ac a _ _ ac = List.concat ac in 
	assertion_fold (Some fe) f_ac None None a




let rec get_logic_expression_literals le =
	let fe = get_logic_expression_literals in
	match le with
	| LLit (LList ls) ->
		let ls = List.map (fun x -> LLit x) ls in
			List.concat (List.map fe ls)
	| LLit lit -> [ lit ]
	| LNone | LVar _ | ALoc _ | PVar _ -> []
	| LBinOp (le1, _, le2) | LLstNth (le1, le2) | LStrNth (le1, le2)  -> (fe le1) @ (fe le2)
	| LUnOp (_, le) |	LTypeOf le -> fe le
	| LCList    les
 	| LEList    les 
	| LESet     les 
	| LSetUnion les
	| LSetInter les -> List.concat (List.map fe les)

let rec get_assertion_literals a =
	let f = get_assertion_literals in
	let fe = get_logic_expression_literals in
	match a with
	| LTrue | LFalse | LEmp | LTypes _ -> []
	| LNot a | LForAll (_, a) -> f a
	| LAnd (a1, a2) | LOr (a1, a2) | LStar (a1, a2) -> (f a1) @ (f a2)
	| LPointsTo (le1, le2, le3) -> (fe le1) @ (fe le2) @ (fe le3)
	| LEq (le1, le2) | LLess (le1, le2) | LLessEq (le1, le2) | LStrLess (le1, le2) 
	| LSetMem (le1, le2) | LSetSub (le1, le2) -> (fe le1) @ (fe le2)
	| LPred (_, les) -> List.concat (List.map fe les)
	| LEmptyFields (e, domain) -> (fe e) @ (fe domain)
	

let rec get_logic_expression_lists le =
	let fe = get_logic_expression_lists in
	match le with
	| LLit (LList ls) -> [ (LEList (List.map (fun x -> LLit x) ls)) ]
	| LLit _ | LNone | LVar _ | ALoc _ | PVar _ -> []
	| LBinOp (le1, LstCons, le2) -> le :: ((fe le1) @ (fe le2))
	| LBinOp (le1, LstCat, le2)  -> le :: ((fe le1) @ (fe le2))
	| LBinOp (le1, _, le2) | LLstNth (le1, le2) | LStrNth (le1, le2)  -> (fe le1) @ (fe le2)
	| LUnOp (_, le) | LTypeOf le -> fe le
 	| LEList les -> (LEList les) :: (List.concat (List.map fe les))
	| LESet les 
	| LSetUnion les
	| LSetInter les -> (List.concat (List.map fe les))

let rec get_assertion_lists a =
	let f = get_assertion_lists in
	let fe = get_logic_expression_lists in
	match a with
	| LTrue | LFalse | LEmp | LTypes _ -> []
	| LNot a | LForAll (_, a) -> f a
	| LAnd (a1, a2) | LOr (a1, a2) | LStar (a1, a2) -> (f a1) @ (f a2)
	| LPointsTo (le1, le2, le3) -> (fe le1) @ (fe le2) @ (fe le3)
	| LEq (le1, le2) | LLess (le1, le2) | LLessEq (le1, le2) 
	| LStrLess (le1, le2) | LSetMem (le1, le2) | LSetSub (le1, le2) -> (fe le1) @ (fe le2)
	| LPred (_, les) -> List.concat (List.map fe les)
	| LEmptyFields (e, domain) -> (fe e) @ (fe domain)



let get_assertion_string_number_literals a =
	let lits = get_assertion_literals a in
	let rec loop lits_to_go (strings_so_far, numbers_so_far) =
		match lits_to_go with
		| [] ->  (strings_so_far, numbers_so_far)
		| (String s) :: rest -> loop rest (s :: strings_so_far, numbers_so_far)
		| (Num n) :: rest -> loop rest (strings_so_far,  n :: numbers_so_far)
		| _ :: rest -> loop rest (strings_so_far, numbers_so_far) in
	loop lits ([], [])

let rec get_logic_expression_lvars_list le =
	let fe = get_logic_expression_lvars_list in
		match le with
		| LLit _ | LNone | ALoc _ | PVar _ -> []
		| LVar x -> [ x ]
		| LBinOp (le1, _, le2) | LLstNth (le1, le2) | LStrNth (le1, le2) -> (fe le1) @ (fe le2)
		| LUnOp (_, le) |	LTypeOf le -> fe le
	 	| LEList    les 
		| LESet     les
		| LSetUnion les
		| LSetInter les
	 	| LCList les -> List.concat (List.map fe les)

let get_logic_expression_lvars le =
	SS.of_list (get_logic_expression_lvars_list le)

let get_assertion_lvars a : JSIL_Syntax.SS.t = 
	
	let rec get_assertion_lvars_list a =
		let f = get_assertion_lvars_list in
		let fe = get_logic_expression_lvars_list in
		match a with
		| LTrue | LFalse | LEmp | LTypes _ -> []
		| LNot a -> f a
		| LAnd (a1, a2) | LOr (a1, a2) | LStar (a1, a2) -> (f a1) @ (f a2)
		| LPointsTo (le1, le2, le3) -> (fe le1) @ (fe le2) @ (fe le3)
		| LEq (le1, le2) | LLess (le1, le2) | LLessEq (le1, le2) | LStrLess (le1, le2) -> (fe le1) @ (fe le2)
		| LPred (_, les) -> List.concat (List.map fe les)
		| LEmptyFields (e, domain) -> (fe e) @ (fe domain) in
		
	SS.of_list (get_assertion_lvars_list a)

let remove_string_duplicates strings =
	let string_set = SS.of_list strings in
	SS.elements string_set

let remove_number_duplicates numbers =
	let number_set = SN.of_list numbers in
	SN.elements number_set

let remove_int_duplicates ints =
	let int_set = SI.of_list ints in
	SI.elements int_set


let is_pure_assertion (a : jsil_logic_assertion) : bool =
	let f_ac a _ _ ac =
		match a with
		| LPred (_, _) | LPointsTo (_, _, _) | LEmp -> false
		| _ -> List.fold_left (fun ac v -> (ac && v)) true ac in
	assertion_fold None f_ac None None a 


let is_pure_atom (a : jsil_logic_assertion) : bool =
	match a with
	| LTrue | LFalse | LEq (_, _) | LLess (_, _) | LLessEq (_, _) | LStrLess (_, _) 
	| LSetMem (_, _) | LSetSub (_, _) | LForAll (_, _) -> true
	| _ -> false


let only_pure_atoms_negated a =
	let f_ac a _ _ ac =
		match a with
		| LAnd (_, _) | LOr (_, _) | LStar (_, _) | LForAll (_, _) -> List.fold_left (fun ac v -> (ac && v)) true ac
		| LNot a -> is_pure_atom a 
		| _      -> true in
	assertion_fold None f_ac None None a


let rec purify_stars a =
	let f = purify_stars in
	match a with
	| LTrue | LFalse | LEq (_,_) | LLess (_,_) | LLessEq (_, _) | LStrLess (_, _) | LPred (_, _) | LSetMem (_, _) | LSetSub (_, _) | LForAll (_, _) -> a, []
	| LTypes types -> LTrue, types
	| LAnd (a1, a2)  ->
		let new_a1, types_a1 = f a1 in
		let new_a2, types_a2 = f a2 in
		(LAnd (new_a1, new_a2)), (types_a1 @ types_a2)
	| LOr (a1, a2)   ->
		let new_a1, types_a1 = f a1 in
		let new_a2, types_a2 = f a2 in
		LOr ((new_a1, new_a2)), (types_a1 @ types_a2)
	| LStar (a1, a2) ->
		let new_a1, types_a1 = f a1 in
		let new_a2, types_a2 = f a2 in
		LAnd ((new_a1, new_a2)), (types_a1 @ types_a2)
	| LNot a1        ->
		let new_a1, types_a1 = f a1 in
		LNot new_a1, types_a1
	| LPointsTo (_, _, _) | LEmp -> raise (Failure "purify_stars with impure argument")


(**
  var_set is a set (NOT A HASHTABLE) that models the set of variables
*)
let rec get_expr_vars catch_pvars e : SS.t =
	let f = get_expr_vars catch_pvars in
	match e with
	| LLit _
	| ALoc _
	| LNone  -> SS.empty
	| LVar var -> 
			if (not catch_pvars)
				then SS.singleton var
				else SS.empty
	| PVar var ->
			if (catch_pvars)
				then SS.singleton var 
				else SS.empty
	| LUnOp (_, e1) -> f e1
	| LTypeOf e1 -> f e1
	| LEList le_list
	| LESet le_list
	| LSetUnion le_list
	| LSetInter le_list
	| LCList le_list -> 
			List.fold_left (fun ac e -> 
				let v_e = f e in
					SS.union ac v_e) SS.empty le_list	
	| LBinOp (e1, _, e2) 
	| LLstNth (e1, e2)
	| LStrNth (e1, e2) -> 
			let v_e1 = f e1 in
			let v_e2 = f e2 in
				SS.union v_e1 v_e2

let rec get_locs_expr e : SS.t =
	let f = get_locs_expr in
	match e with
	| ALoc l -> SS.singleton l
	| LLit _
	| ALoc _
	| LNone 
	| LVar _
	| PVar _ -> SS.empty
	| LUnOp (_, e1) -> f e1
	| LTypeOf e1 -> f e1
	| LEList le_list
	| LESet le_list
	| LSetUnion le_list
	| LSetInter le_list
	| LCList le_list -> 
			List.fold_left (fun ac e -> 
				let v_e = f e in
					SS.union ac v_e) SS.empty le_list	
	| LBinOp (e1, _, e2) 
	| LLstNth (e1, e2)
	| LStrNth (e1, e2) -> 
			let v_e1 = f e1 in
			let v_e2 = f e2 in
				SS.union v_e1 v_e2

let rec get_assertion_vars catch_pvars a : SS.t = 
	let f = get_assertion_vars catch_pvars in
	let fe = get_expr_vars catch_pvars in
	let result = (match a with
	| LTrue
	| LFalse 
	| LEmp -> SS.empty
	| LNot a1 -> f a1
	| LAnd (a1, a2) 
	| LOr (a1, a2)
	| LStar (a1, a2) -> 
			let v_a1 = f a1 in
			let v_a2 = f a2 in
			SS.union v_a1 v_a2
	| LEq (e1, e2)
	| LLess (e1, e2)
	| LLessEq (e1, e2)
	| LStrLess (e1, e2) -> 
			let v_e1 = fe e1 in
			let v_e2 = fe e2 in
			SS.union v_e1 v_e2
	| LPointsTo (e1, e2, e3) -> 
			let v_e1 = fe e1 in
			let v_e2 = fe e2 in
			let v_e3 = fe e3 in
			SS.union v_e1 (SS.union v_e2 v_e3)
	| LTypes vts -> List.fold_left 
			(fun ac (e, t) -> 
				let proceed, x, is_x_lvar = 
					(match e with 
					| LVar x_name -> true, x_name, true 
					| PVar x_name -> true, x_name, false 
					| le -> false, "", false) in 
				if (proceed && (((not catch_pvars) && is_x_lvar) || (catch_pvars &&  (not is_x_lvar)))) 
					then SS.add x ac
					else ac) SS.empty vts 
	| LPred (_, es) -> 
			List.fold_left (fun ac e -> 
				let v_e = fe e in
					SS.union ac v_e) SS.empty es
	| LEmptyFields (o, domain) -> 
			let v_o = fe o in
			let v_les = fe domain in
			SS.union v_o v_les
	| LSetMem (elem, s) -> SS.union (fe elem) (fe s)
	| LSetSub (s1, s2)  -> SS.union (fe s1) (fe s2) 
	(* CAREFUL, BINDERS *)
	| LForAll (bt, a1) -> 
			let v_a1 = f a1 in
			let binders, _ = List.split bt in
			SS.diff v_a1 (SS.of_list binders))
	in result

let get_assertion_list_vars assertions catch_pvars =
	List.fold_left (fun ac a ->
		let v_a = get_assertion_vars catch_pvars a in
		SS.union ac v_a) SS.empty assertions

let rec get_locs_assertion a : SS.t = 
	let f = get_locs_assertion in
	let fe = get_locs_expr in
	let result = (match a with
	| LTrue
	| LFalse 
	| LEmp 
	| LTypes _ 
	| LEmptyFields _ -> SS.empty
	| LNot a1 -> f a1
	| LAnd (a1, a2) 
	| LOr (a1, a2)
	| LStar (a1, a2) -> 
			let v_a1 = f a1 in
			let v_a2 = f a2 in
			SS.union v_a1 v_a2
	| LEq (e1, e2)
	| LLess (e1, e2)
	| LLessEq (e1, e2)
	| LStrLess (e1, e2) -> 
			let v_e1 = fe e1 in
			let v_e2 = fe e2 in
			SS.union v_e1 v_e2
	| LPointsTo (e1, e2, e3) -> 
			let v_e1 = fe e1 in
			let v_e2 = fe e2 in
			let v_e3 = fe e3 in
			SS.union v_e1 (SS.union v_e2 v_e3)
	| LPred (_, es) -> 
			List.fold_left (fun ac e -> 
				let v_e = fe e in
					SS.union ac v_e) SS.empty es
	| LSetMem (elem, s) -> SS.union (fe elem) (fe s)
	| LSetSub (s1, s2)  -> SS.union (fe s1) (fe s2) 
	(* CAREFUL, BINDERS *)
	| LForAll (_, a1) -> 
			f a1)
	in result

(* *********************************** *)

let get_subtraction_vars_old assertions_left assertions_right catch_pvars =
	let v_l = get_assertion_list_vars assertions_left catch_pvars in
	let v_r = get_assertion_list_vars assertions_right catch_pvars in
		SS.diff v_l v_r

let get_subtraction_vars vars subst =
	SS.filter (fun x -> not (Hashtbl.mem subst x)) vars

let get_vars_le_list catch_pvars le_list =
	List.fold_left (fun ac e ->
		let v_e = get_expr_vars catch_pvars e in
		SS.union ac v_e) SS.empty le_list

let get_subtraction_vars_lexpr lexpr_left lexpr_right catch_pvars =
	let v_l = get_expr_vars lexpr_left catch_pvars in
	let v_r = get_expr_vars lexpr_right catch_pvars in
		SS.diff v_l v_r
		

let rec push_in_negations_off a : jsil_logic_assertion =
	let err_msg = "push_in_negations_off: internal error" in
	let f_off = push_in_negations_off in
	let f_on = push_in_negations_on in
	(match a with
	| LAnd (a1, a2)  -> LAnd ((f_off a1), (f_off a2))
	| LOr (a1, a2)   -> LOr ((f_off a1), (f_off a2))
	| LNot a1        ->
		let new_a1, types_a1 = purify_stars a1 in
		if ((List.length types_a1) > 0)
			then LStar (f_on (new_a1), LTypes types_a1)
			else f_on new_a1
	| LStar (a1, a2) -> LStar ((f_off a1), (f_off a2))
	| LForAll (bt, a) -> LForAll (bt, f_off a)
	| LTrue        | LFalse | LEq (_, _)          | LLess (_, _) | LLessEq (_, _) | LStrLess (_, _) | LSetMem (_, _) | LSetSub (_, _) 
	| LPred (_, _) | LEmp   | LPointsTo (_, _, _) | LTypes _ | LEmptyFields _ -> a)
and push_in_negations_on a =
	let err_msg = "push_in_negations_on: internal error" in
	let f_off = push_in_negations_off in
	let f_on = push_in_negations_on in
	(match a with
	|	LAnd (a1, a2)       -> LOr ((f_on a1), (f_on a2))
	| LOr (a1, a2)        -> LAnd ((f_on a1), (f_on a2))
	| LTrue               -> LFalse
	| LFalse              -> LTrue
	| LNot a              -> (f_off a)
	| LEq (_, _)   | LLess (_, _) | LLessEq (_, _) | LStrLess (_, _) | LPred (_, _) |  LSetMem (_, _) | LSetSub (_, _) | LForAll (_, _) -> LNot a
	| LStar (_, _) | LEmp         | LPointsTo (_, _, _) | LEmptyFields _ | LSetMem (_, _) | LSetSub (_, _) -> raise (Failure err_msg)
	| LTypes _            -> LTrue)





(**
  point-wise union composed with cross-product
	CP((L11::L12::L13), (L21::L22)) = ((L11 U L21)::(L11 U L22)::(L12 U L21)::(L12 U L22)::(L13 U L21)::(L13 U L22))
*)

let cross_product or_list1 or_list2 =
	let rec loop1 or_list1 or_list2 ac_list =
		let rec loop2 and_list1 or_list2 ac_list =
			(match or_list2 with
			| [] -> ac_list
			| and_list2 :: rest_or_list2 ->
				loop2 and_list1 rest_or_list2 ((List.append and_list1 and_list2) :: ac_list)) in
		match or_list1 with
		| [] -> ac_list
		| and_list1 :: rest_or_list1 ->
			loop1 rest_or_list1 or_list2 (loop2 and_list1 or_list2 ac_list) in
	loop1 or_list1 or_list2 []

let rec build_disjunt_normal_form a =
	let f = build_disjunt_normal_form in
	let err_msg = "build_disjunt_normal_form: Internal Error" in
	match a with
	| LAnd (a1, a2)
	| LStar (a1, a2)                               -> cross_product (f a1) (f a2)
	| LOr (a1, a2)                                 -> List.append (f a1) (f a2)
	| LTrue                                        -> []
	| LFalse           | LTypes _    | LEmptyFields _
	| LEq (_, _)       | LNot (LEq (_, _))
	| LLess (_, _)     | LNot (LLess (_, _))
	| LLessEq (_, _)   | LNot (LLessEq (_, _))
	| LStrLess (_, _)  | LNot (LStrLess (_, _))
	| LPred (_, _)     | LNot (LPred (_, _))
	| LEmp             | LPointsTo (_, _, _)       -> [[ a ]]
	| _ -> raise (Failure err_msg)


let remove_falses a_dnf =
	let contains_false list =
		List.fold_left
			(fun ac ele -> if (ele = LFalse) then true else ac)
			false
			list in
	let rec loop conjuncts processed_conjuncts =
		match conjuncts with
		| [] -> processed_conjuncts
		| conjunct :: rest_conjuncts ->
			if (contains_false conjunct)
				then (loop rest_conjuncts processed_conjuncts)
				else (loop rest_conjuncts (conjunct :: processed_conjuncts)) in
	loop a_dnf []

let assertion_list_from_dnf c_list =
	let rec loop c_list assertions =
		(match c_list with
		| [] -> assertions
		| conjunct :: rest_c_list ->
			let assertion =
				List.fold_left
					(fun ac atom ->
						(if (ac = LEmp)
							then atom
							else LStar (ac, atom)))
					LEmp
					conjunct in
			loop rest_c_list (assertion :: assertions)) in
	loop c_list []


let normalize_pure_assertion a =
	let a = push_in_negations_off a in
	let a = build_disjunt_normal_form a in
	remove_falses a

let old_pre_normalize_assertion a =
	(* Printf.printf "I am inside the pre_normalize being HAPPY. Looking at the assertion: %s!!!!\n"
		(JSIL_Print.string_of_logic_assertion a false); *)
	let f asrts =
		List.fold_left
			(fun ac asrt ->
				let asrt_str = (JSIL_Print.string_of_logic_assertion asrt false) in
				if (ac = "")
					then asrt_str
					else (ac ^ ";\n" ^ asrt_str))
			""
			asrts in
	if (only_pure_atoms_negated a)
		then [ a ]
		else
			begin
				(* Printf.printf "there are non-pure atoms negated!!!!\n"; *)
				let a = push_in_negations_off a in
				let dnf_a = build_disjunt_normal_form a in
				let dnf_a = remove_falses dnf_a in
				let new_as = assertion_list_from_dnf dnf_a in
				(* Printf.printf "Original a: %s.\nAfter prenormalisation:\n%s\n" (JSIL_Print.string_of_logic_assertion a false) (f new_as); *)
				new_as
			end


let pre_normalise_assertion a : jsil_logic_assertion =
	(match (only_pure_atoms_negated a) with
	| true -> a
	| false -> push_in_negations_off a)


let rec lexpr_substitution lexpr subst partial =
	let f e = lexpr_substitution e subst partial in
	match lexpr with
	| LLit lit -> LLit lit

	| LNone -> LNone

	| LVar var ->
			(try Hashtbl.find subst var with _ ->
				if (not partial)
					then
						let new_var = fresh_lvar () in
						Hashtbl.replace subst var (LVar new_var);
						LVar new_var
					else (LVar var))

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

let rec lexpr_selective_substitution lexpr subst partial =
	let f e = lexpr_selective_substitution e subst partial in
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

let rec assertion_substitution a subst partial =
	let fa a = assertion_substitution a subst partial in
	let fe e = lexpr_substitution e subst partial in
	match a with
	| LAnd (a1, a2) -> LAnd ((fa a1), (fa a2))
	| LOr (a1, a2) -> LOr ((fa a1), (fa a2))
	| LNot a -> LNot (fa a)
	| LTrue -> LTrue
	| LFalse -> LFalse
	| LEq (e1, e2) -> LEq ((fe e1), (fe e2))
	| LLess (e1, e2) -> LLess ((fe e1), (fe e2))
	| LLessEq (e1, e2) -> LLessEq ((fe e1), (fe e2))
	| LStrLess (e1, e2) -> LStrLess ((fe e1), (fe e2))
	| LStar (a1, a2) -> LStar ((fa a1), (fa a2))
	| LPointsTo (e1, e2, e3) -> LPointsTo ((fe e1), (fe e2), (fe e3))
	| LEmp -> LEmp
	| LPred (p_name, args) ->
		let s_args = List.map fe args in
		LPred (p_name, s_args)
	| LTypes types ->
		let s_types = List.map (fun (le, te) -> ((fe le), te)) types in
		LTypes s_types
	| LEmptyFields (obj, lstr) -> LEmptyFields (fe obj, fe lstr)
	| LStrLess (e1, e2) -> LStrLess ((fe e1), (fe e2))
	| LStar (a1, a2) -> LStar ((fa a1), (fa a2))
	| LSetMem (e1, e2) -> LSetMem ((fe e1), (fe e2))
	| LSetSub (e1, e2) -> LSetSub ((fe e1), (fe e2))
	| LForAll (bt, a) -> 
			let binders, _ = List.split bt in
			let old_binders_substs = 
				List.fold_left 
					(fun ac v -> 
						if (Hashtbl.mem subst v) 
							then ((v, Hashtbl.find subst v) :: ac)
							else ac )
					[]
					binders in 
			List.iter (fun v -> Hashtbl.add subst v (LVar v)) binders;
			let new_a = assertion_substitution a subst partial in 
			List.iter (fun (v, old_le_v) -> Hashtbl.replace subst v old_le_v) old_binders_substs;
			LForAll (bt, new_a)


(* DO CAPTURE AVOIDING *)

let get_subst_vars (subst : substitution) (filter : string -> bool) = 
	(Hashtbl.fold 
		(fun x le filtered_vars -> 
			if (filter x) 
				then filtered_vars 
				else SS.add x filtered_vars)
		subst
		SS.empty)

let filter_substitution (subst : substitution) (vars : SS.t) =
	let new_subst = Hashtbl.copy subst in
	Hashtbl.filter_map_inplace (fun v le ->
		match (SS.mem v vars) with
		| true -> Some le
		| false -> None) new_subst;
	new_subst

let filter_substitution_fun (subst : substitution) (filter : string -> bool)  =
	let new_subst = Hashtbl.copy subst in
	Hashtbl.filter_map_inplace (fun v le ->
		match (filter v) with
		| true -> Some le
		| false -> None) new_subst;
	new_subst


let init_substitution vars =
	let new_subst = Hashtbl.create 31 in
	List.iter
		(fun var -> Hashtbl.replace new_subst var (LVar var))
		vars;
	new_subst

let init_substitution2 vars les =
	let subst = Hashtbl.create 1021 in

	let rec loop vars les =
		match vars, les with
		| [], _
		| _, [] -> ()
		| var :: rest_vars, le :: rest_les ->
			Hashtbl.replace subst var le; loop rest_vars rest_les in

	loop vars les;
	subst

let init_substitution3 vars_les =
	let subst = Hashtbl.create 1021 in

	let rec loop vars_les =
		match vars_les with
		| [] -> ()
		| (var, le) :: rest ->
			Hashtbl.replace subst var le; loop rest in

	loop vars_les;
	subst





(**
 subst1 after subst2
**)
let compose_partial_substitutions subst1 subst2 =
	let subst = Hashtbl.create small_tbl_size in
	Hashtbl.iter
		(fun var le ->
			let n_le = lexpr_substitution le subst1 true in
			Hashtbl.add subst var n_le)
		subst2;
	subst


let copy_substitution subst = Hashtbl.copy subst

let extend_subst subst var v =
	Hashtbl.replace subst var v

let extend_substitution subst vars les =
	List.iter2
		(fun v le -> Hashtbl.replace subst v le)
		vars
		les

let filter_vars vars ignore_vars : SS.t =
	SS.diff vars ignore_vars

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
	let new_gamma : typing_environment = mk_gamma () in
	let ret = reverse_type_lexpr_aux gamma new_gamma le le_type in
	if (ret)
		then Some new_gamma
		else None


let is_sensible_subst subst gamma_source gamma_target =
  try
	Hashtbl.iter
		(fun var lexpr ->
			let lexpr_type, _, _ = type_lexpr gamma_target lexpr in
			let var_type = gamma_get_type gamma_source var in
			(match lexpr_type, var_type with
			| Some le_type, Some v_type ->
			  if (le_type = v_type) then () else raise (Failure (Printf.sprintf "Type mismatch: %s %s"
			  	(JSIL_Print.string_of_type le_type) (JSIL_Print.string_of_type v_type)))
			| _, _ -> ()))
		subst;
	true
	with (Failure msg) -> print_normal (Printf.sprintf "is_sensible_subst threw an exception: %s" msg); false


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
		| ((None    , _), (Some   _, _)) -> raise (Failure (err_msg ^ " : LEFT : " ^ (Printf.sprintf "%s" (JSIL_Print.string_of_logic_expression le1 false)) ^ " : right : " ^ (Printf.sprintf "%s" (JSIL_Print.string_of_logic_expression le2 false))))
		| ((Some   _, _), (None    , _)) -> raise (Failure (err_msg ^ " : left : " ^ (Printf.sprintf "%s" (JSIL_Print.string_of_logic_expression le1 false)) ^ " : RIGHT : " ^ (Printf.sprintf "%s" (JSIL_Print.string_of_logic_expression le2 false))))
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


let make_all_different_pure_assertion fv_list_1 fv_list_2 : jsil_logic_assertion list =

	let sle e = JSIL_Print.string_of_logic_expression e false in
	
	let rec all_different_field_against_fv_list f v fv_list pfs : jsil_logic_assertion list =
		match fv_list with
		| [] -> pfs
		| (f', v') :: rest ->
			(match f, f' with
			| LLit _, LLit _ -> all_different_field_against_fv_list f v rest pfs
			| _, _ -> 
				print_debug_petar (Printf.sprintf "all_different: (%s, %s) (%s, %s)\n" (sle f) (sle v) (sle f') (sle v'));
				all_different_field_against_fv_list f v rest ((LNot (LEq (f, f'))) :: pfs)) in

	let rec all_different_fv_list_against_fv_list fv_list_1 fv_list_2 pfs : jsil_logic_assertion list =
		(match fv_list_1 with
		| [] -> pfs
		| (f, v) :: rest ->
			let new_pfs = all_different_field_against_fv_list f v fv_list_2 pfs in
			all_different_fv_list_against_fv_list rest fv_list_2 new_pfs) in

	all_different_fv_list_against_fv_list fv_list_1 fv_list_2 []

let star_asses asses =
	List.fold_left
		(fun ac a ->
			if (not (a = LEmp))
				then (if (ac = LEmp) then a else LStar (a, ac))
				else ac)
		 LEmp
		asses


let generate_all_pairs (les : jsil_logic_expr list) : (jsil_logic_expr * jsil_logic_expr) list = 
	let cross_product lst1 lst2 = List.concat (List.map (fun elem -> List.map (fun e -> (elem, e)) lst2) lst1) in
	cross_product les les   


let concretise (a : jsil_logic_assertion) (x: string) (les : jsil_logic_expr list) : jsil_logic_assertion list = 
	List.map 
		(fun le -> 
			let subst = init_substitution2 [ x ] [ le ] in 
			assertion_substitution a subst true)
		les 

let concretise2 (a : jsil_logic_assertion) (x: string) (y: string) (les : jsil_logic_expr list) : jsil_logic_assertion list = 
	let les_pairs = generate_all_pairs les in 

	List.map 
		(fun (le1, le2) -> 
			let subst = init_substitution2 [ x; y ] [ le1; le2 ] in 
			assertion_substitution a subst true)
		les_pairs  


