open DynArray
open Set
open Stack
open JSIL_Syntax

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


let evaluate_type_of lit =
	match lit with
	| Undefined    -> UndefinedType
	| Null         -> NullType
	| Empty        -> EmptyType
	| Constant _   -> NumberType
	| Bool _       -> BooleanType
	| Num n        -> NumberType
	| String _     -> StringType
	| Char _       -> CharType
	| Loc _        -> ObjectType
	| Type _       -> TypeType
	| LList _      -> ListType
	(* TODO: Could this benefit from being something else? *)
	| CList _      -> ListType


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
  	| LLstNth (e1, e2)    -> LLstNth (map_e e1, map_e e2)
  	| LStrNth (e1, e2)    -> LStrNth (map_e e1, map_e e2)
  	| LUnknown            -> LUnknown


(** Apply function f to the logic expressions in an assertion, recursively when it makes sense. *)
let rec assertion_map f asrt =
	(* Map recursively to assertions and expressions *)
	let map_a = assertion_map f in
	let map_e = logic_expression_map f in
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
	| LEmptyFields (o, ls)   -> LEmptyFields (map_e o, ls)

let rec logic_expression_fold f_atom f_fold lexpr =
	let fold_e = logic_expression_fold f_atom f_fold in
  match lexpr with
  | LLit _ | LNone | LVar _ | ALoc _ | PVar _ | LUnknown -> f_atom lexpr
  | LBinOp (e1, op, e2)   -> f_fold lexpr [ (fold_e e1); (fold_e e2) ]
  | LUnOp (op, e)         -> f_fold lexpr [ (fold_e e) ]
  | LTypeOf e             -> f_fold lexpr [ (fold_e e) ]
  | LEList le             -> f_fold lexpr (List.map fold_e le)
  | LLstNth (e1, e2)      -> f_fold lexpr [ (fold_e e1); (fold_e e2) ]
  | LStrNth (e1, e2)      -> f_fold lexpr [ (fold_e e1); (fold_e e2) ]


let rec assertion_fold f_atom f_fold asrt =
	let fold_a = assertion_fold f_atom f_fold in
	match asrt with
	| LTrue | LFalse | LEq (_, _) | LLess (_, _) | LLessEq (_, _) | LStrLess (_, _) | LPointsTo (_, _, _) | LEmp | LPred (_, _) | LTypes _ | LEmptyFields _ -> f_atom asrt
	| LAnd (a1, a2)         -> f_fold asrt [ (fold_a a1); (fold_a a2) ]
	| LOr (a1, a2)          -> f_fold asrt [ (fold_a a1); (fold_a a2) ]
	| LStar (a1, a2)        -> f_fold asrt [ (fold_a a1); (fold_a a2) ]
	| LNot a                -> f_fold asrt [ (fold_a a) ]



let rec get_logic_expression_literals le =
	let fe = get_logic_expression_literals in
	match le with
	| LLit (LList ls) ->
		let ls = List.map (fun x -> LLit x) ls in
			List.concat (List.map fe ls)
	| LLit lit -> [ lit ]
	| LNone | LVar _ | ALoc _ | PVar _ | LUnknown -> []
	| LBinOp (le1, _, le2) | LLstNth (le1, le2) | LStrNth (le1, le2)  -> (fe le1) @ (fe le2)
	| LUnOp (_, le) |	LTypeOf le -> fe le
 	| LEList les -> List.concat (List.map fe les)

let rec get_assertion_literals a =
	let f = get_assertion_literals in
	let fe = get_logic_expression_literals in
	match a with
	| LTrue | LFalse | LEmp | LTypes _ -> []
	| LNot a -> f a
	| LAnd (a1, a2) | LOr (a1, a2) | LStar (a1, a2) -> (f a1) @ (f a2)
	| LPointsTo (le1, le2, le3) -> (fe le1) @ (fe le2) @ (fe le3)
	| LEq (le1, le2) | LLess (le1, le2) | LLessEq (le1, le2) | LStrLess (le1, le2) -> (fe le1) @ (fe le2)
	| LPred (_, les) -> List.concat (List.map fe les)
	| LEmptyFields (e, les) -> (fe e) @ List.concat (List.map fe les)

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
		| LLit _ | LNone | ALoc _ | PVar _ | LUnknown -> []
		| LVar x -> [ x ]
		| LBinOp (le1, _, le2) | LLstNth (le1, le2) | LStrNth (le1, le2) -> (fe le1) @ (fe le2)
		| LUnOp (_, le) |	LTypeOf le -> fe le
	 	| LEList les -> List.concat (List.map fe les)

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
		| LEmptyFields (e, les) -> (fe e) @ List.concat (List.map fe les) in
		
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


let is_pure_assertion a =
	let f_atom a =
		(match a with
		| LPred (_, _) | LPointsTo (_, _, _) | LEmp -> false
		| _                                         -> true)  in
	let f_fold a ret_list =
		let ret = List.fold_left (fun ac v -> (ac && v)) true ret_list in
		(match a with
		| LAnd (_, _) | LOr (_, _) | LStar (_, _) | LNot _ -> ret
		| _  -> raise (Failure "Internal Error: is_pure_assertion")) in
	assertion_fold f_atom f_fold a


let is_pure_atom a =
	match a with
	| LTrue | LFalse | LEq (_, _) | LLess (_, _) | LLessEq (_, _) | LStrLess (_, _) -> true
	| _ -> false

let only_pure_atoms_negated a =
	let f_atom a = true in
	let f_fold a ret_list =
		let ret = List.fold_left (fun ac v -> (ac && v)) true ret_list in
		(match a with
		| LAnd (_, _) | LOr (_, _) | LStar (_, _) -> ret
		| LNot a -> is_pure_atom a
		| _      -> raise (Failure "Internal Error: only_pure_atoms_negated")) in
	assertion_fold f_atom f_fold a


let rec purify_stars a =
	let f = purify_stars in
	match a with
	| LTrue | LFalse | LEq (_,_) | LLess (_,_) | LLessEq (_, _) | LStrLess (_, _) | LPred (_, _) -> a, []
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
	| LNone 
	| LUnknown -> SS.empty
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
	| LEList le_list -> 
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
	| LEmptyFields (o, les) -> 
			let v_o = fe o in
			let v_les = List.fold_left (fun ac e -> 
				let v_e = fe e in
					SS.union ac v_e) SS.empty les in
			SS.union v_o v_les) in
	result

let get_assertion_list_vars assertions catch_pvars =
	List.fold_left (fun ac a ->
		let v_a = get_assertion_vars catch_pvars a in
		SS.union ac v_a) SS.empty assertions

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
		
let get_vars_tbl vars =
  let len = SS.cardinal vars in
  let vars_tbl = Hashtbl.create len in
  List.iteri (fun i var -> Hashtbl.add vars_tbl var i) (SS.elements vars);
  vars_tbl

let rec push_in_negations_off a =
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
	| LTrue        | LFalse | LEq (_, _)          | LLess (_, _) | LLessEq (_, _) | LStrLess (_, _)
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
	| LEq (_, _)   | LLess (_, _) | LLessEq (_, _) | LStrLess (_, _) | LPred (_, _) -> LNot a
	| LStar (_, _) | LEmp         | LPointsTo (_, _, _) | LEmptyFields _ -> raise (Failure err_msg)
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


let pre_normalize_assertion a =
	(* Printf.printf "I am inside the pre_normalize being HAPPY. Looking at the assertion: %s!!!!\n"
		(JSIL_Print.string_of_logic_assertion a false); *)
	if (only_pure_atoms_negated a)
		then [ a ]
		else
			begin
				(* Printf.printf "there are non-pure atoms negated!!!!\n"; *)
				let new_a = push_in_negations_off a in
				(* Printf.printf "Original a: %s.\nAfter prenormalisation:\n%s\n"
					(JSIL_Print.string_of_logic_assertion a false)
					(JSIL_Print.string_of_logic_assertion new_a false); *)
				[ new_a ]
			end


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

	| LLstNth (le1, le2) -> LLstNth ((f le1), (f le2))

	| LStrNth (le1, le2) -> LStrNth ((f le1), (f le2))

	| LUnknown -> LUnknown


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
	| LEmptyFields (obj, lstr) -> LEmptyFields (fe obj, lstr)


let filter_substitution subst vars =
	let new_subst = Hashtbl.copy subst in
	Hashtbl.filter_map_inplace (fun v le ->
		match (SS.mem v vars) with
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

		let all_types = [ UndefinedType; NullType; EmptyType; BooleanType; NumberType; StringType; ObjectType; ListType; TypeType; NoneType ] in
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
			| _ ->
				Printf.printf "type_lexpr: op: %s, t: %s\n"  (JSIL_Print.string_of_binop op) (JSIL_Print.string_of_type t1);
				raise (Failure "ERROR")))
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

	| LNone    -> (Some NoneType, true, [])
	| LUnknown -> (None, false, [])) in
	
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

  (* LEList is not reverse typable because we lose type information *)
	| LEList _ -> false

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

		| LNone    -> (NoneType = le_type)
		| LUnknown -> false)


let reverse_type_lexpr gamma le le_type : typing_environment option =
	let new_gamma : typing_environment = mk_gamma () in
	let ret = reverse_type_lexpr_aux gamma new_gamma le le_type in
	if (ret)
		then Some new_gamma
		else None


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
	let err_msg = (Printf.sprintf "logical expression: binop %s : cannot be lifted to assertion" (JSIL_Print.string_of_binop op)) in
	let f = lift_logic_expr in
	let lexpr_to_ass_binop binop =
		(match binop with
		| Equal -> (fun le1 le2 -> LEq (le1, le2))
		| LessThan -> (fun le1 le2 -> LLess (le1, le2))
		| LessThanString -> (fun le1 le2 -> LStrLess (le1, le2))
		| LessThanEqual -> (fun le1 le2 -> LLessEq (le1, le2))
		| _ -> raise (Failure "Error: lift_binop_expr")) in
	(match op with
	| Equal
	| LessThan
	| LessThanString
	| LessThanEqual ->
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
				print_debug (Printf.sprintf "all_different: (%s, %s) (%s, %s)\n" (sle f) (sle v) (sle f') (sle v'));
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

exception FoundIt of jsil_logic_expr

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
				| LEList _
				| LBinOp (_, LstCons, _) -> raise (FoundIt value)
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
							| LEList _
							| LBinOp (_, LstCons, _) -> raise (FoundIt lexpr)
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
	let f = reduce_expression store gamma pfs in
	let result = (match e with

	| LBinOp (le1, LstCons, LEList []) -> LEList [ f le1 ]
	| LBinOp (le1, LstCons, LLit (LList [])) -> LEList [ f le1 ] 
	| LBinOp (LEList le1, LstCat, LEList le2) -> f (LEList (le1 @ le2))
	(* TODO: combinations of LLit (LList _) and LEList *)

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

		
	(* Binary operators *)
	| LBinOp (e1, bop, e2) ->
		let re1 = f e1 in
		let re2 = f e2 in
		(match bop with
		| Plus ->
			(match re1, re2 with
			(* n1 +J n2 ---> n1 + n2 *) 
			| LLit (Num n1), LLit (Num n2) -> LLit (Num (n1 +. n2))
			(* (_ +J n1) +J n2 ---> _ +J (n1 + n2) *)
			| LBinOp (re1, Plus, LLit (Num n1)), LLit (Num n2) -> f (LBinOp (re1, Plus, LLit (Num (n1 +. n2))))
			(* (n1 +J _) +J n2 ---> _ +J (n1 + n2) *)
			| LBinOp (LLit (Num n1), Plus, re2), LLit (Num n2) -> f (LBinOp (re2, Plus, LLit (Num (n1 +. n2))))
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
		let list = find_me_Im_a_list store pfs list in
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
			if (Utils.is_int n) then
		  let ni = int_of_float n in
			 (match (ni = 1) with
		   | true -> f le
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
				| _ -> LUnOp (LstLen, e1))
		 | StrLen -> (match re1 with
		    | LLit (String str) -> (LLit (Num (float_of_int (String.length str))))
		    | _ -> LUnOp (StrLen, e1))
		 | _ -> LUnOp (op, re1))

	(* Everything else *)
	| _ -> e) in
	(* if (not (e = result)) then print_debug (Printf.sprintf "Reduce expression: %s ---> %s"
		(JSIL_Print.string_of_logic_expression e false)
		(JSIL_Print.string_of_logic_expression result false)); *)
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
	| LOr (a1, a2) ->
		let ra1 = f a1 in
		let ra2 = f a2 in
		let a' = LOr (ra1, ra2) in
		if ((ra1 = a1) && (ra2 = a2))
			then a' else f a'

	| LNot LTrue -> LFalse
	| LNot LFalse -> LTrue
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
		(* Warning - NaNs, infinities, this and that *)
		let eq = (re1 = re2) && (re1 <> LUnknown) in
		if eq then LTrue
		else
		let ite a b = if (a = b) then LTrue else LFalse in
		let default e1 e2 re1 re2 = 
			let a' = LEq (re1, re2) in
				if ((re1 = e1) && (re2 = e2))
					then a' else f a' in
		(match e1, e2 with
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
					
			| LLit (Bool true), LBinOp (e1, LessThan, e2) -> LLess (e1, e2)
			| LLit (Bool false), LBinOp (e1, LessThan, e2) -> LNot (LLess (e1, e2))

			(* Plus theory *)
			| LBinOp (re1, Plus, LLit (Num n1)), LBinOp (re2, Plus, LLit (Num n2))
			| LBinOp (re1, Plus, LLit (Num n1)), LBinOp (LLit (Num n2), Plus, re2)
			| LBinOp (LLit (Num n1), Plus, re1), LBinOp (re2, Plus, LLit (Num n2))
			| LBinOp (LLit (Num n1), Plus, re1), LBinOp (LLit (Num n2), Plus, re2) ->
					if (Utils.is_normal n1 && (n1 = n2)) then f (LEq (re1, re2)) else default e1 e2 re1 re2
						
			| _, _ -> default e1 e2 re1 re2
		)

	| LLess (e1, e2) ->
		let re1 = fe e1 in
		let re2 = fe e2 in
		LLess (re1, re2)

	| _ -> a) in
	(* if (not (a = result)) then print_debug (Printf.sprintf "Reduce assertion: %s ---> %s"
		(JSIL_Print.string_of_logic_assertion a false)
		(JSIL_Print.string_of_logic_assertion result false)); *)
	result

let reduce_assertion_no_store_no_gamma_no_pfs = reduce_assertion (Hashtbl.create 1) (Hashtbl.create 1) (DynArray.create ())
let reduce_assertion_no_store_no_gamma        = reduce_assertion (Hashtbl.create 1) (Hashtbl.create 1)
let reduce_assertion_no_store                 = reduce_assertion (Hashtbl.create 1)



(*
let resolve_logical_variables pfs lvars = 
	let rec loop pfs lvars_found_so_far = 
		match pfs with 
		| [] -> lvars_found_so_far 
		| LEq (LVar v, le) :: rest
		| LEq (le, LVar v) :: rest ->
			let vars_le = 
			if (List.mem v lvars) 
				then loop rest 
				else find_me_Im_a_loc rest lvar  *)
	
let pred_def_tbl_from_list pred_defs = 
	let pred_def_tbl = Hashtbl.create small_tbl_size in
	List.iter 
		(fun pred_def -> Hashtbl.add pred_def_tbl pred_def.name pred_def)
		pred_defs; 
	pred_def_tbl

(* Unfolding of macros *)
let rec unfold_macro (macro_name : string) (params_vals : jsil_logic_expr list) : jsil_logic_command =
	if (Hashtbl.mem macro_table macro_name) then
		(let macro = Hashtbl.find macro_table macro_name in
		(* print_debug (Printf.sprintf ("Macro: %s(%s) : %s") 
				macro.mname
				(String.concat ", " macro.mparams)
				(JSIL_Print.string_of_lcmd macro.mdefinition)); *)
		let params = macro.mparams in
		let lparo = List.length params in
		let lparv = List.length params_vals in
		if (lparo <> lparv) then
			raise (Failure (Printf.sprintf "Macro %s called with incorrect number of parameters: %d instead of %d." macro.mname lparv lparo))
		else
			let subst = Hashtbl.create 17 in
			List.iter2 (fun x y -> Hashtbl.add subst x y) params params_vals;
			macro_subst macro.mdefinition subst)
		else
			raise (Failure (Printf.sprintf "Macro %s not found in macro table." macro_name))
and
(** Apply function f to the logic expressions in a logic command, recursively when it makes sense. *)
lcmd_map f unfold_macros lcmd =
	(* Map recursively to commands, assertions, and expressions *)
	let map_l = lcmd_map f unfold_macros in
	let map_a = assertion_map f in
	let map_e = logic_expression_map f in
	match lcmd with
	| Fold      a                   -> Fold      (map_a a)
	| Unfold    a                   -> Unfold    (map_a a)
	| RecUnfold s                   -> RecUnfold s
	| LogicIf   (e, lcmds1, lcmds2) -> LogicIf   (map_e e, List.map (fun x -> map_l x) lcmds1, List.map (fun x -> map_l x) lcmds2)
	| Macro     (name, params_vals) -> 
		let fparams_vals = List.map (fun x -> map_e x) params_vals in
		(match unfold_macros with
		| true  -> unfold_macro name fparams_vals
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