open DynArray
open Set
open Stack
open JSIL_Syntax

module SS = Set.Make(String)


let evaluate_type_of lit =
	match lit with
	| Undefined    -> UndefinedType
	| Null         -> NullType
	| Empty        -> EmptyType
	| Constant _   -> NumberType
	| Bool _       -> BooleanType
	| Integer _    -> IntType
	| Num n        -> if (n = (snd (modf n))) then IntType else NumberType
	| String _     -> StringType
	| Loc _        -> ObjectType
	| Type _       -> TypeType
	| LVRef (_, _) -> VariableReferenceType
	| LORef (_, _) -> ObjectReferenceType
	| LList _      -> ListType


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


let rec logic_expression_fold f_atom f_fold lexpr =
	let fold_e = logic_expression_fold f_atom f_fold in
  match lexpr with
  | LLit _ | LNone | LVar _ | ALoc _ | PVar _ | LUnknown -> f_atom lexpr
  | LBinOp (e1, op, e2)   -> f_fold lexpr [ (fold_e e1); (fold_e e2) ]
  | LUnOp (op, e)         -> f_fold lexpr [ (fold_e e) ]
 	| LEVRef (e1, e2)       -> f_fold lexpr [ (fold_e e1); (fold_e e2) ]
  | LEORef (e1, e2)       -> f_fold lexpr [ (fold_e e1); (fold_e e2) ]
  | LBase e               -> f_fold lexpr [ (fold_e e) ]
  | LField e              -> f_fold lexpr [ (fold_e e) ]
  | LTypeOf e             -> f_fold lexpr [ (fold_e e) ]
  | LEList le             -> f_fold lexpr (List.map fold_e le)
  | LLstNth (e1, e2)      -> f_fold lexpr [ (fold_e e1); (fold_e e2) ]
  | LStrNth (e1, e2)      -> f_fold lexpr [ (fold_e e1); (fold_e e2) ]


let rec assertion_fold f_atom f_fold asrt =
	let fold_a = assertion_fold f_atom f_fold in
	match asrt with
	| LTrue | LFalse | LEq (_, _) | LLess (_, _) | LLessEq (_, _) | LStrLess (_, _) | LPointsTo (_, _, _) | LEmp | LPred (_, _) | LTypes _ -> f_atom asrt
	| LAnd (a1, a2)         -> f_fold asrt [ (fold_a a1); (fold_a a2) ]
	| LOr (a1, a2)          -> f_fold asrt [ (fold_a a1); (fold_a a2) ]
	| LStar (a1, a2)        -> f_fold asrt [ (fold_a a1); (fold_a a2) ]
	| LNot a                -> f_fold asrt [ (fold_a a) ]


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
  var_set is a hashtbl (what else?) that models the set of variables
*)
let rec get_expr_vars var_set catch_pvars e =
	let f = get_expr_vars var_set catch_pvars in
	match e with
	| LLit _
	| LNone -> ()
	| LVar var ->
			if (not catch_pvars)
				then (try Hashtbl.find var_set var; () with _ -> Hashtbl.add var_set var true)
				else ()
	| LUnknown
	| ALoc _ -> ()
	| PVar var ->
			if (catch_pvars)
				then (try Hashtbl.find var_set var; () with _ -> Hashtbl.add var_set var true)
				else ()
	| LBinOp (e1, op, e2) -> f e1; f e2
	| LUnOp (op, e1) -> f e1
	| LTypeOf e1 -> f e1
	| LEList le_list -> List.iter (fun le -> f le) le_list
	| LLstNth (e1, e2)
	| LStrNth (e1, e2) -> f e1; f e2


let rec get_ass_vars_iter vars_tbl catch_pvars ass =
	let f = get_ass_vars_iter vars_tbl catch_pvars in
	let fe = get_expr_vars vars_tbl catch_pvars in
	match ass with
	| LAnd (a1, a2) -> f a1; f a2
	| LOr (a1, a2) -> f a1; f a2
	| LNot a1 -> f a1
	| LTrue
	| LFalse -> ()
	| LEq (e1, e2)
	| LLess (e1, e2)
	| LLessEq (e1, e2)
	| LStrLess (e1, e2) -> fe e1; fe e2
	| LStar (a1, a2) -> f a1; f a2
	| LPointsTo (e1, e2, e3) -> fe e1; fe e2; fe e3
	| LEmp
	| LTypes _ -> ()
	| LPred (_, es) -> List.iter fe es


let get_assertion_vars ass catch_pvars =
	let vars_tbl = Hashtbl.create small_tbl_size in
	get_ass_vars_iter vars_tbl catch_pvars ass;
	vars_tbl


let get_list_of_assertions_vars_tbl assertions catch_pvars =
	let vars_tbl = Hashtbl.create small_tbl_size in
	let rec loop assertions =
		match assertions with
		| [] -> ()
		| a :: rest_assertions ->
			get_ass_vars_iter vars_tbl catch_pvars a;
			loop rest_assertions in

	loop assertions;
	vars_tbl


let get_list_of_assertions_vars_list assertions catch_pvars =
	let vars_tbl = get_list_of_assertions_vars_tbl assertions catch_pvars in
	Hashtbl.fold
		(fun var v_val ac -> var :: ac)
		vars_tbl
		[]


let get_subtraction_vars_old assertions_left assertions_right catch_pvars =
	let assertion_left_vars_list = get_list_of_assertions_vars_list assertions_left catch_pvars in
	let assertion_right_vars_tbl = get_list_of_assertions_vars_tbl assertions_right catch_pvars in

	(* Printf.printf "pat_pf_vars: %s\n" (print_var_list assertion_left_vars_list); *)

	let assertion_left_vars_list =
		List.filter
			(fun x -> not (Hashtbl.mem assertion_right_vars_tbl x))
			assertion_left_vars_list in
	assertion_left_vars_list


let get_subtraction_vars assertions subst =
	let vars_list = get_list_of_assertions_vars_list assertions false in
	let new_vars_list =
		List.filter
			(fun x -> not (Hashtbl.mem subst x))
			vars_list in
	new_vars_list


let get_expr_vars_lst le catch_p_vars =
	let vars_tbl = Hashtbl.create small_tbl_size in
	get_expr_vars vars_tbl catch_p_vars le;
	Hashtbl.fold
		(fun var v_val ac -> var :: ac)
		vars_tbl
		[]

let get_ass_vars_lst a catch_p_vars =
	let vars_tbl = get_assertion_vars a catch_p_vars in
	Hashtbl.fold
		(fun var v_val ac -> var :: ac)
		vars_tbl
		[]


let get_vars_tbl var_arr =
	let len = Array.length var_arr in
	let vars_tbl = Hashtbl.create len in
	for u=0 to (len-1) do
		let var_u = var_arr.(u) in
		Hashtbl.add vars_tbl var_u u
	done;
	vars_tbl


let get_subtraction_vars_lexpr lexpr_left lexpr_right catch_pvars =
	let right_lexpr_vars_tbl = Hashtbl.create small_tbl_size in

	let left_lexpr_vars_list = get_expr_vars_lst lexpr_left catch_pvars in
	get_expr_vars right_lexpr_vars_tbl catch_pvars lexpr_right;

	let left_lexpr_vars_list =
		List.filter
			(fun x -> not (Hashtbl.mem right_lexpr_vars_tbl x))
			left_lexpr_vars_list in
	left_lexpr_vars_list


let list_subraction list1 list2 = []


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
	| LPred (_, _) | LEmp   | LPointsTo (_, _, _) | LTypes _ -> a)
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
	| LStar (_, _) | LEmp         | LPointsTo (_, _, _) -> raise (Failure err_msg)
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
	| LFalse           | LTypes _
	| LEq (_, _)    	 | LNot (LEq (_, _))
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
						let new_var = JSIL_Memory_Model.fresh_lvar () in
						Hashtbl.replace subst var (LVar new_var);
						LVar new_var
					else (LVar var))

	| ALoc aloc ->
			(try Hashtbl.find subst aloc with _ ->
				if (not partial)
					then
						let new_aloc = ALoc (JSIL_Memory_Model.fresh_aloc ()) in
						Hashtbl.replace subst aloc new_aloc;
						new_aloc
<<<<<<< 18f80f0857c1f7e1794b3021e93e86c6eef8dc26
					else
						ALoc aloc)

	| PVar var -> (PVar var)

	| LBinOp (le1, op, le2) -> LBinOp ((f le1), op, (f le2))

	| LUnOp (op, le) -> LUnOp (op, (f le))
=======
					else
						ALoc aloc)

	| PVar var -> (PVar var)

	| LBinOp (le1, op, le2) -> LBinOp ((f le1), op, (f le2))

	| LUnOp (op, le) -> LUnOp (op, (f le))

	| LEVRef (le1, le2) -> LEVRef ((f le1), (f le2))

	| LEORef (le1, le2) -> LEORef ((f le1), (f le2))

	| LBase le -> LBase	(f le)

	| LField le -> LField (f le)
>>>>>>> no more symmetry

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


let filter_substitution subst vars =
	let new_subst = Hashtbl.create (List.length vars) in
	List.iter
		(fun var ->
			try
				(let le = Hashtbl.find subst var in
				Hashtbl.add new_subst var le)
			with _ -> ())
		vars;
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


let filter_vars vars ignore_vars : string list =
	let ignore_vars = SS.of_list ignore_vars in
	let vars =
		List.fold_left
			(fun ac var ->
				if (SS.mem var ignore_vars)
					then ac
					else (var :: ac))
			[ ]
			vars in
	vars

let indent = ref 0

let rec type_lexpr gamma le =
	let mk_indent = String.make !indent '\t' in
	let f = type_lexpr gamma in

	(* print_endline (Printf.sprintf "%sI am inside type_lexpr trying to type %s" mk_indent (JSIL_Print.string_of_logic_expression le false)); *)
	indent := !indent + 1;

	(* Printf.printf "I am inside type_lexpr trying to type %s\n%!" (JSIL_Print.string_of_logic_expression le false); *)

	let ret =
	(match le with
	(* Literals are always typable *)
  | LLit lit -> (Some (evaluate_type_of lit), true, [])

	(* Variables are typable if in gamma, otherwise no no *)
	| LVar var
	| PVar var ->
		(match JSIL_Memory_Model.gamma_get_type gamma var with
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
		let tt t1 t2 new_constraints =
			(match te with
			| Some te ->
				if (types_leq te t1)
					then (Some t2, true, (new_constraints @ constraints))
					else (None, false, [])
			| None -> (None, false, [])) in
		if (ite) then
  		(match unop with
			(* Boolean to Boolean  *)
  		| Not -> tt BooleanType BooleanType []
			(* Number to Number    *)
  		| UnaryMinus	| BitwiseNot	| M_sgn			| M_abs	| M_acos
      | M_asin			| M_atan			| M_ceil		| M_cos	| M_exp
      | M_floor			| M_log				| M_round		| M_sin	| M_sqrt
			| M_tan  -> tt NumberType NumberType []
			(* Number to Int       *)
  		| ToIntOp			| ToUint16Op	| ToInt32Op	| ToUint32Op -> tt NumberType IntType []
  		(* Number to String    *)
			| ToStringOp -> tt NumberType StringType []
			(* String to Number    *)
  		| ToNumberOp -> tt StringType NumberType []
			(* Anything to Boolean *)
      | IsPrimitive -> (Some BooleanType, true, constraints)
			(* List to List -> generates constraint *)
			| Cdr ->
				let new_constraint = (LNot (LLess (e, (LLit (Integer 1))))) in
				tt ListType ListType [ new_constraint ]
			(* List to Anything -> generates constraint *)
      | Car ->
				let new_constraint = (LNot (LLess (e, (LLit (Integer 1))))) in
				(match te with
				| Some ListType -> (None, true, [ new_constraint ])
				| None          -> (None, false, [] ))
			(* List to Int         *)
  		| LstLen -> tt ListType IntType []
			(* String to Int       *)
			| StrLen -> tt StringType IntType [])
		else
			(None, false, [])

	| LBinOp (e1, op, e2) ->
		let (te1, ite1, constraints1) = f e1 in
		let (te2, ite2, constraints2) = f e2 in
		let constraints = constraints1 @ constraints2 in

		let all_types = [ UndefinedType; NullType; EmptyType; BooleanType; IntType; NumberType; StringType; ObjectType; ListType; TypeType ] in
		let check_valid_type t types ret_type new_constraints =
			let is_t_in_types = List.exists (fun t_arg -> (t = t_arg)) types in
			if (is_t_in_types)
				then (Some ret_type, true, (new_constraints @ constraints))
				else (None, false, []) in

		(match te1, te2 with
		| (Some t1), (Some t2) ->
			let t = types_lub t1 t2 in
			(match op, t with
			| Equal, (Some t) -> check_valid_type t all_types BooleanType []
			| LessThan, (Some t) | LessThanEqual, (Some t) -> check_valid_type t [ IntType; NumberType ] BooleanType []
			| LessThanString, (Some t) -> check_valid_type t [ StringType ] BooleanType []
			| Plus, (Some t)	| Minus, (Some t)	| Times, (Some t)	| Mod, (Some t) -> check_valid_type t [ IntType; NumberType ] t []
			| Div, (Some t) -> check_valid_type t [ IntType; NumberType ] NumberType []
			| And, (Some t)	| Or, (Some t) -> check_valid_type t [ BooleanType ] BooleanType []
			| BitwiseAnd, (Some t)	| BitwiseOr, (Some t)	| BitwiseXor, (Some t)	| LeftShift, (Some t)	| SignedRightShift, (Some t)
			| UnsignedRightShift, (Some t)	| M_atan2, (Some t) -> check_valid_type t [ IntType; NumberType ] NumberType []
			| M_pow, (Some t) -> check_valid_type t [ IntType; NumberType ] t []
			| Subtype, (Some t) -> check_valid_type t all_types BooleanType []
			| LstCons, _ -> check_valid_type t2 [ ListType ] ListType []
			| LstCat, (Some t) -> check_valid_type t [ ListType ] ListType []
			| StrCat, (Some t) -> check_valid_type t [ StringType ] StringType []
			| _, Some t ->
				Printf.printf "op: %s, t: %s"  (JSIL_Print.string_of_binop op) (JSIL_Print.string_of_type t);
				raise (Failure "ERROR")
		 	| _, None ->
				Printf.printf "op: %s, t: none"  (JSIL_Print.string_of_binop op) ;
				raise (Failure "ERROR"))
		| _, _ -> (None, false, []))

	| LLstNth (lst, index) ->
		(* Printf.printf "Darling targets: %s and %s\n" (JSIL_Print.string_of_logic_expression lst false) (JSIL_Print.string_of_logic_expression index false); *)
		let type_lst, _, constraints1 = f lst in
		let type_index, _, constraints2 = f index in
		let constraints = constraints1 @ constraints2 in
		(match (type_lst, type_index) with
		| Some ListType, Some IntType ->
			(* Printf.printf "Types have matched.\n";
				 I want the shit normalised with respect to the pure part
     	   let simplified = normalise_me_silly pfrm gamma (LLstNth (lst, index)) in
			   Printf.printf "Simplified: %s" (JSIL_Print.string_of_logic_expression simplified false);
         if (simplified = LLstNth (lst, index)) then (None, false)
				else (f simplified) *)
			let new_constraint1 = (LNot (LLess (index, LLit (Integer 0)))) in
			let new_constraint2 = (LLess (index, LUnOp (LstLen, lst))) in
			(None, true, (new_constraint1 :: (new_constraint2 :: constraints)))
		| _, _ -> (None, false, []))

	| LStrNth (str, index) ->
		(* Printf.printf "Darling targets: %s and %s\n" (JSIL_Print.string_of_logic_expression str false) (JSIL_Print.string_of_logic_expression index false); *)

		let type_str, _, constraints1 = f str in
		let type_index, _, constraints2 = f index in
		let constraints = constraints1 @ constraints2 in
		(match (type_str, type_index) with
		| Some StringType, Some IntType ->
			let new_constraint1 = (LNot (LLess (index, LLit (Integer 0)))) in
			let new_constraint2 = (LLess (index, LUnOp (StrLen, str))) in
			(* Printf.printf "Entailment: %b\n" entail; *)
			(Some StringType, true, (new_constraint1 :: (new_constraint2 :: constraints)))
		| Some stype, Some itype ->
			(* Printf.printf "Something went wrong with the types. %s %s\n\n" (JSIL_Print.string_of_type stype) (JSIL_Print.string_of_type stype); *)
			(None, false, [])
		| Some stype, None ->
			(* Printf.printf "String type: %s Index not typable.\n\n" (JSIL_Print.string_of_type stype); *)
			(None, false, [])
		| None, Some itype ->
			(* Printf.printf "String not typable. Index type: %s\n\n" (JSIL_Print.string_of_type itype); *)
			(None, false, [])
		| None, None ->
			(* Printf.printf "Both string and index not typable. Ew.\n\n"; *)
			(None, false, []))

	| LNone    -> (Some NoneType, true, [])
  | LUnknown -> (None, false, [])) in
    indent := !indent - 1;
	(* print_endline (Printf.sprintf "%sI finished typing %s, baby!" mk_indent (JSIL_Print.string_of_logic_expression le false)); *)
	ret
(*
and
normalise_me_silly (pure_formulae : JSIL_Memory_Model.pure_formulae) gamma lexpr =
(match lexpr with
	| LLstNth (lst, index) ->
		let lit_lst = subst_to_literal pure_formulae gamma lst in
		let lit_idx = subst_to_literal pure_formulae gamma index in
		(* Printf.printf "normalise_me_silly: %s %s\n" (JSIL_Print.string_of_logic_expression lit_lst false) (JSIL_Print.string_of_logic_expression lit_idx false); *)
		(match lit_idx with
			| LLit (Num idx) ->
				(match lit_lst with
					| LLit (LList lst) ->
						(try
							let ret = List.nth lst (int_of_float idx) in LLit ret
						with
							| _ -> lexpr)
					| LEList lst ->
						(try
							List.nth lst (int_of_float idx)
						with
							| _ -> lexpr)
					| _ -> lexpr)
			| _ -> lexpr)

	 | _ -> lexpr)
and
subst_to_literal (pure_formulae : JSIL_Memory_Model.pure_formulae) gamma lexpr =
let pf = filter_eqs pure_formulae in
	let rec subst_it pf lexpr =
	(match pf with
	 | LEq (a, b) :: pf ->
	 	let test = (a = lexpr) in
	 		if test then b else (subst_it pf lexpr)
	 | [] -> lexpr
	 | _ -> raise (Failure "NO!")) in
	subst_it pf lexpr
and
filter_eqs (pure_formulae : JSIL_Memory_Model.pure_formulae) =
	DynArray.fold_left
		(fun ac (x : JSIL_Syntax.jsil_logic_assertion) ->
			(match x with
			  | LEq (a, b) -> if ((a = b) || List.mem x ac) then ac else (x :: ac)
			  | _ -> ac)
		) [] pure_formulae
*)



let rec reverse_type_lexpr_aux gamma new_gamma le le_type =
	let f = reverse_type_lexpr_aux gamma new_gamma in
	(* Printf.printf "le: %s\n\n\n" (JSIL_Print.string_of_logic_expression le false); *)
	(match le with
	(* Literals are always typable *)
  | LLit lit -> if (types_leq (evaluate_type_of lit) le_type) then true else false

	(* Variables are reverse-typable if they are already typable *)
	(* with the target type or if they are not typable           *)
	| LVar var
	| PVar var ->
		(match (JSIL_Memory_Model.gamma_get_type gamma var), (JSIL_Memory_Model.gamma_get_type new_gamma var) with
		| Some t, None
		| None, Some t     -> if (types_leq t le_type) then true else false
		| None, None       -> (JSIL_Memory_Model.update_gamma new_gamma var (Some le_type)); true
		| Some t1, Some t2 -> if (t1 = t2) then true else false)

	(* Abstract locations are reverse-typable if the target type is ObjectType *)
	| ALoc _ -> if (le_type = ObjectType) then true else false

  (* LEList is not reverse typable because we lose type information *)
	| LEList _ -> false

  | LUnOp (unop, le) ->
		(* Printf.printf "UNOP\n\n\n"; *)
		(match unop with
  	| Not        -> if (le_type = BooleanType) then f le BooleanType else false
		| UnaryMinus -> if (types_leq le_type NumberType) then f le le_type else false
  	| BitwiseNot	| M_sgn	| M_abs		| M_acos	| M_asin	| M_atan	| M_ceil
    | M_cos				| M_exp	| M_floor	| M_log		| M_round	| M_sin		| M_sqrt
  	| M_tan      -> if (le_type = NumberType) then f le le_type else false
		| ToIntOp			| ToUint16Op			| ToInt32Op					| ToUint32Op
								 ->	if (le_type = IntType) then f le NumberType else false

		| ToStringOp ->	if (le_type = StringType) then f le NumberType else false

		| ToNumberOp ->	if (le_type = NumberType)	then f le StringType else false

	  | IsPrimitive -> false

		| Cdr	| Car	| LstLen -> f le ListType

		| StrLen -> if (le_type = IntType) then f le StringType else false)


	| LBinOp (le1, op, le2) ->
		(match op with
		| Equal	| LessThan	| LessThanEqual -> false
		| LessThanString -> (f le1 StringType) && (f le2 StringType)

		| Plus	| Minus	| Times	| Mod ->
			if ((le_type = NumberType) || (le_type = IntType))
				then ((f le1 le_type) && (f le2 le_type))
				else false

		| Div -> false

		| And | Or ->
			if (le_type = BooleanType)
				then ((f le1 BooleanType) && (f le2 BooleanType))
				else false

		| BitwiseAnd	| BitwiseOr	| BitwiseXor	| LeftShift	| SignedRightShift
		| UnsignedRightShift			| M_atan2			| M_pow			| Subtype
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
			Printf.printf "op: %s, t: %s"  (JSIL_Print.string_of_binop op) (JSIL_Print.string_of_type le_type);
			raise (Failure "ERROR"))

		| LLstNth (le1, le2) -> (f le1 ListType) && (f le2 IntType)

		| LStrNth (le1, le2) -> (f le1 StringType) && (f le2 IntType)

		| LNone    -> (NoneType = le_type)
 	 	| LUnknown -> false)


let reverse_type_lexpr gamma le le_type : JSIL_Memory_Model.typing_environment option =
	let new_gamma : JSIL_Memory_Model.typing_environment = JSIL_Memory_Model.mk_gamma () in
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
	| LLit (Bool true) -> None, Some LTrue
	| LLit (Bool false) -> None, Some LFalse
	| _ -> Some lexpr, Some (LEq (lexpr, LLit (Bool true))))
and lift_binop_logic_expr op le1 le2 =
	let err_msg = "logical expression binop cannot be lifted to assertion" in
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
		| ((Some le1, _), (Some le2, _)) -> None, Some (l_op_fun le1 le2)
		| (_, _) -> raise (Failure (err_msg ^ " <=#")))
	| And ->
		(match ((f le1), (f le2)) with
		| ((_, Some a1), (_, Some a2)) -> None, Some (LAnd (a1, a2))
		| (_, _) -> raise (Failure err_msg))
	| Or ->
		(match ((f le1), (f le2)) with
		| ((_, Some a1), (_, Some a2)) -> None, Some (LOr (a1, a2))
		| (_, _) -> raise (Failure err_msg))
	| _ -> Some (LBinOp (le1, op, le2)), None)
and lift_unop_logic_expr op le =
	let f = lift_logic_expr in
	let err_msg = "logical expression unop cannot be lifted to assertion" in
	(match op with
	| Not ->
		(match (f le) with
		| (None, Some a) -> None, Some (LNot a)
		| (_, _) -> raise (Failure (err_msg ^ " Not")))
	| _ -> Some (LUnOp (op, le)), None)


let make_all_different_pure_assertion fv_list_1 fv_list_2 : jsil_logic_assertion list =
	let rec all_different_field_against_fv_list f fv_list pfs : jsil_logic_assertion list =
		match fv_list with
		| [] -> pfs
		| (f', v') :: rest ->
			(match f, f' with
			| LLit _, LLit _ -> all_different_field_against_fv_list f rest pfs
			| _, _ -> all_different_field_against_fv_list f rest ((LNot (LEq (f, f'))) :: pfs)) in

	let rec all_different_fv_list_against_fv_list fv_list_1 fv_list_2 pfs : jsil_logic_assertion list =
		(match fv_list_1 with
		| [] -> pfs
		| (f, _) :: rest ->
			let new_pfs = all_different_field_against_fv_list f fv_list_2 pfs in
			all_different_fv_list_against_fv_list rest fv_list_2 new_pfs) in

	all_different_fv_list_against_fv_list fv_list_1 fv_list_2 []

