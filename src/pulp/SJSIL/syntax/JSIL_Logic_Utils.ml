open DynArray
open Set
open Stack
open JSIL_Syntax


let fresh_sth (name : string) : (unit -> string) =
  let counter = ref 0 in
  let rec f () =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f
  

let abs_loc_prefix = "_$l_"
let lvar_prefix = "_lvar_"

let fresh_aloc = fresh_sth abs_loc_prefix 
let fresh_lvar = fresh_sth lvar_prefix 

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
	| LEVRef	(e1, e2) 
	| LEORef (e1, e2) -> f e1; f e2
	| LBase e1 
	| LField e1
	| LTypeOf e1 -> f e1 
	| LEList le_list -> List.iter (fun le -> f le) le_list 
	| LLstNth (e1, e2) 
	| LStrNth (e1, e2) -> f e1; f e2


let get_assertion_vars ass catch_pvars = 
	let vars_tbl = Hashtbl.create 101 in 
	let rec get_ass_vars_iter ass = 
		let f = get_ass_vars_iter in 
		let fe = get_expr_vars vars_tbl catch_pvars in  
		match ass with 
		| LAnd (_, _) -> raise (Failure "Unsupported assertion during normalization: LAnd")
		| LOr (_, _) -> raise (Failure "Unsupported assertion during normalization: LOr")
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
		| LTypes _ 
		| LPred (_, _) -> () in 
	get_ass_vars_iter ass; 
	vars_tbl 


let get_expr_vars_lst le catch_p_vars =
	let vars_tbl = Hashtbl.create 31 in
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
			


let rec push_in_negations_off a =
	let err_msg = "Normalize pure assertion got inpure argument" in 
	let f_off = push_in_negations_off in 
	let f_on = push_in_negations_on in
	(match a with 
	| LAnd (a1, a2) -> LAnd ((f_off a1), (f_off a2))
	| LOr (a1, a2) -> LOr ((f_off a1), (f_off a2))
	| LNot a1 -> f_on a1
	| LTrue 
	| LFalse
	| LEq (_, _)
	| LLess (_, _)
	| LLessEq (_, _) 
	| LStrLess (_, _) 
	| LPred (_, _) -> a 
	| _ -> raise (Failure err_msg))
and push_in_negations_on a = 
	let err_msg = "Normalize pure assertion got inpure argument" in 
	let f_off = push_in_negations_off in
	let f_on = push_in_negations_on in 
	(match a with 
	|	LAnd (a1, a2) -> LOr ((f_on a1), (f_on a2)) 
	| LOr (a1, a2) -> LAnd ((f_on a1), (f_on a2)) 
	| LTrue -> LFalse 
	| LFalse -> LTrue 
	| LEq (_, _)
	| LLess (_, _)
	| LLessEq (_, _) 
	| LStrLess (_, _) 
	| LPred (_, _) -> LNot a 
	| _ -> raise (Failure err_msg))	



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
	let err_msg = "Normalize pure assertion got inpure argument" in 
	match a with 
	| LAnd (a1, a2) -> cross_product (f a1) (f a2) 
	| LOr (a1, a2) -> List.append (f a1) (f a2) 
	| LTrue -> []
	| LFalse
	| LEq (_, _)
	| LLess (_, _)
	| LLessEq (_, _) 
	| LStrLess (_, _) 
	| LPred (_, _) -> [[ a ]]
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


let normalize_pure_assertion a = 
	let a = push_in_negations_off a in 
	let a = build_disjunt_normal_form a in 
	remove_falses a
	

let rec lexpr_substitution lexpr subst normalize = 
	let f e = lexpr_substitution e subst normalize in 
	match lexpr with 
	| LLit lit -> LLit lit 
	
	| LNone -> LNone
	
	| LVar var -> 
			(try Hashtbl.find subst var with _ -> 
				if (normalize) 
					then 
						let new_var = fresh_lvar () in 
						Hashtbl.replace subst var (LVar new_var);
						LVar new_var
					else (LVar var))
	
	| ALoc aloc -> (try Hashtbl.find subst aloc with _ -> ALoc (fresh_aloc ())) 
								
	| PVar var -> 
			if (normalize) 
				then raise (Failure "Illegal program variable in logical expression. lexpr_substitution requires its argument to be normalized.")
				else (PVar var) 
				
	| LBinOp (le1, op, le2) -> LBinOp ((f le1), op, (f le2)) 
	
	| LUnOp (op, le) -> LUnOp (op, (f le)) 
	
	| LEVRef (le1, le2) -> LEVRef ((f le1), (f le2))
	
	| LEORef (le1, le2) -> LEORef ((f le1), (f le2))
	
	| LBase le -> LBase	(f le)

	| LField le -> LField (f le)

	| LTypeOf le -> LTypeOf (f le) 
	
	| LEList les -> 
		let s_les = List.map (fun le -> (f le)) les in 
		LEList s_les
	
	| LLstNth (le1, le2) -> LLstNth ((f le1), (f le2))
	
	| LStrNth (le1, le2) -> LStrNth ((f le1), (f le2))
	
	| LUnknown -> LUnknown 


let rec assertion_substitution a subst normalize = 
	let fa a = assertion_substitution a subst normalize in 
	let fe e = lexpr_substitution e subst normalize in 
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
	let new_subst = Hashtbl.create ((List.length vars) + 3) in 
	Hashtbl.iter 
		(fun var _ -> Hashtbl.add new_subst var true)
		subst; 
	new_subst



