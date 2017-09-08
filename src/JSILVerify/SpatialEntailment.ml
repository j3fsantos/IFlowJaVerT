open JSIL_Syntax
open JSIL_Print
open Symbolic_State
open JSIL_Logic_Utils

exception UnificationFailure of unit 

type discharge_list    = ((jsil_logic_expr * jsil_logic_expr) list)



let rec unify_lexprs_rec 
	(pfs         : pure_formulae) 
	(gamma       : typing_environment) 
	(subst       : substitution)
	(le_pat      : jsil_logic_expr) 
	(le          : jsil_logic_expr) : substitution_list * discharge_list =

	let u_lexprs = unify_lexprs_rec pfs gamma subst in 

	let start_time = Sys.time () in
	print_debug_petar (Printf.sprintf "unify_lexprs: %s versus %s" 
		(JSIL_Print.string_of_logic_expression le_pat false)  
		(JSIL_Print.string_of_logic_expression le false));

	let get_rest (le : jsil_logic_expr) : jsil_logic_expr = 
		match le with
			| LEList lst -> []
			| LBinOp (LEList lst, LstCat, rest) -> rest
			| _ -> raise (Failure ("DEATH. unify_lexprs. get_pat_rest")) in 

	match le_pat with
		| LVar x
		| ALoc x ->
			(try
				let s_le_pat = Hashtbl.find subst x in
				if (Pure_Entailment.is_equal s_le_pat le pfs gamma)
					then []
					else raise UnificationFailure
			with _ -> [ (x, le) ])

		| LLit _
		| LNone -> if (Pure_Entailment.is_equal le_pat le pfs gamma) 
			then [] 
			else raise UnificationFailure

		| LEList pat_lst 
		| LBinOp (LEList pat_lst, LstCat, _) ->
			let pat_rest = get_rest le_pat in 
			(match le with 
			| LEList lst 
			| LBinOp (LEList lst, LstCat, _) -> 
				let rest = get_rest le in
				let diff = (List.length lst) - (List.length pat_lst) in    
				let lst, rest = 
					if (diff = 0) then (lst, rest) 
					else if (diff > 0) then (
						let lst_hd, lst_tl = sub_list lst (List.length lst) in 
						lst_hd, LBinOp (LEList lst_tl, LstCat, rest)
					) else raise UnificationFailure in 
				let subst_lst, discharges_lst = List.split (List.map2 u_lexprs pat_lst lst) in 
				List.concat subst_lst, List.concat discharges_lst
			| LVar x -> 
				(match find_le_list_in_pfs pfs x with 
				| None     -> [], [ (le_pat, LVar x) ]
				| Some le' -> u_lexprs le_pat le') 
			| _      -> [], [ (le_pat, LVar x) ])

		| _ -> [], [ (le_pat, LVar x) ]


(** 
  *  Checks whether or not a substitution list is consistent. 
  *  If the same variable is mapped to two different logical expressions
  *  in a substitution list, then these expressions MUST be equal up to pfs. 
  *)
let consistent_subst_list 
		(subst_list : substitution_list) 
		(pfs        : pure_formulae)
		(gamma      : typing_environment) : substitution_list option = 

	let subst = Hashtbl.create small_tbl_size in
	List.fold_left (fun o_subst_list (x, le) -> 
		match o_subst_list with 
		| None -> None 
		| Some subst_list -> 
			try 
				let le_x = Hasthtbl.find var x in 
				if (Pure_Entailment.is_equal le_x le pfs gamma)
					then Some subst_list
					else None
			with _ ->
				Hashtbl.replace vars x le;
				Some ((x, le) :: subst_list) 
	) subst_list





let rec unify_lexprs
	(pfs         : pure_formulae) 
	(gamma       : typing_environment) 
	(subst       : substitution)
	(le_pat      : jsil_logic_expr) 
	(le          : jsil_logic_expr) : (substitution_list * discharge_list) option =

	let le_pat = normalise_list_expressions le_pat in
	let le     = normalise_list_expressions le in 
	
	try (
		let subst_list, discharges = unify_lexprs_rec pfs gamma subst le_pat le in 
		match (consistent_subst_list subst_list), (pre_check_discharges discharges) with 
			| Some subst_list, Some discharges -> Some (subst_list, discharges)
			| _, _                             -> None 
	) with UnificationFailure -> None 








