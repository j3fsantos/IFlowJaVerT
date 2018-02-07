open JSIL_Syntax

(* When reduction fails *)
exception ReductionException of jsil_logic_expr * string

(* What does it mean to be a list? *)
let rec lexpr_is_list (le : jsil_logic_expr) : bool =
	let f = lexpr_is_list in
	match le with
	| PVar _
	| LVar _
	| LLit (LList _)
	| LEList _ -> true
	| LBinOp (_, LstCons, le) -> f le
	| LBinOp (lel, LstCat, ler) -> f lel && f ler
	| _ -> false

(* Finding the length of a list *)
let rec get_length_of_list (lst : jsil_logic_expr) : int option =
	let f = get_length_of_list in

	(* The passed logical expression must represent a list *)
	let _ = assert (lexpr_is_list lst) in

	(match lst with
	| PVar _ -> None
	| LVar _ -> None
	| LLit (LList l) -> Some (List.length l)
	| LEList l -> Some (List.length l)
	| LBinOp (_, LstCons, le) -> Option.map (fun len -> 1 + len) (f le)
	| LBinOp (lel, LstCat, ler) -> Option.default None (Option.map (fun ll -> Option.map (fun lr -> ll + lr) (f ler)) (f lel)) 
	| _ -> raise (Failure (Printf.sprintf "find_length_of_list: list equals %s, impossible" (JSIL_Print.string_of_logic_expression lst)))
	)

(* Finding the nth element of a list *)
let rec get_nth_of_list (lst : jsil_logic_expr) (idx : int) : jsil_logic_expr option =
	let f = get_nth_of_list in

	(* The passed logical expression must represent a list *)
	assert (lexpr_is_list lst);

	let err_msg = "find_nth_in_list: index out of bounds." in

	(* If we can compute the length of the list, then the index needs to be compatible *)
	let olen = get_length_of_list lst in
	let _ = match olen with
		| None -> ()
		| Some len -> if (len <= idx) then raise (ReductionException (LNone, err_msg))
	in

	let result : jsil_logic_expr option = (match lst with
	(* Nothing can be done for variables *)
	| PVar _ -> None
	| LVar _ -> None
	(* Base lists of literals and logical expressions *)
	| LLit (LList l) -> assert (idx < List.length l); Some (LLit (List.nth l idx))
	| LEList l       -> assert (idx < List.length l); Some (List.nth l idx)
	| LBinOp (_, LstCons, lst) -> 
		if (idx = 0) 
			then raise (ReductionException (LNone, err_msg))
			else f lst (idx - 1)
	| LBinOp (lel, LstCat, ler) ->
		Option.default None 
			(Option.map 
				(fun llen -> 
					let lst, idx = if (idx < llen) then lel, idx else ler, (idx - llen) in
						f lst idx)
				(get_length_of_list lel)
			)

	| _ -> raise (Failure (Printf.sprintf "find_nth_in_list: list equals %s, impossible" (JSIL_Print.string_of_logic_expression lst)))
	) in result


(*)
		| LBinOp (le, LstCons, list), LLit (Num n) ->
			print_debug_petar (Printf.sprintf "Cons: %s %s %f" (string_of_logic_expression le) (string_of_logic_expression list) n);
			if (Utils.is_int n) then
		  let ni = int_of_float n in
			 (match (ni = 0) with
		   | true -> print_debug_petar (Printf.sprintf "ni = 0, calling recursively with %s" (string_of_logic_expression le)); f le
		   | false -> f (LLstNth (f list, LLit (Num (n -. 1.)))))
			else
					raise (Failure (Printf.sprintf "Non-integer list index: %f" n)) *)

(**
	Logical expression reduction - there is no additional information
*)
let rec reduce_lexpr (le : jsil_logic_expr) = 
	let f = reduce_lexpr in
	(match le with

	(* The TypeOf operator *)
	| LTypeOf le -> 
		let fle = f le in 
		(match fle with
		| LLit lit             -> LLit (Type (Literal.type_of lit)) (* Types of literals can always be evaluated             *)
		| ALoc   _             -> LLit (Type ObjectType)            (* Abstract locations are always of type Object          *)
		| LEList _             -> LLit (Type ListType)              (* Logical lists are always of type List                 *)
		| LESet  _             -> LLit (Type SetType)               (* Logical sets are always of type Set                   *)
		| LNone                -> LLit (Type NoneType)              (* The logical value None is of type None                *)
		| LBinOp (_, Equal, _) -> LLit (Type BooleanType)           (* Equality is always of type Boolean                    *)
		| _                    -> LTypeOf fle                       (* The remaining cases cannot be conclusively determined *)
		)

	(* Base lists, character lists, and sets are reduced pointwise *)
	| LEList les -> LEList (List.map f les)
	| LCList les -> LCList (List.map f les)
	| LESet  les -> LESet  (List.map f les)

	(* List indexing *)
	| LLstNth (le, idx) ->
		let fle = f le  in
		let fidx = f idx in
		(match fidx with
		(* Index is a non-negative integer *)
		| LLit (Num n) when (Utils.is_int n && 0. <= n) ->
			(match (lexpr_is_list fle) with
			| true -> Option.default (LLstNth (fle, fidx)) (get_nth_of_list fle (int_of_float n))
			| false -> 
				let err_msg = "LstNth(list, index): list is not a JSIL list." in
				raise (ReductionException (LLstNth (fle, fidx), err_msg))
			)

		(* Index is a number, but is either not an integer or is negative *)
		| LLit (Num n) -> 
			let err_msg = "LstNth (list, index): index is non-integer or smaller than zero." in
			raise (ReductionException (LLstNth (fle, fidx), err_msg))

		(* All other cases *)
		| _ -> LLstNth (fle, fidx)
		)

	(* The remaining cases cannot be reduced *)
	| _ -> le 
	)