open JSIL_Syntax

(* Shorthand for printing logical expressions *)
let print_lexpr le = JSIL_Print.string_of_logic_expression le false 

(* What does it mean to be a list? *)
let rec isList (le : jsil_logic_expr) : bool =
(match le with
	| LVar _ 
	| LLit (LList _)
	| LEList _ -> true
	| LBinOp (_, LstCons, le) -> isList le
	| LBinOp (lel, LstCat, ler) -> isList lel && isList ler
	| _ -> false)

(* Arranging lists in a specific order *)
let arrange_lists (le1 : jsil_logic_expr) (le2 : jsil_logic_expr) : (jsil_logic_expr * jsil_logic_expr) =
	if (isList le1 && isList le2) then
	(match le1, le2 with
	  | LVar _, _
		| LLit (LList _), LLit (LList _) 
		| LLit (LList _), LEList _
		| LLit (LList _), LBinOp (_, LstCons, _)
		| LLit (LList _), LBinOp (_, LstCat, _)
		| LEList _, LEList _
		| LEList _, LBinOp (_, LstCons, _)
		| LEList _, LBinOp (_, LstCat, _)
		| LBinOp (_, LstCons, _), LBinOp (_, LstCons, _)
		| LBinOp (_, LstCons, _), LBinOp (_, LstCat, _)
		| LBinOp (_, LstCat, _), LBinOp (_, LstCat, _) -> le1, le2
		| _, _ -> le2, le1
	) else
		let msg = Printf.sprintf "Non-list expressions passed to arrange_lists : %s, %s" (print_lexpr le1) (print_lexpr le2) in
		raise (Failure msg)

(* Extracting elements from a list *)
let rec get_elements_from_list (le : jsil_logic_expr) : jsil_logic_expr list =
(match le with
	| LVar _ -> []
	| LLit (LList l) -> List.map (fun e -> LLit e) l
	| LEList l -> l
	| LBinOp (e, LstCons, le) -> e :: get_elements_from_list le
	| LBinOp (lel, LstCat, ler) -> get_elements_from_list lel @ get_elements_from_list ler
	| _ -> let msg = Printf.sprintf "Non-list expressions passed to get_elements_from_list : %s" (print_lexpr le) in
		raise (Failure msg))

(* Separating a list into a head and a tail *)
let rec get_head_and_tail (le : jsil_logic_expr) : bool option * jsil_logic_expr * jsil_logic_expr =
(match le with
	| LLit (LList l) ->
		(match l with
		| [] -> None, LLit (Bool false), LLit (Bool false)
		| e :: l -> Some true, LLit e, LLit (LList l))
	| LEList l ->
		(match l with
		| [] -> None, LLit (Bool false), LLit (Bool false)
		| e :: l -> Some true, e, LEList l)
	| LBinOp (e, LstCons, l) -> Some true, e, l
	| LBinOp (l1, LstCat, l2) -> 
		let ok, head, tail = get_head_and_tail l1 in
		(match ok with
		| None -> None, LLit (Bool false), LLit (Bool false)
		| Some false -> Some false, LLit (Bool false), LLit (Bool false)
		| Some true -> Some true, head, LBinOp (tail, LstCat, l2))
	| LVar _ -> Some false, LLit (Bool false), LLit (Bool false)
	| _ -> 
		let msg = Printf.sprintf "Non-list expressions passed to get_head_and_tail : %s" (print_lexpr le) in
		raise (Failure msg))

(* TODO: IMPROVE THIS *)
let list_split (l : 'a list) (e : 'a) = 
(match (List.mem e l) with
| false -> false, ([], [])
| true ->
	let m = DynArray.index_of (fun x -> x = e) (DynArray.of_list l) in
	let llen = List.length l in
	let al = Array.of_list l in
	let ll = Array.to_list (Array.sub al 0 m) in
	let lr = Array.to_list (Array.sub al (m + 1) (llen - m - 1)) in
		true, (ll, lr))

(* Splitting a list based on an element *)
let rec split_list_on_element (le : jsil_logic_expr) (e : jsil_logic_expr) : bool * (jsil_logic_expr * jsil_logic_expr) =
(match le with
	| LVar _ -> false, (le, LEList [])
	| LLit (LList l) -> 
		(match e with
		| LLit lit ->
			let ok, (ll, lr) = list_split l lit in
			(match ok with
			| true -> true, (LLit (LList ll), LLit (LList lr))
			| false -> false, (le, LEList [])
		| _ -> false, (le, LEList [])))
  | LEList l ->
			let ok, (ll, lr) = list_split l e in
			(match ok with
			| true -> true, (LEList ll, LEList lr)
			| false -> false, (le, LEList []))
	| LBinOp (e', LstCons, le') -> 
		(match (e = e') with
		| true -> true, (LEList [], le')
		| false -> let ok, (ll, lr) = split_list_on_element le' e in
			(match ok with
			| false -> false, (le, LEList [])
			| true -> true, (LBinOp (e', LstCons, ll), lr)))
	| LBinOp (lel, LstCat, ler) -> 
		let ok, (lll, llr) = split_list_on_element lel e in
		(match ok with
		| true -> 
			let right = (match ler with 
			| LLit (LList [])
			| LEList [] -> llr
			| _ -> LBinOp (llr, LstCat, ler)) in
				true, (lll, right)
		| false -> let ok, (lrl, lrr) = split_list_on_element ler e in
			(match ok with
			| true -> 
				let left = (match lrl with 
				| LLit (LList [])
				| LEList [] -> lel
				| _ -> LBinOp (lel, LstCat, lrl)) in
					true, (left, lrr)
			| false -> false, (le, LEList [])))
	| _ -> let msg = Printf.sprintf "Non-list expressions passed to split_list_on_element : %s" (print_lexpr le) in
		raise (Failure msg))

(* Unifying lists based on a common literal *)
let match_lists_on_element (le1 : jsil_logic_expr) (le2 : jsil_logic_expr) : bool * (jsil_logic_expr * jsil_logic_expr) * (jsil_logic_expr * jsil_logic_expr) =
	let elems1 = get_elements_from_list le1 in
	(match elems1 with
	| [] -> false, (LLit (Bool false), LLit (Bool false)), (LLit (Bool false), LLit (Bool false))
	| _ ->
		let elems2 = get_elements_from_list le2 in
		(match elems2 with
		| [] -> false, (LLit (Bool false), LLit (Bool false)), (LLit (Bool false), LLit (Bool false))
		| _ -> 
			let intersection = List.fold_left (fun ac x -> 
				if (List.mem x elems1) then ac @ [x] else ac) [] elems2 in
			(match intersection with
			| [] -> false, (LLit (Bool false), LLit (Bool false)), (LLit (Bool false), LLit (Bool false))
			| i :: _ ->
				let ok1, (l1, r1) = split_list_on_element le1 i in
				let ok2, (l2, r2) = split_list_on_element le2 i in
				(match ok1, ok2 with
				| true, true -> true, (l1, r1), (l2, r2) 
				| _, _ -> let msg = Printf.sprintf "Element %s that was supposed to be in both lists: %s, %s is not." (print_lexpr i) (print_lexpr le1) (print_lexpr le2) in
						raise (Failure msg)))
		))

(* List unification *)
let rec unify_lists (le1 : jsil_logic_expr) (le2 : jsil_logic_expr) : bool option * ((jsil_logic_expr * jsil_logic_expr) list) = 
	let le1, le2 = arrange_lists le1 le2 in
	(match le1, le2 with
	  (* Base cases *)
	  | LLit (LList []), LLit (LList [])
		| LLit (LList []), LEList []
		| LEList [], LEList [] -> Some false, []
		| LVar _, _ -> Some false, [ (le1, le2) ]
		(* Inductive cases *)
		| LLit (LList _), LLit (LList _)
		| LLit (LList _), LEList _
		| LEList _, LEList _
		| LLit (LList _), LBinOp (_, LstCons, _) 
		| LLit (LList _), LBinOp (_, LstCat, _)
		| LEList _, LBinOp (_, LstCons, _)
		| LEList _, LBinOp (_, LstCat, _)
		| LBinOp (_, LstCons, _), LBinOp (_, LstCons, _)
		| LBinOp (_, LstCons, _), LBinOp (_, LstCat, _)
		| LBinOp (_, LstCat, _), LBinOp (_, LstCat, _) -> 
			let (okl, headl, taill) = get_head_and_tail le1 in
			let (okr, headr, tailr) = get_head_and_tail le2 in
			(match okl, okr with
			(* We can separate both lists *)
			| Some true, Some true ->
				(* Do we still have lists? *)
				if (isList taill && isList tailr) then
					(* Yes, move in recursively *)
					(let ok, rest = unify_lists taill tailr in
					(match ok with
					| None -> None, []
					| _ -> Some true, (headl, headr) :: rest))
				else
					(* No, we are done *)
					Some true, [ (headl, headr); (taill, tailr) ]
			(* Not enough information to separate head and tail *)
			| Some true, Some false
			| Some false, Some true 
			| Some false, Some false -> 
					(* This means that we have on at least one side a LstCat with a leading variable and we need to dig deeper *)
					(* Get all literals on both sides, find first match, then split and call again *)
						let ok, (ll, lr), (rl, rr) = match_lists_on_element le1 le2 in
						(match ok with
						| true -> 
								let okl, left = unify_lists ll rl in
								(match okl with
								| None -> None, []
								| _ -> 
									let okr, right = unify_lists lr rr in
									(match okr with
									| None -> None, []
									| _ -> Some true, left @ right))
						| false -> Some false, [ (le1, le2) ])
			(* A proper error occurred while getting head and tail *)
			| _, _ -> None, [])
		| _, _ ->
			let msg = Printf.sprintf "Non-arranged lists passed to unify_lists : %s, %s" (print_lexpr le1) (print_lexpr le2) in
			raise (Failure msg)
	)

(*
let print_result_of_list_unification le1 le2 ob uni_list =
	Printf.printf "\nList unification:\n\t%s\n\t\tvs.\n\t%s\nResult:\n%s\n" (print_lexpr le1) (print_lexpr le2)
	(match ob with
	| None -> "Horrible failure"
	| Some false -> "No changes made."
	| _ -> String.concat "\n" (List.map (fun (x, y) -> Printf.sprintf "%s = %s" (print_lexpr x) (print_lexpr y)) uni_list))

let test_list_unification le1 le2 = 	
	let le1, le2 = arrange_lists le1 le2 in
	let ob, uni_list = unify_lists le1 le2 in
	print_result_of_list_unification le1 le2 ob uni_list
	
let _ = 
	let le1 = LLit (LList [Num 3.; Bool true; String "flarb"]) in
	let le2 = LEList [ LVar "x"; LVar "y"; LVar "z" ] in
	test_list_unification le1 le2;
	
	let le1 = LEList [ LVar "x"; LVar "y"; LVar "z" ] in
	let le2 = LBinOp ( LVar "v", LstCons, LVar "w" ) in
	test_list_unification le1 le2;
	
	let le1 = LEList [ LVar "x"; LVar "y"; LVar "z" ] in
	let le2 = LEList [ LVar "x"; LVar "y" ] in
	test_list_unification le1 le2;

	let le1 = LEList [ LVar "x"; LVar "y"; LVar "z" ] in
	let le2 = LBinOp ( LVar "v", LstCat, LVar "w" ) in
	test_list_unification le1 le2;
	
	let le1 = LEList [ LVar "x"; LVar "y"; LVar "w"; LVar "t"; LVar "u" ] in
	let le2 = LBinOp ( LVar "v", LstCat, LBinOp (LVar "w", LstCons, LVar "z")) in
	test_list_unification le1 le2;
	
	let le1 = LBinOp (LBinOp ( LEList [ LVar "x"; LVar "y" ], LstCat, LBinOp (LVar "w", LstCons, LEList [ LVar "t"; LVar "u" ])), LstCat, LBinOp ( LEList [ LVar "x"; LVar "y" ], LstCat, LBinOp (LVar "w", LstCons, LEList [ LVar "t"; LVar "u" ]))) in
	let le2 = LBinOp ( LVar "v", LstCat, LBinOp (LVar "w", LstCons, LVar "z")) in
	test_list_unification le1 le2
*)