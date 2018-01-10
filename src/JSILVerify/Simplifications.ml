open JSIL_Syntax
open JSIL_Logic_Utils
open Symbolic_State
open JSIL_Print 
open Symbolic_State_Print

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


let simplify_equalities_between_booleans (p_assertions : pure_formulae) = 
 	let new_as = 
 		DynArray.map 
 			(fun a -> 
 				match a with 
 				| LEq (le, LLit (Bool false))
 				| LEq (LLit (Bool false), le) -> 
 					(* do something *)
 					let _, as_le = lift_logic_expr le in
 					(match as_le with 
 					| Some (_, a_not_le) -> a_not_le 
 					| None -> a)   
 				| LEq (le, LLit (Bool true))
 				| LEq (LLit (Bool true), le) -> 
 					let _, as_le = lift_logic_expr le in
 					(match as_le with 
 					| Some (a_le, _) -> a_le 
 					| None -> a)
 				| _ -> a) p_assertions in 
 	new_as 

let naively_infer_type_information (p_assertions : pure_formulae) (gamma : typing_environment) = 
 	DynArray.iter 
 		(fun a -> 
 			match a with 
 			| LEq (LVar x, le) 
 			| LEq (le, LVar x) -> 
 				if (not (Hashtbl.mem gamma x)) 
 					then (
 						let le_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
 						weak_update_gamma gamma x le_type
 					)
 			| LEq ((LTypeOf (LVar x)), (LLit (Type t))) 
 			| LEq ((LLit (Type t)), (LTypeOf (LVar x))) ->
 				weak_update_gamma gamma x (Some t)
 			| _ -> () 
 		) p_assertions


 let naively_infer_type_information_symb_state (symb_state : symbolic_state) = 
 	let gamma = ss_gamma symb_state in 
 	let pfs = ss_pfs symb_state in 
 	naively_infer_type_information pfs gamma

(*************************************)
(** Symbolic state simplification   **)
(*************************************)


let reduce_pfs_no_store_no_gamma pfs = DynArray.map (fun x -> reduce_assertion_no_store_no_gamma pfs x) pfs
let reduce_pfs_no_store    gamma pfs = DynArray.map (fun x -> reduce_assertion_no_store    gamma pfs x) pfs
let reduce_pfs    store    gamma pfs = DynArray.map (fun x -> reduce_assertion    store    gamma pfs x) pfs

let reduce_pfs_in_place store gamma pfs =
	DynArray.iteri (fun i pf ->
		let rpf = reduce_assertion store gamma pfs pf in
		DynArray.set pfs i rpf) pfs
	
let sanitise_pfs store gamma pfs =
	
	reduce_pfs_in_place store gamma pfs;

	(* let i = ref 0 in
	while (!i < DynArray.length pfs) do
		let pf = DynArray.get pfs !i in
		(match pf with
		| LAnd (a1, a2) ->
				DynArray.delete pfs !i;
				DynArray.add pfs a1;
				DynArray.add pfs a2;
		| _ -> i := !i + 1)
	done; *)
			
	let length = DynArray.length pfs in
	let dindex = DynArray.init length (fun x -> false) in
	let clc = ref 0 in
	let rec find_duplicates l =
		(match l with
		| [] -> ()
		| a :: l ->
			let imem = List.mem a l in
			(if (imem || (a = LTrue)) then
				DynArray.set dindex !clc true);
			clc := !clc + 1;
			find_duplicates l) in
	let ll = DynArray.to_list pfs in
	find_duplicates ll;
	for i = 0 to (length - 1) do
		if (DynArray.get dindex (length - 1 - i))
			then DynArray.delete pfs (length - 1 - i)
	done

let sanitise_pfs_no_store_no_gamma = sanitise_pfs (Hashtbl.create 1) (Hashtbl.create 1)
let sanitise_pfs_no_store          = sanitise_pfs (Hashtbl.create 1)

let allowedListMember le =
(match le with
 | LLit _ -> true
 | ALoc _ -> true
 | LVar var -> true
 | _ -> false)

let rec isSubstitutable le =
(match le with
 | LLit _ -> true
 | ALoc _ -> true
 | LEList lst ->
     List.fold_left (fun ac x -> ac && allowedListMember x) true lst
 | LBinOp (le, LstCons, lst) ->
     allowedListMember le && isSubstitutable lst
 | _ -> false
)

let rec isExistentiallySubstitutable le =
(match le with
 | LLit _ -> true
 | ALoc _ -> true
 | LVar _ -> true
 | LEList les -> List.fold_left
     (fun ac x -> ac && isExistentiallySubstitutable x) true les
 | LBinOp (le, LstCons, les) -> isExistentiallySubstitutable le && isExistentiallySubstitutable les
 | LBinOp (lel, StrCat, ler) -> isExistentiallySubstitutable lel && isExistentiallySubstitutable ler
 | _ -> false
)

let get_lvars_pfs pfs =
	List.fold_left
		(fun lvars pf -> 
			let lvs = get_asrt_lvars pf in
				SS.union lvars lvs)
		SS.empty (DynArray.to_list pfs)
	
let filter_gamma_pfs pfs gamma = 
	let pfs_vars = pfs_lvars pfs in
	Hashtbl.filter_map_inplace 
		(fun k v -> if (SS.mem k pfs_vars) then Some v else None) 
		gamma
	
(*
	SIMPLIFICATION AND MORE INFORMATION
	===================================
*)


(* ***** *
 *       *
 * LISTS *
 *       *
 * ***** *)

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
		let msg = Printf.sprintf "Non-list expressions passed to arrange_lists : %s, %s" (string_of_logic_expression le1) (string_of_logic_expression le2) in
		raise (Failure msg)

(* Extracting elements from a list *)
let rec get_elements_from_list (le : jsil_logic_expr) : jsil_logic_expr list =
(match le with
	| LVar _ -> []
	| LLit (LList l) -> List.map (fun e -> LLit e) l
	| LEList l -> l
	| LBinOp (e, LstCons, le) -> e :: get_elements_from_list le
	| LBinOp (lel, LstCat, ler) -> get_elements_from_list lel @ get_elements_from_list ler
	| _ -> let msg = Printf.sprintf "Non-list expressions passed to get_elements_from_list : %s" (string_of_logic_expression le) in
		raise (Failure msg))

(* Separating a list into a head and a tail *)
let rec get_head_and_tail_list (le : jsil_logic_expr) : bool option * jsil_logic_expr * jsil_logic_expr =
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
		let ok, head, tail = get_head_and_tail_list l1 in
		(match ok with
		| None -> None, LLit (Bool false), LLit (Bool false)
		| Some false -> Some false, LLit (Bool false), LLit (Bool false)
		| Some true -> Some true, head, LBinOp (tail, LstCat, l2))
	| LVar _ -> Some false, LLit (Bool false), LLit (Bool false)
	| _ -> 
		let msg = Printf.sprintf "Non-list expressions passed to get_head_and_tail_list : %s" (string_of_logic_expression le) in
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
	| _ -> let msg = Printf.sprintf "Non-list expressions passed to split_list_on_element : %s" (string_of_logic_expression le) in
		raise (Failure msg))

let crossProduct l l' = List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) l') l)

(* Unifying lists based on a common literal *)
let rec match_lists_on_element (le1 : jsil_logic_expr) (le2 : jsil_logic_expr) : 
	bool * (jsil_logic_expr * jsil_logic_expr) * (jsil_logic_expr * jsil_logic_expr) * (jsil_logic_expr * jsil_logic_expr) option =
	let elems1 = get_elements_from_list le1 in
	(match elems1 with
	| [] -> false, (LLit (Bool false), LLit (Bool false)), (LLit (Bool false), LLit (Bool false)), None
	| _ ->
		let elems2 = get_elements_from_list le2 in
		(match elems2 with
		| [] -> false, (LLit (Bool false), LLit (Bool false)), (LLit (Bool false), LLit (Bool false)), None
		| _ -> 
			(* print_debug_petar (Printf.sprintf "LEL: %s\nREL: %s"
				(String.concat ", " (List.map (fun x -> string_of_logic_expression x) elems1))	
				(String.concat ", " (List.map (fun x -> string_of_logic_expression x) elems2))	
			); *)
			let intersection = List.fold_left (fun ac x -> 
				if (List.mem x elems1) then ac @ [x] else ac) [] elems2 in
			let intersection, list_unification = (match intersection with
			| [] -> 
					let candidates = crossProduct elems1 elems2 in
					let candidates = List.map (fun (le1, le2) ->
						let result = 
						(match isList le1, isList le2 with
						| true, true -> 
								let unifiable, _ = unify_lists le1 le2 false in
								(unifiable <> None)
						| _, _ -> false) in (le1, le2, result)) candidates in
					let candidates = List.filter (fun (_, _, b) -> b) candidates in
					(match candidates with 
					| [] -> None, None
					| [ (le1, le2, _) ] -> Some (le1, le2), Some (le1, le2)
					| _ -> 
						let lcand = List.length candidates in
						let sqrtl = sqrt (float_of_int lcand) in
						if (!interactive) && (not (sqrtl = floor sqrtl)) then (
							print_debug_petar (Printf.sprintf "Actually, we've got %d candidates for this unification.\n%!" (List.length candidates));
							Printf.eprintf "Actually, we've got %d candidates for this unification.\n%!" (List.length candidates);
							List.iter (fun (le1, le2, _) -> 
								Printf.eprintf "%s vs. %s\n%!" (string_of_logic_expression le1) (string_of_logic_expression le2)) candidates;
							Printf.eprintf "Choose: ";
							let n = read_int() in
							let le1, le2, _ = DynArray.get (DynArray.of_list candidates) n in
								Some (le1, le2), Some (le1, le2)) 
							else
						 	let le1, le2, _ = List.hd candidates in 
								Some (le1, le2) , Some (le1, le2))
			| i :: _ -> Some (i, i), None) in
			(match intersection with
			| None -> false, (LLit (Bool false), LLit (Bool false)), (LLit (Bool false), LLit (Bool false)), None
			| Some (i, j) ->
				(* print_debug_petar (Printf.sprintf "(Potential) Intersection: %s, %s" (string_of_logic_expression i) (string_of_logic_expression j)); *)
				let ok1, (l1, r1) = split_list_on_element le1 i in
				let ok2, (l2, r2) = split_list_on_element le2 j in
				(match ok1, ok2 with
				| true, true -> true, (l1, r1), (l2, r2), list_unification
				| _, _ -> let msg = Printf.sprintf "Element %s that was supposed to be in both lists: %s, %s is not." (string_of_logic_expression i) (string_of_logic_expression le1) (string_of_logic_expression le2) in
						raise (Failure msg)))
		))
and
unify_lists (le1 : jsil_logic_expr) (le2 : jsil_logic_expr) to_swap : bool option * ((jsil_logic_expr * jsil_logic_expr) list) = 
	let le1 = reduce_expression_no_store_no_gamma_no_pfs le1 in
	let le2 = reduce_expression_no_store_no_gamma_no_pfs le2 in
	let le1_old = le1 in
	let le1, le2 = arrange_lists le1 le2 in
	let to_swap_now = (le1_old <> le1) in
	let to_swap = (to_swap <> to_swap_now) in
	let swap (le1, le2) = if to_swap then (le2, le1) else (le1, le2) in
	print_debug_petar (Printf.sprintf "unify_lists: \n\t%s\n\t\tand\n\t%s" 
		(string_of_logic_expression le1) (string_of_logic_expression le2)); 
	(match le1, le2 with
	  (* Base cases *)
	  | LLit (LList []), LLit (LList [])
		| LLit (LList []), LEList []
		| LEList [], LEList [] -> Some false, []
		| LVar _, _ -> Some false, [ swap (le1, le2) ]
		(* Inductive cases *)
		| LBinOp (l1, LstCat, LEList [ e1 ]), LBinOp (l2, LstCat, LEList [ e2 ]) ->
				let ok, rest = unify_lists l1 l2 to_swap in
				(match ok with
				| None -> None, []
				| _ -> Some true, (e1, e2) :: rest)
		
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
			let (okl, headl, taill) = get_head_and_tail_list le1 in
			let (okr, headr, tailr) = get_head_and_tail_list le2 in
			(* print_debug_petar (Printf.sprintf "Got head and tail: left: %b, right: %b" 
				(Option.map_default (fun v -> v) false okl) (Option.map_default (fun v -> v) false okr)); *)
			(match okl, okr with
			(* We can separate both lists *)
			| Some true, Some true ->
				(* Do we still have lists? *)
				if (isList taill && isList tailr) then
					(* Yes, move in recursively *)
					(let ok, rest = unify_lists taill tailr to_swap in
					(match ok with
					| None -> None, []
					| _ -> Some true, swap (headl, headr) :: rest))
				else
					(* No, we are done *)
					Some true, [ swap (headl, headr); (taill, tailr) ]
			(* Not enough information to separate head and tail *)
			| Some _, Some _ -> 
				(* This means that we have on at least one side a LstCat with a leading variable and we need to dig deeper *)
				(* Get all literals on both sides, find first match, then split and call again *)
				let ok, (ll, lr), (rl, rr), more_to_unify = match_lists_on_element le1 le2 in
				(match ok with
					| true -> 
							let okl, left = unify_lists ll rl to_swap in
							(match okl with
							| None -> None, []
							| _ -> 
								let okr, right = unify_lists lr rr to_swap in
								(match okr with
								| None -> None, []
								| _ -> (match more_to_unify with
									| None -> Some true, left @ right
									| Some (lm, rm) -> let okm, more = unify_lists lm rm to_swap in
										(match okm with
										| None -> None, []
										| _ -> Some true, left @ right @ more))
									))
					| false -> Some false, [ swap (le1, le2) ])
			(* A proper error occurred while getting head and tail *)
			| _, _ -> None, [])
		| _, _ ->
			let msg = Printf.sprintf "Non-arranged lists passed to unify_lists : %s, %s" (string_of_logic_expression le1) (string_of_logic_expression le2) in
			raise (Failure msg)
	)

(* *********** *
 *             *
 * STRINGS WIP *
 *             *
 * *********** *)

let isString (se : jsil_logic_expr) : bool =
match se with
	| LLit (String _) -> true
	| _ -> false

(* What does it mean to be an internal string? *)
let isInternalString (se : jsil_logic_expr) : bool =
match se with
	| LVar _ 
	| LLit (CList _)
	| LBinOp (_, CharCons, _) (* Non recursive: assume that CharCat/Cons *)
	| LBinOp (_, CharCat,  _) (* only obtained from conversion anyway    *)
	| LCList _ -> true
	| _ -> false

(* Arranging strings in a specific order *)
let arrange_strings (se1 : jsil_logic_expr) (se2 : jsil_logic_expr) : (jsil_logic_expr * jsil_logic_expr) =
	match se1, se2 with
		| LVar _, _
		| LLit (CList _), LLit (CList _)
		| LLit (CList _), LCList _
		| LLit (CList _), LBinOp (_, CharCons, _)
		| LLit (CList _), LBinOp (_, CharCat, _)
		| LCList _, LCList _
		| LCList _, LBinOp (_, CharCons, _)
		| LCList _, LBinOp (_, CharCat, _)
		| LBinOp (_, CharCons, _), LBinOp (_, CharCons, _)
		| LBinOp (_, CharCons, _), LBinOp (_, CharCat, _)
		| LBinOp (_, CharCat, _), LBinOp (_, CharCat, _) -> se1, se2
		| _, _ -> se2, se1

(* Extracting elements from an internal string *)
let rec get_elements_from_string (se : jsil_logic_expr) : jsil_logic_expr list =
(match se with
	| LVar _ -> []
	| LLit (CList l) -> List.map (fun e -> LLit e) l
	| LCList l -> l
	| LBinOp (e, CharCons, se) -> e :: get_elements_from_string se
	| LBinOp (sel, CharCat, ser) -> get_elements_from_string sel @ get_elements_from_string ser
	| _ -> let msg = Printf.sprintf "Non-list expressions passed to get_elements_from_list : %s" (string_of_logic_expression se) in
		raise (Failure msg))

(* Splitting an internal string based on an element *)
let rec split_string_on_element (se : jsil_logic_expr) (e : jsil_logic_expr) : bool * (jsil_logic_expr * jsil_logic_expr) =
(match se with
	| LVar _ -> false, (se, LCList [])
	| LLit (CList l) -> 
		(match e with
		| LLit lit ->
			let ok, (ll, lr) = list_split l lit in
			(match ok with
			| true -> true, (LLit (CList ll), LLit (CList lr))
			| false -> false, (se, LCList [])
		| _ -> false, (se, LCList [])))
	| LCList l ->
		let ok, (ll, lr) = list_split l e in
			(match ok with
			| true -> true, (LCList ll, LCList lr)
			| false -> false, (se, LCList []))
	| LBinOp (e', CharCons, se') -> 
		(match (e = e') with
		| true -> true, (LCList [], se')
		| false -> let ok, (ll, lr) = split_string_on_element se' e in
			(match ok with
			| false -> false, (se, LCList [])
			| true -> true, (LBinOp (e', CharCons, ll), lr)))
	| LBinOp (sel, CharCat, ser) -> 
		let ok, (sll, slr) = split_string_on_element sel e in
		(match ok with
		| true -> 
			let right = 
			(match ser with 
			| LLit (CList [])
			| LCList [] -> slr
			| _ -> LBinOp (slr, CharCat, ser)) in
				true, (sll, right)
		| false -> let ok, (srl, srr) = split_string_on_element ser e in
			(match ok with
			| true -> 
				let left = (match srl with 
				| LLit (CList [])
				| LCList [] -> sel
				| _ -> LBinOp (sel, CharCat, srl)) in
					true, (left, srr)
			| false -> false, (se, LCList [])))
	| _ -> let msg = Printf.sprintf "Non-string expressions passed to split_string_on_element : %s" (string_of_logic_expression se) in
		raise (Failure msg))

(* Unifying strings based on a common literal *)
let match_strings_on_element (se1 : jsil_logic_expr) (se2 : jsil_logic_expr) : bool * (jsil_logic_expr * jsil_logic_expr) * (jsil_logic_expr * jsil_logic_expr) =
	let elems1 = get_elements_from_string se1 in
	(match elems1 with
	| [] -> false, (LLit (Bool false), LLit (Bool false)), (LLit (Bool false), LLit (Bool false))
	| _ ->
		let elems2 = get_elements_from_string se2 in
		(match elems2 with
		| [] -> false, (LLit (Bool false), LLit (Bool false)), (LLit (Bool false), LLit (Bool false))
		| _ -> 
			let intersection = List.fold_left (fun ac x -> 
				if (List.mem x elems1) then ac @ [x] else ac) [] elems2 in
			(match intersection with
			| [] -> false, (LLit (Bool false), LLit (Bool false)), (LLit (Bool false), LLit (Bool false))
			| i :: _ ->
				let ok1, (l1, r1) = split_string_on_element se1 i in
				let ok2, (l2, r2) = split_string_on_element se2 i in
				(match ok1, ok2 with
				| true, true -> true, (l1, r1), (l2, r2) 
				| _, _ -> let msg = Printf.sprintf "Element %s that was supposed to be in both strings: %s, %s is not." (string_of_logic_expression i) (string_of_logic_expression se1) (string_of_logic_expression se2) in
						raise (Failure msg)
				)
			)
		)
	)

(* Separating a list into a head and a tail *)
let rec get_head_and_tail_string (se : jsil_logic_expr) : bool option * jsil_logic_expr * jsil_logic_expr =
(match se with
	| LLit (CList l) ->
		(match l with
		| [] -> None, LLit (Bool false), LLit (Bool false)
		| e :: l -> Some true, LLit e, LLit (CList l))
	| LCList l ->
		(match l with
		| [] -> None, LLit (Bool false), LLit (Bool false)
		| e :: l -> Some true, e, LCList l)
	| LBinOp (e, CharCons,  s) -> Some true, e, s
	| LBinOp (s1, CharCat, s2) -> 
		let ok, head, tail = get_head_and_tail_string s1 in
		(match ok with
		| None -> None, LLit (Bool false), LLit (Bool false)
		| Some false -> Some false, LLit (Bool false), LLit (Bool false)
		| Some true -> Some true, head, LBinOp (tail, CharCat, s2))
	| LVar _ -> Some false, LLit (Bool false), LLit (Bool false)
	| _ -> 
		let msg = Printf.sprintf "Non-list expressions passed to get_head_and_tail_list : %s" (string_of_logic_expression se) in
		raise (Failure msg))

(* String unification *)
let rec unify_strings (se1 : jsil_logic_expr) (se2 : jsil_logic_expr) to_swap : bool option * ((jsil_logic_expr * jsil_logic_expr) list) = 
	(* Figure out reductions for these internal string representations... *)
	let se1 = reduce_expression_no_store_no_gamma_no_pfs se1 in
	let se2 = reduce_expression_no_store_no_gamma_no_pfs se2 in
	let se1_old = se1 in
	let se1, se2 = arrange_strings se1 se2 in
	let to_swap_now = (se1_old <> se1) in
	let to_swap = (to_swap <> to_swap_now) in
	let swap (se1, se2) = if to_swap then (se2, se1) else (se1, se2) in
	(* print_debug (Printf.sprintf "unify_strings: \n\t%s\n\t\tand\n\t%s" 
		(string_of_logic_expression se1) (string_of_logic_expression se2)); *)
	(match se1, se2 with
	  (* Base cases *)
		| LLit (CList []), LLit (CList []) 
		| LLit (CList []), LCList []
		| LCList [], LCList [] -> Some false, []
		| LVar _, _ -> Some false, [ swap (se1, se2) ]
		(* Inductive cases *)
		| LLit (CList _), LLit (CList _)
		| LLit (CList _), LCList _
		| LCList _, LCList _
		| LLit (CList _), LBinOp (_, CharCons, _) 
		| LLit (CList _), LBinOp (_, CharCat, _)
		| LCList _, LBinOp (_, CharCons, _) 
		| LCList _, LBinOp (_, CharCat, _)
		| LBinOp (_, CharCons, _), LBinOp (_, CharCons, _)
		| LBinOp (_, CharCons, _), LBinOp (_, CharCat,  _)
		| LBinOp (_, CharCat,  _), LBinOp (_, CharCat,  _) -> 
			let (okl, headl, taill) = get_head_and_tail_string se1 in
			let (okr, headr, tailr) = get_head_and_tail_string se2 in
			print_debug_petar (Printf.sprintf "Got head and tail: left: %b, right: %b" 
				(Option.map_default (fun v -> v) false okl) (Option.map_default (fun v -> v) false okr));
			(match okl, okr with
			(* We can separate both strings *)
			| Some true, Some true ->
				(* Do we still have strings? *)
				if (isInternalString taill && isInternalString tailr) then
					(* Yes, move in recursively *)
					(let ok, rest = unify_strings taill tailr to_swap in
					(match ok with
					| None -> None, []
					| _ -> Some true, swap (headl, headr) :: rest))
				else
					(* No, we are done *)
					Some true, [ swap (headl, headr); (taill, tailr) ]
			(* Not enough information to separate head and tail *)
			| Some _, Some _ -> 
				(* This means that we have on at least one side a LstCat with a leading variable and we need to dig deeper *)
				(* Get all literals on both sides, find first match, then split and call again *)
				let ok, (ll, lr), (rl, rr) = match_strings_on_element se1 se2 in
				(match ok with
					| true -> 
							let okl, left = unify_strings ll rl to_swap in
							(match okl with
							| None -> None, []
							| _ -> 
								let okr, right = unify_strings lr rr to_swap in
								(match okr with
								| None -> None, []
								| _ -> Some true, left @ right))
					| false -> Some false, [ swap (se1, se2) ])
			(* A proper error occurred while getting head and tail *)
			| _, _ -> None, [])
		| _, _ ->
			let msg = Printf.sprintf "Non-arranged lists passed to unify_lists : %s, %s" (string_of_logic_expression se1) (string_of_logic_expression se2) in
			raise (Failure msg)
	)
				
(* *********************** *
 * ULTIMATE SIMPLIFICATION *
 * *********************** *)

let rec understand_types exists pf_list gamma : bool = 
	let f = understand_types exists in
	(match pf_list with
	| [] -> true
	| (pf, from_where) :: rest ->
	 	(match pf with
		| LTrue | LFalse | LEmp | LNot _ -> f rest gamma
		| LPointsTo	(_, _, _) -> raise (Failure "Heap cell assertion in pure formulae.")
		| LEmp -> raise (Failure "Empty heap assertion in pure formulae.")
		| LPred	(_, _) -> raise (Failure "Predicate in pure formulae.")
		| LTypes _ -> raise (Failure "Types in pure formulae.")
		| LEmptyFields (_, _) -> raise (Failure "EmptyFields in pure formulae.")

		| LEq (le1, le2) -> 
			(* Get the types, if possible *)
			let te1, _, _ = type_lexpr gamma le1 in
			let te2, _, _ = type_lexpr gamma le2 in
			(* Understand if there's enough information to proceed *)
			let proceed = (match te1, te2 with
			| Some t1, Some t2 -> Some (t1 = t2)
			| None, None -> None
			| _, _ -> Some true) in
			(match proceed with
			| None -> f rest gamma
			| Some false -> false
			| Some true -> (* Check for variables *)
				(match le1, le2 with
				| LVar x, LVar y ->
					(* print_debug (Printf.sprintf "Checking: (%s, %s) vs %s" x  from_where y); *)
					(match te1, te2 with
					| Some t1, None ->
						if ((from_where = "l") || ((from_where = "r") && (SS.mem y exists))) 
						then Hashtbl.add gamma y t1; 
						f rest gamma
					| None, Some t2 ->
							if ((from_where = "l") || ((from_where = "r") && (SS.mem x exists))) 
							then Hashtbl.add gamma x t2; 
							f rest gamma 
					| Some t1, Some t2 -> f rest gamma
					| None, None -> raise (Failure "Impossible branch."))
				| LVar x, le
				| le, LVar x ->
					(* print_debug (Printf.sprintf "Checking: (%s, %s) vs %s" x from_where (JSIL_Print.string_of_logic_expression le false)); *)
					let tx = gamma_get_type gamma x in
					let te, _, _ = type_lexpr gamma le in
					(match te with
					| None -> f rest gamma
					| Some te ->
						(match tx with
						| None -> 
								if ((from_where = "l") || ((from_where = "r") && (SS.mem x exists)))
								then Hashtbl.add gamma x te; 
								f rest gamma
						| Some tx -> f rest gamma))
					| _, _ -> f rest gamma))
		| _ -> f rest gamma))
	

(* 
let check_types symb_state = 
	let pfs = get_pf_list symb_state in 
	let gamma = get_gamma symb_state in 
	let types_ok = understand_types SS.empty (List.map (fun x -> (x, "l")) pfs) gamma in
	match types_ok with
		| true -> symb_state
		| false -> raise (Failure "INCONSISTENT STATE") 
*)

(* ******************* *
 * MAIN SIMPLIFICATION *
 * ******************* *)

 (*
  * What do we need? 
  *
  * - The symbolic state
  * - An indicator if we're substituting all lvars or not
  * - If not, the set of allowed lvars (presumably, the spec_vars) (string list)
  * - Other formulas to which we propagate the subst, but we don't simplify otherwise
	* - Set of existentials
  *
  * What should we return?
  *
	* - The new symbolic state
  * - The full substitution 
	* - New others
  * - New set of existentials 
  *)
	
(* 
 * What is the idea?
 * Calculate the full subst while eliminating from the exists
 * In the end, bring back the bit that needs to be saved
 *)

(* Indexing types for easier access *)
let type_index t = 
	(match t with
	| UndefinedType -> 0
	| NullType      -> 1
	| EmptyType     -> 2
	| NoneType      -> 3
	| BooleanType   -> 4
	| NumberType    -> 5
	| StringType    -> 6
	| ObjectType    -> 7
	| ListType      -> 8
	| TypeType      -> 9
	| CharType      -> 10
	| SetType       -> 11)

let type_length = 12

let simplify_symb_state 
	(vars_to_save : (SS.t option) option)
	(other_pfs    : jsil_logic_assertion DynArray.t)
	(existentials : SS.t)
	(symb_state   : symbolic_state) =

	print_time_debug "simplify_symb_state:";

	print_debug_petar (Printf.sprintf "Symbolic state before simplification:\n%s" (Symbolic_State_Print.string_of_symb_state symb_state));  
		
	let initial_existentials = ref existentials in

	let vars_to_save, save_all = 
		(match vars_to_save with
		| Some (Some v) -> v, false 
		| Some None     -> SS.empty, true
		| None          -> SS.empty, false) in

	let setup_equalities pfs =
		let equality_hash : (jsil_logic_expr, jsil_logic_expr) Hashtbl.t = Hashtbl.create 101 in
		let i = ref 0 in
		while (!i < DynArray.length pfs) do
			let pf = DynArray.get pfs !i in
			(match pf with
			| LEq (le1, le2) ->
				print_debug (Printf.sprintf "Removing equality: %s = %s" (JSIL_Print.string_of_logic_expression le1) (JSIL_Print.string_of_logic_expression le2));
				Hashtbl.add equality_hash le1 le2;
				Hashtbl.add equality_hash le2 le1;
				DynArray.delete pfs !i
			| _ -> i := !i + 1);
		done;
		Hashtbl.iter (fun le1 le2 -> 
			let vals = Array.of_list (le1 :: (Hashtbl.find_all equality_hash le1)) in
			let len = Array.length vals in
			let i = ref 0 in
			while (!i < len) do
				let j = ref (!i + 1) in
				while (!j < len) do
					let le1 = Array.get vals !i in
					let le2 = Array.get vals !j in
						let lpfs = DynArray.to_list pfs in
						if (not (List.mem (LEq (le1, le2)) lpfs || List.mem (LEq (le2, le1)) lpfs))
						then (
							print_debug (Printf.sprintf "Adding equality: %s = %s" (JSIL_Print.string_of_logic_expression le1) (JSIL_Print.string_of_logic_expression le2));
							(match le1, le2 with
							| LESet _, LESet _ ->
									let pf = DynArray.get pfs 0 in
									DynArray.set pfs 0 (LEq (le1, le2));
									DynArray.add pfs pf
							| _, _ -> DynArray.add pfs (LEq (le1, le2))));	
						j := !j + 1;
				done;
				i := !i + 1
			done) equality_hash
	in
	
	(* Pure formulae false *)
	let pfs_false subst others exists symb_state msg =
		let _, _, pfs, _, _ = symb_state in
		print_debug_petar (msg ^ " Pure formulae false.");
		DynArray.clear pfs;
		DynArray.add pfs LFalse;
		symb_state, subst, others, exists in

	(* Are there any singleton types in gamma? *)
	let simplify_singleton_types others exists symb_state subst types =		 
		let gamma = ss_gamma symb_state in
		if (types.(0) + types.(1) + types.(2) + types.(3) > 0) then
			(Hashtbl.iter (fun v t -> 
				let lexpr = (match t with
					| UndefinedType -> Some (LLit Undefined)
					| NullType -> Some (LLit Null)
					| EmptyType -> Some (LLit Empty)
					| NoneType -> Some LNone
					| _ -> None) in
				(match lexpr with
				| Some lexpr -> 
						(* print_debug (Printf.sprintf "Singleton: (%s, %s)" v (JSIL_Print.string_of_type t)); *)
						Hashtbl.add subst v lexpr;
				| None -> ())) gamma;
			(* Substitute *)
			let symb_state = ss_substitution subst true symb_state in
			let others = pfs_substitution subst true others in
			let exists = Hashtbl.fold (fun v _ ac -> SS.remove v ac) subst exists in
			(* and remove from gamma, if allowed *)
			Hashtbl.iter (fun v _ ->
				match (save_all || SS.mem v (SS.union vars_to_save !initial_existentials)) with
				| true -> ()
				| false -> 
						while (Hashtbl.mem gamma v) do 
							let t = Hashtbl.find gamma v in
							let it = type_index t in
							types.(it) <- types.(it) - 1;
							Hashtbl.remove gamma v 
						done
				) subst;
				symb_state, subst, others, exists) 
			else
				symb_state, subst, others, exists in
	
	let arrange_pfs vars_to_save save_all exists pfs =
		let to_save = SS.union vars_to_save exists in
		DynArray.iteri (fun i pf ->
			(match pf with
			| LEq (LVar v1, LVar v2) ->
					let save_v1 = (save_all || SS.mem v1 to_save) in
					let save_v2 = (save_all || SS.mem v2 to_save) in
					(match save_v1, save_v2 with
					| true, true 
				  | false, true -> ()
					| true, false -> DynArray.set pfs i (LEq (LVar v2, LVar v1))
					| false, false -> 
							let lvar_v1 = (String.get v1 0 = '#') in
							let lvar_v2 = (String.get v2 0 = '#') in
							(match lvar_v1, lvar_v2 with
							| false, true -> DynArray.set pfs i (LEq (LVar v2, LVar v1))
							| _, _ -> ()))
			| LEq (e, LVar v) -> DynArray.set pfs i (LEq (LVar v, e))
			| _ -> ())) pfs in
		
	(* Let's start *)
	let heap, store, p_formulae, gamma, preds = symb_state in	

	(* 
	 * Trim the variables that are in gamma
	 * but not in the rest of the state, 
	 * and are also not in vars_to_save
	 * and are also not in others
	 *)
	(* print_debug (Printf.sprintf "SS: %s" (Symbolic_State_Print.string_of_shallow_symb_state symb_state)); *)
	
	setup_equalities p_formulae;
	let lvars = SS.union (ss_vars_no_gamma symb_state) (pfs_lvars other_pfs) in
	let lvars_gamma = get_gamma_all_vars gamma in		
	let lvars_inter = SS.inter lvars lvars_gamma in
	Hashtbl.filter_map_inplace (fun v t ->
		(match (save_all || SS.mem v (SS.union lvars_inter (SS.union vars_to_save !initial_existentials))) with
		| true  -> Some t
		| false -> (* print_debug (Printf.sprintf "Cutting %s : %s from gamma" v (JSIL_Print.string_of_type t)); *) None)) gamma;
		
	(* Setup the type indexes *)
	let types = Array.make type_length 0 in
	Hashtbl.iter (fun _ t -> 
		let it = type_index t in
			types.(it) <- types.(it) + 1) gamma;
		
	(* Instantiate uniquely determined variables *)
	let subst = Hashtbl.create 57 in
	let symb_state, subst, others, exists = simplify_singleton_types other_pfs !initial_existentials symb_state subst types in

	let pfs = ss_pfs symb_state in

	(* String translation: Use internal representation as Chars *)
	let pfs = DynArray.map (assertion_map None None (Some (logic_expression_map le_string_to_list None))) pfs in
	(* print_debug_petar (Printf.sprintf "Pfs before simplification (with internal rep): %s" (string_of_pfs pfs)); *)
	let symb_state = ss_replace_pfs symb_state pfs in 
	
	let changes_made = ref true in
	let symb_state   = ref symb_state in
	let others       = ref others in
	let exists       = ref exists in
	let pfs_ok       = ref true in
	let msg          = ref "" in
	
	(* MAIN LOOP *)
	
	while (!changes_made && !pfs_ok) do

		changes_made := false;
		
		let (heap, store, pfs, gamma, preds) = !symb_state in
		
		Hashtbl.filter_map_inplace (fun pvar le -> Some (reduce_expression_no_store gamma pfs le)) store;
		
		arrange_pfs vars_to_save save_all !exists pfs;
		
		sanitise_pfs store gamma pfs;
		
		let n = ref 0 in
		while (!pfs_ok && !n < DynArray.length pfs) do
			let pf = DynArray.get pfs !n in
			(match pf with

			(* If we have true in the pfs, we delete it and restart *)
			| LTrue -> DynArray.delete pfs !n
			
			(* If we have false in the pfs, everything is false and we stop *)
			| LFalse -> pfs_ok := false; msg := "Pure formulae flat-out false."
			
			(* We are false if we have x < x *)
			| LLess	(LVar v1, LVar v2) when (v1 = v2) ->
			  	pfs_ok := false; msg := "Incorrect less-than."
			
			(* We can reduce < if both are numbers *)
			| LLess	(LLit (Num n1), LLit (Num n2)) ->
			  (match (n1 < n2) with
				| true -> DynArray.delete pfs !n
				| false -> pfs_ok := false; msg := "Incorrect less-than.")

			(* Same for <= *)
			| LLessEq	(LLit (Num n1), LLit (Num n2)) ->
			  (match (n1 <= n2) with
				| true -> DynArray.delete pfs !n
				| false -> pfs_ok := false; msg := "Incorrect less-than-or-equal.")

			(* These shouldn't even be here *)
			| LPointsTo	(_, _, _) -> raise (Failure "Heap cell assertion in pure formulae.")
			| LEmp -> raise (Failure "Empty heap assertion in pure formulae.")
			| LPred	(_, _) -> raise (Failure "Predicate in pure formulae.")
			| LTypes _ -> raise (Failure "Types in pure formulae.")
			| LEmptyFields (_, _) -> raise (Failure "EmptyFields in pure formulae.")

			(* I don't know how these could get here, but let's assume they can... *)
			| LAnd  (a1, a2)
			| LStar	(a1, a2) -> DynArray.set pfs !n a1; DynArray.add pfs a2
						
			(* Equality *)
			| LEq (le1, le2) ->
				(match le1, le2 with

				| LVar v1, LVar v2 when (v1 = v2) ->
						DynArray.delete pfs !n
				
				(* Variable and something else *)
				| LVar v, le 
				| le, LVar v ->			
					
					(* Understand, if there are two lvars, which should be substituted *)
					let v, le = (match le with
					| LVar w -> 
							(match (SS.mem v vars_to_save), (SS.mem w vars_to_save) with
							| true, false -> w, LVar v
							| true, true 
							| false, true -> v, le
							| false, false -> 
								let fv = String.get v 0 in
								let fw = String.get w 0 in
								(match (fv = '#'), (fw = '#') with
								| true, false -> w, LVar v
								| _, _ -> v, le))
					| _ -> v, le) in
					
					(* print_debug_petar (Printf.sprintf "LVAR: %s --> %s" v (string_of_logic_expression le)); *)
					
					let lvars_le = get_lexpr_lvars le in
					(match (SS.mem v lvars_le) with
					| true -> n := !n + 1
					| false -> 		
						(* Changes made, stay on n *)
						changes_made := true;
						DynArray.delete pfs !n;
						
						let tv, _, _ = JSIL_Logic_Utils.type_lexpr gamma (LVar v) in
						let tle = if ((not (match le with | LVar _ -> true | _ -> false)) && (isString le || isInternalString le)) then Some StringType else
							let result, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in result in
						(match tv, tle with
						| Some tv, Some tle when (tv <> tle) -> pfs_ok := false; msg := "Nasty type mismatch."
						| _ -> 
							(* Substitute *)
							let temp_subst = Hashtbl.create 1 in
							Hashtbl.add temp_subst v le;
							
							let simpl_fun, how_subst = (match (not (SS.mem v !initial_existentials) && (save_all || SS.mem v vars_to_save)) with
								| false -> ss_substitution_in_place_no_gamma, "general"
								| true -> selective_symb_state_substitution_in_place_no_gamma, "selective"
								) in
							
							(* print_debug_petar (Printf.sprintf "The substitution will be: %s" how_subst); *)
							
							simpl_fun temp_subst !symb_state;
							pfs_substitution_in_place temp_subst !others;
							
							(* Add to subst *)
							if (Hashtbl.mem subst v) then 
								raise (Failure (Printf.sprintf "Impossible variable in subst: %s\n%s"
									v (JSIL_Print.string_of_substitution subst)));
							Hashtbl.iter (fun v' le' ->
								let sb = Hashtbl.create 1 in
									Hashtbl.add sb v le;
									let sa = lexpr_substitution sb true le' in
										Hashtbl.replace subst v' sa) subst;
							Hashtbl.replace subst v le;
							
							(* Understand gamma if subst is another LVar *)
							(match le with
							| LVar v' ->
								(match (Hashtbl.mem gamma v) with
								| false -> ()
								| true -> 
									let t = Hashtbl.find gamma v in
										(match (Hashtbl.mem gamma v') with
										| false -> 
												let it = type_index t in
												types.(it) <- types.(it) + 1;
												Hashtbl.add gamma v' t
										| true -> 
											let t' = Hashtbl.find gamma v' in
											(match (t = t') with
											| false -> pfs_ok := false; msg := "Horrific type mismatch."
											| true -> ()))
								)
							| _ -> ());
									
								
							(* Remove (or add) from (or to) gamma *)
							(match (save_all || SS.mem v (SS.union vars_to_save !exists)) with
		      		| true -> 
									let le_type = if ((not (match le with | LVar _ -> true | _ -> false)) && (isString le || isInternalString le)) then Some StringType else
										let result, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in result in
									(match le_type with
									| None -> ()
									| Some t -> 
										(match Hashtbl.mem gamma v with
										| false -> 
												let it = type_index t in
												types.(it) <- types.(it) + 1;
												(* print_debug_petar (Printf.sprintf "GAT: %s : %s" v (JSIL_Print.string_of_type t)); *)
												Hashtbl.add gamma v t
										| true -> 
												let tv = Hashtbl.find gamma v in
												(match (tv = t) with
												| true -> ()
												| false ->
														(* print_debug_petar (Printf.sprintf "Type mismatch: %s -> %s, but %s." v (JSIL_Print.string_of_type tv) (JSIL_Print.string_of_type t)); *) 
														pfs_ok := false; msg := "Horrific type mismatch.")))
		      		| false -> 
		    					while (Hashtbl.mem gamma v) do 
		    						let t = Hashtbl.find gamma v in
		    						let it = type_index t in
		    						types.(it) <- types.(it) - 1;
										(* print_debug_petar (Printf.sprintf "Removing from gamma: %s" v); *)
		    						Hashtbl.remove gamma v 
		    					done);
							
							(* Remove from existentials *)
							exists := SS.remove v !exists))
					
				(* List length *)
				| LLit (Num len), LUnOp (LstLen, LVar v)
				| LUnOp (LstLen, LVar v), LLit (Num len) ->
						(match (Utils.is_int len) with
						| false -> pfs_ok := false; msg := "Non-integer list-length. Good luck."
						| true -> 
							let len = int_of_float len in
							(match (0 <= len) with
							| false -> pfs_ok := false; msg := "Sub-zero length. Good luck."
							| true -> 
									let subst_list = Array.to_list (Array.init len (fun _ -> fresh_lvar())) in
									let new_exists = !exists in
									let new_exists = List.fold_left (fun ac v -> 
										initial_existentials := SS.add v !initial_existentials;
										SS.add v ac) new_exists subst_list in
									exists := new_exists;
									let subst_list = List.map (fun x -> LVar x) subst_list in
									
									(* Changes made, stay on n *)
									changes_made := true;
									DynArray.delete pfs !n;
									DynArray.add pfs (LEq (LVar v, LEList subst_list))
							)
						)
				
				(* List n-th *)
				| LLstNth (lst, LLit (Num idx)), le ->
					(match (Utils.is_int idx) with
						| false -> pfs_ok := false; msg := "Non-integer list indexation. Good luck."
						| true -> 
							let idx = int_of_float idx in
							(match (0 <= idx) with
							| false -> pfs_ok := false; msg := "Sub-zero indexation. Good luck."
							| true -> 
									let subst_list = Array.to_list (Array.init (idx + 1) (fun _ -> fresh_lvar())) in
									let new_exists = !exists in
									let new_exists = List.fold_left (fun ac v -> 
										initial_existentials := SS.add v !initial_existentials;
										SS.add v ac) new_exists subst_list in
									exists := new_exists;
									(* Get the part of the list before the nth and the part of the list after the nth *)
									let front, back = List.tl subst_list, List.hd subst_list in
									(* The part after is of list type *)
									Hashtbl.add gamma back ListType;
									let front = List.map (fun x -> LVar x) front in
									let back = LVar back in
									
									let new_lst = LBinOp (LEList front, LstCat, (LBinOp (le, LstCons, back))) in
									
									(* Changes made, stay on n *)
									changes_made := true;
									DynArray.delete pfs !n;
									DynArray.add pfs (LEq (lst, new_lst))
								)
						)
				
				(* List unification *)
				| le1, le2 when (isList le1 && isList le2) ->
					(* print_debug (Printf.sprintf "List unification: %s vs. %s" (string_of_logic_expression le1) (string_of_logic_expression le2)); *)
					let ok, subst = unify_lists le1 le2 false in
					(match ok with
					(* Error while unifying lists *)
					| None -> pfs_ok := false; msg := "List error"	
					(* No error, but no progress *)
					| Some false -> (match subst with
						| [ ] 
						| [ _ ] -> n := !n + 1 
						| _ -> 
							(* print_debug_petar (Printf.sprintf "No changes made, but length = %d" (List.length subst));
							print_debug_petar (String.concat "\n" (List.map (fun (x, y) ->
								Printf.sprintf "%s = %s" (string_of_logic_expression x) (string_of_logic_expression y)) subst)); *)
							raise (Failure "Unexpected list obtained from list unification."))
					(* Progress *)
					| Some true -> 
							(* Changes made, stay on n *)
							changes_made := true;
							DynArray.delete pfs !n;
							List.iter (fun (x, y) -> DynArray.add pfs (LEq (x, y))) subst)
				
				(* String length *)
				| LLit (Num len), LUnOp (StrLen, LVar v)
				| LUnOp (StrLen, LVar v), LLit (Num len) ->
						(match (Utils.is_int len) with
						| false -> pfs_ok := false; msg := "Non-integer string-length. Good luck."
						| true -> 
							let len = int_of_float len in
							(match (0 <= len) with
							| false -> pfs_ok := false; msg := "Sub-zero length. Good luck."
							| true -> 
									let subst_list = Array.to_list (Array.init len (fun _ -> fresh_lvar())) in
									let new_exists = !exists in
									let new_exists = List.fold_left (fun ac v -> 
										initial_existentials := SS.add v !initial_existentials;
										SS.add v ac) new_exists subst_list in
									exists := new_exists;
									let subst_list = List.map (fun x -> LVar x) subst_list in
									
									(* Changes made, stay on n *)
									changes_made := true;
									DynArray.delete pfs !n;
									DynArray.add pfs (LEq (LVar v, LCList subst_list))
							)
						)
				(* String unification *)
				| se1, se2 when (isInternalString se1 && isInternalString se2) ->
					(* print_debug (Printf.sprintf "String unification: %s vs. %s" (string_of_logic_expression se1) (string_of_logic_expression se2)); *)
					let ok, subst = unify_strings se1 se2 false in
					(match ok with
					(* Error while unifying strings *)
					| None -> pfs_ok := false; msg := "String error"
					(* No error, but no progress *)
					| Some false -> (match subst with
						| [ ] 
						| [ _ ] -> n := !n + 1 
						| _ -> 
							(* print_debug_petar (Printf.sprintf "No changes made, but length = %d" (List.length subst));
							print_debug_petar (String.concat "\n" (List.map (fun (x, y) ->
								Printf.sprintf "%s = %s" (string_of_logic_expression x) (string_of_logic_expression y)) subst)); *)
							raise (Failure "Unexpected list obtained from string unification."))
					(* Progress *)
					| Some true -> 
							(* Changes made, stay on n *)
							changes_made := true;
							DynArray.delete pfs !n;
							List.iter (fun (x, y) -> DynArray.add pfs (LEq (x, y))) subst)
				
				(* Sets *)
				| LESet [ le1 ], LESet [ le2 ] ->
						DynArray.delete pfs !n;
						DynArray.add pfs (LEq (le1, le2));
						changes_made := true;
				
				(* The insanely specific set stuff that Jose asked for *)
        | LESet ls1, LESet ls2 -> 
					(match (List.length ls1 = List.length ls2) with
					| false -> n := !n + 1
					| true -> 
							let heap_lvars = heap_lvars heap in
							(* All elements of the set have to be something *)
							let ohMy = ref (-1) in
							let gammaL = ref 0 in
							let gammaR = ref 0 in
							let heapL = ref 0 in
							let heapR = ref 0 in
							let ll = List.for_all2 (fun le1 le2 -> 
  						(match le1, le2 with
							(* Lists of equal length *)
  						| LEList le1, LEList le2 when 
									(if (!ohMy = -1) 
										then (if List.length le1 = List.length le2 
											then (ohMy := List.length le1; true)
											else false) 
										else (List.length le1 = !ohMy) && (List.length le2 = !ohMy)) -> 
									List.for_all2 (fun le1 le2 ->
										match le1, le2 with
										| LVar x, LVar y ->
											if (Hashtbl.mem gamma x) then gammaL := !gammaL + 1;
											if (Hashtbl.mem gamma y) then gammaR := !gammaR + 1;
											if (SS.mem x heap_lvars) then heapL := !heapL + 1;
											if (SS.mem y heap_lvars) then heapR := !heapR + 1;
											true
										| _, _ -> false
										) le1 le2
  						| _, _ -> false)) ls1 ls2 in
  							(match ll with
  								| false -> n := !n + 1
  								| true ->
											let ls1, ls2, proceed = 
												if (!gammaL * !gammaR = 0) && (!gammaL + !gammaR > 0) 
													then (if (!gammaL = 0) then ls2, ls1, true else ls1, ls2, true)
													else if (!heapL * !heapR = 0) && (!heapL + !heapR > 0)
														then (if (!heapL = 0) then ls2, ls1, true else ls1, ls2, true)
														else ls1, ls2, false
												in
											if proceed then (
												print_debug (Printf.sprintf "Candidates: %s, %s with length %d" (JSIL_Print.string_of_logic_expression (LESet ls1)) (JSIL_Print.string_of_logic_expression (LESet ls2)) !ohMy);
												(* Now, splitting *)
												let len = List.length ls1 in
												let arr = Array.init !ohMy (fun _ -> [], []) in
												List.iter2 (fun le1 le2 ->
													(match le1, le2 with
													| LEList le1, LEList le2 -> 
  													let i = ref 0 in
  													let al1 = Array.of_list le1 in
  													let al2 = Array.of_list le2 in
  													while !i < !ohMy do
  														let e1 = Array.get al1 !i in
  														let e2 = Array.get al2 !i in
  														let l1, l2 = Array.get arr !i in
  														Array.set arr !i (l1 @ [ e1 ], l2 @ [ e2 ]);
  														i := !i + 1;
  													done)
													) ls1 ls2;
												(* Now, substs, but for full logical expressions, not variables... *)
												let subst_le = Hashtbl.create 31 in
												Array.iter (fun (a1, a2) -> Hashtbl.add subst_le (LESet a2) (LESet a1)) arr;
												Hashtbl.add subst_le (LESet ls2) (LESet ls1);
												DynArray.delete pfs !n;
												
												Hashtbl.iter (fun k v -> print_debug (Printf.sprintf "\t%s --> %s" (JSIL_Print.string_of_logic_expression k) (JSIL_Print.string_of_logic_expression v))) subst_le;
												
                        lexpr_lexpr_symb_state_substitution_in_place_no_gamma subst_le !symb_state;
                        pfs_lexpr_lexpr_substitution_in_place subst_le !others;
												
												DynArray.iteri (fun n pf -> DynArray.set pfs n (lexpr_lexpr_ass_subst subst_le pf)) pfs;

												changes_made := true;
												n := 0
											) else
											n := !n + 1
								)
					)
        
				| _, _ -> n := !n + 1)
		

			(* Special cases *)
			| LNot (LEq (ALoc _, LLit Empty)) 
			| LNot (LEq (LLit Empty, ALoc _))
			| LNot (LEq (ALoc _, LLit Null)) 
			| LNot (LEq (LLit Null, ALoc _)) ->
					DynArray.delete pfs !n
					
			| LNot (LEq (LVar v, LLit Empty)) 
			| LNot (LEq (LLit Empty, LVar v)) ->
				(match (Hashtbl.mem gamma v) with
				| false -> n := !n + 1
				| true -> 	
						let t = Hashtbl.find gamma v in
						(match (t = EmptyType) with
						| true -> pfs_ok := false; msg := "Negation incorrect."
						| false -> DynArray.delete pfs !n))

			| _ -> n := !n + 1);
		done;
	done;

	(* String translation: Move back from internal representation to Strings - EVERYWHERE *)	
	(* Convert substitutions back to string format *)
	Hashtbl.filter_map_inplace (fun var lexpr -> Some (logic_expression_map le_list_to_string None lexpr)) subst;

	Hashtbl.iter (fun var lexpr -> 
		(match (not (SS.mem var !initial_existentials) && (save_all || SS.mem var vars_to_save)) with
		| false -> ()
		| true -> DynArray.add pfs (LEq (LVar var, lexpr)))
		) subst;
	
	(* Convert Pure Formulas back *)
	let pfs = DynArray.map (assertion_map None None (Some (logic_expression_map le_list_to_string None))) (ss_pfs !symb_state) in
	let symb_state = ref (ss_replace_pfs !symb_state pfs) in
	(* print_debug (Printf.sprintf "Pfs after simplification (with internal rep): %s" (print_pfs pfs)); *)

	let heap, store, _, _, preds = !symb_state in
	
	(* Convert Store, Heap and Preds back, which should only change new additions *)
	Hashtbl.filter_map_inplace (fun var lexpr -> Some (logic_expression_map le_list_to_string None lexpr)) store;
	LHeap.filter_map_inplace (fun loc (fv_list, default) -> 
		let fn, fv = List.split fv_list in
		let fn = List.map (fun lexpr -> logic_expression_map le_list_to_string None lexpr) fn in
		let fv = List.map (fun lexpr -> logic_expression_map le_list_to_string None lexpr) fv in
		Some (List.combine fn fv, default)
		) heap; 
	DynArray.iteri (fun i (pname, pparams) ->
		let pparams = List.map (fun lexpr -> logic_expression_map le_list_to_string None lexpr) pparams in
		DynArray.set preds i (pname, pparams)) preds;

	let others = ref (DynArray.map (assertion_map None None (Some (logic_expression_map le_list_to_string None))) !others) in

	(* Final bit - remove any duplicates and equalities that commute *)
	let i = ref 0 in
	while (!i < DynArray.length pfs) do
		let spfs = SA.of_list (DynArray.to_list pfs) in
		let pf = DynArray.get pfs !i in
		(match pf with
		| LEq (le1, le2) ->
				let sorted = List.sort Pervasives.compare [le1; le2] in
				let left = List.hd sorted in 
				let right = List.hd (List.tl sorted) in
				DynArray.set pfs !i (LEq (right, left))
		| _ -> ());
		i := !i + 1
	done;
	
	sanitise_pfs_no_store_no_gamma pfs;

	(* print_debug_petar (Printf.sprintf "Exiting with pfs_ok: %b\n" !pfs_ok); *)
	let ss, subst, ots, exs = if (!pfs_ok) 
		then (!symb_state, subst, !others, !exists)
		else (pfs_false subst !others !exists !symb_state !msg) in
	
	(* let cache_value = simpl_encache_value ss subst ots exs in
	Hashtbl.replace simpl_cache cache_key cache_value; *)

	print_debug_petar ("symb_state after call to simplification: \n" ^ (Symbolic_State_Print.string_of_symb_state ss)); 

	ss, subst, ots, exs
	

let simplify_ss symb_state vars_to_save = 
	let symb_state, _, _, _ = simplify_symb_state vars_to_save (DynArray.create()) (SS.empty) symb_state in
	symb_state
	
let simplify_ss_with_subst symb_state vars_to_save = 
	let symb_state, subst, _, _ = simplify_symb_state vars_to_save (DynArray.create()) (SS.empty) symb_state in
	symb_state, subst

let simplify_pfs pfs gamma vars_to_save =
	let fake_symb_state = (LHeap.create 1, Hashtbl.create 1, (DynArray.copy pfs), (gamma_copy gamma), DynArray.create ()) in
	let (_, _, pfs, gamma, _), _, _, _ = simplify_symb_state vars_to_save (DynArray.create()) (SS.empty) fake_symb_state in
	pfs, gamma
			
let simplify_pfs_with_subst pfs gamma =
	let fake_symb_state = (LHeap.create 1, Hashtbl.create 1, (DynArray.copy pfs), (gamma_copy gamma), DynArray.create ()) in
	let (_, _, pfs, gamma, _), subst, _, _ = simplify_symb_state None (DynArray.create()) (SS.empty) fake_symb_state in
	if (DynArray.to_list pfs = [ LFalse ]) then (pfs, None) else (pfs, Some subst)

let simplify_pfs_with_exists exists lpfs gamma vars_to_save = 
	let fake_symb_state = (LHeap.create 1, Hashtbl.create 1, (DynArray.copy lpfs), (gamma_copy gamma), DynArray.create ()) in
	let (_, _, lpfs, gamma, _), _, _, exists = simplify_symb_state vars_to_save (DynArray.create()) exists fake_symb_state in
	lpfs, exists, gamma

let simplify_pfs_with_exists_and_others exists lpfs rpfs gamma = 
	let fake_symb_state = (LHeap.create 1, Hashtbl.create 1, (DynArray.copy lpfs), (gamma_copy gamma), DynArray.create ()) in
	let (_, _, lpfs, gamma, _), _, rpfs, exists = simplify_symb_state None rpfs exists fake_symb_state in
	lpfs, rpfs, exists, gamma

(* ************************** *
 * IMPLICATION SIMPLIFICATION *
 * ************************** *)
	
let rec simplify_existentials (exists : SS.t) lpfs (p_formulae : jsil_logic_assertion DynArray.t) (gamma : (string, jsil_type) Hashtbl.t) =

	(* print_time_debug ("simplify_existentials:"); *)
	
	let rhs_gamma = gamma_copy gamma in
	filter_gamma_pfs p_formulae rhs_gamma;
	
	let p_formulae, exists, _ = simplify_pfs_with_exists exists p_formulae rhs_gamma (Some None) in
	
	(* print_debug (Printf.sprintf "PFS: %s" (Symbolic_State_Print.string_of_shallow_p_formulae p_formulae false)); *)

	let pfs_false msg =
		print_debug_petar (msg ^ " Pure formulae false.\n");
		DynArray.clear p_formulae;
		DynArray.add p_formulae LFalse;
		SS.empty, lpfs, p_formulae, (Hashtbl.create 1) in

	let delete_substitute_proceed exists p_formulae gamma v n le =
		(* print_debug (Printf.sprintf "Deleting the formula \n%s\nand substituting the variable %s for %s." 
			(JSIL_Print.string_of_logic_assertion (DynArray.get p_formulae n) false) 
			v (JSIL_Print.string_of_logic_expression le false)); *)
		DynArray.delete p_formulae n;
		let exists = SS.remove v exists in
		while (Hashtbl.mem gamma v) do Hashtbl.remove gamma v done;
		let subst = Hashtbl.create 1 in
		Hashtbl.add subst v le;
		simplify_existentials exists lpfs (pfs_substitution subst true p_formulae) gamma in

	let test_for_nonsense pfs =

		let rec test_for_nonsense_var_list var lst =
			print_debug_petar (Printf.sprintf "Nonsense test: %s vs. %s" (string_of_logic_expression var) (string_of_logic_expression lst));
			(match var, lst with
			 | LVar v, LVar w -> v = w
			 | LVar _, LEList lst ->
				 List.fold_left (fun ac x -> ac || x = var) false lst
			 | LVar _, LBinOp (head, LstCons, tail) ->
				  (var = head) || (test_for_nonsense_var_list var tail)
			 | _, _ -> false
			) in

		let rec test_for_nonsense_iter pfs =
		(match pfs with
		| [] -> false
		| a :: rest -> (match a with
		  | LEq (le1, le2) ->
			(match le1, le2 with
			 | LVar _, LEList _
			 | LVar _, LBinOp (_, LstCons, _) ->
			   let is_recursive_nonsense = test_for_nonsense_var_list le1 le2 in
			   (match is_recursive_nonsense with
				| true -> true
				| false -> test_for_nonsense_iter rest)
			 | _, _ -> test_for_nonsense_iter rest)
		  | _ -> test_for_nonsense_iter rest)
		) in

	test_for_nonsense_iter pfs in

	let rec go_through_pfs (pfs : jsil_logic_assertion list) n =
	(match pfs with
	 | [] -> if (test_for_nonsense (pfs_to_list p_formulae))
			 	then pfs_false "Nonsense."
				else
			 (let pf_list = DynArray.to_list p_formulae in
				let types_ok = understand_types exists (List.map (fun x -> (x, "r")) pf_list) gamma in
				(match types_ok with
				| false -> pfs_false "Nasty type mismatch."
				| true -> exists, lpfs, p_formulae, gamma))
	 | pf :: rest ->
	   (match pf with
	    | LEq (LLit l1, LLit l2) ->
	    	if (l1 = l2) 
	    		then (DynArray.delete p_formulae n; go_through_pfs rest n)
	    		else pfs_false "Literals."
		| LEq (LVar x, LVar y) ->
			let mx = SS.mem x exists in
			let my = SS.mem y exists in
			(match mx, my with
			| false, false -> go_through_pfs rest (n + 1)
			| false, true  -> delete_substitute_proceed exists p_formulae gamma y n (LVar x) 
			| true,  _ -> delete_substitute_proceed exists p_formulae gamma x n (LVar y))
		| LEq (LVar v, le) 
		| LEq (le, LVar v) ->
		   (match (SS.mem v exists) with
		   | false -> go_through_pfs rest (n + 1)
		   | true ->
		       (* Why? - if not in gamma and we can type the thing on the right, add to gamma *)
			   (match (Hashtbl.mem gamma v) with
			    | false -> 
					(match le with
						 | LLit lit ->
							 let ltype = evaluate_type_of lit in
							 Hashtbl.replace gamma v ltype;
							 delete_substitute_proceed exists p_formulae gamma v n le
						 | ALoc _ ->
						 	 Hashtbl.replace gamma v ObjectType;
							 delete_substitute_proceed exists p_formulae gamma v n le
						 | LEList _
						 | LBinOp (_, LstCons, _) ->
						 	 Hashtbl.replace gamma v ListType;
							 let can_we_substitute = isExistentiallySubstitutable le in
							 (match can_we_substitute with
							  | false -> go_through_pfs rest (n + 1)
							  | true -> delete_substitute_proceed exists p_formulae gamma v n le
							 )
						 | LBinOp (_, StrCat, _) ->
						 	 Hashtbl.replace gamma v StringType;
							 let can_we_substitute = isExistentiallySubstitutable le in
							 (match can_we_substitute with
							  | false -> go_through_pfs rest (n + 1)
							  | true -> delete_substitute_proceed exists p_formulae gamma v n le
							 )
						 | _ -> go_through_pfs rest (n + 1))
				| true ->
					let vtype = Hashtbl.find gamma v in
					(match le with
					 | LLit lit ->
					     let ltype = evaluate_type_of lit in
						 (match (vtype = ltype) with
						  | false -> pfs_false "Mistypes."
						  | true -> delete_substitute_proceed exists p_formulae gamma v n le
						 )
					 | ALoc _ -> 
					 	(match (vtype = ObjectType) with
						  | false -> pfs_false "Mistypes."
						  | true -> delete_substitute_proceed exists p_formulae gamma v n le
						 )
				     | LEList _
					 | LBinOp (_, LstCons, _) ->
					     let can_we_substitute = isExistentiallySubstitutable le in
						 (match can_we_substitute with
						  | false -> go_through_pfs rest (n + 1)
						  | true -> delete_substitute_proceed exists p_formulae gamma v n le
						 )
					 | _ -> go_through_pfs rest (n + 1)
					)
			   )
		  )
			
		| _ -> go_through_pfs rest (n + 1)
	   )
	) in

	DynArray.iteri
	(fun i pf ->
	  (match pf with
	   | LEq (LVar _, LVar _) -> ()
	   | LEq (le1, LVar var) -> DynArray.set p_formulae i (LEq (LVar var, le1))
	   | _ -> ()
	  )
	) p_formulae;

	let pf_list = DynArray.to_list p_formulae in
	let result = go_through_pfs pf_list 0 in
	result



(* *********** *)
(*   CLEANUP   *)
(* *********** *)

let clean_up_stuff exists left right =
	let sleft = SA.of_list (DynArray.to_list left) in
	let i = ref 0 in
	while (!i < DynArray.length right) do
		let pf = DynArray.get right !i in
		let pf_sym pf = (match pf with
			| LEq (e1, e2) -> SA.mem (LEq (e2, e1)) sleft
			| LNot (LEq (e1, e2)) -> SA.mem (LNot (LEq (e2, e1))) sleft
			| _ -> false) in
		(match ((SA.mem pf sleft) || (pf_sym pf)) with
		| false -> 
			let npf = (match pf with
					| LNot pf -> pf
					| _ -> LNot pf) in
			 	(match ((SA.mem npf sleft) || (pf_sym npf)) with
				| false -> i := !i + 1
				| true -> 
						DynArray.clear left; DynArray.clear right;
						DynArray.add left LFalse)
		 | true -> DynArray.delete right !i
		)
	done;
	
	i := 0;
	while (!i < DynArray.length right) do
		let pf = DynArray.get right !i in
		(match pf with
		| LNot (LEq (le, LLit Empty)) ->
			(match le with
			| LEList _ 
			| LBinOp (_, _, _)  
			| LUnOp (_, _) -> DynArray.delete right !i 
			| _ -> i := !i + 1
			)
		| _ -> i := !i + 1)
	done
	



(* Set intersections *)
let get_set_intersections pfs =
	let lvars = Hashtbl.create 23 in
	let rvars = Hashtbl.create 23 in
	
	List.iter
		(fun pf -> 
			(match pf with
			| LForAll ([ (x, NumberType) ], LOr (LNot (LSetMem (LVar y, LVar set)), LLess (LVar elem, LVar z))) when (x = y && x = z) -> 
					print_debug_petar (Printf.sprintf "Got left: %s, %s" elem set);
					Hashtbl.add lvars elem set;
			| LForAll ([ (x, NumberType) ], LOr (LNot (LSetMem (LVar y, LVar set)), LLess (LVar z, LVar elem))) when (x = y && x = z) -> 
					print_debug_petar (Printf.sprintf "Got right: %s, %s" elem set);
					Hashtbl.add rvars elem set;
			| _ -> ())
		) pfs;
		
	print_debug_petar "v <# set :";  Hashtbl.iter (fun v s -> print_debug_petar (Printf.sprintf "\t%s, %s" v s)) lvars;
	print_debug_petar "set <# v :"; Hashtbl.iter (fun v s -> print_debug_petar (Printf.sprintf "\t%s, %s" v s)) rvars;
	
	(* 
	 *   1. forall (v, s) in lvars -> inter { v }, s = 0
	 *   2. forall (v, s) in rvars -> inter { v }, s = 0
	 *   3. if (v, s1) in lvars and (v, s2) in rvars, then inter s1 s2 = 0
	 *   4. if v1 < v2 and (v1, s1) in lvars and (v2, s2) in lvars, then inter { v1 } { v2 } = 0 and inter { v1 } s2 = 0
	 * 
	 *   THERE ARE MORE
 	 *)
	let intersections = ref [] in
	
	(* 1. *)
	Hashtbl.iter (fun v s -> intersections := (SLExpr.of_list [ LESet [ LVar v ]; LVar s ] ) :: !intersections) lvars;
	(* 2. *)
	Hashtbl.iter (fun v s -> intersections := (SLExpr.of_list [ LESet [ LVar v ]; LVar s ] ) :: !intersections) rvars;
	(* 3. *)
	Hashtbl.iter (fun v s1 -> if (Hashtbl.mem rvars v) then
		let rsets = Hashtbl.find_all rvars v in
		List.iter (fun s2 -> intersections := (SLExpr.of_list [ LVar s1; LVar s2 ] ) :: !intersections) rsets) lvars;
	(* 4. *)
	List.iter (fun a -> 
		(match a with
		| LLess (LVar v1, LVar v2) -> 
			(match (Hashtbl.mem lvars v1), (Hashtbl.mem lvars v2) with
			| true, true -> 
					intersections := (SLExpr.of_list [ LESet [ LVar v1 ]; LESet [ LVar v2 ] ] ) :: !intersections;
					let rsets = Hashtbl.find_all lvars v2 in
					List.iter (fun s2 -> intersections := (SLExpr.of_list [ LESet [ LVar v1 ]; LVar s2 ] ) :: !intersections) rsets;
			| true, false 
			| false, true ->
					intersections := (SLExpr.of_list [ LESet [ LVar v1 ]; LESet [ LVar v2 ] ] ) :: !intersections;
			| _, _ -> ()
			);
		| _ -> ())) pfs;
	let intersections = List.map (fun s -> SLExpr.elements s) !intersections in
	List.sort compare intersections
	
let resolve_set_existentials lpfs rpfs exists gamma =

	let exists = ref exists in

	let set_exists = SS.filter (fun x -> Hashtbl.mem gamma x && (Hashtbl.find gamma x = SetType)) !exists in
	if (SS.cardinal set_exists > 0) then (
	let intersections = get_set_intersections ((DynArray.to_list lpfs) @ (DynArray.to_list rpfs)) in
	print_debug_petar (Printf.sprintf "Intersections we have:\n%s"
		(String.concat "\n" (List.map (fun s -> String.concat ", " (List.map (fun e -> string_of_logic_expression e) s)) intersections)));
					
	let i = ref 0 in
	while (!i < DynArray.length rpfs) do
		let a = DynArray.get rpfs !i in
		(match a with
		| LEq (LSetUnion ul, LSetUnion ur) -> 
				let sul = SLExpr.of_list ul in
				let sur = SLExpr.of_list ur in
				print_debug_petar "Resolve set existentials: I have found a union equality.";
				print_debug_petar (JSIL_Print.string_of_logic_assertion a);
				
				(* Trying to cut the union *)
				let same_parts = SLExpr.inter sul sur in
				print_debug_petar (Printf.sprintf "Same parts: %s" (String.concat ", " (List.map (fun x -> string_of_logic_expression x) (SLExpr.elements same_parts))));
				if (SLExpr.cardinal same_parts = 1) then (
					let must_not_intersect = SLExpr.diff (SLExpr.union sul sur) same_parts in
					print_debug_petar (Printf.sprintf "%s must not intersect any of %s" 
						(String.concat ", " (List.map (fun x -> string_of_logic_expression x) (SLExpr.elements same_parts)))
						(String.concat ", " (List.map (fun x -> string_of_logic_expression x) (SLExpr.elements must_not_intersect))));
					let element : jsil_logic_expr = List.hd (SLExpr.elements same_parts) in 
					let must_not_intersect = List.map (fun s -> List.sort compare [ s; element ]) (SLExpr.elements must_not_intersect) in
					print_debug_petar (Printf.sprintf "Intersections we need:\n%s"
							(String.concat "\n" (List.map (fun s -> String.concat ", " (List.map (fun e -> string_of_logic_expression e) s)) must_not_intersect)));
					let must_not_intersect = List.map (fun s -> List.mem s intersections) must_not_intersect in
					print_debug_petar (Printf.sprintf "And we have: %s" (String.concat ", " (List.map (fun (x : bool) -> if (x = true) then "true" else "false") must_not_intersect)));
					let must_not_intersect = SB.elements (SB.of_list must_not_intersect) in
					if (must_not_intersect = [ true ]) then (
						let success = ref true in
						let cl = SLExpr.diff sul same_parts in
						let cr = SLExpr.diff sur same_parts in
						let lhs = if (SLExpr.cardinal cl = 1) then (List.hd (SLExpr.elements cl)) else LSetUnion (SLExpr.elements cl) in
						let rhs = if (SLExpr.cardinal cr = 1) then (List.hd (SLExpr.elements cr)) else LSetUnion (SLExpr.elements cr) in
						(* CAREFULLY substitute *)
						(match lhs with
						| LVar v when (SS.mem v set_exists) ->
								print_debug_petar (Printf.sprintf "Managed to instantiate a set existential: %s" v);
								let temp_subst = Hashtbl.create 1 in
								Hashtbl.add temp_subst v rhs;
								pfs_substitution_in_place temp_subst rpfs;
								exists := SS.remove v !exists;
								while (Hashtbl.mem gamma v) do Hashtbl.remove gamma v done;
								DynArray.delete rpfs !i
						| _ -> DynArray.set rpfs !i (LEq (lhs, rhs)); i := !i + 1;)
						) else i := !i + 1
				) else i := !i + 1;
				
		| _ -> i := !i + 1;);
	done;

	rpfs, !exists, gamma) else rpfs, !exists, gamma
	
	
	
let find_impossible_unions lpfs rpfs exists gamma =
	
	let exists = ref exists in

	let set_exists = SS.filter (fun x -> Hashtbl.mem gamma x && (Hashtbl.find gamma x = SetType)) !exists in
	if (SS.cardinal set_exists > 0) then (
	let intersections = get_set_intersections ((DynArray.to_list lpfs) @ (DynArray.to_list rpfs)) in
	print_debug_petar (Printf.sprintf "Intersections we have:\n%s"
		(String.concat "\n" (List.map (fun s -> String.concat ", " (List.map (fun e -> string_of_logic_expression e) s)) intersections)));
	
	try (
	let i = ref 0 in
	while (!i < DynArray.length rpfs) do
		let a = DynArray.get rpfs !i in
		(match a with
		| LEq (LSetUnion ul, LSetUnion ur) -> 
				let sul = SLExpr.of_list ul in
				let sur = SLExpr.of_list ur in
				print_debug_petar "Find impossible unions: I have found a union equality.";
				
				(* Just for the left *)
				SLExpr.iter (fun s1 ->
					let must_not_intersect = List.map (fun s -> List.sort compare [ s; s1 ]) (SLExpr.elements sur) in
					print_debug_petar (Printf.sprintf "Intersections we need:\n%s"
							(String.concat "\n" (List.map (fun s -> String.concat ", " (List.map (fun e -> string_of_logic_expression e) s)) must_not_intersect)));
					let must_not_intersect = List.map (fun s -> List.mem s intersections) must_not_intersect in
					print_debug_petar (Printf.sprintf "And we have: %s" (String.concat ", " (List.map (fun (x : bool) -> if (x = true) then "true" else "false") must_not_intersect)));
					let must_not_intersect = SB.elements (SB.of_list must_not_intersect) in
					if (must_not_intersect = [ true ]) then raise (Failure "Oopsie!");
				) sul;
				
				(* Continue if we survived *)
				i := !i + 1;
		
		| _ -> i := !i + 1;);
		done;	
	
		rpfs, !exists, gamma) with
		| Failure _ -> DynArray.of_list [ LFalse ], SS.empty, Hashtbl.create 1) else rpfs, !exists, gamma



let simplify_implication exists lpfs rpfs gamma =
	let lpfs, rpfs, exists, gamma = simplify_pfs_with_exists_and_others exists lpfs rpfs gamma in
	let exists, lpfs, rpfs, gamma = simplify_existentials exists lpfs rpfs gamma in
	let rpfs, exists, gamma = resolve_set_existentials lpfs rpfs exists gamma in
	let rpfs, exists, gamma = find_impossible_unions   lpfs rpfs exists gamma in
	sanitise_pfs_no_store gamma rpfs;
	clean_up_stuff exists lpfs rpfs;
	print_debug_petar (Printf.sprintf "Finished existential simplification:\n\nExistentials:\n%s\nLeft:\n%s\nRight:\n%s\n\nGamma:\n%s\n\n"
		(String.concat ", " (SS.elements exists))
		(string_of_pfs lpfs)
		(string_of_pfs rpfs)
		(Symbolic_State_Print.string_of_gamma gamma)); 
	exists, lpfs, rpfs, gamma (* DO THE SUBST *)

let trim_down (exists : SS.t) (lpfs : jsil_logic_assertion DynArray.t) (rpfs : jsil_logic_assertion DynArray.t) gamma = 
	try (
  	let lhs_lvars = pfs_lvars lpfs in
  	let rhs_lvars = pfs_lvars rpfs in
  	let diff = SS.diff (SS.diff rhs_lvars lhs_lvars) exists in
  	
  	if (DynArray.length rpfs = 1) then (
			let pf = DynArray.get rpfs 0 in
			(match pf with
			| LEq (LVar v1, LVar v2)
			| LLess (LVar v1, LVar v2)
			| LLessEq (LVar v1, LVar v2) 
			| LNot (LEq (LVar v1, LVar v2))
			| LNot (LLess (LVar v1, LVar v2))
			| LNot (LLessEq (LVar v1, LVar v2)) ->
					if (v1 <> v2 && (SS.mem v1 diff || SS.mem v2 diff)) then raise (Failure "")
			| _ -> ())
		);
  	
  	let i = ref 0 in
  	while (!i < DynArray.length lpfs) do
  		let pf = DynArray.get lpfs !i in
  		let pf_lvars = get_asrt_lvars pf in
  		let inter_empty = (SS.inter rhs_lvars pf_lvars = SS.empty) in 
  		(match inter_empty with
  		| true -> 
  				print_debug_petar (Printf.sprintf "Removing from lhs:\n\t%s" (JSIL_Print.string_of_logic_assertion pf)); DynArray.delete lpfs !i 
  		| false -> i := !i + 1)
  	done;
  	true, exists, lpfs, rpfs, gamma)
	with
	| Failure _ -> false, exists, lpfs, rpfs, gamma


let aux_find_me_Im_a_loc pfs gamma v = 
	let _, subst = simplify_pfs_with_subst pfs gamma in
	(match subst with
	| None -> None
	| Some subst -> 
			let w = Hashtbl.find subst v in
				(match w with
				| ALoc w 
				| LLit (Loc w) -> Some w
				| _ -> None))

(** This function is dramatically incomplete **)

	
(* ******************** *
 * EXPRESSION REDUCTION *
 * ******************** *)

let reduce_expression_using_pfs_no_store gamma pfs e =
	let _, subst = simplify_pfs_with_subst pfs gamma in
	(match subst with
	| None -> e
	| Some subst ->
		let e = lexpr_substitution subst true e in
			reduce_expression_no_store gamma pfs e)
			
(* ******************************** *
 * CONGRUENCE CLOSURE APPROXIMATION *
 * ********************************** *)

(* No entailment *)
let cc_from_subst (subst : (string, jsil_logic_expr) Hashtbl.t) : (jsil_logic_expr, SLExpr.t) Hashtbl.t =
	let cc_table : (jsil_logic_expr, SLExpr.t) Hashtbl.t = Hashtbl.create 57 in
	
	let establish_initial_cc () = 
		Hashtbl.iter (fun key value -> 
			let var = (match (is_pvar_name key) with
				| true -> PVar key 
				| false -> LVar key) in
			Hashtbl.add cc_table var (SLExpr.add value (SLExpr.singleton var))) subst in
		
	establish_initial_cc();
	
	let changes_made = ref true in
	
	while (!changes_made) do
		changes_made := false;
	done;
	
	cc_table