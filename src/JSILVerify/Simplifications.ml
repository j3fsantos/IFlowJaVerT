open CCommon
open SCommon
open JSIL_Syntax
open JSIL_Logic_Utils
open Symbolic_State
open JSIL_Print 
open Symbolic_State_Print

exception FoundIt of jsil_logic_expr
exception UnionInUnion of jsil_logic_expr list

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

let all_set_literals lset = List.fold_left (fun x le -> 
	let result = (match le with
		| LESet _ -> true
		| _ -> false) in
	(* print_debug (Printf.sprintf "All literals: %s -> %b" (string_of_logic_expression le) result); *)
	x && result
	) true lset 

(* Reduction of assertions *)
let rec reduce_assertion ?(no_timing: unit option) ?(gamma : TypEnv.t option) ?(pfs : PFS.t option) a =

	let start_time = Sys.time () in

	let f = reduce_assertion ?no_timing:(Some ()) ?gamma:gamma ?pfs:pfs in
	let fe = Reduction.reduce_lexpr ?gamma:gamma ?pfs:pfs in

	let result = (match a with

	| LStar (a1, a2) ->
		let fa1  = f a1 in
		let fa2 = f a2 in
		(match fa1, fa2 with
		| LFalse, _
		| _, LFalse -> LFalse
		| LTrue, a
		| a, LTrue -> a
		| _, _ -> LStar (fa1, fa2)
		)

	| LAnd (a1, a2) ->
		let fa1 = f a1 in
		let fa2 = f a2 in
		(match fa1, fa2 with
		| LFalse, _
		| _, LFalse -> LFalse
		| LTrue, a
		| a, LTrue -> a
		| _, _ -> LAnd (fa1, fa2)
		)

	| LOr (a1, a2) ->
		let fa1 = f a1 in
		let fa2 = f a2 in
		(match fa1, fa2 with
		| LFalse, a
		| a, LFalse -> a
		| LTrue, a
		| a, LTrue -> LTrue
		| _, _ -> LOr (fa1, fa2)
		)

	| LNot a -> 
		let fa = f a in 
		(match a with 
		| LTrue -> LFalse
		| LFalse -> LTrue
		| LNot a -> a
		| LOr (a1, a2) -> f (LAnd (LNot a1, LNot a2))
		| LAnd (a1, a2) -> f (LOr (LNot a1, LNot a2))
		| _ -> LNot fa)

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
			| PVar x, LNone -> default e1 e2 re1 re2
			| LNone, LVar x
			| LVar x, LNone -> 
				(match gamma with
				| None -> default e1 e2 re1 re2
				| Some gamma -> let tx = TypEnv.get gamma x in
					(match tx with 
					| None -> default e1 e2 re1 re2
					| Some tx -> if tx = NoneType then default e1 e2 re1 re2 else LFalse)
				)
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
						let pfs = PFS.to_list (Option.default (DynArray.create ()) pfs) in 
						if ((List.mem (LNot (LEq (LStrNth (LVar x, LLit (Num 0.)), LLit (String "@")))) pfs)  ||
							 (List.mem (LNot (LEq (LLit (String "@"), LStrNth (LVar x, LLit (Num 0.))))) pfs))
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
			| LUnOp (TypeOf, (LBinOp (_, StrCat, _))), LLit (Type t) when (t <> StringType)  -> LFalse
			| LUnOp (TypeOf, (LBinOp (_, SetMem, _))), LLit (Type t) when (t <> BooleanType) -> LFalse
			
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

	| LForAll (bt, a) -> (* Think about quantifier instantiation *)
			let ra = f a in
			let vars = get_asrt_lvars a in
			let bt = List.filter (fun (b, _) -> SS.mem b vars) bt in
			(match bt with
			| [] -> ra
			| _ -> LForAll (bt, ra))

	| _ -> a) in

	let final_result = if (a <> result) && (not (a == result))
		then (print_debug (Printf.sprintf "Reduce_assertion: %s -> %s" (JSIL_Print.string_of_logic_assertion a) (JSIL_Print.string_of_logic_assertion result)); f result)
		else result in

	if (no_timing = None) then (let end_time = Sys.time () in update_statistics "reduce_assertion" (end_time -. start_time));
	final_result


let simplify_equalities_between_booleans (p_assertions : PFS.t) = 
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

let naively_infer_type_information (p_assertions : PFS.t) (gamma : TypEnv.t) = 
 	DynArray.iter 
 		(fun a -> 
 			match a with 
 			| LEq (LVar x, le) 
 			| LEq (le, LVar x) -> 
 				if (not (TypEnv.mem gamma x)) 
 					then (
 						let le_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
 						TypEnv.weak_update gamma x le_type
 					)
 			| LEq ((LUnOp (TypeOf, LVar x)), (LLit (Type t))) 
 			| LEq ((LLit (Type t)), (LUnOp (TypeOf, LVar x))) ->
 				TypEnv.weak_update gamma x (Some t)
 			| _ -> () 
 		) p_assertions


 let naively_infer_type_information_symb_state (symb_state : symbolic_state) = 
 	let gamma = ss_gamma symb_state in 
 	let pfs = ss_pfs symb_state in 
 	naively_infer_type_information pfs gamma

(*************************************)
(** Symbolic state simplification   **)
(*************************************)

let reduce_pfs_in_place store gamma pfs =
	DynArray.iteri (fun i pf ->
		let rpf = reduce_assertion ?gamma:(Some gamma) ?pfs:(Some pfs) pf in
		DynArray.set pfs i rpf) pfs
	
let sanitise_pfs store gamma pfs =
	
	reduce_pfs_in_place store gamma pfs;
			
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

let sanitise_pfs_no_store_no_gamma = sanitise_pfs (Hashtbl.create 1) (TypEnv.init())
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
	TypEnv.filter_vars_in_place gamma pfs_vars
	
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
	let le1 = Reduction.reduce_lexpr le1 in
	let le2 = Reduction.reduce_lexpr le2 in
	let le1_old = le1 in
	let le1, le2 = arrange_lists le1 le2 in
	let to_swap_now = (le1_old <> le1) in
	let to_swap = (to_swap <> to_swap_now) in
	let swap (le1, le2) = if to_swap then (le2, le1) else (le1, le2) in
	(* print_debug_petar (Printf.sprintf "unify_lists: \n\t%s\n\t\tand\n\t%s" 
		(string_of_logic_expression le1) (string_of_logic_expression le2)); *) 
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

(* *********************** *
 * ULTIMATE SIMPLIFICATION *
 * *********************** *)

let rec understand_types exists pf_list (gamma : TypEnv.t) : bool = 
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
						then TypEnv.update gamma y (Some t1); 
						f rest gamma
					| None, Some t2 ->
							if ((from_where = "l") || ((from_where = "r") && (SS.mem x exists))) 
							then TypEnv.update gamma x (Some t2); 
							f rest gamma 
					| Some t1, Some t2 -> f rest gamma
					| None, None -> raise (Failure "Impossible branch."))
				| LVar x, le
				| le, LVar x ->
					(* print_debug (Printf.sprintf "Checking: (%s, %s) vs %s" x from_where (JSIL_Print.string_of_logic_expression le false)); *)
					let tx = TypEnv.get gamma x in
					let te, _, _ = type_lexpr gamma le in
					(match te with
					| None -> f rest gamma
					| Some te ->
						(match tx with
						| None -> 
								if ((from_where = "l") || ((from_where = "r") && (SS.mem x exists)))
								then TypEnv.update gamma x (Some te); 
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
let type_index (t : Type.t) = 
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
	| SetType       -> 10)

let type_length = 12

let simplify_symb_state 
	(vars_to_save : (SS.t option) option)
	(other_pfs    : jsil_logic_assertion DynArray.t)
	(existentials : SS.t)
	(symb_state   : symbolic_state) : symbolic_state * substitution * PFS.t * SS.t =

	print_time_debug "simplify_symb_state:";

	print_debug_petar (Printf.sprintf "Symbolic state before simplification:\n%s" (Symbolic_State_Print.string_of_symb_state symb_state));  
		
	let initial_existentials = ref existentials in

	let vars_to_save, save_all = 
		(match vars_to_save with
		| Some (Some v) -> v, false 
		| Some None     -> SS.empty, true
		| None          -> SS.empty, false) in

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
			(TypEnv.iter gamma (fun v (t : Type.t) -> 
				let lexpr = (match t with
					| UndefinedType -> Some (LLit Undefined)
					| NullType -> Some (LLit Null)
					| EmptyType -> Some (LLit Empty)
					| NoneType -> Some LNone
					| _ -> None) in
				(match lexpr with
				| Some lexpr -> 
						(* print_debug (Printf.sprintf "Singleton: (%s, %s)" v (Type.str t)); *)
						Hashtbl.add subst v lexpr;
				| None -> ()));
			(* Substitute *)
			let symb_state = ss_substitution subst true symb_state in
			let others = pfs_substitution subst true others in
			let exists = Hashtbl.fold (fun v _ ac -> SS.remove v ac) subst exists in
			(* and remove from gamma, if allowed *)
			Hashtbl.iter (fun v _ ->
				match (save_all || SS.mem v (SS.union vars_to_save !initial_existentials)) with
				| true -> ()
				| false -> 
						while (TypEnv.mem gamma v) do 
							let t = TypEnv.get_unsafe gamma v in
							let it = type_index t in
							types.(it) <- types.(it) - 1;
							TypEnv.update gamma v None
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
					| _, true -> ()
					| true, false -> DynArray.set pfs i (LEq (LVar v2, LVar v1))
					| false, false -> 
						let lvar_v1 = (String.get v1 0 = '#') in
						let lvar_v2 = (String.get v2 0 = '#') in
						(match lvar_v1, lvar_v2 with
						| true, false -> DynArray.set pfs i (LEq (LVar v2, LVar v1))
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
	let lvars = SS.union (ss_vars_no_gamma symb_state) (pfs_lvars other_pfs) in
	let lvars_gamma = TypEnv.lvars gamma in		
	let lvars_inter = SS.inter lvars lvars_gamma in
	TypEnv.filter_vars_in_place gamma (SS.union lvars_inter (SS.union vars_to_save !initial_existentials));
		
	(* Setup the type indexes *)
	let types = Array.make type_length 0 in
	TypEnv.iter gamma (fun _ t -> 
		let it = type_index t in
			types.(it) <- types.(it) + 1);
		
	(* Instantiate uniquely determined variables *)
	let subst = Hashtbl.create 57 in
	let symb_state, subst, others, exists = simplify_singleton_types other_pfs !initial_existentials symb_state subst types in

	let pfs = ss_pfs symb_state in

	let changes_made = ref true in
	let symb_state   = ref symb_state in
	let others       = ref others in
	let exists       = ref exists in
	let pfs_ok       = ref true in
	let msg          = ref "" in
	
	sanitise_pfs store gamma pfs;

	(* MAIN LOOP *)
	while (!changes_made && !pfs_ok) do

		changes_made := false;
		
		let (heap, store, pfs, gamma, preds) = !symb_state in

		arrange_pfs vars_to_save save_all !exists pfs;
		
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
				let te1, _, _ = JSIL_Logic_Utils.type_lexpr gamma le1 in
				let te2, _, _ = JSIL_Logic_Utils.type_lexpr gamma le2 in
				(match te1, te2 with
				| Some te1, Some te2 when (te1 <> te2) -> 
						pfs_ok := false; msg := 
							Printf.sprintf "Type mismatch: %s:%s -> %s:%s" 
								(JSIL_Print.string_of_logic_expression le1) (Type.str te1) 
								(JSIL_Print.string_of_logic_expression le2) (Type.str te2)
				| _ -> (match le1, le2 with

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
						let tle, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in 
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
								(match (TypEnv.get gamma v) with
								| None -> ()
								| Some t -> 
									(match (TypEnv.get gamma v') with
									| None -> 
										let it = type_index t in
										types.(it) <- types.(it) + 1;
										TypEnv.update gamma v' (Some t)
									| Some t' -> 
										(match (t = t') with
										| false -> pfs_ok := false; msg := "Horrific type mismatch."
										| true -> ()))
								)
							| _ -> ());
									
								
							(* Remove (or add) from (or to) gamma *)
							(match (save_all || SS.mem v (SS.union vars_to_save !exists)) with
				      		| true -> 
								let le_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
								(match le_type with
								| None -> ()
								| Some t -> 
									(match TypEnv.get gamma v with
									| None -> 
										let it = type_index t in
										types.(it) <- types.(it) + 1;
										(* print_debug_petar (Printf.sprintf "GAT: %s : %s" v (Type.str t)); *)
										TypEnv.update gamma v (Some t)
									| Some tv -> 
										(match (tv = t) with
										| true -> ()
										| false ->
												(* print_debug_petar (Printf.sprintf "Type mismatch: %s -> %s, but %s." v (Type.str tv) (Type.str t)); *) 
												pfs_ok := false; msg := "Horrific type mismatch.")))
				      		| false -> 
								while (TypEnv.mem gamma v) do 
									let t = TypEnv.get_unsafe gamma v in
									let it = type_index t in
									types.(it) <- types.(it) - 1;
										(* print_debug_petar (Printf.sprintf "Removing from gamma: %s" v); *)
									TypEnv.update gamma v None 
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
									TypEnv.update gamma back (Some ListType);
									let front = List.map (fun x -> LVar x) front in
									let back = LVar back in
									
									let new_lst = LBinOp (LEList front, LstCat, (LBinOp (le, LstCons, back))) in
									
									(* Changes made, stay on n *)
									changes_made := true;
									DynArray.delete pfs !n;
									let new_pf = LEq (lst, new_lst) in
									let new_pf = reduce_assertion ?gamma:(Some gamma) ?pfs:(Some pfs) new_pf in
									DynArray.add pfs new_pf
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
							List.iter (fun (x, y) -> 
								let new_pf = LEq (x, y) in
								let new_pf = reduce_assertion ?gamma:(Some gamma) ?pfs:(Some pfs) new_pf in
								DynArray.add pfs new_pf) subst)
				
				| LUnOp (TypeOf, LVar x), LLit (Type t) -> 
					changes_made := true;
					DynArray.delete pfs !n;
					let ot = TypEnv.get gamma x in
						(match ot with
						| None -> TypEnv.update gamma x (Some t)
						| Some t' -> if (t <> t') then (pfs_ok := false; msg := "Typing error")
						);
						changes_made := true;

				| _, _ -> n := !n + 1))
			
			(* Special cases *)
			| LNot (LEq (ALoc _, LLit Empty)) 
			| LNot (LEq (LLit Empty, ALoc _))
			| LNot (LEq (ALoc _, LLit Null)) 
			| LNot (LEq (LLit Null, ALoc _)) ->
					DynArray.delete pfs !n
					
			| LNot (LEq (LVar v, LLit Empty)) 
			| LNot (LEq (LLit Empty, LVar v)) ->
				(match (TypEnv.get gamma v) with
				| None -> n := !n + 1
				| Some t -> 	
					(match (t = EmptyType) with
					| true -> pfs_ok := false; msg := "Negation incorrect."
					| false -> DynArray.delete pfs !n))
			| _ -> n := !n + 1);
		done;
	done;

	Hashtbl.iter (fun var lexpr -> 
		(match (not (SS.mem var !initial_existentials) && (save_all || SS.mem var vars_to_save)) with
		| false -> ()
		| true -> DynArray.add pfs (LEq (LVar var, lexpr)))
		) subst;

	(* print_debug_petar (Printf.sprintf "Symbolic state after simplification:\n%s" (Symbolic_State_Print.string_of_shallow_symb_state !symb_state)); *) 
	
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
	let fake_symb_state = (Heap.create 1, SStore.init [] [], (DynArray.copy pfs), (TypEnv.copy gamma), DynArray.create ()) in
	let (_, _, pfs, gamma, _), _, _, _ = simplify_symb_state vars_to_save (DynArray.create()) (SS.empty) fake_symb_state in
	pfs, gamma
			
let simplify_pfs_with_subst pfs gamma =
	let fake_symb_state = (Heap.create 1, SStore.init [] [], (DynArray.copy pfs), (TypEnv.copy gamma), DynArray.create ()) in
	let (_, _, pfs, gamma, _), subst, _, _ = simplify_symb_state None (DynArray.create()) (SS.empty) fake_symb_state in
	if (DynArray.to_list pfs = [ LFalse ]) then (pfs, None) else (pfs, Some subst)

let simplify_pfs_with_exists exists lpfs gamma vars_to_save = 
	let fake_symb_state = (Heap.create 1, SStore.init [] [], (DynArray.copy lpfs), (TypEnv.copy gamma), DynArray.create ()) in
	let (_, _, lpfs, gamma, _), _, _, exists = simplify_symb_state vars_to_save (DynArray.create()) exists fake_symb_state in
	lpfs, exists, gamma

let simplify_pfs_with_exists_and_others exists lpfs rpfs gamma = 
	let fake_symb_state = (Heap.create 1, SStore.init [] [], (DynArray.copy lpfs), (TypEnv.copy gamma), DynArray.create ()) in
	let (_, _, lpfs, gamma, _), _, rpfs, exists = simplify_symb_state None rpfs exists fake_symb_state in
	lpfs, rpfs, exists, gamma

(* ************************** *
 * IMPLICATION SIMPLIFICATION *
 * ************************** *)
	
let rec simplify_existentials (exists : SS.t) lpfs (p_formulae : jsil_logic_assertion DynArray.t) (gamma : TypEnv.t) =

	(* print_time_debug ("simplify_existentials:"); *)
	
	let rhs_gamma = TypEnv.copy gamma in
	filter_gamma_pfs p_formulae rhs_gamma;
	
	let p_formulae, exists, _ = simplify_pfs_with_exists exists p_formulae rhs_gamma (Some None) in
	
	(* print_debug (Printf.sprintf "PFS: %s" (Symbolic_State_Print.string_of_shallow_p_formulae p_formulae false)); *)

	let pfs_false msg =
		print_debug_petar (msg ^ " Pure formulae false.\n");
		DynArray.clear p_formulae;
		DynArray.add p_formulae LFalse;
		SS.empty, lpfs, p_formulae, TypEnv.init() in

	let delete_substitute_proceed exists p_formulae (gamma : TypEnv.t) v n le =
		(* print_debug (Printf.sprintf "Deleting the formula \n%s\nand substituting the variable %s for %s." 
			(JSIL_Print.string_of_logic_assertion (DynArray.get p_formulae n) false) 
			v (JSIL_Print.string_of_logic_expression le false)); *)
		DynArray.delete p_formulae n;
		let exists = SS.remove v exists in
		while (TypEnv.mem gamma v) do TypEnv.update gamma v None done;
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

	let rec go_through_pfs (pfs : jsil_logic_assertion list) n : SS.t * PFS.t * PFS.t * TypEnv.t =
	(match pfs with
	 | [] -> if (test_for_nonsense (PFS.to_list p_formulae))
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
		   | false -> 
		   		print_debug_petar ("Target case: " ^ v ^ " = " ^ JSIL_Print.string_of_logic_expression le);
		   		go_through_pfs rest (n + 1)
		   | true ->
		       (* Why? - if not in gamma and we can type the thing on the right, add to gamma *)
			   (match (TypEnv.get gamma v) with
			    | None -> 
					(match le with
						 | LLit lit ->
							 let ltype = Literal.type_of lit in
							 TypEnv.update gamma v (Some ltype);
							 delete_substitute_proceed exists p_formulae gamma v n le
						 | ALoc _ ->
						 	 TypEnv.update gamma v (Some ObjectType);
							 delete_substitute_proceed exists p_formulae gamma v n le
						 | LEList _
						 | LBinOp (_, LstCons, _) ->
						 	 TypEnv.update gamma v (Some ListType);
							 let can_we_substitute = isExistentiallySubstitutable le in
							 (match can_we_substitute with
							  | false -> go_through_pfs rest (n + 1)
							  | true -> delete_substitute_proceed exists p_formulae gamma v n le
							 )
						 | LBinOp (_, StrCat, _) ->
						 	 TypEnv.update gamma v (Some StringType);
							 let can_we_substitute = isExistentiallySubstitutable le in
							 (match can_we_substitute with
							  | false -> go_through_pfs rest (n + 1)
							  | true -> delete_substitute_proceed exists p_formulae gamma v n le
							 )
						 | _ -> go_through_pfs rest (n + 1))
				| Some vtype ->
					(match le with
					 | LLit lit ->
					     let ltype = Literal.type_of lit in
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
	
let resolve_set_existentials lpfs rpfs exists (gamma : TypEnv.t) =

	let exists = ref exists in

	let set_exists = SS.filter (fun x -> TypEnv.get gamma x = Some SetType) !exists in
	if (SS.cardinal set_exists > 0) then (
	let intersections = get_set_intersections ((DynArray.to_list lpfs) @ (DynArray.to_list rpfs)) in
	print_debug_petar (Printf.sprintf "Intersections we have:\n%s"
		(String.concat "\n" (List.map (fun s -> String.concat ", " (List.map (fun e -> string_of_logic_expression e) s)) intersections)));
					
	let i = ref 0 in
	while (!i < DynArray.length rpfs) do
		let a = DynArray.get rpfs !i in
		(match a with
		| LEq (LSetUnion ul, LSetUnion ur) -> 
				(* Expand LESets *)
				let ul = List.flatten (List.map (fun u -> (match u with | LESet x -> List.map (fun x -> LESet [ x ]) x | _ -> [ u ])) ul) in
				let ur = List.flatten (List.map (fun u -> (match u with | LESet x -> List.map (fun x -> LESet [ x ]) x | _ -> [ u ])) ur) in

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
								while (TypEnv.mem gamma v) do TypEnv.update gamma v None done;
								DynArray.delete rpfs !i
						| _ -> DynArray.set rpfs !i (LEq (lhs, rhs)); i := !i + 1;)
						) else i := !i + 1
				) else i := !i + 1;
				
		| _ -> i := !i + 1;);
	done;

	rpfs, !exists, gamma) else rpfs, !exists, gamma
	
	
	
let find_impossible_unions lpfs rpfs exists (gamma : TypEnv.t) =
	
	let exists = ref exists in

	let set_exists = SS.filter (fun x -> TypEnv.get gamma x = Some SetType) !exists in
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
		| Failure _ -> DynArray.of_list [ LFalse ], SS.empty, TypEnv.init()) else rpfs, !exists, gamma



let simplify_implication exists lpfs rpfs (gamma : TypEnv.t) =
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
		(TypEnv.str gamma)); 
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
  	
  	(* THIS IS UNSOUND, FIX *)
  	let i = ref 0 in
  	while (!i < DynArray.length lpfs) do
  		let pf = DynArray.get lpfs !i in
  		let pf_lvars = get_asrt_lvars pf in
  		let inter_empty = (SS.inter rhs_lvars pf_lvars = SS.empty) in 
  		(match inter_empty with
  		| true -> DynArray.delete lpfs !i 
  		| false -> i := !i + 1)
  	done;
  	true, exists, lpfs, rpfs, gamma)
	with
	| Failure _ -> false, exists, lpfs, rpfs, gamma

let now_do_some_more_heuristics (exists : SS.t) (lpfs : jsil_logic_assertion DynArray.t) (rpfs : jsil_logic_assertion DynArray.t) gamma =
	
	(* There is only one formula, and the lhs is empty *)
	if (DynArray.length rpfs = 1) then
	(
		let pf = DynArray.get rpfs 0 in

		(match pf with
		| LEq (LVar v, le)
		| LEq (le, LVar v) when (DynArray.length lpfs = 0) ->
			(match le with
			| LLit _  
			| LNone -> 
				let tl, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
				let tl = Option.get tl in 
				let tv = TypEnv.get gamma v in
				(match tv with
				| None -> Some (SS.mem v exists)
				| Some tv -> if (tl <> tv) then Some false else Some (SS.mem v exists || tv = Type.UndefinedType || tv = Type.NullType || tv = Type.NoneType || tv = Type.EmptyType)
				)
			| _ -> None
			)
		| LNot (LEq (LVar v, le))
		| LNot (LEq (le, LVar v)) when (DynArray.length lpfs = 0) ->
			(match le with
			| LLit _  
			| LNone -> 
				let tl, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
				let tl = Option.get tl in 
				let tv = TypEnv.get gamma v in
				(match tv with
				| None -> Some (SS.mem v exists)
				| Some tv -> if (tl <> tv) then Some true else Some (not (SS.mem v exists || tv = Type.UndefinedType || tv = Type.NullType || tv = Type.NoneType || tv = Type.EmptyType))
				)
			| _ -> None
			)
		
		(* Perhaps a bit unsound *)
		| LEq (LUnOp (TypeOf, LVar tv), LLit (Type _))
		| LEq (LLit (Type _), LUnOp (TypeOf, LVar tv)) -> Some (SS.mem tv exists)
		| _ -> None
		)
	) else None

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
			Reduction.reduce_lexpr ?gamma:(Some gamma) ?pfs:(Some pfs) e)

(* Assume le = target, understand equalities, put in subst. It's all about le, nothing about the target *)
let rec subst_for_unification_plan ?(gamma : TypEnv.t option) le target subst : jsil_logic_assertion list option =
	print_debug (Printf.sprintf "SfUP: %s -> %s with %s" (JSIL_Print.string_of_logic_expression le) (JSIL_Print.string_of_logic_expression target) (JSIL_Print.string_of_substitution subst));
	(* Here goes, essentially, what Jose wrote on the whiteboard yesterday *)
	(match le with 
	| LLit _ 
	| LEList [] -> Some [ LEq (le, target) ]
	| ALoc x
	| LVar x -> 
		let le' = Hashtbl.find_opt subst x in 
		(match le' with 
		| None -> 
			print_debug (Printf.sprintf "SfUP: adding %s : %s" x (JSIL_Print.string_of_logic_expression target));
			Hashtbl.add subst x target;
			Some []
		| Some le' -> 
			print_debug (Printf.sprintf "SfUP: already in subst: %s : %s --> %s" x (JSIL_Print.string_of_logic_expression le') (JSIL_Print.string_of_logic_expression target));
			let check = reduce_assertion ?gamma:gamma (LEq (le', target)) in 
			(match check with 
			| LFalse -> None
			| LTrue  -> Hashtbl.replace subst x target; Some []
			| _ -> Some [ LEq (le', target) ])
			)
	| _ when Reduction.lexpr_is_list ?gamma:gamma le ->
		print_debug (Printf.sprintf "SfUP: list %s" (JSIL_Print.string_of_logic_expression le));
		let res = Reduction.get_head_and_tail_of_list le in
		(match res with
			| Some (head, tail) ->
				let head = Reduction.reduce_lexpr ?gamma:gamma head in  
				let tail = Reduction.reduce_lexpr ?gamma:gamma tail in  
				let red_target_head = Reduction.reduce_lexpr ?gamma:gamma (LUnOp (Car, target)) in
				let red_target_tail = Reduction.reduce_lexpr ?gamma:gamma (LUnOp (Cdr, target)) in
				Option.map_default  
					(fun pfs_head -> 
						Option.map_default
							(fun pfs_tail -> Some (pfs_head @ pfs_tail))
							None 
							(subst_for_unification_plan ?gamma:gamma tail red_target_tail subst)
					)
					None 
					(subst_for_unification_plan ?gamma:gamma head red_target_head subst)  
			| _ ->
				print_debug_petar "SfUP: head_and_tail returned None.";
				Some [ LEq (le, target) ]
		)
	(* NOW, MORE CASES FOR LISTS - LEList, Cons, Cat - there are functions for getting a head of a list in Reduction.ml *)
	(* Otherwise, whatever *)
	| _ -> print_debug (Printf.sprintf "SfUP: don't know how to continue: %s" (JSIL_Print.string_of_logic_expression le)); Some [ LEq (le, target) ]
	);

