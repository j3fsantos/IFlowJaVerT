open JSIL_Syntax
open JSIL_Logic_Utils
open Symbolic_State
open JSIL_Print 
open Symbolic_State_Print

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
			print_debug_petar (Printf.sprintf "BinOp case StrCat"); 
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
		| LBinOp (sel, CharCat, ser) -> (LBinOp ((f sel), StrCat, (f ser)), false)
		| _ -> (se, true))


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
		let e1 = logic_expression_map le_list_to_string e1 in
		let e2 = logic_expression_map le_list_to_string e2 in
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
 			| _ -> () 
 		) p_assertions


 let naively_infer_type_information_symb_state (symb_state : symbolic_state) = 
 	let gamma = get_gamma symb_state in 
 	let pfs = get_pf symb_state in 
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
			let lvs = get_assertion_lvars pf in
				SS.union lvars lvs)
		SS.empty (DynArray.to_list pfs)
	
let filter_gamma_pfs pfs gamma = 
	let pfs_vars = get_pf_vars false pfs in
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
		let msg = Printf.sprintf "Non-list expressions passed to get_head_and_tail_list : %s" (print_lexpr le) in
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
let rec unify_lists (le1 : jsil_logic_expr) (le2 : jsil_logic_expr) to_swap : bool option * ((jsil_logic_expr * jsil_logic_expr) list) = 
	let le1 = reduce_expression_no_store_no_gamma_no_pfs le1 in
	let le2 = reduce_expression_no_store_no_gamma_no_pfs le2 in
	let le1_old = le1 in
	let le1, le2 = arrange_lists le1 le2 in
	let to_swap_now = (le1_old <> le1) in
	let to_swap = (to_swap <> to_swap_now) in
	let swap (le1, le2) = if to_swap then (le2, le1) else (le1, le2) in
	(* print_debug (Printf.sprintf "unify_lists: \n\t%s\n\t\tand\n\t%s" 
		(print_lexpr le1) (print_lexpr le2)); *)
	(match le1, le2 with
	  (* Base cases *)
	  | LLit (LList []), LLit (LList [])
		| LLit (LList []), LEList []
		| LEList [], LEList [] -> Some false, []
		| LVar _, _ -> Some false, [ swap (le1, le2) ]
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
			let (okl, headl, taill) = get_head_and_tail_list le1 in
			let (okr, headr, tailr) = get_head_and_tail_list le2 in
			(* print_debug (Printf.sprintf "Got head and tail: left: %b, right: %b" 
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
				let ok, (ll, lr), (rl, rr) = match_lists_on_element le1 le2 in
				(match ok with
					| true -> 
							let okl, left = unify_lists ll rl to_swap in
							(match okl with
							| None -> None, []
							| _ -> 
								let okr, right = unify_lists lr rr to_swap in
								(match okr with
								| None -> None, []
								| _ -> Some true, left @ right))
					| false -> Some false, [ swap (le1, le2) ])
			(* A proper error occurred while getting head and tail *)
			| _, _ -> None, [])
		| _, _ ->
			let msg = Printf.sprintf "Non-arranged lists passed to unify_lists : %s, %s" (print_lexpr le1) (print_lexpr le2) in
			raise (Failure msg)
	)

(* ******* *
 *         *
 * STRINGS WIP *
 *         *
 * ******* *)

let isString (se : jsil_logic_expr) : bool =
match se with
	| LLit (String _) -> true
	| _ -> false

(* What does it mean to be an internal string? *)
let isInternalString (se : jsil_logic_expr) : bool =
match se with
	| LVar _ 
	| LLit (CList _)
	| LBinOp (_, CharCons, _)         (* Non recursive: assume that CharCat/Cons *)
	| LBinOp (_, CharCat,  _) -> true (* only obtained from conversion anyway    *)
	| LCList _ -> print_debug_petar (Printf.sprintf "Wasn't expecting anything to encode to LCList... Got: %s" (print_lexpr se));
		true
	| _ -> false

(* Arranging strings in a specific order *)
let arrange_strings (se1 : jsil_logic_expr) (se2 : jsil_logic_expr) : (jsil_logic_expr * jsil_logic_expr) =
	match se1, se2 with
		| LVar _, _
		| LLit (CList _), LLit (CList _) 
		| LLit (CList _), LBinOp (_, CharCons, _)
		| LLit (CList _), LBinOp (_, CharCat, _)
		| LBinOp (_, CharCons, _), LBinOp (_, CharCons, _)
		| LBinOp (_, CharCons, _), LBinOp (_, CharCat, _)
		| LBinOp (_, CharCat, _), LBinOp (_, CharCat, _) -> se1, se2
		| _, _ -> se2, se1

(* Extracting elements from an internal string *)
let rec get_elements_from_string (se : jsil_logic_expr) : jsil_logic_expr list =
(match se with
	| LVar _ -> []
	| LLit (CList l) -> List.map (fun e -> LLit e) l
	| LBinOp (e, CharCons, se) -> e :: get_elements_from_string se
	| LBinOp (sel, CharCat, ser) -> get_elements_from_string sel @ get_elements_from_string ser
	| _ -> let msg = Printf.sprintf "Non-list expressions passed to get_elements_from_list : %s" (print_lexpr se) in
		raise (Failure msg))

(* Splitting an internal string based on an element *)
let rec split_string_on_element (se : jsil_logic_expr) (e : jsil_logic_expr) : bool * (jsil_logic_expr * jsil_logic_expr) =
(match se with
	| LVar _ -> false, (se, LLit (CList []))
	| LLit (CList l) -> 
		(match e with
		| LLit lit ->
			let ok, (ll, lr) = list_split l lit in
			(match ok with
			| true -> true, (LLit (CList ll), LLit (CList lr))
			| false -> false, (se, LLit (CList []))
		| _ -> false, (se, LLit (CList []))))
	| LBinOp (e', CharCons, se') -> 
		(match (e = e') with
		| true -> true, (LLit (CList []), se')
		| false -> let ok, (ll, lr) = split_string_on_element se' e in
			(match ok with
			| false -> false, (se, LLit (CList []))
			| true -> true, (LBinOp (e', LstCons, ll), lr)))
	| LBinOp (sel, CharCat, ser) -> 
		let ok, (sll, slr) = split_string_on_element sel e in
		(match ok with
		| true -> 
			let right = 
			(match ser with 
			| LLit (CList []) -> slr
			| _ -> LBinOp (slr, CharCat, ser)) in
				true, (sll, right)
		| false -> let ok, (srl, srr) = split_string_on_element ser e in
			(match ok with
			| true -> 
				let left = (match srl with 
				| LLit (CList []) -> sel
				| _ -> LBinOp (sel, CharCat, srl)) in
					true, (left, srr)
			| false -> false, (se, LLit (CList []))))
	| _ -> let msg = Printf.sprintf "Non-string expressions passed to split_string_on_element : %s" (print_lexpr se) in
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
				| _, _ -> let msg = Printf.sprintf "Element %s that was supposed to be in both strings: %s, %s is not." (print_lexpr i) (print_lexpr se1) (print_lexpr se2) in
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
		print_debug_petar (Printf.sprintf "get_head_and_tail_string on a LCList, how did that get there? %s" (print_lexpr se));
		(match l with
		| [] -> None, LLit (Bool false), LLit (Bool false)
		| e :: l -> Some true, e, LCList l)
	| LBinOp (e, CharCons,  s) -> Some true, e, s
	| LBinOp (s1, CharCat, s2) -> 
		let ok, head, tail = get_head_and_tail_string s1 in
		(match ok with
		| None -> None, LLit (Bool false), LLit (Bool false)
		| Some false -> Some false, LLit (Bool false), LLit (Bool false)
		| Some true -> Some true, head, LBinOp (tail, LstCat, s2))
	| LVar _ -> Some false, LLit (Bool false), LLit (Bool false)
	| _ -> 
		let msg = Printf.sprintf "Non-list expressions passed to get_head_and_tail_list : %s" (print_lexpr se) in
		raise (Failure msg))

(* String unification *)
let rec unify_strings (se1 : jsil_logic_expr) (se2 : jsil_logic_expr) to_swap : bool option * ((jsil_logic_expr * jsil_logic_expr) list) = 
	(* Figure out reductions for these internal string representations... *)
	(* let se1 = reduce_expression_no_store_no_gamma_no_pfs se1 in *)
	(* let se2 = reduce_expression_no_store_no_gamma_no_pfs se2 in *)
	let se1_old = se1 in
	let se1, se2 = arrange_strings se1 se2 in
	let to_swap_now = (se1_old <> se1) in
	let to_swap = (to_swap <> to_swap_now) in
	let swap (se1, se2) = if to_swap then (se2, se1) else (se1, se2) in
	(* print_debug (Printf.sprintf "unify_strings: \n\t%s\n\t\tand\n\t%s" 
		(print_lexpr se1) (print_lexpr se2)); *)
	(match se1, se2 with
	  (* Base cases *)
		| LLit (CList []), LLit (CList []) -> Some false, []
		| LVar _, _ -> Some false, [ swap (se1, se2) ]
		(* Inductive cases *)
		| LLit (CList _), LLit (CList _)
		| LLit (CList _), LBinOp (_, CharCons, _) 
		| LLit (CList _), LBinOp (_, CharCat, _)
		| LBinOp (_, CharCons, _), LBinOp (_, CharCons, _)
		| LBinOp (_, CharCons, _), LBinOp (_, CharCat,  _)
		| LBinOp (_, CharCat,  _), LBinOp (_, CharCat,  _) -> 
			let (okl, headl, taill) = get_head_and_tail_string se1 in
			let (okr, headr, tailr) = get_head_and_tail_string se2 in
			print_debug (Printf.sprintf "Got head and tail: left: %b, right: %b" 
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
			let msg = Printf.sprintf "Non-arranged lists passed to unify_lists : %s, %s" (print_lexpr se1) (print_lexpr se2) in
			raise (Failure msg)
	)



let rec aggressively_simplify (to_add : (string * jsil_logic_expr) list) other_pfs save_all_lvars exists (symb_state : symbolic_state) =

	let f = aggressively_simplify to_add other_pfs save_all_lvars exists in

	(* Break down the state into components *)
	let heap, store, p_formulae, gamma, preds (*, _ *) = symb_state in

	(* When we know the formulae are false, set the implication to false -> true *)
	let pfs_false msg =
		print_debug_petar (msg ^ " Pure formulae false.\n");
		DynArray.clear p_formulae;
		DynArray.add p_formulae LFalse;
		DynArray.clear other_pfs;
		symb_state, other_pfs, [], exists in
	
	let perform_substitution var lexpr n chantay = 
	let subst = Hashtbl.create 1 in
		Hashtbl.add subst var lexpr;
		DynArray.delete p_formulae n;
		let new_to_add =
		  (match chantay with
		   | false ->
			   while (Hashtbl.mem gamma var) do Hashtbl.remove gamma var done;
			   to_add
		   | true -> ((var, lexpr) :: to_add)) in
		print_debug_petar (Printf.sprintf "Just added %s to subst." var);
		let symb_state = symb_state_substitution symb_state subst true in
		let other_pfs = pf_substitution other_pfs subst true in
		aggressively_simplify new_to_add other_pfs save_all_lvars exists symb_state in

	(* Main recursive function *)
	let rec go_through_pfs (pfs : jsil_logic_assertion list) n =
		(match pfs with
		| [] ->
			List.iter (fun (x, y) -> DynArray.add p_formulae (LEq (LVar x, y))) to_add;
			symb_state, other_pfs, to_add, exists
		| pf :: rest ->
			(match pf with
			(* If we have true in the pfs, we delete it and restart *)
			| LTrue -> DynArray.delete p_formulae n; go_through_pfs rest n
			(* If we have false in the pfs, everything is false and we stop *)
			| LFalse -> pfs_false ""
			(* Getting rid of disequalities that we know hold due to typing *)
			| LNot (LEq (le1, le2)) ->
				let te1, _, _ = type_lexpr gamma le1 in
				let te2, _, _ = type_lexpr gamma le2 in
				(match te1, te2 with
				| Some t1, Some t2 ->
					(match (t1 = t2) with
					| false -> DynArray.delete p_formulae n; go_through_pfs rest n
					| true -> go_through_pfs rest (n + 1))
				| _, _ -> go_through_pfs rest (n + 1))
			| LEq (le1, le2) ->
				(match le1, le2 with
				(* Obvious falsity *)
				| ALoc loc, LLit l
				| LLit l, ALoc loc ->
					(match l with
					 | Loc _ -> go_through_pfs rest (n + 1)
					 | _ -> pfs_false (Printf.sprintf "ALoc and not-a-loc: %s, %s" loc (JSIL_Print.string_of_literal l false)))
				(* VARIABLES *)
				| LVar v1, LVar v2 ->
					let does_this_work = 
						(match (Hashtbl.mem gamma v1, Hashtbl.mem gamma v2) with
						| true, true -> 
							let t1 = Hashtbl.find gamma v1 in
							let t2 = Hashtbl.find gamma v2 in
								(t1 = t2)
						| true, false ->
							let t1 = Hashtbl.find gamma v1 in
								Hashtbl.add gamma v2 t1;
								true
						| false, true ->
							let t2 = Hashtbl.find gamma v2 in
								Hashtbl.add gamma v1 t2;
								true
						| _, _ -> true) in
					if does_this_work 
						then go_through_pfs rest (n + 1)
						else pfs_false "Nasty type mismatch"
				| LVar v, LLit lit -> 
					let does_this_work = 
						let tl = evaluate_type_of lit in
						(match Hashtbl.mem gamma v with
						| true -> 
							let t1 = Hashtbl.find gamma v in
								(t1 = tl)
						| false -> Hashtbl.add gamma v tl; true) in
					if does_this_work 
						then perform_substitution v le2 n (save_all_lvars || String.get v 0 = '#')
						else pfs_false "Nasty type mismatch: var -> lit"
				| LVar v, le2 when 
						(isSubstitutable le2 && 
							not (let le_vars = get_logic_expression_lvars le2 in SS.mem v le_vars)) ->
					perform_substitution v le2 n (save_all_lvars || String.get v 0 = '#')
					
				(* LIST LENGTH *)
				| LLit (Num len), LUnOp (LstLen, LVar v)
				| LUnOp (LstLen, LVar v), LLit (Num len) ->
						(match (Utils.is_int len) with
						| false -> pfs_false "Non-integer list-length. Good luck."
						| true -> 
							let len = int_of_float len in
							(match (0 <= len) with
							| false -> pfs_false "Sub-zero length. Good luck."
							| true -> 
									let subst_list = Array.to_list (Array.init len (fun _ -> fresh_lvar())) in
									let new_exists = SS.union (SS.of_list subst_list) exists in
									let subst_list = List.map (fun x -> LVar x) subst_list in
									DynArray.delete p_formulae n;
									DynArray.add p_formulae (LEq (LVar v, LEList subst_list));
									aggressively_simplify to_add other_pfs save_all_lvars new_exists symb_state
							)
						)
				
				(* LISTS *)
				| le1, le2 when (isList le1 && isList le2) ->
					let ok, subst = unify_lists le1 le2 false in
					(match ok with
					(* Error while unifying lists *)
					| None -> pfs_false "List error"
					(* No error, but no progress *)
					| Some false -> (match subst with
					  | [ (le1', le2') ] -> go_through_pfs rest (n + 1)
						| _ -> raise (Failure "Unexpected list obtained from list unification."))
					(* Progress *)
					| Some true -> 
							DynArray.delete p_formulae n;
							List.iter (fun (x, y) -> DynArray.add p_formulae (LEq (x, y))) subst;
							f symb_state
					)
					 
				(* More falsity *)
				| LEList _, LLit _
				| LLit _, LEList _ 
				| LBinOp (_, LstCons, _), LLit _
				| LLit _ , LBinOp (_, LstCons, _) -> pfs_false "List and not-a-list"
				
				(* Otherwise, continue *)
				| _, _ -> go_through_pfs rest (n + 1))
			
			(* I don't know how these could get here, but let's assume they can... *)
			| LAnd  (a1, a2)
			| LStar	(a1, a2) -> DynArray.set p_formulae n a1; DynArray.add p_formulae a2; f symb_state
			
			(* Otherwise, continue *)
			| _ -> go_through_pfs rest (n + 1)
			)
		) in

	(* *******************
	 *  ACTUAL PROCESSING
	 * ******************* *) 

	(* Bring lvars to the left side of the equality or not-equality *)
	DynArray.iteri
	(fun i pf ->
	  (match pf with
	   (* Move lvars with # to the left *)
	   | LEq (LVar v1, LVar v2) when (String.get v1 0 = '_' && String.get v2 0 = '#') -> DynArray.set p_formulae i (LEq (LVar v2, LVar v1))
	   (* Don't do anything if the left lvar is with _ or with # *)
	   | LEq (LVar v1, _)       when (String.get v1 0 = '_' || String.get v1 0 = '#') -> ()
	   (* Otherwise, swap *)
	   | LEq (le1, LVar var) -> DynArray.set p_formulae i (LEq (LVar var, le1))
	   (* Move lvars with # to the left *)
	   | LNot (LEq (LVar v1, LVar v2)) when (String.get v1 0 = '_' && String.get v2 0 = '#') -> DynArray.set p_formulae i (LNot (LEq (LVar v2, LVar v1)))
	   (* Don't do anything if the left lvar is with _ or with # *)
	   | LNot (LEq (LVar v1, _))       when (String.get v1 0 = '_' || String.get v1 0 = '#') -> ()
	   (* Otherwise, swap *)
	   | LNot (LEq (le1, LVar var)) -> DynArray.set p_formulae i (LNot (LEq (LVar var, le1)))
	   | _ -> ()
	  )
	) p_formulae;

	(* Sanitise *)
	sanitise_pfs store gamma p_formulae;

	(* Process *)
	let pf_list = DynArray.to_list p_formulae in
		go_through_pfs pf_list 0
		

let simplify how x =
	let (result : symbolic_state), _, _, _ = aggressively_simplify [] (DynArray.create ()) how (SS.empty) x in result

let simplify_with_subst how x = 
	let result, _, subst, _ = aggressively_simplify [] (DynArray.create ()) how (SS.empty) x in result, subst

let aggressively_simplify_pfs pfs gamma how =
	(* let solver = ref None in *)
		let _, _, pfs, _, _ = simplify how (LHeap.create 1, Hashtbl.create 1, (DynArray.copy pfs), (copy_gamma gamma), DynArray.create () (*, solver*)) in
			pfs
				
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
	| TypeType      -> 9)

let type_length = 10

let simplify_symb_state 
	(vars_to_save : (SS.t option) option)
	(other_pfs    : jsil_logic_assertion DynArray.t)
	(existentials : SS.t)
	(symb_state   : symbolic_state) =

	let start_time = Sys.time () in
	print_time_debug "simplify_symb_state:";
	
	let initial_existentials = ref existentials in

	let vars_to_save, save_all = 
		(match vars_to_save with
		| Some (Some v) -> v, false 
		| Some None     -> SS.empty, true
		| None          -> SS.empty, false) in

	print_debug_petar (Printf.sprintf "Vars_to_save: %s" (String.concat ", " (SS.elements vars_to_save)));
	print_debug_petar (Printf.sprintf "Save_all: %b" save_all);
	print_debug_petar (Printf.sprintf "Existentials: %s" (String.concat ", " (SS.elements existentials)));
	

	(* Pure formulae false *)
	let pfs_false subst others exists symb_state msg =
		let _, _, pfs, _, _ = symb_state in
		print_debug_petar (msg ^ " Pure formulae false.");
		DynArray.clear pfs;
		DynArray.add pfs LFalse;
		symb_state, subst, others, exists in

	(* Are there any singleton types in gamma? *)
	let simplify_singleton_types others exists symb_state subst types =		 
		let gamma = get_gamma symb_state in
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
			let symb_state = symb_state_substitution symb_state subst true in
			let others = pf_substitution others subst true in
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
	print_debug (Printf.sprintf "SS: %s" (Symbolic_State_Print.string_of_shallow_symb_state symb_state));
	let lvars = SS.union (get_symb_state_vars_no_gamma false symb_state) (get_pf_vars false other_pfs) in
	let lvars_gamma = get_gamma_all_vars gamma in		
	let lvars_inter = SS.inter lvars lvars_gamma in
	Hashtbl.filter_map_inplace (fun v t ->
		(match (save_all || SS.mem v (SS.union lvars_inter (SS.union vars_to_save !initial_existentials))) with
		| true  -> Some t
		| false -> print_debug (Printf.sprintf "Cutting %s : %s from gamma" v (JSIL_Print.string_of_type t)); None)) gamma;
		
	(* Setup the type indexes *)
	let types = Array.make type_length 0 in
	Hashtbl.iter (fun _ t -> 
		let it = type_index t in
			types.(it) <- types.(it) + 1) gamma;
		
	(* Instantiate uniquely determined variables *)
	let subst = Hashtbl.create 57 in
	let symb_state, subst, others, exists = simplify_singleton_types other_pfs !initial_existentials symb_state subst types in

	let pfs = get_pf symb_state in

	(* String translation: Use internal representation as Chars *)
	let pfs = DynArray.map (assertion_map le_string_to_list) pfs in
	print_debug (Printf.sprintf "Pfs before simplification (with internal rep):%s" (print_pfs pfs));
	let symb_state = symb_state_replace_pfs symb_state pfs in 

	(* print_debug (Printf.sprintf "Entering main loop:\n%s %s" 
		(Symbolic_State_Print.string_of_shallow_symb_state symb_state) (Symbolic_State_Print.string_of_substitution subst)); *)
	
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
							let sv = SS.mem v vars_to_save in
							let sw = SS.mem w vars_to_save in
							(match sv, sw with
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
					
					let lvars_le = get_logic_expression_lvars le in
					(match (SS.mem v lvars_le) with
					| true -> n := !n + 1
					| false -> 		
						(* Changes made, stay on n *)
						changes_made := true;
						DynArray.delete pfs !n;
						
						(* Substitute *)
						let temp_subst = Hashtbl.create 1 in
						Hashtbl.add temp_subst v le;
						
						let simpl_fun = (match (not (SS.mem v !initial_existentials) && (save_all || SS.mem v vars_to_save)) with
							| false -> symb_state_substitution_in_place_no_gamma
							| true -> selective_symb_state_substitution_in_place_no_gamma
							) in
						
						simpl_fun !symb_state temp_subst;
						pf_substitution_in_place !others temp_subst;
						
						(*
						symb_state_substitution_in_place_no_gamma !symb_state temp_subst;
						pf_substitution_in_place !others temp_subst; *)
						
						(* Add to subst *)
						if (Hashtbl.mem subst v) then 
							raise (Failure (Printf.sprintf "Impossible variable in subst: %s\n%s"
								v (Symbolic_State_Print.string_of_substitution subst)));
						Hashtbl.iter (fun v' le' ->
							let sb = Hashtbl.create 1 in
								Hashtbl.add sb v le;
								let sa = lexpr_substitution le' sb true in
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
								
							
						(* Remove from gamma *)
						(match (save_all || SS.mem v (SS.union vars_to_save !exists)) with
	      		| true -> ()
	      		| false -> 
	    					while (Hashtbl.mem gamma v) do 
	    						let t = Hashtbl.find gamma v in
	    						let it = type_index t in
	    						types.(it) <- types.(it) - 1;
									print_debug_petar (Printf.sprintf "Removing from gamma: %s" v);
	    						Hashtbl.remove gamma v 
	    					done);
						
						(* Remove from existentials *)
						exists := SS.remove v !exists)
					
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
				
				(* List unification *)
				| le1, le2 when (isList le1 && isList le2) ->
					(* print_debug (Printf.sprintf "List unification: %s vs. %s" (print_lexpr le1) (print_lexpr le2)); *)
					let ok, subst = unify_lists le1 le2 false in
					(match ok with
					(* Error while unifying lists *)
					| None -> pfs_ok := false; msg := "List error"	
					(* No error, but no progress *)
					| Some false -> (match subst with
						| [ ] 
						| [ _ ] -> n := !n + 1 
						| _ -> 
							print_debug_petar (Printf.sprintf "No changes made, but length = %d" (List.length subst));
							print_debug_petar (String.concat "\n" (List.map (fun (x, y) ->
								Printf.sprintf "%s = %s" (print_lexpr x) (print_lexpr y)) subst)); 
							raise (Failure "Unexpected list obtained from list unification."))
					(* Progress *)
					| Some true -> 
							(* Changes made, stay on n *)
							changes_made := true;
							DynArray.delete pfs !n;
							List.iter (fun (x, y) -> DynArray.add pfs (LEq (x, y))) subst)

				(* String unification *)
				| se1, se2 when (isInternalString se1 && isInternalString se2) ->
					print_debug (Printf.sprintf "String unification: %s vs. %s" (print_lexpr se1) (print_lexpr se2));
					let ok, subst = unify_strings se1 se2 false in
					(match ok with
					(* Error while unifying strings *)
					| None -> pfs_ok := false; msg := "String error"
					(* No error, but no progress *)
					| Some false -> (match subst with
						| [ ] 
						| [ _ ] -> n := !n + 1 
						| _ -> 
							print_debug_petar (Printf.sprintf "No changes made, but length = %d" (List.length subst));
							print_debug_petar (String.concat "\n" (List.map (fun (x, y) ->
								Printf.sprintf "%s = %s" (print_lexpr x) (print_lexpr y)) subst)); 
							raise (Failure "Unexpected list obtained from string unification."))
					(* Progress *)
					| Some true -> 
							(* Changes made, stay on n *)
							changes_made := true;
							DynArray.delete pfs !n;
							List.iter (fun (x, y) -> DynArray.add pfs (LEq (x, y))) subst)
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
	
	(* Convert substitutions back to string format *)
	Hashtbl.filter_map_inplace (fun var lexpr -> Some (logic_expression_map le_list_to_string lexpr)) subst;

	(* Bring back from the subst *)
	print_debug_petar (Printf.sprintf "The subst is:\n%s" (Symbolic_State_Print.string_of_substitution subst));

	Hashtbl.iter (fun var lexpr -> 
		(match (not (SS.mem var !initial_existentials) && (save_all || SS.mem var vars_to_save)) with
		| false -> ()
		| true -> DynArray.add pfs (LEq (LVar var, lexpr)))
		) subst;
	
	(* String translation: Move back from internal representation to Strings *)
	let pfs = DynArray.map (assertion_map le_list_to_string) (get_pf !symb_state) in
	print_debug (Printf.sprintf "Pfs after (no internal Strings should be present):%s" (print_pfs pfs));
	let symb_state = ref (symb_state_replace_pfs !symb_state pfs) in

	let end_time = Sys.time() in
	JSIL_Syntax.update_statistics "simplify_symb_state" (end_time -. start_time);
	
	print_debug_petar (Printf.sprintf "Exiting with pfs_ok: %b" !pfs_ok);
	if (!pfs_ok) 
		then (!symb_state, subst, !others, !exists)
		else (pfs_false subst !others !exists !symb_state !msg)
	

let simplify_ss symb_state vars_to_save = 
	let symb_state, _, _, _ = simplify_symb_state vars_to_save (DynArray.create()) (SS.empty) symb_state in
	symb_state
	
let simplify_ss_with_subst symb_state vars_to_save = 
	let symb_state, subst, _, _ = simplify_symb_state vars_to_save (DynArray.create()) (SS.empty) symb_state in
	symb_state, subst
	
let simplify_pfs pfs gamma vars_to_save =
	let fake_symb_state = (LHeap.create 1, Hashtbl.create 1, (DynArray.copy pfs), (copy_gamma gamma), DynArray.create ()) in
	let (_, _, pfs, gamma, _), _, _, _ = simplify_symb_state vars_to_save (DynArray.create()) (SS.empty) fake_symb_state in
	pfs, gamma

let simplify_pfs_with_subst pfs gamma =
	let fake_symb_state = (LHeap.create 1, Hashtbl.create 1, (DynArray.copy pfs), (copy_gamma gamma), DynArray.create ()) in
	let (_, _, pfs, gamma, _), subst, _, _ = simplify_symb_state None (DynArray.create()) (SS.empty) fake_symb_state in
	if (DynArray.to_list pfs = [ LFalse ]) then (pfs, None) else (pfs, Some subst)

let simplify_pfs_with_exists exists lpfs gamma vars_to_save = 
	let fake_symb_state = (LHeap.create 1, Hashtbl.create 1, (DynArray.copy lpfs), (copy_gamma gamma), DynArray.create ()) in
	let (_, _, lpfs, gamma, _), _, _, exists = simplify_symb_state vars_to_save (DynArray.create()) exists fake_symb_state in
	lpfs, exists, gamma

let simplify_pfs_with_exists_and_others exists lpfs rpfs gamma = 
	let fake_symb_state = (LHeap.create 1, Hashtbl.create 1, (DynArray.copy lpfs), (copy_gamma gamma), DynArray.create ()) in
	let (_, _, lpfs, gamma, _), _, rpfs, exists = simplify_symb_state None rpfs exists fake_symb_state in
	lpfs, rpfs, exists, gamma

(* ************************** *
 * IMPLICATION SIMPLIFICATION *
 * ************************** *)
	
let rec simplify_existentials (exists : SS.t) lpfs (p_formulae : jsil_logic_assertion DynArray.t) (gamma : (string, jsil_type) Hashtbl.t) =

	(* print_time_debug ("simplify_existentials:"); *)
	
	let rhs_gamma = copy_gamma gamma in
	filter_gamma_pfs p_formulae rhs_gamma;
	
	let p_formulae, exists, _ = simplify_pfs_with_exists exists p_formulae rhs_gamma (Some None) in
	
	(* print_debug (Printf.sprintf "PFS: %s" (Symbolic_State_Print.string_of_shallow_p_formulae p_formulae false)); *)

	let pfs_false msg =
		print_debug (msg ^ " Pure formulae false.\n");
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
		simplify_existentials exists lpfs (pf_substitution p_formulae subst true) gamma in

	let test_for_nonsense pfs =

		let rec test_for_nonsense_var_list var lst =
			print_debug (Printf.sprintf "Nonsense test: %s vs. %s" (print_lexpr var) (print_lexpr lst));
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
				| true -> 
					print_debug_petar (Printf.sprintf "Finished existential simplification:\n\nExistentials:\n%s\n\nPure formulae:\n%s\n\nGamma:\n%s\n\n"
			 		(String.concat ", " (SS.elements exists))
			 		(print_pfs p_formulae)
			 		(Symbolic_State_Print.string_of_gamma gamma)); 
		 		 	exists, lpfs, p_formulae, gamma))
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
		go_through_pfs pf_list 0 



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
	done
	
let simplify_implication exists lpfs rpfs gamma =
	let lpfs, rpfs, exists, gamma = simplify_pfs_with_exists_and_others exists lpfs rpfs gamma in
	(* print_debug (Printf.sprintf "In between:\nExistentials:\n%s\nLeft:\n%s\nRight:\n%s\nGamma:\n%s\n" 
	(String.concat ", " (SS.elements exists))
	(Symbolic_State_Print.string_of_shallow_p_formulae lpfs false)
	(Symbolic_State_Print.string_of_shallow_p_formulae rpfs false)
	(Symbolic_State_Print.string_of_gamma gamma)); *)
	sanitise_pfs_no_store gamma rpfs;
	let exists, lpfs, rpfs, gamma = simplify_existentials exists lpfs rpfs gamma in
	clean_up_stuff exists lpfs rpfs;
	exists, lpfs, rpfs, gamma (* DO THE SUBST *)



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
let resolve_location lvar pfs =
	let rec loop pfs =
		match pfs with
		| [] -> None
		| LEq (LVar cur_lvar, ALoc loc) :: rest
		| LEq (ALoc loc, LVar cur_lvar) :: rest  ->
			if (cur_lvar = lvar) then Some (ALoc loc) else loop rest
		| LEq (LVar cur_lvar, LLit (Loc loc)) :: rest
		| LEq (LLit (Loc loc), LVar cur_lvar) :: rest ->
			if (cur_lvar = lvar) then Some (LLit (Loc loc)) else loop rest
		| _ :: rest -> loop rest in
	loop pfs



(*

(* Shorthand for printing logical expressions *)
let print_lexpr le = JSIL_Print.string_of_logic_expression le false 

(* ********* *
 *           *
 * REDUCTION *
 *           *
 * ********* *)

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
			LBinOp (re1, bop, re2)

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
	if (not (e = result)) then print_debug (Printf.sprintf "Reduce expression: %s ---> %s"
		(JSIL_Print.string_of_logic_expression e false)
		(JSIL_Print.string_of_logic_expression result false));
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
			
			| _, _ -> default e1 e2 re1 re2
		)

	| LLess (e1, e2) ->
		let re1 = fe e1 in
		let re2 = fe e2 in
		LLess (re1, re2)

	| _ -> a) in
	result

let reduce_assertion_no_store_no_gamma_no_pfs = reduce_assertion (Hashtbl.create 1) (Hashtbl.create 1) (DynArray.create ())
let reduce_assertion_no_store_no_gamma        = reduce_assertion (Hashtbl.create 1) (Hashtbl.create 1)
let reduce_assertion_no_store                 = reduce_assertion (Hashtbl.create 1)

(* ***** *
 *       *
 * LISTS *
 *       *
 * ***** *)

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

*)