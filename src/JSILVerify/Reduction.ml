open CCommon
open SCommon
open JSIL_Syntax
open JSIL_Logic_Utils

(* When reduction fails *)
exception ReductionException of jsil_logic_expr * string

(***************************)
(* TYPING HELPER FUNCTIONS *)
(***************************)

let typable ?(gamma : TypEnv.t option) (le : jsil_logic_expr) (target_type : Type.t) : bool = 
	let gamma = Option.default (TypEnv.init ()) gamma in
	let t, success, _ = type_lexpr gamma le in
		if success then 
			Option.map_default
			(fun t -> t = target_type) 
			(match le with | LVar _ | PVar _ -> true | _ -> false)
			t
		else
			raise (Failure (Printf.sprintf "typable: type error: %s not typable in typing environment %s" (JSIL_Print.string_of_logic_expression le) (TypEnv.str gamma)))

(* Lists *)
let lexpr_is_list ?(gamma : TypEnv.t option) (le : jsil_logic_expr) : bool =
	typable ?gamma:gamma le ListType

(* Strings *)
let lexpr_is_string ?(gamma : TypEnv.t option) (le : jsil_logic_expr) : bool =
	typable ?gamma:gamma le StringType

(* Numbers *)
let lexpr_is_number ?(gamma : TypEnv.t option) (le : jsil_logic_expr) : bool =
	typable ?gamma:gamma le NumberType

(* Booleans *)
let lexpr_is_bool ?(gamma : TypEnv.t option) (le : jsil_logic_expr) : bool =
	typable ?gamma:gamma le BooleanType

(* Sets *)
let lexpr_is_set ?(gamma : TypEnv.t option) (le : jsil_logic_expr) : bool =
	typable ?gamma:gamma le SetType

(**********************************)
(* Pure formulae helper functions *)
(**********************************)

let find_first_equality_in_pfs (pfs : PFS.t) le =
	let lpfs = PFS.to_list pfs in
	let lpfs = List.find_opt (fun x -> match x with | LEq (x, y) -> (x = le) || (y = le) | _ -> false) lpfs in
	let result = Option.map (fun x -> match x with | LEq (x, y) -> if x = le then y else x) lpfs in
		print_debug_petar (Printf.sprintf "Found equality: %s = %s" (JSIL_Print.string_of_logic_expression le) (Option.map_default (fun x -> JSIL_Print.string_of_logic_expression x) "None" result));
		result

(***********************************)
(* LIST REASONING HELPER FUNCTIONS *)
(***********************************)

(* Finding the length of a list *)
let rec get_length_of_list (lst : jsil_logic_expr) : int option =
	let f = get_length_of_list in

	(match lst with
	| PVar _ -> None
	| LVar _ -> None
	| LLit (LList l) -> Some (List.length l)
	| LEList l -> Some (List.length l)
	| LBinOp (_, LstCons, le) -> Option.map (fun len -> 1 + len) (f le)
	| LBinOp (lel, LstCat, ler) -> Option.default None (Option.map (fun ll -> Option.map (fun lr -> ll + lr) (f ler)) (f lel)) 
	| _ -> raise (Failure (Printf.sprintf "get_length_of_list: list equals %s, impossible" (JSIL_Print.string_of_logic_expression lst)))
	)

(* Finding the nth element of a list *)
let rec get_nth_of_list (lst : jsil_logic_expr) (idx : int) : jsil_logic_expr option =
	let f = get_nth_of_list in

	let err_msg = "get_nth_of_list: index out of bounds." in

	(* If we can compute the length of the list, then the index needs to be compatible *)
	let olen = get_length_of_list lst in
	let _ = match olen with
		| None -> ()
		| Some len -> if (len <= idx) then raise (ReductionException (LNone, err_msg))
	in

	(match lst with
	(* Nothing can be done for variables *)
	| PVar _ -> None
	| LVar _ -> None
	(* Base lists of literals and logical expressions *)
	| LLit (LList l) -> it_must_hold_that (lazy (idx < List.length l)); Some (LLit (List.nth l idx))
	| LEList l       -> it_must_hold_that (lazy (idx < List.length l)); Some (List.nth l idx)
	| LBinOp (hd, LstCons, lst) -> 
		if (idx = 0) 
			then Some hd
			else f lst (idx - 1)
	| LBinOp (lel, LstCat, ler) ->
		Option.default None 
			(Option.map 
				(fun llen -> 
					let lst, idx = if (idx < llen) then lel, idx else ler, (idx - llen) in
						f lst idx)
				(get_length_of_list lel)
			)

	| _ -> raise (Failure (Printf.sprintf "get_nth_of_list: list equals %s, impossible" (JSIL_Print.string_of_logic_expression lst)))
	) 

(* Finding the nth element of a list *)
let rec get_head_and_tail_of_list ?(pfs : PFS.t option) (lst : jsil_logic_expr) : (jsil_logic_expr * jsil_logic_expr) option =
	let f = get_head_and_tail_of_list in

	(match lst with
	(* Nothing can be done for variables *)
	| PVar _ -> None
	| LVar _ -> Option.map_default (fun x -> Option.map_default (fun y -> get_head_and_tail_of_list ?pfs:(Some x) y) None (find_first_equality_in_pfs x lst)) None pfs
	(* Base lists of literals and logical expressions *)
	| LLit (LList l) -> it_must_hold_that (lazy (0 < List.length l)); Some (LLit (List.hd l), LLit (LList (List.tl l)))
	| LEList l       -> it_must_hold_that (lazy (0 < List.length l)); Some (List.nth l 0, LEList (List.tl l))
	| LBinOp (hd, LstCons, lst) -> Some (hd, lst)
	| LBinOp (lel, LstCat, ler) -> 
		Option.default None 
			(Option.map 
				(fun (hd, tl) -> 
					Some (hd, LBinOp (tl, LstCat, ler)))
				(f lel)
			)

	| _ -> raise (Failure (Printf.sprintf "get_head_and_tail_of_list: list equals %s, impossible" (JSIL_Print.string_of_logic_expression lst)))
	)

(*************************************)
(* STRING REASONING HELPER FUNCTIONS *)
(*************************************)

(* Finding the length of a string *)
let rec get_length_of_string (str : jsil_logic_expr) : int option =
	let f = get_length_of_string in

	(match str with
	| PVar _ -> None
	| LVar _ -> None
	| LLit (String s) -> Some (String.length s)
	| LBinOp (sl, StrCat, sr) -> Option.default None (Option.map (fun ll -> Option.map (fun lr -> ll + lr) (f sr)) (f sl)) 
	| _ -> raise (Failure (Printf.sprintf "get_length_of_string: string equals %s, impossible" (JSIL_Print.string_of_logic_expression str)))
	)

(* Finding the nth element of a list *)
let rec get_nth_of_string (str : jsil_logic_expr) (idx : int) : jsil_logic_expr option =
	let f = get_nth_of_string in

	let err_msg = "get_nth_of_string: index out of bounds." in

	(* If we can compute the length of the list, then the index needs to be compatible *)
	let olen = get_length_of_string str in
	let _ = match olen with
		| None -> ()
		| Some len -> if (len <= idx) then raise (ReductionException (LNone, err_msg))
	in

	let result : jsil_logic_expr option = (match str with
	(* Nothing can be done for variables *)
	| PVar _ -> None
	| LVar _ -> None
	(* Base lists of literals and logical expressions *)
	| LLit (String s) -> it_must_hold_that (lazy (idx < String.length s)); Some (LLit (String (String.sub s idx 1)))
	| LBinOp (ls, LstCat, rs) ->
		Option.default None 
			(Option.map 
				(fun llen -> 
					let lst, idx = if (idx < llen) then ls, idx else rs, (idx - llen) in
						f lst idx)
				(get_length_of_string ls)
			)

	| _ -> raise (Failure (Printf.sprintf "get_nth_of_string: string equals %s, impossible" (JSIL_Print.string_of_logic_expression str)))
	) in result

(**********************************)
(* SET REASONING HELPER FUNCTIONS *)
(**********************************)

let is_different pfs li lj : bool option = 
	(match li = lj with
	| true -> Some false
	| false -> (match li, lj with
		| LLit x, LLit y when x <> y -> Some true
		| _, _ -> if (List.mem (LNot (LEq (li, lj))) pfs || List.mem (LNot (LEq (lj, li))) pfs)
			then Some true else None
		)
	)

let rec set_member pfs m s = 
	let f = set_member pfs m in 
	(match s with
	| LVar x -> m = s
	| LESet s -> List.mem m s
	| LSetUnion les -> List.exists  (fun x -> f x) les
	| LSetInter les -> List.for_all (fun x -> f x) les
	| _ -> List.mem (LSetMem (m, s)) pfs
	)

let rec not_set_member pfs m s = 
	let f = not_set_member pfs m in 
	(match s with
	| LSetUnion les -> List.for_all (fun x -> f x) les
	| LSetInter les -> List.exists  (fun x -> f x) les
	| LESet les -> List.for_all (fun le -> is_different pfs m le = Some true) les
	| _ -> List.mem (LNot (LSetMem (m, s))) pfs
	)

let rec set_subset pfs s s' = 
	let f = set_subset pfs s in 
	(match s' with
	| LVar _ -> s = s'
	| LSetUnion les -> List.exists  (fun x -> f x) les
	| LSetInter les -> List.for_all (fun x -> f x) les
	| _ -> 
		(match s with 
		| LESet les -> List.for_all (fun x -> set_member pfs x s') les
		| _ -> false
		)
	)

let all_different pfs les = 
	let result = ref true in
	let len = List.length les in
	let les = Array.of_list les in
	let i = ref 0 in
	while !result && (!i < len - 1) do 
		let j = ref (!i + 1) in
		while !result && (!j < len) do
			let li, lj = Array.get les !i, Array.get les !j in
				print_debug (Printf.sprintf "Checking: %s vs. %s" (JSIL_Print.string_of_logic_expression li) (JSIL_Print.string_of_logic_expression lj));
				if (is_different pfs li lj <> Some true) then result := false;
				j := !j + 1
		done;
		i := !i + 1
	done;
	!result

(*************)
(* REDUCTION *)
(*************)

(** Reduction of logical expressions *)
let rec reduce_lexpr ?(no_timing: unit option) ?(gamma: TypEnv.t option) ?(pfs : PFS.t option) (le : jsil_logic_expr) = 

	let start_time = Sys.time () in

	let f = reduce_lexpr ?no_timing:(Some ()) ?gamma:gamma ?pfs:pfs in
	let result = (match le with

	(* Base lists *)
	| LEList les -> 
		let fles = List.map f les in
		let all_literals = List.for_all (fun x -> (match x with | LLit _ -> true | _ -> false)) fles in
		(match all_literals with
		| false -> LEList fles
		| true  -> 
			let lits = List.map (fun x -> (match x with | LLit x -> x)) fles in
				LLit (LList lits)
		)

	(* Base sets *)
	| LESet les -> LESet (List.map f les)

	(* List indexing *)
	| LLstNth (le, idx) ->
		let fle = f le  in
		let fidx = f idx in
		(match fidx with
		(* Index is a non-negative integer *)
		| LLit (Num n) when (Utils.is_int n && 0. <= n) ->
				(match (lexpr_is_list fle) with
				| true -> 
					Option.default (LLstNth (fle, fidx)) (get_nth_of_list fle (int_of_float n))
				| false -> 
					let err_msg = "LstNth(list, index): list is not a JSIL list." in
					raise (ReductionException (LLstNth (fle, fidx), err_msg))
				)

		(* Index is a number, but is either not an integer or is negative *)
		| LLit (Num n) -> 
			let err_msg = "LstNth(list, index): index is non-integer or smaller than zero." in
			raise (ReductionException (LLstNth (fle, fidx), err_msg))

		(* All other cases *)
		| _ -> LLstNth (fle, fidx)
		)

	(* String indexing *)
	| LStrNth (le, idx) ->
		let fle = f le  in
		let fidx = f idx in
		(match fidx with
		(* Index is a non-negative integer *)
		| LLit (Num n) when (Utils.is_int n && 0. <= n) ->
			(match (lexpr_is_string ?gamma:gamma fle) with
			| true -> Option.default (LStrNth (fle, fidx)) (get_nth_of_string fle (int_of_float n))
			| false -> 
				let err_msg = "StrNth(str, index): string is not a JSIL string." in
				raise (ReductionException (LStrNth (fle, fidx), err_msg))
			)

		(* Index is a number, but is either not an integer or is negative *)
		| LLit (Num n) -> 
			let err_msg = "StrNth(str, index): index is non-integer or smaller than zero." in
			raise (ReductionException (LStrNth (fle, fidx), err_msg))

		(* All other cases *)
		| _ -> LStrNth (fle, fidx)
		)

	| LSetUnion les ->
		let fles = List.map f les in
		(* Flatten unions *)
		let unions, rest = List.partition (fun x -> match x with | LSetUnion _ -> true | _ -> false) fles in
		let unions = List.fold_left
			(fun ac u -> 
				let ls = (match u with
				| LSetUnion ls -> ls
				| _ -> raise (Failure "LSetUnion: flattening unions: impossible.")) in
				ac @ ls
			) 
			[]
			unions in
		let fles = unions @ rest in 
		(* Join LESets *)
		let lesets, rest = List.partition (fun x -> match x with | LESet _ -> true | _ -> false) fles in
		let lesets = List.fold_left
			(fun ac u -> 
				let ls = (match u with
				| LESet ls -> ls
				| _ -> raise (Failure "LSetUnion: joining LESets: impossible.")) in
				ac @ ls
			) 
			[]
			lesets in
		let lesets = SLExpr.elements (SLExpr.of_list lesets) in
		let fles = LESet lesets :: rest in 
		(* Remove empty sets *)
		let fles = List.filter (fun s -> s <> LESet []) fles in
		(* Remove duplicates *)
		let fles = SLExpr.elements (SLExpr.of_list fles) in
			(match fles with
			| [ ] -> LESet [ ] 
			| [ x ] -> x
			| _ -> LSetUnion fles)

	| LSetInter les ->
		let fles = List.map f les in
		(* Flatten intersections *)
		let inters, rest = List.partition (fun x -> match x with | LSetInter _ -> true | _ -> false) fles in
		let inters = List.fold_left
			(fun ac u -> 
				let ls = (match u with
				| LSetInter ls -> ls
				| _ -> raise (Failure "LSetInter: flattening intersections: impossible.")) in
				ac @ ls
			) 
			[]
			inters in
		let fles = inters @ rest in 
		(* Join LESets *)
		let lesets, rest = List.partition (fun x -> match x with | LESet _ -> true | _ -> false) fles in
		let lesets = List.fold_left
			(fun ac u -> 
				let ls = (match u with
				| LESet ls -> ls
				| _ -> raise (Failure "LSetUnion: joining LESets: impossible.")) in
				ac @ ls
			) 
			[]
			lesets in
		let lesets = SLExpr.elements (SLExpr.of_list lesets) in
		let fles = LESet lesets :: rest in 
		(* If there is an empty set, the intersection is empty *)
		if (List.mem (LESet []) fles) 
			then LESet []
			else 
			let fles = SLExpr.elements (SLExpr.of_list fles) in
				(match fles with
				| [ ] -> LESet [ ] 
				| [ x ] -> x
				| _ -> LSetInter fles)

	| LUnOp (op, le) ->
		let fle = f le in
		let def = LUnOp (op, fle) in
		(match fle with
		| LLit lit -> LLit (JSIL_Interpreter.evaluate_unop op lit)
		| _ -> 
			(match op with
			(* The TypeOf operator *)
			| TypeOf ->
				let gamma = Option.default (TypEnv.init ()) gamma in
				let tfle, how, _ = type_lexpr gamma fle in
				(match how with
				| false -> 
					let err_msg = "LTypeOf(le): expression is not typable." in
					raise (ReductionException (def, err_msg))
				| true -> 
					(match tfle with
					| None -> def
					| Some t -> LLit (Type t)
					)
				)
			(* List head *)
			| Car ->
				(match (lexpr_is_list fle) with
				| true -> let ohdtl = get_head_and_tail_of_list ?pfs:pfs fle in
					Option.map_default (fun (hd, _) -> hd) def ohdtl
				| false -> 
					let err_msg = "LUnOp(Car, list): list is not a JSIL list." in
					raise (ReductionException (def, err_msg))
				)

			(* List tail *)
			| Cdr ->
				(match (lexpr_is_list fle) with
				| true -> let ohdtl = get_head_and_tail_of_list ?pfs:pfs fle in
					Option.map_default (fun (_, tl) -> tl) def ohdtl
				| false -> 
					let err_msg = "LUnOp(Cdr, list): list is not a JSIL list." in
					raise (ReductionException (def, err_msg))
				)

			(* List length *)
			| LstLen ->
				(match (lexpr_is_list fle) with
				| true -> let len = get_length_of_list fle in
					Option.map_default (fun len -> LLit (Num (float_of_int len))) def len
				| false -> 
					let err_msg = "LUnOp(LstLen, list): list is not a JSIL list." in
					raise (ReductionException (def, err_msg))
				)

			(* String length *)
			| StrLen ->
				(match (lexpr_is_string fle) with
				| true -> let len = get_length_of_string fle in
					Option.map_default (fun len -> LLit (Num (float_of_int len))) def len
				| false -> 
					let err_msg = "LUnOp(StrLen, list): string is not a JSIL string." in
					raise (ReductionException (def, err_msg))
				)

			| _ -> LUnOp (op, fle)
			)
		)

	(* CHECK: Times and Div are the same, how does the 'when' scope? *)
	| LBinOp (lel, op, ler) ->
		let flel = f lel in
		let fler = f ler in
		let def = LBinOp (flel, op, fler) in
		(match flel, fler with
		| LLit ll , LLit lr -> 
			let empty_store = Hashtbl.create 31 in
			LLit (JSIL_Interpreter.evaluate_binop empty_store op (Literal ll) (Literal lr))
		| _ -> 
			(match op with
			| Equal -> 
				let gamma = Option.default (TypEnv.init()) gamma in
				let t1, _, _ = JSIL_Logic_Utils.type_lexpr gamma flel in
				let t2, _, _ = JSIL_Logic_Utils.type_lexpr gamma fler in
					(match t1, t2 with
					| Some t1, Some t2 -> if (t1 = t2) then def else (LLit (Bool false))
					| _, _             -> def)

			| Plus when (lexpr_is_number ?gamma:gamma def) ->
				(match flel, fler with
				(* 0 is the neutral *)
				| LLit (Num 0.), x
				| x, LLit (Num 0.) -> x
				| LLit (Num x), _ when (x == nan) -> LLit (Num nan)
				| _, LLit (Num x) when (x == nan) -> LLit (Num nan)
				(* This can be more general *)
				| LBinOp (LLit (Num x), Plus, y), LLit (Num z) -> LBinOp (LLit (Num (x +. z)), Plus, y)
				| LLit (Num z), LBinOp (LLit (Num x), Plus, y) -> LBinOp (LLit (Num (z +. x)), Plus, y)
				(* Associate to the right *)
				| LBinOp (flell, Plus, flelr), fler -> LBinOp (flell, Plus, LBinOp (flelr, Plus, fler))
				(* Rest *)
				| _, _ -> print_debug "P6"; def
				)
			| Minus when (lexpr_is_number ?gamma:gamma def) ->
				(match flel, fler with
				(* 0 is the neutral *)
				| LLit (Num 0.), x -> LUnOp (UnaryMinus, x)
				| x, LLit (Num 0.) -> x
				| LLit (Num x), _ when (x == nan) -> LLit (Num nan)
				| _, LLit (Num x) when (x == nan) -> LLit (Num nan)
				(* Transform to unary minus *)
				| _, _ -> LBinOp (flel, Plus, (LUnOp (UnaryMinus, fler)))
				)
			| Times when (lexpr_is_number ?gamma:gamma def) ->
				(match flel, fler with
				(* 1 is the neutral *)
				| LLit (Num 1.), x 
				| x, LLit (Num 1.) -> x
				| LLit (Num x), _ when (x == nan) -> LLit (Num nan)
				| _, LLit (Num x) when (x == nan) -> LLit (Num nan)
				| LBinOp (LLit (Num x), Times, y), LLit (Num z) -> LBinOp (LLit (Num (x *. z)), Times, y)
				| LLit (Num z), LBinOp (LLit (Num x), Times, y) -> LBinOp (LLit (Num (z *. x)), Times, y)
				(* Rest *)
				| _, _ -> def
				)
			| Div when (lexpr_is_number ?gamma:gamma def) ->
				(match flel, fler with
				(* 1 is the neutral *)
				| LLit (Num 1.), x 
				| x, LLit (Num 1.) -> x
				(* Rest *)
				| _, _ -> def
				)
			| And when (lexpr_is_bool ?gamma:gamma def) ->
				(match flel, fler with
				(* 1 is the neutral *)
				| LLit (Bool true), x 
				| x, LLit (Bool true) -> x
				| LLit (Bool false), _ 
				| _, LLit (Bool false) -> LLit (Bool false)
				(* Rest *)
				| _, _ -> def
				)
			| Or when (lexpr_is_bool ?gamma:gamma def) ->
				(match flel, fler with
				(* 1 is the neutral *)
				| LLit (Bool true), _
				| _, LLit (Bool true) -> LLit (Bool true)
				| LLit (Bool false), x
				| x, LLit (Bool false) -> x
				(* Rest *)
				| _, _ -> def
				)
			| LstCons when (lexpr_is_list ?gamma:gamma def) ->
				(match fler with
				| LLit (LList y) -> LEList (flel :: (List.map (fun x -> LLit x) y))
				| LEList y -> LEList (flel :: y)
				| LBinOp (LEList ll, LstCat, lr) -> LBinOp (LEList (flel :: ll), LstCat, lr)
				| _ -> LBinOp (LEList [ flel ], LstCat, fler)
				)
			| LstCat when (lexpr_is_list ?gamma:gamma def) ->
				(match flel, fler with
				(* Empty list is the neutral *)
				| x, LLit (LList [])
				| x, LEList []
				| LLit (LList []), x
				| LEList [], x -> x
				| LEList x, LEList y -> LEList (x @ y)
				| LLit (LList x), LEList y -> LEList (List.map (fun x -> LLit x) x @ y)
				| LEList x, LLit (LList y) -> LEList (x @ List.map (fun x -> LLit x) y)
				(* Rest *)
				| _, _ -> def
				)
			| StrCat when (lexpr_is_string ?gamma:gamma def) ->
				(match flel, fler with
				(* Empty list is the neutral *)
				| x, LLit (String "")
				| LLit (String ""), x -> x
				(* Rest *)
				| _, _ -> def
				)

			| SetDiff when (lexpr_is_set ?gamma:gamma def) ->
				print_debug_petar (Printf.sprintf "SetDiff: %s -d- %s" (JSIL_Print.string_of_logic_expression flel) (JSIL_Print.string_of_logic_expression fler));
				let pfs = Option.map_default (fun pfs -> PFS.to_list pfs) [] pfs in
				(match flel, fler with
				| x, y when (x = y) -> LESet []
				| LESet [], _ -> LESet []
				| x, LESet [] -> x
				| LESet left, LESet right when (all_literals left && all_literals right) ->
					LESet (SLExpr.elements (SLExpr.diff (SLExpr.of_list left) (SLExpr.of_list right)))
				| LESet left, s when (all_literals left) ->
					if (List.for_all (fun x -> set_member pfs x s) left) then LESet [] else def
				| LSetUnion les, _ -> 
					let diffs = List.map (fun le -> f (LBinOp (le, SetDiff, fler))) les in
					LSetUnion diffs
				| LVar _, _ -> if (set_subset pfs flel fler) then LESet [] else def
				| LESet les, fler -> 
					(* We must know that the elements of les are all different, and for that we need the pure formulae *)
					(match all_different pfs les with
					| false -> def
					| true -> 
						print_debug "All different.";
						let _, rest = List.partition (fun x -> set_member pfs x fler) les in
						if (List.for_all (fun x -> not_set_member pfs x fler) rest) then LESet rest else
						LBinOp (LESet rest, SetDiff, fler)
					)
				| _, _ -> def)

				(* let hM = f (LBinOp (flel, SetSub, fler)) in
					(match hM with
					| LLit (Bool true) -> LESet []
					| _ -> def)) *)

			| SetMem when (lexpr_is_bool ?gamma:gamma def) ->
				(match flel, fler with
				| _, LESet [] -> LLit (Bool false)
				| _, LESet [ x ] -> LBinOp (flel, Equal, x)
				| le, LESet les -> 
					(match (List.mem le les) with
					| true -> LLit (Bool true)
					| false -> (match le with
						| LLit _ -> if (all_literals les) then LLit (Bool false) else def
						| _ -> def)
					)

				| _, _ -> def)

			| SetSub when (lexpr_is_bool ?gamma:gamma def) ->
				(match flel, fler with
				| LESet [], _ -> LLit (Bool true)
				| _, LESet [] -> LLit (Bool false)
				| LESet left, LESet right when (all_literals left && all_literals right) ->
					LLit (Bool (SLExpr.subset (SLExpr.of_list left) (SLExpr.of_list right)))
				| LVar v, LSetUnion les -> if (List.mem flel les) then (LLit (Bool true)) else def
				| _, _ -> def)

			| LessThan -> 
				(match flel, fler with
				| LUnOp (LstLen, _), LLit (Num n) when (n <= 0.)-> LLit (Bool false)
				| LUnOp (LstLen, le), LLit (Num 1.) -> LBinOp (le, Equal, LEList [])
				| _, _ -> def)

			| _ -> def
			)
		)

	(* The remaining cases cannot be reduced *)
	| _ -> le 
	) in
	
	let final_result = if (le <> result) && (not (le == result))
		then (print_debug (Printf.sprintf "Reduce_lexpr: %s -> %s" (JSIL_Print.string_of_logic_expression le) (JSIL_Print.string_of_logic_expression result)); f result)
		else result in

	if (no_timing <> None) then (let end_time = Sys.time () in update_statistics "reduce_lexpr" (end_time -. start_time));
	final_result

(* ********************************* *)
(* MULTISETS FOR LOGICAL EXPRESSIONS *)
(* ********************************* *)

(* Unifiables *)

let rec get_lexpr_unifiables ?(no_timing : unit option) (le : jsil_logic_expr) : MS.t * MS.t * MS.t * MS.t = 

	let f = get_lexpr_unifiables ?no_timing:(Some ()) in
	let start_time = Sys.time() in 

	let result = match le with
		| LLit (Loc x) -> MS.empty,       MS.empty,       MS.singleton x, MS.empty
		| LVar x       -> MS.singleton x, MS.empty,       MS.empty,       MS.empty
		| PVar x       -> MS.empty,       MS.singleton x, MS.empty,       MS.empty
		| ALoc x       -> MS.empty,       MS.empty,       MS.empty,       MS.singleton x

		| _ when (lexpr_is_list ?gamma:(Some (TypEnv.init ())) le) -> 
			(match le with 
			| LEList [] -> MS.empty, MS.empty, MS.empty, MS.empty  
			| LEList les -> List.fold_left (fun (lv1, pv1, ll1, al1) x -> 
				let lv2, pv2, ll2, al2 = f x in
					MS.union lv1 lv2, MS.union pv1 pv2, MS.union ll1 ll2, MS.union al1 al2
				) (MS.empty, MS.empty, MS.empty, MS.empty) les
			| _ -> let head_and_tail = get_head_and_tail_of_list le in 
				(match head_and_tail with 
				| None -> MS.empty, MS.empty, MS.empty, MS.empty
				| Some (head, tail) -> 
					let rhead = reduce_lexpr head in 
					let rtail = reduce_lexpr tail in 
						let lv1, pv1, ll1, al1 = f rhead in 
						let lv2, pv2, ll2, al2 = f rtail in 
							MS.union lv1 lv2, MS.union pv1 pv2, MS.union ll1 ll2, MS.union al1 al2
				)
			)

		| _ -> MS.empty, MS.empty, MS.empty, MS.empty
	in

	if (no_timing = None) then 
		(let end_time = Sys.time() in 
		update_statistics "LExpr unification separation" (end_time -. start_time));
	result