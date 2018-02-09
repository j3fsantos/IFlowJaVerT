open SCommon
open JSIL_Syntax

(* When reduction fails *)
exception ReductionException of jsil_logic_expr * string

(***************************)
(* TYPING HELPER FUNCTIONS *)
(***************************)

let typable ?(gamma : TypEnv.t option) (le : jsil_logic_expr) (target_type : Type.t) : bool = 
	let gamma = Option.default (TypEnv.init ()) gamma in
	let t, success, _ = JSIL_Logic_Utils.type_lexpr gamma le in
		if success then (t = Some target_type) else
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

(* Booleans *)
let lexpr_is_set ?(gamma : TypEnv.t option) (le : jsil_logic_expr) : bool =
	typable ?gamma:gamma le SetType

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

	| _ -> raise (Failure (Printf.sprintf "get_nth_of_list: list equals %s, impossible" (JSIL_Print.string_of_logic_expression lst)))
	) 

(* Finding the nth element of a list *)
let rec get_head_and_tail_of_list (lst : jsil_logic_expr) : (jsil_logic_expr * jsil_logic_expr) option =
	let f = get_head_and_tail_of_list in

	let err_msg = "get_head_and_tail_of_list: empty list passed." in

	(match lst with
	(* Nothing can be done for variables *)
	| PVar _ -> None
	| LVar _ -> None
	(* Base lists of literals and logical expressions *)
	| LLit (LList l) -> assert (0 < List.length l); Some (LLit (List.hd l), LLit (LList (List.tl l)))
	| LEList l       -> assert (0 < List.length l); Some (List.nth l 0, LEList (List.tl l))
	| LBinOp (hd, LstCons, lst) -> Some (hd, lst)
	| LBinOp (lel, LstCat, ler) -> 
		Option.default None 
			(Option.map 
				(fun (hd, tl) -> 
					Some (hd, LBinOp (tl, LstCat, ler)))
				(f lel)
			)

	| _ -> raise (Failure (Printf.sprintf "get_nth_of_list: list equals %s, impossible" (JSIL_Print.string_of_logic_expression lst)))
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
	| LLit (String s) -> assert (idx < String.length s); Some (LLit (String (String.sub s idx 1)))
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

(*************)
(* REDUCTION *)
(*************)

(** Reduction of logical expressions *)
let rec reduce_lexpr ?(gamma: TypEnv.t option) (le : jsil_logic_expr) = 

	let start_time = Sys.time () in

	let f = reduce_lexpr ?gamma:gamma in
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
			(match (lexpr_is_list ?gamma:gamma fle) with
			| true -> Option.default (LLstNth (fle, fidx)) (get_nth_of_list fle (int_of_float n))
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
			| [ LESet s ] -> LESet s 
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
				| [ LESet s ] -> LESet s 
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
				let tfle, how, _ = JSIL_Logic_Utils.type_lexpr gamma fle in
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
				(match (lexpr_is_list ?gamma:gamma fle) with
				| true -> let ohdtl = get_head_and_tail_of_list fle in
					Option.map_default (fun (hd, _) -> hd) def ohdtl
				| false -> 
					let err_msg = "LUnOp(Car, list): list is not a JSIL list." in
					raise (ReductionException (def, err_msg))
				)

			(* List tail *)
			| Cdr ->
				(match (lexpr_is_list ?gamma:gamma fle) with
				| true -> let ohdtl = get_head_and_tail_of_list fle in
					Option.map_default (fun (_, tl) -> tl) def ohdtl
				| false -> 
					let err_msg = "LUnOp(Cdr, list): list is not a JSIL list." in
					raise (ReductionException (def, err_msg))
				)

			(* List length *)
			| LstLen ->
				(match (lexpr_is_list ?gamma:gamma fle) with
				| true -> let len = get_length_of_list fle in
					Option.map_default (fun len -> LLit (Num (float_of_int len))) def len
				| false -> 
					let err_msg = "LUnOp(LstLen, list): list is not a JSIL list." in
					raise (ReductionException (def, err_msg))
				)

			(* String length *)
			| StrLen ->
				(match (lexpr_is_string ?gamma:gamma fle) with
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
			| Plus when (lexpr_is_number ?gamma:gamma def) ->
				(match flel, fler with
				(* 0 is the neutral *)
				| LLit (Num 0.), x
				| x, LLit (Num 0.) -> x
				(* Associate to the right *)
				| LBinOp (flell, Plus, flelr), fler -> LBinOp (flell, Plus, LBinOp (flelr, Plus, fler))
				(* Rest *)
				| _, _ -> def
				)
			| Minus when (lexpr_is_number ?gamma:gamma def) ->
				(match flel, fler with
				(* 0 is the neutral *)
				| LLit (Num 0.), x -> LUnOp (UnaryMinus, x)
				| x, LLit (Num 0.) -> x
				(* Transform to unary minus *)
				| _, _ -> LBinOp (flel, Plus, (LUnOp (UnaryMinus, fler)))
				)
			| Times when (lexpr_is_number ?gamma:gamma def) ->
				(match flel, fler with
				(* 1 is the neutral *)
				| LLit (Num 1.), x 
				| x, LLit (Num 1.) -> x
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
				(match flel, fler with
				(* Empty list on the right *)
				| x, LLit (LList [])
				| x, LEList [] -> LEList [ x ]
				(* Rest *)
				| _, _ -> def
				)
			| LstCat when (lexpr_is_list ?gamma:gamma def) ->
				(match flel, fler with
				(* Empty list is the neutral *)
				| x, LLit (LList [])
				| x, LEList []
				| LLit (LList []), x
				| LEList [], x -> x
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
				(match flel, fler with
				| LESet [], _ -> LESet []
				| x, LESet [] -> x
				| _, _ -> def)
			| SetMem when (lexpr_is_set ?gamma:gamma def) ->
				(match flel, fler with
				| _, LESet [] -> LLit (Bool false)
				| _, _ -> def)
			| SetSub when (lexpr_is_set ?gamma:gamma def) ->
				(match flel, fler with
				| LESet [], _ -> LLit (Bool true)
				| _, LESet [] -> LLit (Bool false)
				| _, _ -> def)
			| _ -> def
			)
		)

	(* The remaining cases cannot be reduced *)
	| _ -> le 
	) in
	
	if (le <> result) 
		then f result 
		else 
		(let end_time = Sys.time () in
			update_statistics "reduce_lexpr" (end_time -. start_time);
			result)