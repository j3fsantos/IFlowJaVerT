open SCommon
open JSIL_Syntax

(* When reduction fails *)
exception ReductionException of jsil_logic_expr * string

(****************************)
(* GENERAL HELPER FUNCTIONS *)
(****************************)

let typable ?(gamma : TypEnv.t option) (le : jsil_logic_expr) (target_type : Type.t) : bool = 
	let gamma = Option.default (TypEnv.init ()) gamma in
	let t, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
		t = Some target_type

(***********************************)
(* LIST REASONING HELPER FUNCTIONS *)
(***********************************)

(* What does it mean to be a list? *)
let lexpr_is_list ?(gamma : TypEnv.t option) (le : jsil_logic_expr) : bool =
	typable ?gamma:gamma le ListType

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
	| _ -> raise (Failure (Printf.sprintf "get_length_of_list: list equals %s, impossible" (JSIL_Print.string_of_logic_expression lst)))
	)

(* Finding the nth element of a list *)
let rec get_nth_of_list (lst : jsil_logic_expr) (idx : int) : jsil_logic_expr option =
	let f = get_nth_of_list in

	(* The passed logical expression must represent a list *)
	let _ = assert (lexpr_is_list lst) in

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

	(* The passed logical expression must represent a list *)
	let _ = assert (lexpr_is_list lst) in

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

(* What does it mean to be a string? *)
let rec lexpr_is_string ?(gamma : TypEnv.t option) (le : jsil_logic_expr) : bool =
	typable ?gamma:gamma le StringType

(* Finding the length of a string *)
let rec get_length_of_string (str : jsil_logic_expr) : int option =
	let f = get_length_of_string in

	(* The passed logical expression must represent a list *)
	let _ = assert (lexpr_is_string str) in

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

	(* The passed logical expression must represent a list *)
	let _ = assert (lexpr_is_string str) in

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

(**
	Logical expression reduction - there is no additional information
*)
let rec reduce_lexpr ?(gamma: TypEnv.t option) (le : jsil_logic_expr) = 

	let start_time = Sys.time () in

	let f = reduce_lexpr ?gamma:gamma in
	let result = (match le with

	(* Base lists, character lists, and sets are reduced pointwise *)
	| LEList les -> LEList (List.map f les)
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
			(match (lexpr_is_string fle) with
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
					raise (ReductionException (LUnOp (TypeOf, fle), err_msg))
				| true -> 
					(match tfle with
					| None -> LUnOp (TypeOf, le)
					| Some t -> LLit (Type t)
					)
				)
			(* List head *)
			| Car ->
				let fle = f le in
				(match (lexpr_is_list fle) with
				| true -> let ohdtl = get_head_and_tail_of_list fle in
					Option.map_default (fun (hd, _) -> hd) (LUnOp (Car, fle)) ohdtl
				| false -> 
					let err_msg = "LUnOp(Car, list): list is not a JSIL list." in
					raise (ReductionException (LUnOp (Car, fle), err_msg))
				)

			(* List tail *)
			| Cdr ->
				let fle = f le in
				(match (lexpr_is_list fle) with
				| true -> let ohdtl = get_head_and_tail_of_list fle in
					Option.map_default (fun (_, tl) -> tl) (LUnOp (Cdr, fle)) ohdtl
				| false -> 
					let err_msg = "LUnOp(Cdr, list): list is not a JSIL list." in
					raise (ReductionException (LUnOp (Cdr, fle), err_msg))
				)

			(* List length *)
			| LstLen ->
				let fle = f le in
				(match (lexpr_is_list fle) with
				| true -> let len = get_length_of_list fle in
					Option.map_default (fun len -> LLit (Num (float_of_int len))) (LUnOp (LstLen, fle)) len
				| false -> 
					let err_msg = "LUnOp(LstLen, list): list is not a JSIL list." in
					raise (ReductionException (LUnOp (LstLen, fle), err_msg))
				)

			(* String length *)
			| StrLen ->
				let fle = f le in
				(match (lexpr_is_string fle) with
				| true -> let len = get_length_of_string fle in
					Option.map_default (fun len -> LLit (Num (float_of_int len))) (LUnOp (StrLen, fle)) len
				| false -> 
					let err_msg = "LUnOp(StrLen, list): string is not a JSIL string." in
					raise (ReductionException (LUnOp (StrLen, fle), err_msg))
				)

			| _ -> LUnOp (op, fle)
			)
		)

	| LBinOp (lel, op, ler) ->
		let flel = f lel in
		let fler = f ler in
		(match flel, fler with
		| LLit ll , LLit lr -> 
			let empty_store = Hashtbl.create 31 in
			LLit (JSIL_Interpreter.evaluate_binop empty_store op (Literal ll) (Literal lr))
		| _ -> 
			(match op with
			| _ -> LBinOp (flel, op, fler)
			)
		)

	(* 
		BinOps: don't consider literals!
		But there are cases where one is a literal, and the other isn't, so careful!

		- a Minus b -> a Plus (UnaryMinus b)
		- LstCons         
		- LstCat
		- SetDiff
		- SetMem
		- SetSub
	*)

	(* The remaining cases cannot be reduced *)
	| _ -> le 
	) in

	let end_time = Sys.time () in
  	update_statistics "reduce_lexpr" (end_time -. start_time);
	result