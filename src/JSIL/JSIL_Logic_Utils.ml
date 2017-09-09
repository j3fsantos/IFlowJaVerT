open JSIL_Syntax

(****************************************)
(* Expression/Assertion utilities       *)
(****************************************)

(* Convert expression to logical expression *)
let rec expr_2_lexpr (e : jsil_expr) : jsil_logic_expr =
	let f = expr_2_lexpr in
	match e with
	| Literal l           -> LLit l
	| Var x               -> PVar x
	| BinOp (e1, op, e2)  -> LBinOp ((f e1), op, (f e2))
	| UnOp (op, e)     -> LUnOp (op, f e)
	| TypeOf e            -> LTypeOf (f e)
	| EList es            -> LEList (List.map f es)
	| LstNth (e1, e2)     -> LLstNth (f e1, f e2)
	| StrNth (e1, e2)     -> LStrNth (f e1, f e2)

(** Apply function f to a logic expression, recursively when f returns (new_expr, true). *)
let rec logic_expression_map f lexpr =
	(* Apply the mapping *)
	let map_e = logic_expression_map f in
	let (mapped_lexpr, recurse) = f lexpr in
	if not recurse then mapped_lexpr
	else
  	(* Map recursively to expressions *)
  	(match mapped_lexpr with
  	| LLit _ | LNone | LVar _ | ALoc _ | PVar _ -> mapped_lexpr
  	| LBinOp (e1, op, e2) -> LBinOp (map_e e1, op, map_e e2)
  	| LUnOp (op, e)       -> LUnOp (op, map_e e)
  	| LTypeOf e           -> LTypeOf (map_e e)
  	| LEList le           -> LEList (List.map map_e le)
  	| LCList le           -> LCList (List.map map_e le)
  	| LESet le            -> LESet  (List.map map_e le)
	| LSetUnion le        -> LSetUnion (List.map map_e le)
	| LSetInter le        -> LSetInter (List.map map_e le)
  	| LLstNth (e1, e2)    -> LLstNth (map_e e1, map_e e2)
  	| LStrNth (e1, e2)    -> LStrNth (map_e e1, map_e e2))


(** Apply function f to the logic expressions in an assertion, recursively when f_a returns (new_asrt, true). *)
let rec assertion_map
    (f_a : (jsil_logic_assertion -> jsil_logic_assertion * bool) option)
    (f_e : jsil_logic_expr -> jsil_logic_expr * bool)
    (asrt : jsil_logic_assertion) : jsil_logic_assertion =
  
	(* Map recursively to assertions and expressions *)
	let map_a = assertion_map f_a f_e in
	let map_e = logic_expression_map f_e in
	let (mapped_lasrt, recurse) = (match f_a with
		| Some f -> f asrt
		| None -> (asrt, true)) in
		if not recurse then mapped_lasrt
		else
		(* Recurse *)
		let a' =
			match asrt with
			| LAnd (a1, a2)          -> LAnd (map_a a1, map_a a2)
			| LOr (a1, a2)           -> LOr (map_a a1, map_a a2)
			| LNot a                 -> LNot (map_a a)
			| LTrue                  -> LTrue
			| LFalse                 -> LFalse
			| LEq (e1, e2)           -> LEq (map_e e1, map_e e2)
			| LLess (e1, e2)         -> LLess (map_e e1, map_e e2)
			| LLessEq (e1, e2)       -> LLessEq (map_e e1, map_e e2)
			| LStrLess (e1, e2)      -> LStrLess (map_e e1, map_e e2)
			| LStar (a1, a2)         -> LStar (map_a a1, map_a a2)
			| LPointsTo (e1, e2, e3) -> LPointsTo (map_e e1, map_e e2, map_e e3)
			| LEmp                   -> LEmp
			| LPred (s, le)          -> LPred (s, List.map map_e le)
			| LTypes lt              -> LTypes (List.map (fun (exp, typ) -> (map_e exp, typ)) lt)
			| LEmptyFields (o, ls)   -> LEmptyFields (map_e o, map_e ls)
			| LSetMem (e1, e2)       -> LSetMem (map_e e1, map_e e2)
			| LSetSub (e1, e2)       -> LSetSub (map_e e1, map_e e2)
			| LForAll (bt, a)        -> LForAll (bt, map_a a) in
		let f_a = Option.default (fun x -> (x, true)) f_a in
		let (a'', _) = f_a a' in
			a''

(* A fold on assertions *)
let rec assertion_fold feo f_ac f_state state asrt =
	let new_state = (Option.default (fun le x -> x) f_state) asrt state in
	let fold_a    = assertion_fold feo f_ac f_state new_state in
	let f_ac      = f_ac asrt new_state state in
	let fes les   = Option.map_default (fun fe -> List.map fe les) [] feo in

	match asrt with
	| LTrue | LFalse | LEmp | LTypes _  -> f_ac []

	| LEq (le1, le2) | LLess (le1, le2) | LLessEq (le1, le2)
		| LStrLess (le1, le2) |  LSetMem (le1, le2)
		| LSetSub (le1, le2)  | LEmptyFields (le1, le2) -> f_ac (fes [ le1; le2 ])

	| LPointsTo (le1, le2, le3) -> f_ac (fes [ le1; le2; le3 ])

	| LPred (_, les) -> f_ac (fes les)

	| LAnd (a1, a2)             -> f_ac [ (fold_a a1); (fold_a a2) ]
	| LOr (a1, a2)              -> f_ac [ (fold_a a1); (fold_a a2) ]
	| LStar (a1, a2)            -> f_ac [ (fold_a a1); (fold_a a2) ]
	| LNot a                    -> f_ac [ (fold_a a) ]
	| LForAll (_, a)            -> f_ac [ (fold_a a) ]

(* Producing a star from a list of assertions *)
let star_assertions asrts =
List.fold_left
	(fun ac a ->
		if (not (a = LEmp))
			then (if (ac = LEmp) then a else LStar (a, ac))
			else ac)
	LEmp
	asrts

(* Get all program variables from a logical expression *)
let rec get_logic_expression_pvars_list
    (le : jsil_logic_expr) : jsil_var list =

  let fe = get_logic_expression_pvars_list in
  match le with
  | LLit _ | LNone | ALoc _ | LVar _ -> []
  | PVar v -> [ v ]
  | LBinOp (le1, _, le2) | LLstNth (le1, le2) | LStrNth (le1, le2) -> (fe le1) @ (fe le2)
  | LUnOp (_, le) |	LTypeOf le -> fe le
  | LEList    les
  | LESet     les
  | LSetUnion les
  | LSetInter les
  | LCList les -> List.concat (List.map fe les)

(* Get all program variables from an assertion *)
let get_assertion_pvars (a : jsil_logic_assertion) : jsil_var list =
  let fe = get_logic_expression_pvars_list in
  let f_ac a _ _ ac = List.concat ac in
  assertion_fold (Some fe) f_ac None None a


(** ----------------------------------------------------
    ----------------------------------------------------
    Parser util functions
    ----------------------------------------------------
    ----------------------------------------------------**)
(** ----------------------------------------------------
    Replace "ret" and "err" in spec with corresponding program variables
    -----------------------------------------------------
*)
let replace_spec_keywords
    (spec : jsil_spec option)
    (ret_var : string option)
    (err_var : string option) : (jsil_spec option) =

  (** Step 1 - Extract values from the optionals
   * -----------------------------------------------------------------------------------
  *)
  let ret_var =
    (match ret_var with
     | None -> ""
     | Some var -> var) in
  let err_var =
    (match err_var with
     | None -> ""
     | Some var -> var) in

  (** Step 2 - Construct a new spec with the return keyword replaced by the program variable
   * -----------------------------------------------------------------------------------
   * Map over each of the specs and replace the value in each post-
  *)
  match spec with
  | None      -> None
  | Some spec ->
    Some {
      spec_name   = spec.spec_name;
      spec_params = spec.spec_params;
      proc_specs  = List.map
          (fun current_spec ->
             let subst_ret_err =
               (fun lexpr ->
                  match lexpr with
                  | PVar "ret" -> (PVar ret_var, false)
                  | PVar "err" -> (PVar err_var, false)
                  | _ -> (lexpr, true))
             in
             { pre = current_spec.pre;
               post = List.map (assertion_map None subst_ret_err) current_spec.post;
               ret_flag = current_spec.ret_flag;
             }
          )
          spec.proc_specs;
       previously_normalised = spec.previously_normalised
    } 