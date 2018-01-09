open JSIL_Syntax
open JSIL_Print

let is_int v =
  v = (snd (modf v))

let fresh_sth (name : string) : (unit -> string) =
  let counter = ref 0 in
  let rec f () =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f

let fresh_symbol = fresh_sth "symb_"

(***
 S-Expression Serialization
*)

let sexpr_of_float x =
	if (x == nan)
		then "+nan.0"
		else if (x == neg_infinity)
			then "-inf.0"
			else if (x == infinity)
				then "+inf.0"
				else if (is_int x)
				  then string_of_int (int_of_float x)
					else string_of_float x

let rec sexpr_of_literal lit =
  match lit with
	| Undefined -> "$$undefined"
	| Null -> "$$null"
	| Empty -> "$$empty"
	| Constant c -> string_of_constant c
	| Bool b ->
		(match b with
      		| true -> "#t"
      		| false -> "#f")
    | Num n -> sexpr_of_float n
    | String x -> Printf.sprintf "\"%s\"" x
    | Loc loc -> loc
    | Type t -> string_of_type t
	| LList ll ->
		(match ll with
			| [] -> "(jsil-list )"
			| ll -> Printf.sprintf "(jsil-list %s )" (String.concat " " (List.map sexpr_of_literal ll)))


let sexpr_of_binop bop =
  match bop with
  	| BitwiseXor -> "bor"
  	| _          -> JSIL_Print.string_of_binop bop  


let rec sexpr_of_expression e =
  let se = sexpr_of_expression in
  match e with
    | Literal l -> sexpr_of_literal l
    | Var v -> v
	(* (bop e1 e2) *)
    | BinOp (e1, op, e2) -> Printf.sprintf "(%s %s %s)" (sexpr_of_binop op) (se e1) (se e2)
	(* (uop e1 e2) *)
    | UnOp (op, e) -> Printf.sprintf "(%s %s)" (string_of_unop op) (se e)
	(* (typeof e) *)
    | TypeOf e -> Printf.sprintf "(typeof %s)" (se e)
	(* (make-symbol-number) *)
	| RNumSymb x ->
		let x = 
			match x with 
			| None -> fresh_symbol ()
			| Some x -> x in  
			Printf.sprintf "(make-symbol-number %s)" x
	(* (make-symbol-string) *)
	| RStrSymb x ->
		let x = 
			match x with 
			| None -> fresh_symbol () 
			| Some x -> x in
			Printf.sprintf "(make-symbol-string %s)" x
	| RUntypedSymb x ->
		let x = 
			match x with 
			| None -> fresh_symbol () 
			| Some x -> x in
			Printf.sprintf "(make-untyped-symbol %s)" x
	(* (jsil-list sexpr-e1 ... sexpr-en) *)
	| EList ll ->
		(match ll with
		| [] -> "(jsil-list )"
		| ll -> Printf.sprintf "(jsil-list %s)" (String.concat " " (List.map sexpr_of_expression ll)))
	(* (l-nth e n) *)
	| LstNth (e1, e2) -> Printf.sprintf "(l-nth %s %s)" (se e1) (se e2)
	(* (s-nth e n) *)
	| StrNth (e1, e2) -> Printf.sprintf "(s-nth %s %s)" (se e1) (se e2)
	(* (jsil-set e1 ... en) *)
	| ESet es -> Printf.sprintf "(jsil-set %s)" (String.concat " " (List.map sexpr_of_expression es))
	(* (set-inter e1 ... en) *)
	| SetUnion es -> Printf.sprintf "(set-union %s)" (String.concat " " (List.map sexpr_of_expression es))
    (* (set-union e1 ... en) *)
    | SetInter es -> Printf.sprintf "(set-inter %s)" (String.concat " " (List.map sexpr_of_expression es))
	| _ ->
		let msg = Printf.sprintf "jsil2rkt. Unsupported expression %s\n" 
			(JSIL_Print.string_of_expression e) in  
		raise (Failure msg)


let rec sexpr_of_lexpr le = 
	let sle = sexpr_of_lexpr in 
	match le with 
	| LLit lit               -> sexpr_of_literal lit 
	| LVar v                 -> v
	| ALoc aloc              -> aloc 
	| PVar v                 -> v
	| LBinOp (le1, bop, le2) -> 
		Printf.sprintf "(%s %s %s)" (sexpr_of_binop bop) (sle le1) (sle le2)
	| LUnOp (unop, le)       -> 
		 Printf.sprintf "(%s %s)" (string_of_unop unop) (sle le)
	| LTypeOf le             -> Printf.sprintf "(typeof %s)" (sle le)
	| LLstNth (le1, le2)     -> Printf.sprintf "(l-nth %s %s)" (sle le1) (sle le2)
	| LStrNth (le1, le2)     -> Printf.sprintf "(s-nth %s %s)" (sle le1) (sle le2)
	| LEList les             -> Printf.sprintf "(jsil-list %s)" (String.concat " " (List.map sle les))
	| LCList les             -> raise (Failure "DEATH. sexpr_of_lexpr")
	| LESet les              -> Printf.sprintf "(jsil-set %s)" (String.concat " " (List.map sle les))
	| LSetUnion les          -> Printf.sprintf "(set-union %s)" (String.concat " " (List.map sle les))
	| LSetInter les          -> Printf.sprintf "(set-inter %s)" (String.concat " " (List.map sle les))
	| LNone                  -> "none"



let rec sexpr_of_assertion a = 
	let sle = sexpr_of_lexpr in 
	let sa  = sexpr_of_assertion in 
	match a with 
	| LTrue                     -> "true"
	| LFalse                    -> "false"
	| LNot a                    -> Printf.sprintf "(not %s)" (sa a)
	| LAnd (a1, a2)             -> Printf.sprintf "(and %s %s)" (sa a1) (sa a2)
	| LOr (a1, a2)              -> Printf.sprintf "(or %s %s)" (sa a1) (sa a2)
	| LEmp                      -> "emp"
	| LStar (a1, a2)            -> Printf.sprintf "(star %s %s)" (sa a1) (sa a2)
	| LPointsTo (le1, le2, le3) -> Printf.sprintf "(cell %s %s %s)" (sle le1) (sle le2) (sle le3)
	| LPred (p_name, les)       -> Printf.sprintf "(pred-asrt %s %s)" p_name (String.concat " " (List.map sle les))
	| LForAll _                 -> raise (Failure "DEATH. sexpr_of_assertion")
	| LTypes le_type_pairs      -> Printf.sprintf "(types %s)" 
									(String.concat " " 
										(List.map 
											(fun (le, t) -> "("  ^ (sle le) ^ " " ^ (string_of_type t) ^ ")")
											le_type_pairs))
	| LEmptyFields (le1, le2)   -> Printf.sprintf "(empty-fields %s %s)" (sle le1) (sle le2)             
	| LEq (le1, le2)            -> Printf.sprintf "(eq? %s %s)" (sle le1) (sle le2)
	| LLess (le1, le2)          -> Printf.sprintf "(< %s %s)" (sle le1) (sle le2)
	| LLessEq (le1, le2)        -> Printf.sprintf "(<= %s %s)" (sle le1) (sle le2)
	| LStrLess (le1, le2)       -> Printf.sprintf "(string-less-eq %s %s)" (sle le1) (sle le2)
	| LSetMem (le1, le2)        -> Printf.sprintf "(set-mem %s %s)" (sle le1) (sle le2)
	| LSetSub (le1, le2)        -> Printf.sprintf "(set-sub %s %s)" (sle le1) (sle le2)
	


let rec sexpr_of_bcmd bcmd i line_numbers_on =
	let se = sexpr_of_expression in
	let sa = sexpr_of_assertion in 
	let str_i = if line_numbers_on then (string_of_int i) ^ " " else "" in
	match bcmd with
	(* ('skip) *)
  | SSkip -> Printf.sprintf "'(%sskip)" str_i
	(* ('var_assign var e)       *)
	| SAssignment (var, e) -> Printf.sprintf "'(%sv-assign %s %s)" str_i var (se e)
	(* ('new var)                *)
	| SNew var -> Printf.sprintf "'(%snew %s)" str_i var
 	(* ('h-read var e1 e2)	     *)
	| SLookup (var, e1, e2) -> Printf.sprintf "'(%sh-read %s %s %s)" str_i var (se e1) (se e2)
	(* ('h-assign var e e)       *)
	| SMutation (e1, e2, e3) -> Printf.sprintf "'(%sh-assign %s %s %s)" str_i (se e1) (se e2) (se e3)
	(* ('delete var e1 e2)       *)
	| SDelete (e1, e2) ->  Printf.sprintf "'(%sh-delete %s %s)" str_i (se e1) (se e2)
	(* ('delete-object e1)       *)
	| SDeleteObj (e1) ->  Printf.sprintf "'(%sdelete-object %s)" str_i (se e1)
	(* ('has-field var e1 e2)    *)
    | SHasField (var, e1, e2) -> Printf.sprintf "'(%shas-field %s %s %s)" str_i var (se e1) (se e2)
    (* ('get-fields var e)       *)
	| SGetFields (var, e) -> Printf.sprintf "'(%sget-fields %s %s)" str_i var (se e)
	(* ('arguments var)          *)
	| SArguments (var) -> Printf.sprintf "'(%sarguments %s)" str_i var
	(* ('terminate-successfully) *)
    | STermSucc -> Printf.sprintf "'(%ssuccess)" str_i
	(* ('terminate-successfully) *)
    | STermFail -> Printf.sprintf "'(%sfailure)" str_i
    (* (assume e) *)
	| RAssume e -> Printf.sprintf "'(%sassume %s)" str_i (se e)
	(* (assert e) *)
	| RAssert e -> Printf.sprintf "'(%sassert %s)" str_i (se e)
	(* (assert-* asrts)*)
	| SepAssert asrts -> Printf.sprintf "'(%sassert-* %s)" str_i (String.concat " " (List.map sa asrts))


let rec sexpr_of_cmd sjsil_cmd tabs i line_numbers_on =
	let sjsil_cmd = match sjsil_cmd with | (_, cmd) -> cmd in
	let str_i = if line_numbers_on then (string_of_int i) ^ " " else "" in
	let str_tabs = tabs_to_str tabs in
  match sjsil_cmd with
	(* basic command *)
	| SBasic bcmd -> str_tabs ^ sexpr_of_bcmd bcmd i line_numbers_on
	(* ('goto j) *)
  | SGoto j ->
		let str_j = string_of_int j in
			str_tabs ^ Printf.sprintf "'(%sgoto %s)" str_i str_j
  (* ('goto e j k) *)
	| SGuardedGoto (e, j, k) ->
		let str_j = string_of_int j in
		let str_k = string_of_int k in
		let str_e = (sexpr_of_expression e) in
			str_tabs ^  Printf.sprintf "'(%sgoto %s %s %s)" str_i str_e str_j str_k
	(* ('call left_var proc_name '(arg1 ... argn) err_lab) *)
	| SCall (var, proc_name_expr, arg_expr_list, error_lab) ->
		let proc_name_expr_str = sexpr_of_expression proc_name_expr in
		let error_lab = (match error_lab with | None -> "" | Some error_lab -> (string_of_int error_lab)) in
		let arg_expr_list_str = match arg_expr_list with
		|	[] -> ""
		| _ -> String.concat " " (List.map sexpr_of_expression arg_expr_list) in
			str_tabs ^  Printf.sprintf "'(%scall %s %s (%s) %s)" str_i var proc_name_expr_str arg_expr_list_str error_lab
	(* ('apply left_var expr_list err_lab) *)
	| SApply (var, arg_expr_list, error_lab) ->
		let error_lab = (match error_lab with | None -> "" | Some error_lab -> (string_of_int error_lab)) in
		let arg_expr_list_str = match arg_expr_list with
		|	[] -> ""
		| _ -> String.concat " " (List.map sexpr_of_expression arg_expr_list) in
			str_tabs ^  Printf.sprintf "'(%sapply %s (%s) %s)" str_i var arg_expr_list_str error_lab
	(* ('v-phi-assign var var_1 var_2 ... var_n) *)
	| SPhiAssignment (var, var_arr) ->
		let var_arr_str =
			Array.fold_left
				(fun ac v -> ac ^ " " ^ sexpr_of_expression v)
				""
				var_arr in
		str_tabs ^ (Printf.sprintf "'(%sv-phi-assign %s %s)" str_i var var_arr_str)
	(* ('v-psi-assign var var_1 var_2 ... var_n) *)
	| SPsiAssignment(var, var_arr) ->
		let var_arr_str =
			Array.fold_left
				(fun ac v -> ac ^ " " ^ sexpr_of_expression v)
				""
				var_arr in
		str_tabs ^ (Printf.sprintf "'(%sv-psi-assign %s %s)" str_i var var_arr_str)

let sexpr_of_params fparams =
	match fparams with
	| [] -> ""
	| param :: rest ->
  	List.fold_left
  		(fun prev_params param -> prev_params ^ " '" ^ param)  (" '" ^ param) rest


let serialize_cmd_arr cmds tabs line_numbers serialize_cmd =
	let number_of_cmds = Array.length cmds in
	let rec serialize_cmd_arr_iter i str_ac =
		if (i >= number_of_cmds)
			then str_ac
			else
				((let cmd = cmds.(i) in
				let str_cmd = serialize_cmd cmd tabs i line_numbers in
				serialize_cmd_arr_iter (i + 1) (str_ac ^ str_cmd ^ "\n"))) in
	serialize_cmd_arr_iter 0 ""

let sexpr_of_cmd_arr cmds tabs line_numbers =
	serialize_cmd_arr cmds tabs line_numbers sexpr_of_cmd

(*
  (procedure xpto (arg1 arg2 ...)
		(body ...)
		('return ret_var ret_label)
		('error err_var err_label))
*)
let sexpr_of_procedure proc line_numbers =
	Printf.sprintf "(procedure \"%s\" \n\t(args%s) \n\t(body \n %s \n\t) \n%s \n %s )"
  	proc.proc_name
   	(sexpr_of_params proc.proc_params)
		(sexpr_of_cmd_arr proc.proc_body 2 line_numbers)
		(match proc.ret_var, proc.ret_label with
		| None, None -> "\t'() \n"
		| Some var, Some label -> (Printf.sprintf "\t(ret-ctx '%s %s) \n" var (string_of_int label))
		| _, _ -> raise (Failure "Return variable and return label not both present or both absent!"))
		(match proc.error_var, proc.error_label with
		| None, None -> "\t'() \n"
		| Some var, Some label -> (Printf.sprintf "\t(err-ctx '%s %s) \n" var (string_of_int label))
		| _, _ -> raise (Failure "Error variable and error label not both present or both absent!"))

let sexpr_of_program program line_numbers =
	Hashtbl.fold
	(fun _ proc acc_str ->
		acc_str ^ "\n" ^ (sexpr_of_procedure proc line_numbers))
	program
	""


let serialize_prog_racket prog line_numbers =
	let serialized_prog	= sexpr_of_program prog line_numbers in
	Printf.sprintf SExpr_Templates.template_procs_racket serialized_prog

let serialize_internals_racket specs builtins line_numbers =
	let serialized_specs = sexpr_of_program specs line_numbers in
	let serialized_builtins = sexpr_of_program builtins line_numbers in
	let serialized_internals = serialized_specs ^ "\n" ^ serialized_builtins in
	Printf.sprintf SExpr_Templates.template_internal_procs_racket serialized_internals


let sexpr_of_heap (h : jsil_lit SHeap.t SHeap.t) =
	SHeap.fold
		(fun loc obj printed_heap ->
			  let printed_object =
					(SHeap.fold
						(fun prop hval print_obj ->
							let printed_hval = sexpr_of_literal hval in
							let printed_cell = Printf.sprintf "\n\t(cell '%s \"%s\" '%s)" loc prop printed_hval in
							print_obj ^ printed_cell)
						obj "") in
			printed_heap ^ (printed_object))
		h
		""

(* (define target (heap (cell loc prop val) (cell loc prop val) ... )) *)
let serialize_heap_racket h =
	let serialized_h = sexpr_of_heap h in
	Printf.sprintf SExpr_Templates.template_hp_racket serialized_h


let print_which_pred wp =
	Hashtbl.fold
	  (fun k v ac ->
		 ac ^
		 (match k with
			| (pn : string), (pc : int), (cc : int) -> Printf.sprintf "    (\"%s\" %d %d %d)\n" pn pc cc v))
		wp ""
