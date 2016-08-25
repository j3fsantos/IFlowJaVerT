open JSIL_Syntax
open JSIL_Memory_Model
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
		| Integer i -> string_of_int i
    | Num n -> sexpr_of_float n
    | String x -> Printf.sprintf "\"%s\"" x
    | Loc loc -> loc
    | Type t -> string_of_type t 
		| LVRef (l, x) -> Printf.sprintf "(ref %s \"%s\" $$v-reference_type)" (sexpr_of_literal l) x  
	  | LORef (l, x) -> Printf.sprintf "(ref %s \"%s\" $$o-reference_type)" (sexpr_of_literal l) x   
		| LList ll -> 
			(match ll with
			| [] -> "(jsil-list )"
			| ll -> Printf.sprintf "(jsil-list %s )" (String.concat " " (List.map sexpr_of_literal ll)))

let sexpr_of_binop bop =
  match bop with
  | Equal -> "="
  | LessThan -> "<"
	| LessThanString -> "<s"
  | LessThanEqual -> "<="
 	| Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Div -> "/"
  | Mod -> "%"
	| And -> "and"
  | Or -> "or"
	| BitwiseAnd -> "&"
  | BitwiseOr -> "|"
  | BitwiseXor -> "bor"
	| LeftShift -> "<<"
  | SignedRightShift -> ">>"
  | UnsignedRightShift -> ">>>"
	| M_atan2 -> "m_atan2"
	| M_pow -> "**"
	| Subtype -> "<:"
	| LstCons -> "::"
	| LstCat -> "@"
	| StrCat -> "++"

let rec sexpr_of_expression e =
  let se = sexpr_of_expression in
  match e with
    | Literal l -> sexpr_of_literal l
    | Var v -> v
		(* (bop e1 e2) *)
    | BinOp (e1, op, e2) -> Printf.sprintf "(%s %s %s)" (sexpr_of_binop op) (se e1) (se e2)
		(* (uop e1 e2) *)
    | UnaryOp (op, e) -> Printf.sprintf "(%s %s)" (string_of_unop op) (se e)
		(* (ref-v e1 e2) *)
    | VRef (e1, e2) -> Printf.sprintf "(ref-v %s %s)" (se e1) (se e2)
  	(* (ref-o e1 e2) *)
    | ORef (e1, e2) -> Printf.sprintf "(ref-o %s %s)" (se e1) (se e2)
		(* (base e) *)
    | Base e -> Printf.sprintf "(base %s)" (se e)
		(* (field e) *)
    | Field e -> Printf.sprintf "(field %s)" (se e)
		(* (typeof e) *)
    | TypeOf e -> Printf.sprintf "(typeof %s)" (se e) 
		(* (assume e) *) 
		| RAssume e -> Printf.sprintf "(assume %s)" (se e)
		(* (assert e) *)
		| RAssert e -> Printf.sprintf "(assert %s)" (se e)
		(* (make-symbol-number) *) 
		| RNumSymb -> 
			let x = fresh_symbol () in 
			Printf.sprintf "(make-symbol-number %s)" x 
		(* (make-symbol-string) *) 
		| RStrSymb -> 
			let x = fresh_symbol () in 
			Printf.sprintf "(make-symbol-string %s)" x
		(* (jsil-list sexpr-e1 ... sexpr-en) *) 
		| EList ll -> 
			(match ll with
			| [] -> "(jsil-list )"
			| ll -> Printf.sprintf "(jsil-list %s)" (String.concat " " (List.map sexpr_of_expression ll)))
		(* (l-nth e n) *)
		| LstNth (e1, e2) -> Printf.sprintf "(l-nth %s %s)" (se e1) (se e2)
		(* (s-nth e n) *)
		| StrNth (e1, e2) -> Printf.sprintf "(s-nth %s %s)" (se e1) (se e2)

let rec sexpr_of_bcmd bcmd i line_numbers_on = 
	let se = sexpr_of_expression in
	let str_i = if line_numbers_on then (string_of_int i) ^ " " else "" in
	match bcmd with 
	(* ('skip) *)
  | SSkip -> Printf.sprintf "'(%sskip)" str_i
	(* ('var_assign var e) *)
	| SAssignment (var, e) -> Printf.sprintf "'(%sv-assign %s %s)" str_i var (se e)
	(* ('new var) *)
	| SNew var -> Printf.sprintf "'(%snew %s)" str_i var
 	(* ('h-read var e1 e2)	*)
	| SLookup (var, e1, e2) -> Printf.sprintf "'(%sh-read %s %s %s)" str_i var (se e1) (se e2)
	(* ('h-assign var e e) *)
	| SMutation (e1, e2, e3) -> Printf.sprintf "'(%sh-assign %s %s %s)" str_i (se e1) (se e2) (se e3)
	(* ('delete var e1 e2) *)
	| SDelete (e1, e2) ->  Printf.sprintf "'(%sh-delete %s %s)" str_i (se e1) (se e2)	
	(* ('has-field var e1 e2) *)
  | SHasField (var, e1, e2) -> Printf.sprintf "'(%shas-field %s %s %s)" str_i var (se e1) (se e2)
  (* ('get-fields var e) *)
	| SGetFields (var, e) -> Printf.sprintf "'(%sget-fields %s %s)" str_i var (se e)
	(* ('arguments var) *)
	| SArguments (var) -> Printf.sprintf "'(%sarguments %s)" str_i var

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
				(fun ac v -> 
					match v with 
					| Some v -> ac ^ " " ^ v
					| None -> ac ^ " $$empty "
				)
				""
				var_arr in 
		str_tabs ^ (Printf.sprintf "'(%sv-phi-assign %s %s)" str_i var var_arr_str)
	(* ('v-psi-assign var var_1 var_2 ... var_n) *)
	| SPsiAssignment(var, var_arr) -> 
		let var_arr_str = 
			Array.fold_left 
				(fun ac v -> 
					match v with 
					| Some v -> ac ^ " " ^ v
					| None -> ac ^ " $$empty "
				)
				""
				var_arr in 
		str_tabs ^ (Printf.sprintf "'(%sv-psi-assign %s %s)" str_i var var_arr_str)	

let sexpr_of_params fparams =
	match fparams with
	| [] -> ""
	| param :: rest ->
  	List.fold_left 
  		(fun prev_params param -> prev_params ^ " '" ^ param)  (" '" ^ param) rest

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
							let printed_hval = string_of_literal hval false in 
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
