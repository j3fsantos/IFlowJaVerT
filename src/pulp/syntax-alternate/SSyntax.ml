open Pulp_Syntax
open Pulp_Procedure

(***
 Auxiliary Functions
*)

let rec tabs_to_str i  = 
	if i == 0 then "" else "\t" ^ (tabs_to_str (i - 1))


(***
 SJSIL - syntax
*)

(* SJSIL Basic statements *)
type basic_jsil_cmd =
  | SSkip	      
  | SAssignment of variable   * expression
	| SNew        of variable
	| SLookup     of variable   * expression * expression
  | SMutation   of expression * expression * expression
	| SDelete     of expression * expression
	| SHasField   of variable   * expression * expression
	| SProtoField of variable   * expression * expression
	| SProtoObj   of variable   * expression * expression 

(* SJSIL All Statements *)
type jsil_cmd =
  | SBasic       of basic_jsil_cmd 
	| SGoto        of int
	| SGuardedGoto of expression * int        * int
	| SCall        of variable   * expression * expression list * int

(* SJSIL procedures *)
type procedure = { 
    proc_name : string;
    proc_body : jsil_cmd list;
    proc_params : variable list; 
		ret_label: int; 
		ret_var: variable;
		error_label: int; 
		error_var: variable
}

let spec_function_get_params sf = match sf with
  | GetValue expr -> [expr]
  | PutValue (expr1, expr2) -> [expr1; expr2]
  | Get (expr1, expr2) -> [expr1; expr2]
  | HasProperty (expr1, expr2) -> [expr1; expr2]
  | DefaultValue _ ->  raise (Failure "Generated JSIL code should not contain calls to DefaultValue")
  | ToPrimitive _ -> raise (Failure "Generated JSIL code should not contain calls to ToPrimitive")
  | ToBoolean expr -> [expr] 
  | ToNumber expr -> [expr]
  | ToNumberPrim expr -> [expr]
  | ToString expr -> [expr] 
  | ToStringPrim expr -> [expr]
  | ToObject expr -> [expr]
  | CheckObjectCoercible expr -> [expr]
  | IsCallable expr -> [expr]
  | AbstractRelation _ ->  raise (Failure "Generated JSIL code should not contain calls to Abstract Relation") 
  | StrictEquality (expr1, expr2) -> [expr1; expr2]
  | StrictEqualitySameType (expr1, expr2) -> [expr1; expr2]



(***
 Translating jsil to sjsil 
*)
let jsil_to_sjsil jsil_cmds ret_label ex_label = 
	
	(* Hashtable for labels *) 
	let my_hash = Hashtbl.create 80021 in 
	
	(* retrieve label number from hashtable *)
	let label_to_number lab = 
		if (Hashtbl.mem my_hash lab)
			then (Hashtbl.find my_hash lab)
			else -1 in 
			
	(* associate labels with numbers *)
	let rec register_labels cmd_list cur_len = 
		match cmd_list with 
		| [] -> true
		| cmd :: cmd_list ->
			(match cmd.stmt_stx with 
				| Label l ->
						Hashtbl.add my_hash l cur_len;
					 	if ((l != ret_label) && (l != ex_label)) 
							then register_labels cmd_list cur_len
							else register_labels cmd_list (cur_len + 1)   		 
				| _ -> register_labels cmd_list (cur_len + 1)) in 
	
	(* translate call *) 
	let rewrite_call var call = 
		SCall (var,
		       call.call_name,
			  	 [call.call_this; call.call_scope] @ call.call_args, 
				   label_to_number call.call_throw_label) in
					
	let call_with_name scall new_name =
		match scall with
		 | SCall (var, name, exprs, i) -> SCall (var, new_name, exprs, i)
		 | _ -> raise (Failure "This function only expects a call") in
	
	let rec jsil_to_sjsil_iter jsil_cmds sjil_cmds_so_far = 
		let jsil_cmds = Pulp_Translate_Aux.to_ivl_goto jsil_cmds in
		match jsil_cmds with 
		| [] -> sjil_cmds_so_far
		| jsil_cmd :: rest_jsil_cmds ->
			(match jsil_cmd.stmt_stx with 
			(* Sugar *)
			| Sugar sugar_cmd ->
				(match sugar_cmd with 
				| SpecFunction (var, sf, l) ->
					let sjsil_cmd = (SCall (var, (Literal (String (Pulp_Syntax_Print.string_of_spec_fun_id sf))), (spec_function_get_params sf), (label_to_number l))) in 
						jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ sjsil_cmd ])
				| _ -> raise (Failure "Unexpected Sugar construct"))
			(* Label*)
			| Label l -> 
				if ((l != ret_label) && (l != ex_label))
					then jsil_to_sjsil_iter rest_jsil_cmds sjil_cmds_so_far
					else jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SBasic SSkip) ])
			(* Goto *)
			| Goto l -> jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SGoto (label_to_number l)) ])
			(* Guarded Goto *)
			| GuardedGoto (expr, l1, l2) -> 
				jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SGuardedGoto (expr, (label_to_number l1), (label_to_number l2))) ])
			(* Skip *)
			| Basic (Skip) -> 
				jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SBasic (SSkip)) ])	
		  (* Field Assignment *)
			| Basic (Mutation mutation) -> 
				jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SBasic (SMutation (mutation.m_loc, mutation.m_field, mutation.m_right))) ])
			(* Variable Assignment *)
			| Basic (Assignment ass) -> 
						let var = ass.assign_left in
						(match ass.assign_right with 
						  (* Procedure Call*)
							| Call        call 
							| BuiltinCall call ->
								jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (rewrite_call var call) ])
							(* Eval *)				
							| Eval call -> 
								jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (call_with_name (rewrite_call var call) (Literal (String ("eval")))) ])
							(* New *)	
							| Obj ->
								jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SBasic (SNew var)) ])
							(* Field Lookup *)					
							| Lookup (e1, e2) -> 
								jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SBasic (SLookup (var, e1, e2))) ])
							(* Delete *)				
							| Deallocation (e1, e2) -> 
								jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SBasic (SDelete (e1, e2)));  (SBasic (SAssignment (var, (Literal (Bool true))))) ])
							(* HasField *)					
							| HasField (e1, e2) -> 
								jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SBasic (SHasField (var, e1, e2))) ])
							(* Simple Assignment *)					
							| Expression e1 -> 
								jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SBasic (SAssignment (var, e1))) ])
							(* Proto Field *)					
							| ProtoF (e1, e2) -> 
								jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SBasic (SProtoField (var, e1, e2))) ])
							(* Proto Obj *)															
							| ProtoO (e1, e2) -> 
								jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SBasic (SProtoObj (var, e1, e2))) ]))
				)	in
				
	(* replace labels in gotos with respective numbers *)
	let _ = register_labels jsil_cmds  0 in 
  (jsil_to_sjsil_iter jsil_cmds []), (label_to_number ret_label), (label_to_number ex_label)

let jsil_to_sjsil_proc jsil_proc = 
	let sjsil_body, ret_lab, err_lab = jsil_to_sjsil jsil_proc.func_body jsil_proc.func_ctx.label_return jsil_proc.func_ctx.label_throw in 
	{ 
    proc_name = jsil_proc.func_name;
    proc_body = sjsil_body;
    proc_params = jsil_proc.func_params; 
		ret_label = ret_lab;
		ret_var = jsil_proc.func_ctx.return_var;
		error_label = err_lab;
		error_var = jsil_proc.func_ctx.throw_var
	}
	

(***
 S-Expression Serialization
*)


let sexpr_of_bool x =
  match x with
    | true -> "#t"
    | false -> "#f"

let sexpr_of_literal lit =
  match lit with
    | LLoc l -> Pulp_Syntax_Print.string_of_builtin_loc l
    | Num n -> string_of_float n
    | String x -> Printf.sprintf "\"%s\"" x
    | Null -> "null"
    | Bool b -> sexpr_of_bool b
    | Undefined -> "undefined"
    | Empty -> "empty" 
    | Type t -> Pulp_Syntax_Print.string_of_pulp_type t 

let rec sexpr_of_expression e =
  let se = sexpr_of_expression in
  match e with
    | Literal l -> sexpr_of_literal l
    | Var v -> Pulp_Syntax_Print.string_of_var v
		(* (bop e1 e2) *)
    | BinOp (e1, op, e2) -> Printf.sprintf "(%s %s %s)" (Pulp_Syntax_Print.string_of_bin_op op) (se e1) (se e2)
		(* (uop e1 e2) *)
    | UnaryOp (op, e) -> Printf.sprintf "(%s %s)" (Pulp_Syntax_Print.string_of_unary_op op) (se e)
		(* ('typeof e) *)
    | TypeOf e -> Printf.sprintf "(typeof %s)" (se e) 
		(* ('ref e1 e2 e3) *)
    | Ref (e1, e2, t) -> Printf.sprintf "(ref %s %s %s)" (se e1) (se e2)
      (match t with
        | MemberReference -> "o"
        | VariableReference -> "v")
		(* ('base e) *)
    | Base e -> Printf.sprintf "(base %s)" (se e)
		(* ('field e) *)
    | Field e -> Printf.sprintf "(field %s)" (se e)

let rec sexpr_of_bcmd bcmd i line_numbers_on = 
	let se = sexpr_of_expression in
	let str_i = if line_numbers_on then (string_of_int i) ^ " " else "" in
	match bcmd with 
	(* ('skip) *)
  | SSkip -> Printf.sprintf "'(%sskip)" str_i
	(* ('var_assign var e1 e2) *)
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
	(* ('proto-field var e1 e2) *)
	| SProtoField (var, e1, e2) -> Printf.sprintf "'(%sproto-field %s %s %s)" str_i var (se e1) (se e2)
	(* ('proto-obj var e1 e2) *)
	| SProtoObj (var, e1, e2) -> Printf.sprintf "'(%sproto-obj %s %s %s)" str_i var (se e1) (se e2)		

let rec sexpr_of_cmd sjsil_cmd tabs i line_numbers_on =
	let str_i = if line_numbers_on then (string_of_int i) ^ " " else "" in
	let str_tabs = tabs_to_str tabs in  
  match sjsil_cmd with
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
	(* basic command *)
	| SBasic bcmd -> str_tabs ^ sexpr_of_bcmd bcmd i line_numbers_on
	(* ('call left_var proc_name '(arg1 ... argn) err_lab) *)
	| SCall (var, proc_name_expr, arg_expr_list, error_lab) -> 
		let proc_name_expr_str = sexpr_of_expression proc_name_expr in 
		let error_lab = string_of_int error_lab in 
		let arg_expr_list_str = match arg_expr_list with
		|	[] -> ""
		| _ -> String.concat " " (List.map sexpr_of_expression arg_expr_list) in 
			str_tabs ^  Printf.sprintf "'(%scall %s %s (%s) %s)" str_i var proc_name_expr_str arg_expr_list_str error_lab

let sexpr_of_params fparams = 
	List.fold_left 
		(fun prev_params param -> prev_params ^ " '" ^ param) "" fparams			

let sexpr_of_cmd_list cmd_list tabs line_numbers =
	let rec sexpr_of_cmd_list_iter cmd_list i str_ac = match cmd_list with
	| [] -> str_ac
	| cmd :: rest -> 
		let str_cmd = sexpr_of_cmd cmd tabs i line_numbers in 
		sexpr_of_cmd_list_iter rest (i + 1) (str_ac ^ str_cmd ^ "\n") in 
	sexpr_of_cmd_list_iter cmd_list 0 ""

(*
  (procedure xpto (arg1 arg2 ...) 
		(body ...) 
		('return ret_var ret_label) 
		('error err_var err_label))
*)
let sexpr_of_procedure proc line_numbers =			
	Printf.sprintf "(procedure \"%s\" \n\t(args%s) \n\t(body \n %s \n\t) \n\t(return %s %s) \n\t(error %s %s) \n )" 
  	proc.proc_name 
   	(sexpr_of_params proc.proc_params) 
		(sexpr_of_cmd_list proc.proc_body 2 line_numbers)
		proc.ret_var
		(string_of_int proc.ret_label)
		proc.error_var
		(string_of_int proc.error_label)
