open Pulp_Syntax
open Pulp_Procedure

(***
 Translating jsil to sjsil 
*)


let jsil_to_sjsil_bop bop = 
	match bop with 
	| Comparison cop ->
		(match cop with
		| Equal -> SSyntax.Equal
		| LessThan -> SSyntax.LessThan
		| LessThanEqual -> SSyntax.LessThanEqual)
	| Arith aop ->
		(match aop with 
		| Plus -> SSyntax.Plus
		| Minus -> SSyntax.Minus
		| Times -> SSyntax.Times
		| Div -> SSyntax.Div
		| Mod -> SSyntax.Mod)
	| Subtype -> SSyntax.Subtype
	| Concat -> SSyntax.Concat
	| Boolean bop -> 
		(match bop with 
		| And -> SSyntax.And
		| Or -> SSyntax.Or)
	| Bitwise biop ->
		(match biop with 
		| BitwiseAnd -> SSyntax.BitwiseAnd
		| BitwiseOr -> SSyntax.BitwiseOr
		| BitwiseXor -> SSyntax.BitwiseXor
		| LeftShift -> SSyntax.LeftShift
		| SignedRightShift -> SSyntax.SignedRightShift
		| UnsignedRightShift -> SSyntax.UnsignedRightShift)

let jsil_to_sjsil_uop uop = 
	match uop with 
	| Not -> SSyntax.Not
  | Negative -> SSyntax.Negative
  | ToStringOp -> SSyntax.ToStringOp
  | ToNumberOp -> SSyntax.ToNumberOp
  | ToInt32Op -> SSyntax.ToInt32Op
  | ToUint32Op -> SSyntax.ToUint32Op
  | BitwiseNot -> SSyntax.BitwiseNot

let jsil_to_sjsil_type t = 
	match t with
	| NullType -> SSyntax.NullType
	| UndefinedType -> SSyntax.UndefinedType
	| BooleanType -> SSyntax.BooleanType
	| StringType -> SSyntax.StringType
	| NumberType -> SSyntax.NumberType
	| ObjectType obj_option ->
		(match obj_option with 
		| None -> SSyntax.ObjectType
		| Some option ->
			(match option with 
			| Normal -> SSyntax.ObjectType 
			| Builtin -> raise(Failure "Builtin type literals need to be translated inside the context in which they appear")))
	| ReferenceType ref_type_option ->
		(match ref_type_option with 
		| None -> SSyntax.ReferenceType
		| Some option -> 
			(match option with 
			| MemberReference -> SSyntax.ObjectReferenceType
			| VariableReference -> SSyntax.VariableReferenceType))

let jsil_to_sjsil_builtin_loc l =
	let prefix = "$"  in
  let loc_str = match l with
    | Lg -> "lg"
    | Lg_isNaN -> "lg_isNan"
    | Lg_isFinite -> "lg_isFinite"
    | Lop -> "lop"
    | Lop_toString -> "lop_toString"
    | Lop_valueOf -> "lop_valueOf"
    | Lop_isPrototypeOf -> "lop_isPrototypeOf"
    | LFunction -> "lfunction"
    | Lfp -> "lfp"
    | LEval -> "leval"
    | LError -> "lerror"
    | Lep -> "lep"
    | LRError -> "lrerror"
    | Lrep -> "lrep"
    | LTError -> "lterror"
    | Ltep -> "ltep"
    | LSError -> "lserror"
    | Lsep -> "lsep"
    | LEvalError -> "levalerror"
    | LEvalErrorP -> "levalerrorp"
    | LRangeError -> "lrangeerror"
    | LRangeErrorP -> "lrangeerrorp"
    | LURIError -> "lurierror"
    | LURIErrorP -> "lurierrorp"
    | LObject -> "lobject"
    | LObjectGetPrototypeOf -> "lobject_get_prototype_of"
    | LBoolean -> "lboolean"
    | Lbp -> "lbp"
    | Lbp_toString -> "lbp_toString"
    | Lbp_valueOf -> "lbp_valueOf"
    | LNumber -> "lnumber"
    | Lnp -> "lnp"
    | Lnp_toString -> "lnp_toString"
    | Lnp_valueOf -> "lnp_valueOf"
    | LMath -> "lmath"
    | LString -> "lstring"
    | Lsp -> "lsp"
    | Lsp_toString -> "lsp_toString"
    | Lsp_valueOf -> "lsp_valueOf"
    | LJSON -> "ljson"
    | LNotImplemented f -> "lnotimplemented_" ^ (Pulp_Syntax_Print.string_of_feature f)
    | LStub s -> "lstub" ^ s in 
		prefix ^ loc_str

let jsil_to_sjsil_lit lit = 
	match lit with 
	| LLoc bloc -> SSyntax.Loc (jsil_to_sjsil_builtin_loc bloc) 
	| Null -> SSyntax.Null
	| Bool b -> SSyntax.Bool b
	| Num n -> SSyntax.Num n
	| String s -> SSyntax.String s
	| Undefined -> SSyntax.Undefined
	| Type t -> SSyntax.Type (jsil_to_sjsil_type t)
	| Empty -> SSyntax.Empty


let rec jsil_to_sjsil_expr e var_gen var_table =
	match e with 
	(* Literal *)
	| Literal lit -> SSyntax.Literal (jsil_to_sjsil_lit lit), []
	
	(* Variable *)
	| Var x -> 
		let new_var = try 
			Hashtbl.find var_table x
		with Failure _ -> 
			Printf.printf "Variable %s not found in the variable table.\n" x; exit 2
		in 
		(SSyntax.Var new_var), []
	
	(* Binop *) 
	| BinOp (e1, bop, e2) when ((bop = (Comparison Equal)) && (e2 = Literal(Type (ObjectType(Some Builtin))))) ->
		(match e1 with 
		| TypeOf e_aux ->
			let jsil_aux, cmds_aux = (jsil_to_sjsil_expr e_aux var_gen var_table) in 
			let new_var = var_gen () in 
			let new_cmd = (SSyntax.SBasic 
				(SSyntax.SHasField (new_var, jsil_aux, 
					SSyntax.Literal(SSyntax.String "#user_defined_function")))) in 
			SSyntax.BinOp (SSyntax.Var new_var, SSyntax.Equal, SSyntax.Literal (SSyntax.Bool false)), cmds_aux @ [ new_cmd ]
		| _ -> raise (Failure "Illegal Expression containing the type Builtin Object"))
			  		
	| BinOp (e1, bop, e2) -> 
		let jsil_e1, cmds1 = jsil_to_sjsil_expr e1 var_gen var_table in 
		let jsil_e2, cmds2 = jsil_to_sjsil_expr e2 var_gen var_table in	
		SSyntax.BinOp (jsil_e1, (jsil_to_sjsil_bop bop), jsil_e2), cmds1 @ cmds2
	
	(* Unop *)
	| UnaryOp (uop, e) -> 
		let jsil_e, cmds = jsil_to_sjsil_expr e var_gen var_table in
		SSyntax.UnaryOp ((jsil_to_sjsil_uop uop), jsil_e), cmds
	
	(* Reference constructors *)
	| Ref (e1, e2, r_type) ->
		let jsil_e1, cmds1 = jsil_to_sjsil_expr e1 var_gen var_table in 
		let jsil_e2, cmds2 = jsil_to_sjsil_expr e2 var_gen var_table in	
		(match r_type with 
		| MemberReference -> SSyntax.ORef (jsil_e1, jsil_e2), cmds1 @ cmds2
		| VariableReference -> SSyntax.VRef (jsil_e1, jsil_e2), cmds1 @ cmds2)
	
	(* Base *)		
	| Base e -> 
		let jsil_e, cmds = jsil_to_sjsil_expr e var_gen var_table in
		(SSyntax.Base jsil_e), cmds
	
	(* Field *)		
	| Field e -> 
		let jsil_e, cmds = jsil_to_sjsil_expr e var_gen var_table in
		(SSyntax.Field jsil_e), cmds
	
	(* TypeOf *)		
	| TypeOf e -> 
		let jsil_e, cmds = jsil_to_sjsil_expr e var_gen var_table in
		(SSyntax.TypeOf jsil_e), cmds

				
let jsil_to_sjsil jsil_cmds var_table var_gen (label_to_number : string -> int) ret_label ex_label =  
	
	(* translate calls *) 
	let translate_call var call = 
		let call_name_e, cmds_e = jsil_to_sjsil_expr call.call_name var_gen var_table in 
		let this_e, cmds_this = jsil_to_sjsil_expr call.call_this var_gen var_table in
		let scope_e, cmds_scope = jsil_to_sjsil_expr call.call_scope var_gen var_table in
		let arg_exps_cmds = List.map (fun expr -> jsil_to_sjsil_expr expr var_gen var_table) call.call_args in 
		let arg_exps = List.map (fun (exp,cmds) -> exp) arg_exps_cmds in 
		let arg_cmds = List.fold_left (fun ac_cmds (exp, cmds) -> ac_cmds @ cmds) [] arg_exps_cmds in 
		cmds_e @ cmds_this @ cmds_scope @ arg_cmds @
		[ SSyntax.SCall (var, call_name_e, [this_e; scope_e] @ arg_exps, Some (label_to_number call.call_throw_label)) ] in 

	let translate_eval_call var call = 
		let arg_exps_cmds = List.map (fun expr -> jsil_to_sjsil_expr expr var_gen var_table) call.call_args in 
		let arg_exps = List.map (fun (exp,cmds) -> exp) arg_exps_cmds in 
		let arg_cmds = List.fold_left (fun ac_cmds (exp, cmds) -> ac_cmds @ cmds) [] arg_exps_cmds in
		arg_cmds @
		[ SSyntax.SCall (var, SSyntax.Literal (SSyntax.String "eval"), arg_exps, Some (label_to_number call.call_throw_label)) ] in 
		
	(**
	 * jsil_cmds -> jsil cmds to compile
	 * sjsil_cmds_so_far -> sjsil cmds resulting from the compilation of previous jsil cmds
	 * number_of_new_cmds -> number of additional cmds added by the translation 
	 * cur_number -> index of the next command to be compiled
	 * cmd_shifts -> a map from command indexes to the number extra commands that will appear before the compilation of that command
   *)
	let rec jsil_to_sjsil_iter jsil_cmds sjil_cmds_so_far number_of_new_cmds cur_number cmd_shifts = 
		
		let jsil_cmds = Pulp_Translate_Aux.to_ivl_goto jsil_cmds in
		match jsil_cmds with 
		| [] -> sjil_cmds_so_far
		| jsil_cmd :: rest_jsil_cmds ->
			
			(* Printf.printf "Translating the command number %s whose code is: %s.\n" 
				(string_of_int cur_number) 
				(Pulp_Syntax_Print.string_of_statement jsil_cmd);	*)
			
			(match jsil_cmd.stmt_stx with 
			
			(* Sugar *)
			| Sugar sugar_cmd ->
				(match sugar_cmd with 
				| SpecFunction (var, sf, l) ->
					let new_number = cur_number + 1 in 
					let jsil_var = SSyntax_Aux.try_find var_table var in 
					let jsil_var = match jsil_var with 
						| Some var_x -> 
							(* Printf.printf "Translating an assignment to var: %s. Found in var table and paired up with %s.\n" 
								var var_x; *)
							var_x
						| None -> 
							(let new_var = var_gen () in 
							Hashtbl.add var_table var new_var; 
							(* Printf.printf "Translating an assignment to var: %s. Not found in the var table and paired up with %s.\n" 
								var new_var; *)
							new_var) in 
					let args = SSyntax_Aux.spec_function_get_args sf in 
					let arg_exps_cmds = List.map (fun expr -> jsil_to_sjsil_expr expr var_gen var_table) args in 
					let arg_exps = List.map (fun (exp,cmds) -> exp) arg_exps_cmds in 
					let arg_cmds = List.fold_left (fun ac_cmds (exp, cmds) -> ac_cmds @ cmds) [] arg_exps_cmds in
					let sjsil_cmd = (SSyntax.SCall (jsil_var, (SSyntax.Literal (SSyntax.String (Pulp_Syntax_Print.string_of_spec_fun_id sf))), arg_exps, Some (label_to_number l))) in 
					let number_of_new_cmds = number_of_new_cmds + (List.length arg_cmds) in 
						cmd_shifts.(cur_number) <- number_of_new_cmds;
						jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ arg_cmds @ [ sjsil_cmd ]) number_of_new_cmds new_number cmd_shifts
				| _ -> raise (Failure "Unexpected Sugar construct"))
		
			(* Label - different from return and different from error *)
			| Label l when ((l != ret_label) && (l != ex_label)) -> 
				let new_number = cur_number in
				cmd_shifts.(cur_number) <- number_of_new_cmds;
				jsil_to_sjsil_iter rest_jsil_cmds sjil_cmds_so_far number_of_new_cmds new_number cmd_shifts
			
			(* return label or error label *)	
			| Label l -> 
				let new_number = cur_number + 1 in
				cmd_shifts.(cur_number) <- number_of_new_cmds;
				jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SSyntax.SBasic SSyntax.SSkip) ]) number_of_new_cmds new_number cmd_shifts
			
			(* Goto *)
			| Goto l ->
				let new_number = cur_number + 1 in 
				cmd_shifts.(cur_number) <- number_of_new_cmds; 
				let new_label : int = label_to_number l in 
				jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SSyntax.SGoto new_label) ]) number_of_new_cmds new_number cmd_shifts
			
			(* Guarded Goto *)
			| GuardedGoto (expr, l1, l2) -> 
				let new_number = cur_number + 1 in 
				let sjsil_expr, cmds_e = jsil_to_sjsil_expr expr var_gen var_table in 
				let number_of_new_cmds = number_of_new_cmds + (List.length cmds_e) in
				cmd_shifts.(cur_number) <- number_of_new_cmds;
				jsil_to_sjsil_iter rest_jsil_cmds 
					(sjil_cmds_so_far @ cmds_e @ [ (SSyntax.SGuardedGoto (sjsil_expr, (label_to_number l1), (label_to_number l2))) ]) 
					number_of_new_cmds
					new_number
					cmd_shifts
			
			(* Skip *)
			| Basic (Skip) -> 
				let new_number = cur_number + 1 in 
				cmd_shifts.(cur_number) <- number_of_new_cmds;
				jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SSyntax.SBasic (SSyntax.SSkip)) ])	number_of_new_cmds new_number cmd_shifts
				
		  (* Field Assignment *)
			| Basic (Mutation mutation) -> 
				let new_number = cur_number + 1 in 
				let sjsil_loc_e, cmds_loc = jsil_to_sjsil_expr mutation.m_loc var_gen var_table in 
				let sjsil_field_e, cmds_field = jsil_to_sjsil_expr mutation.m_field var_gen var_table in 
				let sjsil_rhs_e, cmds_rhs = jsil_to_sjsil_expr mutation.m_right var_gen var_table in 
				let number_of_new_cmds = number_of_new_cmds + (List.length cmds_loc) + (List.length cmds_field) + (List.length cmds_rhs) in
				cmd_shifts.(cur_number) <- number_of_new_cmds;
				jsil_to_sjsil_iter rest_jsil_cmds 
					(sjil_cmds_so_far @ cmds_loc @ cmds_field @ cmds_rhs @ [ (SSyntax.SBasic (SSyntax.SMutation (sjsil_loc_e, sjsil_field_e, sjsil_rhs_e))) ])
					number_of_new_cmds
					new_number
					cmd_shifts
					
				(* Variable Assignment *)
			| Basic (Assignment ass) -> 
						let new_number = cur_number + 1 in 
						let var = ass.assign_left in
						let jsil_var = SSyntax_Aux.try_find var_table var in 
						
						let jsil_var = match jsil_var with 
						| Some var_x -> 
							(* Printf.printf "Translating an assignment to var: %s. Found in var table and paired up with %s.\n" 
								var var_x; *)
							var_x
						| None -> 
							(let new_var = var_gen () in 
							Hashtbl.add var_table var new_var; 
							(* Printf.printf "Translating an assignment to var: %s. Not found in the var table and paired up with %s.\n" 
								var new_var; *)
							new_var) in 
							
						(match ass.assign_right with 
						  (* Procedure Call*)
							| Call call
							| BuiltinCall call ->
								let call_cmds = translate_call jsil_var call in 
								let number_of_new_cmds = number_of_new_cmds + ((List.length call_cmds) - 1) in
								cmd_shifts.(cur_number) <- number_of_new_cmds;
								jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ call_cmds) number_of_new_cmds new_number cmd_shifts
								
							(* Eval *)				
							| Eval call -> 
								let eval_cmds = translate_eval_call jsil_var call in 
								let number_of_new_cmds = number_of_new_cmds + ((List.length eval_cmds) - 1) in
								cmd_shifts.(cur_number) <- number_of_new_cmds;
								jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ eval_cmds) number_of_new_cmds new_number cmd_shifts
								
							(* New *)	
							| Obj ->
								cmd_shifts.(cur_number) <- number_of_new_cmds;
								jsil_to_sjsil_iter rest_jsil_cmds (sjil_cmds_so_far @ [ (SSyntax.SBasic (SSyntax.SNew jsil_var)) ]) number_of_new_cmds new_number cmd_shifts
								
							(* Field Lookup *)					
							| Lookup (e1, e2) -> 
								let sjsil_e1, cmds_e1 = jsil_to_sjsil_expr e1 var_gen var_table in 
								let sjsil_e2, cmds_e2 = jsil_to_sjsil_expr e2 var_gen var_table in
								let number_of_new_cmds = number_of_new_cmds + (List.length cmds_e1) + (List.length cmds_e2) in
								cmd_shifts.(cur_number) <- number_of_new_cmds;
								jsil_to_sjsil_iter rest_jsil_cmds 
									(sjil_cmds_so_far @ cmds_e1 @ cmds_e2 @ [ (SSyntax.SBasic (SSyntax.SLookup (jsil_var, sjsil_e1, sjsil_e2))) ])
									number_of_new_cmds
									new_number
									cmd_shifts
									
							(* Delete *)				
							| Deallocation (e1, e2) -> 
								let sjsil_e1, cmds_e1 = jsil_to_sjsil_expr e1 var_gen var_table in 
								let sjsil_e2, cmds_e2 = jsil_to_sjsil_expr e2 var_gen var_table in 
								let number_of_new_cmds = number_of_new_cmds + (List.length cmds_e1) + (List.length cmds_e2) in
								cmd_shifts.(cur_number) <- number_of_new_cmds;
								jsil_to_sjsil_iter rest_jsil_cmds 
									(sjil_cmds_so_far @ cmds_e1 @ cmds_e2 @ 
										[ (SSyntax.SBasic (SSyntax.SDelete (sjsil_e1, sjsil_e2)));  
											(SSyntax.SBasic (SSyntax.SAssignment (jsil_var, (SSyntax.Literal (SSyntax.Bool true))))) ])
									number_of_new_cmds
									new_number
									cmd_shifts
									
							(* HasField *)					
							| HasField (e1, e2) -> 
								let sjsil_e1, cmds_e1 = jsil_to_sjsil_expr e1 var_gen var_table in 
								let sjsil_e2, cmds_e2 = jsil_to_sjsil_expr e2 var_gen var_table in 
								let number_of_new_cmds = number_of_new_cmds + (List.length cmds_e1) + (List.length cmds_e2) in 
								cmd_shifts.(cur_number) <- number_of_new_cmds;
								jsil_to_sjsil_iter rest_jsil_cmds 
									(sjil_cmds_so_far @ cmds_e1 @ cmds_e2 @ 
									[ (SSyntax.SBasic (SSyntax.SHasField (jsil_var, sjsil_e1, sjsil_e2))) ])
									number_of_new_cmds
									new_number
									cmd_shifts
									
							(* Simple Assignment *)					
							| Expression e1 -> 
								let sjsil_e1, cmds_e1 = jsil_to_sjsil_expr e1 var_gen var_table in 
								let number_of_new_cmds = number_of_new_cmds + (List.length cmds_e1) in
								cmd_shifts.(cur_number) <- number_of_new_cmds;
								jsil_to_sjsil_iter rest_jsil_cmds 
									(sjil_cmds_so_far @ cmds_e1 @ [ (SSyntax.SBasic (SSyntax.SAssignment (jsil_var, sjsil_e1))) ])
									number_of_new_cmds
									new_number
									cmd_shifts
									
							(* Proto Field *)					
							| ProtoF (e1, e2) -> 
								let sjsil_e1, cmds_e1 = jsil_to_sjsil_expr e1 var_gen var_table in 
								let sjsil_e2, cmds_e2 = jsil_to_sjsil_expr e2 var_gen var_table in 
								let number_of_new_cmds = number_of_new_cmds + (List.length cmds_e1) + (List.length cmds_e2) in
								cmd_shifts.(cur_number) <- number_of_new_cmds;
								jsil_to_sjsil_iter rest_jsil_cmds 
									(sjil_cmds_so_far @ cmds_e1 @ cmds_e2 @ [ (SSyntax.SBasic (SSyntax.SProtoField (jsil_var, sjsil_e1, sjsil_e2))) ])
									number_of_new_cmds
									new_number
									cmd_shifts
								
							(* Proto Obj *)															
							| ProtoO (e1, e2) -> 
								let sjsil_e1, cmds_e1 = jsil_to_sjsil_expr e1 var_gen var_table in 
								let sjsil_e2, cmds_e2 = jsil_to_sjsil_expr e2 var_gen var_table in 
								let number_of_new_cmds = number_of_new_cmds + (List.length cmds_e1) + (List.length cmds_e2) in 
								cmd_shifts.(cur_number) <- number_of_new_cmds;
								jsil_to_sjsil_iter rest_jsil_cmds 
									(sjil_cmds_so_far @ cmds_e1 @ cmds_e2 @ [ (SSyntax.SBasic (SSyntax.SProtoObj (jsil_var, sjsil_e1, sjsil_e2))) ])
									number_of_new_cmds
									new_number
									cmd_shifts
				))	in
	
	
	(* update the gotos according to the cmd_shifts *)
	let rec shift_cmds cmds cmds_shifted_so_far cmd_shifts = 
		match cmds with 
		| [] -> cmds_shifted_so_far 
		| cmd :: rest_cmds -> 
			match cmd with 
			| SSyntax.SGoto i -> 
				let shift_i = cmd_shifts.(i) in 
				let new_cmd = SSyntax.SGoto (i + shift_i) in 
				shift_cmds rest_cmds (cmds_shifted_so_far @ [ new_cmd ]) cmd_shifts
				
			| SSyntax.SGuardedGoto (e, i, j) ->
				let shift_i = cmd_shifts.(i) in 
				let shift_j = cmd_shifts.(j) in 
				let new_cmd = SSyntax.SGuardedGoto (e, (i + shift_i), (j + shift_j)) in 
				shift_cmds rest_cmds (cmds_shifted_so_far @ [ new_cmd ]) cmd_shifts		
					
			| x -> shift_cmds rest_cmds (cmds_shifted_so_far @ [ x ]) cmd_shifts in
													
	(* replace labels in gotos with respective numbers *)
	let cmd_shifts = Array.make (List.length jsil_cmds) 0 in 
	let sjsil_cmds = jsil_to_sjsil_iter jsil_cmds [] 0 0 cmd_shifts in 
	let sjsil_cmds = shift_cmds sjsil_cmds [] cmd_shifts in
  sjsil_cmds, cmd_shifts

let jsil_to_sjsil_proc jsil_proc = 
	
	(* Printf.printf "Translating procedure: %s.\n" jsil_proc.func_name; *)
	
	(* param generator and variable generator and table*)
	let param_gen = SSyntax_Aux.get_fresh_vars "arg_" in 
	let var_gen = SSyntax_Aux.get_fresh_vars "x_" in 
	let var_table = Hashtbl.create 80021 in
	
	(* register args - put the parms in the table*)
	let rec register_params table params new_params = 
		match params with 
		| [] -> new_params
		| param :: rest_params -> 
			let new_param = param_gen () in 
			Hashtbl.add var_table param new_param;
			register_params table rest_params (new_params @ [ new_param ]) in  
			
	let new_params = register_params var_table jsil_proc.func_params [] in 
	
	let ret_var = jsil_proc.func_ctx.return_var in 
	let ret_label = jsil_proc.func_ctx.label_return in 
	let ex_var = jsil_proc.func_ctx.throw_var in 
	let ex_label = jsil_proc.func_ctx.label_throw in 
				
	(* labels to numbers *)
	let label_to_number : string -> int = SSyntax_Aux.register_labels jsil_proc.func_body ret_label ex_label in
	
	(* translate the body of the procedure *)
	let sjsil_body, cmd_shifts = jsil_to_sjsil jsil_proc.func_body var_table var_gen label_to_number ret_label ex_label in
	
	(* return var and return label *)	
	let new_ret_var = SSyntax_Aux.try_find var_table ret_var in 
	let new_ret_var = 
		match new_ret_var with 
		| Some var_x -> var_x 
		| None ->
			(let new_var = var_gen () in 
			Hashtbl.add var_table ret_var new_var; 
			new_var) in 
			
	let new_ret_label = label_to_number ret_label in 
	let new_ret_label = new_ret_label + cmd_shifts.(new_ret_label)  in 
	
	(* ex var and ex label *)	
	let new_ex_var = SSyntax_Aux.try_find var_table ex_var in 
	let new_ex_var = 
		match new_ex_var with 
		| Some var_x -> var_x 
		| None ->
			(let new_var = var_gen () in 
			Hashtbl.add var_table ex_var new_var; 
			new_var) in 
			
	let new_ex_label = label_to_number ex_label in 
	let new_ex_label = new_ex_label + cmd_shifts.(new_ex_label)  in 
	
		{ 
    	SSyntax.proc_name = jsil_proc.func_name;
    	SSyntax.proc_body = Array.of_list (List.map (fun x -> (None, x)) sjsil_body);
    	SSyntax.proc_params = new_params; 
			SSyntax.ret_label = new_ret_label;
			SSyntax.ret_var = new_ret_var;
			SSyntax.error_label = Some new_ex_label;
			SSyntax.error_var = Some new_ex_var;
			SSyntax.spec = None;
		}

(* translating jsil to sjsil *)
let jsil_to_sjsil_prog jsil_prog = 
	let sjsil_prog = SSyntax.SProgram.create 80021 in
	Pulp_Procedure.AllFunctions.iter
	(fun key fb -> 
		let sfb = jsil_to_sjsil_proc fb in 
		SSyntax.SProgram.add sjsil_prog key sfb)
	jsil_prog; 
	sjsil_prog

let jsil_to_sjsil_loc jsil_loc = 
	match jsil_loc with
	|	Memory_Model.BLoc bl -> jsil_to_sjsil_builtin_loc bl
	| Memory_Model.Loc l -> "$l_" ^ (string_of_int l)  

let jsil_to_sjsil_heap_value hv = 
	match hv with 
	| Memory_Model.HVLiteral lit -> jsil_to_sjsil_lit lit 
	| Memory_Model.HVObj l -> SSyntax.Loc (jsil_to_sjsil_loc l)

let jsil_to_sjsil_heap jsil_heap = 
	let sjsil_heap = SSyntax.SHeap.create 8021 in
	Memory_Model.Heap.iter 
		(fun loc obj -> 
			let sjsil_loc = jsil_to_sjsil_loc loc in
			let new_obj = SSyntax.SHeap.create 1021 in
			Memory_Model.Object.iter
			(fun prop pval ->
				let sjsil_pval = jsil_to_sjsil_heap_value pval in 
				SSyntax.SHeap.add new_obj prop sjsil_pval) obj;
			SSyntax.SHeap.add sjsil_heap sjsil_loc new_obj)
		jsil_heap;
	sjsil_heap