open Z3
open JSIL_Syntax

type smt_translation_ctx = {
	z3_ctx            : context;
	tr_typing_env     : JSIL_Memory_Model.typing_environment; 
	tr_typeof_fun     : FuncDecl.func_decl;
  tr_list_sort      : Sort.sort; 
  tr_list_nil       : FuncDecl.func_decl;
	tr_list_is_nil    : FuncDecl.func_decl;  
	tr_list_cons      : FuncDecl.func_decl;
	tr_list_is_cons   : FuncDecl.func_decl;  
	tr_list_head      : FuncDecl.func_decl; 
	tr_list_tail      : FuncDecl.func_decl; 
	(* tr_existentials   : string list *)
}


let mk_smt_translation_ctx gamma existentials = 
	let cfg = [("model", "true"); ("proof", "false")] in
	let ctx = (mk_context cfg) in

	let z3_typeof_fun_name = (Symbol.mk_string ctx "typeof") in
	let z3_typeof_fun_domain = [ Arithmetic.Integer.mk_sort ctx ] in
	let z3_typeof_fun = FuncDecl.mk_func_decl ctx z3_typeof_fun_name z3_typeof_fun_domain (Arithmetic.Integer.mk_sort ctx) in 
	
	let z3_list_sort_name = (Symbol.mk_string ctx "tr_list") in
	let list_sort = Z3List.mk_sort ctx z3_list_sort_name (Arithmetic.Integer.mk_sort ctx) in 
	
	let list_nil     = Z3List.get_nil_decl     list_sort in 
	let list_is_nil  = Z3List.get_is_nil_decl  list_sort in 
	let list_cons    = Z3List.get_cons_decl    list_sort in 
	let list_is_cons = Z3List.get_is_cons_decl list_sort in 
	let list_head    = Z3List.get_head_decl    list_sort in 
	let list_tail    = Z3List.get_tail_decl    list_sort in 
	
	{
		z3_ctx            = ctx;
		tr_typing_env     = gamma; 
		tr_typeof_fun     = z3_typeof_fun;
  	tr_list_sort      = list_sort; 
 		tr_list_nil       = list_nil; 
		tr_list_is_nil    = list_is_nil;
		tr_list_cons      = list_cons;
		tr_list_is_cons   = list_is_cons;  
		tr_list_head      = list_head; 
		tr_list_tail      = list_tail;
		(* tr_existentials   = existentials *)
	}


let mk_z3_list les tr_ctx = 
	let empty_list = Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_list_nil [ ] in
	let rec loop les cur_list = 
		match les with 
		| [] -> cur_list 
		| le :: rest_les -> 
			let new_cur_list = Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_list_cons [ le; cur_list ] in
			loop rest_les new_cur_list in 
	loop les empty_list
	


(** Encode JSIL type literals as Z3 numerical constants *)
let encode_type ctx jsil_type =
	match jsil_type with
	| UndefinedType         -> Arithmetic.Integer.mk_numeral_i ctx 0
	| NullType              -> Arithmetic.Integer.mk_numeral_i ctx 1
	| EmptyType             -> Arithmetic.Integer.mk_numeral_i ctx 2
	| NoneType              -> Arithmetic.Integer.mk_numeral_i ctx 3
  | BooleanType           -> Arithmetic.Integer.mk_numeral_i ctx 4
	| IntType               -> Arithmetic.Integer.mk_numeral_i ctx 5
  | NumberType            -> Arithmetic.Integer.mk_numeral_i ctx 6
	| StringType            -> Arithmetic.Integer.mk_numeral_i ctx 7
  | ObjectType            -> Arithmetic.Integer.mk_numeral_i ctx 8
	| ReferenceType         -> Arithmetic.Integer.mk_numeral_i ctx 9
	| ObjectReferenceType   -> Arithmetic.Integer.mk_numeral_i ctx 10
	| VariableReferenceType -> Arithmetic.Integer.mk_numeral_i ctx 11
	| ListType              -> Arithmetic.Integer.mk_numeral_i ctx 12
	| TypeType              -> Arithmetic.Integer.mk_numeral_i ctx 13


let types_encoded_as_ints = [
	UndefinedType; 
	NullType; 
	EmptyType; 
	NoneType; 
	BooleanType; 
	IntType; 
	StringType; 
	ObjectType; 
	TypeType
]


(** Encode JSIL constants as Z3 numerical constants *)
let encode_constant ctx constant =
	let value =
		(match JSIL_Interpreter.evaluate_constant constant with
		| Num v -> v
		| _     -> raise (Failure "SMT encoding: Unknown constant")) in
	(Arithmetic.Real.mk_numeral_s ctx (string_of_float value)), (encode_type ctx NumberType)

(** Encode strings as Z3 numerical constants *)
let str_codes = Hashtbl.create 1000
let str_counter = ref 0
let encode_string ctx str =
	(* Printf.printf "I am going to encode a string\n"; *)
	try 
		let str_number = Hashtbl.find str_codes str in 
		(* Printf.printf "the string is already there!"; *)
		let z3_code = Arithmetic.Integer.mk_numeral_i ctx str_number in 
		z3_code
	with Not_found ->
		(* New string: add it to the hashtable *)
		let z3_code = Arithmetic.Integer.mk_numeral_i ctx !str_counter in
		Hashtbl.add str_codes str (!str_counter);
		str_counter := !str_counter + 1;
		z3_code

(** Encode JSIL literals as Z3 numerical constants *)
let rec encode_literal tr_ctx lit =
	let f = encode_literal tr_ctx in 
	let ctx = tr_ctx.z3_ctx in 
	let gamma = tr_ctx.tr_typing_env in
	match lit with
	| Undefined     -> (Arithmetic.Integer.mk_numeral_i ctx 0), (encode_type ctx UndefinedType)
	| Null          -> (Arithmetic.Integer.mk_numeral_i ctx 1), (encode_type ctx NullType)
	| Empty         -> (Arithmetic.Integer.mk_numeral_i ctx 2), (encode_type ctx EmptyType)
	| Constant c    -> encode_constant ctx c
	| Bool b        ->
		(match b with
		| true        -> (Arithmetic.Integer.mk_numeral_i ctx 0), (encode_type ctx BooleanType)
		| false       -> (Arithmetic.Integer.mk_numeral_i ctx 1), (encode_type ctx BooleanType))
	| Integer i     -> (Arithmetic.Integer.mk_numeral_i ctx i), (encode_type ctx IntType)
	| Num n         ->
		if (n = (snd (modf n)))
			then        (Arithmetic.Integer.mk_numeral_i ctx (int_of_float n)), (encode_type ctx IntType)
			else        (Arithmetic.Real.mk_numeral_s ctx (string_of_float n)), (encode_type ctx NumberType)
	| String s      -> (encode_string ctx s), (encode_type ctx StringType)
	| Loc l         -> (encode_string ctx ("$l" ^ l)), (encode_type ctx ObjectType)
	| Type t        -> (encode_type ctx t), (encode_type ctx TypeType)
	| LList lits -> 
		let les_tes = List.map f lits in
		let les, tes = 
			List.fold_left
				(fun (les, tes) (le, te) -> (le :: les, te :: tes))
				([], [])
				les_tes in   
		let le_list = mk_z3_list les tr_ctx in 
		le_list,  (encode_type ctx ListType)
		 						  
	| _             -> raise (Failure "SMT encoding: Construct not supported yet - literal!")

(** Encode JSIL binary operators *)
let encode_binop tr_ctx op le1 le2 =
	let ctx = tr_ctx.z3_ctx in 
	match op with
	| Plus          -> (Arithmetic.mk_add ctx [ le1; le2 ])
	| Minus         -> (Arithmetic.mk_sub ctx [ le1; le2 ])
	| Times         -> (Arithmetic.mk_mul ctx [ le1; le2 ])
	| Div           -> (Arithmetic.mk_div ctx le1 le2)
	| Mod           -> (Arithmetic.Integer.mk_mod ctx le1 le2)
	| LstCons       -> 
		(* Printf.printf "I am going to BURST\nBURST. le1: %s. le2: %s. \n" (Expr.to_string le1) (Expr.to_string le2); *)
		(Expr.mk_app tr_ctx.z3_ctx tr_ctx.tr_list_cons [ le1; le2 ]) 
	| _     -> 
		let msg = Printf.sprintf "SMT encoding: Construct not supported yet - binop - %s!" (JSIL_Print.string_of_binop op) in 
		raise (Failure msg)

(** Encode JSIL unary operators *)
let encode_unop ctx op le = 
	match op with 
	| UnaryMinus -> (Arithmetic.mk_unary_minus ctx le)
	| _          -> 
		let msg = Printf.sprintf "SMT encoding: Construct not supported yet - unop - %s!" (JSIL_Print.string_of_unop op) in 
		raise (Failure msg)
		
let get_z3_var_symbol tr_ctx var = Symbol.mk_string (tr_ctx.z3_ctx) var
		
	
let get_z3_var_and_type tr_ctx var = 
	let ctx = tr_ctx.z3_ctx in 
	let gamma = tr_ctx.tr_typing_env in 
	let var_type = JSIL_Memory_Model.gamma_get_type gamma var in 
	let le, te = 
		(match var_type with 
		  | None            -> 
				                   let le = (Arithmetic.Integer.mk_const ctx (Symbol.mk_string ctx var)) in 
		    								   le, (Expr.mk_app ctx tr_ctx.tr_typeof_fun [ le ])
		  | Some t when (List.mem t types_encoded_as_ints)  
			                  -> (Arithmetic.Integer.mk_const ctx (Symbol.mk_string ctx var)),       (encode_type ctx t)  
			| Some ListType   -> (Expr.mk_const ctx (Symbol.mk_string ctx var) tr_ctx.tr_list_sort), (encode_type ctx ListType) 
			| Some NumberType -> (Arithmetic.Real.mk_const ctx (Symbol.mk_string ctx var)),          (encode_type ctx NumberType) 
			| _               -> raise (Failure "z3 variable encoding: fatal error")) in
	le, te 


(** Encode JSIL logical expressions *)
let rec encode_logical_expression tr_ctx e =
	let ele = encode_logical_expression tr_ctx in
	let ctx = tr_ctx.z3_ctx in 
	let gamma = tr_ctx.tr_typing_env in 
	
	(match e with
	| LLit lit              -> 
		let le, te = encode_literal tr_ctx lit in 
		le, te, []
	
	| LNone                 -> 
		let le, te = (Arithmetic.Integer.mk_numeral_i ctx 3), (encode_type ctx NoneType) in
		le, te, []
	
	| LVar var
	| ALoc var              -> 
		let le, te = get_z3_var_and_type tr_ctx var in 
		le, te, []
		
	| PVar _                -> raise (Failure "Program variable in pure formula: FIRE")
	
	| LBinOp (le1, op, le2) -> 
		let le1, te1, as1 = ele le1 in 
		let le2, te2, as2 = ele le2 in
		let le = encode_binop tr_ctx op le1 le2 in 
		let as_op = Boolean.mk_eq ctx te1 te2 in 
		le, te1, (as_op :: (as1 @ as2))
		
	| LUnOp (op, le)        -> 
		let le, te, as1 = ele le in 
		let le = encode_unop ctx op le in 
		le, te, as1
	
	| LEList les            -> 
		let les_tes_as = List.map ele les in
		let les, tes, assertions = 
			List.fold_left
				(fun (les, tes, ac_assertions) (le, te, le_assertions) -> (le :: les, te :: tes, le_assertions @ ac_assertions))
				([], [], [])
				les_tes_as in   
		let le_list = mk_z3_list les tr_ctx in 
		le_list,  (encode_type ctx ListType), assertions
						
	| _                     -> raise (Failure "Failure - z3 encoding: Unsupported logical expression"))


let rec encode_pure_formula tr_ctx a =
	let f = encode_pure_formula tr_ctx in
	let fe = encode_logical_expression tr_ctx in
	let ctx = tr_ctx.z3_ctx in 
	let gamma = tr_ctx.tr_typing_env in 
	match a with
	| LNot a             -> Boolean.mk_not ctx (f a)
	
	| LEq (le1, le2)     ->
		let t1, _ = JSIL_Logic_Normalise.normalised_is_typable gamma le1 in 
		let t2, _ = JSIL_Logic_Normalise.normalised_is_typable gamma le2 in
		let le1, te1, as1 = fe le1 in 
		let le2, te2, as2 = fe le2 in
		(match t1, t2 with 
		| Some t1, Some t2 ->
			if (t1 = t2)  
				then Boolean.mk_eq ctx le2 le1
				else Boolean.mk_false ctx
					
		| _, _ ->
		  (* Printf.printf "I AM THERE!!!!!. gamma: %s\n" (JSIL_Memory_Print.string_of_gamma gamma);
			Printf.printf "Type hazard. le1: %s. le2: %s\n" (Expr.to_string le1) (Expr.to_string le2); *)
			let cur_as1 = Boolean.mk_eq ctx le1 le2 in 
			let cur_as2 = Boolean.mk_eq ctx te1 te2 in 
			Boolean.mk_and ctx ([ cur_as1; cur_as2 ] @ as1 @ as2))
	
	| LLess (le1', le2')   -> 
		let t1, _ = JSIL_Logic_Normalise.normalised_is_typable gamma le1' in 
		let t2, _ = JSIL_Logic_Normalise.normalised_is_typable gamma le2' in
		let le1, te1, as1 = fe le1' in 
		let le2, te2, as2 = fe le2' in 
		(match t1, t2 with 
		| Some t1, Some t2 -> 
			let t = types_lub t1 t2 in 
			(match t with 
			| Some IntType
			| Some NumberType -> Arithmetic.mk_lt ctx le1 le2
			| _ -> raise (Failure "Arithmetic operation invoked on non-numeric types"))
    | _, _ -> 
			(Printf.printf "LLess Error: %s %s. gamma: %s\n" 
				(JSIL_Print.string_of_logic_expression le1' false) 
				(JSIL_Print.string_of_logic_expression le2' false) 
				(JSIL_Memory_Print.string_of_gamma gamma); 
			raise (Failure "Death.")))
	
	| LLessEq (le1, le2) -> 
		let le1, te1, as1 = fe le1 in 
		let le2, te2, as2 = fe le2 in 
		Arithmetic.mk_le ctx le1 le2
		
	| LStrLess (_, _)    -> raise (Failure ("I don't know how to do string comparison in Z3"))

	| LTrue              -> Boolean.mk_true ctx
	
	| LFalse             -> Boolean.mk_false ctx

	| _                  -> 
		let msg = Printf.sprintf "Unsupported assertion to encode for Z3: %s" (JSIL_Print.string_of_logic_assertion a false) in 
		raise (Failure msg)


let check_satisfiability assertions gamma existentials = 
	let tr_ctx = mk_smt_translation_ctx gamma existentials in 	
	let assertions = 
		List.map 
			(fun a -> 
				(* Printf.printf "I am about to check the satisfiablity of: %s\n" (JSIL_Print.string_of_logic_assertion a false); *)
				let a = encode_pure_formula tr_ctx a in 
				(* Printf.printf "Z3 Expression: %s\n" (Expr.to_string a); *)
				a)
			assertions in 
	let solver = (Solver.mk_solver tr_ctx.z3_ctx None) in
	Solver.add solver assertions;
	let ret = (Solver.check solver []) = Solver.SATISFIABLE in 
	Gc.full_major (); 
	Solver.reset solver;
	(* Printf.printf "Check_satisfiability. Result %b" ret; *)
	ret


let get_sort tr_ctx var_type = 
	let ctx = tr_ctx.z3_ctx in 
	match var_type with 
	| None                                           -> Arithmetic.Integer.mk_sort ctx                                    
	| Some t when (List.mem t types_encoded_as_ints) -> Arithmetic.Integer.mk_sort ctx
	| Some NumberType                                -> Arithmetic.Real.mk_sort ctx 
	| Some ListType                                  -> tr_ctx.tr_list_sort
	| _  -> raise (Failure "Z3 encoding: Unsupported type.")


let get_sorts tr_ctx vars = 
	let gamma = tr_ctx.tr_typing_env in 
	List.map (fun x -> let var_type = JSIL_Memory_Model.gamma_get_type gamma x in get_sort tr_ctx var_type) vars

let get_z3_vars tr_ctx vars =
	List.map (fun x -> get_z3_var_symbol tr_ctx x) vars
	

let encode_quantifier tr_ctx quantified_vars assertion = 
	if ((List.length quantified_vars) > 0) then 
		(let quantified_assertion = 
			let sorts = get_sorts tr_ctx quantified_vars in
			let ctx = tr_ctx.z3_ctx in
			Quantifier.mk_quantifier 
				ctx
				true
				(List.map2 (fun v s -> Expr.mk_const_s ctx v s) quantified_vars sorts)
				assertion
				None 
				[]
				[]
				None 
				None in 
		let quantifier_str = Quantifier.to_string quantified_assertion in 
		let quantified_assertion = Quantifier.expr_of_quantifier quantified_assertion in
		let quantified_assertion = Expr.simplify quantified_assertion None in
		quantified_assertion)
	else assertion	

	
let get_solver tr_ctx existentials left_as right_as_or = 
	Printf.printf "----- Creating the solver -----\n\n";
	if ((List.length existentials) > 0) 
		then ( 
			Printf.printf "There are existentials.\n\n";
			Printf.printf "Left ass:\n";
			List.iter (fun x -> Printf.printf "\n%s\n" (Expr.to_string x)) left_as;
			Printf.printf "\nRight ass:\n";
			Printf.printf "\n%s\n\n" (Expr.to_string right_as_or);
						
			let target_assertion = 
				(if ((List.length left_as) > 0) 
					then Boolean.mk_and tr_ctx.z3_ctx (left_as @ [ right_as_or ])
					else right_as_or) in 
			let target_assertion = encode_quantifier tr_ctx existentials target_assertion in
			
			Printf.printf "The assertion to check is:\n";
			Printf.printf "\n%s\n\n" (Expr.to_string target_assertion);
			
			let solver = (Solver.mk_solver tr_ctx.z3_ctx None) in
			Solver.add solver [ target_assertion ];
			solver)
		else (
			Printf.printf "There are no existentials.\n";
			let solver = (Solver.mk_solver tr_ctx.z3_ctx None) in
			Solver.add solver (left_as @ [ right_as_or ]); 
			solver)
	


(* right_as must be satisfiable *)
let check_entailment existentials left_as right_as gamma =
	Printf.printf "------------------------------\n    Entering entailment\n\n";
	let cfg = [("model", "true"); ("proof", "false")] in
	
	let tr_ctx = mk_smt_translation_ctx gamma existentials in 
	let ctx = tr_ctx.z3_ctx in
	
	
	let ret_right = check_satisfiability right_as gamma existentials in 
	if (not (ret_right)) then false 
	else 	
		begin 
	
		(* check if left_as => right_as *)
		let right_as = List.map 
				(fun a -> 
					(* Printf.printf "I am about to encode a pure formula inside the check_entailment: %s\n" (JSIL_Print.string_of_logic_assertion a false); *)
					let a = encode_pure_formula tr_ctx a in
					(* Printf.printf "Z3 Expression: %s\n" (Expr.to_string a); 
					Printf.printf "I encoded a pure formula successfully\n"; *)
					Boolean.mk_not ctx a)
				right_as in 
		let right_as_or = 
			if ((List.length right_as) > 1) then 
					(Boolean.mk_or ctx right_as) 
				else if ((List.length right_as) = 1) then
					(List.nth right_as 0) 
				else Boolean.mk_false ctx in 
		
		let left_as = 
			List.map 
				(fun a -> encode_pure_formula tr_ctx a)
				left_as in 
		 Printf.printf "The thingies prior to existentials are:\n";
		 List.iter
			(fun expr -> Printf.printf "\n%s\n" (Expr.to_string expr))
			(left_as @ [ right_as_or ]); 
		 Printf.printf "\nDone printing\n";
		
		Printf.printf "\nThe existentials are: ";
		List.iter (fun x -> Printf.printf "%s " x) existentials;
		Printf.printf "\n\n";
		
		(* SOMETHING HAPPENS HERE! *)
		let solver = get_solver tr_ctx existentials left_as right_as_or in 
	
		let ret = (Solver.check solver []) != Solver.SATISFIABLE in 
		
		if (not ret) then 
			begin
				let model = Solver.get_model solver in 
		(match model with 
			| Some model -> 
				let str_model = Model.to_string model in 
				Printf.printf "I found the model: \n\n%s\n\n" str_model
			| None -> 
				Printf.printf "No model filha\n");
		(* Printf.printf "ret: %s\n" (string_of_bool ret); *)
		end;
		Gc.full_major (); 
		Solver.reset solver; 
		Printf.printf "Check_entailment. Result %b\n" ret; 
		Printf.printf "\n    Exiting entailment\n------------------------------\n\n";
		ret
		end 