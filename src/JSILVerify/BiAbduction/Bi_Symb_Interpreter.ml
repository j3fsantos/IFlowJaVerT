open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils

let js = ref false

let print_le = (fun x -> JSIL_Print.string_of_logic_expression x false)
let print_e = (fun x -> JSIL_Print.string_of_expression x false)

(**********************)
(* Symbolic Execution *)
(**********************)

(* List length, when possible *)
let rec get_list_length (le : jsil_logic_expr) : int option =
(match le with
	| LLit (LList list) -> Some (List.length list)
	| LEList list       -> Some (List.length list)
	| LBinOp (el, LstCons, llist) ->
		let len_llist = get_list_length llist in
		if_some len_llist (fun len -> Some (len + 1)) None
	| _ -> None)

(*******************************************)
(* Symbolic evaluation of JSIL expressions *)
(*******************************************)
let rec symb_evaluate_expr (symb_state: symbolic_state) (anti_frame: symbolic_state) (expr : jsil_expr) : jsil_logic_expr =
let heap, store, pure_formulae, gamma, _ = symb_state in
let anti_heap, anti_store, anti_pure_formulae, anti_gamma, _ = anti_frame in
let f = symb_evaluate_expr symb_state anti_frame in
	match expr with
	(* Literals: Return the literal *)
	| Literal lit -> LLit lit

  (* Variables: 
	     a) If a variable is already in the store, return the variable
			 b) Otherwise, add a fresh logical variable (of the appropriate type) to the store and then return it *)
	| Var x ->
		let x_val = store_get_safe store x in
		if_some_val_lazy x_val (lazy (let var = extend_abs_store x store gamma in 
									  store_put anti_store x var;
									  var))

  (* Binary operators:
	     a) if both operands evaluate to literals, execute the operator and return the result
	     b) otherwise, if the operator is equality and the types of the operands are not equal, return false
			 c) otherwise, return the lifted binary operator *)
	| BinOp (e1, op, e2) ->
		let nle1 = f e1 in
		let nle2 = f e2 in
		(match nle1, nle2 with
		| LLit l1, LLit l2 ->
			let l = JSIL_Interpreter.evaluate_binop op (Literal l1) (Literal l2) (Hashtbl.create 1) in
				LLit l
		| _, _ ->
			(match op with
			| Equal ->
				let t1, _, _ = JSIL_Logic_Utils.type_lexpr gamma nle1 in
				let t2, _, _ = JSIL_Logic_Utils.type_lexpr gamma nle2 in
					(match t1, t2 with
					| Some t1, Some t2 -> if (t1 = t2) then LBinOp (nle1, op, nle2) else (LLit (Bool false)) 
					| _, _             -> LBinOp (nle1, op, nle2))
			| _ -> LBinOp (nle1, op, nle2)))

  (* Unary operators
	     a) if the operand evaluates to a literal, execute the operator and return the result
			 b) otherwise, if the operator is Cdr, try to calculate the tail of the list and return it
			 c) otherwise, if the operator is LstLen, try to calculate the length of the list and return it
			 d) otherwise, return the lifted unary operator *)
	| UnOp (op, e) ->
		let nle = f e in
		(match nle with
 	 	| LLit lit -> 
			let l = JSIL_Interpreter.evaluate_unop op lit in
				LLit l
		| _ ->
			(match op with
			| Cdr ->
			let nle = Simplifications.find_me_Im_a_list store pure_formulae nle in
				(match nle with
				| LLit (LList list) ->
				 	(match list with
					 | [] -> raise (Failure "Cdr doesn't exist.")
					 | _ :: list -> LLit (LList list))
				 | LEList list ->
				 	(match list with
					 | [] -> raise (Failure "Cdr doesn't exist.")
					 | _ :: list -> LEList list)
				 | LBinOp (el, LstCons, llist) -> llist
				 | _ -> LUnOp (op, nle))
			| LstLen ->
			 	let nle = Simplifications.find_me_Im_a_list store pure_formulae nle in
				let len = get_list_length nle in
					if_some len (fun len -> LLit (Num (float_of_int len))) (LUnOp (op, nle))
			| _ -> LUnOp (op, nle)))

  (* TypeOf:
	     a) if the parameter is typable in the typing environment, return the type
			 b) otherwise, return the lifted typeOf *)
	| TypeOf (e) ->
		let nle = f e in
		let nle_type, _, _ = type_lexpr gamma nle in
		if_some nle_type (fun t -> LLit (Type t)) (LTypeOf (nle))

  (* List of expressions: Evaluate all elements and then
	     a) If all are literals, convert to a literal list
			 b) Otherwise, return the lifted list of logical expressions
  *)
	| EList es ->
		let les = List.map (fun e -> f e) es in
		let rec loop les lits =
			(match les with
			| [] -> true, lits
			| le :: rest ->
				(match le with
				| LLit l -> loop rest (l :: lits)
				| _ -> false, [])) in
		let all_literals, lits = loop les [] in
		if all_literals
			then 
				let lits = List.rev lits in
					LLit (LList lits)
			else LEList les

  (* List n-th: Evaluate the list and the index
	     a) Attempt to reduce fully, if possible, return the result
			 b) Otherwise, return the lifted list n-th
  *)
	| LstNth (e1, e2) ->
		let list = f e1 in
		let index = f e2 in
		let list = Simplifications.find_me_Im_a_list store pure_formulae list in
		(match index with
		 | LLit (Num n) when (Utils.is_int n) ->
			let n = int_of_float n in
		 	if (n < 0) then raise (Failure "List index negative.")
			else
			(match list with
				| LLit (LList list) ->
					(try (LLit (List.nth list n)) with _ ->
						raise (Failure "List index out of bounds"))
				| LEList list ->
					(try (List.nth list n) with _ ->
						raise (Failure "List index out of bounds"))
				| LBinOp (el, LstCons, llist) ->
		  			if (n = 0)
						then el
						else (match llist with
							  | LLit (LList list) -> (try (LLit (List.nth list (n - 1))) with _ ->
		  							raise (Failure "List index out of bounds"))
							  | LEList list -> (try (List.nth list (n - 1)) with _ ->
		  							raise (Failure "List index out of bounds"))
							  | _ -> LLstNth (list, index))
				| _ -> LLstNth (list, index))
			| LLit (Num n) -> raise (Failure "Non-integer list index.")
		| _ -> LLstNth (list, index))

  (* List n-th: Evaluate the string and the index
	     a) Attempt to reduce fully, if possible, return the result
			 b) Otherwise, return the lifted string n-th
  *)
	| StrNth (e1, e2) ->
		let str = f e1 in
		let index = f e2 in
		(match index with
		| LLit (Num n) when (Utils.is_int n) ->
			let n = int_of_float n in
		 	if (n < 0) then raise (Failure "String index negative.")
			else
				(match str with
				| LLit (String s) -> LLit (String (String.make 1 (String.get s n)))
				| _ -> LStrNth (str, index))
		| LLit (Num n) -> raise (Failure "Non-integer string index.")
		| _ -> LStrNth (str, index))

(*
	Common Pattern with bi-abduction rules: 
		Create an abritary location. 
		Associate the location with the given expression 
		(This expression 'should' have been a location)
		Generate an abritary value for the missing heap cell. 
*)
let create_new_location (expr: jsil_logic_expr) (symb_state : symbolic_state) (anti_frame : symbolic_state) : string * string = 
	let _, store, pfs, _, _ = symb_state in
	let _, anti_store, anti_pfs, _, _ = anti_frame in
	(* New location which 'expr' will be associated with *)
	let anything = fresh_lvar () in
	let new_loc = fresh_aloc () in
	let pf = (LEq ((ALoc new_loc), expr)) in
	add_pure_assertion pfs pf;
	add_pure_assertion anti_pfs pf;
	(new_loc, anything)

(************************************************)
(* SAFE Symbolic evaluation of JSIL expressions *)
(************************************************)
(* 
	a) If the result of the evaluation is typable, then any constraints produced by typing must also make sense
	b) Otherwise, variables are allowed to stay untyped
	c) Otherwise, an error is thrown 
*)
let rec safe_symb_evaluate_expr spec_lvars (symb_state: symbolic_state) (anti_frame : symbolic_state) (expr : jsil_expr) =
	let _, _, pure_formulae, gamma, _ = symb_state in
	let fail nle =
		let gamma_str = Symbolic_State_Print.string_of_gamma gamma in
		let pure_str = Symbolic_State_Print.string_of_shallow_p_formulae pure_formulae false in
		let msg = Printf.sprintf "The logical expression %s is not typable in the typing enviroment: %s \n with the pure formulae %s" (print_le nle) gamma_str pure_str in
		raise (Failure msg) in
	let nle = symb_evaluate_expr symb_state anti_frame expr in
	let nle = Simplifications.replace_nle_with_lvars pure_formulae nle in 
	let nle_type, is_typable, constraints = type_lexpr gamma nle in
	if (is_typable) then
		(if ((List.length constraints = 0) || (Pure_Entailment.check_entailment SS.empty (pfs_to_list pure_formulae) constraints gamma)) then 
			nle, nle_type, true
		else 
			let no_spec_vars_in_cons = List.fold_left (fun ac cons -> 
						 				ac && (not (Bi_Symbolic_State_Functions.l_vars_in_spec_check anti_frame spec_lvars nle)))
										true constraints in
			if (no_spec_vars_in_cons) then 
			 	let _ = Symbolic_State.extend_symb_state_with_pfs symb_state (Symbolic_State.pfs_of_list constraints) in
			 	let _ = Symbolic_State.extend_symb_state_with_pfs anti_frame (Symbolic_State.pfs_of_list constraints) in
				nle, nle_type, true
			else 
				fail nle
		)
	else
		(match nle with
		| LVar _ ->  nle, None, false
		| _ ->
			let new_gamma = Bi_Symbolic_State_Functions.bi_reverse_type_lexpr (get_pf anti_frame) pure_formulae gamma nle nle_type in
			match new_gamma with 
				| Some new_gamma -> 
					extend_gamma gamma new_gamma;
					extend_gamma (get_gamma anti_frame) new_gamma; 
					safe_symb_evaluate_expr spec_lvars symb_state anti_frame expr
				| None -> fail nle
		)

(**********************************************)
(* Symbolic evaluation of JSIL basic commands *)
(**********************************************)
let symb_evaluate_bcmd (bcmd : jsil_basic_cmd) (symb_state : symbolic_state) (anti_frame : symbolic_state) spec_lvars =
	let heap, store, pure_formulae, gamma, _ = symb_state in
	let anti_heap, anti_store, anti_pure_formulae, anti_gamma, _ = anti_frame in
	let ssee = safe_symb_evaluate_expr spec_lvars symb_state anti_frame in
	match bcmd with
	(* Skip: skip;
			Always return $$empty *)
	| SSkip ->
		print_endline "SKIP ";
		LLit Empty

  (* Assignment: x = e;
			a) Safely evaluate e to obtain nle and its type tle
			b) Update the abstract store with [x |-> nle]
			c) Update the typing environment with [x |-> tle] 
			d) Return nle *)
	| SAssignment (x, e) ->
		let nle, tle, _ = ssee e in
		store_put store x nle;
		update_gamma gamma x tle;
		nle

	(* Object creation: x = new ();
			a) Create fresh object location #l and add it to the heap
			b) Set (#l, "@proto") -> $$null in the heap
			c) Update the abstract store with [x |-> #l]
			d) Update the typing environment with [x |-> $$object_type]
			e) Add the fact that the new location is not $lg to the pure formulae
			f) Return the new location
	*)
	| SNew x ->
		let new_loc = fresh_aloc () in
		Symbolic_State_Utils.update_abs_heap_default heap new_loc LNone;
		Symbolic_State_Utils.update_abs_heap heap new_loc (LLit (String (JS2JSIL_Constants.internalProtoFieldName))) (LLit Null) pure_formulae (* solver *) gamma;
		store_put store x (ALoc new_loc);
		update_gamma gamma x (Some ObjectType);
		DynArray.add pure_formulae (LNot (LEq (ALoc new_loc, LLit (Loc JS2JSIL_Constants.locGlobName))));
		ALoc new_loc

  (* Property lookup: x = [e1, e2];
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) Safely evaluate e2 to obtain the property name ne2 and its type te2
			c) If ne1 is not a literal location or an abstract location
				i) Create a new heap cell (e1, e2) -> v
				ii) Add pure formula v != none
				iii) Return new cell location
			d) Otherwise, try to find the value ne of the property ne2 of object ne1
			e) Update the store with [x |-> ne]
			f) Return ne
	*)
	| SLookup (x, e1, e2) ->
		let ne1, te1, _ = ssee e1 in
		let ne2, te2, _ = ssee e2 in
		let l =
			(match ne1 with
			| LLit (Loc l)
			| ALoc l -> l
			| LLit _ -> 
				raise (Failure (Printf.sprintf "Lookup: %s is not a location" (print_le ne1)))
			| _ -> 
				let new_loc, anything = create_new_location ne1 symb_state anti_frame in
				DynArray.add pure_formulae (LNot (LEq (LVar anything, LNone)));
				DynArray.add anti_pure_formulae (LNot (LEq (LVar anything, LNone)));
				Symbolic_State_Utils.update_abs_heap heap new_loc ne2 (LVar anything) pure_formulae gamma;
				Symbolic_State_Utils.update_abs_heap anti_heap new_loc ne2 (LVar anything) pure_formulae gamma;
				new_loc) in
		let ne, extended = Bi_Symbolic_State_Functions.abs_heap_find symb_state anti_frame l ne2  in
		if (extended) then 
			(add_pure_assertion pure_formulae (LNot (LEq (ne, LNone)));
			add_pure_assertion anti_pure_formulae (LNot (LEq (ne, LNone))));
		let ne_type, _, _ = type_lexpr gamma ne  in
		update_gamma gamma x ne_type;
		store_put store x ne;
		ne

  (* Property assignment: [e1, e2] := e3;
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) Safely evaluate e2 to obtain the property name ne2 and its type te2
			c) Safely evaluate e3 to obtain the value ne3 to be assigned
			d) If ne1 is not a literal location or an abstract location
				i) Create the cell (e1, e2) -> v 
				ii) Return new cell location
			e) Update the heap with (ne1, ne2) -> ne3
			f) Return ne3
	*)
	| SMutation (e1, e2, e3) ->
		let ne1, t_le1, _ = ssee e1 in
		let ne2, t_le2, _ = ssee e2 in
		let ne3, _, _ = ssee e3 in
		let l = 
			(match ne1 with
				| LLit (Loc l)
				| ALoc l -> l
				| LLit _ -> 
					raise (Failure (Printf.sprintf "Lookup: %s is not a location" (print_le ne1)))	
				| _ -> 
					let new_loc, anything = create_new_location ne1 symb_state anti_frame in
					new_loc) in
		Bi_Symbolic_State_Functions.update_abs_heap heap anti_heap l ne2 ne3 pure_formulae gamma;
		ne3

  (* Property deletion: delete(e1, e2)
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) Safely evaluate e2 to obtain the property name ne2 and its type te2
			c) If ne1 is not a literal location or an abstract location
				i) Create the cell (e1, e2) -> v 
				ii) Return new cell location
			e) Delete (ne1, ne2) from the heap
			f) Return true
	*)
	| SDelete (e1, e2) ->
		let ne1, t_le1, _ = ssee e1 in
		let ne2, t_le2, _ = ssee e2 in
		let l =
			(match ne1 with
			| LLit (Loc l)
			| ALoc l -> l
			| LLit _ -> 
				raise (Failure (Printf.sprintf "Lookup: %s is not a location" (print_le ne1)))
			| _ -> 
				let new_loc, anything = create_new_location ne1 symb_state anti_frame in
				(* Symbolic_State_Functions.update_abs_heap anti_heap new_loc ne2 (LVar anything) pure_formulae gamma; *)
				new_loc)
			in
		Bi_Symbolic_State_Functions.update_abs_heap heap anti_heap l ne2 LNone pure_formulae gamma;
		LLit (Bool true)

  (* Object deletion: deleteObj(e1)
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) If ne1 is not a literal location or an abstract location, throw an error
			c) If the object at ne1 does not exist in the heap, throw an error
			c) Delete the entire object ne1 from the heap
			d) Return true
	*)
	(* TODO(Beatrix): Look into case *)
	| SDeleteObj e1 ->
		let ne1, t_le1, _ = ssee e1 in
		let l =
			(match ne1 with
			| LLit (Loc l)
			| ALoc l -> l
			| _ -> raise (Failure (Printf.sprintf "DeleteObject: I do not know which location %s denotes in the symbolic heap" (print_le ne1)))) in
		(match (LHeap.mem heap l) with
		 | false -> raise (Failure (Printf.sprintf "Attempting to delete an inexistent object: %s" (print_le ne1)))
		 | true -> LHeap.remove heap l; LLit (Bool true));

  (* Property existence: x = hasField(e1, e2);
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) Safely evaluate e2 to obtain the property name ne2 and its type te2
			c) If ne1 is not a literal location or an abstract location
				i) Create the cell (e1, e2) -> z 
				ii) Create a logical boolean variable y
				iii) Update the store with [x -> y]
				iv) Add pure formula which says:
						If z is none then y is false 
						If z is not none then y is true 
				v) Return y
			d) Otherwise, understand if the object ne1 has the property ne2 and store that result in res;
				i) If conclusive, update the store with [x |-> res] and return res
				ii) Otherwise, return unknown
				iii) If successful, update the store with [x |-> ne]
				iv) Return ne
	*)
	| SHasField (x, e1, e2) ->
		let ne1, t_le1, _ = ssee e1 in
		let ne2, t_le2, _ = ssee e2 in
		(match ne1 with
		| LLit (Loc l)
		| ALoc l ->
				let res = Bi_Symbolic_State_Functions.abs_heap_check_field_existence 
					symb_state anti_frame l ne2 pure_formulae gamma in
				update_gamma gamma x (Some BooleanType);
				(match res with 
				| _, Some b -> 
					Printf.printf "SHasField: got a boolean!\n";
					let res_lit = LLit (Bool b) in
					store_put store x res_lit;	
					res_lit 
				| Some f_val, None -> 
					let ret_lexpr = LUnOp (Not, LBinOp (f_val, Equal, LNone)) in 
					store_put store x ret_lexpr; 
					ret_lexpr
				| None, _ -> 
					let l_x = fresh_lvar () in 
					store_put store x (LVar l_x); 
					update_gamma gamma l_x (Some BooleanType);
					LVar l_x 
				)
		| LLit _ -> 
				raise (Failure (Printf.sprintf "Lookup: %s is not a location" (print_le ne1)))
		| _ -> 
			let new_loc, z = create_new_location ne1 symb_state anti_frame in
			Symbolic_State_Utils.update_abs_heap anti_heap new_loc ne2 (LVar z) pure_formulae gamma; 
			Symbolic_State_Utils.update_abs_heap heap new_loc ne2 (LVar z) pure_formulae gamma; 
			update_gamma gamma x (Some BooleanType);
			let ret_lexpr = LUnOp (Not, LBinOp (LVar z, Equal, LNone)) in 
			store_put store x ret_lexpr;	
			ret_lexpr)

type precondition_total_unifier = (jsil_n_single_spec * symbolic_heap * predicate_set * substitution * (jsil_logic_assertion list) * typing_environment) 
type precondition_partial_unifier = (jsil_n_single_spec * symbolic_heap * symbolic_state * predicate_set * substitution * (jsil_logic_assertion list) * typing_environment) 



let find_and_apply_spec 
			(prog : jsil_program) 
			(proc_name : string) 
			(proc_specs : jsil_n_spec) 
			(symb_state : symbolic_state) 
			(anti_frame : symbolic_state) 
			(le_args : jsil_logic_expr list) =

	print_debug (Printf.sprintf "Entering BI_find_and_apply_spec: %s." proc_name);

	(* create a new symb state with the abstract store in which the
	    called procedure is to be executed *)
	let proc = get_proc prog proc_name in
	let proc_args = get_proc_args proc in
	let new_store = store_init proc_args le_args in
	let symb_state_aux = symb_state_replace_store symb_state new_store in

	let compatible_pfs symb_state pat_symb_state subst =
		print_debug (Printf.sprintf "Entering compatible_pfs.");
		let pfs = get_pf symb_state in
		let gamma = get_gamma symb_state in
		let pat_pfs = get_pf pat_symb_state in
		let pat_gamma = get_gamma pat_symb_state in
		print_debug (Printf.sprintf "pfs: \n%s" (Symbolic_State_Print.string_of_shallow_p_formulae pfs false));
		print_debug (Printf.sprintf "pat_pfs: \n%s" (Symbolic_State_Print.string_of_shallow_p_formulae pat_pfs false));
		print_debug (Printf.sprintf "gamma: \n%s" (Symbolic_State_Print.string_of_gamma gamma));
		print_debug (Printf.sprintf "%s" (Symbolic_State_Print.string_of_substitution subst));
		let pat_pfs = pf_substitution pat_pfs subst false in
		let pat_gamma = gamma_substitution pat_gamma subst false in
		let gamma = copy_gamma gamma in
		merge_gammas gamma pat_gamma;
		let pf_list = (pfs_to_list pat_pfs) @ (pfs_to_list pfs) in
		print_debug (Printf.sprintf "About to check sat of:\n%s\ngiven\n%s" (Symbolic_State_Print.string_of_shallow_p_formulae (DynArray.of_list pf_list) false) (Symbolic_State_Print.string_of_gamma gamma));
		let is_sat = Pure_Entailment.check_satisfiability pf_list gamma in
		print_debug (Printf.sprintf "Satisfiable: %b" is_sat);
		is_sat in


	let transform_symb_state (spec : jsil_n_single_spec) (symb_state : symbolic_state) (quotient_heap : symbolic_heap) (quotient_preds : predicate_set) (subst : substitution) (pf_discharges : jsil_logic_assertion list) (new_gamma : typing_environment) : (symbolic_state * jsil_return_flag * jsil_logic_expr) list =

		print_debug (Printf.sprintf "Entering transform_symb_state.\n");

		let merge_symb_state_with_single_post (symb_state : symbolic_state) (post : symbolic_state) ret_var ret_flag copy_flag : (symbolic_state * jsil_return_flag * jsil_logic_expr) list =
			print_debug (Printf.sprintf "Entering merge_symb_state_with_single_post.");
			let post_makes_sense = compatible_pfs symb_state post subst in
			if (post_makes_sense) then (
				print_debug (Printf.sprintf "The post makes sense.");
				let new_symb_state = if (copy_flag) then (copy_symb_state symb_state) else symb_state in
				let new_symb_state = Structural_Entailment.merge_symb_states new_symb_state post subst in
				let ret_lexpr = store_get (get_store post) ret_var in
				let ret_lexpr = JSIL_Logic_Utils.lexpr_substitution ret_lexpr subst false in
				[ new_symb_state, ret_flag, ret_lexpr ])
				else begin print_debug (Printf.sprintf "The post does not make sense."); [] end in

		let pfs_subst = pf_substitution (DynArray.of_list pf_discharges) subst true in
		extend_symb_state_with_pfs symb_state pfs_subst;
		let symb_state = symb_state_replace_heap symb_state quotient_heap in
		let symb_state = symb_state_replace_preds symb_state quotient_preds in
		let symb_state = symb_state_replace_gamma symb_state new_gamma in
		let ret_var = proc_get_ret_var proc spec.n_ret_flag in
		let ret_flag = spec.n_ret_flag in

		let symb_states_and_ret_lexprs =
			(match spec.n_post with
			| [] -> print_debug (Printf.sprintf "No postconditions found."); []
			| [ post ] -> print_debug (Printf.sprintf "One postcondition found."); merge_symb_state_with_single_post symb_state post ret_var ret_flag false
			| post :: rest_posts ->
					print_debug (Printf.sprintf "Multiple postconditions found.");
					let symb_states_and_ret_lexprs = List.map (fun post -> merge_symb_state_with_single_post symb_state post ret_var ret_flag true) rest_posts in
					let symb_states_and_ret_lexprs =
						(merge_symb_state_with_single_post symb_state post ret_var ret_flag false) :: symb_states_and_ret_lexprs in
					let symb_states_and_ret_lexprs = List.concat symb_states_and_ret_lexprs in
					symb_states_and_ret_lexprs) in
		symb_states_and_ret_lexprs in

	
	let enrich_anti_frame anti_frame new_anti_frame subst = 
		let af_heap, store, pfs, gamma, preds = anti_frame in 
		let n_af_heap, n_store, n_pfs, n_gamma, n_preds = new_anti_frame in 
		let n_af_heap = heap_substitution n_af_heap subst false in
		Symbolic_State_Utils.merge_heaps af_heap n_af_heap pfs gamma;
		merge_pfs pfs n_pfs;
		extend_gamma gamma n_gamma in 

	let rec find_correct_specs 
			spec_list (ac_qs_complete, ac_qs_partial)  
				: ((precondition_total_unifier list) * (precondition_partial_unifier list)) =
		match spec_list with
		| [] -> (ac_qs_complete, ac_qs_partial)
		| spec :: rest_spec_list ->
			print_debug (Printf.sprintf "------------------------------------------");
			print_debug (Printf.sprintf "Entering BI-find_correct_specs with the spec:");
			print_debug (Printf.sprintf "------------------------------------------");
			print_debug (Printf.sprintf "Pre:\n%sPosts:\n%s\n"
				(Symbolic_State_Print.string_of_shallow_symb_state spec.n_pre)
				(Symbolic_State_Print.string_of_symb_state_list spec.n_post));
			print_debug (Printf.sprintf "Current State: \n%s"
				(Symbolic_State_Print.string_of_shallow_symb_state symb_state_aux));
			try (
			let unifier = Bi_Structural_Entailment.bi_unify_symb_states SS.empty spec.n_pre symb_state_aux in
			(match unifier with
			|	Some (true, quotient_heap, anti_frame, quotient_preds, subst, pf_discharges, new_gamma) 
					when (is_empty_symb_state anti_frame !js) ->
				print_debug (Printf.sprintf "I found a COMPLETE match");
				print_debug (Printf.sprintf "ANTI FRAME: %s\n"
					(Symbolic_State_Print.string_of_shallow_symb_state anti_frame));
				print_debug (Printf.sprintf "The pre of the spec that completely matches me is:\n%s"
					(Symbolic_State_Print.string_of_shallow_symb_state spec.n_pre));
				print_debug (Printf.sprintf "The number of posts is: %d"
					(List.length spec.n_post));
				[ (spec, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma) ], []
			
			| Some (false, quotient_heap, anti_frame, quotient_preds, subst, pf_discharges, new_gamma)
					 when (is_empty_symb_state anti_frame !js) ->
				print_debug (Printf.sprintf "I found a PARTIAL match");
				print_debug (Printf.sprintf "ANTI FRAME: %s\n"
					(Symbolic_State_Print.string_of_shallow_symb_state anti_frame));
				let new_ac_qs_partial = (spec, quotient_heap, anti_frame, quotient_preds, subst, pf_discharges, new_gamma) :: ac_qs_partial in 
				find_correct_specs rest_spec_list (ac_qs_complete, new_ac_qs_partial)
			
			| Some (_, quotient_heap, anti_frame, quotient_preds, subst, pf_discharges, new_gamma) -> 
				print_debug (Printf.sprintf "I found a PARTIAL match");
				print_debug (Printf.sprintf "anti frame: %s\n"
					(Symbolic_State_Print.string_of_shallow_symb_state anti_frame));
				let new_ac_qs_partial = (spec, quotient_heap, anti_frame, quotient_preds, subst, pf_discharges, new_gamma) :: ac_qs_partial in 
				find_correct_specs rest_spec_list (ac_qs_complete, new_ac_qs_partial)
				
			| None -> (
				print_debug (Printf.sprintf "I found a NON-match");
				find_correct_specs rest_spec_list (ac_qs_complete, ac_qs_partial))))
			with | e -> (match e with 
				| SymbExecFailure failure -> 
						print_debug (Symbolic_State_Print.print_failure failure);
						print_debug (Printf.sprintf "I found a NON-match");
						find_correct_specs rest_spec_list (ac_qs_complete, ac_qs_partial)
				| _ -> 	print_debug (Printexc.to_string e);
						print_debug (Printf.sprintf "I found a NON-match");
						find_correct_specs rest_spec_list (ac_qs_complete, ac_qs_partial)) in


	let transform_symb_state_partial_match 
		(spec, quotient_heap, new_anti_frame, quotient_preds, subst, pf_discharges, new_gamma) 
			: (symbolic_state * symbolic_state * jsil_return_flag * jsil_logic_expr) list =
		let symb_state = copy_symb_state symb_state in 
		let anti_frame = copy_symb_state anti_frame in 
		let symb_states_and_ret_lexprs = 
			transform_symb_state spec symb_state quotient_heap quotient_preds subst pf_discharges new_gamma in

		let symb_states_and_ret_lexprs =
			List.fold_left
				(fun ac (symb_state, ret_flag, ret_lexpr) ->
					let new_symb_state = Bi_Structural_Entailment.enrich_pure_part symb_state spec.n_pre subst in
					let anti_frame = Bi_Structural_Entailment.enrich_pure_part anti_frame spec.n_pre subst in
					enrich_anti_frame anti_frame new_anti_frame subst;
					extend_symb_state_with_pfs new_symb_state (get_pf new_anti_frame);
					let is_sat = Pure_Entailment.check_satisfiability (get_pf_list new_symb_state) (get_gamma new_symb_state) in
					if is_sat then ((new_symb_state, anti_frame, ret_flag, ret_lexpr) :: ac) else ac)
				[] symb_states_and_ret_lexprs in

		let symb_states_and_ret_lexprs =
			List.map (fun (symb_state, new_anti_frame, ret_flag, ret_lexpr) ->
			let new_symb_state =
				let pfs = get_pf symb_state in
				let rpfs = DynArray.map (fun x -> Simplifications.reduce_assertion_no_store new_gamma pfs x) pfs in
				Simplifications.sanitise_pfs_no_store new_gamma rpfs;
				symb_state_replace_pfs symb_state rpfs in
			(new_symb_state, new_anti_frame, ret_flag, Simplifications.reduce_expression_no_store_no_gamma_no_pfs ret_lexpr)) symb_states_and_ret_lexprs in
		symb_states_and_ret_lexprs in
	
	let transform_symb_state_partial_match_list 
		(symb_state : symbolic_state)
		(quotients  : precondition_partial_unifier list) =
		let new_symb_states = 
			List.map
				(fun (spec, quotient_heap, anti_frame, quotient_preds, subst, pf_discharges, new_gamma) ->
					if (compatible_pfs symb_state spec.n_pre subst)
						then transform_symb_state_partial_match (spec, quotient_heap, anti_frame, quotient_preds, subst, pf_discharges, new_gamma)
						else [])
				quotients in
			let new_symb_states = List.concat new_symb_states in
			new_symb_states in 
					
	let rec apply_correct_specs 
		(quotients : ((precondition_total_unifier list) * (precondition_partial_unifier list))) =
		print_debug (Printf.sprintf "Entering apply_correct_specs.");
		match quotients with
		| ([], []) -> [ ]
		
		| [ (spec, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma) ], _ ->
			print_debug (Printf.sprintf "This was a TOTAL MATCH!!!!");
			let symb_states_and_ret_lexprs = transform_symb_state spec symb_state quotient_heap quotient_preds subst pf_discharges new_gamma in 
			List.map 
				(fun (symb_state, ret_flag, ret_lexpr) -> 
					let anti_frame = copy_symb_state anti_frame in 
					(symb_state, anti_frame, ret_flag, ret_lexpr))
				symb_states_and_ret_lexprs 
				
		| _, _ :: _ ->
			let _, qs_partial = quotients in 
			print_debug (Printf.sprintf "This was a PARTIAL MATCH!!!!");
			transform_symb_state_partial_match_list symb_state qs_partial in

	let quotients = find_correct_specs proc_specs.n_proc_specs ([], []) in
	apply_correct_specs quotients

let rec fold_predicate pred_name pred_defs symb_state params args spec_vars existentials : (symbolic_state * SS.t) option =

	print_time_debug ("fold_predicate:");

	(* create a new symb state with the abstract store in which the
	    called procedure is to be executed *)
	let new_store = store_init params args in
	let symb_state_aux = symb_state_replace_store symb_state new_store in

	let existentials =
		(match existentials with
		| None ->
			let symb_state_vars : SS.t = get_symb_state_vars false symb_state  in
			let args_vars : SS.t = JSIL_Logic_Utils.get_vars_le_list false args in
			let existentials : SS.t = SS.diff args_vars symb_state_vars in
			existentials
		| Some existentials -> existentials) in

	let new_spec_vars = SS.union spec_vars existentials in
	print_debug (Printf.sprintf "New spec vars (fold): %s" (String.concat ", " (SS.elements existentials)));

	let existentials_str = print_var_list (SS.elements existentials) in
	print_debug (Printf.sprintf ("\nFOLDING %s(%s) with the existentials %s in the symbolic state: \n%s\n")
	  pred_name 
		(String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le false) args))
		existentials_str
		(Symbolic_State_Print.string_of_shallow_symb_state symb_state));

	let update_symb_state_after_folding complete_fold symb_state quotient_heap quotient_preds new_pfs new_gamma pred_name args =
		print_time_debug ("update_symb_state_after_folding:");
		let symb_state = symb_state_replace_heap symb_state quotient_heap in
		let symb_state = symb_state_replace_preds symb_state quotient_preds in
		let symb_state = symb_state_replace_gamma symb_state new_gamma in
		extend_symb_state_with_pfs symb_state (DynArray.of_list new_pfs);
		(* if complete_fold then symb_state_add_predicate_assertion symb_state (pred_name, args); *)
		symb_state in

	let rec find_correct_pred_def cur_pred_defs : (symbolic_state * SS.t) option =
		print_time_debug ("find_correct_pred_def:");
		(match cur_pred_defs with
		| [] -> None
		| pred_def :: rest_pred_defs ->
			print_debug (Printf.sprintf "----------------------------");
			print_debug (Printf.sprintf "Current pred symbolic state: %s" (Symbolic_State_Print.string_of_shallow_symb_state pred_def));
			let unifier = try (Some (Structural_Entailment.unify_symb_states_fold pred_name existentials pred_def symb_state_aux))
				with | SymbExecFailure failure -> print_debug (Symbolic_State_Print.print_failure failure); None in
			(match unifier with
			| Some (true, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma, _, []) ->
			  print_debug (Printf.sprintf "I can fold this!!!");
				let new_symb_state = update_symb_state_after_folding true symb_state quotient_heap quotient_preds pf_discharges new_gamma pred_name args in
				print_debug (Printf.sprintf "Symbolic state after FOLDING:\n%s" (Symbolic_State_Print.string_of_shallow_symb_state new_symb_state));
				Some (new_symb_state, new_spec_vars)

			| Some (true, quotient_heap, quotient_preds, subst, pf_discharges, new_gamma, existentials, [ (missing_pred_name, missing_pred_args) ]) ->
				let missing_pred_args = List.map (fun le -> JSIL_Logic_Utils.lexpr_substitution le subst false) missing_pred_args in
				if (not (missing_pred_name = pred_name)) then None else (
					print_debug (Printf.sprintf "I can NOT quite fold this because I am missing %s(%s)!!!"
						missing_pred_name
						(String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le false) missing_pred_args)));
					let new_symb_state = update_symb_state_after_folding false symb_state quotient_heap quotient_preds pf_discharges new_gamma pred_name args in
					let new_symb_state, new_subst = Simplifications.simplify_ss_with_subst new_symb_state (Some None) in 
					
					print_debug (Printf.sprintf "New subst: %s" (Symbolic_State_Print.string_of_substitution new_subst)); 
					
					(** WARNING WARNING WARNING - EXPERIMENTAL START *)
					(* Filtering existentials that still depend on existentials *)
					Hashtbl.iter (fun v le -> 
						let vars_le = get_logic_expression_lvars le in 
							if (SS.inter existentials vars_le <> SS.empty) then
							begin
								print_debug_petar (Printf.sprintf "Warning: variable %s depends on existentials" v);
								Hashtbl.remove new_subst v;
							end) new_subst;
								
					(** WARNING WARNING WARNING - EXPERIMENTAL END   *)
	
					let existentials_to_remove = (Hashtbl.fold (fun v _ ac -> v :: ac) new_subst []) in 
					print_debug_petar (Printf.sprintf "Exists to remove: %s" (String.concat "," existentials_to_remove));
					print_debug_petar (Printf.sprintf "Old exists: %s" (String.concat "," (SS.elements existentials)));				
					
					let new_existentials = SS.filter (fun v -> (not (List.mem v existentials_to_remove))) existentials in 
					print_debug (Printf.sprintf "New exists: %s" (String.concat "," (SS.elements new_existentials)));
					
					let new_subst = JSIL_Logic_Utils.filter_substitution new_subst existentials in
					print_debug (Printf.sprintf "New substitution: \n%s" (Symbolic_State_Print.string_of_substitution new_subst));
					let missing_pred_args = List.map (fun le -> JSIL_Logic_Utils.lexpr_substitution le new_subst true) missing_pred_args in
					print_debug (Printf.sprintf "And now I am missing %s(%s)!!!"
						missing_pred_name
						(String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le false) missing_pred_args)));
					let new_symb_state = symb_state_substitution new_symb_state new_subst true in
					(** WARNING WARNING WARNING - EXPERIMENTAL START *)
					(* Adding equalities we know hold *)
					let new_pfs = get_pf new_symb_state in
					Hashtbl.iter (fun var le -> DynArray.add new_pfs (LEq (LVar var, le))) new_subst;
					(** WARNING WARNING WARNING - EXPERIMENTAL END   *)
					print_debug (Printf.sprintf "Symbolic state after partial FOLDING:\n%s" (Symbolic_State_Print.string_of_shallow_symb_state new_symb_state));
					let new_symb_state = fold_predicate pred_name pred_defs new_symb_state params missing_pred_args new_spec_vars (Some new_existentials) in
					(match new_symb_state with
					| Some new_symb_state ->
						(* remove_predicate_assertion (get_preds new_symb_state) (missing_pred_name, missing_pred_args); *) 
						Some new_symb_state
					| None -> None))

			| Some (_, _, _, _, _, _, _, _) | None -> find_correct_pred_def rest_pred_defs)) in
	find_correct_pred_def pred_defs

(* 
	UNFOLD: Returns ->  a list of pairs containing:
		- an unfolded symbolic state
		- the set of spec vars to be added
*)
let unfold_predicates 
				(pred_name  : string) 
				(pred_defs  : symbolic_state list) 
				(symb_state : symbolic_state)
				(params     : string list) 
				(args       : jsil_logic_expr list)
				(spec_vars  : SS.t) : (symbolic_state * SS.t) list =

	print_debug (Printf.sprintf "UNFOLD_PREDICATES: Current symbolic state:\n%s" (Symbolic_State_Print.string_of_shallow_symb_state symb_state));

	let symb_state_vars : SS.t = get_symb_state_vars false symb_state  in
	let args_vars : SS.t = JSIL_Logic_Utils.get_vars_le_list false args in
	let existentials : SS.t = SS.diff args_vars symb_state_vars in
	
	print_debug (Printf.sprintf "New spec vars (unfold): %s" (String.concat ", " (SS.elements existentials)));
	
	let new_spec_vars = SS.union spec_vars existentials in
	let existentials = SS.elements existentials in 

	let subst0 = Symbolic_State_Utils.subtract_pred pred_name args (get_preds symb_state) (get_pf symb_state) (get_gamma symb_state) spec_vars existentials in
	
	(* Printf.printf "I survived the subtract pred!!!\n"; *)

	let args = List.map (fun le -> lexpr_substitution le subst0 true) args in
	let calling_store = store_init params args in

	let rec loop pred_defs results : (symbolic_state * SS.t) list =
		(match pred_defs with
		| [] -> results
		| pred_symb_state :: rest_pred_defs ->
			print_debug (Printf.sprintf "Current Pred DEF:\n%s" (Symbolic_State_Print.string_of_shallow_symb_state pred_symb_state));
			print_debug (Printf.sprintf "Current symbolic state:\n%s" (Symbolic_State_Print.string_of_shallow_symb_state symb_state));
			let unfolded_symb_state = Structural_Entailment.unfold_predicate_definition symb_state pred_symb_state calling_store subst0 spec_vars in
			(match unfolded_symb_state with
			| None -> loop rest_pred_defs results
			| Some unfolded_symb_state ->
				loop rest_pred_defs ((unfolded_symb_state, new_spec_vars) :: results))) in

	loop pred_defs [] 

let recursive_unfold 
				(pred_name  : string) 
				(pred_defs  : symbolic_state list) 
				(symb_state : symbolic_state)
				(params     : jsil_var list) 
				(spec_vars  : SS.t) : (symbolic_state * SS.t) list =

	print_debug (Printf.sprintf "Recursive Unfold: %s" pred_name); 
	print_debug (Printf.sprintf "Spec vars (recunfold): %s" (String.concat ", " (SS.elements spec_vars)));
	let rec loop cur_spec_vars symb_state : symbolic_state * SS.t =
		let rec aux cur_spec_vars symb_state args : symbolic_state * SS.t =
			print_debug_petar (Printf.sprintf "pred_args: %s\n"
				(String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le false) args)));
			let unfolded_symb_states_with_spec_vars = unfold_predicates pred_name pred_defs symb_state params args cur_spec_vars in
			let len = List.length unfolded_symb_states_with_spec_vars in
			print_debug (Printf.sprintf "number of unfolded_symb_states: %i\n" len);
			if (len <> 1)
				then (print_debug (Printf.sprintf "End of recursive_unfold: More than one unfolding or nothing at all, oops.\n"); symb_state, spec_vars)
				else (
					let new_symb_state, new_spec_vars = List.hd unfolded_symb_states_with_spec_vars in
					let new_symb_state = Simplifications.simplify_ss new_symb_state (Some (Some new_spec_vars)) in
					print_debug (Printf.sprintf "Inside recursive_unfolding. continuing with:\n%s\n" (Symbolic_State_Print.string_of_shallow_symb_state new_symb_state));
					loop new_spec_vars new_symb_state) in

		let rec inner_loop cur_spec_vars pred_args symb_state =
			match pred_args with
			| [] -> symb_state, cur_spec_vars
			| args :: more_args ->
				aux cur_spec_vars symb_state args in

		let pred_args = find_predicate_assertion (get_preds symb_state) pred_name in
		let len_pred_args = List.length pred_args in
		print_debug_petar (Printf.sprintf "len_pred_args: %i\n" len_pred_args);
		inner_loop cur_spec_vars pred_args symb_state in

	[ loop spec_vars symb_state ]


(* Unfolding of macros *)
let rec unfold_macro (macro_name : string) (params_vals : jsil_logic_expr list) : jsil_logic_command =
	if (Hashtbl.mem macro_table macro_name) then
		(let macro = Hashtbl.find macro_table macro_name in
		(* print_debug (Printf.sprintf ("Macro: %s(%s) : %s") 
				macro.mname
				(String.concat ", " macro.mparams)
				(JSIL_Print.string_of_lcmd macro.mdefinition)); *)
		let params = macro.mparams in
		let lparo = List.length params in
		let lparv = List.length params_vals in
		if (lparo <> lparv) then
			raise (Failure (Printf.sprintf "Macro %s called with incorrect number of parameters: %d instead of %d." macro.mname lparv lparo))
		else
			let subst = Hashtbl.create 17 in
			List.iter2 (fun x y -> Hashtbl.add subst x y) params params_vals;
			macro_subst macro.mdefinition subst)
		else
			raise (Failure (Printf.sprintf "Macro %s not found in macro table." macro_name))
and
(** Apply function f to the logic expressions in a logic command, recursively when it makes sense. *)
lcmd_map f unfold_macros lcmd =
	(* Map recursively to commands, assertions, and expressions *)
	let map_l = lcmd_map f unfold_macros in
	let map_a = assertion_map f in
	let map_e = logic_expression_map f in
	match lcmd with
	| Fold      a                   -> Fold      (map_a a)
	| Unfold    a                   -> Unfold    (map_a a)
	| RecUnfold s                   -> RecUnfold s
	| LogicIf   (e, lcmds1, lcmds2) -> LogicIf   (map_e e, List.map (fun x -> map_l x) lcmds1, List.map (fun x -> map_l x) lcmds2)
	| Macro     (name, params_vals) -> 
		let fparams_vals = List.map (fun x -> map_e x) params_vals in
		(match unfold_macros with
		| true  -> unfold_macro name fparams_vals
		| false -> Macro (name, fparams_vals))
and
macro_subst (lcmd : jsil_logic_command) (subst : (string, jsil_logic_expr) Hashtbl.t) : jsil_logic_command = 
	let substitute = 
		(fun e ->
			((match e with
			| PVar v ->
				(match Hashtbl.mem subst v with
				| true  -> Hashtbl.find subst v
				| false -> e)
			| _ -> e), true)) in
	lcmd_map substitute true lcmd



let rec symb_evaluate_logic_cmd s_prog l_cmd symb_state subst spec_vars : (symbolic_state * SS.t) list =

	let get_pred_data pred_name les =
		let pred = get_pred s_prog.pred_defs pred_name in
		let args =
			List.map
				(fun le -> Normaliser.normalise_lexpr (get_store symb_state) (get_gamma symb_state) subst le)
				les in
		let params = pred.n_pred_params in
		let pred_defs = pred.n_pred_definitions in
		(params, pred_defs, args) in

	(match l_cmd with
	| Fold a ->
		print_time "Fold.";
		(match a with
		| LPred	(pred_name, les) ->
			let params, pred_defs, args = get_pred_data pred_name les in
			let new_symb_state = fold_predicate pred_name pred_defs symb_state params args spec_vars None in
			(match new_symb_state with
			| Some (symb_state, new_spec_vars) ->
				symb_state_add_predicate_assertion symb_state (pred_name, args);
				[ symb_state, (* UNDERSTAND *) new_spec_vars ]
			| None ->
				print_endline (Printf.sprintf "\nSTATE ON ERROR: %s" (Symbolic_State_Print.string_of_shallow_symb_state symb_state));
				let msg = Printf.sprintf "Could not fold: %s " (JSIL_Print.string_of_logic_assertion a false) in
				raise (Failure msg))
		| _ ->
			let msg = Printf.sprintf "Illegal fold command %s" (JSIL_Print.string_of_logic_assertion a false) in
			raise (Failure msg))

	| Unfold a ->
		print_time "Unfold.";
		(match a with
		| LPred (pred_name, les) ->
			let params, pred_defs, args = get_pred_data pred_name les in
			let symb_states_with_new_spec_vars = unfold_predicates pred_name pred_defs symb_state params args spec_vars in
			if ((List.length symb_states_with_new_spec_vars) = 0) then (
				print_endline (Printf.sprintf "\nCould not unfold: %s" pred_name);
				let msg = Printf.sprintf "Could not unfold: %s " (JSIL_Print.string_of_logic_assertion a false) in
				raise (Failure msg))
			else symb_states_with_new_spec_vars
		| _ ->
			let msg = Printf.sprintf "Illegal unfold command %s" (JSIL_Print.string_of_logic_assertion a false) in
			raise (Failure msg))

	| RecUnfold pred_name ->
		print_time "RecUnfold.";
		let pred = get_pred s_prog.pred_defs pred_name in
		let pred_defs = pred.n_pred_definitions in
		let params = pred.n_pred_params in
			recursive_unfold pred_name pred_defs symb_state params spec_vars

	| LogicIf (le, then_lcmds, else_lcmds) ->
		print_time "LIf.";
		let le' = Normaliser.normalise_lexpr (get_store symb_state) (get_gamma symb_state) (init_substitution []) le in
		let e_le', a_le' = lift_logic_expr le' in
		let a_le_then =
			match e_le', a_le' with
			| _, Some (a_le, _) -> a_le
			| Some e_le, None -> LEq (e_le, LLit (Bool true))
			| None, None -> LFalse in
		if (Pure_Entailment.check_entailment SS.empty (get_pf_list symb_state) [ a_le_then ] (get_gamma symb_state))
			then symb_evaluate_logic_cmds s_prog then_lcmds [ symb_state, spec_vars ] subst 
			else symb_evaluate_logic_cmds s_prog else_lcmds [ symb_state, spec_vars ] subst  
		
	| Macro (name, param_vals) ->
			let actual_command = unfold_macro name param_vals in 
			(* print_debug (Printf.sprintf ("Unfolded macro: %s(%s) -> %s") 
				name
				(String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x false) param_vals))
				(JSIL_Print.string_of_lcmd actual_command)); *)
					symb_evaluate_logic_cmd s_prog actual_command symb_state subst spec_vars
	)
and
symb_evaluate_logic_cmds s_prog (l_cmds : jsil_logic_command list) (symb_states_with_spec_vars : (symbolic_state * SS.t) list) subst : (symbolic_state * SS.t) list =
	let symb_states_with_spec_vars = 
		let symb_states, spec_vars = List.split symb_states_with_spec_vars in
		let symb_states = List.map2 (fun s sv -> Simplifications.simplify_ss s (Some (Some sv))) symb_states spec_vars in
			List.combine symb_states spec_vars in
	(match l_cmds with
	| [] -> symb_states_with_spec_vars
	| l_cmd :: rest_l_cmds ->
		let new_symb_states_with_spec_vars =
			List.fold_left
				(fun ac_new_symb_states_with_spec_vars (symb_state, spec_vars) ->
					let new_symb_states_with_spec_vars = symb_evaluate_logic_cmd s_prog l_cmd symb_state subst spec_vars in
					new_symb_states_with_spec_vars @ ac_new_symb_states_with_spec_vars)
				[]
				symb_states_with_spec_vars in
			symb_evaluate_logic_cmds s_prog rest_l_cmds new_symb_states_with_spec_vars subst)


let rec symb_evaluate_cmd s_prog proc spec search_info symb_state anti_frame i prev : ((symbolic_state * symbolic_state * jsil_return_flag) list) =

	(* auxiliary functions *)
	let mark_as_visited search_info i =
		let cur_node_info = search_info.cur_node_info in
		Hashtbl.replace search_info.vis_tbl i cur_node_info.node_number in


	let print_symb_state_and_cmd symb_state anti_frame =
		let symb_state_str = Symbolic_State_Print.string_of_shallow_symb_state symb_state in
		let anti_frame_str = Symbolic_State_Print.string_of_shallow_symb_state anti_frame in
		let cmd = get_proc_cmd proc i in
		let cmd_str = JSIL_Print.string_of_cmd cmd 0 0 false false false in
		let time = Sys.time() in
		print_endline "" in
		(*print_endline (Printf.sprintf
			"----------------------------------\n--%i--\nTIME: %f\n ---- STATE: ---- \n%s -------- \n ---- ANTI_FRAME: ----\n%s -------- \n CMD: %s\n----------------------------------"
			i time symb_state_str anti_frame_str cmd_str) in*)


	(* symbolically evaluate a guarded goto *)
	let symb_evaluate_guarded_goto symb_state anti_frame e j k : ((symbolic_state * symbolic_state * jsil_return_flag) list) =
		let le = symb_evaluate_expr symb_state anti_frame e in
		print_debug (Printf.sprintf "Evaluated expression: %s --> %s\n" (JSIL_Print.string_of_expression e false) (JSIL_Print.string_of_logic_expression le false));
		let e_le, a_le = lift_logic_expr le in
		let a_le_then, a_le_else =
			match e_le, a_le with
			| _, Some (a_le, a_not_le) ->
				print_debug (Printf.sprintf "Lifted assertion: %s\n" (JSIL_Print.string_of_logic_assertion a_le false));
				([ a_le ], [ a_not_le ])
			| Some e_le, None ->
				([LEq (e_le, LLit (Bool true))], [LEq (e_le, LLit (Bool false))])
			| None, None -> ([ LFalse ], [ LFalse ]) in

		print_debug (Printf.sprintf "Checking if:\n%s\n\tentails\n%s\n" (JSIL_Print.str_of_assertion_list (get_pf_list symb_state)) (JSIL_Print.str_of_assertion_list a_le_then));
		if (Pure_Entailment.check_entailment SS.empty (get_pf_list symb_state) a_le_then (get_gamma symb_state)) then
			(print_endline "in the THEN branch";
			symb_evaluate_next_cmd s_prog proc spec search_info symb_state anti_frame i j)
		else (
			if (Pure_Entailment.check_entailment SS.empty (get_pf_list symb_state) a_le_else (get_gamma symb_state)) then
				(print_endline "in the ELSE branch";
				symb_evaluate_next_cmd s_prog proc spec search_info symb_state anti_frame i k)
			else (
				print_endline "I could not determine the branch.";
				let then_symb_state = symb_state in
				let then_anti_frame = anti_frame in
				let then_search_info = search_info in
				let else_symb_state = copy_symb_state symb_state in
				let else_anti_frame = copy_symb_state anti_frame in
				let else_search_info = update_vis_tbl search_info (copy_vis_tbl search_info.vis_tbl) in

				if (Bi_Symbolic_State_Functions.l_vars_in_spec_check anti_frame spec.n_lvars le) then
					raise (Failure "Logical Variables of expression not contained within the spec or anti_frame");

				Simplifications.naively_infer_type_information (get_pf symb_state) (get_gamma symb_state);
				Simplifications.naively_infer_type_information (get_pf anti_frame) (get_gamma anti_frame);
				(* Then Branch  
				Printf.printf (
					String.concat ", "
					(List.map 
						(fun a -> JSIL_Print.string_of_logic_assertion a false)
						a_le_then)); *)
				extend_symb_state_with_pfs then_symb_state (DynArray.of_list a_le_then);
				extend_symb_state_with_pfs then_anti_frame (DynArray.of_list a_le_then);
				print_symb_state_and_cmd then_symb_state then_anti_frame;
				let then_result_states =  
					(try 
						symb_evaluate_next_cmd s_prog proc spec then_search_info then_symb_state then_anti_frame i j 
					with e ->
						print_endline (Printf.sprintf "Bi-Symbolic Execution of the then branch has failed with message %s. Ending symbolic execution." (Printexc.to_string e));
						Bi_Utils.update_failures proc.proc_name (Printexc.to_string e);
						[] ) in

				(* Else Branch *)
				extend_symb_state_with_pfs else_symb_state (DynArray.of_list a_le_else);
				extend_symb_state_with_pfs else_anti_frame (DynArray.of_list a_le_else);
				print_symb_state_and_cmd else_symb_state else_anti_frame;
				let else_result_states = 
					(try
						symb_evaluate_next_cmd s_prog proc spec else_search_info else_symb_state else_anti_frame i k 
					with e ->
						print_endline (Printf.sprintf "Bi-Symbolic Execution of the else branch has failed with message %s. Ending symbolic execution." (Printexc.to_string e));
						Bi_Utils.update_failures proc.proc_name (Printexc.to_string e);
						[] ) in
				then_result_states @ else_result_states
			)
		) 
		in

	(* symbolically evaluate a procedure call *)
	let symb_evaluate_call symb_state anti_frame x e e_args j : ((symbolic_state * symbolic_state * jsil_return_flag) list) =
		(* get the name and specs of the procedure being called *)
		let le_proc_name = symb_evaluate_expr symb_state anti_frame e in
		let proc_name =
			(match le_proc_name with
			| LLit (String proc_name) -> proc_name
			| _ ->
				let msg = Printf.sprintf "Symb Execution Error - Cannot analyse a procedure call without the name of the procedure. Got: %s." (JSIL_Print.string_of_logic_expression le_proc_name false) in
				raise (Failure msg)) in
		if ((proc_name = proc.proc_name)) then
			(print_endline "Recursive Call, ending symbolic execution."; 
			[])
		else
			let proc_specs = (try
				Some (Hashtbl.find s_prog.spec_tbl proc_name)
			with Not_found ->
				print_endline "No specs were found for this procedure, probably due to mutual recursion or procedure not found. Ending symbolic execution.";
				None) in
			match proc_specs with  
			| None -> []
			| Some proc_specs -> 
				(List.iter (fun spec -> if (spec.n_post = []) then print_debug "Exists spec with no post.") proc_specs.n_proc_specs;
				(* symbolically evaluate the args *)
				let le_args = List.map (fun e -> symb_evaluate_expr symb_state anti_frame e) e_args in
				let new_symb_states = find_and_apply_spec s_prog.program proc_name proc_specs symb_state anti_frame le_args in
				if ((List.length new_symb_states) = 0) then 
					(print_endline (Printf.sprintf "No precondition found for procedure %s. Ending symbolic execution." proc_name);			
					Bi_Utils.update_failures proc.proc_name "No precondition found for procedure.";
					[])
				else 
					(let list_result_states = List.map
						(fun (symb_state, anti_frame, ret_flag, ret_le) ->
							try 
								(let ret_type, _, _ =	type_lexpr (get_gamma symb_state) ret_le in
								store_put (get_store symb_state) x ret_le;
								update_gamma (get_gamma symb_state) x ret_type;
								let new_search_info = update_vis_tbl search_info (copy_vis_tbl search_info.vis_tbl) in
								(match ret_flag, j with
								| Normal, _ ->
									symb_evaluate_next_cmd s_prog proc spec new_search_info symb_state anti_frame i (i+1)
								| Error, None -> raise (Failure (Printf.sprintf "Procedure %s may return an error, but no error label was provided." proc_name))
								| Error, Some j ->
									symb_evaluate_next_cmd s_prog proc spec new_search_info symb_state anti_frame i j))
							with e -> 
								print_endline (Printf.sprintf "Symbolic execution of this specification for %s failed with the msg %s. Ending symbolic execution." proc_name (Printexc.to_string e));
								Bi_Utils.update_failures proc.proc_name (Printexc.to_string e);
								[])
						new_symb_states in
					List.concat list_result_states))
	 	in

	(* symbolically evaluate a phi command *)
	let symb_evaluate_phi symb_state anti_frame x x_arr : ((symbolic_state * symbolic_state * jsil_return_flag) list) =
		let cur_proc_name = proc.proc_name in
		let cur_which_pred =
			try Hashtbl.find s_prog.which_pred (cur_proc_name, prev, i)
			with _ ->  raise (Failure (Printf.sprintf "which_pred undefined for command: %s %d %d" cur_proc_name prev i)) in
		let expr = x_arr.(cur_which_pred) in
		let le = symb_evaluate_expr symb_state anti_frame expr in
		let te, _, _ =	type_lexpr (get_gamma symb_state) le in
		store_put (get_store symb_state) x le;
		update_gamma (get_gamma symb_state) x te;
		symb_evaluate_next_cmd s_prog proc spec search_info symb_state anti_frame i (i+1)
		in 

	let symb_state = Simplifications.simplify_ss symb_state (Some (Some spec.n_lvars)) in
	let anti_frame = Simplifications.simplify_ss anti_frame (Some (Some spec.n_lvars)) in

	print_symb_state_and_cmd symb_state anti_frame;
	let metadata, cmd = get_proc_cmd proc i in
	mark_as_visited search_info i;
	match cmd with
	| SBasic bcmd ->
		let _ = symb_evaluate_bcmd bcmd symb_state anti_frame spec.n_lvars in
		symb_evaluate_next_cmd s_prog proc spec search_info symb_state anti_frame i (i+1)
	| SGoto j -> 
		symb_evaluate_next_cmd s_prog proc spec search_info symb_state anti_frame i j
	| SGuardedGoto (e, j, k) -> symb_evaluate_guarded_goto symb_state anti_frame e j k
	| SCall (x, e, e_args, j) -> symb_evaluate_call symb_state anti_frame x e e_args j
	| SPhiAssignment (x, x_arr) -> symb_evaluate_phi symb_state anti_frame x x_arr
	| _ -> raise (Failure "not implemented yet");
	

(**
	Symbolically evaluate the next command of the program
	
	@param s_prog      Extended JSIL program
	@param proc        The procedure that is being executed
	@param spec        The specification to be verified
	@param search_info Something for the dot graphs
	@param symb_state  Current symbolic state
	@param cur         Index of the current command
	@param next        Index of the next command
	
	@return symb_states The list of symbolic states resulting from the evaluation
*)
and symb_evaluate_next_cmd s_prog proc spec search_info symb_state anti_frame cur next : ((symbolic_state * symbolic_state * jsil_return_flag) list) =
	(* Get the current command and the associated metadata *)
	let metadata, cmd = get_proc_cmd proc cur in
	(* Evaluate logic commands, if any *)
	let symb_states_with_spec_vars = symb_evaluate_logic_cmds s_prog metadata.post_logic_cmds [ symb_state, spec.n_lvars ] spec.n_subst in
	(* The number of symbolic states resulting from the evaluation of the logic commands *)
	let len = List.length symb_states_with_spec_vars in
	(* For each obtained symbolic state *) 
	let list_result_states = List.map
		(* Get the symbolic state *)
		(fun (symb_state, spec_vars) ->
			let search_info =
				if (len > 1) then 
					{ search_info with vis_tbl = (copy_vis_tbl search_info.vis_tbl) }
				else search_info in
			(* Go bravely into the continuation *)
			let spec = { spec with n_lvars = spec_vars } in
			let (_,_,result_states) = symb_evaluate_next_cmd_cont s_prog proc spec search_info symb_state anti_frame cur next in
			result_states)
		symb_states_with_spec_vars in
	List.concat list_result_states

(**
	Continuation of symbolic evaluation of the next command of the program
	
	@param s_prog      Extended JSIL program
	@param proc        The procedure that is being executed
	@param spec        The specification to be verified
	@param search_info Something for the dot graphs
	@param symb_state  Current symbolic state
	@param cur         Index of the current command
	@param next        Index of the next command
	
	@return symb_states The list of symbolic states resulting from the evaluation
*)
and symb_evaluate_next_cmd_cont 
				(s_prog      : symb_jsil_program)
				(proc        : jsil_procedure)
				(spec        : jsil_n_single_spec) 
				(search_info : symbolic_execution_search_info)
				(symb_state  : symbolic_state) 
				(anti_frame  : symbolic_state)
				(cur         : int)
				(next        : int) 
										: bool * (string option) * ((symbolic_state * symbolic_state * jsil_return_flag) list) =

	(* i1: Has the current command already been visited? *)
	let is_visited i = Hashtbl.mem search_info.vis_tbl i in

	let finish ret_flag = 
		let posts_and_afs = 
				(Bi_Structural_Entailment.bi_unify_symb_state_against_post 
					proc.proc_name spec symb_state anti_frame ret_flag search_info js) in
		let result_states = 
				List.fold_left 
					(fun ac (ac_post, ac_af) -> (ac_post, ac_af, ret_flag) :: ac)
					[]
					posts_and_afs in 
		Symbolic_Traces.create_info_node_from_post search_info spec.n_post ret_flag true;
		(true, None, result_states) in

	(* i2: Have we reached the return label? *)
	(if (Some cur = proc.ret_label) then
		(* i2: YES: Unify the final symbolic state against the postcondition *)
		finish Normal
	else 
		(* i2: NO: Have we reached the error label? *)
		(if (Some cur = proc.error_label) then
			(* i3: YES: Unify the final symbolic state against the postcondition *)
			finish Error
			(* i3: NO: The control did not reach the end of the symbolic execution *)
		else
		begin
			(* Get the next command and its metadata *)
			let metadata, cmd = get_proc_cmd proc next in
			(* i1: YES: We have visited the current command and are in a loop *)
			if (is_visited next) then
				(* Get the invariant *)
				match (metadata.invariant) with
				(* No invariant, throw an error *)
				| None -> print_endline "Already visited current command, recurvsive. Ending symbolic execution."; (true, None, []) (*raise (Failure "back edges need to point to commands annotated with invariants")*)
				(* Invariant present, check if the current symbolic state entails the invariant *)
				| Some a ->
					(* check if the current symbolic state entails the invariant *)
					Printf.printf "LOOP: I found an invariant: %s\n" (JSIL_Print.string_of_logic_assertion a false); 
					let new_symb_state, _ = Normaliser.normalise_postcondition a spec.n_subst spec.n_lvars (get_gamma spec.n_pre) in
					let new_symb_state, _, _, _ = Simplifications.simplify_symb_state None (DynArray.create()) (SS.empty) new_symb_state in
					try (let _ = Structural_Entailment.fully_unify_symb_state new_symb_state symb_state spec.n_lvars !js in (true, None, [])) with
						| SymbExecFailure failure -> 
								let str_of_fail = Symbolic_State_Print.print_failure failure in
								print_debug str_of_fail;
								(false, Some str_of_fail, [])
			else
				(* i1: NO: We have not visited the current command *)
				(* Understand the symbolic state *)
				let symb_state =
					(* Get the invariant *)
					match (metadata.invariant) with
					(* No invariant, proceed *)
					| None -> symb_state
					(* Invariant present, check if the current symbolic state entails the invariant *)
					| Some a ->
						Printf.printf "NO LOOP: I found an invariant: %s\n" (JSIL_Print.string_of_logic_assertion a false); 
						let new_symb_state, _ = Normaliser.normalise_postcondition a spec.n_subst spec.n_lvars (get_gamma spec.n_pre) in
						let new_symb_state, _, _, _ = Simplifications.simplify_symb_state (Some None) (DynArray.create()) (SS.empty) new_symb_state in
						(match (Structural_Entailment.unify_symb_state_against_invariant symb_state new_symb_state spec.n_lvars SS.empty) with
						(* If it does, replace current symbolic state with the invariant *)
						| Some new_symb_state -> new_symb_state
						| None -> raise (Failure "unification with invariant failed")) in

				(* Evaluate logic commands, if any *)
				let symb_states_with_spec_vars = symb_evaluate_logic_cmds s_prog metadata.pre_logic_cmds [ symb_state, spec.n_lvars ] spec.n_subst in
				(* The number of symbolic states resulting from the evaluation of the logic commands *)
				let len = List.length symb_states_with_spec_vars in
				(* For each obtained symbolic state *) 
				let list_result_states = (List.map
					(* Get the symbolic state *)
					(fun (symb_state, spec_vars) ->
						(* Construct the search info for the next command *)
						let vis_tbl = if (len > 1) then (copy_vis_tbl search_info.vis_tbl) else search_info.vis_tbl in
						let info_node = Symbolic_Traces.create_info_node_from_cmd search_info symb_state cmd next in
						let new_search_info = update_search_info search_info info_node vis_tbl in
						(* Actually evaluate the next command *) 
						print_debug 
							(Printf.sprintf  "AF in symb_evaluate_next_cmd_cont:\n%s\n" 
								(Symbolic_State_Print.string_of_shallow_symb_state anti_frame));
						let spec = { spec with n_lvars = spec_vars } in
						symb_evaluate_cmd s_prog proc spec new_search_info symb_state anti_frame next cur)
					symb_states_with_spec_vars) in
				let result_states = List.concat list_result_states in
				(true, None, result_states)
		end
		);
	)

(**
	Symbolic execution of a JSIL procedure
	
	@param s_prog       Extended JSIL program
	@param proc_name    Name of the procedure
	@param spec         The specification to be verified
	@param i            Index of the current specification
	@param pruning_info Pruning information
	
	@return search_dot_graph The dot graph of the symbolic execution
	@return success          Success indicator
	@return failure_msg      Error message in case of failure
*)
let symb_evaluate_proc s_prog proc_name spec i pruning_info 
							: (string option) * bool * (string option) * (((symbolic_state * symbolic_state * jsil_return_flag) list) option)=
	let sep_str = "----------------------------------\n" in
	print_endline (Printf.sprintf "%s" (sep_str ^ sep_str ^ "Symbolic execution of " ^ proc_name));

	let node_info = Symbolic_Traces.create_info_node_aux spec.n_pre 0 (-1) "Precondition" in
	let search_info = make_symb_exe_search_info node_info pruning_info i in
	let process_failure search_info msg_option spec i = 
		let msg = Option.get(msg_option) in
		print_endline (Printf.sprintf " !!!!( ERROR: The evaluation of this proc gave an error: %d %s )!!!!" i msg);
		Symbolic_Traces.create_info_node_from_error search_info msg;
		Symbolic_Traces.create_info_node_from_post search_info spec.n_post spec.n_ret_flag false;
 	in

	(* Get the procedure to be symbolically executed *)
	let proc = get_proc s_prog.program proc_name in
	let success, failure_msg, result_states =
		(try
			print_debug (Printf.sprintf "Initial symbolic state:\n%s" 
				(Symbolic_State_Print.string_of_shallow_symb_state spec.n_pre));
			let symb_state = copy_symb_state spec.n_pre in
			(* Empty initial anti-frame*)
			let anti_frame = init_symb_state () in
			print_debug 
							(Printf.sprintf  "AF in symb_evaluate_proc :\n%s\n" 
								(Symbolic_State_Print.string_of_shallow_symb_state anti_frame));
			(* Symbolically execute the procedure *)
			let (success, msg, result_states) = 
				symb_evaluate_next_cmd_cont s_prog proc spec search_info symb_state anti_frame (-1) 0 in
			if (success) then 
				(* Symbolic execution was successful *)
				success, None, Some result_states
			else
			begin
				process_failure search_info msg spec i;
				success, msg, Some result_states
			end
		(* An error occurred during the symbolic execution *)
		with Failure msg ->
			(process_failure search_info (Some msg) spec i;
			false, Some msg, None)) in
	let proc_name = Printf.sprintf "Spec_%d_of_%s" i proc_name in
	(* Create the dot graph of the symbolic execution *)
	let search_dot_graph = Some (Symbolic_State_Print.dot_of_search_info search_info proc_name) in
	print_debug (Printf.sprintf "%s" (sep_str ^ sep_str ^ sep_str));
	(* Return *)
	search_dot_graph, success, failure_msg, result_states

let add_new_spec proc_name proc_params pre_post result_states new_spec_tbl = 
	(* Create new specification is there is an anti frame *)
	let specs = (List.map (fun (post_state, anti_frame, ret_flag) ->
					(* The new precondition = old precondition * anti frame *)
					(* The new postconition is the final state after evaluation *)
					let new_pre = Symbolic_State_Utils.bi_merge_symb_states anti_frame pre_post.n_pre in 
					let new_pre, simplification_subst = Simplifications.simplify_ss_with_subst new_pre (Some None) in
					(*let more_pfs = pf_of_substitution simplification_subst in 
					extend_symb_state_with_pfs new_pre (pfs_of_list more_pfs); *) 
					let post_subst = symb_state_substitution post_state simplification_subst true in 
					(*remove_concrete_values_from_the_store new_pre;*)
					let (pre_subst,post_subst) = Symbolic_State_Utils.symb_state_lvars_to_svars new_pre post_subst in
					Simplifications.naively_infer_type_information_symb_state pre_subst; 
					let pre_lvars = Symbolic_State_Utils.get_symb_state_lvars pre_subst in
					Simplifications.naively_infer_type_information_symb_state post_subst; 
					let post_lvars = Symbolic_State_Utils.get_symb_state_lvars post_subst in
					{
						n_pre        = pre_subst;
						n_post       = [post_subst];
						n_ret_flag   = ret_flag;
						n_lvars      = pre_lvars;
						n_post_lvars = [post_lvars];
						n_subst      = Hashtbl.create small_tbl_size
					}
			  	) result_states) in
	let spec = try Some (Hashtbl.find new_spec_tbl proc_name) with Not_found -> None in 
	(match spec with 
	| Some spec -> 
		let specs = List.append specs spec.n_proc_specs in
		Hashtbl.replace new_spec_tbl proc_name {
			n_spec_name = proc_name;
			n_spec_params = proc_params;
			n_proc_specs = specs;
		};
	| None -> 
		Hashtbl.add new_spec_tbl proc_name {
			n_spec_name = proc_name;
			n_spec_params = proc_params;
			n_proc_specs = specs;
		};);
	()

(** 
	Symbolic execution of a given set of JSIL procedures

	@param prog            JSIL program 
	@param procs_to_verify The list of procedures of the JSIL program to be symbolically verified
	@param spec_table      The table of specifications associated with the JSIL program
	@param which_pred      The predecessor graph
	@param pred_defs       Predicate definitions
	
	@return results_str      Symbolic execution in string format
	@return dot_graphs       Dot graph of the symbolic execution
	@return complete_success Indicator of complete success
	
	TODO: Construct call graph, do dfs, do in that order
*)
let sym_run_procs prog procs_to_verify spec_table which_pred pred_defs =
	let new_spec_tbl = Hashtbl.create small_tbl_size in
	Hashtbl.iter (fun spec_name spec -> if (not (List.mem spec_name procs_to_verify)) then 
											Hashtbl.add new_spec_tbl spec_name spec
				 ) spec_table; 	
	(* Normalise predicate definitions *)
	let n_pred_defs = Normaliser.normalise_predicate_definitions pred_defs in
	(* Construct corresponding extended JSIL program *)
	let s_prog = {
		program = prog;
		which_pred = which_pred;
		spec_tbl = new_spec_tbl;
		pred_defs = n_pred_defs
	} in
	let pruning_info = init_post_pruning_info () in
	(* Iterate over the specification table *)
	let results = List.fold_left
		(fun ac_results proc_name -> 
		let proc = get_proc s_prog.program proc_name in
	  	let spec = try Some (Hashtbl.find spec_table proc_name) with Not_found -> None in 
			match spec with 
			| Some spec -> 
				(* Get list of pre-post pairs      *)
				let pre_post_list = spec.n_proc_specs in
				(* Iterate over the pre-post pairs *)
				let _, results =
					List.fold_left
					(* For each pre-post pair *)
					(fun (i,ac) pre_post ->
						(* TODO: we should remove this line - but first we need to make sure we are not updating the spec by mistake during symb execution *)
						let new_pre_post = Symbolic_State_Utils.copy_single_spec pre_post in
						(* Symbolically execute the procedure given the pre and post *)
						let dot_graph, success, failure_msg, result_states = symb_evaluate_proc s_prog proc_name new_pre_post i pruning_info in
						if (Option.is_some(result_states)) then  
							let suc_result_states = Option.get result_states in
							if ((List.length suc_result_states) = 0) then
								(i+1, ac)
							else 
								(add_new_spec proc_name proc.proc_params  pre_post suc_result_states new_spec_tbl;
								(i+1, (proc_name, i, pre_post, success, failure_msg, dot_graph) :: ac))
						else 
							(i+1, (proc_name, i, pre_post, success, failure_msg, dot_graph) :: ac))
					(0, []) pre_post_list in
				let results_str, dot_graphs =  Symbolic_State_Print.string_of_symb_exe_results results in
				(* Concatenate symbolic trace *)
				ac_results @ results
			| None -> 
				let new_pre_post = Bi_Symbolic_State_Functions.create_new_spec () in
				let dot_graph, success, failure_msg, result_states = symb_evaluate_proc s_prog proc_name new_pre_post 0 pruning_info in
				if (Option.is_some(result_states)) then  
					(let suc_result_states = Option.get result_states in
					if ((List.length suc_result_states) = 0) then
						ac_results
					else
						(add_new_spec proc_name proc.proc_params new_pre_post suc_result_states new_spec_tbl;
						(proc_name, 0, new_pre_post, success, failure_msg, dot_graph) :: ac_results))
				else
					(proc_name, 0, new_pre_post, success, failure_msg, dot_graph) :: ac_results)
		[]
		procs_to_verify in 
	(* Return *)
	new_spec_tbl, procs_to_verify, results
