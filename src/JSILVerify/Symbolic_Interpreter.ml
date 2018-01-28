open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils

let js = ref false


let domain_from_single_lit lit = Some (LESet [ (LLit (String lit)) ])

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
let rec symb_evaluate_expr 
		(store : symbolic_store) (gamma : typing_environment) 
		(pure_formulae : pure_formulae) (expr : jsil_expr) : jsil_logic_expr =
let f = symb_evaluate_expr store gamma pure_formulae in
	match expr with
	(* Literals: Return the literal *)
	| Literal lit -> LLit lit

  	(* Variables:
	     a) If a variable is already in the store, return the variable
		 b) Otherwise, it dies! *)
	| Var x -> store_get store x

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
			| LstCons ->
				(match nle2 with
				| LEList les -> LEList (nle1 :: les)
				| LLit (LList lits) ->
					let les2 = List.map (fun lit -> LLit lit) lits in
					LEList (nle1 :: les2)
				| _ -> LBinOp (nle1, op, nle2))
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

	| ESet es ->
		let les = List.map (fun e -> f e) es in
			LESet les

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


(************************************************)
(* SAFE Symbolic evaluation of JSIL expressions *)
(************************************************)
(*
	a) If the result of the evaluation is typable, then any constraints produced by typing must also make sense
	b) Otherwise, variables are allowed to stay untyped
	c) Otherwise, an error is thrown
*)
let safe_symb_evaluate_expr 
		(store         : symbolic_store)
		(gamma         : typing_environment) 
		(pure_formulae : pure_formulae) 
		(expr          : jsil_expr) : jsil_logic_expr * (jsil_type option) * bool =
	let nle = symb_evaluate_expr store gamma pure_formulae expr in
	let nle = Simplifications.replace_nle_with_lvars pure_formulae nle in
	let nle_type, is_typable, constraints = type_lexpr gamma nle in
	let is_typable = is_typable && ((List.length constraints = 0) || (Pure_Entailment.check_entailment SS.empty (pfs_to_list pure_formulae) constraints gamma)) in
	if (is_typable) then
		nle, nle_type, true
	else
		(match nle with
		| LVar _ ->  nle, None, false
		| _ ->
				let gamma_str = Symbolic_State_Print.string_of_gamma gamma in
				let pure_str = Symbolic_State_Print.string_of_pfs pure_formulae in
				let msg = Printf.sprintf "The logical expression %s is not typable in the typing enviroment: %s \n with the pure formulae %s" (JSIL_Print.string_of_logic_expression nle) gamma_str pure_str in
				raise (Failure msg))


(**********************************************)
(* Symbolic evaluation of JSIL basic commands *)
(**********************************************)
let symb_evaluate_bcmd 
		(bcmd       : jsil_basic_cmd) 
		(symb_state : symbolic_state) : jsil_logic_expr =
	let heap, store, pure_formulae, gamma, _ = symb_state in
	let ssee = safe_symb_evaluate_expr store gamma pure_formulae in
	match bcmd with
	(* Skip: skip;
			Always return empty *)
	| Skip ->
		LLit Empty

  	(* Assignment: x = e;
			a) Safely evaluate e to obtain nle and its type tle
			b) Update the abstract store with [x |-> nle]
			c) Update the typing environment with [x |-> tle]
			d) Return nle *)
	| Assignment (x, e) ->
		let nle, tle, _ = ssee e in
		store_put store x nle;
		nle

	(* Object creation: x = new ();
			a) Create fresh object location #l and add it to the heap
			b) Set (#l, "@proto") -> null in the heap
			c) Update the abstract store with [x |-> #l]
			e) Add the fact that the new location is not $lg to the pure formulae
			f) Return the new location
	*)
	| New x ->
		let new_loc = fresh_aloc () in
		heap_put heap new_loc []  (domain_from_single_lit JS2JSIL_Constants.internalProtoFieldName);
		heap_put_fv_pair heap new_loc (LLit (String (JS2JSIL_Constants.internalProtoFieldName))) (LLit Null); 
		store_put store x (ALoc new_loc);
		(* THIS NEEDS TO CHANGE ASAP ASAP ASAP!!! *)
		DynArray.add pure_formulae (LNot (LEq (ALoc new_loc, LLit (Loc JS2JSIL_Constants.locGlobName))));
		ALoc new_loc
		
	| MetaData (x, md)

	| Extensible (x)

  (* Property lookup: x = [e1, e2];
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) Safely evaluate e2 to obtain the property name ne2 and its type te2
			c) If ne1 is not a literal location or an abstract location, throw an error
			d) Otherwise, try to find the value ne of the property ne2 of object ne1
			e) If successful, update the store with [x |-> ne]
			f) Return ne
	*)
	| Lookup (x, e1, e2) ->
		let ne1, te1, _ = ssee e1 in
		let ne2, te2, _ = ssee e2 in
		let l = 
			match Normaliser.resolve_location_from_lexpr pure_formulae ne1 with
			| Some l -> l 
			| None   -> 
				let msg = Printf.sprintf "Lookup. LExpr %s does NOT denote a location" (JSIL_Print.string_of_logic_expression ne1) in 
				raise (Symbolic_State_Utils.SymbExecFailure msg) in
		let ne = Symbolic_State_Utils.sheap_get pure_formulae gamma heap l ne2  in
		store_put store x ne;
		ne

  (* Property assignment: [e1, e2] := e3;
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) Safely evaluate e2 to obtain the property name ne2 and its type te2
			c) Safely evaluate e3 to obtain the value ne3 to be assigned
			d) If ne1 is not a literal location or an abstract location, throw an error
			e) Update the heap with (ne1, ne2) -> ne3
			f) Return ne3
	*)
	| Mutation (e1, e2, e3) ->
		let ne1, t_le1, _ = ssee e1 in
		let ne2, t_le2, _ = ssee e2 in
		let ne3, _, _ = ssee e3 in
		let l = 
			match Normaliser.resolve_location_from_lexpr pure_formulae ne1 with
			| Some l -> l 
			| None   -> 
				let msg = Printf.sprintf "Mutation. LExpr %s does NOT denote a location" (JSIL_Print.string_of_logic_expression ne1) in 
				raise (Symbolic_State_Utils.SymbExecFailure msg) in
		Symbolic_State_Utils.sheap_put pure_formulae gamma heap l ne2 ne3; 
		ne3

  	(* Property deletion: delete(e1, e2)
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) Safely evaluate e2 to obtain the property name ne2 and its type te2
			c) If ne1 is not a literal location or an abstract location, throw an error
			e) Delete (ne1, ne2) from the heap
			f) Return true
	*)
	| Delete (e1, e2) ->
		let ne1, t_le1, _ = ssee e1 in
		let ne2, t_le2, _ = ssee e2 in
		let l = 
			match Normaliser.resolve_location_from_lexpr pure_formulae ne1 with
			| Some l -> l 
			| None   -> 
				let msg = Printf.sprintf "Delete. LExpr %s does NOT denote a location" (JSIL_Print.string_of_logic_expression ne1) in 
				raise (Symbolic_State_Utils.SymbExecFailure msg) in
		Symbolic_State_Utils.sheap_put pure_formulae gamma heap l ne2 LNone; 
		LLit (Bool true)

  	(* Object deletion: deleteObj(e1)
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) If ne1 is not a literal location or an abstract location, throw an error
			c) If the object at ne1 does not exist in the heap, throw an error
			c) Delete the entire object ne1 from the heap
			d) Return true *)
	| DeleteObj e1 ->
		let ne1, t_le1, _ = ssee e1 in
		let l = 
			match Normaliser.resolve_location_from_lexpr pure_formulae ne1 with
			| Some l -> l 
			| None   -> 
				let msg = Printf.sprintf "DeleteObj. LExpr %s does NOT denote a location" (JSIL_Print.string_of_logic_expression ne1) in 
				raise (Symbolic_State_Utils.SymbExecFailure msg) in
		(match (heap_has_loc heap l) with
		 | false -> raise (Symbolic_State_Utils.SymbExecFailure (Printf.sprintf "Attempting to delete an inexistent object: %s" (JSIL_Print.string_of_logic_expression ne1)))
		 | true  -> heap_remove heap l; LLit (Bool true));

  	(* Property existence: x = hasField(e1, e2);
			a) Safely evaluate e1 to obtain the object location ne1 and its type te1
			b) Safely evaluate e2 to obtain the property name ne2 and its type te2
			c) If ne1 is not a literal location or an abstract location, throw an error
			d) Otherwise, understand if the object ne1 has the property ne2 and store that result in res;
			e) If conclusive, update the store with [x |-> res] and return res
			f) Otherwise, return unknown
			e) If successful, update the store with [x |-> ne]
			f) Return ne
	*)
	| HasField (x, e1, e2) ->
		let ne1, t_le1, _ = ssee e1 in
		let ne2, t_le2, _ = ssee e2 in
		let l = 
			match Normaliser.resolve_location_from_lexpr pure_formulae ne1 with
			| Some l -> l 
			| None   -> 
				let msg = Printf.sprintf "DeleteObj. LExpr %s does NOT denote a location" (JSIL_Print.string_of_logic_expression ne1) in 
				raise (Symbolic_State_Utils.SymbExecFailure msg) in
	
		let f_val = Symbolic_State_Utils.sheap_get pure_formulae gamma heap l ne2 in
		(match Symbolic_State_Utils.lexpr_is_none pure_formulae gamma f_val  with
		| Some b ->
			let ret_lit = LLit (Bool (not b)) in
			store_put store x ret_lit;
			ret_lit
		| None ->
			let ret_lexpr = LUnOp (Not, LBinOp (f_val, Equal, LNone)) in
			store_put store x ret_lexpr;
			ret_lexpr)
	
	| _ -> raise (Failure (Printf.sprintf "Unsupported basic command"))


(**********************************************)
(** Given a symb_state and a proc spec, find the single specs that are 
    entailed by the symb_state, compute the frames, and compute the 
    symb_states obtained by merging the frames with the appropriate 
    post-conditions
 *)
let find_and_apply_spec 
		(prog       : jsil_program) 
		(proc_name  : string) 
		(proc_specs : jsil_n_spec)
		(symb_state : symbolic_state) 
		(le_args    : jsil_logic_expr list) : bool * ((symbolic_state * jsil_return_flag * jsil_logic_expr) list) =

	print_debug (Printf.sprintf "Entering find_and_apply_spec: %s." proc_name);

	(*  Step 0: create a symb_state with the appropriate calling store
	    --------------------------------------------------------------
	    * Get the parameter list of the procedure to call 
	    * Create the symbolic store mapping the formal arguments to 
	      to the corresponding logical expressions
	    * Create a new symb_state with the new calling store    *)
	let proc              = get_proc prog proc_name in
	let proc_args         = get_proc_args proc in
	let new_store         = store_init proc_args le_args in
	let symb_state_caller = ss_replace_store symb_state new_store in

	(*  Step 1: find the spec(s) of the called function whose preconditions 
	    match the caller's symbolic state. 
	    ----------------------------------------------------------------------------------------
	    We consider two types of matches: 
	     * Complete match   - both the spatial part and the pure part match 
	     * Incomplete match - the pure part of the pre- is not entailed by the current symb_state
	    ---------
	    When we have complete match, we just update the current symbolic state with 
	    the postcondition of the function being called. 
	    When we have no complete match, we branch on all complete matches (soundness 
	    issue...)  
	*)
	let rec find_correct_specs 
			(spec_list : jsil_n_single_spec list) 
			(ac_frames : (bool * jsil_n_single_spec * symbolic_state_frame) list) : (bool * jsil_n_single_spec * symbolic_state_frame) list =
		match spec_list with
		| [] -> ac_frames
		| spec :: rest_spec_list ->
			print_debug (Printf.sprintf "------------------------------------------");
			print_debug (Printf.sprintf "Entering find_correct_specs with the spec:");
			print_debug (Printf.sprintf "------------------------------------------");
			print_debug (Printf.sprintf "Pre:\n%sPosts:\n%s"
				(Symbolic_State_Print.string_of_symb_state spec.n_pre)
				(Symbolic_State_Print.string_of_symb_state_list spec.n_post));

			try (
				let outcome, (framed_heap, framed_preds, subst, pf_discharges, new_gamma) = 
					Spatial_Entailment.unify_symb_states spec.n_unification_plan None spec.n_pre symb_state_caller in
				(match outcome with
				| true ->
				    (*  Complete Match: Return immediately, ignoring the previous partial matches that we may 
				        have previously encountered
				     *)
					print_debug (Printf.sprintf "COMPLETE match");
					print_debug (Printf.sprintf "The pre of the spec that completely matches is:\n%s" (Symbolic_State_Print.string_of_symb_state spec.n_pre));
					print_debug (Printf.sprintf "The number of posts is: %d" (List.length spec.n_post));
					[ (true, spec, (framed_heap, framed_preds, subst, pf_discharges, new_gamma)) ]
				| false ->
					(*  Partial Match: Two cases to consider
						   - If the pure formulae of the pre- are compatible with the pure formuale 
						     of the caller's symb_state, we add the current frame to the ac_frames and 
						     continue searching for matches 
						   - If the pure formulae of the pre- are not compatible with the pure formulae
						   	 of the caller's symb_state, we conitnue searching for matches, without 
						   	 updating the ac_frames
				     *)
					if (Symbolic_State_Utils.compatible_pfs symb_state spec.n_pre subst)
						then (
							print_debug (Printf.sprintf "COMPATIBLE PARTIAL match");
							find_correct_specs rest_spec_list ((false, spec, (framed_heap, framed_preds, subst, pf_discharges, new_gamma)) :: ac_frames)
						) else (
							print_debug (Printf.sprintf "INCOMPATIBLE PARTIAL match");
							find_correct_specs rest_spec_list ac_frames
						)))
			with Spatial_Entailment.UnificationFailure _ -> 
				print_debug (Printf.sprintf "I found a NON-match");
				find_correct_specs rest_spec_list ac_frames in

	
	(*  Step 2: Apply the correct specs 
	    -----------------------------------------------------------------------------
	    We consider two types of matches: 
	     * Complete match   - If we have a complete match, we just combine the 
	       postcondition of the spec with the appropriate frame 

	     * Incomplete match - If we have multiple incomplete matches, we combine 
	       the postcondition of each spec with the appropriate frame, and we 
	       further extend it 
	    ---------
	*)
	let rec apply_correct_specs 
			(ext_frames : (bool * jsil_n_single_spec * symbolic_state_frame) list) : bool * ((symbolic_state * jsil_return_flag * jsil_logic_expr) list) =
		print_debug_petar (Printf.sprintf "Entering apply_correct_specs.");
		match ext_frames with
		| [ ] -> true, [ ]
		| [ (true, spec, frame) ] ->
			print_debug (Printf.sprintf "TOTAL MATCH!!!!");
			(* Total Match - combine the frame with the postcondition of the spec *)
			true, Symbolic_State_Utils.merge_symb_state_with_posts proc spec symb_state frame
	 	| _ ->
			let lpm = List.length ext_frames in
			print_debug (Printf.sprintf "PARTIAL MATCH of length: %d" lpm);
			(match lpm with
			| 1 -> false, []
			| _ ->
				(* Partial Match - combine the frame with the postcondition of the spec
				   AND add the pure part of the precondition because it is not entailed by 
				   the current state *)
				(* TODO: check if the disjunction of the preconditions of the partial matches
				   is a tautology *)
				let symb_states_and_ret_lexprs : (symbolic_state * jsil_return_flag * jsil_logic_expr) list = 
					List.concat (List.map (fun (_, spec, frame) -> 
						let symb_states_and_ret_lexprs = 
							Symbolic_State_Utils.merge_symb_state_with_posts proc spec symb_state frame in
						let _, _, subst, _, _ = frame in  
						List.concat (List.map (fun (symb_state, ret_flag, ret_lexpr) -> 
							let (is_sat, new_symb_state) = Symbolic_State_Utils.enrich_pure_part symb_state spec.n_pre subst in
							if (is_sat) then [ (new_symb_state, ret_flag, ret_lexpr) ] else [ ]) symb_states_and_ret_lexprs)
						) ext_frames) in
				false, (List.map (fun (symb_state, ret_flag, ret_lexpr) -> 
					(* Code for PETAR to clean up *)
					let pfs  = ss_pfs symb_state in 
					let rpfs = DynArray.map (fun x -> Simplifications.reduce_assertion_no_store (ss_gamma symb_state) pfs x) pfs in
					Simplifications.sanitise_pfs_no_store (ss_gamma symb_state) rpfs;
					let symb_state' = ss_replace_pfs symb_state rpfs in 
					let ret_lexpr'  = Simplifications.reduce_expression_no_store_no_gamma_no_pfs ret_lexpr in 
					(symb_state', ret_flag, ret_lexpr')
				) symb_states_and_ret_lexprs)) in  		

	(* DOING IT*)
	let frames = find_correct_specs proc_specs.n_proc_specs [] in
	apply_correct_specs frames


exception SuccessfullyFolded of (symbolic_state * SS.t * symbolic_execution_context) option



(**********************************************)
(** Fold a predicate assertion recursively 
 *)
let rec fold_predicate 
	(pred_name    : string) 
	(pred_defs    : ((string option) * symbolic_state * (jsil_logic_assertion list)) array)  
	(symb_state   : symbolic_state) 
	(params       : string list) 
	(args         : jsil_logic_expr list) 
	(spec_vars    : SS.t) 
	(existentials : SS.t option) 
	(search_info  : symbolic_execution_context) : (symbolic_state * SS.t * symbolic_execution_context) option =

	
	let update_symb_state_after_folding symb_state framed_heap framed_preds new_pfs new_gamma =
		print_time_debug ("update_symb_state_after_folding:");
		let symb_state = ss_replace_heap symb_state framed_heap in
		let symb_state = ss_replace_preds symb_state framed_preds in
		let symb_state = ss_replace_gamma symb_state new_gamma in
		ss_extend_pfs symb_state (pfs_of_list new_pfs);
		symb_state in


	let process_missing_pred_assertion
			(missing_pred_args : jsil_logic_expr list)  (subst : substitution) (existentials : SS.t)
			(symb_state : symbolic_state) (framed_heap : symbolic_heap) (framed_preds : predicate_set) 
			(pf_discharges : jsil_logic_assertion list) (new_gamma : typing_environment) : symbolic_state * (jsil_logic_expr list) * SS.t = 
		
		let missing_pred_args = List.map (JSIL_Logic_Utils.lexpr_substitution subst false) missing_pred_args in
				
		(* 1. Remove from the symb_state the spatial resources corresponding to the folded predicate *)
		let new_symb_state          = update_symb_state_after_folding symb_state framed_heap framed_preds pf_discharges new_gamma in
				
		(* 2. After folding, we may be able to determine the exact expressions for some of the
			existentials. These existentials cease to be existentials. We need to substitute 
			them on the symb_state and on the arguments for the missing predicate assertion  *)
		let new_symb_state, e_subst = Simplifications.simplify_ss_with_subst new_symb_state (Some None) in
		let e_subst                 = filter_substitution (fun v le -> (SS.inter existentials (get_lexpr_lvars le)) = SS.empty) e_subst in 				
		let e_subst_domain          = get_subst_vars (fun x -> false) e_subst in 
		let existentials'           = SS.filter (fun v -> (not (SS.mem v e_subst_domain))) existentials in
		let e_subst'                = filter_substitution_set existentials' e_subst in				
		let new_symb_state          = ss_substitution e_subst' true new_symb_state in
		let missing_pred_args       = List.map (fun le -> JSIL_Logic_Utils.lexpr_substitution e_subst' true le) missing_pred_args in
				
		(* Print useful INFO *)
		(* print_debug (Printf.sprintf "Old exists: %s" (String.concat "," (SS.elements existentials)));
		print_debug (Printf.sprintf "New subst: %s" (Symbolic_State_Print.string_of_substitution e_subst'));
		print_debug (Printf.sprintf "New exists: %s" (String.concat "," (SS.elements existentials')));
		print_debug (Printf.sprintf "Missing %s(%s)!!!"
			pred_name (String.concat ", " (List.map (fun le -> JSIL_Print.string_of_logic_expression le false) missing_pred_args)));
		print_debug (Printf.sprintf "Symbolic state after partial FOLDING:\n%s" (Symbolic_State_Print.string_of_shallow_symb_state new_symb_state)); *)
		
		new_symb_state, missing_pred_args, existentials' in 		


	(*  Step 0: create a symb_state with the appropriate calling store
	    --------------------------------------------------------------
	    * Create the symbolic store mapping the formal arguments of the 
	      predicate to be folded to the corresponding logical expressions
	    * Create a new symb_state with the new calling store    *)
	let new_store         = store_init params args in
	let symb_state_caller = ss_replace_store symb_state new_store in


	(* Step 1: compute the existentials
	    --------------------------------------------------------------
		* the existentials are the new logical variables used in the logical 
		  expressions given as parameters to the fold 
		  e.g. fold(#x, #y) if #y is not a spec var, then it is an existential 
		* the spec vars need to be updated with the existentials 
	*)
	let existentials =
		(match existentials with
		| None ->
			let symb_state_vars : SS.t = ss_lvars symb_state  in
			let args_vars       : SS.t = get_lexpr_list_lvars args in
			let existentials    : SS.t = SS.diff args_vars symb_state_vars in
			existentials
		| Some existentials -> existentials) in
	let new_spec_vars = SS.union spec_vars existentials in
	(* print_debug (Printf.sprintf "New spec vars (fold): %s" (String.concat ", " (SS.elements existentials))); *)

	(* Printing useful info *)
	let existentials_str = print_var_list (SS.elements existentials) in
	print_debug (Printf.sprintf ("\nFOLDING %s(%s) with the existentials %s in the symbolic state: \n%s\n")
	  pred_name
		(String.concat ", " (List.map JSIL_Print.string_of_logic_expression args))
		existentials_str
		(Symbolic_State_Print.string_of_symb_state symb_state));

	let rec one_step_fold  
			(index : int) 
			(search_info : symbolic_execution_context) : (symbolic_state * SS.t * symbolic_execution_context) option =
		
		print_time_debug ("check_pred_def:");
		let _, pred_def, pred_def_up = Array.get pred_defs index in
		print_debug (Printf.sprintf "----------------------------");
		print_debug (Printf.sprintf "Current pred symbolic state: %s" (Symbolic_State_Print.string_of_symb_state pred_def));
		
		let unifier = try (Some (Spatial_Entailment.unify_symb_states_fold pred_name existentials pred_def_up pred_def symb_state_caller))
			with | Spatial_Entailment.UnificationFailure _ -> None in
		
		(match unifier with
		| Some ((framed_heap, framed_preds, subst, pf_discharges, new_gamma), _, None) ->
		  	(* Fold Complete *)

		  	(* Remove from the symb_state the spatial resources corresponding to the folded predicate *)
		  	let new_symb_state = update_symb_state_after_folding symb_state framed_heap framed_preds pf_discharges new_gamma in
			
		  	(* Print useful INFO *)
			print_debug (Printf.sprintf "Folding Complete!");
			print_debug (Printf.sprintf "Symbolic state after FOLDING:\n%s" (Symbolic_State_Print.string_of_symb_state new_symb_state));
			Some (new_symb_state, new_spec_vars, search_info)

		| Some ((framed_heap, framed_preds, subst, pf_discharges, new_gamma), existentials, Some (missing_pred_name, missing_pred_args) ) 
				when missing_pred_name = pred_name ->
			
			print_debug (Printf.sprintf "Folding Incomplete. Missing %s(%s)\n"
				pred_name (String.concat ", " (List.map JSIL_Print.string_of_logic_expression missing_pred_args)));
		
			(* Fold Incomplete - Must recursively fold the predicate *)
			let new_symb_state, missing_pred_args, existentials' = 
				process_missing_pred_assertion missing_pred_args subst existentials symb_state framed_heap framed_preds pf_discharges new_gamma in 
			fold_predicate pred_name pred_defs new_symb_state params missing_pred_args new_spec_vars (Some existentials') search_info

		| _ -> 
			(* Fold Failed - we try to fold again removing a recursive call to the predicate from 
			   the predicate definition  *)
			print_debug (Printf.sprintf "Folding Failed."); 	

			let preds_pred_def  = (ss_preds pred_def) in 
			let preds_pred_def' = preds_copy preds_pred_def in 
			(match preds_remove_by_name preds_pred_def' pred_name with 
			| None -> None 
			| Some (_, missing_pred_args) -> (
				print_debug (Printf.sprintf "Going to remove %s(%s) and try to fold again"
					pred_name (String.concat ", " (List.map JSIL_Print.string_of_logic_expression missing_pred_args)));

				let pred_def' = ss_replace_preds pred_def preds_pred_def' in
				let unifier = try (Some (Spatial_Entailment.unify_symb_states_fold pred_name existentials (Normaliser.create_unification_plan pred_def' SS.empty) pred_def' symb_state_caller))
					with | Spatial_Entailment.UnificationFailure _ -> None in

				(match unifier with
				| Some ((framed_heap, framed_preds, subst, pf_discharges, new_gamma), new_existentials, None) ->
		  			(* We were able to fold the predicate up to a recursive call  *)
		  			(* Now we need to fold the recursive call                     *)

		  			let new_symb_state = update_symb_state_after_folding symb_state framed_heap framed_preds pf_discharges new_gamma in
		  			let new_symb_state', missing_pred_args, existentials' = 
						process_missing_pred_assertion missing_pred_args subst (SS.union existentials new_existentials) new_symb_state framed_heap framed_preds pf_discharges new_gamma in 
					fold_predicate pred_name pred_defs new_symb_state' params missing_pred_args new_spec_vars (Some existentials') search_info

		  		| _ -> None)))) in

	(* If there is a predicate definition to try first when folding, we do that *)
	(* If there is no predicate definition to try first or if the one that exists does 
	   not work, we iterate over all predicate definitions *)
	let search_info, check_me_first = sec_fold_pred_def search_info pred_name in 
	let pred_def_indexes            = Array.to_list (Array.init (Array.length pred_defs) (fun i -> i)) in 
	let ret, pred_def_indexes       = 
		if (0 <= check_me_first) 
			then (
				let pred_def_indexes = List.filter (fun i -> i <> check_me_first) pred_def_indexes in 
				let ret              = one_step_fold check_me_first search_info in 
				ret, pred_def_indexes
			) else None,  pred_def_indexes in 

	List.fold_left (fun ac i -> if (ac = None) then one_step_fold i search_info else ac) ret pred_def_indexes



(**********************************************)
(** Creates a substitution from the unfold_info to be used in the unfold. 
	Filters the pred definitions that do not correspond to the intended label. 
	SOUNDNESS ISSUE 
 *)
let use_unfold_info
	(unfold_info : (string * ((string * jsil_logic_expr) list)) option)
	(pred_defs   : ((string option) * symbolic_state * (jsil_logic_assertion list)) list)
	(subst       : substitution) : ((int * symbolic_state) list) * substitution =
	match unfold_info with
	| None                    ->
		let pred_defs' = List.mapi (fun i (os, a, _) -> (i, a)) pred_defs in
		pred_defs', init_substitution [] 
	| Some (def_id, mappings) ->
		let pred_defs' = List.mapi (fun i (os, a, _) -> i, os, a) pred_defs in 
		let pred_defs' =
			List.filter
				(fun (i, os, a) ->
					match os with
					| Some def_id' -> (def_id = def_id')
					| None         -> false) pred_defs' in
		let pred_defs' = List.map (fun (i, os, a) -> i, a) pred_defs' in
		let pat_subst = init_substitution3 mappings in
		pred_defs', pat_subst


(*---------------------------------------------------------------
	unfold_predicate. 
	Returns a list of triples containing:
		- an unfolded symbolic state
		- the new set of spec vars
		- the new search info 
----------------------------------------------------------------*)
let unfold_predicate
		(pred_name   : string)
		(pred_defs   : ((string option) * symbolic_state * (jsil_logic_assertion list)) list)
		(symb_state  : symbolic_state)
		(params      : string list)
		(args        : jsil_logic_expr list)
		(spec_vars   : SS.t)
		(search_info : symbolic_execution_context)
		(unfold_info : (string * ((string * jsil_logic_expr) list)) option) : (symbolic_state * SS.t * symbolic_execution_context) list =

	print_debug (Printf.sprintf "UNFOLD_PREDICATE %s with info %s in the symbolic state:\n%s"
			(JSIL_Print.string_of_logic_assertion (LPred (pred_name, args)))
			(JSIL_Print.string_of_unfold_info unfold_info)
			(Symbolic_State_Print.string_of_symb_state symb_state));

	(* Step 1: Find the predicate assertion to be unfolded
	    --------------------------------------------------------------
		* compute the new existentials - new logical variables used 
		  in the unfold logical command 
		* find the predicate assertion that matches the unfold logical 
		  command  
		* subst_e maps the new existentials to logical expressions 
		  expressed in terms of pre-existing logical vars
	*)
	let symb_state_vars : SS.t = ss_lvars symb_state  in
	let args_vars : SS.t       = JSIL_Logic_Utils.get_lexpr_list_lvars args in
	let existentials : SS.t    = SS.diff args_vars symb_state_vars in

	let new_spec_vars     = SS.union spec_vars existentials in
	let existentials_lst  = SS.elements existentials in
	let subst_e           = Symbolic_State_Utils.subtract_pred pred_name args (ss_preds symb_state) (ss_pfs symb_state) (ss_gamma symb_state) spec_vars existentials_lst true in
	let subst_e           =
		try Option.get subst_e 
			with _ -> 
				print_debug ("Failed to subtract pred\n");  
				(raise (Failure (Printf.sprintf "Predicate %s not found in the predicate set!!!" pred_name))) in

	(* print_debug (Printf.sprintf "New spec vars (unfold): %s" (String.concat ", " (SS.elements existentials)));
	print_debug(Printf.sprintf "After subtract pred with substitution:\n%s\n" (Symbolic_State_Print.string_of_substitution subst0)); *) 

	(* Step 2: Call the unfolding algorithm
	    --------------------------------------------------------------
		* If the unfold is annotated with a substitution, we have to pass
		  it to the unfolding algorithm 
		* Compute the caller store - mapping the formal arguments of the 
		  predicate to unfold to the logical expressions with which they 
		  are unfolded 
	*)
	let pred_defs, pat_subst = use_unfold_info unfold_info pred_defs subst_e in
	let args                 = List.map (lexpr_substitution subst_e true) args in
	let caller_store         = store_init params args in
  	let unfolded_pred_defs   = List.map (fun (i, pred_symb_state) ->
		i, Spatial_Entailment.unfold_predicate_definition caller_store subst_e pat_subst existentials spec_vars pred_symb_state symb_state) pred_defs in
  	let unfolded_pred_defs   = List.map (fun (i, x) -> i, Option.get x) (List.filter (fun (i, x) -> x <> None) unfolded_pred_defs) in

  	(* Step 3: Update unfolding info in search_info for each 
  	   symb_state resulting from the unfolding of the predicate assertion 
	   ------------------------------------------------------------------
	*)
	List.map (fun (i, unfolded_symb_state) -> 
		let new_search_info = sec_duplicate search_info in 
		sec_unfold_pred_def new_search_info pred_name i; 
		unfolded_symb_state, new_spec_vars, new_search_info) unfolded_pred_defs 


(*---------------------------------------------------------------
	recursive_unfold_predicate. 
	 * Unfolds a predicate assertion recursively but linearly!
	 * The unfolding stops when one of the following two conditions 
	   is met: 
	   - base case of the predicate 
	   - the unfolding would result in more than one symbolic 
	     state
----------------------------------------------------------------*)
let recursive_unfold_predicate
		(pred_name  : string)
		(pred_defs  : ((string option) * symbolic_state * (jsil_logic_assertion list)) list)
		(symb_state : symbolic_state)
		(params     : jsil_var list)
		(spec_vars  : SS.t)
		(search_info : symbolic_execution_context) : (symbolic_state * SS.t * symbolic_execution_context) list =

	print_debug (Printf.sprintf "Recursive Unfold: %s" pred_name);
	print_debug (Printf.sprintf "Spec vars (recunfold): %s" (String.concat ", " (SS.elements spec_vars)));

	let rec loop cur_spec_vars symb_state search_info : symbolic_state * SS.t * symbolic_execution_context =

		let pred_args = find_predicate_assertion_by_name (ss_preds symb_state) pred_name in
		match pred_args with
			| [] -> symb_state, cur_spec_vars, search_info
			| args :: more_args -> (
				let old_symb_state = ss_copy symb_state in
				let unfolded_symb_states_with_spec_vars = unfold_predicate pred_name pred_defs symb_state params args cur_spec_vars search_info None in
				(match unfolded_symb_states_with_spec_vars with 
				| [ (new_symb_state, new_spec_vars, new_search_info) ] ->
					let new_symb_state = Simplifications.simplify_ss new_symb_state (Some (Some new_spec_vars)) in
					loop new_spec_vars new_symb_state new_search_info
				| _ -> 
					print_debug (Printf.sprintf "End of recursive_unfold.\n");
					old_symb_state, spec_vars, search_info)) in 

	[ (loop spec_vars symb_state search_info) ]



let make_spec_var_subst (subst : substitution) (spec_vars : SS.t) : substitution * SS.t = 	
	print_debug (Printf.sprintf "make_spec_var_subst with spec_vars %s and subst:\n%s" 
		(String.concat ", " (SS.elements spec_vars))
		(JSIL_Print.string_of_substitution subst)); 

	let spec_les    = substitution_range subst in 
	let spec_alocs  = List.concat (List.map (fun le -> SS.elements (get_lexpr_alocs le)) spec_les) in 
	let subst_list  = List.map (fun aloc -> (aloc, ALoc aloc)) spec_alocs in 
	let subst_list' = List.map (fun x -> (x, LVar x)) (SS.elements spec_vars) in 
	let pat_subst   = init_substitution3 (subst_list @ subst_list') in 

	print_debug (Printf.sprintf "make_spec_var_subst. pat_subst:\n%s" 
		(JSIL_Print.string_of_substitution pat_subst));

	pat_subst, (SS.of_list spec_alocs) 


let extend_spec_vars_subst 
		(spec_vars : SS.t) 
		(pfs       : pure_formulae) 
		(subst     : substitution) : unit = 

	List.iter (fun x -> 
		if (not (Hashtbl.mem subst x)) then (
			match Normaliser.resolve_location x (pfs_to_list pfs) with 
				| Some loc  when is_lit_loc_name loc  -> Hashtbl.replace subst x (LLit (Loc loc)) 
				| Some aloc when is_abs_loc_name aloc -> Hashtbl.replace subst x (ALoc aloc) 
				| _       -> ()
		)) (SS.elements spec_vars) 

(*---------------------------------------------------------------
Checking if recursive calls terminate
----------------------------------------------------------------*)
let lemma_recursive_call_termination_check
	(lemma : jsil_lemma)
	(symb_state : symbolic_state)
	(args : jsil_logic_expr list) : unit =

	(* Check if a variant has been defined *)
	match lemma.lemma_variant with
	| None -> Printf.printf "WARNING: No variant defined for lemma %s\n" lemma.lemma_name
	| Some variant_expr ->

		(* Convert variant to logical expression, so we can perform operations on it *)
		let variant = expr_2_lexpr variant_expr in

		(* Mapping lemma args -> new logical expressions (in the called state) *)
		let variant_subst = init_substitution2 lemma.lemma_spec.spec_params args in

		(* The new variant, in the called state *)
		let called_variant = lexpr_substitution variant_subst false variant in

		(* Now evaluate each variable in both variants *)
		let _, store, pfs, gamma, _ = symb_state in
		let evaluate_vars
	        (lexpr : jsil_logic_expr) : (jsil_logic_expr * bool) =

	        match lexpr with
	        	| PVar v -> (symb_evaluate_expr store gamma pfs (Var v), false)
	            | e -> (e, true)
	    in
	    let evaluate_variant_pvars = logic_expression_map evaluate_vars None in

	    (* Create an assertion called_variant <# variant *)
	    let termination_assertion = LLess (evaluate_variant_pvars called_variant, evaluate_variant_pvars variant) in
			print_debug (Printf.sprintf "Termination assertion: %s" (JSIL_Print.string_of_logic_assertion termination_assertion));

	    (* Check that the current symb state entails the termination_assertion *)
	    let state_entails_termination_assertion = Pure_Entailment.check_entailment SS.empty (Symbolic_State.pfs_to_list pfs) [termination_assertion] gamma in

	    (* Throw an error if the assertion is not entailed *)
	    match state_entails_termination_assertion with
	    	| true -> ()
	    	| false -> raise (Failure (Printf.sprintf "Lemma %s: Variant %s does not decrease in every recursive call." lemma.lemma_name (JSIL_Print.string_of_logic_expression variant)))


(*---------------------------------------------------------------
	symb_evaluate_logic_cmd. 
----------------------------------------------------------------*)
let rec symb_evaluate_logic_cmd 
		(s_prog            : symb_jsil_program)
		(l_cmd             : jsil_logic_command)
		(symb_state        : symbolic_state)
		(subst             : substitution)
		(spec_vars         : SS.t)
		(search_info       : symbolic_execution_context)
		(print_symb_states : bool) 
		(lemma             : jsil_lemma option) : (symbolic_state * SS.t * symbolic_execution_context) list =

  	let prev_symb_state = ss_copy symb_state in

	let get_pred_data pred_name les =
		print_debug (Printf.sprintf "About to fold %s(%s)" pred_name 
			(String.concat ", " (List.map JSIL_Print.string_of_logic_expression les)));

		let pred = get_pred s_prog.pred_defs pred_name in
		let args =
			List.map
				(fun le -> Normaliser.normalise_lexpr ~store:(ss_store symb_state) ~subst:subst (ss_gamma symb_state) le)
				les in
		let params = pred.n_pred_params in
    	let pred_defs = pred.n_pred_definitions in
		(params, pred_defs, args) in

	(match l_cmd with
	
	| Fold a ->
		(match a with
		| LPred	(pred_name, les) ->
			print_time (Printf.sprintf "Fold %s(%s)." pred_name
				(String.concat ", " (List.map JSIL_Print.string_of_logic_expression les))); 
			print_debug (Printf.sprintf "\nSTATE #1: %s" (Symbolic_State_Print.string_of_symb_state symb_state));
      		let params, pred_defs, args = get_pred_data pred_name les in
      		print_debug (Printf.sprintf "\nSTATE #2: %s" (Symbolic_State_Print.string_of_symb_state symb_state));
			let pred_defs = Array.of_list pred_defs in

      		let folded_predicate = fold_predicate pred_name pred_defs symb_state params args spec_vars None search_info in
			(match folded_predicate with
			| Some (symb_state, new_spec_vars, new_search_info) ->
				ss_extend_preds symb_state (pred_name, args);
				[ symb_state, new_spec_vars, new_search_info ]
			| _ ->
				print_normal (Printf.sprintf "\nSTATE ON ERROR: %s" (Symbolic_State_Print.string_of_symb_state symb_state));
				let msg = Printf.sprintf "Could not fold: %s " (JSIL_Print.string_of_logic_assertion a) in
				raise (Failure msg))
		| _ ->
			let msg = Printf.sprintf "Illegal fold command %s" (JSIL_Print.string_of_logic_assertion a) in
			raise (Failure msg))

	| Unfold (a, unfold_info) ->
		(match a with
   		| LPred (pred_name, les) ->
   			print_time (Printf.sprintf "Unfold %s." pred_name); 
      		let params, pred_defs, args = get_pred_data pred_name les in
			let unfolded_symb_states = unfold_predicate pred_name pred_defs symb_state params args spec_vars search_info unfold_info in
			if ((List.length unfolded_symb_states) = 0) then (
				print_normal (Printf.sprintf "\nCould not unfold: %s" pred_name);
				let msg = Printf.sprintf "Could not unfold: %s " (JSIL_Print.string_of_logic_assertion a) in
				raise (Failure msg))
			else unfolded_symb_states
		| _ ->
			let msg = Printf.sprintf "Illegal unfold command %s" (JSIL_Print.string_of_logic_assertion a) in
			raise (Failure msg))

	| RecUnfold pred_name ->
		print_time (Printf.sprintf "RecUnfold %s." pred_name); 
		let pred      = get_pred s_prog.pred_defs pred_name in
		let pred_defs = pred.n_pred_definitions in
		let params    = pred.n_pred_params in
		recursive_unfold_predicate pred_name pred_defs symb_state params spec_vars search_info

	| ApplyLem (lemma_name, l_args) ->
		print_time (Printf.sprintf "ApplyLemma %s." lemma_name);

   		(* Check recursive calls terminate, if we are inside a lemma *)
   		(match lemma with
			| Some l -> (if (lemma_name = l.lemma_name) then lemma_recursive_call_termination_check l symb_state l_args);
    		| None -> ());

		(* Look up the lemma specs in the spec table *)
		let proc_specs = try Hashtbl.find s_prog.spec_tbl lemma_name
			with _ -> raise (Failure (Printf.sprintf "No spec found for lemma %s" lemma_name)) in

    	(* symbolically evaluate the args *)
   		let le_args = List.map (fun le -> Normaliser.normalise_lexpr ~store:(ss_store symb_state) ~subst:subst (ss_gamma symb_state) le) l_args in
		let _, new_symb_states = find_and_apply_spec s_prog.program lemma_name proc_specs symb_state le_args in

    (* Checking precondition is met *)
		(if ((List.length new_symb_states) = 0)
			then raise (Failure (Printf.sprintf "No precondition found for lemma %s." lemma_name)));

    (* Creating the new symbolic states *)
		List.map (fun (symb_state, _, _) ->
		let new_symb_state : symbolic_state = Simplifications.simplify_ss symb_state (Some (Some spec_vars)) in
		let new_search_info = sec_duplicate search_info in
		(new_symb_state, spec_vars, new_search_info)) new_symb_states

	| LogicIf (le, then_lcmds, else_lcmds) ->
    	print_time "LIf.";
    	
    	let le' = Normaliser.normalise_lexpr ~store:(ss_store symb_state) (ss_gamma symb_state) le in

		let e_le', a_le' = lift_logic_expr le' in
		let a_le_then =
			match e_le', a_le' with
			| _, Some (a_le, _) -> a_le
			| Some e_le, None -> LEq (e_le, LLit (Bool true))
			| None, None -> LFalse in
			if (Pure_Entailment.check_entailment SS.empty (ss_pfs_list symb_state) [ a_le_then ] (ss_gamma symb_state))
				then (
					print_normal (Printf.sprintf "LIf Guard -- %s ==> true" (JSIL_Print.string_of_logic_expression le));
					symb_evaluate_logic_cmds s_prog then_lcmds [ symb_state, spec_vars, search_info ] print_symb_states subst lemma 
				) else (
					print_normal (Printf.sprintf "If Guard -- %s ==> false" (JSIL_Print.string_of_logic_expression le));
					symb_evaluate_logic_cmds s_prog else_lcmds [ symb_state, spec_vars, search_info ] print_symb_states subst lemma)

	| Macro (name, param_vals) ->
		let macro_body = expand_macro name param_vals in
		symb_evaluate_logic_cmd s_prog macro_body symb_state subst spec_vars search_info print_symb_states lemma

 	| Assert a ->
 		extend_spec_vars_subst spec_vars (ss_pfs symb_state) subst;
   		print_normal (Printf.sprintf "Assert %s." (JSIL_Print.string_of_logic_assertion a));
		let existentials            = get_asrt_lvars a in
		let existentials            = SS.diff existentials spec_vars in
		let new_spec_vars_for_later = SS.union existentials spec_vars in
		let gamma_spec_vars         = filter_gamma_f (ss_gamma symb_state) (fun x -> SS.mem x spec_vars) in
		let new_symb_state          = Option.get (Normaliser.normalise_post gamma_spec_vars subst spec_vars (get_asrt_pvars a) a) in
		let pat_subst, spec_alocs   = make_spec_var_subst subst spec_vars in
		(match (Spatial_Entailment.grab_resources new_spec_vars_for_later (Normaliser.create_unification_plan new_symb_state spec_alocs) pat_subst new_symb_state symb_state) with
			| Some new_symb_state -> [ new_symb_state, new_spec_vars_for_later, search_info ]
			| None -> raise (Failure "Assert: could not grab resources.")))					
and
symb_evaluate_logic_cmds s_prog
	(l_cmds : jsil_logic_command list)
	(symb_states_with_spec_vars : (symbolic_state * SS.t * symbolic_execution_context) list)
	(print_symb_states : bool)
	(subst : substitution) 
	(lemma : jsil_lemma option) : ((symbolic_state * SS.t * symbolic_execution_context) list) =
	
	(match l_cmds with
	| [] -> symb_states_with_spec_vars
	| l_cmd :: rest_l_cmds ->
		let new_symb_states_with_spec_vars = 
			List.concat (List.map (fun (symb_state, spec_vars, search_info) ->
				if print_symb_states then (
					print_normal (Printf.sprintf "----------------------------------\nSTATE:\n%s\nLOGIC COMMAND: %s\n----------------------------------\n" 
						(Symbolic_State_Print.string_of_symb_state symb_state) 
						(JSIL_Print.string_of_lcmd l_cmd)));
					let info_node       = Symbolic_Traces.sg_node_from_lcmd symb_state l_cmd in
					let new_search_info = sec_create_new_info_node search_info info_node in  
					symb_evaluate_logic_cmd s_prog l_cmd symb_state subst spec_vars new_search_info print_symb_states lemma) symb_states_with_spec_vars) in 
		symb_evaluate_logic_cmds s_prog rest_l_cmds new_symb_states_with_spec_vars print_symb_states subst lemma)


(**
	Symbolically evaluate a control flow command 

	@param s_prog      Extended JSIL program
	@param proc        The procedure that is being executed
	@param search_info Something for the dot graphs
	@param symb_state  Current symbolic state
	@param cur         Index of the current command
	@param next        Index of the next command

	@return symb_states The list of symbolic states resulting from the evaluation
*)
let rec symb_evaluate_cmd 
		(s_prog            : symb_jsil_program)
		(proc              : jsil_procedure) 
		(spec_vars         : SS.t)
		(subst             : substitution)
		(search_info       : symbolic_execution_context)
		(symb_state        : symbolic_state) 
		(i                 : int)
		(prev              : int) : (symbolic_state * jsil_return_flag * SS.t * symbolic_execution_context) list =

	(* symbolically evaluate a guarded goto *)
	let symb_evaluate_guarded_goto symb_state e j k =
		let le = symb_evaluate_expr (ss_store symb_state) (ss_gamma symb_state) (ss_pfs symb_state) e in
		print_debug (Printf.sprintf "Guarded Goto: Evaluated expression: %s --> %s\n" (JSIL_Print.string_of_expression e) (JSIL_Print.string_of_logic_expression le));
		let e_le, a_le = lift_logic_expr le in
		let a_le_then, a_le_else =
			match e_le, a_le with
			| _, Some (a_le, a_not_le) ->
				print_debug_petar (Printf.sprintf "Lifted assertion: %s\n" (JSIL_Print.string_of_logic_assertion a_le));
				([ a_le ], [ a_not_le ])
			| Some e_le, None ->
				([LEq (e_le, LLit (Bool true))], [LEq (e_le, LLit (Bool false))])
			| None, None -> ([ LFalse ], [ LFalse ]) in

		print_debug (Printf.sprintf "Checking if:\n%s\n\tentails\n%s\n" (JSIL_Print.str_of_assertion_list (ss_pfs_list symb_state)) (JSIL_Print.str_of_assertion_list a_le_then));
		if (Pure_Entailment.check_entailment SS.empty (ss_pfs_list symb_state) a_le_then (ss_gamma symb_state)) then
			(** current symb_state entails that e == true
				we only explore the then branch *)
			(print_normal "ONLY THEN branch is explored";
			post_symb_evaluate_cmd s_prog proc spec_vars subst search_info symb_state i j)
			else (if (Pure_Entailment.check_entailment SS.empty (ss_pfs_list symb_state) a_le_else (ss_gamma symb_state)) then
				(** current symb_state entails that e == false
				    we only explore the false branch *)
				(print_normal "ONLY ELSE branch is explored";
				post_symb_evaluate_cmd s_prog proc spec_vars subst search_info symb_state i k)
			else (
				(** we cannot prove that the current symb_state entails that e == true or e == false
				    both branches need to be explored *)
				print_normal "Could NOT determine the branch.";
				let then_symb_state  = symb_state in
				let then_search_info = search_info in
				let else_symb_state  = ss_copy symb_state in
				let else_search_info = sec_duplicate search_info in

				ss_extend_pfs then_symb_state (DynArray.of_list a_le_then);
				ss_extend_pfs else_symb_state (DynArray.of_list a_le_else);
				let ret_then = post_symb_evaluate_cmd s_prog proc spec_vars subst then_search_info then_symb_state i j in 
				let ret_else = post_symb_evaluate_cmd s_prog proc spec_vars subst else_search_info else_symb_state i k in 
				ret_then @ ret_else 
			)) in

	(* symbolically evaluate a procedure call *)
	let symb_evaluate_call symb_state x e e_args j =

		(** Step 1 - Evaluate the logical expression denoting the procedure name 
          * If we cannot determine the concrete name of the proceduring being called 
            the symbolic execution halts with an error *)
		let le_proc_name = symb_evaluate_expr (ss_store symb_state) (ss_gamma symb_state) (ss_pfs symb_state) e in
		let proc_name =
			(match le_proc_name with
			| LLit (String proc_name) -> proc_name
			| _ ->
				let msg = Printf.sprintf "Symb Execution Error - Cannot analyse a procedure call without the name of the procedure. Got: %s." (JSIL_Print.string_of_logic_expression le_proc_name) in
				raise (Failure msg)) in

		(** Step 2 - Symbolically evaluate the arguments given to the procedure call  *)
		let le_args = List.map (fun e -> symb_evaluate_expr (ss_store symb_state) (ss_gamma symb_state) (ss_pfs symb_state) e) e_args in
		
		(** Step 3 - Symbolically execute the procedure  *)
		let new_symb_states =
			if (Hashtbl.mem s_prog.spec_tbl proc_name) then (
				(** If the procedure has an associated specification, then we use it  *)
				let proc_specs = Hashtbl.find s_prog.spec_tbl proc_name in 
				List.iter 
					(fun spec -> if (spec.n_post = []) 
						then print_debug (Printf.sprintf "WARNING: Exists spec with no post for proc %s." proc_name))
					proc_specs.n_proc_specs;
				let _, new_symb_states = find_and_apply_spec s_prog.program proc_name proc_specs symb_state le_args in
				let new_symb_states    = List.map (fun (symb_state, ret_flag, ret_le) -> (symb_state, ret_flag, ret_le, search_info)) new_symb_states in 
				(if ((List.length new_symb_states) = 0)
					then raise (Failure (Printf.sprintf "No precondition found for procedure %s." proc_name)));
				new_symb_states
			) else (
				(** Otherwise, symbolically execute the code of the procedure itself  *)
				print_normal (Printf.sprintf "No spec found for proc %s - Going to run it" proc_name); 
				
				let proc              = get_proc s_prog.program proc_name in
				let proc_args         = get_proc_args proc in
				let new_store         = store_init proc_args le_args in
				let old_store         = ss_store symb_state in 
				let symb_state_caller = ss_replace_store symb_state new_store in
				let old_vis_tbl       = search_info.vis_tbl in 
				let new_search_info   = sec_reset_vis_tbl search_info in 
				let final_symb_states = pre_symb_evaluate_cmd s_prog proc spec_vars (init_substitution2 [] []) new_search_info symb_state_caller (-1) 0 in 
				List.map (fun (symb_state, ret_flag, _, search_info) -> 
					let ret_var   = proc_get_ret_var proc ret_flag in
					let ret_lexpr = store_get_safe (ss_store symb_state) ret_var in
					match ret_lexpr with 
					| Some ret_le -> 
						let search_info = { search_info with vis_tbl = old_vis_tbl } in 
						let symb_state  = ss_replace_store symb_state old_store in
						(symb_state, ret_flag, ret_le, search_info)
					| None        -> raise (Failure (Printf.sprintf "No return variable found in store for procedure %s." proc_name))
				) final_symb_states
			) in
		
		(** Step 4 - Update the return variable (x) with the returned value and 
	        continue with the symbolic execution *)
		List.concat (List.map 
			(fun (symb_state, ret_flag, ret_le, search_info) ->
				let ret_type, _, _  = type_lexpr (ss_gamma symb_state) ret_le in
				store_put (ss_store symb_state) x ret_le;
				update_gamma (ss_gamma symb_state) x ret_type;
				let symb_state      = Simplifications.simplify_ss symb_state (Some (Some spec_vars)) in
				let new_search_info = sec_duplicate search_info in
				(match ret_flag, j with
				| Normal, _ ->
					post_symb_evaluate_cmd s_prog proc spec_vars subst new_search_info symb_state i (i+1)
				| Error, None -> raise (Failure (Printf.sprintf "Procedure %s may return an error, but no error label was provided." proc_name))
				| Error, Some j ->
					post_symb_evaluate_cmd s_prog proc spec_vars subst new_search_info symb_state i j))
			new_symb_states) in

	(* symbolically evaluate a phi command *)
	let symb_evaluate_phi_psi symb_state x x_arr =
		let cur_proc_name = proc.proc_name in
		let cur_which_pred =
			try Hashtbl.find s_prog.which_pred (cur_proc_name, prev, i)
			with _ ->  raise (Failure (Printf.sprintf "which_pred undefined for command: %s %d %d" cur_proc_name prev i)) in
		let expr     = x_arr.(cur_which_pred) in
		let le       = symb_evaluate_expr (ss_store symb_state) (ss_gamma symb_state) (ss_pfs symb_state) expr in
		let te, _, _ = type_lexpr (ss_gamma symb_state) le in
		store_put (ss_store symb_state) x le;
		update_gamma (ss_gamma symb_state) x te;
		post_symb_evaluate_cmd s_prog proc spec_vars subst search_info symb_state i (i+1) in
	
	let spec_vars = SS.filter (fun x -> is_spec_var_name x) spec_vars in
	let symb_state = Simplifications.simplify_ss symb_state (Some (Some spec_vars)) in
	Symbolic_State_Print.print_symb_state_and_cmd proc i symb_state;
	let metadata, cmd = get_proc_cmd proc i in
	sec_visit_node search_info i;
	
	match cmd with
	| Basic bcmd ->
		let _ = symb_evaluate_bcmd bcmd symb_state in
		post_symb_evaluate_cmd s_prog proc spec_vars subst search_info symb_state i (i+1)

	| Goto j -> post_symb_evaluate_cmd s_prog proc spec_vars subst search_info symb_state i j

	| GuardedGoto (e, j, k) -> symb_evaluate_guarded_goto symb_state e j k

	| Call (x, e, e_args, j) -> symb_evaluate_call symb_state x e e_args j

	| PhiAssignment (x, x_arr)
	| PsiAssignment (x, x_arr) -> symb_evaluate_phi_psi symb_state x x_arr

	| _ -> raise (Failure "not implemented yet")

and post_symb_evaluate_cmd s_prog proc spec_vars subst search_info symb_state cur next =
	(* Get the current command and the associated metadata *)
	let metadata, cmd = get_proc_cmd proc cur in
	(* Evaluate logic commands, if any *)
	let symb_states_with_spec_vars = symb_evaluate_logic_cmds s_prog metadata.post_logic_cmds [ symb_state, spec_vars, search_info ] false subst None in
	(* The number of symbolic states resulting from the evaluation of the logic commands *)
	let len = List.length symb_states_with_spec_vars in
	(* For each obtained symbolic state *)
	List.concat (List.map 
		(* Get the symbolic state *)
		(fun (symb_state, spec_vars', search_info) ->
			pre_symb_evaluate_cmd s_prog proc spec_vars' subst search_info symb_state cur next)
		symb_states_with_spec_vars)

and pre_symb_evaluate_cmd 
		s_prog proc spec_vars subst 
		search_info symb_state cur next : (symbolic_state * jsil_return_flag * SS.t * symbolic_execution_context) list=

	(* Q1: Have we reached the return label? *)
	if (Some cur = proc.ret_label) then
		(* YES. Return - normal mode *)
		[ (symb_state, Normal, spec_vars, search_info) ] 
	(* NO. Q2: Have we reached the error label? *)
	else if (Some cur = proc.error_label) then
		(* YES. Return - error mode  *)
		[ (symb_state, Error, spec_vars, search_info) ]
	(* NO: The control did not reach the end of the symbolic execution *)
	else (
		(* Get the next command and its metadata *)
		let metadata, cmd = get_proc_cmd proc next in
		if (sec_is_visited_node search_info next) then ( 
			(*  Already symbolically executed the next command *)
			(match metadata.invariant with
			| None   -> raise (Failure "Back edges MUST point to commands with invariants")
			| Some a ->
				let symb_state_inv        = Normaliser.normalise_invariant a (ss_gamma symb_state) spec_vars (copy_substitution subst) (get_asrt_pvars a) in 
				let _, spec_alocs = make_spec_var_subst subst spec_vars in 

				print_normal (Printf.sprintf "Current state: %s\n" (Symbolic_State_Print.string_of_symb_state symb_state));
				print_normal (Printf.sprintf "Normalised invariant: %s\n" (Symbolic_State_Print.string_of_symb_state symb_state_inv));
				print_normal (Printf.sprintf "spec_alocs: %s\n" (String.concat ", " (SS.elements spec_alocs)));

				try 
					let outcome, (_, _, new_subst, _, _) = Spatial_Entailment.unify_symb_states (Normaliser.create_unification_plan symb_state_inv spec_alocs) None symb_state_inv symb_state in
					print_normal (Printf.sprintf "new_subst: %s\n" (JSIL_Print.string_of_substitution new_subst)); 
					
					if (outcome) then [] else raise (Failure "Unification with invariant failed")
				with _ -> raise (Failure "Unification with invariant failed"))				
		) else (
			(*  New next command *)
			
			(* 1. If there is an invariant:
			     - check if the current symb_state entails the invariant
			     - add the invariant variables to the spec_vars *)
			let symb_state, spec_vars = (match metadata.invariant with 
				| None    -> symb_state, spec_vars
				| Some a  -> 
					print_normal 
						(Printf.sprintf "INVARIANT: %s.\nSubst:\n%s\n.SpecVars:%s\n"
							(JSIL_Print.string_of_logic_assertion a)
							(JSIL_Print.string_of_substitution subst)
							(String.concat ", " (SS.elements spec_vars)));
					extend_spec_vars_subst spec_vars (ss_pfs symb_state) subst; 
					
					let inv_lvars             = get_asrt_lvars a in
					let symb_state_inv        = Normaliser.normalise_invariant a (ss_gamma symb_state) spec_vars (copy_substitution subst) (get_asrt_pvars a) in 
					let spec_vars_inv         = SS.union inv_lvars spec_vars in 
					let pat_subst, spec_alocs = make_spec_var_subst subst spec_vars in 

					print_normal (Printf.sprintf "Current state: %s\n" (Symbolic_State_Print.string_of_symb_state symb_state));
					print_normal (Printf.sprintf "Normalised invariant: %s\n" (Symbolic_State_Print.string_of_symb_state symb_state_inv));
					print_normal (Printf.sprintf "substitution: %s\n" (JSIL_Print.string_of_substitution pat_subst)); 
					print_normal (Printf.sprintf "spec_alocs: %s\n" (String.concat ", " (SS.elements spec_alocs))); 

					try 
						let outcome, _ = Spatial_Entailment.unify_symb_states (Normaliser.create_unification_plan symb_state_inv spec_alocs) (Some pat_subst) symb_state_inv symb_state in
						if (outcome) then symb_state_inv, spec_vars_inv else raise (Failure "Unification with invariant failed")
					with _ -> raise (Failure "Unification with invariant failed")) in 
			 
			(* 2. Execute the pre logical commands *)
			let symb_states_with_spec_vars = 
				symb_evaluate_logic_cmds s_prog metadata.pre_logic_cmds [ symb_state, spec_vars, search_info ] false subst None in

			(* 3. Evaluate the next command in all the possible symb_states *)
			List.concat (List.map (fun (symb_state, spec_vars', search_info) ->
				(* Construct the search info for the next command *)
				let info_node       = Symbolic_Traces.sg_node_from_cmd symb_state next cmd in
				let new_search_info = sec_create_new_info_node search_info info_node in 
				symb_evaluate_cmd s_prog proc spec_vars' subst new_search_info symb_state next cur)
				symb_states_with_spec_vars)))
	

let unify_symb_state_against_post 
		(intuitionistic : bool)
		(symb_exe_info  : symbolic_execution_context)
		(proc_name      : string) 
		(spec           : jsil_n_single_spec)
		(flag           : jsil_return_flag) 
		(symb_state     : symbolic_state) : symbolic_state =

	let print_error_to_console msg =
		(if (msg = "")
			then Printf.printf "Failed to verify a spec of proc %s\n" proc_name
			else Printf.printf "Failed to verify a spec of proc %s -- %s\n" proc_name msg);
		let final_symb_state_str = Symbolic_State_Print.string_of_symb_state symb_state in
		let post_symb_state_str = Symbolic_State_Print.string_of_symb_state_list spec.n_post in
		Printf.printf "Final symbolic state: %s\n" final_symb_state_str;
		Printf.printf "Post condition: %s\n" post_symb_state_str in

	let rec loop posts i : symbolic_state =
		(match posts with
		| [] -> print_error_to_console ""; raise (Failure "Post condition is not unifiable")
				
		| post :: rest_posts ->
			try (
				let pat_subst, spec_alocs = make_spec_var_subst spec.n_subst spec.n_lvars in 
				let _ = Spatial_Entailment.fully_unify_symb_state intuitionistic (Normaliser.create_unification_plan post spec_alocs) (Some pat_subst) post symb_state in 
				turn_on_post i symb_exe_info; 
				print_normal (Printf.sprintf "Verified one spec of proc %s" proc_name); 
				post 
			) with Spatial_Entailment.UnificationFailure _ -> loop rest_posts (i + 1)) in 
	loop spec.n_post 0



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
let symb_evaluate_proc 
		(s_prog            : symb_jsil_program) 
		(proc_name         : string)
		(spec              : jsil_n_single_spec)
		(i                 : int)
		(pruning_info      : pruning_table) 
		(filter_symb_graph :  ((string * int, int * bool) Hashtbl.t * string array) option) =
	let sep_str = "----------------------------------\n" in
	print_normal (Printf.sprintf "%s" (sep_str ^ sep_str ^ "Symbolic execution of " ^ proc_name));

	let node_info = Symbolic_Traces.sg_node_from_pre spec.n_pre in
	let search_info = sec_init node_info pruning_info proc_name i in

	(* Get the procedure to be symbolically executed *)
	let proc = get_proc s_prog.program proc_name in
	let success, failure_msg =
		try (
			print_debug (Printf.sprintf "Initial symbolic state:\n%s" (Symbolic_State_Print.string_of_symb_state spec.n_pre));
			let symb_state = ss_copy spec.n_pre in
			(* Symbolically execute the procedure *)
			let final_symb_states = pre_symb_evaluate_cmd s_prog proc spec.n_lvars spec.n_subst search_info symb_state (-1) 0 in 
			
			List.iter (fun (symb_state, ret_flag, spec_vars, search_info) -> 
				let successful_post = unify_symb_state_against_post !js search_info proc_name spec ret_flag symb_state in 
				let node_info       = Symbolic_Traces.sg_node_from_post successful_post in
				let _               = sec_create_new_info_node search_info node_info in 
				()) final_symb_states; 
			true, None 			
		) with
			| Spatial_Entailment.UnificationFailure msg 
			| Failure msg -> 
				(print_normal (Printf.sprintf "The EVALUATION OF THIS PROC GAVE AN ERROR: %d %s!!!!" i msg);
				let node_info = Symbolic_Traces.sg_node_from_err msg in
				let _         = sec_create_new_info_node search_info node_info in 
				false, Some msg) in

	let proc_name = Printf.sprintf "Spec_%d_of_%s" i proc_name in
	(* Create the dot graph of the symbolic execution *)
	let search_dot_graph = Some (Symbolic_Traces.dot_of_symb_exec_ctxt search_info proc_name filter_symb_graph) in 
	print_debug (Printf.sprintf "%s" (sep_str ^ sep_str ^ sep_str));
	(* Return *)
	search_dot_graph, success, failure_msg


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
let sym_run_procs 
		(prog              : jsil_program)
		(procs_to_verify   : string list)
		(spec_table        : specification_table) 
		(lemma_table       : lemma_table)
		(which_pred        : which_predecessor) 
		(n_pred_defs       : (string, n_jsil_logic_predicate) Hashtbl.t)
		(filter_symb_graph : ((string * int, int * bool) Hashtbl.t * string array) option) =

	(* Construct corresponding extended JSIL program *)
	let s_prog = {
		program = prog;
		which_pred = which_pred;
		spec_tbl = spec_table;
		lemma_tbl = lemma_table;
		pred_defs = n_pred_defs
	} in
	let pruning_info = pruning_info_init () in
	
	(* Iterate over the specification table *)
	let results = List.fold_left
	  (* For each specification: *)
		(fun ac_results proc_name ->
			(* Q1: Have we got a spec? *)
			let spec = try (Some (Hashtbl.find spec_table proc_name)) with | _ -> None in
			(* Q1: YES *)
			(match spec with
			| Some spec ->
				pruning_info_extend pruning_info spec;
				(* Get list of pre-post pairs *)
				let pre_post_list = spec.n_proc_specs in
				(* Iterate over the pre-post pairs *)
				let results =
					List.mapi
					(* For each pre-post pair *)
					(fun i pre_post ->
						let new_pre_post = Symbolic_State_Utils.copy_single_spec pre_post in
						(* Symbolically execute the procedure given the pre and post *)
						let dot_graph, success, failure_msg = symb_evaluate_proc s_prog proc_name new_pre_post i pruning_info filter_symb_graph in
						(proc_name, i, pre_post, success, failure_msg, dot_graph))
					pre_post_list in
				(* Filter the posts that are not reachable *)
				let new_spec = prune_posts pruning_info spec proc_name in
				(* Update the specification table *)
				Hashtbl.replace spec_table proc_name new_spec;
				(* Concatenate symbolic trace *)
				ac_results @ results
			(* Q1: NO *)
		  | None -> ac_results))
		[]
		procs_to_verify in
	
	(* Understand complete success *)
	let complete_success = List.for_all (fun (_, _, _, partial_success, _, _) -> partial_success) results in
	
	(* Get the string and dot graphs of the symbolic execution *)
	let results_str, dot_graphs = Symbolic_State_Print.string_of_symb_exe_results results in
	
	(* Some statistics *)
	let count_verified, count_prunings = compute_verification_statistics pruning_info procs_to_verify spec_table in 
	print_normal (Printf.sprintf "\nVerified: %d.\t\tPrunings: %d.\n" count_verified count_prunings);

	(* Return *)
	results_str, dot_graphs, complete_success, results

(* Proving the proof body of each lemma *)
let prove_all_lemmas
	(lemma_table : lemma_table)
	(prog : jsil_program)
	(spec_tbl : specification_table)
	(which_pred : which_predecessor)
	(n_pred_defs : (string, n_jsil_logic_predicate) Hashtbl.t) : unit =

	(* Given a series of postconditions,
	   attempt to unify them with the given symb state *)
	(* Can't use a fold, as need to terminate as soon as a successful unification occours *)
	let rec unify_all_posts
		(all_posts : symbolic_state list)
		(symb_state : symbolic_state)
		(lvars : SS.t)
		(lemma_name : string)
		(i : int) : bool =

  		match all_posts with
			| [] ->
				print_normal (Printf.sprintf "Failed to verify a spec of lemma %s:\n" lemma_name);
				print_normal (Printf.sprintf "Non_unifiable symbolic states.\n");
				print_normal (Printf.sprintf "Final symbolic state: %s\n" (Symbolic_State_Print.string_of_symb_state symb_state));
				false
			| post :: posts ->
	      let success =
					try
						Spatial_Entailment.fully_unify_symb_state false (Normaliser.create_unification_plan post SS.empty) None post symb_state;
						(* fully_unify_symb_state throws an error when it fails, so if it succeeds success is assumed *)
						true
				  	with
						| _ -> false
				in
				(* If we failed unification on this post, try on the next *)
				match success with
					| true -> print_normal (Printf.sprintf "Verified one spec of lemma %s" lemma_name);
							  true
					| false -> print_normal ("Failed to verify one postcondition. Moving to next."); 
							unify_all_posts posts symb_state lvars lemma_name (i + 1)
	in

	(* Given a list of symb states and a list of post conditions,
	   attempts to unify each state with a post condition *)
	let unify_all_sym_states
		(all_states : ((symbolic_state * SS.t * symbolic_execution_context) list))
		(all_posts : symbolic_state list)
		(lemma_name : string) : bool =

		(* Call unify_all_posts on each symbolic state, and collect the results *)
		List.for_all (fun elem -> elem == true)
			(List.map (fun (final_symb_state, final_lvars, final_search_info) ->
				unify_all_posts all_posts final_symb_state final_lvars lemma_name 0)
			all_states)
	in

	(* Proving an individual lemma *)
	let prove_lemma
	  	(lemma : jsil_lemma)
	  	(lemma_name : string)
	  	(post_pruning_info : pruning_table) : unit =

		print_normal (Printf.sprintf "------------------------------------------");
	   	print_normal (Printf.sprintf "Proving a lemma: %s.\n" lemma_name);

	   	(* Proves an invididual pre-condition of the lemma *)
	   	let prove_indivdual_pre
	   		(spec_number : int)
	   		(spec : jsil_n_single_spec)
	   		(params : jsil_var list)
	   		(proof_body : jsil_logic_command list) : unit =

	    	(* Initialising the search info *)
			let node_info = Symbolic_Traces.sg_node_from_pre spec.n_pre in
			let symb_exe_search_info = sec_init node_info post_pruning_info lemma_name spec_number in

	  		(* Constructing a dummy program as the context for the execution of the proof body *)
			let s_prog : symb_jsil_program = {
				program    = prog;
				which_pred = which_pred; 
				spec_tbl   = spec_tbl; 
				lemma_tbl  = lemma_table; 
				pred_defs  = n_pred_defs 
		    } in

			(* Execute each command in the proof body, and get the resulting symb states *)
	        let symb_states_with_spec_vars = [((ss_copy spec.n_pre), spec.n_lvars, symb_exe_search_info)] in
			let subst = spec.n_subst in
	      	let result_states = symb_evaluate_logic_cmds s_prog proof_body symb_states_with_spec_vars true subst (Some lemma) in

	      	(* Try to unify all the resulting states with the postconditions *)
			let lemma_result = unify_all_sym_states result_states spec.n_post lemma_name in
				match lemma_result with
					| true -> print_normal (Printf.sprintf "Lemma %s VERIFIED" lemma_name); Printf.printf "Lemma %s succeeded\n" lemma_name
					| false -> print_normal (Printf.sprintf "FAILED to verify lemma %s" lemma_name); Printf.printf "Lemma %s FAILED\n" lemma_name
		in

		(* Look up the normalised lemma spec in the spec table*)
		let lemma_spec = Hashtbl.find spec_tbl lemma_name in

		(* Attempt to prove each pre-condition, if there is a proof body *)
		match lemma.lemma_proof with
			| None ->
				print_normal (Printf.sprintf "No proof body.")
			| Some proof_body ->
				List.iteri (fun spec_number spec -> prove_indivdual_pre spec_number spec lemma_spec.n_spec_params proof_body) lemma_spec.n_proc_specs
	in

	(* Prove each lemma in the lemma table *)
	Hashtbl.iter (fun lemma_name lemma -> prove_lemma lemma lemma_name (pruning_info_init ())) lemma_table
