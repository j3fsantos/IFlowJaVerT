open Pulp_Syntax

(* JSIL Basic statements *)
type s_basic_statement =
  | SSkip	
  | SAssignment of variable   * expression
	| SNew        of variable
	| SLookup     of variable   * expression * expression
  | SMutation   of expression * expression * expression
	| SDelete     of expression * expression
	| SHasField   of variable   * expression * expression
	| SProtoField of variable   * expression * expression
	| SProtoObj   of variable   * expression * expression 
 (* Rosette-specific commands *)
  | SCheck      of expression
	| SAssert     of expression
	| SDischarge

(* JSIL All Statements *)
type s_statement_syntax =
  | SBasic       of s_basic_statement 
	| SGoto        of int
	| SGuardedGoto of expression * int        * int
	| SCall        of variable   * expression * expression list * int

(* JSIL Statements + metadata *)
type s_statement = {
  s_stmt_stx  : s_statement_syntax; 
  s_stmt_data : statement_metadata;
}

let mk_sstmt stmt data = {
		s_stmt_stx  = stmt;
		s_stmt_data = data;
	}

(* Parameters of spec functions *)
let get_params sf = 
	(match sf with
   | ToBoolean            e1 
   | ToNumber             e1 
   | ToNumberPrim         e1 
   | ToString             e1 
   | ToStringPrim         e1 
   | ToObject             e1 
   | CheckObjectCoercible e1 
   | IsCallable           e1 
	 | GetValue             e1 -> [e1]
	
	 | PutValue               (e1, e2) 
   | Get                    (e1, e2) 
   | HasProperty            (e1, e2) 
   | StrictEquality         (e1, e2) 
   | StrictEqualitySameType (e1, e2) -> [e1; e2]
	 
	 | DefaultValue (e1, ot)    
   | ToPrimitive  (e1, ot) -> [e1] @ (match ot with
			                                 | Some t -> [Literal (Type t)]
			                                 | None   -> [])
																										
   | AbstractRelation (e1, e2, b) -> [e1; e2; (Literal (Bool b))])


(* Translation to remove labels *)
let remove_labels cmd_list ret_label ex_label = 
	
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
		 | SCall (var, name, exprs, i) -> SCall (var, new_name, exprs, i) in
	
	(* replace labels in gotos with respective numbers *)
	let rec remove_labels_iter cmd_list scmd_list = 
		let cmd_list = Pulp_Translate_Aux.to_ivl_goto cmd_list in
		match cmd_list with 
		| [] -> scmd_list
		| cmd :: cmd_list ->	
				(match cmd.stmt_stx with 

					| Sugar sss ->
						(match sss with
						  | SpecFunction (var, sf, l) ->
								let command = (SCall (var, (Literal (String (Pulp_Syntax_Print.string_of_spec_fun_id sf))), (get_params sf), (label_to_number l))) in
								  remove_labels_iter cmd_list (scmd_list @ [ mk_sstmt command cmd.stmt_data ])						
						  | _ -> raise (Failure "Unexpected Sugar construct")
						)	  
															
          | Label l -> 
							if ((l != ret_label) && (l != ex_label))
								then remove_labels_iter cmd_list scmd_list
								else remove_labels_iter cmd_list 
									(scmd_list @ [ mk_sstmt (SBasic SSkip) cmd.stmt_data ])
									
					| Goto l -> remove_labels_iter cmd_list 
							(scmd_list @ [ mk_sstmt (SGoto (label_to_number l)) cmd.stmt_data ])
							
					| GuardedGoto (expr, l1, l2) -> 
							remove_labels_iter cmd_list 
								(scmd_list @ [ mk_sstmt (SGuardedGoto (expr, (label_to_number l1), (label_to_number l2))) cmd.stmt_data ])						
											
				  | Basic (Skip) -> remove_labels_iter cmd_list 
														(scmd_list @ [ mk_sstmt (SBasic (SSkip)) cmd.stmt_data ])
														
				  | Basic (Mutation mutation) -> remove_labels_iter cmd_list 
														(scmd_list @ [ mk_sstmt (SBasic (SMutation (mutation.m_loc, mutation.m_field, mutation.m_right))) cmd.stmt_data ])
																											
				  | Basic (Assignment ass) -> 
						let var = ass.assign_left in
						(match ass.assign_right with 
						
							| Call        call 
							| BuiltinCall call ->
									remove_labels_iter cmd_list
										(scmd_list @ [ mk_sstmt (rewrite_call var call) cmd.stmt_data ])
											
							| Eval call -> 
									remove_labels_iter cmd_list
										(scmd_list @ [ mk_sstmt (call_with_name (rewrite_call var call) (Literal (String ("eval")))) cmd.stmt_data ])
								
							| Obj ->
									remove_labels_iter cmd_list 
										(scmd_list @ [ mk_sstmt (SBasic (SNew var)) cmd.stmt_data ])
											
							| Lookup (e1, e2) -> 
									remove_labels_iter cmd_list 
										(scmd_list @ [ mk_sstmt (SBasic (SLookup (var, e1, e2))) cmd.stmt_data ])
										
							| Deallocation (e1, e2) -> 
									remove_labels_iter cmd_list 
										(scmd_list @ [ mk_sstmt (SBasic (SDelete (e1, e2))) cmd.stmt_data; mk_sstmt (SBasic (SAssignment (var, (Literal (Bool true))))) cmd.stmt_data ])
										
							| HasField (e1, e2) -> 
									remove_labels_iter cmd_list 
										(scmd_list @ [ mk_sstmt (SBasic (SHasField (var, e1, e2))) cmd.stmt_data ])
										
							| Expression e1 -> 
									remove_labels_iter cmd_list 
										(scmd_list @ [ mk_sstmt (SBasic (SAssignment (var, e1))) cmd.stmt_data ])
										
							| ProtoF (e1, e2) -> 
									remove_labels_iter cmd_list 
										(scmd_list @ [ mk_sstmt (SBasic (SProtoField (var, e1, e2))) cmd.stmt_data ])
																				
							| ProtoO (e1, e2) -> 
									remove_labels_iter cmd_list 
										(scmd_list @ [ mk_sstmt (SBasic (SProtoObj (var, e1, e2))) cmd.stmt_data ]))
				)																																													
				in 
	 register_labels cmd_list 0;
   (remove_labels_iter cmd_list []), (label_to_number ret_label), (label_to_number ex_label)
