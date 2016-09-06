open JSIL_Syntax

(* Some (possibly empty) list of allowed logical variables, or None to allow all. *)
let allowed_lvars = ref None
(* Some (possibly empty) list of allowed program variables, or None to allow all. *)
let allowed_pvars = ref None
(* Whether or not to check if a predicate used in assertion has been defined before. *)
let allow_any_predicate = ref false
(* Collection of predicates that have been parsed so far, mapping names to number of parameters. *)
let predicate_info = Hashtbl.create 100

(** Adds a new predicate name with its number of parameters to the collection of predicates parsed.
    @return unit
    @raise Syntax_error exception if name conflicts with another predicate.
*)
let register_predicate name num_params =
	try
		if Hashtbl.find predicate_info name = num_params
		  then ()
		  else raise (Syntax_error ("Predicate name \"" ^ name ^ "\" conflicts with a previous declaration."))
	with Not_found -> Hashtbl.add predicate_info name num_params

(** The following functions activate/deactivate syntax validation.
    They are called from the JSIL_Parser when starting to parse definitions. *)
(* Entering procedure body: any program variable allowed, predicate check enforced *)
let enter_procedure () =
	allowed_pvars := None;
	allow_any_predicate := false
(* Entering predicate: those predicate parameters which are variables allowed, any predicate allowed *)
let enter_predicate params =
	let str_params = List.map (fun lexpr -> match lexpr with PVar var -> var | _ -> "") params in
	allowed_pvars := Some (List.filter (fun str -> str <> "") str_params);
	allow_any_predicate := true
(* Entering specs: procedure parameters, "ret" and "err" allowed, predicate check enforced *)
let enter_specs params =
	allowed_pvars := (Some ("ret" :: ("err" :: params)));
	allow_any_predicate := false

(** Checks whether a logical variable is syntactically coherent, i.e., allowed in the current scope.
    @param var The logical variable to be checked.
    @return unit
    @raise Syntax_error exception if invalid.
*)
let validate_lvar var =
	match !allowed_lvars with
	| None      -> ()
	| Some list ->
    (match List.mem var list with
		| true    -> ()
	  | false   -> raise (Syntax_error ("Undefined logical variable \"" ^ var ^ "\"")))

(** Checks whether a program variable is syntactically coherent, i.e., allowed in the current scope.
    @param var The program variable to be checked.
    @return unit
    @raise Syntax_error exception if invalid.
*)
let validate_pvar var =
	match !allowed_pvars with
	| None      -> ()
	| Some list ->
    (match List.mem var list with
		| true    -> ()
	  | false   -> raise (Syntax_error ("Undefined program variable \"" ^ var ^ "\"")))

(** Checks whether a predicate is being correctly used in an assertion, i.e.,
    the predicate has been defined before with the correct number of parameters.
		This check is not enforced inside predicate definitions to allow for mutual recursion.
    @param (name, params) The LPred assertion.
    @return unit
    @raise Syntax_error exception if invalid.
*)
let validate_pred_assertion (name, params) =
	try
		if !allow_any_predicate || Hashtbl.find predicate_info name = List.length params
		  then ()
		  else raise (Syntax_error ("Incorrect no. of parameters for predicate \"" ^ name ^ "\""))
	with Not_found -> raise (Syntax_error ("Undefined predicate \"" ^ name ^ "\""))

(** Checks whether a procedure spec matches its signature (name and parameters).
    @return unit
    @raise Syntax_error exception if invalid.
*)
let validate_proc_signature spec name params =
	match spec with
	| None -> ()
	| Some spec ->
		if (spec.spec_name = name)
		  then ()
		  else (raise (Syntax_error "Specification name does not match procedure name."));
		if (spec.spec_params = params)
		  then ()
			else (raise (Syntax_error "Specification parameters do not match procedure parameters."))

(** Returns a spec option resulting from the substitution of "ret" for ret_var and "err" for err_var *)
let replace_spec_keywords spec ret_var err_var =
	let ret_var =
		(match ret_var with
		| None -> ""
		| Some var -> var) in
	let err_var =
		(match err_var with
		| None -> ""
		| Some var -> var) in
	match spec with
	| None      -> None
	| Some spec ->
		Some {
			spec_name = spec.spec_name;
			spec_params = spec.spec_params;
			proc_specs = List.map
		    (fun current_spec ->
				  let subst_ret_err =
					  (fun lexpr ->
						  match lexpr with
						  | PVar "ret" -> (PVar ret_var, false)
						  | PVar "err" -> (PVar err_var, false)
						  | _ -> (lexpr, true))
					  in
				  { pre = current_spec.pre;
					  post = JSIL_Logic_Utils.assertion_map subst_ret_err current_spec.post;
					  ret_flag = current_spec.ret_flag;
				  }
			  )
			  spec.proc_specs
		}
