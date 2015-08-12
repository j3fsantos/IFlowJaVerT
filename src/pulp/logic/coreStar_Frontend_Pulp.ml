open Batteries
open Config
open Corestar
open Pulp_Syntax
open Pulp_Syntax_Print
open Pulp_Logic
open Pulp_Logic_Utils
open Pulp_Logic_Print
open Utils

exception BadArgument of string
exception StarShouldntBeThere
exception NotImplemented of string
exception ContradictionFound
exception CouldntFindFunctionId
exception CoreStarContradiction of string

let logic = ref Psyntax.empty_logic

let numeric_const = "numeric_const"
let undefined = "undefined"
let null = "null"
let cons = "cons"
let empty_list = "empty"
let empty_value = "empty_value"
let footprint = "footprint"
let reference = "ref"
let none = "none"
let field = "field"
let ret_v1 = "$ret_v1"
let ref_base = "ref_base"
let ref_field = "ref_field"
let type_of = "type_of"
let proto_pred = "proto_pred"
let bool_not = "bool_not"

module LVarMap = Map.Make (
  struct 
    type t = Vars.var
    let compare = compare
  end
)

let initialize () = Profiler.track Profiler.CoreStar (fun () ->
  Corestar.Config.smt_run := !smt_enabled; 
  Corestar.Config.solver_path := !smt_path;
  Corestar.Config.smt_debug_ref := false;
  (if (!smt_enabled) then Corestar.Smt.smt_init());
  begin match List.filter (fun (key, spec, doc) -> key = "-v") Corestar.Config.args_default with
    | (_, Arg.Set v, _) :: _ -> v := true
    | _ -> ()
  end;
  let dirs = get_logic_dirs () in
  (* TODO pulp logic *)
  let sr, rr, cn = Load_logic.load_logic_extra_rules dirs "pulp_logic" [] in
  logic := {Psyntax.empty_logic with Psyntax.seq_rules = sr; Psyntax.rw_rules = rr; Psyntax.consdecl = cn}
  )


let rec get_vars_from_args arg =
  match arg with
    | Psyntax.Arg_var (Vars.PVar (_, "$ret_v1")) -> []
    | Psyntax.Arg_var vv -> [vv]
    | Psyntax.Arg_string s -> []
    | Psyntax.Arg_op (s, argl) -> flat_map get_vars_from_args argl
    | _ -> raise (BadArgument "in get_vars_from_args")

let rec get_vars_from_pform pf =
  flat_map get_vars_from_pform_at pf 
and get_vars_from_pform_at pfa =
  let va = get_vars_from_args in
  match pfa with
      | Psyntax.P_EQ (a1, a2) 
      | Psyntax.P_NEQ (a1, a2) -> va a1 @ va a2
      | Psyntax.P_PPred (s, args)
      | Psyntax.P_SPred (s, args)  -> flat_map va args
      | Psyntax.P_Wand (pf1, pf2)
      | Psyntax.P_Or (pf1, pf2)
      | Psyntax.P_Septract (pf1, pf2) -> raise (BadArgument "in get_vars_from_pform_at")
      | Psyntax.P_False -> []

let find_var_eq v pf =
  let v = Psyntax.Arg_var v in
  let pfa = List.find (fun pfa -> 
    match pfa with
      | Psyntax.P_EQ (a1, a2) -> a1 = v || a2 = v
      | _ -> false
  ) pf in
  match pfa with
    | Psyntax.P_EQ (a1, a2) -> if a2 = v then a1 else a2
    | _ -> raise CannotHappen

let rec substitute_eq_args v a arg = 
  if arg = Psyntax.Arg_var v then a 
  else 
    match arg with
      | Psyntax.Arg_op (s, argl) -> Psyntax.Arg_op (s, List.map (substitute_eq_args v a) argl)
      | _ -> arg

let rec substitute_eq_pform v a pf =
  List.map (substitute_eq_pform_at v a) pf
and substitute_eq_pform_at v a pfa = 
  let sea = substitute_eq_args v a in
  match pfa with
      | Psyntax.P_EQ (a1, a2) -> 
        (* Leaving #r = smth *)
        begin match a1, a2 with
          | Psyntax.Arg_var Vars.PVar (_, "$ret_v1"), _
          | _, Psyntax.Arg_var Vars.PVar (_, "$ret_v1") -> pfa
          | _ -> Psyntax.P_EQ (sea a1, sea a2)
        end
      | Psyntax.P_NEQ (a1, a2) -> Psyntax.P_NEQ (sea a1, sea a2)
      | Psyntax.P_PPred (s, args) -> Psyntax.P_PPred (s, List.map sea args)
      | Psyntax.P_SPred (s, args)  -> Psyntax.P_SPred (s, List.map sea args)
      | Psyntax.P_Wand (pf1, pf2)
      | Psyntax.P_Or (pf1, pf2)
      | Psyntax.P_Septract (pf1, pf2) -> raise (BadArgument "in substitute_eq_pform_at")
      | Psyntax.P_False -> Psyntax.P_False

let elim_ident pf =
  List.filter (fun pfa ->
    match pfa with 
      | Psyntax.P_EQ (a1, a2) -> a1 <> a2
      | _ -> true
  ) pf
  
let elim_vars pf =
  Printf.printf "\nEliminating existential variables\n";
  let vars = get_vars_from_pform pf in
  List.fold_left (fun pf v -> 
    match v with
      | Vars.PVar _ -> pf
      | _ ->
    try 
      Printf.printf "\nVariable %s\n" (Vars.string_var v);
      let veq = find_var_eq v pf in
      Format.fprintf (Format.std_formatter) "Equality: %a \n" Psyntax.string_args veq; Format.pp_print_flush(Format.std_formatter)();     
      let pf = substitute_eq_pform v veq pf in
      Format.fprintf (Format.std_formatter) "Before elim_ident %a \n" Psyntax.string_form pf; Format.pp_print_flush(Format.std_formatter)();     
      let pf = elim_ident pf in
      Format.fprintf (Format.std_formatter) "After elim_ident %a \n" Psyntax.string_form pf; Format.pp_print_flush(Format.std_formatter)();     
      pf
    with Not_found -> pf
  ) pf vars

let invert_varmap varmap : variable_types LVarMap.t =
  VarMap.fold (fun k v -> LVarMap.add v k) varmap LVarMap.empty 
  
let op_of_pulp_type pt =
  match pt with
    | NullType -> "NullType"
    | UndefinedType -> "UndefinedType"
    | BooleanType -> "BooleanType"
    | StringType -> "StringType"
    | NumberType -> "NumberType"
    | ObjectType (Some Builtin) -> "BObjectType"
    | ObjectType (Some Normal) -> "NObjectType"
    | ObjectType None -> "ObjectType"
    | ReferenceType r ->
      match r with
        | None -> "ReferenceType"
        | Some r -> (string_of_ref_type r)^"ReferenceType"

let literal_to_args lit =
  match lit with
    | LLoc bl -> Psyntax.Arg_op (string_of_builtin_loc_no_hash bl, [])
	  | Null -> Psyntax.Arg_op (null, [])                  
	  | Bool b -> Psyntax.Arg_op (string_of_bool b, [])  
	  | Num n -> 
      let n_string = 
      if Utils.is_int n then string_of_int (int_of_float n)
      else string_of_float n in
      Psyntax.Arg_op (numeric_const, [Psyntax.Arg_string n_string])         
	  | String s -> Psyntax.Arg_string s
	  | Undefined -> Psyntax.Arg_op (undefined, [])
	  | Type pt -> Psyntax.Arg_op (op_of_pulp_type pt, [])
	  | Empty -> Psyntax.Arg_op (empty_value, [])

let rec le_to_args (varmap : Vars.var VarMap.t) le : Psyntax.args =
  let f = le_to_args varmap in
  match le with
      | Le_Var lv -> Psyntax.Arg_var (VarMap.find (LogicalVariable lv) varmap)
      | Le_PVar x -> Psyntax.Arg_var (VarMap.find (ProgramVariable x) varmap)
      | Le_None -> Psyntax.Arg_op (none, [])
      | Le_Literal lv -> literal_to_args lv
      | Le_BinOp (le1, Arith Plus, le2) -> Psyntax.Arg_op ("builtin_plus", [f le1; f le2])
      | Le_BinOp (le1, Arith Minus, le2) -> Psyntax.Arg_op ("builtin_minus", [f le1; f le2])
      | Le_BinOp (le1, Comparison LessThan, le2) -> Psyntax.Arg_op ("builtin_lt", [f le1; f le2])
      | Le_BinOp (le1, Concat, le2) -> Psyntax.Arg_op ("concat", [f le1; f le2]) (* TODO *)
      | Le_BinOp (le1, Comparison Equal, le2) -> Psyntax.Arg_op ("triple_eq", [f le1; f le2]) (* TODO *)
      | Le_Base le -> Psyntax.Arg_op (ref_base, [f le])
      | Le_Field le -> Psyntax.Arg_op (ref_field, [f le])
      | Le_TypeOf le -> Psyntax.Arg_op (type_of, [f le])
      | Le_Ref (lb, v, rt) -> Psyntax.Arg_op (reference, [f lb; f v; Psyntax.Arg_op ((string_of_ref_type rt^reference), [])])
      | Le_UnOp (Not, le1) -> Psyntax.Arg_op (bool_not, [f le1])
      | Le_BinOp _ 
      | Le_UnOp _ -> raise (NotImplemented ("le_to_args" ^ (string_of_logical_exp le)))
        
let footprint_to_args varmap l obj_fields = 
  let arg = List.fold_right (fun x arg -> 
    Psyntax.Arg_op (cons, [le_to_args varmap x; arg])
  ) obj_fields (Psyntax.Arg_op (empty_list, [])) in
  Psyntax.mkSPred (footprint, [le_to_args varmap l; arg])

let args_to_logical_var lvarmap v =
  match v with 
    | Vars.PVar (_, "$ret_v1") -> raise (BadArgument "$ret_v1")
    | v -> try LVarMap.find v lvarmap
      (* Generally we do not want logical variables that do not exist in the lvarmap *)
      (* An exception is a first parameter for the pi predicate *)
      with Not_found -> LogicalVariable (fresh_e())

let args_to_bloc args =
  match args with 
    | Psyntax.Arg_op (s, args) ->
      begin match s, args with
        | "lg", [] -> Lg
        | "lop", [] -> Lop
        | "lfp", [] -> Lfp
        | "leval", [] -> LEval
        | "ltep", [] -> Ltep
        | _ -> raise (NotImplemented ("args_to_bloc " ^ s))
      end
    | _ -> raise (BadArgument "in args_to_loc")

let args_to_ref_type args =
  match args with
    | Psyntax.Arg_op (s, args) ->
      begin match s, args with
        | "Memberref", [] -> MemberReference
        | "Variableref", [] -> VariableReference
        | _ -> raise (BadArgument "in args_to_ref_type")
      end
    | _ -> raise (BadArgument "in args_to_ref_type") 

let rec args_to_le (lvarmap : variable_types LVarMap.t) arg = 
  let f = args_to_le lvarmap in
  match arg with
    | Psyntax.Arg_var v -> 
      begin match args_to_logical_var lvarmap v with
        | LogicalVariable x -> Le_Var x
        | ProgramVariable x -> Le_PVar x
      end
    | Psyntax.Arg_string s -> Le_Literal (String s)
    | Psyntax.Arg_op (s, args) -> 
      begin match s, args with
        | "numeric_const", [Psyntax.Arg_string n] -> Le_Literal (Num (float_of_string n))
        | "undefined", [] -> Le_Literal Undefined
        | "null", [] -> Le_Literal Null
        | "true", [] -> Le_Literal (Bool true)
        | "false", [] -> Le_Literal (Bool false)
        | "lg", [] 
        | "lop", [] 
        | "lfp", []
        | "ltep", []
        | "leval", [] -> Le_Literal (LLoc (args_to_bloc arg))
        | "empty_value", [] -> Le_Literal Empty
        | "NullType", [] ->  Le_Literal (Type NullType)
        | "UndefinedType", [] -> Le_Literal (Type UndefinedType)
        | "BooleanType", [] -> Le_Literal (Type BooleanType)
        | "StringType", [] ->  Le_Literal (Type StringType)
        | "NumberType", [] ->  Le_Literal (Type NumberType)
        | "BObjectType", [] ->  Le_Literal (Type (ObjectType (Some Builtin)))
        | "NObjectType", [] ->  Le_Literal (Type (ObjectType (Some Normal)))
        | "ObjectType", [] ->  Le_Literal (Type (ObjectType None))
        | "ReferenceType", [] ->  Le_Literal (Type (ReferenceType None))
        | "MemberReference", [] ->  Le_Literal (Type (ReferenceType (Some MemberReference)))
        | "VariableReference", [] ->  Le_Literal (Type (ReferenceType (Some VariableReference)))
        | "builtin_plus", [arg1; arg2] -> Le_BinOp (f arg1, Arith Plus, f arg2)
        | "builtin_minus", [arg1; arg2] -> Le_BinOp (f arg1, Arith Minus, f arg2)
        | "builtin_lt", [arg1; arg2] -> Le_BinOp (f arg1, Comparison LessThan, f arg2)
        | "concat", [arg1; arg2] -> Le_BinOp (f arg1, Concat, f arg2) 
        | "triple_eq", [arg1; arg2] -> Le_BinOp (f arg1, Comparison Equal, f arg2)
        | "ref", [lb; v; rt] -> Le_Ref (f lb, f v, args_to_ref_type rt)
        | "none", [] -> Le_None
        | "ref_base", [le] -> Le_Base (f le)
        | "ref_field", [le] -> Le_Field (f le)
        | "type_of", [le] -> Le_TypeOf (f le)
        | "bool_not", [le] -> Le_UnOp (Not, f le)
        | str, args -> raise (BadArgument (str ^ " in args_to_le"))
      end
    | arg -> raise (BadArgument "in args_to_le")

let rec args_to_footprint varmap arg =
  match arg with
    | Psyntax.Arg_op ("cons", [x; xs]) -> (args_to_le varmap x) :: (args_to_footprint varmap xs)
    | Psyntax.Arg_op ("empty", []) -> []
    | _ -> raise (BadArgument "in args_to_footprint")
  
let rec convert_to_pform_inner (varmap : Vars.var VarMap.t) (f: formula) : Psyntax.pform =
  let lta = le_to_args varmap in
  match f with
      | Star fs -> raise StarShouldntBeThere
      | Heaplet (l, x, e) -> Psyntax.mkSPred (field, [lta l; lta x; lta e])
      | Eq (e1, e2) -> [Psyntax.P_EQ (lta e1, lta e2)]
      | NEq (e1, e2) -> [Psyntax.P_NEQ (lta e1, lta e2)]
      | REq e -> [Psyntax.P_EQ (Psyntax.Arg_var (Vars.concretep_str ret_v1), lta e)]
      | ObjFootprint (l, xs) -> footprint_to_args varmap l xs
      | Pi p -> Psyntax.mkSPred (proto_pred, [lta p.pi_list; lta p.pi_obj; lta p.pi_field; lta p.pi_loc; lta p.pi_value])

let convert_to_pform fs =
  let fs = List.map lift_equalities fs in
  let fs = List.map simplify fs in
  let logical_vars = List.unique (get_logical_vars (Star fs)) in
  Printf.printf "Logical variables %s" (String.concat "\n" (List.map (Pulp_Logic_Print.string_of_logical_var) logical_vars));
  let varmap = List.fold_left (
    fun varmap v -> 
      let cv = match v with
        (* Z3 does not like function name that starts with number *)
        | AVar v -> Vars.freshp_str ("lv_" ^ v)
        | EVar v -> Vars.freshe_str ("lv_" ^ v) in
      VarMap.add (LogicalVariable v) cv varmap
  ) VarMap.empty logical_vars in 
  Printf.printf "Variable map %s" (String.concat "\n" (List.map (fun (k, v) -> (string_of_variable_types k) ^  ":" ^ (Vars.string_var v)) (VarMap.bindings varmap)));
  let program_vars = List.unique (get_program_vars (Star fs)) in
  let varmap = List.fold_left (
    fun varmap v -> 
      VarMap.add (ProgramVariable v) (Vars.freshp_str ("pv_" ^ v)) varmap
  ) varmap program_vars in 
  List.map (fun f -> 
    match f with 
        | Star fs -> flat_map (convert_to_pform_inner varmap) fs
        | f -> convert_to_pform_inner varmap f
  ) fs, varmap
  
let convert_from_pform_at varmap pfa : formula =
  let f = args_to_le varmap in
  match pfa with
      | Psyntax.P_EQ (a1, a2) -> 
      begin match a1, a2 with
        | Psyntax.Arg_var (Vars.PVar (_, "$ret_v1")), a2 -> REq (f a2)
        | a1, Psyntax.Arg_var (Vars.PVar (_, "$ret_v1")) -> REq (f a1)
        | _ -> Eq (f a1, f a2)
      end
      | Psyntax.P_NEQ (a1, a2) -> NEq (f a1, f a2) 
      | Psyntax.P_PPred (s, al) -> raise (BadArgument (s ^ " in convert_from_pform_at"))
      | Psyntax.P_SPred (s, al) -> 
      begin match s, al with
        | "footprint", [l; arg] -> ObjFootprint (args_to_le varmap l, args_to_footprint varmap arg)
        | "field", [l; x; arg] -> Heaplet (f l, f x, f arg)
        | "proto_pred", [a1; a2; a3; a4; a5] -> Pi (mk_pi_pred (Le_Var (fresh_e())) (f a2) (f a3) (f a4) (f a5))
        | _ ->   raise (BadArgument (s ^ " in convert_from_pform_at"))                      
       end
      | Psyntax.P_Wand _
      | Psyntax.P_Or _
      | Psyntax.P_Septract _
      | Psyntax.P_False -> raise (NotImplemented ("convert_from_pform_at"))
  
let clean_return pf varmap = 
  let r = Vars.concretep_str ret_v1 in
  let v = Vars.freshe_str "N" in 
  try
    let req = find_var_eq r pf in 
    let pf = substitute_eq_pform r req pf in pf, varmap
  with Not_found -> 
    begin    
        let pf = substitute_eq_pform r (Psyntax.Arg_var v) pf in
        let req = Psyntax.P_EQ (Psyntax.Arg_var r, Psyntax.Arg_var v) in
        let varmap = LVarMap.add v (LogicalVariable (fresh_e())) varmap in
        ((req :: pf), varmap)
    end  
  
let convert_from_pform varmap (pf : Psyntax.pform) : formula =
  let pf = elim_vars pf in
  let pf,varmap = clean_return pf varmap in
  Printf.printf "Variable map %s" (String.concat "\n" (List.map (fun (k, v) -> (Vars.string_var k) ^  ":" ^ (string_of_variable_types v)) (LVarMap.bindings varmap)));
  let f = List.map (convert_from_pform_at varmap) pf in
  simplify (Star f)
  
(* Substitution only for existential variables *)
let rename_evars f =
  let all_vars = get_logical_vars f in
  let evars = List.filter (fun x -> 
    match x with
      | EVar _ -> true
      | _ -> false
  ) all_vars in
  let evars = List.unique evars in 
  let vmap = List.fold_left (fun vmap x -> LogicalVarMap.add x (Le_Var (fresh_e ())) vmap) LogicalVarMap.empty evars in
  subs_vars vmap f
 
(* does frame inference : current_state |- pre * ?F *)
(* returns : ?F * post *)
(* returns : None if contradiction found when translating to inner form *)
(*                or if frame ?F is not found *)
(* returns list of formulae because of possible multiple frames *) 
let apply_spec current_state pre post =
  let fs, varmap = convert_to_pform [current_state; pre; post] in
  let pf, pre, post = match fs with
      | [pf; pre; post] -> pf, pre, post
      | _ -> raise CannotHappen in
  match (Sepprover.convert pf) with
    | Some inner -> 
      begin 
        let inner = 
          try Sepprover.lift_inner_form inner
          with Psyntax.Contradiction -> raise (CoreStarContradiction "Lifting Inner Form") in
			  let spec = Spec.mk_spec pre post Spec.ClassMap.empty in
			  let posts = 
          try Specification.jsr (!logic) inner spec false 
          with Psyntax.Contradiction -> raise (CoreStarContradiction "in jsr") in 
			  begin match posts with
			     | None -> (* Couldn't find any frames *) None 
			     | Some posts ->   Some (List.map (fun post -> 
			        let post = Sepprover.inner_form_af_to_form post in
			        Format.fprintf (Format.std_formatter) "%a  \n" Sepprover.string_inner_form post; Format.pp_print_flush(Format.std_formatter)();
			        let pf = Sepprover.convert_back post in
			        let cf = convert_from_pform (invert_varmap varmap) pf in
			        Printf.printf "\nPrinting frames as formula: %s\n" (Pulp_Logic_Print.string_of_formula cf);
              cf
			        ) posts)
               
        end
      end 
    | None -> (* Contradiction found *) raise ContradictionFound

let get_function_id_from_expression f e =
  match e with 
    | Le_Literal (String id) -> id
    | _ -> begin let v = Le_Var (fresh_e ()) in
		  let pre_post = Eq (e, v) in
		  let posts = apply_spec f pre_post pre_post in
		  match posts with
		    | None -> raise CouldntFindFunctionId
		    | Some posts ->
		      begin match posts with
		        | [post] ->        
		          let eqs = get_equalities_of_expr e post in
		          Printf.printf "\nPrinting  eqs: %s\n" (String.concat "\n" (List.map (Pulp_Logic_Print.string_of_formula) eqs));
		          let ids = match eqs with
		            | [] -> raise CouldntFindFunctionId
		            | eqs -> 
		              begin
		                flat_map (fun eq -> 
		                  match eq with
		                    | Eq (e1, Le_Literal (String s))
		                    | Eq (Le_Literal (String s), e1) -> if e1 = e then [s] else []
		                    | _ -> []) eqs
		              end in
		           begin match List.unique ids with
		            | [s] -> s
		            | _ -> raise CouldntFindFunctionId
		           end
		        | _ -> raise CouldntFindFunctionId
		      end
       end
  
let frame_inner f1 f2 : Sepprover.inner_form list option * Vars.var VarMap.t =
  Profiler.track Profiler.CoreStar (fun () ->
      let pf1, pf2, varmap = match (convert_to_pform [f1; f2]) with
        | [pf1; pf2], varmap -> pf1, pf2, varmap
        | _ -> raise CannotHappen in
      let pfs = match Sepprover.convert pf1 with
        | Some inner1 -> Sepprover.frame !logic inner1 pf2
        | _ -> None
      in
      (pfs, varmap)
  )
  
let implies f1 f2 : bool = Profiler.track Profiler.CoreStar (fun () ->
  let f2 = rename_evars f2 in
  match fst (frame_inner f1 f2) with
    | None -> Sepprover.print_counter_example (); false
    | Some [] -> Sepprover.print_counter_example (); false
    | Some frames -> List.iter (fun f -> Format.fprintf (Format.std_formatter) "Implies frames %a" Sepprover.string_inner_form f) frames; 
      true
  )

let inconsistent f : bool = Profiler.track Profiler.CoreStar (fun () ->
  let pf = 
    match (convert_to_pform [f]) with
      | ([pf], _) -> pf
      | _ -> raise CannotHappen
  in
  let maybe_inner = Sepprover.convert pf in
        
        try
        Sepprover.inconsistent_opt !logic maybe_inner
        with Psyntax.Contradiction -> Sepprover.print_counter_example(); false
        
  )

let implies_or_list f1 f2s : bool = Profiler.track Profiler.CoreStar (fun () ->
    List.exists (implies f1) f2s
  )

(* TODO : have a function that returns only one frame and throws exception otherwise *)
let frame f1 f2 : formula list option = Profiler.track Profiler.CoreStar (fun () ->
  let f2 = rename_evars f2 in
  let pfs, varmap = frame_inner f1 f2 in
  match pfs with
    | None -> Sepprover.print_counter_example (); None
    | Some [] -> Sepprover.print_counter_example (); None
    | Some frames -> 
      Printf.printf "\nPrinting frames: %d\n" (List.length frames);
      Some (List.map (fun f -> 
        Format.fprintf (Format.std_formatter) "%a  \n" Sepprover.string_inner_form f; Format.pp_print_flush(Format.std_formatter)();
        let pf = Sepprover.convert_back f in
        Format.fprintf (Format.std_formatter) "After convert back %a \n" Psyntax.string_form pf; Format.pp_print_flush(Format.std_formatter)();
        let cf = convert_from_pform (invert_varmap varmap) pf in
        Printf.printf "\nPrinting frames as formula: %s\n" (Pulp_Logic_Print.string_of_formula cf);
        cf
      ) frames)
  )
  
let frame_or_list f1 f2s : formula list option = Profiler.track Profiler.CoreStar (fun () ->
  try Some (List.find_map (frame f1) f2s)
  with Not_found -> None
  )

let universal_to_substitutable fs =
  let logical_vars = List.unique (get_logical_vars (Star fs)) in
  let varmap = List.fold_left (
    fun varmap v -> 
      match v with
        | AVar v -> LogicalVarMap.add (AVar v) (Le_Var (fresh_e_suggest v)) varmap
        | EVar v -> varmap
  ) LogicalVarMap.empty logical_vars in 
  List.map (subs_vars varmap) fs
  

let function_app_inner f pre post_disjs = Profiler.track Profiler.CoreStar (fun () ->

  let pf, ppre, ppost_disjs, varmap = match (convert_to_pform (f :: (pre :: post_disjs))) with
    | (pf :: (ppre :: ppost_disjs)), varmap -> pf, ppre, ppost_disjs, varmap
    | _ -> raise CannotHappen in

  let convert_ppost_disjs =
    try
      Some (List.map Option.get (List.map Sepprover.convert ppost_disjs))
    with
      Invalid_argument ia -> None
  in

  let pfs = match (Sepprover.convert pf, convert_ppost_disjs) with
    | Some inner_f, Some inner_post_disjs -> 
        begin match (Sepprover.frame !logic inner_f ppre) with
        | Some frames ->

           let g f inner_post_disj = Sepprover.convert_back (Sepprover.conjoin_inner f inner_post_disj) in
           let h f = List.map (g f) inner_post_disjs in
             Some (List.map h frames)

        | None -> None
        end
    | _ -> None
  in
  (pfs, varmap)
  )


let function_app f pre post_disjs = Profiler.track Profiler.CoreStar (fun () ->
  let pre = rename_evars pre in
  let post_disjs = List.map rename_evars post_disjs in
  let (pre, post_disjs) = match universal_to_substitutable (pre :: post_disjs) with
        | a :: bs -> (a, bs)
        | _ -> raise CannotHappen in
  let pfs, varmap = function_app_inner f pre post_disjs in
  match pfs with

    | None -> Sepprover.print_counter_example (); None
    | Some poststates ->
        Some (List.map 
               (List.map (fun f -> convert_from_pform (invert_varmap varmap) f))
               poststates)
  )

let dump_corestar_rules () =

  print_string "\n============================================================\n";
  print_string "Dumping all corestar rules:";
  print_string "\n============================================================\n\n";
       
  let logic = !logic in
  let rs = logic.Psyntax.seq_rules in

    List.iter (Psyntax.pp_sequent_rule Format.std_formatter) rs


let add_rules new_rules =
    logic := {!logic with Psyntax.seq_rules = new_rules @ !logic.Psyntax.seq_rules}            
