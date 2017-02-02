open Parser_syntax
open Utils
open Batteries
open Js2jsil_constants

exception CannotHappen
exception No_Codename
exception EarlyError of string

let update_prev_annot prev_annot cur_annot =
	let is_spec_annot annot =
		(annot.annot_type == Parser_syntax.Requires) ||
			(annot.annot_type == Parser_syntax.Ensures) ||
			(annot.annot_type == Parser_syntax.EnsuresErr) || 
			(annot.annot_type == Parser_syntax.Id) ||
			(annot.annot_type == Parser_syntax.Rec) || 
			(annot.annot_type == Parser_syntax.Pred) || 
			(annot.annot_type == Parser_syntax.Fold) || 
			(annot.annot_type == Parser_syntax.Unfold) in

	let rec annot_has_specs annots =
		match annots with
		| [] -> false
		| annot :: rest_annots ->
			if (is_spec_annot annot)
				then true
				else annot_has_specs rest_annots in

	let rec filter_non_spec_annots annots specs_to_remain =
		match annots with
		| [] -> specs_to_remain
		| annot :: rest_annots ->
			if (is_spec_annot annot)
				then filter_non_spec_annots rest_annots (annot :: specs_to_remain)
				else filter_non_spec_annots rest_annots specs_to_remain in

	if (annot_has_specs cur_annot)
		then cur_annot
		else ((filter_non_spec_annots prev_annot []) @ cur_annot)


let get_predicate_defs_from_annots annots : JS_Logic_Syntax.js_logic_predicate list =
	let rec loop annots pred_defs = 
		match annots with 
		| [] -> pred_defs 
		| annot :: rest -> 
			let pred_defs = 
				if (annot.annot_type == Parser_syntax.Pred) 
					then  (
						(* Printf.printf "I am about to parse the following js_pred definition: %s\n" annot.annot_formula); *)
						(JSIL_Utils.js_logic_pred_def_of_string ("pred " ^ annot.annot_formula)) :: pred_defs 
					) else pred_defs in 
			loop rest pred_defs in 
	loop annots []


let parse_logic_annots annots = 
	List.map 
		(fun annot -> 
			let assertion = JSIL_Utils.js_assertion_of_string annot.annot_formula in
			(annot.annot_type, assertion))
		annots 				

let pop_relevant_logic_annots_stmt e = 
	let annots = e.Parser_syntax.exp_annot in 
	let folds, others = List.partition (fun annot -> annot.annot_type == Parser_syntax.Fold) annots in 
	let unfolds, others = List.partition (fun annot -> annot.annot_type == Parser_syntax.Unfold) others in 
	let invariant, others = List.partition (fun annot -> annot.annot_type == Parser_syntax.Invariant) others in
	
	let invariant = 
		(match invariant with 
		| [] -> None 
		| invariant :: _ -> Some (JSIL_Utils.js_assertion_of_string invariant.annot_formula)) in 								
	
	(* Printf.printf "Inside poppers with the following exp:\n%s\n\n\n" (Pretty_print.string_of_exp false e); *)
	
	let relevant_logic_annots, new_e = 
		(match e.exp_stx with 
		| Call (_, _)	| New (_, _) -> 
			(* Printf.printf "I am popping the relevant logical annotation from a function call, querida!\n"; *)
			let relevant_logic_annots = parse_logic_annots unfolds in 
			let new_e = { e with exp_annot = folds @ others } in 
			relevant_logic_annots, new_e 
		| _ -> 
			let relevant_logic_annots = parse_logic_annots (unfolds @ folds) in 
			let new_e = { e with exp_annot = others } in
			relevant_logic_annots, e) in 
	
	new_e, relevant_logic_annots, invariant 


let pop_relevant_logic_annots_expr e = 
	let annots = e.Parser_syntax.exp_annot in 
	let folds = List.filter (fun annot -> annot.annot_type == Parser_syntax.Fold) annots in 
	match e.exp_stx with 
	| Call (_, _) | New (_, _) -> 
		(* Printf.printf "pop relevant annotations call with the %d folds\n" (List.length folds); *)
		parse_logic_annots folds
	| _ -> []
	

let get_fold_unfold_invariant_annots annots = 
	let rec loop annots fold_unfold_cmds invariant = 
		match annots with 
		| [] -> fold_unfold_cmds, invariant 
		| annot :: rest -> 
			if ((annot.annot_type == Parser_syntax.Fold) || (annot.annot_type == Parser_syntax.Unfold)) then (
				let logic_cmd_str = annot.annot_formula in 
				let logic_cmd_pred = JSIL_Utils.js_assertion_of_string logic_cmd_str in
				loop rest ((annot.annot_type, logic_cmd_pred) :: fold_unfold_cmds) invariant
			) else if (annot.annot_type == Parser_syntax.Invariant) then (
				loop rest fold_unfold_cmds invariant
			) else loop rest fold_unfold_cmds invariant in 
	loop annots [] None 


let sanitise name =
	let s = Str.global_replace (Str.regexp "\$") "_" name in
	s

let update_annotation annots atype new_value =
  let old_removed = List.filter (fun annot -> annot.annot_type <> atype) annots in
  let annot = {annot_type = atype; annot_formula = new_value} in
	(* Printf.printf "I am adding the code name: %s"  new_value; *)
  annot :: old_removed

let update_codename_annotation annots fresh_name_generator =
	let ids = List.filter (fun annot -> annot.annot_type = Id) annots in
	(match ids with 
	| [ id ] -> update_annotation annots Codename id.annot_formula
	| _ :: _ -> raise (Failure "you cannot have more than one identifier per function")
	| _      -> update_annotation annots Codename (fresh_name_generator ()))

let get_codename exp =
  let codenames = List.filter (fun annot -> annot.annot_type = Codename) exp.exp_annot in
  match codenames with
    | [codename] -> codename.annot_formula
    | _ -> raise No_Codename

let flat_map f l = List.flatten (List.map f l)

let test_func_decl_in_block exp =
  let rec f in_block exp =
    let fo f e = match e with None -> false | Some e -> f e in
    match exp.exp_stx with
    | Script (_, es) -> List.exists (f false) es
    (* Expressions *)
    | This | Var _ | Num _ | String _ | Null | Bool _ | RegExp _ | Obj _
    | Array _ | Unary_op _ | BinOp _  | Delete _ | Assign _ | AssignOp _
    | Comma _ | Access _ | CAccess _ | ConditionalOp _ | Call _ | New _
    (* Statements *)
    | VarDec _ | Skip | Continue _ | Break _ | Return _ | Throw _ | Debugger -> false

    (* with is a syntax error in strict mode *)
    (* TODO: Move to a more appropriate pre-processing mapper function so we can get better errors *)
    | With _ -> true

    (* Statements with sub-Statements *)
    | Block es -> List.exists (f true) es
    | If (_, s, so) -> f true s || fo (f true) so
    | While (_, s) | DoWhile (s, _) | For (_, _, _, s)
    | ForIn (_, _, s) | Label (_, s) -> f true s
    | Switch (_, cs) -> List.exists (fun (_, s) -> f true s) cs
    | Try (s, sc, so) -> f true s || fo (fun (_, s) -> f true s) sc || fo (f true) so

    (* TODO: Ideally now the parser identifies these correctly, this test can be amended *)
    | FunctionExp _ | Function _ -> in_block
  in f true exp

let get_all_assigned_declared_identifiers exp =
  let rec fo is_lhs e = match e with None -> [] | Some e -> f is_lhs e
  and f is_lhs exp =
    match exp.exp_stx with
    (* Special Cases *)
    | Var v -> if is_lhs then [v] else []
    | VarDec vars -> flat_map (fun ve -> match ve with (v, None) -> [v] | (v, Some e)  -> v :: (f false e)) vars
    | Unary_op (op, e) -> (match op with Pre_Decr | Post_Decr | Pre_Incr | Post_Incr -> f true e | _ -> [])
    | Delete e -> (f true e)
    | Assign (e1, e2)
    | AssignOp (e1, _, e2) -> (f true e1) @ (f false e2)
    | Try (e1, eo2, eo3) -> (f false e1) @
                            BatOption.map_default (fun (id, e) -> id :: (f false e)) [] eo2 @
                            (fo false eo3)
    | ForIn (e1, e2, e3) -> (f true e1) @ (f false e2) @ (f false e3)
    | FunctionExp (_, n, vs, e) -> (Option.map_default (List.singleton) [] n) @ vs @ (f false e)
    | Function (_, n, vs, e) -> (Option.map_default (List.singleton) [] n) @ vs @ (f false e)

    (* Boring Cases *)
    | Num _ | String _ | Null | Bool _ | RegExp _ | This
    | Skip  | Break _  | Continue _ | Debugger -> []
    | Throw e | Access (e, _) | Label (_, e) -> f false e
    | Return eo -> fo false eo
    | While (e1, e2) | DoWhile (e1, e2) | BinOp (e1, _, e2)
    | CAccess (e1, e2) | Comma (e1, e2)
    | With (e1, e2)              -> (f false e1) @ (f false e2)
    | ConditionalOp (e1, e2, e3) -> (f false e1) @ (f false e2) @ (f false e3)
    | If (e1, e2, eo3)           -> (f false e1) @ (f false e2) @ (fo false eo3)
    | For (eo1, eo2, eo3, e4)    -> (fo false eo1) @ (fo false eo2) @ (fo false eo3) @ (f false e4)
    | Call (e1, e2s)
    | New (e1, e2s)              -> (f false e1) @ (flat_map (fun e2 -> f false e2) e2s)
    | Obj xs                     -> flat_map (fun (_,_,e) -> f false e) xs
    | Array es                   -> flat_map (fo false) es

    | Switch (e1, e2s) -> (f false e1) @ (flat_map
        (fun (e2, e3) -> (match e2 with | Case e2 -> f false e2 | DefaultCase -> []) @ (f false e3))
      e2s)

    | Block es
    | Script (_, es) -> flat_map (f is_lhs) es

  in f false exp




let test_expr_eval_arguments_assignment exp =
  List.exists (fun it -> it = "eval" || it = "arguments") (get_all_assigned_declared_identifiers exp)

let rec var_decls_inner exp =
  let f = var_decls_inner in
  let fo e = match e with None -> [] | Some e -> f e in
  match exp.exp_stx with
  | Num _	| String _	| Null	| Bool _	| Var _	| RegExp _	| This
  | Skip	| Return None	| Break _	| Continue _	| Debugger -> []
  | VarDec vars ->
		flat_map (fun ve -> match ve with (v, None) -> [v] | (v, Some e)  -> v :: (f e)) vars
  | Throw e	| Delete e	| Return (Some e)	| Access (e, _)	| Unary_op (_, e)	| Label (_, e) -> f e
  | While (e1, e2)	| DoWhile (e1, e2)	| BinOp (e1, _, e2)	| Assign (e1, e2)
  | AssignOp (e1, _, e2)	| CAccess (e1, e2)	| Comma (e1, e2)	| With (e1, e2)
  | Try (e1, Some (_, e2), None)	| Try (e1, None, Some e2)	| If (e1, e2, None) -> (f e1) @ (f e2)
  | If (e1, e2, Some e3)	| ForIn (e1, e2, e3)	| Try (e1, Some (_, e2), Some e3)
  | ConditionalOp (e1, e2, e3) -> (f e1) @ (f e2) @ (f e3)
  | For (e1, e2, e3, e4) ->	(fo e1) @ (fo e2) @ (fo e3) @ (f e4)
  | Call (e1, e2s)	| New (e1, e2s) -> (f e1) @ (flat_map (fun e2 -> f e2) e2s)
  | FunctionExp _	| Function _ -> []
  | Obj xs -> flat_map (fun (_,_,e) -> f e) xs
  | Array es -> flat_map (fun e -> match e with None -> [] | Some e -> f e) es
  | Try (_, None, None) -> raise CannotHappen
  | Switch (e1, e2s) ->
		(f e1) @ (flat_map (fun (e2, e3) ->
      (match e2 with
        | Case e2 -> f e2
        | DefaultCase -> []) @ (f e3)
     ) e2s)
  | Block es	| Script (_, es) -> flat_map f es

let var_decls exp = (List.unique (var_decls_inner exp))
                  (* List.append (List.unique (var_decls_inner exp)) [ "arguments" ] *)


let rec get_fun_decls exp : exp list =
	let f = get_fun_decls in
  let fo e = match e with None -> [] | Some e -> f e in
	let fcatch e =
		(match e with
		| None -> []
		| Some (_, e) -> f e
		| _ -> raise (Failure "illegal catch statement")) in
  match exp.exp_stx with
  | Num _
  | String _
  | Null
  | Bool _
  | Var _
  | RegExp _
  | This
  | Skip
  | Return None
  | Break _
  | Continue _
	| VarDec _
  | Debugger
 	| Throw _
  | Delete _
  | Return _
  | Access (_, _)
  | Unary_op (_, _)
	| BinOp (_, _, _)
  | Assign (_, _)
  | AssignOp (_, _, _)
  | CAccess (_, _)
  | Comma (_, _)
  | FunctionExp _
	| ConditionalOp (_, _, _)
	| Call (_, _)
	| Obj _
	| Array _
	| New (_, _) -> []
  | Label (_, e)
  | While (_, e)
  | DoWhile (e, _)
	| For (_, _, _, e)
  | ForIn (_, _, e)
	| With (_, e) -> f e
  | Try (e1, e2, e3) -> (f e1) @ (fcatch e2) @ (fo e3)
  | If (e1, e2, e3)-> (f e2) @ (fo e3)
 	| Switch (_, es) -> flat_map (fun (_, e) -> f e) es
  | Block es
  | Script (_, es) -> flat_map f es
  | Function (_, _, _, _) -> [ exp ]


let rec get_fun_exprs_expr exp =
  let f = get_fun_exprs_expr in
  let fo e = match e with None -> [] | Some e -> f e in
  match exp.exp_stx with
  | Num _
  | String _
  | Null
  | Bool _
  | Var _
  | RegExp _
  | This
  | Skip
  | Return None
  | Break _
  | Continue _
  | Debugger -> []
  | VarDec vars ->
		flat_map (fun ve -> match ve with (_, None) -> [ ] | (_, Some e)  -> f e) vars
  | Throw e
  | Delete e
	| Unary_op (_, e)
	| Access (e, _) -> f e
  | Return e -> fo e
	| BinOp (e1, _, e2)
  | Assign (e1, e2)
	| AssignOp (e1, _, e2)
	| CAccess (e1, e2)
	| Comma (e1, e2) -> (f e1) @ (f e2)
	| Call (e1, e2s)
  | New (e1, e2s) -> (f e1) @ (flat_map (fun e2 -> f e2) e2s)
  | Obj xs -> flat_map (fun (_,_,e) -> f e) xs
  | Array es -> flat_map (fun e -> match e with None -> [] | Some e -> f e) es
	| ConditionalOp (e1, e2, e3) -> (f e1) @ (f e2) @ (f e3)
  | FunctionExp _
  | Function    _ -> [ exp ]
	| Label (_,_)
  | While (_,_)
  | DoWhile (_,_)
  | With (_,_)
  | Try (_,_,_)
  | If (_,_,_)
  | ForIn (_, _,_)
  | For (_,_,_,_)
  | Switch (_, _)
  | Block _
  | Script (_,_) -> raise (Failure "statement in expression context... why you do this to me!?!")

and get_fun_exprs_stmt stmt =
	let f = get_fun_exprs_stmt in
	let fe = get_fun_exprs_expr in
  let fo s = match s with None -> [] | Some s -> f s in
	let feo s = match s with None -> [] | Some s -> fe s in
	let fcatch e =
		(match e with
		| None -> []
		| Some (_, e) -> f e
		| _ -> raise (Failure "illegal catch statement")) in
  match stmt.exp_stx with
	(* Literals *)
	| Null
	| Bool _
	| String _
	| Num _
	(* Expressions *)
	| This
	| Var _
	| Obj _
	| Access (_, _)
	| CAccess (_, _)
	| New (_, _)
	| Call (_, _)
	| FunctionExp _
	| Unary_op (_, _)
  | Delete _
  | BinOp (_, _, _)
  | Assign (_, _)
  | Array _
  | ConditionalOp (_, _, _)
  | AssignOp (_, _, _)
  | Comma (_, _)
  | RegExp _ -> fe stmt
  | Function _ -> []
	(* statements *)
	| Script (_, es)
  | Block es -> flat_map (fun e -> f e) es
  | VarDec vars -> flat_map (fun (_, e) -> feo e) vars
  | If (e1, e2, e3) -> (fe e1) @ (f e2) @ (fo e3)
  | While (e1, e2) -> (fe e1) @ (f e2)
  | DoWhile (e1, e2) -> (f e1) @ (fe e2)
  | Return e -> feo e
  | Try (e1, e2, e3) -> (f e1) @ (fcatch e2) @ (fo e3)
  | Throw e -> fe e
  | Continue _
  | Break _
	| Skip
	| Debugger -> []
  | Label (_, e) -> fe e
  | For (e1, e2, e3, e4) -> (feo e1) @ (feo e2) @ (feo e3) @ (f e4)
  | Switch (e1, sces) ->
		(fe e1) @
		(flat_map
			(fun (sc, ec2) ->
				let funs_sc = (match sc with
				| DefaultCase -> []
				| Case ec1 -> fe ec1) in
				funs_sc @ (f ec2))
			sces)
	| ForIn (e1, e2, e3) -> (fe e1) @ (fe e2) @ (f e3)
	| With (e1, e2) -> (f e1) @ (f e2)


let func_decls_in_elem exp : exp list =
    match exp.exp_stx with
      | Function (s, name, args, body) -> [exp]
      | _ ->  []

let rec func_decls_in_exp exp : exp list =
  match exp.exp_stx with
    | Script (_, es)
    | Block (es) -> List.flatten (List.map (func_decls_in_elem) es)
    | _ -> func_decls_in_elem exp


let get_all_vars_f f_body f_args =
  let f_decls = func_decls_in_exp f_body in
  let fnames = List.map (fun f ->
    match f.exp_stx with
      | Function (s, Some name, args, body) -> name
      | _ -> raise (Failure ("Must be function declaration " ^ (Pretty_print.string_of_exp true f)))
  ) f_decls in
  let vars = List.concat [f_args; (var_decls f_body); fnames] in
	vars


let rec add_codenames (main : string) 
											(fresh_anonymous : unit -> string) 
											(fresh_named : string -> string) 
											(fresh_catch_anonymous : unit -> string) 
											(prev_annot : Parser_syntax.annotation list) 
											exp =
		
	(* print_endline (Printf.sprintf "Annotation list length: %d" (List.length prev_annot)); *)
		
	let cur_annot = update_prev_annot prev_annot exp.Parser_syntax.exp_annot in
	
  let f = add_codenames main fresh_anonymous fresh_named fresh_catch_anonymous cur_annot in
  let fo e =
		(match e with
		| None -> None
		| Some e -> Some (f e)) in
  
	let m exp nstx = {exp with exp_stx = nstx} in
	
  match exp.exp_stx with
      (* Literals *)
      | Num _
      | String _
      | Null
      | Bool _
      | RegExp _
      | This
      | Var _
      | Skip
      | Break _
      | Continue _
      | Debugger -> exp
      | Delete e -> m exp (Delete (f e))
      | Access (e, x) -> m exp (Access (f e, x))
      | Unary_op (op, e) -> m exp (Unary_op (op, f e))
      | Throw e -> m exp (Throw (f e))
      | Label (l, e) -> m exp (Label (l, f e))
      | BinOp (e1, op, e2) -> m exp (BinOp (f e1, op, f e2))
      | Assign (e1, e2) -> m exp (Assign (f e1, f e2))
      | AssignOp (e1, op, e2)  -> m exp (AssignOp (f e1, op, f e2))
      | CAccess (e1, e2) -> m exp (CAccess (f e1, f e2))
      | Comma (e1, e2) -> m exp (Comma (f e1, f e2))
      | While (e1, e2) -> m exp (While (f e1, f e2))
      | DoWhile (e1, e2) -> m exp (DoWhile (f e1, f e2))
      | With (e1, e2) -> m exp (With (f e1, f e2))
      | Call (e1, e2s) -> m exp (Call (f e1, List.map f e2s))
      | New (e1, e2s) -> m exp (New (f e1, List.map f e2s))
      | FunctionExp (str, name, args, fb) -> 
				let new_annot = update_codename_annotation cur_annot fresh_anonymous in 
				{exp with exp_stx = FunctionExp (str, name, args, f fb); exp_annot = new_annot }
      | Function (str, Some name, args, fb) -> 
				let name_generator : unit -> string = (fun () -> fresh_named (sanitise name)) in 
				let new_annot = update_codename_annotation cur_annot name_generator in 
				{exp with exp_stx = Function (str, Some name, args, f fb); exp_annot = new_annot }
      | Obj xs -> m exp (Obj (List.map (fun (pn, pt, e) -> (pn, pt, f e)) xs))
      | Array es -> m exp (Array (List.map fo es))
      | ConditionalOp (e1, e2, e3)  -> m exp (ConditionalOp (f e1, f e2, f e3))
      | ForIn (e1, e2, e3) -> m exp (ForIn (f e1, f e2, f e3))
      | Return e -> m exp (Return (fo e))
      | VarDec vars -> m exp (VarDec (List.map (fun (n, e) -> (n, fo e)) vars))
      | Try (e1, catch, finally) ->
				(* Printf.printf "Processing the try in the add_code_names"; *)
				let catch_id = fresh_catch_anonymous () in
				let annot = [{annot_type = Codename; annot_formula = catch_id}] in
				let annotated_catch =
					(match catch with
          	| None -> None
          |	 Some (n, e) -> Some (n, f e)) in
				{ exp with exp_stx = (Try (f e1, annotated_catch, fo finally)); exp_annot = annot (*add_codename exp catch_id*) }
      | If (e1, e2, e3) -> m exp (If (f e1, f e2, fo e3))
      | For (e1, e2, e3, e4) -> m exp (For (fo e1, fo e2, fo e3, f e4))
      | Switch (e1, sces) -> m exp (Switch (f e1, List.map (fun (sc, e2) ->
        (match sc with
          | DefaultCase -> DefaultCase
          | Case e -> Case (f e)),
        f e2) sces))
      | Block es -> m exp (Block (List.map f es))
      | Script (str, es) ->
				let new_annot = update_codename_annotation cur_annot (fun () -> main) in 
        {exp with exp_stx = Script (str, List.map f es); exp_annot = new_annot }


let process_js_logic_annotations (vis_tbl : (string, string list) Hashtbl.t) fun_tbl fun_name (fun_args : string list) annotations requires_flag ensures_normal_flag ensure_err_flag var_to_fid_tbl vis_list =
	(* Printf.printf "Inside process_js_logic_annotations. function: %s.\n\nAnnotations: \n%s\n\n" fun_name (Pretty_print.string_of_annots annotations); *)
	
	let annot_types_str : string = String.concat ", " (List.map (fun annot -> Pretty_print.string_of_annot_type annot.annot_type) annotations) in 
	(* Printf.printf "annot types: %s\n\n" annot_types_str; *)

	let preconditions  = List.filter (fun annotation -> annotation.annot_type = requires_flag) annotations in
	let postconditions = List.filter (fun annotation -> (annotation.annot_type = ensures_normal_flag) || (annotation.annot_type = ensure_err_flag)) annotations in

	(* Printf.printf "number of preconditions: %d. number of postconditions: %d\n" (List.length preconditions) (List.length postconditions); *)

	let single_specs =
		if ((List.length preconditions) <> (List.length postconditions)) then (
			Printf.printf "WARNING: In %s, preconditions do NOT match postconditions.\n" fun_name;
			[] ) else
		List.map2
		(fun pre post ->
			let pre_str   = pre.annot_formula in
			let post_str  = post.annot_formula in
			let ret_flag  =
				(match post.annot_type with
				| ensures_normal_flag -> JSIL_Syntax.Normal
				| ensure_err_flag     -> JSIL_Syntax.Error) in
			(* Printf.printf "pre_str: %s. post_str: %s\n" pre_str post_str; *)
			let pre_js  = JSIL_Utils.js_assertion_of_string pre_str in
			let post_js = JSIL_Utils.js_assertion_of_string post_str in
			(* Printf.printf "I managed to parse the js assertions\n"; *)
			
			let scope_vars_pre = JS_Logic_Syntax.get_scope_vars pre_js in 
			let scope_vars_post = JS_Logic_Syntax.get_scope_vars post_js in 
			let scope_vars = JSIL_Syntax.SS.union scope_vars_pre scope_vars_post in 
			let new_var_to_fid_tbl = JS_Logic_Syntax.filter_var_to_fid_tbl var_to_fid_tbl scope_vars fun_name in
			
			let pre_jsil = JS_Logic_Syntax.js2jsil_logic_top_level_pre pre_js new_var_to_fid_tbl vis_tbl fun_tbl fun_name in
			let post_jsil = JS_Logic_Syntax.js2jsil_logic_top_level_post post_js new_var_to_fid_tbl vis_tbl fun_tbl fun_name in
			let new_spec = JSIL_Syntax.create_single_spec pre_jsil post_jsil ret_flag in
			new_spec)
		preconditions
		postconditions in

	let f_rec =
		let f_recs = List.filter (fun annotation -> annotation.annot_type = Rec) annotations in
		(match f_recs with
		 | [ f_rec_annot ] -> if (f_rec_annot.annot_formula = "false") then false else true
		 | _ -> true) in

	let args = 
		if (fun_name = Js2jsil_constants.var_main)
			then fun_args 
			else (Js2jsil_constants.var_scope :: (Js2jsil_constants.var_this :: fun_args)) in 

	let fun_spec = if ((List.length single_specs) > 0)
		then Some (JSIL_Syntax.create_jsil_spec fun_name args single_specs)
		else None in
	fun_spec, f_rec


(**
vis_tbl fun_tbl fun_name (fun_args : string list) annotations requires_flag ensures_normal_flag ensure_err_flag var_to_fid_tbl vis_list
*)

let create_js_logic_annotations vis_tbl (old_fun_tbl : Js2jsil_constants.pre_fun_tbl_type) (new_fun_tbl : Js2jsil_constants.fun_tbl_type) =
	Hashtbl.iter 
		(fun f_id (f_id, f_args, f_body, (annotations, vis_list, var_to_fid_tbl)) ->
			let fun_specs, f_rec = 
				if (not (f_id = Js2jsil_constants.var_main))
					then process_js_logic_annotations vis_tbl old_fun_tbl f_id f_args annotations Requires Ensures EnsuresErr var_to_fid_tbl vis_list 
					else process_js_logic_annotations vis_tbl old_fun_tbl f_id [] annotations TopRequires TopEnsures TopEnsuresErr var_to_fid_tbl vis_list in 
			Hashtbl.add new_fun_tbl f_id (f_id, f_args, f_body, f_rec, fun_specs))
		old_fun_tbl


let update_fun_tbl (fun_tbl : Js2jsil_constants.pre_fun_tbl_type) (f_id : string) (f_args : string list) f_body annotations (var_to_fid_tbl : (string, string) Hashtbl.t) (vis_list : string list) =
	(* let fun_spec, f_rec = process_js_logic_annotations f_id f_args annotations Requires Ensures EnsuresErr var_to_fid_tbl vis_list in *)
	Hashtbl.replace fun_tbl f_id (f_id, f_args, f_body, (annotations, vis_list, var_to_fid_tbl))


let update_cc_tbl cc_tbl f_parent_id f_id f_args f_body =
	let f_parent_var_table = get_scope_table f_parent_id cc_tbl in 
	let new_f_tbl = Hashtbl.create 101 in
	Hashtbl.iter
		(fun x x_f_id -> Hashtbl.add new_f_tbl x x_f_id)
		f_parent_var_table;
	let f_vars = get_all_vars_f f_body f_args in
	List.iter
		(fun v -> Hashtbl.replace new_f_tbl v f_id)
		f_vars;
	Hashtbl.add cc_tbl f_id new_f_tbl;
	new_f_tbl

let update_cc_tbl_single_var_er cc_tbl f_parent_id f_id  x =
	let f_parent_var_table =
		try Hashtbl.find cc_tbl f_parent_id
		with _ ->
			let msg = Printf.sprintf "the parent function of %s -- %s -- was not found in the cc table" f_id f_parent_id in
			raise (Failure msg) in
	let new_f_tbl = Hashtbl.create 101 in
	Hashtbl.iter
		(fun x x_f_id -> Hashtbl.add new_f_tbl x x_f_id)
		f_parent_var_table;
	Hashtbl.replace new_f_tbl x f_id;
	Hashtbl.add cc_tbl f_id new_f_tbl;
	new_f_tbl

let get_top_level_annot e =
	match e.Parser_syntax.exp_stx with
	| Script (_, les) ->
		let first_le = List.nth les 0 in
		let annot = first_le.Parser_syntax.exp_annot in
		Some annot
	| _ -> None



let rec get_predicate_definitions pred_defs e = 
	let f = get_predicate_definitions in 
	let fo pred_defs e = match e with | Some e -> f pred_defs e | None -> pred_defs in 
	let analyse_cases pred_defs cases = 
		List.fold_left (fun pred_defs (_, s_case) -> get_predicate_definitions pred_defs s_case) pred_defs cases in  
	let new_pred_defs : JS_Logic_Syntax.js_logic_predicate list = (get_predicate_defs_from_annots e.Parser_syntax.exp_annot) @ pred_defs in 
	match e.exp_stx with 
	(* expressions *)
	|	Num _	| String _	|	Null	| Bool _	| Var _	| This | Delete _ | Unary_op (_, _) 
	| Access (_, _) | Comma (_, _) | BinOp (_, _, _) | Assign (_, _) | AssignOp(_, _, _) 
	| CAccess (_, _) | ConditionalOp (_, _, _) | Call (_, _) | New (_, _) 
	| FunctionExp (_, _, _, _) | Obj _ | Array _ -> new_pred_defs
	(* statement *) 
	| Label (_, s)                              -> f new_pred_defs s  
	| If (_, s1, s2)                            -> fo (f new_pred_defs s1) s2
	| While (_, s) | DoWhile (s, _) 	 
	| For(_, _, _, s) | ForIn (_, _, s)         -> (f new_pred_defs s)
	| Skip | Break _ |	Continue _ | Debugger 
	| Throw _ | Return _ | VarDec _             -> new_pred_defs
	| Script (_, ss) | Block ss                 -> List.fold_left get_predicate_definitions new_pred_defs ss 
	| Try (s1, Some (_, s2), s3)                -> fo (f (f new_pred_defs s1) s2) s3
	| Try (s1, None, s2)                        -> fo (f new_pred_defs s1) s2
	| Switch (_, cases)                         -> analyse_cases new_pred_defs cases  
	| Function (_, _, _, s)                     -> f new_pred_defs s
	(* Non-supported constructs *)
	| RegExp _ | With (_, _)                    -> raise (Failure "JS Construct Not Supported")     		 



let rec ground_fold_annotations folds e = 
	
	let cur_folds, rest_annots = List.partition (fun annot -> annot.annot_type = Parser_syntax.Fold) e.exp_annot in 
		
	let next_folds = 
		match e.exp_stx with
		| New (_, _) | Call (_, _) -> []
		| _ -> folds @ cur_folds in 
	
	let f = ground_fold_annotations next_folds in 
	let f_empty_optional eo = 
		(match eo with 
		| None   -> None
		| Some e -> 
			let e', _ = ground_fold_annotations [] e in 
			Some e') in 
	
	let f_2 e1 e2 = 
		let e1', found_fun_call_1 = f e1 in 
		if (found_fun_call_1) 
			then e1', e2, true 
			else (
				let e2', found_fun_call_2 = f e2 in 
				e1', e2', found_fun_call_2
				) in 
	
	let f_3 e1 e2 e3 = 
		let e1', e2', found_fun_call = f_2 e1 e2 in 
		if (found_fun_call) 
			then e1', e2', e3, true 
			else (
				let e3', found_fun_call_3 = f e3 in 
				e1', e2', e3', found_fun_call_3 
			) in 
	
	let rec f_arr es traversed_es =
		match es with 
		| [] -> (List.rev traversed_es), false
		| e :: rest_es -> 
			(match e with 
			| None -> f_arr rest_es (e :: traversed_es)
			| Some e -> 
				let e', found_fun_call = f e in 
				if (found_fun_call) 
					then (List.rev traversed_es) @ ((Some e') :: rest_es), true
					else f_arr rest_es ((Some e') :: traversed_es)) in 
	
	let rec f_var_decl vdecls traversed_vdecls = 
		match vdecls with 
		| [] -> (List.rev traversed_vdecls), false
		| (v, eo) :: rest_vdecls -> 
			(match eo with 
			| None -> f_var_decl rest_vdecls ((v, eo) :: traversed_vdecls) 
			| Some e -> 
				let e', found_fun_call = f e in 
				if (found_fun_call) 
					then (
						(* Printf.printf "ground_fold_annotations: Inside f_var_decl and I found an initialiser baby! 
							I had a function call inside ME!!! And... I have %d folds to propagate to that poor function call!!\n"
							(List.length next_folds); *)
						(List.rev traversed_vdecls) @ ((v, Some e') :: vdecls), true
					) else f_var_decl rest_vdecls ((v, Some e') :: traversed_vdecls)) in 
	
	let f_cases cases = 
		List.map 
			(fun (e, s) -> 
				let e' = 
					match e with 
					| DefaultCase -> DefaultCase 
					| Case e -> 
						let e', _ = ground_fold_annotations [] e in 
						Case e' in 
				let s', _ = ground_fold_annotations [] s in 
				(e', s'))
			cases in
	
	let rec loop_obj_props props processed_props = 
		match props with 
		| [] -> false, (List.rev processed_props)
		| (x, p, e) :: rest_props -> 
			let e', found_fun_call = f e in 
			if (found_fun_call)  
				then true, ((List.rev processed_props) @ ((x, p, e') :: rest_props))
				else loop_obj_props rest_props ((x, p, e) :: processed_props) in
 	
	let new_exp_stx, has_inner_fun_call = 				
		match e.exp_stx with
 		(* Literals *)
		| Null | Bool _ | String _ | Num _ -> e.exp_stx, false
		(* Expressions *)
		| This | Var _ -> e.exp_stx, false 
		| Obj xs -> 
			let found_fun_call, xs' = loop_obj_props xs [] in 
			Obj xs', found_fun_call
		| Access (e, v) -> 
			let e', found_fun_call = f e in 
			Access (e', v), found_fun_call 
		| CAccess (e1, e2) -> 
			let e1', e2', found_fun_call = f_2 e1 e2 in 
			CAccess (e1', e2'), found_fun_call
		| New (e1, e2s) | Call (e1, e2s) -> e.exp_stx, true
		| FunctionExp (b, f_name, args, fb) -> 
			(* Printf.printf "I got a ****FUNCTION*** BABY!!!!\n"; *)
			let fb', _ = ground_fold_annotations [] fb in 
			FunctionExp (b, f_name, args, fb'), false
  	| Function (b, f_name, args, fb) ->
			let fb', _ = ground_fold_annotations [] fb in 
			Function (b, f_name, args, fb'), false
 		| Unary_op (op, e) -> 
			let e', found_fun_call = f e in
			Unary_op (op, e'), found_fun_call  
		| Delete e ->
			let e', found_fun_call = f e in 
			Delete e', found_fun_call 
		| BinOp (e1, op, e2) ->
			let e1', e2', found_fun_call = f_2 e1 e2 in 
			BinOp (e1', op, e2'), found_fun_call 
		| Assign (e1, e2) -> 
			let e1', e2', found_fun_call = f_2 e1 e2 in 
			Assign (e1', e2'), found_fun_call 
		| Array es -> 
			let es', found_fun_call = f_arr es [] in 
			Array es', found_fun_call 
		| ConditionalOp (e1, e2, e3) -> 
			let e1', e2', e3', found_fun_call = f_3 e1 e2 e3 in 
			ConditionalOp (e1', e2', e3'), found_fun_call
		| AssignOp (e1, op, e2) -> 
			let e1', e2', found_fun_call = f_2 e1 e2 in 
			AssignOp (e1', op, e2'), found_fun_call 
		| Comma (e1, e2) -> 
			let e1', e2', found_fun_call = f_2 e1 e2 in 
			Comma (e1', e2'), found_fun_call 
	 	| VarDec vars -> 
			let vdecls', found_fun_call = f_var_decl vars [] in 
			(* Printf.printf "I processed a vardec. found_fun_call:%b\n" found_fun_call; *)
			VarDec vdecls', found_fun_call 
		| RegExp _	-> raise (Failure "construct not supported yet")
		(* statements *) 
		| Script (b, es) -> 
			(* Printf.printf "I got a ****SCRIPT*** BABY!!!!\n"; *)
			let es' = List.map (fun e -> let e', _ = ground_fold_annotations [] e in e') es in 
			Script (b, es'), false 
		| Block es -> 
			(* Printf.printf "I got a ****BLOCK*** BABY!!!!\n"; *)
			(* Printf.printf "ground_fold_annotations I found a block statement!!!\n"; *)
			let es' = List.map (fun e -> let e', _ = ground_fold_annotations [] e in e') es in 
			Block es', false 
		| Skip -> Skip, false
		| If (e, s1, s2) -> 
			let e', _ = ground_fold_annotations [] e in 
			let s1', _ = ground_fold_annotations [] s1 in 
			let s2' = f_empty_optional s2 in
			If (e', s1', s2'), false 
		| While (e,s) ->
			let e', _ = ground_fold_annotations [] e in 
			let s', _ = ground_fold_annotations [] s in 
			While (e', s'), false
 	 	| DoWhile (s, e) ->
			let s', _ = ground_fold_annotations [] s in
			let e', _ = ground_fold_annotations [] e in 
			DoWhile (s', e'), false
 		| Return e -> 
			let e' = f_empty_optional e in 
			Return e', false
		| Try (s1, None, s3) -> 
			let s1', _ = ground_fold_annotations [] s1 in
			let s3' = f_empty_optional s3 in 
			Try (s1', None, s3'), false
		| Try (s1, Some (x, s2), s3) -> 
			let s1', _ = ground_fold_annotations [] s1 in
			let s2', _ = ground_fold_annotations [] s2 in
			let s3' = f_empty_optional s3 in 
			Try (s1', Some (x, s2'), s3'), false
		| Throw e -> 
			let e', _ = ground_fold_annotations [] e in
			Throw e', false
		| Continue lab -> Continue lab, false
		| Break lab -> Break lab, false 
		| Label (lab, s) -> 
			let s', _ = ground_fold_annotations [] s in
			Label (lab, s'), false 
		| For (e1, e2, e3, s) ->
			let e1' = f_empty_optional e1 in 
			let e2' = f_empty_optional e2 in 
			let e3' = f_empty_optional e3 in 
			let s', _ = ground_fold_annotations [] s in 
			For (e1', e2', e3', s'), false
		| Switch (e, s_cases) -> 
			let e', _ = ground_fold_annotations [] e in 
			let s_cases' = f_cases s_cases in 
			Switch (e', s_cases'), false 
		| ForIn (e1, e2, s) -> 
			let e1', _ = ground_fold_annotations [] e1 in 
			let e2', _ = ground_fold_annotations [] e2 in 
			let s', _ = ground_fold_annotations [] s in 
			ForIn (e1', e2', s'), false
		| With (e, s) -> 
			let e', _ = ground_fold_annotations [] e in 
			let s', _ = ground_fold_annotations [] s in 
			With (e', s'), false
		| Debugger -> Debugger, false in 
	
	match new_exp_stx, has_inner_fun_call with 
	| New (e1, e2s), _ | Call (e1, e2s), _ ->
		(* Printf.printf "In the pooooor function call with %d propagated folds and %d original folds!!!!\n" 
			(List.length folds) (List.length  cur_folds); *)
		let new_e = { exp_offset = e.exp_offset; exp_stx = new_exp_stx; exp_annot = folds @ cur_folds @ rest_annots } in 
		new_e, true 	
	| _, false -> 
		let new_e = { exp_offset = e.exp_offset; exp_stx = new_exp_stx; exp_annot = cur_folds @ rest_annots } in 
		(* Printf.printf "I didn't propagate shit. but perhaps my submodules did. Here is the potentially new me:\n%s\n"
			(Pretty_print.string_of_exp true new_e); *)
		new_e, false 
	| _, true -> 
		(* Printf.printf "I am in the case in which I am deleting annotations from the node. I am deleting %d annotations and %d will remain\n"
			(List.length cur_folds) (List.length rest_annots); *)
		let new_e = { exp_offset = e.exp_offset; exp_stx = new_exp_stx; exp_annot = rest_annots } in 
		(* Printf.printf "Here is the new exp withouth the folds that were deleted:\n%s\n" (Pretty_print.string_of_exp true new_e); *)
		new_e, true 
			



let rec closure_clarification_expr cc_tbl (fun_tbl : Js2jsil_constants.pre_fun_tbl_type) vis_tbl f_id visited_funs prev_annot e =

	let cur_annot = update_prev_annot prev_annot e.Parser_syntax.exp_annot in

	let f = closure_clarification_expr cc_tbl fun_tbl vis_tbl f_id visited_funs cur_annot in
	let fo e = 
		(match e with
		| None   -> ()
		| Some e -> f e) in

	(* Printf.printf "Traversing the js code inside closure_clarification_expr. current annotation: %s\n"
		(Pretty_print.string_of_annots e.exp_annot); *)

	match e.exp_stx with
  (* Literals *)
	| Null | Bool _ | String _ | Num _
	(* Expressions *)
	| This | Var _ -> ()
	| Obj xs -> List.iter (fun (_, _, e) -> f e) xs
	| Access (e, v)                  -> f e
	| CAccess (e1, e2)               -> (f e1); (f e2)
	| New (e1, e2s) | Call (e1, e2s) -> f e1; (List.iter f e2s)
  | FunctionExp (_, f_name, args, fb)
  | Function (_, f_name, args, fb) ->
    begin match f_name with
    | None ->
      let new_f_id = get_codename e in
      let new_f_tbl = update_cc_tbl cc_tbl f_id new_f_id args fb in
      update_fun_tbl fun_tbl new_f_id args fb cur_annot new_f_tbl (new_f_id :: visited_funs);
      Hashtbl.replace vis_tbl new_f_id (new_f_id :: visited_funs);
      closure_clarification_stmt cc_tbl fun_tbl vis_tbl new_f_id (new_f_id :: visited_funs) [] fb
    | Some f_name ->
      let new_f_id = get_codename e in
      let new_f_id_outer = new_f_id ^ "_outer" in
      let _ = update_cc_tbl_single_var_er cc_tbl f_id new_f_id_outer f_name in
      let new_f_tbl = update_cc_tbl cc_tbl new_f_id_outer new_f_id args fb in
      update_fun_tbl fun_tbl new_f_id args fb cur_annot new_f_tbl (new_f_id :: new_f_id_outer :: visited_funs);
      Hashtbl.replace vis_tbl new_f_id (new_f_id :: new_f_id_outer :: visited_funs);
      closure_clarification_stmt cc_tbl fun_tbl vis_tbl new_f_id (new_f_id :: new_f_id_outer :: visited_funs) [] fb
    end
  | Unary_op (_, e)   | Delete e -> f e
	| BinOp (e1, _, e2) | Assign (e1, e2) -> f e1; f e2
  | Array es -> List.iter fo es
  | ConditionalOp (e1, e2, e3) -> f e1; f e2; f e3
  | AssignOp (e1, _, e2) | Comma (e1, e2) -> f e1; f e2
	| VarDec vars -> List.iter (fun (_, e) -> fo e) vars
  | RegExp _	-> ()
	(*Statements*)
  | Script (_, _) | Block _  | Skip _  | If (_, _, _) | While (_,_)
  | DoWhile (_, _) | Return _ | Try (_, _, _) | Throw _ | Continue _ 
  | Break _ | Label (_, _) | For (_, _, _, _) | Switch (_, _) 
	| ForIn (_, _, _) | With (_, _) | Debugger -> 
		raise (Failure "statement in expression context - closure clarification")
and
closure_clarification_stmt cc_tbl fun_tbl vis_tbl f_id visited_funs prev_annot e =
	let cur_annot = update_prev_annot prev_annot e.Parser_syntax.exp_annot in

	let f = closure_clarification_stmt cc_tbl fun_tbl vis_tbl f_id visited_funs cur_annot in
	let fe = closure_clarification_expr cc_tbl fun_tbl vis_tbl f_id visited_funs cur_annot in
	let fo e = (match e with
	| None -> ()
	| Some e -> f e) in
	let feo e = (match e with
	| None -> ()
	| Some e -> fe e) in

	(* Printf.printf "Traversing the js code inside closure_clarification_expr. current annotation: %s\n"
		(Pretty_print.string_of_annots e.exp_annot); *)

	match e.exp_stx with
  (* Literals *)
	| Null
	| Bool _
	| String _
	| Num _
	(* Expressions *)
	| This
	| Var _
	| Obj _
	| Access (_, _)
	| CAccess (_, _)
	| New (_, _)
	| Call (_, _)
	| FunctionExp _
	| Unary_op (_, _)
  | Delete _
  | BinOp (_, _, _)
  | Assign (_, _)
  | Array _
  | ConditionalOp (_, _, _)
  | AssignOp (_, _, _)
  | Comma (_, _)
  | RegExp _ -> fe e
	(*Statements*)
	| Function (_, f_name, args, fb) ->
		let new_f_id = get_codename e in
		let new_f_tbl = update_cc_tbl cc_tbl f_id new_f_id args fb in
		update_fun_tbl fun_tbl new_f_id args fb cur_annot new_f_tbl (new_f_id :: visited_funs);
		Hashtbl.replace vis_tbl new_f_id (new_f_id :: visited_funs);
		closure_clarification_stmt cc_tbl fun_tbl vis_tbl new_f_id (new_f_id :: visited_funs) [] fb
  | Script (_, es) -> List.iter f es
  | Block es -> List.iter f es
  | VarDec vars -> List.iter (fun (_, e) -> feo e) vars
  | Skip -> ()
  | If (e1, e2, e3) -> fe e1; f e2; fo e3
  | While (e1, e2) -> fe e1; f e2
  | DoWhile (e1, e2) -> f e1; fe e2
  | Return e -> feo e
  | Try (e1, Some (x, e2), e3) ->
		f e1; fo e3;
		let new_f_id = get_codename e in
		update_cc_tbl_single_var_er cc_tbl f_id new_f_id x;
		closure_clarification_stmt cc_tbl fun_tbl vis_tbl new_f_id (new_f_id :: visited_funs) cur_annot e2
  | Try (e1, None, e3) -> f e1; fo e3
  | Throw e -> fe e
  | Continue _
  | Break _ -> ()
  | Label (_, e) -> f e
  | For (e1, e2, e3, e4) -> feo e1; feo e2; feo e3; f e4
  | Switch (e1, sces) ->
		fe e1;
		List.iter
			(fun (sc, ec2) ->
				(match sc with
				| DefaultCase -> ()
				| Case ec1 -> fe ec1);
				f ec2)
			sces
	| ForIn (e1, e2, e3) -> fe e1; fe e2; f e3
	| With (e1, e2) -> f e1; f e2
	| Debugger -> ()


let closure_clarification_top_level cc_tbl (fun_tbl : Js2jsil_constants.fun_tbl_type) (old_fun_tbl: Js2jsil_constants.pre_fun_tbl_type)  vis_tbl proc_id e vis_fid args =
	let proc_tbl = Hashtbl.create Js2jsil_constants.medium_tbl_size in

	let proc_vars = get_all_vars_f e [] in
	List.iter
		(fun v -> Hashtbl.replace proc_tbl v proc_id)
		proc_vars;
	Hashtbl.add cc_tbl proc_id proc_tbl;
	Hashtbl.add old_fun_tbl proc_id (proc_id, args, e, ([], [ proc_id ], proc_tbl));
	Hashtbl.add vis_tbl proc_id vis_fid;
	closure_clarification_stmt cc_tbl old_fun_tbl vis_tbl proc_id vis_fid [] e;
	create_js_logic_annotations vis_tbl old_fun_tbl fun_tbl;
	let js_predicate_definitions : JS_Logic_Syntax.js_logic_predicate list = get_predicate_definitions [] e in  
	let jsil_predicate_definitions = 
		List.map (fun pred_def -> JS_Logic_Syntax.translate_predicate_def pred_def vis_tbl old_fun_tbl) js_predicate_definitions in 

	let annots = get_top_level_annot e in
	(match annots with
	| Some annots ->
		(* Printf.printf "Going to generate main. Top-level annotations:\n%s\n" (Pretty_print.string_of_annots annots); *)
		let specs, _ = process_js_logic_annotations vis_tbl old_fun_tbl proc_id [] annots TopRequires TopEnsures TopEnsuresErr proc_tbl [ proc_id ] in
		Hashtbl.replace fun_tbl proc_id (proc_id, args, e, false, specs);
	| None -> ()); 
	let jsil_pred_def_tbl = JSIL_Logic_Utils.pred_def_tbl_from_list jsil_predicate_definitions in 
	jsil_pred_def_tbl
	



let rec print_cc_tbl cc_tbl =
	let print_fun_tbl fun_tbl =
		Hashtbl.fold
			(fun v fun_v ac ->
				let v_fun_v_str = "(" ^ v ^ ", " ^ fun_v ^ ")" in
				if (ac = "")
					then v_fun_v_str
					else ac ^ ", " ^ v_fun_v_str)
			fun_tbl
			"" in
	Hashtbl.fold
		(fun f_id f_tbl ac ->
			let f_tbl_str : string = print_fun_tbl f_tbl in
			let f_str = f_id ^ ": " ^ f_tbl_str ^ "\n" in
			ac ^ f_str)
		cc_tbl
		""

let rec returns_empty_exp (e : Parser_syntax.exp) =
let get_some e =
	(match e with
	| None -> false
	| Some e -> returns_empty_exp e) in
let rec returns_empty_exp_list (el : Parser_syntax.exp list) =
	(match el with
	| [] -> true
	| e :: el ->
		let reeel = returns_empty_exp_list el in
		if (returns_empty_exp e) then true else reeel) in
match e.exp_stx with
  | Null
  | Num _
  | String _
  | Bool _
  | Var _
  | Delete _
  | Unary_op (_, _)
  | BinOp (_, _, _)
  | Access (_, _)
  | New (_, _)
  | CAccess (_, _)
  | Assign (_, _)
  | AssignOp (_, _, _)
  | Comma (_, _)
  | ConditionalOp (_, _, _)
  | Obj _
  | Array _
  | RegExp (_, _)
  | FunctionExp _
  | Function _
  | Call (_, _)
	| This
  | Throw _
  | Return _
  | Debugger ->
			false

  | Label (_, e)
	| DoWhile (e, _) -> returns_empty_exp e

  | If (e, et, ee) ->
			let reeet = returns_empty_exp et in
			let reeee = get_some ee in
			if reeet then true else reeee

  | Try (et, ec, ef) ->
			let reeet = returns_empty_exp et in
			let reeec =
				match ec with
				| None -> false
				| Some (_, ec) -> returns_empty_exp ec in
			let reeef = get_some ef in
			if reeet then true else
				if reeec then true else
					reeef

  | Block el
  | Script (_, el) ->
			returns_empty_exp_list el

  | Switch (_, ese) ->
		let (_, el) = List.split ese in
			returns_empty_exp_list el

  | For (_, _, _, _)
  | ForIn (_, _, _)
	| While (_, _)
	| VarDec _
  | Break _
  | Continue _
  | Skip ->
			true
	| _ -> raise (Failure "unsupported construct by Petar M.")


let generate_offset_lst str =
	let rec traverse_str ac_offset cur_str offset_lst =
		let new_line_index =
			(try String.index cur_str '\n' with
				| _ -> -1) in
			if new_line_index == -1 then
				offset_lst
			else
				let len = String.length cur_str in
				let new_str = (try String.sub cur_str (new_line_index + 1) ((len - new_line_index) - 1) with | _ -> "") in
				traverse_str (ac_offset + new_line_index + 1) new_str (offset_lst @ [ (ac_offset + new_line_index + 1) ]) in
		traverse_str 0 str []

let jsoffsetchar_to_jsoffsetline c_offset offset_list =
	let rec offsetchar_to_offsetline_aux offset_list cur_line =
		match offset_list with
		| [] -> cur_line
		| hd :: rest ->
			if c_offset < hd
				then
					cur_line
				else
					offsetchar_to_offsetline_aux rest (cur_line + 1) in
		offsetchar_to_offsetline_aux offset_list 1

let memoized_offsetchar_to_offsetline str =
	let offset_list = generate_offset_lst str in
	let ht = Hashtbl.create (String.length str) in
	  fun c_offset ->
			try Hashtbl.find ht c_offset
			with Not_found ->
				begin
				let l_offset =  jsoffsetchar_to_jsoffsetline c_offset offset_list in
					Hashtbl.add ht c_offset l_offset;
					l_offset
				end

let test_early_errors e =
  if test_func_decl_in_block e then raise (EarlyError "Function declaration in statement position or use of `with`");
  if test_expr_eval_arguments_assignment e then raise (EarlyError "Expression assigns to `eval` or `arguments`.")



(** Ideally I would like to use to use the following to iterate over the 
grammar of JavaScript, but it is not trivial... **)
let rec js_iterator f_iter e = 
	let f = js_iterator f_iter in 
	let fo e = match e with | Some e -> f e | None -> () in 
	let analyse_cases cases = 
		List.iter 
			(fun (e_case, s_case) -> (match e_case with | Case e -> f e | DefaultCase -> ()); f s_case) 
			cases in 
	let e_stx = e.exp_stx in 
	let recurse = f_iter e_stx in 
	if (not recurse) then () else (
	match e_stx with 
	(* expressions *)
	|	Num _	| String _	|	Null	| Bool _	| Var _	| This      -> ()
  | Delete e | Unary_op (_, e) | Access (e, _)              -> f e  
	| Comma (e1, e2) | BinOp (e1, _, e2) | Assign (e1, e2) 
			| AssignOp(e1, _, e2) | CAccess (e1, e2)              -> f e1; f e2
	| ConditionalOp (e1, e2, e3)                              -> f e1; f e2; f e3  
	| Call (e, es) | New (e, es)                              -> f e; (List.iter (fun e -> f e) es)
  | FunctionExp (_, _, _, s)                                -> f s
	| Obj pes                                                 -> List.iter (fun (_, _, e) -> f e) pes
	| Array es                                                -> List.iter (fun e -> fo e) es
	(* statement *) 
	| Label (_, s)                              -> f s  
	| If (e, s1, s2)                            -> f e; f s1; fo s2
	| While (e, s)                              -> f e; f s
	| DoWhile (s, e) 		                        -> f s; f e
	| Skip | Break _ |	Continue _ | Debugger 	-> () 
	| Throw e                                   -> f e
	| Return e                                  -> fo e 
	| Script (_, ss) | Block ss                 -> List.iter f ss
 	| VarDec ves                                -> List.iter (fun ve -> match ve with (v, None) -> () | (v, Some e)  -> f e) ves
	| For(e1, e2, e3, s)                        -> fo e1; fo e2; fo e3; f s 
	| ForIn (e1, e2, s)                         -> f e1; f e2; f s
	| Try (s1, Some (_, s2), s3)                -> f s1; f s2; fo s3
	| Try (s1, None, s2)                        -> f s1; fo s2
	| Switch (e, cases)                         -> f e; analyse_cases cases  
	| Function (_, _, _, s)                     -> f s
	(* Non-supported constructs *)
	| RegExp _ | With (_, _)                    -> raise (Failure "JS Construct Not Supported"))     		 



let rec js_accumulator_top_down f_acc ac e = 
	let f = js_accumulator_top_down f_acc in 
	let fo ac e = match e with | Some e -> f ac e | None -> ac in 
	let analyse_cases ac cases = 
		List.fold_left 
			(fun ac (e_case, s_case) -> f (match e_case with | Case e -> f ac e | DefaultCase -> ac) s_case) 
			ac
			cases in 
	let e_stx = e.exp_stx in 
	match e_stx with 
	(* expressions *)
	|	Num _	| String _	|	Null	| Bool _	| Var _	| This      -> ac
  | Delete e | Unary_op (_, e) | Access (e, _)              -> f ac e   
	| Comma (e1, e2) | BinOp (e1, _, e2) | Assign (e1, e2) 
			| AssignOp(e1, _, e2) | CAccess (e1, e2)              -> f e2 (f ac e1)
	| ConditionalOp (e1, e2, e3)                              -> f (f (f ac e1) e2) e3 
	| Call (e, es) | New (e, es)                              -> (List.fold_left f (f ac e) es)
  | FunctionExp (_, _, _, s)                                -> f ac s
	| Obj pes                                                 -> List.fold_left (fun ac (_, _, e) -> f ac e) ac pes
	| Array es                                                -> List.fold_left fo ac es
	(* statement *) 
	| Label (_, s)                              -> f ac s  
	| If (e, s1, s2)                            -> fo (f (f ac e) s1) s2
	| While (e, s)                              -> f (f ac e) s
	| DoWhile (s, e) 		                        -> f (f ac s) e
	| Skip | Break _ |	Continue _ | Debugger 	-> ac 
	| Throw e                                   -> f ac e
	| Return e                                  -> fo ac e 
	| Script (_, ss) | Block ss                 -> List.fold_left f ac ss
 	| VarDec ves                                -> List.fold_left (fun ac ve -> match ve with (v, None) -> ac | (v, Some e)  -> f ac e) ac ves
	| For(e1, e2, e3, s)                        -> f (fo (fo (fo ac e1) e2) e3) s
	| ForIn (e1, e2, s)                         -> f (f (f ac e1) e2) s
	| Try (s1, Some (_, s2), s3)                -> fo (f (f ac s1) s2) s3
	| Try (s1, None, s2)                        -> fo (f ac s1) s2
	| Switch (e, cases)                         -> analyse_cases (f ac e) cases  
	| Function (_, _, _, s)                     -> f ac s
	(* Non-supported constructs *)
	| RegExp _ | With (_, _)                    -> raise (Failure "JS Construct Not Supported") 


let rec js_accumulator_bottom_up f_combine f_node e = 
	let f = js_accumulator_bottom_up f_combine f_node in 
	let fo e = match e with | Some e -> [ f e ] | None -> [] in 
	let e_stx = e.exp_stx in 
	let ac, recurse = f_node e_stx in 
	if (not recurse) then ac else (
	match e_stx with 
	(* expressions *)
	|	Num _	| String _	|	Null	| Bool _	| Var _	| This      -> ac
  | Delete e | Unary_op (_, e) | Access (e, _)              -> f_combine [ (f e) ] e_stx  
	| Comma (e1, e2) | BinOp (e1, _, e2) | Assign (e1, e2) 
			| AssignOp(e1, _, e2) | CAccess (e1, e2)              -> f_combine [ (f e1); (f e2) ] e_stx
	| ConditionalOp (e1, e2, e3)                              -> f_combine [ (f e1); (f e2); (f e3) ] e_stx
	| Call (e, es) | New (e, es)                              -> f_combine ((f e) :: (List.map f es)) e_stx
  | FunctionExp (_, _, _, s)                                -> f_combine [ (f s) ] e_stx
	| Obj pes                                                 -> f_combine (List.map (fun (_, _, e) -> f e) pes) e_stx
	| Array es                                                -> 
		let lst = List.fold_right (fun v ac -> match v with None -> ac | Some v -> (f v) :: ac) es [] in 
		f_combine lst e_stx
	(* statement *) 
	| Label (_, s)                              -> f_combine [ f s ] e_stx  
	| If (e, s1, s2)                            -> f_combine ([ f e; f s1 ] @ (fo s2)) e_stx
	| While (e, s)                              -> f_combine [ f e; f s ] e_stx
	| DoWhile (s, e) 		                        -> f_combine [ f s; f e ] e_stx
	| Skip | Break _ |	Continue _ | Debugger 	-> ac 
	| Throw e                                   -> f_combine [ f e ] e_stx
	| Return e                                  -> f_combine (fo e) e_stx
	| Script (_, ss) | Block ss                 -> f_combine (List.map f ss) e_stx 
 	| VarDec ves                                -> 
		let lst = List.fold_right (fun ve ac -> match ve with (v, None) -> ac | (_, Some e)  -> (f e) :: ac) ves [] in 
		f_combine lst e_stx  
	| For(e1, e2, e3, s)                        -> f_combine ((fo e1) @ (fo e2) @ (fo e3) @ [ f s ]) e_stx 
	| ForIn (e1, e2, s)                         -> f_combine [ (f e1); (f e2); (f s) ] e_stx
	| Try (s1, Some (_, s2), s3)                -> f_combine ([ (f s1); (f s2) ] @ (fo s3)) e_stx
	| Try (s1, None, s2)                        -> f_combine ((f s1) :: (fo s2)) e_stx 
	| Switch (e, cases)                         -> 
		let lst = List.fold_right 
			(fun (e_case, s_case) ac ->	
				match e_case with 
				| Case e -> (f e) :: (f s_case) :: ac 
				| DefaultCase -> (f s_case) :: ac)
			cases [] in 
		f_combine ((f e) :: lst) e_stx  
	| Function (_, _, _, s)                     -> f_combine [ (f s) ] e_stx 
	(* Non-supported constructs *)
	| RegExp _ | With (_, _)                    -> raise (Failure "JS Construct Not Supported"))




