open Parser_syntax
open Utils
open Batteries

exception CannotHappen
exception No_Codename
exception EarlyError of string


let sanitise name = 
	let s = Str.global_replace (Str.regexp "\$") "_" name in
	s

let update_annotation annots atype new_value =
  let old_removed = List.filter (fun annot -> annot.annot_type <> atype) annots in
  let annot = {annot_type = atype; annot_formula = new_value} in
	(* Printf.printf "I am adding the code name: %s"  new_value; *)
  annot :: old_removed

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
    | This
    | Var _
    | Num _
    | String _
    | Null
    | Bool _
    | RegExp _
    | Obj _
    | Array _
    | Unary_op _
    | BinOp _
    | Delete _
    | Assign _
    | AssignOp _
    | Comma _
    | Access _
    | CAccess _
    | ConditionalOp _
    | Call _
    | New _
    (* Statements *)
    | VarDec _
    | Skip
    | Continue _
    | Break _
    | Return _
    | Throw _
    | Debugger -> false

    (* with is a syntax error in strict mode *)
    (* TODO: Move to a more appropriate pre-processing mapper function so we can get better errors *)
    | With _ -> true

    (* Statements with sub-Statements *)
    | Block es -> List.exists (f true) es
    | If (_, s, so) -> f true s || fo (f true) so
    | While (_, s)
    | DoWhile (s, _)
    | For (_, _, _, s)
    | ForIn (_, _, s)
    | Label (_, s) -> f true s
    | Switch (_, cs) -> List.exists (fun (_, s) -> f true s) cs
    | Try (s, sc, so) -> f true s || fo (fun (_, s) -> f true s) sc || fo (f true) so

    (* TODO: Ideally now the parser identifies these correctly, this test can be amended *)
    | FunctionExp _
    | Function _ -> in_block
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
    | Num _
    | String _
    | Null
    | Bool _
    | RegExp _
    | This
    | Skip
    | Break _
    | Continue _
    | Debugger -> []
    | Throw e
    | Access (e, _)
    | Label (_, e) -> f false e
    | Return eo -> fo false eo
    | While (e1, e2)
    | DoWhile (e1, e2)
    | BinOp (e1, _, e2)
    | CAccess (e1, e2)
    | Comma (e1, e2)
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
		flat_map (fun ve -> match ve with (v, None) -> [v] | (v, Some e)  -> v :: (f e)) vars 
  | Throw e
  | Delete e
  | Return (Some e) 
  | Access (e, _) 
  | Unary_op (_, e) 
  | Label (_, e) -> f e
  | While (e1, e2) 
  | DoWhile (e1, e2)
  | BinOp (e1, _, e2)
  | Assign (e1, e2)  
  | AssignOp (e1, _, e2) 
  | CAccess (e1, e2) 
  | Comma (e1, e2) 
  | With (e1, e2) 
  | Try (e1, Some (_, e2), None)
  | Try (e1, None, Some e2)
  | If (e1, e2, None)-> (f e1) @ (f e2)
  | If (e1, e2, Some e3) 
  | ForIn (e1, e2, e3) 
  | Try (e1, Some (_, e2), Some e3) 
  | ConditionalOp (e1, e2, e3)-> (f e1) @ (f e2) @ (f e3)
  | For (e1, e2, e3, e4) -> 
    (fo e1) @ (fo e2) @ (fo e3) @ (f e4)
  | Call (e1, e2s) 
  | New (e1, e2s) -> (f e1) @ (flat_map (fun e2 -> f e2) e2s)
  | FunctionExp _
  | Function _ -> []
  | Obj xs -> flat_map (fun (_,_,e) -> f e) xs 
  | Array es -> flat_map (fun e -> match e with None -> [] | Some e -> f e) es
  | Try (_, None, None) -> raise CannotHappen
  | Switch (e1, e2s) -> 
		(f e1) @ (flat_map (fun (e2, e3) ->
      (match e2 with
        | Case e2 -> f e2
        | DefaultCase -> []) @ (f e3)
     ) e2s)
  | Block es
  | Script (_, es) -> flat_map f es

let var_decls exp = List.append (List.unique (var_decls_inner exp)) [ "arguments" ]


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

 
let rec add_codenames main fresh_anonymous fresh_named fresh_catch_anonymous exp =
  let f = add_codenames main fresh_anonymous fresh_named fresh_catch_anonymous in
  let fo e =
    begin match e with
      | None -> None
      | Some e -> Some (f e)
    end in
  let m exp nstx = {exp with exp_stx = nstx} in
  (* I use codename for now. It may be that I want a new annotation for function identifier. *)
  let add_codename exp fid = update_annotation exp.exp_annot Codename fid
  in
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
      | FunctionExp (str, name, args, fb) -> {exp with exp_stx = FunctionExp (str, name, args, f fb); exp_annot = add_codename exp (fresh_anonymous ())}
      | Function (str, Some name, args, fb) -> {exp with exp_stx = Function (str, Some name, args, f fb); exp_annot = add_codename exp (fresh_named (sanitise name))}
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
        {exp with exp_stx = Script (str, List.map f es); exp_annot = add_codename exp main}


let process_js_logic_annotations fun_name fun_args annotations requires_flag ensures_normal_flag ensure_err_flag = 
	let preconditions  = List.filter (fun annotation -> annotation.annot_type = requires_flag) annotations in 
	let postconditions = List.filter (fun annotation -> (annotation.annot_type = ensures_normal_flag) || (annotation.annot_type = ensure_err_flag)) annotations in 
	let single_specs = List.map2 
		(fun pre post ->
			let pre_str   = pre.annot_formula in 
			let post_str  = post.annot_formula in 
			let ret_flag  = 
				(match post.annot_type with 
				| ensures_normal_flag -> JSIL_Syntax.Normal 
				| ensure_err_flag     -> JSIL_Syntax.Error) in 
			let pre_jsil  = JSIL_Utils.jsil_assertion_of_string pre_str in 
			let post_jsil = JSIL_Utils.jsil_assertion_of_string post_str in 
			let new_spec = JSIL_Syntax.create_single_spec pre_jsil post_jsil ret_flag in 
			new_spec)
		preconditions
		postconditions in  
	let fun_spec = if ((List.length single_specs) > 0) 
		then Some (JSIL_Syntax.create_jsil_spec fun_name fun_args single_specs)
		else None in
	fun_spec

let update_fun_tbl fun_tbl f_id f_args f_body annotations = 
	let fun_spec = process_js_logic_annotations f_id f_args annotations Requires Ensures EnsuresErr in  						
	Hashtbl.replace fun_tbl f_id (f_id, f_args, f_body, fun_spec) 

let update_cc_tbl cc_tbl f_parent_id f_id f_args f_body =
	let f_parent_var_table = 
		try Hashtbl.find cc_tbl f_parent_id 
		with _ ->
			let msg = Printf.sprintf "the parent function of %s -- %s -- was not found in the cc table" f_id f_parent_id in  
			raise (Failure msg) in
	let new_f_tbl = Hashtbl.create 101 in 
	Hashtbl.iter
		(fun x x_f_id -> Hashtbl.add new_f_tbl x x_f_id) 
		f_parent_var_table;
	let f_vars = get_all_vars_f f_body f_args in  
	List.iter
		(fun v -> Hashtbl.replace new_f_tbl v f_id)
		f_vars; 
	Hashtbl.add cc_tbl f_id new_f_tbl 	

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
	Hashtbl.add cc_tbl f_id new_f_tbl

let rec closure_clarification_expr cc_tbl fun_tbl vis_tbl f_id visited_funs e = 
	let f = closure_clarification_expr cc_tbl fun_tbl vis_tbl f_id visited_funs in 
	let fo e = (match e with 
	| None -> () 
	| Some e -> f e) in 
	match e.exp_stx with
  (* Literals *)
	| Null 
	| Bool _
	| String _  
	| Num _      
	(* Expressions *)
	| This        
	| Var _ -> ()      
	| Obj xs -> List.iter (fun (_, _, e) -> f e) xs       
	| Access (e, v) -> f e        
	| CAccess (e1, e2) -> (f e1); (f e2)           
	| New (e1, e2s)
	| Call (e1, e2s) -> f e1; (List.iter f e2s)          
  | FunctionExp (_, f_name, args, fb)
  | Function (_, f_name, args, fb) ->
    begin match f_name with
    | None ->
      let new_f_id = get_codename e in 
      update_cc_tbl cc_tbl f_id new_f_id args fb;
      update_fun_tbl fun_tbl new_f_id args fb; 
      Hashtbl.replace vis_tbl new_f_id (new_f_id :: visited_funs); 
      closure_clarification_stmt cc_tbl fun_tbl vis_tbl new_f_id (new_f_id :: visited_funs) fb
    | Some f_name ->
      let new_f_id = get_codename e in
      let new_f_id_outer = new_f_id ^ "_outer" in
      update_cc_tbl_single_var_er cc_tbl f_id new_f_id_outer f_name;  
      update_cc_tbl cc_tbl new_f_id_outer new_f_id args fb;
      update_fun_tbl fun_tbl new_f_id args fb; 
      Hashtbl.replace vis_tbl new_f_id (new_f_id :: new_f_id_outer :: visited_funs); 
      closure_clarification_stmt cc_tbl fun_tbl vis_tbl new_f_id (new_f_id :: new_f_id_outer :: visited_funs) fb
    end
  | Unary_op (_, e) -> f e        
  | Delete e -> f e
  | BinOp (e1, _, e2) -> f e1; f e2         
  | Assign (e1, e2) -> f e1; f e2  
  | Array es -> List.iter fo es
  | ConditionalOp (e1, e2, e3) -> f e1; f e2; f e3
  | AssignOp (e1, _, e2) -> f e1; f e2 
  | Comma (e1, e2) -> f e1; f e2   
	| VarDec vars -> List.iter (fun (_, e) -> fo e) vars        
  | RegExp _	-> ()
	(*Statements*)
  | Script (_, _) -> raise (Failure "statement in expression context - closure clarification: script") 
  | Block _ -> raise (Failure "statement in expression context - closure clarification: block") 
  | Skip _ -> raise (Failure "statement in expression context - closure clarification: skip") 
  | If (_, _, _) -> raise (Failure "statement in expression context - closure clarification: if")  
  | While (_,_) -> raise (Failure "statement in expression context - closure clarification: while") 
  | DoWhile (_, _) -> raise (Failure "statement in expression context - closure clarification: do-while") 
  | Return _ -> raise (Failure "statement in expression context - closure clarification: return") 
  | Try (_, _, _) -> raise (Failure "statement in expression context - closure clarification: try") 
  | Throw _ -> raise (Failure "statement in expression context - closure clarification: throw") 
  | Continue _ -> raise (Failure "statement in expression context - closure clarification: continue") 
  | Break _ -> raise (Failure "statement in expression context - closure clarification: break") 
  | Label (_, _) -> raise (Failure "statement in expression context - closure clarification: label") 
  | For (_, _, _, _) -> raise (Failure "statement in expression context - closure clarification: for") 
  | Switch (_, _) -> raise (Failure "statement in expression context - closure clarification: switch") 
	| ForIn (_, _, _)  -> raise (Failure "statement in expression context - closure clarification: for-in") 
	| With (_, _) -> raise (Failure "statement in expression context - closure clarification: with") 
	| Debugger -> raise (Failure "statement in expression context - closure clarification: debugger") 
and 
closure_clarification_stmt cc_tbl fun_tbl vis_tbl f_id visited_funs e = 
	let f = closure_clarification_stmt cc_tbl fun_tbl vis_tbl f_id visited_funs in 
	let fe = closure_clarification_expr cc_tbl fun_tbl vis_tbl f_id visited_funs in 
	let fo e = (match e with 
	| None -> () 
	| Some e -> f e) in 
	let feo e = (match e with 
	| None -> () 
	| Some e -> fe e) in 
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
		(* Printf.printf("named function expression hihihi\n");   *)
		let new_f_id = get_codename e in                           
		update_cc_tbl cc_tbl f_id new_f_id args fb;                
		update_fun_tbl fun_tbl new_f_id args fb e.exp_annot;        
		Hashtbl.replace vis_tbl new_f_id (new_f_id :: visited_funs); 
		closure_clarification_stmt cc_tbl fun_tbl vis_tbl new_f_id (new_f_id :: visited_funs) fb
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
		closure_clarification_stmt cc_tbl fun_tbl vis_tbl new_f_id (new_f_id :: visited_funs) e2      
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

let closure_clarification_top_level global_spec cc_tbl fun_tbl vis_tbl proc_id e vis_fid args =
	let proc_tbl = Hashtbl.create 101 in 
	
	let proc_vars = get_all_vars_f e [] in
	List.iter
		(fun v -> Hashtbl.replace proc_tbl v proc_id)
		proc_vars; 
	Hashtbl.add cc_tbl proc_id proc_tbl; 
	Hashtbl.add fun_tbl proc_id (proc_id, args, e, global_spec); 
	Hashtbl.add vis_tbl proc_id vis_fid;
	closure_clarification_stmt cc_tbl fun_tbl vis_tbl proc_id vis_fid e

(**
	(Hashtbl.iter
		(fun f_id f_tbl ->
			(Hashtbl.iter 
				(fun v fun_v ->
					Hashtbl.replace f_tbl v (Printf.sprintf "\"%s\"" fun_v))
				f_tbl)) cc_tbl);
	cc_tbl, fun_tbl
*)	
	
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
