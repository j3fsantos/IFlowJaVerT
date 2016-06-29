open Parser_syntax
open Utils
open Batteries

exception CannotHappen
exception No_Codename

let sanitise name = 
	let s = Str.global_replace (Str.regexp "\$") "_" name in
	s

let eval_prefix = "___$eval___" 

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

let fresh_name =
  let counter = ref 0 in
  let rec f name =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f
  
let fresh_anonymous () : string =
  fresh_name "anonymous"

let fresh_catch_anonymous () : string =
  fresh_name "catch_anonymous"	
		  
let fresh_named n : string =
  fresh_name n 

let fresh_eval_name () : string = 
	fresh_name eval_prefix

let flat_map f l = List.flatten (List.map f l)

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
  | AnonymousFun (_,vs, e)
  | NamedFun (_,_, vs, e) -> []
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

let var_decls exp = List.unique (var_decls_inner exp)


let func_decls_in_elem exp : exp list = 
    match exp.Parser_syntax.exp_stx with
      | Parser_syntax.NamedFun (s, name, args, body) -> [exp]
      | _ ->  []

let rec func_decls_in_exp exp : exp list =
  match exp.Parser_syntax.exp_stx with
    | Parser_syntax.Script (_, es) 
    | Parser_syntax.Block (es) -> List.flatten (List.map (func_decls_in_elem) es)
    | _ -> func_decls_in_elem exp  


let get_all_vars_f f_body f_args =
  let f_decls = func_decls_in_exp f_body in
  let fnames = List.map (fun f ->
    match f.Parser_syntax.exp_stx with
      | Parser_syntax.NamedFun (s, name, args, body) -> name
      | _ -> raise (Failure ("Must be function declaration " ^ (Pretty_print.string_of_exp true f)))
  ) f_decls in
  let vars = List.concat [f_args; (var_decls f_body); fnames] in
	vars
  
 
let rec add_codenames main exp : exp =
  let f = add_codenames main in
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
      | AnonymousFun (str, args, fb) -> {exp with exp_stx = AnonymousFun (str, args, f fb); exp_annot = add_codename exp (fresh_anonymous ())}
      | NamedFun (str, name, args, fb) -> {exp with exp_stx = NamedFun (str, name, args, f fb); exp_annot = add_codename exp (fresh_named (sanitise name))}
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


let update_fun_tbl fun_tbl f_id f_args f_body = 
	if (Hashtbl.mem fun_tbl f_id) 
		then 
			let msg = Printf.sprintf "fun tbl already has the function %s" f_id in 
			raise (Failure msg)
		else 
			Hashtbl.add fun_tbl f_id (f_id, f_args, f_body) 

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

let update_cc_tbl_catch cc_tbl f_parent_id f_id  x = 
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

let rec closure_clarification cc_tbl fun_tbl vis_tbl f_id visited_funs e = 
	let f = closure_clarification cc_tbl fun_tbl vis_tbl f_id visited_funs in 
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
  | AnonymousFun (_, args, fb) 
	| NamedFun (_, _, args, fb) -> 
		let new_f_id = get_codename e in 
		update_cc_tbl cc_tbl f_id new_f_id args fb;
		update_fun_tbl fun_tbl new_f_id args fb; 
		Hashtbl.replace vis_tbl new_f_id (new_f_id :: visited_funs); 
		closure_clarification cc_tbl fun_tbl vis_tbl new_f_id (new_f_id :: visited_funs) fb
	| Unary_op (_, e) -> f e        
  | Delete e -> f e
  | BinOp (e1, _, e2) -> 
		f e1; f e2         
  | Assign (e1, e2) ->  
		f e1; f e2  
  | Array es -> List.iter fo es
  | ConditionalOp (e1, e2, e3) -> 
		f e1; f e2; f e3
  | AssignOp (e1, _, e2) -> 
		f e1; f e2 
  | Comma (e1, e2) ->
		f e1; f e2           
  | RegExp _ -> ()
	(*Statements*)
  | Script (_, es) -> List.iter f es 
  | Block es -> List.iter f es
  | VarDec vars -> List.iter (fun (_, e) -> fo e) vars
  | Skip -> ()       
  | If (e1, e2, e3) -> f e1; f e2; fo e3          
  | While (e1, e2) -> f e1; f e2        
  | DoWhile (e1, e2) -> f e1; f e2       
  | Return e -> fo e 
  | Try (e1, Some (x, e2), e3) ->
		f e1; fo e3; 
		let new_f_id = get_codename e in 
		update_cc_tbl_catch cc_tbl f_id new_f_id x;
		closure_clarification cc_tbl fun_tbl vis_tbl new_f_id (new_f_id :: visited_funs) e2      
  | Try (e1, None, e3) -> f e1; fo e3          
  | Throw e -> f e
  | Continue _ 
  | Break _ -> ()
  | Label (_, e) -> f e       
  | For (e1, e2, e3, e4) -> fo e1; fo e2; fo e3; f e4
  | Switch (e1, sces) -> 
		f e1; 
		List.iter 
			(fun (sc, ec2) ->
				(match sc with 
				| DefaultCase -> () 
				| Case ec1 -> f ec1); 
				f ec2)
			sces
	| ForIn (e1, e2, e3) -> f e1; f e2; f e3 
	| With (e1, e2) -> f e1; f e2 
	| Debugger -> ()  
	
let closure_clarification_top_level main e =
	let cc_tbl = Hashtbl.create 101 in 
	let fun_tbl = Hashtbl.create 101 in
	let vis_tbl = Hashtbl.create 101 in  
	
	let main_tbl = Hashtbl.create 101 in 
	let main_vars = get_all_vars_f e [] in
	List.iter
		(fun v -> Hashtbl.replace main_tbl v main)
		main_vars; 
	Hashtbl.add cc_tbl main main_tbl; 
	Hashtbl.add fun_tbl main (main, [], e); 
	Hashtbl.add vis_tbl main [];
	closure_clarification cc_tbl fun_tbl vis_tbl main [ main ] e; 
	cc_tbl, fun_tbl, vis_tbl

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
  | AnonymousFun (_, _, _) 
  | NamedFun (_, _, _, _) 
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