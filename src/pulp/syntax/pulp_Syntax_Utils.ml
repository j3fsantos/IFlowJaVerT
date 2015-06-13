open Parser_syntax
open Utils
open Batteries
 
exception No_Codename
exception PulpInvalid of string

let named_function_decl fid = 
  fid^"_decl"
  
let update_annotation annots atype new_value =
  let old_removed = List.filter (fun annot -> annot.annot_type <> atype) annots in
  let annot = {annot_type = atype; annot_formula = new_value} in
  annot :: old_removed
 
let get_codename exp =
  let codenames = List.filter (fun annot -> annot.annot_type = Codename) exp.exp_annot in
  match codenames with
    | [codename] -> codename.annot_formula
    | _ -> raise No_Codename 

let main_fun_id : Pulp_Procedure.function_id = "main"

let fresh_name =
  let counter = ref 0 in
  let rec f name =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f
  
let fresh_anonymous () : string =
  fresh_name "anonymous"
  
let fresh_named n : string =
  fresh_name n 
  
let map_switch f (e1, e2s) =
    (f e1) @ flat_map (fun (e2, e3) ->
      (match e2 with
        | Case e2 -> f e2
        | DefaultCase -> []) @ (f e3)
     ) e2s

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
  | VarDec vars -> flat_map (fun ve -> match ve with (v, None) -> [v] | (v, Some e)  -> v :: (f e)) vars 
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
  | AnnonymousFun (_,vs, e)
  | NamedFun (_,_, vs, e) -> []
  | Obj xs -> flat_map (fun (_,_,e) -> f e) xs 
  | Array es -> flat_map (fun e -> match e with None -> [] | Some e -> f e) es
  | Try (_, None, None) -> raise CannotHappen
  | Switch (e1, e2s) -> map_switch f (e1, e2s)
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

let make_env env e args fid =
  let f_decls = func_decls_in_exp e in
  let fnames = List.map (fun f ->
    match f.Parser_syntax.exp_stx with
      | Parser_syntax.NamedFun (s, name, args, body) -> name
      | _ -> raise (PulpInvalid ("Must be function declaration " ^ (Pretty_print.string_of_exp true f)))
  ) f_decls in
  let vars = args @ (var_decls e) @ fnames in
  [Pulp_Procedure.make_ctx_vars fid vars] @ env
  
 
let rec add_codenames main exp  : exp =
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
      | AnnonymousFun (str, args, fb) -> {exp with exp_stx = AnnonymousFun (str, args, f fb); exp_annot = add_codename exp (fresh_anonymous ())}
      | NamedFun (str, name, args, fb) -> {exp with exp_stx = NamedFun (str, name, args, f fb); exp_annot = add_codename exp (fresh_named name)}
      | Obj xs -> m exp (Obj (List.map (fun (pn, pt, e) -> (pn, pt, f e)) xs))
      | Array es -> m exp (Array (List.map fo es))
      | ConditionalOp (e1, e2, e3)  -> m exp (ConditionalOp (f e1, f e2, f e3))
      | ForIn (e1, e2, e3) -> m exp (ForIn (f e1, f e2, f e3))
      | Return e -> m exp (Return (fo e)) 
      | VarDec vars -> m exp (VarDec (List.map (fun (n, e) -> (n, fo e)) vars))
      | Try (e1, catch, finally) -> m exp (Try (f e1,  
        (match catch with 
          | None -> None
          | Some (n, e) -> Some (n, f e)), (fo finally)))
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

let rec make_result e fb args env named frec =
	let fid = (get_codename e) in
	let new_env = make_env env fb args fid in
	let new_env, named_bool = 
	  begin match named with
	    | None -> new_env, None
	    | Some name -> [Pulp_Procedure.make_ctx_vars (named_function_decl fid) [name]] @ new_env, (Some name)
	  end in
	(e, named_bool, new_env) :: (get_all_functions_with_env_in_fb new_env fb "")    
and 
get_all_functions_with_env_in_exp env e =
  (*Printf.printf "get_all_functions_with_env_in_expr %s\n" (Pretty_print.string_of_exp true e);*)
  let f = get_all_functions_with_env_in_exp env in 
  let fo e =
    begin match e with
      | None -> []
      | Some e -> f e
    end
  in
  match e.exp_stx with
    (* Literals *)
    | Null 
    | Bool _
    | String _  
    | Num _      
    | This        
    | Var _ -> []      
    | Obj xs -> flat_map (fun (_, _, e) -> f e) xs       
    | Access (e, v) -> f e        
    | CAccess (e1, e2) -> (f e1) @ (f e2)           
    | New (e1, e2s)
    | Call (e1, e2s) -> f e1 @ (flat_map f e2s)          
    | AnnonymousFun (_, args, fb) -> make_result e fb args env None get_all_functions_with_env_in_fb  
    | NamedFun (_, name, args, fb) -> make_result e fb args env (Some name) get_all_functions_with_env_in_fb       
    | Unary_op (_, e) -> f e        
    | Delete e -> f e
    | BinOp (e1, _, e2) -> (f e1) @ (f e2)         
    | Assign (e1, e2) ->  (f e1) @ (f e2)  
    | Array es -> flat_map fo es
    | ConditionalOp (e1, e2, e3) -> (f e1) @ (f e2) @ (f e3)
    | AssignOp (e1, _, e2) -> (f e1) @ (f e2) 
    | Comma (e1, e2) -> (f e1) @ (f e2)           
    | RegExp _ -> []

      (*Statements*)
      | Parser_syntax.Block _
      | Parser_syntax.Script _ 
      | Parser_syntax.VarDec _
      | Parser_syntax.Skip
      | Parser_syntax.If _
      | Parser_syntax.While _
      | Parser_syntax.Return _
      | Parser_syntax.DoWhile _
      | Parser_syntax.For _
      | Parser_syntax.ForIn _
      | Parser_syntax.Continue _
      | Parser_syntax.Break _
      | Parser_syntax.With _
      | Parser_syntax.Switch _  
      | Parser_syntax.Label _
      | Parser_syntax.Throw _
      | Parser_syntax.Try _    
      | Parser_syntax.Debugger -> raise (PulpInvalid ("Expected expression. Actual " ^ (Pretty_print.string_of_exp true e)))
and
get_all_functions_with_env_in_stmt env e =
  (*Printf.printf "get_all_functions_with_env_in_stmt %s\n" (Pretty_print.string_of_exp true e);*)
  let f = get_all_functions_with_env_in_stmt env in 
  let fe = get_all_functions_with_env_in_exp env in 
  let fo e =
    begin match e with
      | None -> []
      | Some e -> f e
    end
  in
  let feo e =
    begin match e with
      | None -> []
      | Some e -> fe e
    end
  in
  match e.Parser_syntax.exp_stx with
        (* Literals *)
      | Null 
      | Bool _
      | String _  
      | Num _
      
      (* Expressions *) 
      | This
      | Var _  
      | Obj _ 
      | Access _
      | CAccess _
      | New _
      | Call _
      | Unary_op _ 
      | Delete _ 
      | BinOp _ 
      | Assign _  
      | Array _
      | ConditionalOp _
      | AssignOp _
      | Comma _ 
      | RegExp _  -> fe e

      | AnnonymousFun _
      | NamedFun _ -> raise (PulpInvalid ("Expected statement. Actual " ^ (Pretty_print.string_of_exp true e)))
         (* If a function appears in the middle of a statement, it shall not be interpreted as an expression function, but as a function declaration *)
         (* NOTE in spec p.86 *)
         (* ... It is recommended that ECMAScript implementations either disallow this usage of FunctionDeclaration or issue a warning *)

      (*Statements*)
      | Script _ -> raise (PulpInvalid ("Expected Statememnt. Got Script"))
      | Block es -> flat_map f es
      | VarDec vars -> flat_map (fun (_, e) -> feo e) vars
      | Skip -> []       
      | If (e1, e2, e3) -> (fe e1) @ (f e2) @ (fo e3)           
      | While (e1, e2) -> (fe e1) @ (f e2)        
      | DoWhile (e1, e2) -> (f e1) @ (fe e2)       
      | Return e -> feo e           
      | Try (e1, Some (id, e2), Some e3) -> (f e1) @ (f e2) @ (f e3)      
      | Try (e1, None, Some e3) -> (f e1) @ (f e3)          
      | Try (e1, Some (id, e2), None) -> (f e1) @ (f e2)       
      | Try _ -> raise (PulpInvalid "Try _ None None")        
      | Throw e -> fe e
      | Continue _ 
      | Break _ -> []
      | Label (_, e) -> f e       
      | For (e1, e2, e3, e4) -> (feo e1) @ (feo e2) @ (feo e3) @ (f e4) 
      | Switch (e1, sces) -> (fe e1) @ flat_map (fun (sc, e2) -> 
        (match sc with
          | DefaultCase -> []
          | Case e -> fe e 
        @ (f e2))) sces       
      | ForIn (e1, e2, e3) -> (fe e1) @ (fe e2) @ (f e3)
      | With (e1, e2) -> (fe e1) @ (f e2)
      | Debugger -> []
and
get_all_functions_with_env_in_elem env e = 
	(*Printf.printf "get_all_functions_with_env_in_elem %s\n" (Pretty_print.string_of_exp true e);*)
	match e.Parser_syntax.exp_stx with
	  | Parser_syntax.NamedFun (s, name, args, fb) -> 
	    make_result e fb args env None get_all_functions_with_env_in_fb
	  | _ ->  get_all_functions_with_env_in_stmt env e
and
get_all_functions_with_env_in_fb env e main : (exp * string option * Pulp_Procedure.ctx_variables list) list =
  (* (expression, if it's named expr, environment *)
  (*Printf.printf "get_all_functions_with_env_in_fb %s\n" (Pretty_print.string_of_exp true e); *)
  match e.Parser_syntax.exp_stx with
    | Parser_syntax.Script (_, es) ->
      let new_env = make_env env e [] main in
        (e, None, new_env) :: (flat_map (get_all_functions_with_env_in_elem new_env) es)
    | Parser_syntax.Block (es) -> Utils.flat_map (get_all_functions_with_env_in_elem env) es
    | _ -> get_all_functions_with_env_in_elem env e