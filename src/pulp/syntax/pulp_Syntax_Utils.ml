open Parser_syntax
open Utils
open Batteries
 
exception No_Codename
exception PulpInvalid of string
  
let update_annotation annots atype new_value =
  let old_removed = List.filter (fun annot -> annot.annot_type <> atype) annots in
  let annot = {annot_type = atype; annot_formula = new_value} in
  annot :: old_removed
 
let get_codename exp =
  let codenames = List.filter (fun annot -> annot.annot_type = Codename) exp.exp_annot in
  match codenames with
    | [codename] -> codename.annot_formula
    | _ -> raise No_Codename 

let main_fun_id : Pulp_Syntax.function_id = "main"

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
  [Pulp_Syntax.make_ctx_vars fid vars] @ env
  
 
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
  

let rec get_all_functions_with_env env e : (exp * Pulp_Syntax.ctx_variables list) list =
  let f = get_all_functions_with_env env in 
  let fo e =
    begin match e with
      | None -> []
      | Some e -> f e
    end
  in
  let make_result e fb args env =
    let new_env = make_env env fb args (get_codename e) in
    (e, new_env) :: (get_all_functions_with_env new_env fb) in
  begin match e.exp_stx with
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
      | Debugger -> [] 
      | Delete e 
      | Access (e, _) 
      | Unary_op (_, e) 
      | Throw e
      | Label (_, e) -> f e
      | BinOp (e1, _, e2)
      | Assign (e1, e2)  
      | AssignOp (e1, _, e2) 
      | CAccess (e1, e2) 
      | Comma (e1, e2) 
      | While (e1, e2)
      | DoWhile (e1, e2)
      | With (e1, e2) -> (f e1) @ (f e2)
      | Call (e1, e2s)
      | New (e1, e2s) -> f e1 @ (flat_map f e2s)
      | AnnonymousFun (_, args, fb) -> make_result e fb args env
      | NamedFun (_, name, args, fb) -> make_result e fb args env
      | Obj xs -> flat_map (fun (_, _, e) -> f e) xs
      | Array es -> flat_map fo es
      | ConditionalOp (e1, e2, e3) 
      | ForIn (e1, e2, e3) -> (f e1) @ (f e2) @ (f e3)
      | Return e -> fo e 
      | VarDec vars -> flat_map (fun (_, e) -> fo e) vars
      | Try (e1, catch, finally) -> (f e1) @ 
        (match catch with 
          | None -> []
          | Some (_, e) -> f e) @ (fo finally)
      | If (e1, e2, e3) -> (f e1) @ (f e2) @ (fo e3)
      | For (e1, e2, e3, e4) -> (fo e1) @ (fo e2) @ (fo e3) @ (f e4)
      | Switch (e1, sces) -> (f e1) @ flat_map (fun (sc, e2) -> 
        (match sc with
          | DefaultCase -> []
          | Case e -> f e 
        @ (f e2))) sces
      | Block es -> flat_map f es
      | Script (_, es) -> let new_env = make_env env e ["undefined"] main_fun_id in
        (e, new_env) :: (flat_map (get_all_functions_with_env new_env) es)
   end