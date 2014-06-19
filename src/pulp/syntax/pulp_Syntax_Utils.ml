open Parser_syntax
open Utils
open Batteries

exception No_Codename
  
let update_annotation annots atype new_value =
  let old_removed = List.filter (fun annot -> annot.annot_type <> atype) annots in
  let annot = {annot_type = atype; annot_formula = new_value} in
  annot :: old_removed
 
let get_codename exp =
  let codenames = List.filter (fun annot -> annot.annot_type = Codename) exp.exp_annot in
  match codenames with
    | [codename] -> codename.annot_formula
    | _ -> raise No_Codename


type function_id = string 

let main_fun_id : function_id = "main"

let fresh_name =
  let counter = ref 0 in
  let rec f name =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f
  
let fresh_annonymous () : string =
  fresh_name "annonymous"
  
let fresh_named n : string =
  fresh_name n 
  
type ctx_variables = {
     func_id : function_id;
     fun_bindings : Pulp_Syntax.variable list
  }
  
let make_ctx_vars fid vars = 
  { 
    func_id = fid;
    fun_bindings = vars
  }

type fun_with_ctx = {
     ctx_vars : ctx_variables list;
     fun_block : Pulp_Syntax.function_block;
  }
  
let make_fun_with_ctx vars f =
  {
    ctx_vars = vars;
    fun_block = f
  }

module AllFunctions = Map.Make ( 
  struct 
    type t = function_id
    let compare = compare
  end
)
  
let map_switch f (e1, e2s) =
    (f e1) @ flat_map (fun (e2, e3) ->
      (match e2 with
        | Case e2 -> f e2
        | DefaultCase -> []) @ (f e3)
     ) e2s

let rec var_decls_inner exp = 
  let f = var_decls_inner in match exp.exp_stx with
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
  | For (e1, e2, e3, e4) -> (f e1) @ (f e2) @ (f e3) @ (f e4)
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

let make_env env e args fid =
  let vars = args @ (var_decls e) in
  [make_ctx_vars fid vars] @ env
  


let rec get_all_functions_with_env env e : (function_id * exp * ctx_variables list) list =
  let f = get_all_functions_with_env env in 
  let fo e =
    begin match e with
      | None -> []
      | Some e -> f e
    end
  in
  let make_result fid e fb args env =
    let new_env = make_env env fb args fid in
    (* I use codename for now. It may be that I want a new annotation for function identifier. *)
    let new_annots = update_annotation e.exp_annot Codename fid in
    (fid, {e with exp_annot = new_annots}, new_env) :: (get_all_functions_with_env new_env fb) in
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
      | AnnonymousFun (_, args, fb) -> make_result (fresh_annonymous ()) e fb args env
      | NamedFun (_, name, args, fb) -> make_result (fresh_named name) e fb args env
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
      | For (e1, e2, e3, e4) -> (f e1) @ (f e2) @ (f e3) @ (f e4)
      | Switch (e1, sces) -> (f e1) @ flat_map (fun (sc, e2) -> 
        (match sc with
          | DefaultCase -> []
          | Case e -> f e 
        @ (f e2))) sces
      | Block es -> flat_map f es
      | Script (_, es) -> let new_env = make_env env e [] main_fun_id in
        (main_fun_id, e, new_env) :: (flat_map (get_all_functions_with_env new_env) es) 
   end