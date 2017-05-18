open Parser_syntax
open Utils
open Batteries


(********************************************)
(********************************************)
(***       JS AST transformers            ***)
(********************************************)
(********************************************)

let flat_map f l = List.flatten (List.map f l)

let rec js_accumulator_top_down f_ac f_state state expr = 
  let new_state = f_state expr state in 
  let f         = js_accumulator_top_down f_ac f_state new_state in 
  let f_ac      = f_ac expr new_state state in 
  let fo e = match e with | Some e -> f e | None -> [] in

  let analyse_cases cases = 
    flat_map  
      (fun (e_case, s_case) -> 
          let f_e_case = 
            (match e_case with 
            | Case e -> f e 
            | DefaultCase -> []) in 
          let f_s_case = f s_case in 
          f_e_case @ f_s_case) cases in 
  
  let e_stx = expr.exp_stx in 
  match e_stx with 
  (* expressions *)
  | Num _ | String _  | Null  | Bool _  | Var _ | This      -> f_ac [ ] 
  | Delete e | Unary_op (_, e) | Access (e, _)              -> f_ac (f e)     
  | Comma (e1, e2) | BinOp (e1, _, e2) | Assign (e1, e2) 
  | AssignOp(e1, _, e2) | CAccess (e1, e2)                  -> f_ac ((f e1) @ (f e2)) 
  | ConditionalOp (e1, e2, e3)                              -> f_ac ((f e1) @ (f e2) @ (f e3)) 
  | Call (e, es) | New (e, es)                              -> f_ac (flat_map f (e :: es))    
  | FunctionExp (_, _, _, s)                                -> f_ac (f s)
  | Obj pes                                                 -> f_ac (flat_map (fun (_, _, e) -> f e) pes)
  | Array es                                                -> f_ac (flat_map fo es)
  (* statement *) 
  | Label (_, s)                              -> f_ac (f s)  
  | If (e, s1, s2)                            -> f_ac ((f e) @ (f s1) @ (fo s2))
  | While (e, s)                              -> f_ac ((f e) @ (f s))
  | DoWhile (s, e)                            -> f_ac ((f s) @ (f e)) 
  | Skip | Break _ |  Continue _ | Debugger   -> f_ac [] 
  | Throw e                                   -> f_ac (f e)
  | Return e                                  -> f_ac (fo e) 
  | Script (_, ss) | Block ss                 -> f_ac (flat_map f ss)
  | VarDec ves                                -> f_ac (flat_map (fun ve -> match ve with (v, None) -> [] | (v, Some e)  -> f e) ves)
  | For(e1, e2, e3, s)                        -> f_ac ((fo e1) @ (fo e2) @ (fo e3) @ (f s)) 
  | ForIn (e1, e2, s)                         -> f_ac ((f e1) @ (f e2) @ (f s)) 
  | Try (s1, Some (_, s2), s3)                -> f_ac ((f s1) @ (f s2) @ (fo s3)) 
  | Try (s1, None, s2)                        -> f_ac ((f s1) @ (fo s2))
  | Switch (e, cases)                         -> f_ac ((f e) @ (analyse_cases cases))
  | Function (_, _, _, s)                     -> f_ac (f s)
  (* Non-supported constructs *)
  | RegExp _ | With (_, _)                    -> raise (Failure "JS Construct Not Supported") 



let rec js_mapper f_m expr = 
  let f = js_mapper f_m in 
  let fo = Option.map f in 
  let f_switch = fun (sc, e2) -> (match sc with | Case e1 -> Case (f e1)| DefaultCase -> DefaultCase), f e2 in 

  let e_stx = expr.exp_stx in 
  let new_e_stx = 
    match e_stx with 
    (* expressions *)
    | Num _ | String _  | Null  | Bool _  | Var _ | This      -> e_stx
    | Delete e                    -> Delete (f e)
    | Unary_op (op, e)            -> Unary_op (op, f e)
    | Access (e, x)               -> Access (f e, x) 
    | Comma (e1, e2)              -> Comma (f e1, f e2)
    | BinOp (e1, op, e2)          -> BinOp (f e1, op, f e2) 
    | Assign (e1, e2)             -> Assign (f e1, f e2)
    | AssignOp(e1, op, e2)        -> AssignOp(f e1, op, f e2)
    | CAccess (e1, e2)            -> CAccess (f e1, f e2)   
    | ConditionalOp (e1, e2, e3)  -> ConditionalOp (f e1, f e2, f e3)                           
    | Call (e, es)                -> Call (f e, List.map f es)    
    | New (e, es)                 -> New (f e, List.map f es)                       
    | FunctionExp (x, n, vs, e)   -> FunctionExp (x, n, vs, f e)
    | Obj lppe                    -> Obj (List.map (fun (pp, pt, e) -> (pp, pt, f e)) lppe)
    | Array leo                   -> Array (List.map fo leo)     
    (* statement *) 
    | Label (lab, s)              -> Label (lab, f s)  
    | If (e, s1, s2)              -> If (e, f s1, fo s2)
    | While (e, s)                -> While (e, f s)
    | DoWhile (s, e)              -> DoWhile (e, f s) 
    | Skip | Break _ |  Continue _ | Debugger   -> e_stx
    | Throw e                     -> Throw (f e)
    | Return eo                   -> Return (fo eo) 
    | Script (b, le)              -> Script (b, List.map f le) 
    | Block le                    -> Block (List.map f le)
    | VarDec lveo                 -> VarDec (List.map (fun (v, eo) -> (v, fo eo)) lveo)
    | For (eo1, eo2, eo3, e)      -> For (fo eo1, fo eo2, fo eo3, f e) 
    | ForIn (e1, e2, e3)          -> ForIn (f e1, f e2, f e3) 
    | Try (e, seo1, eo2)          -> Try (f e, Option.map (fun (s, e) -> (s, f e)) seo1, fo eo2) 
    | Switch (e, les)             -> Switch (f e, List.map f_switch les)
    | Function (b, os, lv, s)     -> Function (b, os, lv, f s)
    (* Non-supported constructs *)
    | RegExp _ | With (_, _)      -> raise (Failure "JS Construct Not Supported") in 

  let new_e = { expr with exp_stx = new_e_stx } in 
  f_m new_e  



(********************************************)
(********************************************)
(***         JavaScript Utils             ***)
(********************************************)
(********************************************)


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


let rec var_decls_inner exp =
  let f_ac exp state prev_state ac = 
    match exp.exp_stx with 
    | VarDec vars -> (List.map (fun (v, _) -> v) vars) @ ac 
    | _ -> ac in 
  js_accumulator_top_down f_ac (fun x y -> y) true exp


let var_decls exp = (List.unique (var_decls_inner exp))


let rec get_fun_decls exp =
  let f_ac exp state prev_state ac = 
    match exp.exp_stx with 
    | Function (_, _, _, _) -> exp :: ac 
    | _ -> ac in 
  js_accumulator_top_down f_ac (fun x y -> y) true exp


let rec get_fun_exprs_expr exp =
  let f_ac exp state prev_state ac = 
    match exp.exp_stx with 
    | Function _  | FunctionExp _ -> exp :: ac 
    | _ -> ac in 
  js_accumulator_top_down f_ac (fun x y -> y) true exp


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
  let vars = List.concat [ f_args; (var_decls f_body); fnames] in
  vars



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
  | Null | Num _ | String _ | Bool _ | Var _ | Delete _ | Unary_op _ | BinOp _ | Access _ 
    | New _ | CAccess _ | Assign _ | AssignOp _ | Comma _ | ConditionalOp _ | Obj _ | Array _ 
    | RegExp _ | FunctionExp _ | Function _ | Call _ | This | Throw _ | Return _ | Debugger -> false

  | Label (_, e) | DoWhile (e, _) -> returns_empty_exp e

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

  | Block el | Script (_, el) -> returns_empty_exp_list el
  | Switch (_, ese) -> let (_, el) = List.split ese in returns_empty_exp_list el

  | For _ | ForIn _ | While _ | VarDec _ | Break _ | Continue _ | Skip -> true
  | _ -> raise (Failure "unsupported construct by Petar M.")


