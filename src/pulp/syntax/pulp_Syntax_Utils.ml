open Parser_syntax
open Utils

let rec get_all_functions e : exp list =
  let f = get_all_functions in 
  let fo e =
    begin match e with
      | None -> []
      | Some e -> f e
    end
  in
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
      | AnnonymousFun (_, _, fb)
      | NamedFun (_, _, _, fb) -> e :: (f fb)
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
      | Block es 
      | Script (_, es) -> flat_map f es
   end