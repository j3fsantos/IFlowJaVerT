open WISL_Utils
open WISL_Syntax

module JSIL = JSIL_Syntax (* Alias to stay concise *)
module LabSet = Set.Make(String)

module LabelGenerator = struct
  let current_seed = ref 0
  
  let get_lab ?(pre="cmd") () =
    let lab = pre ^ (string_of_int (!current_seed)) in
    current_seed := (!current_seed) + 1;
    lab
  end 


(* First we compile expressions *)
let compile_binop b = match b with
  | EQUAL -> BinOp.Equal
  | LESSTHAN -> BinOp.LessThan
	| LESSEQUAL -> BinOp.LessThanEqual
	| PLUS -> BinOp.Plus
	| MINUS -> BinOp.Minus
	| TIMES -> BinOp.Times
	| DIV -> BinOp.Div
	| MOD -> BinOp.Mod
	| AND -> BinOp.And
	| OR -> BinOp.Or
  | _ -> failwith "compile_binop should not be used to compile this operator"

let compile_unop u = match u with
  | NOT -> UnOp.Not

let compile_value v = match v with
  | Bool b -> Literal.Bool b
  | Null -> Literal.Null
  | Loc l -> Literal.Loc l
  | Num n -> Literal.Num (float_of_num n)
  | Str s -> Literal.String s


let rec compile_expression expr =
  let is_special_binop b = match b with
    | NEQ | GREATERTHAN | GREATEREQUAL -> true
    | _ -> false
  in
  let compile_special_binop (e1, b, e2) =
    let comp_e1 = compile_expression e1 in
    let comp_e2 = compile_expression e2 in
    match b with
    | NEQ -> 
        JSIL.UnOp (
          UnOp.Not,
          JSIL.BinOp (comp_e1, BinOp.Equal, comp_e2)
        )
    | GREATERTHAN ->
        JSIL.UnOp (
          UnOp.Not,
          JSIL.BinOp (comp_e1, BinOp.LessThanEqual, comp_e2)
        )
    | GREATEREQUAL ->
        JSIL.UnOp (
          UnOp.Not,
          JSIL.BinOp (comp_e1, BinOp.LessThan, comp_e2)
        )
    | _ -> failwith "This is not a special binary operator"
  in
  match expr with
  | Val v -> JSIL.Literal (compile_value v)
  | Var x -> JSIL.Var x
  | BinOp (e1, b, e2) when is_special_binop b ->
    compile_special_binop (e1, b, e2)
  | BinOp (e1, b, e2) -> JSIL.BinOp (compile_expression e1,
                         compile_binop b, compile_expression e2)
  | UnOp (u, e) -> JSIL.UnOp (compile_unop u, compile_expression e)
            
  
(* Then we compile statements *)
let rec compile_statement stmt =
  (* To get labels when we know there is one *)
  let jsil_expr_of_str s = JSIL.Literal (Literal.String s) in
  let assign_of_rec_field obj_expr recfield =
    let (pn, wisl_expr) = recfield in
    let expr_pn = jsil_expr_of_str pn in
    let comp_expr = compile_expression wisl_expr in
    JSIL.LBasic (
      JSIL.Mutation (obj_expr, expr_pn, comp_expr, Some Permission.Mutable)
      )
  in
  (* No metadata here *)
  let no_metadata =
    { JSIL.line_offset = None;
      JSIL.invariant = None;
      JSIL.pre_logic_cmds = [];
      JSIL.post_logic_cmds = []
     }
  in
  let meta_lab_cmd_of_cmd cmd =
    (no_metadata, None, cmd)
  (* get new unused label *)
  in let cmdlab = LabelGenerator.get_lab ()
  in let cmdlabopt = Some cmdlab
  in
  match stmt with
  | Skip -> let cmd = JSIL.LBasic JSIL.Skip
            in [ (no_metadata, cmdlabopt, cmd) ]
  | VarAssign (v, e) -> let cmd = JSIL.LBasic
                          (JSIL.Assignment (v, compile_expression e))
                        in [ (no_metadata, cmdlabopt, cmd) ]
  | New (x, r) ->
    begin
      let newcmd = JSIL.LBasic (JSIL.New (x, None)) in
      let newcmd_with_lab = (no_metadata, Some cmdlab, newcmd) in
      let expr_x = JSIL.Var x in
      let sealcmd = JSIL.LBasic (JSIL.Seal expr_x) in
      let sealcmd_with_lab = (no_metadata, None, sealcmd) in
      let props_mut = List.map (assign_of_rec_field expr_x) r in
      let props_mut_with_lab = List.map meta_lab_cmd_of_cmd props_mut in
      (newcmd_with_lab::props_mut_with_lab)@[sealcmd_with_lab]
    end
  | Seq (s1, s2) -> let cs1 = compile_statement s1 in
                    cs1 @ (compile_statement s2)
  | Delete e -> begin
                  let comp_e = compile_expression e in
                  let cmd = JSIL.LBasic (JSIL.DeleteObj comp_e)
                  in [ (no_metadata, cmdlabopt, cmd) ]
                end
  | PropLookup (x, e, pn) ->
      begin
        let comp_e = compile_expression e in
        let exp_pn = jsil_expr_of_str pn in
        let cmd = JSIL.LBasic (JSIL.Lookup (x, comp_e, exp_pn))
        in [ (no_metadata, cmdlabopt, cmd) ]
      end
  | PropUpdate (e1, pn, e2) ->
      begin
        let comp_e1, comp_e2 = (compile_expression e1, compile_expression e2) in
        let exp_pn = jsil_expr_of_str pn in
        let cmd = JSIL.LBasic (JSIL.Mutation (comp_e1, exp_pn, comp_e2, None))
        in [ (no_metadata, cmdlabopt, cmd) ]
      end
  | FunCall (x, fn, el) ->
      begin
        let expr_fn = jsil_expr_of_str fn in
        let params = List.map compile_expression el in
        let cmd = JSIL.LCall (x, expr_fn, params, None)
        in [ (no_metadata, cmdlabopt, cmd) ]
      end
  | While (e, body) ->
      begin
        let endlab = LabelGenerator.get_lab ~pre:"end" () in
        let endlabopt = Some endlab in
        let guard = compile_expression e in
        let comp_body = compile_statement body in
        let (_, bodlabopt, _) = List.hd comp_body in
        let bodlab = Option.get bodlabopt in
        let loopheadcmd = JSIL.LGuardedGoto (guard, bodlab, endlab) in
        let gotoloopcmd = JSIL.LGoto cmdlab in
        let endcmd = JSIL.LBasic (JSIL.Skip) in
          ((no_metadata, cmdlabopt, loopheadcmd)::comp_body)@
          [(no_metadata, None, gotoloopcmd); (no_metadata, endlabopt, endcmd)]
      end
  | If (e, s1, s2) ->
      begin
        let endlab = LabelGenerator.get_lab ~pre:"end" () in
        let endlabopt = Some endlab in
        let guard = compile_expression e in
        let comp_s1 = compile_statement s1 in
        let comp_s2 = compile_statement s2 in
        let (_, thenlabopt, _) = List.hd comp_s1 in
        let (_, elselabopt, _) =  List.hd comp_s2 in
        let thenlab, elselab = Option.get thenlabopt, Option.get elselabopt in
        let ifelsecmd = JSIL.LGuardedGoto (guard, thenlab, elselab) in
        let gotoendcmd = JSIL.LGoto endlab in
        let endcmd = JSIL.LBasic JSIL.Skip in
          ((no_metadata, cmdlabopt, ifelsecmd)::comp_s1)@
          ((no_metadata, None, gotoendcmd)::comp_s2)@
          [ (no_metadata, endlabopt, endcmd) ]
      end

let clean_unused_labs lcmdlist =
  let remove_if_unused labset lcmd =
    let (meta, labopt, cmd) = lcmd in
    match labopt with None -> lcmd
    | Some lab -> if LabSet.mem lab labset then lcmd else (meta, None, cmd)
  in
  let fold_used_labs labset lcmd =
    let (_, _, cmd) = lcmd in
    match cmd with
    | JSIL.LGoto lab  -> LabSet.add lab labset
    | JSIL.LGuardedGoto (_, lab1, lab2) -> LabSet.add lab1 
                                           (LabSet.add lab2 labset)
    | _ -> labset
  in let used_labs = List.fold_left fold_used_labs LabSet.empty lcmdlist
  in List.map (remove_if_unused used_labs) lcmdlist
  


let compile_function func =
  let no_metadata =
  { JSIL.line_offset = None;
    JSIL.invariant = None;
    JSIL.pre_logic_cmds = [];
    JSIL.post_logic_cmds = []
   } in
  let (fn, params, body, ret_expr) = func in
  let lbodylist = compile_statement body in
  let comp_ret_expr = compile_expression ret_expr in
  let clean_lbodylist = clean_unused_labs lbodylist in
  let retassigncmd = JSIL.LBasic (JSIL.Assignment ("x__ret", comp_ret_expr)) in
  let lretassigncmd = (no_metadata, Some "rlab", retassigncmd) in
  let lbody_withret = clean_lbodylist@[lretassigncmd] in
  let lbody_withret_array = Array.of_list lbody_withret
  in {
    JSIL.lproc_name = fn;
    JSIL.lproc_body = lbody_withret_array;
    JSIL.lproc_params = params;
    JSIL.lret_label = Some "rlab";
    JSIL.lret_var = Some "x__ret";
    JSIL.lerror_label = None;
    JSIL.lerror_var = None;
    JSIL.lspec = None
  }

let compile_program prog =
  let get_proc_names proclist =
    List.map (fun proc -> proc.JSIL.lproc_name) proclist
  in
  let hashtbl_of_procs proclist =
    let proc_hash = Hashtbl.create (List.length proclist) in
    List.iter
      (fun proc -> Hashtbl.add proc_hash proc.JSIL.lproc_name proc)
      proclist;
    proc_hash
  in
  let main_of_stmt stmt = compile_function ("main", [], stmt, Val (Num (Int 0))) in
  let stmtopt = prog.entry_point in
  let context = prog.context in
  let comp_context = List.map compile_function context in
  let comp_mainfun = Option.map main_of_stmt stmtopt in
  let all_procs = if Option.is_none comp_mainfun
                 then comp_context
                 else (Option.get comp_mainfun)::comp_context
  in let proc_names = get_proc_names all_procs in
  let procs = hashtbl_of_procs all_procs in
  {
    JSIL.imports = [];
  	JSIL.lemmas = Hashtbl.create 1;
  	JSIL.predicates = Hashtbl.create 1;
  	JSIL.onlyspecs = Hashtbl.create 1;
  	JSIL.procedures = procs;
  	JSIL.procedure_names = proc_names;
  }
  
  
  
  
  