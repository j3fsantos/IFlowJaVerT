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





(* WISL Compiler *)
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
  | LSTCONS -> BinOp.LstCons
  | LSTCAT -> BinOp.LstCat
  | _ -> failwith (Format.asprintf "compile_binop should not be used to compile %a"
                  WISL_Printer.pp_binop b)

let compile_unop u = match u with
  | NOT -> UnOp.Not
  | LEN -> UnOp.LstLen
  | HEAD -> UnOp.Car
  | TAIL -> UnOp.Cdr

let rec compile_value v = match v with
  | Bool b -> Literal.Bool b
  | Null -> Literal.Null
  | Loc l -> Literal.Loc l
  | Num n -> Literal.Num (float_of_num n)
  | Str s -> Literal.String s
  | VList l -> Literal.LList (List.map compile_value l)


let rec compile_expression ?(in_lemma = false) expr =
  let is_special_binop b = match b with
    | NEQ | GREATERTHAN | GREATEREQUAL -> true
    | _ -> false
  in
  let is_logic_only_binop b = match b with
    | LSTCONS | LSTCAT -> true
    | _ -> false
  in
  let is_logic_only_unop u = match u with
    | HEAD | TAIL | LEN -> true
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
    | _ -> failwith (Format.asprintf 
      "Operator %a is not a special operator" WISL_Printer.pp_binop b)
  in
  match expr with
  | Val (VList vl) when not in_lemma -> failwith "lists can only be used in the logic"
  | Val v -> JSIL.Literal (compile_value v)
  | Var "ret" -> failwith "ret is the special name used for the return
                           value in the logic. It cannot be a variable name"
  | Var x -> JSIL.Var x
  | BinOp (e1, b, e2) when not (in_lemma) && (is_logic_only_binop b) ->
      failwith (Format.asprintf "Operator %a should only be used in the logic"
      WISL_Printer.pp_binop b)
  | BinOp (e1, b, e2) when is_special_binop b ->
    compile_special_binop (e1, b, e2)
  | BinOp (e1, b, e2) -> JSIL.BinOp (compile_expression e1,
                         compile_binop b, compile_expression e2)
  | UnOp (u, e) when (not in_lemma) && (is_logic_only_unop u) 
  ->
      failwith (Format.asprintf "Operator %a should only be used in the logic"
      WISL_Printer.pp_unop u)
  | UnOp (u, e) -> JSIL.UnOp (compile_unop u, compile_expression e)


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
  

(* Logic related stuff *)
let rec compile_logic_expression lexpr =
  let is_special_binop b = match b with
    | NEQ | GREATERTHAN | GREATEREQUAL -> true
    | _ -> false
  in
  let compile_special_binop (le1, b, le2) =
    let comp_le1 = compile_logic_expression le1 in
    let comp_le2 = compile_logic_expression le2 in
    match b with
    | NEQ -> 
        JSIL.LUnOp (
          UnOp.Not,
          JSIL.LBinOp (comp_le1, BinOp.Equal, comp_le2)
        )
    | GREATERTHAN ->
        JSIL.LUnOp (
          UnOp.Not,
          JSIL.LBinOp (comp_le1, BinOp.LessThanEqual, comp_le2)
        )
    | GREATEREQUAL ->
        JSIL.LUnOp (
          UnOp.Not,
          JSIL.LBinOp (comp_le1, BinOp.LessThan, comp_le2)
        )
    | _ -> failwith (Format.asprintf 
      "Operator %a is not a special operator" WISL_Printer.pp_binop b)
  in
  match lexpr with
  | LVal v -> JSIL.LLit (compile_value v)
  | LVar lx -> JSIL.LVar lx
  | PVar "ret" -> JSIL.PVar "x__ret" (* special name for return value *)
  | PVar x -> JSIL.PVar x
  | LBinOp (le1, b, le2) when is_special_binop b ->
    compile_special_binop (le1, b, le2)
  | LBinOp (le1, b, le2) ->
      JSIL.LBinOp (compile_logic_expression le1,
                   compile_binop b,
                   compile_logic_expression le2)
  | LUnOp (u, le) ->
      JSIL.LUnOp (compile_unop u, compile_logic_expression le)
  | LEList lel -> JSIL.LEList (List.map compile_logic_expression lel)


let rec compile_logic_assertion asser = match asser with
  | LTrue -> JSIL.LTrue
  | LFalse -> JSIL.LFalse
  | LNot la -> JSIL.LNot (compile_logic_assertion la)
  | LAnd (la1, la2) -> JSIL.LAnd
          (compile_logic_assertion la1,
           compile_logic_assertion la2)
  | LOr (la1, la2) -> JSIL.LOr
          (compile_logic_assertion la1,
           compile_logic_assertion la2)
  | LEmp -> JSIL.LEmp
  | LStar (la1, la2) -> JSIL.LStar
          (compile_logic_assertion la1,
           compile_logic_assertion la2)
  | LPointsTo (le1, pn, le3) -> JSIL.LPointsTo
          (compile_logic_expression le1,
           JSIL.LLit (Literal.String pn),
           (Permission.Mutable, compile_logic_expression le3))
  | LEq (le1, le2) -> JSIL.LEq
          (compile_logic_expression le1,
           compile_logic_expression le2)
  | LLess (le1, le2) -> JSIL.LLess
          (compile_logic_expression le1,
           compile_logic_expression le2)
  | LGreater (le1, le2) -> JSIL.LNot (
           JSIL.LLessEq
           (compile_logic_expression le1,
            compile_logic_expression le2))
  | LLessEq (le1, le2) -> JSIL.LLessEq
          (compile_logic_expression le1,
           compile_logic_expression le2)
  | LGreaterEq (le1, le2) -> JSIL.LNot
          (JSIL.LLess
           (compile_logic_expression le1,
            compile_logic_expression le2))
  | LPred (pr, lel) -> JSIL.LPred (
            pr,
            List.map compile_logic_expression lel
          )

let compile_spec pre post name params =
  let comp_pre = compile_logic_assertion pre in
  let comp_post = compile_logic_assertion post in
  let single_spec = JSIL.create_single_spec comp_pre [comp_post] JSIL.Normal in
  JSIL.{
    spec_name = name;
    spec_params = params;
    proc_specs = [single_spec];
    previously_normalised = false;
  }

let compile_type t = match t with
  | WList -> Type.ListType
  | WNull -> Type.NullType
  | WBool -> Type.BooleanType
  | WString -> Type.StringType
  | WObj -> Type.ObjectType
  | WNum -> Type.NumberType

let compile_predicate pred =
  let _, logic_asserts = List.split pred.pred_definitions in
  let types = WISL_Utils.infer_types_pred logic_asserts in
  let getWISLTypes = fun str -> (str, WISL_Utils.TypeMap.find_opt (PVar str) types) in
  let paramsWISLType = List.map getWISLTypes pred.pred_params in
  let getJSILTypes = fun (str, t) -> (str, Option.map compile_type t) in
  let params = List.map getJSILTypes paramsWISLType in
  JSIL.{
    name = pred.pred_name;
    num_params = List.length pred.pred_params;
    params = params;
    ins = pred.ins;
    definitions = List.map 
                  (fun (stopt, asst) -> (stopt, compile_logic_assertion asst))
                  pred.pred_definitions;
    previously_normalised_pred = false;
  }
  
(* TODO: actually implement that *)
let rec compile_logic_command lcmd = match lcmd with
  | Fold la -> let comp_la = compile_logic_assertion la in
               JSIL.Fold comp_la
  | Unfold la -> let comp_la = compile_logic_assertion la in
                 JSIL.Unfold (comp_la, None)
  | ApplyLem (ln, lel) -> let params = List.map compile_logic_expression lel in
                          JSIL.ApplyLem (ln, params)
  | RecUnfold str -> JSIL.RecUnfold str
  | LogicIf (guard, lc1, lc2) ->
      let comp_guard = compile_logic_expression guard in
      let comp_lc1 = List.map compile_logic_command lc1 in
      let comp_lc2 = List.map compile_logic_command lc2 in
      JSIL.LogicIf (comp_guard, comp_lc1, comp_lc2)
  | Assert la -> let comp_la = compile_logic_assertion la in
                 JSIL.Assert comp_la
                 


let compile_metadata meta =
  let invariant = Option.map compile_logic_assertion meta.invariant in
  let pre_logic_cmds = List.map compile_logic_command meta.precmds in
  let post_logic_cmds = List.map compile_logic_command meta.postcmds in
  let line_offset = None in
  JSIL.{ line_offset; invariant; pre_logic_cmds; post_logic_cmds}
  

let separate_pre_post_meta meta =
  let pre = {
    precmds = meta.precmds;
    postcmds = [];
    invariant = meta.invariant;
  } in
  let post = {
    precmds = [];
    postcmds = meta.postcmds;
    invariant = None;
  }
  in (pre, post)


let rec compile_statement_with_meta (meta, stmt) = 
  let comp_meta = compile_metadata meta in
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
  let no_metadata =
  { JSIL.line_offset = None;
    JSIL.invariant = None;
    JSIL.pre_logic_cmds = [];
    JSIL.post_logic_cmds = []
   } in
  let meta_lab_cmd_of_cmd cmd = (no_metadata, None, cmd)
  (* get new unused label *)
  in let cmdlab = LabelGenerator.get_lab ()
  in let cmdlabopt = Some cmdlab
  in
  match stmt with
  | Skip -> let cmd = JSIL.LBasic JSIL.Skip
            in [ (comp_meta, cmdlabopt, cmd) ]
  | VarAssign (v, e) -> let cmd = JSIL.LBasic
                          (JSIL.Assignment (v, compile_expression e))
                        in [ (comp_meta, cmdlabopt, cmd) ]
  | New (x, r) ->
    begin
      let (pre_meta, post_meta) = separate_pre_post_meta meta in
      let (pre_meta_comp, post_meta_comp) =
        (compile_metadata pre_meta, compile_metadata post_meta) in
      let newcmd = JSIL.LBasic (JSIL.New (x, None)) in
      let newcmd_with_lab = (pre_meta_comp, Some cmdlab, newcmd) in
      let expr_x = JSIL.Var x in
      let sealcmd = JSIL.LBasic (JSIL.Seal expr_x) in
      let sealcmd_with_lab = (post_meta_comp, None, sealcmd) in
      let props_mut = List.map (assign_of_rec_field expr_x) r in
      let props_mut_with_lab = List.map meta_lab_cmd_of_cmd props_mut in
      (newcmd_with_lab::props_mut_with_lab)@[sealcmd_with_lab]
    end
  | Delete e -> begin
                  let comp_e = compile_expression e in
                  let cmd = JSIL.LBasic (JSIL.DeleteObj comp_e)
                  in [ (comp_meta, cmdlabopt, cmd) ]
                end
  | PropLookup (x, e, pn) ->
      begin
        let comp_e = compile_expression e in
        let exp_pn = jsil_expr_of_str pn in
        let cmd = JSIL.LBasic (JSIL.Lookup (x, comp_e, exp_pn))
        in [ (comp_meta, cmdlabopt, cmd) ]
      end
  | PropUpdate (e1, pn, e2) ->
      begin
        let comp_e1, comp_e2 = (compile_expression e1, compile_expression e2) in
        let exp_pn = jsil_expr_of_str pn in
        let cmd = JSIL.LBasic (JSIL.Mutation (comp_e1, exp_pn, comp_e2, None))
        in [ (comp_meta, cmdlabopt, cmd) ]
      end
  | FunCall (x, fn, el) ->
      begin
        let expr_fn = jsil_expr_of_str fn in
        let params = List.map compile_expression el in
        let cmd = JSIL.LCall (x, expr_fn, params, None)
        in [ (comp_meta, cmdlabopt, cmd) ]
      end
  | While (e, body) ->
      begin
        if Option.is_none meta.invariant then
          Format.printf "Every while statement has to be preceded by an invariant, analysis will fail.@.@.";
        let (pre_meta, post_meta) = separate_pre_post_meta meta in
        let (pre_meta_comp, post_meta_comp) =
          (compile_metadata pre_meta, compile_metadata post_meta) in
        let endlab = LabelGenerator.get_lab ~pre:"end" () in
        let endlabopt = Some endlab in
        let guard = compile_expression e in
        let comp_body = List.flatten (List.map compile_statement_with_meta body) in
        let (_, bodlabopt, _) = List.hd comp_body in
        let bodlab = Option.get bodlabopt in
        let loopheadcmd = JSIL.LGuardedGoto (guard, bodlab, endlab) in
        let gotoloopcmd = JSIL.LGoto cmdlab in
        let endcmd = JSIL.LBasic (JSIL.Skip) in
          ((pre_meta_comp, cmdlabopt, loopheadcmd)::comp_body)@
          [(no_metadata, None, gotoloopcmd); (post_meta_comp, endlabopt, endcmd)]
      end
  | If (e, s1, s2) ->
      begin
        let (pre_meta, post_meta) = separate_pre_post_meta meta in
        let (pre_meta_comp, post_meta_comp) =
          (compile_metadata pre_meta, compile_metadata post_meta) in
        let endlab = LabelGenerator.get_lab ~pre:"end" () in
        let endlabopt = Some endlab in
        let guard = compile_expression e in
        let comp_s1 = List.flatten (List.map compile_statement_with_meta s1) in
        let comp_s2 = List.flatten (List.map compile_statement_with_meta s2) in
        let (_, thenlabopt, _) = List.hd comp_s1 in
        let (_, elselabopt, _) =  List.hd comp_s2 in
        let thenlab, elselab = Option.get thenlabopt, Option.get elselabopt in
        let ifelsecmd = JSIL.LGuardedGoto (guard, thenlab, elselab) in
        let gotoendcmd = JSIL.LGoto endlab in
        let endcmd = JSIL.LBasic JSIL.Skip in
          ((pre_meta_comp, cmdlabopt, ifelsecmd)::comp_s1)@
          ((no_metadata, None, gotoendcmd)::comp_s2)@
          [ (post_meta_comp, endlabopt, endcmd) ]
      end


let compile_lemma lemma =
  let { lemma_name; lemma_params; proof; variant; hypothesis; conclusions } = lemma in
  let lemma_proof = Option.map (List.map compile_logic_command) proof in
  let lemma_variant = Option.map (compile_expression ~in_lemma:true) variant in
  let single_spec = JSIL.{
    pre = compile_logic_assertion hypothesis;
    post = List.map compile_logic_assertion conclusions;
    ret_flag = JSIL.Normal;
  } in
  let lemma_spec = JSIL.{
    spec_name = lemma_name;
    spec_params = lemma_params;
    proc_specs = [single_spec];
    previously_normalised = false;
  } in
  JSIL.{ lemma_name; lemma_spec; lemma_proof; lemma_variant }

(* program related stuff *)
let compile_function func =
  let no_metadata =
  { JSIL.line_offset = None;
    JSIL.invariant = None;
    JSIL.pre_logic_cmds = [];
    JSIL.post_logic_cmds = []
   } in
  let fn = func.name in
  let params = func.params in
  let body = func.body in
  let ret_expr = func.return_expr in
  let lbodylist = List.flatten (List.map compile_statement_with_meta body) in
  let comp_ret_expr = compile_expression ret_expr in
  let clean_lbodylist = clean_unused_labs lbodylist in
  let retassigncmd = JSIL.LBasic (JSIL.Assignment ("x__ret", comp_ret_expr)) in
  let lretassigncmd = (no_metadata, None, retassigncmd) in
  let rlabcmd = (no_metadata, Some "rlab", JSIL.LBasic (JSIL.Skip)) in
  let lbody_withret = clean_lbodylist@[lretassigncmd; rlabcmd] in
  let lbody_withret_array = Array.of_list lbody_withret in
  let specs = match func.spec with
    | Some sp -> Some (compile_spec sp.pre sp.post fn params)
    | None -> None
  in {
    JSIL.lproc_name = fn;
    JSIL.lproc_body = lbody_withret_array;
    JSIL.lproc_params = params;
    JSIL.lret_label = Some "rlab";
    JSIL.lret_var = Some "x__ret";
    JSIL.lerror_label = None;
    JSIL.lerror_var = None;
    JSIL.lspec = specs
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
  let hashtbl_of_preds predlist =
    let pred_hash:((string, JSIL.jsil_logic_predicate) Hashtbl.t) = Hashtbl.create (List.length predlist) in
    List.iter
      (fun pred -> 
        let _ = pred.JSIL.previously_normalised_pred in (* Necessary so type inference do not fail *)
        Hashtbl.add pred_hash pred.JSIL.name pred)
      predlist;
    pred_hash
  in
  let hashtbl_of_lemmas lemmalist =
    let lemma_hash = Hashtbl.create (List.length lemmalist) in
    List.iter
      (fun lemma -> Hashtbl.add lemma_hash lemma.JSIL.lemma_name lemma)
      lemmalist;
    lemma_hash
  in
  let main_of_stmt stmt = compile_function ({
    name="main";
    params=[];
    body=stmt;
    spec = None;
    return_expr=(Val (Num (Int 0)))
    }) in
  let stmtopt = prog.entry_point in
  let context = prog.context in
  let preds = prog.predicates in
  let lemmas = prog.lemmas in
  let comp_context = List.map compile_function context in
  let comp_mainfun = Option.map main_of_stmt stmtopt in
  let comp_preds = List.map compile_predicate preds in
  let comp_lemmas = List.map compile_lemma lemmas in
  let all_procs = if Option.is_none comp_mainfun
                 then comp_context
                 else (Option.get comp_mainfun)::comp_context
  in let proc_names = get_proc_names all_procs in
  let procs = hashtbl_of_procs all_procs in
  let jsil_preds = hashtbl_of_preds comp_preds in
  let jsil_lemmas = hashtbl_of_lemmas comp_lemmas in
  {
    JSIL.imports = [];
  	JSIL.lemmas = jsil_lemmas;
  	JSIL.predicates = jsil_preds;
  	JSIL.onlyspecs = Hashtbl.create 1;
  	JSIL.procedures = procs;
  	JSIL.procedure_names = proc_names;
  }
  
  
  
  
  