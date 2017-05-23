open Parser_syntax
open Utils
open Batteries
open Js2jsil_constants
open JS_Utils

exception CannotHappen
exception No_Codename
exception EarlyError of string


(********************************************)
(********************************************)
(***         Annotations                  ***)
(********************************************)
(********************************************)

let update_annotation annots atype new_value =
  let old_removed = List.filter (fun annot -> annot.annot_type <> atype) annots in
  let annot = {annot_type = atype; annot_formula = new_value} in
  (* Printf.printf "I am adding the code name: %s"  new_value; *)
  annot :: old_removed

let get_top_level_annot e =
  match e.Parser_syntax.exp_stx with
  | Script (_, les) ->
    let first_le = List.nth les 0 in
    let annot = first_le.Parser_syntax.exp_annot in
    Some annot
  | _ -> None



(********************************************)
(********************************************)
(***         Logic Annotations            ***)
(********************************************)
(********************************************)

let get_predicate_defs_from_annots annots : JS_Logic_Syntax.js_logic_predicate list =
  let pred_def_annots = List.filter (fun annot -> annot.annot_type == Parser_syntax.Pred) annots in 
  let pred_defs = List.map (fun pred_def -> JSIL_Utils.js_logic_pred_def_of_string ("pred " ^ pred_def.annot_formula)) pred_def_annots in 
  pred_defs 

let get_only_specs_from_annots annots : unit =
  let only_specs_annots = List.filter (fun annot -> annot.annot_type == Parser_syntax.OnlySpec) annots in 
  List.iter (fun only_spec -> JSIL_Utils.js_only_spec_from_string ("js_only_spec " ^ only_spec.annot_formula)) only_specs_annots 
  
let parse_logic_annots annots = 
  List.map 
    (fun annot -> 
      let assertion = JSIL_Utils.js_assertion_of_string annot.annot_formula in
      (annot.annot_type, assertion))
    annots        

let process_js_logic_annotations 
      (cc_tbl              : cc_tbl_type) 
      (vis_tbl             : vis_tbl_type) 
      (fun_tbl             : pre_fun_tbl_type) 
      (fun_name            : string) 
      (fun_args            : string list) 
      (annotations         : Parser_syntax.annotation list)
      (requires_flag       : Parser_syntax.annotation_type) 
      (ensures_normal_flag : Parser_syntax.annotation_type)
      (ensure_err_flag     : Parser_syntax.annotation_type) =
  (* Printf.printf "Inside process_js_logic_annotations. function: %s.\n\nAnnotations: \n%s\n\n" fun_name (Pretty_print.string_of_annots annotations); *)
  
  let var_to_fid_tbl : var_to_fid_tbl_type = Js2jsil_constants.get_scope_table cc_tbl fun_name in 
  let vis_list = Js2jsil_constants.get_vis_tbl vis_tbl fun_name in 

  (* 
  let annot_types_str : string = String.concat ", " (List.map (fun annot -> Pretty_print.string_of_annot_type annot.annot_type) annotations) in 
  Printf.printf "annot types: %s\n\n" annot_types_str; *)

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
      let annot_type = post.annot_type in 
      let ret_flag  =
        if (annot_type = ensures_normal_flag)
          then JSIL_Syntax.Normal
          else (if (annot_type = ensure_err_flag)
            then JSIL_Syntax.Error
            else raise (Failure "DEATH: process_js_logic_annotations")) in
      (* Printf.printf "pre_str: %s. post_str: %s\n" pre_str post_str; *)
      let pre_js  = JSIL_Utils.js_assertion_of_string pre_str in
      let post_js = JSIL_Utils.js_assertion_of_string post_str in
      (* Printf.printf "I managed to parse the js assertions\n"; *)
      
      let pre_jsil = JS_Logic_Syntax.js2jsil_logic_top_level_pre pre_js cc_tbl vis_tbl fun_tbl fun_name in
      let post_jsil = JS_Logic_Syntax.js2jsil_logic_top_level_post post_js cc_tbl vis_tbl fun_tbl fun_name in
      let new_spec = JSIL_Syntax.create_single_spec pre_jsil post_jsil ret_flag in
      new_spec)
    preconditions
    postconditions in

  let args = 
    if (fun_name = Js2jsil_constants.var_main)
      then fun_args 
      else (Js2jsil_constants.var_scope :: (Js2jsil_constants.var_this :: fun_args)) in 

  let fun_spec = if ((List.length single_specs) > 0)
    then Some (JSIL_Syntax.create_jsil_spec fun_name args single_specs)
    else None in
  fun_spec


(**
  * Populates the new fun_tbl given the old fun_tbl   
  * by compiling the specs in the old fun_tbl
*)
let create_js_logic_annotations 
    (cc_tbl      : cc_tbl_type) 
    (vis_tbl     : vis_tbl_type) 
    (old_fun_tbl : Js2jsil_constants.pre_fun_tbl_type) 
    (new_fun_tbl : Js2jsil_constants.fun_tbl_type) =
  Hashtbl.iter 
    (fun f_id (f_id, f_args, f_body, (annotations, _, _)) ->
      let fun_specs = 
        if (not (f_id = Js2jsil_constants.var_main))
          then process_js_logic_annotations cc_tbl vis_tbl old_fun_tbl f_id f_args annotations Requires Ensures EnsuresErr   
          else process_js_logic_annotations cc_tbl vis_tbl old_fun_tbl f_id [] annotations TopRequires TopEnsures TopEnsuresErr in 
      Hashtbl.add new_fun_tbl f_id (f_id, f_args, f_body, fun_specs))
    old_fun_tbl


let rec get_predicate_definitions exp =
  let f_ac exp state prev_state ac = 
    let new_pred_defs : JS_Logic_Syntax.js_logic_predicate list = (get_predicate_defs_from_annots exp.Parser_syntax.exp_annot) in 
     new_pred_defs @ ac in 
  js_accumulator_top_down f_ac (fun x y -> y) true exp



(********************************************)
(********************************************)
(***       IDs and CodeNames              ***)
(********************************************)
(********************************************)

let sanitise name =
  let s = Str.global_replace (Str.regexp "\$") "_" name in
  s


let update_codename_annotation annots fresh_name_generator =
  let ids = List.filter (fun annot -> annot.annot_type = Id) annots in
  (match ids with 
  | [ ]    -> update_annotation annots Codename (fresh_name_generator ())
  | [ id ] -> update_annotation annots Codename id.annot_formula
  | _ :: _ -> raise (Failure "you cannot have more than one identifier per function"))

let get_codename exp =
  let codenames = List.filter (fun annot -> annot.annot_type = Codename) exp.exp_annot in
  match codenames with
    | [codename] -> codename.annot_formula
    | _ -> raise No_Codename


let rec add_codenames (main                  : string) 
                      (fresh_anonymous       : unit -> string) 
                      (fresh_named           : string -> string) 
                      (fresh_catch_anonymous : unit -> string) 
                      exp =  
  let f_m e = 
    match e.exp_stx with 
    | FunctionExp _ -> 
      let new_annot = update_codename_annotation e.exp_annot fresh_anonymous in 
      {e with exp_stx = e.exp_stx; exp_annot = new_annot }
    | Function (str, Some name, args, fb) -> 
      let name_generator : unit -> string = (fun () -> fresh_named (sanitise name)) in 
      let new_annot = update_codename_annotation e.exp_annot name_generator in 
      {exp with exp_stx = e.exp_stx; exp_annot = new_annot }
    | Try _ ->
      let catch_id = fresh_catch_anonymous () in
      let annot = [{annot_type = Codename; annot_formula = catch_id}] in
      { exp with exp_stx = e.exp_stx; exp_annot = annot }
    | _ -> e in 

  js_mapper f_m exp 



(********************************************)
(********************************************)
(***         Closure Clarification        ***)
(********************************************)
(********************************************)


let closure_clarification 
    (cc_tbl       : Js2jsil_constants.cc_tbl_type) 
    (fun_tbl      : Js2jsil_constants.pre_fun_tbl_type) 
    (vis_tbl      : vis_tbl_type) 
    (f_id         : string) 
    (visited_funs : string list) 
    (exp          : Parser_syntax.exp) =  
  
  let rec f_state e state = 
    match state with 
    | None -> None 
    | Some (f_id, visited_funs) -> (
      let cur_annot = e.Parser_syntax.exp_annot in
      match e.exp_stx with
      | FunctionExp (_, f_name, args, fb) -> 
        (match f_name with
        | None ->
          let new_f_id = get_codename e in
          let new_f_tbl = update_cc_tbl cc_tbl f_id new_f_id (get_all_vars_f fb args) in
          update_fun_tbl fun_tbl new_f_id args (Some fb) cur_annot new_f_tbl (new_f_id :: visited_funs);
          Hashtbl.replace vis_tbl new_f_id (new_f_id :: visited_funs); 
          Some (new_f_id, (new_f_id :: visited_funs))
        | Some f_name ->
          let new_f_id = get_codename e in
          let new_f_id_outer = new_f_id ^ "_outer" in
          let _ = update_cc_tbl_single_var_er cc_tbl f_id new_f_id_outer f_name in
          let new_f_tbl = update_cc_tbl cc_tbl new_f_id_outer new_f_id (get_all_vars_f fb args) in
          update_fun_tbl fun_tbl new_f_id args (Some fb) cur_annot new_f_tbl (new_f_id :: new_f_id_outer :: visited_funs);
          Hashtbl.replace vis_tbl new_f_id (new_f_id :: new_f_id_outer :: visited_funs);
          Some (new_f_id, (new_f_id :: new_f_id_outer :: visited_funs)))
      | Function (_, f_name, args, fb) ->
        let new_f_id = get_codename e in
        let new_f_tbl = update_cc_tbl cc_tbl f_id new_f_id (get_all_vars_f fb args) in
        update_fun_tbl fun_tbl new_f_id args (Some fb) cur_annot new_f_tbl (new_f_id :: visited_funs);
        Hashtbl.replace vis_tbl new_f_id (new_f_id :: visited_funs);
        Some (new_f_id, (new_f_id :: visited_funs))
      | Try (_, Some (_, _), _)  -> None 
      | _     -> state) in 

  let rec f_ac e state prev_state ac = 
    match prev_state with 
    | None -> ac 
    | Some (f_id, visited_funs) -> 
      match e.exp_stx with
      | Try (e1, Some (x, e2), e3) ->
        let f = js_accumulator_top_down f_ac f_state in 
        let _ = f prev_state e1 in 
        let _ = Option.map (f prev_state) e3 in 
        let new_f_id = get_codename e in
        update_cc_tbl_single_var_er cc_tbl f_id new_f_id x;
        f (Some (new_f_id, (new_f_id :: visited_funs))) e2
      | _ -> [] in 
  js_accumulator_top_down f_ac f_state (Some (f_id, visited_funs)) exp 






let closure_clarification_top_level 
      cc_tbl 
      (fun_tbl : Js2jsil_constants.fun_tbl_type) 
      (old_fun_tbl: Js2jsil_constants.pre_fun_tbl_type) 
      vis_tbl 
      proc_id 
      e 
      vis_fid : (string, JSIL_Syntax.jsil_logic_predicate) Hashtbl.t =
  let proc_tbl = Hashtbl.create Js2jsil_constants.medium_tbl_size in

  let proc_vars = get_all_vars_f e [] in
  List.iter
    (fun v -> Hashtbl.replace proc_tbl v proc_id)
    proc_vars;
  Hashtbl.add cc_tbl proc_id proc_tbl;
  Hashtbl.add old_fun_tbl proc_id (proc_id, [], Some e, ([], [ proc_id ], proc_tbl));
  Hashtbl.add vis_tbl proc_id vis_fid;
  closure_clarification cc_tbl old_fun_tbl vis_tbl proc_id vis_fid e;
  create_js_logic_annotations cc_tbl vis_tbl old_fun_tbl fun_tbl;
  let js_predicate_definitions : JS_Logic_Syntax.js_logic_predicate list = get_predicate_definitions e in  
  let jsil_predicate_definitions = 
    List.map (fun pred_def -> JS_Logic_Syntax.translate_predicate_def pred_def cc_tbl vis_tbl old_fun_tbl) js_predicate_definitions in 
  let annots = get_top_level_annot e in
  (match annots with
  | Some annots ->
    (*Printf.printf "Going to generate main. Top-level annotations:\n%s\n" (Pretty_print.string_of_annots annots); *)
    let specs = process_js_logic_annotations cc_tbl vis_tbl old_fun_tbl proc_id [] annots TopRequires TopEnsures TopEnsuresErr in
    Hashtbl.replace fun_tbl proc_id (proc_id, [], Some e, specs);
  | None -> ()); 
  let jsil_pred_def_tbl : (string, JSIL_Syntax.jsil_logic_predicate) Hashtbl.t = JSIL_Syntax.pred_def_tbl_from_list jsil_predicate_definitions in 
  jsil_pred_def_tbl
  



(********************************************)
(********************************************)
(***         Folds and Unfolds            ***)
(********************************************)
(********************************************)


let rec expand_flashes e =
  let f_m e = 
    let annots = e.exp_annot in 
    let new_annots = List.concat (List.map 
      (fun annot -> 
        let formula = annot.annot_formula in 
        match annot.annot_type with
        | Flash -> [ { annot_type = Unfold; annot_formula = formula }; { annot_type = Fold; annot_formula = formula } ]
        | _     -> [ annot ]) annots) in 
    { e with exp_annot = new_annots } in 
  js_mapper f_m e



let rec ground_fun_annotations fun_annots e = 
 
  let add_more_annots e annots = { e with exp_annot = e.exp_annot @ annots } in 

  let add_more_annots_option eo annots = 
    match eo with 
    | None -> None 
    | Some e -> Some (add_more_annots e annots) in 

  let prev_folds, prev_specs = 
    List.partition (fun annot -> (annot.annot_type  = Parser_syntax.Fold)) fun_annots in

  let folds, rest_annots = 
    List.partition (fun annot -> (annot.annot_type  = Parser_syntax.Fold)) e.exp_annot in 

  let specs, rest_annots = 
    List.partition 
      (fun annot ->
        let annot_type = annot.annot_type  in 
          ((annot_type = Parser_syntax.Id) || (annot_type = Parser_syntax.Requires) || 
              (annot_type = Parser_syntax.Ensures) || (annot_type = Parser_syntax.EnsuresErr)))
      rest_annots in 
    
  let next_fun_annots = 
    match e.exp_stx with
    | New (_, _) | Call (_, _)                         -> prev_specs @ specs 
    | FunctionExp (_, _, _, _) | Function (_, _, _, _) -> prev_folds @ folds
    | _ -> prev_specs @ specs @ folds @ prev_folds in 
  
  let f = ground_fun_annotations next_fun_annots in 
 
  let f_im_done funn_annots e = 
    let e', next_fun_annots' = ground_fun_annotations funn_annots e in 
    let e'' = add_more_annots e' next_fun_annots' in 
    e'' in 

  let f_im_done_optional funn_annots e = 
    match e with 
    | None -> None 
    | Some e -> Some (f_im_done funn_annots e) in 

  let f_optional eo next_fun_annots = 
    (match eo with 
    | None   -> None, next_fun_annots
    | Some e -> 
      let e', next_fun_annots' = ground_fun_annotations next_fun_annots e in 
      Some e', next_fun_annots') in  
  
  let f_2 e1 e2 = 
    let e1', next_fun_annots_1 = f e1 in 
    let e2', next_fun_annots_2 = ground_fun_annotations next_fun_annots_1 e2 in 
    e1', e2', next_fun_annots_2 in 
  
  let f_3 e1 e2 e3 = 
    let e1', e2', next_fun_annots_2 = f_2 e1 e2 in 
    let e3', next_fun_annots_3 = ground_fun_annotations next_fun_annots_2 e3 in 
    e1', e2', e3', next_fun_annots_3 in 
  

  let rec f_args args processed_args next_fun_annots = 
    match args with 
    | [] -> List.rev processed_args, next_fun_annots 
    | arg :: rest_args -> 
      let arg', next_fun_annots' = ground_fun_annotations next_fun_annots arg in
      f_args rest_args (arg' :: processed_args) next_fun_annots' in  


  let rec f_arr es traversed_es next_fun_annots =
    match es with 
    | [] -> (List.rev traversed_es), next_fun_annots
    | e :: rest_es -> 
      (match e with 
      | None -> f_arr rest_es (e :: traversed_es) next_fun_annots
      | Some e -> 
        let e', next_fun_annots' = ground_fun_annotations next_fun_annots e in 
        f_arr rest_es ((Some e') :: traversed_es) next_fun_annots') in 
  
  let rec f_var_decl vdecls traversed_vdecls next_fun_annots = 
    match vdecls with 
    | [] -> (List.rev traversed_vdecls), next_fun_annots 
    | (v, eo) :: rest_vdecls -> 
      (match eo with 
      | None -> f_var_decl rest_vdecls ((v, eo) :: traversed_vdecls) next_fun_annots
      | Some e -> 
        let e', next_fun_annots' = ground_fun_annotations next_fun_annots e in 
        f_var_decl rest_vdecls ((v, Some e') :: traversed_vdecls) next_fun_annots') in 
  
  let f_cases cases = 
    List.map 
      (fun (e, s) -> 
        let e' = 
          match e with 
          | DefaultCase -> DefaultCase 
          | Case e -> 
            let e', _ = ground_fun_annotations [] e in 
            Case e' in 
        let s', _ = ground_fun_annotations [] s in 
        (e', s'))
      cases in
  
  let rec loop_obj_props props processed_props next_fun_annots = 
    match props with 
    | [] -> (List.rev processed_props), next_fun_annots
    | (x, p, e) :: rest_props -> 
      let e', next_fun_annots' = ground_fun_annotations next_fun_annots e in 
      loop_obj_props rest_props ((x, p, e') :: processed_props) next_fun_annots' in 
        

  let new_exp_stx, next_fun_annots', fun_annots_to_reinclude =         
    match e.exp_stx with
    (* Literals *)
    | Null | Bool _ | String _ | Num _ -> e.exp_stx, next_fun_annots, []
    (* Expressions *)
    
    | This | Var _ -> e.exp_stx, next_fun_annots, [] 
    
    | Obj xs -> 
      let xs', next_fun_annots' = loop_obj_props xs [] next_fun_annots in 
      Obj xs', next_fun_annots', []
    
    | Access (e, v) -> 
      let e', next_fun_annots' = f e in 
      Access (e', v), next_fun_annots', [] 
    
    | CAccess (e1, e2) -> 
      let e1', e2', next_fun_annots' = f_2 e1 e2 in 
      CAccess (e1', e2'), next_fun_annots', []
    
    | New (e1, e2s) -> 
      let e1', next_fun_annots_1 = ground_fun_annotations next_fun_annots e1 in 
      let e2s', next_fun_annots_2 = f_args e2s [] next_fun_annots_1 in 
      New (e1', e2s'), next_fun_annots_2, []
    
    | Call (e1, e2s) -> 
      let e1', next_fun_annots_1 = ground_fun_annotations next_fun_annots e1 in 
      let e2s', next_fun_annots_2 = f_args e2s [] next_fun_annots_1 in 
      Call (e1', e2s'), next_fun_annots_2, []
    
    | FunctionExp (b, f_name, args, fb) -> 
      (* Printf.printf "I got a ****FUNCTION*** BABY!!!!\n"; *)
      let fb', _ = ground_fun_annotations [] fb in 
      FunctionExp (b, f_name, args, fb'), next_fun_annots, []

    | Function (b, f_name, args, fb) ->
      let fb', _ = ground_fun_annotations [] fb in 
      Function (b, f_name, args, fb'), next_fun_annots, []

    | Unary_op (op, e) -> 
      let e', next_fun_annots' = f e in
      Unary_op (op, e'), next_fun_annots', []

    | Delete e ->
      let e', next_fun_annots' = f e in 
      Delete e', next_fun_annots', []

    | BinOp (e1, op, e2) ->
      let e1', e2', next_fun_annots' = f_2 e1 e2 in 
      BinOp (e1', op, e2'), next_fun_annots', []

    | Assign (e1, e2) -> 
      let e1', e2', next_fun_annots' = f_2 e1 e2 in 
      Assign (e1', e2'), next_fun_annots', []

    | Array es -> 
      let es', next_fun_annots' = f_arr es [] next_fun_annots in 
      Array es', next_fun_annots', []

    | ConditionalOp (e1, e2, e3) -> 
      let e1', e2', e3', next_fun_annots' = f_3 e1 e2 e3 in 
      ConditionalOp (e1', e2', e3'), next_fun_annots', []
    
    | AssignOp (e1, op, e2) -> 
      let e1', e2', next_fun_annots' = f_2 e1 e2 in 
      AssignOp (e1', op, e2'), next_fun_annots', []

    | Comma (e1, e2) -> 
      let e1', e2', next_fun_annots' = f_2 e1 e2 in 
      Comma (e1', e2'), next_fun_annots', []

    | VarDec vars -> 
      let vdecls', next_fun_annots' = f_var_decl vars [] next_fun_annots in 
      (* Printf.printf "I processed a vardec. found_fun_call:%b\n" found_fun_call; *)
      VarDec vdecls', [], next_fun_annots' 

    | RegExp _  -> raise (Failure "construct not supported yet")
    (* statements *) 
    
    | Script (b, es) -> 
      (* Printf.printf "I got a ****SCRIPT*** BABY!!!!\n"; *)
      let es' = 
        List.map 
          (fun e -> 
            let e', next_fun_annot' = ground_fun_annotations [] e in 
            let e'' = add_more_annots e' next_fun_annot' in 
            e'') es in 
      Script (b, es'), [], []

    | Block es -> 
      (* Printf.printf "I got a ****BLOCK*** BABY!!!!\n"; *)
      (* Printf.printf "ground_fold_annotations I found a block statement!!!\n"; *)
      let es' = List.map 
        (fun e -> 
          let e', next_fun_annot' = ground_fun_annotations [] e in 
          let e'' = add_more_annots e' next_fun_annot' in 
          e'') es in 
      Block es', [], []
    
    | Skip -> Skip, [], next_fun_annots

    | If (e, s1, s2) -> 
      let e'  = f_im_done next_fun_annots e in 
      let s1' = f_im_done [] s1 in 
      let s2' = f_im_done_optional [] s2 in
      (**)
      If (e', s1', s2'), [], []

    | While (e,s) ->
      let e' = f_im_done [] e in 
      let s' = f_im_done [] s in    
      While (e', s'), [], next_fun_annots

    | DoWhile (s, e) ->
      let s' = f_im_done [] s in
      let e' = f_im_done [] e in 
      DoWhile (s', e'), [], next_fun_annots

    | Return e -> 
      let e', next_fun_annots' = f_optional e next_fun_annots in 
      Return e', [], next_fun_annots'

    | Try (s1, None, s3) -> 
      let s1' = f_im_done [] s1 in
      let s3' = f_im_done_optional [] s3 in 
      Try (s1', None, s3'), [], next_fun_annots

    | Try (s1, Some (x, s2), s3) -> 
      let s1' = f_im_done [] s1 in
      let s2' = f_im_done [] s2 in
      let s3' = f_im_done_optional [] s3 in 
      Try (s1', Some (x, s2'), s3'), [], next_fun_annots

    | Throw e -> 
      let e', next_fun_annots' = ground_fun_annotations next_fun_annots e in
      Throw e', [], next_fun_annots' 

    | Continue lab -> Continue lab, [], next_fun_annots
    
    | Break lab -> Break lab, [], next_fun_annots

    | Label (lab, s) -> 
      let s' = f_im_done [] s in
      Label (lab, s'), [], next_fun_annots
    
    | For (e1, e2, e3, s) ->
      let e1' = f_im_done_optional [] e1 in 
      let e2' = f_im_done_optional [] e2 in 
      let e3' = f_im_done_optional [] e3 in 
      let s'  = f_im_done [] s in 
      For (e1', e2', e3', s'), [], next_fun_annots
    
    | Switch (e, s_cases) -> 
      let e' = f_im_done [] e in 
      let s_cases' = f_cases s_cases in 
      Switch (e', s_cases'), [], next_fun_annots
    
    | ForIn (e1, e2, s) -> 
      let e1' = f_im_done [] e1 in 
      let e2' = f_im_done [] e2 in 
      let s'  = f_im_done [] s in 
      ForIn (e1', e2', s'), [], next_fun_annots
    
    | With (e, s) -> 
      let e' = f_im_done [] e in 
      let s' = f_im_done [] s in 
      With (e', s'), [], next_fun_annots

    | Debugger -> Debugger, [], next_fun_annots in 
  
  let new_exp = 
    match new_exp_stx with 
    | New (e1, e2s) | Call (e1, e2s) ->
      (* Printf.printf "In the pooooor function call with %d propagated folds and %d original folds!!!!\n" 
      (List.length folds) (List.length  cur_folds); *)
      { exp_offset = e.exp_offset; exp_stx = new_exp_stx; exp_annot = rest_annots @ prev_folds @ folds } 

    | FunctionExp (b, f_name, args, fb) | Function (b, f_name, args, fb)  -> 
      (* Printf.printf "I didn't propagate shit. but perhaps my submodules did. Here is the potentially new me:\n%s\n"
      (Pretty_print.string_of_exp true new_e); *)
      { exp_offset = e.exp_offset; exp_stx = new_exp_stx; exp_annot = rest_annots @ specs @ prev_specs } 

    | _ -> 
     (* Printf.printf "I am in the case in which I am deleting annotations from the node. I am deleting %d annotations and %d will remain\n"
      (List.length (folds @ prev_folds @ specs @ prev_specs)) (List.length rest_annots); *)
      
    { exp_offset = e.exp_offset; exp_stx = new_exp_stx; exp_annot = rest_annots @ fun_annots_to_reinclude } 
    (* Printf.printf "Here is the new exp withouth the folds that were deleted:\n%s\n" (Pretty_print.string_of_exp true new_e); *) in 
  new_exp, next_fun_annots'
      

let pop_relevant_logic_annots_stmt e = 
	let annots = e.Parser_syntax.exp_annot in 
	let folds, others = List.partition (fun annot -> annot.annot_type == Parser_syntax.Fold) annots in 
	let unfolds, others = List.partition (fun annot -> annot.annot_type == Parser_syntax.Unfold) others in  
	let invariant, others = List.partition (fun annot -> annot.annot_type == Parser_syntax.Invariant) others in
	let callspecs, others = List.partition (fun annot -> annot.annot_type = Parser_syntax.CallSpec) others in 
	let asserts, others = List.partition (fun annot -> annot.annot_type = Parser_syntax.Assert) others in 
	
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
			let relevant_logic_annots = parse_logic_annots (asserts @ unfolds @ folds @ callspecs) in 
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
			if ((annot.annot_type == Parser_syntax.Fold) || (annot.annot_type == Parser_syntax.Unfold) || (annot.annot_type == Parser_syntax.Assert)) then (
				let logic_cmd_str = annot.annot_formula in 
				let logic_cmd_pred = JSIL_Utils.js_assertion_of_string logic_cmd_str in
				loop rest ((annot.annot_type, logic_cmd_pred) :: fold_unfold_cmds) invariant
			) else if (annot.annot_type == Parser_syntax.Invariant) then (
				loop rest fold_unfold_cmds invariant
			) else loop rest fold_unfold_cmds invariant in 
	loop annots [] None 





(********************************************)
(********************************************)
(***     Char offsets to Line offsets     ***)
(********************************************)
(********************************************)


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



(********************************************)
(********************************************)
(***     Early Errors                     ***)
(********************************************)
(********************************************)


let test_expr_eval_arguments_assignment exp =
  List.exists (fun it -> it = "eval" || it = "arguments") (get_all_assigned_declared_identifiers exp)

let test_early_errors e =
  if test_func_decl_in_block e then raise (EarlyError "Function declaration in statement position or use of `with`");
  if test_expr_eval_arguments_assignment e then raise (EarlyError "Expression assigns to `eval` or `arguments`.")

