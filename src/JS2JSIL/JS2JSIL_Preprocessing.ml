open Common
open Parser_syntax
open Utils
open Batteries
open JS2JSIL_Constants
open JS_Utils

exception CannotHappen
exception No_Codename
exception EarlyError of string


(********************************************)
(********************************************)
(***         Compilation Tables           ***)
(********************************************)
(********************************************)

let string_of_vtf_tbl (var_tbl : var_to_fid_tbl_type) =
  let var_tbl_str =
    Hashtbl.fold
      (fun v fid ac ->
        let v_fid_pair_str = v ^ ": " ^ fid in
        if (ac = "")
          then v_fid_pair_str
          else ac ^ ", " ^ v_fid_pair_str)
      var_tbl
      "" in
  "[ " ^ var_tbl_str ^ "]"


let rec string_of_cc_tbl (cc_tbl : cc_tbl_type)  =
  Hashtbl.fold
    (fun f_id f_tbl ac ->
      let f_tbl_str : string = string_of_vtf_tbl f_tbl in
      let f_str = f_id ^ ": " ^ f_tbl_str ^ "\n" in
      ac ^ f_str)
    cc_tbl
    ""

let update_fun_tbl
  (fun_tbl        : pre_fun_tbl_type)
  (f_id           : string)
  (f_args         : string list)
  (f_body         : Parser_syntax.exp option)
  (annotations    : Parser_syntax.annotation list)
  (var_to_fid_tbl : var_to_fid_tbl_type)
  (vis_list       : string list) =
  (* let fun_spec, f_rec = process_js_logic_annotations f_id f_args annotations Requires Ensures EnsuresErr var_to_fid_tbl vis_list in *)
  Hashtbl.replace fun_tbl f_id (f_id, f_args, f_body, (annotations, vis_list, var_to_fid_tbl))


let update_cc_tbl (cc_tbl : cc_tbl_type) (f_parent_id : string) (f_id : string) (f_vars : string list) =
  let f_parent_var_table = get_scope_table cc_tbl f_parent_id in
  let new_f_tbl = Hashtbl.create 101 in
  Hashtbl.iter
    (fun x x_f_id -> Hashtbl.add new_f_tbl x x_f_id)
    f_parent_var_table;
  List.iter
    (fun v -> Hashtbl.replace new_f_tbl v f_id)
    f_vars;
  Hashtbl.add cc_tbl f_id new_f_tbl;
  new_f_tbl


let update_cc_tbl_single_var_er (cc_tbl : cc_tbl_type) (f_parent_id : string) (f_id : string) (x : string) =
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
  Hashtbl.add cc_tbl f_id new_f_tbl;
  new_f_tbl


let get_vis_list_index vis_list fid =
  let rec loop cur vis_list =
    match vis_list with
    | [] -> raise (Failure "get_vis_list_index: DEATH")
    | cur_fid :: rest ->
      if (cur_fid = fid)
        then cur
        else loop (cur + 1) rest in
  loop 0 vis_list


(********************************************)
(********************************************)
(***         Annotations                  ***)
(********************************************)
(********************************************)

let update_annotation annots atype new_value =
  let old_removed = List.filter (fun annot -> annot.annot_type <> atype) annots in
  let annot = {annot_type = atype; annot_formula = new_value} in
  annot :: old_removed


let is_logic_cmd_annot annot = (annot.annot_type = Parser_syntax.Tactic)

let is_spec_annot annot =
  let annot_type = annot.annot_type in
  (annot_type = Parser_syntax.Id) || (annot_type = Parser_syntax.Requires) ||
    (annot_type = Parser_syntax.Ensures) || (annot_type = Parser_syntax.EnsuresErr)


let get_top_level_annot e =
  match e.Parser_syntax.exp_stx with
  | Script (_, les) ->
    let first_le = List.nth les 0 in
    let annot = first_le.Parser_syntax.exp_annot in
    annot
  | _ -> []



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


let rec add_codenames exp =
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

  js_map f_m exp



(********************************************)
(********************************************)
(***         Closure Clarification        ***)
(********************************************)
(********************************************)


let closure_clarification
    (cc_tbl       : JS2JSIL_Constants.cc_tbl_type)
    (fun_tbl      : JS2JSIL_Constants.pre_fun_tbl_type)
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
          let new_visited_funs = visited_funs @ [ new_f_id ] in
          update_fun_tbl fun_tbl new_f_id args (Some fb) cur_annot new_f_tbl new_visited_funs;
          Hashtbl.replace vis_tbl new_f_id new_visited_funs;
          Some (new_f_id, new_visited_funs)
        | Some f_name ->
          let new_f_id = get_codename e in
          let new_f_id_outer = new_f_id ^ "_outer" in
          let _ = update_cc_tbl_single_var_er cc_tbl f_id new_f_id_outer f_name in
          let new_f_tbl = update_cc_tbl cc_tbl new_f_id_outer new_f_id (get_all_vars_f fb args) in
          update_fun_tbl fun_tbl new_f_id args (Some fb) cur_annot new_f_tbl (visited_funs @ [ new_f_id_outer; new_f_id ]);
          Hashtbl.replace vis_tbl new_f_id (visited_funs @ [ new_f_id_outer; new_f_id ]);
          Some (new_f_id, (visited_funs @ [ new_f_id_outer; new_f_id ])))
      | Function (_, f_name, args, fb) ->
        let new_f_id = get_codename e in
        let new_f_tbl = update_cc_tbl cc_tbl f_id new_f_id (get_all_vars_f fb args) in
        update_fun_tbl fun_tbl new_f_id args (Some fb) cur_annot new_f_tbl (visited_funs @ [ new_f_id ]);
        Hashtbl.replace vis_tbl new_f_id (visited_funs @ [ new_f_id ]);
        Some (new_f_id, (visited_funs @ [ new_f_id ]))
      | Try (_, Some (_, _), _)  -> None
      | _     -> state) in

  let rec f_ac e state prev_state ac =
    match prev_state with
    | None -> ac
    | Some (f_id, visited_funs) ->
      match e.exp_stx with
      | Try (e1, Some (x, e2), e3) ->
        let f = js_fold f_ac f_state in
        let _ = f prev_state e1 in
        let _ = Option.map (f prev_state) e3 in
        let new_f_id = get_codename e in
        update_cc_tbl_single_var_er cc_tbl f_id new_f_id x;
        f (Some (new_f_id, (visited_funs @ [ new_f_id ]))) e2
      | _ -> [] in
  js_fold f_ac f_state (Some (f_id, visited_funs)) exp



(********************************************)
(********************************************)
(***         Folds and Unfolds            ***)
(********************************************)
(********************************************)

(*

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
  js_map f_m e
*)


let rec propagate_annotations e =

  let f_state state exp =
    let _, prev_annots = state in
    match exp.exp_stx with
    (* Propagate the specs *)
    | Call _ | New _ ->
      let spec_annots = (List.filter is_spec_annot prev_annots) @ (List.filter is_spec_annot exp.exp_annot) in
      false, spec_annots
    (* Propagate the lcmds *)
    | Function _ | FunctionExp _ ->
      let lcmd_annots = (List.filter is_logic_cmd_annot prev_annots) @ (List.filter is_logic_cmd_annot exp.exp_annot) in
      false, lcmd_annots
    (* Propagate the lcmds and specs *)
    | _ ->
      let spec_annots = List.filter is_spec_annot exp.exp_annot in
      let lcmd_annots = List.filter is_logic_cmd_annot exp.exp_annot in
      if (((List.length (spec_annots)) + (List.length (lcmd_annots))) > 0)
        then Printf.printf "I found the annots %s in %s\n"
                (Pretty_print.string_of_annots (spec_annots @ lcmd_annots)) (Pretty_print.string_of_exp_syntax_1 exp.exp_stx true);
      false, (prev_annots @ spec_annots @ lcmd_annots) in

  let f_transform exp new_exp_stx state_i state_f =
    let no_propagation_i, prev_annots         = state_i in
    let no_propagation_f, annots_to_propagate = state_f in

    let annots_to_stay =
      match exp.exp_stx with
      (* everything stays except for the specs *)
      | Call _ | New _ ->
        let f annot = not (is_spec_annot annot) in
        (List.filter f prev_annots) @ (List.filter f exp.exp_annot)
      (* everything stays except for the lcmds *)
      | Function _ | FunctionExp _ ->
        let f annot = not (is_logic_cmd_annot annot) in
        let ret = (List.filter f prev_annots) @ (List.filter f exp.exp_annot) in
        (* Printf.printf "I am transforming the function literal %s annotating it with: %s\n"
          (Pretty_print.string_of_exp true exp) (Pretty_print.string_of_annots ret); *)
        ret
      (* everything stays except specs and lcmds *)
      | _ ->
        let f annot = not (is_spec_annot annot || is_logic_cmd_annot annot) in
         (List.filter f prev_annots) @ (List.filter f exp.exp_annot) in

    let annots_to_stay, annots_to_propagate =
      if (no_propagation_i) then ((annots_to_propagate @ annots_to_stay), []) else annots_to_stay, annots_to_propagate in

    (* Printf.printf "I found the following annots to stay: %s and the following annots to propagate: %s in the expression %s\n"
      (Pretty_print.string_of_annots annots_to_stay)
      (Pretty_print.string_of_annots annots_to_propagate)
      (Pretty_print.string_of_exp_syntax_1 new_exp_stx true); *)

    { exp with exp_stx = new_exp_stx; exp_annot = annots_to_stay }, (no_propagation_f, annots_to_propagate) in

  let init_state = (true, []) in

  js_map_with_state f_transform f_state init_state init_state e



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


(**************************************************)
(**************************************************)
(***   Translation of logic annotations         ***)
(**************************************************)
(**************************************************)

let get_predicate_defs_from_annots annots : JSLogic.js_logic_predicate list =
  let pred_def_annots = List.filter (fun annot -> annot.annot_type == Parser_syntax.Pred) annots in
  let pred_defs = List.map (fun pred_def -> JSIL_Syntax_Utils.js_logic_pred_def_of_string ("pred " ^ pred_def.annot_formula)) pred_def_annots in
  pred_defs


let get_only_specs_from_annots annots : JSLogic.js_spec list =
  let only_specs_annots = List.filter (fun annot -> annot.annot_type == Parser_syntax.OnlySpec) annots in
  List.map (fun only_spec -> JSIL_Syntax_Utils.js_only_spec_from_string ("js_only_spec " ^ only_spec.annot_formula)) only_specs_annots


let parse_annots_formulae annots =
  let lcmds = List.map
    (fun annot ->
      let lcmds = JSIL_Syntax_Utils.js_logic_commands_of_string annot.annot_formula in
      lcmds) annots in
  List.concat lcmds

let translate_lannots_in_exp cc_tbl vis_tbl fun_tbl inside_stmt_compilation e =
  let is_e_expr = not (is_stmt e) in
  if (is_e_expr && inside_stmt_compilation) then ([], []) else (
    let lcmds   = parse_annots_formulae (List.filter is_logic_cmd_annot e.exp_annot) in
    let t_lcmds = List.concat (List.map (JSLogic.js2jsil_logic_cmd cc_tbl vis_tbl fun_tbl) lcmds) in

    if ((List.length t_lcmds) > 0)
      then (
        let t_lcmds_str = List.map JSIL_Print.string_of_lcmd t_lcmds in
        let t_lcmds_str = String.concat "; " t_lcmds_str in
        Printf.printf "translate_lannots_in_exp. got the following commands: %s\n" t_lcmds_str
      );

    let rec fold_partition lcmds lcmds_so_far =
      (match lcmds with
      | []                           -> (List.rev lcmds_so_far), []
      | (JSIL_Syntax.Fold a) :: rest -> (List.rev lcmds_so_far), lcmds
      | lcmd :: rest                 -> fold_partition rest (lcmd :: lcmds_so_far)) in

    match e.exp_stx with
    | Call _ | New _ -> fold_partition t_lcmds []
    | _              -> t_lcmds, []
  )


let translate_invariant_in_exp
    (cc_tbl : cc_tbl_type) (vis_tbl : vis_tbl_type) (fun_tbl : pre_fun_tbl_type)
    (fid : string) (sc_var : string) (e : Parser_syntax.exp) : JSIL_Syntax.jsil_logic_assertion option =
  let invariant = List.filter (fun annot -> annot.annot_type == Parser_syntax.Invariant) e.exp_annot in
  match invariant with
  | _ :: _ :: _   -> raise (Failure "DEATH: No more than one invariant per command")
  | [ ]           -> None
  | [ invariant ] ->
    let a = JSIL_Syntax_Utils.js_assertion_of_string invariant.annot_formula in
    Some (JSLogic.js2jsil_tactic_assertion cc_tbl vis_tbl fun_tbl fid sc_var a)


let translate_single_func_specs
      (cc_tbl              : cc_tbl_type)
      (vis_tbl             : vis_tbl_type)
      (fun_tbl             : pre_fun_tbl_type)
      (fid                 : string)
      (fun_args            : string list)
      (annotations         : Parser_syntax.annotation list)
      (requires_flag       : Parser_syntax.annotation_type)
      (ensures_normal_flag : Parser_syntax.annotation_type)
      (ensure_err_flag     : Parser_syntax.annotation_type) =
  (* Printf.printf "Inside process_js_logic_annotations. function: %s.\n\nAnnotations: \n%s\n\n" fid (Pretty_print.string_of_annots annotations); *)

  let var_to_fid_tbl : var_to_fid_tbl_type = get_scope_table cc_tbl fid in
  let vis_list = get_vis_list vis_tbl fid in

  (*
  let annot_types_str : string = String.concat ", " (List.map (fun annot -> Pretty_print.string_of_annot_type annot.annot_type) annotations) in
  Printf.printf "annot types: %s\n\n" annot_types_str; *)

  let preconditions  = List.filter (fun annotation -> annotation.annot_type = requires_flag) annotations in
  let postconditions = List.filter (fun annotation -> (annotation.annot_type = ensures_normal_flag) || (annotation.annot_type = ensure_err_flag)) annotations in

  (* Printf.printf "number of preconditions: %d. number of postconditions: %d\n" (List.length preconditions) (List.length postconditions); *)

  let single_specs =
    if ((List.length preconditions) <> (List.length postconditions)) then (
      Printf.printf "WARNING: In %s, preconditions do NOT match postconditions.\n" fid;
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
      let pre_js  = JSIL_Syntax_Utils.js_assertion_of_string pre_str in
      let post_js = JSIL_Syntax_Utils.js_assertion_of_string post_str in
      (* Printf.printf "I managed to parse the js assertions\n"; *)

      let pre_jsil, post_jsil = JSLogic.js2jsil_single_spec pre_js post_js cc_tbl vis_tbl fun_tbl fid in
      let new_spec  = JSIL_Syntax.create_single_spec pre_jsil [ post_jsil ] ret_flag in
      new_spec)
    preconditions
    postconditions in


  let fun_spec = if ((List.length single_specs) > 0)
    then Some (JSIL_Syntax.create_jsil_spec fid fun_args single_specs false)
    else None in
  fun_spec


(**
  * Populates the new fun_tbl given the old fun_tbl
  * by compiling the specs in the old fun_tbl
*)
let translate_specs
    (cc_tbl      : cc_tbl_type)
    (vis_tbl     : vis_tbl_type)
    (old_fun_tbl : JS2JSIL_Constants.pre_fun_tbl_type)
    (new_fun_tbl : JS2JSIL_Constants.fun_tbl_type) =
  Hashtbl.iter
    (fun f_id (f_id, f_args, f_body, (annotations, _, _)) ->

      let non_main_args = JS2JSIL_Constants.var_scope :: (JS2JSIL_Constants.var_this :: f_args) in
      let fun_specs =
        if (not (f_id = JS2JSIL_Constants.var_main))
          then translate_single_func_specs cc_tbl vis_tbl old_fun_tbl f_id non_main_args annotations Requires Ensures EnsuresErr
          else translate_single_func_specs cc_tbl vis_tbl old_fun_tbl f_id [] annotations TopRequires TopEnsures TopEnsuresErr in
      Hashtbl.add new_fun_tbl f_id (f_id, f_args, f_body, fun_specs))
    old_fun_tbl


let rec get_predicate_definitions exp =
  let f_ac exp state prev_state ac =
    let new_pred_defs : JSLogic.js_logic_predicate list = (get_predicate_defs_from_annots exp.Parser_syntax.exp_annot) in
     new_pred_defs @ ac in
  js_fold f_ac (fun x y -> y) true exp


let translate_only_specs cc_tbl old_fun_tbl fun_tbl vis_tbl js_only_specs =
  let only_specs = Hashtbl.create medium_tbl_size in
  List.iter
  (fun { JSLogic.js_spec_name; JSLogic.js_spec_params; JSLogic.js_proc_specs } ->
    Hashtbl.replace vis_tbl js_spec_name [ js_spec_name; main_fid ];
    let proc_specs = List.map (fun { JSLogic.js_pre; JSLogic.js_post; JSLogic.js_ret_flag } ->
      let pre, post = JSLogic.js2jsil_single_spec  js_pre  js_post cc_tbl vis_tbl (Hashtbl.create 0) js_spec_name in
        { JSIL_Syntax.pre = pre; JSIL_Syntax.post = [ post ]; JSIL_Syntax.ret_flag = js_ret_flag }) js_proc_specs in
    let spec = { JSIL_Syntax.spec_name = js_spec_name; JSIL_Syntax.spec_params = [JS2JSIL_Constants.var_scope; JS2JSIL_Constants.var_this] @ js_spec_params; JSIL_Syntax.proc_specs = proc_specs; JSIL_Syntax.previously_normalised = false } in
    Hashtbl.replace only_specs  js_spec_name spec;
    Hashtbl.replace cc_tbl      js_spec_name (Hashtbl.create 1);
    Hashtbl.replace old_fun_tbl js_spec_name (js_spec_name, js_spec_params, None, ([], [ js_spec_name; "main" ], Hashtbl.create 1));
    Hashtbl.replace fun_tbl     js_spec_name (js_spec_name, js_spec_params, None, Some spec);
  ) js_only_specs;
  only_specs



(********************************************)
(********************************************)
(***   Initial Preprocessing Function     ***)
(********************************************)
(********************************************)

let preprocess
  (cc_tbl      : cc_tbl_type)
  (fun_tbl     : fun_tbl_type)
  (vis_tbl     : vis_tbl_type)
  (e           : Parser_syntax.exp) =

  (* 0 - testing early errors                      *)
  test_early_errors e;

  (* 1 - propagating annotations                   *)
  print_debug (Printf.sprintf "AST before grounding the annotations:\n%s\n" (Pretty_print.string_of_exp true e));
  let e, _ = propagate_annotations e in
  print_debug (Printf.sprintf "AST after grounding annotations:\n%s\n" (Pretty_print.string_of_exp true e));

  (* 2 - obtaining and compiling only-specs        *)
  let top_annots = get_top_level_annot e in
  let js_only_specs = get_only_specs_from_annots top_annots in
  let old_fun_tbl : pre_fun_tbl_type = Hashtbl.create medium_tbl_size in
  let only_specs = translate_only_specs cc_tbl old_fun_tbl fun_tbl vis_tbl js_only_specs in

  (* 3 - Adding the main to the translation tables *)
  let main_tbl = Hashtbl.create medium_tbl_size in
  List.iter (fun v -> Hashtbl.replace main_tbl v main_fid) (get_all_vars_f e []);
  Hashtbl.add cc_tbl main_fid main_tbl;
  Hashtbl.add old_fun_tbl main_fid (main_fid, [], Some e, (top_annots, [ main_fid ], main_tbl));
  Hashtbl.add vis_tbl main_fid [ main_fid ];

  (* 4 - Add unique ids to function literals       *)
  let e = add_codenames e in

  (* 5 - Closure clarification                     *)
  closure_clarification cc_tbl old_fun_tbl vis_tbl main_fid [ main_fid ] e;

  (* 6 - Translate JS Specs                        *)
  translate_specs cc_tbl vis_tbl old_fun_tbl fun_tbl;

  (* 7 - Translate JS Predicate Definitions        *)
  let js_predicate_definitions : JSLogic.js_logic_predicate list = get_predicate_definitions e in
  let jsil_predicate_definitions =
    List.map (fun pred_def -> JSLogic.js2jsil_predicate_def pred_def cc_tbl vis_tbl old_fun_tbl) js_predicate_definitions in
  let predicates : (string, JSIL_Syntax.jsil_logic_predicate) Hashtbl.t = JSIL_Syntax.pred_def_tbl_from_list jsil_predicate_definitions in

  e, only_specs, predicates



let preprocess_eval
  (cc_tbl      : cc_tbl_type)
  (vis_tbl     : vis_tbl_type)
  (e           : Parser_syntax.exp)
  (fid_parent  : string)
  (params      : string list) =

  let offset_converter x = 0 in
  let fid                =
    if ((List.length params) > 0)
      then fresh_anonymous ()
      else fresh_anonymous_eval () in
  let pre_fun_tbl        = Hashtbl.create small_tbl_size in
  let fun_tbl            = Hashtbl.create small_tbl_size in

  let vislist =
    try fid :: (Hashtbl.find vis_tbl fid_parent)
      with _ -> raise (Failure (Printf.sprintf "Function %s not found in visibility table" fid_parent)) in

  (* 0 - testing early errors                      *)
  test_early_errors e;

  (* 1 - Add unique ids to function literals       *)
  let e : Parser_syntax.exp = add_codenames e in

  (* 2 - Adding the eval body to the translation tables *)
  update_cc_tbl cc_tbl fid_parent fid (get_all_vars_f e params);
  Hashtbl.add pre_fun_tbl fid (fid, [var_scope; var_this], Some e, ([], vislist, Hashtbl.create small_tbl_size));
  Hashtbl.add vis_tbl fid vislist;

  (* 3 - Closure clarification                     *)
  closure_clarification cc_tbl pre_fun_tbl vis_tbl fid vislist e;

  (* 4 - Translate Specs                           *)
  translate_specs cc_tbl vis_tbl pre_fun_tbl fun_tbl;

  e, fid, vislist, fun_tbl
