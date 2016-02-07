(* ./src/pulp/simplifications/simp_Main.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Pulp_Syntax
open Pulp_Procedure
open Basic_Blocks
open Reaching_Defs
open Spec_Functions

let basic_block_simplifications cfg ctx =
  let cfg_bb = transform_to_basic_blocks_from_cfg cfg ctx in
  remove_unreachable cfg_bb;
  transform_to_basic_blocks cfg_bb ctx;
  remove_unreachable cfg_bb;
  remove_unnecessary_goto_label cfg_bb ctx.label_throw ctx.label_return;
  remove_empty_blocks cfg_bb;
  cfg_bb
  
let constant_propagation cfg fb option =
  List.iter (fun n -> const_prop_node cfg n) (CFG_BB.nodes cfg);
  constant_propagation cfg;
  copy_propagation cfg; (* TODO: Do I need constant_progation if I have copy_propagation? *)
  type_simplifications cfg fb.func_params fb.func_type;
  simplify_guarded_gotos cfg;  
  simplify_spec_functions cfg option;
  remove_unreachable cfg;
  remove_empty_blocks cfg;
  transform_to_basic_blocks cfg fb.func_ctx;
  remove_unnecessary_goto_label cfg fb.func_ctx.label_throw fb.func_ctx.label_return
  
let simplify exp option =
  let cfg = Control_Flow.program_to_cfg exp in
  
  let cfg_bbs = AllFunctions.mapi (fun name cfg ->
    let fb = AllFunctions.find name exp in
    
    let cfg_bb = basic_block_simplifications cfg fb.func_ctx in
    
    constant_propagation cfg_bb fb option;
    constant_propagation cfg_bb fb option;
        
    dead_code_elimination cfg_bb fb.func_ctx.throw_var fb.func_ctx.return_var;
    
    cfg_bb
  ) cfg in
    
  let simplified_exp = AllFunctions.mapi (fun name fb -> 
    let cfg_bb = AllFunctions.find name cfg_bbs in
    
    {fb with func_body = cfg_to_fb cfg_bb fb.func_ctx.label_throw fb.func_ctx.label_return} 
   ) exp in
  
  simplified_exp
  