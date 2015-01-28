open Pulp_Syntax
open Basic_Blocks
open Reaching_Defs

let basic_block_simplifications cfg ctx =
  let cfg_bb = transform_to_basic_blocks_from_cfg cfg in
  remove_unreachable cfg_bb;
  transform_to_basic_blocks cfg_bb;
  remove_unreachable cfg_bb;
  remove_unnecessary_goto_label cfg_bb ctx.label_throw ctx.label_return;
  remove_empty_blocks cfg_bb;
  cfg_bb
  
let constant_propagation cfg ctx =
  List.iter (fun n -> const_prop_node cfg n) (CFG_BB.nodes cfg);
  constant_propagation cfg;
  simplify_guarded_gotos cfg;  
  remove_unreachable cfg;
  remove_empty_blocks cfg;
  transform_to_basic_blocks cfg;
  remove_unnecessary_goto_label cfg ctx.label_throw ctx.label_return
  
let simplify exp =
  let cfg = Control_Flow.program_to_cfg exp in
  
  let cfg_bbs = AllFunctions.mapi (fun name cfg ->
    let fb = AllFunctions.find name exp in
    
    let cfg_bb = basic_block_simplifications cfg fb.func_ctx in
    
    constant_propagation cfg_bb fb.func_ctx;
    constant_propagation cfg_bb fb.func_ctx;
        
    dead_code_elimination cfg_bb fb.func_ctx.throw_var fb.func_ctx.return_var;
    cfg_bb
  ) cfg in
    
  let simplified_exp = AllFunctions.mapi (fun name fb -> 
    let cfg_bb = AllFunctions.find name cfg_bbs in
    
    {fb with func_body = cfg_to_fb cfg_bb fb.func_ctx.label_throw fb.func_ctx.label_return} 
   ) exp in
  
  simplified_exp
  