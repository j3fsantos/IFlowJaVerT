open Pulp_Logic
open Pulp_Logic_Utils
open Pulp_Procedure
open Pulp_Syntax_Print
open Pulp_Syntax
open Pulp_Translate_Aux

let dummy_exp = (Literal Undefined)

let get_value_fn = string_of_spec_fun_id (GetValue dummy_exp)

let get_value_spec param ctx =
  let pre_not_a_ref = Star [not_type_of_mref_f param; not_type_of_vref_f param] in
  
  let v = Le_Var (fresh_a()) in
  
  let pre_vref_obj = Star [
    type_of_vref_f param; 
    type_of_obj_f (Le_Base (Le_PVar param));
    NEq (Le_Base (Le_PVar param), Le_Literal (LLoc Lg));
    Heaplet (Le_Base (Le_PVar param), Le_Field (Le_PVar param), v) 
  ] in 
  
  let l = Le_Var (fresh_e()) in
  let post_vref_obj = combine pre_vref_obj
    (Star [
      REq l;
      proto_heaplet_f l (Le_Literal (LLoc Lrep));
      class_heaplet_f l "Error"
    ]) in
  
  [(mk_spec_with_excep pre_not_a_ref [combine pre_not_a_ref (REq (Le_PVar param))] [false_f]);
   (mk_spec_with_excep pre_vref_obj [false_f] [combine pre_vref_obj post_vref_obj])] 
  
let get_value_fb () =
  let param = "x" in
  let ctx = create_ctx [] in
  let bd = translate_gamma (Var param) ctx.return_var ctx.throw_var ctx.label_throw in
  make_function_block_with_spec get_value_fn bd [param] ctx (get_value_spec param ctx)

let get_env_spec env = 
  let env = AllFunctions.add get_value_fn get_value_fb in
  env


  
  
