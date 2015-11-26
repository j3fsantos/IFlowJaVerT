open OUnit
open Tests_Utils
open Pulp_Procedure
open Pulp_Logic
open Pulp_Logic_Utils
open Pulp_Syntax

let test_js_program_template name f fs =
  List.iteri (fun i s -> check_single_spec name f fs s i "tests/dot/evaluation/") f.func_spec
  
  
(* ch08/8.7/8.7.2/8.7.2-1-s.js *)  
let test_8_7_2_1_s () =
  (* Simplifying the program to exclude eval for a moment *)
  let js_program = "_8_7_2_1 = 11;" in
    
  let p_exp, p_env = get_pexp js_program in
  
  let ls = Le_Var (fresh_e ()) in
  let l = Le_Var (fresh_e ()) in
  let pi = proto_pred_f ls (Le_Literal (LLoc Lg)) (Le_Literal (String "_8_7_2_1")) l (Le_Literal Empty) in
  
  let lerror = Le_Var (fresh_e()) in
  let post_ref_exception = combine empty_f
    (Star [
      REq lerror;
      proto_heaplet_f lerror (Le_Literal (LLoc Lrep));
      class_heaplet_f lerror "Error"
    ]) in

  let p_exp = AllFunctions.mapi (fun id fb ->
    match id with
      | "main" -> 
        let undefined = Le_Var (fresh_e()) in
        let proto = Le_Var (fresh_e()) in
        let pre = Pulp_Logic_Utils.combine
          pi 
          (Star [
          Pulp_Logic.proto_heaplet_f (Le_Literal (LLoc Lg)) proto;
          Heaplet (Le_Literal (LLoc Lg), Le_Literal (String "undefined"), undefined);
        ]) in
        let spec_main = mk_spec_with_excep pre [false_f] [post_ref_exception] in
        {fb with func_spec = [spec_main]}
      | _ -> fb
  ) p_exp in
  
  
  
  Printf.printf "Specs %s" (String.concat "\n" (List.map (fun (id, fb) -> Printf.sprintf "%s : %s" id (Pulp_Logic_Print.string_of_spec_pre_post_list fb.func_spec "\n")) (AllFunctions.bindings p_exp)));
  
  AllFunctions.iter (fun id f -> test_js_program_template "test_8_7_2_1_s" f p_exp) p_exp
  
 let suite = "Testing_Evaluation_Examples" >:::
  [ "test_8_7_2_1_s" >:: test_8_7_2_1_s ]