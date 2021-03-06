(* ./src/pulp/syntax/pulp_Procedure.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Pulp_Syntax

type function_id = string

type ctx_variables = {
     func_id : function_id;
     fun_bindings : variable list
  }
  
let make_ctx_vars fid vars = 
  { 
    func_id = fid;
    fun_bindings = vars
  }
  
  type translation_ctx = { (* Special constants for throws and returns *)
    env_vars : ctx_variables list; 
    return_var : variable;
    throw_var : variable;
    label_entry : label;
    label_return : label;
    label_throw : label;
    label_continue : (string * label) list;
    label_break : (string * label) list; 
		stmt_return_var : variable; 
  }
  
let create_ctx env =
  {
     env_vars = env;
     return_var = fresh_r ();
     throw_var = fresh_r ();
     label_entry = "entry." ^ fresh_r (); 
     label_return = "return." ^ fresh_r ();
     label_throw = "throw." ^ fresh_r ();
     label_continue = [];
     label_break = []; 
		 stmt_return_var = fresh_r (); 
  }
  
type procedure_type = 
  | Procedure_User
  | Procedure_Builtin
  | Procedure_Spec
  
type function_block = { 
    func_type : procedure_type;
    func_name : codename;
    func_body : statement list;
    func_params : formal_param list;
    func_ctx : translation_ctx;
    func_spec : Pulp_Logic.spec_pre_post list
		
}


let make_function_block_with_spec ft fn fb fparams ctx spec = {
    func_type = ft;
    func_name = fn;
    func_body = fb;
    func_params = fparams;
    func_ctx = ctx;
    func_spec = spec
  }
  
let make_function_block ft fn fb fparams ctx = {
    func_type = ft;
    func_name = fn;
    func_body = fb;
    func_params = fparams;
    func_ctx = ctx;
    func_spec = []
  }
  
module AllFunctions = Map.Make ( 
  struct 
    type t = function_id
    let compare = compare
  end
)