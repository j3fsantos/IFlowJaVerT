(* ./src/pulp/syntax/lifting.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

type closure_type = { 
    closure_id : codename;
    closure_params : formal_param list;
    closure_env : (variable list) list;
    closure_body : Parser_Syntax.expr;
    func_ctx : translation_ctx;
}

type ES5_Core_Closures =
  | JS_EXPR of Parser_Syntax.expr
  | Closure of closure_type