open WISL_Syntax

let float_of_num n = match n with
  | Float f -> f
  | Int i -> float_of_int i
  
let add_spec f pre post =
  let specs = Some { pre; post } in
  let { name; params; body; spec; return_expr } = f in
  { name; params; body; return_expr; spec = specs}
  
let empty_metadata = {
  precmds = [];
  postcmds = [];
  invariant = None;
}