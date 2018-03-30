open WISL_Syntax

let float_of_num n = match n with
  | Float f -> f
  | Int i -> float_of_int i