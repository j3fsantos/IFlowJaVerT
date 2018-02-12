(****************************************
 * Interface for JSIL Symbolic FV-lists *
*****************************************)

type t 

type field_name  = JSIL_Syntax.jsil_logic_expr
type field_value = Permission.t * JSIL_Syntax.jsil_logic_expr

val add         : field_name  -> field_value -> t -> t
val copy        : t -> t
val empty       : t
val field_names : t -> field_name list
val fold        : (field_name -> field_value -> 'a -> 'a) -> t -> 'a -> 'a
val get         : field_name -> t -> field_value option
val get_first   : (field_name -> bool) -> t -> (field_name * field_value) option
val is_empty    : t -> bool
val iter        : (field_name -> field_value -> unit) -> t -> unit
val partition   : (field_name -> field_value -> bool) -> t -> (t * t)
val remove      : field_name -> t -> t
val str         : t -> string
val union       : t -> t -> t

val lvars : t -> CCommon.SS.t
val alocs : t -> CCommon.SS.t

val assertions             : JSIL_Syntax.jsil_logic_expr -> t -> JSIL_Syntax.jsil_logic_assertion list
val substitution           : JSIL_Syntax.substitution -> bool -> t -> t
val selective_substitution : JSIL_Syntax.substitution -> bool -> t -> t