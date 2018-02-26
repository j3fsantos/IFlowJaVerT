(*************************************
 * Interface for Typing Environments *
**************************************)

type t

val copy : t -> t
val extend : t -> t -> unit
val filter : t -> (string -> bool) -> t
val filter_in_place : t -> (string -> bool) -> unit
val filter_vars : t -> CCommon.SS.t -> t
val filter_vars_in_place : t -> CCommon.SS.t -> unit
val get : t -> string -> Type.t option
val get_unsafe : t -> string -> Type.t 
val get_var_type_pairs : t -> (string * Type.t) list
val get_vars_of_type : t -> Type.t -> string list
val init : unit -> t
val mem : t -> string -> bool
val safe_extend : t -> t -> unit
val str : t -> string
val update : t -> string -> Type.t option -> unit
val weak_update : t -> string -> Type.t option -> unit

val iter : t -> (string -> Type.t -> unit) -> unit
val fold : t -> (string -> Type.t -> 'a -> 'a) -> 'a -> 'a

val vars : t -> CCommon.SS.t
val lvars : t -> CCommon.SS.t

val assertions : t -> JSIL_Syntax.jsil_logic_assertion
val substitution : t -> JSIL_Syntax.substitution -> bool -> t