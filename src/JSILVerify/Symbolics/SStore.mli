(*********************************
 * Interface for Symbolic stores *
**********************************)

type t 

val copy       : t -> t
val domain     : t -> CCommon.SS.t
val get        : t -> string -> JSIL_Syntax.jsil_logic_expr option
val get_unsafe : t -> string -> JSIL_Syntax.jsil_logic_expr
val init       : string list -> JSIL_Syntax.jsil_logic_expr list -> t
val mem        : t -> string -> bool
val partition  : t -> (JSIL_Syntax.jsil_logic_expr -> bool) -> string list * string list
val projection : t -> string list -> t
val put        : t -> string -> JSIL_Syntax.jsil_logic_expr -> unit
val remove     : t -> string -> unit
val str        : t -> string

val iter       : t -> (string -> JSIL_Syntax.jsil_logic_expr -> unit) -> unit
val fold       : t -> (string -> JSIL_Syntax.jsil_logic_expr -> 'a -> 'a) -> 'a -> 'a
val filter     : t -> (string -> JSIL_Syntax.jsil_logic_expr -> JSIL_Syntax.jsil_logic_expr option) -> unit

val vars       : t -> CCommon.SS.t
val lvars      : t -> CCommon.SS.t
val clocs      : t -> CCommon.SS.t
val alocs      : t -> CCommon.SS.t
val unifiables : t -> CCommon.SS.t

val assertions            : t -> JSIL_Syntax.jsil_logic_assertion list
val substitution          : JSIL_Syntax.substitution -> bool -> t -> t
val substitution_in_place : JSIL_Syntax.substitution -> t -> unit

val is_well_formed : t -> bool