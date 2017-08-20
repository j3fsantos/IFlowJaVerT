open JSIL_Syntax

(** Types and operations to work with JSIL logic predicates. *)

(** Normalises a full collection of predicate declarations. *)
val normalise : (string, jsil_logic_predicate) Hashtbl.t -> (string, normalised_predicate) Hashtbl.t
(** Every predicate declaration for the same predicate is joined in a single normalised predicate.
    In addition, literal parameters are replaced with fresh logical variables which are, in turn,
		constrained in the definitions of the predicate. A simple check is made to detect whether the
		predicates are recursive or not (even mutually recursive). *)

(** Replaces the non-recursive predicate occurrences in the assertion by its definition. *)
val auto_unfold : (string, normalised_predicate) Hashtbl.t -> jsil_logic_assertion -> jsil_logic_assertion list
(** Given a collection of normalised predicates, an assertion is generated for each
    possible combination of unfoldings. *)

(** Returns a string from a normalised predicate. *)
(* val to_string : normalised_predicate -> string *)
(** Useful for debugging. *)

val string_of_normalised_predicates : (string, normalised_predicate) Hashtbl.t -> string


val string_of_normalised_predicate :  (normalised_predicate) -> string

val string_of_normalised_predicates : ((string, normalised_predicate) Hashtbl.t) -> string
