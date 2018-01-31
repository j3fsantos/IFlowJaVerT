(** 
	JSIL Extensibility 
*)

type t = 
	| Extensible
	| NonExtensible
	[@@deriving show, compare]

let equal = [%compare.equal : t]

(** Print *)
let str (x : t) =
  match x with
	| Extensible    -> "extensible"
	| NonExtensible -> "non-extensible"

(** Print of an optional extensibility *)
let ostr (x : t option) = 
	Option.map_default str "unknown" x