(** 
	JSIL MetaData 
*)

type t = Literal.t
	[@@deriving show, compare]

let equal = [%compare.equal : t]

(** Print *)
let str (x : t) =
  Literal.str x
	
(** Print of an optional metadata *)
let ostr (x : t option) = 
	Option.map_default str "unknown" x