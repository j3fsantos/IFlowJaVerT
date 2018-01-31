(** 
	JSIL Permissions 
*)

type t =
	| Readable 
	| Mutable 
	| Deletable
	[@@deriving show, compare]

let equal = [%compare.equal : t]

(** Print *)
let str (x : t) =
  match x with
  | Readable   -> "@r"
  | Mutable    -> "@m"
  | Deletable  -> "@d"

(** Print of an optional permission *)
let ostr (x : t option) = 
	Option.map_default str "" x