(** 
	JSIL Types 
*)

type t =
	| UndefinedType (** Type of Undefined      *)
	| NullType      (** Type of Null           *)
	| EmptyType     (** Type of Empty          *)
	| NoneType    (** Type of logical values *)
	| BooleanType   (** Type of booleans       *)
	| NumberType    (** Type of floats         *)
	| StringType    (** Type of strings        *)
	| CharType      (** Type of chars          *)
	| ObjectType    (** Type of objects        *)
	| ListType      (** Type of lists          *)
	| TypeType      (** Type of types          *)
	| SetType       (** Type of sets           *)
	[@@deriving show, compare]

let equal = [%compare.equal : t]

(** Print *)
let str (x : t) =
  match x with
  | UndefinedType -> "Undefined"
  | NullType      -> "Null"
  | EmptyType     -> "Empty"
  | NoneType      -> "None"
 	| BooleanType   -> "Bool"
 	| NumberType    -> "Num"
 	| StringType    -> "Str"
 	| CharType      -> "Char"
 	| ObjectType    -> "Obj"
 	| ListType      -> "List"
 	| TypeType      -> "Type"
 	| SetType       -> "Set"