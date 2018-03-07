(** 
	JSIL Literals 
*)

type t =
	| Undefined               (** The literal [undefined] *)
	| Null                    (** The literal [null] *)
	| Empty                   (** The literal [empty] *)
	| Constant  of Constant.t (** JSIL constants ({!type:jsil_constant}) *)
	| Bool      of bool       (** JSIL booleans: [true] and [false] *)
	| Num       of float      (** JSIL floats - double-precision 64-bit IEEE 754 *)
	| String    of string     (** JSIL strings *)
	| Loc       of string     (** JSIL object locations *)
	| Type      of Type.t     (** JSIL types ({!type:Type.t}) *)
	| LList     of t list     (** Lists of JSIL literals *)

(** Print *)
let rec str (x : t) =
  	match x with
  	| Undefined  -> "undefined"
  	| Null       -> "null"
  	| Empty      -> "empty"
  	| Constant c -> Constant.str c
  	| Bool b     -> if b then "true" else "false" 
  	| Num n      -> CCommon.string_of_float n
  	| String x   -> let wrap = if !CCommon.escape_string then "\\" else "" in
		                  Printf.sprintf "%s\"%s%s\"" wrap x wrap
  	| Loc loc    -> loc
  	| Type t     -> Type.str t
  	| LList ll   -> Printf.sprintf "{{ %s }}" (String.concat ", " (List.map str ll))

(** Typing *)
let type_of (x : t) : Type.t =
	match x with
	| Undefined    -> UndefinedType
	| Null         -> NullType
	| Empty        -> EmptyType
	| Constant _   -> NumberType
	| Bool _       -> BooleanType
	| Num n        -> NumberType
	| String _     -> StringType
	| Loc _        -> ObjectType
	| Type _       -> TypeType
	| LList _      -> ListType
