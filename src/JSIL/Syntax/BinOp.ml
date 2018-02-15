(* JSIL Unary Operators *)

type t =
	(* Comparison *)
	| Equal              (** Equality *)
	| LessThan           (** Less *)
	| LessThanEqual      (** Less or equal for numbers *)
	| LessThanString     (** Less or equal for strings *)
	(* Arithmetic *)
	| Plus               (** Addition *)
	| Minus              (** Subtraction *)
	| Times              (** Multiplication *)
	| Div                (** Float division *)
	| Mod                (** Modulus *)
	(* Boolean *)
	| And                (** Boolean conjunction *)
	| Or                 (** Boolean disjunction *)
	(* Bitwise *)
	| BitwiseAnd         (** Bitwise conjunction *)
	| BitwiseOr          (** Bitwise disjunction *)
	| BitwiseXor         (** Bitwise exclusive disjunction *)
	| LeftShift          (** Left bitshift *)
	| SignedRightShift   (** Signed right bitshift *)
	| UnsignedRightShift (** Unsigned right bitshift *)
	(* Mathematics *)
	| M_atan2            (** Arctangent y/x *)
	| M_pow              (** Power *)
	(* Lists *)
	| LstCons            (** List construction *)
	| LstCat             (** List concatenation *)
	(* Strings *)
	| StrCat             (** String concatenation *)
	(* Sets *)
	| SetDiff            (** Set difference *)
	| SetMem             (** Set membership *)
	| SetSub             (** Subset *)
	[@@deriving show, compare]

let equal = [%compare.equal : t]

let str (x : t) = 
	match x with
	| Equal -> "="
	| LessThan -> "<"
	| LessThanEqual -> "<="
	| LessThanString -> "<s"
	| Plus -> "+"
	| Minus -> "-"
	| Times -> "*"
	| Div -> "/"
	| Mod -> "%"
	| And -> "and"
	| Or -> "or"
	| BitwiseAnd -> "&"
	| BitwiseOr -> "|"
	| BitwiseXor -> "^"
	| LeftShift -> "<<"
	| SignedRightShift -> ">>"
	| UnsignedRightShift -> ">>>"
	| M_atan2 -> "m_atan2"
	| M_pow -> "**"
	| LstCons -> "::"
	| LstCat -> "@"
	| StrCat -> "++"
	| SetDiff -> "-d-"
	| SetMem -> "-e-"
	| SetSub -> "-s-"