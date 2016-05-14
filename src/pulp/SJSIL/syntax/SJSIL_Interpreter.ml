(***
 SJSIL - Interpreter 
*)
open SSyntax
open Batteries

let proto_f = "@proto" 

let fresh_int =
  let counter = ref 0 in
  let rec f () =
    let v = !counter in
    counter := !counter + 1;
    string_of_int v
  in f
  
let fresh_loc () : string =
  "$l" ^ (fresh_int ())

(* Taken from jscert *)
let to_int32 = fun n ->
  match classify_float n with
  | FP_normal | FP_subnormal ->
    let i32 = 2. ** 32. in
    let i31 = 2. ** 31. in
    let posint = (if n < 0. then (-1.) else 1.) *. (floor (abs_float n)) in
    let int32bit =
      let smod = mod_float posint i32 in
      if smod < 0. then smod +. i32 else smod
    in
    (if int32bit >= i31 then int32bit -. i32 else int32bit)
  | _ -> 0.

let to_uint32 = fun n ->
  match classify_float n with
  | FP_normal | FP_subnormal ->
    let i32 = 2. ** 32. in
    let posint = (if n < 0. then (-1.) else 1.) *. (floor (abs_float n)) in
    let int32bit =
      let smod = mod_float posint i32 in
      if smod < 0. then smod +. i32 else smod
    in
    int32bit
  | _ -> 0.

let modulo_32 = (fun x -> let r = mod_float x 32. in if x < 0. then r +. 32. else r)

let int32_bitwise_not = fun x -> Int32.to_float (Int32.lognot (Int32.of_float x))

let int32_bitwise_and = fun x y -> Int32.to_float (Int32.logand (Int32.of_float x) (Int32.of_float y))

let int32_bitwise_or = fun x y -> Int32.to_float (Int32.logor (Int32.of_float x) (Int32.of_float y))

let int32_bitwise_xor = fun x y -> Int32.to_float (Int32.logxor (Int32.of_float x) (Int32.of_float y))

let int32_left_shift x y =
  let l = Int32.of_float x in
  let r = (int_of_float y) mod 32 in
  Int32.to_float (Int32.shift_left l r)

let int32_right_shift x y =
  let l = Int32.of_float x in
  let r = (int_of_float y) mod 32 in
  Int32.to_float (Int32.shift_right l r)

let uint32_right_shift = (fun x y ->
  let i31 = 2. ** 31. in
  let i32 = 2. ** 32. in
  let signedx = if x >= i31 then x -. i32 else x in
  let left = Int32.of_float signedx in
  let right = (int_of_float y) mod 32 in
  let r = Int32.to_float (Int32.shift_right_logical left right) in
  if r < 0. then r +. i32 else r)

let evaluate_unop op lit = 
	match op with 
	| Not -> 
		(match lit with 
		| Bool b -> (Bool (not b))
		| _ -> raise (Failure "Non-bool argument to Not"))
	| Negative -> 
		(match lit with
		| Num n -> Num (-.n)
		| _ -> raise (Failure "Non-number argument to Negative"))
	| ToStringOp -> 
		(match lit with
		| Num n -> String (Utils.float_to_string_inner n)
		| _ -> raise (Failure "Non-number argument to ToStringOp"))
	| ToNumberOp -> 
		(match lit with
		| String s -> 
			let num = try
				Float.of_string s 
				with Failure "float_of_string" -> nan in
				(Num num)
		| _ -> raise (Failure "Non-string argument to ToNumberOp"))
	| ToInt32Op ->
		(match lit with
		| Num n -> Num (to_int32 n)
		| _ -> raise (Failure "Non-number argument to ToInt32Op"))
	| ToUint32Op ->
		(match lit with
		| Num n -> Num (to_uint32 n)
		| _ -> raise (Failure "Non-number argument to ToUint32Op"))		
	| BitwiseNot ->
		(match lit with
		| Num n -> Num (int32_bitwise_not n)
		| _ -> raise (Failure "Non-number argument to BitwiseNot"))
	
let evaluate_binop op lit1 lit2 = 
	match op with 
	| Equal -> 
		(match lit1, lit2 with 
		| Undefined, Undefined -> (Bool true)
		| Null, Null -> (Bool true)
		| Empty, Empty -> (Bool true)
		| Bool b1, Bool b2 -> (Bool (b1 == b2))
		| Num n1, Num n2 -> (Bool (n1 == n2))
		| String s1, String s2 -> (Bool (s1 == s2))
		| Loc l1, Loc l2 -> (Bool (l1 == l2))
		| Type t1, Type t2 -> (Bool (t1 == t2))
		| LVRef (l11, l12), LVRef  (l21, l22)
		| LORef (l11, l12), LORef  (l21, l22) -> (Bool ((l11 == l21) && (l12 == l22)))
		| _, _ -> Bool false)
	| LessThan -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Bool (n1 < n2)) 
		| _, _ -> raise (Failure "Non-number argument to LessThan"))
	| LessThanEqual -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Bool (n1 <= n2)) 
		| _, _ -> raise (Failure "Non-number argument to LessThanEqual"))
	| Plus -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Num (n1 +. n2)) 
		| _, _ -> raise (Failure "Non-number argument to Plus"))
	| Minus -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Num (n1 -. n2)) 
		| _, _ -> raise (Failure "Non-number argument to Minus"))
	| Times -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Num (n1 *. n2)) 
		| _, _ -> raise (Failure "Non-number argument to Times"))
	| Div -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Num (n1 /. n2)) 
		| _, _ -> raise (Failure "Non-number argument to Div"))
	| Mod -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Num (mod_float n1 n2)) 
		| _, _ -> raise (Failure "Non-number argument to Mod"))
	| Subtype -> 
		(match lit1, lit2 with 
		| Type t1, Type t2 -> 
			(match t1, t2  with 
			| ObjectReferenceType, ReferenceType -> Bool true 
			| VariableReferenceType, ReferenceType -> Bool true 
			| x, y when x == y -> Bool true
			| _, _ -> Bool false)
		| _, _ -> raise (Failure "Non-type argument to Subtype")) 
	| Concat -> 
		(match lit1, lit2 with 
		| String s1, String s2 -> (String (s1 ^ s2)) 
		| _, _ -> raise (Failure "Non-string argument to Concat"))
	| And -> 
		(match lit1, lit2 with 
		| Bool b1, Bool b2 -> (Bool (b1 && b2)) 
		| _, _ -> raise (Failure "Non-boolean argument to And"))
	| Or -> 
		(match lit1, lit2 with 
		| Bool b1, Bool b2 -> (Bool (b1 || b2)) 
		| _, _ -> raise (Failure "Non-string argument to Or"))
	| BitwiseAnd -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Num (int32_bitwise_and n1 n2)) 
		| _, _ -> raise (Failure "Non-string argument to BitwiseAnd"))	
	| BitwiseOr -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Num (int32_bitwise_or n1 n2)) 
		| _, _ -> raise (Failure "Non-string argument to BitwiseOr"))
	| BitwiseXor -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Num (int32_bitwise_xor n1 n2)) 
		| _, _ -> raise (Failure "Non-string argument to BitwiseXor"))
	| LeftShift -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Num (int32_left_shift n1 n2)) 
		| _, _ -> raise (Failure "Non-string argument to LeftShift"))
	| SignedRightShift -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Num (int32_right_shift n1 n2)) 
		| _, _ -> raise (Failure "Non-string argument to SignedRightShift"))	
	| UnsignedRightShift -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Num (uint32_right_shift n1 n2)) 
		| _, _ -> raise (Failure "Non-string argument to SignedRightShift"))

let evaluate_type_of lit = 
	match lit with 
	| Undefined -> UndefinedType
	| Null -> NullType
	| Empty -> EmptyType
	| Bool _ -> BooleanType
	| String _ -> StringType
	| Num _ -> NumberType
	| Loc _ -> ObjectType
	| Type _ -> TypeType
	| LVRef (_, _) -> VariableReferenceType
	| LORef (_, _) -> ObjectReferenceType
							
let rec evaluate_expr (e : jsil_expr) store = 
	match e with 
	| Literal l -> l 
	| Var x -> 
		(match SSyntax_Aux.try_find store x with 
		| None -> raise (Failure "Variable not found in the store")
		| Some v -> v)
	| BinOp (e1, bop, e2) -> 
		let v1 = evaluate_expr e1 store in 
		let v2 = evaluate_expr e2 store in 
		evaluate_binop bop v1 v2  
	| UnaryOp (unop, e) -> 
		let v = evaluate_expr e store in 
		evaluate_unop unop v
	| VRef (e1, e2) -> 
		let v1 = evaluate_expr e1 store in 
		let v2 = evaluate_expr e2 store in 
		(match v1, v2 with 
		| String loc, String field -> LVRef (loc, field)
		| _, _ -> raise (Failure "Illegal V-Reference constructor parameter"))
	| ORef (e1, e2) -> 
		let v1 = evaluate_expr e1 store in 
		let v2 = evaluate_expr e2 store in 
		(match v1, v2 with 
		| String loc, String field -> LORef (loc, field)
		| _, _ -> raise (Failure "Illegal O-Reference constructor parameter"))  
	| Base e -> 
		let v = evaluate_expr e store in
		(match v with 
		| LORef (loc, _) 
		| LVRef (loc, _) -> Loc loc  
		| _ -> raise (Failure "Illegal Base parameter"))
	| Field e -> 
		let v = evaluate_expr e store in
		(match v with 
		| LORef (_, field) 
		| LVRef (_, field) -> String field  
		| _ -> raise (Failure "Illegal Field parameter"))
	| TypeOf e ->
		let v = evaluate_expr e store in
		Type (evaluate_type_of v) 

let rec proto_field heap loc field =
	if (SHeap.mem heap (loc, field)) 
	then Loc loc  
	else 
		let proto_loc = (try SHeap.find heap (loc, proto_f) with 
		| _ -> raise (Failure "Object does not have proto field: this should not happen")) in  
		match proto_loc with 
		| Loc pl -> proto_field heap pl field
		| Null -> Empty 
		| _ -> raise (Failure "Illegal value for proto: this should not happen")

let rec proto_obj heap l1 l2 =
	if (l1 == l2) 
	then Bool (true) 
	else 
		let proto_loc = (try SHeap.find heap (l1, proto_f) with 
		| _ -> raise (Failure "Object does not have proto field: this should not happen")) in 
		match proto_loc with 
		| Loc pl -> proto_obj heap pl l2
		| Null -> Bool (false) 
		| _ -> raise (Failure "Illegal value for proto: this should not happen")

let rec evaluate_bcmd (bcmd : basic_jsil_cmd) heap store which_pred = 
	match bcmd with 
	| SSkip -> ()
	
	| SAssignment (x, e) ->
		let v_e = evaluate_expr e store in 
		Hashtbl.add store x v_e 
	
	| SPhiAssignment (x, x_arr) -> 
		let x_live = x_arr.(which_pred) in 
		let v = (match SSyntax_Aux.try_find store x_live with 
		| None -> raise (Failure "Variable not found in store")
		| Some v -> v) in 
		Hashtbl.add store x v 
	
	| SNew x -> 
		let new_loc = fresh_loc () in 
		SHeap.add heap (new_loc, proto_f) Null
		
	| SLookup (x, e1, e2) -> 
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in 	
		(match v_e1, v_e2 with 
		| Loc l, String f -> 
			let v = (try SHeap.find heap (l, f) with 
				| _ -> raise (Failure "Looking up inexistent cell")) in
			Hashtbl.replace store x v
		| _, _ -> raise (Failure "Illegal field inspection"))
	
	| SMutation (e1, e2, e3) ->
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in 	
		let v_e3 = evaluate_expr e3 store in
		(match v_e1, v_e2 with 
		| Loc l, String f -> SHeap.replace heap (l, f) v_e3
		| _, _ ->  raise (Failure "Illegal field inspection"))
	
	| SDelete (e1, e2) -> 
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in 				
		(match v_e1, v_e2 with 
		| Loc l, String f -> 
			if (SHeap.mem heap (l, f)) 
			then SHeap.remove heap (l, f)
			else raise (Failure "Deleting inexisting field")
		| _, _ -> raise (Failure "Illegal field deletion"))
	
	| SHasField (x, e1, e2) -> 
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in 	
		(match v_e1, v_e2 with 
		| Loc l, String f -> 
			let v = Bool (SHeap.mem heap (l, f)) in 
			Hashtbl.replace store x v
		| _, _ -> raise (Failure "Illegal Field Check"))
	
	| SProtoField (x, e1, e2) -> 
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in 	
		(match v_e1, v_e2 with 
		| Loc l, String f -> 
			let v = proto_field heap l f in 
			Hashtbl.replace store x v
		| _, _ -> raise (Failure "Illegal Proto Field Inspection"))
	
	| SProtoObj (x, e1, e2) -> 
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in 	
		(match v_e1, v_e2 with 
		| Loc l, String f -> 
			let v = proto_obj heap l f in 
			Hashtbl.replace store x v
		| _, _ -> raise (Failure "Illegal Proto Obj Inspection"))

let rec evaluate_cmd (bcmd : basic_jsil_cmd) heap store which_pred = 

