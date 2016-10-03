(***
 SJSIL - Interpreter 
*)
open Batteries
open JSIL_Syntax
open JSIL_Memory_Model

let larguments = "$largs"
let largvals = "args"

let verbose = ref false

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

let evaluate_constant c = 
	match c with
  | Min_float -> Num (5e-324)
	| Max_float -> Num (max_float)
	| Random -> Num (Random.float (1.0 -. epsilon_float))
	| E -> Num (exp 1.0)
	| Ln10 -> Num (log 10.0)
	| Ln2 -> Num (log 2.)
	| Log2e -> Num (log (exp 1.0) /. log (2.0))
	| Log10e -> Num (log10 (exp 1.0))
	| Pi -> Num (4.0 *. atan 1.0)
	| Sqrt1_2 -> Num (sqrt 0.5)
	| Sqrt2 -> Num (sqrt 2.0)

let evaluate_type_of lit = 
	match lit with 
	| Undefined -> UndefinedType
	| Null -> NullType
	| Empty -> EmptyType
	| Constant _ -> NumberType
	| Bool _ -> BooleanType
	| Integer _ -> IntType
	| Num n -> if (n = (snd (modf n))) then IntType else NumberType 
	| String _ -> StringType
	| Loc _ -> ObjectType
	| Type _ -> TypeType
	| LVRef (_, _) -> VariableReferenceType
	| LORef (_, _) -> ObjectReferenceType
	| LList _ -> ListType

(* Taken from jscert *)
let to_int = fun n ->   
match classify_float n with
  | FP_nan -> 0.
	| FP_infinite -> n
	| FP_zero -> n
  | FP_normal 
	| FP_subnormal -> 
			(if n < 0. then (-1.) else 1.) *. (floor (abs_float n))

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

let to_uint16 = fun n ->
  match classify_float n with
  | FP_normal | FP_subnormal ->
    let i16 = 2. ** 16. in
    let posint = (if n < 0. then (-1.) else 1.) *. (floor (abs_float n)) in
    let int16bit =
      let smod = mod_float posint i16 in
      if smod < 0. then smod +. i16 else smod
    in
    int16bit
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

(* SPECIAL STUFF FOR OBJECTS *)

let copy_object heap loc fields = 
	let obj = (try SHeap.find heap loc with _ -> raise (Failure (Printf.sprintf "Not found: object %s" loc))) in
	let new_obj = SHeap.create 1021 in
	List.iter 
		(fun x -> 
			let value = (try SHeap.find obj x with _ -> raise (Failure (Printf.sprintf "Not found: [%s, %s]" loc x))) in
			SHeap.add new_obj x value)
		fields;
	new_obj

(* Default objects *)
let create_default_object proto cls ext = 
	let obj = SHeap.create 1021 in
		SHeap.add obj "@proto" (String proto);
		SHeap.add obj "@class" (String cls);
		SHeap.add obj "@extensible" (Bool ext);
		SHeap.add obj "@getOwnProperty" (String "o__getOwnProperty");
		SHeap.add obj "@getProperty" (String "o__getProperty");
		SHeap.add obj "@get" (String "o__get");
		SHeap.add obj "@canPut" (String "o__canPut");
		SHeap.add obj "@put" (String "o__put");
		SHeap.add obj "@hasProperty" (String "o__hasProperty");
		SHeap.add obj "@deleteProperty" (String "o__deleteProperty");
		SHeap.add obj "@defaultValue" (String "o__defaultValue");
		SHeap.add obj "@defineOwnProperty" (String "o__defineOwnProperty");
		SHeap.add obj "@primitiveValue" Empty;
		SHeap.add obj "@construct" Empty;
		SHeap.add obj "@call" Empty;
		SHeap.add obj "@hasInstance" Empty;
		SHeap.add obj "@scope" Empty;
		SHeap.add obj "@formalParameters" Empty;
		SHeap.add obj "@call" Empty;
		SHeap.add obj "@construct" Empty;
		SHeap.add obj "@targetFunction" Empty;
		SHeap.add obj "@boundThis" Empty;
		SHeap.add obj "@boundArguments" Empty;
		SHeap.add obj "@match" Empty;
		SHeap.add obj "@parameterMap" Empty;
		obj
		
(* Call-construct objects *)
let create_object_with_call_construct call construct len = 
	let obj = create_default_object "$lfun_proto" "Function" true in
		SHeap.add obj "length" (LList [String "d"; Num (float_of_int len); Bool false; Bool false; Bool false]); 
		SHeap.replace obj "@call" (String call);
		SHeap.replace obj "@construct" (String construct);
		SHeap.replace obj "@get" (String "f__get");
		SHeap.replace obj "@hasInstance" (String "f__hasInstance");
		obj

(* Function objects - with heap addition *)
let create_anonymous_function_object heap call construct params scope vis_fid =
	let loc = fresh_loc () in
	let len = List.length params in
	let obj = create_object_with_call_construct call construct len in
	
		(* Do the scope properly *)
		let loc_scope = fresh_loc () in
		let scope_obj = copy_object heap scope (List.tl vis_fid) in
		SHeap.add scope_obj (List.hd vis_fid) (Loc loc);
		SHeap.replace obj "@scope" (Loc loc_scope);
		
		
		SHeap.replace obj "@formalParameters" (LList (List.map (fun x -> String x) params));
		SHeap.add obj "caller"    (LList [(String "a"); Loc "$lthrow_type_error"; Loc "$lthrow_type_error"; Bool false; Bool false]);
		SHeap.add obj "arguments" (LList [(String "a"); Loc "$lthrow_type_error"; Loc "$lthrow_type_error"; Bool false; Bool false]);
			
		let loc_proto = fresh_loc () in
		let proto_obj = create_default_object "$lobj_proto" "Object" true in
			SHeap.add proto_obj "constructor" (LList [String "d"; Loc loc; Bool true; Bool false; Bool true]);
			SHeap.add obj "prototype" (LList [String "d"; Loc loc_proto; Bool true; Bool false; Bool true]);
	
			(* PUT BOTH IN THE HEAP *)
			SHeap.add heap loc_scope scope_obj;
			SHeap.add heap loc_proto proto_obj;
			SHeap.add heap loc obj;

			loc
			
(* END SPECIAL STUFF *)

let evaluate_unop op lit = 
	match op with
	| UnaryMinus -> 
		(match lit with
		| Num n -> Num (-.n)
		| _ -> raise (Failure "Non-number argument to UnaryMinus"))
	| Not -> 
		(match lit with 
		| Bool b -> (Bool (not b))
		| _ -> raise (Failure (Printf.sprintf "Non-bool argument to Not: %s" (JSIL_Print.string_of_literal lit false))))
	| BitwiseNot ->
		(match lit with
		| Num n -> Num (int32_bitwise_not n)
		| _ -> raise (Failure "Non-number argument to BitwiseNot"))
	| M_abs ->
		(match lit with
		| Num n -> Num (abs_float n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_acos ->
		(match lit with
		| Num n -> Num (acos n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_asin ->
		(match lit with
		| Num n -> Num (asin n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_atan ->
		(match lit with
		| Num n -> Num (atan n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_ceil ->
		(match lit with
		| Num n -> Num (ceil n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_cos ->
		(match lit with
		| Num n -> Num (cos n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_exp ->
		(match lit with
		| Num n -> Num (exp n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_floor ->
		(match lit with
		| Num n -> Num (floor n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_log ->
		(match lit with
		| Num n -> Num (log n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_round ->
		(match lit with
		| Num n -> Num (let sign = copysign 1.0 n in
										if ((sign < 0.0) && (n >= -0.5))
										then (-0.0)
										else (floor (n +. 0.5))
									 )
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_sgn ->
		(match lit with
		| Num n -> Num (copysign 1.0 n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_sin ->
		(match lit with
		| Num n -> Num (sin n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_sqrt ->
		(match lit with
		| Num n -> Num (sqrt n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| M_tan ->
		(match lit with
		| Num n -> Num (tan n)
		| _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s instead of a number." (JSIL_Print.string_of_literal lit false))))
	| IsPrimitive ->
		(match lit with
		| Null
		| Undefined
		| Bool _
		| Num _
		| String _ -> (Bool true)
		| _ -> Bool false)
	| ToStringOp -> 
		(match lit with
		| Num n -> String (Utils.float_to_string_inner n)
		| _ -> raise (Failure (Printf.sprintf "Non-number argument to ToStringOp: %s" (JSIL_Print.string_of_literal lit false))))
	| ToIntOp ->
		(match lit with
		| Num n -> Num (to_int n)
		| _ -> raise (Failure "Non-number argument to ToIntOp"))
	| ToUint16Op ->
		(match lit with
		| Num n -> Num (to_uint16 n)
		| _ -> raise (Failure "Non-number argument to ToUint16Op"))	
	| ToInt32Op ->
		(match lit with
		| Num n -> Num (to_int32 n)
		| _ -> raise (Failure "Non-number argument to ToInt32Op"))
	| ToUint32Op ->
		(match lit with
		| Num n -> Num (to_uint32 n)
		| _ -> raise (Failure "Non-number argument to ToUint32Op"))
	| ToNumberOp -> 
		(match lit with
		| String s -> 
			let num = try Float.of_string s 
				with Failure "float_of_string" -> 
					if s = "" then 0. else nan in
				(Num num)
		| _ -> raise (Failure "Non-string argument to ToNumberOp"))
	| Car ->
		(match lit with
		| LList ll -> 
			(match ll with 
			| [] -> Empty
			| lit :: _ -> lit)
		| _ -> raise (Failure "Non-list argument to Car"))
	| Cdr ->
		(match lit with
		| LList ll -> 
			(match ll with 
			| [] -> Empty
			| _ :: ll -> LList ll)
		| _ -> raise (Failure "Non-list argument to Cdr"))
	| LstLen ->
		(match lit with
		| LList l -> Num (float_of_int (List.length l))
		| _ -> raise (Failure (Printf.sprintf "Non-list argument to LstLen: %s" (JSIL_Print.string_of_literal lit false))))
	| StrLen ->
		(match lit with
		| String s -> Num (float_of_int (String.length s))
		| _ -> raise (Failure (Printf.sprintf "Non-string argument to StrLen: %s" (JSIL_Print.string_of_literal lit false))))

(*
			xret := "create_object_with_body" ($lmath_max, "M_max", 2);	
			xret := "create_object_with_body" ($lmath_min, "M_min", 2);

let same_value_num n1 n2 = 
	let cfn1 = classify_float n1 in
	let cfn2 = classify_float n2 in
	match cfn1, cfn2 with
	| FP_nan, FP_nan -> true
	| FP_zero, FP_zero -> 
		let sign1 = copysign 1.0 n1 in
		let sign2 = copysign 1.0 n2 in
			sign1 = sign2
	| _, _ -> (n1 = n2)
*)

let evaluate_binop op lit1 lit2 = 
	match op with 
	| Equal -> 
		(match lit1, lit2 with 
		| Undefined, Undefined -> (Bool true)
		| Null, Null -> (Bool true)
		| Empty, Empty -> (Bool true)
		| Constant c1, Constant c2 -> (Bool (c1 = c2))
		| Bool b1, Bool b2 -> (Bool (b1 = b2))
		| Num n1, Num n2 -> (Bool (n1 = n2))
		| String s1, String s2 -> (Bool (s1 = s2))
		| Loc l1, Loc l2 -> (Bool (l1 = l2))
		| Type t1, Type t2 -> (Bool (t1 = t2))
		| LVRef (l11, l12), LVRef  (l21, l22)
		| LORef (l11, l12), LORef  (l21, l22) -> (Bool ((l11 = l21) && (l12 = l22)))
		| LList l1, LList l2 -> (Bool (l1 = l2))
		| _, _ -> Bool false)
	| LessThan -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Bool (n1 < n2)) 
		| _, _ -> raise (Failure "Non-number arguments to LessThan"))
	| LessThanString -> 
		(match lit1, lit2 with 
		| String s1, String s2 -> (Bool (s1 < s2)) 
		| _, _ -> raise (Failure "Non-string arguments to LessThanString"))
	| LessThanEqual -> 
		(match lit1, lit2 with 
		| Num n1, Num n2 -> (Bool (n1 <= n2)) 
		| _, _ -> raise (Failure (Printf.sprintf "Non-number argument to LessThanEqual: %s <= %s" (JSIL_Print.string_of_literal lit1 false) (JSIL_Print.string_of_literal lit2 false))))
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
	| M_atan2 ->
		(match lit1, lit2 with
		| Num x, Num y -> Num (atan2 x y)
		| _, _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s %s instead of numbers." (JSIL_Print.string_of_literal lit1 false) (JSIL_Print.string_of_literal lit2 false))))
	| M_pow ->
		(match lit1, lit2 with
		| Num x, Num y -> Num (x ** y)
		| _, _ -> raise (Failure (Printf.sprintf "Mathematical function called with %s %s instead of numbers." (JSIL_Print.string_of_literal lit1 false) (JSIL_Print.string_of_literal lit2 false))))
	| Subtype -> 
		(match lit1, lit2 with 
		| Type t1, Type t2 -> (Bool (types_leq t1 t2))
		| _, _ -> raise (Failure "Non-type argument to Subtype")) 
	| LstCons ->
		(match lit2 with
		| LList list -> LList
			(match lit1 with
			| LList [] -> list		(* Are we sure this is the semantics we want for LstCons? *)
			| _ -> lit1 :: list)
		| _ -> raise (Failure "Non-list second argument to LstCons"))
	| LstCat -> 
		(match lit1, lit2 with 
		| LList l1, LList l2 -> (LList (List.append l1 l2))
		| _, _ -> raise (Failure "Non-list argument to LstCat"))
	| StrCat -> 
		(match lit1, lit2 with 
		| String s1, String s2 -> (String (s1 ^ s2)) 
		| _, _ -> raise (Failure (Printf.sprintf "Non-string argument to StrCat: %s, %s" (JSIL_Print.string_of_literal lit1 false) (JSIL_Print.string_of_literal lit2 false))))

let rec evaluate_expr (e : jsil_expr) store = 
	match e with 
	| Literal l -> 
		(match l with
		| Constant c -> evaluate_constant c
		| x -> x) 
	
	| Var x -> 
		(match SSyntax_Aux.try_find store x with 
		| None -> 
			let err_msg = Printf.sprintf "Variable %s not found in the store" x in 
			let store_str = JSIL_Memory_Print.string_of_store store in 
			if (!verbose) then Printf.printf "The current store is: \n %s" store_str;
			raise (Failure err_msg) 
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
		| l, String field -> 
			(match l with
			| Undefined | Bool _ 
			| Num _ | String _ | Loc _ -> LVRef (l, field)
			| _ -> raise (Failure (Printf.sprintf "Illegal V-Reference constructor parameter : %s, %s" (JSIL_Print.string_of_literal v1 false) (JSIL_Print.string_of_literal v2 false))))
		| _, _ -> raise (Failure (Printf.sprintf "Illegal V-Reference constructor parameter : %s, %s" (JSIL_Print.string_of_literal v1 false) (JSIL_Print.string_of_literal v2 false))))
	
	| ORef (e1, e2) -> 
		let v1 = evaluate_expr e1 store in 
		let v2 = evaluate_expr e2 store in 
    (match v1, v2 with 
		| l, String field -> 
			(match l with
			| Undefined | Bool _ 
			| Num _ | String _ | Loc _ -> LORef (l, field)
			| _ -> raise (Failure (Printf.sprintf "Illegal O-Reference constructor parameter : %s, %s" (JSIL_Print.string_of_literal v1 false) (JSIL_Print.string_of_literal v2 false))))
		| _, _ -> raise (Failure (Printf.sprintf "Illegal O-Reference constructor parameter : %s, %s" (JSIL_Print.string_of_literal v1 false) (JSIL_Print.string_of_literal v2 false))))
	
	| Base e -> 
		let v = evaluate_expr e store in
		(match v with 
		| LORef (loc, _) 
		| LVRef (loc, _) -> loc  
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
	
	| EList ll ->
		(match ll with 
		| [] -> LList []
		| e :: ll ->
			let ve = evaluate_expr e store in
			let vll = evaluate_expr (EList ll) store in
			match vll with
			| LList vll -> LList (ve :: vll)
			| _ -> raise (Failure "List evaluation error"))
	
	| LstNth (e1, e2) ->
		let v = evaluate_expr e1 store in 
		let n = evaluate_expr e2 store in
		(match v, n with 
		| LList list, Num n -> 
				(List.nth list (int_of_float n))
		| _, _ -> raise (Failure (Printf.sprintf "Incorrect argument to LstNth: %s, %s" (JSIL_Print.string_of_literal v false) (JSIL_Print.string_of_literal n false))))

	| StrNth (e1, e2) ->
		let v = evaluate_expr e1 store in 
		let n = evaluate_expr e2 store in
		(match v, n with 
		| String s, Num n -> 
				String (String.make 1 (String.get s (int_of_float n)))
		| _, _ -> raise (Failure (Printf.sprintf "Incorrect argument to StrNth: %s, %s" (JSIL_Print.string_of_literal v false) (JSIL_Print.string_of_literal n false))))

	| _ -> raise (Failure (Printf.sprintf "Unknown expression: %s" (JSIL_Print.string_of_expression e false)))
				
let rec proto_field heap loc field =
	let obj = (try SHeap.find heap loc with
	| _ -> raise (Failure (Printf.sprintf "Looking up inexistent object: %s" loc))) in
	if (SHeap.mem obj field)
	then 
		(Loc loc)
	else
		let proto_loc = (try SHeap.find obj proto_f with 
		| _ -> raise (Failure "Object does not have proto field: this should not happen")) in  
		match proto_loc with 
		| Loc pl -> proto_field heap pl field
		| Null -> Undefined 
		| _ -> raise (Failure "Illegal value for proto: this should not happen")

let rec proto_obj heap l1 l2 =
	let obj = (try SHeap.find heap l1 with
	| _ -> raise (Failure "Looking up an inexistent object!")) in
	if (l1 = l2)
		then (Bool true)
	else
		let proto_loc = (try SHeap.find obj proto_f with 
		| _ -> raise (Failure "Object does not have proto field: this should not happen")) in 
		match proto_loc with 
		| Loc pl -> proto_obj heap pl l2
		| Null -> Bool (false) 
		| _ -> raise (Failure "Illegal value for proto: this should not happen")

let rec evaluate_bcmd bcmd heap store =
	match bcmd with 
	| SSkip -> Empty
	
	| SAssignment (x, e) ->
		let v_e = evaluate_expr e store in 
		if (!verbose) then Printf.printf "Assignment: %s := %s\n" x (JSIL_Print.string_of_literal v_e false);
		Hashtbl.replace store x v_e; 
		v_e
		
	| SNew x -> 
		let new_loc = fresh_loc () in 
		let obj = SHeap.create 1021 in
		SHeap.add obj proto_f Null;
		SHeap.add heap new_loc obj;
		Hashtbl.replace store x (Loc new_loc);
		Loc new_loc
		
	| SLookup (x, e1, e2) -> 
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in 	
		(match v_e1, v_e2 with 
		| Loc l, String f -> 
			let obj = (try SHeap.find heap l with
			| _ -> raise (Failure (Printf.sprintf "Looking up inexistent object: %s" (JSIL_Print.string_of_literal v_e1 false)))) in
			let v = (try SHeap.find obj f with
				| _ -> 
					(* let final_heap_str = JSIL_Print.sexpr_of_heap heap in 
					Printf.printf "Final heap: \n%s\n" final_heap_str; *)
					raise (Failure (Printf.sprintf "Looking up inexistent field: [%s, %s]" (JSIL_Print.string_of_literal v_e1 false) (JSIL_Print.string_of_literal v_e2 false)))) in
	
			Hashtbl.replace store x v; 
			if (!verbose) then Printf.printf "Lookup: %s := [%s, %s] = %s \n" x (JSIL_Print.string_of_literal v_e1 false) (JSIL_Print.string_of_literal v_e2 false) (JSIL_Print.string_of_literal v false);
			v
		| _, _ -> raise (Failure (Printf.sprintf "Illegal field inspection: [%s, %s]" (JSIL_Print.string_of_literal v_e1 false) (JSIL_Print.string_of_literal v_e2 false))))
	
	| SMutation (e1, e2, e3) ->
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in 	
		let v_e3 = evaluate_expr e3 store in
		(match v_e1, v_e2 with 
		| Loc l, String f -> 
			if (SHeap.mem heap l) 
			then
				let obj = SHeap.find heap l in ();
				SHeap.replace obj f v_e3;
				if (!verbose) then Printf.printf "Mutation: [%s, %s] = %s \n" (JSIL_Print.string_of_literal v_e1 false) (JSIL_Print.string_of_literal v_e2 false) (JSIL_Print.string_of_literal v_e3 false);	
				v_e3
			else 
				let obj = SHeap.create 1021 in
				SHeap.add obj proto_f Null;
				SHeap.add heap l obj;
				SHeap.replace obj f v_e3;
				if (!verbose) then Printf.printf "Mutation: [%s, %s] = %s \n" (JSIL_Print.string_of_literal v_e1 false) (JSIL_Print.string_of_literal v_e2 false) (JSIL_Print.string_of_literal v_e3 false);
				v_e3
		| _, _ ->  raise (Failure "Illegal field inspection"))
	
	| SDelete (e1, e2) -> 
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in 				
		(match v_e1, v_e2 with 
		| Loc l, String f -> 
			let obj = (try SHeap.find heap l with
			| _ -> raise (Failure (Printf.sprintf "Looking up inexistent object: %s" (JSIL_Print.string_of_literal v_e1 false)))) in
			if (SHeap.mem obj f) 
			then 
				(if (!verbose) then Printf.printf "Removing field (%s, %s)!\n" (JSIL_Print.string_of_literal v_e1 false) (JSIL_Print.string_of_literal v_e2 false);
				SHeap.remove obj f; 
				Bool true)
			else raise (Failure "Deleting inexisting field")
		| _, _ -> raise (Failure "Illegal field deletion"))
	
	| SHasField (x, e1, e2) -> 
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in 	
		let pv_e1 = JSIL_Print.string_of_literal v_e1 false in
		let pv_e2 = JSIL_Print.string_of_literal v_e2 false in
		(match v_e1, v_e2 with 
		| Loc l, String f -> 
			let obj = (try SHeap.find heap l with
			| _ -> raise (Failure (Printf.sprintf "Looking up inexistent object: %s" pv_e1))) in
			let v = Bool (SHeap.mem obj f) in 
			Hashtbl.replace store x v; 
			if (!verbose) then Printf.printf "hasField: %s := hf (%s, %s) = %s \n" x pv_e1 pv_e2 (JSIL_Print.string_of_literal v false);
			v
		| _, _ -> raise (Failure (Printf.sprintf "Illegal Field Check: [%s, %s]" pv_e1 pv_e2)))
	
	| SGetFields (x, e) ->
		let v_e = evaluate_expr e store in
		(match v_e with
		| Loc l -> 
			let obj = (try SHeap.find heap l with
			| _ -> raise (Failure (Printf.sprintf "Looking up inexistent object: %s" (JSIL_Print.string_of_literal v_e false)))) in
			let fields =  
				SHeap.fold
				(fun field value acc ->
					let t = evaluate_type_of value in
					if (t = ListType) then 
						(String field) :: acc
					else
						acc
					) obj [] in
			let v = LList (List.sort compare fields) in
			Hashtbl.replace store x v;
			if (!verbose) then Printf.printf "hasField: %s := gf (%s) = %s \n" x (JSIL_Print.string_of_literal v_e false) (JSIL_Print.string_of_literal v false);
			v
		| _ -> raise (Failure "Passing non-object value to getFields"))
	
  | SArguments x ->
		let arg_obj = (try SHeap.find heap larguments with
		| _ -> raise (Failure "The arguments object doesn't exist.")) in
		let v = (try SHeap.find arg_obj "args" with
		| _ -> raise (Failure "The arguments are not available.")) in
			Hashtbl.replace store x v;
			if (!verbose) then Printf.printf "args: %s \n" (JSIL_Print.string_of_literal v false);
			v

let init_store params args = 
	let number_of_params = List.length params in 
	let new_store = Hashtbl.create (number_of_params + 1) in
	
	if (!verbose) then 
		begin
			Printf.printf "I am initializing a store! Number of args: %d, Number of params: %d\n" (List.length args) (List.length params);
			Printf.printf "Params: ";
			List.iter (fun x -> Printf.printf "%s " x) params;
			Printf.printf "\n";
			Printf.printf "Args: ";
			List.iter (fun x -> Printf.printf "%s " (JSIL_Print.string_of_literal x false)) args;
			Printf.printf "\n"
		end;
	
	let rec loop params args = 
		match params with 
		| [] -> () 
		| param :: rest_params -> 
			(match args with 
			| arg :: rest_args -> 
				Hashtbl.replace new_store param arg;
				loop rest_params rest_args
			| [] -> 
				Hashtbl.replace new_store param Undefined;
				loop rest_params []) in 
	loop params args; 
	
	let str_store = JSIL_Memory_Print.string_of_store new_store in 
	if (!verbose) then Printf.printf "I have just initialized the following store\n %s \n" str_store; 
	new_store 
	
let rec evaluate_cmd prog cur_proc_name which_pred heap store cur_cmd prev_cmd cc_tbl vis_tbl = 	
	let proc = try Hashtbl.find prog cur_proc_name with
		| _ -> raise (Failure (Printf.sprintf "The procedure %s you're trying to call doesn't exist. Ew." cur_proc_name)) in  
	let cmd = proc.proc_body.(cur_cmd) in 

	let metadata, cmd = cmd in
	match cmd with 
	| SBasic bcmd -> 
		let _ = evaluate_bcmd bcmd heap store in 
	  evaluate_next_command prog proc which_pred heap store cur_cmd prev_cmd cc_tbl vis_tbl
		 
	| SGoto i -> 
		evaluate_cmd prog cur_proc_name which_pred heap store i cur_cmd cc_tbl vis_tbl
	
	| SGuardedGoto (e, i, j) -> 
		let v_e = evaluate_expr e store in
		(match v_e with 
		| Bool true -> evaluate_cmd prog cur_proc_name which_pred heap store i cur_cmd cc_tbl vis_tbl
		| Bool false -> evaluate_cmd prog cur_proc_name which_pred heap store j cur_cmd cc_tbl vis_tbl
		| _ -> raise (Failure (Printf.sprintf "So you're really trying to do a goto based on %s? Ok..." (JSIL_Print.string_of_literal v_e false))))

	| SCall (x, e, e_args, j) 
		when  evaluate_expr e store = String "Object_eval" ->
		(* Printf.printf "I intercepted something!!!\n";  *)
		let e_args = 
			(if (List.length e_args < 3) then (List.append e_args [Literal Undefined]) else e_args) in
		let str_e = List.nth e_args 2 in
		let str_e = (evaluate_expr str_e store) in
		(match str_e with
		| String code ->
				let code = Str.global_replace (Str.regexp (Str.quote "\\\"")) "\"" code in
				(* Printf.printf "\n%s\n" code; *)
				let x_scope, x_this = 
					(match SSyntax_Aux.try_find store (Js2jsil.var_scope), SSyntax_Aux.try_find store (Js2jsil.var_this)  with 
					| Some x_scope, Some x_this -> x_scope, x_this
					| _, _ -> raise (Failure "No var_scope or var_this to give to eval")) in
				(match (try
					let e_js = Parser_main.exp_from_string code in
					Some (Js2jsil.js2jsil_eval prog which_pred cc_tbl vis_tbl cur_proc_name e_js)
					with _ -> None) with
				| Some proc_eval ->
					(let new_store = init_store [ Js2jsil.var_scope; Js2jsil.var_this ] [ x_scope; x_this ] in
					match evaluate_cmd prog proc_eval.proc_name which_pred heap new_store 0 0 cc_tbl vis_tbl with
					| Normal, v ->
						Hashtbl.replace store x v;
						Hashtbl.remove prog proc_eval.proc_name;
						evaluate_next_command prog proc which_pred heap store cur_cmd prev_cmd cc_tbl vis_tbl
					| Error, v ->
						match j with
						| None -> raise (Failure "procedure throws an error without an error label")
						| Some j ->
							Hashtbl.replace store x v;
							evaluate_cmd prog cur_proc_name which_pred heap store j cur_cmd cc_tbl vis_tbl)
				| None -> (* Any sort of error from Parsing and JS2JSIL compilation *)
					(match SSyntax_Aux.try_find store (Js2jsil.var_se), j with
					| Some v, Some j ->
						Hashtbl.replace store x v;
						evaluate_cmd prog cur_proc_name which_pred heap store j cur_cmd cc_tbl vis_tbl
					| _, None -> raise (Failure ("Procedure "^ cur_proc_name ^" just returned an error, but no error label was provided. Bad programmer."))
					| _, _ -> raise (Failure "No Syntax Error for you, no noooo!")))

		| _ -> Hashtbl.replace store x str_e;
					 evaluate_next_command prog proc which_pred heap store cur_cmd prev_cmd cc_tbl vis_tbl)

	| SCall (x, e, e_args, j)
	  when evaluate_expr e store = String "Function_construct" ->
			
			(* Printf.printf "Function constructor encountered.\n"; *)
			
			let se = (evaluate_expr (Var (Js2jsil.var_se)) store) in
			
			let argCount = (List.length e_args - 2) in
			let params = ref "" in
			let body = ref "" in
			if (argCount = 0) then () else 
			begin
				if (argCount = 1) then 
				let bd = List.nth e_args 2 in
					let ebd = evaluate_expr bd store in
					(match ebd with
					   | String bd -> body := bd
					   | _ -> raise (Failure "Non-string body in the Function constructor"));
				else
			  	let firstArg = List.nth e_args 2 in
					let evalFirstArg = evaluate_expr firstArg store in
					(match evalFirstArg with
					 | String efa -> params := efa
					 | _ -> raise (Failure "Non-string parameter in the Function constructor"));
					for i = 3 to argCount do
						let arg = List.nth e_args i in
						let evalArg = evaluate_expr arg store in
						(match evalArg with
					   | String efa -> params := !params ^ ", " ^ efa
					   | _ -> raise (Failure "Non-string parameter in the Function constructor"));
					done;
					let bd = List.nth e_args (argCount + 1) in
					let ebd = evaluate_expr bd store in
					(match ebd with
					   | String bd -> body := bd
					   | _ -> raise (Failure "Non-string body in the Function constructor"));
			end;

			(* Printf.printf "\tParameters: %s\n" !params;
			Printf.printf "\tBody: %s\n\n" !body; *)
 
			(* Parsing the parameters as a FormalParametersList *)
			let lexbuf = Lexing.from_string !params in
			let parsed_params = 
				(try (Some (JSIL_Utils.parse_without_error JSIL_Parser.param_list_FC_target lexbuf)) with 
				 | _ -> None) in
			(match parsed_params with
			| None -> (Error, se)
			| Some parsed_params -> 
				let len = List.length parsed_params in
			
				(* Printf.printf "\tParsed parameters: ";
				for i = 0 to (len - 1) do
					let elem = List.nth parsed_params i in
					Printf.printf "%s " elem;
				done;
				Printf.printf "\n"; *)
			
				(* Parsing the body as a FunctionBody *)
				let e_body = (evaluate_expr (Literal (String !body)) store) in
				(match e_body with
				| String code ->
					let code = Str.global_replace (Str.regexp (Str.quote "\\\"")) "\"" code in
					let code = "function (" ^ !params ^ ") {" ^ code ^ "}" in
					
					(* Printf.printf "\n\tParsing: %s\n\n" code; *)
					
					let e_js = 
						(try (Some (Parser_main.exp_from_string code)) with
					   | _ -> None) in
					(match e_js with
					| None -> (Error, se)
    			| Some e_js -> 							
							(match e_js.Parser_syntax.exp_stx with
							  | Script (_, le) -> 
									(match le with
									| e :: [] -> 
										(match e.Parser_syntax.exp_stx with
										| Parser_syntax.AnonymousFun (_, params, body) ->		
												(* Printf.printf "Params: ";
												List.iter (fun x -> Printf.printf "%s " x) params;
												Printf.printf "\n"; *)
												let new_proc = Js2jsil.js2jsil_function_constructor_prop prog which_pred cc_tbl vis_tbl cur_proc_name params e in
												let fun_name = new_proc.proc_name in
												let vis_tbl = (match vis_tbl with
												                | Some t -> t
																				| None -> raise (Failure "No visibility table")) in 
												let vis_fid = try (Hashtbl.find vis_tbl fun_name) 
													with _ -> (let msg = Printf.sprintf "Function %s not found in visibility table" fun_name in 
																		raise (Failure msg)) in
												let scope = (evaluate_expr (Var Js2jsil.var_scope) store) in
												let lsc = (match scope with
												             | Loc lsc -> lsc
																		 | _ -> raise (Failure "Scope not a location.")) in  
												(* Printf.printf "Function name: %s\n" fun_name;
												Printf.printf "vis_fid: ";
												List.iter (fun x -> Printf.printf "%s " x) vis_fid;
												Printf.printf "\n"; *)
												let new_loc = create_anonymous_function_object heap fun_name fun_name params lsc vis_fid in
												Hashtbl.replace store x (Loc new_loc);
					 							evaluate_next_command prog proc which_pred heap store cur_cmd prev_cmd cc_tbl (Some vis_tbl)
											
										| _ -> (Error, se))
									| _ -> (Error, se))
								| _ -> (Error, se))
					| _ -> (Error, se))

				| _ -> (Error, se))
      )
		
	| SCall (x, e, e_args, j) -> 
		(* Printf.printf "Nothing was intercepted!!!\n"; *)
		let call_proc_name_val = evaluate_expr e store in 
		let call_proc_name = (match call_proc_name_val with 
		| String call_proc_name -> 
				if (!verbose) then Printf.printf "\nExecuting procedure %s\n" call_proc_name; 
				call_proc_name 
		| _ -> raise (Failure (Printf.sprintf "Erm, no. Procedures can't be called %s." (JSIL_Print.string_of_literal call_proc_name_val false)))) in 
		let arg_vals = List.map 
			(fun e_arg -> evaluate_expr e_arg store) 
			e_args in 
		let call_proc = try Hashtbl.find prog call_proc_name with
		| _ -> raise (Failure (Printf.sprintf "The procedure %s you're trying to call doesn't exist." call_proc_name)) in
		let new_store = init_store call_proc.proc_params arg_vals in 

		if (List.length arg_vals = 0) || (List.nth arg_vals 0 <> String "args") then
		begin
			let args_obj = SHeap.create 1 in 
				SHeap.replace args_obj largvals (LList arg_vals);
				SHeap.replace heap larguments args_obj;
		end;
		(match evaluate_cmd prog call_proc_name which_pred heap new_store 0 0 cc_tbl vis_tbl with 
		| Normal, v -> 
			Hashtbl.replace store x v;
	 		evaluate_next_command prog proc which_pred heap store cur_cmd prev_cmd cc_tbl vis_tbl
		| Error, v -> 
			(match j with
			| None -> raise (Failure ("Procedure "^ call_proc_name ^" just returned an error, but no error label was provided. Bad programmer."))
			| Some j -> Hashtbl.replace store x v;
				evaluate_cmd prog cur_proc_name which_pred heap store j cur_cmd cc_tbl vis_tbl))

	| SApply (x, e_args, j) ->
		let arguments = evaluate_expr (EList e_args) store in 
		let args =
			(match arguments with
			| LList args ->
				let rec flatten le = 
					(match le with
					| [] -> []
					| e :: le -> 
						List.append
							(match e with 
			      	| LList e -> e
							| x -> [ x ])
							(flatten le)) in
				flatten args
			| _ -> raise (Failure "Nope!")) in
		(match args with
  		| [] -> raise (Failure "No no no. Not at all")
  		| call_proc_name_val :: arg_vals -> 
  		let call_proc_name = (match call_proc_name_val with 
  		| String call_proc_name -> 
  				if (!verbose) then Printf.printf "\nExecuting procedure %s\n" call_proc_name; 
  				call_proc_name 
  		| _ -> raise (Failure (Printf.sprintf "No. You can't call a procedure %s." (JSIL_Print.string_of_literal call_proc_name_val false)))) in 
  		let call_proc = try Hashtbl.find prog call_proc_name with
  		| _ -> raise (Failure (Printf.sprintf "The procedure %s you're trying to call doesn't exist." call_proc_name)) in
  		let new_store = init_store call_proc.proc_params arg_vals in 
  		if (List.length arg_vals = 0) || (List.nth arg_vals 0 <> String "args") then
  		begin
  			let args_obj = SHeap.create 1 in 
  				SHeap.replace args_obj largvals (LList arg_vals);
  				SHeap.replace heap larguments args_obj;
  		end;
  		(match evaluate_cmd prog call_proc_name which_pred heap new_store 0 0 cc_tbl vis_tbl with 
  		| Normal, v -> 
  			Hashtbl.replace store x v;
  	 		evaluate_next_command prog proc which_pred heap store cur_cmd prev_cmd cc_tbl vis_tbl
  		| Error, v -> 
  			(match j with
  			| None -> raise (Failure ("Procedure "^ call_proc_name ^" just returned an error, but no error label was provided. Bad programmer."))
  			| Some j -> Hashtbl.replace store x v;
  				evaluate_cmd prog cur_proc_name which_pred heap store j cur_cmd cc_tbl vis_tbl)))
	
	| SPhiAssignment (x, x_arr) -> 
		evaluate_phi_psi_cmd prog proc which_pred heap store cur_cmd prev_cmd cur_cmd x x_arr cc_tbl vis_tbl

	| SPsiAssignment (x, x_arr) ->
		let rec find_prev_non_psi_cmd index = 
			(if (index < 0) 
				then raise (Failure "Psi node does not have non-psi antecedent") 
				else 
					match proc.proc_body.(index) with 
					| _, SPsiAssignment (_, _) -> find_prev_non_psi_cmd (index - 1) 
					| _ -> index) in 
		let ac_cur_cmd = find_prev_non_psi_cmd cur_cmd in 
		evaluate_phi_psi_cmd prog proc which_pred heap store cur_cmd prev_cmd ac_cur_cmd x x_arr cc_tbl vis_tbl

and 
evaluate_next_command prog proc which_pred heap store cur_cmd prev_cmd cc_tbl vis_tbl = 	
	let cur_proc_name = proc.proc_name in 
	if (Some cur_cmd = proc.ret_label)
		then 
			(let ret_value = 
				(let ret_var = (match proc.ret_var with
			    					    | None -> raise (Failure "No no!") 
												| Some ret_var -> ret_var) in
				  (try (Hashtbl.find store ret_var) with
			| _ -> raise (Failure (Printf.sprintf "Cannot find return variable.")))) in
			if (!verbose) then Printf.printf ("Procedure %s returned: Normal, %s\n") cur_proc_name (JSIL_Print.string_of_literal ret_value false);
			Normal, ret_value)
		else 
			(if (Some cur_cmd = proc.error_label) 
			then 
				(let err_value = 
					(let err_var = (match proc.error_var with 
					                      | None -> raise (Failure "No no!") 
																| Some err_var -> err_var) in
				         (try (Hashtbl.find store err_var) with
				| _ -> raise (Failure (Printf.sprintf "Cannot find error variable in proc %s, err_lab = %d, err_var = %s, cmd = %s" proc.proc_name cur_cmd err_var (JSIL_Print.string_of_cmd proc.proc_body.(prev_cmd)  0 0 false false false))))) in
			if (!verbose) then Printf.printf ("Procedure %s returned: Error, %s\n") cur_proc_name (JSIL_Print.string_of_literal err_value false);
			Error, err_value)
		else (
			let next_cmd = 
				(if ((cur_cmd + 1) < (Array.length proc.proc_body)) 
					then Some proc.proc_body.(cur_cmd+1)
					else None) in 
			let next_prev = 
				match next_cmd with 
				| Some (_, SPsiAssignment (_, _)) -> prev_cmd 
				| _ -> cur_cmd in 
			evaluate_cmd prog proc.proc_name which_pred heap store (cur_cmd + 1) next_prev cc_tbl vis_tbl))
and 
evaluate_phi_psi_cmd prog proc which_pred heap store cur_cmd prev_cmd ac_cur_cmd x x_arr cc_tbl vis_tbl = 
	  let cur_proc_name = proc.proc_name in 
		let cur_which_pred =  
			try Hashtbl.find which_pred (cur_proc_name, prev_cmd, ac_cur_cmd) 
			with _ ->  raise (Failure (Printf.sprintf "which_pred undefined for command: %s %d %d %d" cur_proc_name prev_cmd cur_cmd ac_cur_cmd)) in 		
		let x_live = x_arr.(cur_which_pred) in 
		let v = (match x_live with 
		| None -> Undefined 
		| Some x_live -> 
			(match SSyntax_Aux.try_find store x_live with 
			| None -> 
				let cur_cmd_str = JSIL_Print.string_of_cmd proc.proc_body.(cur_cmd) 0 0 false false false in 
				let prev_cmd_str = JSIL_Print.string_of_cmd proc.proc_body.(prev_cmd) 0 0 false false false in 
				raise (Failure (Printf.sprintf "Variable %s not found in the store. Cur_which_pred: %d. cur_cmd: %s. prev_cmd: %s" x_live cur_which_pred cur_cmd_str prev_cmd_str))
			| Some v -> v)) in 
		if (!verbose) then Printf.printf "PHI-Assignment: %s : %d/%d : %s := %s\n" 
		   (match x_live with
			  | None -> "NONE!" 
				| Some x_live -> x_live) cur_which_pred (Array.length x_arr - 1) x (JSIL_Print.string_of_literal v false);
		Hashtbl.replace store x v; 
		evaluate_next_command prog proc which_pred heap store cur_cmd prev_cmd cc_tbl vis_tbl
								
																						 		
let evaluate_prog prog which_pred heap cc_tbl vis_tbl = 
	Random.self_init();
	let store = init_store [] [] in 
	evaluate_cmd prog "main" which_pred heap store 0 0 cc_tbl vis_tbl
