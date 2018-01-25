(***
 SJSIL - Interpreter
*)
open Batteries
open JSIL_Syntax
(* JAVERT open Symbolic_State *)

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
	| UTCTime ->
			let t = Unix.gettimeofday() in
			let (usec, _) = Float.modf t in
			let gct = Unix.gmtime t in
			let (gctime, _) = Unix.mktime gct in
			let gctime = gctime +. usec in
			let (_, tg) = Float.modf (gctime *. 1e+3) in
				Num (float_of_int (int_of_float tg))
	| LocalTime ->
		  let t = Unix.gettimeofday() in
			let (usec, _) = Float.modf t in
			let lct = Unix.localtime t in
			let (lctime, _) = Unix.mktime lct in
			let lctime = lctime +. usec in
			let (_, tl) = Float.modf (lctime *. 1e+3) in
				Num (float_of_int (int_of_float tl))

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

(* Default objects - create two objects - the "real" one and the metadata one *)
let create_default_object proto cls ext =
	let obj : (permission * jsil_lit) SHeap.t = SHeap.create 1021 in
	let mtd : (permission * jsil_lit) SHeap.t = SHeap.create 1021 in
		SHeap.add mtd "@proto"      (Readable, Loc proto);
		SHeap.add mtd "@class"      (Readable, String cls);
		SHeap.add mtd "@extensible" (Mutable,  Bool ext);
		obj, mtd

(* Call-construct objects *)
let create_object_with_call_construct call construct len =
	let obj, mtd = create_default_object "$lfun_proto" "Function" true in
		SHeap.add     obj "length"     (Deletable, LList [String "d"; Num len; Bool false; Bool false; Bool false]);
		SHeap.replace mtd "@call"      (Readable, String call);
		SHeap.replace mtd "@construct" (Readable, String construct);
		SHeap.replace mtd "@scope"     (Readable, Empty);
		obj, mtd

(* Function objects - with heap addition *)
let create_anonymous_function_object (heap : jsil_heap) call construct params =
	let len = float_of_int (List.length params) in

	let lobj = fresh_loc () in
	let lmtd = fresh_loc () in

	let obj, mtd = create_object_with_call_construct call construct len in

		SHeap.replace mtd "@scope" (Readable, LList [ Loc "$lg" ]);

		SHeap.replace mtd "@formalParameters" (Readable,  LList (List.map (fun x -> String x) params));
		SHeap.add     obj "caller"            (Deletable, LList [(String "a"); Loc "$lthrow_type_error"; Loc "$lthrow_type_error"; Bool false; Bool false]);
		SHeap.add     obj "arguments"         (Deletable, LList [(String "a"); Loc "$lthrow_type_error"; Loc "$lthrow_type_error"; Bool false; Bool false]);

		let lproto    : string = fresh_loc () in
		let lprotomtd : string = fresh_loc () in
		let proto_obj, proto_mtd = create_default_object "$lobj_proto" "Object" true in
			SHeap.add proto_obj "constructor" (Deletable, LList [String "d"; Loc lobj; Bool true; Bool false; Bool true]);
			SHeap.add obj       "prototype"   (Deletable, LList [String "d"; Loc lproto; Bool true; Bool false; Bool false]);

			(* Add to the heap *)
			SHeap.add heap lproto    (proto_obj, Loc lprotomtd, true);
			SHeap.add heap lprotomtd (proto_mtd, Null,          true);
			SHeap.add heap lobj      (obj, Loc lmtd, true);
			SHeap.add heap lmtd      (mtd, Null,     true);

			lobj

(* END SPECIAL STUFF *)

let unary_int_thing lit (f : float -> float) emsg =
	let num =
		(match lit with
 		  | Num n -> n
			| _ -> raise (Failure (Printf.sprintf "%s : %s" emsg (JSIL_Print.string_of_literal lit)))) in
	let res = f num in
		Num res

let evaluate_unop op lit =
	match op with
  | Not ->
		(match lit with
		| Bool b -> (Bool (not b))
		| _ -> raise (Failure (Printf.sprintf "Non-bool argument to Not: %s" (JSIL_Print.string_of_literal lit))))
	| UnaryMinus -> unary_int_thing lit (fun x -> (-. x)) "unary minus called with something other than a number"
	| BitwiseNot -> unary_int_thing lit int32_bitwise_not "bitwise not called with something other than a number"
	| M_abs   -> unary_int_thing lit abs_float "bitwise not called with something other than a number"
	| M_acos  -> unary_int_thing lit acos "acos called with something other than a number"
	| M_asin  -> unary_int_thing lit asin "asin called with something other than a number"
	| M_atan  -> unary_int_thing lit atan "atan called with something other than a number"
	| M_ceil  -> unary_int_thing lit ceil "ceil called with something other than a number"
	| M_cos   -> unary_int_thing lit cos "cos called with something other than a number"
	| M_exp   -> unary_int_thing lit exp "exp called with something other than a number"
	| M_floor -> unary_int_thing lit floor "floor called with something other than a number"
	| M_log   -> unary_int_thing lit log "log called with something other than a number"
	| M_round ->
		(match lit with
		| Num n -> Num (let sign = copysign 1.0 n in
										if ((sign < 0.0) && (n >= -0.5))
										then (-0.0)
										else (floor (n +. 0.5))
									 )
		| _ -> raise (Failure (Printf.sprintf "round function called with %s instead of a number." (JSIL_Print.string_of_literal lit))))
	| M_sgn  -> unary_int_thing lit (fun x -> copysign 1.0 x) "sgn called with something other than a number"
	| M_sin  -> unary_int_thing lit sin "sin called with something other than a number"
	| M_sqrt -> unary_int_thing lit sqrt "sqrt called with something other than a number"
	| M_tan  -> unary_int_thing lit tan "tan called with something other than a number"
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
		| _ -> raise (Failure (Printf.sprintf "Non-number argument to ToStringOp: %s" (JSIL_Print.string_of_literal lit))))
	| ToIntOp    -> unary_int_thing lit to_int "to_int called with something other than a number"
	| ToUint16Op -> unary_int_thing lit to_uint16 "to_uint16 called with something other than a number"
	| ToInt32Op  -> unary_int_thing lit to_int32 "to_int32 called with something other than a number"
	| ToUint32Op -> unary_int_thing lit to_uint32 "log called with something other than a number"
	| ToNumberOp ->
		(match lit with
		 | String s ->
			 let num = try Float.of_string s
				 with Failure "float_of_string" ->
					 if s = "" then 0. else nan in
				 Num num
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
		| _ -> raise (Failure (Printf.sprintf "Non-list argument to LstLen: %s" (JSIL_Print.string_of_literal lit))))
	| StrLen ->
		(match lit with
		| String s -> Num (float_of_int (String.length s))
		| _ -> raise (Failure (Printf.sprintf "Non-string argument to StrLen: %s" (JSIL_Print.string_of_literal lit))))

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

let unary_bin_thing_num lit1 lit2 (f : float -> float -> float) emsg =
	let num1, num2 =
		(match lit1, lit2 with
 		  | Num n1, Num n2 -> n1, n2
			| _ -> raise (Failure (Printf.sprintf "%s : %s, %s" emsg (JSIL_Print.string_of_literal lit1) (JSIL_Print.string_of_literal lit2)))) in
	let res = f num1 num2 in
		Num res

let unary_bin_thing_bool lit1 lit2 (f : float -> float -> bool) emsg =
	let num1, num2 =
		(match lit1, lit2 with
 		  | Num n1, Num n2 -> n1, n2
			| _ -> raise (Failure (Printf.sprintf "%s : %s, %s" emsg (JSIL_Print.string_of_literal lit1) (JSIL_Print.string_of_literal lit2)))) in
	Bool (f num1 num2)

let rec evaluate_binop op e1 e2 store =
	(match op with
	| And ->
        let lit1 = evaluate_expr e1 store in
        (match lit1 with
        | Bool false -> Bool false
        | Bool true ->
            (match evaluate_expr e2 store with
	        | Bool b2 -> Bool b2
            | _ ->  raise (Failure "Non-boolean argument to And"))
        | _ -> raise (Failure "Non-boolean argument to And"))
    | Or ->
        let lit1 = evaluate_expr e1 store in
        (match lit1 with
        | Bool true -> Bool true
        | Bool false ->
            (match evaluate_expr e2 store with
	        | Bool b2 -> Bool b2
            | _ ->  raise (Failure "Non-boolean argument to Or"))
        | _ -> raise (Failure "Non-boolean argument to Or"))
	| _ ->
    let lit1 = evaluate_expr e1 store in
    let lit2 = evaluate_expr e2 store in
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
		| LList l1, LList l2 -> (Bool (l1 = l2))
		| _, _ -> Bool false)
	| LessThan -> unary_bin_thing_bool lit1 lit2 (fun x y -> x < y) "Non-number arguments to LessThan"
	| LessThanString ->
		(match lit1, lit2 with
		| String s1, String s2 -> (Bool (s1 < s2))
		| _, _ -> raise (Failure "Non-string arguments to LessThanString"))
	| LessThanEqual -> unary_bin_thing_bool lit1 lit2 (fun x y -> x <= y) "Non-number arguments to LessThanEqual"
	| Plus  -> unary_bin_thing_num lit1 lit2 (fun x y -> x +. y) "Non-number arguments to Plus"
	| Minus -> unary_bin_thing_num lit1 lit2 (fun x y -> x -. y) "Non-number arguments to Minus"
	| Times -> unary_bin_thing_num lit1 lit2 (fun x y -> x *. y) "Non-number arguments to Times"
	| Div   -> unary_bin_thing_num lit1 lit2 (fun x y -> x /. y) "Non-number arguments to Div"
	| Mod   -> unary_bin_thing_num lit1 lit2 mod_float "Non-number arguments to Mod"
	| BitwiseAnd -> unary_bin_thing_num lit1 lit2 int32_bitwise_and "Non-number arguments to BitwiseAnd"
	| BitwiseOr -> unary_bin_thing_num lit1 lit2 int32_bitwise_or "Non-number arguments to BitwiseOr"
	| BitwiseXor -> unary_bin_thing_num lit1 lit2 int32_bitwise_xor "Non-number arguments to BitwiseXor"
	| LeftShift -> unary_bin_thing_num lit1 lit2 int32_left_shift "Non-number arguments to LeftShift"
	| SignedRightShift -> unary_bin_thing_num lit1 lit2 int32_right_shift "Non-number arguments to SignedRightShift"
	| UnsignedRightShift -> unary_bin_thing_num lit1 lit2 uint32_right_shift  "Non-number arguments to UnsignedRightShift"
	| M_atan2 -> unary_bin_thing_num lit1 lit2 atan2 "Non-number arguments to atan2"
	| M_pow -> unary_bin_thing_num lit1 lit2 (fun x y -> x ** y)  "Non-number arguments to Power"
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
		| _, _ -> raise (Failure (Printf.sprintf "Non-list argument to LstCat: %s @ %s" (JSIL_Print.string_of_literal lit1) (JSIL_Print.string_of_literal lit2))))
	| StrCat ->
		(match lit1, lit2 with
		| String s1, String s2 -> (String (s1 ^ s2))
		| _, _ -> raise (Failure (Printf.sprintf "Non-string argument to StrCat: %s, %s" (JSIL_Print.string_of_literal lit1) (JSIL_Print.string_of_literal lit2))))
    | _ -> Printf.printf "Unsupported binary operator: %s\n" (JSIL_Print.string_of_binop op); exit 1)
and
evaluate_expr (e : jsil_expr) store =
	match e with
	| Literal l ->
		(match l with
		| Constant c -> evaluate_constant c
		| x -> x)

	| Var x ->
		(match Utils.try_find store x with
		| None ->
			let err_msg = Printf.sprintf "Variable %s not found in the store" x in
			let store_str = JSIL_Print.string_of_store store in
			if (!verbose) then Printf.printf "The current store is: \n%s" store_str;
			raise (Failure err_msg)
		| Some v -> v)

	| BinOp (e1, bop, e2) ->
		evaluate_binop bop e1 e2 store

	| UnOp (unop, e) ->
		let v = evaluate_expr e store in
		evaluate_unop unop v

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
		| LList list, Num n when (Utils.is_int n) ->
				List.nth list (int_of_float n)
		| LList list, Num -0. -> List.nth list 0
		| _, _ -> raise (Failure (Printf.sprintf "Incorrect argument to LstNth: %s, %s" (JSIL_Print.string_of_literal v) (JSIL_Print.string_of_literal n))))

	| StrNth (e1, e2) ->
		let v = evaluate_expr e1 store in
		let n = evaluate_expr e2 store in
		(match v, n with
		| String s, Num n when (Utils.is_int n) ->
				String (String.make 1 (String.get s (int_of_float n)))
		| String s, Num -0. ->
				String (String.make 1 (String.get s 0))
		| _, _ -> raise (Failure (Printf.sprintf "Incorrect argument to StrNth: %s, %s" (JSIL_Print.string_of_literal v) (JSIL_Print.string_of_literal n))))

	| _ -> raise (Failure (Printf.sprintf "Unknown expression: %s" (JSIL_Print.string_of_expression e)))

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




let rec evaluate_bcmd bcmd (heap : jsil_heap) store =
	let string_of_op = Option.map_default JSIL_Print.string_of_permission "" in 

	match bcmd with
	| SSkip -> Empty

	| SAssignment (x, e) ->
		let v_e = evaluate_expr e store in
		if (!verbose) then Printf.printf "Assignment: %s := %s\n" x (JSIL_Print.string_of_literal v_e);
		Hashtbl.replace store x v_e;
		v_e

	| SNew (x, metadata) ->
		let new_loc      = fresh_loc () in
		let metadata_val = 
			(match metadata with 
			| None          -> Null 
			| Some metadata -> evaluate_expr metadata store) in
		
		let obj = SHeap.create 1021 in
		SHeap.add heap new_loc (obj, metadata_val, true);
		Hashtbl.replace store x (Loc new_loc);
		Loc new_loc

	| SLookup (x, e1, e2) ->
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in
		(match v_e1, v_e2 with
		| Loc l, String f ->
			let (obj : (permission * jsil_lit) SHeap.t), _, _ = (try SHeap.find heap l with
			| _ -> raise (Failure (Printf.sprintf "Looking up inexistent object: %s" (JSIL_Print.string_of_literal v_e1)))) in
			let _, v = (try SHeap.find obj f with
				| _ ->
					(* let final_heap_str = JSIL_Print.sexpr_of_heap heap in
					Printf.printf "Final heap: \n%s\n" final_heap_str; *)
					raise (Failure (Printf.sprintf "Looking up inexistent field: [%s, %s]" (JSIL_Print.string_of_literal v_e1) (JSIL_Print.string_of_literal v_e2)))) in

			Hashtbl.replace store x v;
			if (!verbose) then Printf.printf "Lookup: %s := [%s, %s] = %s \n" x (JSIL_Print.string_of_literal v_e1) (JSIL_Print.string_of_literal v_e2) (JSIL_Print.string_of_literal v);
			v
		| _, _ -> raise (Failure (Printf.sprintf "Illegal field inspection: [%s, %s]" (JSIL_Print.string_of_literal v_e1) (JSIL_Print.string_of_literal v_e2))))

	| SMutation (e1, e2, e3, op) ->
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in
		let v_e3 = evaluate_expr e3 store in

		let str_of_mutacao : string = JSIL_Print.string_of_bcmd None (SMutation (Literal v_e1, Literal v_e2, Literal v_e3, op)) in
		let error_msg      = "Illegal Mutation: " ^ str_of_mutacao in

		(match v_e1, v_e2 with
		| Loc l, String f ->
			if (SHeap.mem heap l)
			then
				let obj, metadata, ext = SHeap.find heap l in ();

				if (SHeap.mem obj f) then (

					let f_p, _ = SHeap.find obj f in 
					(match op with
					| None                  -> SHeap.replace obj f (f_p, v_e3)
					| Some p when (f_p = p) -> SHeap.replace obj f (f_p, v_e3)
					| _                     -> raise (Failure error_msg))
				) else (
					match ext, op with 
					| false, _     -> raise (Failure error_msg)
					| true, Some p -> SHeap.replace obj f (p, v_e3)
					| true, None   -> SHeap.replace obj f (Deletable, v_e3)
				);
				if (!verbose) then Printf.printf "Mutation: %s\n" str_of_mutacao;
				v_e3
			else
				let obj = SHeap.create 1021 in
				SHeap.add heap l (obj, Null, true);
				SHeap.replace obj f (Deletable, v_e3);
				(* CAREFUL ABOUT PERMISSIONS - ASSIGNING STH MUTABLE TO BE DELETABLE? NOPE! PERMISSIONS INVARIANT! *)
				if (!verbose) then Printf.printf "Mutation: [%s, %s] = <%s>%s \n" 
						(JSIL_Print.string_of_literal v_e1)(JSIL_Print.string_of_literal v_e2) 
						(string_of_op op) (JSIL_Print.string_of_literal v_e3);
				v_e3
		| _, _ ->  raise (Failure "Illegal field inspection"))

	| SDelete (e1, e2) ->
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in
		(match v_e1, v_e2 with
		| Loc l, String f ->
			(match (SHeap.mem heap l) with
			| false -> raise (Failure (Printf.sprintf "Looking up inexistent object: %s" (JSIL_Print.string_of_literal v_e1)))
			| true -> 
				let obj, ext, _ = SHeap.find heap l in
				(match (SHeap.mem obj f) with 
				| false -> raise (Failure "Field to be deleted does not exist")
				| true -> 
					let f_p, _ = SHeap.find obj f in
					(match f_p with
					| Deletable -> 
						if (!verbose) then Printf.printf "Removing field (%s, %s)!\n" (JSIL_Print.string_of_literal v_e1) (JSIL_Print.string_of_literal v_e2);
						SHeap.remove obj f; 
						Bool true; 
					| _ -> raise (Failure (Printf.sprintf "Object %s not deletable" (JSIL_Print.string_of_literal v_e1))))))
		| _, _ -> raise (Failure "Illegal field deletion"))

	| SDeleteObj e1 ->
		let v_e1 = evaluate_expr e1 store in
		(match v_e1 with
		| Loc l ->
		  (match (SHeap.mem heap l) with
		   | false -> raise (Failure (Printf.sprintf "Attempting to delete inexistent object: %s" (JSIL_Print.string_of_literal v_e1)))
		   | true -> SHeap.remove heap l; Bool true)
		| _ -> raise (Failure (Printf.sprintf "Attempting to delete something that's not an object: %s" (JSIL_Print.string_of_literal v_e1))))

	| SHasField (x, e1, e2) ->
		let v_e1 = evaluate_expr e1 store in
		let v_e2 = evaluate_expr e2 store in
		let pv_e1 = JSIL_Print.string_of_literal v_e1 in
		let pv_e2 = JSIL_Print.string_of_literal v_e2 in
		(match v_e1, v_e2 with
		| Loc l, String f ->
			let obj, _, _ = (try SHeap.find heap l with
			| _ -> raise (Failure (Printf.sprintf "Looking up inexistent object: %s" pv_e1))) in
			let v = Bool (SHeap.mem obj f) in
			Hashtbl.replace store x v;
			if (!verbose) then Printf.printf "hasField: %s := hf (%s, %s) = %s \n" x pv_e1 pv_e2 (JSIL_Print.string_of_literal v);
			v
		| _, _ -> raise (Failure (Printf.sprintf "Illegal Field Check: [%s, %s]" pv_e1 pv_e2)))

	| SGetFields (x, e) ->
		let v_e = evaluate_expr e store in
		(match v_e with
		| Loc l ->
			let obj, _, _ = (try SHeap.find heap l with
			| _ -> raise (Failure (Printf.sprintf "Looking up inexistent object: %s" (JSIL_Print.string_of_literal v_e)))) in
			let fields =
				SHeap.fold
				(fun field (_, value) acc ->
					let t = evaluate_type_of value in
					if (t = ListType) then
						(String field) :: acc
					else
						acc
					) obj [] in
			let v = LList (List.sort compare fields) in
			Hashtbl.replace store x v;
			if (!verbose) then Printf.printf "hasField: %s := gf (%s) = %s \n" x (JSIL_Print.string_of_literal v_e) (JSIL_Print.string_of_literal v);
			v
		| _ -> raise (Failure "Passing non-object value to getFields"))

  | SArguments x ->
		let arg_obj, _, _ = (try SHeap.find heap larguments with
		| _ -> raise (Failure "The arguments object doesn't exist.")) in
		let _, v = (try SHeap.find arg_obj "args" with
		| _ -> raise (Failure "The arguments are not available.")) in
			Hashtbl.replace store x v;
			if (!verbose) then Printf.printf "Arguments: %s := %s \n" x (JSIL_Print.string_of_literal v);
			v
			
	| MetaData (x, e) ->
		let v_e = evaluate_expr e store in
		(match v_e with
		| Loc l ->
				(match (SHeap.mem heap l) with
				| false -> (* !!!!! TOFIX !!!!! *)
						(* Generate empty object with metadata null as metadata *) 
						let m = SHeap.create 1021 in
						let lm = fresh_loc () in
						SHeap.replace heap lm (m, Null, true);
						
						(* Generate new object in the heap *)
						let o = SHeap.create 1021 in
						SHeap.replace heap l (o, Loc lm, true);
						Loc lm
						
				| true -> 
						let _, metadata, _ = SHeap.find heap l in
							metadata) 
		| _ -> raise (Failure (Printf.sprintf "Looking up metadata of non-object: %s" (JSIL_Print.string_of_literal v_e))))	

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
			List.iter (fun x -> Printf.printf "%s " (JSIL_Print.string_of_literal x)) args;
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

	let str_store = JSIL_Print.string_of_store new_store in
	if (!verbose) then Printf.printf "I have just initialized the following store\n %s \n" str_store;
	new_store

let rec evaluate_cmd 
			prog 
			cur_proc_name 
			which_pred 
			(heap : jsil_heap) 
			store 
			cur_cmd prev_cmd cc_tbl vis_tbl =

	let execute_function_constructor proc x e_args j = (
			(* Printf.printf "\nFunction call or constructor encountered.\n"; *)

			(* let len = List.length e_args in
			let args n = (evaluate_expr (List.nth e_args n) store) in
			Printf.printf "Arguments: ";
			for i = 0 to (len - 1) do
				Printf.printf "%d: %s " i (JSIL_Print.string_of_literal (args i) false);
			done;
			Printf.printf "\n";  *)

			let se = (evaluate_expr (Var (JS2JSIL_Constants.var_se)) store) in

			let error = ref false in
			let propagate = ref false in
			let message = ref "" in
			let retvalue = ref Empty in

			let throw_syntax_error message =
				((* Printf.printf "SYNTAX ERROR: %s\n" message; *)
				 let throw_value = if !propagate then !retvalue else se in
				 let tse =
					(match j with
				  	| None -> raise (Failure "procedure throws an error without an error label")
					  | Some j ->
						  	Hashtbl.replace store x throw_value;
								evaluate_cmd prog cur_proc_name which_pred heap store j cur_cmd cc_tbl vis_tbl) in
						tse) in

			let argCount = (List.length e_args - 2) in
			let params = ref "" in
			let body = ref "" in
			if (argCount = 0) then () else
			begin
				if (argCount = 1) then
				let bd = List.nth e_args 2 in
					let ebd = evaluate_expr bd store in
  					(* Do the "toString"! *)
  					let new_store = init_store ["v"] [ebd] in
						if (!verbose) then
						  begin
							  Printf.printf "FC: Body: i__toString with %s.\n" (JSIL_Print.string_of_literal ebd);
						  end;
        		(match evaluate_cmd prog "i__toString" which_pred heap new_store 0 0 cc_tbl vis_tbl with
        		| Normal, v -> (match v with
						                 | String bd -> body := bd
      					             | _ -> message := Printf.sprintf "toString didn't return string!"; propagate := false; error := true)
        		| Error, v -> message := "Couldn't do toString!"; propagate := true; retvalue := v; error := true);
				else
			  	let firstArg = List.nth e_args 2 in
					let evalFirstArg = evaluate_expr firstArg store in
					let new_store = init_store ["v"] [evalFirstArg] in
					if (!verbose) then
						begin
							Printf.printf "FC: Params: 1: i__toString with %s.\n" (JSIL_Print.string_of_literal evalFirstArg);
						end;
        	(match evaluate_cmd prog "i__toString" which_pred heap new_store 0 0 cc_tbl vis_tbl with
        		| Normal, v -> (match v with
						                 | String efa -> params := efa
      					             | _ -> message := Printf.sprintf "toString didn't return string!"; propagate := false; error := true)
        		| Error, v -> message := "Couldn't do toString!"; propagate := true; retvalue := v; error := true);
					if (not !error) then
					begin
					for i = 3 to argCount do
						let arg = List.nth e_args i in
						let evalArg = evaluate_expr arg store in
					  let new_store = init_store ["v"] [evalArg] in
						if (!verbose) then
						  begin
							  Printf.printf "FC: Params: %d: i__toString with %s.\n" (i-2) (JSIL_Print.string_of_literal evalArg);
						  end;
        		(match evaluate_cmd prog "i__toString" which_pred heap new_store 0 0 cc_tbl vis_tbl with
        			| Normal, v -> (match v with
						   	              | String efa -> params := !params ^ ", " ^ efa
      						             | _ -> message := Printf.sprintf "toString didn't return string!"; propagate := false; error := true)
        			| Error, v -> message := "Couldn't do toString!"; propagate := true; retvalue := v; error := true);
					done;
					if (not !error) then
					begin
					let bd = List.nth e_args (argCount + 1) in
					let ebd = evaluate_expr bd store in
  					(* Do the "toString"! *)
  					let new_store = init_store ["v"] [ebd] in
						if (!verbose) then
						  begin
							  Printf.printf "FC: Body: i__toString with %s.\n" (JSIL_Print.string_of_literal ebd);
						  end;
        		(match evaluate_cmd prog "i__toString" which_pred heap new_store 0 0 cc_tbl vis_tbl with
        		| Normal, v -> (match v with
						                 | String bd -> body := bd
      					             | _ -> Printf.printf "Body toString fail: %s\n" (JSIL_Print.string_of_literal v);
														        message := Printf.sprintf "toString didn't return string!"; propagate := false; error := true)
        		| Error, v -> message := "Couldn't do toString!"; propagate := true; retvalue := v; error := true)
					end;
					end;
      end;

			(* Printf.printf "Error status: %b, message: %s\n" !error !message; *)

			if (!error) then (throw_syntax_error !message) else
			begin

				propagate := false; retvalue := Empty;

  			(* Parsing the parameters as a FormalParametersList *)
  			let lexbuf = Lexing.from_string !params in
  			let parsed_params =
  				(try (Some (JSIL_Syntax_Utils.parse JSIL_Parser.Incremental.param_list_FC_target lexbuf)) with
  				 | _ -> None) in
  			(match parsed_params with
  			| None -> throw_syntax_error "Parameters not parseable."
  			| Some parsed_params ->
  				let len = List.length parsed_params in

  				let string_of_parsed_params = String.concat ", " parsed_params in
    			Printf.printf "Parsed parameters: %s\n" string_of_parsed_params;

  				(* Parsing the body as a FunctionBody *)
  				let e_body = (evaluate_expr (Literal (String !body)) store) in
  				(match e_body with
  				| String code ->
  					let code = Str.global_replace (Str.regexp (Str.quote "\\\"")) "\"" code in
  					let code = "function THISISANELABORATENAME (" ^ string_of_parsed_params ^ ") {" ^ code ^ "}" in

  					(* Printf.printf "\n\tParsing body: %s\n\n" code; *)

  					let e_js =
  						(try (Some (Parser_main.exp_from_string ~force_strict:true code)) with
  					   | _ -> None) in
  					(match e_js with
  					| None -> throw_syntax_error "Body not parsable."
      			| Some e_js ->
  							(match e_js.Parser_syntax.exp_stx with
  							  | Script (_, le) ->
  									(match le with
  									| e :: [] ->
  										(match e.Parser_syntax.exp_stx with
  										| Parser_syntax.Function (_, Some "THISISANELABORATENAME", params, body) ->
  												let new_proc = JS2JSIL_Compiler.js2jsil_function_constructor_prop prog which_pred cc_tbl vis_tbl cur_proc_name params body in
  												let fun_name = new_proc.proc_name in
  												let vis_tbl = (match vis_tbl with
  												                | Some t -> t
  																| None -> raise (Failure "No visibility table")) in
  												let new_loc = create_anonymous_function_object heap fun_name fun_name params in
  												Hashtbl.replace store x (Loc new_loc);
  					 							evaluate_next_command prog proc which_pred heap store cur_cmd prev_cmd cc_tbl (Some vis_tbl)

  										| _ -> throw_syntax_error "Body not an anonymous function.")
  									| _ -> throw_syntax_error "More than a function body in the string.")
  								| _ -> throw_syntax_error "Not a script."))

  				| _ -> throw_syntax_error "Body not a string.")
        )
			end) in

	let execute_procedure_body proc x e e_args j = (
		let call_proc_name_val = evaluate_expr e store in
		let call_proc_name = (match call_proc_name_val with
			| String call_proc_name ->
				if (!verbose) then Printf.printf "\nExecuting procedure %s\n" call_proc_name;
				call_proc_name
			| _ -> raise (Failure (Printf.sprintf "Erm, no. Procedures can't be called %s." (JSIL_Print.string_of_literal call_proc_name_val)))) in
		let arg_vals = List.map (fun e_arg -> evaluate_expr e_arg store) e_args in
		let call_proc = try Hashtbl.find prog call_proc_name with
			| _ -> raise (Failure (Printf.sprintf "CALL: The procedure %s you're trying to call doesn't exist." call_proc_name)) in
		let new_store = init_store call_proc.proc_params arg_vals in

		(* WHAT THE FUCK IS HAPPENING HERE AND WHY? *)
		if (List.length arg_vals = 0) || (List.nth arg_vals 0 <> String "args") then
		begin
			let args_obj = SHeap.create 1 in
				SHeap.replace args_obj largvals (Readable, LList arg_vals);
				SHeap.replace heap larguments (args_obj, Null, false);
		end;

		(match evaluate_cmd prog call_proc_name which_pred heap new_store 0 0 cc_tbl vis_tbl with
		| Normal, v ->
				if (!verbose) then Printf.printf "Procedure %s normal return: %s := %s\n" call_proc_name x (JSIL_Print.string_of_literal v);
				Hashtbl.replace store x v;
	 			evaluate_next_command prog proc which_pred heap store cur_cmd prev_cmd cc_tbl vis_tbl
		| Error, v ->
			(match j with
			| None -> raise (Failure ("Procedure "^ call_proc_name ^" just returned an error, but no error label was provided. Bad programmer."))
			| Some j ->
					if (!verbose) then Printf.printf "Procedure %s error return: %s := %s\n" call_proc_name x (JSIL_Print.string_of_literal v);
					Hashtbl.replace store x v;
					evaluate_cmd prog cur_proc_name which_pred heap store j cur_cmd cc_tbl vis_tbl))) in

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
		| _ -> raise (Failure (Printf.sprintf "So you're really trying to do a goto based on %s? Ok..." (JSIL_Print.string_of_literal v_e))))

	| SCall (x, e, e_args, j)
		when  evaluate_expr e store = String "Object_eval" ->
		if (!verbose) then Printf.printf "Call to eval intercepted!\n"; 
		if (!verbose) then print_endline (Printf.sprintf "Arguments: %s" (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_expression x) e_args)));
 		if (!verbose) then print_endline (Printf.sprintf "The store is: %s" (JSIL_Print.string_of_store store));
		let e_args =
			(if (List.length e_args < 3) then (List.append e_args [Literal Undefined]) else e_args) in
		let str_e = List.nth e_args 2 in
		let str_e = (evaluate_expr str_e store) in
		(match str_e with
		| String code ->
				let code = Str.global_replace (Str.regexp (Str.quote "\\\"")) "\"" code in
				(* Printf.printf "\n%s\n" code; *)
				let x_scope, x_this =
					(match Utils.try_find store (JS2JSIL_Constants.var_scope), Utils.try_find store (JS2JSIL_Constants.var_this)  with
 					| Some x_scope, Some x_this -> x_scope, x_this
 					| None, None -> raise (Failure "No var_scope AND no var_this to give to eval")
 					| None, _ -> raise (Failure "No var_scope to give to eval") 
 					| _, None -> raise (Failure "No var_this to give to eval")) in
				if (!verbose) then Printf.printf "Scope: %s\nThis: %s\n" (JSIL_Print.string_of_literal x_scope) (JSIL_Print.string_of_literal x_this);
				(match (try
					let e_js = Parser_main.exp_from_string ~force_strict:true code in
					Some (JS2JSIL_Compiler.js2jsil_eval prog which_pred cc_tbl vis_tbl cur_proc_name e_js)
					with _ -> None) with
				| Some proc_eval ->
					(let new_store = init_store [ JS2JSIL_Constants.var_scope; JS2JSIL_Constants.var_this ] [ x_scope; x_this ] in
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
					(match Utils.try_find store (JS2JSIL_Constants.var_se), j with
					| Some v, Some j ->
						Hashtbl.replace store x v;
						evaluate_cmd prog cur_proc_name which_pred heap store j cur_cmd cc_tbl vis_tbl
					| _, None -> raise (Failure ("Procedure "^ cur_proc_name ^" just returned an error, but no error label was provided. Bad programmer."))
					| _, _ -> raise (Failure "No Syntax Error for you, no noooo!")))

		| _ -> Hashtbl.replace store x str_e;
					 evaluate_next_command prog proc which_pred heap store cur_cmd prev_cmd cc_tbl vis_tbl)

	| SCall (x, e, e_args, j)
	  when ((evaluate_expr e store = String "Function_call") || (evaluate_expr e store = String "Function_construct")) ->
			(* Printf.printf "Call: Entering FC from %s\n"  (JSIL_Print.string_of_literal (evaluate_expr e store) false); *)
			execute_function_constructor proc x e_args j

	| SCall (x, e, e_args, j) ->
		  (* Printf.printf "Nothing was intercepted!!!\n"; *)
		  execute_procedure_body proc x e e_args j

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
				let fargs = flatten args in
				(* Printf.printf "Flattened: ";
				let len = List.length fargs in
				for i = 0 to (len - 1) do
					let lit = List.nth fargs i in
					Printf.printf "%s " (JSIL_Print.string_of_literal lit false);
				done;
				Printf.printf "\n"; *)
				fargs
			| _ -> raise (Failure "Nope!")) in
		(match args with
  		| [] -> raise (Failure "No no no. Not at all")
  		| call_proc_name_val :: arg_vals ->
			  let e_args = List.tl e_args in
				let call_proc_name = (match call_proc_name_val with
  		                         | String call_proc_name ->
  				                       if (!verbose) then Printf.printf "\nExecuting procedure %s\n" call_proc_name; call_proc_name
  		                         | _ -> raise (Failure (Printf.sprintf "No. You can't call a procedure %s." (JSIL_Print.string_of_literal call_proc_name_val)))) in
				let new_args = ((List.map (fun x -> (Literal x))) (List.tl args)) in
				if ((call_proc_name = "Function_call") || (call_proc_name = "Function_construct"))
				then
				begin
					(* Printf.printf "Apply: Entering FC from apply.\n"; *)
					execute_function_constructor proc x new_args j
				end
				else
					execute_procedure_body proc x (Literal call_proc_name_val) new_args j)

				(*
  		let call_proc_name = (match call_proc_name_val with
  		| String call_proc_name ->
  				if (!verbose) then Printf.printf "\nExecuting procedure %s\n" call_proc_name;
  				call_proc_name
  		| _ -> raise (Failure (Printf.sprintf "No. You can't call a procedure %s." (JSIL_Print.string_of_literal call_proc_name_val false)))) in
  		let call_proc = try Hashtbl.find prog call_proc_name with
  		| _ -> raise (Failure (Printf.sprintf "APPLY: The procedure %s you're trying to call doesn't exist." call_proc_name)) in
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
  				evaluate_cmd prog cur_proc_name which_pred heap store j cur_cmd cc_tbl vis_tbl))) *)

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
			if (!verbose) then Printf.printf ("Procedure %s returned: Normal, %s\n") cur_proc_name (JSIL_Print.string_of_literal ret_value);
			Normal, ret_value)
		else
			(if (Some cur_cmd = proc.error_label)
			then
				(let err_value =
					(let err_var = (match proc.error_var with
					                      | None -> raise (Failure "No no!")
																| Some err_var -> err_var) in
				         (try (Hashtbl.find store err_var) with
				| _ -> raise (Failure (Printf.sprintf "Cannot find error variable in proc %s, err_lab = %d, err_var = %s, cmd = %s" proc.proc_name cur_cmd err_var (JSIL_Print.string_of_cmd 0 0 proc.proc_body.(prev_cmd)))))) in
			if (!verbose) then Printf.printf ("Procedure %s returned: Error, %s\n") cur_proc_name (JSIL_Print.string_of_literal err_value);
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
		let expr = x_arr.(cur_which_pred) in
		let v = evaluate_expr expr store in
		if (!verbose) then Printf.printf "PHI-Assignment: %s : %d/%d : %s := %s\n"
		   (JSIL_Print.string_of_expression expr) cur_which_pred (Array.length x_arr - 1) x (JSIL_Print.string_of_literal v);
		Hashtbl.replace store x v;
		evaluate_next_command prog proc which_pred heap store cur_cmd prev_cmd cc_tbl vis_tbl


let evaluate_prog prog which_pred heap cc_tbl vis_tbl =
	Random.self_init();
	let store = init_store [] [] in
	evaluate_cmd prog "main" which_pred heap store 0 0 cc_tbl vis_tbl
