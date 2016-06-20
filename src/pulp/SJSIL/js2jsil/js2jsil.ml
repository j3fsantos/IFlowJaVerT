open Utils
open Lexing
open Batteries
open SSyntax

let js2jsil_imports = [
	"Array"; 
	"Boolean";
	"Function"; 
	"Global";
	"Init";
	"Internals";
	"Math"; 
	"Number"; 
	"Object"; 
	"String";
	"Errors"
]

let setupHeapName = "setupInitialHeap"

let callPropName       = "@call"
let constructPropName  = "@construct"
let scopePropName      = "@scope"
let classPropName      = "@class"
let extensiblePropName = "@extensible"

let locGlobName        = "$lg"
let locObjPrototype    = "$lobj_proto"

let toBooleanName                     = "i__toBoolean"                   (* 9.2               *)
let getValueName                      = "i__getValue"                    (* 8.7.1             *)
let isReservedName                    = "i__isReserved"
let putValueName                      = "i__putValue"                    (* 8.7.2             *) 
let createDefaultObjectName           = "create_default_object"          (* 15.2.2.1          *)
let toObjectName                      = "i__toObject"                    (* 9.9               *)
let toStringName                      = "i__toString"                    (* 9.8               *)
let deletePropertyName                = "o__deleteProperty"              (* 8.12.7            *)
let syntaxErrorName                   = "SyntaxError"                    (* 15.1.4.13         *)
let typeErrorName                     = "TypeError"                      (* 15.1.4.14         *) 
let createFunctionObjectName          = "create_function_object"
let isCallableName                    = "i__isCallable"
let copyObjectName                    = "copy_object"
let checkObjectCoercibleName          = "i__checkObjectCoercible"
let jsTypeOfName                      = "i__typeOf"                      (* 11.4.3 - Table 20 *) 
let toNumberName                      = "i__toNumber"                    (* 9.3 - Table 12    *) 
let toPrimitiveName                   = "i__toPrimitive"                 (* 9.1 - Table 10    *) 
let toInt32Name                       = "i__toInt32"                     (* 9.5               *)
let toUInt32Name                      = "i__toUint32"                    (* 9.6               *)
let abstractComparisonName            = "i__abstractComparison"          (* 11.8.5            *) 
let hasInstanceName                   = "i__hasInstance"                 (* 15.3.5.3          *)
let hasPropertyName                   = "o__hasProperty"                 (* 8.12.6            *)
let abstractEqualityComparisonName    = "i__abstractEquality"            (* 11.9.3            *) 
let strictEqualityComparisonName      = "i__strictEquality"              (* 11.9.6            *) 
let defineOwnPropertyName             = "o__defineOwnProperty"           (* 8.12.9            *) 
let checkAssignmentErrorsName         = "i__checkAssignmentErrors"        


let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)  
	
let fresh_sth (name : string) : (unit -> string) =
  let counter = ref 0 in
  let rec f () =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f
  
let fresh_var : (unit -> string) = fresh_sth "x_"

let fresh_scope_chain_var : (unit -> string) = fresh_sth "x_sc_"

let fresh_fun_var : (unit -> string) = fresh_sth "x_f_"

let fresh_obj_var : (unit -> string) = fresh_sth "x_o_"

let fresh_er_var : (unit -> string) = fresh_sth "x_er_"

let fresh_err_var : (unit -> string) = fresh_sth "x_error_"

let fresh_this_var : (unit -> string) = fresh_sth "x_this_"

let fresh_desc_var : (unit -> string) = fresh_sth "x_desc_"

let fresh_body_var : (unit -> string) = fresh_sth "x_body_"

let fresh_fscope_var : (unit -> string) = fresh_sth "x_fscope_"
 
let fresh_label : (unit -> string) = fresh_sth "lab_"

let fresh_next_label : (unit -> string) = fresh_sth "next_"

let fresh_then_label : (unit -> string) = fresh_sth "then_"

let fresh_else_label : (unit -> string) = fresh_sth "else_"

let fresh_endif_label : (unit -> string) = fresh_sth "fi_"

let fresh_end_label : (unit -> string) = fresh_sth "end_"

let fresh_break_label : (unit -> string) = fresh_sth "break_"

let fresh_loop_head_label : (unit -> string) = fresh_sth "loop_h_"

let fresh_loop_cont_label : (unit -> string) = fresh_sth "loop_c_"

let fresh_loop_guard_label : (unit -> string) = fresh_sth "loop_g_"

let fresh_loop_body_label : (unit -> string) = fresh_sth "loop_b_"

let fresh_loop_end_label : (unit -> string) = fresh_sth "loop_e_"

let fresh_tcf_finally_label : (unit -> string) = fresh_sth "finally_"

let fresh_tcf_end_label : (unit -> string) = fresh_sth "end_tcf_"

let fresh_tcf_err_label : (unit -> string) = fresh_sth "err_tcf_"

let fresh_loop_vars () = 
	let head = fresh_loop_head_label () in 
	let end_loop = fresh_loop_end_label () in 
	let cont = fresh_loop_cont_label () in 
	let guard = fresh_loop_guard_label () in 
	let body = fresh_loop_body_label () in 
	head, guard, body, cont, end_loop

let fresh_tcf_vars () = 
	let err = fresh_tcf_err_label () in 
	let end_l = fresh_tcf_end_label () in 
	let finally = fresh_tcf_finally_label () in 
	err, finally, end_l 


let val_var_of_var x = 
	(match x with 
	| Var x_name -> x_name ^ "_v" 
	| Literal l -> (fresh_var ()) ^ "_v"
	| _ -> raise (Failure "val_var_of_var expects a variable or a literal"))

let number_var_of_var x = 
	(match x with 
	| Var x_name -> x_name ^ "_n" 
	| Literal l -> (fresh_var ()) ^ "_n"
	| _ -> raise (Failure "number_var_of_var expects a variable"))

let boolean_var_of_var x = 
	(match x with 
	| Var x_name -> x_name ^ "_b" 
	| Literal l -> (fresh_var ()) ^ "_b"
	| _ -> raise (Failure "boolean_var_of_var expects a variable"))	

let primitive_var_of_var x = 
	(match x with 
	| Var x_name -> x_name ^ "_p" 
	| Literal l -> (fresh_var ()) ^ "_p"
	| _ -> raise (Failure "primitive_var_of_var expects a variable"))				

let string_var_of_var x = 
	(match x with 
	| Var x_name -> x_name ^ "_s" 
	| Literal l -> (fresh_var ()) ^ "_s"
	| _ -> raise (Failure "string_var_of_var expects a variable"))										

let i32_var_of_var x = 
	(match x with 
	| Var x_name -> x_name ^ "_i32" 
	| Literal l -> (fresh_var ()) ^ "_i32"
	| _ -> raise (Failure "string_var_of_var expects a variable"))																												
																																																																																	
let fresh_err_label : (unit -> string) = fresh_sth "err_"

let fresh_ret_label : (unit -> string) = fresh_sth "ret_" 

type tr_ctx = { 
	tr_ret_lab: string; 
	tr_ret_var: string;
	tr_error_lab: string; 
	tr_error_var: string;
}

let make_translation_ctx fid = 
{ 
	tr_ret_lab = "rlab"; (* ^ fid; *)
	tr_ret_var = "xret"; (* ^ fid; *)
	tr_error_lab = "elab"; (* ^ fid; *)
	tr_error_var = "xerr"; (* ^ fid *)
}

let parse str =
  let lexbuf = Lexing.from_string str in
  try SJSIL_Parser.cmd_list_top_target SJSIL_Lexer.read lexbuf with
  | SJSIL_Lexer.SyntaxError msg ->
    Printf.fprintf stderr "%a: %s\n" print_position lexbuf msg;
		[]
  | SJSIL_Parser.Error ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let add_initial_label cmds lab = 
	(match cmds with 
	| [] -> [ (None, Some lab, SLBasic SSkip) ]
	| (_, Some lab_s, _) :: rest -> (None, Some lab, SLBasic SSkip) :: cmds 
	| (spec, None, cmd) :: rest -> (spec, Some lab, cmd) :: rest)

let var_this = "x__this"  
let var_scope = "x__scope"  
let var_se = "x__se"
let var_te = "x__te"


let rec get_break_lab loop_list lab = 
	match loop_list with 
	| [] -> 
		let msg = 
			(match lab with 
			| None -> "breaking outside a loop"
			| Some lab -> Printf.sprintf "either breaking outside a loop or lab %s not found" lab) in 
		raise (Failure msg)
	| (lab_c, lab_b, js_lab) :: rest ->
		match lab with 
		| None -> lab_b 
		| Some lab_str -> 
			(match js_lab with 
			| None ->  get_break_lab rest lab
			| Some js_lab_str -> if (lab_str = js_lab_str) then lab_b else get_break_lab rest lab)

let rec get_continue_lab loop_list lab = 
	match loop_list with 
	| [] -> 
		let msg = 
			(match lab with 
			| None -> "continuing outside a loop"
			| Some lab -> Printf.sprintf "either continuing outside a loop or lab %s not found" lab) in 
		raise (Failure msg)
	| (lab_c, lab_b, js_lab) :: rest ->
		match lab with 
		| None -> 
			(match lab_c with 
			| Some lab_c -> lab_c
			| None -> get_continue_lab rest lab)
		| Some lab_str -> 
			(match js_lab with 
			| None -> get_continue_lab rest lab
			| Some js_lab_str -> 
				if (lab_str = js_lab_str) 
				then 
					(match lab_c with 
					| None -> get_continue_lab rest lab
					| Some lab_c -> lab_c)
				else get_continue_lab rest lab)

let filter_cur_jumps (jumps : (string option * string) list) loop_lab include_no_lab = 
	let rec filter_cur_jumps_iter jumps inner_jumps outer_jumps = 
		match jumps with 
		| [] -> (List.rev inner_jumps), (List.rev outer_jumps) 
		| (None, x) :: rest_jumps ->
			  (match include_no_lab with 
				| true -> filter_cur_jumps_iter rest_jumps (x :: inner_jumps) outer_jumps 
				| false -> filter_cur_jumps_iter rest_jumps inner_jumps ((None, x) :: outer_jumps))  
		| (Some lab, x) :: rest_jumps ->
				(match loop_lab with
				| None ->  filter_cur_jumps_iter rest_jumps inner_jumps ((Some lab, x) :: outer_jumps) 
				| Some loop_lab -> 
						if (loop_lab = lab) 
							then filter_cur_jumps_iter rest_jumps (x :: inner_jumps) outer_jumps 
							else filter_cur_jumps_iter rest_jumps inner_jumps ((Some lab, x) :: outer_jumps)) in 
	filter_cur_jumps_iter jumps [] []

let b_annot_cmd cmd = (None, None, cmd) 		
	
let b_annot_cmds cmds = List.map (fun cmd -> b_annot_cmd cmd) cmds 
	
let add_skip_if_empty cmds x = 
	(match x with 
	| Var _ -> cmds, x
	| Literal lit -> 
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLBasic (SAssignment (x_r, Literal lit)) in 
		cmds @ [ b_annot_cmd cmd_ass_xr ], Var x_r 
	| _ -> raise (Failure "The compiler must always generate a variable or a literal"))

let make_var_ass_se () = SLCall (var_se, Literal (String syntaxErrorName), [ ], None) 
	
let make_var_ass_te () = SLCall (var_te, Literal (String typeErrorName), [ ], None)  	

let add_final_var cmds x = 
	match x with 
	| Var x_name -> cmds, x_name 
	| Literal lit -> 
		let x_new = fresh_var () in 
		let cmd_ass_new = (None, None, SLBasic (SAssignment (x_new, Literal lit))) in 
	 	cmds @ [ cmd_ass_new ], x_new 
	| _ -> raise (Failure "add_final_var: x needs to be a variable or a literal") 

let rec translate fid cc_table ctx vis_fid err loop_list previous js_lab e  = 
	
	let f = translate fid cc_table ctx vis_fid err loop_list previous js_lab in
	
	let f_previous = translate fid cc_table ctx vis_fid err in 
		
	let cur_var_tbl = 
		(try Hashtbl.find cc_table fid 
			with _ -> 
				let msg = Printf.sprintf "var tbl of function %s is not in cc-table" fid in 
				raise (Failure msg)) in 
	
	let find_var_fid v = (try Some (Hashtbl.find cur_var_tbl v) with _ -> None) in 
	
	let non_writable_ref_test x = 
		(* (typeof (x) = $$v-reference_type) and ((field(x) = "eval") or (field(x) = "arguments"))  *) 
		let left_e = BinOp ((TypeOf x), Equal, Literal (Type VariableReferenceType)) in 
		let right_e = BinOp ((BinOp ((Field x), Equal, Literal (String "eval"))), Or, (BinOp ((Field x), Equal, Literal (String "arguments")))) in 
		BinOp (left_e, And, right_e) in
	
	let make_unresolvable_ref_test x = 
		BinOp (BinOp ((Base x), Equal, (Literal Null)), Or, BinOp ((Base x), Equal, (Literal Undefined))) in 
	
	let make_get_value_call x err = 
		(* x_v := getValue (x) with err *)
		let x_v = val_var_of_var x in 
		(x_v, SLCall (x_v, (Literal (String getValueName)), [ x ], Some err)) in
	
	let make_to_number_call x x_v err = 
		let x_n = number_var_of_var x in 
		(x_n, SLCall (x_n, (Literal (String toNumberName)), [ Var x_v ], Some err)) in
	
	let make_to_boolean_call x x_v err = 
		let x_b = boolean_var_of_var x in 
		(x_b, SLCall (x_b, (Literal (String toBooleanName)), [ Var x_v ], Some err)) in
	
	let make_to_primitive_call x x_v err = 
		let x_p = primitive_var_of_var x in 
		(x_p, SLCall (x_p, (Literal (String toPrimitiveName)), [ Var x_v ], Some err)) in
	
	let make_to_string_call x x_v err = 
		let x_s = string_var_of_var x in 
		(x_s, SLCall (x_s, (Literal (String toStringName)), [ Var x_v ], Some err)) in
	
	let make_to_i32_call x x_v err = 
		let x_i32 = i32_var_of_var x in 
		(x_i32,  SLCall (x_i32, (Literal (String toInt32Name)), [ Var x_v ], Some err)) in
	
	let make_put_value_call x x_r err = 
		let x_pv = fresh_var () in 
		(x_pv, SLCall (x_pv, Literal (String putValueName), [x; Var x_r], Some err)) in  
	
	let make_dop_call x_obj prop x_desc b err = 
		let x_dop = fresh_var () in
		(x_dop, SLCall (x_dop, Literal (String defineOwnPropertyName), [Var x_obj; prop; Var x_desc; Literal (Bool b)], Some err)) in 
	
	let make_cae_call x err = 
		let x_cae = fresh_var () in 
		x_cae,  SLCall (x_cae, Literal (String checkAssignmentErrorsName), [ x ], Some err) in
			
	let make_empty_ass () = 
		let x = fresh_var () in 
		let empty_ass = SLBasic (SAssignment (x, (Literal Empty))) in
		x, empty_ass in 
		
	let translate_function_literal fun_id params = 
		(**
       x_sc := copy_scope_chain_obj (x_scope, {{main, fid1, ..., fidn }}); 
		   x_f := create_function_object(x_sc, fun_id, params)
   	*)
		
		(* x_sc := copy_object (x_sc, {{main, fid1, ..., fidn }});  *)
		let x_sc = fresh_scope_chain_var () in 
		let vis_fid_strs = List.map (fun fid -> String fid) vis_fid in   
		let cmd_sc_copy = SLCall (x_sc, Literal (String copyObjectName), 
			[ (Var var_scope); Literal (LList vis_fid_strs) ], None) in 
		
		(* x_f := create_function_object(x_sc, f_id, params) *)
		let x_f = fresh_fun_var () in 
		let processed_params = 
			List.fold_left
				(fun ac param -> (String param) :: ac) 
				[]
				params in 
		let processed_params = List.rev processed_params in 
		let cmd = SLCall (x_f, Literal (String createFunctionObjectName), 
			[ (Var x_sc); (Literal (String fun_id)); (Literal (String fun_id)); (Literal (LList processed_params)) ], None) in 	
		
		[ 
		  (None, None, cmd_sc_copy);            (* x_sc := copy_object (x_scope, {{main, fid1, ..., fidn }});  *)
			(None, None, cmd)                     (* x_f := create_function_object (x_sc, f_id, f_id, params)    *)
		], x_f in 
		
				
	let translate_inc_dec x is_plus err = 	
		(** 
			        goto [ (typeof (x) = $$v-reference_type) and ((field(x) = "eval") or (field(x) = "arguments")) ] err next
			 next:  x_v := getValue (x) with err 
						  x_n := i__toNumber (x_v) with err 
							x_r := x_n +/- 1
						  x_pv := putValue (x, x_r) with err 
    *)
		
		(* goto [ (typeof (x) = $$v-reference_type) and ((field(x) = "eval") or (field(x) = "arguments")) ] err next *)
		let next = fresh_label () in 
		let cmd_goto_legalass = SLGuardedGoto ((non_writable_ref_test x), err, next) in 
		
		(* next:  x_v := getValue (x) with err *) 
		let x_v, cmd_gv_x = make_get_value_call x err in
		
		(* x_n := i__toNumber (x_v) with err *) 
		let x_n, cmd_tn_x = make_to_number_call x x_v err in 
		
		(* x_r := x_n +/- 1 *) 
		let x_r = fresh_var () in 
		let cmd_ass_xr = 
			(match is_plus with 
			| true -> SLBasic (SAssignment (x_r, (BinOp (Var x_n, Plus, Literal (Num 1.))))) 
			| false -> SLBasic (SAssignment (x_r, (BinOp (Var x_n, Minus, Literal (Num 1.)))))) in 
		
		(* x_pv = putValue (x, x_r) with err4 *) 
		let x_pv, cmd_pv_x = make_put_value_call x x_r err in 
		
		let new_cmds = [      
			(None, None,      cmd_goto_legalass);                (*        goto [ (typeof (x) = $$v-reference_type) and ((field(x) = "eval") or (field(x) = "arguments")) ] err next   *)
			(None, Some next, cmd_gv_x);                         (* next:  x_v := i__getValue (x) with err                                                                             *)    
			(None, None,      cmd_tn_x);                  	     (*        x_n := i__toNumber (x_v) with err                                                                           *) 
		  (None, None,      cmd_ass_xr);                       (*        x_r := x_n + 1                                                                                              *) 
			(None, None,      cmd_pv_x)                          (*        x_pv = i__putValue (x, x_r) with err                                                                        *)
		] in 
		let new_errs = [ var_se; x_v; x_n; x_pv ] in 
		new_cmds, new_errs, x_v, x_r in
	
	
	let translate_multiplicative_binop x1 x2 x1_v x2_v aop err = 
		let jsil_aop = 
			(match aop with 
			| Parser_syntax.Times -> Times 
			| Parser_syntax.Div -> Div 
			| Parser_syntax.Mod -> Mod 
			| Parser_syntax.Minus -> Minus
			| _ -> raise (Failure "Illegal binary operator - Impossible case")) in 
		
		(* x1_n := i__toNumber (x1_v) with err *) 
		let x1_n, cmd_tn_x1 = make_to_number_call x1 x1_v err in
		(* x2_n := i__toNumber (x2_v) with err *) 
		let x2_n, cmd_tn_x2 = make_to_number_call x2 x2_v err in
		(* x_r := x1_n * x2_n *) 
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLBasic (SAssignment (x_r, BinOp (Var x1_n, jsil_aop, Var x2_n))) in 
		
		let new_cmds = [
			(None, None, cmd_tn_x1);       (*  x1_n := i__toNumber (x1_v) with err  *)
			(None, None, cmd_tn_x2);       (*  x2_n := i__toNumber (x2_v) with err  *)  
			(None, None, cmd_ass_xr)       (*  x_r := x1_n * x2_n                   *)
		] in 
		let new_errs = [ x1_n; x2_n ] in 
		new_cmds, new_errs, x_r in 
	
	
	let translate_binop_plus x1 x2 x1_v x2_v err = 
		(* x1_p := i__toPrimitive (x1_v) with err *) 
		let x1_p, cmd_tp_x1 = make_to_primitive_call x1 x1_v err in
		
		(* x2_p := i__toPrimitive (x2_v) with err *) 
		let x2_p, cmd_tp_x2 = make_to_primitive_call x2 x2_v err in
		
		(*  goto [((typeOf x1_p) = $$string_type) or ((typeOf x2_p) = $$string_type)] then else *) 
		let then_lab = fresh_then_label () in 
		let else_lab = fresh_else_label () in 
		let end_lab = fresh_endif_label () in 
		let goto_guard_left = BinOp ((TypeOf (Var x1_p)), Equal, (Literal (Type StringType))) in 
		let goto_guard_right = BinOp ((TypeOf (Var x2_p)), Equal, (Literal (Type StringType))) in 
		let goto_guard = BinOp (goto_guard_left, Or, goto_guard_right) in 
		let cmd_goto = SLGuardedGoto (goto_guard, then_lab, else_lab) in 
		
		(* then: x1_s := i__toString (x1_p) with err *) 
		let x1_s, cmd_ts_x1 = make_to_string_call x1 x1_p err in
		
		(* x2_s := i__toString (x2_p) with err *) 
		let x2_s, cmd_ts_x2 = make_to_string_call x2 x2_p err in
		
		(* x_rthen := x1_s :: x2_s  *) 
		let x_rthen = fresh_var () in 
		let cmd_ass_xrthen = SLBasic (SAssignment (x_rthen, BinOp((Var x1_s), Concat, (Var x2_s)))) in 
		
		(* else: x1_n := i__toNumber (x1_p) with err *) 
		let x1_n, cmd_tn_x1 = make_to_number_call x1 x1_p err in
		
		(* x2_n := i__toNumber (x2_p) with err *) 
		let x2_n, cmd_tn_x2 = make_to_number_call x2 x2_p err in
		
		(* x_relse := x1_n + x2_n  *) 
		let x_relse = fresh_var () in 
		let cmd_ass_xrelse = SLBasic (SAssignment (x_relse, BinOp((Var x1_n), Plus, (Var x2_n)))) in 
		
		(* end:  x_r := PHI (x_rthen, x_relse) *) 
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLBasic (SPhiAssignment (x_r, [| Some x_rthen; Some x_relse |])) in 
		
		let new_cmds = [             
			(None, None,          cmd_tp_x1);       (*       x1_p := i__toPrimitive (x1_v) with err                                                 *)
			(None, None,          cmd_tp_x2);       (*       x2_p := i__toPrimitive (x2_v) with err                                                 *)  
			(None, None,          cmd_goto);        (*       goto [((typeOf x1_p) = $$string_type) or ((typeOf x2_p) = $$string_type)] then else    *)
			(None, Some then_lab, cmd_ts_x1);       (* then: x1_s := i__toString (x1_p) with err                                                    *) 
			(None, None,          cmd_ts_x2);       (*       x2_s := i__toString (x2_p) with err                                                    *) 
			(None, None,          cmd_ass_xrthen);  (*       x_rthen := x1_s :: x2_s                                                                *) 
			(None, None,          SLGoto end_lab);  (*       goto end                                                                               *) 
			(None, Some else_lab, cmd_tn_x1);       (* else: x1_n := i__toNumber (x1_p) with err                                                    *) 
			(None, None,          cmd_tn_x2);       (*       x2_n := i__toNumber (x2_p) with err                                                    *) 
			(None, None,          cmd_ass_xrelse);  (* 	     x_relse := x1_n + x2_n                                                                 *) 
			(None, Some end_lab,  cmd_ass_xr)       (* end:  x_r := PHI (x_rthen, x_relse)                                                          *) 
		] in 
		let errs = [ x1_p; x2_p; x1_s; x2_s; x1_n; x2_n ] in 
		new_cmds, errs, x_r in 
	
	
	let translate_binop_comparison x1 x2 x1_v x2_v is_first_first flag_arg bool_undef err = 
		(* x_ac := i__abstractComparison (x1_v, x2_v, flag_arg) with err  *) 
		let x_ac = fresh_var () in
		let args = 
			(match is_first_first with 
			| true -> [ Var x1_v; Var x2_v ]
			| false -> [ Var x2_v; Var x1_v ]) in  
		let cmd_ac = SLCall (x_ac, (Literal (String abstractComparisonName)), args @ [ Literal (Bool flag_arg) ], Some err) in
		
		(*  goto [ x_ac = undefined ] then end *) 
		let then_lab = fresh_label () in  
		let end_lab = fresh_label () in 
		let cmd_goto = SLGuardedGoto (BinOp (Var x_ac, Equal, Literal Undefined), then_lab, end_lab) in 
		
		(* x_r := PHI(x_ac, x_undef) *)
		let x_undef = fresh_var () in 
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLBasic (SPhiAssignment (x_r, [| Some x_ac; Some x_undef |])) in 
		 
		let new_cmds = [
			(None, None, cmd_ac);  	                                                            (*        x_ac := i__abstractComparison (xi_v, xk_v, flag_arg) with err; where: i != k and i,k \in {1,2}  *) 
			(None, None, cmd_goto);                                                             (*        goto [ x_ac = undefined ] then end                                                              *) 
			(None, Some then_lab, SLBasic (SAssignment (x_undef, Literal (Bool bool_undef))));  (* then:  x_undef := bool_undef                                                                           *) 
			(None, Some end_lab, cmd_ass_xr)                                                    (* end:   x_r := PHI(x_ac, x_undef)                                                                       *)
		] in 
		let errs = [ x1_v; x2_v; x_ac ] in 
		new_cmds, errs, x_r	in 
	
	
	let translate_bitwise_shift x1 x2 x1_v x2_v left_fun_name right_fun_name op err = 
		(* x1_f := left_fun_name (x1_v) with err *) 
		let x1_f = fresh_var () in
		let cmd_fc_x1 = SLCall (x1_f, (Literal (String left_fun_name)), [ Var x1_v ], Some err) in
		
		(* x2_f := right_fun_name (x2_v) with err *) 
		let x2_f = fresh_var () in
		let cmd_fc_x2 = SLCall (x2_f, (Literal (String right_fun_name)), [ Var x2_v ], Some err) in
		
		(* x_r := x1_f op x2_f *) 
		let x_r = fresh_var () in
		let cmd_ass_xr = SLBasic (SAssignment (x_r, (BinOp (Var x1_f, op, Var x2_f)))) in 
		
		let new_cmds = [
			(None, None,  cmd_fc_x1);       (*  x1_f := left_fun_name (x1_v) with err     *) 
			(None, None,  cmd_fc_x2);       (*  x2_f := right_fun_name (x2_v) with err    *)
		  (None, None,  cmd_ass_xr)       (*  x_r := x1_f op x2_f                       *)
		] in 
		let errs = [ x1_v; x2_v; x1_f; x2_f ] in 
		new_cmds, errs, x_r in 
		
		
	let translate_binop_equality x1 x2 x1_v x2_v non_strict non_negated err =
		(* x_r1 := i__strictEqualityComparison/i__abstractEqualityComparison (x1_v, x2_v) with err *)
		let x_r1 = fresh_var () in 
		let f_name = 
			(match non_strict with 
			| true -> abstractEqualityComparisonName 
			| false -> strictEqualityComparisonName) in
		let cmd_ass_xr1 = SLCall (x_r1, (Literal (String f_name)), [ Var x1_v; Var x2_v ], Some err) in
		
		let cmd_ass_xr2, ret = 
			(match non_negated with 
			| true -> [], x_r1
			| false -> 
				(let x_r2 = fresh_var () in 
				(* x_r2 := (not x_r1) *) 
				[ (None, None, SLBasic (SAssignment (x_r2, UnaryOp (Not, Var x_r1)))) ], x_r2)) in 
	
		let new_cmds =	[
			(None, None, cmd_ass_xr1) 
		] @ cmd_ass_xr2 in 
		new_cmds, [ x_r1 ], ret in
	
	
	let translate_bitwise_bin_op x1 x2 x1_v x2_v bbop err = 
		let bbop = 
			(match bbop with 
			| Parser_syntax.Bitand -> BitwiseAnd
			| Parser_syntax.Bitor -> BitwiseOr 
			| Parser_syntax.Bitxor -> BitwiseXor
			| _ -> raise (Failure "Illegal bitwise operator")) in
	
		(* x1_i32 := i__toInt32 (x1_v) with err3 *)
		let x1_i32, cmd_ti32_x1 = make_to_i32_call x1 x1_v err in 
		
		(* x2_i32 := i__toInt32 (x2_v) with err4 *)
		let x2_i32, cmd_ti32_x2 = make_to_i32_call x2 x2_v err in 
	
		(*  x_r := (x1_i32 bbop x2_i32) *) 
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLBasic (SAssignment (x_r, BinOp (Var x1_i32, bbop, Var x2_i32))) in 
		
		let new_cmds =	[
			(None, None, cmd_ti32_x1); 
			(None, None, cmd_ti32_x2); 
			(None, None, cmd_ass_xr) 
		] in 
		let new_errs = [ x1_v; x2_v; x1_i32; x2_i32 ] in 
		new_cmds, new_errs, x_r in
	
	
	let translate_bin_logical_operator e1 e2 lbop err =
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
				
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x1_b := i__toBoolean (x1_v) with err  *)
		let x1_b, cmd_tb_x1 = make_to_boolean_call x1 x1_v err in 
		(* goto [x1_b] end next *)
		let next = fresh_next_label () in 
		let end_lab = fresh_end_label () in 
		let cmd_goto = 
			(match lbop with 
			| Parser_syntax.And -> SLGuardedGoto (Var x1_b, next, end_lab) 
			| Parser_syntax.Or -> SLGuardedGoto (Var x1_b, end_lab, next)) in 
		(* x2_v := i__getValue (x2) with err *) 
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		(* x_r := PHI(x1_v, x2_v) *)
		let x_r = fresh_var () in  
		let cmd_ass_xr = SLBasic (SPhiAssignment (x_r, [| Some x1_v; Some x2_v |])) in 
		
		let cmds2 = add_initial_label cmds2 next in  
		let cmds = cmds1 @ [                        (*         cmds1                                              *)
			(None, None,         cmd_gv_x1);          (*         x1_v := i__getValue (x1) with err                  *)
			(None, None,         cmd_tb_x1);          (*         x1_b := i__toBoolean (x1_v) with err               *)
			(None, None,         cmd_goto)            (*         goto [x1_b] next end                               *)
		] @ cmds2 @ [                               (* next:   cmds2                                              *)
			(None, None,         cmd_gv_x2);          (*         x2_v := i__getValue (x2) with err                  *)    
			(None, Some end_lab, cmd_ass_xr)          (* end:    x_r := PHI(x1_v, x2_v)                             *)
		] in 
		let errs = errs1 @ [ x1_v; x1_b ] @ errs2 @ [ x2_v ] in 
		cmds, Var x_r, errs, [], [], []	in
	
	
	let translate_arg_list xes err = 
		let cmds_args, x_args_gv, errs_args = 
			List.fold_left (fun (cmds_args, x_args_gv, errs_args) e_arg -> 
				let cmds_arg, x_arg, errs_arg, _, _, _ = f e_arg in
				let x_arg_v, cmd_gv_arg = make_get_value_call x_arg err in  
				(cmds_args @ cmds_arg @ [ (None, None, cmd_gv_arg) ], x_args_gv @ [ Var x_arg_v ], (errs_args @ errs_arg @ [ x_arg_v ])))
			([], [], [])
			xes in 
		cmds_args, x_args_gv, errs_args in
	
	
	let make_check_empty_test x_prev x_new = 
	(**        goto [x_new = $$empty] next1 next2 
			next1: skip 
			next2: x := PHI(x_new, x_previous) 
	*)
		let x_prev, cmd_ass_xprev = 
			(match x_prev with 
			| Var x_prev -> x_prev, [] 
			| Literal lit -> 
				let x_prev_var = fresh_var () in 
				let cmd_ass_prev = (None, None, SLBasic (SAssignment (x_prev_var, Literal lit))) in 
				x_prev_var, [ cmd_ass_prev ] 
			| _ -> raise (Failure "make_check_empty_test: x_prev needs to be either a literal or a var")) in 
	
		let x_new, cmd_ass_new = 
			(match x_new with 
			| Var x_new -> x_new, [] 
			| Literal lit -> 
				let x_new_var = fresh_var () in 
				let cmd_ass_new = (None, None, SLBasic (SAssignment (x_new_var, Literal lit))) in 
				x_new_var, [ cmd_ass_new ] 
			| _ -> raise (Failure "make_check_empty_test: x_new needs to be either a literal or a var")) in 
	
		(* goto [x_new = $$empty] next1 next2 *)
		let next1 = fresh_next_label () in 
		let next2 = fresh_next_label () in  
		let cmd_goto = (None, None, SLGuardedGoto (BinOp (Var x_new, Equal, Literal Empty), next1, next2)) in 
		
		(* next1: skip  *) 
		let cmd_skip = (None, Some next1, SLBasic SSkip) in 
		
		(* next2: x := PHI(x_new, x_previous) *) 
		let x = fresh_var () in 
		let cmd_phi = (None, Some next2, SLBasic (SPhiAssignment (x, [| Some x_new; Some x_prev |]))) in 
		
		cmd_ass_xprev @ cmd_ass_new @ [ cmd_goto; cmd_skip; cmd_phi], x in 
	
			 
	let make_loop_end cur_val_var prev_val_var break_vars end_lab cur_first = 
		(** 
    	end_loop: x_ret_4 := PHI(break_vars, cur_val_var) 
			          goto [ x_ret_4 = $$empty ] next3 next4
			next3:    skip 
			next4:    x_ret_5 := PHI(x_ret_4, prev_val_var)
		*)
	 	let x_ret_4 = fresh_var () in 
		let x_ret_5 = fresh_var () in 
		let next3 = fresh_next_label () in 
		let next4 = fresh_next_label () in 
		
		(* x_ret_4 := PHI(cur_val_var, break_vars) *)
		let break_vars = 
			match cur_first with 
			| true -> cur_val_var :: break_vars 
			| false -> break_vars @ [ cur_val_var ] in 
		let phi_args = List.map (fun x -> Some x) break_vars in 
		let phi_args = Array.of_list phi_args in 
		let cmd_ass_ret4 = SLBasic (SPhiAssignment (x_ret_4, phi_args)) in 
		
		(* goto [ x_ret_4 = $$empty ] next3 next4 *) 
		let cmd_goto = SLGuardedGoto ((BinOp (Var x_ret_4, Equal, Literal Empty), next3, next4)) in 
		
		(* next4:    x_ret_5 := PHI(x_ret_4, prev_val_var) *)
		let cmd_ass_ret5 = SLBasic (SPhiAssignment (x_ret_5, [| Some x_ret_4; Some prev_val_var |])) in 
		
		let cmds = [
			(None, Some end_lab, cmd_ass_ret4);    (* end_loop:   x_ret_4 := PHI(cur_val_var, break_vars) *)
			(None, None,         cmd_goto);        (*             goto [ x_ret_4 = $$empty ] next3 next4  *)
			(None, Some next3,   SLBasic SSkip);   (* next3:      skip                                    *)
			(None, Some next4,   cmd_ass_ret5)     (* next4:      x_ret_5 := PHI(x_ret_4, prev_val_var)   *)
		]	in 
		cmds, x_ret_5 in 
			
	
	let create_final_phi_cmd cmds x errs rets breaks conts break_label js_lab = 
		let cur_breaks, outer_breaks = filter_cur_jumps breaks js_lab false in
		(match cur_breaks with 
		| [] -> cmds, x, errs, rets, breaks, conts
		| _ -> 
			let x_name, cmds_new_x =
				(match x with 
				| Var x_name -> x_name, []
				| Literal lit -> 
					let x_name = fresh_var () in  
					let cmd_new_x = [ (None, None, SLBasic (SAssignment (x_name, Literal lit))) ] in 
					x_name, cmd_new_x 
				| _ -> raise (Failure "translate. Block: the result of the compilation must be a variable or a literal")) in 
			let x_ret = fresh_var () in 
			let phi_args = cur_breaks @ [ x_name ] in 
			let phi_args = List.map (fun x -> Some x)  phi_args in 
			let phi_args = Array.of_list phi_args in 
			let cmd_ass_phi = [ (None, break_label, SLBasic (SPhiAssignment (x_ret, phi_args))) ] in 
			(cmds @ cmds_new_x @ cmd_ass_phi), Var x_ret, errs, rets, outer_breaks, conts) in 
	
	
	let make_try_catch_cmds e1 (x, e2) catch_id = 						
	  (**
									cmds1
		            	goto finally  
		    err:    	x_err := PHI(errs1)
				        	x_er := new () 
									[x_er, "x"] := x_err 
									[x_scope, "cid"] := x_er 
									cmds2
			  finally:  x_ret_1 := PHI(breaks1, x_1, breaks2, x_2)
	  *) 
		let new_err, finally, end_label = fresh_tcf_vars () in
		let new_loop_list = (None, finally, js_lab) :: loop_list in 
		let cmds1, x1, errs1, rets1, breaks1, conts1 = translate fid cc_table ctx vis_fid new_err new_loop_list None None e1 in
		let cmds1, x1_v = add_final_var cmds1 x1 in 
	
		let cmds2, x2, errs2, rets2, breaks2, conts2 = translate catch_id cc_table ctx vis_fid err new_loop_list None None e2 in
		let cmds2, x2_v = add_final_var cmds2 x2 in 
	
		let cur_breaks1, outer_breaks1 = filter_cur_jumps breaks1 js_lab false in 
		let cur_breaks2, outer_breaks2 = filter_cur_jumps breaks2 js_lab false in

		(* x_err := PHI(errs1) *) 
		let x_err = fresh_err_var () in 
		let phi_args1 = List.map (fun x -> Some x) errs1 in 
		let phi_args1 = Array.of_list phi_args1 in 
		let cmd_ass_xerr = SLBasic (SPhiAssignment (x_err, phi_args1)) in 
	
		(* x_er := new () *)
		let x_er = fresh_er_var () in 
		let cmd_ass_xer = SLBasic (SNew x_er) in 
	
		(* [x_er, "x"] := x_err *) 
		let cmd_mutate_x = SLBasic (SMutation (Var x_er, Literal (String x), Var x_err)) in  					  				
	
		(* [x_scope, "cid"] := x_er *) 
		let cmd_sc_updt = SLBasic (SMutation (Var var_scope, Literal (String catch_id), Var x_er)) in 
	
		(* x_ret := PHI(cur_breaks1, x_1, cur_breaks2, x_2) *)
		let x_ret = fresh_var () in 
		let phi_args2 = cur_breaks1 @ [ x1_v ] @ cur_breaks2 @ [ x2_v ] in 
		let phi_args2 = List.map (fun x -> Some x) phi_args2 in   
		let phi_args2 = Array.of_list phi_args2 in 
		let cmd_ass_xret = SLBasic (SPhiAssignment (x_ret, phi_args2)) in 
		
		let cmds = cmds1 @ [
			(None, None,          SLGoto finally); 
			(None, Some new_err,  cmd_ass_xerr);
			(None, None,          cmd_ass_xer); 
			(None, None,          cmd_mutate_x); 
			(None, None,          cmd_sc_updt)
		] @ cmds2 @ [
			(None, Some finally,  cmd_ass_xret)
		] in 
		
		cmds, x_ret, errs2, rets1 @ rets2, outer_breaks1 @ outer_breaks2, conts1 @ conts2, end_label in

	
	match e.Parser_syntax.exp_stx with 

	| Parser_syntax.This ->
		(**
      Section 11.1.1 - The this Keyword
			C(this) =  		x := __this	
		*)
		let new_var = fresh_var () in 
		let cmd = SLBasic (SAssignment (new_var, (Var var_this))) in
		let cmds = [
			None, None, cmd
		] in  
		cmds, Var new_var, [], [], [], []
		
		
	| Parser_syntax.Var v -> 
		(** 
		 Section 11.1.2 - Identifier Reference		
		 Found in the closure clarification table: Phi(fid_1, x) = fid_2
					x_1 := [__scope_chain, fid_2]; 
					x_r := v-ref(x_1, "x")
	
		Not found in the closure clarification table: Phi(fid_1, x) = bot
						x_1 := o__hasProperty($lg, "x") with err; 
						goto [x_1] then else
			then: x_then := v-ref($lg, "x"); 
		      	goto end; 
			else: x_else := v-ref($$undefined, "x"); 
			end:  x_r = PHI(x_then, x_else)    	 
 		*)
		
		let translate_var_not_found v = 
			(* 	x_1 := o__hasProperty($lg, "x") with err *) 
			let x_1 = fresh_var () in  
		  let cmd_ass_x1 = SLCall (x_1, Literal (String hasPropertyName), [ Literal (Loc locGlobName); Literal (String v) ], Some err) in	
			
			(* goto [x_1] then else *)
			let then_lab = fresh_then_label () in 
			let else_lab = fresh_else_label () in 
			let end_lab = fresh_end_label () in 
			let cmd_goto_unres_ref = SLGuardedGoto (Var x_1, then_lab, else_lab) in 
			
			(* x_then := v-ref($lg, "x");   *) 
			let x_then = fresh_var () in 
			let cmd_ass_xthen = SLBasic (SAssignment (x_then, VRef (Literal (Loc locGlobName), Literal (String v))))  in 
			
			(* x_then := v-ref($$undefined, "x");  *) 
			let x_else = fresh_var () in 
			let cmd_ass_xelse = SLBasic (SAssignment (x_else, VRef (Literal Undefined, Literal (String v)))) in
			
			(* x_r = PHI(x_then, x_else)  *)
			let x_r = fresh_var () in  
		 	let cmd_ass_xr = SLBasic (SPhiAssignment (x_r, [| Some x_then; Some x_else |])) in 
			
			let cmds = [
				(None, None,          cmd_ass_x1);          (*       x_1 := o__hasProperty($lg, "x") with err    *) 
				(None, None,          cmd_goto_unres_ref);  (*       goto [x_1] then else                        *)
				(None, Some then_lab, cmd_ass_xthen);       (* then: x_then := v-ref($lg, "x")                   *) 
				(None, None,          SLGoto end_lab);      (*       goto end                                    *)       
				(None, Some else_lab, cmd_ass_xelse);       (* else: x_else := v-ref($$undefined, "x")           *)
				(None, Some end_lab,  cmd_ass_xr)           (*       x_r = PHI(x_then, x_else)                   *)                                       
			] in 
			cmds, Var x_r, [], [], [], [] in
			
		let translate_var_found v f_id = 
			(* x_1 := [__scope_chain, fid]; *)
			let x_1 = fresh_var () in 
			let cmd_ass_x1 = SLBasic (SLookup (x_1, Var var_scope, Literal (String f_id))) in 
			
			(* x_r := v-ref(x_1, "x") *) 
			let x_r = fresh_var () in 
			let cmd_ass_xret = SLBasic (SAssignment (x_r, VRef (Var x_1, Literal (String v)))) in
			
			let cmds = [
				(None, None, cmd_ass_x1);     (*   x_1 := [__scope_chain, fid]  *) 
				(None, None, cmd_ass_xret);   (*   x_r := v-ref(x_1, "x")       *)
			] in 
			cmds, Var x_r, [], [], [], [] in 
			
		let v_fid = find_var_fid v in
		(match v_fid with 
		| None -> translate_var_not_found v
		| Some v_fid -> translate_var_found v v_fid)
	
	
	(**
	 Section 11.1.3 - Literals 
	*)
	| Parser_syntax.Null ->  [], Literal Null, [], [], [], []
	| Parser_syntax.Bool b -> [], Literal (Bool b), [], [], [], []
	| Parser_syntax.String s -> 
		let escaped_s = Str.global_replace (Str.regexp "\"") "\\\"" s in
		[], Literal (String escaped_s), [], [], [], []
	| Parser_syntax.Num n ->  [], Literal (Num n), [], [], [], []
	
	
	(**
	 Section 11.1.4 - Array Initializer  
	*)
	| Parser_syntax.Array eos -> raise (Failure "not implemented yet - array literal") 


	
	| Parser_syntax.Obj xs -> 
		(**
	 	 Section 11.1.5 - Object Initializer 
	 	 C({ pd_1, ..., pd_n } ) =
				x_obj := new () 
				x_cdo := create_default_object (x_obj, $lobj_proto) 
	      C_pd(pd_1, x_obj)
				... 
				C_pd(pd_n, x_obj) 
			
			pd := pn:e | get pn () { s } | set pn (x1, ..., xn) { s }
			
			pn := x | "x" | n 
			
			C_pn(x) = "x";  C_pn("x") = "x"; C_pn (n) = num_to_string(n)  
				
			C(e) = cmds, x
			----------------------
			C_pd (pn:e) =   cmds
			                x_v := i__getValue (x) with err
			                x_desc := {{ "d", x_v, $$t, $$t, $$t}} 
			                x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err
			
			-----------------------
			C_pd ( get pn () { s }^getter_id ) =  
				          		x1 := copy_object (x_scope, {{main, fid1, ..., fidn }}) 
											x_f := create_function_object(x1, getter_id, {{}})
											x_desc := {{ "a", x_f, $$empty, $$t, $$t }}
											x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err				
			
			-----------------------
		 	C_pd ( set pn (x1, ..., xn) { s }^setter_id ) = 
											x1 := copy_object (x_scope, {{main, fid1, ..., fidn }})
											x_f := create_function_object(x1, setter_id, {{x1, ..., xn}})
											x_desc := {{ "a", $$empty, x_f, $$t, $$t }}
											x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err
		*)
		
		let x_obj = fresh_obj_var () in 
		(* x_obj := new () *) 
		let cmd_new_obj = (None, None, (SLBasic (SNew x_obj))) in 
		(* x_cdo := create_default_object (x_obj, $lobj_proto) *) 
		let x_cdo = fresh_var () in 
		let cmd_cdo_call = (None, None, (SLCall (x_cdo, Literal (String createDefaultObjectName), [ Var x_obj; Literal (Loc locObjPrototype) ], None))) in 
		
		let translate_property_name pname = 
			(match pname with
			| Parser_syntax.PropnameId s
      | Parser_syntax.PropnameString s -> Literal (String s)
      | Parser_syntax.PropnameNum n -> UnaryOp (ToStringOp, (Literal (Num n)))) in 
		
		let translate_data_property_definition x_obj prop e err = 
			let cmds, x, errs, _, _, _ = f e in	
			(* x_v := i__getValue (x) with err *) 
			let x_v, cmd_gv_x = make_get_value_call x err in
		
			(* x_desc := {{ "d", x_v, $$t, $$t, $$t}}  *) 
			let x_desc = fresh_desc_var () in 
			let cmd_ass_xdesc = SLBasic (SAssignment (x_desc, LEList [ Literal (String "d"); Var x_v; Literal (Bool true); Literal (Bool true); Literal (Bool true) ] )) in 
			
			(* x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err *)
			let x_dop, cmd_dop_x = make_dop_call x_obj prop x_desc true err in
			
			let cmds = cmds @ [
				(None, None, cmd_gv_x);          (* x_v := i__getValue (x) with err                                          *)  
				(None, None, cmd_ass_xdesc);     (* x_desc := {{ "d", x_v, $$t, $$t, $$t}}                                   *) 
				(None, None, cmd_dop_x)          (* x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err    *)
			] in 
			let errs = errs @ [ x_v; x_dop ] in
			cmds, errs in 
		
		let translate_accessor_descriptor x_obj prop accessor is_getter err =
			let f_id = try Js_pre_processing.get_codename accessor 
				with _ -> raise (Failure "annonymous function literals should be annotated with their respective code names - Getter function") in 
			let params = 
				(match accessor.Parser_syntax.exp_stx with 
				| Parser_syntax.AnonymousFun (_, params, _) -> params 
				| _ -> raise (Failure "getters should be annonymous functions")) in 
			let cmds, x_f = translate_function_literal f_id params in 
			
			(* x_desc := {{ "a", x_f, $$empty, $$t, $$t }} *) 
			let x_desc = fresh_desc_var () in 
			let desc_params = 
				match is_getter with 
				| true -> [ Literal (String "a"); Var x_f; Literal Empty; Literal (Bool true); Literal (Bool true) ] 
				| false -> [ Literal (String "a"); Literal Empty; Var x_f; Literal (Bool true); Literal (Bool true) ] in 
			let cmd_ass_xdesc = SLBasic (SAssignment (x_desc, LEList desc_params)) in
			
			(* x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err *)
			let x_dop, cmd_dop_x = make_dop_call x_obj prop x_desc true err in
			
			let cmds = cmds @ [  
				(None, None, cmd_ass_xdesc);     (* x_desc := {{ "d", x_v, $$t, $$t, $$t}}                                   *) 
				(None, None, cmd_dop_x)          (* x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err    *)
			] in 
			cmds, [ x_dop ] in 
		
		let cmds, errs = 
			List.fold_left (fun (cmds, errs) (pname, ptype, e) ->
				let prop = translate_property_name pname in 
				let new_cmds, new_errs = 
					(match ptype with 
					| Parser_syntax.PropbodyVal -> translate_data_property_definition x_obj prop e err
					| Parser_syntax.PropbodyGet -> translate_accessor_descriptor x_obj prop e true err
					| Parser_syntax.PropbodySet -> translate_accessor_descriptor x_obj prop e false err) in 
				cmds @ new_cmds, errs @ new_errs)
				([], []) 
				xs in 
		(cmd_new_obj :: (cmd_cdo_call :: cmds)), (Var x_obj), errs, [], [], []

	
	| Parser_syntax.CAccess (e1, e2) -> 
		(**
      Section 11.2.1 - Property Accessors 
			C(e1) = cmds1, x1; C(e2) = cmds2, x2
			C(e1[e2]) = 
				cmds1
      	x1_v := i__getValue (x1) with err
				cmds2
				x2_v := i__getValue (x2) with err
				x_oc := i__checkObjectCoercible (x1_v) with err
				x2_s := i__toString (x2_v) with err
				x_r  := ref-o(x1_v, x4_v)
		 *)
		
		let cmds1, x1, errs1, _, _, _ = f e1 in 
		let cmds2, x2, errs2, _, _, _ = f e2 in 
		
		(* x1_v := i__getValue (x1) with err *) 
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		
		(* x2_v := i__getValue (x2) with err *) 
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		(* x_oc := i__checkObjectCoercible (x1_v) with err *) 
		let x_oc = fresh_var () in 
		let cmd_coc_x1 = SLCall (x_oc, Literal (String checkObjectCoercibleName), [ Var x1_v ], Some err) in 
		
		(* x2_s := i__toString (x2_v) with err *) 
		let x2_s, cmd_ts_x2 = make_to_string_call x2 x2_v err in 
		
		(* 	x_r := ref-o(x1_v, x2_s) *) 
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLBasic (SAssignment (x_r, (ORef ((Var x1_v), (Var x2_s))))) in 
		
		let cmds = cmds1 @ [                (* cmds1                                            *)
			(None, None, cmd_gv_x1)         	(* x1_v := i__getValue (x1) with err                *) 
		] @ cmds2 @ [                       (* cmds2                                            *) 
			(None, None, cmd_gv_x2);          (* x2_v := i__getValue (x2) with err                *) 
			(None, None, cmd_coc_x1);         (* x_oc := i__checkObjectCoercible (x1_v) with err  *) 
			(None, None, cmd_ts_x2);          (* x2_s := i__toString (x2_v) with err              *)  
			(None, None, cmd_ass_xr)          (* x_r := ref-o(x1_v, xs_s)                         *) 
		] in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v; x_oc; x2_s ] in
		cmds, (Var x_r), errs, [], [], []

		
	| Parser_syntax.Access (e, p) -> 
		(**
      Section 11.2.1 - Property Accessors 
			C(e) = cmds, x; 
			C(e.p) = 
				cmds1
      	x_v := i__getValue (x) with err
				x_oc := i__checkObjectCoercible (x1_v) with err
				x_r  := ref-o(x1_v, "p")
		 *)
		
		let cmds, x, errs, _, _, _ = f e in 
		
		(* x_v := i__getValue (x) with err *) 
		let x_v, cmd_gv_x = make_get_value_call x err in
		
		(* x_oc := i__checkObjectCoercible (x_v) with err *) 
		let x_oc = fresh_var () in 
		let cmd_coc_x = SLCall (x_oc, Literal (String checkObjectCoercibleName), [ Var x_v ], Some err) in 
		
		(* 	x_r := ref-o(x_v, "p") *) 
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLBasic (SAssignment (x_r, (ORef (Var x_v, Literal (String p))))) in 
		
		let cmds = cmds @ [                 (* cmds                                             *)
			(None, None, cmd_gv_x);          	(* x_v := i__getValue (x) with err                  *) 
			(None, None, cmd_coc_x) ;         (* x_oc := i__checkObjectCoercible (x_v) with err   *) 
			(None, None, cmd_ass_xr)          (* x_r := ref-o(x_v, "p")                           *) 
		] in 
		let errs = errs @ [ x_v; x_oc ] in 
		cmds, (Var x_r), errs, [], [], []	

	
	| Parser_syntax.New (e_f, xes) -> 
		(**
			Section 11.2.2 - The new Operator 
			C(e_f) = cmds_ef, x_f
			C(e_i) = cmds_ei, x_argi (for i = 1, ..., n) 
			C(new e_f (e_1, ..., e_n) = 
				          cmds_ef
           				x_f_val := i__getValue (x_f) with err; 
									cmds_e1
		 	     				x_arg1_val := i__getValue (x_arg1) with err; 
		       				...
									cmds_en
		       				x_argn_val := i__getValue (x_argn) with err; 
			     				goto [ typeOf(x_f_val) != Object] err next1; 
					next1:  x_hp := hasField(x_f_val, "@construct"); 
					        goto [ x_hp ] next2 err; 
					next2:	x_this := new (); 
					        x_ref_prototype := ref-o(x_f_val, "prototype"); 
									x_f_prototype := i__getValue(x_ref_prototype) with err;
									x_cdo := i__createDefaultObject (x_this, x_f_prototype); 
								 	x_body := [x_f_val, "@construct"]; 
		       				x_scope := [x_f_val, "@scope"]; 
					 				x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err; 
					 				goto [ x_r1 = $$emtpy ] next3 next4;
        	next3:  skip
					next4:  x_r3 := PHI(x_r1, x_this)
		*)	
		let cmds_ef, x_ef, errs_ef, _, _, _ = f e_f in 

		(* x_f_val := i__getValue (x_f) with err1;  *)
		let x_f_val, cmd_gv_f = make_get_value_call x_ef err in 	
		
		let cmds_args, x_args_gv, errs_args = translate_arg_list xes err in 	
		
		(* goto [ typeOf(x_f_val) != Object] err next1; err -> typeerror *) 
		let next1 = fresh_next_label () in   
		let goto_guard_expr = UnaryOp (Not, (BinOp (TypeOf (Var x_f_val), Equal, Literal (Type ObjectType)))) in 
		let cmd_goto_is_obj = SLGuardedGoto (goto_guard_expr, err, next1) in
		
		(* x_hp := hasField[x_f_val, "@construct"]; *)
		let x_hp = fresh_var () in 
		let cmd_hf_construct = SLBasic (SHasField (x_hp, Var x_f_val, Literal (String constructPropName))) in 
		
		(* goto [ x_hp ] next2 err; *) 
		let next2 = fresh_next_label () in 
		let cmd_goto_xhp = SLGuardedGoto (Var x_hp, next2, err) in 
		
		(* x_this := new (); *)
		let x_this = fresh_this_var () in 
		let cmd_create_xobj = SLBasic (SNew x_this) in 
		
		(* x_ref_fprototype := ref-o(x_f_val, "prototype");  *) 
		let x_ref_fprototype = fresh_var () in 
		let cmd_ass_xreffprototype = SLBasic (SAssignment (x_ref_fprototype, ORef (Var x_f_val, Literal (String "prototype")))) in  
		
		(* x_f_prototype := i__getValue(x_ref_prototype) with err; *) 
		let x_f_prototype, cmd_gv_xreffprototype = make_get_value_call (Var x_ref_fprototype) err in 
		
		(* x_cdo := i__createDefaultObject (x_this, x_f_prototype); *) 
		let x_cdo = fresh_var () in 
		let cmd_cdo_call = SLCall (x_cdo, Literal (String createDefaultObjectName), [ Var x_this; Var x_f_prototype ], None) in 
		
		(* x_body := [x_f_val, "@construct"];  *) 
		let x_body = fresh_body_var () in 
		let cmd_body = SLBasic (SLookup (x_body, Var x_f_val, Literal (String constructPropName))) in 
		
		(* x_fscope := [x_f_val, "@scope"]; *)
		let x_fscope = fresh_fscope_var () in 
		let cmd_scope = SLBasic (SLookup (x_fscope, Var x_f_val, Literal (String scopePropName))) in 
		
		(* x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err  *) 
		let x_r1 = fresh_var () in 
		let proc_args = (Var x_fscope) :: (Var x_this) :: x_args_gv in 
		let cmd_proc_call = SLCall (x_r1, (Var x_body), proc_args, Some err) in 
		
		(* goto [ x_r1 = $$emtpy ] next3 next4; *)
		let next3 = fresh_next_label () in 
		let next4 = fresh_next_label () in 
		let goto_guard_expr = BinOp (Var x_r1, Equal, Literal Empty) in
		let cmd_goto_test_empty = SLGuardedGoto (goto_guard_expr, next3, next4) in 
		
		(* next3: skip; *)
		let cmd_ret_this = SLBasic SSkip in
		
		(* next4: x_r2 := PHI(x_r1, x_this) *) 
		let x_r2 = fresh_var () in 
		let cmd_phi_final = SLBasic (SPhiAssignment (x_r2, [| Some x_r1; Some x_this |])) in 
		
		let cmds = cmds_ef @ [                          (*        cmds_ef                                                                  *)
			(None, None,         cmd_gv_f);               (*        x_f_val := i__getValue (x_f) with err                                    *) 
		] @ cmds_args @ [                               (*        cmds_arg_i; x_arg_i_val := i__getValue (x_arg_i) with err                *)
			(None, None,         cmd_goto_is_obj);        (*        goto [ typeOf(x_f_val) != Object] err next1                              *) 
			(None, Some next1,   cmd_hf_construct);       (* next1: x_hp := hasField[x_f_val, "@construct"]                                  *)
			(None, None,         cmd_goto_xhp);           (*        goto [ x_hp ] next2 err                                                  *)
			(None, Some next2,   cmd_create_xobj);        (* next2: x_this := new ()                                                         *)
			(None, None,         cmd_ass_xreffprototype); (*        x_ref_fprototype := ref-o(x_f_val, "prototype")                          *)
			(None, None,         cmd_gv_xreffprototype);  (*        x_f_prototype := i__getValue(x_ref_prototype) with err                   *)
		  (None, None,         cmd_cdo_call);           (*        x_cdo := create_default_object (x_this, x_f_prototype)                   *)
			(None, None,         cmd_body);               (*        x_body := [x_f_val, "@construct"]                                        *)
			(None, None,         cmd_scope);              (*        x_fscope := [x_f_val, "@scope"]                                          *)
			(None, None,         cmd_proc_call);          (*        x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err   *)
			(None, None,         cmd_goto_test_empty);    (*        goto [ x_r1 = $$emtpy ] next3 next4                                      *)
			(None, Some next3,   cmd_ret_this);           (* next3: skip                                                                     *)
			(None, Some next4,   cmd_phi_final)           (* next4: x_r2 := PHI(x_r1, x_this)                                                *)
		] in 
		let errs = errs_ef @ [ x_f_val ] @ errs_args @ [ var_te; var_te; x_f_prototype; x_r1 ] in 
		cmds, Var x_r2, errs, [], [], []				
		 
		
	| Parser_syntax.Call (e_f, xes) -> 
		(**
			Section 11.2.3 - Function call 
			C(e_f) = cmds_ef, x_f
			C(e_i) = cmds_ei, x_argi (for i = 1, ..., n) 
			C(e_f(e_1, ..., e_n) = 
				          cmds_ef
           				x_f_val := i__getValue (x_f) with err; 
									cmds_e1
		 	     				x_arg1_val := i__getValue (x_arg1) with err; 
		       				...
									cmds_en
		       				x_argn_val := i__getValue (x_argn) with err; 
			     				goto [ typeOf(x_f_val) != Object] err next1; 
					next1:  x_ic := isCallable(x_f_val); 
		     				  goto [ x_ic ] next2 err; 
					next2:  goto [ typeOf(x_f) = ObjReference ] then else; 
					then1:  x_this := base(x_f);
					 				goto end; 
					else1: 	x_this := undefined; 
					end1: 	x_body := [x_f_val, "@call"]; 
		       				x_scope := [x_f_val, "@scope"]; 
					 				x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err; 
					 				goto [ x_r1 = $$emtpy ] next3 next4;
        	next3:  x_r2 := $$undefined; 
					next4:  x_r3 := PHI(x_r1, x_r2)
		*)
		
		let cmds_ef, x_ef, errs_ef, _, _, _ = f e_f in 
	
		(* x_f_val := i__getValue (x_f) with err1;  *)
		let x_f_val, cmd_gv_f = make_get_value_call x_ef err in 
		
		let cmds_args, x_args_gv, errs_args = translate_arg_list xes err in 	
		
		(* goto [ typeOf(x_f_val) != Object] err next1; err -> typeerror *) 
		let next1 = fresh_next_label () in   
		let goto_guard_expr = UnaryOp (Not, (BinOp (TypeOf (Var x_f_val), Equal, Literal (Type ObjectType)))) in 
		let cmd_goto_is_obj = SLGuardedGoto (goto_guard_expr, err, next1) in 
		
		(* next1: x_ic := isCallable(x_f_val); *)
		let x_ic = fresh_var () in
		let cmd_ic = SLCall (x_ic, Literal (String isCallableName), [ Var x_f_val ], None) in
		
		(* goto [ x_ic ] next2 err; -> typeerror *)
		let next2 = fresh_next_label () in 
		let cmd_goto_is_callable = SLGuardedGoto (Var x_ic, next2, err) in 
		
		(* next2: goto [ typeOf(x_f) = ObjReference ] then else;  *) 
		let then_lab = fresh_then_label () in 
		let else_lab = fresh_else_label () in 
		let end_lab = fresh_endif_label () in 
		let goto_guard_expr = BinOp (TypeOf x_ef, Equal, Literal (Type ObjectReferenceType)) in 
		let cmd_goto_obj_ref = SLGuardedGoto (goto_guard_expr, then_lab, else_lab) in 
		
		(* then: x_then_this := base(x_f); *)
		let x_this_then = fresh_this_var () in 
		let cmd_this_base = SLBasic (SAssignment (x_this_then, Base x_ef)) in 
		
		(*  goto end; *)  
		let cmd_goto_end = SLGoto end_lab in 
		
		(* else: x_else_this := undefined; *) 
		let x_this_else = fresh_this_var () in 
		let cmd_this_undefined = SLBasic (SAssignment (x_this_else, Literal Undefined)) in 
		
		(* end: x_this := PHI(x_then_this, x_else_this) *)
		let x_this = fresh_this_var () in 
		let cmd_ass_xthis = SLBasic (SPhiAssignment (x_this, [| Some x_this_then; Some x_this_else |])) in 
		
		(* x_body := [x_f_val, "@call"]; *)
		let x_body = fresh_body_var () in 
		let cmd_body = SLBasic (SLookup (x_body, Var x_f_val, Literal (String callPropName))) in 
		
		(* x_fscope := [x_f_val, "@scope"]; *)
		let x_fscope = fresh_fscope_var () in 
		let cmd_scope = SLBasic (SLookup (x_fscope, Var x_f_val, Literal (String scopePropName))) in 
		
		(* x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err  *) 
		let x_r1 = fresh_var () in 
		let proc_args = (Var x_fscope) :: (Var x_this) :: x_args_gv in 
		let cmd_proc_call = SLCall (x_r1, (Var x_body), proc_args, Some err) in 
		
		(* goto [ x_r1 = $$emtpy ] next3 next4; *)
		let next3 = fresh_next_label () in 
		let next4 = fresh_next_label () in 
		let goto_guard_expr = BinOp (Var x_r1, Equal, Literal Empty) in
		let cmd_goto_test_empty = SLGuardedGoto (goto_guard_expr, next3, next4) in 
		
		(* next3: x_r2 := $$undefined; *)
		let x_r2 = fresh_var () in 
		let cmd_ret_undefined = SLBasic (SAssignment (x_r2, Literal Undefined)) in
		
		(* next4: x_r3 := PHI(x_r1, x_r2) *) 
		let x_r3 = fresh_var () in 
		let cmd_phi_final = SLBasic (SPhiAssignment (x_r3, [| Some x_r1; Some x_r2 |])) in 

		let cmds = cmds_ef @ [                          (*        cmds_ef                                                                  *)
			(None, None,           cmd_gv_f);             (*        x_f_val := i__getValue (x_f) with err                                    *) 
		] @ cmds_args @ [                               (*        cmds_arg_i; x_arg_i_val := i__getValue (x_arg_i) with err                *)
			(None, None,           cmd_goto_is_obj);      (*        goto [ typeOf(x_f_val) != Object] err next1                              *) 
			(None, Some next1,     cmd_ic);               (* next1: x_ic := isCallable(x_f_val)                                              *)
			(None, None,           cmd_goto_is_callable); (*        goto [ x_ic ] next2 err; -> typeerror                                    *)
			(None, Some next2,     cmd_goto_obj_ref);     (* next2: goto [ typeOf(x_f) = ObjReference ] then else                            *) 
			(None, Some then_lab,  cmd_this_base);        (* then:  x_then_this := base(x_f)                                                 *)
			(None, None,           cmd_goto_end);         (*        goto end                                                                 *)  
			(None, Some else_lab,  cmd_this_undefined);   (* else:  x_else_this := undefined                                                 *) 
			(None, Some end_lab,   cmd_ass_xthis);        (* end:   x_this := PHI(x_then_this, x_else_this)                                  *)
			(None, None,           cmd_body);             (*        x_body := [x_f_val, "@call"]                                             *)
			(None, None,           cmd_scope);            (*        x_fscope := [x_f_val, "@scope"]                                          *)
			(None, None,           cmd_proc_call);        (*        x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err   *) 
			(None, None,           cmd_goto_test_empty);  (*        goto [ x_r1 = $$emtpy ] next3 next4                                      *)
			(None, Some next3,     cmd_ret_undefined);    (* next3: x_r2 := $$undefined                                                      *)
			(None, Some next4,     cmd_phi_final)         (* next4: x_r3 := PHI(x_r1, x_r2)                                                  *) 
		] in
		let errs = errs_ef @ [ x_f_val ] @ errs_args @ [ var_te; var_te; x_r1 ] in 
		cmds, Var x_r3, errs, [], [], []				
		
		
		
	| Parser_syntax.Unary_op (Parser_syntax.Post_Incr, e) ->
		(**
      Section: 11.3.1
      C(e) = cmds, x
			
			C(e++) =          cmds 
			                  goto [ (typeof (x) = $$v-reference_type) and ((field(x) = "eval") or (field(x) = "arguments")) ] err next
			           next:  x_v := i__getValue (x) with err
								        x_n := i__toNumber (x_v) with err 
							          x_r := x_n + 1
												x_pv := putValue (x, x_r) with err; 
     *)
		let cmds, x, errs, _, _, _ = f e in
	 	let new_cmds, new_errs, x_v, x_r = translate_inc_dec x true err in	
		(cmds @ new_cmds), Var x_v, (errs @ new_errs), [], [], [] 
	
	
	| Parser_syntax.Unary_op (Parser_syntax.Post_Decr, e) ->
		(**
      Section: 11.3.2
      C(e) = cmds, x
			
			C(e--) =          cmds 
			                  goto [ (typeof (x) = $$v-reference_type) and ((field(x) = "eval") or (field(x) = "arguments")) ] err next
			           next:  x_v := i__getValue (x) with err 
								        x_n := i__toNumber (x_v) with err 
							          x_r := x_n - 1
												x_pv := putValue (x, x_r) with err 
     *)
		let cmds, x, errs, _, _, _ = f e in
	 	let new_cmds, new_errs, x_v, x_r = translate_inc_dec x false err in	
		(cmds @ new_cmds), Var x_v, (errs @ new_errs), [], [], [] 
		
		
	| Parser_syntax.Delete e -> 
		(** 		
			Section: 11.4.1 
			C(e) = cmds, x  
			C(delete e) = 
			       cmds
			       goto [ (typeOf x) <: $$reference_type ] next1 next4
			next1: goto [ ((base(x) = $$null) or (base(x) = $$undefined)) ] err next2
			next2: goto [ (typeOf x) = $$v-reference_type ] err next3
			next3: x_obj := toObject(base(x)) with err
						 x_r1 := deleteProperty(x_obj, field(x), $$t) with err 
					   goto next5 
			next4: x_r2 := $$t
			next5: x_r := PHI(x_r1; x_r2) 	
    *)
		
		let cmds, x, errs, _, _, _ = f e in 
		
		(* goto [ (typeOf x) <: $$reference_type ] next1 next4 *) 
		let next1 = fresh_next_label () in 
		let next2 = fresh_next_label () in 
		let next3 = fresh_next_label () in
		let next4 = fresh_next_label () in
		let goto_guard = BinOp (TypeOf x, Subtype, Literal (Type ReferenceType)) in  
		let cmd_goto_isref = SLGuardedGoto (goto_guard, next1, next4) in 
		
		(* next1: goto [ ((base(x) = $$null) or (base(x) = $$undefined)) ] err next2 *) 
		let cmd_goto_is_resolvable_ref = SLGuardedGoto (make_unresolvable_ref_test x , err, next2) in 
		
		(* next2: goto [ (typeOf x) = $$v-reference_type ] err next3 *) 
		let goto_guard = BinOp (TypeOf x, Equal, Literal (Type VariableReferenceType)) in 
		let cmd_goto_is_vref = SLGuardedGoto (goto_guard, err, next3) in 
		
		(* next3: x_obj := toObject(base(x)) err *)
		let x_obj = fresh_obj_var () in 
		let cmd_to_obj = SLCall (x_obj, Literal (String toObjectName), [ (Base x) ], Some err) in 
		
		(* x_r1 := deleteProperty(x_obj, field(x), $$t) with err *) 
		let x_r1 = fresh_var () in 
		let cmd_delete = SLCall (x_r1, Literal (String deletePropertyName), 
			[ (Var x_obj); (Field x); (Literal (Bool true)) ], Some err) in
		
		let x_r2 = fresh_var () in 
		let x_r = fresh_var () in 
		let next5 = fresh_next_label () in
		let cmds = 
			cmds @ [                                                                         (*        cmds                                                                     *) 
			(None, None,       cmd_goto_isref);                                              (*        goto [ (typeOf x) <: $$reference_type ] next1 next4                      *) 
			(None, Some next1, cmd_goto_is_resolvable_ref);                                  (* next1: goto [ ((base(x_e) = $$null) or (base(x_e) = $$undefined)) ] err next2   *)
			(None, Some next2, cmd_goto_is_vref);                                            (* next2: goto [ (typeOf x) = $$v-reference_type ] err next3                       *) 
			(None, Some next3, cmd_to_obj);                                                  (* next3: x_obj := toObject(base(x)) err3                                          *)       
			(None, None,       cmd_delete);                                                  (*        x_r1 := deleteProperty(x_obj, field(x), $$t) with err                    *)
			(None, None,       SLGoto next5);                                                (*        goto next5                                                               *)
			(None, Some next4, SLBasic (SAssignment (x_r2, Literal (Bool true))));           (* next4: x_r2 := $$t                                                              *) 
			(None, Some next5, SLBasic (SPhiAssignment (x_r, [| Some x_r1; Some x_r2 |])))   (* next5: x_r := PHI(x_r1, x_r2)                                                   *)                   
		] in 
		let errs = errs @ [ var_se; var_se; x_obj; x_r1 ] in 
		cmds, Var x_r, errs, [], [], []
	
	
	| Parser_syntax.Unary_op (Parser_syntax.Void, e) ->
		(**
      Section: 11.4.2
      C(e) = cmds, x
			C(void e) =    cmds 
			               x_v := getValue (x) with err 
							       x_r := $$undefined
     *)
		let cmds, x, errs, _, _, _ = f e in 
		(* x_v := getValue (x) with err *)
		let x_v, cmd_gv_x = make_get_value_call x err in 
		let x_r = fresh_var () in 
		let cmds = cmds @ [                                                (*  cmds                                *)
			(None, None, cmd_gv_x);                                          (*  x_v := getValue (x) with err        *)
			(None, None, SLBasic (SAssignment (x_r, Literal Undefined)));    (*  x_r := $$undefined                  *)    
		] in 
		let errs = errs @ [ x_v ] in 
		cmds, Var x_r, errs, [], [], []
	
			
	| Parser_syntax.Unary_op (Parser_syntax.TypeOf, e) ->
		(**
    Section: 11.4.3
		C(e)        =  cmds, x 
		C(typeof e) =           cmds
		                        goto [ typeof (x) <: $$reference-type ] next1 next4
			             next1:   goto [ ((base(x) = $$null) or (base(x) = $$undefined)) ] next2 next3
									 next2:   x1 := $$undefined 
								            goto next4 
									 next3:   x2 := getValue (x) with err
									 next4:   x3 := PHI (x, x1, x2) 
									          x_r := i__typeOf (x3) with err
     *)
		
		let cmds, x, errs, _, _, _ = f e in  
		
		(* goto [ typeof (x) <: $$reference-type ] next1 next4 *) 
		let next1 = fresh_next_label () in 
		let next2 = fresh_next_label () in 
		let next3 = fresh_next_label () in 
		let next4 = fresh_next_label () in 
		let cmd_goto_ref_guard = BinOp ((TypeOf x), Subtype, Literal (Type ReferenceType)) in 
		let cmd_goto_ref = SLGuardedGoto (cmd_goto_ref_guard, next1, next4) in  
		
		(* goto [ ((base(x_e) = $$null) or (base(x_e) = $$undefined)) ] next2 next3 *) 
		let cmd_goto_unres_ref = SLGuardedGoto (make_unresolvable_ref_test x, next2, next3) in
		
		(* x2 := getValue (x) with err *)
		let x1 = fresh_var () in 
		let x2 = fresh_var () in 
		let cmd_gv_x = SLCall (x2, (Literal (String getValueName)), [ x ], Some err) in
		
		(* x_r := i__typeOf (x3) with err *) 
		let x3 = fresh_var () in 
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLCall (x_r, (Literal (String jsTypeOfName)), [ Var x3 ], Some err) in
		
		let x_name = 
			match x with 
			| Var x_name -> x_name 
			| _ -> raise (Failure ("Expected a variable")) in  
		
		let cmds = cmds @ [                                                                         (*             cmds                                                  *)
			(None, None, cmd_goto_ref);                                                               (*             goto [ typeof (x) <: $$reference-type ] next1 next4   *) 
			(None, Some next1, cmd_goto_unres_ref);                                                   (* next1:      goto [ base(x) = undefined] next2 next3               *)
			(None, Some next2, SLBasic (SAssignment (x1, Literal Undefined)));                        (* next2:      x1 := $$undefined                                     *) 
			(None, None,       SLGoto next4);                                                         (*             goto next4                                            *) 
			(None, Some next3, cmd_gv_x);                                                             (* next3:      x2 := getValue (x) with err                           *)
			(None, Some next4, SLBasic (SPhiAssignment (x3, [| Some x_name; Some x1; Some x2 |])));   (* next4:      x3 := PHI (x, x1, x2)                                 *)
			(None, None,       cmd_ass_xr)                                                            (*             x_r := i__typeOf (x3) with err                        *)
		] in 
		let errs = errs @ [ x2; x_r ] in 
		cmds, Var x_r, errs, [], [], []
	
	
	| Parser_syntax.Unary_op (Parser_syntax.Pre_Incr, e) ->
		(**
      Section: 11.4.4
      C(e) = cmds, x
			C(++e) =          cmds 
			                  goto [ (typeof (x) = $$v-reference_type) and ((field(x) = "eval") or (field(x) = "arguments")) ] err next
			           next:  x_v := i__getValue (x) with err
								        x_n := i__toNumber (x_v) with err
							          x_r := x_n + 1
												x_pv := i__putValue (x, x_r) with err
     *)
		let cmds, x, errs, _, _, _ = f e in
	 	let new_cmds, new_errs, x_v, x_r = translate_inc_dec x true err in	
		(cmds @ new_cmds), Var x_r, (errs @ new_errs), [], [], [] 
	
	
	| Parser_syntax.Unary_op (Parser_syntax.Pre_Decr, e) ->
		(**
      Section: 11.4.5
      C(e) = cmds, x
			C(--e) =          cmds 
			                  goto [ (typeof (x) = $$v-reference_type) and ((field(x) = "eval") or (field(x) = "arguments")) ] err next
			           next:  x_v := getValue (x) with err 
								        x_n := i__toNumber (x_v) with err 
							          x_r := x_n - 1
												x_pv := i__putValue (x, x_r) with err 
     *)
		let cmds, x, errs, _, _, _ = f e in
	 	let new_cmds, new_errs, x_v, x_r = translate_inc_dec x false err in	
		(cmds @ new_cmds), Var x_r, (errs @ new_errs), [], [], []


	| Parser_syntax.Unary_op (Parser_syntax.Positive, e) ->
		(**
			Section: 11.4.6
      C(e) = cmds, x
			C(+e) =  cmds 
			         x_v := i__getValue (x) with err 
							 x_n := i__toNumber (x_v) with err
     *)
		let cmds, x, errs, _, _, _ = f e in  
		
		(* x_v := i__getValue (x) with err *)
		let x_v, cmd_gv_x = make_get_value_call x err in 	
		
		(* x_n := i__toNumber (x_v) with err *) 
		let x_n, cmd_tn_x = make_to_number_call x x_v err in 
				
		let cmds = cmds @ [                    (*  cmds                                *)
			(None, None, cmd_gv_x);              (*  x_v := i__getValue (x) with err     *)
			(None, None, cmd_tn_x);              (*  x_n := i__toNumber (x_v) with err   *)
		] in 
		let errs = errs @ [ x_v; x_n ] in 
		cmds, Var x_n, errs, [], [], []
								

	| Parser_syntax.Unary_op (Parser_syntax.Negative, e) ->
		(**
			Section: 11.4.7
      C(e) = cmds, x
			C(-e) =        cmds 
			               x_v := i__getValue (x) with err 
							       x_n := i__toNumber (x_v) with err
							       goto [x_n = nan] then else 
							 then: x_then := nan 
							       goto end 
							 else: x_else := (negative x_n)
							 end:  x_r := PHI(x_then, x_else)  
     *)
		let cmds, x, errs, _, _, _ = f e in  
		
		(* x_v := getValue (x) with err *)
		let x_v, cmd_gv_x = make_get_value_call x err in
		
		(* x_n := i__toNumber (x_v) with err *)
		let x_n, cmd_tn_x = make_to_number_call x x_v err in
		
		(* goto [x_n = nan] then else *) 
		let then_lab = fresh_then_label () in 
		let else_lab = fresh_else_label () in 
		let end_lab = fresh_endif_label () in 
		let cmd_goto_nan = SLGuardedGoto (BinOp (Var x_n, Equal, Literal (Num nan)), then_lab, else_lab) in 
		
		(* then: x_then := nan *) 
		let x_then = fresh_var () in 
		let cmd_ass_xthen = SLBasic (SAssignment (x_then, Literal (Num nan))) in 
		
		(* else: x_else := (negative x_n) *)
		let x_else = fresh_var () in 
		let cmd_ass_xelse = SLBasic (SAssignment (x_else, UnaryOp (Negative, (Var x_n)))) in
		
		(* end:  x_r := PHI(x_then, x_else) *) 
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLBasic (SPhiAssignment (x_r, [| Some x_then; Some x_else |])) in 
		
		let cmds = cmds @ [                             (*            cmds                                *)
			(None, None,          cmd_gv_x);              (*            x_v := i__getValue (x) with err     *)
			(None, None,          cmd_tn_x);              (*            x_n := i__toNumber (x_v) with err   *)
			(None, None,          cmd_goto_nan);          (*            goto [x_n = nan] then else          *)
			(None, Some then_lab, cmd_ass_xthen);         (* then:      x_then := nan                       *)
			(None, None,          SLGoto end_lab);        (*            goto end                            *)
			(None, Some else_lab, cmd_ass_xelse);         (* else:      x_else := (negative x_n)            *)
			(None, Some end_lab,  cmd_ass_xr)             (* end:       x_r := PHI(x_then, x_else)          *)
		] in 
		let errs = errs @ [ x_v; x_n ] in 
		cmds, Var x_r, errs, [], [], []


	| Parser_syntax.Unary_op (Parser_syntax.Bitnot, e) ->
		(**
			Section: 11.4.8
      C(e) = cmds, x
			C(~e) =        cmds 
			               x_v := i__getValue (x) with err
							       x_n := i__toNumber (x_v) with err
										 x_i32 := (num_to_int32 x_n)
										 x_r := (! x_i32) 
     *)
		
		let cmds, x, errs, _, _, _ = f e in  
		
		(* x_v := i__getValue (x) with err *)
		let x_v, cmd_gv_x = make_get_value_call x err in
		
		(* x_n := i__toNumber (x_v) with err *) 
		let x_n, cmd_tn_x = make_to_number_call x x_v err in
		
		let x_r = fresh_var () in 
		let x_i32 = fresh_var () in 
		let cmds = cmds @ [                                                              (*  cmds                                *)
			(None, None, cmd_gv_x);                                                        (*  x_v := i__getValue (x) with err     *)
			(None, None, cmd_tn_x);                                                        (*  x_n := i__toNumber (x_v) with err   *)
			(None, None, SLBasic (SAssignment (x_i32, UnaryOp (ToInt32Op, Var x_n))));     (*  x_i32 := (num_to_int32 x_n)         *) 
			(None, None, SLBasic (SAssignment (x_r, UnaryOp (BitwiseNot, Var x_i32))))     (*  x_r := (! x_i32)                    *)    
		] in 
		let errs = errs @ [ x_v; x_n ] in 
		cmds, Var x_r, errs, [], [], []

									
	| Parser_syntax.Unary_op (Parser_syntax.Not, e) ->
		(**
      Section: 11.4.9
	  	C(e)  =  cmds, x 
	   	C(!e) =  cmds
			         x_v := i__getValue (x) with err
				   	   x_b := i__toBoolean (x_v) with err 
						   x_r := not x_b  
     *)
		
		let cmds, x, errs, _, _, _ = f e in 
		
		(* x_v := i__getValue (x) with err1 *) 
		let x_v, cmd_gv_x = make_get_value_call x err in 
		
		(* x_b := i__toBoolean (x_v) with err2 *)
		let x_b, cmd_tb_x = make_to_boolean_call x x_v err in
		
		(*  x_r := (not x_b)   *) 
		let x_r = fresh_var () in 
		let cmd_xr_ass = SLBasic (SAssignment (x_r, UnaryOp (Not, Var x_b))) in 
		
		let cmds = cmds @ [                        (* cmds                               *)
			(None, None, cmd_gv_x);                  (* x_v := i__getValue (x) with err    *) 
			(None, None, cmd_tb_x);                  (* x_b := i__toBoolean (x_v) with err *)
			(None, None, cmd_xr_ass);                (* x_r := (not x_b)                   *) 
		] in 
		let errs = errs @ [ x_v; x_b ] in
		cmds, Var x_r, errs, [], [], []
				
	
	| Parser_syntax.BinOp (e1, (Parser_syntax.Arith aop), e2) 
		when ((aop = Parser_syntax.Times) || (aop = Parser_syntax.Div) || (aop = Parser_syntax.Mod) || (aop = Parser_syntax.Minus)) ->
		(** Sections 11.5 + 11.6.2 
			  C(e1) = cmds1, x1; C(e2) = cmds2, x2 
				C(e1 * e2) =  cmds1
				              x1_v := i__getValue (x1) with err
				              cmds2
											x2_v := i__getValue (x2) with err
											x1_n := i__toNumber (x1_v) with err 
											x2_n := i__toNumber (x2_v) with err  
											x_r := x1_n * x2_n
		*) 
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r = translate_multiplicative_binop x1 x2 x1_v x2_v aop err in 
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2] @ new_cmds in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r, errs, [], [], []
	
	
	| Parser_syntax.BinOp (e1, (Parser_syntax.Arith Parser_syntax.Plus), e2) ->
		(** 
			Section 11.6.1 
			C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 + e2) =          cmds1
											      x1_v := i__getValue (x1) with err
														cmds2 
											      x2_v := i__getValue (x2) with err
														x1_p := i__toPrimitive (x1_v) with err
														x2_p := i__toPrimitive (x2_v) with err
											      goto [((typeOf x1_p) = $$string_type) or ((typeOf x2_p) = $$string_type)] then else  
									    then: x1_s := i__toString (x1_p) with err
											      x2_s := i__toString (x2_p) with err
														x_rthen := x1_s :: x2_s 
														goto end 
										  else: x1_n := i__toNumber (x1_p) with err
											      x2_n := i__toNumber (x2_p) with err
														x_relse := x1_n + x2_n 
											end:  x_r := PHI (x_rthen, x_relse)
		*)  
		
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r = translate_binop_plus x1 x2 x1_v x2_v err in 
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r, errs, [], [], []
		
		
	| Parser_syntax.BinOp (e1, (Parser_syntax.Arith Parser_syntax.Lsh), e2) ->
	  (**
      Section 11.7.1
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 << e2) =    cmds1 
			                 x1_v := i__getValue (x1) with err
				               cmds2 
											 x2_v := i__getValue (x2) with err
											 x1_i32 := i__toInt32 (x1_v) with err
											 x2_ui32 := i__toUInt32 (x2_v) with err
											 x_r := x1_i32 << x2_ui32
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r = translate_bitwise_shift x1 x2 x1_v x2_v toInt32Name toUInt32Name LeftShift err in  
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r, errs, [], [], []
	
	
	| Parser_syntax.BinOp (e1, (Parser_syntax.Arith Parser_syntax.Rsh), e2) ->
	  (**
      Section 11.7.2
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
		  C(e1 >> e2) =    cmds1 
					             x1_v := i__getValue (x1) with err
				               cmds2 
											 x2_v := i__getValue (x2) with err
											 x1_i32 := i__toInt32 (x1_v) with err
											 x2_ui32 := i__toUInt32 (x2_v) with err
											 x_r := x1_i32 >> x2_ui32
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r = translate_bitwise_shift x1 x2 x1_v x2_v toInt32Name toUInt32Name UnsignedRightShift err in  
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds in
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r, errs, [], [], []
	
	
	| Parser_syntax.BinOp (e1, (Parser_syntax.Arith Parser_syntax.Ursh), e2) ->
	  (**
      Section 11.7.3
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 >>> e2) =   cmds1 
											 x1_v := i__getValue (x1) with err
											 cmds2 
											 x2_v := i__getValue (x2) with err
											 x1_ui32 := i__toUInt32 (x1_v) with err
											 x2_ui32 := i__toUInt32 (x2_v) with err
											 x_r := x1_ui32 >>> x2_ui32
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r = translate_bitwise_shift x1 x2 x1_v x2_v toUInt32Name toUInt32Name SignedRightShift err in  
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds in
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r, errs, [], [], []
	
			
	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.Lt), e2) ->
	  (**
      Section 11.8.1
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 < e2) =             cmds1 
				                       x1_v := i__getValue (x1) with err
				                       cmds2 
											         x2_v := i__getValue (x2) with err
											         x_ac := i__abstractComparison (x1_v, x2_v, true) with err
											         goto [ x_ac = undefined ] then end 
											  then:  x_undef := false 
											  end:   x_r := PHI(x_ac, x_undef)  
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r = translate_binop_comparison x1 x2 x1_v x2_v true true false err in 
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds in
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r, errs, [], [], []
	
	
	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.Gt), e2) ->
	  (**
      Section 11.8.2
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 > e2) =             cmds1 
				                       x1_v := i__getValue (x1) with err
				                       cmds2 
											         x2_v := i__getValue (x2) with err
											         x_ac := i__abstractComparison (x2_v, x1_v, false) with err
											         goto [ x_ac = undefined ] then end 
											  then:  x_undef := false 
											  end:   x_r := PHI(x_ac, x_undef)  
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r = translate_binop_comparison x1 x2 x1_v x2_v false false false err in 
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds in
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r, errs, [], [], []		
	
	
	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.Le), e2) ->
	  (**
      Section 11.8.3
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 <= e2) =            cmds1 
				                       x1_v := i__getValue (x1) with err
				                       cmds2 
											         x2_v := i__getValue (x2) with err
											         x_ac := i__abstractComparison (x2_v, x1_v, false) with err
											         goto [ x_ac = undefined] then end 
											  then:  x_undef := true 
											  end:   x_r1 := PHI(x_ac, x_undef)  
												       x_r2 := (not x_r1) 
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r1 = translate_binop_comparison x1 x2 x1_v x2_v false false true err in 	
		let x_r2 = fresh_var () in 
		let new_cmd = SLBasic (SAssignment (x_r2, UnaryOp (Not, (Var x_r1)))) in 
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds @ [ b_annot_cmd new_cmd ] in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r2, errs, [], [], []		
	
	
	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.Ge), e2) ->
	  (**
      Section 11.8.4
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 >= e2) =            cmds1 
											         x1_v := i__getValue (x1) with err
				                       cmds2 
											         x2_v := i__getValue (x2) with err
											         x_ac := i__abstractComparison (x1_v, x2_v, true) with err
											         goto [ x_ac = undefined] then end 
											  then:  x_undef := true 
											  end:   x_r1 := PHI(x_ac, x_undef)  
												       x_r2 := (not x_r1) 
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r1 = translate_binop_comparison x1 x2 x1_v x2_v true true true err in 	
		let x_r2 = fresh_var () in 
		let new_cmd = SLBasic (SAssignment (x_r2, UnaryOp (Not, (Var x_r1)))) in 
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds @ [ b_annot_cmd new_cmd ] in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r2, errs, [], [], []		
		
		
	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.InstanceOf), e2) ->
	  (**
      Section 11.8.6
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 instanceof e2) =            cmds1
			                                 x1_v := i__getValue (x1) with err
				                               cmds2
											                 x2_v := i__getValue (x2) with err
											                 goto [ (typeOf x2_v) = $$object_type ] next1 err
											         next1:  x_cond := hasField (x2_v, "i__hasInstance") 
															         goto [ x_cond ] next2 err
											         next2:  x_hi := [x2_v, "i__hasInstance"]  
												               x_r := x_hi (x2_v, x1_v) with err
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in	
	
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		(* goto [ (typeOf x2_v) = $$object_type ] next1 err *)
		let next1 = fresh_label () in 
		let cmd_goto_ot = SLGuardedGoto (BinOp (TypeOf (Var x2_v), Equal, Literal (Type ObjectType)), next1, err) in 
		
		(* next1: x_cond := hasField (x2_v, "i__hasInstance")  *)
		let x_cond = fresh_var () in 
		let cmd_hasfield = SLBasic (SHasField (x_cond, Var x2_v, Literal (String hasInstanceName))) in 
		
		(* goto [ x_cond ] next2 err  *)
		let next2 = fresh_label () in 
		let cmd_goto_xcond = SLGuardedGoto (Var x_cond, next2, err) in 
		
		(* next2:  x_hi := [x2_v, "i__hasInstance"]   *) 
		let x_hi = fresh_var () in 
		let cmd_ass_xhi = SLBasic (SLookup (x_hi, Var x2_v, Literal (String hasInstanceName))) in 
		
		(* x_r := x_hi (x2_v, x1_v) with err *) 
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLCall (x_r, Var x_hi, [Var x2_v; Var x1_v], Some err) in 
		
		let cmds = cmds1 @                          (*         cmds1                                              *)
		[ (None, None,         cmd_gv_x1)           (*         x1_v := i__getValue (x1) with err                  *)
		] @ cmds2 @ [                               (*         cmds2                                              *)
			(None, None,         cmd_gv_x2);          (*         x2_v := i__getValue (x2) with err                  *)    
			(None, None,         cmd_goto_ot);        (*         goto [ (typeOf x2_v) = $$object_type ] next1 err   *)
			(None, Some next1,   cmd_hasfield);       (* next1:  x_cond := hasField (x2_v, "i__hasInstance")        *)
			(None, None,         cmd_goto_xcond);     (*         goto [ x_cond ] next2 err                          *)
			(None, Some next2,   cmd_ass_xhi);        (* next2:  x_hi := [x2_v, "i__hasInstance"]                   *)
			(None, None,         cmd_ass_xr)          (*         x_r := x_hi (x2_v, x1_v) with err                  *)
		] in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v; var_se; var_se; x_r ] in 
		cmds, Var x_r, errs, [], [], []
											  
																			              
	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.In), e2) ->
	  (**
      Section 11.8.7
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 in e2) =                    cmds1
			                                 x1_v := i__getValue (x1) with err
				                               cmds2
											                 x2_v := i__getValue (x2) with err
											                 goto [ (typeOf x2_v) = $$object_type ] next1 err 
											         next1:  x1_s := i__toString (x1_v) with err
															         x_r := o__hasProperty (x2_v, x1_s) with err 
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
	
		(* x2_v := getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in	
		
		(* goto [ (typeOf x2_v) = $$object_type ] next1 err *)
		let next1 = fresh_label () in 
		let cmd_goto_ot = SLGuardedGoto (BinOp (TypeOf (Var x2_v), Equal, Literal (Type ObjectType)), next1, err) in 
		
		(* next1: x1_s := i__toString (x1_v) with err   *)
		let x1_s, cmd_ts_x1 = make_to_string_call x1 x1_v err in
		
		(*  x_r := o__hasProperty (x2_v, x1_s) with err   *)
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLCall (x1_s, (Literal (String hasPropertyName)), [ Var x2_v; Var x1_s ], Some err) in 
		
		let cmds = cmds1 @ [                        (*         cmds1                                             *)
			(None, None,         cmd_gv_x1)           (*         x1_v := getValue (x1) with err                    *)
		] @ cmds2 @ [                               (*         cmds2                                             *)
			(None, None,         cmd_gv_x2);          (*         x2_v := getValue (x2) with err                    *)    
			(None, None,         cmd_goto_ot);        (*         goto [ (typeOf x2_v) = $$object_type ] next1 err  *)
			(None, Some next1,   cmd_ts_x1);          (* next1:  x1_s := i__toString (x1_v) with err               *)
			(None, None,         cmd_ass_xr);         (*         x_r := o__hasProperty (x2_v, x1_s) with err       *)
		] in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v; var_se; x1_s; x_r ] in 
		cmds, Var x_r, errs, [], [], []			               
											        
															         
	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.Equal), e2) ->
	  (**
      Section 11.9.1
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 == e2) =                    cmds1 
																			 x1_v := i__getValue (x1) with err
				                               cmds2 
											                 x2_v := i__getValue (x2) with err
											                 x_r := i__abstractEqualityComparison (x1_v, x2_v) with err 
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r = translate_binop_equality x1 x2 x1_v x2_v true true err in 
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r, errs, [], [], []	
													      
	
	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.NotEqual), e2) ->
	  (**
      Section 11.9.2
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 != e2) =                    cmds1
			                                 x1_v := i__getValue (x1) with err
				                               cmds2 
													 		         x2_v := i__getValue (x2) with err
											                 x_r1 := i__abstractEqualityComparison (x1_v, x2_v) with err 
																			 x_r2 := (not x_r1)
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r = translate_binop_equality x1 x2 x1_v x2_v true false err in 
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r, errs, [], [], []																			
					
																																																																																																	            		
	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.TripleEqual), e2) ->
	  (**
      Section 11.9.4
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 === e2) =                   cmds1 
													 		         x1_v := i__getValue (x1) with err
				                               cmds2 
											                 x2_v := i__getValue (x2) with err
											                 x_r := i__strictEqualityComparison (x1_v, x2_v) with err 
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r = translate_binop_equality x1 x2 x1_v x2_v false true err in 
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r, errs, [], [], []	
	
	
	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.NotTripleEqual), e2) ->
	  (**
      Section 11.9.5
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
	  	C(e1 !== e2) =                   cmds1 
													 		         x1_v := i__getValue (x1) with err
				                               cmds2 
											                 x2_v := i__getValue (x2) with err
											                 x_r1 := i__strictEqualityComparison (x1_v, x2_v) with err
																			 x_r2 := (not x_r1)
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r = translate_binop_equality x1 x2 x1_v x2_v false false err in 
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r, errs, [], [], []	
	
	
	| Parser_syntax.BinOp (e1, (Parser_syntax.Arith bbop), e2) 
		when ((bbop = Parser_syntax.Bitand) || (bbop = Parser_syntax.Bitor) || (bbop = Parser_syntax.Bitxor)) ->
	  (**
      Section 11.10
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 == e2) =                    cmds1 
													 		         x1_v := i__getValue (x1) with err
				                               cmds2 
											                 x2_v := i__getValue (x2) with err
																			 x1_i32 := i__toInt32 (x1_v) with err
																			 x2_i32 := i__toInt32 (x2_v) with err 
																			 x_r := (x1_i32 bbop x2_i32)
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in 
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
	
		let new_cmds, new_errs, x_r = translate_bitwise_bin_op x1 x2 x1_v x2_v bbop err in 
		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs in 
		cmds, Var x_r, errs, [], [], []	
		
		
	| Parser_syntax.BinOp (e1, (Parser_syntax.Boolean lbop), e2) ->
		(**
      Section 11.11 
      C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 && e2) =                    cmds1 
													 		         x1_v := i__getValue (x1) with err1
																			 x1_b := i__toBoolean (x1_v) with err2 
																			 goto [x1_b] next end 
																 next: cmds2
																       x2_v := i__getValue (x2) with err3
																 end:  x_r := PHI(x1_v, x2_v)
     *)
 		translate_bin_logical_operator e1 e2 lbop err
		
	| Parser_syntax.ConditionalOp (e1, e2, e3) ->
		(**
      Section 11.12 
      C(e1) = cmds1, x1; C(e2) = cmds2, x2; C(e3) = cmds3, x3
			C(e1 ? e2 : e3) =                cmds1 
													 		         x1_v := i__getValue (x1) with err
																			 x1_b := i__toBoolean (x1_v) with err
																			 goto [x1_b] then else 
														  then:    cmds2 
																       x2_v := i__getValue (x2) with err
																			 goto end_if
														  else:    cmds3 
																       x3_v := i__getValue (x3) with err
															end_if:  x_r := PHI(x2_v, x3_v) 
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		let cmds3, x3, errs3, _, _, _ = f e3 in
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x1_b := i__toBoolean (x1_v) with err  *)
		let x1_b, cmd_tb_x1 = make_to_boolean_call x1 x1_v err in
		(* goto [x1_b] then else *)
		let then_lab = fresh_then_label () in 
		let else_lab = fresh_else_label () in 
		let end_if_lab = fresh_endif_label () in 
		let cmd_goto = SLGuardedGoto (Var x1_b, then_lab, else_lab) in 
		(* x2_v := i__getValue (x2) with err *) 
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		(* x3_v := i__getValue (x3) with err *) 
		let x3_v, cmd_gv_x3 = make_get_value_call x3 err in
		(* x_r := PHI(x2_v, x3_v) *) 
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLBasic (SPhiAssignment (x_r, [| Some x2_v; Some x3_v |])) in 
		
		let cmds2 = add_initial_label cmds2 then_lab in 
		let cmds3 = add_initial_label cmds3 else_lab in 
		let cmds = cmds1 @ [                           (*         cmds1                                              *)
			(None, None,            cmd_gv_x1);          (*         x1_v := i__getValue (x1) with err                  *)
			(None, None,            cmd_tb_x1);          (*         x1_b := i__toBoolean (x1_v) with err               *)
			(None, None,            cmd_goto)            (*         goto [x1_b] then else                              *)
		] @ cmds2 @ [                                  (* then:   cmds2                                              *)
			(None, None,            cmd_gv_x2);          (*         x2_v := i__getValue (x2) with err                  *)    
			(None, None,            SLGoto end_if_lab)   (*         goto end_if                                        *)
		] @ cmds3 @ [                                  (* else:   cmds3                                              *)
			(None, None,            cmd_gv_x3);          (*         x3_v := i__getValue (x3) with err                  *)    
			(None, Some end_if_lab, cmd_ass_xr)          (* end_if: x_r := PHI(x2_v, x3_v)                             *)
		] in 
		
		let errs = errs1 @ [ x1_v; x1_b ] @ errs2 @ [ x2_v ] @ errs3 @ [ x3_v ] in 
		cmds, Var x_r, errs, [], [], [] 
		
		
	| Parser_syntax.Assign (e1, e2) ->
		(**
      Section 11.13.1 - Simple Assignment 
			C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1 = e2) =      cmds1 
			                  cmds2 
			                  x2_v := i__getValue (x2) with err
			 		              x_cae := i__checkAssignmentErrors (x1) with err
								        x_pv = i__putValue (x1, x2_v) with err
     *)
		
		let cmds1, x1, errs1, _, _, _ = f e1 in 
		let cmds2, x2, errs2, _, _, _ = f e2 in 
		
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in 
		
		(*  x_cae := i__checkAssignmentErrors (x1) with err *)
		let x_cae, cmd_cae_x1 = make_cae_call x1 err in 
		
		(* x_pv = i__putValue (x1, x2_v) with err *)
		let x_pv, cmd_put_value = make_put_value_call x1 x2_v err in 

		let cmds = 
			cmds1 @                                   (*   cmds1                                           *)
			cmds2 @	[                                 (*   cmds2                                           *)
			(None, None, cmd_gv_x2);                  (*   x2_v := i__getValue (x2) with err               *)
			(None, None, cmd_cae_x1);                 (*   x_cae := i__checkAssertionErrors (x1) with err  *) 
			(None, None, cmd_put_value)               (*   x_pv := i__putValue (x1, x2_v) with err         *)  
		] in 
		let errs = errs1 @ errs2 @ [ x2_v; x_cae; x_pv ] in 
		cmds, (Var x2_v), errs, [], [], []
	
	
	| Parser_syntax.AssignOp (e1, op, e2) ->
		(**
      Section 11.13.1 - Compound Assignment 
			C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C_op(x1_v, x2_v) = cmds, x
			C(e1 op= e2) =    cmds1
			                  x1_v := i__getValue (x1) with err 
			                  cmds2
			                  x2_v := i__getValue (x2) with err
												cmds
					              x_cae := i__checkAssignmentErrors (x1) with err 
	              next:   x_pv = putValue (x1, x) with err
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in 
		let cmds2, x2, errs2, _, _, _ = f e2 in 
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in
		
		let new_cmds, new_errs, x_r = 
			(match op with 
			| Parser_syntax.Plus -> translate_binop_plus x1 x2 x1_v x2_v err
			| Parser_syntax.Minus 
			| Parser_syntax.Times
			| Parser_syntax.Div
			| Parser_syntax.Mod -> translate_multiplicative_binop x1 x2 x1_v x2_v op err
			| Parser_syntax.Ursh -> translate_bitwise_shift x1 x2 x1_v x2_v toUInt32Name toUInt32Name SignedRightShift err
			| Parser_syntax.Lsh -> translate_bitwise_shift x1 x2 x1_v x2_v toInt32Name toUInt32Name LeftShift err
			| Parser_syntax.Rsh -> translate_bitwise_shift x1 x2 x1_v x2_v toInt32Name toUInt32Name UnsignedRightShift err
			| Parser_syntax.Bitand 
      | Parser_syntax.Bitor 
      | Parser_syntax.Bitxor -> translate_bitwise_bin_op x1 x2 x1_v x2_v op err) in  
		
		(* x_cae := i__checkAssertionErrors (x1) with err *)
		let x_cae, cmd_cae_x1 = make_cae_call x1 err in  
		
		(* x_pv = i__putValue (x1, x_r) with err *)
		let x_pv, cmd_pv = make_put_value_call x1 x_r err in 

		let cmds = cmds1 @ [ b_annot_cmd cmd_gv_x1 ] @ cmds2 @ [ b_annot_cmd cmd_gv_x2 ] @ new_cmds @ [                          
			(None, None, cmd_cae_x1);         (*    x_cae := i__checkAssertionErrors (x1) with err  *)
			(None, None, cmd_pv)              (*    x_pv = putValue (x1, x2_v) with err             *)  
		] in 
		let errs = errs1 @  [ x1_v ] @ errs2 @ [ x2_v ] @ new_errs @ [ var_se; x_pv ] in 
		cmds, (Var x_r), errs, [], [], []
	
	
	| Parser_syntax.Comma (e1, e2) ->
		(**
      Section 11.14 - Comma Operator
			C(e1) = cmds1, x1; C(e2) = cmds2, x2 
			C(e1, e2) =    cmds1
			               x1_v := i__getValue (x1) with err
			               cmds2
			               x2_v := i__getValue (x2) with err
     *)
		let cmds1, x1, errs1, _, _, _ = f e1 in 
		let cmds2, x2, errs2, _, _, _ = f e2 in 
		
		(* x1_v := getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in 
		
		(* x2_v := getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in 	
		
		let cmds = 
			cmds1 @ [                                 (*       cmds1                                *)
				(None, None, cmd_gv_x1)                 (*       x1_v := i__getValue (x1) with err    *)            
			] @ cmds2 @	[                             (*       cmds2                                *) 
				(None, None, cmd_gv_x2)                 (*       x2_v := i__getValue (x2) with err    *)
			] in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v ] in 
		cmds, (Var x2_v), errs, [], [], []
	
	
	(** Statements **) 

	| Parser_syntax.Script (_, es)  
	| Parser_syntax.Block es -> 
		(**
     Section 12.1 - Block
		
		 C_iter({}) = [], $$empty
		
		 C(stmts) = cmds, x
		 C(stmt) = cmds', x'
		 CanBeEmpty(stmt) 
		 ------------------------- 
		 C_iter(stmts; stmt) =        cmds 
						      					      cmds'
											            goto [x' = $$empty] next end 
									         next:  skip 
											     end:   x'' := PHI(x', x)   
		
		
		
		 C_iter(stmts) = cmds, x
		 C_iter(stmt) = cmds', x'
		 !CanBeEmpty(stmt) 
		 ------------------------- 
		 C_iter(stmts; stmt) =   cmds 
											       cmds' 
														
														
		 C_iter (stmts) = cmds, x 											
		 -------------------------------
		 C(Block stmts) = cmds 
		                  x_ret := PHI (break_vars, x)  
     *)
		
		let break_label, new_loop_list = 
			(match js_lab with 
			| None -> None, loop_list 
			| Some lab -> 
				let break_label = fresh_break_label () in 
				Some break_label, ((None, break_label, js_lab) :: loop_list)) in 
		
		let rec loop es bprevious cmds_ac errs_ac rets_ac breaks_ac conts_ac = 
			(match es with 
			| [] -> [], Literal Empty, [], [], [], []
			
			| [ e ] -> 
				let cmds_e, x_e, errs_e, rets_e, breaks_e, conts_e = f_previous new_loop_list bprevious None e in
				(match (Js_pre_processing.returns_empty_exp e), bprevious with 
				| true, Some x_previous -> 
					(let new_cmds, x_r = make_check_empty_test x_previous x_e in 
					cmds_ac @ cmds_e @ new_cmds, Var x_r, errs_ac @ errs_e, rets_ac @ rets_e, breaks_ac @ breaks_e, conts_ac @ conts_e)
				| _, _ -> 
					cmds_ac @ cmds_e, x_e, errs_ac @ errs_e, rets_ac @ rets_e, breaks_ac @ breaks_e, conts_ac @ conts_e)
			
			| e :: rest_es -> 
				let cmds_e, x_e, errs_e, rets_e, breaks_e, conts_e = f_previous new_loop_list bprevious None e in
				(match (Js_pre_processing.returns_empty_exp e), bprevious with 
				| true, Some x_previous -> 
					(let new_cmds, x_r = make_check_empty_test x_previous x_e in 
					loop rest_es (Some (Var x_r)) (cmds_ac @ cmds_e @ new_cmds) (errs_ac @ errs_e) (rets_ac @ rets_e) (breaks_ac @ breaks_e) (conts_ac @ conts_e))
				| _, _ -> 
					loop rest_es (Some x_e) (cmds_ac @ cmds_e) (errs_ac @ errs_e) (rets_ac @ rets_e) (breaks_ac @ breaks_e) (conts_ac @ conts_e))) in 
		
		let cmds, x, errs, rets, breaks, conts = loop es previous [] [] [] [] [] in 
		create_final_phi_cmd cmds x errs rets breaks conts break_label js_lab
	
	 
	| Parser_syntax.VarDec decs -> 
		(**
     Section 12.2 - Variable Statement
		
		  vdec ::= x | x = e
			vdecs ::= vdec, vdecs  | []
		
		
		  C_dec (x) = []
			
			C(e) = cmds, x 
			--------------------------
			C_dec(x = e) = cmds 
			               x_v := i__getValue(x) with err
										 x_sf := [x__scope, fid] 
										 x_ref := ref_v(x_sf, "x") 
										 x_pv := i__putValue(x_ref, x_v) with err
			
			C_dec(vdec) = cmds1
			C_dec(vdecs) = cmds2 
			--------------------------
			C_dec (vdec, vdecs) = cmds1
			                      cmds2 
			
			C_dec ([]) = []
			 							
			C_dec(vdecs) = cmds
			--------------------------							
		  C(var vdecs) = cmds
			               x := $$empty
		 
     *)
		let rec loop decs cmds errs = 
			(match decs with 
			| [] -> 
				let x, empty_ass = make_empty_ass () in 
				x, cmds @ [ b_annot_cmd empty_ass ], errs 
			| (v, eo) :: rest_decs -> 
				(match eo with 
				| None -> loop rest_decs cmds errs 
				| Some e ->
					let cmds_e, x, errs_e, _, _, _ = f e in
					(* x_v := i__getValue (x) with err *)
					let x_v, cmd_gv_x = make_get_value_call x err in
					(* x_sf := [x__scope, fid]  *) 
					let x_sf = fresh_var () in 
					let cmd_xsf_ass = SLBasic (SLookup (x_sf, Var var_scope, Literal (String fid))) in 
					(* x_ref := ref_v(x_sf, "x")  *) 
					let x_ref = fresh_var () in 
					let cmd_xref_ass = SLBasic (SAssignment (x_ref, VRef (Var x_sf, Literal (String v)))) in 
					(* x_pv := i__putValue(x_ref, x_v) with err2 *) 
					let x_pv, cmd_pv = make_put_value_call (Var x_ref) x_v err in 
					let cmds = cmds @ cmds_e @ (b_annot_cmds [
						 cmd_gv_x;      (* x_v := i__getValue (x) with err          *)
						 cmd_xsf_ass;   (* x_sf := [x__scope, fid]                  *)
						 cmd_xref_ass;  (* x_ref := ref_v(x_sf, "x")                *) 
						 cmd_pv        	(* x_pv := i__putValue(x_ref, x_v) with err *) 
					]) in 
					let errs = errs @ errs_e @ [ x_v; x_pv ] in 
					loop rest_decs cmds errs)) in 
		let x, cmds, errs = loop decs [] [] in 
		cmds, Var x, errs, [], [], []
	
	
	| Parser_syntax.Skip ->
		(** 
     Section 12.3 - Empty Statement 
		 *) 
		 [], Literal Empty, [], [], [], [] 
	
		
	| Parser_syntax.If (e1, e2, e3) -> 
		(**
     Section 12.5 - If Statement 
     *  C(e1) = cmds1, x1; C(e2) = cmds2, x2; C(e3) = cmds3, x3
		 *  
		 *  C(if (e1) { e2 } else { e3 }) = 
			       cmds1
						 x1_v := i__getValue (x1) with err
						 x1_b := i__toBoolean (x1_b) with err  
						 goto [x1_b] then else 
			then:  cmds2
			       goto endif
			else:  cmds3 
			endif: x_if := PHI(x2, x3)   
		 *)
		
		let break_label, new_loop_list = 
			(match js_lab with 
			| None -> None, loop_list 
			| Some lab -> 
				let break_label = fresh_break_label () in 
				Some break_label, ((None, break_label, js_lab) :: loop_list)) in
		
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let cmds2, x2, errs2, rets2, breaks2, conts2 = f_previous new_loop_list None None e2 in
		let cmds3, x3, errs3, rets3, breaks3, conts3 = 
			(match e3 with 
			| None -> 
				let x3, cmd3 = make_empty_ass () in   
				[ (b_annot_cmd cmd3) ], Var x3, [], [], [], []
			| Some e3 -> f_previous new_loop_list None None e3) in 
		
		(* x1_v := getValue (x1) with err *) 
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in 
		
		(* x1_b := toBoolean (x1_v) with err *)
		let x1_b, cmd_tb_x1 = make_to_boolean_call x1 x1_v err in 
		
		(* goto [x1_b] then else *) 
		let then_lab = fresh_then_label () in 
		let else_lab = fresh_else_label () in 
		let end_lab = fresh_end_label () in  
		let cmd_goto_if = SLGuardedGoto (Var x1_b, then_lab, else_lab) in 
	
		let cmds2 = add_initial_label cmds2 then_lab in 
		let cmds3 = add_initial_label cmds3 else_lab in 	
		
		let cmds2, x2 = add_skip_if_empty cmds2 x2 in 
		let cmds3, x3 = add_skip_if_empty cmds3 x3 in 
		
		(* goto end *)  
		let cmd_goto_endif = SLGoto end_lab in 
		
		(* end: x_if := PHI(x2, x3) *) 
		let x2_name, x3_name = 
			(match x2, x3 with 
			| Var x2_name, Var x3_name -> x2_name, x3_name 
			| _, _ -> raise (Failure "the compilation of the then and else parts of the ifs must generate a variable each")) in 
		let x_if = fresh_var () in 
		let cmd_end_if = SLBasic (SPhiAssignment (x_if, [| Some x2_name; Some x3_name |])) in 
		
		let cmds = 
			    cmds1 @ [                             (*       cmds1                               *)
				(None, None,           cmd_gv_x1);      (*       x1_v := getValue (x1) with err      *)
				(None, None,           cmd_tb_x1);      (*       x1_b := toBoolean (x1_v) with err   *)
				(None, None,           cmd_goto_if)     (*       goto [x1_b] then else               *) 
			] @ cmds2 @ [                             (* then: cmds2                               *)
				(None, None,           cmd_goto_endif)  (*       goto end                            *)
			] @ cmds3 @ [                             (* else: cmds3                               *)
				(None, Some end_lab, cmd_end_if)        (* end:  x_if := PHI(x3, x2)                 *)
			] in 
		let errs = errs1 @ [ x1_v; x1_b ] @ errs2 @ errs3 in 
		
		let cmds, x, errs, rets, breaks, conts = cmds, Var x_if, errs, rets2 @ rets3, breaks2 @ breaks3, conts2 @ conts3 in 
		create_final_phi_cmd cmds x errs rets breaks conts break_label js_lab
	
	
	| Parser_syntax.DoWhile (e1, e2) -> 
		(**
     Section 12.6.1 - The do-while Statement
     *  C(e1) = cmds1, x1; C(e2) = cmds2, x2
		 *  
		 *  C(do { e1 } while (e2) ) =
			          x_ret_0 := $$empty 
			head:     x_ret_1 := PHI(x_ret_0, x_ret_3) 
								cmds1 
			          x1_v := i__getValue (x1) with err
			cont:	    x_ret_2 := PHI(cont_vars, x1_v) 					
					      goto [ not (x_ret_2 = $$empty) ] next1 next2 
		  next1:    skip 
			next2:    x_ret_3 := PHI(x_ret_1, x_ret_2)
			guard:    cmds2
								x2_v := i__getValue (x2) with err
								x2_b := i__toBoolean (x2_v) with err 
								goto [x2_b] head end_loop 
		  end_loop: x_ret_4 := PHI(break_vars, x_ret_3) 
			          goto [ x_ret_4 = $$empty ] next3 next4
			next3:    skip 
			next4:    x_ret_5 := PHI(x_ret_4, x_ret_1) 
		 *)		
		
		let head, guard, body, cont, end_loop = fresh_loop_vars () in 
		
		let new_loop_list = (Some cont, end_loop, js_lab) :: loop_list in 
		let cmds1, x1, errs1, rets1, breaks1, conts1 = translate fid cc_table ctx vis_fid err new_loop_list None None e1 in
		let cmds2, x2, errs2, _, _, _ = f e2 in
		let cmds2 = add_initial_label cmds2 guard in
		
		let cur_breaks, outer_breaks = filter_cur_jumps breaks1 js_lab true in 
		let cur_conts, outer_conts = filter_cur_jumps conts1 js_lab true in 
		
		(* x_ret_0 := $$empty *) 
		let x_ret_0, cmd_ass_ret_0 = make_empty_ass () in 
		
		(* x_ret_1 := PHI(x_ret_0, x_ret_3)  *) 
		let x_ret_1 = fresh_var () in 
		let x_ret_2 = fresh_var () in 
		let x_ret_3 = fresh_var () in 
		let cmd_ass_ret_1 = SLBasic (SPhiAssignment (x_ret_1, [| Some x_ret_0; Some x_ret_3 |])) in 
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in 
		
		(* x_ret_2 := PHI(cont_vars, x1_v) *) 
		let cur_conts = cur_conts @ [ x1_v ] in 
		let cur_conts = List.map (fun x -> Some x) cur_conts in 
		let cont_vars = Array.of_list cur_conts in 
		let cmd_ass_ret_2 = SLBasic (SPhiAssignment (x_ret_2, cont_vars)) in
		
		(*  goto [ not (x_ret_2 = $$empty) ] next1 next2 *)
		let next1 = fresh_next_label () in 
		let next2 = fresh_next_label () in 
		let expr_goto_guard = BinOp (Var x_ret_2, Equal, Literal Empty) in 
		let expr_goto_guard = UnaryOp (Not, expr_goto_guard) in 
		let cmd_goto_empty_test = SLGuardedGoto (expr_goto_guard, next1, next2) in
		
		(* x_ret_3 := PHI(x_ret_1, x_ret_2)  *) 
		let cmd_ass_ret_3 = SLBasic (SPhiAssignment (x_ret_3, [| Some x_ret_1; Some x_ret_2 |])) in 
		
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in 
		
		(* x2_b := i__toBoolean (x2_v) with err *)
		let x2_b, cmd_tb_x2 = make_to_boolean_call x2 x2_v err in 
		
		(* goto [x2_b] head end_loop *)
		let cmd_dowhile_goto =  SLGuardedGoto (Var x2_b, head, end_loop) in 
		
		let cmds_end_loop, x_ret_5 = make_loop_end x_ret_3 x_ret_1 cur_breaks end_loop false in 
		
		let cmds = 
				[
					(None, None,             cmd_ass_ret_0);         (*              x_ret_0 := $$empty                           *)
					(None, Some head,        cmd_ass_ret_1);         (* head:        x_ret_1 := PHI(x_ret_0, x_ret_3)             *) 
				] @ cmds1 @ [                                      (*              cmds1                                        *)
				  (None, None,             cmd_gv_x1);             (*              x1_v := i__getValue (x1) with err            *)
					(None, Some cont,        cmd_ass_ret_2);         (* cont:	       x_ret_2 := PHI(cont_vars, x1_v) 	            *) 
					(None, None,             cmd_goto_empty_test);   (*              goto [ not (x_ret_2 = $$empty) ] next1 next2 *)
					(None, Some next1,       SLBasic SSkip);         (* next1:       skip                                         *)
					(None, Some next2,       cmd_ass_ret_3);         (* next2:       x_ret_3 := PHI(x_ret_1, x_ret_2)             *)  
				] @ cmds2 @ [                                      (* guard:       cmds2                                        *)
				  (None, None,             cmd_gv_x2);             (*              x2_v := i__getValue (x2) with err            *)
					(None, None,             cmd_tb_x2);             (*              x2_b := i__toBoolean (x2_v) with err         *)
					(None, None,             cmd_dowhile_goto);      (*              goto [x2_b] head end                         *)
				] @ cmds_end_loop in 
		let errs = errs1 @ [ x1_v ] @ errs2 @ [ x2_v; x2_b ] in 
		cmds, Var x_ret_5, errs, rets1, outer_breaks, outer_conts 	 
	
	
	| Parser_syntax.While (e1, e2) -> 
		(**
     Section 12.6.2 - The while Statement
     *  C(e1) = cmds1, x1; C(e2) = cmds2, x2
		 *  
		 *  C(while (e1) { e2 } ) =
			          x_ret_0 := $$empty 
			head:     x_ret_1 := PHI(x_ret_0, x_ret_3) 
					      cmds1
						    x1_v := i__getValue (x1) with err
						    x1_b := i__toBoolean (x1_b) with err  
						    goto [x1_b] body end_loop 
			body:     cmds2
						    x2_v := i__getValue (x2) with err
			cont:	    x_ret_2 := PHI(cont_vars, x2_v) 
								goto [not (x_ret_2 = $$empty)] next1 next2
			next1:    skip; 
			next2:    x_ret_3 := PHI(x_ret_1, x_ret_2) 
			          goto head 
			end_loop: x_ret_4 := PHI(x_ret_1, break_vars) 
			          goto [ x_ret_4 = $$empty ] next3 next4
			next3:    skip 
			next4:    x_ret_5 := PHI(x_ret_4, x_ret_1) 
		 *)
		
		let head, guard, body, cont, end_loop = fresh_loop_vars () in 
		
		let cmds1, x1, errs1, _, _, _ = f e1 in
		let new_loop_list = (Some cont, end_loop, js_lab) :: loop_list in 
		let cmds2, x2, errs2, rets2, breaks2, conts2 = translate fid cc_table ctx vis_fid err new_loop_list None None e2 in
		
		let cur_breaks, outer_breaks = filter_cur_jumps breaks2 js_lab true in 
		let cur_conts, outer_conts = filter_cur_jumps conts2 js_lab true in 
		
		(* x_ret_0 := $$empty *) 
		let x_ret_0, cmd_ass_ret_0 = make_empty_ass () in 
		let x_ret_1 = fresh_var () in 
		
		(* x_ret_1 := PHI(x_ret_0, x_ret_3) *)
		let x_ret_2 = fresh_var () in 
		let x_ret_3 = fresh_var () in 
		let cmd_ass_ret_1 = SLBasic (SPhiAssignment (x_ret_1, [| Some x_ret_0; Some x_ret_3 |])) in 
		
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1 = make_get_value_call x1 err in
		
		(* x1_b := i__toBoolean (x1_v) with err *)
		let x1_b, cmd_tb_x1 = make_to_boolean_call x1 x1_v err in
		
		(* goto [x1_b] body endwhile  *) 
		let cmd_goto_while = SLGuardedGoto (Var x1_b, body, end_loop) in 
		
		(* x2_v := i__getValue (x2) with err *) 
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in 
		
		(* x_ret_2 := PHI(cont_vars, x2_v) *)
		let cur_conts = cur_conts @ [ x2_v ] in 
		let cur_conts = List.map (fun x -> Some x) cur_conts in 
		let cont_vars = Array.of_list cur_conts in 
		let cmd_ass_ret_2 = SLBasic (SPhiAssignment (x_ret_2, cont_vars)) in
		
		(* goto [not (x_ret_2 = $$empty)] next1 next2 *) 
		let next1 = fresh_next_label () in 
		let next2 = fresh_next_label () in 
		let expr_goto_guard = BinOp (Var x_ret_2, Equal, Literal Empty) in 
		let expr_goto_guard = UnaryOp (Not, expr_goto_guard) in 
		let cmd_goto_empty_test = SLGuardedGoto (expr_goto_guard, next1, next2) in 
		
		(* x_ret_3 := PHI(x_ret_1, x_ret_2) *) 
		let cmd_ass_ret_3 = SLBasic (SPhiAssignment (x_ret_3, [| Some x_ret_1; Some x_ret_2 |])) in 
		
		let cmds_end_loop, x_ret_5 = make_loop_end x_ret_1 x_ret_1 cur_breaks end_loop true in
		
		let cmds2 = add_initial_label cmds2 body in 
		let cmds = 
			[
				(None, None,           cmd_ass_ret_0);         (*           x_ret_0 := $$empty                         *)
				(None, Some head, cmd_ass_ret_1);              (* head:     x_ret_1 := PHI(x_ret_0, x_ret_3)           *) 
			] @ cmds1 @ [                                    (*           cmds1                                      *)
			  (None, None,           cmd_gv_x1);             (*           x1_v := i__getValue (x1) with err          *)
				(None, None,           cmd_tb_x1);             (*           x1_b := i__toBoolean (x1_b) with err       *)
				(None, None,           cmd_goto_while)         (*           goto [x1_b] body endwhile                  *)
			] @ cmds2 @ [                                    (* body:     cmds2                                      *)
			  (None, None,           cmd_gv_x2);             (*           x2_v := i__getValue (x2) with err          *)
				(None, Some cont,      cmd_ass_ret_2);         (* cont:     x_ret_2 := PHI(cont_vars, x2_v)            *)
				(None, None,           cmd_goto_empty_test);   (*           goto [not (x_ret_2 = $$empty)] next1 next2 *)
			  (None, Some next1,     SLBasic SSkip);         (* next1:    skip                                       *) 
				(None, Some next2,     cmd_ass_ret_3);         (* next2:    x_ret_3 := PHI(x_ret_1, x_ret_2)           *) 
				(None, None,           SLGoto head);           (*           goto head                                  *)
			] @ cmds_end_loop in 
		let errs = errs1 @ [ x1_v; x1_b ] @ errs2 @ [ x2_v ] in 
		cmds, Var x_ret_5, errs, rets2, outer_breaks, outer_conts
	
	
	| Parser_syntax.For (e1, e2, e3, e4) ->
		(**
		 Section 12.6.3
     *  C(e1) = cmds1, _; C(e2) = cmds2, x2; C(e3) = cmds3, _; C(e4) = cmds4, x4
		 *  
		 *  C( for(e1; e2; e3) { e4 } ) =
			          cmds1 
								x_ret_0 := $$empty 
			head:     x_ret_1 := PHI(x_ret_0, x_ret_3) 
								cmds2
			          x2_v := i__getValue (x2) with err
								x2_b := i__toBoolean (x2_v) with err
								goto [x2_b] body end_loop 
			body: 		cmds4 
								x4_v := i__getValue (x4) with err
			cont:     x_ret_2 := PHI(cont_vars, x4_v) 
								goto [ not (x_ret_2 = $$empty) ] next1 next2 
		  next1:    skip 
			next2:    x_ret_3 := PHI(x_ret_1, x_ret_2)
			          cmds3
								goto head
		  end_loop:	x_ret_4 := PHI(x_ret_1, break_vars) 
			          goto [ x_ret_4 = $$empty ] next3 next4
			next3:    skip 
			next4:    x_ret_5 := PHI(x_ret_4, x_ret_1) 
		 *)	
		
		let cmds1, _, errs1, _, _, _ = 
			(match e1 with 
			| Some e1 -> f e1 
			| None -> [], Var "xpto", [], [], [], []) in
		
		let cmds2, x2, errs2, _, _, _ = 	
			(match e2 with 
			| Some e2 -> f e2 
			| None -> 
				let x2 = fresh_var () in 
				let cmd_ass_x2 = (None, None, SLBasic (SAssignment (x2, Literal (Bool true)))) in 
				[ cmd_ass_x2 ], Var x2, [], [], [], []) in
		
		let cmds3, _, errs3, _, _, _ = 
			(match e3 with 
			| Some e3 -> f e3 
			| None -> [], Var "xpto", [], [], [], []) in
		
		let head, guard, body, cont, end_loop = fresh_loop_vars () in 
		
		let new_loop_list = (Some cont, end_loop, js_lab) :: loop_list in 
		let cmds4, x4, errs4, rets4, breaks4, conts4 = translate fid cc_table ctx vis_fid err new_loop_list None None e4 in 
		
		let cur_breaks, outer_breaks = filter_cur_jumps breaks4 js_lab true in 
		let cur_conts, outer_conts = filter_cur_jumps conts4 js_lab true in 
		
		(* x_ret_0 := $$empty  *) 
		let x_ret_0, cmd_ass_ret_0 = make_empty_ass () in 
		
		(* head:     x_ret_1 := PHI(x_ret_0, x_ret_3)  *)
		let x_ret_1 = fresh_var () in 
		let x_ret_2 = fresh_var () in 
		let x_ret_3 = fresh_var () in 
		let cmd_ass_ret_1 = SLBasic (SPhiAssignment (x_ret_1, [| Some x_ret_0; Some x_ret_3 |])) in
		
		(* x2_v := i__getValue (x2) with err *) 
		let x2_v, cmd_gv_x2 = make_get_value_call x2 err in 	
		
	  (* x2_b := i__toBoolean (x2_v) with err2 *) 
		let x2_b, cmd_tb_x2 = make_to_boolean_call x2 x2_v err in 
		
		(* goto [x2_b] body end_loop *) 
		let body = fresh_loop_body_label () in 
		let cmd_for_goto =  SLGuardedGoto (Var x2_b, body, end_loop) in 
		
		(* x4_v := i__getValue (x4) with err *) 
		let x4_v, cmd_gv_x4 = make_get_value_call x4 err in 
		
		(* cont:     x_ret_2 := PHI(cont_vars, x4_v)  *)
		let cur_conts = cur_conts @ [ x4_v ] in 
		let cur_conts = List.map (fun x -> Some x) cur_conts in 
		let cont_vars = Array.of_list cur_conts in 
		let cmd_ass_ret_2 = SLBasic (SPhiAssignment (x_ret_2, cont_vars)) in
		
		(* 	goto [ not (x_ret_2 = $$empty) ] next1 next2  *) 
		let next1 = fresh_next_label () in 
		let next2 = fresh_next_label () in 
		let expr_goto_guard = BinOp (Var x_ret_2, Equal, Literal Empty) in 
		let expr_goto_guard = UnaryOp (Not, expr_goto_guard) in 
		let cmd_goto_empty_test = SLGuardedGoto (expr_goto_guard, next1, next2) in
		
		(* next2:    x_ret_3 := PHI(x_ret_1, x_ret_2) *) 
		let cmd_ass_ret_3 = SLBasic (SPhiAssignment (x_ret_3, [| Some x_ret_1; Some x_ret_2 |])) in
		
		let cmds_end_loop, x_ret_5 = make_loop_end x_ret_1 x_ret_1 cur_breaks end_loop true in
		
		let cmds4 = add_initial_label cmds4 body in 
		
		let cmds = 
				    cmds1 @ [                                      (*              cmds1                                        *)
					(None, None,             cmd_ass_ret_0);         (*              x_ret_0 := $$empty                           *)
					(None, Some head,        cmd_ass_ret_1);         (* head:        x_ret_1 := PHI(x_ret_0, x_ret_3)             *) 
				] @ cmds2 @ [                                      (*              cmds2                                        *)
					(None, None,             cmd_gv_x2);             (*              x2_v := i__getValue (x2) with err            *)
					(None, None,             cmd_tb_x2);             (*              x2_b := i__toBoolean (x2_v) with err         *) 
					(None, None,             cmd_for_goto);          (*              goto [x2_b] body end                         *) 
				] @ cmds4 @ [                                      (* body:        cmds4                                        *)	   
					(None, None,             cmd_gv_x4);             (*              x4_v := i__getValue (x4) with err            *)
					(None, Some cont,        cmd_ass_ret_2);         (* cont:        x_ret_2 := PHI(cont_vars, x4_v)              *)
					(None, None,             cmd_goto_empty_test);   (*              goto [ not (x_ret_2 = $$empty) ] next1 next2 *)
					(None, Some next1,       SLBasic SSkip);         (* next1:       skip                                         *)
					(None, Some next2,       cmd_ass_ret_3);         (* next2:       x_ret_3 := PHI(x_ret_1, x_ret_2)             *)  
				] @ cmds3 @ [                                      (*              cmds3                                        *)
				  (None, None,             SLGoto head);           (*              goto head                                    *)
				] @ cmds_end_loop in 
		let errs = errs1 @ errs2 @ [ x2_v; x2_b ] @ errs4 @ [ x4_v ] @ errs3 in  
		cmds, Var x_ret_5, errs, rets4, outer_breaks, outer_conts 
		
	
	| Parser_syntax.Return e -> 
		(** 
      Section 12.9
			
			C(return) = 
      	x_r := $$undefined;
      	goto ret_lab
			
			C(e) = cmds, x 
			---------------------------
			C(return e) = 
				cmds 
				x_r := i__getValue(x) with err
      	goto ret_lab
		*) 
		(match e with 
		| None -> 
			let x_r = fresh_var () in 
			(* x_r := $$undefined *) 
			let cmd_xr_ass = (None, None, SLBasic (SAssignment (x_r, Literal Undefined))) in 
			(* goto lab_ret *) 
			let cmd_goto_ret = (None, None, SLGoto ctx.tr_ret_lab) in 
			[ cmd_xr_ass; cmd_goto_ret], Var x_r, [], [ x_r ], [], [] 
			
		| Some e ->
			let cmds, x, errs, _, _, _ = f e in
			(* x_r := i__getValue(x) with err *) 
			let x_r, cmd_gv_x = make_get_value_call x err in 
			(* goto ret_lab *) 
			let cmd_goto_ret = (None, None, SLGoto ctx.tr_ret_lab) in 
			cmds @ [ b_annot_cmd cmd_gv_x; cmd_goto_ret], Var x_r, errs @ [ x_r ], [ x_r ], [], [])		     
	
	
	| Parser_syntax.Continue lab -> 
		(** 
      Section 12.7
			
			find_continue_lab (lab) = jsil_lab
			---------------------------
			C(continue lab) = 
      	x_r := $$empty;
      	goto jsil_lab
			
			next_continue_lab () = jsil_lab
			---------------------------
			C(continue) = 
      	x_r := $$empty;
      	goto jsil_lab 
		*) 
		
		let x_r, cmd_ret = 
			(match previous with 
			| None -> 
				let x_r, cmd = make_empty_ass () in 
				x_r, [ (None, None, cmd) ] 
			| Some (Literal lit) -> 
				let x_r = fresh_var () in 
				let cmd = SLBasic (SAssignment (x_r, Literal lit)) in 
				x_r, [ (None, None, cmd) ]
			| Some (Var x) -> x, []
			| Some _ -> raise (Failure ("Continue: The return of the compilation must be either a variable or a literal"))) in  
				
		(* goto lab_c *) 
		let lab_c = get_continue_lab loop_list lab in
		let cmd_goto = [ (None, None, SLGoto lab_c) ] in
		 
		(cmd_ret @ cmd_goto), Var x_r, [], [], [], [ (lab, x_r) ]
	

	| Parser_syntax.Break lab ->
		(** 
      Section 12.8
      x_r := $$empty;
      goto lab_r 
		*) 
		
		let x_r, cmd_ret = 
			(match previous with 
			| None -> 
				let x_r, cmd = make_empty_ass () in 
				x_r, [ (None, None, cmd) ] 
			| Some (Literal lit) -> 
				let x_r = fresh_var () in 
				let cmd = SLBasic (SAssignment (x_r, Literal lit)) in 
				x_r, [ (None, None, cmd) ]
			| Some (Var x) -> x, []
			| Some _ -> raise (Failure ("Continue: The return of the compilation must be either a variable or a literal"))) in  
		
		(* goto lab_r *) 
		let lab_r = get_break_lab loop_list lab in
		let cmd_goto = [ (None, None, SLGoto lab_r) ] in 
		(cmd_ret @ cmd_goto), Var x_r, [], [], [ (lab, x_r) ], [] 
		
			
	| Parser_syntax.Label (js_lab, e) -> 
		(** Section 12.12 *) 
		translate fid cc_table ctx vis_fid err loop_list previous (Some js_lab) e 


	| Parser_syntax.Throw e -> 
		(** 
     Section 12.13 - The throw statement
		
		 C(e) = cmds, x 
		 ----------------------------
		 C(throw e) =  
			     cmds 
		       x_v := i__getValue (x) with err 
					 goto err 
		*) 
		let cmds, x, errs, _, _, _ = f e in
		let x_v, cmd_gv_x = make_get_value_call x err in 
		
		let cmds = cmds @ [          (*  cmds                            *)
		   (None, None, cmd_gv_x);   (*  x_v := i__getValue (x) with err *)
			 (None, None, SLGoto err)  (*  goto err                        *)
		] in 
		
		cmds, Literal Empty, errs @ [ x_v; x_v ], [], [], []
	
	
	| Parser_syntax.Try (e1, Some (x, e2), Some e3) ->
		(**
     Section 12.14 - The try Statement 
		 C(e1) = cmds1, x1; C(e2) = cmds2, x2; C(e3) = cmds3, x3
		 -----------------------------------------------------------
		  C(try { e1 } catch^{cid}(x) { e2 } finally { e3 } = 
									cmds1
		            	goto finally  
		    err:    	x_err := PHI(errs1)
				        	x_er := new () 
									[x_er, "x"] := x_err 
									[x_scope, "cid"] := x_er 
									cmds2
				finally:  x_ret_1 := PHI(breaks1, x_1, breaks2, x_2)
				          cmds3
		 	  end:      x_ret_2 := PHI(breaks3, x_ret_1)   
		 *)
		
		let catch_id = try Js_pre_processing.get_codename e 
				with _ -> raise (Failure "catch statemetns must be annotated with their respective code names - try - catch - finally") in 
		
		let cmds12, x_ret_1, errs12, rets12, breaks12, conts12, end_lab = make_try_catch_cmds e1 (x, e2) catch_id in 
		let new_loop_list = (None, end_lab, js_lab) :: loop_list in 
		let cmds3, _, errs3, rets3, breaks3, conts3 = translate fid cc_table ctx vis_fid err new_loop_list None None e3 in 
		let cur_breaks, outer_breaks = filter_cur_jumps breaks3 js_lab false in 
		
		(* x_ret_2 := PHI(breaks3, x_ret_1)  *) 
		let x_ret_2 = fresh_var () in 
		let phi_args = cur_breaks @ [ x_ret_1 ] in 
		let phi_args = List.map (fun x -> Some x) phi_args in 
		let phi_args = Array.of_list phi_args in 
		let final_cmd = (None, Some end_lab, SLBasic (SPhiAssignment (x_ret_2, phi_args))) in 
		
		cmds12 @ cmds3 @ [ final_cmd ], Var x_ret_2, errs12 @ errs3, rets12 @ rets3, breaks12 @ outer_breaks, conts12 @ conts3
		
	
	| Parser_syntax.Try (e1, None, Some e3) ->
		(**
     Section 12.14 - The try Statement 
		 C(e1) = cmds1, x1; C(e3) = cmds3, x3
		 -----------------------------------------------------------
		  C(try { e1 } finally { e3 } = 
									cmds1
				finally:  x_ret_1 := PHI(cur_breaks1, x_1)
					        cmds3
			  end:      x_ret_2 := PHI(cur_breaks3, x_ret_1)				
		 *)
		
		let new_err, finally, end_lab = fresh_tcf_vars () in 
		let loop_list1 = (None, finally, js_lab) :: loop_list in 
		let loop_list3 = (None, end_lab, js_lab) :: loop_list in 
		let cmds1, x1, errs1, rets1, breaks1, conts1 = translate fid cc_table ctx vis_fid finally loop_list1 None None e3 in
		let cur_breaks1, outer_breaks1 = filter_cur_jumps breaks1 js_lab false in 
		let cmds1, x1_v = add_final_var cmds1 x1 in 
		
		(* finally:  x_ret_1 := PHI(cur_breaks1, x_1)  *) 
		let x_ret_1 = fresh_var () in 
		let phi_args = cur_breaks1 @ [ x1_v ] in 
		let phi_args = List.map (fun x -> Some x) phi_args in 
		let phi_args = Array.of_list phi_args in 
		let cmd_phi1 = (None, Some finally, SLBasic (SPhiAssignment (x_ret_1, phi_args))) in 
		
		(* end:      x_ret_2 := PHI(cur_breaks3, x_ret_1)	 *) 
		let cmds3, _, errs3, rets3, breaks3, conts3 = translate fid cc_table ctx vis_fid err loop_list3 None None e3 in 
		let cur_breaks3, outer_breaks3 = filter_cur_jumps breaks3 js_lab false in 
		let x_ret_2 = fresh_var () in 
		let phi_args = cur_breaks3 @ [ x_ret_1 ] in 
		let phi_args = List.map (fun x -> Some x) phi_args in 
		let phi_args = Array.of_list phi_args in 
		let cmd_phi2  = (None, Some end_lab, SLBasic (SPhiAssignment (x_ret_2, phi_args))) in 
		
		cmds1 @ [ cmd_phi1 ] @ cmds3 @ [ cmd_phi2 ], Var x_ret_2, errs1 @ errs3, rets1 @ rets3, outer_breaks1 @ outer_breaks3, conts1 @ conts3
		

	| Parser_syntax.Try (e1, Some (x, e2), None) ->
		(**
     Section 12.14 - The try Statement 
		 C(e1) = cmds1, x1; C(e2) = cmds2, x2; 
		 -----------------------------------------------------------		
		 	C(try { e1 } catch^{cid}(x) { e2 } = 
									cmds1
		            	goto finally  
		    err:    	x_err := PHI(errs1)
				        	x_er := new () 
									[x_er, "x"] := x_err 
									[x_scope, "cid"] := x_er 
									cmds2
			  finally:  x_ret_1 := PHI(breaks1, x_1, breaks2, x_2)
		 *)
		let catch_id = try Js_pre_processing.get_codename e 
				with _ -> raise (Failure "catch statemetns must be annotated with their respective code names - try - catch - finally") in 
		let cmds12, x_ret_1, errs12, rets12, breaks12, conts12, _ = make_try_catch_cmds e1 (x, e2) catch_id in 
		cmds12, Var x_ret_1, errs12, rets12, breaks12, conts12
	
	
	| Parser_syntax.AnonymousFun (_, params, e_body) -> 
		(**
       Section 13
       x_sc := copy_scope_chain_obj (x_scope, {{main, fid1, ..., fidn }}); 
		   x_f := create_function_object(x_sc, f_id, params)
   	*)
		let f_id = try Js_pre_processing.get_codename e 
			with _ -> raise (Failure "annonymous function literals should be annotated with their respective code names") in 
		let cmds, x_f = translate_function_literal f_id params in 
		cmds, Var x_f, [], [], [], []
	
	
	| Parser_syntax.Switch (e, xs) ->
		(**
      Section 
			
			a_case = e_c, e_s
			C(e_c) = cmds1, x1
			C(e_s) = cmds2, x2 
			--------------------------------------------------------
			C_case ( a_case, x_prev_found, x_switch_guard ) = 
				           x_found_1 := false
				           goto [ not x_prev_found_a ] then1 next1 
				then1:     cmds1
				           x1_v := getValue (x1) with err
								   goto [ x1_v = x_switch_guard ] next1 end_case
				next1:     x_found_2 := true
				           cmds2
				end_case:  x_found_3 := PHI(x_found_a_1, x_found_a_2) 
									   
			
			
			C_case ( a_case ) = cmds1, x_prev_1
			C_a_cases ( a_cases ) = cmds2, x_prev_2  
			--------------------------------------------------------
			C_cases ( a_case :: a_cases, x_prev, x_switch_guard ) = 
				           cmds1 
									 cmds2 
			
									
			C(s) = cmds_def, x_def
			C(b_stmt_i) = cmds_i, x_i, for all b_stmt_i \in b_stmts
			---------------------------------------------------------
			C_default ( s, b_stmts, x_found_b, breaks) = 
					            cmds_def
									    goto [ not (x_found_b) ] next end_switch
				  next:       cmds_1
					            ... 
									    cmds_n
				  end_switch: x_r := PHI(breaks, x_def, x_found_b) 

										
				 
			C(e) = cmds_guard, x_guard
			C_cases (a_cases, x_found, x_guard_v) = cmds_a, x_found_a, x_a 
			C_cases (b_cases, x_found_a, x_guard_v) = cmds_b, x_found_b, x_b 
			C_defautl (default_case, b_stmts(b_cases), x_found_b) = cmds_default
			------------------------------------------------------
		  C(switch(e) { a_cases, default_case, b_cases} =
				            cmds_guard 
										x_guard_v := i__getValue (x_guard) with err  
				            x_found := false 
										cmds_a 
										cmds_b 
										cmds_default 	
		 
     *)
		[], Literal Empty, [], [], [], [] 
	
	
	
	| Parser_syntax.NamedFun (_, n, params, e_body) -> 
		(** Section 13
			x_sc := copy_scope_chain_obj (x_scope, {{main, fid1, ..., fidn }})
		  x_f := create_function_object(x_sc, f_id, params)
			x_er := [x_scope, "fid"]
			x_ref_n := ref-v(x_er, "f_name")
		  x_pv := i__putValue(x_ref_n, x_f) with err
		*)
		let f_id = try Js_pre_processing.get_codename e 
			with _ -> raise (Failure "named function literals should be annotated with their respective code names") in
		let cmds, x_f = translate_function_literal f_id params in 
		
		(* x_er_fid := [x_scope, "fid"] *)
		let x_er = fresh_er_var () in 
		let cmd_ass_xer = (None, None, SLBasic (SLookup (x_er, Var var_scope, Literal (String fid)))) in 
		
		(* x_ref_n := ref-v(x_er, "f_name") *)
		let x_ref_n = fresh_var () in 
		let cmd_ass_xrefn = (None, None, SLBasic (SAssignment (x_ref_n, VRef (Var x_er, Literal (String n))))) in 
		
		(* x_pv := i__putValue(x_ref_n, x_f) with err *) 
		let x_pv = fresh_var () in 
		let cmd_pv_f = (None, None, SLCall (x_pv, Literal (String putValueName), [ Var x_ref_n; Var x_f ], Some err)) in 
		
		let cmds = cmds @ [ cmd_ass_xer; cmd_ass_xrefn; cmd_pv_f ] in 
		cmds, Var x_f, [ x_pv ], [], [], []
	
	
	| _ -> raise (Failure "not implemented yet")


let make_final_cmd vars final_lab final_var =
	let cmd_final = 
		(match vars with 
		| [] -> SLBasic SSkip 
		| [ x ] -> SLBasic (SAssignment (final_var, Var x))
		| _ -> 
			let vars = List.map (fun x_r -> Some x_r) vars in 
			let vars = Array.of_list vars in 
			SLBasic (SPhiAssignment (final_var, vars))) in 
	(None, Some final_lab, cmd_final)  


let generate_main e main cc_table =
	let cc_tbl_main = 
		try Hashtbl.find cc_table main 
			with _ -> raise (Failure "main not defined in cc_table - assim fica dificil")  in 
	let global_vars = 
		Hashtbl.fold (fun key key_val ac -> key :: ac) cc_tbl_main [] in
	let new_var = fresh_var () in
	let setup_heap_ass = (None, None, SLCall (new_var, Literal (String setupHeapName), [ ], None)) in
	(* __scope := new () *) 
	let init_scope_chain_ass = (None, None, SLBasic (SNew (var_scope))) in
	(* [__scope, "main"] := $lg *)
	let lg_ass = (None, None, SLBasic (SMutation(Var var_scope,  Literal (String main), Literal (Loc "$lg")))) in
	(* __this := $lg *)
	let this_ass = (None, None, SLBasic (SAssignment (var_this, Literal (Loc "$lg")))) in
	(* global vars init asses: [$lg, y] := undefined *)
	let global_var_asses = 
		List.fold_left 
			(fun ac global_v -> 
				let new_global_ass = (None, None, SLBasic (SMutation(Literal (Loc "$lg"),  Literal (String global_v), Literal Undefined))) in 
				new_global_ass :: ac)
			[]
			global_vars in 
			
	(* x__te := TypeError () *)
	let cmd_ass_te = make_var_ass_te () in 
	let cmd_ass_te = b_annot_cmd cmd_ass_te in 
			
	(* x__te := SyntaxError () *)
	let cmd_ass_se = make_var_ass_se () in 
	let cmd_ass_se = b_annot_cmd cmd_ass_se in
					
	let ctx = make_translation_ctx main in 
	let cmds_e, x_e, errs, _, _, _ = translate main cc_table ctx [ main ] ctx.tr_error_lab [] None None e in 
	(* x_ret := x_e *)
	let ret_ass = (None, None, SLBasic (SAssignment (ctx.tr_ret_var, x_e))) in
	(* lab_ret: skip *) 
	let lab_ret_skip = (None, (Some ctx.tr_ret_lab), (SLBasic SSkip)) in
	
	let cmd_err_phi_node = make_final_cmd errs ctx.tr_error_lab ctx.tr_error_var in 
	
	let main_cmds = 
		[ setup_heap_ass; init_scope_chain_ass; lg_ass; this_ass] @ global_var_asses @ [ cmd_ass_te; cmd_ass_se ] @ cmds_e @ [ret_ass; lab_ret_skip; cmd_err_phi_node ] in 
	{ 
		lproc_name = main;
    lproc_body = (Array.of_list main_cmds);
    lproc_params = []; 
		lret_label = Some ctx.tr_ret_lab; 
		lret_var = Some ctx.tr_ret_var;
		lerror_label = Some ctx.tr_error_lab; 
		lerror_var = Some ctx.tr_error_var;
		lspec = None 
	}
	
let generate_proc e fid params cc_table vis_fid =
	let fid_decls = Js_pre_processing.func_decls_in_exp e in
  let fid_fnames = List.map (fun f ->
    match f.Parser_syntax.exp_stx with
      | Parser_syntax.NamedFun (s, name, args, body) -> name
      | _ -> raise (Failure ("Must be function declaration " ^ (Pretty_print.string_of_exp true f)))
  ) fid_decls in
	let fid_vars = List.concat [ (Js_pre_processing.var_decls e); fid_fnames ] in 
	
	(* x_er := new () *)
	let x_er = fresh_var () in  
	let cmd_er_creation = (None, None, SLBasic (SNew x_er)) in 
	
	(* [x_er, "arg_i"] := x_{i+2} *) 
	let cmds_params = 
		List.map (fun param -> 
			let cmd = SLBasic (SMutation (Var x_er, Literal (String param), Var param)) in  
			(None, None, cmd))
		params in 
	
	(* [x_er, decl_var_i] := undefined *) 
	let cmds_decls = 
		List.map (fun decl_var -> 
			let cmd = SLBasic (SMutation (Var x_er, Literal (String decl_var), Literal Undefined)) in
			(None, None, cmd))
		fid_vars in 
	
	(* [__scope, "fid"] := x_er *) 
	let cmd_ass_er_to_sc = (None, None, SLBasic (SMutation (Var var_scope, Literal (String fid), Var x_er))) in 
	
	(* x__te := TypeError () *)
	let cmd_ass_te = make_var_ass_te () in 
	let cmd_ass_te = b_annot_cmd cmd_ass_te in 
	(* x__te := SyntaxError () *)
	let cmd_ass_se = make_var_ass_se () in 
	let cmd_ass_se = b_annot_cmd cmd_ass_se in
	
	let ctx = make_translation_ctx fid in 
	let cmds_e, x_e, errs, rets, _, _ = translate fid cc_table ctx vis_fid ctx.tr_error_lab [] None None e in 
	
	(* x_dr := $$empty *)
	let x_dr = fresh_var () in
	let cmd_dr_ass = (None, None, SLBasic (SAssignment (x_dr, Literal Empty))) in
	let cmd_dr_goto = (None, None, SLGoto ctx.tr_ret_lab) in 
	let rets = rets @ [ x_dr ] in 
	
	(* lab_ret: x_return := PHI(...) *)
	let cmd_return_phi = make_final_cmd rets ctx.tr_ret_lab ctx.tr_ret_var in
	 
	(* lab_err: x_error := PHI(...) *) 
	let cmd_error_phi = make_final_cmd errs ctx.tr_error_lab ctx.tr_error_var in 	
	
	let fid_cmds = 
		[ cmd_er_creation ] @ cmds_params @ cmds_decls @ [ cmd_ass_er_to_sc ] @ [ cmd_ass_te; cmd_ass_se ] @ cmds_e 
		@ [ cmd_dr_ass; cmd_dr_goto; cmd_return_phi; cmd_error_phi] in 
	{ 
		lproc_name = fid;
    lproc_body = (Array.of_list fid_cmds);
    lproc_params = var_scope :: var_this :: params; 
		lret_label = Some ctx.tr_ret_lab; 
		lret_var = Some ctx.tr_ret_var;
		lerror_label = Some ctx.tr_error_lab; 
		lerror_var = Some ctx.tr_error_var;
		lspec = None 
	}

let js2jsil e = 
	let main = "main" in 
	let e = Js_pre_processing.add_codenames main e in 
	let cc_tbl, fun_tbl, vis_tbl = Js_pre_processing.closure_clarification_top_level main e in 
	
	let jsil_prog = SLProgram.create 1021 in 
	Hashtbl.iter
		(fun f_id (_, f_params, f_body) -> 
			let proc = 
				(if (f_id = main) 
					then generate_main e main cc_tbl
					else 
						(let vis_fid = try Hashtbl.find vis_tbl f_id 
							with _ -> 
								(let msg = Printf.sprintf "Function %s not found in visibility table" f_id in 
								raise (Failure msg)) in 	
						generate_proc f_body f_id f_params cc_tbl vis_fid)) in 
			SLProgram.add jsil_prog f_id proc)
		fun_tbl; 
	
	(* Prints to delete *) 
	(* let str = Js_pre_processing.print_cc_tbl cc_tbl in 
	   Printf.printf "closure clarification table: %s\n" str; *)
	(* let main_str = SSyntax_Print.string_of_lprocedure jsil_proc_main in 
	Printf.printf "main code:\n %s\n" main_str; *)
	
	Some js2jsil_imports, jsil_prog	