open Utils
open Lexing

open CCommon
open JSIL_Syntax
open JS2JSIL_Constants
open JSLogic
open JS_Utils

let cc_tbl      : cc_tbl_type      = Hashtbl.create medium_tbl_size
let fun_tbl     : fun_tbl_type     = Hashtbl.create medium_tbl_size
let old_fun_tbl : pre_fun_tbl_type = Hashtbl.create medium_tbl_size
let vis_tbl     : vis_tbl_type     = Hashtbl.create medium_tbl_size

let if_verification a b = 
	let cond = !for_verification in
	 	if cond then a else b
		
let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let power_list list n =
	let rec loop cur_list cur_n =
		(if (cur_n = 1)
		then cur_list
		else
			(if (cur_n > 1)
			then loop (cur_list @ list) (cur_n - 1)
			else raise (Failure "power list only for n > 1"))) in
	loop list n

let number_of_switches = ref 0
let fresh_switch_labels () =
	let b_cases_lab = fresh_b_cases_label () in
	let default_lab = fresh_default_label () in
	let end_switch = fresh_end_switch_label () in
	let fresh_end_case_label = fresh_sth ("end_case_" ^ (string_of_int !number_of_switches) ^ "_") in
	number_of_switches := (!number_of_switches) + 1;
	b_cases_lab, default_lab, end_switch, fresh_end_case_label


let add_initial_label cmds lab metadata =
	(match cmds with
	| [] -> [ (metadata, Some lab, LBasic Skip) ]
	| (_, Some lab_s, _) :: rest -> (metadata, Some lab, LBasic Skip) :: cmds
	| (cmd_metadata, None, cmd) :: rest -> (cmd_metadata, Some lab, cmd) :: rest)


let add_more_metadata def_metadata lcmds invariant cmds =
	match cmds with
	| [] ->
		if ((List.length lcmds) = 0)
			then []
			else
				(let new_metadata = { def_metadata with pre_logic_cmds = lcmds; invariant = invariant } in
				[ (new_metadata, None, LBasic Skip)])
	| (metadata, lab, cmd) :: rest ->
		let pre_l_cmds = metadata.pre_logic_cmds in
		let new_metadata = { metadata with pre_logic_cmds = pre_l_cmds @ lcmds; invariant = invariant } in
		(new_metadata, lab, cmd) :: rest


let is_vref x = BinOp (BinOp ((TypeOf x), Equal, lit_typ ListType), And, BinOp (rtype x, Equal, lit_refv))
let is_oref x = BinOp (BinOp ((TypeOf x), Equal, lit_typ ListType), And, BinOp (rtype x, Equal, lit_refo))
let is_ref  x = BinOp (is_vref x, Or, is_oref x)

let rec get_break_lab loop_list lab =
	match loop_list with
	| [] ->
		let msg =
			(match lab with
			| None -> "breaking outside a loop"
			| Some lab -> Printf.sprintf "either breaking outside a loop or lab %s not found" lab) in
		raise (Failure msg)
	| (lab_c, lab_b, js_lab, valid_unlabelled) :: rest ->
		match lab with
		| None ->
			(match valid_unlabelled with
			| true -> lab_b
			| false ->  get_break_lab rest lab)
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
	| (lab_c, lab_b, js_lab, valid_unlabelled) :: rest ->
		match lab with
		| None ->
			(match lab_c with
			| Some lab_c ->
				(match valid_unlabelled with
				| true -> lab_c
				| false -> get_continue_lab rest lab)
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

let filter_cur_jumps (jumps : (string option * string * string) list) loop_lab include_no_lab =
	let rec filter_cur_jumps_iter jumps inner_jumps outer_jumps =
		match jumps with
		| [] -> (List.rev inner_jumps), (List.rev outer_jumps)
		| (None, x, jump_lab) :: rest_jumps ->
			  (match include_no_lab with
				| true -> filter_cur_jumps_iter rest_jumps (x :: inner_jumps) outer_jumps
				| false -> filter_cur_jumps_iter rest_jumps inner_jumps ((None, x, jump_lab) :: outer_jumps))
		| (Some lab, x, jump_lab) :: rest_jumps ->
				(match loop_lab with
				| None ->  filter_cur_jumps_iter rest_jumps inner_jumps ((Some lab, x, jump_lab) :: outer_jumps)
				| Some loop_lab ->
						if (loop_lab = lab)
							then filter_cur_jumps_iter rest_jumps (x :: inner_jumps) outer_jumps
							else filter_cur_jumps_iter rest_jumps inner_jumps ((Some lab, x, jump_lab) :: outer_jumps)) in
	filter_cur_jumps_iter jumps [] []

let add_none_labs cmds = List.map (fun cmd -> (None, cmd)) cmds

let add_skip_if_empty cmds x metadata =
	(match x with
	| Var _ -> cmds, x
	| Literal lit ->
		let x_r = fresh_var () in
		let cmd_ass_xr = LBasic (Assignment (x_r, Literal lit)) in
		cmds @ [ (metadata, None, cmd_ass_xr) ], Var x_r
	| _ -> raise (Failure "The compiler must always generate a variable or a literal"))

let make_var_ass_se () = LCall (var_se, lit_str syntaxErrorName, [ ], None)

let make_var_ass_te () = LCall (var_te, lit_str typeErrorName, [ ], None)

let add_final_var cmds x metadata =
	match x with
	| Var x_name -> cmds, x_name
	| Literal lit ->
		let x_new = fresh_var () in
		let cmd_ass_new = (metadata, None, LBasic (Assignment (x_new, Literal lit))) in
	 	cmds @ [ cmd_ass_new ], x_new
	| _ -> raise (Failure "add_final_var: x needs to be a variable or a literal")

(**
Auxiliary Compilers
*)
let non_writable_ref_test x =
	(* (typeof (x) = $$v-reference_type) and ((field(x) = "eval") or (field(x) = "arguments"))  *)
	let left_e = is_vref x in
	let right_e = BinOp ((BinOp (field x, Equal, lit_str "eval")), Or, (BinOp (field x, Equal, Literal (String "arguments")))) in
	BinOp (left_e, And, right_e)

let make_unresolvable_ref_test x =
	BinOp (BinOp (base x, Equal, (Literal Null)), Or, BinOp (base x, Equal, (Literal Undefined)))

let make_get_value_call x err =
	(* x_v := getValue (x) with err *)
	match is_get_value_var x with
	| None ->
		let x_v = val_var_of_var x in
		(x_v, LCall (x_v, (Literal (String getValueName)), [ x ], Some err), [x_v])
	| Some x_v -> (x_v, LBasic Skip, [])

let make_to_number_call x x_v err =
	let x_n = number_var_of_var x in
	(x_n, LCall (x_n, (Literal (String toNumberName)), [ Var x_v ], Some err))

let make_to_boolean_call x x_v err =
	let x_b = boolean_var_of_var x in
	(x_b, LCall (x_b, (Literal (String toBooleanName)), [ Var x_v ], Some err))

let make_to_primitive_call x x_v err =
	let x_p = primitive_var_of_var x in
	(x_p, LCall (x_p, (Literal (String toPrimitiveName)), [ Var x_v ], Some err))

let make_to_string_call x x_v err =
	let x_s = string_var_of_var x in
	(x_s, LCall (x_s, (Literal (String toStringName)), [ Var x_v ], Some err))

let make_to_i32_call x x_v err =
	let x_i32 = i32_var_of_var x in
	(x_i32,  LCall (x_i32, (Literal (String toInt32Name)), [ Var x_v ], Some err))

let make_put_value_call x x_r err =
	let x_pv = fresh_var () in
	(x_pv, LCall (x_pv, Literal (String putValueName), [x; Var x_r], Some err))

let make_dop_call x_obj prop x_desc b err =
	let x_dop = fresh_var () in
	(x_dop, LCall (x_dop, Literal (String defineOwnPropertyName), [Var x_obj; prop; Var x_desc; Literal (Bool b)], Some err))

let make_cae_call x err =
	let x_cae = fresh_var () in
	x_cae,  LCall (x_cae, Literal (String checkAssignmentErrorsName), [ x ], Some err)

let make_empty_ass () =
	let x = fresh_var () in
	let empty_ass = LBasic (Assignment (x, (Literal Empty))) in
	x, empty_ass


let make_create_function_object_call x_sc fun_id params =
	let x_f = fresh_fun_var () in
	let processed_params = List.map (fun p -> Literal.String p) params in
	let cmd = LCall (x_f, Literal (String createFunctionObjectName),
		[ (Var x_sc); (Literal (String fun_id)); (Literal (String fun_id)); (Literal (LList processed_params)) ], None) in
	x_f, cmd



let translate_named_function_literal (top_level : bool) x_sc f_name f_id params index =
	  (* x_f := create_function_object(x_sc, f_id, f_id, params) *)
		let x_f, cmd_cfoc = make_create_function_object_call x_sc f_id params in
		let cmd_cfoc = None, cmd_cfoc in

		(* x_er := l-nth(x_sc, index) *)
		let x_er = fresh_er_var () in
		let cmd_ass_xer = (None, (LBasic (Assignment (x_er, LstNth(Var x_sc, Literal (Num (float_of_int index))))))) in

		(* [x_er, f_name] := x_f *)
		(* [x_er, f_name] := {{ "d", x_f, true, true, false }} *)
		let cmd_f = if top_level
			then (None, LBasic (Mutation (Var x_er, lit_str f_name, EList [ Literal (String "d"); Var x_f; Literal (Bool true); Literal (Bool true); Literal (Bool false) ], None)))
			else (None, LBasic (Mutation (Var x_er, lit_str f_name, Var x_f, None))) in

		let cmds = [ cmd_cfoc; cmd_ass_xer; cmd_f ] in
		cmds, Var x_f, []


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
	let cmd_goto_legalass = LGuardedGoto ((non_writable_ref_test x), err, next) in

	(* next:  x_v := getValue (x) with err *)
	let x_v, cmd_gv_x, errs_x_v = make_get_value_call x err in

	(* x_n := i__toNumber (x_v) with err *)
	let x_n, cmd_tn_x = make_to_number_call x x_v err in

	(* x_r := x_n +/- 1 *)
	let x_r = fresh_var () in
	let cmd_ass_xr =
		let (op : BinOp.t) = if is_plus then Plus else Minus in
		LBasic (Assignment (x_r, (BinOp (Var x_n, op,  Literal (Num 1.))))) in

	(* x_pv = putValue (x, x_r) with err4 *)
	let x_pv, cmd_pv_x = make_put_value_call x x_r err in

	let new_cmds = [
		(None,      cmd_goto_legalass);                (*        goto [ (typeof (x) = $$v-reference_type) and ((field(x) = "eval") or (field(x) = "arguments")) ] err next   *)
		(Some next, cmd_gv_x);                         (* next:  x_v := i__getValue (x) with err                                                                             *)
		(None,      cmd_tn_x);                  	     (*        x_n := i__toNumber (x_v) with err                                                                           *)
		(None,      cmd_ass_xr);                       (*        x_r := x_n + 1                                                                                              *)
		(None,      cmd_pv_x)                          (*        x_pv = i__putValue (x, x_r) with err                                                                        *)
	] in
	let new_errs = [ var_se; x_v; x_n; x_pv ] in
	new_cmds, new_errs, x_n, x_r


let translate_multiplicative_binop x1 x2 x1_v x2_v aop err =
	let jsil_aop : BinOp.t =
		(match aop with
		| Parser_syntax.Times -> Times
		| Parser_syntax.Div   -> Div
		| Parser_syntax.Mod   -> Mod
		| Parser_syntax.Minus -> Minus
		| _ -> raise (Failure "Illegal binary operator - Impossible case")) in

	(* x1_n := i__toNumber (x1_v) with err *)
	let x1_n, cmd_tn_x1 = make_to_number_call x1 x1_v err in
	(* x2_n := i__toNumber (x2_v) with err *)
	let x2_n, cmd_tn_x2 = make_to_number_call x2 x2_v err in
	(* x_r := x1_n * x2_n *)
	let x_r = fresh_var () in
	let cmd_ass_xr = LBasic (Assignment (x_r, BinOp (Var x1_n, jsil_aop, Var x2_n))) in

	let new_cmds = [
		(None, cmd_tn_x1);       (*  x1_n := i__toNumber (x1_v) with err  *)
		(None, cmd_tn_x2);       (*  x2_n := i__toNumber (x2_v) with err  *)
		(None, cmd_ass_xr)       (*  x_r := x1_n * x2_n                   *)
	] in
	let new_errs = [ x1_n; x2_n ] in
	new_cmds, new_errs, x_r


let translate_binop_plus x1 x2 x1_v x2_v err =
	(* x1_p := i__toPrimitive (x1_v) with err *)
	let x1_p, cmd_tp_x1 = make_to_primitive_call x1 x1_v err in

	(* x2_p := i__toPrimitive (x2_v) with err *)
	let x2_p, cmd_tp_x2 = make_to_primitive_call x2 x2_v err in

	(*  goto [((typeOf x1_p) = Str) or ((typeOf x2_p) = Str)] then else *)
	let then_lab = fresh_then_label () in
	let else_lab = fresh_else_label () in
	let end_lab = fresh_endif_label () in
	let goto_guard_left = BinOp ((TypeOf (Var x1_p)), Equal, (Literal (Type StringType))) in
	let goto_guard_right = BinOp ((TypeOf (Var x2_p)), Equal, (Literal (Type StringType))) in
	let goto_guard = BinOp (goto_guard_left, Or, goto_guard_right) in
	let cmd_goto = LGuardedGoto (goto_guard, then_lab, else_lab) in

	(* then: x1_s := i__toString (x1_p) with err *)
	let x1_s, cmd_ts_x1 = make_to_string_call x1 x1_p err in

	(* x2_s := i__toString (x2_p) with err *)
	let x2_s, cmd_ts_x2 = make_to_string_call x2 x2_p err in

	(* x_rthen := x1_s ++ x2_s  *)
	let x_rthen = fresh_var () in
	let cmd_ass_xrthen = LBasic (Assignment (x_rthen, BinOp((Var x1_s), StrCat, (Var x2_s)))) in

	(* else: x1_n := i__toNumber (x1_p) with err *)
	let x1_n, cmd_tn_x1 = make_to_number_call x1 x1_p err in

	(* x2_n := i__toNumber (x2_p) with err *)
	let x2_n, cmd_tn_x2 = make_to_number_call x2 x2_p err in

	(* x_relse := x1_n + x2_n  *)
	let x_relse = fresh_var () in
	let cmd_ass_xrelse = LBasic (Assignment (x_relse, BinOp((Var x1_n), Plus, (Var x2_n)))) in

	(* end:  x_r := PHI (x_rthen, x_relse) *)
	let x_r = fresh_var () in
	let cmd_ass_xr = LPhiAssignment (x_r, [| (Var x_rthen); (Var x_relse) |]) in

	let new_cmds = [
		(None,          cmd_tp_x1);       (*       x1_p := i__toPrimitive (x1_v) with err                                                 *)
		(None,          cmd_tp_x2);       (*       x2_p := i__toPrimitive (x2_v) with err                                                 *)
		(None,          cmd_goto);        (*       goto [((typeOf x1_p) = Str) or ((typeOf x2_p) = Str)] then else    *)
		(Some then_lab, cmd_ts_x1);       (* then: x1_s := i__toString (x1_p) with err                                                    *)
		(None,          cmd_ts_x2);       (*       x2_s := i__toString (x2_p) with err                                                    *)
		(None,          cmd_ass_xrthen);  (*       x_rthen := x1_s :: x2_s                                                                *)
		(None,          LGoto end_lab);  (*       goto end                                                                               *)
		(Some else_lab, cmd_tn_x1);       (* else: x1_n := i__toNumber (x1_p) with err                                                    *)
		(None,          cmd_tn_x2);       (*       x2_n := i__toNumber (x2_p) with err                                                    *)
		(None,          cmd_ass_xrelse);  (* 	     x_relse := x1_n + x2_n                                                                 *)
		(Some end_lab,  cmd_ass_xr)       (* end:  x_r := PHI (x_rthen, x_relse)                                                          *)
	] in
	let errs = [ x1_p; x2_p; x1_s; x2_s; x1_n; x2_n ] in
	new_cmds, errs, x_r


let translate_binop_comparison x1 x2 x1_v x2_v is_first_first flag_arg bool_undef err =
	(* x_ac := i__abstractComparison (x1_v, x2_v, flag_arg) with err  *)
	let x_ac = fresh_var () in
	let args =
		(match is_first_first with
		| true -> [ Var x1_v; Var x2_v ]
		| false -> [ Var x2_v; Var x1_v ]) in
	let cmd_ac = LCall (x_ac, (Literal (String abstractComparisonName)), args @ [ Literal (Bool flag_arg) ], Some err) in

	(*  goto [ x_ac = undefined ] then end *)
	let then_lab = fresh_label () in
	let end_lab = fresh_label () in
	let cmd_goto = LGuardedGoto (BinOp (Var x_ac, Equal, Literal Undefined), then_lab, end_lab) in

	(* x_r := PHI(x_ac, x_undef) *)
	let x_undef = fresh_var () in
	let x_r = fresh_var () in
	let cmd_ass_xr = LPhiAssignment (x_r, [| (Var x_ac); (Var x_undef) |]) in

	let new_cmds = [
		(None, cmd_ac);  	                                                          (*        x_ac := i__abstractComparison (xi_v, xk_v, flag_arg) with err; where: i != k and i,k \in {1,2}  *)
		(None, cmd_goto);                                                             (*        goto [ x_ac = undefined ] then end                                                              *)
		(Some then_lab, LBasic (Assignment (x_undef, Literal (Bool bool_undef))));  (* then:  x_undef := bool_undef                                                                           *)
		(Some end_lab, cmd_ass_xr)                                                    (* end:   x_r := PHI(x_ac, x_undef)                                                                       *)
	] in
	let errs = [ x_ac ] in
	new_cmds, errs, x_r


let translate_bitwise_shift x1 x2 x1_v x2_v left_fun_name right_fun_name op err =
	(* x1_f := left_fun_name (x1_v) with err *)
	let x1_f = fresh_var () in
	let cmd_fc_x1 = LCall (x1_f, (Literal (String left_fun_name)), [ Var x1_v ], Some err) in

	(* x2_f := right_fun_name (x2_v) with err *)
	let x2_f = fresh_var () in
	let cmd_fc_x2 = LCall (x2_f, (Literal (String right_fun_name)), [ Var x2_v ], Some err) in

	(* x_r := x1_f op x2_f *)
	let x_r = fresh_var () in
	let cmd_ass_xr = LBasic (Assignment (x_r, (BinOp (Var x1_f, op, Var x2_f)))) in

	let new_cmds = [
		(None,  cmd_fc_x1);       (*  x1_f := left_fun_name (x1_v) with err     *)
		(None,  cmd_fc_x2);       (*  x2_f := right_fun_name (x2_v) with err    *)
		(None,  cmd_ass_xr)       (*  x_r := x1_f op x2_f                       *)
	] in
	let errs = [ x1_f; x2_f ] in
	new_cmds, errs, x_r


let translate_binop_equality x1 x2 x1_v x2_v non_strict non_negated err =
	(* x_r1 := i__strictEqualityComparison/i__abstractEqualityComparison (x1_v, x2_v) with err *)
	let x_r1 = fresh_var () in
	let f_name =
		(match non_strict with
		| true -> abstractEqualityComparisonName
		| false -> strictEqualityComparisonName) in
	let cmd_ass_xr1 = LCall (x_r1, (Literal (String f_name)), [ Var x1_v; Var x2_v ], Some err) in

	let cmd_ass_xr2, ret =
		(match non_negated with
		| true -> [], x_r1
		| false ->
			(let x_r2 = fresh_var () in
			(* x_r2 := (not x_r1) *)
			[ (None, LBasic (Assignment (x_r2, UnOp (Not, Var x_r1)))) ], x_r2)) in

	let new_cmds =	[
		(None, cmd_ass_xr1)
	] @ cmd_ass_xr2 in
	new_cmds, [ x_r1 ], ret


let translate_bitwise_bin_op x1 x2 x1_v x2_v bbop err =
	let bbop : BinOp.t =
		(match bbop with
		| Parser_syntax.Bitand -> BitwiseAnd
		| Parser_syntax.Bitor  -> BitwiseOr
		| Parser_syntax.Bitxor -> BitwiseXor
		| _ -> raise (Failure "Illegal bitwise operator")) in

	(* x1_i32 := i__toInt32 (x1_v) with err3 *)
	let x1_i32, cmd_ti32_x1 = make_to_i32_call x1 x1_v err in

	(* x2_i32 := i__toInt32 (x2_v) with err4 *)
	let x2_i32, cmd_ti32_x2 = make_to_i32_call x2 x2_v err in

	(*  x_r := (x1_i32 bbop x2_i32) *)
	let x_r = fresh_var () in
	let cmd_ass_xr = LBasic (Assignment (x_r, BinOp (Var x1_i32, bbop, Var x2_i32))) in

	let new_cmds =	[
		(None, cmd_ti32_x1);
		(None, cmd_ti32_x2);
		(None, cmd_ass_xr)
	] in
	let new_errs = [ x1_i32; x2_i32 ] in
	new_cmds, new_errs, x_r


let make_check_empty_test x_prev x_new =
(**        goto [x_new = empty] next1 next2
			next1: skip
			next2: x := PHI(x_new, x_previous)
*)
	let x_prev, cmd_ass_xprev =
		(match x_prev with
		| Var x_prev -> x_prev, []
		| Literal lit ->
			let x_prev_var = fresh_var () in
			let cmd_ass_prev = (None, LBasic (Assignment (x_prev_var, Literal lit))) in
			x_prev_var, [ cmd_ass_prev ]
		| _ -> raise (Failure "make_check_empty_test: x_prev needs to be either a literal or a var")) in

	let x_new, cmd_ass_new =
		(match x_new with
		| Var x_new -> x_new, []
		| Literal lit ->
			let x_new_var = fresh_var () in
			let cmd_ass_new = (None, LBasic (Assignment (x_new_var, Literal lit))) in
			x_new_var, [ cmd_ass_new ]
		| _ -> raise (Failure "make_check_empty_test: x_new needs to be either a literal or a var")) in

	(* goto [x_new = empty] next1 next2 *)
	let next1 = fresh_next_label () in
	let next2 = fresh_next_label () in
	let cmd_goto = (None, LGuardedGoto (BinOp (Var x_new, Equal, Literal Empty), next1, next2)) in

	(* next1: skip  *)
	let cmd_skip = (Some next1, LBasic Skip) in

	(* next2: x := PHI(x_new, x_previous) *)
	let x = fresh_var () in
	let cmd_phi = (Some next2, LPhiAssignment (x, [| (Var x_new); (Var x_prev) |])) in

	cmd_ass_xprev @ cmd_ass_new @ [ cmd_goto; cmd_skip; cmd_phi], x


let make_loop_end cur_val_var prev_val_var break_vars end_lab cur_first =
(**
    	end_loop: x_ret_4 := PHI(break_vars, cur_val_var)
			          goto [ x_ret_4 = empty ] next3 next4
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
	let phi_args = List.map (fun x -> Var x) break_vars in
	let phi_args = Array.of_list phi_args in
	let cmd_ass_ret4 = LPhiAssignment (x_ret_4, phi_args) in

	(* goto [ x_ret_4 = empty ] next3 next4 *)
	let cmd_goto = LGuardedGoto ((BinOp (Var x_ret_4, Equal, Literal Empty), next3, next4)) in

	(* next4:    x_ret_5 := PHI(x_ret_4, prev_val_var) *)
	let cmd_ass_ret5 = LPhiAssignment (x_ret_5, [| (Var x_ret_4); (Var prev_val_var) |]) in

	let cmds = [
		(Some end_lab, cmd_ass_ret4);    (* end_loop:   x_ret_4 := PHI(cur_val_var, break_vars) *)
		(None,         cmd_goto);        (*             goto [ x_ret_4 = empty ] next3 next4  *)
		(Some next3,   LBasic Skip);   (* next3:      skip                                    *)
		(Some next4,   cmd_ass_ret5)     (* next4:      x_ret_5 := PHI(x_ret_4, prev_val_var)   *)
	]	in
	cmds, x_ret_5

let is_get_value_call cmd =
	match cmd with
	| LCall (_, (Literal (String proc_name)), _, _) -> (proc_name = getValueName)
	| _ -> false

let is_put_value_call cmd =
	match cmd with
	| LCall (_, (Literal (String proc_name)), _, _) -> (proc_name = putValueName)
	| _ -> false

let is_hasProperty_call cmd =
	match cmd with
	| LCall (_, (Literal (String proc_name)), _, _) -> (proc_name = hasPropertyName)
	| _ -> false

let get_args cmd =
	match cmd with
	| LCall (_, (Literal (String proc_name)), args, _) -> Some args
	| _ -> None


let annotate_cmd_top_level metadata lcmd =

	let lab, (cmd : jsil_lab_cmd) = lcmd in

	let fold_unfold_pi_macro_for_put_and_get_value args =
		let new_args =
			(match args with
			| Some args ->  args
			| None -> raise (Failure "No argument passed to GetPutValue folding.")) in
		(match new_args with
	  (* JOSE: I do not understand this case *)
		| [ Literal n ] -> [], []
		(* PUTVALUE and GETVALUE cases *)
		| [ arg ]
		| [ arg; _ ] ->
			let arg = JSIL_Logic_Utils.expr_2_lexpr arg in
			let fold_args = [arg; LVar (fresh_logical_variable ()); LVar (fresh_logical_variable ()); LVar (fresh_logical_variable ()); LVar (fresh_logical_variable ()) ] in
			let fold_macro = Macro (JS2JSIL_Constants.macro_GPVF_name, fold_args) in
			let unfold_macro = Macro (JS2JSIL_Constants.macro_GPVU_name, [ arg ]) in
			[ fold_macro ], [ unfold_macro ]
		(* No other cases handled *)
		| _ -> raise (Failure "Folding/Unfolding in the wrong place.")) in

	let fold_unfold_pi_for_hasProperty args =
		let new_args =
			(match args with
			| Some args ->  args
			| None -> raise (Failure "No argument passed to hasProperty folding.")) in
		(match new_args with
		(* HasProperty case *)
		| [ arg1; arg2] ->
			let l_arg1 = JSIL_Logic_Utils.expr_2_lexpr arg1 in
			let l_arg2 = JSIL_Logic_Utils.expr_2_lexpr arg2 in
			let fold_args = [l_arg1; l_arg2; LVar (fresh_logical_variable ()); LVar (fresh_logical_variable ()); LVar (fresh_logical_variable ()); LVar (fresh_logical_variable ()) ] in
			let fold_lcmd = Fold (LPred (pi_predicate_name, fold_args)) in
			let unfold_lcmd = RecUnfold pi_predicate_name in
			[ fold_lcmd ], [ unfold_lcmd ]
		(* No other cases handled *)
		| _ -> raise (Failure "Folding/Unfolding in the wrong place.")) in

	if ((is_get_value_call cmd) || (is_put_value_call cmd))  then (
		(* Printf.printf "I found a call to GetValue/PutValue.\n"; *)
		let fold_lcmds, unfold_lcmds = fold_unfold_pi_macro_for_put_and_get_value (get_args cmd) in
		let new_metadata =
			{ metadata with pre_logic_cmds = fold_lcmds; post_logic_cmds = unfold_lcmds } in
		(new_metadata, lab, cmd)
	) else if (is_hasProperty_call cmd) then (
			let fold_lcmds, unfold_lcmds = fold_unfold_pi_for_hasProperty (get_args cmd) in
			(* Printf.printf "I found a call to hasProperty.\n\t%n Folds: %s.\n\tUnfolds: %n!\n"
				(List.length fold_lcmds)
				(String.concat ","
					(List.map JSIL_Print.string_of_lcmd fold_lcmds))
				(List.length unfold_lcmds); *)
			let new_metadata =
				{ metadata with pre_logic_cmds = fold_lcmds; post_logic_cmds = unfold_lcmds } in
			(new_metadata, lab, cmd)
	) else (metadata, lab, cmd)

let annotate_cmds_top_level metadata cmds =
	List.map (annotate_cmd_top_level metadata) cmds


(**
  *  translate_expr( tr_ctx, e) = cmds, e', x_is
	   @param tr_ctx  translation context
		 @param e javascript expression to compile
		 @return (cmds, e', x_is) ->
			  cmd  - the result of the compilation
				e'   - jsil expression that holds at runtime the outcome of the compilation
				x_is - the list of variables that may hold error values
	*)
let rec translate_expr tr_ctx e : ((jsil_metadata * (string option) * jsil_lab_cmd) list) * jsil_expr * (string list) =

	let f = translate_expr tr_ctx in

	let cur_var_tbl = get_scope_table cc_tbl tr_ctx.tr_er_fid in
	let find_var_er_index v =
		(try
			print_debug (Printf.sprintf "Trying to find variable %s given the vislist %s in the var table %s \n"
				v
				(String.concat ", " tr_ctx.tr_vis_list)
				(JS2JSIL_Preprocessing.string_of_vtf_tbl cur_var_tbl));
			let fid_v = Hashtbl.find cur_var_tbl v in
			let fid_v_index = JS2JSIL_Preprocessing.get_vis_list_index tr_ctx.tr_vis_list fid_v in
			fid_v_index
			with _ ->
				raise (Failure (Printf.sprintf "Error: %s is not in the scope clarification table!" v))) in


	(* All the other commands must get the offsets and nothing else *)
	let js_char_offset          = e.Parser_syntax.exp_offset in
	let js_line_offset          = tr_ctx.tr_offset_converter js_char_offset in
	let metadata                = { line_offset = Some js_line_offset; invariant = None; pre_logic_cmds = []; post_logic_cmds = [] } in
	let annotate_cmds           = annotate_cmds_top_level metadata in
	let annotate_cmd            = fun cmd lab -> annotate_cmd_top_level metadata (lab, cmd) in

	(* The first command must get the logic commands and the invariants *)
	let lcmds, call_lcmds       = JS2JSIL_Preprocessing.translate_lannots_in_exp cc_tbl vis_tbl old_fun_tbl tr_ctx.tr_fid tr_ctx.tr_sc_var false e in
	let invariant               = JS2JSIL_Preprocessing.translate_invariant_in_exp cc_tbl vis_tbl old_fun_tbl tr_ctx.tr_fid tr_ctx.tr_sc_var e in
	let annotate_first_cmd      = add_more_metadata metadata lcmds invariant in
	let annotate_first_call_cmd = add_more_metadata metadata call_lcmds None in

	(* Printf.printf "NOW NOW NOW lcmds: %s\n call_cmds: %s with the expression %s\n"
		(String.concat ", " (List.map JSIL_Print.string_of_lcmd lcmds))
		(String.concat ", " (List.map JSIL_Print.string_of_lcmd call_lcmds))
		(Pretty_print.string_of_exp true e); *)


	let compile_var_dec x e =
		let cmds_e, x_e, errs_e = f e in

		(* x_v := i__getValue (x) with err *)
		let x_v, cmd_gv_x, errs_x_v = make_get_value_call x_e tr_ctx.tr_err in

		(* x_sf := l-nth(x_sc, index) *)
		let index = find_var_er_index x in
		let x_sf = fresh_var () in
		let cmd_xsf_ass = LBasic (Assignment (x_sf, LstNth (Var tr_ctx.tr_sc_var, lit_num (float_of_int index)))) in

		(* x_ref := {{ v, x_sf, "x" }}  *)
		let x_ref = fresh_var () in
		let cmd_xref_ass = LBasic (Assignment (x_ref, EList [lit_refv; Var x_sf; lit_str x])) in

		(* x_cae := i__checkAssignmentErrors (x_ref) with err *)
		let x_cae, cmd_cae = make_cae_call (Var x_ref)  tr_ctx.tr_err in

		(* x_pv := i__putValue(x_ref, x_v) with err2 *)
		let x_pv, cmd_pv = make_put_value_call (Var x_ref) x_v tr_ctx.tr_err in
		let cmds = cmds_e @ (annotate_cmds (add_none_labs [
			cmd_gv_x;      (* x_v := i__getValue (x) with err          *)
			cmd_xsf_ass;   (* x_sf := [x__scope, fid]                  *)
			cmd_xref_ass;  (* x_ref := ref_v(x_sf, "x")                *)
			cmd_cae;
			cmd_pv         (* x_pv := i__putValue(x_ref, x_v) with err *)
		])) in
		let errs = errs_e @ errs_x_v @ [ x_cae; x_pv ] in
		cmds, x_ref, errs in

	let compile_var_dec_without_exp x =
		let index = find_var_er_index x in

		(* x_sf := l-nth(x_sc, index) *)
		let index = find_var_er_index x in
		let x_sf = fresh_var () in
		let cmd_xsf_ass = LBasic (Assignment (x_sf, LstNth (Var tr_ctx.tr_sc_var, lit_num (float_of_int index)))) in

		(* x_ref := {{ v, x_sf, "x" }}  *)
		let x_ref = fresh_var () in
		let cmd_xref_ass = LBasic (Assignment (x_ref, EList [lit_refv; Var x_sf; lit_str x])) in


		(* x_cae := i__checkAssignmentErrors (x_ref) with err *)
		let x_cae, cmd_cae = make_cae_call (Var x_ref)  tr_ctx.tr_err in

		let cmds = annotate_cmds (add_none_labs [
			cmd_xsf_ass;   (* x_sf := [x__scope, v_fid]                          *)
			cmd_xref_ass;  (* x_ref := ref_v(x_sf, "x")                          *)
			cmd_cae;       (* x_cae := i__checkAssignmentErrors (x_ref) with err *)
		]) in
		x_ref, cmds, [ x_cae ] in


	let translate_bin_logical_operator e1 e2 lbop err =
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 err in
		(* x1_b := i__toBoolean (x1_v) with err  *)
		let x1_b, cmd_tb_x1 = make_to_boolean_call x1 x1_v err in
		(* goto [x1_b] end next *)
		let next = fresh_next_label () in
		let end_lab = fresh_end_label () in
		let cmd_goto =
			(match lbop with
			| Parser_syntax.And -> LGuardedGoto (Var x1_b, next, end_lab)
			| Parser_syntax.Or -> LGuardedGoto (Var x1_b, end_lab, next)) in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 err in
		(* x_r := PHI(x1_v, x2_v) *)
		let x_r = fresh_var () in
		let cmd_ass_xr = LPhiAssignment (x_r, [| (Var x1_v); (Var x2_v) |]) in

		let cmds2 = add_initial_label cmds2 next metadata in
		let cmds = annotate_first_cmd (
			cmds1 @ (annotate_cmds [            (*         cmds1                                              *)
			(None,         cmd_gv_x1);          (*         x1_v := i__getValue (x1) with err                  *)
			(None,         cmd_tb_x1);          (*         x1_b := i__toBoolean (x1_v) with err               *)
			(None,         cmd_goto)            (*         goto [x1_b] next end                               *)
		]) @ cmds2 @ (annotate_cmds [           (* next:   cmds2                                              *)
			(None,         cmd_gv_x2);          (*         x2_v := i__getValue (x2) with err                  *)
			(Some end_lab, cmd_ass_xr)          (* end:    x_r := PHI(x1_v, x2_v)                             *)
		])) in
		let errs = errs1 @ errs_x1_v @ [ x1_b ] @ errs2 @ errs_x2_v in
		cmds, Var x_r, errs	in

	let translate_arg_list xes err =
		let cmds_args, x_args_gv, errs_args =
			List.fold_left
				(fun (cmds_args, x_args_gv, errs_args) e_arg ->
					let cmds_arg, x_arg, errs_arg = f e_arg in
					let x_arg_v, cmd_gv_arg, errs_xarg_v = make_get_value_call x_arg err in
					(cmds_args @ cmds_arg @ [ (annotate_cmd cmd_gv_arg None) ], x_args_gv @ [ Var x_arg_v ], (errs_args @ errs_arg @ errs_xarg_v)))
				([], [], [])
				xes in
		cmds_args, x_args_gv, errs_args in


	match e.Parser_syntax.exp_stx with

	| Parser_syntax.This ->
		(**
      Section 11.1.1 - The this Keyword
			C(this) =  		x := __this
		*)
		let new_var = fresh_var () in
		let cmd = LBasic (Assignment (new_var, (Var var_this))) in
		let cmds = annotate_first_cmd [
			annotate_cmd cmd None
		] in
		cmds, Var new_var, []

	| Parser_syntax.Var v ->
		(**
		 Section 11.1.2 - Identifier Reference
		 Found in the closure clarification table: Phi(fid_1, x) = i
					x_1 := l-nth(x_sc, i);
					x_r := v-ref(x_1, "x")

		Not found in the closure clarification table: Phi(fid_1, x) = bot
					x_1 := o__hasProperty($lg, "x") with err;
					goto [x_1] then else
			then: 	x_then := v-ref($lg, "x");
		      		goto end;
			else: 	x_else := v-ref(undefined, "x");
			end:  	x_r = PHI(x_then, x_else)
 		*)

		let translate_var_not_found v =
			(* 	x_1 := o__hasProperty($lg, "x") with err *)
			let x_1 = fresh_var () in
		  	let cmd_ass_x1 = LCall (x_1, Literal (String hasPropertyName), [ Literal (Loc locGlobName); Literal (String v) ], Some tr_ctx.tr_err) in

			(* goto [x_1] then else *)
			let then_lab = fresh_then_label () in
			let else_lab = fresh_else_label () in
			let end_lab = fresh_end_label () in
			let cmd_goto_unres_ref = LGuardedGoto (Var x_1, then_lab, else_lab) in

			(* x_then := v-ref($lg, "x");   *)
			let x_then = fresh_var () in
			let cmd_ass_xthen = LBasic (Assignment (x_then, EList [lit_refv; lit_loc locGlobName; lit_str v]))  in

			(* x_then := v-ref(undefined, "x");  *)
			let x_else = fresh_var () in
			let cmd_ass_xelse = LBasic (Assignment (x_else, EList [lit_refv; Literal Undefined; lit_str v])) in

			(* x_r = PHI(x_then, x_else)  *)
			let x_r = fresh_var () in
		 	let cmd_ass_xr = LPhiAssignment (x_r, [| (Var x_then); (Var x_else) |]) in

			let cmds = [
				(None,          cmd_ass_x1);          (*       x_1 := o__hasProperty($lg, "x") with err    *)
				(None,          cmd_goto_unres_ref);  (*       goto [x_1] then else                        *)
				(Some then_lab, cmd_ass_xthen);       (* then: x_then := v-ref($lg, "x")                   *)
				(None,          LGoto end_lab);      (*       goto end                                    *)
				(Some else_lab, cmd_ass_xelse);       (* else: x_else := v-ref(undefined, "x")           *)
				(Some end_lab,  cmd_ass_xr)           (*       x_r = PHI(x_then, x_else)                   *)
			] in
			let cmds = annotate_cmds cmds in
			(* List.iter (fun ({ line_offset; invariant; pre_logic_cmds; post_logic_cmds }, _, _) ->
				Printf.printf "Length: pre: %d \t post: %d\n" (List.length pre_logic_cmds) (List.length post_logic_cmds)) cmds; *)
			cmds, Var x_r, [ x_1 ] in

		let translate_var_found v index =
			(* x_1 := l-nth(x_sc, index) *)
			let x_1 = fresh_var () in
			let cmd_ass_x1 = LBasic (Assignment (x_1, LstNth (Var tr_ctx.tr_sc_var, lit_num (float_of_int index)))) in

			(* x_r := {{ "v", x_1, "x" }} *)
			let x_r = fresh_var () in
			let cmd_ass_xret = LBasic (Assignment (x_r, EList [lit_refv; Var x_1; lit_str v])) in

			let cmds = [
				(None, cmd_ass_x1);     (*   x_1 := l-nth(x_sc, index)    *)
				(None, cmd_ass_xret);   (*   x_r := v-ref(x_1, "x")       *)
			] in
			let cmds = annotate_cmds cmds in
			cmds, Var x_r, [] in

		(try translate_var_found v (find_var_er_index v)
			with _ -> translate_var_not_found v)


	(**
	 Section 11.1.3 - Literals
	*)
	| Parser_syntax.Null ->  (annotate_first_cmd []), Literal Null, []
	| Parser_syntax.Bool b -> (annotate_first_cmd []), Literal (Bool b), []
	| Parser_syntax.String s ->
		let escaped_s = Str.global_replace (Str.regexp "\"") "\\\"" s in
		(annotate_first_cmd []), Literal (String escaped_s), []
	| Parser_syntax.Num n ->  (annotate_first_cmd []), Literal (Num n), []


	(**
	 Section 11.1.4 - Array Initialiser
	*)
	| Parser_syntax.Array eos -> (* raise (Failure "not implemented yet - array literal") *)
		
		(* xfvm := metadata (x_f_val) *)
		let xarrm = fresh_var () in
		let cmd_xarrm = annotate_cmd (LBasic (New (xarrm, Some (Literal Null)))) None in
		
		(* x_arr := new () *)
		let x_arr = fresh_obj_var () in
		(* TODO: METADATA *)
		let cmd_new_obj = annotate_cmd (LBasic (New (x_arr, Some (Var xarrm)))) None in

		(* x_cdo := create_default_object (x_obj, $larr_proto, "Array") *)
		let x_cdo = fresh_var () in
		let cmd_cdo_call = annotate_cmd (LCall (x_cdo, Literal (String createDefaultObjectName), [ Var x_arr; Literal (Loc locArrPrototype); Literal (String "Array") ], None)) None in

		(* [x_arr, "length"] := {{ "d", num, true, false, false }} *)
		let cmd_set_len num = annotate_cmd (LBasic (Mutation (Var x_arr,  Literal (String "length"), EList [ Literal (String "d"); Literal (Num (float_of_int num)); Literal (Bool true); Literal (Bool false); Literal (Bool false) ], None))) None in

    	let translate_array_property_definition x_obj e err num =
			let cmds, x, errs = f e in
			(* x_v := i__getValue (x) with err *)
			let x_v, cmd_gv_x, errs_x_v = make_get_value_call x err in

			(* x_desc := {{ "d", x_v, true, true, true}}  *)
			let x_desc = fresh_desc_var () in
			let cmd_ass_xdesc = LBasic (Assignment (x_desc, EList [ Literal (String "d"); Var x_v; Literal (Bool true); Literal (Bool true); Literal (Bool true) ] )) in

			let prop = Literal (String (string_of_int num)) in

			(* x_adop := a__defineOwnProperty(x_obj, toString(num), x_desc, true) with err *)
			let x_adop, cmd_adop_x = make_dop_call x_obj prop x_desc false err in

			let cmds = cmds @ (annotate_cmds [
				(None, cmd_gv_x);           (* x_v := i__getValue (x) with err                                            *)
				(None, cmd_ass_xdesc);      (* x_desc := {{ "d", x_v, true, true, true}}                                     *)
				(None, cmd_adop_x)          (* x_dop := a__defineOwnProperty(x_obj, toString(num), x_desc, true) with err *)
			]) in
			let errs = errs @ errs_x_v @ [ x_adop ] in
			cmds, errs in

		let cmds, errs, num =
			List.fold_left (fun (cmds, errs, num) oe ->
				let new_cmds, new_errs =
				(match oe with
			  	| None ->
							[cmd_set_len (num + 1)], []
				  | Some e ->
					  	translate_array_property_definition x_arr e tr_ctx.tr_err num) in
				(cmds @ new_cmds, errs @ new_errs, num + 1))
				([], [], 0)
				eos in
		let cmds = annotate_first_cmd (cmd_xarrm :: cmd_new_obj :: (cmd_cdo_call :: (cmd_set_len 0) :: cmds)) in
		cmds, (Var x_arr), errs


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
			                x_desc := {{ "d", x_v, true, true, true}}
			                x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err

			-----------------------
			C_pd ( get pn () { s }^getter_id ) =
				          	x1 := copy_object (x_scope, {{main, fid1, ..., fidn }})
							x_f := create_function_object(x1, getter_id, {{}})
							x_desc := {{ "g", true, true, empty, empty, x_f, empty }}
							x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err

			-----------------------
		 	C_pd ( set pn (x1, ..., xn) { s }^setter_id ) =
							x1 := copy_object (x_scope, {{main, fid1, ..., fidn }})
							x_f := create_function_object(x1, setter_id, {{x1, ..., xn}})
							x_desc := {{ "g", true, true, empty, empty, empty, x_f }}
							x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err
		*)

		(* xfvm := metadata (x_f_val) *)
		let x_obj_m = fresh_var () in
		let cmd_xobjm = annotate_cmd (LBasic (New (x_obj_m, Some (Literal Null)))) None in
		
		(* x_obj := new () *)
		let x_obj = fresh_obj_var () in
		let cmd_new_obj = annotate_cmd (LBasic (New (x_obj, Some (Var x_obj_m)))) None in

		(* x_cdo := create_default_object (x_obj, $lobj_proto) *)
		let x_cdo = fresh_var () in
		let cmd_cdo_call = annotate_cmd (LCall (x_cdo, Literal (String createDefaultObjectName), [ Var x_obj; Literal (Loc locObjPrototype) ], None)) None in

		let translate_property_name pname =
			(match pname with
			| Parser_syntax.PropnameId s
		    | Parser_syntax.PropnameString s -> Literal (String s)
      		| Parser_syntax.PropnameNum n -> UnOp (ToStringOp, (Literal (Num n)))) in

		let translate_data_property_definition x_obj prop e err =
			let cmds, x, errs = f e in
			(* x_v := i__getValue (x) with err *)
			let x_v, cmd_gv_x, errs_x_v = make_get_value_call x err in

			(* x_desc := {{ "d", x_v, true, true, true}}  *)
			let x_desc = fresh_desc_var () in
			let cmd_ass_xdesc = LBasic (Assignment (x_desc, EList [ Literal (String "d"); Var x_v; Literal (Bool true); Literal (Bool true); Literal (Bool true) ] )) in

			(* x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err *)
			let x_dop, cmd_dop_x = make_dop_call x_obj prop x_desc true err in

			let cmds = cmds @ (annotate_cmds [
				(None, cmd_gv_x);          (* x_v := i__getValue (x) with err                                          *)
				(None, cmd_ass_xdesc);     (* x_desc := {{ "d", x_v, true, true, true}}                                   *)
				(None, cmd_dop_x)          (* x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err    *)
			]) in
			let errs = errs @ errs_x_v @ [ x_dop ] in
			cmds, errs in

		let translate_accessor_descriptor x_obj prop accessor is_getter err =
			let f_id = try JS2JSIL_Preprocessing.get_codename accessor
				with _ -> raise (Failure "anonymous function literals should be annotated with their respective code names - Getter function") in
			let params =
				(match accessor.Parser_syntax.exp_stx with
				| Parser_syntax.FunctionExp (_, _, params, _) -> params
				| _ -> raise (Failure "getters should be annonymous functions")) in

			(* x_f := create_function_object(x_sc, f_id, f_id, params) *)
			let x_f, cmd_cfo = make_create_function_object_call tr_ctx.tr_sc_var f_id params in

			(* x_desc := {{ "g", true, true, empty, empty, x_f, empty }} *)
			(* x_desc := {{ "g", true, true, empty, empty, empty, x_f }} *)
			let x_desc = fresh_desc_var () in
			let desc_params =
				match is_getter with
				| true ->  [ Literal (String "g"); Literal (Bool true); Literal (Bool true); Literal Empty; Literal Empty; Var x_f; Literal Empty ]
				| false -> [ Literal (String "g"); Literal (Bool true); Literal (Bool true); Literal Empty; Literal Empty; Literal Empty; Var x_f ] in
			let cmd_ass_xdesc = LBasic (Assignment (x_desc, EList desc_params)) in

			(* x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err *)
			let x_dop, cmd_dop_x = make_dop_call x_obj prop x_desc true err in

			let cmds = annotate_cmds [
				(None, cmd_cfo);           (* x_f := create_function_object(x_sc, f_id, f_id, params)                  *)
				(None, cmd_ass_xdesc);     (* x_desc := x_desc := {{ "g", true, true, empty, empty, -, - }}          *)
				(None, cmd_dop_x)          (* x_dop := o__defineOwnProperty(x_obj, C_pn(pn), x_desc, true) with err    *)
			] in
			cmds, [ x_dop ] in

		let cmds, errs =
			List.fold_left (fun (cmds, errs) (pname, ptype, e) ->
				let prop = translate_property_name pname in
				let new_cmds, new_errs =
					(match ptype with
					| Parser_syntax.PropbodyVal -> translate_data_property_definition x_obj prop e tr_ctx.tr_err
					| Parser_syntax.PropbodyGet -> translate_accessor_descriptor x_obj prop e true tr_ctx.tr_err
					| Parser_syntax.PropbodySet -> translate_accessor_descriptor x_obj prop e false tr_ctx.tr_err) in
				cmds @ new_cmds, errs @ new_errs)
				([], [])
				xs in
		let cmds = annotate_first_cmd (cmd_xobjm :: cmd_new_obj :: (cmd_cdo_call :: cmds)) in
		cmds, (Var x_obj), errs


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

		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in

		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		(* x_oc := i__checkObjectCoercible (x1_v) with err *)
		let x_oc = fresh_var () in
		let cmd_coc_x1 = LCall (x_oc, Literal (String checkObjectCoercibleName), [ Var x1_v ], Some tr_ctx.tr_err) in

		(* x2_s := i__toString (x2_v) with err *)
		let x2_s, cmd_ts_x2 = make_to_string_call x2 x2_v tr_ctx.tr_err in

		(* 	x_r := ref-o(x1_v, x2_s) *)
		let x_r = fresh_var () in
		let cmd_ass_xr = LBasic (Assignment (x_r, EList [lit_refo; Var x1_v; Var x2_s])) in

		let cmds =  annotate_first_cmd (cmds1 @ [              (* cmds1                       *)
			(annotate_cmd cmd_gv_x1 None) (* x1_v := i__getValue (x1) with err                *)
		] @ cmds2 @ (annotate_cmds [      (* cmds2                                            *)
			(None, cmd_gv_x2);            (* x2_v := i__getValue (x2) with err                *)
			(None, cmd_coc_x1);           (* x_oc := i__checkObjectCoercible (x1_v) with err  *)
			(None, cmd_ts_x2);            (* x2_s := i__toString (x2_v) with err              *)
			(None, cmd_ass_xr)            (* x_r := ref-o(x1_v, xs_s)                         *)
		])) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ [ x_oc; x2_s ] in
		cmds, (Var x_r), errs


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

		let cmds, x, errs = f e in

		(* x_v := i__getValue (x) with err *)
		let x_v, cmd_gv_x, errs_x_v = make_get_value_call x tr_ctx.tr_err in

		(* x_oc := i__checkObjectCoercible (x_v) with err *)
		let x_oc = fresh_var () in
		let cmd_coc_x = LCall (x_oc, Literal (String checkObjectCoercibleName), [ Var x_v ], Some tr_ctx.tr_err) in

		(* 	x_r := ref-o(x_v, "p") *)
		let x_r = fresh_var () in
		let cmd_ass_xr = LBasic (Assignment (x_r, EList [lit_refo; Var x_v; lit_str p])) in

		let cmds = annotate_first_cmd (
			cmds @ (annotate_cmds [           (* cmds                                             *)
			(None, cmd_gv_x);                 (* x_v := i__getValue (x) with err                  *)
			(None, cmd_coc_x) ;               (* x_oc := i__checkObjectCoercible (x_v) with err   *)
			(None, cmd_ass_xr)                (* x_r := ref-o(x_v, "p")                           *)
		]))  in
		let errs = errs @ errs_x_v @ [ x_oc ] in
		cmds, (Var x_r), errs


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
					next1:  x_hp := [x_f_val, "@construct"];
					        goto [ x_hp = empty ] err next2;
					next2:	x_this := new ();
					        x_ref_prototype := ref-o(x_f_val, "prototype");
									x_f_prototype := i__getValue(x_ref_prototype) with err;
									goto [typeof (x_f_prototype) = Obj] then0 else0;
					then0:	x_f_prototype := $lobj_proto;
					else0:	x_cdo := i__createDefaultObject (x_this, x_f_prototype);
								 	x_body := [x_f_val, "@construct"];
		       				x_scope := [x_f_val, "@scope"];
					 				x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err;
					 				goto [typeOf(x_r1) = Obj ] next4 next3;
        	next3:  skip
					next4:  x_r3 := PHI(x_r1, x_this)
		*)
		
		let cmds_ef, x_ef, errs_ef = f e_f in

		(* x_f_val := i__getValue (x_f) with err1;  *)
		let x_f_val, cmd_gv_f, errs_xf_val = make_get_value_call x_ef tr_ctx.tr_err in

		let cmds_args, x_args_gv, errs_args = translate_arg_list xes tr_ctx.tr_err in

		(* goto [ typeOf(x_f_val) != Object] err next1; err -> typeerror *)
		let next1 = fresh_next_label () in
		let goto_guard_expr = UnOp (Not, (BinOp (TypeOf (Var x_f_val), Equal, Literal (Type ObjectType)))) in
		let cmd_goto_is_obj = LGuardedGoto (goto_guard_expr, tr_ctx.tr_err, next1) in
		
		(* xfvm := metadata (x_f_val) *)
		let xfvm = fresh_var () in
		let cmd_xfvm = LBasic (MetaData (xfvm, Var x_f_val)) in

		(* x_hp := [xfvm, "@construct"]; *)
		let x_hp = fresh_var () in
		let cmd_hf_construct = LBasic (HasField (x_hp, Var xfvm, Literal (String _constructPropName))) in

		(* goto [ x_hp = empty ] err next2; *)
		let call = fresh_then_label () in
		let get_bt = fresh_then_label () in
		let jump = if_verification call get_bt in
		let cmd_goto_xhp = LGuardedGoto (Var x_hp, jump, tr_ctx.tr_err) in

		let x_bt = fresh_var () in
		let cmd_get_bt = LBasic (HasField (x_bt, Var xfvm, Literal (String "@boundThis"))) in

		let bind = fresh_else_label () in
		let goto_guard_expr = (Var x_bt) in
		let cmd_bind_test = LGuardedGoto (goto_guard_expr, bind, call) in

		(* BIND *)

		let x_ba = fresh_var () in
		let cmd_get_ba = LBasic (Lookup (x_ba, Var xfvm, Literal (String "@boundArguments"))) in

		let x_tf = fresh_var () in
		let cmd_get_tf = LBasic (Lookup (x_tf, Var xfvm, Literal (String "@targetFunction"))) in

		(* xfvm := metadata (x_f_val) *)
		let xbthism = fresh_var () in
		let cmd_xbthism = LBasic (New (xbthism, Some (Literal Null))) in

		(* x_bthis := new (); *)
		let x_bthis = fresh_this_var () in
		let cmd_bcreate_xobj = LBasic (New (x_bthis, Some (Var xbthism))) in

		(* x_bref_fprototype := ref-o(x_tf, "prototype");  *)
		let x_bref_fprototype = fresh_var () in
		let cmd_bass_xreffprototype = LBasic (Assignment (x_bref_fprototype, EList [lit_refo; Var x_tf; lit_str "prototype"])) in

		(* x_bf_prototype := i__getValue(x_bref_prototype) with err; *)
		let x_bf_prototype, cmd_bgv_xreffprototype, errs_bf_prototype = make_get_value_call (Var x_bref_fprototype) tr_ctx.tr_err in

		let bthen1 = fresh_then_label () in
		let belse1 = fresh_else_label () in
		let goto_guard_expr = BinOp (TypeOf (Var x_bf_prototype), Equal, Literal (Type ObjectType)) in
		let cmd_bis_object = LGuardedGoto (goto_guard_expr, belse1, bthen1) in

		let x_bwhyGodwhy = fresh_var () in
		let cmd_bset_proto = LBasic (Assignment (x_bwhyGodwhy, Literal (Loc locObjPrototype))) in

		let x_bprototype = fresh_var () in
		let cmd_bproto_phi = LPhiAssignment (x_bprototype, [| Var x_bf_prototype; Var x_bwhyGodwhy |]) in

		(* x_cdo := i__createDefaultObject (x_this, x_f_prototype); *)
		let x_bcdo = fresh_var () in
		let cmd_bcdo_call = LCall (x_bcdo, Literal (String createDefaultObjectName), [ Var x_bthis; Var x_bprototype ], None) in

		(* xtfm := metadata (x_tf) *)
		let xtfm = fresh_var () in
		let cmd_xtfm = LBasic (MetaData (xtfm, Var x_tf)) in

		let x_bbody = fresh_body_var () in
		let cmd_bbody = LBasic (Lookup (x_bbody, Var xtfm, Literal (String _constructPropName))) in

		let x_bfscope = fresh_fscope_var () in
		let cmd_bscope = LBasic (Lookup (x_bfscope, Var xtfm, Literal (String _scopePropName))) in

		let x_params = fresh_var () in
		let jsil_list_params = EList ([Var x_bbody; Var x_bfscope; Var x_bthis]) in
		let cmd_append = LBasic (Assignment (x_params, (BinOp (BinOp (jsil_list_params, LstCat, Var x_ba), LstCat, (EList x_args_gv))))) in

		let x_bconstruct = fresh_var () in
		let cmd_bind = LApply (x_bconstruct, [ Var x_params ], Some tr_ctx.tr_err) in

		(* goto [ x_bconstruct = empty ] next3 next4; *)
		let bnext3 = fresh_next_label () in
		let bnext4 = fresh_next_label () in
		let goto_guard_expr = BinOp (TypeOf (Var x_bconstruct), Equal, Literal (Type ObjectType)) in
		let cmd_bgoto_test_type = LGuardedGoto (goto_guard_expr, bnext4, bnext3) in

		(* next3: skip; *)
		let cmd_bret_this = LBasic Skip in

		(* next4: x_rbind := PHI(x_bconstruct, x_bt) *)
		let x_rbind = fresh_var () in
		let cmd_bphi_final = LPhiAssignment (x_rbind, [| Var x_bconstruct; Var x_bthis |]) in

		(* SYNC *)

		let join = fresh_label () in
		let cmd_sync = LGoto join in 

		(* xfvm := metadata (x_f_val) *)
		let xthism = fresh_var () in
		let cmd_xobjm = LBasic (New (xthism, Some (Literal Null))) in

		(* x_this := new (); *)
		let x_this = fresh_this_var () in
		let cmd_create_xobj = LBasic (New (x_this, Some (Var xthism))) in

		(* x_ref_fprototype := ref-o(x_f_val, "prototype");  *)
		let x_ref_fprototype = fresh_var () in
		let cmd_ass_xreffprototype = LBasic (Assignment (x_ref_fprototype, EList [lit_refo; Var x_f_val; lit_str "prototype"])) in

		(* x_f_prototype := i__getValue(x_ref_prototype) with err; *)
		let x_f_prototype, cmd_gv_xreffprototype, errs_xf_prototype = make_get_value_call (Var x_ref_fprototype) tr_ctx.tr_err in

		let then1 = fresh_then_label () in
		let else1 = fresh_else_label () in
		let goto_guard_expr = BinOp (TypeOf (Var x_f_prototype), Equal, Literal (Type ObjectType)) in
		let cmd_is_object = LGuardedGoto (goto_guard_expr, else1, then1) in

		let x_whyGodwhy = fresh_var () in
		let cmd_set_proto = LBasic (Assignment (x_whyGodwhy, Literal (Loc locObjPrototype))) in

		let x_prototype = fresh_var () in
		let cmd_proto_phi = LPhiAssignment (x_prototype, [| (Var x_f_prototype); (Var x_whyGodwhy) |]) in

		(* x_cdo := i__createDefaultObject (x_this, x_f_prototype); *)
		let x_cdo = fresh_var () in
		let cmd_cdo_call = LCall (x_cdo, Literal (String createDefaultObjectName), [ Var x_this; Var x_prototype ], None) in

		(* x_body := [xfvm, "@construct"];  *)
		let x_body = fresh_body_var () in
		let cmd_body = LBasic (Lookup (x_body, Var xfvm, Literal (String _constructPropName))) in

		(* x_fscope := [xfvm, "@scope"]; *)
		let x_fscope = fresh_fscope_var () in
		let cmd_scope = LBasic (Lookup (x_fscope, Var xfvm, Literal (String _scopePropName))) in

		(* x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err  *)
		let x_r1 = fresh_var () in
		let proc_args = (Var x_fscope) :: (Var x_this) :: x_args_gv in
		let cmd_proc_call = LCall (x_r1, (Var x_body), proc_args, Some tr_ctx.tr_err) in

		(* goto [ x_r1 = empty ] next3 next4; *)
		let next3 = fresh_next_label () in
		let next4 = fresh_next_label () in
		let goto_guard_expr = BinOp (TypeOf (Var x_r1), Equal, Literal (Type ObjectType)) in
		let cmd_goto_test_type = LGuardedGoto (goto_guard_expr, next4, next3) in

		(* next3: skip; *)
		let cmd_ret_this = LBasic Skip in

		(* next4: x_r2 := PHI(x_r1, x_this) *)
		let x_rcall = fresh_var () in
		let cmd_phi_final = LPhiAssignment (x_rcall, [| (Var x_r1); (Var x_this) |]) in

		let x_final = fresh_var () in
		let cmd_phi_join = LPhiAssignment (x_final, [| Var x_rbind; Var x_rcall |]) in 

		let cmds = annotate_first_cmd (
			cmds_ef @ [                             (*        cmds_ef                                                                 *)
			(annotate_cmd cmd_gv_f None)            (*        x_f_val := i__getValue (x_f) with err                                   *)
		] @ annotate_first_call_cmd (
			cmds_args @ (annotate_cmds [            (*        cmds_arg_i; x_arg_i_val := i__getValue (x_arg_i) with err               *)
			(None,         cmd_goto_is_obj);        (*        goto [ typeOf(x_f_val) != Object] err next1                             *)
			(Some next1,   cmd_xfvm);               (*        xfvm := metadata(x_f_val)                                               *)
			(None,         cmd_hf_construct);       (* next1: x_hp := [xfvm, "@construct"];                                           *)
			(None,         cmd_goto_xhp);           (*        goto [ x_hp = empty ] err next2                                         *) ]

		@ (if_verification [] (annotate_cmds [

			(* PREP *)

			(Some get_bt,    cmd_get_bt);           (*        x_bt := [xfvm, "@boundTarget"];                                         *)
			(None,           cmd_bind_test);        (*        goto [x_bt = empty] call bind                                           *)

			(* BIND *)

			(Some bind,    cmd_get_ba);              (*         x_ba := [xfvm, "@boundArgs"];                                         *)
			(None,         cmd_get_tf);              (*         x_tf := [xfvm, "@targetFunction"];                                    *)
			(None,         cmd_xbthism);             (*         xobjm := new (null)                                                   *)
			(None,         cmd_bcreate_xobj);        (*         x_bthis := new (xobjm)                                                *)
			(None,         cmd_bass_xreffprototype); (*         x_bref_fprototype := ref-o(x_tf, "prototype")                         *)
			(None,         cmd_bgv_xreffprototype);  (*         x_bf_prototype := i__getValue(x_bref_prototype) with err              *)
			(None,         cmd_bis_object);          (*         goto [typeof (x_bf_prototype) = Obj] else1 then1;                     *)
			(Some bthen1,  cmd_bset_proto);          (* bthen1:	x_bwhyGodwhy := $lobj_proto                                           *)
			(Some belse1,  cmd_bproto_phi);          (* belse1: x_bprototype := PHI (x_bf_prototype, x_bwhyGodwhy)		                *)
			(None,         cmd_bcdo_call);           (*         x_bcdo := create_default_object (x_bthis, x_bprototype)               *)
			(None,         cmd_xtfm);                (*         xtfm := metadata(x_tf)                                                *)
			(None,         cmd_bbody);               (*         x_bbody := [xtfm, "@construct"];                                      *)
			(None,         cmd_bscope);              (*         x_fscope := [xtfm, "@scope"]                                          *) 
			(None,         cmd_append);              (*        SOMETHING ABOUT PARAMETERS                                             *)
			(None,         cmd_bind);                (*        MAGICAL FLATTENING CALL                                                *)
			(None,         cmd_bgoto_test_type);     (*        goto [typeOf(x_r1) = Obj ] next4 next3;                                *)
			(Some bnext3,  cmd_bret_this);           (* next3: skip                                                                   *)
			(Some bnext4,  cmd_bphi_final);          (* next4: x_rcall := PHI(x_r1, x_this)                                           *)
			(None,         cmd_sync);                (*        goto join                                                              *) ]))

		@ (annotate_cmds [ 
			(Some call,    cmd_xobjm);               (* next2: xthism := new (null)                                                   *)
			(None,         cmd_create_xobj);         (* next2: x_this := new (xthism)                                                 *)
			(None,         cmd_ass_xreffprototype);  (*        x_ref_fprototype := ref-o(x_f_val, "prototype")                        *)
			(None,         cmd_gv_xreffprototype);   (*        x_f_prototype := i__getValue(x_ref_prototype) with err                 *)
			(None,         cmd_is_object);           (*        goto [typeof (x_f_prototype) = Obj] else1 then1;                       *)
			(Some then1,   cmd_set_proto);           (* then1:	x_whyGodwhy := $lobj_proto                                            *)
			(Some else1,   cmd_proto_phi);         	 (* else1: x_prototype := PHI (x_f_prototype, x_whyGodwhy)		                    *)
			(None,         cmd_cdo_call);            (*        x_cdo := create_default_object (x_this, x_prototype)                   *)
			(None,         cmd_body);                (*        x_body := [xfvm, "@construct"]                                         *)
			(None,         cmd_scope);               (*        x_fscope := [xfvm, "@scope"]                                           *)
			(None,         cmd_proc_call);           (*        x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err *)
			(None,         cmd_goto_test_type);      (*        goto [typeOf(x_r1) = Obj ] next4 next3;                                *)
			(Some next3,   cmd_ret_this);            (* next3: skip                                                                   *)
			(Some next4,   cmd_phi_final);           (* next4: x_rcall := PHI(x_r1, x_this)                                           *) ])
		
		@ (if_verification [] (annotate_cmds [
			(Some join,    cmd_phi_join);            (*        x_final := PHI (x_rbind, x_rcall);                                       *) 
		]))))) in
		let errs = errs_ef @ errs_xf_val @ errs_args @ [ var_te; var_te ] @ (if_verification [] (errs_bf_prototype @ [ x_bconstruct ])) @ errs_xf_prototype @ [ x_r1 ] in
		cmds, Var (if_verification x_rcall x_final), errs


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
					end1: 	xfvm := metadata(x_f_val);
									x_body := [xfvm, "@call"];
		       				x_scope := [xfvm, "@scope"];
					 				x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err;
					 				goto [ x_r1 = empty ] next3 next4;
        	next3:  x_r2 := undefined;
					next4:  x_r3 := PHI(x_r1, x_r2)
		*)

		let cmds_ef, x_ef, errs_ef = f e_f in

		(* x_f_val := i__getValue (x_f) with err1;  *)
		let x_f_val, cmd_gv_f, errs_xf_val = make_get_value_call x_ef tr_ctx.tr_err in

		let cmds_args, x_args_gv, errs_args = translate_arg_list xes tr_ctx.tr_err in

		(* goto [ typeOf(x_f_val) != Object] err next1; err -> typeerror *)
		let next1 = fresh_next_label () in
		let goto_guard_expr = UnOp (Not, (BinOp (TypeOf (Var x_f_val), Equal, Literal (Type ObjectType)))) in
		let cmd_goto_is_obj = LGuardedGoto (goto_guard_expr, tr_ctx.tr_err, next1) in

		(* next1: x_ic := isCallable(x_f_val); *)
		let x_ic = fresh_var () in
		let cmd_ic = LCall (x_ic, Literal (String isCallableName), [ Var x_f_val ], None) in

		(* goto [ x_ic ] getbt err; -> typeerror *)

		let call = fresh_label () in
		let get_bt = fresh_next_label () in
		let jump = if_verification call get_bt in
		let cmd_goto_is_callable = LGuardedGoto (Var x_ic, jump, tr_ctx.tr_err) in

		let xfvm = fresh_var () in
		let cmd_xfvm = LBasic (MetaData (xfvm, Var x_f_val)) in

		let x_ibt = fresh_var () in
		let cmd_get_ibt = LBasic (HasField (x_ibt, Var xfvm, Literal (String "@boundThis"))) in

		let bind = fresh_else_label () in
		let goto_guard_expr = (Var x_ibt) in
		let cmd_bind_test = LGuardedGoto (goto_guard_expr, bind, call) in

		(* BIND *)

		let x_bt = fresh_var () in
		let cmd_get_bt = LBasic (Lookup (x_bt, Var xfvm, Literal (String "@boundThis"))) in

		let x_ba = fresh_var () in
		let cmd_get_ba = LBasic (Lookup (x_ba, Var xfvm, Literal (String "@boundArguments"))) in

		let x_tf = fresh_var () in
		let cmd_get_tf = LBasic (Lookup (x_tf, Var xfvm, Literal (String "@targetFunction"))) in

		(* xtfm := metadata (x_tf) *)
		let xtfm = fresh_var () in
		let cmd_xtfm = LBasic (MetaData (xtfm, Var x_tf)) in

		let x_bbody = fresh_body_var () in
		let cmd_bbody = LBasic (Lookup (x_bbody, Var xtfm, Literal (String _callPropName))) in

		let x_bfscope = fresh_fscope_var () in
		let cmd_bscope = LBasic (Lookup (x_bfscope, Var xtfm, Literal (String _scopePropName))) in

		let x_params = fresh_var () in
		let jsil_list_params = EList ([Var x_bbody; Var x_bfscope; Var x_bt]) in
		let cmd_append = LBasic (Assignment (x_params, (BinOp (BinOp (jsil_list_params, LstCat, Var x_ba), LstCat, (EList x_args_gv))))) in

		let x_rbind = fresh_var () in
		let cmd_bind = LApply (x_rbind, [ Var x_params ], Some tr_ctx.tr_err) in

		(* SYNC *)

		let join = fresh_label () in
		let cmd_sync = LGoto join in 

		(* join: goto [ typeOf(x_f) = ObjReference ] then else;  *)
		let then_lab = fresh_then_label () in
		let else_lab = fresh_else_label () in
		let end_lab = fresh_endif_label () in
		let goto_guard_expr = is_oref x_ef in
		let cmd_goto_obj_ref = LGuardedGoto (goto_guard_expr, then_lab, else_lab) in

		(* then: x_then_this := base(x_f); *)
		let x_this_then = fresh_this_var () in
		let cmd_this_base = LBasic (Assignment (x_this_then, base x_ef)) in

		(*  goto end; *)
		let cmd_goto_end = LGoto end_lab in

		(* else: x_else_this := undefined; *)
		let x_this_else = fresh_this_var () in
		let cmd_this_undefined = LBasic (Assignment (x_this_else, Literal Undefined)) in

		(* end: x_this := PHI(x_then_this, x_else_this) *)
		let x_this = fresh_this_var () in
		let cmd_ass_xthis = LPhiAssignment (x_this, [| (Var x_this_then); (Var x_this_else) |]) in

		(* x_body := [x_f_val, "@call"]; *)
		let x_body = fresh_body_var () in
		let cmd_body = LBasic (Lookup (x_body, Var xfvm, Literal (String _callPropName))) in

		(* x_fscope := [x_f_val, "@scope"]; *)
		let x_fscope = fresh_fscope_var () in
		let cmd_scope = LBasic (Lookup (x_fscope, Var xfvm, Literal (String _scopePropName))) in

		(* x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err  *)
		let x_rcall = fresh_var () in
		let proc_args = (Var x_fscope) :: (Var x_this) :: x_args_gv in
		let cmd_proc_call = LCall (x_rcall, (Var x_body), proc_args, Some tr_ctx.tr_err) in

		let x_r1 = fresh_var () in
		let cmd_phi_join = LPhiAssignment (x_r1, [| (Var x_rbind); (Var x_rcall) |]) in 

		(* goto [ x_r1 = empty ] next3 next4; *)
		let next3 = fresh_next_label () in
		let next4 = fresh_next_label () in
		let goto_guard_expr = BinOp (Var (if_verification x_rcall x_r1), Equal, Literal Empty) in
		let cmd_goto_test_empty = LGuardedGoto (goto_guard_expr, next3, next4) in

		(* next3: x_r2 := undefined; *)
		let x_r2 = fresh_var () in
		let cmd_ret_undefined = LBasic (Assignment (x_r2, Literal Undefined)) in

		(* next4: x_r3 := PHI(x_r1, x_r2) *)
		let x_r3 = fresh_var () in
		let cmd_phi_final = LPhiAssignment (x_r3, [| Var (if_verification x_rcall x_r1); Var x_r2 |]) in

		let cmds = annotate_first_cmd (
			cmds_ef @ [                             (*        cmds_ef                                                                   *)
			(annotate_cmd cmd_gv_f None)            (*        x_f_val := i__getValue (x_f) with err                                     *)
		] @ annotate_first_call_cmd (
			cmds_args @ (annotate_cmds [            (*        cmds_arg_i; x_arg_i_val := i__getValue (x_arg_i) with err                 *)
			(None,           cmd_goto_is_obj);      (*        goto [ typeOf(x_f_val) != Object] err next1                               *)
			(Some next1,     cmd_xfvm);             (* next1: xfvm := metadata(x_f_val)                                               *)
			(None,           cmd_ic);               (*        x_ic := isCallable(x_f_val)                                               *)
			(None,           cmd_goto_is_callable); (*        goto [ x_ic ] getbt err; -> typeerror                                     *) ]

		@ (if_verification [] (annotate_cmds [

			(* PREP *)

			
			(Some get_bt,    cmd_get_ibt);          (*        x_bt := [xfvm, "@boundTarget"];                                      *)
			(None,           cmd_bind_test);        (*        goto [x_bt = empty] call bind                                           *)

			(* BIND *)

			(Some bind,      cmd_get_bt);           (*        x_bt := [xfvm, "@boundThis"];                                          *)
			(None,           cmd_get_ba);           (*        x_ba := [xfvm, "@boundArgs"];                                          *)
			(None,           cmd_get_tf);           (*        x_tf := [xfvm, "@targetFunction"];                                     *)
			(None,           cmd_xtfm);             (*        xtfm := metadata(x_tf)                                                  *)
			(None,           cmd_bbody);            (*        x_bbody := [xtfm, "@call"];                                               *)
			(None,           cmd_bscope);           (*        x_fscope := [xtfm, "@scope"]                                              *)

			(None,           cmd_append);           (*        SOMETHING ABOUT PARAMETERS                                                *)
			(None,           cmd_bind);             (*        MAGICAL FLATTENING CALL                                                   *)
			(None,           cmd_sync);             (*        goto join                                                                 *) ]))

			(* CALL *)

		@ annotate_cmds [
			(Some call,      cmd_goto_obj_ref);     (* next2: goto [ typeOf(x_f) = ObjReference ] then else                             *)
			(Some then_lab,  cmd_this_base);        (* then:  x_then_this := base(x_f)                                                  *)
			(None,           cmd_goto_end);         (*        goto end                                                                  *)
			(Some else_lab,  cmd_this_undefined);   (* else:  x_else_this := undefined                                                  *)
			(Some end_lab,   cmd_ass_xthis);        (* end:   x_this := PHI(x_then_this, x_else_this)                                   *)
			(None,           cmd_body);             (*        x_body := [xfvm, "@call"]                                              *)
			(None,           cmd_scope);            (*        x_fscope := [xfvm, "@scope"]                                           *)
			(None,           cmd_proc_call);        (*        x_rcall := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err *) ]

		@ (if_verification [] (annotate_cmds [

			(* JOIN *)

			(Some join,      cmd_phi_join);         (*        x_r1 := PHI (x_rbind, x_rcall);                                           *) ]))

		@ annotate_cmds [
			(None,           cmd_goto_test_empty);  (*        goto [ x_r1 = empty ] next3 next4                                       *)
			(Some next3,     cmd_ret_undefined);    (* next3: x_r2 := undefined                                                       *)
			(Some next4,     cmd_phi_final)         (* next4: x_r3 := PHI(x_r1, x_r2)                                                   *)
		]))) in
		let errs = errs_ef @ errs_xf_val @ errs_args @ [ var_te; var_te ] @ (if_verification [] [ x_rbind ]) @ [ x_rcall ] in
		cmds, Var x_r3, errs



	| Parser_syntax.Unary_op (Parser_syntax.Post_Incr, e) ->
		(**
      Section: 11.3.1
      C(e) = cmds, x

			C(e++) =
					cmds
			    	goto [ (typeof (x) = $$v-reference_type) and ((field(x) = "eval") or (field(x) = "arguments")) ] err next
			 next:  x_v := i__getValue (x) with err
					x_n := i__toNumber (x_v) with err
					x_r := x_n + 1
					x_pv := putValue (x, x_r) with err;
     *)
		let cmds, x, errs = f e in
	 	let new_cmds, new_errs, x_v, x_r = translate_inc_dec x true tr_ctx.tr_err in
		let new_cmds = annotate_cmds new_cmds in
		(annotate_first_cmd (cmds @ new_cmds)), Var x_v, (errs @ new_errs)


	| Parser_syntax.Unary_op (Parser_syntax.Post_Decr, e) ->
		(**
      Section: 11.3.2
      C(e) = cmds, x

			C(e--) =
					cmds
			        goto [ (typeof (x) = $$v-reference_type) and ((field(x) = "eval") or (field(x) = "arguments")) ] err next
			 next:  x_v := i__getValue (x) with err
					x_n := i__toNumber (x_v) with err
					x_r := x_n - 1
					x_pv := putValue (x, x_r) with err
     *)
		let cmds, x, errs = f e in
	 	let new_cmds, new_errs, x_v, x_r = translate_inc_dec x false tr_ctx.tr_err in
		let new_cmds = annotate_cmds new_cmds in
		(annotate_first_cmd (cmds @ new_cmds)), Var x_v, (errs @ new_errs)


	| Parser_syntax.Delete e ->
		(**
			Section: 11.4.1
			C(e) = cmds, x
			C(delete e) =
			       cmds
			       goto [ (is-ref x) ] next1 next4
			next1: goto [ ((base(x) = null) or (base(x) = undefined)) ] err next2
			next2: goto [ (typeOf x) = $$v-reference_type ] err next3
			next3: x_obj := toObject(base(x)) with err
				   x_r1 := deleteProperty(x_obj, field(x), true) with err
				   goto next5
			next4: x_r2 := true
			next5: x_r := PHI(x_r1; x_r2)
        *)

		let cmds, x, errs = f e in

		(* goto [ (typeOf x) <: $$reference_type ] next1 next4 *)
		let next1 = fresh_next_label () in
		let next2 = fresh_next_label () in
		let next3 = fresh_next_label () in
		let next4 = fresh_next_label () in
		let goto_guard = is_ref x in
		let cmd_goto_isref = LGuardedGoto (goto_guard, next1, next4) in

		(* next1: goto [ ((base(x) = null) or (base(x) = undefined)) ] err next2 *)
		let cmd_goto_is_resolvable_ref = LGuardedGoto (make_unresolvable_ref_test x , tr_ctx.tr_err, next2) in

		(* next2: goto [ (typeOf x) = $$v-reference_type ] err next3 *)
		let goto_guard = is_vref x in
		let cmd_goto_is_vref = LGuardedGoto (goto_guard, tr_ctx.tr_err, next3) in

		(* next3: x_obj := toObject(base(x)) err *)
		let x_obj = fresh_obj_var () in
		let cmd_to_obj = LCall (x_obj, lit_str toObjectName, [ (base x) ], Some tr_ctx.tr_err) in

		(* x_r1 := deleteProperty(x_obj, field(x), true) with err *)
		let x_r1 = fresh_var () in
		let cmd_delete = LCall (x_r1, lit_str deletePropertyName,
			[ (Var x_obj); (field x); (Literal (Bool true)) ], Some tr_ctx.tr_err) in

		let x_r2 = fresh_var () in
		let x_r = fresh_var () in
		let next5 = fresh_next_label () in
		let cmds = annotate_first_cmd (
			cmds @ (annotate_cmds [                                                     (*        cmds                                                                     *)
			(None,       cmd_goto_isref);                                               (*        goto [ (typeOf x) <: $$reference_type ] next1 next4                      *)
			(Some next1, cmd_goto_is_resolvable_ref);                                   (* next1: goto [ ((base(x_e) = null) or (base(x_e) = undefined)) ] err next2   *)
			(Some next2, cmd_goto_is_vref);                                             (* next2: goto [ (typeOf x) = $$v-reference_type ] err next3                       *)
			(Some next3, cmd_to_obj);                                                   (* next3: x_obj := toObject(base(x)) err3                                          *)
			(None,       cmd_delete);                                                   (*        x_r1 := deleteProperty(x_obj, field(x), true) with err                    *)
			(None,       LGoto next5);                                                 (*        goto next5                                                               *)
			(Some next4, LBasic (Assignment (x_r2, Literal (Bool true))));            (* next4: x_r2 := true                                                              *)
			(Some next5, LPhiAssignment (x_r, [| (Var x_r1); (Var x_r2) |]))           (* next5: x_r := PHI(x_r1, x_r2)                                                   *)
		])) in
		let errs = errs @ [ var_se; var_se; x_obj; x_r1 ] in
		cmds, Var x_r, errs


	| Parser_syntax.Unary_op (Parser_syntax.Void, e) ->
	  (** Section: 11.4.2
      	C(e) = cmds, x
	  	C(void e) =
	  				cmds
			        x_v := getValue (x) with err
					x_r := undefined
       *)
		let cmds, x, errs = f e in
		(* x_v := getValue (x) with err *)
		let x_v, cmd_gv_x, errs_x_v = make_get_value_call x tr_ctx.tr_err in
		let x_r = fresh_var () in
		let cmds = annotate_first_cmd ( cmds @ (annotate_cmds [        (*  cmds                                *)
			(None, cmd_gv_x);                                          (*  x_v := getValue (x) with err        *)
			(None, LBasic (Assignment (x_r, Literal Undefined)));    (*  x_r := undefined                  *)
		])) in
		let errs = errs @ errs_x_v in
		cmds, Var x_r, errs


	| Parser_syntax.Unary_op (Parser_syntax.TypeOf, e) ->
	  (** Section: 11.4.3
		C(e) =  cmds, x
		C(typeof e) =
						cmds
		                goto [ is-ref(typeof (x)) ] next1 next4
			   next1:   goto [ ((base(x) = null) or (base(x) = undefined)) ] next2 next3
			   next2:   x1 := undefined
					    goto next4
			   next3:   x2 := getValue (x) with err
			   next4:   x3 := PHI (x, x1, x2)
					    x_r := i__typeOf (x3) with err
      *)

		let cmds, x, errs = f e in
		let cmds, x_name = add_final_var cmds x metadata in

		(* goto [ is-ref(typeof (x)) ] next1 next4 *)
		let next1 = fresh_next_label () in
		let next2 = fresh_next_label () in
		let next3 = fresh_next_label () in
		let next4 = fresh_next_label () in
		let cmd_goto_ref_guard = is_ref x in
		let cmd_goto_ref = LGuardedGoto (cmd_goto_ref_guard, next1, next4) in

		(* goto [ ((base(x_e) = null) or (base(x_e) = undefined)) ] next2 next3 *)
		let cmd_goto_unres_ref = LGuardedGoto (make_unresolvable_ref_test x, next2, next3) in

		(* x2 := getValue (x) with err *)
		let x1 = fresh_var () in
		let x2 = fresh_var () in
		let cmd_gv_x = LCall (x2, (Literal (String getValueName)), [ x ], Some tr_ctx.tr_err) in

		(* x_r := i__typeOf (x3) with err *)
		let x3 = fresh_var () in
		let x_r = fresh_var () in
		let cmd_ass_xr = LCall (x_r, (Literal (String jsTypeOfName)), [ Var x3 ], Some tr_ctx.tr_err) in

		let cmds = annotate_first_cmd (
		    cmds @ (annotate_cmds [                                                              (*             cmds                                                  *)
			(None, cmd_goto_ref);                                                                (*             goto [ typeof (x) <: $$reference-type ] next1 next4   *)
			(Some next1, cmd_goto_unres_ref);                                                    (* next1:      goto [ base(x) = undefined] next2 next3               *)
			(Some next2, LBasic (Assignment (x1, Literal Undefined)));                         (* next2:      x1 := undefined                                     *)
			(None,       LGoto next4);                                                          (*             goto next4                                            *)
			(Some next3, cmd_gv_x);                                                              (* next3:      x2 := getValue (x) with err                           *)
			(Some next4, LPhiAssignment (x3, [| (Var x_name); (Var x1); (Var x2) |]));          (* next4:      x3 := PHI (x, x1, x2)                                 *)
			(None,       cmd_ass_xr)                                                             (*             x_r := i__typeOf (x3) with err                        *)
		])) in
		let errs = errs @ [ x2; x_r ] in
		cmds, Var x_r, errs


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
		let cmds, x, errs = f e in
	 	let new_cmds, new_errs, x_v, x_r = translate_inc_dec x true tr_ctx.tr_err in
		let new_cmds = annotate_cmds new_cmds in
		(annotate_first_cmd (cmds @ new_cmds)), Var x_r, (errs @ new_errs)


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
	  	let cmds, x, errs = f e in
	 	let new_cmds, new_errs, x_v, x_r = translate_inc_dec x false tr_ctx.tr_err in
		let new_cmds = annotate_cmds new_cmds in
		annotate_first_cmd (cmds @ new_cmds), Var x_r, (errs @ new_errs)


	| Parser_syntax.Unary_op (Parser_syntax.Positive, e) ->
		(**
			Section: 11.4.6
      C(e) = cmds, x
			C(+e) =  cmds
			         x_v := i__getValue (x) with err
							 x_n := i__toNumber (x_v) with err
     *)
		let cmds, x, errs = f e in

		(* x_v := i__getValue (x) with err *)
		let x_v, cmd_gv_x, errs_x_v = make_get_value_call x tr_ctx.tr_err in

		(* x_n := i__toNumber (x_v) with err *)
		let x_n, cmd_tn_x = make_to_number_call x x_v tr_ctx.tr_err in

		let cmds = annotate_first_cmd (
			cmds @ (annotate_cmds [          (*  cmds                                *)
			(None, cmd_gv_x);                (*  x_v := i__getValue (x) with err     *)
			(None, cmd_tn_x);                (*  x_n := i__toNumber (x_v) with err   *)
		])) in
		let errs = errs @ errs_x_v @ [ x_n ] in
		cmds, Var x_n, errs


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
		let cmds, x, errs = f e in

		(* x_v := getValue (x) with err *)
		let x_v, cmd_gv_x, errs_x_v = make_get_value_call x tr_ctx.tr_err in

		(* x_n := i__toNumber (x_v) with err *)
		let x_n, cmd_tn_x = make_to_number_call x x_v tr_ctx.tr_err in

		(* goto [x_n = nan] then else *)
		let then_lab = fresh_then_label () in
		let else_lab = fresh_else_label () in
		let end_lab = fresh_endif_label () in
		let cmd_goto_nan = LGuardedGoto (BinOp (Var x_n, Equal, Literal (Num nan)), then_lab, else_lab) in

		(* then: x_then := nan *)
		let x_then = fresh_var () in
		let cmd_ass_xthen = LBasic (Assignment (x_then, Literal (Num nan))) in

		(* else: x_else := (negative x_n) *)
		let x_else = fresh_var () in
		let cmd_ass_xelse = LBasic (Assignment (x_else, UnOp (UnaryMinus, (Var x_n)))) in

		(* end:  x_r := PHI(x_then, x_else) *)
		let x_r = fresh_var () in
		let cmd_ass_xr = LPhiAssignment (x_r, [| (Var x_then); (Var x_else) |]) in

		let cmds = annotate_first_cmd (
		    cmds @ (annotate_cmds [                 (*            cmds                                *)
			(None,          cmd_gv_x);              (*            x_v := i__getValue (x) with err     *)
			(None,          cmd_tn_x);              (*            x_n := i__toNumber (x_v) with err   *)
			(None,          cmd_goto_nan);          (*            goto [x_n = nan] then else          *)
			(Some then_lab, cmd_ass_xthen);         (* then:      x_then := nan                       *)
			(None,          LGoto end_lab);        (*            goto end                            *)
			(Some else_lab, cmd_ass_xelse);         (* else:      x_else := (negative x_n)            *)
			(Some end_lab,  cmd_ass_xr)             (* end:       x_r := PHI(x_then, x_else)          *)
		])) in
		let errs = errs @ errs_x_v @ [ x_n ] in
		cmds, Var x_r, errs


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

		let cmds, x, errs = f e in

		(* x_v := i__getValue (x) with err *)
		let x_v, cmd_gv_x, errs_x_v = make_get_value_call x tr_ctx.tr_err in

		(* x_n := i__toNumber (x_v) with err *)
		let x_n, cmd_tn_x = make_to_number_call x x_v tr_ctx.tr_err in

		let x_r = fresh_var () in
		let x_i32 = fresh_var () in
		let cmds = annotate_first_cmd (
		    cmds @ (annotate_cmds [                                                  (*  cmds                                *)
			(None, cmd_gv_x);                                                        (*  x_v := i__getValue (x) with err     *)
			(None, cmd_tn_x);                                                        (*  x_n := i__toNumber (x_v) with err   *)
			(None, LBasic (Assignment (x_i32, UnOp (ToInt32Op, Var x_n))));        (*  x_i32 := (num_to_int32 x_n)         *)
			(None, LBasic (Assignment (x_r, UnOp (BitwiseNot, Var x_i32))))        (*  x_r := (! x_i32)                    *)
		])) in
		let errs = errs @ errs_x_v @ [ x_n ] in
		cmds, Var x_r, errs


	| Parser_syntax.Unary_op (Parser_syntax.Not, e) ->
		(**
      Section: 11.4.9
	  	C(e)  =  cmds, x
	   	C(!e) =  cmds
			         x_v := i__getValue (x) with err
				   	   x_b := i__toBoolean (x_v) with err
						   x_r := not x_b
     *)

		let cmds, x, errs = f e in

		(* x_v := i__getValue (x) with err1 *)
		let x_v, cmd_gv_x, errs_x_v = make_get_value_call x tr_ctx.tr_err in

		(* x_b := i__toBoolean (x_v) with err2 *)
		let x_b, cmd_tb_x = make_to_boolean_call x x_v tr_ctx.tr_err in

		(*  x_r := (not x_b)   *)
		let x_r = fresh_var () in
		let cmd_xr_ass = LBasic (Assignment (x_r, UnOp (Not, Var x_b))) in

		let cmds = annotate_first_cmd (
		    cmds @ (annotate_cmds [            (* cmds                               *)
			(None, cmd_gv_x);                  (* x_v := i__getValue (x) with err    *)
			(None, cmd_tb_x);                  (* x_b := i__toBoolean (x_v) with err *)
			(None, cmd_xr_ass);                (* x_r := (not x_b)                   *)
		])) in
		let errs = errs @ errs_x_v @ [ x_b ] in
		cmds, Var x_r, errs


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
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r = translate_multiplicative_binop x1 x2 x1_v x2_v aop tr_ctx.tr_err in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2 @ (annotate_cmds ([ (None, cmd_gv_x2) ] @ new_cmds))) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r, errs


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
											      goto [((typeOf x1_p) = Str) or ((typeOf x2_p) = Str)] then else
									    then: x1_s := i__toString (x1_p) with err
											      x2_s := i__toString (x2_p) with err
														x_rthen := x1_s :: x2_s
														goto end
										  else: x1_n := i__toNumber (x1_p) with err
											      x2_n := i__toNumber (x2_p) with err
														x_relse := x1_n + x2_n
											end:  x_r := PHI (x_rthen, x_relse)
		*)

		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r = translate_binop_plus x1 x2 x1_v x2_v tr_ctx.tr_err in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2 @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds)) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r, errs


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
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r = translate_bitwise_shift x1 x2 x1_v x2_v toInt32Name toUInt32Name LeftShift tr_ctx.tr_err in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2 @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds)) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r, errs


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
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r = translate_bitwise_shift x1 x2 x1_v x2_v toInt32Name toUInt32Name SignedRightShift tr_ctx.tr_err in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2 @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds)) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r, errs


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
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r = translate_bitwise_shift x1 x2 x1_v x2_v toUInt32Name toUInt32Name UnsignedRightShift tr_ctx.tr_err in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2 @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds)) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r, errs


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
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r = translate_binop_comparison x1 x2 x1_v x2_v true true false tr_ctx.tr_err in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2  @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds)) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r, errs


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
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r = translate_binop_comparison x1 x2 x1_v x2_v false false false tr_ctx.tr_err in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2 @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds)) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r, errs


	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.Le), e2) ->
	  (**
      Section 11.8.3
      C(e1) = cmds1, x1; C(e2) = cmds2, x2
			C(e1 <= e2) =
					cmds1
				    x1_v := i__getValue (x1) with err
				    cmds2
					x2_v := i__getValue (x2) with err
					x_ac := i__abstractComparison (x2_v, x1_v, false) with err
					goto [ x_ac = undefined] then end
			 then:  x_undef := true
			 end:   x_r1 := PHI(x_ac, x_undef)
					x_r2 := (not x_r1)
     *)
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r1 = translate_binop_comparison x1 x2 x1_v x2_v false false true tr_ctx.tr_err in
		let x_r2 = fresh_var () in
		let new_cmd = LBasic (Assignment (x_r2, UnOp (Not, (Var x_r1)))) in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2 @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds) @ [ annotate_cmd new_cmd None ]) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r2, errs


	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.Ge), e2) ->
	  (**
      Section 11.8.4
      C(e1) = cmds1, x1; C(e2) = cmds2, x2
			C(e1 >= e2) =
				cmds1
				x1_v := i__getValue (x1) with err
				cmds2
				x2_v := i__getValue (x2) with err
				x_ac := i__abstractComparison (x1_v, x2_v, true) with err
			    goto [ x_ac = undefined] then end
		 then:  x_undef := true
		 end:   x_r1 := PHI(x_ac, x_undef)
				x_r2 := (not x_r1)
      *)
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r1 = translate_binop_comparison x1 x2 x1_v x2_v true true true tr_ctx.tr_err in
		let x_r2 = fresh_var () in
		let new_cmd = LBasic (Assignment (x_r2, UnOp (Not, (Var x_r1)))) in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2 @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds) @ [ annotate_cmd new_cmd None ]) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r2, errs


	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.InstanceOf), e2) ->
	  (**
      Section 11.8.6
      C(e1) = cmds1, x1; C(e2) = cmds2, x2
			C(e1 instanceof e2) =
				cmds1
			    x1_v := i__getValue (x1) with err
				cmds2
				x2_v := i__getValue (x2) with err
				goto [ (typeOf x2_v) = Obj ] next1 err
		next1:  x_cond := [x2_v, "@hasInstance"];
				goto [ x_cond = empty ] err next2
		next2:  x_hi := [x2_v, "@hasInstance"]
				x_r := x_hi (x2_v, x1_v) with err
     *)
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in

		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		(* goto [ (typeOf x2_v) = Obj ] next1 err *)
		let next1 = fresh_label () in
		let cmd_goto_ot = LGuardedGoto (BinOp (TypeOf (Var x2_v), Equal, Literal (Type ObjectType)), next1, tr_ctx.tr_err) in

		(* get the metadata *)
		let x2vm = fresh_var () in
		let cmd_x2vm = LBasic (MetaData (x2vm, Var x2_v)) in

		(* next1: x_cond := hasField (x2_v, "@hasInstance")  *)
		let x_cond = fresh_var () in
		let cmd_hasfield = LBasic (Lookup (x_cond, Var x2vm, Literal (String "@class"))) in

		(* goto [ x_cond = empty ] err next2 *)
		let next2 = fresh_label () in
		let cmd_goto_xcond = LGuardedGoto (BinOp (Var x_cond, Equal, Literal (String "Function")), next2, tr_ctx.tr_err) in

		(* x_r := x_hi (x2_v, x1_v) with err *)
		let x_r = fresh_var () in
		let cmd_ass_xr = LCall (x_r, Literal (String "hasInstance"), [Var x2_v; Var x1_v], Some tr_ctx.tr_err) in

		let cmds = annotate_first_cmd (
			cmds1 @ [                           (*        cmds1                                     *)
			annotate_cmd cmd_gv_x1 None         (*        x1_v := i__getValue (x1) with err         *)
		] @ cmds2 @ (annotate_cmds [          (*        cmds2                                     *)
			(None,         cmd_gv_x2);          (*        x2_v := i__getValue (x2) with err         *)
			(None,         cmd_goto_ot);        (*        goto [ (typeOf x2_v) = Obj ] next1 err    *)
			(Some next1,   cmd_x2vm);           (* next1: x2vm := metadata(x2_v)                    *)
			(None,         cmd_hasfield);       (*        x_cond := hasField (x2_v, "@hasInstance") *)
			(None,         cmd_goto_xcond);     (*        goto [ x_cond = empty ] err next2         *)
			(Some next2,   cmd_ass_xr)          (*        x_r := x_hi (x2_v, x1_v) with err         *)
		])) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ [ var_te; var_te; x_r ] in
		cmds, Var x_r, errs


	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.In), e2) ->
	  (**
      Section 11.8.7
      C(e1) = cmds1, x1; C(e2) = cmds2, x2
			C(e1 in e2) =
					cmds1
			    	x1_v := i__getValue (x1) with err
					cmds2
					x2_v := i__getValue (x2) with err
					goto [ (typeOf x2_v) = Obj ] next1 err
			next1:  x1_s := i__toString (x1_v) with err
					x_r := o__hasProperty (x2_v, x1_s) with err
     *)
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in

		(* x2_v := getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		(* goto [ (typeOf x2_v) = Obj ] next1 err *)
		let next1 = fresh_label () in
		let cmd_goto_ot = LGuardedGoto (BinOp (TypeOf (Var x2_v), Equal, Literal (Type ObjectType)), next1, tr_ctx.tr_err) in

		(* next1: x1_s := i__toString (x1_v) with err   *)
		let x1_s, cmd_ts_x1 = make_to_string_call x1 x1_v tr_ctx.tr_err in

		(*  x_r := o__hasProperty (x2_v, x1_s) with err   *)
		let x_r = fresh_var () in
		let cmd_ass_xr = LCall (x_r, (Literal (String hasPropertyName)), [ Var x2_v; Var x1_s ], Some tr_ctx.tr_err) in

		let cmds = annotate_first_cmd (
			cmds1 @ [                           (*         cmds1                                             *)
			annotate_cmd cmd_gv_x1 None         (*         x1_v := getValue (x1) with err                    *)
		] @ cmds2 @ (annotate_cmds [            (*         cmds2                                             *)
			(None,         cmd_gv_x2);          (*         x2_v := getValue (x2) with err                    *)
			(None,         cmd_goto_ot);        (*         goto [ (typeOf x2_v) = Obj ] next1 err  *)
			(Some next1,   cmd_ts_x1);          (* next1:  x1_s := i__toString (x1_v) with err               *)
			(None,         cmd_ass_xr);         (*         x_r := o__hasProperty (x2_v, x1_s) with err       *)
		])) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ [ var_te; x1_s; x_r ] in
		cmds, Var x_r, errs


	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.Equal), e2) ->
	  (**
      Section 11.9.1
      C(e1) = cmds1, x1; C(e2) = cmds2, x2
			C(e1 == e2) =
				cmds1
				x1_v := i__getValue (x1) with err
				cmds2
				x2_v := i__getValue (x2) with err
				x_r := i__abstractEqualityComparison (x1_v, x2_v) with err
     *)
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r = translate_binop_equality x1 x2 x1_v x2_v true true tr_ctx.tr_err in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2 @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds)) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r, errs


	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.NotEqual), e2) ->
	  (**
      Section 11.9.2
      C(e1) = cmds1, x1; C(e2) = cmds2, x2
			C(e1 != e2) =
				cmds1
			    x1_v := i__getValue (x1) with err
				cmds2
				x2_v := i__getValue (x2) with err
				x_r1 := i__abstractEqualityComparison (x1_v, x2_v) with err
				x_r2 := (not x_r1)
     *)
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r = translate_binop_equality x1 x2 x1_v x2_v true false tr_ctx.tr_err in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2 @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds)) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r, errs


	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.TripleEqual), e2) ->
	  (**
      Section 11.9.4
      C(e1) = cmds1, x1; C(e2) = cmds2, x2
			C(e1 === e2) =
				cmds1
				x1_v := i__getValue (x1) with err
				cmds2
				x2_v := i__getValue (x2) with err
				x_r := i__strictEqualityComparison (x1_v, x2_v) with err
     *)
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r = translate_binop_equality x1 x2 x1_v x2_v false true tr_ctx.tr_err in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None] @ cmds2 @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds)) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r, errs


	| Parser_syntax.BinOp (e1, (Parser_syntax.Comparison Parser_syntax.NotTripleEqual), e2) ->
	  (**
      Section 11.9.5
      C(e1) = cmds1, x1; C(e2) = cmds2, x2
	  	C(e1 !== e2) =
	  			cmds1
				x1_v := i__getValue (x1) with err
				cmds2
				x2_v := i__getValue (x2) with err
				x_r1 := i__strictEqualityComparison (x1_v, x2_v) with err
				x_r2 := (not x_r1)
     *)
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r = translate_binop_equality x1 x2 x1_v x2_v false false tr_ctx.tr_err in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2 @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds)) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r, errs


	| Parser_syntax.BinOp (e1, (Parser_syntax.Arith bbop), e2)
		when ((bbop = Parser_syntax.Bitand) || (bbop = Parser_syntax.Bitor) || (bbop = Parser_syntax.Bitxor)) ->
	  (**
      Section 11.10
      C(e1) = cmds1, x1; C(e2) = cmds2, x2
			C(e1 == e2) =
				cmds1
				x1_v := i__getValue (x1) with err
				cmds2
				x2_v := i__getValue (x2) with err
				x1_i32 := i__toInt32 (x1_v) with err
				x2_i32 := i__toInt32 (x2_v) with err
				x_r := (x1_i32 bbop x2_i32)
     *)
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r = translate_bitwise_bin_op x1 x2 x1_v x2_v bbop tr_ctx.tr_err in
		let cmds = annotate_first_cmd (cmds1 @ [ annotate_cmd cmd_gv_x1 None ] @ cmds2 @ [ annotate_cmd cmd_gv_x2 None ] @ (annotate_cmds new_cmds)) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ new_errs in
		cmds, Var x_r, errs


	| Parser_syntax.BinOp (e1, (Parser_syntax.Boolean lbop), e2) ->
		(**
      Section 11.11
      C(e1) = cmds1, x1; C(e2) = cmds2, x2
			C(e1 && e2) =
				  cmds1
				  x1_v := i__getValue (x1) with err1
				  x1_b := i__toBoolean (x1_v) with err2
			      goto [x1_b] next end
		    next: cmds2
				  x2_v := i__getValue (x2) with err3
			end:  x_r := PHI(x1_v, x2_v)
     *)
		 translate_bin_logical_operator e1 e2 lbop tr_ctx.tr_err

	| Parser_syntax.ConditionalOp (e1, e2, e3) ->
		(**
      Section 11.12
      C(e1) = cmds1, x1; C(e2) = cmds2, x2; C(e3) = cmds3, x3
			C(e1 ? e2 : e3) =
					cmds1
					x1_v := i__getValue (x1) with err
					x1_b := i__toBoolean (x1_v) with err
				    goto [x1_b] then else
			 then:  cmds2
					x2_v := i__getValue (x2) with err
					goto end_if
			 else:  cmds3
					x3_v := i__getValue (x3) with err
					end_if:  x_r := PHI(x2_v, x3_v)
     *)
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in
		let cmds3, x3, errs3 = f e3 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x1_b := i__toBoolean (x1_v) with err  *)
		let x1_b, cmd_tb_x1 = make_to_boolean_call x1 x1_v tr_ctx.tr_err in
		(* goto [x1_b] then else *)
		let then_lab = fresh_then_label () in
		let else_lab = fresh_else_label () in
		let end_if_lab = fresh_endif_label () in
		let cmd_goto = LGuardedGoto (Var x1_b, then_lab, else_lab) in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in
		(* x3_v := i__getValue (x3) with err *)
		let x3_v, cmd_gv_x3, errs_x3_v = make_get_value_call x3 tr_ctx.tr_err in
		(* x_r := PHI(x2_v, x3_v) *)
		let x_r = fresh_var () in
		let cmd_ass_xr = LPhiAssignment (x_r, [| (Var x2_v); (Var x3_v) |]) in

		let cmds2 = add_initial_label cmds2 then_lab metadata in
		let cmds3 = add_initial_label cmds3 else_lab metadata in
		let cmds = annotate_first_cmd (
			cmds1 @ (annotate_cmds [      (*         cmds1                                              *)
			(None,            cmd_gv_x1);        (*         x1_v := i__getValue (x1) with err                  *)
			(None,            cmd_tb_x1);        (*         x1_b := i__toBoolean (x1_v) with err               *)
			(None,            cmd_goto)          (*         goto [x1_b] then else                              *)
		]) @ cmds2 @ (annotate_cmds [            (* then:   cmds2                                              *)
			(None,            cmd_gv_x2);        (*         x2_v := i__getValue (x2) with err                  *)
			(None,            LGoto end_if_lab) (*         goto end_if                                        *)
		]) @ cmds3 @ (annotate_cmds [            (* else:   cmds3                                              *)
			(None,            cmd_gv_x3);        (*         x3_v := i__getValue (x3) with err                  *)
			(Some end_if_lab, cmd_ass_xr)        (* end_if: x_r := PHI(x2_v, x3_v)                             *)
		])) in

		let errs = errs1 @ errs_x1_v @ [ x1_b ] @ errs2 @ errs_x2_v @ errs3 @ errs_x3_v in
		cmds, Var x_r, errs


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

		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		(*  x_cae := i__checkAssignmentErrors (x1) with err *)
		let x_cae, cmd_cae_x1 = make_cae_call x1 tr_ctx.tr_err in

		(* x_pv = i__putValue (x1, x2_v) with err *)
		let x_pv, cmd_put_value = make_put_value_call x1 x2_v tr_ctx.tr_err in

		let cmds = annotate_first_cmd (
			cmds1 @                             (*   cmds1                                           *)
			cmds2 @	(annotate_cmds [            (*   cmds2                                           *)
			(None, cmd_gv_x2);                  (*   x2_v := i__getValue (x2) with err               *)
			(None, cmd_cae_x1);                 (*   x_cae := i__checkAssertionErrors (x1) with err  *)
			(None, cmd_put_value)               (*   x_pv := i__putValue (x1, x2_v) with err         *)
		])) in

		let cmds =  cmds in
		let errs = errs1 @ errs2 @ errs_x2_v @ [ x_cae; x_pv ] in
		cmds, (Var x2_v), errs


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
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let new_cmds, new_errs, x_r =
			(match op with
			| Parser_syntax.Plus -> translate_binop_plus x1 x2 x1_v x2_v tr_ctx.tr_err
			| Parser_syntax.Minus
			| Parser_syntax.Times
			| Parser_syntax.Div
			| Parser_syntax.Mod -> translate_multiplicative_binop x1 x2 x1_v x2_v op tr_ctx.tr_err
			| Parser_syntax.Ursh -> translate_bitwise_shift x1 x2 x1_v x2_v toUInt32Name toUInt32Name SignedRightShift tr_ctx.tr_err
			| Parser_syntax.Lsh -> translate_bitwise_shift x1 x2 x1_v x2_v toInt32Name toUInt32Name LeftShift tr_ctx.tr_err
			| Parser_syntax.Rsh -> translate_bitwise_shift x1 x2 x1_v x2_v toInt32Name toUInt32Name UnsignedRightShift tr_ctx.tr_err
			| Parser_syntax.Bitand
      		| Parser_syntax.Bitor
      		| Parser_syntax.Bitxor -> translate_bitwise_bin_op x1 x2 x1_v x2_v op tr_ctx.tr_err) in

		(* x_cae := i__checkAssertionErrors (x1) with err *)
		let x_cae, cmd_cae_x1 = make_cae_call x1 tr_ctx.tr_err in

		(* x_pv = i__putValue (x1, x_r) with err *)
		let x_pv, cmd_pv = make_put_value_call x1 x_r tr_ctx.tr_err in

		let cmds = annotate_first_cmd (
			cmds1 @ [                      (*    cmds1                                           *)
			annotate_cmd cmd_gv_x1 None    (*    x1_v := i__getValue (x1) with err               *)
		] @ cmds2 @ [                      (*    cmds2                                           *)
			annotate_cmd cmd_gv_x2 None    (*    x2_v := i__getValue (x2) with err               *)
		] @ (annotate_cmds (new_cmds @ [   (*    new_cmds                                        *)
			(None, cmd_cae_x1);            (*    x_cae := i__checkAssertionErrors (x1) with err  *)
			(None, cmd_pv)                 (*    x_pv = putValue (x1, x2_v) with err             *)
		]))) in
		let errs = errs1 @  errs_x1_v @ errs2 @ errs_x2_v @ new_errs @ [ x_cae; x_pv ] in
		cmds, (Var x_r), errs


	| Parser_syntax.Comma (e1, e2) ->
		(**
      Section 11.14 - Comma Operator
			C(e1) = cmds1, x1; C(e2) = cmds2, x2
			C(e1, e2) =    cmds1
			               x1_v := i__getValue (x1) with err
			               cmds2
			               x2_v := i__getValue (x2) with err
     *)
		let cmds1, x1, errs1 = f e1 in
		let cmds2, x2, errs2 = f e2 in

		(* x1_v := getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in

		(* x2_v := getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		let cmds = annotate_first_cmd (
			cmds1 @ [                           (*       cmds1                                *)
				annotate_cmd cmd_gv_x1 None     (*       x1_v := i__getValue (x1) with err    *)
			] @ cmds2 @ [                       (*       cmds2                                *)
				annotate_cmd cmd_gv_x2 None     (*       x2_v := i__getValue (x2) with err    *)
			]) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v in
		cmds, (Var x2_v), errs


	| Parser_syntax.FunctionExp (_, None, params, e_body) ->
		(**
       Section 13
		   x_f := create_function_object(x_sc, f_id, f_id, params)
   	*)
		let f_id = try JS2JSIL_Preprocessing.get_codename e
			with _ -> raise (Failure "anonymous function literals should be annotated with their respective code names") in
	  let x_f, cmd = make_create_function_object_call tr_ctx.tr_sc_var f_id params in
		let cmds =  annotate_first_cmd ([ annotate_cmd cmd None ]) in
		cmds, Var x_f, []

	| Parser_syntax.FunctionExp (_, Some f_name, params, _)
	| Parser_syntax.Function (_, Some f_name, params, _) ->
		let f_id = try JS2JSIL_Preprocessing.get_codename e
			with _ -> raise (Failure "named function literals should be annotated with their respective code names") in

		(* x_f_outer_er := new ();  *)
		let x_f_outer_er = fresh_er_var () in
		(* METADATA: null, since environment record *)
		let cmd_ass_xfouter = LBasic (New (x_f_outer_er, None)) in

		(* x_sc_f := x_sc @ {{ x_f_outer_er }}  *)
		let x_sc_f = fresh_scope_chain_var () in
		let cmd_xscf_ass = LBasic (Assignment (x_sc_f, BinOp (Var tr_ctx.tr_sc_var, LstCat, EList [ Var x_f_outer_er ]))) in

		(* x_f := create_function_object(x_sc_f, f_id, params) *)
		let x_f, cmd_fun_constr = make_create_function_object_call x_sc_f f_id params in

		(* [x_f_outer_er, f] := x_f *)
		let cmd_fname_updt = LBasic (Mutation (Var x_f_outer_er, Literal (String f_name), Var x_f, None)) in

		(* x_cae := i__checkAssignmentErrors (ref-v(x_f_outer_er, "f")) with err *)
		let x_cae = fresh_var () in
		let cmd_cae = LCall (x_cae, lit_str checkAssignmentErrorsName, [ EList [lit_refv; Var x_f_outer_er; lit_str f_name] ], Some tr_ctx.tr_err) in

		let cmds = [
		  (None, cmd_ass_xfouter);      (*  x_f_outer_er := new ()                                                *)
			(None, cmd_xscf_ass);         (*  x_sc_f := x_f_outer_er :: x_sc                                        *)
			(None, cmd_fun_constr);       (*  x_f := create_function_object(x_sc_f, f_id, params)                   *)
			(None, cmd_fname_updt);       (*  [x_f_outer_er, f] := x_f                                              *)
			(None, cmd_cae);              (*  x_cae := i__checkAssignmentErrors (ref-v(x_f_outer_er, "f")) with err *)
		] in

		let cmds = annotate_first_cmd (annotate_cmds cmds) in
		cmds, Var x_f, [ (* x_t; *) x_cae ]


	| Parser_syntax.VarDec decs ->
		let rec loop decs cmds errs =
			(match decs with
			| [] -> raise (Failure "no empty variable declaration lists in expression contexts")

			| [ (v, eo) ] ->
				(match eo with
				| None ->
					let x, new_cmds, new_errs = compile_var_dec_without_exp v in
					x, (cmds @ new_cmds), (errs @ new_errs)
				| Some e ->
					let new_cmds, x, new_errs	 = compile_var_dec v e in
					x, (cmds @ new_cmds), (errs @ new_errs))

			| (v, eo) :: rest_decs ->
				(match eo with
				| None -> loop rest_decs cmds errs
				| Some e ->
					let new_cmds, _, new_errs	 = compile_var_dec v e in
					loop rest_decs (cmds @ new_cmds) (errs @ new_errs))) in
		let x, cmds, errs = loop decs [] [] in
		(annotate_first_cmd cmds), Var x, errs

	| Parser_syntax.RegExp (_, _) -> raise (Failure "Not implemented: RegExp literal")
	| x -> raise (Failure (Printf.sprintf "Unhandled expression %s at %s" (Pretty_print.string_of_exp_syntax x) __LOC__))


and translate_statement tr_ctx e  =
	let fe = translate_expr tr_ctx in
	let f = translate_statement tr_ctx in

	let f_previous loop_list previous lab e =
		let new_tr_ctx = update_tr_ctx ~loop_list:loop_list ~previous:previous ~lab:lab tr_ctx in
		translate_statement new_tr_ctx e in

	let cur_var_tbl = get_scope_table cc_tbl tr_ctx.tr_er_fid in
	let find_var_er_index v =
		(try
			let fid_v = Hashtbl.find cur_var_tbl v in
			let fid_v_index = JS2JSIL_Preprocessing.get_vis_list_index tr_ctx.tr_vis_list fid_v in
			fid_v_index
			with _ ->
				raise (Failure (Printf.sprintf "Error: %s is not in the scope clarification table!" v))) in

	(* All the other commands must get the offsets and nothing else *)
	let js_char_offset          = e.Parser_syntax.exp_offset in
	let js_line_offset          = tr_ctx.tr_offset_converter js_char_offset in
	let metadata                = { line_offset = Some js_line_offset; invariant = None; pre_logic_cmds = []; post_logic_cmds = [] } in
	let annotate_cmds           = annotate_cmds_top_level metadata in
	let annotate_cmd            = fun cmd lab -> annotate_cmd_top_level metadata (lab, cmd) in

	(* The first command must get the logic commands and the invariants *)
	let lcmds, _                = JS2JSIL_Preprocessing.translate_lannots_in_exp cc_tbl vis_tbl old_fun_tbl tr_ctx.tr_fid tr_ctx.tr_sc_var true e in
	let invariant               = JS2JSIL_Preprocessing.translate_invariant_in_exp cc_tbl vis_tbl old_fun_tbl tr_ctx.tr_fid tr_ctx.tr_sc_var e in
	let annotate_first_cmd      = add_more_metadata metadata lcmds invariant in

	let compile_var_dec x e =
		let index = find_var_er_index x in
		let cmds_e, x_e, errs_e = fe e in

		(* x_v := i__getValue (x) with err *)
		let x_v, cmd_gv_x, errs_x_v = make_get_value_call x_e tr_ctx.tr_err in

		(* x_sf := l-nth(x__sc, index)  *)
		let x_sf = fresh_var () in
	  let cmd_xsf_ass = LBasic (Assignment (x_sf, LstNth (Var tr_ctx.tr_sc_var, lit_num (float_of_int index)))) in

		(* x_ref := {{ "v", x_sf, "x" }}  *)
		let x_ref = fresh_var () in
		let cmd_xref_ass = LBasic (Assignment (x_ref, EList [lit_refv; Var x_sf; lit_str x])) in

		(* x_cae := i__checkAssignmentErrors (x_ref) with err *)
		let x_cae = fresh_var () in
		let cmd_cae = LCall (x_cae, Literal (String checkAssignmentErrorsName), [ (Var x_ref) ], Some tr_ctx.tr_err) in

		(* x_pv := i__putValue(x_ref, x_v) with err2 *)
		let x_pv, cmd_pv = make_put_value_call (Var x_ref) x_v tr_ctx.tr_err in
		let cmds = cmds_e @ (annotate_cmds [
			(None, cmd_gv_x);      (* x_v := i__getValue (x) with err                      *)
			(None, cmd_xsf_ass);   (* x_sf := l-nth(x_sc, index)                           *)
			(None, cmd_xref_ass);  (* x_ref := {{ "v", x_sf, "x" }}                        *)
			(None, cmd_cae);       (* x_cae := i__checkAssignmentErrors (x_ref) with err   *)
			(None, cmd_pv)         (* x_pv := i__putValue(x_ref, x_v) with err             *)
		]) in
		let errs = errs_e @ errs_x_v @ [ x_cae; x_pv ] in
		cmds, x_ref, errs	in

	let create_final_phi_cmd cmds x errs rets breaks conts break_label js_lab =
		let cur_breaks, outer_breaks = filter_cur_jumps breaks js_lab false in
		(match cur_breaks with
		| [] -> cmds, x, errs, rets, breaks, conts
		| _ ->
			let x_name, cmd_new_x =
				(match x with
				| Var x_name -> x_name, []
				| Literal lit ->
					let x_name = fresh_var () in
					let cmd_new_x = annotate_cmd (LBasic (Assignment (x_name, Literal lit))) None in
					x_name, [ cmd_new_x ]
				| _ -> raise (Failure "translate. Block: the result of the compilation must be a variable or a literal")) in
			let x_ret = fresh_var () in
			let phi_args = cur_breaks @ [ x_name ] in
			let phi_args = List.map (fun x -> Var x)  phi_args in
			let phi_args = Array.of_list phi_args in
			let cmd_ass_phi = annotate_cmd (LPhiAssignment (x_ret, phi_args)) break_label in
			(cmds @ cmd_new_x @ [ cmd_ass_phi ], Var x_ret, errs, rets, outer_breaks, conts)) in

	(**
   *  When breaking or continuing inside a try-catch-finally block, the code of the finally
	 *  always gets executed before breaking or continuing. Hence, the cont_break_list needs to be
	 *  rewritten so that continues and breaks are redirected to the code of the finally.
	 *  this procedure returns the new cont_break_list together with a mapping that associates
	 *  the newly created labels with their original values.
	 *)
	let rename_cont_break_list cont_break_list finally_lab_gen =
		let jumps_mapping = Hashtbl.create 101 in
		(* Printf.printf "I am creating a jumps mapping for a try catch finally\n"; *)
		let rec rename_cont_break_list_iter cont_break_list (new_cont_break_list : (string option * string * string option * bool) list) =
			(match cont_break_list with
				| [] -> List.rev new_cont_break_list
				| (None, break_lab, js_lab, is_valid_unlabelled) :: rest ->
					let new_finally_lab = finally_lab_gen () in
					(* Printf.printf "Creating a mapping from %s to %s\n" break_lab new_finally_lab; *)
					Hashtbl.add jumps_mapping new_finally_lab break_lab;
					rename_cont_break_list_iter rest ((None, new_finally_lab, js_lab, is_valid_unlabelled) :: new_cont_break_list)
				| (Some cont_lab, break_lab, js_lab, is_valid_unlabelled) :: rest ->
					let new_finally_lab1 = finally_lab_gen () in
					let new_finally_lab2 = finally_lab_gen () in
					Hashtbl.add jumps_mapping new_finally_lab1 cont_lab;
					Hashtbl.add jumps_mapping new_finally_lab2 break_lab;
					(* Printf.printf "Creating a mapping from %s to %s and %s to %s\n" break_lab new_finally_lab1 cont_lab new_finally_lab2; *)
          rename_cont_break_list_iter rest ((Some new_finally_lab1, new_finally_lab2, js_lab, is_valid_unlabelled) :: new_cont_break_list)) in
		let new_cont_break_list = rename_cont_break_list_iter cont_break_list [] in
		new_cont_break_list, jumps_mapping in


	(**
   *  We create a finally block for each break/continue that occurs inside
	 *  the try and catch blocks of the try-catch-finally.
	 *)
	let make_finally_break_blocks jump_list jumps_mapping e tcf_lab end_label =
		let rec make_finally_blocks_iter jump_list finally_blocks cur_break_vars errs rets outer_breaks inner_breaks conts =
			(match jump_list with
			| [] -> finally_blocks, cur_break_vars, errs, rets, outer_breaks, inner_breaks, conts
			| (js_lab, var, jump) :: rest ->
				try
					(let original_jump = Hashtbl.find jumps_mapping jump in
					let new_loop_list = (None, end_label, tcf_lab, false) :: tr_ctx.tr_loop_list in
					let new_tr_ctx = update_tr_ctx ~loop_list:tr_ctx.tr_loop_list ~lab:None ~previous:None tr_ctx in
					let cmds_cur, _, errs_cur, rets_cur, breaks_cur, conts_cur = translate_statement new_tr_ctx e in
					let cmds_cur = add_initial_label cmds_cur jump metadata in
					let new_finally_block = cmds_cur @ [ annotate_cmd (LGoto original_jump) None ] in
					let cur_inner_breaks, cur_outer_breaks = filter_cur_jumps breaks_cur tcf_lab false in
          make_finally_blocks_iter rest (finally_blocks @ new_finally_block) cur_break_vars (errs @ errs_cur) (rets @ rets_cur) (outer_breaks @ cur_outer_breaks @ [ (js_lab, var, original_jump) ]) (inner_breaks @ cur_inner_breaks) (conts @ conts_cur) )
					with _ ->
						(if ((not (tcf_lab = None)) && (tcf_lab = js_lab))
							then make_finally_blocks_iter rest finally_blocks (cur_break_vars @ [ var ]) errs rets outer_breaks inner_breaks conts
							else raise (Failure (Printf.sprintf "make_finally_break_blocks: unknown jump %s\n" jump)))) in
		make_finally_blocks_iter jump_list [] [] [] [] [] [] [] in


		let make_finally_cont_blocks jump_list jumps_mapping e tcf_lab end_label  =
		let rec make_finally_blocks_iter jump_list finally_blocks errs rets outer_breaks inner_breaks conts =
			(match jump_list with
			| [] -> finally_blocks, errs, rets, outer_breaks, inner_breaks, conts
			| (js_lab, var, jump) :: rest ->
				try
					(
					(* Printf.printf ("I am processing a continue!!! \n"); *)
					let original_jump = Hashtbl.find jumps_mapping jump in
					let new_loop_list = (None, end_label, tcf_lab, false) :: tr_ctx.tr_loop_list in
					let new_ctx = update_tr_ctx ~loop_list:new_loop_list ~lab:None ~previous:None tr_ctx in
					let cmds_cur, _, errs_cur, rets_cur, breaks_cur, conts_cur = translate_statement new_ctx e in
					let cmds_cur = add_initial_label cmds_cur jump metadata in
					let new_finally_block = cmds_cur @ [ annotate_cmd (LGoto original_jump) None ] in
					let cur_inner_breaks, cur_outer_breaks = filter_cur_jumps breaks_cur tcf_lab false in
          make_finally_blocks_iter rest (finally_blocks @ new_finally_block) (errs @ errs_cur) (rets @ rets_cur) (outer_breaks @ cur_outer_breaks) (inner_breaks @ cur_inner_breaks) (conts @ conts_cur @ [ (js_lab, var, original_jump) ]) )
					with _ -> raise (Failure (Printf.sprintf "make_finally_cont_blocks: unknown jump %s\n" jump))) in
		make_finally_blocks_iter jump_list [] [] [] [] [] [] in



	let make_try_catch_cmds e1 (x, e2) catch_id =
	  (**
									cmds1
		            	goto finally
		    err1:    	x_err := PHI(errs1)
				        	x_er := new ()
									x_cae := i__checkAssignmentErrors (ref-v(x_er, "x")) with err2
									[x_er, "x"] := x_err
									[x_scope, "cid"] := x_er
									cmds2
									goto finally
				err2:     x_ret_1 := PHI(x_cae, errs2)
				          goto err
				finally:  x_ret_2 := PHI(breaks1, x_1, breaks2, x_2)
	  *)
		let new_err1, new_err2, finally, end_label, _, _ = fresh_tcf_vars () in
		let new_loop_list = (None, finally, tr_ctx.tr_js_lab, false) :: tr_ctx.tr_loop_list in
		let new_ctx_1 = update_tr_ctx ~loop_list:new_loop_list ~previous:None ~lab:None ~err:new_err1 tr_ctx in
		let cmds1, x1, errs1, rets1, breaks1, conts1 = translate_statement new_ctx_1 e1 in
		let cmds1, x1_v = add_final_var cmds1 x1 metadata in

		let x_sc_new = fresh_scope_chain_var () in
		let new_ctx_2 = update_tr_ctx ~loop_list:new_loop_list ~previous:None ~lab:None ~err:new_err2 ~vis_list:(tr_ctx.tr_vis_list @ [ catch_id ]) ~er_fid:catch_id ~sc_var:x_sc_new tr_ctx in
		let cmds2, x2, errs2, rets2, breaks2, conts2 = translate_statement new_ctx_2 e2 in
		let cmds2, x2_v = add_final_var cmds2 x2 metadata in

		let cur_breaks1, outer_breaks1 = filter_cur_jumps breaks1 tr_ctx.tr_js_lab false in
		let cur_breaks2, outer_breaks2 = filter_cur_jumps breaks2 tr_ctx.tr_js_lab false in

		(* x_err := PHI(errs1) *)
		let x_err = fresh_err_var () in
		let phi_args1 = List.map (fun x -> Var x) errs1 in
		let phi_args1 = Array.of_list phi_args1 in
		let cmd_ass_xerr = LPhiAssignment (x_err, phi_args1) in

		(* x_er := new () *)
		let x_er = fresh_er_var () in
		(* METADATA: null, since environment record *)
		let cmd_ass_xer = LBasic (New (x_er, None)) in

		(* x_cae := i__checkAssignmentErrors (ref-v(x_er, "x")) with err2 *)
		let x_cae = fresh_var () in
		let cmd_cae = LCall (x_cae, Literal (String checkAssignmentErrorsName), [ EList [lit_refv; Var x_er; lit_str x] ], Some new_err2) in

		(* [x_er, "x"] := x_err *)
		let cmd_mutate_x = LBasic (Mutation (Var x_er, Literal (String x), Var x_err, None)) in

		(* x_sc_new := x_sc @ {{ x_er }}  *)
		let cmd_sc_updt = LBasic (Assignment (x_sc_new, BinOp (Var tr_ctx.tr_sc_var, LstCat, EList [ Var x_er ]))) in

	  (* err2:     x_ret_1 := PHI(x_cae, errs2) *)
		let x_ret_1 = fresh_var () in
		let phi_args2 = List.map (fun x -> Var x) (x_cae :: errs2) in
		let phi_args2 = Array.of_list phi_args2 in
		let cmd_ass_xret1 = LPhiAssignment (x_ret_1, phi_args2) in

		(* x_ret_2 := PHI(cur_breaks1, x_1, cur_breaks2, x_2) *)
		let x_ret_2 = fresh_var () in
		let phi_args3 = cur_breaks1 @ [ x1_v ] @ cur_breaks2 @ [ x2_v ] in
		let phi_args3 = List.map (fun x -> Var x) phi_args3 in
		let phi_args3 = Array.of_list phi_args3 in
		let cmd_ass_xret2 = LPhiAssignment (x_ret_2, phi_args3) in

		let cmds = cmds1 @ (annotate_cmds [
			(None,           LGoto finally);
			(Some new_err1,  cmd_ass_xerr);
			(None,           cmd_ass_xer);
			(None,           cmd_cae);
			(None,           cmd_mutate_x);
			(None,           cmd_sc_updt)
		]) @ cmds2 @ (annotate_cmds [
			(None,           LGoto finally);
			(Some new_err2,  cmd_ass_xret1);
			(None,           LGoto tr_ctx.tr_err);
			(Some finally,   cmd_ass_xret2)
		]) in

		cmds, x_ret_2, [ x_ret_1 ], rets1 @ rets2, outer_breaks1 @ outer_breaks2, conts1 @ conts2, end_label in


	let make_try_catch_cmds_with_finally e1 (x, e2) catch_id e3 =
	  (**
									cmds1
		            	goto finally
		    err1:    	x_err := PHI(errs1)
				        	x_er := new ()
									x_cae := i__checkAssignmentErrors (ref-v(x_er, "x")) with err
									[x_er, "x"] := x_err
									[x_scope, "cid"] := x_er
									cmds2
									goto finally
				err2:    	x_ret_1 := PHI(x_cae; errs2)
				          cmds_finally
									goto err
				finally:  x_ret_2 := PHI(breaks_1, x_1, breaks_2, x_2)
				          cmds_finally
                  goto end
				ret_tcf:  x_ret_3 := PHI(rets1, rets2)
				          cmds_finally
									goto ret_label
									break_cont_ret_finally_blocks_1
									break_cont_ret_finally_blocks_2
			  end:      x_ret_4 := PHI(breaks_finally, x_ret_2)
	  *)
		let new_err1, new_err2, finally, end_label, abnormal_finally, tcf_ret = fresh_tcf_vars () in
		let new_loop_list, jumps_mapping = rename_cont_break_list tr_ctx.tr_loop_list abnormal_finally in

		let new_loop_list = (None, finally, tr_ctx.tr_js_lab, false) :: new_loop_list in

		let new_ctx_1 = update_tr_ctx ~loop_list:new_loop_list ~lab:None ~previous:None ~ret_lab:tcf_ret ~err:new_err1 tr_ctx in
		let cmds1, x1, errs1, rets1, breaks1, conts1 = translate_statement new_ctx_1 e1 in
		let cmds1, x1_v = add_final_var cmds1 x1 metadata in

		let x_sc_new = fresh_scope_chain_var () in
		let new_ctx_2 = update_tr_ctx ~loop_list:new_loop_list ~lab:None ~previous:None ~ret_lab:tcf_ret ~err:new_err2 ~vis_list:(tr_ctx.tr_vis_list @ [ catch_id ]) ~er_fid:catch_id ~sc_var:x_sc_new tr_ctx in
		let cmds2, x2, errs2, rets2, breaks2, conts2 = translate_statement new_ctx_2 e2 in
		let cmds2, x2_v = add_final_var cmds2 x2 metadata in

		let new_loop_list = (None, end_label, tr_ctx.tr_js_lab, false) :: tr_ctx.tr_loop_list  in
		let new_ctx_3 = update_tr_ctx ~loop_list:new_loop_list ~lab:None ~previous:None tr_ctx in
		let cmds3_1, _, errs3_1, rets3_1, breaks3_1, conts3_1 = translate_statement new_ctx_3 e3 in
		let cmds3_2, _, errs3_2, rets3_2, breaks3_2, conts3_2 = translate_statement new_ctx_3 e3 in
		let cmds3_3, _, errs3_3, rets3_3, breaks3_3, conts3_3 = translate_statement new_ctx_3 e3 in

		let inner_breaks3_1, outer_breaks3_1 = filter_cur_jumps breaks3_1 tr_ctx.tr_js_lab false in
		let inner_breaks3_2, outer_breaks3_2 = filter_cur_jumps breaks3_2 tr_ctx.tr_js_lab false in
		let inner_breaks3_3, outer_breaks3_3 = filter_cur_jumps breaks3_3  tr_ctx.tr_js_lab false in

		let finally_cmds_breaks1, cur_break_vars_1, errs_b1, rets_b1, outer_breaks_b1, inner_breaks_b1, conts_b1 = make_finally_break_blocks breaks1 jumps_mapping e3 tr_ctx.tr_js_lab end_label in
		let finally_cmds_conts1, errs_c1, rets_c1, outer_breaks_c1, inner_breaks_c1, conts_c1 = make_finally_cont_blocks conts1 jumps_mapping e3 tr_ctx.tr_js_lab end_label in

		let finally_cmds_breaks2, cur_break_vars_2, errs_b2, rets_b2, outer_breaks_b2, inner_breaks_b2, conts_b2 = make_finally_break_blocks breaks2 jumps_mapping e3 tr_ctx.tr_js_lab end_label in
		let finally_cmds_conts2, errs_c2, rets_c2, outer_breaks_c2, inner_breaks_c2, conts_c2 = make_finally_cont_blocks conts2 jumps_mapping e3 tr_ctx.tr_js_lab end_label in

		(* x_err := PHI(errs1) *)
		let x_err = fresh_err_var () in
		let phi_args1 = List.map (fun x -> Var x) errs1 in
		let phi_args1 = Array.of_list phi_args1 in
		let cmd_ass_xerr = LPhiAssignment (x_err, phi_args1) in

		(* x_er := new () *)
		let x_er = fresh_er_var () in
		(* METADATA: null, since environment record *)
		let cmd_ass_xer = LBasic (New (x_er, None)) in

		(* x_cae := i__checkAssignmentErrors (ref-v(x_er, "x")) with err2 *)
		let x_cae = fresh_var () in
		let cmd_cae = LCall (x_cae, Literal (String checkAssignmentErrorsName), [ EList [lit_refv; Var x_er; lit_str x] ], Some new_err2) in

		(* [x_er, "x"] := x_err *)
		let cmd_mutate_x = LBasic (Mutation (Var x_er, Literal (String x), Var x_err, None)) in

		(* x_sc_new := x_sc @ {{ x_er }} *)
		let cmd_sc_updt = LBasic (Assignment (x_sc_new, BinOp (Var tr_ctx.tr_sc_var, LstCat, EList [ Var x_er ]))) in

	  (* err2:     x_ret_1 := PHI(x_cae, errs2) *)
		let x_ret_1 = fresh_var () in
		let phi_args2 = List.map (fun x -> Var x) (x_cae :: errs2) in
		let phi_args2 = Array.of_list phi_args2 in
		let cmd_ass_xret1 = LPhiAssignment (x_ret_1, phi_args2) in

		(* x_ret_2 := PHI(cur_breaks1, x_1, cur_breaks2, x_2, x_ret_1) *)
		let x_ret_2 = fresh_var () in
		let phi_args3 = cur_break_vars_1 @ [ x1_v ] @ cur_break_vars_2 @ [ x2_v ] in
		let phi_args3 = List.map (fun x -> Var x) phi_args3 in
		let phi_args3 = Array.of_list phi_args3 in
		let cmd_ass_xret2 = LPhiAssignment (x_ret_2, phi_args3) in

		(* x_ret_3 := PHI(rets1, rets2)  *)
		let x_ret_3 = fresh_var () in
		let phi_args4 = rets1 @ rets2 in
		let phi_args4 = List.map (fun x -> Var x) phi_args4 in
		let phi_args4 = Array.of_list phi_args4 in
		let cmd_ass_xret3 = LPhiAssignment (x_ret_3, phi_args4) in

		(* x_ret_4 := PHI(inner_breaks_finally, x_ret_2) *)
		let x_ret_4 = fresh_var () in
		let phi_args5 = inner_breaks3_1 @ inner_breaks3_2 @ [ x_ret_2 ] @ inner_breaks3_3 @ inner_breaks_b1 @ inner_breaks_c1 @ inner_breaks_b2 @ inner_breaks_c2 in
		let phi_args5 = List.map (fun x -> Var x) phi_args5 in
		let phi_args5 = Array.of_list phi_args5 in
		let cmd_ass_xret4 = LPhiAssignment (x_ret_4, phi_args5) in

		let ret_label = tr_ctx.tr_ret_lab in
		let errs = errs3_1 @ [ x_ret_1 ] @ errs3_2 @ errs3_3 @ errs_b1 @ errs_c1 @ errs_b2 @ errs_c2 in
		let rets = rets3_1 @ rets3_2 @ rets3_3 @ [ x_ret_3 ] @ rets_b1 @ rets_c1 @ errs_b2 @ errs_c2 in
		let breaks = outer_breaks3_1 @ outer_breaks3_2 @ outer_breaks3_3 @ outer_breaks_b1 @ outer_breaks_c1 @ outer_breaks_b2 @ outer_breaks_c2 in
		let conts = conts3_1 @ conts3_2 @ conts3_3 @ conts_b1 @ conts_c1 @ conts_b2 @ conts_c2 in

		let cmds = cmds1 @ (annotate_cmds [                 (*            cmds1                                                            *)
			(None,           LGoto finally);                 (*            goto finally                                                     *)
			(Some new_err1,  cmd_ass_xerr);                   (*  err1:     x_err := PHI(errs1)                                              *)
			(None,           cmd_ass_xer);                    (*            x_er := new ()                                                   *)
			(None,           cmd_cae);                        (*            x_cae := i__checkAssignmentErrors (ref-v(x_er, "x")) with err2   *)
			(None,           cmd_mutate_x);                   (*            [x_er, "x"] := x_err                                             *)
			(None,           cmd_sc_updt)                     (*            x_sc_new := x_er :: x_sc                                         *)
		]) @ cmds2 @ (annotate_cmds [                       (*            cmds2                                                            *)
			(None,           LGoto finally);                 (*            goto finally                                                     *)
			(Some new_err2,  cmd_ass_xret1);                  (*  err2:     x_ret_1 := PHI(x_cae, errs2)                                     *)
		]) @ cmds3_1 @ (annotate_cmds [                     (*            cmds3_1                                                          *)
		  (None,           LGoto tr_ctx.tr_err);           (*            goto err                                                         *)
			(Some finally,   cmd_ass_xret2)                   (*  finally:  x_ret_2 := PHI(cur_breaks1, x_1, cur_breaks2, x_2)               *)
		]) @ cmds3_2 @ (annotate_cmds [                     (*            cmds3_2                                                          *)
		  (None,           LGoto end_label);               (*            goto end                                                         *)
			(Some tcf_ret,   cmd_ass_xret3)                   (*  tcf_ret:  x_ret_3 := PHI(rets1, rets2)                                     *)
		]) @ cmds3_3 @ (annotate_cmds [                     (*            cmds3_3                                                          *)
		  (None,           LGoto ret_label)                (*            goto ret_label                                                   *)
		]) @ finally_cmds_breaks1 @ finally_cmds_conts1     (*            break_cont_finally_blocks_1                                      *)
		   @ finally_cmds_breaks2 @ finally_cmds_conts2 @ [ (*            break_cont_finally_blocks_2                                      *)
	    annotate_cmd cmd_ass_xret4 (Some end_label)       (*  end:      x_ret_4 := PHI(x_ret_2, inner_breaks_finally)                    *)
		] in
		cmds, Var x_ret_4, errs, rets, breaks, conts  in


	let make_try_finally_cmds e1 e3 =
	  (**
						cmds1
		            	goto finally
		    err1:    	x_err := PHI(errs1)
						cmds_finally
						goto err
			finally:    x_ret_1 := PHI(breaks_1, x_1)
				        cmds_finally
                  		goto end
			ret_tcf: 	x_ret_2 := PHI(rets1)
				        cmds_finally
						goto ret_label
						break_cont_ret_finally_blocks_1
			end:	   	x_ret_3 := PHI(x_ret_1, breaks_finally)
	  *)
		let new_err1, new_err2, finally, end_label, abnormal_finally, tcf_ret = fresh_tcf_vars () in
		let new_loop_list, jumps_mapping = rename_cont_break_list tr_ctx.tr_loop_list abnormal_finally in

		let new_loop_list = (None, finally, tr_ctx.tr_js_lab, false) :: new_loop_list in
		let new_ctx_1 = update_tr_ctx ~loop_list:new_loop_list ~err:new_err1 ~lab:None ~previous:None ~ret_lab:tcf_ret tr_ctx in
		let cmds1, x1, errs1, rets1, breaks1, conts1 = translate_statement new_ctx_1 e1 in
		let cmds1, x1_v = add_final_var cmds1 x1 metadata in

		let new_loop_list = (None, end_label, tr_ctx.tr_js_lab, false) :: tr_ctx.tr_loop_list in
		let new_ctx_3 = update_tr_ctx ~loop_list:new_loop_list ~lab:None ~previous:None tr_ctx in
		let cmds3_1, _, errs3_1, rets3_1, breaks3_1, conts3_1 = translate_statement new_ctx_3 e3 in
		let cmds3_2, _, errs3_2, rets3_2, breaks3_2, conts3_2 = translate_statement new_ctx_3 e3 in
		let cmds3_3, _, errs3_3, rets3_3, breaks3_3, conts3_3 = translate_statement new_ctx_3 e3 in
		let inner_breaks3_1, outer_breaks3_1 = filter_cur_jumps breaks3_1 tr_ctx.tr_js_lab false in
		let inner_breaks3_2, outer_breaks3_2 = filter_cur_jumps breaks3_2 tr_ctx.tr_js_lab false in
		let inner_breaks3_3, outer_breaks3_3 = filter_cur_jumps breaks3_3 tr_ctx.tr_js_lab false in

		let finally_cmds_breaks1, cur_break_vars_1, errs_b1, rets_b1, outer_breaks_b1, inner_breaks_b1, conts_b1 = make_finally_break_blocks breaks1 jumps_mapping e3 tr_ctx.tr_js_lab end_label in
		let finally_cmds_conts1, errs_c1, rets_c1, outer_breaks_c1, inner_breaks_c1, conts_c1 = make_finally_cont_blocks conts1 jumps_mapping e3 tr_ctx.tr_js_lab end_label in

		(* x_err := PHI(errs1) *)
		let x_err = fresh_err_var () in
		let phi_args1 = List.map (fun x -> Var x) errs1 in
		let phi_args1 = Array.of_list phi_args1 in
		let cmd_ass_xerr = LPhiAssignment (x_err, phi_args1) in

		(* x_ret_1 := PHI(cur_breaks1, x_1) *)
		let x_ret_1 = fresh_var () in
		let phi_args = cur_break_vars_1 @ [ x1_v ] in
		let phi_args = List.map (fun x -> Var x) phi_args in
		let phi_args = Array.of_list phi_args in
		let cmd_ass_xret1 = LPhiAssignment (x_ret_1, phi_args) in

		(* x_ret_2 := PHI(rets1)  *)
		let x_ret_2 = fresh_var () in
		let phi_args = rets1 in
		let phi_args = List.map (fun x -> Var x) phi_args in
		let phi_args = Array.of_list phi_args in
		let cmd_ass_xret2 = LPhiAssignment (x_ret_2, phi_args) in

		(* x_ret_3 := PHI(inner_breaks_finally, x_ret_1) *)
		let x_ret_3 = fresh_var () in
		let phi_args = inner_breaks3_1 @ inner_breaks3_2 @  [ x_ret_1 ] @ inner_breaks3_3 @ inner_breaks_b1 @ inner_breaks_c1 in
		let phi_args = List.map (fun x -> Var x) phi_args in
		let phi_args = Array.of_list phi_args in
		let cmd_ass_xret3 = LPhiAssignment (x_ret_3, phi_args) in

		let ret_label = tr_ctx.tr_ret_lab in
		let errs = errs3_1 @ [ x_err ] @ errs3_2 @ errs3_3 @ errs_b1 @ errs_c1 in
		let rets = rets3_1 @ rets3_2 @ rets3_3 @ [ x_ret_2 ] @ rets_b1 @ rets_c1 in
		let breaks = outer_breaks3_1 @ outer_breaks3_2 @ outer_breaks3_3 @ outer_breaks_b1 @ outer_breaks_c1 in
		let conts = conts3_1 @ conts3_2 @ conts3_3 @ conts_b1 @ conts_c1 in

		let cmds = cmds1 @ (annotate_cmds [                 (*            cmds1                                                       *)
			(None,            LGoto finally);                (*            goto finally                                                *)
			(Some new_err1,   cmd_ass_xerr);                  (*  err1:     x_err := PHI(errs1)                                         *)
		]) @ cmds3_1 @ (annotate_cmds [                     (*            cmds3_1                                                     *)
		  (None,           LGoto tr_ctx.tr_err);           (*            goto err                                                    *)
			(Some finally,   cmd_ass_xret1)                   (*  finally:  x_ret_1 := PHI(breaks_1, x_1)                               *)
		]) @ cmds3_2 @ (annotate_cmds [                     (*            cmds3_2                                                     *)
		  (None,           LGoto end_label);               (*            goto end                                                    *)
			(Some tcf_ret,   cmd_ass_xret2)                   (*  tcf_ret:  x_ret_2 := PHI(rets1)                                       *)
		]) @ cmds3_3 @ (annotate_cmds [                     (*            cmds3_3                                                     *)
		  (None,           LGoto ret_label)                (*            goto ret_label                                              *)
		]) @ finally_cmds_breaks1 @ finally_cmds_conts1 @ [ (*            break_cont_finally_blocks_1                                 *)
	    annotate_cmd cmd_ass_xret3 (Some end_label)       (*  end:      x_ret_3 := PHI(inner_breaks_finally, x_ret_2)               *)
		] in
		cmds, Var x_ret_3, errs, rets, breaks, conts  in


	(** Statements **)
	match e.Parser_syntax.exp_stx with
	| Parser_syntax.Script (_, es)
	| Parser_syntax.Block es ->
		(**
     Section 12.1 - Block

		 C_iter({}) = [], empty

		 C(stmts) = cmds, x
		 C(stmt) = cmds', x'
		 CanBeEmpty(stmt)
		 -------------------------
		 C_iter(stmts; stmt) =      cmds
						      		cmds'
									goto [x' = empty] next end
							 next:  skip
							 end:   x'' := PHI(x', x)



		 C_iter(stmts) = cmds, x
		 C_iter(stmt) = cmds', x'
		 !CanBeEmpty(stmt)
		 -------------------------
		 C_iter(stmts; stmt) =  cmds
								cmds'


		 C_iter (stmts) = cmds, x
		 -------------------------------
		 C(Block stmts) = cmds
		                  x_ret := PHI (break_vars, x)
     *)

		let break_label, new_loop_list =
			(match tr_ctx.tr_js_lab with
			| None -> None, tr_ctx.tr_loop_list
			| Some lab ->
				let break_label = fresh_break_label () in
				Some break_label, ((None, break_label, tr_ctx.tr_js_lab, false) :: tr_ctx.tr_loop_list)) in

		let rec loop es bprevious cmds_ac errs_ac rets_ac breaks_ac conts_ac =
			(match es with
			| [] -> [], Literal Empty, [], [], [], []

			| [ e ] ->
				let cmds_e, x_e, errs_e, rets_e, breaks_e, conts_e = f_previous new_loop_list bprevious None e in
				(match (returns_empty_exp e), bprevious with
				| true, Some x_previous ->
					(let new_cmds, x_r = make_check_empty_test x_previous x_e in
					let new_cmds = annotate_cmds new_cmds in
					cmds_ac @ cmds_e @ new_cmds, Var x_r, errs_ac @ errs_e, rets_ac @ rets_e, breaks_ac @ breaks_e, conts_ac @ conts_e)
				| _, _ ->
					cmds_ac @ cmds_e, x_e, errs_ac @ errs_e, rets_ac @ rets_e, breaks_ac @ breaks_e, conts_ac @ conts_e)

			| e :: rest_es ->
				let cmds_e, x_e, errs_e, rets_e, breaks_e, conts_e = f_previous new_loop_list bprevious None e in
				(match (returns_empty_exp e), bprevious with
				| true, Some x_previous ->
					(let new_cmds, x_r = make_check_empty_test x_previous x_e in
					let new_cmds = annotate_cmds new_cmds in
					loop rest_es (Some (Var x_r)) (cmds_ac @ cmds_e @ new_cmds) (errs_ac @ errs_e) (rets_ac @ rets_e) (breaks_ac @ breaks_e) (conts_ac @ conts_e))
				| _, _ ->
					loop rest_es (Some x_e) (cmds_ac @ cmds_e) (errs_ac @ errs_e) (rets_ac @ rets_e) (breaks_ac @ breaks_e) (conts_ac @ conts_e))) in

		let cmds, x, errs, rets, breaks, conts = loop es tr_ctx.tr_previous [] [] [] [] [] in
		create_final_phi_cmd cmds x errs rets breaks conts break_label tr_ctx.tr_js_lab


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
			              x := empty

     *)
		let rec loop decs cmds errs =
			(match decs with
			| [] ->
				let x, empty_ass = make_empty_ass () in

				x, cmds @ [ annotate_cmd empty_ass None ], errs
			| (v, eo) :: rest_decs ->
				(match eo with
				| None -> loop rest_decs cmds errs
				| Some e ->
					let new_cmds, _, new_errs	 = compile_var_dec v e in
					loop rest_decs (cmds @ new_cmds) (errs @ new_errs))) in
		let x, cmds, errs = loop decs [] [] in
		let cmds = annotate_first_cmd cmds in
		cmds, Var x, errs, [], [], []


  | Parser_syntax.Skip (** Section 12.3 - Empty Statement *)
	| Parser_syntax.Debugger -> (** Section 12.15 - Debugger Statement **)
		 [], Literal Empty, [], [], [], []


	| Parser_syntax.Num _
	| Parser_syntax.String _
	| Parser_syntax.Null
	| Parser_syntax.Bool _
	| Parser_syntax.Var _
	| Parser_syntax.This
	| Parser_syntax.Delete _
	| Parser_syntax.Comma _
	| Parser_syntax.Unary_op _
	| Parser_syntax.BinOp _
	| Parser_syntax.Access _
	| Parser_syntax.Call _
	| Parser_syntax.Assign _
	| Parser_syntax.AssignOp _
	| Parser_syntax.FunctionExp _
	| Parser_syntax.New _
	| Parser_syntax.Obj _
	| Parser_syntax.Array _
	| Parser_syntax.CAccess _
	| Parser_syntax.ConditionalOp _  ->
		(**
     Section 12.4 - Expression Statement
		 *)
		let cmds_e, x_e, errs_e = fe e in
		let x_e_v, cmd_gv_xe, errs_x_e_v = make_get_value_call x_e tr_ctx.tr_err in
		let cmds = cmds_e @ [ annotate_cmd cmd_gv_xe None ] in
		let cmds = annotate_first_cmd cmds in
		cmds, Var x_e_v, errs_e @ errs_x_e_v, [], [], []


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
			(match tr_ctx.tr_js_lab with
			| None -> None, tr_ctx.tr_loop_list
			| Some lab ->
				let break_label = fresh_break_label () in
				Some break_label, ((None, break_label, tr_ctx.tr_js_lab, false) :: tr_ctx.tr_loop_list)) in

		let cmds1, x1, errs1 = fe e1 in
		let cmds2, x2, errs2, rets2, breaks2, conts2 = f_previous new_loop_list None None e2 in
		let cmds3, x3, errs3, rets3, breaks3, conts3 =
			(match e3 with
			| None ->
				let x3, cmd3 = make_empty_ass () in
				[ annotate_cmd cmd3 None ], Var x3, [], [], [], []
			| Some e3 -> f_previous new_loop_list None None e3) in

		(* x1_v := getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in

		(* x1_b := toBoolean (x1_v) with err *)
		let x1_b, cmd_tb_x1 = make_to_boolean_call x1 x1_v tr_ctx.tr_err in

		(* goto [x1_b] then else *)
		let then_lab = fresh_then_label () in
		let else_lab = fresh_else_label () in
		let end_lab = fresh_end_label () in
		let cmd_goto_if = LGuardedGoto (Var x1_b, then_lab, else_lab) in

		let cmds2 = add_initial_label cmds2 then_lab metadata in
		let cmds3 = add_initial_label cmds3 else_lab metadata in

		let cmds2, x2 = add_skip_if_empty cmds2 x2 metadata in
		let cmds3, x3 = add_skip_if_empty cmds3 x3 metadata in

		(* goto end *)
		let cmd_goto_endif = LGoto end_lab in

		(* end: x_if := PHI(x2, x3) *)
		let x2_name, x3_name =
			(match x2, x3 with
			| Var x2_name, Var x3_name -> x2_name, x3_name
			| _, _ -> raise (Failure "the compilation of the then and else parts of the an if statement must generate a variable each")) in
		let x_if = fresh_var () in
		let cmd_end_if = LPhiAssignment (x_if, [| (Var x2_name); (Var x3_name) |]) in

		let cmds =
			    cmds1 @ (annotate_cmds [   (*       cmds1                               *)
				(None, cmd_gv_x1);           (*       x1_v := getValue (x1) with err      *)
				(None, cmd_tb_x1);      	   (*       x1_b := toBoolean (x1_v) with err   *)
				(None, cmd_goto_if)          (*       goto [x1_b] then else               *)
			]) @ cmds2 @ (annotate_cmds [  (* then: cmds2                               *)
				(None, cmd_goto_endif)       (*       goto end                            *)
			]) @ cmds3 @ (annotate_cmds [  (* else: cmds3                               *)
				(Some end_lab, cmd_end_if)   (* end:  x_if := PHI(x3, x2)                 *)
			]) in
		let errs = errs1 @ errs_x1_v @ [ x1_b ] @ errs2 @ errs3 in

		let cmds = annotate_first_cmd cmds in
		let cmds, x, errs, rets, breaks, conts = cmds, Var x_if, errs, rets2 @ rets3, breaks2 @ breaks3, conts2 @ conts3 in
		create_final_phi_cmd cmds x errs rets breaks conts break_label tr_ctx.tr_js_lab


	| Parser_syntax.DoWhile (e1, e2) ->
		(**
     Section 12.6.1 - The do-while Statement
     *  C(e1) = cmds1, x1; C(e2) = cmds2, x2
		 *
		 *  C(do { e1 } while (e2) ) =
			          x_ret_0 := empty
			head:     x_ret_1 := PHI(x_ret_0, x_ret_3)
								cmds1
			          x1_v := i__getValue (x1) with err
			cont:	    x_ret_2 := PHI(cont_vars, x1_v)
					      goto [ not (x_ret_2 = empty) ] next1 next2
		  next1:    skip
			next2:    x_ret_3 := PHI(x_ret_1, x_ret_2)
			guard:    cmds2
								x2_v := i__getValue (x2) with err
								x2_b := i__toBoolean (x2_v) with err
								goto [x2_b] head end_loop
		  end_loop: x_ret_4 := PHI(break_vars, x_ret_3)
			          goto [ x_ret_4 = empty ] next3 next4
			next3:    skip
			next4:    x_ret_5 := PHI(x_ret_4, x_ret_1)
		 *)

		let head, guard, body, cont, end_loop = fresh_loop_vars () in

		let new_loop_list = (Some cont, end_loop, tr_ctx.tr_js_lab, true) :: tr_ctx.tr_loop_list in
		let new_ctx = update_tr_ctx ~previous:None ~lab:None ~loop_list:new_loop_list tr_ctx in
		let cmds1, x1, errs1, rets1, breaks1, conts1 = translate_statement new_ctx e2 in
		let cmds2, x2, errs2 = fe e1 in
		let cmds2 = add_initial_label cmds2 guard metadata in

		let cur_breaks, outer_breaks = filter_cur_jumps breaks1 tr_ctx.tr_js_lab true in
		let cur_conts, outer_conts = filter_cur_jumps conts1 tr_ctx.tr_js_lab true in

		(* x_ret_0 := empty *)
		let x_ret_0, cmd_ass_ret_0 = make_empty_ass () in

		(* x_ret_1 := PHI(x_ret_0, x_ret_3)  *)
		let x_ret_1 = fresh_var () in
		let x_ret_2 = fresh_var () in
		let x_ret_3 = fresh_var () in
		let cmd_ass_ret_1 = LPhiAssignment (x_ret_1, [| (Var x_ret_0); (Var x_ret_3) |]) in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in

		(* x_ret_2 := PHI(cont_vars, x1_v) *)
		let cur_conts = cur_conts @ [ x1_v ] in
		let cur_conts = List.map (fun x -> Var x) cur_conts in
		let cont_vars = Array.of_list cur_conts in
		let cmd_ass_ret_2 = LPhiAssignment (x_ret_2, cont_vars) in

		(*  goto [ not (x_ret_2 = empty) ] next1 next2 *)
		let next1 = fresh_next_label () in
		let next2 = fresh_next_label () in
		let expr_goto_guard = BinOp (Var x_ret_2, Equal, Literal Empty) in
		let expr_goto_guard = UnOp (Not, expr_goto_guard) in
		let cmd_goto_empty_test = LGuardedGoto (expr_goto_guard, next1, next2) in

		(* x_ret_3 := PHI(x_ret_1, x_ret_2)  *)
		let cmd_ass_ret_3 = LPhiAssignment (x_ret_3, [| (Var x_ret_1); (Var x_ret_2) |]) in

		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		(* x2_b := i__toBoolean (x2_v) with err *)
		let x2_b, cmd_tb_x2 = make_to_boolean_call x2 x2_v tr_ctx.tr_err in

		(* goto [x2_b] head end_loop *)
		let cmd_dowhile_goto =  LGuardedGoto (Var x2_b, head, end_loop) in

		let cmds_end_loop, x_ret_5 = make_loop_end x_ret_3 x_ret_1 cur_breaks end_loop false in

		let cmds = (annotate_cmds [
					(None,             cmd_ass_ret_0);         (*              x_ret_0 := empty                           *)
					(Some head,        cmd_ass_ret_1);         (* head:        x_ret_1 := PHI(x_ret_0, x_ret_3)             *)
				]) @ cmds1 @ (annotate_cmds [                  (*              cmds1                                        *)
				  (None,             cmd_gv_x1);               (*              x1_v := i__getValue (x1) with err            *)
					(Some cont,        cmd_ass_ret_2);         (* cont:	       x_ret_2 := PHI(cont_vars, x1_v) 	            *)
					(None,             cmd_goto_empty_test);   (*              goto [ not (x_ret_2 = empty) ] next1 next2 *)
					(Some next1,       LBasic Skip);         (* next1:       skip                                         *)
					(Some next2,       cmd_ass_ret_3);         (* next2:       x_ret_3 := PHI(x_ret_1, x_ret_2)             *)
				]) @ cmds2 @ (annotate_cmds [                  (* guard:       cmds2                                        *)
				  (None,             cmd_gv_x2);               (*              x2_v := i__getValue (x2) with err            *)
					(None,             cmd_tb_x2);             (*              x2_b := i__toBoolean (x2_v) with err         *)
					(None,             cmd_dowhile_goto);      (*              goto [x2_b] head end                         *)
				]) @ (annotate_cmds cmds_end_loop) in
		let errs = errs1 @ errs_x1_v @ errs2 @ errs_x2_v @ [ x2_b ] in
		let cmds = annotate_first_cmd cmds in
		cmds, Var x_ret_5, errs, rets1, outer_breaks, outer_conts


	| Parser_syntax.While (e1, e2) ->
		(**
     Section 12.6.2 - The while Statement
     *  C(e1) = cmds1, x1; C(e2) = cmds2, x2
		 *
		 *  C(while (e1) { e2 } ) =
			          x_ret_0 := empty
			head:     x_ret_1 := PHI(x_ret_0, x_ret_3)
					      cmds1
						    x1_v := i__getValue (x1) with err
						    x1_b := i__toBoolean (x1_b) with err
						    goto [x1_b] body end_loop
			body:     cmds2
						    x2_v := i__getValue (x2) with err
			cont:	    x_ret_2 := PHI(cont_vars, x2_v)
								goto [not (x_ret_2 = empty)] next1 next2
			next1:    skip;
			next2:    x_ret_3 := PHI(x_ret_1, x_ret_2)
			          goto head
			end_loop: x_ret_4 := PHI(x_ret_1, break_vars)
			          goto [ x_ret_4 = empty ] next3 next4
			next3:    skip
			next4:    x_ret_5 := PHI(x_ret_4, x_ret_1)
		 *)

		let head, guard, body, cont, end_loop = fresh_loop_vars () in

		let cmds1, x1, errs1 = fe e1 in
		let new_loop_list = (Some cont, end_loop, tr_ctx.tr_js_lab, true) :: tr_ctx.tr_loop_list in
		let new_ctx = update_tr_ctx ~previous:None ~lab:None ~loop_list:new_loop_list tr_ctx in
		let cmds2, x2, errs2, rets2, breaks2, conts2 = translate_statement new_ctx e2 in

		let cur_breaks, outer_breaks = filter_cur_jumps breaks2 tr_ctx.tr_js_lab true in
		let cur_conts, outer_conts = filter_cur_jumps conts2 tr_ctx.tr_js_lab true in

		(* x_ret_0 := empty *)
		let x_ret_0, cmd_ass_ret_0 = make_empty_ass () in
		let x_ret_1 = fresh_var () in

		(* x_ret_1 := PHI(x_ret_0, x_ret_3) *)
		let x_ret_2 = fresh_var () in
		let x_ret_3 = fresh_var () in
		let cmd_ass_ret_1 = LPhiAssignment (x_ret_1, [| (Var x_ret_0); (Var x_ret_3) |]) in

		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in

		(* x1_b := i__toBoolean (x1_v) with err *)
		let x1_b, cmd_tb_x1 = make_to_boolean_call x1 x1_v tr_ctx.tr_err in

		(* goto [x1_b] body endwhile  *)
		let cmd_goto_while = LGuardedGoto (Var x1_b, body, end_loop) in

		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

		(* x_ret_2 := PHI(cont_vars, x2_v) *)
		let cur_conts = cur_conts @ [ x2_v ] in
		let cur_conts = List.map (fun x -> Var x) cur_conts in
		let cont_vars = Array.of_list cur_conts in
		let cmd_ass_ret_2 = LPhiAssignment (x_ret_2, cont_vars) in

		(* goto [not (x_ret_2 = empty)] next1 next2 *)
		let next1 = fresh_next_label () in
		let next2 = fresh_next_label () in
		let expr_goto_guard = BinOp (Var x_ret_2, Equal, Literal Empty) in
		let expr_goto_guard = UnOp (Not, expr_goto_guard) in
		let cmd_goto_empty_test = LGuardedGoto (expr_goto_guard, next1, next2) in

		(* x_ret_3 := PHI(x_ret_1, x_ret_2) *)
		let cmd_ass_ret_3 = LPhiAssignment (x_ret_3, [| (Var x_ret_1); (Var x_ret_2) |]) in

		let cmds_end_loop, x_ret_5 = make_loop_end x_ret_1 x_ret_1 cur_breaks end_loop true in

		let cmds2 = add_initial_label cmds2 body metadata in
		let cmds = (annotate_cmds [
				(None,           cmd_ass_ret_0);         (*           x_ret_0 := empty                         *)
				(Some head,      cmd_ass_ret_1);         (* head:     x_ret_1 := PHI(x_ret_0, x_ret_3)           *)
			]) @ cmds1 @ (annotate_cmds [                (*           cmds1                                      *)
			  (None,           cmd_gv_x1);               (*           x1_v := i__getValue (x1) with err          *)
				(None,           cmd_tb_x1);             (*           x1_b := i__toBoolean (x1_b) with err       *)
				(None,           cmd_goto_while)         (*           goto [x1_b] body endwhile                  *)
			]) @ cmds2 @ (annotate_cmds [                (* body:     cmds2                                      *)
			  (None,           cmd_gv_x2);               (*           x2_v := i__getValue (x2) with err          *)
				(Some cont,      cmd_ass_ret_2);         (* cont:     x_ret_2 := PHI(cont_vars, x2_v)            *)
				(None,           cmd_goto_empty_test);   (*           goto [not (x_ret_2 = empty)] next1 next2 *)
			  (Some next1,     LBasic Skip);           (* next1:    skip                                       *)
				(Some next2,     cmd_ass_ret_3);         (* next2:    x_ret_3 := PHI(x_ret_1, x_ret_2)           *)
				(None,           LGoto head);           (*           goto head                                  *)
			]) @ (annotate_cmds cmds_end_loop) in
		let errs = errs1 @ errs_x1_v @ [ x1_b ] @ errs2 @ errs_x2_v in
		let cmds = annotate_first_cmd cmds in
		cmds, Var x_ret_5, errs, rets2, outer_breaks, outer_conts


		| Parser_syntax.ForIn (e1, e2, e3) ->
		(**
		 Section 12.6.4
     *  C(e_lhs) = cmds1, x1; C(e_obj) = cmds2, x2; C(e_stmt) = cmds3, x3
		 *
		 *  C( for (e1 in e2) { e3 } ) =
			        cmds2 																		1.	Understand what the object is
					x2_v := i__getValue (x2) with err											2.	and get its value
					x_ret_0 := empty 															5.	Set V to empty
					goto [(x2_v = null) or
					(x2_v = undefined)] next6 next0;											3.	If the object is null or undefined, we're done
			next0:	x4 := "i__toObject" (x2_v) with err											4.	Otherwise, convert whatever we have to an object
					xlf := "i__getAllEnumerableFields" (x4)  with err								Put all of its enumerable properties (protochain included) in xlf
					xf  := getFields (xlf) 															Get all of those properties
					len := l-len (xf)																Get the number of properties
					x_c := 0;																		Initialise counter
			head:   x_ret_1 := PHI(x_ret_0, x_ret_3)												Setup return value
					x_c_1 := PSI(x_c, x_c_2);														Setup counter
					goto [x_c_1 < len] body end_loop 											6.	Are we done?
			body: 	xp := l-nth (xf, x_c_1)																6a.	Get the nth property
					xl := [xlf, xp];																	6a.	Get the location of where it should be
					xhf := hasField (xl, xp)              			  									6a.	Understand if it's still there!
					goto [xhf] next1 next3																6a.	And jump accordingly
			next1:	cmds1																				6b.	Evaluate lhs
					x5 := "i__putValue" (x1, xp) with err												6c.	Put it in, put it in
					cmds3																				6d. Evaluate the statement
					x3_v = "i__getValue" (x3) with err
			cont:   x_ret_2 := PHI(cont_vars, x3_v)
					goto [ not (x_ret_2 = empty) ] next2 next3
		  next2:    skip
			next3:  x_ret_3 := PHI(x_ret_1, x_ret_2)
			next4:	x_c_2 := x_c_1 + 1
					goto head
		  end_loop:	x_ret_4 := PHI(x_ret_1, x_ret_1, break_vars)
			        goto [ x_ret_4 = empty ] next5 next6
			next5:  skip
			next6:  x_ret_5 := PHI(x_ret_0, x_ret_1, x_ret_4)

			errs:	errs2, x2_v, x4, xlf, errs1, x5, errs3, x3_v
		 *)
			let cmds1, x1, errs1 = fe e1 in
			let cmds2, x2, errs2 = fe e2 in
			let head, guard, body, cont, end_loop = fresh_loop_vars () in
			let new_loop_list = (Some cont, end_loop, tr_ctx.tr_js_lab, true) :: tr_ctx.tr_loop_list in
			let new_ctx = update_tr_ctx ~previous:None ~lab:None ~loop_list:new_loop_list tr_ctx in
			let cmds3, x3, errs3, rets3, breaks3, conts3 = translate_statement new_ctx e3 in

			let cur_breaks, outer_breaks = filter_cur_jumps breaks3 tr_ctx.tr_js_lab true in
			let cur_conts, outer_conts = filter_cur_jumps conts3 tr_ctx.tr_js_lab true in

			(* x2_v := i__getValue (x2) with err *)
			let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

			(* 	x_ret_0 := empty *)
			let x_ret_0 = fresh_var () in
			let x_ret_1 = fresh_var () in
			let x_ret_2 = fresh_var () in
			let x_ret_3 = fresh_var () in
			let x_ret_4 = fresh_var () in
			let x_ret_5 = fresh_var () in
			let cmd_ass_xret0 = LBasic (Assignment (x_ret_0, Literal Empty)) in

			(* goto [(x2_v = null) or (x2_v = undefined)] next6 next0;	*)
			let next0 = fresh_next_label () in
			let next1 = fresh_next_label () in
			let next2 = fresh_next_label () in
			let next3 = fresh_next_label () in
			let next4 = fresh_next_label () in
			let next5 = fresh_next_label () in
			let next6 = fresh_next_label () in
			let expr_goto_guard = BinOp (
				BinOp (Var x2_v, Equal, Literal Null),
				Or,
				BinOp (Var x2_v, Equal, Literal Undefined)) in
			let cmd_goto_null_undef = LGuardedGoto (expr_goto_guard, next6, next0) in

			(* x4 := "i__toObject" (x2_v) with err	 *)
			let x4 = fresh_var () in
			let cmd_to_obj_call = LCall (x4, Literal (String toObjectName), [ Var x2_v ], Some tr_ctx.tr_err) in

			(* xlf := "i__getAllEnumerableFields" (x4)  with err	*)
			let xlf = fresh_var () in
			let cmd_get_enum_fields = LCall (xlf, Literal (String getEnumFieldsName), [ Var x4 ], Some tr_ctx.tr_err) in

			(* xf  := getFields (xlf)  *)
			let xf = fresh_var () in
			let cmd_xf_ass = LBasic (GetFields (xf, Var xlf)) in

			(* len := l-len (xf)	 *)
			let len = fresh_var () in
			let cmd_ass_len = LBasic (Assignment (len, UnOp (LstLen, Var xf))) in

			(* x_c := 0 *)
			let x_c = fresh_var () in
			let cmd_ass_xc = LBasic (Assignment (x_c, Literal (Num 0.))) in

			(*   x_ret_1 := PHI(x_ret_0, x_ret_3)	 *)
			let cmd_ass_xret1 = LPhiAssignment (x_ret_1, [| (Var x_ret_0); (Var x_ret_3) |]) in

			(* x_c_1 := PSI(x_c, x_c_2);	 *)
			let x_c_1 = fresh_var () in
			let x_c_2 = fresh_var () in
			let cmd_ass_xc1 = LPsiAssignment (x_c_1, [| (Var x_c); (Var x_c_2) |]) in

			(* goto [x_c_1 < len] body end_loop  *)
			let cmd_goto_len = LGuardedGoto (BinOp (Var x_c_1, LessThan, Var len), body, end_loop) in

			(* xp := l-nth (xf, x_c_1)	*)
			let xp = fresh_var () in
			let cmd_ass_xp = LBasic (Assignment (xp, LstNth (Var xf, Var x_c_1))) in

			(* xl := [xlf, xp];	*)
			let xl = fresh_var () in
			let cmd_ass_xl = LBasic (Lookup (xl, Var xlf, Var xp)) in

			(*  xxl := l-nth (xl, 1)   *)
			let xxl = fresh_var () in
			let cmd_ass_xxl = LBasic (Assignment (xxl, LstNth (Var xl, Literal (Num 1.)))) in

			(* 	xhf := hasField (xxl, xp) *)
			let xhf = fresh_var () in
			let cmd_ass_hf = LBasic (HasField (xhf, Var xxl, Var xp)) in

			(* goto [xhf] next1 next3	 *)
			let cmd_goto_xhf = LGuardedGoto (Var xhf, next1, next3) in

			(* x5 := "i__putValue" (x1, xp) with err	 *)
			let x5, cmd_pv_x1 = make_put_value_call x1 xp tr_ctx.tr_err in

			(* x3_v = "i__getValue" (x3) with err *)
			let x3_v, cmd_gv_x3, errs_x3_v = make_get_value_call x3 tr_ctx.tr_err in

			(* x_ret_2 := PHI(cont_vars, x3_v) *)
			let phi_args = cur_conts @ [ x3_v ] in
			let phi_args = List.map (fun x -> Var x) phi_args in
			let phi_args = Array.of_list phi_args in
			let cmd_phi_cont = LPhiAssignment (x_ret_2, phi_args) in

			(* goto [ not (x_ret_2 = empty) ] next2 next3 *)
			let expr_goto_guard = BinOp (Var x_ret_2, Equal, Literal Empty) in
			let expr_goto_guard = UnOp (Not, expr_goto_guard) in
			let cmd_goto_xret2 = LGuardedGoto (expr_goto_guard, next2, next3) in

			(* x_ret_3 := PHI(x_ret_1, x_ret_2) *)
			let cmd_phi_xret3 = LPhiAssignment (x_ret_3, [| (Var x_ret_1); (Var x_ret_1); (Var x_ret_2) |]) in

			(* x_c_2 := x_c_1 + 1 *)
			let cmd_ass_incr = LBasic (Assignment (x_c_2, BinOp (Var x_c_1, Plus, Literal (Num 1.)))) in

			(* 	x_ret_4 := PHI(x_ret_1, break_vars)  *)
			let phi_args = x_ret_1 :: cur_breaks in
			let phi_args = List.map (fun x -> Var x) phi_args in
			let phi_args = Array.of_list phi_args in
			let cmd_phi_xret4 = LPhiAssignment (x_ret_4, phi_args) in

			(* goto [ x_ret_4 = empty ] next5 next6 *)
			let cmd_goto_xret4_empty = LGuardedGoto (
				BinOp (Var x_ret_4, Equal, Literal Empty), next5, next6) in

			(* x_ret_5 := PHI(x_ret_0, x_ret_1, x_ret_4) *)
			let cmd_phi_xret5 = LPhiAssignment (x_ret_5, [| (Var x_ret_0); (Var x_ret_1); (Var x_ret_4) |]) in

			let cmds1 = add_initial_label cmds1 next1 metadata in
			let cmds = cmds2 @ (annotate_cmds [           (*           cmds2                                                        *)
				(None,          cmd_gv_x2);               (*           x2_v := i__getValue (x2) with err                            *)
				(None,          cmd_ass_xret0);           (*           x_ret_0 := empty 		                                    *)
				(None,          cmd_goto_null_undef);     (*           goto [(x2_v = null) or (x2_v = undefined)] next6 next0   *)
				(Some next0,    cmd_to_obj_call);         (* next0:	   x4 := "i__toObject" (x2_v) with err			                *)
				(None,          cmd_get_enum_fields);     (*           xlf := "i__getAllEnumerableFields" (x4)  with err            *)
				(None,          cmd_xf_ass);              (*           xf  := getFields (xlf)                                       *)
				(None,          cmd_ass_len);             (*           len := l-len (xf)                                            *)
				(None,          cmd_ass_xc);              (*           x_c := 0                                                     *)
				(Some head,     cmd_ass_xret1);           (* head:     x_ret_1 := PHI(x_ret_0, x_ret_3)                             *)
				(None,          cmd_ass_xc1);             (*           x_c_1 := PSI(x_c, x_c_2) 		                            *)
				(None,          cmd_goto_len);            (*           goto [x_c_1 < len] body end_loop 	                        *)
				(Some body,     cmd_ass_xp);              (* body: 	   xp := l-nth (xf, x_c_1)		                                *)
				(None,          cmd_ass_xl);              (*           xl := [xlf, xp] 	                                            *)
				(None,          cmd_ass_xxl);             (*           xxl := l-nth (xl, 1)                                         *)
				(None,          cmd_ass_hf);              (*           xhf := hasField (xxl, xp)                                    *)
				(None,          cmd_goto_xhf)             (*           goto [xhf] next1 next4	                                    *)
			]) @ cmds1 @ (annotate_cmds [                 (* next1:    cmds1                                                        *)
			    (None,          cmd_pv_x1)                (*           x5 := "i__putValue" (x1, xp) with err	                    *)
			]) @ cmds3 @ (annotate_cmds [                 (*           cmds3                                                        *)
			    (None,          cmd_gv_x3);               (*           x3_v = "i__getValue" (x3) with err                           *)
				(Some cont,     cmd_phi_cont);            (* cont:     x_ret_2 := PHI(cont_vars, x3_v)                              *)
			    (None,          cmd_goto_xret2);          (*           goto [ not (x_ret_2 = empty) ] next2 next3                 *)
				(Some next2,    LBasic Skip);           (* next2:    skip                                                         *)
			    (Some next3,    cmd_phi_xret3);           (* next3:    x_ret_3 := PHI(x_ret_1, x_ret_1, x_ret_2)                    *)
				(Some next4,    cmd_ass_incr);            (* next4:	   x_c_2 := x_c_1 + 1                                           *)
				(None,          LGoto head);             (*           goto head                                                    *)
				(Some end_loop, cmd_phi_xret4);           (* end_loop: x_ret_4 := PHI(x_ret_1, break_vars)                          *)
			    (None,          cmd_goto_xret4_empty);    (*           goto [ x_ret_4 = empty ] next5 next6                       *)
			    (Some next5,    LBasic Skip);           (* next5:    skip                                                         *)
				(Some next6,    cmd_phi_xret5)            (* next6:    x_ret_5 := PHI(x_ret_0, x_ret_1, x_ret_4)                    *)
			]) in
			let errs = errs2 @ errs_x2_v @ [x4; xlf] @ errs1 @ [ x5 ] @ errs3 @ errs_x3_v in
			let cmds = annotate_first_cmd cmds in
			cmds, Var x_ret_5, errs, rets3, outer_breaks, outer_conts


  	| Parser_syntax.For (e1, e2, e3, e4) ->
		(**
		 Section 12.6.3
     *  C(e1) = cmds1, x1; C(e2) = cmds2, x2; C(e3) = cmds3, _; C(e4) = cmds4, x4
		 *
		 *  C( for(e1; e2; e3) { e4 } ) =
			        cmds1
					x1_v := i__getValue (x1) with err
					x_ret_0 := empty
			head:   x_ret_1 := PHI(x_ret_0, x_ret_3)
					cmds2
			        x2_v := i__getValue (x2) with err
					x2_b := i__toBoolean (x2_v) with err
					goto [x2_b] body end_loop
			body: 	cmds4
					x4_v := i__getValue (x4) with err
			cont:   x_ret_2 := PHI(cont_vars, x4_v)
					goto [ not (x_ret_2 = empty) ] next1 next2
		  	next1: 	skip
			next2:  x_ret_3 := PHI(x_ret_1, x_ret_2)
			        cmds3
					goto head
		  end_loop:	x_ret_4 := PHI(x_ret_1, break_vars)
			        goto [ x_ret_4 = empty ] next3 next4
			next3:  skip
			next4:  x_ret_5 := PHI(x_ret_4, x_ret_1)
		 *)

		let cmds1, x1, errs1 =
			(match e1 with
			| Some e1 -> fe e1
			| None ->
				let x1_v, cmd_ass_x1v = make_empty_ass () in
				[ annotate_cmd cmd_ass_x1v None ], Var x1_v, []) in
		(* x1_v := i__getValue (x1) with err *)
		let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in
		let cmds1, errs1 = cmds1 @ [ annotate_cmd cmd_gv_x1 None ], errs1 @ [ x1_v ] in

		let cmds2, x2, errs2 =
			(match e2 with
			| Some e2 -> fe e2
			| None ->
				let x2 = fresh_var () in
				let cmd_ass_x2 = annotate_cmd (LBasic (Assignment (x2, Literal (Bool true)))) None in
				[ cmd_ass_x2 ], Var x2, []) in

		let cmds3, _, errs3 =
			(match e3 with
			| Some e3 -> fe e3
			| None ->
				let x3_v, cmd_ass_x3v = make_empty_ass () in
				[ annotate_cmd cmd_ass_x3v None ], Var x3_v, []) in

		let head, guard, body, cont, end_loop = fresh_loop_vars () in

		let new_loop_list = (Some cont, end_loop, tr_ctx.tr_js_lab, true) :: tr_ctx.tr_loop_list in
		let new_ctx = update_tr_ctx ~previous:None ~lab:None ~loop_list:new_loop_list tr_ctx in
		let cmds4, x4, errs4, rets4, breaks4, conts4 = translate_statement new_ctx e4 in

		let cur_breaks, outer_breaks = filter_cur_jumps breaks4 tr_ctx.tr_js_lab true in
		let cur_conts, outer_conts = filter_cur_jumps conts4 tr_ctx.tr_js_lab true in

		(* x_ret_0 := empty  *)
		let x_ret_0, cmd_ass_ret_0 = make_empty_ass () in

		(* head:     x_ret_1 := PHI(x_ret_0, x_ret_3)  *)
		let x_ret_1 = fresh_var () in
		let x_ret_2 = fresh_var () in
		let x_ret_3 = fresh_var () in
		let cmd_ass_ret_1 = LPhiAssignment (x_ret_1, [| (Var x_ret_0); (Var x_ret_3) |]) in

		(* x2_v := i__getValue (x2) with err *)
		let x2_v, cmd_gv_x2, errs_x2_v = make_get_value_call x2 tr_ctx.tr_err in

	  	(* x2_b := i__toBoolean (x2_v) with err2 *)
		let x2_b, cmd_tb_x2 = make_to_boolean_call x2 x2_v tr_ctx.tr_err in

		(* goto [x2_b] body end_loop *)
		let body = fresh_loop_body_label () in
		let cmd_for_goto =  LGuardedGoto (Var x2_b, body, end_loop) in

		(* x4_v := i__getValue (x4) with err *)
		let x4_v, cmd_gv_x4, errs_x4_v = make_get_value_call x4 tr_ctx.tr_err in

		(* cont:     x_ret_2 := PHI(cont_vars, x4_v)  *)
		let cur_conts = cur_conts @ [ x4_v ] in
		let cur_conts = List.map (fun x -> Var x) cur_conts in
		let cont_vars = Array.of_list cur_conts in
		let cmd_ass_ret_2 = LPhiAssignment (x_ret_2, cont_vars) in

		(* 	goto [ not (x_ret_2 = empty) ] next1 next2  *)
		let next1 = fresh_next_label () in
		let next2 = fresh_next_label () in
		let expr_goto_guard = BinOp (Var x_ret_2, Equal, Literal Empty) in
		let expr_goto_guard = UnOp (Not, expr_goto_guard) in
		let cmd_goto_empty_test = LGuardedGoto (expr_goto_guard, next1, next2) in

		(* next2:    x_ret_3 := PHI(x_ret_1, x_ret_2) *)
		let cmd_ass_ret_3 = LPhiAssignment (x_ret_3, [| (Var x_ret_1); (Var x_ret_2) |]) in

		let cmds_end_loop, x_ret_5 = make_loop_end x_ret_1 x_ret_1 cur_breaks end_loop true in

		let cmds4 = add_initial_label cmds4 body metadata in

		let cmds = cmds1 @ (annotate_cmds [                    (*              cmds1                                        *)
					(None,             cmd_ass_ret_0);         (*              x_ret_0 := empty                           *)
					(Some head,        cmd_ass_ret_1);         (* head:        x_ret_1 := PHI(x_ret_0, x_ret_3)             *)
				]) @ cmds2 @ (annotate_cmds [                  (*              cmds2                                        *)
					(None,             cmd_gv_x2);             (*              x2_v := i__getValue (x2) with err            *)
					(None,             cmd_tb_x2);             (*              x2_b := i__toBoolean (x2_v) with err         *)
					(None,             cmd_for_goto);          (*              goto [x2_b] body end                         *)
				]) @ cmds4 @ (annotate_cmds [                  (* body:        cmds4                                        *)
					(None,             cmd_gv_x4);             (*              x4_v := i__getValue (x4) with err            *)
					(Some cont,        cmd_ass_ret_2);         (* cont:        x_ret_2 := PHI(cont_vars, x4_v)              *)
					(None,             cmd_goto_empty_test);   (*              goto [ not (x_ret_2 = empty) ] next1 next2 *)
					(Some next1,       LBasic Skip);         (* next1:       skip                                         *)
					(Some next2,       cmd_ass_ret_3);         (* next2:       x_ret_3 := PHI(x_ret_1, x_ret_2)             *)
				]) @ cmds3 @ (annotate_cmds [                  (*              cmds3                                        *)
				  (None,             LGoto head);             (*              goto head                                    *)
				]) @ (annotate_cmds cmds_end_loop) in
		let errs = errs1 @ errs2 @ errs_x2_v @ [ x2_b ] @ errs4 @ errs_x4_v @ errs3 in
		let cmds = annotate_first_cmd cmds in
		cmds, Var x_ret_5, errs, rets4, outer_breaks, outer_conts


	| Parser_syntax.Return e ->
		(**
      Section 12.9

			C(return) =
      			x_r := undefined;
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
			(* x_r := undefined *)
			let cmd_xr_ass = annotate_cmd (LBasic (Assignment (x_r, Literal Undefined))) None in
			(* goto lab_ret *)
			let cmd_goto_ret = annotate_cmd (LGoto tr_ctx.tr_ret_lab) None in
			let cmds = [ cmd_xr_ass; cmd_goto_ret] in
			let cmds = annotate_first_cmd cmds in
			cmds, Var x_r, [], [ x_r ], [], []

		| Some e ->
			let cmds, x, errs = fe e in
			(* x_r := i__getValue(x) with err *)
			let x_r, cmd_gv_x, errs_x_r = make_get_value_call x tr_ctx.tr_err in
			let cmd_gv_x = annotate_cmd cmd_gv_x None in
			(* goto ret_lab *)
			let cmd_goto_ret = annotate_cmd (LGoto tr_ctx.tr_ret_lab) None in
			let cmds = cmds @ [ cmd_gv_x; cmd_goto_ret] in
			let cmds = annotate_first_cmd cmds in
			cmds, Var x_r, errs @ errs_x_r, [ x_r ], [], [])


	| Parser_syntax.Continue lab ->
		(**
      Section 12.7

			find_continue_lab (lab) = jsil_lab
			---------------------------
			C(continue lab) =
      			x_r := empty;
      			goto jsil_lab

			next_continue_lab () = jsil_lab
			---------------------------
			C(continue) =
      			x_r := empty;
      			goto jsil_lab
		*)

		let x_r, cmd_ret =
			(match tr_ctx.tr_previous with
			| None ->
				let x_r, cmd = make_empty_ass () in
				x_r, [ annotate_cmd cmd None ]
			| Some (Literal lit) ->
				let x_r = fresh_var () in
				let cmd = LBasic (Assignment (x_r, Literal lit)) in
				x_r, [ annotate_cmd cmd None ]
			| Some (Var x) -> x, []
			| Some _ -> raise (Failure ("Continue: The return of the compilation must be either a variable or a literal"))) in

		(* goto lab_c *)
		let lab_c = get_continue_lab tr_ctx.tr_loop_list lab in
		let cmd_goto =  [ annotate_cmd (LGoto lab_c) None ] in

		let cmds = cmd_ret @ cmd_goto in
		let cmds = annotate_first_cmd cmds in
		cmds, Var x_r, [], [], [], [ (lab, x_r, lab_c) ]


	| Parser_syntax.Break lab ->
		(**
      	Section 12.8
      		x_r := empty;
      		goto lab_r
		*)

		let x_r, cmd_ret =
			(match tr_ctx.tr_previous with
			| None ->
				let x_r, cmd = make_empty_ass () in
				x_r, [ annotate_cmd cmd None ]
			| Some (Literal lit) ->
				let x_r = fresh_var () in
				let cmd = LBasic (Assignment (x_r, Literal lit)) in
				x_r,  [ annotate_cmd cmd None ]
			| Some (Var x) -> x, []
			| Some _ -> raise (Failure ("Continue: The return of the compilation must be either a variable or a literal"))) in

		(* goto lab_r *)
		let lab_r = get_break_lab tr_ctx.tr_loop_list lab in
		let cmd_goto = [ (annotate_cmd (LGoto lab_r) None) ] in

		let cmds = cmd_ret @ cmd_goto in
		let cmds = annotate_first_cmd cmds in
		cmds, Var x_r, [], [], [ (lab, x_r, lab_r) ], []


	| Parser_syntax.Label (js_lab, e) ->
		(** Section 12.12 *)
	  let new_ctx = update_tr_ctx ~lab:(Some js_lab) tr_ctx in
		translate_statement new_ctx e


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
		let cmds, x, errs = fe e in
		let x_v, cmd_gv_x, errs_x_v = make_get_value_call x tr_ctx.tr_err in
		let cmd_gv_x = [ annotate_cmd cmd_gv_x None ] in

		(* goto err  *)
		let cmd_goto = [ annotate_cmd (LGoto tr_ctx.tr_err) None ] in

		let cmds = cmds @                    (*  cmds                            *)
		           cmd_gv_x @                (*  x_v := i__getValue (x) with err *)
			       cmd_goto in               (*  goto err                        *)

		let cmds = annotate_first_cmd cmds in
		cmds, Literal Empty, errs @ errs_x_v @ [ x_v ], [], [], []


	| Parser_syntax.Try (e1, Some (x, e2), Some e3) ->
		(**
     	Section 12.14 - The try Statement
		 C(e1) = cmds1, x1; C(e2) = cmds2, x2; C(e3) = cmds3, x3
		 -----------------------------------------------------------
		  C(try { e1 } catch^{cid}(x) { e2 } finally { e3 } =
							cmds1
		            		goto finally
		    	err1:   	x_err := PHI(errs1)
				       		x_er := new ()
							[x_er, "x"] := x_err
							[x_scope, "cid"] := x_er
							cmds2
							goto finally
				err2:   	x_ret_1 := PHI(errs2)
				finally:  	x_ret_2 := PHI(breaks1, x_1, breaks2, x_2, x_ret_1)
				          	cmds3
		 	  	end:      	x_ret_3 := PHI(breaks3, x_ret_2)
		 *)

		let catch_id = try JS2JSIL_Preprocessing.get_codename e
				with _ -> raise (Failure "catch statements must be annotated with their respective code names - try - catch - finally") in
		let cmds, x, errs, rets, breaks, conts = make_try_catch_cmds_with_finally e1 (x, e2) catch_id e3 in
		let cmds = annotate_first_cmd cmds in
		cmds, x, errs, rets, breaks, conts


	| Parser_syntax.Try (e1, None, Some e3) ->
		(**
     Section 12.14 - The try Statement
		 C(e1) = cmds1, x1; C(e3) = cmds3, x3
		 -----------------------------------------------------------
		  C(try { e1 } finally { e3 } =
							cmds1
							goto finally
				err:     	x_ret_1 := PHI(errs1)
				finally: 	x_ret_2 := PHI(cur_breaks1, x_1, x_ret_1)
					        cmds3
			 	end:      	x_ret_3 := PHI(cur_breaks3, x_ret_2)
		 *)
		let cmds, x, errs, rets, breaks, conts =  make_try_finally_cmds e1 e3 in
		let cmds = annotate_first_cmd cmds in
		cmds, x, errs, rets, breaks, conts


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
			finally:  	x_ret_1 := PHI(breaks1, x_1, breaks2, x_2)
		 *)
		let catch_id = try JS2JSIL_Preprocessing.get_codename e
				with _ -> raise (Failure "catch statements must be annotated with their respective code names - try - catch - finally") in
		let cmds12, x_ret_1, errs12, rets12, breaks12, conts12, _ = make_try_catch_cmds e1 (x, e2) catch_id in
		let cmds = annotate_first_cmd cmds12 in
		cmds, Var x_ret_1, errs12, rets12, breaks12, conts12


	| Parser_syntax.Switch (e, xs) ->
		(**
      Section

			a_case = e_c, e_s
			C(e_c) = cmds1, x1
			C(e_s) = cmds2, x2
			--------------------------------------------------------
			C_case ( a_case, x_prev_found, x_switch_guard ) =
				           	goto [ not x_prev_found ] next1 next2
				next1:    	cmds1
				           	x1_v := getValue (x1) with err
							goto [ x1_v = x_switch_guard ] next2 end_case
				           	cmds2
				end_case:  	x_found := PHI(x_false, x_true)
				           	x_case := PSI(x_prev_case, x_2)



			C_case ( a_case ) = cmds1, x_prev_1
			C_a_cases ( a_cases ) = cmds2, x_prev_2
			--------------------------------------------------------
			C_cases ( a_case :: a_cases, x_prev, x_switch_guard ) =
				       	cmds1
						cmds2


			C(s) = cmds_def, x_def
			C(b_stmt_i) = cmds_i, x_i, for all b_stmt_i \in b_stmts
			---------------------------------------------------------
			C_default ( s, b_stmts, x_found_b, breaks_a) =
					            cmds_def
								goto [ not (x_found_b) ] next end_switch
				  next:       	cmds_1
					            ...
								cmds_n
				  end_switch: 	x_r := PHI(breaks_ab, breaks_def, x_def, breaks_b, x_n)



			C(e) = cmds_guard, x_guard
			C_cases (a_cases, x_found, x_guard_v) = cmds_a, x_found_a, x_a
			C_cases (b_cases, x_found_a, x_guard_v) = cmds_b, x_found_b, x_b
			C_defautl (default_case, b_stmts(b_cases), x_found_b) = cmds_default
			------------------------------------------------------
		  C(switch(e) { a_cases, default_case, b_cases} =
				            cmds_guard
							x_guard_v := i__getValue (x_guard) with err
							cmds_a
							goto [ x_found_a ] default b_cases
				b_cases:	cmds_b
				default:	x_found_b := PHI(x_false, x_false, x_true)
				            cmds_default

     *)
		let compile_case e s x_prev_found x_prev_case x_switch_guard end_switch js_lab fresh_end_case_label =
			let x_found = fresh_found_var () in
			let next1 = fresh_next_label () in
			let next2 = fresh_next_label () in

			let new_loop_list = (None, end_switch, tr_ctx.tr_js_lab, true) :: tr_ctx.tr_loop_list in
			let new_ctx = update_tr_ctx ~previous:None ~lab:None ~loop_list:new_loop_list tr_ctx in
			let cmds1, x1, errs1, _, _, _ = translate_statement new_ctx e in
			let cmds1 = add_initial_label cmds1 next1 metadata in

			let cmds2, x2, errs2, rets2, breaks2, conts2 = translate_statement new_ctx s in
			let cmds2, x2 = add_final_var cmds2 x2 metadata in
			let cmds2 = add_initial_label cmds2 next2 metadata in

			(* goto [ not x_prev_found ] next1 next2 *)
			let cmd_goto_1 = LGuardedGoto ( UnOp(Not, Var x_prev_found), next1, next2) in

			(* x1_v := getValue (x1) with err *)
			let x1_v, cmd_gv_x1, errs_x1_v = make_get_value_call x1 tr_ctx.tr_err in

			(* goto [ x1_v = x_switch_guard ] next2 end_case *)
			let next1 = fresh_next_label () in
			let end_case = fresh_end_case_label () in
			let cmd_goto_2 = LGuardedGoto ( BinOp(Var x1_v, Equal, Var x_switch_guard), next2, end_case) in

			(* x_found_2 := PHI(x_false, x_true)  *)
			let cmd_ass_xfound = LPhiAssignment (x_found, [| (Literal (Bool false)); (Literal (Bool true)) |]) in

			(* x_case := PSI(x_prev_case, x_2) *)
			let x_case = fresh_case_var () in
			let cmd_ass_case = LPsiAssignment (x_case, [| (Var x_prev_case); (Var x2) |]) in

			let cmds = (annotate_cmds [
				(None,          cmd_goto_1)           (*           goto [ not x_prev_found ] next1 next2          *)
			]) @ cmds1 @ (annotate_cmds [             (* next1:    cmds1                                          *)
	            (None,          cmd_gv_x1);           (*           x1_v := getValue (x1) with err                 *)
				(None,          cmd_goto_2);          (*           goto [ x1_v = x_switch_guard ] next2 end_case  *)
			]) @ cmds2 @ (annotate_cmds [             (* next2:    cmds2                                          *)
				(Some end_case, cmd_ass_xfound);      (* end_case: x_found := PHI(x_false, x_true)                *)
				(None,          cmd_ass_case)         (*           x_case := PSI(x_prev_case, x_2)                *)
			]) in
			let errs = errs1 @ errs_x1_v @ errs2 in
			cmds, x_case, errs, rets2, breaks2, conts2, x_found  in


		let compile_default s b_stmts x_old_b x_found_b end_switch js_lab cur_breaks_ab =
			let new_loop_list = (None, end_switch, js_lab, true) :: tr_ctx.tr_loop_list in
			let new_ctx = update_tr_ctx ~loop_list:new_loop_list ~previous:None ~lab:None tr_ctx in
			let f_default = translate_statement new_ctx in

			let cmds_def, x_def, errs_def, rets_def, breaks_def, conts_def = f_default s in
			let cmds_def, x_def = add_final_var cmds_def x_def metadata in
			let cmds_b, x_b, errs_b, rets_b, breaks_b, conts_b =
				List.fold_left (fun (cmds_ac, x_ac, errs_ac, rets_ac, breaks_ac, conts_ac) b_stmt ->
					let cur_b_cmds, x_b, cur_b_errs, cur_b_rets, cur_b_breaks, cur_b_conts = f_default b_stmt in
					let cur_b_cmds, x_b = add_final_var cur_b_cmds x_b metadata in
					cmds_ac @ cur_b_cmds, x_b, errs_ac @ cur_b_errs, rets_ac @ cur_b_rets, breaks_ac @ cur_b_breaks, conts_ac @ cur_b_conts)
					([], x_def, [], [], [], [])
					b_stmts in

			let cur_breaks_b, outer_breaks_b = filter_cur_jumps breaks_b js_lab true in
			let cur_breaks_def, outer_breaks_def = filter_cur_jumps breaks_def js_lab true in

			(* goto [ not (x_found_b) ] next end_switch *)
			let next = fresh_next_label () in
			let cmd_goto = LGuardedGoto( UnOp( Not, Var x_found_b), next, end_switch) in
			let cmds_def = add_initial_label cmds_def next metadata in

			(* x_r := PHI(breaks_ab, x_ab, breaks_def, breaks_b, x_b) *)
			let x_r = fresh_var () in
			let phi_args : string list = cur_breaks_ab @ [ x_old_b ] @ cur_breaks_def @ cur_breaks_b @ [ x_b ] in
			let phi_args = List.map (fun x -> Var x) phi_args in
			let phi_args = Array.of_list phi_args in
			let cmd_ass_xr = LPhiAssignment (x_r, phi_args) in

			let cmds =  [
				annotate_cmd cmd_goto None                 (*             goto [ not (x_found_b) ] next end_switch                *)
			] @ cmds_def                                 (* next:       cmds_def                                                *)
			  @ cmds_b  @ [                              (*             b_cmds                                                  *)
				annotate_cmd cmd_ass_xr (Some end_switch)  (* end_switch: x_r := PHI(breaks_ab, x_ab, breaks_def, breaks_b, x_b)  *)
			] in
			cmds, x_r, errs_def @ errs_b, rets_def @ rets_b, outer_breaks_def @ outer_breaks_b, conts_def @ conts_b in

		let filter_cases cases =
			List.fold_left (fun (a_cases, def, b_cases) case ->
				(match case, def with
				| (Parser_syntax.Case e, s), None -> (((e, s) :: a_cases), def, b_cases)
				| (Parser_syntax.DefaultCase, s), None -> (a_cases, Some s, b_cases)
				| (Parser_syntax.Case e, s), Some _ -> (a_cases, def, ((e, s) :: b_cases))
				| (Parser_syntax.DefaultCase, _), Some _ -> raise (Failure "No two defaults for the same try")))
			([], None, [])
			cases in

		let a_cases, def, b_cases = filter_cases xs in
		let a_cases, b_cases = List.rev a_cases, List.rev b_cases in
		let b_cases_lab, default_lab, end_switch, fresh_end_case_label = fresh_switch_labels () in
		let x_found_init = fresh_found_var () in

		let cmds_guard, x_guard, errs_guard = fe e in
		(* x_guard_v := i__getValue (x_guard) with err  *)
		let x_guard_v, cmd_gv_xguardv, errs_x_guard_v = make_get_value_call x_guard tr_ctx.tr_err in
		let cmd_gv_xguardv = annotate_cmd cmd_gv_xguardv None in
		(* x_found := false *)
		let cmd_x_found_init = annotate_cmd (LBasic (Assignment (x_found_init, Literal (Bool false)))) None in
		(* x_init_val := empty *)
		let x_init = fresh_var () in
		let cmd_val_init = annotate_cmd (LBasic (Assignment (x_init, Literal Empty))) None in

		let cmds_as, x_as, errs_as, rets_as, breaks_as, conts_as, x_found_as =
			List.fold_left
				(fun (cmds_ac, x_ac, errs_ac, rets_ac, breaks_ac, conts_ac, x_found_ac) (e, s) ->
					let cmds_a, x_a, errs_a, rets_a, breaks_a, conts_a, x_found_a = compile_case e s x_found_ac x_ac x_guard_v end_switch tr_ctx.tr_js_lab fresh_end_case_label in
					cmds_ac @ cmds_a, x_a, errs_ac @ errs_a, rets_ac @ rets_a, breaks_ac @ breaks_a, conts_ac @ conts_a, x_found_a)
				([], x_init, [], [], [], [], x_found_init)
				a_cases in
		let cmds_as = cmds_guard @ [ cmd_gv_xguardv; cmd_x_found_init; cmd_val_init ] @ cmds_as in
		let errs_as = errs_guard @ errs_x_guard_v @ errs_as in

		let cmds_bs, x_bs, errs_bs, rets_bs, breaks_bs, conts_bs, x_found_bs =
			List.fold_left
				(fun (cmds_bc, x_bc, errs_bc, rets_bc, breaks_bc, conts_bc, x_found_bc) (e, s) ->
					let cmds_b, x_b, errs_b, rets_b, breaks_b, conts_b, x_found_b = compile_case e s x_found_bc x_bc x_guard_v end_switch tr_ctx.tr_js_lab fresh_end_case_label in
					cmds_bc @ cmds_b, x_b, errs_bc @ errs_b, rets_bc @ rets_b, breaks_bc @ breaks_b, conts_bc @ conts_b, x_found_b)
				([], x_as, [], [], [], [], x_found_as)
				b_cases in

		(match b_cases, def with
		| [], None ->
			(*  end_switch: x_r := PHI(breaks_a, x_a) *)
			let x_r = fresh_var () in
			let cur_breaks_as, outer_breaks_as = filter_cur_jumps breaks_as tr_ctx.tr_js_lab true in
			let phi_args = cur_breaks_as @ [ x_as ] in
			let phi_args = List.map (fun x -> Var x) phi_args in
			let phi_args = Array.of_list phi_args in
			let cmd_end_switch = (annotate_cmd (LPhiAssignment (x_r, phi_args)) (Some end_switch)) in
			let cmds = cmds_as @ [ cmd_end_switch ] in
			let cmds = annotate_first_cmd cmds in
			cmds, Var x_r, errs_as, rets_as, outer_breaks_as, conts_as

		| [], Some def ->
			let new_loop_list = (None, end_switch, tr_ctx.tr_js_lab, true) :: tr_ctx.tr_loop_list in
			let new_ctx = update_tr_ctx ~previous:None ~lab:None ~loop_list:new_loop_list tr_ctx in
			let f_default = translate_statement new_ctx in
			let cmds_def, x_def, errs_def, rets_def, breaks_def, conts_def = f_default def in
			let cmds_def, x_def = add_final_var cmds_def x_def metadata in

			(*  end_switch: x_r := PHI(breaks_a, breaks_def, x_def) *)
			let x_r = fresh_var () in
			let cur_breaks_as, outer_breaks_as = filter_cur_jumps breaks_as tr_ctx.tr_js_lab true in
			let cur_breaks_def, outer_breaks_def = filter_cur_jumps breaks_def tr_ctx.tr_js_lab true in
			let phi_args = cur_breaks_as @ cur_breaks_def @ [ x_def ] in
			let phi_args = List.map (fun x -> Var x) phi_args in
			let phi_args = Array.of_list phi_args in
			let cmd_end_switch = (annotate_cmd (LPhiAssignment (x_r, phi_args)) (Some end_switch)) in
			let cmds = cmds_as @ cmds_def @ [ cmd_end_switch ] in
			let cmds = annotate_first_cmd cmds in
			cmds, Var x_r, errs_as @ errs_def, rets_as @ rets_def, outer_breaks_as @ outer_breaks_def, conts_as @ conts_def

	 	| _, Some def ->
			let b_stmts = List.map (fun (a, b) -> b) b_cases in
			let cmds_bs = add_initial_label cmds_bs b_cases_lab metadata in

			(* goto [ x_found_a ] default b_cases *)
			let cmd_goto_xfounda = (annotate_cmd (LGuardedGoto (Var x_found_as, default_lab, b_cases_lab)) None) in

			(* default:		x_found_b := PHI(x_false, x_found_b) *)
			let x_found_b = fresh_xfoundb_var () in
			let cmd_ass_xfoundb = (annotate_cmd (LPhiAssignment (x_found_b, [| (Literal (Bool false)); (Var x_found_bs) |])) (Some default_lab)) in

			let cur_breaks_as, outer_breaks_as = filter_cur_jumps breaks_as tr_ctx.tr_js_lab true in
			let cur_breaks_bs, outer_breaks_bs = filter_cur_jumps breaks_bs tr_ctx.tr_js_lab true in
			let cur_breaks_ab = cur_breaks_as @ cur_breaks_bs in

			let cmds_def, x_def, errs_def, rets_def, outer_breaks_def, conts_def = compile_default def b_stmts x_bs x_found_b end_switch tr_ctx.tr_js_lab cur_breaks_ab in
			let cmds = cmds_as @ [ cmd_goto_xfounda ] @ cmds_bs @ [ cmd_ass_xfoundb ] @ cmds_def in
			let cmds = annotate_first_cmd cmds in
			cmds, Var x_def, errs_as @ errs_bs @ errs_def, rets_as @ rets_bs @ rets_def, outer_breaks_as @ outer_breaks_bs @ outer_breaks_def, conts_as @ conts_bs @ conts_def

		| _, _ -> raise (Failure "no b cases with no default"))


	| Parser_syntax.Function (_, n, params, e_body) -> [], Literal Empty, [], [], [], []

  | Parser_syntax.With (_, _) -> raise (Failure "Not implemented: with (this should not happen)")
	| Parser_syntax.RegExp (_, _) -> raise (Failure "Not implemented: RegExp literal")


let make_final_cmd vars final_lab final_var =
	let cmd_final =
		(match vars with
		| [] -> LBasic Skip
		| [ x ] -> LBasic (Assignment (final_var, Var x))
		| _ ->
			let vars = List.map (fun x_r -> (Var x_r)) vars in
			let vars = Array.of_list vars in
			LPhiAssignment (final_var, vars)) in
	(empty_metadata, (Some final_lab), cmd_final)



let translate_fun_decls (top_level : bool) (sc_var : string) (cur_index : int) e  =
	let f_decls = func_decls_in_exp e in
	let hoisted_fdecls =
		List.fold_left (fun ac f_decl ->
			let f_name, f_params =
				(match f_decl.Parser_syntax.exp_stx with
				| Parser_syntax.Function (s, Some f_name, f_params, body) -> f_name, f_params
				| _ -> raise (Failure "expected function declaration")) in
			let f_id = JS2JSIL_Preprocessing.get_codename f_decl in
			let f_cmds, _, _ = translate_named_function_literal top_level sc_var f_name f_id f_params cur_index in
			ac @ f_cmds)
			[]
			f_decls in
		hoisted_fdecls



let generate_main offset_converter e spec =
	let annotate_cmd cmd lab = (empty_metadata, lab, cmd) in
	let annotate_cmds cmds =
		List.map
			(fun (lab, cmd) ->
				(empty_metadata, lab, cmd))
		cmds in

	let new_var = fresh_var () in
	let setup_heap_ass =  annotate_cmd (LCall (new_var, Literal (String setupHeapName), [ ], None)) None in
	let sc_var_main = JS2JSIL_Constants.var_scope in

	(* x_sc := {{ $lg }} *)
	let init_scope_chain_ass = annotate_cmd (LBasic (Assignment (sc_var_main, Literal (LList [ Loc locGlobName ])))) None in

	let sc_var_main = JS2JSIL_Constants.var_sc_first in
 
 	(* x_sc_fst := {{ $lg }} *)
 	let init_scope_chain_ass_again = annotate_cmd (LBasic (Assignment (sc_var_main, Literal (LList [ Loc locGlobName ])))) None in

	(* __this := $lg *)
	let this_ass = annotate_cmd (LBasic (Assignment (var_this, Literal (Loc locGlobName)))) None in

	(* global vars init assignments: [$lg, y] := {{ "d", undefined, true, true, true }} *)
	let global_var_asses =
		List.map
			(fun global_v ->
				(annotate_cmd
					(LBasic (Mutation(Literal (Loc locGlobName),  Literal (String global_v), Literal (LList [(String "d"); Undefined; (Bool true); (Bool true); (Bool false)]), None)))
					None))
			(var_decls e) in

	(* x__te := TypeError () *)
	let cmd_ass_te = make_var_ass_te () in
	let cmd_ass_te = annotate_cmd cmd_ass_te None in

	(* x__te := SyntaxError () *)
	let cmd_ass_se = make_var_ass_se () in
	let cmd_ass_se = annotate_cmd cmd_ass_se None in

	let ctx = make_translation_ctx offset_converter main_fid [ main_fid ] sc_var_main in
	let cmds_hoist_fdecls = translate_fun_decls true sc_var_main 0 e in
	let cmds_hoist_fdecls = annotate_cmds_top_level empty_metadata cmds_hoist_fdecls in
	let cmds_e, x_e, errs, _, _, _ = translate_statement ctx e in
	(* List.iter (fun ({ line_offset; invariant; pre_logic_cmds; post_logic_cmds }, _, _) ->
		Printf.printf "Length: pre: %d \t post: %d\n" (List.length pre_logic_cmds) (List.length post_logic_cmds)) cmds_e; *)

	(* x_ret := x_e *)
	let ret_ass = annotate_cmd (LBasic (Assignment (ctx.tr_ret_var, x_e))) None in

	let cmd_del_te = annotate_cmd (LBasic (DeleteObj (Var var_te))) None in
	let cmd_del_se = annotate_cmd (LBasic (DeleteObj (Var var_se))) None in

	(* lab_ret: skip *)
	let lab_ret_skip = annotate_cmd (LBasic Skip) (Some ctx.tr_ret_lab) in

	let cmd_err_phi_node = make_final_cmd errs ctx.tr_err ctx.tr_error_var in

	let main_cmds =
		[ setup_heap_ass; init_scope_chain_ass; init_scope_chain_ass_again; this_ass] @
		global_var_asses @
		[ cmd_ass_te; cmd_ass_se ] @
		cmds_hoist_fdecls @
		cmds_e @
		[ret_ass; cmd_del_te; cmd_del_se; lab_ret_skip; cmd_err_phi_node ] in
	{
		lproc_name = main_fid;
    	lproc_body = (Array.of_list main_cmds);
    	lproc_params = [];
		lret_label = Some ctx.tr_ret_lab;
		lret_var = Some ctx.tr_ret_var;
		lerror_label = Some ctx.tr_err;
		lerror_var = Some ctx.tr_error_var;
		lspec = spec
	}

let generate_proc_eval new_fid e vis_fid =
	let annotate_cmd cmd lab = (empty_metadata, lab, cmd) in
	let annotate_cmds cmds =
		List.map
			(fun (lab, cmd) ->
				(empty_metadata, lab, cmd))
		cmds in
	let offset_converter x = 0 in
	let var_sc_proc = JS2JSIL_Constants.var_sc_first in

	(* x_er_m := new (null)   *)
	(* x_er   := new (x_er_m) *)
	let x_er = JS2JSIL_Constants.var_er in
	let x_erm = JS2JSIL_Constants.var_er_metadata in
	let cmd_er_m_creation = annotate_cmd (LBasic (New (x_erm, Some (Literal Null)))) None in
	let cmd_er_creation = annotate_cmd (LBasic (New (x_er, Some (Var x_erm)))) None in

	(* [x_er, "@er"] := true *)
  let cmd_er_flag = annotate_cmd (LBasic (Mutation (Var x_erm, Literal (String _erFlagPropName), Literal (Bool true), None))) None in

	(* [x_er, decl_var_i] := undefined *)
	let new_fid_vars = var_decls e in
	let cmds_decls =
		List.map (fun decl_var ->
			let cmd = LBasic (Mutation (Var x_er, Literal (String decl_var), Literal Undefined, None)) in
			(annotate_cmd cmd None))
		new_fid_vars in

	(* x_sc_0 = x_scope @ {{ x_er }}  *)
	let cmd_ass_er_to_sc = annotate_cmd  (LBasic (Assignment (var_sc_proc, (BinOp ((Var var_scope), LstCat, EList [ (Var var_er) ]))))) None in


	(* x__te := TypeError () *)
	let cmd_ass_te = make_var_ass_te () in
	let cmd_ass_te = annotate_cmd cmd_ass_te None in
	(* x__te := SyntaxError () *)
	let cmd_ass_se = make_var_ass_se () in
	let cmd_ass_se = annotate_cmd cmd_ass_se None in

	let ctx = make_translation_ctx offset_converter new_fid vis_fid var_sc_proc in

	let fake_ret_label = fresh_label () in
	let fake_ret_var = fresh_var () in
	let ret_label = ctx.tr_ret_lab in
	let ret_var = ctx.tr_ret_var in
	let new_ctx = { ctx with tr_ret_lab = fake_ret_label;  tr_ret_var = fake_ret_var } in
	let cmds_hoist_fdecls = translate_fun_decls false var_sc_proc ((List.length vis_fid)-1) e in
	let cmds_hoist_fdecls = annotate_cmds cmds_hoist_fdecls in
	let cmds_e, x_e, errs, rets, _, _ = translate_statement new_ctx e in

	let xe_v, cmd_gv_xe, errs_xe_v = make_get_value_call x_e ctx.tr_err in
	let cmd_gv_xe = annotate_cmd cmd_gv_xe None in

	(* ret_lab: x_ret := xe_v *)
	let cmd_dr_ass = annotate_cmd (LBasic (Assignment (ctx.tr_ret_var, Var xe_v))) (Some ctx.tr_ret_lab) in

	(* fake_ret_lab: x_fake_ret := PHI(rets) *)
	let cmd_fake_ret = make_final_cmd rets new_ctx.tr_ret_lab new_ctx.tr_ret_var in
	(* lab_err: x_error := PHI(errs, x_fake_ret) *)
	let cmd_error_phi = make_final_cmd (errs @ errs_xe_v) ctx.tr_err ctx.tr_error_var in

	let fid_cmds =
		[ cmd_er_m_creation; cmd_er_creation; cmd_er_flag ] @ cmds_decls @ [ cmd_ass_er_to_sc; cmd_ass_te; cmd_ass_se ] @ cmds_hoist_fdecls @ cmds_e
		@ [ cmd_gv_xe; cmd_dr_ass; cmd_fake_ret; cmd_error_phi] in
	{
		lproc_name = new_fid;
    lproc_body = (Array.of_list fid_cmds);
		lproc_params = [ var_scope; var_this ];
		lret_label = Some ctx.tr_ret_lab;
		lret_var = Some ctx.tr_ret_var;
		lerror_label = Some ctx.tr_err;
		lerror_var = Some ctx.tr_error_var;
		lspec = None
	}




let generate_proc offset_converter e fid params vis_fid spec =
	let annotate_cmd cmd lab = (empty_metadata, lab, cmd) in
	let annotate_cmds cmds =
		List.map
			(fun (lab, cmd) ->
				(empty_metadata, lab, cmd))
		cmds in

	let var_sc_proc = JS2JSIL_Constants.var_sc_first in
	let ctx = make_translation_ctx offset_converter fid vis_fid var_sc_proc in

	let new_ctx = { ctx with tr_ret_lab = ("pre_" ^ ctx.tr_ret_lab); tr_err = ("pre_" ^ ctx.tr_err) } in
	let cmds_hoist_fdecls = translate_fun_decls false var_sc_proc ((List.length vis_fid)-1) e in
	let cmds_hoist_fdecls = annotate_cmds_top_level empty_metadata cmds_hoist_fdecls in

	(* x_er_m := new (null)   *)
	(* x_er   := new (x_er_m) *)
	let cmd_er_m_creation = annotate_cmd (LBasic (New (var_er_metadata, Some (Literal Null)))) None in
	let cmd_er_creation = annotate_cmd (LBasic (New (var_er, Some (Var var_er_metadata)))) None in

	(* [x_er, "@er"] := true *)
  let cmd_er_flag = annotate_cmd (LBasic (Mutation (Var var_er_metadata, Literal (String _erFlagPropName), Literal (Bool true), None))) None in

	(* [x_er, "arg_i"] := x_{i+2} *)
	let cmds_params =
		List.map (fun param ->
			let cmd = LBasic (Mutation (Var var_er, Literal (String param), Var param, None)) in
			(annotate_cmd cmd None))
		params in

	(* [x_er, decl_var_i] := undefined *)
	let cmds_decls =
		List.map (fun decl_var ->
			let cmd = LBasic (Mutation (Var var_er, Literal (String decl_var), Literal Undefined, None)) in
			(annotate_cmd cmd None))
		(var_decls e) in

	(**
      CREATING THE ARGUMENTS OBJECT:
			x_argList_pre := args;
			x_argList_act := cdr (cdr (x_argList_pre));
			x_args := "create_arguments_object" (x_argList_act) with err;
			[x_er, "arguments"] := x_args;
	*)

	let x_argList_pre = fresh_var () in
	let x_argList_act = fresh_var () in
	let x_args = fresh_var () in
	let cmds_arg_obj =
		[
			(empty_metadata, None, LBasic (Arguments (x_argList_pre)));
			(empty_metadata, None, LBasic (Assignment (x_argList_act, UnOp (Cdr, (UnOp (Cdr, Var x_argList_pre))))));
			(empty_metadata, None, LCall  (x_args, Literal (String createArgsName), [ Var x_argList_act ], None));
			(empty_metadata, None, LBasic (Mutation (Var var_er, Literal (String "arguments"), Var x_args, None)))
		] in 

	(* x_sc_0 = x_scope @ {{ x_er }} *)
	let cmd_ass_er_to_sc = annotate_cmd  (LBasic (Assignment (var_sc_proc, (BinOp ((Var var_scope), LstCat, EList [ (Var var_er) ]))))) None in

	(* x__te := TypeError () *)
	let cmd_ass_te = make_var_ass_te () in
	let cmd_ass_te = annotate_cmd cmd_ass_te None in
	(* x__te := SyntaxError () *)
	let cmd_ass_se = make_var_ass_se () in
	let cmd_ass_se = annotate_cmd cmd_ass_se None in

	let cmds_e, x_e, errs, rets, _, _ = translate_statement new_ctx e in
	(* List.iter (fun ({ line_offset; invariant; pre_logic_cmds; post_logic_cmds }, _, _) ->
		Printf.printf "Length: pre: %d \t post: %d\n" (List.length pre_logic_cmds) (List.length post_logic_cmds)) cmds_e; *)

	(* x_dr := empty *)
	let x_dr = fresh_var () in
	let cmd_dr_ass = annotate_cmd (LBasic (Assignment (x_dr, Literal Empty))) None in
	let rets = rets @ [ x_dr ] in

	(* x_scope_final := x_scope *)
	let cmd_xscope_final = annotate_cmd (LBasic (Assignment (JS2JSIL_Constants.var_scope_final, Var var_sc_proc))) None in

	(* pre_lab_ret: x_return := PHI(...) *)
	let cmd_return_phi = make_final_cmd rets new_ctx.tr_ret_lab new_ctx.tr_ret_var in

	let cmd_del_te = annotate_cmd (LBasic (DeleteObj (Var var_te))) None in
	let cmd_del_se = annotate_cmd (LBasic (DeleteObj (Var var_se))) None in
	let cmd_ret_final = annotate_cmd (LBasic (Skip)) (Some ctx.tr_ret_lab) in

	(*
	let cmds_restore_er_ret = generate_proc_er_restoring_code fid x_er_old ctx.tr_ret_lab in
	let cmds_restore_er_ret = annotate_cmds cmds_restore_er_ret in *)

	let errs = errs in
	let cmd_error_phi = make_final_cmd errs new_ctx.tr_err new_ctx.tr_error_var in
	let cmd_err_final =  annotate_cmd (LBasic (Skip)) (Some ctx.tr_err) in

	let fid_cmds =
		[ cmd_er_m_creation; cmd_er_creation; cmd_er_flag ] @
		cmds_decls @ cmds_params @
		(if_verification [] cmds_arg_obj) @
		[ cmd_ass_er_to_sc; cmd_ass_te; cmd_ass_se ] @
		cmds_hoist_fdecls @ cmds_e @
		[ cmd_dr_ass; cmd_return_phi; cmd_del_te; cmd_del_se; cmd_xscope_final; cmd_ret_final; cmd_error_phi; cmd_xscope_final; cmd_err_final ] in
	{
		lproc_name = fid;
    	lproc_body = (Array.of_list fid_cmds);
    	lproc_params = var_scope :: var_this :: params;
		lret_label = Some ctx.tr_ret_lab;
		lret_var = Some ctx.tr_ret_var;
		lerror_label = Some ctx.tr_err;
		lerror_var = Some ctx.tr_error_var;
		lspec = spec
	}


(**** EVAL ****)
let js2jsil_eval prog which_pred cc_tbl (vis_tbl : vis_tbl_type option) fid_parent e =

	let offset_converter x = 0 in

	let cc_tbl, vis_tbl =
		(match cc_tbl, vis_tbl with
 		| None, None -> raise (Failure "Wrong call to eval: both cc_table and vis_tbl undefined")
 		| None, _ -> raise (Failure "Wrong call to eval: cc_table undefined")
		| _, None -> raise (Failure "Wrong call to eval: vis_tbl undefined")
 		| Some cc_tbl, Some vis_tbl -> cc_tbl, vis_tbl) in

	let e, fid_eval, vislist_eval, eval_fun_tbl = JS2JSIL_Preprocessing.preprocess_eval cc_tbl vis_tbl e fid_parent [] in

	Hashtbl.iter
		(fun f_id (_, f_params, f_body, _) ->
			Option.may
				(fun f_body ->
					let proc =
						(if (f_id = fid_eval)
							then generate_proc_eval fid_eval e vislist_eval
							else
								(let vislist =
									try Hashtbl.find vis_tbl f_id
										with _ ->
											(let msg = Printf.sprintf "EV: Function %s not found in visibility table" f_id in
											raise (Failure msg)) in
    						let f_params = 
    	  					(match f_params with
    	  					| "x__scope" :: "x__this" :: rest -> rest
    	  					| "x__scope" :: rest -> rest
    	  					| _ -> f_params) in
								generate_proc offset_converter f_body f_id f_params vislist None)) in
					  let proc_eval_str = JSIL_Print.string_of_ext_procedure proc in
		   			  Printf.printf "EVAL wants to run the following proc:\n %s\n" proc_eval_str;
					let proc = JSIL_Syntax_Utils.desugar_labs proc in
					Hashtbl.add prog f_id proc;
					JSIL_Syntax_Utils.extend_which_pred which_pred proc) f_body)
		eval_fun_tbl;

	let proc_eval = try Hashtbl.find prog fid_eval with _ -> raise (Failure "no eval proc was created") in
	proc_eval


(* FUNCTION CONSTRUCTOR *)
let js2jsil_function_constructor_prop prog which_pred cc_tbl vis_tbl fid_parent params e =

	let offset_converter x = 0 in

	let cc_tbl, vis_tbl =
		(match cc_tbl, vis_tbl with
 		| None, None -> raise (Failure "Wrong call to function constructor: both cc_table and vis_tbl undefined")
 		| None, _ -> raise (Failure "Wrong call to function constructor: cc_table undefined")
 		| _, None -> raise (Failure "Wrong call to function constructor: vis_tbl undefined")
 		| Some cc_tbl, Some vis_tbl -> cc_tbl, vis_tbl) in

	let e, new_fid, vislist, new_fun_tbl = JS2JSIL_Preprocessing.preprocess_eval cc_tbl vis_tbl e "main" params in

	Hashtbl.iter
		(fun f_id (_, f_params, f_body, _) ->
		  Option.may
		  	(function f_body ->
				let proc =
	  				(let vis_fid = try Hashtbl.find vis_tbl f_id
	  					with _ ->
	  						(let msg = Printf.sprintf "Function %s not found in visibility table" f_id in
	  						raise (Failure msg)) in
						let f_params = 
	  					(match f_params with
	  					| "x__scope" :: "x__this" :: rest -> rest
	  					| "x__scope" :: rest -> rest
	  					| _ -> f_params) in
						(* WHY WAS THIS HERE????? let f_params = List.tl (List.tl f_params) in *)
	  				generate_proc offset_converter f_body f_id f_params vis_fid None) in
			  		(* let proc_str = JSIL_Print.string_of_ext_procedure proc in
			  		  Printf.printf "Function constructor proc to execute:\n%s\n" proc_str; *)
					let proc = JSIL_Syntax_Utils.desugar_labs proc in
					Hashtbl.replace prog f_id proc;
					JSIL_Syntax_Utils.extend_which_pred which_pred proc) f_body)
		new_fun_tbl;
	let proc_fun_constr = try Hashtbl.find prog new_fid with _ -> raise (Failure "no function constructor proc was created") in
	proc_fun_constr



let js2jsil e offset_converter for_verification =
	let e, only_specs, predicates = JS2JSIL_Preprocessing.preprocess cc_tbl fun_tbl vis_tbl e in
	let procedures = Hashtbl.create medium_tbl_size in
	let proc_names =
		Hashtbl.fold
			(fun f_id (_, f_params, f_body, spec) ac ->
				Option.map_default
					(fun f_body ->
						(* print_normal (Printf.sprintf "Procedure %s is recursive?! %b" f_id f_rec); *)
						let proc =
							(if (f_id = main_fid)
								then generate_main offset_converter e spec
								else
									(let vis_fid = try Hashtbl.find vis_tbl f_id
										with _ ->
											(let msg = Printf.sprintf "Function %s not found in visibility table" f_id in
											raise (Failure msg)) in
									generate_proc offset_converter f_body f_id f_params vis_fid spec)) in
						Hashtbl.add procedures f_id proc;
						f_id :: ac) ac f_body)
			fun_tbl
			[] in

	let cur_imports = if for_verification then js2jsil_logic_imports else js2jsil_imports in
  (* TODO: Populate table with actual lemmas *)
  let lemmas : (string, jsil_lemma) Hashtbl.t = Hashtbl.create 511 in
	{ imports = cur_imports; lemmas; predicates; onlyspecs = only_specs; procedures; procedure_names = proc_names;}, cc_tbl, vis_tbl
