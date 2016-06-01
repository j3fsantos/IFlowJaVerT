open Utils
open Lexing
open Batteries
open SSyntax

let js2jsil_imports = [
	"Array"; 
	"Boolean";
	"Function"; 
	"internals"; 
	"Number"; 
	"Object"; 
	"String"
]

let bodyPropName = "@body"
let scopePropName = "@scope"

let getValueName = "i__getValue"
let isReservedName = "i__isReserved"
let putValueName = "i__putValue"
let objectConstructName = "Object_construct"
let toObjectName = "i__toObject"
let deletePropertyName = "o__deleteProperty"
let syntaxErrorName = "SyntaxError"
let typeErrorName = "TypeError"
let createFunctionObjectName = "create_function_object"
let isCallableName = "i__isCallable"

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
 
let fresh_label : (unit -> string) = fresh_sth "lab_"

let fresh_err_label : (unit -> string) = fresh_sth "err_"

type tr_ctx = { 
	tr_ret_lab: string; 
	tr_ret_var: string;
	tr_error_lab: string; 
	tr_error_var: string;
}

let make_translation_ctx fid = 
{ 
	tr_ret_lab = "lab_ret_" ^ fid; 
	tr_ret_var = "var_ret_" ^ fid;
	tr_error_lab = "err_lab_" ^ fid; 
	tr_error_var = "err_var_" ^ fid
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

let var_this = "x__this"  
let var_scope = "x__scope"  


(**
Variable x::
	Found in the closure clarification table: Phi(fid_1, x) = fid_2
					x_1 := [__scope_chain, fid_2]; 
					x_2 := ref_v(x_1, "x")
	
	Not found in the closure clarification table: Phi(fid_1, x) = bot
					x_1 := proto_field($lg, "x"); 
					goto [x_1 = $$undefined] lab1 lab2
		lab1: x_2 := ref_v($$undefined, "x"); 
		      goto lab3; 
		lab2: x_2 := ref_v($lg, "x"); 
		lab3: skip  	 
 *)
let translate_var_found fid js_var new_var = 
	let tmpl :  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g, unit, string) format = 
" 			%s := [%s, %s]; 
				%s := ref_v(%s, \"%s\")"
	in
	let x_1 = fresh_var () in 
	let target_code_str = Printf.sprintf tmpl x_1 var_scope fid new_var x_1 js_var in 
	parse target_code_str

let translate_var_not_found fid js_var new_var = 
	let lab1 = fresh_label () in 
	let lab2 = fresh_label () in 
	let lab3 = fresh_label () in 
	let x_1 = fresh_var () in 
	let x_2 = fresh_var () in 
	let tmpl :  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i -> 'j -> 'k -> 'l -> 'm -> 'n, unit, string) format = 
"				%s := proto_field($lg, \"%s\"); 
				goto [%s = $$undefined] %s %s; 
	%s: 	%s := ref_v($$undefined, \"%s\"); 
		    goto %s; 
	%s:		%s := ref_v($lg, \"%s\"); 
	%s: 	skip"
	in 
	let target_code_str = Printf.sprintf tmpl x_1 js_var x_1 lab1 lab2 lab1 x_2 js_var lab3 lab2 new_var js_var lab3 in 
	parse target_code_str




let rec translate fid cc_table loop_list ctx e = 
	
	let f = translate fid cc_table loop_list ctx in 
	
	match e.Parser_syntax.exp_stx with 
	
	(* Literals *)
	| Parser_syntax.Null ->  [], Literal Null, []
	| Parser_syntax.Bool b -> [], Literal (Bool b), []
	| Parser_syntax.String s -> [], Literal (String s), []
	| Parser_syntax.Num n ->  [], Literal (Num n), []    
	
	(* expressions *)
	
	| Parser_syntax.This ->
		(* x := __this	*)
		let new_var = fresh_var () in 
		let cmd = SLBasic (SAssignment (new_var, (Var var_this))) in
		let cmds = [
			None, None, cmd
		] in  
		cmds, Var new_var, [] 
		
	| Parser_syntax.Var v -> 
		let new_var = fresh_var () in 
		let cur_var_tbl = 
			(try Hashtbl.find cc_table fid 
			with _ -> 
				let msg = Printf.sprintf "var tbl of function %s is not in cc-table" fid in 
				raise (Failure msg)) in 
		let v_fid = (try Some (Hashtbl.find cur_var_tbl v)
			with _ -> None) in 
		(match v_fid with 
		| None -> translate_var_not_found v_fid v new_var, Var new_var, [] 
		| Some v_fid -> translate_var_found v_fid v new_var, Var new_var, [])
	
	| Parser_syntax.Script (_, es)  
	| Parser_syntax.Block es -> 
		(match es with 
		| [] -> 
			let new_var = fresh_var () in 
			let empty_ass = (None, None, SLBasic (SAssignment (new_var, (Literal Empty)))) in 
			[ empty_ass ], (Var new_var), []
		| es -> 
			let rec loop es cmd_lst err_lst = 
				(match es with 
				| [] -> raise (Failure "block list cannot be empty HERE" )
				| [ e ] -> 
					let cmds_e, x_e, err_e = f e in
					cmd_lst @ cmds_e, x_e, (err_e @ err_lst)  
				| e :: rest_es -> 
					let cmds_e, _, err_e = f e in 
					loop rest_es (cmd_lst @ cmds_e) (err_e @ err_lst)) in
			loop es [] []) 
	
	| Parser_syntax.VarDec decs -> 
		let rec loop decs cmds last_e_x errs = 
			(match decs with 
			| [] -> 
				(match last_e_x with 
				| None ->
					let new_var = fresh_var () in 
					let empty_ass = (None, None, SLBasic (SAssignment (new_var, (Literal Empty)))) in
					cmds @ [ empty_ass ], Var new_var, errs 
				| Some e_x -> cmds, e_x, errs)
			| (v, eo) :: rest_decs -> 
				(match eo with 
				| None -> loop rest_decs cmds last_e_x errs
				| Some e -> raise (Failure "not implemented yet!"))) in 
		loop decs [] None [] 
		
	| Parser_syntax.Assign (e1, e2) ->
		(**
			       x2_val := getValue (x2) with err1;
					   x_ir := is_reserved(x1); 
			 		   goto [(((TypeOf(x1) = $$VarReferenceType) && x_ir) || (base(x1) = $$undefined))] err2 next1; 
	   next1:  x_pv = putValue (x1, x2) with err3; 

	   err1:   x_err := x2_val 
		 err2:   x_err := 
		 err3:   x_err := x_pv 
     *)
		let x_ir = fresh_var () in 
		let x_e2_val = fresh_var () in 
		let x_pv = fresh_var () in  
		let lab_next1 = fresh_label () in 
		let lab_err1 = fresh_err_label () in 
		let lab_err2 = fresh_err_label () in 
		let lab_err3 = fresh_err_label () in 
		
		let cmds_e1, x_e1, err_cmds1 = f e1 in 
		let cmds_e2, x_e2, err_cmds2 = f e2 in 
		
		(* x_e2_val := getValue (x2) with err1 *)
		let cmd_gv_e2 = SLCall (x_e2_val, Literal (String getValueName), [ x_e2 ], Some lab_err1) in 
		(* x_is_reserved := is_reserved (x1) *)
		let cmd_ir_e1 = SLCall (x_ir, Literal (String isReservedName), [x_e1], None) in 
		(* (((TypeOf(x1) = $$VarReferenceType) && x_ir) || (base(x1) = $$undefined)) *)
		let is_invalid_ass_exp = BinOp ((TypeOf x_e1), Equal, (Literal (Type VariableReferenceType))) in 
		let is_invalid_ass_exp = BinOp ((Var x_ir), And, is_invalid_ass_exp) in 
		let is_invalid_ass_exp = BinOp (is_invalid_ass_exp, Or, (BinOp ((Base x_e1), Equal, (Literal Undefined)))) in
		(* goto [is_invalid_assignment] err2 next *) 
		let cmd_guarded_goto = SLGuardedGoto (is_invalid_ass_exp, lab_err2, lab_next1) in 
		(* next: x_pv = putValue (x1, x_e2_val) with err3 *)
		let cmd_put_value = SLCall (x_pv, Literal (String putValueName), [x_e1; (Var x_e2_val)], Some lab_err3) in 
		
		let new_cmds = [
			(None, None, cmd_gv_e2); 
			(None, None, cmd_ir_e1); 
			(None, None, cmd_guarded_goto); 
			(None, Some lab_next1, cmd_put_value)
		] in 
		let cmds = List.concat [ cmds_e1; cmds_e2; new_cmds ] in 
		
		let new_err_cmds = [
			(lab_err1, SLBasic (SAssignment (ctx.tr_error_var, (Var x_e2_val)))); 
			(lab_err2, SLCall (ctx.tr_error_var, Literal (String syntaxErrorName), [ ], None)); 
			(lab_err3, SLBasic (SAssignment (ctx.tr_error_var, (Var x_pv))))
		] in 
		let err_cmds = List.concat [ err_cmds1; err_cmds2; new_err_cmds ] in 
		
		cmds, (Var x_e2_val), err_cmds
	
	| Parser_syntax.CAccess (e1, e2) -> 
		(**
      x1_v := getValue (x1) with err1;
			x2_v := getValue (x2) with err2;
			x_r := ref-o(x1_v, x2_v)
			
			err1: x_err := x1_v 
			err2: x_err := x2_v 
		 *)
		
		let lab_err1 = fresh_err_label () in 
		let lab_err2 = fresh_err_label () in 
		let x1_v = fresh_var () in
		let x2_v = fresh_var () in
		let x_r = fresh_var () in
		
		let cmds_e1, x_e1, err_cmds1 = f e1 in 
		let cmds_e2, x_e2, err_cmds2 = f e2 in 
		
		(* x1_v := getValue ( x1) with err1 *)
		let cmd_gv1 = SLCall (x1_v, Literal (String getValueName), [ x_e1 ], Some lab_err1) in 
		(* x2_v := getValue ( x2) with err2 *)
		let cmd_gv2 = SLCall (x2_v, Literal (String getValueName), [ x_e2 ], Some lab_err2) in
		(* x_r := ref-o(x1_v, x2_v) *) 
		let cmd = SLBasic (SAssignment (x_r, (ORef ((Var x1_v), (Var x2_v))))) in
		
		let new_cmds = [
			(None, None, cmd_gv1); 
			(None, None, cmd_gv2); 
			(None, None, cmd)
		] in  
		let cmds = List.concat [ cmds_e1; cmds_e2; new_cmds ] in 
		
		let new_err_cmds = [
			(lab_err1, SLBasic (SAssignment (ctx.tr_error_var, (Var x1_v)))); 
			(lab_err2, SLBasic (SAssignment (ctx.tr_error_var, (Var x2_v))))
		] in 
		let err_cmds = List.concat [ err_cmds1; err_cmds2; new_err_cmds ] in 
		
		cmds, (Var x_r), err_cmds
	
	| Parser_syntax.Obj xs -> 
		let x_obj = fresh_var () in 
		(* x_obj = objectConstruct() *) 
		let cmd_new_obj = (None, None, (SLCall (x_obj, Literal (String objectConstructName), [ ], None))) in 
		let cmds, errs = 
			List.fold_left (fun (new_cmds_ac, new_errs_ac) (prop_name, prop_type, e) -> 
			(match prop_type with 
			| Parser_syntax.PropbodyVal -> 
				begin 
					let x_p_val = fresh_var () in
					let lab_p_err = fresh_err_label () in
					let cmds_p_val, x_p, cmds_p_err = f e in 
					let cmd_gv = SLCall (x_p_val, Literal (String getValueName), [ x_p ], Some lab_p_err) in 
					let p_name_expr = 
						(match prop_name with
						| Parser_syntax.PropnameId s
           	| Parser_syntax.PropnameString s -> Literal (String s)
           	| Parser_syntax.PropnameNum n -> UnaryOp (ToStringOp, (Literal (Num n)))) in 
					
					(* [ x_obj, prop_expr ] := x_p_val *)
					let cmd_pv_assign = SLBasic (SMutation ((Var x_obj), p_name_expr, (Var x_p_val))) in   
          let new_cmds = [
						(None, None, cmd_gv); 
						(None, None, cmd_pv_assign)
					] in 
					let cmds = List.append cmds_p_val new_cmds in 
					let new_cmds_ac = List.append new_cmds_ac cmds in 
					
					(* lab_p_err: x_err := x_p_val; *)
					let new_err_cmd = (lab_p_err, SLBasic (SAssignment (ctx.tr_error_var, (Var x_p_val)))) in 
					let new_errs_ac = new_err_cmd :: new_errs_ac in 
					
					new_cmds_ac, new_errs_ac 
				end 	              
			| _ -> raise (Failure ("I have to implement getters and setter - it is the point of all this work"))))
			([], [])
			xs in 
		cmd_new_obj :: cmds, (Var x_obj), errs 	
								
	| Parser_syntax.Delete e -> 
		
		(** 		
						 goto [ ((base(x_e) = $$null) or (base(x_e) = $$undefined)) ] err1 next1;
			next1: x_obj := toObject(base(x_e)) with err2;
						 x_dp := deleteProperty(x_obj, field(x_e), $$t) with err3; 
						 x_r := $$t		
			
			err1:  x_err := SyntaxError() 
			err2:  x_err := x_obj
			err3:  x_err := x_dp
    *)
		
		let next_lab = fresh_label () in 
		let lab_err1 = fresh_err_label () in 
		let lab_err2 = fresh_err_label () in 
		let lab_err3 = fresh_err_label () in 
		let x_obj = fresh_var () in
		let x_dp = fresh_var () in
		
		let cmds_e, x_e, cmds_err = f e in  
	
		(*goto [ ((base(x_e) = $$null) or (base(x_e) = $$undefined)) ] err1 next *) 
		let goto_guard_exp_1 = BinOp ((Base x_e), Equal, (Literal Null)) in 
		let goto_guard_exp_2 = BinOp ((Base x_e), Equal, (Literal Undefined)) in 
		let goto_guard_exp =  BinOp (goto_guard_exp_1, Or, goto_guard_exp_2) in
		let cmd_goto = SLGuardedGoto (goto_guard_exp, lab_err1, next_lab) in 
		
		(* next: x_obj := toObject(base(x_e)) err2 *)
		let cmd_to_obj = SLCall (x_obj, Literal (String toObjectName), [ (Base x_e) ], Some lab_err2) in
		
		(* x_err := deleteProperty(x_obj, field(x_e), $$t) with lab_err *) 
		let cmd_delete = SLCall (x_dp, Literal (String deletePropertyName), 
			[ (Var x_obj); (Field x_e); (Literal (Bool true)) ], Some lab_err3) in
		
		let new_cmds = [
			(None, None, cmd_goto); 
			(None, Some next_lab, cmd_to_obj); 
			(None, None, cmd_delete)
		] in 
		let cmds = List.concat [ cmds_e; new_cmds ] in 
		
		(** error cmds *) 
		(* err1:  x_err := SyntaxError()  *) 
		let cmd_err_1 = SLCall (ctx.tr_error_var, Literal (String syntaxErrorName), [ ], None) in 
		(* err2:  x_err := x_obj *)
		let cmd_err_2 = SLBasic (SAssignment (ctx.tr_error_var, Var x_obj)) in 
		(* err3:  x_err := x_dp *)
		let cmd_err_3 = SLBasic (SAssignment (ctx.tr_error_var, Var x_dp)) in 	
		let new_err_cmds = [
			lab_err1, cmd_err_1; 
			lab_err2, cmd_err_2;
			lab_err3, cmd_err_3
		] in 
		cmds, Literal (Bool true), (new_err_cmds @ cmds_err)
	
	
	| Parser_syntax.AnnonymousFun (_, params, e_body) -> 
		(**
		   x_f := create_function_object(x_scope, f_id, params)
   	*)
		let f_id = try Js_pre_processing.get_codename e 
			with _ -> raise (Failure "annonymous function literals should be annotated with their respective code names") in 
		let x_f = fresh_var () in 
		let processed_params = 
			List.fold_left
				(fun ac param -> (String param) :: ac) 
				[]
				params in 
		let processed_params = List.rev processed_params in 
		let cmd = SLCall (x_f, Literal (String createFunctionObjectName), 
			[ (Var var_scope); (Literal (String f_id)); (Literal (LList processed_params)) ], None) in 
		[ (None, None, cmd) ], (Var x_f), []	
	
	
	| Parser_syntax.Call (e_f, xes) -> 
		(** 
	         C(e_f) = cmds_ef, x_f
					 C(e_0, ..., e_n) = cmds_ei, x_argi (for i = 0, ..., n) 

           x_f_val := getValue (x_f) with err1; 
		 	     x_arg1_val := getValue (x_arg1) with err_arg1; 
		       ...
		       x_argn_val := getValue (x_argn) with err_argn; 
			     goto [ typeOf(x_f_val) != Object] err2 next1; 
		next1: x_ic := isCallable(x_f_val); 
		       goto [ x_ic ] next2 err3; 
		next2: goto [ typeOf(x_f) = ObjReference ] next3 next4; 
		next3: x_this := base(x_f);
					 goto next5; 
		next4: x_this := undefined; 
		next5: x_body := [x_f_val, "@body"]; 
		       x_scope := [x_f_val, "@scope"]; 
					 x_r := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err_call 
		
 err_call: x_err := x_r		
		*)
		
		let cmds_ef, x_ef, errs_ef = f e_f in 
		let cmds_args, x_args, errs_args = 
			List.fold_left (fun (cmds_args, x_args, errs_args) e_arg -> 
				let cmds_arg, x_arg, errs_arg = f e_arg in 
				(cmds_args @ cmds_arg, x_args @ [ x_arg ], errs_args @ errs_arg))
			([], [], [])
			xes in 
		
		(* x_f_val := getValue (x_f) with err1;  *)
		(* err1: x_err := x_f_val *) 
		let x_f_val = fresh_var () in 
		let lab_err1 = fresh_err_label () in  				
		let cmd_gv_f = (None, None, SLCall (x_f_val, Literal (String getValueName), [ x_ef ], Some lab_err1)) in 
		let cmd_xf_gv_err_propg = SLBasic (SAssignment (ctx.tr_error_var, (Var x_f_val))) in 
		
		(* x_arg_i_val := getValue (x_arg_i) with err_arg_i; *)
		let cmds_args_gv, x_args_gv, errs_args_gv = 
			List.fold_left (fun (cmds_args, x_args, errs_args) x_arg ->
				let x_arg_v = fresh_var () in 
				let lab_err_arg_gv = fresh_err_label () in 
				let cmd_gv_arg = SLCall (x_arg_v, Literal (String getValueName), [ x_arg ], Some lab_err_arg_gv) in 
				let cmd_err_propg = SLBasic (SAssignment (ctx.tr_error_var, Var x_arg_v)) in 
				(cmds_args @ [ (None, None, cmd_gv_arg) ], x_args @ [ Var x_arg_v ], 
					errs_args @ [ (lab_err_arg_gv, cmd_err_propg) ]))
			([], [], [])
			x_args in 
		
		(* goto [ typeOf(x_f_val) != Object] err2 next1; *) 
		let lab_err2 = fresh_err_label () in
		let lab_next1 = fresh_label () in   
		let goto_guard_expr = UnaryOp (Not, (BinOp (TypeOf (Var x_f_val), Equal, Literal (Type ObjectType)))) in 
		let cmd_goto_is_obj = SLGuardedGoto (goto_guard_expr, lab_err2, lab_next1) in 
		let cmd_goto_is_obj_err_propg = SLCall (ctx.tr_error_var, Literal (String typeErrorName), [ ], None) in 
		
		(* next1: x_ic := isCallable(x_f_val); *)
		let x_ic = fresh_var () in
		let cmd_ic = SLCall (x_ic, Literal (String isCallableName), [ Var x_f_val ], None) in
		
		(* goto [ x_ic ] next2 err3; *)
		(* err3: x_err := SyntaxError() *) 
		let lab_err3 = fresh_err_label () in
		let lab_next2 = fresh_label () in 
		let cmd_goto_is_callable = SLGuardedGoto (Var x_ic, lab_next2, lab_err3) in 
		let cmd_ic_err_propg =  SLCall (ctx.tr_error_var, Literal (String typeErrorName), [ ], None) in 
		
		(* next2: goto [ typeOf(x_f) = ObjReference ] next3 next4;  *) 
		let lab_next3 = fresh_label () in 
		let lab_next4 = fresh_label () in 
		let goto_guard_expr = BinOp (TypeOf x_ef, Equal, Literal (Type ObjectReferenceType)) in 
		let cmd_goto_obj_ref = SLGuardedGoto (goto_guard_expr, lab_next3, lab_next4) in 
		
		(* next3: x_new_this := base(x_f); *)
		let x_new_this = fresh_var () in 
		let cmd_this_base = SLBasic (SAssignment (x_new_this, Base x_ef)) in 
		
		(*  goto next5; *) 
		let lab_next5 = fresh_label () in 
		let cmd_goto_next5 = SLGoto lab_next5 in 
		
		(* next4: x_this := undefined; *) 
		let cmd_this_undefined = SLBasic (SAssignment (x_new_this, Literal Undefined)) in 
		
		(* next5: x_body := [x_f_val, "@body"]; *)
		let x_body = fresh_var () in 
		let cmd_body = SLBasic (SLookup (x_body, Var x_f_val, Literal (String bodyPropName))) in 
		
		(* x_scope := [x_f_val, "@scope"]; *)
		let x_fscope = fresh_var () in 
		let cmd_scope = SLBasic (SLookup (x_fscope, Var x_f_val, Literal (String scopePropName))) in 
		
		(* x_r := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err_call  *) 
		(* err_call: x_err := x_r *) 
		let x_r = fresh_var () in 
		let lab_proc_err = fresh_err_label () in 
		let proc_args = (Var x_fscope) :: (Var x_new_this) :: x_args_gv in 
		let cmd_proc_call = SLCall (x_r, (Var x_body), proc_args, Some lab_proc_err) in 
		let cmd_pc_err_propg =  SLCall (ctx.tr_error_var, (Var x_r), [ ], None) in 
		
		let new_cmds = [
			(None, None, cmd_goto_is_obj); 
			(None, Some lab_next1, cmd_ic); 
			(None, None, cmd_goto_is_callable); 
			(None, Some lab_next2, cmd_goto_obj_ref); 
			(None, Some lab_next3, cmd_this_base); 
			(None, None, cmd_goto_next5); 
			(None, Some lab_next4, cmd_this_undefined); 
			(None, Some lab_next5, cmd_body); 
			(None, None, cmd_scope); 
			(None, None, cmd_proc_call)
		] in
		let cmds = cmds_ef @ cmds_args @ [ cmd_gv_f ] @ cmds_args_gv @ new_cmds in 
		
		let new_errs = [
			(lab_err1, cmd_xf_gv_err_propg); 
			(lab_err2, cmd_goto_is_obj_err_propg); 
			(lab_err3, cmd_ic_err_propg); 
			(lab_proc_err, cmd_pc_err_propg)
		] in 
		let errs = new_errs @ errs_ef @ errs_args @ errs_args_gv in 
		
		cmds, Var x_r, errs
	
	
	
	| _ -> raise (Failure "not implemented yet")		


let process_error_cmds e_cmds ctx = 
	let rec process_error_cmds_iter e_cmds processed_cmds = 
		match e_cmds with 
		| [] -> processed_cmds 
		| (lab_e, e_cmd) :: rest -> 
			let processed_cmds = (None, Some lab_e, e_cmd) :: (None, None, SLGoto ctx.tr_error_lab) :: processed_cmds in 
			process_error_cmds_iter rest processed_cmds in 
	process_error_cmds_iter e_cmds [] 
	

let generate_main e main cc_table =
	let cc_tbl_main = 
		try Hashtbl.find cc_table main 
			with _ -> raise (Failure "main not defined in cc_table - assim fica dificil")  in 
	let global_vars = 
		Hashtbl.fold (fun key key_val ac -> key :: ac) cc_tbl_main [] in
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
	let ctx = make_translation_ctx main in 
	let cmds_e, x_e, errs = translate main cc_table [] ctx e in 
	(* x_ret := x_e *)
	let ret_ass = (None, None, SLBasic (SAssignment (ctx.tr_ret_var, x_e))) in
	(* lab_ret: skip *) 
	let lab_ret_skip = (None, (Some ctx.tr_ret_lab), (SLBasic SSkip)) in 
	(* lab_err: skip *) 
	let lab_err_skip = (None, (Some ctx.tr_error_lab), (SLBasic SSkip)) in 
	(* error processing cmds *) 
	let err_cmds = (process_error_cmds errs ctx) @ [ lab_err_skip ] in 
	let main_cmds = 
		[ init_scope_chain_ass; lg_ass; this_ass] @ global_var_asses @ cmds_e @ [ret_ass; lab_ret_skip ] @ err_cmds in 
	{ 
		lproc_name = main;
    lproc_body = (Array.of_list main_cmds);
    lproc_params = []; 
		lret_label = ctx.tr_ret_lab; 
		lret_var = ctx.tr_ret_var;
		lerror_label = Some ctx.tr_error_lab; 
		lerror_var = Some ctx.tr_error_var;
		lspec = None 
	}
	
let generate_proc e fid params cc_table =
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
	
	let ctx = make_translation_ctx fid in 
	let cmds_e, x_e, errs = translate fid cc_table [] ctx e in 
	
	(* x_ret := $$empty *)
	let ret_ass = (None, None, SLBasic (SAssignment (ctx.tr_ret_var, Literal Empty))) in
	
	(* lab_ret: skip *) 
	let lab_ret_skip = (None, (Some ctx.tr_ret_lab), (SLBasic SSkip)) in 

	(* lab_err: skip *) 
	let lab_err_skip = (None, (Some ctx.tr_error_lab), (SLBasic SSkip)) in 	
			
	(* error processing cmds *) 
	let err_cmds = (process_error_cmds errs ctx) @ [ lab_err_skip ] in 
	let fid_cmds = 
		[ cmd_er_creation ] @ cmds_params @ cmds_decls @ [ cmd_ass_er_to_sc ] @ cmds_e @ [ ret_ass; lab_ret_skip ] @ err_cmds  in 
	{ 
		lproc_name = fid;
    lproc_body = (Array.of_list fid_cmds);
    lproc_params = var_scope :: var_this :: params; 
		lret_label = ctx.tr_ret_lab; 
		lret_var = ctx.tr_ret_var;
		lerror_label = Some ctx.tr_error_lab; 
		lerror_var = Some ctx.tr_error_var;
		lspec = None 
	}

let js2jsil e = 
	let main = "main" in 
	let e = Js_pre_processing.add_codenames main e in 
	let cc_tbl, fun_tbl = Js_pre_processing.closure_clarification_top_level main e in 
	
	let jsil_prog = SProgram.create 1021 in 
	Hashtbl.iter
		(fun f_id (_, f_params, f_body) -> 
			let proc = 
				(if (f_id = main) 
					then generate_main e main cc_tbl 
					else generate_proc f_body f_id f_params cc_tbl) in 
			SProgram.add jsil_prog f_id proc)
		fun_tbl; 
	
	(* Prints to delete *) 
	let str = Js_pre_processing.print_cc_tbl cc_tbl in 
	Printf.printf "closure clarification table: %s\n" str; 
	(* let main_str = SSyntax_Print.string_of_lprocedure jsil_proc_main in 
	Printf.printf "main code:\n %s\n" main_str; *)
	
	Some js2jsil_imports, jsil_prog

	
	
	
	