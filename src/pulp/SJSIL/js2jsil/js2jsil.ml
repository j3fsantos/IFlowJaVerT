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

let callPropName = "@call"
let constructPropName = "@construct"
let scopePropName = "@scope"

let toBooleanName = "i__toBoolean"
let getValueName = "i__getValue"
let isReservedName = "i__isReserved"
let putValueName = "i__putValue"
let objectConstructName = "Object_construct"
let toObjectName = "i__toObject"
let toStringName = "i__toString"
let deletePropertyName = "o__deleteProperty"
let syntaxErrorName = "SyntaxError"
let typeErrorName = "TypeError"
let createFunctionObjectName = "create_function_object"
let isCallableName = "i__isCallable"
let createScopeChainCopyName = "i__create_sc_copy"
let checkObjectCoercibleName = "i__checkObjectCoercible"

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

let fresh_loop_head_label : (unit -> string) = fresh_sth "loop_h_"

let fresh_loop_body_label : (unit -> string) = fresh_sth "loop_b_"

let fresh_loop_end_label : (unit -> string) = fresh_sth "loop_e_"

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
	| [] -> raise (Failure "Cannot add initial label to empty list of commands")
	| (_, Some lab_s, _) :: rest ->
		(let msg = Printf.sprintf  "failed when trying to add an initial label to a sequence of commands that already had the initial label: %s" lab_s in  
		raise (Failure msg))
	| (spec, None, cmd) :: rest -> (spec, Some lab, cmd) :: rest)

let var_this = "x__this"  
let var_scope = "x__scope"  


(**
Variable x::
	Found in the closure clarification table: Phi(fid_1, x) = fid_2
					x_1 := [__scope_chain, fid_2]; 
					x_2 := v-ref(x_1, "x")
	
	Not found in the closure clarification table: Phi(fid_1, x) = bot
					x_1 := protoField($lg, "x"); 
					goto [x_1 = $$undefined] lab1 lab2
		lab1: x_2 := v-ref($$undefined, "x"); 
		      goto lab3; 
		lab2: x_2 := v-ref($lg, "x"); 
		lab3: skip  	 
 *)
let translate_var_found fid js_var new_var = 
	let tmpl :  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g, unit, string) format = 
" 			%s := [%s, %s]; 
				%s := v-ref(%s, \"%s\")"
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
"				%s := protoField($lg, \"%s\"); 
				goto [%s = $$undefined] %s %s; 
	%s: 	%s := v-ref($$undefined, \"%s\"); 
		    goto %s; 
	%s:		%s := v-ref($lg, \"%s\"); 
	%s: 	skip"
	in 
	let target_code_str = Printf.sprintf tmpl x_1 js_var x_1 lab1 lab2 lab1 x_2 js_var lab3 lab2 new_var js_var lab3 in 
	parse target_code_str


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
		| None -> lab_c 
		| Some lab_str -> 
			(match js_lab with 
			| None -> get_continue_lab rest lab
			|Some js_lab_str -> if (lab_str = js_lab_str) then lab_c else get_continue_lab rest lab)

let rec translate fid cc_table loop_list ctx vis_fid e = 
	
	let f = translate fid cc_table loop_list ctx vis_fid in 
	
	match e.Parser_syntax.exp_stx with 
	
	(* Literals *)
	| Parser_syntax.Null ->  [], Literal Null, [], []
	| Parser_syntax.Bool b -> [], Literal (Bool b), [], []
	| Parser_syntax.String s -> [], Literal (String s), [], []
	| Parser_syntax.Num n ->  [], Literal (Num n), [], []
	
	(* expressions *)	
	
	| Parser_syntax.This ->
		(* x := __this	*)
		let new_var = fresh_var () in 
		let cmd = SLBasic (SAssignment (new_var, (Var var_this))) in
		let cmds = [
			None, None, cmd
		] in  
		cmds, Var new_var, [], []
		
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
		| None -> translate_var_not_found v_fid v new_var, Var new_var, [], [] 
		| Some v_fid -> translate_var_found v_fid v new_var, Var new_var, [], [])
	
	| Parser_syntax.Script (_, es)  
	| Parser_syntax.Block es -> 
		(match es with 
		| [] -> 
			let new_var = fresh_var () in 
			let empty_ass = (None, None, SLBasic (SAssignment (new_var, (Literal Empty)))) in 
			[ empty_ass ], (Var new_var), [], []
		| es -> 
			let rec loop es cmd_lst err_lst ret_lst = 
				(match es with 
				| [] -> raise (Failure "block list cannot be empty HERE" )
				| [ e ] -> 
					let cmds_e, x_e, err_e, rets_e = f e in
					cmd_lst @ cmds_e, x_e, (err_e @ err_lst), (rets_e @ ret_lst)
				| e :: rest_es -> 
					let cmds_e, _, err_e, rets_e = f e in 
					loop rest_es (cmd_lst @ cmds_e) (err_e @ err_lst) (rets_e @ ret_lst)) in
			loop es [] [] []) 
	
	| Parser_syntax.VarDec decs -> 
		let rec loop decs cmds last_e_x errs rets = 
			(match decs with 
			| [] -> 
				(match last_e_x with 
				| None ->
					let new_var = fresh_var () in 
					let empty_ass = (None, None, SLBasic (SAssignment (new_var, (Literal Empty)))) in
					cmds @ [ empty_ass ], Var new_var, errs, rets 
				| Some e_x -> cmds, e_x, errs, rets)
			| (v, eo) :: rest_decs -> 
				(match eo with 
				| None -> loop rest_decs cmds last_e_x errs rets
				| Some e -> raise (Failure "not implemented yet!"))) in 
		loop decs [] None [] [] 
		
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
		
		let cmds_e1, x_e1, err_cmds1, rets1 = f e1 in 
		let cmds_e2, x_e2, err_cmds2, rets2 = f e2 in 
		
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
		
		cmds, (Var x_e2_val), err_cmds, rets1 @ rets2
	
	| Parser_syntax.CAccess (e1, e2) -> 
		(**
      x1_v := getValue (x1) with err1;
			x2_v := getValue (x2) with err2;
			x3_v := "checkObjectCoercible" (x1) with err3;
			x4_v := "i__toString" (x2_v) with err4;
			x_r  := ref-o(x1_v, x4_v)
			
			err1: x_err := x1_v 
			err2: x_err := x2_v 
			err3: x_err := x3_v
			err4: x_err := x4_v
		 *)
		
		let lab_err1 = fresh_err_label () in 
		let lab_err2 = fresh_err_label () in 
		let lab_err3 = fresh_err_label () in 
		let lab_err4 = fresh_err_label () in 
		let x1_v = fresh_var () in
		let x2_v = fresh_var () in
		let x3_v = fresh_var () in
		let x4_v = fresh_var () in
		let x_r = fresh_var () in
		
		let cmds_e1, x_e1, err_cmds1, rets1 = f e1 in 
		let cmds_e2, x_e2, err_cmds2, rets2 = f e2 in 
		
		let new_cmds = [
			(None, None, SLCall (x1_v, Literal (String getValueName),             [ x_e1 ], Some lab_err1)); 
			(None, None, SLCall (x2_v, Literal (String getValueName),             [ x_e2 ], Some lab_err2)); 
			(None, None, SLCall (x3_v, Literal (String checkObjectCoercibleName), [ x_e1 ], Some lab_err3)); 
			(None, None, SLCall (x4_v, Literal (String toStringName),             [ x_e2 ], Some lab_err4)); 
			(None, None, SLBasic (SAssignment (x_r, (ORef ((Var x1_v), (Var x4_v))))))
		] in  
		let cmds = List.concat [ cmds_e1; cmds_e2; new_cmds ] in 
		
		let new_err_cmds = [
			(lab_err1, SLBasic (SAssignment (ctx.tr_error_var, (Var x1_v)))); 
			(lab_err2, SLBasic (SAssignment (ctx.tr_error_var, (Var x2_v))));
			(lab_err3, SLBasic (SAssignment (ctx.tr_error_var, (Var x3_v))));
			(lab_err4, SLBasic (SAssignment (ctx.tr_error_var, (Var x4_v))))
		] in 
		let err_cmds = List.concat [ err_cmds1; err_cmds2; new_err_cmds ] in 
		
		cmds, (Var x_r), err_cmds, rets1 @ rets2
	
	| Parser_syntax.Obj xs -> 
		let x_obj = fresh_var () in 
		(* x_obj = objectConstruct() *) 
		let cmd_new_obj = (None, None, (SLCall (x_obj, Literal (String objectConstructName), [ ], None))) in 
		let cmds, errs, rets = 
			List.fold_left (fun (new_cmds_ac, new_errs_ac, rets_ac) (prop_name, prop_type, e) -> 
			(match prop_type with 
			| Parser_syntax.PropbodyVal -> 
				begin 
					let x_p_val = fresh_var () in
					let lab_p_err = fresh_err_label () in
					let cmds_p_val, x_p, cmds_p_err, rets_p = f e in 
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
					
					new_cmds_ac, new_errs_ac, rets_p @ rets_ac
				end 	              
			| _ -> raise (Failure ("I have to implement getters and setter - it is the point of all this work"))))
			([], [], [])
			xs in 
		cmd_new_obj :: cmds, (Var x_obj), errs, rets
								
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
		
		let cmds_e, x_e, cmds_err, rets = f e in  
	
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
		cmds, Literal (Bool true), (new_err_cmds @ cmds_err), rets
	
	
	| Parser_syntax.AnnonymousFun (_, params, e_body) -> 
		(**
       x1 := copy_scope_chain_obj (x_scope, {{main, fid1, ..., fidn }}); 
		   x_f := create_function_object(x_scope, f_id, params)
   	*)
		
		(* x1 := copy_scope_chain_obj (x_scope, {{main, fid1, ..., fidn }});  *)
		let x1 = fresh_var () in 
		let vis_fid_strs = List.map (fun fid -> String fid) vis_fid in   
		let cmd_sc_copy = SLCall (x1, Literal (String createScopeChainCopyName), 
			[ (Var var_scope); Literal (LList vis_fid_strs) ], None) in 
		
		(* x_f := create_function_object(x_scope, f_id, params) *)
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
			[ (Var x1); (Literal (String f_id)); (Literal (LList processed_params)) ], None) in 	
		
		[ 
		  (None, None, cmd_sc_copy); 
			(None, None, cmd)
		], (Var x_f), [], []
	
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
		next5: x_body := [x_f_val, "@call"]; 
		       x_scope := [x_f_val, "@scope"]; 
					 x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err_call; 
					 goto [ x_r1 = $$emtpy ] next6 nex7;
		next6: x_r2 := $$undefined; 
		next7: x_r3 := PHI(x_r1, x_r2)
		
 err_call: x_err := x_r		
		*)
		
		let cmds_ef, x_ef, errs_ef, rets_ef = f e_f in 
		let cmds_args, x_args, errs_args, rets_args = 
			List.fold_left (fun (cmds_args, x_args, errs_args, rets_args) e_arg -> 
				let cmds_arg, x_arg, errs_arg, rets_arg = f e_arg in 
				(cmds_args @ cmds_arg, x_args @ [ x_arg ], (errs_args @ errs_arg), (rets_args @ rets_arg)))
			([], [], [], [])
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
		
		(* next5: x_body := [x_f_val, "@@call"]; *)
		let x_body = fresh_var () in 
		let cmd_body = SLBasic (SLookup (x_body, Var x_f_val, Literal (String callPropName))) in 
		
		(* x_scope := [x_f_val, "@scope"]; *)
		let x_fscope = fresh_var () in 
		let cmd_scope = SLBasic (SLookup (x_fscope, Var x_f_val, Literal (String scopePropName))) in 
		
		(* x_r1 := x_body (x_scope, x_this, x_arg0_val, ..., x_argn_val) with err_call  *) 
		(* err_call: x_err := x_r1 *) 
		let x_r1 = fresh_var () in 
		let lab_proc_err = fresh_err_label () in 
		let proc_args = (Var x_fscope) :: (Var x_new_this) :: x_args_gv in 
		let cmd_proc_call = SLCall (x_r1, (Var x_body), proc_args, Some lab_proc_err) in 
		let cmd_pc_err_propg = SLBasic (SAssignment (ctx.tr_error_var, (Var x_r1))) in 
		
		(* goto [ x_r1 = $$emtpy ] next6 nex7; *)
		let lab_next6 = fresh_label () in 
		let lab_next7 = fresh_label () in 
		let goto_guard_expr = BinOp (Var x_r1, Equal, Literal Empty) in
		let cmd_goto_test_empty = SLGuardedGoto (goto_guard_expr, lab_next6, lab_next7) in 
		
		(* next6: x_r2 := $$undefined; *)
		let x_r2 = fresh_var () in 
		let cmd_ret_undefined = SLBasic (SAssignment (x_r2, Literal Undefined)) in
		
		(* next7: x_r3 := PHI(x_r1, x_r2) *) 
		let x_r3 = fresh_var () in 
		let cmd_phi_final = SLBasic (SPhiAssignment (x_r3, [| Some x_r1; Some x_r2 |])) in 
		 

		let new_cmds = [
			(None, None,           cmd_goto_is_obj); 
			(None, Some lab_next1, cmd_ic); 
			(None, None,           cmd_goto_is_callable); 
			(None, Some lab_next2, cmd_goto_obj_ref); 
			(None, Some lab_next3, cmd_this_base); 
			(None, None,           cmd_goto_next5); 
			(None, Some lab_next4, cmd_this_undefined); 
			(None, Some lab_next5, cmd_body); 
			(None, None,           cmd_scope); 
			(None, None,           cmd_proc_call); 
			(None, None,           cmd_goto_test_empty); 
			(None, Some lab_next6, cmd_ret_undefined); 
			(None, Some lab_next7, cmd_phi_final)
		] in
		let cmds = cmds_ef @ cmds_args @ [ cmd_gv_f ] @ cmds_args_gv @ new_cmds in 
		
		let new_errs = [
			(lab_err1, cmd_xf_gv_err_propg); 
			(lab_err2, cmd_goto_is_obj_err_propg); 
			(lab_err3, cmd_ic_err_propg); 
			(lab_proc_err, cmd_pc_err_propg)
		] in 
		let errs = new_errs @ errs_ef @ errs_args @ errs_args_gv in 
		
		cmds, Var x_r3, errs, (rets_ef @ rets_args)
	
	| Parser_syntax.Return e -> 
		(match e with 
		| None -> 
			let x_r = fresh_var () in 
			let lab_r = fresh_ret_label () in
			(* x_r := $$undefined *) 
			let cmd_xr_ass = (None, None, SLBasic (SAssignment (x_r, Literal Undefined))) in 
			(* goto lab_r *) 
			let cmd_goto_ret = (None, None, SLGoto lab_r) in 
			[ cmd_xr_ass; cmd_goto_ret], Var x_r, [], [ (lab_r, Var x_r) ] 
			
		| Some e ->
			let cmds_e, x_e, errs_e, rets_e = f e in
			let label_ret_e = fresh_ret_label () in 
			let cmd_goto_ret = (None, None, SLGoto label_ret_e) in 
			cmds_e @ [ cmd_goto_ret ], x_e, errs_e, (label_ret_e, x_e) :: rets_e)
		
	
	| Parser_syntax.If (e1, e2, e3) -> 
		(**
     *  C(e1) = cmds1, x1; C(e2) = cmds2, x2; C(e3) = cmds3, x3
		 *  
		 *  C(if (e1) { e2 } else { e3 }) = 
			       cmds1
						 x1_v := getValue (x1) with err1
						 x1_b := toBoolean (x1_b) with err2  
						 goto [x1_b] then else 
			then:  cmds1
			       goto endif
			else:  cmds2 
			endif: x_if := PHI(x2, x3)   
		 *)
		let cmds_e1, x_e1, errs_e1, rets_e1 = f e1 in
		let cmds_e2, x_e2, errs_e2, rets_e2 = f e2 in
		let cmds_e3, x_e3, errs_e3, rets_e3 = 
			(match e3 with 
			| None -> 
				let x3 = fresh_var () in 
				let cmd3 = SLBasic (SAssignment (x3, Literal Empty)) in
				let cmds3 = [ (None, None, cmd3) ] in  
				cmds3, Var x3, [], [] 
			| Some e3 -> f e3) in 
		
		(* x1_v := getValue (x1) with err1 *) 
		let x1_v = fresh_var () in 
		let err1 = fresh_err_label () in 
		let cmd_gv_x1 = SLCall (x1_v, (Literal (String getValueName)), [ x_e1 ], Some err1) in
		let cmd_gv_x1_err = SLBasic (SAssignment (ctx.tr_error_var, (Var x1_v))) in
		
		(* x1_b := toBoolean (x1_v) with err2 *)
		let x1_b = fresh_var () in 
		let err2 = fresh_err_label () in 
	  let cmd_tb_x1 = SLCall (x1_b, (Literal (String toBooleanName)), [ Var x1_v ], Some err2) in
		let cmd_tb_x1_err = SLBasic (SAssignment (ctx.tr_error_var, (Var x1_b))) in
		
		(* goto [x1_b] then else *) 
		let lab_then = fresh_label () in 
		let lab_else = fresh_label () in 
		let cmd_goto_if = SLGuardedGoto (Var x1_b, lab_then, lab_else) in 
	
		let cmds_e2 = add_initial_label cmds_e2 lab_then in 
		let cmds_e3 = add_initial_label cmds_e3 lab_else in 	
		
		(* goto endif *) 
		let lab_endif = fresh_label () in 
		let cmd_goto_endif = SLGoto lab_endif in 
		
		(* endif: x_if := PHI(x2, x3) *) 
		let x_e2_var, x_e3_var = 
			(match x_e2, x_e3 with 
			| Var x_e2_var, Var x_e3_var -> x_e2_var, x_e3_var 
			| _, _ -> raise (Failure "the compilation of the then and else parts of the ifs must generate a variable each")) in 
		let x_if = fresh_var () in 
		let cmd_end_if = SLBasic (SPhiAssignment (x_if, [| Some x_e2_var; Some x_e3_var |])) in 
		
		let cmds = 
			    cmds_e1 @ [                           (*       cmds1                               *)
				(None, None,           cmd_gv_x1);      (*       x1_v := getValue (x1) with err1     *)
				(None, None,           cmd_tb_x1);      (*       x1_b := toBoolean (x1_v) with err2  *)
				(None, None,           cmd_goto_if)     (*       goto [x1_b] then else               *) 
			] @ cmds_e2 @ [                           (* then: cmds2                               *)
				(None, None,           cmd_goto_endif)  (*       goto end                            *)
			] @ cmds_e3 @ [                           (* else: cmds3                               *)
				(None, Some lab_endif, cmd_end_if)      (* end:  x_if := PHI(x2, x3)                 *)
			] in 
	
		let new_errs = [
			(err1, cmd_gv_x1_err); 
			(err2, cmd_tb_x1_err)
		] in 
		let errs = new_errs @ errs_e1 @ errs_e2 @ errs_e3 in 
		
		let rets = rets_e1 @ rets_e2 @ rets_e3 in 
		
		cmds, Var x_if, errs, rets 
	
	| Parser_syntax.While (e1, e2) -> 
		(**
     *  C(e1) = cmds1, x1; C(e2) = cmds2, x2
		 *  
		 *  C(while (e1) { e2 } ) =
			          x_ret_0 := $$empty 
			guard:    x_ret_1 := PHI(x_ret_0, x_ret_2) 
					      cmds1
						    x1_v := getValue (x1) with err1
						    x1_b := toBoolean (x1_b) with err2  
						    goto [x1_b] body endwhile 
			body:     cmds2
						    x2_v := getValue (x2) with err3
						    goto [not (x_2' = $$empty)] next1 next2
			next1:    skip; 
			next2:    x_ret_2 := PHI(x_ret_1, x2_v) 
			          goto guard 
			endwhile: skip 
		 *)
		
		let lab_guard = fresh_loop_head_label () in 
		let endwhile = fresh_loop_end_label () in 
		let cmds1, x1, errs1, rets1 = f e1 in
		let new_loop_list = (lab_guard, endwhile, None) :: loop_list in 
		let cmds2, x2, errs2, rets2 = translate fid cc_table new_loop_list ctx vis_fid e2 in
		
		(* x_ret_0 := $$empty *) 
		let x_ret_0 = fresh_var () in 
		let x_ret_1 = fresh_var () in 
		let cmd_ass_ret_0 = SLBasic (SAssignment (x_ret_0, (Literal Empty))) in 
		
		(* x_ret_1 := PHI(x_ret_0, x_ret_2) *)
		let x_ret_2 = fresh_var () in 
		let cmd_ass_ret_1 = SLBasic (SPhiAssignment (x_ret_1, [| Some x_ret_0; Some x_ret_2 |])) in 
		
		(* x1_v := getValue (x1) with err1 *)
		let x1_v = fresh_var () in 
		let err1 = fresh_err_label () in 
		let cmd_gv_x1 = SLCall (x1_v, (Literal (String getValueName)), [ x1 ], Some err1) in
		let cmd_gv_x1_err = SLBasic (SAssignment (ctx.tr_error_var, (Var x1_v))) in
		
		(* x1_b := toBoolean (x1_v) with err2 *)
		let x1_b = fresh_var () in 
		let err2 = fresh_err_label () in 
	  let cmd_tb_x1 = SLCall (x1_b, (Literal (String toBooleanName)), [ Var x1_v ], Some err2) in
		let cmd_tb_x1_err = SLBasic (SAssignment (ctx.tr_error_var, (Var x1_b))) in
		
		(* goto [x1_b] body endwhile  *) 
		let lab_body = fresh_loop_body_label () in 
		let cmd_goto_while = SLGuardedGoto (Var x1_b, lab_body, endwhile) in 
		
		(* x2_v := getValue (x2) with err3 *) 
		let x2_v = fresh_var () in 
		let err3 = fresh_err_label () in 
	  let cmd_gv_x2 = SLCall (x2_v, (Literal (String getValueName)), [ x2 ], Some err3) in
		let cmd_gv_x2_err = SLBasic (SAssignment (ctx.tr_error_var, (Var x2_v))) in
		
		(* goto [not (x2_v = $$empty)] next1 next2 *) 
		let next1 = fresh_label () in 
		let next2 = fresh_label () in 
		let expr_goto_guard = BinOp (Var x2_v, Equal, Literal Empty) in 
		let expr_goto_guard = UnaryOp (Not, expr_goto_guard) in 
		let cmd_goto_empty_test = SLGuardedGoto (expr_goto_guard, next1, next2) in 
		
		(* x_ret_2 := PHI(x_ret_1, x2_v) *) 
		let cmd_ass_ret_2 = SLBasic (SPhiAssignment (x_ret_2, [| Some x_ret_1; Some x2_v |])) in 
		
		let cmds2 = add_initial_label cmds2 lab_body in 
		let cmds = 
			[
				(None, None,           cmd_ass_ret_0);         (*           x_ret_0 := $$empty                      *)
				(None, Some lab_guard, cmd_ass_ret_1);         (* guard:    x_ret_1 := PHI(x_ret_0, x_ret_2)        *) 
			] @ cmds1 @ [                                    (*           cmds1                                   *)
			  (None, None,           cmd_gv_x1);             (*           x1_v := getValue (x1) with err1         *)
				(None, None,           cmd_tb_x1);             (*           x1_b := toBoolean (x1_b) with err2      *)
				(None, None,           cmd_goto_while)         (*           goto [x1_b] body endwhile               *)
			] @ cmds2 @ [                                    (* body:     cmds2                                   *)
			  (None, None,           cmd_gv_x2);             (*           x2_v := getValue (x2) with err3         *)
				(None, None,           cmd_goto_empty_test);   (*           goto [not (x2_v = $$empty)] next1 next2 *)
			  (None, Some next1,     SLBasic SSkip);         (* next1:    skip                                    *) 
				(None, Some next2,     cmd_ass_ret_2);         (* next2:    x_ret_2 := PHI(x_ret_1, x2_v)           *) 
				(None, None,           SLGoto lab_guard);      (*           goto guard                              *)
				(None, Some endwhile,  SLBasic SSkip)          (* endwhile: skip                                    *)
			] in 
		
		let new_errs = [
			(err1, cmd_gv_x1_err); 
			(err2, cmd_tb_x1_err); 
			(err3, cmd_gv_x2_err)
		] in 
		let errs = new_errs @ errs1 @ errs2 in 
		
		let rets = rets1 @ rets2 in 
			          
		cmds, Var x_ret_1, errs, rets 					     
	
	| Parser_syntax.DoWhile (e1, e2) -> 
		(**
     *  C(e1) = cmds1, x1; C(e2) = cmds2, x2
		 *  
		 *  C(do { e1 } while (e2) ) =
			          x_ret_0 := $$empty 
			head:     x_ret_1 := PHI(x_ret_0, x_ret_2) 
								cmds1 
			          x1_v := getValue (x1) with err1 
					      goto [ not (x1_v = $$empty) ] next1 next2 
		  next1:    skip 
			next2:    x_ret_2 := PHI(x_ret_1, x1_v)
			guard:    cmds2
								x2_v := getValue (x2) with err2
								x2_b := toBoolean (x2_v) with err3 
								goto [x2_b] head end 
		  end:      skip
		 *)			    
		let guard = fresh_loop_head_label () in 
		let dowhile_end = fresh_loop_end_label () in 
		let new_loop_list = (guard, dowhile_end, None) :: loop_list in 
		let cmds1, x1, errs1, rets1 = translate fid cc_table new_loop_list ctx vis_fid e1 in
		let cmds2, x2, errs2, rets2 = f e2 in
		let cmds2 = add_initial_label cmds2 guard in
		
		(* x_ret_0 := $$empty *) 
		let x_ret_0 = fresh_var () in 
		let cmd_ass_ret_0 = SLBasic (SAssignment (x_ret_0, (Literal Empty))) in 
		
		(* x_ret_1 := PHI(x_ret_0, x_ret_2)  *) 
		let x_ret_1 = fresh_var () in 
		let x_ret_2 = fresh_var () in 
		let cmd_ass_ret_1 = SLBasic (SPhiAssignment (x_ret_1, [| Some x_ret_0; Some x_ret_2 |])) in 
		
		(* x1_v := getValue (x1) with err1 *)
		let x1_v = fresh_var () in 
		let err1 = fresh_err_label () in 
		let cmd_gv_x1 = SLCall (x1_v, (Literal (String getValueName)), [ x1 ], Some err1) in
		let cmd_gv_x1_err = SLBasic (SAssignment (ctx.tr_error_var, (Var x1_v))) in
		
		(*  goto [ not (x1_v = $$empty) ] next1 next2 *)
		let next1 = fresh_label () in 
		let next2 = fresh_label () in 
		let expr_goto_guard = BinOp (Var x1_v, Equal, Literal Empty) in 
		let expr_goto_guard = UnaryOp (Not, expr_goto_guard) in 
		let cmd_goto_empty_test = SLGuardedGoto (expr_goto_guard, next1, next2) in
		
		(* x_ret_2 := PHI(x_ret_1, x1_v)  *) 
		let cmd_ass_ret_2 = SLBasic (SPhiAssignment (x_ret_2, [| Some x_ret_1; Some x1_v |])) in 
		
		(* x2_v := getValue (x2) with err2 *)
		let x2_v = fresh_var () in 
		let err2 = fresh_err_label () in 
		let cmd_gv_x2 = SLCall (x2_v, (Literal (String getValueName)), [ x2 ], Some err2) in
		let cmd_gv_x2_err = SLBasic (SAssignment (ctx.tr_error_var, (Var x2_v))) in
		
		(* x2_b := toBoolean (x2_v) with err3 *)
		let x2_b = fresh_var () in 
		let err3 = fresh_err_label () in 
	  let cmd_tb_x2 = SLCall (x2_b, (Literal (String toBooleanName)), [ Var x2_v ], Some err3) in
		let cmd_tb_x2_err = SLBasic (SAssignment (ctx.tr_error_var, (Var x2_b))) in
		
		(* goto [x2_b] head end *)
		let head = fresh_label () in 
		let cmd_dowhile_goto =  SLGuardedGoto (Var x2_b, head, dowhile_end) in 
		
		let cmds = 
				[
					(None, None,             cmd_ass_ret_0);         (*              x_ret_0 := $$empty                           *)
					(None, Some head,        cmd_ass_ret_1);         (* head:        x_ret_1 := PHI(x_ret_0, x_ret_2)             *) 
				] @ cmds1 @ [                                      (*              cmds1                                        *)
				  (None, None,             cmd_gv_x1);             (*              x1_v := getValue (x1) with err1              *)
					(None, None,             cmd_goto_empty_test);   (*              goto [ not (x1_v = $$empty) ] next1 next2    *)
					(None, Some next1,       SLBasic SSkip);         (* next1:       skip                                         *)
					(None, Some next2,       cmd_ass_ret_2);         (* next2:       x_ret_2 := PHI(x_ret_1, x1_v)                *)  
				] @ cmds2 @ [                                      (*              cmds2                                        *)
				  (None, None,             cmd_gv_x2);             (*              x2_v := getValue (x2) with err2              *)
					(None, None,             cmd_tb_x2);             (*              x2_b := toBoolean (x2_v) with err3           *)
					(None, None,             cmd_dowhile_goto);      (*              goto [x2_b] head end                         *)
					(None, Some dowhile_end, SLBasic SSkip);         (* dowhile_end: skip                                         *) 
				] in 
	
		let new_errs = [
			(err1, cmd_gv_x1_err); 
			(err2, cmd_gv_x2_err); 
			(err3, cmd_tb_x2_err)
		] in 
		let errs = new_errs @ errs1 @ errs2 in 
		
		let rets = rets1 @ rets2 in 
			          
		cmds, Var x_ret_2, errs, rets 	 
	
	| Parser_syntax.For (e1, e2, e3, e4) ->
		
		(**
     *  C(e1) = cmds1, _; C(e2) = cmds2, x2; C(e3) = cmds3, _; C(e4) = cmds4, x4
		 *  
		 *  C( for(e1; e2; e3) { e4 } ) =
			          cmds1 
								x_ret_0 := $$empty 
			head:     x_ret_1 := PHI(x_ret_0, x_ret_2) 
								cmds2
			          x2_v := getValue (x2) with err1
								x2_b := toBoolean (x2_v) with err2
								goto [x2_b] body end 
			body: 		cmds4 
								x4_v := getValue (x4) with err3
								goto [ not (x4_v = $$empty) ] next1 next2 
		  next1:    skip 
			next2:    x_ret_2 := PHI(x_ret_1, x4_v)
			          cmds3
								goto head
		  end:      skip
		 *)	
		
		let cmds1, _, errs1, rets1 = 
			(match e1 with 
			| Some e1 -> f e1 
			| None -> [], Var "xpto", [], []) in
		
		let cmds2, x2, errs2, rets2 = 	
			(match e2 with 
			| Some e2 -> f e2 
			| None -> 
				let x2 = fresh_var () in 
				let cmd_ass_x2 = (None, None, SLBasic (SAssignment (x2, Literal (Bool true)))) in 
				[ cmd_ass_x2 ], Var x2, [], []) in
		
		let cmds3, _, errs3, rets3 = 
			(match e3 with 
			| Some e3 -> f e3 
			| None -> [], Var "xpto", [], []) in
		
		let head = fresh_loop_head_label () in 
		let for_end = fresh_loop_end_label () in 
		let new_loop_list = (head, for_end, None) :: loop_list in 
		let cmds4, x4, errs4, rets4 = translate fid cc_table new_loop_list ctx vis_fid e4 in 
		
		(* x_ret_0 := $$empty  *) 
		let x_ret_0 = fresh_var () in 
		let cmd_ass_ret_0 = SLBasic (SAssignment (x_ret_0, (Literal Empty))) in 
		
		(* head:     x_ret_1 := PHI(x_ret_0, x_ret_2)  *)
		let x_ret_1 = fresh_var () in 
		let x_ret_2 = fresh_var () in 
		let cmd_ass_ret_1 = SLBasic (SPhiAssignment (x_ret_1, [| Some x_ret_0; Some x_ret_2 |])) in
		
		(* x2_v := getValue (x2) with err1 *) 
		let x2_v = fresh_var () in 
		let err1 = fresh_err_label () in 
		let cmd_gv_x2 = SLCall (x2_v, (Literal (String getValueName)), [ x2 ], Some err1) in
		let cmd_gv_x2_err = SLBasic (SAssignment (ctx.tr_error_var, (Var x2_v))) in		
		
	  (* x2_b := toBoolean (x2_v) with err2 *) 
		let x2_b = fresh_var () in 
		let err2 = fresh_err_label () in 
	  let cmd_tb_x2 = SLCall (x2_b, (Literal (String toBooleanName)), [ Var x2_v ], Some err2) in
		let cmd_tb_x2_err = SLBasic (SAssignment (ctx.tr_error_var, (Var x2_b))) in
		
		(* goto [x2_b] body for_end *) 
		let body = fresh_loop_body_label () in 
		let cmd_for_goto =  SLGuardedGoto (Var x2_b, body, for_end) in 
		
		(* x4_v := getValue (x4) with err3 *) 
		let x4_v = fresh_var () in 
		let err3 = fresh_err_label () in 
		let cmd_gv_x4 = SLCall (x4_v, (Literal (String getValueName)), [ x4 ], Some err3) in
		let cmd_gv_x4_err = SLBasic (SAssignment (ctx.tr_error_var, (Var x4_v))) in	
		
		(* 	goto [ not (x4_v = $$empty) ] next1 next2  *) 
		let next1 = fresh_label () in 
		let next2 = fresh_label () in 
		let expr_goto_guard = BinOp (Var x4_v, Equal, Literal Empty) in 
		let expr_goto_guard = UnaryOp (Not, expr_goto_guard) in 
		let cmd_goto_empty_test = SLGuardedGoto (expr_goto_guard, next1, next2) in
		
		(* next2:    x_ret_2 := PHI(x_ret_1, x4_v) *) 
		let cmd_ass_ret_2 = SLBasic (SPhiAssignment (x_ret_2, [| Some x_ret_1; Some x4_v |])) in
		
		let cmds4 = add_initial_label cmds4 body in 
		
		let cmds = 
				    cmds1 @ [                                      (*              cmds1                                        *)
					(None, None,             cmd_ass_ret_0);         (*              x_ret_0 := $$empty                           *)
					(None, Some head,        cmd_ass_ret_1);         (* head:        x_ret_1 := PHI(x_ret_0, x_ret_2)             *) 
				] @ cmds2 @ [                                      (*              cmds2                                        *)
					(None, None,             cmd_gv_x2);             (*              x2_v := getValue (x2) with err1              *)
					(None, None,             cmd_tb_x2);             (*              x2_b := toBoolean (x2_v) with err2           *) 
					(None, None,             cmd_for_goto);          (*              goto [x2_b] body end                         *) 
				] @ cmds4 @ [                                      (* body:        cmds4                                        *)	   
					(None, None,             cmd_gv_x4);             (*              x4_v := getValue (x4) with err3              *)
					(None, None,             cmd_goto_empty_test);   (*              goto [ not (x4_v = $$empty) ] next1 next2    *)
					(None, Some next1,       SLBasic SSkip);         (* next1:       skip                                         *)
					(None, Some next2,       cmd_ass_ret_2);         (* next2:       x_ret_2 := PHI(x_ret_1, x4_v)                *)  
				] @ cmds3 @ [                                      (*              cmds2                                        *)
				  (None, None,             SLGoto head);           (*              goto head                                    *)
					(None, Some for_end,     SLBasic SSkip)          (* end:         skip                                         *)
				] in 
		
		let new_errs = [
			(err1, cmd_gv_x2_err); 
			(err2, cmd_tb_x2_err); 
			(err3, cmd_gv_x4_err)
		] in 
		let errs = new_errs @ errs1 @ errs2 @ errs3 @ errs4 in 
		
		let rets = rets1 @ rets2 @ rets3 @ rets4 in 
		
		cmds, Var x_ret_1, errs, rets 
	
	| Parser_syntax.Break lab ->
		(** 
      x_r := $$empty;
      goto lab_r 
		*) 
		(* x_r := $$empty  *) 
		let x_r = fresh_var () in 
		let cmd_ass_xr = SLBasic (SAssignment (x_r, (Literal Empty))) in 
		
		(* goto lab_r *) 
		let lab_r = get_break_lab loop_list lab in
		let cmds = [
			(None, None,             cmd_ass_xr);                (*              x_r := $$empty                           *)
			(None, None,             SLGoto lab_r)               (*              goto lab_r                               *)
		] in 
		
		cmds, Var x_r, [], []
		
	| _ -> raise (Failure "not implemented yet")		


let process_error_cmds e_cmds ctx = 
	let rec process_error_cmds_iter e_cmds processed_cmds = 
		match e_cmds with 
		| [] -> processed_cmds 
		| (lab_e, e_cmd) :: rest -> 
			let processed_cmds = (None, Some lab_e, e_cmd) :: (None, None, SLGoto ctx.tr_error_lab) :: processed_cmds in 
			process_error_cmds_iter rest processed_cmds in 
	process_error_cmds_iter e_cmds [] 
	
let process_ret_cmds rets ctx = 
	let rec process_ret_cmds_iter rets processed_rets = 
		match rets with 
		| [] -> processed_rets 
		| (lab_x, x) :: rest -> 
			(*lab_x: x_ret := x *) 
			let cmd_ass_ret = (None, Some lab_x, SLBasic (SAssignment (ctx.tr_ret_var, x))) in 
			(* goto ret_lab *) 
			let cmd_goto_ret = (None, None, SLGoto ctx.tr_ret_lab) in 
			process_ret_cmds_iter rest (cmd_ass_ret :: cmd_goto_ret :: processed_rets) in 
	process_ret_cmds_iter rets []

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
	let cmds_e, x_e, errs, _ = translate main cc_table [] ctx [ main ] e in 
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
	
	let ctx = make_translation_ctx fid in 
	let cmds_e, x_e, errs, rets = translate fid cc_table [] ctx vis_fid e in 
	
	(* x_dr := $$empty *)
	let x_dr = fresh_var () in
	let ret_lab_dr = fresh_ret_label () in  
	let cmd_dr_ass = (None, None, SLBasic (SAssignment (x_dr, Literal Empty))) in
	let cmd_dr_goto = (None, None, SLGoto ret_lab_dr) in 
	let rets = (ret_lab_dr, Var x_dr) :: rets in 
	
	(* lab_ret: skip *) 
	let lab_ret_skip = (None, (Some ctx.tr_ret_lab), (SLBasic SSkip)) in 

	(* lab_err: skip *) 
	let lab_err_skip = (None, (Some ctx.tr_error_lab), (SLBasic SSkip)) in 	
			
	(* error processing cmds *) 
	let err_cmds = (process_error_cmds errs ctx) @ [ lab_err_skip ] in 
	
	let ret_cmds = (process_ret_cmds rets ctx) @ [ lab_ret_skip ] in 
	
	let fid_cmds = 
		[ cmd_er_creation ] @ cmds_params @ cmds_decls @ [ cmd_ass_er_to_sc ] @ cmds_e 
		@ [ cmd_dr_ass; cmd_dr_goto ] @ ret_cmds @ err_cmds  in 
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
	let cc_tbl, fun_tbl, vis_tbl = Js_pre_processing.closure_clarification_top_level main e in 
	
	let jsil_prog = SProgram.create 1021 in 
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
			SProgram.add jsil_prog f_id proc)
		fun_tbl; 
	
	(* Prints to delete *) 
	let str = Js_pre_processing.print_cc_tbl cc_tbl in 
	Printf.printf "closure clarification table: %s\n" str; 
	(* let main_str = SSyntax_Print.string_of_lprocedure jsil_proc_main in 
	Printf.printf "main code:\n %s\n" main_str; *)
	
	Some js2jsil_imports, jsil_prog

	
	
	
	