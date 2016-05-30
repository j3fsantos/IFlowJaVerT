open Parser_syntax
open Utils
open Lexing
open Batteries
open SSyntax


let getValueName = "i__getValue"
let isReservedName = "i__isReserved"
let putValueName = "i__putValue"

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
This::
		 			goto [not (__this = $$undefined)] elab lab; 
		lab: 	x := __this	
 *)
let translate_this error_label new_var = 
	let new_label : string = fresh_label () in 
	let tmpl : ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g, unit, string) format = 
" 		goto [not (%s = $$undefined)] %s %s; 
	%s:	%s := %s"
	in 
	let target_code_str = Printf.sprintf tmpl var_this error_label new_label new_label new_var var_this in 
	Printf.printf "I am generating the translation of a this: %s\n" target_code_str; 
	parse target_code_str


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
	| Parser_syntax.Null ->  [], Literal Null
	| Parser_syntax.Bool b -> [], Literal (Bool b)
	| Parser_syntax.String s -> [], Literal (String s)
	| Parser_syntax.Num n ->  [], Literal (Num n)    
	
	(* expressions *)
	
	| Parser_syntax.This ->
		let new_var = fresh_var () in 
		let target_code = translate_this ctx.tr_error_lab new_var in 
		target_code, Var new_var 
		
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
		| None -> translate_var_not_found v_fid v new_var, Var new_var 
		| Some v_fid -> translate_var_found v_fid v new_var, Var new_var)
	
	| Parser_syntax.Script (_, es)  
	| Parser_syntax.Block es -> 
		(match es with 
		| [] -> 
			let new_var = fresh_var () in 
			let empty_ass = (None, None, SLBasic (SAssignment (new_var, (Literal Empty)))) in 
			[ empty_ass ], Var new_var
		| es -> 
			let rec loop es cmd_lst = 
				(match es with 
				| [] -> raise (Failure "block list cannot be empty HERE" )
				| [ e ] -> 
					let cmds_e, x_e = f e in
					cmd_lst @ cmds_e, x_e  
				| e :: rest_es -> 
					let cmds_e, _ = f e in 
					loop rest_es (cmd_lst @ cmds_e)) in
			loop es []) 
	
	| Parser_syntax.VarDec decs -> 
		let rec loop decs cmds last_e_x = 
			(match decs with 
			| [] -> 
				(match last_e_x with 
				| None ->
					let new_var = fresh_var () in 
					let empty_ass = (None, None, SLBasic (SAssignment (new_var, (Literal Empty)))) in
					cmds @ [ empty_ass ], Var new_var
				| Some e_x -> cmds, e_x)
			| (v, eo) :: rest_decs -> 
				(match eo with 
				| None -> loop rest_decs cmds last_e_x 
				| Some e -> raise (Failure "not implemented yet!"))) in 
		let cmds, e_x = loop decs [] None in 
		cmds, e_x 
		
	| Parser_syntax.Assign (e1, e2) ->
		let new_var_is_reserved = fresh_var () in 
		let new_var_x_e2 = fresh_var () in 
		let new_var_pv = fresh_var () in  
		let new_lab = fresh_label () in 
		
		let cmds_e1, x_e1 = f e1 in 
		let cmds_e2, x_e2 = f e2 in 
		
		(* x2' := getValue ( x2) with err_lab *)
		let cmd_get_value_e2 = SLCall (new_var_x_e2, Literal (String getValueName), [ x_e2 ], Some ctx.tr_error_lab) in 
		(* x_is_reserved := is_reserved (x1) *)
		let cmd_is_reserved_e1 = SLCall (new_var_is_reserved, Literal (String isReservedName), [x_e1], None) in 
		(* (((TypeOf(x1) = $$VarReferenceType) && x_is_reserved) || (base(x1) = $$undefined)) *)
		let is_invalid_assignment_exp = BinOp ((TypeOf x_e1), Equal, (Literal (Type VariableReferenceType))) in 
		let is_invalid_assignment_exp = BinOp ((Var new_var_is_reserved), And, is_invalid_assignment_exp) in 
		let is_invalid_assignment_exp = BinOp (is_invalid_assignment_exp, Or, (BinOp ((Base x_e1), Equal, (Literal Undefined)))) in
		(* goto [is_invalid_assignment] err_lab next *) 
		let cmd_guarded_goto = SLGuardedGoto (is_invalid_assignment_exp, ctx.tr_error_lab, new_lab) in 
		(* lab: ret = putValue (x1, x2) with lab_err *)
		let cmd_put_value = SLCall (new_var_pv, Literal (String putValueName), [x_e1; (Var new_var_x_e2)], Some ctx.tr_error_lab) in 
		
		let new_cmds = [
			(None, None, cmd_get_value_e2); 
			(None, None, cmd_is_reserved_e1); 
			(None, None, cmd_guarded_goto); 
			(None, Some new_lab, cmd_put_value)
		] in 
		let cmds = List.concat [ cmds_e1; cmds_e2; new_cmds ] in 
		cmds, (Var new_var_x_e2)
	
	| Parser_syntax.CAccess (e1, e2) -> 
		let new_var_x_e1 = fresh_var () in
		let new_var_x_e2 = fresh_var () in
		let new_var = fresh_var () in
		
		let cmds_e1, x_e1 = f e1 in 
		let cmds_e2, x_e2 = f e2 in 
		
		(* x1' := getValue ( x1) with err_lab *)
		let cmd_get_value_x1 = SLCall (new_var_x_e1, Literal (String getValueName), [ x_e1 ], Some ctx.tr_error_lab) in 
		(* x2' := getValue ( x2) with err_lab *)
		let cmd_get_value_x2 = SLCall (new_var_x_e2, Literal (String getValueName), [ x_e2 ], Some ctx.tr_error_lab) in
		(* x_r := ref-o(x1', x2') *) 
		let cmd = SLBasic (SAssignment (new_var, (ORef ((Var new_var_x_e1), (Var new_var_x_e2))))) in
		
		let new_cmds = [
			(None, None, cmd_get_value_x1); 
			(None, None, cmd_get_value_x2); 
			(None, None, cmd)
		] in  
		let cmds = List.concat [ cmds_e1; cmds_e2; new_cmds ] in 
		cmds, (Var new_var)
	
	
		
				
	
	| _ -> raise (Failure "not implemented yet")		


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
	let cmds_e, x_e = translate main cc_table [] ctx e in 
	(* x_ret := x_e *)
	let ret_ass = (None, None, SLBasic (SAssignment (ctx.tr_ret_var, x_e))) in
	(* lab_ret: skip *) 
	let lab_ret_skip = (None, (Some ctx.tr_ret_lab), (SLBasic SSkip)) in 
	(* lab_err: skip *) 
	let lab_err_skip = (None, (Some ctx.tr_error_lab), (SLBasic SSkip)) in 
	let main_cmds = 
		[ init_scope_chain_ass; lg_ass; this_ass] @ global_var_asses @ cmds_e @ [ret_ass; lab_ret_skip; lab_err_skip] in 
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
	
	
	
	
	