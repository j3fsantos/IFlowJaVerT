open Pulp_Syntax
open Pulp_Procedure
open SSyntax_Translate
open SSyntax_Utils


let jsil_cmds ctx =
	let r1 = fresh_r () in
	let r2 = fresh_r () in
	let label1 = ctx.label_return in 
	let label2 = ctx.label_throw in  
	let aiFilha = fresh_r () in 
	let compileForYourLife = fresh_r () in 
	let compileForYourLife2 = fresh_r () in
	let compileForYourLife3 = fresh_r () in
		mk_stmts_empty_data 
			[ Basic (Assignment (mk_assign ctx.return_var (Expression (Literal (Num 1.0)))));
				Basic (Assignment (mk_assign r1 (Expression (Literal (Num 1.0))))); 
				Basic (Assignment (mk_assign r2 (Expression (Literal (Num 2.0))))); 
				GuardedGoto ((BinOp ((Var r2), (Comparison Equal), (Var r1))), aiFilha, compileForYourLife); 
		 		GuardedGoto ((BinOp ((Var r2), (Comparison Equal), (Literal(Type (ObjectType(Some Builtin)))))), aiFilha, compileForYourLife); 
				Basic (Assignment (mk_assign r1 (Expression (Literal (Num 4.0))))); 
				GuardedGoto ((BinOp ((Var r2), (Comparison Equal), (Literal(Type (ObjectType(Some Builtin)))))), label1, compileForYourLife2); 
				GuardedGoto ((BinOp ((Var r2), (Comparison Equal), (Literal(Type (ObjectType(Some Builtin)))))), aiFilha, compileForYourLife3); 
				Label aiFilha;
				Basic (Assignment (mk_assign r1 (Expression (Literal (Num 5.0)))));  
				Label compileForYourLife;
				Basic (Assignment (mk_assign r1 (Expression (Literal (Num 6.0))))); 
				Label compileForYourLife2;
				Basic (Assignment (mk_assign r1 (Expression (Literal (Num 7.0))))); 
				Label compileForYourLife3;
				Basic (Assignment (mk_assign r1 (Expression (Literal (Num 8.0)))));
				Label label1;
    		Label label2 ] 
	
let main () =
	let arg = fresh_r () in
	let ctx = create_ctx [] in
 	let fb = make_function_block Procedure_User  "maria_vanessa" (jsil_cmds ctx) [ arg ] ctx in
	let fb_str = Pulp_Syntax_Print.string_of_func_block fb in
	let sfb = jsil_to_sjsil_proc fb in 
	let sfb_sexpr = SSyntax_Print.sexpr_of_procedure sfb true in 
	    print_string ("Original program:\n" ^ fb_str ^ "\n");
			print_string ("Compiled Output:\n " ^ sfb_sexpr ^ "\n")

let _ = main()