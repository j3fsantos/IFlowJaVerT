open JSIL_Syntax
open JSIL_Utils

let setup_internal_macros () = 
		
	let macro_definitions = [ 
		"macro : GPVFold (x, pi1, pi2, pi3, pi4, pi5) : if ((typeOf(x) = $$list_type)) then { if (((l-nth(x, 0) = \"o\") or ((l-nth(x, 0) = \"v\") and (l-nth(x, 1) = $lg)))) then { fold Pi(l-nth(x, 1), l-nth(x, 2), pi1, pi2, pi3, pi4, pi5) } };";
		"macro : GPVUnfold (x) : if ((typeOf(x) = $$list_type)) then { if (((l-nth(x, 0) = \"o\") or ((l-nth(x, 0) = \"v\") and (l-nth(x, 1) = $lg)))) then { unfold* Pi } };" ] in
		
	List.iter 
	(fun str ->
		let lexbuf = Lexing.from_string str in
  	lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
		let macro = parse_with_error JSIL_Parser.macro_target lexbuf in 
		Hashtbl.add macro_table macro.mname macro
	) macro_definitions