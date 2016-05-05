open JSIL_Logic_Syntax 

let absheap = JSIL_Logic_Syntax.create 1021 


(**
	| LNot				of jsil_logic_assertion
	| LTrue
	| LEq					of jsil_logic_expr * jsil_logic_expr
	| LLessEq			of jsil_logic_expr * jsil_logic_expr
	| LPointTo		of jsil_logic_expr * jsil_logic_expr * jsil_logic_expr
	| LEmp
 
*) 


let fresh_variable =
  let counter = ref 0 in
  let rec f name =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    v
  in f

let fresh_logical_variable variable =
  fresh_variable "lvar"

let normalize_expr expr = expr

let rec normalize_assertion ass (abs_heap : abstract_heap) abs_store pure_formulae = 
	match ass with 
	| LStar (ass_left, ass_right) -> 
		normalize_assertion ass_left abs_heap abs_store pure_formulae; 
		normalize_assertion ass_right abs_heap abs_store pure_formulae
	| LPointTo (PVar pvar, lexp2, lexp3) ->
		let absloc = (try AbstractStore.find abs_store pvar 
			with _ -> 
				let count = abs_heap.count in 
				let new_abs_loc = LocVar count in 
					abs_heap.count <- count  + 1; 
					new_abs_loc) in 
		let normalized_e2 = normalize_expr lexp2 in 
		let normalized_e3 = normalize_expr lexp3 in
		(match absloc with 
		| LocVar var -> 
			let var_field_mappings = try AbstractHeapM.find abs_heap var with _ -> raise (Failure "Error in Normalization") in
			AbstractHeapM.add abs_heap.aheap var ((normalized_e2, normalized_e3)::var_field_mappings) 
	 	| NormalVar var -> 
			let count = abs_heap.count in
			let new_abs_loc = LocVar count in 
					abs_heap.count <- count  + 1; 
					new_abs_loc
			)
	| _ -> raise (Failure "Unsupported assertion during normalization")

				
		


			
				 
	

	
	
	



 