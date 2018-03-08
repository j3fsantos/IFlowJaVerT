open CCommon
open SCommon
open JSIL_Syntax
open Symbolic_State
open JSIL_Logic_Utils

exception UnificationFailure of string  

(** 
  *  Checks whether or not a substitution list is consistent. 
  *  If the same variable is mapped to two different logical expressions
  *  in a substitution list, then these expressions MUST be equal up to pfs. 
  *)
let consistent_subst_list 
		(subst_list : substitution_list) 
		(pfs        : PFS.t)
		(gamma      : TypEnv.t) : substitution_list option = 

	let start_time = Sys.time() in

	let subst = Hashtbl.create small_tbl_size in
	let result = List.fold_left (fun o_subst_list (x, le) -> 
		match o_subst_list with 
		| None -> None 
		| Some subst_list -> 
			try 
				let le_x = Hashtbl.find subst x in 
				if (Pure_Entailment.is_equal le_x le pfs gamma)
					then Some subst_list
					else None
			with _ ->
				Hashtbl.replace subst x le;
				Some ((x, le) :: subst_list) 
	) (Some []) subst_list in
		
	let end_time = Sys.time() in
	update_statistics "consistent_subst_list" (end_time -. start_time);
	result 


let safe_substitution_extension 
		(pfs        : PFS.t) 
		(gamma      : TypEnv.t) 
		(subst      : substitution) 
		(subst_list : substitution_list) : bool = 
	List.fold_left 
		(fun ac (x, le) -> 
			if (not ac) then ac else (
				try (
					Pure_Entailment.is_equal (Hashtbl.find subst x) le pfs gamma)
				with _ -> Hashtbl.replace subst x le; true)) 
		true subst_list 



let substitution_extension 
		(pfs        : PFS.t) 
		(gamma      : TypEnv.t) 
		(subst      : substitution) 
		(subst_list : substitution_list) : (jsil_logic_assertion list) option = 
	
	List.fold_left 
		(fun ac (x, le) ->
			match ac with 
			| None -> None 
			| Some constraints -> 
				try 
					let le_x = Hashtbl.find subst x in 
					if (Pure_Entailment.is_different le_x le pfs gamma) then
						None
					else Some ((LEq (le_x, le)) :: constraints)
				with _ -> Hashtbl.replace subst x le; ac)
		(Some []) subst_list 



let pre_check_discharges (discharges : discharge_list) : discharge_list option = Some discharges 

let type_check_discharges 
		(pat_gamma  : TypEnv.t)
		(gamma      : TypEnv.t)
		(discharges : discharge_list) : bool =
	
	let rets = List.map 
		(fun (le_pat, le) -> 
			let le_pat_tau, _, _ = JSIL_Logic_Utils.type_lexpr pat_gamma le_pat in
			let le_tau,     _, _ = JSIL_Logic_Utils.type_lexpr gamma     le in
			match le_pat_tau, le_tau with 
			| Some le_pat_tau, Some le_tau -> le_pat_tau = le_tau 
			| _ -> true 
		) discharges in
	List.for_all (fun x -> x) rets

let rec unify_lexprs
	(pfs         : PFS.t) 
	(gamma       : TypEnv.t) 
	(subst       : substitution)
	(le_pat      : jsil_logic_expr) 
	(le          : jsil_logic_expr) : (substitution_list * discharge_list) option =

	let start_time = Sys.time() in

	let le_pat = Reduction.reduce_lexpr ?gamma:(Some gamma) ?pfs:(Some pfs) le_pat in
	let le     = Reduction.reduce_lexpr ?gamma:(Some gamma) ?pfs:(Some pfs) le     in

	let rec unify_lexprs_rec le_pat le = 

		match le_pat with 
		| LVar x
		| ALoc x ->
			(try
				let le_pat_subst = (Hashtbl.find subst x) in
				if (Pure_Entailment.is_different le_pat_subst le pfs gamma)
					then None else if (le_pat = le) then Some ([], []) else Some ([], [ (le_pat, le) ])
			with _ -> 
				if (not (is_aloc_name x)) then Some ([ (x, le) ], []) else (
					let le_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le in
					match le_type with 
					| Some ObjectType -> Some ([ (x, le) ], [])
					| _               -> None )
			)

		| LLit _
		| LNone ->
			if (Pure_Entailment.is_equal le_pat le pfs gamma)
				then Some ([], []) else None

		| le_pat when ((Reduction.lexpr_is_list ?gamma:(Some gamma) le_pat) && (Reduction.lexpr_is_list ?gamma:(Some gamma) le)) ->
			let what_happened, to_unify_further = Simplifications.unify_lists le_pat le false in
			(match what_happened with
			| None -> None                            (* Something wrong happened *)
			| Some false -> Some ([], [ le_pat, le ]) (* Couldn't progress        *)
			| Some true -> let left, right = List.split to_unify_further in unify_lexpr_lists_rec left right)

		| _ -> Some ([], [ (le_pat, le) ] )

	and unify_lexpr_lists_rec lst_pat lst = 
		let rets = List.map2 unify_lexprs_rec lst_pat lst in 
		let ret_nones, ret_somes = List.partition (fun ret -> ret = None) rets in 
		if ((List.length ret_nones) > 0) then None else (
			let substs, dschrgs = List.split (List.map Option.get ret_somes) in 
			Some (List.concat substs, List.concat dschrgs)) in 

	let result = try (
		match unify_lexprs_rec le_pat le with 
		| None -> None 
		| Some (subst_list, discharges) -> 
			(match (consistent_subst_list subst_list pfs gamma), (pre_check_discharges discharges) with 
			| Some subst_list, Some discharges -> Some (subst_list, discharges)
			| _, _                             -> None)
	) with _ -> None in
	
	let end_time = Sys.time() in
	update_statistics "unify_lexprs" (end_time -. start_time);
	result 




let unify_stores 
		(pfs       : PFS.t) 
		(gamma     : TypEnv.t)
		(pat_subst : substitution) 
		(pat_store : SStore.t) 
		(store     : SStore.t) : discharge_list =

	print_debug_petar (Printf.sprintf "Unifying stores.\nCalling store: %s\nPat store: %s"
		(SStore.str store) (SStore.str pat_store));

	SStore.fold pat_store 
		(fun x le_pat discharges -> 
			match SStore.get store x with 
			| None    -> raise (UnificationFailure "")
			| Some le -> 
				(match unify_lexprs pfs gamma pat_subst le_pat le with 
				| Some (subst_list, new_discharges) -> 
					if (safe_substitution_extension pfs gamma pat_subst subst_list) 
						then new_discharges @ discharges
						else (
							print_debug "store_fold failed due to unsafe substitution extension\n"; 
							raise (UnificationFailure "") 
						) 
				| None -> 
						let discharge_sat = Pure_Entailment.check_satisfiability [ (LEq (le_pat, le)) ] gamma in
						(match discharge_sat with
						| true -> (le_pat, le) :: discharges
						| false ->
								print_debug "Store unification failure."; 
								raise (UnificationFailure "Store unification failure.")))) []

let unify_cell_assertion 
		(pfs           : PFS.t) 
		(gamma         : TypEnv.t)
		(pat_subst     : substitution) 
		(pat_cell_asrt : jsil_logic_assertion)
		(heap          : SHeap.t) : (SHeap.t * substitution * discharge_list) list = 

	let un_les = unify_lexprs pfs gamma pat_subst in 

	let start_time = Sys.time () in

	(* 1. Obtain the cell to unify *)
	let pat_loc, pat_field, pat_perm, pat_val = 
		match pat_cell_asrt with 
		| LPointsTo (LLit (Loc loc), le_field, (perm, le_val)) 
		| LPointsTo (ALoc loc, le_field, (perm, le_val)) -> loc, le_field, perm, le_val
		| _ -> 
				let msg = "DEATH. unify_cell_assertion. no cell assertion" in
				print_debug msg; raise (Failure msg) in 

    (* 2. Find the location corresponding to that cell *) 
	let loc = if (is_lloc_name pat_loc) then pat_loc else (
		try (
			match Normaliser.resolve_location_from_lexpr pfs (Hashtbl.find pat_subst pat_loc) with 
			| Some loc -> loc
			| None     -> raise (Failure "")   
		)  with _ -> 
			let msg = Printf.sprintf "DEATH. unify_cell_assertion. unmatched pat_loc: %s" pat_loc in 
			print_debug msg; raise (Failure msg)) in 

	(* 3. Get the fv_list and domain *)
	let fv_list, dom, metadata, ext = 
		match SHeap.get heap loc with 
		| Some ((fv_list, dom), metadata, ext) -> fv_list, dom, metadata, ext 
		| None -> 
				let msg = "DEATH. unify_cell_assertion. loc not in the heap" in
				print_debug msg; raise (Failure msg) in 

	(* 4. Try to unify the cell assertion against a cell in fv_list *)
	let fv_list_frames = 
		SFVL.fold (fun field (perm, value) ac -> 
			(match un_les pat_field field with 
			| None -> ac 
			| Some (subst_field, discharges_field) -> 
				print_debug (Printf.sprintf "Field discharge length: %d" (List.length discharges_field));
				(match un_les pat_val value with 
				| None -> ac 
				| Some (subst_val, discharges_val) -> 
					print_debug (Printf.sprintf "Value discharge length: %d" (List.length discharges_val));
					let subst_list = subst_field @ subst_val in 
					let discharges = discharges_field @ discharges_val in 
					(match (consistent_subst_list subst_list pfs gamma), (pre_check_discharges discharges) with 
					| Some subst_list, Some discharges -> 
							let pat_subst     = Hashtbl.copy pat_subst in 
          		if (safe_substitution_extension pfs gamma pat_subst subst_list) then (
          			let heap_frame    = SHeap.copy heap in 
          			let fv_list_frame = SFVL.remove field fv_list in 
          			SHeap.put heap_frame loc fv_list_frame dom metadata ext; 
          			(heap_frame, pat_subst, discharges) :: ac
							) else ac					
					| _, _ -> ac)))) fv_list [] in 

	(* 5. Try to unify the cell assertion using the domain info *)
	let dom_frame =
		(match un_les pat_val LNone, dom with 
		| _, None        
		| None, _ -> [] 
		| Some (subst_field, discharges_field), Some le_dom ->
			let pat_subst = Hashtbl.copy pat_subst in 
    		if (not (safe_substitution_extension pfs gamma pat_subst subst_field)) then [] else (
    			let s_pat_field  = lexpr_substitution pat_subst true pat_field in
				let a_set_inclusion = LNot (LSetMem (s_pat_field, le_dom)) in 
				if (not (Pure_Entailment.check_entailment SS.empty (PFS.to_list pfs) [ a_set_inclusion ] gamma)) then [] else (
					let heap_frame = SHeap.copy heap in 
					let new_domain = LSetUnion [ le_dom; LESet [ s_pat_field ] ] in (* NORMALISE_LEXPR *)
					let new_domain = Reduction.reduce_lexpr ?gamma:(Some gamma) ?pfs:(Some pfs) new_domain in
					SHeap.put heap_frame loc fv_list (Some new_domain) metadata ext; 
					[ (heap_frame, pat_subst, (discharges_field)) ]
			))) in 

	let result = dom_frame @ fv_list_frames in
	print_debug (Printf.sprintf "Result has %d frames." (List.length result));

	let end_time = Sys.time() in
	update_statistics "unify_cell_assertion" (end_time -. start_time);
	result 

let unify_pred_assertion 
		(pfs           : PFS.t) 
		(gamma         : TypEnv.t)
		(pat_subst     : substitution) 
		(pat_pred_asrt : jsil_logic_assertion)
		(preds         : predicate_set) : (predicate_set * substitution * discharge_list) list = 

	let un_les = unify_lexprs pfs gamma pat_subst in 

	let start_time = Sys.time () in

	(* 1. Obtain the pred asrt to unify *)
	let pat_pname, pat_pargs =
		match pat_pred_asrt with 
		| LPred (p_name, p_args) -> p_name, p_args 
		| _ -> raise (Failure "DEATH: Predicate assertion mismatch") in 

	(* 2.  *)
	let preds_lst = preds_to_list preds in 
	let frames = 
		List.mapi (fun i (pname, pargs) -> 
			if (pname <> pat_pname) then None else (
				print_debug ("Predicate: " ^ pname);
				print_debug (Printf.sprintf "\tppargs: %s" (String.concat ", " (List.map JSIL_Print.string_of_logic_expression pat_pargs)));
				print_debug (Printf.sprintf "\tcpargs: %s" (String.concat ", " (List.map JSIL_Print.string_of_logic_expression pargs)));
				let ret_un_args = List.map2 un_les pat_pargs pargs in 
				let ret_un_args_nones, ret_un_args_somes = List.partition (fun ret -> ret = None) ret_un_args in
				if ((List.length ret_un_args_nones) > 0) then None else (
					let substs, dschrgs = List.split (List.map Option.get ret_un_args_somes) in 
					Some (i, List.concat substs, List.concat dschrgs)
				) 
			)
		) preds_lst in 
	let frames = List.filter (fun x -> not (x = None)) frames in 
	let frames = List.map Option.get frames in
	let frames = List.map (fun (i, subst_list, discharges) -> 
    		let pat_subst = Hashtbl.copy pat_subst in 
    		if (safe_substitution_extension pfs gamma pat_subst subst_list) then (
    			let preds_frame = preds_copy preds in 
    			preds_remove_by_index preds_frame i; 
    			Some (preds_frame, pat_subst, discharges)
    		) else None 
		) frames in
	let frames = List.map Option.get (List.filter (fun x -> x <> None) frames) in
	
	let end_time = Sys.time() in
	update_statistics "unify_pred_assertion" (end_time -. start_time);
	frames  


let rec find_missing_nones 
		(pfs            : PFS.t)
		(gamma          : TypEnv.t)
		(fields_to_find : jsil_logic_expr list) 
		(none_fv_list   : SFVL.t) : SFVL.t =
	
	let fmn = find_missing_nones pfs gamma in 

	let rec find_missing_none 
			(missing_field          : jsil_logic_expr)
			(none_fv_list           : SFVL.t) : SFVL.t =
		(match SFVL.get missing_field none_fv_list with
		| Some result -> SFVL.remove missing_field none_fv_list
		| None -> 
			Option.map_default 
			(fun (ffn, ffv) -> SFVL.remove ffn none_fv_list)
			none_fv_list
			(SFVL.get_first (fun name -> Pure_Entailment.is_equal name missing_field pfs gamma) none_fv_list)) in

	match fields_to_find with
	| [] -> none_fv_list
	| f_name :: rest_fields ->
		(* print_debug (Printf.sprintf "I need to find %s \n" (JSIL_Print.string_of_logic_expression f_name false)); *) 
		let rest_none_fv_list = find_missing_none f_name none_fv_list in
		fmn rest_fields rest_none_fv_list  


let unify_domains 
		(pfs       : PFS.t)
		(gamma     : TypEnv.t)
		(pat_subst : substitution)
		(pat_dom   : jsil_logic_expr) 
		(dom       : jsil_logic_expr) 
		(fv_list   : SFVL.t) 
		(perm      : Permission.t) : SFVL.t =
			
	print_debug_petar "Entering unify_domains.";

	(* 1. Split fv_list into two - fields mapped to NONE and the others                   *) 
	let none_fv_list, non_none_fv_list = SFVL.partition (fun field (_, value) -> value = LNone) fv_list in
	
	(* 2. Find domain_difference = -{ f_1, ..., f_n }- = dom \ subst(pat_dom) 
	      The fields f_1, ..., f_n MUST be NONE                                           *) 
	let s_pat_dom         = lexpr_substitution pat_subst true pat_dom in
	let domain_difference = LBinOp (dom, SetDiff, s_pat_dom) in (* NORMALISE_LEXPR *)
	let domain_difference = Simplifications.reduce_expression_using_pfs_no_store gamma pfs domain_difference in

	(* 3. Find domain_frame_difference = -{ f_1', ..., f_n' }- = pat_subst(pat_dom)  \ dom  
	      The fields f_1', ..., f_n' MUST be added to the frame                           *) 
	let domain_frame_difference = LBinOp (s_pat_dom, SetDiff, dom) in (* NORMALISE_LEXPR *)
	let domain_frame_difference = Simplifications.reduce_expression_using_pfs_no_store gamma pfs domain_frame_difference in
	
	(* 4. We can only process explicit sets                                               *) 
	let domain_difference, domain_frame_difference =
		print_debug (Printf.sprintf "DD %s, DFD %s" (JSIL_Print.string_of_logic_expression domain_difference) (JSIL_Print.string_of_logic_expression domain_frame_difference));
		(match domain_difference, domain_frame_difference with
			| LESet domain_difference, LESet domain_frame_difference -> domain_difference, domain_frame_difference
			| _, _ -> 
				let msg = Printf.sprintf "Cannot currently handle: DD %s, DFD %s" (JSIL_Print.string_of_logic_expression domain_difference) (JSIL_Print.string_of_logic_expression domain_frame_difference) in
				print_debug msg; raise (UnificationFailure msg)) in

	(*
	let none_q_v_list_strs = List.map (fun (field, value) -> JSIL_Print.string_of_logic_expression field false) none_q_v_list in
	let none_q_v_list_str = String.concat ", " none_q_v_list_strs in
	print_debug (Printf.sprintf "caralho none_q_v_list: %s\n" none_q_v_list_str);         *)

	(* 5. Finding the missing NONEs (given by the domain difference) in the none_fv_list  *)
	let non_matched_none_fields = find_missing_nones pfs gamma domain_difference none_fv_list in

	(* 6. When dom is smaller than pat_dom, then the footprint of the associated EF 
	      assertion is bigger. In this case, the fields in (pat_dom / dom) need to be 
	      explicitly none cells in the framed heap - but with which permission?! TODO       *)
	let new_none_fv_list = List.fold_left (fun ac le -> SFVL.add le (perm, LNone) ac) (SFVL.empty) domain_frame_difference in

	(* 7. The returned framed fv_list is composed of:   
	        i)  the non-NONE fields in the original fv-list 
	       ii)  the NONE fields that were not used to compensate the domain_difference
	      iii)  the NONE fields that resulted from the domain_frame_difference *)
	SFVL.union non_none_fv_list (SFVL.union non_matched_none_fields new_none_fv_list)


 let unify_empty_fields_assertion 
		(pfs           : PFS.t) 
		(gamma         : TypEnv.t)
		(pat_subst     : substitution) 
		(pat_ef_asrt   : jsil_logic_assertion)
		(heap          : SHeap.t) : (SHeap.t * substitution * discharge_list) list = 

	let start_time = Sys.time () in

	(* 1. Obtain the EF to unify *)
	let pat_loc, pat_dom = 
		match pat_ef_asrt with 
		| LEmptyFields (LLit (Loc loc), dom) 
		| LEmptyFields (ALoc loc, dom) -> loc, dom 
	  	| _ -> print_debug "DEATH 1"; raise (Failure "DEATH. unify_empty_fields_assertion. no EF assertion") in 

	(* 2. Find the location corresponding to that EF assertion *) 
	let loc = if (is_lloc_name pat_loc) then pat_loc else (
		try (
			match Normaliser.resolve_location_from_lexpr pfs (Hashtbl.find pat_subst pat_loc) with 
			| Some loc -> loc
			| None     -> raise (Failure "")
		) with _ -> raise (Failure "DEATH. unify_empty_fields_assertion. unmatched pat_loc")) in 

	(* 3. Get the fv_list and domain *)
	let fv_list, dom, metadata, ext = 
		match SHeap.get heap loc with 
		| Some ((fv_list, dom), metadata, ext) -> fv_list, dom, metadata, ext 
		| None                                 -> print_debug "No location for EF assertion"; raise (Failure "DEATH") in 

	(* 4. Unifying the domains if they exist *)
	let result = (match dom with
	| None                   -> 
		(*  i. pat_domain exists but no domain exists -> entailment fails! *)
		[ ]                       
	| Some dom ->     
		(* ii. pat_domain and domain exist -> we have to check the entailment *)                      
		try 
			(* THIS IS NOT CLEAR AT ALL *)
			let perm : Permission.t = if (ext = Some Extensible) then Deletable else Readable in (* TODO *)
			let fv_list_frame  = unify_domains pfs gamma pat_subst pat_dom dom fv_list perm in 
			let heap_frame     = SHeap.copy heap in 
			SHeap.put heap_frame loc fv_list_frame None metadata ext;
			[ (heap_frame, pat_subst, []) ]
		with _ -> []) in
	
	let end_time = Sys.time() in
	update_statistics "unify_empty_fields_assertion" (end_time -. start_time);
	result

(* TODO : THIS IS NOT SPATIAL?! *)
let unify_metadata_assertion
		(pfs           : PFS.t) 
		(gamma         : TypEnv.t)
		(pat_subst     : substitution) 
		(pat_cell_asrt : jsil_logic_assertion)
		(heap          : SHeap.t) : (SHeap.t * substitution * discharge_list) list = 
	
	let un_les = unify_lexprs pfs gamma pat_subst in 
	
	(* 1. Obtain the cell to unify *)
	let pat_loc, pat_metadata = 
		match pat_cell_asrt with 
		| LMetaData (LLit (Loc loc), metadata) 
		| LMetaData (ALoc loc, metadata) -> loc, metadata
		| _ ->
				let msg = "Unify_metadata_assertion: no metadata assertion" in
				print_debug msg; raise (Failure msg) in 

  (* 2. Find the location corresponding to that cell *) 
	let loc = if (is_lloc_name pat_loc) then pat_loc else (
		try (
			match Normaliser.resolve_location_from_lexpr pfs (Hashtbl.find pat_subst pat_loc) with 
			| Some loc -> loc
			| None     -> raise (Failure "")   
		)  with _ -> 
			let msg = Printf.sprintf "Unify_metadata_assertion: unmatched pat_loc: %s" pat_loc in 
				print_debug msg; raise (Failure msg)) in 

	(* 3. Get the metadata *)
	let fv_list, domain, metadata, ext = 
		match SHeap.get heap loc with 
		| Some ((fv_list, domain), metadata, ext) -> fv_list, domain, metadata, ext 
		| None ->
				let msg = "Unify_metadata_assertion: loc not in the heap" in
				print_debug msg; raise (Failure msg) in 

	(* 4. Try to unify the metadata *)
	let result = 
		(match metadata with
		(* What happens here? *)
		| None -> []
		| Some metadata -> 
  		(match un_les pat_metadata metadata with
  		| None -> [ ]
  		| Some (subst_meta, discharges_meta) ->
  				(match (consistent_subst_list subst_meta pfs gamma), (pre_check_discharges discharges_meta) with
  				| Some subst_meta, Some discharges_meta ->
  						let pat_subst = Hashtbl.copy pat_subst in
  						if (safe_substitution_extension pfs gamma pat_subst subst_meta) then 
  							[ (heap, pat_subst, discharges_meta) ]
  						else [ ]
  				| _, _ -> [ ]))) in
	
	result

let unify_extensible_assertion
		(pfs           : PFS.t) 
		(gamma         : TypEnv.t)
		(pat_subst     : substitution) 
		(pat_cell_asrt : jsil_logic_assertion)
		(heap          : SHeap.t) : (SHeap.t * substitution * discharge_list) list =

	(* 1. Obtain the cell to unify *)
	let pat_loc, pat_ext = 
		match pat_cell_asrt with 
		| LExtensible (LLit (Loc loc), b) 
		| LExtensible (ALoc loc, b) -> loc, b
		| _ -> raise (Failure "Unify_extensible_assertion: no extensible assertion") in 

  (* 2. Find the location corresponding to that cell *) 
	let loc = if (is_lloc_name pat_loc) then pat_loc else (
		try (
			match Normaliser.resolve_location_from_lexpr pfs (Hashtbl.find pat_subst pat_loc) with 
			| Some loc -> loc
			| None     -> raise (Failure "")   
		)  with _ -> 
			let msg = Printf.sprintf "Unify_metadata_assertion: unmatched pat_loc: %s" pat_loc in 
				raise (Failure msg)) in 

	(* 3. Get the extensibility *)
	let fv_list, domain, metadata, ext = 
		match SHeap.get heap loc with 
		| Some ((fv_list, domain), metadata, ext) -> fv_list, domain, metadata, ext 
		| None                -> raise (Failure "Unify_extensible_assertion: loc not in the heap") in 

	(* 4. Unify the extensibility *)
	(match ext with
	| None -> []
	| Some ext -> if (pat_ext = ext) then 
		(* FRAME OFF *)
		let heap_frame = SHeap.copy heap in
		SHeap.put heap loc fv_list domain metadata None;
		[ (heap, Hashtbl.copy pat_subst, [ ]) ] else [ ])

type intermediate_frame = SHeap.t * predicate_set * discharge_list * substitution 

let unify_spatial_assertion
		(pfs           : PFS.t) 
		(gamma         : TypEnv.t)
		(pat_subst     : substitution) 
		(pat_s_asrt    : jsil_logic_assertion)
		(heap          : SHeap.t) 
		(preds         : predicate_set) :  intermediate_frame list =

	let start_time = Sys.time() in
	
	let result = (match pat_s_asrt with 
	| LPointsTo _ -> 
		List.map 
			(fun (h_f, pat_subst, discharges) -> (h_f, preds_copy preds, discharges, pat_subst)) 
			(unify_cell_assertion pfs gamma pat_subst pat_s_asrt heap) 

	| LPred _ -> 
		List.map 
			(fun (p_f, pat_subst, discharges) -> (SHeap.copy heap, p_f, discharges, pat_subst)) 
			(unify_pred_assertion pfs gamma pat_subst pat_s_asrt preds) 

	| LEmptyFields _ -> 
		List.map 
			(fun (h_f, pat_subst, discharges) -> (h_f, preds_copy preds, discharges, pat_subst)) 
			(unify_empty_fields_assertion pfs gamma pat_subst pat_s_asrt heap)  
	
	| LMetaData _ ->
		List.map 
			(fun (h_f, pat_subst, discharges) -> (h_f, preds_copy preds, discharges, pat_subst)) 
			(unify_metadata_assertion pfs gamma pat_subst pat_s_asrt heap)

	| LExtensible _ ->
		List.map 
			(fun (h_f, pat_subst, discharges) -> (h_f, preds_copy preds, discharges, pat_subst)) 
			(unify_extensible_assertion pfs gamma pat_subst pat_s_asrt heap)

	| _ -> raise (Failure "DEATH: Unsupported spatial assertion")) in
	
	let end_time = Sys.time() in
	update_statistics "unify_spatial_assertion" (end_time -. start_time);
	
	result


let unify_gammas 
		(pat_subst : substitution) 
		(pat_gamma : TypEnv.t) 
		(gamma     : TypEnv.t) : bool =

	let start_time = Sys.time() in

	let result = TypEnv.fold pat_gamma
		(fun x x_type ac ->
			if (not ac) then ac else (
				try 
					let le_x          = Hashtbl.find pat_subst x in 
					let le_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le_x in
					(match le_type with
					| Some le_type ->
						if (le_type <> x_type) then (
							print_debug (Printf.sprintf "unify_gamma. pat gamma: %s. gamma: %s. pat_type: %s. type: %s"
								x (JSIL_Print.string_of_logic_expression le_x) (Type.str x_type) (Type.str le_type));
							false 
						) else true 
					| None ->
						print_debug (Printf.sprintf "failed unify_gamma. pat gamma: %s. gamma: %s. pat_type: %s. type: None"
							x (JSIL_Print.string_of_logic_expression le_x) (Type.str x_type));
						false)
				with Not_found -> true)) true in 
	
	let end_time = Sys.time() in
	update_statistics "unify_gammas" (end_time -. start_time);
	print_debug (Printf.sprintf "unify_gammas result: %b" result); 
	
	result


let pf_list_of_discharges 
		(pat_subst : substitution)
		(discharges : discharge_list) : (jsil_logic_assertion list) =	
	List.map (fun (le_pat, le) -> 
		let s_le_pat = JSIL_Logic_Utils.lexpr_substitution pat_subst false le_pat in 
		LEq (s_le_pat, le)
	) discharges  

let filter_gamma_with_subst gamma vars subst =
	let new_gamma = TypEnv.init () in
	TypEnv.iter gamma
		(fun v v_type ->
			(if (List.mem v vars) then
				try
					match (Hashtbl.find subst v) with
					| LVar new_v -> TypEnv.update new_gamma new_v (Some v_type)
					| _ -> ()
				with Not_found -> ()));
	new_gamma


let unify_pfs 
		(pat_subst    : substitution) 
		(existentials : string list)
		(pat_lvars    : SS.t)
		(pat_gamma    : TypEnv.t) 
		(pat_pfs      : PFS.t)
		(gamma        : TypEnv.t) 
		(pfs          : PFS.t)
		(discharges   : discharge_list) : bool * (jsil_logic_assertion list) * (jsil_logic_assertion list) * TypEnv.t * SS.t =

	let start_time = Sys.time() in

	(* 1. pat_existentials = pat_vars \ dom(pat_subst)                                                  *)
	let pat_existentials = SS.elements (SS.filter (fun x -> not (Hashtbl.mem pat_subst x)) pat_lvars) in 
					
	(* 2. pat_subst = pat_subst + [ x_i -> fresh_lvar() ]_{ x_i \in pat_existentials }                  *) 
	let fresh_names_for_pat_existentials = List.map (fun v -> fresh_lvar ()) pat_existentials in
	let subst_pat_existentials           = init_substitution2 pat_existentials (List.map (fun x -> LVar x) fresh_names_for_pat_existentials) in
	extend_substitution pat_subst pat_existentials (List.map (fun x -> LVar x) fresh_names_for_pat_existentials);	

	(* 3. gamma' = gamma + gamma_pat_existentials
	      where gamma_pat_existentials(x) = pat_gamma(y) iff x = pat_subst(y) /\ y \in pat_existentials *)
	let gamma' =
		if ((List.length pat_existentials) = 0) then gamma else (
			let gamma_pat_existentials = filter_gamma_with_subst pat_gamma pat_existentials subst_pat_existentials in
			let gamma'                 = TypEnv.copy gamma in
			TypEnv.extend gamma' gamma_pat_existentials; gamma'			
		) in 
		
	(* 4. pfs |-_{gamma'} Exists_{existentials + pat_existentials} pat_subst(pat_pfs) /\ pf_list_of_discharges(discharges) *)
	let s_pat_pfs      = List.map (asrt_substitution pat_subst true) (PFS.to_list pat_pfs) in
	let pfs_discharges = pf_list_of_discharges pat_subst discharges in
	let pfs_to_prove   = s_pat_pfs @ pfs_discharges in
	print_debug (Printf.sprintf "Checking if %s\n entails %s\n with existentials\n%s\nand gamma %s"
		(Symbolic_State_Print.string_of_pfs pfs)
		(Symbolic_State_Print.string_of_pfs (PFS.of_list pfs_to_prove))
		(String.concat ", "  (existentials @ fresh_names_for_pat_existentials))
		(TypEnv.str gamma')); 
	let entailment_check_ret = Pure_Entailment.check_entailment (SS.of_list (existentials @ fresh_names_for_pat_existentials)) (PFS.to_list pfs) pfs_to_prove gamma' in
	print_debug (Printf.sprintf "entailment_check: %b" entailment_check_ret);

	(* 5. Constraints on the existentials - they come from the pat_pfs and from the discharges          *)
	let existentials_set = SS.of_list (existentials @ fresh_names_for_pat_existentials) in 
	let pfs_existentials = 
		List.filter 
			(fun a -> not (SS.is_empty (SS.inter existentials_set (get_asrt_lvars a)))) 
			pfs_to_prove in 

	(* 6. Return                                                                                        *)
	let result = entailment_check_ret, pfs_existentials, pfs_discharges, gamma', (SS.of_list fresh_names_for_pat_existentials) in
	
	let end_time = Sys.time() in
	update_statistics "unify_pfs" (end_time -. start_time);
	
	result


type extended_intermediate_frame = unification_plan * intermediate_frame * jsil_logic_assertion list * SS.t 

let rec unify_symb_states 
		(predicates            : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t)
		(existentials          : SS.t) 
		(spec_vars             : SS.t) 
		(pat_unification_plan  : unification_plan) 
		(pat_subst             : substitution option)
		(pat_symb_state        : symbolic_state) 
		(symb_state            : symbolic_state) : (bool * symbolic_state_frame) option =


	let heap, store, pfs, gamma, preds                     = symb_state in
	let pat_heap, pat_store, pat_pfs, pat_gamma, pat_preds = pat_symb_state in
	let pat_lvars = (ss_lvars pat_symb_state) in 

	print_debug (Printf.sprintf "STARTING: unify_symb_states with UP: %s.\n" 
			(Symbolic_State_Print.string_of_unification_plan pat_unification_plan)); 

	(* 1. Init the substitution          *)
	let pat_subst  = Option.default (init_substitution []) pat_subst in


	(* 2. Unify stores                   *)
	(*  2.1 - find the pvars that are mapped to expressions containing existentials                            *)
	(*  2.2 - unify the stores except for the pvars that are mapped to lexprs containing existentials          *)
	(*  let filtered_pvars  = { x : x \in dom(store) /\ ((lvars (store(x)) \cap existentials) \neq \emptyset } *)
	(*  let unfiltered_vars = \dom(store) \ filtered_vars                                                      *)
	(*  let store' = store|_{unfiltered_vars}                                                                  *)
	(*  let pat_store' = pat_store|_{unfiltered_vars}                                                          *)
	(*  let discharges = { (le_pat, le) | x \in filtered_vars /\ le = store(x) /\ le_pat = pat_store(x)        *)
	(*  let discharges' = unify_stores (pfs, gamma, pat_subst, new_store, new_pat_store)	                   *)
	(*  TypeCheck(discharges')                                                                                 *)
	let unfiltered_vars, filtered_vars = SStore.partition store 
		(fun le -> SS.is_empty (SS.inter (get_lexpr_lvars le) existentials)) in  					
	let store'      = SStore.projection store     unfiltered_vars in
	let pat_store'  = SStore.projection pat_store unfiltered_vars in
	let discharges  = List.map 
		(fun x -> 
			match SStore.get pat_store x, SStore.get store x with 
			| Some le_pat_x, Some le_x -> (le_pat_x, le_x)
			| _, _ -> raise (UnificationFailure "")) filtered_vars in 
	let discharges' = (unify_stores pfs gamma pat_subst pat_store' store') in 
	print_debug (Printf.sprintf "unify_stores - done. pat_subst: %s\ndischarges: %s\n"
		(JSIL_Print.string_of_substitution pat_subst)
		(Symbolic_State_Print.string_of_discharges (discharges @ discharges')));
	if (not (type_check_discharges pat_gamma gamma discharges')) then raise (UnificationFailure "");	



	(* 3. Find type information for the existentials using the pat_symb_state and extend the current  gamma  
	      with that additional information                                                                     *)
	(*  Find gamma_existentials st                                                                             *)
	(*   dom(gamma_existentials) \subseteq existentials                                                        *)
	(*   forall x \in filtered_vars :                                                                          *)
	(* 	   (pat_gamma |- pat_store(x) : tau) => (gamma + gamma_existentials |- store(x) : tau                  *)
	let gamma_existentials = TypEnv.init () in
	List.iter
		(fun x ->
			match SStore.get store x, TypEnv.get pat_gamma x with
			| Some le_x, Some x_type -> let _ = JSIL_Logic_Utils.infer_types_to_gamma false gamma gamma_existentials le_x x_type in ()
			|	_, _ -> ())
		filtered_vars;
	let gamma_existentials = TypEnv.filter_vars gamma_existentials existentials in	
	TypEnv.extend gamma_existentials gamma;
	let gamma = gamma_existentials in 


	(* 4. Initial frame for the search *)
	let initial_frame = pat_unification_plan, (heap, preds, discharges @ discharges', pat_subst), [] in 


	(* 5. SEARCH *)
	let rec search 
			(frame_list            : extended_intermediate_frame list) 
			(found_partial_matches : symbolic_state_frame list) : (bool * symbolic_state_frame) option = 
		match frame_list with 
		| [] -> 
			(match found_partial_matches with 
			| [] -> raise (UnificationFailure "")
			| ssf :: _ -> Some (false, ssf))


		| (up, (heap_frame, preds_frame, discharges, pat_subst), pfs_to_check, existentials) :: rest_frame_list -> 	
			(match up with 
			| [] -> 
					(* A - All the spatial resources were successfully unified *)
				print_debug (Printf.sprintf "STARTING unify_pfs and gammas. pat_subst: %s\ndischarges: %s\n"
					(JSIL_Print.string_of_substitution pat_subst)
					(Symbolic_State_Print.string_of_discharges discharges)); 

					(* A.2 - Unify remaining pfs *)
					let complete_match_b, pfs_existentials, pfs_discharges, new_gamma, new_existentials = 
						unify_pfs pat_subst (SS.elements existentials) pat_lvars pat_gamma (DynArray.of_list pfs_to_check) gamma pfs discharges in 
					
					print_debug (Printf.sprintf "DONE with unify_pfs and gammas. ret: %b.\nexistentials: %s.\npfs_existentials:%s\n" 
						complete_match_b 
						(String.concat ", " (SS.elements existentials))
						(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion pfs_existentials)));

					(* A.3 - If complete_match -> return
					         Otherwise, continue searching and register the partial match *)
					if (complete_match_b)
						then Some (true, (heap_frame, preds_frame, pat_subst, pfs_existentials @ pfs_discharges, new_gamma))
						else search rest_frame_list ((heap_frame, preds_frame, pat_subst, pfs_existentials @ pfs_discharges, new_gamma) :: found_partial_matches)


			| (LPointsTo _, _) :: rest_up
			| (LEmptyFields _, _) :: rest_up 
			| (LMetaData _, _) :: rest_up
			| (LExtensible _, _) :: rest_up -> 

				print_debug (Symbolic_State_Print.string_of_unification_step (head_unification_plan up) pat_subst heap_frame preds_frame pfs gamma discharges); 

				(* B - Unify spatial assertion - no predicate assertion *)
				let new_frames : intermediate_frame list = unify_spatial_assertion pfs gamma pat_subst (head_unification_plan up) heap_frame preds_frame in 
				let new_frames : extended_intermediate_frame list = 
					List.map 
						(fun (h_f, p_f, new_discharges, pat_subst) -> rest_up, (h_f, p_f, (new_discharges @ discharges), pat_subst), pfs_to_check, existentials) 
						new_frames in 

				print_debug (Printf.sprintf "Unification result: %b\n" ((List.length new_frames) > 0)); 

				search (new_frames @ rest_frame_list) found_partial_matches


			| (LPred _, None) :: _ -> raise (Failure "DEATH unify_symb_states. misformed unification plan")
			| (LPred (p_name, largs), Some unify_as_is) :: rest_up -> 

				print_debug (Symbolic_State_Print.string_of_unification_step (head_unification_plan up) pat_subst heap_frame preds_frame pfs gamma discharges); 
				
				if unify_as_is then (		
					(* C - Unify pred assertion *)
					let new_frames = unify_pred_assertion pfs gamma pat_subst (head_unification_plan up) preds_frame in 
					let new_frames : extended_intermediate_frame list =
						List.map 
							(fun (p_f, pat_subst, new_discharges) -> rest_up, (SHeap.copy heap_frame, p_f, (new_discharges @ discharges), (copy_substitution pat_subst)), pfs_to_check, existentials) 
							new_frames in  

					print_debug (Printf.sprintf "Unification result: %b" ((List.length new_frames) > 0));

					let folding_pred_up = (LPred (p_name, largs), Some false) :: rest_up in
					let folding_frame   = folding_pred_up, (heap_frame, preds_frame, discharges, (copy_substitution pat_subst)), pfs_to_check in

					search (new_frames @ (folding_frame :: rest_frame_list)) found_partial_matches
				) 
				else (

						let largs' = List.map (lexpr_substitution pat_subst true) largs in

						print_debug (Printf.sprintf 
							"Predicate Assertion NOT FOUND. Trying to fold the predicate %s and substitution %s\n" 
							(JSIL_Print.string_of_logic_assertion (LPred (p_name, largs')))
							(JSIL_Print.string_of_substitution pat_subst));  

						let ss  = heap_frame, store, pfs, gamma, preds_frame in 
						let ret = try fold_predicate predicates p_name largs' spec_vars existentials ss None with (Failure _) -> None in 
						(match ret with 
						| Some (new_heap_frame, new_preds_frame, new_pat_subst, new_pfs, new_gamma) -> 
							print_debug_petar (Printf.sprintf "LOST: new_pfs:\n%s" (String.concat ", " (List.map JSIL_Print.string_of_logic_assertion new_pfs)));
							print_debug_petar (Printf.sprintf "LOST: new_gamma:\n%s" (TypEnv.str new_gamma));
							let _, new_subst = Simplifications.simplify_pfs_with_subst (DynArray.of_list new_pfs) new_gamma in 
							(match new_subst with | Some new_subst -> print_debug_petar (Printf.sprintf "LOST: Substitution:\n%s" (JSIL_Print.string_of_substitution new_subst)) | _ -> ());
							let new_frames = rest_up, (new_heap_frame, new_preds_frame, discharges, pat_subst), pfs_to_check in 
							search (new_frames :: rest_frame_list) found_partial_matches
						| None -> search rest_frame_list found_partial_matches)
					)

			| (LTypes type_asrts, _) :: rest_up ->

				print_debug (Symbolic_State_Print.string_of_unification_step (head_unification_plan up) pat_subst heap_frame preds_frame pfs gamma discharges); 

				let local_gamma = TypEnv.init () in
				List.iter (fun (x, typ) -> let x = match x with | LVar x -> x in TypEnv.update local_gamma x (Some typ)) type_asrts;
				if not (unify_gammas pat_subst local_gamma gamma) then (
					print_debug (Printf.sprintf "Failed type assertion %s; moving to next frame" (Symbolic_State_Print.string_of_unification_step (head_unification_plan up) pat_subst heap_frame preds_frame pfs gamma discharges));
					search rest_frame_list found_partial_matches
				)
				else 
					let new_frame = rest_up, (heap_frame, preds_frame, discharges, pat_subst), pfs_to_check in
					search (new_frame::rest_frame_list) found_partial_matches


			| (LEmp, _) :: _
			| (LStar _, _) :: _ -> 
				let asrt_str = JSIL_Print.string_of_logic_assertion (head_unification_plan up) in
					raise (Failure (Printf.sprintf "DEATH: Unknown assertion in unification plan (%s)." asrt_str))

	
			(* PURE FORMULAE *)
			| (pf, _) :: rest_up -> (* PURE FORMULAE *)

				print_debug (Symbolic_State_Print.string_of_unification_step (head_unification_plan up) pat_subst heap_frame preds_frame pfs gamma discharges); 

				(match pf with 
				(* We know le1, learning le2 *)
				| LEq (le1, le2) -> 
					let sle1 = lexpr_substitution pat_subst true le1 in 
					let more_pfs = Simplifications.subst_for_unification_plan ?gamma:(Some pat_gamma) le2 sle1 pat_subst in  
					(match more_pfs with 
					| None -> search rest_frame_list found_partial_matches
					| Some more_pfs -> 
						let pfs_to_check = pfs_to_check @ more_pfs in 
						print_debug_petar ("New pat subst:\n" ^ (JSIL_Print.string_of_substitution pat_subst));
						Hashtbl.iter (fun v le -> Hashtbl.replace pat_subst v (lexpr_substitution pat_subst true le) ) pat_subst;
						let new_frame = rest_up, (heap_frame, preds_frame, discharges, pat_subst), pfs_to_check in 
						search (new_frame :: rest_frame_list) found_partial_matches)
				| _ -> 
					let existentials = get_asrt_lvars pf in 
					let existentials = SS.diff existentials (substitution_domain pat_subst) in 
					(* Substitute in formula *)
					let pf_sbst = asrt_substitution pat_subst true pf in 
					(* Check if the current pfs entail the obtained substituted pf *)
					let pf_entailed : bool = Pure_Entailment.check_entailment existentials (PFS.to_list pfs) [ pf_sbst ] gamma in 
					(match pf_entailed with 
					| false -> 
						let new_frame = rest_up, (heap_frame, preds_frame, discharges, pat_subst), (pf :: pfs_to_check) in
							search (new_frame :: rest_frame_list) found_partial_matches
					| true -> 
						let new_frame = rest_up, (heap_frame, preds_frame, discharges, pat_subst), pfs_to_check in
							search (new_frame :: rest_frame_list) found_partial_matches))
				
			) in 
	let start_time = Sys.time() in
	let result = search [ initial_frame ] [] existentials in
	let end_time = Sys.time() in
	update_statistics "unify_ss : search" (end_time -. start_time);
	result


and 

(**********************************************)
(** Fold a predicate assertion recursively 
 *)
fold_predicate 
	(predicates   : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t)
	(pred_name    : string) 
	(args         : jsil_logic_expr list) 
	(spec_vars    : SS.t) 
	(existentials : SS.t) 
	(symb_state   : symbolic_state) 
	(pat_subst    : substitution option) : symbolic_state_frame option =


	let predicate          = (try Hashtbl.find predicates pred_name with Not_found -> raise (Failure "DEATH. fold_predicate")) in 
	let pred_defs          = Array.of_list predicate.n_pred_definitions in 
	let params             = predicate.n_pred_params in 
	let out_params_indexes = get_out_parameters predicate in 


	(*  Step 0: compute the new existentials
	    -------------------------------------------------------------- *)
	let args_with_existentials = List.mapi (fun (i : int) (x : jsil_logic_expr) -> if (SI.mem i out_params_indexes) then Some x else None) args in 
	let args_with_existentials = List.filter (Option.map_default (fun _ -> true) false) args_with_existentials in 
	let args_with_existentials = List.map (Option.get) args_with_existentials in 
	let new_existentials       = List.fold_left (fun ac x -> SS.union (get_lexpr_lvars x) ac) SS.empty args_with_existentials in 
	let new_existentials       = Option.map_default (fun subst -> SS.diff new_existentials (substitution_domain subst)) new_existentials pat_subst in  
	let new_existentials       = SS.union existentials new_existentials in 


	(*  Step 1: create a symb_state with the appropriate calling store
	    --------------------------------------------------------------
	    * Create the symbolic store mapping the formal parameters of the 
	      predicate to be folded to the corresponding logical expressions
	    * Create a new symb_state with the new calling store    *)
	print_debug_petar ("Inside fold_predicate.");
	print_debug_petar (Printf.sprintf "Arguments: %s" (String.concat ", " (List.map (fun x -> JSIL_Print.string_of_logic_expression x) args)));
	let new_store         = SStore.init params args in
	let symb_state_caller = ss_replace_store symb_state new_store in

	let rec fold_predicate_aux (index : int) : symbolic_state_frame option =
		if (index >= (Array.length pred_defs)) then None else (

			print_time_debug ("check_pred_def:");
			let _, pred_def, pred_def_up = Array.get pred_defs index in
			print_debug (Printf.sprintf "----------------------------");
			print_debug (Printf.sprintf "Current pred symbolic state: %s" (Symbolic_State_Print.string_of_symb_state pred_def));
		
			let unifier = try unify_symb_states predicates new_existentials spec_vars pred_def_up pat_subst pred_def symb_state_caller
				with | UnificationFailure _ -> None in

			match unifier with
			| Some (true, ssf) -> Some ssf
			| _ -> fold_predicate_aux (index+1)) in 

	fold_predicate_aux 0 



let fully_unify_symb_state
		(intuitionistic       : bool) 
		(predicates           : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t)
		(spec_vars            : SS.t)
		(pat_unification_plan : unification_plan) 
		(pat_subst            : substitution option)
		(pat_symb_state       : symbolic_state) 
		(symb_state           : symbolic_state) : substitution =
	
	print_debug (Printf.sprintf "Fully_unify_symb_state.\nSymb_state:\n%s.\nPAT symb_state:\n%s"
		(Symbolic_State_Print.string_of_symb_state symb_state)
		(Symbolic_State_Print.string_of_symb_state pat_symb_state));

	try (
		let res = unify_symb_states predicates SS.empty spec_vars pat_unification_plan pat_subst pat_symb_state symb_state in
		match res, intuitionistic with
		| Some (true, (_, _, subst, _, _)), true -> subst

		| Some (true, (heap_f, preds_f, subst, _, _)), false ->
			let emp_heap  = SHeap.is_empty heap_f in
			let emp_preds = is_preds_empty preds_f in 
		 	if (emp_heap && emp_preds) then subst else
				let _ = if (emp_heap) then begin print_debug "Quotient heap empty.\n" end
							else begin print_debug (Printf.sprintf "Quotient heap left: \n%s\n" (SHeap.str heap_f)) end in
			
				let _ = if (emp_preds) then begin print_debug "Quotient predicates empty.\n" end
							else begin print_debug (Printf.sprintf "Quotient predicates left: \n%s\n" (Symbolic_State_Print.string_of_preds preds_f)) end in
				raise (UnificationFailure "")
		| _ -> raise (UnificationFailure "")
	) with UnificationFailure _ -> raise (UnificationFailure "")


let unify_lexprs_unfold
	(pfs         : PFS.t)
	(subst       : substitution)
	(le_pat      : jsil_logic_expr) 
	(le          : jsil_logic_expr) : (substitution_list * substitution_list * discharge_list) option =

	let old_le_pat = le_pat in 
	let old_le     = le in 
	let le_pat     = Normaliser.normalise_list_expressions le_pat in
	let le         = Normaliser.normalise_list_expressions le in 
	(* print_debug (Printf.sprintf "old_le: %s. le: %s. old_le_pat: %s. le_pat: %s"
		(JSIL_Print.string_of_logic_expression old_le false) (JSIL_Print.string_of_logic_expression le false)
		(JSIL_Print.string_of_logic_expression old_le_pat false) (JSIL_Print.string_of_logic_expression le_pat false)); *)

	let rec unify_lexprs_rec le_pat le = 
		match le_pat, le with 
		| LLit lit_pat, LLit lit -> if (lit_pat = lit) then Some ([ ], [ ], [ ]) else None 

		| LLit _, LVar x 
		| LNone,  LVar x -> Some ([ (x, le_pat) ], [ ], [ ]) 		
		
		| LVar x, LLit _ 
		| LVar x, LNone  -> Some ([ ], [( x, le) ], [ ])

		| ALoc pat_loc, LVar x -> 
			print_debug (Printf.sprintf 
					"WE ARE IN THE CASE WE THINK WE ARE IN. pat_loc: %s. lvar: %s\n" pat_loc x); 
			let loc = Option.map (fun (result, _) -> result) (Normaliser.resolve_location x (PFS.to_list pfs)) in
			(match loc with 
			| Some loc when is_lloc_name loc -> Some ([ ], [ (pat_loc, LLit (Loc loc)) ], [ ])
			| Some loc when is_aloc_name loc -> Some ([ ], [ (pat_loc, ALoc loc) ], [ ])
			| None     ->
				if (Hashtbl.mem subst x) then (
					Some ([ ], [ (pat_loc, Hashtbl.find subst x) ], [])
				) else (
					let new_aloc = ALoc (fresh_aloc ()) in
					Some ([ (x, new_aloc) ], [ (pat_loc, new_aloc) ], [])
				))
				
		| LVar x, ALoc loc -> Some ([ ], [ (x, le) ], [ ])

		| ALoc pat_loc, LLit (Loc _)
		| ALoc pat_loc, ALoc _       -> Some ([ ], [ (pat_loc, le) ], [ ])
		| ALoc _, LLit _
		| LLit _, ALoc _ -> None 

		| LEList pat_lst, _
		| LBinOp (LEList pat_lst, LstCat, _), _ ->
			(match le with 
			| LEList lst 
			| LBinOp (LEList lst, LstCat, _) -> 
				let min_len              = min (List.length lst) (List.length pat_lst) in
				let pat_lst_l, pat_lst_r = Normaliser.reshape_list le_pat min_len in 
				let lst_l, lst_r         = Normaliser.reshape_list le min_len in 
				if ((List.length pat_lst_l) <> (List.length lst_l)) then raise (Failure "DEATH") else (
					match unify_lexpr_lists_rec pat_lst_l lst_l with 
					| None -> None 
					| Some (substs, pat_substs, dschrgs) -> Some (substs, pat_substs, (pat_lst_r, lst_r) :: dschrgs))
			| _ -> Some ([], [], [ (le_pat, le) ]))

		| _ -> Some ([], [], [ (le_pat, le) ]) 

	and unify_lexpr_lists_rec lst_pat lst = 
		let rets = List.map2 unify_lexprs_rec lst_pat lst in 
		let ret_nones, ret_somes = List.partition (fun ret -> ret = None) rets in 
		if ((List.length ret_nones) > 0) then None else (
			let substs, pat_substs, dschrgs = Utils.split3 (List.map Option.get ret_somes) in 
			Some (List.concat substs, List.concat pat_substs, List.concat dschrgs)) in 

	unify_lexprs_rec le_pat le



let unify_stores_unfold 
		(pat_pfs   : PFS.t)
		(pat_gamma : TypEnv.t)
		(pat_subst : substitution)
		(pfs       : PFS.t)
		(gamma     : TypEnv.t)
		(subst     : substitution)
		(pat_store : SStore.t) 
		(store     : SStore.t) : (jsil_logic_assertion list) * (jsil_logic_assertion list) * discharge_list =

	SStore.fold pat_store 
		(fun x le_pat (constraints, pat_constraints, discharges) -> 
			match SStore.get store x with 
			| None    -> raise (UnificationFailure "")
			| Some le -> 
				(match unify_lexprs_unfold pfs subst le_pat le with 
				| Some (subst_list, pat_subst_list, new_discharges) -> 
					let new_constraints     = substitution_extension pfs gamma subst subst_list in 
					let new_pat_constraints = substitution_extension pat_pfs pat_gamma pat_subst pat_subst_list in

					(match new_constraints, new_pat_constraints with 
					| Some new_constraints, Some new_pat_constraints -> 
						new_constraints @ constraints, new_pat_constraints @ pat_constraints, new_discharges @ discharges 
					| _, _ ->
						print_debug (Printf.sprintf "Failed unify_stores_unfold. x: %s. le_pat: %s. le: %s.\nconstraints: %s.\npat_constraints: %s.\ndischarges: %s"
							x (JSIL_Print.string_of_logic_expression le_pat) (JSIL_Print.string_of_logic_expression le)
							(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion constraints))
							(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion pat_constraints))
							(Symbolic_State_Print.string_of_discharges discharges));  
						raise (UnificationFailure "")) 

				| None -> 
					print_debug (Printf.sprintf "Failed unify_stores_unfold. NO LE. x: %s. le_pat: %s. \nconstraints: %s.\npat_constraints: %s.\ndischarges: %s"
							x (JSIL_Print.string_of_logic_expression le_pat) 
							(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion constraints))
							(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion pat_constraints))
							(Symbolic_State_Print.string_of_discharges discharges));  
					raise (UnificationFailure ""))) ([], [], []) 


let is_sensible_subst (subst : substitution) (gamma_source : TypEnv.t) (gamma_target : TypEnv.t) : bool =
	Hashtbl.fold
		(fun x le ac ->
			if (not ac) then ac else (
				let le_type, _, _ = type_lexpr gamma_target le in
				let x_type = TypEnv.get gamma_source x in
				match le_type, x_type with 
				| Some le_type, Some x_type -> (le_type = x_type) 
				| _ -> true))
		subst true


(**
	unfold_store      - a mapping from the parameters of the predicate to the arguments given in the unfolding
 	subst             - substitution that maps some of the newly introduced existentials to logical expressions
	pat_subst         - pat_subst given by the unfolding info
	existentials      - new variables introduced in the unfold
	spec_vars         - logical variables that appear in the precondition
 	pat_symb_state    - the symbolic state corresponding to the definition of the predicate that we are trying to unfold
 	symb_state        - the current symbolic state minus the predicate that is to be unfolded	
*)
let unfold_predicate_definition 
		(unfold_store   : SStore.t)
		(subst          : substitution)
		(pat_subst      : substitution)
		(existentials   : SS.t)
		(spec_vars      : SS.t)
		(pat_symb_state : symbolic_state)
		(symb_state     : symbolic_state) : symbolic_state option = 
	try ( 
	(* PREAMBLE                                                                                                            *)
	let symb_state = ss_copy symb_state in
	let heap,             _,     pfs,     gamma,     preds = symb_state in
	let pat_heap, pat_store, pat_pfs, pat_gamma, pat_preds = pat_symb_state in
	let subst     = copy_substitution subst in 
	let pat_subst = copy_substitution pat_subst in  


	print_debug (Printf.sprintf "STARTING: unfold_predicate_definition.\npred_def_symb_state:%s\nsubst: %s\npat_subst:%s\nexistentials:%s\nstore:%s\n" 
		(Symbolic_State_Print.string_of_symb_state pat_symb_state)	
		(JSIL_Print.string_of_substitution subst)
		(JSIL_Print.string_of_substitution pat_subst)
		(String.concat ", " (SS.elements existentials))
		(SStore.str unfold_store)); 

	(* STEP 1 - Unify(pfs, gamm, pat_subst, subst, pat_store, store) = discharges                                          *)
	(* subst (store) =_{pfs} pat_subst (pat_store) provided that the discharges hold                                       *)
	(* we start by unifying the stores - this unification will produce two substituions: pat_subst and subst               *)
	(* pat_subst is to applied in the pat_symb_state and subst is to be applied in the symb_state                          *)
	(* The store unification also generates a list of discharges - discharges - which need to hold for the stores to match *)
	let constraints, pat_constraints, discharges = unify_stores_unfold pat_pfs pat_gamma pat_subst pfs gamma subst pat_store unfold_store in
	
	print_debug (Printf.sprintf "unfold_predicate_definition. step 1 - done.\nsubst: %s\npat_subst:%s\n.discharges:%s.\nconstraints:%s\npat_constraints:%s\n" 
		(JSIL_Print.string_of_substitution subst)
		(JSIL_Print.string_of_substitution pat_subst)
		(Symbolic_State_Print.string_of_discharges discharges)
		(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion constraints))
		(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion pat_constraints))); 

	(* STEP 2 - the store must agree on the types                                                                          *)
	(* forall x \in domain(store) = domain(pat_store) :                                                                    *)
	(*   (pat_gamma |- pat_store(x) : pat_tau)  /\ (gamma |- store(x) : tau) => pat_tau = tau                              *)
	let find_store_var_type store gamma x = (match SStore.get store x with
			| Some le_x -> let x_type, _, _ = JSIL_Logic_Utils.type_lexpr gamma le_x in x_type
			| None      -> None) in
	let dom_store       = SS.elements (SStore.domain unfold_store) in 
	let dom_pat_store   = SS.elements (SStore.domain pat_store) in 
	let store_types     = List.map (find_store_var_type unfold_store gamma) dom_store in
	let pat_store_types = List.map (find_store_var_type pat_store pat_gamma) dom_pat_store in
	List.iter2 (fun x (tau, pat_tau) -> match tau, pat_tau with 
		| Some t1, Some t2 -> if (not (t1 = t2)) then (
			print_debug (Printf.sprintf "unfold_predicate_definition. mismatching types for pvar %s. pat_type: %s. type: %s" 
				x (Type.str t2) (Type.str t1)); 
			raise (UnificationFailure ""))
		| _                -> ()) dom_store (List.combine store_types pat_store_types); 

	print_debug (Printf.sprintf "unfold_predicate_definition. step 2 - done.\n"); 

	(* STEP 3 - the substitutions need to make sense wrt the gammas                                                        *)
	(* forall x \in subst : subst(x) = le /\ gamma(x) = tau => pat_gamma |- le : tau                                       *)
	(* forall x \in pat_subst : pat_subst (x) = le /\ pat_gamma(x) = tau => gamma |- le : tau                              *)
	let subst_is_sensible     = is_sensible_subst subst gamma pat_gamma in
	let pat_subst_is_sensible = is_sensible_subst pat_subst pat_gamma gamma in
	if ((not subst_is_sensible) || (not pat_subst_is_sensible)) then raise (UnificationFailure "");  

	print_debug (Printf.sprintf "unfold_predicate_definition. step 3 - done.\n "); 

	(* STEP 4 -Find type information for the existentials using the pat_symb_state and extend the current  gamma  
	      with that additional information                                                                                 *)
	(*  Find gamma_existentials st                                                                                         *)
	(*   dom(gamma_existentials) \subseteq existentials                                                                    *)
	(*   forall x \in dom(pat_gamma) :                                                                                     *)
	(* 	   (pat_gamma |- pat_store(x) : tau) => (gamma + gamma_existentials |- store(x) : tau                              *)
	let gamma_existentials = TypEnv.init () in
	List.iter2
		(fun x (x_type, pat_x_type) -> 
			if ((x_type = None) && (pat_x_type <> None)) then (
				match SStore.get unfold_store x, pat_x_type with
				| Some le_x, Some pat_x_type -> let _ = JSIL_Logic_Utils.infer_types_to_gamma false gamma gamma_existentials le_x pat_x_type in ()
				|	_, _ -> ())) 
		dom_pat_store (List.combine store_types pat_store_types);
	let gamma_existentials = TypEnv.filter_vars gamma_existentials existentials in	
	TypEnv.extend gamma_existentials gamma;
	let gamma = gamma_existentials in 	

	print_debug (Printf.sprintf "unfold_predicate_definition. step 4 - done. gamma_existentials: %s\n"
		(TypEnv.str gamma_existentials)); 

	(* STEP 5 - check whether the pure formulae make sense together - new_pat_subst = subst (pat_subst (.))                 *)
	(* pfs' = subst(pfs), s_pat_pfs = new_pat_subst (pat_pfs)                                                               *)
	(* pfs_discharges = new_pat_subst ( discharges );                                                                       *)
	(* pfs_subst = pfs_of_subst ( subst|_{ spec_vars + existentials }  )                                                    *)
	(* pfs'' = pfs' + s_pat_pfs + pfs_discharges + pfs_subst                                                                *)
	(* gamma =  gamma + new_pat_subst (pat_gamma)                                                                           *)
	(* |-_{gamma} pfs                                                                                                       *)
	let new_pat_subst   = compose_partial_substitutions subst pat_subst in
	let constraints     = List.map (asrt_substitution subst true) constraints in 
	let pfs'            = PFS.to_list (pfs_substitution subst true pfs) in
	let s_pat_pfs       = PFS.to_list (pfs_substitution new_pat_subst false pat_pfs) in
	let pat_constraints = List.map (asrt_substitution new_pat_subst true) pat_constraints in 
	let pfs_discharges  = pf_list_of_discharges new_pat_subst discharges in 
	let pfs_subst       = substitution_to_list (filter_substitution_set (SS.union existentials spec_vars) subst) in 
	let pfs''           = pfs' @ s_pat_pfs @ pfs_discharges @ pfs_subst @ constraints @ pat_constraints in 
	TypEnv.extend gamma (TypEnv.substitution pat_gamma new_pat_subst false);
	Normaliser.extend_typing_env_using_assertion_info gamma pfs'';
	(* Printing useful info *)
	print_debug (Printf.sprintf "substitutions immediately before sat check.\nSubst:\n%s\nPat_Subst:\n%s"
		(JSIL_Print.string_of_substitution subst)
		(JSIL_Print.string_of_substitution new_pat_subst));
	print_debug (Printf.sprintf "About to check if the following is SATISFIABLE:\n%s\nGiven the GAMMA:\n%s"
		(JSIL_Print.str_of_assertion_list pfs'')
		(TypEnv.str gamma));
	(* Performing the satisfiability check *)
	if (not (Pure_Entailment.check_satisfiability pfs'' gamma)) then (
			print_debug("It is NOT satisfiable\n"); 
			raise (UnificationFailure "")); 

	print_debug (Printf.sprintf "unfold_predicate_definition. step 5 - done. all_pfs: %s\n"
		(String.concat ", " (List.map JSIL_Print.string_of_logic_assertion pfs''))); 

	(* STEP 6 - Finally unfold: Sigma_0, Sigma_1, subst, pat_subst, pfs, gamma                             *)
	(* subst(Sigma_0) + pat_subst(Sigma_1) + (_, _, pfs_discharges + pfs_subst, gamma , _)                 *)
	let symb_state = ss_substitution subst true symb_state in
	let unfolded_symb_state = Symbolic_State_Utils.merge_symb_states symb_state pat_symb_state new_pat_subst in
	pfs_merge (ss_pfs unfolded_symb_state) (PFS.of_list (pfs_discharges @ pfs_subst @ constraints @ pat_constraints));
	TypEnv.extend (ss_gamma unfolded_symb_state) gamma;
	Normaliser.extend_typing_env_using_assertion_info (ss_gamma unfolded_symb_state) (PFS.to_list (ss_pfs unfolded_symb_state));
	Some unfolded_symb_state ) with UnificationFailure _ -> None 

let grab_resources 
		(predicates           : (string, Symbolic_State.n_jsil_logic_predicate) Hashtbl.t)
		(spec_vars            : SS.t)
		(pat_unification_plan : unification_plan) 
		(pat_subst            : substitution)
		(pat_symb_state       : symbolic_state) 
		(symb_state           : symbolic_state) : symbolic_state option   =
	
	print_debug (Printf.sprintf "grab_resources.\nSymb_state:\n%s.\nAssert symb_state:\n%s"
		(Symbolic_State_Print.string_of_symb_state symb_state)
		(Symbolic_State_Print.string_of_symb_state pat_symb_state));
	
	try (
		let res = unify_symb_states predicates SS.empty spec_vars pat_unification_plan (Some pat_subst) pat_symb_state symb_state in
		match res with
		| Some (true, (heap_f, preds_f, subst, pf_discharges, _)) ->
			ss_extend_pfs symb_state (PFS.of_list pf_discharges);
			let symb_state = ss_replace_heap symb_state heap_f in
			let symb_state = ss_replace_preds symb_state preds_f in
			let new_symb_state = Symbolic_State_Utils.merge_symb_states symb_state pat_symb_state subst in
			let subst_pfs = assertions_of_substitution subst in
			ss_extend_pfs symb_state (PFS.of_list subst_pfs);
			let symb_state = Simplifications.simplify_ss symb_state (Some (Some spec_vars)) in
			Some symb_state
		| _ -> None
	) with UnificationFailure _ -> None 