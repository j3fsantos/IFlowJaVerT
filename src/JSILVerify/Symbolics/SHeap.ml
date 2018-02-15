(** JSIL Symbolic Heap *)

open CCommon
open SCommon
open JSIL_Syntax
open JSIL_Print

type t =
	((SFVL.t * (jsil_logic_expr option)) * jsil_logic_expr option * Extensibility.t option) Heap.t
	
let str (heap : t) = 
  Heap.fold
  (fun loc ((fv_pairs, domain), metadata, ext) ac ->
  	let str_fv_pairs = SFVL.str fv_pairs in
  	let domain_str = Option.map_default JSIL_Print.string_of_logic_expression "" domain in
  	let meta_str = Option.map_default string_of_logic_expression "unknown" metadata in
  	let ext_str = Extensibility.ostr ext in
  	let symb_obj_str = loc ^ " |-> [" ^  str_fv_pairs ^ " | " ^ domain_str ^ "] " ^ ext_str ^ " with metadata " ^ meta_str in
  	if (ac = "\n\t") then (ac ^ symb_obj_str) else ac ^ "\n\t" ^ symb_obj_str)
  heap
  "\n\t"
	
(*************************************)
(** Symbolic heap functions         **)
(*************************************)

(** Returns an empty symbolic heap *)
let init () : t =
	Heap.create big_tbl_size

(** Symbolic heap read heap(loc) *)
let get (heap : t) (loc : string) =
	Heap.find_opt heap loc

let get_unsafe (heap : t) (loc : string) =
	match (Heap.find_opt heap loc) with 
	| Some result -> result
	| None -> raise (Failure (Printf.sprintf "SHeap.heap_get_unsafe: object %s does not exist" loc))

(** Symbolic heap put heap(loc) is assigned to fv_list *)
let put (heap : t) (loc : string) (fv_list : SFVL.t) (dom : jsil_logic_expr option) (metadata : jsil_logic_expr option) (ext : Extensibility.t option) =
	Heap.replace heap loc ((fv_list, dom), metadata, ext)

(** Symbolic heap put heap (loc, (perm, field)) is assigned to value.
    The domain remains unchanged. 
		TODO: FIX - duplicate fields? *) 
let put_fv_pair_simple (heap : t) (loc : string) (perm : Permission.t) (field : jsil_logic_expr) (value : jsil_logic_expr) =
	let ((fv_list, domain), metadata, ext) = try Heap.find heap loc with _ -> ((SFVL.empty, None), None, None) in
	Heap.replace heap loc ((SFVL.add field (perm, value) fv_list, domain), metadata, ext)

let has_loc (heap : t) (loc : string) : bool = 
	Heap.mem heap loc 

(** Removes the fv-list associated with --loc-- in --heap-- *)
let remove (heap : t) (loc : string) =
	Heap.remove heap loc

(** Removes the domain of --heap-- *)
let domain (heap : t) : SS.t =
	SS.of_list (Heap.fold (fun l _ ac -> l :: ac) heap [])

(** Returns a copy of --heap-- *)
let copy (heap : t) : t = 
	let new_heap = init () in
	Heap.iter (fun loc ((fvl, domain), metadata, ext) -> Heap.add new_heap loc ((SFVL.copy fvl, domain), metadata, ext)) heap;
		new_heap

(** Returns subst(heap) *)
let substitution (subst : substitution) (partial : bool) (heap : t) : t =
	let new_heap = Heap.create 1021 in
	Heap.iter
		(fun loc ((fv_list, domain), metadata, ext) ->
			let s_loc = if (is_lloc_name loc) then LLit (Loc loc) else (
				try (Hashtbl.find subst loc) with
				| _ -> 
						if (partial) then (ALoc loc) else (
							let new_aloc = ALoc (fresh_aloc ()) in
							extend_substitution subst [ loc ] [ new_aloc ];
							new_aloc)) in
			let s_loc = match s_loc with LLit (Loc loc) -> loc | ALoc loc -> loc 
				| _ -> raise (Failure (Printf.sprintf "Heap substitution fail for loc: %s" (JSIL_Print.string_of_logic_expression s_loc))) in
			let s_fv_list = SFVL.substitution subst partial fv_list in
			let s_domain = Option.map (JSIL_Logic_Utils.lexpr_substitution subst partial) domain in
			let s_metadata = Option.map (JSIL_Logic_Utils.lexpr_substitution subst partial) metadata in
			Heap.add new_heap s_loc ((s_fv_list, s_domain), s_metadata, ext))			
		heap;
	new_heap

(** Modifies --heap-- in place updating it to subst(heap) *)
let substitution_in_place (subst : substitution) (heap : t) : unit =
	let le_subst = JSIL_Logic_Utils.lexpr_substitution subst true in 
  Heap.iter
		(* For every location in the existing heap *)
  	(fun loc ((fv_list, domain), metadata, ext) ->
			(* Understand the corresponding new location *)
  		let s_loc = 
				if (is_lloc_name loc) 
					then LLit (Loc loc) 
					else (try Hashtbl.find subst loc with _ -> ALoc loc) in 
  		let s_loc = match s_loc with LLit (Loc loc) -> loc | ALoc loc -> loc 
				| _ -> raise (Failure (Printf.sprintf "Heap substitution fail for loc: %s" (JSIL_Print.string_of_logic_expression s_loc))) in 	
				
			(* Perform the substitution in the field-value list *)
  		let s_fv_list = SFVL.substitution subst true fv_list in
			(* Perform the substitution in the domain *)
  		let s_domain = Option.map (fun le -> le_subst le) domain in
			let s_metadata = Option.map le_subst metadata in
			
			(* Remove original location from heap *)
			Heap.remove heap loc;
			
			(* Check if new location is already in the heap *)
			(match (Heap.find_opt heap s_loc) with
			(* It doesn't, simple put *)
			| None -> 
					Heap.replace heap s_loc ((s_fv_list, s_domain), s_metadata, ext)
			(* It does, needs merge *)
			(* Get the data associated with the location *)
			| Some ((nfvl, ndom), nmet, next) ->
					let s_nfvl = SFVL.substitution subst true nfvl in
					let s_metadata = (match s_metadata, nmet with
					  | None, None -> None
            | None, Some domain 
            | Some domain, None -> Some domain 
            | Some m1, Some m2 -> Some m1) in 
					let s_ext = Extensibility.merge ext next in
					(* Perform the substitution in the domain *)
					let s_ndom = Option.map (fun le -> le_subst le) ndom in
					(* Merge the domains (without simplification) *)
					let new_domain = 	match s_domain, s_ndom with 
            	| None, None -> None
            	| None, Some domain 
            	| Some domain, None -> Some domain 
            	| Some set1, Some set2 -> 
            			Some (LSetUnion [ set1; set2 ]) in
											
					(* Perform the replacement *)
					Heap.replace heap s_loc ((SFVL.union s_fv_list s_nfvl, new_domain), s_metadata, s_ext)))
  	heap

(** Returns the logical variables occuring in --heap-- *)
let lvars (heap : t) : SS.t =
	let gllv = JSIL_Logic_Utils.get_lexpr_lvars in
	Heap.fold
		(fun _ ((fv_list, domain), e_metadata, _) ac ->
			let v_fv = SFVL.lvars fv_list in 
			let v_domain = Option.map_default (fun domain -> gllv domain) SS.empty domain in
			let v_metadata = Option.map_default gllv SS.empty e_metadata in
			SS.union ac (SS.union v_fv (SS.union v_domain v_metadata)))
		heap SS.empty

(** Returns the abstract locations occuring in --heap-- *)
let alocs (heap : t) : SS.t =
	let gla = JSIL_Logic_Utils.get_lexpr_alocs in
	Heap.fold
		(fun _ ((fv_list, _), e_metadata, _) ac ->
			let v_fv = SFVL.alocs fv_list in
			let v_metadata = Option.map_default gla SS.empty e_metadata in
			SS.union ac (SS.union v_fv v_metadata))
		heap SS.empty

(** Returns the serialization of --heap-- as a list *)
let to_list (heap : t) : (string * ((SFVL.t * (jsil_logic_expr option)) * jsil_logic_expr option * Extensibility.t option)) list =
	Heap.fold (fun loc obj ac -> ((loc, obj) :: ac)) heap []

(** Calls --f-- on all objects of --heap--; f(loc, (fv_list, dom)) *)
let iterator (heap: t) (f : string -> (((SFVL.t * (jsil_logic_expr option)) * jsil_logic_expr option * Extensibility.t option) -> unit)) =
	Heap.iter f heap

(** Returns true if --heap-- is empty : TODO *)
let is_empty (heap : t) : bool =
	Heap.fold (fun loc ((fv_list, dom), metadata, _) ac -> if (not ac) then ac else (SFVL.is_empty fv_list) && (dom = None)) heap true

(** converts a symbolic heap to a list of assertions *)
let assertions (heap : t) : jsil_logic_assertion list = 
	let make_loc_lexpr loc = 
		if (is_aloc_name loc) then ALoc loc else LLit (Loc loc) in 
	
	(* TODO : Deal with metadata and extensibility *)
	let rec assertions_of_object (loc, ((fv_list, domain), metadata, ext)) =
	 	let le_loc = make_loc_lexpr loc in
		let fv_assertions = SFVL.assertions le_loc fv_list in 
		let domain = Option.map_default (fun domain -> [ LEmptyFields (le_loc, domain) ]) [] domain in
		let metadata = match metadata with | Some metadata -> [ LMetaData (le_loc, metadata) ] | None -> [ ] in
		let ext = match ext with | Some ext -> [ LExtensible (le_loc, ext) ] | None -> [ ] in 
			fv_assertions @ domain @ metadata @ ext 
		in
		
	List.concat (List.map assertions_of_object (to_list heap))

let is_well_formed (heap : t) : bool =
	Heap.fold (fun loc ((fv_list, _), _, _) ac -> if (ac = false) then false 
		else (
			(* print_debug_petar ("\tLocation: " ^ loc); *)
			SFVL.is_well_formed fv_list
		)) heap true
