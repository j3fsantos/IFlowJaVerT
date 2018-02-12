(** JSIL Symbolic Heap *)

open CCommon
open SCommon
open JSIL_Syntax
open JSIL_Print

type t = SObject.t Heap.t

	
let str (heap : t) = 
  Heap.fold
  (fun loc sobj ac ->
  	let str_sobj = SObject.str sobj in
  	let str_sobj = loc ^ " |-> " ^  str_sobj in 
  	if (ac = "\n\t") then (ac ^ str_sobj) else ac ^ "\n\t" ^ str_sobj)
  heap
  "\n\t"

(*************************************)
(** Symbolic heap functions         **)
(*************************************)

(** Returns an empty symbolic heap *)
let init () : t =
	Heap.create big_tbl_size

(** Symbolic heap read heap(loc) *)
let get (heap : t) (loc : string) : SObject.t option =
	Heap.find_opt heap loc

let get_unsafe (heap : t) (loc : string) =
	match (Heap.find_opt heap loc) with 
	| Some result -> result
	| None -> raise (Failure (Printf.sprintf "SHeap.heap_get_unsafe: object %s does not exist" loc))

(** Symbolic heap put heap(loc) is assigned to fv_list *)
let set_object (heap : t) (loc : string) (sobj : SObject.t) =
	Heap.replace heap loc sobj

(** Symbolic heap put heap (loc, (perm, field)) is assigned to value.
    The domain remains unchanged *) 
let set_fv_pair (heap : t) (loc : string) (name : SFVL.field_name) (value : SFVL.field_value) =
	let sobj : SObject.t = Option.default (SObject.empty_object()) (get heap loc) in
		SObject.set_fv_pair sobj name value

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
	let heap' = init () in
	Heap.iter (fun loc sobj -> 
		let sobj' = SObject.copy sobj in 
		Heap.replace heap' loc sobj' 
	) heap;
	heap'

(** Substitution - IN PLACE ALWAYS *)
let substitutionX ?(partial : bool option) (subst : substitution) (heap : t) : unit =
	let is_partial = Option.default true partial in
	print_debug_petar (Printf.sprintf "In substitutionX. My heap is: %s\nMy substitution is:%s" (str heap) (JSIL_Print.string_of_substitution subst));
	let locs_to_inspect = domain heap in
	List.iter
	(fun loc ->
		let sobj = get_unsafe heap loc in
		print_debug ("Checking location: " ^ loc);
		let s_loc = 
			(match is_lloc_name loc with
			| true -> LLit (Loc loc) 
			| false -> 
				(match Hashtbl.find_opt subst loc with
				| Some result -> 
					print_debug ("Location: " ^ loc ^ " found in the subst.");
					result
				| None -> 
					print_debug ("Location: " ^ loc ^ " not found in the subst.");
					(match is_partial with
					| true  -> ALoc loc 
					| false -> 
						let new_aloc = fresh_aloc () in
						print_debug ("We are not partial: new aloc: " ^ new_aloc);
						let new_aloc = ALoc new_aloc in
							
							extend_substitution subst [ loc ] [ new_aloc ];
							new_aloc
					)
				)
			) in
		let s_loc = (match s_loc with LLit (Loc loc) -> loc | ALoc loc -> loc) in
		let new_sobj = SObject.substitution ?partial:partial subst sobj in
		
		(* Remove original location from heap *)
		Heap.remove heap loc;
		
		(* Check if new location is already in the heap *)
		(match (Heap.find_opt heap s_loc) with
		(* It doesn't, simple put *)
		| None -> 
			Heap.replace heap s_loc new_sobj
		(* It does, needs merge *)
		(* Get the data associated with the location *)
		| Some old_sobj ->
			let old_sobj = SObject.substitution ?partial:partial subst old_sobj in
			let new_obj  = SObject.merge_left old_sobj new_sobj in 
			Heap.replace heap s_loc new_obj)
	)
  	(SS.elements locs_to_inspect);
  	print_debug_petar (Printf.sprintf "My resulting heap is: %s" (str heap))

(** Returns the logical variables occuring in --heap-- *)
let get_lvars (heap : t) : SS.t =
	Heap.fold (fun _ sobj ac -> SS.union ac (SObject.get_lvars sobj)) heap SS.empty

(** Returns the abstract locations occuring in --heap-- *)
let get_alocs (heap : t) : SS.t =
	Heap.fold (fun _ sobj ac -> SS.union ac (SObject.get_alocs sobj)) heap SS.empty

(** Returns the serialization of --heap-- as a list *)
let to_list (heap : t) : (string * SObject.t) list =
	Heap.fold (fun loc obj ac -> ((loc, obj) :: ac)) heap []

(** Calls --f-- on all objects of --heap--; f(loc, (fv_list, dom)) *)
let iterator (heap: t) (f : string -> SObject.t -> unit) =
	Heap.iter f heap

(** Returns true if --heap-- is empty : TODO *)
let is_empty (heap : t) : bool =
	Heap.fold (fun loc sobj ac -> if (not ac) then ac else (SObject.can_be_considered_empty sobj)) heap true

(** converts a symbolic heap to a list of assertions *)
let assertions (heap : t) : jsil_logic_assertion list = 
	
	let assertions_of_object (loc, sobj) =
	 	let le_loc = if (is_aloc_name loc) then ALoc loc else LLit (Loc loc) in
	 		SObject.assertions le_loc sobj in

	List.concat (List.map assertions_of_object (to_list heap))