open CCommon
open JSIL_Syntax
open JSIL_Print

type t = 	
	{
		fvl           : SFVL.t;                 (*  mutable  *)
		domain        : jsil_logic_expr option; (* immutable *)
		metadata      : jsil_logic_expr option; (* immutable *)
		extensibility : Extensibility.t option  (* immutable *)
	}

(*************************************)
(** Constants, Getters, Setters     **)
(*************************************)

let empty_object () : t = 
	{ fvl = SFVL.empty (); domain = None; metadata = None; extensibility = None }

let can_be_considered_empty (sobj : t) : bool =
	(sobj.fvl = SFVL.empty()) && (sobj.domain = None) && (sobj.extensibility = None)

let get_fvl (sobj : t) : SFVL.t = sobj.fvl
let get_dom (sobj : t) : jsil_logic_expr option = sobj.domain
let get_met (sobj : t) : jsil_logic_expr option = sobj.metadata
let get_ext (sobj : t) : Extensibility.t option = sobj.extensibility

let set_fvl (sobj : t) fvl : t = { sobj with fvl = fvl }
let set_dom (sobj : t) dom : t = { sobj with domain = dom }
let set_met (sobj : t) met : t = { sobj with metadata = met }
let set_ext (sobj : t) ext : t = { sobj with extensibility = ext }

(*************************************)
(** Symbolic object functions       **)
(*************************************)

let copy (sobj : t) : t = 
	{ sobj with fvl = SFVL.copy sobj.fvl }

let merge_left (sobj_l : t) (sobj_r : t) : t = 

	let _ = SFVL.merge_left sobj_l.fvl sobj_r.fvl in

	let m_dom = 
		(match sobj_l.domain, sobj_r.domain with 
		| None, None -> None
		| None, Some domain 
		| Some domain, None -> Some domain 
		| Some set1, Some set2 -> Some (LSetUnion [ set1; set2 ])) in
			
	let m_met = 
		(match sobj_l.metadata, sobj_r.metadata with
		| None, None -> None
		| None, Some domain 
		| Some domain, None -> Some domain 
		| Some md, _ -> Some md) in

	let m_ext = Extensibility.merge sobj_l.extensibility sobj_r.extensibility in

	{
		fvl           = sobj_l.fvl;
		domain        = m_dom;
		metadata      = m_met;
		extensibility = m_ext
	}

let set_fv_pair (sobj : t) (name : SFVL.field_name) (value : SFVL. field_value) =
	SFVL.set sobj.fvl name value

let remove_field (sobj : t) (name : SFVL.field_name) =
	SFVL.remove sobj.fvl name

let str (sobj : t) = 
	let str_fv_pairs = SFVL.str sobj.fvl in
	let domain_str = Option.map_default JSIL_Print.string_of_logic_expression "" sobj.domain in
	let meta_str = Option.map_default string_of_logic_expression "unknown" sobj.metadata in
	let ext_str = Extensibility.ostr sobj.extensibility in
	let symb_obj_str = "[" ^  str_fv_pairs ^ " | " ^ domain_str ^ "] " ^ ext_str ^ " with metadata " ^ meta_str in
		symb_obj_str

let substitution ?(partial : bool option) (subst : substitution) (sobj : t) : t =
	let is_partial = Option.default true partial in
	let le_subst = JSIL_Logic_Utils.lexpr_substitution subst is_partial in
	let _ = SFVL.substitution ?partial:partial subst sobj.fvl in
	{
		fvl           = sobj.fvl;
		domain        = Option.map le_subst sobj.domain;
		metadata      = Option.map le_subst sobj.metadata;
		extensibility = sobj.extensibility
	}

let get_lvars (sobj : t) : SS.t = 
	let gllv = JSIL_Logic_Utils.get_lexpr_lvars in
	let v_fvl = SFVL.get_lvars sobj.fvl in
	let v_domain = Option.map_default gllv SS.empty sobj.domain in
	let v_metadata = Option.map_default gllv SS.empty sobj.metadata in
	SS.union v_fvl (SS.union v_domain v_metadata)

(** Returns the abstract locations occuring in --heap-- *)
let get_alocs (sobj : t) : SS.t =
	let gla = JSIL_Logic_Utils.get_lexpr_alocs in
	let a_fvl = SFVL.get_alocs sobj.fvl in
	let a_metadata = Option.map_default gla SS.empty sobj.metadata in
		SS.union a_fvl a_metadata

let assertions (loc : jsil_logic_expr) (sobj : t) : jsil_logic_assertion list = 
	let fvl = List.map (fun (field, (perm, value)) -> LPointsTo (loc, field, (perm, value))) (SFVL.to_list sobj.fvl) in 
	let domain = Option.map_default (fun domain -> [ LEmptyFields (loc, domain) ]) [] sobj.domain in
	let metadata = Option.map_default (fun metadata -> [ LMetaData (loc, metadata) ]) [] sobj.metadata in
	let extensibility = Option.map_default (fun ext -> [ LExtensible (loc, ext) ]) [] sobj.extensibility in
		fvl @ domain @ metadata @ extensibility