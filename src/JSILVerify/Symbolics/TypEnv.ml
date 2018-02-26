(** JSIL Typing Environment *)

open CCommon
open SCommon
open JSIL_Syntax

type t = 
	{
		gamma : (string, Type.t) Hashtbl.t;
		lvars : SS.t ref;
		vars  : SS.t ref
	}

let str (x : t) : string =
	let x = x.gamma in
	Hashtbl.fold
		(fun var var_type ac ->
			let var_type_pair_str = Printf.sprintf "(%s: %s)" var (Type.str var_type) in
			let new_line = if (ac = "") then "\t" else "\n\t" in
				ac ^ new_line ^ var_type_pair_str)
		x
		""

(*************************************)
(** Typing Environment Functions    **)
(*************************************)

(* Initialisation *)
let init () : t = { 
	gamma = Hashtbl.create medium_tbl_size; 
	lvars = ref SS.empty;
	vars  = ref SS.empty }

(* Copy *)
let copy (x : t) : t =
	{ 
		gamma = Hashtbl.copy x.gamma;
		lvars = ref !(x.lvars);
		vars  = ref !(x.vars)
	}

(* Type of a variable *)
let get (x : t) (var : string) : Type.t option =
	Hashtbl.find_opt x.gamma var

(* Membership *)
let mem (x : t) (v : string) : bool = 
	Hashtbl.mem x.gamma v

(* Type of a variable *)
let get_unsafe (x : t) (var : string) : Type.t =
	(match Hashtbl.mem x.gamma var with
	| true -> Hashtbl.find x.gamma var
	| false -> raise (Failure ("TypEnv.get_unsafe: variable " ^ var ^ " not found.")))

(* Get all variables *)
let vars (x : t) : SS.t = !(x.lvars)

(* Get all logical variables *)
let lvars (x : t) : SS.t = !(x.vars)

(* Get all variables of specific type *)
let get_vars_of_type (x : t) (tt : Type.t) : string list =
	Hashtbl.fold (fun var t ac_vars -> (if (t = tt) then var :: ac_vars else ac_vars)) x.gamma []

(* Get all var-type pairs as a list *)
let get_var_type_pairs (x : t) : (string * Type.t) list = Hashtbl.fold (fun var t ac_vars -> ((var, t) :: ac_vars)) x.gamma []

(* Iteration *)
let iter (x : t) (f : string -> Type.t -> unit) : unit = 
	Hashtbl.iter f x.gamma

let fold (x : t) (f : string -> Type.t -> 'a -> 'a) (init : 'a) : 'a = 
	Hashtbl.fold f x.gamma init

let update_vars_and_lvars (x : t) (v : string) : unit = 
	if (is_lvar_name v) then (x.lvars := SS.add v !(x.lvars)); x.vars := SS.add v !(x.vars)

(* Update with removal *)
let update (x : t) (v : string) (te : Type.t option) : unit =
	(match te with
	| None    -> Hashtbl.remove x.gamma v; x.lvars := SS.remove v !(x.lvars); x.vars := SS.remove v !(x.vars)
	| Some te -> Hashtbl.replace x.gamma v te; update_vars_and_lvars x v)

(* Update without removal *)
let weak_update (x : t) (v : string) (te : Type.t option) : unit =
	(match te with
	| None -> ()
	| Some te -> Hashtbl.replace x.gamma v te; update_vars_and_lvars x v)

(* Extend gamma with more_gamma *)
let extend (x : t) (y : t) : unit =
	iter y
		(fun v t ->
			match (Hashtbl.find_opt x.gamma v) with
			| None    -> Hashtbl.replace x.gamma v t; update_vars_and_lvars x v
			| Some t' -> if (t <> t') then raise (Failure "Typing environment cannot be extended.")
		)

(* Filter using function on variables *)
let filter (x : t) (f : string -> bool) : t =
	let new_gamma = init () in
	iter x (fun v v_type -> (if (f v) then update new_gamma v (Some v_type)));
	new_gamma

(* Filter using function on variables *)
let filter_in_place (x : t) (f : string -> bool) : unit =
	iter x (fun v v_type -> (if (not (f v)) then update x v None))

(* Filter for specific variables *)
let filter_vars (gamma : t) (vars : SS.t) : t = filter gamma (fun v -> SS.mem v vars)

(* Filter for specific variables *)
let filter_vars_in_place (gamma : t) (vars : SS.t) : unit = filter_in_place gamma (fun v -> SS.mem v vars)

(* Perform substitution, return new typing environment *)
let rec substitution (x : t) (subst : substitution) (partial : bool) : t =
	let new_gamma = init () in
	iter x
		(fun var v_type ->
			let new_var = Hashtbl.find_opt subst var in
			(match new_var with
			| Some (LVar new_var) -> update new_gamma new_var (Some v_type)
			| Some _ -> if partial then update new_gamma var (Some v_type)
			| None   -> if partial then update new_gamma var (Some v_type)
		                else 
						if (is_lvar_name var) then (
							let new_lvar = fresh_lvar () in
							Hashtbl.add subst var (LVar new_lvar);
							update new_gamma new_lvar (Some v_type)
						)));
	new_gamma

(* Convert to assertion *)
let assertions (x : t) : jsil_logic_assertion = 
	let le_type_pairs = 
		Hashtbl.fold
			(fun x t pairs -> 
				(if (is_lvar_name x) 
					then (LVar x, t) :: pairs
					else (PVar x, t) :: pairs)) x.gamma [] in 
	LTypes le_type_pairs 

let is_well_formed (x : t) : bool =
	let lvars, vars = Hashtbl.fold (fun v _ (lvars, vars) -> 
		if (is_lvar_name v) 
			then (SS.add v lvars, SS.add v vars)
			else (lvars, SS.add v vars)) x.gamma (SS.empty, SS.empty) in
		(SS.equal lvars !(x.lvars)) && (SS.equal vars !(x.vars)) 