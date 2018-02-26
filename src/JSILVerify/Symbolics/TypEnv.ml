(** JSIL Typing Environment *)

open CCommon
open SCommon
open JSIL_Syntax

type t = (string, Type.t) Hashtbl.t

let str (x : t) : string =
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
let init () : t = Hashtbl.create medium_tbl_size

(* Copy *)
let copy (gamma : t) : t =
	Hashtbl.copy gamma

(* Type of a variable *)
let get (gamma : t) (var : string) : Type.t option =
	Hashtbl.find_opt gamma var

(* Membership *)
let mem (gamma : t) (x : string) : bool = 
	Hashtbl.mem gamma x

(* Type of a variable *)
let get_unsafe (gamma : t) (var : string) : Type.t =
	(match Hashtbl.mem gamma var with
	| true -> Hashtbl.find gamma var
	| false -> raise (Failure ("TypEnv.get_unsafe: variable " ^ var ^ " not found.")))

(* Get all variables *)
let vars (gamma : t) : SS.t =
	Hashtbl.fold (fun var _ ac -> SS.add var ac) gamma SS.empty

(* Get all logical variables *)
let lvars (gamma : t) : SS.t =
	Hashtbl.fold (fun var _ ac -> if is_lvar_name var then SS.add var ac else ac) gamma SS.empty

(* Get all variables of specific type *)
let get_vars_of_type (gamma : t) (tt : Type.t) : string list =
	Hashtbl.fold (fun var t ac_vars -> (if (t = tt) then var :: ac_vars else ac_vars)) gamma []

(* Get all var-type pairs as a list *)
let get_var_type_pairs (gamma : t) : (string * Type.t) list = Hashtbl.fold (fun var t ac_vars -> ((var, t) :: ac_vars)) gamma []

(* Update with removal *)
let update (gamma : t) (x : string) (te : Type.t option) : unit =
	(match te with
	| None    -> Hashtbl.remove  gamma x
	| Some te -> Hashtbl.replace gamma x te)

(* Update without removal *)
let weak_update (gamma : t) (x : string) (te : Type.t option) : unit =
	(match te with
	| None -> ()
	| Some te -> Hashtbl.replace gamma x te)

(* Extend gamma with more_gamma *)
let extend (gamma : t) (more_gamma : t) : unit =
	Hashtbl.iter
		(fun v t ->
			match (Hashtbl.find_opt gamma v) with
			| None    -> Hashtbl.add gamma v t
			| Some t' -> if (t <> t') then raise (Failure "Typing environment cannot be extended.")
		)
		more_gamma

let safe_extend (gamma_l : t) (gamma_r : t) : unit =
	Hashtbl.iter
		(fun var v_type ->
			(match (Hashtbl.mem gamma_l var) with
			| false -> 
					print_debug_petar (Printf.sprintf "Inferred type: %s : %s" var (Type.str v_type)); 
					update gamma_l var (Some v_type)
			| true -> let t = Hashtbl.find gamma_l var in
					(match (t = v_type) with
					| true -> ()
					| false -> raise (Failure (Printf.sprintf "Incompatible gamma merge: Variable %s: tried %s but %s" var (Type.str v_type) (Type.str t))); 
					)
			)
		)
		gamma_r

(* Iteration *)
let iter (gamma : t) (f : string -> Type.t -> unit) : unit = 
	Hashtbl.iter f gamma

let fold (gamma : t) (f : string -> Type.t -> 'a -> 'a) (init : 'a) : 'a = 
	Hashtbl.fold f gamma init

(* Filter using function on variables *)
let filter (gamma : t) (f : string -> bool) : t =
	let new_gamma = init () in
	Hashtbl.iter (fun v v_type -> (if (f v) then Hashtbl.replace new_gamma v v_type)) gamma;
	new_gamma

(* Filter using function on variables *)
let filter_in_place (gamma : t) (f : string -> bool) : unit =
	Hashtbl.iter (fun v v_type -> (if (not (f v)) then Hashtbl.remove gamma v)) gamma

(* Filter for specific variables *)
let filter_vars (gamma : t) (vars : SS.t) : t = filter gamma (fun v -> SS.mem v vars)

(* Filter for specific variables *)
let filter_vars_in_place (gamma : t) (vars : SS.t) : unit = filter_in_place gamma (fun v -> SS.mem v vars)

(* Perform substitution, return new typing environment *)
let rec substitution (gamma : t) (subst : substitution) (partial : bool) : t =
	let new_gamma = init () in
	Hashtbl.iter
		(fun var v_type ->
			let new_var = Hashtbl.find_opt subst var in
			(match new_var with
			| Some (LVar new_var) -> Hashtbl.replace new_gamma new_var v_type
			| Some _ -> if partial then Hashtbl.add new_gamma var v_type
			| None   -> if partial then Hashtbl.add new_gamma var v_type
		                else 
						if (is_lvar_name var) then (
							let new_lvar = fresh_lvar () in
							Hashtbl.add subst var (LVar new_lvar);
							Hashtbl.add new_gamma new_lvar v_type
						)))
		gamma;
	new_gamma

(* Convert to assertion *)
let assertions (gamma : t) : jsil_logic_assertion = 
	let le_type_pairs = 
		Hashtbl.fold
			(fun x t pairs -> 
				(if (is_lvar_name x) 
					then (LVar x, t) :: pairs
					else (PVar x, t) :: pairs)) gamma [] in 
	LTypes le_type_pairs 