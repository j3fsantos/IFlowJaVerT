(** JSIL Symbolic Store *)

open CCommon
open SCommon
open JSIL_Syntax
open JSIL_Logic_Utils

type t = (string, jsil_logic_expr) Hashtbl.t

let str (x : t) : string =
	Hashtbl.fold
		(fun var le ac ->
			 let le_str = JSIL_Print.string_of_logic_expression le in
			 let var_le_str = "(" ^ var ^ ": " ^ le_str ^ ")" in
			 let space = if ac = "\t" then "" else "\n\t" in
			 	ac ^ space ^ var_le_str)
		x "\t"

(**************************************)
(** Symbolic store functions         **)
(**************************************)

(** Returns a new symbolic store where the variables in vars are 
    mapped to the logical expressions in --les--. 
    When |les| > |vars|, the additional les are ignored. 
    When |les| < |vars|, the vars for which we do not have le are
    set to undefined *)  
let init (vars : string list) (les : jsil_logic_expr list) : t =
	let store = Hashtbl.create big_tbl_size in
	let rec loop vars les =
		match vars, les with
		| [], _ -> ()
		| var :: rest_vars, le :: rest_les -> Hashtbl.replace store var le; loop rest_vars rest_les
		| var :: rest_vars, [] -> Hashtbl.replace store var (LLit Undefined); loop rest_vars [] in
	loop vars les;
	store

(** Returns Some store(x) if defined and None otherwise *)
let get (store : t) (x : string) : jsil_logic_expr option =
	Hashtbl.find_opt store x

(** Returns Some store(x) if defined and throws an error otherwise *)
let get_unsafe (store : t) (x : string) : jsil_logic_expr =
	match (Hashtbl.find_opt store x) with 
	| Some result -> result
	| None -> raise (Failure (Printf.sprintf "SStore.get_unsafe: variable %s not found in store" x))

(** Updates store(x) with --le-- *)
let put (store : t) (x : string) (le : jsil_logic_expr) : unit =
	Hashtbl.replace store x le

(** Checks if --x-- is in the --store-- *)
let mem (store : t) (x : string) : bool =
	Hashtbl.mem store x

(** Removes the binding of --x-- from --store-- *)
let remove (store : t) (x : string) : unit =
	Hashtbl.remove store x

(** Removes the domian of --store-- *)
let domain (store : t) : SS.t =
	SS.of_list (Hashtbl.fold (fun x _ ac -> x :: ac) store [])

(** Returns a copy of --store-- *)
let copy (store : t) : t = Hashtbl.copy store 

(** Returns subst(store) *)
let substitution (subst : substitution) (partial : bool) (store : t) : t =
	let new_store = init [] [] in
		Hashtbl.iter (fun x le -> 
			let le_subst = lexpr_substitution subst partial le in
			let le_subst = if (le <> le_subst) then Reduction.reduce_lexpr le_subst else le_subst in
			Hashtbl.replace new_store x le_subst) store;
		new_store

(** Updates --store-- to subst(store) *)
let substitution_in_place (subst : substitution) (store : t) : unit =
	Hashtbl.iter (fun x le ->
		let s_le = lexpr_substitution subst true le in
		let s_le = if (le <> s_le) then Reduction.reduce_lexpr s_le else s_le in
		Hashtbl.replace store x s_le)
	store

(** Returns the set containing all the vars occurring in --store-- *)
let vars (store : t) : SS.t =
	Hashtbl.fold (fun x le ac -> 
		SS.union ac (SS.add x (get_lexpr_vars le))) store SS.empty

(** Returns the set containing all the lvars occurring in --store-- *)
let lvars (store : t) : SS.t =
	Hashtbl.fold (fun _ le ac -> SS.union ac (get_lexpr_lvars le)) store SS.empty

(** Returns the set containing all the alocs occurring in --store-- *)
let alocs (store : t) : SS.t =
	Hashtbl.fold (fun _ le ac -> SS.union ac (get_lexpr_alocs le)) store SS.empty

(** Partitions the variables in the domain of --store-- into two groups: 
    - the group containing the variables mapped onto lexprs satisfying --pred--
    - the rest *)
let partition (store : t) (pred_fun : jsil_logic_expr -> bool) : (string list) * (string list) =
	Hashtbl.fold (fun x le (pred_xs, npred_xs) ->
		if (pred_fun le) then ((x :: pred_xs), npred_xs) else (pred_xs, (x :: npred_xs)))
	store ([], [])

(** Returns the projection of --store-- onto --xs-- *)
let projection (store : t) (xs : string list) : t =
	let new_store = init [] [] in
		List.iter (fun x ->
			if (Hashtbl.mem store x) then Hashtbl.replace new_store x (get_unsafe store x)
		) xs;
		new_store

(** Calls --f-- on all variables of --store--; f(x, le_x) *)
let iter (store: t) (f : string -> jsil_logic_expr -> unit) : unit =
	Hashtbl.iter f store

let fold (store: t) (f : string -> jsil_logic_expr -> 'a  -> 'a) (init : 'a) : 'a =
	Hashtbl.fold f store init 

(** conversts a symbolic store to a list of assertions *)
let assertions (s : t) : jsil_logic_assertion list= 
	Hashtbl.fold
		(fun x le assertions -> 
			(LEq (PVar x, le)) :: assertions) s []
