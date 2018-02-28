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

(** Updates store(x) with --le-- *)
let put (x : t) (v : string) (le : jsil_logic_expr) : unit =
	Hashtbl.replace x v le

(** Returns Some store(x) if defined and None otherwise *)
let get (x : t) (v : string) : jsil_logic_expr option =
	Hashtbl.find_opt x v

(** Returns Some store(x) if defined and throws an error otherwise *)
let get_unsafe (x : t) (v : string) : jsil_logic_expr =
	match (Hashtbl.find_opt x v) with 
	| Some result -> result
	| None -> raise (Failure (Printf.sprintf "SStore.get_unsafe: variable %s not found in store" v))

(** Checks if --x-- is in the --store-- *)
let mem (x : t) (v : string) : bool =
	Hashtbl.mem x v

(** Calls --f-- on all variables of --store--; f(x, le_x) *)
let iter (x : t) (f : string -> jsil_logic_expr -> unit) : unit =
	Hashtbl.iter f x

let fold (x : t) (f : string -> jsil_logic_expr -> 'a  -> 'a) (init : 'a) : 'a =
	Hashtbl.fold f x init 

(** Returns a new symbolic store where the variables in vars are 
    mapped to the logical expressions in --les--. 
    When |les| > |vars|, the additional les are ignored. 
    When |les| < |vars|, the vars for which we do not have le are
    set to undefined *)  
let init (vars : string list) (les : jsil_logic_expr list) : t =
	let x = Hashtbl.create big_tbl_size in 
	let rec loop vars les =
		(match vars, les with
		| [], _ -> ()
		| var :: rest_vars, le :: rest_les -> 
			put x var le; loop rest_vars rest_les
		| var :: rest_vars, [] -> 
			put x var (LLit Undefined);
			loop rest_vars []) in
	loop vars les;
	x

(** Removes the binding of --x-- from --store-- *)
let remove (x : t) (v : string) : unit =
	(match mem x v with
	| false -> ();
	| true -> Hashtbl.remove x v)

(** Removes the domian of --store-- *)
let domain (x : t) : SS.t =
	SS.of_list (fold x (fun x _ ac -> x :: ac) [])

(** Returns a copy of --store-- *)
let copy (x : t) : t = Hashtbl.copy x

(** Returns subst(store) *)
let substitution (subst : substitution) (partial : bool) (x : t) : t =
	
	(* Do not substitute spec vars for spec vars *)
	let store_subst = copy_substitution subst in 
	Hashtbl.filter_map_inplace (fun v le -> 
		match (is_spec_var_name v), le with 
		| false, _ -> Some le
		| true, LVar w -> Some (LVar v)
		| _, _ -> Some le) store_subst;

	let new_store = init [] [] in
		iter x (fun v le -> 
			let le_subst = lexpr_substitution store_subst partial le in
			let le_subst = if (le <> le_subst) then Reduction.reduce_lexpr le_subst else le_subst in
			put new_store v le_subst);
		new_store

(** Updates --store-- to subst(store) *)
let substitution_in_place (subst : substitution) (x : t) : unit =

	(* Do not substitute spec vars for spec vars *)
	let store_subst = copy_substitution subst in 
	Hashtbl.filter_map_inplace (fun v le -> 
		match (is_spec_var_name v), le with 
		| false, _ -> Some le
		| true, LVar w -> Some (LVar v)
		| _, _ -> Some le) store_subst;
	
	iter x (fun v le ->
		let s_le = lexpr_substitution store_subst true le in
		let s_le = if (le <> s_le) then Reduction.reduce_lexpr s_le else s_le in
		if (le <> s_le) then put x v s_le)

(** Returns the set containing all the vars occurring in --x-- *)
let vars (x : t) : SS.t =
	fold x (fun x le ac -> 
		SS.union ac (SS.add x (get_lexpr_vars le))) SS.empty

(** Returns the set containing all the lvars occurring in --x-- *)
let lvars (x : t) : SS.t =
	fold x (fun _ le ac -> SS.union ac (get_lexpr_lvars le)) SS.empty

(** Returns the set containing all the alocs occurring in --x-- *)
let alocs (x : t) : SS.t =
	fold x (fun _ le ac -> SS.union ac (get_lexpr_alocs le)) SS.empty

(** Returns the set containing all the alocs occurring in --x-- *)
let clocs (x : t) : SS.t =
	fold x (fun _ le ac -> SS.union ac (get_lexpr_clocs le)) SS.empty

let unifiables (x : t) : SS.t = 
	let lv, pv, ll, al = fold x (fun v le (lv1, pv1, ll1, al1) -> 
		let lv2, _, ll2, al2 = get_lexpr_unifiables le in 
		(MS.union lv1 lv2, MS.add pv1 v, MS.union ll1 ll2, MS.union al1 al2)
	) (MS.empty, MS.empty, MS.empty, MS.empty) in
	SS.of_list (MS.to_list (List.fold_left MS.union MS.empty [lv; pv; ll; al]))

(** Partitions the variables in the domain of --store-- into two groups: 
    - the group containing the variables mapped onto lexprs satisfying --pred--
    - the rest *)
let partition (x : t) (pred_fun : jsil_logic_expr -> bool) : (string list) * (string list) =
	fold x (fun x le (pred_xs, npred_xs) ->
		if (pred_fun le) then ((x :: pred_xs), npred_xs) else (pred_xs, (x :: npred_xs)))
	([], [])

(** Returns the projection of --store-- onto --xs-- *)
let projection (x : t) (xs : string list) : t =
	let y = init [] [] in
		List.iter (fun v ->
			if (mem x v) then put y v (get_unsafe x v)
		) xs;
		y

(** conversts a symbolic store to a list of assertions *)
let assertions (x : t) : jsil_logic_assertion list =
	fold x (fun x le assertions -> (LEq (PVar x, le)) :: assertions) []

let is_well_formed (x : t) : bool = true