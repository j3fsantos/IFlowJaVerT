(** JSIL Symbolic Store *)

open CCommon
open SCommon
open JSIL_Syntax
open JSIL_Logic_Utils

type t = 
	{	
		store : (string, jsil_logic_expr) Hashtbl.t;
		lvars : MS.t ref;
		pvars : MS.t ref;
		llocs : MS.t ref;
		alocs : MS.t ref
	}

let str (x : t) : string =
	let x = x.store in 
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
	print_debug (Printf.sprintf "Store put: %s -> %s" v (JSIL_Print.string_of_logic_expression le));
	let lv1, _, ll1, al1 = (match Hashtbl.find_opt x.store v with 
		| None        -> print_debug "\tNot found in store."; MS.empty, MS.empty, MS.empty, MS.empty
		| Some old_le -> print_debug "\tFound in store."; get_lexpr_unifiables old_le) in
	let lv2, _, ll2, al2 = get_lexpr_unifiables le in
		print_debug_petar (Printf.sprintf "New variables: %s" (String.concat ", " (MS.to_list lv2)));
		x.lvars := MS.union (MS.diff !(x.lvars) lv1) lv2;
		x.pvars := MS.add !(x.pvars) v;
		x.llocs := MS.union (MS.diff !(x.llocs) ll1) ll2;
		x.alocs := MS.union (MS.diff !(x.alocs) al1) al2;
		Hashtbl.replace x.store v le

(** Returns a new symbolic store where the variables in vars are 
    mapped to the logical expressions in --les--. 
    When |les| > |vars|, the additional les are ignored. 
    When |les| < |vars|, the vars for which we do not have le are
    set to undefined *)  
let init (vars : string list) (les : jsil_logic_expr list) : t =
	let x = { 
		store = Hashtbl.create big_tbl_size;
		lvars = ref MS.empty;
		pvars = ref MS.empty;
		llocs = ref MS.empty;
		alocs = ref MS.empty } in 
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

(** Returns Some store(x) if defined and None otherwise *)
let get (x : t) (v : string) : jsil_logic_expr option =
	Hashtbl.find_opt x.store v

(** Returns Some store(x) if defined and throws an error otherwise *)
let get_unsafe (x : t) (v : string) : jsil_logic_expr =
	match (Hashtbl.find_opt x.store v) with 
	| Some result -> result
	| None -> raise (Failure (Printf.sprintf "SStore.get_unsafe: variable %s not found in store" v))

(** Checks if --x-- is in the --store-- *)
let mem (x : t) (v : string) : bool =
	Hashtbl.mem x.store v

(** Removes the binding of --x-- from --store-- *)
let remove (x : t) (v : string) : unit =
	(match Hashtbl.mem x.store v with
	| false -> ();
	| true -> let le = Hashtbl.find x.store v in
		let lv, _, ll, al =  get_lexpr_unifiables le in 
			Hashtbl.remove x.store v; 
			x.lvars := MS.diff !(x.lvars) lv;
			x.llocs := MS.diff !(x.llocs) ll;
			x.alocs := MS.diff !(x.alocs) al)

(** Removes the domian of --store-- *)
let domain (x : t) : SS.t =
	SS.of_list (MS.to_list !(x.pvars))

(** Returns a copy of --store-- *)
let copy (x : t) : t = 
	{
		store = Hashtbl.copy x.store;
		lvars = ref !(x.lvars);
		pvars = ref !(x.pvars);
		llocs = ref !(x.llocs);
		alocs = ref !(x.alocs)
	}

(** Returns subst(store) *)
let substitution (subst : substitution) (partial : bool) (x : t) : t =
	let new_store = init [] [] in
		Hashtbl.iter (fun v le -> 
			let le_subst = lexpr_substitution subst partial le in
			let le_subst = if (le <> le_subst) then Reduction.reduce_lexpr le_subst else le_subst in
			put new_store v le_subst) x.store;
		new_store

(** Updates --store-- to subst(store) *)
let substitution_in_place (subst : substitution) (x : t) : unit =
	Hashtbl.iter (fun v le ->
		let s_le = lexpr_substitution subst true le in
		let s_le = if (le <> s_le) then Reduction.reduce_lexpr s_le else s_le in
		if (le <> s_le) then put x v s_le)
	x.store

(** Returns the set containing all the vars occurring in --store-- *)
let vars (x : t) : SS.t =
	SS.of_list (MS.to_list (MS.union !(x.lvars) !(x.pvars)))

(** Returns the set containing all the lvars occurring in --store-- *)
let lvars (x : t) : SS.t =
	let list = MS.to_list !(x.lvars) in
		print_debug_petar ("LVars: " ^ (String.concat ", " list));
		SS.of_list list

(** Returns the set containing all the alocs occurring in --store-- *)
let alocs (x : t) : SS.t =
	SS.of_list (MS.to_list !(x.alocs))

let unifiables (x : t) : SS.t = 
	SS.of_list (MS.to_list (List.fold_left MS.union MS.empty [!(x.lvars); !(x.pvars); !(x.llocs); !(x.alocs)]))

(** Partitions the variables in the domain of --store-- into two groups: 
    - the group containing the variables mapped onto lexprs satisfying --pred--
    - the rest *)
let partition (x : t) (pred_fun : jsil_logic_expr -> bool) : (string list) * (string list) =
	let x = x.store in
	Hashtbl.fold (fun x le (pred_xs, npred_xs) ->
		if (pred_fun le) then ((x :: pred_xs), npred_xs) else (pred_xs, (x :: npred_xs)))
	x ([], [])

(** Returns the projection of --store-- onto --xs-- *)
let projection (x : t) (xs : string list) : t =
	let y = init [] [] in
		List.iter (fun v ->
			if (mem x v) then put y v (get_unsafe x v)
		) xs;
		y

(** Calls --f-- on all variables of --store--; f(x, le_x) *)
let iter (x : t) (f : string -> jsil_logic_expr -> unit) : unit =
	Hashtbl.iter f x.store

let fold (x : t) (f : string -> jsil_logic_expr -> 'a  -> 'a) (init : 'a) : 'a =
	Hashtbl.fold f x.store init 

(** conversts a symbolic store to a list of assertions *)
let assertions (x : t) : jsil_logic_assertion list =
	let x = x.store in 
	Hashtbl.fold
		(fun x le assertions -> 
			(LEq (PVar x, le)) :: assertions) x []

let is_well_formed (x : t) : bool =
	let lvars = SS.elements (Hashtbl.fold (fun _ le ac -> SS.union ac (get_lexpr_lvars le)) x.store SS.empty) in 
	let pvars = SS.elements (Hashtbl.fold (fun v le ac -> SS.union (SS.add v ac) (get_lexpr_pvars le)) x.store SS.empty) in
	let llocs = SS.elements (Hashtbl.fold (fun v le ac -> SS.union ac (get_lexpr_clocs le)) x.store SS.empty) in
	let alocs = SS.elements (Hashtbl.fold (fun v le ac -> SS.union ac (get_lexpr_alocs le)) x.store SS.empty) in
	let ms_to_sl = fun ms -> SS.elements (SS.of_list (MS.to_list ms)) in 
	let rlvars = ms_to_sl !(x.lvars) in 
	let rpvars = ms_to_sl !(x.pvars) in 
	let rllocs = ms_to_sl !(x.llocs) in 
	let ralocs = ms_to_sl !(x.alocs) in 

	(* let strcct = fun ls -> String.concat ", " ls in
		print_debug (Printf.sprintf "LVars: \n\t%s\n\t%s" (strcct lvars) (strcct rlvars));
		print_debug (Printf.sprintf "PVars: \n\t%s\n\t%s" (strcct pvars) (strcct rpvars));
		print_debug (Printf.sprintf "LLocs: \n\t%s\n\t%s" (strcct llocs) (strcct rllocs));
		print_debug (Printf.sprintf "ALocs: \n\t%s\n\t%s" (strcct alocs) (strcct ralocs)); *)
	
		(lvars = rlvars) && 
		(pvars = rpvars) &&
		(llocs = rllocs) &&
		(alocs = ralocs)
			