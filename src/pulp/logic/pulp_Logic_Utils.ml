open Pulp_Syntax
open Batteries (* TODO remove? *)
open List
open Utils
open Pulp_Logic
open Pulp_Logic_Print

exception InconsistentState of string
exception InvalidParameter of string
exception CannotRemoveHeaplet

let fresh_a_suggest =
  let counter = ref 0 in
  let rec f name =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    AVar v
  in f
  
let fresh_a () =
  fresh_a_suggest "av_"
  
let fresh_e_suggest =
  let counter = ref 0 in
  let rec f name =
    let v = name ^ (string_of_int !counter) in
    counter := !counter + 1;
    EVar v
  in f
  
let fresh_e () =
  fresh_e_suggest "ev_"

let rec get_return p =
  match p with
    | Star l -> fold_left (fun e r -> if e = None then get_return r else e) None l
    | REq e -> Some e
    | _ -> None

(* Remove (return = v) from formula p *)
let forget_return p =
  let rec forget_return_with p =
    let f = forget_return_with in
    match p with
      | Star l -> Star (map f l)
      | REq e -> empty_f
      | _ -> p
  in
  forget_return_with p
  
(* simplify don't need? *)  
let rec simplify (p : formula) : formula = Profiler.track Profiler.SymExec (fun () ->
  match p with
	  | Star l ->
	    let l = map simplify l in
	    let star_list p' = match p' with Star l' -> l' | _ -> [p'] in
      Star (flat_map star_list l)
    | _ -> p  
  )

let combine (p:formula) (q:formula) : formula = 
  simplify (Star [p;q])

let join_antiframe af1 af2 =
  match af1, af2 with
    | Some af1, Some af2 -> Some (simplify (Star [af1; af2]))
    | Some af1, None -> Some af1
    | None, _ -> af2

let add_antiframe p af =
  match af with
    | Some af -> simplify (Star [af; p])
    | None -> p

let map_af_formula f fa =
  {fa with af_formula = f fa.af_formula}
  
let map_af_antiframe f fa =
  {fa with af_antiframe = f fa.af_antiframe}

let rec subs_vars_in_exp vmap exp  =
  let g = subs_vars_in_exp vmap in
  let subs x = 
    if LogicalVarMap.mem x vmap then LogicalVarMap.find x vmap else x in
  match exp with
    | Le_Var x -> Le_Var (subs x)
    | Le_PVar x -> Le_PVar x
    | Le_Literal l -> Le_Literal l
    | Le_None -> Le_None
    | Le_UnOp (op, e) -> Le_UnOp (op, g e) 
    | Le_BinOp (e1, bop, e2) -> Le_BinOp (g e1, bop, g e2)
    | Le_Ref (e1, e2, rt) -> Le_Ref (g e1, g e2, rt)
    | Le_Base e -> Le_Base (g e)
    | Le_Field e -> Le_Field (g e)
    | Le_TypeOf e -> Le_TypeOf (g e)

let rec subs_vars vmap (f : formula) =
  let g = subs_vars vmap in
  let ge = subs_vars_in_exp vmap in
  match f with
    | Star fl -> Star (map g fl)
    | Heaplet (e1, e2, e3) -> Heaplet (ge e1, ge e2, ge e3)
    | Eq (f1, f2) -> Eq (ge f1, ge f2)
    | NEq (f1, f2) -> NEq (ge f1, ge f2)
    | REq f1 -> REq (ge f1)       
    | ObjFootprint (e, es) -> ObjFootprint (ge e, map ge es)

let rec get_logical_vars_exp e =
  let f = get_logical_vars_exp in
  match e with
    | Le_Var lv -> [lv]
    | Le_BinOp (le1, _, le2)
    | Le_Ref (le1, le2, _) -> (f le1) @ (f le2)
    | Le_Base e
    | Le_Field e 
    | Le_TypeOf e
    | Le_UnOp (_, e) -> f e
    | Le_Literal _
    | Le_None
    | Le_PVar _ -> []

let rec get_program_vars_exp e =
  let f = get_program_vars_exp in
  match e with
    | Le_PVar v -> [v]
    | Le_BinOp (le1, _, le2)
    | Le_Ref (le1, le2, _) -> (f le1) @ (f le2)
    | Le_Base e
    | Le_Field e 
    | Le_TypeOf e
    | Le_UnOp (_, e) -> f e
    | Le_Literal _
    | Le_None
    | Le_Var _ -> []
      
let rec get_logical_vars f =
  let g = get_logical_vars_exp in
  match f with
    | Star fl -> flat_map get_logical_vars fl
    | Heaplet (le1, le2, le3) -> (g le1) @ (g le2) @ (g le3)
    | Eq (f1, f2) -> (g f1) @ (g f2)
    | NEq (f1, f2) -> (g f1) @ (g f2)
    | REq f1 -> g f1       
    | ObjFootprint (e, es) -> (g e) @ (flat_map g es) 

let rec get_program_vars f =
  let g = get_program_vars_exp in
  match f with
    | Star fl -> flat_map get_program_vars fl
    | Heaplet (le1, le2, le3) -> (g le1) @ (g le2) @ (g le3)
    | Eq (f1, f2) -> (g f1) @ (g f2)
    | NEq (f1, f2) -> (g f1) @ (g f2)
    | REq f1 -> g f1       
    | ObjFootprint (e, es) -> (g e) @ (flat_map g es)
    
           
let pretty_string_of_formula x =
  let f = simplify x in
  let fs = match f with
    | Star fs -> fs
    | f -> [f] in
  let (heaplets, others) = List.partition (fun f -> 
    match f with
      | Heaplet _ -> true
      | _ -> false
  ) fs in
  let es = unique (map (fun h ->
    match h with
      | Heaplet (e1, _, _) -> e1
      | _ -> raise (InvalidParameter "Must be a heaplet")
  ) heaplets) in
  let hf = Star heaplets in
  let obj_strings = map (fun e -> 
    let hasnt = get_empty_heaplets_for_expr e hf in
    let has = get_non_empty_heaplets_for_expr e hf in
    Printf.sprintf "#obj [%s] %s" (string_of_logical_exp e) (string_of_fields hasnt has)
  ) es in
 ("  " ^ String.concat "\n* " obj_strings) ^ ("\n*") ^ (string_of_formula (Star others))

let rec increase_footprint (l : logical_exp) (x : logical_exp) (p : formula) = Profiler.track Profiler.SymExec (fun () ->
  let f = increase_footprint l x in
  match p with
    | Star l -> Star (map f l)
    | ObjFootprint (l', vars) -> 
      if (l = l' && not (mem x vars)) then ObjFootprint (l', x :: vars) else p
    | _ -> p
  )

let rec outside_of_footprint (l : logical_exp) (x : logical_exp) (p : formula) : bool = Profiler.track Profiler.SymExec (fun () ->
  let f = outside_of_footprint l x in
  match p with
    | Star l -> List.exists f l
    | ObjFootprint (l', vars) -> l' = l && not (mem x vars)
    | _ -> false
  )

(* Get the value v of the (l,x) -> v if it exists in p *)
(* v can be (/) *)
let rec get_heaplet (l : logical_exp) (x : logical_exp) (p : formula) : logical_exp option = Profiler.track Profiler.SymExec (fun () ->
  let f = get_heaplet l x in
  match p with
    | Star l -> List.fold_left (fun e r -> if e = None then f r else e) None l
    | Heaplet (l1, x1, e) -> if (l1 = l && x1 = x) then Some e else None
    | _ -> None
  )

(* returns true if (l,x) |-> (/) exists in p *)
let is_heaplet_empty (l : logical_exp) (x : logical_exp) (p : formula) : bool = Profiler.track Profiler.SymExec (fun () ->
  outside_of_footprint l x p || (get_heaplet l x p = Some Le_None)
  )

let rec remove_heaplet l x p = Profiler.track Profiler.SymExec (fun () ->
  let f = remove_heaplet l x in
  match p with
    | Star l -> Star (map f l)
    | Heaplet (l1, x1, _) -> if (l1 = l && x1 = x) then empty_f else p
    | _ -> p
  )  
      
let update_heaplet (l : logical_exp) (x : logical_exp) (e : logical_exp) (p : formula) = Profiler.track Profiler.SymExec (fun () ->
  let p = increase_footprint l x p in 
  let p = remove_heaplet l x p in
  combine (Heaplet (l, x, e)) p
  )
  
let rec subs_pvar_in_exp x xle le =
  let f = subs_pvar_in_exp x xle in
  match le with
    | Le_Var x -> Le_Var x
    | Le_PVar y -> if x = y then xle else le
    | Le_Literal l -> Le_Literal l
    | Le_None -> Le_None
    | Le_UnOp (op, e) -> Le_UnOp (op, f e) 
    | Le_BinOp (e1, bop, e2) -> Le_BinOp (f e1, bop, f e2)
    | Le_Ref (e1, e2, rt) -> Le_Ref (f e1, f e2, rt)
    | Le_Base e -> Le_Base (f e)
    | Le_Field e -> Le_Field (f e)
    | Le_TypeOf e -> Le_TypeOf (f e)

