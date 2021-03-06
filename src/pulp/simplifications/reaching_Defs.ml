(* ./src/pulp/simplifications/reaching_Defs.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Graphs
open Pulp_Syntax
open Pulp_Procedure
open Basic_Blocks
open Pulp_Syntax_Utils
open Simp_Common
open Type_Info

type definition_id = CFG_BB.node * int

let string_of_definition_id id = let n1, n2 = id in (string_of_int (CFG_BB.node_id n1)) ^ "-" ^ (string_of_int n2) 

type n = int

module DefIdSet = Set.Make (
  struct 
    type t = definition_id
    let compare (n1, int1) (n2, int2) =
      compare (CFG_BB.node_id n1, int1) (CFG_BB.node_id n2, int2)
  end
)

module NodeSet = Set.Make (
  struct 
    type t = CFG_BB.node
    let compare = compare
  end
)

module VarSet = Set.Make (
  struct 
    type t = variable
    let compare = compare
  end
)

module AssignSet = Set.Make (
  struct 
    type t = Pulp_Syntax.assignment
    let compare = compare
  end
)

let def_id_set_of_list l =
  List.fold_left (fun s el -> DefIdSet.add el s) DefIdSet.empty l
  
let node_set_of_list l =
  List.fold_left (fun s el -> NodeSet.add el s) NodeSet.empty l
  
let var_set_of_list l =
  List.fold_left (fun s el -> VarSet.add el s) VarSet.empty l
  
let assign_set_of_list l =
  List.fold_left (fun s el -> AssignSet.add el s) AssignSet.empty l

let add_to_hashtbl tbl var def_id = 
  let def_ids = 
    try
      Hashtbl.find tbl var
    with Not_found -> [] in
  if List.mem def_id def_ids then ()
  else Hashtbl.replace tbl var (def_id :: def_ids)
  
(*let remove_from_hashtbl tbl var def_id =
  let def_ids =
    try
      Hashtbl.find tbl var
    with Not_found -> [] in
  if List.mem def_id def_ids then Hashtbl.remove tbl var def_id*)
  
let get_from_hashtbl tbl var =
	try
	  Hashtbl.find tbl var
	with Not_found -> []
  
let calculate_defs (g : CFG_BB.graph) = 
  let def = Hashtbl.create 100 in
  let nodes = CFG_BB.nodes g in
  List.iter (fun n ->
	  let stmts = CFG_BB.get_node_data g n in
	  List.iteri (fun i stmt ->
	    match stmt.as_stmt.stmt_stx with
	      | Basic (Assignment stmt) ->
	        add_to_hashtbl def stmt.assign_left (n, i)
	      | _ -> ()
	  ) stmts
  ) nodes;
  def
  
let gen_kill_stmt def_id stmt def =
  match stmt.as_stmt.stmt_stx with
    | Basic (Assignment stmt) -> 
      let kills = List.filter (fun id -> id <> def_id) (Hashtbl.find def stmt.assign_left) in
      DefIdSet.singleton def_id, def_id_set_of_list kills
    | _ -> DefIdSet.empty, DefIdSet.empty


let rec union l1 l2 =
  match l1 with
    | [] -> l2
    | hd :: tail ->
      if List.mem hd l2 then union tail l2
      else hd :: (union tail l2)
  
let gen_kill_node n stmts def =
   let gen_kills = List.mapi (fun i stmt -> gen_kill_stmt (n, i) stmt def) stmts in
   List.fold_left (fun (gen_p, kill_p) (gen_n, kill_n) ->  
     (DefIdSet.union gen_n (DefIdSet.diff gen_p kill_n)), (DefIdSet.union kill_p kill_n)
    ) (DefIdSet.empty, DefIdSet.empty) gen_kills
  
  
let calculate_gens_kills g def = 
  let nodes = CFG_BB.nodes g in
  let node_gens = Hashtbl.create 100 in
  let node_kills = Hashtbl.create 100 in
  List.iter (fun n -> 
    let (gen, kill) = gen_kill_node n (CFG_BB.get_node_data g n) def in 
    Hashtbl.add node_gens n gen;
    Hashtbl.add node_kills n kill;
  ) nodes;
  node_gens, node_kills
  
let var_defid_tbl g =
  let tbl = Hashtbl.create 100 in
  let tbl_inverse = Hashtbl.create 100 in
  List.iter (fun n -> 
    let stmts = CFG_BB.get_node_data g n in
    List.iteri (fun i stmt ->
    match stmt.as_stmt.stmt_stx with
      | Basic (Assignment stmt) -> Hashtbl.add tbl stmt.assign_left (n, i);  Hashtbl.add tbl_inverse (n, i) stmt.assign_left
      | _ -> ()) stmts;
  ) (CFG_BB.nodes g);
  tbl, tbl_inverse
  
let rec repeat_until_equal ins outs wnodes g gens kills =
  match wnodes with
    | [] -> ()
    | n :: tail ->  
	  let old = Hashtbl.find outs n in
	  let preds = CFG_BB.pred g n in
	  let inn = List.fold_left (fun un pred -> DefIdSet.union un (Hashtbl.find outs pred)) DefIdSet.empty preds in
	  Hashtbl.replace outs n (DefIdSet.union (Hashtbl.find gens n) (DefIdSet.diff inn (Hashtbl.find kills n)));
	  Hashtbl.replace ins n inn;
	  let wnodes = 
	  if (DefIdSet.equal old (Hashtbl.find outs n)) then tail
	  else union tail (CFG_BB.succ g n) in
	  repeat_until_equal ins outs wnodes g gens kills   
      
let reaching_defs nodes g gens kills =
  let ins = Hashtbl.create 100 in
  let outs = Hashtbl.create 100 in
  List.iter (fun n -> Hashtbl.add ins n DefIdSet.empty; Hashtbl.add outs n DefIdSet.empty) nodes;
  repeat_until_equal ins outs nodes g gens kills;
  ins, outs
  
let calculate_reaching_defs g =
	let def = calculate_defs g in
	let gens, kills = calculate_gens_kills g def in
	let ins, outs = reaching_defs (CFG_BB.nodes g) g gens kills in
  ins, outs
  
let update_stmt stmt var const =
  let updated = Simp_Common.update_stmt var const stmt.as_stmt in
  {stmt with as_stmt = Simp_Common.simplify_stmt updated}
    
let rec propagate_const stmts var const =
  match stmts with
    | [] -> []
    | ({as_stmt = {stmt_stx = Basic (Assignment a)}} as s1) :: tail ->
      if a.assign_left = var then (update_stmt s1 var const) :: tail
      else (update_stmt s1 var const) :: (propagate_const tail var const)
    | stmt :: tail -> (update_stmt stmt var const) :: (propagate_const tail var const)
  
let constant_propagation g =
  let nodes = CFG_BB.nodes g in
  let ins, outs = calculate_reaching_defs g in
  let tbl, tblinv = var_defid_tbl g in
  
  List.iter (fun n -> 
    let vars = Hashtbl.create 5 in
    let nins = Hashtbl.find ins n in
    
    DefIdSet.iter (fun defid -> 
      let var = Hashtbl.find tblinv defid in
      Hashtbl.add vars var defid;
    ) nins;
    
    Hashtbl.iter (fun var _ -> 
      let deflist = Hashtbl.find_all vars var in
      match deflist with
        | [(nid, index)] ->
          begin
            let stmts = CFG_BB.get_node_data g nid in
            let stmt = List.nth stmts index in
              match stmt.as_stmt.stmt_stx with
                | Basic (Assignment {assign_right = Expression e}) ->
                  begin
			                 if is_const_expr e then begin
			                    let current_node_stmts = CFG_BB.get_node_data g n in
			                    let new_current_node_stmts = propagate_const current_node_stmts var e in
			                    CFG_BB.set_node_data g n new_current_node_stmts
			                 end else ()
                  end
                | _ -> ()
          end
        | _ -> ()
    ) vars;
  ) nodes
  
let const_prop_node g n =
  let vars_expr = Hashtbl.create 5 in
  
  let rec iter_block stmts =
    match stmts with
      | [] -> []
      | stmt :: stmts ->
        let stmt = Hashtbl.fold (fun var expr stmt -> update_stmt stmt var expr) vars_expr stmt in
        begin match stmt.as_stmt.stmt_stx with
          | Basic (Assignment a) ->
           begin match a.assign_right with
            | Expression e ->
		           if is_const_expr e then begin
                 Hashtbl.replace vars_expr a.assign_left e
		           end else Hashtbl.remove vars_expr a.assign_left
            | _ -> Hashtbl.remove vars_expr a.assign_left
           end
          | _ -> ()
        end; 
        stmt :: (iter_block stmts)
    in
  
  let stmts = CFG_BB.get_node_data g n in
  CFG_BB.set_node_data g n (iter_block stmts)
  

let simplify_guarded_gotos g =
  let nodes = CFG_BB.nodes g in
  let nodemap = Hashtbl.create 100 in
  List.iter (fun n ->
    let stmts = CFG_BB.get_node_data g n in
    match stmts with
      | {as_stmt = {stmt_stx = Label l}} :: tail -> Hashtbl.add nodemap l n
      | _ -> ()
  ) nodes;
  
  List.iter (fun n ->
    let rec update_last stmts = 
      match stmts with
        | [] -> []
        | [{as_stmt = {stmt_stx = GuardedGoto ((Literal (Bool true)), l1, l2)} as stx1} as s1] -> 
          CFG_BB.rm_edge g n (Hashtbl.find nodemap l2);
          CFG_BB.set_edge_data g n (Hashtbl.find nodemap l1) Edge_Normal;
          [{s1 with as_stmt = {stx1 with stmt_stx = Goto l1}}] 
        | [{as_stmt = {stmt_stx = GuardedGoto ((Literal (Bool false)), l1, l2)} as stx2} as s2] -> 
          CFG_BB.rm_edge g n (Hashtbl.find nodemap l1);
          CFG_BB.set_edge_data g n (Hashtbl.find nodemap l2) Edge_Normal;
          [{s2 with as_stmt = {stx2 with stmt_stx = Goto l2}}]
        | stmt :: tail -> stmt :: (update_last tail)
    in
    
    let stmts = CFG_BB.get_node_data g n in
    CFG_BB.set_node_data g n (update_last stmts)
    
  ) nodes
  
(* Liveness *)
  
let liveness_gen_kill_stmt stmt =
  match stmt.as_stmt.stmt_stx with
    | Basic (Assignment a) -> var_set_of_list(get_vars_in_assign_expr a.assign_right), VarSet.singleton (a.assign_left) 
    | _ -> var_set_of_list(get_vars_in_stmt stmt.as_stmt), VarSet.empty
  
let liveness_gen_kill_node n stmts =
   let gen_kills = List.map (fun stmt -> liveness_gen_kill_stmt stmt) stmts in
  
   List.fold_left (fun (gen_p, kill_p) (gen_n, kill_n) ->  
     (VarSet.union gen_p (VarSet.diff gen_n kill_p)), (VarSet.union kill_n kill_p)
    ) (VarSet.empty, VarSet.empty) gen_kills
  
  
let liveness_gens_kills g = 
  let nodes = CFG_BB.nodes g in
  let node_gens = Hashtbl.create 100 in
  let node_kills = Hashtbl.create 100 in
  List.iter (fun n -> 
    let (gen, kill) = liveness_gen_kill_node n (CFG_BB.get_node_data g n) in 
    Hashtbl.add node_gens n gen;
    Hashtbl.add node_kills n kill;
  ) nodes;
  node_gens, node_kills
  
  
let rec repeat_until_equal_liveness ins outs wnodes g gens kills =
  match wnodes with
    | [] -> ()
    | n :: tail ->
      let old = Hashtbl.find ins n in
      let succs = CFG_BB.succ g n in
      let outn = List.fold_left (fun in_s succ -> VarSet.union in_s (Hashtbl.find ins succ)) VarSet.empty succs in
      Hashtbl.replace ins n (VarSet.union (Hashtbl.find gens n) (VarSet.diff outn (Hashtbl.find kills n)));
      Hashtbl.replace outs n outn;
      let wnodes = 
      if (VarSet.equal old (Hashtbl.find ins n)) then tail
      else union tail (CFG_BB.pred g n) in
      repeat_until_equal_liveness ins outs wnodes g gens kills
      
      
let liveness nodes g gens kills =
  let ins = Hashtbl.create 100 in
  let outs = Hashtbl.create 100 in
  List.iter (fun n -> Hashtbl.add ins n VarSet.empty; Hashtbl.add outs n VarSet.empty) nodes;
  (* Do I want to reverse nodes? *)
  repeat_until_equal_liveness ins outs (List.rev nodes) g gens kills;
  ins, outs
  
let calculate_liveness g =
    let gens, kills = liveness_gens_kills g in
    let ins, outs = liveness (CFG_BB.nodes g) g gens kills in
  ins, outs  

let dead_code_elimination g throw_var return_var =
  let ins, outs = calculate_liveness g in
  let nodes = CFG_BB.nodes g in
  
  List.iter (fun n ->
    let var_defid = Hashtbl.create 10 in
    let defid_var = Hashtbl.create 10 in
    let defid_used = Hashtbl.create 10 in
  
	  let rec iter_block index stmts =
	    match stmts with
	      | [] -> []
	      | stmt :: stmts ->
          let vars = get_vars_in_stmt stmt.as_stmt in
          
          List.iter (fun var -> 
            if Hashtbl.mem var_defid var then
              let defid = Hashtbl.find var_defid var in
              Hashtbl.replace defid_used defid true
          ) vars;
          
	        begin match stmt.as_stmt.stmt_stx with
	          | Basic (Assignment a) ->
              Hashtbl.replace var_defid a.assign_left index;
              Hashtbl.replace defid_var index a.assign_left;
              if a.assign_left = throw_var || a.assign_left = return_var then Hashtbl.add defid_used index true
              else begin match a.assign_right with
                  | Expression _ -> Hashtbl.add defid_used index false 
                  | _ -> Hashtbl.add defid_used index true
              end
	          | _ -> ()
	        end; 
	        stmt :: (iter_block (index + 1) stmts)
	   in    
    
     let stmts = CFG_BB.get_node_data g n in
     let stmts = iter_block 0 stmts in
    
    let outn = Hashtbl.find outs n in
  
    let dead = Hashtbl.fold (fun defid used dead ->
      if used = true then dead
      else (* id not used inside the block *)
        begin if VarSet.mem (Hashtbl.find defid_var defid) outn then dead (* id is in out *)
              else defid :: dead
        end
      
    ) defid_used [] in
    
    let rest = List.mapi (fun index stmt -> 
      if List.mem index dead then []
      else [stmt]
    ) stmts in
    
    let rest = List.flatten rest in
    CFG_BB.set_node_data g n rest
    
  ) nodes
  
(* Copy propagation *)
let calculate_exprs g = 
  let exprs = Hashtbl.create 100 in
  let all_exprs = Hashtbl.create 100 in
  let nodes = CFG_BB.nodes g in
  List.iter (fun n ->
      let stmts = CFG_BB.get_node_data g n in
      List.iteri (fun i stmt ->
        match stmt.as_stmt.stmt_stx with
          | Basic (Assignment a) ->
            begin match a.assign_right with
              | Expression e ->
                let vars_in_e = Simp_Common.get_vars_in_expr e in
                List.iter (fun var -> add_to_hashtbl exprs var a) (a.assign_left :: vars_in_e);
                Hashtbl.replace all_exprs a ()
              | _ -> ()
            end
          | _ -> ()
      ) stmts
  ) nodes;
  let all_exprs = Hashtbl.fold (fun e _ l -> e :: l) all_exprs [] in
  exprs, all_exprs
  
let copy_gen_kill_stmt stmt exprs =
  match stmt.as_stmt.stmt_stx with
    | Basic (Assignment a) -> 
      begin match a.assign_right with
        | Expression e -> AssignSet.singleton a, assign_set_of_list (get_from_hashtbl exprs a.assign_left)  
        | _ -> AssignSet.empty, assign_set_of_list (get_from_hashtbl exprs a.assign_left)
      end
    | stmt -> AssignSet.empty, AssignSet.empty
  
  
let copy_gen_kill_node n stmts exprs =
   let gen_kills = List.map (fun stmt -> copy_gen_kill_stmt stmt exprs) stmts in
  
   List.fold_left (fun (gen_p, kill_p) (gen_n, kill_n) ->  
     (AssignSet.union gen_n (AssignSet.diff gen_p kill_n)), (AssignSet.union kill_p kill_n)
    ) (AssignSet.empty, AssignSet.empty) gen_kills
  
  
let copy_gens_kills g exprs = 
  let nodes = CFG_BB.nodes g in
  let node_gens = Hashtbl.create 100 in
  let node_kills = Hashtbl.create 100 in
  List.iter (fun n -> 
    let (gen, kill) = copy_gen_kill_node n (CFG_BB.get_node_data g n) exprs in 
    Hashtbl.add node_gens n gen;
    Hashtbl.add node_kills n kill;
  ) nodes;
  node_gens, node_kills
  
let rec repeat_until_equal_copy ins outs wnodes g gens kills =
  match wnodes with
    | [] -> ()
    | n :: tail ->
      let old = Hashtbl.find outs n in
      let preds = CFG_BB.pred g n in
      let inn = 
        match preds with 
          | [] -> AssignSet.empty
          | firstp :: tail -> 
            List.fold_left (fun un pred -> AssignSet.inter un (Hashtbl.find outs pred)) (Hashtbl.find outs firstp) tail in
      Hashtbl.replace outs n (AssignSet.union (Hashtbl.find gens n) (AssignSet.diff inn (Hashtbl.find kills n)));
      Hashtbl.replace ins n inn;
      let wnodes = 
      if (AssignSet.equal old (Hashtbl.find outs n)) then tail
      else union tail (CFG_BB.succ g n) in
      repeat_until_equal_copy ins outs wnodes g gens kills
      
      
let copy_ins_out nodes g gens kills all_exprs =
  let ins = Hashtbl.create 100 in
  let outs = Hashtbl.create 100 in
  List.iter (fun n -> Hashtbl.add ins n (assign_set_of_list all_exprs); Hashtbl.add outs n AssignSet.empty) nodes;
  begin match nodes with
    | start :: tail -> Hashtbl.add ins start AssignSet.empty
    | [] -> ()
  end;
  repeat_until_equal_copy ins outs nodes g gens kills;
  ins, outs

let copy_propagation g =
  let exprs, all_exprs = calculate_exprs g in
  let gens, kills = copy_gens_kills g exprs in
  let nodes = CFG_BB.nodes g in
  let ins, outs = copy_ins_out nodes g gens kills all_exprs in
  
  List.iter (fun n ->
    let stmts = CFG_BB.get_node_data g n in
    let inn = Hashtbl.find ins n in
    
    let inn, updated_stmts = List.fold_left (fun (inn, updated_stmts) stmt ->
      let vars = match stmt.as_stmt.stmt_stx with
        | Basic (Assignment a) ->
          Simp_Common.get_vars_in_assign_expr a.assign_right
        | _ -> 
          Simp_Common.get_vars_in_stmt stmt.as_stmt
      in
      let updated_stmt = 
          List.fold_left (fun stmt var -> 
            try
              let s = AssignSet.choose (AssignSet.filter (fun s -> s.assign_left = var) inn) in
              match s.assign_right with
                | Expression e -> update_stmt stmt var e
                | _ -> stmt
            with 
              | Not_found -> stmt
          ) stmt vars 
      in
      let (gen, kill) = copy_gen_kill_stmt stmt exprs in
      (AssignSet.union gen (AssignSet.diff inn kill)), updated_stmt :: updated_stmts
    ) (inn, []) stmts in
    
    CFG_BB.set_node_data g n (List.rev updated_stmts)
    
  ) nodes
  
(* Type propagation *)
  
let type_simplifications g params proc_type = 
  let def = calculate_defs g in
  let ins, outs = calculate_reaching_defs g in
  let nodes = CFG_BB.nodes g in
  let tbl, tblinv = var_defid_tbl g in
  
  let defid_type_depend = Hashtbl.create 100 in (* def_id -> var, def_id list *)
  
  (* Type dependence graph *)
  List.iter (fun n ->
    let stmts = CFG_BB.get_node_data g n in
    let inn = Hashtbl.find ins n in
    
    let _ = List.fold_left (fun (inn, index) stmt ->
      let var_defid = Hashtbl.create 5 in (* var -> defid list *)
    
	    DefIdSet.iter (fun defid -> 
	      let var = Hashtbl.find tblinv defid in
	      Hashtbl.add var_defid var defid;
	    ) inn;
    
      begin match stmt.as_stmt.stmt_stx with
        | Basic (Assignment a) ->
          begin match a.assign_right with
            | Expression e -> 
              let vars = Simp_Common.get_vars_in_expr e in
              let defids = List.fold_left (fun defids var -> 
                union (List.map (fun defid -> var, defid) (Hashtbl.find_all var_defid var)) defids
              ) [] vars in
              Hashtbl.add defid_type_depend (n, index) defids
            | _ -> Hashtbl.add defid_type_depend (n, index) []
          end
        | _ -> ()
      end;
          
     let (gen, kill) = gen_kill_stmt (n, index) stmt def in 
     (DefIdSet.union gen (DefIdSet.diff inn kill)), index + 1
      
   ) (inn, 0) stmts in ()
    
  ) nodes;

  let defid_type = Hashtbl.create 100 in (* def_id -> type *)
  
	let type_info depend v = 
    if (proc_type = Procedure_User && List.mem v params) then Some (TI_Value)
    else begin
			let defids = List.filter (fun (var, defid) -> var = v) depend in
			let types = List.map (fun (var, defid) -> Hashtbl.find defid_type defid) defids in
			match types with
			  | [] -> None
			  | t :: types -> List.fold_left upper_bound_type t types
     end in
  
  let rec infer_type defid = 
    if Hashtbl.mem defid_type defid then ()
    else begin
      let depend = Hashtbl.find defid_type_depend defid in
      Hashtbl.add defid_type defid None;
      List.iter (fun (var, defid) -> infer_type defid) depend;
      let (nodeid, index) = defid in
      let stmt = List.nth (CFG_BB.get_node_data g nodeid) index in
      let def_id_t = match stmt.as_stmt.stmt_stx with
        | Basic (Assignment a) -> get_type_info_assign_expr (type_info depend) a.assign_right
        | _ -> None in
      Hashtbl.replace defid_type defid def_id_t
    end
  in
  
  Hashtbl.iter (fun defid _ -> infer_type defid) defid_type_depend;
  
  (* Simplifications *)
  List.iter (fun n ->
    let stmts = CFG_BB.get_node_data g n in
    let inn = Hashtbl.find ins n in
  
    let _, updated_stmts, _ = List.fold_left (fun (inn, updated_stmts, index) stmt ->
      let var_defid = List.map (fun defid -> 
	      let var = Hashtbl.find tblinv defid in
	      (var, defid)
	    ) (DefIdSet.elements inn) in
      
      let updated_stmt = {stmt with as_stmt = simplify_stmt (simplify_type_of_in_stmt (type_info var_defid) stmt.as_stmt)} in 
      
      let vars = get_vars_in_stmt stmt.as_stmt in
      
      let vars_type_info = List.fold_left (fun result var -> 
        match type_info var_defid var with
          | None -> result
          | Some info -> (var, info) :: result) [] vars in
      
      let updated_stmt = {updated_stmt with as_annot = Some {annot_type_info = vars_type_info}} in
          
      let (gen, kill) = gen_kill_stmt (n, index) stmt def in 
      (DefIdSet.union gen (DefIdSet.diff inn kill)), updated_stmt :: updated_stmts, index + 1
      
    ) (inn, [], 0) stmts in 
    
    CFG_BB.set_node_data g n (List.rev updated_stmts)
    
  ) nodes
  

  
let debug_print_cfg_bb_with_defs (cfgs : CFG_BB.graph AllFunctions.t) (filename : string) : unit =
  let d_cfgedge chan dest src =
    Printf.fprintf chan "\t\t%i -> %i\n" (CFG_BB.node_id src) (CFG_BB.node_id dest) in
  let d_cfgnode chan (cfg : CFG_BB.graph) (n : CFG_BB.node) (nd : annotated_statement list) ins outs =
    let ins_ids = DefIdSet.elements (Hashtbl.find ins n) in
    let ins_string = String.concat ";" (List.map string_of_definition_id ins_ids) in
    let outs_ids = DefIdSet.elements (Hashtbl.find outs n) in
    let out_string = String.concat ";" (List.map string_of_definition_id outs_ids) in
    Printf.fprintf chan 
      "\t\t%i [label=\"%i: %s\"]\n" 
      (CFG_BB.node_id n)
      (CFG_BB.node_id n) 
      (String.escaped (string_of_annot_stmts nd) ^ "\n" ^ ins_string ^ "\n" ^ out_string);    
      List.iter (fun dest -> d_cfgedge chan dest n) (CFG_BB.succ cfg n) in
  let chan = open_out (filename ^ ".cfg.dot") in
  Printf.fprintf chan "digraph iCFG {\n\tnode [shape=box,  labeljust=l]\n";
  AllFunctions.iter 
    (fun name cfg -> 
      List.iter (fun n -> const_prop_node cfg n) (CFG_BB.nodes cfg);
      let _ = constant_propagation cfg in
      let _ = simplify_guarded_gotos cfg in
      let _ = remove_unreachable cfg in
      let _ = remove_empty_blocks cfg in
      let _ = transform_to_basic_blocks cfg in
      let ins, outs = calculate_reaching_defs cfg in
      Printf.fprintf chan "\tsubgraph \"cluster_%s\" {\n\t\tlabel=\"%s\"\n" name (String.escaped name);
      List.iter (fun n -> d_cfgnode chan cfg n (CFG_BB.get_node_data cfg n) ins outs) (CFG_BB.nodes cfg);
      Printf.fprintf chan  "\t}\n";
    ) 
    cfgs;
  Printf.fprintf chan "}\n";
  close_out chan


