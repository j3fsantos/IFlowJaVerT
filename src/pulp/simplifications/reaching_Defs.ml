open Graphs
open Pulp_Syntax
open Basic_Blocks
open Pulp_Syntax_Utils
open Simp_Common

type definition_id = int * int

let string_of_definition_id (n1, n2) = (string_of_int n1) ^ "-" ^ (string_of_int n1)

type n = int

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
	    match stmt with
	      | Basic (Assignment stmt) ->
	        add_to_hashtbl def stmt.assign_left (n, i)
	      | _ -> ()
	  ) stmts
  ) nodes;
  def
  
let gen_kill_stmt def_id stmt def =
  match stmt with
    | Basic (Assignment stmt) -> [def_id], List.filter (fun id -> id <> def_id) (Hashtbl.find def stmt.assign_left) 
    | _ -> [], []

let rec union l1 l2 =
  match l1 with
    | [] -> l2
    | hd :: tail ->
      if List.mem hd l2 then union tail l2
      else hd :: (union tail l2)
      
let rec intersection l1 l2 =
  match l1 with
    | [] -> []
    | hd :: tail ->
      if List.mem hd l2 then hd :: (intersection tail l2)
      else intersection tail l2
      
let rec subtract l1 l2 =
  match l1 with
    | [] -> []
    | hd :: tail ->
      if List.mem hd l2 then subtract tail l2
      else hd :: (subtract tail l2)
      
let list_eq l1 l2 =
  (subtract l1 l2 = []) && (subtract l2 l1 = [])
  
let gen_kill_node n stmts def =
   let gen_kills = List.mapi (fun i stmt -> gen_kill_stmt (n, i) stmt def) stmts in
   List.fold_left (fun (gen_p, kill_p) (gen_n, kill_n) ->  
     (union gen_n (subtract gen_p kill_n)), (union kill_p kill_n)
    ) ([], []) gen_kills
  
  
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
    match stmt with
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
      let inn = List.fold_left (fun un pred -> union un (Hashtbl.find outs pred)) [] preds in
      Hashtbl.replace outs n (union (Hashtbl.find gens n) (subtract inn (Hashtbl.find kills n)));
      Hashtbl.replace ins n inn;
      let wnodes = 
      if (list_eq old (Hashtbl.find outs n)) then tail
      else union tail (CFG_BB.succ g n) in
      repeat_until_equal ins outs wnodes g gens kills
      
      
let reaching_defs nodes g gens kills =
  let ins = Hashtbl.create 100 in
  let outs = Hashtbl.create 100 in
  List.iter (fun n -> Hashtbl.add ins n []; Hashtbl.add outs n []) nodes;
  repeat_until_equal ins outs nodes g gens kills;
  ins, outs
  
let calculate_reaching_defs g =
	let def = calculate_defs g in
	let gens, kills = calculate_gens_kills g def in
	let ins, outs = reaching_defs (CFG_BB.nodes g) g gens kills in
  ins, outs
  
let update_stmt stmt var const =
  let updated = Simp_Common.update_stmt var const stmt in
  Simp_Common.simplify_stmt updated
    
let rec propagate_const stmts var const =
  match stmts with
    | [] -> []
    | Basic (Assignment a) :: tail ->
      if a.assign_left = var then (update_stmt (Basic (Assignment a)) var const) :: tail
      else (update_stmt (Basic (Assignment a)) var const) :: (propagate_const tail var const)
    | stmt :: tail -> (update_stmt stmt var const) :: (propagate_const tail var const)
  
let constant_propagation g =
  let nodes = CFG_BB.nodes g in
  let ins, outs = calculate_reaching_defs g in
  let tbl, tblinv = var_defid_tbl g in
  
  List.iter (fun n -> 
    let vars = Hashtbl.create 5 in
    let nins = Hashtbl.find ins n in
    
    List.iter (fun defid -> 
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
              match stmt with
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
        begin match stmt with
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
      | Label l :: tail -> Hashtbl.add nodemap l n
      | _ -> ()
  ) nodes;
  
  List.iter (fun n ->
    let rec update_last stmts = 
      match stmts with
        | [] -> []
        | [GuardedGoto ((Literal (Bool true)), l1, l2)] -> 
          CFG_BB.rm_edge g n (Hashtbl.find nodemap l2);
          CFG_BB.set_edge_data g n (Hashtbl.find nodemap l1) Edge_Normal;
          [Goto l1] 
        | [GuardedGoto ((Literal (Bool false)), l1, l2)] -> 
          CFG_BB.rm_edge g n (Hashtbl.find nodemap l1);
          CFG_BB.set_edge_data g n (Hashtbl.find nodemap l2) Edge_Normal;
          [Goto l2]
        | stmt :: tail -> stmt :: (update_last tail)
    in
    
    let stmts = CFG_BB.get_node_data g n in
    CFG_BB.set_node_data g n (update_last stmts)
    
  ) nodes
  
(* Liveness *)
  
let liveness_gen_kill_stmt stmt =
  match stmt with
    | Basic (Assignment a) -> get_vars_in_assign_expr a.assign_right, [a.assign_left]  
    | stmt -> get_vars_in_stmt stmt, []
  
let liveness_gen_kill_node n stmts =
   let gen_kills = List.map (fun stmt -> liveness_gen_kill_stmt stmt) stmts in
  
   List.fold_left (fun (gen_p, kill_p) (gen_n, kill_n) ->  
     (union gen_p (subtract gen_n kill_p)), (union kill_n kill_p)
    ) ([], []) gen_kills
  
  
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
      let outn = List.fold_left (fun in_s succ -> union in_s (Hashtbl.find ins succ)) [] succs in
      Hashtbl.replace ins n (union (Hashtbl.find gens n) (subtract outn (Hashtbl.find kills n)));
      Hashtbl.replace outs n outn;
      let wnodes = 
      if (list_eq old (Hashtbl.find ins n)) then tail
      else union tail (CFG_BB.pred g n) in
      repeat_until_equal_liveness ins outs wnodes g gens kills
      
      
let liveness nodes g gens kills =
  let ins = Hashtbl.create 100 in
  let outs = Hashtbl.create 100 in
  List.iter (fun n -> Hashtbl.add ins n []; Hashtbl.add outs n []) nodes;
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
          let vars = get_vars_in_stmt stmt in
          
          List.iter (fun var -> 
            if Hashtbl.mem var_defid var then
              let defid = Hashtbl.find var_defid var in
              Hashtbl.replace defid_used defid true
          ) vars;
          
	        begin match stmt with
	          | Basic (Assignment a) ->
              Hashtbl.replace var_defid a.assign_left index;
              Hashtbl.replace defid_var index a.assign_left;
              if a.assign_left = throw_var || a.assign_left = return_var then Hashtbl.add defid_used index true
              else Hashtbl.add defid_used index false;
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
        begin if List.mem (Hashtbl.find defid_var defid) outn then dead (* id is in out *)
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
        match stmt with
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
  match stmt with
    | Basic (Assignment a) -> 
      begin match a.assign_right with
        | Expression e -> [a], get_from_hashtbl exprs a.assign_left  
        | _ -> [], get_from_hashtbl exprs a.assign_left
      end
    | stmt -> [], []
  
  
let copy_gen_kill_node n stmts exprs =
   let gen_kills = List.map (fun stmt -> copy_gen_kill_stmt stmt exprs) stmts in
  
   List.fold_left (fun (gen_p, kill_p) (gen_n, kill_n) ->  
     (union gen_n (subtract gen_p kill_n)), (union kill_p kill_n)
    ) ([], []) gen_kills
  
  
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
          | [] -> []
          | firstp :: tail -> 
            List.fold_left (fun un pred -> intersection un (Hashtbl.find outs pred)) (Hashtbl.find outs firstp) tail in
      Hashtbl.replace outs n (union (Hashtbl.find gens n) (subtract inn (Hashtbl.find kills n)));
      Hashtbl.replace ins n inn;
      let wnodes = 
      if (list_eq old (Hashtbl.find outs n)) then tail
      else union tail (CFG_BB.succ g n) in
      repeat_until_equal_copy ins outs wnodes g gens kills
      
      
let copy_ins_out nodes g gens kills all_exprs =
  let ins = Hashtbl.create 100 in
  let outs = Hashtbl.create 100 in
  List.iter (fun n -> Hashtbl.add ins n all_exprs; Hashtbl.add outs n []) nodes;
  begin match nodes with
    | start :: tail -> Hashtbl.add ins start []
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
      let vars = match stmt with
        | Basic (Assignment a) ->
          Simp_Common.get_vars_in_assign_expr a.assign_right
        | other -> 
          Simp_Common.get_vars_in_stmt other
      in
      let updated_stmt = 
          List.fold_left (fun stmt var -> 
            try
              let s = List.find (fun s -> s.assign_left = var) inn in
              match s.assign_right with
                | Expression e -> update_stmt stmt var e
                | _ -> stmt
            with 
              | Not_found -> stmt
          ) stmt vars 
      in
      let (gen, kill) = copy_gen_kill_stmt stmt exprs in
      (union gen (subtract inn kill)), updated_stmt :: updated_stmts
    ) (inn, []) stmts in
    
    CFG_BB.set_node_data g n (List.rev updated_stmts)
    
  ) nodes
  

  
let debug_print_cfg_bb_with_defs (cfgs : CFG_BB.graph AllFunctions.t) (filename : string) : unit =
  let d_cfgedge chan dest src =
    Printf.fprintf chan "\t\t%i -> %i\n" (CFG_BB.node_id src) (CFG_BB.node_id dest) in
  let d_cfgnode chan (cfg : CFG_BB.graph) (n : CFG_BB.node) (nd : statement list) ins outs =
    let ins_ids = Hashtbl.find ins n in
    let string_of_definition_id id = let n1, n2 = id in (string_of_int (CFG_BB.node_id n1)) ^ "-" ^ (string_of_int n2) in
    let ins_string = String.concat ";" (List.map string_of_definition_id ins_ids) in
    let outs_ids = Hashtbl.find outs n in
    let out_string = String.concat ";" (List.map string_of_definition_id outs_ids) in
    Printf.fprintf chan 
      "\t\t%i [label=\"%i: %s\"]\n" 
      (CFG_BB.node_id n)
      (CFG_BB.node_id n) 
      (String.escaped (Pulp_Syntax_Print.string_of_statement_list nd) ^ "\n" ^ ins_string ^ "\n" ^ out_string);    
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


