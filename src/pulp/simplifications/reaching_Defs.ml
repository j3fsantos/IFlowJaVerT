open Graphs
open Pulp_Syntax
open Basic_Blocks
open Pulp_Syntax_Utils

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
  if List.mem def_id def_ids then Hashtbl.remove tbl var def_id
  
let get_from_hashtbl tbl var =
	try
	  Hasbtbl.find tbl var
	with Not_found -> []*)
  
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
      let ins, outs = calculate_reaching_defs cfg in
      Printf.fprintf chan "\tsubgraph \"cluster_%s\" {\n\t\tlabel=\"%s\"\n" name (String.escaped name);
      List.iter (fun n -> d_cfgnode chan cfg n (CFG_BB.get_node_data cfg n) ins outs) (CFG_BB.nodes cfg);
      Printf.fprintf chan  "\t}\n";
    ) 
    cfgs;
  Printf.fprintf chan "}\n";
  close_out chan


