open Pulp_Syntax
open Batteries

module AllLabels = Map.Make ( 
  struct 
    type t = label
    let compare = compare
  end
)

type cfg_node = { 
  cfgn_id: int;  
  mutable cfgn_children: cfg_node list; 
  mutable cfgn_parents: cfg_node list;
  mutable cfgn_excep_children: cfg_node list;
  mutable cfgn_excep_parents: cfg_node list;
  cfgn_statement: statement;
}

type cf_graph = {
  cfg_id: int;
  cfg_entry: cfg_node;
  cfg_exit: cfg_node;
}

let make_node : statement -> cfg_node =
  let x = ref 0 in
  fun stmt ->
    incr x;
    {cfgn_statement = stmt; 
     cfgn_id = !x; 
     cfgn_children = []; 
     cfgn_parents = []; 
     cfgn_excep_children = [];
     cfgn_excep_parents = [];
    }
    
let make_new_node stmt : cfg_node =
  make_node stmt
  
let make_skip_node () : cfg_node =
  make_new_node Skip    
  
let make_graph () : cf_graph =
  let x = ref 0 in incr x;
  {cfg_id = !x; cfg_entry = make_skip_node (); cfg_exit = make_skip_node ()}
  
let connect node_start node_end =
  node_start.cfgn_children <- node_end :: node_start.cfgn_children;
  node_end.cfgn_parents <- node_start :: node_end.cfgn_parents
  
let connect_excep node_start node_end =
  node_start.cfgn_excep_children <- node_end :: node_start.cfgn_excep_children;
  node_end.cfgn_excep_parents <- node_start :: node_end.cfgn_excep_parents
    
let disconnect node_start node_end =
  node_start.cfgn_children <- List.filter (fun child -> not (child.cfgn_id = node_end.cfgn_id)) node_start.cfgn_children;
  node_end.cfgn_parents <- List.filter (fun parent -> not (parent.cfgn_id = node_start.cfgn_id)) node_end.cfgn_parents
  
let disconnect_excep node_start node_end =
  node_start.cfgn_excep_children <- List.filter (fun child -> not (child.cfgn_id = node_end.cfgn_id)) node_start.cfgn_excep_children;
  node_end.cfgn_excep_parents <- List.filter (fun parent -> not (parent.cfgn_id = node_start.cfgn_id)) node_end.cfgn_excep_parents
    
let get_all_nodes (cfg : cf_graph) : cfg_node list = 
  let rec get_non_existing_child_nodes (node : cfg_node) (node_set : cfg_node list) : cfg_node list =
  if List.mem node node_set then node_set 
  else begin
    let node_set = node :: node_set in
    List.fold_left (fun node_set child -> get_non_existing_child_nodes child node_set) node_set node.cfgn_children 
  end
  in  
  get_non_existing_child_nodes cfg.cfg_entry []
  
let get_all_labels fb =
  let label_map = AllLabels.empty in
  let labels = List.unique ((List.fold_left (fun lbs stmt -> 
    match stmt with
      | Label l -> l :: lbs
      | Goto ls -> ls @ lbs
      | _ -> lbs
    ) [] fb.func_body) @ [fb.func_ctx.label_throw; fb.func_ctx.label_return]) in
  List.fold_left (fun lbs l -> 
    let label_node = make_new_node (Label l) in
    AllLabels.add l label_node lbs
   ) label_map labels
  
  
let stmt_to_cfg (stmt : statement) label_map (ctx : translation_ctx) (start : cfg_node): cfg_node =
  match stmt with
    | Skip
    | Mutation _
    | Deallocation _
    | Assume _
    | Assert _ ->
      begin
	      let n = make_new_node stmt in 
	      connect start n; 
	      n
      end
	  | Assignment assign ->
      begin match assign.assign_right with
			  | Literal _
			  | Empty 
			  | Var _
			  | BinOp _
			  | Ref _
			  | Field _
			  | Base _
			  | HasField _
			  | Lookup _
			  | Obj ->
           let n = make_new_node stmt in 
           connect start n; 
           n
          
			  | BuiltInFunction bf ->
          begin match bf with
            | Pi (b, x) ->            
              let n = make_new_node stmt in 
              connect start n; 
              n
          end
        | Call c ->
           let n = make_new_node stmt in 
           connect start n; 
           let throw_label_node = AllLabels.find ctx.label_throw label_map in
           let return_label_node = AllLabels.find ctx.label_return label_map in
           connect n return_label_node;
           connect_excep n throw_label_node;
           return_label_node
      end
    | Label l -> AllLabels.find l label_map
	  | Goto labels -> 
       let n = make_new_node stmt in 
       List.iter (fun label ->
          connect n (AllLabels.find label label_map)) labels; 
       connect start n;
       make_skip_node ()
    | Sugar _ -> raise (Invalid_argument ("Should be desugared at this point"))

  let remove_skip_from_cfg (cfg : cf_graph) = 
  let nodes = get_all_nodes cfg in 
  List.iter (fun node -> 
    if (node.cfgn_id = cfg.cfg_entry.cfgn_id || node.cfgn_id = cfg.cfg_exit.cfgn_id) then ()
    else match node.cfgn_statement with
      | Skip -> 
        List.iter (fun parent -> 
          List.iter (fun child -> 
            connect parent child;
            disconnect parent node;
            disconnect node child;
          ) node.cfgn_children
        ) node.cfgn_parents;     
        
        List.iter (fun parent -> 
          List.iter (fun child -> 
            connect parent child;
            disconnect parent node;
            disconnect node child;
          ) node.cfgn_excep_children
        ) node.cfgn_excep_parents        
      | _ -> ()
  ) nodes

let rec fun_to_cfg (fb : function_block) : cf_graph =
  let cfg = make_graph () in
  let label_map = get_all_labels fb in
  let lastn = List.fold_left (fun prev stmt ->
    stmt_to_cfg stmt label_map fb.func_ctx prev
    ) cfg.cfg_entry fb.func_body in
  lastn.cfgn_children <- (cfg.cfg_exit) :: lastn.cfgn_children;
  cfg.cfg_exit.cfgn_parents <- lastn :: cfg.cfg_exit.cfgn_parents;
  remove_skip_from_cfg cfg;
  cfg
    
let program_to_cfg (all_functions : function_block AllFunctions.t) : cf_graph AllFunctions.t =
  AllFunctions.map fun_to_cfg all_functions
  
let print_cfg (cfgs : cf_graph AllFunctions.t) (filename : string) : unit =
  let d_cfgedge chan dest src =
    Printf.fprintf chan "\t\t%i -> %i\n" src.cfgn_id dest.cfgn_id in
  let d_cfgnode chan (s : cfg_node) =
    Printf.fprintf chan 
      "\t\t%i [label=\"%i: %s\"]\n" 
      s.cfgn_id 
      s.cfgn_id 
      (String.escaped (Pulp_Syntax_Print.string_of_statement (s.cfgn_statement)));
    List.iter (d_cfgedge chan s) s.cfgn_parents; List.iter (d_cfgedge chan s) s.cfgn_excep_parents; in    
  let chan = open_out (filename ^ ".cfg.dot") in
  Printf.fprintf chan "digraph iCFG {\n\tnode [shape=box,  labeljust=l]\n";
  AllFunctions.iter 
    (fun name cfg -> 
      Printf.fprintf chan "\tsubgraph \"cluster_%s\" {\n\t\tlabel=\"%s\"\n" name (String.escaped name);
      List.iter (d_cfgnode chan) (get_all_nodes cfg);
      Printf.fprintf chan  "\t}\n";
    ) 
    cfgs;
  Printf.fprintf chan "}\n";
  close_out chan
  
let mk_cfg prog file = 
  let cfg = program_to_cfg prog in
  print_cfg cfg file;
  cfg