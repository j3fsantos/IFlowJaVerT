open Graphs
open Pulp_Syntax
open Pulp_Procedure
open Simp_Common
open Control_Flow

type annotation = {
  annot_type_info : (variable * type_info) list
}

let string_of_annotation a =
  match a with 
    | None -> ""
    | Some a -> " | " ^ (String.concat ", " (List.map (fun (v, ty) -> v ^ (string_of_type_info ty)) a.annot_type_info))

type annotated_statement = {
  as_stmt : statement; 
  as_annot : annotation option
}

let string_of_annot_stmt s =
  (Pulp_Syntax_Print.string_of_statement s.as_stmt) ^ (string_of_annotation s.as_annot)
  
let string_of_annot_stmts stmts =
  String.concat "\n" (List.map string_of_annot_stmt stmts)

let as_annot_stmt stmt = {as_stmt = stmt; as_annot = None}

let as_annot_stmts stmts = List.map as_annot_stmt stmts

let remove_annot annot_stmt = annot_stmt.as_stmt

let remove_annots annot_stmts = List.map remove_annot annot_stmts

module CFG_BB = AbstractGraph (struct type t = annotated_statement list end) (struct type t = edge_type end)

exception BBInvalid of string

let get_block_label cfg n =
  let stmts = CFG_BB.get_node_data cfg n in
  match stmts with
    | {as_stmt = Label l} :: tail -> l
    | _ -> raise (BBInvalid ("Block does not start with a label" ^ (string_of_annot_stmts stmts)))

let get_block_labels g =
	let label_map = Hashtbl.create 100 in
	  let _ = List.iter (fun n -> 
	    let d = CFG_BB.get_node_data g n in
	    match d with
	      | {as_stmt = Label l} :: tail -> Hashtbl.add label_map l n
	      | _ -> ()
	    ) (CFG_BB.nodes g) in
	  label_map
    
(* Assumption: n1 is unfinished block without goto at the end *)
(* n2 begins with label *)    
let connect_blocks cfg n1 n2 =
  let n2_label = get_block_label cfg n2 in
  
  let stmts = CFG_BB.get_node_data cfg n1 in
  let stmts = List.rev ((as_annot_stmt (Goto n2_label)) :: (List.rev stmts)) in
  CFG_BB.set_node_data cfg n1 stmts;  
  
  CFG_BB.mk_edge cfg n1 n2 Edge_Normal

let copy (input : CFG.graph) : CFG_BB.graph = 
  let g = CFG_BB.mk_graph () in 
  
  let nodetbl = Hashtbl.create 100 in
  
  List.iter (fun n -> 
    let nd = CFG.get_node_data input n in
    let newn = CFG_BB.mk_node g [as_annot_stmt nd] in
    Hashtbl.add nodetbl n newn 
  ) (CFG.nodes input); 
  
  List.iter (fun n ->
    List.iter (
      fun dest ->
        let ed = CFG.get_edge_data input n dest in
        CFG_BB.mk_edge g (Hashtbl.find nodetbl n) (Hashtbl.find nodetbl dest) ed
    ) (CFG.succ input n)
  ) (CFG.nodes input);
  
  g
  
let merge_two_nodes n1 n2 g = 
  let n2data = CFG_BB.get_node_data g n2 in
  let n2succs = CFG_BB.succ g n2 in
  let n2succs_edges_data = List.map (fun n2succ -> (n2succ, CFG_BB.get_edge_data g n2 n2succ)) n2succs in
  CFG_BB.rm_node g n2;
  let n1data = CFG_BB.get_node_data g n1 in
  CFG_BB.set_node_data g n1 (n1data @ n2data);
  List.iter (fun (succ, data) ->
    CFG_BB.mk_edge g n1 succ data
  ) n2succs_edges_data
  

let rec traverse_node (g : CFG_BB.graph) ctx nodedone current =
  if Hashtbl.mem nodedone current then () 
  else begin
	  let succs = CFG_BB.succ g current in
    let continue_traverse () = Hashtbl.add nodedone current (); List.iter (traverse_node g ctx nodedone) succs in
	  begin match succs with
	    | [succ] -> 
        let preds = CFG_BB.pred g succ in
        begin match preds with
          | [pred] -> 
            let stmts = CFG_BB.get_node_data g succ in
            let can_merge = match stmts with
              | [{as_stmt = Label l}] -> l <> ctx.label_return && l <> ctx.label_throw            
              | _ -> true in
            if can_merge then begin merge_two_nodes current succ g; traverse_node g ctx nodedone current end 
            else continue_traverse ()
          | _ -> continue_traverse ()
        end;
	    | _ -> continue_traverse ()
    end
  end
  
let transform_to_basic_blocks (g : CFG_BB.graph) ctx =
  let nodedone = Hashtbl.create 100 in
  match CFG_BB.nodes g with
    | [] -> ()
    | start :: tail -> traverse_node g ctx nodedone start
  
let remove_unreachable (g : CFG_BB.graph) =
  let nodedone = Hashtbl.create 100 in
  let rec traverse_graph current =
    if Hashtbl.mem nodedone current then ()
    else begin Hashtbl.add nodedone current (); List.iter traverse_graph (CFG_BB.succ g current) end
  in
    
  match CFG_BB.nodes g with
    | [] -> ()
    | start :: tail -> traverse_graph start;
      
  List.iter (fun n -> if not (Hashtbl.mem nodedone n) then CFG_BB.rm_node g n) (CFG_BB.nodes g)
  
  
let transform_to_basic_blocks_from_cfg (input : CFG.graph) ctx : CFG_BB.graph =
  let g = copy input in
  transform_to_basic_blocks g ctx;
  g
  
let rec filter_goto_label stmts throwl returnl =
  match stmts with
    | ({ as_stmt = Goto l1 } as as1) :: tail ->
      begin match tail with
        | ({ as_stmt = Label l2 } as as2) :: tail2 -> 
          if (l1 = l2 && throwl <> l1 && returnl <> l1) then filter_goto_label tail2 throwl returnl
          else [as1; as2] @ filter_goto_label tail2 throwl returnl
        | _ -> as1 :: filter_goto_label tail throwl returnl
      end
   | stmt :: tail -> stmt :: (filter_goto_label tail throwl returnl)
   | [] -> []
  
let remove_unnecessary_goto_label (g : CFG_BB.graph) throwl returnl =
  List.iter (fun n ->
    let stmts = CFG_BB.get_node_data g n in
    let filtered_stmts = filter_goto_label stmts throwl returnl in
    CFG_BB.set_node_data g n filtered_stmts
  ) (CFG_BB.nodes g)
  
let is_block_empty stmts =
  match stmts with
    | [{as_stmt = Label l2}; {as_stmt = Goto l1}] -> 
      true, l1, l2
    | _ -> false, "", ""
  
let remove_empty_blocks g =
  let change_if_equal l1 l2 tol =
    if l1 == l2 then tol else l1 in
  
  let change_last_goto stmts newl oldl = 
    let rev = List.rev stmts in
    match rev with
      (* Fix for function calls *)
      | ({as_stmt = Goto l1} as s1) :: tail -> 
        (List.rev tail) @ [{s1 with as_stmt = Goto (change_if_equal l1 oldl newl)}]
      | ({as_stmt = GuardedGoto (e, l1, l2)} as s2) :: tail -> 
        (List.rev tail) @ [{s2 with as_stmt = GuardedGoto (e, (change_if_equal l1 oldl newl), (change_if_equal l2 oldl newl))}]
      | [] ->  raise (BBInvalid "Expected Goto in removing empty blocks. Got empty list of statements")
      | {as_stmt = stmt} :: tail -> raise (BBInvalid ("Expected Goto in removing empty blocks. Got " ^ Pulp_Syntax_Print.string_of_statement stmt)) in
  
  List.iter (fun n ->
    let nd = CFG_BB.get_node_data g n in
    let is_empty, newl, oldl = is_block_empty nd in
    if is_empty then begin
      let succs = CFG_BB.succ g n in
      match succs with
        | [thesucc] -> 
           let preds = CFG_BB.pred g n in
           let sd = CFG_BB.get_edge_data g n thesucc in
           List.iter (fun pred -> 
             let stmts = CFG_BB.get_node_data g pred in
             let new_stmts = change_last_goto stmts newl oldl in
             CFG_BB.set_node_data g pred new_stmts;
             CFG_BB.mk_edge g pred thesucc sd
           ) preds;   
           CFG_BB.rm_node g n;
        | _ -> raise (BBInvalid "Goto should have excatly one successor")
	  end
    else ()
  ) (CFG_BB.nodes g)

let print_cfg_bb (cfgs : CFG_BB.graph AllFunctions.t) (filename : string) : unit =
  let cfg_index = ref 0 in
  let node_name n = 
    "c" ^ (string_of_int (!cfg_index)) ^ "n" ^ (string_of_int (CFG_BB.node_id n)) in
  let d_cfgedge chan dest src =
    Printf.fprintf chan "\t\t%s -> %s\n" (node_name src) (node_name dest) in
  let d_cfgnode chan (cfg : CFG_BB.graph) (n : CFG_BB.node) (nd : annotated_statement list) =
    Printf.fprintf chan 
      "\t\t%s [label=\"%s: %s\"]\n" 
      (node_name n)
      (node_name n)
      (String.escaped (string_of_annot_stmts nd));    
      List.iter (fun dest -> d_cfgedge chan dest n) (CFG_BB.succ cfg n) in
  let chan = open_out (filename ^ ".cfg.dot") in
  Printf.fprintf chan "digraph iCFG {\n\tnode [shape=box,  labeljust=l]\n";
  AllFunctions.iter 
    (fun name cfg -> 
      (*if name = "main" then begin*)
      cfg_index := !cfg_index + 1;
      Printf.fprintf chan "\tsubgraph \"cluster_%s\" {\n\t\tlabel=\"%s\"\n" name (String.escaped name);
      List.iter (fun n -> d_cfgnode chan cfg n (CFG_BB.get_node_data cfg n)) (CFG_BB.nodes cfg);
      Printf.fprintf chan  "\t}\n";
      (*end*)
    ) 
    cfgs;
  Printf.fprintf chan "}\n";
  close_out chan
  
let print_cfg_bb_single cfg filename =
  let all = AllFunctions.add "" cfg AllFunctions.empty in
  print_cfg_bb all filename  
  
let cfg_to_fb cfg return_label throw_label =
  let rec traverse cfg nodedone current =
      if Hashtbl.mem nodedone current then [] 
      else begin
          let stmts = remove_annots (CFG_BB.get_node_data cfg current) in
          let succs = CFG_BB.succ cfg current in
          let normalsuccs, throwsuccs = List.partition (fun succ ->
             match CFG_BB.get_edge_data cfg current succ with
              | Edge_Normal
              | Edge_True
              | Edge_False -> true
              | Edge_Excep -> false
          ) succs in
          Hashtbl.add nodedone current (); 
          (List.filter (fun stmt ->
          match stmt with
            | Label l -> 
              if l = return_label || l = throw_label then false
              else true
            | _ -> true ) stmts) @ 
          (List.flatten (List.map (traverse cfg nodedone) normalsuccs)) @ 
          (List.flatten (List.map (traverse cfg nodedone) throwsuccs))
      end 
  in
  
  let nodedone = Hashtbl.create 100 in
  let stmts = match CFG_BB.nodes cfg with
    | [] -> []
    | start :: tail -> traverse cfg nodedone start in
  stmts  @ [Label return_label; Label throw_label]