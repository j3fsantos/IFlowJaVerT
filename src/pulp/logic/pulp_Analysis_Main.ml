open State_Graph

type analysis_type =
  | SymbolicExec
  | BiAbduct

let analysis_type_map = ["symexec", SymbolicExec; 
                         "biabduct", BiAbduct]

let file = ref ""
let analysis_op = ref SymbolicExec
   
let parse_flags () =
  let usage_msg="Usage: [-s <strategy>] [-p <precondition>] -f <file_name>" in
  Arg.parse
    ["-f", 
     Arg.String(fun f -> file := f), 
    "JavaScript file name";
    
     "-s", 
     Arg.String(fun s -> 
       if (List.mem_assoc s analysis_type_map) 
         then analysis_op := List.assoc s analysis_type_map
         else Format.eprintf "WARNING: Ignored strategy %s.@." s
     ), 
     "The symbolic execution strategy. Choose one of: "^ (String.concat ", " (List.map (fun (s, _) -> s) analysis_type_map))]
  (fun s -> Format.eprintf "WARNING: Ignored argument %s.@." s)
  usage_msg
  
let initialize () =
  let graph_elements = Sys.getcwd () ^ Filename.dir_sep ^ "all_elements.js" in
  Graph.clear_all_elements();
  if Sys.file_exists graph_elements then
    Sys.remove graph_elements;
  Config.apply_config ();
  Corestar_frontend.initialize ()
  
let analyse_function current_fun all_funcs =
    match (!analysis_op) with
      | SymbolicExec -> Pulp_Sym_Exec.execute_all current_fun all_funcs
      | BiAbduct -> Pulp_Abduct.execute current_fun all_funcs

let main () = 
   parse_flags ();   
   initialize ();
   
   let expression_map = Translate.translate_exp !file Pulp_Translate.IVL_goto in  
   let expression_map = Simp_Main.simplify expression_map in 
     
   Pulp_Syntax.AllFunctions.iter (fun fid f -> ignore (analyse_function f expression_map)) expression_map
      
let _ = main ()