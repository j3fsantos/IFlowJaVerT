open JSIL_Syntax
open JSIL_Logic_Utils
open JSIL_Parser
open Symbolic_State
open JSLogic

let js = ref false
let syntax_checks_enabled = ref false;

type global_which_pred_type = (string * int * int, int) Hashtbl.t
type which_pred_type = (int * int, int) Hashtbl.t


(** ----------------------------------------------------
    ----------------------------------------------------
    JSIL Expressionts - AST transformers
    -----------------------------------------------------
*)

let rec jsil_expr_fold 
  (f_ac    : jsil_expr -> 'b -> 'b -> 'a list -> 'a) 
  (f_state : (jsil_expr -> 'b -> 'b) option)
  (state   : 'b) 
  (expr    : jsil_expr) : 'a =

  let new_state = (Option.default (fun _ x -> x) f_state) expr state in
  let fold_e    = jsil_expr_fold f_ac f_state new_state in
  let f_ac      = f_ac expr new_state state in

    match expr with
    | Literal _ | Var _ | RNumSymb _ | RStrSymb _ -> f_ac []
    | BinOp (e1, op, e2)    -> f_ac [ (fold_e e1); (fold_e e2) ]
    | UnOp (op, e)          -> f_ac [ (fold_e e) ]
    | TypeOf e              -> f_ac [ (fold_e e) ]
    | EList es              -> f_ac (List.map fold_e es)
    | LstNth (e1, e2)       -> f_ac [ (fold_e e1); (fold_e e2) ]
    | StrNth (e1, e2)       -> f_ac [ (fold_e e1); (fold_e e2) ]
    | ESet es
    | SetUnion es
    | SetInter es 
    | CList es              -> f_ac (List.map fold_e es)


let rec jsil_expr_map 
  (f_before : jsil_expr  -> jsil_expr * bool) 
  (f_after  : (jsil_expr -> jsil_expr) option)
  (expr    : jsil_expr) : jsil_expr =
  (* Apply the mapping *)
  let map_e   = jsil_expr_map f_before f_after in
  let f_after = Option.default (fun x -> x) f_after in 
  
  let (mapped_expr, recurse) = f_before expr in
  if not recurse then
    mapped_expr
  else ( 
    (* Map recursively to expressions *)
      let mapped_expr = 
        match mapped_expr with
        | Literal _ | Var _ | RNumSymb _ | RStrSymb _  -> mapped_expr
        | BinOp (e1, op, e2)  -> BinOp (map_e e1, op, map_e e2)
        | UnOp (op, e)        -> UnOp (op, map_e e)
        | TypeOf e            -> TypeOf (map_e e)
        | EList es            -> EList (List.map map_e es)
        | LstNth (e1, e2)     -> LstNth (map_e e1, map_e e2)
        | StrNth (e1, e2)     -> StrNth (map_e e1, map_e e2)
        | ESet es             -> ESet  (List.map map_e es)
        | SetUnion es         -> SetUnion  (List.map map_e es)
        | SetInter es         -> SetInter  (List.map map_e es)
        | CList es            -> CList (List.map map_e es) in 
      f_after mapped_expr)



(* Get all the program variables in --e-- *)
let get_expr_pvars (e : jsil_expr) : SS.t =
  let fe_ac e _ _ ac = match e with
    | Var x -> [ x ]
    | _      -> List.concat ac in 
  SS.of_list (jsil_expr_fold fe_ac None None e)



let jsil_expr_substitution (subst : p_substitution) (partial : bool) (e : jsil_expr) : jsil_expr = 

  let find_in_subst (x : string) (x_old : jsil_expr) 
      (make_new_x : unit -> jsil_expr) : jsil_expr = 
    try Hashtbl.find subst x with _ -> 
      if partial then x_old else (
        let new_x = make_new_x () in 
        Hashtbl.replace subst x new_x;
        new_x) in  

  let f_before e = match e with 
    | Var x    -> find_in_subst x e (fun () ->
        let pvar = fresh_pvar () in
        print_debug_petar (Printf.sprintf "Unable to find PVar %s in subst, generating fresh: %s" x pvar); 
        Var (fresh_pvar ())), false 
    | _         -> e, true in 

  jsil_expr_map f_before None e



let conjunct_exprs (expr_list : jsil_expr list) : jsil_expr = 

  let rec loop ac_expr exprs = 
    match exprs with 
    | []                 -> ac_expr 
    | expr :: rest_exprs -> BinOp (expr, And, ac_expr) in 

  match List.rev expr_list with 
  | [  ]               -> Literal (Bool true)
  | [ expr ]           -> expr 
  | expr :: rest_exprs -> loop expr rest_exprs 






(** ----------------------------------------------------
    ----------------------------------------------------
    JSIL Syntax Checks
    -----------------------------------------------------
*)
(** ----------------------------------------------------
    Checking predicate definitions only use program variables they are allowed to
    -----------------------------------------------------
*)
let check_all_pred_pvars
    (predicates : (string, jsil_logic_predicate) Hashtbl.t) : unit =

  let check_pred_pvars
    (pred_name : string)
    (predicate : jsil_logic_predicate) : unit =

    (** Step 1 - Extract all the program variables used in the definition
      * -----------------------------------------------------------------------------------
    *)
    let all_pred_pvars : jsil_var list = List.concat (List.map (fun (_, ass) -> SS.elements (get_asrt_pvars ass)) predicate.definitions) in

    (** Step 2 - Check all predicates
      * -----------------------------------------------------------------------------------
    *)
    let string_of_params = List.map JSIL_Print.string_of_logic_expression predicate.params in
    List.map (fun (pvar : jsil_var) ->
        let valid_pvar = List.mem pvar string_of_params in
        (match valid_pvar || predicate.previously_normalised_pred with
        | true -> ()
        | false -> raise (Failure (Printf.sprintf "Undefined variable %s in the definition of predicate %s." pvar pred_name)))
      ) all_pred_pvars;
    ()

  in
  Hashtbl.iter check_pred_pvars predicates

(** ----------------------------------------------------
    Checking spec definitions only use program variables they're allowed to
    -----------------------------------------------------
*)
let check_specs_pvars
    (procedures : ((string, jsil_ext_procedure) Hashtbl.t)) : unit =

  (** Step 1 - Get the specs for each procedure, and add the return and error variables to the list of allowed variables
    * -----------------------------------------------------------------------------------
  *)
  (* TODO: only allow return and error variables in the postcondition *)
  let ret_err_params proc =
    let new_params_ret = (match proc.lret_var with
        | None -> []
        | Some v -> [v]) in
    match proc.lerror_var with
    | None -> new_params_ret
    | Some v -> v :: new_params_ret
  in

  (* Allow these variables when dealing with JS files as they are used by the internal functions *)
  let js_constants =
    (match !js with
     | true -> JS2JSIL_Constants.js2jsil_spec_vars
     | false -> []) in

  let specs : jsil_spec list = Hashtbl.fold (fun proc_name proc acc ->
      match proc.lspec with
        | None -> acc
        | Some s -> {s with spec_params = (s.spec_params @ (ret_err_params proc) @ js_constants)} :: acc
    ) procedures []
  in

  (** Step 2 - Function to check for any assertion in the spec
    * -----------------------------------------------------------------------------------
  *)
  let check_spec_assertion_pvars
      (spec_name : string)
      (pre : bool) (* true for pre, false for post *)
      (spec_params : jsil_var list)
      (previously_normalised : bool)
      (assertion : jsil_logic_assertion) : unit =

    let msg_construct_type =
      (match pre with
       | true -> "precondition"
       | false -> "postcondition")
    in

    List.map (fun pvar ->
        let valid_pvar = List.mem pvar spec_params in
        (match valid_pvar || previously_normalised with
         | true -> ()
         | false -> raise (Failure (Printf.sprintf "Undefined variable %s in the %s of %s." pvar msg_construct_type spec_name)))
      )
      (SS.elements (get_asrt_pvars assertion)); ()
  in

  (** Step 3 - Run this function on the pre and all the post's of every spec
    * -----------------------------------------------------------------------------------
  *)
  List.map (fun spec ->
      let spec_params = spec.spec_params in
      List.map (fun single_spec ->
          check_spec_assertion_pvars spec.spec_name true spec_params spec.previously_normalised single_spec.pre;
          List.map (fun post ->
              check_spec_assertion_pvars spec.spec_name false spec_params spec.previously_normalised post;
            )
            single_spec.post;
        )
        spec.proc_specs
    )
    specs;
  ()

(** ----------------------------------------------------
    Checking specs correspond directly to procedures
    -----------------------------------------------------
*)
let check_specs_procs_correspond
    (procedures : ((string, jsil_ext_procedure) Hashtbl.t)) : unit =

  Hashtbl.iter (fun _ proc ->
      match proc.lspec with
      | None -> ()
      | Some spec ->

        (** Check the arguments correspond
          * -----------------------------------------------------------------------------------
        *)
        (match (List.length proc.lproc_params) = (List.length spec.spec_params) with
          | true -> ()
          | false -> raise (Failure (Printf.sprintf "The spec and procedure definitions for %s have different number of arguments." proc.lproc_name)));
        (match proc.lproc_params = spec.spec_params with
          | true -> ()
          | false -> raise (Failure (Printf.sprintf "The spec and procedure definitions for %s have different arguments." proc.lproc_name)));
    ) procedures

(** ----------------------------------------------------
    Wrapper function which calls each check
    -----------------------------------------------------
*)
let syntax_checks
    (ext_prog : jsil_ext_program)
    (prog : jsil_program)
    (which_pred : global_which_pred_type) : unit =

  if (!syntax_checks_enabled)
  then (
    print_debug (Printf.sprintf "Running syntax checks:");
    print_debug (Printf.sprintf "Checking predicate definitions only use program variables they are allowed to.");
    check_all_pred_pvars ext_prog.predicates;
    print_debug (Printf.sprintf "Checking spec definitions only use program variables they're allowed to.");
    check_specs_pvars ext_prog.procedures;
    print_debug (Printf.sprintf "Checking specs correspond directly to procedures");
    check_specs_procs_correspond ext_prog.procedures;
  )

(** ----------------------------------------------------
    Checking logical commands only use program variables they are allowed to
    -----------------------------------------------------
*)
(* -------- Check disabled, needs to be rewritten to perform a DFS -------- *)
(*
let check_logic_command_pvars
    (assertion_type : string) (* eg "fold", "unfold", "assert" *)
    (target_name : string)
    (symb_state : symbolic_state)
    (args : jsil_logic_expr list) : unit =

  (** Step 1 - Attempt to look up each argument in the store
    * -----------------------------------------------------------------------------------
  *)
  let args_pvars = List.concat (List.map get_logic_expression_pvars_list args) in
  let (_, store, _, _, _) = symb_state in
  List.map (fun pvar ->
      (match Hashtbl.mem store pvar with
      | true -> ()
      | false -> raise (Failure (Printf.sprintf "Undefined program variable %s when trying to %s %s." pvar assertion_type target_name)))
    )
    (List.concat (List.map get_logic_expression_pvars_list args));
  ()
*)

(** ----------------------------------------------------
    Checking predicates are called with the correct number of arguments
    -----------------------------------------------------
*)
(* -------- Check disabled, needs to be rewritten to perform a DFS -------- *)
(*
let check_pred_arg_count
    (pred_name : string)
    (args : 'a list)
    (params : 'b list) : unit =

  (** Step 1 - Check same number of args and params
    * -----------------------------------------------------------------------------------
  *)
  (match ((List.length args) == (List.length params)) with
  | true -> ()
  | false -> raise (Failure (Printf.sprintf "Incorrect number of arguments to predicate %s." pred_name)))
*)

(** ----------------------------------------------------
    Extracting the jsil variables from a procedure
    -----------------------------------------------------
*)
let get_proc_variables
    (proc : jsil_procedure) : jsil_var list =

  let var_table = Hashtbl.create 1021 in
  let cmds = proc.proc_body in
  let number_of_cmds = Array.length cmds in

  (** Step 1 - Process each command in the procedure individually,
   *  carrying along the variables found so far
   * -----------------------------------------------------------------------------------
   *)
  let rec loop
      (u : int)
      (vars : jsil_var list) : jsil_var list =
    if (u >= number_of_cmds)
    then vars
    else

      (** Step 2 - Process the command at the current index
       * -----------------------------------------------------------------------------------
       *)
      let spec, cmd = cmds.(u) in
      (match cmd with

       (** Step 3 - Pattern match on the command type to extract the variable
        * -----------------------------------------------------------------------------------
        *)
       | SBasic (SAssignment (var, _))
       | SBasic (SLookup (var, _, _))
       | SBasic (SNew var)
       | SBasic (SHasField (var, _, _))
       | SBasic (SGetFields (var, _))
       | SBasic (SArguments var)
       | SCall (var, _, _, _) when (not (Hashtbl.mem var_table var)) ->

         (** Step 4 - Store the variable in the global hashtable and recurse
          * -----------------------------------------------------------------------------------
         *)
         Hashtbl.add var_table var true;
         loop (u+1) (var :: vars)) in

  (** Step 0 - Iterate over each index associated with a command
   * -----------------------------------------------------------------------------------
  *)
  loop 0 []

(** ----------------------------------------------------
    Replacing all labels in the procedure with numbers, and recording the mapping
    -----------------------------------------------------
*)
let desugar_labs
    (lproc : jsil_ext_procedure) : jsil_procedure =

	let no_of_cmds = Array.length lproc.lproc_body in

  (** Step 1 - Map labels to numbers, adding the label to the mapping hashtable
   * -----------------------------------------------------------------------------------
   *)
	let map_labels_to_numbers =
		let mapping = Hashtbl.create no_of_cmds in
		for i = 0 to (no_of_cmds - 1) do
			(match (lproc.lproc_body).(i) with
			  | (_, Some str, _) -> Hashtbl.add mapping str i
				| _ -> ());
		done;
		mapping in

 (** Step 2 - Replace labels with numbers in the procedure commands
   * -----------------------------------------------------------------------------------
   *)
	let convert_to_sjsil mapping =
		let cmds_nolab = Array.map (fun x -> (match x with | (spec, _, cmd) -> (spec, cmd))) lproc.lproc_body in
		let cmds = Array.map (fun x ->
      match x with
      | spec, x -> 
				let x = match x with
						| SLBasic cmd -> SBasic cmd
			      | SLGoto lab -> SGoto (Utils.try_find_with_error mapping lab)
			      | SLGuardedGoto (e, lt, lf) -> SGuardedGoto (e, Utils.try_find_with_error mapping lt, Utils.try_find_with_error mapping lf)
			      | SLCall (x, e, le, ol) -> SCall (x, e, le, match ol with | None -> None | Some lab -> Some (Utils.try_find_with_error mapping lab))
						| SLApply (x, le, ol) -> SApply (x, le, match ol with | None -> None | Some lab -> Some (Utils.try_find_with_error mapping lab))
						| SLPhiAssignment (x, args) -> SPhiAssignment (x, args)
						| SLPsiAssignment (x, args) -> SPsiAssignment (x, args) in
				(spec, x)
			) cmds_nolab in
      cmds,
      (match lproc.lret_label with
       | None -> None
       | Some lab -> Some (Hashtbl.find mapping lab)),
      (match lproc.lerror_label with
       | None -> None
       | Some lab -> Some (Hashtbl.find mapping lab)) in

 (** Step 3 - Return a new procedure, with the components now devoid of labels
   * -----------------------------------------------------------------------------------
   *)
	let mapping = map_labels_to_numbers in
	let b, rl, el = convert_to_sjsil mapping in
	let proc =
		{
			proc_name = lproc.lproc_name;
    	proc_body = b;
    	proc_params = lproc.lproc_params;
			ret_label = rl;
			ret_var = lproc.lret_var;
			error_label = el;
			error_var = lproc.lerror_var;
			spec = lproc.lspec;
		} in
	print_debug_petar (JSIL_Print.string_of_procedure proc);
	proc

(** ----------------------------------------------------
    Prints the current position of the lexbuf
    -----------------------------------------------------
*)
let print_position
    (outx : Format.formatter)
    (lexbuf : Lexing.lexbuf) : unit =
  let pos = lexbuf.lex_curr_p in
  Format.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

type token = [%import: JSIL_Parser.token] [@@deriving show]

(** ----------------------------------------------------
    Initiates the parsing, of the contents in 'lexbuf', from the starting symbol 'start'.
    Terminates if an error occours.
    -----------------------------------------------------
*)
let parse
    start
    (lexbuf : Lexing.lexbuf) (** Can't specify a return type as depends on target *) =

  let module JPMI = JSIL_Parser.MenhirInterpreter in

  let last_token = ref JSIL_Parser.EOF
  in let lexer lexbuf =
       let token = JSIL_Lexer.read lexbuf in
       last_token := token; token
  in

  (** ----------------------------------------------------
      Start the interpreter
      -----------------------------------------------------
  *)
  JPMI.loop_handle
    (fun result -> result)

    (** ----------------------------------------------------
        Terminate if an error occurs
        -----------------------------------------------------
    *)
    (function JPMI.Rejected -> failwith "Parser rejected input"
            | JPMI.HandlingError e ->
              let csn = JPMI.current_state_number e in
              Format.eprintf "%a, last token: %s: %s.@."
                print_position lexbuf
                (show_token !last_token)
                "Error message found";
              raise JSIL_Parser.Error
            | _ -> failwith "Unexpected state in failure handler!"
    )
    (JPMI.lexer_lexbuf_to_supplier lexer lexbuf)
    (start lexbuf.Lexing.lex_curr_p)


(** ----------------------------------------------------
    Open the file given by 'path' and run the parser on its contents.
    Detect previously normalised files.
    -----------------------------------------------------
*)
let ext_program_of_path
    (path : string) : jsil_ext_program =

  print_debug (Printf.sprintf "Creating ext_program_of_path %s" path);

  let extension = List.hd (List.rev (Str.split (Str.regexp "\.") path)) in
  let file_previously_normalised = String.equal "njsil" extension in

  print_debug (Printf.sprintf "%s is previously normalised? %b" path file_previously_normalised);
  JSIL_Syntax.previously_normalised := file_previously_normalised;

  (* Check that the file is of a valid type *)
  (match (file_previously_normalised || (String.equal "jsil" extension)) with
    | true -> ()
    | false -> raise (Failure (Printf.sprintf "Failed to import %s: not a .jsil or .njsil file." path)));

  let inx = open_in path in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = path };
  let prog = parse JSIL_Parser.Incremental.main_target lexbuf in
  close_in inx;

  print_debug (Printf.sprintf "CREATED ext_program_of_path %s" path);
  prog


(** ----------------------------------------------------
    Run the parser on the given string.
    -----------------------------------------------------
*)
let ext_program_of_string
    (str : string) : jsil_ext_program =

  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
	let prog = parse JSIL_Parser.Incremental.main_target lexbuf in
	prog



(** ----------------------------------------------------
    Run the parser on a string of an assertion.
    -----------------------------------------------------
*)
let js_assertion_of_string
    (str : string) : js_logic_assertion =

  print_debug_petar (Printf.sprintf "Parsing the following js assertion: %s" str);
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
  parse JSIL_Parser.Incremental.top_level_js_assertion_target lexbuf




(** ----------------------------------------------------
    Run the parser on a string of a JSIL Expression
    -----------------------------------------------------
*)
let jsil_expr_of_string
    (str : string) : jsil_expr =

	print_debug_petar (Printf.sprintf "Parsing the following jsil expr: %s" str);
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
	parse JSIL_Parser.Incremental.top_level_jsil_expr_target lexbuf


(** ----------------------------------------------------
    Run the parser on a string of a predicate definition.
    -----------------------------------------------------
*)
let lexpr_of_string
    (str : string) : jsil_logic_expr =
  print_debug_petar (Printf.sprintf "Parsing the following jsil logic expr: %s" str);
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
  parse JSIL_Parser.Incremental.top_level_lexpr_target lexbuf



(** ----------------------------------------------------
    Run the parser on a string of a predicate definition.
    -----------------------------------------------------
*)
let js_logic_pred_def_of_string
    (str : string) : JSLogic.js_logic_predicate =

  print_debug_petar (Printf.sprintf "Parsing the following pred def: %s" str);
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
	parse JSIL_Parser.Incremental.js_pred_target lexbuf


(** ----------------------------------------------------
    Run the parser on a string of an only spec
    -----------------------------------------------------
*)
let js_only_spec_from_string
    (str : string) : JSLogic.js_spec =

  print_debug_petar (Printf.sprintf "Parsing the following only spec: %s" str);
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
	parse JSIL_Parser.Incremental.js_only_spec_target lexbuf

(** ----------------------------------------------------
    Run the parser on a string of a list of JS logical commands
    -----------------------------------------------------
*)
let js_logic_commands_of_string
    (str : string) : js_logic_command list =

	print_debug_petar (Printf.sprintf "Parsing the following logic commands: %s" str);
  let lexbuf = Lexing.from_string str in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "" };
	parse JSIL_Parser.Incremental.js_logic_cmds_target lexbuf


(** ----------------------------------------------------
    Add the declarations in 'program_from' to 'program_to'.
    -----------------------------------------------------
*)
let extend_declarations
    (program_to : jsil_ext_program)
    (program_from : jsil_ext_program) : unit =

  (** Step 1 - Extend the predicates
    * -----------------------------------------------------------------------------------
    *)
	Hashtbl.iter
	  (fun pred_name pred ->
		  (if (Hashtbl.mem program_to.predicates pred_name)
		   then print_debug (Printf.sprintf "*** WARNING: Predicate %s already exists.\n" pred_name)
		   else print_debug (Printf.sprintf "*** MESSAGE: Adding predicate %s.\n" pred_name));
		  Hashtbl.add program_to.predicates pred_name pred)
   program_from.predicates;

 (** Step 2 - Extend the procedures, except where a procedure with the same name already exists
   * -----------------------------------------------------------------------------------
   *)
	Hashtbl.iter
		(fun proc_name proc ->
			if (not (Hashtbl.mem program_to.procedures proc_name))
				then (print_debug (Printf.sprintf "*** MESSAGE: Adding onlyspec procedure: %s.\n" proc_name); Hashtbl.add program_to.procedures proc_name proc)
				else (print_debug (Printf.sprintf "*** WARNING: Procedure %s already exists.\n" proc_name)))
		program_from.procedures;
		
  (** Step 3 - Extend the onlyspecs
    * -----------------------------------------------------------------------------------
    *)
   Hashtbl.iter
   	(fun proc_name proc ->
   		if (not (Hashtbl.mem program_to.onlyspecs proc_name))
   			then (print_debug (Printf.sprintf "*** MESSAGE: Adding procedure: %s.\n" proc_name); Hashtbl.add program_to.onlyspecs proc_name proc)
   			else (print_debug (Printf.sprintf "*** WARNING: Procedure %s already exists.\n" proc_name)))
   	program_from.onlyspecs


(** ----------------------------------------------------
  * Load the programs imported in 'program' and add its declarations to 'program' itself.
  * -----------------------------------------------------------------------------------
  *)
let resolve_imports
    (filename : string)
    (program : jsil_ext_program) : unit =

  (* 'added_imports' keeps track of the loaded files *)
  (** Step 1 - Create a hashtable 'added_imports' which keeps track of the loaded files
    * -----------------------------------------------------------------------------------
    *)
	let added_imports = Hashtbl.create 32 in
  Hashtbl.add added_imports filename true;

  (** Step 2 - Extend the program with each of the programs in imports
    * -----------------------------------------------------------------------------------
    *)
	let rec resolve_imports_iter imports =
		(match imports with
		| [] -> ()
		| file :: rest_imports ->
			print_debug_petar (Printf.sprintf "File: %s\n" file);
			if (not (Hashtbl.mem added_imports file))
				then
					(Hashtbl.replace added_imports file true;
					let imported_program = ext_program_of_path file in
					extend_declarations program imported_program;
     resolve_imports_iter (rest_imports @ imported_program.imports))) in

 (** Step 3 - Print debug messages..
   * -----------------------------------------------------------------------------------
   *)
	print_debug_petar (Printf.sprintf "Predicates Program:\n");
	Hashtbl.iter (fun k v -> print_debug_petar (Printf.sprintf "\t%s\n" k)) program.predicates;
	print_debug_petar (Printf.sprintf "Procedures Program:\n");
  Hashtbl.iter (fun k v -> print_debug_petar (Printf.sprintf "\t%s\n" k)) program.procedures;

	resolve_imports_iter program.imports


(** ----------------------------------------------------
  * Converts an extended JSIL program into a set of basic procedures.
  * -----------------------------------------------------------------------------------
*)
let prog_of_ext_prog
    (filename : string)
    (ext_program : jsil_ext_program) : ((string, jsil_procedure) Hashtbl.t * global_which_pred_type) =

	let epreds = ext_program.predicates in
  let eprocs = ext_program.procedures in

  (** Step 1 - Add the declarations from the imported files
    * -----------------------------------------------------------------------------------
    *)
	print_debug_petar (Printf.sprintf "Entering resolve_imports.\n");
	resolve_imports filename ext_program;
  print_debug_petar (Printf.sprintf "Exiting resolve_imports.\n");

  (** Step 2 - Desugar each procedure
   * -----------------------------------------------------------------------------------
   *)
	let prog = Hashtbl.create 101 in
  let global_which_pred = Hashtbl.create 101 in

	Hashtbl.iter
		(fun proc_name ext_proc ->
			print_debug_petar (Printf.sprintf "Going to desugar procedure %s\n" proc_name);

     (** Step 3 - Desugar labels
      * -----------------------------------------------------------------------------------
     *)
    let proc = desugar_labs ext_proc in

    (** Step 4 - Get the succ and pred tables
      * -----------------------------------------------------------------------------------
      *)
		 let succ_table, pred_table = Graph.get_succ_pred proc.proc_body proc.ret_label proc.error_label in
		 print_debug_petar "succ and pred tables fetched.\n";

     (** Step 5 - Compute the which_pred table
       * -----------------------------------------------------------------------------------
     *)
		 let which_pred = Graph.compute_which_preds pred_table in
		 print_debug_petar "which pred table computed\n";

     (** Step 6 - Update the global_which_pred table with the correct indexes
       * -----------------------------------------------------------------------------------
       *)
			Hashtbl.iter
				(fun (prev_cmd, cur_cmd) i ->
					Hashtbl.replace global_which_pred (proc_name, prev_cmd, cur_cmd) i)
				which_pred;

			Hashtbl.replace prog proc_name proc)
	ext_program.procedures;
	prog, global_which_pred


(** ----------------------------------------------------
    Add the which_pred table to the global_which_pred table
    -----------------------------------------------------
*)
let extend_which_pred
    (global_which_pred : global_which_pred_type)
    (proc : jsil_procedure) : unit =

	let succ_table, pred_table = Graph.get_succ_pred proc.proc_body proc.ret_label proc.error_label in
	let which_pred = Graph.compute_which_preds pred_table in
	let proc_name = proc.proc_name in
	Hashtbl.iter
		(fun (prev_cmd, cur_cmd) i ->
			Hashtbl.replace global_which_pred (proc_name, prev_cmd, cur_cmd) i)
		which_pred


(** ----------------------------------------------------
    Parse a line_numbers file. 
    Proc: proc_name 
    (0, 0)
    ...
    -----------------------------------------------------
*)
let parse_line_numbers (ln_str : string) : (string * int, int * bool) Hashtbl.t = 
  
  let strs            = Str.split (Str.regexp_string "Proc: ") ln_str in
  let line_info       = Hashtbl.create big_tbl_size in 
  List.iter (fun str -> 
    let memory         = Hashtbl.create small_tbl_size in 
    let index          = String.index str '\n' in 
    let proc_name      = String.sub str 0 index in 
    let proc_line_info = String.sub str (index+1) ((String.length str) - (index+1))  in 
    let lines          = Str.split (Str.regexp_string "\n") proc_line_info in 
    List.iter 
      (fun line -> Scanf.sscanf line "(%d, %d)" 
        (fun x y -> 
            if (Hashtbl.mem memory y)
              then Hashtbl.replace line_info (proc_name, x) (y, false)
              else (
                Hashtbl.replace memory y true; 
                Hashtbl.replace line_info (proc_name, x) (y, true) 
              )
        )) lines;  
  ) strs; 

  line_info 




