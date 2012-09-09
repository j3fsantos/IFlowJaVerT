open Batteries_uni
open Xml
open Syntax
open List
open Utils

exception Parser_No_Program
exception Parser_Xml_To_String
exception Parser_Xml_To_Var
exception Parser_Unknown_Tag of (string * int)
exception Parser_PCData
exception Parser_ObjectList
exception JS_To_XML_parser_failure
exception OnlyIntegersAreImplemented
exception Parser_Name_Element
exception Parser_Param_List
exception Unknown_Annotation of string
exception InvalidArgument
exception XmlParserException
exception Unknown_Dec_Inc_Position
exception Parser_Xml_To_Label_Name
exception More_Than_One_Finally

let get_attr attrs attr_name =
  let offset_list = List.filter (fun (name, value) -> name = attr_name) attrs in
  let (name, value) = List.hd offset_list in
  value

let get_offset attrs : int =
  int_of_string (get_attr attrs "pos")
  
let get_value attrs : string =
  get_attr attrs "value"
  
let get_label_name xml : string =
  match xml with
    | Element ("LABEL_NAME", attrs, []) -> get_attr attrs "name"
    | _ -> raise Parser_Xml_To_Label_Name
  
let string_element xml : string =
  match xml with
    | Element ("STRING", attrs, []) -> get_value attrs
    | _ -> raise Parser_Xml_To_String

let name_element xml : string =
  match xml with
    | Element ("NAME", attrs, _) -> get_value attrs
    | _ -> raise Parser_Name_Element

let rec xml_to_vars xml : string list = 
  match xml with
    | Element ("PARAM_LIST", _, childs) -> map name_element childs
    | _ -> raise Parser_Param_List

let remove_annotation_elements children =
  filter (fun child -> 
    match child with
      | Element ("ANNOTATION", _, _) -> false
      | _ -> true
  ) children
  
let get_annot attrs : annotation =
  let atype = get_attr attrs "type" in
  let f = get_attr attrs "formula" in
  let f = unescape_html f in
  match atype with
    | "requires" -> {atype = Requires; aformula = f}
    | "ensures" -> {atype = Ensures; aformula = f}
    | "invariant" -> {atype = Invariant; aformula = f}
    | "codename" -> {atype = Codename; aformula = f}
    | "preddefn" -> {atype = PredDefn; aformula = f}
    | annot -> raise (Unknown_Annotation annot)


type dec_inc_pos =
  | DI_PRE
  | DI_POST

let get_dec_inc_pos attrs : dec_inc_pos = 
  let pos = get_attr attrs "decpos" in
  match pos with
    | "pre" -> DI_PRE
    | "post" -> DI_POST
    | _ -> raise Unknown_Dec_Inc_Position
 
let rec get_function_spec_inner (f : xml) = 
  match f with
    | Element ("FUNCTION", _, children) -> 
      let not_block = filter (fun child -> 
        match child with
          | Element ("BLOCK", _, _) -> false
          | _ -> true
      ) children in
      flat_map get_function_spec_inner not_block
    | Element ("ANNOTATION", attrs, []) -> 
      let annot = get_annot attrs in
      if is_invariant_annot annot then [] else [annot]
    | Element (_, _, children) -> flat_map get_function_spec_inner children
    | _ -> []
 
let get_function_spec (f : xml) =
  match f with
    | Element ("FUNCTION", _, children)
    | Element ("SCRIPT", _, children) ->
      flat_map (fun child -> get_function_spec_inner child) children
    | _ -> raise InvalidArgument

let rec get_invariant_inner (w : xml) =
  match w with 
    | Element ("WHILE", _, _) -> []
    | Element ("FOR", _, _) -> []
    | Element ("DO", _, _) -> []
    | Element ("ANNOTATION", attrs, []) -> 
      let annot = get_annot attrs in
      if is_invariant_annot annot then [annot] else []
    | Element (_, _, children) -> flat_map (fun child -> get_invariant_inner child) children
    | PCData _ -> []

let rec get_invariant (w : xml) =
  match w with
    | Element ("WHILE", _, children) ->
      flat_map (fun child -> get_invariant_inner child) children
    | Element ("FOR", _, children) ->
      flat_map (fun child -> get_invariant_inner child) children
    | Element ("DO", _, children) ->
      flat_map (fun child -> get_invariant_inner child) children
    | _ -> raise InvalidArgument
  
let rec xml_to_exp xml : exp =
  match xml with
    (*Element (tag name, attributes, children )*)
    | Element ("SCRIPT", _, children) -> 
      let stmts = map xml_to_exp children in
      begin
      match stmts with
        | [] -> raise Parser_No_Program
        | stmts -> 
          let last = List.last stmts in
          let stmts = List.take (List.length stmts - 1) stmts in
          let program = fold_right (fun s1 s2 -> (mk_exp (Seq (s1,s2)) s1.offset)) stmts last in
          let program_spec = get_function_spec xml in
          mk_exp_with_annot program.stx program.offset (program.exp_annot @ program_spec)
      end
    | Element ("EXPR_RESULT", _, [child]) -> xml_to_exp child
    | Element ("ASSIGN", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [child1; child2] -> mk_exp (Assign (xml_to_exp child1, xml_to_exp child2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("ASSIGN", (get_offset attrs))) 
      end 
    | Element ("NAME", attrs, _) -> mk_exp (Var (get_value attrs)) (get_offset attrs)
    | Element ("NULL", attrs, _) -> mk_exp Null (get_offset attrs)
    | Element ("FUNCTION", attrs, children) ->
      begin match (remove_annotation_elements children) with
        | [name; params; block] ->
		      let fn_name = name_element name in
		      let fn_params = xml_to_vars params in
		      let fn_body = xml_to_exp block in
		      let fn_spec = get_function_spec xml in
		      if (fn_name = "") then mk_exp_with_annot (AnnonymousFun (fn_params,fn_body)) (get_offset attrs) fn_spec
		      else mk_exp_with_annot (NamedFun (fn_name,fn_params,fn_body)) (get_offset attrs) fn_spec
        | _ -> raise (Parser_Unknown_Tag ("FUNCTION", (get_offset attrs))) 
      end
    | Element ("BLOCK", _, children) ->  
      let stmts = map xml_to_exp children in
      begin
      match stmts with
        | [] -> mk_exp Skip 0
        | stmts -> 
          let last = List.last stmts in
          let stmts = List.take (List.length stmts - 1) stmts in
          fold_right (fun s1 s2 -> (mk_exp (Seq (s1,s2)) s1.offset)) stmts last
      end
    | Element ("VAR", attrs, children) -> 
      let offset = get_offset attrs in
      begin match (remove_annotation_elements children) with
        | [] -> raise (Parser_Unknown_Tag ("VAR", offset))
        | children ->
          let last = var_declaration (List.last children) offset in
          let children = List.take (List.length children - 1) children in
          fold_right (fun s1 s2 -> (
            let s1 = var_declaration s1 offset in
            mk_exp (Seq (s1, s2)) (s1.offset))
          ) children last
      end 
    | Element ("CALL", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | (child1 :: children) -> mk_exp (Call (xml_to_exp child1, (map xml_to_exp children))) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("CALL", (get_offset attrs))) 
      end  
    | Element ("NEW", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | (child1 :: children) -> mk_exp (New (xml_to_exp child1, (map xml_to_exp children))) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("NEW", (get_offset attrs))) 
      end
    | Element ("NUMBER", attrs, _) -> 
      let n_float = float_of_string (get_value attrs) in
      mk_exp (Num n_float) (get_offset attrs)
    | Element ("OBJECTLIT", attrs, objl) ->
      let l = map (fun obj -> 
        match obj with
        | Element ("STRING", attrs, [e]) -> (get_value attrs, xml_to_exp e) 
        | _ -> raise Parser_ObjectList
      ) objl
      in (mk_exp (Obj l) (get_offset attrs))
    | Element ("WITH", attrs, children) ->
      begin match (remove_annotation_elements children) with
        | [obj; block] -> mk_exp (With (xml_to_exp obj, xml_to_exp block)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("WITH", (get_offset attrs))) 
      end 
    | Element ("EMPTY", attrs, _) -> mk_exp Skip (get_offset attrs)
    | Element ("IF", attrs, [condition; t_block]) ->
      let offset = get_offset attrs in
      mk_exp (If (xml_to_exp condition, xml_to_exp t_block, mk_exp Skip offset)) offset
    | Element ("HOOK", attrs, [condition; t_block; f_block])
    | Element ("IF", attrs, [condition; t_block; f_block]) ->
      mk_exp (If (xml_to_exp condition, xml_to_exp t_block, xml_to_exp f_block)) (get_offset attrs)
    | Element ("EQ", attrs, children) -> parse_comparison_op Equal attrs children "EQ"
    | Element ("NE", attrs, children) -> parse_comparison_op NotEqual attrs children "NE"
    | Element ("SHEQ", attrs, children) -> parse_comparison_op TripleEqual attrs children "SHEQ"
    | Element ("SHNE", attrs, children) -> parse_comparison_op NotTripleEqual attrs children "SHNE"
    | Element ("LT", attrs, children) -> parse_comparison_op Lt attrs children "LT"
    | Element ("LE", attrs, children) -> parse_comparison_op Le attrs children "LE"
    | Element ("GT", attrs, children) -> parse_comparison_op Gt attrs children "GT"
    | Element ("GE", attrs, children) -> parse_comparison_op Ge attrs children "GE"
    | Element ("IN", attrs, children) -> parse_comparison_op In attrs children "IN"
    | Element ("INSTANCEOF", attrs, children) -> parse_comparison_op InstanceOf attrs children "INSTANCEOF"
    | Element ("ADD", attrs, children) -> parse_arith_op Plus attrs children "ADD"
    | Element ("SUB", attrs, children) -> parse_arith_op Minus attrs children "SUB"
    | Element ("MUL", attrs, children) -> parse_arith_op Times attrs children "MUL"
    | Element ("DIV", attrs, children) -> parse_arith_op Div attrs children "DIV"
    | Element ("MOD", attrs, children) -> parse_arith_op Mod attrs children "MOD"
    | Element ("URSH", attrs, children) -> parse_arith_op Ursh attrs children "URSH" 
    | Element ("LSH", attrs, children) -> parse_arith_op Lsh attrs children "LSH" 
    | Element ("RSH", attrs, children) -> parse_arith_op Rsh attrs children "RSH"
    | Element ("BITAND", attrs, children) -> parse_arith_op Bitand attrs children "BITAND"
    | Element ("BITOR", attrs, children) -> parse_arith_op Bitor attrs children "BITOR"
    | Element ("BITXOR", attrs, children) -> parse_arith_op Bitxor attrs children "BITXOR"
    | Element ("AND", attrs, children) -> parse_bool_op And attrs children "AND"
    | Element ("OR", attrs, children) -> parse_bool_op Or attrs children "OR"
    | Element ("COMMA", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [child1; child2] -> mk_exp (Comma (xml_to_exp child1, xml_to_exp child2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("COMMA", (get_offset attrs))) 
      end 
    | Element ("THROW", attrs, children) ->
      begin match (remove_annotation_elements children) with
        | [e] -> mk_exp (Throw (xml_to_exp e)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("THROW", (get_offset attrs))) 
      end
    | Element ("WHILE", attrs, [condition; block]) ->
      let invariant = get_invariant xml in
      mk_exp_with_annot (While (xml_to_exp condition, xml_to_exp block)) (get_offset attrs) invariant
    | Element ("GETPROP", attrs, children) ->
      begin match (remove_annotation_elements children) with
        | [child1; child2] -> mk_exp (Access (xml_to_exp child1, string_element child2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("GETPROP", (get_offset attrs))) 
      end 
    | Element ("STRING", attrs, _) -> mk_exp (String (string_element xml)) (get_offset attrs)
    | Element ("TRUE", attrs, _) -> mk_exp (Bool true) (get_offset attrs)
    | Element ("FALSE", attrs, _) -> mk_exp (Bool false) (get_offset attrs)
    | Element ("THIS", attrs, _) -> mk_exp This (get_offset attrs)
    | Element ("RETURN", attrs, []) -> mk_exp (Return None) (get_offset attrs) 
    | Element ("RETURN", attrs, [child]) -> mk_exp (Return (Some (xml_to_exp child))) (get_offset attrs)
    | Element ("REGEXP", attrs, [pattern]) -> mk_exp (RegExp ((string_element pattern), "")) (get_offset attrs)
    | Element ("REGEXP", attrs, [pattern; flags]) -> 
      mk_exp (RegExp ((string_element pattern), (string_element flags))) (get_offset attrs)
    | Element ("NOT", attrs, children) -> parse_unary_op Not attrs children "NOT"
    | Element ("TYPEOF", attrs, children) -> parse_unary_op TypeOf attrs children "TYPEOF"
    | Element ("POS", attrs, children) -> parse_unary_op Positive attrs children "POS"
    | Element ("NEG", attrs, children) -> parse_unary_op Negative attrs children "NEG"
    | Element ("BITNOT", attrs, children) -> parse_unary_op Bitnot attrs children "BITNOT"
    | Element ("VOID", attrs, children) -> parse_unary_op Void attrs children "VOID" 
    | Element ("ASSIGN_ADD", attrs, children) -> parse_assign_op Plus attrs children "ASSIGN_ADD"
    | Element ("ASSIGN_SUB", attrs, children) -> parse_assign_op Minus attrs children "ASSIGN_SUB"
    | Element ("ASSIGN_MUL", attrs, children) -> parse_assign_op Times attrs children "ASSIGN_MUL"
    | Element ("ASSIGN_DIV", attrs, children) -> parse_assign_op Div attrs children "ASSIGN_DIV"
    | Element ("ASSIGN_MOD", attrs, children) -> parse_assign_op Mod attrs children "ASSIGN_MOD"
    | Element ("ASSIGN_URSH", attrs, children) -> parse_assign_op Ursh attrs children "ASSIGN_URSH"
    | Element ("ASSIGN_LSH", attrs, children) -> parse_assign_op Lsh attrs children "ASSIGN_LSH"
    | Element ("ASSIGN_RSH", attrs, children) -> parse_assign_op Rsh attrs children "ASSIGN_RSH"
    | Element ("ASSIGN_BITAND", attrs, children) -> parse_assign_op Bitand attrs children "ASSIGN_BITAND"
    | Element ("ASSIGN_BITXOR", attrs, children) -> parse_assign_op Bitxor attrs children "ASSIGN_BITXOR"
    | Element ("ASSIGN_BITOR", attrs, children) -> parse_assign_op Bitor attrs children "ASSIGN_BITOR" 
    | Element ("DEC", attrs, children) -> 
      begin match (get_dec_inc_pos attrs) with
        | DI_PRE -> parse_unary_op Pre_Decr attrs children "DEC"
        | DI_POST -> parse_unary_op Post_Decr attrs children "DEC"
      end
    | Element ("INC", attrs, children) -> 
      begin match (get_dec_inc_pos attrs) with
        | DI_PRE -> parse_unary_op Pre_Incr attrs children "INC"
        | DI_POST -> parse_unary_op Post_Incr attrs children "INC"
      end
    | Element ("GETELEM", attrs, [child1; child2]) -> mk_exp (CAccess (xml_to_exp child1, xml_to_exp child2)) (get_offset attrs)
    | Element ("ARRAYLIT", attrs, children) ->
      convert_arraylist_to_object attrs children
    | Element ("FOR", attrs, [init; condition; incr; exp]) ->
      let invariant = get_invariant xml in
      let body = mk_exp (Seq (xml_to_exp exp, xml_to_exp incr)) (get_offset attrs) in
      let whileloop = mk_exp_with_annot (While (xml_to_exp condition, body)) (get_offset attrs) invariant in
      mk_exp (Seq (xml_to_exp init, whileloop)) (get_offset attrs)
    | Element ("DO", attrs, [body; condition]) -> 
      let offset = get_offset attrs in
      let invariant = get_invariant xml in
      let body = xml_to_exp body in
      let whileloop = mk_exp_with_annot (While (xml_to_exp condition, body)) offset invariant in
      mk_exp (Seq (body, whileloop)) offset
    | Element ("FOR", attrs, [var; obj; exp]) ->
      mk_exp (ForIn (xml_to_exp var, xml_to_exp obj, xml_to_exp exp)) (get_offset attrs)
    | Element ("DELPROP", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [child] -> mk_exp (Delete (xml_to_exp child)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("DELPROP", (get_offset attrs))) 
      end 
    | Element ("LABEL", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [lname; child] -> mk_exp (Label (get_label_name lname, xml_to_exp child)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("LABEL", (get_offset attrs))) 
      end 
    | Element ("CONTINUE", attrs, children) -> 
      let offset = get_offset attrs in
      begin match (remove_annotation_elements children) with
        | [] -> mk_exp (Continue None) offset
        | [label] -> mk_exp (Continue (Some (get_label_name label))) offset 
        | _ -> raise (Parser_Unknown_Tag ("CONTINUE", offset)) 
      end 
    | Element ("BREAK", attrs, children) -> 
      let offset = get_offset attrs in
      begin match (remove_annotation_elements children) with
        | [] -> mk_exp (Break None) offset
        | [label] -> mk_exp (Break (Some (get_label_name label))) offset 
        | _ -> raise (Parser_Unknown_Tag ("BREAK", offset)) 
      end 
    | Element ("TRY", attrs, children) ->
      let offset = get_offset attrs in
      begin match remove_annotation_elements children with
        | (child1 :: children) ->
          let catch, finally = get_catch_finally children offset in mk_exp (Try (xml_to_exp child1, catch, finally)) offset
        | _ -> raise (Parser_Unknown_Tag ("TRY", offset))
      end  
    | Element ("SWITCH", attrs, children) -> 
      let offset = get_offset attrs in
      begin match (remove_annotation_elements children) with
         | (child1 :: cases) ->
           let cases = remove_annotation_elements cases in
           let cases = map (fun c -> parse_case c offset) cases in
           mk_exp (Switch (xml_to_exp child1, cases)) offset
         | _ -> raise (Parser_Unknown_Tag ("SWITCH", offset))
      end
    (* TODO *)  
    | Element ("DEBUGGER", attrs, []) -> raise NotImplemented 
    | Element ("GETTER_DEF", attrs, children) -> raise NotImplemented
    | Element ("SETTER_DEF", attrs, children) -> raise NotImplemented
    | Element ("STRING_KEY", attrs, children) -> raise NotImplemented
    | Element (tag_name, attrs, _) -> raise (Parser_Unknown_Tag (tag_name, (get_offset attrs)))
    | PCData _ -> raise Parser_PCData
and 
var_declaration vd offset = 
  match vd with
    | Element ("NAME", attrs, []) -> 
      mk_exp (VarDec (get_value attrs)) (get_offset attrs) 
    | Element ("NAME", attrs, [child]) -> 
      let variable = get_value attrs in
      let offset = get_offset attrs in
      let vardec = mk_exp (VarDec variable) offset in
      let vardec_exp = mk_exp (Assign (mk_exp (Var variable) offset, (xml_to_exp child))) offset in
      mk_exp (Seq (mk_exp (Seq (vardec, vardec_exp)) offset, mk_exp Undefined offset)) offset
    | _ -> raise (Parser_Unknown_Tag ("VAR", offset))
and
(* TODO: Does this work only with well-behaved Array constructor and without elisions? *)
(* Closure compiler does not give the last elided element -- we do not need to worry about it *)
convert_arraylist_to_object attrs children =
  let l = mapi (fun index child -> 
    match child with
      | Element ("EMPTY", attrs, _) -> (string_of_int index, (mk_exp Undefined (get_offset attrs)))
      | _ -> (string_of_int index, xml_to_exp child)
  ) children in
  let l = l @ ["length", mk_exp (Num (float_of_int (List.length l))) 0] in
  mk_exp (Obj l) (get_offset attrs)
and 
parse_unary_op uop attrs children uops =
  begin match (remove_annotation_elements children) with
    | [child] -> mk_exp (Unary_op (uop, xml_to_exp child)) (get_offset attrs)
    | _ -> raise (Parser_Unknown_Tag (uops, get_offset attrs)) 
  end 
and
parse_binary_op bop attrs children tag =  
  begin match (remove_annotation_elements children) with
    | [child1; child2] -> mk_exp (BinOp (xml_to_exp child1, bop, xml_to_exp child2)) (get_offset attrs)
    | _ -> raise (Parser_Unknown_Tag (tag, get_offset attrs)) 
  end
and
parse_comparison_op op attrs children tag =
  parse_binary_op (Comparison op) attrs children tag
and
parse_arith_op op attrs children tag =
  parse_binary_op (Arith op) attrs children tag
and
parse_bool_op op attrs children tag =
  parse_binary_op (Boolean op) attrs children tag
and parse_assign_op op attrs children tag =
   begin match (remove_annotation_elements children) with
     | [child1; child2] -> mk_exp (AssignOp (xml_to_exp child1, op, xml_to_exp child2)) (get_offset attrs)
     | _ -> raise (Parser_Unknown_Tag (tag, get_offset attrs)) 
   end
and parse_catch_element catch offset =
  match catch with
      | Element ("CATCH", attrs, children) -> 
        begin match (remove_annotation_elements children) with
          | [name; exp] -> (name_element name, xml_to_exp exp)
          | _ -> raise (Parser_Unknown_Tag ("CATCH", offset))
        end
      | _ -> raise (Parser_Unknown_Tag ("CATCH", offset))
and get_catch_finally children offset =
  begin match children with
    | [catch_block; finally_block] ->
      let catch = match catch_block with
        | Element ("BLOCK", _, children) -> 
          begin match (remove_annotation_elements children) with 
            | [child] -> Some (parse_catch_element child offset)
            | [] -> None
            | _ -> raise (Parser_Unknown_Tag ("TRY", offset))
          end
        | _ -> raise (Parser_Unknown_Tag ("TRY", offset))
      in catch, Some (xml_to_exp finally_block)
    | [catch_block] ->
      begin match catch_block with
        | Element ("BLOCK", _, children) -> 
          begin match (remove_annotation_elements children) with 
            | [child] -> Some (parse_catch_element child offset), None
            | _ -> raise (Parser_Unknown_Tag ("TRY", offset))
          end
        | _ -> raise (Parser_Unknown_Tag ("TRY", offset))
      end 
    | _ -> raise (Parser_Unknown_Tag ("TRY", offset))
  end
and parse_case child offset =
  begin match child with
    | Element ("CASE", attrs, children) ->
      begin match (remove_annotation_elements children) with
        | [exp; block] -> Case (xml_to_exp exp), xml_to_exp block
        | _ -> raise (Parser_Unknown_Tag ("CASE", get_offset attrs))
      end
    | Element ("DEFAULT_CASE", attrs, children) ->
      begin match (remove_annotation_elements children) with
        | [block] -> DefaultCase, xml_to_exp block
        | _ -> raise (Parser_Unknown_Tag ("DEFAULT_CASE", get_offset attrs))
      end
    | _ -> raise (Parser_Unknown_Tag ("SWITCH", offset))
  end
     
let js_to_xml (filename : string) : string =
  match Unix.system ("java -jar " ^ !Config.js_to_xml_parser ^ " " ^ (Filename.quote filename)) with
    | Unix.WEXITED _ -> String.sub filename 0 (String.length filename - 3) ^ ".xml"
    | _ -> raise JS_To_XML_parser_failure
