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

let get_attr attrs attr_name =
  let offset_list = List.filter (fun (name, value) -> name = attr_name) attrs in
  let (name, value) = List.hd offset_list in
  value

let get_offset attrs : int =
  int_of_string (get_attr attrs "pos")
  
let get_value attrs : string =
  get_attr attrs "value"
  
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
    | Element ("ANNOTATION", attrs, []) -> 
      let annot = get_annot attrs in
      if is_invariant_annot annot then [annot] else []
    | Element (_, _, children) -> flat_map (fun child -> get_invariant_inner child) children
    | _ -> []

let rec get_invariant (w : xml) =
  match w with
    | Element ("WHILE", _, children) ->
      flat_map (fun child -> get_invariant_inner child) children
    | Element ("FOR", _, children) ->
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
          mk_exp_with_annot program.stx program.offset program_spec
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
    | Element ("EQ", attrs, children) -> parse_binary_op Equal attrs children "EQ"
    | Element ("SHEQ", attrs, children) -> parse_binary_op TripleEqual attrs children "SHEQ"
    | Element ("SHNE", attrs, children) -> parse_binary_op NotTripleEqual attrs children "SHNE"
    | Element ("LT", attrs, children) -> parse_binary_op Lt attrs children "LT"
    | Element ("LE", attrs, children) -> parse_binary_op Le attrs children "LE"
    | Element ("GE", attrs, children) -> parse_binary_op Ge attrs children "GE"
    | Element ("INSTANCEOF", attrs, children) -> parse_binary_op InstanceOf attrs children "INSTANCEOF"
    | Element ("ADD", attrs, children) -> parse_binary_op Plus attrs children "ADD"
    | Element ("SUB", attrs, children) -> parse_binary_op Minus attrs children "SUB"
    | Element ("AND", attrs, children) -> parse_binary_op And attrs children "AND"
    | Element ("OR", attrs, children) -> parse_binary_op Or attrs children "OR"
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
    | Element ("RETURN", attrs, [child]) -> mk_exp (Return (xml_to_exp child)) (get_offset attrs)
    | Element ("REGEXP", attrs, [pattern]) -> mk_exp (RegExp ((string_element pattern), "")) (get_offset attrs)
    | Element ("REGEXP", attrs, [pattern; flags]) -> 
      mk_exp (RegExp ((string_element pattern), (string_element flags))) (get_offset attrs)
    | Element ("NOT", attrs, children) -> parse_unary_op Not attrs children "NOT"
    | Element ("TYPEOF", attrs, children) -> parse_unary_op TypeOf attrs children "TYPEOF"
    | Element ("POS", attrs, children) -> parse_unary_op Positive attrs children "POS"
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
    | Element ("FOR", attrs, [var; obj; exp]) ->
      mk_exp (ForIn (xml_to_exp var, xml_to_exp obj, xml_to_exp exp)) (get_offset attrs)
    (* TODO *)  
    | Element ("NEG", attrs, [child]) -> raise NotImplemented
    | Element ("CONTINUE", attrs, []) -> raise NotImplemented
    | Element ("NE", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("RETURN", attrs, []) -> raise NotImplemented
    | Element ("BREAK", attrs, []) -> raise NotImplemented
    | Element ("GT", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("TRY", attrs, [trychild; catchchild]) -> raise NotImplemented
    | Element ("CATCH", attrs, [name; block]) -> raise NotImplemented
    | Element ("DEBUGGER", attrs, []) -> raise NotImplemented
    | Element ("TRY", attrs, [trychild; catchchild; finally]) -> raise NotImplemented
    | Element ("IN", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("COMMA", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("DELPROP", attrs, [child]) -> raise NotImplemented
    | Element ("ASSIGN_ADD", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("ASSIGN_SUB", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("ASSIGN_MUL", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("ASSIGN_DIV", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("ASSIGN_MOD", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("ASSIGN_URSH", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("ASSIGN_LSH", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("ASSIGN_RSH", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("ASSIGN_BITAND", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("ASSIGN_BITXOR", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("ASSIGN_BITOR", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("MUL", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("DIV", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("MOD", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("URSH", attrs, [child1; child2]) -> raise NotImplemented 
    | Element ("LSH", attrs, [child1; child2]) -> raise NotImplemented 
    | Element ("RSH", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("BITNOT", attrs, [child]) -> raise NotImplemented
    | Element ("BITAND", attrs, [child1; child2]) -> raise NotImplemented 
    | Element ("BITOR", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("BITXOR", attrs, [child1; child2]) -> raise NotImplemented 
    | Element ("DO", attrs, [child1; child2]) -> raise NotImplemented
    | Element ("SWITCH", attrs, children) -> raise NotImplemented 
    | Element ("CASE", attrs, children) -> raise NotImplemented
    | Element ("DEFAULT_CASE", attrs, [child]) -> raise NotImplemented
    | Element ("GETTER_DEF", attrs, children) -> raise NotImplemented
    | Element ("SETTER_DEF", attrs, children) -> raise NotImplemented
    | Element ("LABEL", attrs, children) -> raise NotImplemented
    | Element ("LABEL_NAME", attrs, children) -> raise NotImplemented
    | Element ("STRING_KEY", attrs, children) -> raise NotImplemented
    | Element ("VOID", attrs, children) -> raise NotImplemented 
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
parse_binary_op bop attrs children bops =  
  begin match (remove_annotation_elements children) with
    | [child1; child2] -> mk_exp (BinOp (xml_to_exp child1, bop, xml_to_exp child2)) (get_offset attrs)
    | _ -> raise (Parser_Unknown_Tag (bops, get_offset attrs)) 
  end

let js_to_xml (filename : string) : string =
  match Unix.system ("java -jar " ^ !Config.js_to_xml_parser ^ " " ^ (Filename.quote filename)) with
    | Unix.WEXITED _ -> String.sub filename 0 (String.length filename - 3) ^ ".xml"
    | _ -> raise JS_To_XML_parser_failure
