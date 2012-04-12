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
    | annot -> raise (Unknown_Annotation annot)

let rec get_function_spec_inner (f : xml) = 
  match f with
    | Element ("FUNCTION", _, _) -> []
    | Element ("ANNOTATION", attrs, []) -> 
      let annot = get_annot attrs in
      if is_invariant_annot annot then [] else [annot]
    | Element (_, _, children) -> flat_map (fun child -> get_function_spec_inner child) children
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
    | Element ("ANNOTATION", attrs, []) -> 
      let annot = get_annot attrs in
      if is_invariant_annot annot then [annot] else []
    | Element (_, _, children) -> flat_map (fun child -> get_invariant_inner child) children
    | _ -> []

let rec get_invariant (w : xml) =
  match w with
    | Element ("WHILE", _, children) ->
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
        | stmt::stmts -> 
          let program = fold_right (fun s1 s2 -> (mk_exp (Seq (s1,s2)) s1.offset)) stmts (mk_exp Skip 0) in
          let program_spec = get_function_spec xml in
          mk_exp_with_annot (Seq (stmt, program)) program.offset program_spec
      end
    | Element ("EXPR_RESULT", _, [child]) -> xml_to_exp child
    | Element ("ASSIGN", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [child1; child2] -> mk_exp (Assign (xml_to_exp child1, xml_to_exp child2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("ASSIGN", (get_offset attrs))) 
      end 
    | Element ("NAME", attrs, _) -> mk_exp (Var (get_value attrs)) (get_offset attrs)
    | Element ("NULL", attrs, _) -> mk_exp Null (get_offset attrs)
    | Element ("FUNCTION", attrs , [name; params; block]) ->
      let fn_name = name_element name in
      let fn_params = xml_to_vars params in
      let fn_body = xml_to_exp block in
      let fn_spec = get_function_spec xml in
      if (fn_name = "") then mk_exp_with_annot (AnnonymousFun (fn_params,fn_body)) (get_offset attrs) fn_spec
      else mk_exp_with_annot (NamedFun (fn_name,fn_params,fn_body)) (get_offset attrs) fn_spec
    | Element ("BLOCK", _, children) ->  
      let stmts = map xml_to_exp children in
      begin
      match stmts with
        | [] -> mk_exp Skip 0
        | stmts -> fold_right (fun s1 s2 -> (mk_exp (Seq (s1,s2)) s1.offset)) stmts (mk_exp Skip 0)
      end
    | Element ("VAR", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [child] -> mk_exp (VarDec (name_element child)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("VAR", (get_offset attrs))) 
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
      if abs_float (n_float -. (floor n_float)) > epsilon_float then raise OnlyIntegersAreImplemented 
      else 
        let n_int = int_of_float n_float in
        mk_exp (Num n_int) (get_offset attrs)
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
    | Element ("EMPTY", attrs, _) -> mk_exp Skip 0
    | Element ("IF", attrs, [condition; t_block; f_block]) ->
      mk_exp (If (xml_to_exp condition, xml_to_exp t_block, xml_to_exp f_block)) (get_offset attrs)
    | Element ("EQ", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [e1; e2] -> mk_exp (BinOp (xml_to_exp e1, Equal, xml_to_exp e2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("EQ", (get_offset attrs))) 
      end 
    | Element ("SHEQ", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [e1; e2] -> mk_exp (BinOp (xml_to_exp e1, TripleEqual, xml_to_exp e2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("SHEQ", (get_offset attrs))) 
      end
    | Element ("LT", attrs, children) ->
      begin match (remove_annotation_elements children) with
        | [e1; e2] -> mk_exp (BinOp (xml_to_exp e1, Lt, xml_to_exp e2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("LT", (get_offset attrs))) 
      end
    | Element ("LE", attrs, children) ->
      begin match (remove_annotation_elements children) with
        | [e1; e2] -> mk_exp (BinOp (xml_to_exp e1, Le, xml_to_exp e2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("LE", (get_offset attrs))) 
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
    | Element ("ADD", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [child1; child2] -> mk_exp (BinOp (xml_to_exp child1, Plus, xml_to_exp child2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("ADD", (get_offset attrs))) 
      end
    | Element ("THIS", attrs, _) -> mk_exp This (get_offset attrs)
    | Element (tag_name, attrs, _) -> raise (Parser_Unknown_Tag (tag_name, (get_offset attrs)))
    | PCData _ -> raise Parser_PCData

let js_to_xml (filename : string) : string =
  match Unix.system ("java -jar " ^ !Config.js_to_xml_parser ^ " " ^ (Filename.quote filename)) with
    | Unix.WEXITED _ -> String.sub filename 0 (String.length filename - 3) ^ ".xml"
    | _ -> raise JS_To_XML_parser_failure