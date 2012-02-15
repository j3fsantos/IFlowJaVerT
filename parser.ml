open Xml
open Syntax
open List

exception Parser_No_Program
exception Parser_Xml_To_String
exception Parser_Xml_To_Var
exception Parser_Unknown_Tag of string
exception Parser_PCData
exception Parser_ObjectList
exception JS_To_XML_parser_failure

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

let xml_to_string xml : string =
  match xml with
    | Element ("NAME", attrs, _) -> get_value attrs
    | _ -> raise Parser_Xml_To_String

let rec xml_to_var xml : string = 
  match xml with
    | Element ("NAME", attrs, _) -> get_value attrs
    | Element ("PARAM_LIST",_,[child]) -> xml_to_var child
    | _ -> raise Parser_Xml_To_Var
  
let rec xml_to_exp xml : exp =
  match xml with
    (*Element (tag name, attributes, children )*)
    | Element ("SCRIPT", _, children) -> 
      let stmts = map xml_to_exp children in
      begin
      match stmts with
        | [] -> raise Parser_No_Program
        | [stmt] -> stmt
        | stmt::stmts -> fold_right (fun s1 s2 -> (mk_exp (Seq (s1,s2)) s1.offset)) (stmt::stmts) (mk_exp Skip 0)
      end
    | Element ("EXPR_RESULT", _, [child]) -> xml_to_exp child
    | Element ("ASSIGN", attrs, [child1; child2]) -> mk_exp (Assign (xml_to_exp child1, xml_to_exp child2)) (get_offset attrs)
    | Element ("NAME", attrs, _) -> mk_exp (Var (get_value attrs)) (get_offset attrs)
    | Element ("NULL", attrs, _) -> mk_exp Null (get_offset attrs)
    | Element ("FUNCTION", attrs , [name; params; block]) ->
      let fn_name = xml_to_string name in
      let fn_params = xml_to_var params in
      let fn_body = xml_to_exp block in
      if (fn_name = "") then mk_exp (AnnonymousFun (fn_params,fn_body)) (get_offset attrs)
      else mk_exp (NamedFun (fn_name,fn_params,fn_body)) (get_offset attrs)
    | Element ("BLOCK", _, children) ->  
      let stmts = map xml_to_exp children in
      begin
      match stmts with
        | [] -> mk_exp Skip 0
        | [stmt] -> stmt
        | stmt::stmts -> fold_right (fun s1 s2 -> (mk_exp (Seq (s1,s2)) s1.offset)) (stmt::stmts) (mk_exp Skip 0)
      end
    | Element ("VAR", attrs, [child]) -> mk_exp (VarDec (xml_to_var child)) (get_offset attrs)
    | Element ("CALL", attrs, [child1; child2]) -> mk_exp (Call (xml_to_exp child1, xml_to_exp child2)) (get_offset attrs)
    | Element ("NUMBER", attrs, _) -> mk_exp (Num (int_of_string (get_value attrs))) (get_offset attrs)
    | Element ("OBJECTLIT", attrs, objl) ->
      let l = map (fun obj -> 
        match obj with
        | Element ("STRING", attrs, [e]) -> (get_value attrs, xml_to_exp e) 
        | _ -> raise Parser_ObjectList
      ) objl
      in (mk_exp (Obj l) (get_offset attrs))
    | Element ("WITH", attrs, [obj; block]) ->
      mk_exp (With (xml_to_exp obj, xml_to_exp block)) (get_offset attrs)
    | Element ("EMPTY", attrs, _) -> mk_exp Skip 0
    | Element ("IF", attrs, [condition; t_block; f_block]) ->
      mk_exp (If (xml_to_exp condition, xml_to_exp t_block, xml_to_exp f_block)) (get_offset attrs)
    | Element ("EQ", attrs, [e1; e2]) -> mk_exp (BinOp (xml_to_exp e1, Equal, xml_to_exp e2)) (get_offset attrs)
    | Element ("WHILE", attrs, [condition; block]) ->
      mk_exp (While (xml_to_exp condition, xml_to_exp block)) (get_offset attrs)
    | Element ("GETPROP", attrs, [child1; child2]) ->
      mk_exp (Access (xml_to_exp child1, string_element child2)) (get_offset attrs)
    | Element (tag_name, _, _) -> raise (Parser_Unknown_Tag tag_name) 
    | PCData _ -> raise Parser_PCData

let js_to_xml (filename : string) : string =
  match Unix.system ("java -jar " ^ !Config.js_to_xml_parser ^ " " ^ (Filename.quote filename)) with
    | Unix.WEXITED _ -> String.sub filename 0 (String.length filename - 3) ^ ".xml"
    | _ -> raise JS_To_XML_parser_failure
      
