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
    | Element ("EMPTY", attrs, _) -> mk_exp Skip (get_offset attrs)
    | Element ("IF", attrs, [condition; t_block]) ->
      let offset = get_offset attrs in
      mk_exp (If (xml_to_exp condition, xml_to_exp t_block, mk_exp Skip offset)) offset
    | Element ("HOOK", attrs, [condition; t_block; f_block])
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
    | Element ("SHNE", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [e1; e2] -> mk_exp (BinOp (xml_to_exp e1, NotTripleEqual, xml_to_exp e2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("SHNE", (get_offset attrs))) 
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
    | Element ("GE", attrs, children) ->
      begin match (remove_annotation_elements children) with
        | [e1; e2] -> mk_exp (BinOp (xml_to_exp e1, Ge, xml_to_exp e2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("GE", (get_offset attrs))) 
      end
    | Element ("INSTANCEOF", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [e1; e2] -> mk_exp (BinOp (xml_to_exp e1, InstanceOf, xml_to_exp e2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("INSTANCEOF", (get_offset attrs))) 
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
    | Element ("ADD", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [child1; child2] -> mk_exp (BinOp (xml_to_exp child1, Plus, xml_to_exp child2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("ADD", (get_offset attrs))) 
      end
    | Element ("SUB", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [child1; child2] -> mk_exp (BinOp (xml_to_exp child1, Minus, xml_to_exp child2)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("SUB", (get_offset attrs))) 
      end
    | Element ("THIS", attrs, _) -> mk_exp This (get_offset attrs)
    | Element ("RETURN", attrs, [child]) -> mk_exp (Return (xml_to_exp child)) (get_offset attrs)
    | Element ("REGEXP", attrs, [pattern]) -> mk_exp (RegExp ((string_element pattern), "")) (get_offset attrs)
    | Element ("REGEXP", attrs, [pattern; flags]) -> 
      mk_exp (RegExp ((string_element pattern), (string_element flags))) (get_offset attrs)
    | Element ("NOT", attrs, [child]) -> mk_exp (Unary_op (Not, xml_to_exp child)) (get_offset attrs)
    | Element ("TYPEOF", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [child] -> mk_exp (Unary_op (TypeOf, xml_to_exp child)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("TYPEOF", get_offset attrs)) 
      end
    | Element ("POS", attrs, children) -> 
      begin match (remove_annotation_elements children) with
        | [child] -> mk_exp (Unary_op (Positive, xml_to_exp child)) (get_offset attrs)
        | _ -> raise (Parser_Unknown_Tag ("POS", get_offset attrs)) 
      end
    | Element ("GETELEM", attrs, [child1; child2]) -> mk_exp (CAccess (xml_to_exp child1, xml_to_exp child2)) (get_offset attrs)
    | Element ("AND", attrs, [child1; child2]) -> mk_exp (BinOp (xml_to_exp child1, And, xml_to_exp child2)) (get_offset attrs)
    | Element ("OR", attrs, [child1; child2]) -> mk_exp (BinOp (xml_to_exp child1, Or, xml_to_exp child2)) (get_offset attrs)
    | Element ("ARRAYLIT", attrs, children) ->
      convert_arraylist_to_object attrs children
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
  let l = l @ ["length", mk_exp (Num (List.length l)) 0] in
  mk_exp (Obj l) (get_offset attrs)
  

let js_to_xml (filename : string) : string =
  match Unix.system ("java -jar " ^ !Config.js_to_xml_parser ^ " " ^ (Filename.quote filename)) with
    | Unix.WEXITED _ -> String.sub filename 0 (String.length filename - 3) ^ ".xml"
    | _ -> raise JS_To_XML_parser_failure
