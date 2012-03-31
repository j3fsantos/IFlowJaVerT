open Xml
open Localconfig

exception UnknownConfigParameter

let js_to_xml_parser = ref ""

let logic_dirs = ref []

let rec parse_config_xml xml : unit =
  match xml with
    | Element ("CONFIG", _, children) -> 
      List.iter parse_config_xml children
    | Element ("JS_TO_XML_PARSER", [(name, value)], _) -> js_to_xml_parser := value
    | Element ("LOGIC", _, children) ->
      List.iter parse_config_xml children
    | Element ("LOGIC_DIR", _, [PCData dir]) -> logic_dirs := dir :: !logic_dirs
    | _ -> raise UnknownConfigParameter

let apply_config () =
  let config_file = Xml.parse_file xmlconfig in 
  parse_config_xml config_file
  
let get_logic_dirs () = !logic_dirs