open Xml
open Localconfig

exception UnknownConfigParameter

let js_to_xml_parser = ref ""

let rec parse_config_xml xml : unit =
  match xml with
    | Element ("CONFIG", _, children) -> 
      List.iter (fun child -> parse_config_xml child) children
    | Element ("JS_TO_XML_PARSER", [(name, value)], _) -> js_to_xml_parser := value
    | _ -> raise UnknownConfigParameter

let apply_config () =
  let config_file = Xml.parse_file xmlconfig in 
  parse_config_xml config_file
