(* ./src/config.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Localconfig
open Xml

exception UnknownConfigParameter

let logic_dirs = ref []
let smt_path = ref ""
let smt_enabled = ref false

let rec parse_config_xml xml : unit =
  match xml with
    | Element ("CONFIG", _, children) -> 
      List.iter parse_config_xml children
    | Element ("JS_TO_XML_PARSER", [(name, value)], _) -> Parser_main.js_to_xml_parser := value
    | Element ("LOGIC", _, children) ->
      List.iter parse_config_xml children
    | Element ("LOGIC_DIR", _, [PCData dir]) -> logic_dirs := dir :: !logic_dirs
    | Element ("SMT", attrs, _) ->
      begin try
        smt_enabled := bool_of_string (List.assoc "enabled" attrs) 
      with
        | Not_found -> ()
        | Invalid_argument _ -> ()
      end;
      begin try
        smt_path := List.assoc "path" attrs 
      with
        | Not_found -> ()
      end
    | _ -> raise UnknownConfigParameter

let apply_config () =
  let config_file = Xml.parse_file xmlconfig in 
  parse_config_xml config_file
  
let get_logic_dirs () = !logic_dirs