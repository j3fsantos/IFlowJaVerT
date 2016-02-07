(* ./src/pulp/logic/formula_parser/pulp_Formula_Parser_Utils.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open Parser_syntax
open List
open Pulp_Logic
open Pulp_Logic_Utils
open Utils

exception No_Spec_In_Code of string
exception No_Codename
exception No_Invariant_In_Code

let parse_formulas f = 
  let lexbuf = Lexing.from_string f in
  Pulp_Formula_Parser.main Pulp_Formula_Lexer.token lexbuf

let get_annots_from_code annots annot_type = 
  let annots = List.filter (fun annot -> annot.annot_type = annot_type) annots in
  List.map (fun annot -> parse_formulas annot.annot_formula) annots
  
let get_spec_from_code annots annot_type = 
  let res = get_annots_from_code annots annot_type in
  match res with
    | [] -> raise (No_Spec_In_Code (Pretty_print.string_of_annot_type annot_type))
    | hd :: tl -> hd
  
let get_inv_from_code annots = 
  let res = get_annots_from_code annots Invariant in
  match res with
    | [] -> raise No_Invariant_In_Code
    | _ -> res

let get_function_spec annots = 
  
  let rec get_fspec_inner annots current_spec =
    match annots with
      | annot1 :: rest ->
        begin match annot1.annot_type with
          | Requires
          | TopRequires -> 
            begin match current_spec with
              | [] -> get_fspec_inner rest [annot1]
              | _ -> current_spec :: (get_fspec_inner rest [annot1])
            end
          | Ensures
          | EnsuresErr
          | TopEnsures
          | TopEnsuresErr -> get_fspec_inner rest (annot1 :: current_spec)
          | t -> raise (Invalid_argument (Pretty_print.string_of_annot_type t))
        end
      | [] -> [current_spec] in

  let annots = List.filter (fun annot -> 
    annot.annot_type = Requires || 
    annot.annot_type = Ensures || 
    annot.annot_type = EnsuresErr || 
    annot.annot_type = TopRequires || 
    annot.annot_type = TopEnsures ||
    annot.annot_type = TopEnsuresErr
  ) annots in
  
  let specs = get_fspec_inner annots [] in

  let rec make_spec spec annots =
    match annots with
      | annot :: rest ->
        begin 
          let spec = match annot.annot_type with
          | Requires
          | TopRequires ->  { spec with spec_pre = parse_formulas annot.annot_formula }
          | Ensures
          | TopEnsures -> { spec with spec_post = (parse_formulas annot.annot_formula) :: spec.spec_post }
          | EnsuresErr
          | TopEnsuresErr -> { spec with spec_excep_post = (parse_formulas annot.annot_formula) :: spec.spec_excep_post }
          | t -> raise (Invalid_argument (Pretty_print.string_of_annot_type t)) in
          make_spec spec rest
        end
      | [] -> spec in
  
  List.map (make_spec (mk_spec empty_f [])) specs

let get_codename annots =
  let codenames = filter (fun annot -> annot.annot_type = Codename) annots in
  match codenames with
    | [codename] -> codename.annot_formula
    | _ -> raise No_Codename

let get_annots annots =
  flat_map (get_annots_from_code annots) [Requires; Ensures; Invariant]
