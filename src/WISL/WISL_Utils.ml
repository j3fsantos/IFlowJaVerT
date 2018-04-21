open WISL_Syntax
open WISL_Printer

exception Unmatching_types

module TypeMap = Map.Make(struct
    type t = logic_expr
    let compare = Pervasives.compare
  end)


let float_of_num n = match n with
  | Float f -> f
  | Int i -> float_of_int i
  
let add_spec f pre post =
  let specs = Some { pre; post } in
  let { name; params; body; spec; return_expr } = f in
  { name; params; body; return_expr; spec = specs}
  
let empty_metadata = {
  precmds = [];
  postcmds = [];
  invariant = None;
}


let type_of_val v =
  match v with
  | Bool _ -> WBool
  | Loc _ -> WObj
  | Num _ -> WNum
  | Str _ -> WString
  | Null -> WNull
  | VList _ -> WList


let print_map types =
    TypeMap.iter (fun le t -> Format.printf "%a has type %a@.@." pp_logic_expr le pp_wisl_type t)
    types

let rec infer_logic_expr knownp lexpr =
  (* Format.printf "calling @.";
  print_map knownp; *)
  let needs_to_be expr t knownp =
    match TypeMap.find_opt expr knownp with
    | Some tp when tp <> t -> 
        failwith (Format.asprintf 
          "I infered both types %a and %a on expression %a in assertion"
          pp_wisl_type tp pp_wisl_type t pp_logic_expr expr)
    | _ -> TypeMap.add expr t knownp
  in
  match lexpr with
  | LVal v -> TypeMap.add lexpr (type_of_val v) knownp
  | LBinOp (le1, b, le2) ->
    begin
      let infered = infer_logic_expr (infer_logic_expr knownp le1) le2 in
      match b with
      | AND | OR -> TypeMap.add lexpr WBool
                    (needs_to_be le1 WBool (needs_to_be le2 WBool infered))
      | EQUAL | NEQ -> TypeMap.add lexpr WBool infered
      | LSTCONS ->  TypeMap.add lexpr WList (needs_to_be le2 WList infered)
      | LSTCAT -> TypeMap.add lexpr WList
                    (needs_to_be le1 WList (needs_to_be le2 WList infered))
      | _ -> TypeMap.add lexpr WNum (needs_to_be le2 WNum (needs_to_be le1 WNum infered))
    end
  | LUnOp (u, le) ->
    begin
    let infered = infer_logic_expr knownp le in
    match u with
    | NOT -> TypeMap.add lexpr WBool (needs_to_be le WBool infered)
    | LEN -> TypeMap.add lexpr WNum (needs_to_be le WList infered)
    | HEAD -> needs_to_be le WList infered
    | TAIL -> TypeMap.add lexpr WList (needs_to_be le WList infered)       
    end
  | LVar lvar ->  knownp
  | PVar lvar -> knownp
  | LEList lel -> TypeMap.add lexpr WList
  (List.fold_left infer_logic_expr knownp lel)



let rec find_fixed_point f a =
  let b = f a in
  if Pervasives.compare a b = 0 then b
  else find_fixed_point f b


let rec infer_single_assert_step asser known =
  let needs_to_be expr t knownp =
    match TypeMap.find_opt expr knownp with
    | Some tp when tp <> t -> 
        failwith (Format.asprintf 
          "I infered both types %a and %a on expression %a in assertion : %a"
          pp_wisl_type tp pp_wisl_type t pp_logic_expr expr
          pp_logic_assert asser)
    | _ -> TypeMap.add expr t knownp
  in
  let same_type e1 e2 knownp =
    let topt1 = TypeMap.find_opt e1 knownp in
    let topt2 = TypeMap.find_opt e2 knownp in
    match topt1, topt2 with
    | Some t1, Some t2 when t1 <> t2 ->
      failwith (Format.asprintf 
        "Expressions %a and %a should have the same type but are of types \
        %a and %a in assertion : %a"
        pp_logic_expr e1 pp_logic_expr e2 pp_wisl_type t1 pp_wisl_type t2
        pp_logic_assert asser)
    | Some t1, _ -> Some t1
    | _, Some t2 -> Some t2
    | None, None -> None
  in
  match asser with
  | LTrue | LFalse | LEmp -> known
  | LNot la -> infer_single_assert_step la known
  | LAnd (la1, la2) -> infer_single_assert_step la2 (infer_single_assert_step la1 known)
  | LOr (la1, la2) -> infer_single_assert_step la2 (infer_single_assert_step la1 known)
  | LStar (la1, la2) -> infer_single_assert_step la2 (infer_single_assert_step la1 known)
  | LPred (_, lel) -> List.fold_left infer_logic_expr known lel
  | LPointsTo (le1, pn, le2) ->
    let infered = infer_logic_expr (infer_logic_expr known le1) le2 in
    TypeMap.add le1 WObj (needs_to_be le1 WObj infered)
  | LEq (le1, le2) ->
    let infered = infer_logic_expr (infer_logic_expr known le1) le2 in
    let topt = same_type le1 le2 infered in
    (match topt with
    | Some t -> TypeMap.add le1 t (TypeMap.add le2 t infered)
    | None -> infered)
  | LLess (le1, le2) | LGreater (le1, le2) | LLessEq (le1, le2)
  | LGreaterEq (le1, le2) ->
    let infered = infer_logic_expr (infer_logic_expr known le1) le2 in
    let inferedp = needs_to_be le1 WNum (needs_to_be le2 WNum infered) in
    TypeMap.add le1 WNum (TypeMap.add le2 WNum inferedp)
  
  
let infer_single_assert known asser =
  find_fixed_point (infer_single_assert_step asser) known

let infer_types_pred assert_list =
  let join _le topt1 topt2 =
  match topt1, topt2 with
  | Some t1, Some t2 when t1 = t2 -> Some t1
  | _ -> None
  in
  let infers_on_asserts = 
    List.map (infer_single_assert TypeMap.empty) assert_list
  in
  let (f, r) = (List.hd infers_on_asserts, List.tl infers_on_asserts) in
  List.fold_left (TypeMap.merge join) f r
