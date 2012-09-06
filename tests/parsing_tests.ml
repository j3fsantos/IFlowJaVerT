open OUnit
open Logic
open Logic_Utils
open Formula_parser
open Formula_lexer
open Syntax
open Parsing_utils
    
let test_formula1 () =
  let f = parse_formulas "(#l1,x) |-> #(/)" in
  assert_equal (HeapletEmpty (LocNum (AVar "1"), "x")) (List.hd f)
 
let test_formula2 () =
  let f = parse_formulas "(#l1,x) |-> #(/) * (#l1,y) |-> 5" in
  assert_equal (Star [HeapletEmpty (LocNum (AVar "1"), "x"); Heaplet (LocNum (AVar "1"), "y", pv_le (Pv_Num 5.0))]) (List.hd f)
  
let test_formula3 () =
  let f = parse_formulas "(_#l1,x) |-> #(/)" in
  assert_equal (HeapletEmpty (LocNum (EVar "1"), "x")) (List.hd f)

let test_string () =
  let f = parse_formulas "(#l1,x) |-> 'abc'" in
  assert_equal (Heaplet (LocNum (AVar "1"), "x", pv_le (Pv_String "abc"))) (List.hd f)
  
let test_obj () =
  let f = parse_formulas "#obj[#l1](x,y,z | a:1,b:'abc')" in
  assert_equal (Star [
    HeapletEmpty (LocNum (AVar "1"), "x");
    HeapletEmpty (LocNum (AVar "1"), "y");
    HeapletEmpty (LocNum (AVar "1"), "z");
    Heaplet (LocNum (AVar "1"), "a", pv_le (Pv_Num 1.0));
    Heaplet (LocNum (AVar "1"), "b", pv_le (Pv_String "abc"));
    ]) (List.hd f)
  
(* TODO unescaping 
let test_esc_string () =
  let f = parse_formula "(@l1,x) |-> \"\\n\\t\\\"\"" in
  print_string (PrintLogic.string_of_formula f);
  assert_equal (Heaplet (LocNum 1, "x", pv_le (Pv_String "\n\t\""))) f *)

let test_abs_heap () =
  let abs_node = AbsLoc { lid = (AVar "1"); ltype = LocStl } in
  let stl = {
      stl_loc_f = abs_node;
      stl_loc_s = Lb_LocNull;
      stl_tail = Some Lb_LocNull;
      stl_fp_fields = {
        has = EFields.empty;
        hasnt = ["x"; "y"];
      };
      stl_sp_fields = empty_fields
  } in
  let apl = AbsLoc { lid = (AVar "1"); ltype = LocPl } in
  let pl_heap = {
    pl_id = apl;
    pl_tail = Some (Lb_Loc abs_node);
    pl_fields = {
      has = EFields.empty;
      hasnt = ["x"; "y"];
    }
  } in 
  let abs_heap_f = Star [
    CScopes [abs_node;Lg];
    ObjFootprint (Lg, ["#proto"; "#this"]);
    Heaplet (Lg, "#proto", lb_le (Lb_Loc apl));
    Heaplet (Lg, "#this", lb_le (Lb_Loc Lg));
    Storelet stl;
    PList pl_heap;
  ] in
  let f = parse_formulas
    "#cScope = [#stl1; #lg] *
     #footprint[#lg] (#proto , #this) * 
     #obj[#lg](|#proto : #pl1, #this : #lg) *
     #storelet[#stl1](x, y|) *
     #plist[#pl1,#stl1](x, y| )" in
  assert_equal (simplify abs_heap_f) (simplify (List.hd f))
  
let test_abs_heaplets_two_parts () =
  let abs_node_f = AbsLoc { lid = (AVar "1"); ltype = LocStl } in
  let abs_node_s = Lb_Loc (AbsLoc { lid = (AVar "2"); ltype = LocStl }) in
  let stl = {
      stl_loc_f = abs_node_f;
      stl_loc_s = abs_node_s;
      stl_tail = Some (Lb_Loc Lop);
      stl_fp_fields = {
        has = EFields.empty;
        hasnt = ["x"; "y"];
      };
      stl_sp_fields = {
        has = EFields.empty;
        hasnt = ["a"];
      };
  } in
  let abs_heap_f = Star [
    CScopes [abs_node_f;Lg];
    ObjFootprint (Lg, ["#proto"; "#this"]);
    Heaplet (Lg, "#proto", lb_le (Lb_Loc Lop));
    Heaplet (Lg, "#this", lb_le (Lb_Loc Lg));
    Storelet stl
  ] in
  let f = parse_formulas
    "#cScope = [#stl1; #lg] *
     #footprint[#lg] (#proto , #this) * 
     #obj[#lg](|#proto : #lop, #this : #lg) *
     #storelet[#stl1,#lop,#stl2](x, y|)(a|) "
    in
  assert_equal (simplify abs_heap_f) (simplify (List.hd f))

let suite = "Testing Parsing" >:::
  ["test formula 1" >:: test_formula1;
   "test formula 2" >:: test_formula2;
   "test formula 3" >:: test_formula3;
   "test string" >:: test_string;
   "test abs_heap" >:: test_abs_heap; 
   "test abs heaplets two parts" >:: test_abs_heaplets_two_parts;
   "test obj" >:: test_obj
]