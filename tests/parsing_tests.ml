open OUnit
open Logic
open Logic_Utils
open Formula_parser
open Formula_lexer
open Syntax
open Parsing_utils
    
let test_formula1 () =
  let f = parse_formula "(#l1,x) |-> #(/)" in
  assert_equal (HeapletEmpty (LocNum 1, "x")) f
  
let test_formula2 () =
  let f = parse_formula "(#l1,x) |-> #(/) * (#l1,y) |-> 5" in
  assert_equal (Star [HeapletEmpty (LocNum 1, "x"); Heaplet (LocNum 1, "y", pv_le (Pv_Num 5))]) f

let test_string () =
  let f = parse_formula "(#l1,x) |-> 'abc'" in
  assert_equal (Heaplet (LocNum 1, "x", pv_le (Pv_String "abc"))) f
  
let test_obj () =
  let f = parse_formula "#obj[#l1](x,y,z | a:1,b:'abc')" in
  assert_equal (Star [
    HeapletEmpty (LocNum 1, "x");
    HeapletEmpty (LocNum 1, "y");
    HeapletEmpty (LocNum 1, "z");
    Heaplet (LocNum 1, "a", pv_le (Pv_Num 1));
    Heaplet (LocNum 1, "b", pv_le (Pv_String "abc"));
    ]) f
  
(* TODO unescaping 
let test_esc_string () =
  let f = parse_formula "(@l1,x) |-> \"\\n\\t\\\"\"" in
  print_string (PrintLogic.string_of_formula f);
  assert_equal (Heaplet (LocNum 1, "x", pv_le (Pv_String "\n\t\""))) f *)

let test_abs_heap () =
  let abs_node = AbsLoc { lid = 1; ltype = LocAh } in
  let sl_segment = {
      ah_loc_f = abs_node;
      ah_loc_s = Lb_LocNull;
      ah_tail = Lb_LocNull;
      ah_fp_fields = {
        has = EFields.empty;
        hasnt = ["x"; "y"];
      };
      ah_sp_fields = empty_fields
  } in
  let apl = AbsLoc { lid = 1; ltype = LocApl } in
  let pl_heap = {
    pl_id = apl;
    pl_tail = Lb_Loc abs_node;
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
    AbstractHeaplets sl_segment;
    AbstractProtoList pl_heap;
  ] in
  let f = parse_formula
    "#cScope = [#ahl1; #lg] *
     #footprint[#lg] (#proto , #this) * 
     #obj[#lg](|#proto : #apl1, #this : #lg) *
     #aheaplets[#ahl1](x, y|) *
     #plist[#apl1,#ahl1](x, y| )" in
  assert_equal (simplify abs_heap_f) (simplify f)
  
let test_abs_heaplets_two_parts () =
  let abs_node_f = AbsLoc { lid = 1; ltype = LocAh } in
  let abs_node_s = Lb_Loc (AbsLoc { lid = 2; ltype = LocAh }) in
  let sl_segment = {
      ah_loc_f = abs_node_f;
      ah_loc_s = abs_node_s;
      ah_tail = Lb_Loc Lop;
      ah_fp_fields = {
        has = EFields.empty;
        hasnt = ["x"; "y"];
      };
      ah_sp_fields = {
        has = EFields.empty;
        hasnt = ["a"];
      };
  } in
  let abs_heap_f = Star [
    CScopes [abs_node_f;Lg];
    ObjFootprint (Lg, ["#proto"; "#this"]);
    Heaplet (Lg, "#proto", lb_le (Lb_Loc Lop));
    Heaplet (Lg, "#this", lb_le (Lb_Loc Lg));
    AbstractHeaplets sl_segment
  ] in
  let f = parse_formula
    "#cScope = [#ahl1; #lg] *
     #footprint[#lg] (#proto , #this) * 
     #obj[#lg](|#proto : #lop, #this : #lg) *
     #aheaplets[#ahl1,#lop,#ahl2](x, y|)(a|) "
    in
  assert_equal (simplify abs_heap_f) (simplify f)

let suite = "Testing Parsing" >:::
  ["test formula 1" >:: test_formula1;
   "test formula 2" >:: test_formula2;
   "test string" >:: test_string;
   "test abs_heap" >:: test_abs_heap; 
   "test abs heaplets two parts" >:: test_abs_heaplets_two_parts;
   "test obj" >:: test_obj
]