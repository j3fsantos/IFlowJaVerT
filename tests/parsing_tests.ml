open OUnit
open Logic
open Formula_parser
open Formula_lexer

let parse_formula f = 
  let lexbuf = Lexing.from_string f in
  Formula_parser.main Formula_lexer.token lexbuf
    
let test_formula1 () =
  let f = parse_formula "(@l1,x) |-> @empty" in
  assert_equal (HeapletEmpty (LocNum 1, "x")) f
  
let test_formula2 () =
  let f = parse_formula "(@l1,x) |-> @empty * (@l1,y) |-> 5" in
  assert_equal (Star [HeapletEmpty (LocNum 1, "x"); Heaplet (LocNum 1, "y", pv_le (Pv_Num 5))]) f

let test_string () =
  let f = parse_formula "(@l1,x) |-> \"abc\"" in
  assert_equal (Heaplet (LocNum 1, "x", pv_le (Pv_String "abc"))) f
  
(* TODO unescaping 
let test_esc_string () =
  let f = parse_formula "(@l1,x) |-> \"\\n\\t\\\"\"" in
  print_string (PrintLogic.string_of_formula f);
  assert_equal (Heaplet (LocNum 1, "x", pv_le (Pv_String "\n\t\""))) f *)

let suite = "Testing Parsing" >:::
  ["test formula 1" >:: test_formula1;
   "test formula 2" >:: test_formula2;
   "test string" >:: test_string  
]