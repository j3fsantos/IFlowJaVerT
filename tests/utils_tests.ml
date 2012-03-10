open OUnit
open Utils
    
let test_unescape_html () =
  assert_equal "<>&\"" (unescape_html "&lt;&gt;&amp;&quot;")

let suite = "Testing Utils" >:::
  ["test unescape" >:: test_unescape_html]