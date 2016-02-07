(* ./tests/test_Evaluation_Examples.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open OUnit

let test = "Test_Evaluation_Examples" >:::
  [Evaluation_Examples.suite]

let _ = run_test_tt_main test
