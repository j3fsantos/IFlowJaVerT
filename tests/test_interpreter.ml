(* ./tests/test_interpreter.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

(* Testing frontend that only pulls in tests that don't depend on Corestar *)
open OUnit

let suite = "Test_Translation" >:::
  [Pulp_Translation_Tests.suite; Pulp_Interpreter_Tests.suite]

let _ =
  run_test_tt_main suite
