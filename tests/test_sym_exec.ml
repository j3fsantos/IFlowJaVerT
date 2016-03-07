(* ./tests/test_sym_exec.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)

open OUnit

let test_translation = "Test_Symbolic_Execution" >:::
  [ (* Pulp_Sym_Exec_Tests.suite; *)  Spec_Functions_Tests.suite]

let _ = run_test_tt_main test_translation
