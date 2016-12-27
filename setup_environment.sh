#!/bin/bash
mkdir -p environment
cp racket/mem_model.rkt environment
cp racket/interpreter.rkt environment 
cp racket/util.rkt environment
cp -r tests/symbolic environment 
cp src/pulp/SJSIL/translation_runtime/*.jsil environment
cp src/pulp/SJSIL/translation_runtime/harness.js environment
cp test_main.native environment
cp js2jsil_main.native environment
cp SJSIL_Parser_main.native environment
cp jsil2rkt.native environment
cp symb_execution_main.native environment
cp src/pulp/SJSIL/examples/internal_functions.jsil environment
cp src/pulp/SJSIL/examples/obj_int_fun.jsil environment
cp symb_execution_main.byte environment
cp src/pulp/SJSIL/examples/js_preds.jsil environment
cp run_racket_example.sh environment
