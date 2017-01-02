#!/bin/bash
mkdir -p environment
cp racket/mem_model.rkt environment
cp racket/interpreter.rkt environment 
cp racket/util.rkt environment
cp -r tests/symbolic environment 
cp src/translation_runtime/*.jsil environment
cp src/translation_runtime/harness.js environment
cp test_main.native environment
cp js2jsil_main.native environment
cp SJSIL_Parser_main.native environment
cp jsil2rkt.native environment
cp symb_execution_main.native environment
cp src/examples/internal_functions.jsil environment
cp src/examples/obj_int_fun.jsil environment
cp src/examples/js_preds.jsil environment
