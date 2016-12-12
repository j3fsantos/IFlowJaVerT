#!/bin/bash
mkdir -p environment
cp racket/mem_model.rkt environment
cp racket/interpreter.rkt environment 
cp racket/util.rkt environment 
cp src/pulp/SJSIL/translation_runtime/*.jsil environment
cp src/pulp/SJSIL/translation_runtime/harness.js environment
cp test_main.byte environment
cp js2jsil_main.{byte,native} environment
cp SJSIL_Parser_main.{byte,native} environment
cp jsil2rkt.{byte,native} environment
cp src/pulp/SJSIL/examples/internal_functions.jsil environment
cp symb_execution_main.byte environment
