#!/bin/bash
mkdir -p environment
cp src/Cosette/new_runtime/mem_model.rkt environment
cp src/Cosette/new_runtime/interpreter.rkt environment 
cp src/Cosette/new_runtime/util.rkt environment
cp src/Cosette/new_runtime/internals_racket.rkt environment 
cp src/Cosette/new_runtime/assertions.rkt environment
cp src/JS2JSIL/runtime/*.jsil environment
cp src/JS2JSIL/runtime/harness.js environment
cp js2jsil.native environment
cp jsil2rkt.native environment
cp remake.sh environment
cp run.sh environment
cp test_concrete_cosette.sh environment
