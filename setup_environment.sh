#!/bin/bash
mkdir -p environment
cp src/Cosette/new_runtime/mem_model.rkt environment
cp src/Cosette/new_runtime/interpreter.rkt environment 
cp src/Cosette/new_runtime/util.rkt environment
cp src/Cosette/new_runtime/internals_racket.rkt environment 
cp src/Cosette/new_runtime/assertions.rkt environment
cp src/JS2JSIL/runtime/*.jsil environment
cp src/JS2JSIL/runtime/harness.js environment
cp src/JaVerT/runtime/* environment
cp *.native environment
cp remake.sh environment
cp run.sh environment

rm -rf test262/environment
cp -r environment test262/environment

mkdir -p environment/concrete
cp src/Cosette/Tests/concrete/*.js environment/concrete
cp test_concrete_cosette.sh environment
cp test_single_file.sh environment
