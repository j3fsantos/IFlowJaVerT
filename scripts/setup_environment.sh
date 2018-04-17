#!/bin/bash
# to be run from the top folder

mkdir -p environment

# racket stuff
cp src/Cosette/runtime/mem_model.rkt environment
cp src/Cosette/runtime/interpreter.rkt environment 
cp src/Cosette/runtime/util.rkt environment
cp src/Cosette/runtime/internals_racket.rkt environment 
cp src/Cosette/runtime/assertions.rkt environment
cp src/Cosette/runtime/racket/*.rkt environment

# JS2JSIL stuff
cp src/JS2JSIL/runtime/*.jsil environment
cp src/JS2JSIL/runtime/harness.js environment
cp src/JaVerT/runtime/* environment

# executables and scripts
cp *.native environment
cp scripts/remake.sh environment
cp scripts/run.sh environment

cp scripts/test_concrete_cosette.sh environment
cp scripts/test_single_file.sh environment
cp scripts/test_passing_cosette.sh environment
cp scripts/test_failing_cosette.sh environment

cp scripts/concretize.py environment
cp scripts/coverage.py environment
cp scripts/overall_coverage.py environment
cp scripts/sum_solver.py environment

# test262 tests
rm -rf test262/environment
cp -r environment test262/environment

# concrete tests
mkdir -p environment/concrete
cp src/Cosette/tests/concrete/*.js environment/concrete
