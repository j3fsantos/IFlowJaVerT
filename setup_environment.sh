#!/bin/bash
mkdir -p environment/lists
mkdir -p environment/sets
mkdir -p environment/PQ
mkdir -p environment/test262
cp remake.sh environment
cp test.sh environment
cp *.native environment
cp src/JaVerT/runtime/* environment
cp src/JS2JSIL/runtime/*.jsil environment
cp src/JS2JSIL/runtime/harness.js environment
cp src/JSILVerify/examples/lists/*.jsil environment/lists
cp src/JSILVerify/examples/sets/*.jsil environment/sets
cp src/JaVerT/examples/*.js environment
cp src/JaVerT/examples/test262/*.js environment/test262
cp *.native web/jsil_binaries
cp src/JaVerT/runtime/*.jsil web/jsil_binaries
