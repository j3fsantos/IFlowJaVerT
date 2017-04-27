#!/bin/bash
mkdir -p environment
mkdir -p environment/lists
mkdir -p environment/PQ
mkdir -p environment/bi
cp remake.sh environment
cp test.sh environment
cp bi_test.sh environment
cp *.native environment
cp src/JaVerT/runtime/* environment
cp src/JaVerT/DOM/*.js environment
cp src/JS2JSIL/runtime/*.jsil environment
cp src/JS2JSIL/runtime/harness.js environment
cp src/JSILVerify/examples/lists/*.jsil environment/lists
cp src/JaVerT/examples/*.js environment
cp src/JaVert/examples/PriorityQueue/*.js environment/PQ
cp src/JSILVerify/bi_examples/*.jsil environment/bi