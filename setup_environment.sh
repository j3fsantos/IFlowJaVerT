#!/bin/bash
mkdir -p environment/DOM
mkdir -p environment/lists
mkdir -p environment/sets
mkdir -p environment/PQ
mkdir -p environment/bi
mkdir -p environment/tom
cp remake.sh environment
cp test.sh environment
cp bi_test.sh environment
cp *.native environment
cp src/JaVerT/runtime/* environment
cp src/JaVerT/DOM/*.js environment/DOM
cp src/JS2JSIL/runtime/*.jsil environment
cp src/JS2JSIL/runtime/harness.js environment
cp src/JSILVerify/examples/lists/*.jsil environment/lists
cp src/JSILVerify/examples/sets/*.jsil environment/sets
cp src/JaVerT/examples/*.js environment
cp src/JaVert/examples/PriorityQueue/*.js environment/PQ
cp src/JSILVerify/bi_examples/*.jsil environment/bi
cp *.native web/jsil_binaries
cp src/JaVerT/runtime/*.jsil web/jsil_binaries
cp src/JSILVerify/examples/tom/*.jsil environment/tom
cp tutorial/main.pdf web/public/docs/tutorial.pdf
