#!/bin/bash
mkdir -p environment
mkdir -p environment/lists
mkdir -p environment/PQ
cp remake.sh environment
cp *.native environment
cp src/JaVerT/runtime/* environment
cp src/JaVerT/DOM/*.js environment
cp src/JS2JSIL/runtime/*.jsil environment
cp src/JS2JSIL/runtime/harness.js environment
cp src/JSILVerify/examples/lists/*.jsil environment/lists
cp src/JaVerT/examples/*.js environment
cp src/JaVert/examples/PriorityQueue/*.js environment/PQ