#!/bin/bash
mkdir -p environment
mkdir -p environment/lists
cp remake.sh environment
cp *.native environment
cp src/JaVerT/runtime/* environment
cp src/JaVerT/DOM/*.js environment
cp src/JS2JSIL/runtime/*.jsil environment
cp src/JS2JSIL/runtime/harness.js environment
cp src/JSILVerify/examples/lists/*.jsil environment/lists
cp src/JaVerT/examples/thesis_queue.js environment
cp src/JaVerT/examples/paper_queue.js environment