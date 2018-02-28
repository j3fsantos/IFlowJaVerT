#!/bin/bash
mkdir -p environment/test262
cp remake.sh environment
cp cleanup.sh environment
cp test.sh environment
cp JaVerT.sh environment
cp *.native environment
cp src/JaVerT/runtime/* environment
cp src/JS2JSIL/runtime/*.jsil environment
cp src/JS2JSIL/runtime/harness.js environment
cp src/JaVerT/examples/*.js environment
cp src/JaVerT/examples/test262/*.js environment/test262
