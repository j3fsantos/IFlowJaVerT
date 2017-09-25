#!/bin/bash
mkdir -p environment
cp scripts/* environment
cp *.native environment
cp src/JS2JSIL/runtime/*.jsil environment
cp src/JS2JSIL/runtime/harness.js environment
cp src/examples/JSIL/*.jsil environment
