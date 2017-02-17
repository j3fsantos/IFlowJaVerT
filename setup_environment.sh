#!/bin/bash
mkdir -p environment
cp *.native environment
cp src/JaVerT/runtime/* environment
cp src/JS2JSIL/runtime/*.jsil environment
cp src/JS2JSIL/runtime/harness.js environment
