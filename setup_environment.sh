#!/bin/bash
mkdir -p environment
cp *.native environment
cp src/javert_runtime/* environment
cp src/translation_runtime/*.jsil environment
cp src/translation_runtime/harness.js environment

