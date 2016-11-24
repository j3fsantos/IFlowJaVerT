#!/bin/bash
mkdir -p environment
cp src/pulp/SJSIL/translation_runtime/*.jsil environment
cp src/pulp/SJSIL/translation_runtime/harness.js environment
cp test_main.byte environment
cp js2jsil_main.{byte,native} environment
cp SJSIL_Parser_main.{byte,native} environment
cp src/pulp/SJSIL/examples/internal_functions.jsil environment
cp symb_execution_main.byte environment
