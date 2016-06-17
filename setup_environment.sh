#!/bin/bash
mkdir -p environment
cp src/parser/lib/js_parser.jar environment
cp src/pulp/SJSIL/translation_runtime/*.jsil environment
cp src/pulp/SJSIL/translation_runtime/harness.js environment
cp test_main.byte environment
cp js2jsil_main.{byte,native} environment
cp SJSIL_Parser_main.{byte,native} environment
