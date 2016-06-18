#!/bin/bash
mkdir -p unit_tests
cp src/parser/lib/js_parser.jar unit_tests
cp src/pulp/SJSIL/translation_runtime/*.jsil unit_tests
cp test_main.byte unit_tests
cd unit_tests
./test_main.byte
cd ..