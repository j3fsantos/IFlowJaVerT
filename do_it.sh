#!/bin/bash
echo "Compiling!"
./js2jsil_main.byte -file example.js
cp example.jsil src/pulp/SJSIL/translation_runtime/
cd src/pulp/SJSIL/translation_runtime
echo "Running!"
../../../../SJSIL_Parser_main.byte -file example.jsil -run > output.txt
cd ../../../../