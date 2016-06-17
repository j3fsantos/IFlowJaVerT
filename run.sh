#!/bin/bash -e
jsfile=$(readlink -f $1)
jsilfile=${jsfile%.js}.jsil
verbose=${jsfile%.js}.verbose

cd environment
./js2jsil_main.native -file $jsfile -harness
./SJSIL_Parser_main.native -file $jsilfile -verbose -run &> $verbose || true
./SJSIL_Parser_main.native -file $jsilfile -run
