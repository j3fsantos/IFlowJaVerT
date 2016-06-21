#!/bin/bash -e
jsfile=$(readlink -f $1)
jsilfile=${jsfile%.js}.jsil
verbose=${jsfile%.js}.verbose

cd environment
./js2jsil_main.native -file $jsfile -harness

if [ -z $CI ]; then
  # Produce verbose version if not in auto-testing
  ./SJSIL_Parser_main.native -file $jsilfile -verbose -run &> $verbose || true
fi
./SJSIL_Parser_main.native -file $jsilfile -run

if [ -n $CI ]; then
  rm $jsilfile
fi
