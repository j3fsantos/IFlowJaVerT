#!/bin/bash -e
jsfile=$(readlink -f $1)

cd environment
exec ./SJSIL_Parser_main.native -from_javascript $jsfile -esprima
