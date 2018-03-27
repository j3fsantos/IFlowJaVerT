#!/bin/bash
filename=`basename $1`
echo $filename
fname="${filename%.*}"
echo $fname
dirname=`dirname $1`
echo $dirname
./js2jsil.native -file $1
mv "$dirname/$fname.jsil" .
./jsil2rkt.native -file $fname.jsil -js
racket $fname.rkt
rm $fname.jsil
#rm $fname.rkt
