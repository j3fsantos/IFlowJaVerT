#!/bin/bash

# copy file to current folder
cp $1 .
#echo "filename:" $1
filename=$(basename $1)
#echo "basename:" $filename
name=${filename%%.*}
#echo $name
jname=$name'.jsil'
#echo $jname
rname=$name'.rkt'
#echo $rname
./js2jsil.native -file "$filename" -cosette &> /dev/null
./jsil2rkt.native -file "$jname" -js 
res=$(racket $rname | tail -n1)
echo $res
if [[ $res == "(unsat)"* ]]; then
	echo "Pass: $filename" 
else
	echo "Fail: $filename" 
fi
