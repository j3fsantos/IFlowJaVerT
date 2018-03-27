#!/bin/bash

for filename in ./$1/*.js; do
	time {
	echo "Next file: $filename"
	name=$(echo $filename | cut -f 2 -d '.')
	#echo $name
	jname='.'$name'.jsil'
	#echo $jname
	./js2jsil.native -file "$filename" -cosette &> /dev/null
	./jsil2rkt.native -file "$jname" -test262
	rname='.'$name'.rkt'
	#echo $rname
	mv "$rname" . 
	rname=$(basename $rname)
	#echo $rname
	res=$(racket $rname | tail -n1)
	#echo $res
	if [[ $res == "(unsat)"* ]]; then
		echo "Pass: $filename" 
	else
		echo "Fail: $filename" 
	fi }
	echo "----------------" }
done