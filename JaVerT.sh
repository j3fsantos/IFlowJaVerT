#!/bin/bash

f=$1

time {
	echo "Verifying: $f.js"
	./js2jsil.native -file $f.js -logic &> /dev/null
	rc=$?; if [[ $rc != 0 ]]; then echo "Failed js2jsil on $f"; fi
	res=$(./jsilverify.native -file $f.jsil -js | tail -n1)
	if [[ $res == "ALL specs succeeded"* ]]; then
		echo "Pass: $f" 
	else
		echo "Fail: $f" 
	fi
}