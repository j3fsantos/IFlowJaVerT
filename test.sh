#!/bin/bash

# Bash array format: ("one" "two" "three")
# JS Files to test
declare -a jsfiles=("function_test0")
# JSIL Files to test
declare -a jsilfiles=("paper_queue")

echo "Testing js files"
for f in "${jsfiles[@]}"
do
	echo "Next file: $f.js"
	./js2jsil.native -file $f.js -logic
	rc=$?; if [[ $rc != 0 ]]; then echo "Failed js2jsil on $f"; fi
	res=$(./jsilverify.native -file $f.jsil -js | tail -n1)
	if [[ $res == "ALL Succeeded"* ]]; then
		echo "Pass: $f"
	else
		echo "Fail: $f"
	fi
done

echo "Testing jsil files"
for f in "${jsilfiles[@]}"
do
	echo "Next file: $f.jsil"
	res=$(./jsilverify.native -file $f.jsil -js | tail -n1)
	if [[ $res == "ALL Succeeded"* ]]; then
		echo "Pass: $f"
	else
		echo "Fail: $f"
	fi
done
