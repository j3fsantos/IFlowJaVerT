#!/bin/bash

# Bash array format: ("one" "two" "three")
# JS Files to test
declare -a jsfiles=("bst" "IdGenerator" "kv-map" "priority_queue" "sort" "test262/switch-01" "test262/switch-02" "test262/try-catch-01" "test262/try-catch-02" "test262/try-catch-03")
# JSIL Files to test
declare -a jsilfiles=("javert_internal_functions")

echo "Testing js files"
echo "----------------"
for f in "${jsfiles[@]}"
do
	time {
	echo "Next file: $f.js"
	./js2jsil.native -file $f.js -logic &> /dev/null
	rc=$?; if [[ $rc != 0 ]]; then echo "Failed js2jsil on $f"; fi
	res=$(./jsilverify.native -file $f.jsil -js | tail -n2)
	if [[ $res == "ALL specs succeeded"* ]]; then
		echo "Pass: $f" 
	else
		echo "Fail: $f" 
	fi }
	echo "----------------"
	sleep 1
done
