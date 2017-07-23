#!/bin/bash

# Bash array format: ("one" "two" "three")
# JS Files to test
declare -a jsfiles=("kv-map" "map" "priority_queue" "bst" "sort" "counter1" "counter2" "function_test1_fail" "function_test3" "closure1" "closure2")
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
	res=$(./jsilverify.native -file $f.jsil -js | tail -n1)
	if [[ $res == "ALL Succeeded"* ]]; then
		echo "Pass: $f" 
	else
		echo "Fail: $f" 
	fi }
	echo "----------------"
done

echo "Testing jsil files"
echo "------------------"
for f in "${jsilfiles[@]}"
do
	time {
	echo "Next file: $f.jsil"
	res=$(./jsilverify.native -file $f.jsil -js | tail -n1)
	if [[ $res == "ALL Succeeded"* ]]; then
		echo "Pass: $f"
	else
		echo "Fail: $f"
	fi }
	echo "------------------"
done
