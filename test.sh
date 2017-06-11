#!/bin/bash

# Bash array format: ("one" "two" "three")
# JS Files to test
declare -a jsfiles=("priority_queue" "counter1"  "map" "bst" "sort" "counter2" "function_test1_fail" "function_test3" "DOM/new_DOM" "DOM/sanitiseImg" "closure1" "closure2")
# JSIL Files to test
declare -a jsilfiles=("javert_internal_functions" "internal_functions_full")

echo "Testing js files"
echo "----------------"
for f in "${jsfiles[@]}"
do
	time {
	START=$(date +%s%N)
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
