#!/bin/bash

pathToTests=$1
interpreter=$2
fullPath="../$pathToTests"

cd environment

time {
echo "----------------------------"
echo "Testing folder: $pathToTests"

../runtests/runtests.py $fullPath --jsonparser --interp $interpreter --verbose --verbose

echo "----------------------------"
}
echo "----------------------------"
