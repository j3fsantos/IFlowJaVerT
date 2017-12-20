#!/bin/bash

pathToTests=$1
fullPath="../$pathToTests"

cd environment

time {
echo "----------------------------"
echo "Testing folder: $pathToTests"

../runtests/runtests.py $fullPath --jsonparser --interp jsil --verbose --verbose

echo "----------------------------"
}
echo "----------------------------"
