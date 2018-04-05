#! /bin/bash

# run it from the environment folder

prefix="../src/Cosette/tests/"

# passing folders to test
declare -a passing=("buckets/passing" \
                    "concrete/passing" \
                    "symbolic/passing" \
                    "jasonsjones/passing" \
                    "test262")

declare -a failing=("jasonsjones/failing" \
                    "javert/failing" \
                    "symbolic/failing")

echo "Running Cosette tests"
echo "---------------------"

echo "Passing tests"
echo "-------------"
for folder in ${passing[@]}
do
  echo "currently in folder $prefix$folder"
  for file in $(ls $prefix$folder/*.js)
  do
    time {
    cp $file .
    filename=$(basename $file)
    name=${filename%%.*}
    echo "Next file: $folder/$filename"
    ./js2jsil.native -file $filename -cosette &> /dev/null
    ./jsil2rkt.native -file $name.jsil -js &> /dev/null
    res=$(racket $name.rkt | tail -n1)
    if [[ $res == "\"#t\"" ]]
    then
      echo "Pass: $filename"
    else
      echo "Fail: $filename"
    fi }
    echo "-----------------"
    sleep 1
  done
done

echo "Failing tests"
echo "-------------"
for folder in ${failing[@]}
do
  echo "currently in folder $prefix$folder"
  for file in $(ls $prefix$folder/*.js)
  do
    time {
    cp $file .
    filename=$(basename $file)
    name=${filename%%.*}
    echo "Next file: $folder/$filename"
    ./js2jsil.native -file $filename -cosette &> /dev/null
    ./jsil2rkt.native -file $name.jsil -js &> /dev/null
    res=$(racket $name.rkt | tail -n1)
    if [[ $res == "\"#f\"" ]]
    then
      echo "Pass: $filename"
    else
      echo "Fail: $filename"
    fi }
    echo "-----------------"
    sleep 1
  done
done
