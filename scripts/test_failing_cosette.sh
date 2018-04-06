#! /bin/bash

# run it from the environment folder

prefix="../src/Cosette/tests/"

declare -a failing=("jasonsjones/failing" \
                    "javert/failing" \
                    "symbolic/failing")



echo "Running Cosette tests"
echo "---------------------"

echo "Failing tests"
echo "-------------"
for folder in ${failing[@]}
do
  echo "currently in folder $prefix$folder"
  for file in $(ls $prefix$folder/*.js)
  do
    cp $file .
    filename=$(basename $file)
    name=${filename%%.*}
    echo "Next file: $folder/$filename"
    ./js2jsil.native -file $filename -cosette &> /dev/null
    ./jsil2rkt.native -file $name.jsil -js &> /dev/null
    time {
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
