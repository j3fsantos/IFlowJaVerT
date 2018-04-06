#!/bin/bash

# copy file to current folder
cp $1 .
#echo "filename:" $1
filename=$(basename $1)
#echo "basename:" $filename
name=${filename%%.*}
#echo $name
jname=$name'.jsil'
#echo $jname
rname=$name'.rkt'
#echo $rname
./js2jsil.native -file "$filename" -cosette -line_numbers &> /dev/null
./jsil2rkt.native -file "$jname" -js 
logname=res_$name.txt
racket $rname > $logname
tail -n 12 $logname
mv models.json $name"_models.json"
mv coverage.txt $name"_coverage.txt"
