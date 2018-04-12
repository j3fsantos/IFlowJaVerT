#!/bin/bash

# copy file to current folder
cp $1 .

filename=$(basename $1)
name=${filename%%.*}
jsilname=$name'.jsil'
rktname=$name'.rkt'
logname=res_$name.txt

./js2jsil.native -file "$filename" -cosette -line_numbers &> /dev/null
./jsil2rkt.native -file "$jsilname" -js 
racket $rktname > $logname
tail -n 12 $logname

mv models.json $name"_models.json"
mv coverage.txt $name"_raw_coverage.txt"
python3 coverage.py $filename > $name"_coverage.txt"
