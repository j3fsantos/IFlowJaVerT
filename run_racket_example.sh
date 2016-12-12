./js2jsil_main.byte -file symbolic/$1.js
./jsil2rkt.byte -file symbolic/$1.jsil -js 
cp symbolic/$1.rkt . 
racket $1.rkt
