echo "Compiling to jsil."
./js2jsil_main.byte -file symbolic/$1.js
echo "Compiling to racket."
./jsil2rkt.byte -file symbolic/$1.jsil -js 
echo "Moving file."
mv symbolic/$1.rkt .
echo "Running racket." 
racket $1.rkt
