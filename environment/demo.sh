./js2jsil_main.byte -file example.js
./SJSIL_Parser_main.byte -file example.jsil -sexpr
cp *.rkt ../racket/
open ../racket/example.rkt
