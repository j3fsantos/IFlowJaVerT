#!/bin/bash
mkdir -p environment
cp racket/mem_model.rkt environment
cp racket/interpreter.rkt environment 
cp racket/util.rkt environment
cp racket/internals_racket.rkt environment 
cp racket/assertions.rkt environment
cp ocaml/js2jsil/runtime/*.jsil environment
cp ocaml/js2jsil/runtime/harness.js environment
cp js2jsil.native environment
cp jsil2rkt.native environment
cp remake.sh environment
