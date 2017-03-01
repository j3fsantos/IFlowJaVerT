# JaVerT

This is a verification tool for JavaScript programs. 

Prerequisites:

1. [opam 1.2.1 or higher] (https://opam.ocaml.org) 

2. [ocaml 4.03 or higher]([http://caml.inria.fr/ocaml/index.en.html)
    Install OCaml using opam:
    
    `opam install ocaml`

3. [make init]
    Get the project dependencies:

    `make init`

4. [Z3](https://github.com/Z3Prover/z3)
    Install Z3 **with** the OCaml bindings.


To compile: 

    `make`

To run:

0.  JSIL Interpreter: `./jsil.native -file <file_name>`
1.  JSILVerify: `./jsilverify.native -file <file_name>` 
    (use the flag `-js` if the jsil program resulted from the compilation of a JavaScript program)
3.  JS2JSIL: `./js2jsil -file <file_name`
    (use the flag `-logic` if the compiled jsil file will be given as input to JSILVerify) 




