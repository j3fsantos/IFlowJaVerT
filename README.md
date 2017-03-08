# JaVerT

This is a verification tool for JavaScript programs. 

Prerequisites:

1. [opam 1.2.1 or higher] (https://opam.ocaml.org) 

2. [ocaml 4.03 or higher](http://caml.inria.fr/ocaml/index.en.html)
    Install OCaml using opam:
    
    `opam install ocaml`

3. [make init]
    Get the project dependencies:

    `make init`

4. [Z3](https://github.com/Z3Prover/z3)
    Install Z3 with the **OCaml bindings**.


To compile: 

    make

To run: 

1.  Setup the running environment: 
    `./setup_environment.sh`
    If inside the environment folder: 
    `./remake.sh`
    
Inside the **environment folder** after step 1: 

2.  JSIL Interpreter: 
	`./jsil.native -file <file_name>.jsil`
    The output of the execution is written to the console. 

3.  JS2JSIL: 
	`./js2jsil.native -file <file_name>.js`
    Use the flag `-logic` if the compiled JSIL file will be given as input to JSILVerify. 
    The compiled code will be written to <file_name>.jsil. 

4.  JSILVerify: 
	`./jsilverify.native -file <file_name>.jsil` 
    Use the flag `-js` if the JSIL program resulted from the compilation of a JavaScript program.
    The symbolic execution traces will be written to the console. 



