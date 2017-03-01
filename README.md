# JSIL + Rosette 

A bug finding tool for JavaScript based on JSIL and Rosette. 

Prerequisites:

1. [opam 1.2.1 or higher] (https://opam.ocaml.org) 

2. [ocaml 4.03 or higher](http://caml.inria.fr/ocaml/index.en.html)
    Install OCaml using opam:
    
    `opam install ocaml`

3. [make init]
    Get the project dependencies:

    `make init`

4. [Z3](https://github.com/Z3Prover/z3)


5. [Racket 6.8](https://racket-lang.org)

6. [Rosette - Talia Ringer's version] (https://github.com/tlringer/rosette) 
	6.1 Add `string->integer integer->string` to the first provide
	    declaration in the files: rosette/base/core/string.rkt 
	    and rosette/base/base.rkt. 
    6.2 In the folder rosette run: 
        
       `raco pkg install`
       
       
To compile the OCaml code:

    make


To run: 

1. JS2JSIL: 
	`./js2jsil.native -file <file_name>`

2. JSIL2RKT: 
    `./jsil2rkt.native -file <file_name>`
   Use the flag `-js` if the JSIL program resulted from the compilation of a JavaScript program.
   
3. Racket Interpreter: 
   Open the result of JSIL2RKT in Dr.Racket and run. 
