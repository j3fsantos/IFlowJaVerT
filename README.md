# JavaScript Analyser

This is a verification tool for JavaScript programs. In time it will
plug into eclipse, emacs and verification web services, to make
writing correct, fast JavaScript easier to do.

Prerequisites:

1. [ocaml 3.11 or higher]([http://caml.inria.fr/ocaml/index.en.html)
    You can get this in ubuntu with:

    `sudo apt-get install ocaml`

2. [the XML-light library](http://tech.motion-twin.com/xmllight)
    You can get this in ubuntu with:

    `sudo apt-get install libxml-light-ocaml-dev`

3. [ocaml batteries included](http://batteries.forge.ocamlcore.org/)
    You can get this in ubuntu with:

    `sudo apt-get install ocaml-batteries-included`

4. [The ocaml unit testing library OUnit](http://ounit.forge.ocamlcore.org/)
    You can get this in ubuntu with:

    `sudo apt-get install libounit-ocaml-dev`

5. [Java](http://www.oracle.com/technetwork/java/index.html )
    You can get this in ubuntu with:

    `sudo apt-get install java7-jdk`

6. [xdot](http://code.google.com/p/jrfonseca/wiki/XDot)
    You can get this in ubuntu with:

    `sudo apt-get install xdot`

7. [etags](http://ctags.sourceforge.net/)
    You can get this in ubuntu with:

    `sudo apt-get install exuberant-ctags`

To build:

0.  `git submodule init && git submodule update`
1.  `cd JS_Symbolic_Debugger && make init`
2.  Set config options so they make sense on your system.

        $EDITOR src/localconfig.ml
        $EDITOR config/config.xml

3.  `make all`

Updated Instructions


1) Obtain the code of the compiler: 
	i) git clone https://github.com/resource-reasoning/JS_Symbolic_Debugger.git
	ii) git submodule init && git submodule update

2) Obtain the OCaml package manager and install OCaml (brew is required)
	i) brew install opam
	ii) opam switch 4.02.1
	iii) eval `opam config env`

3) Obtain the OCaml libraries required for the code:
	i) opam install batteries
	ii) opam install core
	iii) opam xml-light
	iv) opam install oUnit=1.1.2 (the compiler only works with this version of the library)

4) Configure Eclipse (Eclipse for RCP and RAP developers, Version: Luna Service Release 2)
	i) Add OCaml plugin to Eclipse 
    	* Help -> Eclipse MarketPlace -> OcaIDE
    	
    ii) Add EGit
      	* Help -> Eclipse MarketPlace -> EGit

    iii) Compile Corestar
        * Go to the directory PROJECT_PATH/lib/corestar
        E.g. PROJECT_PATH = /Users/josesantos/projects/JS_Symbolic_Debugger/JS_Symbolic_Debugger

        * Run the script compile_prover.sh

        * Verify whether the file _build was created in the folder PROJECT_PATH/lib/corestar/corestar_src

    iv) Set the parameters for compiling the project
        * JS_Symbolic_Debugger -> Properties 

        * Select Properties Menu

        * Targets: main.byte,interpreter_run.byte,translate.byte,test_all.byte

        * Libraries: xml-light,unix,oUnit,nums,str,bigarray,camomile,batteries,dynlink,corestar

        * Compiler Flags: -I OUNIT_PATH/oUnit -I XMLLIGHT_PATH/xml-light -I CAMOMILE_PATH/camomile -I BATTERIES_PATH/batteries -I PROJECT_PATH/lib/corestar/corestar_src/_build
        E.g. BATTERIES_PATH = /Users/josesantos/.opam/4.02.1/lib/batteries
            * To find the path of a library use: ocamlfind query LIBNAME
            E.g. ocamlfind query batteries 

        * Linker Flags: -I OUNIT_PATH/oUnit -I XMLLIGHT_PATH/xml-light -I CAMOMILE_PATH/camomile -I BATTERIES_PATH/batteries -I PROJECT_PATH/lib/corestar/corestar_src/_build

    v) Set the config file
        * Create the file config.xml in the folder PROJECT_PATH/config

        * Copy the contents of the file config.default to the file config.xml

        * Set the value of the attribute "location" of the node JS_TO_XML_PARSER to 
          the path of the xml parser

        * Set the value of the node LOGIC_DIR to the absolute path to the library 
          logic: PROJECT_PATH/lib/logic/

        * Set the value of the attribute "path" of the node SMT to the absolute 
          path to the binary of Z3



