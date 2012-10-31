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

1.  `make init`
2.  Set config options so they make sense on your system.

        $EDITOR localconfig.ml
        $EDITOR config/config.xml

3.  `make all`

