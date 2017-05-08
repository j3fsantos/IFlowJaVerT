OCAMLBUILDFLAGS=-use-ocamlfind -verbose 1

# Please add new default build targets into sjsil.itarget, to improve build speed
default:
	ocamlbuild ${OCAMLBUILDFLAGS} sjsil.otarget

init: init_ci
	.git-hooks/install.sh .
	echo "Now install Z3"

init_ci: init_parser
	opam pin -yn add .
	opam install -y JavaScriptVerification --deps-only

init_parser:
#	opam pin -y add JS_Parser "https://github.com/resource-reasoning/JS_Parser.git#c775ee9922fed3bfd4a6beea5a8d162f1253229c"
	opam pin -y add JS_Parser ../JS_Parser

clean:
	ocamlbuild ${OCAMLBUILDFLAGS} -clean
