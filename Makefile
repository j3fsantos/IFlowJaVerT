OCAMLBUILDFLAGS=-use-ocamlfind -verbose 1

# Please add new default build targets into sjsil.itarget, to improve build speed
default:
	ocamlbuild ${OCAMLBUILDFLAGS} sjsil.otarget

init: init_ci
	.git-hooks/install.sh .

init_ci: init_parser
	opam pin -yn add .
	opam install -y JavaScriptVerification --deps-only

init_parser:
	opam pin -y add JS_Parser "https://github.com/resource-reasoning/JS_Parser.git#448f3ff2c56188b7664c65e44ea98ec6561985a3"
#	opam pin -y add JS_Parser ../JS_Parser

clean:
	ocamlbuild ${OCAMLBUILDFLAGS} -clean
