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
#	opam pin -y add JS_Parser "https://github.com/resource-reasoning/JS_Parser.git#efd08be0a418c4f86954185b07f8c2b7ecd6e5c9"
	opam pin -y add JS_Parser ../JS_Parser


clean:
	ocamlbuild ${OCAMLBUILDFLAGS} -clean
