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
	opam pin -y add JS_Parser "https://github.com/resource-reasoning/JS_Parser.git#0b9d043792661400b9260c34bc4c5ef6f535734c"
#	opam pin -y add JS_Parser ../JS_Parser

clean:
	ocamlbuild ${OCAMLBUILDFLAGS} -clean
