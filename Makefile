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
	opam pin -y add JS_Parser "https://github.com/resource-reasoning/JS_Parser.git#eb1cd571263b01860b0ff5cbfe5fbaac8c1a04e8"
#	opam pin -y add JS_Parser ../JS_Parser


clean:
	ocamlbuild ${OCAMLBUILDFLAGS} -clean
