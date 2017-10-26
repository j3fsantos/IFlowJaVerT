OCAMLBUILDFLAGS=-use-ocamlfind -verbose 1

# Please add new default build targets into sjsil.itarget, to improve build speed
default:
	ocamlbuild ${OCAMLBUILDFLAGS} sjsil.otarget

init: init_build
	.git-hooks/install.sh .

init_build: init_parser
	opam pin -y add JS_Parser "https://github.com/resource-reasoning/JS_Parser.git#002ecf9f28e8cdaf9683c39190e495403196fa7e"
	opam pin -yn add .
	opam install -y JavaScriptVerification --deps-only

init_parser:
	opam pin -y add JS_Parser-runtime "https://github.com/resource-reasoning/JS_Parser.git#002ecf9f28e8cdaf9683c39190e495403196fa7e"
	opam install -y JS_Parser-runtime

clean:
	ocamlbuild ${OCAMLBUILDFLAGS} -clean