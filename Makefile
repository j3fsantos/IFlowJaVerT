OCAMLBUILDFLAGS=-use-ocamlfind -verbose 1

# Please add new default build targets into sjsil.itarget, to improve build speed
default:
	#ocamlbuild -use-ocamlfind src/pulp/interpreter/interpreter_run.byte
	#ocamlbuild -use-ocamlfind src/pulp/interpreter/interpreter_run.d.byte
	#ocamlbuild -use-ocamlfind src/pulp/interpreter/interpreter_run.native
	#ocamlbuild -use-ocamlfind tests/test_interpreter.byte
	#ocamlbuild -use-ocamlfind src/pulp/syntax/translate.byte
	#ocamlbuild -use-ocamlfind tests/spec_Functions_Tests.byte
	#ocamlbuild -use-ocamlfind src/pulp/SJSIL/symb_execution_main.byte
	ocamlbuild ${OCAMLBUILDFLAGS} sjsil.otarget

init: init_ci
	.git-hooks/install.sh .

init_ci: init_parser
	opam pin -yn add .
	opam install -y JavaScriptVerification --deps-only

init_parser:
	opam pin -y add JS_Parser "https://github.com/resource-reasoning/JS_Parser.git#a14ec0ea99141953e50a8c1dbdc51dfe809a083f"

clean:
	ocamlbuild ${OCAMLBUILDFLAGS} -clean