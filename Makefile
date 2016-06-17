default:
	#ocamlbuild -use-ocamlfind src/pulp/interpreter/interpreter_run.byte
	#ocamlbuild -use-ocamlfind src/pulp/interpreter/interpreter_run.d.byte
	#ocamlbuild -use-ocamlfind src/pulp/interpreter/interpreter_run.native
	#ocamlbuild -use-ocamlfind tests/test_interpreter.byte
	#ocamlbuild -use-ocamlfind src/pulp/syntax/translate.byte
	#ocamlbuild -use-ocamlfind tests/spec_Functions_Tests.byte
	ocamlbuild -use-ocamlfind -verbose 1 src/pulp/SJSIL/SJSIL_Parser_main.byte
	ocamlbuild -use-ocamlfind -verbose 1 src/pulp/SJSIL/SJSIL_Parser_main.native
	ocamlbuild -use-ocamlfind -verbose 1 src/pulp/SJSIL/tests/test_main.byte
	ocamlbuild -use-ocamlfind src/pulp/SJSIL/js2jsil_main.byte
	ocamlbuild -use-ocamlfind src/pulp/SJSIL/js2jsil_main.native

init:
	cp src/localconfig.default src/localconfig.ml
	cp config/config.default config/config.xml
	git submodule update --init src/parser
	opam install batteries xml-light extlib menhir ounit



# Old Makefile below

INCLUDES = -I lib/corestar \
	   -I src/strategies/ \
	   -I src/ \
	   -I src/formula_parser \
	   -I src/parser/src \
	   -I src/parser/_build/src \
	   -I src/syntax/ \
	   -I src/logic/ \
	   -I src/utils/ \
	   -I src/strategies/store \
     -I src/pulp \
     -I src/pulp/syntax \
     -I src/pulp/interpreter \
     -I src/pulp/simplifications \
     -I src/pulp/logic \
     -I src/pulp/logic/formula_parser

SOURCE1 = src/localconfig.ml \
	 src/utils/utils.ml \
	 src/utils/profiler.ml \
	 src/parser/src/pretty_print.ml \
	 src/parser/src/parser_syntax.ml \
	 src/parser/src/parser.ml \
	 src/parser/src/parser_main.ml \
	 src/syntax/syntax.ml \
	 src/parser/src/parser_syntax.ml \
	 src/syntax/translate_syntax.ml \
	 src/syntax/printSyntax.ml \
	 src/config.ml \
	 src/logic/logic.ml \
	 src/logic/printLogic.ml \
	 src/logic/logic_Utils.ml \
	 src/assert_Gen.ml \
	 src/abduction.ml \
	 src/graph.ml

SOURCE2_byte = lib/corestar/corestar.cma

SOURCE2_native = lib/corestar/corestar_src/_build/corestar.cmx

   #src/pulp/logic/pulp_Analysis_Main.ml
   #src/pulp/interpreter/interpreter_run.ml
	 #src/main.ml
SOURCE3 = src/corestar_frontend.ml \
	 src/inference_rules.ml \
	 src/strategies/store/store_rules.ml \
	 src/control_flow_graph.ml \
	 src/formula_parser/formula_parser.mli \
	 src/formula_parser/formula_parser.ml \
	 src/formula_parser/formula_lexer.ml \
	 src/formula_parser/formula_parser_utils.ml \
	 src/logic/udpreds.ml \
	 src/help.ml \
	 src/strategies/store/store_naive.ml \
	 src/strategies/naive_strategy.ml \
	 src/strategies/naive_abduction.ml \
	 src/strategies/store/store_finf.ml \
	 src/strategies/store/store_abduct.ml \
	 src/symb_execution.ml \
	 src/strategies/rec_strategy.ml \
	 src/strategy.ml \
	 src/example.ml \
	 src/spec.ml \
   src/pulp/simplifications/graphs.mli \
   src/pulp/simplifications/graphs.ml \
   src/pulp/logic/pulp_Abduct.ml \
   src/pulp/syntax/pulp_Syntax.ml \
   src/pulp/logic/pulp_Logic.ml \
   src/pulp/syntax/pulp_Procedure.ml \
   src/pulp/simplifications/simp_Common.ml \
   src/pulp/syntax/pulp_Syntax_Utils.ml \
   src/pulp/syntax/pulp_Syntax_Print.ml \
   src/pulp/simplifications/control_Flow.ml \
   src/pulp/logic/pulp_Logic_Print.ml \
   src/pulp/logic/state_Graph.ml \
   src/pulp/logic/pulp_Logic_Utils.ml \
   src/pulp/logic/pulp_Logic_Rules.ml \
   src/pulp/logic/coreStar_Frontend_Pulp.ml \
   src/pulp/logic/pulp_Sym_Exec.ml \
   src/pulp/logic/formula_parser/pulp_Formula_Parser.mli \
   src/pulp/logic/formula_parser/pulp_Formula_Parser.ml \
   src/pulp/logic/formula_parser/pulp_Formula_Lexer.ml \
   src/pulp/logic/formula_parser/pulp_Formula_Parser_Utils.ml \
   src/pulp/syntax/pulp_Translate.ml \
   src/pulp/interpreter/memory_Model.ml \
   src/pulp/interpreter/interpreter_Print.ml \
   src/pulp/interpreter/interpreter.ml \
   src/pulp/simplifications/basic_Blocks.ml \
   src/pulp/simplifications/reaching_Defs.ml \
   src/pulp/simplifications/simp_Main.ml \
   src/pulp/syntax/translate.ml \
   src/pulp/logic/pulp_SE_Print.ml

REMOVE = src/*.cmo \
	 src/*.cmi \
	 src/strategies/*.cmo \
	 src/strategies/*.cmi \
	 src/parser/src/*.cmo \
	 src/parser/src/*.cmi \
	 src/syntax/*.cmo \
	 src/syntax/*.cmi \
	 src/logic/*.cmo \
	 src/logic/*.cmi \
	 src/utils/*.cmo \
	 src/utils/*.cmi \
	 src/formula_parser/*.cmo \
	 src/formula_parser/*.cmi \
	 src/formula_parser/formula_lexer.ml \
	 src/formula_parser/formula_parser.ml \
	 src/formula_parser/formula_parser.mli \
	 src/strategies/store/*.cmo \
	 src/strategies/store/*.cmi

BUILD_DIR = _build

REMOVE_COMPILED = interpreter_run.byte \
	interpreter_run.d.byte \
	interpreter_run.native \
	test_interpreter.byte \
	translate.byte

NATIVE_REMOVE = src/*.cmx \
	src/*.o \
	src/formula_parser/*.cmx \
	src/formula_parser/*.o \
	src/parser/src/*.cmx \
	src/parser/src/*.o \
	src/syntax/*.cmx \
	src/syntax/*.o \
	src/logic/*.cmx \
	src/logic/*.o \
	src/utils/*.cmx \
	src/utils/*.o \
	src/strategies/*.cmx \
	src/strategies/*.o \
	src/strategies/store/*.cmx \
	src/strategies/store/*.o

byte: tags parsing $(SOURCE1) $(SOURCE2_byte) $(SOURCE3)
	ocamlfind ocamlc -g -package batteries,unix,xml-light,dynlink -linkpkg $(INCLUDES) $(SOURCE1) $(SOURCE2_byte) $(SOURCE3) -o translate.byte
	rm $(REMOVE)
clean:
	ocamlbuild -clean
	rm $(REMOVE_COMPILED)
	rm -rf $(BUILD_DIR)
	rm $(REMOVE)

tags:
	etags -R .

parsing:
	cd src/formula_parser && make

lib/corestar/corestar.cma:
	cd lib/corestar/corestar_src;\
	./compile_prover.sh;\
	cp _build/corestar.cma _build/corestar.cmi ..

test:
	cd tests && make test

native: parsing $(SOURCE1) $(SOURCE2_native) $(SOURCE3)
	ocamlfind ocamlopt -g -package batteries,unix,xml-light,dynlink -linkpkg $(INCLUDES) $(SOURCE1) $(SOURCE2_native) $(SOURCE3) -o main.native
	rm $(NATIVE_REMOVE)

lib/corestar/corestar_src/_build/corestar.cmx:
	cd lib/corestar/corestar_src/ && ./compile_prover_native.sh
