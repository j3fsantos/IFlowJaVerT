INCLUDES = -I lib/corestar \
	   -I src/strategies/ \
	   -I src/ \
	   -I src/formula_parser \
	   -I src/coq/ \
	   -I src/parser/ \
	   -I src/syntax/ \
	   -I src/logic/ \
	   -I src/utils/ \
	   -I src/strategies/store

SOURCE1 = src/localconfig.ml \
	 src/utils/utils.ml \
	 src/syntax/syntax.ml \
	 src/syntax/printSyntax.ml \
	 src/coq/coq_syntax.ml \
	 src/parser/parser.ml \
	 src/coq/coq_parser.ml \
	 src/parser/parser_main.ml \
	 src/config.ml \
	 src/logic/logic.ml \
	 src/logic/printLogic.ml \
	 src/logic/logic_Utils.ml \
	 src/assert_Gen.ml \
	 src/abduction.ml \
	 src/graph.ml

SOURCE2_byte = lib/corestar/corestar.cma

SOURCE2_native = lib/corestar/corestar_src/_build/corestar.cmx

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
	 src/main.ml

REMOVE = src/*.cmo \
	 src/*.cmi \
	 src/strategies/*.cmo \
	 src/strategies/*.cmi \
	 src/coq/*.cmo \
	 src/coq/*.cmi \
	 src/parser/*.cmo \
	 src/parser/*.cmi \
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

NATIVE_REMOVE = src/*.cmx \
	src/*.o \
	src/formula_parser/*.cmx \
	src/formula_parser/*.o \
	src/coq/*.cmx \
	src/coq/*.o \
	src/parser/*.cmx \
	src/parser/*.o \
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
	ocamlfind ocamlc -g -package batteries,unix,xml-light,dynlink -linkpkg $(INCLUDES) $(SOURCE1) $(SOURCE2_byte) $(SOURCE3) -o main.byte
	rm $(REMOVE)
init:
	cp src/localconfig.default src/localconfig.ml
	cp config/config.default config/config.xml

clean:
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
