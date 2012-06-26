INCLUDES = -I lib/corestar \
	   -I src/strategies/ \
	   -I src/printing \
	   -I src/ \
	   -I src/parsing \
	   -I src/strategies/store

SOURCE = src/localconfig.ml \
	 src/config.ml \
	 src/utils.ml \
	 src/syntax.ml \
	 src/logic.ml \
	 src/printing/printSyntax.ml \
	 src/printing/printLogic.ml \
	 src/logic_Utils.ml \
	 src/abduction.ml \
	 src/graph.ml \
	 lib/corestar/corestar.cma \
	 src/corestar_frontend.ml \
	 src/inference_rules.ml \
	 src/strategies/store/store_rules.ml \
	 src/parser.ml \
	 src/control_flow_graph.ml \
	 src/parsing/formula_parser.mli \
	 src/parsing/formula_parser.ml \
	 src/parsing/formula_lexer.ml \
	 src/parsing/parsing_utils.ml \
         src/udpreds.ml \
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
	 src/printing/*.cmo \
	 src/printing/*.cmi \
	 src/parsing/*.cmo \
	 src/parsing/*.cmi \
	 src/parsing/formula_lexer.ml \
	 src/parsing/formula_parser.ml \
	 src/parsing/formula_parser.mli \
	 src/strategies/store/*.cmo \
	 src/strategies/store/*.cmi

NATIVE_REMOVE = src/*.cmx \
	src/*.o \
	src/parsing/*.cmx \
	src/parsing/*.o \
	src/strategies/*.cmx \
	src/strategies/*.o \
	src/strategies/store/*.cmx \
	src/strategies/store/*.o

all: tags parsing $(SOURCE)
	ocamlfind ocamlc -g -package batteries,unix,xml-light,dynlink -linkpkg $(INCLUDES) $(SOURCE) -o main.byte
	rm $(REMOVE)
init:
	cp src/localconfig.default src/localconfig.ml
	cp config/config.default config/config.xml

tags:
	etags -R .

parsing:
	cd src/parsing && make

lib/corestar/corestar.cma:
	cd lib/corestar/corestar_src;\
	./compile_prover.sh;\
	cp _build/corestar.cma _build/corestar.cmi ..

test:
	cd tests && make test

native:
	ocamlfind ocamlopt -g -package batteries,unix,xml-light,dynlink -linkpkg -I lib/corestar -I src/strategies/ -I src/printing -I src/ -I src/parsing -I src/strategies/store src/localconfig.ml src/config.ml src/utils.ml src/syntax.ml src/logic.ml src/printing/printSyntax.ml src/printing/printLogic.ml src/logic_Utils.ml src/abduction.ml src/graph.ml lib/corestar/corestar_src/_build/corestar.cmx src/corestar_frontend.ml src/inference_rules.ml src/strategies/store/store_rules.ml src/parser.ml src/control_flow_graph.ml src/parsing/formula_parser.mli src/parsing/formula_parser.ml src/parsing/formula_lexer.ml src/parsing/parsing_utils.ml src/strategies/store/store_naive.ml src/strategies/naive_strategy.ml src/strategies/naive_abduction.ml src/strategies/store/store_finf.ml src/strategies/store/store_abduct.ml src/symb_execution.ml src/example.ml src/spec.ml src/main.ml -o main.native
	rm $(NATIVE_REMOVE)
