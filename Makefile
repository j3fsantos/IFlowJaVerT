all: tags parsing
	ocamlfind ocamlc -g -package batteries,unix,xml-light -linkpkg -I src/strategies/ -I src/printing -I src/ -I src/parsing -I src/strategies/store src/localconfig.ml src/config.ml src/utils.ml src/syntax.ml src/logic.ml src/printing/printSyntax.ml src/printing/printLogic.ml src/logic_Utils.ml src/abduction.ml src/graph.ml src/inference_rules.ml src/strategies/store/store_rules.ml src/parser.ml src/symb_execution.ml src/example.ml src/control_flow_graph.ml src/strategies/store/store_naive.ml src/strategies/naive_strategy.ml src/strategies/store/store_finf.ml src/strategies/store/store_abduct.ml src/parsing/formula_parser.mli src/parsing/formula_parser.ml src/parsing/formula_lexer.ml src/parsing/parsing_utils.ml src/main.ml -o main.byte
	rm src/*.cmo src/*.cmi src/strategies/*.cmo src/strategies/*.cmi src/printing/*.cmo src/printing/*.cmi src/parsing/*.cmo src/parsing/*.cmi src/strategies/store/*.cmo src/strategies/store/*.cmi
init:
	cp src/localconfig.default src/localconfig.ml
	cp config/config.default config/config.xml

tags:
	etags -R .

parsing:
	cd src/parsing && make

test:
	cd tests && make test
