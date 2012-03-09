all: tags parsing
	ocamlfind ocamlc -package batteries,unix,xml-light -linkpkg -I src/strategies/ -I src/printing -I src/ -I src/parsing src/localconfig.ml src/config.ml src/utils.ml src/syntax.ml src/logic.ml src/abduction.ml src/printing/printSyntax.ml src/printing/printLogic.ml src/graph.ml src/inference_rules.ml src/parser.ml src/symb_execution.ml src/example.ml src/control_flow_graph.ml src/strategies/store_naive.ml src/strategies/naive_strategy.ml src/strategies/store_finf.ml src/strategies/store_abduct.ml src/parsing/formula_parser.mli src/parsing/formula_parser.ml src/parsing/formula_lexer.ml src/main.ml -o main.byte
	rm src/*.cmo src/*.cmi src/strategies/*.cmo src/strategies/*.cmi src/printing/*.cmo src/printing/*.cmi
init:
	cp src/localconfig.default src/localconfig.ml
	cp config/config.default config/config.xml

tags:
	etags -R .

parsing:
	cd src/parsing && make

test:
	cd tests && make test
