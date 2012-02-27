all: tags
	ocamlfind ocamlc -package batteries,unix,xml-light -linkpkg -I src/strategies/ -I src/printing -I src/ src/localconfig.ml src/config.ml src/utils.ml src/syntax.ml src/logic.ml src/printing/printSyntax.ml src/printing/printLogic.ml src/graph.ml src/inference_rules.ml src/parser.ml src/symb_execution.ml src/example.ml src/control_flow_graph.ml src/strategies/store_naive.ml src/strategies/naive_strategy.ml src/strategies/store_finf.ml src/main.ml -o main.byte
	rm src/*.cmo
	rm src/*.cmi
	rm src/strategies/*.cmo
	rm src/strategies/*.cmi
	rm src/printing/*.cmo
	rm src/printing/*.cmi
init:
	cp src/localconfig.default src/localconfig.ml
	cp config/config.default config/config.xml

tags:
	etags -R .

test:
	cd tests ; make test
