all: tags
	ocamlfind ocamlc -package batteries,unix,xml-light -linkpkg -I strategies/ -I printing localconfig.ml config.ml utils.ml syntax.ml logic.ml printing/printSyntax.ml printing/printLogic.ml graph.ml inference_rules.ml parser.ml symb_execution.ml example.ml control_flow_graph.ml strategies/store_naive.ml strategies/naive_strategy.ml main.ml -o main.byte

init:
	cp localconfig.default localconfig.ml
	cp config/config.default config/config.xml

tags:
	etags -R .
