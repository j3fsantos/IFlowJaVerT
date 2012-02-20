#
#

TESTS = test_all.ml logictests.ml

test: test_suite
	./test_suite

test_suite: $(TESTS)
	ocamlfind ocamlc -o test_suite -package batteries,oUnit,unix,xml-light -linkpkg -I .. -I ../strategies/ ../localconfig.ml ../config.ml ../utils.ml ../syntax.ml ../logic.ml ../graph.ml ../inference_rules.ml ../parser.ml ../symb_execution.ml ../example.ml ../control_flow_graph.ml ../strategies/store_naive.ml ../strategies/naive_strategy.ml logictests.ml test_all.ml
