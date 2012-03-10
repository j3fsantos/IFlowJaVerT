#
#

TESTS = test_all.ml logictests.ml

test: test_suite
	./test_suite

test_suite: $(TESTS)
	ocamlfind ocamlc -o test_suite -package batteries,oUnit,unix,xml-light -linkpkg -I ../src/ -I ../src/strategies/ -I ../src/printing/ -I ../src/parsing ../src/localconfig.ml ../src/config.ml ../src/utils.ml ../src/syntax.ml ../src/logic.ml ../src/abduction.ml ../src/printing/printSyntax.ml ../src/printing/printLogic.ml ../src/graph.ml ../src/inference_rules.ml ../src/parser.ml ../src/symb_execution.ml ../src/example.ml ../src/control_flow_graph.ml ../src/strategies/store_naive.ml ../src/strategies/naive_strategy.ml ../src/strategies/store_finf.ml ../src/strategies/store_abduct.ml ../src/parsing/formula_parser.mli ../src/parsing/formula_parser.ml ../src/parsing/formula_lexer.ml ../src/parsing/parsing_utils.ml logictests.ml parsing_tests.ml utils_tests.ml test_all.ml
	rm *.cmo *.cmi ../src/*.cmo ../src/*.cmi ../src/strategies/*.cmo ../src/strategies/*.cmi ../src/printing/*.cmo ../src/printing/*.cmi ../src/parsing/*.cmo ../src/parsing/*.cmi
