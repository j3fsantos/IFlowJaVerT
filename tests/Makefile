#
#

INCLUDES = -I ../lib/corestar \
	   -I ../src/ \
	   -I ../src/strategies/ \
	   -I ../src/printing/ \
	   -I ../src/parsing \
	   -I ../src/strategies/store/

SOURCE = ../src/localconfig.ml \
	 ../src/config.ml \
	 ../src/utils.ml \
	 ../src/syntax.ml \
	 ../src/logic.ml \
	 ../src/printing/printSyntax.ml \
	 ../src/printing/printLogic.ml \
	 ../src/logic_Utils.ml \
	 ../src/abduction.ml \
	 ../src/graph.ml \
	 ../lib/corestar/corestar.cma \
	 ../src/corestar_frontend.ml \
	 ../src/inference_rules.ml \
	 ../src/strategies/store/store_rules.ml \
	 ../src/parser.ml \
	 ../src/control_flow_graph.ml \
	 ../src/parsing/formula_parser.mli \
	 ../src/parsing/formula_parser.ml \
	 ../src/parsing/formula_lexer.ml \
	 ../src/parsing/parsing_utils.ml \
	 ../src/udpreds.ml \
	 ../src/help.ml \
	 ../src/strategies/store/store_naive.ml \
	 ../src/strategies/naive_strategy.ml \
	 ../src/strategies/naive_abduction.ml \
	 ../src/strategies/store/store_finf.ml \
	 ../src/strategies/store/store_abduct.ml \
	 ../src/symb_execution.ml \
	 ../src/strategies/rec_strategy.ml \
	 ../src/strategy.ml \
	 ../src/example.ml \
	 ../src/spec.ml \
	 paper_examples_tests.ml \
	 logictests.ml \
	 parsing_tests.ml \
	 utils_tests.ml \
	 examples_tests.ml \
	 rec_examples.ml \
	 parser_tests.ml \
	 bin_op_tests.ml \
	 test_all.ml

REMOVE = ../src/*.cmo \
	  ../src/*.cmi \
	  ../src/strategies/*.cmo \
	  ../src/strategies/*.cmi \
	  ../src/printing/*.cmo \
	  ../src/printing/*.cmi \
	  ../src/parsing/*.cmo \
	  ../src/parsing/*.cmi \
	  ../src/parsing/formula_lexer.ml \
	  ../src/parsing/formula_parser.ml \
	  ../src/parsing/formula_parser.mli \
	  ../src/strategies/store/*.cmo \
	  ../src/strategies/store/*.cmi

TESTS = test_all.ml logictests.ml

test: test_suite
	./test_suite

test_suite: $(TESTS) parsing
	ocamlfind ocamlc -o test_suite -package batteries,oUnit,unix,xml-light,dynlink -linkpkg $(INCLUDES) $(SOURCE)
	rm *.cmo *.cmi $(REMOVE)

parsing:
	cd ../src/parsing && make
