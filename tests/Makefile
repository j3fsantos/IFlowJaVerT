#
#

INCLUDES = -I ../lib/corestar \
	   -I ../src/ \
	   -I ../src/strategies/ \
	   -I ../src/formula_parser/ \
	   -I ../src/coq/ \
	   -I ../src/parser/ \
	   -I ../src/syntax/ \
	   -I ../src/logic/ \
	   -I ../src/utils/ \
	   -I ../src/strategies/store/

SOURCE = ../src/localconfig.ml \
	 ../src/config.ml \
	 ../src/utils/utils.ml \
	 ../src/syntax/syntax.ml \
	 ../src/logic/logic.ml \
	 ../src/syntax/printSyntax.ml \
	 ../src/logic/printLogic.ml \
	 ../src/logic/logic_Utils.ml \
	 ../src/assert_Gen.ml \
	 ../src/abduction.ml \
	 ../src/graph.ml \
	 ../lib/corestar/corestar.cma \
	 ../src/corestar_frontend.ml \
	 ../src/inference_rules.ml \
	 ../src/strategies/store/store_rules.ml \
	 ../src/coq/coq_syntax.ml \
	 ../src/parser/parser.ml \
	 ../src/coq/coq_parser.ml \
	 ../src/parser/parser_main.ml \
	 ../src/control_flow_graph.ml \
	 ../src/formula_parser/formula_parser.mli \
	 ../src/formula_parser/formula_parser.ml \
	 ../src/formula_parser/formula_lexer.ml \
	 ../src/formula_parser/formula_parser_utils.ml \
	 ../src/logic/udpreds.ml \
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
	 formula_parser_tests.ml \
	 utils_tests.ml \
	 examples_tests.ml \
	 rec_examples.ml \
	 parser_tests.ml \
	 bin_op_tests.ml \
	 assert_Gen_Tests.ml \
	 test_all.ml

REMOVE = ../src/*.cmo \
	  ../src/*.cmi \
	  ../src/strategies/*.cmo \
	  ../src/strategies/*.cmi \
	  ../src/coq/*.cmo \
	  ../src/coq/*.cmi \
	  ../src/parser/*.cmo \
	  ../src/parser/*.cmi \
	  ../src/syntax/*.cmo \
	  ../src/syntax/*.cmi \
	  ../src/logic/*.cmo \
	  ../src/logic/*.cmi \
	  ../src/utils/*.cmo \
	  ../src/utils/*.cmi \
	  ../src/formula_parser/*.cmo \
	  ../src/formula_parser/*.cmi \
	  ../src/formula_parser/formula_lexer.ml \
	  ../src/formula_parser/formula_parser.ml \
	  ../src/formula_parser/formula_parser.mli \
	  ../src/strategies/store/*.cmo \
	  ../src/strategies/store/*.cmi

TESTS = test_all.ml logictests.ml

test: test_suite
ifdef TST
	./test_suite -only-test $(TST)
else
	./test_suite
endif

test_suite: $(TESTS) parsing
	ocamlfind ocamlc -o test_suite -package batteries,oUnit,unix,xml-light,dynlink -linkpkg $(INCLUDES) $(SOURCE)
	rm *.cmo *.cmi $(REMOVE)

parsing:
	cd ../src/formula_parser && make
