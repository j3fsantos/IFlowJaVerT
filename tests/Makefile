#
#

INCLUDES = -I ../lib/corestar \
	   -I ../src/ \
	   -I ../src/strategies/ \
	   -I ../src/formula_parser/ \
	   -I ../src/parser/src/ \
	   -I ../src/syntax/ \
	   -I ../src/logic/ \
	   -I ../src/utils/ \
	   -I ../src/pulp/ \
	   -I ../src/pulp/syntax/ \
	   -I ../src/pulp/interpreter/ \
	   -I ../src/pulp/simplifications/ \
		 -I ../src/pulp/logic \
		 -I ../src/pulp/logic/formula_parser \
	   -I ../src/strategies/store/

SOURCE = ../src/localconfig.ml \
	 ../src/utils/utils.ml \
	 ../src/utils/profiler.ml \
	 ../src/parser/src/parser_syntax.ml \
	 ../src/parser/src/parser.ml \
	 ../src/parser/src/pretty_print.ml \
	 ../src/parser/src/parser_main.ml \
	 ../src/syntax/syntax.ml \
	 ../src/parser/src/parser_syntax.ml \
	 ../src/syntax/translate_syntax.ml \
	 ../src/syntax/printSyntax.ml \
	 ../src/config.ml \
	 ../src/logic/logic.ml \
	 ../src/logic/printLogic.ml \
	 ../src/logic/logic_Utils.ml \
	 ../src/assert_Gen.ml \
	 ../src/abduction.ml \
	 ../src/graph.ml \
	 ../lib/corestar/corestar.cma \
	 ../src/corestar_frontend.ml \
	 ../src/inference_rules.ml \
	 ../src/strategies/store/store_rules.ml \
	 ../src/control_flow_graph.ml \
	 ../src/formula_parser/formula_parser.mli \
	 ../src/formula_parser/formula_parser.ml \
	 ../src/formula_parser/formula_lexer.ml \
	 ../src/formula_parser/formula_parser_utils.ml \
	 ../src/logic/udpreds.ml \
	 ../src/help.ml \
   ../src/pulp/simplifications/graphs.mli \
   ../src/pulp/simplifications/graphs.ml \
   ../src/pulp/logic/pulp_Abduct.ml \
   ../src/pulp/syntax/pulp_Syntax.ml \
   ../src/pulp/logic/pulp_Logic.ml \
   ../src/pulp/syntax/pulp_Procedure.ml \
   ../src/pulp/simplifications/simp_Common.ml \
   ../src/pulp/syntax/pulp_Syntax_Utils.ml \
   ../src/pulp/syntax/pulp_Syntax_Print.ml \
   ../src/pulp/simplifications/control_Flow.ml \
   ../src/pulp/logic/pulp_Logic_Print.ml \
   ../src/pulp/logic/state_Graph.ml \
   ../src/pulp/logic/pulp_Logic_Utils.ml \
   ../src/pulp/logic/pulp_Logic_Rules.ml \
   ../src/pulp/logic/coreStar_Frontend_Pulp.ml \
   ../src/pulp/logic/pulp_Sym_Exec.ml \
   ../src/pulp/logic/formula_parser/pulp_Formula_Parser.mli \
   ../src/pulp/logic/formula_parser/pulp_Formula_Parser.ml \
   ../src/pulp/logic/formula_parser/pulp_Formula_Lexer.ml \
   ../src/pulp/logic/formula_parser/pulp_Formula_Parser_Utils.ml \
   ../src/pulp/syntax/pulp_Translate.ml \
   ../src/pulp/interpreter/memory_Model.ml \
   ../src/pulp/interpreter/interpreter_Print.ml \
   ../src/pulp/interpreter/interpreter.ml \
   ../src/pulp/simplifications/basic_Blocks.ml \
   ../src/pulp/simplifications/reaching_Defs.ml \
   ../src/pulp/simplifications/simp_Main.ml \
   ../src/pulp/logic/pulp_SE_Print.ml \
   ../src/pulp/cfg.ml \
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
	 examples_tests.ml \
	 rec_examples.ml \
	 bin_op_tests.ml \
	 assert_Gen_Tests.ml \
	 pulp_Translation_Tests.ml \
	 pulp_Interpreter_Tests.ml \
	 pulp_Sym_Exec_Tests.ml \
	 test_all.ml

REMOVE = ../src/*.cmo \
	  ../src/*.cmi \
	  ../src/strategies/*.cmo \
	  ../src/strategies/*.cmi \
	  ../src/parser/src/*.cmo \
	  ../src/parser/src/*.cmi \
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
	  ../src/strategies/store/*.cmi \
	  ../src/pulp/syntax/*.cmo \
	  ../src/pulp/syntax/*.cmi \
	  ../src/pulp/interpreter/*.cmo \
    ../src/pulp/interpreter/*.cmi \
	  ../src/pulp/*.cmo \
	  ../src/pulp/*.cmi \
	  ../src/pulp/simplifications/*.cmo \
	  ../src/pulp/simplifications/*.cmi \

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
