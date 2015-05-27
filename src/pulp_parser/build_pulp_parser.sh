#!/bin/bash

menhir ../pulp/parser/pulp_Parser.mly
ocamllex ../pulp/parser/pulp_Lexer.mll

#ocamlbuild -use-ocamlfind -package batteries -Is ../pulp/syntax,../pulp/parser,../logic,../syntax,../utils,../parser/src,. -use-menhir -menhir "menhir --external-tokens PulpLexer" ParserMain.native

ocamlfind ocamlc -g -c -package batteries -I ../parser/src -I . -I ../utils -I ../syntax -I ../logic -I ../pulp/parser -I ../pulp/syntax -o ../parser/src/parser_syntax.cmo ../parser/src/parser_syntax.ml

ocamlfind ocamlc -g -c -package batteries -I ../utils -I . -I ../syntax -I ../logic -I ../pulp/parser -I ../pulp/syntax -I ../parser/src -o ../utils/utils.cmo ../utils/utils.ml

ocamlfind ocamlc -g -c -package batteries -I ../syntax -I . -I ../utils -I ../logic -I ../pulp/parser -I ../pulp/syntax -I ../parser/src -o ../syntax/syntax.cmo ../syntax/syntax.ml

ocamlfind ocamlc -g -c -package batteries -I ../logic -I . -I ../utils -I ../syntax -I ../pulp/parser -I ../pulp/syntax -I ../parser/src -o ../logic/logic.cmo ../logic/logic.ml

ocamlfind ocamlc -g -c -package batteries -I ../pulp/syntax -I . -I ../utils -I ../syntax -I ../logic -I ../pulp/parser -I ../parser/src -o ../pulp/syntax/pulp_Syntax.cmo ../pulp/syntax/pulp_Syntax.ml

echo "building PulpParser"

ocamlfind ocamlc -g -c -package batteries -I . -I ../utils -I ../syntax -I ../logic -I ../pulp/parser -I ../pulp/syntax -I ../parser/src -o ../pulp/parser/pulp_Parser.cmi ../pulp/parser/pulp_Parser.mli

ocamlfind ocamlc -g -c -package batteries -I . -I ../utils -I ../syntax -I ../logic -I ../pulp/parser -I ../pulp/syntax -I ../parser/src -o ../pulp/parser/pulp_Parser.cmo ../pulp/parser/pulp_Parser.ml

echo "building PulpLexer"

ocamlfind ocamlc -g -c -package batteries -I test -I ../utils -I ../syntax -I ../logic -I ../pulp/parser -I ../pulp/syntax -I ../parser/src -o ../pulp/parser/pulp_Lexer.cmo ../pulp/parser/pulp_Lexer.ml

echo "building ParserMain"

ocamlfind ocamlc -g -c -package batteries -I . -I ../utils -I ../syntax -I ../logic -I ../pulp/parser -I ../pulp/syntax -I ../parser/src -o ParserMain.cmo ParserMain.ml

echo "Linking..."

ocamlfind ocamlc -g -linkpkg -package batteries -o ParserMain ../pulp/syntax/pulp_Syntax.cmo ../pulp/parser/pulp_Lexer.cmo ../pulp/parser/pulp_Parser.cmo ../utils/utils.cmo ../logic/logic.cmo ../syntax/syntax.cmo ../parser/src/parser_syntax.cmo ParserMain.cmo


