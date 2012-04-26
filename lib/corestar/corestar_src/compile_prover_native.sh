ocamlbuild \
   -lflag "-for-pack Corestar" \
   -I src/utils \
   -I src/utils/_build/ \
   -I src/prover_syntax \
   -I src/plugin_interface \
   -I src/prover \
   -I src/symbexe_syntax \
   -I src/parsing \
   corestar.cmx

# touch corestar.mli  ; if  /usr/bin/ocamlopt -pack -I src/utils -I src/prover_syntax -I src/prover -I src/plugin_interface -I src/symbexe_syntax -I src/parsing src/utils/backtrack.cmx src/utils/config.cmx src/utils/corestar_std.cmx src/utils/debug.cmx src/utils/system.cmx src/utils/cli_utils.cmx src/utils/dot.cmx src/utils/load.cmx src/utils/misc.cmx src/utils/multiset.cmx src/utils/persistentarray.cmx src/utils/printing.cmx src/utils/vars.cmx src/prover_syntax/psyntax.cmx src/prover/congruence.cmx src/prover/cterm.cmx src/prover/clogic.cmx src/prover/smtsyntax.cmx src/prover/smtparse.cmx src/prover/smtlex.cmx src/prover/smt.cmx src/prover/prover.cmx src/plugin_interface/plugin.cmx src/plugin_interface/registry.cmx src/plugin_interface/plugin_callback.cmx src/plugin_interface/plugin_manager.cmx src/prover/sepprover.cmx src/symbexe_syntax/spec.cmx src/symbexe_syntax/core.cmx src/parsing/parser.cmx src/parsing/lexer.cmx src/parsing/load_logic.cmx -o corestar.cmx  ; then  rm -f corestar.mli  ; else  rm -f corestar.mli  ; exit 1; fi
# + touch corestar.mli  ; if  /usr/bin/ocamlopt -pack -I src/utils -I src/prover_syntax -I src/prover -I src/plugin_interface -I src/symbexe_syntax -I src/parsing src/utils/backtrack.cmx src/utils/config.cmx src/utils/corestar_std.cmx src/utils/debug.cmx src/utils/system.cmx src/utils/cli_utils.cmx src/utils/dot.cmx src/utils/load.cmx src/utils/misc.cmx src/utils/multiset.cmx src/utils/persistentarray.cmx src/utils/printing.cmx src/utils/vars.cmx src/prover_syntax/psyntax.cmx src/prover/congruence.cmx src/prover/cterm.cmx src/prover/clogic.cmx src/prover/smtsyntax.cmx src/prover/smtparse.cmx src/prover/smtlex.cmx src/prover/smt.cmx src/prover/prover.cmx src/plugin_interface/plugin.cmx src/plugin_interface/registry.cmx src/plugin_interface/plugin_callback.cmx src/plugin_interface/plugin_manager.cmx src/prover/sepprover.cmx src/symbexe_syntax/spec.cmx src/symbexe_syntax/core.cmx src/parsing/parser.cmx src/parsing/lexer.cmx src/parsing/load_logic.cmx -o corestar.cmx  ; then  rm -f corestar.mli  ; else  rm -f corestar.mli  ; exit 1; fi
