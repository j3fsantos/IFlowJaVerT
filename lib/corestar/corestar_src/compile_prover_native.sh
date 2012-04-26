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
