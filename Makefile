all: tags
	ocamlbuild -classic-display -I strategies -tags dtypes -libs unix,xml-light main.native

sanitize:
	_build/sanitize.sh

init:
	cp localconfig.default localconfig.ml
	cp config/config.default config/config.xml

tags:
	etags -R .
