
all:
	ocamlbuild main.native pa_pcduce.cma pcduce_lib.cma

clean:
	ocamlbuild -clean
