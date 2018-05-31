OCB = ocamlbuild -use-ocamlfind

all: native byte # profile debug

clean:
	$(OCB) -clean

test:
	$(OCB) test.native

main:
	$(OCB) main.native

tetravex:
	$(OCB) tetravex.native

test_parser:
	$(OCB) test_parser.native

profile:
	$(OCB) -tag profile client.native

debug:
	$(OCB) -tag debug client.byte

# check that packages can be found
