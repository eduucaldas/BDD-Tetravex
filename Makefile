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

test_parser: sanity
	$(OCB) test_parser.native

profile: sanity
	$(OCB) -tag profile client.native

debug: sanity
	$(OCB) -tag debug client.byte



# check that packages can be found



