OCB = ocamlbuild -use-ocamlfind

all: native byte # profile debug

clean:
	$(OCB) -clean

test: sanity
	$(OCB) test.native

test_parser: sanity
	$(OCB) test_parser.native

profile: sanity
	$(OCB) -tag profile client.native

debug: sanity
	$(OCB) -tag debug client.byte

# check that packages can be found
sanity:
	ocamlfind query lwt

test: native
	echo '[1, 2, "three", {"four": 4}]' | ./client.native
