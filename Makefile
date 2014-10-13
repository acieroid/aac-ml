TARGET     = aac
TEST       = test
OPTS       = -pp camlp4o -use-ocamlfind
TAGS       = annot,debug
LIBS       =
PKGS       = containers
EXTENSION  = byte
RUN_TEST   = ./$(TEST).$(EXTENSION)
DOCDIR     = pcesk.docdir
CFLAGS     = -w A -w -4 -w -27 -short-paths
OCAMLBUILD = ocamlbuild $(OPTS) -tags $(TAGS) -pkgs $(PKGS) -cflags "$(CFLAGS)"

.PHONY: all clean

all:
	$(OCAMLBUILD) $(TARGET).$(EXTENSION)

clean:
	$(OCAMLBUILD) -clean
