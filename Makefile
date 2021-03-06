TARGET     = aac
TARGET2    = aac_optimized
TARGET3    = aac_global
TARGET4    = aac_global_store
TARGET5    = aac_memo
TARGET6    = aac_baseline
TARGET7    = aac_optimized_memo
TARGET8    = aac_optimized_samemo
TEST       = test
OPTS       = -pp camlp4o -use-ocamlfind
TAGS       = annot,debug
LIBS       =
PKGS       = containers,batteries,ocamlgraph
EXTENSION  = byte
RUN_TEST   = ./$(TEST).$(EXTENSION)
DOCDIR     = pcesk.docdir
CFLAGS     = -w A -w -4 -w -27 -short-paths
OCAMLBUILD = ocamlbuild $(OPTS) -tags $(TAGS) -pkgs $(PKGS) -cflags "$(CFLAGS)"

.PHONY: all clean

all:
	$(OCAMLBUILD) $(TARGET).$(EXTENSION)
	$(OCAMLBUILD) $(TARGET2).$(EXTENSION)
	$(OCAMLBUILD) $(TARGET3).$(EXTENSION)
	$(OCAMLBUILD) $(TARGET4).$(EXTENSION)
	$(OCAMLBUILD) $(TARGET5).$(EXTENSION)
	$(OCAMLBUILD) $(TARGET6).$(EXTENSION)
	$(OCAMLBUILD) $(TARGET7).$(EXTENSION)
	$(OCAMLBUILD) $(TARGET8).$(EXTENSION)

clean:
	$(OCAMLBUILD) -clean
