.PHONY: all clean grammars grammars/clean ghcid

all: grammars

clean: grammars/clean

grammars:
	make -C muste/data/gf/grammars

grammars/clean:
	make -C muste/data/gf/grammars clean

# Mainly a reminder to self
ghcid:
	ghcid -c "stack ghci --test --ghci-options=-fno-break-on-exception --ghci-options=-fno-break-on-error --ghci-options=-v1 --ghci-options=-ferror-spans --ghci-options=-j"

deploy: hacky-sack/deploy/cse-principia

hacky-sack/deploy/cse-principia:
	make -C muste-ajax hacky-sack/deploy/cse-principia
