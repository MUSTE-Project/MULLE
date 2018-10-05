.PHONY: all clean grammars grammars/clean ghcid

all: grammars

clean: grammars/clean

install: grammars/install

grammars:
	make -C muste/data/grammars

grammars/clean:
	make -C muste/data/grammars clean

grammars/install:
	make -C muste/data/grammars install

# Mainly a reminder to self
ghcid:
	ghcid -c "stack ghci --test --ghci-options=-fno-break-on-exception --ghci-options=-fno-break-on-error --ghci-options=-v1 --ghci-options=-ferror-spans --ghci-options=-j"

deploy: hacky-sack/deploy/cse-principia

hacky-sack/deploy/cse-principia:
	make -C muste-ajax hacky-sack/deploy/cse-principia
