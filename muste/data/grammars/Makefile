GRAMMARS = novo_modo exemplum programming

XDG_DATA_DIR=$$HOME/.local/share

DATA_DIR=$(XDG_DATA_DIR)/muste

GRAMMARS_DIR=$(DATA_DIR)/grammars

.PHONY: all clean

all: build

build:
	for G in $(GRAMMARS) ; do \
		make -C $$G build ; \
	done

clean:
	for G in $(GRAMMARS) ; do \
		make -C $$G clean ; \
	done

install: build
	for G in $(GRAMMARS) ; do \
		mkdir -p $(GRAMMARS_DIR)/$$G ; \
		cp $$G/*.pgf $(GRAMMARS_DIR)/$$G ; \
	done
