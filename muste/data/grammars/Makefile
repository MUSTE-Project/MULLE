GRAMMARS = novo_modo exemplum

.PHONY: all clean

all:
	for G in $(GRAMMARS) ; do \
		make -C $$G ; \
	done

clean:
	for G in $(GRAMMARS) ; do \
		make -C $$G clean ; \
	done
