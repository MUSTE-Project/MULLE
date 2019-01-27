GFMAKE = gf --make
LANGS = Eng Swe Spa Chi Ara Test
GRAMMARS = Exemplum.pgf

.PHONY: all clean

all: build

build: $(GRAMMARS)

clean:
	rm $(GRAMMARS)
	rm *.gfo

%.pgf: %*.gf
	@echo Updated GF files: $?
	$(GFMAKE) $(LANGS:%=$*%.gf)
	@touch $@

# The line "@touch $@" is because if the PGF is not changed since previous version,
# the PGF is not updated, so we make sure that the PGF will have a recent time stamp.

