GFMAKE = gf --make
LANGS = Lat Eng Swe
ALL_GF_FILES = $(wildcard *.gf)
GRAMMARS = Exemplum.pgf Prima.pgf Secunda.pgf

.PHONY: all clean

all: $(GRAMMARS)

clean:
	rm $(GRAMMARS)
	rm *.gfo

%.pgf: $(filter $*%,$(ALL_GF_FILES))
	$(GFMAKE) $(LANGS:%=$*%.gf)
