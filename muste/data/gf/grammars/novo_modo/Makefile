GFMAKE = gf --make
LANGS = Lat Eng Swe
ALL_GF_FILES = $(wildcard *.gf)

.PHONY: all

all: Exemplum.pgf Prima.pgf Secunda.pgf

clean:
	rm *~ *.gfo

%.pgf: $(filter $*%,$(ALL_GF_FILES))
	$(GFMAKE) $(LANGS:%=$*%.gf)
