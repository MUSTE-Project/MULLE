SHELL=/bin/bash

MAKE = -make 
GF = gf
LANGS = Lat,Eng,Swe
all: prima secunda tertia quarta

prima:
	$(GF) $(MAKE) Prima{$(LANGS)}.gf

prima_test:
	$(GF) Prima.pgf < prima_pars.gfs

prima_api:
	$(GF) -n PrimaAPI $(MAKE) Prima{$(LANGS),API}.gf

secunda:
	$(GF) $(MAKE) Secunda{$(LANGS)}.gf

secunda_test:
	$(GF) Secunda.pgf < secunda_pars.gfs

secunda_api:
	$(GF) -n SecundaAPI $(MAKE) Secunda{$(LANGS),API}.gf

tertia:
	$(GF) $(MAKE) Tertia{$(LANGS)}.gf

tertia_test:
	$(GF) Tertia.pgf < tertia_pars.gfs

tertia_api:
	$(GF) -n TertiaAPI $(MAKE) Tertia{$(LANGS),API}.gf

quarta:
	$(GF) $(MAKE) Quarta{$(LANGS)}.gf

quarta_test:
	$(GF) Quarta.pgf < quarta_pars.gfs

quarta_api:
	$(GF) -n QuartaAPI $(MAKE) Quarta{$(LANGS),API}.gf

test: prima_test secunda_test tertia_test quarta_test

apis : prima_api secunda_api # tertia_api quarta_api

clean:
	rm *~ *.gfo
