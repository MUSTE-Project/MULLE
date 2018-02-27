MAKE = -make 
GF = gf
LANGS = Lat,Eng,Swe
all: prima secunda tertia quarta

prima:
	$(GF) $(MAKE) Prima{$(LANGS)}.gf

prima_test:
	$(GF) Prima.pgf < prima_pars.gfs
	
secunda:
	$(GF) $(MAKE) Secunda{$(LANGS)}.gf

secunda_test:
	$(GF) Secunda.pgf < secunda_pars.gfs

tertia:
	$(GF) $(MAKE) Tertia{$(LANGS)}.gf

tertia_test:
	$(GF) Tertia.pgf < tertia_pars.gfs

quarta:
	$(GF) $(MAKE) Quarta{$(LANGS)}.gf

quarta_test:
	$(GF) Quarta.pgf < quarta_pars.gfs

test: prima_test secunda_test tertia_test quarta_test

clean:
	rm *~ *.gfo
	