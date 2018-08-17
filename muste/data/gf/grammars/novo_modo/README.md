
This folder contains the MULLE grammars:

- `Prima*.gf`: the first lesson
- `Secunda*.gf`: the second lesson
- `Tertia*.gf`: the third lesson
- `Quarta*.gf`: the fourth lesson

Plus the grammar `Exemplum*.gf`, which is an example grammar which is used during the development of MULLE.

Setup
--------

GF and the RGL has to be installed: Follow the guidelines in

- <https://github.com/GrammaticalFramework/gf-core>
- <https://github.com/GrammaticalFramework/gf-rgl>

To compile and install the RGLs, run the make scripts in the `gf-rgl` directory.

You also have to install the dictionary files `DictEng` and `DictSwe`, by running (in the `gf-rgl` directory):

    runghc Make install DictEng.gf DictSwe.gf

Install
---------

To compile and install the MULLE grammars, just run `make` in this directory.
The grammars will compile to `.pgf` files and will be symlinked to `../../compiled/novo_modo/`

