# MULLE
The [MUSTE](http://www.cse.chalmers.se/~peb/muste.html) Language Learning Environment is a framework to provide grammar-based language learning exercises.

## Dependencies

Most dependencies can be automatically resolved by cabal, but the GF Haskell Runtime https://github.com/GrammaticalFramework/GF/tree/master/src/runtime/haskell has to be installed manually.

## Setup
MULLE consists of two major parts, the MUSTE Haskell library in *muste-lib/* and the standalone webserver in *ajax-backend/* both directories contain cabal
files for building and installing. The HTML frontend files are in the *ajax-backend/demo/* subfolder.

To run a standalone instance follow these steps:

1. Build and install the MUSTE library by typing `cd muste-lib && cabal install && cd ..`
1. Build the standalone server by typing `cd ajax-backend && cabal configure && cabal build && cd ..`
1. Initialize the database by typing `cd ajax-backend && cabal run db-init && cd ..`
1. Run the server by typing `cd ajax-backend && cabal run ajax-backend`
1. Access http://localhost:8080 in your webbrowser. 

### Setup with stack
You can alternatively set up the project with git submodules and
stack. First initialize the submodule `git submodule init`. Then for
each package you want to build, select the stack configuration you
want to use. Since the Haste compiler requires ghc-7.10.* we use
newest lts with this compiler (6.35).
