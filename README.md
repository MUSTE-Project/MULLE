MULLE
=====
The [MUSTE](http://www.cse.chalmers.se/~peb/muste.html) Language Learning Environment is a framework to provide grammar-based language learning exercises.

## Dependencies

All dependencies are resolved automatically by stack.  You just need
to initialize the submodules:

    git submodule init

Setup
-----
To setup one of the packages you need to select which GHC version you
want to use.  Currently I've only tested this with 8.4.3.  To e.g. use
this version do

    ln -s stack-12.0.yaml stack.yaml

You can now simply build the projects with `stack build` and see
browse the Haddock documentation with `stack haddock --open`.

Running
-------

The main program is a web server serving both AJAX (and CGI) requests
and the HTML that is the user interface.  This is located in the
`muste-ajax` package.

Before running the program the database needs to be initialized.  This
can be done with the command:

    stack exec db-init

Now the program can be run with

    stack exec muste-ajax

No the program can be accessed in you browser.  The program should
output the location you need to access to see it (default is
http://localhost:8080).
