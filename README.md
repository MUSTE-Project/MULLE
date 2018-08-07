MULLE
=====
The [MUSTE](http://www.cse.chalmers.se/~peb/muste.html) Language
Learning Environment is a framework to provide grammar-based language
learning exercises.

## Dependencies

All dependencies are resolved automatically by stack.  You just need
to initialize the submodules:

    git submodule init

Setup
-----
To setup one of the packages you need to select which GHC version you
want to use.  Currently I've only tested this with 8.4.3.  To e.g. use
this version do

    ln -s stack-8.4.3.yaml stack.yaml

You can now simply build the projects with `stack build` and browse
the Haddock documentation with `stack haddock --open`.

### Configuring

Currently configuration of the package `muste-ajax` is done using the
C preprocessor.  See the values in the file `muste-ajax/app.config`.
Please note that this is not a regular C header file, since it is
included verbatim into `muste-ajax/src/Config.hs` - so it's really
more a fragment of a Haskell source file with C preprocessor
directives.  The values in that directory are the ones suitable for
production.  The directory `config/` provides alternative
configuration sets.  Here is documentation on the available options:

* `SERVE_STATIC_RELATIVE_PATH` useful while developing since changes
  to the static file (e.g. the front end JavaScript code) is served
  from a path relative to where the `muste-ajax` executable is run.
* `WWW_ROOT` used for overriding the location to the physical files
  needed.  I'm not sure this is working correctly, please see
  `Main.appInit` and the documentation for `make-snapplet`.
* `VIRTUAL_ROOT` used when the requests to the application is not made
  against the href `/`.  NB! If you need to override this you should
  also change the value of `VIRTUAL_ROOT` in
  `muste-ajax/static/muste-gui.j`.
* `PORT` the port to serve the application on.

### Building

    stack build

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
