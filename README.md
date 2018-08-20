MULLE
=====
The [MUSTE](http://www.cse.chalmers.se/~peb/muste.html) Language
Learning Environment is a framework to provide grammar-based language
learning exercises.

## Dependencies

All dependencies are resolved automatically by stack.  You just need
to initialize the submodules:

    git submodule update --init

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
a YAML configuration file.  See the values in the file
`muste-ajax/config.yaml`.  In the directory `muste-ajax/config` there
are examples of other configuration files.  To pick an alternative
configuration option you can e.g. from the muste-ajax directory do:

  ln -sf config/desired-config.yaml config.yaml

Here is documentation on the available options:

* `port`: The port to the server listens on
* `virtual-root`: used when the requests to the application is not made
  against the href `/`.  NB! If you need to override this you should
  also change the value of `VIRTUAL_ROOT` in `muste-ajax/static/muste-gui.js`.
* `serve-static-relative`: useful during developing since changes to
  static files (e.g. the front end JavaScript code) is served from a
  path relative to where the `muste-ajax` executable is run.  This
  allows you to change those files without rebuilding the application.
* `data-dir`: Location where the database is kept.
* `log-dir`: Location where the logs are kept.

Partially/unsupported options:
}
* `www-root` Directory where the data files are located.  Currently
  you should probably just leave this value empty as the copying of
  data-files does not respect this flag.
* `static-directory` file with the front end (static) files.  Is
  resolved relative to the above option.

### Building

If the grammar-files (in `muste/data/gf/grammars/`) have changed (or
if you just cloned the repository) you need to build the
grammar-files.  This can be achieved with:

    make

Assuming you have set up `gf-core` and `gf-rgl`.

    stack build

### Installing

    stack install

Running
-------

The main program is a web server serving both AJAX (and CGI) requests
and the HTML that is the user interface.  This is located in the
`muste-ajax` package.

Before running the program for the first time the database needs to be
created.  This can be done with a switch to the main executable:

    muste-ajax --recreate-db

Prepend `stack exec` to the above command if you have not installed
the executable to a location on your `PATH`.  WARNING: This will
delete any existing data in the database.

No the program can be accessed in you browser.  The program should
output the location you need to access to see it (default is
http://localhost:8080).
