<!-- [![Build Status](https://secure.travis-ci.org/MUSTE-Project/MULLE.png)](http://travis-ci.org/MUSTE-Project/MULLE) -->

MULLE
=====

The [MUSTE](http://www.cse.chalmers.se/~peb/muste.html) Language
Learning Environment is a framework to provide grammar-based language
learning exercises.

Setup
-----

For the impatient:

    git submodule update --init
    ln -s stack-lts-12.yaml stack.yaml
    stack install muste-ajax
    muste-ajax --recreate-db

And then navigate to

    http://localhost:8080

For more details please see below.

### Dependencies

All Haskell dependencies are resolved automatically by stack.  You
just need to initialize the submodules:

    git submodule update --init

To be able to build the grammar files you will also need to install
`gf-core`.  Please follow the guidelines in

- <https://github.com/GrammaticalFramework/gf-core>

The front-end dependencies are managed with `npm`.  This is also
required to successfully run the web UI.

### Setup

To setup one of the packages you need to select which GHC version you
want to use.  Currently I've only tested this with 8.4.3.  To e.g. use
this version do

    ln -s stack-lts-12.yaml stack.yaml

You can now simply build the projects with `stack build` and browse
the Haddock documentation with `stack haddock --open`.

### Configuring

Currently configuration of the package `muste-ajax` is done using the
a YAML configuration file.  See the values in the file
`muste-ajax/config.yaml`.  In the directory `muste-ajax/config` there
are examples of other configuration files.  To pick an alternative
configuration option you can e.g. do the following from `muste-ajax/`:

    ln -sf config/desired-config.yaml config.yaml

Here is documentation on the available options:

* `port`: The port that the server listens on.
* `virtual-root`: Used when the requests to the application is not
  made against the href `/`.  NB! If you need to override this you
  should also change the value of `VIRTUAL_ROOT` in
  `muste-ajax/static/muste-gui.js`.
* `serve-static-relative`: Useful during developing since changes to
  static files (e.g. the front end JavaScript code) is served from a
  path relative to where the `muste-ajax` executable is run.  This
  allows you to change those files without rebuilding the application.
* `data-dir`: Location where the database is kept.
* `log-dir`: Location where the logs are kept.

Partially/unsupported options:

* `www-root` Directory where the data files are located.  Currently
  you should probably just leave this value empty as the copying of
  data-files does not respect this flag.
* `static-directory` file with the front end (static) files.  Is
  resolved relative to the above option.

#### An abundance of configuration methods

There are quite a few way that configuration options are handlded
today:

* Some configuration options are embedded into the binary.  This is
  the case for the file `muste-ajax/config.yaml`.
* That file in turn identifies some paths.  E.g. the database-file
  which is created at run-time and seeded by the application (this is
  probably fine)
* There are also some file in `muste-ajax/data`.
  * `data/sql` needed at compile-time
  * `lessons.yaml` copied at install time and read when `muste-ajax
    --recreate-db` is invoked.
* Furhtermore some configuration options are stored as columns in the
  database.  This is probably also fine.

### Building

The grammar-files (in `muste/data/grammars/`) must be kept up-to-date
and installed in a global location for the application to work
correctly.  This should be handled automatically by the cabal build
script.  If this somehow goes wrong you can do it automatically using:

    make install

Assuming you have set up `gf-core` and `gf-rgl`.

    stack build

The front end dependencies are managed with `npm`.  To fetch all
dependencies navigate to.

    muste-ajax/static/

And run

    npm install

To get fetch all dependencies.

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

Testing
---

Run the tests with:

    stack test

If you need profiling things are a bit more complicated.  There's an
issue with GHC[^1][^2] concerned with profiling things involving
template Haskell.  Here's a work-around:

    stack build                              \
      --test                                 \
      --profile                              \
      --work-dir .stack-work-prof            \
      --ghc-options="-fexternal-interpreter"

Using a separate work-dir for profiling means that we don't have to
rebuild the project when switching between (no-) profiling.

[^1]: https://github.com/commercialhaskell/stack/issues/2903
[^2]: https://downloads.haskell.org/~ghc/8.6.1/docs/html/users_guide/glasgow_exts.html#using-template-haskell-with-profiling

Documentation
---

Since most modules of the libraries are marked as internal it can be
useful to generate documentation for these as well as a development
aid.  Consider using this command:

    stack haddock --haddock-internal --no-haddock-deps --force-dirty

