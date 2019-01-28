<!-- [![Build Status](https://secure.travis-ci.org/MUSTE-Project/MULLE.png)](http://travis-ci.org/MUSTE-Project/MULLE) -->

MULLE
=====

The [MUSTE](http://www.cse.chalmers.se/~peb/muste.html) Language Learning Environment is a framework to provide grammar-based language learning exercises.

Setup
-----

For the impatient:

    ln -s stack-lts-12.yaml stack.yaml
    stack install muste-ajax

Now you can test one of the two examples:

    make -C examples/grammars/exemplum/
    muste-ajax -c examples/config-exemplum.yaml --recreate-db

(For the second example, replace `exemplum` with `programming`)

When the server has started, you can navigate to:

    http://localhost:8080

For more details please see below.

### Dependencies

All Haskell dependencies are resolved automatically by `stack`.

To be able to build the grammar files you will also need to install GF and its RGL. Please follow the guidelines here: <http://www.grammaticalframework.org>

The front-end dependencies are managed with `npm`. This is also required to successfully run the web UI.

### Setup

To setup one of the packages you need to select which GHC version you want to use. Currently it's only tested with 8.4.3. To use this version do

    ln -s stack-lts-12.yaml stack.yaml

You can now simply build the projects with `stack build` and browse
the Haddock documentation with `stack haddock --open`.

### Configuring

Currently configuration of the package `muste-ajax` is done using a YAML configuration file.  See examples of how they can look like in the `config-xxx.yaml` files values in the `examples` directory.

Here is documentation on the available options:

* `db`: the path to the generated SQLite database (default: `data/muste.sqlite3`)
* `lessons`: the path to the Yaml file describing the lessons (default: `lessons.yaml`)
* `access-log`: the path to the SQLite access log file (default: `log/access.log`)
* `error-log`: the path to the SQLite error log file (default: `log/error.log`)
* `port`: The port that the server listens on (default: 8080)
* `static-dir`: the path to the directory containing the static HTML/JS files (default: `static`)
* `virtual-root`: Used when the requests to the application is not made against the href `/`.  NB! If you need to override this you should also change the value of `VIRTUAL_ROOT` in `muste-ajax/static/muste-gui.js`.


### Building the grammar files

The grammar-files that you refer to in your `lessons.yaml` must be kept up-to-date. This will not be handled automatically by the `stack`/`cabal` build script, but instead it is up to you.

The example grammars have a `Makefile` in their respective directories, so you can run:

    make -C examples/grammars/exemplum/

(Alternatively, replace `exemplum` with `programming`)

### Building the MUSTE apps

Just run this:

    stack build

The front end dependencies are managed with `npm`.  To fetch all dependencies navigate to

    muste-ajax/static/

and run

    npm install

to fetch all dependencies.This is also executed automatically by the setup-script when you do `stack build`.

### Installing

    stack install

Note that this does not install any grammars, nor the static HTML/JS files. They should instead be pointed to by the config Yaml file, as described earlier.

Running
-------

The main program is a web server serving both AJAX (and CGI) requests and the HTML that is the user interface.This is located in the `muste-ajax` package.

Before running the program for the first time the database needs to be created. This can be done with a switch to the main executable:

    muste-ajax --recreate-db

(Prepend `stack exec` to the above command if you have not installed the executable to a location on your `PATH`).  **WARNING**: This will delete any existing data in the database.

Now the program can be accessed in you browser. The program should output the location you need to access to see it (default is <http://localhost:8080>).

Testing
----

(**Note**: currently the tests are not up-to-date, and do not work).

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
----

Since most modules of the libraries are marked as internal it can be useful to generate documentation for these as well as a development aid. Consider using this command:

    stack haddock --haddock-internal --no-haddock-deps --force-dirty

Diagnostics
----

To get more verbose diagnostics output, compile with:

    stack install --ghc-options="-DDIAGNOSTICS"

