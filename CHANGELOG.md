Change log
==========

HEAD
----

`ClientTree` and `ServerTree` now no longer just store a single tree
and it's linearization, rather it stores a set (list) of `TTree`s
corresponding to all the possible `TTree`s that have this
linearization.


0.2.0.2
----

Depend on gf straight from the source after they split up the runtime
from the core application.

Add exercises for 'Secunda Pars'.

Remove bitrotten test cases.

Add single test case for issue #5: Prune suggestions that can be
reached in multiple steps.

Put authentication token in header.

Use Haskell data files.

Add exercises from "Secunda Pars"

Remove unnecessary un- and re- marshalling of data-types.  Use more
efficient data-structures, like maps rather than lists of tuples.

Put (some) AJAX params in request path.

0.2.0.1
-------

Use `snap`

The idea is to use a framework that already provides logging
functionality, authentication and a "sensible monad for web
development".

Remove unused `demo/Main.js`.

Some parameters that were put in the json body of the request has now
been moved to the location part of the request.  This is good REST API
design.  More parameters might need to be moved here.

We depend on our own version of some package because I had to patch
them to work with the most recent stackage lts.

0.2.0.0
-------

This version has a big diff from the previous one.  Most of the
changes are non functional changes.  I.e. they should not alter the
behaviour of the program.  The purpose of this version if to
reorganize things and to refactor code.

Add haddock documentation to all exported members of all exposed
modules in package `muste`.

Removes some unnecessary marshalling back and forth between different
string representations.

Adds *all of* the GF code base as a git sub module dependency so the
project can be built out of the box with a single command.  Note that
the only thing we need from GF is the Haskell bindings which has a
considerable smaller footprint.  There is currently discussion in GF
about splitting these into seperate packages/repos.  When this is
implemented we can change the upstream dependency.  Please follow the
discussion at [GF](https://github.com/GrammaticalFramework/GF/issues/47).

Stackify the whole project.  Use more recent version of GHC.

Use Haskell resource files to manage most hard coded file locations.

0.1.0.0
-------
This is the last version before a major refactoring.
