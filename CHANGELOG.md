Change log
==========

0.1.0.0
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
