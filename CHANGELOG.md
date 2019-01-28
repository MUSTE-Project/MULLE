Change log
==========

0.3.0
----

The configuration files and grammar are now moved out of the MUSTE project. Some examples are in the `examples` directory, but note that they are not anymore automatically built by `stack` or `make`.

The configuration files are not read during compilation, but instead when the `muste-ajax` app is started. This means that you can have several different config files and switch between them easily.

All GIT submodules are deleted, so installation should be a bit easier.

0.2.8.1b
----

Ensure that only the best score is returned for each lesson when
fetching high scores.

0.2.8.1
----

This version consists mainly of clean-up, simplification and removing of unused code.

0.2.8.0
----

### Interface changes

Disallow re-starting solved lessons.

Make highlighting matching words configurable.

Show high score bar-chart on lessons page.

When restarting cycling through the menus, hide it once.

Make items with no menus unclickable

Add support for rtl scripts.

### Other changes

Entry for Haskell Communities and Activities Report.

### Techincal bits

Support for building with `cabal new-build`.  Tested with
`cabal-install version 2.2.0.0`.

Untested And Totally Unsopported[tm] experiments with travis-ci.

Automatically build the js-deps when building `muste-ajax`.

Automatically build the grammars when building `muste`.

#### Database changes

Implement `Finished{Lesosn,Exercise}` as views.

Make interfacing with the sqlite back end more robust:
  * Use named query parameters.
  * More type-safe primary keys (using phantom types).

0.2.7.0
----

### UI changes

Fix issue with busy indicator

Show overlay when page is loading

Show which page we are on in the browser location bar

Experimental: Navigate to page as given by the location bar header on
page load.

Detect if exercise+lesson is over.  If the lesson is over, go back to
lesson overview page.  If the lesson is not over but the exercise is,
retrieve the next exercise in that lesson.  If the exercise is not
over, just display the sentences.

### Database changes

This change contains a lot of changes to the data model.  Regressions
are likely!

Compunded the time column with the click count column to make a new
"score" column.  The data in it is stored a binary blob.  For one
thing this for instance means that we cannot use aggregate functions
on the column.  In stead we need to pull out all score values and
e.g. mconcat them together.

### Other changes

Update to latest version of our fork of `sqlite-simple`.

0.2.6.0
----

Persist app-state across requests.

Load exercises to seed the database with from a `.yaml` file rather
than embedding it in source.

New page for adding a user to the database.

Various styling changes:

* Use `handlebars.js` (a template engine) for creating the layout on the
  exercise page.
* Do not use table for layout
* Make heavy use of the CSS attribute `flex`.
* Display time difference differently.  In stead of just giving the
  diff in seconds we also show minutes, hours, days (if applicable).
  This requires uses `coundown.js` to work.
* Increase spacing between words in exercise.

More robust error reporting between server and client.

Automatically show login page if a request responds with `401
Unauthorized`.

Update from jQuery version from  v1.11.1 to v3.3.1.

Reduce font-size.  This is to accomodate mobile users.  Users on
hi-dpi screens should use their browsers scaling functionality if they
want a larger font size.

Display an empty menu if we click an element with no menu suggestions.
Old behaviour was to throw an error in the javascript console.

0.2.5.2
----

Make `Category` a newtype wrapper around `Text` (rather than a type
synonym for `String`)

Close issue #37: Store *un*annotated sentences in exercises

0.2.5.1
----

The CLI executable is no longer called `muste-cli`, rather, it's called
`muste` and it has two subcommands:

  * cli
  * precompute

So where you would before write `muste-cli` you must now write `muste
cli` (note the space).

Change styling (Issue #35)

Adds options to CLI:

  * Limit prune depth (Issue #28)
  * Print compact (Issue #27)
  * Switch for showing internal representation (Issue #31)
  * Sub-command precompute to cache adjunction trees and a switch to
    load these (Issue #34)

Other changes to CLI:

  * Drops support for setting the "active menu" (Issue #26)
  * Language argument is mandatory

0.2.5.0
----

Add benchmarking suite for generating menus.

Move grammar files.  This requires the grammar files to be re-built
(with `make`).  First subsequent built may also issue a warning about
missing files.  This warning should dissapear on subsequent builds.

Drop support for old menu.

Performance improvements when generating trees.

0.2.4.0
----

Issue #15: New algorithm for creating menus.

0.2.3.1
----

A menu now maps from "selections".  Selections correspond to the set
of `LinToken`s that correspond to the subtree (`CostTree`) that the
menu maps to.  Perhaps a bit convoluted explanation, sorry about that,
please see `Muste.Menu.Internal.selectionFromPath` for the gory
details.

When clicking words in the UI we now cycle through the various
"selections" corresponding to that word.

A quasi-quoter has been implemented for generating `TTree`'s from
their representation in `pgf`.  To this end a `Lift` instance has been
declared for `TTree`s.  A test-case has been added for this.

The database stores the linearized version of trees.

How `TTree`s are marshalled to/from the database has been changed.
Now uses sqlite's `BLOB` type (for binary data).

`Menu`s are now no longer "cleaned" in `muste-gui` but rather we use
the EcmaScript 6 Maps.  Can I use it?  [Yes I can!
](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Map#Browser_compatibility)

Locate various config/data files in a more robust manner.

Disable text-selection on the menus in the UI.  This is nice because
one often wants to click multiple times, which can be registered as a
double-click, such an even is not supposed to trigger text selection.
Of course this means that it is not possible to copy-paste the
exercises into other programs...

Add new function to `Muste.Grammar.Internal` for parsing sentences
into `TTree`s.  Similarly in `Muste.Linearization.Internal`.

0.2.3.0
----

Recreating the database is now a flag to the single executable that
the package `muste-ajax` defines.

0.2.2.1
----

Add configuration options for

* `port`
* `www-root`
* `static-directory`
* `virtual-root`
* `serve-static-relative`
* `data-dir`
* `log-dir`

Please see the readme.

0.2.2.0
----

Implement `coverNodes` for determining which replacement trees are to
be considered "insertions".

0.2.1.0
----

Embed `.pfg`-files into compiled binary for package `muste`.  This
means that `muste` knows at compile time which grammars it stores.
The benefit of this is that various entities can refer to grammars by
a single identifier for the grammar. See `Muste.Grammar.Grammars`.

Though the change in representation from single trees to sets of trees
happened in `0.2.0.3` ambiguities were never introduced.  They are
now.  This is achieved by changing `CostTree` that is generated by
calls to `Muste.Menu.getCleanMenu`.  `CostTree`s are now grouped
together based on having the same linearization.  See
`Muste.Menu.Internal.costTrees`.

Fixes an error in a `Makefile` that generates `.pgf`s.

Adds `Pretty` instances for `Menu` and `TTree`.

0.2.0.5
----

Move stuff around in `Muste.Linearization`:

* `LinTokens` becomes `Linearization`
* `Linearization` disappears

0.2.0.4
----

Make `Menu` a monomorphic container and make it map to `[CostTree]`
rather than `[[CostTree]]`.

0.2.0.3
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
----

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
----

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
----
This is the last version before a major refactoring.

0.0.3
----

Implemented pruning
