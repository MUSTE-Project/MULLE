BACKLOG
=======

Set expiry on session cookie
---

We have core logic for handling rejecting expired cookie.  HTTP also
supports this notion, so why not let user agents know when we expire
their session?

Move more parameters into location or query params
---

Move demo-dir to "static"
---

And manage with cabal resource paths.

General refactoring
-------------------

Remove `LTree`. `LTree` is currently not exported from `muste-lib`, it
is however used internally. E.g. in `linearizeTree` which is used in
the ajax-backend.

Use framework for (de-) serializing values when storing in database.
---

Make `FromROW` instances for data types.

Use Haskell data files for e.g. the grammar files.
---

Improved support for insertion
----

We need a way for users to insert new nodes into adjunction trees.
This may be achieved by simply having the back alternate between
suggesting replacements for syntactically close nodes.

Automatically generate .pgf files
---

The project depends on the `.pgf` files existing.  They are
automatically generated and should not be source controlled.  There
should be a make target that generates these files from
`muste-ajax/data/gf/grammars/**/*.gf`.

Change representation from single tree to sets of trees.
---

Multiple sentences can have the same linearized
representation. Therefore one linearization must be associated with
one or more abstract representations.

Wide / narrow grammar
---

Support for automatically generating 'wide' grammars from 'narrow' ones.

The interface must also be extended to add support for "fixing
mistakes".

Do we want to keep supporting `muste-cgi`?
---

AFAIK CGI scripts just speak a different protocol from
`application/json`.  So this should be easy to keep support for.

`LinToken` and `Linearization`
---

Do we need both representations?

Depend only on GF's Haskell bindings
---

There is currently discussion in GF about splitting the Haskell
bindings into a seperate package/repo.  When this is implemented we
can change the upstream dependency.  Please follow the discussion at
[GF](https://github.com/GrammaticalFramework/GF/issues/47).

Currently we depend on a fork of GF with only the Haskell runtime.
The reason for this is that the above mentioned repo is absolutely
*huge*.

Rename stack.yamls
---

The name ought to refer to the GHC version.  Also, there should just
be one stack.yaml in the root of the project that manages both
packages -- see e.g. the `stack.yaml` in `digestive-functors`.
