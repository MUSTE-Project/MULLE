BACKLOG
=======

Prune suggestions that can be reached in multiple steps
---

https://github.com/MUSTE-Project/MULLE/issues/5

Better configuration support
---

E.g. using `optparse-applicative`.

Pretty- print/parse for `TTree`?
---

It might make sense to have an instance of `Pretty` for `TTree` based
on PGF parser/printer.  This will require us to make the grammar a
field of `TTree`.  Perhaps we can do something similar for parsing?

Set expiry on session cookie
---

We have core logic for handling rejecting expired cookie.  HTTP also
supports this notion, so why not let user agents know when we expire
their session?

Move more parameters into location or query params
---

Improved support for insertion
----

https://github.com/MUSTE-Project/MULLE/issues/2

Automatically generate .pgf files
---

The project depends on the `.pgf` files existing.  They are
automatically generated and should not be source controlled.  There
should be a make target that generates these files from
`muste-ajax/data/gf/grammars/**/*.gf`.

Change representation from single tree to sets of trees.
---

https://github.com/MUSTE-Project/MULLE/issues/3

Wide / narrow grammar
---

https://github.com/MUSTE-Project/MULLE/issues/4

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
