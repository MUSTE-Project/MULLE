BACKLOG
=======

General refactoring
-------------------
There are 3 representation of a tree.

Remove `LTree`. `LTree` is currently not exported from `muste-lib`, it
is however used internally. E.g. in `linearizeTree` which is used in
the ajax-backend.

Use framework for (de-) serializing values when storing in database.
---

Make `FromROW` instances for data types.

Use framework for web requests
---

E.g. `snap`

Use Haskell data files for e.g. the grammar files.
---

Split database init script into seperate module
---

Improved support for insertion
----

We need a way for users to insert new nodes into adjunction trees.
This may be achieved by simply having the back alternate between
suggesting replacements for syntactically close nodes.

Automatically generate .pgf files
---

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
