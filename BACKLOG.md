BACKLOG
=======

General refactoring
-------------------
There are 3 representation of a tree.

Remove `LTree`. `LTree` is currently not exported from `muste-lib`, it
is however used internally. E.g. in `linearizeTree` which is used in
the ajax-backend.

Style improvements / dead code removal
-----------------

I consider removing the haste front end and `Main.hs` in `muste-lib`. I
don't know if this is needed for some special purpose.


Improved support for insertion
----

We need a way for users to insert new nodes into adjunction trees.
This may be achieved by simply having the back alternate between
suggesting replacements for syntactically close nodes.

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
