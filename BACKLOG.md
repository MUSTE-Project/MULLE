BACKLOG
=======

Restore bitrotten test-cases
---

As of

    commit c3b02e22a06704322c0bc4fb576182f05b0a0ab2 (HEAD -> fredefox, origin/fredefox)
    Author: Frederik Hanghøj Iversen <fhi.1990@gmail.com>
    Date:   Thu Jul 26 09:58:24 2018 +0200

        Remove bitrotten test cases, add test case for issue #5...

        Issue #5: "Prune suggestions that can be reached in multiple
        steps". https://github.com/MUSTE-Project/MULLE/issues/5

The old bitrotten test cases have been removed. We should put some
effort into restoring these and make them work after the recent
refactorings.

Issue #7: https://github.com/MUSTE-Project/MULLE/issues/7

Use front end framework
---

https://github.com/MUSTE-Project/MULLE/issues/6

Better configuration support
---

E.g. using `optparse-applicative`.

Parser for `Pretty` version of `TTree`s
---

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

Issue #3: Change representation from single tree to sets of trees.
---

https://github.com/MUSTE-Project/MULLE/issues/3

In `Protocol.emptyMenus` and `Protocol.assembleMenus` we make use of
`unsafeTakeTree`.  This is perhaps inelegant, but should be safe.
Should work under the assumption that all the trees we consider have
the same linearization, so it probably shouldn't matter which one we
pick.  It would be nice to encapsulate this in the type somehow.  One
low-hanging piece of fruit would be to use some representation for a
non-empty set. Since we at least need one reference tree to linearize.
Also there is some code-duplication in `Protocol.emptyMenus` and
`Protocol.assembleMenus` that I haven't been able to get rid of.  This
is because they differ ever so slightly.

Most importantly perhaps we need to make the test case in `Test.Menu`
pass.  The reason it's not passing is that the saved test case does
not, in fact, contain an ambiguity.  There can of course be several
reasons for this.

Wide / narrow grammar
---

https://github.com/MUSTE-Project/MULLE/issues/4

Do we want to keep supporting `muste-cgi`?
---

AFAIK CGI scripts just speak a different protocol from
`application/json`.  So this should be easy to keep support for.
