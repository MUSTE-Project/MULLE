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

Set expiry on session cookie
---

We have core logic for handling rejecting expired cookie.  HTTP also
supports this notion, so why not let user agents know when we expire
their session?

Move more parameters into location or query params
---

Issue #2: Improved support for insertion
----

https://github.com/MUSTE-Project/MULLE/issues/2

We should now correctly be reporting which trees are to be considered
"insertions", we now need to make the front end act on this.

We need to decide is how to encode an insertion as a `Selection`.

Automatically generate .pgf files
---

Make this a part of the build pipeline.  The user currently needs to
manually call `make`.

Issue #10: Make client oblivious to `TTree`s
---

https://github.com/MUSTE-Project/MULLE/issues/10

Builds on #3: https://github.com/MUSTE-Project/MULLE/issues/3

Wide / narrow grammar
---

https://github.com/MUSTE-Project/MULLE/issues/4

Do we want to keep supporting `muste-cgi`?
---

AFAIK CGI scripts just speak a different protocol from
`application/json`.  So this should be easy to keep support for.
