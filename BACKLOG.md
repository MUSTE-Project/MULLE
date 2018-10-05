BACKLOG
=======

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

Wide / narrow grammar
---

https://github.com/MUSTE-Project/MULLE/issues/4

Do we want to keep supporting `muste-cgi`?
---

AFAIK CGI scripts just speak a different protocol from
`application/json`.  So this should be easy to keep support for.

Add `NFData` instance for `Grammar`.
---

This will allow for better benchmarking, but unfortunately require an
`NFData` instance for `PGF`.

Consider removing the rows source- and target language
---

We're relying on the sentence object given us the correct information
about the language of that sentence, so we don't really need the
source- and target- language rows in the DB anymore.

Issue #50: User registration
---

Added a page for adding new users. TODO

* Handle case when user already exists.

Issue #57: Do not hard code exercises and known grammars.
---

This feature is done.  Unfortunately `f2c10e7` introduces a
significant performance regression.  I don't really know how this can
be since it should only impact when the application is being
initialized.  This should probably be fixed before this feature is
merged in.

Configuration options
---

It would be nice to find a simpler way of managing configuration
options/the environment.  See [the relevant section in the readme
file](README.md#An abundance of configuration methods).
