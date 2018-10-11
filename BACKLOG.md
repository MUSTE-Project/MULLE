BACKLOG
=======

What to do when a lesson is over?
---

Currently is a user tries to open a lesson where they have solved all
exercises, then an error to that effect is logged in the browser
console.

Retrieve necessary data on navigation start
---

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

Configuration options
---

It would be nice to find a simpler way of managing configuration
options/the environment.  See [the relevant section in the readme
file](README.md#An abundance of configuration methods).
