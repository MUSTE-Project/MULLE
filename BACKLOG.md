BACKLOG
=======

Increase response time of continuing a lesson
--

Due to the way updating the exercise counter (for the active lesson) I
have resorted to implementing keeping this up-to-date when we finish
an exercise by sequencing the following two actions:

  * fetch all lessons (this is how the lesson counter is kept up-to-date
  * get the current menu for the current exercise

This means that response-time when finishing an exercise will now be
the sum of those two actions in stead of doing them in parallel as
would be otherwise possible.

A nicer fix would be to change how the exercise/lesson-counter is kept
up-to-date.  Needs a bit of thought.

Update solved exercise counter while solving exercises
---

The global variable `Exercises` are only updated after a `lessons` request.

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

