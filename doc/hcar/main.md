The Multi Semantic Language Learning Environment
===

*MULLE* -- The Multi Semantic Language Learning Environment -- is a
front end to the Grammatical Framework (another project written in
Haskell) that describes natural language by using ideas from Martin
Löf Type Theory.  MULLE consists of two parts, a library for
generating valid replacements of part of a sentence written in natural
language.  The other part is a web UI for language learning exercises.
In the web UI a user is presented with two sentences, one in a
language they speak, and one in a language they are learning.  The
user is then supposed to transform the sentences into translations of
each other.  This is done by clicking parts of the sentences and
choosing a substitution for that part of the sentence from a menu of
valid replacements.  The underlying library ensures that the sentence
is always well-formed according to the grammar.  The application is
extensible with respects to grammars and exercises.  New grammars can
easily be added, and adding exercises is just a matter of writing down
the source- and target sentence.

The project started around the beginning of 2016 but has recently
undergoing a major overhaul.  Further information:
https://github.com/MUSTE-Project/MULLE
