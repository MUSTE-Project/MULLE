The MUSTE Language Learning Environment
===

### Submitter

Frederik Hanghøj Iversen

### Participants:

  * Peter Ljunglöf
  * Herbert Lange
  * Frederik Hanghøj Iversen

### Description

*MULLE* -- The MUSTE Language Learning Environment -- is a web-based
interactive tool for learning a new language.  The user interface is
based on Multimodal Semantic Text Editing (MUSTE), which is a research
project about alternative methods for editing text, in the absence of
a keyboard.

MULLE consists of two parts, one being a library for generating valid
replacements of parts of a sentence written in natural language.  The
other part is a web UI for language learning exercises.  In the web UI
a user is presented with two sentences, one in a language they know,
and one in a language they are learning.  The user is then supposed to
transform the sentences into translations of each other.  This is done
by clicking parts of the sentences and choosing a substitution for
that part of the sentence from a menu of valid replacements.

The underlying library calculates possible modifications to the active
sentence, and ensures that the new suggestions are always well-formed
according to a predefined grammar.  The grammar is written in
Grammatical Framework, which is another project written in Haskell,
that describes natural language by using ideas from Martin Löf Type
Theory.

The application is extensible with respect to grammars and
exercises.  New grammars can easily be added, and adding exercises is
just a matter of writing down the source- and target sentences.

The project started around the beginning of 2016 but has recently
undergone a major overhaul.  It is released as free and open software
and can be accessed at: https://github.com/MUSTE-Project/MULLE
