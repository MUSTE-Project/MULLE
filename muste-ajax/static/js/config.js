
//////////////////////////////////////////////////////////////////////
// Url to the Muste server api

// var SERVER = 'https://...domain.../api/';
var SERVER = '/api/';


//////////////////////////////////////////////////////////////////////
// Special tokens - different kinds of whitespace

var SPECIALS = {
  invisible: {
    token: new Set(['&+']),
    pre  : new Set(['&+', '¿', '¡', '(']),
    post : new Set(['&+', ',', ';', '.', '?', '!']),
  },
  linebreak: {
    pre  : new Set([';', '{', '}']),
    post : new Set(),
  },
  indent: {
    pre  : new Set(['{']),
    post : new Set(),
  },
  dedent: {
    pre  : new Set(),
    post : new Set(['}']),
  },
};
