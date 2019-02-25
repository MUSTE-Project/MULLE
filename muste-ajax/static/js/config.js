
//////////////////////////////////////////////////////////////////////
// Url to the Muste server api

// var SERVER = 'https://...domain.../api/';
var SERVER = '/api/';


//////////////////////////////////////////////////////////////////////
// Special tokens - different kinds of whitespace

var SPECIALS = {
  'spacetokens': {
    'bind'   : new Set(['&+']),
    'newline': new Set(['&/']),
    'indent' : new Set(['&_']),
  },
  'invisible': {
    'pre' : new Set(['¿', '¡', '(']),
    'post': new Set([',', ';', '.', '?', '!']),
  },
  'indentation': {
    'linebreak': {
      'pre' : new Set([';', '{', '}']),
      'post': new Set(),
    },
    'indent': {
      'pre' : new Set(['{']),
      'post': new Set(),
    },
    'dedent': {
      'pre' : new Set(),
      'post': new Set(['}']),
    },
  },
};
