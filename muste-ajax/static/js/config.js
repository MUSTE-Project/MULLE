
//////////////////////////////////////////////////////////////////////
// Url to the Muste server api

// var SERVER = 'https://...domain.../api/';
var SERVER = '/api/';


//////////////////////////////////////////////////////////////////////
// Special tokens - different kinds of whitespace

var SPECIALS = {
  token:  {'&+': "invisible",
           '&/': "linebreak",
          },
  before: {'.': "invisible",
           ',': "invisible",
           ';': "invisible",
           '!': "invisible",
           '?': "invisible",
           ')': "invisible",
           ']': "invisible",
           '}': "linebreak dedent",
          },
  after:  {'¡': "invisible",
           '¿': "invisible",
           '(': "invisible",
           '[': "invisible",
           '{': "linebreak indent",
           '}': "linebreak",
           ';': "linebreak",
          },
};
