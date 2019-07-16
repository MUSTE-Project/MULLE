
var I18N = I18N || {};

var en = I18N.en.translation.backend = {};

en.courses = {
  'Swedish': {
    name: 'Swedish',
    description: 'Learn Swedish',
  },

  'Other languages': {
    name: 'Other languages',
    description: 'Learn other languages (not Swedish)',
  },

  'Programming': {
    name: 'Programming',
    description: 'Learn to program',
  }
};

en.lessons = {
  // Translations for the lessons in "examples/lessons-swedish.yaml"
  'English-Swedish': {
    name: "English—Swedish",
    description: "Learn Swedish from English example sentences",
  },
  'Spanish-Swedish': {
    name: "Spanish—Swedish",
    description: "Learn Swedish from Spanish example sentences",
  },

  // Translations for the lessons in "examples/lessons-otherlangs.yaml"
  'Spanish': {
    name: "Spanish",
    description: "Learn Spanish <br/> (don't show matching words)",
  },
  'Chinese': {
    name: "Chinese",
    description: "Learn Chinese <br/> (non-Latin script)",
  },
  'Arabic': {
    name: "Arabic",
    description: "Learn Arabic <br/> (right-to-left and non-Latin script)",
  },
  'FakePidgin': {
    name: "Fake Pidgin",
    description: "Learn Fake Pidgin <br/> (agglutination and random exercise order)" +
      "<br/> Note: this is not an existing language!",
  },

  // Translations for the lessons in "examples/lessons-programming.yaml"
  'Programming': {
    name: "Imperative programming",
    description: "Play with an imperative programming language",
  },

};
