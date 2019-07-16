
var I18N = I18N || {};

var sv = I18N.sv.translation.backend = {};

sv.courses = {
  'Swedish': {
    name: 'Svenska',
    description: 'Träna svenska',
  },

  'Other languages': {
    name: 'Övriga språk',
    description: 'Träna övriga språk (inte svenska)',
  },

  'Programming': {
    name: 'Programmering',
    description: 'Träna att programmera',
  }
};

sv.lessons = {
  // Translations for the lessons in "examples/lessons-swedish.yaml"
  'English-Swedish': {
    name: "Engelska – Svenska",
    description: "Träna svenska med engelska exempelmeningar",
  },
  'Spanish-Swedish': {
    name: "Spanska – Svenska",
    description: "Träna svenska med spanska exempelmeningar",
  },

  // Translations for the lessons in "examples/lessons-otherlangs.yaml"
  'Spanish': {
    name: "Spanska",
    description: "Träna spanska <br/> (visar inte matchande ord)",
  },
  'Chinese': {
    name: "Kinesiska",
    description: "Träna kinesiska <br/> (icke-latinsk skrift)",
  },
  'Arabic': {
    name: "Arabiska",
    description: "Träna arabiska <br/> (höger-till-vänster och icke-latinsk skrift)",
  },
  'FakePidgin': {
    name: "Fusk-pidgin",
    description: "Träna fusk-pidgin <br/> (agglutinering och slumpmässig ordning mellan övningar)" +
      "<br/> Obs: detta är inte ett existerande språk!",
  },

  // Translations for the lessons in "examples/lessons-programming.yaml"
  'Programming': {
    name: "Imperativ programmering",
    description: "Lek med ett imperativt programmeringsspråk",
  },
};
