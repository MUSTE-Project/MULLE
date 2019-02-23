
var I18N = I18N || {};

I18N.sv = {
  flagicon: 'https://cdn2.iconfinder.com/data/icons/flags_gosquared/32/Sweden_flat.png',
};

var sv = I18N.sv.translation = {};
sv.app = {
  title: "SKOGSMULLE",
  subtitle: "(språkträningsspelet)",
  longtitle: "Skogsmulle (språkträningsspelet)",
  explanation: `
Detta är ett spel för att träna olika grammatiska aspekter av ett språk som du vill lära dig.
Varje lektion är uppdelat i ett antal översättningsövningar, 
där målet är att ändra målmeningen till en översättning av källmeningen. 
Poängen beräknas från hur effektiv du är på att översätta.
`,
};

sv.nav = {
  createUser: "Skapa ny användare",
  settings: "Inställningar",
  logout: "Logga ut",
  highscores: "Poänglista",
  instructions: "Instruktioner",
  help: "Hjälp",
  abortExercise: "Avbryt",
  loginExisting: "Logga in som existerande användare",
  showLessons: "Lektioner",
};

sv.user = {
  name: "Användare:",
  pwd: "Lösenord:",
  pwdAgain: "Skriv lösenordet igen:",
  pwdOld: "Gammalt lösenord:",
  pwdNew: "Nytt lösenord:",
  pwdNewAgain: "Skriv det nya lösenordet igen:",
  login: "Logga in",
  createUser: "Skapa användare",
  changePwd: "Byt lösenord",
};

sv.lesson = {
  title: "Lektioner",
  solve: "Starta",
  'continue': "Fortsätt",
  reSolve: "Starta om",
  result: "Bästa hittills: {{score.clicks}} klick, {{score.time}} s",
  help: {title: "Instruktioner",
         content: `
  Klicka på en lektion för att sätta igång en övning. 
  När du har avslutat alla övningar inom en lektion så räknas lektionen som avslutad.
  De flesta lektioner kan göras om så ofta som du vill, även de som är avslutade.
`}};

sv.exercise = {
  time: "Tis:",
  score: "Poäng:",
  help: {title: "Instruktioner",
         content: `
  Klicka på ett ord (eller mellan två ord) för att markera det ordet.
  En meny dyker då upp som visar andra ord eller fraser som passar på samma ställe som det markerade.
  Färgerna i meningarna ger ett tips om vilka delar av meningen som behöver ändras för att matcha med den andra meningen.
  Om två ord är färgade i samma färg så har de redan en passande översättning. 
  De delar där färgerna inte stämmer överens behöver ändras.
  Ibland behöver du klicka flera gånger på samma ord för att få rätt översättning.
`}};

sv.createUser = {
  title: "Skapa ny användare",
  success: "Din nya användare är skapad, nu kan du logga in",
};

sv.settings = {
  title: "Byt lösenord",
};

sv.highscores = {
  title: "Poänglista",
  lesson: "Lektion",
  user: "Användare",
  clicks: "Poäng - klick",
  time: "Poäng - tid",
};

sv.backend = {
  1: {name: "Svenska",
      description: "Träna svenska <br/> (med markeringshjälp)",
     },
  2: {name: "Spanska",
      description: "Träna spanska <br/> (utan markeringshjälp)",
     },
  3: {name: "Kinesiska",
      description: "Träna kinesiska <br/> (testar icke-latinsk skrift)",
     },
  4: {name: "Arabiska",
      description: "Träna arabiska <br/> (testar höger-till-vänster och icke-latinsk skrift)",
     },
  5: {name: "Fusk-pidgin",
      description: "Träna fusk-pidgin <br/> (testar agglutinering och slumpmässig ordning mellan övningar)",
     },
};
