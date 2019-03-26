
var I18N = I18N || {};

I18N.sv = {
  flagicon: 'https://cdn2.iconfinder.com/data/icons/flags_gosquared/32/Sweden_flat.png',
};

var sv = I18N.sv.translation = {};
sv.app = {
  title: "MULLE",
  subtitle: "(språkträningsspelet)",
  longtitle: "Mulle (språkträningsspelet)",
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
  continue: "Fortsätt",
  reSolve: "Starta om",
  result: "Bästa hittills: {{score.clicks}} klick, {{score.time}} s",
  help: {
    title: "Instruktioner",
    html: `
  <p>Klicka på en lektion för att sätta igång en övning.</p>
  <p>När du har avslutat alla övningar inom en lektion så räknas lektionen som avslutad.
     De flesta lektioner kan göras om så ofta som du vill, även de som är avslutade.</p>
`}};

sv.exercise = {
  time: "Tid:",
  score: "Poäng:",
  wide: "Utöka/krymp mellanrummen",
  lessonComplete: {
    title: "Lektion {{data.lesson.name}} klar!",
    confirmButtonText: 'Visa lektionerna',
    html: `
  <p>Bravo! Du använde {{data.score.clicks}} klick under {{data.score.time}} sekunder.</p>
  <p>Nu är du klar med alla övningar i denna lektion!</p>
`},
  exerciseComplete: {
    title: "Övningen klar!",
    html: `
  <p>Bravo! Du använde {{data.score.clicks}} klick under {{data.score.time}} sekunder.</p>
  <p>Vill du fortsätta med nästa övning?</p>
`},
  help: {
    title: "Instruktioner",
    html: `
  <p>Klicka på ett ord (eller mellan två ord) för att markera det ordet.
     En meny dyker då upp som visar andra ord eller fraser som passar 
     på samma ställe som det markerade.</p>
  <p>Färgerna i meningarna ger ett tips om vilka delar av meningen som 
     behöver ändras för att matcha med den andra meningen.
     Om två ord är färgade i samma färg så har de redan en passande översättning. 
     De delar där färgerna inte stämmer överens behöver ändras.</p>
  <p>Ibland behöver du klicka flera gånger på samma ord för att få rätt översättning.</p>
`}};

sv.createUser = {
  title: "Skapa ny användare",
  userCreated: {
    title: "Användare skapad",
    text: "Användaren '{{user}}' är skapad, nu kan du logga in",
    confirmButtonText: "Gå till inloggningen",
  },
};

sv.settings = {
  title: "Byt lösenord",
  pwdChanged: {
    title: "Lösenordet uppdaterat",
    text: "Lösenordet för '{{user}}' har uppdaterats",
    confirmButtonText: "Gå tillbaka till lektionerna",
  },
};

sv.highscores = {
  title: "Poänglista",
  lesson: "Lektion",
  user: "Användare",
  clicks: "Poäng - klick",
  time: "Poäng - tid",
};

sv.modal = {
  ok: "OK",
  close: "Stäng",
  cancel: "Avbryt",
  yes: "Ja",
  no: "Nej",
};

sv.error = {
  title: "Fel {{status}}",
  '2-0': "Det finns ingen sådan användare",
  '2-8': "Fel lösenord",
  '2-10': "Användarnamnet finns redan",
  unspecific: "<p>Ett fel inträffade</p><p>{{message}}</p>",
};
