
var I18N = I18N || {};

I18N.en = {
  flagicon: 'https://cdn2.iconfinder.com/data/icons/flags_gosquared/32/United-Kingdom_flat.png',
};

var en = I18N.en.translation = {};
en.app = {
  title: "MULLE",
  subtitle: "(MUSTE Language Learning Environment)",
  longtitle: "MULLE (MUSTE Language Learning Environment)",
  explanation: `
This is a game for training different grammatical aspects of another language you want to learn.
Each training lesson is divided into a number of translation exercises, 
where the goal is to turn the target sentence into a translation of the source sentence. 
The score is calculated from how effective you are in translating.
`,
};

en.nav = {
  createUser: "Create new user",
  settings: "Settings",
  logout: "Log out",
  highscores: "Highscores",
  instructions: "Instructions",
  help: "Help",
  abortExercise: "Abort",
  loginExisting: "Log in as existing user",
  showLessons: "Lessons",
};

en.user = {
  name: "User name:",
  pwd: "Password:",
  pwdAgain: "Write the password again:",
  pwdOld: "Old password:",
  pwdNew: "New password:",
  pwdNewAgain: "Write the new password again:",
  login: "Log in",
  createUser: "Create user",
  changePwd: "Change password",
};

en.lesson = {
  title: "Lessons",
  solve: "Solve",
  continue: "Continue",
  reSolve: "Restart",
  result: "Best score so far: {{lesson.score}} points",
  help: {
    title: "Instructions",
    html: `
  <p>Click on the lesson name to start an exercise of this lesson.</p>
  <p>When you finish all exercises within a lesson the lesson counts 
     as finished. Most exercises can be repeated as often as you like.</p>
`}};

en.exercise = {
  time: "Time:",
  score: "Score:",
  wide: "Grow/shink whitespaces",
  lessonComplete: {
    title: "Lesson {{data.lesson.name}} complete!",
    confirmButtonText: 'Show lessons',
    html: `
  <p>Bravo! You got {{data.lesson.score}} points in total.
  <p>Now you are finished with all exercises in this lesson!</p>
`},
  exerciseComplete: {
    title: "Exercise complete!",
    html: `
  <p>Bravo! You gained {{data.exercise.score}} points.
  <p>Do you want to continue with the next exercise?</p>
`},
  help: {
    title: "Instructions",
    html: `
  <p>You can click on a word (or between two words) and set it in focus. 
     A menu will appear which show other words or phrases that 
     fit into the same place as the ones in focus.</p>
  <p>The colors in the sentences give you hints where you have to change 
     parts to match them with the other sentence. If parts are already 
     highlighted in the same color they are already matching translations. 
     The parts where the colors don't match have to be changed.</p>
  <p>Sometimes you have to click several times onto a word to get the right translation.</p>
`}};

en.createUser = {
  title: "Create new user",
  userCreated: {
    title: "User created",
    text: "The user '{{user}}' is created, now you can log in",
    confirmButtonText: "Go to login page",
  },
};

en.settings = {
  title: "Change password",
  pwdChanged: {
    title: "Password updated",
    text: "The password for '{{user}}' is updated",
    confirmButtonText: "Go back to the lessons",
  },
};

en.highscores = {
  title: "High scores",
  lesson: "Lesson",
  user: "User",
  score: "Score",
};

en.modal = {
  ok: "OK",
  close: "Close",
  cancel: "Cancel",
  yes: "Yes",
  no: "No",
};

en.error = {
  title: "Error {{status}}",
  '2-0': "There is no such user",
  '2-8': "Wrong password",
  '2-10': "The user name already exists",
  unspecific: "<p>An error occurred</p><p>{{message}}</p>",
};
