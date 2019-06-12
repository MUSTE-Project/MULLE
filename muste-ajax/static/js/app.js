/*Global $ jQuery : true*/


var DATA = {};
var LOGIN = {};
var DEBUG = null;

var LESSON_ORDER = [];
var LESSONS = {};


//////////////////////////////////////////////////////////////////////
// Initialisation

jQuery().ready(init);

function init() {
  init_environment();
  init_i18n();
  handle_url_search_params();
  $('body').show();
  register_handlers();
  register_timer();
  register_overlay();
  window.onbeforeunload = function(e) {
    e.preventDefault();
    e.returnValue = "";
  }
}

function init_environment() {
  window.muste = {};
}

function init_jconfirm() {
  jconfirm.defaults = {
    useBootstrap: false,
    theme: 'modern',
    boxWidth: '50%',
  };
}

function handle_url_search_params() {
  let searchParams = new URLSearchParams(window.location.search);
  if (searchParams.has('debug')) {
    console.log("DEBUG MODE");
    DEBUG = true;
  }
}

function register_handlers() {
  $('form').submit(submit_form);
  $('input[type=password]').change(check_matching_passwords);

  $('[data-page]').click(show_page);

  $('[data-popup]').click(function() {
    var popup = i18next.t($(this).data('popup'), {returnObjects: true});
    Swal.mixin({
      showCloseButton: true,
      confirmButtonText: i18next.t('modal.ok'),
    }).fire(
      popup
    );
  });
}

// The overlay is shown when the menus pop up.  The click-event on the
// overlay resets the selection - which hides the menu again.
function register_overlay() {
  var $overlay = $('.overlay');
  $('.overlay').click(function() {
    $(this).hide();
    reset_selection();
  });
}


//////////////////////////////////////////////////////////////////////
// Using the i18next framework, with its jQuery plugin:
// https://www.i18next.com/
// https://github.com/i18next/jquery-i18next

var DEFAULT_LANGUAGE;

function set_language(evt) {
  var lng = evt && evt.data && evt.data.language || DEFAULT_LANGUAGE;
  i18next.changeLanguage(lng, function(err, t) {
    console.log(`Setting i18n language: ${lng}`);
    if (err) return console.error('ERROR setting language', lng, err);
    // https://github.com/i18next/jquery-i18next#usage-of-selector-function
    $('title').localize();
    $('body').localize();
    if (LOGIN.token) {
      show_page('pageLessons');
    }
  });
}


function init_i18n() {
  var langs = [];
  for (var lng in I18N) {
    if (!DEFAULT_LANGUAGE) DEFAULT_LANGUAGE = lng;
    langs.push(lng);
    var iconurl = I18N[lng].flagicon;
    $('<a>')
      .append($('<img>').prop({src: iconurl}))
      .click({language: lng}, set_language)
      .appendTo($('.change-language'))
  }
  console.log(`Initialising i18n languages: ${langs.join(" ")}`);

  // https://www.i18next.com/overview/configuration-options
  // evtl. load via xhr https://github.com/i18next/i18next-xhr-backend
  i18next.init({
    whitelist: langs,
    resources: I18N,
  },
  function(err, t) {
    // https://github.com/i18next/jquery-i18next#initialize-the-plugin
    jqueryI18next.init(i18next, $);
    set_language();
  });
}


//////////////////////////////////////////////////////////////////////
// PAGES

var PAGES = {};

function show_page(page) {
  if (page.currentTarget) page = $(page.currentTarget).data('page');
  console.log(`Displaying page: ${page}`);
  if (typeof PAGES[page] === "function") {
    PAGES[page] ();
  }
  $('main').hide();
  $('#' + page).show();
}

PAGES.pageLogin = function() {
  if (LOGIN.token) {
    muste_request({}, 'logout');
    LOGIN = {};
  }
}

PAGES.pageLessons = function() {
  muste_request({}, 'get-completed-lessons')
    .done(function(lessons) {
      for (var less of lessons) {
        set_score_if_better(LESSONS[less.lesson], less.score);
        console.log("Reading completed lesson:",
                    `${less.lesson}, score: ${less.score}`);
      }

      muste_request({}, 'get-completed-exercises')
        .done(function(exercises) {
          for (var ex of exercises) {
            set_score_if_better(LESSONS[ex.lesson].exercises[ex.exercise], ex.score);
            console.log("Reading completed exercise:",
                        `${ex.exercise} in ${ex.lesson}, score: ${ex.score}`);
          }

          populate_lessons();
        });
    });
}

PAGES.pageExercise = function() {
  $('.sentence').empty();
}

PAGES.pageSettings = function() {
  $('#change-pwd-name').val(LOGIN.name);
}

PAGES.pageHighScores = function() {
  fetch_and_populate_high_scores();
}


//////////////////////////////////////////////////////////////////////
// FORMS

var FORMS = {};

function submit_form(event) {
  event.preventDefault();
  var form = event.currentTarget;
  if (form.form) form = form.form;
  if (typeof FORMS[form.id] === "function") {
    FORMS[form.id] (form);
  }
}

FORMS.formLogin = function(form) {
  var data = {
    name: form.name.value,
    pwd: form.pwd.value
  };
  muste_request(data, 'login')
    .done(function(response) {
      LOGIN = {
        name: form.name.value,
        token: response['token'],
      };
      $('.username').text(form.name.value);

      muste_request({}, 'get-lessons')
        .done(function(lessons) {
          LESSON_ORDER = [];
          LESSONS = {};
          for (var less of lessons) {
            LESSON_ORDER.push(less.name);
            LESSONS[less.name] = less;
            for (var nr = 0; nr < less.exercises.length; nr++) {
              less.exercises[nr].nr = nr;
            }
          }
          console.log("Reading lessons:", LESSON_ORDER);
          show_page('pageLessons');
        });
    });   
}

FORMS.formCreateUser = function(form) {
  var data = {
    name: form.name.value,
    pwd: form.pwd.value
  };
  muste_request(data, 'create-user')
    .done(function() {
      var popup = i18next.t('createUser.userCreated', {returnObjects: true, user: data.name});
      Swal.mixin({
        showCloseButton: true,
        allowOutsideClick: false,
        timer: 3000,
      }).fire(
        popup
      ).then(function() {
        show_page('pageLogin');
      });
    });
}

FORMS.formChangePwd = function(form) {
  var data = {
    name: form.name.value,
    newpwd: form.pwd.value,
    oldpwd: form.oldPwd.value
  };
  muste_request(data, 'change-pwd')
    .done(function() {
      var popup = i18next.t('settings.pwdChanged', {returnObjects: true, user: data.name});
      Swal.mixin({
        showCloseButton: true,
        allowOutsideClick: false,
        timer: 3000,
      }).fire(
        popup
      ).then(function() {
        show_page('pageLessons');
      });
    });
}

function check_matching_passwords(event) {
  var form = event.currentTarget.form;
  if (form.form) form = form.form;
  if (form.pwd && form.confirmPwd) {
    if (form.pwd.value === form.confirmPwd.value) {
      form.confirmPwd.setCustomValidity('');
    } else {
      form.confirmPwd.setCustomValidity('Password must match');
    }
  }
}


//////////////////////////////////////////////////////////////////////
// Timers

function register_timer() {
  window.setInterval(update_timer, 500);
}

function start_timer() {
  window.muste['lesson-start'] = new Date();
}

function get_start_time() {
  return window.muste['lesson-start'];
}

// Gets the elapsed time as a floating point representing the seconds passed by.
function get_elapsed_time() {
  var diff = new Date() - get_start_time();
  return diff / 1000;
}

function update_timer() {
  var time = get_elapsed_time();
  $('#timer').text(Math.round(time));
  var score = Math.max(0, Math.min(100, 105 - time));
  $('#score').text(Math.round(score));
}


//////////////////////////////////////////////////////////////////////
// Ajax requests

// Returns a promise with the request. Reports errors.
function muste_request(data, endpoint) {
  busy_start();
  if (LOGIN.token) data.token = LOGIN.token;
  if (DEBUG) console.log(`AJAX request (${endpoint}):`, data);
  var request = {
    cache: false,
    url: SERVER + endpoint,
    dataType: 'json',
    method: 'POST',
    processData: false,
    data: JSON.stringify(data)
  };
  return $.ajax(request)
    .fail(function(jqXHR, textStatus, errorThrown) {
      var error = jqXHR.responseJSON || jqXHR.responseText || jqXHR || "Unknown error";
      if (error.error) error = error.error;
      var status = error.id || jqXHR.status;
      var message = error.message || error;
      var errorinfo = {status: status, message: message};
      console.error(`AJAX ERROR (${endpoint}):`, errorThrown, status, `"${message}"`);
      if (DEBUG) console.error(`AJAX HEADER (${endpoint}):`, jqXHR.getAllResponseHeaders(), jqXHR);
      Swal.fire({
        type: 'error',
        title: i18next.t('error.title', errorinfo),
        html: i18next.t([`error.${status}`, 'error.unspecific'], errorinfo),
        confirmButtonText: i18next.t('modal.close'),
        confirmButtonColor: 'red',
        allowOutsideClick: false,
      });
    })
    .done(function(data, textStatus, jqXHR) {
      if (DEBUG) console.log(`AJAX result (${endpoint}):`, data, jqXHR.getAllResponseHeaders(), jqXHR);
    })
    .always(busy_end);
}


//////////////////////////////////////////////////////////////////////
// The lessons view

// build the lesson boxes
function populate_lessons() {
  console.log(`Building info boxes for ${LESSON_ORDER.length} lessons:`,
              LESSON_ORDER.join(", "));
  var $table = $('#lessonslist').empty();
  for (var name of LESSON_ORDER) {
    var lesson = LESSONS[name];
    var finished = lesson.score > 0;
    var nr_exercises = lesson.exercises.length;
    var nr_solved = get_unsolved(lesson.exercises).length;
    $('<div>')
      .append([
        $('<h3>')
          .text(i18next.t(`backend.${name}.name`, name)),
        $('<button>')
          .click({lesson: name, exercise: nr_solved}, start_exercise)
          .text(i18next.t(nr_solved>0 ? 'lesson.continue'
                          : finished  ? 'lesson.reSolve' 
                          :             'lesson.solve'
                         )),
        $('<p>')
          .html(i18next.t(`backend.${name}.description`, lesson.description || '')),
        $('<meter>')
          .prop(update_progressbar(nr_solved, nr_exercises)),
        $('<p>')
          .text(finished ? i18next.t('lesson.result', {lesson: lesson}) 
                :          i18next.t('lesson.noResult', "")
               ),
      ])
      .toggleClass('finished', finished)
      .toggleClass('disabled', lesson.disabled == true)
      .appendTo($table);
  }
}


//////////////////////////////////////////////////////////////////////
// The exercise view

// clean and annotate the linearisations and menus,
// then show the sentences
function start_exercise(data) {
  if (data.data) data = data.data;
  show_page('pageExercise');
  DATA = {};
  DATA.lesson = LESSONS[data.lesson];
  DATA.exercise = DATA.lesson.exercises[data.exercise];
  function trimlin(sent) {
    return sent.trim().split(/\s+/).map((t) => ({concrete:t}));
  }
  DATA.src = {original: trimlin(DATA.exercise.source)};
  DATA.trg = {original: trimlin(DATA.exercise.target)};
  update_sentences_and_menus();
}


// when the exercise is completed
function exercise_over() {
  DATA.exercise.score = calculate_exercise_score(DATA.exercise);
  var next_exercise = DATA.exercise.nr + 1;

  if (next_exercise >= DATA.lesson.exercises.length) {
    DATA.lesson.score = calculate_lesson_score(DATA.lesson.exercises)
    for (var ex of DATA.lesson.exercises) {
      delete ex.score;
    }
    var request = {
      lesson: DATA.lesson.name,
      score: DATA.lesson.score,
    };
    muste_request(request, 'add-completed-lesson');

    var popup = i18next.t('exercise.lessonComplete', {returnObjects: true, data: DATA});
    Swal.mixin({
      type: 'success',
      allowOutsideClick: false,
      allowEscapeKey: false,
      timer: 5000,
    }).fire(
      popup
    ).then(function() {
      show_page('pageLessons');
    });
  }

  else{
    var request = {
      lesson: DATA.lesson.name,
      exercise: DATA.exercise.nr,
      score: DATA.exercise.score,
    };
    muste_request(request, 'add-completed-exercise');

    var popup = i18next.t('exercise.exerciseComplete', {returnObjects: true, data: DATA});
    Swal.mixin({
      type: 'success',
      showCancelButton: true,
      confirmButtonText: i18next.t('modal.yes'),
      cancelButtonText: i18next.t('modal.no'),
      allowOutsideClick: false,
      allowEscapeKey: false,
    }).fire(
      popup
    ).then(function(reply) {
      if (reply && !reply.dismiss) {
        start_exercise({
          lesson: DATA.lesson.name,
          exercise: next_exercise,
        });
      } else {
        show_page('pageLessons');
      }
    });
  }
}

//////////////////////////////////////////////////////////////////////
// Show the exercise to the user

function update_sentences_and_menus(newdata) {
  if (newdata && newdata.data) newdata = newdata.data;
  if (newdata && newdata.lang && newdata.lin) {
    DATA[newdata.lang].original = DATA[newdata.lang].lin = newdata.lin;
  }
  var request = {
    grammar: DATA.lesson.grammar,
    src: {lang: DATA.lesson.languages.source, lin: DATA.src.original},
    trg: {lang: DATA.lesson.languages.target, lin: DATA.trg.original},
  };
  reset_selection();
  muste_request(request, 'get-edit-distance')
    .done(function(result) {
      console.log("Current edit distance:", result);
      if (result.distance == 0) {
        // show the final sentences, but without menus
        DATA.src.menus = DATA.trg.menus = [];
        handle_menu_response(DATA);
        // show the "exercise complete" dialogue after a delay
        setTimeout(exercise_over, 500);
      } else {
        muste_request(request, 'get-menus')
          .done(handle_menu_response);
      }
    });
}


// handles the response from the MUSTE server
// containing the new sentences and menus
function handle_menu_response(response) {
  DATA.src = response.src;
  DATA.trg = response.trg;
  clean_lin_and_menu(DATA.src);
  clean_lin_and_menu(DATA.trg);
  matchy_magic(DATA.src, DATA.trg);
  matchy_magic(DATA.trg, DATA.src);

  if (DATA.lesson.settings['hide-source-sentence']) {
    $('#src').hide();
  } else {
    $('#src').show();
    show_sentence($('#src'), DATA.src, DATA.lesson.settings);
  }
  show_sentence($('#trg'), DATA.trg, DATA.lesson.settings);
  register_sentence_hover();
  var nr_exercises = DATA.lesson.exercises.length;
  var nr_solved = get_unsolved(DATA.lesson.exercises).length;
  $('#exercisename')
    .text(i18next.t(`backend.${DATA.lesson.name}.name`, DATA.lesson.name));
  $('#lessoncounter')
    .prop(update_progressbar(nr_solved, nr_exercises))
}


function register_sentence_hover() {
  $(".sentence > span").hover(function() {
    $(this).next().addClass("hovered-neighbour");
    $(this).prev().addClass("hovered-neighbour");
  }, function() {
    $(this).next().removeClass("hovered-neighbour");
    $(this).prev().removeClass("hovered-neighbour");
  });
}


// clean the linearisation and the menu for a language
// i.e., remove all special tokens from the linearisation
// (which means that we have to change the selections too)
function clean_lin_and_menu(data) {
  data.original = annotate_and_remove_specials(data.lin);
  if (DEBUG) console.log(`Original:   ${strlin(data.original)}`);
  if (DEBUG) console.log(`Convereted: ${strlin(data.lin)}`);
  for (var menu of data.menus) {
    var sel = convert_specials_selection(menu[0], data.original);
    menu[0] = sel;
    for (var menuitem of menu[1]) {
      var origitem = annotate_and_remove_specials(menuitem[1]);
      menuitem.push(origitem);
    }
  }
  data.menus.sort((a,b) => size_selection(a[0]) - size_selection(b[0]));
  if (DEBUG) console.log("Menu selections:", data.menus.map((e)=>strsel(e[0])).join(", ")); 
}

// convert indexes that refer to the space before a special token, to the space after
// i.e., [2-3], [3-3], [3-4], [3-5] --> [2-4], [4-4], [4-4], [4-5]
// if the 3rd token is a special (invisible, linebreak, etc.)
function convert_specials_selection(sel, lin) {
  var is_special = (j) => j >= 0 && j < lin.length && SPECIALS.token[lin[j].concrete];
  return sel.map(
    (interval) => interval.map((j) => is_special(j) ? j+1 : j)
  );
}

// removes special tokens, and annotates the whitespaces (invisible, linebreak, etc)
// NOTE: this function modifies the lin in place!
// so we return a deep copy of the original 
function annotate_and_remove_specials(lin) {
  var original = JSON.parse(JSON.stringify(lin));
  // loop downwards so that deletions don't mess with the order
  for (var i = lin.length-1; i >= 0; i--) {
    lin[i].nr = i;
    var classes = SPECIALS.token[lin[i].concrete] || "";
    if (classes) {
      lin.splice(i, 1);
    }
    classes += " " + (SPECIALS.before[lin[i].concrete] || "");
    if (i > 0) {
      classes += " " + (SPECIALS.after[lin[i-1].concrete] || "");
    }
    lin[i].space = classes.trim();
  }
  return original;
}

// calculate which words are matched with another with in the other sentence
function matchy_magic(src, trg) {
  var all_src_classes = {};
  for (var tok of src.lin) {
    for (var cls of tok.classes || []) {
      all_src_classes[cls] = true;
    }
  }
  for (var tok of trg.lin) {
    var matching = {};
    for (var cls of tok.classes || []) {
      if (all_src_classes[cls]) matching[cls] = true;
    }
    tok.matchingClasses = Object.keys(matching);
  }
}

// build the sentence from the linearisation, and show it
function show_sentence($sentence, data, settings) {
  $sentence.empty().prop({dir: data.direction});
  build_lin($sentence, data.lin);

  $sentence.children().each(function() {
    var position = $(this).data('nr');
    var isSpace = $(this).hasClass('space');
    if (has_menu(data.menus, position, isSpace)) {
      $(this)
        .addClass('clickable')
        .click(click_word);
    }
  });

  if (settings['highlight-matches']) {
    $sentence.children('.word').each(function() {
      var matchingClasses = $(this).data('matchingClasses');
      if (matchingClasses && matchingClasses.length > 0) {
        var colour = int_to_rgba(hash_array_of_string(matchingClasses));
        $(this)
          .addClass('match')
          .css('border-color', colour);
      }
    });
  }                                   
}

// true if the given word/space has a menu that can be shown
// (i.e., if there is a selection that covers the given position)
function has_menu(menus, position, is_insertion) {
  for (var entry of menus) {
    if (is_selected(entry[0], position, is_insertion)) return true;
  }
  return false;
}

// create the HTML sentece from the given linearisation
// and annotate the spaces with CSS classes (invisible, linebreak, etc)
function build_lin($sentence, lin) {
  var indentation = 0;
  for (var tok of lin) {
    // generate the space between tokens
    var $space = $('<span>')
        .append($('<span>'))
        .addClass('space')
        .addClass(tok.space)
        .data(tok)
        .appendTo($sentence);

    if ($space.hasClass('indent')) indentation++;
    if ($space.hasClass('dedent')) indentation--;
    if ($space.hasClass('linebreak')) $space.addClass('indentation i' + indentation);

    // generate the token following the space
    var $word = $('<span>')
        .append($('<span>').html(tok.concrete))
        .addClass('word')
        .data(tok)
        .appendTo($sentence);

    var nr = tok.nr; // this is only to get the position for the final space below

    // show the semantics as subscript to the word
    if (DEBUG) {
      $('<sub class="debug">')
        .text(tok.classes.join(" "))
        .appendTo($word);
    }
  }

  // add the final space
  $('<span>')
    .append($('<span>'))
    .addClass('space')
    .data({nr: nr+1})
    .appendTo($sentence);
}


//////////////////////////////////////////////////////////////////////
// When the user clicks words/spaces and selects menu items

// when the user clicks a word/space, the system shows a new menu
// if the clicked token is already selected, the next menu in turn is shown,
// otherwise the first menu for that token
function click_word(event) {
  var $clicked  = $(this); 
  var $sentence = $clicked.closest('.sentence');
  var idx       = $clicked.data('nr');
  var lang      = $sentence.prop('id');
  var direction = $sentence.prop('dir');

  var all_menus = DATA[lang].menus;
  var is_insertion = $clicked.hasClass('space');
  var entry = next_menu(all_menus, idx, is_insertion);
  if (!entry) {
    $('.overlay').hide();
    return
  }
  var [selection, menu] = entry;
  console.log(`Selection ${strsel(selection)}: ${menu.length} menu items`);

  $clicked.addClass('selected');
  mark_selected_words($sentence, selection);

  if (DEBUG) console.log("CLICK", idx, lang, direction);
  var $popup = $('#menu');
  for (var i = 0; i < menu.length; i++) {
    var [sel, lin, original] = menu[i];
    var $menuitem = $('<li>')
        .prop({dir: direction})
        .addClass('menuitem clickable')
        .click({lin:original, lang:lang}, update_sentences_and_menus)
        .appendTo($popup);
    build_lin($menuitem, lin);
    var newsel = remove_insertions_from_selection(sel);
    mark_selected_words($menuitem, newsel);

    // TODO: the threshold should be configurable
    var threshold = 2;
    $menuitem.children().addClass('irrelevant');
    $menuitem.children('.selected').each(function() {
      $(this).removeClass('irrelevant');
      $(this)
        .prevAll()
        .slice(0, threshold)
        .removeClass('irrelevant');
      $(this)
        .nextAll()
        .slice(0, threshold)
        .removeClass('irrelevant');
    });
  }
  popup_menu($clicked, $popup);
}

// global variable used by reset_selection and next_menu below
var CURRENT_SELECTION;

// removes the current selection, and hides the popup menu
function reset_selection() {
  $('.selected').removeClass('selected');
  $('#menu').hide().empty();
  CURRENT_SELECTION = null;
}

// returns the next menu, if the position is already selected
// otherwise the first menu for the given position
function next_menu(menus, position, is_insertion) {
  var current = CURRENT_SELECTION;
  if (typeof current === 'number' && current >= 0 &&
      is_selected(menus[current][0], position, is_insertion)) {
    current++;
  } else {
    current = 0;
  }
  reset_selection();
  for (; current < menus.length; current++) {
    if (is_selected(menus[current][0], position, is_insertion)) {
      CURRENT_SELECTION = current;
      return menus[current];
    }
  }
  return null;
}

// adds the CSS class 'selected' to all words/spaces
// that are in the given selection
function mark_selected_words($sentence, selection) {
  $sentence.children()
    .filter(function(){
      var idx = $(this).data('nr');
      if ($(this).hasClass('space')) {
        return selection.some(
          ([i,j]) => idx == i && idx == j
        ) && !selection.some(
          ([i,j]) => i < idx && idx <= j || i <= idx && idx < j
        );
      } else {
        return is_selected(selection, idx);
      }
    })
    .addClass('selected');
}

// remove all insertions that adjacent to a replacement
// i.e., keep 4-4 in [2-3;4-4;5-6], but remove from [2-3;4-4;4-6] and [2-4;4-4;5-6]
function remove_insertions_from_selection(selection) {
  return selection.filter(([i,j]) => {
    if (i < j) return true;
    return ! selection.some(([n,m]) => n < m && (i == n || i == m));
  });
}

// shows the popup menu just below the selected word
function popup_menu($clicked, $menu) {
  var offset = $clicked.offset();
  var bot = offset.top + $clicked.outerHeight();
  var diff = $clicked.outerWidth() - $menu.outerWidth();
  var mid = offset.left + diff / 2;
  var bottom_margin = 10; // pixels
  var css = {
    'top': bot + 'px',
    'left': mid + 'px',
    'max-height': (window.innerHeight - bot - bottom_margin) + 'px'
  };
  $menu.css(css).show();
  $('.overlay').show();
}


//////////////////////////////////////////////////////////////////////
// Scores

function calculate_lesson_score(exercises) {
  var total = exercises.reduce((sum,ex) => sum + ex.score, 0);
  var bonus = 0;
  return total + bonus;
}

function calculate_exercise_score(exercise) {
  return 10 + Math.round(Math.random() * 20);
}

function set_score_if_better(obj, score) {
  if (obj.score && obj.score > score) return;
  obj.score = score;
}

function update_progressbar(passed, total) {
  return {low:     1.5,
          high:    total-0.5,
          max:     total,
          optimum: total,
          value:   passed,
         };
}

function fetch_and_populate_high_scores() {
  muste_request({}, 'get-highscores')
    .then(function (scores) {
      populate_high_scores(scores);
    });
};

function populate_high_scores(scores) {
  var highscores = {};
  for (var row of scores) {
    var current = highscores[row.lesson];
    if (!current || row.score > current.score) {
      highscores[row.lesson] = {score: row.score, users: [row.user]};
    } else if (row.score == current.score && !current.users.includes(row.user)) {
      current.users.push(row.user);
    }
  }
  var $table = $('#high-scores-table').empty();
  for (var lesson of LESSON_ORDER) {
    var $row = $('<tr>')
        .append($('<td>').text(i18next.t(`backend.${lesson}.name`, lesson)))
        .appendTo($table);
    if (highscores[lesson]) {
      $row.append(
        $('<td>').text(highscores[lesson].score),
        $('<td>').text(highscores[lesson].users)
      );
    } else {
      $row.append(
        $('<td>').html("&mdash;"),
        $('<td>').html("&mdash;")
      );
    }
  }
}


//////////////////////////////////////////////////////////////////////
// Busy indicator

var BUSY_CALLS = 0;

function busy_start() {
  BUSY_CALLS++;
  $('#busy-indicator').show();
  $('.overlay').show();
}

function busy_end() {
  BUSY_CALLS--;
  if (BUSY_CALLS > 0) return;
  $('#busy-indicator').hide();
  $('.overlay').hide();
}


//////////////////////////////////////////////////////////////////////
// Converting class names to colour values

function hash_array_of_string(as) {
  var hash = 0;
  for (var i = 0 ; i < as.length ; i++) {
    var a = as[i];
    hash  = ((hash << 5) - hash) + hash_string(a);
    hash |= 0;
  }
  return hash;
}

function hash_string(s) {
  var hash = 0;
  for (var i = 0; i < s.length; i++) {
    var chr  = s.charCodeAt(i);
    hash  = ((hash << 5) - hash) + chr;
    hash |= 0; // Convert to 32bit integer
  }
  return hash;
}

function int_to_rgba(num) {
  num >>>= 0;
  var b = num & 0xFF,
    g = (num & 0xFF00) >>> 8,
    r = (num & 0xFF0000) >>> 16,
    // a = ( (num & 0xFF000000) >>> 24 ) / 255 ;
    a = 1;
  return 'rgba(' + [r, g, b, a].join(',') + ')';
}


//////////////////////////////////////////////////////////////////////
// Utilities

// deep equality between objects
function equal(a, b) {
  return JSON.stringify(a) === JSON.stringify(b);
}

// given a list of exercises, return only the ones that are unsolved
// (i.e., have a score > 0)
function get_unsolved(exercises) {
  return exercises.filter((e) => e.score > 0);
}

// return if a position is inside the selection
function is_selected(sel, j, is_insertion) {
  if (!sel) return false;
  for (var [i, k] of sel) {
    if (is_insertion) {
      if (i == j && j == k) return true;
      if (i < j && j < k) return true;
    } else {
      if (i <= j && j < k) return true;
    }
  }
  return false;
}

// the size of a selection, used when sorting them
function size_selection(selection) {
  var size = 0;
  for (var [i,j] of selection) {
    // The added small constant is so that empty intervals are also counted.
    // With this, the selection {2-3} will come before {2-2,2-3}.
    // And we add i so that {1-2} will come before {2-3}.
    size += 100 * (j-i) + 1 + i;
  }
  return size;
}

// some synonyms for 'rtl' and 'ltr' directions
function mk_direction(direction) {
  switch (direction) {
  case 'right-to-left':
  case 'rtl':
  case 'recto-verso':
    return 'rtl';
  case 'left-to-right':
  case 'ltr':
  case 'verso-recto':
  default:
    return 'ltr';
  }
}


//////////////////////////////////////////////////////////////////////
// For debugging purposes

function strsel(sel) {
  if (!sel || !sel.length) return "[?]";
  return "[" + sel.map((interval) => interval.join("-")).join(";") + "]";
}

function strlin(lin) {
  return lin.map((t) => `[${t.space||''}]${t.nr||''} ${t.concrete}`).join(" ");
}
