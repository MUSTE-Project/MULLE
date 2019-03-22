/*global $ jQuery Set Map : true*/


var DATA = null;
var LOGIN = {};
var DEBUG = null;
var EXERCISES = [];


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
      fetch_and_populate_lessons();
      fetch_and_populate_high_scores();
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
  LOGIN = {};
  muste_request({}, 'logout');
}

PAGES.pageLessons = function() {
  $('#lessonslist').empty();
  fetch_and_populate_lessons();
  fetch_and_populate_high_scores();
}

PAGES.pageExercise = function() {
  $('.sentence').empty();
}

PAGES.pageSettings = function() {
  $('#change-pwd-name').val(LOGIN.name);
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
    password: form.pwd.value
  };
  muste_request(data, 'login')
    .done(function(response) {
      LOGIN = {
        name: form.name.value,
        token: response['login-success'],
      };
      // window.sessionStorage.setItem('LOGIN_TOKEN',LOGIN.token);
      $('.username').text(form.name.value);
      show_page('pageLessons');
    });
}

FORMS.formCreateUser = function(form) {
  var data = {
    name: form.name.value,
    password: form.pwd.value
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
    'new-password': form.pwd.value,
    'old-password': form.oldPwd.value
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

function fetch_and_populate_lessons() {
  muste_request({}, 'lessons')
    .done(function(response) {
      populate_lessons(response.lessons);
    });
}

function populate_lessons(lessons) {
  console.log(`Building info boxes for ${lessons.length} lessons:`,
              lessons.map((l) => l.name).join(", "));
  var $table = $('#lessonslist').empty();
  for (var l of lessons) {
    EXERCISES[l.lesson] = {
      passedcount: l.passedcount,
      totalcount:  l.exercisecount
    };
    $('<div>')
      .append([
        $('<h3>')
          .text(i18next.t(`backend.${l.name}.name`, l.name)),
        $('<button>')
          .click({lesson: l.lesson, restart: l.passed}, start_exercise)
          .text(i18next.t(l.passed          ? 'lesson.reSolve' 
                          : l.passedcount>0 ? 'lesson.continue' 
                          :                   'lesson.solve'
                         )),
        $('<p>')
          .html(i18next.t(`backend.${l.name}.description`, l.description || '')),
        $('<meter>')
          .prop(update_progressbar(l.passedcount, l.exercisecount)),
        $('<p>')
          .text(l.score ? i18next.t('lesson.result', {score: l.score}) 
                :         i18next.t('lesson.noResult', "")
               ),
      ])
      .toggleClass('finished', l.passed)
      .toggleClass('disabled', !l.enabled)
      .appendTo($table);
  }
}


//////////////////////////////////////////////////////////////////////
// The exercise view

function start_exercise(data) {
  show_page('pageExercise');
  if (data.data) data = data.data;
  start_timer();
  muste_request(data, 'lesson/' + data.lesson)
    .then(handle_menu_response);
}

// handles the response from the MUSTE server
// containing the new sentences and menus
function handle_menu_response(data) {
  DATA = data;
  show_exercise(data);
  if (data['lesson-over']) {
    var popup = i18next.t('exercise.lessonComplete', {returnObjects: true, data: data});
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
  else if (data['exercise-over']) {
    var popup = i18next.t('exercise.exerciseComplete', {returnObjects: true, data: data});
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
          lesson: data.lesson.key,
          restart: false,
        });
      } else {
        show_page('pageLessons');
      }
    });
  }
}


//////////////////////////////////////////////////////////////////////
// Show the exercise to the user

// clean and annotate the linearisations and menus,
// then show the sentences
function show_exercise(data) {
  clean_lin_and_menu(data.menu.src);
  clean_lin_and_menu(data.menu.trg);
  matchy_magic(data.menu.src, data.menu.trg);
  matchy_magic(data.menu.trg, data.menu.src);
  show_sentence($('#src'), data.menu.src, data.settings);
  show_sentence($('#trg'), data.menu.trg, data.settings);
  register_sentence_hover();
  $('#src').toggle(data.settings['show-source-sentence']);
  var e = EXERCISES[data.lesson.key];
  $('#exercisename')
    .text(i18next.t(`backend.${data.lesson.key}.name`, data.lesson.name));
  $('#lessoncounter')
    .prop(update_progressbar(e.passedcount, e.totalcount));
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
  var lin = data.sentence.linearization;
  var original = annotate_and_remove_specials(lin);
  data.sentence.original = original;
  if (DEBUG) console.log(`Original:   ${strlin(original)}`);
  if (DEBUG) console.log(`Convereted: ${strlin(lin)}`);
  for (var menu of data.menu) {
    var sel = convert_specials_selection(menu[0], original);
    menu[0] = sel;
    for (var menuitem of menu[1]) {
      var origitem = annotate_and_remove_specials(menuitem[1]);
      menuitem.push(origitem);
    }
  }
  data.menu.sort((a,b) => size_selection(a[0]) - size_selection(b[0]));
  if (DEBUG) console.log("Menu selections:", data.menu.map((e)=>strsel(e[0])).join(", ")); 
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
  for (var tok of src.sentence.linearization) {
    for (var cls of tok.classes) {
      all_src_classes[cls] = true;
    }
  }
  for (var tok of trg.sentence.linearization) {
    var matching = {};
    for (var cls of tok.classes) {
      if (all_src_classes[cls]) matching[cls] = true;
    }
    tok.matchingClasses = Object.keys(matching);
  }
}

// build the sentence from the linearisation, and show it
function show_sentence($sentence, data, settings) {
  $sentence.empty().prop({dir: data.direction});
  build_lin($sentence, data.sentence.linearization);

  $sentence.children().each(function() {
    var position = $(this).data('nr');
    var isSpace = $(this).hasClass('space');
    if (has_menu(data.menu, position, isSpace)) {
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

  var all_menus = DATA.menu[lang].menu;
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

  var $popup = $('#menu');
  for (var i = 0; i < menu.length; i++) {
    var [sel, lin, original] = menu[i];
    var $menuitem = $('<li>')
        .prop({dir: direction})
        .addClass('menuitem clickable')
        .click({lin:original, lang:lang}, select_menuitem)
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

// when the user selects a menu item, the current state is sent to the server
function select_menuitem(event) {
  function mklang(lang) {
    return {direction: DATA.menu.src.direction,
            sentence: {language: lang.sentence.language,
                       linearization: lang.sentence.original},
           };
  }
  var menuRequest = {
    key     : DATA.key,
    lesson  : DATA.lesson,
    score   : {clicks   : DATA.score.clicks,
               time     : get_elapsed_time()},
    src     : mklang(DATA.menu.src),
    trg     : mklang(DATA.menu.trg),
    settings: DATA.settings,
  };
  // use the selected menu item as the new linearisation
  menuRequest[event.data.lang].sentence.linearization = event.data.lin;
  muste_request(menuRequest, 'menu')
    .then(handle_menu_response);
  reset_selection();
}


//////////////////////////////////////////////////////////////////////
// Scores

function update_progressbar(passed, total) {
  return {low:     1.5,
          high:    total-0.5,
          max:     total,
          optimum: total,
          value:   passed,
         };
}

function fetch_and_populate_high_scores() {
  muste_request({}, 'high-scores')
    .then(function (scores) {
      // for testing purposes:
      scores.push(
        {lesson: {name:"Fake"}, user: {name:"Lisa"}, score: {clicks:3, time:6}},
        {lesson: {name:"Faker"}, user: {name:"Pelle"}, score: {clicks:999, time:666}},
      ); // end test
      populate_high_scores(scores);
    });
};

function populate_high_scores(scores) {
  var $table = $('#high-scores-table').empty();
  for (var row of scores) {
    var columns = [row.lesson.name, row.user.name, row.score.clicks, row.score.time];
    $('<tr>').append(
      columns.map(function(cell) {
        return $('<td>').text(cell);
      })
    ).appendTo($table);
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
