/*global $ jQuery Set Map : true*/

var SPACETOKENS = new Set([
  null,
  ...SPECIALS.spacetokens.bind,
  ...SPECIALS.spacetokens.newline,
  ...SPECIALS.spacetokens.indent
]);


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

  $('[data-popup]').click(function(evt) {
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
  $(document).on('overlay', function() {
    $overlay.show();
  });
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
    console.log("Setting i18n language:", lng);
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
  console.log("Initialising i18n languages:", langs.join(" "));

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
  console.log("Showing page:", page);
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
      // window.sessionStorage.setItem('LOGIN_TOKEN',LOGIN_TOKEN);
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
  console.log("Buidling boxes for", lessons.length, "lessons");
  var table = $('#lessonslist').empty();
  for (var l of lessons) {
    EXERCISES[l.lesson] = {
      passedcount: l.passedcount,
      totalcount:  l.exercisecount
    };
    $('<div>')
      .append([
        $('<h3>')
          .text(i18next.t(`backend.${l.lesson}.name`, l.name)),
        $('<button>')
          .click({
            lesson: l.lesson,
            restart: l.passed,
          }, start_exercise)
          .text(i18next.t(l.passed          ? 'lesson.reSolve' 
                          : l.passedcount>0 ? 'lesson.continue' 
                          :                   'lesson.solve'
                         )),
        $('<p>')
          .html(i18next.t(`backend.${l.lesson}.description`, l.description)),
        $('<meter>')
          .prop(update_progressbar(l.passedcount, l.exercisecount)),
        $('<p>')
          .text(l.score ? i18next.t('lesson.result', {score: l.score}) 
                :         i18next.t('lesson.noResult', "")
               ),
      ])
      .toggleClass('finished', l.passed)
      .toggleClass('disabled', !l.enabled)
      .appendTo(table);
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

function handle_menu_response(r) {
  DATA = r;
  show_exercise(r);
  if (r['lesson-over']) {
    var popup = i18next.t('exercise.lessonComplete', {returnObjects: true, data: r});
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
  else if (r['exercise-over']) {
    var popup = i18next.t('exercise.exerciseComplete', {returnObjects: true, data: r});
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
          lesson: r.lesson.key,
          restart: false,
        });
      } else {
        show_page('pageLessons');
      }
    });
  }
}

function show_exercise(resp) {
  var lesson = resp.lesson;
  var key = lesson.key;
  var lessonName = lesson.name;
  var menu = resp.menu;
  clean_server_data(menu.src);
  clean_server_data(menu.trg);
  show_sentences(menu, resp.settings);
  // The score is the exercise score.  Only in the case when we are
  // continuing a lesson will this be non-trivial.
  // display_score(resp.score);
  var e = EXERCISES[key];
  $('#exercisename')
    .text(i18next.t(`backend.${key}.name`, lessonName));
  $('#lessoncounter')
    .prop(update_progressbar(e.passedcount, e.totalcount));
}

function clean_server_data(data) {
  data.menu = new Map(data.menu);
}


function show_sentences(data, settings) {
  var src = data.src;
  var trg = data.trg;
  matchy_magic(src, trg);
  matchy_magic(trg, src);
  $('#src').toggle(settings['show-source-sentence']);
  show_lin('src', src, settings);
  show_lin('trg', trg, settings);
}

function all_classes(xs) {
  var xss = xs.map(function(x) { return x['classes'];});
  var flattened = [].concat.apply([], xss);
  return new Set(flattened);
}


function matchy_magic(src, trg) {
  var cs = all_classes(src.sentence.linearization);
  trg.sentence.linearization.forEach(function(x) {
    var s = intersection(cs, new Set(x['classes']));
    x['matching-classes'] = s;
  });
}

// intersection :: Set a -> Set a -> Set a
function intersection(m, n) {
  return new Set([...m].filter(function(x) {return n.has(x);}));
}

// special spacing tokens all start with "&"
function is_space_token(space) {
  return typeof space == 'string' && space[0] == '&';
}


function show_lin(lang, src, settings) {
  var lin = src.sentence.linearization;
  var sentence = $('#' + lang)
      .empty()
      .prop({dir: mk_direction(src.direction)});

  var indentation = 0;
  for (var i=0; i <= lin.length; i++) {
    var previous = i > 0 ? lin[i-1].concrete : null;
    var current = i < lin.length ? lin[i].concrete : null;

    // generate the space between tokens
    var validMenusSpace = getValidMenusSpace(i, src.menu);
    var isClickableSpace = validMenusSpace !== 'nothing';
    var isInvisibleSpace =
        SPECIALS.invisible.pre.has(previous) || SPACETOKENS.has(previous) || 
        SPECIALS.invisible.post.has(current) || SPACETOKENS.has(current);
    var isLinebreakSpace =
        SPECIALS.indentation.linebreak.pre.has(previous) ||
        SPECIALS.indentation.linebreak.post.has(current);
    var isIndent =
        SPECIALS.indentation.indent.pre.has(previous) ||
        SPECIALS.indentation.indent.post.has(current);
    var isDedent =
        SPECIALS.indentation.dedent.pre.has(previous) ||
        SPECIALS.indentation.dedent.post.has(current);

    var spaceSpan = $('<span>')
        .addClass('space')
        .html(isInvisibleSpace ? ' ' : '&nbsp;')
        .appendTo(sentence)
        .data({
          'nr': i,
          'lang': lang,
          'valid-menus': validMenusSpace,
          'direction': src.direction
        });

    if (isClickableSpace) {
      spaceSpan
        .addClass('clickable')
        .click(click_word);

      // make clickable spaces visible (greyed out)
      // TODO: this should be configurable
      // &oplus; ⊕ (U+2295 "CIRCLED PLUS")
      // &#xFE62; ﹢ (U+FE62 "SMALL PLUS SIGN")
      spaceSpan.html(isInvisibleSpace ? '+' : ' + ')
        .addClass('spaceword');
    }

    if (isLinebreakSpace) {
      spaceSpan.addClass('linebreak');
    }

    // generate the token following the space
    if (i < lin.length) {
      var validMenusWord = getValidMenus(i, src.menu);
      var isClickableWord = validMenusWord !== 'nothing';
      var classes = lin[i]['classes'];
      var matchingClasses = lin[i]['matching-classes'];
      var isMatch = matchingClasses.size > 0;

      var wordSpan = $('<span>')
          .addClass('word')
          .html(current)
          .appendTo(sentence)
          .data({
            'nr': i,
            'lang': lang,
            'classes': classes,
            'valid-menus': validMenusWord,
            'direction': src.direction
          });

      if (isLinebreakSpace) {
        if (isIndent) indentation++;
        if (isDedent) indentation--;
        wordSpan.addClass('indent' + indentation);
      }

      if (isClickableWord) {
        wordSpan
          .addClass('clickable')
          .click(click_word);
      }

      if (isMatch && settings['highlight-matches']) {
        wordSpan.addClass('match');
        var h = hash_array_of_string(Array.from(matchingClasses));
        var c = int_to_rgba(h);
        wordSpan.css('border-color', c);
      }

      if (SPACETOKENS.has(current)) {
        // the special space tokens are shown using special greyed-out symbols
        // TODO: this should be configurable
        if (SPECIALS.spacetokens.newline.has(current)) {
          // &#x23ce; ⏎ (U+23CE "RETURN SYMBOL")
          // &crarr; ↵ (U+21B5 "DOWNWARDS ARROW WITH CORNER LEFTWARDS")
          wordSpan.html(isClickableWord ? '⏎' : '')
            .addClass('spaceword linebreak');
        }
        if (SPECIALS.spacetokens.bind.has(current)) {
          // &bull; • (U+2022 "BULLET")
          // &middot; · (U+00B7 "MIDDLE DOT")
          wordSpan.html(isClickableWord ? ' ' : '')
            .addClass('spaceword bind');
        }
        if (SPECIALS.spacetokens.indent.has(current)) {
          // &hellip; … (U+2026 "HORIZONTAL ELLIPSIS")
          // &nbsp; (U+00A0 "NO-BREAK SPACE")
          wordSpan.html(isClickableWord ? '&hellip;' : '&nbsp;&nbsp;')
            .addClass('spaceword indent');
        }
      }

      if (DEBUG) {
        $('<sub class="debug">')
          .text((isMatch ? '=' : '') + JSON.stringify(classes))
          .appendTo(wordSpan);
      }
    }
  }
}

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

function update_menu(m, idx) {
  var prev = window.currentMenu;
  if (prev !== undefined && prev.idx != idx) {
    reset_selection();
  } else {
    remove_selection_highlighting();
  }
  window.currentMenu = {
    menu: m,
    idx: idx
  };
}

function remove_selection_highlighting() {
  $('.striked').removeClass('striked');
  $('#menus').empty();
}

function reset_selection() {
  remove_selection_highlighting();
  if (window.currentMenu != null) {
    window.currentMenu.menu.reset();
  }
}

function click_word(event) {
  function next_selection(sel) {
    return sel ? sel.slice(0, sel.length-1) : null;
  }
  function getSelection() {
    if (clicked.hasClass('striked')) {
      return next_selection($('#menus').data('selection'));
    }
    else if (clicked.hasClass('word')) {
      return path;
    }
    else if (clicked.hasClass('space')) {
      // Alternate between clicking `clicked`'s neighbors.
      // TODO Unipmlemented.
      return path;
    }
    else {
      // Fallback.  Just try to return `path`, maybe it'll
      // work.
      return path;
    }
  }
  var clicked = $(event.currentTarget).closest('.clickable');
  var lang = clicked.data().lang;
  var path = clicked.data().path;
  var validMenus = clicked.data('valid-menus');
  var idx = clicked.data('nr');
  var direction = mk_direction(clicked.data('direction'));
  // Marks some tokens to not be displayed.  Doesn't remove any
  // tokens, only marks them.
  var threshold = 1;
  function mark_relevant(toks, sel) {
    var t = 0;
    for (var i = 0 ; i < toks.length + threshold ; i++) {
      var tok = toks[i];
      if (tok !== undefined) {
        var s = is_selected(sel, i);
        tok['selected'] = s;
        if (s) t = threshold * 2 + 1;
      }
      var x = toks[i - threshold];
      if (x === undefined) continue;
      x['relevant'] = t > 0;
      t--;
    }
    // TODO: How to elegantly ensure checking relevancy of the last
    // `threshold` elements?
  }
  function mk_ellipsis() {
    var p = $('<span class="ellipsis">');
    var e = $('<span class="words">')
      .hide()
      .click(function() {
        $(this).show();
      });
    p.append(e)
      .append($('<span>...</span>'));
    return {
      parent: p,
      words: e
    };
  }
  function mark_selected_words(lin, sel) {
    mark_relevant(lin, sel);
    var $initial = menuitem;
    var $prevEllipsis;
    for (var i = 0 ; i < lin.length ; i++) {
      var tok = lin[i];
      var pword = tok.concrete;
      var marked = tok['selected'];
      var css = {};
      if (is_space_token(pword)) {
        css['display'] = 'none';
      }
      var $container;
      if (tok.relevant) {
        $container = $initial;
      } else {
        css['opacity'] = '0.5';
        var prevTok = lin[i-1];
        // If there was not previous token, or if the previous token
        // was relevant, then we must must create a new ellipsis.
        if (prevTok === undefined || prevTok.relevant) {
          var e = mk_ellipsis();
          $container = e.words;
          e.parent.appendTo($initial);
          $prevEllipsis = $container;
        } else {
          // It's an invariant that `$prevEllipsis` should be set now.
          $container = $prevEllipsis;
        }
      }
      $('<span>').text(pword)
        .addClass(marked ? 'marked' : 'greyed')
        .appendTo($container)
        .css(css);
      $('<span>').text(' ').appendTo($container);
    }
  }
  if (validMenus === 'nothing') {
    throw 'This should not happen';
  }
  if (validMenus === undefined) {
    throw 'No menu found';
  }

  if (clicked.hasClass('striked') && $('#menus ul').length > 1) {
    $('#menus ul').first().remove();
  }
  else {
    var selection = getSelection();
    update_menu(validMenus, idx);

    // These are the valid menus.  Now we must toggle between them
    // somehow.
    var nextElem = validMenus.next();
    if (nextElem === 'reset') {
      $(document).trigger('overlay-out');
      return;
    }
    var selsnmen = nextElem.value;
    // Again we changed the selection, we can try mapping the snd
    // component.
    selection  = selsnmen[0];
    var menus  = selsnmen[1];
    if (menus === null) throw 'No menu found';

    clicked.addClass('striked');
    $('#' + lang).find('.word')
      .filter(function(){
        var idx = $(this).data('nr');
        return is_selected(selection, idx);
      })
      .addClass('striked');

    var $menus = $('#menus');
    $menus.data('selection', selection);
    var ul = $('<ul>')
      .appendTo($menus);
    for (var i = 0; i < menus.length; i++) {
      var pr = menus[i];
      var item = pr[1]; // snd
      var menuitem = $('<span class="clickable">')
        .data('item', item)
        .data('lang', lang)
        .click(function() {
          var d = $(this).data();
          select_menuitem(d.item, d.lang);
        });
      var lin = item;
      if (lin.length == 0) {
        $('<span>').html('&empty;').appendTo(menuitem);
      } else {
        mark_selected_words(lin, pr[0]);
      }
      $('<li>')
        .prop({dir: direction})
        .append(menuitem)
        .appendTo(ul);

    }
  }

  var menu = $('.menu').show();
  popup_menu(clicked, menu);
}

function popup_menu(clicked, menu) {
  var offset = clicked.offset();
  var bot = offset.top + clicked.outerHeight();
  var diff = clicked.outerWidth() - menu.outerWidth();
  var mid = offset.left + diff / 2;
  var css = {
    'top': bot + 'px',
    'left': mid + 'px',
    'max-height': (window.innerHeight - bot - 6) + 'px'
  };
  menu.css(css).show();
  $(document)
    .trigger('overlay')
    .one('overlay-out', function() {
      menu.hide();
    });
}

function getValidMenus(idx, menu) {
  var mp = lookupKeySetRange(idx, menu);
  return iterateMenu(idx, mp);
}

function getValidMenusSpace(idx, menu) {
  var mp = lookupKeySetEmptyRange(idx, menu);
  return iterateMenu(idx, mp);
}

function iterateMenu(idx, mp) {
  var a = Array.from(mp);
  // This is a bit counter-intuitive perhaps, but this is because
  // when we call next we start by incrementing the counter.
  var initial = -1;
  var i = initial;
  if (a.length === 0) return 'nothing';
  return {
    next: function() {
      i++;
      if (i === a.length) {
        // TODO Return 'reset' now.
        i = initial;
        return 'reset';
      }
      return {'value': a[i]};
    },
    reset: function() {
      i = initial;
    }
  };
}

function to_client_tree(t) {
  return {
    'sentence': t.sentence,
    'direction': t.direction
  };
}

function select_menuitem(item, lang) {
  DATA.menu[lang].sentence.linearization = item;
  var data = DATA;
  var menu = data.menu;
  var score = data.score;
  var menuRequest = {
    'key': data.key,
    'lesson': data.lesson,
    'score': {
      'clicks': score.clicks,
      'time': get_elapsed_time()
      // 'time': get_elapsed_time_as_seconds()
    },
    'src': to_client_tree(menu.src),
    'trg': to_client_tree(menu.trg),
    'settings': data.settings
  };
  muste_request(menuRequest, 'menu')
    .then(handle_menu_response);
  $(document).trigger('overlay-out');
}


//////////////////////////////////////////////////////////////////////
// Selections

// Looks up a value in a set of selections.
// lookupKeySet :: Int -> Map [(Int, Int)] v -> [([(Int, Int)], v)]
function lookupKeySetRange(idx, map) {
  return lookupKeySetWith(idx, map, is_selected);
}

function lookupKeySetEmptyRange(idx, map) {
  return lookupKeySetWith(idx, map, is_selected_empty);
}

// is_selected :: Menu.Selection -> Int -> Bool
function is_selected(sel, idx) {
  function within(intval, i) {
    var a = intval[0];
    var b = intval[1];
    if (i < a) return false;
    if (i >= b) return false;
    return true;
  }
  for (var intval of sel) {
    if (within(intval, idx)) return true;
  }
  return false;
}

function is_selected_empty(sel, idx) {
  function within(intval, i) {
    var a = intval[0];
    var b = intval[1];
    if (a !== b) return false;
    return i === a;
  }
  for (var intval of sel) {
    if (within(intval, idx)) return true;
  }
  return false;
}

function* lookupKeySetWith(idx, map, f) {
  for (var item of map) {
    var ks = item[0];
    if (f(ks, idx)) {
      yield item;
    }
  }
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
      set_global_highscore_mapping(scores);
      populate_high_scores(scores);
      setup_score_bars(window.ScoreBar);
    });
};

function set_global_highscore_mapping(scores) {
  var xs = scores.map(function(score) {
    return [score.lesson.key, score.score];
  });
  var m = new Map(xs);
  window['high-scores'] = m;
}

function populate_high_scores(scores) {
  var table = $('#high-scores-table').empty();
  for (var row of scores) {
    var columns = [row.lesson.name, row.user.name, row.score.clicks, row.score.time];
    $('<tr>').append(
      columns.map(function(cell) {
        return $('<td>').text(cell);
      })
    ).appendTo(table);
  }
}

window.ScoreBar = (function() {
  function normalize(x) {
    return 1 / Math.log(x + 1);
  }
  function valuation(score) {
    return normalize(score.clicks) * normalize(score.time);
  }
  function getHighscore(lesson) {
    var h = window['high-scores'];
    return h.get(lesson);
  }
  function setup(_, canvas) {
    var $canvas = $(canvas).show();
    var data = $canvas.data();
    var score = data['score'];
    var lesson = data['lesson'];
    var ctx = canvas.getContext('2d');
    ctx.fillStyle = 'green';
    var highscore = getHighscore(lesson);
    // TODO What to do then?
    if (highscore === undefined) {
      $canvas.hide();
      return;
    }
    var h = valuation(highscore);
    var v = valuation(score);
    var w = canvas.width * v / h;
    ctx.fillRect(0, 0, w, canvas.height);
  }
  return {
    'setup': setup
  };
})();

function setup_score_bars(ScoreBar) {
  $('.score[data-score]').each(ScoreBar.setup);
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
