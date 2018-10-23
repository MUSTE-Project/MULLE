/*global $ Handlebars jQuery Set Map countdown : true*/
var AGGLUTINATION = '&+';
var PUNCTUATION = /^[,;.?!)]$/;
var PREFIXPUNCT = /^[¿¡(]$/;

var DATA = null;
var LOGIN_TOKEN = null;

var EXERCISES = [];
var VIRTUAL_ROOT = '/';
var SERVER = VIRTUAL_ROOT + 'api/';

jQuery().ready(init);

function init() {
  init_environment();
  register_handlebars_helper();
  register_click_handlers();
  register_busy_indicator(jQuery);
  register_timer();
  register_overlay();
  register_pagers();
  register_create_user_handler();
  register_change_pwd_handler();
  register_popup_menu(jQuery);
  register_page_handler(jQuery);
  register_high_score_handler(jQuery);
  register_lessons_listener(jQuery);
  show_login_page();
}

function init_environment() {
  window.muste = {};
}

function register_click_handlers() {
  $('#loginform').submit(submit_login);
  $('#abortlesson').click(retrieve_lessons);
  $('#logoutbutton').click(restart_everything);
}

function show_login_page() {
  var tok = window.sessionStorage.getItem('LOGIN_TOKEN');
  // Show login page regardless.
  change_page('#page-login');
  if (tok == null) {
    var loginform = document.getElementById('loginform');
    loginform.name.focus();
  } else {
    LOGIN_TOKEN = tok;
    retrieve_lessons();
  }
}

function register_popup_menu($) {
  $.fn.popup = popup_menu;
}

function register_pagers() {
  $('[data-pager]').click(function() {
    var pg = $(this).data('pager');
    change_page(pg);
  });
}

function register_create_user_handler() {
  var $form = $('form[action=create-user]');
  password_matcher($form);
  $form.on('submit', function (event) {
    event.preventDefault();
    var data = {
      'password': $form.find('input[name=pwd]').val(),
      'name': $form.find('input[name=name]').val()
    };
    muste_request(data, 'create-user').then(function() {
      change_page('#page-login');
    }).fail(function(err) {
      var appErr = err.responseJSON.error;
      switch(appErr.id) {
      case 10:
        alert('User name is already taken');
        break;
      default:
        break;
      }
    });
  });
}

function password_matcher($form) {
  $form.find('input').change(function() {
    var pwd  = $form.find('input[name=pwd]').val();
    var $pwdC = $form.find('input[name=confirm-pwd]');
    var cpwd = $pwdC.val();
    if(pwd !== cpwd) {
      $pwdC.each(function () {
        this.setCustomValidity('Password must match');
      });
      return;
    }
    // Input value is now valid.
    this.setCustomValidity('');
  });
}

function register_change_pwd_handler() {
  var $form = $('form[action=change-pwd]');
  password_matcher($form);
  $form.on('submit', function (event) {
    event.preventDefault();
    var data = {
      'new-password': $form.find('input[name=pwd]').val(),
      'old-password': $form.find('input[name=old-pwd]').val(),
      'name': $form.find('input[name=name]').val()
    };
    muste_request(data, 'change-pwd').then(function() {
      change_page('#page-login');
    });
  });
}

function register_timer() {
  window.setInterval(update_timer, 500);
}

function start_timer() {
  window.muste['lesson-start'] = new Date();
}

function get_start_time() {
  return window.muste['lesson-start'];
}

// Returns a formatted string of the elapsed time. Note that currently
// this is not locale sensitive.
function get_elapsed_time() {
  var start = get_start_time();
  var now   = new Date();
  return countdown(start, now);
}

// Gets the elapsed time as a floating point representing the seconds
// passed by.
function get_elapsed_time_as_seconds() {
  var e = get_elapsed_time();
  var start = e.start;
  var end = e.end;
  // 'diff' is in ms.
  var diff = end - start;
  return diff / 1000;
}

// TODO l10n
function get_elapsed_time_formatted() {
  return get_elapsed_time().toString();
}

function update_timer() {
  $('#timer').text(get_elapsed_time_formatted());
}

// The overlay is shown when the menus pop up.  The click-event on the
// overlay resets the selection - which hides the menu again.
function register_overlay() {
  var $overlay = $('.overlay');
  $(document).on('overlay', function() {
    $overlay.show();
  });
  $('.overlay').click(function() {
    $(document).trigger('overlay-out');
  });
  $(document).on('overlay-out', function() {
    $overlay.hide();
    reset_selection();
    clear_errors();
  });
}

function clear_errors() {
  $('.error').empty().hide();
}

function change_page(page, opts) {
  var d = {
    page: page,
    'query-opts': opts
  };
  $(window).trigger('page-change', d);
}

function register_page_handler($) {
  var $w = $(window);
  $w.on('popstate', function() {
    var href = window.location.href;
    // FIXME Hack
    var ref = href.substring(href.lastIndexOf('/') + 1);
    var idx = ref.indexOf('?');
    var id;
    if(idx === -1) {
      id = ref;
    } else {
      ref.substring(0, idx);
    }
    var loc = ref.substring(idx);
    change_page(id, loc);
  });
  $w.on('page-change', function (_ev, d) {
    var pg = d.page;
    var q = d['query-opts'] || '';
    var loc = pg + q;
    show_page(pg);
    history.pushState(null, null, loc);
  });
}

function show_page(pg) {
  $('.page').hide();
  $(pg).show();
}


function restart_everything() {
  muste_request({}, 'logout');
  change_page('#page-login');
}


function submit_login(evt) {
  if (evt && evt.preventDefault) {
    evt.preventDefault();
  }
  var loginform = document.getElementById('loginform');
  var req = {name: loginform.name.value, password: loginform.pwd.value};
  muste_request(req, 'login')
    .then(login_success)
    .fail(function() {
      alert('User name or password incorrect');
    });
}

// Returns a promise with the request.  Reports errors according to
// the protocol.  In contrast with `call_server_new` does not try to
// guess how to interpret the response.
function muste_request(data, endpoint) {
  var $w = $(window);
  $w.trigger('api-load-start');
  var req = {
    cache: false,
    url: SERVER + endpoint,
    dataType: 'json',
    method: 'POST',
    processData: false,
    data: JSON.stringify(data)
  };
  return $.ajax(req).fail(handle_server_fail).always(function() {
    $w.trigger('api-load-end');
  });
}

function handle_server_fail(resp) {
  display_error(resp);
  switch(resp.status) {
  case 401:
    muste_logout();
    break;
  case 400:
  default:
    break;
  }
  resp.fail();
}

function muste_logout() {
  change_page('#page-login');
  window.sessionStorage.removeItem('LOGIN_TOKEN');
}

function display_error(resp) {
  if(resp.responseJSON === undefined) {
    // We've received a response object that we didn't expect.
    console.error(resp.responseText);
    return;
  }
  var err = resp.responseJSON;
  console.error(err.error.message);
}

function register_handlebars_helper() {
  Handlebars.registerHelper({
    eq: function (v1, v2) {
      return v1 === v2;
    },
    ne: function (v1, v2) {
      return v1 !== v2;
    },
    lt: function (v1, v2) {
      return v1 < v2;
    },
    gt: function (v1, v2) {
      return v1 > v2;
    },
    lte: function (v1, v2) {
      return v1 <= v2;
    },
    gte: function (v1, v2) {
      return v1 >= v2;
    },
    and: function () {
      return Array.prototype.slice.call(arguments).every(Boolean);
    },
    or: function () {
      return Array.prototype.slice.call(arguments, 0, -1).some(Boolean);
    },
    json: function(context) {
      return JSON.stringify(context);
    }
  });
}

// Fetches the lessons and triggers a custom event afterwards.
function fetch_lessons() {
  return muste_request({}, 'lessons').then(function(r) {
    $(window).trigger('lessons-loaded', {lessons: r.lessons});
    return r;
  });
}

// Also shows the lessons afterwards.
function retrieve_lessons(evt) {
  if (evt && evt.preventDefault) {
    evt.preventDefault();
  }
  fetch_lessons().then(show_lessons);
}

var lesson_list_template = ' \
<div class="lessons"> \
{{#each .}} \
 <div class="{{#if (or passed (gte passed total))}}finished{{/if}} {{#if enabled}}{{else}}disabled{{/if}}"> \
  <div class="lesson-info"> \
   <div> \
    <h3>{{name}}</h3> \
    <p> \
     {{passedcount}} avklarade av {{exercisecount}} övningar \
    </p> \
    {{#if score}} \
    <p> \
     Your score so far: <span>{{score.clicks}} klick i {{score.time}} sekunder</span> \
     <canvas class="score" data-lesson="{{lesson}}" data-score="{{json score}}"></canvas></td> \
    </p> \
    {{/if}} \
    <p> \
     {{description}} \
    </p> \
   </div> \
   <div class="lesson-info-button"> \
    <button {{#if enabled}}{{else}}disabled{{/if}} onclick="start_lesson({{lesson}});">Solve</button> \
   </div> \
  </div> \
 </div> \
{{/each}} \
</div> \
';

var render_lesson_list = Handlebars.compile(lesson_list_template);

function show_lessons(resp) {
  var lessons = resp.lessons;
  change_page('#page-lessons');
  var table = $('#lessonslist');
  table.empty();
  var e = render_lesson_list(lessons);
  table.html(e);
}

function register_lessons_listener($) {
  function update_exercises(_, x) {
    x.lessons.forEach(function(x) {
      var key = x.lesson;
      EXERCISES[key] = {
        passed: x.passedcount,
        total: x.exercisecount
      };
    });
  }
  $(window)
    .on('lessons-loaded', update_exercises)
    .on('lessons-loaded', window.fetch_high_scores);
}

// Warning defined but never used.  What gives?
function select_lesson(evt) { // eslint-disable-line no-unused-vars
  if (evt && evt.preventDefault) {
    evt.preventDefault();
  }
  start_lesson($(this).data('lesson'));
}


function start_lesson(lesson) {
  start_timer();
  muste_request({}, 'lesson/' + lesson)
    .then(handle_menu_response);
}

function handle_menu_response(r) {
  var key = r.lesson.key;
  var menu = r.menu;
  // FIXME Naughty string interpolation!
  change_page('#page-exercise', '?key=' + key);
  DATA = r;
  if(menu !== null) {
    show_exercise(r);
  } else {
    if(r['lesson-over'] == true) {
      show_exercise_complete(r);
      return;
    }
    continue_lesson(key);
  }
}

function continue_lesson(key) {
  // We need to sequence fetch_lessons and start_lesson due to the way
  // updating the lesson counter is handlded.
  fetch_lessons().then(function () {
    start_lesson(key);
  });
}

function show_exercise(resp) {
  var lesson = resp.lesson;
  var key = lesson.key;
  var lessonName = lesson.name;
  var menu = resp.menu;
  clean_server_data(menu.src);
  clean_server_data(menu.src);
  build_matching_classes(menu);
  show_sentences(menu, resp.settings);
  // The score is the exercise score.  Only in the case when we are
  // continuing a lesson will this be non-trivial.
  // display_score(resp.score);
  var e = EXERCISES[key];
  display_lesson_counter({
    lesson: lessonName,
    passed: e.passed,
    total: e.total
  });
}

// function display_score(score) {
//   $('#score-clicks').text(score.clicks);
//   $('#score-time').text(score.time);
// }

function display_lesson_counter(d) {
  $('#lessoncounter').text(d.lesson + ': övning ' + d.passed + ' av ' + d.total);
}

function show_exercise_complete(resp) {
  var score = resp.score;
  setTimeout(function(){
    alert('BRAVO!' +
      '    Klick: ' + score.clicks +
      '    Tid: ' + score.time + ' sekunder');
    // There used to be a way of figuring out if we should just start
    // the next exercise.  This is no longer possible.
    retrieve_lessons();
  }, 500);
}

// ct_linearization :: ClientTree -> Sentence.Linearization
function ct_linearization(t) {
  return t.sentence.linearization;
}
function ct_setLinearization(t, l) {
  t.sentence.linearization = l;
}

function login_success(resp) {
  LOGIN_TOKEN = resp.token;
  window.sessionStorage.setItem('LOGIN_TOKEN',LOGIN_TOKEN);
  retrieve_lessons();
}

function clean_server_data(data) {
  data.menu = new Map(data.menu);
}


function build_matching_classes(data) {
  var MAX_CLASSES = 4;

  data.matching_classes = {};
  var matching_class = 0;
  ['src', 'trg'].forEach(function(lang) {
    ct_linearization(data[lang]).forEach(function(token) {
      if (token.matched && token.matched.length && !data.matching_classes[token.path]) {
        data.matching_classes[token.path] = 'match-' + matching_class;
        matching_class = (matching_class + 1) % MAX_CLASSES;
      }
    });
  });
}

function show_sentences(data, settings) {
  var src = data.src;
  var trg = data.trg;
  var srcL = ct_linearization(src);
  var trgL = ct_linearization(trg);
  matchy_magic(srcL, trgL);
  matchy_magic(trgL, srcL);
  show_lin('src', srcL, src, settings);
  show_lin('trg', trgL, trg, settings);
}

function all_classes(xs) {
  var xss = xs.map(function(x) { return x['classes'];});
  var flattened = [].concat.apply([], xss);
  return new Set(flattened);
}


function hash_array_of_string(as) {
  var hash = 0;
  for(var i = 0 ; i < as.length ; i++) {
    var a = as[i];
    hash  = ((hash << 5) - hash) + hash_string(a);
    hash |= 0;
  }
  return hash;
}

function hash_string(s) {
  var hash = 0, i, chr;
  if (s.length === 0) return hash;
  for (i = 0; i < s.length; i++) {
    chr  = s.charCodeAt(i);
    hash  = ((hash << 5) - hash) + chr;
    hash |= 0; // Convert to 32bit integer
  }
  return hash;
}

function matchy_magic(src, trg) {
  var cs = all_classes(src);
  trg.forEach(function(x) {
    var s = intersection(cs, new Set(x['classes']));
    x['matching-classes'] = s;
  });
}

// intersection :: Set a -> Set a -> Set a
function intersection(m, n) {
  return new Set([...m].filter(function(x) {return n.has(x);}));
}

function show_lin(lang, lin, x, settings) {
  var menu = x.menu;

  function gen_item(validMenus, idx) {
    var spacyData = {
      nr: idx,
      lang: lang,
      'valid-menus': validMenus,
      'direction': x.direction
    };
    var $span = $('<span>');
    if(validMenus === 'nothing') return $span;
    return $span
      .addClass('clickable')
      .data(spacyData)
      .click(click_word);
  }

  function gen_space(validMenus, idx) {
    return gen_item(validMenus, idx)
      .addClass('space');
  }

  function gen_word(validMenus, idx, linTok) {
    var classes = linTok['classes'];
    var matchingClasses = linTok['matching-classes'];
    var concrete = linTok['concrete'];
    var match = matchingClasses.size > 0;
    var wordData = {
      nr: i,
      lang: lang,
      'classes': classes,
      /* , subtree:subtree */
      'valid-menus': validMenus,
      'direction': x.direction
    };
    // Perhaps we could generalize gen_space and use that here as well?
    var wordspan = $('<span>')
      .addClass('word');
    if(validMenus !== 'nothing') {
      wordspan.addClass('clickable')
        .data(wordData)
        .click(click_word);
    }
    wordspan
      .html(concrete + '<sub class="debug">' + (match ? '=' : '') + JSON.stringify(classes) /* + ' ' + show_tree(subtree) */ + '</sub>')
      .appendTo(sentence);
    if (match && settings['highlight-matches']) {
      wordspan.addClass('match');
      var h = hash_array_of_string(Array.from(matchingClasses));
      var c = int_to_rgba(h);
      var css = {
        'border-color': c
      };
      wordspan.css(css);
    }
    var css_word = {};
    if(concrete == AGGLUTINATION) {
      css_word['display'] = 'none';
    }
    return wordspan.css(css_word);
  }

  var css = {
    'direction': mk_direction(x.direction),
    'unicode-bidi': 'bidi-override'
  };
  var sentence = $('#' + lang)
    .empty()
    .css(css);
  // var tree = parse_tree(DATA[lang].tree);
  for (var i=0; i < lin.length; i++) {
    var linTok = lin[i];
    var previous = i > 0 ? lin[i-1].concrete : null;
    var current = linTok.concrete;
    var spacing = (previous == AGGLUTINATION || current == AGGLUTINATION || PREFIXPUNCT.test(previous) || PUNCTUATION.test(current))
      ? ' ' : ' &emsp; ';
    var validMenusSpace = getValidMenusSpace(i, menu);
    var validMenus = getValidMenus(i, menu);

    gen_space(validMenusSpace, i)
      .html(spacing)
      .appendTo(sentence);

    gen_word(validMenus, i, linTok);
  }
  var validMenusSpace = getValidMenusSpace(lin.length, menu);
  gen_space(validMenusSpace, lin.length)
    .html('&emsp;')
    .appendTo(sentence);
}

function mk_direction(direction) {
  switch(direction) {
  case 'left-to-right':
  case 'ltr':
  case 'verso-recto':
    return 'ltr';
  case 'right-to-left':
  case 'rtl':
  case 'recto-verso':
    return 'rtl';
  }
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

function update_menu(m, idx) {
  var prev = window.currentMenu;
  if(prev !== undefined && prev.idx != idx) {
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
  if(window.currentMenu != null) {
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
  var clicked = $(event.target).closest('.clickable');
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
    for(var i = 0 ; i < toks.length + threshold ; i++) {
      var tok = toks[i];
      if(tok !== undefined) {
        var s = is_selected(sel, i);
        tok['selected'] = s;
        if(s) t = threshold * 2 + 1;
      }
      var x = toks[i - threshold];
      if(x === undefined) continue;
      x['relevant'] = t > 0;
      t--;
    }
    // TODO: How to elegantly ensure checking relevancy of the last
    // `threshold` elements?
  }
  function mk_ellipsis() {
    var p = $('<span class="ellipsis">');
    var e
      = $('<span class="words">')
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
    for(var i = 0 ; i < lin.length ; i++) {
      var tok = lin[i];
      var pword = tok.concrete;
      var marked = tok['selected'];
      var css = {};
      if(pword == AGGLUTINATION) {
        css['display'] = 'none';
      }
      var $container;
      console.info(tok.relevant);
      if(tok.relevant) {
        $container = $initial;
      } else {
        css['opacity'] = '0.5';
        var prevTok = lin[i-1];
        // If there was not previous token, or if the previous token
        // was relevant, then we must must create a new ellipsis.
        if(prevTok === undefined || prevTok.relevant) {
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
  if(validMenus === 'nothing') {
    throw 'This should not happen';
  }
  if(validMenus === undefined) {
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
    if(nextElem === 'reset') {
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
    var css = {
      'direction': direction,
      'unicode-bidi': 'bidi-override'
    };
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
        .css(css)
        .append(menuitem)
        .appendTo(ul);

    }
  }

  var menu = $('.menu').show();
  clicked.popup(menu);
}

function popup_menu(menu) {
  var offset = this.offset();
  var bot = offset.top + this.outerHeight();
  var diff = this.outerWidth() - menu.outerWidth();
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

// is_selected :: Menu.Selection -> Int -> Bool
function is_selected(sel, idx) {
  function within(intval, i) {
    var a = intval[0];
    var b = intval[1];
    if(i < a) return false;
    if(i >= b) return false;
    return true;
  }
  for(var intval of sel) {
    if(within(intval, idx)) return true;
  }
  return false;
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
  if(a.length === 0) return 'nothing';
  return {
    next: function() {
      i++;
      if(i === a.length) {
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

// Looks up a value in a set of keys. Returns the key and value where
// the value is present in the key.

// lookupKeySet :: Int -> Map [(Int, Int)] v -> [([(Int, Int)], v)]
function lookupKeySetRange(idx, map) {
  return lookupKeySetWith(idx, map, is_selected);
}

function is_selected_empty(sel, idx) {
  function within(intval, i) {
    var a = intval[0];
    var b = intval[1];
    if(a !== b) return false;
    return i === a;
  }
  for(var intval of sel) {
    if(within(intval, idx)) return true;
  }
  return false;
}

function lookupKeySetEmptyRange(idx, map) {
  return lookupKeySetWith(idx, map, is_selected_empty);
}
function* lookupKeySetWith(idx, map, f) {
  for(var item of map) {
    var ks = item[0];
    if(f(ks, idx)) {
      yield item;
    }
  }
}

function to_client_tree(t) {
  return {
    'sentence': t.sentence,
    'direction': t.direction
  };
}

function select_menuitem(item, lang) {
  ct_setLinearization(DATA.menu[lang], item);
  var data = DATA;
  var menu = data.menu;
  var score = data.score;
  var menuRequest = {
    'key': data.key,
    'lesson': data.lesson,
    'score': {
      'clicks': score.clicks,
      'time': get_elapsed_time_as_seconds()
    },
    'src': to_client_tree(menu.src),
    'trg': to_client_tree(menu.trg)
  };
  muste_request(menuRequest, 'menu').then(handle_menu_response);
  $(document).trigger('overlay-out');
}

var high_scores_template = `
{{#each .}}
<tr>
 <td>{{lesson.name}}</td>
 <td>{{user.name}}</td>
 <td>{{score.clicks}}</td>
 <td>{{score.time}}</td>
</tr>
{{/each}}
`;

var render_high_scores = Handlebars.compile(high_scores_template);

// Used by a button on the html page.
window.fetch_high_scores = function() {
  muste_request({}, 'high-scores')
    .then(function (xs) {
      $(window).trigger('high-scores-loaded', {scores: xs});
    });
};

function register_high_score_handler($) {
  $(window).on('high-scores-loaded', function(_, e) {
    var scores = e.scores;
    set_global_highscore_mapping(scores);
    display_high_scores(scores);
    setup_score_bars(window.ScoreBar);
  });
}

function set_global_highscore_mapping(scores) {
  var xs = scores.map(function(score) {
    return [score.lesson.key, score.score];
  });
  var m = new Map(xs);
  window['high-scores'] = m;
}

function display_high_scores(scores) {
  var p = $('#high-scores-table');
  p.empty();
  var e = render_high_scores(scores);
  p.html(e);
}

//////////////////////////////////////////////////////////////////////
// Busy indicator

function register_busy_indicator($) {
  var $w = $(window);
  var $busy = $('#busy-indicator');
  var sem = 0;
  $w.on('api-load-start', function () {
    sem++;
    $busy.removeClass('idle');
    $('.overlay').show();
  });
  $w.on('api-load-end', function () {
    sem--;
    if(sem > 0) return;
    $busy.addClass('idle');
    $('.overlay').hide();
  });
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
    if(highscore === undefined) {
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
