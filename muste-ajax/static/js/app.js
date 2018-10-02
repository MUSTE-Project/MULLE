/*global $ Handlebars jQuery Set Map countdown : true*/
var NOSPACING = '&+';
var PUNCTUATION = /^[,;.?!)]$/;
var PREFIXPUNCT = /^[¿¡(]$/;

var DATA = null;
var LOGIN_TOKEN = null;
var TIMER_START = null;

var EXERCISES = [];
var VIRTUAL_ROOT = '/';
var SERVER = VIRTUAL_ROOT + 'api/';

var MESSAGES = {
  LOGOUT: 'logout',
  // Must set authentication header
  LOGIN: 'login',
  LESSONS: 'lessons',
  // Muste request the *name* of the lesson.  E.g:
  //
  //    /lesson/Prima+Pars
  //
  // TODO Would be more convenient if it was an id.
  LESSON: 'lesson',
  MENU: 'menu',
};

jQuery().ready(init);

function init() {
  register_handlebars_helper();
  $('#loginform').submit(submit_login);
  $('#abortlesson').click(retrieve_lessons);
  $('#logoutbutton').click(restart_everything);
  register_timer();
  register_overlay();
  register_pagers();
  register_create_user_handler();
  register_change_pwd_handler();
  register_popup_menu(jQuery);
  var tok = window.sessionStorage.getItem('LOGIN_TOKEN');
  // Show login page regardless.
  show_page('#page-login');
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
  $('.pager').click(function() {
    var pg = $(this).attr('href');
    show_page(pg);
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
      console.aler('That did not work, perhaps you didn\'t enter the correct value for your old password');
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
    muste_request_raw(data, 'change-pwd').then(function() {
      show_page('#page-login');
    }).fail(function() {
      console.error('no way');
    });
  });
}

function register_timer() {
  // FIXME This keeps churning even if we are not using the timer.
  window.setInterval(update_timer, 500);
}

// Returns a formatted string of the elapsed time. Note that currently
// this is not locale sensitive.
function elapsed_time() {
  return countdown(new Date, TIMER_START);
}

function update_timer() {
  if (TIMER_START) {
    $('#timer').text(elapsed_time().toString());
  }
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

function show_page(page) {
  $('.page').hide();
  $(page).show();
}


function restart_everything() {
  call_server(MESSAGES.LOGOUT, {token: LOGIN_TOKEN});
  location.reload();
}


function submit_login(evt) {
  if (evt && evt.preventDefault) {
    evt.preventDefault();
  }
  var loginform = document.getElementById('loginform');
  call_server(MESSAGES.LOGIN, {username: loginform.name.value, password: loginform.pwd.value});
}


function call_server(message, parameters) {
  call_server_new(message, parameters, message + '/');
}

function call_server_new(message, parameters, endpoint) {
  if (typeof(SERVER) === 'function') {
    handle_server_response(SERVER(message, parameters));
  }
  else if (typeof(SERVER) === 'string') {
    var data = {message: message, parameters: parameters};
    muste_request(data, endpoint).done(handle_server_response);
  }
}

// Returns a promise with the request.  Reports errors according to
// the protocol.  In contrast with `call_server_new` does not try to
// guess how to interpret the response.
function muste_request(data, endpoint) {
  return muste_request_raw(data, endpoint).fail(handle_server_fail);
}

// Like `emuste_request` but with no error handler.
function muste_request_raw(data, endpoint) {
  var req = {
    cache: false,
    url: SERVER + endpoint,
    dataType: 'json',
    method: 'POST',
    processData: false,
    data: JSON.stringify(data)
  };
  return $.ajax(req);
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
}

function muste_logout() {
  show_page('#page-login');
  window.sessionStorage.removeItem('LOGIN_TOKEN');
}

function display_error(resp) {
  if(resp.responseJSON === undefined) {
    // We've received a response object that we didn't expect.
    console.error(resp.responseText);
    return;
  }
  console.error(resp.responseJSON);
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
    }
  });
}

function retrieve_lessons(evt) {
  if (evt && evt.preventDefault) {
    evt.preventDefault();
  }
  call_server(MESSAGES.LESSONS, {token: LOGIN_TOKEN});
}

var lesson_list_template = ' \
<div class="lessons"> \
{{#each .}} \
 <div class="{{#if (or passed (gte passed total))}}finished{{/if}} {{#if enabled}}{{else}}disabled{{/if}}"> \
  <h2>{{name}}</h2> \
  <div class="lesson-info"> \
   <div> \
    <span> \
     {{passedcount}} avklarade av {{exercisecount}} övningar, {{lsn.score}}  klick i {{lsn.time}} sekunder \
    </span> \
    <div> \
     {{description}} \
    </div> \
   </div> \
   <div class="lesson-info-button"> \
    <button {{#if enabled}}{{else}}disabled{{/if}} onclick="start_lesson(\'{{name}}\');">Solve</button> \
   </div> \
  </div> \
 </div> \
{{/each}} \
</div> \
';

var render_lesson_list = Handlebars.compile(lesson_list_template);

function show_lessons(lessons) {
  show_page('#page-lessons');
  TIMER_START = null;
  var table = $('#lessonslist');
  table.empty();
  var e = render_lesson_list(lessons);
  table.html(e);
  lessons.forEach(function(lsn) {
    EXERCISES[lsn.name] = {passed : lsn.passedcount, total : lsn.exercisecount};
  });
}

// Warning defined but never used.  What gives?
function select_lesson(evt) { // eslint-disable-line no-unused-vars
  if (evt && evt.preventDefault) {
    evt.preventDefault();
  }
  start_lesson($(this).data('lesson'));
}


function start_lesson(lesson) {
  TIMER_START = new Date().getTime();
  call_server_new(MESSAGES.LESSON, {token: LOGIN_TOKEN, lesson: lesson}, MESSAGES.LESSON + '/' + lesson);
}

function show_exercise(parameters) {
  show_page('#page-exercise');
  DATA = parameters;
  clean_server_data(DATA.a);
  clean_server_data(DATA.b);
  build_matching_classes(DATA);
  show_sentences(DATA.a, DATA.b);
  $('#score').text(DATA.score);
  $('#lessoncounter').text(DATA.lesson + ': övning ' + EXERCISES[DATA.lesson].passed + ' av ' + EXERCISES[DATA.lesson].total);
  if (parameters.success) {
    var t = elapsed_time().toString();
    setTimeout(function(){
      alert('BRAVO!' +
        '    Klick: ' + DATA.score +
        '    Tid: ' + t + ' sekunder');
      if (DATA.exercise < DATA.total) {
        start_lesson(DATA.lesson);
      } else {
        retrieve_lessons();
      }
    }, 500);
  }
}

// ct_linearization :: ClientTree -> Sentence.Linearization
function ct_linearization(t) {
  return t.sentence.linearization;
}
function ct_setLinearization(t, l) {
  t.sentence.linearization = l;
}

function handle_server_response(response) {
  var message = response.message;
  var parameters = response.parameters;

  switch (message) {
  case 'SMLogoutResponse':
    muste_logout();
    break;

  case 'SMLoginSuccess':
    LOGIN_TOKEN = parameters.token;
    window.sessionStorage.setItem('LOGIN_TOKEN',LOGIN_TOKEN);
    retrieve_lessons();
    break;

  case 'SMLessonsList':
    show_lessons(parameters.lessons);
    break;

  case 'SMMenuList':
    show_exercise(parameters);
    break;

  default:
    var title = friendly_title(message);
    var description = (parameters && parameters.error ? parameters.error : '');
    alert_error(title, description);
    break;
  }
}

function friendly_title(m) {
  switch (m) {
  case 'SMLoginFail'      : return 'Login failure, please try again';
  case 'SMSessionInvalid' : return 'Session invalid, please login again';
  case 'SMLessonInvalid'  : return 'Lesson invalid, please login again';
  case 'SMDataInvalid'    : return 'Invalid data, please login again';
  default                 : return 'Uknown message from server: ' + m;
  }
}

function clean_server_data(data) {
  data.menu = new Map(data.menu);
}


function build_matching_classes(data) {
  var MAX_CLASSES = 4;

  data.matching_classes = {};
  var matching_class = 0;
  ['a', 'b'].forEach(function(lang) {
    ct_linearization(data[lang]).forEach(function(token) {
      if (token.matched && token.matched.length && !data.matching_classes[token.path]) {
        data.matching_classes[token.path] = 'match-' + matching_class;
        matching_class = (matching_class + 1) % MAX_CLASSES;
      }
    });
  });
}

function show_sentences(src, trg) {
  var srcL = ct_linearization(src);
  var trgL = ct_linearization(trg);
  matchy_magic(srcL, trgL);
  matchy_magic(trgL, srcL);
  show_lin('a', srcL);
  show_lin('b', trgL);
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

function show_lin(lang, lin) {
  var sentence = $('#' + lang).empty();
  // var tree = parse_tree(DATA[lang].tree);
  for (var i=0; i<lin.length; i++) {
    var linTok = lin[i];
    var previous = i > 0 ? lin[i-1].concrete : null;
    var current = linTok.concrete;
    var menu = DATA[lang].menu;
    var spacing = (previous == NOSPACING || current == NOSPACING || PREFIXPUNCT.test(previous) || PUNCTUATION.test(current))
      ? ' ' : ' &emsp; ';
    var spacyData = {
      nr: i,
      lang: lang,
      'valid-menus': getValidMenusEmpty(i, menu)
    };
    $('<span>')
      .addClass('space clickable').data(spacyData)
      .html(spacing).click(click_word)
      .appendTo(sentence);
    var classes = linTok['classes'];
    var matchingClasses = linTok['matching-classes'];
    var match = matchingClasses.size > 0;
    var validMenus = getValidMenus(i, menu);
    var wordData = {
      nr: i,
      lang: lang,
      'classes': classes,
      /* , subtree:subtree */
      'valid-menus': validMenus
    };
    var wordspan = $('<span>')
      .addClass('word clickable').data(wordData)
      .html(current + '<sub class="debug">' + (match ? '=' : '') + JSON.stringify(classes) /* + ' ' + show_tree(subtree) */ + '</sub>')
      .click(click_word)
      .appendTo(sentence);
    if (match) {
      wordspan.addClass('match');
      var h = hash_array_of_string(Array.from(matchingClasses));
      var c = int_to_rgba(h);
      wordspan.css({'border-color': c});
    }
  }
  $('<span>')
    .addClass('space clickable').data({nr:lin.length, lang:lang})
    .html('&emsp;').click(click_word)
    .appendTo(sentence);
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
      // TODO Unimplemented.
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
  function mark_selected_words(lin, sel) {
    for(var i = 0 ; i < lin.length ; i++) {
      var pword = lin[i].concrete;
      // var marked = prefixOf(selection, pword.path);
      var marked = is_selected(sel, i);
      $('<span>').text(pword)
        .addClass(marked ? 'marked' : 'greyed')
        .appendTo(menuitem);
      $('<span>').text(' ').appendTo(menuitem);
    }
  }
  if(validMenus === 'nothing') {
    // Fake an empty menu.
    validMenus = {next: function() {return [[], []];}, reset: function (){}};
  }
  if(validMenus === undefined) {
    throw 'No menu found. Probably because the user clicked a space between words, this is still not supported.';
  }

  if (clicked.hasClass('striked') && $('#menus ul').length > 1) {
    $('#menus ul').first().remove();
  }
  else {
    var selection = getSelection();
    update_menu(validMenus, idx);

    // These are the valid menus.  Now we must toggle between them
    // somehow.
    var selsnmen = validMenus.next();
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

    $('#menus').data('selection', selection);
    var ul = $('<ul>').appendTo($('#menus'));
    for (var i = 0; i < menus.length; i++) {
      var pr = menus[i];
      var item = pr[1]; // snd
      var menuitem = $('<span class="clickable">')
        .data('item', item)
        .data('lang', lang)
        .click(BUSY(function(c){
          var $c = $(c);
          var item = $c.data('item');
          var lang = $c.data('lang');
          select_menuitem(item, lang);
        }));
      var lin = item;
      if (lin.length == 0) {
        $('<span>').html('&empty;').appendTo(menuitem);
      } else {
        mark_selected_words(lin, pr[0]);
      }
      $('<li>').append(menuitem).appendTo(ul);

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

// is_selected :: Menu.Seleection -> Int -> Bool
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

function getValidMenusEmpty(idx, menu) {
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
      i = (i+1) % a.length;
      return a[i];
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

function select_menuitem(item, lang) {
  ct_setLinearization(DATA[lang], item);
  DATA.token = LOGIN_TOKEN;
  DATA.time = elapsed_time().seconds;
  call_server(MESSAGES.MENU, DATA);
  $(document).trigger('overlay-out');
}


//////////////////////////////////////////////////////////////////////
// Busy indicator

var BUSY_DELAY = 50;
var BUSY_STR = '\u25CF';
// Unicode Character 'BLACK CIRCLE' (U+25CF)

function BUSY(f) {
  return function(){
    var obj = this; // $(this);
    push_busy();
    setTimeout(function(){
      f(obj);
      pop_busy();
    }, BUSY_DELAY);
  };
}

function push_busy() {
  var ind = document.getElementById('busy-indicator');
  ind.className = ind.className + BUSY_STR;
  ind.textContent += BUSY_STR;
}

function pop_busy() {
  var ind = document.getElementById('busy-indicator');
  if (ind.className.slice(-BUSY_STR.length) === BUSY_STR) {
    ind.className = ind.className.slice(0, -BUSY_STR.length);
    ind.textContent = ind.textContent.slice(0, -BUSY_STR.length);
  } else {
    console.error('POP ERROR', ind.className, ind.textContent);
  }
}


//////////////////////////////////////////////////////////////////////
// Error handling

function alert_error(title, description) {
  console.trace('*** ' + title + '***\n' + description);
}
