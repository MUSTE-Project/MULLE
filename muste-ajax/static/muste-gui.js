var AjaxTimeout = 1000; // milliseconds

var NOSPACING = "&+";
var PUNCTUATION = /^[\,\;\.\?\!\)]$/;
var PREFIXPUNCT = /^[¿¡\(]$/;

var DATA = null;
var LOGIN_TOKEN = null;
var TIMER_START = null;

var EXERCISES = [];
var VIRTUAL_ROOT = "/";
var SERVER = VIRTUAL_ROOT + "api/";

var MESSAGES =
  { LOGOUT: "logout"
  // Must set authentication header
  , LOGIN: "login"
  , LESSONS: "lessons"
  // Muste request the *name* of the lesson.  E.g:
  //
  //    /lesson/Prima+Pars
  //
  // TODO Would be more convenient if it was an id.
  , LESSON: "lesson"
  , MENU: "menu"
  };

$(function() {
    $('#loginform').submit(submit_login);
    $('#abortlesson').click(retrieve_lessons);
    $('#logoutbutton').click(restart_everything);
    $('#body').click(click_body);
    window.setInterval(update_timer, 100);
    var tok = window.sessionStorage.getItem("LOGIN_TOKEN");
    // Show login page regardless.
    show_page("loginpage");
    if (tok == null) {
	loginform.name.focus();
    } else {
	LOGIN_TOKEN = tok;
	retrieve_lessons();
    }
});

function elapsed_time() {
    var elapsed = new Date().getTime() - TIMER_START;
    var secs = Math.floor(elapsed / 1000);
    return secs;
}
function update_timer() {
    if (TIMER_START) {
	var secs = elapsed_time();
        $("#timer").text(secs + " s");
    }
}


function show_page(page) {
    $(".page").hide();
    $("#" + page).show();
}


function restart_everything() {
    call_server(MESSAGES.LOGOUT, {token: LOGIN_TOKEN});
    location.reload();
}


function submit_login(evt) {
    if (evt && evt.preventDefault) {
        evt.preventDefault();
    }
    call_server(MESSAGES.LOGIN, {username: loginform.name.value, password: loginform.pwd.value});
}


function click_body(event) {
    var prevented = $(event.target).closest('.prevent-body-click').length > 0;
    if (!prevented) {
        reset_selection();
    }
}

function call_server(message, parameters) {
  call_server_new(message, parameters, message + "/");
}

function call_server_new(message, parameters, endpoint) {
    if (typeof(SERVER) === "function") {
        handle_server_response(SERVER(message, parameters));
    }
    else if (typeof(SERVER) === "string") {
        $.ajax({
            cache: false,
            async: false,
            timeout: AjaxTimeout,
            url: SERVER + endpoint,
            dataType: "json",
	        method: "POST",
	        processData: false,
            data: JSON.stringify({message: message, parameters: parameters})
        }).fail(function(resp, status, error) {
            console.error(resp.responseText);
        }).done(handle_server_response);
    }
}


function retrieve_lessons(evt) {
    if (evt && evt.preventDefault) {
        evt.preventDefault();
    }
    call_server(MESSAGES.LESSONS, {token: LOGIN_TOKEN});
}

function show_lessons(lessons) {
    show_page("lessonspage");
    TIMER_START = null;
    var table = $("#lessonslist");
    table.empty();
    lessons.forEach(function(lsn) {
	EXERCISES[lsn.name] = {passed : lsn.passedcount, total : lsn.exercisecount} ;
        var item = $('<tr>');
	if (lsn.enabled) {
          $('<td>').append(
              $('<button>').text(lsn.name).data({lesson: lsn.name}).click(select_lesson)
          ).appendTo(item);
	}
	else {
	    $('<td>').append(
		$('<button>').text(lsn.name).data({lesson: lsn.name})
	    ).appendTo(item);
	}
        $('<td>').append(
            $('<span>').text(lsn.passedcount + " avklarade av " + lsn.exercisecount + " övningar, " + lsn.score + " klick i " + lsn.time + " sekunder")
        ).appendTo(item);
        if (lsn.passed || lsn.passed >= lsn.total) {
            item.addClass("finished");
        }
	if (!lsn.enabled) {
	    item.addClass("disabled");
	}
        item.appendTo(table);
	var item = $('<tr>');
	$('<td>').text(lsn.description).appendTo(item);
	item.appendTo(table);
    });
}


function select_lesson(evt) {
    if (evt && evt.preventDefault) {
        evt.preventDefault();
    }
    start_lesson($(this).data().lesson);
}


function start_lesson(lesson) {
    TIMER_START = new Date().getTime();
    call_server_new(MESSAGES.LESSON, {token: LOGIN_TOKEN, lesson: lesson}, MESSAGES.LESSON + "/" + lesson);
}

function show_exercise(parameters) {
    show_page("exercisepage");
    DATA = parameters;
    clean_server_data(DATA.a);
    clean_server_data(DATA.b);
    build_matching_classes(DATA);
    show_sentences(DATA.a, DATA.b);
    $('#score').text(DATA.score);
    $('#lessoncounter').text(DATA.lesson + ": övning " + EXERCISES[DATA.lesson].passed + " av " + EXERCISES[DATA.lesson].total);
    if (parameters.success) {
        var elapsed_time = Math.floor((new Date().getTime() - TIMER_START) / 1000);
        setTimeout(function(){
            alert("BRAVO!" +
                  "     Klick: " + DATA.score +
                  "     Tid: " + elapsed_time + " sekunder");
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
    case "SMLogoutResponse":
	window.sessionStorage.removeItem("LOGIN_TOKEN");
        location.reload();
        break;

    case "SMLoginSuccess":
        LOGIN_TOKEN = parameters.token;
	window.sessionStorage.setItem("LOGIN_TOKEN",LOGIN_TOKEN);
        retrieve_lessons();
        break;

    case "SMLessonsList":
        show_lessons(parameters.lessons);
        break;

    case "SMMenuList":
        show_exercise(parameters);
        break;

    default:
        var title = (message == "SMLoginFail"      ? "Login failure, please try again"     :
                     message == "SMSessionInvalid" ? "Session invalid, please login again" :
                     message == "SMLessonInvalid"  ? "Lesson invalid, please login again"  :
                     message == "SMDataInvalid"    ? "Invalid data, please login again"    :
                     "Uknown message from server: " + message);
        var description = (parameters && parameters.error ? parameters.error : "");
        alert_error(title, description);
        // restart_everything();
        break;
    }
}

// This method changes the representation of `[Path]`'s to `String`.
// The side effect of `clean_server_data(data)` occurs at
// `data.trees[0][0][*].path` and `data.menu`
function clean_server_data(data) {
    function convert_path(path) {
        return path.toString().replace(/[,\[\]]/g,"");
    }
    function clean_lin(lin) {
        lin.forEach(function(pword){
            pword.path = convert_path(pword.path)
        });
    }
    // clean_lin(data.lin);
    data.menu = new Map(data.menu);
}


function build_matching_classes(data) {
    var MAX_CLASSES = 4;

    data.matching_classes = {};
    var matching_class = 0;
    ["a", "b"].forEach(function(lang) {
        ct_linearization(data[lang]).forEach(function(token) {
            if (token.matched && token.matched.length && !data.matching_classes[token.path]) {
                data.matching_classes[token.path] = "match-" + matching_class;
                matching_class = (matching_class + 1) % MAX_CLASSES;
            }
        });
    });
}

function show_sentences(src, trg) {
    var srcL = ct_linearization(src)
    var trgL = ct_linearization(trg)
    var srcM = matchy_magic(srcL, trgL);
    var trgM = matchy_magic(trgL, srcL);
    show_lin('a', srcL);
    show_lin('b', trgL);
}

function all_classes(xs) {
    var xss = xs.map(function(x) { return x["classes"];});
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
        chr   = s.charCodeAt(i);
        hash  = ((hash << 5) - hash) + chr;
        hash |= 0; // Convert to 32bit integer
    }
    return hash;
}

function matchy_magic(src, trg) {
    var cs = all_classes(src);
    trg.forEach(function(x) {
        var s = intersection(cs, new Set(x["classes"]));
        x["matching-classes"] = s;
    });
}

// intersection :: Set a -> Set a -> Set a
function intersection(m, n) {
    return new Set([...m].filter(function(x) {return n.has(x)}));
}

function show_lin(lang, lin) {
    reset_selection();
    var sentence = $('#' + lang).empty();
    // var tree = parse_tree(DATA[lang].tree);
    for (var i=0; i<lin.length; i++) {
        var linTok = lin[i];
        var previous = i > 0 ? lin[i-1].concrete : null;
        var current = linTok.concrete;
        var menu = DATA[lang].menu
        var spacing = (previous == NOSPACING || current == NOSPACING || PREFIXPUNCT.test(previous) || PUNCTUATION.test(current))
            ? ' ' : ' &nbsp; ';
        var spacyData = {
            nr: i,
            lang: lang,
            "valid-menus": getValidMenusEmpty(i, menu)
        };
        $('<span>')
            .addClass('space clickable').data(spacyData)
            .html(spacing).click(click_word)
            .appendTo(sentence);
        var classes = linTok["classes"];
        var matchingClasses = linTok["matching-classes"];
        var match = matchingClasses.size > 0;
        var validMenus = getValidMenus(i, menu);
        var wordData = {
            nr: i,
            lang: lang,
            "classes": classes,
            /* , subtree:subtree */
            "valid-menus": validMenus
        }
        var wordspan = $('<span>')
            .addClass('word clickable').data(wordData)
            .html(current + '<sub class="debug">' + (match ? "=" : "") + JSON.stringify(classes) /* + ' ' + show_tree(subtree) */ + '</sub>')
            .click(click_word)
            .appendTo(sentence);
        if (match) {
            wordspan.addClass('match');
            var h = hash_array_of_string(Array.from(matchingClasses));
            var c = int_to_rgba(h);
            wordspan.css({"border-color": c})
        }
    }
    $('<span>')
        .addClass('space clickable').data({nr:lin.length, lang:lang})
        .html(' &nbsp; ').click(click_word)
        .appendTo(sentence);
}

function int_to_rgba(num) {
    num >>>= 0;
    var b = num & 0xFF,
        g = (num & 0xFF00) >>> 8,
        r = (num & 0xFF0000) >>> 16,
        // a = ( (num & 0xFF000000) >>> 24 ) / 255 ;
        a = 1;
    return "rgba(" + [r, g, b, a].join(",") + ")";
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
    var clicked = $(event.target).closest('.clickable');
    var lang = clicked.data().lang;
    var path = clicked.data().path;
    var validMenus = clicked.data("valid-menus");
    var idx = clicked.data("nr");
    function mark_selected_words(lin, sel) {
        for(var i = 0 ; i < lin.length ; i++) {
            var pword = lin[i].concrete;
            // var marked = prefixOf(selection, pword.path);
            var marked = is_selected(sel, i);
            $('<span>').text(pword)
                .addClass(marked ? 'marked' : 'greyed')
                .appendTo(menuitem);
            $('<span>').text(" ").appendTo(menuitem);
        }
    }
    if(validMenus === "nothing") {
        throw "No menu for item";
    }
    if(validMenus === undefined) {
        throw "No menu found. Probably because the user clicked a space between words, this is still not supported.";
    }

    if (clicked.hasClass('striked') && $('#menus ul').length > 1) {
        $('#menus ul').first().remove();
    }
    else {
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
        var selection = getSelection();
        update_menu(validMenus, idx);

        // These are the valid menus.  Now we must toggle between them
        // somehow.
        var selsnmen = validMenus.next();
        // Again we changed the selection, we can try mapping the snd
        // component.
        selection    = selsnmen[0];
        var menus    = selsnmen[1];
        if (menus === null) throw "No menu found";

        clicked.addClass('striked');
        $('#' + lang).find('.word')
            .filter(function(){
                var idx = $(this).data("nr");
                return is_selected(selection, idx);
            })
            .addClass('striked');

        $('#menus').data('selection', selection);
        var ul = $('<ul>').appendTo($('#menus')).hide();
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
                $('<span>').html("&empty;").appendTo(menuitem);
            } else {
                mark_selected_words(lin, pr[0])
            }
            $('<li>').append(menuitem).appendTo(ul);

        }
    }

    var shown_menu = $('#menus ul').first();
    var top = clicked.offset().top + clicked.height() * 3/4;
    var left = clicked.offset().top + (clicked.width() - shown_menu.width()) / 2;
    var striked = $('.striked');
    if (striked.length) {
        left = (striked.offset().left + striked.last().offset().left +
                striked.last().width() - shown_menu.width()) / 2;
    }
    shown_menu.css({
        'top': top + 'px',
        'left': left + 'px',
        'max-height': (window.innerHeight - top - 6) + 'px'
    }).show();
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
    if(a.length === 0) return "nothing";
    return {
        next: function() {
            i = (i+1) % a.length;
            return a[i];
        },
        reset: function() {
            i = initial;
        }
    }
}

function prefixOf(xs, ys) {
    for(var i = 0 ; i < xs.length ; i ++) {
        var x = xs[i];
        var y = xs[i];
        if(x != y) return false;
    }
    return true;
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
    DATA.time = elapsed_time();
    call_server(MESSAGES.MENU, DATA);
}


//////////////////////////////////////////////////////////////////////
// Busy indicator

var BUSY_DELAY = 50;
var BUSY_STR = "\u25CF";
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
        console.error("POP ERROR", ind.className, ind.textContent);
    }
}


//////////////////////////////////////////////////////////////////////
// Error handling

function alert_error(title, description) {
    console.trace("*** " + title + "***\n" + description);
}
