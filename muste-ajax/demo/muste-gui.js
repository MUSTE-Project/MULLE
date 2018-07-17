
var AjaxTimeout = 1000; // milliseconds

var NOSPACING = "&+";
var PUNCTUATION = /^[\,\;\.\?\!\)]$/;
var PREFIXPUNCT = /^[¿¡\(]$/;

var DATA = null;
var LOGIN_TOKEN = null;
var TIMER_START = null;

var EXERCISES = [];
var SERVER = "/api/"

var MESSAGES =
  { LOGOUT: "logout"
  , LOGIN: "login"
  , LESSONS: "lessons"
  , LESSON: "lesson"
  , MENU: "menu"
  };

$(function() {
    $('#loginform').submit(submit_login);
    $('#abortlesson').click(retrieve_lessons);
    $('#logoutbutton').click(restart_everything);
    $('#body').click(click_body);
    window.setInterval(update_timer, 100);
    if (window.sessionStorage.getItem("LOGIN_TOKEN") == null)
    {
	show_page("loginpage");
	loginform.name.focus();
    }
    else
    {
	LOGIN_TOKEN = window.sessionStorage.getItem("LOGIN_TOKEN");
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
        clear_selection();
    }
}


function call_server(message, parameters) {
    if (typeof(SERVER) === "function") {
        handle_server_response(SERVER(message, parameters));
    }
    else if (typeof(SERVER) === "string") {
        $.ajax({
            cache: false,
            async: false,
            timeout: AjaxTimeout,
            url: SERVER + message + "/",
            dataType: "json",
	        method: "POST",
	        processData: false,
            data: JSON.stringify({message: message, parameters: parameters})
        }).fail(function(jqxhr, status, error) {
            alert_error(status, error);
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
              $('<a href="">').text(lsn.name).data({lesson: lsn.name}).click(select_lesson)
          ).appendTo(item);
	}
	else {
	    $('<td>').append(
		$('<a href="">').text(lsn.name).data({lesson: lsn.name})
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
    call_server(MESSAGES.LESSON, {token: LOGIN_TOKEN, lesson: lesson});
}


function show_exercise(parameters) {
    show_page("exercisepage");
    DATA = parameters;
    clean_server_data(DATA.a);
    clean_server_data(DATA.b);
    build_matching_classes(DATA);
    show_lin('a', DATA.a.lin);
    show_lin('b', DATA.b.lin);
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


function clean_server_data(data) {
    function convert_path(path) {
        return path.toString().replace(/[,\[\]]/g,"");
    }
    function clean_lin(lin) {
        lin.forEach(function(pword){
            pword.path = convert_path(pword.path)
        });
    }
    clean_lin(data.lin);
    var oldmenu = data.menu;
    data.menu = {};
    for (var path in oldmenu) {
        oldmenu[path].forEach(function(submenu){
            submenu.forEach(function(item){
                clean_lin(item.lin);
            });
        });
	data.menu[convert_path(path)] = oldmenu[path];
    }
}


function build_matching_classes(data) {
    var MAX_CLASSES = 4;

    data.matching_classes = {};
    var matching_class = 0;
    ["a", "b"].forEach(function(lang) {
        data[lang].lin.forEach(function(token) {
            if (token.matched && token.matched.length && !data.matching_classes[token.path]) {
                data.matching_classes[token.path] = "match-" + matching_class;
                matching_class = (matching_class + 1) % MAX_CLASSES;
            }
        });
    });
}


function show_lin(lang, lin) {
    clear_selection();
    var sentence = $('#' + lang).empty();
    // var tree = parse_tree(DATA[lang].tree);
    for (var i=0; i<lin.length; i++) {
        var previous = i > 0 ? lin[i-1].lin : null;
        var current = lin[i].lin;
        var spacing = (previous == NOSPACING || current == NOSPACING || PREFIXPUNCT.test(previous) || PUNCTUATION.test(current))
            ? ' ' : ' &nbsp; ';
        $('<span>')
            .addClass('space clickable').data({nr:i, lang:lang})
            .html(spacing).click(click_word)
            .appendTo(sentence);
        var path = lin[i].path;
        var match = lin[i].matched && lin[i].matched.length;
        // var subtree = lookup_subtree(path, tree);
        var wordspan = $('<span>')
            .addClass('word clickable').data({nr:i, lang:lang, path:path /* , subtree:subtree */ })
            .html(current + '<sub class="debug">' + (match ? "=" : "") + path /* + ' ' + show_tree(subtree) */ + '</sub>')
            .click(click_word)
            .appendTo(sentence);
        if (match) {
            wordspan.addClass('match').addClass(DATA.matching_classes[path]);
        }
    }
    $('<span>')
        .addClass('space clickable').data({nr:lin.length, lang:lang})
        .html(' &nbsp; ').click(click_word)
        .appendTo(sentence);
}



function clear_selection() {
    $('.striked').removeClass('striked');
    $('#menus').empty();
}


function click_word(event) {
    var clicked = $(event.target).closest('.clickable');
    var lang = clicked.data().lang;
    var path = clicked.data().path;

    if (clicked.hasClass('striked') && $('#menus ul').length > 1) {
        $('#menus ul').first().remove();
    }
    else {
        function next_selection(sel) {
            return sel ? sel.slice(0, sel.length-1) : null;
        }
        var selection =
            (clicked.hasClass('striked') ? next_selection($('#menus').data('selection'))
             : clicked.hasClass('word') ? path
             : /* clicked.hasClass('space')? */ path
            );
        clear_selection();
        var menus = DATA[lang].menu[selection];
        while (!(menus && menus.length)) {
            selection = next_selection(selection);
            if (selection == null) return;
            var menus = DATA[lang].menu[selection];
        }

        clicked.addClass('striked');
        $('#' + lang).find('.word')
            .filter(function(){
                return $(this).data().path.startsWith(selection);
            })
            .addClass('striked');
        // $('#' + lang).find('.space')
        //     .filter(function(){
        //         var nr = $(this).data().nr;
        //         return lin[nr] ? path.startsWith(selection) : false;
        //     })
        //     .addClass('striked');

        $('#menus').data('selection', selection);
        for (var i = 0; i < menus.length; i++) {
            var ul = $('<ul>').appendTo($('#menus')).hide();
            for (var j = 0; j < menus[i].length; j++) {
                var item = menus[i][j];
                var menuitem = $('<span class="clickable">')
                    .data({'tree': item.tree, 'lang': lang})
                    .click(BUSY(function(c){
                        select_menuitem($(c).data());
                    }));
                if (item.lin.length == 0) {
                    $('<span>').html("&empty;").appendTo(menuitem);
                } else {
                    item.lin.forEach(function(pword){
			var marked = pword.path.startsWith(selection);
                        $('<span>').text(pword.lin)
			    .addClass(marked ? 'marked' : 'greyed')
                            .appendTo(menuitem);
                        $('<span>').text(" ").appendTo(menuitem);
                    });
                }
                $('<li>').append(menuitem).appendTo(ul);
            }
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


function select_menuitem(item) {
    DATA[item.lang].tree = item.tree;
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
