
var AjaxTimeout = 1000; // milliseconds

var NOSPACING = "&+";
var PUNCTUATION = /^[\,\;\.\?\!\)]$/;
var PREFIXPUNCT = /^[¿¡\(]$/;

var DATA = null;
var LOGIN_TOKEN = null;
var TIMER_START = null;

$(function() {
    $('#loginform').submit(submit_login);
    $('#abortlesson').click(retrieve_lessons);
    $('#body').click(click_body);
    window.setInterval(update_timer, 100);
    LOGIN_TOKEN = null;
    show_page("loginpage");
    loginform.name.focus();
    // this should be removed...:
    loginform.name.value = "peter";
    loginform.pwd.value = "PETER";
});


function update_timer() {
    if (TIMER_START) {
        var elapsed = new Date().getTime() - TIMER_START;
        var secs = Math.floor(elapsed / 1000);
        $("#timer").text(secs + " s");
    }
}


function show_page(page) {
    $(".page").hide();
    $("#" + page).show();
}


function restart_everything() {
    location.reload();
}


function submit_login(evt) {
    if (evt && evt.preventDefault) {
        evt.preventDefault();
    }
    call_server("CMLoginRequest", {username: loginform.name.value, password: loginform.pwd.value});
}


// http://www.hunlock.com/blogs/Mastering_The_Back_Button_With_Javascript
// window.onbeforeunload = function () {
//    return "Are you sure you want to leave this now?";
// }

// window.location.hash = "no-back-button";
// window.onhashchange = function(){window.location.hash="no-back-button";}

// window.onpopstate = function (event) {
//     if (event.state) {
//         CurrentPage = event.state.page;
//         var trees = event.state.trees;
//         for (var lang in trees) {
//             set_and_show_tree(lang, trees[lang]);
//         }
//     }
// };


function click_body(event) {
    var prevented = $(event.target).closest('.prevent-body-click').length > 0;
    if (!prevented) {
        clear_selection();
    }
}


function call_server(message, parameters) {
    console.log("Calling server", message, parameters);
    if (typeof(SERVER) === "function") {
        handle_server_response(SERVER(message, parameters));
    }
    else if (typeof(SERVER) === "string") {
        $.ajax({
            cache: false,
            async: false,
            timeout: AjaxTimeout,
            url: SERVER, 
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
    call_server("CMLessonsRequest", {token: LOGIN_TOKEN});
}


function show_lessons(lessons) {
    show_page("lessonspage");
    TIMER_START = null;
    var table = $("#lessonslist");
    table.empty();
    lessons.forEach(function(lsn) {
        var item = $('<tr>');
        $('<td>').append(
            $('<a href="">').text(lsn.name).data({lesson: lsn.name}).click(select_lesson)
        ).appendTo(item);
        $('<td>').append(
            $('<span>').text(lsn.passed + " avklarade av " + lsn.total + " övningar, " + lsn.score + " poäng")
        ).appendTo(item);
        if (lsn.passed >= lsn.total) {
            item.addClass("greyed");
        }
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
    call_server("CMLessonInit", {token: LOGIN_TOKEN, lesson: lesson});
}


function show_exercise(parameters) {
    show_page("exercisepage");
    DATA = parameters;
    /* DATA.a = */ clean_server_data(DATA.a);
    /* DATA.b = */ clean_server_data(DATA.b);
    console.log('DATA', DATA);
    show_lin('a', DATA.a.lin);
    show_lin('b', DATA.b.lin);
    $('#score').text(DATA.score);
    $('#lessoncounter').text(DATA.lesson + ": övning " + DATA.exercise + " av " + DATA.total);
    if (parameters.passed) {
        var elapsed_time = Math.floor((new Date().getTime() - TIMER_START) / 1000);
        setTimeout(function(){
            alert("BRAVO!" +
                  "     Poäng: " + DATA.score +
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
    console.log("Response from server", message, parameters);

    switch (message) {
    case "SMLoginSuccessful":
        LOGIN_TOKEN = parameters.token;
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
    function clean_path(path) {
        return path.toString().replace(/[,\[\]]/g,"");
    }
    function clean_lin(lin) {
        lin.forEach(function(pword){
            pword.path = clean_path(pword.path)
        });
        // return lin.map(function(pword){
        //     return {word: pword.word, path: clean_path(pword.path)};
        // });
    }
    clean_lin(data.lin);
    // var result = {grammar: data.grammar,
    //               tree: data.tree,
    //               lin: clean_lin(data.lin),
    //               menu: {}};
    for (var path in data.menu) {
        data.menu[path].forEach(function(submenu){
            submenu.forEach(function(item){
                clean_lin(item.lin);
            });
        });
        // result.menu[clean_path(path)] = data.menu[path].map(function(submenu){
        //     return submenu.map(function(item){
        //         return {cost: item.cost, tree: item.tree, lin: clean_lin(item.lin)};
        //     });
        // });
    }
    // return result;
}


function show_lin(lang, lin) {
    clear_selection();
    var sentence = $('#' + lang).empty();
    // var tree = parse_tree(DATA[lang].tree);
    for (var i=0; i<lin.length; i++) {
        var previous = i > 0 ? lin[i-1].word : null;
        var current = lin[i].word;
        var spacing = (previous == NOSPACING || current == NOSPACING || PREFIXPUNCT.test(previous) || PUNCTUATION.test(current))
            ? ' ' : ' &nbsp; ';
        $('<span>')
            .addClass('space clickable').data({nr:i, lang:lang})
            .html(spacing).click(click_word)
            .appendTo(sentence);
        var path = lin[i].path;
        // var subtree = lookup_subtree(path, tree);
        $('<span>')
            .addClass('word clickable').data({nr:i, lang:lang, path:path /* , subtree:subtree */ })
            .html(current + '<sub class="debug">' + path /* + ' ' + show_tree(subtree) */ + '</sub>')
            .click(click_word)
            .appendTo(sentence);
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
    console.log("Clicked " + lang + ": " + path);

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
        console.log("MENU["+selection+"]", menus);
        while (!(menus && menus.length)) {
            selection = next_selection(selection);
            if (selection == null) return;
            var menus = DATA[lang].menu[selection];
            console.log("MENU["+selection+"]", menus);
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
                        $('<span>').text(pword.word)
                            .addClass(pword.path.startsWith(selection) ? 'marked' : 'greyed')
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
    call_server("CMMenuRequest", DATA);
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
        console.log("POP ERROR", ind.className, ind.textContent);
    }
}


//////////////////////////////////////////////////////////////////////
// Error handling

function alert_error(title, description) {
    alert("*** " + title + "***\n" + description);
}


//////////////////////////////////////////////////////////////////////
// Trees are of the form [node, [node, ...], ..., [node, ...]]

// function lookup_subtree(path, tree) {
//     for (var i=0; i<path.length; i++) {
//         tree = tree[1 + parseInt(path[i])];
//     }
//     return tree;
// }


// function show_tree(tree) {
//     var s = tree[0];
//     for (var i=1; i<tree.length; i++) {
//         s += " " + show_tree(tree[i]);
//     }
//     return "(" + s + ")";
// }

// function parse_tree(descr) {
//     var tokens = descr
//         .replace(/\( */g," (")
//         .replace(/\)/g," ) ")
//         .replace(/^ +| +$/g,"")
//         .split(/ +/);
//     if (tokens[0][0] !== "(") {
//         tokens[0] = "(" + tokens[0];
//         tokens.push(")");
//     }
//     var stack = [[]];
//     for (var i=0; i<tokens.length; i++) {
//         var token = tokens[i];
//         if (token[0] == "(") {
//             if (stack.length == 1 && stack[0].length > 0) {
//                 console.log("PARSE ERROR: Expected end-of-string, found '(': " + descr);
//                 return;
//             } else if (token.length <= 1) {
//                 console.log("PARSE ERROR: Expected node, found end-of-string: " + descr);
//                 return;
//             } else {
//                 var node = token.slice(1);
//                 stack.push([node]);
//             }
//         } else if (token == ")") {
//             if (stack.length == 1) {
//                 var err = (stack[0].length == 0)
//                     ? "No matching open bracket" : "Expected end-of-string";
//                 console.log("PARSE ERROR: " + err + ", found ')': " + descr);
//                 return;
//             } else {
//                 var tree = stack.pop();
//                 stack[stack.length-1].push(tree);
//             }
//         } else if (/^\w+$/.test(token)) {
//             stack[stack.length-1].push([token]);
//         } else {
//             console.log("PARSE ERROR: Unknown token " + token + ": " + descr);
//             return;
//         }
//     }
//     if (stack.length > 1) {
//         console.log("PARSE ERROR: Expected close bracket, found end-of-string: " + descr);
//         return;
//     } else if (stack[0].length == 0) {
//         console.log("PARSE ERROR: Expected open bracket, found end-of-string: " + descr);
//         return;
//     } else {
//         return stack[0][0];
//     }
// }
