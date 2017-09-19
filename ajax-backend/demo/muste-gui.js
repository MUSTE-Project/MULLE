
// var DATA = {
//     score: 0,
//     A: {grammar: null,
//         lin: null,
//         tree: null,
//         menu: null},
//     B: {grammar: null,
//         lin: null,
//         tree: null,
//         menu: null}
// };


var AjaxTimeout = 1000; // milliseconds

var NOSPACING = "&+";
var PUNCTUATION = /^[\,\;\.\?\!\)]$/;
var PREFIXPUNCT = /^[¿¡\(]$/;


$(BUSY(function() {
    $('#body').click(click_body);
    restart_game();
}));


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


function confirm_restart_game() {
    var sure = true; // confirm("Are you sure you want to restart the game?");
    if (sure) {
        restart_game();
    }
}


function restart_game() {
    call_server({
        score: 0,
        a: {grammar: DefaultLang1,
            tree: DefaultTree1,
           },
        b: {grammar: DefaultLang2,
            tree: DefaultTree2,
           }});
}

/* The 'input' from the client to the server should be of this form:

    { score: 34,
      A: {grammar: "MusteEng", tree: "(StartUtt (UttS (UseCl ... (PredVP (...)) ...)))"},
      B: {grammar: "MusteLat", tree: "(StartUtt (UttS (UseCl ... (PredVP (...)) ...)))"} }

Note: the first time the game is started, the input should be 'null'
*/

    function call_server(input) {
	console.log("Calling server with " + input);
    if (typeof(SERVER) === "function") {
        handle_server_result(SERVER(input));
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
            data: JSON.stringify(input)
        }).fail(function(jqxhr, status, error) {
            alert_error(status, error);
        }).done(handle_server_result);
    }
}


/* The return data from the server should be like this:

    { success: false,
      score: 35,
      A: { grammar: "MusteEng", tree: "(StartUtt (UttS (UseCl ... (PredVP (...)) ...)))",
           lin: ["she", "doesn't", "break", "the", "yellow", "stones", "."],
           menu: {"5,6" : [ [ {"cost":2,"lin":"apples","tree":"(StartUtt ...)"},
                              ...],
                            [ {"cost":2,"lin":"x y z","tree":"(StartUtt ...)"},
                              ...]
                          ],
                  "4,4" : [ ... ],
                  ...}
          },
      B: {...same as for A...}
    }

Note: the 'grammar' and the 'tree' should be exactly the same as the ones that the client sent to the server!
*/

function handle_server_result(data) {
    console.log("data", data);
    console.log("score", data.score);
    set_score(data.score);
    set_data('A', data.a);
    set_data('B', data.b);
    show_lin('A', data.a.lin);
    show_lin('B', data.b.lin);
    // mark_correct_phrases();
    if (data.success) {
        setTimeout(function(){
            alert("WELL DONE!\n\nFinal score: " + data.score);
            restart_game();
        }, 500);
    }
}


function get_score() {
    return parseInt($('#score').text());
}


function get_data(lang) {
    return $('#' + lang).data();
}


function set_data(lang, data) {
    $('#' + lang).data(data);
}


function set_score(newScore) {
    $('#score').text(newScore);
}


function select_tree(data) {
    console.log("SELECT", data);
    var A = get_data('A');
    var B = get_data('B');
    call_server({
        score: get_score(),
        a: {grammar: A.grammar,
            tree: data.lang == "A" ? data.tree : A.tree,
           },
        b: {grammar: B.grammar,
            tree: data.lang == "B" ? data.tree : B.tree,
           },
    });
    show_lin('A', A.lin);
    show_lin('B', B.lin);
    // mark_correct_phrases();
}

// function mark_correct_phrases() : void {
//     $('.' + CORRECT).removeClass(CORRECT);
//     $('.' + MATCHING).removeClass(MATCHING);
//     if (!trees_are_connected()) {
//         var t1 : GFTree = $('#A').data('tree');
//         var t2 : GFTree = $('#B').data('tree');
//         if (t1.toString() == t2.toString()) {
//             $('.A-').addClass(CORRECT);
//             $('.B-').addClass(CORRECT);
//         } else {
//             var equals : {[L:string] : {[path:string] : string}}
//                 = equal_phrases('A', t1, 'B', t2);
//             $('.phrase').each(function(){
//                 var L : string = $(this).data('lang');
//                 var path : string = $(this).data('path');
//                 var refpath : string = equals[L][path];
//                 $(this).toggleClass(MATCHING, Boolean(refpath));
//             });
//         }
//     }
// }


function show_lin(lang, lin) {
    clear_selection();
    var sentence = $('#' + lang).empty();
    lin.forEach(function(word, i, lin){
        var previous = lin[i-1];
        var current = lin[i];
        var spacing = (previous == NOSPACING || current == NOSPACING || PREFIXPUNCT.test(previous) || PUNCTUATION.test(current))
            ? ' ' : ' &nbsp; ';
        $('<span></span>')
            .addClass('space clickable').data({nr:i, lang:lang})
            .html(spacing).click(click_word)
            .appendTo(sentence);
        $('<span></span>')
            .addClass('word clickable').data({nr:i, lang:lang})
            .html(word).click(click_word)
            .appendTo(sentence);
    });
    $('<span></span>')
        .addClass('space clickable').data({nr:lin.length, lang:lang})
        .html(' &nbsp; ').click(click_word)
        .appendTo(sentence);
}


function clear_selection() {
    $('.striked').removeClass('striked');
    $('#menus').empty();
}


function get_selection() {
    var striked = $('.striked').map(function(_i, elem){
        return $(elem).data().nr;
    });
    if (striked.length > 0) {
        return [Math.min.apply(null, striked), 1 + Math.max.apply(null, striked)];
    } else {
        return null;
    }
}


function next_selection(wordnr, selection, maxwidth) {
    if (!selection) return [wordnr, wordnr+1];
    var left = selection[0], right = selection[1]-1;
    if (left > 0 && right > wordnr) {
        return [left-1, right-1+1];
    }
    var width = right - left + 1;
    if (width <= maxwidth) {
        left = wordnr;
        right = wordnr + width;
        if (right >= maxwidth) {
            right = maxwidth - 1;
            left = right - width;
        }
        if (left >= 0) {
            return [left, right+1];
        }
    }
    return null;
}


function click_word(event) {
    console.log("-------------------------------------------------------------------------");
    var clicked = $(event.target);
    var lang = clicked.data().lang;
    var wordnr = clicked.data().nr;
    var maxwidth = get_data(lang).lin.length;
    console.log("Clicked", {lang: lang, wordnr: wordnr, len: maxwidth});

    if (clicked.hasClass('striked') && $('#menus ul').length > 1) {
        $('#menus ul').first().remove();
    }
    else {
        var selection =
            (clicked.hasClass('striked') ? next_selection(wordnr, get_selection(), maxwidth) 
            : clicked.hasClass('word') ? next_selection(wordnr, null, maxwidth)
            : [wordnr, wordnr]).toString();
        clear_selection();
        var menus = get_data(lang).menu[selection];
        console.log("MENU["+selection+"]", menus);
        while (!menus) {
            selection = next_selection(wordnr, selection, maxwidth);
            if (!selection) return;
            var menus = get_data(lang).menu[selection];
            console.log("MENU["+selection+"]", menus);
        }

        clicked.addClass('striked');
        $('#' + lang).find('.word')
            .filter(function(){
                var nr = $(this).data().nr;
                return selection[0] <= nr && nr < selection[1];
            })
            .addClass('striked');
        $('#' + lang).find('.space')
            .filter(function(){
                var nr = $(this).data().nr;
                return selection[0] < nr && nr < selection[1];
            })
            .addClass('striked');

        for (var i = 0; i < menus.length; i++) {
            var ul = $('<ul></ul>').appendTo($('#menus')).hide();
            for (var j = 0; j < menus[i].length; j++) {
                var item = menus[i][j];
                var menuitem = $('<span class="clickable">')
                    .data({'tree': item.tree, 'lang': lang})
                    .click(BUSY(function(c){
                        select_tree($(c).data());
                    }));
                if (item.lin.length == 0) {
                    $('<span></span>').html("&empty;").appendTo(menuitem);;
                } else {
                    $('<span></span>').text(item.lin).appendTo(menuitem);
                }
                $('<li></li>').append(menuitem).appendTo(ul);
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


// Error handling

function alert_error(title, description) {
    alert("*** " + title + "***\n" + description);
}
