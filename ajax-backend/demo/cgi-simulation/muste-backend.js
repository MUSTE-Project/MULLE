var MAX_DEPTH = 3;
var MENU_TIMEOUT = 1000;

var FunTyping;
var TypingFuns;
var Linearise;
var GeneratedTrees;

var Grammar = Grasp;
var Languages = ["GraspSwe", "GraspEng", "GraspGer"];
var StartCat = 'Start';

var USER_DATABASE = {peter: "PETER",
                     herbert: "HERBERT"};
var SERVER_TOKEN = null;

var ALL_LESSONS = {"Lektion Apa": {total: 5, passed: 5, score: 42},
                   "Lektion Bunte": {total: 5, passed: 5, score: 23},
                   "Lektion Caesar": {total: 7, passed: 2, score: 11},
                   "Lektion Dahlia": {total: 3, passed: 0, score: 0},
                   "Lektion Eufori": {total: 7, passed: 0, score: 0},
                   "Lektion Fan": {total: 5, passed: 0, score: 0}};


// var DefaultA = {grammar: "GraspSwe",
//                 tree: parseGFTree("(StartUtt (UttS (UseCl (Pres) (Neg) (PredVP (UsePron (she_Pron))"
//                                   + " (UseVN (break_V) (DetCN (DetQuant (DefArt) (NumPl))"
//                                   + " (ModCN (UseA (yellow_A)) (UseN (stone_N)))))))))")
//                };

var DefaultA = {grammar: "GraspSwe",
                tree: parseGFTree("(StartUtt (UttS (UseCl (Perf) (Pos) (PredVP (UsePN (mary_PN))"
                                  + " (UseVN (eat_V) (AdvNP (DetCN (DetQuant (IndefArt) (NumPl))"
                                  + " (UseN (stone_N))) (UseAdverb (here_Adverb))))))))")
               };

var DefaultB = {grammar: "GraspGer",
                tree: parseGFTree("(StartUtt (UttS (UseCl (Perf) (Pos) (PredVP (UsePN (mary_PN))"
                                  + " (UseVN (eat_V) (AdvNP (DetCN (DetQuant (IndefArt) (NumPl))"
                                  + " (UseN (fish_N))) (UseAdverb (here_Adverb))))))))")
               };


function server_simulation(message, parameters) {
    if (parameters && parameters.token && parameters.token !== SERVER_TOKEN) {
        SERVER_TOKEN = null;
        return server_response("SMSessionInvalid", {error: "Invalid token"});
    }

    switch (message) {
    case "CMLogoutRequest":
        return server_response("SMLogoutResponse");
        break;

    case "CMLoginRequest":
        if (USER_DATABASE[parameters.username] == parameters.password) {
            SERVER_TOKEN = parameters.username;
            return server_response("SMLoginSuccessful", {token: SERVER_TOKEN});
        } else {
            SERVER_TOKEN = null;
            return server_response("SMLoginFail", null);
        }
        break;

    case "CMLessonsRequest":
        var list_of_lessons = [];
        for (var lesson in ALL_LESSONS) {
            ALL_LESSONS[lesson].name = lesson;
            list_of_lessons.push(ALL_LESSONS[lesson]);
        }
        return server_response("SMLessonsList", {lessons: list_of_lessons});
        break;        

    case "CMLessonInit":
        if (!(parameters && parameters.lesson && ALL_LESSONS[parameters.lesson])) {
            SERVER_TOKEN = null;
            return server_response("SMLessonInvalid", null);
        }
        var lesson = ALL_LESSONS[parameters.lesson];
        return server_menu_list(false, parameters.lesson, lesson.total,
                                lesson.passed + 1, 0, DefaultA, DefaultB);
        break;

    case "CMMenuRequest":
        if (!(parameters && parameters.lesson && ALL_LESSONS[parameters.lesson]
              && parameters.exercise && parameters.a && parameters.b)) {
            SERVER_TOKEN = null;
            console.log(parameters);
            return server_response("SMLessonInvalid", null);
        }
        var lesson = ALL_LESSONS[parameters.lesson];
        var passed = parameters.a.tree.toString() == parameters.b.tree.toString();
        if (passed && parameters.exercise > lesson.passed) {
            lesson.passed = parameters.exercise;
            lesson.score += parameters.score + 1;
        }
        return server_menu_list(passed, parameters.lesson, lesson.total,
                                parameters.exercise, parameters.score + 1,
                                parameters.a, parameters.b);
        break;

    case "CMMOTDRequest":
    case "CMDataResponse":
    default:
        var title = (message == "CMMOTDRequest"  ? "CMMOTDRequest: Not implemented"  :
                     message == "CMDataResponse" ? "CMDataResponse: Not implemented" :
                     "Uknown message from client: " + message);
        var description = (parameters ? JSON.stringify(parameters) : "");
        alert_error(title, description);
        SERVER_TOKEN = null;
        break;        
    }
}


function server_menu_list(passed, lesson, total, exercise, score, a, b) {
    var alin = Linearise(a.grammar, a.tree);
    var blin = Linearise(b.grammar, b.tree);
    var equals = equal_phrases(a.grammar, a.tree, b.grammar, b.tree);
    alin.forEach(function(token) {
        var bpath = equals[a.grammar][token.path];
        token.matching = bpath;
    });
    blin.forEach(function(token) {
        var apath = equals[b.grammar][token.path];
        token.matching = apath;
    });
    var amenus = initialize_menus(a.grammar, a.tree);
    var bmenus = initialize_menus(b.grammar, b.tree);
    return server_response("SMMenuList", {passed:passed, lesson:lesson, total:total, exercise:exercise, score:score,
                                          a: {grammar:a.grammar, tree:a.tree, lin:alin, menu:amenus},
                                          b: {grammar:b.grammar, tree:b.tree, lin:blin, menu:bmenus}});
}


function server_response(message, parameters) {
    return {message: message, parameters: parameters};
}


function mkresult(obj) {
    return {grammar: obj.grammar,
            tree: obj.tree,
            lin: Linearise(obj.grammar, obj.tree),
            menu: initialize_menus(obj.grammar, obj.tree)
           };
}


function initialize_simulation() {
    FunTyping = Grammar.abs.types;
    TypingFuns = Grammar.abs.typing2funs;
    Linearise = function (lang, tree) {
        return Grammar.cncs[lang].linearise(tree);
    };
    GeneratedTrees = generate_all_trees();
}


var BracketedLin = (function () {
    function BracketedLin(path, tokens) {
        this.path = path;
        this.tokens = tokens;
    }
    BracketedLin.prototype.toString = function (showpath) {
        var tokstr = this.tokens.map(function (tok) {
            return tok.toString(showpath);
        }).join(" ");
        if (showpath) {
            return "[" + this.path + ": " + tokstr + "]";
        }
        else {
            return "[" + tokstr + "]";
        }
    };
    return BracketedLin;
}());

var BracketedToken = (function () {
    function BracketedToken(word, n) {
        this.word = word;
        this.n = n;
    }
    BracketedToken.prototype.toString = function (showpath) {
        return this.word;
    };
    return BracketedToken;
}());

function bracketise(lin) {
    var stack = [new BracketedLin("", [])];
    var n = 0;
    var path = '';
    while (true) {
        var linpath = n < lin.length && lin[n].path + 'w';
        if (startswith(linpath, path)) {
            if (path === linpath) {
                var linword = lin[n].word;
                stack[stack.length - 1].tokens.push(new BracketedToken(linword, n));
                n++;
            }
            else {
                for (var i = path.length + 1; i <= linpath.length; i++) {
                    stack.push(new BracketedLin(linpath.slice(0, i), []));
                }
                path = linpath;
            }
        }
        else {
            var bracklin = stack.pop();
            stack[stack.length - 1].tokens.push(bracklin);
            path = path.slice(0, -1);
            if (!path)
                break;
        }
    }
    if (lin.length !== n || stack.length !== 1) {
        console.log("SERVER: INTERNAL ERROR: ", lin.length, "!=", n, "//", stack.length, "!=", 1);
    }
    return stack[0];
}

function get_subtrees(tree, path, subtrees) {
    if (!path)
        path = "";
    if (!subtrees)
        subtrees = [];
    subtrees.push({ 'path': path, 'tree': tree });
    for (var i = 0; i < tree.children.length; i++) {
        get_subtrees(tree.children[i], path + i, subtrees);
    }
    return subtrees;
}

function equal_phrases(L1, tree1, L2, tree2) {
    var equals = {};
    equals[L1] = {};
    equals[L2] = {};
    var subs1 = get_subtrees(tree1);
    var subs2 = get_subtrees(tree2);
    for (var i = 0; i < subs1.length; i++) {
        var s1 = subs1[i];
        for (var j = 0; j < subs2.length; j++) {
            var s2 = subs2[j];
            if (s1.tree.toString() == s2.tree.toString()) {
                equals[L1][s1.path] = s2.path;
                equals[L2][s2.path] = s1.path;
                break;
            }
        }
    }
    return equals;
}

function initialize_menus(lang, tree) {
    var final_menus = {};
    var lin = Linearise(lang, tree);
    var all_phrase_paths_D = {};
    for (var i = 0; i < lin.length; i++) {
        var path = lin[i].path;
        for (var j = path.length; j > 0; j--) {
            all_phrase_paths_D[path.slice(0, j)] = true;
        }
    }
    var all_phrase_paths = Object.keys(all_phrase_paths_D);
    all_phrase_paths.sort(function (a, b) { return b.length - a.length; });
    // console.log("SERVER: all_phrase_paths", all_phrase_paths);

    var visited = {};
    visited[tree.toString()] = all_phrase_paths;
    var all_similars = {};
    var all_menus = {};
    var max_cost = 0;
    for (var i = 0; i < all_phrase_paths.length; i++) {
        var phrase_path = all_phrase_paths[i];
        var phrase_tree = tree.getSubtree(phrase_path);
        all_similars[phrase_path] = similar_trees(phrase_tree);
        max_cost = Math.max(max_cost, all_similars[phrase_path].length);
        all_menus[phrase_path] = [];
    }

    var ctr = 0;
    for (var cost = 1; cost <= max_cost; cost++) {
        for (var i = 0; i < all_phrase_paths.length; i++) {
            var phrase_path = all_phrase_paths[i];
            var phrase_left = restrict_left(lin, phrase_path);
            var phrase_right = restrict_right(lin, phrase_path);
            var phrase_lin = lin.slice(phrase_left, phrase_right + 1);
            var phrase_menu = [];
            var similars = all_similars[phrase_path];
            var simphrs = similars[cost];
            if (simphrs) {
                itemloop: for (var simix = 0; simix < simphrs.length; simix++) {
                    var sim = simphrs[simix];
                    var simtree = tree.updateCopy(phrase_path, sim);
                    var stree = simtree.toString();
                    var visitlist = visited[stree];
                    if (!visitlist) {
                        visitlist = visited[stree] = [];
                    }
                    else {
                        for (var sti = 0; sti < visitlist.length; sti++) {
                            if (startswith(visitlist[sti], phrase_path)) {
                                // Utilities.STOP_TIMER(lang + ":visited");
                                continue itemloop;
                            }
                        }
                    }
                    visitlist.push(phrase_path);
                    var simlin = Linearise(lang, simtree);

                    phrase_menu.push({cost:cost, tree:simtree, lin:simlin});
                    ctr++;
                }
            }
            if (phrase_menu.length) {
                all_menus[phrase_path].push(phrase_menu);
            }
        }
    }
    return all_menus;

    // Utilities.STOP_TIMER(lang + ":menugroup");
    // Utilities.START_TIMER(lang + ":finalize", true);
    // for (var i = 0; i < all_phrase_paths.length; i++) {
    //     var phrase_path = all_phrase_paths[i];
    //     var ctr = 0;
    //     // var menus = all_menus[phrase_path];
    //     var menu = all_menus[phrase_path][0];
    //     for (var ppspan in menus) {
    //         var menu = menus[ppspan];
    //         var slins = Object.keys(menu);
    //         slins.sort(function (a, b) {
    //             var ma = menu[a], mb = menu[b];
    //             return ma.cost - mb.cost || (ma.sright - ma.sleft) - (mb.sright - mb.sleft) ||
    //                 mapwords(ma.lin).join().localeCompare(mapwords(mb.lin).join());
    //         });
    //         if (!final_menus[ppspan])
    //             final_menus[ppspan] = {};
    //         var menu_items = final_menus[ppspan][phrase_path] = [];
    //         for (var n = 0; n < slins.length; n++) {
    //             var item = menu[slins[n]];
    //             menu_items.push(item);
    //         }
    //     }
    // }
    // Utilities.STOP_TIMER(lang + ":finalize");
    // Utilities.STOP_TIMER(lang);
    // return final_menus;
}

function similar_trees(tree) {
    var all_pruned = prune_tree(tree);
    var result = [];
    for (var pi = 0; pi < all_pruned.length; pi++) {
        var pruned = all_pruned[pi];
        var fun = pruned.tree.node;
        var typ = pruned.tree.isMeta();
        if (!typ) {
            typ = FunTyping[fun].abscat;
        }
        simloop: for (var si = 0; si < GeneratedTrees[typ].length; si++) {
            var simtree = GeneratedTrees[typ][si];
            var cost = pruned.cost + simtree.cost;
            // this should be optimized
            var new_tree = simtree.tree;
            for (var simtyp in simtree.metas) {
                var simmetas = simtree.metas[simtyp];
                var prunedmetas = pruned.metas[simtyp];
                if (!prunedmetas || prunedmetas.length < simmetas.length) {
                    continue simloop;
                }
                for (var j = 0; j < prunedmetas.length; j++) {
                    if (j < simmetas.length) {
                        var old_path = prunedmetas[j].path;
                        var new_path = simmetas[j].path;
                        var sub = tree.getSubtree(old_path);
                        new_tree = new_tree.updateCopy(new_path, sub);
                    }
                    else {
                        cost += prunedmetas[j].cost;
                    }
                }
            }
            for (var extyp in pruned.metas) {
                if (!simtree.metas[extyp]) {
                    for (var j = 0; j < pruned.metas[extyp].length; j++) {
                        cost += pruned.metas[extyp][j].cost;
                    }
                }
            }
            if (!result[cost])
                result[cost] = [];
            result[cost].push(new_tree);
        }
    }
    return result;
}

function prune_tree(tree) {
    function prune(sub, path, depth) {
        if (depth >= MAX_DEPTH)
            return [];
        var fun = sub.node;
        var typ = FunTyping[fun].abscat;
        return prunechildren(sub, path, 0, depth + 1).concat({ 'tree': GFTree.meta(typ),
            'cost': 0,
            'metas': [{ 'path': path, 'type': typ, 'cost': sub.size() }]
        });
    }
    function prunechildren(sub, path, i, depth) {
        var result = [];
        if (i >= sub.children.length) {
            result.push({ 'tree': sub, 'cost': 1, 'metas': [] });
        }
        else {
            var allchild = prune(sub.children[i], path + i, depth);
            var allchildren = prunechildren(sub, path, i + 1, depth);
            for (var childix = 0; childix < allchild.length; childix++) {
                var child = allchild[childix];
                for (var childrenix = 0; childrenix < allchildren.length; childrenix++) {
                    var children = allchildren[childrenix];
                    result.push({ 'tree': sub.updateCopy(i + '', child.tree),
                        'cost': child.cost + children.cost,
                        'metas': child.metas.concat(children.metas) });
                }
            }
        }
        return result;
    }
    var result0 = prune(tree, "", 0);
    var result = [];
    for (var i = 0; i < result0.length; i++) {
        var metas = {};
        for (var j = 0; j < result0[i].metas.length; j++) {
            var meta = result0[i].metas[j];
            if (!metas[meta.type])
                metas[meta.type] = [];
            metas[meta.type].push(meta);
        }
        result.push({ tree: result0[i].tree,
            cost: result0[i].cost,
            metas: metas });
    }
    return result;
}

function gentrees(typ, path, depth, visited) {
    var result = [];
    if (contains_word(typ, visited))
        return result;
    if (depth == 0) {
        // generate a tree of the form: ?t
        result.push({ 'tree': GFTree.meta(typ),
            'cost': 0,
            'metas': [{ 'path': path, 'type': typ, cost: 0 }] });
    }
    var fun = "default_" + typ;
    var fargs = depth > 0 && FunTyping[fun];
    if (fargs && fargs.children) {
        if (fargs.children.length == 0) {
            result.push({ 'tree': new GFTree(fun, []),
                'cost': 1,
                'metas': [] });
        }
        else {
            console.warn("SERVER: Internal error: you shouldn't have got here", fun, fargs);
        }
    }
    else {
        var newvisited = visited + " " + typ + " ";
        for (var argshash in TypingFuns[typ] || {}) {
            var funs = TypingFuns[typ][argshash];
            var targs = JSON.parse(argshash);
            var metatrees = [];
            var metas = [];
            for (var i = 0; i < targs.length; i++) {
                var argtyp = targs[i];
                metatrees.push(GFTree.meta(argtyp));
                metas.push({ 'path': path + i, 'type': argtyp, cost: 0 });
            }
            // generate trees of the form: (f ?t1 ... ?tn)
            for (var funix = 0; funix < funs.length; funix++) {
                var fun = funs[funix];
                result.push({ 'tree': new GFTree(fun, metatrees), 'cost': 1, 'metas': metas });
            }
            // generate trees of the form: (f (t1) ?t2 ... ?tn), (f ?t1 (t2) ?t3 ... ?tn), ...
            for (var argix = 0; argix < targs.length; argix++) {
                var argtyp = targs[argix];
                var allchildren = gentrees(argtyp, path + argix, depth + 1, newvisited);
                for (var chix = 0; chix < allchildren.length; chix++) {
                    var child = allchildren[chix];
                    var childtrees = metatrees.slice(0, argix).concat([child.tree]).concat(metatrees.slice(argix + 1));
                    var childmetas = metas.slice(0, argix).concat(child.metas).concat(metas.slice(argix + 1));
                    for (var funix = 0; funix < funs.length; funix++) {
                        var fun = funs[funix];
                        result.push({ 'tree': new GFTree(fun, childtrees),
                            'cost': child.cost + 1,
                            'metas': childmetas });
                    }
                }
            }
        }
    }
    return result;
}

function generate_all_trees() {
    // Utilities.START_TIMER("generate", true);
    var total_trees = 0;
    var generated_trees = {};
    for (var typ in TypingFuns) {
        var trees0 = gentrees(typ, '', 0, '');
        var trees = generated_trees[typ] = [];
        for (var i = 0; i < trees0.length; i++) {
            var metas = {};
            for (var j = 0; j < trees0[i].metas.length; j++) {
                var meta = trees0[i].metas[j];
                if (!metas[meta.type])
                    metas[meta.type] = [];
                metas[meta.type].push(meta);
            }
            var treeinfo = { tree: trees0[i].tree,
                cost: trees0[i].cost,
                metas: metas };
            trees.push(treeinfo);
        }
        total_trees += generated_trees[typ].length;
    }
    // Utilities.STOP_TIMER("generate");
    return generated_trees;
}

function contains_word(word, words) {
    return new RegExp(" " + word + " ").test(words);
}

function restrict_left(lin, path) {
    for (var i = 0; i < lin.length; i++) {
        if (startswith(lin[i].path, path))
            return i;
    }
}

function restrict_right(lin, path) {
    for (var i = lin.length - 1; i >= 0; i--) {
        if (startswith(lin[i].path, path))
            return i;
    }
}

function linearise_abstract(tree) {
    // flattened abstract tree
    var lin = [];
    function lintree_(tree, path) {
        if (tree instanceof Array) {
            lin.push({ 'word': "(", 'path': path });
            for (var i in tree) {
                lintree_(tree[i], path); // i>0 ? path+i : path);
            }
            lin.push({ 'word': ")", 'path': path });
        }
        else {
            lin.push({ 'word': tree, 'path': path });
        }
    }
    lintree_(tree, "");
    return lin;
}

function mapwords(lin) {
    return lin.map(function (token) { return token.word; });
}
