"use strict";
var __haste_prog_id = '9d3b9c731a6025f5cebc64260fa07eb8fac723185203a3cf9b64b848fd31ff93';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;
window['__haste_crypto'] = window.crypto || window.msCrypto;
if(window['__haste_crypto'] && !window['__haste_crypto'].subtle && window.crypto.webkitSubtle) {
    window['__haste_crypto'].subtle = window.crypto.webkitSubtle;
}

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __isUndef = function(x) {return typeof x == 'undefined';}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

/* Code for creating and querying the static pointer table. */
window.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    window.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return window.__hs_spt[key];
}

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return _0(_3.b,_2);}));},_4=function(_5,_){while(1){var _6=E(_5);if(!_6._){return 0;}else{var _7=_6.b,_8=E(_6.a);switch(_8._){case 0:var _9=B(A1(_8.a,_));_5=_0(_7,new T2(1,_9,__Z));continue;case 1:_5=_0(_7,_8.a);continue;default:_5=_7;continue;}}}},_a=function(_b,_c,_){var _d=E(_b);switch(_d._){case 0:var _e=B(A1(_d.a,_));return _4(_0(_c,new T2(1,_e,__Z)),_);case 1:return _4(_0(_c,_d.a),_);default:return _4(_c,_);}},_f=new T(function(){return toJSStr(__Z);}),_g=function(_h){return E(_f);},_i=function(_j,_){var _k=E(_j);if(!_k._){return __Z;}else{var _l=_i(_k.b,_);return new T2(1,0,_l);}},_m=function(_n,_){var _o=__arr2lst(0,_n);return _i(_o,_);},_p=function(_){return 0;},_q=new T2(0,function(_r,_){return _p(_);},function(_s,_){return _m(E(_s),_);}),_t=function(_u){var _v=B(A1(_u,_));return E(_v);},_w=new T(function(){return _t(function(_){return __jsNull();});}),_x=function(_y){return E(_w);},_z=function(_A,_B){var _C=E(_B);return (_C._==0)?__Z:new T2(1,new T(function(){return B(A1(_A,_C.a));}),new T(function(){return _z(_A,_C.b);}));},_D=function(_E){return __lst2arr(_z(_x,_E));},_F=function(_G){return E(_f);},_H=function(_I,_){var _J=E(_I);if(!_J._){return __Z;}else{var _K=_H(_J.b,_);return new T2(1,new T(function(){return String(E(_J.a));}),_K);}},_L=function(_M,_){var _N=__arr2lst(0,_M);return _H(_N,_);},_O=function(_P,_){return _L(E(_P),_);},_Q=function(_R){return String(E(_R));},_S=function(_T){return _Q(_T);},_U=function(_V,_){return new T(function(){return _S(_V);});},_W=function(_X){return __lst2arr(E(_X));},_Y=function(_Z){return E(_Z);},_10=function(_11,_12,_13){var _14=function(_15){var _16=new T(function(){return B(A1(_13,_15));});return C > 19 ? new F(function(){return A1(_12,function(_17){return E(_16);});}) : (++C,A1(_12,function(_17){return E(_16);}));};return C > 19 ? new F(function(){return A1(_11,_14);}) : (++C,A1(_11,_14));},_18=function(_19,_1a,_1b){var _1c=new T(function(){return B(A1(_1a,function(_1d){return C > 19 ? new F(function(){return A1(_1b,_1d);}) : (++C,A1(_1b,_1d));}));});return C > 19 ? new F(function(){return A1(_19,function(_1e){return E(_1c);});}) : (++C,A1(_19,function(_1e){return E(_1c);}));},_1f=function(_1g,_1h,_1i){var _1j=function(_1k){var _1l=function(_1m){return C > 19 ? new F(function(){return A1(_1i,new T(function(){return B(A1(_1k,_1m));}));}) : (++C,A1(_1i,new T(function(){return B(A1(_1k,_1m));})));};return C > 19 ? new F(function(){return A1(_1h,_1l);}) : (++C,A1(_1h,_1l));};return C > 19 ? new F(function(){return A1(_1g,_1j);}) : (++C,A1(_1g,_1j));},_1n=function(_1o,_1p){return C > 19 ? new F(function(){return A1(_1p,_1o);}) : (++C,A1(_1p,_1o));},_1q=function(_1r,_1s,_1t){var _1u=new T(function(){return B(A1(_1t,_1r));});return C > 19 ? new F(function(){return A1(_1s,function(_1v){return E(_1u);});}) : (++C,A1(_1s,function(_1v){return E(_1u);}));},_1w=function(_1x,_1y,_1z){var _1A=function(_1B){return C > 19 ? new F(function(){return A1(_1z,new T(function(){return B(A1(_1x,_1B));}));}) : (++C,A1(_1z,new T(function(){return B(A1(_1x,_1B));})));};return C > 19 ? new F(function(){return A1(_1y,_1A);}) : (++C,A1(_1y,_1A));},_1C=function(_1D,_1E,_1F){return C > 19 ? new F(function(){return A1(_1D,function(_1G){return C > 19 ? new F(function(){return A2(_1E,_1G,_1F);}) : (++C,A2(_1E,_1G,_1F));});}) : (++C,A1(_1D,function(_1G){return C > 19 ? new F(function(){return A2(_1E,_1G,_1F);}) : (++C,A2(_1E,_1G,_1F));}));},_1H=function(_1I){return E(E(_1I).b);},_1J=function(_1K,_1L){return C > 19 ? new F(function(){return A3(_1H,_1M,_1K,function(_1N){return E(_1L);});}) : (++C,A3(_1H,_1M,_1K,function(_1N){return E(_1L);}));},_1M=new T(function(){return new T5(0,new T5(0,new T2(0,_1w,_1q),_1n,_1f,_18,_10),_1C,_1J,_1n,function(_1O){return err(_1O);});}),_1P=function(_1Q,_1R,_){var _1S=B(A1(_1R,_));return new T(function(){return B(A1(_1Q,_1S));});},_1T=function(_1U,_1V){return new T1(0,function(_){return _1P(_1V,_1U,_);});},_1W=function(_1X){return new T0(2);},_1Y=function(_1Z){var _20=new T(function(){return B(A1(_1Z,_1W));}),_21=function(_22){return new T1(1,new T2(1,new T(function(){return B(A1(_22,0));}),new T2(1,_20,__Z)));};return _21;},_23=function(_24){return E(_24);},_25=new T3(0,new T2(0,_1M,_1T),_23,_1Y),_26=new T(function(){return unCStr("}");}),_27=new T(function(){return unCStr(", ");}),_28=new T(function(){return unCStr("SM {");}),_29=new T(function(){return unCStr("ssuccess = ");}),_2a=new T(function(){return unCStr("sb = ");}),_2b=new T(function(){return unCStr("sa = ");}),_2c=new T(function(){return unCStr("sscore = ");}),_2d=new T(function(){return unCStr("sgrammar = ");}),_2e=new T(function(){return unCStr("ST {");}),_2f=new T(function(){return unCStr("smenu = ");}),_2g=new T(function(){return unCStr("slin = ");}),_2h=new T(function(){return unCStr("stree = ");}),_2i=new T(function(){return unCStr("M ");}),_2j=function(_2k,_2l,_2m){return C > 19 ? new F(function(){return A1(_2k,new T2(1,44,new T(function(){return B(A1(_2l,_2m));})));}) : (++C,A1(_2k,new T2(1,44,new T(function(){return B(A1(_2l,_2m));}))));},_2n=function(_2o,_2p){var _2q=jsShowI(_2o);return _0(fromJSStr(_2q),_2p);},_2r=function(_2s,_2t,_2u){if(_2t>=0){return _2n(_2t,_2u);}else{if(_2s<=6){return _2n(_2t,_2u);}else{return new T2(1,40,new T(function(){var _2v=jsShowI(_2t);return _0(fromJSStr(_2v),new T2(1,41,_2u));}));}}},_2w=new T(function(){return unCStr(": empty list");}),_2x=new T(function(){return unCStr("Prelude.");}),_2y=function(_2z){return err(_0(_2x,new T(function(){return _0(_2z,_2w);},1)));},_2A=new T(function(){return _2y(new T(function(){return unCStr("foldr1");}));}),_2B=function(_2C,_2D){var _2E=E(_2D);if(!_2E._){return E(_2A);}else{var _2F=_2E.a,_2G=E(_2E.b);if(!_2G._){return E(_2F);}else{return C > 19 ? new F(function(){return A2(_2C,_2F,new T(function(){return B(_2B(_2C,_2G));}));}) : (++C,A2(_2C,_2F,new T(function(){return B(_2B(_2C,_2G));})));}}},_2H=new T(function(){return unCStr("tree = ");}),_2I=new T(function(){return unCStr("lin = ");}),_2J=new T(function(){return unCStr("cost = ");}),_2K=new T(function(){return unCStr("T {");}),_2L=new T(function(){return err(new T(function(){return _0(_2x,new T(function(){return unCStr("!!: negative index");}));}));}),_2M=new T(function(){return err(new T(function(){return _0(_2x,new T(function(){return unCStr("!!: index too large");}));}));}),_2N=function(_2O,_2P){while(1){var _2Q=E(_2O);if(!_2Q._){return E(_2M);}else{var _2R=E(_2P);if(!_2R){return E(_2Q.a);}else{_2O=_2Q.b;_2P=_2R-1|0;continue;}}}},_2S=function(_2T,_2U){if(_2U>=0){return _2N(_2T,_2U);}else{return E(_2L);}},_2V=new T(function(){return unCStr("ACK");}),_2W=new T(function(){return unCStr("BEL");}),_2X=new T(function(){return unCStr("BS");}),_2Y=new T(function(){return unCStr("SP");}),_2Z=new T(function(){return unCStr("US");}),_30=new T(function(){return unCStr("RS");}),_31=new T(function(){return unCStr("GS");}),_32=new T(function(){return unCStr("FS");}),_33=new T(function(){return unCStr("ESC");}),_34=new T(function(){return unCStr("SUB");}),_35=new T(function(){return unCStr("EM");}),_36=new T(function(){return unCStr("CAN");}),_37=new T(function(){return unCStr("ETB");}),_38=new T(function(){return unCStr("SYN");}),_39=new T(function(){return unCStr("NAK");}),_3a=new T(function(){return unCStr("DC4");}),_3b=new T(function(){return unCStr("DC3");}),_3c=new T(function(){return unCStr("DC2");}),_3d=new T(function(){return unCStr("DC1");}),_3e=new T(function(){return unCStr("DLE");}),_3f=new T(function(){return unCStr("SI");}),_3g=new T(function(){return unCStr("SO");}),_3h=new T(function(){return unCStr("CR");}),_3i=new T(function(){return unCStr("FF");}),_3j=new T(function(){return unCStr("VT");}),_3k=new T(function(){return unCStr("LF");}),_3l=new T(function(){return unCStr("HT");}),_3m=new T(function(){return unCStr("ENQ");}),_3n=new T(function(){return unCStr("EOT");}),_3o=new T(function(){return unCStr("ETX");}),_3p=new T(function(){return unCStr("STX");}),_3q=new T(function(){return unCStr("SOH");}),_3r=new T(function(){return unCStr("NUL");}),_3s=new T(function(){return unCStr("\\DEL");}),_3t=new T(function(){return unCStr("\\a");}),_3u=new T(function(){return unCStr("\\\\");}),_3v=new T(function(){return unCStr("\\SO");}),_3w=new T(function(){return unCStr("\\r");}),_3x=new T(function(){return unCStr("\\f");}),_3y=new T(function(){return unCStr("\\v");}),_3z=new T(function(){return unCStr("\\n");}),_3A=new T(function(){return unCStr("\\t");}),_3B=new T(function(){return unCStr("\\b");}),_3C=function(_3D,_3E){if(_3D<=127){var _3F=E(_3D);switch(_3F){case 92:return _0(_3u,_3E);case 127:return _0(_3s,_3E);default:if(_3F<32){switch(_3F){case 7:return _0(_3t,_3E);case 8:return _0(_3B,_3E);case 9:return _0(_3A,_3E);case 10:return _0(_3z,_3E);case 11:return _0(_3y,_3E);case 12:return _0(_3x,_3E);case 13:return _0(_3w,_3E);case 14:return _0(_3v,new T(function(){var _3G=E(_3E);if(!_3G._){return __Z;}else{if(E(_3G.a)==72){return unAppCStr("\\&",_3G);}else{return _3G;}}},1));default:return _0(new T2(1,92,new T(function(){return _2S(new T2(1,_3r,new T2(1,_3q,new T2(1,_3p,new T2(1,_3o,new T2(1,_3n,new T2(1,_3m,new T2(1,_2V,new T2(1,_2W,new T2(1,_2X,new T2(1,_3l,new T2(1,_3k,new T2(1,_3j,new T2(1,_3i,new T2(1,_3h,new T2(1,_3g,new T2(1,_3f,new T2(1,_3e,new T2(1,_3d,new T2(1,_3c,new T2(1,_3b,new T2(1,_3a,new T2(1,_39,new T2(1,_38,new T2(1,_37,new T2(1,_36,new T2(1,_35,new T2(1,_34,new T2(1,_33,new T2(1,_32,new T2(1,_31,new T2(1,_30,new T2(1,_2Z,new T2(1,_2Y,__Z))))))))))))))))))))))))))))))))),_3F);})),_3E);}}else{return new T2(1,_3F,_3E);}}}else{var _3H=new T(function(){var _3I=jsShowI(_3D);return _0(fromJSStr(_3I),new T(function(){var _3J=E(_3E);if(!_3J._){return __Z;}else{var _3K=E(_3J.a);if(_3K<48){return _3J;}else{if(_3K>57){return _3J;}else{return unAppCStr("\\&",_3J);}}}},1));});return new T2(1,92,_3H);}},_3L=new T(function(){return unCStr("\\\"");}),_3M=function(_3N,_3O){var _3P=E(_3N);if(!_3P._){return E(_3O);}else{var _3Q=_3P.b,_3R=E(_3P.a);if(_3R==34){return _0(_3L,new T(function(){return _3M(_3Q,_3O);},1));}else{return _3C(_3R,new T(function(){return _3M(_3Q,_3O);}));}}},_3S=function(_3T,_3U){return new T2(1,34,new T(function(){return _3M(_3T,new T2(1,34,_3U));}));},_3V=function(_3W,_3X,_3Y){var _3Z=E(_3X);if(!_3Z._){return unAppCStr("[]",_3Y);}else{var _40=new T(function(){var _41=new T(function(){var _42=function(_43){var _44=E(_43);if(!_44._){return E(new T2(1,93,_3Y));}else{var _45=new T(function(){return B(A2(_3W,_44.a,new T(function(){return _42(_44.b);})));});return new T2(1,44,_45);}};return _42(_3Z.b);});return B(A2(_3W,_3Z.a,_41));});return new T2(1,91,_40);}},_46=function(_47,_48){return _2r(0,E(_47),_48);},_49=function(_4a,_4b){return _3V(_46,_4a,_4b);},_4c=function(_4d,_4e,_4f,_4g,_4h){var _4i=function(_4j){var _4k=new T(function(){var _4l=new T(function(){var _4m=new T(function(){var _4n=new T(function(){var _4o=new T(function(){var _4p=new T(function(){var _4q=new T(function(){var _4r=new T(function(){return _3M(_4g,new T2(1,34,new T(function(){return _0(_26,_4j);})));});return _0(_2H,new T2(1,34,_4r));},1);return _0(_27,_4q);}),_4s=E(_4f);if(!_4s._){return unAppCStr("[]",_4p);}else{var _4t=new T(function(){var _4u=E(_4s.a),_4v=new T(function(){var _4w=new T(function(){var _4x=function(_4y){var _4z=E(_4y);if(!_4z._){return E(new T2(1,93,_4p));}else{var _4A=new T(function(){var _4B=E(_4z.a),_4C=new T(function(){return B(A3(_2B,_2j,new T2(1,function(_4D){return _49(_4B.a,_4D);},new T2(1,function(_4E){return _3S(_4B.b,_4E);},__Z)),new T2(1,41,new T(function(){return _4x(_4z.b);}))));});return new T2(1,40,_4C);});return new T2(1,44,_4A);}};return _4x(_4s.b);});return B(A3(_2B,_2j,new T2(1,function(_4F){return _49(_4u.a,_4F);},new T2(1,function(_4G){return _3S(_4u.b,_4G);},__Z)),new T2(1,41,_4w)));});return new T2(1,40,_4v);});return new T2(1,91,_4t);}},1);return _0(_2I,_4o);},1);return _0(_27,_4n);});return _2r(0,E(_4e),_4m);},1);return _0(_2J,_4l);},1);return _0(_2K,_4k);};if(_4d<11){return _4i(_4h);}else{return new T2(1,40,new T(function(){return _4i(new T2(1,41,_4h));}));}},_4H=function(_4I,_4J){var _4K=E(_4I);return _4c(0,_4K.a,_4K.b,_4K.c,_4J);},_4L=function(_4M,_4N){return _3V(_4H,_4M,_4N);},_4O=function(_4P){return _3V(_4L,_4P,__Z);},_4Q=function(_4R,_4S){return _3V(_4L,_4R,_4S);},_4T=function(_4U,_4V){return _3V(_4Q,_4U,_4V);},_4W=function(_4X,_4M,_4N){return _4Q(_4M,_4N);},_4Y=function(_4Z){return _3V(_46,_4Z,__Z);},_50=function(_51,_52){return _3V(_49,_51,_52);},_53=function(_54,_55,_56){return _49(_55,_56);},_57=function(_58,_59){while(1){var _5a=(function(_5b,_5c){var _5d=E(_5c);if(!_5d._){_58=new T2(1,new T2(0,_5d.b,_5d.c),new T(function(){return _57(_5b,_5d.e);}));_59=_5d.d;return __continue;}else{return E(_5b);}})(_58,_59);if(_5a!=__continue){return _5a;}}},_5e=new T(function(){return unCStr("fromList ");}),_5f=function(_5g){return E(E(_5g).a);},_5h=function(_5i,_5j,_5k,_5l){var _5m=new T(function(){return _57(__Z,_5l);}),_5n=function(_5o,_5p){var _5q=E(_5o),_5r=new T(function(){return B(A3(_2B,_2j,new T2(1,new T(function(){return B(A3(_5f,_5i,0,_5q.a));}),new T2(1,new T(function(){return B(A3(_5f,_5j,0,_5q.b));}),__Z)),new T2(1,41,_5p)));});return new T2(1,40,_5r);};if(_5k<=10){var _5s=function(_5t){return _0(_5e,new T(function(){return _3V(_5n,_5m,_5t);},1));};return _5s;}else{var _5u=function(_5v){var _5w=new T(function(){return _0(_5e,new T(function(){return _3V(_5n,_5m,new T2(1,41,_5v));},1));});return new T2(1,40,_5w);};return _5u;}},_5x=function(_5y,_5z){var _5A=new T(function(){return _5h(new T3(0,_53,_4Y,_50),new T3(0,_4W,_4O,_4T),11,_5z);});if(_5y<11){var _5B=function(_5C){return _0(_2i,new T(function(){return B(A1(_5A,_5C));},1));};return _5B;}else{var _5D=function(_5E){var _5F=new T(function(){return _0(_2i,new T(function(){return B(A1(_5A,new T2(1,41,_5E)));},1));});return new T2(1,40,_5F);};return _5D;}},_5G=function(_5H,_5I,_5J,_5K,_5L){var _5M=new T(function(){return _5x(0,E(_5L).a);}),_5N=function(_5O){var _5P=new T(function(){var _5Q=new T(function(){var _5R=new T(function(){var _5S=new T(function(){var _5T=new T(function(){var _5U=new T(function(){var _5V=new T(function(){var _5W=new T(function(){var _5X=new T(function(){var _5Y=new T(function(){var _5Z=new T(function(){return B(A1(_5M,new T(function(){return _0(_26,_5O);})));},1);return _0(_2f,_5Z);},1);return _0(_27,_5Y);}),_60=E(_5K);if(!_60._){return unAppCStr("[]",_5X);}else{var _61=new T(function(){var _62=new T(function(){var _63=function(_64){var _65=E(_64);if(!_65._){return E(new T2(1,93,_5X));}else{var _66=new T(function(){return _3M(_65.a,new T2(1,34,new T(function(){return _63(_65.b);})));});return new T2(1,44,new T2(1,34,_66));}};return _63(_60.b);});return _3M(_60.a,new T2(1,34,_62));});return new T2(1,91,new T2(1,34,_61));}},1);return _0(_2g,_5W);},1);return _0(_27,_5V);});return _3M(_5J,new T2(1,34,_5U));});return _0(_2h,new T2(1,34,_5T));},1);return _0(_27,_5S);});return _3M(_5I,new T2(1,34,_5R));});return _0(_2d,new T2(1,34,_5Q));},1);return _0(_2e,_5P);};if(_5H<11){return _5N;}else{var _67=function(_68){return new T2(1,40,new T(function(){return _5N(new T2(1,41,_68));}));};return _67;}},_69=new T(function(){return unCStr("True");}),_6a=new T(function(){return unCStr("False");}),_6b=function(_6c,_6d,_6e,_6f,_6g){var _6h=new T(function(){var _6i=E(_6f);return _5G(0,_6i.a,_6i.b,_6i.c,_6i.d);}),_6j=new T(function(){var _6k=E(_6g);return _5G(0,_6k.a,_6k.b,_6k.c,_6k.d);}),_6l=function(_6m){var _6n=new T(function(){var _6o=new T(function(){var _6p=new T(function(){var _6q=new T(function(){var _6r=new T(function(){var _6s=new T(function(){var _6t=new T(function(){var _6u=new T(function(){return B(A1(_6j,new T(function(){return _0(_26,_6m);})));},1);return _0(_2a,_6u);},1);return _0(_27,_6t);});return B(A1(_6h,_6s));},1);return _0(_2b,_6r);},1);return _0(_27,_6q);});return _2r(0,E(_6e),_6p);},1);return _0(_2c,_6o);},1);return _0(_27,_6n);},_6v=function(_6w){var _6x=new T(function(){if(!E(_6d)){return _0(_6a,new T(function(){return _6l(_6w);},1));}else{return _0(_69,new T(function(){return _6l(_6w);},1));}},1);return _0(_29,_6x);};if(_6c<11){var _6y=function(_6z){return _0(_28,new T(function(){return _6v(_6z);},1));};return _6y;}else{var _6A=function(_6B){var _6C=new T(function(){return _0(_28,new T(function(){return _6v(new T2(1,41,_6B));},1));});return new T2(1,40,_6C);};return _6A;}},_6D=function(_6E){return E(E(_6E).a);},_6F=function(_6G,_6H){var _6I=strEq(E(_6G),E(_6H));return (E(_6I)==0)?false:true;},_6J=new T(function(){return new T2(0,function(_6K,_6L){return _6F(_6K,_6L);},function(_6M,_6N){return (!B(A3(_6D,_6J,_6M,_6N)))?true:false;});}),_6O=new T(function(){return unCStr("base");}),_6P=new T(function(){return unCStr("Control.Exception.Base");}),_6Q=new T(function(){return unCStr("PatternMatchFail");}),_6R=function(_6S){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6O,_6P,_6Q),__Z,__Z));},_6T=function(_6U){return E(E(_6U).a);},_6V=function(_6W,_6X,_6Y){var _6Z=B(A1(_6W,_)),_70=B(A1(_6X,_)),_71=hs_eqWord64(_6Z.a,_70.a);if(!_71){return __Z;}else{var _72=hs_eqWord64(_6Z.b,_70.b);return (!_72)?__Z:new T1(1,_6Y);}},_73=function(_74){return E(E(_74).a);},_75=function(_76,_77){return _0(E(_76).a,_77);},_78=new T(function(){return new T5(0,_6R,new T3(0,function(_79,_7a,_7b){return _0(E(_7a).a,_7b);},_73,function(_7c,_7d){return _3V(_75,_7c,_7d);}),function(_7e){return new T2(0,_78,_7e);},function(_7f){var _7g=E(_7f);return _6V(_6T(_7g.a),_6R,_7g.b);},_73);}),_7h=new T(function(){return unCStr("Non-exhaustive patterns in");}),_7i=function(_7j){return E(E(_7j).c);},_7k=function(_7l,_7m){return die(new T(function(){return B(A2(_7i,_7m,_7l));}));},_7n=function(_7o,_7p){return _7k(_7o,_7p);},_7q=function(_7r,_7s){var _7t=E(_7s);if(!_7t._){return new T2(0,__Z,__Z);}else{var _7u=_7t.a;if(!B(A1(_7r,_7u))){return new T2(0,__Z,_7t);}else{var _7v=new T(function(){var _7w=_7q(_7r,_7t.b);return new T2(0,_7w.a,_7w.b);});return new T2(0,new T2(1,_7u,new T(function(){return E(E(_7v).a);})),new T(function(){return E(E(_7v).b);}));}}},_7x=new T(function(){return unCStr("\n");}),_7y=function(_7z){return (E(_7z)==124)?false:true;},_7A=function(_7B,_7C){var _7D=_7q(_7y,unCStr(_7B)),_7E=_7D.a,_7F=function(_7G,_7H){var _7I=new T(function(){var _7J=new T(function(){return _0(_7C,new T(function(){return _0(_7H,_7x);},1));});return unAppCStr(": ",_7J);},1);return _0(_7G,_7I);},_7K=E(_7D.b);if(!_7K._){return _7F(_7E,__Z);}else{if(E(_7K.a)==124){return _7F(_7E,new T2(1,32,_7K.b));}else{return _7F(_7E,__Z);}}},_7L=function(_7M){return _7n(new T1(0,new T(function(){return _7A(_7M,_7h);})),_78);},_7N=new T(function(){return B(_7L("Ajax.hs:166:52-77|lambda"));}),_7O=new T(function(){return B(_7L("Ajax.hs:166:17-37|lambda"));}),_7P=new T(function(){return unCStr("main");}),_7Q=new T(function(){return unCStr("Ajax");}),_7R=new T(function(){return unCStr("ServerMessageException");}),_7S=function(_7T){return E(new T5(0,new Long(2796709153,857663197,true),new Long(2290229150,2001624562,true),new T5(0,new Long(2796709153,857663197,true),new Long(2290229150,2001624562,true),_7P,_7Q,_7R),__Z,__Z));},_7U=new T(function(){return unCStr("SME ");}),_7V=function(_7W,_7X,_7Y){if(_7W<11){return _0(_7U,new T2(1,34,new T(function(){return _3M(_7X,new T2(1,34,_7Y));})));}else{var _7Z=new T(function(){return _0(_7U,new T2(1,34,new T(function(){return _3M(_7X,new T2(1,34,new T2(1,41,_7Y)));})));});return new T2(1,40,_7Z);}},_80=function(_81){return _7V(0,E(_81).a,__Z);},_82=function(_83,_84){return _7V(0,E(_83).a,_84);},_85=new T(function(){return new T5(0,_7S,new T3(0,function(_86,_87,_88){return _7V(E(_86),E(_87).a,_88);},_80,function(_4M,_4N){return _3V(_82,_4M,_4N);}),function(_4N){return new T2(0,_85,_4N);},function(_89){var _8a=E(_89);return _6V(_6T(_8a.a),_7S,_8a.b);},_80);}),_8b=new T(function(){return unCStr("Error decoding message data");}),_8c=new T(function(){var _8d=_;return _7n(new T1(0,_8b),_85);}),_8e=new T(function(){return _7n(new T1(0,new T(function(){return fromJSStr("Invalid JSON!");})),_85);}),_8f=function(_8g,_8h){while(1){var _8i=E(_8g);if(!_8i._){return (E(_8h)._==0)?1:0;}else{var _8j=E(_8h);if(!_8j._){return 2;}else{var _8k=E(_8i.a),_8l=E(_8j.a);if(_8k>=_8l){if(_8k!=_8l){return 2;}else{_8g=_8i.b;_8h=_8j.b;continue;}}else{return 0;}}}}},_8m=new T0(1),_8n=new T(function(){return unCStr("Failure in Data.Map.balanceL");}),_8o=new T(function(){var _8p=_;return err(_8n);}),_8q=function(_8r,_8s,_8t,_8u){var _8v=E(_8u);if(!_8v._){var _8w=_8v.a,_8x=E(_8t);if(!_8x._){var _8y=_8x.a,_8z=_8x.b,_8A=_8x.c;if(_8y<=(imul(3,_8w)|0)){return new T5(0,(1+_8y|0)+_8w|0,E(_8r),_8s,_8x,_8v);}else{var _8B=E(_8x.d);if(!_8B._){var _8C=_8B.a,_8D=E(_8x.e);if(!_8D._){var _8E=_8D.a,_8F=_8D.b,_8G=_8D.c,_8H=_8D.d;if(_8E>=(imul(2,_8C)|0)){var _8I=function(_8J){var _8K=E(_8D.e);return (_8K._==0)?new T5(0,(1+_8y|0)+_8w|0,E(_8F),_8G,E(new T5(0,(1+_8C|0)+_8J|0,E(_8z),_8A,_8B,E(_8H))),E(new T5(0,(1+_8w|0)+_8K.a|0,E(_8r),_8s,_8K,_8v))):new T5(0,(1+_8y|0)+_8w|0,E(_8F),_8G,E(new T5(0,(1+_8C|0)+_8J|0,E(_8z),_8A,_8B,E(_8H))),E(new T5(0,1+_8w|0,E(_8r),_8s,E(_8m),_8v)));},_8L=E(_8H);if(!_8L._){return _8I(_8L.a);}else{return _8I(0);}}else{return new T5(0,(1+_8y|0)+_8w|0,E(_8z),_8A,_8B,E(new T5(0,(1+_8w|0)+_8E|0,E(_8r),_8s,_8D,_8v)));}}else{return E(_8o);}}else{return E(_8o);}}}else{return new T5(0,1+_8w|0,E(_8r),_8s,E(_8m),_8v);}}else{var _8M=E(_8t);if(!_8M._){var _8N=_8M.a,_8O=_8M.b,_8P=_8M.c,_8Q=_8M.e,_8R=E(_8M.d);if(!_8R._){var _8S=_8R.a,_8T=E(_8Q);if(!_8T._){var _8U=_8T.a,_8V=_8T.b,_8W=_8T.c,_8X=_8T.d;if(_8U>=(imul(2,_8S)|0)){var _8Y=function(_8Z){var _90=E(_8T.e);return (_90._==0)?new T5(0,1+_8N|0,E(_8V),_8W,E(new T5(0,(1+_8S|0)+_8Z|0,E(_8O),_8P,_8R,E(_8X))),E(new T5(0,1+_90.a|0,E(_8r),_8s,_90,E(_8m)))):new T5(0,1+_8N|0,E(_8V),_8W,E(new T5(0,(1+_8S|0)+_8Z|0,E(_8O),_8P,_8R,E(_8X))),E(new T5(0,1,E(_8r),_8s,E(_8m),E(_8m))));},_91=E(_8X);if(!_91._){return _8Y(_91.a);}else{return _8Y(0);}}else{return new T5(0,1+_8N|0,E(_8O),_8P,_8R,E(new T5(0,1+_8U|0,E(_8r),_8s,_8T,E(_8m))));}}else{return new T5(0,3,E(_8O),_8P,_8R,E(new T5(0,1,E(_8r),_8s,E(_8m),E(_8m))));}}else{var _92=E(_8Q);return (_92._==0)?new T5(0,3,E(_92.b),_92.c,E(new T5(0,1,E(_8O),_8P,E(_8m),E(_8m))),E(new T5(0,1,E(_8r),_8s,E(_8m),E(_8m)))):new T5(0,2,E(_8r),_8s,_8M,E(_8m));}}else{return new T5(0,1,E(_8r),_8s,E(_8m),E(_8m));}}},_93=new T(function(){return unCStr("Failure in Data.Map.balanceR");}),_94=new T(function(){var _95=_;return err(_93);}),_96=function(_97,_98,_99,_9a){var _9b=E(_99);if(!_9b._){var _9c=_9b.a,_9d=E(_9a);if(!_9d._){var _9e=_9d.a,_9f=_9d.b,_9g=_9d.c;if(_9e<=(imul(3,_9c)|0)){return new T5(0,(1+_9c|0)+_9e|0,E(_97),_98,_9b,_9d);}else{var _9h=E(_9d.d);if(!_9h._){var _9i=_9h.a,_9j=_9h.b,_9k=_9h.c,_9l=_9h.d,_9m=E(_9d.e);if(!_9m._){var _9n=_9m.a;if(_9i>=(imul(2,_9n)|0)){var _9o=function(_9p){var _9q=E(_97),_9r=E(_9h.e);return (_9r._==0)?new T5(0,(1+_9c|0)+_9e|0,E(_9j),_9k,E(new T5(0,(1+_9c|0)+_9p|0,_9q,_98,_9b,E(_9l))),E(new T5(0,(1+_9n|0)+_9r.a|0,E(_9f),_9g,_9r,_9m))):new T5(0,(1+_9c|0)+_9e|0,E(_9j),_9k,E(new T5(0,(1+_9c|0)+_9p|0,_9q,_98,_9b,E(_9l))),E(new T5(0,1+_9n|0,E(_9f),_9g,E(_8m),_9m)));},_9s=E(_9l);if(!_9s._){return _9o(_9s.a);}else{return _9o(0);}}else{return new T5(0,(1+_9c|0)+_9e|0,E(_9f),_9g,E(new T5(0,(1+_9c|0)+_9i|0,E(_97),_98,_9b,_9h)),_9m);}}else{return E(_94);}}else{return E(_94);}}}else{return new T5(0,1+_9c|0,E(_97),_98,_9b,E(_8m));}}else{var _9t=E(_9a);if(!_9t._){var _9u=_9t.a,_9v=_9t.b,_9w=_9t.c,_9x=_9t.e,_9y=E(_9t.d);if(!_9y._){var _9z=_9y.a,_9A=_9y.b,_9B=_9y.c,_9C=_9y.d,_9D=E(_9x);if(!_9D._){var _9E=_9D.a;if(_9z>=(imul(2,_9E)|0)){var _9F=function(_9G){var _9H=E(_97),_9I=E(_9y.e);return (_9I._==0)?new T5(0,1+_9u|0,E(_9A),_9B,E(new T5(0,1+_9G|0,_9H,_98,E(_8m),E(_9C))),E(new T5(0,(1+_9E|0)+_9I.a|0,E(_9v),_9w,_9I,_9D))):new T5(0,1+_9u|0,E(_9A),_9B,E(new T5(0,1+_9G|0,_9H,_98,E(_8m),E(_9C))),E(new T5(0,1+_9E|0,E(_9v),_9w,E(_8m),_9D)));},_9J=E(_9C);if(!_9J._){return _9F(_9J.a);}else{return _9F(0);}}else{return new T5(0,1+_9u|0,E(_9v),_9w,E(new T5(0,1+_9z|0,E(_97),_98,E(_8m),_9y)),_9D);}}else{return new T5(0,3,E(_9A),_9B,E(new T5(0,1,E(_97),_98,E(_8m),E(_8m))),E(new T5(0,1,E(_9v),_9w,E(_8m),E(_8m))));}}else{var _9K=E(_9x);return (_9K._==0)?new T5(0,3,E(_9v),_9w,E(new T5(0,1,E(_97),_98,E(_8m),E(_8m))),_9K):new T5(0,2,E(_97),_98,E(_8m),_9t);}}else{return new T5(0,1,E(_97),_98,E(_8m),E(_8m));}}},_9L=function(_9M,_9N,_9O){var _9P=E(_9M),_9Q=E(_9N),_9R=E(_9O);if(!_9R._){var _9S=_9R.b,_9T=_9R.c,_9U=_9R.d,_9V=_9R.e;switch(_8f(_9P,_9S)){case 0:return _8q(_9S,_9T,_9L(_9P,_9Q,_9U),_9V);case 1:return new T5(0,_9R.a,_9P,_9Q,E(_9U),E(_9V));default:return _96(_9S,_9T,_9U,_9L(_9P,_9Q,_9V));}}else{return new T5(0,1,_9P,_9Q,E(_8m),E(_8m));}},_9W=function(_9X,_9Y){while(1){var _9Z=E(_9Y);if(!_9Z._){return E(_9X);}else{var _a0=E(_9Z.a),_a1=_9L(_a0.a,_a0.b,_9X);_9X=_a1;_9Y=_9Z.b;continue;}}},_a2=function(_a3,_a4){return new T5(0,1,E(_a3),_a4,E(_8m),E(_8m));},_a5=function(_a6,_a7,_a8){var _a9=E(_a8);if(!_a9._){return _96(_a9.b,_a9.c,_a9.d,_a5(_a6,_a7,_a9.e));}else{return _a2(_a6,_a7);}},_aa=function(_ab,_ac,_ad){var _ae=E(_ad);if(!_ae._){return _8q(_ae.b,_ae.c,_aa(_ab,_ac,_ae.d),_ae.e);}else{return _a2(_ab,_ac);}},_af=function(_ag,_ah,_ai,_aj,_ak,_al,_am){return _8q(_aj,_ak,_aa(_ag,_ah,_al),_am);},_an=function(_ao,_ap,_aq,_ar,_as,_at,_au,_av){var _aw=E(_aq);if(!_aw._){var _ax=_aw.a,_ay=_aw.b,_az=_aw.c,_aA=_aw.d,_aB=_aw.e;if((imul(3,_ax)|0)>=_ar){if((imul(3,_ar)|0)>=_ax){return new T5(0,(_ax+_ar|0)+1|0,E(_ao),_ap,_aw,E(new T5(0,_ar,E(_as),_at,E(_au),E(_av))));}else{return _96(_ay,_az,_aA,B(_an(_ao,_ap,_aB,_ar,_as,_at,_au,_av)));}}else{return _8q(_as,_at,B(_aC(_ao,_ap,_ax,_ay,_az,_aA,_aB,_au)),_av);}}else{return _af(_ao,_ap,_ar,_as,_at,_au,_av);}},_aC=function(_aD,_aE,_aF,_aG,_aH,_aI,_aJ,_aK){var _aL=E(_aK);if(!_aL._){var _aM=_aL.a,_aN=_aL.b,_aO=_aL.c,_aP=_aL.d,_aQ=_aL.e;if((imul(3,_aF)|0)>=_aM){if((imul(3,_aM)|0)>=_aF){return new T5(0,(_aF+_aM|0)+1|0,E(_aD),_aE,E(new T5(0,_aF,E(_aG),_aH,E(_aI),E(_aJ))),_aL);}else{return _96(_aG,_aH,_aI,B(_an(_aD,_aE,_aJ,_aM,_aN,_aO,_aP,_aQ)));}}else{return _8q(_aN,_aO,B(_aC(_aD,_aE,_aF,_aG,_aH,_aI,_aJ,_aP)),_aQ);}}else{return _a5(_aD,_aE,new T5(0,_aF,E(_aG),_aH,E(_aI),E(_aJ)));}},_aR=function(_aS,_aT,_aU,_aV){var _aW=E(_aU);if(!_aW._){var _aX=_aW.a,_aY=_aW.b,_aZ=_aW.c,_b0=_aW.d,_b1=_aW.e,_b2=E(_aV);if(!_b2._){var _b3=_b2.a,_b4=_b2.b,_b5=_b2.c,_b6=_b2.d,_b7=_b2.e;if((imul(3,_aX)|0)>=_b3){if((imul(3,_b3)|0)>=_aX){return new T5(0,(_aX+_b3|0)+1|0,E(_aS),_aT,_aW,_b2);}else{return _96(_aY,_aZ,_b0,B(_an(_aS,_aT,_b1,_b3,_b4,_b5,_b6,_b7)));}}else{return _8q(_b4,_b5,B(_aC(_aS,_aT,_aX,_aY,_aZ,_b0,_b1,_b6)),_b7);}}else{return _a5(_aS,_aT,_aW);}}else{return _aa(_aS,_aT,_aV);}},_b8=function(_b9,_ba){var _bb=E(_ba);if(!_bb._){return new T3(0,_8m,__Z,__Z);}else{var _bc=E(_b9);if(_bc==1){var _bd=E(_bb.a),_be=_bd.a,_bf=_bd.b,_bg=E(_bb.b);return (_bg._==0)?new T3(0,new T(function(){return new T5(0,1,E(_be),E(_bf),E(_8m),E(_8m));}),__Z,__Z):(_8f(_be,E(_bg.a).a)==0)?new T3(0,new T(function(){return new T5(0,1,E(_be),E(_bf),E(_8m),E(_8m));}),_bg,__Z):new T3(0,new T(function(){return new T5(0,1,E(_be),E(_bf),E(_8m),E(_8m));}),__Z,_bg);}else{var _bh=_b8(_bc>>1,_bb),_bi=_bh.a,_bj=_bh.c,_bk=E(_bh.b);if(!_bk._){return new T3(0,_bi,__Z,_bj);}else{var _bl=E(_bk.a),_bm=_bl.a,_bn=_bl.b,_bo=E(_bk.b);if(!_bo._){return new T3(0,new T(function(){return _a5(_bm,E(_bn),_bi);}),__Z,_bj);}else{if(!_8f(_bm,E(_bo.a).a)){var _bp=_b8(_bc>>1,_bo);return new T3(0,new T(function(){return B(_aR(_bm,E(_bn),_bi,_bp.a));}),_bp.b,_bp.c);}else{return new T3(0,_bi,__Z,_bk);}}}}}},_bq=function(_br,_bs,_bt){while(1){var _bu=E(_bt);if(!_bu._){return E(_bs);}else{var _bv=E(_bu.a),_bw=_bv.a,_bx=_bv.b,_by=E(_bu.b);if(!_by._){return _a5(_bw,E(_bx),_bs);}else{if(!_8f(_bw,E(_by.a).a)){var _bz=_b8(_br,_by),_bA=_bz.a,_bB=E(_bz.c);if(!_bB._){var _bC=_br<<1,_bD=B(_aR(_bw,E(_bx),_bs,_bA));_br=_bC;_bs=_bD;_bt=_bz.b;continue;}else{return _9W(B(_aR(_bw,E(_bx),_bs,_bA)),_bB);}}else{return _9W(_bs,_bu);}}}}},_bE=new T(function(){return B((function(_bF){var _bG=E(_bF);if(!_bG._){return new T0(1);}else{var _bH=E(_bG.a),_bI=_bH.a,_bJ=_bH.b,_bK=E(_bG.b);if(!_bK._){return new T5(0,1,E(_bI),E(_bJ),E(_8m),E(_8m));}else{if(!_8f(_bI,E(_bK.a).a)){return C > 19 ? new F(function(){return _bq(1,new T5(0,1,E(_bI),E(_bJ),E(_8m),E(_8m)),_bK);}) : (++C,_bq(1,new T5(0,1,E(_bI),E(_bJ),E(_8m),E(_8m)),_bK));}else{return _9W(new T5(0,1,E(_bI),E(_bJ),E(_8m),E(_8m)),_bK);}}}})(__Z));}),_bL=new T(function(){return _7n(new T1(0,new T(function(){return unCStr("Error decoding tree data");})),_85);}),_bM=function(_bN){var _bO=E(_bN);if(_bO._==1){return fromJSStr(_bO.a);}else{return C > 19 ? new F(function(){return _7L("Ajax.hs:183:12-31|lambda");}) : (++C,_7L("Ajax.hs:183:12-31|lambda"));}},_bP=new T(function(){return _7n(new T1(0,new T(function(){return unCStr("Error decoding lin data");})),_85);}),_bQ=new T(function(){return B(_7L("Ajax.hs:178:57-83|lambda"));}),_bR=new T(function(){return B(_7L("Ajax.hs:178:16-42|lambda"));}),_bS=function(_bT,_bU,_bV){while(1){var _bW=E(_bV);if(!_bW._){return __Z;}else{var _bX=E(_bW.a);if(!B(A3(_6D,_bT,_bU,_bX.a))){_bV=_bW.b;continue;}else{return new T1(1,_bX.b);}}}},_bY=function(_bZ){var _c0=E(_bZ);if(_c0._==4){var _c1=_c0.a,_c2=_bS(_6J,"grammar",_c1);if(!_c2._){return E(_bL);}else{var _c3=_bS(_6J,"tree",_c1);if(!_c3._){return E(_bL);}else{var _c4=_bS(_6J,"lin",_c1);return (_c4._==0)?E(_bL):(_bS(_6J,"menu",_c1)._==0)?E(_bL):new T4(0,new T(function(){var _c5=E(_c2.a);if(_c5._==1){return fromJSStr(_c5.a);}else{return E(_bR);}}),new T(function(){var _c6=E(_c3.a);if(_c6._==1){return fromJSStr(_c6.a);}else{return E(_bQ);}}),new T(function(){var _c7=E(_c4.a);if(_c7._==3){return _z(_bM,_c7.a);}else{return E(_bP);}}),new T1(0,_bE));}}}else{return E(_bL);}},_c8=function(_c9){var _ca=_bY(_c9);return new T4(0,_ca.a,_ca.b,_ca.c,_ca.d);},_cb=function(_cc){var _cd=jsParseJSON(_cc);if(!_cd._){return E(_8e);}else{var _ce=E(_cd.a);if(_ce._==4){var _cf=_ce.a,_cg=_bS(_6J,"success",_cf);if(!_cg._){return E(_8c);}else{var _ch=_bS(_6J,"score",_cf);if(!_ch._){return E(_8c);}else{var _ci=_bS(_6J,"a",_cf);if(!_ci._){return E(_8c);}else{var _cj=_bS(_6J,"b",_cf);return (_cj._==0)?E(_8c):new T4(0,new T(function(){var _ck=E(_cg.a);if(_ck._==2){return E(_ck.a);}else{return E(_7O);}}),new T(function(){var _cl=E(_ch.a);if(!_cl._){var _cm=_cl.a,_cn=_cm&4294967295;if(_cm>=_cn){return _cn;}else{return _cn-1|0;}}else{return E(_7N);}}),new T(function(){return _c8(_ci.a);}),new T(function(){return _c8(_cj.a);}));}}}}else{return E(_8c);}}},_co=new T(function(){return JSON.stringify;}),_cp=function(_cq,_cr){var _cs=E(_cr);switch(_cs._){case 0:return new T2(0,new T(function(){return jsShow(_cs.a);}),_cq);case 1:return new T2(0,new T(function(){var _ct=E(_co)(_cs.a);return String(_ct);}),_cq);case 2:return (!E(_cs.a))?new T2(0,"false",_cq):new T2(0,"true",_cq);case 3:var _cu=E(_cs.a);if(!_cu._){return new T2(0,"[",new T2(1,"]",_cq));}else{var _cv=new T(function(){var _cw=new T(function(){var _cx=function(_cy){var _cz=E(_cy);if(!_cz._){return E(new T2(1,"]",_cq));}else{var _cA=new T(function(){var _cB=_cp(new T(function(){return _cx(_cz.b);}),_cz.a);return new T2(1,_cB.a,_cB.b);});return new T2(1,",",_cA);}};return _cx(_cu.b);}),_cC=_cp(_cw,_cu.a);return new T2(1,_cC.a,_cC.b);});return new T2(0,"[",_cv);}break;case 4:var _cD=E(_cs.a);if(!_cD._){return new T2(0,"{",new T2(1,"}",_cq));}else{var _cE=E(_cD.a),_cF=new T(function(){var _cG=new T(function(){var _cH=function(_cI){var _cJ=E(_cI);if(!_cJ._){return E(new T2(1,"}",_cq));}else{var _cK=E(_cJ.a),_cL=new T(function(){var _cM=_cp(new T(function(){return _cH(_cJ.b);}),_cK.b);return new T2(1,_cM.a,_cM.b);});return new T2(1,",",new T2(1,"\"",new T2(1,_cK.a,new T2(1,"\"",new T2(1,":",_cL)))));}};return _cH(_cD.b);}),_cN=_cp(_cG,_cE.b);return new T2(1,_cN.a,_cN.b);});return new T2(0,"{",new T2(1,new T(function(){var _cO=E(_co)(E(_cE.a));return String(_cO);}),new T2(1,":",_cF)));}break;default:return new T2(0,"null",_cq);}},_cP=new T(function(){return toJSStr(__Z);}),_cQ=function(_cR){var _cS=_cp(__Z,_cR),_cT=jsCat(new T2(1,_cS.a,_cS.b),E(_cP));return E(_cT);},_cU=function(_cV,_cW){return new T2(1,new T2(0,"grammar",new T(function(){return new T1(1,toJSStr(E(_cV)));})),new T2(1,new T2(0,"tree",new T(function(){return new T1(1,toJSStr(E(_cW)));})),__Z));},_cX=function(_cY){var _cZ=E(_cY);return new T1(4,E(_cU(_cZ.a,_cZ.b)));},_d0=function(_d1){var _d2=E(_d1);if(!_d2._){return _cQ(new T0(5));}else{return _cQ(new T1(4,E(new T2(1,new T2(0,"score",new T(function(){return new T1(1,toJSStr(_2r(0,E(_d2.a),__Z)));})),new T2(1,new T2(0,"a",new T(function(){return _cX(_d2.b);})),new T2(1,new T2(0,"b",new T(function(){return _cX(_d2.c);})),__Z))))));}},_d3=function(_d4){return E(E(_d4).a);},_d5=function(_d6,_d7,_d8,_d9,_da){return C > 19 ? new F(function(){return A2(_d7,_d8,new T2(1,B(A2(_d3,_d6,E(_da))),E(_d9)));}) : (++C,A2(_d7,_d8,new T2(1,B(A2(_d3,_d6,E(_da))),E(_d9))));},_db=function(_dc){return E(E(_dc).a);},_dd=function(_de){return E(E(_de).a);},_df=function(_dg){return E(E(_dg).a);},_dh=function(_di){return E(E(_di).b);},_dj=new T(function(){return unCStr("base");}),_dk=new T(function(){return unCStr("GHC.IO.Exception");}),_dl=new T(function(){return unCStr("IOException");}),_dm=function(_dn){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_dj,_dk,_dl),__Z,__Z));},_do=new T(function(){return unCStr(": ");}),_dp=new T(function(){return unCStr(")");}),_dq=new T(function(){return unCStr(" (");}),_dr=new T(function(){return unCStr("interrupted");}),_ds=new T(function(){return unCStr("system error");}),_dt=new T(function(){return unCStr("unsatisified constraints");}),_du=new T(function(){return unCStr("user error");}),_dv=new T(function(){return unCStr("permission denied");}),_dw=new T(function(){return unCStr("illegal operation");}),_dx=new T(function(){return unCStr("end of file");}),_dy=new T(function(){return unCStr("resource exhausted");}),_dz=new T(function(){return unCStr("resource busy");}),_dA=new T(function(){return unCStr("does not exist");}),_dB=new T(function(){return unCStr("already exists");}),_dC=new T(function(){return unCStr("resource vanished");}),_dD=new T(function(){return unCStr("timeout");}),_dE=new T(function(){return unCStr("unsupported operation");}),_dF=new T(function(){return unCStr("hardware fault");}),_dG=new T(function(){return unCStr("inappropriate type");}),_dH=new T(function(){return unCStr("invalid argument");}),_dI=new T(function(){return unCStr("failed");}),_dJ=new T(function(){return unCStr("protocol error");}),_dK=function(_dL,_dM){switch(E(_dL)){case 0:return _0(_dB,_dM);case 1:return _0(_dA,_dM);case 2:return _0(_dz,_dM);case 3:return _0(_dy,_dM);case 4:return _0(_dx,_dM);case 5:return _0(_dw,_dM);case 6:return _0(_dv,_dM);case 7:return _0(_du,_dM);case 8:return _0(_dt,_dM);case 9:return _0(_ds,_dM);case 10:return _0(_dJ,_dM);case 11:return _0(_dI,_dM);case 12:return _0(_dH,_dM);case 13:return _0(_dG,_dM);case 14:return _0(_dF,_dM);case 15:return _0(_dE,_dM);case 16:return _0(_dD,_dM);case 17:return _0(_dC,_dM);default:return _0(_dr,_dM);}},_dN=new T(function(){return unCStr("}");}),_dO=new T(function(){return unCStr("{handle: ");}),_dP=function(_dQ,_dR,_dS,_dT,_dU,_dV){var _dW=new T(function(){var _dX=new T(function(){var _dY=new T(function(){var _dZ=E(_dT);if(!_dZ._){return E(_dV);}else{var _e0=new T(function(){return _0(_dZ,new T(function(){return _0(_dp,_dV);},1));},1);return _0(_dq,_e0);}},1);return _dK(_dR,_dY);}),_e1=E(_dS);if(!_e1._){return E(_dX);}else{return _0(_e1,new T(function(){return _0(_do,_dX);},1));}}),_e2=E(_dU);if(!_e2._){var _e3=E(_dQ);if(!_e3._){return E(_dW);}else{var _e4=E(_e3.a);if(!_e4._){var _e5=new T(function(){var _e6=new T(function(){return _0(_dN,new T(function(){return _0(_do,_dW);},1));},1);return _0(_e4.a,_e6);},1);return _0(_dO,_e5);}else{var _e7=new T(function(){var _e8=new T(function(){return _0(_dN,new T(function(){return _0(_do,_dW);},1));},1);return _0(_e4.a,_e8);},1);return _0(_dO,_e7);}}}else{return _0(_e2.a,new T(function(){return _0(_do,_dW);},1));}},_e9=function(_ea){var _eb=E(_ea);return _dP(_eb.a,_eb.b,_eb.c,_eb.d,_eb.f,__Z);},_ec=function(_ed,_ee){var _ef=E(_ed);return _dP(_ef.a,_ef.b,_ef.c,_ef.d,_ef.f,_ee);},_eg=new T(function(){return new T5(0,_dm,new T3(0,function(_eh,_ei,_ej){var _ek=E(_ei);return _dP(_ek.a,_ek.b,_ek.c,_ek.d,_ek.f,_ej);},_e9,function(_el,_em){return _3V(_ec,_el,_em);}),_en,function(_eo){var _ep=E(_eo);return _6V(_6T(_ep.a),_dm,_ep.b);},_e9);}),_en=function(_eq){return new T2(0,_eg,_eq);},_er=function(_es,_){var _et=_es["type"],_eu=String(_et),_ev=strEq(_eu,"network");if(!E(_ev)){var _ew=strEq(_eu,"http");if(!E(_ew)){var _ex=new T(function(){var _ey=new T(function(){return unAppCStr("unknown type of ajax error: ",new T(function(){return fromJSStr(_eu);}));});return _en(new T6(0,__Z,7,__Z,_ey,__Z,__Z));});return die(_ex);}else{var _ez=_es["status"],_eA=_es["status-text"];return new T2(1,new T(function(){var _eB=Number(_ez);return jsTrunc(_eB);}),new T(function(){return String(_eA);}));}}else{return __Z;}},_eC=function(_eD,_){var _eE=E(_eD);if(!_eE._){return __Z;}else{var _eF=_er(E(_eE.a),_),_eG=_eC(_eE.b,_);return new T2(1,_eF,_eG);}},_eH=function(_eI,_){var _eJ=__arr2lst(0,_eI);return _eC(_eJ,_);},_eK=new T2(0,function(_eL,_){return _er(E(_eL),_);},function(_eM,_){return _eH(E(_eM),_);}),_eN=function(_eO){return E(E(_eO).a);},_eP=function(_eQ,_eR,_){var _eS=__eq(_eR,E(_w));if(!E(_eS)){var _eT=__isUndef(_eR);if(!E(_eT)){var _eU=B(A3(_eN,_eQ,_eR,_));return new T1(1,_eU);}else{return __Z;}}else{return __Z;}},_eV=function(_eW,_eX,_){var _eY=__arr2lst(0,_eX),_eZ=function(_f0,_){var _f1=E(_f0);if(!_f1._){return __Z;}else{var _f2=_f1.b,_f3=E(_f1.a),_f4=__eq(_f3,E(_w));if(!E(_f4)){var _f5=__isUndef(_f3);if(!E(_f5)){var _f6=B(A3(_eN,_eW,_f3,_)),_f7=_eZ(_f2,_);return new T2(1,new T1(1,_f6),_f7);}else{var _f8=_eZ(_f2,_);return new T2(1,__Z,_f8);}}else{var _f9=_eZ(_f2,_);return new T2(1,__Z,_f9);}}};return _eZ(_eY,_);},_fa=new T2(0,function(_fb,_){return _eP(_eK,E(_fb),_);},function(_fc,_){return _eV(_eK,E(_fc),_);}),_fd=function(_fe,_ff,_){var _fg=B(A2(_fe,new T(function(){var _fh=E(_ff),_fi=__eq(_fh,E(_w));if(!E(_fi)){var _fj=__isUndef(_fh);if(!E(_fj)){return new T1(1,_fh);}else{return __Z;}}else{return __Z;}}),_));return _w;},_fk=new T2(0,_fd,function(_fl){return 2;}),_fm=function(_fn){return E(E(_fn).a);},_fo=function(_fp,_fq,_fr,_fs){var _ft=new T(function(){return B(A1(_fr,new T(function(){var _fu=B(A3(_eN,_fp,_fs,_));return E(_fu);})));});return C > 19 ? new F(function(){return A2(_fm,_fq,_ft);}) : (++C,A2(_fm,_fq,_ft));},_fv=function(_fw){return E(E(_fw).b);},_fx=new T(function(){return err(new T(function(){return unCStr("Prelude.undefined");}));}),_fy=function(_fz,_fA,_fB){var _fC=__createJSFunc(1+B(A2(_fv,_fA,new T(function(){return B(A1(_fB,_fx));})))|0,function(_fD){return C > 19 ? new F(function(){return _fo(_fz,_fA,_fB,_fD);}) : (++C,_fo(_fz,_fA,_fB,_fD));});return E(_fC);},_fE=function(_fF,_fG,_fH){return _fy(_fF,_fG,_fH);},_fI=function(_fJ,_fK,_fL){var _fM=__lst2arr(_z(function(_fN){return _fE(_fJ,_fK,_fN);},_fL));return E(_fM);},_fO=new T2(0,function(_fP){return _fy(_fa,_fk,_fP);},function(_fQ){return _fI(_fa,_fk,_fQ);}),_fR=function(_fS,_fT,_fU,_){var _fV=__apply(_fT,E(_fU));return C > 19 ? new F(function(){return A3(_eN,_fS,_fV,_);}) : (++C,A3(_eN,_fS,_fV,_));},_fW=function(_fX,_fY,_fZ,_){return C > 19 ? new F(function(){return _fR(_fX,E(_fY),_fZ,_);}) : (++C,_fR(_fX,E(_fY),_fZ,_));},_g0=function(_g1,_g2,_g3,_){return C > 19 ? new F(function(){return _fW(_g1,_g2,_g3,_);}) : (++C,_fW(_g1,_g2,_g3,_));},_g4=function(_g5,_g6,_){return C > 19 ? new F(function(){return _g0(_q,_g5,_g6,_);}) : (++C,_g0(_q,_g5,_g6,_));},_g7=function(_g8){return E(E(_g8).c);},_g9=(function(method, uri, mimeout, responseType, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, uri);xhr.responseType = responseType;if(mimeout != '') {xhr.setRequestHeader('Content-type', mimeout);}xhr.addEventListener('load', function() {if(xhr.status < 400) {cb(null, xhr.response);}else {cb({'type':'http', 'status':xhr.status, 'status-text': xhr.statusText}, null);}});xhr.addEventListener('error', function() {if(xhr.status != 0) {cb({'type':'http', 'status':xhr.status, 'status-text': xhr.statusText}, null);} else {cb({'type':'network'}, null);}});xhr.send(postdata);}),_ga=function(_gb){return E(E(_gb).b);},_gc=function(_gd){return E(E(_gd).b);},_ge=new T(function(){return B(_7L("src/Haste/Ajax.hs:(61,7)-(63,60)|case"));}),_gf=function(_gg){return E(E(_gg).c);},_gh=new T1(1,__Z),_gi=function(_){return nMV(_gh);},_gj=new T0(2),_gk=function(_gl,_gm,_gn){var _go=function(_gp){var _gq=function(_){var _gr=E(_gm),_gs=rMV(_gr),_gt=E(_gs);if(!_gt._){var _gu=new T(function(){var _gv=new T(function(){return B(A1(_gp,0));});return _0(_gt.b,new T2(1,new T2(0,_gn,function(_gw){return E(_gv);}),__Z));}),_=wMV(_gr,new T2(0,_gt.a,_gu));return _gj;}else{var _gx=E(_gt.a);if(!_gx._){var _=wMV(_gr,new T2(0,_gn,__Z));return new T(function(){return B(A1(_gp,0));});}else{var _=wMV(_gr,new T1(1,_gx.b));return new T1(1,new T2(1,new T(function(){return B(A1(_gp,0));}),new T2(1,new T(function(){return B(A2(_gx.a,_gn,_1W));}),__Z)));}}};return new T1(0,_gq);};return C > 19 ? new F(function(){return A2(_ga,_gl,_go);}) : (++C,A2(_ga,_gl,_go));},_gy=function(_gz){return E(E(_gz).d);},_gA=function(_gB,_gC){var _gD=function(_gE){var _gF=function(_){var _gG=E(_gC),_gH=rMV(_gG),_gI=E(_gH);if(!_gI._){var _gJ=_gI.a,_gK=E(_gI.b);if(!_gK._){var _=wMV(_gG,_gh);return new T(function(){return B(A1(_gE,_gJ));});}else{var _gL=E(_gK.a),_=wMV(_gG,new T2(0,_gL.a,_gK.b));return new T1(1,new T2(1,new T(function(){return B(A1(_gE,_gJ));}),new T2(1,new T(function(){return B(A1(_gL.b,_1W));}),__Z)));}}else{var _gM=new T(function(){var _gN=function(_gO){var _gP=new T(function(){return B(A1(_gE,_gO));});return function(_gQ){return E(_gP);};};return _0(_gI.a,new T2(1,_gN,__Z));}),_=wMV(_gG,new T1(1,_gM));return _gj;}};return new T1(0,_gF);};return C > 19 ? new F(function(){return A2(_ga,_gB,_gD);}) : (++C,A2(_ga,_gB,_gD));},_gR=function(_gS,_gT,_gU,_gV,_gW,_gX){var _gY=_dd(_gS),_gZ=new T(function(){return _ga(_gS);}),_h0=new T(function(){return _gc(_gY);}),_h1=_df(_gY),_h2=new T(function(){return _dh(_gU);}),_h3=new T(function(){var _h4=function(_h5){var _h6=E(_gV),_h7=strEq(E(_f),_h6);if(!E(_h7)){var _h8=_h6;}else{var _h8=B(A2(_gf,_gT,0));}return function(_fD){return C > 19 ? new F(function(){return _d5(_fO,_g4,_g9,new T2(1,E(_w),new T2(1,B(A2(_gy,_gU,0)),new T2(1,_h8,new T2(1,E(_gX),new T2(1,_h5,__Z))))),_fD);}) : (++C,_d5(_fO,_g4,_g9,new T2(1,E(_w),new T2(1,B(A2(_gy,_gU,0)),new T2(1,_h8,new T2(1,E(_gX),new T2(1,_h5,__Z))))),_fD));};},_h9=function(_ha,_hb){var _hc=E(_gV),_hd=strEq(E(_f),_hc);if(!E(_hd)){var _he=_hc;}else{var _he=B(A2(_gf,_gT,0));}return function(_fD){return C > 19 ? new F(function(){return _d5(_fO,_g4,_g9,new T2(1,E(_ha),new T2(1,B(A2(_gy,_gU,0)),new T2(1,_he,new T2(1,E(_gX),new T2(1,_hb,__Z))))),_fD);}) : (++C,_d5(_fO,_g4,_g9,new T2(1,E(_ha),new T2(1,B(A2(_gy,_gU,0)),new T2(1,_he,new T2(1,E(_gX),new T2(1,_hb,__Z))))),_fD));};},_hf=E(_gW);switch(_hf._){case 0:return _h4("GET");break;case 1:return _h4("DELETE");break;case 2:return _h9(new T(function(){return B(A2(_d3,_db(_gT),_hf.a));}),"POST");break;default:return _h9(new T(function(){return B(A2(_d3,_db(_gT),_hf.a));}),"PUT");}}),_hg=function(_hh){var _hi=new T(function(){return B(A1(_gZ,new T(function(){return B(_gA(_25,_hh));})));}),_hj=new T(function(){var _hk=new T(function(){var _hl=function(_hm,_hn,_){var _ho=E(_hn);if(!_ho._){var _hp=E(_hm);if(!_hp._){return E(_ge);}else{return _a(new T(function(){return B(A(_gk,[_25,_hh,new T1(0,_hp.a),_1W]));}),__Z,_);}}else{var _hq=B(A3(_eN,_h2,_ho.a,_));return _a(new T(function(){return B(A(_gk,[_25,_hh,new T1(1,_hq),_1W]));}),__Z,_);}};return B(A1(_h3,_hl));});return B(A1(_h0,_hk));});return C > 19 ? new F(function(){return A3(_g7,_h1,_hj,_hi);}) : (++C,A3(_g7,_h1,_hj,_hi));};return C > 19 ? new F(function(){return A3(_1H,_h1,new T(function(){return B(A2(_gc,_gY,_gi));}),_hg);}) : (++C,A3(_1H,_h1,new T(function(){return B(A2(_gc,_gY,_gi));}),_hg));},_hr=new T(function(){return err(new T(function(){return unCStr("AjaxError");}));}),_hs=(function(x){console.log(x);}),_ht=function(_hu){var _hv=new T(function(){return _d0(_hu);}),_hw=new T(function(){return toJSStr(unAppCStr("Send client message ",new T(function(){return fromJSStr(E(_hv));})));}),_hx=new T(function(){return B(_gR(_25,new T4(0,new T2(0,_x,_D),_q,_g,_g),new T4(0,new T2(0,_Y,_W),new T2(0,_U,_O),_F,_F),_f,new T1(0,_),_hv));}),_hy=function(_hz){var _hA=function(_){var _hB=_hs(E(_hw));return new T(function(){var _hC=function(_hD){var _hE=E(_hD);if(!_hE._){return E(_hr);}else{var _hF=new T(function(){var _hG=_cb(E(_hE.a));return new T4(0,_hG.a,_hG.b,_hG.c,_hG.d);}),_hH=function(_){var _hI=_hs(toJSStr(unAppCStr("Loaded server message ",new T(function(){var _hJ=E(_hF);return B(A(_6b,[0,_hJ.a,_hJ.b,_hJ.c,_hJ.d,__Z]));}))));return new T(function(){return B(A1(_hz,_hF));});};return new T1(0,_hH);}};return B(A1(_hx,_hC));});};return new T1(0,_hA);};return _hy;},_hK=new T(function(){return unAppCStr(") is outside of enumeration\'s range (0,",new T(function(){return _2r(0,2,new T(function(){return unCStr(")");}));}));}),_hL=function(_hM){return err(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return _2r(0,_hM,_hK);})));},_hN=function(_hO,_){return new T(function(){var _hP=Number(E(_hO)),_hQ=jsTrunc(_hP);if(_hQ<0){return _hL(_hQ);}else{if(_hQ>2){return _hL(_hQ);}else{return _hQ;}}});},_hR=new T3(0,0,0,0),_hS=new T(function(){return jsGetMouseCoords;}),_hT=function(_hU,_){var _hV=E(_hU);if(!_hV._){return __Z;}else{var _hW=_hT(_hV.b,_);return new T2(1,new T(function(){var _hX=Number(E(_hV.a));return jsTrunc(_hX);}),_hW);}},_hY=function(_hZ,_){var _i0=__arr2lst(0,_hZ);return _hT(_i0,_);},_i1=function(_i2,_){return new T(function(){var _i3=Number(E(_i2));return jsTrunc(_i3);});},_i4=new T2(0,_i1,function(_i5,_){return _hY(E(_i5),_);}),_i6=function(_i7,_){var _i8=E(_i7);if(!_i8._){return __Z;}else{var _i9=_i6(_i8.b,_);return new T2(1,_i8.a,_i9);}},_ia=new T(function(){return _en(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9");}),__Z,__Z));}),_ib=function(_){return die(_ia);},_ic=function(_id,_ie,_if,_){var _ig=__arr2lst(0,_if),_ih=_i6(_ig,_),_ii=E(_ih);if(!_ii._){return _ib(_);}else{var _ij=E(_ii.b);if(!_ij._){return _ib(_);}else{if(!E(_ij.b)._){var _ik=B(A3(_eN,_id,_ii.a,_)),_il=B(A3(_eN,_ie,_ij.a,_));return new T2(0,_ik,_il);}else{return _ib(_);}}}},_im=function(_in,_io,_){if(E(_in)==7){var _ip=E(_hS)(_io),_iq=_ic(_i4,_i4,_ip,_),_ir=_io["deltaX"],_is=_io["deltaY"],_it=_io["deltaZ"];return new T(function(){return new T3(0,E(_iq),E(__Z),E(new T3(0,_ir,_is,_it)));});}else{var _iu=E(_hS)(_io),_iv=_ic(_i4,_i4,_iu,_),_iw=_io["button"],_ix=__eq(_iw,E(_w));if(!E(_ix)){var _iy=__isUndef(_iw);if(!E(_iy)){var _iz=_hN(_iw,_);return new T(function(){return new T3(0,E(_iv),E(new T1(1,_iz)),E(_hR));});}else{return new T(function(){return new T3(0,E(_iv),E(__Z),E(_hR));});}}else{return new T(function(){return new T3(0,E(_iv),E(__Z),E(_hR));});}}},_iA=new T2(0,function(_iB){switch(E(_iB)){case 0:return "click";case 1:return "dblclick";case 2:return "mousedown";case 3:return "mouseup";case 4:return "mousemove";case 5:return "mouseover";case 6:return "mouseout";default:return "wheel";}},function(_iC,_iD,_){return _im(_iC,E(_iD),_);}),_iE=function(_iF){return E(_iF);},_iG=function(_iH,_iI,_){var _iJ=B(A1(_iH,_)),_iK=B(A1(_iI,_));return new T(function(){return B(A1(_iJ,_iK));});},_iL=function(_iM,_){return _iM;},_iN=function(_iO,_iP,_){var _iQ=B(A1(_iO,_));return C > 19 ? new F(function(){return A1(_iP,_);}) : (++C,A1(_iP,_));},_iR=new T(function(){return E(_eg);}),_iS=function(_iT){return new T6(0,__Z,7,__Z,_iT,__Z,__Z);},_iU=function(_iV,_){var _iW=new T(function(){return B(A2(_7i,_iR,new T(function(){return B(A1(_iS,_iV));})));});return die(_iW);},_iX=function(_iY,_){return _iU(_iY,_);},_iZ=new T2(0,new T5(0,new T5(0,new T2(0,_1P,function(_j0,_j1,_){var _j2=B(A1(_j1,_));return _j0;}),_iL,_iG,_iN,function(_j3,_j4,_){var _j5=B(A1(_j3,_)),_j6=B(A1(_j4,_));return _j5;}),function(_j7,_j8,_){var _j9=B(A1(_j7,_));return C > 19 ? new F(function(){return A2(_j8,_j9,_);}) : (++C,A2(_j8,_j9,_));},_iN,_iL,function(_ja){return C > 19 ? new F(function(){return A1(_iX,_ja);}) : (++C,A1(_iX,_ja));}),_23),_jb=new T2(0,_iZ,_iL),_jc=(function(c,p){p.appendChild(c);}),_jd=function(_je){return E(E(_je).d);},_jf=new T2(0,_23,function(_jg,_jh){return C > 19 ? new F(function(){return A2(_jd,_df(_jg),new T1(1,_jh));}) : (++C,A2(_jd,_df(_jg),new T1(1,_jh)));}),_ji=(function(t){return document.createElement(t);}),_jj=function(_){return _ji("span");},_jk=function(_jl){return E(E(_jl).a);},_jm=(function(e,p,v){e.setAttribute(p, v);}),_jn=(function(e,p,v){e.style[p] = v;}),_jo=(function(e,p,v){e[p] = v;}),_jp=function(_jq,_jr,_js,_jt){var _ju=new T(function(){return B(A2(_jk,_jq,_js));}),_jv=function(_jw,_){var _jx=E(_jw);if(!_jx._){return 0;}else{var _jy=E(_ju),_jz=_jc(E(_jx.a),_jy),_jA=function(_jB,_){while(1){var _jC=E(_jB);if(!_jC._){return 0;}else{var _jD=_jc(E(_jC.a),_jy);_jB=_jC.b;continue;}}};return _jA(_jx.b,_);}},_jE=function(_jF,_){while(1){var _jG=(function(_jH,_){var _jI=E(_jH);if(!_jI._){return 0;}else{var _jJ=_jI.b,_jK=E(_jI.a);if(!_jK._){var _jL=_jK.b,_jM=E(_jK.a);switch(_jM._){case 0:var _jN=E(_ju),_jO=_jo(_jN,_jM.a,_jL),_jP=function(_jQ,_){while(1){var _jR=E(_jQ);if(!_jR._){return 0;}else{var _jS=_jR.b,_jT=E(_jR.a);if(!_jT._){var _jU=_jT.b,_jV=E(_jT.a);switch(_jV._){case 0:var _jW=_jo(_jN,_jV.a,_jU);_jQ=_jS;continue;case 1:var _jX=_jn(_jN,_jV.a,_jU);_jQ=_jS;continue;default:var _jY=_jm(_jN,_jV.a,_jU);_jQ=_jS;continue;}}else{var _jZ=_jv(_jT.a,_);_jQ=_jS;continue;}}}};return _jP(_jJ,_);case 1:var _k0=E(_ju),_k1=_jn(_k0,_jM.a,_jL),_k2=function(_k3,_){while(1){var _k4=E(_k3);if(!_k4._){return 0;}else{var _k5=_k4.b,_k6=E(_k4.a);if(!_k6._){var _k7=_k6.b,_k8=E(_k6.a);switch(_k8._){case 0:var _k9=_jo(_k0,_k8.a,_k7);_k3=_k5;continue;case 1:var _ka=_jn(_k0,_k8.a,_k7);_k3=_k5;continue;default:var _kb=_jm(_k0,_k8.a,_k7);_k3=_k5;continue;}}else{var _kc=_jv(_k6.a,_);_k3=_k5;continue;}}}};return _k2(_jJ,_);default:var _kd=E(_ju),_ke=_jm(_kd,_jM.a,_jL),_kf=function(_kg,_){while(1){var _kh=E(_kg);if(!_kh._){return 0;}else{var _ki=_kh.b,_kj=E(_kh.a);if(!_kj._){var _kk=_kj.b,_kl=E(_kj.a);switch(_kl._){case 0:var _km=_jo(_kd,_kl.a,_kk);_kg=_ki;continue;case 1:var _kn=_jn(_kd,_kl.a,_kk);_kg=_ki;continue;default:var _ko=_jm(_kd,_kl.a,_kk);_kg=_ki;continue;}}else{var _kp=_jv(_kj.a,_);_kg=_ki;continue;}}}};return _kf(_jJ,_);}}else{var _kq=_jv(_jK.a,_);_jF=_jJ;return __continue;}}})(_jF,_);if(_jG!=__continue){return _jG;}}};return C > 19 ? new F(function(){return A2(_gc,_jr,function(_){return _jE(_jt,_);});}) : (++C,A2(_gc,_jr,function(_){return _jE(_jt,_);}));},_kr=function(_ks,_kt,_ku,_kv){var _kw=_df(_kt),_kx=function(_ky){return C > 19 ? new F(function(){return A3(_g7,_kw,new T(function(){return B(_jp(_ks,_kt,_ky,_kv));}),new T(function(){return B(A2(_jd,_kw,_ky));}));}) : (++C,A3(_g7,_kw,new T(function(){return B(_jp(_ks,_kt,_ky,_kv));}),new T(function(){return B(A2(_jd,_kw,_ky));})));};return C > 19 ? new F(function(){return A3(_1H,_kw,_ku,_kx);}) : (++C,A3(_1H,_kw,_ku,_kx));},_kz=new T(function(){return B(_kr(_jf,_iZ,_jj,new T2(1,new T(function(){return new T2(0,E(new T1(2,"class")),"path");}),__Z)));}),_kA=new T(function(){return _t(function(_){return nMV(__Z);});}),_kB=(function(e){if(e){e.stopPropagation();}}),_kC=function(_){var _kD=rMV(E(_kA)),_kE=E(_kD);if(!_kE._){var _kF=_kB(E(_w));return _p(_);}else{var _kG=_kB(E(_kE.a));return _p(_);}},_kH=function(_kI,_){var _kJ=_kC(_);return 0;},_kK=new T(function(){return unCStr(" ");}),_kL=new T(function(){return B(_kr(_jf,_iZ,_jj,new T2(1,new T(function(){return new T2(0,E(new T1(2,"class")),"gap");}),__Z)));}),_kM=new T(function(){return B(_kr(_jf,_iZ,_jj,new T2(1,new T(function(){return new T2(0,E(new T1(2,"class")),"word");}),__Z)));}),_kN=(function(s){return document.createTextNode(s);}),_kO=function(_kP){return E(E(_kP).a);},_kQ=function(_kR){return E(E(_kR).b);},_kS=function(_kT){return E(E(_kT).a);},_kU=function(_kV){return E(E(_kV).b);},_kW=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_kX=function(_kY,_kZ,_l0,_l1,_l2,_l3){var _l4=_kO(_kY),_l5=_df(_l4),_l6=new T(function(){return _gc(_l4);}),_l7=new T(function(){return _jd(_l5);}),_l8=new T(function(){return B(A1(_kZ,_l1));}),_l9=new T(function(){return B(A2(_kS,_l0,_l2));}),_la=function(_lb){return C > 19 ? new F(function(){return A1(_l7,new T3(0,_l9,_l8,_lb));}) : (++C,A1(_l7,new T3(0,_l9,_l8,_lb)));},_lc=function(_ld){var _le=new T(function(){var _lf=new T(function(){var _lg=__createJSFunc(2,function(_lh,_){var _li=B(A2(E(_ld),_lh,_));return _w;}),_lj=_lg;return function(_){return _kW(E(_l8),E(_l9),_lj);};});return B(A1(_l6,_lf));});return C > 19 ? new F(function(){return A3(_1H,_l5,_le,_la);}) : (++C,A3(_1H,_l5,_le,_la));},_lk=new T(function(){var _ll=new T(function(){return _gc(_l4);}),_lm=function(_ln){var _lo=new T(function(){return B(A1(_ll,function(_){var _=wMV(E(_kA),new T1(1,_ln));return C > 19 ? new F(function(){return A(_kQ,[_l0,_l2,_ln,_]);}) : (++C,A(_kQ,[_l0,_l2,_ln,_]));}));});return C > 19 ? new F(function(){return A3(_1H,_l5,_lo,_l3);}) : (++C,A3(_1H,_l5,_lo,_l3));};return B(A2(_kU,_kY,_lm));});return C > 19 ? new F(function(){return A3(_1H,_l5,_lk,_lc);}) : (++C,A3(_1H,_l5,_lk,_lc));},_lp=(function(e,c) {e.classList.toggle(c);}),_lq=new T(function(){return unCStr("wordHover");}),_lr=function(_ls,_){var _lt=_lp(_ls,toJSStr(E(_lq)));return _p(_);},_lu=function(_lv,_lw,_){return _lr(E(_lv),_);},_lx=function(_ly,_lz,_lA,_lB,_lC,_lD,_){var _lE=function(_){var _lF=B(A1(_kM,_)),_lG=_lF,_lH=_kN(toJSStr(E(_lA))),_lI=B(A(_kX,[_jb,_iE,_iA,_lG,5,function(_lJ,_){return _lu(_lG,_lJ,_);},_])),_lK=B(A(_kX,[_jb,_iE,_iA,_lG,6,function(_lJ,_){return _lu(_lG,_lJ,_);},_])),_lL=E(_lG),_lM=_jc(_lH,_lL),_lN=E(_ly),_lO=_jc(_lL,_lN),_lP=function(_){if(!E(_lB)){return 0;}else{var _lQ=B(A1(_kz,_)),_lR=_kN(toJSStr(_3V(_46,_lz,__Z))),_lS=E(_lQ),_lT=_jc(_lR,_lS),_lU=_jc(_lS,_lN);return _p(_);}};if(!E(_lD)){return _lP(_);}else{var _lV=B(A(_kX,[_jb,_iE,_iA,_lL,0,_kH,_]));return _lP(_);}};if(!E(_lC)){return _lE(_);}else{var _lW=B(A1(_kL,_)),_lX=_lW,_lY=_kN(toJSStr(E(_kK))),_lZ=B(A(_kX,[_jb,_iE,_iA,_lX,5,function(_lJ,_){return _lu(_lX,_lJ,_);},_])),_m0=B(A(_kX,[_jb,_iE,_iA,_lX,6,function(_lJ,_){return _lu(_lX,_lJ,_);},_])),_m1=E(_lX),_m2=_jc(_lY,_m1),_m3=_jc(_m1,E(_ly));if(!E(_lD)){return _lE(_);}else{var _m4=B(A(_kX,[_jb,_iE,_iA,_m1,0,_kH,_]));return _lE(_);}}},_m5=(function(e){while(e.firstChild){e.removeChild(e.firstChild);}}),_m6=new T(function(){return unCStr("debug");}),_m7=new T(function(){return _en(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:68:5-23");}),__Z,__Z));}),_m8=new T(function(){return unCStr("is");}),_m9=new T2(1,0,new T2(1,0,new T2(1,1,__Z))),_ma=new T(function(){return unCStr("Roman");}),_mb=new T2(1,0,__Z),_mc=new T2(1,0,new T2(1,0,new T2(1,1,_mb))),_md=new T(function(){return unCStr("he");}),_me=new T2(1,0,new T2(1,0,new T2(1,0,_mb))),_mf=(function(e,c) {return e.classList.contains(c);}),_mg=function(_,_mh){var _mi=E(_mh);if(!_mi._){return die(_m7);}else{var _mj=E(_mi.a),_mk=_m5(_mj),_ml=_mf(_mj,toJSStr(E(_m6))),_mm=_ml,_mn=function(_mo,_){while(1){var _mp=E(_mo);if(!_mp._){return 0;}else{var _mq=E(_mp.a),_mr=B(_lx(_mj,_mq.a,_mq.b,_mm,false,false,_));_mo=_mp.b;continue;}}},_ms=_mn(new T2(1,new T2(0,_me,_md),new T2(1,new T2(0,_m9,_m8),new T2(1,new T2(0,_mc,_ma),__Z))),_);return 0;}},_mt=new T(function(){return unCStr("exampleTree");}),_mu=(function(id){return document.getElementById(id);}),_mv=function(_mw,_){var _mx=rMV(_mw),_my=_mu(toJSStr(E(_mt))),_mz=__eq(_my,E(_w));if(!E(_mz)){var _mA=__isUndef(_my);if(!E(_mA)){return _mg(_,new T1(1,_my));}else{return _mg(_,__Z);}}else{return _mg(_,__Z);}},_mB=function(_mC,_mD){if(_mC<=_mD){var _mE=function(_mF){return new T2(1,_mF,new T(function(){if(_mF!=_mD){return _mE(_mF+1|0);}else{return __Z;}}));};return _mE(_mC);}else{return __Z;}},_mG=new T(function(){return _mB(0,2147483647);}),_mH=new T(function(){return _en(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:119:5-24");}),__Z,__Z));}),_mI=new T(function(){return unCStr("exerciseTree");}),_mJ=function(_mK,_){var _mL=rMV(_mK),_mM=_mL,_mN=_mu(toJSStr(E(_mI))),_mO=__eq(_mN,E(_w)),_mP=function(_,_mQ){var _mR=E(_mQ);if(!_mR._){return die(_mH);}else{var _mS=E(_mR.a),_mT=_m5(_mS),_mU=_mf(_mS,toJSStr(E(_m6))),_mV=_mU,_mW=function(_mX,_mY,_){while(1){var _mZ=E(_mX);if(!_mZ._){return 0;}else{var _n0=E(_mY);if(!_n0._){return 0;}else{var _n1=E(_n0.a),_n2=B(_lx(_mS,_n1.a,_n1.b,_mV,true,true,_));_mX=_mZ.b;_mY=_n0.b;continue;}}}},_n3=_mW(_mG,new T(function(){return E(E(_mM).c);},1),_);return 0;}};if(!E(_mO)){var _n4=__isUndef(_mN);if(!E(_n4)){return _mP(_,new T1(1,_mN));}else{return _mP(_,__Z);}}else{return _mP(_,__Z);}},_n5=(function(c,p){p.removeChild(c);}),_n6=new T(function(){return document.body;}),_n7=function(_,_n8){var _n9=E(_n8);if(!_n9._){return 0;}else{var _na=E(_n9.a),_nb=_m5(_na),_nc=_n5(_na,E(_n6));return _p(_);}},_nd=function(_ne,_){var _nf=_mu(toJSStr(E(_ne))),_ng=__eq(_nf,E(_w));if(!E(_ng)){var _nh=__isUndef(_nf);if(!E(_nh)){return _n7(_,new T1(1,_nf));}else{return _n7(_,__Z);}}else{return _n7(_,__Z);}},_ni=new T(function(){return unCStr("menuList");}),_nj=new T(function(){return unCStr("suggestionList");}),_nk=function(_nl,_){var _nm=_nd(_nj,_),_nn=_nd(_ni,_),_no=E(_nl),_np=rMV(_no),_=wMV(_no,new T5(0,new T(function(){return E(E(_np).a);}),new T(function(){return E(E(_np).b);}),new T(function(){return E(E(_np).c);}),__Z,new T(function(){return E(E(_np).e);})));return 0;},_nq=function(_){return _ji("div");},_nr=new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:56:5-14");}),_ns=new T(function(){return unCStr("score");}),_nt=function(_nu,_){var _nv=_mu(toJSStr(E(_ns))),_nw=__eq(_nv,E(_w)),_nx=function(_,_ny){var _nz=E(_ny);if(!_nz._){return _iU(_nr,_);}else{var _nA=rMV(E(_nu)),_nB=E(_nz.a),_nC=_m5(_nB),_nD=_kN(toJSStr(_2r(0,E(E(_nA).e),__Z))),_nE=_jc(_nD,_nB);return _p(_);}};if(!E(_nw)){var _nF=__isUndef(_nv);if(!E(_nF)){return _nx(_,new T1(1,_nv));}else{return _nx(_,__Z);}}else{return _nx(_,__Z);}},_nG=new T2(1,new T2(0,_me,new T(function(){return unCStr("Augustus");})),new T2(1,new T2(0,_mc,new T(function(){return unCStr("laetus");})),new T2(1,new T2(0,_m9,new T(function(){return unCStr("est");})),__Z))),_nH=new T(function(){return unCStr("useS (useCl (simpleCl (usePN Augustus_PN) (complA laetus_A)))");}),_nI=function(_nJ){return fromJSStr(E(_nJ));},_nK=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_nL=function(_nM,_nN,_nO,_nP){var _nQ=new T(function(){var _nR=function(_){var _nS=_nK(B(A2(_jk,_nM,_nO)),E(_nP));return new T(function(){return String(_nS);});};return _nR;});return C > 19 ? new F(function(){return A2(_gc,_nN,_nQ);}) : (++C,A2(_gc,_nN,_nQ));},_nT=function(_nU,_nV,_nW,_nX){var _nY=_df(_nV),_nZ=new T(function(){return _jd(_nY);}),_o0=function(_o1){return C > 19 ? new F(function(){return A1(_nZ,new T(function(){return _nI(_o1);}));}) : (++C,A1(_nZ,new T(function(){return _nI(_o1);})));},_o2=new T(function(){return B(_nL(_nU,_nV,_nW,new T(function(){return toJSStr(E(_nX));},1)));});return C > 19 ? new F(function(){return A3(_1H,_nY,_o2,_o0);}) : (++C,A3(_1H,_nY,_o2,_o0));},_o3=new T(function(){return err(new T(function(){return unCStr("Prelude.read: no parse");}));}),_o4=new T(function(){return err(new T(function(){return unCStr("Prelude.read: ambiguous parse");}));}),_o5=new T(function(){return unCStr("offsetLeft");}),_o6=new T(function(){return B(_7L("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_o7=function(_o8,_o9){while(1){var _oa=(function(_ob,_oc){var _od=E(_ob);switch(_od._){case 0:var _oe=E(_oc);if(!_oe._){return __Z;}else{_o8=B(A1(_od.a,_oe.a));_o9=_oe.b;return __continue;}break;case 1:var _of=B(A1(_od.a,_oc)),_og=_oc;_o8=_of;_o9=_og;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_od.a,_oc),new T(function(){return _o7(_od.b,_oc);}));default:return E(_od.a);}})(_o8,_o9);if(_oa!=__continue){return _oa;}}},_oh=function(_oi,_oj){var _ok=function(_ol){var _om=E(_oj);if(_om._==3){return new T2(3,_om.a,new T(function(){return _oh(_oi,_om.b);}));}else{var _on=E(_oi);if(_on._==2){return _om;}else{if(_om._==2){return _on;}else{var _oo=function(_op){if(_om._==4){var _oq=function(_or){return new T1(4,new T(function(){return _0(_o7(_on,_or),_om.a);}));};return new T1(1,_oq);}else{if(_on._==1){var _os=_on.a;if(!_om._){return new T1(1,function(_ot){return _oh(B(A1(_os,_ot)),_om);});}else{var _ou=function(_ov){return _oh(B(A1(_os,_ov)),new T(function(){return B(A1(_om.a,_ov));}));};return new T1(1,_ou);}}else{if(!_om._){return E(_o6);}else{var _ow=function(_ox){return _oh(_on,new T(function(){return B(A1(_om.a,_ox));}));};return new T1(1,_ow);}}}};switch(_on._){case 1:if(_om._==4){var _oy=function(_oz){return new T1(4,new T(function(){return _0(_o7(B(A1(_on.a,_oz)),_oz),_om.a);}));};return new T1(1,_oy);}else{return _oo(_);}break;case 4:var _oA=_on.a;switch(_om._){case 0:var _oB=function(_oC){var _oD=new T(function(){return _0(_oA,new T(function(){return _o7(_om,_oC);},1));});return new T1(4,_oD);};return new T1(1,_oB);case 1:var _oE=function(_oF){var _oG=new T(function(){return _0(_oA,new T(function(){return _o7(B(A1(_om.a,_oF)),_oF);},1));});return new T1(4,_oG);};return new T1(1,_oE);default:return new T1(4,new T(function(){return _0(_oA,_om.a);}));}break;default:return _oo(_);}}}}},_oH=E(_oi);switch(_oH._){case 0:var _oI=E(_oj);if(!_oI._){var _oJ=function(_oK){return _oh(B(A1(_oH.a,_oK)),new T(function(){return B(A1(_oI.a,_oK));}));};return new T1(0,_oJ);}else{return _ok(_);}break;case 3:return new T2(3,_oH.a,new T(function(){return _oh(_oH.b,_oj);}));default:return _ok(_);}},_oL=new T(function(){return unCStr("(");}),_oM=new T(function(){return unCStr(")");}),_oN=function(_oO,_oP){while(1){var _oQ=E(_oO);if(!_oQ._){return (E(_oP)._==0)?true:false;}else{var _oR=E(_oP);if(!_oR._){return false;}else{if(E(_oQ.a)!=E(_oR.a)){return false;}else{_oO=_oQ.b;_oP=_oR.b;continue;}}}}},_oS=new T2(0,function(_oT,_oU){return E(_oT)==E(_oU);},function(_oV,_oW){return E(_oV)!=E(_oW);}),_oX=function(_oY,_oZ){while(1){var _p0=E(_oY);if(!_p0._){return (E(_oZ)._==0)?true:false;}else{var _p1=E(_oZ);if(!_p1._){return false;}else{if(E(_p0.a)!=E(_p1.a)){return false;}else{_oY=_p0.b;_oZ=_p1.b;continue;}}}}},_p2=function(_p3,_p4){return (!_oX(_p3,_p4))?true:false;},_p5=function(_p6,_p7){var _p8=E(_p6);switch(_p8._){case 0:return new T1(0,function(_p9){return C > 19 ? new F(function(){return _p5(B(A1(_p8.a,_p9)),_p7);}) : (++C,_p5(B(A1(_p8.a,_p9)),_p7));});case 1:return new T1(1,function(_pa){return C > 19 ? new F(function(){return _p5(B(A1(_p8.a,_pa)),_p7);}) : (++C,_p5(B(A1(_p8.a,_pa)),_p7));});case 2:return new T0(2);case 3:return _oh(B(A1(_p7,_p8.a)),new T(function(){return B(_p5(_p8.b,_p7));}));default:var _pb=function(_pc){var _pd=E(_pc);if(!_pd._){return __Z;}else{var _pe=E(_pd.a);return _0(_o7(B(A1(_p7,_pe.a)),_pe.b),new T(function(){return _pb(_pd.b);},1));}},_pf=_pb(_p8.a);return (_pf._==0)?new T0(2):new T1(4,_pf);}},_pg=new T0(2),_ph=function(_pi){return new T2(3,_pi,_pg);},_pj=function(_pk,_pl){var _pm=E(_pk);if(!_pm){return C > 19 ? new F(function(){return A1(_pl,0);}) : (++C,A1(_pl,0));}else{var _pn=new T(function(){return B(_pj(_pm-1|0,_pl));});return new T1(0,function(_po){return E(_pn);});}},_pp=function(_pq,_pr,_ps){var _pt=new T(function(){return B(A1(_pq,_ph));}),_pu=function(_pv,_pw,_px,_py){while(1){var _pz=B((function(_pA,_pB,_pC,_pD){var _pE=E(_pA);switch(_pE._){case 0:var _pF=E(_pB);if(!_pF._){return C > 19 ? new F(function(){return A1(_pr,_pD);}) : (++C,A1(_pr,_pD));}else{var _pG=_pC+1|0,_pH=_pD;_pv=B(A1(_pE.a,_pF.a));_pw=_pF.b;_px=_pG;_py=_pH;return __continue;}break;case 1:var _pI=B(A1(_pE.a,_pB)),_pJ=_pB,_pG=_pC,_pH=_pD;_pv=_pI;_pw=_pJ;_px=_pG;_py=_pH;return __continue;case 2:return C > 19 ? new F(function(){return A1(_pr,_pD);}) : (++C,A1(_pr,_pD));break;case 3:var _pK=new T(function(){return B(_p5(_pE,_pD));});return C > 19 ? new F(function(){return _pj(_pC,function(_pL){return E(_pK);});}) : (++C,_pj(_pC,function(_pL){return E(_pK);}));break;default:return C > 19 ? new F(function(){return _p5(_pE,_pD);}) : (++C,_p5(_pE,_pD));}})(_pv,_pw,_px,_py));if(_pz!=__continue){return _pz;}}};return function(_pM){return _pu(_pt,_pM,0,_ps);};},_pN=function(_pO){return C > 19 ? new F(function(){return A1(_pO,__Z);}) : (++C,A1(_pO,__Z));},_pP=function(_pQ,_pR){var _pS=function(_pT){var _pU=E(_pT);if(!_pU._){return _pN;}else{var _pV=_pU.a;if(!B(A1(_pQ,_pV))){return _pN;}else{var _pW=new T(function(){return _pS(_pU.b);}),_pX=function(_pY){var _pZ=new T(function(){return B(A1(_pW,function(_q0){return C > 19 ? new F(function(){return A1(_pY,new T2(1,_pV,_q0));}) : (++C,A1(_pY,new T2(1,_pV,_q0)));}));});return new T1(0,function(_q1){return E(_pZ);});};return _pX;}}};return function(_q2){return C > 19 ? new F(function(){return A2(_pS,_q2,_pR);}) : (++C,A2(_pS,_q2,_pR));};},_q3=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_q4=function(_q5,_q6){var _q7=function(_q8,_q9){var _qa=E(_q8);if(!_qa._){var _qb=new T(function(){return B(A1(_q9,__Z));});return function(_qc){return C > 19 ? new F(function(){return A1(_qc,_qb);}) : (++C,A1(_qc,_qb));};}else{var _qd=E(_qa.a),_qe=function(_qf){var _qg=new T(function(){return _q7(_qa.b,function(_qh){return C > 19 ? new F(function(){return A1(_q9,new T2(1,_qf,_qh));}) : (++C,A1(_q9,new T2(1,_qf,_qh)));});}),_qi=function(_qj){var _qk=new T(function(){return B(A1(_qg,_qj));});return new T1(0,function(_ql){return E(_qk);});};return _qi;};switch(E(_q5)){case 8:if(48>_qd){var _qm=new T(function(){return B(A1(_q9,__Z));});return function(_qn){return C > 19 ? new F(function(){return A1(_qn,_qm);}) : (++C,A1(_qn,_qm));};}else{if(_qd>55){var _qo=new T(function(){return B(A1(_q9,__Z));});return function(_qp){return C > 19 ? new F(function(){return A1(_qp,_qo);}) : (++C,A1(_qp,_qo));};}else{return _qe(_qd-48|0);}}break;case 10:if(48>_qd){var _qq=new T(function(){return B(A1(_q9,__Z));});return function(_qr){return C > 19 ? new F(function(){return A1(_qr,_qq);}) : (++C,A1(_qr,_qq));};}else{if(_qd>57){var _qs=new T(function(){return B(A1(_q9,__Z));});return function(_qt){return C > 19 ? new F(function(){return A1(_qt,_qs);}) : (++C,A1(_qt,_qs));};}else{return _qe(_qd-48|0);}}break;case 16:if(48>_qd){if(97>_qd){if(65>_qd){var _qu=new T(function(){return B(A1(_q9,__Z));});return function(_qv){return C > 19 ? new F(function(){return A1(_qv,_qu);}) : (++C,A1(_qv,_qu));};}else{if(_qd>70){var _qw=new T(function(){return B(A1(_q9,__Z));});return function(_qx){return C > 19 ? new F(function(){return A1(_qx,_qw);}) : (++C,A1(_qx,_qw));};}else{return _qe((_qd-65|0)+10|0);}}}else{if(_qd>102){if(65>_qd){var _qy=new T(function(){return B(A1(_q9,__Z));});return function(_qz){return C > 19 ? new F(function(){return A1(_qz,_qy);}) : (++C,A1(_qz,_qy));};}else{if(_qd>70){var _qA=new T(function(){return B(A1(_q9,__Z));});return function(_qB){return C > 19 ? new F(function(){return A1(_qB,_qA);}) : (++C,A1(_qB,_qA));};}else{return _qe((_qd-65|0)+10|0);}}}else{return _qe((_qd-97|0)+10|0);}}}else{if(_qd>57){if(97>_qd){if(65>_qd){var _qC=new T(function(){return B(A1(_q9,__Z));});return function(_qD){return C > 19 ? new F(function(){return A1(_qD,_qC);}) : (++C,A1(_qD,_qC));};}else{if(_qd>70){var _qE=new T(function(){return B(A1(_q9,__Z));});return function(_qF){return C > 19 ? new F(function(){return A1(_qF,_qE);}) : (++C,A1(_qF,_qE));};}else{return _qe((_qd-65|0)+10|0);}}}else{if(_qd>102){if(65>_qd){var _qG=new T(function(){return B(A1(_q9,__Z));});return function(_qH){return C > 19 ? new F(function(){return A1(_qH,_qG);}) : (++C,A1(_qH,_qG));};}else{if(_qd>70){var _qI=new T(function(){return B(A1(_q9,__Z));});return function(_qJ){return C > 19 ? new F(function(){return A1(_qJ,_qI);}) : (++C,A1(_qJ,_qI));};}else{return _qe((_qd-65|0)+10|0);}}}else{return _qe((_qd-97|0)+10|0);}}}else{return _qe(_qd-48|0);}}break;default:return E(_q3);}}},_qK=function(_qL){var _qM=E(_qL);if(!_qM._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_q6,_qM);}) : (++C,A1(_q6,_qM));}};return function(_qN){return C > 19 ? new F(function(){return A3(_q7,_qN,_23,_qK);}) : (++C,A3(_q7,_qN,_23,_qK));};},_qO=function(_qP){var _qQ=function(_qR){return C > 19 ? new F(function(){return A1(_qP,new T1(5,new T2(0,8,_qR)));}) : (++C,A1(_qP,new T1(5,new T2(0,8,_qR))));},_qS=function(_qT){return C > 19 ? new F(function(){return A1(_qP,new T1(5,new T2(0,16,_qT)));}) : (++C,A1(_qP,new T1(5,new T2(0,16,_qT))));},_qU=function(_qV){switch(E(_qV)){case 79:return new T1(1,_q4(8,_qQ));case 88:return new T1(1,_q4(16,_qS));case 111:return new T1(1,_q4(8,_qQ));case 120:return new T1(1,_q4(16,_qS));default:return new T0(2);}};return function(_qW){return (E(_qW)==48)?E(new T1(0,_qU)):new T0(2);};},_qX=function(_qY){return new T1(0,_qO(_qY));},_qZ=function(_r0){return C > 19 ? new F(function(){return A1(_r0,__Z);}) : (++C,A1(_r0,__Z));},_r1=function(_r2){return C > 19 ? new F(function(){return A1(_r2,__Z);}) : (++C,A1(_r2,__Z));},_r3=function(_r4,_r5){while(1){var _r6=E(_r4);if(!_r6._){var _r7=_r6.a,_r8=E(_r5);if(!_r8._){var _r9=_r8.a,_ra=addC(_r7,_r9);if(!E(_ra.b)){return new T1(0,_ra.a);}else{_r4=new T1(1,I_fromInt(_r7));_r5=new T1(1,I_fromInt(_r9));continue;}}else{_r4=new T1(1,I_fromInt(_r7));_r5=_r8;continue;}}else{var _rb=E(_r5);if(!_rb._){_r4=_r6;_r5=new T1(1,I_fromInt(_rb.a));continue;}else{return new T1(1,I_add(_r6.a,_rb.a));}}}},_rc=new T(function(){return _r3(new T1(0,2147483647),new T1(0,1));}),_rd=function(_re){var _rf=E(_re);if(!_rf._){var _rg=E(_rf.a);return (_rg==(-2147483648))?E(_rc):new T1(0, -_rg);}else{return new T1(1,I_negate(_rf.a));}},_rh=new T1(0,10),_ri=function(_rj,_rk){while(1){var _rl=E(_rj);if(!_rl._){return E(_rk);}else{var _rm=_rk+1|0;_rj=_rl.b;_rk=_rm;continue;}}},_rn=function(_ro){return new T1(0,_ro);},_rp=function(_rq){return _rn(E(_rq));},_rr=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_rs=function(_rt,_ru){while(1){var _rv=E(_rt);if(!_rv._){var _rw=_rv.a,_rx=E(_ru);if(!_rx._){var _ry=_rx.a;if(!(imul(_rw,_ry)|0)){return new T1(0,imul(_rw,_ry)|0);}else{_rt=new T1(1,I_fromInt(_rw));_ru=new T1(1,I_fromInt(_ry));continue;}}else{_rt=new T1(1,I_fromInt(_rw));_ru=_rx;continue;}}else{var _rz=E(_ru);if(!_rz._){_rt=_rv;_ru=new T1(1,I_fromInt(_rz.a));continue;}else{return new T1(1,I_mul(_rv.a,_rz.a));}}}},_rA=function(_rB,_rC){var _rD=E(_rC);if(!_rD._){return __Z;}else{var _rE=E(_rD.b);return (_rE._==0)?E(_rr):new T2(1,_r3(_rs(_rD.a,_rB),_rE.a),new T(function(){return _rA(_rB,_rE.b);}));}},_rF=new T1(0,0),_rG=function(_rH,_rI,_rJ){while(1){var _rK=(function(_rL,_rM,_rN){var _rO=E(_rN);if(!_rO._){return E(_rF);}else{if(!E(_rO.b)._){return E(_rO.a);}else{var _rP=E(_rM);if(_rP<=40){var _rQ=function(_rR,_rS){while(1){var _rT=E(_rS);if(!_rT._){return E(_rR);}else{var _rU=_r3(_rs(_rR,_rL),_rT.a);_rR=_rU;_rS=_rT.b;continue;}}};return _rQ(_rF,_rO);}else{var _rV=_rs(_rL,_rL);if(!(_rP%2)){var _rW=_rA(_rL,_rO);_rH=_rV;_rI=quot(_rP+1|0,2);_rJ=_rW;return __continue;}else{var _rW=_rA(_rL,new T2(1,_rF,_rO));_rH=_rV;_rI=quot(_rP+1|0,2);_rJ=_rW;return __continue;}}}}})(_rH,_rI,_rJ);if(_rK!=__continue){return _rK;}}},_rX=function(_rY,_rZ){return _rG(_rY,new T(function(){return _ri(_rZ,0);},1),_z(_rp,_rZ));},_s0=function(_s1){var _s2=new T(function(){var _s3=new T(function(){var _s4=function(_s5){return C > 19 ? new F(function(){return A1(_s1,new T1(1,new T(function(){return _rX(_rh,_s5);})));}) : (++C,A1(_s1,new T1(1,new T(function(){return _rX(_rh,_s5);}))));};return new T1(1,_q4(10,_s4));}),_s6=function(_s7){if(E(_s7)==43){var _s8=function(_s9){return C > 19 ? new F(function(){return A1(_s1,new T1(1,new T(function(){return _rX(_rh,_s9);})));}) : (++C,A1(_s1,new T1(1,new T(function(){return _rX(_rh,_s9);}))));};return new T1(1,_q4(10,_s8));}else{return new T0(2);}},_sa=function(_sb){if(E(_sb)==45){var _sc=function(_sd){return C > 19 ? new F(function(){return A1(_s1,new T1(1,new T(function(){return _rd(_rX(_rh,_sd));})));}) : (++C,A1(_s1,new T1(1,new T(function(){return _rd(_rX(_rh,_sd));}))));};return new T1(1,_q4(10,_sc));}else{return new T0(2);}};return _oh(_oh(new T1(0,_sa),new T1(0,_s6)),_s3);});return _oh(new T1(0,function(_se){return (E(_se)==101)?E(_s2):new T0(2);}),new T1(0,function(_sf){return (E(_sf)==69)?E(_s2):new T0(2);}));},_sg=function(_sh){var _si=function(_sj){return C > 19 ? new F(function(){return A1(_sh,new T1(1,_sj));}) : (++C,A1(_sh,new T1(1,_sj)));};return function(_sk){return (E(_sk)==46)?new T1(1,_q4(10,_si)):new T0(2);};},_sl=function(_sm){return new T1(0,_sg(_sm));},_sn=function(_so){var _sp=function(_sq){var _sr=function(_ss){return new T1(1,_pp(_s0,_qZ,function(_st){return C > 19 ? new F(function(){return A1(_so,new T1(5,new T3(1,_sq,_ss,_st)));}) : (++C,A1(_so,new T1(5,new T3(1,_sq,_ss,_st))));}));};return new T1(1,_pp(_sl,_r1,_sr));};return _q4(10,_sp);},_su=function(_sv){return new T1(1,_sn(_sv));},_sw=function(_sx,_sy,_sz){while(1){var _sA=E(_sz);if(!_sA._){return false;}else{if(!B(A3(_6D,_sx,_sy,_sA.a))){_sz=_sA.b;continue;}else{return true;}}}},_sB=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_sC=function(_sD){return _sw(_oS,_sD,_sB);},_sE=function(_sF){var _sG=new T(function(){return B(A1(_sF,8));}),_sH=new T(function(){return B(A1(_sF,16));});return function(_sI){switch(E(_sI)){case 79:return E(_sG);case 88:return E(_sH);case 111:return E(_sG);case 120:return E(_sH);default:return new T0(2);}};},_sJ=function(_sK){return new T1(0,_sE(_sK));},_sL=function(_sM){return C > 19 ? new F(function(){return A1(_sM,10);}) : (++C,A1(_sM,10));},_sN=function(_sO){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _2r(9,_sO,__Z);})));},_sP=function(_sQ){var _sR=E(_sQ);if(!_sR._){return E(_sR.a);}else{return I_toInt(_sR.a);}},_sS=function(_sT,_sU){var _sV=E(_sT);if(!_sV._){var _sW=_sV.a,_sX=E(_sU);return (_sX._==0)?_sW<=_sX.a:I_compareInt(_sX.a,_sW)>=0;}else{var _sY=_sV.a,_sZ=E(_sU);return (_sZ._==0)?I_compareInt(_sY,_sZ.a)<=0:I_compare(_sY,_sZ.a)<=0;}},_t0=function(_t1){return new T0(2);},_t2=function(_t3){var _t4=E(_t3);if(!_t4._){return _t0;}else{var _t5=_t4.a,_t6=E(_t4.b);if(!_t6._){return E(_t5);}else{var _t7=new T(function(){return _t2(_t6);}),_t8=function(_t9){return _oh(B(A1(_t5,_t9)),new T(function(){return B(A1(_t7,_t9));}));};return _t8;}}},_ta=function(_tb,_tc){var _td=function(_te,_tf,_tg){var _th=E(_te);if(!_th._){return C > 19 ? new F(function(){return A1(_tg,_tb);}) : (++C,A1(_tg,_tb));}else{var _ti=E(_tf);if(!_ti._){return new T0(2);}else{if(E(_th.a)!=E(_ti.a)){return new T0(2);}else{var _tj=new T(function(){return B(_td(_th.b,_ti.b,_tg));});return new T1(0,function(_tk){return E(_tj);});}}}};return function(_tl){return C > 19 ? new F(function(){return _td(_tb,_tl,_tc);}) : (++C,_td(_tb,_tl,_tc));};},_tm=new T(function(){return unCStr("SO");}),_tn=function(_to){var _tp=new T(function(){return B(A1(_to,14));});return new T1(1,_ta(_tm,function(_tq){return E(_tp);}));},_tr=new T(function(){return unCStr("SOH");}),_ts=function(_tt){var _tu=new T(function(){return B(A1(_tt,1));});return new T1(1,_ta(_tr,function(_tv){return E(_tu);}));},_tw=new T(function(){return unCStr("NUL");}),_tx=function(_ty){var _tz=new T(function(){return B(A1(_ty,0));});return new T1(1,_ta(_tw,function(_tA){return E(_tz);}));},_tB=new T(function(){return unCStr("STX");}),_tC=function(_tD){var _tE=new T(function(){return B(A1(_tD,2));});return new T1(1,_ta(_tB,function(_tF){return E(_tE);}));},_tG=new T(function(){return unCStr("ETX");}),_tH=function(_tI){var _tJ=new T(function(){return B(A1(_tI,3));});return new T1(1,_ta(_tG,function(_tK){return E(_tJ);}));},_tL=new T(function(){return unCStr("EOT");}),_tM=function(_tN){var _tO=new T(function(){return B(A1(_tN,4));});return new T1(1,_ta(_tL,function(_tP){return E(_tO);}));},_tQ=new T(function(){return unCStr("ENQ");}),_tR=function(_tS){var _tT=new T(function(){return B(A1(_tS,5));});return new T1(1,_ta(_tQ,function(_tU){return E(_tT);}));},_tV=new T(function(){return unCStr("ACK");}),_tW=function(_tX){var _tY=new T(function(){return B(A1(_tX,6));});return new T1(1,_ta(_tV,function(_tZ){return E(_tY);}));},_u0=new T(function(){return unCStr("BEL");}),_u1=function(_u2){var _u3=new T(function(){return B(A1(_u2,7));});return new T1(1,_ta(_u0,function(_u4){return E(_u3);}));},_u5=new T(function(){return unCStr("BS");}),_u6=function(_u7){var _u8=new T(function(){return B(A1(_u7,8));});return new T1(1,_ta(_u5,function(_u9){return E(_u8);}));},_ua=new T(function(){return unCStr("HT");}),_ub=function(_uc){var _ud=new T(function(){return B(A1(_uc,9));});return new T1(1,_ta(_ua,function(_ue){return E(_ud);}));},_uf=new T(function(){return unCStr("LF");}),_ug=function(_uh){var _ui=new T(function(){return B(A1(_uh,10));});return new T1(1,_ta(_uf,function(_uj){return E(_ui);}));},_uk=new T(function(){return unCStr("VT");}),_ul=function(_um){var _un=new T(function(){return B(A1(_um,11));});return new T1(1,_ta(_uk,function(_uo){return E(_un);}));},_up=new T(function(){return unCStr("FF");}),_uq=function(_ur){var _us=new T(function(){return B(A1(_ur,12));});return new T1(1,_ta(_up,function(_ut){return E(_us);}));},_uu=new T(function(){return unCStr("CR");}),_uv=function(_uw){var _ux=new T(function(){return B(A1(_uw,13));});return new T1(1,_ta(_uu,function(_uy){return E(_ux);}));},_uz=new T(function(){return unCStr("SI");}),_uA=function(_uB){var _uC=new T(function(){return B(A1(_uB,15));});return new T1(1,_ta(_uz,function(_uD){return E(_uC);}));},_uE=new T(function(){return unCStr("DLE");}),_uF=function(_uG){var _uH=new T(function(){return B(A1(_uG,16));});return new T1(1,_ta(_uE,function(_uI){return E(_uH);}));},_uJ=new T(function(){return unCStr("DC1");}),_uK=function(_uL){var _uM=new T(function(){return B(A1(_uL,17));});return new T1(1,_ta(_uJ,function(_uN){return E(_uM);}));},_uO=new T(function(){return unCStr("DC2");}),_uP=function(_uQ){var _uR=new T(function(){return B(A1(_uQ,18));});return new T1(1,_ta(_uO,function(_uS){return E(_uR);}));},_uT=new T(function(){return unCStr("DC3");}),_uU=function(_uV){var _uW=new T(function(){return B(A1(_uV,19));});return new T1(1,_ta(_uT,function(_uX){return E(_uW);}));},_uY=new T(function(){return unCStr("DC4");}),_uZ=function(_v0){var _v1=new T(function(){return B(A1(_v0,20));});return new T1(1,_ta(_uY,function(_v2){return E(_v1);}));},_v3=new T(function(){return unCStr("NAK");}),_v4=function(_v5){var _v6=new T(function(){return B(A1(_v5,21));});return new T1(1,_ta(_v3,function(_v7){return E(_v6);}));},_v8=new T(function(){return unCStr("SYN");}),_v9=function(_va){var _vb=new T(function(){return B(A1(_va,22));});return new T1(1,_ta(_v8,function(_vc){return E(_vb);}));},_vd=new T(function(){return unCStr("ETB");}),_ve=function(_vf){var _vg=new T(function(){return B(A1(_vf,23));});return new T1(1,_ta(_vd,function(_vh){return E(_vg);}));},_vi=new T(function(){return unCStr("CAN");}),_vj=function(_vk){var _vl=new T(function(){return B(A1(_vk,24));});return new T1(1,_ta(_vi,function(_vm){return E(_vl);}));},_vn=new T(function(){return unCStr("EM");}),_vo=function(_vp){var _vq=new T(function(){return B(A1(_vp,25));});return new T1(1,_ta(_vn,function(_vr){return E(_vq);}));},_vs=new T(function(){return unCStr("SUB");}),_vt=function(_vu){var _vv=new T(function(){return B(A1(_vu,26));});return new T1(1,_ta(_vs,function(_vw){return E(_vv);}));},_vx=new T(function(){return unCStr("ESC");}),_vy=function(_vz){var _vA=new T(function(){return B(A1(_vz,27));});return new T1(1,_ta(_vx,function(_vB){return E(_vA);}));},_vC=new T(function(){return unCStr("FS");}),_vD=function(_vE){var _vF=new T(function(){return B(A1(_vE,28));});return new T1(1,_ta(_vC,function(_vG){return E(_vF);}));},_vH=new T(function(){return unCStr("GS");}),_vI=function(_vJ){var _vK=new T(function(){return B(A1(_vJ,29));});return new T1(1,_ta(_vH,function(_vL){return E(_vK);}));},_vM=new T(function(){return unCStr("RS");}),_vN=function(_vO){var _vP=new T(function(){return B(A1(_vO,30));});return new T1(1,_ta(_vM,function(_vQ){return E(_vP);}));},_vR=new T(function(){return unCStr("US");}),_vS=function(_vT){var _vU=new T(function(){return B(A1(_vT,31));});return new T1(1,_ta(_vR,function(_vV){return E(_vU);}));},_vW=new T(function(){return unCStr("SP");}),_vX=function(_vY){var _vZ=new T(function(){return B(A1(_vY,32));});return new T1(1,_ta(_vW,function(_w0){return E(_vZ);}));},_w1=new T(function(){return unCStr("DEL");}),_w2=function(_w3){var _w4=new T(function(){return B(A1(_w3,127));});return new T1(1,_ta(_w1,function(_w5){return E(_w4);}));},_w6=new T(function(){return _t2(new T2(1,function(_w7){return new T1(1,_pp(_ts,_tn,_w7));},new T2(1,_tx,new T2(1,_tC,new T2(1,_tH,new T2(1,_tM,new T2(1,_tR,new T2(1,_tW,new T2(1,_u1,new T2(1,_u6,new T2(1,_ub,new T2(1,_ug,new T2(1,_ul,new T2(1,_uq,new T2(1,_uv,new T2(1,_uA,new T2(1,_uF,new T2(1,_uK,new T2(1,_uP,new T2(1,_uU,new T2(1,_uZ,new T2(1,_v4,new T2(1,_v9,new T2(1,_ve,new T2(1,_vj,new T2(1,_vo,new T2(1,_vt,new T2(1,_vy,new T2(1,_vD,new T2(1,_vI,new T2(1,_vN,new T2(1,_vS,new T2(1,_vX,new T2(1,_w2,__Z))))))))))))))))))))))))))))))))));}),_w8=function(_w9){var _wa=new T(function(){return B(A1(_w9,7));}),_wb=new T(function(){return B(A1(_w9,8));}),_wc=new T(function(){return B(A1(_w9,9));}),_wd=new T(function(){return B(A1(_w9,10));}),_we=new T(function(){return B(A1(_w9,11));}),_wf=new T(function(){return B(A1(_w9,12));}),_wg=new T(function(){return B(A1(_w9,13));}),_wh=new T(function(){return B(A1(_w9,92));}),_wi=new T(function(){return B(A1(_w9,39));}),_wj=new T(function(){return B(A1(_w9,34));}),_wk=new T(function(){var _wl=function(_wm){var _wn=new T(function(){return _rn(E(_wm));}),_wo=function(_wp){var _wq=_rX(_wn,_wp);if(!_sS(_wq,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_w9,new T(function(){var _wr=_sP(_wq);if(_wr>>>0>1114111){return _sN(_wr);}else{return _wr;}}));}) : (++C,A1(_w9,new T(function(){var _wr=_sP(_wq);if(_wr>>>0>1114111){return _sN(_wr);}else{return _wr;}})));}};return new T1(1,_q4(_wm,_wo));},_ws=new T(function(){var _wt=new T(function(){return B(A1(_w9,31));}),_wu=new T(function(){return B(A1(_w9,30));}),_wv=new T(function(){return B(A1(_w9,29));}),_ww=new T(function(){return B(A1(_w9,28));}),_wx=new T(function(){return B(A1(_w9,27));}),_wy=new T(function(){return B(A1(_w9,26));}),_wz=new T(function(){return B(A1(_w9,25));}),_wA=new T(function(){return B(A1(_w9,24));}),_wB=new T(function(){return B(A1(_w9,23));}),_wC=new T(function(){return B(A1(_w9,22));}),_wD=new T(function(){return B(A1(_w9,21));}),_wE=new T(function(){return B(A1(_w9,20));}),_wF=new T(function(){return B(A1(_w9,19));}),_wG=new T(function(){return B(A1(_w9,18));}),_wH=new T(function(){return B(A1(_w9,17));}),_wI=new T(function(){return B(A1(_w9,16));}),_wJ=new T(function(){return B(A1(_w9,15));}),_wK=new T(function(){return B(A1(_w9,14));}),_wL=new T(function(){return B(A1(_w9,6));}),_wM=new T(function(){return B(A1(_w9,5));}),_wN=new T(function(){return B(A1(_w9,4));}),_wO=new T(function(){return B(A1(_w9,3));}),_wP=new T(function(){return B(A1(_w9,2));}),_wQ=new T(function(){return B(A1(_w9,1));}),_wR=new T(function(){return B(A1(_w9,0));}),_wS=function(_wT){switch(E(_wT)){case 64:return E(_wR);case 65:return E(_wQ);case 66:return E(_wP);case 67:return E(_wO);case 68:return E(_wN);case 69:return E(_wM);case 70:return E(_wL);case 71:return E(_wa);case 72:return E(_wb);case 73:return E(_wc);case 74:return E(_wd);case 75:return E(_we);case 76:return E(_wf);case 77:return E(_wg);case 78:return E(_wK);case 79:return E(_wJ);case 80:return E(_wI);case 81:return E(_wH);case 82:return E(_wG);case 83:return E(_wF);case 84:return E(_wE);case 85:return E(_wD);case 86:return E(_wC);case 87:return E(_wB);case 88:return E(_wA);case 89:return E(_wz);case 90:return E(_wy);case 91:return E(_wx);case 92:return E(_ww);case 93:return E(_wv);case 94:return E(_wu);case 95:return E(_wt);default:return new T0(2);}};return _oh(new T1(0,function(_wU){return (E(_wU)==94)?E(new T1(0,_wS)):new T0(2);}),new T(function(){return B(A1(_w6,_w9));}));});return _oh(new T1(1,_pp(_sJ,_sL,_wl)),_ws);});return _oh(new T1(0,function(_wV){switch(E(_wV)){case 34:return E(_wj);case 39:return E(_wi);case 92:return E(_wh);case 97:return E(_wa);case 98:return E(_wb);case 102:return E(_wf);case 110:return E(_wd);case 114:return E(_wg);case 116:return E(_wc);case 118:return E(_we);default:return new T0(2);}}),_wk);},_wW=function(_wX){return C > 19 ? new F(function(){return A1(_wX,0);}) : (++C,A1(_wX,0));},_wY=function(_wZ){var _x0=E(_wZ);if(!_x0._){return _wW;}else{var _x1=E(_x0.a),_x2=_x1>>>0,_x3=new T(function(){return _wY(_x0.b);});if(_x2>887){var _x4=u_iswspace(_x1);if(!E(_x4)){return _wW;}else{var _x5=function(_x6){var _x7=new T(function(){return B(A1(_x3,_x6));});return new T1(0,function(_x8){return E(_x7);});};return _x5;}}else{if(_x2==32){var _x9=function(_xa){var _xb=new T(function(){return B(A1(_x3,_xa));});return new T1(0,function(_xc){return E(_xb);});};return _x9;}else{if(_x2-9>>>0>4){if(_x2==160){var _xd=function(_xe){var _xf=new T(function(){return B(A1(_x3,_xe));});return new T1(0,function(_xg){return E(_xf);});};return _xd;}else{return _wW;}}else{var _xh=function(_xi){var _xj=new T(function(){return B(A1(_x3,_xi));});return new T1(0,function(_xk){return E(_xj);});};return _xh;}}}}},_xl=function(_xm){var _xn=new T(function(){return B(_xl(_xm));}),_xo=function(_xp){return (E(_xp)==92)?E(_xn):new T0(2);},_xq=function(_xr){return E(new T1(0,_xo));},_xs=new T1(1,function(_xt){return C > 19 ? new F(function(){return A2(_wY,_xt,_xq);}) : (++C,A2(_wY,_xt,_xq));}),_xu=new T(function(){return B(_w8(function(_xv){return C > 19 ? new F(function(){return A1(_xm,new T2(0,_xv,true));}) : (++C,A1(_xm,new T2(0,_xv,true)));}));}),_xw=function(_xx){var _xy=E(_xx);if(_xy==38){return E(_xn);}else{var _xz=_xy>>>0;if(_xz>887){var _xA=u_iswspace(_xy);return (E(_xA)==0)?new T0(2):E(_xs);}else{return (_xz==32)?E(_xs):(_xz-9>>>0>4)?(_xz==160)?E(_xs):new T0(2):E(_xs);}}};return _oh(new T1(0,function(_xB){return (E(_xB)==92)?E(new T1(0,_xw)):new T0(2);}),new T1(0,function(_xC){var _xD=E(_xC);if(_xD==92){return E(_xu);}else{return C > 19 ? new F(function(){return A1(_xm,new T2(0,_xD,false));}) : (++C,A1(_xm,new T2(0,_xD,false)));}}));},_xE=function(_xF,_xG){var _xH=new T(function(){return B(A1(_xG,new T1(1,new T(function(){return B(A1(_xF,__Z));}))));}),_xI=function(_xJ){var _xK=E(_xJ),_xL=E(_xK.a);if(_xL==34){if(!E(_xK.b)){return E(_xH);}else{return C > 19 ? new F(function(){return _xE(function(_xM){return C > 19 ? new F(function(){return A1(_xF,new T2(1,_xL,_xM));}) : (++C,A1(_xF,new T2(1,_xL,_xM)));},_xG);}) : (++C,_xE(function(_xM){return C > 19 ? new F(function(){return A1(_xF,new T2(1,_xL,_xM));}) : (++C,A1(_xF,new T2(1,_xL,_xM)));},_xG));}}else{return C > 19 ? new F(function(){return _xE(function(_xN){return C > 19 ? new F(function(){return A1(_xF,new T2(1,_xL,_xN));}) : (++C,A1(_xF,new T2(1,_xL,_xN)));},_xG);}) : (++C,_xE(function(_xN){return C > 19 ? new F(function(){return A1(_xF,new T2(1,_xL,_xN));}) : (++C,A1(_xF,new T2(1,_xL,_xN)));},_xG));}};return C > 19 ? new F(function(){return _xl(_xI);}) : (++C,_xl(_xI));},_xO=new T(function(){return unCStr("_\'");}),_xP=function(_xQ){var _xR=u_iswalnum(_xQ);if(!E(_xR)){return _sw(_oS,_xQ,_xO);}else{return true;}},_xS=function(_xT){return _xP(E(_xT));},_xU=new T(function(){return unCStr(",;()[]{}`");}),_xV=new T(function(){return unCStr("=>");}),_xW=new T(function(){return unCStr("~");}),_xX=new T(function(){return unCStr("@");}),_xY=new T(function(){return unCStr("->");}),_xZ=new T(function(){return unCStr("<-");}),_y0=new T(function(){return unCStr("|");}),_y1=new T(function(){return unCStr("\\");}),_y2=new T(function(){return unCStr("=");}),_y3=new T(function(){return unCStr("::");}),_y4=new T(function(){return unCStr("..");}),_y5=function(_y6){var _y7=new T(function(){return B(A1(_y6,new T0(6)));}),_y8=new T(function(){var _y9=new T(function(){var _ya=function(_yb){var _yc=new T(function(){return B(A1(_y6,new T1(0,_yb)));});return new T1(0,function(_yd){return (E(_yd)==39)?E(_yc):new T0(2);});};return B(_w8(_ya));}),_ye=function(_yf){var _yg=E(_yf);switch(_yg){case 39:return new T0(2);case 92:return E(_y9);default:var _yh=new T(function(){return B(A1(_y6,new T1(0,_yg)));});return new T1(0,function(_yi){return (E(_yi)==39)?E(_yh):new T0(2);});}},_yj=new T(function(){var _yk=new T(function(){return B(_xE(_23,_y6));}),_yl=new T(function(){var _ym=new T(function(){var _yn=new T(function(){var _yo=function(_yp){var _yq=E(_yp),_yr=u_iswalpha(_yq);return (E(_yr)==0)?(_yq==95)?new T1(1,_pP(_xS,function(_ys){return C > 19 ? new F(function(){return A1(_y6,new T1(3,new T2(1,_yq,_ys)));}) : (++C,A1(_y6,new T1(3,new T2(1,_yq,_ys))));})):new T0(2):new T1(1,_pP(_xS,function(_yt){return C > 19 ? new F(function(){return A1(_y6,new T1(3,new T2(1,_yq,_yt)));}) : (++C,A1(_y6,new T1(3,new T2(1,_yq,_yt))));}));};return _oh(new T1(0,_yo),new T(function(){return new T1(1,_pp(_qX,_su,_y6));}));}),_yu=function(_yv){return (!_sw(_oS,_yv,_sB))?new T0(2):new T1(1,_pP(_sC,function(_yw){var _yx=new T2(1,_yv,_yw);if(!_sw(new T2(0,_oX,_p2),_yx,new T2(1,_y4,new T2(1,_y3,new T2(1,_y2,new T2(1,_y1,new T2(1,_y0,new T2(1,_xZ,new T2(1,_xY,new T2(1,_xX,new T2(1,_xW,new T2(1,_xV,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_y6,new T1(4,_yx));}) : (++C,A1(_y6,new T1(4,_yx)));}else{return C > 19 ? new F(function(){return A1(_y6,new T1(2,_yx));}) : (++C,A1(_y6,new T1(2,_yx)));}}));};return _oh(new T1(0,_yu),_yn);});return _oh(new T1(0,function(_yy){if(!_sw(_oS,_yy,_xU)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_y6,new T1(2,new T2(1,_yy,__Z)));}) : (++C,A1(_y6,new T1(2,new T2(1,_yy,__Z))));}}),_ym);});return _oh(new T1(0,function(_yz){return (E(_yz)==34)?E(_yk):new T0(2);}),_yl);});return _oh(new T1(0,function(_yA){return (E(_yA)==39)?E(new T1(0,_ye)):new T0(2);}),_yj);});return _oh(new T1(1,function(_yB){return (E(_yB)._==0)?E(_y7):new T0(2);}),_y8);},_yC=function(_yD,_yE){var _yF=new T(function(){var _yG=new T(function(){var _yH=function(_yI){var _yJ=new T(function(){var _yK=new T(function(){return B(A1(_yE,_yI));});return B(_y5(function(_yL){var _yM=E(_yL);return (_yM._==2)?(!_oN(_yM.a,_oM))?new T0(2):E(_yK):new T0(2);}));}),_yN=function(_yO){return E(_yJ);};return new T1(1,function(_yP){return C > 19 ? new F(function(){return A2(_wY,_yP,_yN);}) : (++C,A2(_wY,_yP,_yN));});};return B(A2(_yD,0,_yH));});return B(_y5(function(_yQ){var _yR=E(_yQ);return (_yR._==2)?(!_oN(_yR.a,_oL))?new T0(2):E(_yG):new T0(2);}));}),_yS=function(_yT){return E(_yF);};return function(_yU){return C > 19 ? new F(function(){return A2(_wY,_yU,_yS);}) : (++C,A2(_wY,_yU,_yS));};},_yV=function(_yW,_yX){var _yY=function(_yZ){var _z0=new T(function(){return B(A1(_yW,_yZ));}),_z1=function(_z2){return _oh(B(A1(_z0,_z2)),new T(function(){return new T1(1,_yC(_yY,_z2));}));};return _z1;},_z3=new T(function(){return B(A1(_yW,_yX));}),_z4=function(_z5){return _oh(B(A1(_z3,_z5)),new T(function(){return new T1(1,_yC(_yY,_z5));}));};return _z4;},_z6=function(_z7,_z8){var _z9=function(_za,_zb){var _zc=function(_zd){return C > 19 ? new F(function(){return A1(_zb,new T(function(){return  -E(_zd);}));}) : (++C,A1(_zb,new T(function(){return  -E(_zd);})));},_ze=new T(function(){return B(_y5(function(_zf){return C > 19 ? new F(function(){return A3(_z7,_zf,_za,_zc);}) : (++C,A3(_z7,_zf,_za,_zc));}));}),_zg=function(_zh){return E(_ze);},_zi=function(_zj){return C > 19 ? new F(function(){return A2(_wY,_zj,_zg);}) : (++C,A2(_wY,_zj,_zg));},_zk=new T(function(){return B(_y5(function(_zl){var _zm=E(_zl);if(_zm._==4){var _zn=E(_zm.a);if(!_zn._){return C > 19 ? new F(function(){return A3(_z7,_zm,_za,_zb);}) : (++C,A3(_z7,_zm,_za,_zb));}else{if(E(_zn.a)==45){if(!E(_zn.b)._){return E(new T1(1,_zi));}else{return C > 19 ? new F(function(){return A3(_z7,_zm,_za,_zb);}) : (++C,A3(_z7,_zm,_za,_zb));}}else{return C > 19 ? new F(function(){return A3(_z7,_zm,_za,_zb);}) : (++C,A3(_z7,_zm,_za,_zb));}}}else{return C > 19 ? new F(function(){return A3(_z7,_zm,_za,_zb);}) : (++C,A3(_z7,_zm,_za,_zb));}}));}),_zo=function(_zp){return E(_zk);};return new T1(1,function(_zq){return C > 19 ? new F(function(){return A2(_wY,_zq,_zo);}) : (++C,A2(_wY,_zq,_zo));});};return _yV(_z9,_z8);},_zr=function(_zs){var _zt=E(_zs);if(!_zt._){var _zu=_zt.b,_zv=new T(function(){return _rG(new T(function(){return _rn(E(_zt.a));}),new T(function(){return _ri(_zu,0);},1),_z(_rp,_zu));});return new T1(1,_zv);}else{return (E(_zt.b)._==0)?(E(_zt.c)._==0)?new T1(1,new T(function(){return _rX(_rh,_zt.a);})):__Z:__Z;}},_zw=function(_zx,_zy){return new T0(2);},_zz=function(_zA){var _zB=E(_zA);if(_zB._==5){var _zC=_zr(_zB.a);if(!_zC._){return _zw;}else{var _zD=new T(function(){return _sP(_zC.a);});return function(_zE,_zF){return C > 19 ? new F(function(){return A1(_zF,_zD);}) : (++C,A1(_zF,_zD));};}}else{return _zw;}},_zG=function(_zH){var _zI=function(_zJ){return E(new T2(3,_zH,_pg));};return new T1(1,function(_zK){return C > 19 ? new F(function(){return A2(_wY,_zK,_zI);}) : (++C,A2(_wY,_zK,_zI));});},_zL=new T(function(){return B(A3(_z6,_zz,0,_zG));}),_zM=new T(function(){return unCStr("offsetTop");}),_zN=new T(function(){return new T2(0,E(new T1(2,"id")),"menuList");}),_zO=new T(function(){return new T2(0,E(new T1(2,"class")),"menu");}),_zP=new T(function(){return new T1(1,"top");}),_zQ=new T(function(){return new T1(1,"left");}),_zR=new T(function(){return unCStr("Toggle Debug");}),_zS=new T(function(){return unCStr("Reset");}),_zT=new T(function(){return _en(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:206:51-57");}),__Z,__Z));}),_zU=new T(function(){return _en(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:206:87-93");}),__Z,__Z));}),_zV=new T(function(){return unCStr("px");}),_zW=new T(function(){return unCStr("menuHover");}),_zX=function(_zY,_){var _zZ=_lp(_zY,toJSStr(E(_zW)));return _p(_);},_A0=new T(function(){return unCStr("div");}),_A1=function(_A2,_A3,_A4,_){var _A5=_kN(toJSStr(E(_A3))),_A6=_ji(toJSStr(E(_A0))),_A7=_A6,_A8=B(A(_kX,[_jb,_iE,_iA,_A7,5,function(_A9,_){return _zX(_A7,_);},_])),_Aa=B(A(_kX,[_jb,_iE,_iA,_A7,6,function(_Ab,_){return _zX(_A7,_);},_])),_Ac=B(A(_kX,[_jb,_iE,_iA,_A7,0,_A4,_])),_Ad=_jc(_A5,_A7),_Ae=_jc(_A7,E(_A2));return 0;},_Af=function(_Ag){while(1){var _Ah=(function(_Ai){var _Aj=E(_Ai);if(!_Aj._){return __Z;}else{var _Ak=_Aj.b,_Al=E(_Aj.a);if(!E(_Al.b)._){return new T2(1,_Al.a,new T(function(){return _Af(_Ak);}));}else{_Ag=_Ak;return __continue;}}})(_Ag);if(_Ah!=__continue){return _Ah;}}},_Am=function(_An,_Ao,_){var _Ap=_kC(_),_Aq=B(A(_nT,[_jf,_iZ,_An,_o5,_])),_Ar=B(A(_nT,[_jf,_iZ,_An,_zM,_])),_As=_nd(_ni,_),_At=B(A(_kr,[_jf,_iZ,_nq,new T2(1,_zN,new T2(1,_zO,new T2(1,new T(function(){return new T2(0,E(_zP),toJSStr(_0(_Ar,_zV)));}),new T2(1,new T(function(){var _Au=_Af(_o7(_zL,_Aq));if(!_Au._){return E(_o3);}else{if(!E(_Au.b)._){return new T2(0,E(_zQ),toJSStr(_0(_2r(0,E(_Au.a)-200|0,__Z),_zV)));}else{return E(_o4);}}}),__Z)))),_])),_Av=function(_Aw,_){var _Ax=_mu(toJSStr(E(_mt))),_Ay=E(_w),_Az=__eq(_Ax,_Ay),_AA=function(_,_AB){var _AC=E(_AB);if(!_AC._){return die(_zT);}else{var _AD=_mu(toJSStr(E(_mI))),_AE=__eq(_AD,_Ay),_AF=function(_,_AG){var _AH=E(_AG);if(!_AH._){return die(_zU);}else{var _AI=toJSStr(E(_m6)),_AJ=_lp(E(_AC.a),_AI),_AK=_lp(E(_AH.a),_AI),_AL=E(_Ao),_AM=_mJ(_AL,_);return _mv(_AL,_);}};if(!E(_AE)){var _AN=__isUndef(_AD);if(!E(_AN)){return C > 19 ? new F(function(){return _AF(_,new T1(1,_AD));}) : (++C,_AF(_,new T1(1,_AD)));}else{return C > 19 ? new F(function(){return _AF(_,__Z);}) : (++C,_AF(_,__Z));}}else{return C > 19 ? new F(function(){return _AF(_,__Z);}) : (++C,_AF(_,__Z));}}};if(!E(_Az)){var _AO=__isUndef(_Ax);if(!E(_AO)){return C > 19 ? new F(function(){return _AA(_,new T1(1,_Ax));}) : (++C,_AA(_,new T1(1,_Ax)));}else{return C > 19 ? new F(function(){return _AA(_,__Z);}) : (++C,_AA(_,__Z));}}else{return C > 19 ? new F(function(){return _AA(_,__Z);}) : (++C,_AA(_,__Z));}},_AP=_A1(_At,_zR,_Av,_),_AQ=E(_Ao),_AR=rMV(_AQ),_AS=nMV(new T5(0,new T(function(){return E(E(_AR).a);}),_nH,_nG,__Z,0)),_AT=_AS,_AU=_A1(_At,_zS,function(_AV,_){var _AW=_mJ(_AT,_),_AX=B(_nt(_AT,_)),_AY=rMV(_AT),_=wMV(_AQ,_AY);return 0;},_),_AZ=_jc(E(_At),E(_n6));return 0;},_B0=new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:43:5-13");}),_B1=function(_B2,_){var _B3=B(A(_kX,[_jb,_iE,_iA,_n6,0,function(_B4,_){return _nk(_B2,_);},_])),_B5=_mu("menuButton"),_B6=__eq(_B5,E(_w)),_B7=function(_,_B8){var _B9=E(_B8);if(!_B9._){return _iU(_B0,_);}else{var _Ba=_B9.a,_Bb=B(A(_kX,[_jb,_iE,_iA,_Ba,0,function(_Bc,_){return _Am(_Ba,_B2,_);},_])),_Bd=_hs("Draw example tree"),_Be=E(_B2),_Bf=_mv(_Be,_),_Bg=_hs("Draw exercise tree"),_Bh=_mJ(_Be,_);return 0;}};if(!E(_B6)){var _Bi=__isUndef(_B5);if(!E(_Bi)){return _B7(_,new T1(1,_B5));}else{return _B7(_,__Z);}}else{return _B7(_,__Z);}},_Bj=new T(function(){return unCStr("PrimaLat");}),_Bk=function(_){var _Bl=nMV(new T5(0,_Bj,_nH,_nG,__Z,0)),_Bm=B(_B1(_Bl,_));return _gj;},_Bn=new T(function(){return B(A2(_ht,new T3(1,0,new T2(0,new T(function(){return unCStr("PrimaEng");}),new T(function(){return unCStr("(useS (useCl (simpleCl (usePron he_PP) (complA Romanus_A))))");})),new T2(0,_Bj,_nH)),function(_Bo){return E(new T1(0,_Bk));}));}),_Bp=function(_){var _Bq=_a(_Bn,__Z,_);return 0;},_Br=function(_){return _Bp(_);};
var hasteMain = function() {B(A(_Br, [0]));};window.onload = hasteMain;