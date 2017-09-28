"use strict";
var __haste_prog_id = 'cd2f156e086bfa41d4b41a28c092576cb8288a2bf00224b0ba00e3794a7b8529';
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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return _0(_3.b,_2);}));},_4=function(_5,_){while(1){var _6=E(_5);if(!_6._){return 0;}else{var _7=_6.b,_8=E(_6.a);switch(_8._){case 0:var _9=B(A1(_8.a,_));_5=_0(_7,new T2(1,_9,__Z));continue;case 1:_5=_0(_7,_8.a);continue;default:_5=_7;continue;}}}},_a=function(_b,_c,_){var _d=E(_b);switch(_d._){case 0:var _e=B(A1(_d.a,_));return _4(_0(_c,new T2(1,_e,__Z)),_);case 1:return _4(_0(_c,_d.a),_);default:return _4(_c,_);}},_f=new T(function(){return toJSStr(__Z);}),_g=function(_h){return E(_f);},_i=function(_j,_){var _k=E(_j);if(!_k._){return __Z;}else{var _l=_i(_k.b,_);return new T2(1,new T(function(){return String(E(_k.a));}),_l);}},_m=function(_n,_){var _o=__arr2lst(0,_n);return _i(_o,_);},_p=function(_q){return String(E(_q));},_r=function(_s){return _p(_s);},_t=function(_u,_){return new T(function(){return _r(_u);});},_v=new T4(0,new T2(0,function(_w){return E(_w);},function(_x){return __lst2arr(E(_x));}),new T2(0,_t,function(_y,_){return _m(E(_y),_);}),_g,_g),_z=function(_A,_B,_C){var _D=function(_E){var _F=new T(function(){return B(A1(_C,_E));});return C > 19 ? new F(function(){return A1(_B,function(_G){return E(_F);});}) : (++C,A1(_B,function(_G){return E(_F);}));};return C > 19 ? new F(function(){return A1(_A,_D);}) : (++C,A1(_A,_D));},_H=function(_I,_J,_K){var _L=new T(function(){return B(A1(_J,function(_M){return C > 19 ? new F(function(){return A1(_K,_M);}) : (++C,A1(_K,_M));}));});return C > 19 ? new F(function(){return A1(_I,function(_N){return E(_L);});}) : (++C,A1(_I,function(_N){return E(_L);}));},_O=function(_P,_Q,_R){var _S=function(_T){var _U=function(_V){return C > 19 ? new F(function(){return A1(_R,new T(function(){return B(A1(_T,_V));}));}) : (++C,A1(_R,new T(function(){return B(A1(_T,_V));})));};return C > 19 ? new F(function(){return A1(_Q,_U);}) : (++C,A1(_Q,_U));};return C > 19 ? new F(function(){return A1(_P,_S);}) : (++C,A1(_P,_S));},_W=function(_X,_Y){return C > 19 ? new F(function(){return A1(_Y,_X);}) : (++C,A1(_Y,_X));},_Z=function(_10,_11,_12){var _13=new T(function(){return B(A1(_12,_10));});return C > 19 ? new F(function(){return A1(_11,function(_14){return E(_13);});}) : (++C,A1(_11,function(_14){return E(_13);}));},_15=function(_16,_17,_18){var _19=function(_1a){return C > 19 ? new F(function(){return A1(_18,new T(function(){return B(A1(_16,_1a));}));}) : (++C,A1(_18,new T(function(){return B(A1(_16,_1a));})));};return C > 19 ? new F(function(){return A1(_17,_19);}) : (++C,A1(_17,_19));},_1b=function(_1c,_1d,_1e){return C > 19 ? new F(function(){return A1(_1c,function(_1f){return C > 19 ? new F(function(){return A2(_1d,_1f,_1e);}) : (++C,A2(_1d,_1f,_1e));});}) : (++C,A1(_1c,function(_1f){return C > 19 ? new F(function(){return A2(_1d,_1f,_1e);}) : (++C,A2(_1d,_1f,_1e));}));},_1g=function(_1h){return E(E(_1h).b);},_1i=function(_1j,_1k){return C > 19 ? new F(function(){return A3(_1g,_1l,_1j,function(_1m){return E(_1k);});}) : (++C,A3(_1g,_1l,_1j,function(_1m){return E(_1k);}));},_1l=new T(function(){return new T5(0,new T5(0,new T2(0,_15,_Z),_W,_O,_H,_z),_1b,_1i,_W,function(_1n){return err(_1n);});}),_1o=function(_1p,_1q,_){var _1r=B(A1(_1q,_));return new T(function(){return B(A1(_1p,_1r));});},_1s=function(_1t,_1u){return new T1(0,function(_){return _1o(_1u,_1t,_);});},_1v=function(_1w){return new T0(2);},_1x=function(_1y){var _1z=new T(function(){return B(A1(_1y,_1v));}),_1A=function(_1B){return new T1(1,new T2(1,new T(function(){return B(A1(_1B,0));}),new T2(1,_1z,__Z)));};return _1A;},_1C=function(_1D){return E(_1D);},_1E=new T3(0,new T2(0,_1l,_1s),_1C,_1x),_1F=function(_1G){return E(E(_1G).a);},_1H=function(_1I,_1J){var _1K=strEq(E(_1I),E(_1J));return (E(_1K)==0)?false:true;},_1L=new T(function(){return new T2(0,function(_1M,_1N){return _1H(_1M,_1N);},function(_1O,_1P){return (!B(A3(_1F,_1L,_1O,_1P)))?true:false;});}),_1Q=function(_1R,_1S){if(_1R<=_1S){var _1T=function(_1U){return new T2(1,_1U,new T(function(){if(_1U!=_1S){return _1T(_1U+1|0);}else{return __Z;}}));};return _1T(_1R);}else{return __Z;}},_1V=function(_1W,_1X,_1Y){if(_1Y<=_1X){var _1Z=new T(function(){var _20=_1X-_1W|0,_21=function(_22){return (_22>=(_1Y-_20|0))?new T2(1,_22,new T(function(){return _21(_22+_20|0);})):new T2(1,_22,__Z);};return _21(_1X);});return new T2(1,_1W,_1Z);}else{return (_1Y<=_1W)?new T2(1,_1W,__Z):__Z;}},_23=function(_24,_25,_26){if(_26>=_25){var _27=new T(function(){var _28=_25-_24|0,_29=function(_2a){return (_2a<=(_26-_28|0))?new T2(1,_2a,new T(function(){return _29(_2a+_28|0);})):new T2(1,_2a,__Z);};return _29(_25);});return new T2(1,_24,_27);}else{return (_26>=_24)?new T2(1,_24,__Z):__Z;}},_2b=function(_2c,_2d){if(_2d<_2c){return _1V(_2c,_2d,-2147483648);}else{return _23(_2c,_2d,2147483647);}},_2e=function(_2f,_2g,_2h){if(_2g<_2f){return _1V(_2f,_2g,_2h);}else{return _23(_2f,_2g,_2h);}},_2i=function(_2j){return E(_2j);},_2k=new T(function(){return err(new T(function(){return unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound");}));}),_2l=new T(function(){return err(new T(function(){return unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound");}));}),_2m=function(_2n,_2o){if(_2n<=0){if(_2n>=0){return quot(_2n,_2o);}else{if(_2o<=0){return quot(_2n,_2o);}else{return quot(_2n+1|0,_2o)-1|0;}}}else{if(_2o>=0){if(_2n>=0){return quot(_2n,_2o);}else{if(_2o<=0){return quot(_2n,_2o);}else{return quot(_2n+1|0,_2o)-1|0;}}}else{return quot(_2n-1|0,_2o)-1|0;}}},_2p=new T(function(){return unCStr("base");}),_2q=new T(function(){return unCStr("GHC.Exception");}),_2r=new T(function(){return unCStr("ArithException");}),_2s=function(_2t){return E(new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2p,_2q,_2r),__Z,__Z));},_2u=function(_2v){return E(E(_2v).a);},_2w=function(_2x,_2y,_2z){var _2A=B(A1(_2x,_)),_2B=B(A1(_2y,_)),_2C=hs_eqWord64(_2A.a,_2B.a);if(!_2C){return __Z;}else{var _2D=hs_eqWord64(_2A.b,_2B.b);return (!_2D)?__Z:new T1(1,_2z);}},_2E=new T(function(){return unCStr("Ratio has zero denominator");}),_2F=new T(function(){return unCStr("denormal");}),_2G=new T(function(){return unCStr("divide by zero");}),_2H=new T(function(){return unCStr("loss of precision");}),_2I=new T(function(){return unCStr("arithmetic underflow");}),_2J=new T(function(){return unCStr("arithmetic overflow");}),_2K=function(_2L,_2M){switch(E(_2L)){case 0:return _0(_2J,_2M);case 1:return _0(_2I,_2M);case 2:return _0(_2H,_2M);case 3:return _0(_2G,_2M);case 4:return _0(_2F,_2M);default:return _0(_2E,_2M);}},_2N=function(_2O){return _2K(_2O,__Z);},_2P=function(_2Q,_2R,_2S){var _2T=E(_2R);if(!_2T._){return unAppCStr("[]",_2S);}else{var _2U=new T(function(){var _2V=new T(function(){var _2W=function(_2X){var _2Y=E(_2X);if(!_2Y._){return E(new T2(1,93,_2S));}else{var _2Z=new T(function(){return B(A2(_2Q,_2Y.a,new T(function(){return _2W(_2Y.b);})));});return new T2(1,44,_2Z);}};return _2W(_2T.b);});return B(A2(_2Q,_2T.a,_2V));});return new T2(1,91,_2U);}},_30=new T(function(){return new T5(0,_2s,new T3(0,function(_31,_32,_33){return _2K(_32,_33);},_2N,function(_34,_35){return _2P(_2K,_34,_35);}),_36,function(_37){var _38=E(_37);return _2w(_2u(_38.a),_2s,_38.b);},_2N);}),_36=function(_39){return new T2(0,_30,_39);},_3a=new T(function(){return die(new T(function(){return _36(3);}));}),_3b=new T(function(){return die(new T(function(){return _36(0);}));}),_3c=function(_3d,_3e){var _3f=E(_3e);switch(_3f){case -1:var _3g=E(_3d);if(_3g==(-2147483648)){return E(_3b);}else{return _2m(_3g,-1);}break;case 0:return E(_3a);default:return _2m(_3d,_3f);}},_3h=new T2(0,_3b,0),_3i=function(_3j,_3k){var _3l=_3j%_3k;if(_3j<=0){if(_3j>=0){return _3l;}else{if(_3k<=0){return _3l;}else{return (_3l==0)?0:_3l+_3k|0;}}}else{if(_3k>=0){if(_3j>=0){return _3l;}else{if(_3k<=0){return _3l;}else{return (_3l==0)?0:_3l+_3k|0;}}}else{return (_3l==0)?0:_3l+_3k|0;}}},_3m=function(_3n){return new T1(0,_3n);},_3o=new T1(0,1),_3p=function(_3q){var _3r=E(_3q);if(!_3r._){return E(_3r.a);}else{return I_toInt(_3r.a);}},_3s=new T2(0,function(_3t,_3u){return E(_3t)==E(_3u);},function(_3v,_3w){return E(_3v)!=E(_3w);}),_3x=function(_3y,_3z){return (_3y>=_3z)?(_3y!=_3z)?2:1:0;},_3A={_:0,a:new T3(0,{_:0,a:function(_3B,_3C){return E(_3B)+E(_3C)|0;},b:function(_3D,_3E){return E(_3D)-E(_3E)|0;},c:function(_3F,_3G){return imul(E(_3F),E(_3G))|0;},d:function(_3H){return  -E(_3H);},e:function(_3I){var _3J=E(_3I);return (_3J<0)? -_3J:_3J;},f:function(_3K){var _3L=E(_3K);return (_3L>=0)?(_3L==0)?0:1:-1;},g:function(_3M){return _3p(_3M);}},{_:0,a:_3s,b:function(_3N,_3O){return _3x(E(_3N),E(_3O));},c:function(_3P,_3Q){return E(_3P)<E(_3Q);},d:function(_3R,_3S){return E(_3R)<=E(_3S);},e:function(_3T,_3U){return E(_3T)>E(_3U);},f:function(_3V,_3W){return E(_3V)>=E(_3W);},g:function(_3X,_3Y){var _3Z=E(_3X),_40=E(_3Y);return (_3Z>_40)?_3Z:_40;},h:function(_41,_42){var _43=E(_41),_44=E(_42);return (_43>_44)?_44:_43;}},function(_45){return new T2(0,E(_3m(E(_45))),E(_3o));}),b:{_:0,a:function(_46){var _47=E(_46);return (_47==2147483647)?E(_2l):_47+1|0;},b:function(_48){var _49=E(_48);return (_49==(-2147483648))?E(_2k):_49-1|0;},c:_2i,d:_2i,e:function(_4a){return _1Q(E(_4a),2147483647);},f:function(_4b,_4c){return _2b(E(_4b),E(_4c));},g:function(_4d,_4e){return _1Q(E(_4d),E(_4e));},h:function(_4f,_4g,_4h){return _2e(E(_4f),E(_4g),E(_4h));}},c:function(_4i,_4j){var _4k=E(_4i),_4l=E(_4j);switch(_4l){case -1:if(_4k==(-2147483648)){return E(_3b);}else{return quot(_4k,-1);}break;case 0:return E(_3a);default:return quot(_4k,_4l);}},d:function(_4m,_4n){var _4o=E(_4n);switch(_4o){case -1:return 0;case 0:return E(_3a);default:return E(_4m)%_4o;}},e:function(_4p,_4q){return _3c(E(_4p),E(_4q));},f:function(_4r,_4s){var _4t=E(_4s);switch(_4t){case -1:return 0;case 0:return E(_3a);default:return _3i(E(_4r),_4t);}},g:function(_4u,_4v){var _4w=E(_4u),_4x=E(_4v);switch(_4x){case -1:if(_4w==(-2147483648)){return E(_3h);}else{var _4y=quotRemI(_4w,-1);return new T2(0,_4y.a,_4y.b);}break;case 0:return E(_3a);default:var _4z=quotRemI(_4w,_4x);return new T2(0,_4z.a,_4z.b);}},h:function(_4A,_4B){var _4C=E(_4A),_4D=E(_4B);switch(_4D){case -1:if(_4C==(-2147483648)){return E(_3h);}else{if(_4C<=0){if(_4C>=0){var _4E=quotRemI(_4C,-1);return new T2(0,_4E.a,_4E.b);}else{var _4F=quotRemI(_4C,-1);return new T2(0,_4F.a,_4F.b);}}else{var _4G=quotRemI(_4C-1|0,-1);return new T2(0,_4G.a-1|0,(_4G.b+(-1)|0)+1|0);}}break;case 0:return E(_3a);default:if(_4C<=0){if(_4C>=0){var _4H=quotRemI(_4C,_4D);return new T2(0,_4H.a,_4H.b);}else{if(_4D<=0){var _4I=quotRemI(_4C,_4D);return new T2(0,_4I.a,_4I.b);}else{var _4J=quotRemI(_4C+1|0,_4D);return new T2(0,_4J.a-1|0,(_4J.b+_4D|0)-1|0);}}}else{if(_4D>=0){if(_4C>=0){var _4K=quotRemI(_4C,_4D);return new T2(0,_4K.a,_4K.b);}else{if(_4D<=0){var _4L=quotRemI(_4C,_4D);return new T2(0,_4L.a,_4L.b);}else{var _4M=quotRemI(_4C+1|0,_4D);return new T2(0,_4M.a-1|0,(_4M.b+_4D|0)-1|0);}}}else{var _4N=quotRemI(_4C-1|0,_4D);return new T2(0,_4N.a-1|0,(_4N.b+_4D|0)+1|0);}}}},i:function(_4O){return _3m(E(_4O));}},_4P=new T1(0,2),_4Q=function(_4R){return E(E(_4R).a);},_4S=function(_4T){return E(E(_4T).a);},_4U=function(_4V,_4W){while(1){var _4X=E(_4V);if(!_4X._){var _4Y=_4X.a,_4Z=E(_4W);if(!_4Z._){var _50=_4Z.a;if(!(imul(_4Y,_50)|0)){return new T1(0,imul(_4Y,_50)|0);}else{_4V=new T1(1,I_fromInt(_4Y));_4W=new T1(1,I_fromInt(_50));continue;}}else{_4V=new T1(1,I_fromInt(_4Y));_4W=_4Z;continue;}}else{var _51=E(_4W);if(!_51._){_4V=_4X;_4W=new T1(1,I_fromInt(_51.a));continue;}else{return new T1(1,I_mul(_4X.a,_51.a));}}}},_52=function(_53,_54,_55){while(1){if(!(_54%2)){var _56=_4U(_53,_53),_57=quot(_54,2);_53=_56;_54=_57;continue;}else{var _58=E(_54);if(_58==1){return _4U(_53,_55);}else{var _56=_4U(_53,_53),_59=_4U(_53,_55);_53=_56;_54=quot(_58-1|0,2);_55=_59;continue;}}}},_5a=function(_5b,_5c){while(1){if(!(_5c%2)){var _5d=_4U(_5b,_5b),_5e=quot(_5c,2);_5b=_5d;_5c=_5e;continue;}else{var _5f=E(_5c);if(_5f==1){return E(_5b);}else{return _52(_4U(_5b,_5b),quot(_5f-1|0,2),_5b);}}}},_5g=function(_5h){return E(E(_5h).c);},_5i=function(_5j){return E(E(_5j).a);},_5k=function(_5l){return E(E(_5l).b);},_5m=function(_5n){return E(E(_5n).b);},_5o=function(_5p){return E(E(_5p).c);},_5q=new T1(0,0),_5r=new T1(0,2),_5s=function(_5t){return E(E(_5t).g);},_5u=function(_5v){return E(E(_5v).d);},_5w=function(_5x,_5y){var _5z=_4Q(_5x),_5A=new T(function(){return _4S(_5z);}),_5B=new T(function(){return B(A3(_5u,_5x,_5y,new T(function(){return B(A2(_5s,_5A,_5r));})));});return C > 19 ? new F(function(){return A3(_1F,_5i(_5k(_5z)),_5B,new T(function(){return B(A2(_5s,_5A,_5q));}));}) : (++C,A3(_1F,_5i(_5k(_5z)),_5B,new T(function(){return B(A2(_5s,_5A,_5q));})));},_5C=new T(function(){return unCStr("Negative exponent");}),_5D=new T(function(){return err(_5C);}),_5E=function(_5F){return E(E(_5F).c);},_5G=function(_5H,_5I,_5J,_5K){var _5L=_4Q(_5I),_5M=new T(function(){return _4S(_5L);}),_5N=_5k(_5L);if(!B(A3(_5o,_5N,_5K,new T(function(){return B(A2(_5s,_5M,_5q));})))){if(!B(A3(_1F,_5i(_5N),_5K,new T(function(){return B(A2(_5s,_5M,_5q));})))){var _5O=new T(function(){return B(A2(_5s,_5M,_5r));}),_5P=new T(function(){return B(A2(_5s,_5M,_3o));}),_5Q=_5i(_5N),_5R=function(_5S,_5T,_5U){while(1){var _5V=B((function(_5W,_5X,_5Y){if(!B(_5w(_5I,_5X))){if(!B(A3(_1F,_5Q,_5X,_5P))){var _5Z=new T(function(){return B(A3(_5E,_5I,new T(function(){return B(A3(_5m,_5M,_5X,_5P));}),_5O));});_5S=new T(function(){return B(A3(_5g,_5H,_5W,_5W));});_5T=_5Z;_5U=new T(function(){return B(A3(_5g,_5H,_5W,_5Y));});return __continue;}else{return C > 19 ? new F(function(){return A3(_5g,_5H,_5W,_5Y);}) : (++C,A3(_5g,_5H,_5W,_5Y));}}else{var _60=_5Y;_5S=new T(function(){return B(A3(_5g,_5H,_5W,_5W));});_5T=new T(function(){return B(A3(_5E,_5I,_5X,_5O));});_5U=_60;return __continue;}})(_5S,_5T,_5U));if(_5V!=__continue){return _5V;}}},_61=function(_62,_63){while(1){var _64=(function(_65,_66){if(!B(_5w(_5I,_66))){if(!B(A3(_1F,_5Q,_66,_5P))){var _67=new T(function(){return B(A3(_5E,_5I,new T(function(){return B(A3(_5m,_5M,_66,_5P));}),_5O));});return _5R(new T(function(){return B(A3(_5g,_5H,_65,_65));}),_67,_65);}else{return E(_65);}}else{_62=new T(function(){return B(A3(_5g,_5H,_65,_65));});_63=new T(function(){return B(A3(_5E,_5I,_66,_5O));});return __continue;}})(_62,_63);if(_64!=__continue){return _64;}}};return _61(_5J,_5K);}else{return C > 19 ? new F(function(){return A2(_5s,_5H,_3o);}) : (++C,A2(_5s,_5H,_3o));}}else{return E(_5D);}},_68=new T(function(){return err(_5C);}),_69=function(_6a){var _6b=I_decodeDouble(_6a);return new T2(0,new T1(1,_6b.b),_6b.a);},_6c=function(_6d,_6e){var _6f=E(_6d);return (_6f._==0)?_6f.a*Math.pow(2,_6e):I_toNumber(_6f.a)*Math.pow(2,_6e);},_6g=function(_6h,_6i){var _6j=E(_6h);if(!_6j._){var _6k=_6j.a,_6l=E(_6i);return (_6l._==0)?_6k==_6l.a:(I_compareInt(_6l.a,_6k)==0)?true:false;}else{var _6m=_6j.a,_6n=E(_6i);return (_6n._==0)?(I_compareInt(_6m,_6n.a)==0)?true:false:(I_compare(_6m,_6n.a)==0)?true:false;}},_6o=function(_6p,_6q){while(1){var _6r=E(_6p);if(!_6r._){var _6s=E(_6r.a);if(_6s==(-2147483648)){_6p=new T1(1,I_fromInt(-2147483648));continue;}else{var _6t=E(_6q);if(!_6t._){var _6u=_6t.a;return new T2(0,new T1(0,quot(_6s,_6u)),new T1(0,_6s%_6u));}else{_6p=new T1(1,I_fromInt(_6s));_6q=_6t;continue;}}}else{var _6v=E(_6q);if(!_6v._){_6p=_6r;_6q=new T1(1,I_fromInt(_6v.a));continue;}else{var _6w=I_quotRem(_6r.a,_6v.a);return new T2(0,new T1(1,_6w.a),new T1(1,_6w.b));}}}},_6x=function(_6y,_6z){var _6A=_69(_6z),_6B=_6A.a,_6C=_6A.b,_6D=new T(function(){return _4S(new T(function(){return _4Q(_6y);}));});if(_6C<0){var _6E= -_6C;if(_6E>=0){if(!_6E){var _6F=E(_3o);}else{var _6F=_5a(_4P,_6E);}if(!_6g(_6F,new T1(0,0))){var _6G=_6o(_6B,_6F);return new T2(0,new T(function(){return B(A2(_5s,_6D,_6G.a));}),new T(function(){return _6c(_6G.b,_6C);}));}else{return E(_3a);}}else{return E(_68);}}else{var _6H=new T(function(){var _6I=new T(function(){return B(_5G(_6D,_3A,new T(function(){return B(A2(_5s,_6D,_4P));}),_6C));});return B(A3(_5g,_6D,new T(function(){return B(A2(_5s,_6D,_6B));}),_6I));});return new T2(0,_6H,0);}},_6J=function(_){return 0;},_6K=(function(x){console.log(x);}),_6L=function(_){var _6M=_6K("Error decoding message data");return _6J(_);},_6N=function(_6O,_6P){while(1){var _6Q=E(_6O);if(!_6Q._){return (E(_6P)._==0)?1:0;}else{var _6R=E(_6P);if(!_6R._){return 2;}else{var _6S=E(_6Q.a),_6T=E(_6R.a);if(_6S>=_6T){if(_6S!=_6T){return 2;}else{_6O=_6Q.b;_6P=_6R.b;continue;}}else{return 0;}}}}},_6U=new T0(1),_6V=new T(function(){return unCStr("Failure in Data.Map.balanceL");}),_6W=new T(function(){var _6X=_;return err(_6V);}),_6Y=function(_6Z,_70,_71,_72){var _73=E(_72);if(!_73._){var _74=_73.a,_75=E(_71);if(!_75._){var _76=_75.a,_77=_75.b,_78=_75.c;if(_76<=(imul(3,_74)|0)){return new T5(0,(1+_76|0)+_74|0,E(_6Z),_70,_75,_73);}else{var _79=E(_75.d);if(!_79._){var _7a=_79.a,_7b=E(_75.e);if(!_7b._){var _7c=_7b.a,_7d=_7b.b,_7e=_7b.c,_7f=_7b.d;if(_7c>=(imul(2,_7a)|0)){var _7g=function(_7h){var _7i=E(_7b.e);return (_7i._==0)?new T5(0,(1+_76|0)+_74|0,E(_7d),_7e,E(new T5(0,(1+_7a|0)+_7h|0,E(_77),_78,_79,E(_7f))),E(new T5(0,(1+_74|0)+_7i.a|0,E(_6Z),_70,_7i,_73))):new T5(0,(1+_76|0)+_74|0,E(_7d),_7e,E(new T5(0,(1+_7a|0)+_7h|0,E(_77),_78,_79,E(_7f))),E(new T5(0,1+_74|0,E(_6Z),_70,E(_6U),_73)));},_7j=E(_7f);if(!_7j._){return _7g(_7j.a);}else{return _7g(0);}}else{return new T5(0,(1+_76|0)+_74|0,E(_77),_78,_79,E(new T5(0,(1+_74|0)+_7c|0,E(_6Z),_70,_7b,_73)));}}else{return E(_6W);}}else{return E(_6W);}}}else{return new T5(0,1+_74|0,E(_6Z),_70,E(_6U),_73);}}else{var _7k=E(_71);if(!_7k._){var _7l=_7k.a,_7m=_7k.b,_7n=_7k.c,_7o=_7k.e,_7p=E(_7k.d);if(!_7p._){var _7q=_7p.a,_7r=E(_7o);if(!_7r._){var _7s=_7r.a,_7t=_7r.b,_7u=_7r.c,_7v=_7r.d;if(_7s>=(imul(2,_7q)|0)){var _7w=function(_7x){var _7y=E(_7r.e);return (_7y._==0)?new T5(0,1+_7l|0,E(_7t),_7u,E(new T5(0,(1+_7q|0)+_7x|0,E(_7m),_7n,_7p,E(_7v))),E(new T5(0,1+_7y.a|0,E(_6Z),_70,_7y,E(_6U)))):new T5(0,1+_7l|0,E(_7t),_7u,E(new T5(0,(1+_7q|0)+_7x|0,E(_7m),_7n,_7p,E(_7v))),E(new T5(0,1,E(_6Z),_70,E(_6U),E(_6U))));},_7z=E(_7v);if(!_7z._){return _7w(_7z.a);}else{return _7w(0);}}else{return new T5(0,1+_7l|0,E(_7m),_7n,_7p,E(new T5(0,1+_7s|0,E(_6Z),_70,_7r,E(_6U))));}}else{return new T5(0,3,E(_7m),_7n,_7p,E(new T5(0,1,E(_6Z),_70,E(_6U),E(_6U))));}}else{var _7A=E(_7o);return (_7A._==0)?new T5(0,3,E(_7A.b),_7A.c,E(new T5(0,1,E(_7m),_7n,E(_6U),E(_6U))),E(new T5(0,1,E(_6Z),_70,E(_6U),E(_6U)))):new T5(0,2,E(_6Z),_70,_7k,E(_6U));}}else{return new T5(0,1,E(_6Z),_70,E(_6U),E(_6U));}}},_7B=new T(function(){return unCStr("Failure in Data.Map.balanceR");}),_7C=new T(function(){var _7D=_;return err(_7B);}),_7E=function(_7F,_7G,_7H,_7I){var _7J=E(_7H);if(!_7J._){var _7K=_7J.a,_7L=E(_7I);if(!_7L._){var _7M=_7L.a,_7N=_7L.b,_7O=_7L.c;if(_7M<=(imul(3,_7K)|0)){return new T5(0,(1+_7K|0)+_7M|0,E(_7F),_7G,_7J,_7L);}else{var _7P=E(_7L.d);if(!_7P._){var _7Q=_7P.a,_7R=_7P.b,_7S=_7P.c,_7T=_7P.d,_7U=E(_7L.e);if(!_7U._){var _7V=_7U.a;if(_7Q>=(imul(2,_7V)|0)){var _7W=function(_7X){var _7Y=E(_7F),_7Z=E(_7P.e);return (_7Z._==0)?new T5(0,(1+_7K|0)+_7M|0,E(_7R),_7S,E(new T5(0,(1+_7K|0)+_7X|0,_7Y,_7G,_7J,E(_7T))),E(new T5(0,(1+_7V|0)+_7Z.a|0,E(_7N),_7O,_7Z,_7U))):new T5(0,(1+_7K|0)+_7M|0,E(_7R),_7S,E(new T5(0,(1+_7K|0)+_7X|0,_7Y,_7G,_7J,E(_7T))),E(new T5(0,1+_7V|0,E(_7N),_7O,E(_6U),_7U)));},_80=E(_7T);if(!_80._){return _7W(_80.a);}else{return _7W(0);}}else{return new T5(0,(1+_7K|0)+_7M|0,E(_7N),_7O,E(new T5(0,(1+_7K|0)+_7Q|0,E(_7F),_7G,_7J,_7P)),_7U);}}else{return E(_7C);}}else{return E(_7C);}}}else{return new T5(0,1+_7K|0,E(_7F),_7G,_7J,E(_6U));}}else{var _81=E(_7I);if(!_81._){var _82=_81.a,_83=_81.b,_84=_81.c,_85=_81.e,_86=E(_81.d);if(!_86._){var _87=_86.a,_88=_86.b,_89=_86.c,_8a=_86.d,_8b=E(_85);if(!_8b._){var _8c=_8b.a;if(_87>=(imul(2,_8c)|0)){var _8d=function(_8e){var _8f=E(_7F),_8g=E(_86.e);return (_8g._==0)?new T5(0,1+_82|0,E(_88),_89,E(new T5(0,1+_8e|0,_8f,_7G,E(_6U),E(_8a))),E(new T5(0,(1+_8c|0)+_8g.a|0,E(_83),_84,_8g,_8b))):new T5(0,1+_82|0,E(_88),_89,E(new T5(0,1+_8e|0,_8f,_7G,E(_6U),E(_8a))),E(new T5(0,1+_8c|0,E(_83),_84,E(_6U),_8b)));},_8h=E(_8a);if(!_8h._){return _8d(_8h.a);}else{return _8d(0);}}else{return new T5(0,1+_82|0,E(_83),_84,E(new T5(0,1+_87|0,E(_7F),_7G,E(_6U),_86)),_8b);}}else{return new T5(0,3,E(_88),_89,E(new T5(0,1,E(_7F),_7G,E(_6U),E(_6U))),E(new T5(0,1,E(_83),_84,E(_6U),E(_6U))));}}else{var _8i=E(_85);return (_8i._==0)?new T5(0,3,E(_83),_84,E(new T5(0,1,E(_7F),_7G,E(_6U),E(_6U))),_8i):new T5(0,2,E(_7F),_7G,E(_6U),_81);}}else{return new T5(0,1,E(_7F),_7G,E(_6U),E(_6U));}}},_8j=function(_8k,_8l,_8m){var _8n=E(_8k),_8o=E(_8l),_8p=E(_8m);if(!_8p._){var _8q=_8p.b,_8r=_8p.c,_8s=_8p.d,_8t=_8p.e;switch(_6N(_8n,_8q)){case 0:return _6Y(_8q,_8r,_8j(_8n,_8o,_8s),_8t);case 1:return new T5(0,_8p.a,_8n,_8o,E(_8s),E(_8t));default:return _7E(_8q,_8r,_8s,_8j(_8n,_8o,_8t));}}else{return new T5(0,1,_8n,_8o,E(_6U),E(_6U));}},_8u=function(_8v,_8w){while(1){var _8x=E(_8w);if(!_8x._){return E(_8v);}else{var _8y=E(_8x.a),_8z=_8j(_8y.a,_8y.b,_8v);_8v=_8z;_8w=_8x.b;continue;}}},_8A=function(_8B,_8C){return new T5(0,1,E(_8B),_8C,E(_6U),E(_6U));},_8D=function(_8E,_8F,_8G){var _8H=E(_8G);if(!_8H._){return _7E(_8H.b,_8H.c,_8H.d,_8D(_8E,_8F,_8H.e));}else{return _8A(_8E,_8F);}},_8I=function(_8J,_8K,_8L){var _8M=E(_8L);if(!_8M._){return _6Y(_8M.b,_8M.c,_8I(_8J,_8K,_8M.d),_8M.e);}else{return _8A(_8J,_8K);}},_8N=function(_8O,_8P,_8Q,_8R,_8S,_8T,_8U){return _6Y(_8R,_8S,_8I(_8O,_8P,_8T),_8U);},_8V=function(_8W,_8X,_8Y,_8Z,_90,_91,_92,_93){var _94=E(_8Y);if(!_94._){var _95=_94.a,_96=_94.b,_97=_94.c,_98=_94.d,_99=_94.e;if((imul(3,_95)|0)>=_8Z){if((imul(3,_8Z)|0)>=_95){return new T5(0,(_95+_8Z|0)+1|0,E(_8W),_8X,_94,E(new T5(0,_8Z,E(_90),_91,E(_92),E(_93))));}else{return _7E(_96,_97,_98,B(_8V(_8W,_8X,_99,_8Z,_90,_91,_92,_93)));}}else{return _6Y(_90,_91,B(_9a(_8W,_8X,_95,_96,_97,_98,_99,_92)),_93);}}else{return _8N(_8W,_8X,_8Z,_90,_91,_92,_93);}},_9a=function(_9b,_9c,_9d,_9e,_9f,_9g,_9h,_9i){var _9j=E(_9i);if(!_9j._){var _9k=_9j.a,_9l=_9j.b,_9m=_9j.c,_9n=_9j.d,_9o=_9j.e;if((imul(3,_9d)|0)>=_9k){if((imul(3,_9k)|0)>=_9d){return new T5(0,(_9d+_9k|0)+1|0,E(_9b),_9c,E(new T5(0,_9d,E(_9e),_9f,E(_9g),E(_9h))),_9j);}else{return _7E(_9e,_9f,_9g,B(_8V(_9b,_9c,_9h,_9k,_9l,_9m,_9n,_9o)));}}else{return _6Y(_9l,_9m,B(_9a(_9b,_9c,_9d,_9e,_9f,_9g,_9h,_9n)),_9o);}}else{return _8D(_9b,_9c,new T5(0,_9d,E(_9e),_9f,E(_9g),E(_9h)));}},_9p=function(_9q,_9r,_9s,_9t){var _9u=E(_9s);if(!_9u._){var _9v=_9u.a,_9w=_9u.b,_9x=_9u.c,_9y=_9u.d,_9z=_9u.e,_9A=E(_9t);if(!_9A._){var _9B=_9A.a,_9C=_9A.b,_9D=_9A.c,_9E=_9A.d,_9F=_9A.e;if((imul(3,_9v)|0)>=_9B){if((imul(3,_9B)|0)>=_9v){return new T5(0,(_9v+_9B|0)+1|0,E(_9q),_9r,_9u,_9A);}else{return _7E(_9w,_9x,_9y,B(_8V(_9q,_9r,_9z,_9B,_9C,_9D,_9E,_9F)));}}else{return _6Y(_9C,_9D,B(_9a(_9q,_9r,_9v,_9w,_9x,_9y,_9z,_9E)),_9F);}}else{return _8D(_9q,_9r,_9u);}}else{return _8I(_9q,_9r,_9t);}},_9G=function(_9H,_9I){var _9J=E(_9I);if(!_9J._){return new T3(0,_6U,__Z,__Z);}else{var _9K=E(_9H);if(_9K==1){var _9L=E(_9J.a),_9M=_9L.a,_9N=_9L.b,_9O=E(_9J.b);return (_9O._==0)?new T3(0,new T(function(){return new T5(0,1,E(_9M),E(_9N),E(_6U),E(_6U));}),__Z,__Z):(_6N(_9M,E(_9O.a).a)==0)?new T3(0,new T(function(){return new T5(0,1,E(_9M),E(_9N),E(_6U),E(_6U));}),_9O,__Z):new T3(0,new T(function(){return new T5(0,1,E(_9M),E(_9N),E(_6U),E(_6U));}),__Z,_9O);}else{var _9P=_9G(_9K>>1,_9J),_9Q=_9P.a,_9R=_9P.c,_9S=E(_9P.b);if(!_9S._){return new T3(0,_9Q,__Z,_9R);}else{var _9T=E(_9S.a),_9U=_9T.a,_9V=_9T.b,_9W=E(_9S.b);if(!_9W._){return new T3(0,new T(function(){return _8D(_9U,E(_9V),_9Q);}),__Z,_9R);}else{if(!_6N(_9U,E(_9W.a).a)){var _9X=_9G(_9K>>1,_9W);return new T3(0,new T(function(){return B(_9p(_9U,E(_9V),_9Q,_9X.a));}),_9X.b,_9X.c);}else{return new T3(0,_9Q,__Z,_9S);}}}}}},_9Y=function(_9Z,_a0,_a1){while(1){var _a2=E(_a1);if(!_a2._){return E(_a0);}else{var _a3=E(_a2.a),_a4=_a3.a,_a5=_a3.b,_a6=E(_a2.b);if(!_a6._){return _8D(_a4,E(_a5),_a0);}else{if(!_6N(_a4,E(_a6.a).a)){var _a7=_9G(_9Z,_a6),_a8=_a7.a,_a9=E(_a7.c);if(!_a9._){var _aa=_9Z<<1,_ab=B(_9p(_a4,E(_a5),_a0,_a8));_9Z=_aa;_a0=_ab;_a1=_a7.b;continue;}else{return _8u(B(_9p(_a4,E(_a5),_a0,_a8)),_a9);}}else{return _8u(_a0,_a2);}}}}},_ac=function(_ad){var _ae=E(_ad);if(!_ae._){return new T0(1);}else{var _af=E(_ae.a),_ag=_af.a,_ah=_af.b,_ai=E(_ae.b);if(!_ai._){return new T5(0,1,E(_ag),E(_ah),E(_6U),E(_6U));}else{if(!_6N(_ag,E(_ai.a).a)){return C > 19 ? new F(function(){return _9Y(1,new T5(0,1,E(_ag),E(_ah),E(_6U),E(_6U)),_ai);}) : (++C,_9Y(1,new T5(0,1,E(_ag),E(_ah),E(_6U),E(_6U)),_ai));}else{return _8u(new T5(0,1,E(_ag),E(_ah),E(_6U),E(_6U)),_ai);}}}},_aj=function(_ak,_){var _al=E(_ak);if(!_al._){return __Z;}else{var _am=B(A1(_al.a,_)),_an=_aj(_al.b,_);return new T2(1,_am,_an);}},_ao=function(_){var _ap=_6K("Error decoding cost tree data");return _6J(_);},_aq=new T(function(){return err(new T(function(){return unCStr("Maybe.fromJust: Nothing");}));}),_ar=function(_as,_at,_au){while(1){var _av=E(_au);if(!_av._){return __Z;}else{var _aw=E(_av.a);if(!B(A3(_1F,_as,_at,_aw.a))){_au=_av.b;continue;}else{return new T1(1,_aw.b);}}}},_ax=new T(function(){return unCStr("main");}),_ay=new T(function(){return unCStr("Ajax");}),_az=new T(function(){return unCStr("ServerMessageException");}),_aA=function(_aB){return E(new T5(0,new Long(2796709153,857663197,true),new Long(2290229150,2001624562,true),new T5(0,new Long(2796709153,857663197,true),new Long(2290229150,2001624562,true),_ax,_ay,_az),__Z,__Z));},_aC=new T(function(){return unCStr("SME ");}),_aD=new T(function(){return unCStr("Prelude.");}),_aE=new T(function(){return err(new T(function(){return _0(_aD,new T(function(){return unCStr("!!: negative index");}));}));}),_aF=new T(function(){return err(new T(function(){return _0(_aD,new T(function(){return unCStr("!!: index too large");}));}));}),_aG=function(_aH,_aI){while(1){var _aJ=E(_aH);if(!_aJ._){return E(_aF);}else{var _aK=E(_aI);if(!_aK){return E(_aJ.a);}else{_aH=_aJ.b;_aI=_aK-1|0;continue;}}}},_aL=function(_aM,_aN){if(_aN>=0){return _aG(_aM,_aN);}else{return E(_aE);}},_aO=new T(function(){return unCStr("ACK");}),_aP=new T(function(){return unCStr("BEL");}),_aQ=new T(function(){return unCStr("BS");}),_aR=new T(function(){return unCStr("SP");}),_aS=new T(function(){return unCStr("US");}),_aT=new T(function(){return unCStr("RS");}),_aU=new T(function(){return unCStr("GS");}),_aV=new T(function(){return unCStr("FS");}),_aW=new T(function(){return unCStr("ESC");}),_aX=new T(function(){return unCStr("SUB");}),_aY=new T(function(){return unCStr("EM");}),_aZ=new T(function(){return unCStr("CAN");}),_b0=new T(function(){return unCStr("ETB");}),_b1=new T(function(){return unCStr("SYN");}),_b2=new T(function(){return unCStr("NAK");}),_b3=new T(function(){return unCStr("DC4");}),_b4=new T(function(){return unCStr("DC3");}),_b5=new T(function(){return unCStr("DC2");}),_b6=new T(function(){return unCStr("DC1");}),_b7=new T(function(){return unCStr("DLE");}),_b8=new T(function(){return unCStr("SI");}),_b9=new T(function(){return unCStr("SO");}),_ba=new T(function(){return unCStr("CR");}),_bb=new T(function(){return unCStr("FF");}),_bc=new T(function(){return unCStr("VT");}),_bd=new T(function(){return unCStr("LF");}),_be=new T(function(){return unCStr("HT");}),_bf=new T(function(){return unCStr("ENQ");}),_bg=new T(function(){return unCStr("EOT");}),_bh=new T(function(){return unCStr("ETX");}),_bi=new T(function(){return unCStr("STX");}),_bj=new T(function(){return unCStr("SOH");}),_bk=new T(function(){return unCStr("NUL");}),_bl=new T(function(){return unCStr("\\DEL");}),_bm=new T(function(){return unCStr("\\a");}),_bn=new T(function(){return unCStr("\\\\");}),_bo=new T(function(){return unCStr("\\SO");}),_bp=new T(function(){return unCStr("\\r");}),_bq=new T(function(){return unCStr("\\f");}),_br=new T(function(){return unCStr("\\v");}),_bs=new T(function(){return unCStr("\\n");}),_bt=new T(function(){return unCStr("\\t");}),_bu=new T(function(){return unCStr("\\b");}),_bv=function(_bw,_bx){if(_bw<=127){var _by=E(_bw);switch(_by){case 92:return _0(_bn,_bx);case 127:return _0(_bl,_bx);default:if(_by<32){switch(_by){case 7:return _0(_bm,_bx);case 8:return _0(_bu,_bx);case 9:return _0(_bt,_bx);case 10:return _0(_bs,_bx);case 11:return _0(_br,_bx);case 12:return _0(_bq,_bx);case 13:return _0(_bp,_bx);case 14:return _0(_bo,new T(function(){var _bz=E(_bx);if(!_bz._){return __Z;}else{if(E(_bz.a)==72){return unAppCStr("\\&",_bz);}else{return _bz;}}},1));default:return _0(new T2(1,92,new T(function(){return _aL(new T2(1,_bk,new T2(1,_bj,new T2(1,_bi,new T2(1,_bh,new T2(1,_bg,new T2(1,_bf,new T2(1,_aO,new T2(1,_aP,new T2(1,_aQ,new T2(1,_be,new T2(1,_bd,new T2(1,_bc,new T2(1,_bb,new T2(1,_ba,new T2(1,_b9,new T2(1,_b8,new T2(1,_b7,new T2(1,_b6,new T2(1,_b5,new T2(1,_b4,new T2(1,_b3,new T2(1,_b2,new T2(1,_b1,new T2(1,_b0,new T2(1,_aZ,new T2(1,_aY,new T2(1,_aX,new T2(1,_aW,new T2(1,_aV,new T2(1,_aU,new T2(1,_aT,new T2(1,_aS,new T2(1,_aR,__Z))))))))))))))))))))))))))))))))),_by);})),_bx);}}else{return new T2(1,_by,_bx);}}}else{var _bA=new T(function(){var _bB=jsShowI(_bw);return _0(fromJSStr(_bB),new T(function(){var _bC=E(_bx);if(!_bC._){return __Z;}else{var _bD=E(_bC.a);if(_bD<48){return _bC;}else{if(_bD>57){return _bC;}else{return unAppCStr("\\&",_bC);}}}},1));});return new T2(1,92,_bA);}},_bE=new T(function(){return unCStr("\\\"");}),_bF=function(_bG,_bH){var _bI=E(_bG);if(!_bI._){return E(_bH);}else{var _bJ=_bI.b,_bK=E(_bI.a);if(_bK==34){return _0(_bE,new T(function(){return _bF(_bJ,_bH);},1));}else{return _bv(_bK,new T(function(){return _bF(_bJ,_bH);}));}}},_bL=function(_bM,_bN,_bO){if(_bM<11){return _0(_aC,new T2(1,34,new T(function(){return _bF(_bN,new T2(1,34,_bO));})));}else{var _bP=new T(function(){return _0(_aC,new T2(1,34,new T(function(){return _bF(_bN,new T2(1,34,new T2(1,41,_bO)));})));});return new T2(1,40,_bP);}},_bQ=function(_bR){return _bL(0,E(_bR).a,__Z);},_bS=function(_bT,_bU){return _bL(0,E(_bT).a,_bU);},_bV=new T(function(){return new T5(0,_aA,new T3(0,function(_bW,_bX,_bY){return _bL(E(_bW),E(_bX).a,_bY);},_bQ,function(_bZ,_c0){return _2P(_bS,_bZ,_c0);}),function(_c0){return new T2(0,_bV,_c0);},function(_c1){var _c2=E(_c1);return _2w(_2u(_c2.a),_aA,_c2.b);},_bQ);}),_c3=function(_c4){return E(E(_c4).c);},_c5=function(_c6,_c7){return die(new T(function(){return B(A2(_c3,_c7,_c6));}));},_c8=function(_c9,_39){return _c5(_c9,_39);},_ca=new T(function(){return _c8(new T1(0,new T(function(){return unCStr("Error decoding cost tree data");})),_bV);}),_cb=new T(function(){return unCStr("base");}),_cc=new T(function(){return unCStr("Control.Exception.Base");}),_cd=new T(function(){return unCStr("PatternMatchFail");}),_ce=function(_cf){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_cb,_cc,_cd),__Z,__Z));},_cg=function(_ch){return E(E(_ch).a);},_ci=function(_cj,_ck){return _0(E(_cj).a,_ck);},_cl=new T(function(){return new T5(0,_ce,new T3(0,function(_cm,_cn,_co){return _0(E(_cn).a,_co);},_cg,function(_cp,_cq){return _2P(_ci,_cp,_cq);}),function(_cr){return new T2(0,_cl,_cr);},function(_cs){var _ct=E(_cs);return _2w(_2u(_ct.a),_ce,_ct.b);},_cg);}),_cu=new T(function(){return unCStr("Non-exhaustive patterns in");}),_cv=function(_cw,_cx){var _cy=E(_cx);if(!_cy._){return new T2(0,__Z,__Z);}else{var _cz=_cy.a;if(!B(A1(_cw,_cz))){return new T2(0,__Z,_cy);}else{var _cA=new T(function(){var _cB=_cv(_cw,_cy.b);return new T2(0,_cB.a,_cB.b);});return new T2(0,new T2(1,_cz,new T(function(){return E(E(_cA).a);})),new T(function(){return E(E(_cA).b);}));}}},_cC=new T(function(){return unCStr("\n");}),_cD=function(_cE){return (E(_cE)==124)?false:true;},_cF=function(_cG,_cH){var _cI=_cv(_cD,unCStr(_cG)),_cJ=_cI.a,_cK=function(_cL,_cM){var _cN=new T(function(){var _cO=new T(function(){return _0(_cH,new T(function(){return _0(_cM,_cC);},1));});return unAppCStr(": ",_cO);},1);return _0(_cL,_cN);},_cP=E(_cI.b);if(!_cP._){return _cK(_cJ,__Z);}else{if(E(_cP.a)==124){return _cK(_cJ,new T2(1,32,_cP.b));}else{return _cK(_cJ,__Z);}}},_cQ=function(_cR){return _c8(new T1(0,new T(function(){return _cF(_cR,_cu);})),_cl);},_cS=function(_cT){return C > 19 ? new F(function(){return _cQ("Ajax.hs:94:21-91|lambda");}) : (++C,_cQ("Ajax.hs:94:21-91|lambda"));},_cU=function(_cV){var _cW=E(_cV);if(!_cW._){var _cX=_cW.a,_cY=_cX&4294967295;return (_cX>=_cY)?_cY:_cY-1|0;}else{return C > 19 ? new F(function(){return _cQ("Ajax.hs:94:56-74|lambda");}) : (++C,_cQ("Ajax.hs:94:56-74|lambda"));}},_cZ=function(_d0){return C > 19 ? new F(function(){return _cU(_d0);}) : (++C,_cU(_d0));},_d1=function(_d2,_d3){var _d4=E(_d3);return (_d4._==0)?__Z:new T2(1,new T(function(){return B(A1(_d2,_d4.a));}),new T(function(){return _d1(_d2,_d4.b);}));},_d5=function(_d6){var _d7=E(_d6);if(_d7._==3){var _d8=E(_d7.a);if(!_d8._){return C > 19 ? new F(function(){return _cS(_);}) : (++C,_cS(_));}else{var _d9=E(_d8.a);if(_d9._==3){var _da=E(_d8.b);if(!_da._){return C > 19 ? new F(function(){return _cS(_);}) : (++C,_cS(_));}else{var _db=E(_da.a);if(_db._==1){if(!E(_da.b)._){return new T2(0,new T(function(){return _d1(_cZ,_d9.a);}),new T(function(){return fromJSStr(_db.a);}));}else{return C > 19 ? new F(function(){return _cS(_);}) : (++C,_cS(_));}}else{return C > 19 ? new F(function(){return _cS(_);}) : (++C,_cS(_));}}}else{return C > 19 ? new F(function(){return _cS(_);}) : (++C,_cS(_));}}}else{return C > 19 ? new F(function(){return _cS(_);}) : (++C,_cS(_));}},_dc=function(_dd){var _de=B(_d5(_dd));return new T2(0,_de.a,_de.b);},_df=new T(function(){return B(_cQ("Ajax.hs:132:5-39|function getJustNum"));}),_dg=new T(function(){return B(_cQ("Ajax.hs:133:5-42|function getJustStr"));}),_dh=function(_di,_){var _dj=E(_di);if(_dj._==4){var _dk=_dj.a,_dl=_ar(_1L,"lin",_dk);if(!_dl._){return E(_aq);}else{var _dm=function(_,_dn){var _do=_ar(_1L,"score",_dk);if(!_do._){var _dp=_ao(_);return E(_ca);}else{var _dq=_ar(_1L,"tree",_dk);if(!_dq._){var _dr=_ao(_);return E(_ca);}else{return new T3(0,new T(function(){var _ds=E(_do.a);if(!_ds._){var _dt=_6x(_3A,_ds.a),_du=_dt.a;if(E(_dt.b)>=0){return E(_du);}else{return E(_du)-1|0;}}else{return E(_df);}}),_dn,new T(function(){var _dv=E(_dq.a);if(_dv._==1){return fromJSStr(_dv.a);}else{return E(_dg);}}));}}},_dw=E(_dl.a);if(_dw._==3){return _dm(_,new T(function(){return _d1(_dc,_dw.a);}));}else{return _dm(_,__Z);}}}else{return E(_aq);}},_dx=new T(function(){return B(_cQ("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_dy=function(_dz,_dA){while(1){var _dB=(function(_dC,_dD){var _dE=E(_dC);switch(_dE._){case 0:var _dF=E(_dD);if(!_dF._){return __Z;}else{_dz=B(A1(_dE.a,_dF.a));_dA=_dF.b;return __continue;}break;case 1:var _dG=B(A1(_dE.a,_dD)),_dH=_dD;_dz=_dG;_dA=_dH;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_dE.a,_dD),new T(function(){return _dy(_dE.b,_dD);}));default:return E(_dE.a);}})(_dz,_dA);if(_dB!=__continue){return _dB;}}},_dI=function(_dJ,_dK){var _dL=function(_dM){var _dN=E(_dK);if(_dN._==3){return new T2(3,_dN.a,new T(function(){return _dI(_dJ,_dN.b);}));}else{var _dO=E(_dJ);if(_dO._==2){return _dN;}else{if(_dN._==2){return _dO;}else{var _dP=function(_dQ){if(_dN._==4){var _dR=function(_dS){return new T1(4,new T(function(){return _0(_dy(_dO,_dS),_dN.a);}));};return new T1(1,_dR);}else{if(_dO._==1){var _dT=_dO.a;if(!_dN._){return new T1(1,function(_dU){return _dI(B(A1(_dT,_dU)),_dN);});}else{var _dV=function(_dW){return _dI(B(A1(_dT,_dW)),new T(function(){return B(A1(_dN.a,_dW));}));};return new T1(1,_dV);}}else{if(!_dN._){return E(_dx);}else{var _dX=function(_dY){return _dI(_dO,new T(function(){return B(A1(_dN.a,_dY));}));};return new T1(1,_dX);}}}};switch(_dO._){case 1:if(_dN._==4){var _dZ=function(_e0){return new T1(4,new T(function(){return _0(_dy(B(A1(_dO.a,_e0)),_e0),_dN.a);}));};return new T1(1,_dZ);}else{return _dP(_);}break;case 4:var _e1=_dO.a;switch(_dN._){case 0:var _e2=function(_e3){var _e4=new T(function(){return _0(_e1,new T(function(){return _dy(_dN,_e3);},1));});return new T1(4,_e4);};return new T1(1,_e2);case 1:var _e5=function(_e6){var _e7=new T(function(){return _0(_e1,new T(function(){return _dy(B(A1(_dN.a,_e6)),_e6);},1));});return new T1(4,_e7);};return new T1(1,_e5);default:return new T1(4,new T(function(){return _0(_e1,_dN.a);}));}break;default:return _dP(_);}}}}},_e8=E(_dJ);switch(_e8._){case 0:var _e9=E(_dK);if(!_e9._){var _ea=function(_eb){return _dI(B(A1(_e8.a,_eb)),new T(function(){return B(A1(_e9.a,_eb));}));};return new T1(0,_ea);}else{return _dL(_);}break;case 3:return new T2(3,_e8.a,new T(function(){return _dI(_e8.b,_dK);}));default:return _dL(_);}},_ec=new T(function(){return unCStr("(");}),_ed=new T(function(){return unCStr(")");}),_ee=function(_ef,_eg){while(1){var _eh=E(_ef);if(!_eh._){return (E(_eg)._==0)?true:false;}else{var _ei=E(_eg);if(!_ei._){return false;}else{if(E(_eh.a)!=E(_ei.a)){return false;}else{_ef=_eh.b;_eg=_ei.b;continue;}}}}},_ej=new T2(0,function(_ek,_el){return E(_ek)==E(_el);},function(_em,_en){return E(_em)!=E(_en);}),_eo=function(_ep,_eq){while(1){var _er=E(_ep);if(!_er._){return (E(_eq)._==0)?true:false;}else{var _es=E(_eq);if(!_es._){return false;}else{if(E(_er.a)!=E(_es.a)){return false;}else{_ep=_er.b;_eq=_es.b;continue;}}}}},_et=function(_eu,_ev){return (!_eo(_eu,_ev))?true:false;},_ew=function(_ex,_ey){var _ez=E(_ex);switch(_ez._){case 0:return new T1(0,function(_eA){return C > 19 ? new F(function(){return _ew(B(A1(_ez.a,_eA)),_ey);}) : (++C,_ew(B(A1(_ez.a,_eA)),_ey));});case 1:return new T1(1,function(_eB){return C > 19 ? new F(function(){return _ew(B(A1(_ez.a,_eB)),_ey);}) : (++C,_ew(B(A1(_ez.a,_eB)),_ey));});case 2:return new T0(2);case 3:return _dI(B(A1(_ey,_ez.a)),new T(function(){return B(_ew(_ez.b,_ey));}));default:var _eC=function(_eD){var _eE=E(_eD);if(!_eE._){return __Z;}else{var _eF=E(_eE.a);return _0(_dy(B(A1(_ey,_eF.a)),_eF.b),new T(function(){return _eC(_eE.b);},1));}},_eG=_eC(_ez.a);return (_eG._==0)?new T0(2):new T1(4,_eG);}},_eH=new T0(2),_eI=function(_eJ){return new T2(3,_eJ,_eH);},_eK=function(_eL,_eM){var _eN=E(_eL);if(!_eN){return C > 19 ? new F(function(){return A1(_eM,0);}) : (++C,A1(_eM,0));}else{var _eO=new T(function(){return B(_eK(_eN-1|0,_eM));});return new T1(0,function(_eP){return E(_eO);});}},_eQ=function(_eR,_eS,_eT){var _eU=new T(function(){return B(A1(_eR,_eI));}),_eV=function(_eW,_eX,_eY,_eZ){while(1){var _f0=B((function(_f1,_f2,_f3,_f4){var _f5=E(_f1);switch(_f5._){case 0:var _f6=E(_f2);if(!_f6._){return C > 19 ? new F(function(){return A1(_eS,_f4);}) : (++C,A1(_eS,_f4));}else{var _f7=_f3+1|0,_f8=_f4;_eW=B(A1(_f5.a,_f6.a));_eX=_f6.b;_eY=_f7;_eZ=_f8;return __continue;}break;case 1:var _f9=B(A1(_f5.a,_f2)),_fa=_f2,_f7=_f3,_f8=_f4;_eW=_f9;_eX=_fa;_eY=_f7;_eZ=_f8;return __continue;case 2:return C > 19 ? new F(function(){return A1(_eS,_f4);}) : (++C,A1(_eS,_f4));break;case 3:var _fb=new T(function(){return B(_ew(_f5,_f4));});return C > 19 ? new F(function(){return _eK(_f3,function(_fc){return E(_fb);});}) : (++C,_eK(_f3,function(_fc){return E(_fb);}));break;default:return C > 19 ? new F(function(){return _ew(_f5,_f4);}) : (++C,_ew(_f5,_f4));}})(_eW,_eX,_eY,_eZ));if(_f0!=__continue){return _f0;}}};return function(_fd){return _eV(_eU,_fd,0,_eT);};},_fe=function(_ff){return C > 19 ? new F(function(){return A1(_ff,__Z);}) : (++C,A1(_ff,__Z));},_fg=function(_fh,_fi){var _fj=function(_fk){var _fl=E(_fk);if(!_fl._){return _fe;}else{var _fm=_fl.a;if(!B(A1(_fh,_fm))){return _fe;}else{var _fn=new T(function(){return _fj(_fl.b);}),_fo=function(_fp){var _fq=new T(function(){return B(A1(_fn,function(_fr){return C > 19 ? new F(function(){return A1(_fp,new T2(1,_fm,_fr));}) : (++C,A1(_fp,new T2(1,_fm,_fr)));}));});return new T1(0,function(_fs){return E(_fq);});};return _fo;}}};return function(_ft){return C > 19 ? new F(function(){return A2(_fj,_ft,_fi);}) : (++C,A2(_fj,_ft,_fi));};},_fu=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_fv=function(_fw,_fx){var _fy=function(_fz,_fA){var _fB=E(_fz);if(!_fB._){var _fC=new T(function(){return B(A1(_fA,__Z));});return function(_fD){return C > 19 ? new F(function(){return A1(_fD,_fC);}) : (++C,A1(_fD,_fC));};}else{var _fE=E(_fB.a),_fF=function(_fG){var _fH=new T(function(){return _fy(_fB.b,function(_fI){return C > 19 ? new F(function(){return A1(_fA,new T2(1,_fG,_fI));}) : (++C,A1(_fA,new T2(1,_fG,_fI)));});}),_fJ=function(_fK){var _fL=new T(function(){return B(A1(_fH,_fK));});return new T1(0,function(_fM){return E(_fL);});};return _fJ;};switch(E(_fw)){case 8:if(48>_fE){var _fN=new T(function(){return B(A1(_fA,__Z));});return function(_fO){return C > 19 ? new F(function(){return A1(_fO,_fN);}) : (++C,A1(_fO,_fN));};}else{if(_fE>55){var _fP=new T(function(){return B(A1(_fA,__Z));});return function(_fQ){return C > 19 ? new F(function(){return A1(_fQ,_fP);}) : (++C,A1(_fQ,_fP));};}else{return _fF(_fE-48|0);}}break;case 10:if(48>_fE){var _fR=new T(function(){return B(A1(_fA,__Z));});return function(_fS){return C > 19 ? new F(function(){return A1(_fS,_fR);}) : (++C,A1(_fS,_fR));};}else{if(_fE>57){var _fT=new T(function(){return B(A1(_fA,__Z));});return function(_fU){return C > 19 ? new F(function(){return A1(_fU,_fT);}) : (++C,A1(_fU,_fT));};}else{return _fF(_fE-48|0);}}break;case 16:if(48>_fE){if(97>_fE){if(65>_fE){var _fV=new T(function(){return B(A1(_fA,__Z));});return function(_fW){return C > 19 ? new F(function(){return A1(_fW,_fV);}) : (++C,A1(_fW,_fV));};}else{if(_fE>70){var _fX=new T(function(){return B(A1(_fA,__Z));});return function(_fY){return C > 19 ? new F(function(){return A1(_fY,_fX);}) : (++C,A1(_fY,_fX));};}else{return _fF((_fE-65|0)+10|0);}}}else{if(_fE>102){if(65>_fE){var _fZ=new T(function(){return B(A1(_fA,__Z));});return function(_g0){return C > 19 ? new F(function(){return A1(_g0,_fZ);}) : (++C,A1(_g0,_fZ));};}else{if(_fE>70){var _g1=new T(function(){return B(A1(_fA,__Z));});return function(_g2){return C > 19 ? new F(function(){return A1(_g2,_g1);}) : (++C,A1(_g2,_g1));};}else{return _fF((_fE-65|0)+10|0);}}}else{return _fF((_fE-97|0)+10|0);}}}else{if(_fE>57){if(97>_fE){if(65>_fE){var _g3=new T(function(){return B(A1(_fA,__Z));});return function(_g4){return C > 19 ? new F(function(){return A1(_g4,_g3);}) : (++C,A1(_g4,_g3));};}else{if(_fE>70){var _g5=new T(function(){return B(A1(_fA,__Z));});return function(_g6){return C > 19 ? new F(function(){return A1(_g6,_g5);}) : (++C,A1(_g6,_g5));};}else{return _fF((_fE-65|0)+10|0);}}}else{if(_fE>102){if(65>_fE){var _g7=new T(function(){return B(A1(_fA,__Z));});return function(_g8){return C > 19 ? new F(function(){return A1(_g8,_g7);}) : (++C,A1(_g8,_g7));};}else{if(_fE>70){var _g9=new T(function(){return B(A1(_fA,__Z));});return function(_ga){return C > 19 ? new F(function(){return A1(_ga,_g9);}) : (++C,A1(_ga,_g9));};}else{return _fF((_fE-65|0)+10|0);}}}else{return _fF((_fE-97|0)+10|0);}}}else{return _fF(_fE-48|0);}}break;default:return E(_fu);}}},_gb=function(_gc){var _gd=E(_gc);if(!_gd._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_fx,_gd);}) : (++C,A1(_fx,_gd));}};return function(_ge){return C > 19 ? new F(function(){return A3(_fy,_ge,_1C,_gb);}) : (++C,A3(_fy,_ge,_1C,_gb));};},_gf=function(_gg){var _gh=function(_gi){return C > 19 ? new F(function(){return A1(_gg,new T1(5,new T2(0,8,_gi)));}) : (++C,A1(_gg,new T1(5,new T2(0,8,_gi))));},_gj=function(_gk){return C > 19 ? new F(function(){return A1(_gg,new T1(5,new T2(0,16,_gk)));}) : (++C,A1(_gg,new T1(5,new T2(0,16,_gk))));},_gl=function(_gm){switch(E(_gm)){case 79:return new T1(1,_fv(8,_gh));case 88:return new T1(1,_fv(16,_gj));case 111:return new T1(1,_fv(8,_gh));case 120:return new T1(1,_fv(16,_gj));default:return new T0(2);}};return function(_gn){return (E(_gn)==48)?E(new T1(0,_gl)):new T0(2);};},_go=function(_gp){return new T1(0,_gf(_gp));},_gq=function(_gr){return C > 19 ? new F(function(){return A1(_gr,__Z);}) : (++C,A1(_gr,__Z));},_gs=function(_gt){return C > 19 ? new F(function(){return A1(_gt,__Z);}) : (++C,A1(_gt,__Z));},_gu=function(_gv,_gw){while(1){var _gx=E(_gv);if(!_gx._){var _gy=_gx.a,_gz=E(_gw);if(!_gz._){var _gA=_gz.a,_gB=addC(_gy,_gA);if(!E(_gB.b)){return new T1(0,_gB.a);}else{_gv=new T1(1,I_fromInt(_gy));_gw=new T1(1,I_fromInt(_gA));continue;}}else{_gv=new T1(1,I_fromInt(_gy));_gw=_gz;continue;}}else{var _gC=E(_gw);if(!_gC._){_gv=_gx;_gw=new T1(1,I_fromInt(_gC.a));continue;}else{return new T1(1,I_add(_gx.a,_gC.a));}}}},_gD=new T(function(){return _gu(new T1(0,2147483647),new T1(0,1));}),_gE=function(_gF){var _gG=E(_gF);if(!_gG._){var _gH=E(_gG.a);return (_gH==(-2147483648))?E(_gD):new T1(0, -_gH);}else{return new T1(1,I_negate(_gG.a));}},_gI=new T1(0,10),_gJ=function(_gK,_gL){while(1){var _gM=E(_gK);if(!_gM._){return E(_gL);}else{var _gN=_gL+1|0;_gK=_gM.b;_gL=_gN;continue;}}},_gO=function(_gP){return _3m(E(_gP));},_gQ=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_gR=function(_gS,_gT){var _gU=E(_gT);if(!_gU._){return __Z;}else{var _gV=E(_gU.b);return (_gV._==0)?E(_gQ):new T2(1,_gu(_4U(_gU.a,_gS),_gV.a),new T(function(){return _gR(_gS,_gV.b);}));}},_gW=new T1(0,0),_gX=function(_gY,_gZ,_h0){while(1){var _h1=(function(_h2,_h3,_h4){var _h5=E(_h4);if(!_h5._){return E(_gW);}else{if(!E(_h5.b)._){return E(_h5.a);}else{var _h6=E(_h3);if(_h6<=40){var _h7=function(_h8,_h9){while(1){var _ha=E(_h9);if(!_ha._){return E(_h8);}else{var _hb=_gu(_4U(_h8,_h2),_ha.a);_h8=_hb;_h9=_ha.b;continue;}}};return _h7(_gW,_h5);}else{var _hc=_4U(_h2,_h2);if(!(_h6%2)){var _hd=_gR(_h2,_h5);_gY=_hc;_gZ=quot(_h6+1|0,2);_h0=_hd;return __continue;}else{var _hd=_gR(_h2,new T2(1,_gW,_h5));_gY=_hc;_gZ=quot(_h6+1|0,2);_h0=_hd;return __continue;}}}}})(_gY,_gZ,_h0);if(_h1!=__continue){return _h1;}}},_he=function(_hf,_hg){return _gX(_hf,new T(function(){return _gJ(_hg,0);},1),_d1(_gO,_hg));},_hh=function(_hi){var _hj=new T(function(){var _hk=new T(function(){var _hl=function(_hm){return C > 19 ? new F(function(){return A1(_hi,new T1(1,new T(function(){return _he(_gI,_hm);})));}) : (++C,A1(_hi,new T1(1,new T(function(){return _he(_gI,_hm);}))));};return new T1(1,_fv(10,_hl));}),_hn=function(_ho){if(E(_ho)==43){var _hp=function(_hq){return C > 19 ? new F(function(){return A1(_hi,new T1(1,new T(function(){return _he(_gI,_hq);})));}) : (++C,A1(_hi,new T1(1,new T(function(){return _he(_gI,_hq);}))));};return new T1(1,_fv(10,_hp));}else{return new T0(2);}},_hr=function(_hs){if(E(_hs)==45){var _ht=function(_hu){return C > 19 ? new F(function(){return A1(_hi,new T1(1,new T(function(){return _gE(_he(_gI,_hu));})));}) : (++C,A1(_hi,new T1(1,new T(function(){return _gE(_he(_gI,_hu));}))));};return new T1(1,_fv(10,_ht));}else{return new T0(2);}};return _dI(_dI(new T1(0,_hr),new T1(0,_hn)),_hk);});return _dI(new T1(0,function(_hv){return (E(_hv)==101)?E(_hj):new T0(2);}),new T1(0,function(_hw){return (E(_hw)==69)?E(_hj):new T0(2);}));},_hx=function(_hy){var _hz=function(_hA){return C > 19 ? new F(function(){return A1(_hy,new T1(1,_hA));}) : (++C,A1(_hy,new T1(1,_hA)));};return function(_hB){return (E(_hB)==46)?new T1(1,_fv(10,_hz)):new T0(2);};},_hC=function(_hD){return new T1(0,_hx(_hD));},_hE=function(_hF){var _hG=function(_hH){var _hI=function(_hJ){return new T1(1,_eQ(_hh,_gq,function(_hK){return C > 19 ? new F(function(){return A1(_hF,new T1(5,new T3(1,_hH,_hJ,_hK)));}) : (++C,A1(_hF,new T1(5,new T3(1,_hH,_hJ,_hK))));}));};return new T1(1,_eQ(_hC,_gs,_hI));};return _fv(10,_hG);},_hL=function(_hM){return new T1(1,_hE(_hM));},_hN=function(_hO,_hP,_hQ){while(1){var _hR=E(_hQ);if(!_hR._){return false;}else{if(!B(A3(_1F,_hO,_hP,_hR.a))){_hQ=_hR.b;continue;}else{return true;}}}},_hS=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_hT=function(_hU){return _hN(_ej,_hU,_hS);},_hV=function(_hW){var _hX=new T(function(){return B(A1(_hW,8));}),_hY=new T(function(){return B(A1(_hW,16));});return function(_hZ){switch(E(_hZ)){case 79:return E(_hX);case 88:return E(_hY);case 111:return E(_hX);case 120:return E(_hY);default:return new T0(2);}};},_i0=function(_i1){return new T1(0,_hV(_i1));},_i2=function(_i3){return C > 19 ? new F(function(){return A1(_i3,10);}) : (++C,A1(_i3,10));},_i4=function(_i5,_i6){var _i7=jsShowI(_i5);return _0(fromJSStr(_i7),_i6);},_i8=function(_i9,_ia,_ib){if(_ia>=0){return _i4(_ia,_ib);}else{if(_i9<=6){return _i4(_ia,_ib);}else{return new T2(1,40,new T(function(){var _ic=jsShowI(_ia);return _0(fromJSStr(_ic),new T2(1,41,_ib));}));}}},_id=function(_ie){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _i8(9,_ie,__Z);})));},_if=function(_ig,_ih){var _ii=E(_ig);if(!_ii._){var _ij=_ii.a,_ik=E(_ih);return (_ik._==0)?_ij<=_ik.a:I_compareInt(_ik.a,_ij)>=0;}else{var _il=_ii.a,_im=E(_ih);return (_im._==0)?I_compareInt(_il,_im.a)<=0:I_compare(_il,_im.a)<=0;}},_in=function(_io){return new T0(2);},_ip=function(_iq){var _ir=E(_iq);if(!_ir._){return _in;}else{var _is=_ir.a,_it=E(_ir.b);if(!_it._){return E(_is);}else{var _iu=new T(function(){return _ip(_it);}),_iv=function(_iw){return _dI(B(A1(_is,_iw)),new T(function(){return B(A1(_iu,_iw));}));};return _iv;}}},_ix=function(_iy,_iz){var _iA=function(_iB,_iC,_iD){var _iE=E(_iB);if(!_iE._){return C > 19 ? new F(function(){return A1(_iD,_iy);}) : (++C,A1(_iD,_iy));}else{var _iF=E(_iC);if(!_iF._){return new T0(2);}else{if(E(_iE.a)!=E(_iF.a)){return new T0(2);}else{var _iG=new T(function(){return B(_iA(_iE.b,_iF.b,_iD));});return new T1(0,function(_iH){return E(_iG);});}}}};return function(_iI){return C > 19 ? new F(function(){return _iA(_iy,_iI,_iz);}) : (++C,_iA(_iy,_iI,_iz));};},_iJ=new T(function(){return unCStr("SO");}),_iK=function(_iL){var _iM=new T(function(){return B(A1(_iL,14));});return new T1(1,_ix(_iJ,function(_iN){return E(_iM);}));},_iO=new T(function(){return unCStr("SOH");}),_iP=function(_iQ){var _iR=new T(function(){return B(A1(_iQ,1));});return new T1(1,_ix(_iO,function(_iS){return E(_iR);}));},_iT=new T(function(){return unCStr("NUL");}),_iU=function(_iV){var _iW=new T(function(){return B(A1(_iV,0));});return new T1(1,_ix(_iT,function(_iX){return E(_iW);}));},_iY=new T(function(){return unCStr("STX");}),_iZ=function(_j0){var _j1=new T(function(){return B(A1(_j0,2));});return new T1(1,_ix(_iY,function(_j2){return E(_j1);}));},_j3=new T(function(){return unCStr("ETX");}),_j4=function(_j5){var _j6=new T(function(){return B(A1(_j5,3));});return new T1(1,_ix(_j3,function(_j7){return E(_j6);}));},_j8=new T(function(){return unCStr("EOT");}),_j9=function(_ja){var _jb=new T(function(){return B(A1(_ja,4));});return new T1(1,_ix(_j8,function(_jc){return E(_jb);}));},_jd=new T(function(){return unCStr("ENQ");}),_je=function(_jf){var _jg=new T(function(){return B(A1(_jf,5));});return new T1(1,_ix(_jd,function(_jh){return E(_jg);}));},_ji=new T(function(){return unCStr("ACK");}),_jj=function(_jk){var _jl=new T(function(){return B(A1(_jk,6));});return new T1(1,_ix(_ji,function(_jm){return E(_jl);}));},_jn=new T(function(){return unCStr("BEL");}),_jo=function(_jp){var _jq=new T(function(){return B(A1(_jp,7));});return new T1(1,_ix(_jn,function(_jr){return E(_jq);}));},_js=new T(function(){return unCStr("BS");}),_jt=function(_ju){var _jv=new T(function(){return B(A1(_ju,8));});return new T1(1,_ix(_js,function(_jw){return E(_jv);}));},_jx=new T(function(){return unCStr("HT");}),_jy=function(_jz){var _jA=new T(function(){return B(A1(_jz,9));});return new T1(1,_ix(_jx,function(_jB){return E(_jA);}));},_jC=new T(function(){return unCStr("LF");}),_jD=function(_jE){var _jF=new T(function(){return B(A1(_jE,10));});return new T1(1,_ix(_jC,function(_jG){return E(_jF);}));},_jH=new T(function(){return unCStr("VT");}),_jI=function(_jJ){var _jK=new T(function(){return B(A1(_jJ,11));});return new T1(1,_ix(_jH,function(_jL){return E(_jK);}));},_jM=new T(function(){return unCStr("FF");}),_jN=function(_jO){var _jP=new T(function(){return B(A1(_jO,12));});return new T1(1,_ix(_jM,function(_jQ){return E(_jP);}));},_jR=new T(function(){return unCStr("CR");}),_jS=function(_jT){var _jU=new T(function(){return B(A1(_jT,13));});return new T1(1,_ix(_jR,function(_jV){return E(_jU);}));},_jW=new T(function(){return unCStr("SI");}),_jX=function(_jY){var _jZ=new T(function(){return B(A1(_jY,15));});return new T1(1,_ix(_jW,function(_k0){return E(_jZ);}));},_k1=new T(function(){return unCStr("DLE");}),_k2=function(_k3){var _k4=new T(function(){return B(A1(_k3,16));});return new T1(1,_ix(_k1,function(_k5){return E(_k4);}));},_k6=new T(function(){return unCStr("DC1");}),_k7=function(_k8){var _k9=new T(function(){return B(A1(_k8,17));});return new T1(1,_ix(_k6,function(_ka){return E(_k9);}));},_kb=new T(function(){return unCStr("DC2");}),_kc=function(_kd){var _ke=new T(function(){return B(A1(_kd,18));});return new T1(1,_ix(_kb,function(_kf){return E(_ke);}));},_kg=new T(function(){return unCStr("DC3");}),_kh=function(_ki){var _kj=new T(function(){return B(A1(_ki,19));});return new T1(1,_ix(_kg,function(_kk){return E(_kj);}));},_kl=new T(function(){return unCStr("DC4");}),_km=function(_kn){var _ko=new T(function(){return B(A1(_kn,20));});return new T1(1,_ix(_kl,function(_kp){return E(_ko);}));},_kq=new T(function(){return unCStr("NAK");}),_kr=function(_ks){var _kt=new T(function(){return B(A1(_ks,21));});return new T1(1,_ix(_kq,function(_ku){return E(_kt);}));},_kv=new T(function(){return unCStr("SYN");}),_kw=function(_kx){var _ky=new T(function(){return B(A1(_kx,22));});return new T1(1,_ix(_kv,function(_kz){return E(_ky);}));},_kA=new T(function(){return unCStr("ETB");}),_kB=function(_kC){var _kD=new T(function(){return B(A1(_kC,23));});return new T1(1,_ix(_kA,function(_kE){return E(_kD);}));},_kF=new T(function(){return unCStr("CAN");}),_kG=function(_kH){var _kI=new T(function(){return B(A1(_kH,24));});return new T1(1,_ix(_kF,function(_kJ){return E(_kI);}));},_kK=new T(function(){return unCStr("EM");}),_kL=function(_kM){var _kN=new T(function(){return B(A1(_kM,25));});return new T1(1,_ix(_kK,function(_kO){return E(_kN);}));},_kP=new T(function(){return unCStr("SUB");}),_kQ=function(_kR){var _kS=new T(function(){return B(A1(_kR,26));});return new T1(1,_ix(_kP,function(_kT){return E(_kS);}));},_kU=new T(function(){return unCStr("ESC");}),_kV=function(_kW){var _kX=new T(function(){return B(A1(_kW,27));});return new T1(1,_ix(_kU,function(_kY){return E(_kX);}));},_kZ=new T(function(){return unCStr("FS");}),_l0=function(_l1){var _l2=new T(function(){return B(A1(_l1,28));});return new T1(1,_ix(_kZ,function(_l3){return E(_l2);}));},_l4=new T(function(){return unCStr("GS");}),_l5=function(_l6){var _l7=new T(function(){return B(A1(_l6,29));});return new T1(1,_ix(_l4,function(_l8){return E(_l7);}));},_l9=new T(function(){return unCStr("RS");}),_la=function(_lb){var _lc=new T(function(){return B(A1(_lb,30));});return new T1(1,_ix(_l9,function(_ld){return E(_lc);}));},_le=new T(function(){return unCStr("US");}),_lf=function(_lg){var _lh=new T(function(){return B(A1(_lg,31));});return new T1(1,_ix(_le,function(_li){return E(_lh);}));},_lj=new T(function(){return unCStr("SP");}),_lk=function(_ll){var _lm=new T(function(){return B(A1(_ll,32));});return new T1(1,_ix(_lj,function(_ln){return E(_lm);}));},_lo=new T(function(){return unCStr("DEL");}),_lp=function(_lq){var _lr=new T(function(){return B(A1(_lq,127));});return new T1(1,_ix(_lo,function(_ls){return E(_lr);}));},_lt=new T(function(){return _ip(new T2(1,function(_lu){return new T1(1,_eQ(_iP,_iK,_lu));},new T2(1,_iU,new T2(1,_iZ,new T2(1,_j4,new T2(1,_j9,new T2(1,_je,new T2(1,_jj,new T2(1,_jo,new T2(1,_jt,new T2(1,_jy,new T2(1,_jD,new T2(1,_jI,new T2(1,_jN,new T2(1,_jS,new T2(1,_jX,new T2(1,_k2,new T2(1,_k7,new T2(1,_kc,new T2(1,_kh,new T2(1,_km,new T2(1,_kr,new T2(1,_kw,new T2(1,_kB,new T2(1,_kG,new T2(1,_kL,new T2(1,_kQ,new T2(1,_kV,new T2(1,_l0,new T2(1,_l5,new T2(1,_la,new T2(1,_lf,new T2(1,_lk,new T2(1,_lp,__Z))))))))))))))))))))))))))))))))));}),_lv=function(_lw){var _lx=new T(function(){return B(A1(_lw,7));}),_ly=new T(function(){return B(A1(_lw,8));}),_lz=new T(function(){return B(A1(_lw,9));}),_lA=new T(function(){return B(A1(_lw,10));}),_lB=new T(function(){return B(A1(_lw,11));}),_lC=new T(function(){return B(A1(_lw,12));}),_lD=new T(function(){return B(A1(_lw,13));}),_lE=new T(function(){return B(A1(_lw,92));}),_lF=new T(function(){return B(A1(_lw,39));}),_lG=new T(function(){return B(A1(_lw,34));}),_lH=new T(function(){var _lI=function(_lJ){var _lK=new T(function(){return _3m(E(_lJ));}),_lL=function(_lM){var _lN=_he(_lK,_lM);if(!_if(_lN,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_lw,new T(function(){var _lO=_3p(_lN);if(_lO>>>0>1114111){return _id(_lO);}else{return _lO;}}));}) : (++C,A1(_lw,new T(function(){var _lO=_3p(_lN);if(_lO>>>0>1114111){return _id(_lO);}else{return _lO;}})));}};return new T1(1,_fv(_lJ,_lL));},_lP=new T(function(){var _lQ=new T(function(){return B(A1(_lw,31));}),_lR=new T(function(){return B(A1(_lw,30));}),_lS=new T(function(){return B(A1(_lw,29));}),_lT=new T(function(){return B(A1(_lw,28));}),_lU=new T(function(){return B(A1(_lw,27));}),_lV=new T(function(){return B(A1(_lw,26));}),_lW=new T(function(){return B(A1(_lw,25));}),_lX=new T(function(){return B(A1(_lw,24));}),_lY=new T(function(){return B(A1(_lw,23));}),_lZ=new T(function(){return B(A1(_lw,22));}),_m0=new T(function(){return B(A1(_lw,21));}),_m1=new T(function(){return B(A1(_lw,20));}),_m2=new T(function(){return B(A1(_lw,19));}),_m3=new T(function(){return B(A1(_lw,18));}),_m4=new T(function(){return B(A1(_lw,17));}),_m5=new T(function(){return B(A1(_lw,16));}),_m6=new T(function(){return B(A1(_lw,15));}),_m7=new T(function(){return B(A1(_lw,14));}),_m8=new T(function(){return B(A1(_lw,6));}),_m9=new T(function(){return B(A1(_lw,5));}),_ma=new T(function(){return B(A1(_lw,4));}),_mb=new T(function(){return B(A1(_lw,3));}),_mc=new T(function(){return B(A1(_lw,2));}),_md=new T(function(){return B(A1(_lw,1));}),_me=new T(function(){return B(A1(_lw,0));}),_mf=function(_mg){switch(E(_mg)){case 64:return E(_me);case 65:return E(_md);case 66:return E(_mc);case 67:return E(_mb);case 68:return E(_ma);case 69:return E(_m9);case 70:return E(_m8);case 71:return E(_lx);case 72:return E(_ly);case 73:return E(_lz);case 74:return E(_lA);case 75:return E(_lB);case 76:return E(_lC);case 77:return E(_lD);case 78:return E(_m7);case 79:return E(_m6);case 80:return E(_m5);case 81:return E(_m4);case 82:return E(_m3);case 83:return E(_m2);case 84:return E(_m1);case 85:return E(_m0);case 86:return E(_lZ);case 87:return E(_lY);case 88:return E(_lX);case 89:return E(_lW);case 90:return E(_lV);case 91:return E(_lU);case 92:return E(_lT);case 93:return E(_lS);case 94:return E(_lR);case 95:return E(_lQ);default:return new T0(2);}};return _dI(new T1(0,function(_mh){return (E(_mh)==94)?E(new T1(0,_mf)):new T0(2);}),new T(function(){return B(A1(_lt,_lw));}));});return _dI(new T1(1,_eQ(_i0,_i2,_lI)),_lP);});return _dI(new T1(0,function(_mi){switch(E(_mi)){case 34:return E(_lG);case 39:return E(_lF);case 92:return E(_lE);case 97:return E(_lx);case 98:return E(_ly);case 102:return E(_lC);case 110:return E(_lA);case 114:return E(_lD);case 116:return E(_lz);case 118:return E(_lB);default:return new T0(2);}}),_lH);},_mj=function(_mk){return C > 19 ? new F(function(){return A1(_mk,0);}) : (++C,A1(_mk,0));},_ml=function(_mm){var _mn=E(_mm);if(!_mn._){return _mj;}else{var _mo=E(_mn.a),_mp=_mo>>>0,_mq=new T(function(){return _ml(_mn.b);});if(_mp>887){var _mr=u_iswspace(_mo);if(!E(_mr)){return _mj;}else{var _ms=function(_mt){var _mu=new T(function(){return B(A1(_mq,_mt));});return new T1(0,function(_mv){return E(_mu);});};return _ms;}}else{if(_mp==32){var _mw=function(_mx){var _my=new T(function(){return B(A1(_mq,_mx));});return new T1(0,function(_mz){return E(_my);});};return _mw;}else{if(_mp-9>>>0>4){if(_mp==160){var _mA=function(_mB){var _mC=new T(function(){return B(A1(_mq,_mB));});return new T1(0,function(_mD){return E(_mC);});};return _mA;}else{return _mj;}}else{var _mE=function(_mF){var _mG=new T(function(){return B(A1(_mq,_mF));});return new T1(0,function(_mH){return E(_mG);});};return _mE;}}}}},_mI=function(_mJ){var _mK=new T(function(){return B(_mI(_mJ));}),_mL=function(_mM){return (E(_mM)==92)?E(_mK):new T0(2);},_mN=function(_mO){return E(new T1(0,_mL));},_mP=new T1(1,function(_mQ){return C > 19 ? new F(function(){return A2(_ml,_mQ,_mN);}) : (++C,A2(_ml,_mQ,_mN));}),_mR=new T(function(){return B(_lv(function(_mS){return C > 19 ? new F(function(){return A1(_mJ,new T2(0,_mS,true));}) : (++C,A1(_mJ,new T2(0,_mS,true)));}));}),_mT=function(_mU){var _mV=E(_mU);if(_mV==38){return E(_mK);}else{var _mW=_mV>>>0;if(_mW>887){var _mX=u_iswspace(_mV);return (E(_mX)==0)?new T0(2):E(_mP);}else{return (_mW==32)?E(_mP):(_mW-9>>>0>4)?(_mW==160)?E(_mP):new T0(2):E(_mP);}}};return _dI(new T1(0,function(_mY){return (E(_mY)==92)?E(new T1(0,_mT)):new T0(2);}),new T1(0,function(_mZ){var _n0=E(_mZ);if(_n0==92){return E(_mR);}else{return C > 19 ? new F(function(){return A1(_mJ,new T2(0,_n0,false));}) : (++C,A1(_mJ,new T2(0,_n0,false)));}}));},_n1=function(_n2,_n3){var _n4=new T(function(){return B(A1(_n3,new T1(1,new T(function(){return B(A1(_n2,__Z));}))));}),_n5=function(_n6){var _n7=E(_n6),_n8=E(_n7.a);if(_n8==34){if(!E(_n7.b)){return E(_n4);}else{return C > 19 ? new F(function(){return _n1(function(_n9){return C > 19 ? new F(function(){return A1(_n2,new T2(1,_n8,_n9));}) : (++C,A1(_n2,new T2(1,_n8,_n9)));},_n3);}) : (++C,_n1(function(_n9){return C > 19 ? new F(function(){return A1(_n2,new T2(1,_n8,_n9));}) : (++C,A1(_n2,new T2(1,_n8,_n9)));},_n3));}}else{return C > 19 ? new F(function(){return _n1(function(_na){return C > 19 ? new F(function(){return A1(_n2,new T2(1,_n8,_na));}) : (++C,A1(_n2,new T2(1,_n8,_na)));},_n3);}) : (++C,_n1(function(_na){return C > 19 ? new F(function(){return A1(_n2,new T2(1,_n8,_na));}) : (++C,A1(_n2,new T2(1,_n8,_na)));},_n3));}};return C > 19 ? new F(function(){return _mI(_n5);}) : (++C,_mI(_n5));},_nb=new T(function(){return unCStr("_\'");}),_nc=function(_nd){var _ne=u_iswalnum(_nd);if(!E(_ne)){return _hN(_ej,_nd,_nb);}else{return true;}},_nf=function(_ng){return _nc(E(_ng));},_nh=new T(function(){return unCStr(",;()[]{}`");}),_ni=new T(function(){return unCStr("=>");}),_nj=new T(function(){return unCStr("~");}),_nk=new T(function(){return unCStr("@");}),_nl=new T(function(){return unCStr("->");}),_nm=new T(function(){return unCStr("<-");}),_nn=new T(function(){return unCStr("|");}),_no=new T(function(){return unCStr("\\");}),_np=new T(function(){return unCStr("=");}),_nq=new T(function(){return unCStr("::");}),_nr=new T(function(){return unCStr("..");}),_ns=function(_nt){var _nu=new T(function(){return B(A1(_nt,new T0(6)));}),_nv=new T(function(){var _nw=new T(function(){var _nx=function(_ny){var _nz=new T(function(){return B(A1(_nt,new T1(0,_ny)));});return new T1(0,function(_nA){return (E(_nA)==39)?E(_nz):new T0(2);});};return B(_lv(_nx));}),_nB=function(_nC){var _nD=E(_nC);switch(_nD){case 39:return new T0(2);case 92:return E(_nw);default:var _nE=new T(function(){return B(A1(_nt,new T1(0,_nD)));});return new T1(0,function(_nF){return (E(_nF)==39)?E(_nE):new T0(2);});}},_nG=new T(function(){var _nH=new T(function(){return B(_n1(_1C,_nt));}),_nI=new T(function(){var _nJ=new T(function(){var _nK=new T(function(){var _nL=function(_nM){var _nN=E(_nM),_nO=u_iswalpha(_nN);return (E(_nO)==0)?(_nN==95)?new T1(1,_fg(_nf,function(_nP){return C > 19 ? new F(function(){return A1(_nt,new T1(3,new T2(1,_nN,_nP)));}) : (++C,A1(_nt,new T1(3,new T2(1,_nN,_nP))));})):new T0(2):new T1(1,_fg(_nf,function(_nQ){return C > 19 ? new F(function(){return A1(_nt,new T1(3,new T2(1,_nN,_nQ)));}) : (++C,A1(_nt,new T1(3,new T2(1,_nN,_nQ))));}));};return _dI(new T1(0,_nL),new T(function(){return new T1(1,_eQ(_go,_hL,_nt));}));}),_nR=function(_nS){return (!_hN(_ej,_nS,_hS))?new T0(2):new T1(1,_fg(_hT,function(_nT){var _nU=new T2(1,_nS,_nT);if(!_hN(new T2(0,_eo,_et),_nU,new T2(1,_nr,new T2(1,_nq,new T2(1,_np,new T2(1,_no,new T2(1,_nn,new T2(1,_nm,new T2(1,_nl,new T2(1,_nk,new T2(1,_nj,new T2(1,_ni,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_nt,new T1(4,_nU));}) : (++C,A1(_nt,new T1(4,_nU)));}else{return C > 19 ? new F(function(){return A1(_nt,new T1(2,_nU));}) : (++C,A1(_nt,new T1(2,_nU)));}}));};return _dI(new T1(0,_nR),_nK);});return _dI(new T1(0,function(_nV){if(!_hN(_ej,_nV,_nh)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_nt,new T1(2,new T2(1,_nV,__Z)));}) : (++C,A1(_nt,new T1(2,new T2(1,_nV,__Z))));}}),_nJ);});return _dI(new T1(0,function(_nW){return (E(_nW)==34)?E(_nH):new T0(2);}),_nI);});return _dI(new T1(0,function(_nX){return (E(_nX)==39)?E(new T1(0,_nB)):new T0(2);}),_nG);});return _dI(new T1(1,function(_nY){return (E(_nY)._==0)?E(_nu):new T0(2);}),_nv);},_nZ=function(_o0,_o1){var _o2=new T(function(){var _o3=new T(function(){var _o4=function(_o5){var _o6=new T(function(){var _o7=new T(function(){return B(A1(_o1,_o5));});return B(_ns(function(_o8){var _o9=E(_o8);return (_o9._==2)?(!_ee(_o9.a,_ed))?new T0(2):E(_o7):new T0(2);}));}),_oa=function(_ob){return E(_o6);};return new T1(1,function(_oc){return C > 19 ? new F(function(){return A2(_ml,_oc,_oa);}) : (++C,A2(_ml,_oc,_oa));});};return B(A2(_o0,0,_o4));});return B(_ns(function(_od){var _oe=E(_od);return (_oe._==2)?(!_ee(_oe.a,_ec))?new T0(2):E(_o3):new T0(2);}));}),_of=function(_og){return E(_o2);};return function(_oh){return C > 19 ? new F(function(){return A2(_ml,_oh,_of);}) : (++C,A2(_ml,_oh,_of));};},_oi=function(_oj,_ok){var _ol=function(_om){var _on=new T(function(){return B(A1(_oj,_om));}),_oo=function(_op){return _dI(B(A1(_on,_op)),new T(function(){return new T1(1,_nZ(_ol,_op));}));};return _oo;},_oq=new T(function(){return B(A1(_oj,_ok));}),_or=function(_os){return _dI(B(A1(_oq,_os)),new T(function(){return new T1(1,_nZ(_ol,_os));}));};return _or;},_ot=function(_ou,_ov){var _ow=function(_ox,_oy){var _oz=function(_oA){return C > 19 ? new F(function(){return A1(_oy,new T(function(){return  -E(_oA);}));}) : (++C,A1(_oy,new T(function(){return  -E(_oA);})));},_oB=new T(function(){return B(_ns(function(_oC){return C > 19 ? new F(function(){return A3(_ou,_oC,_ox,_oz);}) : (++C,A3(_ou,_oC,_ox,_oz));}));}),_oD=function(_oE){return E(_oB);},_oF=function(_oG){return C > 19 ? new F(function(){return A2(_ml,_oG,_oD);}) : (++C,A2(_ml,_oG,_oD));},_oH=new T(function(){return B(_ns(function(_oI){var _oJ=E(_oI);if(_oJ._==4){var _oK=E(_oJ.a);if(!_oK._){return C > 19 ? new F(function(){return A3(_ou,_oJ,_ox,_oy);}) : (++C,A3(_ou,_oJ,_ox,_oy));}else{if(E(_oK.a)==45){if(!E(_oK.b)._){return E(new T1(1,_oF));}else{return C > 19 ? new F(function(){return A3(_ou,_oJ,_ox,_oy);}) : (++C,A3(_ou,_oJ,_ox,_oy));}}else{return C > 19 ? new F(function(){return A3(_ou,_oJ,_ox,_oy);}) : (++C,A3(_ou,_oJ,_ox,_oy));}}}else{return C > 19 ? new F(function(){return A3(_ou,_oJ,_ox,_oy);}) : (++C,A3(_ou,_oJ,_ox,_oy));}}));}),_oL=function(_oM){return E(_oH);};return new T1(1,function(_oN){return C > 19 ? new F(function(){return A2(_ml,_oN,_oL);}) : (++C,A2(_ml,_oN,_oL));});};return _oi(_ow,_ov);},_oO=function(_oP){var _oQ=E(_oP);if(!_oQ._){var _oR=_oQ.b,_oS=new T(function(){return _gX(new T(function(){return _3m(E(_oQ.a));}),new T(function(){return _gJ(_oR,0);},1),_d1(_gO,_oR));});return new T1(1,_oS);}else{return (E(_oQ.b)._==0)?(E(_oQ.c)._==0)?new T1(1,new T(function(){return _he(_gI,_oQ.a);})):__Z:__Z;}},_oT=function(_oU,_oV){return new T0(2);},_oW=function(_oX){var _oY=E(_oX);if(_oY._==5){var _oZ=_oO(_oY.a);if(!_oZ._){return _oT;}else{var _p0=new T(function(){return _3p(_oZ.a);});return function(_p1,_p2){return C > 19 ? new F(function(){return A1(_p2,_p0);}) : (++C,A1(_p2,_p0));};}}else{return _oT;}},_p3=function(_p4){return _ot(_oW,_p4);},_p5=new T(function(){return unCStr("[");}),_p6=function(_p7,_p8){var _p9=function(_pa,_pb){var _pc=new T(function(){return B(A1(_pb,__Z));}),_pd=new T(function(){var _pe=function(_pf){return _p9(true,function(_pg){return C > 19 ? new F(function(){return A1(_pb,new T2(1,_pf,_pg));}) : (++C,A1(_pb,new T2(1,_pf,_pg)));});};return B(A2(_p7,0,_pe));}),_ph=new T(function(){return B(_ns(function(_pi){var _pj=E(_pi);if(_pj._==2){var _pk=E(_pj.a);if(!_pk._){return new T0(2);}else{var _pl=_pk.b;switch(E(_pk.a)){case 44:return (E(_pl)._==0)?(!E(_pa))?new T0(2):E(_pd):new T0(2);case 93:return (E(_pl)._==0)?E(_pc):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_pm=function(_pn){return E(_ph);};return new T1(1,function(_po){return C > 19 ? new F(function(){return A2(_ml,_po,_pm);}) : (++C,A2(_ml,_po,_pm));});},_pp=function(_pq,_pr){return C > 19 ? new F(function(){return _ps(_pr);}) : (++C,_ps(_pr));},_ps=function(_pt){var _pu=new T(function(){var _pv=new T(function(){var _pw=new T(function(){var _px=function(_py){return _p9(true,function(_pz){return C > 19 ? new F(function(){return A1(_pt,new T2(1,_py,_pz));}) : (++C,A1(_pt,new T2(1,_py,_pz)));});};return B(A2(_p7,0,_px));});return _dI(_p9(false,_pt),_pw);});return B(_ns(function(_pA){var _pB=E(_pA);return (_pB._==2)?(!_ee(_pB.a,_p5))?new T0(2):E(_pv):new T0(2);}));}),_pC=function(_pD){return E(_pu);};return _dI(new T1(1,function(_pE){return C > 19 ? new F(function(){return A2(_ml,_pE,_pC);}) : (++C,A2(_ml,_pE,_pC));}),new T(function(){return new T1(1,_nZ(_pp,_pt));}));};return C > 19 ? new F(function(){return _ps(_p8);}) : (++C,_ps(_p8));},_pF=function(_pG){var _pH=function(_pI){return E(new T2(3,_pG,_eH));};return new T1(1,function(_pJ){return C > 19 ? new F(function(){return A2(_ml,_pJ,_pH);}) : (++C,A2(_ml,_pJ,_pH));});},_pK=new T(function(){return B(_p6(_p3,_pF));}),_pL=new T(function(){return unCStr("Prelude.read: ambiguous parse");}),_pM=new T(function(){return unCStr("Prelude.read: no parse");}),_pN=function(_pO){while(1){var _pP=(function(_pQ){var _pR=E(_pQ);if(!_pR._){return __Z;}else{var _pS=_pR.b,_pT=E(_pR.a);if(!E(_pT.b)._){return new T2(1,_pT.a,new T(function(){return _pN(_pS);}));}else{_pO=_pS;return __continue;}}})(_pO);if(_pP!=__continue){return _pP;}}},_pU=function(_pV,_pW,_){var _pX=new T(function(){var _pY=_pN(_dy(_pK,new T(function(){return fromJSStr(E(_pV));})));if(!_pY._){return err(_pM);}else{if(!E(_pY.b)._){return E(_pY.a);}else{return err(_pL);}}}),_pZ=E(_pW);if(_pZ._==3){var _q0=E(_pZ.a);if(!_q0._){return new T2(0,_pX,__Z);}else{var _q1=E(_q0.a);if(_q1._==3){if(!E(_q0.b)._){var _q2=_aj(_d1(_dh,_q1.a),_);return new T2(0,_pX,new T2(1,_q2,__Z));}else{return new T2(0,_pX,__Z);}}else{return new T2(0,_pX,__Z);}}}else{return new T2(0,_pX,__Z);}},_q3=function(_q4,_){var _q5=E(_q4);return _pU(_q5.a,_q5.b,_);},_q6=function(_q7,_q8){var _q9=E(_q7);if(!_q9._){return __Z;}else{var _qa=_q9.a,_qb=E(_q8);return (_qb==1)?new T2(1,function(_){return _q3(_qa,_);},__Z):new T2(1,function(_){return _q3(_qa,_);},new T(function(){return _q6(_q9.b,_qb-1|0);}));}},_qc=function(_){var _qd=_6K("Error decoding tree data");return _6J(_);},_qe=function(_qf,_){var _qg=E(_qf);if(!_qg._){return __Z;}else{var _qh=B(A1(_qg.a,_)),_qi=_qe(_qg.b,_);return new T2(1,_qh,_qi);}},_qj=new T(function(){return B(_cQ("Ajax.hs:(97,5)-(101,81)|function decodeMenu"));}),_qk=new T(function(){return _c8(new T1(0,new T(function(){return unCStr("Error decoding tree data");})),_bV);}),_ql=function(_qm,_){var _qn=E(_qm);if(_qn._==4){var _qo=_qn.a,_qp=_ar(_1L,"lin",_qo);if(!_qp._){return E(_aq);}else{var _qq=function(_,_qr){var _qs=_ar(_1L,"menu",_qo);if(!_qs._){return E(_aq);}else{var _qt=E(_qs.a);if(_qt._==4){var _qu=_qt.a,_qv=_gJ(_qu,0),_qw=function(_,_qx){var _qy=_ar(_1L,"grammar",_qo);if(!_qy._){var _qz=_qc(_);return E(_qk);}else{var _qA=_ar(_1L,"tree",_qo);if(!_qA._){var _qB=_qc(_);return E(_qk);}else{return new T4(0,new T(function(){var _qC=E(_qy.a);if(_qC._==1){return fromJSStr(_qC.a);}else{return E(_dg);}}),new T(function(){var _qD=E(_qA.a);if(_qD._==1){return fromJSStr(_qD.a);}else{return E(_dg);}}),_qr,new T1(0,new T(function(){var _qE=E(_qx);if(!_qE._){return new T0(1);}else{return B(_ac(_qE));}})));}}};if(0>=_qv){var _qF=_qe(__Z,_);return _qw(_,_qF);}else{var _qG=_qe(_q6(_qu,_qv),_);return _qw(_,_qG);}}else{return E(_qj);}}},_qH=E(_qp.a);if(_qH._==3){return _qq(_,new T(function(){return _d1(_dc,_qH.a);}));}else{return _qq(_,__Z);}}}else{return E(_aq);}},_qI=function(_qJ){var _qK=E(_qJ);return (_qK._==0)?E(_aq):E(_qK.a);},_qL=new T(function(){return _c8(new T1(0,new T(function(){return unCStr("Error decoding message data");})),_bV);}),_qM=new T(function(){return fromJSStr("Invalid JSON!");}),_qN=new T(function(){return _c8(new T1(0,_qM),_bV);}),_qO=new T(function(){return unAppCStr("Error ",_qM);}),_qP=new T(function(){return B(_cQ("Ajax.hs:131:5-35|function getJustBool"));}),_qQ=function(_qR,_){var _qS=jsParseJSON(_qR);if(!_qS._){var _qT=_6K(toJSStr(E(_qO)));return E(_qN);}else{var _qU=_qS.a,_qV=E(_qU);if(_qV._==4){var _qW=_ar(_1L,"a",_qV.a);}else{var _qW=__Z;}var _qX=_ql(_qI(_qW),_),_qY=_qX;if(_qU._==4){var _qZ=_ar(_1L,"b",_qU.a);}else{var _qZ=__Z;}var _r0=_ql(_qI(_qZ),_);if(_qU._==4){var _r1=_qU.a,_r2=_ar(_1L,"success",_r1);if(!_r2._){var _r3=_6L(_);return E(_qL);}else{var _r4=_ar(_1L,"score",_r1);if(!_r4._){var _r5=_6L(_);return E(_qL);}else{if(!E(_qW)._){var _r6=_6L(_);return E(_qL);}else{if(!E(_qZ)._){var _r7=_6L(_);return E(_qL);}else{return new T4(0,new T(function(){var _r8=E(_r2.a);if(_r8._==2){return E(_r8.a);}else{return E(_qP);}}),new T(function(){var _r9=E(_r4.a);if(!_r9._){var _ra=_6x(_3A,_r9.a),_rb=_ra.a;if(E(_ra.b)>=0){return E(_rb);}else{return E(_rb)-1|0;}}else{return E(_df);}}),_qY,_r0);}}}}}else{var _rc=_6L(_);return E(_qL);}}},_rd=new T(function(){return JSON.stringify;}),_re=function(_rf,_rg){var _rh=E(_rg);switch(_rh._){case 0:return new T2(0,new T(function(){return jsShow(_rh.a);}),_rf);case 1:return new T2(0,new T(function(){var _ri=E(_rd)(_rh.a);return String(_ri);}),_rf);case 2:return (!E(_rh.a))?new T2(0,"false",_rf):new T2(0,"true",_rf);case 3:var _rj=E(_rh.a);if(!_rj._){return new T2(0,"[",new T2(1,"]",_rf));}else{var _rk=new T(function(){var _rl=new T(function(){var _rm=function(_rn){var _ro=E(_rn);if(!_ro._){return E(new T2(1,"]",_rf));}else{var _rp=new T(function(){var _rq=_re(new T(function(){return _rm(_ro.b);}),_ro.a);return new T2(1,_rq.a,_rq.b);});return new T2(1,",",_rp);}};return _rm(_rj.b);}),_rr=_re(_rl,_rj.a);return new T2(1,_rr.a,_rr.b);});return new T2(0,"[",_rk);}break;case 4:var _rs=E(_rh.a);if(!_rs._){return new T2(0,"{",new T2(1,"}",_rf));}else{var _rt=E(_rs.a),_ru=new T(function(){var _rv=new T(function(){var _rw=function(_rx){var _ry=E(_rx);if(!_ry._){return E(new T2(1,"}",_rf));}else{var _rz=E(_ry.a),_rA=new T(function(){var _rB=_re(new T(function(){return _rw(_ry.b);}),_rz.b);return new T2(1,_rB.a,_rB.b);});return new T2(1,",",new T2(1,"\"",new T2(1,_rz.a,new T2(1,"\"",new T2(1,":",_rA)))));}};return _rw(_rs.b);}),_rC=_re(_rv,_rt.b);return new T2(1,_rC.a,_rC.b);});return new T2(0,"{",new T2(1,new T(function(){var _rD=E(_rd)(E(_rt.a));return String(_rD);}),new T2(1,":",_ru)));}break;default:return new T2(0,"null",_rf);}},_rE=new T(function(){return toJSStr(__Z);}),_rF=function(_rG){var _rH=_re(__Z,_rG),_rI=jsCat(new T2(1,_rH.a,_rH.b),E(_rE));return E(_rI);},_rJ=function(_rK,_rL){return new T2(1,new T2(0,"grammar",new T(function(){return new T1(1,toJSStr(E(_rK)));})),new T2(1,new T2(0,"tree",new T(function(){return new T1(1,toJSStr(E(_rL)));})),__Z));},_rM=function(_rN){var _rO=E(_rN);return new T1(4,E(_rJ(_rO.a,_rO.b)));},_rP=function(_rQ){var _rR=E(_rQ);if(!_rR._){return _rF(new T0(5));}else{return _rF(new T1(4,E(new T2(1,new T2(0,"score",new T(function(){return new T1(0,E(_rR.a));})),new T2(1,new T2(0,"a",new T(function(){return _rM(_rR.b);})),new T2(1,new T2(0,"b",new T(function(){return _rM(_rR.c);})),__Z))))));}},_rS=function(_rT){return E(E(_rT).a);},_rU=function(_rV,_rW,_rX,_rY,_rZ){return C > 19 ? new F(function(){return A2(_rW,_rX,new T2(1,B(A2(_rS,_rV,E(_rZ))),E(_rY)));}) : (++C,A2(_rW,_rX,new T2(1,B(A2(_rS,_rV,E(_rZ))),E(_rY))));},_s0=function(_s1){return E(E(_s1).a);},_s2=function(_s3){return E(E(_s3).a);},_s4=function(_s5){return E(E(_s5).a);},_s6=function(_s7){return E(E(_s7).b);},_s8=new T(function(){return unCStr("base");}),_s9=new T(function(){return unCStr("GHC.IO.Exception");}),_sa=new T(function(){return unCStr("IOException");}),_sb=function(_sc){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_s8,_s9,_sa),__Z,__Z));},_sd=new T(function(){return unCStr(": ");}),_se=new T(function(){return unCStr(")");}),_sf=new T(function(){return unCStr(" (");}),_sg=new T(function(){return unCStr("interrupted");}),_sh=new T(function(){return unCStr("system error");}),_si=new T(function(){return unCStr("unsatisified constraints");}),_sj=new T(function(){return unCStr("user error");}),_sk=new T(function(){return unCStr("permission denied");}),_sl=new T(function(){return unCStr("illegal operation");}),_sm=new T(function(){return unCStr("end of file");}),_sn=new T(function(){return unCStr("resource exhausted");}),_so=new T(function(){return unCStr("resource busy");}),_sp=new T(function(){return unCStr("does not exist");}),_sq=new T(function(){return unCStr("already exists");}),_sr=new T(function(){return unCStr("resource vanished");}),_ss=new T(function(){return unCStr("timeout");}),_st=new T(function(){return unCStr("unsupported operation");}),_su=new T(function(){return unCStr("hardware fault");}),_sv=new T(function(){return unCStr("inappropriate type");}),_sw=new T(function(){return unCStr("invalid argument");}),_sx=new T(function(){return unCStr("failed");}),_sy=new T(function(){return unCStr("protocol error");}),_sz=function(_sA,_sB){switch(E(_sA)){case 0:return _0(_sq,_sB);case 1:return _0(_sp,_sB);case 2:return _0(_so,_sB);case 3:return _0(_sn,_sB);case 4:return _0(_sm,_sB);case 5:return _0(_sl,_sB);case 6:return _0(_sk,_sB);case 7:return _0(_sj,_sB);case 8:return _0(_si,_sB);case 9:return _0(_sh,_sB);case 10:return _0(_sy,_sB);case 11:return _0(_sx,_sB);case 12:return _0(_sw,_sB);case 13:return _0(_sv,_sB);case 14:return _0(_su,_sB);case 15:return _0(_st,_sB);case 16:return _0(_ss,_sB);case 17:return _0(_sr,_sB);default:return _0(_sg,_sB);}},_sC=new T(function(){return unCStr("}");}),_sD=new T(function(){return unCStr("{handle: ");}),_sE=function(_sF,_sG,_sH,_sI,_sJ,_sK){var _sL=new T(function(){var _sM=new T(function(){var _sN=new T(function(){var _sO=E(_sI);if(!_sO._){return E(_sK);}else{var _sP=new T(function(){return _0(_sO,new T(function(){return _0(_se,_sK);},1));},1);return _0(_sf,_sP);}},1);return _sz(_sG,_sN);}),_sQ=E(_sH);if(!_sQ._){return E(_sM);}else{return _0(_sQ,new T(function(){return _0(_sd,_sM);},1));}}),_sR=E(_sJ);if(!_sR._){var _sS=E(_sF);if(!_sS._){return E(_sL);}else{var _sT=E(_sS.a);if(!_sT._){var _sU=new T(function(){var _sV=new T(function(){return _0(_sC,new T(function(){return _0(_sd,_sL);},1));},1);return _0(_sT.a,_sV);},1);return _0(_sD,_sU);}else{var _sW=new T(function(){var _sX=new T(function(){return _0(_sC,new T(function(){return _0(_sd,_sL);},1));},1);return _0(_sT.a,_sX);},1);return _0(_sD,_sW);}}}else{return _0(_sR.a,new T(function(){return _0(_sd,_sL);},1));}},_sY=function(_sZ){var _t0=E(_sZ);return _sE(_t0.a,_t0.b,_t0.c,_t0.d,_t0.f,__Z);},_t1=function(_t2,_t3){var _t4=E(_t2);return _sE(_t4.a,_t4.b,_t4.c,_t4.d,_t4.f,_t3);},_t5=new T(function(){return new T5(0,_sb,new T3(0,function(_t6,_t7,_t8){var _t9=E(_t7);return _sE(_t9.a,_t9.b,_t9.c,_t9.d,_t9.f,_t8);},_sY,function(_ta,_tb){return _2P(_t1,_ta,_tb);}),_tc,function(_td){var _te=E(_td);return _2w(_2u(_te.a),_sb,_te.b);},_sY);}),_tc=function(_tf){return new T2(0,_t5,_tf);},_tg=function(_th,_){var _ti=_th["type"],_tj=String(_ti),_tk=strEq(_tj,"network");if(!E(_tk)){var _tl=strEq(_tj,"http");if(!E(_tl)){var _tm=new T(function(){var _tn=new T(function(){return unAppCStr("unknown type of ajax error: ",new T(function(){return fromJSStr(_tj);}));});return _tc(new T6(0,__Z,7,__Z,_tn,__Z,__Z));});return die(_tm);}else{var _to=_th["status"],_tp=_th["status-text"];return new T2(1,new T(function(){var _tq=Number(_to);return jsTrunc(_tq);}),new T(function(){return String(_tp);}));}}else{return __Z;}},_tr=function(_ts,_){var _tt=E(_ts);if(!_tt._){return __Z;}else{var _tu=_tg(E(_tt.a),_),_tv=_tr(_tt.b,_);return new T2(1,_tu,_tv);}},_tw=function(_tx,_){var _ty=__arr2lst(0,_tx);return _tr(_ty,_);},_tz=new T2(0,function(_tA,_){return _tg(E(_tA),_);},function(_tB,_){return _tw(E(_tB),_);}),_tC=function(_tD){return E(E(_tD).a);},_tE=function(_tF){var _tG=B(A1(_tF,_));return E(_tG);},_tH=new T(function(){return _tE(function(_){return __jsNull();});}),_tI=function(_tJ,_tK,_){var _tL=__eq(_tK,E(_tH));if(!E(_tL)){var _tM=__isUndef(_tK);if(!E(_tM)){var _tN=B(A3(_tC,_tJ,_tK,_));return new T1(1,_tN);}else{return __Z;}}else{return __Z;}},_tO=function(_tP,_tQ,_){var _tR=__arr2lst(0,_tQ),_tS=function(_tT,_){var _tU=E(_tT);if(!_tU._){return __Z;}else{var _tV=_tU.b,_tW=E(_tU.a),_tX=__eq(_tW,E(_tH));if(!E(_tX)){var _tY=__isUndef(_tW);if(!E(_tY)){var _tZ=B(A3(_tC,_tP,_tW,_)),_u0=_tS(_tV,_);return new T2(1,new T1(1,_tZ),_u0);}else{var _u1=_tS(_tV,_);return new T2(1,__Z,_u1);}}else{var _u2=_tS(_tV,_);return new T2(1,__Z,_u2);}}};return _tS(_tR,_);},_u3=new T2(0,function(_u4,_){return _tI(_tz,E(_u4),_);},function(_u5,_){return _tO(_tz,E(_u5),_);}),_u6=function(_u7,_u8,_){var _u9=B(A2(_u7,new T(function(){var _ua=E(_u8),_ub=__eq(_ua,E(_tH));if(!E(_ub)){var _uc=__isUndef(_ua);if(!E(_uc)){return new T1(1,_ua);}else{return __Z;}}else{return __Z;}}),_));return _tH;},_ud=new T2(0,_u6,function(_ue){return 2;}),_uf=function(_ug){return E(E(_ug).a);},_uh=function(_ui,_uj,_uk,_ul){var _um=new T(function(){return B(A1(_uk,new T(function(){var _un=B(A3(_tC,_ui,_ul,_));return E(_un);})));});return C > 19 ? new F(function(){return A2(_uf,_uj,_um);}) : (++C,A2(_uf,_uj,_um));},_uo=function(_up){return E(E(_up).b);},_uq=new T(function(){return err(new T(function(){return unCStr("Prelude.undefined");}));}),_ur=function(_us,_ut,_uu){var _uv=__createJSFunc(1+B(A2(_uo,_ut,new T(function(){return B(A1(_uu,_uq));})))|0,function(_uw){return C > 19 ? new F(function(){return _uh(_us,_ut,_uu,_uw);}) : (++C,_uh(_us,_ut,_uu,_uw));});return E(_uv);},_ux=function(_uy,_uz,_uA){return _ur(_uy,_uz,_uA);},_uB=function(_uC,_uD,_uE){var _uF=__lst2arr(_d1(function(_uG){return _ux(_uC,_uD,_uG);},_uE));return E(_uF);},_uH=new T2(0,function(_uI){return _ur(_u3,_ud,_uI);},function(_uJ){return _uB(_u3,_ud,_uJ);}),_uK=function(_uL,_){var _uM=E(_uL);if(!_uM._){return __Z;}else{var _uN=_uK(_uM.b,_);return new T2(1,0,_uN);}},_uO=function(_uP,_){var _uQ=__arr2lst(0,_uP);return _uK(_uQ,_);},_uR=function(_uS,_){return _uO(E(_uS),_);},_uT=function(_uU,_){return _6J(_);},_uV=function(_uW,_uX,_uY,_){var _uZ=__apply(_uX,E(_uY));return C > 19 ? new F(function(){return A3(_tC,_uW,_uZ,_);}) : (++C,A3(_tC,_uW,_uZ,_));},_v0=function(_v1,_v2,_v3,_){return C > 19 ? new F(function(){return _uV(_v1,E(_v2),_v3,_);}) : (++C,_uV(_v1,E(_v2),_v3,_));},_v4=function(_v5,_v6,_v7,_){return C > 19 ? new F(function(){return _v0(_v5,_v6,_v7,_);}) : (++C,_v0(_v5,_v6,_v7,_));},_v8=function(_v9,_va,_){return C > 19 ? new F(function(){return _v4(new T2(0,_uT,_uR),_v9,_va,_);}) : (++C,_v4(new T2(0,_uT,_uR),_v9,_va,_));},_vb=function(_vc){return E(E(_vc).c);},_vd=(function(method, uri, mimeout, responseType, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, uri);xhr.responseType = responseType;if(mimeout != '') {xhr.setRequestHeader('Content-type', mimeout);}xhr.addEventListener('load', function() {if(xhr.status < 400) {cb(null, xhr.response);}else {cb({'type':'http', 'status':xhr.status, 'status-text': xhr.statusText}, null);}});xhr.addEventListener('error', function() {if(xhr.status != 0) {cb({'type':'http', 'status':xhr.status, 'status-text': xhr.statusText}, null);} else {cb({'type':'network'}, null);}});xhr.send(postdata);}),_ve=function(_vf){return E(E(_vf).b);},_vg=function(_vh){return E(E(_vh).b);},_vi=new T(function(){return B(_cQ("src/Haste/Ajax.hs:(61,7)-(63,60)|case"));}),_vj=function(_vk){return E(E(_vk).c);},_vl=new T1(1,__Z),_vm=function(_){return nMV(_vl);},_vn=new T0(2),_vo=function(_vp,_vq,_vr){var _vs=function(_vt){var _vu=function(_){var _vv=E(_vq),_vw=rMV(_vv),_vx=E(_vw);if(!_vx._){var _vy=new T(function(){var _vz=new T(function(){return B(A1(_vt,0));});return _0(_vx.b,new T2(1,new T2(0,_vr,function(_vA){return E(_vz);}),__Z));}),_=wMV(_vv,new T2(0,_vx.a,_vy));return _vn;}else{var _vB=E(_vx.a);if(!_vB._){var _=wMV(_vv,new T2(0,_vr,__Z));return new T(function(){return B(A1(_vt,0));});}else{var _=wMV(_vv,new T1(1,_vB.b));return new T1(1,new T2(1,new T(function(){return B(A1(_vt,0));}),new T2(1,new T(function(){return B(A2(_vB.a,_vr,_1v));}),__Z)));}}};return new T1(0,_vu);};return C > 19 ? new F(function(){return A2(_ve,_vp,_vs);}) : (++C,A2(_ve,_vp,_vs));},_vC=function(_vD){return E(E(_vD).d);},_vE=function(_vF,_vG){var _vH=function(_vI){var _vJ=function(_){var _vK=E(_vG),_vL=rMV(_vK),_vM=E(_vL);if(!_vM._){var _vN=_vM.a,_vO=E(_vM.b);if(!_vO._){var _=wMV(_vK,_vl);return new T(function(){return B(A1(_vI,_vN));});}else{var _vP=E(_vO.a),_=wMV(_vK,new T2(0,_vP.a,_vO.b));return new T1(1,new T2(1,new T(function(){return B(A1(_vI,_vN));}),new T2(1,new T(function(){return B(A1(_vP.b,_1v));}),__Z)));}}else{var _vQ=new T(function(){var _vR=function(_vS){var _vT=new T(function(){return B(A1(_vI,_vS));});return function(_vU){return E(_vT);};};return _0(_vM.a,new T2(1,_vR,__Z));}),_=wMV(_vK,new T1(1,_vQ));return _vn;}};return new T1(0,_vJ);};return C > 19 ? new F(function(){return A2(_ve,_vF,_vH);}) : (++C,A2(_ve,_vF,_vH));},_vV=function(_vW,_vX,_vY,_vZ,_w0,_w1){var _w2=_s2(_vW),_w3=new T(function(){return _ve(_vW);}),_w4=new T(function(){return _vg(_w2);}),_w5=_s4(_w2),_w6=new T(function(){return _s6(_vY);}),_w7=new T(function(){var _w8=function(_w9){var _wa=E(_vZ),_wb=strEq(E(_f),_wa);if(!E(_wb)){var _wc=_wa;}else{var _wc=B(A2(_vj,_vX,0));}return function(_uw){return C > 19 ? new F(function(){return _rU(_uH,_v8,_vd,new T2(1,E(_tH),new T2(1,B(A2(_vC,_vY,0)),new T2(1,_wc,new T2(1,E(_w1),new T2(1,_w9,__Z))))),_uw);}) : (++C,_rU(_uH,_v8,_vd,new T2(1,E(_tH),new T2(1,B(A2(_vC,_vY,0)),new T2(1,_wc,new T2(1,E(_w1),new T2(1,_w9,__Z))))),_uw));};},_wd=function(_we,_wf){var _wg=E(_vZ),_wh=strEq(E(_f),_wg);if(!E(_wh)){var _wi=_wg;}else{var _wi=B(A2(_vj,_vX,0));}return function(_uw){return C > 19 ? new F(function(){return _rU(_uH,_v8,_vd,new T2(1,E(_we),new T2(1,B(A2(_vC,_vY,0)),new T2(1,_wi,new T2(1,E(_w1),new T2(1,_wf,__Z))))),_uw);}) : (++C,_rU(_uH,_v8,_vd,new T2(1,E(_we),new T2(1,B(A2(_vC,_vY,0)),new T2(1,_wi,new T2(1,E(_w1),new T2(1,_wf,__Z))))),_uw));};},_wj=E(_w0);switch(_wj._){case 0:return _w8("GET");break;case 1:return _w8("DELETE");break;case 2:return _wd(new T(function(){return B(A2(_rS,_s0(_vX),_wj.a));}),"POST");break;default:return _wd(new T(function(){return B(A2(_rS,_s0(_vX),_wj.a));}),"PUT");}}),_wk=function(_wl){var _wm=new T(function(){return B(A1(_w3,new T(function(){return B(_vE(_1E,_wl));})));}),_wn=new T(function(){var _wo=new T(function(){var _wp=function(_wq,_wr,_){var _ws=E(_wr);if(!_ws._){var _wt=E(_wq);if(!_wt._){return E(_vi);}else{return _a(new T(function(){return B(A(_vo,[_1E,_wl,new T1(0,_wt.a),_1v]));}),__Z,_);}}else{var _wu=B(A3(_tC,_w6,_ws.a,_));return _a(new T(function(){return B(A(_vo,[_1E,_wl,new T1(1,_wu),_1v]));}),__Z,_);}};return B(A1(_w7,_wp));});return B(A1(_w4,_wo));});return C > 19 ? new F(function(){return A3(_vb,_w5,_wn,_wm);}) : (++C,A3(_vb,_w5,_wn,_wm));};return C > 19 ? new F(function(){return A3(_1g,_w5,new T(function(){return B(A2(_vg,_w2,_vm));}),_wk);}) : (++C,A3(_1g,_w5,new T(function(){return B(A2(_vg,_w2,_vm));}),_wk));},_wv=new T(function(){return err(new T(function(){return unCStr("AjaxError");}));}),_ww=function(_wx){var _wy=new T(function(){return _rP(_wx);}),_wz=new T(function(){return toJSStr(unAppCStr("Send client message ",new T(function(){return fromJSStr(E(_wy));})));}),_wA=new T(function(){return B(_vV(_1E,_v,_v,_f,new T1(2,_wy),"http://localhost:8080/cgi"));}),_wB=function(_wC){var _wD=function(_){var _wE=_6K(E(_wz));return new T(function(){var _wF=function(_wG){var _wH=E(_wG);if(!_wH._){return E(_wv);}else{var _wI=function(_){var _wJ=_qQ(E(_wH.a),_);return new T(function(){return B(A1(_wC,_wJ));});};return new T1(0,_wI);}};return B(A1(_wA,_wF));});};return new T1(0,_wD);};return _wB;},_wK=new T(function(){return unAppCStr(") is outside of enumeration\'s range (0,",new T(function(){return _i8(0,2,new T(function(){return unCStr(")");}));}));}),_wL=function(_wM){return err(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return _i8(0,_wM,_wK);})));},_wN=function(_wO,_){return new T(function(){var _wP=Number(E(_wO)),_wQ=jsTrunc(_wP);if(_wQ<0){return _wL(_wQ);}else{if(_wQ>2){return _wL(_wQ);}else{return _wQ;}}});},_wR=new T3(0,0,0,0),_wS=new T(function(){return jsGetMouseCoords;}),_wT=function(_wU,_){var _wV=E(_wU);if(!_wV._){return __Z;}else{var _wW=_wT(_wV.b,_);return new T2(1,new T(function(){var _wX=Number(E(_wV.a));return jsTrunc(_wX);}),_wW);}},_wY=function(_wZ,_){var _x0=__arr2lst(0,_wZ);return _wT(_x0,_);},_x1=function(_x2,_){return new T(function(){var _x3=Number(E(_x2));return jsTrunc(_x3);});},_x4=new T2(0,_x1,function(_x5,_){return _wY(E(_x5),_);}),_x6=function(_x7,_){var _x8=E(_x7);if(!_x8._){return __Z;}else{var _x9=_x6(_x8.b,_);return new T2(1,_x8.a,_x9);}},_xa=new T(function(){return _tc(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9");}),__Z,__Z));}),_xb=function(_){return die(_xa);},_xc=function(_xd,_xe,_xf,_){var _xg=__arr2lst(0,_xf),_xh=_x6(_xg,_),_xi=E(_xh);if(!_xi._){return _xb(_);}else{var _xj=E(_xi.b);if(!_xj._){return _xb(_);}else{if(!E(_xj.b)._){var _xk=B(A3(_tC,_xd,_xi.a,_)),_xl=B(A3(_tC,_xe,_xj.a,_));return new T2(0,_xk,_xl);}else{return _xb(_);}}}},_xm=function(_xn,_xo,_){if(E(_xn)==7){var _xp=E(_wS)(_xo),_xq=_xc(_x4,_x4,_xp,_),_xr=_xo["deltaX"],_xs=_xo["deltaY"],_xt=_xo["deltaZ"];return new T(function(){return new T3(0,E(_xq),E(__Z),E(new T3(0,_xr,_xs,_xt)));});}else{var _xu=E(_wS)(_xo),_xv=_xc(_x4,_x4,_xu,_),_xw=_xo["button"],_xx=__eq(_xw,E(_tH));if(!E(_xx)){var _xy=__isUndef(_xw);if(!E(_xy)){var _xz=_wN(_xw,_);return new T(function(){return new T3(0,E(_xv),E(new T1(1,_xz)),E(_wR));});}else{return new T(function(){return new T3(0,E(_xv),E(__Z),E(_wR));});}}else{return new T(function(){return new T3(0,E(_xv),E(__Z),E(_wR));});}}},_xA=new T2(0,function(_xB){switch(E(_xB)){case 0:return "click";case 1:return "dblclick";case 2:return "mousedown";case 3:return "mouseup";case 4:return "mousemove";case 5:return "mouseover";case 6:return "mouseout";default:return "wheel";}},function(_xC,_xD,_){return _xm(_xC,E(_xD),_);}),_xE=function(_xF){return E(_xF);},_xG=function(_xH,_xI,_){var _xJ=B(A1(_xH,_)),_xK=B(A1(_xI,_));return new T(function(){return B(A1(_xJ,_xK));});},_xL=function(_xM,_){return _xM;},_xN=function(_xO,_xP,_){var _xQ=B(A1(_xO,_));return C > 19 ? new F(function(){return A1(_xP,_);}) : (++C,A1(_xP,_));},_xR=new T(function(){return E(_t5);}),_xS=function(_xT){return new T6(0,__Z,7,__Z,_xT,__Z,__Z);},_xU=function(_xV,_){var _xW=new T(function(){return B(A2(_c3,_xR,new T(function(){return B(A1(_xS,_xV));})));});return die(_xW);},_xX=function(_xY,_){return _xU(_xY,_);},_xZ=new T2(0,new T5(0,new T5(0,new T2(0,_1o,function(_y0,_y1,_){var _y2=B(A1(_y1,_));return _y0;}),_xL,_xG,_xN,function(_y3,_y4,_){var _y5=B(A1(_y3,_)),_y6=B(A1(_y4,_));return _y5;}),function(_y7,_y8,_){var _y9=B(A1(_y7,_));return C > 19 ? new F(function(){return A2(_y8,_y9,_);}) : (++C,A2(_y8,_y9,_));},_xN,_xL,function(_ya){return C > 19 ? new F(function(){return A1(_xX,_ya);}) : (++C,A1(_xX,_ya));}),_1C),_yb=new T2(0,_xZ,_xL),_yc=function(_yd){return E(E(_yd).d);},_ye=new T2(0,_1C,function(_yf,_yg){return C > 19 ? new F(function(){return A2(_yc,_s4(_yf),new T1(1,_yg));}) : (++C,A2(_yc,_s4(_yf),new T1(1,_yg)));}),_yh=(function(t){return document.createElement(t);}),_yi=function(_){return _yh("div");},_yj=(function(c,p){p.appendChild(c);}),_yk=(function(e){while(e.firstChild){e.removeChild(e.firstChild);}}),_yl=(function(c,p){p.removeChild(c);}),_ym=new T(function(){return document.body;}),_yn=function(_,_yo){var _yp=E(_yo);if(!_yp._){return 0;}else{var _yq=E(_yp.a),_yr=_yk(_yq),_ys=_yl(_yq,E(_ym));return _6J(_);}},_yt=(function(id){return document.getElementById(id);}),_yu=function(_yv,_){var _yw=_yt(toJSStr(E(_yv))),_yx=__eq(_yw,E(_tH));if(!E(_yx)){var _yy=__isUndef(_yw);if(!E(_yy)){return _yn(_,new T1(1,_yw));}else{return _yn(_,__Z);}}else{return _yn(_,__Z);}},_yz=function(_yA,_yB,_yC){while(1){var _yD=E(_yB);if(!_yD._){return (E(_yC)._==0)?true:false;}else{var _yE=E(_yC);if(!_yE._){return false;}else{if(!B(A3(_1F,_yA,_yD.a,_yE.a))){return false;}else{_yB=_yD.b;_yC=_yE.b;continue;}}}}},_yF=function(_yG,_){var _yH=E(_yG);if(!_yH._){return __Z;}else{var _yI=_yF(_yH.b,_);return new T2(1,_yH.a,_yI);}},_yJ=new T(function(){return err(new T(function(){return unCStr("Map.!: given key is not an element in the map");}));}),_yK=function(_yL,_yM){while(1){var _yN=E(_yM);if(!_yN._){switch(_6N(_yL,_yN.b)){case 0:_yM=_yN.d;continue;case 1:return E(_yN.c);default:_yM=_yN.e;continue;}}else{return E(_yJ);}}},_yO=function(_yP,_yQ){while(1){var _yR=E(_yP);if(!_yR._){return (E(_yQ)._==0)?true:false;}else{var _yS=E(_yQ);if(!_yS._){return false;}else{if(E(_yR.a)!=E(_yS.a)){return false;}else{_yP=_yR.b;_yQ=_yS.b;continue;}}}}},_yT=function(_yU,_yV,_yW,_yX){return (!_yO(_yU,_yW))?true:(!_ee(_yV,_yX))?true:false;},_yY=function(_yZ,_z0){var _z1=E(_yZ),_z2=E(_z0);return _yT(_z1.a,_z1.b,_z2.a,_z2.b);},_z3=function(_z4,_z5,_z6,_z7){if(!_yO(_z4,_z6)){return false;}else{return _ee(_z5,_z7);}},_z8=function(_z9,_za){var _zb=E(_z9),_zc=E(_za);return _z3(_zb.a,_zb.b,_zc.a,_zc.b);},_zd=function(_ze){return fromJSStr(E(_ze));},_zf=function(_zg){return E(E(_zg).a);},_zh=(function(e,p){return e.hasAttribute(p) ? e.getAttribute(p) : '';}),_zi=function(_zj,_zk,_zl,_zm){var _zn=new T(function(){var _zo=function(_){var _zp=_zh(B(A2(_zf,_zj,_zl)),E(_zm));return new T(function(){return String(_zp);});};return _zo;});return C > 19 ? new F(function(){return A2(_vg,_zk,_zn);}) : (++C,A2(_vg,_zk,_zn));},_zq=function(_zr,_zs,_zt,_zu){var _zv=_s4(_zs),_zw=new T(function(){return _yc(_zv);}),_zx=function(_zy){return C > 19 ? new F(function(){return A1(_zw,new T(function(){return _zd(_zy);}));}) : (++C,A1(_zw,new T(function(){return _zd(_zy);})));},_zz=new T(function(){return B(_zi(_zr,_zs,_zt,new T(function(){return toJSStr(E(_zu));},1)));});return C > 19 ? new F(function(){return A3(_1g,_zv,_zz,_zx);}) : (++C,A3(_1g,_zv,_zz,_zx));},_zA=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_zB=function(_zC,_zD,_zE,_zF){var _zG=new T(function(){var _zH=function(_){var _zI=_zA(B(A2(_zf,_zC,_zE)),E(_zF));return new T(function(){return String(_zI);});};return _zH;});return C > 19 ? new F(function(){return A2(_vg,_zD,_zG);}) : (++C,A2(_vg,_zD,_zG));},_zJ=function(_zK,_zL,_zM,_zN){var _zO=_s4(_zL),_zP=new T(function(){return _yc(_zO);}),_zQ=function(_zR){return C > 19 ? new F(function(){return A1(_zP,new T(function(){return _zd(_zR);}));}) : (++C,A1(_zP,new T(function(){return _zd(_zR);})));},_zS=new T(function(){return B(_zB(_zK,_zL,_zM,new T(function(){return toJSStr(E(_zN));},1)));});return C > 19 ? new F(function(){return A3(_1g,_zO,_zS,_zQ);}) : (++C,A3(_1g,_zO,_zS,_zQ));},_zT=new T(function(){return unCStr("suggestionList");}),_zU=new T2(0,new T(function(){return unCStr("PrimaEng");}),new T(function(){return unCStr("useS (useCl (simpleCl (usePron he_PP) (complA Romanus_A)))");})),_zV=new T(function(){return _tE(function(_){return nMV(__Z);});}),_zW=(function(e){if(e){e.stopPropagation();}}),_zX=function(_){var _zY=rMV(E(_zV)),_zZ=E(_zY);if(!_zZ._){var _A0=_zW(E(_tH));return _6J(_);}else{var _A1=_zW(E(_zZ.a));return _6J(_);}},_A2=new T(function(){return unCStr("lang");}),_A3=new T(function(){return err(_pL);}),_A4=new T(function(){return err(_pM);}),_A5=new T(function(){return B(A3(_ot,_oW,0,_pF));}),_A6=new T(function(){return unCStr("textContent");}),_A7=new T(function(){return _tc(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:298:5-16");}),__Z,__Z));}),_A8=new T(function(){return unCStr("score");}),_A9=function(_Aa,_Ab,_){var _Ac=_zX(_),_Ad=_yu(_zT,_),_Ae=B(A(_zq,[_ye,_xZ,_Aa,_A2,_])),_Af=_Ae,_Ag=_yt(toJSStr(E(_A8))),_Ah=__eq(_Ag,E(_tH)),_Ai=function(_,_Aj){var _Ak=E(_Aj);if(!_Ak._){return die(_A7);}else{var _Al=B(A(_zJ,[_ye,_xZ,_Ak.a,_A6,_])),_Am=new T(function(){return B(A2(_ww,new T3(1,new T(function(){var _An=_pN(_dy(_A5,_Al));if(!_An._){return E(_A4);}else{if(!E(_An.b)._){return E(_An.a);}else{return E(_A3);}}}),_zU,new T2(0,_Af,_Ab)),_Ao));});return _a(_Am,__Z,_);}};if(!E(_Ah)){var _Ap=__isUndef(_Ag);if(!E(_Ap)){return _Ai(_,new T1(1,_Ag));}else{return _Ai(_,__Z);}}else{return _Ai(_,__Z);}},_Aq=function(_Ar,_As){var _At=E(_As);if(!_At._){return __Z;}else{var _Au=_At.a,_Av=E(_Ar);return (_Av==1)?new T2(1,_Au,__Z):new T2(1,_Au,new T(function(){return _Aq(_Av-1|0,_At.b);}));}},_Aw=(function(e,c,x){x?e.classList.add(c):e.classList.remove(c);}),_Ax=new T(function(){return unCStr("wordHover");}),_Ay=function(_Az,_){while(1){var _AA=E(_Az);if(!_AA._){return 0;}else{var _AB=_Aw(E(_AA.a),toJSStr(E(_Ax)),true);_Az=_AA.b;continue;}}},_AC=(function(e,p,v){e.setAttribute(p, v);}),_AD=(function(e,p){e.removeAttribute(p);}),_AE=new T(function(){return unCStr("clickCount");}),_AF=new T(function(){return unCStr("clicked");}),_AG=new T(function(){return unCStr("False");}),_AH=function(_AI,_){while(1){var _AJ=E(_AI);if(!_AJ._){return 0;}else{var _AK=E(_AJ.a),_AL=_AC(_AK,toJSStr(E(_AF)),toJSStr(E(_AG))),_AM=_AD(_AK,toJSStr(E(_AE)));_AI=_AJ.b;continue;}}},_AN=new T(function(){return unCStr(": empty list");}),_AO=function(_AP){return err(_0(_aD,new T(function(){return _0(_AP,_AN);},1)));},_AQ=new T(function(){return _AO(new T(function(){return unCStr("head");}));}),_AR=new T(function(){return _AS(__Z);}),_AS=function(_AT){while(1){var _AU=(function(_AV){var _AW=E(_AV);if(!_AW._){return __Z;}else{var _AX=_AW.b,_AY=E(_AW.a);if(_AY==32){var _AZ=E(_AX);if(!_AZ._){return new T2(1,_AY,_AR);}else{if(E(_AZ.a)==38){var _B0=E(_AZ.b);if(!_B0._){return new T2(1,_AY,new T(function(){return _AS(_AZ);}));}else{if(E(_B0.a)==43){var _B1=E(_B0.b);if(!_B1._){return new T2(1,_AY,new T(function(){return _AS(_AZ);}));}else{if(E(_B1.a)==32){_AT=_B1.b;return __continue;}else{return new T2(1,_AY,new T(function(){return _AS(_AZ);}));}}}else{return new T2(1,_AY,new T(function(){return _AS(_AZ);}));}}}else{return new T2(1,_AY,new T(function(){return _AS(_AZ);}));}}}else{return new T2(1,_AY,new T(function(){return _AS(_AX);}));}}})(_AT);if(_AU!=__continue){return _AU;}}},_B2=(function(e){var ch = [];for(e = e.firstChild; e != null; e = e.nextSibling)  {if(e instanceof HTMLElement) {ch.push(e);}}return ch;}),_B3=function(_B4,_B5,_B6){while(1){var _B7=E(_B5);if(!_B7._){return true;}else{var _B8=E(_B6);if(!_B8._){return false;}else{if(!B(A3(_1F,_B4,_B7.a,_B8.a))){return false;}else{_B5=_B7.b;_B6=_B8.b;continue;}}}}},_B9=new T(function(){return unCStr("path");}),_Ba=new T(function(){return unCStr("\u2205");}),_Bb=new T(function(){return unCStr("offsetTop");}),_Bc=new T(function(){return unCStr("offsetLeft");}),_Bd=new T(function(){return new T1(1,"left");}),_Be=new T(function(){return new T1(1,"top");}),_Bf=new T(function(){return new T2(0,E(new T1(2,"class")),"menu");}),_Bg=new T(function(){return err(_pM);}),_Bh=new T(function(){return err(_pL);}),_Bi=function(_Bj,_Bk){return C > 19 ? new F(function(){return _Bl(_Bk);}) : (++C,_Bl(_Bk));},_Bm=new T(function(){return unCStr("True");}),_Bn=new T(function(){return unCStr("False");}),_Bl=function(_Bo){var _Bp=new T(function(){return B(A1(_Bo,false));}),_Bq=new T(function(){return B(A1(_Bo,true));}),_Br=new T(function(){return B(_ns(function(_Bs){var _Bt=E(_Bs);if(_Bt._==3){var _Bu=_Bt.a;return (!_ee(_Bu,_Bn))?(!_ee(_Bu,_Bm))?new T0(2):E(_Bq):E(_Bp);}else{return new T0(2);}}));}),_Bv=function(_Bw){return E(_Br);};return _dI(new T1(1,function(_Bx){return C > 19 ? new F(function(){return A2(_ml,_Bx,_Bv);}) : (++C,A2(_ml,_Bx,_Bv));}),new T(function(){return new T1(1,_nZ(_Bi,_Bo));}));},_By=new T(function(){return B(_Bl(_pF));}),_Bz=new T(function(){return new T2(0,E(new T1(2,"id")),"suggestionList");}),_BA=new T(function(){return err(_pL);}),_BB=new T(function(){return B(_p6(_p3,_pF));}),_BC=new T(function(){return unCStr("lin");}),_BD=new T(function(){return err(_pL);}),_BE=new T(function(){return err(_pM);}),_BF=function(_BG,_BH){return C > 19 ? new F(function(){return _p6(_p3,_BH);}) : (++C,_p6(_p3,_BH));},_BI=function(_BJ,_BK){return C > 19 ? new F(function(){return _p6(_BF,_BK);}) : (++C,_p6(_BF,_BK));},_BL=new T(function(){return B(_p6(_BF,_eI));}),_BM=function(_p4){return _dy(_BL,_p4);},_BN=new T(function(){return B(_p6(_p3,_eI));}),_BO=function(_p4){return _dy(_BN,_p4);},_BP=function(_BQ,_p4){return _BO(_p4);},_BR=function(_BS,_BT){return C > 19 ? new F(function(){return _BU(_BT);}) : (++C,_BU(_BT));},_BU=function(_BV){var _BW=new T(function(){return B(_ns(function(_BX){var _BY=E(_BX);if(!_BY._){return C > 19 ? new F(function(){return A1(_BV,_BY.a);}) : (++C,A1(_BV,_BY.a));}else{return new T0(2);}}));}),_BZ=function(_C0){return E(_BW);};return _dI(new T1(1,function(_C1){return C > 19 ? new F(function(){return A2(_ml,_C1,_BZ);}) : (++C,A2(_ml,_C1,_BZ));}),new T(function(){return new T1(1,_nZ(_BR,_BV));}));},_C2=function(_C3,_C4){return C > 19 ? new F(function(){return _BU(_C4);}) : (++C,_BU(_C4));},_C5=function(_C6,_C7){return C > 19 ? new F(function(){return _C8(_C7);}) : (++C,_C8(_C7));},_C8=function(_C9){var _Ca=new T(function(){return B(_ns(function(_Cb){var _Cc=E(_Cb);if(_Cc._==1){return C > 19 ? new F(function(){return A1(_C9,_Cc.a);}) : (++C,A1(_C9,_Cc.a));}else{return new T0(2);}}));}),_Cd=function(_Ce){return E(_Ca);};return _dI(_dI(new T1(1,function(_Cf){return C > 19 ? new F(function(){return A2(_ml,_Cf,_Cd);}) : (++C,A2(_ml,_Cf,_Cd));}),new T(function(){return B(_p6(_C2,_C9));})),new T(function(){return new T1(1,_nZ(_C5,_C9));}));},_Cg=function(_Ch,_Ci){return C > 19 ? new F(function(){return _C8(_Ci);}) : (++C,_C8(_Ci));},_Cj=function(_Ck,_Cl){return C > 19 ? new F(function(){return _p6(_Cg,_Cl);}) : (++C,_p6(_Cg,_Cl));},_Cm=new T(function(){return B(_p6(_Cg,_eI));}),_Cn=function(_p4){return _dy(_Cm,_p4);},_Co=new T(function(){return B(_C8(_eI));}),_Cp=function(_p4){return _dy(_Co,_p4);},_Cq=function(_Cr,_p4){return _Cp(_p4);},_Cs=new T(function(){return unCStr(",");}),_Ct=function(_Cu){return E(E(_Cu).c);},_Cv=function(_Cw,_Cx,_Cy){var _Cz=new T(function(){return _Ct(_Cx);}),_CA=new T(function(){return B(A2(_Ct,_Cw,_Cy));}),_CB=function(_CC){var _CD=function(_CE){var _CF=new T(function(){var _CG=new T(function(){return B(A2(_Cz,_Cy,function(_CH){return C > 19 ? new F(function(){return A1(_CC,new T2(0,_CE,_CH));}) : (++C,A1(_CC,new T2(0,_CE,_CH)));}));});return B(_ns(function(_CI){var _CJ=E(_CI);return (_CJ._==2)?(!_ee(_CJ.a,_Cs))?new T0(2):E(_CG):new T0(2);}));}),_CK=function(_CL){return E(_CF);};return new T1(1,function(_CM){return C > 19 ? new F(function(){return A2(_ml,_CM,_CK);}) : (++C,A2(_ml,_CM,_CK));});};return C > 19 ? new F(function(){return A1(_CA,_CD);}) : (++C,A1(_CA,_CD));};return _CB;},_CN=function(_CO,_CP,_CQ){var _CR=function(_p4){return _Cv(_CO,_CP,_p4);},_CS=function(_CT,_CU){return C > 19 ? new F(function(){return _CV(_CU);}) : (++C,_CV(_CU));},_CV=function(_CW){return _dI(new T1(1,_nZ(_CR,_CW)),new T(function(){return new T1(1,_nZ(_CS,_CW));}));};return C > 19 ? new F(function(){return _CV(_CQ);}) : (++C,_CV(_CQ));},_CX=new T(function(){return B(_p6(function(_CY,_CZ){return C > 19 ? new F(function(){return _CN(new T4(0,_BP,_BM,_BF,_BI),new T4(0,_Cq,_Cn,_Cg,_Cj),_CZ);}) : (++C,_CN(new T4(0,_BP,_BM,_BF,_BI),new T4(0,_Cq,_Cn,_Cg,_Cj),_CZ));},_pF));}),_D0=new T(function(){return err(_pM);}),_D1=new T(function(){return _tc(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:202:5-15");}),__Z,__Z));}),_D2=new T(function(){return unCStr("px");}),_D3=new T(function(){return unCStr("parentid");}),_D4=new T(function(){return unCStr("menuHover");}),_D5=(function(e,c) {e.classList.toggle(c);}),_D6=function(_D7,_){var _D8=_D5(_D7,toJSStr(E(_D4)));return _6J(_);},_D9=new T(function(){return unCStr("div");}),_Da=(function(s){return document.createTextNode(s);}),_Db=function(_Dc){return E(E(_Dc).a);},_Dd=function(_De){return E(E(_De).b);},_Df=function(_Dg){return E(E(_Dg).a);},_Dh=function(_Di){return E(E(_Di).b);},_Dj=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_Dk=function(_Dl,_Dm,_Dn,_Do,_Dp,_Dq){var _Dr=_Db(_Dl),_Ds=_s4(_Dr),_Dt=new T(function(){return _vg(_Dr);}),_Du=new T(function(){return _yc(_Ds);}),_Dv=new T(function(){return B(A1(_Dm,_Do));}),_Dw=new T(function(){return B(A2(_Df,_Dn,_Dp));}),_Dx=function(_Dy){return C > 19 ? new F(function(){return A1(_Du,new T3(0,_Dw,_Dv,_Dy));}) : (++C,A1(_Du,new T3(0,_Dw,_Dv,_Dy)));},_Dz=function(_DA){var _DB=new T(function(){var _DC=new T(function(){var _DD=__createJSFunc(2,function(_DE,_){var _DF=B(A2(E(_DA),_DE,_));return _tH;}),_DG=_DD;return function(_){return _Dj(E(_Dv),E(_Dw),_DG);};});return B(A1(_Dt,_DC));});return C > 19 ? new F(function(){return A3(_1g,_Ds,_DB,_Dx);}) : (++C,A3(_1g,_Ds,_DB,_Dx));},_DH=new T(function(){var _DI=new T(function(){return _vg(_Dr);}),_DJ=function(_DK){var _DL=new T(function(){return B(A1(_DI,function(_){var _=wMV(E(_zV),new T1(1,_DK));return C > 19 ? new F(function(){return A(_Dd,[_Dn,_Dp,_DK,_]);}) : (++C,A(_Dd,[_Dn,_Dp,_DK,_]));}));});return C > 19 ? new F(function(){return A3(_1g,_Ds,_DL,_Dq);}) : (++C,A3(_1g,_Ds,_DL,_Dq));};return B(A2(_Dh,_Dl,_DJ));});return C > 19 ? new F(function(){return A3(_1g,_Ds,_DH,_Dz);}) : (++C,A3(_1g,_Ds,_DH,_Dz));},_DM=function(_DN,_DO,_DP,_){var _DQ=_Da(toJSStr(E(_DO))),_DR=_yh(toJSStr(E(_D9))),_DS=_DR,_DT=B(A(_Dk,[_yb,_xE,_xA,_DS,5,function(_DU,_){return _D6(_DS,_);},_])),_DV=B(A(_Dk,[_yb,_xE,_xA,_DS,6,function(_DW,_){return _D6(_DS,_);},_])),_DX=B(A(_Dk,[_yb,_xE,_xA,_DS,0,_DP,_])),_DY=_yj(_DQ,_DS),_DZ=_yj(_DS,E(_DN));return 0;},_E0=new T(function(){return unCStr("True");}),_E1=(function(e,p,v){e.style[p] = v;}),_E2=(function(e,p,v){e[p] = v;}),_E3=function(_E4,_E5,_E6,_E7){var _E8=new T(function(){return B(A2(_zf,_E4,_E6));}),_E9=function(_Ea,_){var _Eb=E(_Ea);if(!_Eb._){return 0;}else{var _Ec=E(_E8),_Ed=_yj(E(_Eb.a),_Ec),_Ee=function(_Ef,_){while(1){var _Eg=E(_Ef);if(!_Eg._){return 0;}else{var _Eh=_yj(E(_Eg.a),_Ec);_Ef=_Eg.b;continue;}}};return _Ee(_Eb.b,_);}},_Ei=function(_Ej,_){while(1){var _Ek=(function(_El,_){var _Em=E(_El);if(!_Em._){return 0;}else{var _En=_Em.b,_Eo=E(_Em.a);if(!_Eo._){var _Ep=_Eo.b,_Eq=E(_Eo.a);switch(_Eq._){case 0:var _Er=E(_E8),_Es=_E2(_Er,_Eq.a,_Ep),_Et=function(_Eu,_){while(1){var _Ev=E(_Eu);if(!_Ev._){return 0;}else{var _Ew=_Ev.b,_Ex=E(_Ev.a);if(!_Ex._){var _Ey=_Ex.b,_Ez=E(_Ex.a);switch(_Ez._){case 0:var _EA=_E2(_Er,_Ez.a,_Ey);_Eu=_Ew;continue;case 1:var _EB=_E1(_Er,_Ez.a,_Ey);_Eu=_Ew;continue;default:var _EC=_AC(_Er,_Ez.a,_Ey);_Eu=_Ew;continue;}}else{var _ED=_E9(_Ex.a,_);_Eu=_Ew;continue;}}}};return _Et(_En,_);case 1:var _EE=E(_E8),_EF=_E1(_EE,_Eq.a,_Ep),_EG=function(_EH,_){while(1){var _EI=E(_EH);if(!_EI._){return 0;}else{var _EJ=_EI.b,_EK=E(_EI.a);if(!_EK._){var _EL=_EK.b,_EM=E(_EK.a);switch(_EM._){case 0:var _EN=_E2(_EE,_EM.a,_EL);_EH=_EJ;continue;case 1:var _EO=_E1(_EE,_EM.a,_EL);_EH=_EJ;continue;default:var _EP=_AC(_EE,_EM.a,_EL);_EH=_EJ;continue;}}else{var _EQ=_E9(_EK.a,_);_EH=_EJ;continue;}}}};return _EG(_En,_);default:var _ER=E(_E8),_ES=_AC(_ER,_Eq.a,_Ep),_ET=function(_EU,_){while(1){var _EV=E(_EU);if(!_EV._){return 0;}else{var _EW=_EV.b,_EX=E(_EV.a);if(!_EX._){var _EY=_EX.b,_EZ=E(_EX.a);switch(_EZ._){case 0:var _F0=_E2(_ER,_EZ.a,_EY);_EU=_EW;continue;case 1:var _F1=_E1(_ER,_EZ.a,_EY);_EU=_EW;continue;default:var _F2=_AC(_ER,_EZ.a,_EY);_EU=_EW;continue;}}else{var _F3=_E9(_EX.a,_);_EU=_EW;continue;}}}};return _ET(_En,_);}}else{var _F4=_E9(_Eo.a,_);_Ej=_En;return __continue;}}})(_Ej,_);if(_Ek!=__continue){return _Ek;}}};return C > 19 ? new F(function(){return A2(_vg,_E5,function(_){return _Ei(_E7,_);});}) : (++C,A2(_vg,_E5,function(_){return _Ei(_E7,_);}));},_F5=function(_F6,_F7,_F8,_F9){var _Fa=_s4(_F7),_Fb=function(_Fc){return C > 19 ? new F(function(){return A3(_vb,_Fa,new T(function(){return B(_E3(_F6,_F7,_Fc,_F9));}),new T(function(){return B(A2(_yc,_Fa,_Fc));}));}) : (++C,A3(_vb,_Fa,new T(function(){return B(_E3(_F6,_F7,_Fc,_F9));}),new T(function(){return B(A2(_yc,_Fa,_Fc));})));};return C > 19 ? new F(function(){return A3(_1g,_Fa,_F8,_Fb);}) : (++C,A3(_1g,_Fa,_F8,_Fb));},_Fd=function(_Fe,_Ff,_Fg,_){var _Fh=_zX(_),_Fi=B(A(_zJ,[_ye,_xZ,_Fe,_Bc,_])),_Fj=_Fi,_Fk=B(A(_zJ,[_ye,_xZ,_Fe,_Bb,_])),_Fl=_Fk,_Fm=_yu(_zT,_),_Fn=B(A(_zq,[_ye,_xZ,_Fe,_AF,_])),_Fo=_pN(_dy(_By,_Fn));if(!_Fo._){return E(_Bg);}else{if(!E(_Fo.b)._){var _Fp=function(_,_Fq){var _Fr=B(A(_zq,[_ye,_xZ,_Fe,_D3,_])),_Fs=_yt(toJSStr(E(_Fr))),_Ft=__eq(_Fs,E(_tH)),_Fu=function(_,_Fv){var _Fw=E(_Fv);if(!_Fw._){return die(_D1);}else{var _Fx=E(_Fw.a),_Fy=_B2(_Fx),_Fz=__arr2lst(0,_Fy),_FA=_yF(_Fz,_),_FB=_FA,_FC=_AH(_FB,_),_FD=E(_Fe),_FE=_AC(_FD,toJSStr(E(_AF)),toJSStr(E(_E0))),_FF=E(_Fq),_FG=_AC(_FD,toJSStr(E(_AE)),toJSStr(_i8(0,_FF+1|0,__Z))),_FH=B(A(_zq,[_ye,_xZ,_FD,_B9,_])),_FI=B(A(_zq,[_ye,_xZ,_Fx,_BC,_])),_FJ=_FI,_FK=new T(function(){return E(E(_Fg).a);}),_FL=B(A(_F5,[_ye,_xZ,_yi,new T2(1,_Bz,new T2(1,_Bf,new T2(1,new T(function(){var _FM=_pN(_dy(_A5,_Fl));if(!_FM._){return E(_A4);}else{if(!E(_FM.b)._){return new T2(0,E(_Be),toJSStr(_0(_i8(0,E(E(_FK).b)+E(_FM.a)|0,__Z),_D2)));}else{return E(_A3);}}}),new T2(1,new T(function(){var _FN=_pN(_dy(_A5,_Fj));if(!_FN._){return E(_A4);}else{if(!E(_FN.b)._){return new T2(0,E(_Bd),toJSStr(_0(_i8(0,E(E(_FK).a)+E(_FN.a)|0,__Z),_D2)));}else{return E(_A3);}}}),__Z)))),_])),_FO=_FL,_FP=_pN(_dy(_BB,_FH));if(!_FP._){return E(_D0);}else{var _FQ=_FP.a;if(!E(_FP.b)._){var _FR=_gJ(_FQ,0)-_FF|0;if(0>=_FR){var _FS=__Z;}else{var _FS=_Aq(_FR,_FQ);}var _FT=_yK(_FS,_Ff);if(!_FT._){return E(_AQ);}else{var _FU=new T(function(){var _FV=_pN(_dy(_CX,_FJ));if(!_FV._){return E(_BE);}else{if(!E(_FV.b)._){return E(_FV.a);}else{return E(_BD);}}}),_FW=function(_FX){while(1){var _FY=(function(_FZ){var _G0=E(_FZ);if(!_G0._){return __Z;}else{var _G1=_G0.b,_G2=E(_G0.a);if(!_B3(_3s,_FS,_G2.a)){_FX=_G1;return __continue;}else{var _G3=new T(function(){return _0(_G2.b,new T(function(){return _FW(_G1);},1));});return new T2(1,32,_G3);}}})(_FX);if(_FY!=__continue){return _FY;}}},_G4=function(_G5,_){while(1){var _G6=(function(_G7,_){var _G8=E(_G7);if(!_G8._){return 0;}else{var _G9=_G8.b,_Ga=E(_G8.a),_Gb=_Ga.b;if(!_yz(new T2(0,_z8,_yY),_Gb,_FU)){var _Gc=function(_Gd,_){return C > 19 ? new F(function(){return _A9(_Fx,_Ga.c,_);}) : (++C,_A9(_Fx,_Ga.c,_));},_Ge=_FW(_Gb);if(!_Ge._){var _Gf=E(_AR);if(!_Gf._){var _Gg=_DM(_FO,_Ba,_Gc,_);_G5=_G9;return __continue;}else{var _Gh=_DM(_FO,_Gf,_Gc,_);_G5=_G9;return __continue;}}else{var _Gi=_AS(_Ge.b);if(!_Gi._){var _Gj=_DM(_FO,_Ba,_Gc,_);_G5=_G9;return __continue;}else{var _Gk=_DM(_FO,_Gi,_Gc,_);_G5=_G9;return __continue;}}}else{_G5=_G9;return __continue;}}})(_G5,_);if(_G6!=__continue){return _G6;}}},_Gl=_G4(_FT.a,_),_Gm=_yj(E(_FO),E(_ym)),_Gn=function(_Go,_){var _Gp=E(_Go);if(!_Gp._){return __Z;}else{var _Gq=_Gp.a,_Gr=B(A(_zq,[_ye,_xZ,_Gq,_B9,_])),_Gs=_Gn(_Gp.b,_);return new T(function(){if(!_B3(_3s,_FS,new T(function(){var _Gt=_pN(_dy(_BB,_Gr));if(!_Gt._){return E(_D0);}else{if(!E(_Gt.b)._){return E(_Gt.a);}else{return E(_BA);}}},1))){return E(_Gs);}else{return new T2(1,_Gq,_Gs);}});}},_Gu=_Gn(_FB,_),_Gv=_Ay(_Gu,_);return 0;}}else{return E(_BA);}}}};if(!E(_Ft)){var _Gw=__isUndef(_Fs);if(!E(_Gw)){return _Fu(_,new T1(1,_Fs));}else{return _Fu(_,__Z);}}else{return _Fu(_,__Z);}};if(!E(_Fo.a)){return _Fp(_,0);}else{var _Gx=B(A(_zq,[_ye,_xZ,_Fe,_AE,_]));return _Fp(_,new T(function(){var _Gy=_pN(_dy(_A5,_Gx));if(!_Gy._){return E(_A4);}else{if(!E(_Gy.b)._){return E(_Gy.a);}else{return E(_A3);}}},1));}}else{return E(_Bh);}}},_Gz=function(_GA,_GB){return new T2(0,E(_GA),toJSStr(E(_GB)));},_GC=function(_){return _yh("span");},_GD=new T(function(){return B(_F5(_ye,_xZ,function(_){return _yh("span");},new T2(1,new T(function(){return new T2(0,E(new T1(2,"class")),"path");}),__Z)));}),_GE=new T(function(){return new T1(2,"parentId");}),_GF=new T(function(){return new T1(2,"path");}),_GG=new T(function(){return new T2(0,E(new T1(2,"class")),"word");}),_GH=new T(function(){return new T2(0,E(new T1(2,"class")),"gap");}),_GI=new T(function(){return unCStr("id");}),_GJ=new T(function(){return unCStr(" ");}),_GK=new T2(1,new T(function(){return new T2(0,E(new T1(2,"clicked")),toJSStr(E(_AG)));}),__Z),_GL=function(_GM,_GN){return _i8(0,E(_GM),_GN);},_GO=function(_GP,_){var _GQ=_D5(_GP,toJSStr(E(_Ax)));return _6J(_);},_GR=function(_GS,_GT,_){return _GO(E(_GS),_);},_GU=function(_GV,_GW,_GX,_GY,_GZ,_H0,_H1,_){var _H2=B(A(_zq,[_ye,_xZ,_GV,_GI,_])),_H3=_H2,_H4=function(_){var _H5=B(A(_F5,[_ye,_xZ,_GC,new T2(1,_GG,new T2(1,new T(function(){return new T2(0,E(_GF),toJSStr(_2P(_GL,_GW,__Z)));}),new T2(1,new T(function(){return _Gz(_GE,_H3);}),_GK))),_])),_H6=_H5,_H7=_Da(toJSStr(E(_GX))),_H8=B(A(_Dk,[_yb,_xE,_xA,_H6,5,function(_H9,_){return _GR(_H6,_H9,_);},_])),_Ha=B(A(_Dk,[_yb,_xE,_xA,_H6,6,function(_H9,_){return _GR(_H6,_H9,_);},_])),_Hb=E(_H6),_Hc=_yj(_H7,_Hb),_Hd=E(_GV),_He=_yj(_Hb,_Hd),_Hf=function(_){if(!E(_GZ)){return 0;}else{var _Hg=B(A1(_GD,_)),_Hh=_Da(toJSStr(_2P(_GL,_GW,__Z))),_Hi=E(_Hg),_Hj=_yj(_Hh,_Hi),_Hk=_yj(_Hi,_Hd);return _6J(_);}};if(!E(_H1)){return _Hf(_);}else{var _Hl=B(A(_Dk,[_yb,_xE,_xA,_Hb,0,function(_Hm,_){return C > 19 ? new F(function(){return _Fd(_Hb,E(_GY).a,_Hm,_);}) : (++C,_Fd(_Hb,E(_GY).a,_Hm,_));},_]));return _Hf(_);}};if(!E(_H0)){return _H4(_);}else{var _Hn=B(A(_F5,[_ye,_xZ,_GC,new T2(1,_GH,new T2(1,new T(function(){return new T2(0,E(_GF),toJSStr(_2P(_GL,_GW,__Z)));}),new T2(1,new T(function(){return _Gz(_GE,_H3);}),_GK))),_])),_Ho=_Hn,_Hp=_Da(toJSStr(E(_GJ))),_Hq=B(A(_Dk,[_yb,_xE,_xA,_Ho,5,function(_H9,_){return _GR(_Ho,_H9,_);},_])),_Hr=B(A(_Dk,[_yb,_xE,_xA,_Ho,6,function(_H9,_){return _GR(_Ho,_H9,_);},_])),_Hs=E(_Ho),_Ht=_yj(_Hp,_Hs),_Hu=_yj(_Hs,E(_GV));if(!E(_H1)){return _H4(_);}else{var _Hv=B(A(_Dk,[_yb,_xE,_xA,_Hs,0,function(_Hw,_){return C > 19 ? new F(function(){return _Fd(_Hs,E(_GY).a,_Hw,_);}) : (++C,_Fd(_Hs,E(_GY).a,_Hw,_));},_]));return _H4(_);}}},_Hx=(function(e,c) {return e.classList.contains(c);}),_Hy=new T(function(){return unCStr("debug");}),_Hz=function(_HA,_HB,_HC){return C > 19 ? new F(function(){return A1(_HA,new T2(1,44,new T(function(){return B(A1(_HB,_HC));})));}) : (++C,A1(_HA,new T2(1,44,new T(function(){return B(A1(_HB,_HC));}))));},_HD=new T(function(){return _AO(new T(function(){return unCStr("foldr1");}));}),_HE=function(_HF,_HG){var _HH=E(_HG);if(!_HH._){return E(_HD);}else{var _HI=_HH.a,_HJ=E(_HH.b);if(!_HJ._){return E(_HI);}else{return C > 19 ? new F(function(){return A2(_HF,_HI,new T(function(){return B(_HE(_HF,_HJ));}));}) : (++C,A2(_HF,_HI,new T(function(){return B(_HE(_HF,_HJ));})));}}},_HK=function(_HL,_HM){return new T2(1,34,new T(function(){return _bF(_HL,new T2(1,34,_HM));}));},_HN=function(_HO,_HP){return _2P(_GL,_HO,_HP);},_HQ=function(_HR,_HS){var _HT=E(_HR),_HU=new T(function(){return B(A3(_HE,_Hz,new T2(1,function(_HV){return _HN(_HT.a,_HV);},new T2(1,function(_HW){return _HK(_HT.b,_HW);},__Z)),new T2(1,41,_HS)));});return new T2(1,40,_HU);},_HX=new T(function(){return _tc(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:69:5-23");}),__Z,__Z));}),_HY=new T(function(){return unCStr("exampleTree");}),_HZ=function(_I0,_I1,_I2,_){var _I3=_yt(toJSStr(E(_HY))),_I4=__eq(_I3,E(_tH)),_I5=function(_,_I6){var _I7=E(_I6);if(!_I7._){return die(_HX);}else{var _I8=E(_I7.a),_I9=_yk(_I8),_Ia=_Hx(_I8,toJSStr(E(_Hy))),_Ib=_Ia,_Ic=_AC(_I8,toJSStr(E(_BC)),toJSStr(_2P(_HQ,_I1,__Z))),_Id=_AC(_I8,toJSStr(E(_A2)),toJSStr(E(_I0))),_Ie=function(_If,_){while(1){var _Ig=E(_If);if(!_Ig._){return 0;}else{var _Ih=E(_Ig.a),_Ii=B(_GU(_I8,_Ih.a,_Ih.b,_I2,_Ib,false,false,_));_If=_Ig.b;continue;}}},_Ij=_Ie(_I1,_);return 0;}};if(!E(_I4)){var _Ik=__isUndef(_I3);if(!E(_Ik)){return _I5(_,new T1(1,_I3));}else{return _I5(_,__Z);}}else{return _I5(_,__Z);}},_Il=new T(function(){return _tc(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:86:5-24");}),__Z,__Z));}),_Im=new T(function(){return unCStr("exerciseTree");}),_In=function(_Io,_Ip,_Iq,_){var _Ir=_yt(toJSStr(E(_Im))),_Is=__eq(_Ir,E(_tH)),_It=function(_,_Iu){var _Iv=E(_Iu);if(!_Iv._){return die(_Il);}else{var _Iw=E(_Iv.a),_Ix=_yk(_Iw),_Iy=_Hx(_Iw,toJSStr(E(_Hy))),_Iz=_Iy,_IA=_AC(_Iw,toJSStr(E(_BC)),toJSStr(_2P(_HQ,_Ip,__Z))),_IB=_AC(_Iw,toJSStr(E(_A2)),toJSStr(E(_Io))),_IC=function(_ID,_){while(1){var _IE=E(_ID);if(!_IE._){return 0;}else{var _IF=E(_IE.a),_IG=B(_GU(_Iw,_IF.a,_IF.b,_Iq,_Iz,true,true,_));_ID=_IE.b;continue;}}},_IH=_IC(_Ip,_);return 0;}};if(!E(_Is)){var _II=__isUndef(_Ir);if(!E(_II)){return _It(_,new T1(1,_Ir));}else{return _It(_,__Z);}}else{return _It(_,__Z);}},_IJ=(function(t,f){return window.setInterval(f,t);}),_IK=(function(t,f){return window.setTimeout(f,t);}),_IL=function(_IM,_IN,_IO){var _IP=_Db(_IM),_IQ=new T(function(){return _vg(_IP);}),_IR=function(_IS){var _IT=function(_){var _IU=E(_IN);if(!_IU._){var _IV=B(A1(_IS,0)),_IW=__createJSFunc(0,function(_){var _IX=B(A1(_IV,_));return _tH;}),_IY=_IK(_IU.a,_IW);return new T(function(){var _IZ=Number(_IY),_J0=jsTrunc(_IZ);return new T2(0,_J0,_IU);});}else{var _J1=B(A1(_IS,0)),_J2=__createJSFunc(0,function(_){var _J3=B(A1(_J1,_));return _tH;}),_J4=_IJ(_IU.a,_J2);return new T(function(){var _J5=Number(_J4),_J6=jsTrunc(_J5);return new T2(0,_J6,_IU);});}};return C > 19 ? new F(function(){return A1(_IQ,_IT);}) : (++C,A1(_IQ,_IT));},_J7=new T(function(){return B(A2(_Dh,_IM,function(_J8){return E(_IO);}));});return C > 19 ? new F(function(){return A3(_1g,_s4(_IP),_J7,_IR);}) : (++C,A3(_1g,_s4(_IP),_J7,_IR));},_J9=function(_Ja,_Jb){return function(_){var _Jc=nMV(new T1(1,__Z)),_Jd=_Jc,_Je=function(_){var _Jf=function(_){return _a(new T(function(){return B(A(_vo,[_1E,_Jd,0,_1v]));}),__Z,_);},_Jg=B(A(_IL,[_yb,new T(function(){return new T1(0,E(_Ja));}),_Jf,_]));return new T(function(){return B(A3(_vE,_1E,_Jd,_Jb));});};return new T1(0,_Je);};},_Jh=new T(function(){return alert;}),_Ji=new T(function(){return unCStr("won");}),_Jj=new T(function(){return _tc(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:54:5-16");}),__Z,__Z));}),_Jk=new T(function(){return unCStr(" Clicks");}),_Jl=function(_Jm,_Jn,_){var _Jo=new T(function(){var _Jp=new T(function(){return unAppCStr(" and Success ",new T(function(){if(!E(_Jn)){return E(_AG);}else{return E(_E0);}}));},1);return _0(_i8(0,E(_Jm),__Z),_Jp);}),_Jq=_6K(toJSStr(unAppCStr("Score ",_Jo))),_Jr=_yt(toJSStr(E(_A8))),_Js=__eq(_Jr,E(_tH)),_Jt=function(_,_Ju){var _Jv=E(_Ju);if(!_Jv._){return die(_Jj);}else{var _Jw=E(_Jv.a),_Jx=_yk(_Jw),_Jy=E(_Jm),_Jz=_Da(toJSStr(_i8(0,_Jy,__Z))),_JA=E(_Jn),_JB=_Aw(_Jw,toJSStr(E(_Ji)),_JA);if(!_JA){var _JC=_yj(_Jz,_Jw);return _6J(_);}else{var _JD=new T(function(){var _JE=function(_){var _JF=E(_Jh)(toJSStr(unAppCStr("Congratulations! You won after ",new T(function(){return _0(_i8(0,_Jy,__Z),_Jk);}))));return _vn;};return new T1(0,_J9(200,function(_JG){return E(new T1(0,_JE));}));}),_JH=_a(_JD,__Z,_),_JI=_yj(_Jz,_Jw);return _6J(_);}}};if(!E(_Js)){var _JJ=__isUndef(_Jr);if(!E(_JJ)){return _Jt(_,new T1(1,_Jr));}else{return _Jt(_,__Z);}}else{return _Jt(_,__Z);}},_JK=new T(function(){return unCStr("laetus");}),_JL=new T2(1,0,__Z),_JM=new T(function(){return unCStr("est");}),_JN=new T(function(){return unCStr("Augustus");}),_JO=new T(function(){return unCStr("menuList");}),_JP=new T(function(){return unCStr("Reset");}),_JQ=new T(function(){return unCStr("Toggle Debug");}),_JR=new T(function(){return new T2(0,E(new T1(2,"id")),"menuList");}),_JS=new T(function(){return _tc(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:283:87-93");}),__Z,__Z));}),_JT=new T(function(){return _tc(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:283:51-57");}),__Z,__Z));}),_JU=function(_JV,_JW,_){var _JX=new T(function(){return E(E(E(_JW).d).a);}),_JY=new T(function(){return E(E(E(_JW).d).d);}),_JZ=_zX(_),_K0=B(A(_zJ,[_ye,_xZ,_JV,_Bc,_])),_K1=B(A(_zJ,[_ye,_xZ,_JV,_Bb,_])),_K2=_yu(_JO,_),_K3=B(A(_F5,[_ye,_xZ,_yi,new T2(1,_JR,new T2(1,_Bf,new T2(1,new T(function(){return new T2(0,E(_Be),toJSStr(_0(_K1,_D2)));}),new T2(1,new T(function(){var _K4=_pN(_dy(_A5,_K0));if(!_K4._){return E(_A4);}else{if(!E(_K4.b)._){return new T2(0,E(_Bd),toJSStr(_0(_i8(0,E(_K4.a)-200|0,__Z),_D2)));}else{return E(_A3);}}}),__Z)))),_])),_K5=new T(function(){return E(E(E(_JW).d).c);}),_K6=new T(function(){return E(E(E(_JW).c).d);}),_K7=new T(function(){return E(E(E(_JW).c).c);}),_K8=new T(function(){return E(E(E(_JW).c).a);}),_K9=function(_Ka,_){var _Kb=_yt(toJSStr(E(_HY))),_Kc=E(_tH),_Kd=__eq(_Kb,_Kc),_Ke=function(_,_Kf){var _Kg=E(_Kf);if(!_Kg._){return die(_JT);}else{var _Kh=_yt(toJSStr(E(_Im))),_Ki=__eq(_Kh,_Kc),_Kj=function(_,_Kk){var _Kl=E(_Kk);if(!_Kl._){return die(_JS);}else{var _Km=toJSStr(E(_Hy)),_Kn=_D5(E(_Kg.a),_Km),_Ko=_D5(E(_Kl.a),_Km),_Kp=_In(_JX,_K5,_JY,_);return _HZ(_K8,_K7,_K6,_);}};if(!E(_Ki)){var _Kq=__isUndef(_Kh);if(!E(_Kq)){return C > 19 ? new F(function(){return _Kj(_,new T1(1,_Kh));}) : (++C,_Kj(_,new T1(1,_Kh)));}else{return C > 19 ? new F(function(){return _Kj(_,__Z);}) : (++C,_Kj(_,__Z));}}else{return C > 19 ? new F(function(){return _Kj(_,__Z);}) : (++C,_Kj(_,__Z));}}};if(!E(_Kd)){var _Kr=__isUndef(_Kb);if(!E(_Kr)){return C > 19 ? new F(function(){return _Ke(_,new T1(1,_Kb));}) : (++C,_Ke(_,new T1(1,_Kb)));}else{return C > 19 ? new F(function(){return _Ke(_,__Z);}) : (++C,_Ke(_,__Z));}}else{return C > 19 ? new F(function(){return _Ke(_,__Z);}) : (++C,_Ke(_,__Z));}},_Ks=_DM(_K3,_JQ,_K9,_),_Kt=_DM(_K3,_JP,function(_Ku,_){var _Kv=_In(_JX,new T2(1,new T2(0,new T2(1,0,new T2(1,0,new T2(1,0,_JL))),_JN),new T2(1,new T2(0,new T2(1,0,new T2(1,0,new T2(1,1,_JL))),_JK),new T2(1,new T2(0,new T2(1,0,new T2(1,0,new T2(1,1,__Z))),_JM),__Z))),_JY,_);return _Jl(0,false,_);},_),_Kw=_yj(E(_K3),E(_ym));return 0;},_Kx=new T(function(){return unCStr("clickcount");}),_Ky=function(_Kz,_){while(1){var _KA=E(_Kz);if(!_KA._){return 0;}else{var _KB=_AD(E(_KA.a),toJSStr(E(_Kx)));_Kz=_KA.b;continue;}}},_KC=function(_KD,_){while(1){var _KE=E(_KD);if(!_KE._){return 0;}else{var _KF=_AC(E(_KE.a),toJSStr(E(_AF)),toJSStr(E(_AG)));_KD=_KE.b;continue;}}},_KG=function(_KH,_){while(1){var _KI=E(_KH);if(!_KI._){return 0;}else{var _KJ=_Aw(E(_KI.a),toJSStr(E(_Ax)),false);_KH=_KI.b;continue;}}},_KK=new T(function(){return _tc(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:160:5-15");}),__Z,__Z));}),_KL=function(_,_KM){var _KN=E(_KM);if(!_KN._){return die(_KK);}else{var _KO=_B2(E(_KN.a)),_KP=__arr2lst(0,_KO),_KQ=_yF(_KP,_),_KR=_KG(_KQ,_),_KS=_KC(_KQ,_);return _Ky(_KQ,_);}},_KT=function(_){var _KU=_yu(_zT,_),_KV=_yu(_JO,_),_KW=_yt("exerciseTree"),_KX=__eq(_KW,E(_tH));if(!E(_KX)){var _KY=__isUndef(_KW);if(!E(_KY)){return _KL(_,new T1(1,_KW));}else{return _KL(_,__Z);}}else{return _KL(_,__Z);}},_KZ=new T(function(){return B(_Dk(_yb,_xE,_xA,_ym,0,function(_L0,_){return _KT(_);}));}),_L1=new T(function(){return _tc(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:40:5-13");}),__Z,__Z));}),_L2=new T(function(){return unCStr("menuButton");}),_L3=function(_L4){return E(E(_L4).b);},_L5=function(_L6){return E(E(_L6).a);},_L7=function(_L8,_){var _L9=B(A1(_KZ,_)),_La=_yt(toJSStr(E(_L2))),_Lb=__eq(_La,E(_tH)),_Lc=function(_,_Ld){var _Le=E(_Ld);if(!_Le._){return die(_L1);}else{var _Lf=_Le.a,_Lg=B(A(_Dk,[_yb,_xE,_xA,_Lf,0,function(_Lh,_){return _JU(_Lf,_L8,_);},_])),_Li=_HZ(new T(function(){return E(E(E(_L8).c).a);},1),new T(function(){return E(E(E(_L8).c).c);}),new T(function(){return E(E(E(_L8).c).d);}),_),_Lj=_In(new T(function(){return E(E(E(_L8).d).a);},1),new T(function(){return E(E(E(_L8).d).c);}),new T(function(){return E(E(E(_L8).d).d);}),_),_Lk=_Jl(new T(function(){return _L3(_L8);}),new T(function(){return _L5(_L8);}),_);return 0;}};if(!E(_Lb)){var _Ll=__isUndef(_La);if(!E(_Ll)){return _Lc(_,new T1(1,_La));}else{return _Lc(_,__Z);}}else{return _Lc(_,__Z);}},_Ao=function(_Lm){return new T1(0,function(_){var _Ln=_L7(_Lm,_);return _vn;});},_Lo=new T(function(){return B(A2(_ww,new T3(1,-1,_zU,new T2(0,new T(function(){return unCStr("PrimaLat");}),new T(function(){return unCStr("useS (useCl (simpleCl (usePN Augustus_PN) (complA laetus_A)))");}))),_Ao));}),_Lp=function(_){var _Lq=_a(_Lo,__Z,_);return 0;},_Lr=function(_){return _Lp(_);};
var hasteMain = function() {B(A(_Lr, [0]));};window.onload = hasteMain;