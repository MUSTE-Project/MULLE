"use strict";
var __haste_prog_id = '31bd3b7996df95539264cdf21caaaccd689f56783441552c5fb0563474efca97';
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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=new T1(0,_),_i=new T(function(){return toJSStr(_4);}),_j=function(_k){return E(_i);},_l=function(_m,_){var _n=E(_m);if(!_n._){return _4;}else{var _o=B(_l(_n.b,_));return new T2(1,_5,_o);}},_p=function(_q,_){var _r=__arr2lst(0,_q);return new F(function(){return _l(_r,_);});},_s=function(_t,_){return new F(function(){return _p(E(_t),_);});},_u=function(_){return _5;},_v=function(_w,_){return new F(function(){return _u(_);});},_x=new T2(0,_v,_s),_y=function(_){return new F(function(){return __jsNull();});},_z=function(_A){var _B=B(A1(_A,_));return E(_B);},_C=new T(function(){return B(_z(_y));}),_D=new T(function(){return E(_C);}),_E=function(_F){return E(_D);},_G=function(_H,_I){var _J=E(_I);return (_J._==0)?__Z:new T2(1,new T(function(){return B(A1(_H,_J.a));}),new T(function(){return B(_G(_H,_J.b));}));},_K=function(_L){return new F(function(){return __lst2arr(B(_G(_E,_L)));});},_M=new T2(0,_E,_K),_N=new T4(0,_M,_x,_j,_j),_O="application/octet-stream",_P=function(_Q){return E(_O);},_R="blob",_S=function(_T){return E(_R);},_U=function(_V,_){var _W=E(_V);if(!_W._){return _4;}else{var _X=B(_U(_W.b,_));return new T2(1,_W.a,_X);}},_Y=function(_Z,_){var _10=__arr2lst(0,_Z);return new F(function(){return _U(_10,_);});},_11=function(_12,_){return new F(function(){return _Y(E(_12),_);});},_13=function(_14,_){return _14;},_15=new T2(0,_13,_11),_16=function(_17){return E(_17);},_18=function(_19){return new F(function(){return __lst2arr(B(_G(_16,_19)));});},_1a=new T2(0,_16,_18),_1b=new T4(0,_1a,_15,_P,_S),_1c=function(_1d,_1e,_1f){var _1g=function(_1h){var _1i=new T(function(){return B(A1(_1f,_1h));});return new F(function(){return A1(_1e,function(_1j){return E(_1i);});});};return new F(function(){return A1(_1d,_1g);});},_1k=function(_1l,_1m,_1n){var _1o=new T(function(){return B(A1(_1m,function(_1p){return new F(function(){return A1(_1n,_1p);});}));});return new F(function(){return A1(_1l,function(_1q){return E(_1o);});});},_1r=function(_1s,_1t,_1u){var _1v=function(_1w){var _1x=function(_1y){return new F(function(){return A1(_1u,new T(function(){return B(A1(_1w,_1y));}));});};return new F(function(){return A1(_1t,_1x);});};return new F(function(){return A1(_1s,_1v);});},_1z=function(_1A,_1B){return new F(function(){return A1(_1B,_1A);});},_1C=function(_1D,_1E,_1F){var _1G=new T(function(){return B(A1(_1F,_1D));});return new F(function(){return A1(_1E,function(_1H){return E(_1G);});});},_1I=function(_1J,_1K,_1L){var _1M=function(_1N){return new F(function(){return A1(_1L,new T(function(){return B(A1(_1J,_1N));}));});};return new F(function(){return A1(_1K,_1M);});},_1O=new T2(0,_1I,_1C),_1P=new T5(0,_1O,_1z,_1r,_1k,_1c),_1Q=function(_1R,_1S,_1T){return new F(function(){return A1(_1R,function(_1U){return new F(function(){return A2(_1S,_1U,_1T);});});});},_1V=function(_1W){return E(E(_1W).b);},_1X=function(_1Y,_1Z){return new F(function(){return A3(_1V,_20,_1Y,function(_21){return E(_1Z);});});},_22=function(_23){return new F(function(){return err(_23);});},_20=new T(function(){return new T5(0,_1P,_1Q,_1X,_1z,_22);}),_24=function(_25,_26,_){var _27=B(A1(_26,_));return new T(function(){return B(A1(_25,_27));});},_28=function(_29,_2a){return new T1(0,function(_){return new F(function(){return _24(_2a,_29,_);});});},_2b=new T2(0,_20,_28),_2c=function(_2d){return new T0(2);},_2e=function(_2f){var _2g=new T(function(){return B(A1(_2f,_2c));}),_2h=function(_2i){return new T1(1,new T2(1,new T(function(){return B(A1(_2i,_5));}),new T2(1,_2g,_4)));};return E(_2h);},_2j=function(_2k){return E(_2k);},_2l=new T3(0,_2b,_2j,_2e),_2m=function(_2n){return E(E(_2n).a);},_2o=function(_2p,_2q,_2r,_2s,_2t){var _2u=B(A2(_2m,_2p,E(_2t)));return new F(function(){return A2(_2q,_2r,new T2(1,_2u,E(_2s)));});},_2v=function(_2w){return E(E(_2w).a);},_2x=function(_2y){return E(E(_2y).a);},_2z=function(_2A){return E(E(_2A).a);},_2B=function(_2C){return E(E(_2C).b);},_2D=new T(function(){return B(unCStr("base"));}),_2E=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_2F=new T(function(){return B(unCStr("IOException"));}),_2G=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_2D,_2E,_2F),_2H=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_2G,_4,_4),_2I=function(_2J){return E(_2H);},_2K=function(_2L){return E(E(_2L).a);},_2M=function(_2N,_2O,_2P){var _2Q=B(A1(_2N,_)),_2R=B(A1(_2O,_)),_2S=hs_eqWord64(_2Q.a,_2R.a);if(!_2S){return __Z;}else{var _2T=hs_eqWord64(_2Q.b,_2R.b);return (!_2T)?__Z:new T1(1,_2P);}},_2U=function(_2V){var _2W=E(_2V);return new F(function(){return _2M(B(_2K(_2W.a)),_2I,_2W.b);});},_2X=new T(function(){return B(unCStr(": "));}),_2Y=new T(function(){return B(unCStr(")"));}),_2Z=new T(function(){return B(unCStr(" ("));}),_30=new T(function(){return B(unCStr("interrupted"));}),_31=new T(function(){return B(unCStr("system error"));}),_32=new T(function(){return B(unCStr("unsatisified constraints"));}),_33=new T(function(){return B(unCStr("user error"));}),_34=new T(function(){return B(unCStr("permission denied"));}),_35=new T(function(){return B(unCStr("illegal operation"));}),_36=new T(function(){return B(unCStr("end of file"));}),_37=new T(function(){return B(unCStr("resource exhausted"));}),_38=new T(function(){return B(unCStr("resource busy"));}),_39=new T(function(){return B(unCStr("does not exist"));}),_3a=new T(function(){return B(unCStr("already exists"));}),_3b=new T(function(){return B(unCStr("resource vanished"));}),_3c=new T(function(){return B(unCStr("timeout"));}),_3d=new T(function(){return B(unCStr("unsupported operation"));}),_3e=new T(function(){return B(unCStr("hardware fault"));}),_3f=new T(function(){return B(unCStr("inappropriate type"));}),_3g=new T(function(){return B(unCStr("invalid argument"));}),_3h=new T(function(){return B(unCStr("failed"));}),_3i=new T(function(){return B(unCStr("protocol error"));}),_3j=function(_3k,_3l){switch(E(_3k)){case 0:return new F(function(){return _0(_3a,_3l);});break;case 1:return new F(function(){return _0(_39,_3l);});break;case 2:return new F(function(){return _0(_38,_3l);});break;case 3:return new F(function(){return _0(_37,_3l);});break;case 4:return new F(function(){return _0(_36,_3l);});break;case 5:return new F(function(){return _0(_35,_3l);});break;case 6:return new F(function(){return _0(_34,_3l);});break;case 7:return new F(function(){return _0(_33,_3l);});break;case 8:return new F(function(){return _0(_32,_3l);});break;case 9:return new F(function(){return _0(_31,_3l);});break;case 10:return new F(function(){return _0(_3i,_3l);});break;case 11:return new F(function(){return _0(_3h,_3l);});break;case 12:return new F(function(){return _0(_3g,_3l);});break;case 13:return new F(function(){return _0(_3f,_3l);});break;case 14:return new F(function(){return _0(_3e,_3l);});break;case 15:return new F(function(){return _0(_3d,_3l);});break;case 16:return new F(function(){return _0(_3c,_3l);});break;case 17:return new F(function(){return _0(_3b,_3l);});break;default:return new F(function(){return _0(_30,_3l);});}},_3m=new T(function(){return B(unCStr("}"));}),_3n=new T(function(){return B(unCStr("{handle: "));}),_3o=function(_3p,_3q,_3r,_3s,_3t,_3u){var _3v=new T(function(){var _3w=new T(function(){var _3x=new T(function(){var _3y=E(_3s);if(!_3y._){return E(_3u);}else{var _3z=new T(function(){return B(_0(_3y,new T(function(){return B(_0(_2Y,_3u));},1)));},1);return B(_0(_2Z,_3z));}},1);return B(_3j(_3q,_3x));}),_3A=E(_3r);if(!_3A._){return E(_3w);}else{return B(_0(_3A,new T(function(){return B(_0(_2X,_3w));},1)));}}),_3B=E(_3t);if(!_3B._){var _3C=E(_3p);if(!_3C._){return E(_3v);}else{var _3D=E(_3C.a);if(!_3D._){var _3E=new T(function(){var _3F=new T(function(){return B(_0(_3m,new T(function(){return B(_0(_2X,_3v));},1)));},1);return B(_0(_3D.a,_3F));},1);return new F(function(){return _0(_3n,_3E);});}else{var _3G=new T(function(){var _3H=new T(function(){return B(_0(_3m,new T(function(){return B(_0(_2X,_3v));},1)));},1);return B(_0(_3D.a,_3H));},1);return new F(function(){return _0(_3n,_3G);});}}}else{return new F(function(){return _0(_3B.a,new T(function(){return B(_0(_2X,_3v));},1));});}},_3I=function(_3J){var _3K=E(_3J);return new F(function(){return _3o(_3K.a,_3K.b,_3K.c,_3K.d,_3K.f,_4);});},_3L=function(_3M,_3N,_3O){var _3P=E(_3N);return new F(function(){return _3o(_3P.a,_3P.b,_3P.c,_3P.d,_3P.f,_3O);});},_3Q=function(_3R,_3S){var _3T=E(_3R);return new F(function(){return _3o(_3T.a,_3T.b,_3T.c,_3T.d,_3T.f,_3S);});},_3U=44,_3V=93,_3W=91,_3X=function(_3Y,_3Z,_40){var _41=E(_3Z);if(!_41._){return new F(function(){return unAppCStr("[]",_40);});}else{var _42=new T(function(){var _43=new T(function(){var _44=function(_45){var _46=E(_45);if(!_46._){return E(new T2(1,_3V,_40));}else{var _47=new T(function(){return B(A2(_3Y,_46.a,new T(function(){return B(_44(_46.b));})));});return new T2(1,_3U,_47);}};return B(_44(_41.b));});return B(A2(_3Y,_41.a,_43));});return new T2(1,_3W,_42);}},_48=function(_49,_4a){return new F(function(){return _3X(_3Q,_49,_4a);});},_4b=new T3(0,_3L,_3I,_48),_4c=new T(function(){return new T5(0,_2I,_4b,_4d,_2U,_3I);}),_4d=function(_4e){return new T2(0,_4c,_4e);},_4f="status-text",_4g="status",_4h="http",_4i="network",_4j="type",_4k=__Z,_4l=__Z,_4m=7,_4n=function(_4o,_){var _4p=__get(_4o,E(_4j)),_4q=String(_4p),_4r=strEq(_4q,E(_4i));if(!E(_4r)){var _4s=strEq(_4q,E(_4h));if(!E(_4s)){var _4t=new T(function(){var _4u=new T(function(){return B(unAppCStr("unknown type of ajax error: ",new T(function(){return fromJSStr(_4q);})));});return B(_4d(new T6(0,_4l,_4m,_4,_4u,_4l,_4l)));});return new F(function(){return die(_4t);});}else{var _4v=__get(_4o,E(_4g)),_4w=__get(_4o,E(_4f));return new T2(1,new T(function(){var _4x=Number(_4v);return jsTrunc(_4x);}),new T(function(){return String(_4w);}));}}else{return _4k;}},_4y=function(_4z,_){var _4A=E(_4z);if(!_4A._){return _4;}else{var _4B=B(_4n(E(_4A.a),_)),_4C=B(_4y(_4A.b,_));return new T2(1,_4B,_4C);}},_4D=function(_4E,_){var _4F=__arr2lst(0,_4E);return new F(function(){return _4y(_4F,_);});},_4G=function(_4H,_){return new F(function(){return _4D(E(_4H),_);});},_4I=function(_4J,_){return new F(function(){return _4n(E(_4J),_);});},_4K=new T2(0,_4I,_4G),_4L=function(_4M){return E(E(_4M).a);},_4N=function(_4O,_4P,_){var _4Q=__eq(_4P,E(_D));if(!E(_4Q)){var _4R=__isUndef(_4P);if(!E(_4R)){var _4S=B(A3(_4L,_4O,_4P,_));return new T1(1,_4S);}else{return _4l;}}else{return _4l;}},_4T=function(_4U,_){return new F(function(){return _4N(_4K,E(_4U),_);});},_4V=function(_4W,_4X,_){var _4Y=__arr2lst(0,_4X),_4Z=function(_50,_){var _51=E(_50);if(!_51._){return _4;}else{var _52=_51.b,_53=E(_51.a),_54=__eq(_53,E(_D));if(!E(_54)){var _55=__isUndef(_53);if(!E(_55)){var _56=B(A3(_4L,_4W,_53,_)),_57=B(_4Z(_52,_));return new T2(1,new T1(1,_56),_57);}else{var _58=B(_4Z(_52,_));return new T2(1,_4l,_58);}}else{var _59=B(_4Z(_52,_));return new T2(1,_4l,_59);}}};return new F(function(){return _4Z(_4Y,_);});},_5a=function(_5b,_){return new F(function(){return _4V(_4K,E(_5b),_);});},_5c=new T2(0,_4T,_5a),_5d=2,_5e=function(_5f){return E(_5d);},_5g=function(_5h,_5i,_){var _5j=B(A2(_5h,new T(function(){var _5k=E(_5i),_5l=__eq(_5k,E(_D));if(!E(_5l)){var _5m=__isUndef(_5k);if(!E(_5m)){return new T1(1,_5k);}else{return __Z;}}else{return __Z;}}),_));return _D;},_5n=new T2(0,_5g,_5e),_5o=function(_5p){return E(E(_5p).a);},_5q=function(_5r,_5s,_5t,_5u){var _5v=new T(function(){return B(A1(_5t,new T(function(){var _5w=B(A3(_4L,_5r,_5u,_));return E(_5w);})));});return new F(function(){return A2(_5o,_5s,_5v);});},_5x=function(_5y){return E(E(_5y).b);},_5z=new T(function(){return B(unCStr("Prelude.undefined"));}),_5A=new T(function(){return B(err(_5z));}),_5B=function(_5C,_5D,_5E){var _5F=__createJSFunc(1+B(A2(_5x,_5D,new T(function(){return B(A1(_5E,_5A));})))|0,function(_5G){return new F(function(){return _5q(_5C,_5D,_5E,_5G);});});return E(_5F);},_5H=function(_5I){return new F(function(){return _5B(_5c,_5n,_5I);});},_5J=function(_5K,_5L,_5M){return new F(function(){return _5B(_5K,_5L,_5M);});},_5N=function(_5O,_5P,_5Q){var _5R=__lst2arr(B(_G(function(_5S){return new F(function(){return _5J(_5O,_5P,_5S);});},_5Q)));return E(_5R);},_5T=function(_5U){return new F(function(){return _5N(_5c,_5n,_5U);});},_5V=new T2(0,_5H,_5T),_5W=function(_5X,_5Y,_5Z,_){var _60=__apply(_5Y,E(_5Z));return new F(function(){return A3(_4L,_5X,_60,_);});},_61=function(_62,_63,_64,_){return new F(function(){return _5W(_62,E(_63),_64,_);});},_65=function(_66,_67,_68,_){return new F(function(){return _61(_66,_67,_68,_);});},_69=function(_6a,_6b,_){return new F(function(){return _65(_x,_6a,_6b,_);});},_6c=function(_6d){return E(E(_6d).c);},_6e=0,_6f=new T(function(){return eval("(function(method, uri, mimeout, responseType, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, uri);xhr.responseType = responseType;if(mimeout != \'\') {xhr.setRequestHeader(\'Content-type\', mimeout);}xhr.addEventListener(\'load\', function() {if(xhr.status < 400) {cb(null, xhr.response);}else {cb({\'type\':\'http\', \'status\':xhr.status, \'status-text\': xhr.statusText}, null);}});xhr.addEventListener(\'error\', function() {if(xhr.status != 0) {cb({\'type\':\'http\', \'status\':xhr.status, \'status-text\': xhr.statusText}, null);} else {cb({\'type\':\'network\'}, null);}});xhr.send(postdata);})");}),_6g=function(_6h){return E(E(_6h).b);},_6i=function(_6j){return E(E(_6j).b);},_6k=new T(function(){return B(unCStr("base"));}),_6l=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6m=new T(function(){return B(unCStr("PatternMatchFail"));}),_6n=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6k,_6l,_6m),_6o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6n,_4,_4),_6p=function(_6q){return E(_6o);},_6r=function(_6s){var _6t=E(_6s);return new F(function(){return _2M(B(_2K(_6t.a)),_6p,_6t.b);});},_6u=function(_6v){return E(E(_6v).a);},_6w=function(_6x){return new T2(0,_6y,_6x);},_6z=function(_6A,_6B){return new F(function(){return _0(E(_6A).a,_6B);});},_6C=function(_6D,_6E){return new F(function(){return _3X(_6z,_6D,_6E);});},_6F=function(_6G,_6H,_6I){return new F(function(){return _0(E(_6H).a,_6I);});},_6J=new T3(0,_6F,_6u,_6C),_6y=new T(function(){return new T5(0,_6p,_6J,_6w,_6r,_6u);}),_6K=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_6L=function(_6M){return E(E(_6M).c);},_6N=function(_6O,_6P){return new F(function(){return die(new T(function(){return B(A2(_6L,_6P,_6O));}));});},_6Q=function(_6R,_6S){return new F(function(){return _6N(_6R,_6S);});},_6T=function(_6U,_6V){var _6W=E(_6V);if(!_6W._){return new T2(0,_4,_4);}else{var _6X=_6W.a;if(!B(A1(_6U,_6X))){return new T2(0,_4,_6W);}else{var _6Y=new T(function(){var _6Z=B(_6T(_6U,_6W.b));return new T2(0,_6Z.a,_6Z.b);});return new T2(0,new T2(1,_6X,new T(function(){return E(E(_6Y).a);})),new T(function(){return E(E(_6Y).b);}));}}},_70=32,_71=new T(function(){return B(unCStr("\n"));}),_72=function(_73){return (E(_73)==124)?false:true;},_74=function(_75,_76){var _77=B(_6T(_72,B(unCStr(_75)))),_78=_77.a,_79=function(_7a,_7b){var _7c=new T(function(){var _7d=new T(function(){return B(_0(_76,new T(function(){return B(_0(_7b,_71));},1)));});return B(unAppCStr(": ",_7d));},1);return new F(function(){return _0(_7a,_7c);});},_7e=E(_77.b);if(!_7e._){return new F(function(){return _79(_78,_4);});}else{if(E(_7e.a)==124){return new F(function(){return _79(_78,new T2(1,_70,_7e.b));});}else{return new F(function(){return _79(_78,_4);});}}},_7f=function(_7g){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_7g,_6K));})),_6y);});},_7h=new T(function(){return B(_7f("src/Haste/Ajax.hs:(61,7)-(63,60)|case"));}),_7i="PUT",_7j="POST",_7k="DELETE",_7l="GET",_7m=function(_7n){return E(E(_7n).c);},_7o=new T1(1,_4),_7p=function(_){return new F(function(){return nMV(_7o);});},_7q=new T0(2),_7r=function(_7s,_7t,_7u){var _7v=function(_7w){var _7x=function(_){var _7y=E(_7t),_7z=rMV(_7y),_7A=E(_7z);if(!_7A._){var _7B=new T(function(){var _7C=new T(function(){return B(A1(_7w,_5));});return B(_0(_7A.b,new T2(1,new T2(0,_7u,function(_7D){return E(_7C);}),_4)));}),_=wMV(_7y,new T2(0,_7A.a,_7B));return _7q;}else{var _7E=E(_7A.a);if(!_7E._){var _=wMV(_7y,new T2(0,_7u,_4));return new T(function(){return B(A1(_7w,_5));});}else{var _=wMV(_7y,new T1(1,_7E.b));return new T1(1,new T2(1,new T(function(){return B(A1(_7w,_5));}),new T2(1,new T(function(){return B(A2(_7E.a,_7u,_2c));}),_4)));}}};return new T1(0,_7x);};return new F(function(){return A2(_6g,_7s,_7v);});},_7F=function(_7G){return E(E(_7G).d);},_7H=function(_7I,_7J){var _7K=function(_7L){var _7M=function(_){var _7N=E(_7J),_7O=rMV(_7N),_7P=E(_7O);if(!_7P._){var _7Q=_7P.a,_7R=E(_7P.b);if(!_7R._){var _=wMV(_7N,_7o);return new T(function(){return B(A1(_7L,_7Q));});}else{var _7S=E(_7R.a),_=wMV(_7N,new T2(0,_7S.a,_7R.b));return new T1(1,new T2(1,new T(function(){return B(A1(_7L,_7Q));}),new T2(1,new T(function(){return B(A1(_7S.b,_2c));}),_4)));}}else{var _7T=new T(function(){var _7U=function(_7V){var _7W=new T(function(){return B(A1(_7L,_7V));});return function(_7X){return E(_7W);};};return B(_0(_7P.a,new T2(1,_7U,_4)));}),_=wMV(_7N,new T1(1,_7T));return _7q;}};return new T1(0,_7M);};return new F(function(){return A2(_6g,_7I,_7K);});},_7Y=function(_7Z,_80,_81,_82,_83,_84){var _85=B(_2x(_7Z)),_86=new T(function(){return B(_6g(_7Z));}),_87=new T(function(){return B(_6i(_85));}),_88=B(_2z(_85)),_89=new T(function(){return B(_2B(_81));}),_8a=new T(function(){var _8b=function(_8c){var _8d=E(_84),_8e=E(_82),_8f=strEq(E(_i),_8e);if(!E(_8f)){var _8g=E(_8e);}else{var _8g=B(A2(_7m,_80,_6e));}var _8h=B(A2(_7F,_81,_6e)),_8i=E(_D);return function(_5G){return new F(function(){return _2o(_5V,_69,_6f,new T2(1,_8i,new T2(1,_8h,new T2(1,_8g,new T2(1,_8d,new T2(1,_8c,_4))))),_5G);});};},_8j=function(_8k,_8l){var _8m=E(_84),_8n=E(_82),_8o=strEq(E(_i),_8n);if(!E(_8o)){var _8p=E(_8n);}else{var _8p=B(A2(_7m,_80,_6e));}var _8q=B(A2(_7F,_81,_6e)),_8r=E(_8k);return function(_5G){return new F(function(){return _2o(_5V,_69,_6f,new T2(1,_8r,new T2(1,_8q,new T2(1,_8p,new T2(1,_8m,new T2(1,_8l,_4))))),_5G);});};},_8s=E(_83);switch(_8s._){case 0:return B(_8b(E(_7l)));break;case 1:return B(_8b(E(_7k)));break;case 2:return B(_8j(new T(function(){return B(A2(_2m,B(_2v(_80)),_8s.a));}),E(_7j)));break;default:return B(_8j(new T(function(){return B(A2(_2m,B(_2v(_80)),_8s.a));}),E(_7i)));}}),_8t=function(_8u){var _8v=new T(function(){return B(A1(_86,new T(function(){return B(_7H(_2l,_8u));})));}),_8w=new T(function(){var _8x=new T(function(){var _8y=function(_8z,_8A,_){var _8B=E(_8A);if(!_8B._){var _8C=E(_8z);if(!_8C._){return E(_7h);}else{return new F(function(){return _c(new T(function(){return B(A(_7r,[_2l,_8u,new T1(0,_8C.a),_2c]));}),_4,_);});}}else{var _8D=B(A3(_4L,_89,_8B.a,_));return new F(function(){return _c(new T(function(){return B(A(_7r,[_2l,_8u,new T1(1,_8D),_2c]));}),_4,_);});}};return B(A1(_8a,_8y));});return B(A1(_87,_8x));});return new F(function(){return A3(_6c,_88,_8w,_8v);});};return new F(function(){return A3(_1V,_88,new T(function(){return B(A2(_6i,_85,_7p));}),_8t);});},_8E="w8",_8F=function(_8G){return E(_8E);},_8H=function(_8I,_8J){var _8K=E(_8J);return new T2(0,_8K.a,_8K.b);},_8L=function(_8M,_8N){return E(_8N).c;},_8O=function(_8P){var _8Q=B(A1(_8P,_));return E(_8Q);},_8R=function(_8S,_8T,_8U,_8V){var _8W=function(_){var _8X=E(_8U),_8Y=_8X.d,_8Z=_8Y["byteLength"],_90=newByteArr(_8Z),_91=_90,_92=memcpy(_91,_8Y,_8Z>>>0),_93=function(_94,_){while(1){var _95=E(_94);if(!_95._){return _5;}else{var _96=E(_95.a),_97=E(_96.a),_98=_91["v"]["w8"][_97],_=_91["v"]["w8"][_97]=B(A2(_8T,_98,_96.b));_94=_95.b;continue;}}},_99=B(_93(_8V,_));return new T4(0,E(_8X.a),E(_8X.b),_8X.c,_91);};return new F(function(){return _8O(_8W);});},_9a=function(_9b){return E(E(_9b).f);},_9c=new T(function(){return B(unCStr("Negative range size"));}),_9d=new T(function(){return B(err(_9c));}),_9e=function(_9f,_9g,_9h,_9i,_9j){var _9k=E(_9i),_9l=function(_){var _9m=B(A2(_9a,_9f,_9k)),_9n=newByteArr(_9m),_9o=_9n;if(_9m>=0){var _9p=_9m-1|0,_9q=function(_){var _9r=function(_9s,_){while(1){var _9t=E(_9s);if(!_9t._){return _5;}else{var _9u=E(_9t.a),_9v=E(_9u.a),_9w=_9o["v"]["w8"][_9v],_=_9o["v"]["w8"][_9v]=B(A2(_9g,_9w,_9u.b));_9s=_9t.b;continue;}}},_9x=B(_9r(_9j,_));return new T4(0,E(_9k.a),E(_9k.b),_9m,_9o);};if(0<=_9p){var _9y=function(_9z,_){while(1){var _=_9o["v"]["w8"][_9z]=E(_9h);if(_9z!=_9p){var _9A=_9z+1|0;_9z=_9A;continue;}else{return _5;}}},_9B=B(_9y(0,_));return new F(function(){return _9q(_);});}else{return new F(function(){return _9q(_);});}}else{return E(_9d);}},_9C=E(_9l);return new F(function(){return _8O(_9C);});},_9D=function(_9E,_9F,_9G){var _9H=E(_9F),_9I=function(_){var _9J=B(A2(_9a,_9E,_9H)),_9K=newByteArr(_9J),_9L=_9K;if(_9J>=0){var _9M=_9J-1|0,_9N=function(_){var _9O=function(_9P,_){while(1){var _9Q=E(_9P);if(!_9Q._){return _5;}else{var _9R=E(_9Q.a),_=_9L["v"]["w8"][E(_9R.a)]=E(_9R.b);_9P=_9Q.b;continue;}}},_9S=B(_9O(_9G,_));return new T4(0,E(_9H.a),E(_9H.b),_9J,_9L);};if(0<=_9M){var _9T=function(_9U,_){while(1){var _=_9L["v"]["w8"][_9U]=0;if(_9U!=_9M){var _9V=_9U+1|0;_9U=_9V;continue;}else{return _5;}}},_9W=B(_9T(0,_));return new F(function(){return _9N(_);});}else{return new F(function(){return _9N(_);});}}else{return E(_9d);}},_9X=E(_9I);return new F(function(){return _8O(_9X);});},_9Y=function(_9Z,_a0,_a1){return E(_a0).d["v"]["w8"][E(_a1)];},_a2=function(_a3,_a4,_a5){var _a6=function(_){var _a7=E(_a4),_a8=_a7.d,_a9=_a8["byteLength"],_aa=newByteArr(_a9),_ab=_aa,_ac=memcpy(_ab,_a8,_a9>>>0),_ad=function(_ae,_){while(1){var _af=E(_ae);if(!_af._){return _5;}else{var _ag=E(_af.a),_=_ab["v"]["w8"][E(_ag.a)]=E(_ag.b);_ae=_af.b;continue;}}},_ah=B(_ad(_a5,_));return new T4(0,E(_a7.a),E(_a7.b),_a7.c,_ab);};return new F(function(){return _8O(_a6);});},_ai={_:0,a:_8H,b:_8L,c:_9D,d:_9Y,e:_a2,f:_8R,g:_9e},_aj=function(_ak,_al,_){var _am=E(_al);return new T2(0,_am.a,_am.b);},_an=function(_ao,_ap,_){return new F(function(){return _aj(_ao,_ap,_);});},_aq=function(_ar,_as,_){return E(_as).c;},_at=function(_ao,_ap,_){return new F(function(){return _aq(_ao,_ap,_);});},_au=new T(function(){return B(unCStr("Negative range size"));}),_av=new T(function(){return B(err(_au));}),_aw=function(_ax,_ay,_az,_aA,_){var _aB=B(A2(_9a,_ax,new T2(0,_ay,_az))),_aC=newByteArr(_aB);if(_aB>=0){var _aD=_aB-1|0,_aE=new T(function(){return new T4(0,E(_ay),E(_az),_aB,_aC);});if(0<=_aD){var _aF=function(_aG,_){while(1){var _=E(_aE).d["v"]["w8"][_aG]=E(_aA);if(_aG!=_aD){var _aH=_aG+1|0;_aG=_aH;continue;}else{return _5;}}},_aI=B(_aF(0,_));return _aE;}else{return _aE;}}else{return E(_av);}},_aJ=function(_aK,_aL,_aM,_){var _aN=E(_aL);return new F(function(){return _aw(_aK,_aN.a,_aN.b,_aM,_);});},_aO=function(_aP,_ao,_ap,_){return new F(function(){return _aJ(_aP,_ao,_ap,_);});},_aQ=function(_aR,_aS,_aT,_){var _aU=B(A2(_9a,_aR,new T2(0,_aS,_aT))),_aV=newByteArr(_aU);return new T(function(){return new T4(0,E(_aS),E(_aT),_aU,_aV);});},_aW=function(_aX,_aY,_){var _aZ=E(_aY);return new F(function(){return _aQ(_aX,_aZ.a,_aZ.b,_);});},_b0=function(_ao,_ap,_){return new F(function(){return _aW(_ao,_ap,_);});},_b1=function(_b2,_b3,_b4,_){return E(_b3).d["v"]["w8"][E(_b4)];},_b5=function(_aP,_ao,_ap,_){return new F(function(){return _b1(_aP,_ao,_ap,_);});},_b6=function(_b7,_b8,_b9,_ba,_){var _=E(_b8).d["v"]["w8"][E(_b9)]=E(_ba);return _5;},_bb=function(_bc,_aP,_ao,_ap,_){return new F(function(){return _b6(_bc,_aP,_ao,_ap,_);});},_bd=function(_be,_bf,_){var _bg=B(A1(_be,_)),_bh=B(A1(_bf,_));return _bg;},_bi=function(_bj,_bk,_){var _bl=B(A1(_bj,_)),_bm=B(A1(_bk,_));return new T(function(){return B(A1(_bl,_bm));});},_bn=function(_bo,_bp,_){var _bq=B(A1(_bp,_));return _bo;},_br=new T2(0,_24,_bn),_bs=function(_bt,_){return _bt;},_bu=function(_bv,_bw,_){var _bx=B(A1(_bv,_));return new F(function(){return A1(_bw,_);});},_by=new T5(0,_br,_bs,_bi,_bu,_bd),_bz=new T(function(){return E(_4c);}),_bA=function(_bB){return new T6(0,_4l,_4m,_4,_bB,_4l,_4l);},_bC=function(_bD,_){var _bE=new T(function(){return B(A2(_6L,_bz,new T(function(){return B(A1(_bA,_bD));})));});return new F(function(){return die(_bE);});},_bF=function(_bG,_){return new F(function(){return _bC(_bG,_);});},_bH=function(_bI){return new F(function(){return A1(_bF,_bI);});},_bJ=function(_bK,_bL,_){var _bM=B(A1(_bK,_));return new F(function(){return A2(_bL,_bM,_);});},_bN=new T5(0,_by,_bJ,_bu,_bs,_bH),_bO={_:0,a:_bN,b:_an,c:_at,d:_aO,e:_b0,f:_b0,g:_b5,h:_bb},_bP=new T3(0,_ai,_bO,_8F),_bQ="deltaZ",_bR="deltaY",_bS="deltaX",_bT=function(_bU,_bV){var _bW=jsShowI(_bU);return new F(function(){return _0(fromJSStr(_bW),_bV);});},_bX=41,_bY=40,_bZ=function(_c0,_c1,_c2){if(_c1>=0){return new F(function(){return _bT(_c1,_c2);});}else{if(_c0<=6){return new F(function(){return _bT(_c1,_c2);});}else{return new T2(1,_bY,new T(function(){var _c3=jsShowI(_c1);return B(_0(fromJSStr(_c3),new T2(1,_bX,_c2)));}));}}},_c4=new T(function(){return B(unCStr(")"));}),_c5=new T(function(){return B(_bZ(0,2,_c4));}),_c6=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_c5));}),_c7=function(_c8){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_bZ(0,_c8,_c6));}))));});},_c9=function(_ca,_){return new T(function(){var _cb=Number(E(_ca)),_cc=jsTrunc(_cb);if(_cc<0){return B(_c7(_cc));}else{if(_cc>2){return B(_c7(_cc));}else{return _cc;}}});},_cd=0,_ce=new T3(0,_cd,_cd,_cd),_cf="button",_cg=new T(function(){return eval("jsGetMouseCoords");}),_ch=function(_ci,_){var _cj=E(_ci);if(!_cj._){return _4;}else{var _ck=B(_ch(_cj.b,_));return new T2(1,new T(function(){var _cl=Number(E(_cj.a));return jsTrunc(_cl);}),_ck);}},_cm=function(_cn,_){var _co=__arr2lst(0,_cn);return new F(function(){return _ch(_co,_);});},_cp=function(_cq,_){return new F(function(){return _cm(E(_cq),_);});},_cr=function(_cs,_){return new T(function(){var _ct=Number(E(_cs));return jsTrunc(_ct);});},_cu=new T2(0,_cr,_cp),_cv=function(_cw,_){var _cx=E(_cw);if(!_cx._){return _4;}else{var _cy=B(_cv(_cx.b,_));return new T2(1,_cx.a,_cy);}},_cz=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_cA=new T6(0,_4l,_4m,_4,_cz,_4l,_4l),_cB=new T(function(){return B(_4d(_cA));}),_cC=function(_){return new F(function(){return die(_cB);});},_cD=function(_cE,_cF,_cG,_){var _cH=__arr2lst(0,_cG),_cI=B(_cv(_cH,_)),_cJ=E(_cI);if(!_cJ._){return new F(function(){return _cC(_);});}else{var _cK=E(_cJ.b);if(!_cK._){return new F(function(){return _cC(_);});}else{if(!E(_cK.b)._){var _cL=B(A3(_4L,_cE,_cJ.a,_)),_cM=B(A3(_4L,_cF,_cK.a,_));return new T2(0,_cL,_cM);}else{return new F(function(){return _cC(_);});}}}},_cN=function(_cO,_cP,_){if(E(_cO)==7){var _cQ=__app1(E(_cg),_cP),_cR=B(_cD(_cu,_cu,_cQ,_)),_cS=__get(_cP,E(_bS)),_cT=__get(_cP,E(_bR)),_cU=__get(_cP,E(_bQ));return new T(function(){return new T3(0,E(_cR),E(_4l),E(new T3(0,_cS,_cT,_cU)));});}else{var _cV=__app1(E(_cg),_cP),_cW=B(_cD(_cu,_cu,_cV,_)),_cX=__get(_cP,E(_cf)),_cY=__eq(_cX,E(_D));if(!E(_cY)){var _cZ=__isUndef(_cX);if(!E(_cZ)){var _d0=B(_c9(_cX,_));return new T(function(){return new T3(0,E(_cW),E(new T1(1,_d0)),E(_ce));});}else{return new T(function(){return new T3(0,E(_cW),E(_4l),E(_ce));});}}else{return new T(function(){return new T3(0,E(_cW),E(_4l),E(_ce));});}}},_d1=function(_d2,_d3,_){return new F(function(){return _cN(_d2,E(_d3),_);});},_d4="mouseout",_d5="mouseover",_d6="mousemove",_d7="mouseup",_d8="mousedown",_d9="dblclick",_da="click",_db="wheel",_dc=function(_dd){switch(E(_dd)){case 0:return E(_da);case 1:return E(_d9);case 2:return E(_d8);case 3:return E(_d7);case 4:return E(_d6);case 5:return E(_d5);case 6:return E(_d4);default:return E(_db);}},_de=new T2(0,_dc,_d1),_df=function(_dg){return E(_dg);},_dh=function(_di){return E(E(_di).d);},_dj=function(_dk,_dl){return new F(function(){return A2(_dh,B(_2z(_dk)),new T1(1,_dl));});},_dm=new T2(0,_2j,_dj),_dn=new T2(0,_bN,_2j),_do=new T2(0,_dn,_bs),_dp=new T(function(){return B(unCStr("NoMethodError"));}),_dq=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_6k,_6l,_dp),_dr=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_dq,_4,_4),_ds=function(_dt){return E(_dr);},_du=function(_dv){var _dw=E(_dv);return new F(function(){return _2M(B(_2K(_dw.a)),_ds,_dw.b);});},_dx=function(_dy){return E(E(_dy).a);},_dz=function(_6x){return new T2(0,_dA,_6x);},_dB=function(_dC,_dD){return new F(function(){return _0(E(_dC).a,_dD);});},_dE=function(_dF,_dG){return new F(function(){return _3X(_dB,_dF,_dG);});},_dH=function(_dI,_dJ,_dK){return new F(function(){return _0(E(_dJ).a,_dK);});},_dL=new T3(0,_dH,_dx,_dE),_dA=new T(function(){return new T5(0,_ds,_dL,_dz,_du,_dx);}),_dM=new T(function(){return B(unCStr("No instance nor default method for class operation"));}),_dN=function(_dO){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_dO,_dM));})),_dA);});},_dP=new T(function(){return B(_dN("Data/Binary/Put.hs:17:10-19|>>="));}),_dQ=function(_dR){return E(_dP);},_dS=new T(function(){return B(unCStr(")"));}),_dT=function(_dU,_dV){var _dW=new T(function(){var _dX=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_dV,_4)),_dS));})));},1);return B(_0(B(_bZ(0,_dU,_4)),_dX));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_dW)));});},_dY=function(_dZ){return new F(function(){return _bZ(0,E(_dZ),_4);});},_e0=function(_e1,_e2,_e3){return new F(function(){return _bZ(E(_e1),E(_e2),_e3);});},_e4=function(_e5,_e6){return new F(function(){return _bZ(0,E(_e5),_e6);});},_e7=function(_e8,_e9){return new F(function(){return _3X(_e4,_e8,_e9);});},_ea=new T3(0,_e0,_dY,_e7),_eb=0,_ec=function(_ed,_ee,_ef){return new F(function(){return A1(_ed,new T2(1,_3U,new T(function(){return B(A1(_ee,_ef));})));});},_eg=new T(function(){return B(unCStr(": empty list"));}),_eh=new T(function(){return B(unCStr("Prelude."));}),_ei=function(_ej){return new F(function(){return err(B(_0(_eh,new T(function(){return B(_0(_ej,_eg));},1))));});},_ek=new T(function(){return B(unCStr("foldr1"));}),_el=new T(function(){return B(_ei(_ek));}),_em=function(_en,_eo){var _ep=E(_eo);if(!_ep._){return E(_el);}else{var _eq=_ep.a,_er=E(_ep.b);if(!_er._){return E(_eq);}else{return new F(function(){return A2(_en,_eq,new T(function(){return B(_em(_en,_er));}));});}}},_es=new T(function(){return B(unCStr(" out of range "));}),_et=new T(function(){return B(unCStr("}.index: Index "));}),_eu=new T(function(){return B(unCStr("Ix{"));}),_ev=new T2(1,_bX,_4),_ew=new T2(1,_bX,_ev),_ex=0,_ey=function(_ez){return E(E(_ez).a);},_eA=function(_eB,_eC,_eD,_eE,_eF){var _eG=new T(function(){var _eH=new T(function(){var _eI=new T(function(){var _eJ=new T(function(){var _eK=new T(function(){return B(A3(_em,_ec,new T2(1,new T(function(){return B(A3(_ey,_eD,_ex,_eE));}),new T2(1,new T(function(){return B(A3(_ey,_eD,_ex,_eF));}),_4)),_ew));});return B(_0(_es,new T2(1,_bY,new T2(1,_bY,_eK))));});return B(A(_ey,[_eD,_eb,_eC,new T2(1,_bX,_eJ)]));});return B(_0(_et,new T2(1,_bY,_eI)));},1);return B(_0(_eB,_eH));},1);return new F(function(){return err(B(_0(_eu,_eG)));});},_eL=function(_eM,_eN,_eO,_eP,_eQ){return new F(function(){return _eA(_eM,_eN,_eQ,_eO,_eP);});},_eR=function(_eS,_eT,_eU,_eV){var _eW=E(_eU);return new F(function(){return _eL(_eS,_eT,_eW.a,_eW.b,_eV);});},_eX=function(_eY,_eZ,_f0,_f1){return new F(function(){return _eR(_f1,_f0,_eZ,_eY);});},_f2=new T(function(){return B(unCStr("Int"));}),_f3=function(_f4,_f5,_f6){return new F(function(){return _eX(_ea,new T2(0,_f5,_f6),_f4,_f2);});},_f7=function(_f8,_f9,_fa,_fb,_fc,_fd){var _fe=_f8+_fd|0;if(_f9>_fe){return new F(function(){return _f3(_fe,_f9,_fa);});}else{if(_fe>_fa){return new F(function(){return _f3(_fe,_f9,_fa);});}else{var _ff=_fe-_f9|0;if(0>_ff){return new F(function(){return _dT(_ff,_fb);});}else{if(_ff>=_fb){return new F(function(){return _dT(_ff,_fb);});}else{return _fc["v"]["w8"][_ff];}}}}},_fg=function(_fh){return new F(function(){return err(B(unAppCStr("getWord8: no bytes left at ",new T(function(){return B(_bZ(0,_fh,_4));}))));});},_fi=function(_fj,_fk,_fl,_fm){if(_fm>=_fk){return new F(function(){return _fg(_fm);});}else{return new T2(0,new T(function(){var _fn=E(_fl);return B(_f7(_fj,E(_fn.a),E(_fn.b),_fn.c,_fn.d,_fm));}),_fm+1|0);}},_fo=function(_fp,_fq,_fr,_fs){var _ft=B(_fi(_fp,_fq,_fr,_fs)),_fu=_ft.b,_fv=E(_ft.a);if(_fv>127){var _fw=B(_fo(_fp,_fq,_fr,E(_fu)));return new T2(0,new T(function(){return (E(_fw.a)<<7>>>0|(_fv&127)>>>0)>>>0;}),_fw.b);}else{return new T2(0,_fv,_fu);}},_fx=new T(function(){return B(unCStr("too few bytes"));}),_fy=new T(function(){return B(err(_fx));}),_fz=function(_fA,_fB,_fC,_fD){var _fE=B(_fo(_fA,_fB,_fC,_fD)),_fF=E(_fE.b),_fG=E(_fE.a)&4294967295;return ((_fF+_fG|0)<=_fB)?new T2(0,new T(function(){var _fH=_fB-_fF|0;if(_fG>_fH){return new T3(0,_fA+_fF|0,_fH,_fC);}else{return new T3(0,_fA+_fF|0,_fG,_fC);}}),_fF+_fG|0):E(_fy);},_fI=function(_fJ,_fK){var _fL=E(_fJ),_fM=B(_fz(_fL.a,_fL.b,_fL.c,E(_fK)));return new T2(0,_fM.a,_fM.b);},_fN=new T2(0,_dQ,_fI),_fO=function(_fP){return E(_dP);},_fQ=function(_fR){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_bZ(9,_fR,_4));}))));});},_fS=function(_fT,_fU,_fV,_fW){var _fX=B(_fi(_fT,_fU,_fV,_fW)),_fY=_fX.b,_fZ=E(_fX.a)&4294967295;if(_fZ>=128){if(_fZ>=224){if(_fZ>=240){var _g0=B(_fi(_fT,_fU,_fV,E(_fY))),_g1=B(_fi(_fT,_fU,_fV,E(_g0.b))),_g2=B(_fi(_fT,_fU,_fV,E(_g1.b))),_g3=128^E(_g2.a)&4294967295|(128^E(_g1.a)&4294967295|(128^E(_g0.a)&4294967295|(240^_fZ)<<6)<<6)<<6;if(_g3>>>0>1114111){return new F(function(){return _fQ(_g3);});}else{return new T2(0,_g3,_g2.b);}}else{var _g4=B(_fi(_fT,_fU,_fV,E(_fY))),_g5=B(_fi(_fT,_fU,_fV,E(_g4.b))),_g6=128^E(_g5.a)&4294967295|(128^E(_g4.a)&4294967295|(224^_fZ)<<6)<<6;if(_g6>>>0>1114111){return new F(function(){return _fQ(_g6);});}else{return new T2(0,_g6,_g5.b);}}}else{var _g7=B(_fi(_fT,_fU,_fV,E(_fY))),_g8=128^E(_g7.a)&4294967295|(192^_fZ)<<6;if(_g8>>>0>1114111){return new F(function(){return _fQ(_g8);});}else{return new T2(0,_g8,_g7.b);}}}else{if(_fZ>>>0>1114111){return new F(function(){return _fQ(_fZ);});}else{return new T2(0,_fZ,_fY);}}},_g9=function(_ga,_gb){var _gc=E(_ga),_gd=B(_fS(_gc.a,_gc.b,_gc.c,E(_gb)));return new T2(0,_gd.a,_gd.b);},_ge=function(_gf,_gg,_gh){var _gi=E(_gf);if(!_gi._){return new T2(0,_4,_gh);}else{var _gj=new T(function(){return B(A2(_gi.a,_gg,_gh));}),_gk=B(_ge(_gi.b,_gg,new T(function(){return E(E(_gj).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_gj).a);}),_gk.a),_gk.b);}},_gl=function(_gm,_gn,_go,_gp){if(0>=_gm){return new F(function(){return _ge(_4,_go,_gp);});}else{var _gq=function(_gr){var _gs=E(_gr);return (_gs==1)?E(new T2(1,_gn,_4)):new T2(1,_gn,new T(function(){return B(_gq(_gs-1|0));}));};return new F(function(){return _ge(B(_gq(_gm)),_go,_gp);});}},_gt=function(_gu,_gv,_gw,_gx){var _gy=B(_fo(_gu,_gv,_gw,_gx));return new F(function(){return _gl(E(_gy.a)&4294967295,_g9,new T3(0,_gu,_gv,_gw),_gy.b);});},_gz=function(_gA,_gB){var _gC=E(_gA),_gD=B(_gt(_gC.a,_gC.b,_gC.c,E(_gB)));return new T2(0,_gD.a,_gD.b);},_gE=new T2(0,_fO,_gz),_gF=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_gG=new T(function(){return B(err(_gF));}),_gH=function(_gI,_gJ,_gK){var _gL=function(_){var _gM=E(_gJ),_gN=_gM.c,_gO=newArr(_gN,_gG),_gP=_gO,_gQ=function(_gR,_){while(1){if(_gR!=_gN){var _=_gP[_gR]=_gM.d[_gR],_gS=_gR+1|0;_gR=_gS;continue;}else{return E(_);}}},_=B(_gQ(0,_)),_gT=function(_gU,_){while(1){var _gV=E(_gU);if(!_gV._){return new T4(0,E(_gM.a),E(_gM.b),_gN,_gP);}else{var _gW=E(_gV.a),_=_gP[E(_gW.a)]=_gW.b;_gU=_gV.b;continue;}}};return new F(function(){return _gT(_gK,_);});};return new F(function(){return _8O(_gL);});},_gX=function(_gY,_gZ,_h0){return new F(function(){return _gH(_gY,_gZ,_h0);});},_h1=function(_h2,_h3,_h4){return E(E(_h3).d[E(_h4)]);},_h5=function(_h6,_h7,_h8){return new F(function(){return _h1(_h6,_h7,_h8);});},_h9=function(_ha,_hb,_hc){var _hd=E(_hb),_he=B(A2(_9a,_ha,_hd)),_hf=function(_){var _hg=newArr(_he,_gG),_hh=_hg,_hi=function(_hj,_){while(1){var _hk=B((function(_hl,_){var _hm=E(_hl);if(!_hm._){return new T(function(){return new T4(0,E(_hd.a),E(_hd.b),_he,_hh);});}else{var _hn=E(_hm.a),_=_hh[E(_hn.a)]=_hn.b;_hj=_hm.b;return __continue;}})(_hj,_));if(_hk!=__continue){return _hk;}}};return new F(function(){return _hi(_hc,_);});};return new F(function(){return _8O(_hf);});},_ho=function(_hp,_hq,_hr){return new F(function(){return _h9(_hp,_hq,_hr);});},_hs=function(_ht,_hu){return E(_hu).c;},_hv=function(_hw,_hx){return new F(function(){return _hs(_hw,_hx);});},_hy=function(_hz,_hA){var _hB=E(_hA);return new T2(0,_hB.a,_hB.b);},_hC=function(_hD,_hE){return new F(function(){return _hy(_hD,_hE);});},_hF=function(_hG,_hH,_hI,_hJ){var _hK=function(_){var _hL=E(_hI),_hM=_hL.c,_hN=newArr(_hM,_gG),_hO=_hN,_hP=function(_hQ,_){while(1){if(_hQ!=_hM){var _=_hO[_hQ]=_hL.d[_hQ],_hR=_hQ+1|0;_hQ=_hR;continue;}else{return E(_);}}},_=B(_hP(0,_)),_hS=function(_hT,_){while(1){var _hU=B((function(_hV,_){var _hW=E(_hV);if(!_hW._){return new T4(0,E(_hL.a),E(_hL.b),_hM,_hO);}else{var _hX=E(_hW.a),_hY=E(_hX.a),_hZ=_hO[_hY],_=_hO[_hY]=new T(function(){return B(A2(_hH,_hZ,_hX.b));});_hT=_hW.b;return __continue;}})(_hT,_));if(_hU!=__continue){return _hU;}}};return new F(function(){return _hS(_hJ,_);});};return new F(function(){return _8O(_hK);});},_i0=function(_i1,_i2,_i3,_i4,_i5){var _i6=E(_i4),_i7=B(A2(_9a,_i1,_i6)),_i8=function(_){var _i9=newArr(_i7,_i3),_ia=_i9,_ib=function(_ic,_){while(1){var _id=B((function(_ie,_){var _if=E(_ie);if(!_if._){return new T(function(){return new T4(0,E(_i6.a),E(_i6.b),_i7,_ia);});}else{var _ig=E(_if.a),_ih=E(_ig.a),_ii=_ia[_ih],_=_ia[_ih]=new T(function(){return B(A2(_i2,_ii,_ig.b));});_ic=_if.b;return __continue;}})(_ic,_));if(_id!=__continue){return _id;}}};return new F(function(){return _ib(_i5,_);});};return new F(function(){return _8O(_i8);});},_ij={_:0,a:_hC,b:_hv,c:_ho,d:_h5,e:_gX,f:_hF,g:_i0},_ik=new T(function(){return B(unCStr("Negative range size"));}),_il=new T(function(){return B(err(_ik));}),_im=0,_in=function(_io){var _ip=E(_io);return (E(_ip.b)-E(_ip.a)|0)+1|0;},_iq=function(_ir,_is){var _it=E(_ir),_iu=E(_is);return (E(_it.a)>_iu)?false:_iu<=E(_it.b);},_iv=new T(function(){return B(unCStr("Int"));}),_iw=function(_ix,_iy){return new F(function(){return _eX(_ea,_iy,_ix,_iv);});},_iz=function(_iA,_iB){var _iC=E(_iA),_iD=E(_iC.a),_iE=E(_iB);if(_iD>_iE){return new F(function(){return _iw(_iE,_iC);});}else{if(_iE>E(_iC.b)){return new F(function(){return _iw(_iE,_iC);});}else{return _iE-_iD|0;}}},_iF=function(_iG,_iH){if(_iG<=_iH){var _iI=function(_iJ){return new T2(1,_iJ,new T(function(){if(_iJ!=_iH){return B(_iI(_iJ+1|0));}else{return __Z;}}));};return new F(function(){return _iI(_iG);});}else{return __Z;}},_iK=function(_iL,_iM){return new F(function(){return _iF(E(_iL),E(_iM));});},_iN=function(_iO){var _iP=E(_iO);return new F(function(){return _iK(_iP.a,_iP.b);});},_iQ=function(_iR){var _iS=E(_iR),_iT=E(_iS.a),_iU=E(_iS.b);return (_iT>_iU)?E(_eb):(_iU-_iT|0)+1|0;},_iV=function(_iW,_iX){return E(_iW)-E(_iX)|0;},_iY=function(_iZ,_j0){return new F(function(){return _iV(_j0,E(_iZ).a);});},_j1=function(_j2,_j3){return E(_j2)==E(_j3);},_j4=function(_j5,_j6){return E(_j5)!=E(_j6);},_j7=new T2(0,_j1,_j4),_j8=function(_j9,_ja){var _jb=E(_j9),_jc=E(_ja);return (_jb>_jc)?E(_jb):E(_jc);},_jd=function(_je,_jf){var _jg=E(_je),_jh=E(_jf);return (_jg>_jh)?E(_jh):E(_jg);},_ji=function(_jj,_jk){return (_jj>=_jk)?(_jj!=_jk)?2:1:0;},_jl=function(_jm,_jn){return new F(function(){return _ji(E(_jm),E(_jn));});},_jo=function(_jp,_jq){return E(_jp)>=E(_jq);},_jr=function(_js,_jt){return E(_js)>E(_jt);},_ju=function(_jv,_jw){return E(_jv)<=E(_jw);},_jx=function(_jy,_jz){return E(_jy)<E(_jz);},_jA={_:0,a:_j7,b:_jl,c:_jx,d:_ju,e:_jr,f:_jo,g:_j8,h:_jd},_jB={_:0,a:_jA,b:_iN,c:_iz,d:_iY,e:_iq,f:_iQ,g:_in},_jC=function(_jD,_jE,_jF){var _jG=E(_jD);if(!_jG._){return new T2(0,_4,_jF);}else{var _jH=new T(function(){return B(A2(_jG.a,_jE,_jF));}),_jI=B(_jC(_jG.b,_jE,new T(function(){return E(E(_jH).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_jH).a);}),_jI.a),_jI.b);}},_jJ=function(_jK,_jL,_jM,_jN){if(0>=_jK){return new F(function(){return _jC(_4,_jM,_jN);});}else{var _jO=function(_jP){var _jQ=E(_jP);return (_jQ==1)?E(new T2(1,_jL,_4)):new T2(1,_jL,new T(function(){return B(_jO(_jQ-1|0));}));};return new F(function(){return _jC(B(_jO(_jK)),_jM,_jN);});}},_jR=function(_jS){return E(E(_jS).b);},_jT=function(_jU){return E(E(_jU).c);},_jV=function(_jW,_jX){var _jY=E(_jW);if(!_jY._){return __Z;}else{var _jZ=E(_jX);return (_jZ._==0)?__Z:new T2(1,new T2(0,_jY.a,_jZ.a),new T(function(){return B(_jV(_jY.b,_jZ.b));}));}},_k0=function(_k1,_k2,_k3,_k4,_k5,_k6){var _k7=B(_fo(_k3,_k4,_k5,_k6)),_k8=E(_k7.a)&4294967295,_k9=B(_jJ(_k8,new T(function(){return B(_jR(_k1));}),new T3(0,_k3,_k4,_k5),_k7.b)),_ka=_k9.a,_kb=new T(function(){var _kc=_k8-1|0;return B(A(_jT,[_k2,_jB,new T2(0,_im,_kc),new T(function(){if(0>_kc){return B(_jV(B(_iF(0,-1)),_ka));}else{var _kd=_kc+1|0;if(_kd>=0){return B(_jV(B(_iF(0,_kd-1|0)),_ka));}else{return E(_il);}}})]));});return new T2(0,_kb,_k9.b);},_ke=function(_kf,_kg,_kh,_ki){var _kj=B(_fo(_kf,_kg,_kh,_ki)),_kk=B(_fo(_kf,_kg,_kh,E(_kj.b))),_kl=B(_k0(_gE,_ij,_kf,_kg,_kh,E(_kk.b)));return new T2(0,new T(function(){var _km=E(_kl.a);return new T6(0,E(_kj.a)&4294967295,E(_kk.a)&4294967295,E(_km.a),E(_km.b),_km.c,_km.d);}),_kl.b);},_kn=function(_ko,_kp){var _kq=E(_ko),_kr=B(_ke(_kq.a,_kq.b,_kq.c,E(_kp)));return new T2(0,_kr.a,_kr.b);},_ks=function(_kt){return E(_dP);},_ku=new T2(0,_ks,_kn),_kv=function(_kw,_kx){var _ky=E(_kw),_kz=B(_fo(_ky.a,_ky.b,_ky.c,E(_kx)));return new T2(0,new T(function(){return E(_kz.a)&4294967295;}),_kz.b);},_kA=new T(function(){return B(_dN("Data/Binary.hs:56:10-20|put"));}),_kB=function(_kC){return E(_kA);},_kD=new T2(0,_kB,_kv),_kE=function(_kF,_kG){var _kH=E(_kG);return new T2(0,_kH.a,_kH.b);},_kI=function(_kJ,_kK){return E(_kK).c;},_kL=function(_kM,_kN,_kO,_kP){var _kQ=function(_){var _kR=E(_kO),_kS=_kR.d,_kT=_kS["byteLength"],_kU=newByteArr(_kT),_kV=_kU,_kW=memcpy(_kV,_kS,_kT>>>0),_kX=function(_kY,_){while(1){var _kZ=E(_kY);if(!_kZ._){return _5;}else{var _l0=E(_kZ.a),_l1=E(_l0.a),_l2=_kV["v"]["i32"][_l1],_=_kV["v"]["i32"][_l1]=B(A2(_kN,_l2,_l0.b));_kY=_kZ.b;continue;}}},_l3=B(_kX(_kP,_));return new T4(0,E(_kR.a),E(_kR.b),_kR.c,_kV);};return new F(function(){return _8O(_kQ);});},_l4=function(_l5,_l6,_l7,_l8,_l9){var _la=E(_l8),_lb=function(_){var _lc=B(A2(_9a,_l5,_la)),_ld=newByteArr(imul(4,_lc)|0),_le=_ld;if(_lc>=0){var _lf=_lc-1|0,_lg=function(_){var _lh=function(_li,_){while(1){var _lj=E(_li);if(!_lj._){return _5;}else{var _lk=E(_lj.a),_ll=E(_lk.a),_lm=_le["v"]["i32"][_ll],_=_le["v"]["i32"][_ll]=B(A2(_l6,_lm,_lk.b));_li=_lj.b;continue;}}},_ln=B(_lh(_l9,_));return new T4(0,E(_la.a),E(_la.b),_lc,_le);};if(0<=_lf){var _lo=function(_lp,_){while(1){var _=_le["v"]["i32"][_lp]=E(_l7);if(_lp!=_lf){var _lq=_lp+1|0;_lp=_lq;continue;}else{return _5;}}},_lr=B(_lo(0,_));return new F(function(){return _lg(_);});}else{return new F(function(){return _lg(_);});}}else{return E(_9d);}},_ls=E(_lb);return new F(function(){return _8O(_ls);});},_lt=function(_lu,_lv,_lw){var _lx=E(_lv),_ly=function(_){var _lz=B(A2(_9a,_lu,_lx)),_lA=newByteArr(imul(4,_lz)|0),_lB=_lA;if(_lz>=0){var _lC=_lz-1|0,_lD=function(_){var _lE=function(_lF,_){while(1){var _lG=E(_lF);if(!_lG._){return _5;}else{var _lH=E(_lG.a),_=_lB["v"]["i32"][E(_lH.a)]=E(_lH.b);_lF=_lG.b;continue;}}},_lI=B(_lE(_lw,_));return new T4(0,E(_lx.a),E(_lx.b),_lz,_lB);};if(0<=_lC){var _lJ=function(_lK,_){while(1){var _=_lB["v"]["i32"][_lK]=0;if(_lK!=_lC){var _lL=_lK+1|0;_lK=_lL;continue;}else{return _5;}}},_lM=B(_lJ(0,_));return new F(function(){return _lD(_);});}else{return new F(function(){return _lD(_);});}}else{return E(_9d);}},_lN=E(_ly);return new F(function(){return _8O(_lN);});},_lO=function(_lP,_lQ,_lR){return E(_lQ).d["v"]["i32"][E(_lR)];},_lS=function(_lT,_lU,_lV){var _lW=function(_){var _lX=E(_lU),_lY=_lX.d,_lZ=_lY["byteLength"],_m0=newByteArr(_lZ),_m1=_m0,_m2=memcpy(_m1,_lY,_lZ>>>0),_m3=function(_m4,_){while(1){var _m5=E(_m4);if(!_m5._){return _5;}else{var _m6=E(_m5.a),_=_m1["v"]["i32"][E(_m6.a)]=E(_m6.b);_m4=_m5.b;continue;}}},_m7=B(_m3(_lV,_));return new T4(0,E(_lX.a),E(_lX.b),_lX.c,_m1);};return new F(function(){return _8O(_lW);});},_m8={_:0,a:_kE,b:_kI,c:_lt,d:_lO,e:_lS,f:_kL,g:_l4},_m9=function(_ma,_mb,_mc,_md){var _me=B(_fz(_ma,_mb,_mc,_md)),_mf=B(_k0(_kD,_m8,_ma,_mb,_mc,E(_me.b)));return new T2(0,new T(function(){var _mg=E(_mf.a);return new T5(0,_me.a,E(_mg.a),E(_mg.b),_mg.c,_mg.d);}),_mf.b);},_mh=function(_mi,_mj){var _mk=E(_mi),_ml=B(_m9(_mk.a,_mk.b,_mk.c,E(_mj)));return new T2(0,_ml.a,_ml.b);},_mm=function(_mn){return E(_dP);},_mo=new T2(0,_mm,_mh),_mp=function(_mq){return new F(function(){return _iF(E(_mq),2147483647);});},_mr=function(_ms,_mt,_mu){if(_mu<=_mt){var _mv=new T(function(){var _mw=_mt-_ms|0,_mx=function(_my){return (_my>=(_mu-_mw|0))?new T2(1,_my,new T(function(){return B(_mx(_my+_mw|0));})):new T2(1,_my,_4);};return B(_mx(_mt));});return new T2(1,_ms,_mv);}else{return (_mu<=_ms)?new T2(1,_ms,_4):__Z;}},_mz=function(_mA,_mB,_mC){if(_mC>=_mB){var _mD=new T(function(){var _mE=_mB-_mA|0,_mF=function(_mG){return (_mG<=(_mC-_mE|0))?new T2(1,_mG,new T(function(){return B(_mF(_mG+_mE|0));})):new T2(1,_mG,_4);};return B(_mF(_mB));});return new T2(1,_mA,_mD);}else{return (_mC>=_mA)?new T2(1,_mA,_4):__Z;}},_mH=function(_mI,_mJ){if(_mJ<_mI){return new F(function(){return _mr(_mI,_mJ,-2147483648);});}else{return new F(function(){return _mz(_mI,_mJ,2147483647);});}},_mK=function(_mL,_mM){return new F(function(){return _mH(E(_mL),E(_mM));});},_mN=function(_mO,_mP,_mQ){if(_mP<_mO){return new F(function(){return _mr(_mO,_mP,_mQ);});}else{return new F(function(){return _mz(_mO,_mP,_mQ);});}},_mR=function(_mS,_mT,_mU){return new F(function(){return _mN(E(_mS),E(_mT),E(_mU));});},_mV=function(_mW){return E(_mW);},_mX=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_mY=new T(function(){return B(err(_mX));}),_mZ=function(_n0){var _n1=E(_n0);return (_n1==(-2147483648))?E(_mY):_n1-1|0;},_n2=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_n3=new T(function(){return B(err(_n2));}),_n4=function(_n5){var _n6=E(_n5);return (_n6==2147483647)?E(_n3):_n6+1|0;},_n7={_:0,a:_n4,b:_mZ,c:_mV,d:_mV,e:_mp,f:_mK,g:_iK,h:_mR},_n8=function(_n9,_na){if(_n9<=0){if(_n9>=0){return new F(function(){return quot(_n9,_na);});}else{if(_na<=0){return new F(function(){return quot(_n9,_na);});}else{return quot(_n9+1|0,_na)-1|0;}}}else{if(_na>=0){if(_n9>=0){return new F(function(){return quot(_n9,_na);});}else{if(_na<=0){return new F(function(){return quot(_n9,_na);});}else{return quot(_n9+1|0,_na)-1|0;}}}else{return quot(_n9-1|0,_na)-1|0;}}},_nb=new T(function(){return B(unCStr("base"));}),_nc=new T(function(){return B(unCStr("GHC.Exception"));}),_nd=new T(function(){return B(unCStr("ArithException"));}),_ne=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_nb,_nc,_nd),_nf=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_ne,_4,_4),_ng=function(_nh){return E(_nf);},_ni=function(_nj){var _nk=E(_nj);return new F(function(){return _2M(B(_2K(_nk.a)),_ng,_nk.b);});},_nl=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_nm=new T(function(){return B(unCStr("denormal"));}),_nn=new T(function(){return B(unCStr("divide by zero"));}),_no=new T(function(){return B(unCStr("loss of precision"));}),_np=new T(function(){return B(unCStr("arithmetic underflow"));}),_nq=new T(function(){return B(unCStr("arithmetic overflow"));}),_nr=function(_ns,_nt){switch(E(_ns)){case 0:return new F(function(){return _0(_nq,_nt);});break;case 1:return new F(function(){return _0(_np,_nt);});break;case 2:return new F(function(){return _0(_no,_nt);});break;case 3:return new F(function(){return _0(_nn,_nt);});break;case 4:return new F(function(){return _0(_nm,_nt);});break;default:return new F(function(){return _0(_nl,_nt);});}},_nu=function(_nv){return new F(function(){return _nr(_nv,_4);});},_nw=function(_nx,_ny,_nz){return new F(function(){return _nr(_ny,_nz);});},_nA=function(_nB,_nC){return new F(function(){return _3X(_nr,_nB,_nC);});},_nD=new T3(0,_nw,_nu,_nA),_nE=new T(function(){return new T5(0,_ng,_nD,_nF,_ni,_nu);}),_nF=function(_6S){return new T2(0,_nE,_6S);},_nG=3,_nH=new T(function(){return B(_nF(_nG));}),_nI=new T(function(){return die(_nH);}),_nJ=0,_nK=new T(function(){return B(_nF(_nJ));}),_nL=new T(function(){return die(_nK);}),_nM=function(_nN,_nO){var _nP=E(_nO);switch(_nP){case -1:var _nQ=E(_nN);if(_nQ==(-2147483648)){return E(_nL);}else{return new F(function(){return _n8(_nQ,-1);});}break;case 0:return E(_nI);default:return new F(function(){return _n8(_nN,_nP);});}},_nR=function(_nS,_nT){return new F(function(){return _nM(E(_nS),E(_nT));});},_nU=0,_nV=new T2(0,_nL,_nU),_nW=function(_nX,_nY){var _nZ=E(_nX),_o0=E(_nY);switch(_o0){case -1:var _o1=E(_nZ);if(_o1==(-2147483648)){return E(_nV);}else{if(_o1<=0){if(_o1>=0){var _o2=quotRemI(_o1,-1);return new T2(0,_o2.a,_o2.b);}else{var _o3=quotRemI(_o1,-1);return new T2(0,_o3.a,_o3.b);}}else{var _o4=quotRemI(_o1-1|0,-1);return new T2(0,_o4.a-1|0,(_o4.b+(-1)|0)+1|0);}}break;case 0:return E(_nI);default:if(_nZ<=0){if(_nZ>=0){var _o5=quotRemI(_nZ,_o0);return new T2(0,_o5.a,_o5.b);}else{if(_o0<=0){var _o6=quotRemI(_nZ,_o0);return new T2(0,_o6.a,_o6.b);}else{var _o7=quotRemI(_nZ+1|0,_o0);return new T2(0,_o7.a-1|0,(_o7.b+_o0|0)-1|0);}}}else{if(_o0>=0){if(_nZ>=0){var _o8=quotRemI(_nZ,_o0);return new T2(0,_o8.a,_o8.b);}else{if(_o0<=0){var _o9=quotRemI(_nZ,_o0);return new T2(0,_o9.a,_o9.b);}else{var _oa=quotRemI(_nZ+1|0,_o0);return new T2(0,_oa.a-1|0,(_oa.b+_o0|0)-1|0);}}}else{var _ob=quotRemI(_nZ-1|0,_o0);return new T2(0,_ob.a-1|0,(_ob.b+_o0|0)+1|0);}}}},_oc=function(_od,_oe){var _of=_od%_oe;if(_od<=0){if(_od>=0){return E(_of);}else{if(_oe<=0){return E(_of);}else{var _og=E(_of);return (_og==0)?0:_og+_oe|0;}}}else{if(_oe>=0){if(_od>=0){return E(_of);}else{if(_oe<=0){return E(_of);}else{var _oh=E(_of);return (_oh==0)?0:_oh+_oe|0;}}}else{var _oi=E(_of);return (_oi==0)?0:_oi+_oe|0;}}},_oj=function(_ok,_ol){var _om=E(_ol);switch(_om){case -1:return E(_nU);case 0:return E(_nI);default:return new F(function(){return _oc(E(_ok),_om);});}},_on=function(_oo,_op){var _oq=E(_oo),_or=E(_op);switch(_or){case -1:var _os=E(_oq);if(_os==(-2147483648)){return E(_nL);}else{return new F(function(){return quot(_os,-1);});}break;case 0:return E(_nI);default:return new F(function(){return quot(_oq,_or);});}},_ot=function(_ou,_ov){var _ow=E(_ou),_ox=E(_ov);switch(_ox){case -1:var _oy=E(_ow);if(_oy==(-2147483648)){return E(_nV);}else{var _oz=quotRemI(_oy,-1);return new T2(0,_oz.a,_oz.b);}break;case 0:return E(_nI);default:var _oA=quotRemI(_ow,_ox);return new T2(0,_oA.a,_oA.b);}},_oB=function(_oC,_oD){var _oE=E(_oD);switch(_oE){case -1:return E(_nU);case 0:return E(_nI);default:return E(_oC)%_oE;}},_oF=function(_oG){return new T1(0,_oG);},_oH=function(_oI){return new F(function(){return _oF(E(_oI));});},_oJ=new T1(0,1),_oK=function(_oL){return new T2(0,E(B(_oF(E(_oL)))),E(_oJ));},_oM=function(_oN,_oO){return imul(E(_oN),E(_oO))|0;},_oP=function(_oQ,_oR){return E(_oQ)+E(_oR)|0;},_oS=function(_oT){var _oU=E(_oT);return (_oU<0)? -_oU:E(_oU);},_oV=function(_oW){var _oX=E(_oW);if(!_oX._){return E(_oX.a);}else{return new F(function(){return I_toInt(_oX.a);});}},_oY=function(_oZ){return new F(function(){return _oV(_oZ);});},_p0=function(_p1){return  -E(_p1);},_p2=-1,_p3=0,_p4=1,_p5=function(_p6){var _p7=E(_p6);return (_p7>=0)?(E(_p7)==0)?E(_p3):E(_p4):E(_p2);},_p8={_:0,a:_oP,b:_iV,c:_oM,d:_p0,e:_oS,f:_p5,g:_oY},_p9=new T2(0,_j1,_j4),_pa={_:0,a:_p9,b:_jl,c:_jx,d:_ju,e:_jr,f:_jo,g:_j8,h:_jd},_pb=new T3(0,_p8,_pa,_oK),_pc={_:0,a:_pb,b:_n7,c:_on,d:_oB,e:_nR,f:_oj,g:_ot,h:_nW,i:_oH},_pd={_:0,a:_n4,b:_mZ,c:_mV,d:_mV,e:_mp,f:_mK,g:_iK,h:_mR},_pe={_:0,a:_oP,b:_iV,c:_oM,d:_p0,e:_oS,f:_p5,g:_oY},_pf=new T3(0,_pe,_jA,_oK),_pg={_:0,a:_pf,b:_pd,c:_on,d:_oB,e:_nR,f:_oj,g:_ot,h:_nW,i:_oH},_ph=new T1(0,2),_pi=function(_pj){return E(E(_pj).a);},_pk=function(_pl){return E(E(_pl).a);},_pm=function(_pn,_po){while(1){var _pp=E(_pn);if(!_pp._){var _pq=_pp.a,_pr=E(_po);if(!_pr._){var _ps=_pr.a;if(!(imul(_pq,_ps)|0)){return new T1(0,imul(_pq,_ps)|0);}else{_pn=new T1(1,I_fromInt(_pq));_po=new T1(1,I_fromInt(_ps));continue;}}else{_pn=new T1(1,I_fromInt(_pq));_po=_pr;continue;}}else{var _pt=E(_po);if(!_pt._){_pn=_pp;_po=new T1(1,I_fromInt(_pt.a));continue;}else{return new T1(1,I_mul(_pp.a,_pt.a));}}}},_pu=function(_pv,_pw,_px){while(1){if(!(_pw%2)){var _py=B(_pm(_pv,_pv)),_pz=quot(_pw,2);_pv=_py;_pw=_pz;continue;}else{var _pA=E(_pw);if(_pA==1){return new F(function(){return _pm(_pv,_px);});}else{var _py=B(_pm(_pv,_pv)),_pB=B(_pm(_pv,_px));_pv=_py;_pw=quot(_pA-1|0,2);_px=_pB;continue;}}}},_pC=function(_pD,_pE){while(1){if(!(_pE%2)){var _pF=B(_pm(_pD,_pD)),_pG=quot(_pE,2);_pD=_pF;_pE=_pG;continue;}else{var _pH=E(_pE);if(_pH==1){return E(_pD);}else{return new F(function(){return _pu(B(_pm(_pD,_pD)),quot(_pH-1|0,2),_pD);});}}}},_pI=function(_pJ){return E(E(_pJ).c);},_pK=function(_pL){return E(E(_pL).a);},_pM=function(_pN){return E(E(_pN).b);},_pO=function(_pP){return E(E(_pP).b);},_pQ=function(_pR){return E(E(_pR).c);},_pS=function(_pT){return E(E(_pT).a);},_pU=new T1(0,0),_pV=new T1(0,2),_pW=function(_pX){return E(E(_pX).g);},_pY=function(_pZ){return E(E(_pZ).d);},_q0=function(_q1,_q2){var _q3=B(_pi(_q1)),_q4=new T(function(){return B(_pk(_q3));}),_q5=new T(function(){return B(A3(_pY,_q1,_q2,new T(function(){return B(A2(_pW,_q4,_pV));})));});return new F(function(){return A3(_pS,B(_pK(B(_pM(_q3)))),_q5,new T(function(){return B(A2(_pW,_q4,_pU));}));});},_q6=new T(function(){return B(unCStr("Negative exponent"));}),_q7=new T(function(){return B(err(_q6));}),_q8=function(_q9){return E(E(_q9).c);},_qa=function(_qb,_qc,_qd,_qe){var _qf=B(_pi(_qc)),_qg=new T(function(){return B(_pk(_qf));}),_qh=B(_pM(_qf));if(!B(A3(_pQ,_qh,_qe,new T(function(){return B(A2(_pW,_qg,_pU));})))){if(!B(A3(_pS,B(_pK(_qh)),_qe,new T(function(){return B(A2(_pW,_qg,_pU));})))){var _qi=new T(function(){return B(A2(_pW,_qg,_pV));}),_qj=new T(function(){return B(A2(_pW,_qg,_oJ));}),_qk=B(_pK(_qh)),_ql=function(_qm,_qn,_qo){while(1){var _qp=B((function(_qq,_qr,_qs){if(!B(_q0(_qc,_qr))){if(!B(A3(_pS,_qk,_qr,_qj))){var _qt=new T(function(){return B(A3(_q8,_qc,new T(function(){return B(A3(_pO,_qg,_qr,_qj));}),_qi));});_qm=new T(function(){return B(A3(_pI,_qb,_qq,_qq));});_qn=_qt;_qo=new T(function(){return B(A3(_pI,_qb,_qq,_qs));});return __continue;}else{return new F(function(){return A3(_pI,_qb,_qq,_qs);});}}else{var _qu=_qs;_qm=new T(function(){return B(A3(_pI,_qb,_qq,_qq));});_qn=new T(function(){return B(A3(_q8,_qc,_qr,_qi));});_qo=_qu;return __continue;}})(_qm,_qn,_qo));if(_qp!=__continue){return _qp;}}},_qv=function(_qw,_qx){while(1){var _qy=B((function(_qz,_qA){if(!B(_q0(_qc,_qA))){if(!B(A3(_pS,_qk,_qA,_qj))){var _qB=new T(function(){return B(A3(_q8,_qc,new T(function(){return B(A3(_pO,_qg,_qA,_qj));}),_qi));});return new F(function(){return _ql(new T(function(){return B(A3(_pI,_qb,_qz,_qz));}),_qB,_qz);});}else{return E(_qz);}}else{_qw=new T(function(){return B(A3(_pI,_qb,_qz,_qz));});_qx=new T(function(){return B(A3(_q8,_qc,_qA,_qi));});return __continue;}})(_qw,_qx));if(_qy!=__continue){return _qy;}}};return new F(function(){return _qv(_qd,_qe);});}else{return new F(function(){return A2(_pW,_qb,_oJ);});}}else{return E(_q7);}},_qC=new T(function(){return B(err(_q6));}),_qD=function(_qE){var _qF=I_decodeDouble(_qE);return new T2(0,new T1(1,_qF.b),_qF.a);},_qG=function(_qH,_qI){var _qJ=E(_qH);return (_qJ._==0)?_qJ.a*Math.pow(2,_qI):I_toNumber(_qJ.a)*Math.pow(2,_qI);},_qK=function(_qL,_qM){var _qN=E(_qL);if(!_qN._){var _qO=_qN.a,_qP=E(_qM);return (_qP._==0)?_qO==_qP.a:(I_compareInt(_qP.a,_qO)==0)?true:false;}else{var _qQ=_qN.a,_qR=E(_qM);return (_qR._==0)?(I_compareInt(_qQ,_qR.a)==0)?true:false:(I_compare(_qQ,_qR.a)==0)?true:false;}},_qS=function(_qT,_qU){while(1){var _qV=E(_qT);if(!_qV._){var _qW=E(_qV.a);if(_qW==(-2147483648)){_qT=new T1(1,I_fromInt(-2147483648));continue;}else{var _qX=E(_qU);if(!_qX._){var _qY=_qX.a;return new T2(0,new T1(0,quot(_qW,_qY)),new T1(0,_qW%_qY));}else{_qT=new T1(1,I_fromInt(_qW));_qU=_qX;continue;}}}else{var _qZ=E(_qU);if(!_qZ._){_qT=_qV;_qU=new T1(1,I_fromInt(_qZ.a));continue;}else{var _r0=I_quotRem(_qV.a,_qZ.a);return new T2(0,new T1(1,_r0.a),new T1(1,_r0.b));}}}},_r1=0,_r2=new T1(0,0),_r3=function(_r4,_r5){var _r6=B(_qD(_r5)),_r7=_r6.a,_r8=_r6.b,_r9=new T(function(){return B(_pk(new T(function(){return B(_pi(_r4));})));});if(_r8<0){var _ra= -_r8;if(_ra>=0){var _rb=E(_ra);if(!_rb){var _rc=E(_oJ);}else{var _rc=B(_pC(_ph,_rb));}if(!B(_qK(_rc,_r2))){var _rd=B(_qS(_r7,_rc));return new T2(0,new T(function(){return B(A2(_pW,_r9,_rd.a));}),new T(function(){return B(_qG(_rd.b,_r8));}));}else{return E(_nI);}}else{return E(_qC);}}else{var _re=new T(function(){var _rf=new T(function(){return B(_qa(_r9,_pg,new T(function(){return B(A2(_pW,_r9,_ph));}),_r8));});return B(A3(_pI,_r9,new T(function(){return B(A2(_pW,_r9,_r7));}),_rf));});return new T2(0,_re,_r1);}},_rg=function(_rh){var _ri=E(_rh);if(!_ri._){return _ri.a;}else{return new F(function(){return I_toNumber(_ri.a);});}},_rj=function(_rk,_rl){var _rm=B(_r3(_pc,Math.pow(B(_rg(_rk)),_rl))),_rn=_rm.a;return (E(_rm.b)>=0)?E(_rn):E(_rn)-1|0;},_ro=new T1(0,1),_rp=new T1(0,0),_rq=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_rr=new T(function(){return B(err(_rq));}),_rs=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_rt=new T(function(){return B(err(_rs));}),_ru=new T1(0,2),_rv=new T(function(){return B(unCStr("NaN"));}),_rw=new T(function(){return B(_7f("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_rx=function(_ry,_rz){while(1){var _rA=B((function(_rB,_rC){var _rD=E(_rB);switch(_rD._){case 0:var _rE=E(_rC);if(!_rE._){return __Z;}else{_ry=B(A1(_rD.a,_rE.a));_rz=_rE.b;return __continue;}break;case 1:var _rF=B(A1(_rD.a,_rC)),_rG=_rC;_ry=_rF;_rz=_rG;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_rD.a,_rC),new T(function(){return B(_rx(_rD.b,_rC));}));default:return E(_rD.a);}})(_ry,_rz));if(_rA!=__continue){return _rA;}}},_rH=function(_rI,_rJ){var _rK=function(_rL){var _rM=E(_rJ);if(_rM._==3){return new T2(3,_rM.a,new T(function(){return B(_rH(_rI,_rM.b));}));}else{var _rN=E(_rI);if(_rN._==2){return E(_rM);}else{var _rO=E(_rM);if(_rO._==2){return E(_rN);}else{var _rP=function(_rQ){var _rR=E(_rO);if(_rR._==4){var _rS=function(_rT){return new T1(4,new T(function(){return B(_0(B(_rx(_rN,_rT)),_rR.a));}));};return new T1(1,_rS);}else{var _rU=E(_rN);if(_rU._==1){var _rV=_rU.a,_rW=E(_rR);if(!_rW._){return new T1(1,function(_rX){return new F(function(){return _rH(B(A1(_rV,_rX)),_rW);});});}else{var _rY=function(_rZ){return new F(function(){return _rH(B(A1(_rV,_rZ)),new T(function(){return B(A1(_rW.a,_rZ));}));});};return new T1(1,_rY);}}else{var _s0=E(_rR);if(!_s0._){return E(_rw);}else{var _s1=function(_s2){return new F(function(){return _rH(_rU,new T(function(){return B(A1(_s0.a,_s2));}));});};return new T1(1,_s1);}}}},_s3=E(_rN);switch(_s3._){case 1:var _s4=E(_rO);if(_s4._==4){var _s5=function(_s6){return new T1(4,new T(function(){return B(_0(B(_rx(B(A1(_s3.a,_s6)),_s6)),_s4.a));}));};return new T1(1,_s5);}else{return new F(function(){return _rP(_);});}break;case 4:var _s7=_s3.a,_s8=E(_rO);switch(_s8._){case 0:var _s9=function(_sa){var _sb=new T(function(){return B(_0(_s7,new T(function(){return B(_rx(_s8,_sa));},1)));});return new T1(4,_sb);};return new T1(1,_s9);case 1:var _sc=function(_sd){var _se=new T(function(){return B(_0(_s7,new T(function(){return B(_rx(B(A1(_s8.a,_sd)),_sd));},1)));});return new T1(4,_se);};return new T1(1,_sc);default:return new T1(4,new T(function(){return B(_0(_s7,_s8.a));}));}break;default:return new F(function(){return _rP(_);});}}}}},_sf=E(_rI);switch(_sf._){case 0:var _sg=E(_rJ);if(!_sg._){var _sh=function(_si){return new F(function(){return _rH(B(A1(_sf.a,_si)),new T(function(){return B(A1(_sg.a,_si));}));});};return new T1(0,_sh);}else{return new F(function(){return _rK(_);});}break;case 3:return new T2(3,_sf.a,new T(function(){return B(_rH(_sf.b,_rJ));}));default:return new F(function(){return _rK(_);});}},_sj=new T(function(){return B(unCStr("("));}),_sk=new T(function(){return B(unCStr(")"));}),_sl=function(_sm,_sn){while(1){var _so=E(_sm);if(!_so._){return (E(_sn)._==0)?true:false;}else{var _sp=E(_sn);if(!_sp._){return false;}else{if(E(_so.a)!=E(_sp.a)){return false;}else{_sm=_so.b;_sn=_sp.b;continue;}}}}},_sq=function(_sr,_ss){return E(_sr)!=E(_ss);},_st=function(_su,_sv){return E(_su)==E(_sv);},_sw=new T2(0,_st,_sq),_sx=function(_sy,_sz){while(1){var _sA=E(_sy);if(!_sA._){return (E(_sz)._==0)?true:false;}else{var _sB=E(_sz);if(!_sB._){return false;}else{if(E(_sA.a)!=E(_sB.a)){return false;}else{_sy=_sA.b;_sz=_sB.b;continue;}}}}},_sC=function(_sD,_sE){return (!B(_sx(_sD,_sE)))?true:false;},_sF=new T2(0,_sx,_sC),_sG=function(_sH,_sI){var _sJ=E(_sH);switch(_sJ._){case 0:return new T1(0,function(_sK){return new F(function(){return _sG(B(A1(_sJ.a,_sK)),_sI);});});case 1:return new T1(1,function(_sL){return new F(function(){return _sG(B(A1(_sJ.a,_sL)),_sI);});});case 2:return new T0(2);case 3:return new F(function(){return _rH(B(A1(_sI,_sJ.a)),new T(function(){return B(_sG(_sJ.b,_sI));}));});break;default:var _sM=function(_sN){var _sO=E(_sN);if(!_sO._){return __Z;}else{var _sP=E(_sO.a);return new F(function(){return _0(B(_rx(B(A1(_sI,_sP.a)),_sP.b)),new T(function(){return B(_sM(_sO.b));},1));});}},_sQ=B(_sM(_sJ.a));return (_sQ._==0)?new T0(2):new T1(4,_sQ);}},_sR=new T0(2),_sS=function(_sT){return new T2(3,_sT,_sR);},_sU=function(_sV,_sW){var _sX=E(_sV);if(!_sX){return new F(function(){return A1(_sW,_5);});}else{var _sY=new T(function(){return B(_sU(_sX-1|0,_sW));});return new T1(0,function(_sZ){return E(_sY);});}},_t0=function(_t1,_t2,_t3){var _t4=new T(function(){return B(A1(_t1,_sS));}),_t5=function(_t6,_t7,_t8,_t9){while(1){var _ta=B((function(_tb,_tc,_td,_te){var _tf=E(_tb);switch(_tf._){case 0:var _tg=E(_tc);if(!_tg._){return new F(function(){return A1(_t2,_te);});}else{var _th=_td+1|0,_ti=_te;_t6=B(A1(_tf.a,_tg.a));_t7=_tg.b;_t8=_th;_t9=_ti;return __continue;}break;case 1:var _tj=B(A1(_tf.a,_tc)),_tk=_tc,_th=_td,_ti=_te;_t6=_tj;_t7=_tk;_t8=_th;_t9=_ti;return __continue;case 2:return new F(function(){return A1(_t2,_te);});break;case 3:var _tl=new T(function(){return B(_sG(_tf,_te));});return new F(function(){return _sU(_td,function(_tm){return E(_tl);});});break;default:return new F(function(){return _sG(_tf,_te);});}})(_t6,_t7,_t8,_t9));if(_ta!=__continue){return _ta;}}};return function(_tn){return new F(function(){return _t5(_t4,_tn,0,_t3);});};},_to=function(_tp){return new F(function(){return A1(_tp,_4);});},_tq=function(_tr,_ts){var _tt=function(_tu){var _tv=E(_tu);if(!_tv._){return E(_to);}else{var _tw=_tv.a;if(!B(A1(_tr,_tw))){return E(_to);}else{var _tx=new T(function(){return B(_tt(_tv.b));}),_ty=function(_tz){var _tA=new T(function(){return B(A1(_tx,function(_tB){return new F(function(){return A1(_tz,new T2(1,_tw,_tB));});}));});return new T1(0,function(_tC){return E(_tA);});};return E(_ty);}}};return function(_tD){return new F(function(){return A2(_tt,_tD,_ts);});};},_tE=new T0(6),_tF=new T(function(){return B(unCStr("valDig: Bad base"));}),_tG=new T(function(){return B(err(_tF));}),_tH=function(_tI,_tJ){var _tK=function(_tL,_tM){var _tN=E(_tL);if(!_tN._){var _tO=new T(function(){return B(A1(_tM,_4));});return function(_tP){return new F(function(){return A1(_tP,_tO);});};}else{var _tQ=E(_tN.a),_tR=function(_tS){var _tT=new T(function(){return B(_tK(_tN.b,function(_tU){return new F(function(){return A1(_tM,new T2(1,_tS,_tU));});}));}),_tV=function(_tW){var _tX=new T(function(){return B(A1(_tT,_tW));});return new T1(0,function(_tY){return E(_tX);});};return E(_tV);};switch(E(_tI)){case 8:if(48>_tQ){var _tZ=new T(function(){return B(A1(_tM,_4));});return function(_u0){return new F(function(){return A1(_u0,_tZ);});};}else{if(_tQ>55){var _u1=new T(function(){return B(A1(_tM,_4));});return function(_u2){return new F(function(){return A1(_u2,_u1);});};}else{return new F(function(){return _tR(_tQ-48|0);});}}break;case 10:if(48>_tQ){var _u3=new T(function(){return B(A1(_tM,_4));});return function(_u4){return new F(function(){return A1(_u4,_u3);});};}else{if(_tQ>57){var _u5=new T(function(){return B(A1(_tM,_4));});return function(_u6){return new F(function(){return A1(_u6,_u5);});};}else{return new F(function(){return _tR(_tQ-48|0);});}}break;case 16:if(48>_tQ){if(97>_tQ){if(65>_tQ){var _u7=new T(function(){return B(A1(_tM,_4));});return function(_u8){return new F(function(){return A1(_u8,_u7);});};}else{if(_tQ>70){var _u9=new T(function(){return B(A1(_tM,_4));});return function(_ua){return new F(function(){return A1(_ua,_u9);});};}else{return new F(function(){return _tR((_tQ-65|0)+10|0);});}}}else{if(_tQ>102){if(65>_tQ){var _ub=new T(function(){return B(A1(_tM,_4));});return function(_uc){return new F(function(){return A1(_uc,_ub);});};}else{if(_tQ>70){var _ud=new T(function(){return B(A1(_tM,_4));});return function(_ue){return new F(function(){return A1(_ue,_ud);});};}else{return new F(function(){return _tR((_tQ-65|0)+10|0);});}}}else{return new F(function(){return _tR((_tQ-97|0)+10|0);});}}}else{if(_tQ>57){if(97>_tQ){if(65>_tQ){var _uf=new T(function(){return B(A1(_tM,_4));});return function(_ug){return new F(function(){return A1(_ug,_uf);});};}else{if(_tQ>70){var _uh=new T(function(){return B(A1(_tM,_4));});return function(_ui){return new F(function(){return A1(_ui,_uh);});};}else{return new F(function(){return _tR((_tQ-65|0)+10|0);});}}}else{if(_tQ>102){if(65>_tQ){var _uj=new T(function(){return B(A1(_tM,_4));});return function(_uk){return new F(function(){return A1(_uk,_uj);});};}else{if(_tQ>70){var _ul=new T(function(){return B(A1(_tM,_4));});return function(_um){return new F(function(){return A1(_um,_ul);});};}else{return new F(function(){return _tR((_tQ-65|0)+10|0);});}}}else{return new F(function(){return _tR((_tQ-97|0)+10|0);});}}}else{return new F(function(){return _tR(_tQ-48|0);});}}break;default:return E(_tG);}}},_un=function(_uo){var _up=E(_uo);if(!_up._){return new T0(2);}else{return new F(function(){return A1(_tJ,_up);});}};return function(_uq){return new F(function(){return A3(_tK,_uq,_2j,_un);});};},_ur=16,_us=8,_ut=function(_uu){var _uv=function(_uw){return new F(function(){return A1(_uu,new T1(5,new T2(0,_us,_uw)));});},_ux=function(_uy){return new F(function(){return A1(_uu,new T1(5,new T2(0,_ur,_uy)));});},_uz=function(_uA){switch(E(_uA)){case 79:return new T1(1,B(_tH(_us,_uv)));case 88:return new T1(1,B(_tH(_ur,_ux)));case 111:return new T1(1,B(_tH(_us,_uv)));case 120:return new T1(1,B(_tH(_ur,_ux)));default:return new T0(2);}};return function(_uB){return (E(_uB)==48)?E(new T1(0,_uz)):new T0(2);};},_uC=function(_uD){return new T1(0,B(_ut(_uD)));},_uE=function(_uF){return new F(function(){return A1(_uF,_4l);});},_uG=function(_uH){return new F(function(){return A1(_uH,_4l);});},_uI=10,_uJ=new T1(0,1),_uK=new T1(0,2147483647),_uL=function(_uM,_uN){while(1){var _uO=E(_uM);if(!_uO._){var _uP=_uO.a,_uQ=E(_uN);if(!_uQ._){var _uR=_uQ.a,_uS=addC(_uP,_uR);if(!E(_uS.b)){return new T1(0,_uS.a);}else{_uM=new T1(1,I_fromInt(_uP));_uN=new T1(1,I_fromInt(_uR));continue;}}else{_uM=new T1(1,I_fromInt(_uP));_uN=_uQ;continue;}}else{var _uT=E(_uN);if(!_uT._){_uM=_uO;_uN=new T1(1,I_fromInt(_uT.a));continue;}else{return new T1(1,I_add(_uO.a,_uT.a));}}}},_uU=new T(function(){return B(_uL(_uK,_uJ));}),_uV=function(_uW){var _uX=E(_uW);if(!_uX._){var _uY=E(_uX.a);return (_uY==(-2147483648))?E(_uU):new T1(0, -_uY);}else{return new T1(1,I_negate(_uX.a));}},_uZ=new T1(0,10),_v0=function(_v1,_v2){while(1){var _v3=E(_v1);if(!_v3._){return E(_v2);}else{var _v4=_v2+1|0;_v1=_v3.b;_v2=_v4;continue;}}},_v5=function(_v6){return new F(function(){return _oF(E(_v6));});},_v7=new T(function(){return B(unCStr("this should not happen"));}),_v8=new T(function(){return B(err(_v7));}),_v9=function(_va,_vb){var _vc=E(_vb);if(!_vc._){return __Z;}else{var _vd=E(_vc.b);return (_vd._==0)?E(_v8):new T2(1,B(_uL(B(_pm(_vc.a,_va)),_vd.a)),new T(function(){return B(_v9(_va,_vd.b));}));}},_ve=new T1(0,0),_vf=function(_vg,_vh,_vi){while(1){var _vj=B((function(_vk,_vl,_vm){var _vn=E(_vm);if(!_vn._){return E(_ve);}else{if(!E(_vn.b)._){return E(_vn.a);}else{var _vo=E(_vl);if(_vo<=40){var _vp=function(_vq,_vr){while(1){var _vs=E(_vr);if(!_vs._){return E(_vq);}else{var _vt=B(_uL(B(_pm(_vq,_vk)),_vs.a));_vq=_vt;_vr=_vs.b;continue;}}};return new F(function(){return _vp(_ve,_vn);});}else{var _vu=B(_pm(_vk,_vk));if(!(_vo%2)){var _vv=B(_v9(_vk,_vn));_vg=_vu;_vh=quot(_vo+1|0,2);_vi=_vv;return __continue;}else{var _vv=B(_v9(_vk,new T2(1,_ve,_vn)));_vg=_vu;_vh=quot(_vo+1|0,2);_vi=_vv;return __continue;}}}}})(_vg,_vh,_vi));if(_vj!=__continue){return _vj;}}},_vw=function(_vx,_vy){return new F(function(){return _vf(_vx,new T(function(){return B(_v0(_vy,0));},1),B(_G(_v5,_vy)));});},_vz=function(_vA){var _vB=new T(function(){var _vC=new T(function(){var _vD=function(_vE){return new F(function(){return A1(_vA,new T1(1,new T(function(){return B(_vw(_uZ,_vE));})));});};return new T1(1,B(_tH(_uI,_vD)));}),_vF=function(_vG){if(E(_vG)==43){var _vH=function(_vI){return new F(function(){return A1(_vA,new T1(1,new T(function(){return B(_vw(_uZ,_vI));})));});};return new T1(1,B(_tH(_uI,_vH)));}else{return new T0(2);}},_vJ=function(_vK){if(E(_vK)==45){var _vL=function(_vM){return new F(function(){return A1(_vA,new T1(1,new T(function(){return B(_uV(B(_vw(_uZ,_vM))));})));});};return new T1(1,B(_tH(_uI,_vL)));}else{return new T0(2);}};return B(_rH(B(_rH(new T1(0,_vJ),new T1(0,_vF))),_vC));});return new F(function(){return _rH(new T1(0,function(_vN){return (E(_vN)==101)?E(_vB):new T0(2);}),new T1(0,function(_vO){return (E(_vO)==69)?E(_vB):new T0(2);}));});},_vP=function(_vQ){var _vR=function(_vS){return new F(function(){return A1(_vQ,new T1(1,_vS));});};return function(_vT){return (E(_vT)==46)?new T1(1,B(_tH(_uI,_vR))):new T0(2);};},_vU=function(_vV){return new T1(0,B(_vP(_vV)));},_vW=function(_vX){var _vY=function(_vZ){var _w0=function(_w1){return new T1(1,B(_t0(_vz,_uE,function(_w2){return new F(function(){return A1(_vX,new T1(5,new T3(1,_vZ,_w1,_w2)));});})));};return new T1(1,B(_t0(_vU,_uG,_w0)));};return new F(function(){return _tH(_uI,_vY);});},_w3=function(_w4){return new T1(1,B(_vW(_w4)));},_w5=function(_w6,_w7,_w8){while(1){var _w9=E(_w8);if(!_w9._){return false;}else{if(!B(A3(_pS,_w6,_w7,_w9.a))){_w8=_w9.b;continue;}else{return true;}}}},_wa=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_wb=function(_wc){return new F(function(){return _w5(_sw,_wc,_wa);});},_wd=false,_we=true,_wf=function(_wg){var _wh=new T(function(){return B(A1(_wg,_us));}),_wi=new T(function(){return B(A1(_wg,_ur));});return function(_wj){switch(E(_wj)){case 79:return E(_wh);case 88:return E(_wi);case 111:return E(_wh);case 120:return E(_wi);default:return new T0(2);}};},_wk=function(_wl){return new T1(0,B(_wf(_wl)));},_wm=function(_wn){return new F(function(){return A1(_wn,_uI);});},_wo=function(_wp,_wq){var _wr=E(_wp);if(!_wr._){var _ws=_wr.a,_wt=E(_wq);return (_wt._==0)?_ws<=_wt.a:I_compareInt(_wt.a,_ws)>=0;}else{var _wu=_wr.a,_wv=E(_wq);return (_wv._==0)?I_compareInt(_wu,_wv.a)<=0:I_compare(_wu,_wv.a)<=0;}},_ww=function(_wx){return new T0(2);},_wy=function(_wz){var _wA=E(_wz);if(!_wA._){return E(_ww);}else{var _wB=_wA.a,_wC=E(_wA.b);if(!_wC._){return E(_wB);}else{var _wD=new T(function(){return B(_wy(_wC));}),_wE=function(_wF){return new F(function(){return _rH(B(A1(_wB,_wF)),new T(function(){return B(A1(_wD,_wF));}));});};return E(_wE);}}},_wG=function(_wH,_wI){var _wJ=function(_wK,_wL,_wM){var _wN=E(_wK);if(!_wN._){return new F(function(){return A1(_wM,_wH);});}else{var _wO=E(_wL);if(!_wO._){return new T0(2);}else{if(E(_wN.a)!=E(_wO.a)){return new T0(2);}else{var _wP=new T(function(){return B(_wJ(_wN.b,_wO.b,_wM));});return new T1(0,function(_wQ){return E(_wP);});}}}};return function(_wR){return new F(function(){return _wJ(_wH,_wR,_wI);});};},_wS=new T(function(){return B(unCStr("SO"));}),_wT=14,_wU=function(_wV){var _wW=new T(function(){return B(A1(_wV,_wT));});return new T1(1,B(_wG(_wS,function(_wX){return E(_wW);})));},_wY=new T(function(){return B(unCStr("SOH"));}),_wZ=1,_x0=function(_x1){var _x2=new T(function(){return B(A1(_x1,_wZ));});return new T1(1,B(_wG(_wY,function(_x3){return E(_x2);})));},_x4=function(_x5){return new T1(1,B(_t0(_x0,_wU,_x5)));},_x6=new T(function(){return B(unCStr("NUL"));}),_x7=0,_x8=function(_x9){var _xa=new T(function(){return B(A1(_x9,_x7));});return new T1(1,B(_wG(_x6,function(_xb){return E(_xa);})));},_xc=new T(function(){return B(unCStr("STX"));}),_xd=2,_xe=function(_xf){var _xg=new T(function(){return B(A1(_xf,_xd));});return new T1(1,B(_wG(_xc,function(_xh){return E(_xg);})));},_xi=new T(function(){return B(unCStr("ETX"));}),_xj=3,_xk=function(_xl){var _xm=new T(function(){return B(A1(_xl,_xj));});return new T1(1,B(_wG(_xi,function(_xn){return E(_xm);})));},_xo=new T(function(){return B(unCStr("EOT"));}),_xp=4,_xq=function(_xr){var _xs=new T(function(){return B(A1(_xr,_xp));});return new T1(1,B(_wG(_xo,function(_xt){return E(_xs);})));},_xu=new T(function(){return B(unCStr("ENQ"));}),_xv=5,_xw=function(_xx){var _xy=new T(function(){return B(A1(_xx,_xv));});return new T1(1,B(_wG(_xu,function(_xz){return E(_xy);})));},_xA=new T(function(){return B(unCStr("ACK"));}),_xB=6,_xC=function(_xD){var _xE=new T(function(){return B(A1(_xD,_xB));});return new T1(1,B(_wG(_xA,function(_xF){return E(_xE);})));},_xG=new T(function(){return B(unCStr("BEL"));}),_xH=7,_xI=function(_xJ){var _xK=new T(function(){return B(A1(_xJ,_xH));});return new T1(1,B(_wG(_xG,function(_xL){return E(_xK);})));},_xM=new T(function(){return B(unCStr("BS"));}),_xN=8,_xO=function(_xP){var _xQ=new T(function(){return B(A1(_xP,_xN));});return new T1(1,B(_wG(_xM,function(_xR){return E(_xQ);})));},_xS=new T(function(){return B(unCStr("HT"));}),_xT=9,_xU=function(_xV){var _xW=new T(function(){return B(A1(_xV,_xT));});return new T1(1,B(_wG(_xS,function(_xX){return E(_xW);})));},_xY=new T(function(){return B(unCStr("LF"));}),_xZ=10,_y0=function(_y1){var _y2=new T(function(){return B(A1(_y1,_xZ));});return new T1(1,B(_wG(_xY,function(_y3){return E(_y2);})));},_y4=new T(function(){return B(unCStr("VT"));}),_y5=11,_y6=function(_y7){var _y8=new T(function(){return B(A1(_y7,_y5));});return new T1(1,B(_wG(_y4,function(_y9){return E(_y8);})));},_ya=new T(function(){return B(unCStr("FF"));}),_yb=12,_yc=function(_yd){var _ye=new T(function(){return B(A1(_yd,_yb));});return new T1(1,B(_wG(_ya,function(_yf){return E(_ye);})));},_yg=new T(function(){return B(unCStr("CR"));}),_yh=13,_yi=function(_yj){var _yk=new T(function(){return B(A1(_yj,_yh));});return new T1(1,B(_wG(_yg,function(_yl){return E(_yk);})));},_ym=new T(function(){return B(unCStr("SI"));}),_yn=15,_yo=function(_yp){var _yq=new T(function(){return B(A1(_yp,_yn));});return new T1(1,B(_wG(_ym,function(_yr){return E(_yq);})));},_ys=new T(function(){return B(unCStr("DLE"));}),_yt=16,_yu=function(_yv){var _yw=new T(function(){return B(A1(_yv,_yt));});return new T1(1,B(_wG(_ys,function(_yx){return E(_yw);})));},_yy=new T(function(){return B(unCStr("DC1"));}),_yz=17,_yA=function(_yB){var _yC=new T(function(){return B(A1(_yB,_yz));});return new T1(1,B(_wG(_yy,function(_yD){return E(_yC);})));},_yE=new T(function(){return B(unCStr("DC2"));}),_yF=18,_yG=function(_yH){var _yI=new T(function(){return B(A1(_yH,_yF));});return new T1(1,B(_wG(_yE,function(_yJ){return E(_yI);})));},_yK=new T(function(){return B(unCStr("DC3"));}),_yL=19,_yM=function(_yN){var _yO=new T(function(){return B(A1(_yN,_yL));});return new T1(1,B(_wG(_yK,function(_yP){return E(_yO);})));},_yQ=new T(function(){return B(unCStr("DC4"));}),_yR=20,_yS=function(_yT){var _yU=new T(function(){return B(A1(_yT,_yR));});return new T1(1,B(_wG(_yQ,function(_yV){return E(_yU);})));},_yW=new T(function(){return B(unCStr("NAK"));}),_yX=21,_yY=function(_yZ){var _z0=new T(function(){return B(A1(_yZ,_yX));});return new T1(1,B(_wG(_yW,function(_z1){return E(_z0);})));},_z2=new T(function(){return B(unCStr("SYN"));}),_z3=22,_z4=function(_z5){var _z6=new T(function(){return B(A1(_z5,_z3));});return new T1(1,B(_wG(_z2,function(_z7){return E(_z6);})));},_z8=new T(function(){return B(unCStr("ETB"));}),_z9=23,_za=function(_zb){var _zc=new T(function(){return B(A1(_zb,_z9));});return new T1(1,B(_wG(_z8,function(_zd){return E(_zc);})));},_ze=new T(function(){return B(unCStr("CAN"));}),_zf=24,_zg=function(_zh){var _zi=new T(function(){return B(A1(_zh,_zf));});return new T1(1,B(_wG(_ze,function(_zj){return E(_zi);})));},_zk=new T(function(){return B(unCStr("EM"));}),_zl=25,_zm=function(_zn){var _zo=new T(function(){return B(A1(_zn,_zl));});return new T1(1,B(_wG(_zk,function(_zp){return E(_zo);})));},_zq=new T(function(){return B(unCStr("SUB"));}),_zr=26,_zs=function(_zt){var _zu=new T(function(){return B(A1(_zt,_zr));});return new T1(1,B(_wG(_zq,function(_zv){return E(_zu);})));},_zw=new T(function(){return B(unCStr("ESC"));}),_zx=27,_zy=function(_zz){var _zA=new T(function(){return B(A1(_zz,_zx));});return new T1(1,B(_wG(_zw,function(_zB){return E(_zA);})));},_zC=new T(function(){return B(unCStr("FS"));}),_zD=28,_zE=function(_zF){var _zG=new T(function(){return B(A1(_zF,_zD));});return new T1(1,B(_wG(_zC,function(_zH){return E(_zG);})));},_zI=new T(function(){return B(unCStr("GS"));}),_zJ=29,_zK=function(_zL){var _zM=new T(function(){return B(A1(_zL,_zJ));});return new T1(1,B(_wG(_zI,function(_zN){return E(_zM);})));},_zO=new T(function(){return B(unCStr("RS"));}),_zP=30,_zQ=function(_zR){var _zS=new T(function(){return B(A1(_zR,_zP));});return new T1(1,B(_wG(_zO,function(_zT){return E(_zS);})));},_zU=new T(function(){return B(unCStr("US"));}),_zV=31,_zW=function(_zX){var _zY=new T(function(){return B(A1(_zX,_zV));});return new T1(1,B(_wG(_zU,function(_zZ){return E(_zY);})));},_A0=new T(function(){return B(unCStr("SP"));}),_A1=32,_A2=function(_A3){var _A4=new T(function(){return B(A1(_A3,_A1));});return new T1(1,B(_wG(_A0,function(_A5){return E(_A4);})));},_A6=new T(function(){return B(unCStr("DEL"));}),_A7=127,_A8=function(_A9){var _Aa=new T(function(){return B(A1(_A9,_A7));});return new T1(1,B(_wG(_A6,function(_Ab){return E(_Aa);})));},_Ac=new T2(1,_A8,_4),_Ad=new T2(1,_A2,_Ac),_Ae=new T2(1,_zW,_Ad),_Af=new T2(1,_zQ,_Ae),_Ag=new T2(1,_zK,_Af),_Ah=new T2(1,_zE,_Ag),_Ai=new T2(1,_zy,_Ah),_Aj=new T2(1,_zs,_Ai),_Ak=new T2(1,_zm,_Aj),_Al=new T2(1,_zg,_Ak),_Am=new T2(1,_za,_Al),_An=new T2(1,_z4,_Am),_Ao=new T2(1,_yY,_An),_Ap=new T2(1,_yS,_Ao),_Aq=new T2(1,_yM,_Ap),_Ar=new T2(1,_yG,_Aq),_As=new T2(1,_yA,_Ar),_At=new T2(1,_yu,_As),_Au=new T2(1,_yo,_At),_Av=new T2(1,_yi,_Au),_Aw=new T2(1,_yc,_Av),_Ax=new T2(1,_y6,_Aw),_Ay=new T2(1,_y0,_Ax),_Az=new T2(1,_xU,_Ay),_AA=new T2(1,_xO,_Az),_AB=new T2(1,_xI,_AA),_AC=new T2(1,_xC,_AB),_AD=new T2(1,_xw,_AC),_AE=new T2(1,_xq,_AD),_AF=new T2(1,_xk,_AE),_AG=new T2(1,_xe,_AF),_AH=new T2(1,_x8,_AG),_AI=new T2(1,_x4,_AH),_AJ=new T(function(){return B(_wy(_AI));}),_AK=34,_AL=new T1(0,1114111),_AM=92,_AN=39,_AO=function(_AP){var _AQ=new T(function(){return B(A1(_AP,_xH));}),_AR=new T(function(){return B(A1(_AP,_xN));}),_AS=new T(function(){return B(A1(_AP,_xT));}),_AT=new T(function(){return B(A1(_AP,_xZ));}),_AU=new T(function(){return B(A1(_AP,_y5));}),_AV=new T(function(){return B(A1(_AP,_yb));}),_AW=new T(function(){return B(A1(_AP,_yh));}),_AX=new T(function(){return B(A1(_AP,_AM));}),_AY=new T(function(){return B(A1(_AP,_AN));}),_AZ=new T(function(){return B(A1(_AP,_AK));}),_B0=new T(function(){var _B1=function(_B2){var _B3=new T(function(){return B(_oF(E(_B2)));}),_B4=function(_B5){var _B6=B(_vw(_B3,_B5));if(!B(_wo(_B6,_AL))){return new T0(2);}else{return new F(function(){return A1(_AP,new T(function(){var _B7=B(_oV(_B6));if(_B7>>>0>1114111){return B(_fQ(_B7));}else{return _B7;}}));});}};return new T1(1,B(_tH(_B2,_B4)));},_B8=new T(function(){var _B9=new T(function(){return B(A1(_AP,_zV));}),_Ba=new T(function(){return B(A1(_AP,_zP));}),_Bb=new T(function(){return B(A1(_AP,_zJ));}),_Bc=new T(function(){return B(A1(_AP,_zD));}),_Bd=new T(function(){return B(A1(_AP,_zx));}),_Be=new T(function(){return B(A1(_AP,_zr));}),_Bf=new T(function(){return B(A1(_AP,_zl));}),_Bg=new T(function(){return B(A1(_AP,_zf));}),_Bh=new T(function(){return B(A1(_AP,_z9));}),_Bi=new T(function(){return B(A1(_AP,_z3));}),_Bj=new T(function(){return B(A1(_AP,_yX));}),_Bk=new T(function(){return B(A1(_AP,_yR));}),_Bl=new T(function(){return B(A1(_AP,_yL));}),_Bm=new T(function(){return B(A1(_AP,_yF));}),_Bn=new T(function(){return B(A1(_AP,_yz));}),_Bo=new T(function(){return B(A1(_AP,_yt));}),_Bp=new T(function(){return B(A1(_AP,_yn));}),_Bq=new T(function(){return B(A1(_AP,_wT));}),_Br=new T(function(){return B(A1(_AP,_xB));}),_Bs=new T(function(){return B(A1(_AP,_xv));}),_Bt=new T(function(){return B(A1(_AP,_xp));}),_Bu=new T(function(){return B(A1(_AP,_xj));}),_Bv=new T(function(){return B(A1(_AP,_xd));}),_Bw=new T(function(){return B(A1(_AP,_wZ));}),_Bx=new T(function(){return B(A1(_AP,_x7));}),_By=function(_Bz){switch(E(_Bz)){case 64:return E(_Bx);case 65:return E(_Bw);case 66:return E(_Bv);case 67:return E(_Bu);case 68:return E(_Bt);case 69:return E(_Bs);case 70:return E(_Br);case 71:return E(_AQ);case 72:return E(_AR);case 73:return E(_AS);case 74:return E(_AT);case 75:return E(_AU);case 76:return E(_AV);case 77:return E(_AW);case 78:return E(_Bq);case 79:return E(_Bp);case 80:return E(_Bo);case 81:return E(_Bn);case 82:return E(_Bm);case 83:return E(_Bl);case 84:return E(_Bk);case 85:return E(_Bj);case 86:return E(_Bi);case 87:return E(_Bh);case 88:return E(_Bg);case 89:return E(_Bf);case 90:return E(_Be);case 91:return E(_Bd);case 92:return E(_Bc);case 93:return E(_Bb);case 94:return E(_Ba);case 95:return E(_B9);default:return new T0(2);}};return B(_rH(new T1(0,function(_BA){return (E(_BA)==94)?E(new T1(0,_By)):new T0(2);}),new T(function(){return B(A1(_AJ,_AP));})));});return B(_rH(new T1(1,B(_t0(_wk,_wm,_B1))),_B8));});return new F(function(){return _rH(new T1(0,function(_BB){switch(E(_BB)){case 34:return E(_AZ);case 39:return E(_AY);case 92:return E(_AX);case 97:return E(_AQ);case 98:return E(_AR);case 102:return E(_AV);case 110:return E(_AT);case 114:return E(_AW);case 116:return E(_AS);case 118:return E(_AU);default:return new T0(2);}}),_B0);});},_BC=function(_BD){return new F(function(){return A1(_BD,_5);});},_BE=function(_BF){var _BG=E(_BF);if(!_BG._){return E(_BC);}else{var _BH=E(_BG.a),_BI=_BH>>>0,_BJ=new T(function(){return B(_BE(_BG.b));});if(_BI>887){var _BK=u_iswspace(_BH);if(!E(_BK)){return E(_BC);}else{var _BL=function(_BM){var _BN=new T(function(){return B(A1(_BJ,_BM));});return new T1(0,function(_BO){return E(_BN);});};return E(_BL);}}else{var _BP=E(_BI);if(_BP==32){var _BQ=function(_BR){var _BS=new T(function(){return B(A1(_BJ,_BR));});return new T1(0,function(_BT){return E(_BS);});};return E(_BQ);}else{if(_BP-9>>>0>4){if(E(_BP)==160){var _BU=function(_BV){var _BW=new T(function(){return B(A1(_BJ,_BV));});return new T1(0,function(_BX){return E(_BW);});};return E(_BU);}else{return E(_BC);}}else{var _BY=function(_BZ){var _C0=new T(function(){return B(A1(_BJ,_BZ));});return new T1(0,function(_C1){return E(_C0);});};return E(_BY);}}}}},_C2=function(_C3){var _C4=new T(function(){return B(_C2(_C3));}),_C5=function(_C6){return (E(_C6)==92)?E(_C4):new T0(2);},_C7=function(_C8){return E(new T1(0,_C5));},_C9=new T1(1,function(_Ca){return new F(function(){return A2(_BE,_Ca,_C7);});}),_Cb=new T(function(){return B(_AO(function(_Cc){return new F(function(){return A1(_C3,new T2(0,_Cc,_we));});}));}),_Cd=function(_Ce){var _Cf=E(_Ce);if(_Cf==38){return E(_C4);}else{var _Cg=_Cf>>>0;if(_Cg>887){var _Ch=u_iswspace(_Cf);return (E(_Ch)==0)?new T0(2):E(_C9);}else{var _Ci=E(_Cg);return (_Ci==32)?E(_C9):(_Ci-9>>>0>4)?(E(_Ci)==160)?E(_C9):new T0(2):E(_C9);}}};return new F(function(){return _rH(new T1(0,function(_Cj){return (E(_Cj)==92)?E(new T1(0,_Cd)):new T0(2);}),new T1(0,function(_Ck){var _Cl=E(_Ck);if(E(_Cl)==92){return E(_Cb);}else{return new F(function(){return A1(_C3,new T2(0,_Cl,_wd));});}}));});},_Cm=function(_Cn,_Co){var _Cp=new T(function(){return B(A1(_Co,new T1(1,new T(function(){return B(A1(_Cn,_4));}))));}),_Cq=function(_Cr){var _Cs=E(_Cr),_Ct=E(_Cs.a);if(E(_Ct)==34){if(!E(_Cs.b)){return E(_Cp);}else{return new F(function(){return _Cm(function(_Cu){return new F(function(){return A1(_Cn,new T2(1,_Ct,_Cu));});},_Co);});}}else{return new F(function(){return _Cm(function(_Cv){return new F(function(){return A1(_Cn,new T2(1,_Ct,_Cv));});},_Co);});}};return new F(function(){return _C2(_Cq);});},_Cw=new T(function(){return B(unCStr("_\'"));}),_Cx=function(_Cy){var _Cz=u_iswalnum(_Cy);if(!E(_Cz)){return new F(function(){return _w5(_sw,_Cy,_Cw);});}else{return true;}},_CA=function(_CB){return new F(function(){return _Cx(E(_CB));});},_CC=new T(function(){return B(unCStr(",;()[]{}`"));}),_CD=new T(function(){return B(unCStr("=>"));}),_CE=new T2(1,_CD,_4),_CF=new T(function(){return B(unCStr("~"));}),_CG=new T2(1,_CF,_CE),_CH=new T(function(){return B(unCStr("@"));}),_CI=new T2(1,_CH,_CG),_CJ=new T(function(){return B(unCStr("->"));}),_CK=new T2(1,_CJ,_CI),_CL=new T(function(){return B(unCStr("<-"));}),_CM=new T2(1,_CL,_CK),_CN=new T(function(){return B(unCStr("|"));}),_CO=new T2(1,_CN,_CM),_CP=new T(function(){return B(unCStr("\\"));}),_CQ=new T2(1,_CP,_CO),_CR=new T(function(){return B(unCStr("="));}),_CS=new T2(1,_CR,_CQ),_CT=new T(function(){return B(unCStr("::"));}),_CU=new T2(1,_CT,_CS),_CV=new T(function(){return B(unCStr(".."));}),_CW=new T2(1,_CV,_CU),_CX=function(_CY){var _CZ=new T(function(){return B(A1(_CY,_tE));}),_D0=new T(function(){var _D1=new T(function(){var _D2=function(_D3){var _D4=new T(function(){return B(A1(_CY,new T1(0,_D3)));});return new T1(0,function(_D5){return (E(_D5)==39)?E(_D4):new T0(2);});};return B(_AO(_D2));}),_D6=function(_D7){var _D8=E(_D7);switch(E(_D8)){case 39:return new T0(2);case 92:return E(_D1);default:var _D9=new T(function(){return B(A1(_CY,new T1(0,_D8)));});return new T1(0,function(_Da){return (E(_Da)==39)?E(_D9):new T0(2);});}},_Db=new T(function(){var _Dc=new T(function(){return B(_Cm(_2j,_CY));}),_Dd=new T(function(){var _De=new T(function(){var _Df=new T(function(){var _Dg=function(_Dh){var _Di=E(_Dh),_Dj=u_iswalpha(_Di);return (E(_Dj)==0)?(E(_Di)==95)?new T1(1,B(_tq(_CA,function(_Dk){return new F(function(){return A1(_CY,new T1(3,new T2(1,_Di,_Dk)));});}))):new T0(2):new T1(1,B(_tq(_CA,function(_Dl){return new F(function(){return A1(_CY,new T1(3,new T2(1,_Di,_Dl)));});})));};return B(_rH(new T1(0,_Dg),new T(function(){return new T1(1,B(_t0(_uC,_w3,_CY)));})));}),_Dm=function(_Dn){return (!B(_w5(_sw,_Dn,_wa)))?new T0(2):new T1(1,B(_tq(_wb,function(_Do){var _Dp=new T2(1,_Dn,_Do);if(!B(_w5(_sF,_Dp,_CW))){return new F(function(){return A1(_CY,new T1(4,_Dp));});}else{return new F(function(){return A1(_CY,new T1(2,_Dp));});}})));};return B(_rH(new T1(0,_Dm),_Df));});return B(_rH(new T1(0,function(_Dq){if(!B(_w5(_sw,_Dq,_CC))){return new T0(2);}else{return new F(function(){return A1(_CY,new T1(2,new T2(1,_Dq,_4)));});}}),_De));});return B(_rH(new T1(0,function(_Dr){return (E(_Dr)==34)?E(_Dc):new T0(2);}),_Dd));});return B(_rH(new T1(0,function(_Ds){return (E(_Ds)==39)?E(new T1(0,_D6)):new T0(2);}),_Db));});return new F(function(){return _rH(new T1(1,function(_Dt){return (E(_Dt)._==0)?E(_CZ):new T0(2);}),_D0);});},_Du=0,_Dv=function(_Dw,_Dx){var _Dy=new T(function(){var _Dz=new T(function(){var _DA=function(_DB){var _DC=new T(function(){var _DD=new T(function(){return B(A1(_Dx,_DB));});return B(_CX(function(_DE){var _DF=E(_DE);return (_DF._==2)?(!B(_sl(_DF.a,_sk)))?new T0(2):E(_DD):new T0(2);}));}),_DG=function(_DH){return E(_DC);};return new T1(1,function(_DI){return new F(function(){return A2(_BE,_DI,_DG);});});};return B(A2(_Dw,_Du,_DA));});return B(_CX(function(_DJ){var _DK=E(_DJ);return (_DK._==2)?(!B(_sl(_DK.a,_sj)))?new T0(2):E(_Dz):new T0(2);}));}),_DL=function(_DM){return E(_Dy);};return function(_DN){return new F(function(){return A2(_BE,_DN,_DL);});};},_DO=function(_DP,_DQ){var _DR=function(_DS){var _DT=new T(function(){return B(A1(_DP,_DS));}),_DU=function(_DV){return new F(function(){return _rH(B(A1(_DT,_DV)),new T(function(){return new T1(1,B(_Dv(_DR,_DV)));}));});};return E(_DU);},_DW=new T(function(){return B(A1(_DP,_DQ));}),_DX=function(_DY){return new F(function(){return _rH(B(A1(_DW,_DY)),new T(function(){return new T1(1,B(_Dv(_DR,_DY)));}));});};return E(_DX);},_DZ=function(_E0,_E1){var _E2=function(_E3,_E4){var _E5=function(_E6){return new F(function(){return A1(_E4,new T(function(){return  -E(_E6);}));});},_E7=new T(function(){return B(_CX(function(_E8){return new F(function(){return A3(_E0,_E8,_E3,_E5);});}));}),_E9=function(_Ea){return E(_E7);},_Eb=function(_Ec){return new F(function(){return A2(_BE,_Ec,_E9);});},_Ed=new T(function(){return B(_CX(function(_Ee){var _Ef=E(_Ee);if(_Ef._==4){var _Eg=E(_Ef.a);if(!_Eg._){return new F(function(){return A3(_E0,_Ef,_E3,_E4);});}else{if(E(_Eg.a)==45){if(!E(_Eg.b)._){return E(new T1(1,_Eb));}else{return new F(function(){return A3(_E0,_Ef,_E3,_E4);});}}else{return new F(function(){return A3(_E0,_Ef,_E3,_E4);});}}}else{return new F(function(){return A3(_E0,_Ef,_E3,_E4);});}}));}),_Eh=function(_Ei){return E(_Ed);};return new T1(1,function(_Ej){return new F(function(){return A2(_BE,_Ej,_Eh);});});};return new F(function(){return _DO(_E2,_E1);});},_Ek=new T(function(){return 1/0;}),_El=function(_Em,_En){return new F(function(){return A1(_En,_Ek);});},_Eo=new T(function(){return 0/0;}),_Ep=function(_Eq,_Er){return new F(function(){return A1(_Er,_Eo);});},_Es=new T(function(){return B(unCStr("NaN"));}),_Et=new T(function(){return B(unCStr("Infinity"));}),_Eu=1024,_Ev=-1021,_Ew=function(_Ex,_Ey){while(1){var _Ez=E(_Ex);if(!_Ez._){var _EA=E(_Ez.a);if(_EA==(-2147483648)){_Ex=new T1(1,I_fromInt(-2147483648));continue;}else{var _EB=E(_Ey);if(!_EB._){return new T1(0,_EA%_EB.a);}else{_Ex=new T1(1,I_fromInt(_EA));_Ey=_EB;continue;}}}else{var _EC=_Ez.a,_ED=E(_Ey);return (_ED._==0)?new T1(1,I_rem(_EC,I_fromInt(_ED.a))):new T1(1,I_rem(_EC,_ED.a));}}},_EE=function(_EF,_EG){if(!B(_qK(_EG,_pU))){return new F(function(){return _Ew(_EF,_EG);});}else{return E(_nI);}},_EH=function(_EI,_EJ){while(1){if(!B(_qK(_EJ,_pU))){var _EK=_EJ,_EL=B(_EE(_EI,_EJ));_EI=_EK;_EJ=_EL;continue;}else{return E(_EI);}}},_EM=function(_EN){var _EO=E(_EN);if(!_EO._){var _EP=E(_EO.a);return (_EP==(-2147483648))?E(_uU):(_EP<0)?new T1(0, -_EP):E(_EO);}else{var _EQ=_EO.a;return (I_compareInt(_EQ,0)>=0)?E(_EO):new T1(1,I_negate(_EQ));}},_ER=function(_ES,_ET){while(1){var _EU=E(_ES);if(!_EU._){var _EV=E(_EU.a);if(_EV==(-2147483648)){_ES=new T1(1,I_fromInt(-2147483648));continue;}else{var _EW=E(_ET);if(!_EW._){return new T1(0,quot(_EV,_EW.a));}else{_ES=new T1(1,I_fromInt(_EV));_ET=_EW;continue;}}}else{var _EX=_EU.a,_EY=E(_ET);return (_EY._==0)?new T1(0,I_toInt(I_quot(_EX,I_fromInt(_EY.a)))):new T1(1,I_quot(_EX,_EY.a));}}},_EZ=5,_F0=new T(function(){return B(_nF(_EZ));}),_F1=new T(function(){return die(_F0);}),_F2=function(_F3,_F4){if(!B(_qK(_F4,_pU))){var _F5=B(_EH(B(_EM(_F3)),B(_EM(_F4))));return (!B(_qK(_F5,_pU)))?new T2(0,B(_ER(_F3,_F5)),B(_ER(_F4,_F5))):E(_nI);}else{return E(_F1);}},_F6=new T(function(){return B(_qK(_pV,_pU));}),_F7=function(_F8,_F9){while(1){var _Fa=E(_F8);if(!_Fa._){var _Fb=_Fa.a,_Fc=E(_F9);if(!_Fc._){var _Fd=_Fc.a,_Fe=subC(_Fb,_Fd);if(!E(_Fe.b)){return new T1(0,_Fe.a);}else{_F8=new T1(1,I_fromInt(_Fb));_F9=new T1(1,I_fromInt(_Fd));continue;}}else{_F8=new T1(1,I_fromInt(_Fb));_F9=_Fc;continue;}}else{var _Ff=E(_F9);if(!_Ff._){_F8=_Fa;_F9=new T1(1,I_fromInt(_Ff.a));continue;}else{return new T1(1,I_sub(_Fa.a,_Ff.a));}}}},_Fg=function(_Fh,_Fi,_Fj){while(1){if(!E(_F6)){if(!B(_qK(B(_Ew(_Fi,_pV)),_pU))){if(!B(_qK(_Fi,_oJ))){var _Fk=B(_pm(_Fh,_Fh)),_Fl=B(_ER(B(_F7(_Fi,_oJ)),_pV)),_Fm=B(_pm(_Fh,_Fj));_Fh=_Fk;_Fi=_Fl;_Fj=_Fm;continue;}else{return new F(function(){return _pm(_Fh,_Fj);});}}else{var _Fk=B(_pm(_Fh,_Fh)),_Fl=B(_ER(_Fi,_pV));_Fh=_Fk;_Fi=_Fl;continue;}}else{return E(_nI);}}},_Fn=function(_Fo,_Fp){while(1){if(!E(_F6)){if(!B(_qK(B(_Ew(_Fp,_pV)),_pU))){if(!B(_qK(_Fp,_oJ))){return new F(function(){return _Fg(B(_pm(_Fo,_Fo)),B(_ER(B(_F7(_Fp,_oJ)),_pV)),_Fo);});}else{return E(_Fo);}}else{var _Fq=B(_pm(_Fo,_Fo)),_Fr=B(_ER(_Fp,_pV));_Fo=_Fq;_Fp=_Fr;continue;}}else{return E(_nI);}}},_Fs=function(_Ft,_Fu){var _Fv=E(_Ft);if(!_Fv._){var _Fw=_Fv.a,_Fx=E(_Fu);return (_Fx._==0)?_Fw<_Fx.a:I_compareInt(_Fx.a,_Fw)>0;}else{var _Fy=_Fv.a,_Fz=E(_Fu);return (_Fz._==0)?I_compareInt(_Fy,_Fz.a)<0:I_compare(_Fy,_Fz.a)<0;}},_FA=function(_FB,_FC){if(!B(_Fs(_FC,_pU))){if(!B(_qK(_FC,_pU))){return new F(function(){return _Fn(_FB,_FC);});}else{return E(_oJ);}}else{return E(_qC);}},_FD=new T1(0,1),_FE=new T1(0,0),_FF=new T1(0,-1),_FG=function(_FH){var _FI=E(_FH);if(!_FI._){var _FJ=_FI.a;return (_FJ>=0)?(E(_FJ)==0)?E(_FE):E(_uJ):E(_FF);}else{var _FK=I_compareInt(_FI.a,0);return (_FK<=0)?(E(_FK)==0)?E(_FE):E(_FF):E(_uJ);}},_FL=function(_FM,_FN,_FO){while(1){var _FP=E(_FO);if(!_FP._){if(!B(_Fs(_FM,_ve))){return new T2(0,B(_pm(_FN,B(_FA(_uZ,_FM)))),_oJ);}else{var _FQ=B(_FA(_uZ,B(_uV(_FM))));return new F(function(){return _F2(B(_pm(_FN,B(_FG(_FQ)))),B(_EM(_FQ)));});}}else{var _FR=B(_F7(_FM,_FD)),_FS=B(_uL(B(_pm(_FN,_uZ)),B(_oF(E(_FP.a)))));_FM=_FR;_FN=_FS;_FO=_FP.b;continue;}}},_FT=function(_FU,_FV){var _FW=E(_FU);if(!_FW._){var _FX=_FW.a,_FY=E(_FV);return (_FY._==0)?_FX>=_FY.a:I_compareInt(_FY.a,_FX)<=0;}else{var _FZ=_FW.a,_G0=E(_FV);return (_G0._==0)?I_compareInt(_FZ,_G0.a)>=0:I_compare(_FZ,_G0.a)>=0;}},_G1=function(_G2){var _G3=E(_G2);if(!_G3._){var _G4=_G3.b;return new F(function(){return _F2(B(_pm(B(_vf(new T(function(){return B(_oF(E(_G3.a)));}),new T(function(){return B(_v0(_G4,0));},1),B(_G(_v5,_G4)))),_FD)),_FD);});}else{var _G5=_G3.a,_G6=_G3.c,_G7=E(_G3.b);if(!_G7._){var _G8=E(_G6);if(!_G8._){return new F(function(){return _F2(B(_pm(B(_vw(_uZ,_G5)),_FD)),_FD);});}else{var _G9=_G8.a;if(!B(_FT(_G9,_ve))){var _Ga=B(_FA(_uZ,B(_uV(_G9))));return new F(function(){return _F2(B(_pm(B(_vw(_uZ,_G5)),B(_FG(_Ga)))),B(_EM(_Ga)));});}else{return new F(function(){return _F2(B(_pm(B(_pm(B(_vw(_uZ,_G5)),B(_FA(_uZ,_G9)))),_FD)),_FD);});}}}else{var _Gb=_G7.a,_Gc=E(_G6);if(!_Gc._){return new F(function(){return _FL(_ve,B(_vw(_uZ,_G5)),_Gb);});}else{return new F(function(){return _FL(_Gc.a,B(_vw(_uZ,_G5)),_Gb);});}}}},_Gd=function(_Ge,_Gf){while(1){var _Gg=E(_Gf);if(!_Gg._){return __Z;}else{if(!B(A1(_Ge,_Gg.a))){return E(_Gg);}else{_Gf=_Gg.b;continue;}}}},_Gh=function(_Gi,_Gj){var _Gk=E(_Gi);if(!_Gk._){var _Gl=_Gk.a,_Gm=E(_Gj);return (_Gm._==0)?_Gl>_Gm.a:I_compareInt(_Gm.a,_Gl)<0;}else{var _Gn=_Gk.a,_Go=E(_Gj);return (_Go._==0)?I_compareInt(_Gn,_Go.a)>0:I_compare(_Gn,_Go.a)>0;}},_Gp=0,_Gq=function(_Gr){return new F(function(){return _j1(_Gp,_Gr);});},_Gs=new T2(0,E(_ve),E(_oJ)),_Gt=new T1(1,_Gs),_Gu=new T1(0,-2147483648),_Gv=new T1(0,2147483647),_Gw=function(_Gx,_Gy,_Gz){var _GA=E(_Gz);if(!_GA._){return new T1(1,new T(function(){var _GB=B(_G1(_GA));return new T2(0,E(_GB.a),E(_GB.b));}));}else{var _GC=E(_GA.c);if(!_GC._){return new T1(1,new T(function(){var _GD=B(_G1(_GA));return new T2(0,E(_GD.a),E(_GD.b));}));}else{var _GE=_GC.a;if(!B(_Gh(_GE,_Gv))){if(!B(_Fs(_GE,_Gu))){var _GF=function(_GG){var _GH=_GG+B(_oV(_GE))|0;return (_GH<=(E(_Gy)+3|0))?(_GH>=(E(_Gx)-3|0))?new T1(1,new T(function(){var _GI=B(_G1(_GA));return new T2(0,E(_GI.a),E(_GI.b));})):E(_Gt):__Z;},_GJ=B(_Gd(_Gq,_GA.a));if(!_GJ._){var _GK=E(_GA.b);if(!_GK._){return E(_Gt);}else{var _GL=B(_6T(_Gq,_GK.a));if(!E(_GL.b)._){return E(_Gt);}else{return new F(function(){return _GF( -B(_v0(_GL.a,0)));});}}}else{return new F(function(){return _GF(B(_v0(_GJ,0)));});}}else{return __Z;}}else{return __Z;}}}},_GM=function(_GN,_GO){return new T0(2);},_GP=new T1(0,1),_GQ=function(_GR,_GS){var _GT=E(_GR);if(!_GT._){var _GU=_GT.a,_GV=E(_GS);if(!_GV._){var _GW=_GV.a;return (_GU!=_GW)?(_GU>_GW)?2:0:1;}else{var _GX=I_compareInt(_GV.a,_GU);return (_GX<=0)?(_GX>=0)?1:2:0;}}else{var _GY=_GT.a,_GZ=E(_GS);if(!_GZ._){var _H0=I_compareInt(_GY,_GZ.a);return (_H0>=0)?(_H0<=0)?1:2:0;}else{var _H1=I_compare(_GY,_GZ.a);return (_H1>=0)?(_H1<=0)?1:2:0;}}},_H2=function(_H3,_H4){while(1){var _H5=E(_H3);if(!_H5._){_H3=new T1(1,I_fromInt(_H5.a));continue;}else{return new T1(1,I_shiftLeft(_H5.a,_H4));}}},_H6=function(_H7,_H8,_H9){if(!B(_qK(_H9,_r2))){var _Ha=B(_qS(_H8,_H9)),_Hb=_Ha.a;switch(B(_GQ(B(_H2(_Ha.b,1)),_H9))){case 0:return new F(function(){return _qG(_Hb,_H7);});break;case 1:if(!(B(_oV(_Hb))&1)){return new F(function(){return _qG(_Hb,_H7);});}else{return new F(function(){return _qG(B(_uL(_Hb,_GP)),_H7);});}break;default:return new F(function(){return _qG(B(_uL(_Hb,_GP)),_H7);});}}else{return E(_nI);}},_Hc=function(_Hd){var _He=function(_Hf,_Hg){while(1){if(!B(_Fs(_Hf,_Hd))){if(!B(_Gh(_Hf,_Hd))){if(!B(_qK(_Hf,_Hd))){return new F(function(){return _7f("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_Hg);}}else{return _Hg-1|0;}}else{var _Hh=B(_H2(_Hf,1)),_Hi=_Hg+1|0;_Hf=_Hh;_Hg=_Hi;continue;}}};return new F(function(){return _He(_uJ,0);});},_Hj=function(_Hk){var _Hl=E(_Hk);if(!_Hl._){var _Hm=_Hl.a>>>0;if(!_Hm){return -1;}else{var _Hn=function(_Ho,_Hp){while(1){if(_Ho>=_Hm){if(_Ho<=_Hm){if(_Ho!=_Hm){return new F(function(){return _7f("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_Hp);}}else{return _Hp-1|0;}}else{var _Hq=imul(_Ho,2)>>>0,_Hr=_Hp+1|0;_Ho=_Hq;_Hp=_Hr;continue;}}};return new F(function(){return _Hn(1,0);});}}else{return new F(function(){return _Hc(_Hl);});}},_Hs=function(_Ht){var _Hu=E(_Ht);if(!_Hu._){var _Hv=_Hu.a>>>0;if(!_Hv){return new T2(0,-1,0);}else{var _Hw=function(_Hx,_Hy){while(1){if(_Hx>=_Hv){if(_Hx<=_Hv){if(_Hx!=_Hv){return new F(function(){return _7f("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_Hy);}}else{return _Hy-1|0;}}else{var _Hz=imul(_Hx,2)>>>0,_HA=_Hy+1|0;_Hx=_Hz;_Hy=_HA;continue;}}};return new T2(0,B(_Hw(1,0)),(_Hv&_Hv-1>>>0)>>>0&4294967295);}}else{var _HB=_Hu.a;return new T2(0,B(_Hj(_Hu)),I_compareInt(I_and(_HB,I_sub(_HB,I_fromInt(1))),0));}},_HC=function(_HD,_HE){while(1){var _HF=E(_HD);if(!_HF._){var _HG=_HF.a,_HH=E(_HE);if(!_HH._){return new T1(0,(_HG>>>0&_HH.a>>>0)>>>0&4294967295);}else{_HD=new T1(1,I_fromInt(_HG));_HE=_HH;continue;}}else{var _HI=E(_HE);if(!_HI._){_HD=_HF;_HE=new T1(1,I_fromInt(_HI.a));continue;}else{return new T1(1,I_and(_HF.a,_HI.a));}}}},_HJ=new T1(0,2),_HK=function(_HL,_HM){var _HN=E(_HL);if(!_HN._){var _HO=(_HN.a>>>0&(2<<_HM>>>0)-1>>>0)>>>0,_HP=1<<_HM>>>0;return (_HP<=_HO)?(_HP>=_HO)?1:2:0;}else{var _HQ=B(_HC(_HN,B(_F7(B(_H2(_HJ,_HM)),_uJ)))),_HR=B(_H2(_uJ,_HM));return (!B(_Gh(_HR,_HQ)))?(!B(_Fs(_HR,_HQ)))?1:2:0;}},_HS=function(_HT,_HU){while(1){var _HV=E(_HT);if(!_HV._){_HT=new T1(1,I_fromInt(_HV.a));continue;}else{return new T1(1,I_shiftRight(_HV.a,_HU));}}},_HW=function(_HX,_HY,_HZ,_I0){var _I1=B(_Hs(_I0)),_I2=_I1.a;if(!E(_I1.b)){var _I3=B(_Hj(_HZ));if(_I3<((_I2+_HX|0)-1|0)){var _I4=_I2+(_HX-_HY|0)|0;if(_I4>0){if(_I4>_I3){if(_I4<=(_I3+1|0)){if(!E(B(_Hs(_HZ)).b)){return 0;}else{return new F(function(){return _qG(_GP,_HX-_HY|0);});}}else{return 0;}}else{var _I5=B(_HS(_HZ,_I4));switch(B(_HK(_HZ,_I4-1|0))){case 0:return new F(function(){return _qG(_I5,_HX-_HY|0);});break;case 1:if(!(B(_oV(_I5))&1)){return new F(function(){return _qG(_I5,_HX-_HY|0);});}else{return new F(function(){return _qG(B(_uL(_I5,_GP)),_HX-_HY|0);});}break;default:return new F(function(){return _qG(B(_uL(_I5,_GP)),_HX-_HY|0);});}}}else{return new F(function(){return _qG(_HZ,(_HX-_HY|0)-_I4|0);});}}else{if(_I3>=_HY){var _I6=B(_HS(_HZ,(_I3+1|0)-_HY|0));switch(B(_HK(_HZ,_I3-_HY|0))){case 0:return new F(function(){return _qG(_I6,((_I3-_I2|0)+1|0)-_HY|0);});break;case 2:return new F(function(){return _qG(B(_uL(_I6,_GP)),((_I3-_I2|0)+1|0)-_HY|0);});break;default:if(!(B(_oV(_I6))&1)){return new F(function(){return _qG(_I6,((_I3-_I2|0)+1|0)-_HY|0);});}else{return new F(function(){return _qG(B(_uL(_I6,_GP)),((_I3-_I2|0)+1|0)-_HY|0);});}}}else{return new F(function(){return _qG(_HZ, -_I2);});}}}else{var _I7=B(_Hj(_HZ))-_I2|0,_I8=function(_I9){var _Ia=function(_Ib,_Ic){if(!B(_wo(B(_H2(_Ic,_HY)),_Ib))){return new F(function(){return _H6(_I9-_HY|0,_Ib,_Ic);});}else{return new F(function(){return _H6((_I9-_HY|0)+1|0,_Ib,B(_H2(_Ic,1)));});}};if(_I9>=_HY){if(_I9!=_HY){return new F(function(){return _Ia(_HZ,new T(function(){return B(_H2(_I0,_I9-_HY|0));}));});}else{return new F(function(){return _Ia(_HZ,_I0);});}}else{return new F(function(){return _Ia(new T(function(){return B(_H2(_HZ,_HY-_I9|0));}),_I0);});}};if(_HX>_I7){return new F(function(){return _I8(_HX);});}else{return new F(function(){return _I8(_I7);});}}},_Id=new T(function(){return 0/0;}),_Ie=new T(function(){return -1/0;}),_If=new T(function(){return 1/0;}),_Ig=function(_Ih,_Ii){if(!B(_qK(_Ii,_r2))){if(!B(_qK(_Ih,_r2))){if(!B(_Fs(_Ih,_r2))){return new F(function(){return _HW(-1021,53,_Ih,_Ii);});}else{return  -B(_HW(-1021,53,B(_uV(_Ih)),_Ii));}}else{return E(_r1);}}else{return (!B(_qK(_Ih,_r2)))?(!B(_Fs(_Ih,_r2)))?E(_If):E(_Ie):E(_Id);}},_Ij=function(_Ik){var _Il=E(_Ik);switch(_Il._){case 3:var _Im=_Il.a;return (!B(_sl(_Im,_Et)))?(!B(_sl(_Im,_Es)))?E(_GM):E(_Ep):E(_El);case 5:var _In=B(_Gw(_Ev,_Eu,_Il.a));if(!_In._){return E(_El);}else{var _Io=new T(function(){var _Ip=E(_In.a);return B(_Ig(_Ip.a,_Ip.b));});return function(_Iq,_Ir){return new F(function(){return A1(_Ir,_Io);});};}break;default:return E(_GM);}},_Is=function(_It){var _Iu=function(_Iv){return E(new T2(3,_It,_sR));};return new T1(1,function(_Iw){return new F(function(){return A2(_BE,_Iw,_Iu);});});},_Ix=new T(function(){return B(A3(_DZ,_Ij,_Du,_Is));}),_Iy=new T(function(){return B(_rx(_Ix,_rv));}),_Iz=function(_IA){while(1){var _IB=B((function(_IC){var _ID=E(_IC);if(!_ID._){return __Z;}else{var _IE=_ID.b,_IF=E(_ID.a);if(!E(_IF.b)._){return new T2(1,_IF.a,new T(function(){return B(_Iz(_IE));}));}else{_IA=_IE;return __continue;}}})(_IA));if(_IB!=__continue){return _IB;}}},_IG=new T(function(){return B(_Iz(_Iy));}),_IH=new T(function(){return B(unCStr("Infinity"));}),_II=new T(function(){return B(_rx(_Ix,_IH));}),_IJ=new T(function(){return B(_Iz(_II));}),_IK=0,_IL=function(_IM,_IN,_IO){return new F(function(){return _eX(_ea,new T2(0,_IN,_IO),_IM,_f2);});},_IP=function(_IQ,_IR,_IS){var _IT=(_IQ+_IR|0)-1|0;if(_IQ<=_IT){var _IU=function(_IV){return new T2(1,new T(function(){var _IW=E(_IS),_IX=_IW.c,_IY=E(_IW.a),_IZ=E(_IW.b);if(_IY>_IV){return B(_IL(_IV,_IY,_IZ));}else{if(_IV>_IZ){return B(_IL(_IV,_IY,_IZ));}else{var _J0=_IV-_IY|0;if(0>_J0){return B(_dT(_J0,_IX));}else{if(_J0>=_IX){return B(_dT(_J0,_IX));}else{return _IW.d["v"]["w8"][_J0];}}}}}),new T(function(){if(_IV!=_IT){return B(_IU(_IV+1|0));}else{return __Z;}}));};return new F(function(){return _IU(_IQ);});}else{return __Z;}},_J1=function(_J2){var _J3=E(_J2);return new F(function(){return _IP(_J3.a,_J3.b,_J3.c);});},_J4=function(_J5,_J6,_J7,_J8){var _J9=new T(function(){var _Ja=E(_J5),_Jb=E(_J7),_Jc=_Jb.a,_Jd=_Jb.b,_Je=_Jb.c,_Jf=E(_J8);if((_Jf+_Ja|0)<=_Jd){return new T2(0,new T(function(){var _Jg=_Jd-_Jf|0;if(_Ja>_Jg){return new T3(0,_Jc+_Jf|0,_Jg,_Je);}else{return new T3(0,_Jc+_Jf|0,_Ja,_Je);}}),_Jf+_Ja|0);}else{return E(_fy);}}),_Jh=new T(function(){return B(A1(_J6,new T(function(){return B(_J1(E(_J9).a));})));}),_Ji=new T(function(){var _Jj=E(_Jh),_Jk=_Jj.d,_Jl=_Jj.e,_Jm=_Jj.f,_Jn=E(_Jj.c);if(!_Jn){if(!B(_qK(_Jk,_rp))){var _Jo=B(_r3(_pc,Math.pow(2,E(_Jl)-1|0))),_Jp=_Jo.a;if(E(_Jo.b)>=0){return B(_qG(_Jk,((1-E(_Jp)|0)-E(_Jm)|0)+1|0));}else{return B(_qG(_Jk,((1-(E(_Jp)-1|0)|0)-E(_Jm)|0)+1|0));}}else{return E(_IK);}}else{var _Jq=E(_Jl);if(_Jn!=(B(_rj(_ru,_Jq))-1|0)){var _Jr=B(_r3(_pc,Math.pow(2,_Jq-1|0))),_Js=_Jr.a;if(E(_Jr.b)>=0){var _Jt=E(_Jm);return B(_qG(B(_uL(_Jk,B(_H2(_ro,_Jt)))),((_Jn+1|0)-E(_Js)|0)-_Jt|0));}else{var _Ju=E(_Jm);return B(_qG(B(_uL(_Jk,B(_H2(_ro,_Ju)))),((_Jn+1|0)-(E(_Js)-1|0)|0)-_Ju|0));}}else{if(!B(_qK(_Jk,_rp))){var _Jv=E(_IG);if(!_Jv._){return E(_rr);}else{if(!E(_Jv.b)._){return E(_Jv.a);}else{return E(_rt);}}}else{var _Jw=E(_IJ);if(!_Jw._){return E(_rr);}else{if(!E(_Jw.b)._){return E(_Jw.a);}else{return E(_rt);}}}}}});return new T2(0,new T(function(){if(!E(E(_Jh).b)){return E(_Ji);}else{return  -E(_Ji);}}),new T(function(){return E(E(_J9).b);}));},_Jx=new T(function(){return B(unCStr("This file was compiled with different version of GF"));}),_Jy=new T(function(){return B(err(_Jx));}),_Jz=8,_JA={_:0,a:_n4,b:_mZ,c:_mV,d:_mV,e:_mp,f:_mK,g:_iK,h:_mR},_JB={_:0,a:_oP,b:_iV,c:_oM,d:_p0,e:_oS,f:_p5,g:_oY},_JC=new T2(0,_j1,_j4),_JD={_:0,a:_JC,b:_jl,c:_jx,d:_ju,e:_jr,f:_jo,g:_j8,h:_jd},_JE=new T3(0,_JB,_JD,_oK),_JF={_:0,a:_JE,b:_JA,c:_on,d:_oB,e:_nR,f:_oj,g:_ot,h:_nW,i:_oH},_JG=new T1(0,1),_JH=function(_JI,_JJ){var _JK=E(_JI);return new T2(0,_JK,new T(function(){var _JL=B(_JH(B(_uL(_JK,_JJ)),_JJ));return new T2(1,_JL.a,_JL.b);}));},_JM=function(_JN){var _JO=B(_JH(_JN,_JG));return new T2(1,_JO.a,_JO.b);},_JP=function(_JQ,_JR){var _JS=B(_JH(_JQ,new T(function(){return B(_F7(_JR,_JQ));})));return new T2(1,_JS.a,_JS.b);},_JT=new T1(0,0),_JU=function(_JV,_JW,_JX){if(!B(_FT(_JW,_JT))){var _JY=function(_JZ){return (!B(_Fs(_JZ,_JX)))?new T2(1,_JZ,new T(function(){return B(_JY(B(_uL(_JZ,_JW))));})):__Z;};return new F(function(){return _JY(_JV);});}else{var _K0=function(_K1){return (!B(_Gh(_K1,_JX)))?new T2(1,_K1,new T(function(){return B(_K0(B(_uL(_K1,_JW))));})):__Z;};return new F(function(){return _K0(_JV);});}},_K2=function(_K3,_K4,_K5){return new F(function(){return _JU(_K3,B(_F7(_K4,_K3)),_K5);});},_K6=function(_K7,_K8){return new F(function(){return _JU(_K7,_JG,_K8);});},_K9=function(_Ka){return new F(function(){return _oV(_Ka);});},_Kb=function(_Kc){return new F(function(){return _F7(_Kc,_JG);});},_Kd=function(_Ke){return new F(function(){return _uL(_Ke,_JG);});},_Kf=function(_Kg){return new F(function(){return _oF(E(_Kg));});},_Kh={_:0,a:_Kd,b:_Kb,c:_Kf,d:_K9,e:_JM,f:_JP,g:_K6,h:_K2},_Ki=function(_Kj,_Kk){while(1){var _Kl=E(_Kj);if(!_Kl._){var _Km=E(_Kl.a);if(_Km==(-2147483648)){_Kj=new T1(1,I_fromInt(-2147483648));continue;}else{var _Kn=E(_Kk);if(!_Kn._){return new T1(0,B(_n8(_Km,_Kn.a)));}else{_Kj=new T1(1,I_fromInt(_Km));_Kk=_Kn;continue;}}}else{var _Ko=_Kl.a,_Kp=E(_Kk);return (_Kp._==0)?new T1(1,I_div(_Ko,I_fromInt(_Kp.a))):new T1(1,I_div(_Ko,_Kp.a));}}},_Kq=function(_Kr,_Ks){if(!B(_qK(_Ks,_pU))){return new F(function(){return _Ki(_Kr,_Ks);});}else{return E(_nI);}},_Kt=function(_Ku,_Kv){while(1){var _Kw=E(_Ku);if(!_Kw._){var _Kx=E(_Kw.a);if(_Kx==(-2147483648)){_Ku=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ky=E(_Kv);if(!_Ky._){var _Kz=_Ky.a;return new T2(0,new T1(0,B(_n8(_Kx,_Kz))),new T1(0,B(_oc(_Kx,_Kz))));}else{_Ku=new T1(1,I_fromInt(_Kx));_Kv=_Ky;continue;}}}else{var _KA=E(_Kv);if(!_KA._){_Ku=_Kw;_Kv=new T1(1,I_fromInt(_KA.a));continue;}else{var _KB=I_divMod(_Kw.a,_KA.a);return new T2(0,new T1(1,_KB.a),new T1(1,_KB.b));}}}},_KC=function(_KD,_KE){if(!B(_qK(_KE,_pU))){var _KF=B(_Kt(_KD,_KE));return new T2(0,_KF.a,_KF.b);}else{return E(_nI);}},_KG=function(_KH,_KI){while(1){var _KJ=E(_KH);if(!_KJ._){var _KK=E(_KJ.a);if(_KK==(-2147483648)){_KH=new T1(1,I_fromInt(-2147483648));continue;}else{var _KL=E(_KI);if(!_KL._){return new T1(0,B(_oc(_KK,_KL.a)));}else{_KH=new T1(1,I_fromInt(_KK));_KI=_KL;continue;}}}else{var _KM=_KJ.a,_KN=E(_KI);return (_KN._==0)?new T1(1,I_mod(_KM,I_fromInt(_KN.a))):new T1(1,I_mod(_KM,_KN.a));}}},_KO=function(_KP,_KQ){if(!B(_qK(_KQ,_pU))){return new F(function(){return _KG(_KP,_KQ);});}else{return E(_nI);}},_KR=function(_KS,_KT){if(!B(_qK(_KT,_pU))){return new F(function(){return _ER(_KS,_KT);});}else{return E(_nI);}},_KU=function(_KV,_KW){if(!B(_qK(_KW,_pU))){var _KX=B(_qS(_KV,_KW));return new T2(0,_KX.a,_KX.b);}else{return E(_nI);}},_KY=function(_KZ){return E(_KZ);},_L0=function(_L1){return E(_L1);},_L2={_:0,a:_uL,b:_F7,c:_pm,d:_uV,e:_EM,f:_FG,g:_L0},_L3=function(_L4,_L5){var _L6=E(_L4);if(!_L6._){var _L7=_L6.a,_L8=E(_L5);return (_L8._==0)?_L7!=_L8.a:(I_compareInt(_L8.a,_L7)==0)?false:true;}else{var _L9=_L6.a,_La=E(_L5);return (_La._==0)?(I_compareInt(_L9,_La.a)==0)?false:true:(I_compare(_L9,_La.a)==0)?false:true;}},_Lb=new T2(0,_qK,_L3),_Lc=function(_Ld,_Le){return (!B(_wo(_Ld,_Le)))?E(_Ld):E(_Le);},_Lf=function(_Lg,_Lh){return (!B(_wo(_Lg,_Lh)))?E(_Lh):E(_Lg);},_Li={_:0,a:_Lb,b:_GQ,c:_Fs,d:_wo,e:_Gh,f:_FT,g:_Lc,h:_Lf},_Lj=function(_Lk){return new T2(0,E(_Lk),E(_oJ));},_Ll=new T3(0,_L2,_Li,_Lj),_Lm={_:0,a:_Ll,b:_Kh,c:_KR,d:_EE,e:_Kq,f:_KO,g:_KU,h:_KC,i:_KY},_Ln=function(_Lo,_Lp){while(1){var _Lq=E(_Lo);if(!_Lq._){return E(_Lp);}else{var _Lr=B(_uL(B(_H2(_Lp,8)),B(_oF(E(_Lq.a)&4294967295))));_Lo=_Lq.b;_Lp=_Lr;continue;}}},_Ls=function(_Lt,_Lu,_Lv){var _Lw=imul(B(_v0(_Lt,0)),8)|0,_Lx=B(_r3(_Lm,Math.pow(2,_Lw-_Lu|0))),_Ly=_Lx.a;return (E(_Lx.b)>=0)?E(B(_HS(B(_HC(B(_Ln(_Lt,_rp)),B(_F7(_Ly,_ro)))),_Lw-_Lv|0)).a):E(B(_HS(B(_HC(B(_Ln(_Lt,_rp)),B(_F7(B(_F7(_Ly,_ro)),_ro)))),_Lw-_Lv|0)).a);},_Lz=new T(function(){return B(unCStr("head"));}),_LA=new T(function(){return B(_ei(_Lz));}),_LB=function(_LC,_LD,_LE){return new T1(1,B(_Ls(_LC,E(_LD),E(_LE))));},_LF=5,_LG=new T(function(){return B(unCStr("Invalid length of floating-point value"));}),_LH=new T(function(){return B(err(_LG));}),_LI=function(_LJ){var _LK=new T(function(){return imul(B(_v0(_LJ,0)),8)|0;}),_LL=new T(function(){var _LM=E(_LK);switch(_LM){case 16:return E(_LF);break;case 32:return E(_Jz);break;default:if(!B(_oc(_LM,32))){var _LN=B(_r3(_JF,4*(Math.log(_LM)/Math.log(2)))),_LO=_LN.a;if(E(_LN.b)<=0){return E(_LO)-13|0;}else{return (E(_LO)+1|0)-13|0;}}else{return E(_LH);}}}),_LP=new T(function(){return 1+E(_LL)|0;});return new T6(0,new T(function(){return B(_v0(_LJ,0));}),new T(function(){var _LQ=E(_LJ);if(!_LQ._){return E(_LA);}else{if((E(_LQ.a)&128)>>>0==128){return 1;}else{return 0;}}}),new T(function(){return B(_oV(new T1(1,B(_Ls(_LJ,1,E(_LP))))));}),new T(function(){return B(_LB(_LJ,_LP,_LK));}),_LL,new T(function(){return B(_iV(_LK,_LP));}));},_LR=function(_LS){var _LT=B(_LI(_LS));return new T6(0,_LT.a,_LT.b,_LT.c,_LT.d,_LT.e,_LT.f);},_LU=function(_LV,_LW,_LX,_LY){var _LZ=B(_fi(_LV,_LW,_LX,_LY)),_M0=_LZ.b;switch(E(_LZ.a)){case 0:var _M1=B(_fo(_LV,_LW,_LX,E(_M0))),_M2=B(_gl(E(_M1.a)&4294967295,_g9,new T3(0,_LV,_LW,_LX),_M1.b));return new T2(0,new T1(0,_M2.a),_M2.b);case 1:var _M3=B(_fo(_LV,_LW,_LX,E(_M0)));return new T2(0,new T1(1,new T(function(){return E(_M3.a)&4294967295;})),_M3.b);case 2:var _M4=B(_J4(_Jz,_LR,new T3(0,_LV,_LW,_LX),_M0));return new T2(0,new T1(2,_M4.a),_M4.b);default:return E(_Jy);}},_M5=function(_M6,_M7){var _M8=E(_M6),_M9=B(_LU(_M8.a,_M8.b,_M8.c,E(_M7)));return new T2(0,_M9.a,_M9.b);},_Ma=function(_Mb){switch(E(_Mb)._){case 0:return E(_dP);case 1:return E(_dP);default:return E(_dP);}},_Mc=new T2(0,_Ma,_M5),_Md=function(_Me){return E(_dP);},_Mf=-4,_Mg=function(_Mh){var _Mi=E(_Mh);return (_Mi._==0)?__Z:new T2(1,new T2(0,_Mf,_Mi.a),new T(function(){return B(_Mg(_Mi.b));}));},_Mj=function(_Mk,_Ml,_Mm,_Mn){var _Mo=B(_fo(_Mk,_Ml,_Mm,_Mn)),_Mp=B(_gl(E(_Mo.a)&4294967295,_kv,new T3(0,_Mk,_Ml,_Mm),_Mo.b)),_Mq=B(_fo(_Mk,_Ml,_Mm,E(_Mp.b))),_Mr=new T(function(){return new T2(0,new T(function(){return B(_Mg(_Mp.a));}),E(_Mq.a)&4294967295);});return new T2(0,_Mr,_Mq.b);},_Ms=function(_Mt,_Mu){var _Mv=E(_Mt),_Mw=B(_Mj(_Mv.a,_Mv.b,_Mv.c,E(_Mu)));return new T2(0,_Mw.a,_Mw.b);},_Mx=function(_My,_Mz,_MA,_MB){var _MC=B(_fi(_My,_Mz,_MA,_MB)),_MD=_MC.b;switch(E(_MC.a)){case 0:var _ME=B(_fo(_My,_Mz,_MA,E(_MD))),_MF=B(_fo(_My,_Mz,_MA,E(_ME.b))),_MG=B(_gl(E(_MF.a)&4294967295,_Ms,new T3(0,_My,_Mz,_MA),_MF.b));return new T2(0,new T(function(){return new T2(0,E(_ME.a)&4294967295,_MG.a);}),_MG.b);case 1:var _MH=B(_fo(_My,_Mz,_MA,E(_MD)));return new T2(0,new T(function(){return new T1(1,E(_MH.a)&4294967295);}),_MH.b);default:return E(_Jy);}},_MI=function(_MJ,_MK){var _ML=E(_MJ),_MM=B(_Mx(_ML.a,_ML.b,_ML.c,E(_MK)));return new T2(0,_MM.a,_MM.b);},_MN=new T(function(){return B(_7f("pgf/PGF/Binary.hs:(243,3)-(244,51)|function put"));}),_MO=function(_MP){switch(E(_MP)._){case 0:return E(_dP);case 1:return E(_dP);default:return E(_MN);}},_MQ=new T2(0,_MO,_MI),_MR=new T0(1),_MS=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_MT=function(_MU){return new F(function(){return err(_MS);});},_MV=new T(function(){return B(_MT(_));}),_MW=function(_MX,_MY,_MZ){var _N0=E(_MZ);if(!_N0._){var _N1=_N0.a,_N2=E(_MY);if(!_N2._){var _N3=_N2.a,_N4=_N2.b;if(_N3<=(imul(3,_N1)|0)){return new T4(0,(1+_N3|0)+_N1|0,E(_MX),E(_N2),E(_N0));}else{var _N5=E(_N2.c);if(!_N5._){var _N6=_N5.a,_N7=E(_N2.d);if(!_N7._){var _N8=_N7.a,_N9=_N7.b,_Na=_N7.c;if(_N8>=(imul(2,_N6)|0)){var _Nb=function(_Nc){var _Nd=E(_N7.d);return (_Nd._==0)?new T4(0,(1+_N3|0)+_N1|0,E(_N9),E(new T4(0,(1+_N6|0)+_Nc|0,E(_N4),E(_N5),E(_Na))),E(new T4(0,(1+_N1|0)+_Nd.a|0,E(_MX),E(_Nd),E(_N0)))):new T4(0,(1+_N3|0)+_N1|0,E(_N9),E(new T4(0,(1+_N6|0)+_Nc|0,E(_N4),E(_N5),E(_Na))),E(new T4(0,1+_N1|0,E(_MX),E(_MR),E(_N0))));},_Ne=E(_Na);if(!_Ne._){return new F(function(){return _Nb(_Ne.a);});}else{return new F(function(){return _Nb(0);});}}else{return new T4(0,(1+_N3|0)+_N1|0,E(_N4),E(_N5),E(new T4(0,(1+_N1|0)+_N8|0,E(_MX),E(_N7),E(_N0))));}}else{return E(_MV);}}else{return E(_MV);}}}else{return new T4(0,1+_N1|0,E(_MX),E(_MR),E(_N0));}}else{var _Nf=E(_MY);if(!_Nf._){var _Ng=_Nf.a,_Nh=_Nf.b,_Ni=_Nf.d,_Nj=E(_Nf.c);if(!_Nj._){var _Nk=_Nj.a,_Nl=E(_Ni);if(!_Nl._){var _Nm=_Nl.a,_Nn=_Nl.b,_No=_Nl.c;if(_Nm>=(imul(2,_Nk)|0)){var _Np=function(_Nq){var _Nr=E(_Nl.d);return (_Nr._==0)?new T4(0,1+_Ng|0,E(_Nn),E(new T4(0,(1+_Nk|0)+_Nq|0,E(_Nh),E(_Nj),E(_No))),E(new T4(0,1+_Nr.a|0,E(_MX),E(_Nr),E(_MR)))):new T4(0,1+_Ng|0,E(_Nn),E(new T4(0,(1+_Nk|0)+_Nq|0,E(_Nh),E(_Nj),E(_No))),E(new T4(0,1,E(_MX),E(_MR),E(_MR))));},_Ns=E(_No);if(!_Ns._){return new F(function(){return _Np(_Ns.a);});}else{return new F(function(){return _Np(0);});}}else{return new T4(0,1+_Ng|0,E(_Nh),E(_Nj),E(new T4(0,1+_Nm|0,E(_MX),E(_Nl),E(_MR))));}}else{return new T4(0,3,E(_Nh),E(_Nj),E(new T4(0,1,E(_MX),E(_MR),E(_MR))));}}else{var _Nt=E(_Ni);return (_Nt._==0)?new T4(0,3,E(_Nt.b),E(new T4(0,1,E(_Nh),E(_MR),E(_MR))),E(new T4(0,1,E(_MX),E(_MR),E(_MR)))):new T4(0,2,E(_MX),E(_Nf),E(_MR));}}else{return new T4(0,1,E(_MX),E(_MR),E(_MR));}}},_Nu=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_Nv=function(_Nw){return new F(function(){return err(_Nu);});},_Nx=new T(function(){return B(_Nv(_));}),_Ny=function(_Nz,_NA,_NB){var _NC=E(_NA);if(!_NC._){var _ND=_NC.a,_NE=E(_NB);if(!_NE._){var _NF=_NE.a,_NG=_NE.b;if(_NF<=(imul(3,_ND)|0)){return new T4(0,(1+_ND|0)+_NF|0,E(_Nz),E(_NC),E(_NE));}else{var _NH=E(_NE.c);if(!_NH._){var _NI=_NH.a,_NJ=_NH.b,_NK=_NH.c,_NL=E(_NE.d);if(!_NL._){var _NM=_NL.a;if(_NI>=(imul(2,_NM)|0)){var _NN=function(_NO){var _NP=E(_Nz),_NQ=E(_NH.d);return (_NQ._==0)?new T4(0,(1+_ND|0)+_NF|0,E(_NJ),E(new T4(0,(1+_ND|0)+_NO|0,E(_NP),E(_NC),E(_NK))),E(new T4(0,(1+_NM|0)+_NQ.a|0,E(_NG),E(_NQ),E(_NL)))):new T4(0,(1+_ND|0)+_NF|0,E(_NJ),E(new T4(0,(1+_ND|0)+_NO|0,E(_NP),E(_NC),E(_NK))),E(new T4(0,1+_NM|0,E(_NG),E(_MR),E(_NL))));},_NR=E(_NK);if(!_NR._){return new F(function(){return _NN(_NR.a);});}else{return new F(function(){return _NN(0);});}}else{return new T4(0,(1+_ND|0)+_NF|0,E(_NG),E(new T4(0,(1+_ND|0)+_NI|0,E(_Nz),E(_NC),E(_NH))),E(_NL));}}else{return E(_Nx);}}else{return E(_Nx);}}}else{return new T4(0,1+_ND|0,E(_Nz),E(_NC),E(_MR));}}else{var _NS=E(_NB);if(!_NS._){var _NT=_NS.a,_NU=_NS.b,_NV=_NS.d,_NW=E(_NS.c);if(!_NW._){var _NX=_NW.a,_NY=_NW.b,_NZ=_NW.c,_O0=E(_NV);if(!_O0._){var _O1=_O0.a;if(_NX>=(imul(2,_O1)|0)){var _O2=function(_O3){var _O4=E(_Nz),_O5=E(_NW.d);return (_O5._==0)?new T4(0,1+_NT|0,E(_NY),E(new T4(0,1+_O3|0,E(_O4),E(_MR),E(_NZ))),E(new T4(0,(1+_O1|0)+_O5.a|0,E(_NU),E(_O5),E(_O0)))):new T4(0,1+_NT|0,E(_NY),E(new T4(0,1+_O3|0,E(_O4),E(_MR),E(_NZ))),E(new T4(0,1+_O1|0,E(_NU),E(_MR),E(_O0))));},_O6=E(_NZ);if(!_O6._){return new F(function(){return _O2(_O6.a);});}else{return new F(function(){return _O2(0);});}}else{return new T4(0,1+_NT|0,E(_NU),E(new T4(0,1+_NX|0,E(_Nz),E(_MR),E(_NW))),E(_O0));}}else{return new T4(0,3,E(_NY),E(new T4(0,1,E(_Nz),E(_MR),E(_MR))),E(new T4(0,1,E(_NU),E(_MR),E(_MR))));}}else{var _O7=E(_NV);return (_O7._==0)?new T4(0,3,E(_NU),E(new T4(0,1,E(_Nz),E(_MR),E(_MR))),E(_O7)):new T4(0,2,E(_Nz),E(_MR),E(_NS));}}else{return new T4(0,1,E(_Nz),E(_MR),E(_MR));}}},_O8=function(_O9){return new T4(0,1,E(_O9),E(_MR),E(_MR));},_Oa=function(_Ob,_Oc){var _Od=E(_Oc);if(!_Od._){return new F(function(){return _MW(_Od.b,B(_Oa(_Ob,_Od.c)),_Od.d);});}else{return new F(function(){return _O8(_Ob);});}},_Oe=function(_Of,_Og){var _Oh=E(_Og);if(!_Oh._){return new F(function(){return _Ny(_Oh.b,_Oh.c,B(_Oe(_Of,_Oh.d)));});}else{return new F(function(){return _O8(_Of);});}},_Oi=function(_Oj,_Ok,_Ol,_Om,_On){return new F(function(){return _Ny(_Ol,_Om,B(_Oe(_Oj,_On)));});},_Oo=function(_Op,_Oq,_Or,_Os,_Ot){return new F(function(){return _MW(_Or,B(_Oa(_Op,_Os)),_Ot);});},_Ou=function(_Ov,_Ow,_Ox,_Oy,_Oz,_OA){var _OB=E(_Ow);if(!_OB._){var _OC=_OB.a,_OD=_OB.b,_OE=_OB.c,_OF=_OB.d;if((imul(3,_OC)|0)>=_Ox){if((imul(3,_Ox)|0)>=_OC){return new T4(0,(_OC+_Ox|0)+1|0,E(_Ov),E(_OB),E(new T4(0,_Ox,E(_Oy),E(_Oz),E(_OA))));}else{return new F(function(){return _Ny(_OD,_OE,B(_Ou(_Ov,_OF,_Ox,_Oy,_Oz,_OA)));});}}else{return new F(function(){return _MW(_Oy,B(_OG(_Ov,_OC,_OD,_OE,_OF,_Oz)),_OA);});}}else{return new F(function(){return _Oo(_Ov,_Ox,_Oy,_Oz,_OA);});}},_OG=function(_OH,_OI,_OJ,_OK,_OL,_OM){var _ON=E(_OM);if(!_ON._){var _OO=_ON.a,_OP=_ON.b,_OQ=_ON.c,_OR=_ON.d;if((imul(3,_OI)|0)>=_OO){if((imul(3,_OO)|0)>=_OI){return new T4(0,(_OI+_OO|0)+1|0,E(_OH),E(new T4(0,_OI,E(_OJ),E(_OK),E(_OL))),E(_ON));}else{return new F(function(){return _Ny(_OJ,_OK,B(_Ou(_OH,_OL,_OO,_OP,_OQ,_OR)));});}}else{return new F(function(){return _MW(_OP,B(_OG(_OH,_OI,_OJ,_OK,_OL,_OQ)),_OR);});}}else{return new F(function(){return _Oi(_OH,_OI,_OJ,_OK,_OL);});}},_OS=function(_OT,_OU,_OV){var _OW=E(_OU);if(!_OW._){var _OX=_OW.a,_OY=_OW.b,_OZ=_OW.c,_P0=_OW.d,_P1=E(_OV);if(!_P1._){var _P2=_P1.a,_P3=_P1.b,_P4=_P1.c,_P5=_P1.d;if((imul(3,_OX)|0)>=_P2){if((imul(3,_P2)|0)>=_OX){return new T4(0,(_OX+_P2|0)+1|0,E(_OT),E(_OW),E(_P1));}else{return new F(function(){return _Ny(_OY,_OZ,B(_Ou(_OT,_P0,_P2,_P3,_P4,_P5)));});}}else{return new F(function(){return _MW(_P3,B(_OG(_OT,_OX,_OY,_OZ,_P0,_P4)),_P5);});}}else{return new F(function(){return _Oi(_OT,_OX,_OY,_OZ,_P0);});}}else{return new F(function(){return _Oa(_OT,_OV);});}},_P6=function(_P7,_P8,_P9){var _Pa=E(_P7);if(_Pa==1){return new T2(0,new T(function(){return new T4(0,1,E(_P8),E(_MR),E(_MR));}),_P9);}else{var _Pb=B(_P6(_Pa>>1,_P8,_P9)),_Pc=_Pb.a,_Pd=E(_Pb.b);if(!_Pd._){return new T2(0,_Pc,_4);}else{var _Pe=B(_Pf(_Pa>>1,_Pd.b));return new T2(0,new T(function(){return B(_OS(_Pd.a,_Pc,_Pe.a));}),_Pe.b);}}},_Pf=function(_Pg,_Ph){var _Pi=E(_Ph);if(!_Pi._){return new T2(0,_MR,_4);}else{var _Pj=_Pi.a,_Pk=_Pi.b,_Pl=E(_Pg);if(_Pl==1){return new T2(0,new T(function(){return new T4(0,1,E(_Pj),E(_MR),E(_MR));}),_Pk);}else{var _Pm=B(_P6(_Pl>>1,_Pj,_Pk)),_Pn=_Pm.a,_Po=E(_Pm.b);if(!_Po._){return new T2(0,_Pn,_4);}else{var _Pp=B(_Pf(_Pl>>1,_Po.b));return new T2(0,new T(function(){return B(_OS(_Po.a,_Pn,_Pp.a));}),_Pp.b);}}}},_Pq=function(_Pr,_Ps,_Pt){while(1){var _Pu=E(_Pt);if(!_Pu._){return E(_Ps);}else{var _Pv=B(_Pf(_Pr,_Pu.b)),_Pw=_Pr<<1,_Px=B(_OS(_Pu.a,_Ps,_Pv.a));_Pr=_Pw;_Ps=_Px;_Pt=_Pv.b;continue;}}},_Py=function(_Pz,_PA,_PB,_PC,_PD){var _PE=B(_fo(_PA,_PB,_PC,_PD)),_PF=B(_gl(E(_PE.a)&4294967295,new T(function(){return B(_jR(_Pz));}),new T3(0,_PA,_PB,_PC),_PE.b));return new T2(0,new T(function(){var _PG=E(_PF.a);if(!_PG._){return new T0(1);}else{return B(_Pq(1,new T4(0,1,E(_PG.a),E(_MR),E(_MR)),_PG.b));}}),_PF.b);},_PH=function(_PI,_PJ){var _PK=E(_PI),_PL=B(_Py(_MQ,_PK.a,_PK.b,_PK.c,E(_PJ)));return new T2(0,_PL.a,_PL.b);},_PM=new T2(0,_Md,_PH),_PN=function(_PO){return E(_dP);},_PP=function(_PQ,_PR,_PS,_PT){var _PU=B(_fo(_PQ,_PR,_PS,_PT));return new F(function(){return _gl(E(_PU.a)&4294967295,_kv,new T3(0,_PQ,_PR,_PS),_PU.b);});},_PV=function(_PW,_PX){var _PY=E(_PW),_PZ=B(_PP(_PY.a,_PY.b,_PY.c,E(_PX)));return new T2(0,_PZ.a,_PZ.b);},_Q0=new T2(0,_PN,_PV),_Q1=new T0(1),_Q2=function(_Q3,_Q4,_Q5,_Q6,_Q7,_Q8,_Q9){while(1){var _Qa=E(_Q9);if(!_Qa._){var _Qb=(_Q7>>>0^_Qa.a>>>0)>>>0,_Qc=(_Qb|_Qb>>>1)>>>0,_Qd=(_Qc|_Qc>>>2)>>>0,_Qe=(_Qd|_Qd>>>4)>>>0,_Qf=(_Qe|_Qe>>>8)>>>0,_Qg=(_Qf|_Qf>>>16)>>>0,_Qh=(_Qg^_Qg>>>1)>>>0&4294967295;if(_Q6>>>0<=_Qh>>>0){return new F(function(){return _Qi(_Q3,_Q4,_Q5,new T3(0,_Q7,E(_Q8),E(_Qa)));});}else{var _Qj=_Qh>>>0,_Qk=(_Q7>>>0&((_Qj-1>>>0^4294967295)>>>0^_Qj)>>>0)>>>0&4294967295,_Ql=new T4(0,_Qk,_Qh,E(_Qa.b),E(_Q8));_Q7=_Qk;_Q8=_Ql;_Q9=_Qa.c;continue;}}else{return new F(function(){return _Qi(_Q3,_Q4,_Q5,new T3(0,_Q7,E(_Q8),E(_Q1)));});}}},_Qm=function(_Qn,_Qo,_Qp){while(1){var _Qq=E(_Qp);if(!_Qq._){var _Qr=_Qq.a,_Qs=_Qq.b,_Qt=_Qq.c,_Qu=(_Qr>>>0^_Qn>>>0)>>>0,_Qv=(_Qu|_Qu>>>1)>>>0,_Qw=(_Qv|_Qv>>>2)>>>0,_Qx=(_Qw|_Qw>>>4)>>>0,_Qy=(_Qx|_Qx>>>8)>>>0,_Qz=(_Qy|_Qy>>>16)>>>0,_QA=(_Qz^_Qz>>>1)>>>0&4294967295,_QB=(_Qn>>>0^_Qr>>>0)>>>0,_QC=(_QB|_QB>>>1)>>>0,_QD=(_QC|_QC>>>2)>>>0,_QE=(_QD|_QD>>>4)>>>0,_QF=(_QE|_QE>>>8)>>>0,_QG=(_QF|_QF>>>16)>>>0,_QH=(_QG^_QG>>>1)>>>0;if(!((_Qr>>>0&_QA>>>0)>>>0)){var _QI=_QA>>>0,_QJ=(_Qn>>>0&((_QH-1>>>0^4294967295)>>>0^_QH)>>>0)>>>0&4294967295,_QK=new T4(0,(_Qr>>>0&((_QI-1>>>0^4294967295)>>>0^_QI)>>>0)>>>0&4294967295,_QA,E(_Qs),E(_Qo));_Qn=_QJ;_Qo=_QK;_Qp=_Qt;continue;}else{var _QL=_QA>>>0,_QJ=(_Qn>>>0&((_QH-1>>>0^4294967295)>>>0^_QH)>>>0)>>>0&4294967295,_QK=new T4(0,(_Qr>>>0&((_QL-1>>>0^4294967295)>>>0^_QL)>>>0)>>>0&4294967295,_QA,E(_Qo),E(_Qs));_Qn=_QJ;_Qo=_QK;_Qp=_Qt;continue;}}else{return E(_Qo);}}},_Qi=function(_QM,_QN,_QO,_QP){var _QQ=E(_QO);if(!_QQ._){return new F(function(){return _Qm(_QM,new T2(1,_QM,_QN),_QP);});}else{var _QR=E(_QQ.a),_QS=E(_QR.a),_QT=(_QM>>>0^_QS>>>0)>>>0,_QU=(_QT|_QT>>>1)>>>0,_QV=(_QU|_QU>>>2)>>>0,_QW=(_QV|_QV>>>4)>>>0,_QX=(_QW|_QW>>>8)>>>0,_QY=(_QX|_QX>>>16)>>>0;return new F(function(){return _Q2(_QS,_QR.b,_QQ.b,(_QY^_QY>>>1)>>>0&4294967295,_QM,new T2(1,_QM,_QN),_QP);});}},_QZ=function(_R0,_R1,_R2,_R3,_R4){var _R5=B(_fo(_R1,_R2,_R3,_R4)),_R6=function(_R7,_R8){var _R9=E(_R7),_Ra=B(_fo(_R9.a,_R9.b,_R9.c,E(_R8))),_Rb=B(A3(_jR,_R0,_R9,_Ra.b));return new T2(0,new T2(0,new T(function(){return E(_Ra.a)&4294967295;}),_Rb.a),_Rb.b);},_Rc=B(_gl(E(_R5.a)&4294967295,_R6,new T3(0,_R1,_R2,_R3),_R5.b));return new T2(0,new T(function(){var _Rd=E(_Rc.a);if(!_Rd._){return new T0(2);}else{var _Re=E(_Rd.a);return B(_Qi(E(_Re.a),_Re.b,_Rd.b,_Q1));}}),_Rc.b);},_Rf=function(_Rg,_Rh,_Ri,_Rj){var _Rk=B(A3(_jR,_Rg,_Ri,_Rj)),_Rl=B(A3(_jR,_Rh,_Ri,_Rk.b));return new T2(0,new T2(0,_Rk.a,_Rl.a),_Rl.b);},_Rm=new T0(1),_Rn=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_Ro=function(_Rp){return new F(function(){return err(_Rn);});},_Rq=new T(function(){return B(_Ro(_));}),_Rr=function(_Rs,_Rt,_Ru,_Rv){var _Rw=E(_Rv);if(!_Rw._){var _Rx=_Rw.a,_Ry=E(_Ru);if(!_Ry._){var _Rz=_Ry.a,_RA=_Ry.b,_RB=_Ry.c;if(_Rz<=(imul(3,_Rx)|0)){return new T5(0,(1+_Rz|0)+_Rx|0,E(_Rs),_Rt,E(_Ry),E(_Rw));}else{var _RC=E(_Ry.d);if(!_RC._){var _RD=_RC.a,_RE=E(_Ry.e);if(!_RE._){var _RF=_RE.a,_RG=_RE.b,_RH=_RE.c,_RI=_RE.d;if(_RF>=(imul(2,_RD)|0)){var _RJ=function(_RK){var _RL=E(_RE.e);return (_RL._==0)?new T5(0,(1+_Rz|0)+_Rx|0,E(_RG),_RH,E(new T5(0,(1+_RD|0)+_RK|0,E(_RA),_RB,E(_RC),E(_RI))),E(new T5(0,(1+_Rx|0)+_RL.a|0,E(_Rs),_Rt,E(_RL),E(_Rw)))):new T5(0,(1+_Rz|0)+_Rx|0,E(_RG),_RH,E(new T5(0,(1+_RD|0)+_RK|0,E(_RA),_RB,E(_RC),E(_RI))),E(new T5(0,1+_Rx|0,E(_Rs),_Rt,E(_Rm),E(_Rw))));},_RM=E(_RI);if(!_RM._){return new F(function(){return _RJ(_RM.a);});}else{return new F(function(){return _RJ(0);});}}else{return new T5(0,(1+_Rz|0)+_Rx|0,E(_RA),_RB,E(_RC),E(new T5(0,(1+_Rx|0)+_RF|0,E(_Rs),_Rt,E(_RE),E(_Rw))));}}else{return E(_Rq);}}else{return E(_Rq);}}}else{return new T5(0,1+_Rx|0,E(_Rs),_Rt,E(_Rm),E(_Rw));}}else{var _RN=E(_Ru);if(!_RN._){var _RO=_RN.a,_RP=_RN.b,_RQ=_RN.c,_RR=_RN.e,_RS=E(_RN.d);if(!_RS._){var _RT=_RS.a,_RU=E(_RR);if(!_RU._){var _RV=_RU.a,_RW=_RU.b,_RX=_RU.c,_RY=_RU.d;if(_RV>=(imul(2,_RT)|0)){var _RZ=function(_S0){var _S1=E(_RU.e);return (_S1._==0)?new T5(0,1+_RO|0,E(_RW),_RX,E(new T5(0,(1+_RT|0)+_S0|0,E(_RP),_RQ,E(_RS),E(_RY))),E(new T5(0,1+_S1.a|0,E(_Rs),_Rt,E(_S1),E(_Rm)))):new T5(0,1+_RO|0,E(_RW),_RX,E(new T5(0,(1+_RT|0)+_S0|0,E(_RP),_RQ,E(_RS),E(_RY))),E(new T5(0,1,E(_Rs),_Rt,E(_Rm),E(_Rm))));},_S2=E(_RY);if(!_S2._){return new F(function(){return _RZ(_S2.a);});}else{return new F(function(){return _RZ(0);});}}else{return new T5(0,1+_RO|0,E(_RP),_RQ,E(_RS),E(new T5(0,1+_RV|0,E(_Rs),_Rt,E(_RU),E(_Rm))));}}else{return new T5(0,3,E(_RP),_RQ,E(_RS),E(new T5(0,1,E(_Rs),_Rt,E(_Rm),E(_Rm))));}}else{var _S3=E(_RR);return (_S3._==0)?new T5(0,3,E(_S3.b),_S3.c,E(new T5(0,1,E(_RP),_RQ,E(_Rm),E(_Rm))),E(new T5(0,1,E(_Rs),_Rt,E(_Rm),E(_Rm)))):new T5(0,2,E(_Rs),_Rt,E(_RN),E(_Rm));}}else{return new T5(0,1,E(_Rs),_Rt,E(_Rm),E(_Rm));}}},_S4=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_S5=function(_S6){return new F(function(){return err(_S4);});},_S7=new T(function(){return B(_S5(_));}),_S8=function(_S9,_Sa,_Sb,_Sc){var _Sd=E(_Sb);if(!_Sd._){var _Se=_Sd.a,_Sf=E(_Sc);if(!_Sf._){var _Sg=_Sf.a,_Sh=_Sf.b,_Si=_Sf.c;if(_Sg<=(imul(3,_Se)|0)){return new T5(0,(1+_Se|0)+_Sg|0,E(_S9),_Sa,E(_Sd),E(_Sf));}else{var _Sj=E(_Sf.d);if(!_Sj._){var _Sk=_Sj.a,_Sl=_Sj.b,_Sm=_Sj.c,_Sn=_Sj.d,_So=E(_Sf.e);if(!_So._){var _Sp=_So.a;if(_Sk>=(imul(2,_Sp)|0)){var _Sq=function(_Sr){var _Ss=E(_S9),_St=E(_Sj.e);return (_St._==0)?new T5(0,(1+_Se|0)+_Sg|0,E(_Sl),_Sm,E(new T5(0,(1+_Se|0)+_Sr|0,E(_Ss),_Sa,E(_Sd),E(_Sn))),E(new T5(0,(1+_Sp|0)+_St.a|0,E(_Sh),_Si,E(_St),E(_So)))):new T5(0,(1+_Se|0)+_Sg|0,E(_Sl),_Sm,E(new T5(0,(1+_Se|0)+_Sr|0,E(_Ss),_Sa,E(_Sd),E(_Sn))),E(new T5(0,1+_Sp|0,E(_Sh),_Si,E(_Rm),E(_So))));},_Su=E(_Sn);if(!_Su._){return new F(function(){return _Sq(_Su.a);});}else{return new F(function(){return _Sq(0);});}}else{return new T5(0,(1+_Se|0)+_Sg|0,E(_Sh),_Si,E(new T5(0,(1+_Se|0)+_Sk|0,E(_S9),_Sa,E(_Sd),E(_Sj))),E(_So));}}else{return E(_S7);}}else{return E(_S7);}}}else{return new T5(0,1+_Se|0,E(_S9),_Sa,E(_Sd),E(_Rm));}}else{var _Sv=E(_Sc);if(!_Sv._){var _Sw=_Sv.a,_Sx=_Sv.b,_Sy=_Sv.c,_Sz=_Sv.e,_SA=E(_Sv.d);if(!_SA._){var _SB=_SA.a,_SC=_SA.b,_SD=_SA.c,_SE=_SA.d,_SF=E(_Sz);if(!_SF._){var _SG=_SF.a;if(_SB>=(imul(2,_SG)|0)){var _SH=function(_SI){var _SJ=E(_S9),_SK=E(_SA.e);return (_SK._==0)?new T5(0,1+_Sw|0,E(_SC),_SD,E(new T5(0,1+_SI|0,E(_SJ),_Sa,E(_Rm),E(_SE))),E(new T5(0,(1+_SG|0)+_SK.a|0,E(_Sx),_Sy,E(_SK),E(_SF)))):new T5(0,1+_Sw|0,E(_SC),_SD,E(new T5(0,1+_SI|0,E(_SJ),_Sa,E(_Rm),E(_SE))),E(new T5(0,1+_SG|0,E(_Sx),_Sy,E(_Rm),E(_SF))));},_SL=E(_SE);if(!_SL._){return new F(function(){return _SH(_SL.a);});}else{return new F(function(){return _SH(0);});}}else{return new T5(0,1+_Sw|0,E(_Sx),_Sy,E(new T5(0,1+_SB|0,E(_S9),_Sa,E(_Rm),E(_SA))),E(_SF));}}else{return new T5(0,3,E(_SC),_SD,E(new T5(0,1,E(_S9),_Sa,E(_Rm),E(_Rm))),E(new T5(0,1,E(_Sx),_Sy,E(_Rm),E(_Rm))));}}else{var _SM=E(_Sz);return (_SM._==0)?new T5(0,3,E(_Sx),_Sy,E(new T5(0,1,E(_S9),_Sa,E(_Rm),E(_Rm))),E(_SM)):new T5(0,2,E(_S9),_Sa,E(_Rm),E(_Sv));}}else{return new T5(0,1,E(_S9),_Sa,E(_Rm),E(_Rm));}}},_SN=function(_SO,_SP){return new T5(0,1,E(_SO),_SP,E(_Rm),E(_Rm));},_SQ=function(_SR,_SS,_ST){var _SU=E(_ST);if(!_SU._){return new F(function(){return _S8(_SU.b,_SU.c,_SU.d,B(_SQ(_SR,_SS,_SU.e)));});}else{return new F(function(){return _SN(_SR,_SS);});}},_SV=function(_SW,_SX,_SY){var _SZ=E(_SY);if(!_SZ._){return new F(function(){return _Rr(_SZ.b,_SZ.c,B(_SV(_SW,_SX,_SZ.d)),_SZ.e);});}else{return new F(function(){return _SN(_SW,_SX);});}},_T0=function(_T1,_T2,_T3,_T4,_T5,_T6,_T7){return new F(function(){return _Rr(_T4,_T5,B(_SV(_T1,_T2,_T6)),_T7);});},_T8=function(_T9,_Ta,_Tb,_Tc,_Td,_Te,_Tf,_Tg){var _Th=E(_Tb);if(!_Th._){var _Ti=_Th.a,_Tj=_Th.b,_Tk=_Th.c,_Tl=_Th.d,_Tm=_Th.e;if((imul(3,_Ti)|0)>=_Tc){if((imul(3,_Tc)|0)>=_Ti){return new T5(0,(_Ti+_Tc|0)+1|0,E(_T9),_Ta,E(_Th),E(new T5(0,_Tc,E(_Td),_Te,E(_Tf),E(_Tg))));}else{return new F(function(){return _S8(_Tj,_Tk,_Tl,B(_T8(_T9,_Ta,_Tm,_Tc,_Td,_Te,_Tf,_Tg)));});}}else{return new F(function(){return _Rr(_Td,_Te,B(_Tn(_T9,_Ta,_Ti,_Tj,_Tk,_Tl,_Tm,_Tf)),_Tg);});}}else{return new F(function(){return _T0(_T9,_Ta,_Tc,_Td,_Te,_Tf,_Tg);});}},_Tn=function(_To,_Tp,_Tq,_Tr,_Ts,_Tt,_Tu,_Tv){var _Tw=E(_Tv);if(!_Tw._){var _Tx=_Tw.a,_Ty=_Tw.b,_Tz=_Tw.c,_TA=_Tw.d,_TB=_Tw.e;if((imul(3,_Tq)|0)>=_Tx){if((imul(3,_Tx)|0)>=_Tq){return new T5(0,(_Tq+_Tx|0)+1|0,E(_To),_Tp,E(new T5(0,_Tq,E(_Tr),_Ts,E(_Tt),E(_Tu))),E(_Tw));}else{return new F(function(){return _S8(_Tr,_Ts,_Tt,B(_T8(_To,_Tp,_Tu,_Tx,_Ty,_Tz,_TA,_TB)));});}}else{return new F(function(){return _Rr(_Ty,_Tz,B(_Tn(_To,_Tp,_Tq,_Tr,_Ts,_Tt,_Tu,_TA)),_TB);});}}else{return new F(function(){return _SQ(_To,_Tp,new T5(0,_Tq,E(_Tr),_Ts,E(_Tt),E(_Tu)));});}},_TC=function(_TD,_TE,_TF,_TG){var _TH=E(_TF);if(!_TH._){var _TI=_TH.a,_TJ=_TH.b,_TK=_TH.c,_TL=_TH.d,_TM=_TH.e,_TN=E(_TG);if(!_TN._){var _TO=_TN.a,_TP=_TN.b,_TQ=_TN.c,_TR=_TN.d,_TS=_TN.e;if((imul(3,_TI)|0)>=_TO){if((imul(3,_TO)|0)>=_TI){return new T5(0,(_TI+_TO|0)+1|0,E(_TD),_TE,E(_TH),E(_TN));}else{return new F(function(){return _S8(_TJ,_TK,_TL,B(_T8(_TD,_TE,_TM,_TO,_TP,_TQ,_TR,_TS)));});}}else{return new F(function(){return _Rr(_TP,_TQ,B(_Tn(_TD,_TE,_TI,_TJ,_TK,_TL,_TM,_TR)),_TS);});}}else{return new F(function(){return _SQ(_TD,_TE,_TH);});}}else{return new F(function(){return _SV(_TD,_TE,_TG);});}},_TT=function(_TU,_TV,_TW){var _TX=E(_TU);if(_TX==1){var _TY=E(_TV);return new T2(0,new T(function(){return new T5(0,1,E(_TY.a),_TY.b,E(_Rm),E(_Rm));}),_TW);}else{var _TZ=B(_TT(_TX>>1,_TV,_TW)),_U0=_TZ.a,_U1=E(_TZ.b);if(!_U1._){return new T2(0,_U0,_4);}else{var _U2=E(_U1.a),_U3=B(_U4(_TX>>1,_U1.b));return new T2(0,new T(function(){return B(_TC(_U2.a,_U2.b,_U0,_U3.a));}),_U3.b);}}},_U4=function(_U5,_U6){var _U7=E(_U6);if(!_U7._){return new T2(0,_Rm,_4);}else{var _U8=_U7.a,_U9=_U7.b,_Ua=E(_U5);if(_Ua==1){var _Ub=E(_U8);return new T2(0,new T(function(){return new T5(0,1,E(_Ub.a),_Ub.b,E(_Rm),E(_Rm));}),_U9);}else{var _Uc=B(_TT(_Ua>>1,_U8,_U9)),_Ud=_Uc.a,_Ue=E(_Uc.b);if(!_Ue._){return new T2(0,_Ud,_4);}else{var _Uf=E(_Ue.a),_Ug=B(_U4(_Ua>>1,_Ue.b));return new T2(0,new T(function(){return B(_TC(_Uf.a,_Uf.b,_Ud,_Ug.a));}),_Ug.b);}}}},_Uh=function(_Ui,_Uj,_Uk){while(1){var _Ul=E(_Uk);if(!_Ul._){return E(_Uj);}else{var _Um=E(_Ul.a),_Un=B(_U4(_Ui,_Ul.b)),_Uo=_Ui<<1,_Up=B(_TC(_Um.a,_Um.b,_Uj,_Un.a));_Ui=_Uo;_Uj=_Up;_Uk=_Un.b;continue;}}},_Uq=function(_Ur,_Us,_Ut,_Uu,_Uv,_Uw){var _Ux=B(_fo(_Ut,_Uu,_Uv,_Uw)),_Uy=B(_gl(E(_Ux.a)&4294967295,function(_Uz,_UA){return new F(function(){return _Rf(_Ur,_Us,_Uz,_UA);});},new T3(0,_Ut,_Uu,_Uv),_Ux.b));return new T2(0,new T(function(){var _UB=E(_Uy.a);if(!_UB._){return new T0(1);}else{var _UC=E(_UB.a);return B(_Uh(1,new T5(0,1,E(_UC.a),_UC.b,E(_Rm),E(_Rm)),_UB.b));}}),_Uy.b);},_UD=new T0(2),_UE=new T0(10),_UF=new T0(5),_UG=new T0(9),_UH=new T0(6),_UI=new T0(7),_UJ=new T0(8),_UK=function(_UL,_UM){var _UN=E(_UL),_UO=B(_fo(_UN.a,_UN.b,_UN.c,E(_UM))),_UP=B(_gl(E(_UO.a)&4294967295,_g9,_UN,_UO.b));return new T2(0,_UP.a,_UP.b);},_UQ=function(_UR,_US){var _UT=E(_UR),_UU=_UT.a,_UV=_UT.b,_UW=_UT.c,_UX=B(_fo(_UU,_UV,_UW,E(_US))),_UY=B(_gl(E(_UX.a)&4294967295,_UZ,_UT,_UX.b)),_V0=B(_fo(_UU,_UV,_UW,E(_UY.b))),_V1=B(_gl(E(_V0.a)&4294967295,_UK,_UT,_V0.b));return new T2(0,new T2(0,_UY.a,_V1.a),_V1.b);},_V2=function(_V3,_V4,_V5,_V6){var _V7=B(_fi(_V3,_V4,_V5,_V6)),_V8=_V7.b;switch(E(_V7.a)){case 0:var _V9=B(_fo(_V3,_V4,_V5,E(_V8))),_Va=B(_fo(_V3,_V4,_V5,E(_V9.b)));return new T2(0,new T(function(){return new T2(0,E(_V9.a)&4294967295,E(_Va.a)&4294967295);}),_Va.b);case 1:var _Vb=B(_fo(_V3,_V4,_V5,E(_V8))),_Vc=B(_fo(_V3,_V4,_V5,E(_Vb.b)));return new T2(0,new T(function(){return new T2(1,E(_Vb.a)&4294967295,E(_Vc.a)&4294967295);}),_Vc.b);case 2:var _Vd=B(_fo(_V3,_V4,_V5,E(_V8))),_Ve=B(_fo(_V3,_V4,_V5,E(_Vd.b)));return new T2(0,new T(function(){return new T2(2,E(_Vd.a)&4294967295,E(_Ve.a)&4294967295);}),_Ve.b);case 3:var _Vf=B(_fo(_V3,_V4,_V5,E(_V8))),_Vg=B(_gl(E(_Vf.a)&4294967295,_g9,new T3(0,_V3,_V4,_V5),_Vf.b));return new T2(0,new T1(3,_Vg.a),_Vg.b);case 4:var _Vh=B(_fo(_V3,_V4,_V5,E(_V8))),_Vi=B(_gl(E(_Vh.a)&4294967295,_UZ,new T3(0,_V3,_V4,_V5),_Vh.b)),_Vj=B(_fo(_V3,_V4,_V5,E(_Vi.b))),_Vk=B(_gl(E(_Vj.a)&4294967295,_UQ,new T3(0,_V3,_V4,_V5),_Vj.b));return new T2(0,new T2(4,_Vi.a,_Vk.a),_Vk.b);case 5:return new T2(0,_UF,_V8);case 6:return new T2(0,_UI,_V8);case 7:return new T2(0,_UH,_V8);case 8:return new T2(0,_UJ,_V8);case 9:return new T2(0,_UG,_V8);case 10:return new T2(0,_UE,_V8);default:return E(_Jy);}},_UZ=function(_Vl,_Vm){var _Vn=E(_Vl),_Vo=B(_V2(_Vn.a,_Vn.b,_Vn.c,E(_Vm)));return new T2(0,_Vo.a,_Vo.b);},_Vp=new T(function(){return B(unCStr("putWord8 not implemented"));}),_Vq=new T(function(){return B(err(_Vp));}),_Vr=function(_Vs){switch(E(_Vs)._){case 0:return E(_dP);case 1:return E(_dP);case 2:return E(_dP);case 3:return E(_dP);case 4:return E(_dP);case 5:return E(_Vq);case 6:return E(_Vq);case 7:return E(_Vq);case 8:return E(_Vq);case 9:return E(_Vq);default:return E(_Vq);}},_Vt=new T2(0,_Vr,_UZ),_Vu=function(_Vv,_Vw){var _Vx=E(_Vv),_Vy=B(_k0(_Vt,_ij,_Vx.a,_Vx.b,_Vx.c,E(_Vw)));return new T2(0,_Vy.a,_Vy.b);},_Vz=new T(function(){return B(unCStr("MArray: undefined array element"));}),_VA=new T(function(){return B(err(_Vz));}),_VB=new T(function(){return B(unCStr("Negative range size"));}),_VC=new T(function(){return B(err(_VB));}),_VD=function(_VE,_VF,_VG,_VH){var _VI=B(_Uq(_fN,_Mc,_VE,_VF,_VG,_VH)),_VJ=B(_Uq(_fN,_gE,_VE,_VF,_VG,E(_VI.b))),_VK=B(_fo(_VE,_VF,_VG,E(_VJ.b))),_VL=E(_VK.a)&4294967295,_VM=B(_jJ(_VL,_Vu,new T3(0,_VE,_VF,_VG),_VK.b)),_VN=B(_k0(_mo,_ij,_VE,_VF,_VG,E(_VM.b))),_VO=B(_QZ(_Q0,_VE,_VF,_VG,E(_VN.b))),_VP=B(_QZ(_Q0,_VE,_VF,_VG,E(_VO.b))),_VQ=B(_QZ(_PM,_VE,_VF,_VG,E(_VP.b))),_VR=B(_Uq(_fN,_ku,_VE,_VF,_VG,E(_VQ.b))),_VS=B(_fo(_VE,_VF,_VG,E(_VR.b))),_VT=new T(function(){var _VU=new T(function(){var _VV=function(_){var _VW=_VL-1|0,_VX=function(_VY){if(_VY>=0){var _VZ=newArr(_VY,_VA),_W0=_VZ,_W1=function(_W2){var _W3=function(_W4,_W5,_){while(1){if(_W4!=_W2){var _W6=E(_W5);if(!_W6._){return _5;}else{var _=_W0[_W4]=_W6.a,_W7=_W4+1|0;_W4=_W7;_W5=_W6.b;continue;}}else{return _5;}}},_W8=B(_W3(0,_VM.a,_));return new T4(0,E(_im),E(_VW),_VY,_W0);};if(0>_VW){return new F(function(){return _W1(0);});}else{var _W9=_VW+1|0;if(_W9>=0){return new F(function(){return _W1(_W9);});}else{return E(_il);}}}else{return E(_VC);}};if(0>_VW){return new F(function(){return _VX(0);});}else{return new F(function(){return _VX(_VW+1|0);});}};return B(_8O(_VV));});return {_:0,a:_VI.a,b:_VJ.a,c:_VN.a,d:_VO.a,e:_VP.a,f:_VU,g:_VQ.a,h:_UD,i:_Rm,j:_VR.a,k:_UD,l:E(_VS.a)&4294967295};});return new T2(0,_VT,_VS.b);},_Wa=function(_Wb,_Wc){var _Wd=E(_Wb),_We=B(_VD(_Wd.a,_Wd.b,_Wd.c,E(_Wc)));return new T2(0,_We.a,_We.b);},_Wf=function(_Wg){return E(_dP);},_Wh=new T2(0,_Wf,_Wa),_Wi=new T2(1,_bX,_4),_Wj=function(_Wk,_Wl){var _Wm=new T(function(){return B(A3(_em,_ec,new T2(1,function(_Wn){return new F(function(){return _bZ(0,_Wl&4294967295,_Wn);});},new T2(1,function(_Wo){return new F(function(){return _bZ(0,E(_Wk)&4294967295,_Wo);});},_4)),_Wi));});return new F(function(){return err(B(unAppCStr("Unsupported PGF version ",new T2(1,_bY,_Wm))));});},_Wp=function(_Wq,_Wr){var _Ws=new T(function(){var _Wt=E(_Wq),_Wu=B(_fi(_Wt.a,_Wt.b,_Wt.c,E(_Wr)));return new T2(0,_Wu.a,_Wu.b);}),_Wv=new T(function(){var _Ww=E(_Wq),_Wx=B(_fi(_Ww.a,_Ww.b,_Ww.c,E(E(_Ws).b)));return new T2(0,_Wx.a,_Wx.b);});return new T2(0,new T(function(){return (E(E(_Ws).a)<<8>>>0&65535|E(E(_Wv).a))>>>0;}),new T(function(){return E(E(_Wv).b);}));},_Wy=function(_Wz){var _WA=E(_Wz);return new T4(0,_WA.a,_WA.b,new T(function(){var _WB=E(_WA.c);if(!_WB._){return __Z;}else{return new T1(1,new T2(0,_WB.a,_4));}}),_WA.d);},_WC=function(_WD){return E(_dP);},_WE=0,_WF=1,_WG=function(_WH,_WI,_WJ,_WK){var _WL=B(_fi(_WH,_WI,_WJ,_WK)),_WM=_WL.b;switch(E(_WL.a)){case 0:var _WN=B(_fi(_WH,_WI,_WJ,E(_WM))),_WO=_WN.b;switch(E(_WN.a)){case 0:var _WP=B(_fz(_WH,_WI,_WJ,E(_WO))),_WQ=B(_WG(_WH,_WI,_WJ,E(_WP.b)));return new T2(0,new T3(0,_WE,_WP.a,_WQ.a),_WQ.b);case 1:var _WR=B(_fz(_WH,_WI,_WJ,E(_WO))),_WS=B(_WG(_WH,_WI,_WJ,E(_WR.b)));return new T2(0,new T3(0,_WF,_WR.a,_WS.a),_WS.b);default:return E(_Jy);}break;case 1:var _WT=B(_WG(_WH,_WI,_WJ,E(_WM))),_WU=B(_WG(_WH,_WI,_WJ,E(_WT.b)));return new T2(0,new T2(1,_WT.a,_WU.a),_WU.b);case 2:var _WV=B(_LU(_WH,_WI,_WJ,E(_WM)));return new T2(0,new T1(2,_WV.a),_WV.b);case 3:var _WW=B(_fo(_WH,_WI,_WJ,E(_WM)));return new T2(0,new T(function(){return new T1(3,E(_WW.a)&4294967295);}),_WW.b);case 4:var _WX=B(_fz(_WH,_WI,_WJ,E(_WM)));return new T2(0,new T1(4,_WX.a),_WX.b);case 5:var _WY=B(_fo(_WH,_WI,_WJ,E(_WM)));return new T2(0,new T(function(){return new T1(5,E(_WY.a)&4294967295);}),_WY.b);case 6:var _WZ=B(_WG(_WH,_WI,_WJ,E(_WM))),_X0=B(_X1(_WH,_WI,_WJ,E(_WZ.b)));return new T2(0,new T2(6,_WZ.a,_X0.a),_X0.b);case 7:var _X2=B(_WG(_WH,_WI,_WJ,E(_WM)));return new T2(0,new T1(7,_X2.a),_X2.b);default:return E(_Jy);}},_X3=function(_X4,_X5){var _X6=E(_X4),_X7=B(_WG(_X6.a,_X6.b,_X6.c,E(_X5)));return new T2(0,_X7.a,_X7.b);},_X8=function(_X9,_Xa){var _Xb=E(_X9),_Xc=_Xb.a,_Xd=_Xb.b,_Xe=_Xb.c,_Xf=B(_fi(_Xc,_Xd,_Xe,E(_Xa))),_Xg=_Xf.b,_Xh=function(_Xi,_Xj){var _Xk=B(_fz(_Xc,_Xd,_Xe,_Xj)),_Xl=B(_X1(_Xc,_Xd,_Xe,E(_Xk.b)));return new T2(0,new T3(0,_Xi,_Xk.a,_Xl.a),_Xl.b);};switch(E(_Xf.a)){case 0:var _Xm=B(_Xh(_WE,E(_Xg)));return new T2(0,_Xm.a,_Xm.b);case 1:var _Xn=B(_Xh(_WF,E(_Xg)));return new T2(0,_Xn.a,_Xn.b);default:return E(_Jy);}},_X1=function(_Xo,_Xp,_Xq,_Xr){var _Xs=B(_fo(_Xo,_Xp,_Xq,_Xr)),_Xt=B(_gl(E(_Xs.a)&4294967295,_X8,new T3(0,_Xo,_Xp,_Xq),_Xs.b)),_Xu=B(_fz(_Xo,_Xp,_Xq,E(_Xt.b))),_Xv=B(_fo(_Xo,_Xp,_Xq,E(_Xu.b))),_Xw=B(_gl(E(_Xv.a)&4294967295,_X3,new T3(0,_Xo,_Xp,_Xq),_Xv.b));return new T2(0,new T3(0,_Xt.a,_Xu.a,_Xw.a),_Xw.b);},_Xx=function(_Xy,_Xz){var _XA=E(_Xy),_XB=_XA.a,_XC=_XA.b,_XD=_XA.c,_XE=B(_fi(_XB,_XC,_XD,E(_Xz))),_XF=_XE.b,_XG=function(_XH,_XI){var _XJ=B(_fz(_XB,_XC,_XD,_XI)),_XK=B(_X1(_XB,_XC,_XD,E(_XJ.b)));return new T2(0,new T3(0,_XH,_XJ.a,_XK.a),_XK.b);};switch(E(_XE.a)){case 0:var _XL=B(_XG(_WE,E(_XF)));return new T2(0,_XL.a,_XL.b);case 1:var _XM=B(_XG(_WF,E(_XF)));return new T2(0,_XM.a,_XM.b);default:return E(_Jy);}},_XN=function(_XO,_XP){var _XQ=B(_J4(_Jz,_LR,_XO,_XP)),_XR=E(_XO),_XS=B(_fz(_XR.a,_XR.b,_XR.c,E(_XQ.b)));return new T2(0,new T2(0,_XQ.a,_XS.a),_XS.b);},_XT=function(_XU,_XV,_XW,_XX){var _XY=B(_fo(_XU,_XV,_XW,_XX)),_XZ=B(_gl(E(_XY.a)&4294967295,_Xx,new T3(0,_XU,_XV,_XW),_XY.b)),_Y0=B(_fo(_XU,_XV,_XW,E(_XZ.b))),_Y1=B(_gl(E(_Y0.a)&4294967295,_XN,new T3(0,_XU,_XV,_XW),_Y0.b)),_Y2=B(_J4(_Jz,_LR,new T3(0,_XU,_XV,_XW),_Y1.b));return new T2(0,new T3(0,_XZ.a,_Y1.a,_Y2.a),_Y2.b);},_Y3=function(_Y4,_Y5){var _Y6=E(_Y4),_Y7=B(_XT(_Y6.a,_Y6.b,_Y6.c,E(_Y5)));return new T2(0,_Y7.a,_Y7.b);},_Y8=new T2(0,_WC,_Y3),_Y9=function(_Ya){return E(_dP);},_Yb=new T0(4),_Yc=function(_Yd,_Ye,_Yf){switch(E(_Yd)){case 0:var _Yg=E(_Ye),_Yh=_Yg.a,_Yi=_Yg.b,_Yj=_Yg.c,_Yk=B(_fz(_Yh,_Yi,_Yj,E(_Yf))),_Yl=B(_fo(_Yh,_Yi,_Yj,E(_Yk.b))),_Ym=B(_gl(E(_Yl.a)&4294967295,_Yn,_Yg,_Yl.b));return new T2(0,new T2(0,_Yk.a,_Ym.a),_Ym.b);case 1:var _Yo=E(_Ye),_Yp=B(_fz(_Yo.a,_Yo.b,_Yo.c,E(_Yf)));return new T2(0,new T1(2,_Yp.a),_Yp.b);case 2:var _Yq=E(_Ye),_Yr=_Yq.a,_Ys=_Yq.b,_Yt=_Yq.c,_Yu=B(_fz(_Yr,_Ys,_Yt,E(_Yf))),_Yv=B(_fi(_Yr,_Ys,_Yt,E(_Yu.b))),_Yw=B(_Yc(E(_Yv.a),_Yq,_Yv.b));return new T2(0,new T2(3,_Yu.a,_Yw.a),_Yw.b);case 3:return new T2(0,_Yb,_Yf);case 4:var _Yx=E(_Ye),_Yy=B(_LU(_Yx.a,_Yx.b,_Yx.c,E(_Yf)));return new T2(0,new T1(1,_Yy.a),_Yy.b);case 5:var _Yz=E(_Ye),_YA=B(_fi(_Yz.a,_Yz.b,_Yz.c,E(_Yf))),_YB=B(_Yc(E(_YA.a),_Yz,_YA.b));return new T2(0,new T1(5,_YB.a),_YB.b);case 6:var _YC=E(_Ye),_YD=B(_WG(_YC.a,_YC.b,_YC.c,E(_Yf)));return new T2(0,new T1(6,_YD.a),_YD.b);default:return E(_Jy);}},_YE=function(_YF,_YG,_YH,_YI){var _YJ=B(_fi(_YF,_YG,_YH,_YI));return new F(function(){return _Yc(E(_YJ.a),new T3(0,_YF,_YG,_YH),_YJ.b);});},_Yn=function(_YK,_YL){var _YM=E(_YK),_YN=B(_YE(_YM.a,_YM.b,_YM.c,E(_YL)));return new T2(0,_YN.a,_YN.b);},_YO=function(_YP,_YQ,_YR,_YS){var _YT=B(_fo(_YP,_YQ,_YR,_YS)),_YU=B(_gl(E(_YT.a)&4294967295,_Yn,new T3(0,_YP,_YQ,_YR),_YT.b)),_YV=B(_WG(_YP,_YQ,_YR,E(_YU.b)));return new T2(0,new T2(0,_YU.a,_YV.a),_YV.b);},_YW=function(_YX,_YY){var _YZ=E(_YX),_Z0=B(_YO(_YZ.a,_YZ.b,_YZ.c,E(_YY)));return new T2(0,_Z0.a,_Z0.b);},_Z1=function(_Z2,_Z3,_Z4,_Z5){var _Z6=B(_X1(_Z2,_Z3,_Z4,_Z5)),_Z7=_Z6.a,_Z8=B(_fo(_Z2,_Z3,_Z4,E(_Z6.b))),_Z9=_Z8.a,_Za=B(_fi(_Z2,_Z3,_Z4,E(_Z8.b))),_Zb=_Za.b;if(!E(_Za.a)){var _Zc=B(_J4(_Jz,_LR,new T3(0,_Z2,_Z3,_Z4),_Zb));return new T2(0,new T4(0,_Z7,new T(function(){return E(_Z9)&4294967295;}),_4l,_Zc.a),_Zc.b);}else{var _Zd=B(_fo(_Z2,_Z3,_Z4,E(_Zb))),_Ze=B(_gl(E(_Zd.a)&4294967295,_YW,new T3(0,_Z2,_Z3,_Z4),_Zd.b)),_Zf=B(_J4(_Jz,_LR,new T3(0,_Z2,_Z3,_Z4),_Ze.b));return new T2(0,new T4(0,_Z7,new T(function(){return E(_Z9)&4294967295;}),new T1(1,_Ze.a),_Zf.a),_Zf.b);}},_Zg=function(_Zh,_Zi){var _Zj=E(_Zh),_Zk=B(_Z1(_Zj.a,_Zj.b,_Zj.c,E(_Zi)));return new T2(0,_Zk.a,_Zk.b);},_Zl=new T2(0,_Y9,_Zg),_Zm=function(_Zn,_Zo){var _Zp=E(_Zo);return (_Zp._==0)?new T5(0,_Zp.a,E(_Zp.b),new T(function(){return B(A1(_Zn,_Zp.c));}),E(B(_Zm(_Zn,_Zp.d))),E(B(_Zm(_Zn,_Zp.e)))):new T0(1);},_Zq=function(_Zr,_Zs,_Zt,_Zu){var _Zv=B(_Uq(_fN,_Mc,_Zr,_Zs,_Zt,_Zu)),_Zw=B(_Uq(_fN,_Zl,_Zr,_Zs,_Zt,E(_Zv.b))),_Zx=B(_Uq(_fN,_Y8,_Zr,_Zs,_Zt,E(_Zw.b)));return new T2(0,new T3(0,_Zv.a,new T(function(){return B(_Zm(_Wy,_Zw.a));}),_Zx.a),_Zx.b);},_Zy=function(_Zz,_ZA,_ZB){var _ZC=E(_Zz);if(!_ZC._){return new T2(0,_4,_ZB);}else{var _ZD=new T(function(){return B(A2(_ZC.a,_ZA,_ZB));}),_ZE=B(_Zy(_ZC.b,_ZA,new T(function(){return E(E(_ZD).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_ZD).a);}),_ZE.a),_ZE.b);}},_ZF=function(_ZG,_ZH,_ZI,_ZJ){if(0>=_ZG){return new F(function(){return _Zy(_4,_ZI,_ZJ);});}else{var _ZK=function(_ZL){var _ZM=E(_ZL);return (_ZM==1)?E(new T2(1,_ZH,_4)):new T2(1,_ZH,new T(function(){return B(_ZK(_ZM-1|0));}));};return new F(function(){return _Zy(B(_ZK(_ZG)),_ZI,_ZJ);});}},_ZN=function(_ZO,_ZP,_ZQ){var _ZR=new T(function(){var _ZS=E(_ZP),_ZT=B(_fo(_ZS.a,_ZS.b,_ZS.c,E(_ZQ))),_ZU=E(_ZT.a)&4294967295,_ZV=B(_ZF(_ZU,_ZO,_ZS,_ZT.b));return new T2(0,new T2(0,_ZU,_ZV.a),_ZV.b);});return new T2(0,new T(function(){return E(E(E(_ZR).a).b);}),new T(function(){return E(E(_ZR).b);}));},_ZW=function(_ZX,_ZY,_ZZ,_100){var _101=new T(function(){var _102=function(_103,_104){var _105=new T(function(){return B(A2(_ZX,_103,_104));}),_106=B(A2(_ZY,_103,new T(function(){return E(E(_105).b);})));return new T2(0,new T2(0,new T(function(){return E(E(_105).a);}),_106.a),_106.b);},_107=B(_ZN(_102,_ZZ,_100));return new T2(0,_107.a,_107.b);});return new T2(0,new T(function(){var _108=E(E(_101).a);if(!_108._){return new T0(1);}else{var _109=E(_108.a);return B(_Uh(1,new T5(0,1,E(_109.a),_109.b,E(_Rm),E(_Rm)),_108.b));}}),new T(function(){return E(E(_101).b);}));},_10a=new T(function(){return B(unCStr("Prelude.Enum.Bool.toEnum: bad argument"));}),_10b=new T(function(){return B(err(_10a));}),_10c=new T(function(){return B(unCStr(")"));}),_10d=function(_10e){return new F(function(){return err(B(unAppCStr("Unable to read PGF file (",new T(function(){return B(_0(_10e,_10c));}))));});},_10f=new T(function(){return B(unCStr("getLiteral"));}),_10g=new T(function(){return B(_10d(_10f));}),_10h=function(_10i,_10j,_10k,_10l){var _10m=B(_fi(_10i,_10j,_10k,_10l)),_10n=_10m.b;switch(E(_10m.a)){case 0:var _10o=B(_fo(_10i,_10j,_10k,E(_10n))),_10p=B(_gl(E(_10o.a)&4294967295,_g9,new T3(0,_10i,_10j,_10k),_10o.b));return new T2(0,new T1(0,_10p.a),_10p.b);case 1:var _10q=B(_fo(_10i,_10j,_10k,E(_10n)));return new T2(0,new T1(1,new T(function(){return E(_10q.a)&4294967295;})),_10q.b);case 2:var _10r=B(_J4(_Jz,_LR,new T3(0,_10i,_10j,_10k),_10n));return new T2(0,new T1(2,_10r.a),_10r.b);default:return E(_10g);}},_10s=new T(function(){return B(unCStr("getBindType"));}),_10t=new T(function(){return B(_10d(_10s));}),_10u=new T(function(){return B(unCStr("getExpr"));}),_10v=new T(function(){return B(_10d(_10u));}),_10w=function(_10x,_10y,_10z,_10A){var _10B=B(_fi(_10x,_10y,_10z,_10A)),_10C=_10B.b;switch(E(_10B.a)){case 0:var _10D=B(_fi(_10x,_10y,_10z,E(_10C))),_10E=_10D.b;switch(E(_10D.a)){case 0:var _10F=B(_fz(_10x,_10y,_10z,E(_10E))),_10G=B(_10w(_10x,_10y,_10z,E(_10F.b)));return new T2(0,new T3(0,_WE,_10F.a,_10G.a),_10G.b);case 1:var _10H=B(_fz(_10x,_10y,_10z,E(_10E))),_10I=B(_10w(_10x,_10y,_10z,E(_10H.b)));return new T2(0,new T3(0,_WF,_10H.a,_10I.a),_10I.b);default:return E(_10t);}break;case 1:var _10J=B(_10w(_10x,_10y,_10z,E(_10C))),_10K=B(_10w(_10x,_10y,_10z,E(_10J.b)));return new T2(0,new T2(1,_10J.a,_10K.a),_10K.b);case 2:var _10L=B(_10h(_10x,_10y,_10z,E(_10C)));return new T2(0,new T1(2,_10L.a),_10L.b);case 3:var _10M=B(_fo(_10x,_10y,_10z,E(_10C)));return new T2(0,new T(function(){return new T1(3,E(_10M.a)&4294967295);}),_10M.b);case 4:var _10N=B(_fz(_10x,_10y,_10z,E(_10C)));return new T2(0,new T1(4,_10N.a),_10N.b);case 5:var _10O=B(_fo(_10x,_10y,_10z,E(_10C)));return new T2(0,new T(function(){return new T1(5,E(_10O.a)&4294967295);}),_10O.b);case 6:var _10P=B(_10w(_10x,_10y,_10z,E(_10C))),_10Q=B(_10R(_10x,_10y,_10z,_10P.b));return new T2(0,new T2(6,_10P.a,_10Q.a),_10Q.b);case 7:var _10S=B(_10w(_10x,_10y,_10z,E(_10C)));return new T2(0,new T1(7,_10S.a),_10S.b);default:return E(_10v);}},_10T=function(_10U,_10V){var _10W=E(_10U),_10X=B(_10w(_10W.a,_10W.b,_10W.c,E(_10V)));return new T2(0,_10X.a,_10X.b);},_10Y=function(_10Z,_110,_111,_112){var _113=B(_fi(_10Z,_110,_111,_112)),_114=_113.b;switch(E(_113.a)){case 0:var _115=B(_fz(_10Z,_110,_111,E(_114))),_116=B(_10R(_10Z,_110,_111,_115.b));return new T2(0,new T3(0,_WE,_115.a,_116.a),_116.b);case 1:var _117=B(_fz(_10Z,_110,_111,E(_114))),_118=B(_10R(_10Z,_110,_111,_117.b));return new T2(0,new T3(0,_WF,_117.a,_118.a),_118.b);default:return E(_10t);}},_119=function(_11a,_11b){var _11c=E(_11a),_11d=B(_10Y(_11c.a,_11c.b,_11c.c,E(_11b)));return new T2(0,_11d.a,_11d.b);},_10R=function(_11e,_11f,_11g,_11h){var _11i=new T3(0,_11e,_11f,_11g),_11j=B(_ZN(_119,_11i,_11h)),_11k=B(_fz(_11e,_11f,_11g,E(_11j.b))),_11l=B(_ZN(_10T,_11i,_11k.b));return new T2(0,new T3(0,_11j.a,_11k.a,_11l.a),_11l.b);},_11m=new T(function(){return B(unCStr("getPatt"));}),_11n=new T(function(){return B(_10d(_11m));}),_11o=function(_11p,_11q,_11r,_11s){var _11t=B(_fi(_11p,_11q,_11r,_11s)),_11u=_11t.b;switch(E(_11t.a)){case 0:var _11v=B(_fz(_11p,_11q,_11r,E(_11u))),_11w=B(_ZN(_11x,new T3(0,_11p,_11q,_11r),_11v.b));return new T2(0,new T2(0,_11v.a,_11w.a),_11w.b);case 1:var _11y=B(_fz(_11p,_11q,_11r,E(_11u)));return new T2(0,new T1(2,_11y.a),_11y.b);case 2:var _11z=B(_fz(_11p,_11q,_11r,E(_11u))),_11A=B(_11o(_11p,_11q,_11r,E(_11z.b)));return new T2(0,new T2(3,_11z.a,_11A.a),_11A.b);case 3:return new T2(0,_Yb,_11u);case 4:var _11B=B(_10h(_11p,_11q,_11r,E(_11u)));return new T2(0,new T1(1,_11B.a),_11B.b);case 5:var _11C=B(_11o(_11p,_11q,_11r,E(_11u)));return new T2(0,new T1(5,_11C.a),_11C.b);case 6:var _11D=B(_10w(_11p,_11q,_11r,E(_11u)));return new T2(0,new T1(6,_11D.a),_11D.b);default:return E(_11n);}},_11x=function(_11E,_11F){var _11G=E(_11E),_11H=B(_11o(_11G.a,_11G.b,_11G.c,E(_11F)));return new T2(0,_11H.a,_11H.b);},_11I=function(_11J,_11K){var _11L=E(_11J),_11M=B(_ZN(_11x,_11L,_11K)),_11N=B(_10w(_11L.a,_11L.b,_11L.c,E(_11M.b)));return new T2(0,new T2(0,_11M.a,_11N.a),_11N.b);},_11O=function(_11P,_11Q,_11R,_11S){var _11T=B(_10R(_11P,_11Q,_11R,_11S)),_11U=_11T.a,_11V=B(_fo(_11P,_11Q,_11R,E(_11T.b))),_11W=_11V.a,_11X=B(_fi(_11P,_11Q,_11R,E(_11V.b))),_11Y=_11X.b;switch(E(_11X.a)&4294967295){case 0:var _11Z=B(_J4(_Jz,_LR,new T3(0,_11P,_11Q,_11R),_11Y));return new T2(0,new T4(0,_11U,new T(function(){return E(_11W)&4294967295;}),_4l,_11Z.a),_11Z.b);case 1:var _120=new T3(0,_11P,_11Q,_11R),_121=new T(function(){var _122=B(_ZN(_11I,_120,_11Y));return new T2(0,_122.a,_122.b);}),_123=B(_J4(_Jz,_LR,_120,new T(function(){return E(E(_121).b);},1)));return new T2(0,new T4(0,_11U,new T(function(){return E(_11W)&4294967295;}),new T1(1,new T(function(){return E(E(_121).a);})),_123.a),_123.b);default:return E(_10b);}},_124=function(_125,_126){var _127=E(_125),_128=B(_11O(_127.a,_127.b,_127.c,_126));return new T2(0,_128.a,_128.b);},_129=function(_12a,_12b){var _12c=E(_12a),_12d=B(_10h(_12c.a,_12c.b,_12c.c,E(_12b)));return new T2(0,_12d.a,_12d.b);},_12e=function(_12f,_12g){var _12h=E(_12f),_12i=B(_fz(_12h.a,_12h.b,_12h.c,E(_12g)));return new T2(0,_12i.a,_12i.b);},_12j=function(_12k,_12l){while(1){var _12m=E(_12k);if(!_12m._){return (E(_12l)._==0)?1:0;}else{var _12n=E(_12l);if(!_12n._){return 2;}else{var _12o=E(_12m.a),_12p=E(_12n.a);if(_12o!=_12p){return (_12o>_12p)?2:0;}else{_12k=_12m.b;_12l=_12n.b;continue;}}}}},_12q=function(_12r,_12s){return (B(_12j(_12r,_12s))==0)?true:false;},_12t=function(_12u,_12v){return (B(_12j(_12u,_12v))==2)?false:true;},_12w=function(_12x,_12y){return (B(_12j(_12x,_12y))==2)?true:false;},_12z=function(_12A,_12B){return (B(_12j(_12A,_12B))==0)?false:true;},_12C=function(_12D,_12E){return (B(_12j(_12D,_12E))==2)?E(_12D):E(_12E);},_12F=function(_12G,_12H){return (B(_12j(_12G,_12H))==2)?E(_12H):E(_12G);},_12I={_:0,a:_sF,b:_12j,c:_12q,d:_12t,e:_12w,f:_12z,g:_12C,h:_12F},_12J=function(_12K){var _12L=E(_12K)&4294967295;if(_12L>>>0>1114111){return new F(function(){return _fQ(_12L);});}else{return _12L;}},_12M=function(_12N){var _12O=E(_12N);return (_12O._==0)?__Z:new T2(1,new T(function(){return B(_12J(_12O.a));}),new T(function(){return B(_12M(_12O.b));}));},_12P=function(_12Q){var _12R=E(_12Q);return (_12R._==0)?__Z:new T2(1,new T(function(){return B(_12J(_12R.a));}),new T(function(){return B(_12P(_12R.b));}));},_12S=function(_12T,_12U,_12V,_12W,_12X,_12Y){return new F(function(){return _sl(B(_G(_12J,B(_IP(_12T,_12U,_12V)))),B(_G(_12J,B(_IP(_12W,_12X,_12Y)))));});},_12Z=function(_130,_131,_132,_133,_134,_135){return (!B(_12S(_130,_131,_132,_133,_134,_135)))?(B(_12j(B(_12P(new T(function(){return B(_IP(_130,_131,_132));}))),B(_12M(new T(function(){return B(_IP(_133,_134,_135));})))))==2)?2:0:1;},_136=function(_137,_138,_139,_13a,_13b,_13c){var _13d=new T3(0,_138,_139,_13a),_13e=E(_13c);if(!_13e._){var _13f=_13e.c,_13g=_13e.d,_13h=_13e.e,_13i=E(_13e.b);switch(B(_12Z(_138,_139,_13a,_13i.a,_13i.b,_13i.c))){case 0:return new F(function(){return _Rr(_13i,_13f,B(_136(_137,_138,_139,_13a,_13b,_13g)),_13h);});break;case 1:return new T5(0,_13e.a,E(_13d),new T(function(){return B(A3(_137,_13d,_13b,_13f));}),E(_13g),E(_13h));default:return new F(function(){return _S8(_13i,_13f,_13g,B(_136(_137,_138,_139,_13a,_13b,_13h)));});}}else{return new T5(0,1,E(_13d),_13b,E(_Rm),E(_Rm));}},_13j=function(_13k,_13l){var _13m=function(_13n,_13o){while(1){var _13p=E(_13o);if(!_13p._){return E(_13n);}else{var _13q=E(_13p.a),_13r=E(_13q.a),_13s=B(_136(_13k,_13r.a,_13r.b,_13r.c,_13q.b,_13n));_13n=_13s;_13o=_13p.b;continue;}}};return new F(function(){return _13m(_Rm,_13l);});},_13t=function(_13u){return E(E(_13u).b);},_13v=function(_13w,_13x,_13y,_13z){var _13A=E(_13x),_13B=E(_13z);if(!_13B._){var _13C=_13B.b,_13D=_13B.c,_13E=_13B.d,_13F=_13B.e;switch(B(A3(_13t,_13w,_13A,_13C))){case 0:return new F(function(){return _Rr(_13C,_13D,B(_13v(_13w,_13A,_13y,_13E)),_13F);});break;case 1:return new T5(0,_13B.a,E(_13A),_13y,E(_13E),E(_13F));default:return new F(function(){return _S8(_13C,_13D,_13E,B(_13v(_13w,_13A,_13y,_13F)));});}}else{return new T5(0,1,E(_13A),_13y,E(_Rm),E(_Rm));}},_13G=function(_13H,_13I,_13J,_13K){return new F(function(){return _13v(_13H,_13I,_13J,_13K);});},_13L=function(_13M,_13N,_13O,_13P,_13Q){var _13R=E(_13Q),_13S=B(_13T(_13M,_13N,_13O,_13P,_13R.a,_13R.b));return new T2(0,_13S.a,_13S.b);},_13U=function(_13V,_13W,_13X){var _13Y=function(_13Z,_140){while(1){var _141=E(_13Z),_142=E(_140);if(!_142._){switch(B(A3(_13t,_13V,_141,_142.b))){case 0:_13Z=_141;_140=_142.d;continue;case 1:return new T1(1,_142.c);default:_13Z=_141;_140=_142.e;continue;}}else{return __Z;}}};return new F(function(){return _13Y(_13W,_13X);});},_143=function(_144,_145){var _146=E(_144);if(!_146._){return new T2(0,new T1(1,_145),_Rm);}else{var _147=new T(function(){return new T5(0,1,E(_146.a),new T(function(){return B(_148(_146.b,_145));}),E(_Rm),E(_Rm));});return new T2(0,_4l,_147);}},_148=function(_149,_14a){var _14b=B(_143(_149,_14a));return new T2(0,_14b.a,_14b.b);},_13T=function(_14c,_14d,_14e,_14f,_14g,_14h){var _14i=E(_14e);if(!_14i._){var _14j=E(_14g);return (_14j._==0)?new T2(0,new T1(1,_14f),_14h):new T2(0,new T1(1,new T(function(){return B(A2(_14d,_14f,_14j.a));})),_14h);}else{var _14k=_14i.a,_14l=_14i.b,_14m=B(_13U(_14c,_14k,_14h));if(!_14m._){var _14n=new T(function(){return B(_13G(_14c,_14k,new T(function(){return B(_148(_14l,_14f));}),_14h));});return new T2(0,_14g,_14n);}else{var _14o=new T(function(){return B(_13G(_14c,_14k,new T(function(){return B(_13L(_14c,_14d,_14l,_14f,_14m.a));}),_14h));});return new T2(0,_14g,_14o);}}},_14p=function(_14q,_14r,_14s){var _14t=function(_14u,_14v,_14w){while(1){var _14x=E(_14u);if(!_14x._){return new T2(0,_14v,_14w);}else{var _14y=E(_14x.a),_14z=B(_13T(_14q,_14r,_14y.a,_14y.b,_14v,_14w));_14u=_14x.b;_14v=_14z.a;_14w=_14z.b;continue;}}};return new F(function(){return _14t(_14s,_4l,_Rm);});},_14A=function(_14B,_14C,_14D){var _14E=E(_14D);switch(_14E._){case 0:var _14F=_14E.a,_14G=_14E.b,_14H=_14E.c,_14I=_14E.d,_14J=_14G>>>0;if(((_14B>>>0&((_14J-1>>>0^4294967295)>>>0^_14J)>>>0)>>>0&4294967295)==_14F){return ((_14B>>>0&_14J)>>>0==0)?new T4(0,_14F,_14G,E(B(_14A(_14B,_14C,_14H))),E(_14I)):new T4(0,_14F,_14G,E(_14H),E(B(_14A(_14B,_14C,_14I))));}else{var _14K=(_14B>>>0^_14F>>>0)>>>0,_14L=(_14K|_14K>>>1)>>>0,_14M=(_14L|_14L>>>2)>>>0,_14N=(_14M|_14M>>>4)>>>0,_14O=(_14N|_14N>>>8)>>>0,_14P=(_14O|_14O>>>16)>>>0,_14Q=(_14P^_14P>>>1)>>>0&4294967295,_14R=_14Q>>>0;return ((_14B>>>0&_14R)>>>0==0)?new T4(0,(_14B>>>0&((_14R-1>>>0^4294967295)>>>0^_14R)>>>0)>>>0&4294967295,_14Q,E(new T2(1,_14B,_14C)),E(_14E)):new T4(0,(_14B>>>0&((_14R-1>>>0^4294967295)>>>0^_14R)>>>0)>>>0&4294967295,_14Q,E(_14E),E(new T2(1,_14B,_14C)));}break;case 1:var _14S=_14E.a;if(_14B!=_14S){var _14T=(_14B>>>0^_14S>>>0)>>>0,_14U=(_14T|_14T>>>1)>>>0,_14V=(_14U|_14U>>>2)>>>0,_14W=(_14V|_14V>>>4)>>>0,_14X=(_14W|_14W>>>8)>>>0,_14Y=(_14X|_14X>>>16)>>>0,_14Z=(_14Y^_14Y>>>1)>>>0&4294967295,_150=_14Z>>>0;return ((_14B>>>0&_150)>>>0==0)?new T4(0,(_14B>>>0&((_150-1>>>0^4294967295)>>>0^_150)>>>0)>>>0&4294967295,_14Z,E(new T2(1,_14B,_14C)),E(_14E)):new T4(0,(_14B>>>0&((_150-1>>>0^4294967295)>>>0^_150)>>>0)>>>0&4294967295,_14Z,E(_14E),E(new T2(1,_14B,_14C)));}else{return new T2(1,_14B,_14C);}break;default:return new T2(1,_14B,_14C);}},_151=function(_152,_153){var _154=function(_155){while(1){var _156=E(_155);switch(_156._){case 0:var _157=_156.b>>>0;if(((_152>>>0&((_157-1>>>0^4294967295)>>>0^_157)>>>0)>>>0&4294967295)==_156.a){if(!((_152>>>0&_157)>>>0)){_155=_156.c;continue;}else{_155=_156.d;continue;}}else{return __Z;}break;case 1:return (_152!=_156.a)?__Z:new T1(1,_156.b);default:return __Z;}}};return new F(function(){return _154(_153);});},_158=function(_159,_15a,_15b,_15c){var _15d=E(_15c);if(!_15d._){var _15e=new T(function(){var _15f=B(_158(_15d.a,_15d.b,_15d.c,_15d.d));return new T2(0,_15f.a,_15f.b);});return new T2(0,new T(function(){return E(E(_15e).a);}),new T(function(){return B(_MW(_15a,_15b,E(_15e).b));}));}else{return new T2(0,_15a,_15b);}},_15g=function(_15h,_15i,_15j,_15k){var _15l=E(_15j);if(!_15l._){var _15m=new T(function(){var _15n=B(_15g(_15l.a,_15l.b,_15l.c,_15l.d));return new T2(0,_15n.a,_15n.b);});return new T2(0,new T(function(){return E(E(_15m).a);}),new T(function(){return B(_Ny(_15i,E(_15m).b,_15k));}));}else{return new T2(0,_15i,_15k);}},_15o=function(_15p,_15q){var _15r=E(_15p);if(!_15r._){var _15s=_15r.a,_15t=E(_15q);if(!_15t._){var _15u=_15t.a;if(_15s<=_15u){var _15v=B(_15g(_15u,_15t.b,_15t.c,_15t.d));return new F(function(){return _MW(_15v.a,_15r,_15v.b);});}else{var _15w=B(_158(_15s,_15r.b,_15r.c,_15r.d));return new F(function(){return _Ny(_15w.a,_15w.b,_15t);});}}else{return E(_15r);}}else{return E(_15q);}},_15x=function(_15y,_15z,_15A,_15B,_15C){var _15D=E(_15y);if(!_15D._){var _15E=_15D.a,_15F=_15D.b,_15G=_15D.c,_15H=_15D.d;if((imul(3,_15E)|0)>=_15z){if((imul(3,_15z)|0)>=_15E){return new F(function(){return _15o(_15D,new T4(0,_15z,E(_15A),E(_15B),E(_15C)));});}else{return new F(function(){return _Ny(_15F,_15G,B(_15x(_15H,_15z,_15A,_15B,_15C)));});}}else{return new F(function(){return _MW(_15A,B(_15I(_15E,_15F,_15G,_15H,_15B)),_15C);});}}else{return new T4(0,_15z,E(_15A),E(_15B),E(_15C));}},_15I=function(_15J,_15K,_15L,_15M,_15N){var _15O=E(_15N);if(!_15O._){var _15P=_15O.a,_15Q=_15O.b,_15R=_15O.c,_15S=_15O.d;if((imul(3,_15J)|0)>=_15P){if((imul(3,_15P)|0)>=_15J){return new F(function(){return _15o(new T4(0,_15J,E(_15K),E(_15L),E(_15M)),_15O);});}else{return new F(function(){return _Ny(_15K,_15L,B(_15x(_15M,_15P,_15Q,_15R,_15S)));});}}else{return new F(function(){return _MW(_15Q,B(_15I(_15J,_15K,_15L,_15M,_15R)),_15S);});}}else{return new T4(0,_15J,E(_15K),E(_15L),E(_15M));}},_15T=function(_15U,_15V){var _15W=E(_15U);if(!_15W._){var _15X=_15W.a,_15Y=_15W.b,_15Z=_15W.c,_160=_15W.d,_161=E(_15V);if(!_161._){var _162=_161.a,_163=_161.b,_164=_161.c,_165=_161.d;if((imul(3,_15X)|0)>=_162){if((imul(3,_162)|0)>=_15X){return new F(function(){return _15o(_15W,_161);});}else{return new F(function(){return _Ny(_15Y,_15Z,B(_15x(_160,_162,_163,_164,_165)));});}}else{return new F(function(){return _MW(_163,B(_15I(_15X,_15Y,_15Z,_160,_164)),_165);});}}else{return E(_15W);}}else{return E(_15V);}},_166=function(_167,_168){var _169=E(_168);if(!_169._){var _16a=_169.b,_16b=B(_166(_167,_169.c)),_16c=_16b.a,_16d=_16b.b,_16e=B(_166(_167,_169.d)),_16f=_16e.a,_16g=_16e.b;return (!B(A1(_167,_16a)))?new T2(0,B(_15T(_16c,_16f)),B(_OS(_16a,_16d,_16g))):new T2(0,B(_OS(_16a,_16c,_16f)),B(_15T(_16d,_16g)));}else{return new T2(0,_MR,_MR);}},_16h=function(_16i,_16j,_16k,_16l){var _16m=E(_16k),_16n=B(_16o(_16i,_16j,_16m.a,_16m.b,_16l));return new T2(0,_16n.a,_16n.b);},_16p=function(_16q,_16r,_16s){while(1){var _16t=E(_16s);if(!_16t._){var _16u=_16t.e;switch(B(A3(_13t,_16q,_16r,_16t.b))){case 0:return new T2(0,B(_13U(_16q,_16r,_16t.d)),_16t);case 1:return new T2(0,new T1(1,_16t.c),_16u);default:_16s=_16u;continue;}}else{return new T2(0,_4l,_Rm);}}},_16v=function(_16w){return E(E(_16w).f);},_16x=function(_16y,_16z,_16A){while(1){var _16B=E(_16A);if(!_16B._){if(!B(A3(_16v,_16y,_16B.b,_16z))){return E(_16B);}else{_16A=_16B.d;continue;}}else{return new T0(1);}}},_16C=function(_16D,_16E,_16F,_16G){while(1){var _16H=E(_16G);if(!_16H._){var _16I=_16H.b,_16J=_16H.d,_16K=_16H.e;switch(B(A3(_13t,_16D,_16E,_16I))){case 0:if(!B(A3(_pQ,_16D,_16I,_16F))){_16G=_16J;continue;}else{return new T2(0,B(_13U(_16D,_16E,_16J)),_16H);}break;case 1:return new T2(0,new T1(1,_16H.c),B(_16x(_16D,_16F,_16K)));default:_16G=_16K;continue;}}else{return new T2(0,_4l,_Rm);}}},_16L=function(_16M,_16N,_16O,_16P){var _16Q=E(_16O);if(!_16Q._){return new F(function(){return _16p(_16M,_16N,_16P);});}else{return new F(function(){return _16C(_16M,_16N,_16Q.a,_16P);});}},_16R=__Z,_16S=function(_16T,_16U,_16V){var _16W=E(_16U);if(!_16W._){return E(_16V);}else{var _16X=function(_16Y,_16Z){while(1){var _170=E(_16Z);if(!_170._){var _171=_170.b,_172=_170.e;switch(B(A3(_13t,_16T,_16Y,_171))){case 0:return new F(function(){return _TC(_171,_170.c,B(_16X(_16Y,_170.d)),_172);});break;case 1:return E(_172);default:_16Z=_172;continue;}}else{return new T0(1);}}};return new F(function(){return _16X(_16W.a,_16V);});}},_173=function(_174,_175,_176){var _177=E(_175);if(!_177._){return E(_176);}else{var _178=function(_179,_17a){while(1){var _17b=E(_17a);if(!_17b._){var _17c=_17b.b,_17d=_17b.d;switch(B(A3(_13t,_174,_17c,_179))){case 0:return new F(function(){return _TC(_17c,_17b.c,_17d,B(_178(_179,_17b.e)));});break;case 1:return E(_17d);default:_17a=_17d;continue;}}else{return new T0(1);}}};return new F(function(){return _178(_177.a,_176);});}},_17e=function(_17f){return E(E(_17f).d);},_17g=function(_17h,_17i,_17j,_17k){var _17l=E(_17i);if(!_17l._){var _17m=E(_17j);if(!_17m._){return E(_17k);}else{var _17n=function(_17o,_17p){while(1){var _17q=E(_17p);if(!_17q._){if(!B(A3(_16v,_17h,_17q.b,_17o))){return E(_17q);}else{_17p=_17q.d;continue;}}else{return new T0(1);}}};return new F(function(){return _17n(_17m.a,_17k);});}}else{var _17r=_17l.a,_17s=E(_17j);if(!_17s._){var _17t=function(_17u,_17v){while(1){var _17w=E(_17v);if(!_17w._){if(!B(A3(_17e,_17h,_17w.b,_17u))){return E(_17w);}else{_17v=_17w.e;continue;}}else{return new T0(1);}}};return new F(function(){return _17t(_17r,_17k);});}else{var _17x=function(_17y,_17z,_17A){while(1){var _17B=E(_17A);if(!_17B._){var _17C=_17B.b;if(!B(A3(_17e,_17h,_17C,_17y))){if(!B(A3(_16v,_17h,_17C,_17z))){return E(_17B);}else{_17A=_17B.d;continue;}}else{_17A=_17B.e;continue;}}else{return new T0(1);}}};return new F(function(){return _17x(_17r,_17s.a,_17k);});}}},_17D=function(_17E,_17F,_17G,_17H){var _17I=E(_17G);if(!_17I._){var _17J=E(_17H);if(!_17J._){var _17K=function(_17L,_17M,_17N,_17O){var _17P=E(_17O);if(!_17P._){var _17Q=E(_17N);if(!_17Q._){var _17R=_17Q.b,_17S=_17Q.c,_17T=_17Q.e,_17U=B(_16L(_17E,_17R,_17M,_17P)),_17V=_17U.b,_17W=new T1(1,E(_17R)),_17X=B(_17K(_17L,_17W,_17Q.d,B(_17g(_17E,_17L,_17W,_17P)))),_17Y=E(_17U.a);if(!_17Y._){return new F(function(){return _TC(_17R,_17S,_17X,B(_17K(_17W,_17M,_17T,_17V)));});}else{return new F(function(){return _TC(_17R,new T(function(){return B(A3(_17F,_17R,_17S,_17Y.a));}),_17X,B(_17K(_17W,_17M,_17T,_17V)));});}}else{return new F(function(){return _TC(_17P.b,_17P.c,B(_16S(_17E,_17L,_17P.d)),B(_173(_17E,_17M,_17P.e)));});}}else{return E(_17N);}},_17Z=_16R,_180=_16R,_181=_17I.a,_182=_17I.b,_183=_17I.c,_184=_17I.d,_185=_17I.e,_186=_17J.a,_187=_17J.b,_188=_17J.c,_189=_17J.d,_18a=_17J.e,_18b=B(_16L(_17E,_182,_180,new T5(0,_186,E(_187),_188,E(_189),E(_18a)))),_18c=_18b.b,_18d=new T1(1,E(_182)),_18e=B(_17K(_17Z,_18d,_184,B(_17g(_17E,_17Z,_18d,new T5(0,_186,E(_187),_188,E(_189),E(_18a)))))),_18f=E(_18b.a);if(!_18f._){return new F(function(){return _TC(_182,_183,_18e,B(_17K(_18d,_180,_185,_18c)));});}else{return new F(function(){return _TC(_182,new T(function(){return B(A3(_17F,_182,_183,_18f.a));}),_18e,B(_17K(_18d,_180,_185,_18c)));});}}else{return E(_17I);}}else{return E(_17H);}},_16o=function(_18g,_18h,_18i,_18j,_18k){var _18l=E(_18k),_18m=_18l.a,_18n=new T(function(){return B(_17D(_18g,function(_18o,_18p,_18q){return new F(function(){return _16h(_18g,_18h,_18p,_18q);});},_18j,_18l.b));}),_18r=new T(function(){var _18s=E(_18i);if(!_18s._){return E(_18m);}else{var _18t=E(_18m);if(!_18t._){return E(_18s);}else{return new T1(1,new T(function(){return B(A2(_18h,_18s.a,_18t.a));}));}}});return new T2(0,_18r,_18n);},_18u=function(_18v,_18w,_18x){var _18y=function(_18z,_18A,_18B){while(1){var _18C=E(_18z);if(!_18C._){return new T2(0,_18A,_18B);}else{var _18D=B(_16o(_18v,_18w,_18A,_18B,_18C.a));_18z=_18C.b;_18A=_18D.a;_18B=_18D.b;continue;}}};return new F(function(){return _18y(_18x,_4l,_Rm);});},_18E=new T0(2),_18F=function(_18G,_18H){var _18I=E(_18G),_18J=E(_18H);return new F(function(){return _12S(_18I.a,_18I.b,_18I.c,_18J.a,_18J.b,_18J.c);});},_18K=function(_18L,_18M){return E(_18L)==E(_18M);},_18N=function(_18O,_18P){var _18Q=E(_18O);switch(_18Q._){case 0:var _18R=E(_18P);if(!_18R._){return new F(function(){return _sl(_18Q.a,_18R.a);});}else{return false;}break;case 1:var _18S=E(_18P);if(_18S._==1){return new F(function(){return _j1(_18Q.a,_18S.a);});}else{return false;}break;default:var _18T=E(_18P);if(_18T._==2){return new F(function(){return _18K(_18Q.a,_18T.a);});}else{return false;}}},_18U=function(_18V,_18W,_18X){while(1){var _18Y=E(_18W);if(!_18Y._){return (E(_18X)._==0)?true:false;}else{var _18Z=E(_18X);if(!_18Z._){return false;}else{if(!B(A3(_pS,_18V,_18Y.a,_18Z.a))){return false;}else{_18W=_18Y.b;_18X=_18Z.b;continue;}}}}},_190=function(_191,_192){return (!B(_193(_191,_192)))?true:false;},_194=new T2(0,_193,_190),_195=new T(function(){return E(_194);}),_196=function(_197,_198){return (E(_197)==0)?(E(_198)==0)?false:true:(E(_198)==0)?true:false;},_199=function(_19a,_19b){return (E(_19a)==0)?(E(_19b)==0)?true:false:(E(_19b)==0)?false:true;},_19c=new T2(0,_199,_196),_19d=new T(function(){return E(_19c);}),_19e=function(_19f,_19g,_19h,_19i,_19j,_19k){if(!B(A3(_pS,_19d,_19f,_19i))){return false;}else{var _19l=E(_19g),_19m=E(_19j);if(!B(_12S(_19l.a,_19l.b,_19l.c,_19m.a,_19m.b,_19m.c))){return false;}else{return new F(function(){return _19n(_19h,_19k);});}}},_19o=function(_19p,_19q){var _19r=E(_19p),_19s=E(_19q);return new F(function(){return _19e(_19r.a,_19r.b,_19r.c,_19s.a,_19s.b,_19s.c);});},_19t=function(_19u,_19v,_19w,_19x,_19y,_19z){if(!B(A3(_pS,_19d,_19u,_19x))){return true;}else{var _19A=E(_19v),_19B=E(_19y);if(!B(_12S(_19A.a,_19A.b,_19A.c,_19B.a,_19B.b,_19B.c))){return true;}else{var _19C=E(_19w);return (!B(_19D(_19C.a,_19C.b,_19C.c,_19z)))?true:false;}}},_19E=function(_19F,_19G){var _19H=E(_19F),_19I=E(_19G);return new F(function(){return _19t(_19H.a,_19H.b,_19H.c,_19I.a,_19I.b,_19I.c);});},_19J=new T(function(){return new T2(0,_19o,_19E);}),_19D=function(_19K,_19L,_19M,_19N){var _19O=E(_19N);if(!B(_18U(_19J,_19K,_19O.a))){return false;}else{var _19P=E(_19L),_19Q=E(_19O.b);if(!B(_12S(_19P.a,_19P.b,_19P.c,_19Q.a,_19Q.b,_19Q.c))){return false;}else{return new F(function(){return _18U(_195,_19M,_19O.c);});}}},_19n=function(_19R,_19S){var _19T=E(_19R);return new F(function(){return _19D(_19T.a,_19T.b,_19T.c,_19S);});},_193=function(_19U,_19V){while(1){var _19W=E(_19U);switch(_19W._){case 0:var _19X=_19W.b,_19Y=_19W.c,_19Z=E(_19V);if(!_19Z._){var _1a0=_19Z.a,_1a1=_19Z.b,_1a2=_19Z.c;if(!E(_19W.a)){if(!E(_1a0)){var _1a3=E(_19X),_1a4=E(_1a1);if(!B(_12S(_1a3.a,_1a3.b,_1a3.c,_1a4.a,_1a4.b,_1a4.c))){return false;}else{_19U=_19Y;_19V=_1a2;continue;}}else{return false;}}else{if(!E(_1a0)){return false;}else{var _1a5=E(_19X),_1a6=E(_1a1);if(!B(_12S(_1a5.a,_1a5.b,_1a5.c,_1a6.a,_1a6.b,_1a6.c))){return false;}else{_19U=_19Y;_19V=_1a2;continue;}}}}else{return false;}break;case 1:var _1a7=E(_19V);if(_1a7._==1){if(!B(_193(_19W.a,_1a7.a))){return false;}else{_19U=_19W.b;_19V=_1a7.b;continue;}}else{return false;}break;case 2:var _1a8=E(_19V);if(_1a8._==2){return new F(function(){return _18N(_19W.a,_1a8.a);});}else{return false;}break;case 3:var _1a9=E(_19V);return (_1a9._==3)?_19W.a==_1a9.a:false;case 4:var _1aa=E(_19V);if(_1aa._==4){return new F(function(){return _18F(_19W.a,_1aa.a);});}else{return false;}break;case 5:var _1ab=E(_19V);return (_1ab._==5)?_19W.a==_1ab.a:false;case 6:var _1ac=E(_19V);if(_1ac._==6){if(!B(_193(_19W.a,_1ac.a))){return false;}else{return new F(function(){return _19n(_19W.b,_1ac.b);});}}else{return false;}break;default:var _1ad=E(_19V);if(_1ad._==7){_19U=_19W.a;_19V=_1ad.a;continue;}else{return false;}}}},_1ae=function(_1af,_1ag,_1ah,_1ai){return (_1af!=_1ah)?true:(E(_1ag)!=E(_1ai))?true:false;},_1aj=function(_1ak,_1al){var _1am=E(_1ak),_1an=E(_1al);return new F(function(){return _1ae(E(_1am.a),_1am.b,E(_1an.a),_1an.b);});},_1ao=function(_1ap,_1aq,_1ar,_1as){if(_1ap!=_1ar){return false;}else{return new F(function(){return _j1(_1aq,_1as);});}},_1at=function(_1au,_1av){var _1aw=E(_1au),_1ax=E(_1av);return new F(function(){return _1ao(E(_1aw.a),_1aw.b,E(_1ax.a),_1ax.b);});},_1ay=new T2(0,_1at,_1aj),_1az=function(_1aA,_1aB,_1aC,_1aD){return (!B(_18U(_1ay,_1aA,_1aC)))?true:(_1aB!=_1aD)?true:false;},_1aE=function(_1aF,_1aG){var _1aH=E(_1aF),_1aI=E(_1aG);return new F(function(){return _1az(_1aH.a,_1aH.b,_1aI.a,_1aI.b);});},_1aJ=function(_1aK,_1aL){var _1aM=E(_1aK),_1aN=E(_1aL);return (!B(_18U(_1ay,_1aM.a,_1aN.a)))?false:_1aM.b==_1aN.b;},_1aO=new T2(0,_1aJ,_1aE),_1aP=function(_1aQ,_1aR){while(1){var _1aS=E(_1aQ);if(!_1aS._){return (E(_1aR)._==0)?true:false;}else{var _1aT=E(_1aR);if(!_1aT._){return false;}else{if(!B(_sx(_1aS.a,_1aT.a))){return false;}else{_1aQ=_1aS.b;_1aR=_1aT.b;continue;}}}}},_1aU=function(_1aV,_1aW){var _1aX=E(_1aV);switch(_1aX._){case 0:var _1aY=E(_1aW);if(!_1aY._){if(_1aX.a!=_1aY.a){return false;}else{return new F(function(){return _18U(_1aO,_1aX.b,_1aY.b);});}}else{return false;}break;case 1:var _1aZ=E(_1aW);return (_1aZ._==1)?_1aX.a==_1aZ.a:false;default:var _1b0=E(_1aW);if(_1b0._==2){var _1b1=E(_1aX.a),_1b2=E(_1b0.a);if(!B(_12S(_1b1.a,_1b1.b,_1b1.c,_1b2.a,_1b2.b,_1b2.c))){return false;}else{if(!B(_193(_1aX.b,_1b0.b))){return false;}else{return new F(function(){return _1aP(_1aX.c,_1b0.c);});}}}else{return false;}}},_1b3=function(_1b4,_1b5){return (!B(_1aU(_1b4,_1b5)))?true:false;},_1b6=new T2(0,_1aU,_1b3),_1b7=function(_1b8,_1b9){var _1ba=E(_1b8),_1bb=E(_1b9);return new F(function(){return _12Z(_1ba.a,_1ba.b,_1ba.c,_1bb.a,_1bb.b,_1bb.c);});},_1bc=function(_1bd,_1be){var _1bf=E(_1bd),_1bg=E(_1be);return (_1bf>=_1bg)?(_1bf!=_1bg)?2:1:0;},_1bh=function(_1bi,_1bj){var _1bk=E(_1bi);switch(_1bk._){case 0:var _1bl=E(_1bj);if(!_1bl._){return new F(function(){return _12j(_1bk.a,_1bl.a);});}else{return 0;}break;case 1:var _1bm=E(_1bj);switch(_1bm._){case 0:return 2;case 1:return new F(function(){return _jl(_1bk.a,_1bm.a);});break;default:return 0;}break;default:var _1bn=E(_1bj);if(_1bn._==2){return new F(function(){return _1bc(_1bk.a,_1bn.a);});}else{return 2;}}},_1bo=function(_1bp,_1bq){return (B(_1br(_1bp,_1bq))==0)?true:false;},_1bs=function(_1bt,_1bu){return (B(_1br(_1bt,_1bu))==2)?false:true;},_1bv=function(_1bw,_1bx){return (B(_1br(_1bw,_1bx))==2)?true:false;},_1by=function(_1bz,_1bA){return (B(_1br(_1bz,_1bA))==0)?false:true;},_1bB=function(_1bC,_1bD){return (B(_1br(_1bC,_1bD))==2)?E(_1bC):E(_1bD);},_1bE=function(_1bF,_1bG){return (B(_1br(_1bF,_1bG))==2)?E(_1bG):E(_1bF);},_1bH={_:0,a:_194,b:_1br,c:_1bo,d:_1bs,e:_1bv,f:_1by,g:_1bB,h:_1bE},_1bI=new T(function(){return E(_1bH);}),_1bJ=function(_1bK,_1bL,_1bM){while(1){var _1bN=E(_1bL);if(!_1bN._){return (E(_1bM)._==0)?1:0;}else{var _1bO=E(_1bM);if(!_1bO._){return 2;}else{var _1bP=B(A3(_13t,_1bK,_1bN.a,_1bO.a));if(_1bP==1){_1bL=_1bN.b;_1bM=_1bO.b;continue;}else{return E(_1bP);}}}}},_1bQ=function(_1bR,_1bS,_1bT,_1bU){var _1bV=E(_1bU);switch(B(_1bJ(_1bW,_1bR,_1bV.a))){case 0:return false;case 1:var _1bX=E(_1bS),_1bY=E(_1bV.b);switch(B(_12Z(_1bX.a,_1bX.b,_1bX.c,_1bY.a,_1bY.b,_1bY.c))){case 0:return false;case 1:return (B(_1bJ(_1bI,_1bT,_1bV.c))==0)?false:true;default:return true;}break;default:return true;}},_1bZ=function(_1c0,_1c1){var _1c2=E(_1c0);return new F(function(){return _1bQ(_1c2.a,_1c2.b,_1c2.c,_1c1);});},_1c3=function(_1c4,_1c5){if(!E(_1c4)){return (E(_1c5)==0)?false:true;}else{var _1c6=E(_1c5);return false;}},_1c7=function(_1c8,_1c9){if(!E(_1c8)){var _1ca=E(_1c9);return true;}else{return (E(_1c9)==0)?false:true;}},_1cb=function(_1cc,_1cd){if(!E(_1cc)){var _1ce=E(_1cd);return false;}else{return (E(_1cd)==0)?true:false;}},_1cf=function(_1cg,_1ch){if(!E(_1cg)){return (E(_1ch)==0)?true:false;}else{var _1ci=E(_1ch);return true;}},_1cj=function(_1ck,_1cl){return (E(_1ck)==0)?(E(_1cl)==0)?1:0:(E(_1cl)==0)?2:1;},_1cm=function(_1cn,_1co){if(!E(_1cn)){return E(_1co);}else{var _1cp=E(_1co);return 1;}},_1cq=function(_1cr,_1cs){if(!E(_1cr)){var _1ct=E(_1cs);return 0;}else{return E(_1cs);}},_1cu={_:0,a:_19c,b:_1cj,c:_1c3,d:_1c7,e:_1cb,f:_1cf,g:_1cm,h:_1cq},_1cv=new T(function(){return E(_1cu);}),_1cw=function(_1cx,_1cy,_1cz,_1cA,_1cB,_1cC){switch(B(A3(_13t,_1cv,_1cx,_1cA))){case 0:return false;case 1:var _1cD=E(_1cy),_1cE=E(_1cB);switch(B(_12Z(_1cD.a,_1cD.b,_1cD.c,_1cE.a,_1cE.b,_1cE.c))){case 0:return false;case 1:return new F(function(){return _1bZ(_1cz,_1cC);});break;default:return true;}break;default:return true;}},_1cF=function(_1cG,_1cH){var _1cI=E(_1cG),_1cJ=E(_1cH);return new F(function(){return _1cw(_1cI.a,_1cI.b,_1cI.c,_1cJ.a,_1cJ.b,_1cJ.c);});},_1cK=function(_1cL,_1cM,_1cN,_1cO){var _1cP=E(_1cO);switch(B(_1bJ(_1bW,_1cL,_1cP.a))){case 0:return false;case 1:var _1cQ=E(_1cM),_1cR=E(_1cP.b);switch(B(_12Z(_1cQ.a,_1cQ.b,_1cQ.c,_1cR.a,_1cR.b,_1cR.c))){case 0:return false;case 1:return (B(_1bJ(_1bI,_1cN,_1cP.c))==2)?true:false;default:return true;}break;default:return true;}},_1cS=function(_1cT,_1cU){var _1cV=E(_1cT);return new F(function(){return _1cK(_1cV.a,_1cV.b,_1cV.c,_1cU);});},_1cW=function(_1cX,_1cY,_1cZ,_1d0,_1d1,_1d2){switch(B(A3(_13t,_1cv,_1cX,_1d0))){case 0:return false;case 1:var _1d3=E(_1cY),_1d4=E(_1d1);switch(B(_12Z(_1d3.a,_1d3.b,_1d3.c,_1d4.a,_1d4.b,_1d4.c))){case 0:return false;case 1:return new F(function(){return _1cS(_1cZ,_1d2);});break;default:return true;}break;default:return true;}},_1d5=function(_1d6,_1d7){var _1d8=E(_1d6),_1d9=E(_1d7);return new F(function(){return _1cW(_1d8.a,_1d8.b,_1d8.c,_1d9.a,_1d9.b,_1d9.c);});},_1da=function(_1db,_1dc,_1dd,_1de){var _1df=E(_1de);switch(B(_1bJ(_1bW,_1db,_1df.a))){case 0:return true;case 1:var _1dg=E(_1dc),_1dh=E(_1df.b);switch(B(_12Z(_1dg.a,_1dg.b,_1dg.c,_1dh.a,_1dh.b,_1dh.c))){case 0:return true;case 1:return (B(_1bJ(_1bI,_1dd,_1df.c))==2)?false:true;default:return false;}break;default:return false;}},_1di=function(_1dj,_1dk){var _1dl=E(_1dj);return new F(function(){return _1da(_1dl.a,_1dl.b,_1dl.c,_1dk);});},_1dm=function(_1dn,_1do,_1dp,_1dq,_1dr,_1ds){switch(B(A3(_13t,_1cv,_1dn,_1dq))){case 0:return true;case 1:var _1dt=E(_1do),_1du=E(_1dr);switch(B(_12Z(_1dt.a,_1dt.b,_1dt.c,_1du.a,_1du.b,_1du.c))){case 0:return true;case 1:return new F(function(){return _1di(_1dp,_1ds);});break;default:return false;}break;default:return false;}},_1dv=function(_1dw,_1dx){var _1dy=E(_1dw),_1dz=E(_1dx);return new F(function(){return _1dm(_1dy.a,_1dy.b,_1dy.c,_1dz.a,_1dz.b,_1dz.c);});},_1dA=function(_1dB,_1dC){var _1dD=E(_1dB),_1dE=_1dD.a,_1dF=_1dD.c,_1dG=E(_1dC),_1dH=_1dG.a,_1dI=_1dG.c;switch(B(A3(_13t,_1cv,_1dE,_1dH))){case 0:return E(_1dG);case 1:var _1dJ=E(_1dD.b),_1dK=E(_1dG.b);switch(B(_12Z(_1dJ.a,_1dJ.b,_1dJ.c,_1dK.a,_1dK.b,_1dK.c))){case 0:return new T3(0,_1dH,_1dK,_1dI);case 1:var _1dL=E(_1dF);return (!B(_1da(_1dL.a,_1dL.b,_1dL.c,_1dI)))?new T3(0,_1dE,_1dJ,_1dL):new T3(0,_1dH,_1dK,_1dI);default:return new T3(0,_1dE,_1dJ,_1dF);}break;default:return E(_1dD);}},_1dM=function(_1dN,_1dO){var _1dP=E(_1dN),_1dQ=_1dP.a,_1dR=_1dP.c,_1dS=E(_1dO),_1dT=_1dS.a,_1dU=_1dS.c;switch(B(A3(_13t,_1cv,_1dQ,_1dT))){case 0:return E(_1dP);case 1:var _1dV=E(_1dP.b),_1dW=E(_1dS.b);switch(B(_12Z(_1dV.a,_1dV.b,_1dV.c,_1dW.a,_1dW.b,_1dW.c))){case 0:return new T3(0,_1dQ,_1dV,_1dR);case 1:var _1dX=E(_1dR);return (!B(_1da(_1dX.a,_1dX.b,_1dX.c,_1dU)))?new T3(0,_1dT,_1dW,_1dU):new T3(0,_1dQ,_1dV,_1dX);default:return new T3(0,_1dT,_1dW,_1dU);}break;default:return E(_1dS);}},_1dY=function(_1dZ,_1e0,_1e1,_1e2){var _1e3=E(_1e2);switch(B(_1bJ(_1bW,_1dZ,_1e3.a))){case 0:return true;case 1:var _1e4=E(_1e0),_1e5=E(_1e3.b);switch(B(_12Z(_1e4.a,_1e4.b,_1e4.c,_1e5.a,_1e5.b,_1e5.c))){case 0:return true;case 1:return (B(_1bJ(_1bI,_1e1,_1e3.c))==0)?true:false;default:return false;}break;default:return false;}},_1e6=function(_1e7,_1e8){var _1e9=E(_1e7);return new F(function(){return _1dY(_1e9.a,_1e9.b,_1e9.c,_1e8);});},_1ea=function(_1eb,_1ec,_1ed,_1ee,_1ef,_1eg){switch(B(A3(_13t,_1cv,_1eb,_1ee))){case 0:return true;case 1:var _1eh=E(_1ec),_1ei=E(_1ef);switch(B(_12Z(_1eh.a,_1eh.b,_1eh.c,_1ei.a,_1ei.b,_1ei.c))){case 0:return true;case 1:return new F(function(){return _1e6(_1ed,_1eg);});break;default:return false;}break;default:return false;}},_1ej=function(_1ek,_1el){var _1em=E(_1ek),_1en=E(_1el);return new F(function(){return _1ea(_1em.a,_1em.b,_1em.c,_1en.a,_1en.b,_1en.c);});},_1eo=function(_1ep,_1eq,_1er,_1es,_1et,_1eu){switch(B(A3(_13t,_1cv,_1ep,_1es))){case 0:return 0;case 1:var _1ev=E(_1eq),_1ew=E(_1et);switch(B(_12Z(_1ev.a,_1ev.b,_1ev.c,_1ew.a,_1ew.b,_1ew.c))){case 0:return 0;case 1:return new F(function(){return _1ex(_1er,_1eu);});break;default:return 2;}break;default:return 2;}},_1ey=function(_1ez,_1eA){var _1eB=E(_1ez),_1eC=E(_1eA);return new F(function(){return _1eo(_1eB.a,_1eB.b,_1eB.c,_1eC.a,_1eC.b,_1eC.c);});},_1bW=new T(function(){return {_:0,a:_19J,b:_1ey,c:_1ej,d:_1dv,e:_1d5,f:_1cF,g:_1dA,h:_1dM};}),_1eD=function(_1eE,_1eF,_1eG,_1eH){var _1eI=E(_1eH);switch(B(_1bJ(_1bW,_1eE,_1eI.a))){case 0:return 0;case 1:var _1eJ=E(_1eF),_1eK=E(_1eI.b);switch(B(_12Z(_1eJ.a,_1eJ.b,_1eJ.c,_1eK.a,_1eK.b,_1eK.c))){case 0:return 0;case 1:return new F(function(){return _1bJ(_1bI,_1eG,_1eI.c);});break;default:return 2;}break;default:return 2;}},_1ex=function(_1eL,_1eM){var _1eN=E(_1eL);return new F(function(){return _1eD(_1eN.a,_1eN.b,_1eN.c,_1eM);});},_1br=function(_1eO,_1eP){while(1){var _1eQ=B((function(_1eR,_1eS){var _1eT=E(_1eR);switch(_1eT._){case 0:var _1eU=E(_1eS);if(!_1eU._){var _1eV=_1eU.a,_1eW=function(_1eX){var _1eY=E(_1eT.b),_1eZ=E(_1eU.b);switch(B(_12Z(_1eY.a,_1eY.b,_1eY.c,_1eZ.a,_1eZ.b,_1eZ.c))){case 0:return 0;case 1:return new F(function(){return _1br(_1eT.c,_1eU.c);});break;default:return 2;}};if(!E(_1eT.a)){if(!E(_1eV)){return new F(function(){return _1eW(_);});}else{return 0;}}else{if(!E(_1eV)){return 2;}else{return new F(function(){return _1eW(_);});}}}else{return 0;}break;case 1:var _1f0=E(_1eS);switch(_1f0._){case 0:return 2;case 1:switch(B(_1br(_1eT.a,_1f0.a))){case 0:return 0;case 1:_1eO=_1eT.b;_1eP=_1f0.b;return __continue;default:return 2;}break;default:return 0;}break;case 2:var _1f1=E(_1eS);switch(_1f1._){case 2:return new F(function(){return _1bh(_1eT.a,_1f1.a);});break;case 3:return 0;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 3:var _1f2=E(_1eS);switch(_1f2._){case 3:return new F(function(){return _ji(_1eT.a,_1f2.a);});break;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 4:var _1f3=E(_1eS);switch(_1f3._){case 4:return new F(function(){return _1b7(_1eT.a,_1f3.a);});break;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 5:var _1f4=E(_1eS);switch(_1f4._){case 5:return new F(function(){return _ji(_1eT.a,_1f4.a);});break;case 6:return 0;case 7:return 0;default:return 2;}break;case 6:var _1f5=E(_1eS);switch(_1f5._){case 6:switch(B(_1br(_1eT.a,_1f5.a))){case 0:return 0;case 1:return new F(function(){return _1ex(_1eT.b,_1f5.b);});break;default:return 2;}break;case 7:return 0;default:return 2;}break;default:var _1f6=E(_1eS);if(_1f6._==7){_1eO=_1eT.a;_1eP=_1f6.a;return __continue;}else{return 2;}}})(_1eO,_1eP));if(_1eQ!=__continue){return _1eQ;}}},_1f7=function(_1f8,_1f9,_1fa,_1fb){if(_1f8>=_1fa){if(_1f8!=_1fa){return 2;}else{return new F(function(){return _jl(_1f9,_1fb);});}}else{return 0;}},_1fc=function(_1fd,_1fe){var _1ff=E(_1fd),_1fg=E(_1fe);return new F(function(){return _1f7(E(_1ff.a),_1ff.b,E(_1fg.a),_1fg.b);});},_1fh=function(_1fi,_1fj,_1fk,_1fl){if(_1fi>=_1fk){if(_1fi!=_1fk){return false;}else{return new F(function(){return _jx(_1fj,_1fl);});}}else{return true;}},_1fm=function(_1fn,_1fo){var _1fp=E(_1fn),_1fq=E(_1fo);return new F(function(){return _1fh(E(_1fp.a),_1fp.b,E(_1fq.a),_1fq.b);});},_1fr=function(_1fs,_1ft,_1fu,_1fv){if(_1fs>=_1fu){if(_1fs!=_1fu){return false;}else{return new F(function(){return _ju(_1ft,_1fv);});}}else{return true;}},_1fw=function(_1fx,_1fy){var _1fz=E(_1fx),_1fA=E(_1fy);return new F(function(){return _1fr(E(_1fz.a),_1fz.b,E(_1fA.a),_1fA.b);});},_1fB=function(_1fC,_1fD,_1fE,_1fF){if(_1fC>=_1fE){if(_1fC!=_1fE){return true;}else{return new F(function(){return _jr(_1fD,_1fF);});}}else{return false;}},_1fG=function(_1fH,_1fI){var _1fJ=E(_1fH),_1fK=E(_1fI);return new F(function(){return _1fB(E(_1fJ.a),_1fJ.b,E(_1fK.a),_1fK.b);});},_1fL=function(_1fM,_1fN,_1fO,_1fP){if(_1fM>=_1fO){if(_1fM!=_1fO){return true;}else{return new F(function(){return _jo(_1fN,_1fP);});}}else{return false;}},_1fQ=function(_1fR,_1fS){var _1fT=E(_1fR),_1fU=E(_1fS);return new F(function(){return _1fL(E(_1fT.a),_1fT.b,E(_1fU.a),_1fU.b);});},_1fV=function(_1fW,_1fX){var _1fY=E(_1fW),_1fZ=E(_1fY.a),_1g0=E(_1fX),_1g1=E(_1g0.a);return (_1fZ>=_1g1)?(_1fZ!=_1g1)?E(_1fY):(E(_1fY.b)>E(_1g0.b))?E(_1fY):E(_1g0):E(_1g0);},_1g2=function(_1g3,_1g4){var _1g5=E(_1g3),_1g6=E(_1g5.a),_1g7=E(_1g4),_1g8=E(_1g7.a);return (_1g6>=_1g8)?(_1g6!=_1g8)?E(_1g7):(E(_1g5.b)>E(_1g7.b))?E(_1g7):E(_1g5):E(_1g5);},_1g9={_:0,a:_1ay,b:_1fc,c:_1fm,d:_1fw,e:_1fG,f:_1fQ,g:_1fV,h:_1g2},_1ga=function(_1gb,_1gc,_1gd,_1ge){switch(B(_1bJ(_1g9,_1gb,_1gd))){case 0:return true;case 1:return _1gc<_1ge;default:return false;}},_1gf=function(_1gg,_1gh){var _1gi=E(_1gg),_1gj=E(_1gh);return new F(function(){return _1ga(_1gi.a,_1gi.b,_1gj.a,_1gj.b);});},_1gk=function(_1gl,_1gm,_1gn,_1go){switch(B(_1bJ(_1g9,_1gl,_1gn))){case 0:return true;case 1:return _1gm<=_1go;default:return false;}},_1gp=function(_1gq,_1gr){var _1gs=E(_1gq),_1gt=E(_1gr);return new F(function(){return _1gk(_1gs.a,_1gs.b,_1gt.a,_1gt.b);});},_1gu=function(_1gv,_1gw,_1gx,_1gy){switch(B(_1bJ(_1g9,_1gv,_1gx))){case 0:return false;case 1:return _1gw>_1gy;default:return true;}},_1gz=function(_1gA,_1gB){var _1gC=E(_1gA),_1gD=E(_1gB);return new F(function(){return _1gu(_1gC.a,_1gC.b,_1gD.a,_1gD.b);});},_1gE=function(_1gF,_1gG,_1gH,_1gI){switch(B(_1bJ(_1g9,_1gF,_1gH))){case 0:return false;case 1:return _1gG>=_1gI;default:return true;}},_1gJ=function(_1gK,_1gL){var _1gM=E(_1gK),_1gN=E(_1gL);return new F(function(){return _1gE(_1gM.a,_1gM.b,_1gN.a,_1gN.b);});},_1gO=function(_1gP,_1gQ,_1gR,_1gS){switch(B(_1bJ(_1g9,_1gP,_1gR))){case 0:return 0;case 1:return new F(function(){return _ji(_1gQ,_1gS);});break;default:return 2;}},_1gT=function(_1gU,_1gV){var _1gW=E(_1gU),_1gX=E(_1gV);return new F(function(){return _1gO(_1gW.a,_1gW.b,_1gX.a,_1gX.b);});},_1gY=function(_1gZ,_1h0){var _1h1=E(_1gZ),_1h2=E(_1h0);switch(B(_1bJ(_1g9,_1h1.a,_1h2.a))){case 0:return E(_1h2);case 1:return (_1h1.b>_1h2.b)?E(_1h1):E(_1h2);default:return E(_1h1);}},_1h3=function(_1h4,_1h5){var _1h6=E(_1h4),_1h7=E(_1h5);switch(B(_1bJ(_1g9,_1h6.a,_1h7.a))){case 0:return E(_1h6);case 1:return (_1h6.b>_1h7.b)?E(_1h7):E(_1h6);default:return E(_1h7);}},_1h8={_:0,a:_1aO,b:_1gT,c:_1gf,d:_1gp,e:_1gz,f:_1gJ,g:_1gY,h:_1h3},_1h9=function(_1ha,_1hb){while(1){var _1hc=E(_1ha);if(!_1hc._){return (E(_1hb)._==0)?1:0;}else{var _1hd=E(_1hb);if(!_1hd._){return 2;}else{var _1he=B(_12j(_1hc.a,_1hd.a));if(_1he==1){_1ha=_1hc.b;_1hb=_1hd.b;continue;}else{return E(_1he);}}}}},_1hf=function(_1hg,_1hh){return (B(_1h9(_1hg,_1hh))==0)?true:false;},_1hi=function(_1hj,_1hk){var _1hl=E(_1hj);switch(_1hl._){case 0:var _1hm=_1hl.a,_1hn=E(_1hk);if(!_1hn._){var _1ho=_1hn.a;return (_1hm>=_1ho)?(_1hm!=_1ho)?false:(B(_1bJ(_1h8,_1hl.b,_1hn.b))==0)?true:false:true;}else{return true;}break;case 1:var _1hp=E(_1hk);switch(_1hp._){case 0:return false;case 1:return _1hl.a<_1hp.a;default:return true;}break;default:var _1hq=E(_1hk);if(_1hq._==2){var _1hr=E(_1hl.a),_1hs=E(_1hq.a);switch(B(_12Z(_1hr.a,_1hr.b,_1hr.c,_1hs.a,_1hs.b,_1hs.c))){case 0:return true;case 1:switch(B(_1br(_1hl.b,_1hq.b))){case 0:return true;case 1:return new F(function(){return _1hf(_1hl.c,_1hq.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1ht=function(_1hu,_1hv){return (B(_1h9(_1hu,_1hv))==2)?false:true;},_1hw=function(_1hx,_1hy){var _1hz=E(_1hx);switch(_1hz._){case 0:var _1hA=_1hz.a,_1hB=E(_1hy);if(!_1hB._){var _1hC=_1hB.a;return (_1hA>=_1hC)?(_1hA!=_1hC)?false:(B(_1bJ(_1h8,_1hz.b,_1hB.b))==2)?false:true:true;}else{return true;}break;case 1:var _1hD=E(_1hy);switch(_1hD._){case 0:return false;case 1:return _1hz.a<=_1hD.a;default:return true;}break;default:var _1hE=E(_1hy);if(_1hE._==2){var _1hF=E(_1hz.a),_1hG=E(_1hE.a);switch(B(_12Z(_1hF.a,_1hF.b,_1hF.c,_1hG.a,_1hG.b,_1hG.c))){case 0:return true;case 1:switch(B(_1br(_1hz.b,_1hE.b))){case 0:return true;case 1:return new F(function(){return _1ht(_1hz.c,_1hE.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1hH=function(_1hI,_1hJ){return (B(_1h9(_1hI,_1hJ))==2)?true:false;},_1hK=function(_1hL,_1hM){var _1hN=E(_1hL);switch(_1hN._){case 0:var _1hO=_1hN.a,_1hP=E(_1hM);if(!_1hP._){var _1hQ=_1hP.a;return (_1hO>=_1hQ)?(_1hO!=_1hQ)?true:(B(_1bJ(_1h8,_1hN.b,_1hP.b))==2)?true:false:false;}else{return false;}break;case 1:var _1hR=E(_1hM);switch(_1hR._){case 0:return true;case 1:return _1hN.a>_1hR.a;default:return false;}break;default:var _1hS=E(_1hM);if(_1hS._==2){var _1hT=E(_1hN.a),_1hU=E(_1hS.a);switch(B(_12Z(_1hT.a,_1hT.b,_1hT.c,_1hU.a,_1hU.b,_1hU.c))){case 0:return false;case 1:switch(B(_1br(_1hN.b,_1hS.b))){case 0:return false;case 1:return new F(function(){return _1hH(_1hN.c,_1hS.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1hV=function(_1hW,_1hX){return (B(_1h9(_1hW,_1hX))==0)?false:true;},_1hY=function(_1hZ,_1i0){var _1i1=E(_1hZ);switch(_1i1._){case 0:var _1i2=_1i1.a,_1i3=E(_1i0);if(!_1i3._){var _1i4=_1i3.a;return (_1i2>=_1i4)?(_1i2!=_1i4)?true:(B(_1bJ(_1h8,_1i1.b,_1i3.b))==0)?false:true:false;}else{return false;}break;case 1:var _1i5=E(_1i0);switch(_1i5._){case 0:return true;case 1:return _1i1.a>=_1i5.a;default:return false;}break;default:var _1i6=E(_1i0);if(_1i6._==2){var _1i7=E(_1i1.a),_1i8=E(_1i6.a);switch(B(_12Z(_1i7.a,_1i7.b,_1i7.c,_1i8.a,_1i8.b,_1i8.c))){case 0:return false;case 1:switch(B(_1br(_1i1.b,_1i6.b))){case 0:return false;case 1:return new F(function(){return _1hV(_1i1.c,_1i6.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1i9=function(_1ia,_1ib){var _1ic=E(_1ia);switch(_1ic._){case 0:var _1id=_1ic.a,_1ie=E(_1ib);if(!_1ie._){var _1if=_1ie.a;if(_1id>=_1if){if(_1id!=_1if){return 2;}else{return new F(function(){return _1bJ(_1h8,_1ic.b,_1ie.b);});}}else{return 0;}}else{return 0;}break;case 1:var _1ig=E(_1ib);switch(_1ig._){case 0:return 2;case 1:return new F(function(){return _ji(_1ic.a,_1ig.a);});break;default:return 0;}break;default:var _1ih=E(_1ib);if(_1ih._==2){var _1ii=E(_1ic.a),_1ij=E(_1ih.a);switch(B(_12Z(_1ii.a,_1ii.b,_1ii.c,_1ij.a,_1ij.b,_1ij.c))){case 0:return 0;case 1:switch(B(_1br(_1ic.b,_1ih.b))){case 0:return 0;case 1:return new F(function(){return _1h9(_1ic.c,_1ih.c);});break;default:return 2;}break;default:return 2;}}else{return 2;}}},_1ik=function(_1il,_1im){return (!B(_1hw(_1il,_1im)))?E(_1il):E(_1im);},_1in=function(_1io,_1ip){return (!B(_1hw(_1io,_1ip)))?E(_1ip):E(_1io);},_1iq={_:0,a:_1b6,b:_1i9,c:_1hi,d:_1hw,e:_1hK,f:_1hY,g:_1ik,h:_1in},_1ir=__Z,_1is=function(_1it,_1iu,_1iv){var _1iw=E(_1iu);if(!_1iw._){return E(_1iv);}else{var _1ix=function(_1iy,_1iz){while(1){var _1iA=E(_1iz);if(!_1iA._){var _1iB=_1iA.b,_1iC=_1iA.d;switch(B(A3(_13t,_1it,_1iy,_1iB))){case 0:return new F(function(){return _OS(_1iB,B(_1ix(_1iy,_1iA.c)),_1iC);});break;case 1:return E(_1iC);default:_1iz=_1iC;continue;}}else{return new T0(1);}}};return new F(function(){return _1ix(_1iw.a,_1iv);});}},_1iD=function(_1iE,_1iF,_1iG){var _1iH=E(_1iF);if(!_1iH._){return E(_1iG);}else{var _1iI=function(_1iJ,_1iK){while(1){var _1iL=E(_1iK);if(!_1iL._){var _1iM=_1iL.b,_1iN=_1iL.c;switch(B(A3(_13t,_1iE,_1iM,_1iJ))){case 0:return new F(function(){return _OS(_1iM,_1iN,B(_1iI(_1iJ,_1iL.d)));});break;case 1:return E(_1iN);default:_1iK=_1iN;continue;}}else{return new T0(1);}}};return new F(function(){return _1iI(_1iH.a,_1iG);});}},_1iO=function(_1iP,_1iQ,_1iR){var _1iS=E(_1iQ),_1iT=E(_1iR);if(!_1iT._){var _1iU=_1iT.b,_1iV=_1iT.c,_1iW=_1iT.d;switch(B(A3(_13t,_1iP,_1iS,_1iU))){case 0:return new F(function(){return _MW(_1iU,B(_1iO(_1iP,_1iS,_1iV)),_1iW);});break;case 1:return E(_1iT);default:return new F(function(){return _Ny(_1iU,_1iV,B(_1iO(_1iP,_1iS,_1iW)));});}}else{return new T4(0,1,E(_1iS),E(_MR),E(_MR));}},_1iX=function(_1iY,_1iZ,_1j0){return new F(function(){return _1iO(_1iY,_1iZ,_1j0);});},_1j1=function(_1j2,_1j3,_1j4,_1j5){var _1j6=E(_1j3);if(!_1j6._){var _1j7=E(_1j4);if(!_1j7._){return E(_1j5);}else{var _1j8=function(_1j9,_1ja){while(1){var _1jb=E(_1ja);if(!_1jb._){if(!B(A3(_16v,_1j2,_1jb.b,_1j9))){return E(_1jb);}else{_1ja=_1jb.c;continue;}}else{return new T0(1);}}};return new F(function(){return _1j8(_1j7.a,_1j5);});}}else{var _1jc=_1j6.a,_1jd=E(_1j4);if(!_1jd._){var _1je=function(_1jf,_1jg){while(1){var _1jh=E(_1jg);if(!_1jh._){if(!B(A3(_17e,_1j2,_1jh.b,_1jf))){return E(_1jh);}else{_1jg=_1jh.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1je(_1jc,_1j5);});}else{var _1ji=function(_1jj,_1jk,_1jl){while(1){var _1jm=E(_1jl);if(!_1jm._){var _1jn=_1jm.b;if(!B(A3(_17e,_1j2,_1jn,_1jj))){if(!B(A3(_16v,_1j2,_1jn,_1jk))){return E(_1jm);}else{_1jl=_1jm.c;continue;}}else{_1jl=_1jm.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1ji(_1jc,_1jd.a,_1j5);});}}},_1jo=function(_1jp,_1jq,_1jr,_1js,_1jt){var _1ju=E(_1jt);if(!_1ju._){var _1jv=_1ju.b,_1jw=_1ju.c,_1jx=_1ju.d,_1jy=E(_1js);if(!_1jy._){var _1jz=_1jy.b,_1jA=function(_1jB){var _1jC=new T1(1,E(_1jz));return new F(function(){return _OS(_1jz,B(_1jo(_1jp,_1jq,_1jC,_1jy.c,B(_1j1(_1jp,_1jq,_1jC,_1ju)))),B(_1jo(_1jp,_1jC,_1jr,_1jy.d,B(_1j1(_1jp,_1jC,_1jr,_1ju)))));});};if(!E(_1jw)._){return new F(function(){return _1jA(_);});}else{if(!E(_1jx)._){return new F(function(){return _1jA(_);});}else{return new F(function(){return _1iX(_1jp,_1jv,_1jy);});}}}else{return new F(function(){return _OS(_1jv,B(_1is(_1jp,_1jq,_1jw)),B(_1iD(_1jp,_1jr,_1jx)));});}}else{return E(_1js);}},_1jD=function(_1jE,_1jF,_1jG,_1jH,_1jI,_1jJ,_1jK,_1jL,_1jM,_1jN,_1jO){var _1jP=function(_1jQ){var _1jR=new T1(1,E(_1jI));return new F(function(){return _OS(_1jI,B(_1jo(_1jE,_1jF,_1jR,_1jJ,B(_1j1(_1jE,_1jF,_1jR,new T4(0,_1jL,E(_1jM),E(_1jN),E(_1jO)))))),B(_1jo(_1jE,_1jR,_1jG,_1jK,B(_1j1(_1jE,_1jR,_1jG,new T4(0,_1jL,E(_1jM),E(_1jN),E(_1jO)))))));});};if(!E(_1jN)._){return new F(function(){return _1jP(_);});}else{if(!E(_1jO)._){return new F(function(){return _1jP(_);});}else{return new F(function(){return _1iX(_1jE,_1jM,new T4(0,_1jH,E(_1jI),E(_1jJ),E(_1jK)));});}}},_1jS=function(_1jT,_1jU,_1jV){var _1jW=E(_1jU);if(!_1jW._){var _1jX=E(_1jV);if(!_1jX._){return new F(function(){return _1jD(_1iq,_1ir,_1ir,_1jW.a,_1jW.b,_1jW.c,_1jW.d,_1jX.a,_1jX.b,_1jX.c,_1jX.d);});}else{return E(_1jW);}}else{return E(_1jV);}},_1jY=function(_1jZ,_1k0,_1k1){var _1k2=function(_1k3,_1k4,_1k5,_1k6){var _1k7=E(_1k6);switch(_1k7._){case 0:var _1k8=_1k7.a,_1k9=_1k7.b,_1ka=_1k7.c,_1kb=_1k7.d,_1kc=_1k9>>>0;if(((_1k5>>>0&((_1kc-1>>>0^4294967295)>>>0^_1kc)>>>0)>>>0&4294967295)==_1k8){return ((_1k5>>>0&_1kc)>>>0==0)?new T4(0,_1k8,_1k9,E(B(_1k2(_1k3,_1k4,_1k5,_1ka))),E(_1kb)):new T4(0,_1k8,_1k9,E(_1ka),E(B(_1k2(_1k3,_1k4,_1k5,_1kb))));}else{var _1kd=(_1k5>>>0^_1k8>>>0)>>>0,_1ke=(_1kd|_1kd>>>1)>>>0,_1kf=(_1ke|_1ke>>>2)>>>0,_1kg=(_1kf|_1kf>>>4)>>>0,_1kh=(_1kg|_1kg>>>8)>>>0,_1ki=(_1kh|_1kh>>>16)>>>0,_1kj=(_1ki^_1ki>>>1)>>>0&4294967295,_1kk=_1kj>>>0;return ((_1k5>>>0&_1kk)>>>0==0)?new T4(0,(_1k5>>>0&((_1kk-1>>>0^4294967295)>>>0^_1kk)>>>0)>>>0&4294967295,_1kj,E(new T2(1,_1k3,_1k4)),E(_1k7)):new T4(0,(_1k5>>>0&((_1kk-1>>>0^4294967295)>>>0^_1kk)>>>0)>>>0&4294967295,_1kj,E(_1k7),E(new T2(1,_1k3,_1k4)));}break;case 1:var _1kl=_1k7.a;if(_1k5!=_1kl){var _1km=(_1k5>>>0^_1kl>>>0)>>>0,_1kn=(_1km|_1km>>>1)>>>0,_1ko=(_1kn|_1kn>>>2)>>>0,_1kp=(_1ko|_1ko>>>4)>>>0,_1kq=(_1kp|_1kp>>>8)>>>0,_1kr=(_1kq|_1kq>>>16)>>>0,_1ks=(_1kr^_1kr>>>1)>>>0&4294967295,_1kt=_1ks>>>0;return ((_1k5>>>0&_1kt)>>>0==0)?new T4(0,(_1k5>>>0&((_1kt-1>>>0^4294967295)>>>0^_1kt)>>>0)>>>0&4294967295,_1ks,E(new T2(1,_1k3,_1k4)),E(_1k7)):new T4(0,(_1k5>>>0&((_1kt-1>>>0^4294967295)>>>0^_1kt)>>>0)>>>0&4294967295,_1ks,E(_1k7),E(new T2(1,_1k3,_1k4)));}else{return new T2(1,_1k3,new T(function(){return B(A3(_1jZ,_1k3,_1k4,_1k7.b));}));}break;default:return new T2(1,_1k3,_1k4);}},_1ku=function(_1kv,_1kw,_1kx,_1ky){var _1kz=E(_1ky);switch(_1kz._){case 0:var _1kA=_1kz.a,_1kB=_1kz.b,_1kC=_1kz.c,_1kD=_1kz.d,_1kE=_1kB>>>0;if(((_1kx>>>0&((_1kE-1>>>0^4294967295)>>>0^_1kE)>>>0)>>>0&4294967295)==_1kA){return ((_1kx>>>0&_1kE)>>>0==0)?new T4(0,_1kA,_1kB,E(B(_1ku(_1kv,_1kw,_1kx,_1kC))),E(_1kD)):new T4(0,_1kA,_1kB,E(_1kC),E(B(_1ku(_1kv,_1kw,_1kx,_1kD))));}else{var _1kF=(_1kA>>>0^_1kx>>>0)>>>0,_1kG=(_1kF|_1kF>>>1)>>>0,_1kH=(_1kG|_1kG>>>2)>>>0,_1kI=(_1kH|_1kH>>>4)>>>0,_1kJ=(_1kI|_1kI>>>8)>>>0,_1kK=(_1kJ|_1kJ>>>16)>>>0,_1kL=(_1kK^_1kK>>>1)>>>0&4294967295,_1kM=_1kL>>>0;return ((_1kA>>>0&_1kM)>>>0==0)?new T4(0,(_1kA>>>0&((_1kM-1>>>0^4294967295)>>>0^_1kM)>>>0)>>>0&4294967295,_1kL,E(_1kz),E(new T2(1,_1kv,_1kw))):new T4(0,(_1kA>>>0&((_1kM-1>>>0^4294967295)>>>0^_1kM)>>>0)>>>0&4294967295,_1kL,E(new T2(1,_1kv,_1kw)),E(_1kz));}break;case 1:var _1kN=_1kz.a;if(_1kN!=_1kx){var _1kO=(_1kN>>>0^_1kx>>>0)>>>0,_1kP=(_1kO|_1kO>>>1)>>>0,_1kQ=(_1kP|_1kP>>>2)>>>0,_1kR=(_1kQ|_1kQ>>>4)>>>0,_1kS=(_1kR|_1kR>>>8)>>>0,_1kT=(_1kS|_1kS>>>16)>>>0,_1kU=(_1kT^_1kT>>>1)>>>0&4294967295,_1kV=_1kU>>>0;return ((_1kN>>>0&_1kV)>>>0==0)?new T4(0,(_1kN>>>0&((_1kV-1>>>0^4294967295)>>>0^_1kV)>>>0)>>>0&4294967295,_1kU,E(_1kz),E(new T2(1,_1kv,_1kw))):new T4(0,(_1kN>>>0&((_1kV-1>>>0^4294967295)>>>0^_1kV)>>>0)>>>0&4294967295,_1kU,E(new T2(1,_1kv,_1kw)),E(_1kz));}else{return new T2(1,_1kN,new T(function(){return B(A3(_1jZ,_1kN,_1kz.b,_1kw));}));}break;default:return new T2(1,_1kv,_1kw);}},_1kW=function(_1kX,_1kY,_1kZ,_1l0,_1l1,_1l2,_1l3){var _1l4=_1l1>>>0;if(((_1kZ>>>0&((_1l4-1>>>0^4294967295)>>>0^_1l4)>>>0)>>>0&4294967295)==_1l0){return ((_1kZ>>>0&_1l4)>>>0==0)?new T4(0,_1l0,_1l1,E(B(_1ku(_1kX,_1kY,_1kZ,_1l2))),E(_1l3)):new T4(0,_1l0,_1l1,E(_1l2),E(B(_1ku(_1kX,_1kY,_1kZ,_1l3))));}else{var _1l5=(_1l0>>>0^_1kZ>>>0)>>>0,_1l6=(_1l5|_1l5>>>1)>>>0,_1l7=(_1l6|_1l6>>>2)>>>0,_1l8=(_1l7|_1l7>>>4)>>>0,_1l9=(_1l8|_1l8>>>8)>>>0,_1la=(_1l9|_1l9>>>16)>>>0,_1lb=(_1la^_1la>>>1)>>>0&4294967295,_1lc=_1lb>>>0;return ((_1l0>>>0&_1lc)>>>0==0)?new T4(0,(_1l0>>>0&((_1lc-1>>>0^4294967295)>>>0^_1lc)>>>0)>>>0&4294967295,_1lb,E(new T4(0,_1l0,_1l1,E(_1l2),E(_1l3))),E(new T2(1,_1kX,_1kY))):new T4(0,(_1l0>>>0&((_1lc-1>>>0^4294967295)>>>0^_1lc)>>>0)>>>0&4294967295,_1lb,E(new T2(1,_1kX,_1kY)),E(new T4(0,_1l0,_1l1,E(_1l2),E(_1l3))));}},_1ld=function(_1le,_1lf){var _1lg=E(_1le);switch(_1lg._){case 0:var _1lh=_1lg.a,_1li=_1lg.b,_1lj=_1lg.c,_1lk=_1lg.d,_1ll=E(_1lf);switch(_1ll._){case 0:var _1lm=_1ll.a,_1ln=_1ll.b,_1lo=_1ll.c,_1lp=_1ll.d;if(_1li>>>0<=_1ln>>>0){if(_1ln>>>0<=_1li>>>0){if(_1lh!=_1lm){var _1lq=(_1lh>>>0^_1lm>>>0)>>>0,_1lr=(_1lq|_1lq>>>1)>>>0,_1ls=(_1lr|_1lr>>>2)>>>0,_1lt=(_1ls|_1ls>>>4)>>>0,_1lu=(_1lt|_1lt>>>8)>>>0,_1lv=(_1lu|_1lu>>>16)>>>0,_1lw=(_1lv^_1lv>>>1)>>>0&4294967295,_1lx=_1lw>>>0;return ((_1lh>>>0&_1lx)>>>0==0)?new T4(0,(_1lh>>>0&((_1lx-1>>>0^4294967295)>>>0^_1lx)>>>0)>>>0&4294967295,_1lw,E(_1lg),E(_1ll)):new T4(0,(_1lh>>>0&((_1lx-1>>>0^4294967295)>>>0^_1lx)>>>0)>>>0&4294967295,_1lw,E(_1ll),E(_1lg));}else{return new T4(0,_1lh,_1li,E(B(_1ld(_1lj,_1lo))),E(B(_1ld(_1lk,_1lp))));}}else{var _1ly=_1ln>>>0;if(((_1lh>>>0&((_1ly-1>>>0^4294967295)>>>0^_1ly)>>>0)>>>0&4294967295)==_1lm){return ((_1lh>>>0&_1ly)>>>0==0)?new T4(0,_1lm,_1ln,E(B(_1lz(_1lh,_1li,_1lj,_1lk,_1lo))),E(_1lp)):new T4(0,_1lm,_1ln,E(_1lo),E(B(_1lz(_1lh,_1li,_1lj,_1lk,_1lp))));}else{var _1lA=(_1lh>>>0^_1lm>>>0)>>>0,_1lB=(_1lA|_1lA>>>1)>>>0,_1lC=(_1lB|_1lB>>>2)>>>0,_1lD=(_1lC|_1lC>>>4)>>>0,_1lE=(_1lD|_1lD>>>8)>>>0,_1lF=(_1lE|_1lE>>>16)>>>0,_1lG=(_1lF^_1lF>>>1)>>>0&4294967295,_1lH=_1lG>>>0;return ((_1lh>>>0&_1lH)>>>0==0)?new T4(0,(_1lh>>>0&((_1lH-1>>>0^4294967295)>>>0^_1lH)>>>0)>>>0&4294967295,_1lG,E(_1lg),E(_1ll)):new T4(0,(_1lh>>>0&((_1lH-1>>>0^4294967295)>>>0^_1lH)>>>0)>>>0&4294967295,_1lG,E(_1ll),E(_1lg));}}}else{var _1lI=_1li>>>0;if(((_1lm>>>0&((_1lI-1>>>0^4294967295)>>>0^_1lI)>>>0)>>>0&4294967295)==_1lh){return ((_1lm>>>0&_1lI)>>>0==0)?new T4(0,_1lh,_1li,E(B(_1lJ(_1lj,_1lm,_1ln,_1lo,_1lp))),E(_1lk)):new T4(0,_1lh,_1li,E(_1lj),E(B(_1lJ(_1lk,_1lm,_1ln,_1lo,_1lp))));}else{var _1lK=(_1lh>>>0^_1lm>>>0)>>>0,_1lL=(_1lK|_1lK>>>1)>>>0,_1lM=(_1lL|_1lL>>>2)>>>0,_1lN=(_1lM|_1lM>>>4)>>>0,_1lO=(_1lN|_1lN>>>8)>>>0,_1lP=(_1lO|_1lO>>>16)>>>0,_1lQ=(_1lP^_1lP>>>1)>>>0&4294967295,_1lR=_1lQ>>>0;return ((_1lh>>>0&_1lR)>>>0==0)?new T4(0,(_1lh>>>0&((_1lR-1>>>0^4294967295)>>>0^_1lR)>>>0)>>>0&4294967295,_1lQ,E(_1lg),E(_1ll)):new T4(0,(_1lh>>>0&((_1lR-1>>>0^4294967295)>>>0^_1lR)>>>0)>>>0&4294967295,_1lQ,E(_1ll),E(_1lg));}}break;case 1:var _1lS=_1ll.a;return new F(function(){return _1kW(_1lS,_1ll.b,_1lS,_1lh,_1li,_1lj,_1lk);});break;default:return E(_1lg);}break;case 1:var _1lT=_1lg.a;return new F(function(){return _1k2(_1lT,_1lg.b,_1lT,_1lf);});break;default:return E(_1lf);}},_1lz=function(_1lU,_1lV,_1lW,_1lX,_1lY){var _1lZ=E(_1lY);switch(_1lZ._){case 0:var _1m0=_1lZ.a,_1m1=_1lZ.b,_1m2=_1lZ.c,_1m3=_1lZ.d;if(_1lV>>>0<=_1m1>>>0){if(_1m1>>>0<=_1lV>>>0){if(_1lU!=_1m0){var _1m4=(_1lU>>>0^_1m0>>>0)>>>0,_1m5=(_1m4|_1m4>>>1)>>>0,_1m6=(_1m5|_1m5>>>2)>>>0,_1m7=(_1m6|_1m6>>>4)>>>0,_1m8=(_1m7|_1m7>>>8)>>>0,_1m9=(_1m8|_1m8>>>16)>>>0,_1ma=(_1m9^_1m9>>>1)>>>0&4294967295,_1mb=_1ma>>>0;return ((_1lU>>>0&_1mb)>>>0==0)?new T4(0,(_1lU>>>0&((_1mb-1>>>0^4294967295)>>>0^_1mb)>>>0)>>>0&4294967295,_1ma,E(new T4(0,_1lU,_1lV,E(_1lW),E(_1lX))),E(_1lZ)):new T4(0,(_1lU>>>0&((_1mb-1>>>0^4294967295)>>>0^_1mb)>>>0)>>>0&4294967295,_1ma,E(_1lZ),E(new T4(0,_1lU,_1lV,E(_1lW),E(_1lX))));}else{return new T4(0,_1lU,_1lV,E(B(_1ld(_1lW,_1m2))),E(B(_1ld(_1lX,_1m3))));}}else{var _1mc=_1m1>>>0;if(((_1lU>>>0&((_1mc-1>>>0^4294967295)>>>0^_1mc)>>>0)>>>0&4294967295)==_1m0){return ((_1lU>>>0&_1mc)>>>0==0)?new T4(0,_1m0,_1m1,E(B(_1lz(_1lU,_1lV,_1lW,_1lX,_1m2))),E(_1m3)):new T4(0,_1m0,_1m1,E(_1m2),E(B(_1lz(_1lU,_1lV,_1lW,_1lX,_1m3))));}else{var _1md=(_1lU>>>0^_1m0>>>0)>>>0,_1me=(_1md|_1md>>>1)>>>0,_1mf=(_1me|_1me>>>2)>>>0,_1mg=(_1mf|_1mf>>>4)>>>0,_1mh=(_1mg|_1mg>>>8)>>>0,_1mi=(_1mh|_1mh>>>16)>>>0,_1mj=(_1mi^_1mi>>>1)>>>0&4294967295,_1mk=_1mj>>>0;return ((_1lU>>>0&_1mk)>>>0==0)?new T4(0,(_1lU>>>0&((_1mk-1>>>0^4294967295)>>>0^_1mk)>>>0)>>>0&4294967295,_1mj,E(new T4(0,_1lU,_1lV,E(_1lW),E(_1lX))),E(_1lZ)):new T4(0,(_1lU>>>0&((_1mk-1>>>0^4294967295)>>>0^_1mk)>>>0)>>>0&4294967295,_1mj,E(_1lZ),E(new T4(0,_1lU,_1lV,E(_1lW),E(_1lX))));}}}else{var _1ml=_1lV>>>0;if(((_1m0>>>0&((_1ml-1>>>0^4294967295)>>>0^_1ml)>>>0)>>>0&4294967295)==_1lU){return ((_1m0>>>0&_1ml)>>>0==0)?new T4(0,_1lU,_1lV,E(B(_1lJ(_1lW,_1m0,_1m1,_1m2,_1m3))),E(_1lX)):new T4(0,_1lU,_1lV,E(_1lW),E(B(_1lJ(_1lX,_1m0,_1m1,_1m2,_1m3))));}else{var _1mm=(_1lU>>>0^_1m0>>>0)>>>0,_1mn=(_1mm|_1mm>>>1)>>>0,_1mo=(_1mn|_1mn>>>2)>>>0,_1mp=(_1mo|_1mo>>>4)>>>0,_1mq=(_1mp|_1mp>>>8)>>>0,_1mr=(_1mq|_1mq>>>16)>>>0,_1ms=(_1mr^_1mr>>>1)>>>0&4294967295,_1mt=_1ms>>>0;return ((_1lU>>>0&_1mt)>>>0==0)?new T4(0,(_1lU>>>0&((_1mt-1>>>0^4294967295)>>>0^_1mt)>>>0)>>>0&4294967295,_1ms,E(new T4(0,_1lU,_1lV,E(_1lW),E(_1lX))),E(_1lZ)):new T4(0,(_1lU>>>0&((_1mt-1>>>0^4294967295)>>>0^_1mt)>>>0)>>>0&4294967295,_1ms,E(_1lZ),E(new T4(0,_1lU,_1lV,E(_1lW),E(_1lX))));}}break;case 1:var _1mu=_1lZ.a;return new F(function(){return _1kW(_1mu,_1lZ.b,_1mu,_1lU,_1lV,_1lW,_1lX);});break;default:return new T4(0,_1lU,_1lV,E(_1lW),E(_1lX));}},_1lJ=function(_1mv,_1mw,_1mx,_1my,_1mz){var _1mA=E(_1mv);switch(_1mA._){case 0:var _1mB=_1mA.a,_1mC=_1mA.b,_1mD=_1mA.c,_1mE=_1mA.d;if(_1mC>>>0<=_1mx>>>0){if(_1mx>>>0<=_1mC>>>0){if(_1mB!=_1mw){var _1mF=(_1mB>>>0^_1mw>>>0)>>>0,_1mG=(_1mF|_1mF>>>1)>>>0,_1mH=(_1mG|_1mG>>>2)>>>0,_1mI=(_1mH|_1mH>>>4)>>>0,_1mJ=(_1mI|_1mI>>>8)>>>0,_1mK=(_1mJ|_1mJ>>>16)>>>0,_1mL=(_1mK^_1mK>>>1)>>>0&4294967295,_1mM=_1mL>>>0;return ((_1mB>>>0&_1mM)>>>0==0)?new T4(0,(_1mB>>>0&((_1mM-1>>>0^4294967295)>>>0^_1mM)>>>0)>>>0&4294967295,_1mL,E(_1mA),E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz)))):new T4(0,(_1mB>>>0&((_1mM-1>>>0^4294967295)>>>0^_1mM)>>>0)>>>0&4294967295,_1mL,E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz))),E(_1mA));}else{return new T4(0,_1mB,_1mC,E(B(_1ld(_1mD,_1my))),E(B(_1ld(_1mE,_1mz))));}}else{var _1mN=_1mx>>>0;if(((_1mB>>>0&((_1mN-1>>>0^4294967295)>>>0^_1mN)>>>0)>>>0&4294967295)==_1mw){return ((_1mB>>>0&_1mN)>>>0==0)?new T4(0,_1mw,_1mx,E(B(_1lz(_1mB,_1mC,_1mD,_1mE,_1my))),E(_1mz)):new T4(0,_1mw,_1mx,E(_1my),E(B(_1lz(_1mB,_1mC,_1mD,_1mE,_1mz))));}else{var _1mO=(_1mB>>>0^_1mw>>>0)>>>0,_1mP=(_1mO|_1mO>>>1)>>>0,_1mQ=(_1mP|_1mP>>>2)>>>0,_1mR=(_1mQ|_1mQ>>>4)>>>0,_1mS=(_1mR|_1mR>>>8)>>>0,_1mT=(_1mS|_1mS>>>16)>>>0,_1mU=(_1mT^_1mT>>>1)>>>0&4294967295,_1mV=_1mU>>>0;return ((_1mB>>>0&_1mV)>>>0==0)?new T4(0,(_1mB>>>0&((_1mV-1>>>0^4294967295)>>>0^_1mV)>>>0)>>>0&4294967295,_1mU,E(_1mA),E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz)))):new T4(0,(_1mB>>>0&((_1mV-1>>>0^4294967295)>>>0^_1mV)>>>0)>>>0&4294967295,_1mU,E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz))),E(_1mA));}}}else{var _1mW=_1mC>>>0;if(((_1mw>>>0&((_1mW-1>>>0^4294967295)>>>0^_1mW)>>>0)>>>0&4294967295)==_1mB){return ((_1mw>>>0&_1mW)>>>0==0)?new T4(0,_1mB,_1mC,E(B(_1lJ(_1mD,_1mw,_1mx,_1my,_1mz))),E(_1mE)):new T4(0,_1mB,_1mC,E(_1mD),E(B(_1lJ(_1mE,_1mw,_1mx,_1my,_1mz))));}else{var _1mX=(_1mB>>>0^_1mw>>>0)>>>0,_1mY=(_1mX|_1mX>>>1)>>>0,_1mZ=(_1mY|_1mY>>>2)>>>0,_1n0=(_1mZ|_1mZ>>>4)>>>0,_1n1=(_1n0|_1n0>>>8)>>>0,_1n2=(_1n1|_1n1>>>16)>>>0,_1n3=(_1n2^_1n2>>>1)>>>0&4294967295,_1n4=_1n3>>>0;return ((_1mB>>>0&_1n4)>>>0==0)?new T4(0,(_1mB>>>0&((_1n4-1>>>0^4294967295)>>>0^_1n4)>>>0)>>>0&4294967295,_1n3,E(_1mA),E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz)))):new T4(0,(_1mB>>>0&((_1n4-1>>>0^4294967295)>>>0^_1n4)>>>0)>>>0&4294967295,_1n3,E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz))),E(_1mA));}}break;case 1:var _1n5=_1mA.a,_1n6=_1mA.b,_1n7=_1mx>>>0;if(((_1n5>>>0&((_1n7-1>>>0^4294967295)>>>0^_1n7)>>>0)>>>0&4294967295)==_1mw){return ((_1n5>>>0&_1n7)>>>0==0)?new T4(0,_1mw,_1mx,E(B(_1k2(_1n5,_1n6,_1n5,_1my))),E(_1mz)):new T4(0,_1mw,_1mx,E(_1my),E(B(_1k2(_1n5,_1n6,_1n5,_1mz))));}else{var _1n8=(_1n5>>>0^_1mw>>>0)>>>0,_1n9=(_1n8|_1n8>>>1)>>>0,_1na=(_1n9|_1n9>>>2)>>>0,_1nb=(_1na|_1na>>>4)>>>0,_1nc=(_1nb|_1nb>>>8)>>>0,_1nd=(_1nc|_1nc>>>16)>>>0,_1ne=(_1nd^_1nd>>>1)>>>0&4294967295,_1nf=_1ne>>>0;return ((_1n5>>>0&_1nf)>>>0==0)?new T4(0,(_1n5>>>0&((_1nf-1>>>0^4294967295)>>>0^_1nf)>>>0)>>>0&4294967295,_1ne,E(new T2(1,_1n5,_1n6)),E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz)))):new T4(0,(_1n5>>>0&((_1nf-1>>>0^4294967295)>>>0^_1nf)>>>0)>>>0&4294967295,_1ne,E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz))),E(new T2(1,_1n5,_1n6)));}break;default:return new T4(0,_1mw,_1mx,E(_1my),E(_1mz));}};return new F(function(){return _1ld(_1k0,_1k1);});},_1ng=function(_1nh,_1ni,_1nj){return new F(function(){return _1jY(_1jS,_1ni,_1nj);});},_1nk=function(_1nl,_1nm){return E(_1nl);},_1nn=new T2(0,_4l,_Rm),_1no=function(_1np,_1nq){while(1){var _1nr=B((function(_1ns,_1nt){var _1nu=E(_1nt);if(!_1nu._){_1np=new T2(1,_1nu.b,new T(function(){return B(_1no(_1ns,_1nu.d));}));_1nq=_1nu.c;return __continue;}else{return E(_1ns);}})(_1np,_1nq));if(_1nr!=__continue){return _1nr;}}},_1nv=function(_1nw,_1nx,_1ny){var _1nz=function(_1nA){var _1nB=function(_1nC){if(_1nA!=_1nC){return false;}else{return new F(function(){return _18U(_1nw,B(_1no(_4,_1nx)),B(_1no(_4,_1ny)));});}},_1nD=E(_1ny);if(!_1nD._){return new F(function(){return _1nB(_1nD.a);});}else{return new F(function(){return _1nB(0);});}},_1nE=E(_1nx);if(!_1nE._){return new F(function(){return _1nz(_1nE.a);});}else{return new F(function(){return _1nz(0);});}},_1nF=function(_1nG,_1nH){return (!B(_1nv(_1b6,_1nG,_1nH)))?true:false;},_1nI=function(_1nJ,_1nK){return new F(function(){return _1nv(_1b6,_1nJ,_1nK);});},_1nL=new T2(0,_1nI,_1nF),_1nM=function(_1nN,_1nO){var _1nP=function(_1nQ){while(1){var _1nR=E(_1nQ);switch(_1nR._){case 0:var _1nS=_1nR.b>>>0;if(((_1nN>>>0&((_1nS-1>>>0^4294967295)>>>0^_1nS)>>>0)>>>0&4294967295)==_1nR.a){if(!((_1nN>>>0&_1nS)>>>0)){_1nQ=_1nR.c;continue;}else{_1nQ=_1nR.d;continue;}}else{return false;}break;case 1:return _1nN==_1nR.a;default:return false;}}};return new F(function(){return _1nP(_1nO);});},_1nT=function(_1nU,_1nV){var _1nW=function(_1nX){while(1){var _1nY=E(_1nX);switch(_1nY._){case 0:var _1nZ=_1nY.b>>>0;if(((_1nU>>>0&((_1nZ-1>>>0^4294967295)>>>0^_1nZ)>>>0)>>>0&4294967295)==_1nY.a){if(!((_1nU>>>0&_1nZ)>>>0)){_1nX=_1nY.c;continue;}else{_1nX=_1nY.d;continue;}}else{return false;}break;case 1:return ((_1nU&(-32))!=_1nY.a)?false:((1<<(_1nU&31)>>>0&_1nY.b)>>>0==0)?false:true;default:return false;}}};return new F(function(){return _1nW(_1nV);});},_1o0=function(_1o1,_1o2,_1o3){while(1){var _1o4=E(_1o2);switch(_1o4._){case 0:var _1o5=E(_1o3);if(!_1o5._){if(_1o4.b!=_1o5.b){return false;}else{if(_1o4.a!=_1o5.a){return false;}else{if(!B(_1o0(_1o1,_1o4.c,_1o5.c))){return false;}else{_1o2=_1o4.d;_1o3=_1o5.d;continue;}}}}else{return false;}break;case 1:var _1o6=E(_1o3);if(_1o6._==1){if(_1o4.a!=_1o6.a){return false;}else{return new F(function(){return A3(_pS,_1o1,_1o4.b,_1o6.b);});}}else{return false;}break;default:return (E(_1o3)._==2)?true:false;}}},_1o7=function(_1o8,_1o9){var _1oa=E(_1o9);if(!_1oa._){var _1ob=_1oa.b,_1oc=_1oa.c,_1od=_1oa.d;if(!B(A1(_1o8,_1ob))){return new F(function(){return _15T(B(_1o7(_1o8,_1oc)),B(_1o7(_1o8,_1od)));});}else{return new F(function(){return _OS(_1ob,B(_1o7(_1o8,_1oc)),B(_1o7(_1o8,_1od)));});}}else{return new T0(1);}},_1oe=function(_1of,_1og,_1oh){var _1oi=E(_1oh);switch(_1oi._){case 0:var _1oj=_1oi.a,_1ok=_1oi.b,_1ol=_1oi.c,_1om=_1oi.d,_1on=_1ok>>>0;if(((_1of>>>0&((_1on-1>>>0^4294967295)>>>0^_1on)>>>0)>>>0&4294967295)==_1oj){return ((_1of>>>0&_1on)>>>0==0)?new T4(0,_1oj,_1ok,E(B(_1oe(_1of,_1og,_1ol))),E(_1om)):new T4(0,_1oj,_1ok,E(_1ol),E(B(_1oe(_1of,_1og,_1om))));}else{var _1oo=(_1of>>>0^_1oj>>>0)>>>0,_1op=(_1oo|_1oo>>>1)>>>0,_1oq=(_1op|_1op>>>2)>>>0,_1or=(_1oq|_1oq>>>4)>>>0,_1os=(_1or|_1or>>>8)>>>0,_1ot=(_1os|_1os>>>16)>>>0,_1ou=(_1ot^_1ot>>>1)>>>0&4294967295,_1ov=_1ou>>>0;return ((_1of>>>0&_1ov)>>>0==0)?new T4(0,(_1of>>>0&((_1ov-1>>>0^4294967295)>>>0^_1ov)>>>0)>>>0&4294967295,_1ou,E(new T2(1,_1of,_1og)),E(_1oi)):new T4(0,(_1of>>>0&((_1ov-1>>>0^4294967295)>>>0^_1ov)>>>0)>>>0&4294967295,_1ou,E(_1oi),E(new T2(1,_1of,_1og)));}break;case 1:var _1ow=_1oi.a;if(_1ow!=_1of){var _1ox=(_1of>>>0^_1ow>>>0)>>>0,_1oy=(_1ox|_1ox>>>1)>>>0,_1oz=(_1oy|_1oy>>>2)>>>0,_1oA=(_1oz|_1oz>>>4)>>>0,_1oB=(_1oA|_1oA>>>8)>>>0,_1oC=(_1oB|_1oB>>>16)>>>0,_1oD=(_1oC^_1oC>>>1)>>>0&4294967295,_1oE=_1oD>>>0;return ((_1of>>>0&_1oE)>>>0==0)?new T4(0,(_1of>>>0&((_1oE-1>>>0^4294967295)>>>0^_1oE)>>>0)>>>0&4294967295,_1oD,E(new T2(1,_1of,_1og)),E(_1oi)):new T4(0,(_1of>>>0&((_1oE-1>>>0^4294967295)>>>0^_1oE)>>>0)>>>0&4294967295,_1oD,E(_1oi),E(new T2(1,_1of,_1og)));}else{return new T2(1,_1ow,(_1og|_1oi.b)>>>0);}break;default:return new T2(1,_1of,_1og);}},_1oF=function(_1oG,_1oH){while(1){var _1oI=E(_1oG);if(!_1oI._){return E(_1oH);}else{var _1oJ=E(E(_1oI.a).b),_1oK=B(_1oe(_1oJ&(-32),1<<(_1oJ&31)>>>0,_1oH));_1oG=_1oI.b;_1oH=_1oK;continue;}}},_1oL=function(_1oM,_1oN){while(1){var _1oO=E(_1oM);if(!_1oO._){return E(_1oN);}else{var _1oP=B(_1oF(E(_1oO.a).a,_1oN));_1oM=_1oO.b;_1oN=_1oP;continue;}}},_1oQ=function(_1oR,_1oS){while(1){var _1oT=E(_1oS);if(!_1oT._){var _1oU=_1oT.c,_1oV=_1oT.d,_1oW=E(_1oT.b);if(!_1oW._){var _1oX=B(_1oL(_1oW.b,B(_1oQ(_1oR,_1oV))));_1oR=_1oX;_1oS=_1oU;continue;}else{var _1oX=B(_1oQ(_1oR,_1oV));_1oR=_1oX;_1oS=_1oU;continue;}}else{return E(_1oR);}}},_1oY=-1,_1oZ=-2,_1p0=-3,_1p1=new T2(1,_Mf,_4),_1p2=new T2(1,_1p0,_1p1),_1p3=new T2(1,_1oZ,_1p2),_1p4=new T2(1,_1oY,_1p3),_1p5=function(_1p6,_1p7,_1p8){var _1p9=function(_1pa,_1pb){if(!B(_1o0(_1nL,_1p6,_1pa))){return new F(function(){return _1p5(_1pa,_1pb,_1p8);});}else{return E(_1p6);}},_1pc=function(_1pd){if(!B(_w5(_j7,_1pd,_1p4))){var _1pe=E(_1pd);if(!B(_1nM(_1pe,_1p6))){return new F(function(){return _1nT(_1pe,_1p7);});}else{return true;}}else{return true;}},_1pf=function(_1pg){while(1){var _1ph=E(_1pg);if(!_1ph._){return true;}else{if(!B(_1pc(E(_1ph.a).b))){return false;}else{_1pg=_1ph.b;continue;}}}},_1pi=function(_1pj){var _1pk=E(_1pj);switch(_1pk._){case 0:return new F(function(){return _1pf(_1pk.b);});break;case 1:return new F(function(){return _1pc(_1pk.a);});break;default:return true;}},_1pl=function(_1pm,_1pn,_1po){while(1){var _1pp=B((function(_1pq,_1pr,_1ps){var _1pt=E(_1ps);switch(_1pt._){case 0:var _1pu=B(_1pl(_1pq,_1pr,_1pt.d));_1pm=_1pu.a;_1pn=_1pu.b;_1po=_1pt.c;return __continue;case 1:var _1pv=E(_1pq),_1pw=E(_1pr),_1px=B(_1o7(_1pi,_1pt.b));return (_1px._==0)?new T2(0,new T(function(){return B(_14A(_1pt.a,_1px,_1pv));}),new T(function(){return B(_1oQ(_1pw,_1px));})):new T2(0,_1pv,_1pw);default:return new T2(0,_1pq,_1pr);}})(_1pm,_1pn,_1po));if(_1pp!=__continue){return _1pp;}}},_1py=E(_1p8);if(!_1py._){var _1pz=_1py.c,_1pA=_1py.d;if(_1py.b>=0){var _1pB=B(_1pl(_UD,_18E,_1pA)),_1pC=B(_1pl(_1pB.a,_1pB.b,_1pz));return new F(function(){return _1p9(_1pC.a,_1pC.b);});}else{var _1pD=B(_1pl(_UD,_18E,_1pz)),_1pE=B(_1pl(_1pD.a,_1pD.b,_1pA));return new F(function(){return _1p9(_1pE.a,_1pE.b);});}}else{var _1pF=B(_1pl(_UD,_18E,_1py));return new F(function(){return _1p9(_1pF.a,_1pF.b);});}},_1pG=function(_1pH,_1pI){while(1){var _1pJ=E(_1pI);if(!_1pJ._){return E(_1pH);}else{var _1pK=E(_1pJ.a),_1pL=B(_14A(E(_1pK.a),_1pK.b,_1pH));_1pH=_1pL;_1pI=_1pJ.b;continue;}}},_1pM=function(_1pN){var _1pO=E(_1pN);return (_1pO._==0)?(E(_1pO.b)._==0)?true:false:false;},_1pP=new T(function(){return B(unCStr(")"));}),_1pQ=function(_1pR,_1pS){var _1pT=new T(function(){var _1pU=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_1pS,_4)),_1pP));})));},1);return B(_0(B(_bZ(0,_1pR,_4)),_1pU));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1pT)));});},_1pV=new T(function(){return B(_7f("pgf/PGF/Optimize.hs:(259,9)-(262,117)|function getFunctions"));}),_1pW=new T(function(){return B(unCStr("&|"));}),_1pX=new T2(1,_1pW,_4),_1pY=new T(function(){return B(unCStr("&+"));}),_1pZ=new T2(1,_1pY,_4),_1q0=new T(function(){return B(_7f("pgf/PGF/Optimize.hs:(235,9)-(245,73)|function seq2prefix"));}),_1q1=function(_1q2,_1q3,_1q4,_1q5,_1q6,_1q7){var _1q8=_1q5>>>0;if(((_1q2>>>0&((_1q8-1>>>0^4294967295)>>>0^_1q8)>>>0)>>>0&4294967295)==_1q4){return ((_1q2>>>0&_1q8)>>>0==0)?new T4(0,_1q4,_1q5,E(B(_1oe(_1q2,_1q3,_1q6))),E(_1q7)):new T4(0,_1q4,_1q5,E(_1q6),E(B(_1oe(_1q2,_1q3,_1q7))));}else{var _1q9=(_1q2>>>0^_1q4>>>0)>>>0,_1qa=(_1q9|_1q9>>>1)>>>0,_1qb=(_1qa|_1qa>>>2)>>>0,_1qc=(_1qb|_1qb>>>4)>>>0,_1qd=(_1qc|_1qc>>>8)>>>0,_1qe=(_1qd|_1qd>>>16)>>>0,_1qf=(_1qe^_1qe>>>1)>>>0&4294967295,_1qg=_1qf>>>0;return ((_1q2>>>0&_1qg)>>>0==0)?new T4(0,(_1q2>>>0&((_1qg-1>>>0^4294967295)>>>0^_1qg)>>>0)>>>0&4294967295,_1qf,E(new T2(1,_1q2,_1q3)),E(new T4(0,_1q4,_1q5,E(_1q6),E(_1q7)))):new T4(0,(_1q2>>>0&((_1qg-1>>>0^4294967295)>>>0^_1qg)>>>0)>>>0&4294967295,_1qf,E(new T4(0,_1q4,_1q5,E(_1q6),E(_1q7))),E(new T2(1,_1q2,_1q3)));}},_1qh=function(_1qi,_1qj,_1qk,_1ql,_1qm){var _1qn=E(_1qm);switch(_1qn._){case 0:var _1qo=_1qn.a,_1qp=_1qn.b,_1qq=_1qn.c,_1qr=_1qn.d;if(_1qj>>>0<=_1qp>>>0){if(_1qp>>>0<=_1qj>>>0){if(_1qi!=_1qo){var _1qs=(_1qi>>>0^_1qo>>>0)>>>0,_1qt=(_1qs|_1qs>>>1)>>>0,_1qu=(_1qt|_1qt>>>2)>>>0,_1qv=(_1qu|_1qu>>>4)>>>0,_1qw=(_1qv|_1qv>>>8)>>>0,_1qx=(_1qw|_1qw>>>16)>>>0,_1qy=(_1qx^_1qx>>>1)>>>0&4294967295,_1qz=_1qy>>>0;return ((_1qi>>>0&_1qz)>>>0==0)?new T4(0,(_1qi>>>0&((_1qz-1>>>0^4294967295)>>>0^_1qz)>>>0)>>>0&4294967295,_1qy,E(new T4(0,_1qi,_1qj,E(_1qk),E(_1ql))),E(_1qn)):new T4(0,(_1qi>>>0&((_1qz-1>>>0^4294967295)>>>0^_1qz)>>>0)>>>0&4294967295,_1qy,E(_1qn),E(new T4(0,_1qi,_1qj,E(_1qk),E(_1ql))));}else{return new T4(0,_1qi,_1qj,E(B(_1qA(_1qk,_1qq))),E(B(_1qA(_1ql,_1qr))));}}else{var _1qB=_1qp>>>0;if(((_1qi>>>0&((_1qB-1>>>0^4294967295)>>>0^_1qB)>>>0)>>>0&4294967295)==_1qo){return ((_1qi>>>0&_1qB)>>>0==0)?new T4(0,_1qo,_1qp,E(B(_1qh(_1qi,_1qj,_1qk,_1ql,_1qq))),E(_1qr)):new T4(0,_1qo,_1qp,E(_1qq),E(B(_1qh(_1qi,_1qj,_1qk,_1ql,_1qr))));}else{var _1qC=(_1qi>>>0^_1qo>>>0)>>>0,_1qD=(_1qC|_1qC>>>1)>>>0,_1qE=(_1qD|_1qD>>>2)>>>0,_1qF=(_1qE|_1qE>>>4)>>>0,_1qG=(_1qF|_1qF>>>8)>>>0,_1qH=(_1qG|_1qG>>>16)>>>0,_1qI=(_1qH^_1qH>>>1)>>>0&4294967295,_1qJ=_1qI>>>0;return ((_1qi>>>0&_1qJ)>>>0==0)?new T4(0,(_1qi>>>0&((_1qJ-1>>>0^4294967295)>>>0^_1qJ)>>>0)>>>0&4294967295,_1qI,E(new T4(0,_1qi,_1qj,E(_1qk),E(_1ql))),E(_1qn)):new T4(0,(_1qi>>>0&((_1qJ-1>>>0^4294967295)>>>0^_1qJ)>>>0)>>>0&4294967295,_1qI,E(_1qn),E(new T4(0,_1qi,_1qj,E(_1qk),E(_1ql))));}}}else{var _1qK=_1qj>>>0;if(((_1qo>>>0&((_1qK-1>>>0^4294967295)>>>0^_1qK)>>>0)>>>0&4294967295)==_1qi){return ((_1qo>>>0&_1qK)>>>0==0)?new T4(0,_1qi,_1qj,E(B(_1qL(_1qk,_1qo,_1qp,_1qq,_1qr))),E(_1ql)):new T4(0,_1qi,_1qj,E(_1qk),E(B(_1qL(_1ql,_1qo,_1qp,_1qq,_1qr))));}else{var _1qM=(_1qi>>>0^_1qo>>>0)>>>0,_1qN=(_1qM|_1qM>>>1)>>>0,_1qO=(_1qN|_1qN>>>2)>>>0,_1qP=(_1qO|_1qO>>>4)>>>0,_1qQ=(_1qP|_1qP>>>8)>>>0,_1qR=(_1qQ|_1qQ>>>16)>>>0,_1qS=(_1qR^_1qR>>>1)>>>0&4294967295,_1qT=_1qS>>>0;return ((_1qi>>>0&_1qT)>>>0==0)?new T4(0,(_1qi>>>0&((_1qT-1>>>0^4294967295)>>>0^_1qT)>>>0)>>>0&4294967295,_1qS,E(new T4(0,_1qi,_1qj,E(_1qk),E(_1ql))),E(_1qn)):new T4(0,(_1qi>>>0&((_1qT-1>>>0^4294967295)>>>0^_1qT)>>>0)>>>0&4294967295,_1qS,E(_1qn),E(new T4(0,_1qi,_1qj,E(_1qk),E(_1ql))));}}break;case 1:return new F(function(){return _1q1(_1qn.a,_1qn.b,_1qi,_1qj,_1qk,_1ql);});break;default:return new T4(0,_1qi,_1qj,E(_1qk),E(_1ql));}},_1qL=function(_1qU,_1qV,_1qW,_1qX,_1qY){var _1qZ=E(_1qU);switch(_1qZ._){case 0:var _1r0=_1qZ.a,_1r1=_1qZ.b,_1r2=_1qZ.c,_1r3=_1qZ.d;if(_1r1>>>0<=_1qW>>>0){if(_1qW>>>0<=_1r1>>>0){if(_1r0!=_1qV){var _1r4=(_1r0>>>0^_1qV>>>0)>>>0,_1r5=(_1r4|_1r4>>>1)>>>0,_1r6=(_1r5|_1r5>>>2)>>>0,_1r7=(_1r6|_1r6>>>4)>>>0,_1r8=(_1r7|_1r7>>>8)>>>0,_1r9=(_1r8|_1r8>>>16)>>>0,_1ra=(_1r9^_1r9>>>1)>>>0&4294967295,_1rb=_1ra>>>0;return ((_1r0>>>0&_1rb)>>>0==0)?new T4(0,(_1r0>>>0&((_1rb-1>>>0^4294967295)>>>0^_1rb)>>>0)>>>0&4294967295,_1ra,E(_1qZ),E(new T4(0,_1qV,_1qW,E(_1qX),E(_1qY)))):new T4(0,(_1r0>>>0&((_1rb-1>>>0^4294967295)>>>0^_1rb)>>>0)>>>0&4294967295,_1ra,E(new T4(0,_1qV,_1qW,E(_1qX),E(_1qY))),E(_1qZ));}else{return new T4(0,_1r0,_1r1,E(B(_1qA(_1r2,_1qX))),E(B(_1qA(_1r3,_1qY))));}}else{var _1rc=_1qW>>>0;if(((_1r0>>>0&((_1rc-1>>>0^4294967295)>>>0^_1rc)>>>0)>>>0&4294967295)==_1qV){return ((_1r0>>>0&_1rc)>>>0==0)?new T4(0,_1qV,_1qW,E(B(_1qh(_1r0,_1r1,_1r2,_1r3,_1qX))),E(_1qY)):new T4(0,_1qV,_1qW,E(_1qX),E(B(_1qh(_1r0,_1r1,_1r2,_1r3,_1qY))));}else{var _1rd=(_1r0>>>0^_1qV>>>0)>>>0,_1re=(_1rd|_1rd>>>1)>>>0,_1rf=(_1re|_1re>>>2)>>>0,_1rg=(_1rf|_1rf>>>4)>>>0,_1rh=(_1rg|_1rg>>>8)>>>0,_1ri=(_1rh|_1rh>>>16)>>>0,_1rj=(_1ri^_1ri>>>1)>>>0&4294967295,_1rk=_1rj>>>0;return ((_1r0>>>0&_1rk)>>>0==0)?new T4(0,(_1r0>>>0&((_1rk-1>>>0^4294967295)>>>0^_1rk)>>>0)>>>0&4294967295,_1rj,E(_1qZ),E(new T4(0,_1qV,_1qW,E(_1qX),E(_1qY)))):new T4(0,(_1r0>>>0&((_1rk-1>>>0^4294967295)>>>0^_1rk)>>>0)>>>0&4294967295,_1rj,E(new T4(0,_1qV,_1qW,E(_1qX),E(_1qY))),E(_1qZ));}}}else{var _1rl=_1r1>>>0;if(((_1qV>>>0&((_1rl-1>>>0^4294967295)>>>0^_1rl)>>>0)>>>0&4294967295)==_1r0){return ((_1qV>>>0&_1rl)>>>0==0)?new T4(0,_1r0,_1r1,E(B(_1qL(_1r2,_1qV,_1qW,_1qX,_1qY))),E(_1r3)):new T4(0,_1r0,_1r1,E(_1r2),E(B(_1qL(_1r3,_1qV,_1qW,_1qX,_1qY))));}else{var _1rm=(_1r0>>>0^_1qV>>>0)>>>0,_1rn=(_1rm|_1rm>>>1)>>>0,_1ro=(_1rn|_1rn>>>2)>>>0,_1rp=(_1ro|_1ro>>>4)>>>0,_1rq=(_1rp|_1rp>>>8)>>>0,_1rr=(_1rq|_1rq>>>16)>>>0,_1rs=(_1rr^_1rr>>>1)>>>0&4294967295,_1rt=_1rs>>>0;return ((_1r0>>>0&_1rt)>>>0==0)?new T4(0,(_1r0>>>0&((_1rt-1>>>0^4294967295)>>>0^_1rt)>>>0)>>>0&4294967295,_1rs,E(_1qZ),E(new T4(0,_1qV,_1qW,E(_1qX),E(_1qY)))):new T4(0,(_1r0>>>0&((_1rt-1>>>0^4294967295)>>>0^_1rt)>>>0)>>>0&4294967295,_1rs,E(new T4(0,_1qV,_1qW,E(_1qX),E(_1qY))),E(_1qZ));}}break;case 1:return new F(function(){return _1q1(_1qZ.a,_1qZ.b,_1qV,_1qW,_1qX,_1qY);});break;default:return new T4(0,_1qV,_1qW,E(_1qX),E(_1qY));}},_1qA=function(_1ru,_1rv){var _1rw=E(_1ru);switch(_1rw._){case 0:var _1rx=_1rw.a,_1ry=_1rw.b,_1rz=_1rw.c,_1rA=_1rw.d,_1rB=E(_1rv);switch(_1rB._){case 0:var _1rC=_1rB.a,_1rD=_1rB.b,_1rE=_1rB.c,_1rF=_1rB.d;if(_1ry>>>0<=_1rD>>>0){if(_1rD>>>0<=_1ry>>>0){if(_1rx!=_1rC){var _1rG=(_1rx>>>0^_1rC>>>0)>>>0,_1rH=(_1rG|_1rG>>>1)>>>0,_1rI=(_1rH|_1rH>>>2)>>>0,_1rJ=(_1rI|_1rI>>>4)>>>0,_1rK=(_1rJ|_1rJ>>>8)>>>0,_1rL=(_1rK|_1rK>>>16)>>>0,_1rM=(_1rL^_1rL>>>1)>>>0&4294967295,_1rN=_1rM>>>0;return ((_1rx>>>0&_1rN)>>>0==0)?new T4(0,(_1rx>>>0&((_1rN-1>>>0^4294967295)>>>0^_1rN)>>>0)>>>0&4294967295,_1rM,E(_1rw),E(_1rB)):new T4(0,(_1rx>>>0&((_1rN-1>>>0^4294967295)>>>0^_1rN)>>>0)>>>0&4294967295,_1rM,E(_1rB),E(_1rw));}else{return new T4(0,_1rx,_1ry,E(B(_1qA(_1rz,_1rE))),E(B(_1qA(_1rA,_1rF))));}}else{var _1rO=_1rD>>>0;if(((_1rx>>>0&((_1rO-1>>>0^4294967295)>>>0^_1rO)>>>0)>>>0&4294967295)==_1rC){return ((_1rx>>>0&_1rO)>>>0==0)?new T4(0,_1rC,_1rD,E(B(_1qh(_1rx,_1ry,_1rz,_1rA,_1rE))),E(_1rF)):new T4(0,_1rC,_1rD,E(_1rE),E(B(_1qh(_1rx,_1ry,_1rz,_1rA,_1rF))));}else{var _1rP=(_1rx>>>0^_1rC>>>0)>>>0,_1rQ=(_1rP|_1rP>>>1)>>>0,_1rR=(_1rQ|_1rQ>>>2)>>>0,_1rS=(_1rR|_1rR>>>4)>>>0,_1rT=(_1rS|_1rS>>>8)>>>0,_1rU=(_1rT|_1rT>>>16)>>>0,_1rV=(_1rU^_1rU>>>1)>>>0&4294967295,_1rW=_1rV>>>0;return ((_1rx>>>0&_1rW)>>>0==0)?new T4(0,(_1rx>>>0&((_1rW-1>>>0^4294967295)>>>0^_1rW)>>>0)>>>0&4294967295,_1rV,E(_1rw),E(_1rB)):new T4(0,(_1rx>>>0&((_1rW-1>>>0^4294967295)>>>0^_1rW)>>>0)>>>0&4294967295,_1rV,E(_1rB),E(_1rw));}}}else{var _1rX=_1ry>>>0;if(((_1rC>>>0&((_1rX-1>>>0^4294967295)>>>0^_1rX)>>>0)>>>0&4294967295)==_1rx){return ((_1rC>>>0&_1rX)>>>0==0)?new T4(0,_1rx,_1ry,E(B(_1qL(_1rz,_1rC,_1rD,_1rE,_1rF))),E(_1rA)):new T4(0,_1rx,_1ry,E(_1rz),E(B(_1qL(_1rA,_1rC,_1rD,_1rE,_1rF))));}else{var _1rY=(_1rx>>>0^_1rC>>>0)>>>0,_1rZ=(_1rY|_1rY>>>1)>>>0,_1s0=(_1rZ|_1rZ>>>2)>>>0,_1s1=(_1s0|_1s0>>>4)>>>0,_1s2=(_1s1|_1s1>>>8)>>>0,_1s3=(_1s2|_1s2>>>16)>>>0,_1s4=(_1s3^_1s3>>>1)>>>0&4294967295,_1s5=_1s4>>>0;return ((_1rx>>>0&_1s5)>>>0==0)?new T4(0,(_1rx>>>0&((_1s5-1>>>0^4294967295)>>>0^_1s5)>>>0)>>>0&4294967295,_1s4,E(_1rw),E(_1rB)):new T4(0,(_1rx>>>0&((_1s5-1>>>0^4294967295)>>>0^_1s5)>>>0)>>>0&4294967295,_1s4,E(_1rB),E(_1rw));}}break;case 1:return new F(function(){return _1q1(_1rB.a,_1rB.b,_1rx,_1ry,_1rz,_1rA);});break;default:return E(_1rw);}break;case 1:return new F(function(){return _1oe(_1rw.a,_1rw.b,_1rv);});break;default:return E(_1rv);}},_1s6=function(_1s7,_1s8){var _1s9=E(_1s7),_1sa=B(_16o(_12I,_1qA,_1s9.a,_1s9.b,_1s8));return new T2(0,_1sa.a,_1sa.b);},_1sb=new T(function(){return B(unCStr("Int"));}),_1sc=function(_1sd,_1se,_1sf){return new F(function(){return _eX(_ea,new T2(0,_1se,_1sf),_1sd,_1sb);});},_1sg=function(_1sh,_1si,_1sj){return new F(function(){return _eX(_ea,new T2(0,_1sh,_1si),_1sj,_1sb);});},_1sk=new T(function(){return B(_1pG(_UD,_4));}),_1sl=function(_1sm,_1sn){var _1so=function(_1sp,_1sq,_1sr){return new F(function(){return A2(_1sm,_1sq,_1sr);});},_1ss=function(_1st,_1su){while(1){var _1sv=E(_1su);if(!_1sv._){return E(_1st);}else{var _1sw=B(_1jY(_1so,_1st,_1sv.a));_1st=_1sw;_1su=_1sv.b;continue;}}};return new F(function(){return _1ss(_UD,_1sn);});},_1sx=function(_1sy,_1sz,_1sA,_1sB,_1sC,_1sD,_1sE,_1sF,_1sG){var _1sH=new T(function(){return B(_1p5(_UD,_18E,_1sE));}),_1sI=new T(function(){var _1sJ=function(_1sK,_1sL){while(1){var _1sM=B((function(_1sN,_1sO){var _1sP=E(_1sO);if(!_1sP._){var _1sQ=_1sP.d,_1sR=new T(function(){var _1sS=E(_1sP.b);if(!_1sS._){var _1sT=_1sS.a;if(!E(_1sS.b)._){var _1sU=new T(function(){var _1sV=E(_1sA),_1sW=_1sV.c,_1sX=E(_1sV.a),_1sY=E(_1sV.b);if(_1sX>_1sT){return B(_1sc(_1sT,_1sX,_1sY));}else{if(_1sT>_1sY){return B(_1sc(_1sT,_1sX,_1sY));}else{var _1sZ=_1sT-_1sX|0;if(0>_1sZ){return B(_1pQ(_1sZ,_1sW));}else{if(_1sZ>=_1sW){return B(_1pQ(_1sZ,_1sW));}else{var _1t0=E(_1sV.d[_1sZ]),_1t1=_1t0.d,_1t2=E(_1t0.b),_1t3=E(_1t0.c);if(_1t2<=_1t3){var _1t4=new T(function(){var _1t5=B(_14p(_12I,_1nk,new T2(1,new T2(0,_1pX,new T2(1,_1sT&(-32),1<<(_1sT&31)>>>0)),_4)));return new T2(0,_1t5.a,_1t5.b);}),_1t6=new T(function(){var _1t7=B(_14p(_12I,_1nk,new T2(1,new T2(0,_4,new T2(1,_1sT&(-32),1<<(_1sT&31)>>>0)),_4)));return new T2(0,_1t7.a,_1t7.b);}),_1t8=new T2(1,_1sT&(-32),1<<(_1sT&31)>>>0),_1t9=new T(function(){var _1ta=B(_14p(_12I,_1nk,new T2(1,new T2(0,_4,_1t8),_4)));return new T2(0,_1ta.a,_1ta.b);}),_1tb=new T(function(){var _1tc=B(_14p(_12I,_1nk,new T2(1,new T2(0,_1pZ,new T2(1,_1sT&(-32),1<<(_1sT&31)>>>0)),_4)));return new T2(0,_1tc.a,_1tc.b);}),_1td=function(_1te){var _1tf=E(_1te);if(!_1tf._){return E(_1t9);}else{var _1tg=_1tf.b,_1th=E(_1tf.a);switch(_1th._){case 3:var _1ti=B(_14p(_12I,_1nk,new T2(1,new T2(0,new T2(1,_1th.a,_4),_1t8),_4)));return new T2(0,_1ti.a,_1ti.b);case 4:var _1tj=new T(function(){var _1tk=function(_1tl){var _1tm=E(_1tl);return (_1tm._==0)?__Z:new T2(1,new T(function(){return B(_1td(B(_0(E(_1tm.a).a,_1tg))));}),new T(function(){return B(_1tk(_1tm.b));}));};return B(_1tk(_1th.b));}),_1tn=B(_18u(_12I,_1qA,new T2(1,new T(function(){return B(_1td(B(_0(_1th.a,_1tg))));}),_1tj)));return new T2(0,_1tn.a,_1tn.b);case 5:return E(_1tb);case 6:return E(_1nn);case 7:return E(_1t6);case 8:return E(_1t6);case 9:return E(_1t4);case 10:return E(_1t4);default:return E(_1q0);}}},_1to=new T(function(){return B(_1td(_4));}),_1tp=function(_1tq){var _1tr=new T(function(){var _1ts=E(_1sD),_1tt=_1ts.c,_1tu=E(_1ts.a),_1tv=E(_1ts.b);if(_1t2>_1tq){return B(_1sg(_1t2,_1t3,_1tq));}else{if(_1tq>_1t3){return B(_1sg(_1t2,_1t3,_1tq));}else{var _1tw=_1tq-_1t2|0;if(0>_1tw){return B(_1pQ(_1tw,_1t1));}else{if(_1tw>=_1t1){return B(_1pQ(_1tw,_1t1));}else{var _1tx=_1t0.e["v"]["i32"][_1tw];if(_1tu>_1tx){return B(_1sc(_1tx,_1tu,_1tv));}else{if(_1tx>_1tv){return B(_1sc(_1tx,_1tu,_1tv));}else{var _1ty=_1tx-_1tu|0;if(0>_1ty){return B(_1pQ(_1ty,_1tt));}else{if(_1ty>=_1tt){return B(_1pQ(_1ty,_1tt));}else{var _1tz=E(_1ts.d[_1ty]),_1tA=_1tz.c-1|0;if(0<=_1tA){var _1tB=function(_1tC){return new T2(1,new T(function(){return E(_1tz.d[_1tC]);}),new T(function(){if(_1tC!=_1tA){return B(_1tB(_1tC+1|0));}else{return __Z;}}));};return B(_1td(B(_1tB(0))));}else{return E(_1to);}}}}}}}}}});return new T2(1,new T2(0,_1tq,_1tr),new T(function(){if(_1tq!=_1t3){return B(_1tp(_1tq+1|0));}else{return __Z;}}));};return B(_1pG(_UD,B(_1tp(_1t2))));}else{return E(_1sk);}}}}}});return new T2(1,_1sU,new T(function(){return B(_1sJ(_1sN,_1sQ));}));}else{return B(_1sJ(_1sN,_1sQ));}}else{return B(_1sJ(_1sN,_1sQ));}},1);_1sK=_1sR;_1sL=_1sP.c;return __continue;}else{return E(_1sN);}})(_1sK,_1sL));if(_1sM!=__continue){return _1sM;}}},_1tD=function(_1tE,_1tF,_1tG){while(1){var _1tH=E(_1tG);switch(_1tH._){case 0:var _1tI=B(_1tD(_1tE,_1tF,_1tH.d));_1tE=_1tI.a;_1tF=_1tI.b;_1tG=_1tH.c;continue;case 1:var _1tJ=_1tH.a,_1tK=B(_166(_1pM,_1tH.b)),_1tL=E(_1tK.a);if(!_1tL._){var _1tM=B(_14A(_1tJ,B(_1sl(_1s6,B(_1sJ(_4,_1tL)))),_1tE));}else{var _1tM=E(_1tE);}var _1tN=E(_1tK.b);if(!_1tN._){var _1tO=B(_14A(_1tJ,_1tN,_1tF));}else{var _1tO=E(_1tF);}return new T2(0,_1tM,_1tO);default:return new T2(0,_1tE,_1tF);}}},_1tP=E(_1sH);if(!_1tP._){var _1tQ=_1tP.c,_1tR=_1tP.d;if(_1tP.b>=0){var _1tS=B(_1tD(_UD,_UD,_1tR)),_1tT=B(_1tD(_1tS.a,_1tS.b,_1tQ));return new T2(0,_1tT.a,_1tT.b);}else{var _1tU=B(_1tD(_UD,_UD,_1tQ)),_1tV=B(_1tD(_1tU.a,_1tU.b,_1tR));return new T2(0,_1tV.a,_1tV.b);}}else{var _1tW=B(_1tD(_UD,_UD,_1tP));return new T2(0,_1tW.a,_1tW.b);}}),_1tX=new T(function(){var _1tY=function(_1tZ){var _1u0=E(_1tZ);switch(_1u0._){case 0:var _1u1=_1u0.a;return new T2(1,new T(function(){var _1u2=E(_1sA),_1u3=_1u2.c,_1u4=E(_1u2.a),_1u5=E(_1u2.b);if(_1u4>_1u1){return B(_1sc(_1u1,_1u4,_1u5));}else{if(_1u1>_1u5){return B(_1sc(_1u1,_1u4,_1u5));}else{var _1u6=_1u1-_1u4|0;if(0>_1u6){return B(_1pQ(_1u6,_1u3));}else{if(_1u6>=_1u3){return B(_1pQ(_1u6,_1u3));}else{return E(E(_1u2.d[_1u6]).a);}}}}}),_4);case 1:var _1u7=B(_151(_1u0.a,_1sH));if(!_1u7._){return __Z;}else{return new F(function(){return _1u8(_4,_1u7.a);});}break;default:return E(_1pV);}},_1u8=function(_1u9,_1ua){while(1){var _1ub=B((function(_1uc,_1ud){var _1ue=E(_1ud);if(!_1ue._){var _1uf=new T(function(){return B(_0(B(_1tY(_1ue.b)),new T(function(){return B(_1u8(_1uc,_1ue.d));},1)));},1);_1u9=_1uf;_1ua=_1ue.c;return __continue;}else{return E(_1uc);}})(_1u9,_1ua));if(_1ub!=__continue){return _1ub;}}},_1ug=function(_1uh,_1ui){while(1){var _1uj=B((function(_1uk,_1ul){var _1um=E(_1ul);switch(_1um._){case 0:_1uh=new T(function(){return B(_1ug(_1uk,_1um.d));},1);_1ui=_1um.c;return __continue;case 1:var _1un=function(_1uo,_1up){while(1){var _1uq=B((function(_1ur,_1us){var _1ut=E(_1us);if(!_1ut._){var _1uu=_1ut.b,_1uv=new T(function(){var _1uw=new T(function(){return B(_1un(_1ur,_1ut.d));}),_1ux=function(_1uy){var _1uz=E(_1uy);return (_1uz._==0)?E(_1uw):new T2(1,new T2(0,_1uz.a,new T2(1,_1um.a,new T4(0,1,E(_1uu),E(_MR),E(_MR)))),new T(function(){return B(_1ux(_1uz.b));}));};return B(_1ux(B(_1tY(_1uu))));},1);_1uo=_1uv;_1up=_1ut.c;return __continue;}else{return E(_1ur);}})(_1uo,_1up));if(_1uq!=__continue){return _1uq;}}};return new F(function(){return _1un(_1uk,_1um.b);});break;default:return E(_1uk);}})(_1uh,_1ui));if(_1uj!=__continue){return _1uj;}}},_1uA=E(_1sH);if(!_1uA._){var _1uB=_1uA.c,_1uC=_1uA.d;if(_1uA.b>=0){return B(_13j(_1ng,B(_1ug(new T(function(){return B(_1ug(_4,_1uC));},1),_1uB))));}else{return B(_13j(_1ng,B(_1ug(new T(function(){return B(_1ug(_4,_1uB));},1),_1uC))));}}else{return B(_13j(_1ng,B(_1ug(_4,_1uA))));}});return {_:0,a:_1sy,b:_1sz,c:_1sA,d:_1sB,e:_1sC,f:_1sD,g:_1sE,h:new T(function(){return E(E(_1sI).b);}),i:_1tX,j:_1sF,k:new T(function(){return E(E(_1sI).a);}),l:_1sG};},_1uD=function(_1uE){var _1uF=E(_1uE);return new F(function(){return _1sx(_1uF.a,_1uF.b,_1uF.c,_1uF.d,_1uF.e,_1uF.f,_1uF.g,_1uF.j,_1uF.l);});},_1uG=0,_1uH=function(_1uI){var _1uJ=E(_1uI);return new T3(0,_1uJ.a,_1uJ.b,_1uG);},_1uK=function(_1uL){var _1uM=E(_1uL);return new T4(0,_1uM.a,_1uM.b,new T(function(){var _1uN=E(_1uM.c);if(!_1uN._){return __Z;}else{return new T1(1,new T2(0,_1uN.a,_4));}}),_1uM.d);},_1uO=0,_1uP=new T(function(){return B(unCStr("Negative range size"));}),_1uQ=function(_1uR){var _1uS=function(_){var _1uT=B(_v0(_1uR,0))-1|0,_1uU=function(_1uV){if(_1uV>=0){var _1uW=newArr(_1uV,_VA),_1uX=_1uW,_1uY=function(_1uZ){var _1v0=function(_1v1,_1v2,_){while(1){if(_1v1!=_1uZ){var _1v3=E(_1v2);if(!_1v3._){return _5;}else{var _=_1uX[_1v1]=_1v3.a,_1v4=_1v1+1|0;_1v1=_1v4;_1v2=_1v3.b;continue;}}else{return _5;}}},_1v5=B(_1v0(0,_1uR,_));return new T4(0,E(_1uO),E(_1uT),_1uV,_1uX);};if(0>_1uT){return new F(function(){return _1uY(0);});}else{var _1v6=_1uT+1|0;if(_1v6>=0){return new F(function(){return _1uY(_1v6);});}else{return new F(function(){return err(_1uP);});}}}else{return E(_VC);}};if(0>_1uT){var _1v7=B(_1uU(0)),_1v8=E(_1v7),_1v9=_1v8.d;return new T4(0,E(_1v8.a),E(_1v8.b),_1v8.c,_1v9);}else{var _1va=B(_1uU(_1uT+1|0)),_1vb=E(_1va),_1vc=_1vb.d;return new T4(0,E(_1vb.a),E(_1vb.b),_1vb.c,_1vc);}};return new F(function(){return _8O(_1uS);});},_1vd=function(_1ve){return new T1(3,_1ve);},_1vf=function(_1vg,_1vh){var _1vi=new T(function(){var _1vj=E(_1vg),_1vk=B(_fo(_1vj.a,_1vj.b,_1vj.c,E(_1vh))),_1vl=B(_gl(E(_1vk.a)&4294967295,_g9,_1vj,_1vk.b));return new T2(0,_1vl.a,_1vl.b);});return new T2(0,new T1(3,new T(function(){return E(E(_1vi).a);})),new T(function(){return E(E(_1vi).b);}));},_1vm=function(_1vn,_1vo){var _1vp=B(_1vf(_1vn,_1vo));return new T2(0,_1vp.a,_1vp.b);},_1vq=function(_1vr,_1vs){var _1vt=E(_1vr),_1vu=B(_fo(_1vt.a,_1vt.b,_1vt.c,E(_1vs))),_1vv=B(_gl(E(_1vu.a)&4294967295,_g9,_1vt,_1vu.b));return new T2(0,_1vv.a,_1vv.b);},_1vw=function(_1vx,_1vy,_1vz,_1vA){var _1vB=B(_ZN(_1vm,new T3(0,_1vx,_1vy,_1vz),_1vA)),_1vC=B(_fo(_1vx,_1vy,_1vz,E(_1vB.b))),_1vD=B(_gl(E(_1vC.a)&4294967295,_1vq,new T3(0,_1vx,_1vy,_1vz),_1vC.b));return new T2(0,new T2(0,_1vB.a,_1vD.a),_1vD.b);},_1vE=function(_1vF,_1vG){var _1vH=E(_1vF),_1vI=B(_1vw(_1vH.a,_1vH.b,_1vH.c,_1vG));return new T2(0,_1vI.a,_1vI.b);},_1vJ=function(_1vK){var _1vL=new T(function(){return B(unAppCStr("getSymbol ",new T(function(){return B(_bZ(0,_1vK&4294967295,_4));})));});return new F(function(){return _10d(_1vL);});},_1vM=function(_1vN,_1vO,_1vP,_1vQ){var _1vR=B(_fi(_1vN,_1vO,_1vP,_1vQ)),_1vS=_1vR.b,_1vT=E(_1vR.a);switch(_1vT){case 0:var _1vU=new T(function(){var _1vV=B(_fo(_1vN,_1vO,_1vP,E(_1vS))),_1vW=B(_fo(_1vN,_1vO,_1vP,E(_1vV.b)));return new T2(0,new T(function(){return new T2(0,E(_1vV.a)&4294967295,E(_1vW.a)&4294967295);}),_1vW.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1vU).a);}),_4),new T(function(){return E(E(_1vU).b);}));case 1:var _1vX=new T(function(){var _1vY=B(_fo(_1vN,_1vO,_1vP,E(_1vS))),_1vZ=B(_fo(_1vN,_1vO,_1vP,E(_1vY.b)));return new T2(0,new T(function(){return new T2(1,E(_1vY.a)&4294967295,E(_1vZ.a)&4294967295);}),_1vZ.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1vX).a);}),_4),new T(function(){return E(E(_1vX).b);}));case 2:var _1w0=new T(function(){var _1w1=B(_fo(_1vN,_1vO,_1vP,E(_1vS))),_1w2=B(_fo(_1vN,_1vO,_1vP,E(_1w1.b)));return new T2(0,new T(function(){return new T2(2,E(_1w1.a)&4294967295,E(_1w2.a)&4294967295);}),_1w2.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1w0).a);}),_4),new T(function(){return E(E(_1w0).b);}));case 3:var _1w3=B(_fo(_1vN,_1vO,_1vP,E(_1vS))),_1w4=B(_gl(E(_1w3.a)&4294967295,_1vq,new T3(0,_1vN,_1vO,_1vP),_1w3.b));return new T2(0,new T(function(){return B(_G(_1vd,_1w4.a));}),_1w4.b);case 4:var _1w5=new T(function(){var _1w6=new T3(0,_1vN,_1vO,_1vP),_1w7=B(_ZN(_1vm,_1w6,_1vS)),_1w8=B(_ZN(_1vE,_1w6,_1w7.b));return new T2(0,new T2(4,_1w7.a,_1w8.a),_1w8.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1w5).a);}),_4),new T(function(){return E(E(_1w5).b);}));default:return new F(function(){return _1vJ(_1vT);});}},_1w9=function(_1wa,_1wb){var _1wc=E(_1wa),_1wd=B(_1vM(_1wc.a,_1wc.b,_1wc.c,E(_1wb)));return new T2(0,_1wd.a,_1wd.b);},_1we=function(_1wf){var _1wg=E(_1wf);if(!_1wg._){return __Z;}else{return new F(function(){return _0(_1wg.a,new T(function(){return B(_1we(_1wg.b));},1));});}},_1wh=function(_1wi,_1wj){var _1wk=new T(function(){var _1wl=B(_ZN(_1w9,_1wi,_1wj));return new T2(0,_1wl.a,_1wl.b);});return new T2(0,new T(function(){return B(_1uQ(B(_1we(E(_1wk).a))));}),new T(function(){return E(E(_1wk).b);}));},_1wm=function(_1wn,_1wo,_1wp,_1wq){var _1wr=B(_fo(_1wn,_1wo,_1wp,_1wq));return new F(function(){return _gl(E(_1wr.a)&4294967295,_g9,new T3(0,_1wn,_1wo,_1wp),_1wr.b);});},_1ws=function(_1wt,_1wu){var _1wv=E(_1wt),_1ww=B(_1wm(_1wv.a,_1wv.b,_1wv.c,E(_1wu)));return new T2(0,_1ww.a,_1ww.b);},_1wx=function(_1wy){var _1wz=E(_1wy);return (_1wz._==0)?__Z:new T2(1,new T2(0,_Mf,_1wz.a),new T(function(){return B(_1wx(_1wz.b));}));},_1wA=function(_1wB,_1wC,_1wD,_1wE){var _1wF=B(_fo(_1wB,_1wC,_1wD,_1wE)),_1wG=B(_gl(E(_1wF.a)&4294967295,_kv,new T3(0,_1wB,_1wC,_1wD),_1wF.b)),_1wH=B(_fo(_1wB,_1wC,_1wD,E(_1wG.b))),_1wI=new T(function(){return new T2(0,new T(function(){return B(_1wx(_1wG.a));}),E(_1wH.a)&4294967295);});return new T2(0,_1wI,_1wH.b);},_1wJ=function(_1wK,_1wL){var _1wM=E(_1wK),_1wN=B(_1wA(_1wM.a,_1wM.b,_1wM.c,E(_1wL)));return new T2(0,_1wN.a,_1wN.b);},_1wO=new T(function(){return B(unCStr("getProduction"));}),_1wP=new T(function(){return B(_10d(_1wO));}),_1wQ=function(_1wR,_1wS,_1wT,_1wU){var _1wV=B(_fi(_1wR,_1wS,_1wT,_1wU)),_1wW=_1wV.b;switch(E(_1wV.a)){case 0:var _1wX=B(_fo(_1wR,_1wS,_1wT,E(_1wW))),_1wY=B(_ZN(_1wJ,new T3(0,_1wR,_1wS,_1wT),_1wX.b));return new T2(0,new T(function(){return new T2(0,E(_1wX.a)&4294967295,_1wY.a);}),_1wY.b);case 1:var _1wZ=B(_fo(_1wR,_1wS,_1wT,E(_1wW)));return new T2(0,new T(function(){return new T1(1,E(_1wZ.a)&4294967295);}),_1wZ.b);default:return E(_1wP);}},_1x0=function(_1x1,_1x2){var _1x3=E(_1x1),_1x4=B(_1wQ(_1x3.a,_1x3.b,_1x3.c,E(_1x2)));return new T2(0,_1x4.a,_1x4.b);},_1x5=function(_1x6,_1x7){var _1x8=new T(function(){var _1x9=E(_1x6),_1xa=B(_fo(_1x9.a,_1x9.b,_1x9.c,E(_1x7)));return new T2(0,new T(function(){return E(_1xa.a)&4294967295;}),_1xa.b);}),_1xb=new T(function(){var _1xc=B(_ZN(_1x0,_1x6,new T(function(){return E(E(_1x8).b);},1)));return new T2(0,_1xc.a,_1xc.b);});return new T2(0,new T2(0,new T(function(){return E(E(_1x8).a);}),new T(function(){var _1xd=E(E(_1xb).a);if(!_1xd._){return new T0(1);}else{return B(_Pq(1,new T4(0,1,E(_1xd.a),E(_MR),E(_MR)),_1xd.b));}})),new T(function(){return E(E(_1xb).b);}));},_1xe=function(_1xf,_1xg){var _1xh=B(_1x5(_1xf,_1xg));return new T2(0,_1xh.a,_1xh.b);},_1xi=new T(function(){return B(err(_1uP));}),_1xj=function(_1xk,_1xl,_1xm,_1xn){var _1xo=new T(function(){var _1xp=E(_1xm),_1xq=B(_fo(_1xp.a,_1xp.b,_1xp.c,E(_1xn))),_1xr=E(_1xq.a)&4294967295,_1xs=B(_ZF(_1xr,_1xl,_1xp,_1xq.b));return new T2(0,new T2(0,_1xr,_1xs.a),_1xs.b);}),_1xt=new T(function(){var _1xu=E(E(_1xo).a),_1xv=_1xu.b,_1xw=new T(function(){return E(_1xu.a)-1|0;});return B(A(_jT,[_1xk,_jB,new T2(0,_1uO,_1xw),new T(function(){var _1xx=E(_1xw);if(0>_1xx){return B(_jV(B(_iF(0,-1)),_1xv));}else{var _1xy=_1xx+1|0;if(_1xy>=0){return B(_jV(B(_iF(0,_1xy-1|0)),_1xv));}else{return E(_1xi);}}})]));});return new T2(0,_1xt,new T(function(){return E(E(_1xo).b);}));},_1xz=function(_1xA,_1xB,_1xC,_1xD){var _1xE=B(_fo(_1xA,_1xB,_1xC,_1xD));return new F(function(){return _gl(E(_1xE.a)&4294967295,_g9,new T3(0,_1xA,_1xB,_1xC),_1xE.b);});},_1xF=function(_1xG,_1xH){var _1xI=E(_1xG),_1xJ=B(_1xz(_1xI.a,_1xI.b,_1xI.c,E(_1xH)));return new T2(0,_1xJ.a,_1xJ.b);},_1xK=function(_1xL,_1xM,_1xN,_1xO){var _1xP=B(_fo(_1xL,_1xM,_1xN,_1xO)),_1xQ=B(_fo(_1xL,_1xM,_1xN,E(_1xP.b))),_1xR=B(_1xj(_ij,_1xF,new T3(0,_1xL,_1xM,_1xN),_1xQ.b));return new T2(0,new T(function(){var _1xS=E(_1xR.a);return new T6(0,E(_1xP.a)&4294967295,E(_1xQ.a)&4294967295,E(_1xS.a),E(_1xS.b),_1xS.c,_1xS.d);}),_1xR.b);},_1xT=function(_1xU,_1xV){var _1xW=E(_1xU),_1xX=B(_1xK(_1xW.a,_1xW.b,_1xW.c,E(_1xV)));return new T2(0,_1xX.a,_1xX.b);},_1xY=0,_1xZ=new T(function(){return B(unCStr("Negative range size"));}),_1y0=function(_1y1){var _1y2=B(_v0(_1y1,0)),_1y3=new T(function(){var _1y4=function(_){var _1y5=_1y2-1|0,_1y6=function(_,_1y7){var _1y8=function(_1y9){var _1ya=_1y9-1|0;if(0<=_1ya){var _1yb=function(_1yc,_){while(1){var _=E(_1y7).d["v"]["w8"][_1yc]=0;if(_1yc!=_1ya){var _1yd=_1yc+1|0;_1yc=_1yd;continue;}else{return _5;}}},_1ye=B(_1yb(0,_));return _1y7;}else{return _1y7;}};if(0>_1y5){return new F(function(){return _1y8(0);});}else{var _1yf=_1y5+1|0;if(_1yf>=0){return new F(function(){return _1y8(_1yf);});}else{return new F(function(){return err(_1xZ);});}}},_1yg=function(_,_1yh,_1yi,_1yj,_1yk){var _1yl=function(_1ym){var _1yn=function(_1yo,_1yp,_){while(1){if(_1yo!=_1ym){var _1yq=E(_1yp);if(!_1yq._){return _5;}else{var _=_1yk["v"]["w8"][_1yo]=E(_1yq.a),_1yr=_1yo+1|0;_1yo=_1yr;_1yp=_1yq.b;continue;}}else{return _5;}}},_1ys=B(_1yn(0,_1y1,_));return new T4(0,E(_1yh),E(_1yi),_1yj,_1yk);};if(0>_1y5){return new F(function(){return _1yl(0);});}else{var _1yt=_1y5+1|0;if(_1yt>=0){return new F(function(){return _1yl(_1yt);});}else{return new F(function(){return err(_1xZ);});}}};if(0>_1y5){var _1yu=newByteArr(0),_1yv=B(_1y6(_,new T4(0,E(_1xY),E(_1y5),0,_1yu))),_1yw=E(_1yv);return new F(function(){return _1yg(_,_1yw.a,_1yw.b,_1yw.c,_1yw.d);});}else{var _1yx=_1y5+1|0,_1yy=newByteArr(_1yx),_1yz=B(_1y6(_,new T4(0,E(_1xY),E(_1y5),_1yx,_1yy))),_1yA=E(_1yz);return new F(function(){return _1yg(_,_1yA.a,_1yA.b,_1yA.c,_1yA.d);});}};return B(_8O(_1y4));});return new T3(0,0,_1y2,_1y3);},_1yB=function(_1yC){return new F(function(){return _bZ(0,E(_1yC)&4294967295,_4);});},_1yD=function(_1yE,_1yF){return new F(function(){return _bZ(0,E(_1yE)&4294967295,_1yF);});},_1yG=function(_1yH,_1yI){return new F(function(){return _3X(_1yD,_1yH,_1yI);});},_1yJ=function(_1yK,_1yL,_1yM){return new F(function(){return _bZ(E(_1yK),E(_1yL)&4294967295,_1yM);});},_1yN=new T3(0,_1yJ,_1yB,_1yG),_1yO=new T(function(){return B(unCStr("Word8"));}),_1yP=0,_1yQ=255,_1yR=new T2(0,_1yP,_1yQ),_1yS=new T2(1,_bX,_4),_1yT=function(_1yU,_1yV,_1yW,_1yX){var _1yY=new T(function(){var _1yZ=new T(function(){var _1z0=new T(function(){var _1z1=new T(function(){var _1z2=new T(function(){var _1z3=E(_1yW),_1z4=new T(function(){return B(A3(_em,_ec,new T2(1,new T(function(){return B(A3(_ey,_1yX,_ex,_1z3.a));}),new T2(1,new T(function(){return B(A3(_ey,_1yX,_ex,_1z3.b));}),_4)),_1yS));});return new T2(1,_bY,_1z4);});return B(unAppCStr(") is outside of bounds ",_1z2));},1);return B(_0(B(_bZ(0,E(_1yV),_4)),_1z1));});return B(unAppCStr("}: tag (",_1z0));},1);return B(_0(_1yU,_1yZ));});return new F(function(){return err(B(unAppCStr("Enum.toEnum{",_1yY)));});},_1z5=function(_1z6,_1z7,_1z8,_1z9){return new F(function(){return _1yT(_1z7,_1z8,_1z9,_1z6);});},_1za=function(_1zb){return new F(function(){return _1z5(_1yN,_1yO,_1zb,_1yR);});},_1zc=function(_1zd){if(_1zd<0){return new F(function(){return _1za(_1zd);});}else{if(_1zd>255){return new F(function(){return _1za(_1zd);});}else{return _1zd>>>0;}}},_1ze=function(_1zf){return new F(function(){return _1zc(E(_1zf));});},_1zg=function(_1zh){var _1zi=E(_1zh);if(!_1zi._){return __Z;}else{var _1zj=_1zi.b,_1zk=E(_1zi.a),_1zl=function(_1zm){return (_1zk>=2048)?new T2(1,new T(function(){var _1zn=224+B(_n8(_1zk,4096))|0;if(_1zn>>>0>1114111){return B(_fQ(_1zn));}else{return _1zn;}}),new T2(1,new T(function(){var _1zo=128+B(_n8(B(_oc(_1zk,4096)),64))|0;if(_1zo>>>0>1114111){return B(_fQ(_1zo));}else{return _1zo;}}),new T2(1,new T(function(){var _1zp=128+B(_oc(_1zk,64))|0;if(_1zp>>>0>1114111){return B(_fQ(_1zp));}else{return _1zp;}}),new T(function(){return B(_1zg(_1zj));})))):new T2(1,new T(function(){var _1zq=192+B(_n8(_1zk,64))|0;if(_1zq>>>0>1114111){return B(_fQ(_1zq));}else{return _1zq;}}),new T2(1,new T(function(){var _1zr=128+B(_oc(_1zk,64))|0;if(_1zr>>>0>1114111){return B(_fQ(_1zr));}else{return _1zr;}}),new T(function(){return B(_1zg(_1zj));})));};if(_1zk<=0){return new F(function(){return _1zl(_);});}else{if(_1zk>=128){return new F(function(){return _1zl(_);});}else{return new T2(1,_1zk,new T(function(){return B(_1zg(_1zj));}));}}}},_1zs=new T(function(){return B(unCStr("linref"));}),_1zt=new T(function(){return B(_1zg(_1zs));}),_1zu=new T(function(){return B(_G(_1ze,_1zt));}),_1zv=new T(function(){var _1zw=B(_1y0(_1zu));return new T3(0,_1zw.a,_1zw.b,_1zw.c);}),_1zx=function(_1zy,_1zz){var _1zA=E(_1zy),_1zB=B(_fz(_1zA.a,_1zA.b,_1zA.c,E(_1zz))),_1zC=B(_1xj(_m8,_kv,_1zA,_1zB.b));return new T2(0,new T(function(){var _1zD=E(_1zC.a);return new T5(0,_1zB.a,E(_1zD.a),E(_1zD.b),_1zD.c,_1zD.d);}),_1zC.b);},_1zE=new T(function(){return B(_1pG(_UD,_4));}),_1zF=new T2(0,0,0),_1zG=new T2(1,_1zF,_4),_1zH=new T(function(){return B(_1uQ(_1zG));}),_1zI=new T2(1,_1zH,_4),_1zJ=function(_1zK,_1zL,_1zM,_1zN){var _1zO=new T3(0,_1zK,_1zL,_1zM),_1zP=B(_ZW(_12e,_129,_1zO,_1zN)),_1zQ=B(_ZW(_12e,_1ws,_1zO,_1zP.b)),_1zR=B(_fo(_1zK,_1zL,_1zM,E(_1zQ.b))),_1zS=E(_1zR.a)&4294967295,_1zT=B(_ZF(_1zS,_1wh,_1zO,_1zR.b)),_1zU=B(_fo(_1zK,_1zL,_1zM,E(_1zT.b))),_1zV=E(_1zU.a)&4294967295,_1zW=B(_ZF(_1zV,_1zx,_1zO,_1zU.b)),_1zX=B(_QZ(_Q0,_1zK,_1zL,_1zM,E(_1zW.b))),_1zY=new T(function(){var _1zZ=B(_ZN(_1xe,_1zO,_1zX.b));return new T2(0,_1zZ.a,_1zZ.b);}),_1A0=B(_ZW(_12e,_1xT,_1zO,new T(function(){return E(E(_1zY).b);},1))),_1A1=B(_fo(_1zK,_1zL,_1zM,E(_1A0.b))),_1A2=new T(function(){var _1A3=E(_1A1.a)&4294967295,_1A4=new T(function(){var _1A5=function(_){var _1A6=(_1zS+1|0)-1|0,_1A7=function(_1A8){if(_1A8>=0){var _1A9=newArr(_1A8,_VA),_1Aa=_1A9,_1Ab=function(_1Ac){var _1Ad=function(_1Ae,_1Af,_){while(1){if(_1Ae!=_1Ac){var _1Ag=E(_1Af);if(!_1Ag._){return _5;}else{var _=_1Aa[_1Ae]=_1Ag.a,_1Ah=_1Ae+1|0;_1Ae=_1Ah;_1Af=_1Ag.b;continue;}}else{return _5;}}},_1Ai=B(_1Ad(0,new T(function(){return B(_0(_1zT.a,_1zI));},1),_));return new T4(0,E(_1uO),E(_1A6),_1A8,_1Aa);};if(0>_1A6){return new F(function(){return _1Ab(0);});}else{var _1Aj=_1A6+1|0;if(_1Aj>=0){return new F(function(){return _1Ab(_1Aj);});}else{return E(_1xi);}}}else{return E(_VC);}};if(0>_1A6){var _1Ak=B(_1A7(0)),_1Al=E(_1Ak),_1Am=_1Al.d;return new T4(0,E(_1Al.a),E(_1Al.b),_1Al.c,_1Am);}else{var _1An=B(_1A7(_1A6+1|0)),_1Ao=E(_1An),_1Ap=_1Ao.d;return new T4(0,E(_1Ao.a),E(_1Ao.b),_1Ao.c,_1Ap);}};return B(_8O(_1A5));}),_1Aq=new T(function(){var _1Ar=_1A3-1|0;if(0<=_1Ar){var _1As=function(_1At){return new T2(1,new T2(0,_1At,new T2(1,_1zV,_4)),new T(function(){if(_1At!=_1Ar){return B(_1As(_1At+1|0));}else{return __Z;}}));};return B(_1pG(_UD,B(_1As(0))));}else{return E(_1zE);}}),_1Au=new T(function(){var _1Av=function(_){var _1Aw=(_1zV+1|0)-1|0,_1Ax=function(_1Ay){if(_1Ay>=0){var _1Az=newArr(_1Ay,_VA),_1AA=_1Az,_1AB=function(_1AC){var _1AD=function(_1AE,_1AF,_){while(1){if(_1AE!=_1AC){var _1AG=E(_1AF);if(!_1AG._){return _5;}else{var _=_1AA[_1AE]=_1AG.a,_1AH=_1AE+1|0;_1AE=_1AH;_1AF=_1AG.b;continue;}}else{return _5;}}},_1AI=new T(function(){var _1AJ=new T(function(){var _1AK=function(_){var _1AL=newByteArr(4),_1AM=_1AL,_1AN=function(_1AO,_){while(1){var _=_1AM["v"]["i32"][_1AO]=0,_1AP=E(_1AO);if(!_1AP){return _5;}else{_1AO=_1AP+1|0;continue;}}},_1AQ=B(_1AN(0,_)),_1AR=function(_1AS,_1AT,_){while(1){var _1AU=E(_1AS);if(_1AU==1){return _5;}else{var _1AV=E(_1AT);if(!_1AV._){return _5;}else{var _=_1AM["v"]["i32"][_1AU]=E(_1AV.a);_1AS=_1AU+1|0;_1AT=_1AV.b;continue;}}}},_1AW=B(_1AR(0,new T2(1,_1zS,_4),_));return new T4(0,E(_1uO),E(_1uO),1,_1AM);},_1AX=B(_8O(_1AK));return new T5(0,_1zv,E(_1AX.a),E(_1AX.b),_1AX.c,_1AX.d);});return B(_0(_1zW.a,new T2(1,_1AJ,_4)));},1),_1AY=B(_1AD(0,_1AI,_));return new T4(0,E(_1uO),E(_1Aw),_1Ay,_1AA);};if(0>_1Aw){return new F(function(){return _1AB(0);});}else{var _1AZ=_1Aw+1|0;if(_1AZ>=0){return new F(function(){return _1AB(_1AZ);});}else{return E(_1xi);}}}else{return E(_VC);}};if(0>_1Aw){var _1B0=B(_1Ax(0)),_1B1=E(_1B0),_1B2=_1B1.d;return new T4(0,E(_1B1.a),E(_1B1.b),_1B1.c,_1B2);}else{var _1B3=B(_1Ax(_1Aw+1|0)),_1B4=E(_1B3),_1B5=_1B4.d;return new T4(0,E(_1B4.a),E(_1B4.b),_1B4.c,_1B5);}};return B(_8O(_1Av));});return {_:0,a:_1zP.a,b:_1zQ.a,c:_1Au,d:_1zX.a,e:_1Aq,f:_1A4,g:new T(function(){var _1B6=E(E(_1zY).a);if(!_1B6._){return new T0(2);}else{var _1B7=E(_1B6.a);return B(_Qi(E(_1B7.a),_1B7.b,_1B6.b,_Q1));}}),h:_UD,i:_Rm,j:_1A0.a,k:_UD,l:_1A3};});return new T2(0,_1A2,_1A1.b);},_1B8=function(_1B9,_1Ba){var _1Bb=E(_1B9),_1Bc=B(_1zJ(_1Bb.a,_1Bb.b,_1Bb.c,_1Ba));return new T2(0,_1Bc.a,_1Bc.b);},_1Bd=function(_1Be,_1Bf){var _1Bg=E(_1Be),_1Bh=B(_J4(_Jz,_LR,_1Bg,_1Bf)),_1Bi=B(_fz(_1Bg.a,_1Bg.b,_1Bg.c,E(_1Bh.b)));return new T2(0,new T2(0,_1Bh.a,_1Bi.a),_1Bi.b);},_1Bj=function(_1Bk,_1Bl){var _1Bm=new T(function(){var _1Bn=B(_ZN(_119,_1Bk,_1Bl));return new T2(0,_1Bn.a,_1Bn.b);}),_1Bo=B(_ZN(_1Bd,_1Bk,new T(function(){return E(E(_1Bm).b);},1)));return new T2(0,new T2(0,new T(function(){return E(E(_1Bm).a);}),_1Bo.a),_1Bo.b);},_1Bp=function(_1Bq,_1Br){var _1Bs=B(_1Bj(_1Bq,_1Br));return new T2(0,_1Bs.a,_1Bs.b);},_1Bt=function(_1Bu,_1Bv,_1Bw,_1Bx,_1By){var _1Bz=B(_fz(_1Bv,_1Bw,_1Bx,_1By)),_1BA=new T3(0,_1Bv,_1Bw,_1Bx),_1BB=B(_ZW(_12e,_129,_1BA,_1Bz.b)),_1BC=B(_ZW(_12e,_124,_1BA,_1BB.b)),_1BD=B(_ZW(_12e,_1Bp,_1BA,_1BC.b)),_1BE=B(_ZW(_12e,_1B8,_1BA,_1BD.b));return new T2(0,new T4(0,_1Bu,_1Bz.a,new T3(0,_1BB.a,new T(function(){return B(_Zm(_1uK,_1BC.a));}),new T(function(){return B(_Zm(_1uH,_1BD.a));})),new T(function(){return B(_Zm(_1uD,_1BE.a));})),_1BE.b);},_1BF=function(_1BG,_1BH,_1BI,_1BJ){var _1BK=B(_ZW(_12e,_129,new T3(0,_1BG,_1BH,_1BI),_1BJ));return new F(function(){return _1Bt(_1BK.a,_1BG,_1BH,_1BI,E(_1BK.b));});},_1BL=function(_1BM,_1BN){var _1BO=E(_1BN);return new F(function(){return _1sx(_1BO.a,_1BO.b,_1BO.c,_1BO.d,_1BO.e,_1BO.f,_1BO.g,_1BO.j,_1BO.l);});},_1BP=function(_1BQ,_1BR,_1BS,_1BT){var _1BU=new T3(0,_1BQ,_1BR,_1BS),_1BV=B(_Wp(_1BU,_1BT)),_1BW=B(_Wp(_1BU,_1BV.b)),_1BX=_1BW.a,_1BY=_1BW.b,_1BZ=E(_1BV.a),_1C0=function(_1C1){var _1C2=E(_1BZ);if(_1C2==1){var _1C3=E(_1BX);if(!E(_1C3)){return new F(function(){return _1BF(_1BQ,_1BR,_1BS,_1BY);});}else{return new F(function(){return _Wj(_1C3,1);});}}else{return new F(function(){return _Wj(_1BX,_1C2);});}};if(E(_1BZ)==2){if(E(_1BX)>1){return new F(function(){return _1C0(_);});}else{var _1C4=B(_Uq(_fN,_Mc,_1BQ,_1BR,_1BS,E(_1BY))),_1C5=B(_fz(_1BQ,_1BR,_1BS,E(_1C4.b))),_1C6=B(_Zq(_1BQ,_1BR,_1BS,E(_1C5.b))),_1C7=_1C6.a,_1C8=B(_Uq(_fN,_Wh,_1BQ,_1BR,_1BS,E(_1C6.b))),_1C9=new T(function(){return B(_Zm(function(_1Ca){return new F(function(){return _1BL(_1C7,_1Ca);});},_1C8.a));});return new T2(0,new T4(0,_1C4.a,_1C5.a,_1C7,_1C9),_1C8.b);}}else{return new F(function(){return _1C0(_);});}},_1Cb=0,_1Cc=new T(function(){return new T2(0,_18F,_1Cd);}),_1Cd=function(_1Ce,_1Cf){return (!B(A3(_pS,_1Cc,_1Ce,_1Cf)))?true:false;},_1Cg=new T2(0,_18F,_1Cd),_1Ch=function(_1Ci,_1Cj){var _1Ck=E(_1Ci);if(!_1Ck._){var _1Cl=E(_1Cj);if(!_1Cl._){var _1Cm=E(_1Ck.a),_1Cn=E(_1Cl.a);if(!B(_12S(_1Cm.a,_1Cm.b,_1Cm.c,_1Cn.a,_1Cn.b,_1Cn.c))){return false;}else{return new F(function(){return _18U(_1Cg,_1Ck.b,_1Cl.b);});}}else{return false;}}else{return (E(_1Cj)._==0)?false:true;}},_1Co=function(_1Cp,_1Cq){return (!B(_1Cr(_1Cp,_1Cq)))?true:false;},_1Cs=new T(function(){return new T2(0,_1Cr,_1Co);}),_1Cr=function(_1Ct,_1Cu){var _1Cv=E(_1Ct);if(!_1Cv._){var _1Cw=E(_1Cu);if(!_1Cw._){var _1Cx=E(_1Cv.a),_1Cy=E(_1Cw.a);if(!B(_12S(_1Cx.a,_1Cx.b,_1Cx.c,_1Cy.a,_1Cy.b,_1Cy.c))){return false;}else{if(!B(_1Ch(_1Cv.b,_1Cw.b))){return false;}else{return new F(function(){return _18U(_1Cs,_1Cv.c,_1Cw.c);});}}}else{return false;}}else{var _1Cz=E(_1Cu);if(!_1Cz._){return false;}else{return new F(function(){return _18F(_1Cv.a,_1Cz.a);});}}},_1CA=new T(function(){return B(unCStr("()"));}),_1CB=new T(function(){return B(unCStr(")"));}),_1CC=function(_1CD){var _1CE=E(_1CD);if(_1CE==95){return true;}else{var _1CF=function(_1CG){if(_1CE<65){if(_1CE<192){return false;}else{if(_1CE>255){return false;}else{switch(E(_1CE)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1CE>90){if(_1CE<192){return false;}else{if(_1CE>255){return false;}else{switch(E(_1CE)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1CE<97){return new F(function(){return _1CF(_);});}else{if(_1CE>122){return new F(function(){return _1CF(_);});}else{return true;}}}},_1CH=new T(function(){return B(unCStr("UTF8.decodeUTF8: bad data"));}),_1CI=function(_1CJ){return new F(function(){return err(_1CH);});},_1CK=new T(function(){return B(_1CI(_));}),_1CL=function(_1CM){var _1CN=E(_1CM);if(!_1CN._){return __Z;}else{var _1CO=_1CN.b,_1CP=E(_1CN.a);if(_1CP>=128){var _1CQ=E(_1CO);if(!_1CQ._){return E(_1CK);}else{var _1CR=_1CQ.a,_1CS=_1CQ.b,_1CT=function(_1CU){var _1CV=E(_1CS);if(!_1CV._){return E(_1CK);}else{if(224>_1CP){return E(_1CK);}else{if(_1CP>239){return E(_1CK);}else{var _1CW=E(_1CR);if(128>_1CW){return E(_1CK);}else{if(_1CW>191){return E(_1CK);}else{var _1CX=E(_1CV.a);return (128>_1CX)?E(_1CK):(_1CX>191)?E(_1CK):new T2(1,new T(function(){var _1CY=((imul(B(_oc(_1CP,16)),4096)|0)+(imul(B(_oc(_1CW,64)),64)|0)|0)+B(_oc(_1CX,64))|0;if(_1CY>>>0>1114111){return B(_fQ(_1CY));}else{return _1CY;}}),new T(function(){return B(_1CL(_1CV.b));}));}}}}}};if(192>_1CP){return new F(function(){return _1CT(_);});}else{if(_1CP>223){return new F(function(){return _1CT(_);});}else{var _1CZ=E(_1CR);if(128>_1CZ){return new F(function(){return _1CT(_);});}else{if(_1CZ>191){return new F(function(){return _1CT(_);});}else{return new T2(1,new T(function(){var _1D0=(imul(B(_oc(_1CP,32)),64)|0)+B(_oc(_1CZ,64))|0;if(_1D0>>>0>1114111){return B(_fQ(_1D0));}else{return _1D0;}}),new T(function(){return B(_1CL(_1CS));}));}}}}}}else{return new T2(1,_1CP,new T(function(){return B(_1CL(_1CO));}));}}},_1D1=function(_1D2){var _1D3=E(_1D2);switch(_1D3){case 39:return true;case 95:return true;default:var _1D4=function(_1D5){var _1D6=function(_1D7){if(_1D3<65){if(_1D3<192){return false;}else{if(_1D3>255){return false;}else{switch(E(_1D3)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1D3>90){if(_1D3<192){return false;}else{if(_1D3>255){return false;}else{switch(E(_1D3)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1D3<97){return new F(function(){return _1D6(_);});}else{if(_1D3>122){return new F(function(){return _1D6(_);});}else{return true;}}};if(_1D3<48){return new F(function(){return _1D4(_);});}else{if(_1D3>57){return new F(function(){return _1D4(_);});}else{return true;}}}},_1D8=function(_1D9){while(1){var _1Da=E(_1D9);if(!_1Da._){return true;}else{if(!B(_1D1(E(_1Da.a)))){return false;}else{_1D9=_1Da.b;continue;}}}},_1Db=new T(function(){return B(unCStr("\\\\"));}),_1Dc=new T(function(){return B(unCStr("\\\'"));}),_1Dd=new T(function(){return B(unCStr("\'"));}),_1De=function(_1Df){var _1Dg=E(_1Df);if(!_1Dg._){return E(_1Dd);}else{var _1Dh=_1Dg.b,_1Di=E(_1Dg.a);switch(E(_1Di)){case 39:return new F(function(){return _0(_1Dc,new T(function(){return B(_1De(_1Dh));},1));});break;case 92:return new F(function(){return _0(_1Db,new T(function(){return B(_1De(_1Dh));},1));});break;default:return new T2(1,_1Di,new T(function(){return B(_1De(_1Dh));}));}}},_1Dj=function(_1Dk){var _1Dl=E(_1Dk);return (_1Dl._==0)?__Z:new T2(1,new T(function(){return B(_12J(_1Dl.a));}),new T(function(){return B(_1Dj(_1Dl.b));}));},_1Dm=function(_1Dn,_1Do,_1Dp){var _1Dq=B(_1CL(B(_1Dj(new T(function(){return B(_IP(_1Dn,_1Do,_1Dp));})))));if(!_1Dq._){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1De(_4));}));});}else{if(!B(_1CC(E(_1Dq.a)))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1De(_1Dq));}));});}else{if(!B(_1D8(_1Dq.b))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1De(_1Dq));}));});}else{return E(_1Dq);}}}},_1Dr=function(_1Ds,_1Dt){while(1){var _1Du=B((function(_1Dv,_1Dw){var _1Dx=E(_1Dv);if(!_1Dx._){return E(_1Dw);}else{var _1Dy=new T(function(){return B(unAppCStr(" -> ",new T(function(){var _1Dz=E(_1Dx.a);return B(_1Dm(_1Dz.a,_1Dz.b,_1Dz.c));})));},1),_1DA=B(_0(_1Dw,_1Dy));_1Ds=_1Dx.b;_1Dt=_1DA;return __continue;}})(_1Ds,_1Dt));if(_1Du!=__continue){return _1Du;}}},_1DB=function(_1DC){var _1DD=E(_1DC);if(!_1DD._){var _1DE=_1DD.a,_1DF=E(_1DD.b);if(!_1DF._){return new F(function(){return unAppCStr("(",new T(function(){var _1DG=E(_1DE);return B(_0(B(_1Dm(_1DG.a,_1DG.b,_1DG.c)),_1CB));}));});}else{var _1DH=new T(function(){var _1DI=E(_1DF.a),_1DJ=new T(function(){return B(unAppCStr(" -> ",new T(function(){var _1DK=E(_1DE);return B(_0(B(_1Dm(_1DK.a,_1DK.b,_1DK.c)),_1CB));})));},1);return B(_0(B(_1Dr(_1DF.b,B(_1Dm(_1DI.a,_1DI.b,_1DI.c)))),_1DJ));});return new F(function(){return unAppCStr("(",_1DH);});}}else{return E(_1CA);}},_1DL=32,_1DM=function(_1DN){var _1DO=E(_1DN);if(!_1DO._){return __Z;}else{var _1DP=new T(function(){return B(_0(B(_1DQ(_1DO.a)),new T(function(){return B(_1DM(_1DO.b));},1)));});return new T2(1,_1DL,_1DP);}},_1DR=new T(function(){return B(unCStr("}"));}),_1DS=new T(function(){return B(_0(_4,_1DR));}),_1DQ=function(_1DT){var _1DU=E(_1DT);if(!_1DU._){var _1DV=_1DU.a,_1DW=_1DU.b,_1DX=E(_1DU.c);if(!_1DX._){var _1DY=new T(function(){var _1DZ=E(_1DV),_1E0=new T(function(){return B(unAppCStr(":",new T(function(){return B(_0(B(_1DB(_1DW)),_1DR));})));},1);return B(_0(B(_1Dm(_1DZ.a,_1DZ.b,_1DZ.c)),_1E0));});return new F(function(){return unAppCStr("{",_1DY);});}else{var _1E1=new T(function(){var _1E2=E(_1DV),_1E3=new T(function(){var _1E4=new T(function(){var _1E5=new T(function(){return B(unAppCStr(" ",new T(function(){var _1E6=B(_1DM(_1DX));if(!_1E6._){return E(_1DS);}else{return B(_0(_1E6.b,_1DR));}})));},1);return B(_0(B(_1DB(_1DW)),_1E5));});return B(unAppCStr(":",_1E4));},1);return B(_0(B(_1Dm(_1E2.a,_1E2.b,_1E2.c)),_1E3));});return new F(function(){return unAppCStr("{",_1E1);});}}else{return new F(function(){return unAppCStr("{?",new T(function(){var _1E7=E(_1DU.a);return B(_0(B(_1Dm(_1E7.a,_1E7.b,_1E7.c)),_1DR));}));});}},_1E8=new T(function(){return B(unCStr("!!: negative index"));}),_1E9=new T(function(){return B(_0(_eh,_1E8));}),_1Ea=new T(function(){return B(err(_1E9));}),_1Eb=new T(function(){return B(unCStr("!!: index too large"));}),_1Ec=new T(function(){return B(_0(_eh,_1Eb));}),_1Ed=new T(function(){return B(err(_1Ec));}),_1Ee=function(_1Ef,_1Eg){while(1){var _1Eh=E(_1Ef);if(!_1Eh._){return E(_1Ed);}else{var _1Ei=E(_1Eg);if(!_1Ei){return E(_1Eh.a);}else{_1Ef=_1Eh.b;_1Eg=_1Ei-1|0;continue;}}}},_1Ej=function(_1Ek,_1El){if(_1El>=0){return new F(function(){return _1Ee(_1Ek,_1El);});}else{return E(_1Ea);}},_1Em=function(_1En,_1Eo){var _1Ep=E(_1En);if(!_1Ep._){var _1Eq=E(_1Ep.c);if(!_1Eq._){return __Z;}else{var _1Er=E(_1Eo);return (_1Er>=0)?(_1Er<B(_v0(_1Eq,0)))?new T1(1,new T(function(){return B(_1Ej(_1Eq,_1Er));})):__Z:__Z;}}else{return __Z;}},_1Es=function(_1Et,_1Eu){while(1){var _1Ev=B((function(_1Ew,_1Ex){var _1Ey=E(_1Ex);if(!_1Ey._){return new T1(1,_1Ew);}else{var _1Ez=_1Ey.a,_1EA=E(_1Ey.b);if(!_1EA._){return new F(function(){return _1Em(_1Ew,_1Ez);});}else{var _1EB=E(_1Ew);if(!_1EB._){var _1EC=E(_1EB.c);if(!_1EC._){return __Z;}else{var _1ED=E(_1Ez);if(_1ED>=0){if(_1ED<B(_v0(_1EC,0))){_1Et=new T(function(){return B(_1Ej(_1EC,_1ED));});_1Eu=_1EA;return __continue;}else{return __Z;}}else{return __Z;}}}else{return __Z;}}}})(_1Et,_1Eu));if(_1Ev!=__continue){return _1Ev;}}},_1EE=function(_1EF,_1EG){var _1EH=E(_1EG);if(!_1EH._){return __Z;}else{var _1EI=_1EH.a,_1EJ=E(_1EF);return (_1EJ==1)?new T2(1,_1EI,_4):new T2(1,_1EI,new T(function(){return B(_1EE(_1EJ-1|0,_1EH.b));}));}},_1EK=new T(function(){return B(unCStr("suggestionList"));}),_1EL=new T(function(){return B(err(_rq));}),_1EM=new T(function(){return B(err(_rs));}),_1EN=new T(function(){return B(unCStr("_"));}),_1EO=92,_1EP=39,_1EQ=function(_1ER){var _1ES=E(_1ER);if(!_1ES._){return __Z;}else{var _1ET=_1ES.b,_1EU=E(_1ES.a);switch(E(_1EU)){case 39:return __Z;case 92:var _1EV=E(_1ET);if(!_1EV._){return __Z;}else{var _1EW=_1EV.b;switch(E(_1EV.a)){case 39:return new T2(1,new T2(0,_1EP,_1EW),_4);case 92:return new T2(1,new T2(0,_1EO,_1EW),_4);default:return __Z;}}break;default:return new T2(1,new T2(0,_1EU,_1ET),_4);}}},_1EX=function(_1EY,_1EZ){var _1F0=function(_1F1){var _1F2=E(_1F1);if(!_1F2._){return __Z;}else{var _1F3=E(_1F2.a);return new F(function(){return _0(B(_rx(B(A1(_1EZ,_1F3.a)),_1F3.b)),new T(function(){return B(_1F0(_1F2.b));},1));});}};return function(_1F4){var _1F5=B(_1F0(B(A1(_1EY,_1F4))));return (_1F5._==0)?new T0(2):new T1(4,_1F5);};},_1F6=function(_1F7){return new T1(1,B(_1EX(_1EQ,_1F7)));},_1F8=function(_1F9,_1Fa){var _1Fb=new T(function(){var _1Fc=function(_1Fd){return new F(function(){return _1F8(_1F9,function(_1Fe){return new F(function(){return A1(_1Fa,new T2(1,_1Fd,_1Fe));});});});};return B(A1(_1F9,_1Fc));});return new F(function(){return _rH(B(A1(_1Fa,_4)),_1Fb);});},_1Ff=function(_1Fg){var _1Fh=function(_1Fi){var _1Fj=E(_1Fi);if(!_1Fj._){return __Z;}else{var _1Fk=E(_1Fj.a),_1Fl=function(_1Fm){var _1Fn=new T(function(){return B(A1(_1Fg,new T2(1,_1Fk.a,_1Fm)));});return new T1(0,function(_1Fo){return (E(_1Fo)==39)?E(_1Fn):new T0(2);});};return new F(function(){return _0(B(_rx(B(_1F8(_1F6,_1Fl)),_1Fk.b)),new T(function(){return B(_1Fh(_1Fj.b));},1));});}},_1Fp=function(_1Fq){var _1Fr=B(_1Fh(B(_1EQ(_1Fq))));return (_1Fr._==0)?new T0(2):new T1(4,_1Fr);};return function(_1Fs){return (E(_1Fs)==39)?E(new T1(1,_1Fp)):new T0(2);};},_1Ft=function(_1Fu){var _1Fv=B(_1y0(B(_G(_1ze,B(_1zg(_1Fu))))));return new T3(0,_1Fv.a,_1Fv.b,_1Fv.c);},_1Fw=function(_1Fx){return new F(function(){return _1D1(E(_1Fx));});},_1Fy=function(_1Fz){var _1FA=function(_1FB){if(!B(_sl(_1FB,_1EN))){return new F(function(){return A1(_1Fz,new T(function(){return B(_1Ft(_1FB));}));});}else{return new T0(2);}},_1FC=function(_1FD){var _1FE=E(_1FD);return (!B(_1CC(_1FE)))?new T0(2):new T1(1,B(_tq(_1Fw,function(_1FF){return new F(function(){return _1FA(new T2(1,_1FE,_1FF));});})));};return new F(function(){return _rH(new T1(0,_1FC),new T(function(){return new T1(0,B(_1Ff(_1FA)));}));});},_1FG=new T(function(){return B(_1Fy(_sS));}),_1FH=function(_1FI,_1FJ){while(1){var _1FK=E(_1FI);if(!_1FK._){return E(_1FJ);}else{_1FI=_1FK.b;_1FJ=_1FK.a;continue;}}},_1FL=function(_1FM){return E(E(_1FM).a);},_1FN=function(_1FO){return E(E(_1FO).b);},_1FP=function(_1FQ,_1FR){var _1FS=new T(function(){var _1FT=B(_1FU(B(_1FN(_1FQ))));return new T2(0,_1FT.a,_1FT.b);});return new T2(0,new T2(1,new T(function(){return B(_1FL(_1FQ));}),new T(function(){return B(_1FL(_1FS));})),new T(function(){return B(_1FN(_1FS));}));},_1FU=function(_1FV){var _1FW=E(_1FV);if(!_1FW._){return new T2(0,_4,_4);}else{if(E(_1FW.a)==32){var _1FX=B(_1FY(_1FW.b));if(!_1FX._){return new T2(0,_4,_1FW);}else{return new F(function(){return _1FP(_1FX.a,_1FX.b);});}}else{var _1FZ=B(_1FY(_1FW));if(!_1FZ._){return new T2(0,_4,_1FW);}else{return new F(function(){return _1FP(_1FZ.a,_1FZ.b);});}}}},_1G0=new T(function(){return B(unCStr("?"));}),_1G1=new T(function(){return B(_1zg(_1G0));}),_1G2=new T(function(){return B(_G(_1ze,_1G1));}),_1G3=new T(function(){var _1G4=B(_1y0(_1G2));return new T3(0,_1G4.a,_1G4.b,_1G4.c);}),_1G5=new T2(0,_1G3,_4),_1G6=new T1(1,_1G5),_1G7=new T(function(){return B(_rx(_1FG,_4));}),_1G8=function(_1G9){var _1Ga=E(_1G9);if(!_1Ga._){var _1Gb=E(_1G7);return (_1Gb._==0)?__Z:new T1(1,_1Gb.a);}else{if(E(_1Ga.a)==63){var _1Gc=B(_1G8(_1Ga.b));if(!_1Gc._){return E(_1G6);}else{var _1Gd=E(_1Gc.a),_1Ge=new T(function(){var _1Gf=B(_1y0(B(_G(_1ze,B(_1zg(B(unAppCStr("?",new T(function(){var _1Gg=E(_1Gd.a);return B(_1Dm(_1Gg.a,_1Gg.b,_1Gg.c));})))))))));return new T3(0,_1Gf.a,_1Gf.b,_1Gf.c);});return new T1(1,new T2(0,_1Ge,_1Gd.b));}}else{var _1Gh=B(_rx(_1FG,_1Ga));return (_1Gh._==0)?__Z:new T1(1,_1Gh.a);}}},_1Gi=function(_1Gj){while(1){var _1Gk=B((function(_1Gl){var _1Gm=E(_1Gl);if(!_1Gm._){return new T2(0,_4,_4);}else{var _1Gn=_1Gm.b,_1Go=function(_1Gp){var _1Gq=B(_1G8(_1Gm));if(!_1Gq._){return new T2(0,_4,_1Gm);}else{var _1Gr=_1Gq.a,_1Gs=new T(function(){var _1Gt=B(_1Gi(B(_1FN(_1Gr))));return new T2(0,_1Gt.a,_1Gt.b);});return new T2(0,new T2(1,new T(function(){return B(_1FL(_1Gr));}),new T(function(){return B(_1FL(_1Gs));})),new T(function(){return B(_1FN(_1Gs));}));}};switch(E(_1Gm.a)){case 32:_1Gj=_1Gn;return __continue;case 40:_1Gj=_1Gn;return __continue;case 41:return new T2(0,_4,_1Gn);case 45:var _1Gu=E(_1Gn);if(!_1Gu._){return new F(function(){return _1Go(_);});}else{if(E(_1Gu.a)==62){_1Gj=_1Gu.b;return __continue;}else{return new F(function(){return _1Go(_);});}}break;default:return new F(function(){return _1Go(_);});}}})(_1Gj));if(_1Gk!=__continue){return _1Gk;}}},_1Gv=new T(function(){return B(unCStr("?"));}),_1Gw=function(_1Gx){var _1Gy=E(_1Gx);if(!_1Gy._){var _1Gz=E(_1Gy.b);if(!_1Gz._){return E(_1Gz.a);}else{return new F(function(){return _1Ft(_1Gv);});}}else{return E(_1Gy.a);}},_1GA=new T(function(){return B(_1zg(_1Gv));}),_1GB=new T(function(){return B(_G(_1ze,_1GA));}),_1GC=new T(function(){var _1GD=B(_1y0(_1GB));return new T3(0,_1GD.a,_1GD.b,_1GD.c);}),_1GE=new T2(0,_1GC,_4),_1GF=function(_1GG){var _1GH=E(_1GG);if(!_1GH._){var _1GI=_1GH.c,_1GJ=new T(function(){var _1GK=E(_1GH.b);if(!_1GK._){if(!E(_1GK.b)._){return new T2(0,_1GK.a,new T(function(){return B(_G(_1Gw,_1GI));}));}else{return E(_1GK);}}else{return E(_1GE);}});return new T3(0,_1GH.a,_1GJ,new T(function(){return B(_G(_1GF,_1GI));}));}else{return E(_1GH);}},_1GL=function(_1GM,_1GN){var _1GO=E(_1GN);return (_1GO._==0)?__Z:new T2(1,_1GM,new T(function(){return B(_1GL(_1GO.a,_1GO.b));}));},_1GP=new T(function(){return B(unCStr("last"));}),_1GQ=new T(function(){return B(_ei(_1GP));}),_1GR=function(_1GS){var _1GT=E(_1GS);return new T2(0,new T1(1,_1GT.a),new T(function(){var _1GU=E(_1GT.b);if(!_1GU._){return __Z;}else{if(E(_1GU.a)==125){return E(_1GU.b);}else{return E(_1GU);}}}));},_1FY=function(_1GV){var _1GW=E(_1GV);if(!_1GW._){var _1GX=__Z;}else{if(E(_1GW.a)==123){var _1GY=E(_1GW.b);}else{var _1GY=E(_1GW);}var _1GX=_1GY;}var _1GZ=function(_1H0){var _1H1=B(_1G8(_1GX));if(!_1H1._){return __Z;}else{var _1H2=E(_1H1.a),_1H3=function(_1H4){var _1H5=new T(function(){var _1H6=E(E(_1H4).b);if(!_1H6._){var _1H7=B(_1FU(_4));return new T2(0,_1H7.a,_1H7.b);}else{var _1H8=_1H6.b;switch(E(_1H6.a)){case 32:var _1H9=E(_1H8);if(!_1H9._){var _1Ha=B(_1FU(_4));return new T2(0,_1Ha.a,_1Ha.b);}else{if(E(_1H9.a)==123){var _1Hb=B(_1FU(_1H9.b));return new T2(0,_1Hb.a,_1Hb.b);}else{var _1Hc=B(_1FU(_1H9));return new T2(0,_1Hc.a,_1Hc.b);}}break;case 123:var _1Hd=B(_1FU(_1H8));return new T2(0,_1Hd.a,_1Hd.b);break;default:var _1He=B(_1FU(_1H6));return new T2(0,_1He.a,_1He.b);}}}),_1Hf=new T(function(){return B(_1GF(new T3(0,_1H2.a,new T(function(){return B(_1FL(_1H4));}),new T(function(){return B(_1FL(_1H5));}))));});return new T2(1,new T2(0,_1Hf,new T(function(){var _1Hg=E(E(_1H5).b);if(!_1Hg._){return __Z;}else{if(E(_1Hg.a)==125){return E(_1Hg.b);}else{return E(_1Hg);}}})),_4);},_1Hh=E(_1H2.b);if(!_1Hh._){var _1Hi=B(_1Gi(_4)),_1Hj=E(_1Hi.a);if(!_1Hj._){return __Z;}else{return new F(function(){return _1H3(new T2(0,new T2(0,new T(function(){return B(_1FH(_1Hj,_1GQ));}),new T(function(){return B(_1GL(_1Hj.a,_1Hj.b));})),_1Hi.b));});}}else{if(E(_1Hh.a)==58){var _1Hk=B(_1Gi(_1Hh.b)),_1Hl=E(_1Hk.a);if(!_1Hl._){return __Z;}else{return new F(function(){return _1H3(new T2(0,new T2(0,new T(function(){return B(_1FH(_1Hl,_1GQ));}),new T(function(){return B(_1GL(_1Hl.a,_1Hl.b));})),_1Hk.b));});}}else{var _1Hm=B(_1Gi(_1Hh)),_1Hn=E(_1Hm.a);if(!_1Hn._){return __Z;}else{return new F(function(){return _1H3(new T2(0,new T2(0,new T(function(){return B(_1FH(_1Hn,_1GQ));}),new T(function(){return B(_1GL(_1Hn.a,_1Hn.b));})),_1Hm.b));});}}}}},_1Ho=E(_1GX);if(!_1Ho._){return new F(function(){return _1GZ(_);});}else{if(E(_1Ho.a)==63){return new F(function(){return _G(_1GR,B(_rx(_1FG,_1Ho.b)));});}else{return new F(function(){return _1GZ(_);});}}},_1Hp=function(_1Hq){var _1Hr=E(_1Hq);if(!_1Hr._){return __Z;}else{var _1Hs=E(_1Hr.a),_1Ht=function(_1Hu){return E(new T2(3,_1Hs.a,_sR));};return new F(function(){return _0(B(_rx(new T1(1,function(_1Hv){return new F(function(){return A2(_BE,_1Hv,_1Ht);});}),_1Hs.b)),new T(function(){return B(_1Hp(_1Hr.b));},1));});}},_1Hw=function(_1Hx){var _1Hy=B(_1Hp(B(_1FY(_1Hx))));return (_1Hy._==0)?new T0(2):new T1(4,_1Hy);},_1Hz=new T1(1,_1Hw),_1HA=new T(function(){return B(unCStr("{Pred:(Item->Quality->Comment) {These:(Kind->Item) {Fish:Kind}} {Boring:Quality}}"));}),_1HB=new T(function(){return B(_rx(_1Hz,_1HA));}),_1HC=new T(function(){var _1HD=B(_Iz(_1HB));if(!_1HD._){return E(_1EL);}else{if(!E(_1HD.b)._){return E(_1HD.a);}else{return E(_1EM);}}}),_1HE=new T(function(){return B(unCStr("hover"));}),_1HF=new T(function(){return eval("(function(e,c) {e.classList.toggle(c);})");}),_1HG=function(_1HH,_){var _1HI=__app2(E(_1HF),_1HH,toJSStr(E(_1HE)));return new F(function(){return _u(_);});},_1HJ=6,_1HK=5,_1HL=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1HM=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_1HN=new T(function(){return B(unCStr("div"));}),_1HO=new T(function(){return eval("(function(s){return document.createTextNode(s);})");}),_1HP=function(_1HQ){return E(E(_1HQ).a);},_1HR=function(_1HS){return E(E(_1HS).b);},_1HT=function(_1HU){return E(E(_1HU).a);},_1HV=function(_){return new F(function(){return nMV(_4l);});},_1HW=new T(function(){return B(_z(_1HV));}),_1HX=function(_1HY){return E(E(_1HY).b);},_1HZ=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1I0=function(_1I1,_1I2,_1I3,_1I4,_1I5,_1I6){var _1I7=B(_1HP(_1I1)),_1I8=B(_2z(_1I7)),_1I9=new T(function(){return B(_6i(_1I7));}),_1Ia=new T(function(){return B(_dh(_1I8));}),_1Ib=new T(function(){return B(A1(_1I2,_1I4));}),_1Ic=new T(function(){return B(A2(_1HT,_1I3,_1I5));}),_1Id=function(_1Ie){return new F(function(){return A1(_1Ia,new T3(0,_1Ic,_1Ib,_1Ie));});},_1If=function(_1Ig){var _1Ih=new T(function(){var _1Ii=new T(function(){var _1Ij=__createJSFunc(2,function(_1Ik,_){var _1Il=B(A2(E(_1Ig),_1Ik,_));return _D;}),_1Im=_1Ij;return function(_){return new F(function(){return __app3(E(_1HZ),E(_1Ib),E(_1Ic),_1Im);});};});return B(A1(_1I9,_1Ii));});return new F(function(){return A3(_1V,_1I8,_1Ih,_1Id);});},_1In=new T(function(){var _1Io=new T(function(){return B(_6i(_1I7));}),_1Ip=function(_1Iq){var _1Ir=new T(function(){return B(A1(_1Io,function(_){var _=wMV(E(_1HW),new T1(1,_1Iq));return new F(function(){return A(_1HR,[_1I3,_1I5,_1Iq,_]);});}));});return new F(function(){return A3(_1V,_1I8,_1Ir,_1I6);});};return B(A2(_1HX,_1I1,_1Ip));});return new F(function(){return A3(_1V,_1I8,_1In,_1If);});},_1Is=function(_1It,_1Iu,_1Iv,_){var _1Iw=__app1(E(_1HO),toJSStr(E(_1Iu))),_1Ix=__app1(E(_1HL),toJSStr(E(_1HN))),_1Iy=_1Ix,_1Iz=B(A(_1I0,[_do,_df,_de,_1Iy,_1HK,function(_1IA,_){return new F(function(){return _1HG(_1Iy,_);});},_])),_1IB=B(A(_1I0,[_do,_df,_de,_1Iy,_1HJ,function(_1IC,_){return new F(function(){return _1HG(_1Iy,_);});},_])),_1ID=B(A(_1I0,[_do,_df,_de,_1Iy,_1Cb,_1Iv,_])),_1IE=E(_1HM),_1IF=__app2(_1IE,_1Iw,_1Iy),_1IG=__app2(_1IE,_1Iy,E(_1It));return _5;},_1IH=function(_){return new F(function(){return __app1(E(_1HL),"div");});},_1II=new T(function(){return eval("(function(e){while(e.firstChild){e.removeChild(e.firstChild);}})");}),_1IJ=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1IK=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:77:5-14"));}),_1IL=new T(function(){return B(unCStr("score"));}),_1IM=function(_1IN,_){var _1IO=__app1(E(_1IJ),toJSStr(E(_1IL))),_1IP=__eq(_1IO,E(_D)),_1IQ=function(_,_1IR){var _1IS=E(_1IR);if(!_1IS._){return new F(function(){return _bC(_1IK,_);});}else{var _1IT=rMV(E(_1IN)),_1IU=E(_1IS.a),_1IV=__app1(E(_1II),_1IU),_1IW=__app1(E(_1HO),toJSStr(B(_bZ(0,E(E(_1IT).e),_4)))),_1IX=__app2(E(_1HM),_1IW,_1IU);return new F(function(){return _u(_);});}};if(!E(_1IP)){var _1IY=__isUndef(_1IO);if(!E(_1IY)){return new F(function(){return _1IQ(_,new T1(1,_1IO));});}else{return new F(function(){return _1IQ(_,_4l);});}}else{return new F(function(){return _1IQ(_,_4l);});}},_1IZ=new T(function(){return eval("(function(c,p){p.removeChild(c);})");}),_1J0=new T(function(){return eval("document.body");}),_1J1=function(_,_1J2){var _1J3=E(_1J2);if(!_1J3._){return _5;}else{var _1J4=E(_1J3.a),_1J5=__app1(E(_1II),_1J4),_1J6=__app2(E(_1IZ),_1J4,E(_1J0));return new F(function(){return _u(_);});}},_1J7=function(_1J8,_){var _1J9=__app1(E(_1IJ),toJSStr(E(_1J8))),_1Ja=__eq(_1J9,E(_D));if(!E(_1Ja)){var _1Jb=__isUndef(_1J9);if(!E(_1Jb)){return new F(function(){return _1J1(_,new T1(1,_1J9));});}else{return new F(function(){return _1J1(_,_4l);});}}else{return new F(function(){return _1J1(_,_4l);});}},_1Jc=new T(function(){return eval("alert");}),_1Jd=3,_1Je=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1Jf=new T(function(){return B(err(_1Je));}),_1Jg=function(_1Jh){return new F(function(){return fromJSStr(E(_1Jh));});},_1Ji=function(_1Jj){return E(E(_1Jj).a);},_1Jk=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_1Jl=function(_1Jm,_1Jn,_1Jo,_1Jp){var _1Jq=new T(function(){var _1Jr=function(_){var _1Js=__app2(E(_1Jk),B(A2(_1Ji,_1Jm,_1Jo)),E(_1Jp));return new T(function(){return String(_1Js);});};return E(_1Jr);});return new F(function(){return A2(_6i,_1Jn,_1Jq);});},_1Jt=function(_1Ju,_1Jv,_1Jw,_1Jx){var _1Jy=B(_2z(_1Jv)),_1Jz=new T(function(){return B(_dh(_1Jy));}),_1JA=function(_1JB){return new F(function(){return A1(_1Jz,new T(function(){return B(_1Jg(_1JB));}));});},_1JC=new T(function(){return B(_1Jl(_1Ju,_1Jv,_1Jw,new T(function(){return toJSStr(E(_1Jx));},1)));});return new F(function(){return A3(_1V,_1Jy,_1JC,_1JA);});},_1JD=function(_1JE,_1JF){while(1){var _1JG=E(_1JE);if(!_1JG._){return (E(_1JF)._==0)?true:false;}else{var _1JH=E(_1JF);if(!_1JH._){return false;}else{if(E(_1JG.a)!=E(_1JH.a)){return false;}else{_1JE=_1JG.b;_1JF=_1JH.b;continue;}}}}},_1JI=function(_1JJ,_1JK,_1JL,_1JM){if(!B(_1JD(_1JJ,_1JL))){return false;}else{return new F(function(){return _1Cr(_1JK,_1JM);});}},_1JN=function(_1JO,_1JP){var _1JQ=E(_1JO),_1JR=E(_1JP);return new F(function(){return _1JI(_1JQ.a,_1JQ.b,_1JR.a,_1JR.b);});},_1JS=function(_1JT,_1JU,_1JV,_1JW){return (!B(_1JD(_1JT,_1JV)))?true:(!B(_1Cr(_1JU,_1JW)))?true:false;},_1JX=function(_1JY,_1JZ){var _1K0=E(_1JY),_1K1=E(_1JZ);return new F(function(){return _1JS(_1K0.a,_1K0.b,_1K1.a,_1K1.b);});},_1K2=new T2(0,_1JN,_1JX),_1K3=function(_1K4,_1K5){var _1K6=E(_1K4),_1K7=E(_1K5);return (!B(_1Cr(_1K6.a,_1K7.a)))?true:(!B(_1nv(_1K2,_1K6.b,_1K7.b)))?true:false;},_1K8=function(_1K9,_1Ka,_1Kb,_1Kc){if(!B(_1Cr(_1K9,_1Kb))){return false;}else{return new F(function(){return _1nv(_1K2,_1Ka,_1Kc);});}},_1Kd=function(_1Ke,_1Kf){var _1Kg=E(_1Ke),_1Kh=E(_1Kf);return new F(function(){return _1K8(_1Kg.a,_1Kg.b,_1Kh.a,_1Kh.b);});},_1Ki=new T2(0,_1Kd,_1K3),_1Kj=function(_1Kk,_1Kl){var _1Km=E(_1Kk),_1Kn=E(_1Kl);return (B(_12Z(_1Km.a,_1Km.b,_1Km.c,_1Kn.a,_1Kn.b,_1Kn.c))==0)?true:false;},_1Ko=function(_1Kp){var _1Kq=E(_1Kp);return new F(function(){return _G(_12J,B(_IP(_1Kq.a,_1Kq.b,_1Kq.c)));});},_1Kr=function(_1Ks,_1Kt){return (B(_12j(B(_1Ko(_1Ks)),B(_1Ko(_1Kt))))==2)?false:true;},_1Ku=function(_1Kv,_1Kw){var _1Kx=E(_1Kv),_1Ky=E(_1Kw);return (B(_12Z(_1Kx.a,_1Kx.b,_1Kx.c,_1Ky.a,_1Ky.b,_1Ky.c))==2)?true:false;},_1Kz=function(_1KA,_1KB){var _1KC=E(_1KA),_1KD=E(_1KB);return (B(_12Z(_1KC.a,_1KC.b,_1KC.c,_1KD.a,_1KD.b,_1KD.c))==0)?false:true;},_1KE=function(_1KF,_1KG){return (B(_12j(B(_1Ko(_1KF)),B(_1Ko(_1KG))))==2)?E(_1KF):E(_1KG);},_1KH=function(_1KI,_1KJ){return (B(_12j(B(_1Ko(_1KI)),B(_1Ko(_1KJ))))==2)?E(_1KJ):E(_1KI);},_1KK={_:0,a:_1Cg,b:_1b7,c:_1Kj,d:_1Kr,e:_1Ku,f:_1Kz,g:_1KE,h:_1KH},_1KL=function(_1KM,_1KN){var _1KO=E(_1KM);if(!_1KO._){var _1KP=E(_1KN);if(!_1KP._){var _1KQ=E(_1KO.a),_1KR=E(_1KP.a);switch(B(_12Z(_1KQ.a,_1KQ.b,_1KQ.c,_1KR.a,_1KR.b,_1KR.c))){case 0:return 0;case 1:return new F(function(){return _1bJ(_1KK,_1KO.b,_1KP.b);});break;default:return 2;}}else{return 0;}}else{return (E(_1KN)._==0)?2:1;}},_1KS=function(_1KT,_1KU){var _1KV=E(_1KT);if(!_1KV._){var _1KW=E(_1KU);if(!_1KW._){var _1KX=E(_1KV.a),_1KY=E(_1KW.a);switch(B(_12Z(_1KX.a,_1KX.b,_1KX.c,_1KY.a,_1KY.b,_1KY.c))){case 0:return true;case 1:switch(B(_1KL(_1KV.b,_1KW.b))){case 0:return true;case 1:return (B(_1bJ(_1KZ,_1KV.c,_1KW.c))==0)?true:false;default:return false;}break;default:return false;}}else{return true;}}else{var _1L0=E(_1KU);if(!_1L0._){return false;}else{return new F(function(){return _1Kj(_1KV.a,_1L0.a);});}}},_1L1=function(_1L2,_1L3){var _1L4=E(_1L2);if(!_1L4._){var _1L5=E(_1L3);if(!_1L5._){var _1L6=E(_1L4.a),_1L7=E(_1L5.a);switch(B(_12Z(_1L6.a,_1L6.b,_1L6.c,_1L7.a,_1L7.b,_1L7.c))){case 0:return true;case 1:switch(B(_1KL(_1L4.b,_1L5.b))){case 0:return true;case 1:return (B(_1bJ(_1KZ,_1L4.c,_1L5.c))==2)?false:true;default:return false;}break;default:return false;}}else{return true;}}else{var _1L8=E(_1L3);if(!_1L8._){return false;}else{return new F(function(){return _1Kr(_1L4.a,_1L8.a);});}}},_1L9=function(_1La,_1Lb){var _1Lc=E(_1La);if(!_1Lc._){var _1Ld=E(_1Lb);if(!_1Ld._){var _1Le=E(_1Lc.a),_1Lf=E(_1Ld.a);switch(B(_12Z(_1Le.a,_1Le.b,_1Le.c,_1Lf.a,_1Lf.b,_1Lf.c))){case 0:return false;case 1:switch(B(_1KL(_1Lc.b,_1Ld.b))){case 0:return false;case 1:return (B(_1bJ(_1KZ,_1Lc.c,_1Ld.c))==2)?true:false;default:return true;}break;default:return true;}}else{return false;}}else{var _1Lg=E(_1Lb);if(!_1Lg._){return true;}else{return new F(function(){return _1Ku(_1Lc.a,_1Lg.a);});}}},_1Lh=function(_1Li,_1Lj){var _1Lk=E(_1Li);if(!_1Lk._){var _1Ll=E(_1Lj);if(!_1Ll._){var _1Lm=E(_1Lk.a),_1Ln=E(_1Ll.a);switch(B(_12Z(_1Lm.a,_1Lm.b,_1Lm.c,_1Ln.a,_1Ln.b,_1Ln.c))){case 0:return false;case 1:switch(B(_1KL(_1Lk.b,_1Ll.b))){case 0:return false;case 1:return (B(_1bJ(_1KZ,_1Lk.c,_1Ll.c))==0)?false:true;default:return true;}break;default:return true;}}else{return false;}}else{var _1Lo=E(_1Lj);if(!_1Lo._){return true;}else{return new F(function(){return _1Kz(_1Lk.a,_1Lo.a);});}}},_1Lp=function(_1Lq,_1Lr){return (!B(_1L1(_1Lq,_1Lr)))?E(_1Lq):E(_1Lr);},_1Ls=function(_1Lt,_1Lu){return (!B(_1L1(_1Lt,_1Lu)))?E(_1Lu):E(_1Lt);},_1KZ=new T(function(){return {_:0,a:_1Cs,b:_1Lv,c:_1KS,d:_1L1,e:_1L9,f:_1Lh,g:_1Lp,h:_1Ls};}),_1Lv=function(_1Lw,_1Lx){var _1Ly=E(_1Lw);if(!_1Ly._){var _1Lz=E(_1Lx);if(!_1Lz._){var _1LA=E(_1Ly.a),_1LB=E(_1Lz.a);switch(B(_12Z(_1LA.a,_1LA.b,_1LA.c,_1LB.a,_1LB.b,_1LB.c))){case 0:return 0;case 1:switch(B(_1KL(_1Ly.b,_1Lz.b))){case 0:return 0;case 1:return new F(function(){return _1bJ(_1KZ,_1Ly.c,_1Lz.c);});break;default:return 2;}break;default:return 2;}}else{return 0;}}else{var _1LC=E(_1Lx);if(!_1LC._){return 2;}else{return new F(function(){return _1b7(_1Ly.a,_1LC.a);});}}},_1LD=function(_1LE,_1LF){while(1){var _1LG=E(_1LE);if(!_1LG._){return (E(_1LF)._==0)?1:0;}else{var _1LH=E(_1LF);if(!_1LH._){return 2;}else{var _1LI=E(_1LG.a),_1LJ=E(_1LH.a);if(_1LI>=_1LJ){if(_1LI!=_1LJ){return 2;}else{_1LE=_1LG.b;_1LF=_1LH.b;continue;}}else{return 0;}}}}},_1LK=function(_1LL,_1LM,_1LN,_1LO){switch(B(_1LD(_1LL,_1LN))){case 0:return 0;case 1:return new F(function(){return _1Lv(_1LM,_1LO);});break;default:return 2;}},_1LP=function(_1LQ,_1LR){var _1LS=E(_1LQ),_1LT=E(_1LR);return new F(function(){return _1LK(_1LS.a,_1LS.b,_1LT.a,_1LT.b);});},_1LU=function(_1LV,_1LW,_1LX,_1LY){switch(B(_1LD(_1LV,_1LX))){case 0:return true;case 1:return new F(function(){return _1KS(_1LW,_1LY);});break;default:return false;}},_1LZ=function(_1M0,_1M1){var _1M2=E(_1M0),_1M3=E(_1M1);return new F(function(){return _1LU(_1M2.a,_1M2.b,_1M3.a,_1M3.b);});},_1M4=function(_1M5,_1M6,_1M7,_1M8){switch(B(_1LD(_1M5,_1M7))){case 0:return true;case 1:return new F(function(){return _1L1(_1M6,_1M8);});break;default:return false;}},_1M9=function(_1Ma,_1Mb){var _1Mc=E(_1Ma),_1Md=E(_1Mb);return new F(function(){return _1M4(_1Mc.a,_1Mc.b,_1Md.a,_1Md.b);});},_1Me=function(_1Mf,_1Mg,_1Mh,_1Mi){switch(B(_1LD(_1Mf,_1Mh))){case 0:return false;case 1:return new F(function(){return _1L9(_1Mg,_1Mi);});break;default:return true;}},_1Mj=function(_1Mk,_1Ml){var _1Mm=E(_1Mk),_1Mn=E(_1Ml);return new F(function(){return _1Me(_1Mm.a,_1Mm.b,_1Mn.a,_1Mn.b);});},_1Mo=function(_1Mp,_1Mq,_1Mr,_1Ms){switch(B(_1LD(_1Mp,_1Mr))){case 0:return false;case 1:return new F(function(){return _1Lh(_1Mq,_1Ms);});break;default:return true;}},_1Mt=function(_1Mu,_1Mv){var _1Mw=E(_1Mu),_1Mx=E(_1Mv);return new F(function(){return _1Mo(_1Mw.a,_1Mw.b,_1Mx.a,_1Mx.b);});},_1My=function(_1Mz,_1MA){var _1MB=E(_1Mz),_1MC=E(_1MA);switch(B(_1LD(_1MB.a,_1MC.a))){case 0:return E(_1MC);case 1:return (!B(_1L1(_1MB.b,_1MC.b)))?E(_1MB):E(_1MC);default:return E(_1MB);}},_1MD=function(_1ME,_1MF){var _1MG=E(_1ME),_1MH=E(_1MF);switch(B(_1LD(_1MG.a,_1MH.a))){case 0:return E(_1MG);case 1:return (!B(_1L1(_1MG.b,_1MH.b)))?E(_1MH):E(_1MG);default:return E(_1MH);}},_1MI={_:0,a:_1K2,b:_1LP,c:_1LZ,d:_1M9,e:_1Mj,f:_1Mt,g:_1My,h:_1MD},_1MJ=function(_1MK){return new F(function(){return _1no(_4,_1MK);});},_1ML=function(_1MM,_1MN,_1MO,_1MP){switch(B(_1Lv(_1MM,_1MO))){case 0:return true;case 1:return (B(_1bJ(_1MI,B(_1MJ(_1MN)),B(_1MJ(_1MP))))==0)?true:false;default:return false;}},_1MQ=function(_1MR,_1MS){var _1MT=E(_1MR),_1MU=E(_1MS);return new F(function(){return _1ML(_1MT.a,_1MT.b,_1MU.a,_1MU.b);});},_1MV=function(_1MW,_1MX,_1MY,_1MZ){switch(B(_1Lv(_1MW,_1MY))){case 0:return true;case 1:return (B(_1bJ(_1MI,B(_1MJ(_1MX)),B(_1MJ(_1MZ))))==2)?false:true;default:return false;}},_1N0=function(_1N1,_1N2){var _1N3=E(_1N1),_1N4=E(_1N2);return new F(function(){return _1MV(_1N3.a,_1N3.b,_1N4.a,_1N4.b);});},_1N5=function(_1N6,_1N7,_1N8,_1N9){switch(B(_1Lv(_1N6,_1N8))){case 0:return false;case 1:return (B(_1bJ(_1MI,B(_1MJ(_1N7)),B(_1MJ(_1N9))))==2)?true:false;default:return true;}},_1Na=function(_1Nb,_1Nc){var _1Nd=E(_1Nb),_1Ne=E(_1Nc);return new F(function(){return _1N5(_1Nd.a,_1Nd.b,_1Ne.a,_1Ne.b);});},_1Nf=function(_1Ng,_1Nh,_1Ni,_1Nj){switch(B(_1Lv(_1Ng,_1Ni))){case 0:return false;case 1:return (B(_1bJ(_1MI,B(_1MJ(_1Nh)),B(_1MJ(_1Nj))))==0)?false:true;default:return true;}},_1Nk=function(_1Nl,_1Nm){var _1Nn=E(_1Nl),_1No=E(_1Nm);return new F(function(){return _1Nf(_1Nn.a,_1Nn.b,_1No.a,_1No.b);});},_1Np=function(_1Nq,_1Nr,_1Ns,_1Nt){switch(B(_1Lv(_1Nq,_1Ns))){case 0:return 0;case 1:return new F(function(){return _1bJ(_1MI,B(_1MJ(_1Nr)),B(_1MJ(_1Nt)));});break;default:return 2;}},_1Nu=function(_1Nv,_1Nw){var _1Nx=E(_1Nv),_1Ny=E(_1Nw);return new F(function(){return _1Np(_1Nx.a,_1Nx.b,_1Ny.a,_1Ny.b);});},_1Nz=function(_1NA,_1NB){var _1NC=E(_1NA),_1ND=E(_1NB);switch(B(_1Lv(_1NC.a,_1ND.a))){case 0:return E(_1ND);case 1:return (B(_1bJ(_1MI,B(_1MJ(_1NC.b)),B(_1MJ(_1ND.b))))==2)?E(_1NC):E(_1ND);default:return E(_1NC);}},_1NE=function(_1NF,_1NG){var _1NH=E(_1NF),_1NI=E(_1NG);switch(B(_1Lv(_1NH.a,_1NI.a))){case 0:return E(_1NH);case 1:return (B(_1bJ(_1MI,B(_1MJ(_1NH.b)),B(_1MJ(_1NI.b))))==2)?E(_1NI):E(_1NH);default:return E(_1NI);}},_1NJ={_:0,a:_1Ki,b:_1Nu,c:_1MQ,d:_1N0,e:_1Na,f:_1Nk,g:_1Nz,h:_1NE},_1NK=function(_1NL,_1NM,_1NN){var _1NO=E(_1NN);if(!_1NO._){var _1NP=_1NO.c,_1NQ=_1NO.d,_1NR=E(_1NO.b);switch(B(_1Lv(_1NL,_1NR.a))){case 0:return new F(function(){return _Ny(_1NR,B(_1NK(_1NL,_1NM,_1NP)),_1NQ);});break;case 1:switch(B(_1bJ(_1MI,B(_1MJ(_1NM)),B(_1MJ(_1NR.b))))){case 0:return new F(function(){return _Ny(_1NR,B(_1NK(_1NL,_1NM,_1NP)),_1NQ);});break;case 1:return new F(function(){return _15o(_1NP,_1NQ);});break;default:return new F(function(){return _MW(_1NR,_1NP,B(_1NK(_1NL,_1NM,_1NQ)));});}break;default:return new F(function(){return _MW(_1NR,_1NP,B(_1NK(_1NL,_1NM,_1NQ)));});}}else{return new T0(1);}},_1NS=function(_1NT,_1NU){var _1NV=E(_1NT),_1NW=E(_1NU);if(!_1NW._){var _1NX=_1NW.b,_1NY=_1NW.c,_1NZ=_1NW.d;switch(B(_1bJ(_1NJ,B(_1no(_4,_1NV)),B(_1no(_4,_1NX))))){case 0:return new F(function(){return _MW(_1NX,B(_1NS(_1NV,_1NY)),_1NZ);});break;case 1:return new T4(0,_1NW.a,E(_1NV),E(_1NY),E(_1NZ));default:return new F(function(){return _Ny(_1NX,_1NY,B(_1NS(_1NV,_1NZ)));});}}else{return new T4(0,1,E(_1NV),E(_MR),E(_MR));}},_1O0=function(_1O1,_1O2){while(1){var _1O3=E(_1O2);if(!_1O3._){return E(_1O1);}else{var _1O4=B(_1NS(_1O3.a,_1O1));_1O1=_1O4;_1O2=_1O3.b;continue;}}},_1O5=function(_1O6,_1O7){var _1O8=E(_1O7);if(!_1O8._){return new T3(0,_MR,_4,_4);}else{var _1O9=_1O8.a,_1Oa=E(_1O6);if(_1Oa==1){var _1Ob=E(_1O8.b);return (_1Ob._==0)?new T3(0,new T(function(){return new T4(0,1,E(_1O9),E(_MR),E(_MR));}),_4,_4):(B(_1bJ(_1NJ,B(_1MJ(_1O9)),B(_1MJ(_1Ob.a))))==0)?new T3(0,new T(function(){return new T4(0,1,E(_1O9),E(_MR),E(_MR));}),_1Ob,_4):new T3(0,new T(function(){return new T4(0,1,E(_1O9),E(_MR),E(_MR));}),_4,_1Ob);}else{var _1Oc=B(_1O5(_1Oa>>1,_1O8)),_1Od=_1Oc.a,_1Oe=_1Oc.c,_1Of=E(_1Oc.b);if(!_1Of._){return new T3(0,_1Od,_4,_1Oe);}else{var _1Og=_1Of.a,_1Oh=E(_1Of.b);if(!_1Oh._){return new T3(0,new T(function(){return B(_Oe(_1Og,_1Od));}),_4,_1Oe);}else{if(!B(_1bJ(_1NJ,B(_1MJ(_1Og)),B(_1MJ(_1Oh.a))))){var _1Oi=B(_1O5(_1Oa>>1,_1Oh));return new T3(0,new T(function(){return B(_OS(_1Og,_1Od,_1Oi.a));}),_1Oi.b,_1Oi.c);}else{return new T3(0,_1Od,_4,_1Of);}}}}}},_1Oj=function(_1Ok,_1Ol,_1Om){while(1){var _1On=E(_1Om);if(!_1On._){return E(_1Ol);}else{var _1Oo=_1On.a,_1Op=E(_1On.b);if(!_1Op._){return new F(function(){return _Oe(_1Oo,_1Ol);});}else{if(!B(_1bJ(_1NJ,B(_1MJ(_1Oo)),B(_1MJ(_1Op.a))))){var _1Oq=B(_1O5(_1Ok,_1Op)),_1Or=_1Oq.a,_1Os=E(_1Oq.c);if(!_1Os._){var _1Ot=_1Ok<<1,_1Ou=B(_OS(_1Oo,_1Ol,_1Or));_1Ok=_1Ot;_1Ol=_1Ou;_1Om=_1Oq.b;continue;}else{return new F(function(){return _1O0(B(_OS(_1Oo,_1Ol,_1Or)),_1Os);});}}else{return new F(function(){return _1O0(_1Ol,_1On);});}}}}},_1Ov=function(_1Ow){var _1Ox=E(_1Ow);if(!_1Ox._){return new T0(1);}else{var _1Oy=_1Ox.a,_1Oz=E(_1Ox.b);if(!_1Oz._){return new T4(0,1,E(_1Oy),E(_MR),E(_MR));}else{if(!B(_1bJ(_1NJ,B(_1MJ(_1Oy)),B(_1MJ(_1Oz.a))))){return new F(function(){return _1Oj(1,new T4(0,1,E(_1Oy),E(_MR),E(_MR)),_1Oz);});}else{return new F(function(){return _1O0(new T4(0,1,E(_1Oy),E(_MR),E(_MR)),_1Oz);});}}}},_1OA=function(_1OB,_1OC){while(1){var _1OD=E(_1OC);if(!_1OD._){return E(_1OB);}else{var _1OE=_1OD.a,_1OF=E(_1OB);if(!_1OF._){var _1OG=E(_1OE);if(!_1OG._){var _1OH=B(_1jD(_1NJ,_1ir,_1ir,_1OF.a,_1OF.b,_1OF.c,_1OF.d,_1OG.a,_1OG.b,_1OG.c,_1OG.d));}else{var _1OH=E(_1OF);}var _1OI=_1OH;}else{var _1OI=E(_1OE);}_1OB=_1OI;_1OC=_1OD.b;continue;}}},_1OJ=function(_1OK,_1OL,_1OM){var _1ON=E(_1OM);if(!_1ON._){var _1OO=_1ON.c,_1OP=_1ON.d,_1OQ=E(_1ON.b);switch(B(_1Lv(_1OK,_1OQ.a))){case 0:return new F(function(){return _MW(_1OQ,B(_1OJ(_1OK,_1OL,_1OO)),_1OP);});break;case 1:switch(B(_1bJ(_1MI,B(_1MJ(_1OL)),B(_1MJ(_1OQ.b))))){case 0:return new F(function(){return _MW(_1OQ,B(_1OJ(_1OK,_1OL,_1OO)),_1OP);});break;case 1:return new T4(0,_1ON.a,E(new T2(0,_1OK,_1OL)),E(_1OO),E(_1OP));default:return new F(function(){return _Ny(_1OQ,_1OO,B(_1OJ(_1OK,_1OL,_1OP)));});}break;default:return new F(function(){return _Ny(_1OQ,_1OO,B(_1OJ(_1OK,_1OL,_1OP)));});}}else{return new T4(0,1,E(new T2(0,_1OK,_1OL)),E(_MR),E(_MR));}},_1OR=function(_1OS,_1OT){while(1){var _1OU=E(_1OT);if(!_1OU._){return E(_1OS);}else{var _1OV=E(_1OU.a),_1OW=B(_1OJ(_1OV.a,_1OV.b,_1OS));_1OS=_1OW;_1OT=_1OU.b;continue;}}},_1OX=function(_1OY,_1OZ){var _1P0=E(_1OZ);if(!_1P0._){return new T3(0,_MR,_4,_4);}else{var _1P1=_1P0.a,_1P2=E(_1OY);if(_1P2==1){var _1P3=E(_1P0.b);if(!_1P3._){return new T3(0,new T(function(){return new T4(0,1,E(_1P1),E(_MR),E(_MR));}),_4,_4);}else{var _1P4=E(_1P1),_1P5=E(_1P3.a);switch(B(_1Lv(_1P4.a,_1P5.a))){case 0:return new T3(0,new T4(0,1,E(_1P4),E(_MR),E(_MR)),_1P3,_4);case 1:return (B(_1bJ(_1MI,B(_1MJ(_1P4.b)),B(_1MJ(_1P5.b))))==0)?new T3(0,new T4(0,1,E(_1P4),E(_MR),E(_MR)),_1P3,_4):new T3(0,new T4(0,1,E(_1P4),E(_MR),E(_MR)),_4,_1P3);default:return new T3(0,new T4(0,1,E(_1P4),E(_MR),E(_MR)),_4,_1P3);}}}else{var _1P6=B(_1OX(_1P2>>1,_1P0)),_1P7=_1P6.a,_1P8=_1P6.c,_1P9=E(_1P6.b);if(!_1P9._){return new T3(0,_1P7,_4,_1P8);}else{var _1Pa=_1P9.a,_1Pb=E(_1P9.b);if(!_1Pb._){return new T3(0,new T(function(){return B(_Oe(_1Pa,_1P7));}),_4,_1P8);}else{var _1Pc=E(_1Pa),_1Pd=E(_1Pb.a),_1Pe=function(_1Pf){var _1Pg=B(_1OX(_1P2>>1,_1Pb));return new T3(0,new T(function(){return B(_OS(_1Pc,_1P7,_1Pg.a));}),_1Pg.b,_1Pg.c);};switch(B(_1Lv(_1Pc.a,_1Pd.a))){case 0:return new F(function(){return _1Pe(_);});break;case 1:if(!B(_1bJ(_1MI,B(_1MJ(_1Pc.b)),B(_1MJ(_1Pd.b))))){return new F(function(){return _1Pe(_);});}else{return new T3(0,_1P7,_4,_1P9);}break;default:return new T3(0,_1P7,_4,_1P9);}}}}}},_1Ph=function(_1Pi,_1Pj,_1Pk){var _1Pl=E(_1Pk);if(!_1Pl._){return E(_1Pj);}else{var _1Pm=_1Pl.a,_1Pn=E(_1Pl.b);if(!_1Pn._){return new F(function(){return _Oe(_1Pm,_1Pj);});}else{var _1Po=E(_1Pm),_1Pp=E(_1Pn.a),_1Pq=function(_1Pr){var _1Ps=B(_1OX(_1Pi,_1Pn)),_1Pt=_1Ps.a,_1Pu=E(_1Ps.c);if(!_1Pu._){return new F(function(){return _1Ph(_1Pi<<1,B(_OS(_1Po,_1Pj,_1Pt)),_1Ps.b);});}else{return new F(function(){return _1OR(B(_OS(_1Po,_1Pj,_1Pt)),_1Pu);});}};switch(B(_1Lv(_1Po.a,_1Pp.a))){case 0:return new F(function(){return _1Pq(_);});break;case 1:if(!B(_1bJ(_1MI,B(_1MJ(_1Po.b)),B(_1MJ(_1Pp.b))))){return new F(function(){return _1Pq(_);});}else{return new F(function(){return _1OR(_1Pj,_1Pl);});}break;default:return new F(function(){return _1OR(_1Pj,_1Pl);});}}}},_1Pv=function(_1Pw){var _1Px=E(_1Pw);if(!_1Px._){return new T0(1);}else{var _1Py=_1Px.a,_1Pz=E(_1Px.b);if(!_1Pz._){return new T4(0,1,E(_1Py),E(_MR),E(_MR));}else{var _1PA=E(_1Py),_1PB=E(_1Pz.a);switch(B(_1Lv(_1PA.a,_1PB.a))){case 0:return new F(function(){return _1Ph(1,new T4(0,1,E(_1PA),E(_MR),E(_MR)),_1Pz);});break;case 1:if(!B(_1bJ(_1MI,B(_1MJ(_1PA.b)),B(_1MJ(_1PB.b))))){return new F(function(){return _1Ph(1,new T4(0,1,E(_1PA),E(_MR),E(_MR)),_1Pz);});}else{return new F(function(){return _1OR(new T4(0,1,E(_1PA),E(_MR),E(_MR)),_1Pz);});}break;default:return new F(function(){return _1OR(new T4(0,1,E(_1PA),E(_MR),E(_MR)),_1Pz);});}}}},_1PC=function(_1PD,_1PE,_1PF){var _1PG=E(_1PF);if(!_1PG._){var _1PH=_1PG.c,_1PI=_1PG.d,_1PJ=E(_1PG.b);switch(B(_1LD(_1PD,_1PJ.a))){case 0:return new F(function(){return _MW(_1PJ,B(_1PC(_1PD,_1PE,_1PH)),_1PI);});break;case 1:switch(B(_1Lv(_1PE,_1PJ.b))){case 0:return new F(function(){return _MW(_1PJ,B(_1PC(_1PD,_1PE,_1PH)),_1PI);});break;case 1:return new T4(0,_1PG.a,E(new T2(0,_1PD,_1PE)),E(_1PH),E(_1PI));default:return new F(function(){return _Ny(_1PJ,_1PH,B(_1PC(_1PD,_1PE,_1PI)));});}break;default:return new F(function(){return _Ny(_1PJ,_1PH,B(_1PC(_1PD,_1PE,_1PI)));});}}else{return new T4(0,1,E(new T2(0,_1PD,_1PE)),E(_MR),E(_MR));}},_1PK=function(_1PL,_1PM){while(1){var _1PN=E(_1PM);if(!_1PN._){return E(_1PL);}else{var _1PO=E(_1PN.a),_1PP=B(_1PC(_1PO.a,_1PO.b,_1PL));_1PL=_1PP;_1PM=_1PN.b;continue;}}},_1PQ=function(_1PR,_1PS){var _1PT=E(_1PS);if(!_1PT._){return new T3(0,_MR,_4,_4);}else{var _1PU=_1PT.a,_1PV=E(_1PR);if(_1PV==1){var _1PW=E(_1PT.b);if(!_1PW._){return new T3(0,new T(function(){return new T4(0,1,E(_1PU),E(_MR),E(_MR));}),_4,_4);}else{var _1PX=E(_1PU),_1PY=E(_1PW.a);switch(B(_1LD(_1PX.a,_1PY.a))){case 0:return new T3(0,new T4(0,1,E(_1PX),E(_MR),E(_MR)),_1PW,_4);case 1:return (!B(_1Lh(_1PX.b,_1PY.b)))?new T3(0,new T4(0,1,E(_1PX),E(_MR),E(_MR)),_1PW,_4):new T3(0,new T4(0,1,E(_1PX),E(_MR),E(_MR)),_4,_1PW);default:return new T3(0,new T4(0,1,E(_1PX),E(_MR),E(_MR)),_4,_1PW);}}}else{var _1PZ=B(_1PQ(_1PV>>1,_1PT)),_1Q0=_1PZ.a,_1Q1=_1PZ.c,_1Q2=E(_1PZ.b);if(!_1Q2._){return new T3(0,_1Q0,_4,_1Q1);}else{var _1Q3=_1Q2.a,_1Q4=E(_1Q2.b);if(!_1Q4._){return new T3(0,new T(function(){return B(_Oe(_1Q3,_1Q0));}),_4,_1Q1);}else{var _1Q5=E(_1Q3),_1Q6=E(_1Q4.a);switch(B(_1LD(_1Q5.a,_1Q6.a))){case 0:var _1Q7=B(_1PQ(_1PV>>1,_1Q4));return new T3(0,new T(function(){return B(_OS(_1Q5,_1Q0,_1Q7.a));}),_1Q7.b,_1Q7.c);case 1:if(!B(_1Lh(_1Q5.b,_1Q6.b))){var _1Q8=B(_1PQ(_1PV>>1,_1Q4));return new T3(0,new T(function(){return B(_OS(_1Q5,_1Q0,_1Q8.a));}),_1Q8.b,_1Q8.c);}else{return new T3(0,_1Q0,_4,_1Q2);}break;default:return new T3(0,_1Q0,_4,_1Q2);}}}}}},_1Q9=function(_1Qa,_1Qb,_1Qc){var _1Qd=E(_1Qc);if(!_1Qd._){return E(_1Qb);}else{var _1Qe=_1Qd.a,_1Qf=E(_1Qd.b);if(!_1Qf._){return new F(function(){return _Oe(_1Qe,_1Qb);});}else{var _1Qg=E(_1Qe),_1Qh=E(_1Qf.a),_1Qi=function(_1Qj){var _1Qk=B(_1PQ(_1Qa,_1Qf)),_1Ql=_1Qk.a,_1Qm=E(_1Qk.c);if(!_1Qm._){return new F(function(){return _1Q9(_1Qa<<1,B(_OS(_1Qg,_1Qb,_1Ql)),_1Qk.b);});}else{return new F(function(){return _1PK(B(_OS(_1Qg,_1Qb,_1Ql)),_1Qm);});}};switch(B(_1LD(_1Qg.a,_1Qh.a))){case 0:return new F(function(){return _1Qi(_);});break;case 1:if(!B(_1Lh(_1Qg.b,_1Qh.b))){return new F(function(){return _1Qi(_);});}else{return new F(function(){return _1PK(_1Qb,_1Qd);});}break;default:return new F(function(){return _1PK(_1Qb,_1Qd);});}}}},_1Qn=function(_1Qo){var _1Qp=E(_1Qo);if(!_1Qp._){return new T0(1);}else{var _1Qq=_1Qp.a,_1Qr=E(_1Qp.b);if(!_1Qr._){return new T4(0,1,E(_1Qq),E(_MR),E(_MR));}else{var _1Qs=E(_1Qq),_1Qt=E(_1Qr.a);switch(B(_1LD(_1Qs.a,_1Qt.a))){case 0:return new F(function(){return _1Q9(1,new T4(0,1,E(_1Qs),E(_MR),E(_MR)),_1Qr);});break;case 1:if(!B(_1Lh(_1Qs.b,_1Qt.b))){return new F(function(){return _1Q9(1,new T4(0,1,E(_1Qs),E(_MR),E(_MR)),_1Qr);});}else{return new F(function(){return _1PK(new T4(0,1,E(_1Qs),E(_MR),E(_MR)),_1Qr);});}break;default:return new F(function(){return _1PK(new T4(0,1,E(_1Qs),E(_MR),E(_MR)),_1Qr);});}}}},_1Qu=function(_1Qv){return new T1(1,_1Qv);},_1Qw=function(_1Qx,_1Qy){var _1Qz=E(_1Qx);if(!_1Qz._){var _1QA=_1Qz.c,_1QB=B(_v0(_1QA,0));if(0<=_1QB){var _1QC=function(_1QD,_1QE){var _1QF=E(_1QE);if(!_1QF._){return __Z;}else{return new F(function(){return _0(B(_1Qw(_1QF.a,new T(function(){return B(_0(_1Qy,new T2(1,_1QD,_4)));}))),new T(function(){if(_1QD!=_1QB){return B(_1QC(_1QD+1|0,_1QF.b));}else{return __Z;}},1));});}};return new F(function(){return _1QC(0,_1QA);});}else{return __Z;}}else{return new T2(1,new T2(0,_1Qy,_1Qz.a),_4);}},_1QG=function(_1QH,_1QI){var _1QJ=E(_1QI);if(!_1QJ._){return new T2(0,_4,_4);}else{var _1QK=_1QJ.a,_1QL=_1QJ.b,_1QM=E(_1QH);if(_1QM==1){return new T2(0,new T2(1,_1QK,_4),_1QL);}else{var _1QN=new T(function(){var _1QO=B(_1QG(_1QM-1|0,_1QL));return new T2(0,_1QO.a,_1QO.b);});return new T2(0,new T2(1,_1QK,new T(function(){return E(E(_1QN).a);})),new T(function(){return E(E(_1QN).b);}));}}},_1QP=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_1QQ=function(_1QR){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_1QR,_1QP));})),_6y);});},_1QS=new T(function(){return B(_1QQ("Muste/Tree/Internal.hs:217:9-39|(pre, _ : post)"));}),_1QT=function(_1QU,_1QV,_1QW){if(0>_1QV){return E(_1QU);}else{if(_1QV>=B(_v0(_1QU,0))){return E(_1QU);}else{if(_1QV>0){var _1QX=B(_1QG(_1QV,_1QU)),_1QY=E(_1QX.b);if(!_1QY._){return E(_1QS);}else{return new F(function(){return _0(_1QX.a,new T2(1,_1QW,_1QY.b));});}}else{var _1QZ=E(_1QU);if(!_1QZ._){return E(_1QS);}else{return new F(function(){return _0(_4,new T2(1,_1QW,_1QZ.b));});}}}}},_1R0=function(_1R1,_1R2,_1R3){var _1R4=E(_1R1);if(!_1R4._){var _1R5=_1R4.c,_1R6=E(_1R2);if(!_1R6._){return E(_1R3);}else{var _1R7=E(_1R6.a);if(_1R7<0){return E(_1R4);}else{var _1R8=B(_v0(_1R5,0));if(_1R7>=_1R8){return E(_1R4);}else{var _1R9=new T(function(){return B(_1QT(_1R5,_1R7,new T(function(){var _1Ra=E(_1R5);if(!_1Ra._){return E(_1Jf);}else{if(_1R7>=0){if(_1R7<_1R8){return B(_1R0(B(_1Ej(_1Ra,_1R7)),_1R6.b,_1R3));}else{return E(_1Jf);}}else{return E(_1Jf);}}})));});return new T3(0,_1R4.a,_1R4.b,_1R9);}}}}else{return (E(_1R2)._==0)?E(_1R3):E(_1R4);}},_1Rb=function(_1Rc,_1Rd,_1Re,_1Rf,_1Rg){while(1){var _1Rh=B((function(_1Ri,_1Rj,_1Rk,_1Rl,_1Rm){var _1Rn=E(_1Rl);if(!_1Rn._){var _1Ro=E(_1Rm);if(!_1Ro._){return new T2(0,_1Ri,_1Rj);}else{var _1Rp=_1Ro.a,_1Rq=new T3(0,_1Rk,_1Rn,new T(function(){return B(_G(_1Qu,_1Rn.b));})),_1Rr=new T(function(){var _1Rs=function(_1Rt){var _1Ru=E(_1Rt);return new T2(0,new T(function(){return B(_0(_1Rp,_1Ru.a));}),new T1(1,_1Ru.b));},_1Rv=B(_1Qn(B(_G(_1Rs,B(_1Qw(_1Rq,_4)))))),_1Rw=B(_1o7(function(_1Rx){return (!B(_1JD(_1Rp,B(_1FL(_1Rx)))))?true:false;},_1Rj));if(!_1Rw._){var _1Ry=E(_1Rv);if(!_1Ry._){return B(_1jD(_1MI,_1ir,_1ir,_1Rw.a,_1Rw.b,_1Rw.c,_1Rw.d,_1Ry.a,_1Ry.b,_1Ry.c,_1Ry.d));}else{return E(_1Rw);}}else{return E(_1Rv);}}),_1Rz=_1Rk;_1Rc=new T(function(){return B(_1R0(_1Ri,_1Rp,_1Rq));});_1Rd=_1Rr;_1Re=_1Rz;_1Rf=_1Rn;_1Rg=_1Ro.b;return __continue;}}else{return new T2(0,_1Ri,_1Rj);}})(_1Rc,_1Rd,_1Re,_1Rf,_1Rg));if(_1Rh!=__continue){return _1Rh;}}},_1RA=new T2(1,_4,_4),_1RB=function(_1RC){var _1RD=E(_1RC);if(!_1RD._){return E(_1RA);}else{var _1RE=_1RD.b,_1RF=new T(function(){return B(_G(function(_1Qv){return new T2(1,_1RD.a,_1Qv);},B(_1RB(_1RE))));},1);return new F(function(){return _0(B(_1RB(_1RE)),_1RF);});}},_1RG=new T(function(){return B(_1zc(95));}),_1RH=new T2(1,_1RG,_4),_1RI=new T(function(){var _1RJ=B(_1y0(_1RH));return new T3(0,_1RJ.a,_1RJ.b,_1RJ.c);}),_1RK=function(_1RL,_1RM,_1RN,_1RO){var _1RP=new T(function(){return E(_1RN)-1|0;}),_1RQ=function(_1RR){var _1RS=E(_1RR);if(!_1RS._){return __Z;}else{var _1RT=_1RS.b,_1RU=E(_1RS.a),_1RV=_1RU.a,_1RW=function(_1RX,_1RY,_1RZ){var _1S0=E(_1RU.b);if(!B(_12S(_1RX,_1RY,_1RZ,_1S0.a,_1S0.b,_1S0.c))){return new F(function(){return _1RQ(_1RT);});}else{if(B(_v0(_1RV,0))>E(_1RP)){return new F(function(){return _1RQ(_1RT);});}else{return new T2(1,_1RV,new T(function(){return B(_1RQ(_1RT));}));}}},_1S1=E(E(_1RO).b);if(!_1S1._){var _1S2=E(_1S1.a);return new F(function(){return _1RW(_1S2.a,_1S2.b,_1S2.c);});}else{var _1S3=E(_1RI);return new F(function(){return _1RW(_1S3.a,_1S3.b,_1S3.c);});}}},_1S4=function(_1S5){var _1S6=new T(function(){var _1S7=E(_1RO),_1S8=B(_1Rb(_1RL,_1RM,_1S7.a,_1S7.b,_1S5));return new T2(0,_1S8.a,_1S8.b);}),_1S9=new T(function(){return E(E(_1S6).a);}),_1Sa=new T(function(){var _1Sb=function(_1Sc){var _1Sd=B(_1Es(_1S9,E(_1Sc).a));return (_1Sd._==0)?false:(E(_1Sd.a)._==0)?false:true;},_1Se=E(E(_1S6).b);if(!_1Se._){var _1Sf=E(_1RM);if(!_1Sf._){return B(_1o7(_1Sb,B(_1jD(_1MI,_1ir,_1ir,_1Se.a,_1Se.b,_1Se.c,_1Se.d,_1Sf.a,_1Sf.b,_1Sf.c,_1Sf.d))));}else{return B(_1o7(_1Sb,_1Se));}}else{return B(_1o7(_1Sb,_1RM));}});return new T2(0,_1S9,_1Sa);};return new F(function(){return _1Pv(B(_G(_1S4,B(_1RB(B(_1RQ(B(_1Qw(_1RL,_4)))))))));});},_1Sg=function(_1Sh,_1Si){while(1){var _1Sj=E(_1Si);if(!_1Sj._){return E(_1Sh);}else{var _1Sk=_1Sj.a,_1Sl=E(_1Sh);if(!_1Sl._){var _1Sm=E(_1Sk);if(!_1Sm._){var _1Sn=B(_1jD(_1KK,_1ir,_1ir,_1Sl.a,_1Sl.b,_1Sl.c,_1Sl.d,_1Sm.a,_1Sm.b,_1Sm.c,_1Sm.d));}else{var _1Sn=E(_1Sl);}var _1So=_1Sn;}else{var _1So=E(_1Sk);}_1Sh=_1So;_1Si=_1Sj.b;continue;}}},_1Sp=function(_1Sq){var _1Sr=E(_1Sq);if(!_1Sr._){return new F(function(){return _1Sg(_MR,B(_G(_1Sp,_1Sr.c)));});}else{return new F(function(){return _O8(_1Sr.a);});}},_1Ss=function(_1St,_1Su,_1Sv){var _1Sw=E(_1Sv);if(!_1Sw._){var _1Sx=_1Sw.c,_1Sy=_1Sw.d,_1Sz=E(_1Sw.b),_1SA=E(_1St),_1SB=E(_1Sz.a);switch(B(_12Z(_1SA.a,_1SA.b,_1SA.c,_1SB.a,_1SB.b,_1SB.c))){case 0:return new F(function(){return _MW(_1Sz,B(_1Ss(_1SA,_1Su,_1Sx)),_1Sy);});break;case 1:switch(B(_1KL(_1Su,_1Sz.b))){case 0:return new F(function(){return _MW(_1Sz,B(_1Ss(_1SA,_1Su,_1Sx)),_1Sy);});break;case 1:return new T4(0,_1Sw.a,E(new T2(0,_1SA,_1Su)),E(_1Sx),E(_1Sy));default:return new F(function(){return _Ny(_1Sz,_1Sx,B(_1Ss(_1SA,_1Su,_1Sy)));});}break;default:return new F(function(){return _Ny(_1Sz,_1Sx,B(_1Ss(_1SA,_1Su,_1Sy)));});}}else{return new T4(0,1,E(new T2(0,_1St,_1Su)),E(_MR),E(_MR));}},_1SC=function(_1SD,_1SE){while(1){var _1SF=E(_1SE);if(!_1SF._){return E(_1SD);}else{var _1SG=E(_1SF.a),_1SH=B(_1Ss(_1SG.a,_1SG.b,_1SD));_1SD=_1SH;_1SE=_1SF.b;continue;}}},_1SI=function(_1SJ,_1SK){var _1SL=E(_1SK);if(!_1SL._){return new T3(0,_MR,_4,_4);}else{var _1SM=_1SL.a,_1SN=E(_1SJ);if(_1SN==1){var _1SO=E(_1SL.b);if(!_1SO._){return new T3(0,new T(function(){return new T4(0,1,E(_1SM),E(_MR),E(_MR));}),_4,_4);}else{var _1SP=E(_1SM),_1SQ=E(_1SO.a),_1SR=_1SQ.b,_1SS=E(_1SP.a),_1ST=E(_1SQ.a);switch(B(_12Z(_1SS.a,_1SS.b,_1SS.c,_1ST.a,_1ST.b,_1ST.c))){case 0:return new T3(0,new T4(0,1,E(_1SP),E(_MR),E(_MR)),_1SO,_4);case 1:var _1SU=E(_1SP.b);if(!_1SU._){var _1SV=E(_1SR);if(!_1SV._){var _1SW=E(_1SU.a),_1SX=E(_1SV.a);switch(B(_12Z(_1SW.a,_1SW.b,_1SW.c,_1SX.a,_1SX.b,_1SX.c))){case 0:return new T3(0,new T4(0,1,E(_1SP),E(_MR),E(_MR)),_1SO,_4);case 1:return (B(_1bJ(_1KK,_1SU.b,_1SV.b))==0)?new T3(0,new T4(0,1,E(_1SP),E(_MR),E(_MR)),_1SO,_4):new T3(0,new T4(0,1,E(_1SP),E(_MR),E(_MR)),_4,_1SO);default:return new T3(0,new T4(0,1,E(_1SP),E(_MR),E(_MR)),_4,_1SO);}}else{return new T3(0,new T4(0,1,E(_1SP),E(_MR),E(_MR)),_1SO,_4);}}else{var _1SY=E(_1SR);return new T3(0,new T4(0,1,E(_1SP),E(_MR),E(_MR)),_4,_1SO);}break;default:return new T3(0,new T4(0,1,E(_1SP),E(_MR),E(_MR)),_4,_1SO);}}}else{var _1SZ=B(_1SI(_1SN>>1,_1SL)),_1T0=_1SZ.a,_1T1=_1SZ.c,_1T2=E(_1SZ.b);if(!_1T2._){return new T3(0,_1T0,_4,_1T1);}else{var _1T3=_1T2.a,_1T4=E(_1T2.b);if(!_1T4._){return new T3(0,new T(function(){return B(_Oe(_1T3,_1T0));}),_4,_1T1);}else{var _1T5=E(_1T3),_1T6=E(_1T4.a),_1T7=_1T6.b,_1T8=E(_1T5.a),_1T9=E(_1T6.a);switch(B(_12Z(_1T8.a,_1T8.b,_1T8.c,_1T9.a,_1T9.b,_1T9.c))){case 0:var _1Ta=B(_1SI(_1SN>>1,_1T4));return new T3(0,new T(function(){return B(_OS(_1T5,_1T0,_1Ta.a));}),_1Ta.b,_1Ta.c);case 1:var _1Tb=E(_1T5.b);if(!_1Tb._){var _1Tc=E(_1T7);if(!_1Tc._){var _1Td=E(_1Tb.a),_1Te=E(_1Tc.a);switch(B(_12Z(_1Td.a,_1Td.b,_1Td.c,_1Te.a,_1Te.b,_1Te.c))){case 0:var _1Tf=B(_1SI(_1SN>>1,_1T4));return new T3(0,new T(function(){return B(_OS(_1T5,_1T0,_1Tf.a));}),_1Tf.b,_1Tf.c);case 1:if(!B(_1bJ(_1KK,_1Tb.b,_1Tc.b))){var _1Tg=B(_1SI(_1SN>>1,_1T4));return new T3(0,new T(function(){return B(_OS(_1T5,_1T0,_1Tg.a));}),_1Tg.b,_1Tg.c);}else{return new T3(0,_1T0,_4,_1T2);}break;default:return new T3(0,_1T0,_4,_1T2);}}else{var _1Th=B(_1SI(_1SN>>1,_1T4));return new T3(0,new T(function(){return B(_OS(_1T5,_1T0,_1Th.a));}),_1Th.b,_1Th.c);}}else{var _1Ti=E(_1T7);return new T3(0,_1T0,_4,_1T2);}break;default:return new T3(0,_1T0,_4,_1T2);}}}}}},_1Tj=function(_1Tk,_1Tl,_1Tm){var _1Tn=E(_1Tm);if(!_1Tn._){return E(_1Tl);}else{var _1To=_1Tn.a,_1Tp=E(_1Tn.b);if(!_1Tp._){return new F(function(){return _Oe(_1To,_1Tl);});}else{var _1Tq=E(_1To),_1Tr=E(_1Tp.a),_1Ts=_1Tr.b,_1Tt=E(_1Tq.a),_1Tu=E(_1Tr.a),_1Tv=function(_1Tw){var _1Tx=B(_1SI(_1Tk,_1Tp)),_1Ty=_1Tx.a,_1Tz=E(_1Tx.c);if(!_1Tz._){return new F(function(){return _1Tj(_1Tk<<1,B(_OS(_1Tq,_1Tl,_1Ty)),_1Tx.b);});}else{return new F(function(){return _1SC(B(_OS(_1Tq,_1Tl,_1Ty)),_1Tz);});}};switch(B(_12Z(_1Tt.a,_1Tt.b,_1Tt.c,_1Tu.a,_1Tu.b,_1Tu.c))){case 0:return new F(function(){return _1Tv(_);});break;case 1:var _1TA=E(_1Tq.b);if(!_1TA._){var _1TB=E(_1Ts);if(!_1TB._){var _1TC=E(_1TA.a),_1TD=E(_1TB.a);switch(B(_12Z(_1TC.a,_1TC.b,_1TC.c,_1TD.a,_1TD.b,_1TD.c))){case 0:return new F(function(){return _1Tv(_);});break;case 1:if(!B(_1bJ(_1KK,_1TA.b,_1TB.b))){return new F(function(){return _1Tv(_);});}else{return new F(function(){return _1SC(_1Tl,_1Tn);});}break;default:return new F(function(){return _1SC(_1Tl,_1Tn);});}}else{return new F(function(){return _1Tv(_);});}}else{var _1TE=E(_1Ts);return new F(function(){return _1SC(_1Tl,_1Tn);});}break;default:return new F(function(){return _1SC(_1Tl,_1Tn);});}}}},_1TF=function(_1TG){var _1TH=E(_1TG);if(!_1TH._){return new T0(1);}else{var _1TI=_1TH.a,_1TJ=E(_1TH.b);if(!_1TJ._){return new T4(0,1,E(_1TI),E(_MR),E(_MR));}else{var _1TK=E(_1TI),_1TL=E(_1TJ.a),_1TM=_1TL.b,_1TN=E(_1TK.a),_1TO=E(_1TL.a);switch(B(_12Z(_1TN.a,_1TN.b,_1TN.c,_1TO.a,_1TO.b,_1TO.c))){case 0:return new F(function(){return _1Tj(1,new T4(0,1,E(_1TK),E(_MR),E(_MR)),_1TJ);});break;case 1:var _1TP=E(_1TK.b);if(!_1TP._){var _1TQ=E(_1TM);if(!_1TQ._){var _1TR=E(_1TP.a),_1TS=E(_1TQ.a);switch(B(_12Z(_1TR.a,_1TR.b,_1TR.c,_1TS.a,_1TS.b,_1TS.c))){case 0:return new F(function(){return _1Tj(1,new T4(0,1,E(_1TK),E(_MR),E(_MR)),_1TJ);});break;case 1:if(!B(_1bJ(_1KK,_1TP.b,_1TQ.b))){return new F(function(){return _1Tj(1,new T4(0,1,E(_1TK),E(_MR),E(_MR)),_1TJ);});}else{return new F(function(){return _1SC(new T4(0,1,E(_1TK),E(_MR),E(_MR)),_1TJ);});}break;default:return new F(function(){return _1SC(new T4(0,1,E(_1TK),E(_MR),E(_MR)),_1TJ);});}}else{return new F(function(){return _1Tj(1,new T4(0,1,E(_1TK),E(_MR),E(_MR)),_1TJ);});}}else{var _1TT=E(_1TM);return new F(function(){return _1SC(new T4(0,1,E(_1TK),E(_MR),E(_MR)),_1TJ);});}break;default:return new F(function(){return _1SC(new T4(0,1,E(_1TK),E(_MR),E(_MR)),_1TJ);});}}}},_1TU=new T(function(){return B(_7f("Muste/Grammar/Internal.hs:151:43-81|lambda"));}),_1TV=function(_1TW,_1TX){var _1TY=new T(function(){return E(E(_1TW).b);}),_1TZ=function(_1U0){var _1U1=E(_1U0);if(!_1U1._){return __Z;}else{var _1U2=new T(function(){return B(_1TZ(_1U1.b));}),_1U3=function(_1U4){while(1){var _1U5=B((function(_1U6){var _1U7=E(_1U6);if(!_1U7._){return E(_1U2);}else{var _1U8=_1U7.b,_1U9=E(_1U7.a),_1Ua=E(_1U9.b);if(!_1Ua._){var _1Ub=E(_1Ua.a),_1Uc=E(_1U1.a);if(!B(_12S(_1Ub.a,_1Ub.b,_1Ub.c,_1Uc.a,_1Uc.b,_1Uc.c))){_1U4=_1U8;return __continue;}else{return new T2(1,_1U9,new T(function(){return B(_1U3(_1U8));}));}}else{return E(_1TU);}}})(_1U4));if(_1U5!=__continue){return _1U5;}}};return new F(function(){return _1U3(_1TY);});}};return new F(function(){return _1TF(B(_1TZ(_1TX)));});},_1Ud=function(_1Ue,_1Uf,_1Ug,_1Uh){var _1Ui=function(_1Uj,_1Uk){while(1){var _1Ul=B((function(_1Um,_1Un){var _1Uo=E(_1Un);if(!_1Uo._){_1Uj=new T2(1,new T(function(){return B(_1RK(_1Uf,_1Ug,_1Uh,_1Uo.b));}),new T(function(){return B(_1Ui(_1Um,_1Uo.d));}));_1Uk=_1Uo.c;return __continue;}else{return E(_1Um);}})(_1Uj,_1Uk));if(_1Ul!=__continue){return _1Ul;}}};return new F(function(){return _1OA(_MR,B(_1no(_4,B(_1Ov(B(_1Ui(_4,B(_1TV(_1Ue,B(_1no(_4,B(_1Sp(_1Uf)))))))))))));});},_1Up=function(_1Uq,_1Ur,_1Us){var _1Ut=E(_1Ur);return new F(function(){return _1Ud(_1Uq,_1Ut.a,_1Ut.b,_1Us);});},_1Uu=function(_1Uv,_1Uw){while(1){var _1Ux=B((function(_1Uy,_1Uz){var _1UA=E(_1Uz);if(!_1UA._){return __Z;}else{var _1UB=_1UA.a,_1UC=_1UA.b;if(!B(A1(_1Uy,_1UB))){var _1UD=_1Uy;_1Uv=_1UD;_1Uw=_1UC;return __continue;}else{return new T2(1,_1UB,new T(function(){return B(_1Uu(_1Uy,_1UC));}));}}})(_1Uv,_1Uw));if(_1Ux!=__continue){return _1Ux;}}},_1UE=function(_1UF,_1UG,_1UH){var _1UI=new T(function(){return E(_1UH)-1|0;}),_1UJ=function(_1UK){return B(_v0(E(_1UK).a,0))<=E(_1UI);},_1UL=function(_1UM,_1UN){while(1){var _1UO=B((function(_1UP,_1UQ){var _1UR=E(_1UQ);if(!_1UR._){var _1US=_1UR.d,_1UT=E(_1UR.b),_1UU=new T(function(){if(!B(_1Uu(_1UJ,B(_1Qw(_1UT.a,_4))))._){return B(_1UL(_1UP,_1US));}else{return new T2(1,_1UT,new T(function(){return B(_1UL(_1UP,_1US));}));}},1);_1UM=_1UU;_1UN=_1UR.c;return __continue;}else{return E(_1UP);}})(_1UM,_1UN));if(_1UO!=__continue){return _1UO;}}},_1UV=function(_1UW){var _1UX=E(_1UW);if(!_1UX._){return new T0(1);}else{var _1UY=_1UX.a,_1UZ=B(_1Up(_1UF,_1UY,_1UH)),_1V0=B(_1UV(B(_0(_1UX.b,new T(function(){var _1V1=E(_1UY);return B(_1UL(_4,B(_1NK(_1V1.a,_1V1.b,_1UZ))));},1))))),_1V2=function(_1V3,_1V4,_1V5,_1V6){return new F(function(){return _1jD(_1NJ,_1ir,_1ir,1,_1UY,_MR,_MR,_1V3,_1V4,_1V5,_1V6);});},_1V7=E(_1UZ);if(!_1V7._){var _1V8=_1V7.a,_1V9=_1V7.b,_1Va=_1V7.c,_1Vb=_1V7.d,_1Vc=E(_1V0);if(!_1Vc._){var _1Vd=B(_1jD(_1NJ,_1ir,_1ir,_1V8,_1V9,_1Va,_1Vb,_1Vc.a,_1Vc.b,_1Vc.c,_1Vc.d));if(!_1Vd._){return new F(function(){return _1V2(_1Vd.a,_1Vd.b,_1Vd.c,_1Vd.d);});}else{return new T4(0,1,E(_1UY),E(_MR),E(_MR));}}else{return new F(function(){return _1V2(_1V8,_1V9,_1Va,_1Vb);});}}else{var _1Ve=E(_1V0);if(!_1Ve._){return new F(function(){return _1V2(_1Ve.a,_1Ve.b,_1Ve.c,_1Ve.d);});}else{return new T4(0,1,E(_1UY),E(_MR),E(_MR));}}}};return new F(function(){return _1UV(new T2(1,new T2(0,new T1(1,_1UG),new T4(0,1,E(new T2(0,_4,new T1(1,_1UG))),E(_MR),E(_MR))),_4));});},_1Vf=function(_1Vg){return E(E(_1Vg).a);},_1Vh=function(_1Vi,_1Vj,_1Vk,_1Vl){var _1Vm=new T(function(){var _1Vn=B(_1Es(new T(function(){return B(_1Vf(_1Vj));}),_1Vk));if(!_1Vn._){return E(_1Jf);}else{var _1Vo=E(_1Vn.a);if(!_1Vo._){var _1Vp=E(_1Vo.b);if(!_1Vp._){return E(_1Vp.a);}else{return E(_1RI);}}else{return E(_1Vo.a);}}});return new F(function(){return _1UE(_1Vi,_1Vm,_1Vl);});},_1Vq=function(_1Vr,_1Vs,_1Vt,_1Vu){while(1){var _1Vv=E(_1Vs);if(!_1Vv._){return E(_1Vu);}else{var _1Vw=_1Vv.a,_1Vx=E(_1Vt);if(!_1Vx._){return E(_1Vu);}else{if(!B(A3(_pS,_1Vr,_1Vw,_1Vx.a))){return E(_1Vu);}else{var _1Vy=new T2(1,_1Vw,_1Vu);_1Vs=_1Vv.b;_1Vt=_1Vx.b;_1Vu=_1Vy;continue;}}}}},_1Vz=function(_1VA,_1VB){while(1){var _1VC=E(_1VA);if(!_1VC._){return E(_1VB);}else{var _1VD=new T2(1,_1VC.a,_1VB);_1VA=_1VC.b;_1VB=_1VD;continue;}}},_1VE=function(_1VF,_1VG,_1VH,_1VI,_1VJ){while(1){var _1VK=B((function(_1VL,_1VM,_1VN,_1VO,_1VP){var _1VQ=E(_1VM);if(!_1VQ._){return new T2(0,_1VO,_1VP);}else{var _1VR=_1VQ.a,_1VS=_1VQ.b,_1VT=E(_1VN);if(!_1VT._){return new T2(0,_1VO,_1VP);}else{var _1VU=_1VT.b;if(!B(A3(_pS,_1VL,_1VR,_1VT.a))){var _1VV=new T(function(){return B(_1Vq(_1VL,B(_1Vz(_1VQ,_4)),new T(function(){return B(_1Vz(_1VT,_4));},1),_4));}),_1VW=_1VL,_1VX=_1VO;_1VF=_1VW;_1VG=_1VS;_1VH=_1VU;_1VI=_1VX;_1VJ=_1VV;return __continue;}else{var _1VW=_1VL,_1VY=_1VP;_1VF=_1VW;_1VG=_1VS;_1VH=_1VU;_1VI=new T(function(){return B(_0(_1VO,new T2(1,_1VR,_4)));});_1VJ=_1VY;return __continue;}}}})(_1VF,_1VG,_1VH,_1VI,_1VJ));if(_1VK!=__continue){return _1VK;}}},_1VZ=function(_1W0,_1W1,_1W2,_1W3){return (!B(_1JD(_1W0,_1W2)))?true:(!B(_sl(_1W1,_1W3)))?true:false;},_1W4=function(_1W5,_1W6){var _1W7=E(_1W5),_1W8=E(_1W6);return new F(function(){return _1VZ(_1W7.a,_1W7.b,_1W8.a,_1W8.b);});},_1W9=function(_1Wa,_1Wb,_1Wc,_1Wd){if(!B(_1JD(_1Wa,_1Wc))){return false;}else{return new F(function(){return _sl(_1Wb,_1Wd);});}},_1We=function(_1Wf,_1Wg){var _1Wh=E(_1Wf),_1Wi=E(_1Wg);return new F(function(){return _1W9(_1Wh.a,_1Wh.b,_1Wi.a,_1Wi.b);});},_1Wj=new T2(0,_1We,_1W4),_1Wk=function(_1Wl,_1Wm,_1Wn,_1Wo){switch(B(_1LD(_1Wl,_1Wn))){case 0:return false;case 1:return new F(function(){return _12z(_1Wm,_1Wo);});break;default:return true;}},_1Wp=function(_1Wq,_1Wr){var _1Ws=E(_1Wq),_1Wt=E(_1Wr);return new F(function(){return _1Wk(_1Ws.a,_1Ws.b,_1Wt.a,_1Wt.b);});},_1Wu=function(_1Wv,_1Ww){var _1Wx=E(_1Wv),_1Wy=E(_1Ww);switch(B(_1LD(_1Wx.a,_1Wy.a))){case 0:return E(_1Wy);case 1:return (B(_12j(_1Wx.b,_1Wy.b))==2)?E(_1Wx):E(_1Wy);default:return E(_1Wx);}},_1Wz=function(_1WA,_1WB){var _1WC=E(_1WA),_1WD=E(_1WB);switch(B(_1LD(_1WC.a,_1WD.a))){case 0:return E(_1WC);case 1:return (B(_12j(_1WC.b,_1WD.b))==2)?E(_1WD):E(_1WC);default:return E(_1WD);}},_1WE=function(_1WF,_1WG,_1WH,_1WI){switch(B(_1LD(_1WF,_1WH))){case 0:return 0;case 1:return new F(function(){return _12j(_1WG,_1WI);});break;default:return 2;}},_1WJ=function(_1WK,_1WL){var _1WM=E(_1WK),_1WN=E(_1WL);return new F(function(){return _1WE(_1WM.a,_1WM.b,_1WN.a,_1WN.b);});},_1WO=function(_1WP,_1WQ,_1WR,_1WS){switch(B(_1LD(_1WP,_1WR))){case 0:return true;case 1:return new F(function(){return _12q(_1WQ,_1WS);});break;default:return false;}},_1WT=function(_1WU,_1WV){var _1WW=E(_1WU),_1WX=E(_1WV);return new F(function(){return _1WO(_1WW.a,_1WW.b,_1WX.a,_1WX.b);});},_1WY=function(_1WZ,_1X0,_1X1,_1X2){switch(B(_1LD(_1WZ,_1X1))){case 0:return true;case 1:return new F(function(){return _12t(_1X0,_1X2);});break;default:return false;}},_1X3=function(_1X4,_1X5){var _1X6=E(_1X4),_1X7=E(_1X5);return new F(function(){return _1WY(_1X6.a,_1X6.b,_1X7.a,_1X7.b);});},_1X8=function(_1X9,_1Xa,_1Xb,_1Xc){switch(B(_1LD(_1X9,_1Xb))){case 0:return false;case 1:return new F(function(){return _12w(_1Xa,_1Xc);});break;default:return true;}},_1Xd=function(_1Xe,_1Xf){var _1Xg=E(_1Xe),_1Xh=E(_1Xf);return new F(function(){return _1X8(_1Xg.a,_1Xg.b,_1Xh.a,_1Xh.b);});},_1Xi={_:0,a:_1Wj,b:_1WJ,c:_1WT,d:_1X3,e:_1Xd,f:_1Wp,g:_1Wu,h:_1Wz},_1Xj=function(_1Xk){var _1Xl=E(_1Xk);if(!_1Xl._){return __Z;}else{return new F(function(){return _0(_1Xl.a,new T(function(){return B(_1Xj(_1Xl.b));},1));});}},_1Xm=new T1(1,_4),_1Xn=function(_1Xo){var _1Xp=E(_1Xo);if(!_1Xp._){return E(_1Xm);}else{var _1Xq=E(_1Xp.a);if(!_1Xq._){return __Z;}else{var _1Xr=B(_1Xn(_1Xp.b));return (_1Xr._==0)?__Z:new T1(1,new T2(1,_1Xq.a,_1Xr.a));}}},_1Xs=function(_1Xt,_1Xu){var _1Xv=B(_1Xn(_1Xu));return (_1Xv._==0)?new T2(0,_4l,_4l):new T2(0,_1Xt,new T1(1,new T(function(){return B(_1Xj(_1Xv.a));})));},_1Xw=function(_1Xx,_1Xy){var _1Xz=E(_1Xx);if(!_1Xz._){return new T2(0,_1Xy,_4);}else{var _1XA=new T(function(){var _1XB=B(_1Xw(_1Xz.b,_1Xy));return new T2(0,_1XB.a,_1XB.b);}),_1XC=new T(function(){var _1XD=B(_1XE(new T(function(){return E(E(_1XA).a);}),_1Xz.a));return new T2(0,_1XD.a,_1XD.b);});return new T2(0,new T(function(){return E(E(_1XC).a);}),new T2(1,new T(function(){return E(E(_1XC).b);}),new T(function(){return E(E(_1XA).b);})));}},_1XF=function(_1XG,_1XH){var _1XI=E(_1XG);if(!_1XI._){return new T2(0,_1XH,_4);}else{var _1XJ=new T(function(){var _1XK=B(_1XF(_1XI.b,_1XH));return new T2(0,_1XK.a,_1XK.b);}),_1XL=new T(function(){var _1XM=B(_1XE(new T(function(){return E(E(_1XJ).a);}),_1XI.a));return new T2(0,_1XM.a,_1XM.b);});return new T2(0,new T(function(){return E(E(_1XL).a);}),new T2(1,new T(function(){return E(E(_1XL).b);}),new T(function(){return E(E(_1XJ).b);})));}},_1XN=function(_1XO,_1XP){var _1XQ=E(_1XO);if(!_1XQ._){return new T2(0,_1XP,_4);}else{var _1XR=new T(function(){var _1XS=B(_1XN(_1XQ.b,_1XP));return new T2(0,_1XS.a,_1XS.b);}),_1XT=new T(function(){var _1XU=B(_1XE(new T(function(){return E(E(_1XR).a);}),_1XQ.a));return new T2(0,_1XU.a,_1XU.b);});return new T2(0,new T(function(){return E(E(_1XT).a);}),new T2(1,new T(function(){return E(E(_1XT).b);}),new T(function(){return E(E(_1XR).b);})));}},_1XV=function(_1XW,_1XX){var _1XY=E(_1XW);if(!_1XY._){return new T2(0,_1XX,_4);}else{var _1XZ=new T(function(){var _1Y0=B(_1XV(_1XY.b,_1XX));return new T2(0,_1Y0.a,_1Y0.b);}),_1Y1=new T(function(){var _1Y2=B(_1XE(new T(function(){return E(E(_1XZ).a);}),_1XY.a));return new T2(0,_1Y2.a,_1Y2.b);});return new T2(0,new T(function(){return E(E(_1Y1).a);}),new T2(1,new T(function(){return E(E(_1Y1).b);}),new T(function(){return E(E(_1XZ).b);})));}},_1Y3=function(_1Y4){var _1Y5=E(_1Y4);if(!_1Y5._){return __Z;}else{return new F(function(){return _0(_1Y5.a,new T(function(){return B(_1Y3(_1Y5.b));},1));});}},_1Y6=function(_1Y7){var _1Y8=E(_1Y7);if(!_1Y8._){return E(_1Xm);}else{var _1Y9=E(_1Y8.a);if(!_1Y9._){return __Z;}else{var _1Ya=B(_1Y6(_1Y8.b));return (_1Ya._==0)?__Z:new T1(1,new T2(1,_1Y9.a,_1Ya.a));}}},_1Yb=function(_1Yc,_1Yd,_1Ye){while(1){var _1Yf=E(_1Yd);if(!_1Yf._){return true;}else{var _1Yg=E(_1Ye);if(!_1Yg._){return false;}else{if(!B(A3(_pS,_1Yc,_1Yf.a,_1Yg.a))){return false;}else{_1Yd=_1Yf.b;_1Ye=_1Yg.b;continue;}}}}},_1Yh=new T1(1,_4),_1Yi=new T(function(){return B(_7f("pgf/PGF/Macros.hs:(186,5)-(204,44)|function untokn"));}),_1XE=function(_1Yj,_1Yk){var _1Yl=E(_1Yk);switch(_1Yl._){case 0:var _1Ym=B(_1XV(_1Yl.f,_1Yj)),_1Yn=B(_1Y6(_1Ym.b));return (_1Yn._==0)?new T2(0,_4l,_4l):new T2(0,_1Ym.a,new T1(1,new T2(1,new T6(1,_1Yl.a,_1Yl.b,_1Yl.c,_1Yl.d,_1Yl.e,new T(function(){return B(_1Y3(_1Yn.a));})),_4)));case 1:var _1Yo=E(_1Yl.a);return (_1Yo._==0)?new T2(0,_1Yj,_1Yh):new T2(0,new T1(1,_1Yo),new T1(1,new T2(1,new T1(0,_1Yo),_4)));case 2:return new T2(0,_4l,_4l);case 6:var _1Yp=_1Yl.a,_1Yq=E(_1Yj);if(!_1Yq._){var _1Yr=B(_1XN(_1Yp,_4l));return new F(function(){return _1Xs(_1Yr.a,_1Yr.b);});}else{var _1Ys=function(_1Yt){while(1){var _1Yu=E(_1Yt);if(!_1Yu._){return false;}else{if(!B(_1Yb(_sw,_1Yu.a,_1Yq.a))){_1Yt=_1Yu.b;continue;}else{return true;}}}},_1Yv=function(_1Yw){while(1){var _1Yx=B((function(_1Yy){var _1Yz=E(_1Yy);if(!_1Yz._){return __Z;}else{var _1YA=_1Yz.b,_1YB=E(_1Yz.a);if(!B(_1Ys(_1YB.b))){_1Yw=_1YA;return __continue;}else{return new T2(1,_1YB.a,new T(function(){return B(_1Yv(_1YA));}));}}})(_1Yw));if(_1Yx!=__continue){return _1Yx;}}},_1YC=B(_1Yv(_1Yl.b));if(!_1YC._){var _1YD=B(_1XF(_1Yp,_1Yq));return new F(function(){return _1Xs(_1YD.a,_1YD.b);});}else{var _1YE=B(_1Xw(_1YC.a,_1Yq));return new F(function(){return _1Xs(_1YE.a,_1YE.b);});}}break;default:return E(_1Yi);}},_1YF=function(_1YG,_1YH){var _1YI=E(_1YG);if(!_1YI._){return new T2(0,_1YH,_4);}else{var _1YJ=new T(function(){var _1YK=B(_1YF(_1YI.b,_1YH));return new T2(0,_1YK.a,_1YK.b);}),_1YL=new T(function(){var _1YM=B(_1XE(new T(function(){return E(E(_1YJ).a);}),_1YI.a));return new T2(0,_1YM.a,_1YM.b);});return new T2(0,new T(function(){return E(E(_1YL).a);}),new T2(1,new T(function(){return E(E(_1YL).b);}),new T(function(){return E(E(_1YJ).b);})));}},_1YN=new T(function(){return B(unCStr(")"));}),_1YO=function(_1YP,_1YQ){var _1YR=new T(function(){var _1YS=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_1YQ,_4)),_1YN));})));},1);return B(_0(B(_bZ(0,_1YP,_4)),_1YS));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1YR)));});},_1YT=new T(function(){return B(unCStr("Int"));}),_1YU=function(_1YV,_1YW,_1YX){return new F(function(){return _eX(_ea,new T2(0,_1YW,_1YX),_1YV,_1YT);});},_1YY=new T(function(){return B(unCStr("&|"));}),_1YZ=new T1(1,_1YY),_1Z0=new T2(1,_1YZ,_4),_1Z1=new T0(2),_1Z2=new T2(1,_1Z1,_4),_1Z3=new T(function(){return B(unCStr("&+"));}),_1Z4=new T1(1,_1Z3),_1Z5=new T2(1,_1Z4,_4),_1Z6=function(_1Z7,_1Z8,_1Z9){var _1Za=function(_1Zb,_1Zc){var _1Zd=B(_1Ej(_1Z9,_1Zb)),_1Ze=E(_1Zd.a),_1Zf=E(E(_1Zd.e).b),_1Zg=_1Zf.c,_1Zh=E(_1Zf.a),_1Zi=E(_1Zf.b);if(_1Zh>_1Zc){return new F(function(){return _1YU(_1Zc,_1Zh,_1Zi);});}else{if(_1Zc>_1Zi){return new F(function(){return _1YU(_1Zc,_1Zh,_1Zi);});}else{var _1Zj=_1Zc-_1Zh|0;if(0>_1Zj){return new F(function(){return _1YO(_1Zj,_1Zg);});}else{if(_1Zj>=_1Zg){return new F(function(){return _1YO(_1Zj,_1Zg);});}else{var _1Zk=E(_1Zf.d[_1Zj]);return (_1Zk._==0)?__Z:(!B(A1(_1Z7,_1Ze)))?E(_1Zk):new T2(1,new T(function(){return new T6(0,_1Ze.a,E(_1Ze.b),_1Zc,_1Zd.c,_1Zd.d,_1Zk);}),_4);}}}}},_1Zl=function(_1Zm){var _1Zn=E(_1Zm);if(!_1Zn._){return __Z;}else{var _1Zo=E(_1Zn.a);return new T2(1,new T2(0,new T(function(){return B(_1Zp(_1Zo.a));}),_1Zo.b),new T(function(){return B(_1Zl(_1Zn.b));}));}},_1Zq=function(_1Zr){var _1Zs=E(_1Zr);if(!_1Zs._){return __Z;}else{return new F(function(){return _0(B(_1Zt(_1Zs.a)),new T(function(){return B(_1Zq(_1Zs.b));},1));});}},_1Zt=function(_1Zu){var _1Zv=E(_1Zu);switch(_1Zv._){case 0:return new F(function(){return _1Za(_1Zv.a,_1Zv.b);});break;case 1:return new F(function(){return _1Za(_1Zv.a,_1Zv.b);});break;case 2:return new T2(1,new T1(1,new T(function(){var _1Zw=B(_1Ej(E(B(_1Ej(_1Z9,_1Zv.a)).e).a,_1Zv.b));return B(_1Dm(_1Zw.a,_1Zw.b,_1Zw.c));})),_4);case 3:return new T2(1,new T1(1,_1Zv.a),_4);case 4:return new T2(1,new T2(6,new T(function(){return B(_1Zq(_1Zv.a));}),new T(function(){return B(_1Zl(_1Zv.b));})),_4);case 5:return E(_1Z5);case 6:return E(_1Z2);case 7:return __Z;case 8:return __Z;case 9:return E(_1Z0);default:return E(_1Z0);}},_1Zp=function(_1Zx){var _1Zy=E(_1Zx);if(!_1Zy._){return __Z;}else{return new F(function(){return _0(B(_1Zt(_1Zy.a)),new T(function(){return B(_1Zp(_1Zy.b));},1));});}},_1Zz=function(_1ZA){var _1ZB=E(_1ZA);if(!_1ZB._){return __Z;}else{return new F(function(){return _0(B(_1Zt(_1ZB.a)),new T(function(){return B(_1Zz(_1ZB.b));},1));});}};return new F(function(){return _1Zz(_1Z8);});},_1ZC=function(_1ZD,_1ZE,_1ZF){return new F(function(){return _eX(_ea,new T2(0,_1ZE,_1ZF),_1ZD,_1YT);});},_1ZG=new T(function(){return B(unCStr("Negative range size"));}),_1ZH=function(_1ZI,_1ZJ,_1ZK,_1ZL,_1ZM){var _1ZN=new T(function(){var _1ZO=function(_){var _1ZP=E(_1ZI),_1ZQ=E(_1ZP.c),_1ZR=_1ZQ.c,_1ZS=E(_1ZQ.a),_1ZT=E(_1ZQ.b),_1ZU=E(_1ZL);if(_1ZS>_1ZU){return new F(function(){return _1ZC(_1ZU,_1ZS,_1ZT);});}else{if(_1ZU>_1ZT){return new F(function(){return _1ZC(_1ZU,_1ZS,_1ZT);});}else{var _1ZV=_1ZU-_1ZS|0;if(0>_1ZV){return new F(function(){return _1YO(_1ZV,_1ZR);});}else{if(_1ZV>=_1ZR){return new F(function(){return _1YO(_1ZV,_1ZR);});}else{var _1ZW=E(_1ZQ.d[_1ZV]),_1ZX=E(_1ZW.b),_1ZY=E(_1ZW.c),_1ZZ=function(_200){if(_200>=0){var _201=newArr(_200,_VA),_202=_201,_203=function(_204){var _205=function(_206,_207,_){while(1){if(_206!=_204){var _208=E(_207);if(!_208._){return _5;}else{var _=_202[_206]=_208.a,_209=_206+1|0;_206=_209;_207=_208.b;continue;}}else{return _5;}}},_20a=new T(function(){var _20b=_1ZW.d-1|0;if(0<=_20b){var _20c=new T(function(){return B(_1Z6(_1ZJ,_4,_1ZM));}),_20d=function(_20e){var _20f=new T(function(){var _20g=E(_1ZP.f),_20h=_20g.c,_20i=E(_20g.a),_20j=E(_20g.b),_20k=_1ZW.e["v"]["i32"][_20e];if(_20i>_20k){return B(_1YU(_20k,_20i,_20j));}else{if(_20k>_20j){return B(_1YU(_20k,_20i,_20j));}else{var _20l=_20k-_20i|0;if(0>_20l){return B(_1YO(_20l,_20h));}else{if(_20l>=_20h){return B(_1YO(_20l,_20h));}else{var _20m=E(_20g.d[_20l]),_20n=_20m.c-1|0;if(0<=_20n){var _20o=function(_20p){return new T2(1,new T(function(){return E(_20m.d[_20p]);}),new T(function(){if(_20p!=_20n){return B(_20o(_20p+1|0));}else{return __Z;}}));};return B(_1Z6(_1ZJ,B(_20o(0)),_1ZM));}else{return E(_20c);}}}}}});return new T2(1,_20f,new T(function(){if(_20e!=_20b){return B(_20d(_20e+1|0));}else{return __Z;}}));};return B(_20d(0));}else{return __Z;}},1),_20q=B(_205(0,_20a,_));return new T4(0,E(_1ZX),E(_1ZY),_200,_202);};if(_1ZX>_1ZY){return new F(function(){return _203(0);});}else{var _20r=(_1ZY-_1ZX|0)+1|0;if(_20r>=0){return new F(function(){return _203(_20r);});}else{return new F(function(){return err(_1ZG);});}}}else{return E(_VC);}};if(_1ZX>_1ZY){return new F(function(){return _1ZZ(0);});}else{return new F(function(){return _1ZZ((_1ZY-_1ZX|0)+1|0);});}}}}}};return B(_8O(_1ZO));});return new T2(0,_1ZK,_1ZN);},_20s=new T(function(){return B(unCStr(")"));}),_20t=function(_20u,_20v){var _20w=new T(function(){var _20x=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_20v,_4)),_20s));})));},1);return B(_0(B(_bZ(0,_20u,_4)),_20x));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_20w)));});},_20y=function(_20z){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_20z));}))));});},_20A=new T(function(){return B(_20y("ww_sZJc Map CId String"));}),_20B=new T(function(){return B(_20y("ww_sZJb Map CId Literal"));}),_20C=new T1(1,_4),_20D=new T2(1,_20C,_4),_20E=0,_20F=new T(function(){return B(unCStr("Int"));}),_20G=function(_20H,_20I){return new F(function(){return _eX(_ea,new T2(0,_20H,_20I),_20E,_20F);});},_20J=function(_20K){return true;},_20L=new T(function(){return B(_20y("ww_sZJl IntMap (IntMap (TrieMap Token IntSet))"));}),_20M=new T(function(){return B(_20y("ww_sZJk Map CId CncCat"));}),_20N=new T(function(){return B(_20y("ww_sZJj Map CId (IntMap (Set Production))"));}),_20O=new T(function(){return B(_20y("ww_sZJi IntMap (Set Production)"));}),_20P=new T(function(){return B(_20y("ww_sZJh IntMap (Set Production)"));}),_20Q=new T(function(){return B(_20y("ww_sZJe IntMap [FunId]"));}),_20R=function(_20S,_20T,_20U,_20V,_20W,_20X,_20Y,_20Z){var _210=B(_151(_20W,_20T));if(!_210._){return E(_20D);}else{var _211=E(_210.a);if(!_211._){return E(_20D);}else{var _212=E(B(_1ZH({_:0,a:_20B,b:_20A,c:_20S,d:_20Q,e:_20T,f:_20U,g:_20P,h:_20O,i:_20N,j:_20M,k:_20L,l:0},_20J,_4,_211.a,new T2(1,new T5(0,E(_20V),_20W,_20X,_20Y,E(_20Z)),_4))).b),_213=_212.c,_214=E(_212.a),_215=E(_212.b);if(_214>0){return new F(function(){return _20G(_214,_215);});}else{if(0>_215){return new F(function(){return _20G(_214,_215);});}else{var _216= -_214|0;if(0>_216){return new F(function(){return _20t(_216,_213);});}else{if(_216>=_213){return new F(function(){return _20t(_216,_213);});}else{return E(_212.d[_216]);}}}}}}},_217=new T(function(){return B(unCStr("no lang"));}),_218=new T(function(){return B(err(_217));}),_219=function(_21a){return E(E(_21a).d);},_21b=function(_21c,_21d,_21e,_21f){var _21g=function(_21h,_21i,_21j){while(1){var _21k=E(_21i),_21l=E(_21j);if(!_21l._){switch(B(A3(_13t,_21c,_21k,_21l.b))){case 0:_21i=_21k;_21j=_21l.d;continue;case 1:return E(_21l.c);default:_21i=_21k;_21j=_21l.e;continue;}}else{return E(_21h);}}};return new F(function(){return _21g(_21d,_21e,_21f);});},_21m=function(_21n){var _21o=function(_){var _21p=newArr(1,_VA),_21q=_21p,_21r=function(_21s,_21t,_){while(1){var _21u=E(_21s);if(_21u==1){return _5;}else{var _21v=E(_21t);if(!_21v._){return _5;}else{var _=_21q[_21u]=_21v.a;_21s=_21u+1|0;_21t=_21v.b;continue;}}}},_21w=B(_21r(0,new T2(1,new T2(1,new T1(1,_21n),_4),_4),_));return new T4(0,E(_20E),E(_20E),1,_21q);};return new F(function(){return _8O(_21o);});},_21x=function(_21y,_21z,_21A,_21B){while(1){var _21C=E(_21B);if(!_21C._){var _21D=E(_21C.b);switch(B(_12Z(_21y,_21z,_21A,_21D.a,_21D.b,_21D.c))){case 0:_21B=_21C.d;continue;case 1:return new T1(1,_21C.c);default:_21B=_21C.e;continue;}}else{return __Z;}}},_21E=new T(function(){return B(unCStr("Float"));}),_21F=new T(function(){return B(_1zg(_21E));}),_21G=new T(function(){return B(_G(_1ze,_21F));}),_21H=new T(function(){var _21I=B(_1y0(_21G));return new T3(0,_21I.a,_21I.b,_21I.c);}),_21J=new T(function(){return B(_1zg(_1YT));}),_21K=new T(function(){return B(_G(_1ze,_21J));}),_21L=new T(function(){var _21M=B(_1y0(_21K));return new T3(0,_21M.a,_21M.b,_21M.c);}),_21N=new T(function(){return B(unCStr("String"));}),_21O=new T(function(){return B(_1zg(_21N));}),_21P=new T(function(){return B(_G(_1ze,_21O));}),_21Q=new T(function(){var _21R=B(_1y0(_21P));return new T3(0,_21R.a,_21R.b,_21R.c);}),_21S=function(_21T){var _21U=E(_21T);return (_21U._==0)?__Z:new T2(1,E(_21U.a).b,new T(function(){return B(_21S(_21U.b));}));},_21V=function(_21W){var _21X=E(_21W);return (_21X._==0)?__Z:new T2(1,new T(function(){return E(E(E(_21X.a).c).b);}),new T(function(){return B(_21V(_21X.b));}));},_21Y=new T(function(){return B(_7f("pgf/PGF/Linearize.hs:(77,5)-(87,137)|function lin"));}),_21Z=63,_220=new T(function(){return B(_1QQ("pgf/PGF/Linearize.hs:105:19-70|Just (ty, _, _, _)"));}),_221=new T(function(){return B(_7f("pgf/PGF/Linearize.hs:(104,13)-(109,85)|function toApp"));}),_222=new T(function(){return B(unCStr("]"));}),_223=function(_224,_225,_226,_227){if(!B(_18U(_228,_224,_226))){return false;}else{return new F(function(){return _1aP(_225,_227);});}},_229=function(_22a,_22b){var _22c=E(_22a),_22d=E(_22b);return new F(function(){return _223(_22c.a,_22c.b,_22d.a,_22d.b);});},_22e=function(_22f,_22g,_22h,_22i){return (!B(_18U(_228,_22f,_22h)))?true:(!B(_1aP(_22g,_22i)))?true:false;},_22j=function(_22k,_22l){var _22m=E(_22k),_22n=E(_22l);return new F(function(){return _22e(_22m.a,_22m.b,_22n.a,_22n.b);});},_22o=new T(function(){return new T2(0,_229,_22j);}),_22p=function(_22q,_22r){var _22s=E(_22q);switch(_22s._){case 0:var _22t=E(_22r);if(!_22t._){var _22u=E(_22s.a),_22v=E(_22t.a);if(!B(_12S(_22u.a,_22u.b,_22u.c,_22v.a,_22v.b,_22v.c))){return false;}else{if(_22s.b!=_22t.b){return false;}else{if(_22s.c!=_22t.c){return false;}else{var _22w=E(_22s.d),_22x=E(_22t.d);if(!B(_12S(_22w.a,_22w.b,_22w.c,_22x.a,_22x.b,_22x.c))){return false;}else{if(!B(_18U(_194,_22s.e,_22t.e))){return false;}else{return new F(function(){return _18U(_228,_22s.f,_22t.f);});}}}}}}else{return false;}break;case 1:var _22y=E(_22r);if(_22y._==1){return new F(function(){return _sl(_22s.a,_22y.a);});}else{return false;}break;case 2:return (E(_22r)._==2)?true:false;case 3:return (E(_22r)._==3)?true:false;case 4:return (E(_22r)._==4)?true:false;case 5:return (E(_22r)._==5)?true:false;default:var _22z=E(_22r);if(_22z._==6){if(!B(_18U(_228,_22s.a,_22z.a))){return false;}else{return new F(function(){return _18U(_22o,_22s.b,_22z.b);});}}else{return false;}}},_22A=function(_22B,_22C){return (!B(_22p(_22B,_22C)))?true:false;},_228=new T(function(){return new T2(0,_22p,_22A);}),_22D=function(_22E,_22F){var _22G=E(_22E),_22H=E(_22F),_22I=E(_22G.c);if(!_22I){return (E(_22H.c)==0)?true:false;}else{if(E(_22G.a)!=E(_22H.a)){return false;}else{if(E(_22G.b)!=E(_22H.b)){return false;}else{var _22J=_22I-1|0;if(0<=_22J){var _22K=function(_22L){while(1){if(!B(_18U(_228,_22G.d[_22L],_22H.d[_22L]))){return false;}else{if(_22L!=_22J){var _22M=_22L+1|0;_22L=_22M;continue;}else{return true;}}}};return new F(function(){return _22K(0);});}else{return true;}}}}},_22N=function(_22O,_22P){var _22Q=E(_22O),_22R=E(_22P),_22S=E(_22Q.a),_22T=E(_22R.a),_22U=E(_22S.a),_22V=E(_22T.a);if(!B(_12S(_22U.a,_22U.b,_22U.c,_22V.a,_22V.b,_22V.c))){return false;}else{if(E(_22S.b)!=E(_22T.b)){return false;}else{if(E(_22Q.b)!=E(_22R.b)){return false;}else{var _22W=E(_22Q.c),_22X=E(_22R.c);if(!B(_12S(_22W.a,_22W.b,_22W.c,_22X.a,_22X.b,_22X.c))){return false;}else{if(!B(_18U(_194,_22Q.d,_22R.d))){return false;}else{var _22Y=E(_22Q.e),_22Z=E(_22R.e);if(!B(_18U(_1Cg,_22Y.a,_22Z.a))){return false;}else{return new F(function(){return _22D(_22Y.b,_22Z.b);});}}}}}}},_230=function(_231,_232,_233){while(1){var _234=E(_233);if(!_234._){return false;}else{if(!B(A2(_231,_234.a,_232))){_233=_234.b;continue;}else{return true;}}}},_235=function(_236,_237){var _238=function(_239,_23a){while(1){var _23b=B((function(_23c,_23d){var _23e=E(_23c);if(!_23e._){return __Z;}else{var _23f=_23e.a,_23g=_23e.b;if(!B(_230(_236,_23f,_23d))){return new T2(1,_23f,new T(function(){return B(_238(_23g,new T2(1,_23f,_23d)));}));}else{var _23h=_23d;_239=_23g;_23a=_23h;return __continue;}}})(_239,_23a));if(_23b!=__continue){return _23b;}}};return new F(function(){return _238(_237,_4);});},_23i=function(_23j,_23k,_23l){var _23m=new T(function(){return E(E(E(_23j).c).b);}),_23n=new T(function(){return E(E(_23k).h);}),_23o=new T(function(){return E(E(_23k).d);}),_23p=function(_23q,_23r,_23s,_23t,_23u){var _23v=E(_23q);if(!_23v._){return __Z;}else{var _23w=E(_23v.a),_23x=_23w.a,_23y=E(_23w.b),_23z=B(_151(_23y,_23o));if(!_23z._){if(!B(_w5(_j7,_23y,_1p4))){var _23A=B(_151(_23y,_23n));if(!_23A._){return __Z;}else{var _23B=function(_23C,_23D){while(1){var _23E=B((function(_23F,_23G){var _23H=E(_23G);if(!_23H._){var _23I=_23H.d,_23J=new T(function(){var _23K=E(_23H.b);if(_23K._==1){return B(_0(B(_23p(new T1(1,new T2(0,_23x,_23K.a)),_23r,_23s,_23t,_23u)),new T(function(){return B(_23B(_23F,_23I));},1)));}else{return B(_23B(_23F,_23I));}},1);_23C=_23J;_23D=_23H.c;return __continue;}else{return E(_23F);}})(_23C,_23D));if(_23E!=__continue){return _23E;}}};return new F(function(){return _23B(_4,_23A.a);});}}else{var _23L=new T(function(){var _23M=function(_){var _23N=newArr(1,_VA),_23O=_23N,_23P=function(_23Q,_23R,_){while(1){var _23S=E(_23Q);if(_23S==1){return _5;}else{var _23T=E(_23R);if(!_23T._){return _5;}else{var _=_23O[_23S]=_23T.a;_23Q=_23S+1|0;_23R=_23T.b;continue;}}}},_23U=B(_23P(0,new T2(1,new T2(1,new T1(1,_23u),_4),_4),_));return new T4(0,E(_20E),E(_20E),1,_23O);};return B(_8O(_23M));});return new T2(1,new T2(0,new T(function(){return E(_23r)+2|0;}),new T5(0,new T2(0,_23x,new T(function(){return E(_23r)+1|0;})),_23y,_1RI,new T2(1,_23s,_4),new T2(0,_23t,_23L))),_4);}}else{var _23V=new T2(1,_23s,_4),_23W=new T(function(){return E(_23r)+2|0;}),_23X=new T(function(){return B(_21m(_23u));}),_23Y=new T(function(){return E(_23r)+1|0;}),_23Z=function(_240){var _241=E(_240);return (_241._==0)?__Z:new T2(1,new T2(0,_23W,new T5(0,new T2(0,_23x,_23Y),_23y,_1RI,_23V,new T(function(){var _242=B(_1ZH(_23k,_20J,_23t,_241.a,new T2(1,new T5(0,new T2(0,_1RI,_23r),_1oY,_1RI,_23V,new T2(0,_4,_23X)),_4)));return new T2(0,_242.a,_242.b);}))),new T(function(){return B(_23Z(_241.b));}));};return new F(function(){return _23Z(_23z.a);});}}},_243=new T(function(){return E(E(_23k).i);}),_244=function(_245,_246,_247,_248,_249,_24a,_24b){while(1){var _24c=B((function(_24d,_24e,_24f,_24g,_24h,_24i,_24j){var _24k=E(_24i);switch(_24k._){case 0:var _24l=_24d,_24m=_24e,_24n=_24f,_24o=_24g,_24p=new T2(1,_24k.b,_24h),_24q=_24j;_245=_24l;_246=_24m;_247=_24n;_248=_24o;_249=_24p;_24a=_24k.c;_24b=_24q;return __continue;case 1:var _24l=_24d,_24m=_24e,_24n=_24f,_24o=_24g,_24p=_24h,_24q=new T2(1,_24k.b,_24j);_245=_24l;_246=_24m;_247=_24n;_248=_24o;_249=_24p;_24a=_24k.a;_24b=_24q;return __continue;case 2:if(!E(_24j)._){var _24r=E(_24k.a);switch(_24r._){case 0:return new T2(1,new T2(0,new T(function(){return E(_24e)+1|0;}),new T5(0,new T2(0,_21Q,_24e),_1oY,_1RI,new T2(1,_24f,_4),new T2(0,_4,new T(function(){return B(_21m(_24r.a));})))),_4);case 1:var _24s=new T(function(){return B(_21m(new T(function(){return B(_bZ(0,E(_24r.a),_4));})));});return new T2(1,new T2(0,new T(function(){return E(_24e)+1|0;}),new T5(0,new T2(0,_21L,_24e),_1oZ,_1RI,new T2(1,_24f,_4),new T2(0,_4,_24s))),_4);default:var _24t=new T(function(){return B(_21m(new T(function(){var _24u=jsShow(E(_24r.a));return fromJSStr(_24u);})));});return new T2(1,new T2(0,new T(function(){return E(_24e)+1|0;}),new T5(0,new T2(0,_21H,_24e),_1p0,_1RI,new T2(1,_24f,_4),new T2(0,_4,_24t))),_4);}}else{return E(_21Y);}break;case 3:return new F(function(){return _23p(_24d,_24e,_24f,_24h,new T2(1,_21Z,new T(function(){return B(_bZ(0,_24k.a,_4));})));});break;case 4:var _24v=E(_24k.a),_24w=_24v.a,_24x=_24v.b,_24y=_24v.c,_24z=B(_21x(_24w,_24x,_24y,_243));if(!_24z._){var _24A=new T(function(){return B(unAppCStr("[",new T(function(){return B(_0(B(_1Dm(_24w,_24x,_24y)),_222));})));});return new F(function(){return _23p(_24d,_24e,_24f,_24h,_24A);});}else{var _24B=_24z.a,_24C=new T(function(){var _24D=B(_21x(_24w,_24x,_24y,_23m));if(!_24D._){return E(_220);}else{var _24E=E(E(_24D.a).a);return new T2(0,new T(function(){return B(_21V(_24E.a));}),_24E.b);}}),_24F=new T(function(){return E(E(_24C).b);}),_24G=new T(function(){return E(E(_24C).a);}),_24H=function(_24I,_24J){var _24K=E(_24J);switch(_24K._){case 0:var _24L=new T(function(){return B(_jV(_24G,new T(function(){return B(_21S(_24K.b));},1)));});return new T2(1,new T3(0,_24K.a,new T2(0,_24F,_24I),_24L),_4);case 1:var _24M=_24K.a,_24N=B(_151(_24M,_24B));if(!_24N._){return __Z;}else{var _24O=function(_24P,_24Q){while(1){var _24R=B((function(_24S,_24T){var _24U=E(_24T);if(!_24U._){var _24V=new T(function(){return B(_0(B(_24H(_24M,_24U.b)),new T(function(){return B(_24O(_24S,_24U.d));},1)));},1);_24P=_24V;_24Q=_24U.c;return __continue;}else{return E(_24S);}})(_24P,_24Q));if(_24R!=__continue){return _24R;}}};return new F(function(){return _24O(_4,_24N.a);});}break;default:return E(_221);}},_24W=new T(function(){return B(_0(_24h,_24g));}),_24X=function(_24Y,_24Z){var _250=E(_24Z);if(!_250._){return new T2(1,new T2(0,_24Y,_4),_4);}else{var _251=E(_250.a),_252=_251.b,_253=function(_254){var _255=E(_254);if(!_255._){return __Z;}else{var _256=E(_255.a),_257=new T(function(){return B(_253(_255.b));}),_258=function(_259){var _25a=E(_259);if(!_25a._){return E(_257);}else{var _25b=E(_25a.a);return new T2(1,new T2(0,_25b.a,new T2(1,_256.b,_25b.b)),new T(function(){return B(_258(_25a.b));}));}};return new F(function(){return _258(B(_24X(_256.a,_250.b)));});}};return new F(function(){return _253(B(_244(new T1(1,_251.a),_24Y,_252,_24W,_4,_252,_4)));});}},_25c=function(_25d,_25e,_25f,_25g,_25h){var _25i=function(_25j){var _25k=E(_25j);if(!_25k._){return E(_25h);}else{var _25l=E(_25k.a),_25m=_25l.a;return new T2(1,new T2(0,new T(function(){return E(_25m)+1|0;}),new T5(0,new T2(0,_25e,_25m),_25f,_24v,new T2(1,_24f,_4),new T(function(){var _25n=B(_1ZH(_23k,_20J,_24h,_25d,_25l.b));return new T2(0,_25n.a,_25n.b);}))),new T(function(){return B(_25i(_25k.b));}));}};return new F(function(){return _25i(B(_24X(_24e,B(_jV(_25g,_24j)))));});},_25o=E(_24d);if(!_25o._){var _25p=function(_25q,_25r){while(1){var _25s=B((function(_25t,_25u){var _25v=E(_25u);switch(_25v._){case 0:_25q=new T(function(){return B(_25p(_25t,_25v.d));},1);_25r=_25v.c;return __continue;case 1:var _25w=function(_25x,_25y){while(1){var _25z=B((function(_25A,_25B){var _25C=E(_25B);if(!_25C._){var _25D=new T(function(){var _25E=new T(function(){return B(_25w(_25A,_25C.d));}),_25F=function(_25G){var _25H=E(_25G);if(!_25H._){return E(_25E);}else{var _25I=E(_25H.a),_25J=E(_25I.b);return new F(function(){return _25c(_25I.a,_25J.a,_25J.b,_25I.c,new T(function(){return B(_25F(_25H.b));}));});}};return B(_25F(B(_24H(_25v.a,_25C.b))));},1);_25x=_25D;_25y=_25C.c;return __continue;}else{return E(_25A);}})(_25x,_25y));if(_25z!=__continue){return _25z;}}};return new F(function(){return _25w(_25t,_25v.b);});break;default:return E(_25t);}})(_25q,_25r));if(_25s!=__continue){return _25s;}}},_25K=E(_24B);if(!_25K._){var _25L=_25K.c,_25M=_25K.d;if(_25K.b>=0){return new F(function(){return _25p(new T(function(){return B(_25p(_4,_25M));},1),_25L);});}else{return new F(function(){return _25p(new T(function(){return B(_25p(_4,_25L));},1),_25M);});}}else{return new F(function(){return _25p(_4,_25K);});}}else{var _25N=E(E(_25o.a).b),_25O=B(_151(_25N,_24B));if(!_25O._){return __Z;}else{var _25P=function(_25Q,_25R){while(1){var _25S=B((function(_25T,_25U){var _25V=E(_25U);if(!_25V._){var _25W=new T(function(){var _25X=new T(function(){return B(_25P(_25T,_25V.d));}),_25Y=function(_25Z){var _260=E(_25Z);if(!_260._){return E(_25X);}else{var _261=E(_260.a),_262=E(_261.b);return new F(function(){return _25c(_261.a,_262.a,_262.b,_261.c,new T(function(){return B(_25Y(_260.b));}));});}};return B(_25Y(B(_24H(_25N,_25V.b))));},1);_25Q=_25W;_25R=_25V.c;return __continue;}else{return E(_25T);}})(_25Q,_25R));if(_25S!=__continue){return _25S;}}};return new F(function(){return _25P(_4,_25O.a);});}}}break;case 5:return new F(function(){return _23p(_24d,_24e,_24f,_24h,new T(function(){var _263=B(_1Ej(B(_0(_24h,_24g)),_24k.a));return B(_1Dm(_263.a,_263.b,_263.c));}));});break;case 6:var _24l=_24d,_24m=_24e,_24n=_24f,_24o=_24g,_24p=_24h,_24q=_24j;_245=_24l;_246=_24m;_247=_24n;_248=_24o;_249=_24p;_24a=_24k.a;_24b=_24q;return __continue;default:var _24l=_24d,_24m=_24e,_24n=_24f,_24o=_24g,_24p=_24h,_24q=_24j;_245=_24l;_246=_24m;_247=_24n;_248=_24o;_249=_24p;_24a=_24k.a;_24b=_24q;return __continue;}})(_245,_246,_247,_248,_249,_24a,_24b));if(_24c!=__continue){return _24c;}}};return new F(function(){return _235(_22N,B(_G(_1FN,B(_244(_4l,_20E,_23l,_4,_4,_23l,_4)))));});},_264=function(_265){var _266=E(_265);if(!_266._){return __Z;}else{return new F(function(){return _0(_266.a,new T(function(){return B(_264(_266.b));},1));});}},_267=function(_268){var _269=E(_268);if(!_269._){return E(_1Xm);}else{var _26a=E(_269.a);if(!_26a._){return __Z;}else{var _26b=B(_267(_269.b));return (_26b._==0)?__Z:new T1(1,new T2(1,_26a.a,_26b.a));}}},_26c=function(_26d,_26e){var _26f=new T(function(){return B(_21b(_1KK,_218,_26e,B(_219(_26d))));}),_26g=function(_26h,_26i,_26j,_26k,_26l){var _26m=E(_26f),_26n=B(_267(B(_1YF(B(_20R(_26m.c,_26m.e,_26m.f,_26h,_26i,_26j,_26k,_26l)),_4l)).b));if(!_26n._){return __Z;}else{return new F(function(){return _264(_26n.a);});}},_26o=function(_26p){var _26q=E(_26p);return new F(function(){return _26g(_26q.a,E(_26q.b),_26q.c,_26q.d,_26q.e);});};return function(_26r){var _26s=B(_G(_26o,B(_23i(_26d,_26f,_26r))));return (_26s._==0)?__Z:E(_26s.a);};},_26t=new T(function(){return B(unCStr("?0"));}),_26u=new T2(0,_4,_26t),_26v=new T2(1,_26u,_4),_26w=0,_26x=new T(function(){return B(_1Vz(_4,_4));}),_26y=function(_26z,_26A,_26B,_26C){while(1){var _26D=B((function(_26E,_26F,_26G,_26H){var _26I=E(_26E);if(!_26I._){return __Z;}else{var _26J=_26I.b,_26K=E(_26I.a);if(!_26K._){var _26L=E(_26F);if(E(_26K.b)!=_26L){var _26M=B(_26y(_26K.c,_26L,new T2(1,_26H,_26G),_26w));if(!_26M._){var _26N=_26G;_26z=_26J;_26A=_26L;_26B=_26N;_26C=new T(function(){return E(_26H)+1|0;});return __continue;}else{return E(_26M);}}else{return new T2(1,_26H,_26G);}}else{var _26O=_26F,_26N=_26G;_26z=_26J;_26A=_26O;_26B=_26N;_26C=new T(function(){return E(_26H)+1|0;});return __continue;}}})(_26z,_26A,_26B,_26C));if(_26D!=__continue){return _26D;}}},_26P=function(_26Q,_26R){var _26S=E(_26Q);if(!_26S._){var _26T=E(_26R);if(E(_26S.b)!=_26T){return new F(function(){return _1Vz(B(_26y(_26S.c,_26T,_4,_26w)),_4);});}else{return E(_26x);}}else{return E(_26x);}},_26U=new T(function(){return B(_7f("Muste.hs:(45,9)-(54,31)|function deep"));}),_26V=function(_26W,_26X,_26Y,_26Z){var _270=E(_26Y);if(!_270._){return E(_26Z);}else{var _271=_270.b,_272=E(_270.a);if(!_272._){return new T2(1,new T2(0,new T(function(){return B(_26P(_26W,_26X));}),_272.a),new T(function(){return B(_26V(_26W,_26X,_271,_26Z));}));}else{return new F(function(){return _0(B(_273(_26W,_272)),new T(function(){return B(_26V(_26W,_26X,_271,_26Z));},1));});}}},_273=function(_274,_275){var _276=E(_275);if(!_276._){return E(_26U);}else{var _277=_276.b,_278=E(_276.f);if(!_278._){return __Z;}else{var _279=function(_27a){var _27b=E(_276.e);if(!_27b._){return new F(function(){return _26V(_274,_277,_278,_4);});}else{var _27c=E(_27b.a);if(_27c._==3){if(!E(_27b.b)._){var _27d=new T(function(){return B(unAppCStr("?",new T(function(){return B(_bZ(0,_27c.a,_4));})));});return new T2(1,new T2(0,new T(function(){return B(_26P(_274,_277));}),_27d),_4);}else{return new F(function(){return _26V(_274,_277,_278,_4);});}}else{return new F(function(){return _26V(_274,_277,_278,_4);});}}},_27e=E(_278.a);if(!_27e._){if(!E(_278.b)._){return new T2(1,new T2(0,new T(function(){return B(_26P(_274,_277));}),_27e.a),_4);}else{return new F(function(){return _279(_);});}}else{return new F(function(){return _279(_);});}}}},_27f=function(_27g){return E(E(_27g).c);},_27h=function(_27i){return new T1(3,E(_27i));},_27j=function(_27k,_27l){while(1){var _27m=E(_27k);if(!_27m._){return E(_27l);}else{var _27n=new T2(1,_27l,_27m.a);_27k=_27m.b;_27l=_27n;continue;}}},_27o=function(_27p,_27q){var _27r=E(_27p);if(!_27r._){var _27s=new T(function(){var _27t=B(_27u(_27r.c,_27q));return new T2(0,_27t.a,_27t.b);});return new T2(0,new T(function(){return E(E(_27s).a);}),new T(function(){return B(_27j(E(_27s).b,new T1(4,_27r.a)));}));}else{return new T2(0,new T(function(){return E(_27q)+1|0;}),new T(function(){return B(_27h(_27q));}));}},_27u=function(_27v,_27w){var _27x=E(_27v);if(!_27x._){return new T2(0,_27w,_4);}else{var _27y=new T(function(){var _27z=B(_27o(_27x.a,_27w));return new T2(0,_27z.a,_27z.b);}),_27A=new T(function(){var _27B=B(_27u(_27x.b,new T(function(){return E(E(_27y).a);})));return new T2(0,_27B.a,_27B.b);});return new T2(0,new T(function(){return E(E(_27A).a);}),new T2(1,new T(function(){return E(E(_27y).b);}),new T(function(){return E(E(_27A).b);})));}},_27C=new T1(3,0),_27D=function(_27E){var _27F=E(_27E);if(!_27F._){return new F(function(){return _27j(B(_27u(_27F.c,_26w)).b,new T1(4,_27F.a));});}else{return E(_27C);}},_27G=-1,_27H=function(_27I){var _27J=B(_27K(_27I));return new T3(0,_27J.a,_27J.b,_27J.c);},_27L=new T(function(){return B(unCStr("_"));}),_27M=new T(function(){return B(_1zg(_27L));}),_27N=new T(function(){return B(_G(_1ze,_27M));}),_27O=new T(function(){var _27P=B(_1y0(_27N));return new T3(0,_27P.a,_27P.b,_27P.c);}),_27Q=new T0(1),_27R=new T2(1,_27Q,_4),_27S=new T3(0,_27O,_27G,_27R),_27T=new T2(1,_27S,_4),_27U=new T(function(){return B(_7f("Muste/Tree/Internal.hs:(285,5)-(287,70)|function convert"));}),_27K=function(_27V){var _27W=E(_27V);if(!_27W._){var _27X=E(_27W.b);if(!_27X._){var _27Y=_27X.a,_27Z=E(_27W.c);return (_27Z._==0)?new T3(0,_27Y,_27G,_4):new T3(0,_27Y,_27G,new T(function(){return B(_G(_27H,_27Z));}));}else{return E(_27U);}}else{return new T3(0,_27W.a,_27G,_27T);}},_280=function(_281,_282){var _283=E(_282);if(!_283._){return new T2(0,_281,_4);}else{var _284=new T(function(){var _285=E(_283.a);if(!_285._){var _286=_285.a,_287=E(_285.c);if(!_287._){return new T2(0,new T(function(){return E(_281)+1|0;}),new T3(0,_286,_281,_4));}else{var _288=new T(function(){var _289=B(_280(_281,_287));return new T2(0,_289.a,_289.b);}),_28a=new T(function(){return E(E(_288).a);});return new T2(0,new T(function(){return E(_28a)+1|0;}),new T3(0,_286,_28a,new T(function(){return E(E(_288).b);})));}}else{return new T2(0,_281,_27Q);}}),_28b=new T(function(){var _28c=B(_280(new T(function(){return E(E(_284).a);}),_283.b));return new T2(0,_28c.a,_28c.b);});return new T2(0,new T(function(){return E(E(_28b).a);}),new T2(1,new T(function(){return E(E(_284).b);}),new T(function(){return E(E(_28b).b);})));}},_28d=function(_28e){var _28f=B(_27K(_28e)),_28g=_28f.a,_28h=E(_28f.c);if(!_28h._){return new T3(0,_28g,_26w,_4);}else{var _28i=new T(function(){var _28j=B(_280(_26w,_28h));return new T2(0,_28j.a,_28j.b);});return new T3(0,_28g,new T(function(){return E(E(_28i).a);}),new T(function(){return E(E(_28i).b);}));}},_28k=function(_28l,_28m,_28n){var _28o=new T(function(){return E(E(_28n).a);}),_28p=B(A3(_26c,new T(function(){return B(_27f(_28l));}),_28m,new T(function(){return B(_27D(_28o));})));if(!_28p._){return E(_26v);}else{return new F(function(){return _273(new T(function(){return B(_28d(_28o));}),_28p.a);});}},_28q=new T2(1,_4,_4),_28r=function(_28s,_28t){var _28u=function(_28v,_28w){var _28x=E(_28v);if(!_28x._){return E(_28w);}else{var _28y=_28x.a,_28z=E(_28w);if(!_28z._){return E(_28x);}else{var _28A=_28z.a;return (B(A2(_28s,_28y,_28A))==2)?new T2(1,_28A,new T(function(){return B(_28u(_28x,_28z.b));})):new T2(1,_28y,new T(function(){return B(_28u(_28x.b,_28z));}));}}},_28B=function(_28C){var _28D=E(_28C);if(!_28D._){return __Z;}else{var _28E=E(_28D.b);return (_28E._==0)?E(_28D):new T2(1,new T(function(){return B(_28u(_28D.a,_28E.a));}),new T(function(){return B(_28B(_28E.b));}));}},_28F=new T(function(){return B(_28G(B(_28B(_4))));}),_28G=function(_28H){while(1){var _28I=E(_28H);if(!_28I._){return E(_28F);}else{if(!E(_28I.b)._){return E(_28I.a);}else{_28H=B(_28B(_28I));continue;}}}},_28J=new T(function(){return B(_28K(_4));}),_28L=function(_28M,_28N,_28O){while(1){var _28P=B((function(_28Q,_28R,_28S){var _28T=E(_28S);if(!_28T._){return new T2(1,new T2(1,_28Q,_28R),_28J);}else{var _28U=_28T.a;if(B(A2(_28s,_28Q,_28U))==2){var _28V=new T2(1,_28Q,_28R);_28M=_28U;_28N=_28V;_28O=_28T.b;return __continue;}else{return new T2(1,new T2(1,_28Q,_28R),new T(function(){return B(_28K(_28T));}));}}})(_28M,_28N,_28O));if(_28P!=__continue){return _28P;}}},_28W=function(_28X,_28Y,_28Z){while(1){var _290=B((function(_291,_292,_293){var _294=E(_293);if(!_294._){return new T2(1,new T(function(){return B(A1(_292,new T2(1,_291,_4)));}),_28J);}else{var _295=_294.a,_296=_294.b;switch(B(A2(_28s,_291,_295))){case 0:_28X=_295;_28Y=function(_297){return new F(function(){return A1(_292,new T2(1,_291,_297));});};_28Z=_296;return __continue;case 1:_28X=_295;_28Y=function(_298){return new F(function(){return A1(_292,new T2(1,_291,_298));});};_28Z=_296;return __continue;default:return new T2(1,new T(function(){return B(A1(_292,new T2(1,_291,_4)));}),new T(function(){return B(_28K(_294));}));}}})(_28X,_28Y,_28Z));if(_290!=__continue){return _290;}}},_28K=function(_299){var _29a=E(_299);if(!_29a._){return E(_28q);}else{var _29b=_29a.a,_29c=E(_29a.b);if(!_29c._){return new T2(1,_29a,_4);}else{var _29d=_29c.a,_29e=_29c.b;if(B(A2(_28s,_29b,_29d))==2){return new F(function(){return _28L(_29d,new T2(1,_29b,_4),_29e);});}else{return new F(function(){return _28W(_29d,function(_29f){return new T2(1,_29b,_29f);},_29e);});}}}};return new F(function(){return _28G(B(_28K(_28t)));});},_29g=function(_29h,_29i,_29j,_29k){var _29l=B(_1no(_4,_29k)),_29m=new T(function(){return B(_G(_1FN,B(_28k(_29h,_29i,_29j))));}),_29n=function(_29o,_29p){var _29q=E(_29o);if(!_29q._){return __Z;}else{var _29r=E(_29p);return (_29r._==0)?__Z:new T2(1,new T2(0,new T(function(){var _29s=E(_29m);if(!_29s._){var _29t=B(_v0(_4,0));return _29t+_29t|0;}else{var _29u=B(_G(_1FN,B(_28k(_29h,_29i,_29q.a))));if(!_29u._){var _29v=B(_v0(_4,0));return _29v+_29v|0;}else{var _29w=B(_1VE(_sF,_29s,_29u,_4,_4));return B(_v0(_29w.a,0))+B(_v0(_29w.b,0))|0;}}}),_29r.a),new T(function(){return B(_29n(_29q.b,_29r.b));}));}};return new F(function(){return _G(_1FN,B(_28r(function(_29x,_29y){var _29z=E(_29x),_29A=E(_29y),_29B=E(_29A.a),_29C=E(_29z.a);if(_29B>=_29C){if(_29B!=_29C){return 2;}else{var _29D=B(_28k(_29h,_29i,_29z.b)),_29E=B(_v0(_29D,0)),_29F=B(_28k(_29h,_29i,_29A.b)),_29G=B(_v0(_29F,0));if(_29E>=_29G){if(_29E!=_29G){return 2;}else{return new F(function(){return _1bJ(_1Xi,_29D,_29F);});}}else{return 0;}}}else{return 0;}},B(_29n(_29l,_29l)))));});},_29H=function(_29I){while(1){var _29J=E(_29I);if(!_29J._){return false;}else{if(!E(_29J.a)){_29I=_29J.b;continue;}else{return true;}}}},_29K=function(_29L){var _29M=E(_29L);if(!_29M._){return new F(function(){return _29H(B(_G(_29K,_29M.c)));});}else{return true;}},_29N=function(_29O){return (!B(_29K(B(_1Vf(_29O)))))?true:false;},_29P=function(_29Q){while(1){var _29R=E(_29Q);if(!_29R._){_29Q=new T1(1,I_fromInt(_29R.a));continue;}else{return new F(function(){return I_toString(_29R.a);});}}},_29S=function(_29T,_29U){return new F(function(){return _0(fromJSStr(B(_29P(_29T))),_29U);});},_29V=new T1(0,0),_29W=function(_29X,_29Y,_29Z){if(_29X<=6){return new F(function(){return _29S(_29Y,_29Z);});}else{if(!B(_Fs(_29Y,_29V))){return new F(function(){return _29S(_29Y,_29Z);});}else{return new T2(1,_bY,new T(function(){return B(_0(fromJSStr(B(_29P(_29Y))),new T2(1,_bX,_29Z)));}));}}},_2a0=new T1(0,1),_2a1=new T1(0,0),_2a2=new T(function(){var _2a3=B(_JH(_2a1,_2a0));return new T2(1,_2a3.a,_2a3.b);}),_2a4=32,_2a5=new T(function(){return B(unCStr(" "));}),_2a6=new T2(0,_4,_2a5),_2a7=new T2(1,_2a6,_4),_2a8=function(_2a9){var _2aa=E(_2a9);if(!_2aa._){return E(_2a7);}else{var _2ab=E(_2aa.a);return new T2(1,new T2(0,_2ab.a,_2a5),new T2(1,_2ab,new T(function(){return B(_2a8(_2aa.b));})));}},_2ac=function(_2ad,_2ae,_2af){var _2ag=function(_2ah,_2ai){var _2aj=E(_2ah);if(!_2aj._){return __Z;}else{var _2ak=_2aj.b,_2al=E(_2ai);if(!_2al._){return __Z;}else{var _2am=_2al.b,_2an=new T(function(){var _2ao=E(_2al.a),_2ap=new T(function(){var _2aq=new T(function(){if(!E(_2ad)){return __Z;}else{return B(unAppCStr(" ",new T(function(){return B(_3X(_e4,_2ao.a,_4));})));}},1);return B(_0(_2ao.b,_2aq));});if(!E(_2ae)){return B(_0(_2ap,new T(function(){return B(_2ag(_2ak,_2am));},1)));}else{var _2ar=new T(function(){return B(_0(B(_29W(0,_2aj.a,_4)),new T(function(){return B(unAppCStr(") ",_2ap));},1)));});return B(_0(B(unAppCStr("(",_2ar)),new T(function(){return B(_2ag(_2ak,_2am));},1)));}});return new T2(1,_2a4,_2an);}}},_2as=B(_2ag(_2a2,new T(function(){return B(_2a8(_2af));},1)));return (_2as._==0)?__Z:E(_2as.b);},_2at=function(_2au,_2av,_2aw){var _2ax=function(_2ay){return new F(function(){return _2ac(_wd,_wd,new T(function(){return B(_28k(_2au,_2av,_2ay));},1));});};return new F(function(){return _G(_2ax,_2aw);});},_2az=function(_2aA,_2aB){var _2aC=E(_2aB);if(!_2aC._){return new T2(0,_4,_4);}else{var _2aD=_2aC.a;if(!B(A1(_2aA,_2aD))){var _2aE=new T(function(){var _2aF=B(_2az(_2aA,_2aC.b));return new T2(0,_2aF.a,_2aF.b);});return new T2(0,new T2(1,_2aD,new T(function(){return E(E(_2aE).a);})),new T(function(){return E(E(_2aE).b);}));}else{return new T2(0,_4,_2aC);}}},_2aG=function(_2aH){var _2aI=_2aH>>>0;if(_2aI>887){var _2aJ=u_iswspace(_2aH);return (E(_2aJ)==0)?false:true;}else{var _2aK=E(_2aI);return (_2aK==32)?true:(_2aK-9>>>0>4)?(E(_2aK)==160)?true:false:true;}},_2aL=function(_2aM){return new F(function(){return _2aG(E(_2aM));});},_2aN=function(_2aO){var _2aP=B(_Gd(_2aL,_2aO));if(!_2aP._){return __Z;}else{var _2aQ=new T(function(){var _2aR=B(_2az(_2aL,_2aP));return new T2(0,_2aR.a,_2aR.b);});return new T2(1,new T(function(){return E(E(_2aQ).a);}),new T(function(){return B(_2aN(E(_2aQ).b));}));}},_2aS=function(_2aT,_2aU,_2aV,_2aW,_2aX,_2aY){var _2aZ=new T(function(){var _2b0=B(_1Es(new T(function(){return B(_1Vf(_2aV));}),_2aW));if(!_2b0._){return E(_1Jf);}else{return E(_2b0.a);}}),_2b1=new T2(0,_2aZ,_MR),_2b2=new T(function(){return B(_G(_1FN,B(_28k(_2aT,_2aU,_2b1))));}),_2b3=new T(function(){return B(_v0(_2b2,0));}),_2b4=new T(function(){var _2b5=B(_v0(B(_28k(_2aT,_2aU,_2b1)),0));if(!E(_2aX)){return _2b5;}else{return _2b5+1|0;}}),_2b6=B(_1Uu(function(_2b7){return E(_2b4)>=B(_v0(B(_28k(_2aT,_2aU,_2b7)),0));},B(_29g(_2aT,_2aU,_2b1,B(_1o7(_29N,B(_1Vh(_2aT,_2aV,_2aW,_2aY)))))))),_2b8=function(_2b9,_2ba){while(1){var _2bb=B((function(_2bc,_2bd){var _2be=E(_2bc);if(!_2be._){return __Z;}else{var _2bf=_2be.a,_2bg=_2be.b,_2bh=E(_2bd);if(!_2bh._){return __Z;}else{var _2bi=_2bh.a,_2bj=_2bh.b,_2bk=B(_2aN(_2bf));if(!B(_1aP(_2bk,_2b2))){var _2bl=B(_v0(_2bk,0)),_2bm=E(_2b3);if(_2bl!=_2bm){if(_2bl<=_2bm){_2b9=_2bg;_2ba=_2bj;return __continue;}else{var _2bn=E(_2bk);if(!_2bn._){var _2bo=B(_v0(_4,0));if(!(_2bo+_2bo|0)){_2b9=_2bg;_2ba=_2bj;return __continue;}else{return new T2(1,new T2(0,_2bf,_2bi),new T(function(){return B(_2b8(_2bg,_2bj));}));}}else{var _2bp=E(_2b2);if(!_2bp._){var _2bq=B(_v0(_4,0));if(!(_2bq+_2bq|0)){_2b9=_2bg;_2ba=_2bj;return __continue;}else{return new T2(1,new T2(0,_2bf,_2bi),new T(function(){return B(_2b8(_2bg,_2bj));}));}}else{var _2br=B(_1VE(_sF,_2bn,_2bp,_4,_4));if(!(B(_v0(_2br.a,0))+B(_v0(_2br.b,0))|0)){_2b9=_2bg;_2ba=_2bj;return __continue;}else{return new T2(1,new T2(0,_2bf,_2bi),new T(function(){return B(_2b8(_2bg,_2bj));}));}}}}}else{return new T2(1,new T2(0,_2bf,_2bi),new T(function(){return B(_2b8(_2bg,_2bj));}));}}else{_2b9=_2bg;_2ba=_2bj;return __continue;}}}})(_2b9,_2ba));if(_2bb!=__continue){return _2bb;}}};return new F(function(){return _2b8(B(_2at(_2aT,_2aU,_2b6)),_2b6);});},_2bs=new T(function(){return new T1(1,"top");}),_2bt=new T(function(){return new T2(0,E(new T1(2,"class")),"menu");}),_2bu=new T(function(){return B(unCStr("offsetTop"));}),_2bv=new T(function(){return B(unCStr("offsetLeft"));}),_2bw=new T(function(){return B(unCStr("won"));}),_2bx=new T(function(){return new T2(0,E(new T1(2,"id")),"suggestionList");}),_2by=1,_2bz=new T(function(){return B(err(_rq));}),_2bA=new T(function(){return B(err(_rs));}),_2bB=function(_2bC,_2bD){var _2bE=function(_2bF,_2bG){var _2bH=function(_2bI){return new F(function(){return A1(_2bG,new T(function(){return  -E(_2bI);}));});},_2bJ=new T(function(){return B(_CX(function(_2bK){return new F(function(){return A3(_2bC,_2bK,_2bF,_2bH);});}));}),_2bL=function(_2bM){return E(_2bJ);},_2bN=function(_2bO){return new F(function(){return A2(_BE,_2bO,_2bL);});},_2bP=new T(function(){return B(_CX(function(_2bQ){var _2bR=E(_2bQ);if(_2bR._==4){var _2bS=E(_2bR.a);if(!_2bS._){return new F(function(){return A3(_2bC,_2bR,_2bF,_2bG);});}else{if(E(_2bS.a)==45){if(!E(_2bS.b)._){return E(new T1(1,_2bN));}else{return new F(function(){return A3(_2bC,_2bR,_2bF,_2bG);});}}else{return new F(function(){return A3(_2bC,_2bR,_2bF,_2bG);});}}}else{return new F(function(){return A3(_2bC,_2bR,_2bF,_2bG);});}}));}),_2bT=function(_2bU){return E(_2bP);};return new T1(1,function(_2bV){return new F(function(){return A2(_BE,_2bV,_2bT);});});};return new F(function(){return _DO(_2bE,_2bD);});},_2bW=function(_2bX){var _2bY=E(_2bX);if(!_2bY._){var _2bZ=_2bY.b,_2c0=new T(function(){return B(_vf(new T(function(){return B(_oF(E(_2bY.a)));}),new T(function(){return B(_v0(_2bZ,0));},1),B(_G(_v5,_2bZ))));});return new T1(1,_2c0);}else{return (E(_2bY.b)._==0)?(E(_2bY.c)._==0)?new T1(1,new T(function(){return B(_vw(_uZ,_2bY.a));})):__Z:__Z;}},_2c1=function(_2c2){var _2c3=E(_2c2);if(_2c3._==5){var _2c4=B(_2bW(_2c3.a));if(!_2c4._){return E(_GM);}else{var _2c5=new T(function(){return B(_oV(_2c4.a));});return function(_2c6,_2c7){return new F(function(){return A1(_2c7,_2c5);});};}}else{return E(_GM);}},_2c8=new T(function(){return B(A3(_2bB,_2c1,_Du,_Is));}),_2c9=new T(function(){return B(unCStr(" Clicks"));}),_2ca=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:263:11-20"));}),_2cb=new T6(0,_4l,_4m,_4,_2ca,_4l,_4l),_2cc=new T(function(){return B(_4d(_2cb));}),_2cd=new T(function(){return B(_1nv(_1K2,_MR,_MR));}),_2ce=new T(function(){return B(unCStr("Click on suggestion"));}),_2cf=new T(function(){return B(unCStr("px"));}),_2cg=new T(function(){return B(unCStr(")"));}),_2ch=new T(function(){return new T1(1,"left");}),_2ci=function(_2cj){return new T2(0,_2cj,_MR);},_2ck=new T(function(){return eval("(function(e){if(e){e.stopPropagation();}})");}),_2cl=function(_){var _2cm=rMV(E(_1HW)),_2cn=E(_2cm);if(!_2cn._){var _2co=__app1(E(_2ck),E(_D));return new F(function(){return _u(_);});}else{var _2cp=__app1(E(_2ck),E(_2cn.a));return new F(function(){return _u(_);});}},_2cq=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_2cr=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_2cs=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_2ct=function(_2cu,_2cv,_2cw,_2cx){var _2cy=new T(function(){return B(A2(_1Ji,_2cu,_2cw));}),_2cz=function(_2cA,_){var _2cB=E(_2cA);if(!_2cB._){return _5;}else{var _2cC=E(_2cy),_2cD=E(_1HM),_2cE=__app2(_2cD,E(_2cB.a),_2cC),_2cF=function(_2cG,_){while(1){var _2cH=E(_2cG);if(!_2cH._){return _5;}else{var _2cI=__app2(_2cD,E(_2cH.a),_2cC);_2cG=_2cH.b;continue;}}};return new F(function(){return _2cF(_2cB.b,_);});}},_2cJ=function(_2cK,_){while(1){var _2cL=B((function(_2cM,_){var _2cN=E(_2cM);if(!_2cN._){return _5;}else{var _2cO=_2cN.b,_2cP=E(_2cN.a);if(!_2cP._){var _2cQ=_2cP.b,_2cR=E(_2cP.a);switch(_2cR._){case 0:var _2cS=E(_2cy),_2cT=E(_2cs),_2cU=__app3(_2cT,_2cS,_2cR.a,_2cQ),_2cV=function(_2cW,_){while(1){var _2cX=E(_2cW);if(!_2cX._){return _5;}else{var _2cY=_2cX.b,_2cZ=E(_2cX.a);if(!_2cZ._){var _2d0=_2cZ.b,_2d1=E(_2cZ.a);switch(_2d1._){case 0:var _2d2=__app3(_2cT,_2cS,_2d1.a,_2d0);_2cW=_2cY;continue;case 1:var _2d3=__app3(E(_2cr),_2cS,_2d1.a,_2d0);_2cW=_2cY;continue;default:var _2d4=__app3(E(_2cq),_2cS,_2d1.a,_2d0);_2cW=_2cY;continue;}}else{var _2d5=B(_2cz(_2cZ.a,_));_2cW=_2cY;continue;}}}};return new F(function(){return _2cV(_2cO,_);});break;case 1:var _2d6=E(_2cy),_2d7=E(_2cr),_2d8=__app3(_2d7,_2d6,_2cR.a,_2cQ),_2d9=function(_2da,_){while(1){var _2db=E(_2da);if(!_2db._){return _5;}else{var _2dc=_2db.b,_2dd=E(_2db.a);if(!_2dd._){var _2de=_2dd.b,_2df=E(_2dd.a);switch(_2df._){case 0:var _2dg=__app3(E(_2cs),_2d6,_2df.a,_2de);_2da=_2dc;continue;case 1:var _2dh=__app3(_2d7,_2d6,_2df.a,_2de);_2da=_2dc;continue;default:var _2di=__app3(E(_2cq),_2d6,_2df.a,_2de);_2da=_2dc;continue;}}else{var _2dj=B(_2cz(_2dd.a,_));_2da=_2dc;continue;}}}};return new F(function(){return _2d9(_2cO,_);});break;default:var _2dk=E(_2cy),_2dl=E(_2cq),_2dm=__app3(_2dl,_2dk,_2cR.a,_2cQ),_2dn=function(_2do,_){while(1){var _2dp=E(_2do);if(!_2dp._){return _5;}else{var _2dq=_2dp.b,_2dr=E(_2dp.a);if(!_2dr._){var _2ds=_2dr.b,_2dt=E(_2dr.a);switch(_2dt._){case 0:var _2du=__app3(E(_2cs),_2dk,_2dt.a,_2ds);_2do=_2dq;continue;case 1:var _2dv=__app3(E(_2cr),_2dk,_2dt.a,_2ds);_2do=_2dq;continue;default:var _2dw=__app3(_2dl,_2dk,_2dt.a,_2ds);_2do=_2dq;continue;}}else{var _2dx=B(_2cz(_2dr.a,_));_2do=_2dq;continue;}}}};return new F(function(){return _2dn(_2cO,_);});}}else{var _2dy=B(_2cz(_2cP.a,_));_2cK=_2cO;return __continue;}}})(_2cK,_));if(_2cL!=__continue){return _2cL;}}};return new F(function(){return A2(_6i,_2cv,function(_){return new F(function(){return _2cJ(_2cx,_);});});});},_2dz=function(_2dA,_2dB,_2dC,_2dD){var _2dE=B(_2z(_2dB)),_2dF=function(_2dG){return new F(function(){return A3(_6c,_2dE,new T(function(){return B(_2ct(_2dA,_2dB,_2dG,_2dD));}),new T(function(){return B(A2(_dh,_2dE,_2dG));}));});};return new F(function(){return A3(_1V,_2dE,_2dC,_2dF);});},_2dH=new T(function(){return eval("(function(x){console.log(x);})");}),_2dI=function(_2dJ,_2dK,_2dL,_2dM,_2dN,_2dO,_){var _2dP=B(_2cl(_)),_2dQ=E(_2dK),_2dR=rMV(_2dQ),_2dS=new T(function(){var _2dT=E(E(_2dR).d);if(!_2dT._){return new T2(0,_2dL,_2by);}else{var _2dU=E(_2dT.a),_2dV=E(_2dL);if(E(_2dU.a)!=_2dV){return new T2(0,_2dV,_2by);}else{return new T2(0,_2dV,new T(function(){return E(_2dU.b)+1|0;}));}}}),_=wMV(_2dQ,new T5(0,new T(function(){return E(E(_2dR).a);}),new T(function(){return E(E(_2dR).b);}),new T(function(){return E(E(_2dR).c);}),new T1(1,_2dS),new T(function(){return E(E(_2dR).e);}))),_2dW=B(A(_1Jt,[_dm,_dn,_2dJ,_2bv,_])),_2dX=B(A(_1Jt,[_dm,_dn,_2dJ,_2bu,_])),_2dY=new T(function(){return E(E(_2dO).a);}),_2dZ=new T(function(){var _2e0=B(_Iz(B(_rx(_2c8,_2dW))));if(!_2e0._){return E(_2bz);}else{if(!E(_2e0.b)._){return E(E(_2dY).a)+E(_2e0.a)|0;}else{return E(_2bA);}}}),_2e1=new T(function(){var _2e2=B(_Iz(B(_rx(_2c8,_2dX))));if(!_2e2._){return E(_2bz);}else{if(!E(_2e2.b)._){return E(E(_2dY).b)+E(_2e2.a)|0;}else{return E(_2bA);}}}),_2e3=new T(function(){var _2e4=new T(function(){return B(unAppCStr(",",new T(function(){return B(_0(B(_bZ(0,E(_2e1),_4)),_2cg));})));},1);return B(_0(B(_bZ(0,E(_2dZ),_4)),_2e4));}),_2e5=E(_2dH),_2e6=__app1(_2e5,toJSStr(B(unAppCStr("Click on (",_2e3)))),_2e7=B(_1J7(_1EK,_)),_2e8=new T(function(){var _2e9=(B(_v0(_2dM,0))+1|0)-E(E(_2dS).b)|0;if(0>=_2e9){return __Z;}else{return B(_1EE(_2e9,_2dM));}}),_2ea=new T(function(){return B(_3X(_e4,_2e8,_4));}),_2eb=new T(function(){return B(_0(B(_3X(_e4,_2dM,_4)),new T(function(){return B(unAppCStr(" with selected path ",_2ea));},1)));}),_2ec=__app1(_2e5,toJSStr(B(unAppCStr("Full path ",_2eb)))),_2ed=B(A(_2dz,[_dm,_dn,_1IH,new T2(1,_2bx,new T2(1,_2bt,new T2(1,new T(function(){return new T2(0,E(_2bs),toJSStr(B(_0(B(_bZ(0,E(_2e1),_4)),_2cf))));}),new T2(1,new T(function(){return new T2(0,E(_2ch),toJSStr(B(_0(B(_bZ(0,E(_2dZ),_4)),_2cf))));}),_4)))),_])),_2ee=_2ed,_2ef=function(_2eg,_){while(1){var _2eh=B((function(_2ei,_){var _2ej=E(_2ei);if(!_2ej._){return _5;}else{var _2ek=E(_2ej.a),_2el=_2ek.b,_2em=new T(function(){var _2en=new T(function(){var _2eo=new T(function(){return B(unAppCStr(" with ",new T(function(){return B(_1DQ(E(_2el).a));})));},1);return B(_0(_2ea,_2eo));});return B(unAppCStr(" at ",_2en));}),_2ep=new T(function(){return E(E(_2el).a);}),_2eq=function(_2er,_){var _2es=B(_2cl(_)),_2et=__app1(_2e5,toJSStr(E(_2ce))),_2eu=B(_1J7(_1EK,_)),_2ev=rMV(_2dQ),_2ew=_2ev,_2ex=new T(function(){return E(E(_2ew).c);}),_2ey=new T(function(){var _2ez=B(_1Es(new T(function(){return B(_1Vf(_2ex));}),_2e8));if(!_2ez._){return E(_1Jf);}else{var _2eA=new T(function(){return B(unAppCStr(" in ",new T(function(){return B(_0(B(_1DQ(E(_2ex).a)),_2em));})));},1);return B(_0(B(_1DQ(_2ez.a)),_2eA));}}),_2eB=__app1(_2e5,toJSStr(B(unAppCStr("Trying to replace ",_2ey)))),_2eC=B(_1R0(B(_1Vf(_2ex)),_2e8,_2ep)),_=wMV(_2dQ,new T5(0,new T(function(){return E(E(_2ew).a);}),new T(function(){return E(E(_2ew).b);}),new T(function(){return B(_2ci(_2eC));}),_4l,new T(function(){return E(E(_2ew).e)+1|0;})));if(!B(_1Cr(_2eC,_1HC))){var _2eD=B(_1IM(_2dQ,_));return new F(function(){return _2eE(_2dQ,_);});}else{if(!E(_2cd)){var _2eF=B(_1IM(_2dQ,_));return new F(function(){return _2eE(_2dQ,_);});}else{var _2eG=__app1(E(_1IJ),toJSStr(E(_1IL))),_2eH=__eq(_2eG,E(_D)),_2eI=function(_,_2eJ){var _2eK=E(_2eJ);if(!_2eK._){return new F(function(){return die(_2cc);});}else{var _2eL=__app2(E(_1HF),E(_2eK.a),toJSStr(E(_2bw))),_2eM=__app1(E(_1Jc),toJSStr(B(unAppCStr("Congratulations! You won after ",new T(function(){return B(_0(B(_bZ(0,E(E(_2ew).e)+1|0,_4)),_2c9));}))))),_2eN=B(_1IM(_2dQ,_));return new F(function(){return _2eE(_2dQ,_);});}};if(!E(_2eH)){var _2eO=__isUndef(_2eG);if(!E(_2eO)){return new F(function(){return _2eI(_,new T1(1,_2eG));});}else{return new F(function(){return _2eI(_,_4l);});}}else{return new F(function(){return _2eI(_,_4l);});}}}},_2eP=B(_1Is(_2ee,_2ek.a,_2eq,_));_2eg=_2ej.b;return __continue;}})(_2eg,_));if(_2eh!=__continue){return _2eh;}}},_2eQ=B(_2ef(B(_2aS(new T(function(){return E(E(_2dR).a);}),new T(function(){return E(E(_2dR).b);}),new T(function(){return E(E(_2dR).c);}),_2e8,_2dN,_1Jd)),_)),_2eR=__app2(E(_1HM),E(_2ee),E(_1J0));return _5;},_2eS=function(_){return new F(function(){return __app1(E(_1HL),"span");});},_2eT=new T(function(){return new T2(0,E(new T1(2,"class")),"path");}),_2eU=new T2(1,_2eT,_4),_2eV=new T(function(){return B(_2dz(_dm,_dn,_2eS,_2eU));}),_2eW=new T(function(){return new T2(0,E(new T1(2,"class")),"word");}),_2eX=new T2(1,_2eW,_4),_2eY=new T(function(){return B(_2dz(_dm,_dn,_2eS,_2eX));}),_2eZ=new T(function(){return new T2(0,E(new T1(2,"class")),"gap");}),_2f0=new T2(1,_2eZ,_4),_2f1=new T(function(){return B(_2dz(_dm,_dn,_2eS,_2f0));}),_2f2=new T(function(){return B(unCStr(" "));}),_2f3=function(_2f4,_2f5,_2f6,_2f7,_2f8,_2f9,_2fa,_2fb,_){var _2fc=function(_){var _2fd=B(A1(_2eY,_)),_2fe=E(_1HO),_2ff=__app1(_2fe,toJSStr(E(_2f7))),_2fg=E(_2fd),_2fh=E(_1HM),_2fi=__app2(_2fh,_2ff,_2fg),_2fj=E(_2f4),_2fk=__app2(_2fh,_2fg,_2fj),_2fl=function(_){if(!E(_2f9)){return _5;}else{var _2fm=B(A1(_2eV,_)),_2fn=__app1(_2fe,toJSStr(B(_3X(_e4,_2f6,_4)))),_2fo=E(_2fm),_2fp=__app2(_2fh,_2fn,_2fo),_2fq=__app2(_2fh,_2fo,_2fj);return new F(function(){return _u(_);});}};if(!E(_2fb)){return new F(function(){return _2fl(_);});}else{var _2fr=B(A(_1I0,[_do,_df,_de,_2fg,_1Cb,function(_2fs,_){return new F(function(){return _2dI(_2fg,_2f5,_2f8,_2f6,_wd,_2fs,_);});},_]));return new F(function(){return _2fl(_);});}};if(!E(_2fa)){return new F(function(){return _2fc(_);});}else{var _2ft=B(A1(_2f1,_)),_2fu=__app1(E(_1HO),toJSStr(E(_2f2))),_2fv=E(_2ft),_2fw=E(_1HM),_2fx=__app2(_2fw,_2fu,_2fv),_2fy=__app2(_2fw,_2fv,E(_2f4));if(!E(_2fb)){return new F(function(){return _2fc(_);});}else{var _2fz=B(A(_1I0,[_do,_df,_de,_2fv,_1Cb,function(_2fs,_){return new F(function(){return _2dI(_2fv,_2f5,_2f8,_2f6,_we,_2fs,_);});},_]));return new F(function(){return _2fc(_);});}}},_2fA=new T(function(){return eval("(function(e,c) {return e.classList.contains(c);})");}),_2fB=new T(function(){return B(_iF(0,2147483647));}),_2fC=new T(function(){return B(unCStr("ACK"));}),_2fD=new T(function(){return B(unCStr("BEL"));}),_2fE=new T(function(){return B(unCStr("BS"));}),_2fF=new T(function(){return B(unCStr("SP"));}),_2fG=new T2(1,_2fF,_4),_2fH=new T(function(){return B(unCStr("US"));}),_2fI=new T2(1,_2fH,_2fG),_2fJ=new T(function(){return B(unCStr("RS"));}),_2fK=new T2(1,_2fJ,_2fI),_2fL=new T(function(){return B(unCStr("GS"));}),_2fM=new T2(1,_2fL,_2fK),_2fN=new T(function(){return B(unCStr("FS"));}),_2fO=new T2(1,_2fN,_2fM),_2fP=new T(function(){return B(unCStr("ESC"));}),_2fQ=new T2(1,_2fP,_2fO),_2fR=new T(function(){return B(unCStr("SUB"));}),_2fS=new T2(1,_2fR,_2fQ),_2fT=new T(function(){return B(unCStr("EM"));}),_2fU=new T2(1,_2fT,_2fS),_2fV=new T(function(){return B(unCStr("CAN"));}),_2fW=new T2(1,_2fV,_2fU),_2fX=new T(function(){return B(unCStr("ETB"));}),_2fY=new T2(1,_2fX,_2fW),_2fZ=new T(function(){return B(unCStr("SYN"));}),_2g0=new T2(1,_2fZ,_2fY),_2g1=new T(function(){return B(unCStr("NAK"));}),_2g2=new T2(1,_2g1,_2g0),_2g3=new T(function(){return B(unCStr("DC4"));}),_2g4=new T2(1,_2g3,_2g2),_2g5=new T(function(){return B(unCStr("DC3"));}),_2g6=new T2(1,_2g5,_2g4),_2g7=new T(function(){return B(unCStr("DC2"));}),_2g8=new T2(1,_2g7,_2g6),_2g9=new T(function(){return B(unCStr("DC1"));}),_2ga=new T2(1,_2g9,_2g8),_2gb=new T(function(){return B(unCStr("DLE"));}),_2gc=new T2(1,_2gb,_2ga),_2gd=new T(function(){return B(unCStr("SI"));}),_2ge=new T2(1,_2gd,_2gc),_2gf=new T(function(){return B(unCStr("SO"));}),_2gg=new T2(1,_2gf,_2ge),_2gh=new T(function(){return B(unCStr("CR"));}),_2gi=new T2(1,_2gh,_2gg),_2gj=new T(function(){return B(unCStr("FF"));}),_2gk=new T2(1,_2gj,_2gi),_2gl=new T(function(){return B(unCStr("VT"));}),_2gm=new T2(1,_2gl,_2gk),_2gn=new T(function(){return B(unCStr("LF"));}),_2go=new T2(1,_2gn,_2gm),_2gp=new T(function(){return B(unCStr("HT"));}),_2gq=new T2(1,_2gp,_2go),_2gr=new T2(1,_2fE,_2gq),_2gs=new T2(1,_2fD,_2gr),_2gt=new T2(1,_2fC,_2gs),_2gu=new T(function(){return B(unCStr("ENQ"));}),_2gv=new T2(1,_2gu,_2gt),_2gw=new T(function(){return B(unCStr("EOT"));}),_2gx=new T2(1,_2gw,_2gv),_2gy=new T(function(){return B(unCStr("ETX"));}),_2gz=new T2(1,_2gy,_2gx),_2gA=new T(function(){return B(unCStr("STX"));}),_2gB=new T2(1,_2gA,_2gz),_2gC=new T(function(){return B(unCStr("SOH"));}),_2gD=new T2(1,_2gC,_2gB),_2gE=new T(function(){return B(unCStr("NUL"));}),_2gF=new T2(1,_2gE,_2gD),_2gG=92,_2gH=new T(function(){return B(unCStr("\\DEL"));}),_2gI=new T(function(){return B(unCStr("\\a"));}),_2gJ=new T(function(){return B(unCStr("\\\\"));}),_2gK=new T(function(){return B(unCStr("\\SO"));}),_2gL=new T(function(){return B(unCStr("\\r"));}),_2gM=new T(function(){return B(unCStr("\\f"));}),_2gN=new T(function(){return B(unCStr("\\v"));}),_2gO=new T(function(){return B(unCStr("\\n"));}),_2gP=new T(function(){return B(unCStr("\\t"));}),_2gQ=new T(function(){return B(unCStr("\\b"));}),_2gR=function(_2gS,_2gT){if(_2gS<=127){var _2gU=E(_2gS);switch(_2gU){case 92:return new F(function(){return _0(_2gJ,_2gT);});break;case 127:return new F(function(){return _0(_2gH,_2gT);});break;default:if(_2gU<32){var _2gV=E(_2gU);switch(_2gV){case 7:return new F(function(){return _0(_2gI,_2gT);});break;case 8:return new F(function(){return _0(_2gQ,_2gT);});break;case 9:return new F(function(){return _0(_2gP,_2gT);});break;case 10:return new F(function(){return _0(_2gO,_2gT);});break;case 11:return new F(function(){return _0(_2gN,_2gT);});break;case 12:return new F(function(){return _0(_2gM,_2gT);});break;case 13:return new F(function(){return _0(_2gL,_2gT);});break;case 14:return new F(function(){return _0(_2gK,new T(function(){var _2gW=E(_2gT);if(!_2gW._){return __Z;}else{if(E(_2gW.a)==72){return B(unAppCStr("\\&",_2gW));}else{return E(_2gW);}}},1));});break;default:return new F(function(){return _0(new T2(1,_2gG,new T(function(){return B(_1Ej(_2gF,_2gV));})),_2gT);});}}else{return new T2(1,_2gU,_2gT);}}}else{var _2gX=new T(function(){var _2gY=jsShowI(_2gS);return B(_0(fromJSStr(_2gY),new T(function(){var _2gZ=E(_2gT);if(!_2gZ._){return __Z;}else{var _2h0=E(_2gZ.a);if(_2h0<48){return E(_2gZ);}else{if(_2h0>57){return E(_2gZ);}else{return B(unAppCStr("\\&",_2gZ));}}}},1)));});return new T2(1,_2gG,_2gX);}},_2h1=new T(function(){return B(unCStr("\\\""));}),_2h2=function(_2h3,_2h4){var _2h5=E(_2h3);if(!_2h5._){return E(_2h4);}else{var _2h6=_2h5.b,_2h7=E(_2h5.a);if(_2h7==34){return new F(function(){return _0(_2h1,new T(function(){return B(_2h2(_2h6,_2h4));},1));});}else{return new F(function(){return _2gR(_2h7,new T(function(){return B(_2h2(_2h6,_2h4));}));});}}},_2h8=34,_2h9=function(_2ha,_2hb){return new T2(1,_2h8,new T(function(){return B(_2h2(_2ha,new T2(1,_2h8,_2hb)));}));},_2hc=function(_2hd,_2he){var _2hf=E(_2hd),_2hg=new T(function(){return B(A3(_em,_ec,new T2(1,function(_2hh){return new F(function(){return _e7(_2hf.a,_2hh);});},new T2(1,function(_2hi){return new F(function(){return _2h9(_2hf.b,_2hi);});},_4)),new T2(1,_bX,_2he)));});return new T2(1,_bY,_2hg);},_2hj=new T(function(){return B(unCStr("debug"));}),_2hk=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:138:5-20"));}),_2hl=new T6(0,_4l,_4m,_4,_2hk,_4l,_4l),_2hm=new T(function(){return B(_4d(_2hl));}),_2hn=new T(function(){return B(unCStr("editTree"));}),_2eE=function(_2ho,_){var _2hp=rMV(_2ho),_2hq=B(_28k(new T(function(){return E(E(_2hp).a);},1),new T(function(){return E(E(_2hp).b);},1),new T(function(){return E(E(_2hp).c);},1))),_2hr=__app1(E(_2dH),toJSStr(B(_3X(_2hc,_2hq,_4)))),_2hs=__app1(E(_1IJ),toJSStr(E(_2hn))),_2ht=__eq(_2hs,E(_D)),_2hu=function(_,_2hv){var _2hw=E(_2hv);if(!_2hw._){return new F(function(){return die(_2hm);});}else{var _2hx=E(_2hw.a),_2hy=__app1(E(_1II),_2hx),_2hz=__app2(E(_2fA),_2hx,toJSStr(E(_2hj))),_2hA=_2hz,_2hB=function(_2hC,_2hD,_){while(1){var _2hE=E(_2hC);if(!_2hE._){return _5;}else{var _2hF=E(_2hD);if(!_2hF._){return _5;}else{var _2hG=E(_2hF.a),_2hH=B(_2f3(_2hx,_2ho,_2hG.a,_2hG.b,_2hE.a,_2hA,_we,_we,_));_2hC=_2hE.b;_2hD=_2hF.b;continue;}}}},_2hI=B(_2hB(_2fB,_2hq,_));return _5;}};if(!E(_2ht)){var _2hJ=__isUndef(_2hs);if(!E(_2hJ)){return new F(function(){return _2hu(_,new T1(1,_2hs));});}else{return new F(function(){return _2hu(_,_4l);});}}else{return new F(function(){return _2hu(_,_4l);});}},_2hK=new T(function(){return B(unCStr("FoodsEng"));}),_2hL=new T(function(){return B(_1zg(_2hK));}),_2hM=new T(function(){return B(_G(_1ze,_2hL));}),_2hN=new T(function(){var _2hO=B(_1y0(_2hM));return new T3(0,_2hO.a,_2hO.b,_2hO.c);}),_2hP=0,_2hQ=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:89:5-22"));}),_2hR=new T6(0,_4l,_4m,_4,_2hQ,_4l,_4l),_2hS=new T(function(){return B(_4d(_2hR));}),_2hT=new T(function(){return B(unCStr("sampleTree"));}),_2hU=new T2(0,_1HC,_MR),_2hV=function(_2hW,_){var _2hX=rMV(_2hW),_2hY=_2hX,_2hZ=__app1(E(_1IJ),toJSStr(E(_2hT))),_2i0=__eq(_2hZ,E(_D)),_2i1=function(_,_2i2){var _2i3=E(_2i2);if(!_2i3._){return new F(function(){return die(_2hS);});}else{var _2i4=E(_2i3.a),_2i5=__app1(E(_1II),_2i4),_2i6=__app2(E(_2fA),_2i4,toJSStr(E(_2hj))),_2i7=_2i6,_2i8=function(_2i9,_){while(1){var _2ia=E(_2i9);if(!_2ia._){return _5;}else{var _2ib=E(_2ia.a),_2ic=B(_2f3(_2i4,_2hW,_2ib.a,_2ib.b,_2hP,_2i7,_wd,_wd,_));_2i9=_2ia.b;continue;}}},_2id=B(_2i8(B(_28k(new T(function(){return E(E(_2hY).a);},1),_2hN,_2hU)),_));return _5;}};if(!E(_2i0)){var _2ie=__isUndef(_2hZ);if(!E(_2ie)){return new F(function(){return _2i1(_,new T1(1,_2hZ));});}else{return new F(function(){return _2i1(_,_4l);});}}else{return new F(function(){return _2i1(_,_4l);});}},_2if=new T(function(){return eval("(function(a){var arr = new ByteArray(new a.constructor(a[\'buffer\']));return new T4(0,0,a[\'length\']-1,a[\'length\'],arr);})");}),_2ig=function(_2ih){return E(_2ih);},_2ii=function(_2ij){return E(E(_2ij).a);},_2ik=function(_2il){return E(E(_2il).a);},_2im=function(_2in){return E(E(_2in).a);},_2io=function(_2ip){return E(E(_2ip).b);},_2iq=function(_2ir){return E(E(_2ir).a);},_2is=function(_2it){var _2iu=new T(function(){return B(A2(_2iq,B(_2ii(B(_2im(B(_2ik(B(_2io(_2it)))))))),_2ig));}),_2iv=function(_2iw){var _2ix=function(_){return new F(function(){return __app1(E(_2if),E(_2iw));});};return new F(function(){return A1(_2iu,_2ix);});};return E(_2iv);},_2iy="(function(from, to, buf){return new Uint8Array(buf.buffer.slice(from, to+from));})",_2iz=function(_2iA,_2iB,_2iC,_2iD){var _2iE=function(_){var _2iF=eval(E(_2iy)),_2iG=__app3(E(_2iF),E(_2iB),E(_2iC),E(_2iD));return new F(function(){return A3(_2is,_2iA,_2iG,0);});};return new F(function(){return _z(_2iE);});},_2iH=new T(function(){return B(unCStr("menuList"));}),_2iI=new T(function(){return eval("(function(b){return b.size;})");}),_2iJ=function(_2iK){return new F(function(){return _z(function(_){var _2iL=__app1(E(_2iI),E(_2iK));return new F(function(){return _cr(_2iL,0);});});});},_2iM=0,_2iN=new T1(1,_4),_2iO=new T(function(){return eval("(function(b,cb){var r=new FileReader();r.onload=function(){cb(new DataView(r.result));};r.readAsArrayBuffer(b);})");}),_2iP=function(_2iQ,_2iR){var _2iS=new T(function(){return B(_2iJ(_2iR));}),_2iT=function(_2iU){var _2iV=function(_){var _2iW=nMV(_2iN),_2iX=_2iW,_2iY=function(_){var _2iZ=function(_2j0,_){var _2j1=B(_c(new T(function(){return B(A(_7r,[_2l,_2iX,new T3(0,_2iM,_2iS,_2j0),_2c]));}),_4,_));return _D;},_2j2=__createJSFunc(2,E(_2iZ)),_2j3=__app2(E(_2iO),E(_2iR),_2j2);return new T(function(){return B(A3(_7H,_2l,_2iX,_2iU));});};return new T1(0,_2iY);};return new T1(0,_2iV);};return new F(function(){return A2(_6g,_2iQ,_2iT);});},_2j4=new T(function(){return new T2(0,E(new T1(2,"id")),"menuList");}),_2j5=new T(function(){return B(unCStr("AjaxError"));}),_2j6=new T(function(){return B(err(_2j5));}),_2j7=new T(function(){return B(unCStr("Reset"));}),_2j8=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:240:84-90"));}),_2j9=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:240:51-57"));}),_2ja=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:66:5-13"));}),_2jb=new T6(0,_4l,_4m,_4,_2ja,_4l,_4l),_2jc=new T(function(){return B(_4d(_2jb));}),_2jd=new T(function(){return B(unCStr("Click on menu"));}),_2je=new T(function(){return B(unCStr("menuButton"));}),_2jf=new T(function(){return B(unCStr("global click"));}),_2jg=new T(function(){return B(unCStr("Got blobdata"));}),_2jh=new T(function(){return B(unCStr("Foods.pgf"));}),_2ji=new T(function(){return B(unAppCStr("Loaded pgf as Blob ",_2jh));}),_2jj=new T(function(){return B(unCStr("Toggle Debug"));}),_2jk=function(_2jl,_2jm,_2jn,_2jo){while(1){var _2jp=E(_2jo);if(!_2jp._){var _2jq=E(_2jp.b);switch(B(_12Z(_2jl,_2jm,_2jn,_2jq.a,_2jq.b,_2jq.c))){case 0:_2jo=_2jp.d;continue;case 1:return new T1(1,_2jp.c);default:_2jo=_2jp.e;continue;}}else{return __Z;}}},_2jr=function(_2js){return E(E(E(_2js).c).b);},_2jt=function(_2ju,_2jv,_2jw,_2jx,_2jy){var _2jz=E(_1RI);if(!B(_12S(_2ju,_2jv,_2jw,_2jz.a,_2jz.b,_2jz.c))){var _2jA=E(_2jy),_2jB=B(_2jk(_2jA.a,_2jA.b,_2jA.c,E(_2jx).b));if(!_2jB._){return new T0(1);}else{var _2jC=new T(function(){var _2jD=E(E(_2jB.a).a);return new T3(0,_2jD.a,_2jD.b,_2jD.c);});return new T2(0,new T(function(){return E(E(_2jC).b);}),new T(function(){return B(_G(_2jr,E(_2jC).a));}));}}else{return new T0(1);}},_2jE=function(_2jF,_2jG,_2jH,_2jI){while(1){var _2jJ=E(_2jI);if(!_2jJ._){var _2jK=E(_2jJ.b);switch(B(_12Z(_2jF,_2jG,_2jH,_2jK.a,_2jK.b,_2jK.c))){case 0:_2jI=_2jJ.d;continue;case 1:return new T1(1,_2jJ.c);default:_2jI=_2jJ.e;continue;}}else{return __Z;}}},_2jL=new T(function(){return B(unCStr("S"));}),_2jM=new T(function(){return B(_1zg(_2jL));}),_2jN=new T(function(){return B(_G(_1ze,_2jM));}),_2jO=new T(function(){return B(unCStr("startcat"));}),_2jP=new T(function(){return B(_1zg(_2jO));}),_2jQ=new T(function(){return B(_G(_1ze,_2jP));}),_2jR=new T(function(){var _2jS=B(_1y0(_2jQ));return new T3(0,_2jS.a,_2jS.b,_2jS.c);}),_2jT=function(_2jU,_2jV){var _2jW=E(_2jR),_2jX=_2jW.a,_2jY=_2jW.b,_2jZ=_2jW.c,_2k0=B(_2jE(_2jX,_2jY,_2jZ,_2jU));if(!_2k0._){var _2k1=B(_2jE(_2jX,_2jY,_2jZ,E(_2jV).a));if(!_2k1._){return new F(function(){return _1y0(_2jN);});}else{var _2k2=E(_2k1.a);if(!_2k2._){return new F(function(){return _1y0(B(_G(_1ze,B(_1zg(_2k2.a)))));});}else{return new F(function(){return _1y0(_2jN);});}}}else{var _2k3=E(_2k0.a);if(!_2k3._){return new F(function(){return _1y0(B(_G(_1ze,B(_1zg(_2k3.a)))));});}else{return new F(function(){return _1y0(_2jN);});}}},_2k4=function(_2k5,_2k6){return new T2(0,_2k5,_2k6);},_2k7=new T(function(){return B(unCStr("empty grammar, no abstract"));}),_2k8=new T(function(){return B(err(_2k7));}),_2k9=new T4(0,_Rm,_1RI,_2k8,_Rm),_2ka=function(_2kb,_2kc){while(1){var _2kd=B((function(_2ke,_2kf){var _2kg=E(_2kf);if(!_2kg._){_2kb=new T2(1,_2kg.b,new T(function(){return B(_2ka(_2ke,_2kg.e));}));_2kc=_2kg.d;return __continue;}else{return E(_2ke);}})(_2kb,_2kc));if(_2kd!=__continue){return _2kd;}}},_2kh=function(_2ki,_2kj,_2kk){var _2kl=E(_2kj);if(!_2kl._){return __Z;}else{var _2km=E(_2kk);return (_2km._==0)?__Z:new T2(1,new T(function(){return B(A2(_2ki,_2kl.a,_2km.a));}),new T(function(){return B(_2kh(_2ki,_2kl.b,_2km.b));}));}},_2kn=function(_2ko,_2kp,_2kq,_2kr,_2ks,_2kt){var _2ku=E(_1RI);if(!B(_12S(_2kp,_2kq,_2kr,_2ku.a,_2ku.b,_2ku.c))){var _2kv=new T(function(){var _2kw=E(_2ks),_2kx=B(_2ka(_4,_2kw.b)),_2ky=new T(function(){return B(_G(function(_2kz){return new F(function(){return _2jt(_2kp,_2kq,_2kr,_2kw,_2kz);});},_2kx));},1);return B(_2kh(_2k4,_2kx,_2ky));});return new T3(0,new T(function(){var _2kA=B(_2jT(_2ko,_2ks));return new T3(0,_2kA.a,_2kA.b,_2kA.c);}),_2kv,new T4(0,_2ko,new T3(0,_2kp,_2kq,_2kr),_2ks,_2kt));}else{return new T3(0,_2ku,_4,_2k9);}},_2kB=function(_2kC){var _2kD=E(_2kC),_2kE=E(_2kD.b),_2kF=B(_2kn(_2kD.a,_2kE.a,_2kE.b,_2kE.c,_2kD.c,_2kD.d));return new T3(0,_2kF.a,_2kF.b,_2kF.c);},_2kG=0,_2kH=function(_2kI){var _2kJ=E(_2kI);return new F(function(){return _1Dm(_2kJ.a,_2kJ.b,_2kJ.c);});},_2kK=function(_2kL){var _2kM=E(_2kL);if(!_2kM._){return __Z;}else{var _2kN=E(_2kM.a),_2kO=function(_2kP){return E(new T2(3,_2kN.a,_sR));};return new F(function(){return _0(B(_rx(new T1(1,function(_2kQ){return new F(function(){return A2(_BE,_2kQ,_2kO);});}),_2kN.b)),new T(function(){return B(_2kK(_2kM.b));},1));});}},_2kR=function(_2kS){var _2kT=B(_2kK(B(_1FY(_2kS))));return (_2kT._==0)?new T0(2):new T1(4,_2kT);},_2kU=new T1(1,_2kR),_2kV=new T(function(){return B(unCStr("{Pred:(Item->Quality->Comment) {These:(Kind->Item) {Fish:Kind}} {Italian:Quality}}"));}),_2kW=new T(function(){return B(_rx(_2kU,_2kV));}),_2kX=new T(function(){var _2kY=B(_Iz(_2kW));if(!_2kY._){return E(_1EL);}else{if(!E(_2kY.b)._){return E(_2kY.a);}else{return E(_1EM);}}}),_2kZ=new T2(0,_2kX,_MR),_2l0=function(_2l1){var _2l2=E(_2l1);if(!_2l2._){return E(_2j6);}else{var _2l3=function(_){var _2l4=E(_2dH),_2l5=__app1(_2l4,toJSStr(E(_2ji)));return new T(function(){var _2l6=function(_2l7){var _2l8=function(_){var _2l9=__app1(_2l4,toJSStr(E(_2jg))),_2la=new T(function(){var _2lb=E(_2l7),_2lc=B(_2iz(_bP,_2lb.a,_2lb.b,_2lb.c)),_2ld=E(_2lc.a);return E(B(_1BP(_2ld,(E(_2lc.b)-_2ld|0)+1|0,_2lc,_2kG)).a);}),_2le=function(_){var _2lf=__app1(_2l4,toJSStr(B(unAppCStr("Loaded ",new T(function(){return B(_2kH(E(_2la).b));}))))),_2lg=function(_){var _2lh=nMV(new T5(0,new T(function(){return B(_2kB(_2la));}),_2hN,_2kZ,_4l,_2hP)),_2li=_2lh,_2lj=function(_2lk,_){var _2ll=__app1(_2l4,toJSStr(E(_2jf))),_2lm=B(_1J7(_1EK,_)),_2ln=B(_1J7(_2iH,_)),_2lo=rMV(_2li),_=wMV(_2li,new T5(0,new T(function(){return E(E(_2lo).a);}),new T(function(){return E(E(_2lo).b);}),new T(function(){return E(E(_2lo).c);}),_4l,new T(function(){return E(E(_2lo).e);})));return _5;},_2lp=B(A(_1I0,[_do,_df,_de,_1J0,_1Cb,_2lj,_])),_2lq=E(_1IJ),_2lr=__app1(_2lq,toJSStr(E(_2je))),_2ls=E(_D),_2lt=__eq(_2lr,_2ls),_2lu=function(_,_2lv){var _2lw=E(_2lv);if(!_2lw._){return new F(function(){return die(_2jc);});}else{var _2lx=_2lw.a,_2ly=function(_,_2lz){var _2lA=E(_2lz);if(!_2lA._){return new F(function(){return _bC(_2j9,_);});}else{var _2lB=__app1(_2lq,toJSStr(E(_2hT))),_2lC=__eq(_2lB,_2ls),_2lD=function(_,_2lE){var _2lF=E(_2lE);if(!_2lF._){return new F(function(){return _bC(_2j8,_);});}else{var _2lG=toJSStr(E(_2hj)),_2lH=E(_1HF),_2lI=__app2(_2lH,E(_2lA.a),_2lG),_2lJ=__app2(_2lH,E(_2lF.a),_2lG),_2lK=B(_2eE(_2li,_));return new F(function(){return _2hV(_2li,_);});}};if(!E(_2lC)){var _2lL=__isUndef(_2lB);if(!E(_2lL)){return new F(function(){return _2lD(_,new T1(1,_2lB));});}else{return new F(function(){return _2lD(_,_4l);});}}else{return new F(function(){return _2lD(_,_4l);});}}},_2lM=function(_2lN,_){var _2lO=__app1(_2lq,toJSStr(E(_2hn))),_2lP=__eq(_2lO,_2ls);if(!E(_2lP)){var _2lQ=__isUndef(_2lO);if(!E(_2lQ)){return new F(function(){return _2ly(_,new T1(1,_2lO));});}else{return new F(function(){return _2ly(_,_4l);});}}else{return new F(function(){return _2ly(_,_4l);});}},_2lR=function(_2lS,_){var _2lT=B(_2cl(_)),_2lU=__app1(_2l4,toJSStr(E(_2jd))),_2lV=B(A(_1Jt,[_dm,_dn,_2lx,_2bv,_])),_2lW=B(A(_1Jt,[_dm,_dn,_2lx,_2bu,_])),_2lX=B(_1J7(_2iH,_)),_2lY=B(A(_2dz,[_dm,_dn,_1IH,new T2(1,_2j4,new T2(1,_2bt,new T2(1,new T(function(){return new T2(0,E(_2bs),toJSStr(B(_0(_2lW,_2cf))));}),new T2(1,new T(function(){var _2lZ=B(_Iz(B(_rx(_2c8,_2lV))));if(!_2lZ._){return E(_2bz);}else{if(!E(_2lZ.b)._){return new T2(0,E(_2ch),toJSStr(B(_0(B(_bZ(0,E(_2lZ.a)-200|0,_4)),_2cf))));}else{return E(_2bA);}}}),_4)))),_])),_2m0=B(_1Is(_2lY,_2jj,_2lM,_)),_2m1=rMV(_2li),_2m2=nMV(new T5(0,new T(function(){return E(E(_2m1).a);}),new T(function(){return E(E(_2m1).b);}),_2kZ,_4l,_2hP)),_2m3=_2m2,_2m4=B(_1Is(_2lY,_2j7,function(_2m5,_){var _2m6=B(_2eE(_2m3,_)),_2m7=B(_1IM(_2m3,_)),_2m8=rMV(_2m3),_=wMV(_2li,_2m8);return _5;},_)),_2m9=__app2(E(_1HM),E(_2lY),E(_1J0));return _5;},_2ma=B(A(_1I0,[_do,_df,_de,_2lx,_1Cb,_2lR,_])),_2mb=B(_2hV(_2li,_)),_2mc=B(_2eE(_2li,_));return _7q;}};if(!E(_2lt)){var _2md=__isUndef(_2lr);if(!E(_2md)){return new F(function(){return _2lu(_,new T1(1,_2lr));});}else{return new F(function(){return _2lu(_,_4l);});}}else{return new F(function(){return _2lu(_,_4l);});}};return new T1(0,_2lg);};return new T1(0,_2le);};return new T1(0,_2l8);};return B(A3(_2iP,_2l,_2l2.a,_2l6));});};return new T1(0,_2l3);}},_2me=new T(function(){return toJSStr(E(_2jh));}),_2mf=new T(function(){return B(A(_7Y,[_2l,_N,_1b,_i,_h,_2me,_2l0]));}),_2mg=function(_){var _2mh=B(_c(_2mf,_4,_));return _5;},_2mi=function(_){return new F(function(){return _2mg(_);});};
var hasteMain = function() {B(A(_2mi, [0]));};window.onload = hasteMain;