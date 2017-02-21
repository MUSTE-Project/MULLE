"use strict";
var __haste_prog_id = '88edbb0ceb02bfe23bc8df2dfb2c58f37cef055b6cc76faf3e653209a3191c02';
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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=new T1(0,_),_i=new T(function(){return toJSStr(_4);}),_j=function(_k){return E(_i);},_l=function(_m,_){var _n=E(_m);if(!_n._){return _4;}else{var _o=B(_l(_n.b,_));return new T2(1,_5,_o);}},_p=function(_q,_){var _r=__arr2lst(0,_q);return new F(function(){return _l(_r,_);});},_s=function(_t,_){return new F(function(){return _p(E(_t),_);});},_u=function(_){return _5;},_v=function(_w,_){return new F(function(){return _u(_);});},_x=new T2(0,_v,_s),_y=function(_){return new F(function(){return __jsNull();});},_z=function(_A){var _B=B(A1(_A,_));return E(_B);},_C=new T(function(){return B(_z(_y));}),_D=new T(function(){return E(_C);}),_E=function(_F){return E(_D);},_G=function(_H,_I){var _J=E(_I);return (_J._==0)?__Z:new T2(1,new T(function(){return B(A1(_H,_J.a));}),new T(function(){return B(_G(_H,_J.b));}));},_K=function(_L){return new F(function(){return __lst2arr(B(_G(_E,_L)));});},_M=new T2(0,_E,_K),_N=new T4(0,_M,_x,_j,_j),_O="application/octet-stream",_P=function(_Q){return E(_O);},_R="blob",_S=function(_T){return E(_R);},_U=function(_V,_){var _W=E(_V);if(!_W._){return _4;}else{var _X=B(_U(_W.b,_));return new T2(1,_W.a,_X);}},_Y=function(_Z,_){var _10=__arr2lst(0,_Z);return new F(function(){return _U(_10,_);});},_11=function(_12,_){return new F(function(){return _Y(E(_12),_);});},_13=function(_14,_){return _14;},_15=new T2(0,_13,_11),_16=function(_17){return E(_17);},_18=function(_19){return new F(function(){return __lst2arr(B(_G(_16,_19)));});},_1a=new T2(0,_16,_18),_1b=new T4(0,_1a,_15,_P,_S),_1c=function(_1d,_1e,_1f){var _1g=function(_1h){var _1i=new T(function(){return B(A1(_1f,_1h));});return new F(function(){return A1(_1e,function(_1j){return E(_1i);});});};return new F(function(){return A1(_1d,_1g);});},_1k=function(_1l,_1m,_1n){var _1o=new T(function(){return B(A1(_1m,function(_1p){return new F(function(){return A1(_1n,_1p);});}));});return new F(function(){return A1(_1l,function(_1q){return E(_1o);});});},_1r=function(_1s,_1t,_1u){var _1v=function(_1w){var _1x=function(_1y){return new F(function(){return A1(_1u,new T(function(){return B(A1(_1w,_1y));}));});};return new F(function(){return A1(_1t,_1x);});};return new F(function(){return A1(_1s,_1v);});},_1z=function(_1A,_1B){return new F(function(){return A1(_1B,_1A);});},_1C=function(_1D,_1E,_1F){var _1G=new T(function(){return B(A1(_1F,_1D));});return new F(function(){return A1(_1E,function(_1H){return E(_1G);});});},_1I=function(_1J,_1K,_1L){var _1M=function(_1N){return new F(function(){return A1(_1L,new T(function(){return B(A1(_1J,_1N));}));});};return new F(function(){return A1(_1K,_1M);});},_1O=new T2(0,_1I,_1C),_1P=new T5(0,_1O,_1z,_1r,_1k,_1c),_1Q=function(_1R,_1S,_1T){return new F(function(){return A1(_1R,function(_1U){return new F(function(){return A2(_1S,_1U,_1T);});});});},_1V=function(_1W){return E(E(_1W).b);},_1X=function(_1Y,_1Z){return new F(function(){return A3(_1V,_20,_1Y,function(_21){return E(_1Z);});});},_22=function(_23){return new F(function(){return err(_23);});},_20=new T(function(){return new T5(0,_1P,_1Q,_1X,_1z,_22);}),_24=function(_25,_26,_){var _27=B(A1(_26,_));return new T(function(){return B(A1(_25,_27));});},_28=function(_29,_2a){return new T1(0,function(_){return new F(function(){return _24(_2a,_29,_);});});},_2b=new T2(0,_20,_28),_2c=function(_2d){return new T0(2);},_2e=function(_2f){var _2g=new T(function(){return B(A1(_2f,_2c));}),_2h=function(_2i){return new T1(1,new T2(1,new T(function(){return B(A1(_2i,_5));}),new T2(1,_2g,_4)));};return E(_2h);},_2j=function(_2k){return E(_2k);},_2l=new T3(0,_2b,_2j,_2e),_2m=function(_2n){return E(E(_2n).a);},_2o=function(_2p,_2q,_2r,_2s,_2t){var _2u=B(A2(_2m,_2p,E(_2t)));return new F(function(){return A2(_2q,_2r,new T2(1,_2u,E(_2s)));});},_2v=function(_2w){return E(E(_2w).a);},_2x=function(_2y){return E(E(_2y).a);},_2z=function(_2A){return E(E(_2A).a);},_2B=function(_2C){return E(E(_2C).b);},_2D=new T(function(){return B(unCStr("base"));}),_2E=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_2F=new T(function(){return B(unCStr("IOException"));}),_2G=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_2D,_2E,_2F),_2H=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_2G,_4,_4),_2I=function(_2J){return E(_2H);},_2K=function(_2L){return E(E(_2L).a);},_2M=function(_2N,_2O,_2P){var _2Q=B(A1(_2N,_)),_2R=B(A1(_2O,_)),_2S=hs_eqWord64(_2Q.a,_2R.a);if(!_2S){return __Z;}else{var _2T=hs_eqWord64(_2Q.b,_2R.b);return (!_2T)?__Z:new T1(1,_2P);}},_2U=function(_2V){var _2W=E(_2V);return new F(function(){return _2M(B(_2K(_2W.a)),_2I,_2W.b);});},_2X=new T(function(){return B(unCStr(": "));}),_2Y=new T(function(){return B(unCStr(")"));}),_2Z=new T(function(){return B(unCStr(" ("));}),_30=new T(function(){return B(unCStr("interrupted"));}),_31=new T(function(){return B(unCStr("system error"));}),_32=new T(function(){return B(unCStr("unsatisified constraints"));}),_33=new T(function(){return B(unCStr("user error"));}),_34=new T(function(){return B(unCStr("permission denied"));}),_35=new T(function(){return B(unCStr("illegal operation"));}),_36=new T(function(){return B(unCStr("end of file"));}),_37=new T(function(){return B(unCStr("resource exhausted"));}),_38=new T(function(){return B(unCStr("resource busy"));}),_39=new T(function(){return B(unCStr("does not exist"));}),_3a=new T(function(){return B(unCStr("already exists"));}),_3b=new T(function(){return B(unCStr("resource vanished"));}),_3c=new T(function(){return B(unCStr("timeout"));}),_3d=new T(function(){return B(unCStr("unsupported operation"));}),_3e=new T(function(){return B(unCStr("hardware fault"));}),_3f=new T(function(){return B(unCStr("inappropriate type"));}),_3g=new T(function(){return B(unCStr("invalid argument"));}),_3h=new T(function(){return B(unCStr("failed"));}),_3i=new T(function(){return B(unCStr("protocol error"));}),_3j=function(_3k,_3l){switch(E(_3k)){case 0:return new F(function(){return _0(_3a,_3l);});break;case 1:return new F(function(){return _0(_39,_3l);});break;case 2:return new F(function(){return _0(_38,_3l);});break;case 3:return new F(function(){return _0(_37,_3l);});break;case 4:return new F(function(){return _0(_36,_3l);});break;case 5:return new F(function(){return _0(_35,_3l);});break;case 6:return new F(function(){return _0(_34,_3l);});break;case 7:return new F(function(){return _0(_33,_3l);});break;case 8:return new F(function(){return _0(_32,_3l);});break;case 9:return new F(function(){return _0(_31,_3l);});break;case 10:return new F(function(){return _0(_3i,_3l);});break;case 11:return new F(function(){return _0(_3h,_3l);});break;case 12:return new F(function(){return _0(_3g,_3l);});break;case 13:return new F(function(){return _0(_3f,_3l);});break;case 14:return new F(function(){return _0(_3e,_3l);});break;case 15:return new F(function(){return _0(_3d,_3l);});break;case 16:return new F(function(){return _0(_3c,_3l);});break;case 17:return new F(function(){return _0(_3b,_3l);});break;default:return new F(function(){return _0(_30,_3l);});}},_3m=new T(function(){return B(unCStr("}"));}),_3n=new T(function(){return B(unCStr("{handle: "));}),_3o=function(_3p,_3q,_3r,_3s,_3t,_3u){var _3v=new T(function(){var _3w=new T(function(){var _3x=new T(function(){var _3y=E(_3s);if(!_3y._){return E(_3u);}else{var _3z=new T(function(){return B(_0(_3y,new T(function(){return B(_0(_2Y,_3u));},1)));},1);return B(_0(_2Z,_3z));}},1);return B(_3j(_3q,_3x));}),_3A=E(_3r);if(!_3A._){return E(_3w);}else{return B(_0(_3A,new T(function(){return B(_0(_2X,_3w));},1)));}}),_3B=E(_3t);if(!_3B._){var _3C=E(_3p);if(!_3C._){return E(_3v);}else{var _3D=E(_3C.a);if(!_3D._){var _3E=new T(function(){var _3F=new T(function(){return B(_0(_3m,new T(function(){return B(_0(_2X,_3v));},1)));},1);return B(_0(_3D.a,_3F));},1);return new F(function(){return _0(_3n,_3E);});}else{var _3G=new T(function(){var _3H=new T(function(){return B(_0(_3m,new T(function(){return B(_0(_2X,_3v));},1)));},1);return B(_0(_3D.a,_3H));},1);return new F(function(){return _0(_3n,_3G);});}}}else{return new F(function(){return _0(_3B.a,new T(function(){return B(_0(_2X,_3v));},1));});}},_3I=function(_3J){var _3K=E(_3J);return new F(function(){return _3o(_3K.a,_3K.b,_3K.c,_3K.d,_3K.f,_4);});},_3L=function(_3M,_3N,_3O){var _3P=E(_3N);return new F(function(){return _3o(_3P.a,_3P.b,_3P.c,_3P.d,_3P.f,_3O);});},_3Q=function(_3R,_3S){var _3T=E(_3R);return new F(function(){return _3o(_3T.a,_3T.b,_3T.c,_3T.d,_3T.f,_3S);});},_3U=44,_3V=93,_3W=91,_3X=function(_3Y,_3Z,_40){var _41=E(_3Z);if(!_41._){return new F(function(){return unAppCStr("[]",_40);});}else{var _42=new T(function(){var _43=new T(function(){var _44=function(_45){var _46=E(_45);if(!_46._){return E(new T2(1,_3V,_40));}else{var _47=new T(function(){return B(A2(_3Y,_46.a,new T(function(){return B(_44(_46.b));})));});return new T2(1,_3U,_47);}};return B(_44(_41.b));});return B(A2(_3Y,_41.a,_43));});return new T2(1,_3W,_42);}},_48=function(_49,_4a){return new F(function(){return _3X(_3Q,_49,_4a);});},_4b=new T3(0,_3L,_3I,_48),_4c=new T(function(){return new T5(0,_2I,_4b,_4d,_2U,_3I);}),_4d=function(_4e){return new T2(0,_4c,_4e);},_4f="status-text",_4g="status",_4h="http",_4i="network",_4j="type",_4k=__Z,_4l=__Z,_4m=7,_4n=function(_4o,_){var _4p=__get(_4o,E(_4j)),_4q=String(_4p),_4r=strEq(_4q,E(_4i));if(!E(_4r)){var _4s=strEq(_4q,E(_4h));if(!E(_4s)){var _4t=new T(function(){var _4u=new T(function(){return B(unAppCStr("unknown type of ajax error: ",new T(function(){return fromJSStr(_4q);})));});return B(_4d(new T6(0,_4l,_4m,_4,_4u,_4l,_4l)));});return new F(function(){return die(_4t);});}else{var _4v=__get(_4o,E(_4g)),_4w=__get(_4o,E(_4f));return new T2(1,new T(function(){var _4x=Number(_4v);return jsTrunc(_4x);}),new T(function(){return String(_4w);}));}}else{return _4k;}},_4y=function(_4z,_){var _4A=E(_4z);if(!_4A._){return _4;}else{var _4B=B(_4n(E(_4A.a),_)),_4C=B(_4y(_4A.b,_));return new T2(1,_4B,_4C);}},_4D=function(_4E,_){var _4F=__arr2lst(0,_4E);return new F(function(){return _4y(_4F,_);});},_4G=function(_4H,_){return new F(function(){return _4D(E(_4H),_);});},_4I=function(_4J,_){return new F(function(){return _4n(E(_4J),_);});},_4K=new T2(0,_4I,_4G),_4L=function(_4M){return E(E(_4M).a);},_4N=function(_4O,_4P,_){var _4Q=__eq(_4P,E(_D));if(!E(_4Q)){var _4R=__isUndef(_4P);if(!E(_4R)){var _4S=B(A3(_4L,_4O,_4P,_));return new T1(1,_4S);}else{return _4l;}}else{return _4l;}},_4T=function(_4U,_){return new F(function(){return _4N(_4K,E(_4U),_);});},_4V=function(_4W,_4X,_){var _4Y=__arr2lst(0,_4X),_4Z=function(_50,_){var _51=E(_50);if(!_51._){return _4;}else{var _52=_51.b,_53=E(_51.a),_54=__eq(_53,E(_D));if(!E(_54)){var _55=__isUndef(_53);if(!E(_55)){var _56=B(A3(_4L,_4W,_53,_)),_57=B(_4Z(_52,_));return new T2(1,new T1(1,_56),_57);}else{var _58=B(_4Z(_52,_));return new T2(1,_4l,_58);}}else{var _59=B(_4Z(_52,_));return new T2(1,_4l,_59);}}};return new F(function(){return _4Z(_4Y,_);});},_5a=function(_5b,_){return new F(function(){return _4V(_4K,E(_5b),_);});},_5c=new T2(0,_4T,_5a),_5d=2,_5e=function(_5f){return E(_5d);},_5g=function(_5h,_5i,_){var _5j=B(A2(_5h,new T(function(){var _5k=E(_5i),_5l=__eq(_5k,E(_D));if(!E(_5l)){var _5m=__isUndef(_5k);if(!E(_5m)){return new T1(1,_5k);}else{return __Z;}}else{return __Z;}}),_));return _D;},_5n=new T2(0,_5g,_5e),_5o=function(_5p){return E(E(_5p).a);},_5q=function(_5r,_5s,_5t,_5u){var _5v=new T(function(){return B(A1(_5t,new T(function(){var _5w=B(A3(_4L,_5r,_5u,_));return E(_5w);})));});return new F(function(){return A2(_5o,_5s,_5v);});},_5x=function(_5y){return E(E(_5y).b);},_5z=new T(function(){return B(unCStr("Prelude.undefined"));}),_5A=new T(function(){return B(err(_5z));}),_5B=function(_5C,_5D,_5E){var _5F=__createJSFunc(1+B(A2(_5x,_5D,new T(function(){return B(A1(_5E,_5A));})))|0,function(_5G){return new F(function(){return _5q(_5C,_5D,_5E,_5G);});});return E(_5F);},_5H=function(_5I){return new F(function(){return _5B(_5c,_5n,_5I);});},_5J=function(_5K,_5L,_5M){return new F(function(){return _5B(_5K,_5L,_5M);});},_5N=function(_5O,_5P,_5Q){var _5R=__lst2arr(B(_G(function(_5S){return new F(function(){return _5J(_5O,_5P,_5S);});},_5Q)));return E(_5R);},_5T=function(_5U){return new F(function(){return _5N(_5c,_5n,_5U);});},_5V=new T2(0,_5H,_5T),_5W=function(_5X,_5Y,_5Z,_){var _60=__apply(_5Y,E(_5Z));return new F(function(){return A3(_4L,_5X,_60,_);});},_61=function(_62,_63,_64,_){return new F(function(){return _5W(_62,E(_63),_64,_);});},_65=function(_66,_67,_68,_){return new F(function(){return _61(_66,_67,_68,_);});},_69=function(_6a,_6b,_){return new F(function(){return _65(_x,_6a,_6b,_);});},_6c=function(_6d){return E(E(_6d).c);},_6e=0,_6f=new T(function(){return eval("(function(method, uri, mimeout, responseType, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, uri);xhr.responseType = responseType;if(mimeout != \'\') {xhr.setRequestHeader(\'Content-type\', mimeout);}xhr.addEventListener(\'load\', function() {if(xhr.status < 400) {cb(null, xhr.response);}else {cb({\'type\':\'http\', \'status\':xhr.status, \'status-text\': xhr.statusText}, null);}});xhr.addEventListener(\'error\', function() {if(xhr.status != 0) {cb({\'type\':\'http\', \'status\':xhr.status, \'status-text\': xhr.statusText}, null);} else {cb({\'type\':\'network\'}, null);}});xhr.send(postdata);})");}),_6g=function(_6h){return E(E(_6h).b);},_6i=function(_6j){return E(E(_6j).b);},_6k=new T(function(){return B(unCStr("base"));}),_6l=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6m=new T(function(){return B(unCStr("PatternMatchFail"));}),_6n=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6k,_6l,_6m),_6o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6n,_4,_4),_6p=function(_6q){return E(_6o);},_6r=function(_6s){var _6t=E(_6s);return new F(function(){return _2M(B(_2K(_6t.a)),_6p,_6t.b);});},_6u=function(_6v){return E(E(_6v).a);},_6w=function(_6x){return new T2(0,_6y,_6x);},_6z=function(_6A,_6B){return new F(function(){return _0(E(_6A).a,_6B);});},_6C=function(_6D,_6E){return new F(function(){return _3X(_6z,_6D,_6E);});},_6F=function(_6G,_6H,_6I){return new F(function(){return _0(E(_6H).a,_6I);});},_6J=new T3(0,_6F,_6u,_6C),_6y=new T(function(){return new T5(0,_6p,_6J,_6w,_6r,_6u);}),_6K=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_6L=function(_6M){return E(E(_6M).c);},_6N=function(_6O,_6P){return new F(function(){return die(new T(function(){return B(A2(_6L,_6P,_6O));}));});},_6Q=function(_6R,_6S){return new F(function(){return _6N(_6R,_6S);});},_6T=function(_6U,_6V){var _6W=E(_6V);if(!_6W._){return new T2(0,_4,_4);}else{var _6X=_6W.a;if(!B(A1(_6U,_6X))){return new T2(0,_4,_6W);}else{var _6Y=new T(function(){var _6Z=B(_6T(_6U,_6W.b));return new T2(0,_6Z.a,_6Z.b);});return new T2(0,new T2(1,_6X,new T(function(){return E(E(_6Y).a);})),new T(function(){return E(E(_6Y).b);}));}}},_70=32,_71=new T(function(){return B(unCStr("\n"));}),_72=function(_73){return (E(_73)==124)?false:true;},_74=function(_75,_76){var _77=B(_6T(_72,B(unCStr(_75)))),_78=_77.a,_79=function(_7a,_7b){var _7c=new T(function(){var _7d=new T(function(){return B(_0(_76,new T(function(){return B(_0(_7b,_71));},1)));});return B(unAppCStr(": ",_7d));},1);return new F(function(){return _0(_7a,_7c);});},_7e=E(_77.b);if(!_7e._){return new F(function(){return _79(_78,_4);});}else{if(E(_7e.a)==124){return new F(function(){return _79(_78,new T2(1,_70,_7e.b));});}else{return new F(function(){return _79(_78,_4);});}}},_7f=function(_7g){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_7g,_6K));})),_6y);});},_7h=new T(function(){return B(_7f("src/Haste/Ajax.hs:(61,7)-(63,60)|case"));}),_7i="PUT",_7j="POST",_7k="DELETE",_7l="GET",_7m=function(_7n){return E(E(_7n).c);},_7o=new T1(1,_4),_7p=function(_){return new F(function(){return nMV(_7o);});},_7q=new T0(2),_7r=function(_7s,_7t,_7u){var _7v=function(_7w){var _7x=function(_){var _7y=E(_7t),_7z=rMV(_7y),_7A=E(_7z);if(!_7A._){var _7B=new T(function(){var _7C=new T(function(){return B(A1(_7w,_5));});return B(_0(_7A.b,new T2(1,new T2(0,_7u,function(_7D){return E(_7C);}),_4)));}),_=wMV(_7y,new T2(0,_7A.a,_7B));return _7q;}else{var _7E=E(_7A.a);if(!_7E._){var _=wMV(_7y,new T2(0,_7u,_4));return new T(function(){return B(A1(_7w,_5));});}else{var _=wMV(_7y,new T1(1,_7E.b));return new T1(1,new T2(1,new T(function(){return B(A1(_7w,_5));}),new T2(1,new T(function(){return B(A2(_7E.a,_7u,_2c));}),_4)));}}};return new T1(0,_7x);};return new F(function(){return A2(_6g,_7s,_7v);});},_7F=function(_7G){return E(E(_7G).d);},_7H=function(_7I,_7J){var _7K=function(_7L){var _7M=function(_){var _7N=E(_7J),_7O=rMV(_7N),_7P=E(_7O);if(!_7P._){var _7Q=_7P.a,_7R=E(_7P.b);if(!_7R._){var _=wMV(_7N,_7o);return new T(function(){return B(A1(_7L,_7Q));});}else{var _7S=E(_7R.a),_=wMV(_7N,new T2(0,_7S.a,_7R.b));return new T1(1,new T2(1,new T(function(){return B(A1(_7L,_7Q));}),new T2(1,new T(function(){return B(A1(_7S.b,_2c));}),_4)));}}else{var _7T=new T(function(){var _7U=function(_7V){var _7W=new T(function(){return B(A1(_7L,_7V));});return function(_7X){return E(_7W);};};return B(_0(_7P.a,new T2(1,_7U,_4)));}),_=wMV(_7N,new T1(1,_7T));return _7q;}};return new T1(0,_7M);};return new F(function(){return A2(_6g,_7I,_7K);});},_7Y=function(_7Z,_80,_81,_82,_83,_84){var _85=B(_2x(_7Z)),_86=new T(function(){return B(_6g(_7Z));}),_87=new T(function(){return B(_6i(_85));}),_88=B(_2z(_85)),_89=new T(function(){return B(_2B(_81));}),_8a=new T(function(){var _8b=function(_8c){var _8d=E(_84),_8e=E(_82),_8f=strEq(E(_i),_8e);if(!E(_8f)){var _8g=E(_8e);}else{var _8g=B(A2(_7m,_80,_6e));}var _8h=B(A2(_7F,_81,_6e)),_8i=E(_D);return function(_5G){return new F(function(){return _2o(_5V,_69,_6f,new T2(1,_8i,new T2(1,_8h,new T2(1,_8g,new T2(1,_8d,new T2(1,_8c,_4))))),_5G);});};},_8j=function(_8k,_8l){var _8m=E(_84),_8n=E(_82),_8o=strEq(E(_i),_8n);if(!E(_8o)){var _8p=E(_8n);}else{var _8p=B(A2(_7m,_80,_6e));}var _8q=B(A2(_7F,_81,_6e)),_8r=E(_8k);return function(_5G){return new F(function(){return _2o(_5V,_69,_6f,new T2(1,_8r,new T2(1,_8q,new T2(1,_8p,new T2(1,_8m,new T2(1,_8l,_4))))),_5G);});};},_8s=E(_83);switch(_8s._){case 0:return B(_8b(E(_7l)));break;case 1:return B(_8b(E(_7k)));break;case 2:return B(_8j(new T(function(){return B(A2(_2m,B(_2v(_80)),_8s.a));}),E(_7j)));break;default:return B(_8j(new T(function(){return B(A2(_2m,B(_2v(_80)),_8s.a));}),E(_7i)));}}),_8t=function(_8u){var _8v=new T(function(){return B(A1(_86,new T(function(){return B(_7H(_2l,_8u));})));}),_8w=new T(function(){var _8x=new T(function(){var _8y=function(_8z,_8A,_){var _8B=E(_8A);if(!_8B._){var _8C=E(_8z);if(!_8C._){return E(_7h);}else{return new F(function(){return _c(new T(function(){return B(A(_7r,[_2l,_8u,new T1(0,_8C.a),_2c]));}),_4,_);});}}else{var _8D=B(A3(_4L,_89,_8B.a,_));return new F(function(){return _c(new T(function(){return B(A(_7r,[_2l,_8u,new T1(1,_8D),_2c]));}),_4,_);});}};return B(A1(_8a,_8y));});return B(A1(_87,_8x));});return new F(function(){return A3(_6c,_88,_8w,_8v);});};return new F(function(){return A3(_1V,_88,new T(function(){return B(A2(_6i,_85,_7p));}),_8t);});},_8E="w8",_8F=function(_8G){return E(_8E);},_8H=function(_8I,_8J){var _8K=E(_8J);return new T2(0,_8K.a,_8K.b);},_8L=function(_8M,_8N){return E(_8N).c;},_8O=function(_8P){var _8Q=B(A1(_8P,_));return E(_8Q);},_8R=function(_8S,_8T,_8U,_8V){var _8W=function(_){var _8X=E(_8U),_8Y=_8X.d,_8Z=_8Y["byteLength"],_90=newByteArr(_8Z),_91=_90,_92=memcpy(_91,_8Y,_8Z>>>0),_93=function(_94,_){while(1){var _95=E(_94);if(!_95._){return _5;}else{var _96=E(_95.a),_97=E(_96.a),_98=_91["v"]["w8"][_97],_=_91["v"]["w8"][_97]=B(A2(_8T,_98,_96.b));_94=_95.b;continue;}}},_99=B(_93(_8V,_));return new T4(0,E(_8X.a),E(_8X.b),_8X.c,_91);};return new F(function(){return _8O(_8W);});},_9a=function(_9b){return E(E(_9b).f);},_9c=new T(function(){return B(unCStr("Negative range size"));}),_9d=new T(function(){return B(err(_9c));}),_9e=function(_9f,_9g,_9h,_9i,_9j){var _9k=E(_9i),_9l=function(_){var _9m=B(A2(_9a,_9f,_9k)),_9n=newByteArr(_9m),_9o=_9n;if(_9m>=0){var _9p=_9m-1|0,_9q=function(_){var _9r=function(_9s,_){while(1){var _9t=E(_9s);if(!_9t._){return _5;}else{var _9u=E(_9t.a),_9v=E(_9u.a),_9w=_9o["v"]["w8"][_9v],_=_9o["v"]["w8"][_9v]=B(A2(_9g,_9w,_9u.b));_9s=_9t.b;continue;}}},_9x=B(_9r(_9j,_));return new T4(0,E(_9k.a),E(_9k.b),_9m,_9o);};if(0<=_9p){var _9y=function(_9z,_){while(1){var _=_9o["v"]["w8"][_9z]=E(_9h);if(_9z!=_9p){var _9A=_9z+1|0;_9z=_9A;continue;}else{return _5;}}},_9B=B(_9y(0,_));return new F(function(){return _9q(_);});}else{return new F(function(){return _9q(_);});}}else{return E(_9d);}},_9C=E(_9l);return new F(function(){return _8O(_9C);});},_9D=function(_9E,_9F,_9G){var _9H=E(_9F),_9I=function(_){var _9J=B(A2(_9a,_9E,_9H)),_9K=newByteArr(_9J),_9L=_9K;if(_9J>=0){var _9M=_9J-1|0,_9N=function(_){var _9O=function(_9P,_){while(1){var _9Q=E(_9P);if(!_9Q._){return _5;}else{var _9R=E(_9Q.a),_=_9L["v"]["w8"][E(_9R.a)]=E(_9R.b);_9P=_9Q.b;continue;}}},_9S=B(_9O(_9G,_));return new T4(0,E(_9H.a),E(_9H.b),_9J,_9L);};if(0<=_9M){var _9T=function(_9U,_){while(1){var _=_9L["v"]["w8"][_9U]=0;if(_9U!=_9M){var _9V=_9U+1|0;_9U=_9V;continue;}else{return _5;}}},_9W=B(_9T(0,_));return new F(function(){return _9N(_);});}else{return new F(function(){return _9N(_);});}}else{return E(_9d);}},_9X=E(_9I);return new F(function(){return _8O(_9X);});},_9Y=function(_9Z,_a0,_a1){return E(_a0).d["v"]["w8"][E(_a1)];},_a2=function(_a3,_a4,_a5){var _a6=function(_){var _a7=E(_a4),_a8=_a7.d,_a9=_a8["byteLength"],_aa=newByteArr(_a9),_ab=_aa,_ac=memcpy(_ab,_a8,_a9>>>0),_ad=function(_ae,_){while(1){var _af=E(_ae);if(!_af._){return _5;}else{var _ag=E(_af.a),_=_ab["v"]["w8"][E(_ag.a)]=E(_ag.b);_ae=_af.b;continue;}}},_ah=B(_ad(_a5,_));return new T4(0,E(_a7.a),E(_a7.b),_a7.c,_ab);};return new F(function(){return _8O(_a6);});},_ai={_:0,a:_8H,b:_8L,c:_9D,d:_9Y,e:_a2,f:_8R,g:_9e},_aj=function(_ak,_al,_){var _am=E(_al);return new T2(0,_am.a,_am.b);},_an=function(_ao,_ap,_){return new F(function(){return _aj(_ao,_ap,_);});},_aq=function(_ar,_as,_){return E(_as).c;},_at=function(_ao,_ap,_){return new F(function(){return _aq(_ao,_ap,_);});},_au=new T(function(){return B(unCStr("Negative range size"));}),_av=new T(function(){return B(err(_au));}),_aw=function(_ax,_ay,_az,_aA,_){var _aB=B(A2(_9a,_ax,new T2(0,_ay,_az))),_aC=newByteArr(_aB);if(_aB>=0){var _aD=_aB-1|0,_aE=new T(function(){return new T4(0,E(_ay),E(_az),_aB,_aC);});if(0<=_aD){var _aF=function(_aG,_){while(1){var _=E(_aE).d["v"]["w8"][_aG]=E(_aA);if(_aG!=_aD){var _aH=_aG+1|0;_aG=_aH;continue;}else{return _5;}}},_aI=B(_aF(0,_));return _aE;}else{return _aE;}}else{return E(_av);}},_aJ=function(_aK,_aL,_aM,_){var _aN=E(_aL);return new F(function(){return _aw(_aK,_aN.a,_aN.b,_aM,_);});},_aO=function(_aP,_ao,_ap,_){return new F(function(){return _aJ(_aP,_ao,_ap,_);});},_aQ=function(_aR,_aS,_aT,_){var _aU=B(A2(_9a,_aR,new T2(0,_aS,_aT))),_aV=newByteArr(_aU);return new T(function(){return new T4(0,E(_aS),E(_aT),_aU,_aV);});},_aW=function(_aX,_aY,_){var _aZ=E(_aY);return new F(function(){return _aQ(_aX,_aZ.a,_aZ.b,_);});},_b0=function(_ao,_ap,_){return new F(function(){return _aW(_ao,_ap,_);});},_b1=function(_b2,_b3,_b4,_){return E(_b3).d["v"]["w8"][E(_b4)];},_b5=function(_aP,_ao,_ap,_){return new F(function(){return _b1(_aP,_ao,_ap,_);});},_b6=function(_b7,_b8,_b9,_ba,_){var _=E(_b8).d["v"]["w8"][E(_b9)]=E(_ba);return _5;},_bb=function(_bc,_aP,_ao,_ap,_){return new F(function(){return _b6(_bc,_aP,_ao,_ap,_);});},_bd=function(_be,_bf,_){var _bg=B(A1(_be,_)),_bh=B(A1(_bf,_));return _bg;},_bi=function(_bj,_bk,_){var _bl=B(A1(_bj,_)),_bm=B(A1(_bk,_));return new T(function(){return B(A1(_bl,_bm));});},_bn=function(_bo,_bp,_){var _bq=B(A1(_bp,_));return _bo;},_br=new T2(0,_24,_bn),_bs=function(_bt,_){return _bt;},_bu=function(_bv,_bw,_){var _bx=B(A1(_bv,_));return new F(function(){return A1(_bw,_);});},_by=new T5(0,_br,_bs,_bi,_bu,_bd),_bz=new T(function(){return E(_4c);}),_bA=function(_bB){return new T6(0,_4l,_4m,_4,_bB,_4l,_4l);},_bC=function(_bD,_){var _bE=new T(function(){return B(A2(_6L,_bz,new T(function(){return B(A1(_bA,_bD));})));});return new F(function(){return die(_bE);});},_bF=function(_bG,_){return new F(function(){return _bC(_bG,_);});},_bH=function(_bI){return new F(function(){return A1(_bF,_bI);});},_bJ=function(_bK,_bL,_){var _bM=B(A1(_bK,_));return new F(function(){return A2(_bL,_bM,_);});},_bN=new T5(0,_by,_bJ,_bu,_bs,_bH),_bO={_:0,a:_bN,b:_an,c:_at,d:_aO,e:_b0,f:_b0,g:_b5,h:_bb},_bP=new T3(0,_ai,_bO,_8F),_bQ="deltaZ",_bR="deltaY",_bS="deltaX",_bT=function(_bU,_bV){var _bW=jsShowI(_bU);return new F(function(){return _0(fromJSStr(_bW),_bV);});},_bX=41,_bY=40,_bZ=function(_c0,_c1,_c2){if(_c1>=0){return new F(function(){return _bT(_c1,_c2);});}else{if(_c0<=6){return new F(function(){return _bT(_c1,_c2);});}else{return new T2(1,_bY,new T(function(){var _c3=jsShowI(_c1);return B(_0(fromJSStr(_c3),new T2(1,_bX,_c2)));}));}}},_c4=new T(function(){return B(unCStr(")"));}),_c5=new T(function(){return B(_bZ(0,2,_c4));}),_c6=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_c5));}),_c7=function(_c8){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_bZ(0,_c8,_c6));}))));});},_c9=function(_ca,_){return new T(function(){var _cb=Number(E(_ca)),_cc=jsTrunc(_cb);if(_cc<0){return B(_c7(_cc));}else{if(_cc>2){return B(_c7(_cc));}else{return _cc;}}});},_cd=0,_ce=new T3(0,_cd,_cd,_cd),_cf="button",_cg=new T(function(){return eval("jsGetMouseCoords");}),_ch=function(_ci,_){var _cj=E(_ci);if(!_cj._){return _4;}else{var _ck=B(_ch(_cj.b,_));return new T2(1,new T(function(){var _cl=Number(E(_cj.a));return jsTrunc(_cl);}),_ck);}},_cm=function(_cn,_){var _co=__arr2lst(0,_cn);return new F(function(){return _ch(_co,_);});},_cp=function(_cq,_){return new F(function(){return _cm(E(_cq),_);});},_cr=function(_cs,_){return new T(function(){var _ct=Number(E(_cs));return jsTrunc(_ct);});},_cu=new T2(0,_cr,_cp),_cv=function(_cw,_){var _cx=E(_cw);if(!_cx._){return _4;}else{var _cy=B(_cv(_cx.b,_));return new T2(1,_cx.a,_cy);}},_cz=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_cA=new T6(0,_4l,_4m,_4,_cz,_4l,_4l),_cB=new T(function(){return B(_4d(_cA));}),_cC=function(_){return new F(function(){return die(_cB);});},_cD=function(_cE,_cF,_cG,_){var _cH=__arr2lst(0,_cG),_cI=B(_cv(_cH,_)),_cJ=E(_cI);if(!_cJ._){return new F(function(){return _cC(_);});}else{var _cK=E(_cJ.b);if(!_cK._){return new F(function(){return _cC(_);});}else{if(!E(_cK.b)._){var _cL=B(A3(_4L,_cE,_cJ.a,_)),_cM=B(A3(_4L,_cF,_cK.a,_));return new T2(0,_cL,_cM);}else{return new F(function(){return _cC(_);});}}}},_cN=function(_cO,_cP,_){if(E(_cO)==7){var _cQ=__app1(E(_cg),_cP),_cR=B(_cD(_cu,_cu,_cQ,_)),_cS=__get(_cP,E(_bS)),_cT=__get(_cP,E(_bR)),_cU=__get(_cP,E(_bQ));return new T(function(){return new T3(0,E(_cR),E(_4l),E(new T3(0,_cS,_cT,_cU)));});}else{var _cV=__app1(E(_cg),_cP),_cW=B(_cD(_cu,_cu,_cV,_)),_cX=__get(_cP,E(_cf)),_cY=__eq(_cX,E(_D));if(!E(_cY)){var _cZ=__isUndef(_cX);if(!E(_cZ)){var _d0=B(_c9(_cX,_));return new T(function(){return new T3(0,E(_cW),E(new T1(1,_d0)),E(_ce));});}else{return new T(function(){return new T3(0,E(_cW),E(_4l),E(_ce));});}}else{return new T(function(){return new T3(0,E(_cW),E(_4l),E(_ce));});}}},_d1=function(_d2,_d3,_){return new F(function(){return _cN(_d2,E(_d3),_);});},_d4="mouseout",_d5="mouseover",_d6="mousemove",_d7="mouseup",_d8="mousedown",_d9="dblclick",_da="click",_db="wheel",_dc=function(_dd){switch(E(_dd)){case 0:return E(_da);case 1:return E(_d9);case 2:return E(_d8);case 3:return E(_d7);case 4:return E(_d6);case 5:return E(_d5);case 6:return E(_d4);default:return E(_db);}},_de=new T2(0,_dc,_d1),_df=function(_dg){return E(_dg);},_dh=new T2(0,_bN,_2j),_di=new T2(0,_dh,_bs),_dj=new T(function(){return B(unCStr("NoMethodError"));}),_dk=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_6k,_6l,_dj),_dl=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_dk,_4,_4),_dm=function(_dn){return E(_dl);},_do=function(_dp){var _dq=E(_dp);return new F(function(){return _2M(B(_2K(_dq.a)),_dm,_dq.b);});},_dr=function(_ds){return E(E(_ds).a);},_dt=function(_6x){return new T2(0,_du,_6x);},_dv=function(_dw,_dx){return new F(function(){return _0(E(_dw).a,_dx);});},_dy=function(_dz,_dA){return new F(function(){return _3X(_dv,_dz,_dA);});},_dB=function(_dC,_dD,_dE){return new F(function(){return _0(E(_dD).a,_dE);});},_dF=new T3(0,_dB,_dr,_dy),_du=new T(function(){return new T5(0,_dm,_dF,_dt,_do,_dr);}),_dG=new T(function(){return B(unCStr("No instance nor default method for class operation"));}),_dH=function(_dI){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_dI,_dG));})),_du);});},_dJ=new T(function(){return B(_dH("Data/Binary/Put.hs:17:10-19|>>="));}),_dK=function(_dL){return E(_dJ);},_dM=new T(function(){return B(unCStr(")"));}),_dN=function(_dO,_dP){var _dQ=new T(function(){var _dR=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_dP,_4)),_dM));})));},1);return B(_0(B(_bZ(0,_dO,_4)),_dR));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_dQ)));});},_dS=function(_dT){return new F(function(){return _bZ(0,E(_dT),_4);});},_dU=function(_dV,_dW,_dX){return new F(function(){return _bZ(E(_dV),E(_dW),_dX);});},_dY=function(_dZ,_e0){return new F(function(){return _bZ(0,E(_dZ),_e0);});},_e1=function(_e2,_e3){return new F(function(){return _3X(_dY,_e2,_e3);});},_e4=new T3(0,_dU,_dS,_e1),_e5=0,_e6=function(_e7,_e8,_e9){return new F(function(){return A1(_e7,new T2(1,_3U,new T(function(){return B(A1(_e8,_e9));})));});},_ea=new T(function(){return B(unCStr(": empty list"));}),_eb=new T(function(){return B(unCStr("Prelude."));}),_ec=function(_ed){return new F(function(){return err(B(_0(_eb,new T(function(){return B(_0(_ed,_ea));},1))));});},_ee=new T(function(){return B(unCStr("foldr1"));}),_ef=new T(function(){return B(_ec(_ee));}),_eg=function(_eh,_ei){var _ej=E(_ei);if(!_ej._){return E(_ef);}else{var _ek=_ej.a,_el=E(_ej.b);if(!_el._){return E(_ek);}else{return new F(function(){return A2(_eh,_ek,new T(function(){return B(_eg(_eh,_el));}));});}}},_em=new T(function(){return B(unCStr(" out of range "));}),_en=new T(function(){return B(unCStr("}.index: Index "));}),_eo=new T(function(){return B(unCStr("Ix{"));}),_ep=new T2(1,_bX,_4),_eq=new T2(1,_bX,_ep),_er=0,_es=function(_et){return E(E(_et).a);},_eu=function(_ev,_ew,_ex,_ey,_ez){var _eA=new T(function(){var _eB=new T(function(){var _eC=new T(function(){var _eD=new T(function(){var _eE=new T(function(){return B(A3(_eg,_e6,new T2(1,new T(function(){return B(A3(_es,_ex,_er,_ey));}),new T2(1,new T(function(){return B(A3(_es,_ex,_er,_ez));}),_4)),_eq));});return B(_0(_em,new T2(1,_bY,new T2(1,_bY,_eE))));});return B(A(_es,[_ex,_e5,_ew,new T2(1,_bX,_eD)]));});return B(_0(_en,new T2(1,_bY,_eC)));},1);return B(_0(_ev,_eB));},1);return new F(function(){return err(B(_0(_eo,_eA)));});},_eF=function(_eG,_eH,_eI,_eJ,_eK){return new F(function(){return _eu(_eG,_eH,_eK,_eI,_eJ);});},_eL=function(_eM,_eN,_eO,_eP){var _eQ=E(_eO);return new F(function(){return _eF(_eM,_eN,_eQ.a,_eQ.b,_eP);});},_eR=function(_eS,_eT,_eU,_eV){return new F(function(){return _eL(_eV,_eU,_eT,_eS);});},_eW=new T(function(){return B(unCStr("Int"));}),_eX=function(_eY,_eZ,_f0){return new F(function(){return _eR(_e4,new T2(0,_eZ,_f0),_eY,_eW);});},_f1=function(_f2,_f3,_f4,_f5,_f6,_f7){var _f8=_f2+_f7|0;if(_f3>_f8){return new F(function(){return _eX(_f8,_f3,_f4);});}else{if(_f8>_f4){return new F(function(){return _eX(_f8,_f3,_f4);});}else{var _f9=_f8-_f3|0;if(0>_f9){return new F(function(){return _dN(_f9,_f5);});}else{if(_f9>=_f5){return new F(function(){return _dN(_f9,_f5);});}else{return _f6["v"]["w8"][_f9];}}}}},_fa=function(_fb){return new F(function(){return err(B(unAppCStr("getWord8: no bytes left at ",new T(function(){return B(_bZ(0,_fb,_4));}))));});},_fc=function(_fd,_fe,_ff,_fg){if(_fg>=_fe){return new F(function(){return _fa(_fg);});}else{return new T2(0,new T(function(){var _fh=E(_ff);return B(_f1(_fd,E(_fh.a),E(_fh.b),_fh.c,_fh.d,_fg));}),_fg+1|0);}},_fi=function(_fj,_fk,_fl,_fm){var _fn=B(_fc(_fj,_fk,_fl,_fm)),_fo=_fn.b,_fp=E(_fn.a);if(_fp>127){var _fq=B(_fi(_fj,_fk,_fl,E(_fo)));return new T2(0,new T(function(){return (E(_fq.a)<<7>>>0|(_fp&127)>>>0)>>>0;}),_fq.b);}else{return new T2(0,_fp,_fo);}},_fr=new T(function(){return B(unCStr("too few bytes"));}),_fs=new T(function(){return B(err(_fr));}),_ft=function(_fu,_fv,_fw,_fx){var _fy=B(_fi(_fu,_fv,_fw,_fx)),_fz=E(_fy.b),_fA=E(_fy.a)&4294967295;return ((_fz+_fA|0)<=_fv)?new T2(0,new T(function(){var _fB=_fv-_fz|0;if(_fA>_fB){return new T3(0,_fu+_fz|0,_fB,_fw);}else{return new T3(0,_fu+_fz|0,_fA,_fw);}}),_fz+_fA|0):E(_fs);},_fC=function(_fD,_fE){var _fF=E(_fD),_fG=B(_ft(_fF.a,_fF.b,_fF.c,E(_fE)));return new T2(0,_fG.a,_fG.b);},_fH=new T2(0,_dK,_fC),_fI=function(_fJ){return E(_dJ);},_fK=function(_fL){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_bZ(9,_fL,_4));}))));});},_fM=function(_fN,_fO,_fP,_fQ){var _fR=B(_fc(_fN,_fO,_fP,_fQ)),_fS=_fR.b,_fT=E(_fR.a)&4294967295;if(_fT>=128){if(_fT>=224){if(_fT>=240){var _fU=B(_fc(_fN,_fO,_fP,E(_fS))),_fV=B(_fc(_fN,_fO,_fP,E(_fU.b))),_fW=B(_fc(_fN,_fO,_fP,E(_fV.b))),_fX=128^E(_fW.a)&4294967295|(128^E(_fV.a)&4294967295|(128^E(_fU.a)&4294967295|(240^_fT)<<6)<<6)<<6;if(_fX>>>0>1114111){return new F(function(){return _fK(_fX);});}else{return new T2(0,_fX,_fW.b);}}else{var _fY=B(_fc(_fN,_fO,_fP,E(_fS))),_fZ=B(_fc(_fN,_fO,_fP,E(_fY.b))),_g0=128^E(_fZ.a)&4294967295|(128^E(_fY.a)&4294967295|(224^_fT)<<6)<<6;if(_g0>>>0>1114111){return new F(function(){return _fK(_g0);});}else{return new T2(0,_g0,_fZ.b);}}}else{var _g1=B(_fc(_fN,_fO,_fP,E(_fS))),_g2=128^E(_g1.a)&4294967295|(192^_fT)<<6;if(_g2>>>0>1114111){return new F(function(){return _fK(_g2);});}else{return new T2(0,_g2,_g1.b);}}}else{if(_fT>>>0>1114111){return new F(function(){return _fK(_fT);});}else{return new T2(0,_fT,_fS);}}},_g3=function(_g4,_g5){var _g6=E(_g4),_g7=B(_fM(_g6.a,_g6.b,_g6.c,E(_g5)));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga,_gb){var _gc=E(_g9);if(!_gc._){return new T2(0,_4,_gb);}else{var _gd=new T(function(){return B(A2(_gc.a,_ga,_gb));}),_ge=B(_g8(_gc.b,_ga,new T(function(){return E(E(_gd).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_gd).a);}),_ge.a),_ge.b);}},_gf=function(_gg,_gh,_gi,_gj){if(0>=_gg){return new F(function(){return _g8(_4,_gi,_gj);});}else{var _gk=function(_gl){var _gm=E(_gl);return (_gm==1)?E(new T2(1,_gh,_4)):new T2(1,_gh,new T(function(){return B(_gk(_gm-1|0));}));};return new F(function(){return _g8(B(_gk(_gg)),_gi,_gj);});}},_gn=function(_go,_gp,_gq,_gr){var _gs=B(_fi(_go,_gp,_gq,_gr));return new F(function(){return _gf(E(_gs.a)&4294967295,_g3,new T3(0,_go,_gp,_gq),_gs.b);});},_gt=function(_gu,_gv){var _gw=E(_gu),_gx=B(_gn(_gw.a,_gw.b,_gw.c,E(_gv)));return new T2(0,_gx.a,_gx.b);},_gy=new T2(0,_fI,_gt),_gz=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_gA=new T(function(){return B(err(_gz));}),_gB=function(_gC,_gD,_gE){var _gF=function(_){var _gG=E(_gD),_gH=_gG.c,_gI=newArr(_gH,_gA),_gJ=_gI,_gK=function(_gL,_){while(1){if(_gL!=_gH){var _=_gJ[_gL]=_gG.d[_gL],_gM=_gL+1|0;_gL=_gM;continue;}else{return E(_);}}},_=B(_gK(0,_)),_gN=function(_gO,_){while(1){var _gP=E(_gO);if(!_gP._){return new T4(0,E(_gG.a),E(_gG.b),_gH,_gJ);}else{var _gQ=E(_gP.a),_=_gJ[E(_gQ.a)]=_gQ.b;_gO=_gP.b;continue;}}};return new F(function(){return _gN(_gE,_);});};return new F(function(){return _8O(_gF);});},_gR=function(_gS,_gT,_gU){return new F(function(){return _gB(_gS,_gT,_gU);});},_gV=function(_gW,_gX,_gY){return E(E(_gX).d[E(_gY)]);},_gZ=function(_h0,_h1,_h2){return new F(function(){return _gV(_h0,_h1,_h2);});},_h3=function(_h4,_h5,_h6){var _h7=E(_h5),_h8=B(A2(_9a,_h4,_h7)),_h9=function(_){var _ha=newArr(_h8,_gA),_hb=_ha,_hc=function(_hd,_){while(1){var _he=B((function(_hf,_){var _hg=E(_hf);if(!_hg._){return new T(function(){return new T4(0,E(_h7.a),E(_h7.b),_h8,_hb);});}else{var _hh=E(_hg.a),_=_hb[E(_hh.a)]=_hh.b;_hd=_hg.b;return __continue;}})(_hd,_));if(_he!=__continue){return _he;}}};return new F(function(){return _hc(_h6,_);});};return new F(function(){return _8O(_h9);});},_hi=function(_hj,_hk,_hl){return new F(function(){return _h3(_hj,_hk,_hl);});},_hm=function(_hn,_ho){return E(_ho).c;},_hp=function(_hq,_hr){return new F(function(){return _hm(_hq,_hr);});},_hs=function(_ht,_hu){var _hv=E(_hu);return new T2(0,_hv.a,_hv.b);},_hw=function(_hx,_hy){return new F(function(){return _hs(_hx,_hy);});},_hz=function(_hA,_hB,_hC,_hD){var _hE=function(_){var _hF=E(_hC),_hG=_hF.c,_hH=newArr(_hG,_gA),_hI=_hH,_hJ=function(_hK,_){while(1){if(_hK!=_hG){var _=_hI[_hK]=_hF.d[_hK],_hL=_hK+1|0;_hK=_hL;continue;}else{return E(_);}}},_=B(_hJ(0,_)),_hM=function(_hN,_){while(1){var _hO=B((function(_hP,_){var _hQ=E(_hP);if(!_hQ._){return new T4(0,E(_hF.a),E(_hF.b),_hG,_hI);}else{var _hR=E(_hQ.a),_hS=E(_hR.a),_hT=_hI[_hS],_=_hI[_hS]=new T(function(){return B(A2(_hB,_hT,_hR.b));});_hN=_hQ.b;return __continue;}})(_hN,_));if(_hO!=__continue){return _hO;}}};return new F(function(){return _hM(_hD,_);});};return new F(function(){return _8O(_hE);});},_hU=function(_hV,_hW,_hX,_hY,_hZ){var _i0=E(_hY),_i1=B(A2(_9a,_hV,_i0)),_i2=function(_){var _i3=newArr(_i1,_hX),_i4=_i3,_i5=function(_i6,_){while(1){var _i7=B((function(_i8,_){var _i9=E(_i8);if(!_i9._){return new T(function(){return new T4(0,E(_i0.a),E(_i0.b),_i1,_i4);});}else{var _ia=E(_i9.a),_ib=E(_ia.a),_ic=_i4[_ib],_=_i4[_ib]=new T(function(){return B(A2(_hW,_ic,_ia.b));});_i6=_i9.b;return __continue;}})(_i6,_));if(_i7!=__continue){return _i7;}}};return new F(function(){return _i5(_hZ,_);});};return new F(function(){return _8O(_i2);});},_id={_:0,a:_hw,b:_hp,c:_hi,d:_gZ,e:_gR,f:_hz,g:_hU},_ie=new T(function(){return B(unCStr("Negative range size"));}),_if=new T(function(){return B(err(_ie));}),_ig=0,_ih=function(_ii){var _ij=E(_ii);return (E(_ij.b)-E(_ij.a)|0)+1|0;},_ik=function(_il,_im){var _in=E(_il),_io=E(_im);return (E(_in.a)>_io)?false:_io<=E(_in.b);},_ip=new T(function(){return B(unCStr("Int"));}),_iq=function(_ir,_is){return new F(function(){return _eR(_e4,_is,_ir,_ip);});},_it=function(_iu,_iv){var _iw=E(_iu),_ix=E(_iw.a),_iy=E(_iv);if(_ix>_iy){return new F(function(){return _iq(_iy,_iw);});}else{if(_iy>E(_iw.b)){return new F(function(){return _iq(_iy,_iw);});}else{return _iy-_ix|0;}}},_iz=function(_iA,_iB){if(_iA<=_iB){var _iC=function(_iD){return new T2(1,_iD,new T(function(){if(_iD!=_iB){return B(_iC(_iD+1|0));}else{return __Z;}}));};return new F(function(){return _iC(_iA);});}else{return __Z;}},_iE=function(_iF,_iG){return new F(function(){return _iz(E(_iF),E(_iG));});},_iH=function(_iI){var _iJ=E(_iI);return new F(function(){return _iE(_iJ.a,_iJ.b);});},_iK=function(_iL){var _iM=E(_iL),_iN=E(_iM.a),_iO=E(_iM.b);return (_iN>_iO)?E(_e5):(_iO-_iN|0)+1|0;},_iP=function(_iQ,_iR){return E(_iQ)-E(_iR)|0;},_iS=function(_iT,_iU){return new F(function(){return _iP(_iU,E(_iT).a);});},_iV=function(_iW,_iX){return E(_iW)==E(_iX);},_iY=function(_iZ,_j0){return E(_iZ)!=E(_j0);},_j1=new T2(0,_iV,_iY),_j2=function(_j3,_j4){var _j5=E(_j3),_j6=E(_j4);return (_j5>_j6)?E(_j5):E(_j6);},_j7=function(_j8,_j9){var _ja=E(_j8),_jb=E(_j9);return (_ja>_jb)?E(_jb):E(_ja);},_jc=function(_jd,_je){return (_jd>=_je)?(_jd!=_je)?2:1:0;},_jf=function(_jg,_jh){return new F(function(){return _jc(E(_jg),E(_jh));});},_ji=function(_jj,_jk){return E(_jj)>=E(_jk);},_jl=function(_jm,_jn){return E(_jm)>E(_jn);},_jo=function(_jp,_jq){return E(_jp)<=E(_jq);},_jr=function(_js,_jt){return E(_js)<E(_jt);},_ju={_:0,a:_j1,b:_jf,c:_jr,d:_jo,e:_jl,f:_ji,g:_j2,h:_j7},_jv={_:0,a:_ju,b:_iH,c:_it,d:_iS,e:_ik,f:_iK,g:_ih},_jw=function(_jx,_jy,_jz){var _jA=E(_jx);if(!_jA._){return new T2(0,_4,_jz);}else{var _jB=new T(function(){return B(A2(_jA.a,_jy,_jz));}),_jC=B(_jw(_jA.b,_jy,new T(function(){return E(E(_jB).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_jB).a);}),_jC.a),_jC.b);}},_jD=function(_jE,_jF,_jG,_jH){if(0>=_jE){return new F(function(){return _jw(_4,_jG,_jH);});}else{var _jI=function(_jJ){var _jK=E(_jJ);return (_jK==1)?E(new T2(1,_jF,_4)):new T2(1,_jF,new T(function(){return B(_jI(_jK-1|0));}));};return new F(function(){return _jw(B(_jI(_jE)),_jG,_jH);});}},_jL=function(_jM){return E(E(_jM).b);},_jN=function(_jO){return E(E(_jO).c);},_jP=function(_jQ,_jR){var _jS=E(_jQ);if(!_jS._){return __Z;}else{var _jT=E(_jR);return (_jT._==0)?__Z:new T2(1,new T2(0,_jS.a,_jT.a),new T(function(){return B(_jP(_jS.b,_jT.b));}));}},_jU=function(_jV,_jW,_jX,_jY,_jZ,_k0){var _k1=B(_fi(_jX,_jY,_jZ,_k0)),_k2=E(_k1.a)&4294967295,_k3=B(_jD(_k2,new T(function(){return B(_jL(_jV));}),new T3(0,_jX,_jY,_jZ),_k1.b)),_k4=_k3.a,_k5=new T(function(){var _k6=_k2-1|0;return B(A(_jN,[_jW,_jv,new T2(0,_ig,_k6),new T(function(){if(0>_k6){return B(_jP(B(_iz(0,-1)),_k4));}else{var _k7=_k6+1|0;if(_k7>=0){return B(_jP(B(_iz(0,_k7-1|0)),_k4));}else{return E(_if);}}})]));});return new T2(0,_k5,_k3.b);},_k8=function(_k9,_ka,_kb,_kc){var _kd=B(_fi(_k9,_ka,_kb,_kc)),_ke=B(_fi(_k9,_ka,_kb,E(_kd.b))),_kf=B(_jU(_gy,_id,_k9,_ka,_kb,E(_ke.b)));return new T2(0,new T(function(){var _kg=E(_kf.a);return new T6(0,E(_kd.a)&4294967295,E(_ke.a)&4294967295,E(_kg.a),E(_kg.b),_kg.c,_kg.d);}),_kf.b);},_kh=function(_ki,_kj){var _kk=E(_ki),_kl=B(_k8(_kk.a,_kk.b,_kk.c,E(_kj)));return new T2(0,_kl.a,_kl.b);},_km=function(_kn){return E(_dJ);},_ko=new T2(0,_km,_kh),_kp=function(_kq,_kr){var _ks=E(_kq),_kt=B(_fi(_ks.a,_ks.b,_ks.c,E(_kr)));return new T2(0,new T(function(){return E(_kt.a)&4294967295;}),_kt.b);},_ku=new T(function(){return B(_dH("Data/Binary.hs:56:10-20|put"));}),_kv=function(_kw){return E(_ku);},_kx=new T2(0,_kv,_kp),_ky=function(_kz,_kA){var _kB=E(_kA);return new T2(0,_kB.a,_kB.b);},_kC=function(_kD,_kE){return E(_kE).c;},_kF=function(_kG,_kH,_kI,_kJ){var _kK=function(_){var _kL=E(_kI),_kM=_kL.d,_kN=_kM["byteLength"],_kO=newByteArr(_kN),_kP=_kO,_kQ=memcpy(_kP,_kM,_kN>>>0),_kR=function(_kS,_){while(1){var _kT=E(_kS);if(!_kT._){return _5;}else{var _kU=E(_kT.a),_kV=E(_kU.a),_kW=_kP["v"]["i32"][_kV],_=_kP["v"]["i32"][_kV]=B(A2(_kH,_kW,_kU.b));_kS=_kT.b;continue;}}},_kX=B(_kR(_kJ,_));return new T4(0,E(_kL.a),E(_kL.b),_kL.c,_kP);};return new F(function(){return _8O(_kK);});},_kY=function(_kZ,_l0,_l1,_l2,_l3){var _l4=E(_l2),_l5=function(_){var _l6=B(A2(_9a,_kZ,_l4)),_l7=newByteArr(imul(4,_l6)|0),_l8=_l7;if(_l6>=0){var _l9=_l6-1|0,_la=function(_){var _lb=function(_lc,_){while(1){var _ld=E(_lc);if(!_ld._){return _5;}else{var _le=E(_ld.a),_lf=E(_le.a),_lg=_l8["v"]["i32"][_lf],_=_l8["v"]["i32"][_lf]=B(A2(_l0,_lg,_le.b));_lc=_ld.b;continue;}}},_lh=B(_lb(_l3,_));return new T4(0,E(_l4.a),E(_l4.b),_l6,_l8);};if(0<=_l9){var _li=function(_lj,_){while(1){var _=_l8["v"]["i32"][_lj]=E(_l1);if(_lj!=_l9){var _lk=_lj+1|0;_lj=_lk;continue;}else{return _5;}}},_ll=B(_li(0,_));return new F(function(){return _la(_);});}else{return new F(function(){return _la(_);});}}else{return E(_9d);}},_lm=E(_l5);return new F(function(){return _8O(_lm);});},_ln=function(_lo,_lp,_lq){var _lr=E(_lp),_ls=function(_){var _lt=B(A2(_9a,_lo,_lr)),_lu=newByteArr(imul(4,_lt)|0),_lv=_lu;if(_lt>=0){var _lw=_lt-1|0,_lx=function(_){var _ly=function(_lz,_){while(1){var _lA=E(_lz);if(!_lA._){return _5;}else{var _lB=E(_lA.a),_=_lv["v"]["i32"][E(_lB.a)]=E(_lB.b);_lz=_lA.b;continue;}}},_lC=B(_ly(_lq,_));return new T4(0,E(_lr.a),E(_lr.b),_lt,_lv);};if(0<=_lw){var _lD=function(_lE,_){while(1){var _=_lv["v"]["i32"][_lE]=0;if(_lE!=_lw){var _lF=_lE+1|0;_lE=_lF;continue;}else{return _5;}}},_lG=B(_lD(0,_));return new F(function(){return _lx(_);});}else{return new F(function(){return _lx(_);});}}else{return E(_9d);}},_lH=E(_ls);return new F(function(){return _8O(_lH);});},_lI=function(_lJ,_lK,_lL){return E(_lK).d["v"]["i32"][E(_lL)];},_lM=function(_lN,_lO,_lP){var _lQ=function(_){var _lR=E(_lO),_lS=_lR.d,_lT=_lS["byteLength"],_lU=newByteArr(_lT),_lV=_lU,_lW=memcpy(_lV,_lS,_lT>>>0),_lX=function(_lY,_){while(1){var _lZ=E(_lY);if(!_lZ._){return _5;}else{var _m0=E(_lZ.a),_=_lV["v"]["i32"][E(_m0.a)]=E(_m0.b);_lY=_lZ.b;continue;}}},_m1=B(_lX(_lP,_));return new T4(0,E(_lR.a),E(_lR.b),_lR.c,_lV);};return new F(function(){return _8O(_lQ);});},_m2={_:0,a:_ky,b:_kC,c:_ln,d:_lI,e:_lM,f:_kF,g:_kY},_m3=function(_m4,_m5,_m6,_m7){var _m8=B(_ft(_m4,_m5,_m6,_m7)),_m9=B(_jU(_kx,_m2,_m4,_m5,_m6,E(_m8.b)));return new T2(0,new T(function(){var _ma=E(_m9.a);return new T5(0,_m8.a,E(_ma.a),E(_ma.b),_ma.c,_ma.d);}),_m9.b);},_mb=function(_mc,_md){var _me=E(_mc),_mf=B(_m3(_me.a,_me.b,_me.c,E(_md)));return new T2(0,_mf.a,_mf.b);},_mg=function(_mh){return E(_dJ);},_mi=new T2(0,_mg,_mb),_mj=function(_mk){return new F(function(){return _iz(E(_mk),2147483647);});},_ml=function(_mm,_mn,_mo){if(_mo<=_mn){var _mp=new T(function(){var _mq=_mn-_mm|0,_mr=function(_ms){return (_ms>=(_mo-_mq|0))?new T2(1,_ms,new T(function(){return B(_mr(_ms+_mq|0));})):new T2(1,_ms,_4);};return B(_mr(_mn));});return new T2(1,_mm,_mp);}else{return (_mo<=_mm)?new T2(1,_mm,_4):__Z;}},_mt=function(_mu,_mv,_mw){if(_mw>=_mv){var _mx=new T(function(){var _my=_mv-_mu|0,_mz=function(_mA){return (_mA<=(_mw-_my|0))?new T2(1,_mA,new T(function(){return B(_mz(_mA+_my|0));})):new T2(1,_mA,_4);};return B(_mz(_mv));});return new T2(1,_mu,_mx);}else{return (_mw>=_mu)?new T2(1,_mu,_4):__Z;}},_mB=function(_mC,_mD){if(_mD<_mC){return new F(function(){return _ml(_mC,_mD,-2147483648);});}else{return new F(function(){return _mt(_mC,_mD,2147483647);});}},_mE=function(_mF,_mG){return new F(function(){return _mB(E(_mF),E(_mG));});},_mH=function(_mI,_mJ,_mK){if(_mJ<_mI){return new F(function(){return _ml(_mI,_mJ,_mK);});}else{return new F(function(){return _mt(_mI,_mJ,_mK);});}},_mL=function(_mM,_mN,_mO){return new F(function(){return _mH(E(_mM),E(_mN),E(_mO));});},_mP=function(_mQ){return E(_mQ);},_mR=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_mS=new T(function(){return B(err(_mR));}),_mT=function(_mU){var _mV=E(_mU);return (_mV==(-2147483648))?E(_mS):_mV-1|0;},_mW=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_mX=new T(function(){return B(err(_mW));}),_mY=function(_mZ){var _n0=E(_mZ);return (_n0==2147483647)?E(_mX):_n0+1|0;},_n1={_:0,a:_mY,b:_mT,c:_mP,d:_mP,e:_mj,f:_mE,g:_iE,h:_mL},_n2=function(_n3,_n4){if(_n3<=0){if(_n3>=0){return new F(function(){return quot(_n3,_n4);});}else{if(_n4<=0){return new F(function(){return quot(_n3,_n4);});}else{return quot(_n3+1|0,_n4)-1|0;}}}else{if(_n4>=0){if(_n3>=0){return new F(function(){return quot(_n3,_n4);});}else{if(_n4<=0){return new F(function(){return quot(_n3,_n4);});}else{return quot(_n3+1|0,_n4)-1|0;}}}else{return quot(_n3-1|0,_n4)-1|0;}}},_n5=new T(function(){return B(unCStr("base"));}),_n6=new T(function(){return B(unCStr("GHC.Exception"));}),_n7=new T(function(){return B(unCStr("ArithException"));}),_n8=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_n5,_n6,_n7),_n9=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_n8,_4,_4),_na=function(_nb){return E(_n9);},_nc=function(_nd){var _ne=E(_nd);return new F(function(){return _2M(B(_2K(_ne.a)),_na,_ne.b);});},_nf=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_ng=new T(function(){return B(unCStr("denormal"));}),_nh=new T(function(){return B(unCStr("divide by zero"));}),_ni=new T(function(){return B(unCStr("loss of precision"));}),_nj=new T(function(){return B(unCStr("arithmetic underflow"));}),_nk=new T(function(){return B(unCStr("arithmetic overflow"));}),_nl=function(_nm,_nn){switch(E(_nm)){case 0:return new F(function(){return _0(_nk,_nn);});break;case 1:return new F(function(){return _0(_nj,_nn);});break;case 2:return new F(function(){return _0(_ni,_nn);});break;case 3:return new F(function(){return _0(_nh,_nn);});break;case 4:return new F(function(){return _0(_ng,_nn);});break;default:return new F(function(){return _0(_nf,_nn);});}},_no=function(_np){return new F(function(){return _nl(_np,_4);});},_nq=function(_nr,_ns,_nt){return new F(function(){return _nl(_ns,_nt);});},_nu=function(_nv,_nw){return new F(function(){return _3X(_nl,_nv,_nw);});},_nx=new T3(0,_nq,_no,_nu),_ny=new T(function(){return new T5(0,_na,_nx,_nz,_nc,_no);}),_nz=function(_6S){return new T2(0,_ny,_6S);},_nA=3,_nB=new T(function(){return B(_nz(_nA));}),_nC=new T(function(){return die(_nB);}),_nD=0,_nE=new T(function(){return B(_nz(_nD));}),_nF=new T(function(){return die(_nE);}),_nG=function(_nH,_nI){var _nJ=E(_nI);switch(_nJ){case -1:var _nK=E(_nH);if(_nK==(-2147483648)){return E(_nF);}else{return new F(function(){return _n2(_nK,-1);});}break;case 0:return E(_nC);default:return new F(function(){return _n2(_nH,_nJ);});}},_nL=function(_nM,_nN){return new F(function(){return _nG(E(_nM),E(_nN));});},_nO=0,_nP=new T2(0,_nF,_nO),_nQ=function(_nR,_nS){var _nT=E(_nR),_nU=E(_nS);switch(_nU){case -1:var _nV=E(_nT);if(_nV==(-2147483648)){return E(_nP);}else{if(_nV<=0){if(_nV>=0){var _nW=quotRemI(_nV,-1);return new T2(0,_nW.a,_nW.b);}else{var _nX=quotRemI(_nV,-1);return new T2(0,_nX.a,_nX.b);}}else{var _nY=quotRemI(_nV-1|0,-1);return new T2(0,_nY.a-1|0,(_nY.b+(-1)|0)+1|0);}}break;case 0:return E(_nC);default:if(_nT<=0){if(_nT>=0){var _nZ=quotRemI(_nT,_nU);return new T2(0,_nZ.a,_nZ.b);}else{if(_nU<=0){var _o0=quotRemI(_nT,_nU);return new T2(0,_o0.a,_o0.b);}else{var _o1=quotRemI(_nT+1|0,_nU);return new T2(0,_o1.a-1|0,(_o1.b+_nU|0)-1|0);}}}else{if(_nU>=0){if(_nT>=0){var _o2=quotRemI(_nT,_nU);return new T2(0,_o2.a,_o2.b);}else{if(_nU<=0){var _o3=quotRemI(_nT,_nU);return new T2(0,_o3.a,_o3.b);}else{var _o4=quotRemI(_nT+1|0,_nU);return new T2(0,_o4.a-1|0,(_o4.b+_nU|0)-1|0);}}}else{var _o5=quotRemI(_nT-1|0,_nU);return new T2(0,_o5.a-1|0,(_o5.b+_nU|0)+1|0);}}}},_o6=function(_o7,_o8){var _o9=_o7%_o8;if(_o7<=0){if(_o7>=0){return E(_o9);}else{if(_o8<=0){return E(_o9);}else{var _oa=E(_o9);return (_oa==0)?0:_oa+_o8|0;}}}else{if(_o8>=0){if(_o7>=0){return E(_o9);}else{if(_o8<=0){return E(_o9);}else{var _ob=E(_o9);return (_ob==0)?0:_ob+_o8|0;}}}else{var _oc=E(_o9);return (_oc==0)?0:_oc+_o8|0;}}},_od=function(_oe,_of){var _og=E(_of);switch(_og){case -1:return E(_nO);case 0:return E(_nC);default:return new F(function(){return _o6(E(_oe),_og);});}},_oh=function(_oi,_oj){var _ok=E(_oi),_ol=E(_oj);switch(_ol){case -1:var _om=E(_ok);if(_om==(-2147483648)){return E(_nF);}else{return new F(function(){return quot(_om,-1);});}break;case 0:return E(_nC);default:return new F(function(){return quot(_ok,_ol);});}},_on=function(_oo,_op){var _oq=E(_oo),_or=E(_op);switch(_or){case -1:var _os=E(_oq);if(_os==(-2147483648)){return E(_nP);}else{var _ot=quotRemI(_os,-1);return new T2(0,_ot.a,_ot.b);}break;case 0:return E(_nC);default:var _ou=quotRemI(_oq,_or);return new T2(0,_ou.a,_ou.b);}},_ov=function(_ow,_ox){var _oy=E(_ox);switch(_oy){case -1:return E(_nO);case 0:return E(_nC);default:return E(_ow)%_oy;}},_oz=function(_oA){return new T1(0,_oA);},_oB=function(_oC){return new F(function(){return _oz(E(_oC));});},_oD=new T1(0,1),_oE=function(_oF){return new T2(0,E(B(_oz(E(_oF)))),E(_oD));},_oG=function(_oH,_oI){return imul(E(_oH),E(_oI))|0;},_oJ=function(_oK,_oL){return E(_oK)+E(_oL)|0;},_oM=function(_oN){var _oO=E(_oN);return (_oO<0)? -_oO:E(_oO);},_oP=function(_oQ){var _oR=E(_oQ);if(!_oR._){return E(_oR.a);}else{return new F(function(){return I_toInt(_oR.a);});}},_oS=function(_oT){return new F(function(){return _oP(_oT);});},_oU=function(_oV){return  -E(_oV);},_oW=-1,_oX=0,_oY=1,_oZ=function(_p0){var _p1=E(_p0);return (_p1>=0)?(E(_p1)==0)?E(_oX):E(_oY):E(_oW);},_p2={_:0,a:_oJ,b:_iP,c:_oG,d:_oU,e:_oM,f:_oZ,g:_oS},_p3=new T2(0,_iV,_iY),_p4={_:0,a:_p3,b:_jf,c:_jr,d:_jo,e:_jl,f:_ji,g:_j2,h:_j7},_p5=new T3(0,_p2,_p4,_oE),_p6={_:0,a:_p5,b:_n1,c:_oh,d:_ov,e:_nL,f:_od,g:_on,h:_nQ,i:_oB},_p7={_:0,a:_mY,b:_mT,c:_mP,d:_mP,e:_mj,f:_mE,g:_iE,h:_mL},_p8={_:0,a:_oJ,b:_iP,c:_oG,d:_oU,e:_oM,f:_oZ,g:_oS},_p9=new T3(0,_p8,_ju,_oE),_pa={_:0,a:_p9,b:_p7,c:_oh,d:_ov,e:_nL,f:_od,g:_on,h:_nQ,i:_oB},_pb=new T1(0,2),_pc=function(_pd){return E(E(_pd).a);},_pe=function(_pf){return E(E(_pf).a);},_pg=function(_ph,_pi){while(1){var _pj=E(_ph);if(!_pj._){var _pk=_pj.a,_pl=E(_pi);if(!_pl._){var _pm=_pl.a;if(!(imul(_pk,_pm)|0)){return new T1(0,imul(_pk,_pm)|0);}else{_ph=new T1(1,I_fromInt(_pk));_pi=new T1(1,I_fromInt(_pm));continue;}}else{_ph=new T1(1,I_fromInt(_pk));_pi=_pl;continue;}}else{var _pn=E(_pi);if(!_pn._){_ph=_pj;_pi=new T1(1,I_fromInt(_pn.a));continue;}else{return new T1(1,I_mul(_pj.a,_pn.a));}}}},_po=function(_pp,_pq,_pr){while(1){if(!(_pq%2)){var _ps=B(_pg(_pp,_pp)),_pt=quot(_pq,2);_pp=_ps;_pq=_pt;continue;}else{var _pu=E(_pq);if(_pu==1){return new F(function(){return _pg(_pp,_pr);});}else{var _ps=B(_pg(_pp,_pp)),_pv=B(_pg(_pp,_pr));_pp=_ps;_pq=quot(_pu-1|0,2);_pr=_pv;continue;}}}},_pw=function(_px,_py){while(1){if(!(_py%2)){var _pz=B(_pg(_px,_px)),_pA=quot(_py,2);_px=_pz;_py=_pA;continue;}else{var _pB=E(_py);if(_pB==1){return E(_px);}else{return new F(function(){return _po(B(_pg(_px,_px)),quot(_pB-1|0,2),_px);});}}}},_pC=function(_pD){return E(E(_pD).c);},_pE=function(_pF){return E(E(_pF).a);},_pG=function(_pH){return E(E(_pH).b);},_pI=function(_pJ){return E(E(_pJ).b);},_pK=function(_pL){return E(E(_pL).c);},_pM=function(_pN){return E(E(_pN).a);},_pO=new T1(0,0),_pP=new T1(0,2),_pQ=function(_pR){return E(E(_pR).g);},_pS=function(_pT){return E(E(_pT).d);},_pU=function(_pV,_pW){var _pX=B(_pc(_pV)),_pY=new T(function(){return B(_pe(_pX));}),_pZ=new T(function(){return B(A3(_pS,_pV,_pW,new T(function(){return B(A2(_pQ,_pY,_pP));})));});return new F(function(){return A3(_pM,B(_pE(B(_pG(_pX)))),_pZ,new T(function(){return B(A2(_pQ,_pY,_pO));}));});},_q0=new T(function(){return B(unCStr("Negative exponent"));}),_q1=new T(function(){return B(err(_q0));}),_q2=function(_q3){return E(E(_q3).c);},_q4=function(_q5,_q6,_q7,_q8){var _q9=B(_pc(_q6)),_qa=new T(function(){return B(_pe(_q9));}),_qb=B(_pG(_q9));if(!B(A3(_pK,_qb,_q8,new T(function(){return B(A2(_pQ,_qa,_pO));})))){if(!B(A3(_pM,B(_pE(_qb)),_q8,new T(function(){return B(A2(_pQ,_qa,_pO));})))){var _qc=new T(function(){return B(A2(_pQ,_qa,_pP));}),_qd=new T(function(){return B(A2(_pQ,_qa,_oD));}),_qe=B(_pE(_qb)),_qf=function(_qg,_qh,_qi){while(1){var _qj=B((function(_qk,_ql,_qm){if(!B(_pU(_q6,_ql))){if(!B(A3(_pM,_qe,_ql,_qd))){var _qn=new T(function(){return B(A3(_q2,_q6,new T(function(){return B(A3(_pI,_qa,_ql,_qd));}),_qc));});_qg=new T(function(){return B(A3(_pC,_q5,_qk,_qk));});_qh=_qn;_qi=new T(function(){return B(A3(_pC,_q5,_qk,_qm));});return __continue;}else{return new F(function(){return A3(_pC,_q5,_qk,_qm);});}}else{var _qo=_qm;_qg=new T(function(){return B(A3(_pC,_q5,_qk,_qk));});_qh=new T(function(){return B(A3(_q2,_q6,_ql,_qc));});_qi=_qo;return __continue;}})(_qg,_qh,_qi));if(_qj!=__continue){return _qj;}}},_qp=function(_qq,_qr){while(1){var _qs=B((function(_qt,_qu){if(!B(_pU(_q6,_qu))){if(!B(A3(_pM,_qe,_qu,_qd))){var _qv=new T(function(){return B(A3(_q2,_q6,new T(function(){return B(A3(_pI,_qa,_qu,_qd));}),_qc));});return new F(function(){return _qf(new T(function(){return B(A3(_pC,_q5,_qt,_qt));}),_qv,_qt);});}else{return E(_qt);}}else{_qq=new T(function(){return B(A3(_pC,_q5,_qt,_qt));});_qr=new T(function(){return B(A3(_q2,_q6,_qu,_qc));});return __continue;}})(_qq,_qr));if(_qs!=__continue){return _qs;}}};return new F(function(){return _qp(_q7,_q8);});}else{return new F(function(){return A2(_pQ,_q5,_oD);});}}else{return E(_q1);}},_qw=new T(function(){return B(err(_q0));}),_qx=function(_qy){var _qz=I_decodeDouble(_qy);return new T2(0,new T1(1,_qz.b),_qz.a);},_qA=function(_qB,_qC){var _qD=E(_qB);return (_qD._==0)?_qD.a*Math.pow(2,_qC):I_toNumber(_qD.a)*Math.pow(2,_qC);},_qE=function(_qF,_qG){var _qH=E(_qF);if(!_qH._){var _qI=_qH.a,_qJ=E(_qG);return (_qJ._==0)?_qI==_qJ.a:(I_compareInt(_qJ.a,_qI)==0)?true:false;}else{var _qK=_qH.a,_qL=E(_qG);return (_qL._==0)?(I_compareInt(_qK,_qL.a)==0)?true:false:(I_compare(_qK,_qL.a)==0)?true:false;}},_qM=function(_qN,_qO){while(1){var _qP=E(_qN);if(!_qP._){var _qQ=E(_qP.a);if(_qQ==(-2147483648)){_qN=new T1(1,I_fromInt(-2147483648));continue;}else{var _qR=E(_qO);if(!_qR._){var _qS=_qR.a;return new T2(0,new T1(0,quot(_qQ,_qS)),new T1(0,_qQ%_qS));}else{_qN=new T1(1,I_fromInt(_qQ));_qO=_qR;continue;}}}else{var _qT=E(_qO);if(!_qT._){_qN=_qP;_qO=new T1(1,I_fromInt(_qT.a));continue;}else{var _qU=I_quotRem(_qP.a,_qT.a);return new T2(0,new T1(1,_qU.a),new T1(1,_qU.b));}}}},_qV=0,_qW=new T1(0,0),_qX=function(_qY,_qZ){var _r0=B(_qx(_qZ)),_r1=_r0.a,_r2=_r0.b,_r3=new T(function(){return B(_pe(new T(function(){return B(_pc(_qY));})));});if(_r2<0){var _r4= -_r2;if(_r4>=0){var _r5=E(_r4);if(!_r5){var _r6=E(_oD);}else{var _r6=B(_pw(_pb,_r5));}if(!B(_qE(_r6,_qW))){var _r7=B(_qM(_r1,_r6));return new T2(0,new T(function(){return B(A2(_pQ,_r3,_r7.a));}),new T(function(){return B(_qA(_r7.b,_r2));}));}else{return E(_nC);}}else{return E(_qw);}}else{var _r8=new T(function(){var _r9=new T(function(){return B(_q4(_r3,_pa,new T(function(){return B(A2(_pQ,_r3,_pb));}),_r2));});return B(A3(_pC,_r3,new T(function(){return B(A2(_pQ,_r3,_r1));}),_r9));});return new T2(0,_r8,_qV);}},_ra=function(_rb){var _rc=E(_rb);if(!_rc._){return _rc.a;}else{return new F(function(){return I_toNumber(_rc.a);});}},_rd=function(_re,_rf){var _rg=B(_qX(_p6,Math.pow(B(_ra(_re)),_rf))),_rh=_rg.a;return (E(_rg.b)>=0)?E(_rh):E(_rh)-1|0;},_ri=new T1(0,1),_rj=new T1(0,0),_rk=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_rl=new T(function(){return B(err(_rk));}),_rm=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_rn=new T(function(){return B(err(_rm));}),_ro=new T1(0,2),_rp=new T(function(){return B(unCStr("NaN"));}),_rq=new T(function(){return B(_7f("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_rr=function(_rs,_rt){while(1){var _ru=B((function(_rv,_rw){var _rx=E(_rv);switch(_rx._){case 0:var _ry=E(_rw);if(!_ry._){return __Z;}else{_rs=B(A1(_rx.a,_ry.a));_rt=_ry.b;return __continue;}break;case 1:var _rz=B(A1(_rx.a,_rw)),_rA=_rw;_rs=_rz;_rt=_rA;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_rx.a,_rw),new T(function(){return B(_rr(_rx.b,_rw));}));default:return E(_rx.a);}})(_rs,_rt));if(_ru!=__continue){return _ru;}}},_rB=function(_rC,_rD){var _rE=function(_rF){var _rG=E(_rD);if(_rG._==3){return new T2(3,_rG.a,new T(function(){return B(_rB(_rC,_rG.b));}));}else{var _rH=E(_rC);if(_rH._==2){return E(_rG);}else{var _rI=E(_rG);if(_rI._==2){return E(_rH);}else{var _rJ=function(_rK){var _rL=E(_rI);if(_rL._==4){var _rM=function(_rN){return new T1(4,new T(function(){return B(_0(B(_rr(_rH,_rN)),_rL.a));}));};return new T1(1,_rM);}else{var _rO=E(_rH);if(_rO._==1){var _rP=_rO.a,_rQ=E(_rL);if(!_rQ._){return new T1(1,function(_rR){return new F(function(){return _rB(B(A1(_rP,_rR)),_rQ);});});}else{var _rS=function(_rT){return new F(function(){return _rB(B(A1(_rP,_rT)),new T(function(){return B(A1(_rQ.a,_rT));}));});};return new T1(1,_rS);}}else{var _rU=E(_rL);if(!_rU._){return E(_rq);}else{var _rV=function(_rW){return new F(function(){return _rB(_rO,new T(function(){return B(A1(_rU.a,_rW));}));});};return new T1(1,_rV);}}}},_rX=E(_rH);switch(_rX._){case 1:var _rY=E(_rI);if(_rY._==4){var _rZ=function(_s0){return new T1(4,new T(function(){return B(_0(B(_rr(B(A1(_rX.a,_s0)),_s0)),_rY.a));}));};return new T1(1,_rZ);}else{return new F(function(){return _rJ(_);});}break;case 4:var _s1=_rX.a,_s2=E(_rI);switch(_s2._){case 0:var _s3=function(_s4){var _s5=new T(function(){return B(_0(_s1,new T(function(){return B(_rr(_s2,_s4));},1)));});return new T1(4,_s5);};return new T1(1,_s3);case 1:var _s6=function(_s7){var _s8=new T(function(){return B(_0(_s1,new T(function(){return B(_rr(B(A1(_s2.a,_s7)),_s7));},1)));});return new T1(4,_s8);};return new T1(1,_s6);default:return new T1(4,new T(function(){return B(_0(_s1,_s2.a));}));}break;default:return new F(function(){return _rJ(_);});}}}}},_s9=E(_rC);switch(_s9._){case 0:var _sa=E(_rD);if(!_sa._){var _sb=function(_sc){return new F(function(){return _rB(B(A1(_s9.a,_sc)),new T(function(){return B(A1(_sa.a,_sc));}));});};return new T1(0,_sb);}else{return new F(function(){return _rE(_);});}break;case 3:return new T2(3,_s9.a,new T(function(){return B(_rB(_s9.b,_rD));}));default:return new F(function(){return _rE(_);});}},_sd=new T(function(){return B(unCStr("("));}),_se=new T(function(){return B(unCStr(")"));}),_sf=function(_sg,_sh){while(1){var _si=E(_sg);if(!_si._){return (E(_sh)._==0)?true:false;}else{var _sj=E(_sh);if(!_sj._){return false;}else{if(E(_si.a)!=E(_sj.a)){return false;}else{_sg=_si.b;_sh=_sj.b;continue;}}}}},_sk=function(_sl,_sm){return E(_sl)!=E(_sm);},_sn=function(_so,_sp){return E(_so)==E(_sp);},_sq=new T2(0,_sn,_sk),_sr=function(_ss,_st){while(1){var _su=E(_ss);if(!_su._){return (E(_st)._==0)?true:false;}else{var _sv=E(_st);if(!_sv._){return false;}else{if(E(_su.a)!=E(_sv.a)){return false;}else{_ss=_su.b;_st=_sv.b;continue;}}}}},_sw=function(_sx,_sy){return (!B(_sr(_sx,_sy)))?true:false;},_sz=new T2(0,_sr,_sw),_sA=function(_sB,_sC){var _sD=E(_sB);switch(_sD._){case 0:return new T1(0,function(_sE){return new F(function(){return _sA(B(A1(_sD.a,_sE)),_sC);});});case 1:return new T1(1,function(_sF){return new F(function(){return _sA(B(A1(_sD.a,_sF)),_sC);});});case 2:return new T0(2);case 3:return new F(function(){return _rB(B(A1(_sC,_sD.a)),new T(function(){return B(_sA(_sD.b,_sC));}));});break;default:var _sG=function(_sH){var _sI=E(_sH);if(!_sI._){return __Z;}else{var _sJ=E(_sI.a);return new F(function(){return _0(B(_rr(B(A1(_sC,_sJ.a)),_sJ.b)),new T(function(){return B(_sG(_sI.b));},1));});}},_sK=B(_sG(_sD.a));return (_sK._==0)?new T0(2):new T1(4,_sK);}},_sL=new T0(2),_sM=function(_sN){return new T2(3,_sN,_sL);},_sO=function(_sP,_sQ){var _sR=E(_sP);if(!_sR){return new F(function(){return A1(_sQ,_5);});}else{var _sS=new T(function(){return B(_sO(_sR-1|0,_sQ));});return new T1(0,function(_sT){return E(_sS);});}},_sU=function(_sV,_sW,_sX){var _sY=new T(function(){return B(A1(_sV,_sM));}),_sZ=function(_t0,_t1,_t2,_t3){while(1){var _t4=B((function(_t5,_t6,_t7,_t8){var _t9=E(_t5);switch(_t9._){case 0:var _ta=E(_t6);if(!_ta._){return new F(function(){return A1(_sW,_t8);});}else{var _tb=_t7+1|0,_tc=_t8;_t0=B(A1(_t9.a,_ta.a));_t1=_ta.b;_t2=_tb;_t3=_tc;return __continue;}break;case 1:var _td=B(A1(_t9.a,_t6)),_te=_t6,_tb=_t7,_tc=_t8;_t0=_td;_t1=_te;_t2=_tb;_t3=_tc;return __continue;case 2:return new F(function(){return A1(_sW,_t8);});break;case 3:var _tf=new T(function(){return B(_sA(_t9,_t8));});return new F(function(){return _sO(_t7,function(_tg){return E(_tf);});});break;default:return new F(function(){return _sA(_t9,_t8);});}})(_t0,_t1,_t2,_t3));if(_t4!=__continue){return _t4;}}};return function(_th){return new F(function(){return _sZ(_sY,_th,0,_sX);});};},_ti=function(_tj){return new F(function(){return A1(_tj,_4);});},_tk=function(_tl,_tm){var _tn=function(_to){var _tp=E(_to);if(!_tp._){return E(_ti);}else{var _tq=_tp.a;if(!B(A1(_tl,_tq))){return E(_ti);}else{var _tr=new T(function(){return B(_tn(_tp.b));}),_ts=function(_tt){var _tu=new T(function(){return B(A1(_tr,function(_tv){return new F(function(){return A1(_tt,new T2(1,_tq,_tv));});}));});return new T1(0,function(_tw){return E(_tu);});};return E(_ts);}}};return function(_tx){return new F(function(){return A2(_tn,_tx,_tm);});};},_ty=new T0(6),_tz=new T(function(){return B(unCStr("valDig: Bad base"));}),_tA=new T(function(){return B(err(_tz));}),_tB=function(_tC,_tD){var _tE=function(_tF,_tG){var _tH=E(_tF);if(!_tH._){var _tI=new T(function(){return B(A1(_tG,_4));});return function(_tJ){return new F(function(){return A1(_tJ,_tI);});};}else{var _tK=E(_tH.a),_tL=function(_tM){var _tN=new T(function(){return B(_tE(_tH.b,function(_tO){return new F(function(){return A1(_tG,new T2(1,_tM,_tO));});}));}),_tP=function(_tQ){var _tR=new T(function(){return B(A1(_tN,_tQ));});return new T1(0,function(_tS){return E(_tR);});};return E(_tP);};switch(E(_tC)){case 8:if(48>_tK){var _tT=new T(function(){return B(A1(_tG,_4));});return function(_tU){return new F(function(){return A1(_tU,_tT);});};}else{if(_tK>55){var _tV=new T(function(){return B(A1(_tG,_4));});return function(_tW){return new F(function(){return A1(_tW,_tV);});};}else{return new F(function(){return _tL(_tK-48|0);});}}break;case 10:if(48>_tK){var _tX=new T(function(){return B(A1(_tG,_4));});return function(_tY){return new F(function(){return A1(_tY,_tX);});};}else{if(_tK>57){var _tZ=new T(function(){return B(A1(_tG,_4));});return function(_u0){return new F(function(){return A1(_u0,_tZ);});};}else{return new F(function(){return _tL(_tK-48|0);});}}break;case 16:if(48>_tK){if(97>_tK){if(65>_tK){var _u1=new T(function(){return B(A1(_tG,_4));});return function(_u2){return new F(function(){return A1(_u2,_u1);});};}else{if(_tK>70){var _u3=new T(function(){return B(A1(_tG,_4));});return function(_u4){return new F(function(){return A1(_u4,_u3);});};}else{return new F(function(){return _tL((_tK-65|0)+10|0);});}}}else{if(_tK>102){if(65>_tK){var _u5=new T(function(){return B(A1(_tG,_4));});return function(_u6){return new F(function(){return A1(_u6,_u5);});};}else{if(_tK>70){var _u7=new T(function(){return B(A1(_tG,_4));});return function(_u8){return new F(function(){return A1(_u8,_u7);});};}else{return new F(function(){return _tL((_tK-65|0)+10|0);});}}}else{return new F(function(){return _tL((_tK-97|0)+10|0);});}}}else{if(_tK>57){if(97>_tK){if(65>_tK){var _u9=new T(function(){return B(A1(_tG,_4));});return function(_ua){return new F(function(){return A1(_ua,_u9);});};}else{if(_tK>70){var _ub=new T(function(){return B(A1(_tG,_4));});return function(_uc){return new F(function(){return A1(_uc,_ub);});};}else{return new F(function(){return _tL((_tK-65|0)+10|0);});}}}else{if(_tK>102){if(65>_tK){var _ud=new T(function(){return B(A1(_tG,_4));});return function(_ue){return new F(function(){return A1(_ue,_ud);});};}else{if(_tK>70){var _uf=new T(function(){return B(A1(_tG,_4));});return function(_ug){return new F(function(){return A1(_ug,_uf);});};}else{return new F(function(){return _tL((_tK-65|0)+10|0);});}}}else{return new F(function(){return _tL((_tK-97|0)+10|0);});}}}else{return new F(function(){return _tL(_tK-48|0);});}}break;default:return E(_tA);}}},_uh=function(_ui){var _uj=E(_ui);if(!_uj._){return new T0(2);}else{return new F(function(){return A1(_tD,_uj);});}};return function(_uk){return new F(function(){return A3(_tE,_uk,_2j,_uh);});};},_ul=16,_um=8,_un=function(_uo){var _up=function(_uq){return new F(function(){return A1(_uo,new T1(5,new T2(0,_um,_uq)));});},_ur=function(_us){return new F(function(){return A1(_uo,new T1(5,new T2(0,_ul,_us)));});},_ut=function(_uu){switch(E(_uu)){case 79:return new T1(1,B(_tB(_um,_up)));case 88:return new T1(1,B(_tB(_ul,_ur)));case 111:return new T1(1,B(_tB(_um,_up)));case 120:return new T1(1,B(_tB(_ul,_ur)));default:return new T0(2);}};return function(_uv){return (E(_uv)==48)?E(new T1(0,_ut)):new T0(2);};},_uw=function(_ux){return new T1(0,B(_un(_ux)));},_uy=function(_uz){return new F(function(){return A1(_uz,_4l);});},_uA=function(_uB){return new F(function(){return A1(_uB,_4l);});},_uC=10,_uD=new T1(0,1),_uE=new T1(0,2147483647),_uF=function(_uG,_uH){while(1){var _uI=E(_uG);if(!_uI._){var _uJ=_uI.a,_uK=E(_uH);if(!_uK._){var _uL=_uK.a,_uM=addC(_uJ,_uL);if(!E(_uM.b)){return new T1(0,_uM.a);}else{_uG=new T1(1,I_fromInt(_uJ));_uH=new T1(1,I_fromInt(_uL));continue;}}else{_uG=new T1(1,I_fromInt(_uJ));_uH=_uK;continue;}}else{var _uN=E(_uH);if(!_uN._){_uG=_uI;_uH=new T1(1,I_fromInt(_uN.a));continue;}else{return new T1(1,I_add(_uI.a,_uN.a));}}}},_uO=new T(function(){return B(_uF(_uE,_uD));}),_uP=function(_uQ){var _uR=E(_uQ);if(!_uR._){var _uS=E(_uR.a);return (_uS==(-2147483648))?E(_uO):new T1(0, -_uS);}else{return new T1(1,I_negate(_uR.a));}},_uT=new T1(0,10),_uU=function(_uV,_uW){while(1){var _uX=E(_uV);if(!_uX._){return E(_uW);}else{var _uY=_uW+1|0;_uV=_uX.b;_uW=_uY;continue;}}},_uZ=function(_v0){return new F(function(){return _oz(E(_v0));});},_v1=new T(function(){return B(unCStr("this should not happen"));}),_v2=new T(function(){return B(err(_v1));}),_v3=function(_v4,_v5){var _v6=E(_v5);if(!_v6._){return __Z;}else{var _v7=E(_v6.b);return (_v7._==0)?E(_v2):new T2(1,B(_uF(B(_pg(_v6.a,_v4)),_v7.a)),new T(function(){return B(_v3(_v4,_v7.b));}));}},_v8=new T1(0,0),_v9=function(_va,_vb,_vc){while(1){var _vd=B((function(_ve,_vf,_vg){var _vh=E(_vg);if(!_vh._){return E(_v8);}else{if(!E(_vh.b)._){return E(_vh.a);}else{var _vi=E(_vf);if(_vi<=40){var _vj=function(_vk,_vl){while(1){var _vm=E(_vl);if(!_vm._){return E(_vk);}else{var _vn=B(_uF(B(_pg(_vk,_ve)),_vm.a));_vk=_vn;_vl=_vm.b;continue;}}};return new F(function(){return _vj(_v8,_vh);});}else{var _vo=B(_pg(_ve,_ve));if(!(_vi%2)){var _vp=B(_v3(_ve,_vh));_va=_vo;_vb=quot(_vi+1|0,2);_vc=_vp;return __continue;}else{var _vp=B(_v3(_ve,new T2(1,_v8,_vh)));_va=_vo;_vb=quot(_vi+1|0,2);_vc=_vp;return __continue;}}}}})(_va,_vb,_vc));if(_vd!=__continue){return _vd;}}},_vq=function(_vr,_vs){return new F(function(){return _v9(_vr,new T(function(){return B(_uU(_vs,0));},1),B(_G(_uZ,_vs)));});},_vt=function(_vu){var _vv=new T(function(){var _vw=new T(function(){var _vx=function(_vy){return new F(function(){return A1(_vu,new T1(1,new T(function(){return B(_vq(_uT,_vy));})));});};return new T1(1,B(_tB(_uC,_vx)));}),_vz=function(_vA){if(E(_vA)==43){var _vB=function(_vC){return new F(function(){return A1(_vu,new T1(1,new T(function(){return B(_vq(_uT,_vC));})));});};return new T1(1,B(_tB(_uC,_vB)));}else{return new T0(2);}},_vD=function(_vE){if(E(_vE)==45){var _vF=function(_vG){return new F(function(){return A1(_vu,new T1(1,new T(function(){return B(_uP(B(_vq(_uT,_vG))));})));});};return new T1(1,B(_tB(_uC,_vF)));}else{return new T0(2);}};return B(_rB(B(_rB(new T1(0,_vD),new T1(0,_vz))),_vw));});return new F(function(){return _rB(new T1(0,function(_vH){return (E(_vH)==101)?E(_vv):new T0(2);}),new T1(0,function(_vI){return (E(_vI)==69)?E(_vv):new T0(2);}));});},_vJ=function(_vK){var _vL=function(_vM){return new F(function(){return A1(_vK,new T1(1,_vM));});};return function(_vN){return (E(_vN)==46)?new T1(1,B(_tB(_uC,_vL))):new T0(2);};},_vO=function(_vP){return new T1(0,B(_vJ(_vP)));},_vQ=function(_vR){var _vS=function(_vT){var _vU=function(_vV){return new T1(1,B(_sU(_vt,_uy,function(_vW){return new F(function(){return A1(_vR,new T1(5,new T3(1,_vT,_vV,_vW)));});})));};return new T1(1,B(_sU(_vO,_uA,_vU)));};return new F(function(){return _tB(_uC,_vS);});},_vX=function(_vY){return new T1(1,B(_vQ(_vY)));},_vZ=function(_w0,_w1,_w2){while(1){var _w3=E(_w2);if(!_w3._){return false;}else{if(!B(A3(_pM,_w0,_w1,_w3.a))){_w2=_w3.b;continue;}else{return true;}}}},_w4=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_w5=function(_w6){return new F(function(){return _vZ(_sq,_w6,_w4);});},_w7=false,_w8=true,_w9=function(_wa){var _wb=new T(function(){return B(A1(_wa,_um));}),_wc=new T(function(){return B(A1(_wa,_ul));});return function(_wd){switch(E(_wd)){case 79:return E(_wb);case 88:return E(_wc);case 111:return E(_wb);case 120:return E(_wc);default:return new T0(2);}};},_we=function(_wf){return new T1(0,B(_w9(_wf)));},_wg=function(_wh){return new F(function(){return A1(_wh,_uC);});},_wi=function(_wj,_wk){var _wl=E(_wj);if(!_wl._){var _wm=_wl.a,_wn=E(_wk);return (_wn._==0)?_wm<=_wn.a:I_compareInt(_wn.a,_wm)>=0;}else{var _wo=_wl.a,_wp=E(_wk);return (_wp._==0)?I_compareInt(_wo,_wp.a)<=0:I_compare(_wo,_wp.a)<=0;}},_wq=function(_wr){return new T0(2);},_ws=function(_wt){var _wu=E(_wt);if(!_wu._){return E(_wq);}else{var _wv=_wu.a,_ww=E(_wu.b);if(!_ww._){return E(_wv);}else{var _wx=new T(function(){return B(_ws(_ww));}),_wy=function(_wz){return new F(function(){return _rB(B(A1(_wv,_wz)),new T(function(){return B(A1(_wx,_wz));}));});};return E(_wy);}}},_wA=function(_wB,_wC){var _wD=function(_wE,_wF,_wG){var _wH=E(_wE);if(!_wH._){return new F(function(){return A1(_wG,_wB);});}else{var _wI=E(_wF);if(!_wI._){return new T0(2);}else{if(E(_wH.a)!=E(_wI.a)){return new T0(2);}else{var _wJ=new T(function(){return B(_wD(_wH.b,_wI.b,_wG));});return new T1(0,function(_wK){return E(_wJ);});}}}};return function(_wL){return new F(function(){return _wD(_wB,_wL,_wC);});};},_wM=new T(function(){return B(unCStr("SO"));}),_wN=14,_wO=function(_wP){var _wQ=new T(function(){return B(A1(_wP,_wN));});return new T1(1,B(_wA(_wM,function(_wR){return E(_wQ);})));},_wS=new T(function(){return B(unCStr("SOH"));}),_wT=1,_wU=function(_wV){var _wW=new T(function(){return B(A1(_wV,_wT));});return new T1(1,B(_wA(_wS,function(_wX){return E(_wW);})));},_wY=function(_wZ){return new T1(1,B(_sU(_wU,_wO,_wZ)));},_x0=new T(function(){return B(unCStr("NUL"));}),_x1=0,_x2=function(_x3){var _x4=new T(function(){return B(A1(_x3,_x1));});return new T1(1,B(_wA(_x0,function(_x5){return E(_x4);})));},_x6=new T(function(){return B(unCStr("STX"));}),_x7=2,_x8=function(_x9){var _xa=new T(function(){return B(A1(_x9,_x7));});return new T1(1,B(_wA(_x6,function(_xb){return E(_xa);})));},_xc=new T(function(){return B(unCStr("ETX"));}),_xd=3,_xe=function(_xf){var _xg=new T(function(){return B(A1(_xf,_xd));});return new T1(1,B(_wA(_xc,function(_xh){return E(_xg);})));},_xi=new T(function(){return B(unCStr("EOT"));}),_xj=4,_xk=function(_xl){var _xm=new T(function(){return B(A1(_xl,_xj));});return new T1(1,B(_wA(_xi,function(_xn){return E(_xm);})));},_xo=new T(function(){return B(unCStr("ENQ"));}),_xp=5,_xq=function(_xr){var _xs=new T(function(){return B(A1(_xr,_xp));});return new T1(1,B(_wA(_xo,function(_xt){return E(_xs);})));},_xu=new T(function(){return B(unCStr("ACK"));}),_xv=6,_xw=function(_xx){var _xy=new T(function(){return B(A1(_xx,_xv));});return new T1(1,B(_wA(_xu,function(_xz){return E(_xy);})));},_xA=new T(function(){return B(unCStr("BEL"));}),_xB=7,_xC=function(_xD){var _xE=new T(function(){return B(A1(_xD,_xB));});return new T1(1,B(_wA(_xA,function(_xF){return E(_xE);})));},_xG=new T(function(){return B(unCStr("BS"));}),_xH=8,_xI=function(_xJ){var _xK=new T(function(){return B(A1(_xJ,_xH));});return new T1(1,B(_wA(_xG,function(_xL){return E(_xK);})));},_xM=new T(function(){return B(unCStr("HT"));}),_xN=9,_xO=function(_xP){var _xQ=new T(function(){return B(A1(_xP,_xN));});return new T1(1,B(_wA(_xM,function(_xR){return E(_xQ);})));},_xS=new T(function(){return B(unCStr("LF"));}),_xT=10,_xU=function(_xV){var _xW=new T(function(){return B(A1(_xV,_xT));});return new T1(1,B(_wA(_xS,function(_xX){return E(_xW);})));},_xY=new T(function(){return B(unCStr("VT"));}),_xZ=11,_y0=function(_y1){var _y2=new T(function(){return B(A1(_y1,_xZ));});return new T1(1,B(_wA(_xY,function(_y3){return E(_y2);})));},_y4=new T(function(){return B(unCStr("FF"));}),_y5=12,_y6=function(_y7){var _y8=new T(function(){return B(A1(_y7,_y5));});return new T1(1,B(_wA(_y4,function(_y9){return E(_y8);})));},_ya=new T(function(){return B(unCStr("CR"));}),_yb=13,_yc=function(_yd){var _ye=new T(function(){return B(A1(_yd,_yb));});return new T1(1,B(_wA(_ya,function(_yf){return E(_ye);})));},_yg=new T(function(){return B(unCStr("SI"));}),_yh=15,_yi=function(_yj){var _yk=new T(function(){return B(A1(_yj,_yh));});return new T1(1,B(_wA(_yg,function(_yl){return E(_yk);})));},_ym=new T(function(){return B(unCStr("DLE"));}),_yn=16,_yo=function(_yp){var _yq=new T(function(){return B(A1(_yp,_yn));});return new T1(1,B(_wA(_ym,function(_yr){return E(_yq);})));},_ys=new T(function(){return B(unCStr("DC1"));}),_yt=17,_yu=function(_yv){var _yw=new T(function(){return B(A1(_yv,_yt));});return new T1(1,B(_wA(_ys,function(_yx){return E(_yw);})));},_yy=new T(function(){return B(unCStr("DC2"));}),_yz=18,_yA=function(_yB){var _yC=new T(function(){return B(A1(_yB,_yz));});return new T1(1,B(_wA(_yy,function(_yD){return E(_yC);})));},_yE=new T(function(){return B(unCStr("DC3"));}),_yF=19,_yG=function(_yH){var _yI=new T(function(){return B(A1(_yH,_yF));});return new T1(1,B(_wA(_yE,function(_yJ){return E(_yI);})));},_yK=new T(function(){return B(unCStr("DC4"));}),_yL=20,_yM=function(_yN){var _yO=new T(function(){return B(A1(_yN,_yL));});return new T1(1,B(_wA(_yK,function(_yP){return E(_yO);})));},_yQ=new T(function(){return B(unCStr("NAK"));}),_yR=21,_yS=function(_yT){var _yU=new T(function(){return B(A1(_yT,_yR));});return new T1(1,B(_wA(_yQ,function(_yV){return E(_yU);})));},_yW=new T(function(){return B(unCStr("SYN"));}),_yX=22,_yY=function(_yZ){var _z0=new T(function(){return B(A1(_yZ,_yX));});return new T1(1,B(_wA(_yW,function(_z1){return E(_z0);})));},_z2=new T(function(){return B(unCStr("ETB"));}),_z3=23,_z4=function(_z5){var _z6=new T(function(){return B(A1(_z5,_z3));});return new T1(1,B(_wA(_z2,function(_z7){return E(_z6);})));},_z8=new T(function(){return B(unCStr("CAN"));}),_z9=24,_za=function(_zb){var _zc=new T(function(){return B(A1(_zb,_z9));});return new T1(1,B(_wA(_z8,function(_zd){return E(_zc);})));},_ze=new T(function(){return B(unCStr("EM"));}),_zf=25,_zg=function(_zh){var _zi=new T(function(){return B(A1(_zh,_zf));});return new T1(1,B(_wA(_ze,function(_zj){return E(_zi);})));},_zk=new T(function(){return B(unCStr("SUB"));}),_zl=26,_zm=function(_zn){var _zo=new T(function(){return B(A1(_zn,_zl));});return new T1(1,B(_wA(_zk,function(_zp){return E(_zo);})));},_zq=new T(function(){return B(unCStr("ESC"));}),_zr=27,_zs=function(_zt){var _zu=new T(function(){return B(A1(_zt,_zr));});return new T1(1,B(_wA(_zq,function(_zv){return E(_zu);})));},_zw=new T(function(){return B(unCStr("FS"));}),_zx=28,_zy=function(_zz){var _zA=new T(function(){return B(A1(_zz,_zx));});return new T1(1,B(_wA(_zw,function(_zB){return E(_zA);})));},_zC=new T(function(){return B(unCStr("GS"));}),_zD=29,_zE=function(_zF){var _zG=new T(function(){return B(A1(_zF,_zD));});return new T1(1,B(_wA(_zC,function(_zH){return E(_zG);})));},_zI=new T(function(){return B(unCStr("RS"));}),_zJ=30,_zK=function(_zL){var _zM=new T(function(){return B(A1(_zL,_zJ));});return new T1(1,B(_wA(_zI,function(_zN){return E(_zM);})));},_zO=new T(function(){return B(unCStr("US"));}),_zP=31,_zQ=function(_zR){var _zS=new T(function(){return B(A1(_zR,_zP));});return new T1(1,B(_wA(_zO,function(_zT){return E(_zS);})));},_zU=new T(function(){return B(unCStr("SP"));}),_zV=32,_zW=function(_zX){var _zY=new T(function(){return B(A1(_zX,_zV));});return new T1(1,B(_wA(_zU,function(_zZ){return E(_zY);})));},_A0=new T(function(){return B(unCStr("DEL"));}),_A1=127,_A2=function(_A3){var _A4=new T(function(){return B(A1(_A3,_A1));});return new T1(1,B(_wA(_A0,function(_A5){return E(_A4);})));},_A6=new T2(1,_A2,_4),_A7=new T2(1,_zW,_A6),_A8=new T2(1,_zQ,_A7),_A9=new T2(1,_zK,_A8),_Aa=new T2(1,_zE,_A9),_Ab=new T2(1,_zy,_Aa),_Ac=new T2(1,_zs,_Ab),_Ad=new T2(1,_zm,_Ac),_Ae=new T2(1,_zg,_Ad),_Af=new T2(1,_za,_Ae),_Ag=new T2(1,_z4,_Af),_Ah=new T2(1,_yY,_Ag),_Ai=new T2(1,_yS,_Ah),_Aj=new T2(1,_yM,_Ai),_Ak=new T2(1,_yG,_Aj),_Al=new T2(1,_yA,_Ak),_Am=new T2(1,_yu,_Al),_An=new T2(1,_yo,_Am),_Ao=new T2(1,_yi,_An),_Ap=new T2(1,_yc,_Ao),_Aq=new T2(1,_y6,_Ap),_Ar=new T2(1,_y0,_Aq),_As=new T2(1,_xU,_Ar),_At=new T2(1,_xO,_As),_Au=new T2(1,_xI,_At),_Av=new T2(1,_xC,_Au),_Aw=new T2(1,_xw,_Av),_Ax=new T2(1,_xq,_Aw),_Ay=new T2(1,_xk,_Ax),_Az=new T2(1,_xe,_Ay),_AA=new T2(1,_x8,_Az),_AB=new T2(1,_x2,_AA),_AC=new T2(1,_wY,_AB),_AD=new T(function(){return B(_ws(_AC));}),_AE=34,_AF=new T1(0,1114111),_AG=92,_AH=39,_AI=function(_AJ){var _AK=new T(function(){return B(A1(_AJ,_xB));}),_AL=new T(function(){return B(A1(_AJ,_xH));}),_AM=new T(function(){return B(A1(_AJ,_xN));}),_AN=new T(function(){return B(A1(_AJ,_xT));}),_AO=new T(function(){return B(A1(_AJ,_xZ));}),_AP=new T(function(){return B(A1(_AJ,_y5));}),_AQ=new T(function(){return B(A1(_AJ,_yb));}),_AR=new T(function(){return B(A1(_AJ,_AG));}),_AS=new T(function(){return B(A1(_AJ,_AH));}),_AT=new T(function(){return B(A1(_AJ,_AE));}),_AU=new T(function(){var _AV=function(_AW){var _AX=new T(function(){return B(_oz(E(_AW)));}),_AY=function(_AZ){var _B0=B(_vq(_AX,_AZ));if(!B(_wi(_B0,_AF))){return new T0(2);}else{return new F(function(){return A1(_AJ,new T(function(){var _B1=B(_oP(_B0));if(_B1>>>0>1114111){return B(_fK(_B1));}else{return _B1;}}));});}};return new T1(1,B(_tB(_AW,_AY)));},_B2=new T(function(){var _B3=new T(function(){return B(A1(_AJ,_zP));}),_B4=new T(function(){return B(A1(_AJ,_zJ));}),_B5=new T(function(){return B(A1(_AJ,_zD));}),_B6=new T(function(){return B(A1(_AJ,_zx));}),_B7=new T(function(){return B(A1(_AJ,_zr));}),_B8=new T(function(){return B(A1(_AJ,_zl));}),_B9=new T(function(){return B(A1(_AJ,_zf));}),_Ba=new T(function(){return B(A1(_AJ,_z9));}),_Bb=new T(function(){return B(A1(_AJ,_z3));}),_Bc=new T(function(){return B(A1(_AJ,_yX));}),_Bd=new T(function(){return B(A1(_AJ,_yR));}),_Be=new T(function(){return B(A1(_AJ,_yL));}),_Bf=new T(function(){return B(A1(_AJ,_yF));}),_Bg=new T(function(){return B(A1(_AJ,_yz));}),_Bh=new T(function(){return B(A1(_AJ,_yt));}),_Bi=new T(function(){return B(A1(_AJ,_yn));}),_Bj=new T(function(){return B(A1(_AJ,_yh));}),_Bk=new T(function(){return B(A1(_AJ,_wN));}),_Bl=new T(function(){return B(A1(_AJ,_xv));}),_Bm=new T(function(){return B(A1(_AJ,_xp));}),_Bn=new T(function(){return B(A1(_AJ,_xj));}),_Bo=new T(function(){return B(A1(_AJ,_xd));}),_Bp=new T(function(){return B(A1(_AJ,_x7));}),_Bq=new T(function(){return B(A1(_AJ,_wT));}),_Br=new T(function(){return B(A1(_AJ,_x1));}),_Bs=function(_Bt){switch(E(_Bt)){case 64:return E(_Br);case 65:return E(_Bq);case 66:return E(_Bp);case 67:return E(_Bo);case 68:return E(_Bn);case 69:return E(_Bm);case 70:return E(_Bl);case 71:return E(_AK);case 72:return E(_AL);case 73:return E(_AM);case 74:return E(_AN);case 75:return E(_AO);case 76:return E(_AP);case 77:return E(_AQ);case 78:return E(_Bk);case 79:return E(_Bj);case 80:return E(_Bi);case 81:return E(_Bh);case 82:return E(_Bg);case 83:return E(_Bf);case 84:return E(_Be);case 85:return E(_Bd);case 86:return E(_Bc);case 87:return E(_Bb);case 88:return E(_Ba);case 89:return E(_B9);case 90:return E(_B8);case 91:return E(_B7);case 92:return E(_B6);case 93:return E(_B5);case 94:return E(_B4);case 95:return E(_B3);default:return new T0(2);}};return B(_rB(new T1(0,function(_Bu){return (E(_Bu)==94)?E(new T1(0,_Bs)):new T0(2);}),new T(function(){return B(A1(_AD,_AJ));})));});return B(_rB(new T1(1,B(_sU(_we,_wg,_AV))),_B2));});return new F(function(){return _rB(new T1(0,function(_Bv){switch(E(_Bv)){case 34:return E(_AT);case 39:return E(_AS);case 92:return E(_AR);case 97:return E(_AK);case 98:return E(_AL);case 102:return E(_AP);case 110:return E(_AN);case 114:return E(_AQ);case 116:return E(_AM);case 118:return E(_AO);default:return new T0(2);}}),_AU);});},_Bw=function(_Bx){return new F(function(){return A1(_Bx,_5);});},_By=function(_Bz){var _BA=E(_Bz);if(!_BA._){return E(_Bw);}else{var _BB=E(_BA.a),_BC=_BB>>>0,_BD=new T(function(){return B(_By(_BA.b));});if(_BC>887){var _BE=u_iswspace(_BB);if(!E(_BE)){return E(_Bw);}else{var _BF=function(_BG){var _BH=new T(function(){return B(A1(_BD,_BG));});return new T1(0,function(_BI){return E(_BH);});};return E(_BF);}}else{var _BJ=E(_BC);if(_BJ==32){var _BK=function(_BL){var _BM=new T(function(){return B(A1(_BD,_BL));});return new T1(0,function(_BN){return E(_BM);});};return E(_BK);}else{if(_BJ-9>>>0>4){if(E(_BJ)==160){var _BO=function(_BP){var _BQ=new T(function(){return B(A1(_BD,_BP));});return new T1(0,function(_BR){return E(_BQ);});};return E(_BO);}else{return E(_Bw);}}else{var _BS=function(_BT){var _BU=new T(function(){return B(A1(_BD,_BT));});return new T1(0,function(_BV){return E(_BU);});};return E(_BS);}}}}},_BW=function(_BX){var _BY=new T(function(){return B(_BW(_BX));}),_BZ=function(_C0){return (E(_C0)==92)?E(_BY):new T0(2);},_C1=function(_C2){return E(new T1(0,_BZ));},_C3=new T1(1,function(_C4){return new F(function(){return A2(_By,_C4,_C1);});}),_C5=new T(function(){return B(_AI(function(_C6){return new F(function(){return A1(_BX,new T2(0,_C6,_w8));});}));}),_C7=function(_C8){var _C9=E(_C8);if(_C9==38){return E(_BY);}else{var _Ca=_C9>>>0;if(_Ca>887){var _Cb=u_iswspace(_C9);return (E(_Cb)==0)?new T0(2):E(_C3);}else{var _Cc=E(_Ca);return (_Cc==32)?E(_C3):(_Cc-9>>>0>4)?(E(_Cc)==160)?E(_C3):new T0(2):E(_C3);}}};return new F(function(){return _rB(new T1(0,function(_Cd){return (E(_Cd)==92)?E(new T1(0,_C7)):new T0(2);}),new T1(0,function(_Ce){var _Cf=E(_Ce);if(E(_Cf)==92){return E(_C5);}else{return new F(function(){return A1(_BX,new T2(0,_Cf,_w7));});}}));});},_Cg=function(_Ch,_Ci){var _Cj=new T(function(){return B(A1(_Ci,new T1(1,new T(function(){return B(A1(_Ch,_4));}))));}),_Ck=function(_Cl){var _Cm=E(_Cl),_Cn=E(_Cm.a);if(E(_Cn)==34){if(!E(_Cm.b)){return E(_Cj);}else{return new F(function(){return _Cg(function(_Co){return new F(function(){return A1(_Ch,new T2(1,_Cn,_Co));});},_Ci);});}}else{return new F(function(){return _Cg(function(_Cp){return new F(function(){return A1(_Ch,new T2(1,_Cn,_Cp));});},_Ci);});}};return new F(function(){return _BW(_Ck);});},_Cq=new T(function(){return B(unCStr("_\'"));}),_Cr=function(_Cs){var _Ct=u_iswalnum(_Cs);if(!E(_Ct)){return new F(function(){return _vZ(_sq,_Cs,_Cq);});}else{return true;}},_Cu=function(_Cv){return new F(function(){return _Cr(E(_Cv));});},_Cw=new T(function(){return B(unCStr(",;()[]{}`"));}),_Cx=new T(function(){return B(unCStr("=>"));}),_Cy=new T2(1,_Cx,_4),_Cz=new T(function(){return B(unCStr("~"));}),_CA=new T2(1,_Cz,_Cy),_CB=new T(function(){return B(unCStr("@"));}),_CC=new T2(1,_CB,_CA),_CD=new T(function(){return B(unCStr("->"));}),_CE=new T2(1,_CD,_CC),_CF=new T(function(){return B(unCStr("<-"));}),_CG=new T2(1,_CF,_CE),_CH=new T(function(){return B(unCStr("|"));}),_CI=new T2(1,_CH,_CG),_CJ=new T(function(){return B(unCStr("\\"));}),_CK=new T2(1,_CJ,_CI),_CL=new T(function(){return B(unCStr("="));}),_CM=new T2(1,_CL,_CK),_CN=new T(function(){return B(unCStr("::"));}),_CO=new T2(1,_CN,_CM),_CP=new T(function(){return B(unCStr(".."));}),_CQ=new T2(1,_CP,_CO),_CR=function(_CS){var _CT=new T(function(){return B(A1(_CS,_ty));}),_CU=new T(function(){var _CV=new T(function(){var _CW=function(_CX){var _CY=new T(function(){return B(A1(_CS,new T1(0,_CX)));});return new T1(0,function(_CZ){return (E(_CZ)==39)?E(_CY):new T0(2);});};return B(_AI(_CW));}),_D0=function(_D1){var _D2=E(_D1);switch(E(_D2)){case 39:return new T0(2);case 92:return E(_CV);default:var _D3=new T(function(){return B(A1(_CS,new T1(0,_D2)));});return new T1(0,function(_D4){return (E(_D4)==39)?E(_D3):new T0(2);});}},_D5=new T(function(){var _D6=new T(function(){return B(_Cg(_2j,_CS));}),_D7=new T(function(){var _D8=new T(function(){var _D9=new T(function(){var _Da=function(_Db){var _Dc=E(_Db),_Dd=u_iswalpha(_Dc);return (E(_Dd)==0)?(E(_Dc)==95)?new T1(1,B(_tk(_Cu,function(_De){return new F(function(){return A1(_CS,new T1(3,new T2(1,_Dc,_De)));});}))):new T0(2):new T1(1,B(_tk(_Cu,function(_Df){return new F(function(){return A1(_CS,new T1(3,new T2(1,_Dc,_Df)));});})));};return B(_rB(new T1(0,_Da),new T(function(){return new T1(1,B(_sU(_uw,_vX,_CS)));})));}),_Dg=function(_Dh){return (!B(_vZ(_sq,_Dh,_w4)))?new T0(2):new T1(1,B(_tk(_w5,function(_Di){var _Dj=new T2(1,_Dh,_Di);if(!B(_vZ(_sz,_Dj,_CQ))){return new F(function(){return A1(_CS,new T1(4,_Dj));});}else{return new F(function(){return A1(_CS,new T1(2,_Dj));});}})));};return B(_rB(new T1(0,_Dg),_D9));});return B(_rB(new T1(0,function(_Dk){if(!B(_vZ(_sq,_Dk,_Cw))){return new T0(2);}else{return new F(function(){return A1(_CS,new T1(2,new T2(1,_Dk,_4)));});}}),_D8));});return B(_rB(new T1(0,function(_Dl){return (E(_Dl)==34)?E(_D6):new T0(2);}),_D7));});return B(_rB(new T1(0,function(_Dm){return (E(_Dm)==39)?E(new T1(0,_D0)):new T0(2);}),_D5));});return new F(function(){return _rB(new T1(1,function(_Dn){return (E(_Dn)._==0)?E(_CT):new T0(2);}),_CU);});},_Do=0,_Dp=function(_Dq,_Dr){var _Ds=new T(function(){var _Dt=new T(function(){var _Du=function(_Dv){var _Dw=new T(function(){var _Dx=new T(function(){return B(A1(_Dr,_Dv));});return B(_CR(function(_Dy){var _Dz=E(_Dy);return (_Dz._==2)?(!B(_sf(_Dz.a,_se)))?new T0(2):E(_Dx):new T0(2);}));}),_DA=function(_DB){return E(_Dw);};return new T1(1,function(_DC){return new F(function(){return A2(_By,_DC,_DA);});});};return B(A2(_Dq,_Do,_Du));});return B(_CR(function(_DD){var _DE=E(_DD);return (_DE._==2)?(!B(_sf(_DE.a,_sd)))?new T0(2):E(_Dt):new T0(2);}));}),_DF=function(_DG){return E(_Ds);};return function(_DH){return new F(function(){return A2(_By,_DH,_DF);});};},_DI=function(_DJ,_DK){var _DL=function(_DM){var _DN=new T(function(){return B(A1(_DJ,_DM));}),_DO=function(_DP){return new F(function(){return _rB(B(A1(_DN,_DP)),new T(function(){return new T1(1,B(_Dp(_DL,_DP)));}));});};return E(_DO);},_DQ=new T(function(){return B(A1(_DJ,_DK));}),_DR=function(_DS){return new F(function(){return _rB(B(A1(_DQ,_DS)),new T(function(){return new T1(1,B(_Dp(_DL,_DS)));}));});};return E(_DR);},_DT=function(_DU,_DV){var _DW=function(_DX,_DY){var _DZ=function(_E0){return new F(function(){return A1(_DY,new T(function(){return  -E(_E0);}));});},_E1=new T(function(){return B(_CR(function(_E2){return new F(function(){return A3(_DU,_E2,_DX,_DZ);});}));}),_E3=function(_E4){return E(_E1);},_E5=function(_E6){return new F(function(){return A2(_By,_E6,_E3);});},_E7=new T(function(){return B(_CR(function(_E8){var _E9=E(_E8);if(_E9._==4){var _Ea=E(_E9.a);if(!_Ea._){return new F(function(){return A3(_DU,_E9,_DX,_DY);});}else{if(E(_Ea.a)==45){if(!E(_Ea.b)._){return E(new T1(1,_E5));}else{return new F(function(){return A3(_DU,_E9,_DX,_DY);});}}else{return new F(function(){return A3(_DU,_E9,_DX,_DY);});}}}else{return new F(function(){return A3(_DU,_E9,_DX,_DY);});}}));}),_Eb=function(_Ec){return E(_E7);};return new T1(1,function(_Ed){return new F(function(){return A2(_By,_Ed,_Eb);});});};return new F(function(){return _DI(_DW,_DV);});},_Ee=new T(function(){return 1/0;}),_Ef=function(_Eg,_Eh){return new F(function(){return A1(_Eh,_Ee);});},_Ei=new T(function(){return 0/0;}),_Ej=function(_Ek,_El){return new F(function(){return A1(_El,_Ei);});},_Em=new T(function(){return B(unCStr("NaN"));}),_En=new T(function(){return B(unCStr("Infinity"));}),_Eo=1024,_Ep=-1021,_Eq=function(_Er,_Es){while(1){var _Et=E(_Er);if(!_Et._){var _Eu=E(_Et.a);if(_Eu==(-2147483648)){_Er=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ev=E(_Es);if(!_Ev._){return new T1(0,_Eu%_Ev.a);}else{_Er=new T1(1,I_fromInt(_Eu));_Es=_Ev;continue;}}}else{var _Ew=_Et.a,_Ex=E(_Es);return (_Ex._==0)?new T1(1,I_rem(_Ew,I_fromInt(_Ex.a))):new T1(1,I_rem(_Ew,_Ex.a));}}},_Ey=function(_Ez,_EA){if(!B(_qE(_EA,_pO))){return new F(function(){return _Eq(_Ez,_EA);});}else{return E(_nC);}},_EB=function(_EC,_ED){while(1){if(!B(_qE(_ED,_pO))){var _EE=_ED,_EF=B(_Ey(_EC,_ED));_EC=_EE;_ED=_EF;continue;}else{return E(_EC);}}},_EG=function(_EH){var _EI=E(_EH);if(!_EI._){var _EJ=E(_EI.a);return (_EJ==(-2147483648))?E(_uO):(_EJ<0)?new T1(0, -_EJ):E(_EI);}else{var _EK=_EI.a;return (I_compareInt(_EK,0)>=0)?E(_EI):new T1(1,I_negate(_EK));}},_EL=function(_EM,_EN){while(1){var _EO=E(_EM);if(!_EO._){var _EP=E(_EO.a);if(_EP==(-2147483648)){_EM=new T1(1,I_fromInt(-2147483648));continue;}else{var _EQ=E(_EN);if(!_EQ._){return new T1(0,quot(_EP,_EQ.a));}else{_EM=new T1(1,I_fromInt(_EP));_EN=_EQ;continue;}}}else{var _ER=_EO.a,_ES=E(_EN);return (_ES._==0)?new T1(0,I_toInt(I_quot(_ER,I_fromInt(_ES.a)))):new T1(1,I_quot(_ER,_ES.a));}}},_ET=5,_EU=new T(function(){return B(_nz(_ET));}),_EV=new T(function(){return die(_EU);}),_EW=function(_EX,_EY){if(!B(_qE(_EY,_pO))){var _EZ=B(_EB(B(_EG(_EX)),B(_EG(_EY))));return (!B(_qE(_EZ,_pO)))?new T2(0,B(_EL(_EX,_EZ)),B(_EL(_EY,_EZ))):E(_nC);}else{return E(_EV);}},_F0=new T(function(){return B(_qE(_pP,_pO));}),_F1=function(_F2,_F3){while(1){var _F4=E(_F2);if(!_F4._){var _F5=_F4.a,_F6=E(_F3);if(!_F6._){var _F7=_F6.a,_F8=subC(_F5,_F7);if(!E(_F8.b)){return new T1(0,_F8.a);}else{_F2=new T1(1,I_fromInt(_F5));_F3=new T1(1,I_fromInt(_F7));continue;}}else{_F2=new T1(1,I_fromInt(_F5));_F3=_F6;continue;}}else{var _F9=E(_F3);if(!_F9._){_F2=_F4;_F3=new T1(1,I_fromInt(_F9.a));continue;}else{return new T1(1,I_sub(_F4.a,_F9.a));}}}},_Fa=function(_Fb,_Fc,_Fd){while(1){if(!E(_F0)){if(!B(_qE(B(_Eq(_Fc,_pP)),_pO))){if(!B(_qE(_Fc,_oD))){var _Fe=B(_pg(_Fb,_Fb)),_Ff=B(_EL(B(_F1(_Fc,_oD)),_pP)),_Fg=B(_pg(_Fb,_Fd));_Fb=_Fe;_Fc=_Ff;_Fd=_Fg;continue;}else{return new F(function(){return _pg(_Fb,_Fd);});}}else{var _Fe=B(_pg(_Fb,_Fb)),_Ff=B(_EL(_Fc,_pP));_Fb=_Fe;_Fc=_Ff;continue;}}else{return E(_nC);}}},_Fh=function(_Fi,_Fj){while(1){if(!E(_F0)){if(!B(_qE(B(_Eq(_Fj,_pP)),_pO))){if(!B(_qE(_Fj,_oD))){return new F(function(){return _Fa(B(_pg(_Fi,_Fi)),B(_EL(B(_F1(_Fj,_oD)),_pP)),_Fi);});}else{return E(_Fi);}}else{var _Fk=B(_pg(_Fi,_Fi)),_Fl=B(_EL(_Fj,_pP));_Fi=_Fk;_Fj=_Fl;continue;}}else{return E(_nC);}}},_Fm=function(_Fn,_Fo){var _Fp=E(_Fn);if(!_Fp._){var _Fq=_Fp.a,_Fr=E(_Fo);return (_Fr._==0)?_Fq<_Fr.a:I_compareInt(_Fr.a,_Fq)>0;}else{var _Fs=_Fp.a,_Ft=E(_Fo);return (_Ft._==0)?I_compareInt(_Fs,_Ft.a)<0:I_compare(_Fs,_Ft.a)<0;}},_Fu=function(_Fv,_Fw){if(!B(_Fm(_Fw,_pO))){if(!B(_qE(_Fw,_pO))){return new F(function(){return _Fh(_Fv,_Fw);});}else{return E(_oD);}}else{return E(_qw);}},_Fx=new T1(0,1),_Fy=new T1(0,0),_Fz=new T1(0,-1),_FA=function(_FB){var _FC=E(_FB);if(!_FC._){var _FD=_FC.a;return (_FD>=0)?(E(_FD)==0)?E(_Fy):E(_uD):E(_Fz);}else{var _FE=I_compareInt(_FC.a,0);return (_FE<=0)?(E(_FE)==0)?E(_Fy):E(_Fz):E(_uD);}},_FF=function(_FG,_FH,_FI){while(1){var _FJ=E(_FI);if(!_FJ._){if(!B(_Fm(_FG,_v8))){return new T2(0,B(_pg(_FH,B(_Fu(_uT,_FG)))),_oD);}else{var _FK=B(_Fu(_uT,B(_uP(_FG))));return new F(function(){return _EW(B(_pg(_FH,B(_FA(_FK)))),B(_EG(_FK)));});}}else{var _FL=B(_F1(_FG,_Fx)),_FM=B(_uF(B(_pg(_FH,_uT)),B(_oz(E(_FJ.a)))));_FG=_FL;_FH=_FM;_FI=_FJ.b;continue;}}},_FN=function(_FO,_FP){var _FQ=E(_FO);if(!_FQ._){var _FR=_FQ.a,_FS=E(_FP);return (_FS._==0)?_FR>=_FS.a:I_compareInt(_FS.a,_FR)<=0;}else{var _FT=_FQ.a,_FU=E(_FP);return (_FU._==0)?I_compareInt(_FT,_FU.a)>=0:I_compare(_FT,_FU.a)>=0;}},_FV=function(_FW){var _FX=E(_FW);if(!_FX._){var _FY=_FX.b;return new F(function(){return _EW(B(_pg(B(_v9(new T(function(){return B(_oz(E(_FX.a)));}),new T(function(){return B(_uU(_FY,0));},1),B(_G(_uZ,_FY)))),_Fx)),_Fx);});}else{var _FZ=_FX.a,_G0=_FX.c,_G1=E(_FX.b);if(!_G1._){var _G2=E(_G0);if(!_G2._){return new F(function(){return _EW(B(_pg(B(_vq(_uT,_FZ)),_Fx)),_Fx);});}else{var _G3=_G2.a;if(!B(_FN(_G3,_v8))){var _G4=B(_Fu(_uT,B(_uP(_G3))));return new F(function(){return _EW(B(_pg(B(_vq(_uT,_FZ)),B(_FA(_G4)))),B(_EG(_G4)));});}else{return new F(function(){return _EW(B(_pg(B(_pg(B(_vq(_uT,_FZ)),B(_Fu(_uT,_G3)))),_Fx)),_Fx);});}}}else{var _G5=_G1.a,_G6=E(_G0);if(!_G6._){return new F(function(){return _FF(_v8,B(_vq(_uT,_FZ)),_G5);});}else{return new F(function(){return _FF(_G6.a,B(_vq(_uT,_FZ)),_G5);});}}}},_G7=function(_G8,_G9){while(1){var _Ga=E(_G9);if(!_Ga._){return __Z;}else{if(!B(A1(_G8,_Ga.a))){return E(_Ga);}else{_G9=_Ga.b;continue;}}}},_Gb=function(_Gc,_Gd){var _Ge=E(_Gc);if(!_Ge._){var _Gf=_Ge.a,_Gg=E(_Gd);return (_Gg._==0)?_Gf>_Gg.a:I_compareInt(_Gg.a,_Gf)<0;}else{var _Gh=_Ge.a,_Gi=E(_Gd);return (_Gi._==0)?I_compareInt(_Gh,_Gi.a)>0:I_compare(_Gh,_Gi.a)>0;}},_Gj=0,_Gk=function(_Gl){return new F(function(){return _iV(_Gj,_Gl);});},_Gm=new T2(0,E(_v8),E(_oD)),_Gn=new T1(1,_Gm),_Go=new T1(0,-2147483648),_Gp=new T1(0,2147483647),_Gq=function(_Gr,_Gs,_Gt){var _Gu=E(_Gt);if(!_Gu._){return new T1(1,new T(function(){var _Gv=B(_FV(_Gu));return new T2(0,E(_Gv.a),E(_Gv.b));}));}else{var _Gw=E(_Gu.c);if(!_Gw._){return new T1(1,new T(function(){var _Gx=B(_FV(_Gu));return new T2(0,E(_Gx.a),E(_Gx.b));}));}else{var _Gy=_Gw.a;if(!B(_Gb(_Gy,_Gp))){if(!B(_Fm(_Gy,_Go))){var _Gz=function(_GA){var _GB=_GA+B(_oP(_Gy))|0;return (_GB<=(E(_Gs)+3|0))?(_GB>=(E(_Gr)-3|0))?new T1(1,new T(function(){var _GC=B(_FV(_Gu));return new T2(0,E(_GC.a),E(_GC.b));})):E(_Gn):__Z;},_GD=B(_G7(_Gk,_Gu.a));if(!_GD._){var _GE=E(_Gu.b);if(!_GE._){return E(_Gn);}else{var _GF=B(_6T(_Gk,_GE.a));if(!E(_GF.b)._){return E(_Gn);}else{return new F(function(){return _Gz( -B(_uU(_GF.a,0)));});}}}else{return new F(function(){return _Gz(B(_uU(_GD,0)));});}}else{return __Z;}}else{return __Z;}}}},_GG=function(_GH,_GI){return new T0(2);},_GJ=new T1(0,1),_GK=function(_GL,_GM){var _GN=E(_GL);if(!_GN._){var _GO=_GN.a,_GP=E(_GM);if(!_GP._){var _GQ=_GP.a;return (_GO!=_GQ)?(_GO>_GQ)?2:0:1;}else{var _GR=I_compareInt(_GP.a,_GO);return (_GR<=0)?(_GR>=0)?1:2:0;}}else{var _GS=_GN.a,_GT=E(_GM);if(!_GT._){var _GU=I_compareInt(_GS,_GT.a);return (_GU>=0)?(_GU<=0)?1:2:0;}else{var _GV=I_compare(_GS,_GT.a);return (_GV>=0)?(_GV<=0)?1:2:0;}}},_GW=function(_GX,_GY){while(1){var _GZ=E(_GX);if(!_GZ._){_GX=new T1(1,I_fromInt(_GZ.a));continue;}else{return new T1(1,I_shiftLeft(_GZ.a,_GY));}}},_H0=function(_H1,_H2,_H3){if(!B(_qE(_H3,_qW))){var _H4=B(_qM(_H2,_H3)),_H5=_H4.a;switch(B(_GK(B(_GW(_H4.b,1)),_H3))){case 0:return new F(function(){return _qA(_H5,_H1);});break;case 1:if(!(B(_oP(_H5))&1)){return new F(function(){return _qA(_H5,_H1);});}else{return new F(function(){return _qA(B(_uF(_H5,_GJ)),_H1);});}break;default:return new F(function(){return _qA(B(_uF(_H5,_GJ)),_H1);});}}else{return E(_nC);}},_H6=function(_H7){var _H8=function(_H9,_Ha){while(1){if(!B(_Fm(_H9,_H7))){if(!B(_Gb(_H9,_H7))){if(!B(_qE(_H9,_H7))){return new F(function(){return _7f("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_Ha);}}else{return _Ha-1|0;}}else{var _Hb=B(_GW(_H9,1)),_Hc=_Ha+1|0;_H9=_Hb;_Ha=_Hc;continue;}}};return new F(function(){return _H8(_uD,0);});},_Hd=function(_He){var _Hf=E(_He);if(!_Hf._){var _Hg=_Hf.a>>>0;if(!_Hg){return -1;}else{var _Hh=function(_Hi,_Hj){while(1){if(_Hi>=_Hg){if(_Hi<=_Hg){if(_Hi!=_Hg){return new F(function(){return _7f("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_Hj);}}else{return _Hj-1|0;}}else{var _Hk=imul(_Hi,2)>>>0,_Hl=_Hj+1|0;_Hi=_Hk;_Hj=_Hl;continue;}}};return new F(function(){return _Hh(1,0);});}}else{return new F(function(){return _H6(_Hf);});}},_Hm=function(_Hn){var _Ho=E(_Hn);if(!_Ho._){var _Hp=_Ho.a>>>0;if(!_Hp){return new T2(0,-1,0);}else{var _Hq=function(_Hr,_Hs){while(1){if(_Hr>=_Hp){if(_Hr<=_Hp){if(_Hr!=_Hp){return new F(function(){return _7f("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_Hs);}}else{return _Hs-1|0;}}else{var _Ht=imul(_Hr,2)>>>0,_Hu=_Hs+1|0;_Hr=_Ht;_Hs=_Hu;continue;}}};return new T2(0,B(_Hq(1,0)),(_Hp&_Hp-1>>>0)>>>0&4294967295);}}else{var _Hv=_Ho.a;return new T2(0,B(_Hd(_Ho)),I_compareInt(I_and(_Hv,I_sub(_Hv,I_fromInt(1))),0));}},_Hw=function(_Hx,_Hy){while(1){var _Hz=E(_Hx);if(!_Hz._){var _HA=_Hz.a,_HB=E(_Hy);if(!_HB._){return new T1(0,(_HA>>>0&_HB.a>>>0)>>>0&4294967295);}else{_Hx=new T1(1,I_fromInt(_HA));_Hy=_HB;continue;}}else{var _HC=E(_Hy);if(!_HC._){_Hx=_Hz;_Hy=new T1(1,I_fromInt(_HC.a));continue;}else{return new T1(1,I_and(_Hz.a,_HC.a));}}}},_HD=new T1(0,2),_HE=function(_HF,_HG){var _HH=E(_HF);if(!_HH._){var _HI=(_HH.a>>>0&(2<<_HG>>>0)-1>>>0)>>>0,_HJ=1<<_HG>>>0;return (_HJ<=_HI)?(_HJ>=_HI)?1:2:0;}else{var _HK=B(_Hw(_HH,B(_F1(B(_GW(_HD,_HG)),_uD)))),_HL=B(_GW(_uD,_HG));return (!B(_Gb(_HL,_HK)))?(!B(_Fm(_HL,_HK)))?1:2:0;}},_HM=function(_HN,_HO){while(1){var _HP=E(_HN);if(!_HP._){_HN=new T1(1,I_fromInt(_HP.a));continue;}else{return new T1(1,I_shiftRight(_HP.a,_HO));}}},_HQ=function(_HR,_HS,_HT,_HU){var _HV=B(_Hm(_HU)),_HW=_HV.a;if(!E(_HV.b)){var _HX=B(_Hd(_HT));if(_HX<((_HW+_HR|0)-1|0)){var _HY=_HW+(_HR-_HS|0)|0;if(_HY>0){if(_HY>_HX){if(_HY<=(_HX+1|0)){if(!E(B(_Hm(_HT)).b)){return 0;}else{return new F(function(){return _qA(_GJ,_HR-_HS|0);});}}else{return 0;}}else{var _HZ=B(_HM(_HT,_HY));switch(B(_HE(_HT,_HY-1|0))){case 0:return new F(function(){return _qA(_HZ,_HR-_HS|0);});break;case 1:if(!(B(_oP(_HZ))&1)){return new F(function(){return _qA(_HZ,_HR-_HS|0);});}else{return new F(function(){return _qA(B(_uF(_HZ,_GJ)),_HR-_HS|0);});}break;default:return new F(function(){return _qA(B(_uF(_HZ,_GJ)),_HR-_HS|0);});}}}else{return new F(function(){return _qA(_HT,(_HR-_HS|0)-_HY|0);});}}else{if(_HX>=_HS){var _I0=B(_HM(_HT,(_HX+1|0)-_HS|0));switch(B(_HE(_HT,_HX-_HS|0))){case 0:return new F(function(){return _qA(_I0,((_HX-_HW|0)+1|0)-_HS|0);});break;case 2:return new F(function(){return _qA(B(_uF(_I0,_GJ)),((_HX-_HW|0)+1|0)-_HS|0);});break;default:if(!(B(_oP(_I0))&1)){return new F(function(){return _qA(_I0,((_HX-_HW|0)+1|0)-_HS|0);});}else{return new F(function(){return _qA(B(_uF(_I0,_GJ)),((_HX-_HW|0)+1|0)-_HS|0);});}}}else{return new F(function(){return _qA(_HT, -_HW);});}}}else{var _I1=B(_Hd(_HT))-_HW|0,_I2=function(_I3){var _I4=function(_I5,_I6){if(!B(_wi(B(_GW(_I6,_HS)),_I5))){return new F(function(){return _H0(_I3-_HS|0,_I5,_I6);});}else{return new F(function(){return _H0((_I3-_HS|0)+1|0,_I5,B(_GW(_I6,1)));});}};if(_I3>=_HS){if(_I3!=_HS){return new F(function(){return _I4(_HT,new T(function(){return B(_GW(_HU,_I3-_HS|0));}));});}else{return new F(function(){return _I4(_HT,_HU);});}}else{return new F(function(){return _I4(new T(function(){return B(_GW(_HT,_HS-_I3|0));}),_HU);});}};if(_HR>_I1){return new F(function(){return _I2(_HR);});}else{return new F(function(){return _I2(_I1);});}}},_I7=new T(function(){return 0/0;}),_I8=new T(function(){return -1/0;}),_I9=new T(function(){return 1/0;}),_Ia=function(_Ib,_Ic){if(!B(_qE(_Ic,_qW))){if(!B(_qE(_Ib,_qW))){if(!B(_Fm(_Ib,_qW))){return new F(function(){return _HQ(-1021,53,_Ib,_Ic);});}else{return  -B(_HQ(-1021,53,B(_uP(_Ib)),_Ic));}}else{return E(_qV);}}else{return (!B(_qE(_Ib,_qW)))?(!B(_Fm(_Ib,_qW)))?E(_I9):E(_I8):E(_I7);}},_Id=function(_Ie){var _If=E(_Ie);switch(_If._){case 3:var _Ig=_If.a;return (!B(_sf(_Ig,_En)))?(!B(_sf(_Ig,_Em)))?E(_GG):E(_Ej):E(_Ef);case 5:var _Ih=B(_Gq(_Ep,_Eo,_If.a));if(!_Ih._){return E(_Ef);}else{var _Ii=new T(function(){var _Ij=E(_Ih.a);return B(_Ia(_Ij.a,_Ij.b));});return function(_Ik,_Il){return new F(function(){return A1(_Il,_Ii);});};}break;default:return E(_GG);}},_Im=function(_In){var _Io=function(_Ip){return E(new T2(3,_In,_sL));};return new T1(1,function(_Iq){return new F(function(){return A2(_By,_Iq,_Io);});});},_Ir=new T(function(){return B(A3(_DT,_Id,_Do,_Im));}),_Is=new T(function(){return B(_rr(_Ir,_rp));}),_It=function(_Iu){while(1){var _Iv=B((function(_Iw){var _Ix=E(_Iw);if(!_Ix._){return __Z;}else{var _Iy=_Ix.b,_Iz=E(_Ix.a);if(!E(_Iz.b)._){return new T2(1,_Iz.a,new T(function(){return B(_It(_Iy));}));}else{_Iu=_Iy;return __continue;}}})(_Iu));if(_Iv!=__continue){return _Iv;}}},_IA=new T(function(){return B(_It(_Is));}),_IB=new T(function(){return B(unCStr("Infinity"));}),_IC=new T(function(){return B(_rr(_Ir,_IB));}),_ID=new T(function(){return B(_It(_IC));}),_IE=0,_IF=function(_IG,_IH,_II){return new F(function(){return _eR(_e4,new T2(0,_IH,_II),_IG,_eW);});},_IJ=function(_IK,_IL,_IM){var _IN=(_IK+_IL|0)-1|0;if(_IK<=_IN){var _IO=function(_IP){return new T2(1,new T(function(){var _IQ=E(_IM),_IR=_IQ.c,_IS=E(_IQ.a),_IT=E(_IQ.b);if(_IS>_IP){return B(_IF(_IP,_IS,_IT));}else{if(_IP>_IT){return B(_IF(_IP,_IS,_IT));}else{var _IU=_IP-_IS|0;if(0>_IU){return B(_dN(_IU,_IR));}else{if(_IU>=_IR){return B(_dN(_IU,_IR));}else{return _IQ.d["v"]["w8"][_IU];}}}}}),new T(function(){if(_IP!=_IN){return B(_IO(_IP+1|0));}else{return __Z;}}));};return new F(function(){return _IO(_IK);});}else{return __Z;}},_IV=function(_IW){var _IX=E(_IW);return new F(function(){return _IJ(_IX.a,_IX.b,_IX.c);});},_IY=function(_IZ,_J0,_J1,_J2){var _J3=new T(function(){var _J4=E(_IZ),_J5=E(_J1),_J6=_J5.a,_J7=_J5.b,_J8=_J5.c,_J9=E(_J2);if((_J9+_J4|0)<=_J7){return new T2(0,new T(function(){var _Ja=_J7-_J9|0;if(_J4>_Ja){return new T3(0,_J6+_J9|0,_Ja,_J8);}else{return new T3(0,_J6+_J9|0,_J4,_J8);}}),_J9+_J4|0);}else{return E(_fs);}}),_Jb=new T(function(){return B(A1(_J0,new T(function(){return B(_IV(E(_J3).a));})));}),_Jc=new T(function(){var _Jd=E(_Jb),_Je=_Jd.d,_Jf=_Jd.e,_Jg=_Jd.f,_Jh=E(_Jd.c);if(!_Jh){if(!B(_qE(_Je,_rj))){var _Ji=B(_qX(_p6,Math.pow(2,E(_Jf)-1|0))),_Jj=_Ji.a;if(E(_Ji.b)>=0){return B(_qA(_Je,((1-E(_Jj)|0)-E(_Jg)|0)+1|0));}else{return B(_qA(_Je,((1-(E(_Jj)-1|0)|0)-E(_Jg)|0)+1|0));}}else{return E(_IE);}}else{var _Jk=E(_Jf);if(_Jh!=(B(_rd(_ro,_Jk))-1|0)){var _Jl=B(_qX(_p6,Math.pow(2,_Jk-1|0))),_Jm=_Jl.a;if(E(_Jl.b)>=0){var _Jn=E(_Jg);return B(_qA(B(_uF(_Je,B(_GW(_ri,_Jn)))),((_Jh+1|0)-E(_Jm)|0)-_Jn|0));}else{var _Jo=E(_Jg);return B(_qA(B(_uF(_Je,B(_GW(_ri,_Jo)))),((_Jh+1|0)-(E(_Jm)-1|0)|0)-_Jo|0));}}else{if(!B(_qE(_Je,_rj))){var _Jp=E(_IA);if(!_Jp._){return E(_rl);}else{if(!E(_Jp.b)._){return E(_Jp.a);}else{return E(_rn);}}}else{var _Jq=E(_ID);if(!_Jq._){return E(_rl);}else{if(!E(_Jq.b)._){return E(_Jq.a);}else{return E(_rn);}}}}}});return new T2(0,new T(function(){if(!E(E(_Jb).b)){return E(_Jc);}else{return  -E(_Jc);}}),new T(function(){return E(E(_J3).b);}));},_Jr=new T(function(){return B(unCStr("This file was compiled with different version of GF"));}),_Js=new T(function(){return B(err(_Jr));}),_Jt=8,_Ju={_:0,a:_mY,b:_mT,c:_mP,d:_mP,e:_mj,f:_mE,g:_iE,h:_mL},_Jv={_:0,a:_oJ,b:_iP,c:_oG,d:_oU,e:_oM,f:_oZ,g:_oS},_Jw=new T2(0,_iV,_iY),_Jx={_:0,a:_Jw,b:_jf,c:_jr,d:_jo,e:_jl,f:_ji,g:_j2,h:_j7},_Jy=new T3(0,_Jv,_Jx,_oE),_Jz={_:0,a:_Jy,b:_Ju,c:_oh,d:_ov,e:_nL,f:_od,g:_on,h:_nQ,i:_oB},_JA=new T1(0,1),_JB=function(_JC,_JD){var _JE=E(_JC);return new T2(0,_JE,new T(function(){var _JF=B(_JB(B(_uF(_JE,_JD)),_JD));return new T2(1,_JF.a,_JF.b);}));},_JG=function(_JH){var _JI=B(_JB(_JH,_JA));return new T2(1,_JI.a,_JI.b);},_JJ=function(_JK,_JL){var _JM=B(_JB(_JK,new T(function(){return B(_F1(_JL,_JK));})));return new T2(1,_JM.a,_JM.b);},_JN=new T1(0,0),_JO=function(_JP,_JQ,_JR){if(!B(_FN(_JQ,_JN))){var _JS=function(_JT){return (!B(_Fm(_JT,_JR)))?new T2(1,_JT,new T(function(){return B(_JS(B(_uF(_JT,_JQ))));})):__Z;};return new F(function(){return _JS(_JP);});}else{var _JU=function(_JV){return (!B(_Gb(_JV,_JR)))?new T2(1,_JV,new T(function(){return B(_JU(B(_uF(_JV,_JQ))));})):__Z;};return new F(function(){return _JU(_JP);});}},_JW=function(_JX,_JY,_JZ){return new F(function(){return _JO(_JX,B(_F1(_JY,_JX)),_JZ);});},_K0=function(_K1,_K2){return new F(function(){return _JO(_K1,_JA,_K2);});},_K3=function(_K4){return new F(function(){return _oP(_K4);});},_K5=function(_K6){return new F(function(){return _F1(_K6,_JA);});},_K7=function(_K8){return new F(function(){return _uF(_K8,_JA);});},_K9=function(_Ka){return new F(function(){return _oz(E(_Ka));});},_Kb={_:0,a:_K7,b:_K5,c:_K9,d:_K3,e:_JG,f:_JJ,g:_K0,h:_JW},_Kc=function(_Kd,_Ke){while(1){var _Kf=E(_Kd);if(!_Kf._){var _Kg=E(_Kf.a);if(_Kg==(-2147483648)){_Kd=new T1(1,I_fromInt(-2147483648));continue;}else{var _Kh=E(_Ke);if(!_Kh._){return new T1(0,B(_n2(_Kg,_Kh.a)));}else{_Kd=new T1(1,I_fromInt(_Kg));_Ke=_Kh;continue;}}}else{var _Ki=_Kf.a,_Kj=E(_Ke);return (_Kj._==0)?new T1(1,I_div(_Ki,I_fromInt(_Kj.a))):new T1(1,I_div(_Ki,_Kj.a));}}},_Kk=function(_Kl,_Km){if(!B(_qE(_Km,_pO))){return new F(function(){return _Kc(_Kl,_Km);});}else{return E(_nC);}},_Kn=function(_Ko,_Kp){while(1){var _Kq=E(_Ko);if(!_Kq._){var _Kr=E(_Kq.a);if(_Kr==(-2147483648)){_Ko=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ks=E(_Kp);if(!_Ks._){var _Kt=_Ks.a;return new T2(0,new T1(0,B(_n2(_Kr,_Kt))),new T1(0,B(_o6(_Kr,_Kt))));}else{_Ko=new T1(1,I_fromInt(_Kr));_Kp=_Ks;continue;}}}else{var _Ku=E(_Kp);if(!_Ku._){_Ko=_Kq;_Kp=new T1(1,I_fromInt(_Ku.a));continue;}else{var _Kv=I_divMod(_Kq.a,_Ku.a);return new T2(0,new T1(1,_Kv.a),new T1(1,_Kv.b));}}}},_Kw=function(_Kx,_Ky){if(!B(_qE(_Ky,_pO))){var _Kz=B(_Kn(_Kx,_Ky));return new T2(0,_Kz.a,_Kz.b);}else{return E(_nC);}},_KA=function(_KB,_KC){while(1){var _KD=E(_KB);if(!_KD._){var _KE=E(_KD.a);if(_KE==(-2147483648)){_KB=new T1(1,I_fromInt(-2147483648));continue;}else{var _KF=E(_KC);if(!_KF._){return new T1(0,B(_o6(_KE,_KF.a)));}else{_KB=new T1(1,I_fromInt(_KE));_KC=_KF;continue;}}}else{var _KG=_KD.a,_KH=E(_KC);return (_KH._==0)?new T1(1,I_mod(_KG,I_fromInt(_KH.a))):new T1(1,I_mod(_KG,_KH.a));}}},_KI=function(_KJ,_KK){if(!B(_qE(_KK,_pO))){return new F(function(){return _KA(_KJ,_KK);});}else{return E(_nC);}},_KL=function(_KM,_KN){if(!B(_qE(_KN,_pO))){return new F(function(){return _EL(_KM,_KN);});}else{return E(_nC);}},_KO=function(_KP,_KQ){if(!B(_qE(_KQ,_pO))){var _KR=B(_qM(_KP,_KQ));return new T2(0,_KR.a,_KR.b);}else{return E(_nC);}},_KS=function(_KT){return E(_KT);},_KU=function(_KV){return E(_KV);},_KW={_:0,a:_uF,b:_F1,c:_pg,d:_uP,e:_EG,f:_FA,g:_KU},_KX=function(_KY,_KZ){var _L0=E(_KY);if(!_L0._){var _L1=_L0.a,_L2=E(_KZ);return (_L2._==0)?_L1!=_L2.a:(I_compareInt(_L2.a,_L1)==0)?false:true;}else{var _L3=_L0.a,_L4=E(_KZ);return (_L4._==0)?(I_compareInt(_L3,_L4.a)==0)?false:true:(I_compare(_L3,_L4.a)==0)?false:true;}},_L5=new T2(0,_qE,_KX),_L6=function(_L7,_L8){return (!B(_wi(_L7,_L8)))?E(_L7):E(_L8);},_L9=function(_La,_Lb){return (!B(_wi(_La,_Lb)))?E(_Lb):E(_La);},_Lc={_:0,a:_L5,b:_GK,c:_Fm,d:_wi,e:_Gb,f:_FN,g:_L6,h:_L9},_Ld=function(_Le){return new T2(0,E(_Le),E(_oD));},_Lf=new T3(0,_KW,_Lc,_Ld),_Lg={_:0,a:_Lf,b:_Kb,c:_KL,d:_Ey,e:_Kk,f:_KI,g:_KO,h:_Kw,i:_KS},_Lh=function(_Li,_Lj){while(1){var _Lk=E(_Li);if(!_Lk._){return E(_Lj);}else{var _Ll=B(_uF(B(_GW(_Lj,8)),B(_oz(E(_Lk.a)&4294967295))));_Li=_Lk.b;_Lj=_Ll;continue;}}},_Lm=function(_Ln,_Lo,_Lp){var _Lq=imul(B(_uU(_Ln,0)),8)|0,_Lr=B(_qX(_Lg,Math.pow(2,_Lq-_Lo|0))),_Ls=_Lr.a;return (E(_Lr.b)>=0)?E(B(_HM(B(_Hw(B(_Lh(_Ln,_rj)),B(_F1(_Ls,_ri)))),_Lq-_Lp|0)).a):E(B(_HM(B(_Hw(B(_Lh(_Ln,_rj)),B(_F1(B(_F1(_Ls,_ri)),_ri)))),_Lq-_Lp|0)).a);},_Lt=new T(function(){return B(unCStr("head"));}),_Lu=new T(function(){return B(_ec(_Lt));}),_Lv=function(_Lw,_Lx,_Ly){return new T1(1,B(_Lm(_Lw,E(_Lx),E(_Ly))));},_Lz=5,_LA=new T(function(){return B(unCStr("Invalid length of floating-point value"));}),_LB=new T(function(){return B(err(_LA));}),_LC=function(_LD){var _LE=new T(function(){return imul(B(_uU(_LD,0)),8)|0;}),_LF=new T(function(){var _LG=E(_LE);switch(_LG){case 16:return E(_Lz);break;case 32:return E(_Jt);break;default:if(!B(_o6(_LG,32))){var _LH=B(_qX(_Jz,4*(Math.log(_LG)/Math.log(2)))),_LI=_LH.a;if(E(_LH.b)<=0){return E(_LI)-13|0;}else{return (E(_LI)+1|0)-13|0;}}else{return E(_LB);}}}),_LJ=new T(function(){return 1+E(_LF)|0;});return new T6(0,new T(function(){return B(_uU(_LD,0));}),new T(function(){var _LK=E(_LD);if(!_LK._){return E(_Lu);}else{if((E(_LK.a)&128)>>>0==128){return 1;}else{return 0;}}}),new T(function(){return B(_oP(new T1(1,B(_Lm(_LD,1,E(_LJ))))));}),new T(function(){return B(_Lv(_LD,_LJ,_LE));}),_LF,new T(function(){return B(_iP(_LE,_LJ));}));},_LL=function(_LM){var _LN=B(_LC(_LM));return new T6(0,_LN.a,_LN.b,_LN.c,_LN.d,_LN.e,_LN.f);},_LO=function(_LP,_LQ,_LR,_LS){var _LT=B(_fc(_LP,_LQ,_LR,_LS)),_LU=_LT.b;switch(E(_LT.a)){case 0:var _LV=B(_fi(_LP,_LQ,_LR,E(_LU))),_LW=B(_gf(E(_LV.a)&4294967295,_g3,new T3(0,_LP,_LQ,_LR),_LV.b));return new T2(0,new T1(0,_LW.a),_LW.b);case 1:var _LX=B(_fi(_LP,_LQ,_LR,E(_LU)));return new T2(0,new T1(1,new T(function(){return E(_LX.a)&4294967295;})),_LX.b);case 2:var _LY=B(_IY(_Jt,_LL,new T3(0,_LP,_LQ,_LR),_LU));return new T2(0,new T1(2,_LY.a),_LY.b);default:return E(_Js);}},_LZ=function(_M0,_M1){var _M2=E(_M0),_M3=B(_LO(_M2.a,_M2.b,_M2.c,E(_M1)));return new T2(0,_M3.a,_M3.b);},_M4=function(_M5){switch(E(_M5)._){case 0:return E(_dJ);case 1:return E(_dJ);default:return E(_dJ);}},_M6=new T2(0,_M4,_LZ),_M7=function(_M8){return E(_dJ);},_M9=-4,_Ma=function(_Mb){var _Mc=E(_Mb);return (_Mc._==0)?__Z:new T2(1,new T2(0,_M9,_Mc.a),new T(function(){return B(_Ma(_Mc.b));}));},_Md=function(_Me,_Mf,_Mg,_Mh){var _Mi=B(_fi(_Me,_Mf,_Mg,_Mh)),_Mj=B(_gf(E(_Mi.a)&4294967295,_kp,new T3(0,_Me,_Mf,_Mg),_Mi.b)),_Mk=B(_fi(_Me,_Mf,_Mg,E(_Mj.b))),_Ml=new T(function(){return new T2(0,new T(function(){return B(_Ma(_Mj.a));}),E(_Mk.a)&4294967295);});return new T2(0,_Ml,_Mk.b);},_Mm=function(_Mn,_Mo){var _Mp=E(_Mn),_Mq=B(_Md(_Mp.a,_Mp.b,_Mp.c,E(_Mo)));return new T2(0,_Mq.a,_Mq.b);},_Mr=function(_Ms,_Mt,_Mu,_Mv){var _Mw=B(_fc(_Ms,_Mt,_Mu,_Mv)),_Mx=_Mw.b;switch(E(_Mw.a)){case 0:var _My=B(_fi(_Ms,_Mt,_Mu,E(_Mx))),_Mz=B(_fi(_Ms,_Mt,_Mu,E(_My.b))),_MA=B(_gf(E(_Mz.a)&4294967295,_Mm,new T3(0,_Ms,_Mt,_Mu),_Mz.b));return new T2(0,new T(function(){return new T2(0,E(_My.a)&4294967295,_MA.a);}),_MA.b);case 1:var _MB=B(_fi(_Ms,_Mt,_Mu,E(_Mx)));return new T2(0,new T(function(){return new T1(1,E(_MB.a)&4294967295);}),_MB.b);default:return E(_Js);}},_MC=function(_MD,_ME){var _MF=E(_MD),_MG=B(_Mr(_MF.a,_MF.b,_MF.c,E(_ME)));return new T2(0,_MG.a,_MG.b);},_MH=new T(function(){return B(_7f("pgf/PGF/Binary.hs:(243,3)-(244,51)|function put"));}),_MI=function(_MJ){switch(E(_MJ)._){case 0:return E(_dJ);case 1:return E(_dJ);default:return E(_MH);}},_MK=new T2(0,_MI,_MC),_ML=new T0(1),_MM=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_MN=function(_MO){return new F(function(){return err(_MM);});},_MP=new T(function(){return B(_MN(_));}),_MQ=function(_MR,_MS,_MT){var _MU=E(_MT);if(!_MU._){var _MV=_MU.a,_MW=E(_MS);if(!_MW._){var _MX=_MW.a,_MY=_MW.b;if(_MX<=(imul(3,_MV)|0)){return new T4(0,(1+_MX|0)+_MV|0,E(_MR),E(_MW),E(_MU));}else{var _MZ=E(_MW.c);if(!_MZ._){var _N0=_MZ.a,_N1=E(_MW.d);if(!_N1._){var _N2=_N1.a,_N3=_N1.b,_N4=_N1.c;if(_N2>=(imul(2,_N0)|0)){var _N5=function(_N6){var _N7=E(_N1.d);return (_N7._==0)?new T4(0,(1+_MX|0)+_MV|0,E(_N3),E(new T4(0,(1+_N0|0)+_N6|0,E(_MY),E(_MZ),E(_N4))),E(new T4(0,(1+_MV|0)+_N7.a|0,E(_MR),E(_N7),E(_MU)))):new T4(0,(1+_MX|0)+_MV|0,E(_N3),E(new T4(0,(1+_N0|0)+_N6|0,E(_MY),E(_MZ),E(_N4))),E(new T4(0,1+_MV|0,E(_MR),E(_ML),E(_MU))));},_N8=E(_N4);if(!_N8._){return new F(function(){return _N5(_N8.a);});}else{return new F(function(){return _N5(0);});}}else{return new T4(0,(1+_MX|0)+_MV|0,E(_MY),E(_MZ),E(new T4(0,(1+_MV|0)+_N2|0,E(_MR),E(_N1),E(_MU))));}}else{return E(_MP);}}else{return E(_MP);}}}else{return new T4(0,1+_MV|0,E(_MR),E(_ML),E(_MU));}}else{var _N9=E(_MS);if(!_N9._){var _Na=_N9.a,_Nb=_N9.b,_Nc=_N9.d,_Nd=E(_N9.c);if(!_Nd._){var _Ne=_Nd.a,_Nf=E(_Nc);if(!_Nf._){var _Ng=_Nf.a,_Nh=_Nf.b,_Ni=_Nf.c;if(_Ng>=(imul(2,_Ne)|0)){var _Nj=function(_Nk){var _Nl=E(_Nf.d);return (_Nl._==0)?new T4(0,1+_Na|0,E(_Nh),E(new T4(0,(1+_Ne|0)+_Nk|0,E(_Nb),E(_Nd),E(_Ni))),E(new T4(0,1+_Nl.a|0,E(_MR),E(_Nl),E(_ML)))):new T4(0,1+_Na|0,E(_Nh),E(new T4(0,(1+_Ne|0)+_Nk|0,E(_Nb),E(_Nd),E(_Ni))),E(new T4(0,1,E(_MR),E(_ML),E(_ML))));},_Nm=E(_Ni);if(!_Nm._){return new F(function(){return _Nj(_Nm.a);});}else{return new F(function(){return _Nj(0);});}}else{return new T4(0,1+_Na|0,E(_Nb),E(_Nd),E(new T4(0,1+_Ng|0,E(_MR),E(_Nf),E(_ML))));}}else{return new T4(0,3,E(_Nb),E(_Nd),E(new T4(0,1,E(_MR),E(_ML),E(_ML))));}}else{var _Nn=E(_Nc);return (_Nn._==0)?new T4(0,3,E(_Nn.b),E(new T4(0,1,E(_Nb),E(_ML),E(_ML))),E(new T4(0,1,E(_MR),E(_ML),E(_ML)))):new T4(0,2,E(_MR),E(_N9),E(_ML));}}else{return new T4(0,1,E(_MR),E(_ML),E(_ML));}}},_No=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_Np=function(_Nq){return new F(function(){return err(_No);});},_Nr=new T(function(){return B(_Np(_));}),_Ns=function(_Nt,_Nu,_Nv){var _Nw=E(_Nu);if(!_Nw._){var _Nx=_Nw.a,_Ny=E(_Nv);if(!_Ny._){var _Nz=_Ny.a,_NA=_Ny.b;if(_Nz<=(imul(3,_Nx)|0)){return new T4(0,(1+_Nx|0)+_Nz|0,E(_Nt),E(_Nw),E(_Ny));}else{var _NB=E(_Ny.c);if(!_NB._){var _NC=_NB.a,_ND=_NB.b,_NE=_NB.c,_NF=E(_Ny.d);if(!_NF._){var _NG=_NF.a;if(_NC>=(imul(2,_NG)|0)){var _NH=function(_NI){var _NJ=E(_Nt),_NK=E(_NB.d);return (_NK._==0)?new T4(0,(1+_Nx|0)+_Nz|0,E(_ND),E(new T4(0,(1+_Nx|0)+_NI|0,E(_NJ),E(_Nw),E(_NE))),E(new T4(0,(1+_NG|0)+_NK.a|0,E(_NA),E(_NK),E(_NF)))):new T4(0,(1+_Nx|0)+_Nz|0,E(_ND),E(new T4(0,(1+_Nx|0)+_NI|0,E(_NJ),E(_Nw),E(_NE))),E(new T4(0,1+_NG|0,E(_NA),E(_ML),E(_NF))));},_NL=E(_NE);if(!_NL._){return new F(function(){return _NH(_NL.a);});}else{return new F(function(){return _NH(0);});}}else{return new T4(0,(1+_Nx|0)+_Nz|0,E(_NA),E(new T4(0,(1+_Nx|0)+_NC|0,E(_Nt),E(_Nw),E(_NB))),E(_NF));}}else{return E(_Nr);}}else{return E(_Nr);}}}else{return new T4(0,1+_Nx|0,E(_Nt),E(_Nw),E(_ML));}}else{var _NM=E(_Nv);if(!_NM._){var _NN=_NM.a,_NO=_NM.b,_NP=_NM.d,_NQ=E(_NM.c);if(!_NQ._){var _NR=_NQ.a,_NS=_NQ.b,_NT=_NQ.c,_NU=E(_NP);if(!_NU._){var _NV=_NU.a;if(_NR>=(imul(2,_NV)|0)){var _NW=function(_NX){var _NY=E(_Nt),_NZ=E(_NQ.d);return (_NZ._==0)?new T4(0,1+_NN|0,E(_NS),E(new T4(0,1+_NX|0,E(_NY),E(_ML),E(_NT))),E(new T4(0,(1+_NV|0)+_NZ.a|0,E(_NO),E(_NZ),E(_NU)))):new T4(0,1+_NN|0,E(_NS),E(new T4(0,1+_NX|0,E(_NY),E(_ML),E(_NT))),E(new T4(0,1+_NV|0,E(_NO),E(_ML),E(_NU))));},_O0=E(_NT);if(!_O0._){return new F(function(){return _NW(_O0.a);});}else{return new F(function(){return _NW(0);});}}else{return new T4(0,1+_NN|0,E(_NO),E(new T4(0,1+_NR|0,E(_Nt),E(_ML),E(_NQ))),E(_NU));}}else{return new T4(0,3,E(_NS),E(new T4(0,1,E(_Nt),E(_ML),E(_ML))),E(new T4(0,1,E(_NO),E(_ML),E(_ML))));}}else{var _O1=E(_NP);return (_O1._==0)?new T4(0,3,E(_NO),E(new T4(0,1,E(_Nt),E(_ML),E(_ML))),E(_O1)):new T4(0,2,E(_Nt),E(_ML),E(_NM));}}else{return new T4(0,1,E(_Nt),E(_ML),E(_ML));}}},_O2=function(_O3){return new T4(0,1,E(_O3),E(_ML),E(_ML));},_O4=function(_O5,_O6){var _O7=E(_O6);if(!_O7._){return new F(function(){return _MQ(_O7.b,B(_O4(_O5,_O7.c)),_O7.d);});}else{return new F(function(){return _O2(_O5);});}},_O8=function(_O9,_Oa){var _Ob=E(_Oa);if(!_Ob._){return new F(function(){return _Ns(_Ob.b,_Ob.c,B(_O8(_O9,_Ob.d)));});}else{return new F(function(){return _O2(_O9);});}},_Oc=function(_Od,_Oe,_Of,_Og,_Oh){return new F(function(){return _Ns(_Of,_Og,B(_O8(_Od,_Oh)));});},_Oi=function(_Oj,_Ok,_Ol,_Om,_On){return new F(function(){return _MQ(_Ol,B(_O4(_Oj,_Om)),_On);});},_Oo=function(_Op,_Oq,_Or,_Os,_Ot,_Ou){var _Ov=E(_Oq);if(!_Ov._){var _Ow=_Ov.a,_Ox=_Ov.b,_Oy=_Ov.c,_Oz=_Ov.d;if((imul(3,_Ow)|0)>=_Or){if((imul(3,_Or)|0)>=_Ow){return new T4(0,(_Ow+_Or|0)+1|0,E(_Op),E(_Ov),E(new T4(0,_Or,E(_Os),E(_Ot),E(_Ou))));}else{return new F(function(){return _Ns(_Ox,_Oy,B(_Oo(_Op,_Oz,_Or,_Os,_Ot,_Ou)));});}}else{return new F(function(){return _MQ(_Os,B(_OA(_Op,_Ow,_Ox,_Oy,_Oz,_Ot)),_Ou);});}}else{return new F(function(){return _Oi(_Op,_Or,_Os,_Ot,_Ou);});}},_OA=function(_OB,_OC,_OD,_OE,_OF,_OG){var _OH=E(_OG);if(!_OH._){var _OI=_OH.a,_OJ=_OH.b,_OK=_OH.c,_OL=_OH.d;if((imul(3,_OC)|0)>=_OI){if((imul(3,_OI)|0)>=_OC){return new T4(0,(_OC+_OI|0)+1|0,E(_OB),E(new T4(0,_OC,E(_OD),E(_OE),E(_OF))),E(_OH));}else{return new F(function(){return _Ns(_OD,_OE,B(_Oo(_OB,_OF,_OI,_OJ,_OK,_OL)));});}}else{return new F(function(){return _MQ(_OJ,B(_OA(_OB,_OC,_OD,_OE,_OF,_OK)),_OL);});}}else{return new F(function(){return _Oc(_OB,_OC,_OD,_OE,_OF);});}},_OM=function(_ON,_OO,_OP){var _OQ=E(_OO);if(!_OQ._){var _OR=_OQ.a,_OS=_OQ.b,_OT=_OQ.c,_OU=_OQ.d,_OV=E(_OP);if(!_OV._){var _OW=_OV.a,_OX=_OV.b,_OY=_OV.c,_OZ=_OV.d;if((imul(3,_OR)|0)>=_OW){if((imul(3,_OW)|0)>=_OR){return new T4(0,(_OR+_OW|0)+1|0,E(_ON),E(_OQ),E(_OV));}else{return new F(function(){return _Ns(_OS,_OT,B(_Oo(_ON,_OU,_OW,_OX,_OY,_OZ)));});}}else{return new F(function(){return _MQ(_OX,B(_OA(_ON,_OR,_OS,_OT,_OU,_OY)),_OZ);});}}else{return new F(function(){return _Oc(_ON,_OR,_OS,_OT,_OU);});}}else{return new F(function(){return _O4(_ON,_OP);});}},_P0=function(_P1,_P2,_P3){var _P4=E(_P1);if(_P4==1){return new T2(0,new T(function(){return new T4(0,1,E(_P2),E(_ML),E(_ML));}),_P3);}else{var _P5=B(_P0(_P4>>1,_P2,_P3)),_P6=_P5.a,_P7=E(_P5.b);if(!_P7._){return new T2(0,_P6,_4);}else{var _P8=B(_P9(_P4>>1,_P7.b));return new T2(0,new T(function(){return B(_OM(_P7.a,_P6,_P8.a));}),_P8.b);}}},_P9=function(_Pa,_Pb){var _Pc=E(_Pb);if(!_Pc._){return new T2(0,_ML,_4);}else{var _Pd=_Pc.a,_Pe=_Pc.b,_Pf=E(_Pa);if(_Pf==1){return new T2(0,new T(function(){return new T4(0,1,E(_Pd),E(_ML),E(_ML));}),_Pe);}else{var _Pg=B(_P0(_Pf>>1,_Pd,_Pe)),_Ph=_Pg.a,_Pi=E(_Pg.b);if(!_Pi._){return new T2(0,_Ph,_4);}else{var _Pj=B(_P9(_Pf>>1,_Pi.b));return new T2(0,new T(function(){return B(_OM(_Pi.a,_Ph,_Pj.a));}),_Pj.b);}}}},_Pk=function(_Pl,_Pm,_Pn){while(1){var _Po=E(_Pn);if(!_Po._){return E(_Pm);}else{var _Pp=B(_P9(_Pl,_Po.b)),_Pq=_Pl<<1,_Pr=B(_OM(_Po.a,_Pm,_Pp.a));_Pl=_Pq;_Pm=_Pr;_Pn=_Pp.b;continue;}}},_Ps=function(_Pt,_Pu,_Pv,_Pw,_Px){var _Py=B(_fi(_Pu,_Pv,_Pw,_Px)),_Pz=B(_gf(E(_Py.a)&4294967295,new T(function(){return B(_jL(_Pt));}),new T3(0,_Pu,_Pv,_Pw),_Py.b));return new T2(0,new T(function(){var _PA=E(_Pz.a);if(!_PA._){return new T0(1);}else{return B(_Pk(1,new T4(0,1,E(_PA.a),E(_ML),E(_ML)),_PA.b));}}),_Pz.b);},_PB=function(_PC,_PD){var _PE=E(_PC),_PF=B(_Ps(_MK,_PE.a,_PE.b,_PE.c,E(_PD)));return new T2(0,_PF.a,_PF.b);},_PG=new T2(0,_M7,_PB),_PH=function(_PI){return E(_dJ);},_PJ=function(_PK,_PL,_PM,_PN){var _PO=B(_fi(_PK,_PL,_PM,_PN));return new F(function(){return _gf(E(_PO.a)&4294967295,_kp,new T3(0,_PK,_PL,_PM),_PO.b);});},_PP=function(_PQ,_PR){var _PS=E(_PQ),_PT=B(_PJ(_PS.a,_PS.b,_PS.c,E(_PR)));return new T2(0,_PT.a,_PT.b);},_PU=new T2(0,_PH,_PP),_PV=new T0(1),_PW=function(_PX,_PY,_PZ,_Q0,_Q1,_Q2,_Q3){while(1){var _Q4=E(_Q3);if(!_Q4._){var _Q5=(_Q1>>>0^_Q4.a>>>0)>>>0,_Q6=(_Q5|_Q5>>>1)>>>0,_Q7=(_Q6|_Q6>>>2)>>>0,_Q8=(_Q7|_Q7>>>4)>>>0,_Q9=(_Q8|_Q8>>>8)>>>0,_Qa=(_Q9|_Q9>>>16)>>>0,_Qb=(_Qa^_Qa>>>1)>>>0&4294967295;if(_Q0>>>0<=_Qb>>>0){return new F(function(){return _Qc(_PX,_PY,_PZ,new T3(0,_Q1,E(_Q2),E(_Q4)));});}else{var _Qd=_Qb>>>0,_Qe=(_Q1>>>0&((_Qd-1>>>0^4294967295)>>>0^_Qd)>>>0)>>>0&4294967295,_Qf=new T4(0,_Qe,_Qb,E(_Q4.b),E(_Q2));_Q1=_Qe;_Q2=_Qf;_Q3=_Q4.c;continue;}}else{return new F(function(){return _Qc(_PX,_PY,_PZ,new T3(0,_Q1,E(_Q2),E(_PV)));});}}},_Qg=function(_Qh,_Qi,_Qj){while(1){var _Qk=E(_Qj);if(!_Qk._){var _Ql=_Qk.a,_Qm=_Qk.b,_Qn=_Qk.c,_Qo=(_Ql>>>0^_Qh>>>0)>>>0,_Qp=(_Qo|_Qo>>>1)>>>0,_Qq=(_Qp|_Qp>>>2)>>>0,_Qr=(_Qq|_Qq>>>4)>>>0,_Qs=(_Qr|_Qr>>>8)>>>0,_Qt=(_Qs|_Qs>>>16)>>>0,_Qu=(_Qt^_Qt>>>1)>>>0&4294967295,_Qv=(_Qh>>>0^_Ql>>>0)>>>0,_Qw=(_Qv|_Qv>>>1)>>>0,_Qx=(_Qw|_Qw>>>2)>>>0,_Qy=(_Qx|_Qx>>>4)>>>0,_Qz=(_Qy|_Qy>>>8)>>>0,_QA=(_Qz|_Qz>>>16)>>>0,_QB=(_QA^_QA>>>1)>>>0;if(!((_Ql>>>0&_Qu>>>0)>>>0)){var _QC=_Qu>>>0,_QD=(_Qh>>>0&((_QB-1>>>0^4294967295)>>>0^_QB)>>>0)>>>0&4294967295,_QE=new T4(0,(_Ql>>>0&((_QC-1>>>0^4294967295)>>>0^_QC)>>>0)>>>0&4294967295,_Qu,E(_Qm),E(_Qi));_Qh=_QD;_Qi=_QE;_Qj=_Qn;continue;}else{var _QF=_Qu>>>0,_QD=(_Qh>>>0&((_QB-1>>>0^4294967295)>>>0^_QB)>>>0)>>>0&4294967295,_QE=new T4(0,(_Ql>>>0&((_QF-1>>>0^4294967295)>>>0^_QF)>>>0)>>>0&4294967295,_Qu,E(_Qi),E(_Qm));_Qh=_QD;_Qi=_QE;_Qj=_Qn;continue;}}else{return E(_Qi);}}},_Qc=function(_QG,_QH,_QI,_QJ){var _QK=E(_QI);if(!_QK._){return new F(function(){return _Qg(_QG,new T2(1,_QG,_QH),_QJ);});}else{var _QL=E(_QK.a),_QM=E(_QL.a),_QN=(_QG>>>0^_QM>>>0)>>>0,_QO=(_QN|_QN>>>1)>>>0,_QP=(_QO|_QO>>>2)>>>0,_QQ=(_QP|_QP>>>4)>>>0,_QR=(_QQ|_QQ>>>8)>>>0,_QS=(_QR|_QR>>>16)>>>0;return new F(function(){return _PW(_QM,_QL.b,_QK.b,(_QS^_QS>>>1)>>>0&4294967295,_QG,new T2(1,_QG,_QH),_QJ);});}},_QT=function(_QU,_QV,_QW,_QX,_QY){var _QZ=B(_fi(_QV,_QW,_QX,_QY)),_R0=function(_R1,_R2){var _R3=E(_R1),_R4=B(_fi(_R3.a,_R3.b,_R3.c,E(_R2))),_R5=B(A3(_jL,_QU,_R3,_R4.b));return new T2(0,new T2(0,new T(function(){return E(_R4.a)&4294967295;}),_R5.a),_R5.b);},_R6=B(_gf(E(_QZ.a)&4294967295,_R0,new T3(0,_QV,_QW,_QX),_QZ.b));return new T2(0,new T(function(){var _R7=E(_R6.a);if(!_R7._){return new T0(2);}else{var _R8=E(_R7.a);return B(_Qc(E(_R8.a),_R8.b,_R7.b,_PV));}}),_R6.b);},_R9=function(_Ra,_Rb,_Rc,_Rd){var _Re=B(A3(_jL,_Ra,_Rc,_Rd)),_Rf=B(A3(_jL,_Rb,_Rc,_Re.b));return new T2(0,new T2(0,_Re.a,_Rf.a),_Rf.b);},_Rg=new T0(1),_Rh=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_Ri=function(_Rj){return new F(function(){return err(_Rh);});},_Rk=new T(function(){return B(_Ri(_));}),_Rl=function(_Rm,_Rn,_Ro,_Rp){var _Rq=E(_Rp);if(!_Rq._){var _Rr=_Rq.a,_Rs=E(_Ro);if(!_Rs._){var _Rt=_Rs.a,_Ru=_Rs.b,_Rv=_Rs.c;if(_Rt<=(imul(3,_Rr)|0)){return new T5(0,(1+_Rt|0)+_Rr|0,E(_Rm),_Rn,E(_Rs),E(_Rq));}else{var _Rw=E(_Rs.d);if(!_Rw._){var _Rx=_Rw.a,_Ry=E(_Rs.e);if(!_Ry._){var _Rz=_Ry.a,_RA=_Ry.b,_RB=_Ry.c,_RC=_Ry.d;if(_Rz>=(imul(2,_Rx)|0)){var _RD=function(_RE){var _RF=E(_Ry.e);return (_RF._==0)?new T5(0,(1+_Rt|0)+_Rr|0,E(_RA),_RB,E(new T5(0,(1+_Rx|0)+_RE|0,E(_Ru),_Rv,E(_Rw),E(_RC))),E(new T5(0,(1+_Rr|0)+_RF.a|0,E(_Rm),_Rn,E(_RF),E(_Rq)))):new T5(0,(1+_Rt|0)+_Rr|0,E(_RA),_RB,E(new T5(0,(1+_Rx|0)+_RE|0,E(_Ru),_Rv,E(_Rw),E(_RC))),E(new T5(0,1+_Rr|0,E(_Rm),_Rn,E(_Rg),E(_Rq))));},_RG=E(_RC);if(!_RG._){return new F(function(){return _RD(_RG.a);});}else{return new F(function(){return _RD(0);});}}else{return new T5(0,(1+_Rt|0)+_Rr|0,E(_Ru),_Rv,E(_Rw),E(new T5(0,(1+_Rr|0)+_Rz|0,E(_Rm),_Rn,E(_Ry),E(_Rq))));}}else{return E(_Rk);}}else{return E(_Rk);}}}else{return new T5(0,1+_Rr|0,E(_Rm),_Rn,E(_Rg),E(_Rq));}}else{var _RH=E(_Ro);if(!_RH._){var _RI=_RH.a,_RJ=_RH.b,_RK=_RH.c,_RL=_RH.e,_RM=E(_RH.d);if(!_RM._){var _RN=_RM.a,_RO=E(_RL);if(!_RO._){var _RP=_RO.a,_RQ=_RO.b,_RR=_RO.c,_RS=_RO.d;if(_RP>=(imul(2,_RN)|0)){var _RT=function(_RU){var _RV=E(_RO.e);return (_RV._==0)?new T5(0,1+_RI|0,E(_RQ),_RR,E(new T5(0,(1+_RN|0)+_RU|0,E(_RJ),_RK,E(_RM),E(_RS))),E(new T5(0,1+_RV.a|0,E(_Rm),_Rn,E(_RV),E(_Rg)))):new T5(0,1+_RI|0,E(_RQ),_RR,E(new T5(0,(1+_RN|0)+_RU|0,E(_RJ),_RK,E(_RM),E(_RS))),E(new T5(0,1,E(_Rm),_Rn,E(_Rg),E(_Rg))));},_RW=E(_RS);if(!_RW._){return new F(function(){return _RT(_RW.a);});}else{return new F(function(){return _RT(0);});}}else{return new T5(0,1+_RI|0,E(_RJ),_RK,E(_RM),E(new T5(0,1+_RP|0,E(_Rm),_Rn,E(_RO),E(_Rg))));}}else{return new T5(0,3,E(_RJ),_RK,E(_RM),E(new T5(0,1,E(_Rm),_Rn,E(_Rg),E(_Rg))));}}else{var _RX=E(_RL);return (_RX._==0)?new T5(0,3,E(_RX.b),_RX.c,E(new T5(0,1,E(_RJ),_RK,E(_Rg),E(_Rg))),E(new T5(0,1,E(_Rm),_Rn,E(_Rg),E(_Rg)))):new T5(0,2,E(_Rm),_Rn,E(_RH),E(_Rg));}}else{return new T5(0,1,E(_Rm),_Rn,E(_Rg),E(_Rg));}}},_RY=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_RZ=function(_S0){return new F(function(){return err(_RY);});},_S1=new T(function(){return B(_RZ(_));}),_S2=function(_S3,_S4,_S5,_S6){var _S7=E(_S5);if(!_S7._){var _S8=_S7.a,_S9=E(_S6);if(!_S9._){var _Sa=_S9.a,_Sb=_S9.b,_Sc=_S9.c;if(_Sa<=(imul(3,_S8)|0)){return new T5(0,(1+_S8|0)+_Sa|0,E(_S3),_S4,E(_S7),E(_S9));}else{var _Sd=E(_S9.d);if(!_Sd._){var _Se=_Sd.a,_Sf=_Sd.b,_Sg=_Sd.c,_Sh=_Sd.d,_Si=E(_S9.e);if(!_Si._){var _Sj=_Si.a;if(_Se>=(imul(2,_Sj)|0)){var _Sk=function(_Sl){var _Sm=E(_S3),_Sn=E(_Sd.e);return (_Sn._==0)?new T5(0,(1+_S8|0)+_Sa|0,E(_Sf),_Sg,E(new T5(0,(1+_S8|0)+_Sl|0,E(_Sm),_S4,E(_S7),E(_Sh))),E(new T5(0,(1+_Sj|0)+_Sn.a|0,E(_Sb),_Sc,E(_Sn),E(_Si)))):new T5(0,(1+_S8|0)+_Sa|0,E(_Sf),_Sg,E(new T5(0,(1+_S8|0)+_Sl|0,E(_Sm),_S4,E(_S7),E(_Sh))),E(new T5(0,1+_Sj|0,E(_Sb),_Sc,E(_Rg),E(_Si))));},_So=E(_Sh);if(!_So._){return new F(function(){return _Sk(_So.a);});}else{return new F(function(){return _Sk(0);});}}else{return new T5(0,(1+_S8|0)+_Sa|0,E(_Sb),_Sc,E(new T5(0,(1+_S8|0)+_Se|0,E(_S3),_S4,E(_S7),E(_Sd))),E(_Si));}}else{return E(_S1);}}else{return E(_S1);}}}else{return new T5(0,1+_S8|0,E(_S3),_S4,E(_S7),E(_Rg));}}else{var _Sp=E(_S6);if(!_Sp._){var _Sq=_Sp.a,_Sr=_Sp.b,_Ss=_Sp.c,_St=_Sp.e,_Su=E(_Sp.d);if(!_Su._){var _Sv=_Su.a,_Sw=_Su.b,_Sx=_Su.c,_Sy=_Su.d,_Sz=E(_St);if(!_Sz._){var _SA=_Sz.a;if(_Sv>=(imul(2,_SA)|0)){var _SB=function(_SC){var _SD=E(_S3),_SE=E(_Su.e);return (_SE._==0)?new T5(0,1+_Sq|0,E(_Sw),_Sx,E(new T5(0,1+_SC|0,E(_SD),_S4,E(_Rg),E(_Sy))),E(new T5(0,(1+_SA|0)+_SE.a|0,E(_Sr),_Ss,E(_SE),E(_Sz)))):new T5(0,1+_Sq|0,E(_Sw),_Sx,E(new T5(0,1+_SC|0,E(_SD),_S4,E(_Rg),E(_Sy))),E(new T5(0,1+_SA|0,E(_Sr),_Ss,E(_Rg),E(_Sz))));},_SF=E(_Sy);if(!_SF._){return new F(function(){return _SB(_SF.a);});}else{return new F(function(){return _SB(0);});}}else{return new T5(0,1+_Sq|0,E(_Sr),_Ss,E(new T5(0,1+_Sv|0,E(_S3),_S4,E(_Rg),E(_Su))),E(_Sz));}}else{return new T5(0,3,E(_Sw),_Sx,E(new T5(0,1,E(_S3),_S4,E(_Rg),E(_Rg))),E(new T5(0,1,E(_Sr),_Ss,E(_Rg),E(_Rg))));}}else{var _SG=E(_St);return (_SG._==0)?new T5(0,3,E(_Sr),_Ss,E(new T5(0,1,E(_S3),_S4,E(_Rg),E(_Rg))),E(_SG)):new T5(0,2,E(_S3),_S4,E(_Rg),E(_Sp));}}else{return new T5(0,1,E(_S3),_S4,E(_Rg),E(_Rg));}}},_SH=function(_SI,_SJ){return new T5(0,1,E(_SI),_SJ,E(_Rg),E(_Rg));},_SK=function(_SL,_SM,_SN){var _SO=E(_SN);if(!_SO._){return new F(function(){return _S2(_SO.b,_SO.c,_SO.d,B(_SK(_SL,_SM,_SO.e)));});}else{return new F(function(){return _SH(_SL,_SM);});}},_SP=function(_SQ,_SR,_SS){var _ST=E(_SS);if(!_ST._){return new F(function(){return _Rl(_ST.b,_ST.c,B(_SP(_SQ,_SR,_ST.d)),_ST.e);});}else{return new F(function(){return _SH(_SQ,_SR);});}},_SU=function(_SV,_SW,_SX,_SY,_SZ,_T0,_T1){return new F(function(){return _Rl(_SY,_SZ,B(_SP(_SV,_SW,_T0)),_T1);});},_T2=function(_T3,_T4,_T5,_T6,_T7,_T8,_T9,_Ta){var _Tb=E(_T5);if(!_Tb._){var _Tc=_Tb.a,_Td=_Tb.b,_Te=_Tb.c,_Tf=_Tb.d,_Tg=_Tb.e;if((imul(3,_Tc)|0)>=_T6){if((imul(3,_T6)|0)>=_Tc){return new T5(0,(_Tc+_T6|0)+1|0,E(_T3),_T4,E(_Tb),E(new T5(0,_T6,E(_T7),_T8,E(_T9),E(_Ta))));}else{return new F(function(){return _S2(_Td,_Te,_Tf,B(_T2(_T3,_T4,_Tg,_T6,_T7,_T8,_T9,_Ta)));});}}else{return new F(function(){return _Rl(_T7,_T8,B(_Th(_T3,_T4,_Tc,_Td,_Te,_Tf,_Tg,_T9)),_Ta);});}}else{return new F(function(){return _SU(_T3,_T4,_T6,_T7,_T8,_T9,_Ta);});}},_Th=function(_Ti,_Tj,_Tk,_Tl,_Tm,_Tn,_To,_Tp){var _Tq=E(_Tp);if(!_Tq._){var _Tr=_Tq.a,_Ts=_Tq.b,_Tt=_Tq.c,_Tu=_Tq.d,_Tv=_Tq.e;if((imul(3,_Tk)|0)>=_Tr){if((imul(3,_Tr)|0)>=_Tk){return new T5(0,(_Tk+_Tr|0)+1|0,E(_Ti),_Tj,E(new T5(0,_Tk,E(_Tl),_Tm,E(_Tn),E(_To))),E(_Tq));}else{return new F(function(){return _S2(_Tl,_Tm,_Tn,B(_T2(_Ti,_Tj,_To,_Tr,_Ts,_Tt,_Tu,_Tv)));});}}else{return new F(function(){return _Rl(_Ts,_Tt,B(_Th(_Ti,_Tj,_Tk,_Tl,_Tm,_Tn,_To,_Tu)),_Tv);});}}else{return new F(function(){return _SK(_Ti,_Tj,new T5(0,_Tk,E(_Tl),_Tm,E(_Tn),E(_To)));});}},_Tw=function(_Tx,_Ty,_Tz,_TA){var _TB=E(_Tz);if(!_TB._){var _TC=_TB.a,_TD=_TB.b,_TE=_TB.c,_TF=_TB.d,_TG=_TB.e,_TH=E(_TA);if(!_TH._){var _TI=_TH.a,_TJ=_TH.b,_TK=_TH.c,_TL=_TH.d,_TM=_TH.e;if((imul(3,_TC)|0)>=_TI){if((imul(3,_TI)|0)>=_TC){return new T5(0,(_TC+_TI|0)+1|0,E(_Tx),_Ty,E(_TB),E(_TH));}else{return new F(function(){return _S2(_TD,_TE,_TF,B(_T2(_Tx,_Ty,_TG,_TI,_TJ,_TK,_TL,_TM)));});}}else{return new F(function(){return _Rl(_TJ,_TK,B(_Th(_Tx,_Ty,_TC,_TD,_TE,_TF,_TG,_TL)),_TM);});}}else{return new F(function(){return _SK(_Tx,_Ty,_TB);});}}else{return new F(function(){return _SP(_Tx,_Ty,_TA);});}},_TN=function(_TO,_TP,_TQ){var _TR=E(_TO);if(_TR==1){var _TS=E(_TP);return new T2(0,new T(function(){return new T5(0,1,E(_TS.a),_TS.b,E(_Rg),E(_Rg));}),_TQ);}else{var _TT=B(_TN(_TR>>1,_TP,_TQ)),_TU=_TT.a,_TV=E(_TT.b);if(!_TV._){return new T2(0,_TU,_4);}else{var _TW=E(_TV.a),_TX=B(_TY(_TR>>1,_TV.b));return new T2(0,new T(function(){return B(_Tw(_TW.a,_TW.b,_TU,_TX.a));}),_TX.b);}}},_TY=function(_TZ,_U0){var _U1=E(_U0);if(!_U1._){return new T2(0,_Rg,_4);}else{var _U2=_U1.a,_U3=_U1.b,_U4=E(_TZ);if(_U4==1){var _U5=E(_U2);return new T2(0,new T(function(){return new T5(0,1,E(_U5.a),_U5.b,E(_Rg),E(_Rg));}),_U3);}else{var _U6=B(_TN(_U4>>1,_U2,_U3)),_U7=_U6.a,_U8=E(_U6.b);if(!_U8._){return new T2(0,_U7,_4);}else{var _U9=E(_U8.a),_Ua=B(_TY(_U4>>1,_U8.b));return new T2(0,new T(function(){return B(_Tw(_U9.a,_U9.b,_U7,_Ua.a));}),_Ua.b);}}}},_Ub=function(_Uc,_Ud,_Ue){while(1){var _Uf=E(_Ue);if(!_Uf._){return E(_Ud);}else{var _Ug=E(_Uf.a),_Uh=B(_TY(_Uc,_Uf.b)),_Ui=_Uc<<1,_Uj=B(_Tw(_Ug.a,_Ug.b,_Ud,_Uh.a));_Uc=_Ui;_Ud=_Uj;_Ue=_Uh.b;continue;}}},_Uk=function(_Ul,_Um,_Un,_Uo,_Up,_Uq){var _Ur=B(_fi(_Un,_Uo,_Up,_Uq)),_Us=B(_gf(E(_Ur.a)&4294967295,function(_Ut,_Uu){return new F(function(){return _R9(_Ul,_Um,_Ut,_Uu);});},new T3(0,_Un,_Uo,_Up),_Ur.b));return new T2(0,new T(function(){var _Uv=E(_Us.a);if(!_Uv._){return new T0(1);}else{var _Uw=E(_Uv.a);return B(_Ub(1,new T5(0,1,E(_Uw.a),_Uw.b,E(_Rg),E(_Rg)),_Uv.b));}}),_Us.b);},_Ux=new T0(2),_Uy=new T0(10),_Uz=new T0(5),_UA=new T0(9),_UB=new T0(6),_UC=new T0(7),_UD=new T0(8),_UE=function(_UF,_UG){var _UH=E(_UF),_UI=B(_fi(_UH.a,_UH.b,_UH.c,E(_UG))),_UJ=B(_gf(E(_UI.a)&4294967295,_g3,_UH,_UI.b));return new T2(0,_UJ.a,_UJ.b);},_UK=function(_UL,_UM){var _UN=E(_UL),_UO=_UN.a,_UP=_UN.b,_UQ=_UN.c,_UR=B(_fi(_UO,_UP,_UQ,E(_UM))),_US=B(_gf(E(_UR.a)&4294967295,_UT,_UN,_UR.b)),_UU=B(_fi(_UO,_UP,_UQ,E(_US.b))),_UV=B(_gf(E(_UU.a)&4294967295,_UE,_UN,_UU.b));return new T2(0,new T2(0,_US.a,_UV.a),_UV.b);},_UW=function(_UX,_UY,_UZ,_V0){var _V1=B(_fc(_UX,_UY,_UZ,_V0)),_V2=_V1.b;switch(E(_V1.a)){case 0:var _V3=B(_fi(_UX,_UY,_UZ,E(_V2))),_V4=B(_fi(_UX,_UY,_UZ,E(_V3.b)));return new T2(0,new T(function(){return new T2(0,E(_V3.a)&4294967295,E(_V4.a)&4294967295);}),_V4.b);case 1:var _V5=B(_fi(_UX,_UY,_UZ,E(_V2))),_V6=B(_fi(_UX,_UY,_UZ,E(_V5.b)));return new T2(0,new T(function(){return new T2(1,E(_V5.a)&4294967295,E(_V6.a)&4294967295);}),_V6.b);case 2:var _V7=B(_fi(_UX,_UY,_UZ,E(_V2))),_V8=B(_fi(_UX,_UY,_UZ,E(_V7.b)));return new T2(0,new T(function(){return new T2(2,E(_V7.a)&4294967295,E(_V8.a)&4294967295);}),_V8.b);case 3:var _V9=B(_fi(_UX,_UY,_UZ,E(_V2))),_Va=B(_gf(E(_V9.a)&4294967295,_g3,new T3(0,_UX,_UY,_UZ),_V9.b));return new T2(0,new T1(3,_Va.a),_Va.b);case 4:var _Vb=B(_fi(_UX,_UY,_UZ,E(_V2))),_Vc=B(_gf(E(_Vb.a)&4294967295,_UT,new T3(0,_UX,_UY,_UZ),_Vb.b)),_Vd=B(_fi(_UX,_UY,_UZ,E(_Vc.b))),_Ve=B(_gf(E(_Vd.a)&4294967295,_UK,new T3(0,_UX,_UY,_UZ),_Vd.b));return new T2(0,new T2(4,_Vc.a,_Ve.a),_Ve.b);case 5:return new T2(0,_Uz,_V2);case 6:return new T2(0,_UC,_V2);case 7:return new T2(0,_UB,_V2);case 8:return new T2(0,_UD,_V2);case 9:return new T2(0,_UA,_V2);case 10:return new T2(0,_Uy,_V2);default:return E(_Js);}},_UT=function(_Vf,_Vg){var _Vh=E(_Vf),_Vi=B(_UW(_Vh.a,_Vh.b,_Vh.c,E(_Vg)));return new T2(0,_Vi.a,_Vi.b);},_Vj=new T(function(){return B(unCStr("putWord8 not implemented"));}),_Vk=new T(function(){return B(err(_Vj));}),_Vl=function(_Vm){switch(E(_Vm)._){case 0:return E(_dJ);case 1:return E(_dJ);case 2:return E(_dJ);case 3:return E(_dJ);case 4:return E(_dJ);case 5:return E(_Vk);case 6:return E(_Vk);case 7:return E(_Vk);case 8:return E(_Vk);case 9:return E(_Vk);default:return E(_Vk);}},_Vn=new T2(0,_Vl,_UT),_Vo=function(_Vp,_Vq){var _Vr=E(_Vp),_Vs=B(_jU(_Vn,_id,_Vr.a,_Vr.b,_Vr.c,E(_Vq)));return new T2(0,_Vs.a,_Vs.b);},_Vt=new T(function(){return B(unCStr("MArray: undefined array element"));}),_Vu=new T(function(){return B(err(_Vt));}),_Vv=new T(function(){return B(unCStr("Negative range size"));}),_Vw=new T(function(){return B(err(_Vv));}),_Vx=function(_Vy,_Vz,_VA,_VB){var _VC=B(_Uk(_fH,_M6,_Vy,_Vz,_VA,_VB)),_VD=B(_Uk(_fH,_gy,_Vy,_Vz,_VA,E(_VC.b))),_VE=B(_fi(_Vy,_Vz,_VA,E(_VD.b))),_VF=E(_VE.a)&4294967295,_VG=B(_jD(_VF,_Vo,new T3(0,_Vy,_Vz,_VA),_VE.b)),_VH=B(_jU(_mi,_id,_Vy,_Vz,_VA,E(_VG.b))),_VI=B(_QT(_PU,_Vy,_Vz,_VA,E(_VH.b))),_VJ=B(_QT(_PU,_Vy,_Vz,_VA,E(_VI.b))),_VK=B(_QT(_PG,_Vy,_Vz,_VA,E(_VJ.b))),_VL=B(_Uk(_fH,_ko,_Vy,_Vz,_VA,E(_VK.b))),_VM=B(_fi(_Vy,_Vz,_VA,E(_VL.b))),_VN=new T(function(){var _VO=new T(function(){var _VP=function(_){var _VQ=_VF-1|0,_VR=function(_VS){if(_VS>=0){var _VT=newArr(_VS,_Vu),_VU=_VT,_VV=function(_VW){var _VX=function(_VY,_VZ,_){while(1){if(_VY!=_VW){var _W0=E(_VZ);if(!_W0._){return _5;}else{var _=_VU[_VY]=_W0.a,_W1=_VY+1|0;_VY=_W1;_VZ=_W0.b;continue;}}else{return _5;}}},_W2=B(_VX(0,_VG.a,_));return new T4(0,E(_ig),E(_VQ),_VS,_VU);};if(0>_VQ){return new F(function(){return _VV(0);});}else{var _W3=_VQ+1|0;if(_W3>=0){return new F(function(){return _VV(_W3);});}else{return E(_if);}}}else{return E(_Vw);}};if(0>_VQ){return new F(function(){return _VR(0);});}else{return new F(function(){return _VR(_VQ+1|0);});}};return B(_8O(_VP));});return {_:0,a:_VC.a,b:_VD.a,c:_VH.a,d:_VI.a,e:_VJ.a,f:_VO,g:_VK.a,h:_Ux,i:_Rg,j:_VL.a,k:_Ux,l:E(_VM.a)&4294967295};});return new T2(0,_VN,_VM.b);},_W4=function(_W5,_W6){var _W7=E(_W5),_W8=B(_Vx(_W7.a,_W7.b,_W7.c,E(_W6)));return new T2(0,_W8.a,_W8.b);},_W9=function(_Wa){return E(_dJ);},_Wb=new T2(0,_W9,_W4),_Wc=new T2(1,_bX,_4),_Wd=function(_We,_Wf){var _Wg=new T(function(){return B(A3(_eg,_e6,new T2(1,function(_Wh){return new F(function(){return _bZ(0,_Wf&4294967295,_Wh);});},new T2(1,function(_Wi){return new F(function(){return _bZ(0,E(_We)&4294967295,_Wi);});},_4)),_Wc));});return new F(function(){return err(B(unAppCStr("Unsupported PGF version ",new T2(1,_bY,_Wg))));});},_Wj=function(_Wk,_Wl){var _Wm=new T(function(){var _Wn=E(_Wk),_Wo=B(_fc(_Wn.a,_Wn.b,_Wn.c,E(_Wl)));return new T2(0,_Wo.a,_Wo.b);}),_Wp=new T(function(){var _Wq=E(_Wk),_Wr=B(_fc(_Wq.a,_Wq.b,_Wq.c,E(E(_Wm).b)));return new T2(0,_Wr.a,_Wr.b);});return new T2(0,new T(function(){return (E(E(_Wm).a)<<8>>>0&65535|E(E(_Wp).a))>>>0;}),new T(function(){return E(E(_Wp).b);}));},_Ws=function(_Wt){var _Wu=E(_Wt);return new T4(0,_Wu.a,_Wu.b,new T(function(){var _Wv=E(_Wu.c);if(!_Wv._){return __Z;}else{return new T1(1,new T2(0,_Wv.a,_4));}}),_Wu.d);},_Ww=function(_Wx){return E(_dJ);},_Wy=0,_Wz=1,_WA=function(_WB,_WC,_WD,_WE){var _WF=B(_fc(_WB,_WC,_WD,_WE)),_WG=_WF.b;switch(E(_WF.a)){case 0:var _WH=B(_fc(_WB,_WC,_WD,E(_WG))),_WI=_WH.b;switch(E(_WH.a)){case 0:var _WJ=B(_ft(_WB,_WC,_WD,E(_WI))),_WK=B(_WA(_WB,_WC,_WD,E(_WJ.b)));return new T2(0,new T3(0,_Wy,_WJ.a,_WK.a),_WK.b);case 1:var _WL=B(_ft(_WB,_WC,_WD,E(_WI))),_WM=B(_WA(_WB,_WC,_WD,E(_WL.b)));return new T2(0,new T3(0,_Wz,_WL.a,_WM.a),_WM.b);default:return E(_Js);}break;case 1:var _WN=B(_WA(_WB,_WC,_WD,E(_WG))),_WO=B(_WA(_WB,_WC,_WD,E(_WN.b)));return new T2(0,new T2(1,_WN.a,_WO.a),_WO.b);case 2:var _WP=B(_LO(_WB,_WC,_WD,E(_WG)));return new T2(0,new T1(2,_WP.a),_WP.b);case 3:var _WQ=B(_fi(_WB,_WC,_WD,E(_WG)));return new T2(0,new T(function(){return new T1(3,E(_WQ.a)&4294967295);}),_WQ.b);case 4:var _WR=B(_ft(_WB,_WC,_WD,E(_WG)));return new T2(0,new T1(4,_WR.a),_WR.b);case 5:var _WS=B(_fi(_WB,_WC,_WD,E(_WG)));return new T2(0,new T(function(){return new T1(5,E(_WS.a)&4294967295);}),_WS.b);case 6:var _WT=B(_WA(_WB,_WC,_WD,E(_WG))),_WU=B(_WV(_WB,_WC,_WD,E(_WT.b)));return new T2(0,new T2(6,_WT.a,_WU.a),_WU.b);case 7:var _WW=B(_WA(_WB,_WC,_WD,E(_WG)));return new T2(0,new T1(7,_WW.a),_WW.b);default:return E(_Js);}},_WX=function(_WY,_WZ){var _X0=E(_WY),_X1=B(_WA(_X0.a,_X0.b,_X0.c,E(_WZ)));return new T2(0,_X1.a,_X1.b);},_X2=function(_X3,_X4){var _X5=E(_X3),_X6=_X5.a,_X7=_X5.b,_X8=_X5.c,_X9=B(_fc(_X6,_X7,_X8,E(_X4))),_Xa=_X9.b,_Xb=function(_Xc,_Xd){var _Xe=B(_ft(_X6,_X7,_X8,_Xd)),_Xf=B(_WV(_X6,_X7,_X8,E(_Xe.b)));return new T2(0,new T3(0,_Xc,_Xe.a,_Xf.a),_Xf.b);};switch(E(_X9.a)){case 0:var _Xg=B(_Xb(_Wy,E(_Xa)));return new T2(0,_Xg.a,_Xg.b);case 1:var _Xh=B(_Xb(_Wz,E(_Xa)));return new T2(0,_Xh.a,_Xh.b);default:return E(_Js);}},_WV=function(_Xi,_Xj,_Xk,_Xl){var _Xm=B(_fi(_Xi,_Xj,_Xk,_Xl)),_Xn=B(_gf(E(_Xm.a)&4294967295,_X2,new T3(0,_Xi,_Xj,_Xk),_Xm.b)),_Xo=B(_ft(_Xi,_Xj,_Xk,E(_Xn.b))),_Xp=B(_fi(_Xi,_Xj,_Xk,E(_Xo.b))),_Xq=B(_gf(E(_Xp.a)&4294967295,_WX,new T3(0,_Xi,_Xj,_Xk),_Xp.b));return new T2(0,new T3(0,_Xn.a,_Xo.a,_Xq.a),_Xq.b);},_Xr=function(_Xs,_Xt){var _Xu=E(_Xs),_Xv=_Xu.a,_Xw=_Xu.b,_Xx=_Xu.c,_Xy=B(_fc(_Xv,_Xw,_Xx,E(_Xt))),_Xz=_Xy.b,_XA=function(_XB,_XC){var _XD=B(_ft(_Xv,_Xw,_Xx,_XC)),_XE=B(_WV(_Xv,_Xw,_Xx,E(_XD.b)));return new T2(0,new T3(0,_XB,_XD.a,_XE.a),_XE.b);};switch(E(_Xy.a)){case 0:var _XF=B(_XA(_Wy,E(_Xz)));return new T2(0,_XF.a,_XF.b);case 1:var _XG=B(_XA(_Wz,E(_Xz)));return new T2(0,_XG.a,_XG.b);default:return E(_Js);}},_XH=function(_XI,_XJ){var _XK=B(_IY(_Jt,_LL,_XI,_XJ)),_XL=E(_XI),_XM=B(_ft(_XL.a,_XL.b,_XL.c,E(_XK.b)));return new T2(0,new T2(0,_XK.a,_XM.a),_XM.b);},_XN=function(_XO,_XP,_XQ,_XR){var _XS=B(_fi(_XO,_XP,_XQ,_XR)),_XT=B(_gf(E(_XS.a)&4294967295,_Xr,new T3(0,_XO,_XP,_XQ),_XS.b)),_XU=B(_fi(_XO,_XP,_XQ,E(_XT.b))),_XV=B(_gf(E(_XU.a)&4294967295,_XH,new T3(0,_XO,_XP,_XQ),_XU.b)),_XW=B(_IY(_Jt,_LL,new T3(0,_XO,_XP,_XQ),_XV.b));return new T2(0,new T3(0,_XT.a,_XV.a,_XW.a),_XW.b);},_XX=function(_XY,_XZ){var _Y0=E(_XY),_Y1=B(_XN(_Y0.a,_Y0.b,_Y0.c,E(_XZ)));return new T2(0,_Y1.a,_Y1.b);},_Y2=new T2(0,_Ww,_XX),_Y3=function(_Y4){return E(_dJ);},_Y5=new T0(4),_Y6=function(_Y7,_Y8,_Y9){switch(E(_Y7)){case 0:var _Ya=E(_Y8),_Yb=_Ya.a,_Yc=_Ya.b,_Yd=_Ya.c,_Ye=B(_ft(_Yb,_Yc,_Yd,E(_Y9))),_Yf=B(_fi(_Yb,_Yc,_Yd,E(_Ye.b))),_Yg=B(_gf(E(_Yf.a)&4294967295,_Yh,_Ya,_Yf.b));return new T2(0,new T2(0,_Ye.a,_Yg.a),_Yg.b);case 1:var _Yi=E(_Y8),_Yj=B(_ft(_Yi.a,_Yi.b,_Yi.c,E(_Y9)));return new T2(0,new T1(2,_Yj.a),_Yj.b);case 2:var _Yk=E(_Y8),_Yl=_Yk.a,_Ym=_Yk.b,_Yn=_Yk.c,_Yo=B(_ft(_Yl,_Ym,_Yn,E(_Y9))),_Yp=B(_fc(_Yl,_Ym,_Yn,E(_Yo.b))),_Yq=B(_Y6(E(_Yp.a),_Yk,_Yp.b));return new T2(0,new T2(3,_Yo.a,_Yq.a),_Yq.b);case 3:return new T2(0,_Y5,_Y9);case 4:var _Yr=E(_Y8),_Ys=B(_LO(_Yr.a,_Yr.b,_Yr.c,E(_Y9)));return new T2(0,new T1(1,_Ys.a),_Ys.b);case 5:var _Yt=E(_Y8),_Yu=B(_fc(_Yt.a,_Yt.b,_Yt.c,E(_Y9))),_Yv=B(_Y6(E(_Yu.a),_Yt,_Yu.b));return new T2(0,new T1(5,_Yv.a),_Yv.b);case 6:var _Yw=E(_Y8),_Yx=B(_WA(_Yw.a,_Yw.b,_Yw.c,E(_Y9)));return new T2(0,new T1(6,_Yx.a),_Yx.b);default:return E(_Js);}},_Yy=function(_Yz,_YA,_YB,_YC){var _YD=B(_fc(_Yz,_YA,_YB,_YC));return new F(function(){return _Y6(E(_YD.a),new T3(0,_Yz,_YA,_YB),_YD.b);});},_Yh=function(_YE,_YF){var _YG=E(_YE),_YH=B(_Yy(_YG.a,_YG.b,_YG.c,E(_YF)));return new T2(0,_YH.a,_YH.b);},_YI=function(_YJ,_YK,_YL,_YM){var _YN=B(_fi(_YJ,_YK,_YL,_YM)),_YO=B(_gf(E(_YN.a)&4294967295,_Yh,new T3(0,_YJ,_YK,_YL),_YN.b)),_YP=B(_WA(_YJ,_YK,_YL,E(_YO.b)));return new T2(0,new T2(0,_YO.a,_YP.a),_YP.b);},_YQ=function(_YR,_YS){var _YT=E(_YR),_YU=B(_YI(_YT.a,_YT.b,_YT.c,E(_YS)));return new T2(0,_YU.a,_YU.b);},_YV=function(_YW,_YX,_YY,_YZ){var _Z0=B(_WV(_YW,_YX,_YY,_YZ)),_Z1=_Z0.a,_Z2=B(_fi(_YW,_YX,_YY,E(_Z0.b))),_Z3=_Z2.a,_Z4=B(_fc(_YW,_YX,_YY,E(_Z2.b))),_Z5=_Z4.b;if(!E(_Z4.a)){var _Z6=B(_IY(_Jt,_LL,new T3(0,_YW,_YX,_YY),_Z5));return new T2(0,new T4(0,_Z1,new T(function(){return E(_Z3)&4294967295;}),_4l,_Z6.a),_Z6.b);}else{var _Z7=B(_fi(_YW,_YX,_YY,E(_Z5))),_Z8=B(_gf(E(_Z7.a)&4294967295,_YQ,new T3(0,_YW,_YX,_YY),_Z7.b)),_Z9=B(_IY(_Jt,_LL,new T3(0,_YW,_YX,_YY),_Z8.b));return new T2(0,new T4(0,_Z1,new T(function(){return E(_Z3)&4294967295;}),new T1(1,_Z8.a),_Z9.a),_Z9.b);}},_Za=function(_Zb,_Zc){var _Zd=E(_Zb),_Ze=B(_YV(_Zd.a,_Zd.b,_Zd.c,E(_Zc)));return new T2(0,_Ze.a,_Ze.b);},_Zf=new T2(0,_Y3,_Za),_Zg=function(_Zh,_Zi){var _Zj=E(_Zi);return (_Zj._==0)?new T5(0,_Zj.a,E(_Zj.b),new T(function(){return B(A1(_Zh,_Zj.c));}),E(B(_Zg(_Zh,_Zj.d))),E(B(_Zg(_Zh,_Zj.e)))):new T0(1);},_Zk=function(_Zl,_Zm,_Zn,_Zo){var _Zp=B(_Uk(_fH,_M6,_Zl,_Zm,_Zn,_Zo)),_Zq=B(_Uk(_fH,_Zf,_Zl,_Zm,_Zn,E(_Zp.b))),_Zr=B(_Uk(_fH,_Y2,_Zl,_Zm,_Zn,E(_Zq.b)));return new T2(0,new T3(0,_Zp.a,new T(function(){return B(_Zg(_Ws,_Zq.a));}),_Zr.a),_Zr.b);},_Zs=function(_Zt,_Zu,_Zv){var _Zw=E(_Zt);if(!_Zw._){return new T2(0,_4,_Zv);}else{var _Zx=new T(function(){return B(A2(_Zw.a,_Zu,_Zv));}),_Zy=B(_Zs(_Zw.b,_Zu,new T(function(){return E(E(_Zx).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_Zx).a);}),_Zy.a),_Zy.b);}},_Zz=function(_ZA,_ZB,_ZC,_ZD){if(0>=_ZA){return new F(function(){return _Zs(_4,_ZC,_ZD);});}else{var _ZE=function(_ZF){var _ZG=E(_ZF);return (_ZG==1)?E(new T2(1,_ZB,_4)):new T2(1,_ZB,new T(function(){return B(_ZE(_ZG-1|0));}));};return new F(function(){return _Zs(B(_ZE(_ZA)),_ZC,_ZD);});}},_ZH=function(_ZI,_ZJ,_ZK){var _ZL=new T(function(){var _ZM=E(_ZJ),_ZN=B(_fi(_ZM.a,_ZM.b,_ZM.c,E(_ZK))),_ZO=E(_ZN.a)&4294967295,_ZP=B(_Zz(_ZO,_ZI,_ZM,_ZN.b));return new T2(0,new T2(0,_ZO,_ZP.a),_ZP.b);});return new T2(0,new T(function(){return E(E(E(_ZL).a).b);}),new T(function(){return E(E(_ZL).b);}));},_ZQ=function(_ZR,_ZS,_ZT,_ZU){var _ZV=new T(function(){var _ZW=function(_ZX,_ZY){var _ZZ=new T(function(){return B(A2(_ZR,_ZX,_ZY));}),_100=B(A2(_ZS,_ZX,new T(function(){return E(E(_ZZ).b);})));return new T2(0,new T2(0,new T(function(){return E(E(_ZZ).a);}),_100.a),_100.b);},_101=B(_ZH(_ZW,_ZT,_ZU));return new T2(0,_101.a,_101.b);});return new T2(0,new T(function(){var _102=E(E(_ZV).a);if(!_102._){return new T0(1);}else{var _103=E(_102.a);return B(_Ub(1,new T5(0,1,E(_103.a),_103.b,E(_Rg),E(_Rg)),_102.b));}}),new T(function(){return E(E(_ZV).b);}));},_104=new T(function(){return B(unCStr("Prelude.Enum.Bool.toEnum: bad argument"));}),_105=new T(function(){return B(err(_104));}),_106=new T(function(){return B(unCStr(")"));}),_107=function(_108){return new F(function(){return err(B(unAppCStr("Unable to read PGF file (",new T(function(){return B(_0(_108,_106));}))));});},_109=new T(function(){return B(unCStr("getLiteral"));}),_10a=new T(function(){return B(_107(_109));}),_10b=function(_10c,_10d,_10e,_10f){var _10g=B(_fc(_10c,_10d,_10e,_10f)),_10h=_10g.b;switch(E(_10g.a)){case 0:var _10i=B(_fi(_10c,_10d,_10e,E(_10h))),_10j=B(_gf(E(_10i.a)&4294967295,_g3,new T3(0,_10c,_10d,_10e),_10i.b));return new T2(0,new T1(0,_10j.a),_10j.b);case 1:var _10k=B(_fi(_10c,_10d,_10e,E(_10h)));return new T2(0,new T1(1,new T(function(){return E(_10k.a)&4294967295;})),_10k.b);case 2:var _10l=B(_IY(_Jt,_LL,new T3(0,_10c,_10d,_10e),_10h));return new T2(0,new T1(2,_10l.a),_10l.b);default:return E(_10a);}},_10m=new T(function(){return B(unCStr("getBindType"));}),_10n=new T(function(){return B(_107(_10m));}),_10o=new T(function(){return B(unCStr("getExpr"));}),_10p=new T(function(){return B(_107(_10o));}),_10q=function(_10r,_10s,_10t,_10u){var _10v=B(_fc(_10r,_10s,_10t,_10u)),_10w=_10v.b;switch(E(_10v.a)){case 0:var _10x=B(_fc(_10r,_10s,_10t,E(_10w))),_10y=_10x.b;switch(E(_10x.a)){case 0:var _10z=B(_ft(_10r,_10s,_10t,E(_10y))),_10A=B(_10q(_10r,_10s,_10t,E(_10z.b)));return new T2(0,new T3(0,_Wy,_10z.a,_10A.a),_10A.b);case 1:var _10B=B(_ft(_10r,_10s,_10t,E(_10y))),_10C=B(_10q(_10r,_10s,_10t,E(_10B.b)));return new T2(0,new T3(0,_Wz,_10B.a,_10C.a),_10C.b);default:return E(_10n);}break;case 1:var _10D=B(_10q(_10r,_10s,_10t,E(_10w))),_10E=B(_10q(_10r,_10s,_10t,E(_10D.b)));return new T2(0,new T2(1,_10D.a,_10E.a),_10E.b);case 2:var _10F=B(_10b(_10r,_10s,_10t,E(_10w)));return new T2(0,new T1(2,_10F.a),_10F.b);case 3:var _10G=B(_fi(_10r,_10s,_10t,E(_10w)));return new T2(0,new T(function(){return new T1(3,E(_10G.a)&4294967295);}),_10G.b);case 4:var _10H=B(_ft(_10r,_10s,_10t,E(_10w)));return new T2(0,new T1(4,_10H.a),_10H.b);case 5:var _10I=B(_fi(_10r,_10s,_10t,E(_10w)));return new T2(0,new T(function(){return new T1(5,E(_10I.a)&4294967295);}),_10I.b);case 6:var _10J=B(_10q(_10r,_10s,_10t,E(_10w))),_10K=B(_10L(_10r,_10s,_10t,_10J.b));return new T2(0,new T2(6,_10J.a,_10K.a),_10K.b);case 7:var _10M=B(_10q(_10r,_10s,_10t,E(_10w)));return new T2(0,new T1(7,_10M.a),_10M.b);default:return E(_10p);}},_10N=function(_10O,_10P){var _10Q=E(_10O),_10R=B(_10q(_10Q.a,_10Q.b,_10Q.c,E(_10P)));return new T2(0,_10R.a,_10R.b);},_10S=function(_10T,_10U,_10V,_10W){var _10X=B(_fc(_10T,_10U,_10V,_10W)),_10Y=_10X.b;switch(E(_10X.a)){case 0:var _10Z=B(_ft(_10T,_10U,_10V,E(_10Y))),_110=B(_10L(_10T,_10U,_10V,_10Z.b));return new T2(0,new T3(0,_Wy,_10Z.a,_110.a),_110.b);case 1:var _111=B(_ft(_10T,_10U,_10V,E(_10Y))),_112=B(_10L(_10T,_10U,_10V,_111.b));return new T2(0,new T3(0,_Wz,_111.a,_112.a),_112.b);default:return E(_10n);}},_113=function(_114,_115){var _116=E(_114),_117=B(_10S(_116.a,_116.b,_116.c,E(_115)));return new T2(0,_117.a,_117.b);},_10L=function(_118,_119,_11a,_11b){var _11c=new T3(0,_118,_119,_11a),_11d=B(_ZH(_113,_11c,_11b)),_11e=B(_ft(_118,_119,_11a,E(_11d.b))),_11f=B(_ZH(_10N,_11c,_11e.b));return new T2(0,new T3(0,_11d.a,_11e.a,_11f.a),_11f.b);},_11g=new T(function(){return B(unCStr("getPatt"));}),_11h=new T(function(){return B(_107(_11g));}),_11i=function(_11j,_11k,_11l,_11m){var _11n=B(_fc(_11j,_11k,_11l,_11m)),_11o=_11n.b;switch(E(_11n.a)){case 0:var _11p=B(_ft(_11j,_11k,_11l,E(_11o))),_11q=B(_ZH(_11r,new T3(0,_11j,_11k,_11l),_11p.b));return new T2(0,new T2(0,_11p.a,_11q.a),_11q.b);case 1:var _11s=B(_ft(_11j,_11k,_11l,E(_11o)));return new T2(0,new T1(2,_11s.a),_11s.b);case 2:var _11t=B(_ft(_11j,_11k,_11l,E(_11o))),_11u=B(_11i(_11j,_11k,_11l,E(_11t.b)));return new T2(0,new T2(3,_11t.a,_11u.a),_11u.b);case 3:return new T2(0,_Y5,_11o);case 4:var _11v=B(_10b(_11j,_11k,_11l,E(_11o)));return new T2(0,new T1(1,_11v.a),_11v.b);case 5:var _11w=B(_11i(_11j,_11k,_11l,E(_11o)));return new T2(0,new T1(5,_11w.a),_11w.b);case 6:var _11x=B(_10q(_11j,_11k,_11l,E(_11o)));return new T2(0,new T1(6,_11x.a),_11x.b);default:return E(_11h);}},_11r=function(_11y,_11z){var _11A=E(_11y),_11B=B(_11i(_11A.a,_11A.b,_11A.c,E(_11z)));return new T2(0,_11B.a,_11B.b);},_11C=function(_11D,_11E){var _11F=E(_11D),_11G=B(_ZH(_11r,_11F,_11E)),_11H=B(_10q(_11F.a,_11F.b,_11F.c,E(_11G.b)));return new T2(0,new T2(0,_11G.a,_11H.a),_11H.b);},_11I=function(_11J,_11K,_11L,_11M){var _11N=B(_10L(_11J,_11K,_11L,_11M)),_11O=_11N.a,_11P=B(_fi(_11J,_11K,_11L,E(_11N.b))),_11Q=_11P.a,_11R=B(_fc(_11J,_11K,_11L,E(_11P.b))),_11S=_11R.b;switch(E(_11R.a)&4294967295){case 0:var _11T=B(_IY(_Jt,_LL,new T3(0,_11J,_11K,_11L),_11S));return new T2(0,new T4(0,_11O,new T(function(){return E(_11Q)&4294967295;}),_4l,_11T.a),_11T.b);case 1:var _11U=new T3(0,_11J,_11K,_11L),_11V=new T(function(){var _11W=B(_ZH(_11C,_11U,_11S));return new T2(0,_11W.a,_11W.b);}),_11X=B(_IY(_Jt,_LL,_11U,new T(function(){return E(E(_11V).b);},1)));return new T2(0,new T4(0,_11O,new T(function(){return E(_11Q)&4294967295;}),new T1(1,new T(function(){return E(E(_11V).a);})),_11X.a),_11X.b);default:return E(_105);}},_11Y=function(_11Z,_120){var _121=E(_11Z),_122=B(_11I(_121.a,_121.b,_121.c,_120));return new T2(0,_122.a,_122.b);},_123=function(_124,_125){var _126=E(_124),_127=B(_10b(_126.a,_126.b,_126.c,E(_125)));return new T2(0,_127.a,_127.b);},_128=function(_129,_12a){var _12b=E(_129),_12c=B(_ft(_12b.a,_12b.b,_12b.c,E(_12a)));return new T2(0,_12c.a,_12c.b);},_12d=function(_12e,_12f){while(1){var _12g=E(_12e);if(!_12g._){return (E(_12f)._==0)?1:0;}else{var _12h=E(_12f);if(!_12h._){return 2;}else{var _12i=E(_12g.a),_12j=E(_12h.a);if(_12i!=_12j){return (_12i>_12j)?2:0;}else{_12e=_12g.b;_12f=_12h.b;continue;}}}}},_12k=function(_12l,_12m){return (B(_12d(_12l,_12m))==0)?true:false;},_12n=function(_12o,_12p){return (B(_12d(_12o,_12p))==2)?false:true;},_12q=function(_12r,_12s){return (B(_12d(_12r,_12s))==2)?true:false;},_12t=function(_12u,_12v){return (B(_12d(_12u,_12v))==0)?false:true;},_12w=function(_12x,_12y){return (B(_12d(_12x,_12y))==2)?E(_12x):E(_12y);},_12z=function(_12A,_12B){return (B(_12d(_12A,_12B))==2)?E(_12B):E(_12A);},_12C={_:0,a:_sz,b:_12d,c:_12k,d:_12n,e:_12q,f:_12t,g:_12w,h:_12z},_12D=function(_12E){var _12F=E(_12E)&4294967295;if(_12F>>>0>1114111){return new F(function(){return _fK(_12F);});}else{return _12F;}},_12G=function(_12H){var _12I=E(_12H);return (_12I._==0)?__Z:new T2(1,new T(function(){return B(_12D(_12I.a));}),new T(function(){return B(_12G(_12I.b));}));},_12J=function(_12K){var _12L=E(_12K);return (_12L._==0)?__Z:new T2(1,new T(function(){return B(_12D(_12L.a));}),new T(function(){return B(_12J(_12L.b));}));},_12M=function(_12N,_12O,_12P,_12Q,_12R,_12S){return new F(function(){return _sf(B(_G(_12D,B(_IJ(_12N,_12O,_12P)))),B(_G(_12D,B(_IJ(_12Q,_12R,_12S)))));});},_12T=function(_12U,_12V,_12W,_12X,_12Y,_12Z){return (!B(_12M(_12U,_12V,_12W,_12X,_12Y,_12Z)))?(B(_12d(B(_12J(new T(function(){return B(_IJ(_12U,_12V,_12W));}))),B(_12G(new T(function(){return B(_IJ(_12X,_12Y,_12Z));})))))==2)?2:0:1;},_130=function(_131,_132,_133,_134,_135,_136){var _137=new T3(0,_132,_133,_134),_138=E(_136);if(!_138._){var _139=_138.c,_13a=_138.d,_13b=_138.e,_13c=E(_138.b);switch(B(_12T(_132,_133,_134,_13c.a,_13c.b,_13c.c))){case 0:return new F(function(){return _Rl(_13c,_139,B(_130(_131,_132,_133,_134,_135,_13a)),_13b);});break;case 1:return new T5(0,_138.a,E(_137),new T(function(){return B(A3(_131,_137,_135,_139));}),E(_13a),E(_13b));default:return new F(function(){return _S2(_13c,_139,_13a,B(_130(_131,_132,_133,_134,_135,_13b)));});}}else{return new T5(0,1,E(_137),_135,E(_Rg),E(_Rg));}},_13d=function(_13e,_13f){var _13g=function(_13h,_13i){while(1){var _13j=E(_13i);if(!_13j._){return E(_13h);}else{var _13k=E(_13j.a),_13l=E(_13k.a),_13m=B(_130(_13e,_13l.a,_13l.b,_13l.c,_13k.b,_13h));_13h=_13m;_13i=_13j.b;continue;}}};return new F(function(){return _13g(_Rg,_13f);});},_13n=function(_13o){return E(E(_13o).b);},_13p=function(_13q,_13r,_13s,_13t){var _13u=E(_13r),_13v=E(_13t);if(!_13v._){var _13w=_13v.b,_13x=_13v.c,_13y=_13v.d,_13z=_13v.e;switch(B(A3(_13n,_13q,_13u,_13w))){case 0:return new F(function(){return _Rl(_13w,_13x,B(_13p(_13q,_13u,_13s,_13y)),_13z);});break;case 1:return new T5(0,_13v.a,E(_13u),_13s,E(_13y),E(_13z));default:return new F(function(){return _S2(_13w,_13x,_13y,B(_13p(_13q,_13u,_13s,_13z)));});}}else{return new T5(0,1,E(_13u),_13s,E(_Rg),E(_Rg));}},_13A=function(_13B,_13C,_13D,_13E){return new F(function(){return _13p(_13B,_13C,_13D,_13E);});},_13F=function(_13G,_13H,_13I,_13J,_13K){var _13L=E(_13K),_13M=B(_13N(_13G,_13H,_13I,_13J,_13L.a,_13L.b));return new T2(0,_13M.a,_13M.b);},_13O=function(_13P,_13Q,_13R){var _13S=function(_13T,_13U){while(1){var _13V=E(_13T),_13W=E(_13U);if(!_13W._){switch(B(A3(_13n,_13P,_13V,_13W.b))){case 0:_13T=_13V;_13U=_13W.d;continue;case 1:return new T1(1,_13W.c);default:_13T=_13V;_13U=_13W.e;continue;}}else{return __Z;}}};return new F(function(){return _13S(_13Q,_13R);});},_13X=function(_13Y,_13Z){var _140=E(_13Y);if(!_140._){return new T2(0,new T1(1,_13Z),_Rg);}else{var _141=new T(function(){return new T5(0,1,E(_140.a),new T(function(){return B(_142(_140.b,_13Z));}),E(_Rg),E(_Rg));});return new T2(0,_4l,_141);}},_142=function(_143,_144){var _145=B(_13X(_143,_144));return new T2(0,_145.a,_145.b);},_13N=function(_146,_147,_148,_149,_14a,_14b){var _14c=E(_148);if(!_14c._){var _14d=E(_14a);return (_14d._==0)?new T2(0,new T1(1,_149),_14b):new T2(0,new T1(1,new T(function(){return B(A2(_147,_149,_14d.a));})),_14b);}else{var _14e=_14c.a,_14f=_14c.b,_14g=B(_13O(_146,_14e,_14b));if(!_14g._){var _14h=new T(function(){return B(_13A(_146,_14e,new T(function(){return B(_142(_14f,_149));}),_14b));});return new T2(0,_14a,_14h);}else{var _14i=new T(function(){return B(_13A(_146,_14e,new T(function(){return B(_13F(_146,_147,_14f,_149,_14g.a));}),_14b));});return new T2(0,_14a,_14i);}}},_14j=function(_14k,_14l,_14m){var _14n=function(_14o,_14p,_14q){while(1){var _14r=E(_14o);if(!_14r._){return new T2(0,_14p,_14q);}else{var _14s=E(_14r.a),_14t=B(_13N(_14k,_14l,_14s.a,_14s.b,_14p,_14q));_14o=_14r.b;_14p=_14t.a;_14q=_14t.b;continue;}}};return new F(function(){return _14n(_14m,_4l,_Rg);});},_14u=function(_14v,_14w,_14x){var _14y=E(_14x);switch(_14y._){case 0:var _14z=_14y.a,_14A=_14y.b,_14B=_14y.c,_14C=_14y.d,_14D=_14A>>>0;if(((_14v>>>0&((_14D-1>>>0^4294967295)>>>0^_14D)>>>0)>>>0&4294967295)==_14z){return ((_14v>>>0&_14D)>>>0==0)?new T4(0,_14z,_14A,E(B(_14u(_14v,_14w,_14B))),E(_14C)):new T4(0,_14z,_14A,E(_14B),E(B(_14u(_14v,_14w,_14C))));}else{var _14E=(_14v>>>0^_14z>>>0)>>>0,_14F=(_14E|_14E>>>1)>>>0,_14G=(_14F|_14F>>>2)>>>0,_14H=(_14G|_14G>>>4)>>>0,_14I=(_14H|_14H>>>8)>>>0,_14J=(_14I|_14I>>>16)>>>0,_14K=(_14J^_14J>>>1)>>>0&4294967295,_14L=_14K>>>0;return ((_14v>>>0&_14L)>>>0==0)?new T4(0,(_14v>>>0&((_14L-1>>>0^4294967295)>>>0^_14L)>>>0)>>>0&4294967295,_14K,E(new T2(1,_14v,_14w)),E(_14y)):new T4(0,(_14v>>>0&((_14L-1>>>0^4294967295)>>>0^_14L)>>>0)>>>0&4294967295,_14K,E(_14y),E(new T2(1,_14v,_14w)));}break;case 1:var _14M=_14y.a;if(_14v!=_14M){var _14N=(_14v>>>0^_14M>>>0)>>>0,_14O=(_14N|_14N>>>1)>>>0,_14P=(_14O|_14O>>>2)>>>0,_14Q=(_14P|_14P>>>4)>>>0,_14R=(_14Q|_14Q>>>8)>>>0,_14S=(_14R|_14R>>>16)>>>0,_14T=(_14S^_14S>>>1)>>>0&4294967295,_14U=_14T>>>0;return ((_14v>>>0&_14U)>>>0==0)?new T4(0,(_14v>>>0&((_14U-1>>>0^4294967295)>>>0^_14U)>>>0)>>>0&4294967295,_14T,E(new T2(1,_14v,_14w)),E(_14y)):new T4(0,(_14v>>>0&((_14U-1>>>0^4294967295)>>>0^_14U)>>>0)>>>0&4294967295,_14T,E(_14y),E(new T2(1,_14v,_14w)));}else{return new T2(1,_14v,_14w);}break;default:return new T2(1,_14v,_14w);}},_14V=function(_14W,_14X){var _14Y=function(_14Z){while(1){var _150=E(_14Z);switch(_150._){case 0:var _151=_150.b>>>0;if(((_14W>>>0&((_151-1>>>0^4294967295)>>>0^_151)>>>0)>>>0&4294967295)==_150.a){if(!((_14W>>>0&_151)>>>0)){_14Z=_150.c;continue;}else{_14Z=_150.d;continue;}}else{return __Z;}break;case 1:return (_14W!=_150.a)?__Z:new T1(1,_150.b);default:return __Z;}}};return new F(function(){return _14Y(_14X);});},_152=function(_153,_154,_155,_156){var _157=E(_156);if(!_157._){var _158=new T(function(){var _159=B(_152(_157.a,_157.b,_157.c,_157.d));return new T2(0,_159.a,_159.b);});return new T2(0,new T(function(){return E(E(_158).a);}),new T(function(){return B(_MQ(_154,_155,E(_158).b));}));}else{return new T2(0,_154,_155);}},_15a=function(_15b,_15c,_15d,_15e){var _15f=E(_15d);if(!_15f._){var _15g=new T(function(){var _15h=B(_15a(_15f.a,_15f.b,_15f.c,_15f.d));return new T2(0,_15h.a,_15h.b);});return new T2(0,new T(function(){return E(E(_15g).a);}),new T(function(){return B(_Ns(_15c,E(_15g).b,_15e));}));}else{return new T2(0,_15c,_15e);}},_15i=function(_15j,_15k){var _15l=E(_15j);if(!_15l._){var _15m=_15l.a,_15n=E(_15k);if(!_15n._){var _15o=_15n.a;if(_15m<=_15o){var _15p=B(_15a(_15o,_15n.b,_15n.c,_15n.d));return new F(function(){return _MQ(_15p.a,_15l,_15p.b);});}else{var _15q=B(_152(_15m,_15l.b,_15l.c,_15l.d));return new F(function(){return _Ns(_15q.a,_15q.b,_15n);});}}else{return E(_15l);}}else{return E(_15k);}},_15r=function(_15s,_15t,_15u,_15v,_15w){var _15x=E(_15s);if(!_15x._){var _15y=_15x.a,_15z=_15x.b,_15A=_15x.c,_15B=_15x.d;if((imul(3,_15y)|0)>=_15t){if((imul(3,_15t)|0)>=_15y){return new F(function(){return _15i(_15x,new T4(0,_15t,E(_15u),E(_15v),E(_15w)));});}else{return new F(function(){return _Ns(_15z,_15A,B(_15r(_15B,_15t,_15u,_15v,_15w)));});}}else{return new F(function(){return _MQ(_15u,B(_15C(_15y,_15z,_15A,_15B,_15v)),_15w);});}}else{return new T4(0,_15t,E(_15u),E(_15v),E(_15w));}},_15C=function(_15D,_15E,_15F,_15G,_15H){var _15I=E(_15H);if(!_15I._){var _15J=_15I.a,_15K=_15I.b,_15L=_15I.c,_15M=_15I.d;if((imul(3,_15D)|0)>=_15J){if((imul(3,_15J)|0)>=_15D){return new F(function(){return _15i(new T4(0,_15D,E(_15E),E(_15F),E(_15G)),_15I);});}else{return new F(function(){return _Ns(_15E,_15F,B(_15r(_15G,_15J,_15K,_15L,_15M)));});}}else{return new F(function(){return _MQ(_15K,B(_15C(_15D,_15E,_15F,_15G,_15L)),_15M);});}}else{return new T4(0,_15D,E(_15E),E(_15F),E(_15G));}},_15N=function(_15O,_15P){var _15Q=E(_15O);if(!_15Q._){var _15R=_15Q.a,_15S=_15Q.b,_15T=_15Q.c,_15U=_15Q.d,_15V=E(_15P);if(!_15V._){var _15W=_15V.a,_15X=_15V.b,_15Y=_15V.c,_15Z=_15V.d;if((imul(3,_15R)|0)>=_15W){if((imul(3,_15W)|0)>=_15R){return new F(function(){return _15i(_15Q,_15V);});}else{return new F(function(){return _Ns(_15S,_15T,B(_15r(_15U,_15W,_15X,_15Y,_15Z)));});}}else{return new F(function(){return _MQ(_15X,B(_15C(_15R,_15S,_15T,_15U,_15Y)),_15Z);});}}else{return E(_15Q);}}else{return E(_15P);}},_160=function(_161,_162){var _163=E(_162);if(!_163._){var _164=_163.b,_165=B(_160(_161,_163.c)),_166=_165.a,_167=_165.b,_168=B(_160(_161,_163.d)),_169=_168.a,_16a=_168.b;return (!B(A1(_161,_164)))?new T2(0,B(_15N(_166,_169)),B(_OM(_164,_167,_16a))):new T2(0,B(_OM(_164,_166,_169)),B(_15N(_167,_16a)));}else{return new T2(0,_ML,_ML);}},_16b=function(_16c,_16d,_16e,_16f){var _16g=E(_16e),_16h=B(_16i(_16c,_16d,_16g.a,_16g.b,_16f));return new T2(0,_16h.a,_16h.b);},_16j=function(_16k,_16l,_16m){while(1){var _16n=E(_16m);if(!_16n._){var _16o=_16n.e;switch(B(A3(_13n,_16k,_16l,_16n.b))){case 0:return new T2(0,B(_13O(_16k,_16l,_16n.d)),_16n);case 1:return new T2(0,new T1(1,_16n.c),_16o);default:_16m=_16o;continue;}}else{return new T2(0,_4l,_Rg);}}},_16p=function(_16q){return E(E(_16q).f);},_16r=function(_16s,_16t,_16u){while(1){var _16v=E(_16u);if(!_16v._){if(!B(A3(_16p,_16s,_16v.b,_16t))){return E(_16v);}else{_16u=_16v.d;continue;}}else{return new T0(1);}}},_16w=function(_16x,_16y,_16z,_16A){while(1){var _16B=E(_16A);if(!_16B._){var _16C=_16B.b,_16D=_16B.d,_16E=_16B.e;switch(B(A3(_13n,_16x,_16y,_16C))){case 0:if(!B(A3(_pK,_16x,_16C,_16z))){_16A=_16D;continue;}else{return new T2(0,B(_13O(_16x,_16y,_16D)),_16B);}break;case 1:return new T2(0,new T1(1,_16B.c),B(_16r(_16x,_16z,_16E)));default:_16A=_16E;continue;}}else{return new T2(0,_4l,_Rg);}}},_16F=function(_16G,_16H,_16I,_16J){var _16K=E(_16I);if(!_16K._){return new F(function(){return _16j(_16G,_16H,_16J);});}else{return new F(function(){return _16w(_16G,_16H,_16K.a,_16J);});}},_16L=__Z,_16M=function(_16N,_16O,_16P){var _16Q=E(_16O);if(!_16Q._){return E(_16P);}else{var _16R=function(_16S,_16T){while(1){var _16U=E(_16T);if(!_16U._){var _16V=_16U.b,_16W=_16U.e;switch(B(A3(_13n,_16N,_16S,_16V))){case 0:return new F(function(){return _Tw(_16V,_16U.c,B(_16R(_16S,_16U.d)),_16W);});break;case 1:return E(_16W);default:_16T=_16W;continue;}}else{return new T0(1);}}};return new F(function(){return _16R(_16Q.a,_16P);});}},_16X=function(_16Y,_16Z,_170){var _171=E(_16Z);if(!_171._){return E(_170);}else{var _172=function(_173,_174){while(1){var _175=E(_174);if(!_175._){var _176=_175.b,_177=_175.d;switch(B(A3(_13n,_16Y,_176,_173))){case 0:return new F(function(){return _Tw(_176,_175.c,_177,B(_172(_173,_175.e)));});break;case 1:return E(_177);default:_174=_177;continue;}}else{return new T0(1);}}};return new F(function(){return _172(_171.a,_170);});}},_178=function(_179){return E(E(_179).d);},_17a=function(_17b,_17c,_17d,_17e){var _17f=E(_17c);if(!_17f._){var _17g=E(_17d);if(!_17g._){return E(_17e);}else{var _17h=function(_17i,_17j){while(1){var _17k=E(_17j);if(!_17k._){if(!B(A3(_16p,_17b,_17k.b,_17i))){return E(_17k);}else{_17j=_17k.d;continue;}}else{return new T0(1);}}};return new F(function(){return _17h(_17g.a,_17e);});}}else{var _17l=_17f.a,_17m=E(_17d);if(!_17m._){var _17n=function(_17o,_17p){while(1){var _17q=E(_17p);if(!_17q._){if(!B(A3(_178,_17b,_17q.b,_17o))){return E(_17q);}else{_17p=_17q.e;continue;}}else{return new T0(1);}}};return new F(function(){return _17n(_17l,_17e);});}else{var _17r=function(_17s,_17t,_17u){while(1){var _17v=E(_17u);if(!_17v._){var _17w=_17v.b;if(!B(A3(_178,_17b,_17w,_17s))){if(!B(A3(_16p,_17b,_17w,_17t))){return E(_17v);}else{_17u=_17v.d;continue;}}else{_17u=_17v.e;continue;}}else{return new T0(1);}}};return new F(function(){return _17r(_17l,_17m.a,_17e);});}}},_17x=function(_17y,_17z,_17A,_17B){var _17C=E(_17A);if(!_17C._){var _17D=E(_17B);if(!_17D._){var _17E=function(_17F,_17G,_17H,_17I){var _17J=E(_17I);if(!_17J._){var _17K=E(_17H);if(!_17K._){var _17L=_17K.b,_17M=_17K.c,_17N=_17K.e,_17O=B(_16F(_17y,_17L,_17G,_17J)),_17P=_17O.b,_17Q=new T1(1,E(_17L)),_17R=B(_17E(_17F,_17Q,_17K.d,B(_17a(_17y,_17F,_17Q,_17J)))),_17S=E(_17O.a);if(!_17S._){return new F(function(){return _Tw(_17L,_17M,_17R,B(_17E(_17Q,_17G,_17N,_17P)));});}else{return new F(function(){return _Tw(_17L,new T(function(){return B(A3(_17z,_17L,_17M,_17S.a));}),_17R,B(_17E(_17Q,_17G,_17N,_17P)));});}}else{return new F(function(){return _Tw(_17J.b,_17J.c,B(_16M(_17y,_17F,_17J.d)),B(_16X(_17y,_17G,_17J.e)));});}}else{return E(_17H);}},_17T=_16L,_17U=_16L,_17V=_17C.a,_17W=_17C.b,_17X=_17C.c,_17Y=_17C.d,_17Z=_17C.e,_180=_17D.a,_181=_17D.b,_182=_17D.c,_183=_17D.d,_184=_17D.e,_185=B(_16F(_17y,_17W,_17U,new T5(0,_180,E(_181),_182,E(_183),E(_184)))),_186=_185.b,_187=new T1(1,E(_17W)),_188=B(_17E(_17T,_187,_17Y,B(_17a(_17y,_17T,_187,new T5(0,_180,E(_181),_182,E(_183),E(_184)))))),_189=E(_185.a);if(!_189._){return new F(function(){return _Tw(_17W,_17X,_188,B(_17E(_187,_17U,_17Z,_186)));});}else{return new F(function(){return _Tw(_17W,new T(function(){return B(A3(_17z,_17W,_17X,_189.a));}),_188,B(_17E(_187,_17U,_17Z,_186)));});}}else{return E(_17C);}}else{return E(_17B);}},_16i=function(_18a,_18b,_18c,_18d,_18e){var _18f=E(_18e),_18g=_18f.a,_18h=new T(function(){return B(_17x(_18a,function(_18i,_18j,_18k){return new F(function(){return _16b(_18a,_18b,_18j,_18k);});},_18d,_18f.b));}),_18l=new T(function(){var _18m=E(_18c);if(!_18m._){return E(_18g);}else{var _18n=E(_18g);if(!_18n._){return E(_18m);}else{return new T1(1,new T(function(){return B(A2(_18b,_18m.a,_18n.a));}));}}});return new T2(0,_18l,_18h);},_18o=function(_18p,_18q,_18r){var _18s=function(_18t,_18u,_18v){while(1){var _18w=E(_18t);if(!_18w._){return new T2(0,_18u,_18v);}else{var _18x=B(_16i(_18p,_18q,_18u,_18v,_18w.a));_18t=_18w.b;_18u=_18x.a;_18v=_18x.b;continue;}}};return new F(function(){return _18s(_18r,_4l,_Rg);});},_18y=new T0(2),_18z=function(_18A,_18B){var _18C=E(_18A),_18D=E(_18B);return new F(function(){return _12M(_18C.a,_18C.b,_18C.c,_18D.a,_18D.b,_18D.c);});},_18E=function(_18F,_18G){return E(_18F)==E(_18G);},_18H=function(_18I,_18J){var _18K=E(_18I);switch(_18K._){case 0:var _18L=E(_18J);if(!_18L._){return new F(function(){return _sf(_18K.a,_18L.a);});}else{return false;}break;case 1:var _18M=E(_18J);if(_18M._==1){return new F(function(){return _iV(_18K.a,_18M.a);});}else{return false;}break;default:var _18N=E(_18J);if(_18N._==2){return new F(function(){return _18E(_18K.a,_18N.a);});}else{return false;}}},_18O=function(_18P,_18Q,_18R){while(1){var _18S=E(_18Q);if(!_18S._){return (E(_18R)._==0)?true:false;}else{var _18T=E(_18R);if(!_18T._){return false;}else{if(!B(A3(_pM,_18P,_18S.a,_18T.a))){return false;}else{_18Q=_18S.b;_18R=_18T.b;continue;}}}}},_18U=function(_18V,_18W){return (!B(_18X(_18V,_18W)))?true:false;},_18Y=new T2(0,_18X,_18U),_18Z=new T(function(){return E(_18Y);}),_190=function(_191,_192){return (E(_191)==0)?(E(_192)==0)?false:true:(E(_192)==0)?true:false;},_193=function(_194,_195){return (E(_194)==0)?(E(_195)==0)?true:false:(E(_195)==0)?false:true;},_196=new T2(0,_193,_190),_197=new T(function(){return E(_196);}),_198=function(_199,_19a,_19b,_19c,_19d,_19e){if(!B(A3(_pM,_197,_199,_19c))){return false;}else{var _19f=E(_19a),_19g=E(_19d);if(!B(_12M(_19f.a,_19f.b,_19f.c,_19g.a,_19g.b,_19g.c))){return false;}else{return new F(function(){return _19h(_19b,_19e);});}}},_19i=function(_19j,_19k){var _19l=E(_19j),_19m=E(_19k);return new F(function(){return _198(_19l.a,_19l.b,_19l.c,_19m.a,_19m.b,_19m.c);});},_19n=function(_19o,_19p,_19q,_19r,_19s,_19t){if(!B(A3(_pM,_197,_19o,_19r))){return true;}else{var _19u=E(_19p),_19v=E(_19s);if(!B(_12M(_19u.a,_19u.b,_19u.c,_19v.a,_19v.b,_19v.c))){return true;}else{var _19w=E(_19q);return (!B(_19x(_19w.a,_19w.b,_19w.c,_19t)))?true:false;}}},_19y=function(_19z,_19A){var _19B=E(_19z),_19C=E(_19A);return new F(function(){return _19n(_19B.a,_19B.b,_19B.c,_19C.a,_19C.b,_19C.c);});},_19D=new T(function(){return new T2(0,_19i,_19y);}),_19x=function(_19E,_19F,_19G,_19H){var _19I=E(_19H);if(!B(_18O(_19D,_19E,_19I.a))){return false;}else{var _19J=E(_19F),_19K=E(_19I.b);if(!B(_12M(_19J.a,_19J.b,_19J.c,_19K.a,_19K.b,_19K.c))){return false;}else{return new F(function(){return _18O(_18Z,_19G,_19I.c);});}}},_19h=function(_19L,_19M){var _19N=E(_19L);return new F(function(){return _19x(_19N.a,_19N.b,_19N.c,_19M);});},_18X=function(_19O,_19P){while(1){var _19Q=E(_19O);switch(_19Q._){case 0:var _19R=_19Q.b,_19S=_19Q.c,_19T=E(_19P);if(!_19T._){var _19U=_19T.a,_19V=_19T.b,_19W=_19T.c;if(!E(_19Q.a)){if(!E(_19U)){var _19X=E(_19R),_19Y=E(_19V);if(!B(_12M(_19X.a,_19X.b,_19X.c,_19Y.a,_19Y.b,_19Y.c))){return false;}else{_19O=_19S;_19P=_19W;continue;}}else{return false;}}else{if(!E(_19U)){return false;}else{var _19Z=E(_19R),_1a0=E(_19V);if(!B(_12M(_19Z.a,_19Z.b,_19Z.c,_1a0.a,_1a0.b,_1a0.c))){return false;}else{_19O=_19S;_19P=_19W;continue;}}}}else{return false;}break;case 1:var _1a1=E(_19P);if(_1a1._==1){if(!B(_18X(_19Q.a,_1a1.a))){return false;}else{_19O=_19Q.b;_19P=_1a1.b;continue;}}else{return false;}break;case 2:var _1a2=E(_19P);if(_1a2._==2){return new F(function(){return _18H(_19Q.a,_1a2.a);});}else{return false;}break;case 3:var _1a3=E(_19P);return (_1a3._==3)?_19Q.a==_1a3.a:false;case 4:var _1a4=E(_19P);if(_1a4._==4){return new F(function(){return _18z(_19Q.a,_1a4.a);});}else{return false;}break;case 5:var _1a5=E(_19P);return (_1a5._==5)?_19Q.a==_1a5.a:false;case 6:var _1a6=E(_19P);if(_1a6._==6){if(!B(_18X(_19Q.a,_1a6.a))){return false;}else{return new F(function(){return _19h(_19Q.b,_1a6.b);});}}else{return false;}break;default:var _1a7=E(_19P);if(_1a7._==7){_19O=_19Q.a;_19P=_1a7.a;continue;}else{return false;}}}},_1a8=function(_1a9,_1aa,_1ab,_1ac){return (_1a9!=_1ab)?true:(E(_1aa)!=E(_1ac))?true:false;},_1ad=function(_1ae,_1af){var _1ag=E(_1ae),_1ah=E(_1af);return new F(function(){return _1a8(E(_1ag.a),_1ag.b,E(_1ah.a),_1ah.b);});},_1ai=function(_1aj,_1ak,_1al,_1am){if(_1aj!=_1al){return false;}else{return new F(function(){return _iV(_1ak,_1am);});}},_1an=function(_1ao,_1ap){var _1aq=E(_1ao),_1ar=E(_1ap);return new F(function(){return _1ai(E(_1aq.a),_1aq.b,E(_1ar.a),_1ar.b);});},_1as=new T2(0,_1an,_1ad),_1at=function(_1au,_1av,_1aw,_1ax){return (!B(_18O(_1as,_1au,_1aw)))?true:(_1av!=_1ax)?true:false;},_1ay=function(_1az,_1aA){var _1aB=E(_1az),_1aC=E(_1aA);return new F(function(){return _1at(_1aB.a,_1aB.b,_1aC.a,_1aC.b);});},_1aD=function(_1aE,_1aF){var _1aG=E(_1aE),_1aH=E(_1aF);return (!B(_18O(_1as,_1aG.a,_1aH.a)))?false:_1aG.b==_1aH.b;},_1aI=new T2(0,_1aD,_1ay),_1aJ=function(_1aK,_1aL){while(1){var _1aM=E(_1aK);if(!_1aM._){return (E(_1aL)._==0)?true:false;}else{var _1aN=E(_1aL);if(!_1aN._){return false;}else{if(!B(_sr(_1aM.a,_1aN.a))){return false;}else{_1aK=_1aM.b;_1aL=_1aN.b;continue;}}}}},_1aO=function(_1aP,_1aQ){var _1aR=E(_1aP);switch(_1aR._){case 0:var _1aS=E(_1aQ);if(!_1aS._){if(_1aR.a!=_1aS.a){return false;}else{return new F(function(){return _18O(_1aI,_1aR.b,_1aS.b);});}}else{return false;}break;case 1:var _1aT=E(_1aQ);return (_1aT._==1)?_1aR.a==_1aT.a:false;default:var _1aU=E(_1aQ);if(_1aU._==2){var _1aV=E(_1aR.a),_1aW=E(_1aU.a);if(!B(_12M(_1aV.a,_1aV.b,_1aV.c,_1aW.a,_1aW.b,_1aW.c))){return false;}else{if(!B(_18X(_1aR.b,_1aU.b))){return false;}else{return new F(function(){return _1aJ(_1aR.c,_1aU.c);});}}}else{return false;}}},_1aX=function(_1aY,_1aZ){return (!B(_1aO(_1aY,_1aZ)))?true:false;},_1b0=new T2(0,_1aO,_1aX),_1b1=function(_1b2,_1b3){var _1b4=E(_1b2),_1b5=E(_1b3);return new F(function(){return _12T(_1b4.a,_1b4.b,_1b4.c,_1b5.a,_1b5.b,_1b5.c);});},_1b6=function(_1b7,_1b8){var _1b9=E(_1b7),_1ba=E(_1b8);return (_1b9>=_1ba)?(_1b9!=_1ba)?2:1:0;},_1bb=function(_1bc,_1bd){var _1be=E(_1bc);switch(_1be._){case 0:var _1bf=E(_1bd);if(!_1bf._){return new F(function(){return _12d(_1be.a,_1bf.a);});}else{return 0;}break;case 1:var _1bg=E(_1bd);switch(_1bg._){case 0:return 2;case 1:return new F(function(){return _jf(_1be.a,_1bg.a);});break;default:return 0;}break;default:var _1bh=E(_1bd);if(_1bh._==2){return new F(function(){return _1b6(_1be.a,_1bh.a);});}else{return 2;}}},_1bi=function(_1bj,_1bk){return (B(_1bl(_1bj,_1bk))==0)?true:false;},_1bm=function(_1bn,_1bo){return (B(_1bl(_1bn,_1bo))==2)?false:true;},_1bp=function(_1bq,_1br){return (B(_1bl(_1bq,_1br))==2)?true:false;},_1bs=function(_1bt,_1bu){return (B(_1bl(_1bt,_1bu))==0)?false:true;},_1bv=function(_1bw,_1bx){return (B(_1bl(_1bw,_1bx))==2)?E(_1bw):E(_1bx);},_1by=function(_1bz,_1bA){return (B(_1bl(_1bz,_1bA))==2)?E(_1bA):E(_1bz);},_1bB={_:0,a:_18Y,b:_1bl,c:_1bi,d:_1bm,e:_1bp,f:_1bs,g:_1bv,h:_1by},_1bC=new T(function(){return E(_1bB);}),_1bD=function(_1bE,_1bF,_1bG){while(1){var _1bH=E(_1bF);if(!_1bH._){return (E(_1bG)._==0)?1:0;}else{var _1bI=E(_1bG);if(!_1bI._){return 2;}else{var _1bJ=B(A3(_13n,_1bE,_1bH.a,_1bI.a));if(_1bJ==1){_1bF=_1bH.b;_1bG=_1bI.b;continue;}else{return E(_1bJ);}}}}},_1bK=function(_1bL,_1bM,_1bN,_1bO){var _1bP=E(_1bO);switch(B(_1bD(_1bQ,_1bL,_1bP.a))){case 0:return false;case 1:var _1bR=E(_1bM),_1bS=E(_1bP.b);switch(B(_12T(_1bR.a,_1bR.b,_1bR.c,_1bS.a,_1bS.b,_1bS.c))){case 0:return false;case 1:return (B(_1bD(_1bC,_1bN,_1bP.c))==0)?false:true;default:return true;}break;default:return true;}},_1bT=function(_1bU,_1bV){var _1bW=E(_1bU);return new F(function(){return _1bK(_1bW.a,_1bW.b,_1bW.c,_1bV);});},_1bX=function(_1bY,_1bZ){if(!E(_1bY)){return (E(_1bZ)==0)?false:true;}else{var _1c0=E(_1bZ);return false;}},_1c1=function(_1c2,_1c3){if(!E(_1c2)){var _1c4=E(_1c3);return true;}else{return (E(_1c3)==0)?false:true;}},_1c5=function(_1c6,_1c7){if(!E(_1c6)){var _1c8=E(_1c7);return false;}else{return (E(_1c7)==0)?true:false;}},_1c9=function(_1ca,_1cb){if(!E(_1ca)){return (E(_1cb)==0)?true:false;}else{var _1cc=E(_1cb);return true;}},_1cd=function(_1ce,_1cf){return (E(_1ce)==0)?(E(_1cf)==0)?1:0:(E(_1cf)==0)?2:1;},_1cg=function(_1ch,_1ci){if(!E(_1ch)){return E(_1ci);}else{var _1cj=E(_1ci);return 1;}},_1ck=function(_1cl,_1cm){if(!E(_1cl)){var _1cn=E(_1cm);return 0;}else{return E(_1cm);}},_1co={_:0,a:_196,b:_1cd,c:_1bX,d:_1c1,e:_1c5,f:_1c9,g:_1cg,h:_1ck},_1cp=new T(function(){return E(_1co);}),_1cq=function(_1cr,_1cs,_1ct,_1cu,_1cv,_1cw){switch(B(A3(_13n,_1cp,_1cr,_1cu))){case 0:return false;case 1:var _1cx=E(_1cs),_1cy=E(_1cv);switch(B(_12T(_1cx.a,_1cx.b,_1cx.c,_1cy.a,_1cy.b,_1cy.c))){case 0:return false;case 1:return new F(function(){return _1bT(_1ct,_1cw);});break;default:return true;}break;default:return true;}},_1cz=function(_1cA,_1cB){var _1cC=E(_1cA),_1cD=E(_1cB);return new F(function(){return _1cq(_1cC.a,_1cC.b,_1cC.c,_1cD.a,_1cD.b,_1cD.c);});},_1cE=function(_1cF,_1cG,_1cH,_1cI){var _1cJ=E(_1cI);switch(B(_1bD(_1bQ,_1cF,_1cJ.a))){case 0:return false;case 1:var _1cK=E(_1cG),_1cL=E(_1cJ.b);switch(B(_12T(_1cK.a,_1cK.b,_1cK.c,_1cL.a,_1cL.b,_1cL.c))){case 0:return false;case 1:return (B(_1bD(_1bC,_1cH,_1cJ.c))==2)?true:false;default:return true;}break;default:return true;}},_1cM=function(_1cN,_1cO){var _1cP=E(_1cN);return new F(function(){return _1cE(_1cP.a,_1cP.b,_1cP.c,_1cO);});},_1cQ=function(_1cR,_1cS,_1cT,_1cU,_1cV,_1cW){switch(B(A3(_13n,_1cp,_1cR,_1cU))){case 0:return false;case 1:var _1cX=E(_1cS),_1cY=E(_1cV);switch(B(_12T(_1cX.a,_1cX.b,_1cX.c,_1cY.a,_1cY.b,_1cY.c))){case 0:return false;case 1:return new F(function(){return _1cM(_1cT,_1cW);});break;default:return true;}break;default:return true;}},_1cZ=function(_1d0,_1d1){var _1d2=E(_1d0),_1d3=E(_1d1);return new F(function(){return _1cQ(_1d2.a,_1d2.b,_1d2.c,_1d3.a,_1d3.b,_1d3.c);});},_1d4=function(_1d5,_1d6,_1d7,_1d8){var _1d9=E(_1d8);switch(B(_1bD(_1bQ,_1d5,_1d9.a))){case 0:return true;case 1:var _1da=E(_1d6),_1db=E(_1d9.b);switch(B(_12T(_1da.a,_1da.b,_1da.c,_1db.a,_1db.b,_1db.c))){case 0:return true;case 1:return (B(_1bD(_1bC,_1d7,_1d9.c))==2)?false:true;default:return false;}break;default:return false;}},_1dc=function(_1dd,_1de){var _1df=E(_1dd);return new F(function(){return _1d4(_1df.a,_1df.b,_1df.c,_1de);});},_1dg=function(_1dh,_1di,_1dj,_1dk,_1dl,_1dm){switch(B(A3(_13n,_1cp,_1dh,_1dk))){case 0:return true;case 1:var _1dn=E(_1di),_1do=E(_1dl);switch(B(_12T(_1dn.a,_1dn.b,_1dn.c,_1do.a,_1do.b,_1do.c))){case 0:return true;case 1:return new F(function(){return _1dc(_1dj,_1dm);});break;default:return false;}break;default:return false;}},_1dp=function(_1dq,_1dr){var _1ds=E(_1dq),_1dt=E(_1dr);return new F(function(){return _1dg(_1ds.a,_1ds.b,_1ds.c,_1dt.a,_1dt.b,_1dt.c);});},_1du=function(_1dv,_1dw){var _1dx=E(_1dv),_1dy=_1dx.a,_1dz=_1dx.c,_1dA=E(_1dw),_1dB=_1dA.a,_1dC=_1dA.c;switch(B(A3(_13n,_1cp,_1dy,_1dB))){case 0:return E(_1dA);case 1:var _1dD=E(_1dx.b),_1dE=E(_1dA.b);switch(B(_12T(_1dD.a,_1dD.b,_1dD.c,_1dE.a,_1dE.b,_1dE.c))){case 0:return new T3(0,_1dB,_1dE,_1dC);case 1:var _1dF=E(_1dz);return (!B(_1d4(_1dF.a,_1dF.b,_1dF.c,_1dC)))?new T3(0,_1dy,_1dD,_1dF):new T3(0,_1dB,_1dE,_1dC);default:return new T3(0,_1dy,_1dD,_1dz);}break;default:return E(_1dx);}},_1dG=function(_1dH,_1dI){var _1dJ=E(_1dH),_1dK=_1dJ.a,_1dL=_1dJ.c,_1dM=E(_1dI),_1dN=_1dM.a,_1dO=_1dM.c;switch(B(A3(_13n,_1cp,_1dK,_1dN))){case 0:return E(_1dJ);case 1:var _1dP=E(_1dJ.b),_1dQ=E(_1dM.b);switch(B(_12T(_1dP.a,_1dP.b,_1dP.c,_1dQ.a,_1dQ.b,_1dQ.c))){case 0:return new T3(0,_1dK,_1dP,_1dL);case 1:var _1dR=E(_1dL);return (!B(_1d4(_1dR.a,_1dR.b,_1dR.c,_1dO)))?new T3(0,_1dN,_1dQ,_1dO):new T3(0,_1dK,_1dP,_1dR);default:return new T3(0,_1dN,_1dQ,_1dO);}break;default:return E(_1dM);}},_1dS=function(_1dT,_1dU,_1dV,_1dW){var _1dX=E(_1dW);switch(B(_1bD(_1bQ,_1dT,_1dX.a))){case 0:return true;case 1:var _1dY=E(_1dU),_1dZ=E(_1dX.b);switch(B(_12T(_1dY.a,_1dY.b,_1dY.c,_1dZ.a,_1dZ.b,_1dZ.c))){case 0:return true;case 1:return (B(_1bD(_1bC,_1dV,_1dX.c))==0)?true:false;default:return false;}break;default:return false;}},_1e0=function(_1e1,_1e2){var _1e3=E(_1e1);return new F(function(){return _1dS(_1e3.a,_1e3.b,_1e3.c,_1e2);});},_1e4=function(_1e5,_1e6,_1e7,_1e8,_1e9,_1ea){switch(B(A3(_13n,_1cp,_1e5,_1e8))){case 0:return true;case 1:var _1eb=E(_1e6),_1ec=E(_1e9);switch(B(_12T(_1eb.a,_1eb.b,_1eb.c,_1ec.a,_1ec.b,_1ec.c))){case 0:return true;case 1:return new F(function(){return _1e0(_1e7,_1ea);});break;default:return false;}break;default:return false;}},_1ed=function(_1ee,_1ef){var _1eg=E(_1ee),_1eh=E(_1ef);return new F(function(){return _1e4(_1eg.a,_1eg.b,_1eg.c,_1eh.a,_1eh.b,_1eh.c);});},_1ei=function(_1ej,_1ek,_1el,_1em,_1en,_1eo){switch(B(A3(_13n,_1cp,_1ej,_1em))){case 0:return 0;case 1:var _1ep=E(_1ek),_1eq=E(_1en);switch(B(_12T(_1ep.a,_1ep.b,_1ep.c,_1eq.a,_1eq.b,_1eq.c))){case 0:return 0;case 1:return new F(function(){return _1er(_1el,_1eo);});break;default:return 2;}break;default:return 2;}},_1es=function(_1et,_1eu){var _1ev=E(_1et),_1ew=E(_1eu);return new F(function(){return _1ei(_1ev.a,_1ev.b,_1ev.c,_1ew.a,_1ew.b,_1ew.c);});},_1bQ=new T(function(){return {_:0,a:_19D,b:_1es,c:_1ed,d:_1dp,e:_1cZ,f:_1cz,g:_1du,h:_1dG};}),_1ex=function(_1ey,_1ez,_1eA,_1eB){var _1eC=E(_1eB);switch(B(_1bD(_1bQ,_1ey,_1eC.a))){case 0:return 0;case 1:var _1eD=E(_1ez),_1eE=E(_1eC.b);switch(B(_12T(_1eD.a,_1eD.b,_1eD.c,_1eE.a,_1eE.b,_1eE.c))){case 0:return 0;case 1:return new F(function(){return _1bD(_1bC,_1eA,_1eC.c);});break;default:return 2;}break;default:return 2;}},_1er=function(_1eF,_1eG){var _1eH=E(_1eF);return new F(function(){return _1ex(_1eH.a,_1eH.b,_1eH.c,_1eG);});},_1bl=function(_1eI,_1eJ){while(1){var _1eK=B((function(_1eL,_1eM){var _1eN=E(_1eL);switch(_1eN._){case 0:var _1eO=E(_1eM);if(!_1eO._){var _1eP=_1eO.a,_1eQ=function(_1eR){var _1eS=E(_1eN.b),_1eT=E(_1eO.b);switch(B(_12T(_1eS.a,_1eS.b,_1eS.c,_1eT.a,_1eT.b,_1eT.c))){case 0:return 0;case 1:return new F(function(){return _1bl(_1eN.c,_1eO.c);});break;default:return 2;}};if(!E(_1eN.a)){if(!E(_1eP)){return new F(function(){return _1eQ(_);});}else{return 0;}}else{if(!E(_1eP)){return 2;}else{return new F(function(){return _1eQ(_);});}}}else{return 0;}break;case 1:var _1eU=E(_1eM);switch(_1eU._){case 0:return 2;case 1:switch(B(_1bl(_1eN.a,_1eU.a))){case 0:return 0;case 1:_1eI=_1eN.b;_1eJ=_1eU.b;return __continue;default:return 2;}break;default:return 0;}break;case 2:var _1eV=E(_1eM);switch(_1eV._){case 2:return new F(function(){return _1bb(_1eN.a,_1eV.a);});break;case 3:return 0;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 3:var _1eW=E(_1eM);switch(_1eW._){case 3:return new F(function(){return _jc(_1eN.a,_1eW.a);});break;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 4:var _1eX=E(_1eM);switch(_1eX._){case 4:return new F(function(){return _1b1(_1eN.a,_1eX.a);});break;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 5:var _1eY=E(_1eM);switch(_1eY._){case 5:return new F(function(){return _jc(_1eN.a,_1eY.a);});break;case 6:return 0;case 7:return 0;default:return 2;}break;case 6:var _1eZ=E(_1eM);switch(_1eZ._){case 6:switch(B(_1bl(_1eN.a,_1eZ.a))){case 0:return 0;case 1:return new F(function(){return _1er(_1eN.b,_1eZ.b);});break;default:return 2;}break;case 7:return 0;default:return 2;}break;default:var _1f0=E(_1eM);if(_1f0._==7){_1eI=_1eN.a;_1eJ=_1f0.a;return __continue;}else{return 2;}}})(_1eI,_1eJ));if(_1eK!=__continue){return _1eK;}}},_1f1=function(_1f2,_1f3,_1f4,_1f5){if(_1f2>=_1f4){if(_1f2!=_1f4){return 2;}else{return new F(function(){return _jf(_1f3,_1f5);});}}else{return 0;}},_1f6=function(_1f7,_1f8){var _1f9=E(_1f7),_1fa=E(_1f8);return new F(function(){return _1f1(E(_1f9.a),_1f9.b,E(_1fa.a),_1fa.b);});},_1fb=function(_1fc,_1fd,_1fe,_1ff){if(_1fc>=_1fe){if(_1fc!=_1fe){return false;}else{return new F(function(){return _jr(_1fd,_1ff);});}}else{return true;}},_1fg=function(_1fh,_1fi){var _1fj=E(_1fh),_1fk=E(_1fi);return new F(function(){return _1fb(E(_1fj.a),_1fj.b,E(_1fk.a),_1fk.b);});},_1fl=function(_1fm,_1fn,_1fo,_1fp){if(_1fm>=_1fo){if(_1fm!=_1fo){return false;}else{return new F(function(){return _jo(_1fn,_1fp);});}}else{return true;}},_1fq=function(_1fr,_1fs){var _1ft=E(_1fr),_1fu=E(_1fs);return new F(function(){return _1fl(E(_1ft.a),_1ft.b,E(_1fu.a),_1fu.b);});},_1fv=function(_1fw,_1fx,_1fy,_1fz){if(_1fw>=_1fy){if(_1fw!=_1fy){return true;}else{return new F(function(){return _jl(_1fx,_1fz);});}}else{return false;}},_1fA=function(_1fB,_1fC){var _1fD=E(_1fB),_1fE=E(_1fC);return new F(function(){return _1fv(E(_1fD.a),_1fD.b,E(_1fE.a),_1fE.b);});},_1fF=function(_1fG,_1fH,_1fI,_1fJ){if(_1fG>=_1fI){if(_1fG!=_1fI){return true;}else{return new F(function(){return _ji(_1fH,_1fJ);});}}else{return false;}},_1fK=function(_1fL,_1fM){var _1fN=E(_1fL),_1fO=E(_1fM);return new F(function(){return _1fF(E(_1fN.a),_1fN.b,E(_1fO.a),_1fO.b);});},_1fP=function(_1fQ,_1fR){var _1fS=E(_1fQ),_1fT=E(_1fS.a),_1fU=E(_1fR),_1fV=E(_1fU.a);return (_1fT>=_1fV)?(_1fT!=_1fV)?E(_1fS):(E(_1fS.b)>E(_1fU.b))?E(_1fS):E(_1fU):E(_1fU);},_1fW=function(_1fX,_1fY){var _1fZ=E(_1fX),_1g0=E(_1fZ.a),_1g1=E(_1fY),_1g2=E(_1g1.a);return (_1g0>=_1g2)?(_1g0!=_1g2)?E(_1g1):(E(_1fZ.b)>E(_1g1.b))?E(_1g1):E(_1fZ):E(_1fZ);},_1g3={_:0,a:_1as,b:_1f6,c:_1fg,d:_1fq,e:_1fA,f:_1fK,g:_1fP,h:_1fW},_1g4=function(_1g5,_1g6,_1g7,_1g8){switch(B(_1bD(_1g3,_1g5,_1g7))){case 0:return true;case 1:return _1g6<_1g8;default:return false;}},_1g9=function(_1ga,_1gb){var _1gc=E(_1ga),_1gd=E(_1gb);return new F(function(){return _1g4(_1gc.a,_1gc.b,_1gd.a,_1gd.b);});},_1ge=function(_1gf,_1gg,_1gh,_1gi){switch(B(_1bD(_1g3,_1gf,_1gh))){case 0:return true;case 1:return _1gg<=_1gi;default:return false;}},_1gj=function(_1gk,_1gl){var _1gm=E(_1gk),_1gn=E(_1gl);return new F(function(){return _1ge(_1gm.a,_1gm.b,_1gn.a,_1gn.b);});},_1go=function(_1gp,_1gq,_1gr,_1gs){switch(B(_1bD(_1g3,_1gp,_1gr))){case 0:return false;case 1:return _1gq>_1gs;default:return true;}},_1gt=function(_1gu,_1gv){var _1gw=E(_1gu),_1gx=E(_1gv);return new F(function(){return _1go(_1gw.a,_1gw.b,_1gx.a,_1gx.b);});},_1gy=function(_1gz,_1gA,_1gB,_1gC){switch(B(_1bD(_1g3,_1gz,_1gB))){case 0:return false;case 1:return _1gA>=_1gC;default:return true;}},_1gD=function(_1gE,_1gF){var _1gG=E(_1gE),_1gH=E(_1gF);return new F(function(){return _1gy(_1gG.a,_1gG.b,_1gH.a,_1gH.b);});},_1gI=function(_1gJ,_1gK,_1gL,_1gM){switch(B(_1bD(_1g3,_1gJ,_1gL))){case 0:return 0;case 1:return new F(function(){return _jc(_1gK,_1gM);});break;default:return 2;}},_1gN=function(_1gO,_1gP){var _1gQ=E(_1gO),_1gR=E(_1gP);return new F(function(){return _1gI(_1gQ.a,_1gQ.b,_1gR.a,_1gR.b);});},_1gS=function(_1gT,_1gU){var _1gV=E(_1gT),_1gW=E(_1gU);switch(B(_1bD(_1g3,_1gV.a,_1gW.a))){case 0:return E(_1gW);case 1:return (_1gV.b>_1gW.b)?E(_1gV):E(_1gW);default:return E(_1gV);}},_1gX=function(_1gY,_1gZ){var _1h0=E(_1gY),_1h1=E(_1gZ);switch(B(_1bD(_1g3,_1h0.a,_1h1.a))){case 0:return E(_1h0);case 1:return (_1h0.b>_1h1.b)?E(_1h1):E(_1h0);default:return E(_1h1);}},_1h2={_:0,a:_1aI,b:_1gN,c:_1g9,d:_1gj,e:_1gt,f:_1gD,g:_1gS,h:_1gX},_1h3=function(_1h4,_1h5){while(1){var _1h6=E(_1h4);if(!_1h6._){return (E(_1h5)._==0)?1:0;}else{var _1h7=E(_1h5);if(!_1h7._){return 2;}else{var _1h8=B(_12d(_1h6.a,_1h7.a));if(_1h8==1){_1h4=_1h6.b;_1h5=_1h7.b;continue;}else{return E(_1h8);}}}}},_1h9=function(_1ha,_1hb){return (B(_1h3(_1ha,_1hb))==0)?true:false;},_1hc=function(_1hd,_1he){var _1hf=E(_1hd);switch(_1hf._){case 0:var _1hg=_1hf.a,_1hh=E(_1he);if(!_1hh._){var _1hi=_1hh.a;return (_1hg>=_1hi)?(_1hg!=_1hi)?false:(B(_1bD(_1h2,_1hf.b,_1hh.b))==0)?true:false:true;}else{return true;}break;case 1:var _1hj=E(_1he);switch(_1hj._){case 0:return false;case 1:return _1hf.a<_1hj.a;default:return true;}break;default:var _1hk=E(_1he);if(_1hk._==2){var _1hl=E(_1hf.a),_1hm=E(_1hk.a);switch(B(_12T(_1hl.a,_1hl.b,_1hl.c,_1hm.a,_1hm.b,_1hm.c))){case 0:return true;case 1:switch(B(_1bl(_1hf.b,_1hk.b))){case 0:return true;case 1:return new F(function(){return _1h9(_1hf.c,_1hk.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1hn=function(_1ho,_1hp){return (B(_1h3(_1ho,_1hp))==2)?false:true;},_1hq=function(_1hr,_1hs){var _1ht=E(_1hr);switch(_1ht._){case 0:var _1hu=_1ht.a,_1hv=E(_1hs);if(!_1hv._){var _1hw=_1hv.a;return (_1hu>=_1hw)?(_1hu!=_1hw)?false:(B(_1bD(_1h2,_1ht.b,_1hv.b))==2)?false:true:true;}else{return true;}break;case 1:var _1hx=E(_1hs);switch(_1hx._){case 0:return false;case 1:return _1ht.a<=_1hx.a;default:return true;}break;default:var _1hy=E(_1hs);if(_1hy._==2){var _1hz=E(_1ht.a),_1hA=E(_1hy.a);switch(B(_12T(_1hz.a,_1hz.b,_1hz.c,_1hA.a,_1hA.b,_1hA.c))){case 0:return true;case 1:switch(B(_1bl(_1ht.b,_1hy.b))){case 0:return true;case 1:return new F(function(){return _1hn(_1ht.c,_1hy.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1hB=function(_1hC,_1hD){return (B(_1h3(_1hC,_1hD))==2)?true:false;},_1hE=function(_1hF,_1hG){var _1hH=E(_1hF);switch(_1hH._){case 0:var _1hI=_1hH.a,_1hJ=E(_1hG);if(!_1hJ._){var _1hK=_1hJ.a;return (_1hI>=_1hK)?(_1hI!=_1hK)?true:(B(_1bD(_1h2,_1hH.b,_1hJ.b))==2)?true:false:false;}else{return false;}break;case 1:var _1hL=E(_1hG);switch(_1hL._){case 0:return true;case 1:return _1hH.a>_1hL.a;default:return false;}break;default:var _1hM=E(_1hG);if(_1hM._==2){var _1hN=E(_1hH.a),_1hO=E(_1hM.a);switch(B(_12T(_1hN.a,_1hN.b,_1hN.c,_1hO.a,_1hO.b,_1hO.c))){case 0:return false;case 1:switch(B(_1bl(_1hH.b,_1hM.b))){case 0:return false;case 1:return new F(function(){return _1hB(_1hH.c,_1hM.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1hP=function(_1hQ,_1hR){return (B(_1h3(_1hQ,_1hR))==0)?false:true;},_1hS=function(_1hT,_1hU){var _1hV=E(_1hT);switch(_1hV._){case 0:var _1hW=_1hV.a,_1hX=E(_1hU);if(!_1hX._){var _1hY=_1hX.a;return (_1hW>=_1hY)?(_1hW!=_1hY)?true:(B(_1bD(_1h2,_1hV.b,_1hX.b))==0)?false:true:false;}else{return false;}break;case 1:var _1hZ=E(_1hU);switch(_1hZ._){case 0:return true;case 1:return _1hV.a>=_1hZ.a;default:return false;}break;default:var _1i0=E(_1hU);if(_1i0._==2){var _1i1=E(_1hV.a),_1i2=E(_1i0.a);switch(B(_12T(_1i1.a,_1i1.b,_1i1.c,_1i2.a,_1i2.b,_1i2.c))){case 0:return false;case 1:switch(B(_1bl(_1hV.b,_1i0.b))){case 0:return false;case 1:return new F(function(){return _1hP(_1hV.c,_1i0.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1i3=function(_1i4,_1i5){var _1i6=E(_1i4);switch(_1i6._){case 0:var _1i7=_1i6.a,_1i8=E(_1i5);if(!_1i8._){var _1i9=_1i8.a;if(_1i7>=_1i9){if(_1i7!=_1i9){return 2;}else{return new F(function(){return _1bD(_1h2,_1i6.b,_1i8.b);});}}else{return 0;}}else{return 0;}break;case 1:var _1ia=E(_1i5);switch(_1ia._){case 0:return 2;case 1:return new F(function(){return _jc(_1i6.a,_1ia.a);});break;default:return 0;}break;default:var _1ib=E(_1i5);if(_1ib._==2){var _1ic=E(_1i6.a),_1id=E(_1ib.a);switch(B(_12T(_1ic.a,_1ic.b,_1ic.c,_1id.a,_1id.b,_1id.c))){case 0:return 0;case 1:switch(B(_1bl(_1i6.b,_1ib.b))){case 0:return 0;case 1:return new F(function(){return _1h3(_1i6.c,_1ib.c);});break;default:return 2;}break;default:return 2;}}else{return 2;}}},_1ie=function(_1if,_1ig){return (!B(_1hq(_1if,_1ig)))?E(_1if):E(_1ig);},_1ih=function(_1ii,_1ij){return (!B(_1hq(_1ii,_1ij)))?E(_1ij):E(_1ii);},_1ik={_:0,a:_1b0,b:_1i3,c:_1hc,d:_1hq,e:_1hE,f:_1hS,g:_1ie,h:_1ih},_1il=__Z,_1im=function(_1in,_1io,_1ip){var _1iq=E(_1io);if(!_1iq._){return E(_1ip);}else{var _1ir=function(_1is,_1it){while(1){var _1iu=E(_1it);if(!_1iu._){var _1iv=_1iu.b,_1iw=_1iu.d;switch(B(A3(_13n,_1in,_1is,_1iv))){case 0:return new F(function(){return _OM(_1iv,B(_1ir(_1is,_1iu.c)),_1iw);});break;case 1:return E(_1iw);default:_1it=_1iw;continue;}}else{return new T0(1);}}};return new F(function(){return _1ir(_1iq.a,_1ip);});}},_1ix=function(_1iy,_1iz,_1iA){var _1iB=E(_1iz);if(!_1iB._){return E(_1iA);}else{var _1iC=function(_1iD,_1iE){while(1){var _1iF=E(_1iE);if(!_1iF._){var _1iG=_1iF.b,_1iH=_1iF.c;switch(B(A3(_13n,_1iy,_1iG,_1iD))){case 0:return new F(function(){return _OM(_1iG,_1iH,B(_1iC(_1iD,_1iF.d)));});break;case 1:return E(_1iH);default:_1iE=_1iH;continue;}}else{return new T0(1);}}};return new F(function(){return _1iC(_1iB.a,_1iA);});}},_1iI=function(_1iJ,_1iK,_1iL){var _1iM=E(_1iK),_1iN=E(_1iL);if(!_1iN._){var _1iO=_1iN.b,_1iP=_1iN.c,_1iQ=_1iN.d;switch(B(A3(_13n,_1iJ,_1iM,_1iO))){case 0:return new F(function(){return _MQ(_1iO,B(_1iI(_1iJ,_1iM,_1iP)),_1iQ);});break;case 1:return E(_1iN);default:return new F(function(){return _Ns(_1iO,_1iP,B(_1iI(_1iJ,_1iM,_1iQ)));});}}else{return new T4(0,1,E(_1iM),E(_ML),E(_ML));}},_1iR=function(_1iS,_1iT,_1iU){return new F(function(){return _1iI(_1iS,_1iT,_1iU);});},_1iV=function(_1iW,_1iX,_1iY,_1iZ){var _1j0=E(_1iX);if(!_1j0._){var _1j1=E(_1iY);if(!_1j1._){return E(_1iZ);}else{var _1j2=function(_1j3,_1j4){while(1){var _1j5=E(_1j4);if(!_1j5._){if(!B(A3(_16p,_1iW,_1j5.b,_1j3))){return E(_1j5);}else{_1j4=_1j5.c;continue;}}else{return new T0(1);}}};return new F(function(){return _1j2(_1j1.a,_1iZ);});}}else{var _1j6=_1j0.a,_1j7=E(_1iY);if(!_1j7._){var _1j8=function(_1j9,_1ja){while(1){var _1jb=E(_1ja);if(!_1jb._){if(!B(A3(_178,_1iW,_1jb.b,_1j9))){return E(_1jb);}else{_1ja=_1jb.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1j8(_1j6,_1iZ);});}else{var _1jc=function(_1jd,_1je,_1jf){while(1){var _1jg=E(_1jf);if(!_1jg._){var _1jh=_1jg.b;if(!B(A3(_178,_1iW,_1jh,_1jd))){if(!B(A3(_16p,_1iW,_1jh,_1je))){return E(_1jg);}else{_1jf=_1jg.c;continue;}}else{_1jf=_1jg.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1jc(_1j6,_1j7.a,_1iZ);});}}},_1ji=function(_1jj,_1jk,_1jl,_1jm,_1jn){var _1jo=E(_1jn);if(!_1jo._){var _1jp=_1jo.b,_1jq=_1jo.c,_1jr=_1jo.d,_1js=E(_1jm);if(!_1js._){var _1jt=_1js.b,_1ju=function(_1jv){var _1jw=new T1(1,E(_1jt));return new F(function(){return _OM(_1jt,B(_1ji(_1jj,_1jk,_1jw,_1js.c,B(_1iV(_1jj,_1jk,_1jw,_1jo)))),B(_1ji(_1jj,_1jw,_1jl,_1js.d,B(_1iV(_1jj,_1jw,_1jl,_1jo)))));});};if(!E(_1jq)._){return new F(function(){return _1ju(_);});}else{if(!E(_1jr)._){return new F(function(){return _1ju(_);});}else{return new F(function(){return _1iR(_1jj,_1jp,_1js);});}}}else{return new F(function(){return _OM(_1jp,B(_1im(_1jj,_1jk,_1jq)),B(_1ix(_1jj,_1jl,_1jr)));});}}else{return E(_1jm);}},_1jx=function(_1jy,_1jz,_1jA,_1jB,_1jC,_1jD,_1jE,_1jF,_1jG,_1jH,_1jI){var _1jJ=function(_1jK){var _1jL=new T1(1,E(_1jC));return new F(function(){return _OM(_1jC,B(_1ji(_1jy,_1jz,_1jL,_1jD,B(_1iV(_1jy,_1jz,_1jL,new T4(0,_1jF,E(_1jG),E(_1jH),E(_1jI)))))),B(_1ji(_1jy,_1jL,_1jA,_1jE,B(_1iV(_1jy,_1jL,_1jA,new T4(0,_1jF,E(_1jG),E(_1jH),E(_1jI)))))));});};if(!E(_1jH)._){return new F(function(){return _1jJ(_);});}else{if(!E(_1jI)._){return new F(function(){return _1jJ(_);});}else{return new F(function(){return _1iR(_1jy,_1jG,new T4(0,_1jB,E(_1jC),E(_1jD),E(_1jE)));});}}},_1jM=function(_1jN,_1jO,_1jP){var _1jQ=E(_1jO);if(!_1jQ._){var _1jR=E(_1jP);if(!_1jR._){return new F(function(){return _1jx(_1ik,_1il,_1il,_1jQ.a,_1jQ.b,_1jQ.c,_1jQ.d,_1jR.a,_1jR.b,_1jR.c,_1jR.d);});}else{return E(_1jQ);}}else{return E(_1jP);}},_1jS=function(_1jT,_1jU,_1jV){var _1jW=function(_1jX,_1jY,_1jZ,_1k0){var _1k1=E(_1k0);switch(_1k1._){case 0:var _1k2=_1k1.a,_1k3=_1k1.b,_1k4=_1k1.c,_1k5=_1k1.d,_1k6=_1k3>>>0;if(((_1jZ>>>0&((_1k6-1>>>0^4294967295)>>>0^_1k6)>>>0)>>>0&4294967295)==_1k2){return ((_1jZ>>>0&_1k6)>>>0==0)?new T4(0,_1k2,_1k3,E(B(_1jW(_1jX,_1jY,_1jZ,_1k4))),E(_1k5)):new T4(0,_1k2,_1k3,E(_1k4),E(B(_1jW(_1jX,_1jY,_1jZ,_1k5))));}else{var _1k7=(_1jZ>>>0^_1k2>>>0)>>>0,_1k8=(_1k7|_1k7>>>1)>>>0,_1k9=(_1k8|_1k8>>>2)>>>0,_1ka=(_1k9|_1k9>>>4)>>>0,_1kb=(_1ka|_1ka>>>8)>>>0,_1kc=(_1kb|_1kb>>>16)>>>0,_1kd=(_1kc^_1kc>>>1)>>>0&4294967295,_1ke=_1kd>>>0;return ((_1jZ>>>0&_1ke)>>>0==0)?new T4(0,(_1jZ>>>0&((_1ke-1>>>0^4294967295)>>>0^_1ke)>>>0)>>>0&4294967295,_1kd,E(new T2(1,_1jX,_1jY)),E(_1k1)):new T4(0,(_1jZ>>>0&((_1ke-1>>>0^4294967295)>>>0^_1ke)>>>0)>>>0&4294967295,_1kd,E(_1k1),E(new T2(1,_1jX,_1jY)));}break;case 1:var _1kf=_1k1.a;if(_1jZ!=_1kf){var _1kg=(_1jZ>>>0^_1kf>>>0)>>>0,_1kh=(_1kg|_1kg>>>1)>>>0,_1ki=(_1kh|_1kh>>>2)>>>0,_1kj=(_1ki|_1ki>>>4)>>>0,_1kk=(_1kj|_1kj>>>8)>>>0,_1kl=(_1kk|_1kk>>>16)>>>0,_1km=(_1kl^_1kl>>>1)>>>0&4294967295,_1kn=_1km>>>0;return ((_1jZ>>>0&_1kn)>>>0==0)?new T4(0,(_1jZ>>>0&((_1kn-1>>>0^4294967295)>>>0^_1kn)>>>0)>>>0&4294967295,_1km,E(new T2(1,_1jX,_1jY)),E(_1k1)):new T4(0,(_1jZ>>>0&((_1kn-1>>>0^4294967295)>>>0^_1kn)>>>0)>>>0&4294967295,_1km,E(_1k1),E(new T2(1,_1jX,_1jY)));}else{return new T2(1,_1jX,new T(function(){return B(A3(_1jT,_1jX,_1jY,_1k1.b));}));}break;default:return new T2(1,_1jX,_1jY);}},_1ko=function(_1kp,_1kq,_1kr,_1ks){var _1kt=E(_1ks);switch(_1kt._){case 0:var _1ku=_1kt.a,_1kv=_1kt.b,_1kw=_1kt.c,_1kx=_1kt.d,_1ky=_1kv>>>0;if(((_1kr>>>0&((_1ky-1>>>0^4294967295)>>>0^_1ky)>>>0)>>>0&4294967295)==_1ku){return ((_1kr>>>0&_1ky)>>>0==0)?new T4(0,_1ku,_1kv,E(B(_1ko(_1kp,_1kq,_1kr,_1kw))),E(_1kx)):new T4(0,_1ku,_1kv,E(_1kw),E(B(_1ko(_1kp,_1kq,_1kr,_1kx))));}else{var _1kz=(_1ku>>>0^_1kr>>>0)>>>0,_1kA=(_1kz|_1kz>>>1)>>>0,_1kB=(_1kA|_1kA>>>2)>>>0,_1kC=(_1kB|_1kB>>>4)>>>0,_1kD=(_1kC|_1kC>>>8)>>>0,_1kE=(_1kD|_1kD>>>16)>>>0,_1kF=(_1kE^_1kE>>>1)>>>0&4294967295,_1kG=_1kF>>>0;return ((_1ku>>>0&_1kG)>>>0==0)?new T4(0,(_1ku>>>0&((_1kG-1>>>0^4294967295)>>>0^_1kG)>>>0)>>>0&4294967295,_1kF,E(_1kt),E(new T2(1,_1kp,_1kq))):new T4(0,(_1ku>>>0&((_1kG-1>>>0^4294967295)>>>0^_1kG)>>>0)>>>0&4294967295,_1kF,E(new T2(1,_1kp,_1kq)),E(_1kt));}break;case 1:var _1kH=_1kt.a;if(_1kH!=_1kr){var _1kI=(_1kH>>>0^_1kr>>>0)>>>0,_1kJ=(_1kI|_1kI>>>1)>>>0,_1kK=(_1kJ|_1kJ>>>2)>>>0,_1kL=(_1kK|_1kK>>>4)>>>0,_1kM=(_1kL|_1kL>>>8)>>>0,_1kN=(_1kM|_1kM>>>16)>>>0,_1kO=(_1kN^_1kN>>>1)>>>0&4294967295,_1kP=_1kO>>>0;return ((_1kH>>>0&_1kP)>>>0==0)?new T4(0,(_1kH>>>0&((_1kP-1>>>0^4294967295)>>>0^_1kP)>>>0)>>>0&4294967295,_1kO,E(_1kt),E(new T2(1,_1kp,_1kq))):new T4(0,(_1kH>>>0&((_1kP-1>>>0^4294967295)>>>0^_1kP)>>>0)>>>0&4294967295,_1kO,E(new T2(1,_1kp,_1kq)),E(_1kt));}else{return new T2(1,_1kH,new T(function(){return B(A3(_1jT,_1kH,_1kt.b,_1kq));}));}break;default:return new T2(1,_1kp,_1kq);}},_1kQ=function(_1kR,_1kS,_1kT,_1kU,_1kV,_1kW,_1kX){var _1kY=_1kV>>>0;if(((_1kT>>>0&((_1kY-1>>>0^4294967295)>>>0^_1kY)>>>0)>>>0&4294967295)==_1kU){return ((_1kT>>>0&_1kY)>>>0==0)?new T4(0,_1kU,_1kV,E(B(_1ko(_1kR,_1kS,_1kT,_1kW))),E(_1kX)):new T4(0,_1kU,_1kV,E(_1kW),E(B(_1ko(_1kR,_1kS,_1kT,_1kX))));}else{var _1kZ=(_1kU>>>0^_1kT>>>0)>>>0,_1l0=(_1kZ|_1kZ>>>1)>>>0,_1l1=(_1l0|_1l0>>>2)>>>0,_1l2=(_1l1|_1l1>>>4)>>>0,_1l3=(_1l2|_1l2>>>8)>>>0,_1l4=(_1l3|_1l3>>>16)>>>0,_1l5=(_1l4^_1l4>>>1)>>>0&4294967295,_1l6=_1l5>>>0;return ((_1kU>>>0&_1l6)>>>0==0)?new T4(0,(_1kU>>>0&((_1l6-1>>>0^4294967295)>>>0^_1l6)>>>0)>>>0&4294967295,_1l5,E(new T4(0,_1kU,_1kV,E(_1kW),E(_1kX))),E(new T2(1,_1kR,_1kS))):new T4(0,(_1kU>>>0&((_1l6-1>>>0^4294967295)>>>0^_1l6)>>>0)>>>0&4294967295,_1l5,E(new T2(1,_1kR,_1kS)),E(new T4(0,_1kU,_1kV,E(_1kW),E(_1kX))));}},_1l7=function(_1l8,_1l9){var _1la=E(_1l8);switch(_1la._){case 0:var _1lb=_1la.a,_1lc=_1la.b,_1ld=_1la.c,_1le=_1la.d,_1lf=E(_1l9);switch(_1lf._){case 0:var _1lg=_1lf.a,_1lh=_1lf.b,_1li=_1lf.c,_1lj=_1lf.d;if(_1lc>>>0<=_1lh>>>0){if(_1lh>>>0<=_1lc>>>0){if(_1lb!=_1lg){var _1lk=(_1lb>>>0^_1lg>>>0)>>>0,_1ll=(_1lk|_1lk>>>1)>>>0,_1lm=(_1ll|_1ll>>>2)>>>0,_1ln=(_1lm|_1lm>>>4)>>>0,_1lo=(_1ln|_1ln>>>8)>>>0,_1lp=(_1lo|_1lo>>>16)>>>0,_1lq=(_1lp^_1lp>>>1)>>>0&4294967295,_1lr=_1lq>>>0;return ((_1lb>>>0&_1lr)>>>0==0)?new T4(0,(_1lb>>>0&((_1lr-1>>>0^4294967295)>>>0^_1lr)>>>0)>>>0&4294967295,_1lq,E(_1la),E(_1lf)):new T4(0,(_1lb>>>0&((_1lr-1>>>0^4294967295)>>>0^_1lr)>>>0)>>>0&4294967295,_1lq,E(_1lf),E(_1la));}else{return new T4(0,_1lb,_1lc,E(B(_1l7(_1ld,_1li))),E(B(_1l7(_1le,_1lj))));}}else{var _1ls=_1lh>>>0;if(((_1lb>>>0&((_1ls-1>>>0^4294967295)>>>0^_1ls)>>>0)>>>0&4294967295)==_1lg){return ((_1lb>>>0&_1ls)>>>0==0)?new T4(0,_1lg,_1lh,E(B(_1lt(_1lb,_1lc,_1ld,_1le,_1li))),E(_1lj)):new T4(0,_1lg,_1lh,E(_1li),E(B(_1lt(_1lb,_1lc,_1ld,_1le,_1lj))));}else{var _1lu=(_1lb>>>0^_1lg>>>0)>>>0,_1lv=(_1lu|_1lu>>>1)>>>0,_1lw=(_1lv|_1lv>>>2)>>>0,_1lx=(_1lw|_1lw>>>4)>>>0,_1ly=(_1lx|_1lx>>>8)>>>0,_1lz=(_1ly|_1ly>>>16)>>>0,_1lA=(_1lz^_1lz>>>1)>>>0&4294967295,_1lB=_1lA>>>0;return ((_1lb>>>0&_1lB)>>>0==0)?new T4(0,(_1lb>>>0&((_1lB-1>>>0^4294967295)>>>0^_1lB)>>>0)>>>0&4294967295,_1lA,E(_1la),E(_1lf)):new T4(0,(_1lb>>>0&((_1lB-1>>>0^4294967295)>>>0^_1lB)>>>0)>>>0&4294967295,_1lA,E(_1lf),E(_1la));}}}else{var _1lC=_1lc>>>0;if(((_1lg>>>0&((_1lC-1>>>0^4294967295)>>>0^_1lC)>>>0)>>>0&4294967295)==_1lb){return ((_1lg>>>0&_1lC)>>>0==0)?new T4(0,_1lb,_1lc,E(B(_1lD(_1ld,_1lg,_1lh,_1li,_1lj))),E(_1le)):new T4(0,_1lb,_1lc,E(_1ld),E(B(_1lD(_1le,_1lg,_1lh,_1li,_1lj))));}else{var _1lE=(_1lb>>>0^_1lg>>>0)>>>0,_1lF=(_1lE|_1lE>>>1)>>>0,_1lG=(_1lF|_1lF>>>2)>>>0,_1lH=(_1lG|_1lG>>>4)>>>0,_1lI=(_1lH|_1lH>>>8)>>>0,_1lJ=(_1lI|_1lI>>>16)>>>0,_1lK=(_1lJ^_1lJ>>>1)>>>0&4294967295,_1lL=_1lK>>>0;return ((_1lb>>>0&_1lL)>>>0==0)?new T4(0,(_1lb>>>0&((_1lL-1>>>0^4294967295)>>>0^_1lL)>>>0)>>>0&4294967295,_1lK,E(_1la),E(_1lf)):new T4(0,(_1lb>>>0&((_1lL-1>>>0^4294967295)>>>0^_1lL)>>>0)>>>0&4294967295,_1lK,E(_1lf),E(_1la));}}break;case 1:var _1lM=_1lf.a;return new F(function(){return _1kQ(_1lM,_1lf.b,_1lM,_1lb,_1lc,_1ld,_1le);});break;default:return E(_1la);}break;case 1:var _1lN=_1la.a;return new F(function(){return _1jW(_1lN,_1la.b,_1lN,_1l9);});break;default:return E(_1l9);}},_1lt=function(_1lO,_1lP,_1lQ,_1lR,_1lS){var _1lT=E(_1lS);switch(_1lT._){case 0:var _1lU=_1lT.a,_1lV=_1lT.b,_1lW=_1lT.c,_1lX=_1lT.d;if(_1lP>>>0<=_1lV>>>0){if(_1lV>>>0<=_1lP>>>0){if(_1lO!=_1lU){var _1lY=(_1lO>>>0^_1lU>>>0)>>>0,_1lZ=(_1lY|_1lY>>>1)>>>0,_1m0=(_1lZ|_1lZ>>>2)>>>0,_1m1=(_1m0|_1m0>>>4)>>>0,_1m2=(_1m1|_1m1>>>8)>>>0,_1m3=(_1m2|_1m2>>>16)>>>0,_1m4=(_1m3^_1m3>>>1)>>>0&4294967295,_1m5=_1m4>>>0;return ((_1lO>>>0&_1m5)>>>0==0)?new T4(0,(_1lO>>>0&((_1m5-1>>>0^4294967295)>>>0^_1m5)>>>0)>>>0&4294967295,_1m4,E(new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR))),E(_1lT)):new T4(0,(_1lO>>>0&((_1m5-1>>>0^4294967295)>>>0^_1m5)>>>0)>>>0&4294967295,_1m4,E(_1lT),E(new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR))));}else{return new T4(0,_1lO,_1lP,E(B(_1l7(_1lQ,_1lW))),E(B(_1l7(_1lR,_1lX))));}}else{var _1m6=_1lV>>>0;if(((_1lO>>>0&((_1m6-1>>>0^4294967295)>>>0^_1m6)>>>0)>>>0&4294967295)==_1lU){return ((_1lO>>>0&_1m6)>>>0==0)?new T4(0,_1lU,_1lV,E(B(_1lt(_1lO,_1lP,_1lQ,_1lR,_1lW))),E(_1lX)):new T4(0,_1lU,_1lV,E(_1lW),E(B(_1lt(_1lO,_1lP,_1lQ,_1lR,_1lX))));}else{var _1m7=(_1lO>>>0^_1lU>>>0)>>>0,_1m8=(_1m7|_1m7>>>1)>>>0,_1m9=(_1m8|_1m8>>>2)>>>0,_1ma=(_1m9|_1m9>>>4)>>>0,_1mb=(_1ma|_1ma>>>8)>>>0,_1mc=(_1mb|_1mb>>>16)>>>0,_1md=(_1mc^_1mc>>>1)>>>0&4294967295,_1me=_1md>>>0;return ((_1lO>>>0&_1me)>>>0==0)?new T4(0,(_1lO>>>0&((_1me-1>>>0^4294967295)>>>0^_1me)>>>0)>>>0&4294967295,_1md,E(new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR))),E(_1lT)):new T4(0,(_1lO>>>0&((_1me-1>>>0^4294967295)>>>0^_1me)>>>0)>>>0&4294967295,_1md,E(_1lT),E(new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR))));}}}else{var _1mf=_1lP>>>0;if(((_1lU>>>0&((_1mf-1>>>0^4294967295)>>>0^_1mf)>>>0)>>>0&4294967295)==_1lO){return ((_1lU>>>0&_1mf)>>>0==0)?new T4(0,_1lO,_1lP,E(B(_1lD(_1lQ,_1lU,_1lV,_1lW,_1lX))),E(_1lR)):new T4(0,_1lO,_1lP,E(_1lQ),E(B(_1lD(_1lR,_1lU,_1lV,_1lW,_1lX))));}else{var _1mg=(_1lO>>>0^_1lU>>>0)>>>0,_1mh=(_1mg|_1mg>>>1)>>>0,_1mi=(_1mh|_1mh>>>2)>>>0,_1mj=(_1mi|_1mi>>>4)>>>0,_1mk=(_1mj|_1mj>>>8)>>>0,_1ml=(_1mk|_1mk>>>16)>>>0,_1mm=(_1ml^_1ml>>>1)>>>0&4294967295,_1mn=_1mm>>>0;return ((_1lO>>>0&_1mn)>>>0==0)?new T4(0,(_1lO>>>0&((_1mn-1>>>0^4294967295)>>>0^_1mn)>>>0)>>>0&4294967295,_1mm,E(new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR))),E(_1lT)):new T4(0,(_1lO>>>0&((_1mn-1>>>0^4294967295)>>>0^_1mn)>>>0)>>>0&4294967295,_1mm,E(_1lT),E(new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR))));}}break;case 1:var _1mo=_1lT.a;return new F(function(){return _1kQ(_1mo,_1lT.b,_1mo,_1lO,_1lP,_1lQ,_1lR);});break;default:return new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR));}},_1lD=function(_1mp,_1mq,_1mr,_1ms,_1mt){var _1mu=E(_1mp);switch(_1mu._){case 0:var _1mv=_1mu.a,_1mw=_1mu.b,_1mx=_1mu.c,_1my=_1mu.d;if(_1mw>>>0<=_1mr>>>0){if(_1mr>>>0<=_1mw>>>0){if(_1mv!=_1mq){var _1mz=(_1mv>>>0^_1mq>>>0)>>>0,_1mA=(_1mz|_1mz>>>1)>>>0,_1mB=(_1mA|_1mA>>>2)>>>0,_1mC=(_1mB|_1mB>>>4)>>>0,_1mD=(_1mC|_1mC>>>8)>>>0,_1mE=(_1mD|_1mD>>>16)>>>0,_1mF=(_1mE^_1mE>>>1)>>>0&4294967295,_1mG=_1mF>>>0;return ((_1mv>>>0&_1mG)>>>0==0)?new T4(0,(_1mv>>>0&((_1mG-1>>>0^4294967295)>>>0^_1mG)>>>0)>>>0&4294967295,_1mF,E(_1mu),E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt)))):new T4(0,(_1mv>>>0&((_1mG-1>>>0^4294967295)>>>0^_1mG)>>>0)>>>0&4294967295,_1mF,E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt))),E(_1mu));}else{return new T4(0,_1mv,_1mw,E(B(_1l7(_1mx,_1ms))),E(B(_1l7(_1my,_1mt))));}}else{var _1mH=_1mr>>>0;if(((_1mv>>>0&((_1mH-1>>>0^4294967295)>>>0^_1mH)>>>0)>>>0&4294967295)==_1mq){return ((_1mv>>>0&_1mH)>>>0==0)?new T4(0,_1mq,_1mr,E(B(_1lt(_1mv,_1mw,_1mx,_1my,_1ms))),E(_1mt)):new T4(0,_1mq,_1mr,E(_1ms),E(B(_1lt(_1mv,_1mw,_1mx,_1my,_1mt))));}else{var _1mI=(_1mv>>>0^_1mq>>>0)>>>0,_1mJ=(_1mI|_1mI>>>1)>>>0,_1mK=(_1mJ|_1mJ>>>2)>>>0,_1mL=(_1mK|_1mK>>>4)>>>0,_1mM=(_1mL|_1mL>>>8)>>>0,_1mN=(_1mM|_1mM>>>16)>>>0,_1mO=(_1mN^_1mN>>>1)>>>0&4294967295,_1mP=_1mO>>>0;return ((_1mv>>>0&_1mP)>>>0==0)?new T4(0,(_1mv>>>0&((_1mP-1>>>0^4294967295)>>>0^_1mP)>>>0)>>>0&4294967295,_1mO,E(_1mu),E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt)))):new T4(0,(_1mv>>>0&((_1mP-1>>>0^4294967295)>>>0^_1mP)>>>0)>>>0&4294967295,_1mO,E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt))),E(_1mu));}}}else{var _1mQ=_1mw>>>0;if(((_1mq>>>0&((_1mQ-1>>>0^4294967295)>>>0^_1mQ)>>>0)>>>0&4294967295)==_1mv){return ((_1mq>>>0&_1mQ)>>>0==0)?new T4(0,_1mv,_1mw,E(B(_1lD(_1mx,_1mq,_1mr,_1ms,_1mt))),E(_1my)):new T4(0,_1mv,_1mw,E(_1mx),E(B(_1lD(_1my,_1mq,_1mr,_1ms,_1mt))));}else{var _1mR=(_1mv>>>0^_1mq>>>0)>>>0,_1mS=(_1mR|_1mR>>>1)>>>0,_1mT=(_1mS|_1mS>>>2)>>>0,_1mU=(_1mT|_1mT>>>4)>>>0,_1mV=(_1mU|_1mU>>>8)>>>0,_1mW=(_1mV|_1mV>>>16)>>>0,_1mX=(_1mW^_1mW>>>1)>>>0&4294967295,_1mY=_1mX>>>0;return ((_1mv>>>0&_1mY)>>>0==0)?new T4(0,(_1mv>>>0&((_1mY-1>>>0^4294967295)>>>0^_1mY)>>>0)>>>0&4294967295,_1mX,E(_1mu),E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt)))):new T4(0,(_1mv>>>0&((_1mY-1>>>0^4294967295)>>>0^_1mY)>>>0)>>>0&4294967295,_1mX,E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt))),E(_1mu));}}break;case 1:var _1mZ=_1mu.a,_1n0=_1mu.b,_1n1=_1mr>>>0;if(((_1mZ>>>0&((_1n1-1>>>0^4294967295)>>>0^_1n1)>>>0)>>>0&4294967295)==_1mq){return ((_1mZ>>>0&_1n1)>>>0==0)?new T4(0,_1mq,_1mr,E(B(_1jW(_1mZ,_1n0,_1mZ,_1ms))),E(_1mt)):new T4(0,_1mq,_1mr,E(_1ms),E(B(_1jW(_1mZ,_1n0,_1mZ,_1mt))));}else{var _1n2=(_1mZ>>>0^_1mq>>>0)>>>0,_1n3=(_1n2|_1n2>>>1)>>>0,_1n4=(_1n3|_1n3>>>2)>>>0,_1n5=(_1n4|_1n4>>>4)>>>0,_1n6=(_1n5|_1n5>>>8)>>>0,_1n7=(_1n6|_1n6>>>16)>>>0,_1n8=(_1n7^_1n7>>>1)>>>0&4294967295,_1n9=_1n8>>>0;return ((_1mZ>>>0&_1n9)>>>0==0)?new T4(0,(_1mZ>>>0&((_1n9-1>>>0^4294967295)>>>0^_1n9)>>>0)>>>0&4294967295,_1n8,E(new T2(1,_1mZ,_1n0)),E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt)))):new T4(0,(_1mZ>>>0&((_1n9-1>>>0^4294967295)>>>0^_1n9)>>>0)>>>0&4294967295,_1n8,E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt))),E(new T2(1,_1mZ,_1n0)));}break;default:return new T4(0,_1mq,_1mr,E(_1ms),E(_1mt));}};return new F(function(){return _1l7(_1jU,_1jV);});},_1na=function(_1nb,_1nc,_1nd){return new F(function(){return _1jS(_1jM,_1nc,_1nd);});},_1ne=function(_1nf,_1ng){return E(_1nf);},_1nh=new T2(0,_4l,_Rg),_1ni=function(_1nj,_1nk){while(1){var _1nl=B((function(_1nm,_1nn){var _1no=E(_1nn);if(!_1no._){_1nj=new T2(1,_1no.b,new T(function(){return B(_1ni(_1nm,_1no.d));}));_1nk=_1no.c;return __continue;}else{return E(_1nm);}})(_1nj,_1nk));if(_1nl!=__continue){return _1nl;}}},_1np=function(_1nq,_1nr,_1ns){var _1nt=function(_1nu){var _1nv=function(_1nw){if(_1nu!=_1nw){return false;}else{return new F(function(){return _18O(_1nq,B(_1ni(_4,_1nr)),B(_1ni(_4,_1ns)));});}},_1nx=E(_1ns);if(!_1nx._){return new F(function(){return _1nv(_1nx.a);});}else{return new F(function(){return _1nv(0);});}},_1ny=E(_1nr);if(!_1ny._){return new F(function(){return _1nt(_1ny.a);});}else{return new F(function(){return _1nt(0);});}},_1nz=function(_1nA,_1nB){return (!B(_1np(_1b0,_1nA,_1nB)))?true:false;},_1nC=function(_1nD,_1nE){return new F(function(){return _1np(_1b0,_1nD,_1nE);});},_1nF=new T2(0,_1nC,_1nz),_1nG=function(_1nH,_1nI){var _1nJ=function(_1nK){while(1){var _1nL=E(_1nK);switch(_1nL._){case 0:var _1nM=_1nL.b>>>0;if(((_1nH>>>0&((_1nM-1>>>0^4294967295)>>>0^_1nM)>>>0)>>>0&4294967295)==_1nL.a){if(!((_1nH>>>0&_1nM)>>>0)){_1nK=_1nL.c;continue;}else{_1nK=_1nL.d;continue;}}else{return false;}break;case 1:return _1nH==_1nL.a;default:return false;}}};return new F(function(){return _1nJ(_1nI);});},_1nN=function(_1nO,_1nP){var _1nQ=function(_1nR){while(1){var _1nS=E(_1nR);switch(_1nS._){case 0:var _1nT=_1nS.b>>>0;if(((_1nO>>>0&((_1nT-1>>>0^4294967295)>>>0^_1nT)>>>0)>>>0&4294967295)==_1nS.a){if(!((_1nO>>>0&_1nT)>>>0)){_1nR=_1nS.c;continue;}else{_1nR=_1nS.d;continue;}}else{return false;}break;case 1:return ((_1nO&(-32))!=_1nS.a)?false:((1<<(_1nO&31)>>>0&_1nS.b)>>>0==0)?false:true;default:return false;}}};return new F(function(){return _1nQ(_1nP);});},_1nU=function(_1nV,_1nW,_1nX){while(1){var _1nY=E(_1nW);switch(_1nY._){case 0:var _1nZ=E(_1nX);if(!_1nZ._){if(_1nY.b!=_1nZ.b){return false;}else{if(_1nY.a!=_1nZ.a){return false;}else{if(!B(_1nU(_1nV,_1nY.c,_1nZ.c))){return false;}else{_1nW=_1nY.d;_1nX=_1nZ.d;continue;}}}}else{return false;}break;case 1:var _1o0=E(_1nX);if(_1o0._==1){if(_1nY.a!=_1o0.a){return false;}else{return new F(function(){return A3(_pM,_1nV,_1nY.b,_1o0.b);});}}else{return false;}break;default:return (E(_1nX)._==2)?true:false;}}},_1o1=function(_1o2,_1o3){var _1o4=E(_1o3);if(!_1o4._){var _1o5=_1o4.b,_1o6=_1o4.c,_1o7=_1o4.d;if(!B(A1(_1o2,_1o5))){return new F(function(){return _15N(B(_1o1(_1o2,_1o6)),B(_1o1(_1o2,_1o7)));});}else{return new F(function(){return _OM(_1o5,B(_1o1(_1o2,_1o6)),B(_1o1(_1o2,_1o7)));});}}else{return new T0(1);}},_1o8=function(_1o9,_1oa,_1ob){var _1oc=E(_1ob);switch(_1oc._){case 0:var _1od=_1oc.a,_1oe=_1oc.b,_1of=_1oc.c,_1og=_1oc.d,_1oh=_1oe>>>0;if(((_1o9>>>0&((_1oh-1>>>0^4294967295)>>>0^_1oh)>>>0)>>>0&4294967295)==_1od){return ((_1o9>>>0&_1oh)>>>0==0)?new T4(0,_1od,_1oe,E(B(_1o8(_1o9,_1oa,_1of))),E(_1og)):new T4(0,_1od,_1oe,E(_1of),E(B(_1o8(_1o9,_1oa,_1og))));}else{var _1oi=(_1o9>>>0^_1od>>>0)>>>0,_1oj=(_1oi|_1oi>>>1)>>>0,_1ok=(_1oj|_1oj>>>2)>>>0,_1ol=(_1ok|_1ok>>>4)>>>0,_1om=(_1ol|_1ol>>>8)>>>0,_1on=(_1om|_1om>>>16)>>>0,_1oo=(_1on^_1on>>>1)>>>0&4294967295,_1op=_1oo>>>0;return ((_1o9>>>0&_1op)>>>0==0)?new T4(0,(_1o9>>>0&((_1op-1>>>0^4294967295)>>>0^_1op)>>>0)>>>0&4294967295,_1oo,E(new T2(1,_1o9,_1oa)),E(_1oc)):new T4(0,(_1o9>>>0&((_1op-1>>>0^4294967295)>>>0^_1op)>>>0)>>>0&4294967295,_1oo,E(_1oc),E(new T2(1,_1o9,_1oa)));}break;case 1:var _1oq=_1oc.a;if(_1oq!=_1o9){var _1or=(_1o9>>>0^_1oq>>>0)>>>0,_1os=(_1or|_1or>>>1)>>>0,_1ot=(_1os|_1os>>>2)>>>0,_1ou=(_1ot|_1ot>>>4)>>>0,_1ov=(_1ou|_1ou>>>8)>>>0,_1ow=(_1ov|_1ov>>>16)>>>0,_1ox=(_1ow^_1ow>>>1)>>>0&4294967295,_1oy=_1ox>>>0;return ((_1o9>>>0&_1oy)>>>0==0)?new T4(0,(_1o9>>>0&((_1oy-1>>>0^4294967295)>>>0^_1oy)>>>0)>>>0&4294967295,_1ox,E(new T2(1,_1o9,_1oa)),E(_1oc)):new T4(0,(_1o9>>>0&((_1oy-1>>>0^4294967295)>>>0^_1oy)>>>0)>>>0&4294967295,_1ox,E(_1oc),E(new T2(1,_1o9,_1oa)));}else{return new T2(1,_1oq,(_1oa|_1oc.b)>>>0);}break;default:return new T2(1,_1o9,_1oa);}},_1oz=function(_1oA,_1oB){while(1){var _1oC=E(_1oA);if(!_1oC._){return E(_1oB);}else{var _1oD=E(E(_1oC.a).b),_1oE=B(_1o8(_1oD&(-32),1<<(_1oD&31)>>>0,_1oB));_1oA=_1oC.b;_1oB=_1oE;continue;}}},_1oF=function(_1oG,_1oH){while(1){var _1oI=E(_1oG);if(!_1oI._){return E(_1oH);}else{var _1oJ=B(_1oz(E(_1oI.a).a,_1oH));_1oG=_1oI.b;_1oH=_1oJ;continue;}}},_1oK=function(_1oL,_1oM){while(1){var _1oN=E(_1oM);if(!_1oN._){var _1oO=_1oN.c,_1oP=_1oN.d,_1oQ=E(_1oN.b);if(!_1oQ._){var _1oR=B(_1oF(_1oQ.b,B(_1oK(_1oL,_1oP))));_1oL=_1oR;_1oM=_1oO;continue;}else{var _1oR=B(_1oK(_1oL,_1oP));_1oL=_1oR;_1oM=_1oO;continue;}}else{return E(_1oL);}}},_1oS=-1,_1oT=-2,_1oU=-3,_1oV=new T2(1,_M9,_4),_1oW=new T2(1,_1oU,_1oV),_1oX=new T2(1,_1oT,_1oW),_1oY=new T2(1,_1oS,_1oX),_1oZ=function(_1p0,_1p1,_1p2){var _1p3=function(_1p4,_1p5){if(!B(_1nU(_1nF,_1p0,_1p4))){return new F(function(){return _1oZ(_1p4,_1p5,_1p2);});}else{return E(_1p0);}},_1p6=function(_1p7){if(!B(_vZ(_j1,_1p7,_1oY))){var _1p8=E(_1p7);if(!B(_1nG(_1p8,_1p0))){return new F(function(){return _1nN(_1p8,_1p1);});}else{return true;}}else{return true;}},_1p9=function(_1pa){while(1){var _1pb=E(_1pa);if(!_1pb._){return true;}else{if(!B(_1p6(E(_1pb.a).b))){return false;}else{_1pa=_1pb.b;continue;}}}},_1pc=function(_1pd){var _1pe=E(_1pd);switch(_1pe._){case 0:return new F(function(){return _1p9(_1pe.b);});break;case 1:return new F(function(){return _1p6(_1pe.a);});break;default:return true;}},_1pf=function(_1pg,_1ph,_1pi){while(1){var _1pj=B((function(_1pk,_1pl,_1pm){var _1pn=E(_1pm);switch(_1pn._){case 0:var _1po=B(_1pf(_1pk,_1pl,_1pn.d));_1pg=_1po.a;_1ph=_1po.b;_1pi=_1pn.c;return __continue;case 1:var _1pp=E(_1pk),_1pq=E(_1pl),_1pr=B(_1o1(_1pc,_1pn.b));return (_1pr._==0)?new T2(0,new T(function(){return B(_14u(_1pn.a,_1pr,_1pp));}),new T(function(){return B(_1oK(_1pq,_1pr));})):new T2(0,_1pp,_1pq);default:return new T2(0,_1pk,_1pl);}})(_1pg,_1ph,_1pi));if(_1pj!=__continue){return _1pj;}}},_1ps=E(_1p2);if(!_1ps._){var _1pt=_1ps.c,_1pu=_1ps.d;if(_1ps.b>=0){var _1pv=B(_1pf(_Ux,_18y,_1pu)),_1pw=B(_1pf(_1pv.a,_1pv.b,_1pt));return new F(function(){return _1p3(_1pw.a,_1pw.b);});}else{var _1px=B(_1pf(_Ux,_18y,_1pt)),_1py=B(_1pf(_1px.a,_1px.b,_1pu));return new F(function(){return _1p3(_1py.a,_1py.b);});}}else{var _1pz=B(_1pf(_Ux,_18y,_1ps));return new F(function(){return _1p3(_1pz.a,_1pz.b);});}},_1pA=function(_1pB,_1pC){while(1){var _1pD=E(_1pC);if(!_1pD._){return E(_1pB);}else{var _1pE=E(_1pD.a),_1pF=B(_14u(E(_1pE.a),_1pE.b,_1pB));_1pB=_1pF;_1pC=_1pD.b;continue;}}},_1pG=function(_1pH){var _1pI=E(_1pH);return (_1pI._==0)?(E(_1pI.b)._==0)?true:false:false;},_1pJ=new T(function(){return B(unCStr(")"));}),_1pK=function(_1pL,_1pM){var _1pN=new T(function(){var _1pO=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_1pM,_4)),_1pJ));})));},1);return B(_0(B(_bZ(0,_1pL,_4)),_1pO));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1pN)));});},_1pP=new T(function(){return B(_7f("pgf/PGF/Optimize.hs:(259,9)-(262,117)|function getFunctions"));}),_1pQ=new T(function(){return B(unCStr("&|"));}),_1pR=new T2(1,_1pQ,_4),_1pS=new T(function(){return B(unCStr("&+"));}),_1pT=new T2(1,_1pS,_4),_1pU=new T(function(){return B(_7f("pgf/PGF/Optimize.hs:(235,9)-(245,73)|function seq2prefix"));}),_1pV=function(_1pW,_1pX,_1pY,_1pZ,_1q0,_1q1){var _1q2=_1pZ>>>0;if(((_1pW>>>0&((_1q2-1>>>0^4294967295)>>>0^_1q2)>>>0)>>>0&4294967295)==_1pY){return ((_1pW>>>0&_1q2)>>>0==0)?new T4(0,_1pY,_1pZ,E(B(_1o8(_1pW,_1pX,_1q0))),E(_1q1)):new T4(0,_1pY,_1pZ,E(_1q0),E(B(_1o8(_1pW,_1pX,_1q1))));}else{var _1q3=(_1pW>>>0^_1pY>>>0)>>>0,_1q4=(_1q3|_1q3>>>1)>>>0,_1q5=(_1q4|_1q4>>>2)>>>0,_1q6=(_1q5|_1q5>>>4)>>>0,_1q7=(_1q6|_1q6>>>8)>>>0,_1q8=(_1q7|_1q7>>>16)>>>0,_1q9=(_1q8^_1q8>>>1)>>>0&4294967295,_1qa=_1q9>>>0;return ((_1pW>>>0&_1qa)>>>0==0)?new T4(0,(_1pW>>>0&((_1qa-1>>>0^4294967295)>>>0^_1qa)>>>0)>>>0&4294967295,_1q9,E(new T2(1,_1pW,_1pX)),E(new T4(0,_1pY,_1pZ,E(_1q0),E(_1q1)))):new T4(0,(_1pW>>>0&((_1qa-1>>>0^4294967295)>>>0^_1qa)>>>0)>>>0&4294967295,_1q9,E(new T4(0,_1pY,_1pZ,E(_1q0),E(_1q1))),E(new T2(1,_1pW,_1pX)));}},_1qb=function(_1qc,_1qd,_1qe,_1qf,_1qg){var _1qh=E(_1qg);switch(_1qh._){case 0:var _1qi=_1qh.a,_1qj=_1qh.b,_1qk=_1qh.c,_1ql=_1qh.d;if(_1qd>>>0<=_1qj>>>0){if(_1qj>>>0<=_1qd>>>0){if(_1qc!=_1qi){var _1qm=(_1qc>>>0^_1qi>>>0)>>>0,_1qn=(_1qm|_1qm>>>1)>>>0,_1qo=(_1qn|_1qn>>>2)>>>0,_1qp=(_1qo|_1qo>>>4)>>>0,_1qq=(_1qp|_1qp>>>8)>>>0,_1qr=(_1qq|_1qq>>>16)>>>0,_1qs=(_1qr^_1qr>>>1)>>>0&4294967295,_1qt=_1qs>>>0;return ((_1qc>>>0&_1qt)>>>0==0)?new T4(0,(_1qc>>>0&((_1qt-1>>>0^4294967295)>>>0^_1qt)>>>0)>>>0&4294967295,_1qs,E(new T4(0,_1qc,_1qd,E(_1qe),E(_1qf))),E(_1qh)):new T4(0,(_1qc>>>0&((_1qt-1>>>0^4294967295)>>>0^_1qt)>>>0)>>>0&4294967295,_1qs,E(_1qh),E(new T4(0,_1qc,_1qd,E(_1qe),E(_1qf))));}else{return new T4(0,_1qc,_1qd,E(B(_1qu(_1qe,_1qk))),E(B(_1qu(_1qf,_1ql))));}}else{var _1qv=_1qj>>>0;if(((_1qc>>>0&((_1qv-1>>>0^4294967295)>>>0^_1qv)>>>0)>>>0&4294967295)==_1qi){return ((_1qc>>>0&_1qv)>>>0==0)?new T4(0,_1qi,_1qj,E(B(_1qb(_1qc,_1qd,_1qe,_1qf,_1qk))),E(_1ql)):new T4(0,_1qi,_1qj,E(_1qk),E(B(_1qb(_1qc,_1qd,_1qe,_1qf,_1ql))));}else{var _1qw=(_1qc>>>0^_1qi>>>0)>>>0,_1qx=(_1qw|_1qw>>>1)>>>0,_1qy=(_1qx|_1qx>>>2)>>>0,_1qz=(_1qy|_1qy>>>4)>>>0,_1qA=(_1qz|_1qz>>>8)>>>0,_1qB=(_1qA|_1qA>>>16)>>>0,_1qC=(_1qB^_1qB>>>1)>>>0&4294967295,_1qD=_1qC>>>0;return ((_1qc>>>0&_1qD)>>>0==0)?new T4(0,(_1qc>>>0&((_1qD-1>>>0^4294967295)>>>0^_1qD)>>>0)>>>0&4294967295,_1qC,E(new T4(0,_1qc,_1qd,E(_1qe),E(_1qf))),E(_1qh)):new T4(0,(_1qc>>>0&((_1qD-1>>>0^4294967295)>>>0^_1qD)>>>0)>>>0&4294967295,_1qC,E(_1qh),E(new T4(0,_1qc,_1qd,E(_1qe),E(_1qf))));}}}else{var _1qE=_1qd>>>0;if(((_1qi>>>0&((_1qE-1>>>0^4294967295)>>>0^_1qE)>>>0)>>>0&4294967295)==_1qc){return ((_1qi>>>0&_1qE)>>>0==0)?new T4(0,_1qc,_1qd,E(B(_1qF(_1qe,_1qi,_1qj,_1qk,_1ql))),E(_1qf)):new T4(0,_1qc,_1qd,E(_1qe),E(B(_1qF(_1qf,_1qi,_1qj,_1qk,_1ql))));}else{var _1qG=(_1qc>>>0^_1qi>>>0)>>>0,_1qH=(_1qG|_1qG>>>1)>>>0,_1qI=(_1qH|_1qH>>>2)>>>0,_1qJ=(_1qI|_1qI>>>4)>>>0,_1qK=(_1qJ|_1qJ>>>8)>>>0,_1qL=(_1qK|_1qK>>>16)>>>0,_1qM=(_1qL^_1qL>>>1)>>>0&4294967295,_1qN=_1qM>>>0;return ((_1qc>>>0&_1qN)>>>0==0)?new T4(0,(_1qc>>>0&((_1qN-1>>>0^4294967295)>>>0^_1qN)>>>0)>>>0&4294967295,_1qM,E(new T4(0,_1qc,_1qd,E(_1qe),E(_1qf))),E(_1qh)):new T4(0,(_1qc>>>0&((_1qN-1>>>0^4294967295)>>>0^_1qN)>>>0)>>>0&4294967295,_1qM,E(_1qh),E(new T4(0,_1qc,_1qd,E(_1qe),E(_1qf))));}}break;case 1:return new F(function(){return _1pV(_1qh.a,_1qh.b,_1qc,_1qd,_1qe,_1qf);});break;default:return new T4(0,_1qc,_1qd,E(_1qe),E(_1qf));}},_1qF=function(_1qO,_1qP,_1qQ,_1qR,_1qS){var _1qT=E(_1qO);switch(_1qT._){case 0:var _1qU=_1qT.a,_1qV=_1qT.b,_1qW=_1qT.c,_1qX=_1qT.d;if(_1qV>>>0<=_1qQ>>>0){if(_1qQ>>>0<=_1qV>>>0){if(_1qU!=_1qP){var _1qY=(_1qU>>>0^_1qP>>>0)>>>0,_1qZ=(_1qY|_1qY>>>1)>>>0,_1r0=(_1qZ|_1qZ>>>2)>>>0,_1r1=(_1r0|_1r0>>>4)>>>0,_1r2=(_1r1|_1r1>>>8)>>>0,_1r3=(_1r2|_1r2>>>16)>>>0,_1r4=(_1r3^_1r3>>>1)>>>0&4294967295,_1r5=_1r4>>>0;return ((_1qU>>>0&_1r5)>>>0==0)?new T4(0,(_1qU>>>0&((_1r5-1>>>0^4294967295)>>>0^_1r5)>>>0)>>>0&4294967295,_1r4,E(_1qT),E(new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS)))):new T4(0,(_1qU>>>0&((_1r5-1>>>0^4294967295)>>>0^_1r5)>>>0)>>>0&4294967295,_1r4,E(new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS))),E(_1qT));}else{return new T4(0,_1qU,_1qV,E(B(_1qu(_1qW,_1qR))),E(B(_1qu(_1qX,_1qS))));}}else{var _1r6=_1qQ>>>0;if(((_1qU>>>0&((_1r6-1>>>0^4294967295)>>>0^_1r6)>>>0)>>>0&4294967295)==_1qP){return ((_1qU>>>0&_1r6)>>>0==0)?new T4(0,_1qP,_1qQ,E(B(_1qb(_1qU,_1qV,_1qW,_1qX,_1qR))),E(_1qS)):new T4(0,_1qP,_1qQ,E(_1qR),E(B(_1qb(_1qU,_1qV,_1qW,_1qX,_1qS))));}else{var _1r7=(_1qU>>>0^_1qP>>>0)>>>0,_1r8=(_1r7|_1r7>>>1)>>>0,_1r9=(_1r8|_1r8>>>2)>>>0,_1ra=(_1r9|_1r9>>>4)>>>0,_1rb=(_1ra|_1ra>>>8)>>>0,_1rc=(_1rb|_1rb>>>16)>>>0,_1rd=(_1rc^_1rc>>>1)>>>0&4294967295,_1re=_1rd>>>0;return ((_1qU>>>0&_1re)>>>0==0)?new T4(0,(_1qU>>>0&((_1re-1>>>0^4294967295)>>>0^_1re)>>>0)>>>0&4294967295,_1rd,E(_1qT),E(new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS)))):new T4(0,(_1qU>>>0&((_1re-1>>>0^4294967295)>>>0^_1re)>>>0)>>>0&4294967295,_1rd,E(new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS))),E(_1qT));}}}else{var _1rf=_1qV>>>0;if(((_1qP>>>0&((_1rf-1>>>0^4294967295)>>>0^_1rf)>>>0)>>>0&4294967295)==_1qU){return ((_1qP>>>0&_1rf)>>>0==0)?new T4(0,_1qU,_1qV,E(B(_1qF(_1qW,_1qP,_1qQ,_1qR,_1qS))),E(_1qX)):new T4(0,_1qU,_1qV,E(_1qW),E(B(_1qF(_1qX,_1qP,_1qQ,_1qR,_1qS))));}else{var _1rg=(_1qU>>>0^_1qP>>>0)>>>0,_1rh=(_1rg|_1rg>>>1)>>>0,_1ri=(_1rh|_1rh>>>2)>>>0,_1rj=(_1ri|_1ri>>>4)>>>0,_1rk=(_1rj|_1rj>>>8)>>>0,_1rl=(_1rk|_1rk>>>16)>>>0,_1rm=(_1rl^_1rl>>>1)>>>0&4294967295,_1rn=_1rm>>>0;return ((_1qU>>>0&_1rn)>>>0==0)?new T4(0,(_1qU>>>0&((_1rn-1>>>0^4294967295)>>>0^_1rn)>>>0)>>>0&4294967295,_1rm,E(_1qT),E(new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS)))):new T4(0,(_1qU>>>0&((_1rn-1>>>0^4294967295)>>>0^_1rn)>>>0)>>>0&4294967295,_1rm,E(new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS))),E(_1qT));}}break;case 1:return new F(function(){return _1pV(_1qT.a,_1qT.b,_1qP,_1qQ,_1qR,_1qS);});break;default:return new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS));}},_1qu=function(_1ro,_1rp){var _1rq=E(_1ro);switch(_1rq._){case 0:var _1rr=_1rq.a,_1rs=_1rq.b,_1rt=_1rq.c,_1ru=_1rq.d,_1rv=E(_1rp);switch(_1rv._){case 0:var _1rw=_1rv.a,_1rx=_1rv.b,_1ry=_1rv.c,_1rz=_1rv.d;if(_1rs>>>0<=_1rx>>>0){if(_1rx>>>0<=_1rs>>>0){if(_1rr!=_1rw){var _1rA=(_1rr>>>0^_1rw>>>0)>>>0,_1rB=(_1rA|_1rA>>>1)>>>0,_1rC=(_1rB|_1rB>>>2)>>>0,_1rD=(_1rC|_1rC>>>4)>>>0,_1rE=(_1rD|_1rD>>>8)>>>0,_1rF=(_1rE|_1rE>>>16)>>>0,_1rG=(_1rF^_1rF>>>1)>>>0&4294967295,_1rH=_1rG>>>0;return ((_1rr>>>0&_1rH)>>>0==0)?new T4(0,(_1rr>>>0&((_1rH-1>>>0^4294967295)>>>0^_1rH)>>>0)>>>0&4294967295,_1rG,E(_1rq),E(_1rv)):new T4(0,(_1rr>>>0&((_1rH-1>>>0^4294967295)>>>0^_1rH)>>>0)>>>0&4294967295,_1rG,E(_1rv),E(_1rq));}else{return new T4(0,_1rr,_1rs,E(B(_1qu(_1rt,_1ry))),E(B(_1qu(_1ru,_1rz))));}}else{var _1rI=_1rx>>>0;if(((_1rr>>>0&((_1rI-1>>>0^4294967295)>>>0^_1rI)>>>0)>>>0&4294967295)==_1rw){return ((_1rr>>>0&_1rI)>>>0==0)?new T4(0,_1rw,_1rx,E(B(_1qb(_1rr,_1rs,_1rt,_1ru,_1ry))),E(_1rz)):new T4(0,_1rw,_1rx,E(_1ry),E(B(_1qb(_1rr,_1rs,_1rt,_1ru,_1rz))));}else{var _1rJ=(_1rr>>>0^_1rw>>>0)>>>0,_1rK=(_1rJ|_1rJ>>>1)>>>0,_1rL=(_1rK|_1rK>>>2)>>>0,_1rM=(_1rL|_1rL>>>4)>>>0,_1rN=(_1rM|_1rM>>>8)>>>0,_1rO=(_1rN|_1rN>>>16)>>>0,_1rP=(_1rO^_1rO>>>1)>>>0&4294967295,_1rQ=_1rP>>>0;return ((_1rr>>>0&_1rQ)>>>0==0)?new T4(0,(_1rr>>>0&((_1rQ-1>>>0^4294967295)>>>0^_1rQ)>>>0)>>>0&4294967295,_1rP,E(_1rq),E(_1rv)):new T4(0,(_1rr>>>0&((_1rQ-1>>>0^4294967295)>>>0^_1rQ)>>>0)>>>0&4294967295,_1rP,E(_1rv),E(_1rq));}}}else{var _1rR=_1rs>>>0;if(((_1rw>>>0&((_1rR-1>>>0^4294967295)>>>0^_1rR)>>>0)>>>0&4294967295)==_1rr){return ((_1rw>>>0&_1rR)>>>0==0)?new T4(0,_1rr,_1rs,E(B(_1qF(_1rt,_1rw,_1rx,_1ry,_1rz))),E(_1ru)):new T4(0,_1rr,_1rs,E(_1rt),E(B(_1qF(_1ru,_1rw,_1rx,_1ry,_1rz))));}else{var _1rS=(_1rr>>>0^_1rw>>>0)>>>0,_1rT=(_1rS|_1rS>>>1)>>>0,_1rU=(_1rT|_1rT>>>2)>>>0,_1rV=(_1rU|_1rU>>>4)>>>0,_1rW=(_1rV|_1rV>>>8)>>>0,_1rX=(_1rW|_1rW>>>16)>>>0,_1rY=(_1rX^_1rX>>>1)>>>0&4294967295,_1rZ=_1rY>>>0;return ((_1rr>>>0&_1rZ)>>>0==0)?new T4(0,(_1rr>>>0&((_1rZ-1>>>0^4294967295)>>>0^_1rZ)>>>0)>>>0&4294967295,_1rY,E(_1rq),E(_1rv)):new T4(0,(_1rr>>>0&((_1rZ-1>>>0^4294967295)>>>0^_1rZ)>>>0)>>>0&4294967295,_1rY,E(_1rv),E(_1rq));}}break;case 1:return new F(function(){return _1pV(_1rv.a,_1rv.b,_1rr,_1rs,_1rt,_1ru);});break;default:return E(_1rq);}break;case 1:return new F(function(){return _1o8(_1rq.a,_1rq.b,_1rp);});break;default:return E(_1rp);}},_1s0=function(_1s1,_1s2){var _1s3=E(_1s1),_1s4=B(_16i(_12C,_1qu,_1s3.a,_1s3.b,_1s2));return new T2(0,_1s4.a,_1s4.b);},_1s5=new T(function(){return B(unCStr("Int"));}),_1s6=function(_1s7,_1s8,_1s9){return new F(function(){return _eR(_e4,new T2(0,_1s8,_1s9),_1s7,_1s5);});},_1sa=function(_1sb,_1sc,_1sd){return new F(function(){return _eR(_e4,new T2(0,_1sb,_1sc),_1sd,_1s5);});},_1se=new T(function(){return B(_1pA(_Ux,_4));}),_1sf=function(_1sg,_1sh){var _1si=function(_1sj,_1sk,_1sl){return new F(function(){return A2(_1sg,_1sk,_1sl);});},_1sm=function(_1sn,_1so){while(1){var _1sp=E(_1so);if(!_1sp._){return E(_1sn);}else{var _1sq=B(_1jS(_1si,_1sn,_1sp.a));_1sn=_1sq;_1so=_1sp.b;continue;}}};return new F(function(){return _1sm(_Ux,_1sh);});},_1sr=function(_1ss,_1st,_1su,_1sv,_1sw,_1sx,_1sy,_1sz,_1sA){var _1sB=new T(function(){return B(_1oZ(_Ux,_18y,_1sy));}),_1sC=new T(function(){var _1sD=function(_1sE,_1sF){while(1){var _1sG=B((function(_1sH,_1sI){var _1sJ=E(_1sI);if(!_1sJ._){var _1sK=_1sJ.d,_1sL=new T(function(){var _1sM=E(_1sJ.b);if(!_1sM._){var _1sN=_1sM.a;if(!E(_1sM.b)._){var _1sO=new T(function(){var _1sP=E(_1su),_1sQ=_1sP.c,_1sR=E(_1sP.a),_1sS=E(_1sP.b);if(_1sR>_1sN){return B(_1s6(_1sN,_1sR,_1sS));}else{if(_1sN>_1sS){return B(_1s6(_1sN,_1sR,_1sS));}else{var _1sT=_1sN-_1sR|0;if(0>_1sT){return B(_1pK(_1sT,_1sQ));}else{if(_1sT>=_1sQ){return B(_1pK(_1sT,_1sQ));}else{var _1sU=E(_1sP.d[_1sT]),_1sV=_1sU.d,_1sW=E(_1sU.b),_1sX=E(_1sU.c);if(_1sW<=_1sX){var _1sY=new T(function(){var _1sZ=B(_14j(_12C,_1ne,new T2(1,new T2(0,_1pR,new T2(1,_1sN&(-32),1<<(_1sN&31)>>>0)),_4)));return new T2(0,_1sZ.a,_1sZ.b);}),_1t0=new T(function(){var _1t1=B(_14j(_12C,_1ne,new T2(1,new T2(0,_4,new T2(1,_1sN&(-32),1<<(_1sN&31)>>>0)),_4)));return new T2(0,_1t1.a,_1t1.b);}),_1t2=new T2(1,_1sN&(-32),1<<(_1sN&31)>>>0),_1t3=new T(function(){var _1t4=B(_14j(_12C,_1ne,new T2(1,new T2(0,_4,_1t2),_4)));return new T2(0,_1t4.a,_1t4.b);}),_1t5=new T(function(){var _1t6=B(_14j(_12C,_1ne,new T2(1,new T2(0,_1pT,new T2(1,_1sN&(-32),1<<(_1sN&31)>>>0)),_4)));return new T2(0,_1t6.a,_1t6.b);}),_1t7=function(_1t8){var _1t9=E(_1t8);if(!_1t9._){return E(_1t3);}else{var _1ta=_1t9.b,_1tb=E(_1t9.a);switch(_1tb._){case 3:var _1tc=B(_14j(_12C,_1ne,new T2(1,new T2(0,new T2(1,_1tb.a,_4),_1t2),_4)));return new T2(0,_1tc.a,_1tc.b);case 4:var _1td=new T(function(){var _1te=function(_1tf){var _1tg=E(_1tf);return (_1tg._==0)?__Z:new T2(1,new T(function(){return B(_1t7(B(_0(E(_1tg.a).a,_1ta))));}),new T(function(){return B(_1te(_1tg.b));}));};return B(_1te(_1tb.b));}),_1th=B(_18o(_12C,_1qu,new T2(1,new T(function(){return B(_1t7(B(_0(_1tb.a,_1ta))));}),_1td)));return new T2(0,_1th.a,_1th.b);case 5:return E(_1t5);case 6:return E(_1nh);case 7:return E(_1t0);case 8:return E(_1t0);case 9:return E(_1sY);case 10:return E(_1sY);default:return E(_1pU);}}},_1ti=new T(function(){return B(_1t7(_4));}),_1tj=function(_1tk){var _1tl=new T(function(){var _1tm=E(_1sx),_1tn=_1tm.c,_1to=E(_1tm.a),_1tp=E(_1tm.b);if(_1sW>_1tk){return B(_1sa(_1sW,_1sX,_1tk));}else{if(_1tk>_1sX){return B(_1sa(_1sW,_1sX,_1tk));}else{var _1tq=_1tk-_1sW|0;if(0>_1tq){return B(_1pK(_1tq,_1sV));}else{if(_1tq>=_1sV){return B(_1pK(_1tq,_1sV));}else{var _1tr=_1sU.e["v"]["i32"][_1tq];if(_1to>_1tr){return B(_1s6(_1tr,_1to,_1tp));}else{if(_1tr>_1tp){return B(_1s6(_1tr,_1to,_1tp));}else{var _1ts=_1tr-_1to|0;if(0>_1ts){return B(_1pK(_1ts,_1tn));}else{if(_1ts>=_1tn){return B(_1pK(_1ts,_1tn));}else{var _1tt=E(_1tm.d[_1ts]),_1tu=_1tt.c-1|0;if(0<=_1tu){var _1tv=function(_1tw){return new T2(1,new T(function(){return E(_1tt.d[_1tw]);}),new T(function(){if(_1tw!=_1tu){return B(_1tv(_1tw+1|0));}else{return __Z;}}));};return B(_1t7(B(_1tv(0))));}else{return E(_1ti);}}}}}}}}}});return new T2(1,new T2(0,_1tk,_1tl),new T(function(){if(_1tk!=_1sX){return B(_1tj(_1tk+1|0));}else{return __Z;}}));};return B(_1pA(_Ux,B(_1tj(_1sW))));}else{return E(_1se);}}}}}});return new T2(1,_1sO,new T(function(){return B(_1sD(_1sH,_1sK));}));}else{return B(_1sD(_1sH,_1sK));}}else{return B(_1sD(_1sH,_1sK));}},1);_1sE=_1sL;_1sF=_1sJ.c;return __continue;}else{return E(_1sH);}})(_1sE,_1sF));if(_1sG!=__continue){return _1sG;}}},_1tx=function(_1ty,_1tz,_1tA){while(1){var _1tB=E(_1tA);switch(_1tB._){case 0:var _1tC=B(_1tx(_1ty,_1tz,_1tB.d));_1ty=_1tC.a;_1tz=_1tC.b;_1tA=_1tB.c;continue;case 1:var _1tD=_1tB.a,_1tE=B(_160(_1pG,_1tB.b)),_1tF=E(_1tE.a);if(!_1tF._){var _1tG=B(_14u(_1tD,B(_1sf(_1s0,B(_1sD(_4,_1tF)))),_1ty));}else{var _1tG=E(_1ty);}var _1tH=E(_1tE.b);if(!_1tH._){var _1tI=B(_14u(_1tD,_1tH,_1tz));}else{var _1tI=E(_1tz);}return new T2(0,_1tG,_1tI);default:return new T2(0,_1ty,_1tz);}}},_1tJ=E(_1sB);if(!_1tJ._){var _1tK=_1tJ.c,_1tL=_1tJ.d;if(_1tJ.b>=0){var _1tM=B(_1tx(_Ux,_Ux,_1tL)),_1tN=B(_1tx(_1tM.a,_1tM.b,_1tK));return new T2(0,_1tN.a,_1tN.b);}else{var _1tO=B(_1tx(_Ux,_Ux,_1tK)),_1tP=B(_1tx(_1tO.a,_1tO.b,_1tL));return new T2(0,_1tP.a,_1tP.b);}}else{var _1tQ=B(_1tx(_Ux,_Ux,_1tJ));return new T2(0,_1tQ.a,_1tQ.b);}}),_1tR=new T(function(){var _1tS=function(_1tT){var _1tU=E(_1tT);switch(_1tU._){case 0:var _1tV=_1tU.a;return new T2(1,new T(function(){var _1tW=E(_1su),_1tX=_1tW.c,_1tY=E(_1tW.a),_1tZ=E(_1tW.b);if(_1tY>_1tV){return B(_1s6(_1tV,_1tY,_1tZ));}else{if(_1tV>_1tZ){return B(_1s6(_1tV,_1tY,_1tZ));}else{var _1u0=_1tV-_1tY|0;if(0>_1u0){return B(_1pK(_1u0,_1tX));}else{if(_1u0>=_1tX){return B(_1pK(_1u0,_1tX));}else{return E(E(_1tW.d[_1u0]).a);}}}}}),_4);case 1:var _1u1=B(_14V(_1tU.a,_1sB));if(!_1u1._){return __Z;}else{return new F(function(){return _1u2(_4,_1u1.a);});}break;default:return E(_1pP);}},_1u2=function(_1u3,_1u4){while(1){var _1u5=B((function(_1u6,_1u7){var _1u8=E(_1u7);if(!_1u8._){var _1u9=new T(function(){return B(_0(B(_1tS(_1u8.b)),new T(function(){return B(_1u2(_1u6,_1u8.d));},1)));},1);_1u3=_1u9;_1u4=_1u8.c;return __continue;}else{return E(_1u6);}})(_1u3,_1u4));if(_1u5!=__continue){return _1u5;}}},_1ua=function(_1ub,_1uc){while(1){var _1ud=B((function(_1ue,_1uf){var _1ug=E(_1uf);switch(_1ug._){case 0:_1ub=new T(function(){return B(_1ua(_1ue,_1ug.d));},1);_1uc=_1ug.c;return __continue;case 1:var _1uh=function(_1ui,_1uj){while(1){var _1uk=B((function(_1ul,_1um){var _1un=E(_1um);if(!_1un._){var _1uo=_1un.b,_1up=new T(function(){var _1uq=new T(function(){return B(_1uh(_1ul,_1un.d));}),_1ur=function(_1us){var _1ut=E(_1us);return (_1ut._==0)?E(_1uq):new T2(1,new T2(0,_1ut.a,new T2(1,_1ug.a,new T4(0,1,E(_1uo),E(_ML),E(_ML)))),new T(function(){return B(_1ur(_1ut.b));}));};return B(_1ur(B(_1tS(_1uo))));},1);_1ui=_1up;_1uj=_1un.c;return __continue;}else{return E(_1ul);}})(_1ui,_1uj));if(_1uk!=__continue){return _1uk;}}};return new F(function(){return _1uh(_1ue,_1ug.b);});break;default:return E(_1ue);}})(_1ub,_1uc));if(_1ud!=__continue){return _1ud;}}},_1uu=E(_1sB);if(!_1uu._){var _1uv=_1uu.c,_1uw=_1uu.d;if(_1uu.b>=0){return B(_13d(_1na,B(_1ua(new T(function(){return B(_1ua(_4,_1uw));},1),_1uv))));}else{return B(_13d(_1na,B(_1ua(new T(function(){return B(_1ua(_4,_1uv));},1),_1uw))));}}else{return B(_13d(_1na,B(_1ua(_4,_1uu))));}});return {_:0,a:_1ss,b:_1st,c:_1su,d:_1sv,e:_1sw,f:_1sx,g:_1sy,h:new T(function(){return E(E(_1sC).b);}),i:_1tR,j:_1sz,k:new T(function(){return E(E(_1sC).a);}),l:_1sA};},_1ux=function(_1uy){var _1uz=E(_1uy);return new F(function(){return _1sr(_1uz.a,_1uz.b,_1uz.c,_1uz.d,_1uz.e,_1uz.f,_1uz.g,_1uz.j,_1uz.l);});},_1uA=0,_1uB=function(_1uC){var _1uD=E(_1uC);return new T3(0,_1uD.a,_1uD.b,_1uA);},_1uE=function(_1uF){var _1uG=E(_1uF);return new T4(0,_1uG.a,_1uG.b,new T(function(){var _1uH=E(_1uG.c);if(!_1uH._){return __Z;}else{return new T1(1,new T2(0,_1uH.a,_4));}}),_1uG.d);},_1uI=0,_1uJ=new T(function(){return B(unCStr("Negative range size"));}),_1uK=function(_1uL){var _1uM=function(_){var _1uN=B(_uU(_1uL,0))-1|0,_1uO=function(_1uP){if(_1uP>=0){var _1uQ=newArr(_1uP,_Vu),_1uR=_1uQ,_1uS=function(_1uT){var _1uU=function(_1uV,_1uW,_){while(1){if(_1uV!=_1uT){var _1uX=E(_1uW);if(!_1uX._){return _5;}else{var _=_1uR[_1uV]=_1uX.a,_1uY=_1uV+1|0;_1uV=_1uY;_1uW=_1uX.b;continue;}}else{return _5;}}},_1uZ=B(_1uU(0,_1uL,_));return new T4(0,E(_1uI),E(_1uN),_1uP,_1uR);};if(0>_1uN){return new F(function(){return _1uS(0);});}else{var _1v0=_1uN+1|0;if(_1v0>=0){return new F(function(){return _1uS(_1v0);});}else{return new F(function(){return err(_1uJ);});}}}else{return E(_Vw);}};if(0>_1uN){var _1v1=B(_1uO(0)),_1v2=E(_1v1),_1v3=_1v2.d;return new T4(0,E(_1v2.a),E(_1v2.b),_1v2.c,_1v3);}else{var _1v4=B(_1uO(_1uN+1|0)),_1v5=E(_1v4),_1v6=_1v5.d;return new T4(0,E(_1v5.a),E(_1v5.b),_1v5.c,_1v6);}};return new F(function(){return _8O(_1uM);});},_1v7=function(_1v8){return new T1(3,_1v8);},_1v9=function(_1va,_1vb){var _1vc=new T(function(){var _1vd=E(_1va),_1ve=B(_fi(_1vd.a,_1vd.b,_1vd.c,E(_1vb))),_1vf=B(_gf(E(_1ve.a)&4294967295,_g3,_1vd,_1ve.b));return new T2(0,_1vf.a,_1vf.b);});return new T2(0,new T1(3,new T(function(){return E(E(_1vc).a);})),new T(function(){return E(E(_1vc).b);}));},_1vg=function(_1vh,_1vi){var _1vj=B(_1v9(_1vh,_1vi));return new T2(0,_1vj.a,_1vj.b);},_1vk=function(_1vl,_1vm){var _1vn=E(_1vl),_1vo=B(_fi(_1vn.a,_1vn.b,_1vn.c,E(_1vm))),_1vp=B(_gf(E(_1vo.a)&4294967295,_g3,_1vn,_1vo.b));return new T2(0,_1vp.a,_1vp.b);},_1vq=function(_1vr,_1vs,_1vt,_1vu){var _1vv=B(_ZH(_1vg,new T3(0,_1vr,_1vs,_1vt),_1vu)),_1vw=B(_fi(_1vr,_1vs,_1vt,E(_1vv.b))),_1vx=B(_gf(E(_1vw.a)&4294967295,_1vk,new T3(0,_1vr,_1vs,_1vt),_1vw.b));return new T2(0,new T2(0,_1vv.a,_1vx.a),_1vx.b);},_1vy=function(_1vz,_1vA){var _1vB=E(_1vz),_1vC=B(_1vq(_1vB.a,_1vB.b,_1vB.c,_1vA));return new T2(0,_1vC.a,_1vC.b);},_1vD=function(_1vE){var _1vF=new T(function(){return B(unAppCStr("getSymbol ",new T(function(){return B(_bZ(0,_1vE&4294967295,_4));})));});return new F(function(){return _107(_1vF);});},_1vG=function(_1vH,_1vI,_1vJ,_1vK){var _1vL=B(_fc(_1vH,_1vI,_1vJ,_1vK)),_1vM=_1vL.b,_1vN=E(_1vL.a);switch(_1vN){case 0:var _1vO=new T(function(){var _1vP=B(_fi(_1vH,_1vI,_1vJ,E(_1vM))),_1vQ=B(_fi(_1vH,_1vI,_1vJ,E(_1vP.b)));return new T2(0,new T(function(){return new T2(0,E(_1vP.a)&4294967295,E(_1vQ.a)&4294967295);}),_1vQ.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1vO).a);}),_4),new T(function(){return E(E(_1vO).b);}));case 1:var _1vR=new T(function(){var _1vS=B(_fi(_1vH,_1vI,_1vJ,E(_1vM))),_1vT=B(_fi(_1vH,_1vI,_1vJ,E(_1vS.b)));return new T2(0,new T(function(){return new T2(1,E(_1vS.a)&4294967295,E(_1vT.a)&4294967295);}),_1vT.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1vR).a);}),_4),new T(function(){return E(E(_1vR).b);}));case 2:var _1vU=new T(function(){var _1vV=B(_fi(_1vH,_1vI,_1vJ,E(_1vM))),_1vW=B(_fi(_1vH,_1vI,_1vJ,E(_1vV.b)));return new T2(0,new T(function(){return new T2(2,E(_1vV.a)&4294967295,E(_1vW.a)&4294967295);}),_1vW.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1vU).a);}),_4),new T(function(){return E(E(_1vU).b);}));case 3:var _1vX=B(_fi(_1vH,_1vI,_1vJ,E(_1vM))),_1vY=B(_gf(E(_1vX.a)&4294967295,_1vk,new T3(0,_1vH,_1vI,_1vJ),_1vX.b));return new T2(0,new T(function(){return B(_G(_1v7,_1vY.a));}),_1vY.b);case 4:var _1vZ=new T(function(){var _1w0=new T3(0,_1vH,_1vI,_1vJ),_1w1=B(_ZH(_1vg,_1w0,_1vM)),_1w2=B(_ZH(_1vy,_1w0,_1w1.b));return new T2(0,new T2(4,_1w1.a,_1w2.a),_1w2.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1vZ).a);}),_4),new T(function(){return E(E(_1vZ).b);}));default:return new F(function(){return _1vD(_1vN);});}},_1w3=function(_1w4,_1w5){var _1w6=E(_1w4),_1w7=B(_1vG(_1w6.a,_1w6.b,_1w6.c,E(_1w5)));return new T2(0,_1w7.a,_1w7.b);},_1w8=function(_1w9){var _1wa=E(_1w9);if(!_1wa._){return __Z;}else{return new F(function(){return _0(_1wa.a,new T(function(){return B(_1w8(_1wa.b));},1));});}},_1wb=function(_1wc,_1wd){var _1we=new T(function(){var _1wf=B(_ZH(_1w3,_1wc,_1wd));return new T2(0,_1wf.a,_1wf.b);});return new T2(0,new T(function(){return B(_1uK(B(_1w8(E(_1we).a))));}),new T(function(){return E(E(_1we).b);}));},_1wg=function(_1wh,_1wi,_1wj,_1wk){var _1wl=B(_fi(_1wh,_1wi,_1wj,_1wk));return new F(function(){return _gf(E(_1wl.a)&4294967295,_g3,new T3(0,_1wh,_1wi,_1wj),_1wl.b);});},_1wm=function(_1wn,_1wo){var _1wp=E(_1wn),_1wq=B(_1wg(_1wp.a,_1wp.b,_1wp.c,E(_1wo)));return new T2(0,_1wq.a,_1wq.b);},_1wr=function(_1ws){var _1wt=E(_1ws);return (_1wt._==0)?__Z:new T2(1,new T2(0,_M9,_1wt.a),new T(function(){return B(_1wr(_1wt.b));}));},_1wu=function(_1wv,_1ww,_1wx,_1wy){var _1wz=B(_fi(_1wv,_1ww,_1wx,_1wy)),_1wA=B(_gf(E(_1wz.a)&4294967295,_kp,new T3(0,_1wv,_1ww,_1wx),_1wz.b)),_1wB=B(_fi(_1wv,_1ww,_1wx,E(_1wA.b))),_1wC=new T(function(){return new T2(0,new T(function(){return B(_1wr(_1wA.a));}),E(_1wB.a)&4294967295);});return new T2(0,_1wC,_1wB.b);},_1wD=function(_1wE,_1wF){var _1wG=E(_1wE),_1wH=B(_1wu(_1wG.a,_1wG.b,_1wG.c,E(_1wF)));return new T2(0,_1wH.a,_1wH.b);},_1wI=new T(function(){return B(unCStr("getProduction"));}),_1wJ=new T(function(){return B(_107(_1wI));}),_1wK=function(_1wL,_1wM,_1wN,_1wO){var _1wP=B(_fc(_1wL,_1wM,_1wN,_1wO)),_1wQ=_1wP.b;switch(E(_1wP.a)){case 0:var _1wR=B(_fi(_1wL,_1wM,_1wN,E(_1wQ))),_1wS=B(_ZH(_1wD,new T3(0,_1wL,_1wM,_1wN),_1wR.b));return new T2(0,new T(function(){return new T2(0,E(_1wR.a)&4294967295,_1wS.a);}),_1wS.b);case 1:var _1wT=B(_fi(_1wL,_1wM,_1wN,E(_1wQ)));return new T2(0,new T(function(){return new T1(1,E(_1wT.a)&4294967295);}),_1wT.b);default:return E(_1wJ);}},_1wU=function(_1wV,_1wW){var _1wX=E(_1wV),_1wY=B(_1wK(_1wX.a,_1wX.b,_1wX.c,E(_1wW)));return new T2(0,_1wY.a,_1wY.b);},_1wZ=function(_1x0,_1x1){var _1x2=new T(function(){var _1x3=E(_1x0),_1x4=B(_fi(_1x3.a,_1x3.b,_1x3.c,E(_1x1)));return new T2(0,new T(function(){return E(_1x4.a)&4294967295;}),_1x4.b);}),_1x5=new T(function(){var _1x6=B(_ZH(_1wU,_1x0,new T(function(){return E(E(_1x2).b);},1)));return new T2(0,_1x6.a,_1x6.b);});return new T2(0,new T2(0,new T(function(){return E(E(_1x2).a);}),new T(function(){var _1x7=E(E(_1x5).a);if(!_1x7._){return new T0(1);}else{return B(_Pk(1,new T4(0,1,E(_1x7.a),E(_ML),E(_ML)),_1x7.b));}})),new T(function(){return E(E(_1x5).b);}));},_1x8=function(_1x9,_1xa){var _1xb=B(_1wZ(_1x9,_1xa));return new T2(0,_1xb.a,_1xb.b);},_1xc=new T(function(){return B(err(_1uJ));}),_1xd=function(_1xe,_1xf,_1xg,_1xh){var _1xi=new T(function(){var _1xj=E(_1xg),_1xk=B(_fi(_1xj.a,_1xj.b,_1xj.c,E(_1xh))),_1xl=E(_1xk.a)&4294967295,_1xm=B(_Zz(_1xl,_1xf,_1xj,_1xk.b));return new T2(0,new T2(0,_1xl,_1xm.a),_1xm.b);}),_1xn=new T(function(){var _1xo=E(E(_1xi).a),_1xp=_1xo.b,_1xq=new T(function(){return E(_1xo.a)-1|0;});return B(A(_jN,[_1xe,_jv,new T2(0,_1uI,_1xq),new T(function(){var _1xr=E(_1xq);if(0>_1xr){return B(_jP(B(_iz(0,-1)),_1xp));}else{var _1xs=_1xr+1|0;if(_1xs>=0){return B(_jP(B(_iz(0,_1xs-1|0)),_1xp));}else{return E(_1xc);}}})]));});return new T2(0,_1xn,new T(function(){return E(E(_1xi).b);}));},_1xt=function(_1xu,_1xv,_1xw,_1xx){var _1xy=B(_fi(_1xu,_1xv,_1xw,_1xx));return new F(function(){return _gf(E(_1xy.a)&4294967295,_g3,new T3(0,_1xu,_1xv,_1xw),_1xy.b);});},_1xz=function(_1xA,_1xB){var _1xC=E(_1xA),_1xD=B(_1xt(_1xC.a,_1xC.b,_1xC.c,E(_1xB)));return new T2(0,_1xD.a,_1xD.b);},_1xE=function(_1xF,_1xG,_1xH,_1xI){var _1xJ=B(_fi(_1xF,_1xG,_1xH,_1xI)),_1xK=B(_fi(_1xF,_1xG,_1xH,E(_1xJ.b))),_1xL=B(_1xd(_id,_1xz,new T3(0,_1xF,_1xG,_1xH),_1xK.b));return new T2(0,new T(function(){var _1xM=E(_1xL.a);return new T6(0,E(_1xJ.a)&4294967295,E(_1xK.a)&4294967295,E(_1xM.a),E(_1xM.b),_1xM.c,_1xM.d);}),_1xL.b);},_1xN=function(_1xO,_1xP){var _1xQ=E(_1xO),_1xR=B(_1xE(_1xQ.a,_1xQ.b,_1xQ.c,E(_1xP)));return new T2(0,_1xR.a,_1xR.b);},_1xS=0,_1xT=new T(function(){return B(unCStr("Negative range size"));}),_1xU=function(_1xV){var _1xW=B(_uU(_1xV,0)),_1xX=new T(function(){var _1xY=function(_){var _1xZ=_1xW-1|0,_1y0=function(_,_1y1){var _1y2=function(_1y3){var _1y4=_1y3-1|0;if(0<=_1y4){var _1y5=function(_1y6,_){while(1){var _=E(_1y1).d["v"]["w8"][_1y6]=0;if(_1y6!=_1y4){var _1y7=_1y6+1|0;_1y6=_1y7;continue;}else{return _5;}}},_1y8=B(_1y5(0,_));return _1y1;}else{return _1y1;}};if(0>_1xZ){return new F(function(){return _1y2(0);});}else{var _1y9=_1xZ+1|0;if(_1y9>=0){return new F(function(){return _1y2(_1y9);});}else{return new F(function(){return err(_1xT);});}}},_1ya=function(_,_1yb,_1yc,_1yd,_1ye){var _1yf=function(_1yg){var _1yh=function(_1yi,_1yj,_){while(1){if(_1yi!=_1yg){var _1yk=E(_1yj);if(!_1yk._){return _5;}else{var _=_1ye["v"]["w8"][_1yi]=E(_1yk.a),_1yl=_1yi+1|0;_1yi=_1yl;_1yj=_1yk.b;continue;}}else{return _5;}}},_1ym=B(_1yh(0,_1xV,_));return new T4(0,E(_1yb),E(_1yc),_1yd,_1ye);};if(0>_1xZ){return new F(function(){return _1yf(0);});}else{var _1yn=_1xZ+1|0;if(_1yn>=0){return new F(function(){return _1yf(_1yn);});}else{return new F(function(){return err(_1xT);});}}};if(0>_1xZ){var _1yo=newByteArr(0),_1yp=B(_1y0(_,new T4(0,E(_1xS),E(_1xZ),0,_1yo))),_1yq=E(_1yp);return new F(function(){return _1ya(_,_1yq.a,_1yq.b,_1yq.c,_1yq.d);});}else{var _1yr=_1xZ+1|0,_1ys=newByteArr(_1yr),_1yt=B(_1y0(_,new T4(0,E(_1xS),E(_1xZ),_1yr,_1ys))),_1yu=E(_1yt);return new F(function(){return _1ya(_,_1yu.a,_1yu.b,_1yu.c,_1yu.d);});}};return B(_8O(_1xY));});return new T3(0,0,_1xW,_1xX);},_1yv=function(_1yw){return new F(function(){return _bZ(0,E(_1yw)&4294967295,_4);});},_1yx=function(_1yy,_1yz){return new F(function(){return _bZ(0,E(_1yy)&4294967295,_1yz);});},_1yA=function(_1yB,_1yC){return new F(function(){return _3X(_1yx,_1yB,_1yC);});},_1yD=function(_1yE,_1yF,_1yG){return new F(function(){return _bZ(E(_1yE),E(_1yF)&4294967295,_1yG);});},_1yH=new T3(0,_1yD,_1yv,_1yA),_1yI=new T(function(){return B(unCStr("Word8"));}),_1yJ=0,_1yK=255,_1yL=new T2(0,_1yJ,_1yK),_1yM=new T2(1,_bX,_4),_1yN=function(_1yO,_1yP,_1yQ,_1yR){var _1yS=new T(function(){var _1yT=new T(function(){var _1yU=new T(function(){var _1yV=new T(function(){var _1yW=new T(function(){var _1yX=E(_1yQ),_1yY=new T(function(){return B(A3(_eg,_e6,new T2(1,new T(function(){return B(A3(_es,_1yR,_er,_1yX.a));}),new T2(1,new T(function(){return B(A3(_es,_1yR,_er,_1yX.b));}),_4)),_1yM));});return new T2(1,_bY,_1yY);});return B(unAppCStr(") is outside of bounds ",_1yW));},1);return B(_0(B(_bZ(0,E(_1yP),_4)),_1yV));});return B(unAppCStr("}: tag (",_1yU));},1);return B(_0(_1yO,_1yT));});return new F(function(){return err(B(unAppCStr("Enum.toEnum{",_1yS)));});},_1yZ=function(_1z0,_1z1,_1z2,_1z3){return new F(function(){return _1yN(_1z1,_1z2,_1z3,_1z0);});},_1z4=function(_1z5){return new F(function(){return _1yZ(_1yH,_1yI,_1z5,_1yL);});},_1z6=function(_1z7){if(_1z7<0){return new F(function(){return _1z4(_1z7);});}else{if(_1z7>255){return new F(function(){return _1z4(_1z7);});}else{return _1z7>>>0;}}},_1z8=function(_1z9){return new F(function(){return _1z6(E(_1z9));});},_1za=function(_1zb){var _1zc=E(_1zb);if(!_1zc._){return __Z;}else{var _1zd=_1zc.b,_1ze=E(_1zc.a),_1zf=function(_1zg){return (_1ze>=2048)?new T2(1,new T(function(){var _1zh=224+B(_n2(_1ze,4096))|0;if(_1zh>>>0>1114111){return B(_fK(_1zh));}else{return _1zh;}}),new T2(1,new T(function(){var _1zi=128+B(_n2(B(_o6(_1ze,4096)),64))|0;if(_1zi>>>0>1114111){return B(_fK(_1zi));}else{return _1zi;}}),new T2(1,new T(function(){var _1zj=128+B(_o6(_1ze,64))|0;if(_1zj>>>0>1114111){return B(_fK(_1zj));}else{return _1zj;}}),new T(function(){return B(_1za(_1zd));})))):new T2(1,new T(function(){var _1zk=192+B(_n2(_1ze,64))|0;if(_1zk>>>0>1114111){return B(_fK(_1zk));}else{return _1zk;}}),new T2(1,new T(function(){var _1zl=128+B(_o6(_1ze,64))|0;if(_1zl>>>0>1114111){return B(_fK(_1zl));}else{return _1zl;}}),new T(function(){return B(_1za(_1zd));})));};if(_1ze<=0){return new F(function(){return _1zf(_);});}else{if(_1ze>=128){return new F(function(){return _1zf(_);});}else{return new T2(1,_1ze,new T(function(){return B(_1za(_1zd));}));}}}},_1zm=new T(function(){return B(unCStr("linref"));}),_1zn=new T(function(){return B(_1za(_1zm));}),_1zo=new T(function(){return B(_G(_1z8,_1zn));}),_1zp=new T(function(){var _1zq=B(_1xU(_1zo));return new T3(0,_1zq.a,_1zq.b,_1zq.c);}),_1zr=function(_1zs,_1zt){var _1zu=E(_1zs),_1zv=B(_ft(_1zu.a,_1zu.b,_1zu.c,E(_1zt))),_1zw=B(_1xd(_m2,_kp,_1zu,_1zv.b));return new T2(0,new T(function(){var _1zx=E(_1zw.a);return new T5(0,_1zv.a,E(_1zx.a),E(_1zx.b),_1zx.c,_1zx.d);}),_1zw.b);},_1zy=new T(function(){return B(_1pA(_Ux,_4));}),_1zz=new T2(0,0,0),_1zA=new T2(1,_1zz,_4),_1zB=new T(function(){return B(_1uK(_1zA));}),_1zC=new T2(1,_1zB,_4),_1zD=function(_1zE,_1zF,_1zG,_1zH){var _1zI=new T3(0,_1zE,_1zF,_1zG),_1zJ=B(_ZQ(_128,_123,_1zI,_1zH)),_1zK=B(_ZQ(_128,_1wm,_1zI,_1zJ.b)),_1zL=B(_fi(_1zE,_1zF,_1zG,E(_1zK.b))),_1zM=E(_1zL.a)&4294967295,_1zN=B(_Zz(_1zM,_1wb,_1zI,_1zL.b)),_1zO=B(_fi(_1zE,_1zF,_1zG,E(_1zN.b))),_1zP=E(_1zO.a)&4294967295,_1zQ=B(_Zz(_1zP,_1zr,_1zI,_1zO.b)),_1zR=B(_QT(_PU,_1zE,_1zF,_1zG,E(_1zQ.b))),_1zS=new T(function(){var _1zT=B(_ZH(_1x8,_1zI,_1zR.b));return new T2(0,_1zT.a,_1zT.b);}),_1zU=B(_ZQ(_128,_1xN,_1zI,new T(function(){return E(E(_1zS).b);},1))),_1zV=B(_fi(_1zE,_1zF,_1zG,E(_1zU.b))),_1zW=new T(function(){var _1zX=E(_1zV.a)&4294967295,_1zY=new T(function(){var _1zZ=function(_){var _1A0=(_1zM+1|0)-1|0,_1A1=function(_1A2){if(_1A2>=0){var _1A3=newArr(_1A2,_Vu),_1A4=_1A3,_1A5=function(_1A6){var _1A7=function(_1A8,_1A9,_){while(1){if(_1A8!=_1A6){var _1Aa=E(_1A9);if(!_1Aa._){return _5;}else{var _=_1A4[_1A8]=_1Aa.a,_1Ab=_1A8+1|0;_1A8=_1Ab;_1A9=_1Aa.b;continue;}}else{return _5;}}},_1Ac=B(_1A7(0,new T(function(){return B(_0(_1zN.a,_1zC));},1),_));return new T4(0,E(_1uI),E(_1A0),_1A2,_1A4);};if(0>_1A0){return new F(function(){return _1A5(0);});}else{var _1Ad=_1A0+1|0;if(_1Ad>=0){return new F(function(){return _1A5(_1Ad);});}else{return E(_1xc);}}}else{return E(_Vw);}};if(0>_1A0){var _1Ae=B(_1A1(0)),_1Af=E(_1Ae),_1Ag=_1Af.d;return new T4(0,E(_1Af.a),E(_1Af.b),_1Af.c,_1Ag);}else{var _1Ah=B(_1A1(_1A0+1|0)),_1Ai=E(_1Ah),_1Aj=_1Ai.d;return new T4(0,E(_1Ai.a),E(_1Ai.b),_1Ai.c,_1Aj);}};return B(_8O(_1zZ));}),_1Ak=new T(function(){var _1Al=_1zX-1|0;if(0<=_1Al){var _1Am=function(_1An){return new T2(1,new T2(0,_1An,new T2(1,_1zP,_4)),new T(function(){if(_1An!=_1Al){return B(_1Am(_1An+1|0));}else{return __Z;}}));};return B(_1pA(_Ux,B(_1Am(0))));}else{return E(_1zy);}}),_1Ao=new T(function(){var _1Ap=function(_){var _1Aq=(_1zP+1|0)-1|0,_1Ar=function(_1As){if(_1As>=0){var _1At=newArr(_1As,_Vu),_1Au=_1At,_1Av=function(_1Aw){var _1Ax=function(_1Ay,_1Az,_){while(1){if(_1Ay!=_1Aw){var _1AA=E(_1Az);if(!_1AA._){return _5;}else{var _=_1Au[_1Ay]=_1AA.a,_1AB=_1Ay+1|0;_1Ay=_1AB;_1Az=_1AA.b;continue;}}else{return _5;}}},_1AC=new T(function(){var _1AD=new T(function(){var _1AE=function(_){var _1AF=newByteArr(4),_1AG=_1AF,_1AH=function(_1AI,_){while(1){var _=_1AG["v"]["i32"][_1AI]=0,_1AJ=E(_1AI);if(!_1AJ){return _5;}else{_1AI=_1AJ+1|0;continue;}}},_1AK=B(_1AH(0,_)),_1AL=function(_1AM,_1AN,_){while(1){var _1AO=E(_1AM);if(_1AO==1){return _5;}else{var _1AP=E(_1AN);if(!_1AP._){return _5;}else{var _=_1AG["v"]["i32"][_1AO]=E(_1AP.a);_1AM=_1AO+1|0;_1AN=_1AP.b;continue;}}}},_1AQ=B(_1AL(0,new T2(1,_1zM,_4),_));return new T4(0,E(_1uI),E(_1uI),1,_1AG);},_1AR=B(_8O(_1AE));return new T5(0,_1zp,E(_1AR.a),E(_1AR.b),_1AR.c,_1AR.d);});return B(_0(_1zQ.a,new T2(1,_1AD,_4)));},1),_1AS=B(_1Ax(0,_1AC,_));return new T4(0,E(_1uI),E(_1Aq),_1As,_1Au);};if(0>_1Aq){return new F(function(){return _1Av(0);});}else{var _1AT=_1Aq+1|0;if(_1AT>=0){return new F(function(){return _1Av(_1AT);});}else{return E(_1xc);}}}else{return E(_Vw);}};if(0>_1Aq){var _1AU=B(_1Ar(0)),_1AV=E(_1AU),_1AW=_1AV.d;return new T4(0,E(_1AV.a),E(_1AV.b),_1AV.c,_1AW);}else{var _1AX=B(_1Ar(_1Aq+1|0)),_1AY=E(_1AX),_1AZ=_1AY.d;return new T4(0,E(_1AY.a),E(_1AY.b),_1AY.c,_1AZ);}};return B(_8O(_1Ap));});return {_:0,a:_1zJ.a,b:_1zK.a,c:_1Ao,d:_1zR.a,e:_1Ak,f:_1zY,g:new T(function(){var _1B0=E(E(_1zS).a);if(!_1B0._){return new T0(2);}else{var _1B1=E(_1B0.a);return B(_Qc(E(_1B1.a),_1B1.b,_1B0.b,_PV));}}),h:_Ux,i:_Rg,j:_1zU.a,k:_Ux,l:_1zX};});return new T2(0,_1zW,_1zV.b);},_1B2=function(_1B3,_1B4){var _1B5=E(_1B3),_1B6=B(_1zD(_1B5.a,_1B5.b,_1B5.c,_1B4));return new T2(0,_1B6.a,_1B6.b);},_1B7=function(_1B8,_1B9){var _1Ba=E(_1B8),_1Bb=B(_IY(_Jt,_LL,_1Ba,_1B9)),_1Bc=B(_ft(_1Ba.a,_1Ba.b,_1Ba.c,E(_1Bb.b)));return new T2(0,new T2(0,_1Bb.a,_1Bc.a),_1Bc.b);},_1Bd=function(_1Be,_1Bf){var _1Bg=new T(function(){var _1Bh=B(_ZH(_113,_1Be,_1Bf));return new T2(0,_1Bh.a,_1Bh.b);}),_1Bi=B(_ZH(_1B7,_1Be,new T(function(){return E(E(_1Bg).b);},1)));return new T2(0,new T2(0,new T(function(){return E(E(_1Bg).a);}),_1Bi.a),_1Bi.b);},_1Bj=function(_1Bk,_1Bl){var _1Bm=B(_1Bd(_1Bk,_1Bl));return new T2(0,_1Bm.a,_1Bm.b);},_1Bn=function(_1Bo,_1Bp,_1Bq,_1Br,_1Bs){var _1Bt=B(_ft(_1Bp,_1Bq,_1Br,_1Bs)),_1Bu=new T3(0,_1Bp,_1Bq,_1Br),_1Bv=B(_ZQ(_128,_123,_1Bu,_1Bt.b)),_1Bw=B(_ZQ(_128,_11Y,_1Bu,_1Bv.b)),_1Bx=B(_ZQ(_128,_1Bj,_1Bu,_1Bw.b)),_1By=B(_ZQ(_128,_1B2,_1Bu,_1Bx.b));return new T2(0,new T4(0,_1Bo,_1Bt.a,new T3(0,_1Bv.a,new T(function(){return B(_Zg(_1uE,_1Bw.a));}),new T(function(){return B(_Zg(_1uB,_1Bx.a));})),new T(function(){return B(_Zg(_1ux,_1By.a));})),_1By.b);},_1Bz=function(_1BA,_1BB,_1BC,_1BD){var _1BE=B(_ZQ(_128,_123,new T3(0,_1BA,_1BB,_1BC),_1BD));return new F(function(){return _1Bn(_1BE.a,_1BA,_1BB,_1BC,E(_1BE.b));});},_1BF=function(_1BG,_1BH){var _1BI=E(_1BH);return new F(function(){return _1sr(_1BI.a,_1BI.b,_1BI.c,_1BI.d,_1BI.e,_1BI.f,_1BI.g,_1BI.j,_1BI.l);});},_1BJ=function(_1BK,_1BL,_1BM,_1BN){var _1BO=new T3(0,_1BK,_1BL,_1BM),_1BP=B(_Wj(_1BO,_1BN)),_1BQ=B(_Wj(_1BO,_1BP.b)),_1BR=_1BQ.a,_1BS=_1BQ.b,_1BT=E(_1BP.a),_1BU=function(_1BV){var _1BW=E(_1BT);if(_1BW==1){var _1BX=E(_1BR);if(!E(_1BX)){return new F(function(){return _1Bz(_1BK,_1BL,_1BM,_1BS);});}else{return new F(function(){return _Wd(_1BX,1);});}}else{return new F(function(){return _Wd(_1BR,_1BW);});}};if(E(_1BT)==2){if(E(_1BR)>1){return new F(function(){return _1BU(_);});}else{var _1BY=B(_Uk(_fH,_M6,_1BK,_1BL,_1BM,E(_1BS))),_1BZ=B(_ft(_1BK,_1BL,_1BM,E(_1BY.b))),_1C0=B(_Zk(_1BK,_1BL,_1BM,E(_1BZ.b))),_1C1=_1C0.a,_1C2=B(_Uk(_fH,_Wb,_1BK,_1BL,_1BM,E(_1C0.b))),_1C3=new T(function(){return B(_Zg(function(_1C4){return new F(function(){return _1BF(_1C1,_1C4);});},_1C2.a));});return new T2(0,new T4(0,_1BY.a,_1BZ.a,_1C1,_1C3),_1C2.b);}}else{return new F(function(){return _1BU(_);});}},_1C5=function(_1C6,_1C7,_1C8,_1C9){while(1){var _1Ca=E(_1C9);if(!_1Ca._){var _1Cb=E(_1Ca.b);switch(B(_12T(_1C6,_1C7,_1C8,_1Cb.a,_1Cb.b,_1Cb.c))){case 0:_1C9=_1Ca.d;continue;case 1:return new T1(1,_1Ca.c);default:_1C9=_1Ca.e;continue;}}else{return __Z;}}},_1Cc=function(_1Cd){return E(E(E(_1Cd).c).b);},_1Ce=new T(function(){return B(_1z6(95));}),_1Cf=new T2(1,_1Ce,_4),_1Cg=new T(function(){var _1Ch=B(_1xU(_1Cf));return new T3(0,_1Ch.a,_1Ch.b,_1Ch.c);}),_1Ci=function(_1Cj,_1Ck,_1Cl,_1Cm,_1Cn){var _1Co=E(_1Cg);if(!B(_12M(_1Cj,_1Ck,_1Cl,_1Co.a,_1Co.b,_1Co.c))){var _1Cp=E(_1Cn),_1Cq=B(_1C5(_1Cp.a,_1Cp.b,_1Cp.c,E(_1Cm).b));if(!_1Cq._){return new T0(1);}else{var _1Cr=new T(function(){var _1Cs=E(E(_1Cq.a).a);return new T3(0,_1Cs.a,_1Cs.b,_1Cs.c);});return new T2(0,new T(function(){return E(E(_1Cr).b);}),new T(function(){return B(_G(_1Cc,E(_1Cr).a));}));}}else{return new T0(1);}},_1Ct=function(_1Cu,_1Cv,_1Cw,_1Cx){while(1){var _1Cy=E(_1Cx);if(!_1Cy._){var _1Cz=E(_1Cy.b);switch(B(_12T(_1Cu,_1Cv,_1Cw,_1Cz.a,_1Cz.b,_1Cz.c))){case 0:_1Cx=_1Cy.d;continue;case 1:return new T1(1,_1Cy.c);default:_1Cx=_1Cy.e;continue;}}else{return __Z;}}},_1CA=new T(function(){return B(unCStr("S"));}),_1CB=new T(function(){return B(_1za(_1CA));}),_1CC=new T(function(){return B(_G(_1z8,_1CB));}),_1CD=new T(function(){return B(unCStr("startcat"));}),_1CE=new T(function(){return B(_1za(_1CD));}),_1CF=new T(function(){return B(_G(_1z8,_1CE));}),_1CG=new T(function(){var _1CH=B(_1xU(_1CF));return new T3(0,_1CH.a,_1CH.b,_1CH.c);}),_1CI=function(_1CJ,_1CK){var _1CL=E(_1CG),_1CM=_1CL.a,_1CN=_1CL.b,_1CO=_1CL.c,_1CP=B(_1Ct(_1CM,_1CN,_1CO,_1CJ));if(!_1CP._){var _1CQ=B(_1Ct(_1CM,_1CN,_1CO,E(_1CK).a));if(!_1CQ._){return new F(function(){return _1xU(_1CC);});}else{var _1CR=E(_1CQ.a);if(!_1CR._){return new F(function(){return _1xU(B(_G(_1z8,B(_1za(_1CR.a)))));});}else{return new F(function(){return _1xU(_1CC);});}}}else{var _1CS=E(_1CP.a);if(!_1CS._){return new F(function(){return _1xU(B(_G(_1z8,B(_1za(_1CS.a)))));});}else{return new F(function(){return _1xU(_1CC);});}}},_1CT=function(_1CU,_1CV){return new T2(0,_1CU,_1CV);},_1CW=new T(function(){return B(unCStr("empty grammar, no abstract"));}),_1CX=new T(function(){return B(err(_1CW));}),_1CY=new T4(0,_Rg,_1Cg,_1CX,_Rg),_1CZ=function(_1D0,_1D1){while(1){var _1D2=B((function(_1D3,_1D4){var _1D5=E(_1D4);if(!_1D5._){_1D0=new T2(1,_1D5.b,new T(function(){return B(_1CZ(_1D3,_1D5.e));}));_1D1=_1D5.d;return __continue;}else{return E(_1D3);}})(_1D0,_1D1));if(_1D2!=__continue){return _1D2;}}},_1D6=function(_1D7,_1D8,_1D9){var _1Da=E(_1D8);if(!_1Da._){return __Z;}else{var _1Db=E(_1D9);return (_1Db._==0)?__Z:new T2(1,new T(function(){return B(A2(_1D7,_1Da.a,_1Db.a));}),new T(function(){return B(_1D6(_1D7,_1Da.b,_1Db.b));}));}},_1Dc=function(_1Dd,_1De,_1Df,_1Dg,_1Dh,_1Di){var _1Dj=E(_1Cg);if(!B(_12M(_1De,_1Df,_1Dg,_1Dj.a,_1Dj.b,_1Dj.c))){var _1Dk=new T(function(){var _1Dl=E(_1Dh),_1Dm=B(_1CZ(_4,_1Dl.b)),_1Dn=new T(function(){return B(_G(function(_1Do){return new F(function(){return _1Ci(_1De,_1Df,_1Dg,_1Dl,_1Do);});},_1Dm));},1);return B(_1D6(_1CT,_1Dm,_1Dn));});return new T3(0,new T(function(){var _1Dp=B(_1CI(_1Dd,_1Dh));return new T3(0,_1Dp.a,_1Dp.b,_1Dp.c);}),_1Dk,new T4(0,_1Dd,new T3(0,_1De,_1Df,_1Dg),_1Dh,_1Di));}else{return new T3(0,_1Dj,_4,_1CY);}},_1Dq=new T(function(){return eval("(function(a){var arr = new ByteArray(new a.constructor(a[\'buffer\']));return new T4(0,0,a[\'length\']-1,a[\'length\'],arr);})");}),_1Dr=function(_1Ds){return E(_1Ds);},_1Dt=function(_1Du){return E(E(_1Du).a);},_1Dv=function(_1Dw){return E(E(_1Dw).a);},_1Dx=function(_1Dy){return E(E(_1Dy).a);},_1Dz=function(_1DA){return E(E(_1DA).b);},_1DB=function(_1DC){return E(E(_1DC).a);},_1DD=function(_1DE){var _1DF=new T(function(){return B(A2(_1DB,B(_1Dt(B(_1Dx(B(_1Dv(B(_1Dz(_1DE)))))))),_1Dr));}),_1DG=function(_1DH){var _1DI=function(_){return new F(function(){return __app1(E(_1Dq),E(_1DH));});};return new F(function(){return A1(_1DF,_1DI);});};return E(_1DG);},_1DJ="(function(from, to, buf){return new Uint8Array(buf.buffer.slice(from, to+from));})",_1DK=function(_1DL,_1DM,_1DN,_1DO){var _1DP=function(_){var _1DQ=eval(E(_1DJ)),_1DR=__app3(E(_1DQ),E(_1DM),E(_1DN),E(_1DO));return new F(function(){return A3(_1DD,_1DL,_1DR,0);});};return new F(function(){return _z(_1DP);});},_1DS=0,_1DT=function(_1DU){return E(E(_1DU).d);},_1DV=function(_1DW,_1DX){return new F(function(){return A2(_1DT,B(_2z(_1DW)),new T1(1,_1DX));});},_1DY=new T2(0,_2j,_1DV),_1DZ=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1E0=function(_){return new F(function(){return __app1(E(_1DZ),"div");});},_1E1=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_1E2=new T(function(){return eval("(function(e){while(e.firstChild){e.removeChild(e.firstChild);}})");}),_1E3=new T(function(){return eval("(function(c,p){p.removeChild(c);})");}),_1E4=3,_1E5=new T(function(){return eval("document.body");}),_1E6=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1E7=function(_1E8){return new F(function(){return fromJSStr(E(_1E8));});},_1E9=function(_1Ea){return E(E(_1Ea).a);},_1Eb=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_1Ec=function(_1Ed,_1Ee,_1Ef,_1Eg){var _1Eh=new T(function(){var _1Ei=function(_){var _1Ej=__app2(E(_1Eb),B(A2(_1E9,_1Ed,_1Ef)),E(_1Eg));return new T(function(){return String(_1Ej);});};return E(_1Ei);});return new F(function(){return A2(_6i,_1Ee,_1Eh);});},_1Ek=function(_1El,_1Em,_1En,_1Eo){var _1Ep=B(_2z(_1Em)),_1Eq=new T(function(){return B(_1DT(_1Ep));}),_1Er=function(_1Es){return new F(function(){return A1(_1Eq,new T(function(){return B(_1E7(_1Es));}));});},_1Et=new T(function(){return B(_1Ec(_1El,_1Em,_1En,new T(function(){return toJSStr(E(_1Eo));},1)));});return new F(function(){return A3(_1V,_1Ep,_1Et,_1Er);});},_1Eu=new T(function(){return B(unCStr("!!: negative index"));}),_1Ev=new T(function(){return B(_0(_eb,_1Eu));}),_1Ew=new T(function(){return B(err(_1Ev));}),_1Ex=new T(function(){return B(unCStr("!!: index too large"));}),_1Ey=new T(function(){return B(_0(_eb,_1Ex));}),_1Ez=new T(function(){return B(err(_1Ey));}),_1EA=function(_1EB,_1EC){while(1){var _1ED=E(_1EB);if(!_1ED._){return E(_1Ez);}else{var _1EE=E(_1EC);if(!_1EE){return E(_1ED.a);}else{_1EB=_1ED.b;_1EC=_1EE-1|0;continue;}}}},_1EF=function(_1EG,_1EH){if(_1EH>=0){return new F(function(){return _1EA(_1EG,_1EH);});}else{return E(_1Ew);}},_1EI=function(_1EJ,_1EK){var _1EL=E(_1EJ);if(!_1EL._){var _1EM=E(_1EL.c);if(!_1EM._){return __Z;}else{var _1EN=E(_1EK);return (_1EN>=0)?(_1EN<B(_uU(_1EM,0)))?new T1(1,new T(function(){return B(_1EF(_1EM,_1EN));})):__Z:__Z;}}else{return __Z;}},_1EO=function(_1EP,_1EQ){while(1){var _1ER=B((function(_1ES,_1ET){var _1EU=E(_1ET);if(!_1EU._){return new T1(1,_1ES);}else{var _1EV=_1EU.a,_1EW=E(_1EU.b);if(!_1EW._){return new F(function(){return _1EI(_1ES,_1EV);});}else{var _1EX=E(_1ES);if(!_1EX._){var _1EY=E(_1EX.c);if(!_1EY._){return __Z;}else{var _1EZ=E(_1EV);if(_1EZ>=0){if(_1EZ<B(_uU(_1EY,0))){_1EP=new T(function(){return B(_1EF(_1EY,_1EZ));});_1EQ=_1EW;return __continue;}else{return __Z;}}else{return __Z;}}}else{return __Z;}}}})(_1EP,_1EQ));if(_1ER!=__continue){return _1ER;}}},_1F0=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1F1=new T(function(){return B(err(_1F0));}),_1F2=new T(function(){return new T2(0,_18z,_1F3);}),_1F3=function(_1F4,_1F5){return (!B(A3(_pM,_1F2,_1F4,_1F5)))?true:false;},_1F6=new T2(0,_18z,_1F3),_1F7=function(_1F8,_1F9){var _1Fa=E(_1F8);if(!_1Fa._){var _1Fb=E(_1F9);if(!_1Fb._){var _1Fc=E(_1Fa.a),_1Fd=E(_1Fb.a);if(!B(_12M(_1Fc.a,_1Fc.b,_1Fc.c,_1Fd.a,_1Fd.b,_1Fd.c))){return false;}else{return new F(function(){return _18O(_1F6,_1Fa.b,_1Fb.b);});}}else{return false;}}else{return (E(_1F9)._==0)?false:true;}},_1Fe=function(_1Ff,_1Fg){return (!B(_1Fh(_1Ff,_1Fg)))?true:false;},_1Fi=new T(function(){return new T2(0,_1Fh,_1Fe);}),_1Fh=function(_1Fj,_1Fk){var _1Fl=E(_1Fj);if(!_1Fl._){var _1Fm=E(_1Fk);if(!_1Fm._){var _1Fn=E(_1Fl.a),_1Fo=E(_1Fm.a);if(!B(_12M(_1Fn.a,_1Fn.b,_1Fn.c,_1Fo.a,_1Fo.b,_1Fo.c))){return false;}else{if(!B(_1F7(_1Fl.b,_1Fm.b))){return false;}else{return new F(function(){return _18O(_1Fi,_1Fl.c,_1Fm.c);});}}}else{return false;}}else{var _1Fp=E(_1Fk);if(!_1Fp._){return false;}else{return new F(function(){return _18z(_1Fl.a,_1Fp.a);});}}},_1Fq=function(_1Fr,_1Fs){while(1){var _1Ft=E(_1Fr);if(!_1Ft._){return (E(_1Fs)._==0)?true:false;}else{var _1Fu=E(_1Fs);if(!_1Fu._){return false;}else{if(E(_1Ft.a)!=E(_1Fu.a)){return false;}else{_1Fr=_1Ft.b;_1Fs=_1Fu.b;continue;}}}}},_1Fv=function(_1Fw,_1Fx,_1Fy,_1Fz){if(!B(_1Fq(_1Fw,_1Fy))){return false;}else{return new F(function(){return _1Fh(_1Fx,_1Fz);});}},_1FA=function(_1FB,_1FC){var _1FD=E(_1FB),_1FE=E(_1FC);return new F(function(){return _1Fv(_1FD.a,_1FD.b,_1FE.a,_1FE.b);});},_1FF=function(_1FG,_1FH,_1FI,_1FJ){return (!B(_1Fq(_1FG,_1FI)))?true:(!B(_1Fh(_1FH,_1FJ)))?true:false;},_1FK=function(_1FL,_1FM){var _1FN=E(_1FL),_1FO=E(_1FM);return new F(function(){return _1FF(_1FN.a,_1FN.b,_1FO.a,_1FO.b);});},_1FP=new T2(0,_1FA,_1FK),_1FQ=function(_1FR,_1FS){var _1FT=E(_1FR),_1FU=E(_1FS);return (!B(_1Fh(_1FT.a,_1FU.a)))?true:(!B(_1np(_1FP,_1FT.b,_1FU.b)))?true:false;},_1FV=function(_1FW,_1FX,_1FY,_1FZ){if(!B(_1Fh(_1FW,_1FY))){return false;}else{return new F(function(){return _1np(_1FP,_1FX,_1FZ);});}},_1G0=function(_1G1,_1G2){var _1G3=E(_1G1),_1G4=E(_1G2);return new F(function(){return _1FV(_1G3.a,_1G3.b,_1G4.a,_1G4.b);});},_1G5=new T2(0,_1G0,_1FQ),_1G6=function(_1G7,_1G8){var _1G9=E(_1G7),_1Ga=E(_1G8);return (B(_12T(_1G9.a,_1G9.b,_1G9.c,_1Ga.a,_1Ga.b,_1Ga.c))==0)?true:false;},_1Gb=function(_1Gc){var _1Gd=E(_1Gc);return new F(function(){return _G(_12D,B(_IJ(_1Gd.a,_1Gd.b,_1Gd.c)));});},_1Ge=function(_1Gf,_1Gg){return (B(_12d(B(_1Gb(_1Gf)),B(_1Gb(_1Gg))))==2)?false:true;},_1Gh=function(_1Gi,_1Gj){var _1Gk=E(_1Gi),_1Gl=E(_1Gj);return (B(_12T(_1Gk.a,_1Gk.b,_1Gk.c,_1Gl.a,_1Gl.b,_1Gl.c))==2)?true:false;},_1Gm=function(_1Gn,_1Go){var _1Gp=E(_1Gn),_1Gq=E(_1Go);return (B(_12T(_1Gp.a,_1Gp.b,_1Gp.c,_1Gq.a,_1Gq.b,_1Gq.c))==0)?false:true;},_1Gr=function(_1Gs,_1Gt){return (B(_12d(B(_1Gb(_1Gs)),B(_1Gb(_1Gt))))==2)?E(_1Gs):E(_1Gt);},_1Gu=function(_1Gv,_1Gw){return (B(_12d(B(_1Gb(_1Gv)),B(_1Gb(_1Gw))))==2)?E(_1Gw):E(_1Gv);},_1Gx={_:0,a:_1F6,b:_1b1,c:_1G6,d:_1Ge,e:_1Gh,f:_1Gm,g:_1Gr,h:_1Gu},_1Gy=function(_1Gz,_1GA){var _1GB=E(_1Gz);if(!_1GB._){var _1GC=E(_1GA);if(!_1GC._){var _1GD=E(_1GB.a),_1GE=E(_1GC.a);switch(B(_12T(_1GD.a,_1GD.b,_1GD.c,_1GE.a,_1GE.b,_1GE.c))){case 0:return 0;case 1:return new F(function(){return _1bD(_1Gx,_1GB.b,_1GC.b);});break;default:return 2;}}else{return 0;}}else{return (E(_1GA)._==0)?2:1;}},_1GF=function(_1GG,_1GH){var _1GI=E(_1GG);if(!_1GI._){var _1GJ=E(_1GH);if(!_1GJ._){var _1GK=E(_1GI.a),_1GL=E(_1GJ.a);switch(B(_12T(_1GK.a,_1GK.b,_1GK.c,_1GL.a,_1GL.b,_1GL.c))){case 0:return true;case 1:switch(B(_1Gy(_1GI.b,_1GJ.b))){case 0:return true;case 1:return (B(_1bD(_1GM,_1GI.c,_1GJ.c))==0)?true:false;default:return false;}break;default:return false;}}else{return true;}}else{var _1GN=E(_1GH);if(!_1GN._){return false;}else{return new F(function(){return _1G6(_1GI.a,_1GN.a);});}}},_1GO=function(_1GP,_1GQ){var _1GR=E(_1GP);if(!_1GR._){var _1GS=E(_1GQ);if(!_1GS._){var _1GT=E(_1GR.a),_1GU=E(_1GS.a);switch(B(_12T(_1GT.a,_1GT.b,_1GT.c,_1GU.a,_1GU.b,_1GU.c))){case 0:return true;case 1:switch(B(_1Gy(_1GR.b,_1GS.b))){case 0:return true;case 1:return (B(_1bD(_1GM,_1GR.c,_1GS.c))==2)?false:true;default:return false;}break;default:return false;}}else{return true;}}else{var _1GV=E(_1GQ);if(!_1GV._){return false;}else{return new F(function(){return _1Ge(_1GR.a,_1GV.a);});}}},_1GW=function(_1GX,_1GY){var _1GZ=E(_1GX);if(!_1GZ._){var _1H0=E(_1GY);if(!_1H0._){var _1H1=E(_1GZ.a),_1H2=E(_1H0.a);switch(B(_12T(_1H1.a,_1H1.b,_1H1.c,_1H2.a,_1H2.b,_1H2.c))){case 0:return false;case 1:switch(B(_1Gy(_1GZ.b,_1H0.b))){case 0:return false;case 1:return (B(_1bD(_1GM,_1GZ.c,_1H0.c))==2)?true:false;default:return true;}break;default:return true;}}else{return false;}}else{var _1H3=E(_1GY);if(!_1H3._){return true;}else{return new F(function(){return _1Gh(_1GZ.a,_1H3.a);});}}},_1H4=function(_1H5,_1H6){var _1H7=E(_1H5);if(!_1H7._){var _1H8=E(_1H6);if(!_1H8._){var _1H9=E(_1H7.a),_1Ha=E(_1H8.a);switch(B(_12T(_1H9.a,_1H9.b,_1H9.c,_1Ha.a,_1Ha.b,_1Ha.c))){case 0:return false;case 1:switch(B(_1Gy(_1H7.b,_1H8.b))){case 0:return false;case 1:return (B(_1bD(_1GM,_1H7.c,_1H8.c))==0)?false:true;default:return true;}break;default:return true;}}else{return false;}}else{var _1Hb=E(_1H6);if(!_1Hb._){return true;}else{return new F(function(){return _1Gm(_1H7.a,_1Hb.a);});}}},_1Hc=function(_1Hd,_1He){return (!B(_1GO(_1Hd,_1He)))?E(_1Hd):E(_1He);},_1Hf=function(_1Hg,_1Hh){return (!B(_1GO(_1Hg,_1Hh)))?E(_1Hh):E(_1Hg);},_1GM=new T(function(){return {_:0,a:_1Fi,b:_1Hi,c:_1GF,d:_1GO,e:_1GW,f:_1H4,g:_1Hc,h:_1Hf};}),_1Hi=function(_1Hj,_1Hk){var _1Hl=E(_1Hj);if(!_1Hl._){var _1Hm=E(_1Hk);if(!_1Hm._){var _1Hn=E(_1Hl.a),_1Ho=E(_1Hm.a);switch(B(_12T(_1Hn.a,_1Hn.b,_1Hn.c,_1Ho.a,_1Ho.b,_1Ho.c))){case 0:return 0;case 1:switch(B(_1Gy(_1Hl.b,_1Hm.b))){case 0:return 0;case 1:return new F(function(){return _1bD(_1GM,_1Hl.c,_1Hm.c);});break;default:return 2;}break;default:return 2;}}else{return 0;}}else{var _1Hp=E(_1Hk);if(!_1Hp._){return 2;}else{return new F(function(){return _1b1(_1Hl.a,_1Hp.a);});}}},_1Hq=function(_1Hr,_1Hs){while(1){var _1Ht=E(_1Hr);if(!_1Ht._){return (E(_1Hs)._==0)?1:0;}else{var _1Hu=E(_1Hs);if(!_1Hu._){return 2;}else{var _1Hv=E(_1Ht.a),_1Hw=E(_1Hu.a);if(_1Hv>=_1Hw){if(_1Hv!=_1Hw){return 2;}else{_1Hr=_1Ht.b;_1Hs=_1Hu.b;continue;}}else{return 0;}}}}},_1Hx=function(_1Hy,_1Hz,_1HA,_1HB){switch(B(_1Hq(_1Hy,_1HA))){case 0:return 0;case 1:return new F(function(){return _1Hi(_1Hz,_1HB);});break;default:return 2;}},_1HC=function(_1HD,_1HE){var _1HF=E(_1HD),_1HG=E(_1HE);return new F(function(){return _1Hx(_1HF.a,_1HF.b,_1HG.a,_1HG.b);});},_1HH=function(_1HI,_1HJ,_1HK,_1HL){switch(B(_1Hq(_1HI,_1HK))){case 0:return true;case 1:return new F(function(){return _1GF(_1HJ,_1HL);});break;default:return false;}},_1HM=function(_1HN,_1HO){var _1HP=E(_1HN),_1HQ=E(_1HO);return new F(function(){return _1HH(_1HP.a,_1HP.b,_1HQ.a,_1HQ.b);});},_1HR=function(_1HS,_1HT,_1HU,_1HV){switch(B(_1Hq(_1HS,_1HU))){case 0:return true;case 1:return new F(function(){return _1GO(_1HT,_1HV);});break;default:return false;}},_1HW=function(_1HX,_1HY){var _1HZ=E(_1HX),_1I0=E(_1HY);return new F(function(){return _1HR(_1HZ.a,_1HZ.b,_1I0.a,_1I0.b);});},_1I1=function(_1I2,_1I3,_1I4,_1I5){switch(B(_1Hq(_1I2,_1I4))){case 0:return false;case 1:return new F(function(){return _1GW(_1I3,_1I5);});break;default:return true;}},_1I6=function(_1I7,_1I8){var _1I9=E(_1I7),_1Ia=E(_1I8);return new F(function(){return _1I1(_1I9.a,_1I9.b,_1Ia.a,_1Ia.b);});},_1Ib=function(_1Ic,_1Id,_1Ie,_1If){switch(B(_1Hq(_1Ic,_1Ie))){case 0:return false;case 1:return new F(function(){return _1H4(_1Id,_1If);});break;default:return true;}},_1Ig=function(_1Ih,_1Ii){var _1Ij=E(_1Ih),_1Ik=E(_1Ii);return new F(function(){return _1Ib(_1Ij.a,_1Ij.b,_1Ik.a,_1Ik.b);});},_1Il=function(_1Im,_1In){var _1Io=E(_1Im),_1Ip=E(_1In);switch(B(_1Hq(_1Io.a,_1Ip.a))){case 0:return E(_1Ip);case 1:return (!B(_1GO(_1Io.b,_1Ip.b)))?E(_1Io):E(_1Ip);default:return E(_1Io);}},_1Iq=function(_1Ir,_1Is){var _1It=E(_1Ir),_1Iu=E(_1Is);switch(B(_1Hq(_1It.a,_1Iu.a))){case 0:return E(_1It);case 1:return (!B(_1GO(_1It.b,_1Iu.b)))?E(_1Iu):E(_1It);default:return E(_1Iu);}},_1Iv={_:0,a:_1FP,b:_1HC,c:_1HM,d:_1HW,e:_1I6,f:_1Ig,g:_1Il,h:_1Iq},_1Iw=function(_1Ix){return new F(function(){return _1ni(_4,_1Ix);});},_1Iy=function(_1Iz,_1IA,_1IB,_1IC){switch(B(_1Hi(_1Iz,_1IB))){case 0:return true;case 1:return (B(_1bD(_1Iv,B(_1Iw(_1IA)),B(_1Iw(_1IC))))==0)?true:false;default:return false;}},_1ID=function(_1IE,_1IF){var _1IG=E(_1IE),_1IH=E(_1IF);return new F(function(){return _1Iy(_1IG.a,_1IG.b,_1IH.a,_1IH.b);});},_1II=function(_1IJ,_1IK,_1IL,_1IM){switch(B(_1Hi(_1IJ,_1IL))){case 0:return true;case 1:return (B(_1bD(_1Iv,B(_1Iw(_1IK)),B(_1Iw(_1IM))))==2)?false:true;default:return false;}},_1IN=function(_1IO,_1IP){var _1IQ=E(_1IO),_1IR=E(_1IP);return new F(function(){return _1II(_1IQ.a,_1IQ.b,_1IR.a,_1IR.b);});},_1IS=function(_1IT,_1IU,_1IV,_1IW){switch(B(_1Hi(_1IT,_1IV))){case 0:return false;case 1:return (B(_1bD(_1Iv,B(_1Iw(_1IU)),B(_1Iw(_1IW))))==2)?true:false;default:return true;}},_1IX=function(_1IY,_1IZ){var _1J0=E(_1IY),_1J1=E(_1IZ);return new F(function(){return _1IS(_1J0.a,_1J0.b,_1J1.a,_1J1.b);});},_1J2=function(_1J3,_1J4,_1J5,_1J6){switch(B(_1Hi(_1J3,_1J5))){case 0:return false;case 1:return (B(_1bD(_1Iv,B(_1Iw(_1J4)),B(_1Iw(_1J6))))==0)?false:true;default:return true;}},_1J7=function(_1J8,_1J9){var _1Ja=E(_1J8),_1Jb=E(_1J9);return new F(function(){return _1J2(_1Ja.a,_1Ja.b,_1Jb.a,_1Jb.b);});},_1Jc=function(_1Jd,_1Je,_1Jf,_1Jg){switch(B(_1Hi(_1Jd,_1Jf))){case 0:return 0;case 1:return new F(function(){return _1bD(_1Iv,B(_1Iw(_1Je)),B(_1Iw(_1Jg)));});break;default:return 2;}},_1Jh=function(_1Ji,_1Jj){var _1Jk=E(_1Ji),_1Jl=E(_1Jj);return new F(function(){return _1Jc(_1Jk.a,_1Jk.b,_1Jl.a,_1Jl.b);});},_1Jm=function(_1Jn,_1Jo){var _1Jp=E(_1Jn),_1Jq=E(_1Jo);switch(B(_1Hi(_1Jp.a,_1Jq.a))){case 0:return E(_1Jq);case 1:return (B(_1bD(_1Iv,B(_1Iw(_1Jp.b)),B(_1Iw(_1Jq.b))))==2)?E(_1Jp):E(_1Jq);default:return E(_1Jp);}},_1Jr=function(_1Js,_1Jt){var _1Ju=E(_1Js),_1Jv=E(_1Jt);switch(B(_1Hi(_1Ju.a,_1Jv.a))){case 0:return E(_1Ju);case 1:return (B(_1bD(_1Iv,B(_1Iw(_1Ju.b)),B(_1Iw(_1Jv.b))))==2)?E(_1Jv):E(_1Ju);default:return E(_1Jv);}},_1Jw={_:0,a:_1G5,b:_1Jh,c:_1ID,d:_1IN,e:_1IX,f:_1J7,g:_1Jm,h:_1Jr},_1Jx=function(_1Jy,_1Jz,_1JA){var _1JB=E(_1JA);if(!_1JB._){var _1JC=_1JB.c,_1JD=_1JB.d,_1JE=E(_1JB.b);switch(B(_1Hi(_1Jy,_1JE.a))){case 0:return new F(function(){return _Ns(_1JE,B(_1Jx(_1Jy,_1Jz,_1JC)),_1JD);});break;case 1:switch(B(_1bD(_1Iv,B(_1Iw(_1Jz)),B(_1Iw(_1JE.b))))){case 0:return new F(function(){return _Ns(_1JE,B(_1Jx(_1Jy,_1Jz,_1JC)),_1JD);});break;case 1:return new F(function(){return _15i(_1JC,_1JD);});break;default:return new F(function(){return _MQ(_1JE,_1JC,B(_1Jx(_1Jy,_1Jz,_1JD)));});}break;default:return new F(function(){return _MQ(_1JE,_1JC,B(_1Jx(_1Jy,_1Jz,_1JD)));});}}else{return new T0(1);}},_1JF=function(_1JG,_1JH){var _1JI=E(_1JG),_1JJ=E(_1JH);if(!_1JJ._){var _1JK=_1JJ.b,_1JL=_1JJ.c,_1JM=_1JJ.d;switch(B(_1bD(_1Jw,B(_1ni(_4,_1JI)),B(_1ni(_4,_1JK))))){case 0:return new F(function(){return _MQ(_1JK,B(_1JF(_1JI,_1JL)),_1JM);});break;case 1:return new T4(0,_1JJ.a,E(_1JI),E(_1JL),E(_1JM));default:return new F(function(){return _Ns(_1JK,_1JL,B(_1JF(_1JI,_1JM)));});}}else{return new T4(0,1,E(_1JI),E(_ML),E(_ML));}},_1JN=function(_1JO,_1JP){while(1){var _1JQ=E(_1JP);if(!_1JQ._){return E(_1JO);}else{var _1JR=B(_1JF(_1JQ.a,_1JO));_1JO=_1JR;_1JP=_1JQ.b;continue;}}},_1JS=function(_1JT,_1JU){var _1JV=E(_1JU);if(!_1JV._){return new T3(0,_ML,_4,_4);}else{var _1JW=_1JV.a,_1JX=E(_1JT);if(_1JX==1){var _1JY=E(_1JV.b);return (_1JY._==0)?new T3(0,new T(function(){return new T4(0,1,E(_1JW),E(_ML),E(_ML));}),_4,_4):(B(_1bD(_1Jw,B(_1Iw(_1JW)),B(_1Iw(_1JY.a))))==0)?new T3(0,new T(function(){return new T4(0,1,E(_1JW),E(_ML),E(_ML));}),_1JY,_4):new T3(0,new T(function(){return new T4(0,1,E(_1JW),E(_ML),E(_ML));}),_4,_1JY);}else{var _1JZ=B(_1JS(_1JX>>1,_1JV)),_1K0=_1JZ.a,_1K1=_1JZ.c,_1K2=E(_1JZ.b);if(!_1K2._){return new T3(0,_1K0,_4,_1K1);}else{var _1K3=_1K2.a,_1K4=E(_1K2.b);if(!_1K4._){return new T3(0,new T(function(){return B(_O8(_1K3,_1K0));}),_4,_1K1);}else{if(!B(_1bD(_1Jw,B(_1Iw(_1K3)),B(_1Iw(_1K4.a))))){var _1K5=B(_1JS(_1JX>>1,_1K4));return new T3(0,new T(function(){return B(_OM(_1K3,_1K0,_1K5.a));}),_1K5.b,_1K5.c);}else{return new T3(0,_1K0,_4,_1K2);}}}}}},_1K6=function(_1K7,_1K8,_1K9){while(1){var _1Ka=E(_1K9);if(!_1Ka._){return E(_1K8);}else{var _1Kb=_1Ka.a,_1Kc=E(_1Ka.b);if(!_1Kc._){return new F(function(){return _O8(_1Kb,_1K8);});}else{if(!B(_1bD(_1Jw,B(_1Iw(_1Kb)),B(_1Iw(_1Kc.a))))){var _1Kd=B(_1JS(_1K7,_1Kc)),_1Ke=_1Kd.a,_1Kf=E(_1Kd.c);if(!_1Kf._){var _1Kg=_1K7<<1,_1Kh=B(_OM(_1Kb,_1K8,_1Ke));_1K7=_1Kg;_1K8=_1Kh;_1K9=_1Kd.b;continue;}else{return new F(function(){return _1JN(B(_OM(_1Kb,_1K8,_1Ke)),_1Kf);});}}else{return new F(function(){return _1JN(_1K8,_1Ka);});}}}}},_1Ki=function(_1Kj){var _1Kk=E(_1Kj);if(!_1Kk._){return new T0(1);}else{var _1Kl=_1Kk.a,_1Km=E(_1Kk.b);if(!_1Km._){return new T4(0,1,E(_1Kl),E(_ML),E(_ML));}else{if(!B(_1bD(_1Jw,B(_1Iw(_1Kl)),B(_1Iw(_1Km.a))))){return new F(function(){return _1K6(1,new T4(0,1,E(_1Kl),E(_ML),E(_ML)),_1Km);});}else{return new F(function(){return _1JN(new T4(0,1,E(_1Kl),E(_ML),E(_ML)),_1Km);});}}}},_1Kn=function(_1Ko,_1Kp){while(1){var _1Kq=E(_1Kp);if(!_1Kq._){return E(_1Ko);}else{var _1Kr=_1Kq.a,_1Ks=E(_1Ko);if(!_1Ks._){var _1Kt=E(_1Kr);if(!_1Kt._){var _1Ku=B(_1jx(_1Jw,_1il,_1il,_1Ks.a,_1Ks.b,_1Ks.c,_1Ks.d,_1Kt.a,_1Kt.b,_1Kt.c,_1Kt.d));}else{var _1Ku=E(_1Ks);}var _1Kv=_1Ku;}else{var _1Kv=E(_1Kr);}_1Ko=_1Kv;_1Kp=_1Kq.b;continue;}}},_1Kw=function(_1Kx,_1Ky,_1Kz){var _1KA=E(_1Kz);if(!_1KA._){var _1KB=_1KA.c,_1KC=_1KA.d,_1KD=E(_1KA.b);switch(B(_1Hi(_1Kx,_1KD.a))){case 0:return new F(function(){return _MQ(_1KD,B(_1Kw(_1Kx,_1Ky,_1KB)),_1KC);});break;case 1:switch(B(_1bD(_1Iv,B(_1Iw(_1Ky)),B(_1Iw(_1KD.b))))){case 0:return new F(function(){return _MQ(_1KD,B(_1Kw(_1Kx,_1Ky,_1KB)),_1KC);});break;case 1:return new T4(0,_1KA.a,E(new T2(0,_1Kx,_1Ky)),E(_1KB),E(_1KC));default:return new F(function(){return _Ns(_1KD,_1KB,B(_1Kw(_1Kx,_1Ky,_1KC)));});}break;default:return new F(function(){return _Ns(_1KD,_1KB,B(_1Kw(_1Kx,_1Ky,_1KC)));});}}else{return new T4(0,1,E(new T2(0,_1Kx,_1Ky)),E(_ML),E(_ML));}},_1KE=function(_1KF,_1KG){while(1){var _1KH=E(_1KG);if(!_1KH._){return E(_1KF);}else{var _1KI=E(_1KH.a),_1KJ=B(_1Kw(_1KI.a,_1KI.b,_1KF));_1KF=_1KJ;_1KG=_1KH.b;continue;}}},_1KK=function(_1KL,_1KM){var _1KN=E(_1KM);if(!_1KN._){return new T3(0,_ML,_4,_4);}else{var _1KO=_1KN.a,_1KP=E(_1KL);if(_1KP==1){var _1KQ=E(_1KN.b);if(!_1KQ._){return new T3(0,new T(function(){return new T4(0,1,E(_1KO),E(_ML),E(_ML));}),_4,_4);}else{var _1KR=E(_1KO),_1KS=E(_1KQ.a);switch(B(_1Hi(_1KR.a,_1KS.a))){case 0:return new T3(0,new T4(0,1,E(_1KR),E(_ML),E(_ML)),_1KQ,_4);case 1:return (B(_1bD(_1Iv,B(_1Iw(_1KR.b)),B(_1Iw(_1KS.b))))==0)?new T3(0,new T4(0,1,E(_1KR),E(_ML),E(_ML)),_1KQ,_4):new T3(0,new T4(0,1,E(_1KR),E(_ML),E(_ML)),_4,_1KQ);default:return new T3(0,new T4(0,1,E(_1KR),E(_ML),E(_ML)),_4,_1KQ);}}}else{var _1KT=B(_1KK(_1KP>>1,_1KN)),_1KU=_1KT.a,_1KV=_1KT.c,_1KW=E(_1KT.b);if(!_1KW._){return new T3(0,_1KU,_4,_1KV);}else{var _1KX=_1KW.a,_1KY=E(_1KW.b);if(!_1KY._){return new T3(0,new T(function(){return B(_O8(_1KX,_1KU));}),_4,_1KV);}else{var _1KZ=E(_1KX),_1L0=E(_1KY.a),_1L1=function(_1L2){var _1L3=B(_1KK(_1KP>>1,_1KY));return new T3(0,new T(function(){return B(_OM(_1KZ,_1KU,_1L3.a));}),_1L3.b,_1L3.c);};switch(B(_1Hi(_1KZ.a,_1L0.a))){case 0:return new F(function(){return _1L1(_);});break;case 1:if(!B(_1bD(_1Iv,B(_1Iw(_1KZ.b)),B(_1Iw(_1L0.b))))){return new F(function(){return _1L1(_);});}else{return new T3(0,_1KU,_4,_1KW);}break;default:return new T3(0,_1KU,_4,_1KW);}}}}}},_1L4=function(_1L5,_1L6,_1L7){var _1L8=E(_1L7);if(!_1L8._){return E(_1L6);}else{var _1L9=_1L8.a,_1La=E(_1L8.b);if(!_1La._){return new F(function(){return _O8(_1L9,_1L6);});}else{var _1Lb=E(_1L9),_1Lc=E(_1La.a),_1Ld=function(_1Le){var _1Lf=B(_1KK(_1L5,_1La)),_1Lg=_1Lf.a,_1Lh=E(_1Lf.c);if(!_1Lh._){return new F(function(){return _1L4(_1L5<<1,B(_OM(_1Lb,_1L6,_1Lg)),_1Lf.b);});}else{return new F(function(){return _1KE(B(_OM(_1Lb,_1L6,_1Lg)),_1Lh);});}};switch(B(_1Hi(_1Lb.a,_1Lc.a))){case 0:return new F(function(){return _1Ld(_);});break;case 1:if(!B(_1bD(_1Iv,B(_1Iw(_1Lb.b)),B(_1Iw(_1Lc.b))))){return new F(function(){return _1Ld(_);});}else{return new F(function(){return _1KE(_1L6,_1L8);});}break;default:return new F(function(){return _1KE(_1L6,_1L8);});}}}},_1Li=function(_1Lj){var _1Lk=E(_1Lj);if(!_1Lk._){return new T0(1);}else{var _1Ll=_1Lk.a,_1Lm=E(_1Lk.b);if(!_1Lm._){return new T4(0,1,E(_1Ll),E(_ML),E(_ML));}else{var _1Ln=E(_1Ll),_1Lo=E(_1Lm.a);switch(B(_1Hi(_1Ln.a,_1Lo.a))){case 0:return new F(function(){return _1L4(1,new T4(0,1,E(_1Ln),E(_ML),E(_ML)),_1Lm);});break;case 1:if(!B(_1bD(_1Iv,B(_1Iw(_1Ln.b)),B(_1Iw(_1Lo.b))))){return new F(function(){return _1L4(1,new T4(0,1,E(_1Ln),E(_ML),E(_ML)),_1Lm);});}else{return new F(function(){return _1KE(new T4(0,1,E(_1Ln),E(_ML),E(_ML)),_1Lm);});}break;default:return new F(function(){return _1KE(new T4(0,1,E(_1Ln),E(_ML),E(_ML)),_1Lm);});}}}},_1Lp=function(_1Lq,_1Lr,_1Ls){var _1Lt=E(_1Ls);if(!_1Lt._){var _1Lu=_1Lt.c,_1Lv=_1Lt.d,_1Lw=E(_1Lt.b);switch(B(_1Hq(_1Lq,_1Lw.a))){case 0:return new F(function(){return _MQ(_1Lw,B(_1Lp(_1Lq,_1Lr,_1Lu)),_1Lv);});break;case 1:switch(B(_1Hi(_1Lr,_1Lw.b))){case 0:return new F(function(){return _MQ(_1Lw,B(_1Lp(_1Lq,_1Lr,_1Lu)),_1Lv);});break;case 1:return new T4(0,_1Lt.a,E(new T2(0,_1Lq,_1Lr)),E(_1Lu),E(_1Lv));default:return new F(function(){return _Ns(_1Lw,_1Lu,B(_1Lp(_1Lq,_1Lr,_1Lv)));});}break;default:return new F(function(){return _Ns(_1Lw,_1Lu,B(_1Lp(_1Lq,_1Lr,_1Lv)));});}}else{return new T4(0,1,E(new T2(0,_1Lq,_1Lr)),E(_ML),E(_ML));}},_1Lx=function(_1Ly,_1Lz){while(1){var _1LA=E(_1Lz);if(!_1LA._){return E(_1Ly);}else{var _1LB=E(_1LA.a),_1LC=B(_1Lp(_1LB.a,_1LB.b,_1Ly));_1Ly=_1LC;_1Lz=_1LA.b;continue;}}},_1LD=function(_1LE,_1LF){var _1LG=E(_1LF);if(!_1LG._){return new T3(0,_ML,_4,_4);}else{var _1LH=_1LG.a,_1LI=E(_1LE);if(_1LI==1){var _1LJ=E(_1LG.b);if(!_1LJ._){return new T3(0,new T(function(){return new T4(0,1,E(_1LH),E(_ML),E(_ML));}),_4,_4);}else{var _1LK=E(_1LH),_1LL=E(_1LJ.a);switch(B(_1Hq(_1LK.a,_1LL.a))){case 0:return new T3(0,new T4(0,1,E(_1LK),E(_ML),E(_ML)),_1LJ,_4);case 1:return (!B(_1H4(_1LK.b,_1LL.b)))?new T3(0,new T4(0,1,E(_1LK),E(_ML),E(_ML)),_1LJ,_4):new T3(0,new T4(0,1,E(_1LK),E(_ML),E(_ML)),_4,_1LJ);default:return new T3(0,new T4(0,1,E(_1LK),E(_ML),E(_ML)),_4,_1LJ);}}}else{var _1LM=B(_1LD(_1LI>>1,_1LG)),_1LN=_1LM.a,_1LO=_1LM.c,_1LP=E(_1LM.b);if(!_1LP._){return new T3(0,_1LN,_4,_1LO);}else{var _1LQ=_1LP.a,_1LR=E(_1LP.b);if(!_1LR._){return new T3(0,new T(function(){return B(_O8(_1LQ,_1LN));}),_4,_1LO);}else{var _1LS=E(_1LQ),_1LT=E(_1LR.a);switch(B(_1Hq(_1LS.a,_1LT.a))){case 0:var _1LU=B(_1LD(_1LI>>1,_1LR));return new T3(0,new T(function(){return B(_OM(_1LS,_1LN,_1LU.a));}),_1LU.b,_1LU.c);case 1:if(!B(_1H4(_1LS.b,_1LT.b))){var _1LV=B(_1LD(_1LI>>1,_1LR));return new T3(0,new T(function(){return B(_OM(_1LS,_1LN,_1LV.a));}),_1LV.b,_1LV.c);}else{return new T3(0,_1LN,_4,_1LP);}break;default:return new T3(0,_1LN,_4,_1LP);}}}}}},_1LW=function(_1LX,_1LY,_1LZ){var _1M0=E(_1LZ);if(!_1M0._){return E(_1LY);}else{var _1M1=_1M0.a,_1M2=E(_1M0.b);if(!_1M2._){return new F(function(){return _O8(_1M1,_1LY);});}else{var _1M3=E(_1M1),_1M4=E(_1M2.a),_1M5=function(_1M6){var _1M7=B(_1LD(_1LX,_1M2)),_1M8=_1M7.a,_1M9=E(_1M7.c);if(!_1M9._){return new F(function(){return _1LW(_1LX<<1,B(_OM(_1M3,_1LY,_1M8)),_1M7.b);});}else{return new F(function(){return _1Lx(B(_OM(_1M3,_1LY,_1M8)),_1M9);});}};switch(B(_1Hq(_1M3.a,_1M4.a))){case 0:return new F(function(){return _1M5(_);});break;case 1:if(!B(_1H4(_1M3.b,_1M4.b))){return new F(function(){return _1M5(_);});}else{return new F(function(){return _1Lx(_1LY,_1M0);});}break;default:return new F(function(){return _1Lx(_1LY,_1M0);});}}}},_1Ma=function(_1Mb){var _1Mc=E(_1Mb);if(!_1Mc._){return new T0(1);}else{var _1Md=_1Mc.a,_1Me=E(_1Mc.b);if(!_1Me._){return new T4(0,1,E(_1Md),E(_ML),E(_ML));}else{var _1Mf=E(_1Md),_1Mg=E(_1Me.a);switch(B(_1Hq(_1Mf.a,_1Mg.a))){case 0:return new F(function(){return _1LW(1,new T4(0,1,E(_1Mf),E(_ML),E(_ML)),_1Me);});break;case 1:if(!B(_1H4(_1Mf.b,_1Mg.b))){return new F(function(){return _1LW(1,new T4(0,1,E(_1Mf),E(_ML),E(_ML)),_1Me);});}else{return new F(function(){return _1Lx(new T4(0,1,E(_1Mf),E(_ML),E(_ML)),_1Me);});}break;default:return new F(function(){return _1Lx(new T4(0,1,E(_1Mf),E(_ML),E(_ML)),_1Me);});}}}},_1Mh=function(_1Mi){return new T1(1,_1Mi);},_1Mj=function(_1Mk){return E(E(_1Mk).a);},_1Ml=function(_1Mm,_1Mn){var _1Mo=E(_1Mm);if(!_1Mo._){var _1Mp=_1Mo.c,_1Mq=B(_uU(_1Mp,0));if(0<=_1Mq){var _1Mr=function(_1Ms,_1Mt){var _1Mu=E(_1Mt);if(!_1Mu._){return __Z;}else{return new F(function(){return _0(B(_1Ml(_1Mu.a,new T(function(){return B(_0(_1Mn,new T2(1,_1Ms,_4)));}))),new T(function(){if(_1Ms!=_1Mq){return B(_1Mr(_1Ms+1|0,_1Mu.b));}else{return __Z;}},1));});}};return new F(function(){return _1Mr(0,_1Mp);});}else{return __Z;}}else{return new T2(1,new T2(0,_1Mn,_1Mo.a),_4);}},_1Mv=function(_1Mw,_1Mx){var _1My=E(_1Mx);if(!_1My._){return new T2(0,_4,_4);}else{var _1Mz=_1My.a,_1MA=_1My.b,_1MB=E(_1Mw);if(_1MB==1){return new T2(0,new T2(1,_1Mz,_4),_1MA);}else{var _1MC=new T(function(){var _1MD=B(_1Mv(_1MB-1|0,_1MA));return new T2(0,_1MD.a,_1MD.b);});return new T2(0,new T2(1,_1Mz,new T(function(){return E(E(_1MC).a);})),new T(function(){return E(E(_1MC).b);}));}}},_1ME=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_1MF=function(_1MG){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_1MG,_1ME));})),_6y);});},_1MH=new T(function(){return B(_1MF("Muste/Tree/Internal.hs:217:9-39|(pre, _ : post)"));}),_1MI=function(_1MJ,_1MK,_1ML){if(0>_1MK){return E(_1MJ);}else{if(_1MK>=B(_uU(_1MJ,0))){return E(_1MJ);}else{if(_1MK>0){var _1MM=B(_1Mv(_1MK,_1MJ)),_1MN=E(_1MM.b);if(!_1MN._){return E(_1MH);}else{return new F(function(){return _0(_1MM.a,new T2(1,_1ML,_1MN.b));});}}else{var _1MO=E(_1MJ);if(!_1MO._){return E(_1MH);}else{return new F(function(){return _0(_4,new T2(1,_1ML,_1MO.b));});}}}}},_1MP=function(_1MQ,_1MR,_1MS){var _1MT=E(_1MQ);if(!_1MT._){var _1MU=_1MT.c,_1MV=E(_1MR);if(!_1MV._){return E(_1MS);}else{var _1MW=E(_1MV.a);if(_1MW<0){return E(_1MT);}else{var _1MX=B(_uU(_1MU,0));if(_1MW>=_1MX){return E(_1MT);}else{var _1MY=new T(function(){return B(_1MI(_1MU,_1MW,new T(function(){var _1MZ=E(_1MU);if(!_1MZ._){return E(_1F1);}else{if(_1MW>=0){if(_1MW<_1MX){return B(_1MP(B(_1EF(_1MZ,_1MW)),_1MV.b,_1MS));}else{return E(_1F1);}}else{return E(_1F1);}}})));});return new T3(0,_1MT.a,_1MT.b,_1MY);}}}}else{return (E(_1MR)._==0)?E(_1MS):E(_1MT);}},_1N0=function(_1N1,_1N2,_1N3,_1N4,_1N5){while(1){var _1N6=B((function(_1N7,_1N8,_1N9,_1Na,_1Nb){var _1Nc=E(_1Na);if(!_1Nc._){var _1Nd=E(_1Nb);if(!_1Nd._){return new T2(0,_1N7,_1N8);}else{var _1Ne=_1Nd.a,_1Nf=new T3(0,_1N9,_1Nc,new T(function(){return B(_G(_1Mh,_1Nc.b));})),_1Ng=new T(function(){var _1Nh=function(_1Ni){var _1Nj=E(_1Ni);return new T2(0,new T(function(){return B(_0(_1Ne,_1Nj.a));}),new T1(1,_1Nj.b));},_1Nk=B(_1Ma(B(_G(_1Nh,B(_1Ml(_1Nf,_4)))))),_1Nl=B(_1o1(function(_1Nm){return (!B(_1Fq(_1Ne,B(_1Mj(_1Nm)))))?true:false;},_1N8));if(!_1Nl._){var _1Nn=E(_1Nk);if(!_1Nn._){return B(_1jx(_1Iv,_1il,_1il,_1Nl.a,_1Nl.b,_1Nl.c,_1Nl.d,_1Nn.a,_1Nn.b,_1Nn.c,_1Nn.d));}else{return E(_1Nl);}}else{return E(_1Nk);}}),_1No=_1N9;_1N1=new T(function(){return B(_1MP(_1N7,_1Ne,_1Nf));});_1N2=_1Ng;_1N3=_1No;_1N4=_1Nc;_1N5=_1Nd.b;return __continue;}}else{return new T2(0,_1N7,_1N8);}})(_1N1,_1N2,_1N3,_1N4,_1N5));if(_1N6!=__continue){return _1N6;}}},_1Np=new T2(1,_4,_4),_1Nq=function(_1Nr){var _1Ns=E(_1Nr);if(!_1Ns._){return E(_1Np);}else{var _1Nt=_1Ns.b,_1Nu=new T(function(){return B(_G(function(_1Mi){return new T2(1,_1Ns.a,_1Mi);},B(_1Nq(_1Nt))));},1);return new F(function(){return _0(B(_1Nq(_1Nt)),_1Nu);});}},_1Nv=function(_1Nw,_1Nx,_1Ny,_1Nz){var _1NA=new T(function(){return E(_1Ny)-1|0;}),_1NB=function(_1NC){var _1ND=E(_1NC);if(!_1ND._){return __Z;}else{var _1NE=_1ND.b,_1NF=E(_1ND.a),_1NG=_1NF.a,_1NH=function(_1NI,_1NJ,_1NK){var _1NL=E(_1NF.b);if(!B(_12M(_1NI,_1NJ,_1NK,_1NL.a,_1NL.b,_1NL.c))){return new F(function(){return _1NB(_1NE);});}else{if(B(_uU(_1NG,0))>E(_1NA)){return new F(function(){return _1NB(_1NE);});}else{return new T2(1,_1NG,new T(function(){return B(_1NB(_1NE));}));}}},_1NM=E(E(_1Nz).b);if(!_1NM._){var _1NN=E(_1NM.a);return new F(function(){return _1NH(_1NN.a,_1NN.b,_1NN.c);});}else{var _1NO=E(_1Cg);return new F(function(){return _1NH(_1NO.a,_1NO.b,_1NO.c);});}}},_1NP=function(_1NQ){var _1NR=new T(function(){var _1NS=E(_1Nz),_1NT=B(_1N0(_1Nw,_1Nx,_1NS.a,_1NS.b,_1NQ));return new T2(0,_1NT.a,_1NT.b);}),_1NU=new T(function(){return E(E(_1NR).a);}),_1NV=new T(function(){var _1NW=function(_1NX){var _1NY=B(_1EO(_1NU,E(_1NX).a));return (_1NY._==0)?false:(E(_1NY.a)._==0)?false:true;},_1NZ=E(E(_1NR).b);if(!_1NZ._){var _1O0=E(_1Nx);if(!_1O0._){return B(_1o1(_1NW,B(_1jx(_1Iv,_1il,_1il,_1NZ.a,_1NZ.b,_1NZ.c,_1NZ.d,_1O0.a,_1O0.b,_1O0.c,_1O0.d))));}else{return B(_1o1(_1NW,_1NZ));}}else{return B(_1o1(_1NW,_1Nx));}});return new T2(0,_1NU,_1NV);};return new F(function(){return _1Li(B(_G(_1NP,B(_1Nq(B(_1NB(B(_1Ml(_1Nw,_4)))))))));});},_1O1=function(_1O2,_1O3){while(1){var _1O4=E(_1O3);if(!_1O4._){return E(_1O2);}else{var _1O5=_1O4.a,_1O6=E(_1O2);if(!_1O6._){var _1O7=E(_1O5);if(!_1O7._){var _1O8=B(_1jx(_1Gx,_1il,_1il,_1O6.a,_1O6.b,_1O6.c,_1O6.d,_1O7.a,_1O7.b,_1O7.c,_1O7.d));}else{var _1O8=E(_1O6);}var _1O9=_1O8;}else{var _1O9=E(_1O5);}_1O2=_1O9;_1O3=_1O4.b;continue;}}},_1Oa=function(_1Ob){var _1Oc=E(_1Ob);if(!_1Oc._){return new F(function(){return _1O1(_ML,B(_G(_1Oa,_1Oc.c)));});}else{return new F(function(){return _O2(_1Oc.a);});}},_1Od=function(_1Oe,_1Of,_1Og){var _1Oh=E(_1Og);if(!_1Oh._){var _1Oi=_1Oh.c,_1Oj=_1Oh.d,_1Ok=E(_1Oh.b),_1Ol=E(_1Oe),_1Om=E(_1Ok.a);switch(B(_12T(_1Ol.a,_1Ol.b,_1Ol.c,_1Om.a,_1Om.b,_1Om.c))){case 0:return new F(function(){return _MQ(_1Ok,B(_1Od(_1Ol,_1Of,_1Oi)),_1Oj);});break;case 1:switch(B(_1Gy(_1Of,_1Ok.b))){case 0:return new F(function(){return _MQ(_1Ok,B(_1Od(_1Ol,_1Of,_1Oi)),_1Oj);});break;case 1:return new T4(0,_1Oh.a,E(new T2(0,_1Ol,_1Of)),E(_1Oi),E(_1Oj));default:return new F(function(){return _Ns(_1Ok,_1Oi,B(_1Od(_1Ol,_1Of,_1Oj)));});}break;default:return new F(function(){return _Ns(_1Ok,_1Oi,B(_1Od(_1Ol,_1Of,_1Oj)));});}}else{return new T4(0,1,E(new T2(0,_1Oe,_1Of)),E(_ML),E(_ML));}},_1On=function(_1Oo,_1Op){while(1){var _1Oq=E(_1Op);if(!_1Oq._){return E(_1Oo);}else{var _1Or=E(_1Oq.a),_1Os=B(_1Od(_1Or.a,_1Or.b,_1Oo));_1Oo=_1Os;_1Op=_1Oq.b;continue;}}},_1Ot=function(_1Ou,_1Ov){var _1Ow=E(_1Ov);if(!_1Ow._){return new T3(0,_ML,_4,_4);}else{var _1Ox=_1Ow.a,_1Oy=E(_1Ou);if(_1Oy==1){var _1Oz=E(_1Ow.b);if(!_1Oz._){return new T3(0,new T(function(){return new T4(0,1,E(_1Ox),E(_ML),E(_ML));}),_4,_4);}else{var _1OA=E(_1Ox),_1OB=E(_1Oz.a),_1OC=_1OB.b,_1OD=E(_1OA.a),_1OE=E(_1OB.a);switch(B(_12T(_1OD.a,_1OD.b,_1OD.c,_1OE.a,_1OE.b,_1OE.c))){case 0:return new T3(0,new T4(0,1,E(_1OA),E(_ML),E(_ML)),_1Oz,_4);case 1:var _1OF=E(_1OA.b);if(!_1OF._){var _1OG=E(_1OC);if(!_1OG._){var _1OH=E(_1OF.a),_1OI=E(_1OG.a);switch(B(_12T(_1OH.a,_1OH.b,_1OH.c,_1OI.a,_1OI.b,_1OI.c))){case 0:return new T3(0,new T4(0,1,E(_1OA),E(_ML),E(_ML)),_1Oz,_4);case 1:return (B(_1bD(_1Gx,_1OF.b,_1OG.b))==0)?new T3(0,new T4(0,1,E(_1OA),E(_ML),E(_ML)),_1Oz,_4):new T3(0,new T4(0,1,E(_1OA),E(_ML),E(_ML)),_4,_1Oz);default:return new T3(0,new T4(0,1,E(_1OA),E(_ML),E(_ML)),_4,_1Oz);}}else{return new T3(0,new T4(0,1,E(_1OA),E(_ML),E(_ML)),_1Oz,_4);}}else{var _1OJ=E(_1OC);return new T3(0,new T4(0,1,E(_1OA),E(_ML),E(_ML)),_4,_1Oz);}break;default:return new T3(0,new T4(0,1,E(_1OA),E(_ML),E(_ML)),_4,_1Oz);}}}else{var _1OK=B(_1Ot(_1Oy>>1,_1Ow)),_1OL=_1OK.a,_1OM=_1OK.c,_1ON=E(_1OK.b);if(!_1ON._){return new T3(0,_1OL,_4,_1OM);}else{var _1OO=_1ON.a,_1OP=E(_1ON.b);if(!_1OP._){return new T3(0,new T(function(){return B(_O8(_1OO,_1OL));}),_4,_1OM);}else{var _1OQ=E(_1OO),_1OR=E(_1OP.a),_1OS=_1OR.b,_1OT=E(_1OQ.a),_1OU=E(_1OR.a);switch(B(_12T(_1OT.a,_1OT.b,_1OT.c,_1OU.a,_1OU.b,_1OU.c))){case 0:var _1OV=B(_1Ot(_1Oy>>1,_1OP));return new T3(0,new T(function(){return B(_OM(_1OQ,_1OL,_1OV.a));}),_1OV.b,_1OV.c);case 1:var _1OW=E(_1OQ.b);if(!_1OW._){var _1OX=E(_1OS);if(!_1OX._){var _1OY=E(_1OW.a),_1OZ=E(_1OX.a);switch(B(_12T(_1OY.a,_1OY.b,_1OY.c,_1OZ.a,_1OZ.b,_1OZ.c))){case 0:var _1P0=B(_1Ot(_1Oy>>1,_1OP));return new T3(0,new T(function(){return B(_OM(_1OQ,_1OL,_1P0.a));}),_1P0.b,_1P0.c);case 1:if(!B(_1bD(_1Gx,_1OW.b,_1OX.b))){var _1P1=B(_1Ot(_1Oy>>1,_1OP));return new T3(0,new T(function(){return B(_OM(_1OQ,_1OL,_1P1.a));}),_1P1.b,_1P1.c);}else{return new T3(0,_1OL,_4,_1ON);}break;default:return new T3(0,_1OL,_4,_1ON);}}else{var _1P2=B(_1Ot(_1Oy>>1,_1OP));return new T3(0,new T(function(){return B(_OM(_1OQ,_1OL,_1P2.a));}),_1P2.b,_1P2.c);}}else{var _1P3=E(_1OS);return new T3(0,_1OL,_4,_1ON);}break;default:return new T3(0,_1OL,_4,_1ON);}}}}}},_1P4=function(_1P5,_1P6,_1P7){var _1P8=E(_1P7);if(!_1P8._){return E(_1P6);}else{var _1P9=_1P8.a,_1Pa=E(_1P8.b);if(!_1Pa._){return new F(function(){return _O8(_1P9,_1P6);});}else{var _1Pb=E(_1P9),_1Pc=E(_1Pa.a),_1Pd=_1Pc.b,_1Pe=E(_1Pb.a),_1Pf=E(_1Pc.a),_1Pg=function(_1Ph){var _1Pi=B(_1Ot(_1P5,_1Pa)),_1Pj=_1Pi.a,_1Pk=E(_1Pi.c);if(!_1Pk._){return new F(function(){return _1P4(_1P5<<1,B(_OM(_1Pb,_1P6,_1Pj)),_1Pi.b);});}else{return new F(function(){return _1On(B(_OM(_1Pb,_1P6,_1Pj)),_1Pk);});}};switch(B(_12T(_1Pe.a,_1Pe.b,_1Pe.c,_1Pf.a,_1Pf.b,_1Pf.c))){case 0:return new F(function(){return _1Pg(_);});break;case 1:var _1Pl=E(_1Pb.b);if(!_1Pl._){var _1Pm=E(_1Pd);if(!_1Pm._){var _1Pn=E(_1Pl.a),_1Po=E(_1Pm.a);switch(B(_12T(_1Pn.a,_1Pn.b,_1Pn.c,_1Po.a,_1Po.b,_1Po.c))){case 0:return new F(function(){return _1Pg(_);});break;case 1:if(!B(_1bD(_1Gx,_1Pl.b,_1Pm.b))){return new F(function(){return _1Pg(_);});}else{return new F(function(){return _1On(_1P6,_1P8);});}break;default:return new F(function(){return _1On(_1P6,_1P8);});}}else{return new F(function(){return _1Pg(_);});}}else{var _1Pp=E(_1Pd);return new F(function(){return _1On(_1P6,_1P8);});}break;default:return new F(function(){return _1On(_1P6,_1P8);});}}}},_1Pq=function(_1Pr){var _1Ps=E(_1Pr);if(!_1Ps._){return new T0(1);}else{var _1Pt=_1Ps.a,_1Pu=E(_1Ps.b);if(!_1Pu._){return new T4(0,1,E(_1Pt),E(_ML),E(_ML));}else{var _1Pv=E(_1Pt),_1Pw=E(_1Pu.a),_1Px=_1Pw.b,_1Py=E(_1Pv.a),_1Pz=E(_1Pw.a);switch(B(_12T(_1Py.a,_1Py.b,_1Py.c,_1Pz.a,_1Pz.b,_1Pz.c))){case 0:return new F(function(){return _1P4(1,new T4(0,1,E(_1Pv),E(_ML),E(_ML)),_1Pu);});break;case 1:var _1PA=E(_1Pv.b);if(!_1PA._){var _1PB=E(_1Px);if(!_1PB._){var _1PC=E(_1PA.a),_1PD=E(_1PB.a);switch(B(_12T(_1PC.a,_1PC.b,_1PC.c,_1PD.a,_1PD.b,_1PD.c))){case 0:return new F(function(){return _1P4(1,new T4(0,1,E(_1Pv),E(_ML),E(_ML)),_1Pu);});break;case 1:if(!B(_1bD(_1Gx,_1PA.b,_1PB.b))){return new F(function(){return _1P4(1,new T4(0,1,E(_1Pv),E(_ML),E(_ML)),_1Pu);});}else{return new F(function(){return _1On(new T4(0,1,E(_1Pv),E(_ML),E(_ML)),_1Pu);});}break;default:return new F(function(){return _1On(new T4(0,1,E(_1Pv),E(_ML),E(_ML)),_1Pu);});}}else{return new F(function(){return _1P4(1,new T4(0,1,E(_1Pv),E(_ML),E(_ML)),_1Pu);});}}else{var _1PE=E(_1Px);return new F(function(){return _1On(new T4(0,1,E(_1Pv),E(_ML),E(_ML)),_1Pu);});}break;default:return new F(function(){return _1On(new T4(0,1,E(_1Pv),E(_ML),E(_ML)),_1Pu);});}}}},_1PF=new T(function(){return B(_7f("Muste/Grammar/Internal.hs:151:43-81|lambda"));}),_1PG=function(_1PH,_1PI){var _1PJ=new T(function(){return E(E(_1PH).b);}),_1PK=function(_1PL){var _1PM=E(_1PL);if(!_1PM._){return __Z;}else{var _1PN=new T(function(){return B(_1PK(_1PM.b));}),_1PO=function(_1PP){while(1){var _1PQ=B((function(_1PR){var _1PS=E(_1PR);if(!_1PS._){return E(_1PN);}else{var _1PT=_1PS.b,_1PU=E(_1PS.a),_1PV=E(_1PU.b);if(!_1PV._){var _1PW=E(_1PV.a),_1PX=E(_1PM.a);if(!B(_12M(_1PW.a,_1PW.b,_1PW.c,_1PX.a,_1PX.b,_1PX.c))){_1PP=_1PT;return __continue;}else{return new T2(1,_1PU,new T(function(){return B(_1PO(_1PT));}));}}else{return E(_1PF);}}})(_1PP));if(_1PQ!=__continue){return _1PQ;}}};return new F(function(){return _1PO(_1PJ);});}};return new F(function(){return _1Pq(B(_1PK(_1PI)));});},_1PY=function(_1PZ,_1Q0,_1Q1,_1Q2){var _1Q3=function(_1Q4,_1Q5){while(1){var _1Q6=B((function(_1Q7,_1Q8){var _1Q9=E(_1Q8);if(!_1Q9._){_1Q4=new T2(1,new T(function(){return B(_1Nv(_1Q0,_1Q1,_1Q2,_1Q9.b));}),new T(function(){return B(_1Q3(_1Q7,_1Q9.d));}));_1Q5=_1Q9.c;return __continue;}else{return E(_1Q7);}})(_1Q4,_1Q5));if(_1Q6!=__continue){return _1Q6;}}};return new F(function(){return _1Kn(_ML,B(_1ni(_4,B(_1Ki(B(_1Q3(_4,B(_1PG(_1PZ,B(_1ni(_4,B(_1Oa(_1Q0)))))))))))));});},_1Qa=function(_1Qb,_1Qc,_1Qd){var _1Qe=E(_1Qc);return new F(function(){return _1PY(_1Qb,_1Qe.a,_1Qe.b,_1Qd);});},_1Qf=function(_1Qg,_1Qh){while(1){var _1Qi=B((function(_1Qj,_1Qk){var _1Ql=E(_1Qk);if(!_1Ql._){return __Z;}else{var _1Qm=_1Ql.a,_1Qn=_1Ql.b;if(!B(A1(_1Qj,_1Qm))){var _1Qo=_1Qj;_1Qg=_1Qo;_1Qh=_1Qn;return __continue;}else{return new T2(1,_1Qm,new T(function(){return B(_1Qf(_1Qj,_1Qn));}));}}})(_1Qg,_1Qh));if(_1Qi!=__continue){return _1Qi;}}},_1Qp=function(_1Qq,_1Qr,_1Qs){var _1Qt=new T(function(){return E(_1Qs)-1|0;}),_1Qu=function(_1Qv){return B(_uU(E(_1Qv).a,0))<=E(_1Qt);},_1Qw=function(_1Qx,_1Qy){while(1){var _1Qz=B((function(_1QA,_1QB){var _1QC=E(_1QB);if(!_1QC._){var _1QD=_1QC.d,_1QE=E(_1QC.b),_1QF=new T(function(){if(!B(_1Qf(_1Qu,B(_1Ml(_1QE.a,_4))))._){return B(_1Qw(_1QA,_1QD));}else{return new T2(1,_1QE,new T(function(){return B(_1Qw(_1QA,_1QD));}));}},1);_1Qx=_1QF;_1Qy=_1QC.c;return __continue;}else{return E(_1QA);}})(_1Qx,_1Qy));if(_1Qz!=__continue){return _1Qz;}}},_1QG=function(_1QH){var _1QI=E(_1QH);if(!_1QI._){return new T0(1);}else{var _1QJ=_1QI.a,_1QK=B(_1Qa(_1Qq,_1QJ,_1Qs)),_1QL=B(_1QG(B(_0(_1QI.b,new T(function(){var _1QM=E(_1QJ);return B(_1Qw(_4,B(_1Jx(_1QM.a,_1QM.b,_1QK))));},1))))),_1QN=function(_1QO,_1QP,_1QQ,_1QR){return new F(function(){return _1jx(_1Jw,_1il,_1il,1,_1QJ,_ML,_ML,_1QO,_1QP,_1QQ,_1QR);});},_1QS=E(_1QK);if(!_1QS._){var _1QT=_1QS.a,_1QU=_1QS.b,_1QV=_1QS.c,_1QW=_1QS.d,_1QX=E(_1QL);if(!_1QX._){var _1QY=B(_1jx(_1Jw,_1il,_1il,_1QT,_1QU,_1QV,_1QW,_1QX.a,_1QX.b,_1QX.c,_1QX.d));if(!_1QY._){return new F(function(){return _1QN(_1QY.a,_1QY.b,_1QY.c,_1QY.d);});}else{return new T4(0,1,E(_1QJ),E(_ML),E(_ML));}}else{return new F(function(){return _1QN(_1QT,_1QU,_1QV,_1QW);});}}else{var _1QZ=E(_1QL);if(!_1QZ._){return new F(function(){return _1QN(_1QZ.a,_1QZ.b,_1QZ.c,_1QZ.d);});}else{return new T4(0,1,E(_1QJ),E(_ML),E(_ML));}}}};return new F(function(){return _1QG(new T2(1,new T2(0,new T1(1,_1Qr),new T4(0,1,E(new T2(0,_4,new T1(1,_1Qr))),E(_ML),E(_ML))),_4));});},_1R0=function(_1R1){return E(E(_1R1).a);},_1R2=function(_1R3,_1R4,_1R5,_1R6){var _1R7=new T(function(){var _1R8=B(_1EO(new T(function(){return B(_1R0(_1R4));}),_1R5));if(!_1R8._){return E(_1F1);}else{var _1R9=E(_1R8.a);if(!_1R9._){var _1Ra=E(_1R9.b);if(!_1Ra._){return E(_1Ra.a);}else{return E(_1Cg);}}else{return E(_1R9.a);}}});return new F(function(){return _1Qp(_1R3,_1R7,_1R6);});},_1Rb=function(_1Rc,_1Rd,_1Re,_1Rf){while(1){var _1Rg=E(_1Rd);if(!_1Rg._){return E(_1Rf);}else{var _1Rh=_1Rg.a,_1Ri=E(_1Re);if(!_1Ri._){return E(_1Rf);}else{if(!B(A3(_pM,_1Rc,_1Rh,_1Ri.a))){return E(_1Rf);}else{var _1Rj=new T2(1,_1Rh,_1Rf);_1Rd=_1Rg.b;_1Re=_1Ri.b;_1Rf=_1Rj;continue;}}}}},_1Rk=function(_1Rl,_1Rm){while(1){var _1Rn=E(_1Rl);if(!_1Rn._){return E(_1Rm);}else{var _1Ro=new T2(1,_1Rn.a,_1Rm);_1Rl=_1Rn.b;_1Rm=_1Ro;continue;}}},_1Rp=function(_1Rq,_1Rr,_1Rs,_1Rt,_1Ru){while(1){var _1Rv=B((function(_1Rw,_1Rx,_1Ry,_1Rz,_1RA){var _1RB=E(_1Rx);if(!_1RB._){return new T2(0,_1Rz,_1RA);}else{var _1RC=_1RB.a,_1RD=_1RB.b,_1RE=E(_1Ry);if(!_1RE._){return new T2(0,_1Rz,_1RA);}else{var _1RF=_1RE.b;if(!B(A3(_pM,_1Rw,_1RC,_1RE.a))){var _1RG=new T(function(){return B(_1Rb(_1Rw,B(_1Rk(_1RB,_4)),new T(function(){return B(_1Rk(_1RE,_4));},1),_4));}),_1RH=_1Rw,_1RI=_1Rz;_1Rq=_1RH;_1Rr=_1RD;_1Rs=_1RF;_1Rt=_1RI;_1Ru=_1RG;return __continue;}else{var _1RH=_1Rw,_1RJ=_1RA;_1Rq=_1RH;_1Rr=_1RD;_1Rs=_1RF;_1Rt=new T(function(){return B(_0(_1Rz,new T2(1,_1RC,_4)));});_1Ru=_1RJ;return __continue;}}}})(_1Rq,_1Rr,_1Rs,_1Rt,_1Ru));if(_1Rv!=__continue){return _1Rv;}}},_1RK=function(_1RL,_1RM,_1RN,_1RO){return (!B(_1Fq(_1RL,_1RN)))?true:(!B(_sf(_1RM,_1RO)))?true:false;},_1RP=function(_1RQ,_1RR){var _1RS=E(_1RQ),_1RT=E(_1RR);return new F(function(){return _1RK(_1RS.a,_1RS.b,_1RT.a,_1RT.b);});},_1RU=function(_1RV,_1RW,_1RX,_1RY){if(!B(_1Fq(_1RV,_1RX))){return false;}else{return new F(function(){return _sf(_1RW,_1RY);});}},_1RZ=function(_1S0,_1S1){var _1S2=E(_1S0),_1S3=E(_1S1);return new F(function(){return _1RU(_1S2.a,_1S2.b,_1S3.a,_1S3.b);});},_1S4=new T2(0,_1RZ,_1RP),_1S5=function(_1S6,_1S7,_1S8,_1S9){switch(B(_1Hq(_1S6,_1S8))){case 0:return false;case 1:return new F(function(){return _12t(_1S7,_1S9);});break;default:return true;}},_1Sa=function(_1Sb,_1Sc){var _1Sd=E(_1Sb),_1Se=E(_1Sc);return new F(function(){return _1S5(_1Sd.a,_1Sd.b,_1Se.a,_1Se.b);});},_1Sf=function(_1Sg,_1Sh){var _1Si=E(_1Sg),_1Sj=E(_1Sh);switch(B(_1Hq(_1Si.a,_1Sj.a))){case 0:return E(_1Sj);case 1:return (B(_12d(_1Si.b,_1Sj.b))==2)?E(_1Si):E(_1Sj);default:return E(_1Si);}},_1Sk=function(_1Sl,_1Sm){var _1Sn=E(_1Sl),_1So=E(_1Sm);switch(B(_1Hq(_1Sn.a,_1So.a))){case 0:return E(_1Sn);case 1:return (B(_12d(_1Sn.b,_1So.b))==2)?E(_1So):E(_1Sn);default:return E(_1So);}},_1Sp=function(_1Sq,_1Sr,_1Ss,_1St){switch(B(_1Hq(_1Sq,_1Ss))){case 0:return 0;case 1:return new F(function(){return _12d(_1Sr,_1St);});break;default:return 2;}},_1Su=function(_1Sv,_1Sw){var _1Sx=E(_1Sv),_1Sy=E(_1Sw);return new F(function(){return _1Sp(_1Sx.a,_1Sx.b,_1Sy.a,_1Sy.b);});},_1Sz=function(_1SA,_1SB,_1SC,_1SD){switch(B(_1Hq(_1SA,_1SC))){case 0:return true;case 1:return new F(function(){return _12k(_1SB,_1SD);});break;default:return false;}},_1SE=function(_1SF,_1SG){var _1SH=E(_1SF),_1SI=E(_1SG);return new F(function(){return _1Sz(_1SH.a,_1SH.b,_1SI.a,_1SI.b);});},_1SJ=function(_1SK,_1SL,_1SM,_1SN){switch(B(_1Hq(_1SK,_1SM))){case 0:return true;case 1:return new F(function(){return _12n(_1SL,_1SN);});break;default:return false;}},_1SO=function(_1SP,_1SQ){var _1SR=E(_1SP),_1SS=E(_1SQ);return new F(function(){return _1SJ(_1SR.a,_1SR.b,_1SS.a,_1SS.b);});},_1ST=function(_1SU,_1SV,_1SW,_1SX){switch(B(_1Hq(_1SU,_1SW))){case 0:return false;case 1:return new F(function(){return _12q(_1SV,_1SX);});break;default:return true;}},_1SY=function(_1SZ,_1T0){var _1T1=E(_1SZ),_1T2=E(_1T0);return new F(function(){return _1ST(_1T1.a,_1T1.b,_1T2.a,_1T2.b);});},_1T3={_:0,a:_1S4,b:_1Su,c:_1SE,d:_1SO,e:_1SY,f:_1Sa,g:_1Sf,h:_1Sk},_1T4=function(_1T5){var _1T6=E(_1T5);if(!_1T6._){return __Z;}else{return new F(function(){return _0(_1T6.a,new T(function(){return B(_1T4(_1T6.b));},1));});}},_1T7=new T1(1,_4),_1T8=function(_1T9){var _1Ta=E(_1T9);if(!_1Ta._){return E(_1T7);}else{var _1Tb=E(_1Ta.a);if(!_1Tb._){return __Z;}else{var _1Tc=B(_1T8(_1Ta.b));return (_1Tc._==0)?__Z:new T1(1,new T2(1,_1Tb.a,_1Tc.a));}}},_1Td=function(_1Te,_1Tf){var _1Tg=B(_1T8(_1Tf));return (_1Tg._==0)?new T2(0,_4l,_4l):new T2(0,_1Te,new T1(1,new T(function(){return B(_1T4(_1Tg.a));})));},_1Th=function(_1Ti,_1Tj){var _1Tk=E(_1Ti);if(!_1Tk._){return new T2(0,_1Tj,_4);}else{var _1Tl=new T(function(){var _1Tm=B(_1Th(_1Tk.b,_1Tj));return new T2(0,_1Tm.a,_1Tm.b);}),_1Tn=new T(function(){var _1To=B(_1Tp(new T(function(){return E(E(_1Tl).a);}),_1Tk.a));return new T2(0,_1To.a,_1To.b);});return new T2(0,new T(function(){return E(E(_1Tn).a);}),new T2(1,new T(function(){return E(E(_1Tn).b);}),new T(function(){return E(E(_1Tl).b);})));}},_1Tq=function(_1Tr,_1Ts){var _1Tt=E(_1Tr);if(!_1Tt._){return new T2(0,_1Ts,_4);}else{var _1Tu=new T(function(){var _1Tv=B(_1Tq(_1Tt.b,_1Ts));return new T2(0,_1Tv.a,_1Tv.b);}),_1Tw=new T(function(){var _1Tx=B(_1Tp(new T(function(){return E(E(_1Tu).a);}),_1Tt.a));return new T2(0,_1Tx.a,_1Tx.b);});return new T2(0,new T(function(){return E(E(_1Tw).a);}),new T2(1,new T(function(){return E(E(_1Tw).b);}),new T(function(){return E(E(_1Tu).b);})));}},_1Ty=function(_1Tz,_1TA){var _1TB=E(_1Tz);if(!_1TB._){return new T2(0,_1TA,_4);}else{var _1TC=new T(function(){var _1TD=B(_1Ty(_1TB.b,_1TA));return new T2(0,_1TD.a,_1TD.b);}),_1TE=new T(function(){var _1TF=B(_1Tp(new T(function(){return E(E(_1TC).a);}),_1TB.a));return new T2(0,_1TF.a,_1TF.b);});return new T2(0,new T(function(){return E(E(_1TE).a);}),new T2(1,new T(function(){return E(E(_1TE).b);}),new T(function(){return E(E(_1TC).b);})));}},_1TG=function(_1TH,_1TI){var _1TJ=E(_1TH);if(!_1TJ._){return new T2(0,_1TI,_4);}else{var _1TK=new T(function(){var _1TL=B(_1TG(_1TJ.b,_1TI));return new T2(0,_1TL.a,_1TL.b);}),_1TM=new T(function(){var _1TN=B(_1Tp(new T(function(){return E(E(_1TK).a);}),_1TJ.a));return new T2(0,_1TN.a,_1TN.b);});return new T2(0,new T(function(){return E(E(_1TM).a);}),new T2(1,new T(function(){return E(E(_1TM).b);}),new T(function(){return E(E(_1TK).b);})));}},_1TO=function(_1TP){var _1TQ=E(_1TP);if(!_1TQ._){return __Z;}else{return new F(function(){return _0(_1TQ.a,new T(function(){return B(_1TO(_1TQ.b));},1));});}},_1TR=function(_1TS){var _1TT=E(_1TS);if(!_1TT._){return E(_1T7);}else{var _1TU=E(_1TT.a);if(!_1TU._){return __Z;}else{var _1TV=B(_1TR(_1TT.b));return (_1TV._==0)?__Z:new T1(1,new T2(1,_1TU.a,_1TV.a));}}},_1TW=function(_1TX,_1TY,_1TZ){while(1){var _1U0=E(_1TY);if(!_1U0._){return true;}else{var _1U1=E(_1TZ);if(!_1U1._){return false;}else{if(!B(A3(_pM,_1TX,_1U0.a,_1U1.a))){return false;}else{_1TY=_1U0.b;_1TZ=_1U1.b;continue;}}}}},_1U2=new T1(1,_4),_1U3=new T(function(){return B(_7f("pgf/PGF/Macros.hs:(186,5)-(204,44)|function untokn"));}),_1Tp=function(_1U4,_1U5){var _1U6=E(_1U5);switch(_1U6._){case 0:var _1U7=B(_1TG(_1U6.f,_1U4)),_1U8=B(_1TR(_1U7.b));return (_1U8._==0)?new T2(0,_4l,_4l):new T2(0,_1U7.a,new T1(1,new T2(1,new T6(1,_1U6.a,_1U6.b,_1U6.c,_1U6.d,_1U6.e,new T(function(){return B(_1TO(_1U8.a));})),_4)));case 1:var _1U9=E(_1U6.a);return (_1U9._==0)?new T2(0,_1U4,_1U2):new T2(0,new T1(1,_1U9),new T1(1,new T2(1,new T1(0,_1U9),_4)));case 2:return new T2(0,_4l,_4l);case 6:var _1Ua=_1U6.a,_1Ub=E(_1U4);if(!_1Ub._){var _1Uc=B(_1Ty(_1Ua,_4l));return new F(function(){return _1Td(_1Uc.a,_1Uc.b);});}else{var _1Ud=function(_1Ue){while(1){var _1Uf=E(_1Ue);if(!_1Uf._){return false;}else{if(!B(_1TW(_sq,_1Uf.a,_1Ub.a))){_1Ue=_1Uf.b;continue;}else{return true;}}}},_1Ug=function(_1Uh){while(1){var _1Ui=B((function(_1Uj){var _1Uk=E(_1Uj);if(!_1Uk._){return __Z;}else{var _1Ul=_1Uk.b,_1Um=E(_1Uk.a);if(!B(_1Ud(_1Um.b))){_1Uh=_1Ul;return __continue;}else{return new T2(1,_1Um.a,new T(function(){return B(_1Ug(_1Ul));}));}}})(_1Uh));if(_1Ui!=__continue){return _1Ui;}}},_1Un=B(_1Ug(_1U6.b));if(!_1Un._){var _1Uo=B(_1Tq(_1Ua,_1Ub));return new F(function(){return _1Td(_1Uo.a,_1Uo.b);});}else{var _1Up=B(_1Th(_1Un.a,_1Ub));return new F(function(){return _1Td(_1Up.a,_1Up.b);});}}break;default:return E(_1U3);}},_1Uq=function(_1Ur,_1Us){var _1Ut=E(_1Ur);if(!_1Ut._){return new T2(0,_1Us,_4);}else{var _1Uu=new T(function(){var _1Uv=B(_1Uq(_1Ut.b,_1Us));return new T2(0,_1Uv.a,_1Uv.b);}),_1Uw=new T(function(){var _1Ux=B(_1Tp(new T(function(){return E(E(_1Uu).a);}),_1Ut.a));return new T2(0,_1Ux.a,_1Ux.b);});return new T2(0,new T(function(){return E(E(_1Uw).a);}),new T2(1,new T(function(){return E(E(_1Uw).b);}),new T(function(){return E(E(_1Uu).b);})));}},_1Uy=function(_1Uz){var _1UA=E(_1Uz);if(_1UA==95){return true;}else{var _1UB=function(_1UC){if(_1UA<65){if(_1UA<192){return false;}else{if(_1UA>255){return false;}else{switch(E(_1UA)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1UA>90){if(_1UA<192){return false;}else{if(_1UA>255){return false;}else{switch(E(_1UA)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1UA<97){return new F(function(){return _1UB(_);});}else{if(_1UA>122){return new F(function(){return _1UB(_);});}else{return true;}}}},_1UD=new T(function(){return B(unCStr("UTF8.decodeUTF8: bad data"));}),_1UE=function(_1UF){return new F(function(){return err(_1UD);});},_1UG=new T(function(){return B(_1UE(_));}),_1UH=function(_1UI){var _1UJ=E(_1UI);if(!_1UJ._){return __Z;}else{var _1UK=_1UJ.b,_1UL=E(_1UJ.a);if(_1UL>=128){var _1UM=E(_1UK);if(!_1UM._){return E(_1UG);}else{var _1UN=_1UM.a,_1UO=_1UM.b,_1UP=function(_1UQ){var _1UR=E(_1UO);if(!_1UR._){return E(_1UG);}else{if(224>_1UL){return E(_1UG);}else{if(_1UL>239){return E(_1UG);}else{var _1US=E(_1UN);if(128>_1US){return E(_1UG);}else{if(_1US>191){return E(_1UG);}else{var _1UT=E(_1UR.a);return (128>_1UT)?E(_1UG):(_1UT>191)?E(_1UG):new T2(1,new T(function(){var _1UU=((imul(B(_o6(_1UL,16)),4096)|0)+(imul(B(_o6(_1US,64)),64)|0)|0)+B(_o6(_1UT,64))|0;if(_1UU>>>0>1114111){return B(_fK(_1UU));}else{return _1UU;}}),new T(function(){return B(_1UH(_1UR.b));}));}}}}}};if(192>_1UL){return new F(function(){return _1UP(_);});}else{if(_1UL>223){return new F(function(){return _1UP(_);});}else{var _1UV=E(_1UN);if(128>_1UV){return new F(function(){return _1UP(_);});}else{if(_1UV>191){return new F(function(){return _1UP(_);});}else{return new T2(1,new T(function(){var _1UW=(imul(B(_o6(_1UL,32)),64)|0)+B(_o6(_1UV,64))|0;if(_1UW>>>0>1114111){return B(_fK(_1UW));}else{return _1UW;}}),new T(function(){return B(_1UH(_1UO));}));}}}}}}else{return new T2(1,_1UL,new T(function(){return B(_1UH(_1UK));}));}}},_1UX=function(_1UY){var _1UZ=E(_1UY);switch(_1UZ){case 39:return true;case 95:return true;default:var _1V0=function(_1V1){var _1V2=function(_1V3){if(_1UZ<65){if(_1UZ<192){return false;}else{if(_1UZ>255){return false;}else{switch(E(_1UZ)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1UZ>90){if(_1UZ<192){return false;}else{if(_1UZ>255){return false;}else{switch(E(_1UZ)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1UZ<97){return new F(function(){return _1V2(_);});}else{if(_1UZ>122){return new F(function(){return _1V2(_);});}else{return true;}}};if(_1UZ<48){return new F(function(){return _1V0(_);});}else{if(_1UZ>57){return new F(function(){return _1V0(_);});}else{return true;}}}},_1V4=function(_1V5){while(1){var _1V6=E(_1V5);if(!_1V6._){return true;}else{if(!B(_1UX(E(_1V6.a)))){return false;}else{_1V5=_1V6.b;continue;}}}},_1V7=new T(function(){return B(unCStr("\\\\"));}),_1V8=new T(function(){return B(unCStr("\\\'"));}),_1V9=new T(function(){return B(unCStr("\'"));}),_1Va=function(_1Vb){var _1Vc=E(_1Vb);if(!_1Vc._){return E(_1V9);}else{var _1Vd=_1Vc.b,_1Ve=E(_1Vc.a);switch(E(_1Ve)){case 39:return new F(function(){return _0(_1V8,new T(function(){return B(_1Va(_1Vd));},1));});break;case 92:return new F(function(){return _0(_1V7,new T(function(){return B(_1Va(_1Vd));},1));});break;default:return new T2(1,_1Ve,new T(function(){return B(_1Va(_1Vd));}));}}},_1Vf=function(_1Vg){var _1Vh=E(_1Vg);return (_1Vh._==0)?__Z:new T2(1,new T(function(){return B(_12D(_1Vh.a));}),new T(function(){return B(_1Vf(_1Vh.b));}));},_1Vi=function(_1Vj,_1Vk,_1Vl){var _1Vm=B(_1UH(B(_1Vf(new T(function(){return B(_IJ(_1Vj,_1Vk,_1Vl));})))));if(!_1Vm._){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1Va(_4));}));});}else{if(!B(_1Uy(E(_1Vm.a)))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1Va(_1Vm));}));});}else{if(!B(_1V4(_1Vm.b))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1Va(_1Vm));}));});}else{return E(_1Vm);}}}},_1Vn=new T(function(){return B(unCStr(")"));}),_1Vo=function(_1Vp,_1Vq){var _1Vr=new T(function(){var _1Vs=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_1Vq,_4)),_1Vn));})));},1);return B(_0(B(_bZ(0,_1Vp,_4)),_1Vs));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1Vr)));});},_1Vt=new T(function(){return B(unCStr("Int"));}),_1Vu=function(_1Vv,_1Vw,_1Vx){return new F(function(){return _eR(_e4,new T2(0,_1Vw,_1Vx),_1Vv,_1Vt);});},_1Vy=new T(function(){return B(unCStr("&|"));}),_1Vz=new T1(1,_1Vy),_1VA=new T2(1,_1Vz,_4),_1VB=new T0(2),_1VC=new T2(1,_1VB,_4),_1VD=new T(function(){return B(unCStr("&+"));}),_1VE=new T1(1,_1VD),_1VF=new T2(1,_1VE,_4),_1VG=function(_1VH,_1VI,_1VJ){var _1VK=function(_1VL,_1VM){var _1VN=B(_1EF(_1VJ,_1VL)),_1VO=E(_1VN.a),_1VP=E(E(_1VN.e).b),_1VQ=_1VP.c,_1VR=E(_1VP.a),_1VS=E(_1VP.b);if(_1VR>_1VM){return new F(function(){return _1Vu(_1VM,_1VR,_1VS);});}else{if(_1VM>_1VS){return new F(function(){return _1Vu(_1VM,_1VR,_1VS);});}else{var _1VT=_1VM-_1VR|0;if(0>_1VT){return new F(function(){return _1Vo(_1VT,_1VQ);});}else{if(_1VT>=_1VQ){return new F(function(){return _1Vo(_1VT,_1VQ);});}else{var _1VU=E(_1VP.d[_1VT]);return (_1VU._==0)?__Z:(!B(A1(_1VH,_1VO)))?E(_1VU):new T2(1,new T(function(){return new T6(0,_1VO.a,E(_1VO.b),_1VM,_1VN.c,_1VN.d,_1VU);}),_4);}}}}},_1VV=function(_1VW){var _1VX=E(_1VW);if(!_1VX._){return __Z;}else{var _1VY=E(_1VX.a);return new T2(1,new T2(0,new T(function(){return B(_1VZ(_1VY.a));}),_1VY.b),new T(function(){return B(_1VV(_1VX.b));}));}},_1W0=function(_1W1){var _1W2=E(_1W1);if(!_1W2._){return __Z;}else{return new F(function(){return _0(B(_1W3(_1W2.a)),new T(function(){return B(_1W0(_1W2.b));},1));});}},_1W3=function(_1W4){var _1W5=E(_1W4);switch(_1W5._){case 0:return new F(function(){return _1VK(_1W5.a,_1W5.b);});break;case 1:return new F(function(){return _1VK(_1W5.a,_1W5.b);});break;case 2:return new T2(1,new T1(1,new T(function(){var _1W6=B(_1EF(E(B(_1EF(_1VJ,_1W5.a)).e).a,_1W5.b));return B(_1Vi(_1W6.a,_1W6.b,_1W6.c));})),_4);case 3:return new T2(1,new T1(1,_1W5.a),_4);case 4:return new T2(1,new T2(6,new T(function(){return B(_1W0(_1W5.a));}),new T(function(){return B(_1VV(_1W5.b));})),_4);case 5:return E(_1VF);case 6:return E(_1VC);case 7:return __Z;case 8:return __Z;case 9:return E(_1VA);default:return E(_1VA);}},_1VZ=function(_1W7){var _1W8=E(_1W7);if(!_1W8._){return __Z;}else{return new F(function(){return _0(B(_1W3(_1W8.a)),new T(function(){return B(_1VZ(_1W8.b));},1));});}},_1W9=function(_1Wa){var _1Wb=E(_1Wa);if(!_1Wb._){return __Z;}else{return new F(function(){return _0(B(_1W3(_1Wb.a)),new T(function(){return B(_1W9(_1Wb.b));},1));});}};return new F(function(){return _1W9(_1VI);});},_1Wc=function(_1Wd,_1We,_1Wf){return new F(function(){return _eR(_e4,new T2(0,_1We,_1Wf),_1Wd,_1Vt);});},_1Wg=new T(function(){return B(unCStr("Negative range size"));}),_1Wh=function(_1Wi,_1Wj,_1Wk,_1Wl,_1Wm){var _1Wn=new T(function(){var _1Wo=function(_){var _1Wp=E(_1Wi),_1Wq=E(_1Wp.c),_1Wr=_1Wq.c,_1Ws=E(_1Wq.a),_1Wt=E(_1Wq.b),_1Wu=E(_1Wl);if(_1Ws>_1Wu){return new F(function(){return _1Wc(_1Wu,_1Ws,_1Wt);});}else{if(_1Wu>_1Wt){return new F(function(){return _1Wc(_1Wu,_1Ws,_1Wt);});}else{var _1Wv=_1Wu-_1Ws|0;if(0>_1Wv){return new F(function(){return _1Vo(_1Wv,_1Wr);});}else{if(_1Wv>=_1Wr){return new F(function(){return _1Vo(_1Wv,_1Wr);});}else{var _1Ww=E(_1Wq.d[_1Wv]),_1Wx=E(_1Ww.b),_1Wy=E(_1Ww.c),_1Wz=function(_1WA){if(_1WA>=0){var _1WB=newArr(_1WA,_Vu),_1WC=_1WB,_1WD=function(_1WE){var _1WF=function(_1WG,_1WH,_){while(1){if(_1WG!=_1WE){var _1WI=E(_1WH);if(!_1WI._){return _5;}else{var _=_1WC[_1WG]=_1WI.a,_1WJ=_1WG+1|0;_1WG=_1WJ;_1WH=_1WI.b;continue;}}else{return _5;}}},_1WK=new T(function(){var _1WL=_1Ww.d-1|0;if(0<=_1WL){var _1WM=new T(function(){return B(_1VG(_1Wj,_4,_1Wm));}),_1WN=function(_1WO){var _1WP=new T(function(){var _1WQ=E(_1Wp.f),_1WR=_1WQ.c,_1WS=E(_1WQ.a),_1WT=E(_1WQ.b),_1WU=_1Ww.e["v"]["i32"][_1WO];if(_1WS>_1WU){return B(_1Vu(_1WU,_1WS,_1WT));}else{if(_1WU>_1WT){return B(_1Vu(_1WU,_1WS,_1WT));}else{var _1WV=_1WU-_1WS|0;if(0>_1WV){return B(_1Vo(_1WV,_1WR));}else{if(_1WV>=_1WR){return B(_1Vo(_1WV,_1WR));}else{var _1WW=E(_1WQ.d[_1WV]),_1WX=_1WW.c-1|0;if(0<=_1WX){var _1WY=function(_1WZ){return new T2(1,new T(function(){return E(_1WW.d[_1WZ]);}),new T(function(){if(_1WZ!=_1WX){return B(_1WY(_1WZ+1|0));}else{return __Z;}}));};return B(_1VG(_1Wj,B(_1WY(0)),_1Wm));}else{return E(_1WM);}}}}}});return new T2(1,_1WP,new T(function(){if(_1WO!=_1WL){return B(_1WN(_1WO+1|0));}else{return __Z;}}));};return B(_1WN(0));}else{return __Z;}},1),_1X0=B(_1WF(0,_1WK,_));return new T4(0,E(_1Wx),E(_1Wy),_1WA,_1WC);};if(_1Wx>_1Wy){return new F(function(){return _1WD(0);});}else{var _1X1=(_1Wy-_1Wx|0)+1|0;if(_1X1>=0){return new F(function(){return _1WD(_1X1);});}else{return new F(function(){return err(_1Wg);});}}}else{return E(_Vw);}};if(_1Wx>_1Wy){return new F(function(){return _1Wz(0);});}else{return new F(function(){return _1Wz((_1Wy-_1Wx|0)+1|0);});}}}}}};return B(_8O(_1Wo));});return new T2(0,_1Wk,_1Wn);},_1X2=new T(function(){return B(unCStr(")"));}),_1X3=function(_1X4,_1X5){var _1X6=new T(function(){var _1X7=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_1X5,_4)),_1X2));})));},1);return B(_0(B(_bZ(0,_1X4,_4)),_1X7));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1X6)));});},_1X8=function(_1X9){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_1X9));}))));});},_1Xa=new T(function(){return B(_1X8("ww_sZJc Map CId String"));}),_1Xb=new T(function(){return B(_1X8("ww_sZJb Map CId Literal"));}),_1Xc=new T1(1,_4),_1Xd=new T2(1,_1Xc,_4),_1Xe=0,_1Xf=new T(function(){return B(unCStr("Int"));}),_1Xg=function(_1Xh,_1Xi){return new F(function(){return _eR(_e4,new T2(0,_1Xh,_1Xi),_1Xe,_1Xf);});},_1Xj=function(_1Xk){return true;},_1Xl=new T(function(){return B(_1X8("ww_sZJl IntMap (IntMap (TrieMap Token IntSet))"));}),_1Xm=new T(function(){return B(_1X8("ww_sZJk Map CId CncCat"));}),_1Xn=new T(function(){return B(_1X8("ww_sZJj Map CId (IntMap (Set Production))"));}),_1Xo=new T(function(){return B(_1X8("ww_sZJi IntMap (Set Production)"));}),_1Xp=new T(function(){return B(_1X8("ww_sZJh IntMap (Set Production)"));}),_1Xq=new T(function(){return B(_1X8("ww_sZJe IntMap [FunId]"));}),_1Xr=function(_1Xs,_1Xt,_1Xu,_1Xv,_1Xw,_1Xx,_1Xy,_1Xz){var _1XA=B(_14V(_1Xw,_1Xt));if(!_1XA._){return E(_1Xd);}else{var _1XB=E(_1XA.a);if(!_1XB._){return E(_1Xd);}else{var _1XC=E(B(_1Wh({_:0,a:_1Xb,b:_1Xa,c:_1Xs,d:_1Xq,e:_1Xt,f:_1Xu,g:_1Xp,h:_1Xo,i:_1Xn,j:_1Xm,k:_1Xl,l:0},_1Xj,_4,_1XB.a,new T2(1,new T5(0,E(_1Xv),_1Xw,_1Xx,_1Xy,E(_1Xz)),_4))).b),_1XD=_1XC.c,_1XE=E(_1XC.a),_1XF=E(_1XC.b);if(_1XE>0){return new F(function(){return _1Xg(_1XE,_1XF);});}else{if(0>_1XF){return new F(function(){return _1Xg(_1XE,_1XF);});}else{var _1XG= -_1XE|0;if(0>_1XG){return new F(function(){return _1X3(_1XG,_1XD);});}else{if(_1XG>=_1XD){return new F(function(){return _1X3(_1XG,_1XD);});}else{return E(_1XC.d[_1XG]);}}}}}}},_1XH=new T(function(){return B(unCStr("no lang"));}),_1XI=new T(function(){return B(err(_1XH));}),_1XJ=function(_1XK){return E(E(_1XK).d);},_1XL=function(_1XM,_1XN,_1XO,_1XP){var _1XQ=function(_1XR,_1XS,_1XT){while(1){var _1XU=E(_1XS),_1XV=E(_1XT);if(!_1XV._){switch(B(A3(_13n,_1XM,_1XU,_1XV.b))){case 0:_1XS=_1XU;_1XT=_1XV.d;continue;case 1:return E(_1XV.c);default:_1XS=_1XU;_1XT=_1XV.e;continue;}}else{return E(_1XR);}}};return new F(function(){return _1XQ(_1XN,_1XO,_1XP);});},_1XW=function(_1XX){var _1XY=function(_){var _1XZ=newArr(1,_Vu),_1Y0=_1XZ,_1Y1=function(_1Y2,_1Y3,_){while(1){var _1Y4=E(_1Y2);if(_1Y4==1){return _5;}else{var _1Y5=E(_1Y3);if(!_1Y5._){return _5;}else{var _=_1Y0[_1Y4]=_1Y5.a;_1Y2=_1Y4+1|0;_1Y3=_1Y5.b;continue;}}}},_1Y6=B(_1Y1(0,new T2(1,new T2(1,new T1(1,_1XX),_4),_4),_));return new T4(0,E(_1Xe),E(_1Xe),1,_1Y0);};return new F(function(){return _8O(_1XY);});},_1Y7=function(_1Y8,_1Y9,_1Ya,_1Yb){while(1){var _1Yc=E(_1Yb);if(!_1Yc._){var _1Yd=E(_1Yc.b);switch(B(_12T(_1Y8,_1Y9,_1Ya,_1Yd.a,_1Yd.b,_1Yd.c))){case 0:_1Yb=_1Yc.d;continue;case 1:return new T1(1,_1Yc.c);default:_1Yb=_1Yc.e;continue;}}else{return __Z;}}},_1Ye=new T(function(){return B(unCStr("Float"));}),_1Yf=new T(function(){return B(_1za(_1Ye));}),_1Yg=new T(function(){return B(_G(_1z8,_1Yf));}),_1Yh=new T(function(){var _1Yi=B(_1xU(_1Yg));return new T3(0,_1Yi.a,_1Yi.b,_1Yi.c);}),_1Yj=new T(function(){return B(_1za(_1Vt));}),_1Yk=new T(function(){return B(_G(_1z8,_1Yj));}),_1Yl=new T(function(){var _1Ym=B(_1xU(_1Yk));return new T3(0,_1Ym.a,_1Ym.b,_1Ym.c);}),_1Yn=new T(function(){return B(unCStr("String"));}),_1Yo=new T(function(){return B(_1za(_1Yn));}),_1Yp=new T(function(){return B(_G(_1z8,_1Yo));}),_1Yq=new T(function(){var _1Yr=B(_1xU(_1Yp));return new T3(0,_1Yr.a,_1Yr.b,_1Yr.c);}),_1Ys=function(_1Yt){var _1Yu=E(_1Yt);return (_1Yu._==0)?__Z:new T2(1,E(_1Yu.a).b,new T(function(){return B(_1Ys(_1Yu.b));}));},_1Yv=function(_1Yw){var _1Yx=E(_1Yw);return (_1Yx._==0)?__Z:new T2(1,new T(function(){return E(E(E(_1Yx.a).c).b);}),new T(function(){return B(_1Yv(_1Yx.b));}));},_1Yy=new T(function(){return B(_7f("pgf/PGF/Linearize.hs:(77,5)-(87,137)|function lin"));}),_1Yz=63,_1YA=new T(function(){return B(_1MF("pgf/PGF/Linearize.hs:105:19-70|Just (ty, _, _, _)"));}),_1YB=new T(function(){return B(_7f("pgf/PGF/Linearize.hs:(104,13)-(109,85)|function toApp"));}),_1YC=new T(function(){return B(unCStr("]"));}),_1YD=function(_1YE,_1YF,_1YG,_1YH){if(!B(_18O(_1YI,_1YE,_1YG))){return false;}else{return new F(function(){return _1aJ(_1YF,_1YH);});}},_1YJ=function(_1YK,_1YL){var _1YM=E(_1YK),_1YN=E(_1YL);return new F(function(){return _1YD(_1YM.a,_1YM.b,_1YN.a,_1YN.b);});},_1YO=function(_1YP,_1YQ,_1YR,_1YS){return (!B(_18O(_1YI,_1YP,_1YR)))?true:(!B(_1aJ(_1YQ,_1YS)))?true:false;},_1YT=function(_1YU,_1YV){var _1YW=E(_1YU),_1YX=E(_1YV);return new F(function(){return _1YO(_1YW.a,_1YW.b,_1YX.a,_1YX.b);});},_1YY=new T(function(){return new T2(0,_1YJ,_1YT);}),_1YZ=function(_1Z0,_1Z1){var _1Z2=E(_1Z0);switch(_1Z2._){case 0:var _1Z3=E(_1Z1);if(!_1Z3._){var _1Z4=E(_1Z2.a),_1Z5=E(_1Z3.a);if(!B(_12M(_1Z4.a,_1Z4.b,_1Z4.c,_1Z5.a,_1Z5.b,_1Z5.c))){return false;}else{if(_1Z2.b!=_1Z3.b){return false;}else{if(_1Z2.c!=_1Z3.c){return false;}else{var _1Z6=E(_1Z2.d),_1Z7=E(_1Z3.d);if(!B(_12M(_1Z6.a,_1Z6.b,_1Z6.c,_1Z7.a,_1Z7.b,_1Z7.c))){return false;}else{if(!B(_18O(_18Y,_1Z2.e,_1Z3.e))){return false;}else{return new F(function(){return _18O(_1YI,_1Z2.f,_1Z3.f);});}}}}}}else{return false;}break;case 1:var _1Z8=E(_1Z1);if(_1Z8._==1){return new F(function(){return _sf(_1Z2.a,_1Z8.a);});}else{return false;}break;case 2:return (E(_1Z1)._==2)?true:false;case 3:return (E(_1Z1)._==3)?true:false;case 4:return (E(_1Z1)._==4)?true:false;case 5:return (E(_1Z1)._==5)?true:false;default:var _1Z9=E(_1Z1);if(_1Z9._==6){if(!B(_18O(_1YI,_1Z2.a,_1Z9.a))){return false;}else{return new F(function(){return _18O(_1YY,_1Z2.b,_1Z9.b);});}}else{return false;}}},_1Za=function(_1Zb,_1Zc){return (!B(_1YZ(_1Zb,_1Zc)))?true:false;},_1YI=new T(function(){return new T2(0,_1YZ,_1Za);}),_1Zd=function(_1Ze,_1Zf){var _1Zg=E(_1Ze),_1Zh=E(_1Zf),_1Zi=E(_1Zg.c);if(!_1Zi){return (E(_1Zh.c)==0)?true:false;}else{if(E(_1Zg.a)!=E(_1Zh.a)){return false;}else{if(E(_1Zg.b)!=E(_1Zh.b)){return false;}else{var _1Zj=_1Zi-1|0;if(0<=_1Zj){var _1Zk=function(_1Zl){while(1){if(!B(_18O(_1YI,_1Zg.d[_1Zl],_1Zh.d[_1Zl]))){return false;}else{if(_1Zl!=_1Zj){var _1Zm=_1Zl+1|0;_1Zl=_1Zm;continue;}else{return true;}}}};return new F(function(){return _1Zk(0);});}else{return true;}}}}},_1Zn=function(_1Zo,_1Zp){var _1Zq=E(_1Zo),_1Zr=E(_1Zp),_1Zs=E(_1Zq.a),_1Zt=E(_1Zr.a),_1Zu=E(_1Zs.a),_1Zv=E(_1Zt.a);if(!B(_12M(_1Zu.a,_1Zu.b,_1Zu.c,_1Zv.a,_1Zv.b,_1Zv.c))){return false;}else{if(E(_1Zs.b)!=E(_1Zt.b)){return false;}else{if(E(_1Zq.b)!=E(_1Zr.b)){return false;}else{var _1Zw=E(_1Zq.c),_1Zx=E(_1Zr.c);if(!B(_12M(_1Zw.a,_1Zw.b,_1Zw.c,_1Zx.a,_1Zx.b,_1Zx.c))){return false;}else{if(!B(_18O(_18Y,_1Zq.d,_1Zr.d))){return false;}else{var _1Zy=E(_1Zq.e),_1Zz=E(_1Zr.e);if(!B(_18O(_1F6,_1Zy.a,_1Zz.a))){return false;}else{return new F(function(){return _1Zd(_1Zy.b,_1Zz.b);});}}}}}}},_1ZA=function(_1ZB,_1ZC,_1ZD){while(1){var _1ZE=E(_1ZD);if(!_1ZE._){return false;}else{if(!B(A2(_1ZB,_1ZE.a,_1ZC))){_1ZD=_1ZE.b;continue;}else{return true;}}}},_1ZF=function(_1ZG,_1ZH){var _1ZI=function(_1ZJ,_1ZK){while(1){var _1ZL=B((function(_1ZM,_1ZN){var _1ZO=E(_1ZM);if(!_1ZO._){return __Z;}else{var _1ZP=_1ZO.a,_1ZQ=_1ZO.b;if(!B(_1ZA(_1ZG,_1ZP,_1ZN))){return new T2(1,_1ZP,new T(function(){return B(_1ZI(_1ZQ,new T2(1,_1ZP,_1ZN)));}));}else{var _1ZR=_1ZN;_1ZJ=_1ZQ;_1ZK=_1ZR;return __continue;}}})(_1ZJ,_1ZK));if(_1ZL!=__continue){return _1ZL;}}};return new F(function(){return _1ZI(_1ZH,_4);});},_1ZS=function(_1ZT){return E(E(_1ZT).b);},_1ZU=function(_1ZV,_1ZW,_1ZX){var _1ZY=new T(function(){return E(E(E(_1ZV).c).b);}),_1ZZ=new T(function(){return E(E(_1ZW).h);}),_200=new T(function(){return E(E(_1ZW).d);}),_201=function(_202,_203,_204,_205,_206){var _207=E(_202);if(!_207._){return __Z;}else{var _208=E(_207.a),_209=_208.a,_20a=E(_208.b),_20b=B(_14V(_20a,_200));if(!_20b._){if(!B(_vZ(_j1,_20a,_1oY))){var _20c=B(_14V(_20a,_1ZZ));if(!_20c._){return __Z;}else{var _20d=function(_20e,_20f){while(1){var _20g=B((function(_20h,_20i){var _20j=E(_20i);if(!_20j._){var _20k=_20j.d,_20l=new T(function(){var _20m=E(_20j.b);if(_20m._==1){return B(_0(B(_201(new T1(1,new T2(0,_209,_20m.a)),_203,_204,_205,_206)),new T(function(){return B(_20d(_20h,_20k));},1)));}else{return B(_20d(_20h,_20k));}},1);_20e=_20l;_20f=_20j.c;return __continue;}else{return E(_20h);}})(_20e,_20f));if(_20g!=__continue){return _20g;}}};return new F(function(){return _20d(_4,_20c.a);});}}else{var _20n=new T(function(){var _20o=function(_){var _20p=newArr(1,_Vu),_20q=_20p,_20r=function(_20s,_20t,_){while(1){var _20u=E(_20s);if(_20u==1){return _5;}else{var _20v=E(_20t);if(!_20v._){return _5;}else{var _=_20q[_20u]=_20v.a;_20s=_20u+1|0;_20t=_20v.b;continue;}}}},_20w=B(_20r(0,new T2(1,new T2(1,new T1(1,_206),_4),_4),_));return new T4(0,E(_1Xe),E(_1Xe),1,_20q);};return B(_8O(_20o));});return new T2(1,new T2(0,new T(function(){return E(_203)+2|0;}),new T5(0,new T2(0,_209,new T(function(){return E(_203)+1|0;})),_20a,_1Cg,new T2(1,_204,_4),new T2(0,_205,_20n))),_4);}}else{var _20x=new T2(1,_204,_4),_20y=new T(function(){return E(_203)+2|0;}),_20z=new T(function(){return B(_1XW(_206));}),_20A=new T(function(){return E(_203)+1|0;}),_20B=function(_20C){var _20D=E(_20C);return (_20D._==0)?__Z:new T2(1,new T2(0,_20y,new T5(0,new T2(0,_209,_20A),_20a,_1Cg,_20x,new T(function(){var _20E=B(_1Wh(_1ZW,_1Xj,_205,_20D.a,new T2(1,new T5(0,new T2(0,_1Cg,_203),_1oS,_1Cg,_20x,new T2(0,_4,_20z)),_4)));return new T2(0,_20E.a,_20E.b);}))),new T(function(){return B(_20B(_20D.b));}));};return new F(function(){return _20B(_20b.a);});}}},_20F=new T(function(){return E(E(_1ZW).i);}),_20G=function(_20H,_20I,_20J,_20K,_20L,_20M,_20N){while(1){var _20O=B((function(_20P,_20Q,_20R,_20S,_20T,_20U,_20V){var _20W=E(_20U);switch(_20W._){case 0:var _20X=_20P,_20Y=_20Q,_20Z=_20R,_210=_20S,_211=new T2(1,_20W.b,_20T),_212=_20V;_20H=_20X;_20I=_20Y;_20J=_20Z;_20K=_210;_20L=_211;_20M=_20W.c;_20N=_212;return __continue;case 1:var _20X=_20P,_20Y=_20Q,_20Z=_20R,_210=_20S,_211=_20T,_212=new T2(1,_20W.b,_20V);_20H=_20X;_20I=_20Y;_20J=_20Z;_20K=_210;_20L=_211;_20M=_20W.a;_20N=_212;return __continue;case 2:if(!E(_20V)._){var _213=E(_20W.a);switch(_213._){case 0:return new T2(1,new T2(0,new T(function(){return E(_20Q)+1|0;}),new T5(0,new T2(0,_1Yq,_20Q),_1oS,_1Cg,new T2(1,_20R,_4),new T2(0,_4,new T(function(){return B(_1XW(_213.a));})))),_4);case 1:var _214=new T(function(){return B(_1XW(new T(function(){return B(_bZ(0,E(_213.a),_4));})));});return new T2(1,new T2(0,new T(function(){return E(_20Q)+1|0;}),new T5(0,new T2(0,_1Yl,_20Q),_1oT,_1Cg,new T2(1,_20R,_4),new T2(0,_4,_214))),_4);default:var _215=new T(function(){return B(_1XW(new T(function(){var _216=jsShow(E(_213.a));return fromJSStr(_216);})));});return new T2(1,new T2(0,new T(function(){return E(_20Q)+1|0;}),new T5(0,new T2(0,_1Yh,_20Q),_1oU,_1Cg,new T2(1,_20R,_4),new T2(0,_4,_215))),_4);}}else{return E(_1Yy);}break;case 3:return new F(function(){return _201(_20P,_20Q,_20R,_20T,new T2(1,_1Yz,new T(function(){return B(_bZ(0,_20W.a,_4));})));});break;case 4:var _217=E(_20W.a),_218=_217.a,_219=_217.b,_21a=_217.c,_21b=B(_1Y7(_218,_219,_21a,_20F));if(!_21b._){var _21c=new T(function(){return B(unAppCStr("[",new T(function(){return B(_0(B(_1Vi(_218,_219,_21a)),_1YC));})));});return new F(function(){return _201(_20P,_20Q,_20R,_20T,_21c);});}else{var _21d=_21b.a,_21e=new T(function(){var _21f=B(_1Y7(_218,_219,_21a,_1ZY));if(!_21f._){return E(_1YA);}else{var _21g=E(E(_21f.a).a);return new T2(0,new T(function(){return B(_1Yv(_21g.a));}),_21g.b);}}),_21h=new T(function(){return E(E(_21e).b);}),_21i=new T(function(){return E(E(_21e).a);}),_21j=function(_21k,_21l){var _21m=E(_21l);switch(_21m._){case 0:var _21n=new T(function(){return B(_jP(_21i,new T(function(){return B(_1Ys(_21m.b));},1)));});return new T2(1,new T3(0,_21m.a,new T2(0,_21h,_21k),_21n),_4);case 1:var _21o=_21m.a,_21p=B(_14V(_21o,_21d));if(!_21p._){return __Z;}else{var _21q=function(_21r,_21s){while(1){var _21t=B((function(_21u,_21v){var _21w=E(_21v);if(!_21w._){var _21x=new T(function(){return B(_0(B(_21j(_21o,_21w.b)),new T(function(){return B(_21q(_21u,_21w.d));},1)));},1);_21r=_21x;_21s=_21w.c;return __continue;}else{return E(_21u);}})(_21r,_21s));if(_21t!=__continue){return _21t;}}};return new F(function(){return _21q(_4,_21p.a);});}break;default:return E(_1YB);}},_21y=new T(function(){return B(_0(_20T,_20S));}),_21z=function(_21A,_21B){var _21C=E(_21B);if(!_21C._){return new T2(1,new T2(0,_21A,_4),_4);}else{var _21D=E(_21C.a),_21E=_21D.b,_21F=function(_21G){var _21H=E(_21G);if(!_21H._){return __Z;}else{var _21I=E(_21H.a),_21J=new T(function(){return B(_21F(_21H.b));}),_21K=function(_21L){var _21M=E(_21L);if(!_21M._){return E(_21J);}else{var _21N=E(_21M.a);return new T2(1,new T2(0,_21N.a,new T2(1,_21I.b,_21N.b)),new T(function(){return B(_21K(_21M.b));}));}};return new F(function(){return _21K(B(_21z(_21I.a,_21C.b)));});}};return new F(function(){return _21F(B(_20G(new T1(1,_21D.a),_21A,_21E,_21y,_4,_21E,_4)));});}},_21O=function(_21P,_21Q,_21R,_21S,_21T){var _21U=function(_21V){var _21W=E(_21V);if(!_21W._){return E(_21T);}else{var _21X=E(_21W.a),_21Y=_21X.a;return new T2(1,new T2(0,new T(function(){return E(_21Y)+1|0;}),new T5(0,new T2(0,_21Q,_21Y),_21R,_217,new T2(1,_20R,_4),new T(function(){var _21Z=B(_1Wh(_1ZW,_1Xj,_20T,_21P,_21X.b));return new T2(0,_21Z.a,_21Z.b);}))),new T(function(){return B(_21U(_21W.b));}));}};return new F(function(){return _21U(B(_21z(_20Q,B(_jP(_21S,_20V)))));});},_220=E(_20P);if(!_220._){var _221=function(_222,_223){while(1){var _224=B((function(_225,_226){var _227=E(_226);switch(_227._){case 0:_222=new T(function(){return B(_221(_225,_227.d));},1);_223=_227.c;return __continue;case 1:var _228=function(_229,_22a){while(1){var _22b=B((function(_22c,_22d){var _22e=E(_22d);if(!_22e._){var _22f=new T(function(){var _22g=new T(function(){return B(_228(_22c,_22e.d));}),_22h=function(_22i){var _22j=E(_22i);if(!_22j._){return E(_22g);}else{var _22k=E(_22j.a),_22l=E(_22k.b);return new F(function(){return _21O(_22k.a,_22l.a,_22l.b,_22k.c,new T(function(){return B(_22h(_22j.b));}));});}};return B(_22h(B(_21j(_227.a,_22e.b))));},1);_229=_22f;_22a=_22e.c;return __continue;}else{return E(_22c);}})(_229,_22a));if(_22b!=__continue){return _22b;}}};return new F(function(){return _228(_225,_227.b);});break;default:return E(_225);}})(_222,_223));if(_224!=__continue){return _224;}}},_22m=E(_21d);if(!_22m._){var _22n=_22m.c,_22o=_22m.d;if(_22m.b>=0){return new F(function(){return _221(new T(function(){return B(_221(_4,_22o));},1),_22n);});}else{return new F(function(){return _221(new T(function(){return B(_221(_4,_22n));},1),_22o);});}}else{return new F(function(){return _221(_4,_22m);});}}else{var _22p=E(E(_220.a).b),_22q=B(_14V(_22p,_21d));if(!_22q._){return __Z;}else{var _22r=function(_22s,_22t){while(1){var _22u=B((function(_22v,_22w){var _22x=E(_22w);if(!_22x._){var _22y=new T(function(){var _22z=new T(function(){return B(_22r(_22v,_22x.d));}),_22A=function(_22B){var _22C=E(_22B);if(!_22C._){return E(_22z);}else{var _22D=E(_22C.a),_22E=E(_22D.b);return new F(function(){return _21O(_22D.a,_22E.a,_22E.b,_22D.c,new T(function(){return B(_22A(_22C.b));}));});}};return B(_22A(B(_21j(_22p,_22x.b))));},1);_22s=_22y;_22t=_22x.c;return __continue;}else{return E(_22v);}})(_22s,_22t));if(_22u!=__continue){return _22u;}}};return new F(function(){return _22r(_4,_22q.a);});}}}break;case 5:return new F(function(){return _201(_20P,_20Q,_20R,_20T,new T(function(){var _22F=B(_1EF(B(_0(_20T,_20S)),_20W.a));return B(_1Vi(_22F.a,_22F.b,_22F.c));}));});break;case 6:var _20X=_20P,_20Y=_20Q,_20Z=_20R,_210=_20S,_211=_20T,_212=_20V;_20H=_20X;_20I=_20Y;_20J=_20Z;_20K=_210;_20L=_211;_20M=_20W.a;_20N=_212;return __continue;default:var _20X=_20P,_20Y=_20Q,_20Z=_20R,_210=_20S,_211=_20T,_212=_20V;_20H=_20X;_20I=_20Y;_20J=_20Z;_20K=_210;_20L=_211;_20M=_20W.a;_20N=_212;return __continue;}})(_20H,_20I,_20J,_20K,_20L,_20M,_20N));if(_20O!=__continue){return _20O;}}};return new F(function(){return _1ZF(_1Zn,B(_G(_1ZS,B(_20G(_4l,_1Xe,_1ZX,_4,_4,_1ZX,_4)))));});},_22G=function(_22H){var _22I=E(_22H);if(!_22I._){return __Z;}else{return new F(function(){return _0(_22I.a,new T(function(){return B(_22G(_22I.b));},1));});}},_22J=function(_22K){var _22L=E(_22K);if(!_22L._){return E(_1T7);}else{var _22M=E(_22L.a);if(!_22M._){return __Z;}else{var _22N=B(_22J(_22L.b));return (_22N._==0)?__Z:new T1(1,new T2(1,_22M.a,_22N.a));}}},_22O=function(_22P,_22Q){var _22R=new T(function(){return B(_1XL(_1Gx,_1XI,_22Q,B(_1XJ(_22P))));}),_22S=function(_22T,_22U,_22V,_22W,_22X){var _22Y=E(_22R),_22Z=B(_22J(B(_1Uq(B(_1Xr(_22Y.c,_22Y.e,_22Y.f,_22T,_22U,_22V,_22W,_22X)),_4l)).b));if(!_22Z._){return __Z;}else{return new F(function(){return _22G(_22Z.a);});}},_230=function(_231){var _232=E(_231);return new F(function(){return _22S(_232.a,E(_232.b),_232.c,_232.d,_232.e);});};return function(_233){var _234=B(_G(_230,B(_1ZU(_22P,_22R,_233))));return (_234._==0)?__Z:E(_234.a);};},_235=new T(function(){return B(unCStr("?0"));}),_236=new T2(0,_4,_235),_237=new T2(1,_236,_4),_238=0,_239=new T(function(){return B(_1Rk(_4,_4));}),_23a=function(_23b,_23c,_23d,_23e){while(1){var _23f=B((function(_23g,_23h,_23i,_23j){var _23k=E(_23g);if(!_23k._){return __Z;}else{var _23l=_23k.b,_23m=E(_23k.a);if(!_23m._){var _23n=E(_23h);if(E(_23m.b)!=_23n){var _23o=B(_23a(_23m.c,_23n,new T2(1,_23j,_23i),_238));if(!_23o._){var _23p=_23i;_23b=_23l;_23c=_23n;_23d=_23p;_23e=new T(function(){return E(_23j)+1|0;});return __continue;}else{return E(_23o);}}else{return new T2(1,_23j,_23i);}}else{var _23q=_23h,_23p=_23i;_23b=_23l;_23c=_23q;_23d=_23p;_23e=new T(function(){return E(_23j)+1|0;});return __continue;}}})(_23b,_23c,_23d,_23e));if(_23f!=__continue){return _23f;}}},_23r=function(_23s,_23t){var _23u=E(_23s);if(!_23u._){var _23v=E(_23t);if(E(_23u.b)!=_23v){return new F(function(){return _1Rk(B(_23a(_23u.c,_23v,_4,_238)),_4);});}else{return E(_239);}}else{return E(_239);}},_23w=new T(function(){return B(_7f("Muste.hs:(45,9)-(54,31)|function deep"));}),_23x=function(_23y,_23z,_23A,_23B){var _23C=E(_23A);if(!_23C._){return E(_23B);}else{var _23D=_23C.b,_23E=E(_23C.a);if(!_23E._){return new T2(1,new T2(0,new T(function(){return B(_23r(_23y,_23z));}),_23E.a),new T(function(){return B(_23x(_23y,_23z,_23D,_23B));}));}else{return new F(function(){return _0(B(_23F(_23y,_23E)),new T(function(){return B(_23x(_23y,_23z,_23D,_23B));},1));});}}},_23F=function(_23G,_23H){var _23I=E(_23H);if(!_23I._){return E(_23w);}else{var _23J=_23I.b,_23K=E(_23I.f);if(!_23K._){return __Z;}else{var _23L=function(_23M){var _23N=E(_23I.e);if(!_23N._){return new F(function(){return _23x(_23G,_23J,_23K,_4);});}else{var _23O=E(_23N.a);if(_23O._==3){if(!E(_23N.b)._){var _23P=new T(function(){return B(unAppCStr("?",new T(function(){return B(_bZ(0,_23O.a,_4));})));});return new T2(1,new T2(0,new T(function(){return B(_23r(_23G,_23J));}),_23P),_4);}else{return new F(function(){return _23x(_23G,_23J,_23K,_4);});}}else{return new F(function(){return _23x(_23G,_23J,_23K,_4);});}}},_23Q=E(_23K.a);if(!_23Q._){if(!E(_23K.b)._){return new T2(1,new T2(0,new T(function(){return B(_23r(_23G,_23J));}),_23Q.a),_4);}else{return new F(function(){return _23L(_);});}}else{return new F(function(){return _23L(_);});}}}},_23R=function(_23S){return E(E(_23S).c);},_23T=function(_23U){return new T1(3,E(_23U));},_23V=function(_23W,_23X){while(1){var _23Y=E(_23W);if(!_23Y._){return E(_23X);}else{var _23Z=new T2(1,_23X,_23Y.a);_23W=_23Y.b;_23X=_23Z;continue;}}},_240=function(_241,_242){var _243=E(_241);if(!_243._){var _244=new T(function(){var _245=B(_246(_243.c,_242));return new T2(0,_245.a,_245.b);});return new T2(0,new T(function(){return E(E(_244).a);}),new T(function(){return B(_23V(E(_244).b,new T1(4,_243.a)));}));}else{return new T2(0,new T(function(){return E(_242)+1|0;}),new T(function(){return B(_23T(_242));}));}},_246=function(_247,_248){var _249=E(_247);if(!_249._){return new T2(0,_248,_4);}else{var _24a=new T(function(){var _24b=B(_240(_249.a,_248));return new T2(0,_24b.a,_24b.b);}),_24c=new T(function(){var _24d=B(_246(_249.b,new T(function(){return E(E(_24a).a);})));return new T2(0,_24d.a,_24d.b);});return new T2(0,new T(function(){return E(E(_24c).a);}),new T2(1,new T(function(){return E(E(_24a).b);}),new T(function(){return E(E(_24c).b);})));}},_24e=new T1(3,0),_24f=function(_24g){var _24h=E(_24g);if(!_24h._){return new F(function(){return _23V(B(_246(_24h.c,_238)).b,new T1(4,_24h.a));});}else{return E(_24e);}},_24i=-1,_24j=function(_24k){var _24l=B(_24m(_24k));return new T3(0,_24l.a,_24l.b,_24l.c);},_24n=new T(function(){return B(unCStr("_"));}),_24o=new T(function(){return B(_1za(_24n));}),_24p=new T(function(){return B(_G(_1z8,_24o));}),_24q=new T(function(){var _24r=B(_1xU(_24p));return new T3(0,_24r.a,_24r.b,_24r.c);}),_24s=new T0(1),_24t=new T2(1,_24s,_4),_24u=new T3(0,_24q,_24i,_24t),_24v=new T2(1,_24u,_4),_24w=new T(function(){return B(_7f("Muste/Tree/Internal.hs:(285,5)-(287,70)|function convert"));}),_24m=function(_24x){var _24y=E(_24x);if(!_24y._){var _24z=E(_24y.b);if(!_24z._){var _24A=_24z.a,_24B=E(_24y.c);return (_24B._==0)?new T3(0,_24A,_24i,_4):new T3(0,_24A,_24i,new T(function(){return B(_G(_24j,_24B));}));}else{return E(_24w);}}else{return new T3(0,_24y.a,_24i,_24v);}},_24C=function(_24D,_24E){var _24F=E(_24E);if(!_24F._){return new T2(0,_24D,_4);}else{var _24G=new T(function(){var _24H=E(_24F.a);if(!_24H._){var _24I=_24H.a,_24J=E(_24H.c);if(!_24J._){return new T2(0,new T(function(){return E(_24D)+1|0;}),new T3(0,_24I,_24D,_4));}else{var _24K=new T(function(){var _24L=B(_24C(_24D,_24J));return new T2(0,_24L.a,_24L.b);}),_24M=new T(function(){return E(E(_24K).a);});return new T2(0,new T(function(){return E(_24M)+1|0;}),new T3(0,_24I,_24M,new T(function(){return E(E(_24K).b);})));}}else{return new T2(0,_24D,_24s);}}),_24N=new T(function(){var _24O=B(_24C(new T(function(){return E(E(_24G).a);}),_24F.b));return new T2(0,_24O.a,_24O.b);});return new T2(0,new T(function(){return E(E(_24N).a);}),new T2(1,new T(function(){return E(E(_24G).b);}),new T(function(){return E(E(_24N).b);})));}},_24P=function(_24Q){var _24R=B(_24m(_24Q)),_24S=_24R.a,_24T=E(_24R.c);if(!_24T._){return new T3(0,_24S,_238,_4);}else{var _24U=new T(function(){var _24V=B(_24C(_238,_24T));return new T2(0,_24V.a,_24V.b);});return new T3(0,_24S,new T(function(){return E(E(_24U).a);}),new T(function(){return E(E(_24U).b);}));}},_24W=function(_24X,_24Y,_24Z){var _250=new T(function(){return E(E(_24Z).a);}),_251=B(A3(_22O,new T(function(){return B(_23R(_24X));}),_24Y,new T(function(){return B(_24f(_250));})));if(!_251._){return E(_237);}else{return new F(function(){return _23F(new T(function(){return B(_24P(_250));}),_251.a);});}},_252=new T2(1,_4,_4),_253=function(_254,_255){var _256=function(_257,_258){var _259=E(_257);if(!_259._){return E(_258);}else{var _25a=_259.a,_25b=E(_258);if(!_25b._){return E(_259);}else{var _25c=_25b.a;return (B(A2(_254,_25a,_25c))==2)?new T2(1,_25c,new T(function(){return B(_256(_259,_25b.b));})):new T2(1,_25a,new T(function(){return B(_256(_259.b,_25b));}));}}},_25d=function(_25e){var _25f=E(_25e);if(!_25f._){return __Z;}else{var _25g=E(_25f.b);return (_25g._==0)?E(_25f):new T2(1,new T(function(){return B(_256(_25f.a,_25g.a));}),new T(function(){return B(_25d(_25g.b));}));}},_25h=new T(function(){return B(_25i(B(_25d(_4))));}),_25i=function(_25j){while(1){var _25k=E(_25j);if(!_25k._){return E(_25h);}else{if(!E(_25k.b)._){return E(_25k.a);}else{_25j=B(_25d(_25k));continue;}}}},_25l=new T(function(){return B(_25m(_4));}),_25n=function(_25o,_25p,_25q){while(1){var _25r=B((function(_25s,_25t,_25u){var _25v=E(_25u);if(!_25v._){return new T2(1,new T2(1,_25s,_25t),_25l);}else{var _25w=_25v.a;if(B(A2(_254,_25s,_25w))==2){var _25x=new T2(1,_25s,_25t);_25o=_25w;_25p=_25x;_25q=_25v.b;return __continue;}else{return new T2(1,new T2(1,_25s,_25t),new T(function(){return B(_25m(_25v));}));}}})(_25o,_25p,_25q));if(_25r!=__continue){return _25r;}}},_25y=function(_25z,_25A,_25B){while(1){var _25C=B((function(_25D,_25E,_25F){var _25G=E(_25F);if(!_25G._){return new T2(1,new T(function(){return B(A1(_25E,new T2(1,_25D,_4)));}),_25l);}else{var _25H=_25G.a,_25I=_25G.b;switch(B(A2(_254,_25D,_25H))){case 0:_25z=_25H;_25A=function(_25J){return new F(function(){return A1(_25E,new T2(1,_25D,_25J));});};_25B=_25I;return __continue;case 1:_25z=_25H;_25A=function(_25K){return new F(function(){return A1(_25E,new T2(1,_25D,_25K));});};_25B=_25I;return __continue;default:return new T2(1,new T(function(){return B(A1(_25E,new T2(1,_25D,_4)));}),new T(function(){return B(_25m(_25G));}));}}})(_25z,_25A,_25B));if(_25C!=__continue){return _25C;}}},_25m=function(_25L){var _25M=E(_25L);if(!_25M._){return E(_252);}else{var _25N=_25M.a,_25O=E(_25M.b);if(!_25O._){return new T2(1,_25M,_4);}else{var _25P=_25O.a,_25Q=_25O.b;if(B(A2(_254,_25N,_25P))==2){return new F(function(){return _25n(_25P,new T2(1,_25N,_4),_25Q);});}else{return new F(function(){return _25y(_25P,function(_25R){return new T2(1,_25N,_25R);},_25Q);});}}}};return new F(function(){return _25i(B(_25m(_255)));});},_25S=function(_25T,_25U,_25V,_25W){var _25X=B(_1ni(_4,_25W)),_25Y=new T(function(){return B(_G(_1ZS,B(_24W(_25T,_25U,_25V))));}),_25Z=function(_260,_261){var _262=E(_260);if(!_262._){return __Z;}else{var _263=E(_261);return (_263._==0)?__Z:new T2(1,new T2(0,new T(function(){var _264=E(_25Y);if(!_264._){var _265=B(_uU(_4,0));return _265+_265|0;}else{var _266=B(_G(_1ZS,B(_24W(_25T,_25U,_262.a))));if(!_266._){var _267=B(_uU(_4,0));return _267+_267|0;}else{var _268=B(_1Rp(_sz,_264,_266,_4,_4));return B(_uU(_268.a,0))+B(_uU(_268.b,0))|0;}}}),_263.a),new T(function(){return B(_25Z(_262.b,_263.b));}));}};return new F(function(){return _G(_1ZS,B(_253(function(_269,_26a){var _26b=E(_269),_26c=E(_26a),_26d=E(_26c.a),_26e=E(_26b.a);if(_26d>=_26e){if(_26d!=_26e){return 2;}else{var _26f=B(_24W(_25T,_25U,_26b.b)),_26g=B(_uU(_26f,0)),_26h=B(_24W(_25T,_25U,_26c.b)),_26i=B(_uU(_26h,0));if(_26g>=_26i){if(_26g!=_26i){return 2;}else{return new F(function(){return _1bD(_1T3,_26f,_26h);});}}else{return 0;}}}else{return 0;}},B(_25Z(_25X,_25X)))));});},_26j=function(_26k){while(1){var _26l=E(_26k);if(!_26l._){return false;}else{if(!E(_26l.a)){_26k=_26l.b;continue;}else{return true;}}}},_26m=function(_26n){var _26o=E(_26n);if(!_26o._){return new F(function(){return _26j(B(_G(_26m,_26o.c)));});}else{return true;}},_26p=function(_26q){return (!B(_26m(B(_1R0(_26q)))))?true:false;},_26r=function(_26s){while(1){var _26t=E(_26s);if(!_26t._){_26s=new T1(1,I_fromInt(_26t.a));continue;}else{return new F(function(){return I_toString(_26t.a);});}}},_26u=function(_26v,_26w){return new F(function(){return _0(fromJSStr(B(_26r(_26v))),_26w);});},_26x=new T1(0,0),_26y=function(_26z,_26A,_26B){if(_26z<=6){return new F(function(){return _26u(_26A,_26B);});}else{if(!B(_Fm(_26A,_26x))){return new F(function(){return _26u(_26A,_26B);});}else{return new T2(1,_bY,new T(function(){return B(_0(fromJSStr(B(_26r(_26A))),new T2(1,_bX,_26B)));}));}}},_26C=new T1(0,1),_26D=new T1(0,0),_26E=new T(function(){var _26F=B(_JB(_26D,_26C));return new T2(1,_26F.a,_26F.b);}),_26G=32,_26H=new T(function(){return B(unCStr(" "));}),_26I=new T2(0,_4,_26H),_26J=new T2(1,_26I,_4),_26K=function(_26L){var _26M=E(_26L);if(!_26M._){return E(_26J);}else{var _26N=E(_26M.a);return new T2(1,new T2(0,_26N.a,_26H),new T2(1,_26N,new T(function(){return B(_26K(_26M.b));})));}},_26O=function(_26P,_26Q,_26R){var _26S=function(_26T,_26U){var _26V=E(_26T);if(!_26V._){return __Z;}else{var _26W=_26V.b,_26X=E(_26U);if(!_26X._){return __Z;}else{var _26Y=_26X.b,_26Z=new T(function(){var _270=E(_26X.a),_271=new T(function(){var _272=new T(function(){if(!E(_26P)){return __Z;}else{return B(unAppCStr(" ",new T(function(){return B(_3X(_dY,_270.a,_4));})));}},1);return B(_0(_270.b,_272));});if(!E(_26Q)){return B(_0(_271,new T(function(){return B(_26S(_26W,_26Y));},1)));}else{var _273=new T(function(){return B(_0(B(_26y(0,_26V.a,_4)),new T(function(){return B(unAppCStr(") ",_271));},1)));});return B(_0(B(unAppCStr("(",_273)),new T(function(){return B(_26S(_26W,_26Y));},1)));}});return new T2(1,_26G,_26Z);}}},_274=B(_26S(_26E,new T(function(){return B(_26K(_26R));},1)));return (_274._==0)?__Z:E(_274.b);},_275=function(_276,_277,_278){var _279=function(_27a){return new F(function(){return _26O(_w7,_w7,new T(function(){return B(_24W(_276,_277,_27a));},1));});};return new F(function(){return _G(_279,_278);});},_27b=function(_27c,_27d){var _27e=E(_27d);if(!_27e._){return new T2(0,_4,_4);}else{var _27f=_27e.a;if(!B(A1(_27c,_27f))){var _27g=new T(function(){var _27h=B(_27b(_27c,_27e.b));return new T2(0,_27h.a,_27h.b);});return new T2(0,new T2(1,_27f,new T(function(){return E(E(_27g).a);})),new T(function(){return E(E(_27g).b);}));}else{return new T2(0,_4,_27e);}}},_27i=function(_27j){var _27k=_27j>>>0;if(_27k>887){var _27l=u_iswspace(_27j);return (E(_27l)==0)?false:true;}else{var _27m=E(_27k);return (_27m==32)?true:(_27m-9>>>0>4)?(E(_27m)==160)?true:false:true;}},_27n=function(_27o){return new F(function(){return _27i(E(_27o));});},_27p=function(_27q){var _27r=B(_G7(_27n,_27q));if(!_27r._){return __Z;}else{var _27s=new T(function(){var _27t=B(_27b(_27n,_27r));return new T2(0,_27t.a,_27t.b);});return new T2(1,new T(function(){return E(E(_27s).a);}),new T(function(){return B(_27p(E(_27s).b));}));}},_27u=function(_27v,_27w,_27x,_27y,_27z,_27A){var _27B=new T(function(){var _27C=B(_1EO(new T(function(){return B(_1R0(_27x));}),_27y));if(!_27C._){return E(_1F1);}else{return E(_27C.a);}}),_27D=new T2(0,_27B,_ML),_27E=new T(function(){return B(_G(_1ZS,B(_24W(_27v,_27w,_27D))));}),_27F=new T(function(){return B(_uU(_27E,0));}),_27G=new T(function(){var _27H=B(_uU(B(_24W(_27v,_27w,_27D)),0));if(!E(_27z)){return _27H;}else{return _27H+1|0;}}),_27I=B(_1Qf(function(_27J){return E(_27G)>=B(_uU(B(_24W(_27v,_27w,_27J)),0));},B(_25S(_27v,_27w,_27D,B(_1o1(_26p,B(_1R2(_27v,_27x,_27y,_27A)))))))),_27K=function(_27L,_27M){while(1){var _27N=B((function(_27O,_27P){var _27Q=E(_27O);if(!_27Q._){return __Z;}else{var _27R=_27Q.a,_27S=_27Q.b,_27T=E(_27P);if(!_27T._){return __Z;}else{var _27U=_27T.a,_27V=_27T.b,_27W=B(_27p(_27R));if(!B(_1aJ(_27W,_27E))){var _27X=B(_uU(_27W,0)),_27Y=E(_27F);if(_27X!=_27Y){if(_27X<=_27Y){_27L=_27S;_27M=_27V;return __continue;}else{var _27Z=E(_27W);if(!_27Z._){var _280=B(_uU(_4,0));if(!(_280+_280|0)){_27L=_27S;_27M=_27V;return __continue;}else{return new T2(1,new T2(0,_27R,_27U),new T(function(){return B(_27K(_27S,_27V));}));}}else{var _281=E(_27E);if(!_281._){var _282=B(_uU(_4,0));if(!(_282+_282|0)){_27L=_27S;_27M=_27V;return __continue;}else{return new T2(1,new T2(0,_27R,_27U),new T(function(){return B(_27K(_27S,_27V));}));}}else{var _283=B(_1Rp(_sz,_27Z,_281,_4,_4));if(!(B(_uU(_283.a,0))+B(_uU(_283.b,0))|0)){_27L=_27S;_27M=_27V;return __continue;}else{return new T2(1,new T2(0,_27R,_27U),new T(function(){return B(_27K(_27S,_27V));}));}}}}}else{return new T2(1,new T2(0,_27R,_27U),new T(function(){return B(_27K(_27S,_27V));}));}}else{_27L=_27S;_27M=_27V;return __continue;}}}})(_27L,_27M));if(_27N!=__continue){return _27N;}}};return new F(function(){return _27K(B(_275(_27v,_27w,_27I)),_27I);});},_284=new T(function(){return new T1(1,"left");}),_285=new T(function(){return new T1(1,"top");}),_286=new T(function(){return new T2(0,E(new T1(2,"id")),"suggestionList");}),_287=new T(function(){return B(unCStr("offsetTop"));}),_288=new T(function(){return B(unCStr("offsetLeft"));}),_289=new T(function(){return B(err(_rk));}),_28a=new T(function(){return B(err(_rm));}),_28b=function(_28c,_28d){var _28e=function(_28f,_28g){var _28h=function(_28i){return new F(function(){return A1(_28g,new T(function(){return  -E(_28i);}));});},_28j=new T(function(){return B(_CR(function(_28k){return new F(function(){return A3(_28c,_28k,_28f,_28h);});}));}),_28l=function(_28m){return E(_28j);},_28n=function(_28o){return new F(function(){return A2(_By,_28o,_28l);});},_28p=new T(function(){return B(_CR(function(_28q){var _28r=E(_28q);if(_28r._==4){var _28s=E(_28r.a);if(!_28s._){return new F(function(){return A3(_28c,_28r,_28f,_28g);});}else{if(E(_28s.a)==45){if(!E(_28s.b)._){return E(new T1(1,_28n));}else{return new F(function(){return A3(_28c,_28r,_28f,_28g);});}}else{return new F(function(){return A3(_28c,_28r,_28f,_28g);});}}}else{return new F(function(){return A3(_28c,_28r,_28f,_28g);});}}));}),_28t=function(_28u){return E(_28p);};return new T1(1,function(_28v){return new F(function(){return A2(_By,_28v,_28t);});});};return new F(function(){return _DI(_28e,_28d);});},_28w=function(_28x){var _28y=E(_28x);if(!_28y._){var _28z=_28y.b,_28A=new T(function(){return B(_v9(new T(function(){return B(_oz(E(_28y.a)));}),new T(function(){return B(_uU(_28z,0));},1),B(_G(_uZ,_28z))));});return new T1(1,_28A);}else{return (E(_28y.b)._==0)?(E(_28y.c)._==0)?new T1(1,new T(function(){return B(_vq(_uT,_28y.a));})):__Z:__Z;}},_28B=function(_28C){var _28D=E(_28C);if(_28D._==5){var _28E=B(_28w(_28D.a));if(!_28E._){return E(_GG);}else{var _28F=new T(function(){return B(_oP(_28E.a));});return function(_28G,_28H){return new F(function(){return A1(_28H,_28F);});};}}else{return E(_GG);}},_28I=new T(function(){return B(A3(_28b,_28B,_Do,_Im));}),_28J=new T(function(){return B(unCStr("div"));}),_28K=new T(function(){return B(unCStr("px"));}),_28L=new T(function(){return B(unCStr("suggestionList"));}),_28M=new T(function(){return B(unCStr(")"));}),_28N=new T(function(){return eval("(function(s){return document.createTextNode(s);})");}),_28O=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_28P=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_28Q=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_28R=function(_28S,_28T,_28U,_28V){var _28W=new T(function(){return B(A2(_1E9,_28S,_28U));}),_28X=function(_28Y,_){var _28Z=E(_28Y);if(!_28Z._){return _5;}else{var _290=E(_28W),_291=E(_1E1),_292=__app2(_291,E(_28Z.a),_290),_293=function(_294,_){while(1){var _295=E(_294);if(!_295._){return _5;}else{var _296=__app2(_291,E(_295.a),_290);_294=_295.b;continue;}}};return new F(function(){return _293(_28Z.b,_);});}},_297=function(_298,_){while(1){var _299=B((function(_29a,_){var _29b=E(_29a);if(!_29b._){return _5;}else{var _29c=_29b.b,_29d=E(_29b.a);if(!_29d._){var _29e=_29d.b,_29f=E(_29d.a);switch(_29f._){case 0:var _29g=E(_28W),_29h=E(_28Q),_29i=__app3(_29h,_29g,_29f.a,_29e),_29j=function(_29k,_){while(1){var _29l=E(_29k);if(!_29l._){return _5;}else{var _29m=_29l.b,_29n=E(_29l.a);if(!_29n._){var _29o=_29n.b,_29p=E(_29n.a);switch(_29p._){case 0:var _29q=__app3(_29h,_29g,_29p.a,_29o);_29k=_29m;continue;case 1:var _29r=__app3(E(_28P),_29g,_29p.a,_29o);_29k=_29m;continue;default:var _29s=__app3(E(_28O),_29g,_29p.a,_29o);_29k=_29m;continue;}}else{var _29t=B(_28X(_29n.a,_));_29k=_29m;continue;}}}};return new F(function(){return _29j(_29c,_);});break;case 1:var _29u=E(_28W),_29v=E(_28P),_29w=__app3(_29v,_29u,_29f.a,_29e),_29x=function(_29y,_){while(1){var _29z=E(_29y);if(!_29z._){return _5;}else{var _29A=_29z.b,_29B=E(_29z.a);if(!_29B._){var _29C=_29B.b,_29D=E(_29B.a);switch(_29D._){case 0:var _29E=__app3(E(_28Q),_29u,_29D.a,_29C);_29y=_29A;continue;case 1:var _29F=__app3(_29v,_29u,_29D.a,_29C);_29y=_29A;continue;default:var _29G=__app3(E(_28O),_29u,_29D.a,_29C);_29y=_29A;continue;}}else{var _29H=B(_28X(_29B.a,_));_29y=_29A;continue;}}}};return new F(function(){return _29x(_29c,_);});break;default:var _29I=E(_28W),_29J=E(_28O),_29K=__app3(_29J,_29I,_29f.a,_29e),_29L=function(_29M,_){while(1){var _29N=E(_29M);if(!_29N._){return _5;}else{var _29O=_29N.b,_29P=E(_29N.a);if(!_29P._){var _29Q=_29P.b,_29R=E(_29P.a);switch(_29R._){case 0:var _29S=__app3(E(_28Q),_29I,_29R.a,_29Q);_29M=_29O;continue;case 1:var _29T=__app3(E(_28P),_29I,_29R.a,_29Q);_29M=_29O;continue;default:var _29U=__app3(_29J,_29I,_29R.a,_29Q);_29M=_29O;continue;}}else{var _29V=B(_28X(_29P.a,_));_29M=_29O;continue;}}}};return new F(function(){return _29L(_29c,_);});}}else{var _29W=B(_28X(_29d.a,_));_298=_29c;return __continue;}}})(_298,_));if(_299!=__continue){return _299;}}};return new F(function(){return A2(_6i,_28T,function(_){return new F(function(){return _297(_28V,_);});});});},_29X=function(_29Y,_29Z,_2a0,_2a1){var _2a2=B(_2z(_29Z)),_2a3=function(_2a4){return new F(function(){return A3(_6c,_2a2,new T(function(){return B(_28R(_29Y,_29Z,_2a4,_2a1));}),new T(function(){return B(A2(_1DT,_2a2,_2a4));}));});};return new F(function(){return A3(_1V,_2a2,_2a0,_2a3);});},_2a5=new T(function(){return eval("(function(x){console.log(x);})");}),_2a6=function(_2a7,_2a8,_2a9,_2aa,_2ab,_2ac,_2ad,_){var _2ae=B(A(_1Ek,[_1DY,_dh,_2ac,_288,_])),_2af=B(A(_1Ek,[_1DY,_dh,_2ac,_287,_])),_2ag=new T(function(){return E(E(_2ad).a);}),_2ah=new T(function(){return E(E(_2ag).a);}),_2ai=new T(function(){var _2aj=B(_It(B(_rr(_28I,_2ae))));if(!_2aj._){return E(_289);}else{if(!E(_2aj.b)._){return E(_2ah)+E(_2aj.a)|0;}else{return E(_28a);}}}),_2ak=new T(function(){return E(E(_2ag).b);}),_2al=new T(function(){var _2am=B(_It(B(_rr(_28I,_2af))));if(!_2am._){return E(_289);}else{if(!E(_2am.b)._){return E(_2ak)+E(_2am.a)|0;}else{return E(_28a);}}}),_2an=new T(function(){var _2ao=new T(function(){return B(unAppCStr(",",new T(function(){return B(_0(B(_bZ(0,E(_2al)+E(_2ak)|0,_4)),_28M));})));},1);return B(_0(B(_bZ(0,E(_2ai)+E(_2ah)|0,_4)),_2ao));}),_2ap=__app1(E(_2a5),toJSStr(B(unAppCStr("Click on (",_2an)))),_2aq=__app1(E(_1E6),toJSStr(E(_28L))),_2ar=__eq(_2aq,E(_D)),_2as=function(_,_2at){var _2au=function(_){var _2av=B(A(_29X,[_1DY,_dh,_1E0,new T2(1,_286,new T2(1,new T(function(){return new T2(0,E(_285),toJSStr(B(_0(B(_bZ(0,E(_2al),_4)),_28K))));}),new T2(1,new T(function(){return new T2(0,E(_284),toJSStr(B(_0(B(_bZ(0,E(_2ai),_4)),_28K))));}),_4))),_])),_2aw=_2av,_2ax=function(_2ay,_){while(1){var _2az=E(_2ay);if(!_2az._){return _5;}else{var _2aA=__app1(E(_28N),toJSStr(E(E(_2az.a).a))),_2aB=__app1(E(_1DZ),toJSStr(E(_28J))),_2aC=E(_1E1),_2aD=__app2(_2aC,_2aA,_2aB),_2aE=__app2(_2aC,_2aB,E(_2aw));_2ay=_2az.b;continue;}}},_2aF=B(_2ax(B(_27u(_2a7,_2a8,_2a9,_2aa,_2ab,_1E4)),_)),_2aG=__app2(E(_1E1),E(_2aw),E(_1E5));return _5;},_2aH=E(_2at);if(!_2aH._){return new F(function(){return _2au(_);});}else{var _2aI=E(_2aH.a),_2aJ=__app1(E(_1E2),_2aI),_2aK=__app2(E(_1E3),_2aI,E(_1E5));return new F(function(){return _2au(_);});}};if(!E(_2ar)){var _2aL=__isUndef(_2aq);if(!E(_2aL)){return new F(function(){return _2as(_,new T1(1,_2aq));});}else{return new F(function(){return _2as(_,_4l);});}}else{return new F(function(){return _2as(_,_4l);});}},_2aM=new T(function(){return eval("(function(b){return b.size;})");}),_2aN=function(_2aO){return new F(function(){return _z(function(_){var _2aP=__app1(E(_2aM),E(_2aO));return new F(function(){return _cr(_2aP,0);});});});},_2aQ=0,_2aR=new T1(1,_4),_2aS=new T(function(){return eval("(function(b,cb){var r=new FileReader();r.onload=function(){cb(new DataView(r.result));};r.readAsArrayBuffer(b);})");}),_2aT=function(_2aU,_2aV){var _2aW=new T(function(){return B(_2aN(_2aV));}),_2aX=function(_2aY){var _2aZ=function(_){var _2b0=nMV(_2aR),_2b1=_2b0,_2b2=function(_){var _2b3=function(_2b4,_){var _2b5=B(_c(new T(function(){return B(A(_7r,[_2l,_2b1,new T3(0,_2aQ,_2aW,_2b4),_2c]));}),_4,_));return _D;},_2b6=__createJSFunc(2,E(_2b3)),_2b7=__app2(E(_2aS),E(_2aV),_2b6);return new T(function(){return B(A3(_7H,_2l,_2b1,_2aY));});};return new T1(0,_2b2);};return new T1(0,_2aZ);};return new F(function(){return A2(_6g,_2aU,_2aX);});},_2b8=function(_2b9,_2ba){while(1){var _2bb=E(_2ba);if(!_2bb._){_2b9=_2bb.b;_2ba=_2bb.d;continue;}else{return E(_2b9);}}},_2bc=new T(function(){return B(unCStr("AjaxError"));}),_2bd=new T(function(){return B(err(_2bc));}),_2be=new T(function(){return B(unCStr("ACK"));}),_2bf=new T(function(){return B(unCStr("BEL"));}),_2bg=new T(function(){return B(unCStr("BS"));}),_2bh=new T(function(){return B(unCStr("SP"));}),_2bi=new T2(1,_2bh,_4),_2bj=new T(function(){return B(unCStr("US"));}),_2bk=new T2(1,_2bj,_2bi),_2bl=new T(function(){return B(unCStr("RS"));}),_2bm=new T2(1,_2bl,_2bk),_2bn=new T(function(){return B(unCStr("GS"));}),_2bo=new T2(1,_2bn,_2bm),_2bp=new T(function(){return B(unCStr("FS"));}),_2bq=new T2(1,_2bp,_2bo),_2br=new T(function(){return B(unCStr("ESC"));}),_2bs=new T2(1,_2br,_2bq),_2bt=new T(function(){return B(unCStr("SUB"));}),_2bu=new T2(1,_2bt,_2bs),_2bv=new T(function(){return B(unCStr("EM"));}),_2bw=new T2(1,_2bv,_2bu),_2bx=new T(function(){return B(unCStr("CAN"));}),_2by=new T2(1,_2bx,_2bw),_2bz=new T(function(){return B(unCStr("ETB"));}),_2bA=new T2(1,_2bz,_2by),_2bB=new T(function(){return B(unCStr("SYN"));}),_2bC=new T2(1,_2bB,_2bA),_2bD=new T(function(){return B(unCStr("NAK"));}),_2bE=new T2(1,_2bD,_2bC),_2bF=new T(function(){return B(unCStr("DC4"));}),_2bG=new T2(1,_2bF,_2bE),_2bH=new T(function(){return B(unCStr("DC3"));}),_2bI=new T2(1,_2bH,_2bG),_2bJ=new T(function(){return B(unCStr("DC2"));}),_2bK=new T2(1,_2bJ,_2bI),_2bL=new T(function(){return B(unCStr("DC1"));}),_2bM=new T2(1,_2bL,_2bK),_2bN=new T(function(){return B(unCStr("DLE"));}),_2bO=new T2(1,_2bN,_2bM),_2bP=new T(function(){return B(unCStr("SI"));}),_2bQ=new T2(1,_2bP,_2bO),_2bR=new T(function(){return B(unCStr("SO"));}),_2bS=new T2(1,_2bR,_2bQ),_2bT=new T(function(){return B(unCStr("CR"));}),_2bU=new T2(1,_2bT,_2bS),_2bV=new T(function(){return B(unCStr("FF"));}),_2bW=new T2(1,_2bV,_2bU),_2bX=new T(function(){return B(unCStr("VT"));}),_2bY=new T2(1,_2bX,_2bW),_2bZ=new T(function(){return B(unCStr("LF"));}),_2c0=new T2(1,_2bZ,_2bY),_2c1=new T(function(){return B(unCStr("HT"));}),_2c2=new T2(1,_2c1,_2c0),_2c3=new T2(1,_2bg,_2c2),_2c4=new T2(1,_2bf,_2c3),_2c5=new T2(1,_2be,_2c4),_2c6=new T(function(){return B(unCStr("ENQ"));}),_2c7=new T2(1,_2c6,_2c5),_2c8=new T(function(){return B(unCStr("EOT"));}),_2c9=new T2(1,_2c8,_2c7),_2ca=new T(function(){return B(unCStr("ETX"));}),_2cb=new T2(1,_2ca,_2c9),_2cc=new T(function(){return B(unCStr("STX"));}),_2cd=new T2(1,_2cc,_2cb),_2ce=new T(function(){return B(unCStr("SOH"));}),_2cf=new T2(1,_2ce,_2cd),_2cg=new T(function(){return B(unCStr("NUL"));}),_2ch=new T2(1,_2cg,_2cf),_2ci=92,_2cj=new T(function(){return B(unCStr("\\DEL"));}),_2ck=new T(function(){return B(unCStr("\\a"));}),_2cl=new T(function(){return B(unCStr("\\\\"));}),_2cm=new T(function(){return B(unCStr("\\SO"));}),_2cn=new T(function(){return B(unCStr("\\r"));}),_2co=new T(function(){return B(unCStr("\\f"));}),_2cp=new T(function(){return B(unCStr("\\v"));}),_2cq=new T(function(){return B(unCStr("\\n"));}),_2cr=new T(function(){return B(unCStr("\\t"));}),_2cs=new T(function(){return B(unCStr("\\b"));}),_2ct=function(_2cu,_2cv){if(_2cu<=127){var _2cw=E(_2cu);switch(_2cw){case 92:return new F(function(){return _0(_2cl,_2cv);});break;case 127:return new F(function(){return _0(_2cj,_2cv);});break;default:if(_2cw<32){var _2cx=E(_2cw);switch(_2cx){case 7:return new F(function(){return _0(_2ck,_2cv);});break;case 8:return new F(function(){return _0(_2cs,_2cv);});break;case 9:return new F(function(){return _0(_2cr,_2cv);});break;case 10:return new F(function(){return _0(_2cq,_2cv);});break;case 11:return new F(function(){return _0(_2cp,_2cv);});break;case 12:return new F(function(){return _0(_2co,_2cv);});break;case 13:return new F(function(){return _0(_2cn,_2cv);});break;case 14:return new F(function(){return _0(_2cm,new T(function(){var _2cy=E(_2cv);if(!_2cy._){return __Z;}else{if(E(_2cy.a)==72){return B(unAppCStr("\\&",_2cy));}else{return E(_2cy);}}},1));});break;default:return new F(function(){return _0(new T2(1,_2ci,new T(function(){return B(_1EF(_2ch,_2cx));})),_2cv);});}}else{return new T2(1,_2cw,_2cv);}}}else{var _2cz=new T(function(){var _2cA=jsShowI(_2cu);return B(_0(fromJSStr(_2cA),new T(function(){var _2cB=E(_2cv);if(!_2cB._){return __Z;}else{var _2cC=E(_2cB.a);if(_2cC<48){return E(_2cB);}else{if(_2cC>57){return E(_2cB);}else{return B(unAppCStr("\\&",_2cB));}}}},1)));});return new T2(1,_2ci,_2cz);}},_2cD=new T(function(){return B(unCStr("\\\""));}),_2cE=function(_2cF,_2cG){var _2cH=E(_2cF);if(!_2cH._){return E(_2cG);}else{var _2cI=_2cH.b,_2cJ=E(_2cH.a);if(_2cJ==34){return new F(function(){return _0(_2cD,new T(function(){return B(_2cE(_2cI,_2cG));},1));});}else{return new F(function(){return _2ct(_2cJ,new T(function(){return B(_2cE(_2cI,_2cG));}));});}}},_2cK=34,_2cL=function(_2cM,_2cN){return new T2(1,_2cK,new T(function(){return B(_2cE(_2cM,new T2(1,_2cK,_2cN)));}));},_2cO=function(_2cP,_2cQ){var _2cR=E(_2cP),_2cS=new T(function(){return B(A3(_eg,_e6,new T2(1,function(_2cT){return new F(function(){return _e1(_2cR.a,_2cT);});},new T2(1,function(_2cU){return new F(function(){return _2cL(_2cR.b,_2cU);});},_4)),new T2(1,_bX,_2cQ)));});return new T2(1,_bY,_2cS);},_2cV=function(_){return new F(function(){return __app1(E(_1DZ),"span");});},_2cW=new T(function(){return new T2(0,E(new T1(2,"class")),"path");}),_2cX=new T2(1,_2cW,_4),_2cY=new T(function(){return B(_29X(_1DY,_dh,_2cV,_2cX));}),_2cZ=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:81:7-21"));}),_2d0=new T6(0,_4l,_4m,_4,_2cZ,_4l,_4l),_2d1=new T(function(){return B(_4d(_2d0));}),_2d2=new T(function(){return B(unCStr(" "));}),_2d3=new T(function(){return B(unCStr("linTree"));}),_2d4=new T(function(){return B(unCStr("Got blobdata"));}),_2d5=new T(function(){return B(unCStr("Foods.pgf"));}),_2d6=new T(function(){return B(unAppCStr("Loaded pgf as Blob ",_2d5));}),_2d7=new T(function(){return new T2(0,E(new T1(2,"class")),"word");}),_2d8=new T2(1,_2d7,_4),_2d9=new T(function(){return B(_29X(_1DY,_dh,_2cV,_2d8));}),_2da=new T(function(){return new T2(0,E(new T1(2,"class")),"gap");}),_2db=new T2(1,_2da,_4),_2dc=new T(function(){return B(_29X(_1DY,_dh,_2cV,_2db));}),_2dd=function(_2de){return E(E(_2de).a);},_2df=function(_2dg){return E(E(_2dg).b);},_2dh=function(_2di){return E(E(_2di).a);},_2dj=function(_){return new F(function(){return nMV(_4l);});},_2dk=new T(function(){return B(_z(_2dj));}),_2dl=function(_2dm){return E(E(_2dm).b);},_2dn=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_2do=function(_2dp,_2dq,_2dr,_2ds,_2dt,_2du){var _2dv=B(_2dd(_2dp)),_2dw=B(_2z(_2dv)),_2dx=new T(function(){return B(_6i(_2dv));}),_2dy=new T(function(){return B(_1DT(_2dw));}),_2dz=new T(function(){return B(A1(_2dq,_2ds));}),_2dA=new T(function(){return B(A2(_2dh,_2dr,_2dt));}),_2dB=function(_2dC){return new F(function(){return A1(_2dy,new T3(0,_2dA,_2dz,_2dC));});},_2dD=function(_2dE){var _2dF=new T(function(){var _2dG=new T(function(){var _2dH=__createJSFunc(2,function(_2dI,_){var _2dJ=B(A2(E(_2dE),_2dI,_));return _D;}),_2dK=_2dH;return function(_){return new F(function(){return __app3(E(_2dn),E(_2dz),E(_2dA),_2dK);});};});return B(A1(_2dx,_2dG));});return new F(function(){return A3(_1V,_2dw,_2dF,_2dB);});},_2dL=new T(function(){var _2dM=new T(function(){return B(_6i(_2dv));}),_2dN=function(_2dO){var _2dP=new T(function(){return B(A1(_2dM,function(_){var _=wMV(E(_2dk),new T1(1,_2dO));return new F(function(){return A(_2df,[_2dr,_2dt,_2dO,_]);});}));});return new F(function(){return A3(_1V,_2dw,_2dP,_2du);});};return B(A2(_2dl,_2dp,_2dN));});return new F(function(){return A3(_1V,_2dw,_2dL,_2dD);});},_2dQ=0,_2dR=function(_2dS){var _2dT=E(_2dS);return new F(function(){return _1Vi(_2dT.a,_2dT.b,_2dT.c);});},_2dU=new T(function(){return B(err(_rk));}),_2dV=new T(function(){return B(err(_rm));}),_2dW=new T(function(){return B(unCStr("_"));}),_2dX=92,_2dY=39,_2dZ=function(_2e0){var _2e1=E(_2e0);if(!_2e1._){return __Z;}else{var _2e2=_2e1.b,_2e3=E(_2e1.a);switch(E(_2e3)){case 39:return __Z;case 92:var _2e4=E(_2e2);if(!_2e4._){return __Z;}else{var _2e5=_2e4.b;switch(E(_2e4.a)){case 39:return new T2(1,new T2(0,_2dY,_2e5),_4);case 92:return new T2(1,new T2(0,_2dX,_2e5),_4);default:return __Z;}}break;default:return new T2(1,new T2(0,_2e3,_2e2),_4);}}},_2e6=function(_2e7,_2e8){var _2e9=function(_2ea){var _2eb=E(_2ea);if(!_2eb._){return __Z;}else{var _2ec=E(_2eb.a);return new F(function(){return _0(B(_rr(B(A1(_2e8,_2ec.a)),_2ec.b)),new T(function(){return B(_2e9(_2eb.b));},1));});}};return function(_2ed){var _2ee=B(_2e9(B(A1(_2e7,_2ed))));return (_2ee._==0)?new T0(2):new T1(4,_2ee);};},_2ef=function(_2eg){return new T1(1,B(_2e6(_2dZ,_2eg)));},_2eh=function(_2ei,_2ej){var _2ek=new T(function(){var _2el=function(_2em){return new F(function(){return _2eh(_2ei,function(_2en){return new F(function(){return A1(_2ej,new T2(1,_2em,_2en));});});});};return B(A1(_2ei,_2el));});return new F(function(){return _rB(B(A1(_2ej,_4)),_2ek);});},_2eo=function(_2ep){var _2eq=function(_2er){var _2es=E(_2er);if(!_2es._){return __Z;}else{var _2et=E(_2es.a),_2eu=function(_2ev){var _2ew=new T(function(){return B(A1(_2ep,new T2(1,_2et.a,_2ev)));});return new T1(0,function(_2ex){return (E(_2ex)==39)?E(_2ew):new T0(2);});};return new F(function(){return _0(B(_rr(B(_2eh(_2ef,_2eu)),_2et.b)),new T(function(){return B(_2eq(_2es.b));},1));});}},_2ey=function(_2ez){var _2eA=B(_2eq(B(_2dZ(_2ez))));return (_2eA._==0)?new T0(2):new T1(4,_2eA);};return function(_2eB){return (E(_2eB)==39)?E(new T1(1,_2ey)):new T0(2);};},_2eC=function(_2eD){var _2eE=B(_1xU(B(_G(_1z8,B(_1za(_2eD))))));return new T3(0,_2eE.a,_2eE.b,_2eE.c);},_2eF=function(_2eG){return new F(function(){return _1UX(E(_2eG));});},_2eH=function(_2eI){var _2eJ=function(_2eK){if(!B(_sf(_2eK,_2dW))){return new F(function(){return A1(_2eI,new T(function(){return B(_2eC(_2eK));}));});}else{return new T0(2);}},_2eL=function(_2eM){var _2eN=E(_2eM);return (!B(_1Uy(_2eN)))?new T0(2):new T1(1,B(_tk(_2eF,function(_2eO){return new F(function(){return _2eJ(new T2(1,_2eN,_2eO));});})));};return new F(function(){return _rB(new T1(0,_2eL),new T(function(){return new T1(0,B(_2eo(_2eJ)));}));});},_2eP=new T(function(){return B(_2eH(_sM));}),_2eQ=function(_2eR,_2eS){while(1){var _2eT=E(_2eR);if(!_2eT._){return E(_2eS);}else{_2eR=_2eT.b;_2eS=_2eT.a;continue;}}},_2eU=function(_2eV,_2eW){var _2eX=new T(function(){var _2eY=B(_2eZ(B(_1ZS(_2eV))));return new T2(0,_2eY.a,_2eY.b);});return new T2(0,new T2(1,new T(function(){return B(_1Mj(_2eV));}),new T(function(){return B(_1Mj(_2eX));})),new T(function(){return B(_1ZS(_2eX));}));},_2eZ=function(_2f0){var _2f1=E(_2f0);if(!_2f1._){return new T2(0,_4,_4);}else{if(E(_2f1.a)==32){var _2f2=B(_2f3(_2f1.b));if(!_2f2._){return new T2(0,_4,_2f1);}else{return new F(function(){return _2eU(_2f2.a,_2f2.b);});}}else{var _2f4=B(_2f3(_2f1));if(!_2f4._){return new T2(0,_4,_2f1);}else{return new F(function(){return _2eU(_2f4.a,_2f4.b);});}}}},_2f5=new T(function(){return B(unCStr("?"));}),_2f6=new T(function(){return B(_1za(_2f5));}),_2f7=new T(function(){return B(_G(_1z8,_2f6));}),_2f8=new T(function(){var _2f9=B(_1xU(_2f7));return new T3(0,_2f9.a,_2f9.b,_2f9.c);}),_2fa=new T2(0,_2f8,_4),_2fb=new T1(1,_2fa),_2fc=new T(function(){return B(_rr(_2eP,_4));}),_2fd=function(_2fe){var _2ff=E(_2fe);if(!_2ff._){var _2fg=E(_2fc);return (_2fg._==0)?__Z:new T1(1,_2fg.a);}else{if(E(_2ff.a)==63){var _2fh=B(_2fd(_2ff.b));if(!_2fh._){return E(_2fb);}else{var _2fi=E(_2fh.a),_2fj=new T(function(){var _2fk=B(_1xU(B(_G(_1z8,B(_1za(B(unAppCStr("?",new T(function(){var _2fl=E(_2fi.a);return B(_1Vi(_2fl.a,_2fl.b,_2fl.c));})))))))));return new T3(0,_2fk.a,_2fk.b,_2fk.c);});return new T1(1,new T2(0,_2fj,_2fi.b));}}else{var _2fm=B(_rr(_2eP,_2ff));return (_2fm._==0)?__Z:new T1(1,_2fm.a);}}},_2fn=function(_2fo){while(1){var _2fp=B((function(_2fq){var _2fr=E(_2fq);if(!_2fr._){return new T2(0,_4,_4);}else{var _2fs=_2fr.b,_2ft=function(_2fu){var _2fv=B(_2fd(_2fr));if(!_2fv._){return new T2(0,_4,_2fr);}else{var _2fw=_2fv.a,_2fx=new T(function(){var _2fy=B(_2fn(B(_1ZS(_2fw))));return new T2(0,_2fy.a,_2fy.b);});return new T2(0,new T2(1,new T(function(){return B(_1Mj(_2fw));}),new T(function(){return B(_1Mj(_2fx));})),new T(function(){return B(_1ZS(_2fx));}));}};switch(E(_2fr.a)){case 32:_2fo=_2fs;return __continue;case 40:_2fo=_2fs;return __continue;case 41:return new T2(0,_4,_2fs);case 45:var _2fz=E(_2fs);if(!_2fz._){return new F(function(){return _2ft(_);});}else{if(E(_2fz.a)==62){_2fo=_2fz.b;return __continue;}else{return new F(function(){return _2ft(_);});}}break;default:return new F(function(){return _2ft(_);});}}})(_2fo));if(_2fp!=__continue){return _2fp;}}},_2fA=new T(function(){return B(unCStr("?"));}),_2fB=function(_2fC){var _2fD=E(_2fC);if(!_2fD._){var _2fE=E(_2fD.b);if(!_2fE._){return E(_2fE.a);}else{return new F(function(){return _2eC(_2fA);});}}else{return E(_2fD.a);}},_2fF=new T(function(){return B(_1za(_2fA));}),_2fG=new T(function(){return B(_G(_1z8,_2fF));}),_2fH=new T(function(){var _2fI=B(_1xU(_2fG));return new T3(0,_2fI.a,_2fI.b,_2fI.c);}),_2fJ=new T2(0,_2fH,_4),_2fK=function(_2fL){var _2fM=E(_2fL);if(!_2fM._){var _2fN=_2fM.c,_2fO=new T(function(){var _2fP=E(_2fM.b);if(!_2fP._){if(!E(_2fP.b)._){return new T2(0,_2fP.a,new T(function(){return B(_G(_2fB,_2fN));}));}else{return E(_2fP);}}else{return E(_2fJ);}});return new T3(0,_2fM.a,_2fO,new T(function(){return B(_G(_2fK,_2fN));}));}else{return E(_2fM);}},_2fQ=function(_2fR,_2fS){var _2fT=E(_2fS);return (_2fT._==0)?__Z:new T2(1,_2fR,new T(function(){return B(_2fQ(_2fT.a,_2fT.b));}));},_2fU=new T(function(){return B(unCStr("last"));}),_2fV=new T(function(){return B(_ec(_2fU));}),_2fW=function(_2fX){var _2fY=E(_2fX);return new T2(0,new T1(1,_2fY.a),new T(function(){var _2fZ=E(_2fY.b);if(!_2fZ._){return __Z;}else{if(E(_2fZ.a)==125){return E(_2fZ.b);}else{return E(_2fZ);}}}));},_2f3=function(_2g0){var _2g1=E(_2g0);if(!_2g1._){var _2g2=__Z;}else{if(E(_2g1.a)==123){var _2g3=E(_2g1.b);}else{var _2g3=E(_2g1);}var _2g2=_2g3;}var _2g4=function(_2g5){var _2g6=B(_2fd(_2g2));if(!_2g6._){return __Z;}else{var _2g7=E(_2g6.a),_2g8=function(_2g9){var _2ga=new T(function(){var _2gb=E(E(_2g9).b);if(!_2gb._){var _2gc=B(_2eZ(_4));return new T2(0,_2gc.a,_2gc.b);}else{var _2gd=_2gb.b;switch(E(_2gb.a)){case 32:var _2ge=E(_2gd);if(!_2ge._){var _2gf=B(_2eZ(_4));return new T2(0,_2gf.a,_2gf.b);}else{if(E(_2ge.a)==123){var _2gg=B(_2eZ(_2ge.b));return new T2(0,_2gg.a,_2gg.b);}else{var _2gh=B(_2eZ(_2ge));return new T2(0,_2gh.a,_2gh.b);}}break;case 123:var _2gi=B(_2eZ(_2gd));return new T2(0,_2gi.a,_2gi.b);break;default:var _2gj=B(_2eZ(_2gb));return new T2(0,_2gj.a,_2gj.b);}}}),_2gk=new T(function(){return B(_2fK(new T3(0,_2g7.a,new T(function(){return B(_1Mj(_2g9));}),new T(function(){return B(_1Mj(_2ga));}))));});return new T2(1,new T2(0,_2gk,new T(function(){var _2gl=E(E(_2ga).b);if(!_2gl._){return __Z;}else{if(E(_2gl.a)==125){return E(_2gl.b);}else{return E(_2gl);}}})),_4);},_2gm=E(_2g7.b);if(!_2gm._){var _2gn=B(_2fn(_4)),_2go=E(_2gn.a);if(!_2go._){return __Z;}else{return new F(function(){return _2g8(new T2(0,new T2(0,new T(function(){return B(_2eQ(_2go,_2fV));}),new T(function(){return B(_2fQ(_2go.a,_2go.b));})),_2gn.b));});}}else{if(E(_2gm.a)==58){var _2gp=B(_2fn(_2gm.b)),_2gq=E(_2gp.a);if(!_2gq._){return __Z;}else{return new F(function(){return _2g8(new T2(0,new T2(0,new T(function(){return B(_2eQ(_2gq,_2fV));}),new T(function(){return B(_2fQ(_2gq.a,_2gq.b));})),_2gp.b));});}}else{var _2gr=B(_2fn(_2gm)),_2gs=E(_2gr.a);if(!_2gs._){return __Z;}else{return new F(function(){return _2g8(new T2(0,new T2(0,new T(function(){return B(_2eQ(_2gs,_2fV));}),new T(function(){return B(_2fQ(_2gs.a,_2gs.b));})),_2gr.b));});}}}}},_2gt=E(_2g2);if(!_2gt._){return new F(function(){return _2g4(_);});}else{if(E(_2gt.a)==63){return new F(function(){return _G(_2fW,B(_rr(_2eP,_2gt.b)));});}else{return new F(function(){return _2g4(_);});}}},_2gu=function(_2gv){var _2gw=E(_2gv);if(!_2gw._){return __Z;}else{var _2gx=E(_2gw.a),_2gy=function(_2gz){return E(new T2(3,_2gx.a,_sL));};return new F(function(){return _0(B(_rr(new T1(1,function(_2gA){return new F(function(){return A2(_By,_2gA,_2gy);});}),_2gx.b)),new T(function(){return B(_2gu(_2gw.b));},1));});}},_2gB=function(_2gC){var _2gD=B(_2gu(B(_2f3(_2gC))));return (_2gD._==0)?new T0(2):new T1(4,_2gD);},_2gE=new T1(1,_2gB),_2gF=new T(function(){return B(unCStr("{Pred:(Item->Quality->Comment) {This:(Kind->Item) {Pizza:Kind}} {Very:(Quality->Quality) {Italian:Quality}}}"));}),_2gG=new T(function(){return B(_rr(_2gE,_2gF));}),_2gH=new T(function(){var _2gI=B(_It(_2gG));if(!_2gI._){return E(_2dU);}else{if(!E(_2gI.b)._){return E(_2gI.a);}else{return E(_2dV);}}}),_2gJ=new T2(0,_2gH,_ML),_2gK=function(_2gL){var _2gM=E(_2gL);if(!_2gM._){return E(_2bd);}else{var _2gN=function(_){var _2gO=E(_2a5),_2gP=__app1(_2gO,toJSStr(E(_2d6)));return new T(function(){var _2gQ=function(_2gR){var _2gS=function(_){var _2gT=__app1(_2gO,toJSStr(E(_2d4))),_2gU=new T(function(){var _2gV=E(_2gR),_2gW=B(_1DK(_bP,_2gV.a,_2gV.b,_2gV.c)),_2gX=E(_2gW.a);return E(B(_1BJ(_2gX,(E(_2gW.b)-_2gX|0)+1|0,_2gW,_2dQ)).a);}),_2gY=function(_){var _2gZ=__app1(_2gO,toJSStr(B(unAppCStr("Loaded ",new T(function(){return B(_2dR(E(_2gU).b));}))))),_2h0=function(_){var _2h1=new T(function(){var _2h2=E(_2gU),_2h3=E(_2h2.b),_2h4=B(_1Dc(_2h2.a,_2h3.a,_2h3.b,_2h3.c,_2h2.c,_2h2.d));return new T3(0,_2h4.a,_2h4.b,_2h4.c);}),_2h5=new T(function(){return B(_2b8(_Lu,E(_2gU).d));}),_2h6=B(_24W(_2h1,_2h5,_2gJ)),_2h7=__app1(_2gO,toJSStr(B(_3X(_2cO,_2h6,_4)))),_2h8=__app1(E(_1E6),toJSStr(E(_2d3))),_2h9=__eq(_2h8,E(_D)),_2ha=function(_,_2hb){var _2hc=E(_2hb);if(!_2hc._){return new F(function(){return die(_2d1);});}else{var _2hd=function(_2he,_){while(1){var _2hf=B((function(_2hg,_){var _2hh=E(_2hg);if(!_2hh._){return _5;}else{var _2hi=E(_2hh.a),_2hj=_2hi.a,_2hk=B(A1(_2dc,_)),_2hl=E(_28N),_2hm=__app1(_2hl,toJSStr(E(_2d2))),_2hn=E(_2hk),_2ho=E(_1E1),_2hp=__app2(_2ho,_2hm,_2hn),_2hq=B(A(_2do,[_di,_df,_de,_2hn,_1DS,function(_2hr,_){return new F(function(){return _2a6(_2h1,_2h5,_2gJ,_2hj,_w8,_2hn,_2hr,_);});},_])),_2hs=E(_2hc.a),_2ht=__app2(_2ho,_2hn,_2hs),_2hu=B(A1(_2d9,_)),_2hv=__app1(_2hl,toJSStr(E(_2hi.b))),_2hw=E(_2hu),_2hx=__app2(_2ho,_2hv,_2hw),_2hy=B(A(_2do,[_di,_df,_de,_2hw,_1DS,function(_2hr,_){return new F(function(){return _2a6(_2h1,_2h5,_2gJ,_2hj,_w7,_2hw,_2hr,_);});},_])),_2hz=__app2(_2ho,_2hw,_2hs),_2hA=B(A1(_2cY,_)),_2hB=__app1(_2hl,toJSStr(B(_3X(_dY,_2hj,_4)))),_2hC=E(_2hA),_2hD=__app2(_2ho,_2hB,_2hC),_2hE=__app2(_2ho,_2hC,_2hs);_2he=_2hh.b;return __continue;}})(_2he,_));if(_2hf!=__continue){return _2hf;}}},_2hF=B(_2hd(_2h6,_));return _7q;}};if(!E(_2h9)){var _2hG=__isUndef(_2h8);if(!E(_2hG)){return new F(function(){return _2ha(_,new T1(1,_2h8));});}else{return new F(function(){return _2ha(_,_4l);});}}else{return new F(function(){return _2ha(_,_4l);});}};return new T1(0,_2h0);};return new T1(0,_2gY);};return new T1(0,_2gS);};return B(A3(_2aT,_2l,_2gM.a,_2gQ));});};return new T1(0,_2gN);}},_2hH=new T(function(){return toJSStr(E(_2d5));}),_2hI=new T(function(){return B(A(_7Y,[_2l,_N,_1b,_i,_h,_2hH,_2gK]));}),_2hJ=function(_){var _2hK=B(_c(_2hI,_4,_));return _5;},_2hL=function(_){return new F(function(){return _2hJ(_);});};
var hasteMain = function() {B(A(_2hL, [0]));};window.onload = hasteMain;