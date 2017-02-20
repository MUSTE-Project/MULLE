"use strict";
var __haste_prog_id = '6fc1b764e2ed3678fe80c0f0a46e39419ecd1fd781742131fc2d6a19ff5314c9';
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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=new T1(0,_),_i=new T(function(){return toJSStr(_4);}),_j=function(_k){return E(_i);},_l=function(_m,_){var _n=E(_m);if(!_n._){return _4;}else{var _o=B(_l(_n.b,_));return new T2(1,_5,_o);}},_p=function(_q,_){var _r=__arr2lst(0,_q);return new F(function(){return _l(_r,_);});},_s=function(_t,_){return new F(function(){return _p(E(_t),_);});},_u=function(_){return _5;},_v=function(_w,_){return new F(function(){return _u(_);});},_x=new T2(0,_v,_s),_y=function(_){return new F(function(){return __jsNull();});},_z=function(_A){var _B=B(A1(_A,_));return E(_B);},_C=new T(function(){return B(_z(_y));}),_D=new T(function(){return E(_C);}),_E=function(_F){return E(_D);},_G=function(_H,_I){var _J=E(_I);return (_J._==0)?__Z:new T2(1,new T(function(){return B(A1(_H,_J.a));}),new T(function(){return B(_G(_H,_J.b));}));},_K=function(_L){return new F(function(){return __lst2arr(B(_G(_E,_L)));});},_M=new T2(0,_E,_K),_N=new T4(0,_M,_x,_j,_j),_O="application/octet-stream",_P=function(_Q){return E(_O);},_R="blob",_S=function(_T){return E(_R);},_U=function(_V,_){var _W=E(_V);if(!_W._){return _4;}else{var _X=B(_U(_W.b,_));return new T2(1,_W.a,_X);}},_Y=function(_Z,_){var _10=__arr2lst(0,_Z);return new F(function(){return _U(_10,_);});},_11=function(_12,_){return new F(function(){return _Y(E(_12),_);});},_13=function(_14,_){return _14;},_15=new T2(0,_13,_11),_16=function(_17){return E(_17);},_18=function(_19){return new F(function(){return __lst2arr(B(_G(_16,_19)));});},_1a=new T2(0,_16,_18),_1b=new T4(0,_1a,_15,_P,_S),_1c=function(_1d,_1e,_1f){var _1g=function(_1h){var _1i=new T(function(){return B(A1(_1f,_1h));});return new F(function(){return A1(_1e,function(_1j){return E(_1i);});});};return new F(function(){return A1(_1d,_1g);});},_1k=function(_1l,_1m,_1n){var _1o=new T(function(){return B(A1(_1m,function(_1p){return new F(function(){return A1(_1n,_1p);});}));});return new F(function(){return A1(_1l,function(_1q){return E(_1o);});});},_1r=function(_1s,_1t,_1u){var _1v=function(_1w){var _1x=function(_1y){return new F(function(){return A1(_1u,new T(function(){return B(A1(_1w,_1y));}));});};return new F(function(){return A1(_1t,_1x);});};return new F(function(){return A1(_1s,_1v);});},_1z=function(_1A,_1B){return new F(function(){return A1(_1B,_1A);});},_1C=function(_1D,_1E,_1F){var _1G=new T(function(){return B(A1(_1F,_1D));});return new F(function(){return A1(_1E,function(_1H){return E(_1G);});});},_1I=function(_1J,_1K,_1L){var _1M=function(_1N){return new F(function(){return A1(_1L,new T(function(){return B(A1(_1J,_1N));}));});};return new F(function(){return A1(_1K,_1M);});},_1O=new T2(0,_1I,_1C),_1P=new T5(0,_1O,_1z,_1r,_1k,_1c),_1Q=function(_1R,_1S,_1T){return new F(function(){return A1(_1R,function(_1U){return new F(function(){return A2(_1S,_1U,_1T);});});});},_1V=function(_1W){return E(E(_1W).b);},_1X=function(_1Y,_1Z){return new F(function(){return A3(_1V,_20,_1Y,function(_21){return E(_1Z);});});},_22=function(_23){return new F(function(){return err(_23);});},_20=new T(function(){return new T5(0,_1P,_1Q,_1X,_1z,_22);}),_24=function(_25,_26,_){var _27=B(A1(_26,_));return new T(function(){return B(A1(_25,_27));});},_28=function(_29,_2a){return new T1(0,function(_){return new F(function(){return _24(_2a,_29,_);});});},_2b=new T2(0,_20,_28),_2c=function(_2d){return new T0(2);},_2e=function(_2f){var _2g=new T(function(){return B(A1(_2f,_2c));}),_2h=function(_2i){return new T1(1,new T2(1,new T(function(){return B(A1(_2i,_5));}),new T2(1,_2g,_4)));};return E(_2h);},_2j=function(_2k){return E(_2k);},_2l=new T3(0,_2b,_2j,_2e),_2m=function(_2n){return E(E(_2n).a);},_2o=function(_2p,_2q,_2r,_2s,_2t){var _2u=B(A2(_2m,_2p,E(_2t)));return new F(function(){return A2(_2q,_2r,new T2(1,_2u,E(_2s)));});},_2v=function(_2w){return E(E(_2w).a);},_2x=function(_2y){return E(E(_2y).a);},_2z=function(_2A){return E(E(_2A).a);},_2B=function(_2C){return E(E(_2C).b);},_2D=new T(function(){return B(unCStr("base"));}),_2E=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_2F=new T(function(){return B(unCStr("IOException"));}),_2G=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_2D,_2E,_2F),_2H=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_2G,_4,_4),_2I=function(_2J){return E(_2H);},_2K=function(_2L){return E(E(_2L).a);},_2M=function(_2N,_2O,_2P){var _2Q=B(A1(_2N,_)),_2R=B(A1(_2O,_)),_2S=hs_eqWord64(_2Q.a,_2R.a);if(!_2S){return __Z;}else{var _2T=hs_eqWord64(_2Q.b,_2R.b);return (!_2T)?__Z:new T1(1,_2P);}},_2U=function(_2V){var _2W=E(_2V);return new F(function(){return _2M(B(_2K(_2W.a)),_2I,_2W.b);});},_2X=new T(function(){return B(unCStr(": "));}),_2Y=new T(function(){return B(unCStr(")"));}),_2Z=new T(function(){return B(unCStr(" ("));}),_30=new T(function(){return B(unCStr("interrupted"));}),_31=new T(function(){return B(unCStr("system error"));}),_32=new T(function(){return B(unCStr("unsatisified constraints"));}),_33=new T(function(){return B(unCStr("user error"));}),_34=new T(function(){return B(unCStr("permission denied"));}),_35=new T(function(){return B(unCStr("illegal operation"));}),_36=new T(function(){return B(unCStr("end of file"));}),_37=new T(function(){return B(unCStr("resource exhausted"));}),_38=new T(function(){return B(unCStr("resource busy"));}),_39=new T(function(){return B(unCStr("does not exist"));}),_3a=new T(function(){return B(unCStr("already exists"));}),_3b=new T(function(){return B(unCStr("resource vanished"));}),_3c=new T(function(){return B(unCStr("timeout"));}),_3d=new T(function(){return B(unCStr("unsupported operation"));}),_3e=new T(function(){return B(unCStr("hardware fault"));}),_3f=new T(function(){return B(unCStr("inappropriate type"));}),_3g=new T(function(){return B(unCStr("invalid argument"));}),_3h=new T(function(){return B(unCStr("failed"));}),_3i=new T(function(){return B(unCStr("protocol error"));}),_3j=function(_3k,_3l){switch(E(_3k)){case 0:return new F(function(){return _0(_3a,_3l);});break;case 1:return new F(function(){return _0(_39,_3l);});break;case 2:return new F(function(){return _0(_38,_3l);});break;case 3:return new F(function(){return _0(_37,_3l);});break;case 4:return new F(function(){return _0(_36,_3l);});break;case 5:return new F(function(){return _0(_35,_3l);});break;case 6:return new F(function(){return _0(_34,_3l);});break;case 7:return new F(function(){return _0(_33,_3l);});break;case 8:return new F(function(){return _0(_32,_3l);});break;case 9:return new F(function(){return _0(_31,_3l);});break;case 10:return new F(function(){return _0(_3i,_3l);});break;case 11:return new F(function(){return _0(_3h,_3l);});break;case 12:return new F(function(){return _0(_3g,_3l);});break;case 13:return new F(function(){return _0(_3f,_3l);});break;case 14:return new F(function(){return _0(_3e,_3l);});break;case 15:return new F(function(){return _0(_3d,_3l);});break;case 16:return new F(function(){return _0(_3c,_3l);});break;case 17:return new F(function(){return _0(_3b,_3l);});break;default:return new F(function(){return _0(_30,_3l);});}},_3m=new T(function(){return B(unCStr("}"));}),_3n=new T(function(){return B(unCStr("{handle: "));}),_3o=function(_3p,_3q,_3r,_3s,_3t,_3u){var _3v=new T(function(){var _3w=new T(function(){var _3x=new T(function(){var _3y=E(_3s);if(!_3y._){return E(_3u);}else{var _3z=new T(function(){return B(_0(_3y,new T(function(){return B(_0(_2Y,_3u));},1)));},1);return B(_0(_2Z,_3z));}},1);return B(_3j(_3q,_3x));}),_3A=E(_3r);if(!_3A._){return E(_3w);}else{return B(_0(_3A,new T(function(){return B(_0(_2X,_3w));},1)));}}),_3B=E(_3t);if(!_3B._){var _3C=E(_3p);if(!_3C._){return E(_3v);}else{var _3D=E(_3C.a);if(!_3D._){var _3E=new T(function(){var _3F=new T(function(){return B(_0(_3m,new T(function(){return B(_0(_2X,_3v));},1)));},1);return B(_0(_3D.a,_3F));},1);return new F(function(){return _0(_3n,_3E);});}else{var _3G=new T(function(){var _3H=new T(function(){return B(_0(_3m,new T(function(){return B(_0(_2X,_3v));},1)));},1);return B(_0(_3D.a,_3H));},1);return new F(function(){return _0(_3n,_3G);});}}}else{return new F(function(){return _0(_3B.a,new T(function(){return B(_0(_2X,_3v));},1));});}},_3I=function(_3J){var _3K=E(_3J);return new F(function(){return _3o(_3K.a,_3K.b,_3K.c,_3K.d,_3K.f,_4);});},_3L=function(_3M,_3N,_3O){var _3P=E(_3N);return new F(function(){return _3o(_3P.a,_3P.b,_3P.c,_3P.d,_3P.f,_3O);});},_3Q=function(_3R,_3S){var _3T=E(_3R);return new F(function(){return _3o(_3T.a,_3T.b,_3T.c,_3T.d,_3T.f,_3S);});},_3U=44,_3V=93,_3W=91,_3X=function(_3Y,_3Z,_40){var _41=E(_3Z);if(!_41._){return new F(function(){return unAppCStr("[]",_40);});}else{var _42=new T(function(){var _43=new T(function(){var _44=function(_45){var _46=E(_45);if(!_46._){return E(new T2(1,_3V,_40));}else{var _47=new T(function(){return B(A2(_3Y,_46.a,new T(function(){return B(_44(_46.b));})));});return new T2(1,_3U,_47);}};return B(_44(_41.b));});return B(A2(_3Y,_41.a,_43));});return new T2(1,_3W,_42);}},_48=function(_49,_4a){return new F(function(){return _3X(_3Q,_49,_4a);});},_4b=new T3(0,_3L,_3I,_48),_4c=new T(function(){return new T5(0,_2I,_4b,_4d,_2U,_3I);}),_4d=function(_4e){return new T2(0,_4c,_4e);},_4f="status-text",_4g="status",_4h="http",_4i="network",_4j="type",_4k=__Z,_4l=__Z,_4m=7,_4n=function(_4o,_){var _4p=__get(_4o,E(_4j)),_4q=String(_4p),_4r=strEq(_4q,E(_4i));if(!E(_4r)){var _4s=strEq(_4q,E(_4h));if(!E(_4s)){var _4t=new T(function(){var _4u=new T(function(){return B(unAppCStr("unknown type of ajax error: ",new T(function(){return fromJSStr(_4q);})));});return B(_4d(new T6(0,_4l,_4m,_4,_4u,_4l,_4l)));});return new F(function(){return die(_4t);});}else{var _4v=__get(_4o,E(_4g)),_4w=__get(_4o,E(_4f));return new T2(1,new T(function(){var _4x=Number(_4v);return jsTrunc(_4x);}),new T(function(){return String(_4w);}));}}else{return _4k;}},_4y=function(_4z,_){var _4A=E(_4z);if(!_4A._){return _4;}else{var _4B=B(_4n(E(_4A.a),_)),_4C=B(_4y(_4A.b,_));return new T2(1,_4B,_4C);}},_4D=function(_4E,_){var _4F=__arr2lst(0,_4E);return new F(function(){return _4y(_4F,_);});},_4G=function(_4H,_){return new F(function(){return _4D(E(_4H),_);});},_4I=function(_4J,_){return new F(function(){return _4n(E(_4J),_);});},_4K=new T2(0,_4I,_4G),_4L=function(_4M){return E(E(_4M).a);},_4N=function(_4O,_4P,_){var _4Q=__eq(_4P,E(_D));if(!E(_4Q)){var _4R=__isUndef(_4P);if(!E(_4R)){var _4S=B(A3(_4L,_4O,_4P,_));return new T1(1,_4S);}else{return _4l;}}else{return _4l;}},_4T=function(_4U,_){return new F(function(){return _4N(_4K,E(_4U),_);});},_4V=function(_4W,_4X,_){var _4Y=__arr2lst(0,_4X),_4Z=function(_50,_){var _51=E(_50);if(!_51._){return _4;}else{var _52=_51.b,_53=E(_51.a),_54=__eq(_53,E(_D));if(!E(_54)){var _55=__isUndef(_53);if(!E(_55)){var _56=B(A3(_4L,_4W,_53,_)),_57=B(_4Z(_52,_));return new T2(1,new T1(1,_56),_57);}else{var _58=B(_4Z(_52,_));return new T2(1,_4l,_58);}}else{var _59=B(_4Z(_52,_));return new T2(1,_4l,_59);}}};return new F(function(){return _4Z(_4Y,_);});},_5a=function(_5b,_){return new F(function(){return _4V(_4K,E(_5b),_);});},_5c=new T2(0,_4T,_5a),_5d=2,_5e=function(_5f){return E(_5d);},_5g=function(_5h,_5i,_){var _5j=B(A2(_5h,new T(function(){var _5k=E(_5i),_5l=__eq(_5k,E(_D));if(!E(_5l)){var _5m=__isUndef(_5k);if(!E(_5m)){return new T1(1,_5k);}else{return __Z;}}else{return __Z;}}),_));return _D;},_5n=new T2(0,_5g,_5e),_5o=function(_5p){return E(E(_5p).a);},_5q=function(_5r,_5s,_5t,_5u){var _5v=new T(function(){return B(A1(_5t,new T(function(){var _5w=B(A3(_4L,_5r,_5u,_));return E(_5w);})));});return new F(function(){return A2(_5o,_5s,_5v);});},_5x=function(_5y){return E(E(_5y).b);},_5z=new T(function(){return B(unCStr("Prelude.undefined"));}),_5A=new T(function(){return B(err(_5z));}),_5B=function(_5C,_5D,_5E){var _5F=__createJSFunc(1+B(A2(_5x,_5D,new T(function(){return B(A1(_5E,_5A));})))|0,function(_5G){return new F(function(){return _5q(_5C,_5D,_5E,_5G);});});return E(_5F);},_5H=function(_5I){return new F(function(){return _5B(_5c,_5n,_5I);});},_5J=function(_5K,_5L,_5M){return new F(function(){return _5B(_5K,_5L,_5M);});},_5N=function(_5O,_5P,_5Q){var _5R=__lst2arr(B(_G(function(_5S){return new F(function(){return _5J(_5O,_5P,_5S);});},_5Q)));return E(_5R);},_5T=function(_5U){return new F(function(){return _5N(_5c,_5n,_5U);});},_5V=new T2(0,_5H,_5T),_5W=function(_5X,_5Y,_5Z,_){var _60=__apply(_5Y,E(_5Z));return new F(function(){return A3(_4L,_5X,_60,_);});},_61=function(_62,_63,_64,_){return new F(function(){return _5W(_62,E(_63),_64,_);});},_65=function(_66,_67,_68,_){return new F(function(){return _61(_66,_67,_68,_);});},_69=function(_6a,_6b,_){return new F(function(){return _65(_x,_6a,_6b,_);});},_6c=function(_6d){return E(E(_6d).c);},_6e=0,_6f=new T(function(){return eval("(function(method, uri, mimeout, responseType, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, uri);xhr.responseType = responseType;if(mimeout != \'\') {xhr.setRequestHeader(\'Content-type\', mimeout);}xhr.addEventListener(\'load\', function() {if(xhr.status < 400) {cb(null, xhr.response);}else {cb({\'type\':\'http\', \'status\':xhr.status, \'status-text\': xhr.statusText}, null);}});xhr.addEventListener(\'error\', function() {if(xhr.status != 0) {cb({\'type\':\'http\', \'status\':xhr.status, \'status-text\': xhr.statusText}, null);} else {cb({\'type\':\'network\'}, null);}});xhr.send(postdata);})");}),_6g=function(_6h){return E(E(_6h).b);},_6i=function(_6j){return E(E(_6j).b);},_6k=new T(function(){return B(unCStr("base"));}),_6l=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6m=new T(function(){return B(unCStr("PatternMatchFail"));}),_6n=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6k,_6l,_6m),_6o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6n,_4,_4),_6p=function(_6q){return E(_6o);},_6r=function(_6s){var _6t=E(_6s);return new F(function(){return _2M(B(_2K(_6t.a)),_6p,_6t.b);});},_6u=function(_6v){return E(E(_6v).a);},_6w=function(_6x){return new T2(0,_6y,_6x);},_6z=function(_6A,_6B){return new F(function(){return _0(E(_6A).a,_6B);});},_6C=function(_6D,_6E){return new F(function(){return _3X(_6z,_6D,_6E);});},_6F=function(_6G,_6H,_6I){return new F(function(){return _0(E(_6H).a,_6I);});},_6J=new T3(0,_6F,_6u,_6C),_6y=new T(function(){return new T5(0,_6p,_6J,_6w,_6r,_6u);}),_6K=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_6L=function(_6M){return E(E(_6M).c);},_6N=function(_6O,_6P){return new F(function(){return die(new T(function(){return B(A2(_6L,_6P,_6O));}));});},_6Q=function(_6R,_6S){return new F(function(){return _6N(_6R,_6S);});},_6T=function(_6U,_6V){var _6W=E(_6V);if(!_6W._){return new T2(0,_4,_4);}else{var _6X=_6W.a;if(!B(A1(_6U,_6X))){return new T2(0,_4,_6W);}else{var _6Y=new T(function(){var _6Z=B(_6T(_6U,_6W.b));return new T2(0,_6Z.a,_6Z.b);});return new T2(0,new T2(1,_6X,new T(function(){return E(E(_6Y).a);})),new T(function(){return E(E(_6Y).b);}));}}},_70=32,_71=new T(function(){return B(unCStr("\n"));}),_72=function(_73){return (E(_73)==124)?false:true;},_74=function(_75,_76){var _77=B(_6T(_72,B(unCStr(_75)))),_78=_77.a,_79=function(_7a,_7b){var _7c=new T(function(){var _7d=new T(function(){return B(_0(_76,new T(function(){return B(_0(_7b,_71));},1)));});return B(unAppCStr(": ",_7d));},1);return new F(function(){return _0(_7a,_7c);});},_7e=E(_77.b);if(!_7e._){return new F(function(){return _79(_78,_4);});}else{if(E(_7e.a)==124){return new F(function(){return _79(_78,new T2(1,_70,_7e.b));});}else{return new F(function(){return _79(_78,_4);});}}},_7f=function(_7g){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_7g,_6K));})),_6y);});},_7h=new T(function(){return B(_7f("src/Haste/Ajax.hs:(61,7)-(63,60)|case"));}),_7i="PUT",_7j="POST",_7k="DELETE",_7l="GET",_7m=function(_7n){return E(E(_7n).c);},_7o=new T1(1,_4),_7p=function(_){return new F(function(){return nMV(_7o);});},_7q=new T0(2),_7r=function(_7s,_7t,_7u){var _7v=function(_7w){var _7x=function(_){var _7y=E(_7t),_7z=rMV(_7y),_7A=E(_7z);if(!_7A._){var _7B=new T(function(){var _7C=new T(function(){return B(A1(_7w,_5));});return B(_0(_7A.b,new T2(1,new T2(0,_7u,function(_7D){return E(_7C);}),_4)));}),_=wMV(_7y,new T2(0,_7A.a,_7B));return _7q;}else{var _7E=E(_7A.a);if(!_7E._){var _=wMV(_7y,new T2(0,_7u,_4));return new T(function(){return B(A1(_7w,_5));});}else{var _=wMV(_7y,new T1(1,_7E.b));return new T1(1,new T2(1,new T(function(){return B(A1(_7w,_5));}),new T2(1,new T(function(){return B(A2(_7E.a,_7u,_2c));}),_4)));}}};return new T1(0,_7x);};return new F(function(){return A2(_6g,_7s,_7v);});},_7F=function(_7G){return E(E(_7G).d);},_7H=function(_7I,_7J){var _7K=function(_7L){var _7M=function(_){var _7N=E(_7J),_7O=rMV(_7N),_7P=E(_7O);if(!_7P._){var _7Q=_7P.a,_7R=E(_7P.b);if(!_7R._){var _=wMV(_7N,_7o);return new T(function(){return B(A1(_7L,_7Q));});}else{var _7S=E(_7R.a),_=wMV(_7N,new T2(0,_7S.a,_7R.b));return new T1(1,new T2(1,new T(function(){return B(A1(_7L,_7Q));}),new T2(1,new T(function(){return B(A1(_7S.b,_2c));}),_4)));}}else{var _7T=new T(function(){var _7U=function(_7V){var _7W=new T(function(){return B(A1(_7L,_7V));});return function(_7X){return E(_7W);};};return B(_0(_7P.a,new T2(1,_7U,_4)));}),_=wMV(_7N,new T1(1,_7T));return _7q;}};return new T1(0,_7M);};return new F(function(){return A2(_6g,_7I,_7K);});},_7Y=function(_7Z,_80,_81,_82,_83,_84){var _85=B(_2x(_7Z)),_86=new T(function(){return B(_6g(_7Z));}),_87=new T(function(){return B(_6i(_85));}),_88=B(_2z(_85)),_89=new T(function(){return B(_2B(_81));}),_8a=new T(function(){var _8b=function(_8c){var _8d=E(_84),_8e=E(_82),_8f=strEq(E(_i),_8e);if(!E(_8f)){var _8g=E(_8e);}else{var _8g=B(A2(_7m,_80,_6e));}var _8h=B(A2(_7F,_81,_6e)),_8i=E(_D);return function(_5G){return new F(function(){return _2o(_5V,_69,_6f,new T2(1,_8i,new T2(1,_8h,new T2(1,_8g,new T2(1,_8d,new T2(1,_8c,_4))))),_5G);});};},_8j=function(_8k,_8l){var _8m=E(_84),_8n=E(_82),_8o=strEq(E(_i),_8n);if(!E(_8o)){var _8p=E(_8n);}else{var _8p=B(A2(_7m,_80,_6e));}var _8q=B(A2(_7F,_81,_6e)),_8r=E(_8k);return function(_5G){return new F(function(){return _2o(_5V,_69,_6f,new T2(1,_8r,new T2(1,_8q,new T2(1,_8p,new T2(1,_8m,new T2(1,_8l,_4))))),_5G);});};},_8s=E(_83);switch(_8s._){case 0:return B(_8b(E(_7l)));break;case 1:return B(_8b(E(_7k)));break;case 2:return B(_8j(new T(function(){return B(A2(_2m,B(_2v(_80)),_8s.a));}),E(_7j)));break;default:return B(_8j(new T(function(){return B(A2(_2m,B(_2v(_80)),_8s.a));}),E(_7i)));}}),_8t=function(_8u){var _8v=new T(function(){return B(A1(_86,new T(function(){return B(_7H(_2l,_8u));})));}),_8w=new T(function(){var _8x=new T(function(){var _8y=function(_8z,_8A,_){var _8B=E(_8A);if(!_8B._){var _8C=E(_8z);if(!_8C._){return E(_7h);}else{return new F(function(){return _c(new T(function(){return B(A(_7r,[_2l,_8u,new T1(0,_8C.a),_2c]));}),_4,_);});}}else{var _8D=B(A3(_4L,_89,_8B.a,_));return new F(function(){return _c(new T(function(){return B(A(_7r,[_2l,_8u,new T1(1,_8D),_2c]));}),_4,_);});}};return B(A1(_8a,_8y));});return B(A1(_87,_8x));});return new F(function(){return A3(_6c,_88,_8w,_8v);});};return new F(function(){return A3(_1V,_88,new T(function(){return B(A2(_6i,_85,_7p));}),_8t);});},_8E="w8",_8F=function(_8G){return E(_8E);},_8H=function(_8I,_8J){var _8K=E(_8J);return new T2(0,_8K.a,_8K.b);},_8L=function(_8M,_8N){return E(_8N).c;},_8O=function(_8P){var _8Q=B(A1(_8P,_));return E(_8Q);},_8R=function(_8S,_8T,_8U,_8V){var _8W=function(_){var _8X=E(_8U),_8Y=_8X.d,_8Z=_8Y["byteLength"],_90=newByteArr(_8Z),_91=_90,_92=memcpy(_91,_8Y,_8Z>>>0),_93=function(_94,_){while(1){var _95=E(_94);if(!_95._){return _5;}else{var _96=E(_95.a),_97=E(_96.a),_98=_91["v"]["w8"][_97],_=_91["v"]["w8"][_97]=B(A2(_8T,_98,_96.b));_94=_95.b;continue;}}},_99=B(_93(_8V,_));return new T4(0,E(_8X.a),E(_8X.b),_8X.c,_91);};return new F(function(){return _8O(_8W);});},_9a=function(_9b){return E(E(_9b).f);},_9c=new T(function(){return B(unCStr("Negative range size"));}),_9d=new T(function(){return B(err(_9c));}),_9e=function(_9f,_9g,_9h,_9i,_9j){var _9k=E(_9i),_9l=function(_){var _9m=B(A2(_9a,_9f,_9k)),_9n=newByteArr(_9m),_9o=_9n;if(_9m>=0){var _9p=_9m-1|0,_9q=function(_){var _9r=function(_9s,_){while(1){var _9t=E(_9s);if(!_9t._){return _5;}else{var _9u=E(_9t.a),_9v=E(_9u.a),_9w=_9o["v"]["w8"][_9v],_=_9o["v"]["w8"][_9v]=B(A2(_9g,_9w,_9u.b));_9s=_9t.b;continue;}}},_9x=B(_9r(_9j,_));return new T4(0,E(_9k.a),E(_9k.b),_9m,_9o);};if(0<=_9p){var _9y=function(_9z,_){while(1){var _=_9o["v"]["w8"][_9z]=E(_9h);if(_9z!=_9p){var _9A=_9z+1|0;_9z=_9A;continue;}else{return _5;}}},_9B=B(_9y(0,_));return new F(function(){return _9q(_);});}else{return new F(function(){return _9q(_);});}}else{return E(_9d);}},_9C=E(_9l);return new F(function(){return _8O(_9C);});},_9D=function(_9E,_9F,_9G){var _9H=E(_9F),_9I=function(_){var _9J=B(A2(_9a,_9E,_9H)),_9K=newByteArr(_9J),_9L=_9K;if(_9J>=0){var _9M=_9J-1|0,_9N=function(_){var _9O=function(_9P,_){while(1){var _9Q=E(_9P);if(!_9Q._){return _5;}else{var _9R=E(_9Q.a),_=_9L["v"]["w8"][E(_9R.a)]=E(_9R.b);_9P=_9Q.b;continue;}}},_9S=B(_9O(_9G,_));return new T4(0,E(_9H.a),E(_9H.b),_9J,_9L);};if(0<=_9M){var _9T=function(_9U,_){while(1){var _=_9L["v"]["w8"][_9U]=0;if(_9U!=_9M){var _9V=_9U+1|0;_9U=_9V;continue;}else{return _5;}}},_9W=B(_9T(0,_));return new F(function(){return _9N(_);});}else{return new F(function(){return _9N(_);});}}else{return E(_9d);}},_9X=E(_9I);return new F(function(){return _8O(_9X);});},_9Y=function(_9Z,_a0,_a1){return E(_a0).d["v"]["w8"][E(_a1)];},_a2=function(_a3,_a4,_a5){var _a6=function(_){var _a7=E(_a4),_a8=_a7.d,_a9=_a8["byteLength"],_aa=newByteArr(_a9),_ab=_aa,_ac=memcpy(_ab,_a8,_a9>>>0),_ad=function(_ae,_){while(1){var _af=E(_ae);if(!_af._){return _5;}else{var _ag=E(_af.a),_=_ab["v"]["w8"][E(_ag.a)]=E(_ag.b);_ae=_af.b;continue;}}},_ah=B(_ad(_a5,_));return new T4(0,E(_a7.a),E(_a7.b),_a7.c,_ab);};return new F(function(){return _8O(_a6);});},_ai={_:0,a:_8H,b:_8L,c:_9D,d:_9Y,e:_a2,f:_8R,g:_9e},_aj=function(_ak,_al,_){var _am=E(_al);return new T2(0,_am.a,_am.b);},_an=function(_ao,_ap,_){return new F(function(){return _aj(_ao,_ap,_);});},_aq=function(_ar,_as,_){return E(_as).c;},_at=function(_ao,_ap,_){return new F(function(){return _aq(_ao,_ap,_);});},_au=new T(function(){return B(unCStr("Negative range size"));}),_av=new T(function(){return B(err(_au));}),_aw=function(_ax,_ay,_az,_aA,_){var _aB=B(A2(_9a,_ax,new T2(0,_ay,_az))),_aC=newByteArr(_aB);if(_aB>=0){var _aD=_aB-1|0,_aE=new T(function(){return new T4(0,E(_ay),E(_az),_aB,_aC);});if(0<=_aD){var _aF=function(_aG,_){while(1){var _=E(_aE).d["v"]["w8"][_aG]=E(_aA);if(_aG!=_aD){var _aH=_aG+1|0;_aG=_aH;continue;}else{return _5;}}},_aI=B(_aF(0,_));return _aE;}else{return _aE;}}else{return E(_av);}},_aJ=function(_aK,_aL,_aM,_){var _aN=E(_aL);return new F(function(){return _aw(_aK,_aN.a,_aN.b,_aM,_);});},_aO=function(_aP,_ao,_ap,_){return new F(function(){return _aJ(_aP,_ao,_ap,_);});},_aQ=function(_aR,_aS,_aT,_){var _aU=B(A2(_9a,_aR,new T2(0,_aS,_aT))),_aV=newByteArr(_aU);return new T(function(){return new T4(0,E(_aS),E(_aT),_aU,_aV);});},_aW=function(_aX,_aY,_){var _aZ=E(_aY);return new F(function(){return _aQ(_aX,_aZ.a,_aZ.b,_);});},_b0=function(_ao,_ap,_){return new F(function(){return _aW(_ao,_ap,_);});},_b1=function(_b2,_b3,_b4,_){return E(_b3).d["v"]["w8"][E(_b4)];},_b5=function(_aP,_ao,_ap,_){return new F(function(){return _b1(_aP,_ao,_ap,_);});},_b6=function(_b7,_b8,_b9,_ba,_){var _=E(_b8).d["v"]["w8"][E(_b9)]=E(_ba);return _5;},_bb=function(_bc,_aP,_ao,_ap,_){return new F(function(){return _b6(_bc,_aP,_ao,_ap,_);});},_bd=function(_be,_bf,_){var _bg=B(A1(_be,_)),_bh=B(A1(_bf,_));return _bg;},_bi=function(_bj,_bk,_){var _bl=B(A1(_bj,_)),_bm=B(A1(_bk,_));return new T(function(){return B(A1(_bl,_bm));});},_bn=function(_bo,_bp,_){var _bq=B(A1(_bp,_));return _bo;},_br=new T2(0,_24,_bn),_bs=function(_bt,_){return _bt;},_bu=function(_bv,_bw,_){var _bx=B(A1(_bv,_));return new F(function(){return A1(_bw,_);});},_by=new T5(0,_br,_bs,_bi,_bu,_bd),_bz=new T(function(){return E(_4c);}),_bA=function(_bB){return new T6(0,_4l,_4m,_4,_bB,_4l,_4l);},_bC=function(_bD,_){var _bE=new T(function(){return B(A2(_6L,_bz,new T(function(){return B(A1(_bA,_bD));})));});return new F(function(){return die(_bE);});},_bF=function(_bG,_){return new F(function(){return _bC(_bG,_);});},_bH=function(_bI){return new F(function(){return A1(_bF,_bI);});},_bJ=function(_bK,_bL,_){var _bM=B(A1(_bK,_));return new F(function(){return A2(_bL,_bM,_);});},_bN=new T5(0,_by,_bJ,_bu,_bs,_bH),_bO={_:0,a:_bN,b:_an,c:_at,d:_aO,e:_b0,f:_b0,g:_b5,h:_bb},_bP=new T3(0,_ai,_bO,_8F),_bQ=new T(function(){return B(unCStr("NoMethodError"));}),_bR=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_6k,_6l,_bQ),_bS=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_bR,_4,_4),_bT=function(_bU){return E(_bS);},_bV=function(_bW){var _bX=E(_bW);return new F(function(){return _2M(B(_2K(_bX.a)),_bT,_bX.b);});},_bY=function(_bZ){return E(E(_bZ).a);},_c0=function(_6x){return new T2(0,_c1,_6x);},_c2=function(_c3,_c4){return new F(function(){return _0(E(_c3).a,_c4);});},_c5=function(_c6,_c7){return new F(function(){return _3X(_c2,_c6,_c7);});},_c8=function(_c9,_ca,_cb){return new F(function(){return _0(E(_ca).a,_cb);});},_cc=new T3(0,_c8,_bY,_c5),_c1=new T(function(){return new T5(0,_bT,_cc,_c0,_bV,_bY);}),_cd=new T(function(){return B(unCStr("No instance nor default method for class operation"));}),_ce=function(_cf){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_cf,_cd));})),_c1);});},_cg=new T(function(){return B(_ce("Data/Binary/Put.hs:17:10-19|>>="));}),_ch=function(_ci){return E(_cg);},_cj=function(_ck,_cl){var _cm=jsShowI(_ck);return new F(function(){return _0(fromJSStr(_cm),_cl);});},_cn=41,_co=40,_cp=function(_cq,_cr,_cs){if(_cr>=0){return new F(function(){return _cj(_cr,_cs);});}else{if(_cq<=6){return new F(function(){return _cj(_cr,_cs);});}else{return new T2(1,_co,new T(function(){var _ct=jsShowI(_cr);return B(_0(fromJSStr(_ct),new T2(1,_cn,_cs)));}));}}},_cu=new T(function(){return B(unCStr(")"));}),_cv=function(_cw,_cx){var _cy=new T(function(){var _cz=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_cp(0,_cx,_4)),_cu));})));},1);return B(_0(B(_cp(0,_cw,_4)),_cz));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_cy)));});},_cA=function(_cB){return new F(function(){return _cp(0,E(_cB),_4);});},_cC=function(_cD,_cE,_cF){return new F(function(){return _cp(E(_cD),E(_cE),_cF);});},_cG=function(_cH,_cI){return new F(function(){return _cp(0,E(_cH),_cI);});},_cJ=function(_cK,_cL){return new F(function(){return _3X(_cG,_cK,_cL);});},_cM=new T3(0,_cC,_cA,_cJ),_cN=0,_cO=function(_cP,_cQ,_cR){return new F(function(){return A1(_cP,new T2(1,_3U,new T(function(){return B(A1(_cQ,_cR));})));});},_cS=new T(function(){return B(unCStr(": empty list"));}),_cT=new T(function(){return B(unCStr("Prelude."));}),_cU=function(_cV){return new F(function(){return err(B(_0(_cT,new T(function(){return B(_0(_cV,_cS));},1))));});},_cW=new T(function(){return B(unCStr("foldr1"));}),_cX=new T(function(){return B(_cU(_cW));}),_cY=function(_cZ,_d0){var _d1=E(_d0);if(!_d1._){return E(_cX);}else{var _d2=_d1.a,_d3=E(_d1.b);if(!_d3._){return E(_d2);}else{return new F(function(){return A2(_cZ,_d2,new T(function(){return B(_cY(_cZ,_d3));}));});}}},_d4=new T(function(){return B(unCStr(" out of range "));}),_d5=new T(function(){return B(unCStr("}.index: Index "));}),_d6=new T(function(){return B(unCStr("Ix{"));}),_d7=new T2(1,_cn,_4),_d8=new T2(1,_cn,_d7),_d9=0,_da=function(_db){return E(E(_db).a);},_dc=function(_dd,_de,_df,_dg,_dh){var _di=new T(function(){var _dj=new T(function(){var _dk=new T(function(){var _dl=new T(function(){var _dm=new T(function(){return B(A3(_cY,_cO,new T2(1,new T(function(){return B(A3(_da,_df,_d9,_dg));}),new T2(1,new T(function(){return B(A3(_da,_df,_d9,_dh));}),_4)),_d8));});return B(_0(_d4,new T2(1,_co,new T2(1,_co,_dm))));});return B(A(_da,[_df,_cN,_de,new T2(1,_cn,_dl)]));});return B(_0(_d5,new T2(1,_co,_dk)));},1);return B(_0(_dd,_dj));},1);return new F(function(){return err(B(_0(_d6,_di)));});},_dn=function(_do,_dp,_dq,_dr,_ds){return new F(function(){return _dc(_do,_dp,_ds,_dq,_dr);});},_dt=function(_du,_dv,_dw,_dx){var _dy=E(_dw);return new F(function(){return _dn(_du,_dv,_dy.a,_dy.b,_dx);});},_dz=function(_dA,_dB,_dC,_dD){return new F(function(){return _dt(_dD,_dC,_dB,_dA);});},_dE=new T(function(){return B(unCStr("Int"));}),_dF=function(_dG,_dH,_dI){return new F(function(){return _dz(_cM,new T2(0,_dH,_dI),_dG,_dE);});},_dJ=function(_dK,_dL,_dM,_dN,_dO,_dP){var _dQ=_dK+_dP|0;if(_dL>_dQ){return new F(function(){return _dF(_dQ,_dL,_dM);});}else{if(_dQ>_dM){return new F(function(){return _dF(_dQ,_dL,_dM);});}else{var _dR=_dQ-_dL|0;if(0>_dR){return new F(function(){return _cv(_dR,_dN);});}else{if(_dR>=_dN){return new F(function(){return _cv(_dR,_dN);});}else{return _dO["v"]["w8"][_dR];}}}}},_dS=function(_dT){return new F(function(){return err(B(unAppCStr("getWord8: no bytes left at ",new T(function(){return B(_cp(0,_dT,_4));}))));});},_dU=function(_dV,_dW,_dX,_dY){if(_dY>=_dW){return new F(function(){return _dS(_dY);});}else{return new T2(0,new T(function(){var _dZ=E(_dX);return B(_dJ(_dV,E(_dZ.a),E(_dZ.b),_dZ.c,_dZ.d,_dY));}),_dY+1|0);}},_e0=function(_e1,_e2,_e3,_e4){var _e5=B(_dU(_e1,_e2,_e3,_e4)),_e6=_e5.b,_e7=E(_e5.a);if(_e7>127){var _e8=B(_e0(_e1,_e2,_e3,E(_e6)));return new T2(0,new T(function(){return (E(_e8.a)<<7>>>0|(_e7&127)>>>0)>>>0;}),_e8.b);}else{return new T2(0,_e7,_e6);}},_e9=new T(function(){return B(unCStr("too few bytes"));}),_ea=new T(function(){return B(err(_e9));}),_eb=function(_ec,_ed,_ee,_ef){var _eg=B(_e0(_ec,_ed,_ee,_ef)),_eh=E(_eg.b),_ei=E(_eg.a)&4294967295;return ((_eh+_ei|0)<=_ed)?new T2(0,new T(function(){var _ej=_ed-_eh|0;if(_ei>_ej){return new T3(0,_ec+_eh|0,_ej,_ee);}else{return new T3(0,_ec+_eh|0,_ei,_ee);}}),_eh+_ei|0):E(_ea);},_ek=function(_el,_em){var _en=E(_el),_eo=B(_eb(_en.a,_en.b,_en.c,E(_em)));return new T2(0,_eo.a,_eo.b);},_ep=new T2(0,_ch,_ek),_eq=function(_er){return E(_cg);},_es=function(_et){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_cp(9,_et,_4));}))));});},_eu=function(_ev,_ew,_ex,_ey){var _ez=B(_dU(_ev,_ew,_ex,_ey)),_eA=_ez.b,_eB=E(_ez.a)&4294967295;if(_eB>=128){if(_eB>=224){if(_eB>=240){var _eC=B(_dU(_ev,_ew,_ex,E(_eA))),_eD=B(_dU(_ev,_ew,_ex,E(_eC.b))),_eE=B(_dU(_ev,_ew,_ex,E(_eD.b))),_eF=128^E(_eE.a)&4294967295|(128^E(_eD.a)&4294967295|(128^E(_eC.a)&4294967295|(240^_eB)<<6)<<6)<<6;if(_eF>>>0>1114111){return new F(function(){return _es(_eF);});}else{return new T2(0,_eF,_eE.b);}}else{var _eG=B(_dU(_ev,_ew,_ex,E(_eA))),_eH=B(_dU(_ev,_ew,_ex,E(_eG.b))),_eI=128^E(_eH.a)&4294967295|(128^E(_eG.a)&4294967295|(224^_eB)<<6)<<6;if(_eI>>>0>1114111){return new F(function(){return _es(_eI);});}else{return new T2(0,_eI,_eH.b);}}}else{var _eJ=B(_dU(_ev,_ew,_ex,E(_eA))),_eK=128^E(_eJ.a)&4294967295|(192^_eB)<<6;if(_eK>>>0>1114111){return new F(function(){return _es(_eK);});}else{return new T2(0,_eK,_eJ.b);}}}else{if(_eB>>>0>1114111){return new F(function(){return _es(_eB);});}else{return new T2(0,_eB,_eA);}}},_eL=function(_eM,_eN){var _eO=E(_eM),_eP=B(_eu(_eO.a,_eO.b,_eO.c,E(_eN)));return new T2(0,_eP.a,_eP.b);},_eQ=function(_eR,_eS,_eT){var _eU=E(_eR);if(!_eU._){return new T2(0,_4,_eT);}else{var _eV=new T(function(){return B(A2(_eU.a,_eS,_eT));}),_eW=B(_eQ(_eU.b,_eS,new T(function(){return E(E(_eV).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_eV).a);}),_eW.a),_eW.b);}},_eX=function(_eY,_eZ,_f0,_f1){if(0>=_eY){return new F(function(){return _eQ(_4,_f0,_f1);});}else{var _f2=function(_f3){var _f4=E(_f3);return (_f4==1)?E(new T2(1,_eZ,_4)):new T2(1,_eZ,new T(function(){return B(_f2(_f4-1|0));}));};return new F(function(){return _eQ(B(_f2(_eY)),_f0,_f1);});}},_f5=function(_f6,_f7,_f8,_f9){var _fa=B(_e0(_f6,_f7,_f8,_f9));return new F(function(){return _eX(E(_fa.a)&4294967295,_eL,new T3(0,_f6,_f7,_f8),_fa.b);});},_fb=function(_fc,_fd){var _fe=E(_fc),_ff=B(_f5(_fe.a,_fe.b,_fe.c,E(_fd)));return new T2(0,_ff.a,_ff.b);},_fg=new T2(0,_eq,_fb),_fh=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_fi=new T(function(){return B(err(_fh));}),_fj=function(_fk,_fl,_fm){var _fn=function(_){var _fo=E(_fl),_fp=_fo.c,_fq=newArr(_fp,_fi),_fr=_fq,_fs=function(_ft,_){while(1){if(_ft!=_fp){var _=_fr[_ft]=_fo.d[_ft],_fu=_ft+1|0;_ft=_fu;continue;}else{return E(_);}}},_=B(_fs(0,_)),_fv=function(_fw,_){while(1){var _fx=E(_fw);if(!_fx._){return new T4(0,E(_fo.a),E(_fo.b),_fp,_fr);}else{var _fy=E(_fx.a),_=_fr[E(_fy.a)]=_fy.b;_fw=_fx.b;continue;}}};return new F(function(){return _fv(_fm,_);});};return new F(function(){return _8O(_fn);});},_fz=function(_fA,_fB,_fC){return new F(function(){return _fj(_fA,_fB,_fC);});},_fD=function(_fE,_fF,_fG){return E(E(_fF).d[E(_fG)]);},_fH=function(_fI,_fJ,_fK){return new F(function(){return _fD(_fI,_fJ,_fK);});},_fL=function(_fM,_fN,_fO){var _fP=E(_fN),_fQ=B(A2(_9a,_fM,_fP)),_fR=function(_){var _fS=newArr(_fQ,_fi),_fT=_fS,_fU=function(_fV,_){while(1){var _fW=B((function(_fX,_){var _fY=E(_fX);if(!_fY._){return new T(function(){return new T4(0,E(_fP.a),E(_fP.b),_fQ,_fT);});}else{var _fZ=E(_fY.a),_=_fT[E(_fZ.a)]=_fZ.b;_fV=_fY.b;return __continue;}})(_fV,_));if(_fW!=__continue){return _fW;}}};return new F(function(){return _fU(_fO,_);});};return new F(function(){return _8O(_fR);});},_g0=function(_g1,_g2,_g3){return new F(function(){return _fL(_g1,_g2,_g3);});},_g4=function(_g5,_g6){return E(_g6).c;},_g7=function(_g8,_g9){return new F(function(){return _g4(_g8,_g9);});},_ga=function(_gb,_gc){var _gd=E(_gc);return new T2(0,_gd.a,_gd.b);},_ge=function(_gf,_gg){return new F(function(){return _ga(_gf,_gg);});},_gh=function(_gi,_gj,_gk,_gl){var _gm=function(_){var _gn=E(_gk),_go=_gn.c,_gp=newArr(_go,_fi),_gq=_gp,_gr=function(_gs,_){while(1){if(_gs!=_go){var _=_gq[_gs]=_gn.d[_gs],_gt=_gs+1|0;_gs=_gt;continue;}else{return E(_);}}},_=B(_gr(0,_)),_gu=function(_gv,_){while(1){var _gw=B((function(_gx,_){var _gy=E(_gx);if(!_gy._){return new T4(0,E(_gn.a),E(_gn.b),_go,_gq);}else{var _gz=E(_gy.a),_gA=E(_gz.a),_gB=_gq[_gA],_=_gq[_gA]=new T(function(){return B(A2(_gj,_gB,_gz.b));});_gv=_gy.b;return __continue;}})(_gv,_));if(_gw!=__continue){return _gw;}}};return new F(function(){return _gu(_gl,_);});};return new F(function(){return _8O(_gm);});},_gC=function(_gD,_gE,_gF,_gG,_gH){var _gI=E(_gG),_gJ=B(A2(_9a,_gD,_gI)),_gK=function(_){var _gL=newArr(_gJ,_gF),_gM=_gL,_gN=function(_gO,_){while(1){var _gP=B((function(_gQ,_){var _gR=E(_gQ);if(!_gR._){return new T(function(){return new T4(0,E(_gI.a),E(_gI.b),_gJ,_gM);});}else{var _gS=E(_gR.a),_gT=E(_gS.a),_gU=_gM[_gT],_=_gM[_gT]=new T(function(){return B(A2(_gE,_gU,_gS.b));});_gO=_gR.b;return __continue;}})(_gO,_));if(_gP!=__continue){return _gP;}}};return new F(function(){return _gN(_gH,_);});};return new F(function(){return _8O(_gK);});},_gV={_:0,a:_ge,b:_g7,c:_g0,d:_fH,e:_fz,f:_gh,g:_gC},_gW=new T(function(){return B(unCStr("Negative range size"));}),_gX=new T(function(){return B(err(_gW));}),_gY=0,_gZ=function(_h0){var _h1=E(_h0);return (E(_h1.b)-E(_h1.a)|0)+1|0;},_h2=function(_h3,_h4){var _h5=E(_h3),_h6=E(_h4);return (E(_h5.a)>_h6)?false:_h6<=E(_h5.b);},_h7=new T(function(){return B(unCStr("Int"));}),_h8=function(_h9,_ha){return new F(function(){return _dz(_cM,_ha,_h9,_h7);});},_hb=function(_hc,_hd){var _he=E(_hc),_hf=E(_he.a),_hg=E(_hd);if(_hf>_hg){return new F(function(){return _h8(_hg,_he);});}else{if(_hg>E(_he.b)){return new F(function(){return _h8(_hg,_he);});}else{return _hg-_hf|0;}}},_hh=function(_hi,_hj){if(_hi<=_hj){var _hk=function(_hl){return new T2(1,_hl,new T(function(){if(_hl!=_hj){return B(_hk(_hl+1|0));}else{return __Z;}}));};return new F(function(){return _hk(_hi);});}else{return __Z;}},_hm=function(_hn,_ho){return new F(function(){return _hh(E(_hn),E(_ho));});},_hp=function(_hq){var _hr=E(_hq);return new F(function(){return _hm(_hr.a,_hr.b);});},_hs=function(_ht){var _hu=E(_ht),_hv=E(_hu.a),_hw=E(_hu.b);return (_hv>_hw)?E(_cN):(_hw-_hv|0)+1|0;},_hx=function(_hy,_hz){return E(_hy)-E(_hz)|0;},_hA=function(_hB,_hC){return new F(function(){return _hx(_hC,E(_hB).a);});},_hD=function(_hE,_hF){return E(_hE)==E(_hF);},_hG=function(_hH,_hI){return E(_hH)!=E(_hI);},_hJ=new T2(0,_hD,_hG),_hK=function(_hL,_hM){var _hN=E(_hL),_hO=E(_hM);return (_hN>_hO)?E(_hN):E(_hO);},_hP=function(_hQ,_hR){var _hS=E(_hQ),_hT=E(_hR);return (_hS>_hT)?E(_hT):E(_hS);},_hU=function(_hV,_hW){return (_hV>=_hW)?(_hV!=_hW)?2:1:0;},_hX=function(_hY,_hZ){return new F(function(){return _hU(E(_hY),E(_hZ));});},_i0=function(_i1,_i2){return E(_i1)>=E(_i2);},_i3=function(_i4,_i5){return E(_i4)>E(_i5);},_i6=function(_i7,_i8){return E(_i7)<=E(_i8);},_i9=function(_ia,_ib){return E(_ia)<E(_ib);},_ic={_:0,a:_hJ,b:_hX,c:_i9,d:_i6,e:_i3,f:_i0,g:_hK,h:_hP},_id={_:0,a:_ic,b:_hp,c:_hb,d:_hA,e:_h2,f:_hs,g:_gZ},_ie=function(_if,_ig,_ih){var _ii=E(_if);if(!_ii._){return new T2(0,_4,_ih);}else{var _ij=new T(function(){return B(A2(_ii.a,_ig,_ih));}),_ik=B(_ie(_ii.b,_ig,new T(function(){return E(E(_ij).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_ij).a);}),_ik.a),_ik.b);}},_il=function(_im,_in,_io,_ip){if(0>=_im){return new F(function(){return _ie(_4,_io,_ip);});}else{var _iq=function(_ir){var _is=E(_ir);return (_is==1)?E(new T2(1,_in,_4)):new T2(1,_in,new T(function(){return B(_iq(_is-1|0));}));};return new F(function(){return _ie(B(_iq(_im)),_io,_ip);});}},_it=function(_iu){return E(E(_iu).b);},_iv=function(_iw){return E(E(_iw).c);},_ix=function(_iy,_iz){var _iA=E(_iy);if(!_iA._){return __Z;}else{var _iB=E(_iz);return (_iB._==0)?__Z:new T2(1,new T2(0,_iA.a,_iB.a),new T(function(){return B(_ix(_iA.b,_iB.b));}));}},_iC=function(_iD,_iE,_iF,_iG,_iH,_iI){var _iJ=B(_e0(_iF,_iG,_iH,_iI)),_iK=E(_iJ.a)&4294967295,_iL=B(_il(_iK,new T(function(){return B(_it(_iD));}),new T3(0,_iF,_iG,_iH),_iJ.b)),_iM=_iL.a,_iN=new T(function(){var _iO=_iK-1|0;return B(A(_iv,[_iE,_id,new T2(0,_gY,_iO),new T(function(){if(0>_iO){return B(_ix(B(_hh(0,-1)),_iM));}else{var _iP=_iO+1|0;if(_iP>=0){return B(_ix(B(_hh(0,_iP-1|0)),_iM));}else{return E(_gX);}}})]));});return new T2(0,_iN,_iL.b);},_iQ=function(_iR,_iS,_iT,_iU){var _iV=B(_e0(_iR,_iS,_iT,_iU)),_iW=B(_e0(_iR,_iS,_iT,E(_iV.b))),_iX=B(_iC(_fg,_gV,_iR,_iS,_iT,E(_iW.b)));return new T2(0,new T(function(){var _iY=E(_iX.a);return new T6(0,E(_iV.a)&4294967295,E(_iW.a)&4294967295,E(_iY.a),E(_iY.b),_iY.c,_iY.d);}),_iX.b);},_iZ=function(_j0,_j1){var _j2=E(_j0),_j3=B(_iQ(_j2.a,_j2.b,_j2.c,E(_j1)));return new T2(0,_j3.a,_j3.b);},_j4=function(_j5){return E(_cg);},_j6=new T2(0,_j4,_iZ),_j7=function(_j8,_j9){var _ja=E(_j8),_jb=B(_e0(_ja.a,_ja.b,_ja.c,E(_j9)));return new T2(0,new T(function(){return E(_jb.a)&4294967295;}),_jb.b);},_jc=new T(function(){return B(_ce("Data/Binary.hs:56:10-20|put"));}),_jd=function(_je){return E(_jc);},_jf=new T2(0,_jd,_j7),_jg=function(_jh,_ji){var _jj=E(_ji);return new T2(0,_jj.a,_jj.b);},_jk=function(_jl,_jm){return E(_jm).c;},_jn=function(_jo,_jp,_jq,_jr){var _js=function(_){var _jt=E(_jq),_ju=_jt.d,_jv=_ju["byteLength"],_jw=newByteArr(_jv),_jx=_jw,_jy=memcpy(_jx,_ju,_jv>>>0),_jz=function(_jA,_){while(1){var _jB=E(_jA);if(!_jB._){return _5;}else{var _jC=E(_jB.a),_jD=E(_jC.a),_jE=_jx["v"]["i32"][_jD],_=_jx["v"]["i32"][_jD]=B(A2(_jp,_jE,_jC.b));_jA=_jB.b;continue;}}},_jF=B(_jz(_jr,_));return new T4(0,E(_jt.a),E(_jt.b),_jt.c,_jx);};return new F(function(){return _8O(_js);});},_jG=function(_jH,_jI,_jJ,_jK,_jL){var _jM=E(_jK),_jN=function(_){var _jO=B(A2(_9a,_jH,_jM)),_jP=newByteArr(imul(4,_jO)|0),_jQ=_jP;if(_jO>=0){var _jR=_jO-1|0,_jS=function(_){var _jT=function(_jU,_){while(1){var _jV=E(_jU);if(!_jV._){return _5;}else{var _jW=E(_jV.a),_jX=E(_jW.a),_jY=_jQ["v"]["i32"][_jX],_=_jQ["v"]["i32"][_jX]=B(A2(_jI,_jY,_jW.b));_jU=_jV.b;continue;}}},_jZ=B(_jT(_jL,_));return new T4(0,E(_jM.a),E(_jM.b),_jO,_jQ);};if(0<=_jR){var _k0=function(_k1,_){while(1){var _=_jQ["v"]["i32"][_k1]=E(_jJ);if(_k1!=_jR){var _k2=_k1+1|0;_k1=_k2;continue;}else{return _5;}}},_k3=B(_k0(0,_));return new F(function(){return _jS(_);});}else{return new F(function(){return _jS(_);});}}else{return E(_9d);}},_k4=E(_jN);return new F(function(){return _8O(_k4);});},_k5=function(_k6,_k7,_k8){var _k9=E(_k7),_ka=function(_){var _kb=B(A2(_9a,_k6,_k9)),_kc=newByteArr(imul(4,_kb)|0),_kd=_kc;if(_kb>=0){var _ke=_kb-1|0,_kf=function(_){var _kg=function(_kh,_){while(1){var _ki=E(_kh);if(!_ki._){return _5;}else{var _kj=E(_ki.a),_=_kd["v"]["i32"][E(_kj.a)]=E(_kj.b);_kh=_ki.b;continue;}}},_kk=B(_kg(_k8,_));return new T4(0,E(_k9.a),E(_k9.b),_kb,_kd);};if(0<=_ke){var _kl=function(_km,_){while(1){var _=_kd["v"]["i32"][_km]=0;if(_km!=_ke){var _kn=_km+1|0;_km=_kn;continue;}else{return _5;}}},_ko=B(_kl(0,_));return new F(function(){return _kf(_);});}else{return new F(function(){return _kf(_);});}}else{return E(_9d);}},_kp=E(_ka);return new F(function(){return _8O(_kp);});},_kq=function(_kr,_ks,_kt){return E(_ks).d["v"]["i32"][E(_kt)];},_ku=function(_kv,_kw,_kx){var _ky=function(_){var _kz=E(_kw),_kA=_kz.d,_kB=_kA["byteLength"],_kC=newByteArr(_kB),_kD=_kC,_kE=memcpy(_kD,_kA,_kB>>>0),_kF=function(_kG,_){while(1){var _kH=E(_kG);if(!_kH._){return _5;}else{var _kI=E(_kH.a),_=_kD["v"]["i32"][E(_kI.a)]=E(_kI.b);_kG=_kH.b;continue;}}},_kJ=B(_kF(_kx,_));return new T4(0,E(_kz.a),E(_kz.b),_kz.c,_kD);};return new F(function(){return _8O(_ky);});},_kK={_:0,a:_jg,b:_jk,c:_k5,d:_kq,e:_ku,f:_jn,g:_jG},_kL=function(_kM,_kN,_kO,_kP){var _kQ=B(_eb(_kM,_kN,_kO,_kP)),_kR=B(_iC(_jf,_kK,_kM,_kN,_kO,E(_kQ.b)));return new T2(0,new T(function(){var _kS=E(_kR.a);return new T5(0,_kQ.a,E(_kS.a),E(_kS.b),_kS.c,_kS.d);}),_kR.b);},_kT=function(_kU,_kV){var _kW=E(_kU),_kX=B(_kL(_kW.a,_kW.b,_kW.c,E(_kV)));return new T2(0,_kX.a,_kX.b);},_kY=function(_kZ){return E(_cg);},_l0=new T2(0,_kY,_kT),_l1=function(_l2){return new F(function(){return _hh(E(_l2),2147483647);});},_l3=function(_l4,_l5,_l6){if(_l6<=_l5){var _l7=new T(function(){var _l8=_l5-_l4|0,_l9=function(_la){return (_la>=(_l6-_l8|0))?new T2(1,_la,new T(function(){return B(_l9(_la+_l8|0));})):new T2(1,_la,_4);};return B(_l9(_l5));});return new T2(1,_l4,_l7);}else{return (_l6<=_l4)?new T2(1,_l4,_4):__Z;}},_lb=function(_lc,_ld,_le){if(_le>=_ld){var _lf=new T(function(){var _lg=_ld-_lc|0,_lh=function(_li){return (_li<=(_le-_lg|0))?new T2(1,_li,new T(function(){return B(_lh(_li+_lg|0));})):new T2(1,_li,_4);};return B(_lh(_ld));});return new T2(1,_lc,_lf);}else{return (_le>=_lc)?new T2(1,_lc,_4):__Z;}},_lj=function(_lk,_ll){if(_ll<_lk){return new F(function(){return _l3(_lk,_ll,-2147483648);});}else{return new F(function(){return _lb(_lk,_ll,2147483647);});}},_lm=function(_ln,_lo){return new F(function(){return _lj(E(_ln),E(_lo));});},_lp=function(_lq,_lr,_ls){if(_lr<_lq){return new F(function(){return _l3(_lq,_lr,_ls);});}else{return new F(function(){return _lb(_lq,_lr,_ls);});}},_lt=function(_lu,_lv,_lw){return new F(function(){return _lp(E(_lu),E(_lv),E(_lw));});},_lx=function(_ly){return E(_ly);},_lz=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_lA=new T(function(){return B(err(_lz));}),_lB=function(_lC){var _lD=E(_lC);return (_lD==(-2147483648))?E(_lA):_lD-1|0;},_lE=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_lF=new T(function(){return B(err(_lE));}),_lG=function(_lH){var _lI=E(_lH);return (_lI==2147483647)?E(_lF):_lI+1|0;},_lJ={_:0,a:_lG,b:_lB,c:_lx,d:_lx,e:_l1,f:_lm,g:_hm,h:_lt},_lK=function(_lL,_lM){if(_lL<=0){if(_lL>=0){return new F(function(){return quot(_lL,_lM);});}else{if(_lM<=0){return new F(function(){return quot(_lL,_lM);});}else{return quot(_lL+1|0,_lM)-1|0;}}}else{if(_lM>=0){if(_lL>=0){return new F(function(){return quot(_lL,_lM);});}else{if(_lM<=0){return new F(function(){return quot(_lL,_lM);});}else{return quot(_lL+1|0,_lM)-1|0;}}}else{return quot(_lL-1|0,_lM)-1|0;}}},_lN=new T(function(){return B(unCStr("base"));}),_lO=new T(function(){return B(unCStr("GHC.Exception"));}),_lP=new T(function(){return B(unCStr("ArithException"));}),_lQ=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_lN,_lO,_lP),_lR=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_lQ,_4,_4),_lS=function(_lT){return E(_lR);},_lU=function(_lV){var _lW=E(_lV);return new F(function(){return _2M(B(_2K(_lW.a)),_lS,_lW.b);});},_lX=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_lY=new T(function(){return B(unCStr("denormal"));}),_lZ=new T(function(){return B(unCStr("divide by zero"));}),_m0=new T(function(){return B(unCStr("loss of precision"));}),_m1=new T(function(){return B(unCStr("arithmetic underflow"));}),_m2=new T(function(){return B(unCStr("arithmetic overflow"));}),_m3=function(_m4,_m5){switch(E(_m4)){case 0:return new F(function(){return _0(_m2,_m5);});break;case 1:return new F(function(){return _0(_m1,_m5);});break;case 2:return new F(function(){return _0(_m0,_m5);});break;case 3:return new F(function(){return _0(_lZ,_m5);});break;case 4:return new F(function(){return _0(_lY,_m5);});break;default:return new F(function(){return _0(_lX,_m5);});}},_m6=function(_m7){return new F(function(){return _m3(_m7,_4);});},_m8=function(_m9,_ma,_mb){return new F(function(){return _m3(_ma,_mb);});},_mc=function(_md,_me){return new F(function(){return _3X(_m3,_md,_me);});},_mf=new T3(0,_m8,_m6,_mc),_mg=new T(function(){return new T5(0,_lS,_mf,_mh,_lU,_m6);}),_mh=function(_6S){return new T2(0,_mg,_6S);},_mi=3,_mj=new T(function(){return B(_mh(_mi));}),_mk=new T(function(){return die(_mj);}),_ml=0,_mm=new T(function(){return B(_mh(_ml));}),_mn=new T(function(){return die(_mm);}),_mo=function(_mp,_mq){var _mr=E(_mq);switch(_mr){case -1:var _ms=E(_mp);if(_ms==(-2147483648)){return E(_mn);}else{return new F(function(){return _lK(_ms,-1);});}break;case 0:return E(_mk);default:return new F(function(){return _lK(_mp,_mr);});}},_mt=function(_mu,_mv){return new F(function(){return _mo(E(_mu),E(_mv));});},_mw=0,_mx=new T2(0,_mn,_mw),_my=function(_mz,_mA){var _mB=E(_mz),_mC=E(_mA);switch(_mC){case -1:var _mD=E(_mB);if(_mD==(-2147483648)){return E(_mx);}else{if(_mD<=0){if(_mD>=0){var _mE=quotRemI(_mD,-1);return new T2(0,_mE.a,_mE.b);}else{var _mF=quotRemI(_mD,-1);return new T2(0,_mF.a,_mF.b);}}else{var _mG=quotRemI(_mD-1|0,-1);return new T2(0,_mG.a-1|0,(_mG.b+(-1)|0)+1|0);}}break;case 0:return E(_mk);default:if(_mB<=0){if(_mB>=0){var _mH=quotRemI(_mB,_mC);return new T2(0,_mH.a,_mH.b);}else{if(_mC<=0){var _mI=quotRemI(_mB,_mC);return new T2(0,_mI.a,_mI.b);}else{var _mJ=quotRemI(_mB+1|0,_mC);return new T2(0,_mJ.a-1|0,(_mJ.b+_mC|0)-1|0);}}}else{if(_mC>=0){if(_mB>=0){var _mK=quotRemI(_mB,_mC);return new T2(0,_mK.a,_mK.b);}else{if(_mC<=0){var _mL=quotRemI(_mB,_mC);return new T2(0,_mL.a,_mL.b);}else{var _mM=quotRemI(_mB+1|0,_mC);return new T2(0,_mM.a-1|0,(_mM.b+_mC|0)-1|0);}}}else{var _mN=quotRemI(_mB-1|0,_mC);return new T2(0,_mN.a-1|0,(_mN.b+_mC|0)+1|0);}}}},_mO=function(_mP,_mQ){var _mR=_mP%_mQ;if(_mP<=0){if(_mP>=0){return E(_mR);}else{if(_mQ<=0){return E(_mR);}else{var _mS=E(_mR);return (_mS==0)?0:_mS+_mQ|0;}}}else{if(_mQ>=0){if(_mP>=0){return E(_mR);}else{if(_mQ<=0){return E(_mR);}else{var _mT=E(_mR);return (_mT==0)?0:_mT+_mQ|0;}}}else{var _mU=E(_mR);return (_mU==0)?0:_mU+_mQ|0;}}},_mV=function(_mW,_mX){var _mY=E(_mX);switch(_mY){case -1:return E(_mw);case 0:return E(_mk);default:return new F(function(){return _mO(E(_mW),_mY);});}},_mZ=function(_n0,_n1){var _n2=E(_n0),_n3=E(_n1);switch(_n3){case -1:var _n4=E(_n2);if(_n4==(-2147483648)){return E(_mn);}else{return new F(function(){return quot(_n4,-1);});}break;case 0:return E(_mk);default:return new F(function(){return quot(_n2,_n3);});}},_n5=function(_n6,_n7){var _n8=E(_n6),_n9=E(_n7);switch(_n9){case -1:var _na=E(_n8);if(_na==(-2147483648)){return E(_mx);}else{var _nb=quotRemI(_na,-1);return new T2(0,_nb.a,_nb.b);}break;case 0:return E(_mk);default:var _nc=quotRemI(_n8,_n9);return new T2(0,_nc.a,_nc.b);}},_nd=function(_ne,_nf){var _ng=E(_nf);switch(_ng){case -1:return E(_mw);case 0:return E(_mk);default:return E(_ne)%_ng;}},_nh=function(_ni){return new T1(0,_ni);},_nj=function(_nk){return new F(function(){return _nh(E(_nk));});},_nl=new T1(0,1),_nm=function(_nn){return new T2(0,E(B(_nh(E(_nn)))),E(_nl));},_no=function(_np,_nq){return imul(E(_np),E(_nq))|0;},_nr=function(_ns,_nt){return E(_ns)+E(_nt)|0;},_nu=function(_nv){var _nw=E(_nv);return (_nw<0)? -_nw:E(_nw);},_nx=function(_ny){var _nz=E(_ny);if(!_nz._){return E(_nz.a);}else{return new F(function(){return I_toInt(_nz.a);});}},_nA=function(_nB){return new F(function(){return _nx(_nB);});},_nC=function(_nD){return  -E(_nD);},_nE=-1,_nF=0,_nG=1,_nH=function(_nI){var _nJ=E(_nI);return (_nJ>=0)?(E(_nJ)==0)?E(_nF):E(_nG):E(_nE);},_nK={_:0,a:_nr,b:_hx,c:_no,d:_nC,e:_nu,f:_nH,g:_nA},_nL=new T2(0,_hD,_hG),_nM={_:0,a:_nL,b:_hX,c:_i9,d:_i6,e:_i3,f:_i0,g:_hK,h:_hP},_nN=new T3(0,_nK,_nM,_nm),_nO={_:0,a:_nN,b:_lJ,c:_mZ,d:_nd,e:_mt,f:_mV,g:_n5,h:_my,i:_nj},_nP={_:0,a:_lG,b:_lB,c:_lx,d:_lx,e:_l1,f:_lm,g:_hm,h:_lt},_nQ={_:0,a:_nr,b:_hx,c:_no,d:_nC,e:_nu,f:_nH,g:_nA},_nR=new T3(0,_nQ,_ic,_nm),_nS={_:0,a:_nR,b:_nP,c:_mZ,d:_nd,e:_mt,f:_mV,g:_n5,h:_my,i:_nj},_nT=new T1(0,2),_nU=function(_nV){return E(E(_nV).a);},_nW=function(_nX){return E(E(_nX).a);},_nY=function(_nZ,_o0){while(1){var _o1=E(_nZ);if(!_o1._){var _o2=_o1.a,_o3=E(_o0);if(!_o3._){var _o4=_o3.a;if(!(imul(_o2,_o4)|0)){return new T1(0,imul(_o2,_o4)|0);}else{_nZ=new T1(1,I_fromInt(_o2));_o0=new T1(1,I_fromInt(_o4));continue;}}else{_nZ=new T1(1,I_fromInt(_o2));_o0=_o3;continue;}}else{var _o5=E(_o0);if(!_o5._){_nZ=_o1;_o0=new T1(1,I_fromInt(_o5.a));continue;}else{return new T1(1,I_mul(_o1.a,_o5.a));}}}},_o6=function(_o7,_o8,_o9){while(1){if(!(_o8%2)){var _oa=B(_nY(_o7,_o7)),_ob=quot(_o8,2);_o7=_oa;_o8=_ob;continue;}else{var _oc=E(_o8);if(_oc==1){return new F(function(){return _nY(_o7,_o9);});}else{var _oa=B(_nY(_o7,_o7)),_od=B(_nY(_o7,_o9));_o7=_oa;_o8=quot(_oc-1|0,2);_o9=_od;continue;}}}},_oe=function(_of,_og){while(1){if(!(_og%2)){var _oh=B(_nY(_of,_of)),_oi=quot(_og,2);_of=_oh;_og=_oi;continue;}else{var _oj=E(_og);if(_oj==1){return E(_of);}else{return new F(function(){return _o6(B(_nY(_of,_of)),quot(_oj-1|0,2),_of);});}}}},_ok=function(_ol){return E(E(_ol).c);},_om=function(_on){return E(E(_on).a);},_oo=function(_op){return E(E(_op).b);},_oq=function(_or){return E(E(_or).b);},_os=function(_ot){return E(E(_ot).c);},_ou=function(_ov){return E(E(_ov).a);},_ow=new T1(0,0),_ox=new T1(0,2),_oy=function(_oz){return E(E(_oz).g);},_oA=function(_oB){return E(E(_oB).d);},_oC=function(_oD,_oE){var _oF=B(_nU(_oD)),_oG=new T(function(){return B(_nW(_oF));}),_oH=new T(function(){return B(A3(_oA,_oD,_oE,new T(function(){return B(A2(_oy,_oG,_ox));})));});return new F(function(){return A3(_ou,B(_om(B(_oo(_oF)))),_oH,new T(function(){return B(A2(_oy,_oG,_ow));}));});},_oI=new T(function(){return B(unCStr("Negative exponent"));}),_oJ=new T(function(){return B(err(_oI));}),_oK=function(_oL){return E(E(_oL).c);},_oM=function(_oN,_oO,_oP,_oQ){var _oR=B(_nU(_oO)),_oS=new T(function(){return B(_nW(_oR));}),_oT=B(_oo(_oR));if(!B(A3(_os,_oT,_oQ,new T(function(){return B(A2(_oy,_oS,_ow));})))){if(!B(A3(_ou,B(_om(_oT)),_oQ,new T(function(){return B(A2(_oy,_oS,_ow));})))){var _oU=new T(function(){return B(A2(_oy,_oS,_ox));}),_oV=new T(function(){return B(A2(_oy,_oS,_nl));}),_oW=B(_om(_oT)),_oX=function(_oY,_oZ,_p0){while(1){var _p1=B((function(_p2,_p3,_p4){if(!B(_oC(_oO,_p3))){if(!B(A3(_ou,_oW,_p3,_oV))){var _p5=new T(function(){return B(A3(_oK,_oO,new T(function(){return B(A3(_oq,_oS,_p3,_oV));}),_oU));});_oY=new T(function(){return B(A3(_ok,_oN,_p2,_p2));});_oZ=_p5;_p0=new T(function(){return B(A3(_ok,_oN,_p2,_p4));});return __continue;}else{return new F(function(){return A3(_ok,_oN,_p2,_p4);});}}else{var _p6=_p4;_oY=new T(function(){return B(A3(_ok,_oN,_p2,_p2));});_oZ=new T(function(){return B(A3(_oK,_oO,_p3,_oU));});_p0=_p6;return __continue;}})(_oY,_oZ,_p0));if(_p1!=__continue){return _p1;}}},_p7=function(_p8,_p9){while(1){var _pa=B((function(_pb,_pc){if(!B(_oC(_oO,_pc))){if(!B(A3(_ou,_oW,_pc,_oV))){var _pd=new T(function(){return B(A3(_oK,_oO,new T(function(){return B(A3(_oq,_oS,_pc,_oV));}),_oU));});return new F(function(){return _oX(new T(function(){return B(A3(_ok,_oN,_pb,_pb));}),_pd,_pb);});}else{return E(_pb);}}else{_p8=new T(function(){return B(A3(_ok,_oN,_pb,_pb));});_p9=new T(function(){return B(A3(_oK,_oO,_pc,_oU));});return __continue;}})(_p8,_p9));if(_pa!=__continue){return _pa;}}};return new F(function(){return _p7(_oP,_oQ);});}else{return new F(function(){return A2(_oy,_oN,_nl);});}}else{return E(_oJ);}},_pe=new T(function(){return B(err(_oI));}),_pf=function(_pg){var _ph=I_decodeDouble(_pg);return new T2(0,new T1(1,_ph.b),_ph.a);},_pi=function(_pj,_pk){var _pl=E(_pj);return (_pl._==0)?_pl.a*Math.pow(2,_pk):I_toNumber(_pl.a)*Math.pow(2,_pk);},_pm=function(_pn,_po){var _pp=E(_pn);if(!_pp._){var _pq=_pp.a,_pr=E(_po);return (_pr._==0)?_pq==_pr.a:(I_compareInt(_pr.a,_pq)==0)?true:false;}else{var _ps=_pp.a,_pt=E(_po);return (_pt._==0)?(I_compareInt(_ps,_pt.a)==0)?true:false:(I_compare(_ps,_pt.a)==0)?true:false;}},_pu=function(_pv,_pw){while(1){var _px=E(_pv);if(!_px._){var _py=E(_px.a);if(_py==(-2147483648)){_pv=new T1(1,I_fromInt(-2147483648));continue;}else{var _pz=E(_pw);if(!_pz._){var _pA=_pz.a;return new T2(0,new T1(0,quot(_py,_pA)),new T1(0,_py%_pA));}else{_pv=new T1(1,I_fromInt(_py));_pw=_pz;continue;}}}else{var _pB=E(_pw);if(!_pB._){_pv=_px;_pw=new T1(1,I_fromInt(_pB.a));continue;}else{var _pC=I_quotRem(_px.a,_pB.a);return new T2(0,new T1(1,_pC.a),new T1(1,_pC.b));}}}},_pD=0,_pE=new T1(0,0),_pF=function(_pG,_pH){var _pI=B(_pf(_pH)),_pJ=_pI.a,_pK=_pI.b,_pL=new T(function(){return B(_nW(new T(function(){return B(_nU(_pG));})));});if(_pK<0){var _pM= -_pK;if(_pM>=0){var _pN=E(_pM);if(!_pN){var _pO=E(_nl);}else{var _pO=B(_oe(_nT,_pN));}if(!B(_pm(_pO,_pE))){var _pP=B(_pu(_pJ,_pO));return new T2(0,new T(function(){return B(A2(_oy,_pL,_pP.a));}),new T(function(){return B(_pi(_pP.b,_pK));}));}else{return E(_mk);}}else{return E(_pe);}}else{var _pQ=new T(function(){var _pR=new T(function(){return B(_oM(_pL,_nS,new T(function(){return B(A2(_oy,_pL,_nT));}),_pK));});return B(A3(_ok,_pL,new T(function(){return B(A2(_oy,_pL,_pJ));}),_pR));});return new T2(0,_pQ,_pD);}},_pS=function(_pT){var _pU=E(_pT);if(!_pU._){return _pU.a;}else{return new F(function(){return I_toNumber(_pU.a);});}},_pV=function(_pW,_pX){var _pY=B(_pF(_nO,Math.pow(B(_pS(_pW)),_pX))),_pZ=_pY.a;return (E(_pY.b)>=0)?E(_pZ):E(_pZ)-1|0;},_q0=new T1(0,1),_q1=new T1(0,0),_q2=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_q3=new T(function(){return B(err(_q2));}),_q4=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_q5=new T(function(){return B(err(_q4));}),_q6=new T1(0,2),_q7=new T(function(){return B(unCStr("NaN"));}),_q8=new T(function(){return B(_7f("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_q9=function(_qa,_qb){while(1){var _qc=B((function(_qd,_qe){var _qf=E(_qd);switch(_qf._){case 0:var _qg=E(_qe);if(!_qg._){return __Z;}else{_qa=B(A1(_qf.a,_qg.a));_qb=_qg.b;return __continue;}break;case 1:var _qh=B(A1(_qf.a,_qe)),_qi=_qe;_qa=_qh;_qb=_qi;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_qf.a,_qe),new T(function(){return B(_q9(_qf.b,_qe));}));default:return E(_qf.a);}})(_qa,_qb));if(_qc!=__continue){return _qc;}}},_qj=function(_qk,_ql){var _qm=function(_qn){var _qo=E(_ql);if(_qo._==3){return new T2(3,_qo.a,new T(function(){return B(_qj(_qk,_qo.b));}));}else{var _qp=E(_qk);if(_qp._==2){return E(_qo);}else{var _qq=E(_qo);if(_qq._==2){return E(_qp);}else{var _qr=function(_qs){var _qt=E(_qq);if(_qt._==4){var _qu=function(_qv){return new T1(4,new T(function(){return B(_0(B(_q9(_qp,_qv)),_qt.a));}));};return new T1(1,_qu);}else{var _qw=E(_qp);if(_qw._==1){var _qx=_qw.a,_qy=E(_qt);if(!_qy._){return new T1(1,function(_qz){return new F(function(){return _qj(B(A1(_qx,_qz)),_qy);});});}else{var _qA=function(_qB){return new F(function(){return _qj(B(A1(_qx,_qB)),new T(function(){return B(A1(_qy.a,_qB));}));});};return new T1(1,_qA);}}else{var _qC=E(_qt);if(!_qC._){return E(_q8);}else{var _qD=function(_qE){return new F(function(){return _qj(_qw,new T(function(){return B(A1(_qC.a,_qE));}));});};return new T1(1,_qD);}}}},_qF=E(_qp);switch(_qF._){case 1:var _qG=E(_qq);if(_qG._==4){var _qH=function(_qI){return new T1(4,new T(function(){return B(_0(B(_q9(B(A1(_qF.a,_qI)),_qI)),_qG.a));}));};return new T1(1,_qH);}else{return new F(function(){return _qr(_);});}break;case 4:var _qJ=_qF.a,_qK=E(_qq);switch(_qK._){case 0:var _qL=function(_qM){var _qN=new T(function(){return B(_0(_qJ,new T(function(){return B(_q9(_qK,_qM));},1)));});return new T1(4,_qN);};return new T1(1,_qL);case 1:var _qO=function(_qP){var _qQ=new T(function(){return B(_0(_qJ,new T(function(){return B(_q9(B(A1(_qK.a,_qP)),_qP));},1)));});return new T1(4,_qQ);};return new T1(1,_qO);default:return new T1(4,new T(function(){return B(_0(_qJ,_qK.a));}));}break;default:return new F(function(){return _qr(_);});}}}}},_qR=E(_qk);switch(_qR._){case 0:var _qS=E(_ql);if(!_qS._){var _qT=function(_qU){return new F(function(){return _qj(B(A1(_qR.a,_qU)),new T(function(){return B(A1(_qS.a,_qU));}));});};return new T1(0,_qT);}else{return new F(function(){return _qm(_);});}break;case 3:return new T2(3,_qR.a,new T(function(){return B(_qj(_qR.b,_ql));}));default:return new F(function(){return _qm(_);});}},_qV=new T(function(){return B(unCStr("("));}),_qW=new T(function(){return B(unCStr(")"));}),_qX=function(_qY,_qZ){while(1){var _r0=E(_qY);if(!_r0._){return (E(_qZ)._==0)?true:false;}else{var _r1=E(_qZ);if(!_r1._){return false;}else{if(E(_r0.a)!=E(_r1.a)){return false;}else{_qY=_r0.b;_qZ=_r1.b;continue;}}}}},_r2=function(_r3,_r4){return E(_r3)!=E(_r4);},_r5=function(_r6,_r7){return E(_r6)==E(_r7);},_r8=new T2(0,_r5,_r2),_r9=function(_ra,_rb){while(1){var _rc=E(_ra);if(!_rc._){return (E(_rb)._==0)?true:false;}else{var _rd=E(_rb);if(!_rd._){return false;}else{if(E(_rc.a)!=E(_rd.a)){return false;}else{_ra=_rc.b;_rb=_rd.b;continue;}}}}},_re=function(_rf,_rg){return (!B(_r9(_rf,_rg)))?true:false;},_rh=new T2(0,_r9,_re),_ri=function(_rj,_rk){var _rl=E(_rj);switch(_rl._){case 0:return new T1(0,function(_rm){return new F(function(){return _ri(B(A1(_rl.a,_rm)),_rk);});});case 1:return new T1(1,function(_rn){return new F(function(){return _ri(B(A1(_rl.a,_rn)),_rk);});});case 2:return new T0(2);case 3:return new F(function(){return _qj(B(A1(_rk,_rl.a)),new T(function(){return B(_ri(_rl.b,_rk));}));});break;default:var _ro=function(_rp){var _rq=E(_rp);if(!_rq._){return __Z;}else{var _rr=E(_rq.a);return new F(function(){return _0(B(_q9(B(A1(_rk,_rr.a)),_rr.b)),new T(function(){return B(_ro(_rq.b));},1));});}},_rs=B(_ro(_rl.a));return (_rs._==0)?new T0(2):new T1(4,_rs);}},_rt=new T0(2),_ru=function(_rv){return new T2(3,_rv,_rt);},_rw=function(_rx,_ry){var _rz=E(_rx);if(!_rz){return new F(function(){return A1(_ry,_5);});}else{var _rA=new T(function(){return B(_rw(_rz-1|0,_ry));});return new T1(0,function(_rB){return E(_rA);});}},_rC=function(_rD,_rE,_rF){var _rG=new T(function(){return B(A1(_rD,_ru));}),_rH=function(_rI,_rJ,_rK,_rL){while(1){var _rM=B((function(_rN,_rO,_rP,_rQ){var _rR=E(_rN);switch(_rR._){case 0:var _rS=E(_rO);if(!_rS._){return new F(function(){return A1(_rE,_rQ);});}else{var _rT=_rP+1|0,_rU=_rQ;_rI=B(A1(_rR.a,_rS.a));_rJ=_rS.b;_rK=_rT;_rL=_rU;return __continue;}break;case 1:var _rV=B(A1(_rR.a,_rO)),_rW=_rO,_rT=_rP,_rU=_rQ;_rI=_rV;_rJ=_rW;_rK=_rT;_rL=_rU;return __continue;case 2:return new F(function(){return A1(_rE,_rQ);});break;case 3:var _rX=new T(function(){return B(_ri(_rR,_rQ));});return new F(function(){return _rw(_rP,function(_rY){return E(_rX);});});break;default:return new F(function(){return _ri(_rR,_rQ);});}})(_rI,_rJ,_rK,_rL));if(_rM!=__continue){return _rM;}}};return function(_rZ){return new F(function(){return _rH(_rG,_rZ,0,_rF);});};},_s0=function(_s1){return new F(function(){return A1(_s1,_4);});},_s2=function(_s3,_s4){var _s5=function(_s6){var _s7=E(_s6);if(!_s7._){return E(_s0);}else{var _s8=_s7.a;if(!B(A1(_s3,_s8))){return E(_s0);}else{var _s9=new T(function(){return B(_s5(_s7.b));}),_sa=function(_sb){var _sc=new T(function(){return B(A1(_s9,function(_sd){return new F(function(){return A1(_sb,new T2(1,_s8,_sd));});}));});return new T1(0,function(_se){return E(_sc);});};return E(_sa);}}};return function(_sf){return new F(function(){return A2(_s5,_sf,_s4);});};},_sg=new T0(6),_sh=new T(function(){return B(unCStr("valDig: Bad base"));}),_si=new T(function(){return B(err(_sh));}),_sj=function(_sk,_sl){var _sm=function(_sn,_so){var _sp=E(_sn);if(!_sp._){var _sq=new T(function(){return B(A1(_so,_4));});return function(_sr){return new F(function(){return A1(_sr,_sq);});};}else{var _ss=E(_sp.a),_st=function(_su){var _sv=new T(function(){return B(_sm(_sp.b,function(_sw){return new F(function(){return A1(_so,new T2(1,_su,_sw));});}));}),_sx=function(_sy){var _sz=new T(function(){return B(A1(_sv,_sy));});return new T1(0,function(_sA){return E(_sz);});};return E(_sx);};switch(E(_sk)){case 8:if(48>_ss){var _sB=new T(function(){return B(A1(_so,_4));});return function(_sC){return new F(function(){return A1(_sC,_sB);});};}else{if(_ss>55){var _sD=new T(function(){return B(A1(_so,_4));});return function(_sE){return new F(function(){return A1(_sE,_sD);});};}else{return new F(function(){return _st(_ss-48|0);});}}break;case 10:if(48>_ss){var _sF=new T(function(){return B(A1(_so,_4));});return function(_sG){return new F(function(){return A1(_sG,_sF);});};}else{if(_ss>57){var _sH=new T(function(){return B(A1(_so,_4));});return function(_sI){return new F(function(){return A1(_sI,_sH);});};}else{return new F(function(){return _st(_ss-48|0);});}}break;case 16:if(48>_ss){if(97>_ss){if(65>_ss){var _sJ=new T(function(){return B(A1(_so,_4));});return function(_sK){return new F(function(){return A1(_sK,_sJ);});};}else{if(_ss>70){var _sL=new T(function(){return B(A1(_so,_4));});return function(_sM){return new F(function(){return A1(_sM,_sL);});};}else{return new F(function(){return _st((_ss-65|0)+10|0);});}}}else{if(_ss>102){if(65>_ss){var _sN=new T(function(){return B(A1(_so,_4));});return function(_sO){return new F(function(){return A1(_sO,_sN);});};}else{if(_ss>70){var _sP=new T(function(){return B(A1(_so,_4));});return function(_sQ){return new F(function(){return A1(_sQ,_sP);});};}else{return new F(function(){return _st((_ss-65|0)+10|0);});}}}else{return new F(function(){return _st((_ss-97|0)+10|0);});}}}else{if(_ss>57){if(97>_ss){if(65>_ss){var _sR=new T(function(){return B(A1(_so,_4));});return function(_sS){return new F(function(){return A1(_sS,_sR);});};}else{if(_ss>70){var _sT=new T(function(){return B(A1(_so,_4));});return function(_sU){return new F(function(){return A1(_sU,_sT);});};}else{return new F(function(){return _st((_ss-65|0)+10|0);});}}}else{if(_ss>102){if(65>_ss){var _sV=new T(function(){return B(A1(_so,_4));});return function(_sW){return new F(function(){return A1(_sW,_sV);});};}else{if(_ss>70){var _sX=new T(function(){return B(A1(_so,_4));});return function(_sY){return new F(function(){return A1(_sY,_sX);});};}else{return new F(function(){return _st((_ss-65|0)+10|0);});}}}else{return new F(function(){return _st((_ss-97|0)+10|0);});}}}else{return new F(function(){return _st(_ss-48|0);});}}break;default:return E(_si);}}},_sZ=function(_t0){var _t1=E(_t0);if(!_t1._){return new T0(2);}else{return new F(function(){return A1(_sl,_t1);});}};return function(_t2){return new F(function(){return A3(_sm,_t2,_2j,_sZ);});};},_t3=16,_t4=8,_t5=function(_t6){var _t7=function(_t8){return new F(function(){return A1(_t6,new T1(5,new T2(0,_t4,_t8)));});},_t9=function(_ta){return new F(function(){return A1(_t6,new T1(5,new T2(0,_t3,_ta)));});},_tb=function(_tc){switch(E(_tc)){case 79:return new T1(1,B(_sj(_t4,_t7)));case 88:return new T1(1,B(_sj(_t3,_t9)));case 111:return new T1(1,B(_sj(_t4,_t7)));case 120:return new T1(1,B(_sj(_t3,_t9)));default:return new T0(2);}};return function(_td){return (E(_td)==48)?E(new T1(0,_tb)):new T0(2);};},_te=function(_tf){return new T1(0,B(_t5(_tf)));},_tg=function(_th){return new F(function(){return A1(_th,_4l);});},_ti=function(_tj){return new F(function(){return A1(_tj,_4l);});},_tk=10,_tl=new T1(0,1),_tm=new T1(0,2147483647),_tn=function(_to,_tp){while(1){var _tq=E(_to);if(!_tq._){var _tr=_tq.a,_ts=E(_tp);if(!_ts._){var _tt=_ts.a,_tu=addC(_tr,_tt);if(!E(_tu.b)){return new T1(0,_tu.a);}else{_to=new T1(1,I_fromInt(_tr));_tp=new T1(1,I_fromInt(_tt));continue;}}else{_to=new T1(1,I_fromInt(_tr));_tp=_ts;continue;}}else{var _tv=E(_tp);if(!_tv._){_to=_tq;_tp=new T1(1,I_fromInt(_tv.a));continue;}else{return new T1(1,I_add(_tq.a,_tv.a));}}}},_tw=new T(function(){return B(_tn(_tm,_tl));}),_tx=function(_ty){var _tz=E(_ty);if(!_tz._){var _tA=E(_tz.a);return (_tA==(-2147483648))?E(_tw):new T1(0, -_tA);}else{return new T1(1,I_negate(_tz.a));}},_tB=new T1(0,10),_tC=function(_tD,_tE){while(1){var _tF=E(_tD);if(!_tF._){return E(_tE);}else{var _tG=_tE+1|0;_tD=_tF.b;_tE=_tG;continue;}}},_tH=function(_tI){return new F(function(){return _nh(E(_tI));});},_tJ=new T(function(){return B(unCStr("this should not happen"));}),_tK=new T(function(){return B(err(_tJ));}),_tL=function(_tM,_tN){var _tO=E(_tN);if(!_tO._){return __Z;}else{var _tP=E(_tO.b);return (_tP._==0)?E(_tK):new T2(1,B(_tn(B(_nY(_tO.a,_tM)),_tP.a)),new T(function(){return B(_tL(_tM,_tP.b));}));}},_tQ=new T1(0,0),_tR=function(_tS,_tT,_tU){while(1){var _tV=B((function(_tW,_tX,_tY){var _tZ=E(_tY);if(!_tZ._){return E(_tQ);}else{if(!E(_tZ.b)._){return E(_tZ.a);}else{var _u0=E(_tX);if(_u0<=40){var _u1=function(_u2,_u3){while(1){var _u4=E(_u3);if(!_u4._){return E(_u2);}else{var _u5=B(_tn(B(_nY(_u2,_tW)),_u4.a));_u2=_u5;_u3=_u4.b;continue;}}};return new F(function(){return _u1(_tQ,_tZ);});}else{var _u6=B(_nY(_tW,_tW));if(!(_u0%2)){var _u7=B(_tL(_tW,_tZ));_tS=_u6;_tT=quot(_u0+1|0,2);_tU=_u7;return __continue;}else{var _u7=B(_tL(_tW,new T2(1,_tQ,_tZ)));_tS=_u6;_tT=quot(_u0+1|0,2);_tU=_u7;return __continue;}}}}})(_tS,_tT,_tU));if(_tV!=__continue){return _tV;}}},_u8=function(_u9,_ua){return new F(function(){return _tR(_u9,new T(function(){return B(_tC(_ua,0));},1),B(_G(_tH,_ua)));});},_ub=function(_uc){var _ud=new T(function(){var _ue=new T(function(){var _uf=function(_ug){return new F(function(){return A1(_uc,new T1(1,new T(function(){return B(_u8(_tB,_ug));})));});};return new T1(1,B(_sj(_tk,_uf)));}),_uh=function(_ui){if(E(_ui)==43){var _uj=function(_uk){return new F(function(){return A1(_uc,new T1(1,new T(function(){return B(_u8(_tB,_uk));})));});};return new T1(1,B(_sj(_tk,_uj)));}else{return new T0(2);}},_ul=function(_um){if(E(_um)==45){var _un=function(_uo){return new F(function(){return A1(_uc,new T1(1,new T(function(){return B(_tx(B(_u8(_tB,_uo))));})));});};return new T1(1,B(_sj(_tk,_un)));}else{return new T0(2);}};return B(_qj(B(_qj(new T1(0,_ul),new T1(0,_uh))),_ue));});return new F(function(){return _qj(new T1(0,function(_up){return (E(_up)==101)?E(_ud):new T0(2);}),new T1(0,function(_uq){return (E(_uq)==69)?E(_ud):new T0(2);}));});},_ur=function(_us){var _ut=function(_uu){return new F(function(){return A1(_us,new T1(1,_uu));});};return function(_uv){return (E(_uv)==46)?new T1(1,B(_sj(_tk,_ut))):new T0(2);};},_uw=function(_ux){return new T1(0,B(_ur(_ux)));},_uy=function(_uz){var _uA=function(_uB){var _uC=function(_uD){return new T1(1,B(_rC(_ub,_tg,function(_uE){return new F(function(){return A1(_uz,new T1(5,new T3(1,_uB,_uD,_uE)));});})));};return new T1(1,B(_rC(_uw,_ti,_uC)));};return new F(function(){return _sj(_tk,_uA);});},_uF=function(_uG){return new T1(1,B(_uy(_uG)));},_uH=function(_uI,_uJ,_uK){while(1){var _uL=E(_uK);if(!_uL._){return false;}else{if(!B(A3(_ou,_uI,_uJ,_uL.a))){_uK=_uL.b;continue;}else{return true;}}}},_uM=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_uN=function(_uO){return new F(function(){return _uH(_r8,_uO,_uM);});},_uP=false,_uQ=true,_uR=function(_uS){var _uT=new T(function(){return B(A1(_uS,_t4));}),_uU=new T(function(){return B(A1(_uS,_t3));});return function(_uV){switch(E(_uV)){case 79:return E(_uT);case 88:return E(_uU);case 111:return E(_uT);case 120:return E(_uU);default:return new T0(2);}};},_uW=function(_uX){return new T1(0,B(_uR(_uX)));},_uY=function(_uZ){return new F(function(){return A1(_uZ,_tk);});},_v0=function(_v1,_v2){var _v3=E(_v1);if(!_v3._){var _v4=_v3.a,_v5=E(_v2);return (_v5._==0)?_v4<=_v5.a:I_compareInt(_v5.a,_v4)>=0;}else{var _v6=_v3.a,_v7=E(_v2);return (_v7._==0)?I_compareInt(_v6,_v7.a)<=0:I_compare(_v6,_v7.a)<=0;}},_v8=function(_v9){return new T0(2);},_va=function(_vb){var _vc=E(_vb);if(!_vc._){return E(_v8);}else{var _vd=_vc.a,_ve=E(_vc.b);if(!_ve._){return E(_vd);}else{var _vf=new T(function(){return B(_va(_ve));}),_vg=function(_vh){return new F(function(){return _qj(B(A1(_vd,_vh)),new T(function(){return B(A1(_vf,_vh));}));});};return E(_vg);}}},_vi=function(_vj,_vk){var _vl=function(_vm,_vn,_vo){var _vp=E(_vm);if(!_vp._){return new F(function(){return A1(_vo,_vj);});}else{var _vq=E(_vn);if(!_vq._){return new T0(2);}else{if(E(_vp.a)!=E(_vq.a)){return new T0(2);}else{var _vr=new T(function(){return B(_vl(_vp.b,_vq.b,_vo));});return new T1(0,function(_vs){return E(_vr);});}}}};return function(_vt){return new F(function(){return _vl(_vj,_vt,_vk);});};},_vu=new T(function(){return B(unCStr("SO"));}),_vv=14,_vw=function(_vx){var _vy=new T(function(){return B(A1(_vx,_vv));});return new T1(1,B(_vi(_vu,function(_vz){return E(_vy);})));},_vA=new T(function(){return B(unCStr("SOH"));}),_vB=1,_vC=function(_vD){var _vE=new T(function(){return B(A1(_vD,_vB));});return new T1(1,B(_vi(_vA,function(_vF){return E(_vE);})));},_vG=function(_vH){return new T1(1,B(_rC(_vC,_vw,_vH)));},_vI=new T(function(){return B(unCStr("NUL"));}),_vJ=0,_vK=function(_vL){var _vM=new T(function(){return B(A1(_vL,_vJ));});return new T1(1,B(_vi(_vI,function(_vN){return E(_vM);})));},_vO=new T(function(){return B(unCStr("STX"));}),_vP=2,_vQ=function(_vR){var _vS=new T(function(){return B(A1(_vR,_vP));});return new T1(1,B(_vi(_vO,function(_vT){return E(_vS);})));},_vU=new T(function(){return B(unCStr("ETX"));}),_vV=3,_vW=function(_vX){var _vY=new T(function(){return B(A1(_vX,_vV));});return new T1(1,B(_vi(_vU,function(_vZ){return E(_vY);})));},_w0=new T(function(){return B(unCStr("EOT"));}),_w1=4,_w2=function(_w3){var _w4=new T(function(){return B(A1(_w3,_w1));});return new T1(1,B(_vi(_w0,function(_w5){return E(_w4);})));},_w6=new T(function(){return B(unCStr("ENQ"));}),_w7=5,_w8=function(_w9){var _wa=new T(function(){return B(A1(_w9,_w7));});return new T1(1,B(_vi(_w6,function(_wb){return E(_wa);})));},_wc=new T(function(){return B(unCStr("ACK"));}),_wd=6,_we=function(_wf){var _wg=new T(function(){return B(A1(_wf,_wd));});return new T1(1,B(_vi(_wc,function(_wh){return E(_wg);})));},_wi=new T(function(){return B(unCStr("BEL"));}),_wj=7,_wk=function(_wl){var _wm=new T(function(){return B(A1(_wl,_wj));});return new T1(1,B(_vi(_wi,function(_wn){return E(_wm);})));},_wo=new T(function(){return B(unCStr("BS"));}),_wp=8,_wq=function(_wr){var _ws=new T(function(){return B(A1(_wr,_wp));});return new T1(1,B(_vi(_wo,function(_wt){return E(_ws);})));},_wu=new T(function(){return B(unCStr("HT"));}),_wv=9,_ww=function(_wx){var _wy=new T(function(){return B(A1(_wx,_wv));});return new T1(1,B(_vi(_wu,function(_wz){return E(_wy);})));},_wA=new T(function(){return B(unCStr("LF"));}),_wB=10,_wC=function(_wD){var _wE=new T(function(){return B(A1(_wD,_wB));});return new T1(1,B(_vi(_wA,function(_wF){return E(_wE);})));},_wG=new T(function(){return B(unCStr("VT"));}),_wH=11,_wI=function(_wJ){var _wK=new T(function(){return B(A1(_wJ,_wH));});return new T1(1,B(_vi(_wG,function(_wL){return E(_wK);})));},_wM=new T(function(){return B(unCStr("FF"));}),_wN=12,_wO=function(_wP){var _wQ=new T(function(){return B(A1(_wP,_wN));});return new T1(1,B(_vi(_wM,function(_wR){return E(_wQ);})));},_wS=new T(function(){return B(unCStr("CR"));}),_wT=13,_wU=function(_wV){var _wW=new T(function(){return B(A1(_wV,_wT));});return new T1(1,B(_vi(_wS,function(_wX){return E(_wW);})));},_wY=new T(function(){return B(unCStr("SI"));}),_wZ=15,_x0=function(_x1){var _x2=new T(function(){return B(A1(_x1,_wZ));});return new T1(1,B(_vi(_wY,function(_x3){return E(_x2);})));},_x4=new T(function(){return B(unCStr("DLE"));}),_x5=16,_x6=function(_x7){var _x8=new T(function(){return B(A1(_x7,_x5));});return new T1(1,B(_vi(_x4,function(_x9){return E(_x8);})));},_xa=new T(function(){return B(unCStr("DC1"));}),_xb=17,_xc=function(_xd){var _xe=new T(function(){return B(A1(_xd,_xb));});return new T1(1,B(_vi(_xa,function(_xf){return E(_xe);})));},_xg=new T(function(){return B(unCStr("DC2"));}),_xh=18,_xi=function(_xj){var _xk=new T(function(){return B(A1(_xj,_xh));});return new T1(1,B(_vi(_xg,function(_xl){return E(_xk);})));},_xm=new T(function(){return B(unCStr("DC3"));}),_xn=19,_xo=function(_xp){var _xq=new T(function(){return B(A1(_xp,_xn));});return new T1(1,B(_vi(_xm,function(_xr){return E(_xq);})));},_xs=new T(function(){return B(unCStr("DC4"));}),_xt=20,_xu=function(_xv){var _xw=new T(function(){return B(A1(_xv,_xt));});return new T1(1,B(_vi(_xs,function(_xx){return E(_xw);})));},_xy=new T(function(){return B(unCStr("NAK"));}),_xz=21,_xA=function(_xB){var _xC=new T(function(){return B(A1(_xB,_xz));});return new T1(1,B(_vi(_xy,function(_xD){return E(_xC);})));},_xE=new T(function(){return B(unCStr("SYN"));}),_xF=22,_xG=function(_xH){var _xI=new T(function(){return B(A1(_xH,_xF));});return new T1(1,B(_vi(_xE,function(_xJ){return E(_xI);})));},_xK=new T(function(){return B(unCStr("ETB"));}),_xL=23,_xM=function(_xN){var _xO=new T(function(){return B(A1(_xN,_xL));});return new T1(1,B(_vi(_xK,function(_xP){return E(_xO);})));},_xQ=new T(function(){return B(unCStr("CAN"));}),_xR=24,_xS=function(_xT){var _xU=new T(function(){return B(A1(_xT,_xR));});return new T1(1,B(_vi(_xQ,function(_xV){return E(_xU);})));},_xW=new T(function(){return B(unCStr("EM"));}),_xX=25,_xY=function(_xZ){var _y0=new T(function(){return B(A1(_xZ,_xX));});return new T1(1,B(_vi(_xW,function(_y1){return E(_y0);})));},_y2=new T(function(){return B(unCStr("SUB"));}),_y3=26,_y4=function(_y5){var _y6=new T(function(){return B(A1(_y5,_y3));});return new T1(1,B(_vi(_y2,function(_y7){return E(_y6);})));},_y8=new T(function(){return B(unCStr("ESC"));}),_y9=27,_ya=function(_yb){var _yc=new T(function(){return B(A1(_yb,_y9));});return new T1(1,B(_vi(_y8,function(_yd){return E(_yc);})));},_ye=new T(function(){return B(unCStr("FS"));}),_yf=28,_yg=function(_yh){var _yi=new T(function(){return B(A1(_yh,_yf));});return new T1(1,B(_vi(_ye,function(_yj){return E(_yi);})));},_yk=new T(function(){return B(unCStr("GS"));}),_yl=29,_ym=function(_yn){var _yo=new T(function(){return B(A1(_yn,_yl));});return new T1(1,B(_vi(_yk,function(_yp){return E(_yo);})));},_yq=new T(function(){return B(unCStr("RS"));}),_yr=30,_ys=function(_yt){var _yu=new T(function(){return B(A1(_yt,_yr));});return new T1(1,B(_vi(_yq,function(_yv){return E(_yu);})));},_yw=new T(function(){return B(unCStr("US"));}),_yx=31,_yy=function(_yz){var _yA=new T(function(){return B(A1(_yz,_yx));});return new T1(1,B(_vi(_yw,function(_yB){return E(_yA);})));},_yC=new T(function(){return B(unCStr("SP"));}),_yD=32,_yE=function(_yF){var _yG=new T(function(){return B(A1(_yF,_yD));});return new T1(1,B(_vi(_yC,function(_yH){return E(_yG);})));},_yI=new T(function(){return B(unCStr("DEL"));}),_yJ=127,_yK=function(_yL){var _yM=new T(function(){return B(A1(_yL,_yJ));});return new T1(1,B(_vi(_yI,function(_yN){return E(_yM);})));},_yO=new T2(1,_yK,_4),_yP=new T2(1,_yE,_yO),_yQ=new T2(1,_yy,_yP),_yR=new T2(1,_ys,_yQ),_yS=new T2(1,_ym,_yR),_yT=new T2(1,_yg,_yS),_yU=new T2(1,_ya,_yT),_yV=new T2(1,_y4,_yU),_yW=new T2(1,_xY,_yV),_yX=new T2(1,_xS,_yW),_yY=new T2(1,_xM,_yX),_yZ=new T2(1,_xG,_yY),_z0=new T2(1,_xA,_yZ),_z1=new T2(1,_xu,_z0),_z2=new T2(1,_xo,_z1),_z3=new T2(1,_xi,_z2),_z4=new T2(1,_xc,_z3),_z5=new T2(1,_x6,_z4),_z6=new T2(1,_x0,_z5),_z7=new T2(1,_wU,_z6),_z8=new T2(1,_wO,_z7),_z9=new T2(1,_wI,_z8),_za=new T2(1,_wC,_z9),_zb=new T2(1,_ww,_za),_zc=new T2(1,_wq,_zb),_zd=new T2(1,_wk,_zc),_ze=new T2(1,_we,_zd),_zf=new T2(1,_w8,_ze),_zg=new T2(1,_w2,_zf),_zh=new T2(1,_vW,_zg),_zi=new T2(1,_vQ,_zh),_zj=new T2(1,_vK,_zi),_zk=new T2(1,_vG,_zj),_zl=new T(function(){return B(_va(_zk));}),_zm=34,_zn=new T1(0,1114111),_zo=92,_zp=39,_zq=function(_zr){var _zs=new T(function(){return B(A1(_zr,_wj));}),_zt=new T(function(){return B(A1(_zr,_wp));}),_zu=new T(function(){return B(A1(_zr,_wv));}),_zv=new T(function(){return B(A1(_zr,_wB));}),_zw=new T(function(){return B(A1(_zr,_wH));}),_zx=new T(function(){return B(A1(_zr,_wN));}),_zy=new T(function(){return B(A1(_zr,_wT));}),_zz=new T(function(){return B(A1(_zr,_zo));}),_zA=new T(function(){return B(A1(_zr,_zp));}),_zB=new T(function(){return B(A1(_zr,_zm));}),_zC=new T(function(){var _zD=function(_zE){var _zF=new T(function(){return B(_nh(E(_zE)));}),_zG=function(_zH){var _zI=B(_u8(_zF,_zH));if(!B(_v0(_zI,_zn))){return new T0(2);}else{return new F(function(){return A1(_zr,new T(function(){var _zJ=B(_nx(_zI));if(_zJ>>>0>1114111){return B(_es(_zJ));}else{return _zJ;}}));});}};return new T1(1,B(_sj(_zE,_zG)));},_zK=new T(function(){var _zL=new T(function(){return B(A1(_zr,_yx));}),_zM=new T(function(){return B(A1(_zr,_yr));}),_zN=new T(function(){return B(A1(_zr,_yl));}),_zO=new T(function(){return B(A1(_zr,_yf));}),_zP=new T(function(){return B(A1(_zr,_y9));}),_zQ=new T(function(){return B(A1(_zr,_y3));}),_zR=new T(function(){return B(A1(_zr,_xX));}),_zS=new T(function(){return B(A1(_zr,_xR));}),_zT=new T(function(){return B(A1(_zr,_xL));}),_zU=new T(function(){return B(A1(_zr,_xF));}),_zV=new T(function(){return B(A1(_zr,_xz));}),_zW=new T(function(){return B(A1(_zr,_xt));}),_zX=new T(function(){return B(A1(_zr,_xn));}),_zY=new T(function(){return B(A1(_zr,_xh));}),_zZ=new T(function(){return B(A1(_zr,_xb));}),_A0=new T(function(){return B(A1(_zr,_x5));}),_A1=new T(function(){return B(A1(_zr,_wZ));}),_A2=new T(function(){return B(A1(_zr,_vv));}),_A3=new T(function(){return B(A1(_zr,_wd));}),_A4=new T(function(){return B(A1(_zr,_w7));}),_A5=new T(function(){return B(A1(_zr,_w1));}),_A6=new T(function(){return B(A1(_zr,_vV));}),_A7=new T(function(){return B(A1(_zr,_vP));}),_A8=new T(function(){return B(A1(_zr,_vB));}),_A9=new T(function(){return B(A1(_zr,_vJ));}),_Aa=function(_Ab){switch(E(_Ab)){case 64:return E(_A9);case 65:return E(_A8);case 66:return E(_A7);case 67:return E(_A6);case 68:return E(_A5);case 69:return E(_A4);case 70:return E(_A3);case 71:return E(_zs);case 72:return E(_zt);case 73:return E(_zu);case 74:return E(_zv);case 75:return E(_zw);case 76:return E(_zx);case 77:return E(_zy);case 78:return E(_A2);case 79:return E(_A1);case 80:return E(_A0);case 81:return E(_zZ);case 82:return E(_zY);case 83:return E(_zX);case 84:return E(_zW);case 85:return E(_zV);case 86:return E(_zU);case 87:return E(_zT);case 88:return E(_zS);case 89:return E(_zR);case 90:return E(_zQ);case 91:return E(_zP);case 92:return E(_zO);case 93:return E(_zN);case 94:return E(_zM);case 95:return E(_zL);default:return new T0(2);}};return B(_qj(new T1(0,function(_Ac){return (E(_Ac)==94)?E(new T1(0,_Aa)):new T0(2);}),new T(function(){return B(A1(_zl,_zr));})));});return B(_qj(new T1(1,B(_rC(_uW,_uY,_zD))),_zK));});return new F(function(){return _qj(new T1(0,function(_Ad){switch(E(_Ad)){case 34:return E(_zB);case 39:return E(_zA);case 92:return E(_zz);case 97:return E(_zs);case 98:return E(_zt);case 102:return E(_zx);case 110:return E(_zv);case 114:return E(_zy);case 116:return E(_zu);case 118:return E(_zw);default:return new T0(2);}}),_zC);});},_Ae=function(_Af){return new F(function(){return A1(_Af,_5);});},_Ag=function(_Ah){var _Ai=E(_Ah);if(!_Ai._){return E(_Ae);}else{var _Aj=E(_Ai.a),_Ak=_Aj>>>0,_Al=new T(function(){return B(_Ag(_Ai.b));});if(_Ak>887){var _Am=u_iswspace(_Aj);if(!E(_Am)){return E(_Ae);}else{var _An=function(_Ao){var _Ap=new T(function(){return B(A1(_Al,_Ao));});return new T1(0,function(_Aq){return E(_Ap);});};return E(_An);}}else{var _Ar=E(_Ak);if(_Ar==32){var _As=function(_At){var _Au=new T(function(){return B(A1(_Al,_At));});return new T1(0,function(_Av){return E(_Au);});};return E(_As);}else{if(_Ar-9>>>0>4){if(E(_Ar)==160){var _Aw=function(_Ax){var _Ay=new T(function(){return B(A1(_Al,_Ax));});return new T1(0,function(_Az){return E(_Ay);});};return E(_Aw);}else{return E(_Ae);}}else{var _AA=function(_AB){var _AC=new T(function(){return B(A1(_Al,_AB));});return new T1(0,function(_AD){return E(_AC);});};return E(_AA);}}}}},_AE=function(_AF){var _AG=new T(function(){return B(_AE(_AF));}),_AH=function(_AI){return (E(_AI)==92)?E(_AG):new T0(2);},_AJ=function(_AK){return E(new T1(0,_AH));},_AL=new T1(1,function(_AM){return new F(function(){return A2(_Ag,_AM,_AJ);});}),_AN=new T(function(){return B(_zq(function(_AO){return new F(function(){return A1(_AF,new T2(0,_AO,_uQ));});}));}),_AP=function(_AQ){var _AR=E(_AQ);if(_AR==38){return E(_AG);}else{var _AS=_AR>>>0;if(_AS>887){var _AT=u_iswspace(_AR);return (E(_AT)==0)?new T0(2):E(_AL);}else{var _AU=E(_AS);return (_AU==32)?E(_AL):(_AU-9>>>0>4)?(E(_AU)==160)?E(_AL):new T0(2):E(_AL);}}};return new F(function(){return _qj(new T1(0,function(_AV){return (E(_AV)==92)?E(new T1(0,_AP)):new T0(2);}),new T1(0,function(_AW){var _AX=E(_AW);if(E(_AX)==92){return E(_AN);}else{return new F(function(){return A1(_AF,new T2(0,_AX,_uP));});}}));});},_AY=function(_AZ,_B0){var _B1=new T(function(){return B(A1(_B0,new T1(1,new T(function(){return B(A1(_AZ,_4));}))));}),_B2=function(_B3){var _B4=E(_B3),_B5=E(_B4.a);if(E(_B5)==34){if(!E(_B4.b)){return E(_B1);}else{return new F(function(){return _AY(function(_B6){return new F(function(){return A1(_AZ,new T2(1,_B5,_B6));});},_B0);});}}else{return new F(function(){return _AY(function(_B7){return new F(function(){return A1(_AZ,new T2(1,_B5,_B7));});},_B0);});}};return new F(function(){return _AE(_B2);});},_B8=new T(function(){return B(unCStr("_\'"));}),_B9=function(_Ba){var _Bb=u_iswalnum(_Ba);if(!E(_Bb)){return new F(function(){return _uH(_r8,_Ba,_B8);});}else{return true;}},_Bc=function(_Bd){return new F(function(){return _B9(E(_Bd));});},_Be=new T(function(){return B(unCStr(",;()[]{}`"));}),_Bf=new T(function(){return B(unCStr("=>"));}),_Bg=new T2(1,_Bf,_4),_Bh=new T(function(){return B(unCStr("~"));}),_Bi=new T2(1,_Bh,_Bg),_Bj=new T(function(){return B(unCStr("@"));}),_Bk=new T2(1,_Bj,_Bi),_Bl=new T(function(){return B(unCStr("->"));}),_Bm=new T2(1,_Bl,_Bk),_Bn=new T(function(){return B(unCStr("<-"));}),_Bo=new T2(1,_Bn,_Bm),_Bp=new T(function(){return B(unCStr("|"));}),_Bq=new T2(1,_Bp,_Bo),_Br=new T(function(){return B(unCStr("\\"));}),_Bs=new T2(1,_Br,_Bq),_Bt=new T(function(){return B(unCStr("="));}),_Bu=new T2(1,_Bt,_Bs),_Bv=new T(function(){return B(unCStr("::"));}),_Bw=new T2(1,_Bv,_Bu),_Bx=new T(function(){return B(unCStr(".."));}),_By=new T2(1,_Bx,_Bw),_Bz=function(_BA){var _BB=new T(function(){return B(A1(_BA,_sg));}),_BC=new T(function(){var _BD=new T(function(){var _BE=function(_BF){var _BG=new T(function(){return B(A1(_BA,new T1(0,_BF)));});return new T1(0,function(_BH){return (E(_BH)==39)?E(_BG):new T0(2);});};return B(_zq(_BE));}),_BI=function(_BJ){var _BK=E(_BJ);switch(E(_BK)){case 39:return new T0(2);case 92:return E(_BD);default:var _BL=new T(function(){return B(A1(_BA,new T1(0,_BK)));});return new T1(0,function(_BM){return (E(_BM)==39)?E(_BL):new T0(2);});}},_BN=new T(function(){var _BO=new T(function(){return B(_AY(_2j,_BA));}),_BP=new T(function(){var _BQ=new T(function(){var _BR=new T(function(){var _BS=function(_BT){var _BU=E(_BT),_BV=u_iswalpha(_BU);return (E(_BV)==0)?(E(_BU)==95)?new T1(1,B(_s2(_Bc,function(_BW){return new F(function(){return A1(_BA,new T1(3,new T2(1,_BU,_BW)));});}))):new T0(2):new T1(1,B(_s2(_Bc,function(_BX){return new F(function(){return A1(_BA,new T1(3,new T2(1,_BU,_BX)));});})));};return B(_qj(new T1(0,_BS),new T(function(){return new T1(1,B(_rC(_te,_uF,_BA)));})));}),_BY=function(_BZ){return (!B(_uH(_r8,_BZ,_uM)))?new T0(2):new T1(1,B(_s2(_uN,function(_C0){var _C1=new T2(1,_BZ,_C0);if(!B(_uH(_rh,_C1,_By))){return new F(function(){return A1(_BA,new T1(4,_C1));});}else{return new F(function(){return A1(_BA,new T1(2,_C1));});}})));};return B(_qj(new T1(0,_BY),_BR));});return B(_qj(new T1(0,function(_C2){if(!B(_uH(_r8,_C2,_Be))){return new T0(2);}else{return new F(function(){return A1(_BA,new T1(2,new T2(1,_C2,_4)));});}}),_BQ));});return B(_qj(new T1(0,function(_C3){return (E(_C3)==34)?E(_BO):new T0(2);}),_BP));});return B(_qj(new T1(0,function(_C4){return (E(_C4)==39)?E(new T1(0,_BI)):new T0(2);}),_BN));});return new F(function(){return _qj(new T1(1,function(_C5){return (E(_C5)._==0)?E(_BB):new T0(2);}),_BC);});},_C6=0,_C7=function(_C8,_C9){var _Ca=new T(function(){var _Cb=new T(function(){var _Cc=function(_Cd){var _Ce=new T(function(){var _Cf=new T(function(){return B(A1(_C9,_Cd));});return B(_Bz(function(_Cg){var _Ch=E(_Cg);return (_Ch._==2)?(!B(_qX(_Ch.a,_qW)))?new T0(2):E(_Cf):new T0(2);}));}),_Ci=function(_Cj){return E(_Ce);};return new T1(1,function(_Ck){return new F(function(){return A2(_Ag,_Ck,_Ci);});});};return B(A2(_C8,_C6,_Cc));});return B(_Bz(function(_Cl){var _Cm=E(_Cl);return (_Cm._==2)?(!B(_qX(_Cm.a,_qV)))?new T0(2):E(_Cb):new T0(2);}));}),_Cn=function(_Co){return E(_Ca);};return function(_Cp){return new F(function(){return A2(_Ag,_Cp,_Cn);});};},_Cq=function(_Cr,_Cs){var _Ct=function(_Cu){var _Cv=new T(function(){return B(A1(_Cr,_Cu));}),_Cw=function(_Cx){return new F(function(){return _qj(B(A1(_Cv,_Cx)),new T(function(){return new T1(1,B(_C7(_Ct,_Cx)));}));});};return E(_Cw);},_Cy=new T(function(){return B(A1(_Cr,_Cs));}),_Cz=function(_CA){return new F(function(){return _qj(B(A1(_Cy,_CA)),new T(function(){return new T1(1,B(_C7(_Ct,_CA)));}));});};return E(_Cz);},_CB=function(_CC,_CD){var _CE=function(_CF,_CG){var _CH=function(_CI){return new F(function(){return A1(_CG,new T(function(){return  -E(_CI);}));});},_CJ=new T(function(){return B(_Bz(function(_CK){return new F(function(){return A3(_CC,_CK,_CF,_CH);});}));}),_CL=function(_CM){return E(_CJ);},_CN=function(_CO){return new F(function(){return A2(_Ag,_CO,_CL);});},_CP=new T(function(){return B(_Bz(function(_CQ){var _CR=E(_CQ);if(_CR._==4){var _CS=E(_CR.a);if(!_CS._){return new F(function(){return A3(_CC,_CR,_CF,_CG);});}else{if(E(_CS.a)==45){if(!E(_CS.b)._){return E(new T1(1,_CN));}else{return new F(function(){return A3(_CC,_CR,_CF,_CG);});}}else{return new F(function(){return A3(_CC,_CR,_CF,_CG);});}}}else{return new F(function(){return A3(_CC,_CR,_CF,_CG);});}}));}),_CT=function(_CU){return E(_CP);};return new T1(1,function(_CV){return new F(function(){return A2(_Ag,_CV,_CT);});});};return new F(function(){return _Cq(_CE,_CD);});},_CW=new T(function(){return 1/0;}),_CX=function(_CY,_CZ){return new F(function(){return A1(_CZ,_CW);});},_D0=new T(function(){return 0/0;}),_D1=function(_D2,_D3){return new F(function(){return A1(_D3,_D0);});},_D4=new T(function(){return B(unCStr("NaN"));}),_D5=new T(function(){return B(unCStr("Infinity"));}),_D6=1024,_D7=-1021,_D8=function(_D9,_Da){while(1){var _Db=E(_D9);if(!_Db._){var _Dc=E(_Db.a);if(_Dc==(-2147483648)){_D9=new T1(1,I_fromInt(-2147483648));continue;}else{var _Dd=E(_Da);if(!_Dd._){return new T1(0,_Dc%_Dd.a);}else{_D9=new T1(1,I_fromInt(_Dc));_Da=_Dd;continue;}}}else{var _De=_Db.a,_Df=E(_Da);return (_Df._==0)?new T1(1,I_rem(_De,I_fromInt(_Df.a))):new T1(1,I_rem(_De,_Df.a));}}},_Dg=function(_Dh,_Di){if(!B(_pm(_Di,_ow))){return new F(function(){return _D8(_Dh,_Di);});}else{return E(_mk);}},_Dj=function(_Dk,_Dl){while(1){if(!B(_pm(_Dl,_ow))){var _Dm=_Dl,_Dn=B(_Dg(_Dk,_Dl));_Dk=_Dm;_Dl=_Dn;continue;}else{return E(_Dk);}}},_Do=function(_Dp){var _Dq=E(_Dp);if(!_Dq._){var _Dr=E(_Dq.a);return (_Dr==(-2147483648))?E(_tw):(_Dr<0)?new T1(0, -_Dr):E(_Dq);}else{var _Ds=_Dq.a;return (I_compareInt(_Ds,0)>=0)?E(_Dq):new T1(1,I_negate(_Ds));}},_Dt=function(_Du,_Dv){while(1){var _Dw=E(_Du);if(!_Dw._){var _Dx=E(_Dw.a);if(_Dx==(-2147483648)){_Du=new T1(1,I_fromInt(-2147483648));continue;}else{var _Dy=E(_Dv);if(!_Dy._){return new T1(0,quot(_Dx,_Dy.a));}else{_Du=new T1(1,I_fromInt(_Dx));_Dv=_Dy;continue;}}}else{var _Dz=_Dw.a,_DA=E(_Dv);return (_DA._==0)?new T1(0,I_toInt(I_quot(_Dz,I_fromInt(_DA.a)))):new T1(1,I_quot(_Dz,_DA.a));}}},_DB=5,_DC=new T(function(){return B(_mh(_DB));}),_DD=new T(function(){return die(_DC);}),_DE=function(_DF,_DG){if(!B(_pm(_DG,_ow))){var _DH=B(_Dj(B(_Do(_DF)),B(_Do(_DG))));return (!B(_pm(_DH,_ow)))?new T2(0,B(_Dt(_DF,_DH)),B(_Dt(_DG,_DH))):E(_mk);}else{return E(_DD);}},_DI=new T(function(){return B(_pm(_ox,_ow));}),_DJ=function(_DK,_DL){while(1){var _DM=E(_DK);if(!_DM._){var _DN=_DM.a,_DO=E(_DL);if(!_DO._){var _DP=_DO.a,_DQ=subC(_DN,_DP);if(!E(_DQ.b)){return new T1(0,_DQ.a);}else{_DK=new T1(1,I_fromInt(_DN));_DL=new T1(1,I_fromInt(_DP));continue;}}else{_DK=new T1(1,I_fromInt(_DN));_DL=_DO;continue;}}else{var _DR=E(_DL);if(!_DR._){_DK=_DM;_DL=new T1(1,I_fromInt(_DR.a));continue;}else{return new T1(1,I_sub(_DM.a,_DR.a));}}}},_DS=function(_DT,_DU,_DV){while(1){if(!E(_DI)){if(!B(_pm(B(_D8(_DU,_ox)),_ow))){if(!B(_pm(_DU,_nl))){var _DW=B(_nY(_DT,_DT)),_DX=B(_Dt(B(_DJ(_DU,_nl)),_ox)),_DY=B(_nY(_DT,_DV));_DT=_DW;_DU=_DX;_DV=_DY;continue;}else{return new F(function(){return _nY(_DT,_DV);});}}else{var _DW=B(_nY(_DT,_DT)),_DX=B(_Dt(_DU,_ox));_DT=_DW;_DU=_DX;continue;}}else{return E(_mk);}}},_DZ=function(_E0,_E1){while(1){if(!E(_DI)){if(!B(_pm(B(_D8(_E1,_ox)),_ow))){if(!B(_pm(_E1,_nl))){return new F(function(){return _DS(B(_nY(_E0,_E0)),B(_Dt(B(_DJ(_E1,_nl)),_ox)),_E0);});}else{return E(_E0);}}else{var _E2=B(_nY(_E0,_E0)),_E3=B(_Dt(_E1,_ox));_E0=_E2;_E1=_E3;continue;}}else{return E(_mk);}}},_E4=function(_E5,_E6){var _E7=E(_E5);if(!_E7._){var _E8=_E7.a,_E9=E(_E6);return (_E9._==0)?_E8<_E9.a:I_compareInt(_E9.a,_E8)>0;}else{var _Ea=_E7.a,_Eb=E(_E6);return (_Eb._==0)?I_compareInt(_Ea,_Eb.a)<0:I_compare(_Ea,_Eb.a)<0;}},_Ec=function(_Ed,_Ee){if(!B(_E4(_Ee,_ow))){if(!B(_pm(_Ee,_ow))){return new F(function(){return _DZ(_Ed,_Ee);});}else{return E(_nl);}}else{return E(_pe);}},_Ef=new T1(0,1),_Eg=new T1(0,0),_Eh=new T1(0,-1),_Ei=function(_Ej){var _Ek=E(_Ej);if(!_Ek._){var _El=_Ek.a;return (_El>=0)?(E(_El)==0)?E(_Eg):E(_tl):E(_Eh);}else{var _Em=I_compareInt(_Ek.a,0);return (_Em<=0)?(E(_Em)==0)?E(_Eg):E(_Eh):E(_tl);}},_En=function(_Eo,_Ep,_Eq){while(1){var _Er=E(_Eq);if(!_Er._){if(!B(_E4(_Eo,_tQ))){return new T2(0,B(_nY(_Ep,B(_Ec(_tB,_Eo)))),_nl);}else{var _Es=B(_Ec(_tB,B(_tx(_Eo))));return new F(function(){return _DE(B(_nY(_Ep,B(_Ei(_Es)))),B(_Do(_Es)));});}}else{var _Et=B(_DJ(_Eo,_Ef)),_Eu=B(_tn(B(_nY(_Ep,_tB)),B(_nh(E(_Er.a)))));_Eo=_Et;_Ep=_Eu;_Eq=_Er.b;continue;}}},_Ev=function(_Ew,_Ex){var _Ey=E(_Ew);if(!_Ey._){var _Ez=_Ey.a,_EA=E(_Ex);return (_EA._==0)?_Ez>=_EA.a:I_compareInt(_EA.a,_Ez)<=0;}else{var _EB=_Ey.a,_EC=E(_Ex);return (_EC._==0)?I_compareInt(_EB,_EC.a)>=0:I_compare(_EB,_EC.a)>=0;}},_ED=function(_EE){var _EF=E(_EE);if(!_EF._){var _EG=_EF.b;return new F(function(){return _DE(B(_nY(B(_tR(new T(function(){return B(_nh(E(_EF.a)));}),new T(function(){return B(_tC(_EG,0));},1),B(_G(_tH,_EG)))),_Ef)),_Ef);});}else{var _EH=_EF.a,_EI=_EF.c,_EJ=E(_EF.b);if(!_EJ._){var _EK=E(_EI);if(!_EK._){return new F(function(){return _DE(B(_nY(B(_u8(_tB,_EH)),_Ef)),_Ef);});}else{var _EL=_EK.a;if(!B(_Ev(_EL,_tQ))){var _EM=B(_Ec(_tB,B(_tx(_EL))));return new F(function(){return _DE(B(_nY(B(_u8(_tB,_EH)),B(_Ei(_EM)))),B(_Do(_EM)));});}else{return new F(function(){return _DE(B(_nY(B(_nY(B(_u8(_tB,_EH)),B(_Ec(_tB,_EL)))),_Ef)),_Ef);});}}}else{var _EN=_EJ.a,_EO=E(_EI);if(!_EO._){return new F(function(){return _En(_tQ,B(_u8(_tB,_EH)),_EN);});}else{return new F(function(){return _En(_EO.a,B(_u8(_tB,_EH)),_EN);});}}}},_EP=function(_EQ,_ER){while(1){var _ES=E(_ER);if(!_ES._){return __Z;}else{if(!B(A1(_EQ,_ES.a))){return E(_ES);}else{_ER=_ES.b;continue;}}}},_ET=function(_EU,_EV){var _EW=E(_EU);if(!_EW._){var _EX=_EW.a,_EY=E(_EV);return (_EY._==0)?_EX>_EY.a:I_compareInt(_EY.a,_EX)<0;}else{var _EZ=_EW.a,_F0=E(_EV);return (_F0._==0)?I_compareInt(_EZ,_F0.a)>0:I_compare(_EZ,_F0.a)>0;}},_F1=0,_F2=function(_F3){return new F(function(){return _hD(_F1,_F3);});},_F4=new T2(0,E(_tQ),E(_nl)),_F5=new T1(1,_F4),_F6=new T1(0,-2147483648),_F7=new T1(0,2147483647),_F8=function(_F9,_Fa,_Fb){var _Fc=E(_Fb);if(!_Fc._){return new T1(1,new T(function(){var _Fd=B(_ED(_Fc));return new T2(0,E(_Fd.a),E(_Fd.b));}));}else{var _Fe=E(_Fc.c);if(!_Fe._){return new T1(1,new T(function(){var _Ff=B(_ED(_Fc));return new T2(0,E(_Ff.a),E(_Ff.b));}));}else{var _Fg=_Fe.a;if(!B(_ET(_Fg,_F7))){if(!B(_E4(_Fg,_F6))){var _Fh=function(_Fi){var _Fj=_Fi+B(_nx(_Fg))|0;return (_Fj<=(E(_Fa)+3|0))?(_Fj>=(E(_F9)-3|0))?new T1(1,new T(function(){var _Fk=B(_ED(_Fc));return new T2(0,E(_Fk.a),E(_Fk.b));})):E(_F5):__Z;},_Fl=B(_EP(_F2,_Fc.a));if(!_Fl._){var _Fm=E(_Fc.b);if(!_Fm._){return E(_F5);}else{var _Fn=B(_6T(_F2,_Fm.a));if(!E(_Fn.b)._){return E(_F5);}else{return new F(function(){return _Fh( -B(_tC(_Fn.a,0)));});}}}else{return new F(function(){return _Fh(B(_tC(_Fl,0)));});}}else{return __Z;}}else{return __Z;}}}},_Fo=function(_Fp,_Fq){return new T0(2);},_Fr=new T1(0,1),_Fs=function(_Ft,_Fu){var _Fv=E(_Ft);if(!_Fv._){var _Fw=_Fv.a,_Fx=E(_Fu);if(!_Fx._){var _Fy=_Fx.a;return (_Fw!=_Fy)?(_Fw>_Fy)?2:0:1;}else{var _Fz=I_compareInt(_Fx.a,_Fw);return (_Fz<=0)?(_Fz>=0)?1:2:0;}}else{var _FA=_Fv.a,_FB=E(_Fu);if(!_FB._){var _FC=I_compareInt(_FA,_FB.a);return (_FC>=0)?(_FC<=0)?1:2:0;}else{var _FD=I_compare(_FA,_FB.a);return (_FD>=0)?(_FD<=0)?1:2:0;}}},_FE=function(_FF,_FG){while(1){var _FH=E(_FF);if(!_FH._){_FF=new T1(1,I_fromInt(_FH.a));continue;}else{return new T1(1,I_shiftLeft(_FH.a,_FG));}}},_FI=function(_FJ,_FK,_FL){if(!B(_pm(_FL,_pE))){var _FM=B(_pu(_FK,_FL)),_FN=_FM.a;switch(B(_Fs(B(_FE(_FM.b,1)),_FL))){case 0:return new F(function(){return _pi(_FN,_FJ);});break;case 1:if(!(B(_nx(_FN))&1)){return new F(function(){return _pi(_FN,_FJ);});}else{return new F(function(){return _pi(B(_tn(_FN,_Fr)),_FJ);});}break;default:return new F(function(){return _pi(B(_tn(_FN,_Fr)),_FJ);});}}else{return E(_mk);}},_FO=function(_FP){var _FQ=function(_FR,_FS){while(1){if(!B(_E4(_FR,_FP))){if(!B(_ET(_FR,_FP))){if(!B(_pm(_FR,_FP))){return new F(function(){return _7f("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_FS);}}else{return _FS-1|0;}}else{var _FT=B(_FE(_FR,1)),_FU=_FS+1|0;_FR=_FT;_FS=_FU;continue;}}};return new F(function(){return _FQ(_tl,0);});},_FV=function(_FW){var _FX=E(_FW);if(!_FX._){var _FY=_FX.a>>>0;if(!_FY){return -1;}else{var _FZ=function(_G0,_G1){while(1){if(_G0>=_FY){if(_G0<=_FY){if(_G0!=_FY){return new F(function(){return _7f("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_G1);}}else{return _G1-1|0;}}else{var _G2=imul(_G0,2)>>>0,_G3=_G1+1|0;_G0=_G2;_G1=_G3;continue;}}};return new F(function(){return _FZ(1,0);});}}else{return new F(function(){return _FO(_FX);});}},_G4=function(_G5){var _G6=E(_G5);if(!_G6._){var _G7=_G6.a>>>0;if(!_G7){return new T2(0,-1,0);}else{var _G8=function(_G9,_Ga){while(1){if(_G9>=_G7){if(_G9<=_G7){if(_G9!=_G7){return new F(function(){return _7f("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_Ga);}}else{return _Ga-1|0;}}else{var _Gb=imul(_G9,2)>>>0,_Gc=_Ga+1|0;_G9=_Gb;_Ga=_Gc;continue;}}};return new T2(0,B(_G8(1,0)),(_G7&_G7-1>>>0)>>>0&4294967295);}}else{var _Gd=_G6.a;return new T2(0,B(_FV(_G6)),I_compareInt(I_and(_Gd,I_sub(_Gd,I_fromInt(1))),0));}},_Ge=function(_Gf,_Gg){while(1){var _Gh=E(_Gf);if(!_Gh._){var _Gi=_Gh.a,_Gj=E(_Gg);if(!_Gj._){return new T1(0,(_Gi>>>0&_Gj.a>>>0)>>>0&4294967295);}else{_Gf=new T1(1,I_fromInt(_Gi));_Gg=_Gj;continue;}}else{var _Gk=E(_Gg);if(!_Gk._){_Gf=_Gh;_Gg=new T1(1,I_fromInt(_Gk.a));continue;}else{return new T1(1,I_and(_Gh.a,_Gk.a));}}}},_Gl=new T1(0,2),_Gm=function(_Gn,_Go){var _Gp=E(_Gn);if(!_Gp._){var _Gq=(_Gp.a>>>0&(2<<_Go>>>0)-1>>>0)>>>0,_Gr=1<<_Go>>>0;return (_Gr<=_Gq)?(_Gr>=_Gq)?1:2:0;}else{var _Gs=B(_Ge(_Gp,B(_DJ(B(_FE(_Gl,_Go)),_tl)))),_Gt=B(_FE(_tl,_Go));return (!B(_ET(_Gt,_Gs)))?(!B(_E4(_Gt,_Gs)))?1:2:0;}},_Gu=function(_Gv,_Gw){while(1){var _Gx=E(_Gv);if(!_Gx._){_Gv=new T1(1,I_fromInt(_Gx.a));continue;}else{return new T1(1,I_shiftRight(_Gx.a,_Gw));}}},_Gy=function(_Gz,_GA,_GB,_GC){var _GD=B(_G4(_GC)),_GE=_GD.a;if(!E(_GD.b)){var _GF=B(_FV(_GB));if(_GF<((_GE+_Gz|0)-1|0)){var _GG=_GE+(_Gz-_GA|0)|0;if(_GG>0){if(_GG>_GF){if(_GG<=(_GF+1|0)){if(!E(B(_G4(_GB)).b)){return 0;}else{return new F(function(){return _pi(_Fr,_Gz-_GA|0);});}}else{return 0;}}else{var _GH=B(_Gu(_GB,_GG));switch(B(_Gm(_GB,_GG-1|0))){case 0:return new F(function(){return _pi(_GH,_Gz-_GA|0);});break;case 1:if(!(B(_nx(_GH))&1)){return new F(function(){return _pi(_GH,_Gz-_GA|0);});}else{return new F(function(){return _pi(B(_tn(_GH,_Fr)),_Gz-_GA|0);});}break;default:return new F(function(){return _pi(B(_tn(_GH,_Fr)),_Gz-_GA|0);});}}}else{return new F(function(){return _pi(_GB,(_Gz-_GA|0)-_GG|0);});}}else{if(_GF>=_GA){var _GI=B(_Gu(_GB,(_GF+1|0)-_GA|0));switch(B(_Gm(_GB,_GF-_GA|0))){case 0:return new F(function(){return _pi(_GI,((_GF-_GE|0)+1|0)-_GA|0);});break;case 2:return new F(function(){return _pi(B(_tn(_GI,_Fr)),((_GF-_GE|0)+1|0)-_GA|0);});break;default:if(!(B(_nx(_GI))&1)){return new F(function(){return _pi(_GI,((_GF-_GE|0)+1|0)-_GA|0);});}else{return new F(function(){return _pi(B(_tn(_GI,_Fr)),((_GF-_GE|0)+1|0)-_GA|0);});}}}else{return new F(function(){return _pi(_GB, -_GE);});}}}else{var _GJ=B(_FV(_GB))-_GE|0,_GK=function(_GL){var _GM=function(_GN,_GO){if(!B(_v0(B(_FE(_GO,_GA)),_GN))){return new F(function(){return _FI(_GL-_GA|0,_GN,_GO);});}else{return new F(function(){return _FI((_GL-_GA|0)+1|0,_GN,B(_FE(_GO,1)));});}};if(_GL>=_GA){if(_GL!=_GA){return new F(function(){return _GM(_GB,new T(function(){return B(_FE(_GC,_GL-_GA|0));}));});}else{return new F(function(){return _GM(_GB,_GC);});}}else{return new F(function(){return _GM(new T(function(){return B(_FE(_GB,_GA-_GL|0));}),_GC);});}};if(_Gz>_GJ){return new F(function(){return _GK(_Gz);});}else{return new F(function(){return _GK(_GJ);});}}},_GP=new T(function(){return 0/0;}),_GQ=new T(function(){return -1/0;}),_GR=new T(function(){return 1/0;}),_GS=function(_GT,_GU){if(!B(_pm(_GU,_pE))){if(!B(_pm(_GT,_pE))){if(!B(_E4(_GT,_pE))){return new F(function(){return _Gy(-1021,53,_GT,_GU);});}else{return  -B(_Gy(-1021,53,B(_tx(_GT)),_GU));}}else{return E(_pD);}}else{return (!B(_pm(_GT,_pE)))?(!B(_E4(_GT,_pE)))?E(_GR):E(_GQ):E(_GP);}},_GV=function(_GW){var _GX=E(_GW);switch(_GX._){case 3:var _GY=_GX.a;return (!B(_qX(_GY,_D5)))?(!B(_qX(_GY,_D4)))?E(_Fo):E(_D1):E(_CX);case 5:var _GZ=B(_F8(_D7,_D6,_GX.a));if(!_GZ._){return E(_CX);}else{var _H0=new T(function(){var _H1=E(_GZ.a);return B(_GS(_H1.a,_H1.b));});return function(_H2,_H3){return new F(function(){return A1(_H3,_H0);});};}break;default:return E(_Fo);}},_H4=function(_H5){var _H6=function(_H7){return E(new T2(3,_H5,_rt));};return new T1(1,function(_H8){return new F(function(){return A2(_Ag,_H8,_H6);});});},_H9=new T(function(){return B(A3(_CB,_GV,_C6,_H4));}),_Ha=new T(function(){return B(_q9(_H9,_q7));}),_Hb=function(_Hc){while(1){var _Hd=B((function(_He){var _Hf=E(_He);if(!_Hf._){return __Z;}else{var _Hg=_Hf.b,_Hh=E(_Hf.a);if(!E(_Hh.b)._){return new T2(1,_Hh.a,new T(function(){return B(_Hb(_Hg));}));}else{_Hc=_Hg;return __continue;}}})(_Hc));if(_Hd!=__continue){return _Hd;}}},_Hi=new T(function(){return B(_Hb(_Ha));}),_Hj=new T(function(){return B(unCStr("Infinity"));}),_Hk=new T(function(){return B(_q9(_H9,_Hj));}),_Hl=new T(function(){return B(_Hb(_Hk));}),_Hm=0,_Hn=function(_Ho,_Hp,_Hq){return new F(function(){return _dz(_cM,new T2(0,_Hp,_Hq),_Ho,_dE);});},_Hr=function(_Hs,_Ht,_Hu){var _Hv=(_Hs+_Ht|0)-1|0;if(_Hs<=_Hv){var _Hw=function(_Hx){return new T2(1,new T(function(){var _Hy=E(_Hu),_Hz=_Hy.c,_HA=E(_Hy.a),_HB=E(_Hy.b);if(_HA>_Hx){return B(_Hn(_Hx,_HA,_HB));}else{if(_Hx>_HB){return B(_Hn(_Hx,_HA,_HB));}else{var _HC=_Hx-_HA|0;if(0>_HC){return B(_cv(_HC,_Hz));}else{if(_HC>=_Hz){return B(_cv(_HC,_Hz));}else{return _Hy.d["v"]["w8"][_HC];}}}}}),new T(function(){if(_Hx!=_Hv){return B(_Hw(_Hx+1|0));}else{return __Z;}}));};return new F(function(){return _Hw(_Hs);});}else{return __Z;}},_HD=function(_HE){var _HF=E(_HE);return new F(function(){return _Hr(_HF.a,_HF.b,_HF.c);});},_HG=function(_HH,_HI,_HJ,_HK){var _HL=new T(function(){var _HM=E(_HH),_HN=E(_HJ),_HO=_HN.a,_HP=_HN.b,_HQ=_HN.c,_HR=E(_HK);if((_HR+_HM|0)<=_HP){return new T2(0,new T(function(){var _HS=_HP-_HR|0;if(_HM>_HS){return new T3(0,_HO+_HR|0,_HS,_HQ);}else{return new T3(0,_HO+_HR|0,_HM,_HQ);}}),_HR+_HM|0);}else{return E(_ea);}}),_HT=new T(function(){return B(A1(_HI,new T(function(){return B(_HD(E(_HL).a));})));}),_HU=new T(function(){var _HV=E(_HT),_HW=_HV.d,_HX=_HV.e,_HY=_HV.f,_HZ=E(_HV.c);if(!_HZ){if(!B(_pm(_HW,_q1))){var _I0=B(_pF(_nO,Math.pow(2,E(_HX)-1|0))),_I1=_I0.a;if(E(_I0.b)>=0){return B(_pi(_HW,((1-E(_I1)|0)-E(_HY)|0)+1|0));}else{return B(_pi(_HW,((1-(E(_I1)-1|0)|0)-E(_HY)|0)+1|0));}}else{return E(_Hm);}}else{var _I2=E(_HX);if(_HZ!=(B(_pV(_q6,_I2))-1|0)){var _I3=B(_pF(_nO,Math.pow(2,_I2-1|0))),_I4=_I3.a;if(E(_I3.b)>=0){var _I5=E(_HY);return B(_pi(B(_tn(_HW,B(_FE(_q0,_I5)))),((_HZ+1|0)-E(_I4)|0)-_I5|0));}else{var _I6=E(_HY);return B(_pi(B(_tn(_HW,B(_FE(_q0,_I6)))),((_HZ+1|0)-(E(_I4)-1|0)|0)-_I6|0));}}else{if(!B(_pm(_HW,_q1))){var _I7=E(_Hi);if(!_I7._){return E(_q3);}else{if(!E(_I7.b)._){return E(_I7.a);}else{return E(_q5);}}}else{var _I8=E(_Hl);if(!_I8._){return E(_q3);}else{if(!E(_I8.b)._){return E(_I8.a);}else{return E(_q5);}}}}}});return new T2(0,new T(function(){if(!E(E(_HT).b)){return E(_HU);}else{return  -E(_HU);}}),new T(function(){return E(E(_HL).b);}));},_I9=new T(function(){return B(unCStr("This file was compiled with different version of GF"));}),_Ia=new T(function(){return B(err(_I9));}),_Ib=8,_Ic={_:0,a:_lG,b:_lB,c:_lx,d:_lx,e:_l1,f:_lm,g:_hm,h:_lt},_Id={_:0,a:_nr,b:_hx,c:_no,d:_nC,e:_nu,f:_nH,g:_nA},_Ie=new T2(0,_hD,_hG),_If={_:0,a:_Ie,b:_hX,c:_i9,d:_i6,e:_i3,f:_i0,g:_hK,h:_hP},_Ig=new T3(0,_Id,_If,_nm),_Ih={_:0,a:_Ig,b:_Ic,c:_mZ,d:_nd,e:_mt,f:_mV,g:_n5,h:_my,i:_nj},_Ii=new T1(0,1),_Ij=function(_Ik,_Il){var _Im=E(_Ik);return new T2(0,_Im,new T(function(){var _In=B(_Ij(B(_tn(_Im,_Il)),_Il));return new T2(1,_In.a,_In.b);}));},_Io=function(_Ip){var _Iq=B(_Ij(_Ip,_Ii));return new T2(1,_Iq.a,_Iq.b);},_Ir=function(_Is,_It){var _Iu=B(_Ij(_Is,new T(function(){return B(_DJ(_It,_Is));})));return new T2(1,_Iu.a,_Iu.b);},_Iv=new T1(0,0),_Iw=function(_Ix,_Iy,_Iz){if(!B(_Ev(_Iy,_Iv))){var _IA=function(_IB){return (!B(_E4(_IB,_Iz)))?new T2(1,_IB,new T(function(){return B(_IA(B(_tn(_IB,_Iy))));})):__Z;};return new F(function(){return _IA(_Ix);});}else{var _IC=function(_ID){return (!B(_ET(_ID,_Iz)))?new T2(1,_ID,new T(function(){return B(_IC(B(_tn(_ID,_Iy))));})):__Z;};return new F(function(){return _IC(_Ix);});}},_IE=function(_IF,_IG,_IH){return new F(function(){return _Iw(_IF,B(_DJ(_IG,_IF)),_IH);});},_II=function(_IJ,_IK){return new F(function(){return _Iw(_IJ,_Ii,_IK);});},_IL=function(_IM){return new F(function(){return _nx(_IM);});},_IN=function(_IO){return new F(function(){return _DJ(_IO,_Ii);});},_IP=function(_IQ){return new F(function(){return _tn(_IQ,_Ii);});},_IR=function(_IS){return new F(function(){return _nh(E(_IS));});},_IT={_:0,a:_IP,b:_IN,c:_IR,d:_IL,e:_Io,f:_Ir,g:_II,h:_IE},_IU=function(_IV,_IW){while(1){var _IX=E(_IV);if(!_IX._){var _IY=E(_IX.a);if(_IY==(-2147483648)){_IV=new T1(1,I_fromInt(-2147483648));continue;}else{var _IZ=E(_IW);if(!_IZ._){return new T1(0,B(_lK(_IY,_IZ.a)));}else{_IV=new T1(1,I_fromInt(_IY));_IW=_IZ;continue;}}}else{var _J0=_IX.a,_J1=E(_IW);return (_J1._==0)?new T1(1,I_div(_J0,I_fromInt(_J1.a))):new T1(1,I_div(_J0,_J1.a));}}},_J2=function(_J3,_J4){if(!B(_pm(_J4,_ow))){return new F(function(){return _IU(_J3,_J4);});}else{return E(_mk);}},_J5=function(_J6,_J7){while(1){var _J8=E(_J6);if(!_J8._){var _J9=E(_J8.a);if(_J9==(-2147483648)){_J6=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ja=E(_J7);if(!_Ja._){var _Jb=_Ja.a;return new T2(0,new T1(0,B(_lK(_J9,_Jb))),new T1(0,B(_mO(_J9,_Jb))));}else{_J6=new T1(1,I_fromInt(_J9));_J7=_Ja;continue;}}}else{var _Jc=E(_J7);if(!_Jc._){_J6=_J8;_J7=new T1(1,I_fromInt(_Jc.a));continue;}else{var _Jd=I_divMod(_J8.a,_Jc.a);return new T2(0,new T1(1,_Jd.a),new T1(1,_Jd.b));}}}},_Je=function(_Jf,_Jg){if(!B(_pm(_Jg,_ow))){var _Jh=B(_J5(_Jf,_Jg));return new T2(0,_Jh.a,_Jh.b);}else{return E(_mk);}},_Ji=function(_Jj,_Jk){while(1){var _Jl=E(_Jj);if(!_Jl._){var _Jm=E(_Jl.a);if(_Jm==(-2147483648)){_Jj=new T1(1,I_fromInt(-2147483648));continue;}else{var _Jn=E(_Jk);if(!_Jn._){return new T1(0,B(_mO(_Jm,_Jn.a)));}else{_Jj=new T1(1,I_fromInt(_Jm));_Jk=_Jn;continue;}}}else{var _Jo=_Jl.a,_Jp=E(_Jk);return (_Jp._==0)?new T1(1,I_mod(_Jo,I_fromInt(_Jp.a))):new T1(1,I_mod(_Jo,_Jp.a));}}},_Jq=function(_Jr,_Js){if(!B(_pm(_Js,_ow))){return new F(function(){return _Ji(_Jr,_Js);});}else{return E(_mk);}},_Jt=function(_Ju,_Jv){if(!B(_pm(_Jv,_ow))){return new F(function(){return _Dt(_Ju,_Jv);});}else{return E(_mk);}},_Jw=function(_Jx,_Jy){if(!B(_pm(_Jy,_ow))){var _Jz=B(_pu(_Jx,_Jy));return new T2(0,_Jz.a,_Jz.b);}else{return E(_mk);}},_JA=function(_JB){return E(_JB);},_JC=function(_JD){return E(_JD);},_JE={_:0,a:_tn,b:_DJ,c:_nY,d:_tx,e:_Do,f:_Ei,g:_JC},_JF=function(_JG,_JH){var _JI=E(_JG);if(!_JI._){var _JJ=_JI.a,_JK=E(_JH);return (_JK._==0)?_JJ!=_JK.a:(I_compareInt(_JK.a,_JJ)==0)?false:true;}else{var _JL=_JI.a,_JM=E(_JH);return (_JM._==0)?(I_compareInt(_JL,_JM.a)==0)?false:true:(I_compare(_JL,_JM.a)==0)?false:true;}},_JN=new T2(0,_pm,_JF),_JO=function(_JP,_JQ){return (!B(_v0(_JP,_JQ)))?E(_JP):E(_JQ);},_JR=function(_JS,_JT){return (!B(_v0(_JS,_JT)))?E(_JT):E(_JS);},_JU={_:0,a:_JN,b:_Fs,c:_E4,d:_v0,e:_ET,f:_Ev,g:_JO,h:_JR},_JV=function(_JW){return new T2(0,E(_JW),E(_nl));},_JX=new T3(0,_JE,_JU,_JV),_JY={_:0,a:_JX,b:_IT,c:_Jt,d:_Dg,e:_J2,f:_Jq,g:_Jw,h:_Je,i:_JA},_JZ=function(_K0,_K1){while(1){var _K2=E(_K0);if(!_K2._){return E(_K1);}else{var _K3=B(_tn(B(_FE(_K1,8)),B(_nh(E(_K2.a)&4294967295))));_K0=_K2.b;_K1=_K3;continue;}}},_K4=function(_K5,_K6,_K7){var _K8=imul(B(_tC(_K5,0)),8)|0,_K9=B(_pF(_JY,Math.pow(2,_K8-_K6|0))),_Ka=_K9.a;return (E(_K9.b)>=0)?E(B(_Gu(B(_Ge(B(_JZ(_K5,_q1)),B(_DJ(_Ka,_q0)))),_K8-_K7|0)).a):E(B(_Gu(B(_Ge(B(_JZ(_K5,_q1)),B(_DJ(B(_DJ(_Ka,_q0)),_q0)))),_K8-_K7|0)).a);},_Kb=new T(function(){return B(unCStr("head"));}),_Kc=new T(function(){return B(_cU(_Kb));}),_Kd=function(_Ke,_Kf,_Kg){return new T1(1,B(_K4(_Ke,E(_Kf),E(_Kg))));},_Kh=5,_Ki=new T(function(){return B(unCStr("Invalid length of floating-point value"));}),_Kj=new T(function(){return B(err(_Ki));}),_Kk=function(_Kl){var _Km=new T(function(){return imul(B(_tC(_Kl,0)),8)|0;}),_Kn=new T(function(){var _Ko=E(_Km);switch(_Ko){case 16:return E(_Kh);break;case 32:return E(_Ib);break;default:if(!B(_mO(_Ko,32))){var _Kp=B(_pF(_Ih,4*(Math.log(_Ko)/Math.log(2)))),_Kq=_Kp.a;if(E(_Kp.b)<=0){return E(_Kq)-13|0;}else{return (E(_Kq)+1|0)-13|0;}}else{return E(_Kj);}}}),_Kr=new T(function(){return 1+E(_Kn)|0;});return new T6(0,new T(function(){return B(_tC(_Kl,0));}),new T(function(){var _Ks=E(_Kl);if(!_Ks._){return E(_Kc);}else{if((E(_Ks.a)&128)>>>0==128){return 1;}else{return 0;}}}),new T(function(){return B(_nx(new T1(1,B(_K4(_Kl,1,E(_Kr))))));}),new T(function(){return B(_Kd(_Kl,_Kr,_Km));}),_Kn,new T(function(){return B(_hx(_Km,_Kr));}));},_Kt=function(_Ku){var _Kv=B(_Kk(_Ku));return new T6(0,_Kv.a,_Kv.b,_Kv.c,_Kv.d,_Kv.e,_Kv.f);},_Kw=function(_Kx,_Ky,_Kz,_KA){var _KB=B(_dU(_Kx,_Ky,_Kz,_KA)),_KC=_KB.b;switch(E(_KB.a)){case 0:var _KD=B(_e0(_Kx,_Ky,_Kz,E(_KC))),_KE=B(_eX(E(_KD.a)&4294967295,_eL,new T3(0,_Kx,_Ky,_Kz),_KD.b));return new T2(0,new T1(0,_KE.a),_KE.b);case 1:var _KF=B(_e0(_Kx,_Ky,_Kz,E(_KC)));return new T2(0,new T1(1,new T(function(){return E(_KF.a)&4294967295;})),_KF.b);case 2:var _KG=B(_HG(_Ib,_Kt,new T3(0,_Kx,_Ky,_Kz),_KC));return new T2(0,new T1(2,_KG.a),_KG.b);default:return E(_Ia);}},_KH=function(_KI,_KJ){var _KK=E(_KI),_KL=B(_Kw(_KK.a,_KK.b,_KK.c,E(_KJ)));return new T2(0,_KL.a,_KL.b);},_KM=function(_KN){switch(E(_KN)._){case 0:return E(_cg);case 1:return E(_cg);default:return E(_cg);}},_KO=new T2(0,_KM,_KH),_KP=function(_KQ){return E(_cg);},_KR=-4,_KS=function(_KT){var _KU=E(_KT);return (_KU._==0)?__Z:new T2(1,new T2(0,_KR,_KU.a),new T(function(){return B(_KS(_KU.b));}));},_KV=function(_KW,_KX,_KY,_KZ){var _L0=B(_e0(_KW,_KX,_KY,_KZ)),_L1=B(_eX(E(_L0.a)&4294967295,_j7,new T3(0,_KW,_KX,_KY),_L0.b)),_L2=B(_e0(_KW,_KX,_KY,E(_L1.b))),_L3=new T(function(){return new T2(0,new T(function(){return B(_KS(_L1.a));}),E(_L2.a)&4294967295);});return new T2(0,_L3,_L2.b);},_L4=function(_L5,_L6){var _L7=E(_L5),_L8=B(_KV(_L7.a,_L7.b,_L7.c,E(_L6)));return new T2(0,_L8.a,_L8.b);},_L9=function(_La,_Lb,_Lc,_Ld){var _Le=B(_dU(_La,_Lb,_Lc,_Ld)),_Lf=_Le.b;switch(E(_Le.a)){case 0:var _Lg=B(_e0(_La,_Lb,_Lc,E(_Lf))),_Lh=B(_e0(_La,_Lb,_Lc,E(_Lg.b))),_Li=B(_eX(E(_Lh.a)&4294967295,_L4,new T3(0,_La,_Lb,_Lc),_Lh.b));return new T2(0,new T(function(){return new T2(0,E(_Lg.a)&4294967295,_Li.a);}),_Li.b);case 1:var _Lj=B(_e0(_La,_Lb,_Lc,E(_Lf)));return new T2(0,new T(function(){return new T1(1,E(_Lj.a)&4294967295);}),_Lj.b);default:return E(_Ia);}},_Lk=function(_Ll,_Lm){var _Ln=E(_Ll),_Lo=B(_L9(_Ln.a,_Ln.b,_Ln.c,E(_Lm)));return new T2(0,_Lo.a,_Lo.b);},_Lp=new T(function(){return B(_7f("pgf/PGF/Binary.hs:(243,3)-(244,51)|function put"));}),_Lq=function(_Lr){switch(E(_Lr)._){case 0:return E(_cg);case 1:return E(_cg);default:return E(_Lp);}},_Ls=new T2(0,_Lq,_Lk),_Lt=new T0(1),_Lu=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_Lv=function(_Lw){return new F(function(){return err(_Lu);});},_Lx=new T(function(){return B(_Lv(_));}),_Ly=function(_Lz,_LA,_LB){var _LC=E(_LB);if(!_LC._){var _LD=_LC.a,_LE=E(_LA);if(!_LE._){var _LF=_LE.a,_LG=_LE.b;if(_LF<=(imul(3,_LD)|0)){return new T4(0,(1+_LF|0)+_LD|0,E(_Lz),E(_LE),E(_LC));}else{var _LH=E(_LE.c);if(!_LH._){var _LI=_LH.a,_LJ=E(_LE.d);if(!_LJ._){var _LK=_LJ.a,_LL=_LJ.b,_LM=_LJ.c;if(_LK>=(imul(2,_LI)|0)){var _LN=function(_LO){var _LP=E(_LJ.d);return (_LP._==0)?new T4(0,(1+_LF|0)+_LD|0,E(_LL),E(new T4(0,(1+_LI|0)+_LO|0,E(_LG),E(_LH),E(_LM))),E(new T4(0,(1+_LD|0)+_LP.a|0,E(_Lz),E(_LP),E(_LC)))):new T4(0,(1+_LF|0)+_LD|0,E(_LL),E(new T4(0,(1+_LI|0)+_LO|0,E(_LG),E(_LH),E(_LM))),E(new T4(0,1+_LD|0,E(_Lz),E(_Lt),E(_LC))));},_LQ=E(_LM);if(!_LQ._){return new F(function(){return _LN(_LQ.a);});}else{return new F(function(){return _LN(0);});}}else{return new T4(0,(1+_LF|0)+_LD|0,E(_LG),E(_LH),E(new T4(0,(1+_LD|0)+_LK|0,E(_Lz),E(_LJ),E(_LC))));}}else{return E(_Lx);}}else{return E(_Lx);}}}else{return new T4(0,1+_LD|0,E(_Lz),E(_Lt),E(_LC));}}else{var _LR=E(_LA);if(!_LR._){var _LS=_LR.a,_LT=_LR.b,_LU=_LR.d,_LV=E(_LR.c);if(!_LV._){var _LW=_LV.a,_LX=E(_LU);if(!_LX._){var _LY=_LX.a,_LZ=_LX.b,_M0=_LX.c;if(_LY>=(imul(2,_LW)|0)){var _M1=function(_M2){var _M3=E(_LX.d);return (_M3._==0)?new T4(0,1+_LS|0,E(_LZ),E(new T4(0,(1+_LW|0)+_M2|0,E(_LT),E(_LV),E(_M0))),E(new T4(0,1+_M3.a|0,E(_Lz),E(_M3),E(_Lt)))):new T4(0,1+_LS|0,E(_LZ),E(new T4(0,(1+_LW|0)+_M2|0,E(_LT),E(_LV),E(_M0))),E(new T4(0,1,E(_Lz),E(_Lt),E(_Lt))));},_M4=E(_M0);if(!_M4._){return new F(function(){return _M1(_M4.a);});}else{return new F(function(){return _M1(0);});}}else{return new T4(0,1+_LS|0,E(_LT),E(_LV),E(new T4(0,1+_LY|0,E(_Lz),E(_LX),E(_Lt))));}}else{return new T4(0,3,E(_LT),E(_LV),E(new T4(0,1,E(_Lz),E(_Lt),E(_Lt))));}}else{var _M5=E(_LU);return (_M5._==0)?new T4(0,3,E(_M5.b),E(new T4(0,1,E(_LT),E(_Lt),E(_Lt))),E(new T4(0,1,E(_Lz),E(_Lt),E(_Lt)))):new T4(0,2,E(_Lz),E(_LR),E(_Lt));}}else{return new T4(0,1,E(_Lz),E(_Lt),E(_Lt));}}},_M6=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_M7=function(_M8){return new F(function(){return err(_M6);});},_M9=new T(function(){return B(_M7(_));}),_Ma=function(_Mb,_Mc,_Md){var _Me=E(_Mc);if(!_Me._){var _Mf=_Me.a,_Mg=E(_Md);if(!_Mg._){var _Mh=_Mg.a,_Mi=_Mg.b;if(_Mh<=(imul(3,_Mf)|0)){return new T4(0,(1+_Mf|0)+_Mh|0,E(_Mb),E(_Me),E(_Mg));}else{var _Mj=E(_Mg.c);if(!_Mj._){var _Mk=_Mj.a,_Ml=_Mj.b,_Mm=_Mj.c,_Mn=E(_Mg.d);if(!_Mn._){var _Mo=_Mn.a;if(_Mk>=(imul(2,_Mo)|0)){var _Mp=function(_Mq){var _Mr=E(_Mb),_Ms=E(_Mj.d);return (_Ms._==0)?new T4(0,(1+_Mf|0)+_Mh|0,E(_Ml),E(new T4(0,(1+_Mf|0)+_Mq|0,E(_Mr),E(_Me),E(_Mm))),E(new T4(0,(1+_Mo|0)+_Ms.a|0,E(_Mi),E(_Ms),E(_Mn)))):new T4(0,(1+_Mf|0)+_Mh|0,E(_Ml),E(new T4(0,(1+_Mf|0)+_Mq|0,E(_Mr),E(_Me),E(_Mm))),E(new T4(0,1+_Mo|0,E(_Mi),E(_Lt),E(_Mn))));},_Mt=E(_Mm);if(!_Mt._){return new F(function(){return _Mp(_Mt.a);});}else{return new F(function(){return _Mp(0);});}}else{return new T4(0,(1+_Mf|0)+_Mh|0,E(_Mi),E(new T4(0,(1+_Mf|0)+_Mk|0,E(_Mb),E(_Me),E(_Mj))),E(_Mn));}}else{return E(_M9);}}else{return E(_M9);}}}else{return new T4(0,1+_Mf|0,E(_Mb),E(_Me),E(_Lt));}}else{var _Mu=E(_Md);if(!_Mu._){var _Mv=_Mu.a,_Mw=_Mu.b,_Mx=_Mu.d,_My=E(_Mu.c);if(!_My._){var _Mz=_My.a,_MA=_My.b,_MB=_My.c,_MC=E(_Mx);if(!_MC._){var _MD=_MC.a;if(_Mz>=(imul(2,_MD)|0)){var _ME=function(_MF){var _MG=E(_Mb),_MH=E(_My.d);return (_MH._==0)?new T4(0,1+_Mv|0,E(_MA),E(new T4(0,1+_MF|0,E(_MG),E(_Lt),E(_MB))),E(new T4(0,(1+_MD|0)+_MH.a|0,E(_Mw),E(_MH),E(_MC)))):new T4(0,1+_Mv|0,E(_MA),E(new T4(0,1+_MF|0,E(_MG),E(_Lt),E(_MB))),E(new T4(0,1+_MD|0,E(_Mw),E(_Lt),E(_MC))));},_MI=E(_MB);if(!_MI._){return new F(function(){return _ME(_MI.a);});}else{return new F(function(){return _ME(0);});}}else{return new T4(0,1+_Mv|0,E(_Mw),E(new T4(0,1+_Mz|0,E(_Mb),E(_Lt),E(_My))),E(_MC));}}else{return new T4(0,3,E(_MA),E(new T4(0,1,E(_Mb),E(_Lt),E(_Lt))),E(new T4(0,1,E(_Mw),E(_Lt),E(_Lt))));}}else{var _MJ=E(_Mx);return (_MJ._==0)?new T4(0,3,E(_Mw),E(new T4(0,1,E(_Mb),E(_Lt),E(_Lt))),E(_MJ)):new T4(0,2,E(_Mb),E(_Lt),E(_Mu));}}else{return new T4(0,1,E(_Mb),E(_Lt),E(_Lt));}}},_MK=function(_ML){return new T4(0,1,E(_ML),E(_Lt),E(_Lt));},_MM=function(_MN,_MO){var _MP=E(_MO);if(!_MP._){return new F(function(){return _Ly(_MP.b,B(_MM(_MN,_MP.c)),_MP.d);});}else{return new F(function(){return _MK(_MN);});}},_MQ=function(_MR,_MS){var _MT=E(_MS);if(!_MT._){return new F(function(){return _Ma(_MT.b,_MT.c,B(_MQ(_MR,_MT.d)));});}else{return new F(function(){return _MK(_MR);});}},_MU=function(_MV,_MW,_MX,_MY,_MZ){return new F(function(){return _Ma(_MX,_MY,B(_MQ(_MV,_MZ)));});},_N0=function(_N1,_N2,_N3,_N4,_N5){return new F(function(){return _Ly(_N3,B(_MM(_N1,_N4)),_N5);});},_N6=function(_N7,_N8,_N9,_Na,_Nb,_Nc){var _Nd=E(_N8);if(!_Nd._){var _Ne=_Nd.a,_Nf=_Nd.b,_Ng=_Nd.c,_Nh=_Nd.d;if((imul(3,_Ne)|0)>=_N9){if((imul(3,_N9)|0)>=_Ne){return new T4(0,(_Ne+_N9|0)+1|0,E(_N7),E(_Nd),E(new T4(0,_N9,E(_Na),E(_Nb),E(_Nc))));}else{return new F(function(){return _Ma(_Nf,_Ng,B(_N6(_N7,_Nh,_N9,_Na,_Nb,_Nc)));});}}else{return new F(function(){return _Ly(_Na,B(_Ni(_N7,_Ne,_Nf,_Ng,_Nh,_Nb)),_Nc);});}}else{return new F(function(){return _N0(_N7,_N9,_Na,_Nb,_Nc);});}},_Ni=function(_Nj,_Nk,_Nl,_Nm,_Nn,_No){var _Np=E(_No);if(!_Np._){var _Nq=_Np.a,_Nr=_Np.b,_Ns=_Np.c,_Nt=_Np.d;if((imul(3,_Nk)|0)>=_Nq){if((imul(3,_Nq)|0)>=_Nk){return new T4(0,(_Nk+_Nq|0)+1|0,E(_Nj),E(new T4(0,_Nk,E(_Nl),E(_Nm),E(_Nn))),E(_Np));}else{return new F(function(){return _Ma(_Nl,_Nm,B(_N6(_Nj,_Nn,_Nq,_Nr,_Ns,_Nt)));});}}else{return new F(function(){return _Ly(_Nr,B(_Ni(_Nj,_Nk,_Nl,_Nm,_Nn,_Ns)),_Nt);});}}else{return new F(function(){return _MU(_Nj,_Nk,_Nl,_Nm,_Nn);});}},_Nu=function(_Nv,_Nw,_Nx){var _Ny=E(_Nw);if(!_Ny._){var _Nz=_Ny.a,_NA=_Ny.b,_NB=_Ny.c,_NC=_Ny.d,_ND=E(_Nx);if(!_ND._){var _NE=_ND.a,_NF=_ND.b,_NG=_ND.c,_NH=_ND.d;if((imul(3,_Nz)|0)>=_NE){if((imul(3,_NE)|0)>=_Nz){return new T4(0,(_Nz+_NE|0)+1|0,E(_Nv),E(_Ny),E(_ND));}else{return new F(function(){return _Ma(_NA,_NB,B(_N6(_Nv,_NC,_NE,_NF,_NG,_NH)));});}}else{return new F(function(){return _Ly(_NF,B(_Ni(_Nv,_Nz,_NA,_NB,_NC,_NG)),_NH);});}}else{return new F(function(){return _MU(_Nv,_Nz,_NA,_NB,_NC);});}}else{return new F(function(){return _MM(_Nv,_Nx);});}},_NI=function(_NJ,_NK,_NL){var _NM=E(_NJ);if(_NM==1){return new T2(0,new T(function(){return new T4(0,1,E(_NK),E(_Lt),E(_Lt));}),_NL);}else{var _NN=B(_NI(_NM>>1,_NK,_NL)),_NO=_NN.a,_NP=E(_NN.b);if(!_NP._){return new T2(0,_NO,_4);}else{var _NQ=B(_NR(_NM>>1,_NP.b));return new T2(0,new T(function(){return B(_Nu(_NP.a,_NO,_NQ.a));}),_NQ.b);}}},_NR=function(_NS,_NT){var _NU=E(_NT);if(!_NU._){return new T2(0,_Lt,_4);}else{var _NV=_NU.a,_NW=_NU.b,_NX=E(_NS);if(_NX==1){return new T2(0,new T(function(){return new T4(0,1,E(_NV),E(_Lt),E(_Lt));}),_NW);}else{var _NY=B(_NI(_NX>>1,_NV,_NW)),_NZ=_NY.a,_O0=E(_NY.b);if(!_O0._){return new T2(0,_NZ,_4);}else{var _O1=B(_NR(_NX>>1,_O0.b));return new T2(0,new T(function(){return B(_Nu(_O0.a,_NZ,_O1.a));}),_O1.b);}}}},_O2=function(_O3,_O4,_O5){while(1){var _O6=E(_O5);if(!_O6._){return E(_O4);}else{var _O7=B(_NR(_O3,_O6.b)),_O8=_O3<<1,_O9=B(_Nu(_O6.a,_O4,_O7.a));_O3=_O8;_O4=_O9;_O5=_O7.b;continue;}}},_Oa=function(_Ob,_Oc,_Od,_Oe,_Of){var _Og=B(_e0(_Oc,_Od,_Oe,_Of)),_Oh=B(_eX(E(_Og.a)&4294967295,new T(function(){return B(_it(_Ob));}),new T3(0,_Oc,_Od,_Oe),_Og.b));return new T2(0,new T(function(){var _Oi=E(_Oh.a);if(!_Oi._){return new T0(1);}else{return B(_O2(1,new T4(0,1,E(_Oi.a),E(_Lt),E(_Lt)),_Oi.b));}}),_Oh.b);},_Oj=function(_Ok,_Ol){var _Om=E(_Ok),_On=B(_Oa(_Ls,_Om.a,_Om.b,_Om.c,E(_Ol)));return new T2(0,_On.a,_On.b);},_Oo=new T2(0,_KP,_Oj),_Op=function(_Oq){return E(_cg);},_Or=function(_Os,_Ot,_Ou,_Ov){var _Ow=B(_e0(_Os,_Ot,_Ou,_Ov));return new F(function(){return _eX(E(_Ow.a)&4294967295,_j7,new T3(0,_Os,_Ot,_Ou),_Ow.b);});},_Ox=function(_Oy,_Oz){var _OA=E(_Oy),_OB=B(_Or(_OA.a,_OA.b,_OA.c,E(_Oz)));return new T2(0,_OB.a,_OB.b);},_OC=new T2(0,_Op,_Ox),_OD=new T0(1),_OE=function(_OF,_OG,_OH,_OI,_OJ,_OK,_OL){while(1){var _OM=E(_OL);if(!_OM._){var _ON=(_OJ>>>0^_OM.a>>>0)>>>0,_OO=(_ON|_ON>>>1)>>>0,_OP=(_OO|_OO>>>2)>>>0,_OQ=(_OP|_OP>>>4)>>>0,_OR=(_OQ|_OQ>>>8)>>>0,_OS=(_OR|_OR>>>16)>>>0,_OT=(_OS^_OS>>>1)>>>0&4294967295;if(_OI>>>0<=_OT>>>0){return new F(function(){return _OU(_OF,_OG,_OH,new T3(0,_OJ,E(_OK),E(_OM)));});}else{var _OV=_OT>>>0,_OW=(_OJ>>>0&((_OV-1>>>0^4294967295)>>>0^_OV)>>>0)>>>0&4294967295,_OX=new T4(0,_OW,_OT,E(_OM.b),E(_OK));_OJ=_OW;_OK=_OX;_OL=_OM.c;continue;}}else{return new F(function(){return _OU(_OF,_OG,_OH,new T3(0,_OJ,E(_OK),E(_OD)));});}}},_OY=function(_OZ,_P0,_P1){while(1){var _P2=E(_P1);if(!_P2._){var _P3=_P2.a,_P4=_P2.b,_P5=_P2.c,_P6=(_P3>>>0^_OZ>>>0)>>>0,_P7=(_P6|_P6>>>1)>>>0,_P8=(_P7|_P7>>>2)>>>0,_P9=(_P8|_P8>>>4)>>>0,_Pa=(_P9|_P9>>>8)>>>0,_Pb=(_Pa|_Pa>>>16)>>>0,_Pc=(_Pb^_Pb>>>1)>>>0&4294967295,_Pd=(_OZ>>>0^_P3>>>0)>>>0,_Pe=(_Pd|_Pd>>>1)>>>0,_Pf=(_Pe|_Pe>>>2)>>>0,_Pg=(_Pf|_Pf>>>4)>>>0,_Ph=(_Pg|_Pg>>>8)>>>0,_Pi=(_Ph|_Ph>>>16)>>>0,_Pj=(_Pi^_Pi>>>1)>>>0;if(!((_P3>>>0&_Pc>>>0)>>>0)){var _Pk=_Pc>>>0,_Pl=(_OZ>>>0&((_Pj-1>>>0^4294967295)>>>0^_Pj)>>>0)>>>0&4294967295,_Pm=new T4(0,(_P3>>>0&((_Pk-1>>>0^4294967295)>>>0^_Pk)>>>0)>>>0&4294967295,_Pc,E(_P4),E(_P0));_OZ=_Pl;_P0=_Pm;_P1=_P5;continue;}else{var _Pn=_Pc>>>0,_Pl=(_OZ>>>0&((_Pj-1>>>0^4294967295)>>>0^_Pj)>>>0)>>>0&4294967295,_Pm=new T4(0,(_P3>>>0&((_Pn-1>>>0^4294967295)>>>0^_Pn)>>>0)>>>0&4294967295,_Pc,E(_P0),E(_P4));_OZ=_Pl;_P0=_Pm;_P1=_P5;continue;}}else{return E(_P0);}}},_OU=function(_Po,_Pp,_Pq,_Pr){var _Ps=E(_Pq);if(!_Ps._){return new F(function(){return _OY(_Po,new T2(1,_Po,_Pp),_Pr);});}else{var _Pt=E(_Ps.a),_Pu=E(_Pt.a),_Pv=(_Po>>>0^_Pu>>>0)>>>0,_Pw=(_Pv|_Pv>>>1)>>>0,_Px=(_Pw|_Pw>>>2)>>>0,_Py=(_Px|_Px>>>4)>>>0,_Pz=(_Py|_Py>>>8)>>>0,_PA=(_Pz|_Pz>>>16)>>>0;return new F(function(){return _OE(_Pu,_Pt.b,_Ps.b,(_PA^_PA>>>1)>>>0&4294967295,_Po,new T2(1,_Po,_Pp),_Pr);});}},_PB=function(_PC,_PD,_PE,_PF,_PG){var _PH=B(_e0(_PD,_PE,_PF,_PG)),_PI=function(_PJ,_PK){var _PL=E(_PJ),_PM=B(_e0(_PL.a,_PL.b,_PL.c,E(_PK))),_PN=B(A3(_it,_PC,_PL,_PM.b));return new T2(0,new T2(0,new T(function(){return E(_PM.a)&4294967295;}),_PN.a),_PN.b);},_PO=B(_eX(E(_PH.a)&4294967295,_PI,new T3(0,_PD,_PE,_PF),_PH.b));return new T2(0,new T(function(){var _PP=E(_PO.a);if(!_PP._){return new T0(2);}else{var _PQ=E(_PP.a);return B(_OU(E(_PQ.a),_PQ.b,_PP.b,_OD));}}),_PO.b);},_PR=function(_PS,_PT,_PU,_PV){var _PW=B(A3(_it,_PS,_PU,_PV)),_PX=B(A3(_it,_PT,_PU,_PW.b));return new T2(0,new T2(0,_PW.a,_PX.a),_PX.b);},_PY=new T0(1),_PZ=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_Q0=function(_Q1){return new F(function(){return err(_PZ);});},_Q2=new T(function(){return B(_Q0(_));}),_Q3=function(_Q4,_Q5,_Q6,_Q7){var _Q8=E(_Q7);if(!_Q8._){var _Q9=_Q8.a,_Qa=E(_Q6);if(!_Qa._){var _Qb=_Qa.a,_Qc=_Qa.b,_Qd=_Qa.c;if(_Qb<=(imul(3,_Q9)|0)){return new T5(0,(1+_Qb|0)+_Q9|0,E(_Q4),_Q5,E(_Qa),E(_Q8));}else{var _Qe=E(_Qa.d);if(!_Qe._){var _Qf=_Qe.a,_Qg=E(_Qa.e);if(!_Qg._){var _Qh=_Qg.a,_Qi=_Qg.b,_Qj=_Qg.c,_Qk=_Qg.d;if(_Qh>=(imul(2,_Qf)|0)){var _Ql=function(_Qm){var _Qn=E(_Qg.e);return (_Qn._==0)?new T5(0,(1+_Qb|0)+_Q9|0,E(_Qi),_Qj,E(new T5(0,(1+_Qf|0)+_Qm|0,E(_Qc),_Qd,E(_Qe),E(_Qk))),E(new T5(0,(1+_Q9|0)+_Qn.a|0,E(_Q4),_Q5,E(_Qn),E(_Q8)))):new T5(0,(1+_Qb|0)+_Q9|0,E(_Qi),_Qj,E(new T5(0,(1+_Qf|0)+_Qm|0,E(_Qc),_Qd,E(_Qe),E(_Qk))),E(new T5(0,1+_Q9|0,E(_Q4),_Q5,E(_PY),E(_Q8))));},_Qo=E(_Qk);if(!_Qo._){return new F(function(){return _Ql(_Qo.a);});}else{return new F(function(){return _Ql(0);});}}else{return new T5(0,(1+_Qb|0)+_Q9|0,E(_Qc),_Qd,E(_Qe),E(new T5(0,(1+_Q9|0)+_Qh|0,E(_Q4),_Q5,E(_Qg),E(_Q8))));}}else{return E(_Q2);}}else{return E(_Q2);}}}else{return new T5(0,1+_Q9|0,E(_Q4),_Q5,E(_PY),E(_Q8));}}else{var _Qp=E(_Q6);if(!_Qp._){var _Qq=_Qp.a,_Qr=_Qp.b,_Qs=_Qp.c,_Qt=_Qp.e,_Qu=E(_Qp.d);if(!_Qu._){var _Qv=_Qu.a,_Qw=E(_Qt);if(!_Qw._){var _Qx=_Qw.a,_Qy=_Qw.b,_Qz=_Qw.c,_QA=_Qw.d;if(_Qx>=(imul(2,_Qv)|0)){var _QB=function(_QC){var _QD=E(_Qw.e);return (_QD._==0)?new T5(0,1+_Qq|0,E(_Qy),_Qz,E(new T5(0,(1+_Qv|0)+_QC|0,E(_Qr),_Qs,E(_Qu),E(_QA))),E(new T5(0,1+_QD.a|0,E(_Q4),_Q5,E(_QD),E(_PY)))):new T5(0,1+_Qq|0,E(_Qy),_Qz,E(new T5(0,(1+_Qv|0)+_QC|0,E(_Qr),_Qs,E(_Qu),E(_QA))),E(new T5(0,1,E(_Q4),_Q5,E(_PY),E(_PY))));},_QE=E(_QA);if(!_QE._){return new F(function(){return _QB(_QE.a);});}else{return new F(function(){return _QB(0);});}}else{return new T5(0,1+_Qq|0,E(_Qr),_Qs,E(_Qu),E(new T5(0,1+_Qx|0,E(_Q4),_Q5,E(_Qw),E(_PY))));}}else{return new T5(0,3,E(_Qr),_Qs,E(_Qu),E(new T5(0,1,E(_Q4),_Q5,E(_PY),E(_PY))));}}else{var _QF=E(_Qt);return (_QF._==0)?new T5(0,3,E(_QF.b),_QF.c,E(new T5(0,1,E(_Qr),_Qs,E(_PY),E(_PY))),E(new T5(0,1,E(_Q4),_Q5,E(_PY),E(_PY)))):new T5(0,2,E(_Q4),_Q5,E(_Qp),E(_PY));}}else{return new T5(0,1,E(_Q4),_Q5,E(_PY),E(_PY));}}},_QG=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_QH=function(_QI){return new F(function(){return err(_QG);});},_QJ=new T(function(){return B(_QH(_));}),_QK=function(_QL,_QM,_QN,_QO){var _QP=E(_QN);if(!_QP._){var _QQ=_QP.a,_QR=E(_QO);if(!_QR._){var _QS=_QR.a,_QT=_QR.b,_QU=_QR.c;if(_QS<=(imul(3,_QQ)|0)){return new T5(0,(1+_QQ|0)+_QS|0,E(_QL),_QM,E(_QP),E(_QR));}else{var _QV=E(_QR.d);if(!_QV._){var _QW=_QV.a,_QX=_QV.b,_QY=_QV.c,_QZ=_QV.d,_R0=E(_QR.e);if(!_R0._){var _R1=_R0.a;if(_QW>=(imul(2,_R1)|0)){var _R2=function(_R3){var _R4=E(_QL),_R5=E(_QV.e);return (_R5._==0)?new T5(0,(1+_QQ|0)+_QS|0,E(_QX),_QY,E(new T5(0,(1+_QQ|0)+_R3|0,E(_R4),_QM,E(_QP),E(_QZ))),E(new T5(0,(1+_R1|0)+_R5.a|0,E(_QT),_QU,E(_R5),E(_R0)))):new T5(0,(1+_QQ|0)+_QS|0,E(_QX),_QY,E(new T5(0,(1+_QQ|0)+_R3|0,E(_R4),_QM,E(_QP),E(_QZ))),E(new T5(0,1+_R1|0,E(_QT),_QU,E(_PY),E(_R0))));},_R6=E(_QZ);if(!_R6._){return new F(function(){return _R2(_R6.a);});}else{return new F(function(){return _R2(0);});}}else{return new T5(0,(1+_QQ|0)+_QS|0,E(_QT),_QU,E(new T5(0,(1+_QQ|0)+_QW|0,E(_QL),_QM,E(_QP),E(_QV))),E(_R0));}}else{return E(_QJ);}}else{return E(_QJ);}}}else{return new T5(0,1+_QQ|0,E(_QL),_QM,E(_QP),E(_PY));}}else{var _R7=E(_QO);if(!_R7._){var _R8=_R7.a,_R9=_R7.b,_Ra=_R7.c,_Rb=_R7.e,_Rc=E(_R7.d);if(!_Rc._){var _Rd=_Rc.a,_Re=_Rc.b,_Rf=_Rc.c,_Rg=_Rc.d,_Rh=E(_Rb);if(!_Rh._){var _Ri=_Rh.a;if(_Rd>=(imul(2,_Ri)|0)){var _Rj=function(_Rk){var _Rl=E(_QL),_Rm=E(_Rc.e);return (_Rm._==0)?new T5(0,1+_R8|0,E(_Re),_Rf,E(new T5(0,1+_Rk|0,E(_Rl),_QM,E(_PY),E(_Rg))),E(new T5(0,(1+_Ri|0)+_Rm.a|0,E(_R9),_Ra,E(_Rm),E(_Rh)))):new T5(0,1+_R8|0,E(_Re),_Rf,E(new T5(0,1+_Rk|0,E(_Rl),_QM,E(_PY),E(_Rg))),E(new T5(0,1+_Ri|0,E(_R9),_Ra,E(_PY),E(_Rh))));},_Rn=E(_Rg);if(!_Rn._){return new F(function(){return _Rj(_Rn.a);});}else{return new F(function(){return _Rj(0);});}}else{return new T5(0,1+_R8|0,E(_R9),_Ra,E(new T5(0,1+_Rd|0,E(_QL),_QM,E(_PY),E(_Rc))),E(_Rh));}}else{return new T5(0,3,E(_Re),_Rf,E(new T5(0,1,E(_QL),_QM,E(_PY),E(_PY))),E(new T5(0,1,E(_R9),_Ra,E(_PY),E(_PY))));}}else{var _Ro=E(_Rb);return (_Ro._==0)?new T5(0,3,E(_R9),_Ra,E(new T5(0,1,E(_QL),_QM,E(_PY),E(_PY))),E(_Ro)):new T5(0,2,E(_QL),_QM,E(_PY),E(_R7));}}else{return new T5(0,1,E(_QL),_QM,E(_PY),E(_PY));}}},_Rp=function(_Rq,_Rr){return new T5(0,1,E(_Rq),_Rr,E(_PY),E(_PY));},_Rs=function(_Rt,_Ru,_Rv){var _Rw=E(_Rv);if(!_Rw._){return new F(function(){return _QK(_Rw.b,_Rw.c,_Rw.d,B(_Rs(_Rt,_Ru,_Rw.e)));});}else{return new F(function(){return _Rp(_Rt,_Ru);});}},_Rx=function(_Ry,_Rz,_RA){var _RB=E(_RA);if(!_RB._){return new F(function(){return _Q3(_RB.b,_RB.c,B(_Rx(_Ry,_Rz,_RB.d)),_RB.e);});}else{return new F(function(){return _Rp(_Ry,_Rz);});}},_RC=function(_RD,_RE,_RF,_RG,_RH,_RI,_RJ){return new F(function(){return _Q3(_RG,_RH,B(_Rx(_RD,_RE,_RI)),_RJ);});},_RK=function(_RL,_RM,_RN,_RO,_RP,_RQ,_RR,_RS){var _RT=E(_RN);if(!_RT._){var _RU=_RT.a,_RV=_RT.b,_RW=_RT.c,_RX=_RT.d,_RY=_RT.e;if((imul(3,_RU)|0)>=_RO){if((imul(3,_RO)|0)>=_RU){return new T5(0,(_RU+_RO|0)+1|0,E(_RL),_RM,E(_RT),E(new T5(0,_RO,E(_RP),_RQ,E(_RR),E(_RS))));}else{return new F(function(){return _QK(_RV,_RW,_RX,B(_RK(_RL,_RM,_RY,_RO,_RP,_RQ,_RR,_RS)));});}}else{return new F(function(){return _Q3(_RP,_RQ,B(_RZ(_RL,_RM,_RU,_RV,_RW,_RX,_RY,_RR)),_RS);});}}else{return new F(function(){return _RC(_RL,_RM,_RO,_RP,_RQ,_RR,_RS);});}},_RZ=function(_S0,_S1,_S2,_S3,_S4,_S5,_S6,_S7){var _S8=E(_S7);if(!_S8._){var _S9=_S8.a,_Sa=_S8.b,_Sb=_S8.c,_Sc=_S8.d,_Sd=_S8.e;if((imul(3,_S2)|0)>=_S9){if((imul(3,_S9)|0)>=_S2){return new T5(0,(_S2+_S9|0)+1|0,E(_S0),_S1,E(new T5(0,_S2,E(_S3),_S4,E(_S5),E(_S6))),E(_S8));}else{return new F(function(){return _QK(_S3,_S4,_S5,B(_RK(_S0,_S1,_S6,_S9,_Sa,_Sb,_Sc,_Sd)));});}}else{return new F(function(){return _Q3(_Sa,_Sb,B(_RZ(_S0,_S1,_S2,_S3,_S4,_S5,_S6,_Sc)),_Sd);});}}else{return new F(function(){return _Rs(_S0,_S1,new T5(0,_S2,E(_S3),_S4,E(_S5),E(_S6)));});}},_Se=function(_Sf,_Sg,_Sh,_Si){var _Sj=E(_Sh);if(!_Sj._){var _Sk=_Sj.a,_Sl=_Sj.b,_Sm=_Sj.c,_Sn=_Sj.d,_So=_Sj.e,_Sp=E(_Si);if(!_Sp._){var _Sq=_Sp.a,_Sr=_Sp.b,_Ss=_Sp.c,_St=_Sp.d,_Su=_Sp.e;if((imul(3,_Sk)|0)>=_Sq){if((imul(3,_Sq)|0)>=_Sk){return new T5(0,(_Sk+_Sq|0)+1|0,E(_Sf),_Sg,E(_Sj),E(_Sp));}else{return new F(function(){return _QK(_Sl,_Sm,_Sn,B(_RK(_Sf,_Sg,_So,_Sq,_Sr,_Ss,_St,_Su)));});}}else{return new F(function(){return _Q3(_Sr,_Ss,B(_RZ(_Sf,_Sg,_Sk,_Sl,_Sm,_Sn,_So,_St)),_Su);});}}else{return new F(function(){return _Rs(_Sf,_Sg,_Sj);});}}else{return new F(function(){return _Rx(_Sf,_Sg,_Si);});}},_Sv=function(_Sw,_Sx,_Sy){var _Sz=E(_Sw);if(_Sz==1){var _SA=E(_Sx);return new T2(0,new T(function(){return new T5(0,1,E(_SA.a),_SA.b,E(_PY),E(_PY));}),_Sy);}else{var _SB=B(_Sv(_Sz>>1,_Sx,_Sy)),_SC=_SB.a,_SD=E(_SB.b);if(!_SD._){return new T2(0,_SC,_4);}else{var _SE=E(_SD.a),_SF=B(_SG(_Sz>>1,_SD.b));return new T2(0,new T(function(){return B(_Se(_SE.a,_SE.b,_SC,_SF.a));}),_SF.b);}}},_SG=function(_SH,_SI){var _SJ=E(_SI);if(!_SJ._){return new T2(0,_PY,_4);}else{var _SK=_SJ.a,_SL=_SJ.b,_SM=E(_SH);if(_SM==1){var _SN=E(_SK);return new T2(0,new T(function(){return new T5(0,1,E(_SN.a),_SN.b,E(_PY),E(_PY));}),_SL);}else{var _SO=B(_Sv(_SM>>1,_SK,_SL)),_SP=_SO.a,_SQ=E(_SO.b);if(!_SQ._){return new T2(0,_SP,_4);}else{var _SR=E(_SQ.a),_SS=B(_SG(_SM>>1,_SQ.b));return new T2(0,new T(function(){return B(_Se(_SR.a,_SR.b,_SP,_SS.a));}),_SS.b);}}}},_ST=function(_SU,_SV,_SW){while(1){var _SX=E(_SW);if(!_SX._){return E(_SV);}else{var _SY=E(_SX.a),_SZ=B(_SG(_SU,_SX.b)),_T0=_SU<<1,_T1=B(_Se(_SY.a,_SY.b,_SV,_SZ.a));_SU=_T0;_SV=_T1;_SW=_SZ.b;continue;}}},_T2=function(_T3,_T4,_T5,_T6,_T7,_T8){var _T9=B(_e0(_T5,_T6,_T7,_T8)),_Ta=B(_eX(E(_T9.a)&4294967295,function(_Tb,_Tc){return new F(function(){return _PR(_T3,_T4,_Tb,_Tc);});},new T3(0,_T5,_T6,_T7),_T9.b));return new T2(0,new T(function(){var _Td=E(_Ta.a);if(!_Td._){return new T0(1);}else{var _Te=E(_Td.a);return B(_ST(1,new T5(0,1,E(_Te.a),_Te.b,E(_PY),E(_PY)),_Td.b));}}),_Ta.b);},_Tf=new T0(2),_Tg=new T0(10),_Th=new T0(5),_Ti=new T0(9),_Tj=new T0(6),_Tk=new T0(7),_Tl=new T0(8),_Tm=function(_Tn,_To){var _Tp=E(_Tn),_Tq=B(_e0(_Tp.a,_Tp.b,_Tp.c,E(_To))),_Tr=B(_eX(E(_Tq.a)&4294967295,_eL,_Tp,_Tq.b));return new T2(0,_Tr.a,_Tr.b);},_Ts=function(_Tt,_Tu){var _Tv=E(_Tt),_Tw=_Tv.a,_Tx=_Tv.b,_Ty=_Tv.c,_Tz=B(_e0(_Tw,_Tx,_Ty,E(_Tu))),_TA=B(_eX(E(_Tz.a)&4294967295,_TB,_Tv,_Tz.b)),_TC=B(_e0(_Tw,_Tx,_Ty,E(_TA.b))),_TD=B(_eX(E(_TC.a)&4294967295,_Tm,_Tv,_TC.b));return new T2(0,new T2(0,_TA.a,_TD.a),_TD.b);},_TE=function(_TF,_TG,_TH,_TI){var _TJ=B(_dU(_TF,_TG,_TH,_TI)),_TK=_TJ.b;switch(E(_TJ.a)){case 0:var _TL=B(_e0(_TF,_TG,_TH,E(_TK))),_TM=B(_e0(_TF,_TG,_TH,E(_TL.b)));return new T2(0,new T(function(){return new T2(0,E(_TL.a)&4294967295,E(_TM.a)&4294967295);}),_TM.b);case 1:var _TN=B(_e0(_TF,_TG,_TH,E(_TK))),_TO=B(_e0(_TF,_TG,_TH,E(_TN.b)));return new T2(0,new T(function(){return new T2(1,E(_TN.a)&4294967295,E(_TO.a)&4294967295);}),_TO.b);case 2:var _TP=B(_e0(_TF,_TG,_TH,E(_TK))),_TQ=B(_e0(_TF,_TG,_TH,E(_TP.b)));return new T2(0,new T(function(){return new T2(2,E(_TP.a)&4294967295,E(_TQ.a)&4294967295);}),_TQ.b);case 3:var _TR=B(_e0(_TF,_TG,_TH,E(_TK))),_TS=B(_eX(E(_TR.a)&4294967295,_eL,new T3(0,_TF,_TG,_TH),_TR.b));return new T2(0,new T1(3,_TS.a),_TS.b);case 4:var _TT=B(_e0(_TF,_TG,_TH,E(_TK))),_TU=B(_eX(E(_TT.a)&4294967295,_TB,new T3(0,_TF,_TG,_TH),_TT.b)),_TV=B(_e0(_TF,_TG,_TH,E(_TU.b))),_TW=B(_eX(E(_TV.a)&4294967295,_Ts,new T3(0,_TF,_TG,_TH),_TV.b));return new T2(0,new T2(4,_TU.a,_TW.a),_TW.b);case 5:return new T2(0,_Th,_TK);case 6:return new T2(0,_Tk,_TK);case 7:return new T2(0,_Tj,_TK);case 8:return new T2(0,_Tl,_TK);case 9:return new T2(0,_Ti,_TK);case 10:return new T2(0,_Tg,_TK);default:return E(_Ia);}},_TB=function(_TX,_TY){var _TZ=E(_TX),_U0=B(_TE(_TZ.a,_TZ.b,_TZ.c,E(_TY)));return new T2(0,_U0.a,_U0.b);},_U1=new T(function(){return B(unCStr("putWord8 not implemented"));}),_U2=new T(function(){return B(err(_U1));}),_U3=function(_U4){switch(E(_U4)._){case 0:return E(_cg);case 1:return E(_cg);case 2:return E(_cg);case 3:return E(_cg);case 4:return E(_cg);case 5:return E(_U2);case 6:return E(_U2);case 7:return E(_U2);case 8:return E(_U2);case 9:return E(_U2);default:return E(_U2);}},_U5=new T2(0,_U3,_TB),_U6=function(_U7,_U8){var _U9=E(_U7),_Ua=B(_iC(_U5,_gV,_U9.a,_U9.b,_U9.c,E(_U8)));return new T2(0,_Ua.a,_Ua.b);},_Ub=new T(function(){return B(unCStr("MArray: undefined array element"));}),_Uc=new T(function(){return B(err(_Ub));}),_Ud=new T(function(){return B(unCStr("Negative range size"));}),_Ue=new T(function(){return B(err(_Ud));}),_Uf=function(_Ug,_Uh,_Ui,_Uj){var _Uk=B(_T2(_ep,_KO,_Ug,_Uh,_Ui,_Uj)),_Ul=B(_T2(_ep,_fg,_Ug,_Uh,_Ui,E(_Uk.b))),_Um=B(_e0(_Ug,_Uh,_Ui,E(_Ul.b))),_Un=E(_Um.a)&4294967295,_Uo=B(_il(_Un,_U6,new T3(0,_Ug,_Uh,_Ui),_Um.b)),_Up=B(_iC(_l0,_gV,_Ug,_Uh,_Ui,E(_Uo.b))),_Uq=B(_PB(_OC,_Ug,_Uh,_Ui,E(_Up.b))),_Ur=B(_PB(_OC,_Ug,_Uh,_Ui,E(_Uq.b))),_Us=B(_PB(_Oo,_Ug,_Uh,_Ui,E(_Ur.b))),_Ut=B(_T2(_ep,_j6,_Ug,_Uh,_Ui,E(_Us.b))),_Uu=B(_e0(_Ug,_Uh,_Ui,E(_Ut.b))),_Uv=new T(function(){var _Uw=new T(function(){var _Ux=function(_){var _Uy=_Un-1|0,_Uz=function(_UA){if(_UA>=0){var _UB=newArr(_UA,_Uc),_UC=_UB,_UD=function(_UE){var _UF=function(_UG,_UH,_){while(1){if(_UG!=_UE){var _UI=E(_UH);if(!_UI._){return _5;}else{var _=_UC[_UG]=_UI.a,_UJ=_UG+1|0;_UG=_UJ;_UH=_UI.b;continue;}}else{return _5;}}},_UK=B(_UF(0,_Uo.a,_));return new T4(0,E(_gY),E(_Uy),_UA,_UC);};if(0>_Uy){return new F(function(){return _UD(0);});}else{var _UL=_Uy+1|0;if(_UL>=0){return new F(function(){return _UD(_UL);});}else{return E(_gX);}}}else{return E(_Ue);}};if(0>_Uy){return new F(function(){return _Uz(0);});}else{return new F(function(){return _Uz(_Uy+1|0);});}};return B(_8O(_Ux));});return {_:0,a:_Uk.a,b:_Ul.a,c:_Up.a,d:_Uq.a,e:_Ur.a,f:_Uw,g:_Us.a,h:_Tf,i:_PY,j:_Ut.a,k:_Tf,l:E(_Uu.a)&4294967295};});return new T2(0,_Uv,_Uu.b);},_UM=function(_UN,_UO){var _UP=E(_UN),_UQ=B(_Uf(_UP.a,_UP.b,_UP.c,E(_UO)));return new T2(0,_UQ.a,_UQ.b);},_UR=function(_US){return E(_cg);},_UT=new T2(0,_UR,_UM),_UU=new T2(1,_cn,_4),_UV=function(_UW,_UX){var _UY=new T(function(){return B(A3(_cY,_cO,new T2(1,function(_UZ){return new F(function(){return _cp(0,_UX&4294967295,_UZ);});},new T2(1,function(_V0){return new F(function(){return _cp(0,E(_UW)&4294967295,_V0);});},_4)),_UU));});return new F(function(){return err(B(unAppCStr("Unsupported PGF version ",new T2(1,_co,_UY))));});},_V1=function(_V2,_V3){var _V4=new T(function(){var _V5=E(_V2),_V6=B(_dU(_V5.a,_V5.b,_V5.c,E(_V3)));return new T2(0,_V6.a,_V6.b);}),_V7=new T(function(){var _V8=E(_V2),_V9=B(_dU(_V8.a,_V8.b,_V8.c,E(E(_V4).b)));return new T2(0,_V9.a,_V9.b);});return new T2(0,new T(function(){return (E(E(_V4).a)<<8>>>0&65535|E(E(_V7).a))>>>0;}),new T(function(){return E(E(_V7).b);}));},_Va=function(_Vb){var _Vc=E(_Vb);return new T4(0,_Vc.a,_Vc.b,new T(function(){var _Vd=E(_Vc.c);if(!_Vd._){return __Z;}else{return new T1(1,new T2(0,_Vd.a,_4));}}),_Vc.d);},_Ve=function(_Vf){return E(_cg);},_Vg=0,_Vh=1,_Vi=function(_Vj,_Vk,_Vl,_Vm){var _Vn=B(_dU(_Vj,_Vk,_Vl,_Vm)),_Vo=_Vn.b;switch(E(_Vn.a)){case 0:var _Vp=B(_dU(_Vj,_Vk,_Vl,E(_Vo))),_Vq=_Vp.b;switch(E(_Vp.a)){case 0:var _Vr=B(_eb(_Vj,_Vk,_Vl,E(_Vq))),_Vs=B(_Vi(_Vj,_Vk,_Vl,E(_Vr.b)));return new T2(0,new T3(0,_Vg,_Vr.a,_Vs.a),_Vs.b);case 1:var _Vt=B(_eb(_Vj,_Vk,_Vl,E(_Vq))),_Vu=B(_Vi(_Vj,_Vk,_Vl,E(_Vt.b)));return new T2(0,new T3(0,_Vh,_Vt.a,_Vu.a),_Vu.b);default:return E(_Ia);}break;case 1:var _Vv=B(_Vi(_Vj,_Vk,_Vl,E(_Vo))),_Vw=B(_Vi(_Vj,_Vk,_Vl,E(_Vv.b)));return new T2(0,new T2(1,_Vv.a,_Vw.a),_Vw.b);case 2:var _Vx=B(_Kw(_Vj,_Vk,_Vl,E(_Vo)));return new T2(0,new T1(2,_Vx.a),_Vx.b);case 3:var _Vy=B(_e0(_Vj,_Vk,_Vl,E(_Vo)));return new T2(0,new T(function(){return new T1(3,E(_Vy.a)&4294967295);}),_Vy.b);case 4:var _Vz=B(_eb(_Vj,_Vk,_Vl,E(_Vo)));return new T2(0,new T1(4,_Vz.a),_Vz.b);case 5:var _VA=B(_e0(_Vj,_Vk,_Vl,E(_Vo)));return new T2(0,new T(function(){return new T1(5,E(_VA.a)&4294967295);}),_VA.b);case 6:var _VB=B(_Vi(_Vj,_Vk,_Vl,E(_Vo))),_VC=B(_VD(_Vj,_Vk,_Vl,E(_VB.b)));return new T2(0,new T2(6,_VB.a,_VC.a),_VC.b);case 7:var _VE=B(_Vi(_Vj,_Vk,_Vl,E(_Vo)));return new T2(0,new T1(7,_VE.a),_VE.b);default:return E(_Ia);}},_VF=function(_VG,_VH){var _VI=E(_VG),_VJ=B(_Vi(_VI.a,_VI.b,_VI.c,E(_VH)));return new T2(0,_VJ.a,_VJ.b);},_VK=function(_VL,_VM){var _VN=E(_VL),_VO=_VN.a,_VP=_VN.b,_VQ=_VN.c,_VR=B(_dU(_VO,_VP,_VQ,E(_VM))),_VS=_VR.b,_VT=function(_VU,_VV){var _VW=B(_eb(_VO,_VP,_VQ,_VV)),_VX=B(_VD(_VO,_VP,_VQ,E(_VW.b)));return new T2(0,new T3(0,_VU,_VW.a,_VX.a),_VX.b);};switch(E(_VR.a)){case 0:var _VY=B(_VT(_Vg,E(_VS)));return new T2(0,_VY.a,_VY.b);case 1:var _VZ=B(_VT(_Vh,E(_VS)));return new T2(0,_VZ.a,_VZ.b);default:return E(_Ia);}},_VD=function(_W0,_W1,_W2,_W3){var _W4=B(_e0(_W0,_W1,_W2,_W3)),_W5=B(_eX(E(_W4.a)&4294967295,_VK,new T3(0,_W0,_W1,_W2),_W4.b)),_W6=B(_eb(_W0,_W1,_W2,E(_W5.b))),_W7=B(_e0(_W0,_W1,_W2,E(_W6.b))),_W8=B(_eX(E(_W7.a)&4294967295,_VF,new T3(0,_W0,_W1,_W2),_W7.b));return new T2(0,new T3(0,_W5.a,_W6.a,_W8.a),_W8.b);},_W9=function(_Wa,_Wb){var _Wc=E(_Wa),_Wd=_Wc.a,_We=_Wc.b,_Wf=_Wc.c,_Wg=B(_dU(_Wd,_We,_Wf,E(_Wb))),_Wh=_Wg.b,_Wi=function(_Wj,_Wk){var _Wl=B(_eb(_Wd,_We,_Wf,_Wk)),_Wm=B(_VD(_Wd,_We,_Wf,E(_Wl.b)));return new T2(0,new T3(0,_Wj,_Wl.a,_Wm.a),_Wm.b);};switch(E(_Wg.a)){case 0:var _Wn=B(_Wi(_Vg,E(_Wh)));return new T2(0,_Wn.a,_Wn.b);case 1:var _Wo=B(_Wi(_Vh,E(_Wh)));return new T2(0,_Wo.a,_Wo.b);default:return E(_Ia);}},_Wp=function(_Wq,_Wr){var _Ws=B(_HG(_Ib,_Kt,_Wq,_Wr)),_Wt=E(_Wq),_Wu=B(_eb(_Wt.a,_Wt.b,_Wt.c,E(_Ws.b)));return new T2(0,new T2(0,_Ws.a,_Wu.a),_Wu.b);},_Wv=function(_Ww,_Wx,_Wy,_Wz){var _WA=B(_e0(_Ww,_Wx,_Wy,_Wz)),_WB=B(_eX(E(_WA.a)&4294967295,_W9,new T3(0,_Ww,_Wx,_Wy),_WA.b)),_WC=B(_e0(_Ww,_Wx,_Wy,E(_WB.b))),_WD=B(_eX(E(_WC.a)&4294967295,_Wp,new T3(0,_Ww,_Wx,_Wy),_WC.b)),_WE=B(_HG(_Ib,_Kt,new T3(0,_Ww,_Wx,_Wy),_WD.b));return new T2(0,new T3(0,_WB.a,_WD.a,_WE.a),_WE.b);},_WF=function(_WG,_WH){var _WI=E(_WG),_WJ=B(_Wv(_WI.a,_WI.b,_WI.c,E(_WH)));return new T2(0,_WJ.a,_WJ.b);},_WK=new T2(0,_Ve,_WF),_WL=function(_WM){return E(_cg);},_WN=new T0(4),_WO=function(_WP,_WQ,_WR){switch(E(_WP)){case 0:var _WS=E(_WQ),_WT=_WS.a,_WU=_WS.b,_WV=_WS.c,_WW=B(_eb(_WT,_WU,_WV,E(_WR))),_WX=B(_e0(_WT,_WU,_WV,E(_WW.b))),_WY=B(_eX(E(_WX.a)&4294967295,_WZ,_WS,_WX.b));return new T2(0,new T2(0,_WW.a,_WY.a),_WY.b);case 1:var _X0=E(_WQ),_X1=B(_eb(_X0.a,_X0.b,_X0.c,E(_WR)));return new T2(0,new T1(2,_X1.a),_X1.b);case 2:var _X2=E(_WQ),_X3=_X2.a,_X4=_X2.b,_X5=_X2.c,_X6=B(_eb(_X3,_X4,_X5,E(_WR))),_X7=B(_dU(_X3,_X4,_X5,E(_X6.b))),_X8=B(_WO(E(_X7.a),_X2,_X7.b));return new T2(0,new T2(3,_X6.a,_X8.a),_X8.b);case 3:return new T2(0,_WN,_WR);case 4:var _X9=E(_WQ),_Xa=B(_Kw(_X9.a,_X9.b,_X9.c,E(_WR)));return new T2(0,new T1(1,_Xa.a),_Xa.b);case 5:var _Xb=E(_WQ),_Xc=B(_dU(_Xb.a,_Xb.b,_Xb.c,E(_WR))),_Xd=B(_WO(E(_Xc.a),_Xb,_Xc.b));return new T2(0,new T1(5,_Xd.a),_Xd.b);case 6:var _Xe=E(_WQ),_Xf=B(_Vi(_Xe.a,_Xe.b,_Xe.c,E(_WR)));return new T2(0,new T1(6,_Xf.a),_Xf.b);default:return E(_Ia);}},_Xg=function(_Xh,_Xi,_Xj,_Xk){var _Xl=B(_dU(_Xh,_Xi,_Xj,_Xk));return new F(function(){return _WO(E(_Xl.a),new T3(0,_Xh,_Xi,_Xj),_Xl.b);});},_WZ=function(_Xm,_Xn){var _Xo=E(_Xm),_Xp=B(_Xg(_Xo.a,_Xo.b,_Xo.c,E(_Xn)));return new T2(0,_Xp.a,_Xp.b);},_Xq=function(_Xr,_Xs,_Xt,_Xu){var _Xv=B(_e0(_Xr,_Xs,_Xt,_Xu)),_Xw=B(_eX(E(_Xv.a)&4294967295,_WZ,new T3(0,_Xr,_Xs,_Xt),_Xv.b)),_Xx=B(_Vi(_Xr,_Xs,_Xt,E(_Xw.b)));return new T2(0,new T2(0,_Xw.a,_Xx.a),_Xx.b);},_Xy=function(_Xz,_XA){var _XB=E(_Xz),_XC=B(_Xq(_XB.a,_XB.b,_XB.c,E(_XA)));return new T2(0,_XC.a,_XC.b);},_XD=function(_XE,_XF,_XG,_XH){var _XI=B(_VD(_XE,_XF,_XG,_XH)),_XJ=_XI.a,_XK=B(_e0(_XE,_XF,_XG,E(_XI.b))),_XL=_XK.a,_XM=B(_dU(_XE,_XF,_XG,E(_XK.b))),_XN=_XM.b;if(!E(_XM.a)){var _XO=B(_HG(_Ib,_Kt,new T3(0,_XE,_XF,_XG),_XN));return new T2(0,new T4(0,_XJ,new T(function(){return E(_XL)&4294967295;}),_4l,_XO.a),_XO.b);}else{var _XP=B(_e0(_XE,_XF,_XG,E(_XN))),_XQ=B(_eX(E(_XP.a)&4294967295,_Xy,new T3(0,_XE,_XF,_XG),_XP.b)),_XR=B(_HG(_Ib,_Kt,new T3(0,_XE,_XF,_XG),_XQ.b));return new T2(0,new T4(0,_XJ,new T(function(){return E(_XL)&4294967295;}),new T1(1,_XQ.a),_XR.a),_XR.b);}},_XS=function(_XT,_XU){var _XV=E(_XT),_XW=B(_XD(_XV.a,_XV.b,_XV.c,E(_XU)));return new T2(0,_XW.a,_XW.b);},_XX=new T2(0,_WL,_XS),_XY=function(_XZ,_Y0){var _Y1=E(_Y0);return (_Y1._==0)?new T5(0,_Y1.a,E(_Y1.b),new T(function(){return B(A1(_XZ,_Y1.c));}),E(B(_XY(_XZ,_Y1.d))),E(B(_XY(_XZ,_Y1.e)))):new T0(1);},_Y2=function(_Y3,_Y4,_Y5,_Y6){var _Y7=B(_T2(_ep,_KO,_Y3,_Y4,_Y5,_Y6)),_Y8=B(_T2(_ep,_XX,_Y3,_Y4,_Y5,E(_Y7.b))),_Y9=B(_T2(_ep,_WK,_Y3,_Y4,_Y5,E(_Y8.b)));return new T2(0,new T3(0,_Y7.a,new T(function(){return B(_XY(_Va,_Y8.a));}),_Y9.a),_Y9.b);},_Ya=function(_Yb,_Yc,_Yd){var _Ye=E(_Yb);if(!_Ye._){return new T2(0,_4,_Yd);}else{var _Yf=new T(function(){return B(A2(_Ye.a,_Yc,_Yd));}),_Yg=B(_Ya(_Ye.b,_Yc,new T(function(){return E(E(_Yf).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_Yf).a);}),_Yg.a),_Yg.b);}},_Yh=function(_Yi,_Yj,_Yk,_Yl){if(0>=_Yi){return new F(function(){return _Ya(_4,_Yk,_Yl);});}else{var _Ym=function(_Yn){var _Yo=E(_Yn);return (_Yo==1)?E(new T2(1,_Yj,_4)):new T2(1,_Yj,new T(function(){return B(_Ym(_Yo-1|0));}));};return new F(function(){return _Ya(B(_Ym(_Yi)),_Yk,_Yl);});}},_Yp=function(_Yq,_Yr,_Ys){var _Yt=new T(function(){var _Yu=E(_Yr),_Yv=B(_e0(_Yu.a,_Yu.b,_Yu.c,E(_Ys))),_Yw=E(_Yv.a)&4294967295,_Yx=B(_Yh(_Yw,_Yq,_Yu,_Yv.b));return new T2(0,new T2(0,_Yw,_Yx.a),_Yx.b);});return new T2(0,new T(function(){return E(E(E(_Yt).a).b);}),new T(function(){return E(E(_Yt).b);}));},_Yy=function(_Yz,_YA,_YB,_YC){var _YD=new T(function(){var _YE=function(_YF,_YG){var _YH=new T(function(){return B(A2(_Yz,_YF,_YG));}),_YI=B(A2(_YA,_YF,new T(function(){return E(E(_YH).b);})));return new T2(0,new T2(0,new T(function(){return E(E(_YH).a);}),_YI.a),_YI.b);},_YJ=B(_Yp(_YE,_YB,_YC));return new T2(0,_YJ.a,_YJ.b);});return new T2(0,new T(function(){var _YK=E(E(_YD).a);if(!_YK._){return new T0(1);}else{var _YL=E(_YK.a);return B(_ST(1,new T5(0,1,E(_YL.a),_YL.b,E(_PY),E(_PY)),_YK.b));}}),new T(function(){return E(E(_YD).b);}));},_YM=new T(function(){return B(unCStr("Prelude.Enum.Bool.toEnum: bad argument"));}),_YN=new T(function(){return B(err(_YM));}),_YO=new T(function(){return B(unCStr(")"));}),_YP=function(_YQ){return new F(function(){return err(B(unAppCStr("Unable to read PGF file (",new T(function(){return B(_0(_YQ,_YO));}))));});},_YR=new T(function(){return B(unCStr("getLiteral"));}),_YS=new T(function(){return B(_YP(_YR));}),_YT=function(_YU,_YV,_YW,_YX){var _YY=B(_dU(_YU,_YV,_YW,_YX)),_YZ=_YY.b;switch(E(_YY.a)){case 0:var _Z0=B(_e0(_YU,_YV,_YW,E(_YZ))),_Z1=B(_eX(E(_Z0.a)&4294967295,_eL,new T3(0,_YU,_YV,_YW),_Z0.b));return new T2(0,new T1(0,_Z1.a),_Z1.b);case 1:var _Z2=B(_e0(_YU,_YV,_YW,E(_YZ)));return new T2(0,new T1(1,new T(function(){return E(_Z2.a)&4294967295;})),_Z2.b);case 2:var _Z3=B(_HG(_Ib,_Kt,new T3(0,_YU,_YV,_YW),_YZ));return new T2(0,new T1(2,_Z3.a),_Z3.b);default:return E(_YS);}},_Z4=new T(function(){return B(unCStr("getBindType"));}),_Z5=new T(function(){return B(_YP(_Z4));}),_Z6=new T(function(){return B(unCStr("getExpr"));}),_Z7=new T(function(){return B(_YP(_Z6));}),_Z8=function(_Z9,_Za,_Zb,_Zc){var _Zd=B(_dU(_Z9,_Za,_Zb,_Zc)),_Ze=_Zd.b;switch(E(_Zd.a)){case 0:var _Zf=B(_dU(_Z9,_Za,_Zb,E(_Ze))),_Zg=_Zf.b;switch(E(_Zf.a)){case 0:var _Zh=B(_eb(_Z9,_Za,_Zb,E(_Zg))),_Zi=B(_Z8(_Z9,_Za,_Zb,E(_Zh.b)));return new T2(0,new T3(0,_Vg,_Zh.a,_Zi.a),_Zi.b);case 1:var _Zj=B(_eb(_Z9,_Za,_Zb,E(_Zg))),_Zk=B(_Z8(_Z9,_Za,_Zb,E(_Zj.b)));return new T2(0,new T3(0,_Vh,_Zj.a,_Zk.a),_Zk.b);default:return E(_Z5);}break;case 1:var _Zl=B(_Z8(_Z9,_Za,_Zb,E(_Ze))),_Zm=B(_Z8(_Z9,_Za,_Zb,E(_Zl.b)));return new T2(0,new T2(1,_Zl.a,_Zm.a),_Zm.b);case 2:var _Zn=B(_YT(_Z9,_Za,_Zb,E(_Ze)));return new T2(0,new T1(2,_Zn.a),_Zn.b);case 3:var _Zo=B(_e0(_Z9,_Za,_Zb,E(_Ze)));return new T2(0,new T(function(){return new T1(3,E(_Zo.a)&4294967295);}),_Zo.b);case 4:var _Zp=B(_eb(_Z9,_Za,_Zb,E(_Ze)));return new T2(0,new T1(4,_Zp.a),_Zp.b);case 5:var _Zq=B(_e0(_Z9,_Za,_Zb,E(_Ze)));return new T2(0,new T(function(){return new T1(5,E(_Zq.a)&4294967295);}),_Zq.b);case 6:var _Zr=B(_Z8(_Z9,_Za,_Zb,E(_Ze))),_Zs=B(_Zt(_Z9,_Za,_Zb,_Zr.b));return new T2(0,new T2(6,_Zr.a,_Zs.a),_Zs.b);case 7:var _Zu=B(_Z8(_Z9,_Za,_Zb,E(_Ze)));return new T2(0,new T1(7,_Zu.a),_Zu.b);default:return E(_Z7);}},_Zv=function(_Zw,_Zx){var _Zy=E(_Zw),_Zz=B(_Z8(_Zy.a,_Zy.b,_Zy.c,E(_Zx)));return new T2(0,_Zz.a,_Zz.b);},_ZA=function(_ZB,_ZC,_ZD,_ZE){var _ZF=B(_dU(_ZB,_ZC,_ZD,_ZE)),_ZG=_ZF.b;switch(E(_ZF.a)){case 0:var _ZH=B(_eb(_ZB,_ZC,_ZD,E(_ZG))),_ZI=B(_Zt(_ZB,_ZC,_ZD,_ZH.b));return new T2(0,new T3(0,_Vg,_ZH.a,_ZI.a),_ZI.b);case 1:var _ZJ=B(_eb(_ZB,_ZC,_ZD,E(_ZG))),_ZK=B(_Zt(_ZB,_ZC,_ZD,_ZJ.b));return new T2(0,new T3(0,_Vh,_ZJ.a,_ZK.a),_ZK.b);default:return E(_Z5);}},_ZL=function(_ZM,_ZN){var _ZO=E(_ZM),_ZP=B(_ZA(_ZO.a,_ZO.b,_ZO.c,E(_ZN)));return new T2(0,_ZP.a,_ZP.b);},_Zt=function(_ZQ,_ZR,_ZS,_ZT){var _ZU=new T3(0,_ZQ,_ZR,_ZS),_ZV=B(_Yp(_ZL,_ZU,_ZT)),_ZW=B(_eb(_ZQ,_ZR,_ZS,E(_ZV.b))),_ZX=B(_Yp(_Zv,_ZU,_ZW.b));return new T2(0,new T3(0,_ZV.a,_ZW.a,_ZX.a),_ZX.b);},_ZY=new T(function(){return B(unCStr("getPatt"));}),_ZZ=new T(function(){return B(_YP(_ZY));}),_100=function(_101,_102,_103,_104){var _105=B(_dU(_101,_102,_103,_104)),_106=_105.b;switch(E(_105.a)){case 0:var _107=B(_eb(_101,_102,_103,E(_106))),_108=B(_Yp(_109,new T3(0,_101,_102,_103),_107.b));return new T2(0,new T2(0,_107.a,_108.a),_108.b);case 1:var _10a=B(_eb(_101,_102,_103,E(_106)));return new T2(0,new T1(2,_10a.a),_10a.b);case 2:var _10b=B(_eb(_101,_102,_103,E(_106))),_10c=B(_100(_101,_102,_103,E(_10b.b)));return new T2(0,new T2(3,_10b.a,_10c.a),_10c.b);case 3:return new T2(0,_WN,_106);case 4:var _10d=B(_YT(_101,_102,_103,E(_106)));return new T2(0,new T1(1,_10d.a),_10d.b);case 5:var _10e=B(_100(_101,_102,_103,E(_106)));return new T2(0,new T1(5,_10e.a),_10e.b);case 6:var _10f=B(_Z8(_101,_102,_103,E(_106)));return new T2(0,new T1(6,_10f.a),_10f.b);default:return E(_ZZ);}},_109=function(_10g,_10h){var _10i=E(_10g),_10j=B(_100(_10i.a,_10i.b,_10i.c,E(_10h)));return new T2(0,_10j.a,_10j.b);},_10k=function(_10l,_10m){var _10n=E(_10l),_10o=B(_Yp(_109,_10n,_10m)),_10p=B(_Z8(_10n.a,_10n.b,_10n.c,E(_10o.b)));return new T2(0,new T2(0,_10o.a,_10p.a),_10p.b);},_10q=function(_10r,_10s,_10t,_10u){var _10v=B(_Zt(_10r,_10s,_10t,_10u)),_10w=_10v.a,_10x=B(_e0(_10r,_10s,_10t,E(_10v.b))),_10y=_10x.a,_10z=B(_dU(_10r,_10s,_10t,E(_10x.b))),_10A=_10z.b;switch(E(_10z.a)&4294967295){case 0:var _10B=B(_HG(_Ib,_Kt,new T3(0,_10r,_10s,_10t),_10A));return new T2(0,new T4(0,_10w,new T(function(){return E(_10y)&4294967295;}),_4l,_10B.a),_10B.b);case 1:var _10C=new T3(0,_10r,_10s,_10t),_10D=new T(function(){var _10E=B(_Yp(_10k,_10C,_10A));return new T2(0,_10E.a,_10E.b);}),_10F=B(_HG(_Ib,_Kt,_10C,new T(function(){return E(E(_10D).b);},1)));return new T2(0,new T4(0,_10w,new T(function(){return E(_10y)&4294967295;}),new T1(1,new T(function(){return E(E(_10D).a);})),_10F.a),_10F.b);default:return E(_YN);}},_10G=function(_10H,_10I){var _10J=E(_10H),_10K=B(_10q(_10J.a,_10J.b,_10J.c,_10I));return new T2(0,_10K.a,_10K.b);},_10L=function(_10M,_10N){var _10O=E(_10M),_10P=B(_YT(_10O.a,_10O.b,_10O.c,E(_10N)));return new T2(0,_10P.a,_10P.b);},_10Q=function(_10R,_10S){var _10T=E(_10R),_10U=B(_eb(_10T.a,_10T.b,_10T.c,E(_10S)));return new T2(0,_10U.a,_10U.b);},_10V=function(_10W,_10X){while(1){var _10Y=E(_10W);if(!_10Y._){return (E(_10X)._==0)?1:0;}else{var _10Z=E(_10X);if(!_10Z._){return 2;}else{var _110=E(_10Y.a),_111=E(_10Z.a);if(_110!=_111){return (_110>_111)?2:0;}else{_10W=_10Y.b;_10X=_10Z.b;continue;}}}}},_112=function(_113,_114){return (B(_10V(_113,_114))==0)?true:false;},_115=function(_116,_117){return (B(_10V(_116,_117))==2)?false:true;},_118=function(_119,_11a){return (B(_10V(_119,_11a))==2)?true:false;},_11b=function(_11c,_11d){return (B(_10V(_11c,_11d))==0)?false:true;},_11e=function(_11f,_11g){return (B(_10V(_11f,_11g))==2)?E(_11f):E(_11g);},_11h=function(_11i,_11j){return (B(_10V(_11i,_11j))==2)?E(_11j):E(_11i);},_11k={_:0,a:_rh,b:_10V,c:_112,d:_115,e:_118,f:_11b,g:_11e,h:_11h},_11l=function(_11m){var _11n=E(_11m)&4294967295;if(_11n>>>0>1114111){return new F(function(){return _es(_11n);});}else{return _11n;}},_11o=function(_11p){var _11q=E(_11p);return (_11q._==0)?__Z:new T2(1,new T(function(){return B(_11l(_11q.a));}),new T(function(){return B(_11o(_11q.b));}));},_11r=function(_11s){var _11t=E(_11s);return (_11t._==0)?__Z:new T2(1,new T(function(){return B(_11l(_11t.a));}),new T(function(){return B(_11r(_11t.b));}));},_11u=function(_11v,_11w,_11x,_11y,_11z,_11A){return new F(function(){return _qX(B(_G(_11l,B(_Hr(_11v,_11w,_11x)))),B(_G(_11l,B(_Hr(_11y,_11z,_11A)))));});},_11B=function(_11C,_11D,_11E,_11F,_11G,_11H){return (!B(_11u(_11C,_11D,_11E,_11F,_11G,_11H)))?(B(_10V(B(_11r(new T(function(){return B(_Hr(_11C,_11D,_11E));}))),B(_11o(new T(function(){return B(_Hr(_11F,_11G,_11H));})))))==2)?2:0:1;},_11I=function(_11J,_11K,_11L,_11M,_11N,_11O){var _11P=new T3(0,_11K,_11L,_11M),_11Q=E(_11O);if(!_11Q._){var _11R=_11Q.c,_11S=_11Q.d,_11T=_11Q.e,_11U=E(_11Q.b);switch(B(_11B(_11K,_11L,_11M,_11U.a,_11U.b,_11U.c))){case 0:return new F(function(){return _Q3(_11U,_11R,B(_11I(_11J,_11K,_11L,_11M,_11N,_11S)),_11T);});break;case 1:return new T5(0,_11Q.a,E(_11P),new T(function(){return B(A3(_11J,_11P,_11N,_11R));}),E(_11S),E(_11T));default:return new F(function(){return _QK(_11U,_11R,_11S,B(_11I(_11J,_11K,_11L,_11M,_11N,_11T)));});}}else{return new T5(0,1,E(_11P),_11N,E(_PY),E(_PY));}},_11V=function(_11W,_11X){var _11Y=function(_11Z,_120){while(1){var _121=E(_120);if(!_121._){return E(_11Z);}else{var _122=E(_121.a),_123=E(_122.a),_124=B(_11I(_11W,_123.a,_123.b,_123.c,_122.b,_11Z));_11Z=_124;_120=_121.b;continue;}}};return new F(function(){return _11Y(_PY,_11X);});},_125=function(_126){return E(E(_126).b);},_127=function(_128,_129,_12a,_12b){var _12c=E(_129),_12d=E(_12b);if(!_12d._){var _12e=_12d.b,_12f=_12d.c,_12g=_12d.d,_12h=_12d.e;switch(B(A3(_125,_128,_12c,_12e))){case 0:return new F(function(){return _Q3(_12e,_12f,B(_127(_128,_12c,_12a,_12g)),_12h);});break;case 1:return new T5(0,_12d.a,E(_12c),_12a,E(_12g),E(_12h));default:return new F(function(){return _QK(_12e,_12f,_12g,B(_127(_128,_12c,_12a,_12h)));});}}else{return new T5(0,1,E(_12c),_12a,E(_PY),E(_PY));}},_12i=function(_12j,_12k,_12l,_12m){return new F(function(){return _127(_12j,_12k,_12l,_12m);});},_12n=function(_12o,_12p,_12q,_12r,_12s){var _12t=E(_12s),_12u=B(_12v(_12o,_12p,_12q,_12r,_12t.a,_12t.b));return new T2(0,_12u.a,_12u.b);},_12w=function(_12x,_12y,_12z){var _12A=function(_12B,_12C){while(1){var _12D=E(_12B),_12E=E(_12C);if(!_12E._){switch(B(A3(_125,_12x,_12D,_12E.b))){case 0:_12B=_12D;_12C=_12E.d;continue;case 1:return new T1(1,_12E.c);default:_12B=_12D;_12C=_12E.e;continue;}}else{return __Z;}}};return new F(function(){return _12A(_12y,_12z);});},_12F=function(_12G,_12H){var _12I=E(_12G);if(!_12I._){return new T2(0,new T1(1,_12H),_PY);}else{var _12J=new T(function(){return new T5(0,1,E(_12I.a),new T(function(){return B(_12K(_12I.b,_12H));}),E(_PY),E(_PY));});return new T2(0,_4l,_12J);}},_12K=function(_12L,_12M){var _12N=B(_12F(_12L,_12M));return new T2(0,_12N.a,_12N.b);},_12v=function(_12O,_12P,_12Q,_12R,_12S,_12T){var _12U=E(_12Q);if(!_12U._){var _12V=E(_12S);return (_12V._==0)?new T2(0,new T1(1,_12R),_12T):new T2(0,new T1(1,new T(function(){return B(A2(_12P,_12R,_12V.a));})),_12T);}else{var _12W=_12U.a,_12X=_12U.b,_12Y=B(_12w(_12O,_12W,_12T));if(!_12Y._){var _12Z=new T(function(){return B(_12i(_12O,_12W,new T(function(){return B(_12K(_12X,_12R));}),_12T));});return new T2(0,_12S,_12Z);}else{var _130=new T(function(){return B(_12i(_12O,_12W,new T(function(){return B(_12n(_12O,_12P,_12X,_12R,_12Y.a));}),_12T));});return new T2(0,_12S,_130);}}},_131=function(_132,_133,_134){var _135=function(_136,_137,_138){while(1){var _139=E(_136);if(!_139._){return new T2(0,_137,_138);}else{var _13a=E(_139.a),_13b=B(_12v(_132,_133,_13a.a,_13a.b,_137,_138));_136=_139.b;_137=_13b.a;_138=_13b.b;continue;}}};return new F(function(){return _135(_134,_4l,_PY);});},_13c=function(_13d,_13e,_13f){var _13g=E(_13f);switch(_13g._){case 0:var _13h=_13g.a,_13i=_13g.b,_13j=_13g.c,_13k=_13g.d,_13l=_13i>>>0;if(((_13d>>>0&((_13l-1>>>0^4294967295)>>>0^_13l)>>>0)>>>0&4294967295)==_13h){return ((_13d>>>0&_13l)>>>0==0)?new T4(0,_13h,_13i,E(B(_13c(_13d,_13e,_13j))),E(_13k)):new T4(0,_13h,_13i,E(_13j),E(B(_13c(_13d,_13e,_13k))));}else{var _13m=(_13d>>>0^_13h>>>0)>>>0,_13n=(_13m|_13m>>>1)>>>0,_13o=(_13n|_13n>>>2)>>>0,_13p=(_13o|_13o>>>4)>>>0,_13q=(_13p|_13p>>>8)>>>0,_13r=(_13q|_13q>>>16)>>>0,_13s=(_13r^_13r>>>1)>>>0&4294967295,_13t=_13s>>>0;return ((_13d>>>0&_13t)>>>0==0)?new T4(0,(_13d>>>0&((_13t-1>>>0^4294967295)>>>0^_13t)>>>0)>>>0&4294967295,_13s,E(new T2(1,_13d,_13e)),E(_13g)):new T4(0,(_13d>>>0&((_13t-1>>>0^4294967295)>>>0^_13t)>>>0)>>>0&4294967295,_13s,E(_13g),E(new T2(1,_13d,_13e)));}break;case 1:var _13u=_13g.a;if(_13d!=_13u){var _13v=(_13d>>>0^_13u>>>0)>>>0,_13w=(_13v|_13v>>>1)>>>0,_13x=(_13w|_13w>>>2)>>>0,_13y=(_13x|_13x>>>4)>>>0,_13z=(_13y|_13y>>>8)>>>0,_13A=(_13z|_13z>>>16)>>>0,_13B=(_13A^_13A>>>1)>>>0&4294967295,_13C=_13B>>>0;return ((_13d>>>0&_13C)>>>0==0)?new T4(0,(_13d>>>0&((_13C-1>>>0^4294967295)>>>0^_13C)>>>0)>>>0&4294967295,_13B,E(new T2(1,_13d,_13e)),E(_13g)):new T4(0,(_13d>>>0&((_13C-1>>>0^4294967295)>>>0^_13C)>>>0)>>>0&4294967295,_13B,E(_13g),E(new T2(1,_13d,_13e)));}else{return new T2(1,_13d,_13e);}break;default:return new T2(1,_13d,_13e);}},_13D=function(_13E,_13F){var _13G=function(_13H){while(1){var _13I=E(_13H);switch(_13I._){case 0:var _13J=_13I.b>>>0;if(((_13E>>>0&((_13J-1>>>0^4294967295)>>>0^_13J)>>>0)>>>0&4294967295)==_13I.a){if(!((_13E>>>0&_13J)>>>0)){_13H=_13I.c;continue;}else{_13H=_13I.d;continue;}}else{return __Z;}break;case 1:return (_13E!=_13I.a)?__Z:new T1(1,_13I.b);default:return __Z;}}};return new F(function(){return _13G(_13F);});},_13K=function(_13L,_13M,_13N,_13O){var _13P=E(_13O);if(!_13P._){var _13Q=new T(function(){var _13R=B(_13K(_13P.a,_13P.b,_13P.c,_13P.d));return new T2(0,_13R.a,_13R.b);});return new T2(0,new T(function(){return E(E(_13Q).a);}),new T(function(){return B(_Ly(_13M,_13N,E(_13Q).b));}));}else{return new T2(0,_13M,_13N);}},_13S=function(_13T,_13U,_13V,_13W){var _13X=E(_13V);if(!_13X._){var _13Y=new T(function(){var _13Z=B(_13S(_13X.a,_13X.b,_13X.c,_13X.d));return new T2(0,_13Z.a,_13Z.b);});return new T2(0,new T(function(){return E(E(_13Y).a);}),new T(function(){return B(_Ma(_13U,E(_13Y).b,_13W));}));}else{return new T2(0,_13U,_13W);}},_140=function(_141,_142){var _143=E(_141);if(!_143._){var _144=_143.a,_145=E(_142);if(!_145._){var _146=_145.a;if(_144<=_146){var _147=B(_13S(_146,_145.b,_145.c,_145.d));return new F(function(){return _Ly(_147.a,_143,_147.b);});}else{var _148=B(_13K(_144,_143.b,_143.c,_143.d));return new F(function(){return _Ma(_148.a,_148.b,_145);});}}else{return E(_143);}}else{return E(_142);}},_149=function(_14a,_14b,_14c,_14d,_14e){var _14f=E(_14a);if(!_14f._){var _14g=_14f.a,_14h=_14f.b,_14i=_14f.c,_14j=_14f.d;if((imul(3,_14g)|0)>=_14b){if((imul(3,_14b)|0)>=_14g){return new F(function(){return _140(_14f,new T4(0,_14b,E(_14c),E(_14d),E(_14e)));});}else{return new F(function(){return _Ma(_14h,_14i,B(_149(_14j,_14b,_14c,_14d,_14e)));});}}else{return new F(function(){return _Ly(_14c,B(_14k(_14g,_14h,_14i,_14j,_14d)),_14e);});}}else{return new T4(0,_14b,E(_14c),E(_14d),E(_14e));}},_14k=function(_14l,_14m,_14n,_14o,_14p){var _14q=E(_14p);if(!_14q._){var _14r=_14q.a,_14s=_14q.b,_14t=_14q.c,_14u=_14q.d;if((imul(3,_14l)|0)>=_14r){if((imul(3,_14r)|0)>=_14l){return new F(function(){return _140(new T4(0,_14l,E(_14m),E(_14n),E(_14o)),_14q);});}else{return new F(function(){return _Ma(_14m,_14n,B(_149(_14o,_14r,_14s,_14t,_14u)));});}}else{return new F(function(){return _Ly(_14s,B(_14k(_14l,_14m,_14n,_14o,_14t)),_14u);});}}else{return new T4(0,_14l,E(_14m),E(_14n),E(_14o));}},_14v=function(_14w,_14x){var _14y=E(_14w);if(!_14y._){var _14z=_14y.a,_14A=_14y.b,_14B=_14y.c,_14C=_14y.d,_14D=E(_14x);if(!_14D._){var _14E=_14D.a,_14F=_14D.b,_14G=_14D.c,_14H=_14D.d;if((imul(3,_14z)|0)>=_14E){if((imul(3,_14E)|0)>=_14z){return new F(function(){return _140(_14y,_14D);});}else{return new F(function(){return _Ma(_14A,_14B,B(_149(_14C,_14E,_14F,_14G,_14H)));});}}else{return new F(function(){return _Ly(_14F,B(_14k(_14z,_14A,_14B,_14C,_14G)),_14H);});}}else{return E(_14y);}}else{return E(_14x);}},_14I=function(_14J,_14K){var _14L=E(_14K);if(!_14L._){var _14M=_14L.b,_14N=B(_14I(_14J,_14L.c)),_14O=_14N.a,_14P=_14N.b,_14Q=B(_14I(_14J,_14L.d)),_14R=_14Q.a,_14S=_14Q.b;return (!B(A1(_14J,_14M)))?new T2(0,B(_14v(_14O,_14R)),B(_Nu(_14M,_14P,_14S))):new T2(0,B(_Nu(_14M,_14O,_14R)),B(_14v(_14P,_14S)));}else{return new T2(0,_Lt,_Lt);}},_14T=function(_14U,_14V,_14W,_14X){var _14Y=E(_14W),_14Z=B(_150(_14U,_14V,_14Y.a,_14Y.b,_14X));return new T2(0,_14Z.a,_14Z.b);},_151=function(_152,_153,_154){while(1){var _155=E(_154);if(!_155._){var _156=_155.e;switch(B(A3(_125,_152,_153,_155.b))){case 0:return new T2(0,B(_12w(_152,_153,_155.d)),_155);case 1:return new T2(0,new T1(1,_155.c),_156);default:_154=_156;continue;}}else{return new T2(0,_4l,_PY);}}},_157=function(_158){return E(E(_158).f);},_159=function(_15a,_15b,_15c){while(1){var _15d=E(_15c);if(!_15d._){if(!B(A3(_157,_15a,_15d.b,_15b))){return E(_15d);}else{_15c=_15d.d;continue;}}else{return new T0(1);}}},_15e=function(_15f,_15g,_15h,_15i){while(1){var _15j=E(_15i);if(!_15j._){var _15k=_15j.b,_15l=_15j.d,_15m=_15j.e;switch(B(A3(_125,_15f,_15g,_15k))){case 0:if(!B(A3(_os,_15f,_15k,_15h))){_15i=_15l;continue;}else{return new T2(0,B(_12w(_15f,_15g,_15l)),_15j);}break;case 1:return new T2(0,new T1(1,_15j.c),B(_159(_15f,_15h,_15m)));default:_15i=_15m;continue;}}else{return new T2(0,_4l,_PY);}}},_15n=function(_15o,_15p,_15q,_15r){var _15s=E(_15q);if(!_15s._){return new F(function(){return _151(_15o,_15p,_15r);});}else{return new F(function(){return _15e(_15o,_15p,_15s.a,_15r);});}},_15t=__Z,_15u=function(_15v,_15w,_15x){var _15y=E(_15w);if(!_15y._){return E(_15x);}else{var _15z=function(_15A,_15B){while(1){var _15C=E(_15B);if(!_15C._){var _15D=_15C.b,_15E=_15C.e;switch(B(A3(_125,_15v,_15A,_15D))){case 0:return new F(function(){return _Se(_15D,_15C.c,B(_15z(_15A,_15C.d)),_15E);});break;case 1:return E(_15E);default:_15B=_15E;continue;}}else{return new T0(1);}}};return new F(function(){return _15z(_15y.a,_15x);});}},_15F=function(_15G,_15H,_15I){var _15J=E(_15H);if(!_15J._){return E(_15I);}else{var _15K=function(_15L,_15M){while(1){var _15N=E(_15M);if(!_15N._){var _15O=_15N.b,_15P=_15N.d;switch(B(A3(_125,_15G,_15O,_15L))){case 0:return new F(function(){return _Se(_15O,_15N.c,_15P,B(_15K(_15L,_15N.e)));});break;case 1:return E(_15P);default:_15M=_15P;continue;}}else{return new T0(1);}}};return new F(function(){return _15K(_15J.a,_15I);});}},_15Q=function(_15R){return E(E(_15R).d);},_15S=function(_15T,_15U,_15V,_15W){var _15X=E(_15U);if(!_15X._){var _15Y=E(_15V);if(!_15Y._){return E(_15W);}else{var _15Z=function(_160,_161){while(1){var _162=E(_161);if(!_162._){if(!B(A3(_157,_15T,_162.b,_160))){return E(_162);}else{_161=_162.d;continue;}}else{return new T0(1);}}};return new F(function(){return _15Z(_15Y.a,_15W);});}}else{var _163=_15X.a,_164=E(_15V);if(!_164._){var _165=function(_166,_167){while(1){var _168=E(_167);if(!_168._){if(!B(A3(_15Q,_15T,_168.b,_166))){return E(_168);}else{_167=_168.e;continue;}}else{return new T0(1);}}};return new F(function(){return _165(_163,_15W);});}else{var _169=function(_16a,_16b,_16c){while(1){var _16d=E(_16c);if(!_16d._){var _16e=_16d.b;if(!B(A3(_15Q,_15T,_16e,_16a))){if(!B(A3(_157,_15T,_16e,_16b))){return E(_16d);}else{_16c=_16d.d;continue;}}else{_16c=_16d.e;continue;}}else{return new T0(1);}}};return new F(function(){return _169(_163,_164.a,_15W);});}}},_16f=function(_16g,_16h,_16i,_16j){var _16k=E(_16i);if(!_16k._){var _16l=E(_16j);if(!_16l._){var _16m=function(_16n,_16o,_16p,_16q){var _16r=E(_16q);if(!_16r._){var _16s=E(_16p);if(!_16s._){var _16t=_16s.b,_16u=_16s.c,_16v=_16s.e,_16w=B(_15n(_16g,_16t,_16o,_16r)),_16x=_16w.b,_16y=new T1(1,E(_16t)),_16z=B(_16m(_16n,_16y,_16s.d,B(_15S(_16g,_16n,_16y,_16r)))),_16A=E(_16w.a);if(!_16A._){return new F(function(){return _Se(_16t,_16u,_16z,B(_16m(_16y,_16o,_16v,_16x)));});}else{return new F(function(){return _Se(_16t,new T(function(){return B(A3(_16h,_16t,_16u,_16A.a));}),_16z,B(_16m(_16y,_16o,_16v,_16x)));});}}else{return new F(function(){return _Se(_16r.b,_16r.c,B(_15u(_16g,_16n,_16r.d)),B(_15F(_16g,_16o,_16r.e)));});}}else{return E(_16p);}},_16B=_15t,_16C=_15t,_16D=_16k.a,_16E=_16k.b,_16F=_16k.c,_16G=_16k.d,_16H=_16k.e,_16I=_16l.a,_16J=_16l.b,_16K=_16l.c,_16L=_16l.d,_16M=_16l.e,_16N=B(_15n(_16g,_16E,_16C,new T5(0,_16I,E(_16J),_16K,E(_16L),E(_16M)))),_16O=_16N.b,_16P=new T1(1,E(_16E)),_16Q=B(_16m(_16B,_16P,_16G,B(_15S(_16g,_16B,_16P,new T5(0,_16I,E(_16J),_16K,E(_16L),E(_16M)))))),_16R=E(_16N.a);if(!_16R._){return new F(function(){return _Se(_16E,_16F,_16Q,B(_16m(_16P,_16C,_16H,_16O)));});}else{return new F(function(){return _Se(_16E,new T(function(){return B(A3(_16h,_16E,_16F,_16R.a));}),_16Q,B(_16m(_16P,_16C,_16H,_16O)));});}}else{return E(_16k);}}else{return E(_16j);}},_150=function(_16S,_16T,_16U,_16V,_16W){var _16X=E(_16W),_16Y=_16X.a,_16Z=new T(function(){return B(_16f(_16S,function(_170,_171,_172){return new F(function(){return _14T(_16S,_16T,_171,_172);});},_16V,_16X.b));}),_173=new T(function(){var _174=E(_16U);if(!_174._){return E(_16Y);}else{var _175=E(_16Y);if(!_175._){return E(_174);}else{return new T1(1,new T(function(){return B(A2(_16T,_174.a,_175.a));}));}}});return new T2(0,_173,_16Z);},_176=function(_177,_178,_179){var _17a=function(_17b,_17c,_17d){while(1){var _17e=E(_17b);if(!_17e._){return new T2(0,_17c,_17d);}else{var _17f=B(_150(_177,_178,_17c,_17d,_17e.a));_17b=_17e.b;_17c=_17f.a;_17d=_17f.b;continue;}}};return new F(function(){return _17a(_179,_4l,_PY);});},_17g=new T0(2),_17h=function(_17i,_17j){var _17k=E(_17i),_17l=E(_17j);return new F(function(){return _11u(_17k.a,_17k.b,_17k.c,_17l.a,_17l.b,_17l.c);});},_17m=function(_17n,_17o){return E(_17n)==E(_17o);},_17p=function(_17q,_17r){var _17s=E(_17q);switch(_17s._){case 0:var _17t=E(_17r);if(!_17t._){return new F(function(){return _qX(_17s.a,_17t.a);});}else{return false;}break;case 1:var _17u=E(_17r);if(_17u._==1){return new F(function(){return _hD(_17s.a,_17u.a);});}else{return false;}break;default:var _17v=E(_17r);if(_17v._==2){return new F(function(){return _17m(_17s.a,_17v.a);});}else{return false;}}},_17w=function(_17x,_17y,_17z){while(1){var _17A=E(_17y);if(!_17A._){return (E(_17z)._==0)?true:false;}else{var _17B=E(_17z);if(!_17B._){return false;}else{if(!B(A3(_ou,_17x,_17A.a,_17B.a))){return false;}else{_17y=_17A.b;_17z=_17B.b;continue;}}}}},_17C=function(_17D,_17E){return (!B(_17F(_17D,_17E)))?true:false;},_17G=new T2(0,_17F,_17C),_17H=new T(function(){return E(_17G);}),_17I=function(_17J,_17K){return (E(_17J)==0)?(E(_17K)==0)?false:true:(E(_17K)==0)?true:false;},_17L=function(_17M,_17N){return (E(_17M)==0)?(E(_17N)==0)?true:false:(E(_17N)==0)?false:true;},_17O=new T2(0,_17L,_17I),_17P=new T(function(){return E(_17O);}),_17Q=function(_17R,_17S,_17T,_17U,_17V,_17W){if(!B(A3(_ou,_17P,_17R,_17U))){return false;}else{var _17X=E(_17S),_17Y=E(_17V);if(!B(_11u(_17X.a,_17X.b,_17X.c,_17Y.a,_17Y.b,_17Y.c))){return false;}else{return new F(function(){return _17Z(_17T,_17W);});}}},_180=function(_181,_182){var _183=E(_181),_184=E(_182);return new F(function(){return _17Q(_183.a,_183.b,_183.c,_184.a,_184.b,_184.c);});},_185=function(_186,_187,_188,_189,_18a,_18b){if(!B(A3(_ou,_17P,_186,_189))){return true;}else{var _18c=E(_187),_18d=E(_18a);if(!B(_11u(_18c.a,_18c.b,_18c.c,_18d.a,_18d.b,_18d.c))){return true;}else{var _18e=E(_188);return (!B(_18f(_18e.a,_18e.b,_18e.c,_18b)))?true:false;}}},_18g=function(_18h,_18i){var _18j=E(_18h),_18k=E(_18i);return new F(function(){return _185(_18j.a,_18j.b,_18j.c,_18k.a,_18k.b,_18k.c);});},_18l=new T(function(){return new T2(0,_180,_18g);}),_18f=function(_18m,_18n,_18o,_18p){var _18q=E(_18p);if(!B(_17w(_18l,_18m,_18q.a))){return false;}else{var _18r=E(_18n),_18s=E(_18q.b);if(!B(_11u(_18r.a,_18r.b,_18r.c,_18s.a,_18s.b,_18s.c))){return false;}else{return new F(function(){return _17w(_17H,_18o,_18q.c);});}}},_17Z=function(_18t,_18u){var _18v=E(_18t);return new F(function(){return _18f(_18v.a,_18v.b,_18v.c,_18u);});},_17F=function(_18w,_18x){while(1){var _18y=E(_18w);switch(_18y._){case 0:var _18z=_18y.b,_18A=_18y.c,_18B=E(_18x);if(!_18B._){var _18C=_18B.a,_18D=_18B.b,_18E=_18B.c;if(!E(_18y.a)){if(!E(_18C)){var _18F=E(_18z),_18G=E(_18D);if(!B(_11u(_18F.a,_18F.b,_18F.c,_18G.a,_18G.b,_18G.c))){return false;}else{_18w=_18A;_18x=_18E;continue;}}else{return false;}}else{if(!E(_18C)){return false;}else{var _18H=E(_18z),_18I=E(_18D);if(!B(_11u(_18H.a,_18H.b,_18H.c,_18I.a,_18I.b,_18I.c))){return false;}else{_18w=_18A;_18x=_18E;continue;}}}}else{return false;}break;case 1:var _18J=E(_18x);if(_18J._==1){if(!B(_17F(_18y.a,_18J.a))){return false;}else{_18w=_18y.b;_18x=_18J.b;continue;}}else{return false;}break;case 2:var _18K=E(_18x);if(_18K._==2){return new F(function(){return _17p(_18y.a,_18K.a);});}else{return false;}break;case 3:var _18L=E(_18x);return (_18L._==3)?_18y.a==_18L.a:false;case 4:var _18M=E(_18x);if(_18M._==4){return new F(function(){return _17h(_18y.a,_18M.a);});}else{return false;}break;case 5:var _18N=E(_18x);return (_18N._==5)?_18y.a==_18N.a:false;case 6:var _18O=E(_18x);if(_18O._==6){if(!B(_17F(_18y.a,_18O.a))){return false;}else{return new F(function(){return _17Z(_18y.b,_18O.b);});}}else{return false;}break;default:var _18P=E(_18x);if(_18P._==7){_18w=_18y.a;_18x=_18P.a;continue;}else{return false;}}}},_18Q=function(_18R,_18S,_18T,_18U){return (_18R!=_18T)?true:(E(_18S)!=E(_18U))?true:false;},_18V=function(_18W,_18X){var _18Y=E(_18W),_18Z=E(_18X);return new F(function(){return _18Q(E(_18Y.a),_18Y.b,E(_18Z.a),_18Z.b);});},_190=function(_191,_192,_193,_194){if(_191!=_193){return false;}else{return new F(function(){return _hD(_192,_194);});}},_195=function(_196,_197){var _198=E(_196),_199=E(_197);return new F(function(){return _190(E(_198.a),_198.b,E(_199.a),_199.b);});},_19a=new T2(0,_195,_18V),_19b=function(_19c,_19d,_19e,_19f){return (!B(_17w(_19a,_19c,_19e)))?true:(_19d!=_19f)?true:false;},_19g=function(_19h,_19i){var _19j=E(_19h),_19k=E(_19i);return new F(function(){return _19b(_19j.a,_19j.b,_19k.a,_19k.b);});},_19l=function(_19m,_19n){var _19o=E(_19m),_19p=E(_19n);return (!B(_17w(_19a,_19o.a,_19p.a)))?false:_19o.b==_19p.b;},_19q=new T2(0,_19l,_19g),_19r=function(_19s,_19t){while(1){var _19u=E(_19s);if(!_19u._){return (E(_19t)._==0)?true:false;}else{var _19v=E(_19t);if(!_19v._){return false;}else{if(!B(_r9(_19u.a,_19v.a))){return false;}else{_19s=_19u.b;_19t=_19v.b;continue;}}}}},_19w=function(_19x,_19y){var _19z=E(_19x);switch(_19z._){case 0:var _19A=E(_19y);if(!_19A._){if(_19z.a!=_19A.a){return false;}else{return new F(function(){return _17w(_19q,_19z.b,_19A.b);});}}else{return false;}break;case 1:var _19B=E(_19y);return (_19B._==1)?_19z.a==_19B.a:false;default:var _19C=E(_19y);if(_19C._==2){var _19D=E(_19z.a),_19E=E(_19C.a);if(!B(_11u(_19D.a,_19D.b,_19D.c,_19E.a,_19E.b,_19E.c))){return false;}else{if(!B(_17F(_19z.b,_19C.b))){return false;}else{return new F(function(){return _19r(_19z.c,_19C.c);});}}}else{return false;}}},_19F=function(_19G,_19H){return (!B(_19w(_19G,_19H)))?true:false;},_19I=new T2(0,_19w,_19F),_19J=function(_19K,_19L){var _19M=E(_19K),_19N=E(_19L);return new F(function(){return _11B(_19M.a,_19M.b,_19M.c,_19N.a,_19N.b,_19N.c);});},_19O=function(_19P,_19Q){var _19R=E(_19P),_19S=E(_19Q);return (_19R>=_19S)?(_19R!=_19S)?2:1:0;},_19T=function(_19U,_19V){var _19W=E(_19U);switch(_19W._){case 0:var _19X=E(_19V);if(!_19X._){return new F(function(){return _10V(_19W.a,_19X.a);});}else{return 0;}break;case 1:var _19Y=E(_19V);switch(_19Y._){case 0:return 2;case 1:return new F(function(){return _hX(_19W.a,_19Y.a);});break;default:return 0;}break;default:var _19Z=E(_19V);if(_19Z._==2){return new F(function(){return _19O(_19W.a,_19Z.a);});}else{return 2;}}},_1a0=function(_1a1,_1a2){return (B(_1a3(_1a1,_1a2))==0)?true:false;},_1a4=function(_1a5,_1a6){return (B(_1a3(_1a5,_1a6))==2)?false:true;},_1a7=function(_1a8,_1a9){return (B(_1a3(_1a8,_1a9))==2)?true:false;},_1aa=function(_1ab,_1ac){return (B(_1a3(_1ab,_1ac))==0)?false:true;},_1ad=function(_1ae,_1af){return (B(_1a3(_1ae,_1af))==2)?E(_1ae):E(_1af);},_1ag=function(_1ah,_1ai){return (B(_1a3(_1ah,_1ai))==2)?E(_1ai):E(_1ah);},_1aj={_:0,a:_17G,b:_1a3,c:_1a0,d:_1a4,e:_1a7,f:_1aa,g:_1ad,h:_1ag},_1ak=new T(function(){return E(_1aj);}),_1al=function(_1am,_1an,_1ao){while(1){var _1ap=E(_1an);if(!_1ap._){return (E(_1ao)._==0)?1:0;}else{var _1aq=E(_1ao);if(!_1aq._){return 2;}else{var _1ar=B(A3(_125,_1am,_1ap.a,_1aq.a));if(_1ar==1){_1an=_1ap.b;_1ao=_1aq.b;continue;}else{return E(_1ar);}}}}},_1as=function(_1at,_1au,_1av,_1aw){var _1ax=E(_1aw);switch(B(_1al(_1ay,_1at,_1ax.a))){case 0:return false;case 1:var _1az=E(_1au),_1aA=E(_1ax.b);switch(B(_11B(_1az.a,_1az.b,_1az.c,_1aA.a,_1aA.b,_1aA.c))){case 0:return false;case 1:return (B(_1al(_1ak,_1av,_1ax.c))==0)?false:true;default:return true;}break;default:return true;}},_1aB=function(_1aC,_1aD){var _1aE=E(_1aC);return new F(function(){return _1as(_1aE.a,_1aE.b,_1aE.c,_1aD);});},_1aF=function(_1aG,_1aH){if(!E(_1aG)){return (E(_1aH)==0)?false:true;}else{var _1aI=E(_1aH);return false;}},_1aJ=function(_1aK,_1aL){if(!E(_1aK)){var _1aM=E(_1aL);return true;}else{return (E(_1aL)==0)?false:true;}},_1aN=function(_1aO,_1aP){if(!E(_1aO)){var _1aQ=E(_1aP);return false;}else{return (E(_1aP)==0)?true:false;}},_1aR=function(_1aS,_1aT){if(!E(_1aS)){return (E(_1aT)==0)?true:false;}else{var _1aU=E(_1aT);return true;}},_1aV=function(_1aW,_1aX){return (E(_1aW)==0)?(E(_1aX)==0)?1:0:(E(_1aX)==0)?2:1;},_1aY=function(_1aZ,_1b0){if(!E(_1aZ)){return E(_1b0);}else{var _1b1=E(_1b0);return 1;}},_1b2=function(_1b3,_1b4){if(!E(_1b3)){var _1b5=E(_1b4);return 0;}else{return E(_1b4);}},_1b6={_:0,a:_17O,b:_1aV,c:_1aF,d:_1aJ,e:_1aN,f:_1aR,g:_1aY,h:_1b2},_1b7=new T(function(){return E(_1b6);}),_1b8=function(_1b9,_1ba,_1bb,_1bc,_1bd,_1be){switch(B(A3(_125,_1b7,_1b9,_1bc))){case 0:return false;case 1:var _1bf=E(_1ba),_1bg=E(_1bd);switch(B(_11B(_1bf.a,_1bf.b,_1bf.c,_1bg.a,_1bg.b,_1bg.c))){case 0:return false;case 1:return new F(function(){return _1aB(_1bb,_1be);});break;default:return true;}break;default:return true;}},_1bh=function(_1bi,_1bj){var _1bk=E(_1bi),_1bl=E(_1bj);return new F(function(){return _1b8(_1bk.a,_1bk.b,_1bk.c,_1bl.a,_1bl.b,_1bl.c);});},_1bm=function(_1bn,_1bo,_1bp,_1bq){var _1br=E(_1bq);switch(B(_1al(_1ay,_1bn,_1br.a))){case 0:return false;case 1:var _1bs=E(_1bo),_1bt=E(_1br.b);switch(B(_11B(_1bs.a,_1bs.b,_1bs.c,_1bt.a,_1bt.b,_1bt.c))){case 0:return false;case 1:return (B(_1al(_1ak,_1bp,_1br.c))==2)?true:false;default:return true;}break;default:return true;}},_1bu=function(_1bv,_1bw){var _1bx=E(_1bv);return new F(function(){return _1bm(_1bx.a,_1bx.b,_1bx.c,_1bw);});},_1by=function(_1bz,_1bA,_1bB,_1bC,_1bD,_1bE){switch(B(A3(_125,_1b7,_1bz,_1bC))){case 0:return false;case 1:var _1bF=E(_1bA),_1bG=E(_1bD);switch(B(_11B(_1bF.a,_1bF.b,_1bF.c,_1bG.a,_1bG.b,_1bG.c))){case 0:return false;case 1:return new F(function(){return _1bu(_1bB,_1bE);});break;default:return true;}break;default:return true;}},_1bH=function(_1bI,_1bJ){var _1bK=E(_1bI),_1bL=E(_1bJ);return new F(function(){return _1by(_1bK.a,_1bK.b,_1bK.c,_1bL.a,_1bL.b,_1bL.c);});},_1bM=function(_1bN,_1bO,_1bP,_1bQ){var _1bR=E(_1bQ);switch(B(_1al(_1ay,_1bN,_1bR.a))){case 0:return true;case 1:var _1bS=E(_1bO),_1bT=E(_1bR.b);switch(B(_11B(_1bS.a,_1bS.b,_1bS.c,_1bT.a,_1bT.b,_1bT.c))){case 0:return true;case 1:return (B(_1al(_1ak,_1bP,_1bR.c))==2)?false:true;default:return false;}break;default:return false;}},_1bU=function(_1bV,_1bW){var _1bX=E(_1bV);return new F(function(){return _1bM(_1bX.a,_1bX.b,_1bX.c,_1bW);});},_1bY=function(_1bZ,_1c0,_1c1,_1c2,_1c3,_1c4){switch(B(A3(_125,_1b7,_1bZ,_1c2))){case 0:return true;case 1:var _1c5=E(_1c0),_1c6=E(_1c3);switch(B(_11B(_1c5.a,_1c5.b,_1c5.c,_1c6.a,_1c6.b,_1c6.c))){case 0:return true;case 1:return new F(function(){return _1bU(_1c1,_1c4);});break;default:return false;}break;default:return false;}},_1c7=function(_1c8,_1c9){var _1ca=E(_1c8),_1cb=E(_1c9);return new F(function(){return _1bY(_1ca.a,_1ca.b,_1ca.c,_1cb.a,_1cb.b,_1cb.c);});},_1cc=function(_1cd,_1ce){var _1cf=E(_1cd),_1cg=_1cf.a,_1ch=_1cf.c,_1ci=E(_1ce),_1cj=_1ci.a,_1ck=_1ci.c;switch(B(A3(_125,_1b7,_1cg,_1cj))){case 0:return E(_1ci);case 1:var _1cl=E(_1cf.b),_1cm=E(_1ci.b);switch(B(_11B(_1cl.a,_1cl.b,_1cl.c,_1cm.a,_1cm.b,_1cm.c))){case 0:return new T3(0,_1cj,_1cm,_1ck);case 1:var _1cn=E(_1ch);return (!B(_1bM(_1cn.a,_1cn.b,_1cn.c,_1ck)))?new T3(0,_1cg,_1cl,_1cn):new T3(0,_1cj,_1cm,_1ck);default:return new T3(0,_1cg,_1cl,_1ch);}break;default:return E(_1cf);}},_1co=function(_1cp,_1cq){var _1cr=E(_1cp),_1cs=_1cr.a,_1ct=_1cr.c,_1cu=E(_1cq),_1cv=_1cu.a,_1cw=_1cu.c;switch(B(A3(_125,_1b7,_1cs,_1cv))){case 0:return E(_1cr);case 1:var _1cx=E(_1cr.b),_1cy=E(_1cu.b);switch(B(_11B(_1cx.a,_1cx.b,_1cx.c,_1cy.a,_1cy.b,_1cy.c))){case 0:return new T3(0,_1cs,_1cx,_1ct);case 1:var _1cz=E(_1ct);return (!B(_1bM(_1cz.a,_1cz.b,_1cz.c,_1cw)))?new T3(0,_1cv,_1cy,_1cw):new T3(0,_1cs,_1cx,_1cz);default:return new T3(0,_1cv,_1cy,_1cw);}break;default:return E(_1cu);}},_1cA=function(_1cB,_1cC,_1cD,_1cE){var _1cF=E(_1cE);switch(B(_1al(_1ay,_1cB,_1cF.a))){case 0:return true;case 1:var _1cG=E(_1cC),_1cH=E(_1cF.b);switch(B(_11B(_1cG.a,_1cG.b,_1cG.c,_1cH.a,_1cH.b,_1cH.c))){case 0:return true;case 1:return (B(_1al(_1ak,_1cD,_1cF.c))==0)?true:false;default:return false;}break;default:return false;}},_1cI=function(_1cJ,_1cK){var _1cL=E(_1cJ);return new F(function(){return _1cA(_1cL.a,_1cL.b,_1cL.c,_1cK);});},_1cM=function(_1cN,_1cO,_1cP,_1cQ,_1cR,_1cS){switch(B(A3(_125,_1b7,_1cN,_1cQ))){case 0:return true;case 1:var _1cT=E(_1cO),_1cU=E(_1cR);switch(B(_11B(_1cT.a,_1cT.b,_1cT.c,_1cU.a,_1cU.b,_1cU.c))){case 0:return true;case 1:return new F(function(){return _1cI(_1cP,_1cS);});break;default:return false;}break;default:return false;}},_1cV=function(_1cW,_1cX){var _1cY=E(_1cW),_1cZ=E(_1cX);return new F(function(){return _1cM(_1cY.a,_1cY.b,_1cY.c,_1cZ.a,_1cZ.b,_1cZ.c);});},_1d0=function(_1d1,_1d2,_1d3,_1d4,_1d5,_1d6){switch(B(A3(_125,_1b7,_1d1,_1d4))){case 0:return 0;case 1:var _1d7=E(_1d2),_1d8=E(_1d5);switch(B(_11B(_1d7.a,_1d7.b,_1d7.c,_1d8.a,_1d8.b,_1d8.c))){case 0:return 0;case 1:return new F(function(){return _1d9(_1d3,_1d6);});break;default:return 2;}break;default:return 2;}},_1da=function(_1db,_1dc){var _1dd=E(_1db),_1de=E(_1dc);return new F(function(){return _1d0(_1dd.a,_1dd.b,_1dd.c,_1de.a,_1de.b,_1de.c);});},_1ay=new T(function(){return {_:0,a:_18l,b:_1da,c:_1cV,d:_1c7,e:_1bH,f:_1bh,g:_1cc,h:_1co};}),_1df=function(_1dg,_1dh,_1di,_1dj){var _1dk=E(_1dj);switch(B(_1al(_1ay,_1dg,_1dk.a))){case 0:return 0;case 1:var _1dl=E(_1dh),_1dm=E(_1dk.b);switch(B(_11B(_1dl.a,_1dl.b,_1dl.c,_1dm.a,_1dm.b,_1dm.c))){case 0:return 0;case 1:return new F(function(){return _1al(_1ak,_1di,_1dk.c);});break;default:return 2;}break;default:return 2;}},_1d9=function(_1dn,_1do){var _1dp=E(_1dn);return new F(function(){return _1df(_1dp.a,_1dp.b,_1dp.c,_1do);});},_1a3=function(_1dq,_1dr){while(1){var _1ds=B((function(_1dt,_1du){var _1dv=E(_1dt);switch(_1dv._){case 0:var _1dw=E(_1du);if(!_1dw._){var _1dx=_1dw.a,_1dy=function(_1dz){var _1dA=E(_1dv.b),_1dB=E(_1dw.b);switch(B(_11B(_1dA.a,_1dA.b,_1dA.c,_1dB.a,_1dB.b,_1dB.c))){case 0:return 0;case 1:return new F(function(){return _1a3(_1dv.c,_1dw.c);});break;default:return 2;}};if(!E(_1dv.a)){if(!E(_1dx)){return new F(function(){return _1dy(_);});}else{return 0;}}else{if(!E(_1dx)){return 2;}else{return new F(function(){return _1dy(_);});}}}else{return 0;}break;case 1:var _1dC=E(_1du);switch(_1dC._){case 0:return 2;case 1:switch(B(_1a3(_1dv.a,_1dC.a))){case 0:return 0;case 1:_1dq=_1dv.b;_1dr=_1dC.b;return __continue;default:return 2;}break;default:return 0;}break;case 2:var _1dD=E(_1du);switch(_1dD._){case 2:return new F(function(){return _19T(_1dv.a,_1dD.a);});break;case 3:return 0;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 3:var _1dE=E(_1du);switch(_1dE._){case 3:return new F(function(){return _hU(_1dv.a,_1dE.a);});break;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 4:var _1dF=E(_1du);switch(_1dF._){case 4:return new F(function(){return _19J(_1dv.a,_1dF.a);});break;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 5:var _1dG=E(_1du);switch(_1dG._){case 5:return new F(function(){return _hU(_1dv.a,_1dG.a);});break;case 6:return 0;case 7:return 0;default:return 2;}break;case 6:var _1dH=E(_1du);switch(_1dH._){case 6:switch(B(_1a3(_1dv.a,_1dH.a))){case 0:return 0;case 1:return new F(function(){return _1d9(_1dv.b,_1dH.b);});break;default:return 2;}break;case 7:return 0;default:return 2;}break;default:var _1dI=E(_1du);if(_1dI._==7){_1dq=_1dv.a;_1dr=_1dI.a;return __continue;}else{return 2;}}})(_1dq,_1dr));if(_1ds!=__continue){return _1ds;}}},_1dJ=function(_1dK,_1dL,_1dM,_1dN){if(_1dK>=_1dM){if(_1dK!=_1dM){return 2;}else{return new F(function(){return _hX(_1dL,_1dN);});}}else{return 0;}},_1dO=function(_1dP,_1dQ){var _1dR=E(_1dP),_1dS=E(_1dQ);return new F(function(){return _1dJ(E(_1dR.a),_1dR.b,E(_1dS.a),_1dS.b);});},_1dT=function(_1dU,_1dV,_1dW,_1dX){if(_1dU>=_1dW){if(_1dU!=_1dW){return false;}else{return new F(function(){return _i9(_1dV,_1dX);});}}else{return true;}},_1dY=function(_1dZ,_1e0){var _1e1=E(_1dZ),_1e2=E(_1e0);return new F(function(){return _1dT(E(_1e1.a),_1e1.b,E(_1e2.a),_1e2.b);});},_1e3=function(_1e4,_1e5,_1e6,_1e7){if(_1e4>=_1e6){if(_1e4!=_1e6){return false;}else{return new F(function(){return _i6(_1e5,_1e7);});}}else{return true;}},_1e8=function(_1e9,_1ea){var _1eb=E(_1e9),_1ec=E(_1ea);return new F(function(){return _1e3(E(_1eb.a),_1eb.b,E(_1ec.a),_1ec.b);});},_1ed=function(_1ee,_1ef,_1eg,_1eh){if(_1ee>=_1eg){if(_1ee!=_1eg){return true;}else{return new F(function(){return _i3(_1ef,_1eh);});}}else{return false;}},_1ei=function(_1ej,_1ek){var _1el=E(_1ej),_1em=E(_1ek);return new F(function(){return _1ed(E(_1el.a),_1el.b,E(_1em.a),_1em.b);});},_1en=function(_1eo,_1ep,_1eq,_1er){if(_1eo>=_1eq){if(_1eo!=_1eq){return true;}else{return new F(function(){return _i0(_1ep,_1er);});}}else{return false;}},_1es=function(_1et,_1eu){var _1ev=E(_1et),_1ew=E(_1eu);return new F(function(){return _1en(E(_1ev.a),_1ev.b,E(_1ew.a),_1ew.b);});},_1ex=function(_1ey,_1ez){var _1eA=E(_1ey),_1eB=E(_1eA.a),_1eC=E(_1ez),_1eD=E(_1eC.a);return (_1eB>=_1eD)?(_1eB!=_1eD)?E(_1eA):(E(_1eA.b)>E(_1eC.b))?E(_1eA):E(_1eC):E(_1eC);},_1eE=function(_1eF,_1eG){var _1eH=E(_1eF),_1eI=E(_1eH.a),_1eJ=E(_1eG),_1eK=E(_1eJ.a);return (_1eI>=_1eK)?(_1eI!=_1eK)?E(_1eJ):(E(_1eH.b)>E(_1eJ.b))?E(_1eJ):E(_1eH):E(_1eH);},_1eL={_:0,a:_19a,b:_1dO,c:_1dY,d:_1e8,e:_1ei,f:_1es,g:_1ex,h:_1eE},_1eM=function(_1eN,_1eO,_1eP,_1eQ){switch(B(_1al(_1eL,_1eN,_1eP))){case 0:return true;case 1:return _1eO<_1eQ;default:return false;}},_1eR=function(_1eS,_1eT){var _1eU=E(_1eS),_1eV=E(_1eT);return new F(function(){return _1eM(_1eU.a,_1eU.b,_1eV.a,_1eV.b);});},_1eW=function(_1eX,_1eY,_1eZ,_1f0){switch(B(_1al(_1eL,_1eX,_1eZ))){case 0:return true;case 1:return _1eY<=_1f0;default:return false;}},_1f1=function(_1f2,_1f3){var _1f4=E(_1f2),_1f5=E(_1f3);return new F(function(){return _1eW(_1f4.a,_1f4.b,_1f5.a,_1f5.b);});},_1f6=function(_1f7,_1f8,_1f9,_1fa){switch(B(_1al(_1eL,_1f7,_1f9))){case 0:return false;case 1:return _1f8>_1fa;default:return true;}},_1fb=function(_1fc,_1fd){var _1fe=E(_1fc),_1ff=E(_1fd);return new F(function(){return _1f6(_1fe.a,_1fe.b,_1ff.a,_1ff.b);});},_1fg=function(_1fh,_1fi,_1fj,_1fk){switch(B(_1al(_1eL,_1fh,_1fj))){case 0:return false;case 1:return _1fi>=_1fk;default:return true;}},_1fl=function(_1fm,_1fn){var _1fo=E(_1fm),_1fp=E(_1fn);return new F(function(){return _1fg(_1fo.a,_1fo.b,_1fp.a,_1fp.b);});},_1fq=function(_1fr,_1fs,_1ft,_1fu){switch(B(_1al(_1eL,_1fr,_1ft))){case 0:return 0;case 1:return new F(function(){return _hU(_1fs,_1fu);});break;default:return 2;}},_1fv=function(_1fw,_1fx){var _1fy=E(_1fw),_1fz=E(_1fx);return new F(function(){return _1fq(_1fy.a,_1fy.b,_1fz.a,_1fz.b);});},_1fA=function(_1fB,_1fC){var _1fD=E(_1fB),_1fE=E(_1fC);switch(B(_1al(_1eL,_1fD.a,_1fE.a))){case 0:return E(_1fE);case 1:return (_1fD.b>_1fE.b)?E(_1fD):E(_1fE);default:return E(_1fD);}},_1fF=function(_1fG,_1fH){var _1fI=E(_1fG),_1fJ=E(_1fH);switch(B(_1al(_1eL,_1fI.a,_1fJ.a))){case 0:return E(_1fI);case 1:return (_1fI.b>_1fJ.b)?E(_1fJ):E(_1fI);default:return E(_1fJ);}},_1fK={_:0,a:_19q,b:_1fv,c:_1eR,d:_1f1,e:_1fb,f:_1fl,g:_1fA,h:_1fF},_1fL=function(_1fM,_1fN){while(1){var _1fO=E(_1fM);if(!_1fO._){return (E(_1fN)._==0)?1:0;}else{var _1fP=E(_1fN);if(!_1fP._){return 2;}else{var _1fQ=B(_10V(_1fO.a,_1fP.a));if(_1fQ==1){_1fM=_1fO.b;_1fN=_1fP.b;continue;}else{return E(_1fQ);}}}}},_1fR=function(_1fS,_1fT){return (B(_1fL(_1fS,_1fT))==0)?true:false;},_1fU=function(_1fV,_1fW){var _1fX=E(_1fV);switch(_1fX._){case 0:var _1fY=_1fX.a,_1fZ=E(_1fW);if(!_1fZ._){var _1g0=_1fZ.a;return (_1fY>=_1g0)?(_1fY!=_1g0)?false:(B(_1al(_1fK,_1fX.b,_1fZ.b))==0)?true:false:true;}else{return true;}break;case 1:var _1g1=E(_1fW);switch(_1g1._){case 0:return false;case 1:return _1fX.a<_1g1.a;default:return true;}break;default:var _1g2=E(_1fW);if(_1g2._==2){var _1g3=E(_1fX.a),_1g4=E(_1g2.a);switch(B(_11B(_1g3.a,_1g3.b,_1g3.c,_1g4.a,_1g4.b,_1g4.c))){case 0:return true;case 1:switch(B(_1a3(_1fX.b,_1g2.b))){case 0:return true;case 1:return new F(function(){return _1fR(_1fX.c,_1g2.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1g5=function(_1g6,_1g7){return (B(_1fL(_1g6,_1g7))==2)?false:true;},_1g8=function(_1g9,_1ga){var _1gb=E(_1g9);switch(_1gb._){case 0:var _1gc=_1gb.a,_1gd=E(_1ga);if(!_1gd._){var _1ge=_1gd.a;return (_1gc>=_1ge)?(_1gc!=_1ge)?false:(B(_1al(_1fK,_1gb.b,_1gd.b))==2)?false:true:true;}else{return true;}break;case 1:var _1gf=E(_1ga);switch(_1gf._){case 0:return false;case 1:return _1gb.a<=_1gf.a;default:return true;}break;default:var _1gg=E(_1ga);if(_1gg._==2){var _1gh=E(_1gb.a),_1gi=E(_1gg.a);switch(B(_11B(_1gh.a,_1gh.b,_1gh.c,_1gi.a,_1gi.b,_1gi.c))){case 0:return true;case 1:switch(B(_1a3(_1gb.b,_1gg.b))){case 0:return true;case 1:return new F(function(){return _1g5(_1gb.c,_1gg.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1gj=function(_1gk,_1gl){return (B(_1fL(_1gk,_1gl))==2)?true:false;},_1gm=function(_1gn,_1go){var _1gp=E(_1gn);switch(_1gp._){case 0:var _1gq=_1gp.a,_1gr=E(_1go);if(!_1gr._){var _1gs=_1gr.a;return (_1gq>=_1gs)?(_1gq!=_1gs)?true:(B(_1al(_1fK,_1gp.b,_1gr.b))==2)?true:false:false;}else{return false;}break;case 1:var _1gt=E(_1go);switch(_1gt._){case 0:return true;case 1:return _1gp.a>_1gt.a;default:return false;}break;default:var _1gu=E(_1go);if(_1gu._==2){var _1gv=E(_1gp.a),_1gw=E(_1gu.a);switch(B(_11B(_1gv.a,_1gv.b,_1gv.c,_1gw.a,_1gw.b,_1gw.c))){case 0:return false;case 1:switch(B(_1a3(_1gp.b,_1gu.b))){case 0:return false;case 1:return new F(function(){return _1gj(_1gp.c,_1gu.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1gx=function(_1gy,_1gz){return (B(_1fL(_1gy,_1gz))==0)?false:true;},_1gA=function(_1gB,_1gC){var _1gD=E(_1gB);switch(_1gD._){case 0:var _1gE=_1gD.a,_1gF=E(_1gC);if(!_1gF._){var _1gG=_1gF.a;return (_1gE>=_1gG)?(_1gE!=_1gG)?true:(B(_1al(_1fK,_1gD.b,_1gF.b))==0)?false:true:false;}else{return false;}break;case 1:var _1gH=E(_1gC);switch(_1gH._){case 0:return true;case 1:return _1gD.a>=_1gH.a;default:return false;}break;default:var _1gI=E(_1gC);if(_1gI._==2){var _1gJ=E(_1gD.a),_1gK=E(_1gI.a);switch(B(_11B(_1gJ.a,_1gJ.b,_1gJ.c,_1gK.a,_1gK.b,_1gK.c))){case 0:return false;case 1:switch(B(_1a3(_1gD.b,_1gI.b))){case 0:return false;case 1:return new F(function(){return _1gx(_1gD.c,_1gI.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1gL=function(_1gM,_1gN){var _1gO=E(_1gM);switch(_1gO._){case 0:var _1gP=_1gO.a,_1gQ=E(_1gN);if(!_1gQ._){var _1gR=_1gQ.a;if(_1gP>=_1gR){if(_1gP!=_1gR){return 2;}else{return new F(function(){return _1al(_1fK,_1gO.b,_1gQ.b);});}}else{return 0;}}else{return 0;}break;case 1:var _1gS=E(_1gN);switch(_1gS._){case 0:return 2;case 1:return new F(function(){return _hU(_1gO.a,_1gS.a);});break;default:return 0;}break;default:var _1gT=E(_1gN);if(_1gT._==2){var _1gU=E(_1gO.a),_1gV=E(_1gT.a);switch(B(_11B(_1gU.a,_1gU.b,_1gU.c,_1gV.a,_1gV.b,_1gV.c))){case 0:return 0;case 1:switch(B(_1a3(_1gO.b,_1gT.b))){case 0:return 0;case 1:return new F(function(){return _1fL(_1gO.c,_1gT.c);});break;default:return 2;}break;default:return 2;}}else{return 2;}}},_1gW=function(_1gX,_1gY){return (!B(_1g8(_1gX,_1gY)))?E(_1gX):E(_1gY);},_1gZ=function(_1h0,_1h1){return (!B(_1g8(_1h0,_1h1)))?E(_1h1):E(_1h0);},_1h2={_:0,a:_19I,b:_1gL,c:_1fU,d:_1g8,e:_1gm,f:_1gA,g:_1gW,h:_1gZ},_1h3=__Z,_1h4=function(_1h5,_1h6,_1h7){var _1h8=E(_1h6);if(!_1h8._){return E(_1h7);}else{var _1h9=function(_1ha,_1hb){while(1){var _1hc=E(_1hb);if(!_1hc._){var _1hd=_1hc.b,_1he=_1hc.d;switch(B(A3(_125,_1h5,_1ha,_1hd))){case 0:return new F(function(){return _Nu(_1hd,B(_1h9(_1ha,_1hc.c)),_1he);});break;case 1:return E(_1he);default:_1hb=_1he;continue;}}else{return new T0(1);}}};return new F(function(){return _1h9(_1h8.a,_1h7);});}},_1hf=function(_1hg,_1hh,_1hi){var _1hj=E(_1hh);if(!_1hj._){return E(_1hi);}else{var _1hk=function(_1hl,_1hm){while(1){var _1hn=E(_1hm);if(!_1hn._){var _1ho=_1hn.b,_1hp=_1hn.c;switch(B(A3(_125,_1hg,_1ho,_1hl))){case 0:return new F(function(){return _Nu(_1ho,_1hp,B(_1hk(_1hl,_1hn.d)));});break;case 1:return E(_1hp);default:_1hm=_1hp;continue;}}else{return new T0(1);}}};return new F(function(){return _1hk(_1hj.a,_1hi);});}},_1hq=function(_1hr,_1hs,_1ht){var _1hu=E(_1hs),_1hv=E(_1ht);if(!_1hv._){var _1hw=_1hv.b,_1hx=_1hv.c,_1hy=_1hv.d;switch(B(A3(_125,_1hr,_1hu,_1hw))){case 0:return new F(function(){return _Ly(_1hw,B(_1hq(_1hr,_1hu,_1hx)),_1hy);});break;case 1:return E(_1hv);default:return new F(function(){return _Ma(_1hw,_1hx,B(_1hq(_1hr,_1hu,_1hy)));});}}else{return new T4(0,1,E(_1hu),E(_Lt),E(_Lt));}},_1hz=function(_1hA,_1hB,_1hC){return new F(function(){return _1hq(_1hA,_1hB,_1hC);});},_1hD=function(_1hE,_1hF,_1hG,_1hH){var _1hI=E(_1hF);if(!_1hI._){var _1hJ=E(_1hG);if(!_1hJ._){return E(_1hH);}else{var _1hK=function(_1hL,_1hM){while(1){var _1hN=E(_1hM);if(!_1hN._){if(!B(A3(_157,_1hE,_1hN.b,_1hL))){return E(_1hN);}else{_1hM=_1hN.c;continue;}}else{return new T0(1);}}};return new F(function(){return _1hK(_1hJ.a,_1hH);});}}else{var _1hO=_1hI.a,_1hP=E(_1hG);if(!_1hP._){var _1hQ=function(_1hR,_1hS){while(1){var _1hT=E(_1hS);if(!_1hT._){if(!B(A3(_15Q,_1hE,_1hT.b,_1hR))){return E(_1hT);}else{_1hS=_1hT.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1hQ(_1hO,_1hH);});}else{var _1hU=function(_1hV,_1hW,_1hX){while(1){var _1hY=E(_1hX);if(!_1hY._){var _1hZ=_1hY.b;if(!B(A3(_15Q,_1hE,_1hZ,_1hV))){if(!B(A3(_157,_1hE,_1hZ,_1hW))){return E(_1hY);}else{_1hX=_1hY.c;continue;}}else{_1hX=_1hY.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1hU(_1hO,_1hP.a,_1hH);});}}},_1i0=function(_1i1,_1i2,_1i3,_1i4,_1i5){var _1i6=E(_1i5);if(!_1i6._){var _1i7=_1i6.b,_1i8=_1i6.c,_1i9=_1i6.d,_1ia=E(_1i4);if(!_1ia._){var _1ib=_1ia.b,_1ic=function(_1id){var _1ie=new T1(1,E(_1ib));return new F(function(){return _Nu(_1ib,B(_1i0(_1i1,_1i2,_1ie,_1ia.c,B(_1hD(_1i1,_1i2,_1ie,_1i6)))),B(_1i0(_1i1,_1ie,_1i3,_1ia.d,B(_1hD(_1i1,_1ie,_1i3,_1i6)))));});};if(!E(_1i8)._){return new F(function(){return _1ic(_);});}else{if(!E(_1i9)._){return new F(function(){return _1ic(_);});}else{return new F(function(){return _1hz(_1i1,_1i7,_1ia);});}}}else{return new F(function(){return _Nu(_1i7,B(_1h4(_1i1,_1i2,_1i8)),B(_1hf(_1i1,_1i3,_1i9)));});}}else{return E(_1i4);}},_1if=function(_1ig,_1ih,_1ii,_1ij,_1ik,_1il,_1im,_1in,_1io,_1ip,_1iq){var _1ir=function(_1is){var _1it=new T1(1,E(_1ik));return new F(function(){return _Nu(_1ik,B(_1i0(_1ig,_1ih,_1it,_1il,B(_1hD(_1ig,_1ih,_1it,new T4(0,_1in,E(_1io),E(_1ip),E(_1iq)))))),B(_1i0(_1ig,_1it,_1ii,_1im,B(_1hD(_1ig,_1it,_1ii,new T4(0,_1in,E(_1io),E(_1ip),E(_1iq)))))));});};if(!E(_1ip)._){return new F(function(){return _1ir(_);});}else{if(!E(_1iq)._){return new F(function(){return _1ir(_);});}else{return new F(function(){return _1hz(_1ig,_1io,new T4(0,_1ij,E(_1ik),E(_1il),E(_1im)));});}}},_1iu=function(_1iv,_1iw,_1ix){var _1iy=E(_1iw);if(!_1iy._){var _1iz=E(_1ix);if(!_1iz._){return new F(function(){return _1if(_1h2,_1h3,_1h3,_1iy.a,_1iy.b,_1iy.c,_1iy.d,_1iz.a,_1iz.b,_1iz.c,_1iz.d);});}else{return E(_1iy);}}else{return E(_1ix);}},_1iA=function(_1iB,_1iC,_1iD){var _1iE=function(_1iF,_1iG,_1iH,_1iI){var _1iJ=E(_1iI);switch(_1iJ._){case 0:var _1iK=_1iJ.a,_1iL=_1iJ.b,_1iM=_1iJ.c,_1iN=_1iJ.d,_1iO=_1iL>>>0;if(((_1iH>>>0&((_1iO-1>>>0^4294967295)>>>0^_1iO)>>>0)>>>0&4294967295)==_1iK){return ((_1iH>>>0&_1iO)>>>0==0)?new T4(0,_1iK,_1iL,E(B(_1iE(_1iF,_1iG,_1iH,_1iM))),E(_1iN)):new T4(0,_1iK,_1iL,E(_1iM),E(B(_1iE(_1iF,_1iG,_1iH,_1iN))));}else{var _1iP=(_1iH>>>0^_1iK>>>0)>>>0,_1iQ=(_1iP|_1iP>>>1)>>>0,_1iR=(_1iQ|_1iQ>>>2)>>>0,_1iS=(_1iR|_1iR>>>4)>>>0,_1iT=(_1iS|_1iS>>>8)>>>0,_1iU=(_1iT|_1iT>>>16)>>>0,_1iV=(_1iU^_1iU>>>1)>>>0&4294967295,_1iW=_1iV>>>0;return ((_1iH>>>0&_1iW)>>>0==0)?new T4(0,(_1iH>>>0&((_1iW-1>>>0^4294967295)>>>0^_1iW)>>>0)>>>0&4294967295,_1iV,E(new T2(1,_1iF,_1iG)),E(_1iJ)):new T4(0,(_1iH>>>0&((_1iW-1>>>0^4294967295)>>>0^_1iW)>>>0)>>>0&4294967295,_1iV,E(_1iJ),E(new T2(1,_1iF,_1iG)));}break;case 1:var _1iX=_1iJ.a;if(_1iH!=_1iX){var _1iY=(_1iH>>>0^_1iX>>>0)>>>0,_1iZ=(_1iY|_1iY>>>1)>>>0,_1j0=(_1iZ|_1iZ>>>2)>>>0,_1j1=(_1j0|_1j0>>>4)>>>0,_1j2=(_1j1|_1j1>>>8)>>>0,_1j3=(_1j2|_1j2>>>16)>>>0,_1j4=(_1j3^_1j3>>>1)>>>0&4294967295,_1j5=_1j4>>>0;return ((_1iH>>>0&_1j5)>>>0==0)?new T4(0,(_1iH>>>0&((_1j5-1>>>0^4294967295)>>>0^_1j5)>>>0)>>>0&4294967295,_1j4,E(new T2(1,_1iF,_1iG)),E(_1iJ)):new T4(0,(_1iH>>>0&((_1j5-1>>>0^4294967295)>>>0^_1j5)>>>0)>>>0&4294967295,_1j4,E(_1iJ),E(new T2(1,_1iF,_1iG)));}else{return new T2(1,_1iF,new T(function(){return B(A3(_1iB,_1iF,_1iG,_1iJ.b));}));}break;default:return new T2(1,_1iF,_1iG);}},_1j6=function(_1j7,_1j8,_1j9,_1ja){var _1jb=E(_1ja);switch(_1jb._){case 0:var _1jc=_1jb.a,_1jd=_1jb.b,_1je=_1jb.c,_1jf=_1jb.d,_1jg=_1jd>>>0;if(((_1j9>>>0&((_1jg-1>>>0^4294967295)>>>0^_1jg)>>>0)>>>0&4294967295)==_1jc){return ((_1j9>>>0&_1jg)>>>0==0)?new T4(0,_1jc,_1jd,E(B(_1j6(_1j7,_1j8,_1j9,_1je))),E(_1jf)):new T4(0,_1jc,_1jd,E(_1je),E(B(_1j6(_1j7,_1j8,_1j9,_1jf))));}else{var _1jh=(_1jc>>>0^_1j9>>>0)>>>0,_1ji=(_1jh|_1jh>>>1)>>>0,_1jj=(_1ji|_1ji>>>2)>>>0,_1jk=(_1jj|_1jj>>>4)>>>0,_1jl=(_1jk|_1jk>>>8)>>>0,_1jm=(_1jl|_1jl>>>16)>>>0,_1jn=(_1jm^_1jm>>>1)>>>0&4294967295,_1jo=_1jn>>>0;return ((_1jc>>>0&_1jo)>>>0==0)?new T4(0,(_1jc>>>0&((_1jo-1>>>0^4294967295)>>>0^_1jo)>>>0)>>>0&4294967295,_1jn,E(_1jb),E(new T2(1,_1j7,_1j8))):new T4(0,(_1jc>>>0&((_1jo-1>>>0^4294967295)>>>0^_1jo)>>>0)>>>0&4294967295,_1jn,E(new T2(1,_1j7,_1j8)),E(_1jb));}break;case 1:var _1jp=_1jb.a;if(_1jp!=_1j9){var _1jq=(_1jp>>>0^_1j9>>>0)>>>0,_1jr=(_1jq|_1jq>>>1)>>>0,_1js=(_1jr|_1jr>>>2)>>>0,_1jt=(_1js|_1js>>>4)>>>0,_1ju=(_1jt|_1jt>>>8)>>>0,_1jv=(_1ju|_1ju>>>16)>>>0,_1jw=(_1jv^_1jv>>>1)>>>0&4294967295,_1jx=_1jw>>>0;return ((_1jp>>>0&_1jx)>>>0==0)?new T4(0,(_1jp>>>0&((_1jx-1>>>0^4294967295)>>>0^_1jx)>>>0)>>>0&4294967295,_1jw,E(_1jb),E(new T2(1,_1j7,_1j8))):new T4(0,(_1jp>>>0&((_1jx-1>>>0^4294967295)>>>0^_1jx)>>>0)>>>0&4294967295,_1jw,E(new T2(1,_1j7,_1j8)),E(_1jb));}else{return new T2(1,_1jp,new T(function(){return B(A3(_1iB,_1jp,_1jb.b,_1j8));}));}break;default:return new T2(1,_1j7,_1j8);}},_1jy=function(_1jz,_1jA,_1jB,_1jC,_1jD,_1jE,_1jF){var _1jG=_1jD>>>0;if(((_1jB>>>0&((_1jG-1>>>0^4294967295)>>>0^_1jG)>>>0)>>>0&4294967295)==_1jC){return ((_1jB>>>0&_1jG)>>>0==0)?new T4(0,_1jC,_1jD,E(B(_1j6(_1jz,_1jA,_1jB,_1jE))),E(_1jF)):new T4(0,_1jC,_1jD,E(_1jE),E(B(_1j6(_1jz,_1jA,_1jB,_1jF))));}else{var _1jH=(_1jC>>>0^_1jB>>>0)>>>0,_1jI=(_1jH|_1jH>>>1)>>>0,_1jJ=(_1jI|_1jI>>>2)>>>0,_1jK=(_1jJ|_1jJ>>>4)>>>0,_1jL=(_1jK|_1jK>>>8)>>>0,_1jM=(_1jL|_1jL>>>16)>>>0,_1jN=(_1jM^_1jM>>>1)>>>0&4294967295,_1jO=_1jN>>>0;return ((_1jC>>>0&_1jO)>>>0==0)?new T4(0,(_1jC>>>0&((_1jO-1>>>0^4294967295)>>>0^_1jO)>>>0)>>>0&4294967295,_1jN,E(new T4(0,_1jC,_1jD,E(_1jE),E(_1jF))),E(new T2(1,_1jz,_1jA))):new T4(0,(_1jC>>>0&((_1jO-1>>>0^4294967295)>>>0^_1jO)>>>0)>>>0&4294967295,_1jN,E(new T2(1,_1jz,_1jA)),E(new T4(0,_1jC,_1jD,E(_1jE),E(_1jF))));}},_1jP=function(_1jQ,_1jR){var _1jS=E(_1jQ);switch(_1jS._){case 0:var _1jT=_1jS.a,_1jU=_1jS.b,_1jV=_1jS.c,_1jW=_1jS.d,_1jX=E(_1jR);switch(_1jX._){case 0:var _1jY=_1jX.a,_1jZ=_1jX.b,_1k0=_1jX.c,_1k1=_1jX.d;if(_1jU>>>0<=_1jZ>>>0){if(_1jZ>>>0<=_1jU>>>0){if(_1jT!=_1jY){var _1k2=(_1jT>>>0^_1jY>>>0)>>>0,_1k3=(_1k2|_1k2>>>1)>>>0,_1k4=(_1k3|_1k3>>>2)>>>0,_1k5=(_1k4|_1k4>>>4)>>>0,_1k6=(_1k5|_1k5>>>8)>>>0,_1k7=(_1k6|_1k6>>>16)>>>0,_1k8=(_1k7^_1k7>>>1)>>>0&4294967295,_1k9=_1k8>>>0;return ((_1jT>>>0&_1k9)>>>0==0)?new T4(0,(_1jT>>>0&((_1k9-1>>>0^4294967295)>>>0^_1k9)>>>0)>>>0&4294967295,_1k8,E(_1jS),E(_1jX)):new T4(0,(_1jT>>>0&((_1k9-1>>>0^4294967295)>>>0^_1k9)>>>0)>>>0&4294967295,_1k8,E(_1jX),E(_1jS));}else{return new T4(0,_1jT,_1jU,E(B(_1jP(_1jV,_1k0))),E(B(_1jP(_1jW,_1k1))));}}else{var _1ka=_1jZ>>>0;if(((_1jT>>>0&((_1ka-1>>>0^4294967295)>>>0^_1ka)>>>0)>>>0&4294967295)==_1jY){return ((_1jT>>>0&_1ka)>>>0==0)?new T4(0,_1jY,_1jZ,E(B(_1kb(_1jT,_1jU,_1jV,_1jW,_1k0))),E(_1k1)):new T4(0,_1jY,_1jZ,E(_1k0),E(B(_1kb(_1jT,_1jU,_1jV,_1jW,_1k1))));}else{var _1kc=(_1jT>>>0^_1jY>>>0)>>>0,_1kd=(_1kc|_1kc>>>1)>>>0,_1ke=(_1kd|_1kd>>>2)>>>0,_1kf=(_1ke|_1ke>>>4)>>>0,_1kg=(_1kf|_1kf>>>8)>>>0,_1kh=(_1kg|_1kg>>>16)>>>0,_1ki=(_1kh^_1kh>>>1)>>>0&4294967295,_1kj=_1ki>>>0;return ((_1jT>>>0&_1kj)>>>0==0)?new T4(0,(_1jT>>>0&((_1kj-1>>>0^4294967295)>>>0^_1kj)>>>0)>>>0&4294967295,_1ki,E(_1jS),E(_1jX)):new T4(0,(_1jT>>>0&((_1kj-1>>>0^4294967295)>>>0^_1kj)>>>0)>>>0&4294967295,_1ki,E(_1jX),E(_1jS));}}}else{var _1kk=_1jU>>>0;if(((_1jY>>>0&((_1kk-1>>>0^4294967295)>>>0^_1kk)>>>0)>>>0&4294967295)==_1jT){return ((_1jY>>>0&_1kk)>>>0==0)?new T4(0,_1jT,_1jU,E(B(_1kl(_1jV,_1jY,_1jZ,_1k0,_1k1))),E(_1jW)):new T4(0,_1jT,_1jU,E(_1jV),E(B(_1kl(_1jW,_1jY,_1jZ,_1k0,_1k1))));}else{var _1km=(_1jT>>>0^_1jY>>>0)>>>0,_1kn=(_1km|_1km>>>1)>>>0,_1ko=(_1kn|_1kn>>>2)>>>0,_1kp=(_1ko|_1ko>>>4)>>>0,_1kq=(_1kp|_1kp>>>8)>>>0,_1kr=(_1kq|_1kq>>>16)>>>0,_1ks=(_1kr^_1kr>>>1)>>>0&4294967295,_1kt=_1ks>>>0;return ((_1jT>>>0&_1kt)>>>0==0)?new T4(0,(_1jT>>>0&((_1kt-1>>>0^4294967295)>>>0^_1kt)>>>0)>>>0&4294967295,_1ks,E(_1jS),E(_1jX)):new T4(0,(_1jT>>>0&((_1kt-1>>>0^4294967295)>>>0^_1kt)>>>0)>>>0&4294967295,_1ks,E(_1jX),E(_1jS));}}break;case 1:var _1ku=_1jX.a;return new F(function(){return _1jy(_1ku,_1jX.b,_1ku,_1jT,_1jU,_1jV,_1jW);});break;default:return E(_1jS);}break;case 1:var _1kv=_1jS.a;return new F(function(){return _1iE(_1kv,_1jS.b,_1kv,_1jR);});break;default:return E(_1jR);}},_1kb=function(_1kw,_1kx,_1ky,_1kz,_1kA){var _1kB=E(_1kA);switch(_1kB._){case 0:var _1kC=_1kB.a,_1kD=_1kB.b,_1kE=_1kB.c,_1kF=_1kB.d;if(_1kx>>>0<=_1kD>>>0){if(_1kD>>>0<=_1kx>>>0){if(_1kw!=_1kC){var _1kG=(_1kw>>>0^_1kC>>>0)>>>0,_1kH=(_1kG|_1kG>>>1)>>>0,_1kI=(_1kH|_1kH>>>2)>>>0,_1kJ=(_1kI|_1kI>>>4)>>>0,_1kK=(_1kJ|_1kJ>>>8)>>>0,_1kL=(_1kK|_1kK>>>16)>>>0,_1kM=(_1kL^_1kL>>>1)>>>0&4294967295,_1kN=_1kM>>>0;return ((_1kw>>>0&_1kN)>>>0==0)?new T4(0,(_1kw>>>0&((_1kN-1>>>0^4294967295)>>>0^_1kN)>>>0)>>>0&4294967295,_1kM,E(new T4(0,_1kw,_1kx,E(_1ky),E(_1kz))),E(_1kB)):new T4(0,(_1kw>>>0&((_1kN-1>>>0^4294967295)>>>0^_1kN)>>>0)>>>0&4294967295,_1kM,E(_1kB),E(new T4(0,_1kw,_1kx,E(_1ky),E(_1kz))));}else{return new T4(0,_1kw,_1kx,E(B(_1jP(_1ky,_1kE))),E(B(_1jP(_1kz,_1kF))));}}else{var _1kO=_1kD>>>0;if(((_1kw>>>0&((_1kO-1>>>0^4294967295)>>>0^_1kO)>>>0)>>>0&4294967295)==_1kC){return ((_1kw>>>0&_1kO)>>>0==0)?new T4(0,_1kC,_1kD,E(B(_1kb(_1kw,_1kx,_1ky,_1kz,_1kE))),E(_1kF)):new T4(0,_1kC,_1kD,E(_1kE),E(B(_1kb(_1kw,_1kx,_1ky,_1kz,_1kF))));}else{var _1kP=(_1kw>>>0^_1kC>>>0)>>>0,_1kQ=(_1kP|_1kP>>>1)>>>0,_1kR=(_1kQ|_1kQ>>>2)>>>0,_1kS=(_1kR|_1kR>>>4)>>>0,_1kT=(_1kS|_1kS>>>8)>>>0,_1kU=(_1kT|_1kT>>>16)>>>0,_1kV=(_1kU^_1kU>>>1)>>>0&4294967295,_1kW=_1kV>>>0;return ((_1kw>>>0&_1kW)>>>0==0)?new T4(0,(_1kw>>>0&((_1kW-1>>>0^4294967295)>>>0^_1kW)>>>0)>>>0&4294967295,_1kV,E(new T4(0,_1kw,_1kx,E(_1ky),E(_1kz))),E(_1kB)):new T4(0,(_1kw>>>0&((_1kW-1>>>0^4294967295)>>>0^_1kW)>>>0)>>>0&4294967295,_1kV,E(_1kB),E(new T4(0,_1kw,_1kx,E(_1ky),E(_1kz))));}}}else{var _1kX=_1kx>>>0;if(((_1kC>>>0&((_1kX-1>>>0^4294967295)>>>0^_1kX)>>>0)>>>0&4294967295)==_1kw){return ((_1kC>>>0&_1kX)>>>0==0)?new T4(0,_1kw,_1kx,E(B(_1kl(_1ky,_1kC,_1kD,_1kE,_1kF))),E(_1kz)):new T4(0,_1kw,_1kx,E(_1ky),E(B(_1kl(_1kz,_1kC,_1kD,_1kE,_1kF))));}else{var _1kY=(_1kw>>>0^_1kC>>>0)>>>0,_1kZ=(_1kY|_1kY>>>1)>>>0,_1l0=(_1kZ|_1kZ>>>2)>>>0,_1l1=(_1l0|_1l0>>>4)>>>0,_1l2=(_1l1|_1l1>>>8)>>>0,_1l3=(_1l2|_1l2>>>16)>>>0,_1l4=(_1l3^_1l3>>>1)>>>0&4294967295,_1l5=_1l4>>>0;return ((_1kw>>>0&_1l5)>>>0==0)?new T4(0,(_1kw>>>0&((_1l5-1>>>0^4294967295)>>>0^_1l5)>>>0)>>>0&4294967295,_1l4,E(new T4(0,_1kw,_1kx,E(_1ky),E(_1kz))),E(_1kB)):new T4(0,(_1kw>>>0&((_1l5-1>>>0^4294967295)>>>0^_1l5)>>>0)>>>0&4294967295,_1l4,E(_1kB),E(new T4(0,_1kw,_1kx,E(_1ky),E(_1kz))));}}break;case 1:var _1l6=_1kB.a;return new F(function(){return _1jy(_1l6,_1kB.b,_1l6,_1kw,_1kx,_1ky,_1kz);});break;default:return new T4(0,_1kw,_1kx,E(_1ky),E(_1kz));}},_1kl=function(_1l7,_1l8,_1l9,_1la,_1lb){var _1lc=E(_1l7);switch(_1lc._){case 0:var _1ld=_1lc.a,_1le=_1lc.b,_1lf=_1lc.c,_1lg=_1lc.d;if(_1le>>>0<=_1l9>>>0){if(_1l9>>>0<=_1le>>>0){if(_1ld!=_1l8){var _1lh=(_1ld>>>0^_1l8>>>0)>>>0,_1li=(_1lh|_1lh>>>1)>>>0,_1lj=(_1li|_1li>>>2)>>>0,_1lk=(_1lj|_1lj>>>4)>>>0,_1ll=(_1lk|_1lk>>>8)>>>0,_1lm=(_1ll|_1ll>>>16)>>>0,_1ln=(_1lm^_1lm>>>1)>>>0&4294967295,_1lo=_1ln>>>0;return ((_1ld>>>0&_1lo)>>>0==0)?new T4(0,(_1ld>>>0&((_1lo-1>>>0^4294967295)>>>0^_1lo)>>>0)>>>0&4294967295,_1ln,E(_1lc),E(new T4(0,_1l8,_1l9,E(_1la),E(_1lb)))):new T4(0,(_1ld>>>0&((_1lo-1>>>0^4294967295)>>>0^_1lo)>>>0)>>>0&4294967295,_1ln,E(new T4(0,_1l8,_1l9,E(_1la),E(_1lb))),E(_1lc));}else{return new T4(0,_1ld,_1le,E(B(_1jP(_1lf,_1la))),E(B(_1jP(_1lg,_1lb))));}}else{var _1lp=_1l9>>>0;if(((_1ld>>>0&((_1lp-1>>>0^4294967295)>>>0^_1lp)>>>0)>>>0&4294967295)==_1l8){return ((_1ld>>>0&_1lp)>>>0==0)?new T4(0,_1l8,_1l9,E(B(_1kb(_1ld,_1le,_1lf,_1lg,_1la))),E(_1lb)):new T4(0,_1l8,_1l9,E(_1la),E(B(_1kb(_1ld,_1le,_1lf,_1lg,_1lb))));}else{var _1lq=(_1ld>>>0^_1l8>>>0)>>>0,_1lr=(_1lq|_1lq>>>1)>>>0,_1ls=(_1lr|_1lr>>>2)>>>0,_1lt=(_1ls|_1ls>>>4)>>>0,_1lu=(_1lt|_1lt>>>8)>>>0,_1lv=(_1lu|_1lu>>>16)>>>0,_1lw=(_1lv^_1lv>>>1)>>>0&4294967295,_1lx=_1lw>>>0;return ((_1ld>>>0&_1lx)>>>0==0)?new T4(0,(_1ld>>>0&((_1lx-1>>>0^4294967295)>>>0^_1lx)>>>0)>>>0&4294967295,_1lw,E(_1lc),E(new T4(0,_1l8,_1l9,E(_1la),E(_1lb)))):new T4(0,(_1ld>>>0&((_1lx-1>>>0^4294967295)>>>0^_1lx)>>>0)>>>0&4294967295,_1lw,E(new T4(0,_1l8,_1l9,E(_1la),E(_1lb))),E(_1lc));}}}else{var _1ly=_1le>>>0;if(((_1l8>>>0&((_1ly-1>>>0^4294967295)>>>0^_1ly)>>>0)>>>0&4294967295)==_1ld){return ((_1l8>>>0&_1ly)>>>0==0)?new T4(0,_1ld,_1le,E(B(_1kl(_1lf,_1l8,_1l9,_1la,_1lb))),E(_1lg)):new T4(0,_1ld,_1le,E(_1lf),E(B(_1kl(_1lg,_1l8,_1l9,_1la,_1lb))));}else{var _1lz=(_1ld>>>0^_1l8>>>0)>>>0,_1lA=(_1lz|_1lz>>>1)>>>0,_1lB=(_1lA|_1lA>>>2)>>>0,_1lC=(_1lB|_1lB>>>4)>>>0,_1lD=(_1lC|_1lC>>>8)>>>0,_1lE=(_1lD|_1lD>>>16)>>>0,_1lF=(_1lE^_1lE>>>1)>>>0&4294967295,_1lG=_1lF>>>0;return ((_1ld>>>0&_1lG)>>>0==0)?new T4(0,(_1ld>>>0&((_1lG-1>>>0^4294967295)>>>0^_1lG)>>>0)>>>0&4294967295,_1lF,E(_1lc),E(new T4(0,_1l8,_1l9,E(_1la),E(_1lb)))):new T4(0,(_1ld>>>0&((_1lG-1>>>0^4294967295)>>>0^_1lG)>>>0)>>>0&4294967295,_1lF,E(new T4(0,_1l8,_1l9,E(_1la),E(_1lb))),E(_1lc));}}break;case 1:var _1lH=_1lc.a,_1lI=_1lc.b,_1lJ=_1l9>>>0;if(((_1lH>>>0&((_1lJ-1>>>0^4294967295)>>>0^_1lJ)>>>0)>>>0&4294967295)==_1l8){return ((_1lH>>>0&_1lJ)>>>0==0)?new T4(0,_1l8,_1l9,E(B(_1iE(_1lH,_1lI,_1lH,_1la))),E(_1lb)):new T4(0,_1l8,_1l9,E(_1la),E(B(_1iE(_1lH,_1lI,_1lH,_1lb))));}else{var _1lK=(_1lH>>>0^_1l8>>>0)>>>0,_1lL=(_1lK|_1lK>>>1)>>>0,_1lM=(_1lL|_1lL>>>2)>>>0,_1lN=(_1lM|_1lM>>>4)>>>0,_1lO=(_1lN|_1lN>>>8)>>>0,_1lP=(_1lO|_1lO>>>16)>>>0,_1lQ=(_1lP^_1lP>>>1)>>>0&4294967295,_1lR=_1lQ>>>0;return ((_1lH>>>0&_1lR)>>>0==0)?new T4(0,(_1lH>>>0&((_1lR-1>>>0^4294967295)>>>0^_1lR)>>>0)>>>0&4294967295,_1lQ,E(new T2(1,_1lH,_1lI)),E(new T4(0,_1l8,_1l9,E(_1la),E(_1lb)))):new T4(0,(_1lH>>>0&((_1lR-1>>>0^4294967295)>>>0^_1lR)>>>0)>>>0&4294967295,_1lQ,E(new T4(0,_1l8,_1l9,E(_1la),E(_1lb))),E(new T2(1,_1lH,_1lI)));}break;default:return new T4(0,_1l8,_1l9,E(_1la),E(_1lb));}};return new F(function(){return _1jP(_1iC,_1iD);});},_1lS=function(_1lT,_1lU,_1lV){return new F(function(){return _1iA(_1iu,_1lU,_1lV);});},_1lW=function(_1lX,_1lY){return E(_1lX);},_1lZ=new T2(0,_4l,_PY),_1m0=function(_1m1,_1m2){while(1){var _1m3=B((function(_1m4,_1m5){var _1m6=E(_1m5);if(!_1m6._){_1m1=new T2(1,_1m6.b,new T(function(){return B(_1m0(_1m4,_1m6.d));}));_1m2=_1m6.c;return __continue;}else{return E(_1m4);}})(_1m1,_1m2));if(_1m3!=__continue){return _1m3;}}},_1m7=function(_1m8,_1m9,_1ma){var _1mb=function(_1mc){var _1md=function(_1me){if(_1mc!=_1me){return false;}else{return new F(function(){return _17w(_1m8,B(_1m0(_4,_1m9)),B(_1m0(_4,_1ma)));});}},_1mf=E(_1ma);if(!_1mf._){return new F(function(){return _1md(_1mf.a);});}else{return new F(function(){return _1md(0);});}},_1mg=E(_1m9);if(!_1mg._){return new F(function(){return _1mb(_1mg.a);});}else{return new F(function(){return _1mb(0);});}},_1mh=function(_1mi,_1mj){return (!B(_1m7(_19I,_1mi,_1mj)))?true:false;},_1mk=function(_1ml,_1mm){return new F(function(){return _1m7(_19I,_1ml,_1mm);});},_1mn=new T2(0,_1mk,_1mh),_1mo=function(_1mp,_1mq){var _1mr=function(_1ms){while(1){var _1mt=E(_1ms);switch(_1mt._){case 0:var _1mu=_1mt.b>>>0;if(((_1mp>>>0&((_1mu-1>>>0^4294967295)>>>0^_1mu)>>>0)>>>0&4294967295)==_1mt.a){if(!((_1mp>>>0&_1mu)>>>0)){_1ms=_1mt.c;continue;}else{_1ms=_1mt.d;continue;}}else{return false;}break;case 1:return _1mp==_1mt.a;default:return false;}}};return new F(function(){return _1mr(_1mq);});},_1mv=function(_1mw,_1mx){var _1my=function(_1mz){while(1){var _1mA=E(_1mz);switch(_1mA._){case 0:var _1mB=_1mA.b>>>0;if(((_1mw>>>0&((_1mB-1>>>0^4294967295)>>>0^_1mB)>>>0)>>>0&4294967295)==_1mA.a){if(!((_1mw>>>0&_1mB)>>>0)){_1mz=_1mA.c;continue;}else{_1mz=_1mA.d;continue;}}else{return false;}break;case 1:return ((_1mw&(-32))!=_1mA.a)?false:((1<<(_1mw&31)>>>0&_1mA.b)>>>0==0)?false:true;default:return false;}}};return new F(function(){return _1my(_1mx);});},_1mC=function(_1mD,_1mE,_1mF){while(1){var _1mG=E(_1mE);switch(_1mG._){case 0:var _1mH=E(_1mF);if(!_1mH._){if(_1mG.b!=_1mH.b){return false;}else{if(_1mG.a!=_1mH.a){return false;}else{if(!B(_1mC(_1mD,_1mG.c,_1mH.c))){return false;}else{_1mE=_1mG.d;_1mF=_1mH.d;continue;}}}}else{return false;}break;case 1:var _1mI=E(_1mF);if(_1mI._==1){if(_1mG.a!=_1mI.a){return false;}else{return new F(function(){return A3(_ou,_1mD,_1mG.b,_1mI.b);});}}else{return false;}break;default:return (E(_1mF)._==2)?true:false;}}},_1mJ=function(_1mK,_1mL){var _1mM=E(_1mL);if(!_1mM._){var _1mN=_1mM.b,_1mO=_1mM.c,_1mP=_1mM.d;if(!B(A1(_1mK,_1mN))){return new F(function(){return _14v(B(_1mJ(_1mK,_1mO)),B(_1mJ(_1mK,_1mP)));});}else{return new F(function(){return _Nu(_1mN,B(_1mJ(_1mK,_1mO)),B(_1mJ(_1mK,_1mP)));});}}else{return new T0(1);}},_1mQ=function(_1mR,_1mS,_1mT){var _1mU=E(_1mT);switch(_1mU._){case 0:var _1mV=_1mU.a,_1mW=_1mU.b,_1mX=_1mU.c,_1mY=_1mU.d,_1mZ=_1mW>>>0;if(((_1mR>>>0&((_1mZ-1>>>0^4294967295)>>>0^_1mZ)>>>0)>>>0&4294967295)==_1mV){return ((_1mR>>>0&_1mZ)>>>0==0)?new T4(0,_1mV,_1mW,E(B(_1mQ(_1mR,_1mS,_1mX))),E(_1mY)):new T4(0,_1mV,_1mW,E(_1mX),E(B(_1mQ(_1mR,_1mS,_1mY))));}else{var _1n0=(_1mR>>>0^_1mV>>>0)>>>0,_1n1=(_1n0|_1n0>>>1)>>>0,_1n2=(_1n1|_1n1>>>2)>>>0,_1n3=(_1n2|_1n2>>>4)>>>0,_1n4=(_1n3|_1n3>>>8)>>>0,_1n5=(_1n4|_1n4>>>16)>>>0,_1n6=(_1n5^_1n5>>>1)>>>0&4294967295,_1n7=_1n6>>>0;return ((_1mR>>>0&_1n7)>>>0==0)?new T4(0,(_1mR>>>0&((_1n7-1>>>0^4294967295)>>>0^_1n7)>>>0)>>>0&4294967295,_1n6,E(new T2(1,_1mR,_1mS)),E(_1mU)):new T4(0,(_1mR>>>0&((_1n7-1>>>0^4294967295)>>>0^_1n7)>>>0)>>>0&4294967295,_1n6,E(_1mU),E(new T2(1,_1mR,_1mS)));}break;case 1:var _1n8=_1mU.a;if(_1n8!=_1mR){var _1n9=(_1mR>>>0^_1n8>>>0)>>>0,_1na=(_1n9|_1n9>>>1)>>>0,_1nb=(_1na|_1na>>>2)>>>0,_1nc=(_1nb|_1nb>>>4)>>>0,_1nd=(_1nc|_1nc>>>8)>>>0,_1ne=(_1nd|_1nd>>>16)>>>0,_1nf=(_1ne^_1ne>>>1)>>>0&4294967295,_1ng=_1nf>>>0;return ((_1mR>>>0&_1ng)>>>0==0)?new T4(0,(_1mR>>>0&((_1ng-1>>>0^4294967295)>>>0^_1ng)>>>0)>>>0&4294967295,_1nf,E(new T2(1,_1mR,_1mS)),E(_1mU)):new T4(0,(_1mR>>>0&((_1ng-1>>>0^4294967295)>>>0^_1ng)>>>0)>>>0&4294967295,_1nf,E(_1mU),E(new T2(1,_1mR,_1mS)));}else{return new T2(1,_1n8,(_1mS|_1mU.b)>>>0);}break;default:return new T2(1,_1mR,_1mS);}},_1nh=function(_1ni,_1nj){while(1){var _1nk=E(_1ni);if(!_1nk._){return E(_1nj);}else{var _1nl=E(E(_1nk.a).b),_1nm=B(_1mQ(_1nl&(-32),1<<(_1nl&31)>>>0,_1nj));_1ni=_1nk.b;_1nj=_1nm;continue;}}},_1nn=function(_1no,_1np){while(1){var _1nq=E(_1no);if(!_1nq._){return E(_1np);}else{var _1nr=B(_1nh(E(_1nq.a).a,_1np));_1no=_1nq.b;_1np=_1nr;continue;}}},_1ns=function(_1nt,_1nu){while(1){var _1nv=E(_1nu);if(!_1nv._){var _1nw=_1nv.c,_1nx=_1nv.d,_1ny=E(_1nv.b);if(!_1ny._){var _1nz=B(_1nn(_1ny.b,B(_1ns(_1nt,_1nx))));_1nt=_1nz;_1nu=_1nw;continue;}else{var _1nz=B(_1ns(_1nt,_1nx));_1nt=_1nz;_1nu=_1nw;continue;}}else{return E(_1nt);}}},_1nA=-1,_1nB=-2,_1nC=-3,_1nD=new T2(1,_KR,_4),_1nE=new T2(1,_1nC,_1nD),_1nF=new T2(1,_1nB,_1nE),_1nG=new T2(1,_1nA,_1nF),_1nH=function(_1nI,_1nJ,_1nK){var _1nL=function(_1nM,_1nN){if(!B(_1mC(_1mn,_1nI,_1nM))){return new F(function(){return _1nH(_1nM,_1nN,_1nK);});}else{return E(_1nI);}},_1nO=function(_1nP){if(!B(_uH(_hJ,_1nP,_1nG))){var _1nQ=E(_1nP);if(!B(_1mo(_1nQ,_1nI))){return new F(function(){return _1mv(_1nQ,_1nJ);});}else{return true;}}else{return true;}},_1nR=function(_1nS){while(1){var _1nT=E(_1nS);if(!_1nT._){return true;}else{if(!B(_1nO(E(_1nT.a).b))){return false;}else{_1nS=_1nT.b;continue;}}}},_1nU=function(_1nV){var _1nW=E(_1nV);switch(_1nW._){case 0:return new F(function(){return _1nR(_1nW.b);});break;case 1:return new F(function(){return _1nO(_1nW.a);});break;default:return true;}},_1nX=function(_1nY,_1nZ,_1o0){while(1){var _1o1=B((function(_1o2,_1o3,_1o4){var _1o5=E(_1o4);switch(_1o5._){case 0:var _1o6=B(_1nX(_1o2,_1o3,_1o5.d));_1nY=_1o6.a;_1nZ=_1o6.b;_1o0=_1o5.c;return __continue;case 1:var _1o7=E(_1o2),_1o8=E(_1o3),_1o9=B(_1mJ(_1nU,_1o5.b));return (_1o9._==0)?new T2(0,new T(function(){return B(_13c(_1o5.a,_1o9,_1o7));}),new T(function(){return B(_1ns(_1o8,_1o9));})):new T2(0,_1o7,_1o8);default:return new T2(0,_1o2,_1o3);}})(_1nY,_1nZ,_1o0));if(_1o1!=__continue){return _1o1;}}},_1oa=E(_1nK);if(!_1oa._){var _1ob=_1oa.c,_1oc=_1oa.d;if(_1oa.b>=0){var _1od=B(_1nX(_Tf,_17g,_1oc)),_1oe=B(_1nX(_1od.a,_1od.b,_1ob));return new F(function(){return _1nL(_1oe.a,_1oe.b);});}else{var _1of=B(_1nX(_Tf,_17g,_1ob)),_1og=B(_1nX(_1of.a,_1of.b,_1oc));return new F(function(){return _1nL(_1og.a,_1og.b);});}}else{var _1oh=B(_1nX(_Tf,_17g,_1oa));return new F(function(){return _1nL(_1oh.a,_1oh.b);});}},_1oi=function(_1oj,_1ok){while(1){var _1ol=E(_1ok);if(!_1ol._){return E(_1oj);}else{var _1om=E(_1ol.a),_1on=B(_13c(E(_1om.a),_1om.b,_1oj));_1oj=_1on;_1ok=_1ol.b;continue;}}},_1oo=function(_1op){var _1oq=E(_1op);return (_1oq._==0)?(E(_1oq.b)._==0)?true:false:false;},_1or=new T(function(){return B(unCStr(")"));}),_1os=function(_1ot,_1ou){var _1ov=new T(function(){var _1ow=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_cp(0,_1ou,_4)),_1or));})));},1);return B(_0(B(_cp(0,_1ot,_4)),_1ow));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1ov)));});},_1ox=new T(function(){return B(_7f("pgf/PGF/Optimize.hs:(259,9)-(262,117)|function getFunctions"));}),_1oy=new T(function(){return B(unCStr("&|"));}),_1oz=new T2(1,_1oy,_4),_1oA=new T(function(){return B(unCStr("&+"));}),_1oB=new T2(1,_1oA,_4),_1oC=new T(function(){return B(_7f("pgf/PGF/Optimize.hs:(235,9)-(245,73)|function seq2prefix"));}),_1oD=function(_1oE,_1oF,_1oG,_1oH,_1oI,_1oJ){var _1oK=_1oH>>>0;if(((_1oE>>>0&((_1oK-1>>>0^4294967295)>>>0^_1oK)>>>0)>>>0&4294967295)==_1oG){return ((_1oE>>>0&_1oK)>>>0==0)?new T4(0,_1oG,_1oH,E(B(_1mQ(_1oE,_1oF,_1oI))),E(_1oJ)):new T4(0,_1oG,_1oH,E(_1oI),E(B(_1mQ(_1oE,_1oF,_1oJ))));}else{var _1oL=(_1oE>>>0^_1oG>>>0)>>>0,_1oM=(_1oL|_1oL>>>1)>>>0,_1oN=(_1oM|_1oM>>>2)>>>0,_1oO=(_1oN|_1oN>>>4)>>>0,_1oP=(_1oO|_1oO>>>8)>>>0,_1oQ=(_1oP|_1oP>>>16)>>>0,_1oR=(_1oQ^_1oQ>>>1)>>>0&4294967295,_1oS=_1oR>>>0;return ((_1oE>>>0&_1oS)>>>0==0)?new T4(0,(_1oE>>>0&((_1oS-1>>>0^4294967295)>>>0^_1oS)>>>0)>>>0&4294967295,_1oR,E(new T2(1,_1oE,_1oF)),E(new T4(0,_1oG,_1oH,E(_1oI),E(_1oJ)))):new T4(0,(_1oE>>>0&((_1oS-1>>>0^4294967295)>>>0^_1oS)>>>0)>>>0&4294967295,_1oR,E(new T4(0,_1oG,_1oH,E(_1oI),E(_1oJ))),E(new T2(1,_1oE,_1oF)));}},_1oT=function(_1oU,_1oV,_1oW,_1oX,_1oY){var _1oZ=E(_1oY);switch(_1oZ._){case 0:var _1p0=_1oZ.a,_1p1=_1oZ.b,_1p2=_1oZ.c,_1p3=_1oZ.d;if(_1oV>>>0<=_1p1>>>0){if(_1p1>>>0<=_1oV>>>0){if(_1oU!=_1p0){var _1p4=(_1oU>>>0^_1p0>>>0)>>>0,_1p5=(_1p4|_1p4>>>1)>>>0,_1p6=(_1p5|_1p5>>>2)>>>0,_1p7=(_1p6|_1p6>>>4)>>>0,_1p8=(_1p7|_1p7>>>8)>>>0,_1p9=(_1p8|_1p8>>>16)>>>0,_1pa=(_1p9^_1p9>>>1)>>>0&4294967295,_1pb=_1pa>>>0;return ((_1oU>>>0&_1pb)>>>0==0)?new T4(0,(_1oU>>>0&((_1pb-1>>>0^4294967295)>>>0^_1pb)>>>0)>>>0&4294967295,_1pa,E(new T4(0,_1oU,_1oV,E(_1oW),E(_1oX))),E(_1oZ)):new T4(0,(_1oU>>>0&((_1pb-1>>>0^4294967295)>>>0^_1pb)>>>0)>>>0&4294967295,_1pa,E(_1oZ),E(new T4(0,_1oU,_1oV,E(_1oW),E(_1oX))));}else{return new T4(0,_1oU,_1oV,E(B(_1pc(_1oW,_1p2))),E(B(_1pc(_1oX,_1p3))));}}else{var _1pd=_1p1>>>0;if(((_1oU>>>0&((_1pd-1>>>0^4294967295)>>>0^_1pd)>>>0)>>>0&4294967295)==_1p0){return ((_1oU>>>0&_1pd)>>>0==0)?new T4(0,_1p0,_1p1,E(B(_1oT(_1oU,_1oV,_1oW,_1oX,_1p2))),E(_1p3)):new T4(0,_1p0,_1p1,E(_1p2),E(B(_1oT(_1oU,_1oV,_1oW,_1oX,_1p3))));}else{var _1pe=(_1oU>>>0^_1p0>>>0)>>>0,_1pf=(_1pe|_1pe>>>1)>>>0,_1pg=(_1pf|_1pf>>>2)>>>0,_1ph=(_1pg|_1pg>>>4)>>>0,_1pi=(_1ph|_1ph>>>8)>>>0,_1pj=(_1pi|_1pi>>>16)>>>0,_1pk=(_1pj^_1pj>>>1)>>>0&4294967295,_1pl=_1pk>>>0;return ((_1oU>>>0&_1pl)>>>0==0)?new T4(0,(_1oU>>>0&((_1pl-1>>>0^4294967295)>>>0^_1pl)>>>0)>>>0&4294967295,_1pk,E(new T4(0,_1oU,_1oV,E(_1oW),E(_1oX))),E(_1oZ)):new T4(0,(_1oU>>>0&((_1pl-1>>>0^4294967295)>>>0^_1pl)>>>0)>>>0&4294967295,_1pk,E(_1oZ),E(new T4(0,_1oU,_1oV,E(_1oW),E(_1oX))));}}}else{var _1pm=_1oV>>>0;if(((_1p0>>>0&((_1pm-1>>>0^4294967295)>>>0^_1pm)>>>0)>>>0&4294967295)==_1oU){return ((_1p0>>>0&_1pm)>>>0==0)?new T4(0,_1oU,_1oV,E(B(_1pn(_1oW,_1p0,_1p1,_1p2,_1p3))),E(_1oX)):new T4(0,_1oU,_1oV,E(_1oW),E(B(_1pn(_1oX,_1p0,_1p1,_1p2,_1p3))));}else{var _1po=(_1oU>>>0^_1p0>>>0)>>>0,_1pp=(_1po|_1po>>>1)>>>0,_1pq=(_1pp|_1pp>>>2)>>>0,_1pr=(_1pq|_1pq>>>4)>>>0,_1ps=(_1pr|_1pr>>>8)>>>0,_1pt=(_1ps|_1ps>>>16)>>>0,_1pu=(_1pt^_1pt>>>1)>>>0&4294967295,_1pv=_1pu>>>0;return ((_1oU>>>0&_1pv)>>>0==0)?new T4(0,(_1oU>>>0&((_1pv-1>>>0^4294967295)>>>0^_1pv)>>>0)>>>0&4294967295,_1pu,E(new T4(0,_1oU,_1oV,E(_1oW),E(_1oX))),E(_1oZ)):new T4(0,(_1oU>>>0&((_1pv-1>>>0^4294967295)>>>0^_1pv)>>>0)>>>0&4294967295,_1pu,E(_1oZ),E(new T4(0,_1oU,_1oV,E(_1oW),E(_1oX))));}}break;case 1:return new F(function(){return _1oD(_1oZ.a,_1oZ.b,_1oU,_1oV,_1oW,_1oX);});break;default:return new T4(0,_1oU,_1oV,E(_1oW),E(_1oX));}},_1pn=function(_1pw,_1px,_1py,_1pz,_1pA){var _1pB=E(_1pw);switch(_1pB._){case 0:var _1pC=_1pB.a,_1pD=_1pB.b,_1pE=_1pB.c,_1pF=_1pB.d;if(_1pD>>>0<=_1py>>>0){if(_1py>>>0<=_1pD>>>0){if(_1pC!=_1px){var _1pG=(_1pC>>>0^_1px>>>0)>>>0,_1pH=(_1pG|_1pG>>>1)>>>0,_1pI=(_1pH|_1pH>>>2)>>>0,_1pJ=(_1pI|_1pI>>>4)>>>0,_1pK=(_1pJ|_1pJ>>>8)>>>0,_1pL=(_1pK|_1pK>>>16)>>>0,_1pM=(_1pL^_1pL>>>1)>>>0&4294967295,_1pN=_1pM>>>0;return ((_1pC>>>0&_1pN)>>>0==0)?new T4(0,(_1pC>>>0&((_1pN-1>>>0^4294967295)>>>0^_1pN)>>>0)>>>0&4294967295,_1pM,E(_1pB),E(new T4(0,_1px,_1py,E(_1pz),E(_1pA)))):new T4(0,(_1pC>>>0&((_1pN-1>>>0^4294967295)>>>0^_1pN)>>>0)>>>0&4294967295,_1pM,E(new T4(0,_1px,_1py,E(_1pz),E(_1pA))),E(_1pB));}else{return new T4(0,_1pC,_1pD,E(B(_1pc(_1pE,_1pz))),E(B(_1pc(_1pF,_1pA))));}}else{var _1pO=_1py>>>0;if(((_1pC>>>0&((_1pO-1>>>0^4294967295)>>>0^_1pO)>>>0)>>>0&4294967295)==_1px){return ((_1pC>>>0&_1pO)>>>0==0)?new T4(0,_1px,_1py,E(B(_1oT(_1pC,_1pD,_1pE,_1pF,_1pz))),E(_1pA)):new T4(0,_1px,_1py,E(_1pz),E(B(_1oT(_1pC,_1pD,_1pE,_1pF,_1pA))));}else{var _1pP=(_1pC>>>0^_1px>>>0)>>>0,_1pQ=(_1pP|_1pP>>>1)>>>0,_1pR=(_1pQ|_1pQ>>>2)>>>0,_1pS=(_1pR|_1pR>>>4)>>>0,_1pT=(_1pS|_1pS>>>8)>>>0,_1pU=(_1pT|_1pT>>>16)>>>0,_1pV=(_1pU^_1pU>>>1)>>>0&4294967295,_1pW=_1pV>>>0;return ((_1pC>>>0&_1pW)>>>0==0)?new T4(0,(_1pC>>>0&((_1pW-1>>>0^4294967295)>>>0^_1pW)>>>0)>>>0&4294967295,_1pV,E(_1pB),E(new T4(0,_1px,_1py,E(_1pz),E(_1pA)))):new T4(0,(_1pC>>>0&((_1pW-1>>>0^4294967295)>>>0^_1pW)>>>0)>>>0&4294967295,_1pV,E(new T4(0,_1px,_1py,E(_1pz),E(_1pA))),E(_1pB));}}}else{var _1pX=_1pD>>>0;if(((_1px>>>0&((_1pX-1>>>0^4294967295)>>>0^_1pX)>>>0)>>>0&4294967295)==_1pC){return ((_1px>>>0&_1pX)>>>0==0)?new T4(0,_1pC,_1pD,E(B(_1pn(_1pE,_1px,_1py,_1pz,_1pA))),E(_1pF)):new T4(0,_1pC,_1pD,E(_1pE),E(B(_1pn(_1pF,_1px,_1py,_1pz,_1pA))));}else{var _1pY=(_1pC>>>0^_1px>>>0)>>>0,_1pZ=(_1pY|_1pY>>>1)>>>0,_1q0=(_1pZ|_1pZ>>>2)>>>0,_1q1=(_1q0|_1q0>>>4)>>>0,_1q2=(_1q1|_1q1>>>8)>>>0,_1q3=(_1q2|_1q2>>>16)>>>0,_1q4=(_1q3^_1q3>>>1)>>>0&4294967295,_1q5=_1q4>>>0;return ((_1pC>>>0&_1q5)>>>0==0)?new T4(0,(_1pC>>>0&((_1q5-1>>>0^4294967295)>>>0^_1q5)>>>0)>>>0&4294967295,_1q4,E(_1pB),E(new T4(0,_1px,_1py,E(_1pz),E(_1pA)))):new T4(0,(_1pC>>>0&((_1q5-1>>>0^4294967295)>>>0^_1q5)>>>0)>>>0&4294967295,_1q4,E(new T4(0,_1px,_1py,E(_1pz),E(_1pA))),E(_1pB));}}break;case 1:return new F(function(){return _1oD(_1pB.a,_1pB.b,_1px,_1py,_1pz,_1pA);});break;default:return new T4(0,_1px,_1py,E(_1pz),E(_1pA));}},_1pc=function(_1q6,_1q7){var _1q8=E(_1q6);switch(_1q8._){case 0:var _1q9=_1q8.a,_1qa=_1q8.b,_1qb=_1q8.c,_1qc=_1q8.d,_1qd=E(_1q7);switch(_1qd._){case 0:var _1qe=_1qd.a,_1qf=_1qd.b,_1qg=_1qd.c,_1qh=_1qd.d;if(_1qa>>>0<=_1qf>>>0){if(_1qf>>>0<=_1qa>>>0){if(_1q9!=_1qe){var _1qi=(_1q9>>>0^_1qe>>>0)>>>0,_1qj=(_1qi|_1qi>>>1)>>>0,_1qk=(_1qj|_1qj>>>2)>>>0,_1ql=(_1qk|_1qk>>>4)>>>0,_1qm=(_1ql|_1ql>>>8)>>>0,_1qn=(_1qm|_1qm>>>16)>>>0,_1qo=(_1qn^_1qn>>>1)>>>0&4294967295,_1qp=_1qo>>>0;return ((_1q9>>>0&_1qp)>>>0==0)?new T4(0,(_1q9>>>0&((_1qp-1>>>0^4294967295)>>>0^_1qp)>>>0)>>>0&4294967295,_1qo,E(_1q8),E(_1qd)):new T4(0,(_1q9>>>0&((_1qp-1>>>0^4294967295)>>>0^_1qp)>>>0)>>>0&4294967295,_1qo,E(_1qd),E(_1q8));}else{return new T4(0,_1q9,_1qa,E(B(_1pc(_1qb,_1qg))),E(B(_1pc(_1qc,_1qh))));}}else{var _1qq=_1qf>>>0;if(((_1q9>>>0&((_1qq-1>>>0^4294967295)>>>0^_1qq)>>>0)>>>0&4294967295)==_1qe){return ((_1q9>>>0&_1qq)>>>0==0)?new T4(0,_1qe,_1qf,E(B(_1oT(_1q9,_1qa,_1qb,_1qc,_1qg))),E(_1qh)):new T4(0,_1qe,_1qf,E(_1qg),E(B(_1oT(_1q9,_1qa,_1qb,_1qc,_1qh))));}else{var _1qr=(_1q9>>>0^_1qe>>>0)>>>0,_1qs=(_1qr|_1qr>>>1)>>>0,_1qt=(_1qs|_1qs>>>2)>>>0,_1qu=(_1qt|_1qt>>>4)>>>0,_1qv=(_1qu|_1qu>>>8)>>>0,_1qw=(_1qv|_1qv>>>16)>>>0,_1qx=(_1qw^_1qw>>>1)>>>0&4294967295,_1qy=_1qx>>>0;return ((_1q9>>>0&_1qy)>>>0==0)?new T4(0,(_1q9>>>0&((_1qy-1>>>0^4294967295)>>>0^_1qy)>>>0)>>>0&4294967295,_1qx,E(_1q8),E(_1qd)):new T4(0,(_1q9>>>0&((_1qy-1>>>0^4294967295)>>>0^_1qy)>>>0)>>>0&4294967295,_1qx,E(_1qd),E(_1q8));}}}else{var _1qz=_1qa>>>0;if(((_1qe>>>0&((_1qz-1>>>0^4294967295)>>>0^_1qz)>>>0)>>>0&4294967295)==_1q9){return ((_1qe>>>0&_1qz)>>>0==0)?new T4(0,_1q9,_1qa,E(B(_1pn(_1qb,_1qe,_1qf,_1qg,_1qh))),E(_1qc)):new T4(0,_1q9,_1qa,E(_1qb),E(B(_1pn(_1qc,_1qe,_1qf,_1qg,_1qh))));}else{var _1qA=(_1q9>>>0^_1qe>>>0)>>>0,_1qB=(_1qA|_1qA>>>1)>>>0,_1qC=(_1qB|_1qB>>>2)>>>0,_1qD=(_1qC|_1qC>>>4)>>>0,_1qE=(_1qD|_1qD>>>8)>>>0,_1qF=(_1qE|_1qE>>>16)>>>0,_1qG=(_1qF^_1qF>>>1)>>>0&4294967295,_1qH=_1qG>>>0;return ((_1q9>>>0&_1qH)>>>0==0)?new T4(0,(_1q9>>>0&((_1qH-1>>>0^4294967295)>>>0^_1qH)>>>0)>>>0&4294967295,_1qG,E(_1q8),E(_1qd)):new T4(0,(_1q9>>>0&((_1qH-1>>>0^4294967295)>>>0^_1qH)>>>0)>>>0&4294967295,_1qG,E(_1qd),E(_1q8));}}break;case 1:return new F(function(){return _1oD(_1qd.a,_1qd.b,_1q9,_1qa,_1qb,_1qc);});break;default:return E(_1q8);}break;case 1:return new F(function(){return _1mQ(_1q8.a,_1q8.b,_1q7);});break;default:return E(_1q7);}},_1qI=function(_1qJ,_1qK){var _1qL=E(_1qJ),_1qM=B(_150(_11k,_1pc,_1qL.a,_1qL.b,_1qK));return new T2(0,_1qM.a,_1qM.b);},_1qN=new T(function(){return B(unCStr("Int"));}),_1qO=function(_1qP,_1qQ,_1qR){return new F(function(){return _dz(_cM,new T2(0,_1qQ,_1qR),_1qP,_1qN);});},_1qS=function(_1qT,_1qU,_1qV){return new F(function(){return _dz(_cM,new T2(0,_1qT,_1qU),_1qV,_1qN);});},_1qW=new T(function(){return B(_1oi(_Tf,_4));}),_1qX=function(_1qY,_1qZ){var _1r0=function(_1r1,_1r2,_1r3){return new F(function(){return A2(_1qY,_1r2,_1r3);});},_1r4=function(_1r5,_1r6){while(1){var _1r7=E(_1r6);if(!_1r7._){return E(_1r5);}else{var _1r8=B(_1iA(_1r0,_1r5,_1r7.a));_1r5=_1r8;_1r6=_1r7.b;continue;}}};return new F(function(){return _1r4(_Tf,_1qZ);});},_1r9=function(_1ra,_1rb,_1rc,_1rd,_1re,_1rf,_1rg,_1rh,_1ri){var _1rj=new T(function(){return B(_1nH(_Tf,_17g,_1rg));}),_1rk=new T(function(){var _1rl=function(_1rm,_1rn){while(1){var _1ro=B((function(_1rp,_1rq){var _1rr=E(_1rq);if(!_1rr._){var _1rs=_1rr.d,_1rt=new T(function(){var _1ru=E(_1rr.b);if(!_1ru._){var _1rv=_1ru.a;if(!E(_1ru.b)._){var _1rw=new T(function(){var _1rx=E(_1rc),_1ry=_1rx.c,_1rz=E(_1rx.a),_1rA=E(_1rx.b);if(_1rz>_1rv){return B(_1qO(_1rv,_1rz,_1rA));}else{if(_1rv>_1rA){return B(_1qO(_1rv,_1rz,_1rA));}else{var _1rB=_1rv-_1rz|0;if(0>_1rB){return B(_1os(_1rB,_1ry));}else{if(_1rB>=_1ry){return B(_1os(_1rB,_1ry));}else{var _1rC=E(_1rx.d[_1rB]),_1rD=_1rC.d,_1rE=E(_1rC.b),_1rF=E(_1rC.c);if(_1rE<=_1rF){var _1rG=new T(function(){var _1rH=B(_131(_11k,_1lW,new T2(1,new T2(0,_1oz,new T2(1,_1rv&(-32),1<<(_1rv&31)>>>0)),_4)));return new T2(0,_1rH.a,_1rH.b);}),_1rI=new T(function(){var _1rJ=B(_131(_11k,_1lW,new T2(1,new T2(0,_4,new T2(1,_1rv&(-32),1<<(_1rv&31)>>>0)),_4)));return new T2(0,_1rJ.a,_1rJ.b);}),_1rK=new T2(1,_1rv&(-32),1<<(_1rv&31)>>>0),_1rL=new T(function(){var _1rM=B(_131(_11k,_1lW,new T2(1,new T2(0,_4,_1rK),_4)));return new T2(0,_1rM.a,_1rM.b);}),_1rN=new T(function(){var _1rO=B(_131(_11k,_1lW,new T2(1,new T2(0,_1oB,new T2(1,_1rv&(-32),1<<(_1rv&31)>>>0)),_4)));return new T2(0,_1rO.a,_1rO.b);}),_1rP=function(_1rQ){var _1rR=E(_1rQ);if(!_1rR._){return E(_1rL);}else{var _1rS=_1rR.b,_1rT=E(_1rR.a);switch(_1rT._){case 3:var _1rU=B(_131(_11k,_1lW,new T2(1,new T2(0,new T2(1,_1rT.a,_4),_1rK),_4)));return new T2(0,_1rU.a,_1rU.b);case 4:var _1rV=new T(function(){var _1rW=function(_1rX){var _1rY=E(_1rX);return (_1rY._==0)?__Z:new T2(1,new T(function(){return B(_1rP(B(_0(E(_1rY.a).a,_1rS))));}),new T(function(){return B(_1rW(_1rY.b));}));};return B(_1rW(_1rT.b));}),_1rZ=B(_176(_11k,_1pc,new T2(1,new T(function(){return B(_1rP(B(_0(_1rT.a,_1rS))));}),_1rV)));return new T2(0,_1rZ.a,_1rZ.b);case 5:return E(_1rN);case 6:return E(_1lZ);case 7:return E(_1rI);case 8:return E(_1rI);case 9:return E(_1rG);case 10:return E(_1rG);default:return E(_1oC);}}},_1s0=new T(function(){return B(_1rP(_4));}),_1s1=function(_1s2){var _1s3=new T(function(){var _1s4=E(_1rf),_1s5=_1s4.c,_1s6=E(_1s4.a),_1s7=E(_1s4.b);if(_1rE>_1s2){return B(_1qS(_1rE,_1rF,_1s2));}else{if(_1s2>_1rF){return B(_1qS(_1rE,_1rF,_1s2));}else{var _1s8=_1s2-_1rE|0;if(0>_1s8){return B(_1os(_1s8,_1rD));}else{if(_1s8>=_1rD){return B(_1os(_1s8,_1rD));}else{var _1s9=_1rC.e["v"]["i32"][_1s8];if(_1s6>_1s9){return B(_1qO(_1s9,_1s6,_1s7));}else{if(_1s9>_1s7){return B(_1qO(_1s9,_1s6,_1s7));}else{var _1sa=_1s9-_1s6|0;if(0>_1sa){return B(_1os(_1sa,_1s5));}else{if(_1sa>=_1s5){return B(_1os(_1sa,_1s5));}else{var _1sb=E(_1s4.d[_1sa]),_1sc=_1sb.c-1|0;if(0<=_1sc){var _1sd=function(_1se){return new T2(1,new T(function(){return E(_1sb.d[_1se]);}),new T(function(){if(_1se!=_1sc){return B(_1sd(_1se+1|0));}else{return __Z;}}));};return B(_1rP(B(_1sd(0))));}else{return E(_1s0);}}}}}}}}}});return new T2(1,new T2(0,_1s2,_1s3),new T(function(){if(_1s2!=_1rF){return B(_1s1(_1s2+1|0));}else{return __Z;}}));};return B(_1oi(_Tf,B(_1s1(_1rE))));}else{return E(_1qW);}}}}}});return new T2(1,_1rw,new T(function(){return B(_1rl(_1rp,_1rs));}));}else{return B(_1rl(_1rp,_1rs));}}else{return B(_1rl(_1rp,_1rs));}},1);_1rm=_1rt;_1rn=_1rr.c;return __continue;}else{return E(_1rp);}})(_1rm,_1rn));if(_1ro!=__continue){return _1ro;}}},_1sf=function(_1sg,_1sh,_1si){while(1){var _1sj=E(_1si);switch(_1sj._){case 0:var _1sk=B(_1sf(_1sg,_1sh,_1sj.d));_1sg=_1sk.a;_1sh=_1sk.b;_1si=_1sj.c;continue;case 1:var _1sl=_1sj.a,_1sm=B(_14I(_1oo,_1sj.b)),_1sn=E(_1sm.a);if(!_1sn._){var _1so=B(_13c(_1sl,B(_1qX(_1qI,B(_1rl(_4,_1sn)))),_1sg));}else{var _1so=E(_1sg);}var _1sp=E(_1sm.b);if(!_1sp._){var _1sq=B(_13c(_1sl,_1sp,_1sh));}else{var _1sq=E(_1sh);}return new T2(0,_1so,_1sq);default:return new T2(0,_1sg,_1sh);}}},_1sr=E(_1rj);if(!_1sr._){var _1ss=_1sr.c,_1st=_1sr.d;if(_1sr.b>=0){var _1su=B(_1sf(_Tf,_Tf,_1st)),_1sv=B(_1sf(_1su.a,_1su.b,_1ss));return new T2(0,_1sv.a,_1sv.b);}else{var _1sw=B(_1sf(_Tf,_Tf,_1ss)),_1sx=B(_1sf(_1sw.a,_1sw.b,_1st));return new T2(0,_1sx.a,_1sx.b);}}else{var _1sy=B(_1sf(_Tf,_Tf,_1sr));return new T2(0,_1sy.a,_1sy.b);}}),_1sz=new T(function(){var _1sA=function(_1sB){var _1sC=E(_1sB);switch(_1sC._){case 0:var _1sD=_1sC.a;return new T2(1,new T(function(){var _1sE=E(_1rc),_1sF=_1sE.c,_1sG=E(_1sE.a),_1sH=E(_1sE.b);if(_1sG>_1sD){return B(_1qO(_1sD,_1sG,_1sH));}else{if(_1sD>_1sH){return B(_1qO(_1sD,_1sG,_1sH));}else{var _1sI=_1sD-_1sG|0;if(0>_1sI){return B(_1os(_1sI,_1sF));}else{if(_1sI>=_1sF){return B(_1os(_1sI,_1sF));}else{return E(E(_1sE.d[_1sI]).a);}}}}}),_4);case 1:var _1sJ=B(_13D(_1sC.a,_1rj));if(!_1sJ._){return __Z;}else{return new F(function(){return _1sK(_4,_1sJ.a);});}break;default:return E(_1ox);}},_1sK=function(_1sL,_1sM){while(1){var _1sN=B((function(_1sO,_1sP){var _1sQ=E(_1sP);if(!_1sQ._){var _1sR=new T(function(){return B(_0(B(_1sA(_1sQ.b)),new T(function(){return B(_1sK(_1sO,_1sQ.d));},1)));},1);_1sL=_1sR;_1sM=_1sQ.c;return __continue;}else{return E(_1sO);}})(_1sL,_1sM));if(_1sN!=__continue){return _1sN;}}},_1sS=function(_1sT,_1sU){while(1){var _1sV=B((function(_1sW,_1sX){var _1sY=E(_1sX);switch(_1sY._){case 0:_1sT=new T(function(){return B(_1sS(_1sW,_1sY.d));},1);_1sU=_1sY.c;return __continue;case 1:var _1sZ=function(_1t0,_1t1){while(1){var _1t2=B((function(_1t3,_1t4){var _1t5=E(_1t4);if(!_1t5._){var _1t6=_1t5.b,_1t7=new T(function(){var _1t8=new T(function(){return B(_1sZ(_1t3,_1t5.d));}),_1t9=function(_1ta){var _1tb=E(_1ta);return (_1tb._==0)?E(_1t8):new T2(1,new T2(0,_1tb.a,new T2(1,_1sY.a,new T4(0,1,E(_1t6),E(_Lt),E(_Lt)))),new T(function(){return B(_1t9(_1tb.b));}));};return B(_1t9(B(_1sA(_1t6))));},1);_1t0=_1t7;_1t1=_1t5.c;return __continue;}else{return E(_1t3);}})(_1t0,_1t1));if(_1t2!=__continue){return _1t2;}}};return new F(function(){return _1sZ(_1sW,_1sY.b);});break;default:return E(_1sW);}})(_1sT,_1sU));if(_1sV!=__continue){return _1sV;}}},_1tc=E(_1rj);if(!_1tc._){var _1td=_1tc.c,_1te=_1tc.d;if(_1tc.b>=0){return B(_11V(_1lS,B(_1sS(new T(function(){return B(_1sS(_4,_1te));},1),_1td))));}else{return B(_11V(_1lS,B(_1sS(new T(function(){return B(_1sS(_4,_1td));},1),_1te))));}}else{return B(_11V(_1lS,B(_1sS(_4,_1tc))));}});return {_:0,a:_1ra,b:_1rb,c:_1rc,d:_1rd,e:_1re,f:_1rf,g:_1rg,h:new T(function(){return E(E(_1rk).b);}),i:_1sz,j:_1rh,k:new T(function(){return E(E(_1rk).a);}),l:_1ri};},_1tf=function(_1tg){var _1th=E(_1tg);return new F(function(){return _1r9(_1th.a,_1th.b,_1th.c,_1th.d,_1th.e,_1th.f,_1th.g,_1th.j,_1th.l);});},_1ti=0,_1tj=function(_1tk){var _1tl=E(_1tk);return new T3(0,_1tl.a,_1tl.b,_1ti);},_1tm=function(_1tn){var _1to=E(_1tn);return new T4(0,_1to.a,_1to.b,new T(function(){var _1tp=E(_1to.c);if(!_1tp._){return __Z;}else{return new T1(1,new T2(0,_1tp.a,_4));}}),_1to.d);},_1tq=0,_1tr=new T(function(){return B(unCStr("Negative range size"));}),_1ts=function(_1tt){var _1tu=function(_){var _1tv=B(_tC(_1tt,0))-1|0,_1tw=function(_1tx){if(_1tx>=0){var _1ty=newArr(_1tx,_Uc),_1tz=_1ty,_1tA=function(_1tB){var _1tC=function(_1tD,_1tE,_){while(1){if(_1tD!=_1tB){var _1tF=E(_1tE);if(!_1tF._){return _5;}else{var _=_1tz[_1tD]=_1tF.a,_1tG=_1tD+1|0;_1tD=_1tG;_1tE=_1tF.b;continue;}}else{return _5;}}},_1tH=B(_1tC(0,_1tt,_));return new T4(0,E(_1tq),E(_1tv),_1tx,_1tz);};if(0>_1tv){return new F(function(){return _1tA(0);});}else{var _1tI=_1tv+1|0;if(_1tI>=0){return new F(function(){return _1tA(_1tI);});}else{return new F(function(){return err(_1tr);});}}}else{return E(_Ue);}};if(0>_1tv){var _1tJ=B(_1tw(0)),_1tK=E(_1tJ),_1tL=_1tK.d;return new T4(0,E(_1tK.a),E(_1tK.b),_1tK.c,_1tL);}else{var _1tM=B(_1tw(_1tv+1|0)),_1tN=E(_1tM),_1tO=_1tN.d;return new T4(0,E(_1tN.a),E(_1tN.b),_1tN.c,_1tO);}};return new F(function(){return _8O(_1tu);});},_1tP=function(_1tQ){return new T1(3,_1tQ);},_1tR=function(_1tS,_1tT){var _1tU=new T(function(){var _1tV=E(_1tS),_1tW=B(_e0(_1tV.a,_1tV.b,_1tV.c,E(_1tT))),_1tX=B(_eX(E(_1tW.a)&4294967295,_eL,_1tV,_1tW.b));return new T2(0,_1tX.a,_1tX.b);});return new T2(0,new T1(3,new T(function(){return E(E(_1tU).a);})),new T(function(){return E(E(_1tU).b);}));},_1tY=function(_1tZ,_1u0){var _1u1=B(_1tR(_1tZ,_1u0));return new T2(0,_1u1.a,_1u1.b);},_1u2=function(_1u3,_1u4){var _1u5=E(_1u3),_1u6=B(_e0(_1u5.a,_1u5.b,_1u5.c,E(_1u4))),_1u7=B(_eX(E(_1u6.a)&4294967295,_eL,_1u5,_1u6.b));return new T2(0,_1u7.a,_1u7.b);},_1u8=function(_1u9,_1ua,_1ub,_1uc){var _1ud=B(_Yp(_1tY,new T3(0,_1u9,_1ua,_1ub),_1uc)),_1ue=B(_e0(_1u9,_1ua,_1ub,E(_1ud.b))),_1uf=B(_eX(E(_1ue.a)&4294967295,_1u2,new T3(0,_1u9,_1ua,_1ub),_1ue.b));return new T2(0,new T2(0,_1ud.a,_1uf.a),_1uf.b);},_1ug=function(_1uh,_1ui){var _1uj=E(_1uh),_1uk=B(_1u8(_1uj.a,_1uj.b,_1uj.c,_1ui));return new T2(0,_1uk.a,_1uk.b);},_1ul=function(_1um){var _1un=new T(function(){return B(unAppCStr("getSymbol ",new T(function(){return B(_cp(0,_1um&4294967295,_4));})));});return new F(function(){return _YP(_1un);});},_1uo=function(_1up,_1uq,_1ur,_1us){var _1ut=B(_dU(_1up,_1uq,_1ur,_1us)),_1uu=_1ut.b,_1uv=E(_1ut.a);switch(_1uv){case 0:var _1uw=new T(function(){var _1ux=B(_e0(_1up,_1uq,_1ur,E(_1uu))),_1uy=B(_e0(_1up,_1uq,_1ur,E(_1ux.b)));return new T2(0,new T(function(){return new T2(0,E(_1ux.a)&4294967295,E(_1uy.a)&4294967295);}),_1uy.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1uw).a);}),_4),new T(function(){return E(E(_1uw).b);}));case 1:var _1uz=new T(function(){var _1uA=B(_e0(_1up,_1uq,_1ur,E(_1uu))),_1uB=B(_e0(_1up,_1uq,_1ur,E(_1uA.b)));return new T2(0,new T(function(){return new T2(1,E(_1uA.a)&4294967295,E(_1uB.a)&4294967295);}),_1uB.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1uz).a);}),_4),new T(function(){return E(E(_1uz).b);}));case 2:var _1uC=new T(function(){var _1uD=B(_e0(_1up,_1uq,_1ur,E(_1uu))),_1uE=B(_e0(_1up,_1uq,_1ur,E(_1uD.b)));return new T2(0,new T(function(){return new T2(2,E(_1uD.a)&4294967295,E(_1uE.a)&4294967295);}),_1uE.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1uC).a);}),_4),new T(function(){return E(E(_1uC).b);}));case 3:var _1uF=B(_e0(_1up,_1uq,_1ur,E(_1uu))),_1uG=B(_eX(E(_1uF.a)&4294967295,_1u2,new T3(0,_1up,_1uq,_1ur),_1uF.b));return new T2(0,new T(function(){return B(_G(_1tP,_1uG.a));}),_1uG.b);case 4:var _1uH=new T(function(){var _1uI=new T3(0,_1up,_1uq,_1ur),_1uJ=B(_Yp(_1tY,_1uI,_1uu)),_1uK=B(_Yp(_1ug,_1uI,_1uJ.b));return new T2(0,new T2(4,_1uJ.a,_1uK.a),_1uK.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1uH).a);}),_4),new T(function(){return E(E(_1uH).b);}));default:return new F(function(){return _1ul(_1uv);});}},_1uL=function(_1uM,_1uN){var _1uO=E(_1uM),_1uP=B(_1uo(_1uO.a,_1uO.b,_1uO.c,E(_1uN)));return new T2(0,_1uP.a,_1uP.b);},_1uQ=function(_1uR){var _1uS=E(_1uR);if(!_1uS._){return __Z;}else{return new F(function(){return _0(_1uS.a,new T(function(){return B(_1uQ(_1uS.b));},1));});}},_1uT=function(_1uU,_1uV){var _1uW=new T(function(){var _1uX=B(_Yp(_1uL,_1uU,_1uV));return new T2(0,_1uX.a,_1uX.b);});return new T2(0,new T(function(){return B(_1ts(B(_1uQ(E(_1uW).a))));}),new T(function(){return E(E(_1uW).b);}));},_1uY=function(_1uZ,_1v0,_1v1,_1v2){var _1v3=B(_e0(_1uZ,_1v0,_1v1,_1v2));return new F(function(){return _eX(E(_1v3.a)&4294967295,_eL,new T3(0,_1uZ,_1v0,_1v1),_1v3.b);});},_1v4=function(_1v5,_1v6){var _1v7=E(_1v5),_1v8=B(_1uY(_1v7.a,_1v7.b,_1v7.c,E(_1v6)));return new T2(0,_1v8.a,_1v8.b);},_1v9=function(_1va){var _1vb=E(_1va);return (_1vb._==0)?__Z:new T2(1,new T2(0,_KR,_1vb.a),new T(function(){return B(_1v9(_1vb.b));}));},_1vc=function(_1vd,_1ve,_1vf,_1vg){var _1vh=B(_e0(_1vd,_1ve,_1vf,_1vg)),_1vi=B(_eX(E(_1vh.a)&4294967295,_j7,new T3(0,_1vd,_1ve,_1vf),_1vh.b)),_1vj=B(_e0(_1vd,_1ve,_1vf,E(_1vi.b))),_1vk=new T(function(){return new T2(0,new T(function(){return B(_1v9(_1vi.a));}),E(_1vj.a)&4294967295);});return new T2(0,_1vk,_1vj.b);},_1vl=function(_1vm,_1vn){var _1vo=E(_1vm),_1vp=B(_1vc(_1vo.a,_1vo.b,_1vo.c,E(_1vn)));return new T2(0,_1vp.a,_1vp.b);},_1vq=new T(function(){return B(unCStr("getProduction"));}),_1vr=new T(function(){return B(_YP(_1vq));}),_1vs=function(_1vt,_1vu,_1vv,_1vw){var _1vx=B(_dU(_1vt,_1vu,_1vv,_1vw)),_1vy=_1vx.b;switch(E(_1vx.a)){case 0:var _1vz=B(_e0(_1vt,_1vu,_1vv,E(_1vy))),_1vA=B(_Yp(_1vl,new T3(0,_1vt,_1vu,_1vv),_1vz.b));return new T2(0,new T(function(){return new T2(0,E(_1vz.a)&4294967295,_1vA.a);}),_1vA.b);case 1:var _1vB=B(_e0(_1vt,_1vu,_1vv,E(_1vy)));return new T2(0,new T(function(){return new T1(1,E(_1vB.a)&4294967295);}),_1vB.b);default:return E(_1vr);}},_1vC=function(_1vD,_1vE){var _1vF=E(_1vD),_1vG=B(_1vs(_1vF.a,_1vF.b,_1vF.c,E(_1vE)));return new T2(0,_1vG.a,_1vG.b);},_1vH=function(_1vI,_1vJ){var _1vK=new T(function(){var _1vL=E(_1vI),_1vM=B(_e0(_1vL.a,_1vL.b,_1vL.c,E(_1vJ)));return new T2(0,new T(function(){return E(_1vM.a)&4294967295;}),_1vM.b);}),_1vN=new T(function(){var _1vO=B(_Yp(_1vC,_1vI,new T(function(){return E(E(_1vK).b);},1)));return new T2(0,_1vO.a,_1vO.b);});return new T2(0,new T2(0,new T(function(){return E(E(_1vK).a);}),new T(function(){var _1vP=E(E(_1vN).a);if(!_1vP._){return new T0(1);}else{return B(_O2(1,new T4(0,1,E(_1vP.a),E(_Lt),E(_Lt)),_1vP.b));}})),new T(function(){return E(E(_1vN).b);}));},_1vQ=function(_1vR,_1vS){var _1vT=B(_1vH(_1vR,_1vS));return new T2(0,_1vT.a,_1vT.b);},_1vU=new T(function(){return B(err(_1tr));}),_1vV=function(_1vW,_1vX,_1vY,_1vZ){var _1w0=new T(function(){var _1w1=E(_1vY),_1w2=B(_e0(_1w1.a,_1w1.b,_1w1.c,E(_1vZ))),_1w3=E(_1w2.a)&4294967295,_1w4=B(_Yh(_1w3,_1vX,_1w1,_1w2.b));return new T2(0,new T2(0,_1w3,_1w4.a),_1w4.b);}),_1w5=new T(function(){var _1w6=E(E(_1w0).a),_1w7=_1w6.b,_1w8=new T(function(){return E(_1w6.a)-1|0;});return B(A(_iv,[_1vW,_id,new T2(0,_1tq,_1w8),new T(function(){var _1w9=E(_1w8);if(0>_1w9){return B(_ix(B(_hh(0,-1)),_1w7));}else{var _1wa=_1w9+1|0;if(_1wa>=0){return B(_ix(B(_hh(0,_1wa-1|0)),_1w7));}else{return E(_1vU);}}})]));});return new T2(0,_1w5,new T(function(){return E(E(_1w0).b);}));},_1wb=function(_1wc,_1wd,_1we,_1wf){var _1wg=B(_e0(_1wc,_1wd,_1we,_1wf));return new F(function(){return _eX(E(_1wg.a)&4294967295,_eL,new T3(0,_1wc,_1wd,_1we),_1wg.b);});},_1wh=function(_1wi,_1wj){var _1wk=E(_1wi),_1wl=B(_1wb(_1wk.a,_1wk.b,_1wk.c,E(_1wj)));return new T2(0,_1wl.a,_1wl.b);},_1wm=function(_1wn,_1wo,_1wp,_1wq){var _1wr=B(_e0(_1wn,_1wo,_1wp,_1wq)),_1ws=B(_e0(_1wn,_1wo,_1wp,E(_1wr.b))),_1wt=B(_1vV(_gV,_1wh,new T3(0,_1wn,_1wo,_1wp),_1ws.b));return new T2(0,new T(function(){var _1wu=E(_1wt.a);return new T6(0,E(_1wr.a)&4294967295,E(_1ws.a)&4294967295,E(_1wu.a),E(_1wu.b),_1wu.c,_1wu.d);}),_1wt.b);},_1wv=function(_1ww,_1wx){var _1wy=E(_1ww),_1wz=B(_1wm(_1wy.a,_1wy.b,_1wy.c,E(_1wx)));return new T2(0,_1wz.a,_1wz.b);},_1wA=0,_1wB=new T(function(){return B(unCStr("Negative range size"));}),_1wC=function(_1wD){var _1wE=B(_tC(_1wD,0)),_1wF=new T(function(){var _1wG=function(_){var _1wH=_1wE-1|0,_1wI=function(_,_1wJ){var _1wK=function(_1wL){var _1wM=_1wL-1|0;if(0<=_1wM){var _1wN=function(_1wO,_){while(1){var _=E(_1wJ).d["v"]["w8"][_1wO]=0;if(_1wO!=_1wM){var _1wP=_1wO+1|0;_1wO=_1wP;continue;}else{return _5;}}},_1wQ=B(_1wN(0,_));return _1wJ;}else{return _1wJ;}};if(0>_1wH){return new F(function(){return _1wK(0);});}else{var _1wR=_1wH+1|0;if(_1wR>=0){return new F(function(){return _1wK(_1wR);});}else{return new F(function(){return err(_1wB);});}}},_1wS=function(_,_1wT,_1wU,_1wV,_1wW){var _1wX=function(_1wY){var _1wZ=function(_1x0,_1x1,_){while(1){if(_1x0!=_1wY){var _1x2=E(_1x1);if(!_1x2._){return _5;}else{var _=_1wW["v"]["w8"][_1x0]=E(_1x2.a),_1x3=_1x0+1|0;_1x0=_1x3;_1x1=_1x2.b;continue;}}else{return _5;}}},_1x4=B(_1wZ(0,_1wD,_));return new T4(0,E(_1wT),E(_1wU),_1wV,_1wW);};if(0>_1wH){return new F(function(){return _1wX(0);});}else{var _1x5=_1wH+1|0;if(_1x5>=0){return new F(function(){return _1wX(_1x5);});}else{return new F(function(){return err(_1wB);});}}};if(0>_1wH){var _1x6=newByteArr(0),_1x7=B(_1wI(_,new T4(0,E(_1wA),E(_1wH),0,_1x6))),_1x8=E(_1x7);return new F(function(){return _1wS(_,_1x8.a,_1x8.b,_1x8.c,_1x8.d);});}else{var _1x9=_1wH+1|0,_1xa=newByteArr(_1x9),_1xb=B(_1wI(_,new T4(0,E(_1wA),E(_1wH),_1x9,_1xa))),_1xc=E(_1xb);return new F(function(){return _1wS(_,_1xc.a,_1xc.b,_1xc.c,_1xc.d);});}};return B(_8O(_1wG));});return new T3(0,0,_1wE,_1wF);},_1xd=function(_1xe){return new F(function(){return _cp(0,E(_1xe)&4294967295,_4);});},_1xf=function(_1xg,_1xh){return new F(function(){return _cp(0,E(_1xg)&4294967295,_1xh);});},_1xi=function(_1xj,_1xk){return new F(function(){return _3X(_1xf,_1xj,_1xk);});},_1xl=function(_1xm,_1xn,_1xo){return new F(function(){return _cp(E(_1xm),E(_1xn)&4294967295,_1xo);});},_1xp=new T3(0,_1xl,_1xd,_1xi),_1xq=new T(function(){return B(unCStr("Word8"));}),_1xr=0,_1xs=255,_1xt=new T2(0,_1xr,_1xs),_1xu=new T2(1,_cn,_4),_1xv=function(_1xw,_1xx,_1xy,_1xz){var _1xA=new T(function(){var _1xB=new T(function(){var _1xC=new T(function(){var _1xD=new T(function(){var _1xE=new T(function(){var _1xF=E(_1xy),_1xG=new T(function(){return B(A3(_cY,_cO,new T2(1,new T(function(){return B(A3(_da,_1xz,_d9,_1xF.a));}),new T2(1,new T(function(){return B(A3(_da,_1xz,_d9,_1xF.b));}),_4)),_1xu));});return new T2(1,_co,_1xG);});return B(unAppCStr(") is outside of bounds ",_1xE));},1);return B(_0(B(_cp(0,E(_1xx),_4)),_1xD));});return B(unAppCStr("}: tag (",_1xC));},1);return B(_0(_1xw,_1xB));});return new F(function(){return err(B(unAppCStr("Enum.toEnum{",_1xA)));});},_1xH=function(_1xI,_1xJ,_1xK,_1xL){return new F(function(){return _1xv(_1xJ,_1xK,_1xL,_1xI);});},_1xM=function(_1xN){return new F(function(){return _1xH(_1xp,_1xq,_1xN,_1xt);});},_1xO=function(_1xP){if(_1xP<0){return new F(function(){return _1xM(_1xP);});}else{if(_1xP>255){return new F(function(){return _1xM(_1xP);});}else{return _1xP>>>0;}}},_1xQ=function(_1xR){return new F(function(){return _1xO(E(_1xR));});},_1xS=function(_1xT){var _1xU=E(_1xT);if(!_1xU._){return __Z;}else{var _1xV=_1xU.b,_1xW=E(_1xU.a),_1xX=function(_1xY){return (_1xW>=2048)?new T2(1,new T(function(){var _1xZ=224+B(_lK(_1xW,4096))|0;if(_1xZ>>>0>1114111){return B(_es(_1xZ));}else{return _1xZ;}}),new T2(1,new T(function(){var _1y0=128+B(_lK(B(_mO(_1xW,4096)),64))|0;if(_1y0>>>0>1114111){return B(_es(_1y0));}else{return _1y0;}}),new T2(1,new T(function(){var _1y1=128+B(_mO(_1xW,64))|0;if(_1y1>>>0>1114111){return B(_es(_1y1));}else{return _1y1;}}),new T(function(){return B(_1xS(_1xV));})))):new T2(1,new T(function(){var _1y2=192+B(_lK(_1xW,64))|0;if(_1y2>>>0>1114111){return B(_es(_1y2));}else{return _1y2;}}),new T2(1,new T(function(){var _1y3=128+B(_mO(_1xW,64))|0;if(_1y3>>>0>1114111){return B(_es(_1y3));}else{return _1y3;}}),new T(function(){return B(_1xS(_1xV));})));};if(_1xW<=0){return new F(function(){return _1xX(_);});}else{if(_1xW>=128){return new F(function(){return _1xX(_);});}else{return new T2(1,_1xW,new T(function(){return B(_1xS(_1xV));}));}}}},_1y4=new T(function(){return B(unCStr("linref"));}),_1y5=new T(function(){return B(_1xS(_1y4));}),_1y6=new T(function(){return B(_G(_1xQ,_1y5));}),_1y7=new T(function(){var _1y8=B(_1wC(_1y6));return new T3(0,_1y8.a,_1y8.b,_1y8.c);}),_1y9=function(_1ya,_1yb){var _1yc=E(_1ya),_1yd=B(_eb(_1yc.a,_1yc.b,_1yc.c,E(_1yb))),_1ye=B(_1vV(_kK,_j7,_1yc,_1yd.b));return new T2(0,new T(function(){var _1yf=E(_1ye.a);return new T5(0,_1yd.a,E(_1yf.a),E(_1yf.b),_1yf.c,_1yf.d);}),_1ye.b);},_1yg=new T(function(){return B(_1oi(_Tf,_4));}),_1yh=new T2(0,0,0),_1yi=new T2(1,_1yh,_4),_1yj=new T(function(){return B(_1ts(_1yi));}),_1yk=new T2(1,_1yj,_4),_1yl=function(_1ym,_1yn,_1yo,_1yp){var _1yq=new T3(0,_1ym,_1yn,_1yo),_1yr=B(_Yy(_10Q,_10L,_1yq,_1yp)),_1ys=B(_Yy(_10Q,_1v4,_1yq,_1yr.b)),_1yt=B(_e0(_1ym,_1yn,_1yo,E(_1ys.b))),_1yu=E(_1yt.a)&4294967295,_1yv=B(_Yh(_1yu,_1uT,_1yq,_1yt.b)),_1yw=B(_e0(_1ym,_1yn,_1yo,E(_1yv.b))),_1yx=E(_1yw.a)&4294967295,_1yy=B(_Yh(_1yx,_1y9,_1yq,_1yw.b)),_1yz=B(_PB(_OC,_1ym,_1yn,_1yo,E(_1yy.b))),_1yA=new T(function(){var _1yB=B(_Yp(_1vQ,_1yq,_1yz.b));return new T2(0,_1yB.a,_1yB.b);}),_1yC=B(_Yy(_10Q,_1wv,_1yq,new T(function(){return E(E(_1yA).b);},1))),_1yD=B(_e0(_1ym,_1yn,_1yo,E(_1yC.b))),_1yE=new T(function(){var _1yF=E(_1yD.a)&4294967295,_1yG=new T(function(){var _1yH=function(_){var _1yI=(_1yu+1|0)-1|0,_1yJ=function(_1yK){if(_1yK>=0){var _1yL=newArr(_1yK,_Uc),_1yM=_1yL,_1yN=function(_1yO){var _1yP=function(_1yQ,_1yR,_){while(1){if(_1yQ!=_1yO){var _1yS=E(_1yR);if(!_1yS._){return _5;}else{var _=_1yM[_1yQ]=_1yS.a,_1yT=_1yQ+1|0;_1yQ=_1yT;_1yR=_1yS.b;continue;}}else{return _5;}}},_1yU=B(_1yP(0,new T(function(){return B(_0(_1yv.a,_1yk));},1),_));return new T4(0,E(_1tq),E(_1yI),_1yK,_1yM);};if(0>_1yI){return new F(function(){return _1yN(0);});}else{var _1yV=_1yI+1|0;if(_1yV>=0){return new F(function(){return _1yN(_1yV);});}else{return E(_1vU);}}}else{return E(_Ue);}};if(0>_1yI){var _1yW=B(_1yJ(0)),_1yX=E(_1yW),_1yY=_1yX.d;return new T4(0,E(_1yX.a),E(_1yX.b),_1yX.c,_1yY);}else{var _1yZ=B(_1yJ(_1yI+1|0)),_1z0=E(_1yZ),_1z1=_1z0.d;return new T4(0,E(_1z0.a),E(_1z0.b),_1z0.c,_1z1);}};return B(_8O(_1yH));}),_1z2=new T(function(){var _1z3=_1yF-1|0;if(0<=_1z3){var _1z4=function(_1z5){return new T2(1,new T2(0,_1z5,new T2(1,_1yx,_4)),new T(function(){if(_1z5!=_1z3){return B(_1z4(_1z5+1|0));}else{return __Z;}}));};return B(_1oi(_Tf,B(_1z4(0))));}else{return E(_1yg);}}),_1z6=new T(function(){var _1z7=function(_){var _1z8=(_1yx+1|0)-1|0,_1z9=function(_1za){if(_1za>=0){var _1zb=newArr(_1za,_Uc),_1zc=_1zb,_1zd=function(_1ze){var _1zf=function(_1zg,_1zh,_){while(1){if(_1zg!=_1ze){var _1zi=E(_1zh);if(!_1zi._){return _5;}else{var _=_1zc[_1zg]=_1zi.a,_1zj=_1zg+1|0;_1zg=_1zj;_1zh=_1zi.b;continue;}}else{return _5;}}},_1zk=new T(function(){var _1zl=new T(function(){var _1zm=function(_){var _1zn=newByteArr(4),_1zo=_1zn,_1zp=function(_1zq,_){while(1){var _=_1zo["v"]["i32"][_1zq]=0,_1zr=E(_1zq);if(!_1zr){return _5;}else{_1zq=_1zr+1|0;continue;}}},_1zs=B(_1zp(0,_)),_1zt=function(_1zu,_1zv,_){while(1){var _1zw=E(_1zu);if(_1zw==1){return _5;}else{var _1zx=E(_1zv);if(!_1zx._){return _5;}else{var _=_1zo["v"]["i32"][_1zw]=E(_1zx.a);_1zu=_1zw+1|0;_1zv=_1zx.b;continue;}}}},_1zy=B(_1zt(0,new T2(1,_1yu,_4),_));return new T4(0,E(_1tq),E(_1tq),1,_1zo);},_1zz=B(_8O(_1zm));return new T5(0,_1y7,E(_1zz.a),E(_1zz.b),_1zz.c,_1zz.d);});return B(_0(_1yy.a,new T2(1,_1zl,_4)));},1),_1zA=B(_1zf(0,_1zk,_));return new T4(0,E(_1tq),E(_1z8),_1za,_1zc);};if(0>_1z8){return new F(function(){return _1zd(0);});}else{var _1zB=_1z8+1|0;if(_1zB>=0){return new F(function(){return _1zd(_1zB);});}else{return E(_1vU);}}}else{return E(_Ue);}};if(0>_1z8){var _1zC=B(_1z9(0)),_1zD=E(_1zC),_1zE=_1zD.d;return new T4(0,E(_1zD.a),E(_1zD.b),_1zD.c,_1zE);}else{var _1zF=B(_1z9(_1z8+1|0)),_1zG=E(_1zF),_1zH=_1zG.d;return new T4(0,E(_1zG.a),E(_1zG.b),_1zG.c,_1zH);}};return B(_8O(_1z7));});return {_:0,a:_1yr.a,b:_1ys.a,c:_1z6,d:_1yz.a,e:_1z2,f:_1yG,g:new T(function(){var _1zI=E(E(_1yA).a);if(!_1zI._){return new T0(2);}else{var _1zJ=E(_1zI.a);return B(_OU(E(_1zJ.a),_1zJ.b,_1zI.b,_OD));}}),h:_Tf,i:_PY,j:_1yC.a,k:_Tf,l:_1yF};});return new T2(0,_1yE,_1yD.b);},_1zK=function(_1zL,_1zM){var _1zN=E(_1zL),_1zO=B(_1yl(_1zN.a,_1zN.b,_1zN.c,_1zM));return new T2(0,_1zO.a,_1zO.b);},_1zP=function(_1zQ,_1zR){var _1zS=E(_1zQ),_1zT=B(_HG(_Ib,_Kt,_1zS,_1zR)),_1zU=B(_eb(_1zS.a,_1zS.b,_1zS.c,E(_1zT.b)));return new T2(0,new T2(0,_1zT.a,_1zU.a),_1zU.b);},_1zV=function(_1zW,_1zX){var _1zY=new T(function(){var _1zZ=B(_Yp(_ZL,_1zW,_1zX));return new T2(0,_1zZ.a,_1zZ.b);}),_1A0=B(_Yp(_1zP,_1zW,new T(function(){return E(E(_1zY).b);},1)));return new T2(0,new T2(0,new T(function(){return E(E(_1zY).a);}),_1A0.a),_1A0.b);},_1A1=function(_1A2,_1A3){var _1A4=B(_1zV(_1A2,_1A3));return new T2(0,_1A4.a,_1A4.b);},_1A5=function(_1A6,_1A7,_1A8,_1A9,_1Aa){var _1Ab=B(_eb(_1A7,_1A8,_1A9,_1Aa)),_1Ac=new T3(0,_1A7,_1A8,_1A9),_1Ad=B(_Yy(_10Q,_10L,_1Ac,_1Ab.b)),_1Ae=B(_Yy(_10Q,_10G,_1Ac,_1Ad.b)),_1Af=B(_Yy(_10Q,_1A1,_1Ac,_1Ae.b)),_1Ag=B(_Yy(_10Q,_1zK,_1Ac,_1Af.b));return new T2(0,new T4(0,_1A6,_1Ab.a,new T3(0,_1Ad.a,new T(function(){return B(_XY(_1tm,_1Ae.a));}),new T(function(){return B(_XY(_1tj,_1Af.a));})),new T(function(){return B(_XY(_1tf,_1Ag.a));})),_1Ag.b);},_1Ah=function(_1Ai,_1Aj,_1Ak,_1Al){var _1Am=B(_Yy(_10Q,_10L,new T3(0,_1Ai,_1Aj,_1Ak),_1Al));return new F(function(){return _1A5(_1Am.a,_1Ai,_1Aj,_1Ak,E(_1Am.b));});},_1An=function(_1Ao,_1Ap){var _1Aq=E(_1Ap);return new F(function(){return _1r9(_1Aq.a,_1Aq.b,_1Aq.c,_1Aq.d,_1Aq.e,_1Aq.f,_1Aq.g,_1Aq.j,_1Aq.l);});},_1Ar=function(_1As,_1At,_1Au,_1Av){var _1Aw=new T3(0,_1As,_1At,_1Au),_1Ax=B(_V1(_1Aw,_1Av)),_1Ay=B(_V1(_1Aw,_1Ax.b)),_1Az=_1Ay.a,_1AA=_1Ay.b,_1AB=E(_1Ax.a),_1AC=function(_1AD){var _1AE=E(_1AB);if(_1AE==1){var _1AF=E(_1Az);if(!E(_1AF)){return new F(function(){return _1Ah(_1As,_1At,_1Au,_1AA);});}else{return new F(function(){return _UV(_1AF,1);});}}else{return new F(function(){return _UV(_1Az,_1AE);});}};if(E(_1AB)==2){if(E(_1Az)>1){return new F(function(){return _1AC(_);});}else{var _1AG=B(_T2(_ep,_KO,_1As,_1At,_1Au,E(_1AA))),_1AH=B(_eb(_1As,_1At,_1Au,E(_1AG.b))),_1AI=B(_Y2(_1As,_1At,_1Au,E(_1AH.b))),_1AJ=_1AI.a,_1AK=B(_T2(_ep,_UT,_1As,_1At,_1Au,E(_1AI.b))),_1AL=new T(function(){return B(_XY(function(_1AM){return new F(function(){return _1An(_1AJ,_1AM);});},_1AK.a));});return new T2(0,new T4(0,_1AG.a,_1AH.a,_1AJ,_1AL),_1AK.b);}}else{return new F(function(){return _1AC(_);});}},_1AN=function(_1AO){var _1AP=E(_1AO);if(_1AP==95){return true;}else{var _1AQ=function(_1AR){if(_1AP<65){if(_1AP<192){return false;}else{if(_1AP>255){return false;}else{switch(E(_1AP)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1AP>90){if(_1AP<192){return false;}else{if(_1AP>255){return false;}else{switch(E(_1AP)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1AP<97){return new F(function(){return _1AQ(_);});}else{if(_1AP>122){return new F(function(){return _1AQ(_);});}else{return true;}}}},_1AS=new T(function(){return B(unCStr("UTF8.decodeUTF8: bad data"));}),_1AT=function(_1AU){return new F(function(){return err(_1AS);});},_1AV=new T(function(){return B(_1AT(_));}),_1AW=function(_1AX){var _1AY=E(_1AX);if(!_1AY._){return __Z;}else{var _1AZ=_1AY.b,_1B0=E(_1AY.a);if(_1B0>=128){var _1B1=E(_1AZ);if(!_1B1._){return E(_1AV);}else{var _1B2=_1B1.a,_1B3=_1B1.b,_1B4=function(_1B5){var _1B6=E(_1B3);if(!_1B6._){return E(_1AV);}else{if(224>_1B0){return E(_1AV);}else{if(_1B0>239){return E(_1AV);}else{var _1B7=E(_1B2);if(128>_1B7){return E(_1AV);}else{if(_1B7>191){return E(_1AV);}else{var _1B8=E(_1B6.a);return (128>_1B8)?E(_1AV):(_1B8>191)?E(_1AV):new T2(1,new T(function(){var _1B9=((imul(B(_mO(_1B0,16)),4096)|0)+(imul(B(_mO(_1B7,64)),64)|0)|0)+B(_mO(_1B8,64))|0;if(_1B9>>>0>1114111){return B(_es(_1B9));}else{return _1B9;}}),new T(function(){return B(_1AW(_1B6.b));}));}}}}}};if(192>_1B0){return new F(function(){return _1B4(_);});}else{if(_1B0>223){return new F(function(){return _1B4(_);});}else{var _1Ba=E(_1B2);if(128>_1Ba){return new F(function(){return _1B4(_);});}else{if(_1Ba>191){return new F(function(){return _1B4(_);});}else{return new T2(1,new T(function(){var _1Bb=(imul(B(_mO(_1B0,32)),64)|0)+B(_mO(_1Ba,64))|0;if(_1Bb>>>0>1114111){return B(_es(_1Bb));}else{return _1Bb;}}),new T(function(){return B(_1AW(_1B3));}));}}}}}}else{return new T2(1,_1B0,new T(function(){return B(_1AW(_1AZ));}));}}},_1Bc=function(_1Bd){var _1Be=E(_1Bd);switch(_1Be){case 39:return true;case 95:return true;default:var _1Bf=function(_1Bg){var _1Bh=function(_1Bi){if(_1Be<65){if(_1Be<192){return false;}else{if(_1Be>255){return false;}else{switch(E(_1Be)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1Be>90){if(_1Be<192){return false;}else{if(_1Be>255){return false;}else{switch(E(_1Be)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1Be<97){return new F(function(){return _1Bh(_);});}else{if(_1Be>122){return new F(function(){return _1Bh(_);});}else{return true;}}};if(_1Be<48){return new F(function(){return _1Bf(_);});}else{if(_1Be>57){return new F(function(){return _1Bf(_);});}else{return true;}}}},_1Bj=function(_1Bk){while(1){var _1Bl=E(_1Bk);if(!_1Bl._){return true;}else{if(!B(_1Bc(E(_1Bl.a)))){return false;}else{_1Bk=_1Bl.b;continue;}}}},_1Bm=new T(function(){return B(unCStr("\\\\"));}),_1Bn=new T(function(){return B(unCStr("\\\'"));}),_1Bo=new T(function(){return B(unCStr("\'"));}),_1Bp=function(_1Bq){var _1Br=E(_1Bq);if(!_1Br._){return E(_1Bo);}else{var _1Bs=_1Br.b,_1Bt=E(_1Br.a);switch(E(_1Bt)){case 39:return new F(function(){return _0(_1Bn,new T(function(){return B(_1Bp(_1Bs));},1));});break;case 92:return new F(function(){return _0(_1Bm,new T(function(){return B(_1Bp(_1Bs));},1));});break;default:return new T2(1,_1Bt,new T(function(){return B(_1Bp(_1Bs));}));}}},_1Bu=function(_1Bv){var _1Bw=E(_1Bv);return (_1Bw._==0)?__Z:new T2(1,new T(function(){return B(_11l(_1Bw.a));}),new T(function(){return B(_1Bu(_1Bw.b));}));},_1Bx=function(_1By,_1Bz,_1BA){var _1BB=B(_1AW(B(_1Bu(new T(function(){return B(_Hr(_1By,_1Bz,_1BA));})))));if(!_1BB._){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1Bp(_4));}));});}else{if(!B(_1AN(E(_1BB.a)))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1Bp(_1BB));}));});}else{if(!B(_1Bj(_1BB.b))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1Bp(_1BB));}));});}else{return E(_1BB);}}}},_1BC=new T(function(){return eval("(function(a){var arr = new ByteArray(new a.constructor(a[\'buffer\']));return new T4(0,0,a[\'length\']-1,a[\'length\'],arr);})");}),_1BD=function(_1BE){return E(_1BE);},_1BF=function(_1BG){return E(E(_1BG).a);},_1BH=function(_1BI){return E(E(_1BI).a);},_1BJ=function(_1BK){return E(E(_1BK).a);},_1BL=function(_1BM){return E(E(_1BM).b);},_1BN=function(_1BO){return E(E(_1BO).a);},_1BP=function(_1BQ){var _1BR=new T(function(){return B(A2(_1BN,B(_1BF(B(_1BJ(B(_1BH(B(_1BL(_1BQ)))))))),_1BD));}),_1BS=function(_1BT){var _1BU=function(_){return new F(function(){return __app1(E(_1BC),E(_1BT));});};return new F(function(){return A1(_1BR,_1BU);});};return E(_1BS);},_1BV="(function(from, to, buf){return new Uint8Array(buf.buffer.slice(from, to+from));})",_1BW=function(_1BX,_1BY,_1BZ,_1C0){var _1C1=function(_){var _1C2=eval(E(_1BV)),_1C3=__app3(E(_1C2),E(_1BY),E(_1BZ),E(_1C0));return new F(function(){return A3(_1BP,_1BX,_1C3,0);});};return new F(function(){return _z(_1C1);});},_1C4=function(_){return _5;},_1C5=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1C6=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_1C7=new T(function(){return eval("document.body");}),_1C8=function(_1C9,_){return new T(function(){var _1Ca=Number(E(_1C9));return jsTrunc(_1Ca);});},_1Cb=new T(function(){return eval("(function(b){return b.size;})");}),_1Cc=function(_1Cd){return new F(function(){return _z(function(_){var _1Ce=__app1(E(_1Cb),E(_1Cd));return new F(function(){return _1C8(_1Ce,0);});});});},_1Cf=0,_1Cg=new T1(1,_4),_1Ch=new T(function(){return eval("(function(b,cb){var r=new FileReader();r.onload=function(){cb(new DataView(r.result));};r.readAsArrayBuffer(b);})");}),_1Ci=function(_1Cj,_1Ck){var _1Cl=new T(function(){return B(_1Cc(_1Ck));}),_1Cm=function(_1Cn){var _1Co=function(_){var _1Cp=nMV(_1Cg),_1Cq=_1Cp,_1Cr=function(_){var _1Cs=function(_1Ct,_){var _1Cu=B(_c(new T(function(){return B(A(_7r,[_2l,_1Cq,new T3(0,_1Cf,_1Cl,_1Ct),_2c]));}),_4,_));return _D;},_1Cv=__createJSFunc(2,E(_1Cs)),_1Cw=__app2(E(_1Ch),E(_1Ck),_1Cv);return new T(function(){return B(A3(_7H,_2l,_1Cq,_1Cn));});};return new T1(0,_1Cr);};return new T1(0,_1Co);};return new F(function(){return A2(_6g,_1Cj,_1Cm);});},_1Cx=function(_1Cy,_1Cz){while(1){var _1CA=B((function(_1CB,_1CC){var _1CD=E(_1CC);if(!_1CD._){var _1CE=E(_1CD.b);_1Cy=new T2(1,new T(function(){return B(_1Bx(_1CE.a,_1CE.b,_1CE.c));}),new T(function(){return B(_1Cx(_1CB,_1CD.e));}));_1Cz=_1CD.d;return __continue;}else{return E(_1CB);}})(_1Cy,_1Cz));if(_1CA!=__continue){return _1CA;}}},_1CF=new T(function(){return B(unCStr("AjaxError"));}),_1CG=new T(function(){return B(err(_1CF));}),_1CH=new T(function(){return B(unCStr("li"));}),_1CI=new T(function(){return B(unCStr("Languages"));}),_1CJ=new T(function(){return B(unCStr("h1"));}),_1CK=new T(function(){return B(unCStr("ul"));}),_1CL=new T(function(){return B(unAppCStr("[]",_4));}),_1CM=new T(function(){return B(unCStr("Got blobdata"));}),_1CN=new T(function(){return B(unCStr("Foods.pgf"));}),_1CO=new T(function(){return B(unAppCStr("Loaded pgf as Blob ",_1CN));}),_1CP=new T(function(){return eval("(function(s){return document.createTextNode(s);})");}),_1CQ=0,_1CR=function(_1CS){var _1CT=E(_1CS);return new F(function(){return _1Bx(_1CT.a,_1CT.b,_1CT.c);});},_1CU=new T(function(){return B(unCStr("!!: negative index"));}),_1CV=new T(function(){return B(_0(_cT,_1CU));}),_1CW=new T(function(){return B(err(_1CV));}),_1CX=new T(function(){return B(unCStr("!!: index too large"));}),_1CY=new T(function(){return B(_0(_cT,_1CX));}),_1CZ=new T(function(){return B(err(_1CY));}),_1D0=function(_1D1,_1D2){while(1){var _1D3=E(_1D1);if(!_1D3._){return E(_1CZ);}else{var _1D4=E(_1D2);if(!_1D4){return E(_1D3.a);}else{_1D1=_1D3.b;_1D2=_1D4-1|0;continue;}}}},_1D5=function(_1D6,_1D7){if(_1D7>=0){return new F(function(){return _1D0(_1D6,_1D7);});}else{return E(_1CW);}},_1D8=new T(function(){return B(unCStr("ACK"));}),_1D9=new T(function(){return B(unCStr("BEL"));}),_1Da=new T(function(){return B(unCStr("BS"));}),_1Db=new T(function(){return B(unCStr("SP"));}),_1Dc=new T2(1,_1Db,_4),_1Dd=new T(function(){return B(unCStr("US"));}),_1De=new T2(1,_1Dd,_1Dc),_1Df=new T(function(){return B(unCStr("RS"));}),_1Dg=new T2(1,_1Df,_1De),_1Dh=new T(function(){return B(unCStr("GS"));}),_1Di=new T2(1,_1Dh,_1Dg),_1Dj=new T(function(){return B(unCStr("FS"));}),_1Dk=new T2(1,_1Dj,_1Di),_1Dl=new T(function(){return B(unCStr("ESC"));}),_1Dm=new T2(1,_1Dl,_1Dk),_1Dn=new T(function(){return B(unCStr("SUB"));}),_1Do=new T2(1,_1Dn,_1Dm),_1Dp=new T(function(){return B(unCStr("EM"));}),_1Dq=new T2(1,_1Dp,_1Do),_1Dr=new T(function(){return B(unCStr("CAN"));}),_1Ds=new T2(1,_1Dr,_1Dq),_1Dt=new T(function(){return B(unCStr("ETB"));}),_1Du=new T2(1,_1Dt,_1Ds),_1Dv=new T(function(){return B(unCStr("SYN"));}),_1Dw=new T2(1,_1Dv,_1Du),_1Dx=new T(function(){return B(unCStr("NAK"));}),_1Dy=new T2(1,_1Dx,_1Dw),_1Dz=new T(function(){return B(unCStr("DC4"));}),_1DA=new T2(1,_1Dz,_1Dy),_1DB=new T(function(){return B(unCStr("DC3"));}),_1DC=new T2(1,_1DB,_1DA),_1DD=new T(function(){return B(unCStr("DC2"));}),_1DE=new T2(1,_1DD,_1DC),_1DF=new T(function(){return B(unCStr("DC1"));}),_1DG=new T2(1,_1DF,_1DE),_1DH=new T(function(){return B(unCStr("DLE"));}),_1DI=new T2(1,_1DH,_1DG),_1DJ=new T(function(){return B(unCStr("SI"));}),_1DK=new T2(1,_1DJ,_1DI),_1DL=new T(function(){return B(unCStr("SO"));}),_1DM=new T2(1,_1DL,_1DK),_1DN=new T(function(){return B(unCStr("CR"));}),_1DO=new T2(1,_1DN,_1DM),_1DP=new T(function(){return B(unCStr("FF"));}),_1DQ=new T2(1,_1DP,_1DO),_1DR=new T(function(){return B(unCStr("VT"));}),_1DS=new T2(1,_1DR,_1DQ),_1DT=new T(function(){return B(unCStr("LF"));}),_1DU=new T2(1,_1DT,_1DS),_1DV=new T(function(){return B(unCStr("HT"));}),_1DW=new T2(1,_1DV,_1DU),_1DX=new T2(1,_1Da,_1DW),_1DY=new T2(1,_1D9,_1DX),_1DZ=new T2(1,_1D8,_1DY),_1E0=new T(function(){return B(unCStr("ENQ"));}),_1E1=new T2(1,_1E0,_1DZ),_1E2=new T(function(){return B(unCStr("EOT"));}),_1E3=new T2(1,_1E2,_1E1),_1E4=new T(function(){return B(unCStr("ETX"));}),_1E5=new T2(1,_1E4,_1E3),_1E6=new T(function(){return B(unCStr("STX"));}),_1E7=new T2(1,_1E6,_1E5),_1E8=new T(function(){return B(unCStr("SOH"));}),_1E9=new T2(1,_1E8,_1E7),_1Ea=new T(function(){return B(unCStr("NUL"));}),_1Eb=new T2(1,_1Ea,_1E9),_1Ec=92,_1Ed=new T(function(){return B(unCStr("\\DEL"));}),_1Ee=new T(function(){return B(unCStr("\\a"));}),_1Ef=new T(function(){return B(unCStr("\\\\"));}),_1Eg=new T(function(){return B(unCStr("\\SO"));}),_1Eh=new T(function(){return B(unCStr("\\r"));}),_1Ei=new T(function(){return B(unCStr("\\f"));}),_1Ej=new T(function(){return B(unCStr("\\v"));}),_1Ek=new T(function(){return B(unCStr("\\n"));}),_1El=new T(function(){return B(unCStr("\\t"));}),_1Em=new T(function(){return B(unCStr("\\b"));}),_1En=function(_1Eo,_1Ep){if(_1Eo<=127){var _1Eq=E(_1Eo);switch(_1Eq){case 92:return new F(function(){return _0(_1Ef,_1Ep);});break;case 127:return new F(function(){return _0(_1Ed,_1Ep);});break;default:if(_1Eq<32){var _1Er=E(_1Eq);switch(_1Er){case 7:return new F(function(){return _0(_1Ee,_1Ep);});break;case 8:return new F(function(){return _0(_1Em,_1Ep);});break;case 9:return new F(function(){return _0(_1El,_1Ep);});break;case 10:return new F(function(){return _0(_1Ek,_1Ep);});break;case 11:return new F(function(){return _0(_1Ej,_1Ep);});break;case 12:return new F(function(){return _0(_1Ei,_1Ep);});break;case 13:return new F(function(){return _0(_1Eh,_1Ep);});break;case 14:return new F(function(){return _0(_1Eg,new T(function(){var _1Es=E(_1Ep);if(!_1Es._){return __Z;}else{if(E(_1Es.a)==72){return B(unAppCStr("\\&",_1Es));}else{return E(_1Es);}}},1));});break;default:return new F(function(){return _0(new T2(1,_1Ec,new T(function(){return B(_1D5(_1Eb,_1Er));})),_1Ep);});}}else{return new T2(1,_1Eq,_1Ep);}}}else{var _1Et=new T(function(){var _1Eu=jsShowI(_1Eo);return B(_0(fromJSStr(_1Eu),new T(function(){var _1Ev=E(_1Ep);if(!_1Ev._){return __Z;}else{var _1Ew=E(_1Ev.a);if(_1Ew<48){return E(_1Ev);}else{if(_1Ew>57){return E(_1Ev);}else{return B(unAppCStr("\\&",_1Ev));}}}},1)));});return new T2(1,_1Ec,_1Et);}},_1Ex=new T(function(){return B(unCStr("\\\""));}),_1Ey=function(_1Ez,_1EA){var _1EB=E(_1Ez);if(!_1EB._){return E(_1EA);}else{var _1EC=_1EB.b,_1ED=E(_1EB.a);if(_1ED==34){return new F(function(){return _0(_1Ex,new T(function(){return B(_1Ey(_1EC,_1EA));},1));});}else{return new F(function(){return _1En(_1ED,new T(function(){return B(_1Ey(_1EC,_1EA));}));});}}},_1EE=new T2(1,_3V,_4),_1EF=34,_1EG=function(_1EH){var _1EI=E(_1EH);if(!_1EI._){return E(_1EE);}else{var _1EJ=new T(function(){return B(_1Ey(_1EI.a,new T2(1,_1EF,new T(function(){return B(_1EG(_1EI.b));}))));});return new T2(1,_3U,new T2(1,_1EF,_1EJ));}},_1EK=new T(function(){return eval("(function(x){console.log(x);})");}),_1EL=function(_1EM){var _1EN=E(_1EM);if(!_1EN._){return E(_1CG);}else{var _1EO=function(_){var _1EP=E(_1EK),_1EQ=__app1(_1EP,toJSStr(E(_1CO)));return new T(function(){var _1ER=function(_1ES){var _1ET=function(_){var _1EU=__app1(_1EP,toJSStr(E(_1CM))),_1EV=new T(function(){var _1EW=E(_1ES),_1EX=B(_1BW(_bP,_1EW.a,_1EW.b,_1EW.c)),_1EY=E(_1EX.a);return E(B(_1Ar(_1EY,(E(_1EX.b)-_1EY|0)+1|0,_1EX,_1CQ)).a);}),_1EZ=function(_){var _1F0=__app1(_1EP,toJSStr(B(unAppCStr("Loaded ",new T(function(){return B(_1CR(E(_1EV).b));}))))),_1F1=function(_){var _1F2=E(_1EV).d,_1F3=function(_){var _1F4=E(_1C5),_1F5=__app1(_1F4,toJSStr(E(_1CK))),_1F6=_1F5,_1F7=function(_1F8,_1F9,_){while(1){var _1Fa=B((function(_1Fb,_1Fc,_){var _1Fd=E(_1Fc);if(!_1Fd._){var _1Fe=E(_1Fd.b),_1Ff=function(_){var _1Fg=new T(function(){return B(_1Bx(_1Fe.a,_1Fe.b,_1Fe.c));}),_1Fh=__app1(_1EP,toJSStr(B(unAppCStr("added ",_1Fg)))),_1Fi=__app1(_1F4,toJSStr(E(_1CH))),_1Fj=__app1(E(_1CP),toJSStr(E(_1Fg))),_1Fk=E(_1C6),_1Fl=__app2(_1Fk,_1Fj,_1Fi),_1Fm=__app2(_1Fk,_1Fi,_1F6);return new F(function(){return _1F7(_1Fb,_1Fd.e,_);});};_1F8=_1Ff;_1F9=_1Fd.d;return __continue;}else{return new F(function(){return A1(_1Fb,_);});}})(_1F8,_1F9,_));if(_1Fa!=__continue){return _1Fa;}}},_1Fn=B(_1F7(_1C4,_1F2,_)),_1Fo=__app1(_1F4,toJSStr(E(_1CJ))),_1Fp=__app1(E(_1CP),toJSStr(E(_1CI))),_1Fq=E(_1C6),_1Fr=__app2(_1Fq,_1Fp,_1Fo),_1Fs=E(_1C7),_1Ft=__app2(_1Fq,_1Fo,_1Fs),_1Fu=__app2(_1Fq,_1F6,_1Fs);return _5;},_1Fv=B(_1Cx(_4,_1F2));if(!_1Fv._){var _1Fw=__app1(_1EP,toJSStr(E(_1CL))),_1Fx=B(_1F3(_));return _7q;}else{var _1Fy=new T(function(){return B(_1Ey(_1Fv.a,new T2(1,_1EF,new T(function(){return B(_1EG(_1Fv.b));}))));}),_1Fz=__app1(_1EP,toJSStr(new T2(1,_3W,new T2(1,_1EF,_1Fy)))),_1FA=B(_1F3(_));return _7q;}};return new T1(0,_1F1);};return new T1(0,_1EZ);};return new T1(0,_1ET);};return B(A3(_1Ci,_2l,_1EN.a,_1ER));});};return new T1(0,_1EO);}},_1FB=new T(function(){return toJSStr(E(_1CN));}),_1FC=new T(function(){return B(A(_7Y,[_2l,_N,_1b,_i,_h,_1FB,_1EL]));}),_1FD=function(_){var _1FE=B(_c(_1FC,_4,_));return _5;},_1FF=function(_){return new F(function(){return _1FD(_);});};
var hasteMain = function() {B(A(_1FF, [0]));};window.onload = hasteMain;