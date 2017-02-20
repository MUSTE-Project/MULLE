"use strict";
var __haste_prog_id = '57977d1c329adf141920a13d1a89862ac1975dbe65aca3fbf3bb8fc76adc177d';
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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=new T1(0,_),_i=new T(function(){return toJSStr(_4);}),_j=function(_k){return E(_i);},_l=function(_m,_){var _n=E(_m);if(!_n._){return _4;}else{var _o=B(_l(_n.b,_));return new T2(1,_5,_o);}},_p=function(_q,_){var _r=__arr2lst(0,_q);return new F(function(){return _l(_r,_);});},_s=function(_t,_){return new F(function(){return _p(E(_t),_);});},_u=function(_){return _5;},_v=function(_w,_){return new F(function(){return _u(_);});},_x=new T2(0,_v,_s),_y=function(_){return new F(function(){return __jsNull();});},_z=function(_A){var _B=B(A1(_A,_));return E(_B);},_C=new T(function(){return B(_z(_y));}),_D=new T(function(){return E(_C);}),_E=function(_F){return E(_D);},_G=function(_H,_I){var _J=E(_I);return (_J._==0)?__Z:new T2(1,new T(function(){return B(A1(_H,_J.a));}),new T(function(){return B(_G(_H,_J.b));}));},_K=function(_L){return new F(function(){return __lst2arr(B(_G(_E,_L)));});},_M=new T2(0,_E,_K),_N=new T4(0,_M,_x,_j,_j),_O="application/octet-stream",_P=function(_Q){return E(_O);},_R="blob",_S=function(_T){return E(_R);},_U=function(_V,_){var _W=E(_V);if(!_W._){return _4;}else{var _X=B(_U(_W.b,_));return new T2(1,_W.a,_X);}},_Y=function(_Z,_){var _10=__arr2lst(0,_Z);return new F(function(){return _U(_10,_);});},_11=function(_12,_){return new F(function(){return _Y(E(_12),_);});},_13=function(_14,_){return _14;},_15=new T2(0,_13,_11),_16=function(_17){return E(_17);},_18=function(_19){return new F(function(){return __lst2arr(B(_G(_16,_19)));});},_1a=new T2(0,_16,_18),_1b=new T4(0,_1a,_15,_P,_S),_1c=function(_1d,_1e,_1f){var _1g=function(_1h){var _1i=new T(function(){return B(A1(_1f,_1h));});return new F(function(){return A1(_1e,function(_1j){return E(_1i);});});};return new F(function(){return A1(_1d,_1g);});},_1k=function(_1l,_1m,_1n){var _1o=new T(function(){return B(A1(_1m,function(_1p){return new F(function(){return A1(_1n,_1p);});}));});return new F(function(){return A1(_1l,function(_1q){return E(_1o);});});},_1r=function(_1s,_1t,_1u){var _1v=function(_1w){var _1x=function(_1y){return new F(function(){return A1(_1u,new T(function(){return B(A1(_1w,_1y));}));});};return new F(function(){return A1(_1t,_1x);});};return new F(function(){return A1(_1s,_1v);});},_1z=function(_1A,_1B){return new F(function(){return A1(_1B,_1A);});},_1C=function(_1D,_1E,_1F){var _1G=new T(function(){return B(A1(_1F,_1D));});return new F(function(){return A1(_1E,function(_1H){return E(_1G);});});},_1I=function(_1J,_1K,_1L){var _1M=function(_1N){return new F(function(){return A1(_1L,new T(function(){return B(A1(_1J,_1N));}));});};return new F(function(){return A1(_1K,_1M);});},_1O=new T2(0,_1I,_1C),_1P=new T5(0,_1O,_1z,_1r,_1k,_1c),_1Q=function(_1R,_1S,_1T){return new F(function(){return A1(_1R,function(_1U){return new F(function(){return A2(_1S,_1U,_1T);});});});},_1V=function(_1W){return E(E(_1W).b);},_1X=function(_1Y,_1Z){return new F(function(){return A3(_1V,_20,_1Y,function(_21){return E(_1Z);});});},_22=function(_23){return new F(function(){return err(_23);});},_20=new T(function(){return new T5(0,_1P,_1Q,_1X,_1z,_22);}),_24=function(_25,_26,_){var _27=B(A1(_26,_));return new T(function(){return B(A1(_25,_27));});},_28=function(_29,_2a){return new T1(0,function(_){return new F(function(){return _24(_2a,_29,_);});});},_2b=new T2(0,_20,_28),_2c=function(_2d){return new T0(2);},_2e=function(_2f){var _2g=new T(function(){return B(A1(_2f,_2c));}),_2h=function(_2i){return new T1(1,new T2(1,new T(function(){return B(A1(_2i,_5));}),new T2(1,_2g,_4)));};return E(_2h);},_2j=function(_2k){return E(_2k);},_2l=new T3(0,_2b,_2j,_2e),_2m=function(_2n){return E(E(_2n).a);},_2o=function(_2p,_2q,_2r,_2s,_2t){var _2u=B(A2(_2m,_2p,E(_2t)));return new F(function(){return A2(_2q,_2r,new T2(1,_2u,E(_2s)));});},_2v=function(_2w){return E(E(_2w).a);},_2x=function(_2y){return E(E(_2y).a);},_2z=function(_2A){return E(E(_2A).a);},_2B=function(_2C){return E(E(_2C).b);},_2D=new T(function(){return B(unCStr("base"));}),_2E=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_2F=new T(function(){return B(unCStr("IOException"));}),_2G=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_2D,_2E,_2F),_2H=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_2G,_4,_4),_2I=function(_2J){return E(_2H);},_2K=function(_2L){return E(E(_2L).a);},_2M=function(_2N,_2O,_2P){var _2Q=B(A1(_2N,_)),_2R=B(A1(_2O,_)),_2S=hs_eqWord64(_2Q.a,_2R.a);if(!_2S){return __Z;}else{var _2T=hs_eqWord64(_2Q.b,_2R.b);return (!_2T)?__Z:new T1(1,_2P);}},_2U=function(_2V){var _2W=E(_2V);return new F(function(){return _2M(B(_2K(_2W.a)),_2I,_2W.b);});},_2X=new T(function(){return B(unCStr(": "));}),_2Y=new T(function(){return B(unCStr(")"));}),_2Z=new T(function(){return B(unCStr(" ("));}),_30=new T(function(){return B(unCStr("interrupted"));}),_31=new T(function(){return B(unCStr("system error"));}),_32=new T(function(){return B(unCStr("unsatisified constraints"));}),_33=new T(function(){return B(unCStr("user error"));}),_34=new T(function(){return B(unCStr("permission denied"));}),_35=new T(function(){return B(unCStr("illegal operation"));}),_36=new T(function(){return B(unCStr("end of file"));}),_37=new T(function(){return B(unCStr("resource exhausted"));}),_38=new T(function(){return B(unCStr("resource busy"));}),_39=new T(function(){return B(unCStr("does not exist"));}),_3a=new T(function(){return B(unCStr("already exists"));}),_3b=new T(function(){return B(unCStr("resource vanished"));}),_3c=new T(function(){return B(unCStr("timeout"));}),_3d=new T(function(){return B(unCStr("unsupported operation"));}),_3e=new T(function(){return B(unCStr("hardware fault"));}),_3f=new T(function(){return B(unCStr("inappropriate type"));}),_3g=new T(function(){return B(unCStr("invalid argument"));}),_3h=new T(function(){return B(unCStr("failed"));}),_3i=new T(function(){return B(unCStr("protocol error"));}),_3j=function(_3k,_3l){switch(E(_3k)){case 0:return new F(function(){return _0(_3a,_3l);});break;case 1:return new F(function(){return _0(_39,_3l);});break;case 2:return new F(function(){return _0(_38,_3l);});break;case 3:return new F(function(){return _0(_37,_3l);});break;case 4:return new F(function(){return _0(_36,_3l);});break;case 5:return new F(function(){return _0(_35,_3l);});break;case 6:return new F(function(){return _0(_34,_3l);});break;case 7:return new F(function(){return _0(_33,_3l);});break;case 8:return new F(function(){return _0(_32,_3l);});break;case 9:return new F(function(){return _0(_31,_3l);});break;case 10:return new F(function(){return _0(_3i,_3l);});break;case 11:return new F(function(){return _0(_3h,_3l);});break;case 12:return new F(function(){return _0(_3g,_3l);});break;case 13:return new F(function(){return _0(_3f,_3l);});break;case 14:return new F(function(){return _0(_3e,_3l);});break;case 15:return new F(function(){return _0(_3d,_3l);});break;case 16:return new F(function(){return _0(_3c,_3l);});break;case 17:return new F(function(){return _0(_3b,_3l);});break;default:return new F(function(){return _0(_30,_3l);});}},_3m=new T(function(){return B(unCStr("}"));}),_3n=new T(function(){return B(unCStr("{handle: "));}),_3o=function(_3p,_3q,_3r,_3s,_3t,_3u){var _3v=new T(function(){var _3w=new T(function(){var _3x=new T(function(){var _3y=E(_3s);if(!_3y._){return E(_3u);}else{var _3z=new T(function(){return B(_0(_3y,new T(function(){return B(_0(_2Y,_3u));},1)));},1);return B(_0(_2Z,_3z));}},1);return B(_3j(_3q,_3x));}),_3A=E(_3r);if(!_3A._){return E(_3w);}else{return B(_0(_3A,new T(function(){return B(_0(_2X,_3w));},1)));}}),_3B=E(_3t);if(!_3B._){var _3C=E(_3p);if(!_3C._){return E(_3v);}else{var _3D=E(_3C.a);if(!_3D._){var _3E=new T(function(){var _3F=new T(function(){return B(_0(_3m,new T(function(){return B(_0(_2X,_3v));},1)));},1);return B(_0(_3D.a,_3F));},1);return new F(function(){return _0(_3n,_3E);});}else{var _3G=new T(function(){var _3H=new T(function(){return B(_0(_3m,new T(function(){return B(_0(_2X,_3v));},1)));},1);return B(_0(_3D.a,_3H));},1);return new F(function(){return _0(_3n,_3G);});}}}else{return new F(function(){return _0(_3B.a,new T(function(){return B(_0(_2X,_3v));},1));});}},_3I=function(_3J){var _3K=E(_3J);return new F(function(){return _3o(_3K.a,_3K.b,_3K.c,_3K.d,_3K.f,_4);});},_3L=function(_3M,_3N,_3O){var _3P=E(_3N);return new F(function(){return _3o(_3P.a,_3P.b,_3P.c,_3P.d,_3P.f,_3O);});},_3Q=function(_3R,_3S){var _3T=E(_3R);return new F(function(){return _3o(_3T.a,_3T.b,_3T.c,_3T.d,_3T.f,_3S);});},_3U=44,_3V=93,_3W=91,_3X=function(_3Y,_3Z,_40){var _41=E(_3Z);if(!_41._){return new F(function(){return unAppCStr("[]",_40);});}else{var _42=new T(function(){var _43=new T(function(){var _44=function(_45){var _46=E(_45);if(!_46._){return E(new T2(1,_3V,_40));}else{var _47=new T(function(){return B(A2(_3Y,_46.a,new T(function(){return B(_44(_46.b));})));});return new T2(1,_3U,_47);}};return B(_44(_41.b));});return B(A2(_3Y,_41.a,_43));});return new T2(1,_3W,_42);}},_48=function(_49,_4a){return new F(function(){return _3X(_3Q,_49,_4a);});},_4b=new T3(0,_3L,_3I,_48),_4c=new T(function(){return new T5(0,_2I,_4b,_4d,_2U,_3I);}),_4d=function(_4e){return new T2(0,_4c,_4e);},_4f="status-text",_4g="status",_4h="http",_4i="network",_4j="type",_4k=__Z,_4l=__Z,_4m=7,_4n=function(_4o,_){var _4p=__get(_4o,E(_4j)),_4q=String(_4p),_4r=strEq(_4q,E(_4i));if(!E(_4r)){var _4s=strEq(_4q,E(_4h));if(!E(_4s)){var _4t=new T(function(){var _4u=new T(function(){return B(unAppCStr("unknown type of ajax error: ",new T(function(){return fromJSStr(_4q);})));});return B(_4d(new T6(0,_4l,_4m,_4,_4u,_4l,_4l)));});return new F(function(){return die(_4t);});}else{var _4v=__get(_4o,E(_4g)),_4w=__get(_4o,E(_4f));return new T2(1,new T(function(){var _4x=Number(_4v);return jsTrunc(_4x);}),new T(function(){return String(_4w);}));}}else{return _4k;}},_4y=function(_4z,_){var _4A=E(_4z);if(!_4A._){return _4;}else{var _4B=B(_4n(E(_4A.a),_)),_4C=B(_4y(_4A.b,_));return new T2(1,_4B,_4C);}},_4D=function(_4E,_){var _4F=__arr2lst(0,_4E);return new F(function(){return _4y(_4F,_);});},_4G=function(_4H,_){return new F(function(){return _4D(E(_4H),_);});},_4I=function(_4J,_){return new F(function(){return _4n(E(_4J),_);});},_4K=new T2(0,_4I,_4G),_4L=function(_4M){return E(E(_4M).a);},_4N=function(_4O,_4P,_){var _4Q=__eq(_4P,E(_D));if(!E(_4Q)){var _4R=__isUndef(_4P);if(!E(_4R)){var _4S=B(A3(_4L,_4O,_4P,_));return new T1(1,_4S);}else{return _4l;}}else{return _4l;}},_4T=function(_4U,_){return new F(function(){return _4N(_4K,E(_4U),_);});},_4V=function(_4W,_4X,_){var _4Y=__arr2lst(0,_4X),_4Z=function(_50,_){var _51=E(_50);if(!_51._){return _4;}else{var _52=_51.b,_53=E(_51.a),_54=__eq(_53,E(_D));if(!E(_54)){var _55=__isUndef(_53);if(!E(_55)){var _56=B(A3(_4L,_4W,_53,_)),_57=B(_4Z(_52,_));return new T2(1,new T1(1,_56),_57);}else{var _58=B(_4Z(_52,_));return new T2(1,_4l,_58);}}else{var _59=B(_4Z(_52,_));return new T2(1,_4l,_59);}}};return new F(function(){return _4Z(_4Y,_);});},_5a=function(_5b,_){return new F(function(){return _4V(_4K,E(_5b),_);});},_5c=new T2(0,_4T,_5a),_5d=2,_5e=function(_5f){return E(_5d);},_5g=function(_5h,_5i,_){var _5j=B(A2(_5h,new T(function(){var _5k=E(_5i),_5l=__eq(_5k,E(_D));if(!E(_5l)){var _5m=__isUndef(_5k);if(!E(_5m)){return new T1(1,_5k);}else{return __Z;}}else{return __Z;}}),_));return _D;},_5n=new T2(0,_5g,_5e),_5o=function(_5p){return E(E(_5p).a);},_5q=function(_5r,_5s,_5t,_5u){var _5v=new T(function(){return B(A1(_5t,new T(function(){var _5w=B(A3(_4L,_5r,_5u,_));return E(_5w);})));});return new F(function(){return A2(_5o,_5s,_5v);});},_5x=function(_5y){return E(E(_5y).b);},_5z=new T(function(){return B(unCStr("Prelude.undefined"));}),_5A=new T(function(){return B(err(_5z));}),_5B=function(_5C,_5D,_5E){var _5F=__createJSFunc(1+B(A2(_5x,_5D,new T(function(){return B(A1(_5E,_5A));})))|0,function(_5G){return new F(function(){return _5q(_5C,_5D,_5E,_5G);});});return E(_5F);},_5H=function(_5I){return new F(function(){return _5B(_5c,_5n,_5I);});},_5J=function(_5K,_5L,_5M){return new F(function(){return _5B(_5K,_5L,_5M);});},_5N=function(_5O,_5P,_5Q){var _5R=__lst2arr(B(_G(function(_5S){return new F(function(){return _5J(_5O,_5P,_5S);});},_5Q)));return E(_5R);},_5T=function(_5U){return new F(function(){return _5N(_5c,_5n,_5U);});},_5V=new T2(0,_5H,_5T),_5W=function(_5X,_5Y,_5Z,_){var _60=__apply(_5Y,E(_5Z));return new F(function(){return A3(_4L,_5X,_60,_);});},_61=function(_62,_63,_64,_){return new F(function(){return _5W(_62,E(_63),_64,_);});},_65=function(_66,_67,_68,_){return new F(function(){return _61(_66,_67,_68,_);});},_69=function(_6a,_6b,_){return new F(function(){return _65(_x,_6a,_6b,_);});},_6c=function(_6d){return E(E(_6d).c);},_6e=0,_6f=new T(function(){return eval("(function(method, uri, mimeout, responseType, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, uri);xhr.responseType = responseType;if(mimeout != \'\') {xhr.setRequestHeader(\'Content-type\', mimeout);}xhr.addEventListener(\'load\', function() {if(xhr.status < 400) {cb(null, xhr.response);}else {cb({\'type\':\'http\', \'status\':xhr.status, \'status-text\': xhr.statusText}, null);}});xhr.addEventListener(\'error\', function() {if(xhr.status != 0) {cb({\'type\':\'http\', \'status\':xhr.status, \'status-text\': xhr.statusText}, null);} else {cb({\'type\':\'network\'}, null);}});xhr.send(postdata);})");}),_6g=function(_6h){return E(E(_6h).b);},_6i=function(_6j){return E(E(_6j).b);},_6k=new T(function(){return B(unCStr("base"));}),_6l=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6m=new T(function(){return B(unCStr("PatternMatchFail"));}),_6n=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6k,_6l,_6m),_6o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6n,_4,_4),_6p=function(_6q){return E(_6o);},_6r=function(_6s){var _6t=E(_6s);return new F(function(){return _2M(B(_2K(_6t.a)),_6p,_6t.b);});},_6u=function(_6v){return E(E(_6v).a);},_6w=function(_6x){return new T2(0,_6y,_6x);},_6z=function(_6A,_6B){return new F(function(){return _0(E(_6A).a,_6B);});},_6C=function(_6D,_6E){return new F(function(){return _3X(_6z,_6D,_6E);});},_6F=function(_6G,_6H,_6I){return new F(function(){return _0(E(_6H).a,_6I);});},_6J=new T3(0,_6F,_6u,_6C),_6y=new T(function(){return new T5(0,_6p,_6J,_6w,_6r,_6u);}),_6K=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_6L=function(_6M){return E(E(_6M).c);},_6N=function(_6O,_6P){return new F(function(){return die(new T(function(){return B(A2(_6L,_6P,_6O));}));});},_6Q=function(_6R,_6S){return new F(function(){return _6N(_6R,_6S);});},_6T=function(_6U,_6V){var _6W=E(_6V);if(!_6W._){return new T2(0,_4,_4);}else{var _6X=_6W.a;if(!B(A1(_6U,_6X))){return new T2(0,_4,_6W);}else{var _6Y=new T(function(){var _6Z=B(_6T(_6U,_6W.b));return new T2(0,_6Z.a,_6Z.b);});return new T2(0,new T2(1,_6X,new T(function(){return E(E(_6Y).a);})),new T(function(){return E(E(_6Y).b);}));}}},_70=32,_71=new T(function(){return B(unCStr("\n"));}),_72=function(_73){return (E(_73)==124)?false:true;},_74=function(_75,_76){var _77=B(_6T(_72,B(unCStr(_75)))),_78=_77.a,_79=function(_7a,_7b){var _7c=new T(function(){var _7d=new T(function(){return B(_0(_76,new T(function(){return B(_0(_7b,_71));},1)));});return B(unAppCStr(": ",_7d));},1);return new F(function(){return _0(_7a,_7c);});},_7e=E(_77.b);if(!_7e._){return new F(function(){return _79(_78,_4);});}else{if(E(_7e.a)==124){return new F(function(){return _79(_78,new T2(1,_70,_7e.b));});}else{return new F(function(){return _79(_78,_4);});}}},_7f=function(_7g){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_7g,_6K));})),_6y);});},_7h=new T(function(){return B(_7f("src/Haste/Ajax.hs:(61,7)-(63,60)|case"));}),_7i="PUT",_7j="POST",_7k="DELETE",_7l="GET",_7m=function(_7n){return E(E(_7n).c);},_7o=new T1(1,_4),_7p=function(_){return new F(function(){return nMV(_7o);});},_7q=new T0(2),_7r=function(_7s,_7t,_7u){var _7v=function(_7w){var _7x=function(_){var _7y=E(_7t),_7z=rMV(_7y),_7A=E(_7z);if(!_7A._){var _7B=new T(function(){var _7C=new T(function(){return B(A1(_7w,_5));});return B(_0(_7A.b,new T2(1,new T2(0,_7u,function(_7D){return E(_7C);}),_4)));}),_=wMV(_7y,new T2(0,_7A.a,_7B));return _7q;}else{var _7E=E(_7A.a);if(!_7E._){var _=wMV(_7y,new T2(0,_7u,_4));return new T(function(){return B(A1(_7w,_5));});}else{var _=wMV(_7y,new T1(1,_7E.b));return new T1(1,new T2(1,new T(function(){return B(A1(_7w,_5));}),new T2(1,new T(function(){return B(A2(_7E.a,_7u,_2c));}),_4)));}}};return new T1(0,_7x);};return new F(function(){return A2(_6g,_7s,_7v);});},_7F=function(_7G){return E(E(_7G).d);},_7H=function(_7I,_7J){var _7K=function(_7L){var _7M=function(_){var _7N=E(_7J),_7O=rMV(_7N),_7P=E(_7O);if(!_7P._){var _7Q=_7P.a,_7R=E(_7P.b);if(!_7R._){var _=wMV(_7N,_7o);return new T(function(){return B(A1(_7L,_7Q));});}else{var _7S=E(_7R.a),_=wMV(_7N,new T2(0,_7S.a,_7R.b));return new T1(1,new T2(1,new T(function(){return B(A1(_7L,_7Q));}),new T2(1,new T(function(){return B(A1(_7S.b,_2c));}),_4)));}}else{var _7T=new T(function(){var _7U=function(_7V){var _7W=new T(function(){return B(A1(_7L,_7V));});return function(_7X){return E(_7W);};};return B(_0(_7P.a,new T2(1,_7U,_4)));}),_=wMV(_7N,new T1(1,_7T));return _7q;}};return new T1(0,_7M);};return new F(function(){return A2(_6g,_7I,_7K);});},_7Y=function(_7Z,_80,_81,_82,_83,_84){var _85=B(_2x(_7Z)),_86=new T(function(){return B(_6g(_7Z));}),_87=new T(function(){return B(_6i(_85));}),_88=B(_2z(_85)),_89=new T(function(){return B(_2B(_81));}),_8a=new T(function(){var _8b=function(_8c){var _8d=E(_84),_8e=E(_82),_8f=strEq(E(_i),_8e);if(!E(_8f)){var _8g=E(_8e);}else{var _8g=B(A2(_7m,_80,_6e));}var _8h=B(A2(_7F,_81,_6e)),_8i=E(_D);return function(_5G){return new F(function(){return _2o(_5V,_69,_6f,new T2(1,_8i,new T2(1,_8h,new T2(1,_8g,new T2(1,_8d,new T2(1,_8c,_4))))),_5G);});};},_8j=function(_8k,_8l){var _8m=E(_84),_8n=E(_82),_8o=strEq(E(_i),_8n);if(!E(_8o)){var _8p=E(_8n);}else{var _8p=B(A2(_7m,_80,_6e));}var _8q=B(A2(_7F,_81,_6e)),_8r=E(_8k);return function(_5G){return new F(function(){return _2o(_5V,_69,_6f,new T2(1,_8r,new T2(1,_8q,new T2(1,_8p,new T2(1,_8m,new T2(1,_8l,_4))))),_5G);});};},_8s=E(_83);switch(_8s._){case 0:return B(_8b(E(_7l)));break;case 1:return B(_8b(E(_7k)));break;case 2:return B(_8j(new T(function(){return B(A2(_2m,B(_2v(_80)),_8s.a));}),E(_7j)));break;default:return B(_8j(new T(function(){return B(A2(_2m,B(_2v(_80)),_8s.a));}),E(_7i)));}}),_8t=function(_8u){var _8v=new T(function(){return B(A1(_86,new T(function(){return B(_7H(_2l,_8u));})));}),_8w=new T(function(){var _8x=new T(function(){var _8y=function(_8z,_8A,_){var _8B=E(_8A);if(!_8B._){var _8C=E(_8z);if(!_8C._){return E(_7h);}else{return new F(function(){return _c(new T(function(){return B(A(_7r,[_2l,_8u,new T1(0,_8C.a),_2c]));}),_4,_);});}}else{var _8D=B(A3(_4L,_89,_8B.a,_));return new F(function(){return _c(new T(function(){return B(A(_7r,[_2l,_8u,new T1(1,_8D),_2c]));}),_4,_);});}};return B(A1(_8a,_8y));});return B(A1(_87,_8x));});return new F(function(){return A3(_6c,_88,_8w,_8v);});};return new F(function(){return A3(_1V,_88,new T(function(){return B(A2(_6i,_85,_7p));}),_8t);});},_8E="w8",_8F=function(_8G){return E(_8E);},_8H=function(_8I,_8J){var _8K=E(_8J);return new T2(0,_8K.a,_8K.b);},_8L=function(_8M,_8N){return E(_8N).c;},_8O=function(_8P){var _8Q=B(A1(_8P,_));return E(_8Q);},_8R=function(_8S,_8T,_8U,_8V){var _8W=function(_){var _8X=E(_8U),_8Y=_8X.d,_8Z=_8Y["byteLength"],_90=newByteArr(_8Z),_91=_90,_92=memcpy(_91,_8Y,_8Z>>>0),_93=function(_94,_){while(1){var _95=E(_94);if(!_95._){return _5;}else{var _96=E(_95.a),_97=E(_96.a),_98=_91["v"]["w8"][_97],_=_91["v"]["w8"][_97]=B(A2(_8T,_98,_96.b));_94=_95.b;continue;}}},_99=B(_93(_8V,_));return new T4(0,E(_8X.a),E(_8X.b),_8X.c,_91);};return new F(function(){return _8O(_8W);});},_9a=function(_9b){return E(E(_9b).f);},_9c=new T(function(){return B(unCStr("Negative range size"));}),_9d=new T(function(){return B(err(_9c));}),_9e=function(_9f,_9g,_9h,_9i,_9j){var _9k=E(_9i),_9l=function(_){var _9m=B(A2(_9a,_9f,_9k)),_9n=newByteArr(_9m),_9o=_9n;if(_9m>=0){var _9p=_9m-1|0,_9q=function(_){var _9r=function(_9s,_){while(1){var _9t=E(_9s);if(!_9t._){return _5;}else{var _9u=E(_9t.a),_9v=E(_9u.a),_9w=_9o["v"]["w8"][_9v],_=_9o["v"]["w8"][_9v]=B(A2(_9g,_9w,_9u.b));_9s=_9t.b;continue;}}},_9x=B(_9r(_9j,_));return new T4(0,E(_9k.a),E(_9k.b),_9m,_9o);};if(0<=_9p){var _9y=function(_9z,_){while(1){var _=_9o["v"]["w8"][_9z]=E(_9h);if(_9z!=_9p){var _9A=_9z+1|0;_9z=_9A;continue;}else{return _5;}}},_9B=B(_9y(0,_));return new F(function(){return _9q(_);});}else{return new F(function(){return _9q(_);});}}else{return E(_9d);}},_9C=E(_9l);return new F(function(){return _8O(_9C);});},_9D=function(_9E,_9F,_9G){var _9H=E(_9F),_9I=function(_){var _9J=B(A2(_9a,_9E,_9H)),_9K=newByteArr(_9J),_9L=_9K;if(_9J>=0){var _9M=_9J-1|0,_9N=function(_){var _9O=function(_9P,_){while(1){var _9Q=E(_9P);if(!_9Q._){return _5;}else{var _9R=E(_9Q.a),_=_9L["v"]["w8"][E(_9R.a)]=E(_9R.b);_9P=_9Q.b;continue;}}},_9S=B(_9O(_9G,_));return new T4(0,E(_9H.a),E(_9H.b),_9J,_9L);};if(0<=_9M){var _9T=function(_9U,_){while(1){var _=_9L["v"]["w8"][_9U]=0;if(_9U!=_9M){var _9V=_9U+1|0;_9U=_9V;continue;}else{return _5;}}},_9W=B(_9T(0,_));return new F(function(){return _9N(_);});}else{return new F(function(){return _9N(_);});}}else{return E(_9d);}},_9X=E(_9I);return new F(function(){return _8O(_9X);});},_9Y=function(_9Z,_a0,_a1){return E(_a0).d["v"]["w8"][E(_a1)];},_a2=function(_a3,_a4,_a5){var _a6=function(_){var _a7=E(_a4),_a8=_a7.d,_a9=_a8["byteLength"],_aa=newByteArr(_a9),_ab=_aa,_ac=memcpy(_ab,_a8,_a9>>>0),_ad=function(_ae,_){while(1){var _af=E(_ae);if(!_af._){return _5;}else{var _ag=E(_af.a),_=_ab["v"]["w8"][E(_ag.a)]=E(_ag.b);_ae=_af.b;continue;}}},_ah=B(_ad(_a5,_));return new T4(0,E(_a7.a),E(_a7.b),_a7.c,_ab);};return new F(function(){return _8O(_a6);});},_ai={_:0,a:_8H,b:_8L,c:_9D,d:_9Y,e:_a2,f:_8R,g:_9e},_aj=function(_ak,_al,_){var _am=E(_al);return new T2(0,_am.a,_am.b);},_an=function(_ao,_ap,_){return new F(function(){return _aj(_ao,_ap,_);});},_aq=function(_ar,_as,_){return E(_as).c;},_at=function(_ao,_ap,_){return new F(function(){return _aq(_ao,_ap,_);});},_au=new T(function(){return B(unCStr("Negative range size"));}),_av=new T(function(){return B(err(_au));}),_aw=function(_ax,_ay,_az,_aA,_){var _aB=B(A2(_9a,_ax,new T2(0,_ay,_az))),_aC=newByteArr(_aB);if(_aB>=0){var _aD=_aB-1|0,_aE=new T(function(){return new T4(0,E(_ay),E(_az),_aB,_aC);});if(0<=_aD){var _aF=function(_aG,_){while(1){var _=E(_aE).d["v"]["w8"][_aG]=E(_aA);if(_aG!=_aD){var _aH=_aG+1|0;_aG=_aH;continue;}else{return _5;}}},_aI=B(_aF(0,_));return _aE;}else{return _aE;}}else{return E(_av);}},_aJ=function(_aK,_aL,_aM,_){var _aN=E(_aL);return new F(function(){return _aw(_aK,_aN.a,_aN.b,_aM,_);});},_aO=function(_aP,_ao,_ap,_){return new F(function(){return _aJ(_aP,_ao,_ap,_);});},_aQ=function(_aR,_aS,_aT,_){var _aU=B(A2(_9a,_aR,new T2(0,_aS,_aT))),_aV=newByteArr(_aU);return new T(function(){return new T4(0,E(_aS),E(_aT),_aU,_aV);});},_aW=function(_aX,_aY,_){var _aZ=E(_aY);return new F(function(){return _aQ(_aX,_aZ.a,_aZ.b,_);});},_b0=function(_ao,_ap,_){return new F(function(){return _aW(_ao,_ap,_);});},_b1=function(_b2,_b3,_b4,_){return E(_b3).d["v"]["w8"][E(_b4)];},_b5=function(_aP,_ao,_ap,_){return new F(function(){return _b1(_aP,_ao,_ap,_);});},_b6=function(_b7,_b8,_b9,_ba,_){var _=E(_b8).d["v"]["w8"][E(_b9)]=E(_ba);return _5;},_bb=function(_bc,_aP,_ao,_ap,_){return new F(function(){return _b6(_bc,_aP,_ao,_ap,_);});},_bd=function(_be,_bf,_){var _bg=B(A1(_be,_)),_bh=B(A1(_bf,_));return _bg;},_bi=function(_bj,_bk,_){var _bl=B(A1(_bj,_)),_bm=B(A1(_bk,_));return new T(function(){return B(A1(_bl,_bm));});},_bn=function(_bo,_bp,_){var _bq=B(A1(_bp,_));return _bo;},_br=new T2(0,_24,_bn),_bs=function(_bt,_){return _bt;},_bu=function(_bv,_bw,_){var _bx=B(A1(_bv,_));return new F(function(){return A1(_bw,_);});},_by=new T5(0,_br,_bs,_bi,_bu,_bd),_bz=new T(function(){return E(_4c);}),_bA=function(_bB){return new T6(0,_4l,_4m,_4,_bB,_4l,_4l);},_bC=function(_bD,_){var _bE=new T(function(){return B(A2(_6L,_bz,new T(function(){return B(A1(_bA,_bD));})));});return new F(function(){return die(_bE);});},_bF=function(_bG,_){return new F(function(){return _bC(_bG,_);});},_bH=function(_bI){return new F(function(){return A1(_bF,_bI);});},_bJ=function(_bK,_bL,_){var _bM=B(A1(_bK,_));return new F(function(){return A2(_bL,_bM,_);});},_bN=new T5(0,_by,_bJ,_bu,_bs,_bH),_bO={_:0,a:_bN,b:_an,c:_at,d:_aO,e:_b0,f:_b0,g:_b5,h:_bb},_bP=new T3(0,_ai,_bO,_8F),_bQ="deltaZ",_bR="deltaY",_bS="deltaX",_bT=function(_bU,_bV){var _bW=jsShowI(_bU);return new F(function(){return _0(fromJSStr(_bW),_bV);});},_bX=41,_bY=40,_bZ=function(_c0,_c1,_c2){if(_c1>=0){return new F(function(){return _bT(_c1,_c2);});}else{if(_c0<=6){return new F(function(){return _bT(_c1,_c2);});}else{return new T2(1,_bY,new T(function(){var _c3=jsShowI(_c1);return B(_0(fromJSStr(_c3),new T2(1,_bX,_c2)));}));}}},_c4=new T(function(){return B(unCStr(")"));}),_c5=new T(function(){return B(_bZ(0,2,_c4));}),_c6=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_c5));}),_c7=function(_c8){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_bZ(0,_c8,_c6));}))));});},_c9=function(_ca,_){return new T(function(){var _cb=Number(E(_ca)),_cc=jsTrunc(_cb);if(_cc<0){return B(_c7(_cc));}else{if(_cc>2){return B(_c7(_cc));}else{return _cc;}}});},_cd=0,_ce=new T3(0,_cd,_cd,_cd),_cf="button",_cg=new T(function(){return eval("jsGetMouseCoords");}),_ch=function(_ci,_){var _cj=E(_ci);if(!_cj._){return _4;}else{var _ck=B(_ch(_cj.b,_));return new T2(1,new T(function(){var _cl=Number(E(_cj.a));return jsTrunc(_cl);}),_ck);}},_cm=function(_cn,_){var _co=__arr2lst(0,_cn);return new F(function(){return _ch(_co,_);});},_cp=function(_cq,_){return new F(function(){return _cm(E(_cq),_);});},_cr=function(_cs,_){return new T(function(){var _ct=Number(E(_cs));return jsTrunc(_ct);});},_cu=new T2(0,_cr,_cp),_cv=function(_cw,_){var _cx=E(_cw);if(!_cx._){return _4;}else{var _cy=B(_cv(_cx.b,_));return new T2(1,_cx.a,_cy);}},_cz=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_cA=new T6(0,_4l,_4m,_4,_cz,_4l,_4l),_cB=new T(function(){return B(_4d(_cA));}),_cC=function(_){return new F(function(){return die(_cB);});},_cD=function(_cE,_cF,_cG,_){var _cH=__arr2lst(0,_cG),_cI=B(_cv(_cH,_)),_cJ=E(_cI);if(!_cJ._){return new F(function(){return _cC(_);});}else{var _cK=E(_cJ.b);if(!_cK._){return new F(function(){return _cC(_);});}else{if(!E(_cK.b)._){var _cL=B(A3(_4L,_cE,_cJ.a,_)),_cM=B(A3(_4L,_cF,_cK.a,_));return new T2(0,_cL,_cM);}else{return new F(function(){return _cC(_);});}}}},_cN=function(_cO,_cP,_){if(E(_cO)==7){var _cQ=__app1(E(_cg),_cP),_cR=B(_cD(_cu,_cu,_cQ,_)),_cS=__get(_cP,E(_bS)),_cT=__get(_cP,E(_bR)),_cU=__get(_cP,E(_bQ));return new T(function(){return new T3(0,E(_cR),E(_4l),E(new T3(0,_cS,_cT,_cU)));});}else{var _cV=__app1(E(_cg),_cP),_cW=B(_cD(_cu,_cu,_cV,_)),_cX=__get(_cP,E(_cf)),_cY=__eq(_cX,E(_D));if(!E(_cY)){var _cZ=__isUndef(_cX);if(!E(_cZ)){var _d0=B(_c9(_cX,_));return new T(function(){return new T3(0,E(_cW),E(new T1(1,_d0)),E(_ce));});}else{return new T(function(){return new T3(0,E(_cW),E(_4l),E(_ce));});}}else{return new T(function(){return new T3(0,E(_cW),E(_4l),E(_ce));});}}},_d1=function(_d2,_d3,_){return new F(function(){return _cN(_d2,E(_d3),_);});},_d4="mouseout",_d5="mouseover",_d6="mousemove",_d7="mouseup",_d8="mousedown",_d9="dblclick",_da="click",_db="wheel",_dc=function(_dd){switch(E(_dd)){case 0:return E(_da);case 1:return E(_d9);case 2:return E(_d8);case 3:return E(_d7);case 4:return E(_d6);case 5:return E(_d5);case 6:return E(_d4);default:return E(_db);}},_de=new T2(0,_dc,_d1),_df=function(_dg){return E(_dg);},_dh=new T2(0,_bN,_2j),_di=new T2(0,_dh,_bs),_dj=new T(function(){return B(unCStr("NoMethodError"));}),_dk=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_6k,_6l,_dj),_dl=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_dk,_4,_4),_dm=function(_dn){return E(_dl);},_do=function(_dp){var _dq=E(_dp);return new F(function(){return _2M(B(_2K(_dq.a)),_dm,_dq.b);});},_dr=function(_ds){return E(E(_ds).a);},_dt=function(_6x){return new T2(0,_du,_6x);},_dv=function(_dw,_dx){return new F(function(){return _0(E(_dw).a,_dx);});},_dy=function(_dz,_dA){return new F(function(){return _3X(_dv,_dz,_dA);});},_dB=function(_dC,_dD,_dE){return new F(function(){return _0(E(_dD).a,_dE);});},_dF=new T3(0,_dB,_dr,_dy),_du=new T(function(){return new T5(0,_dm,_dF,_dt,_do,_dr);}),_dG=new T(function(){return B(unCStr("No instance nor default method for class operation"));}),_dH=function(_dI){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_dI,_dG));})),_du);});},_dJ=new T(function(){return B(_dH("Data/Binary/Put.hs:17:10-19|>>="));}),_dK=function(_dL){return E(_dJ);},_dM=new T(function(){return B(unCStr(")"));}),_dN=function(_dO,_dP){var _dQ=new T(function(){var _dR=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_dP,_4)),_dM));})));},1);return B(_0(B(_bZ(0,_dO,_4)),_dR));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_dQ)));});},_dS=function(_dT){return new F(function(){return _bZ(0,E(_dT),_4);});},_dU=function(_dV,_dW,_dX){return new F(function(){return _bZ(E(_dV),E(_dW),_dX);});},_dY=function(_dZ,_e0){return new F(function(){return _bZ(0,E(_dZ),_e0);});},_e1=function(_e2,_e3){return new F(function(){return _3X(_dY,_e2,_e3);});},_e4=new T3(0,_dU,_dS,_e1),_e5=0,_e6=function(_e7,_e8,_e9){return new F(function(){return A1(_e7,new T2(1,_3U,new T(function(){return B(A1(_e8,_e9));})));});},_ea=new T(function(){return B(unCStr(": empty list"));}),_eb=new T(function(){return B(unCStr("Prelude."));}),_ec=function(_ed){return new F(function(){return err(B(_0(_eb,new T(function(){return B(_0(_ed,_ea));},1))));});},_ee=new T(function(){return B(unCStr("foldr1"));}),_ef=new T(function(){return B(_ec(_ee));}),_eg=function(_eh,_ei){var _ej=E(_ei);if(!_ej._){return E(_ef);}else{var _ek=_ej.a,_el=E(_ej.b);if(!_el._){return E(_ek);}else{return new F(function(){return A2(_eh,_ek,new T(function(){return B(_eg(_eh,_el));}));});}}},_em=new T(function(){return B(unCStr(" out of range "));}),_en=new T(function(){return B(unCStr("}.index: Index "));}),_eo=new T(function(){return B(unCStr("Ix{"));}),_ep=new T2(1,_bX,_4),_eq=new T2(1,_bX,_ep),_er=0,_es=function(_et){return E(E(_et).a);},_eu=function(_ev,_ew,_ex,_ey,_ez){var _eA=new T(function(){var _eB=new T(function(){var _eC=new T(function(){var _eD=new T(function(){var _eE=new T(function(){return B(A3(_eg,_e6,new T2(1,new T(function(){return B(A3(_es,_ex,_er,_ey));}),new T2(1,new T(function(){return B(A3(_es,_ex,_er,_ez));}),_4)),_eq));});return B(_0(_em,new T2(1,_bY,new T2(1,_bY,_eE))));});return B(A(_es,[_ex,_e5,_ew,new T2(1,_bX,_eD)]));});return B(_0(_en,new T2(1,_bY,_eC)));},1);return B(_0(_ev,_eB));},1);return new F(function(){return err(B(_0(_eo,_eA)));});},_eF=function(_eG,_eH,_eI,_eJ,_eK){return new F(function(){return _eu(_eG,_eH,_eK,_eI,_eJ);});},_eL=function(_eM,_eN,_eO,_eP){var _eQ=E(_eO);return new F(function(){return _eF(_eM,_eN,_eQ.a,_eQ.b,_eP);});},_eR=function(_eS,_eT,_eU,_eV){return new F(function(){return _eL(_eV,_eU,_eT,_eS);});},_eW=new T(function(){return B(unCStr("Int"));}),_eX=function(_eY,_eZ,_f0){return new F(function(){return _eR(_e4,new T2(0,_eZ,_f0),_eY,_eW);});},_f1=function(_f2,_f3,_f4,_f5,_f6,_f7){var _f8=_f2+_f7|0;if(_f3>_f8){return new F(function(){return _eX(_f8,_f3,_f4);});}else{if(_f8>_f4){return new F(function(){return _eX(_f8,_f3,_f4);});}else{var _f9=_f8-_f3|0;if(0>_f9){return new F(function(){return _dN(_f9,_f5);});}else{if(_f9>=_f5){return new F(function(){return _dN(_f9,_f5);});}else{return _f6["v"]["w8"][_f9];}}}}},_fa=function(_fb){return new F(function(){return err(B(unAppCStr("getWord8: no bytes left at ",new T(function(){return B(_bZ(0,_fb,_4));}))));});},_fc=function(_fd,_fe,_ff,_fg){if(_fg>=_fe){return new F(function(){return _fa(_fg);});}else{return new T2(0,new T(function(){var _fh=E(_ff);return B(_f1(_fd,E(_fh.a),E(_fh.b),_fh.c,_fh.d,_fg));}),_fg+1|0);}},_fi=function(_fj,_fk,_fl,_fm){var _fn=B(_fc(_fj,_fk,_fl,_fm)),_fo=_fn.b,_fp=E(_fn.a);if(_fp>127){var _fq=B(_fi(_fj,_fk,_fl,E(_fo)));return new T2(0,new T(function(){return (E(_fq.a)<<7>>>0|(_fp&127)>>>0)>>>0;}),_fq.b);}else{return new T2(0,_fp,_fo);}},_fr=new T(function(){return B(unCStr("too few bytes"));}),_fs=new T(function(){return B(err(_fr));}),_ft=function(_fu,_fv,_fw,_fx){var _fy=B(_fi(_fu,_fv,_fw,_fx)),_fz=E(_fy.b),_fA=E(_fy.a)&4294967295;return ((_fz+_fA|0)<=_fv)?new T2(0,new T(function(){var _fB=_fv-_fz|0;if(_fA>_fB){return new T3(0,_fu+_fz|0,_fB,_fw);}else{return new T3(0,_fu+_fz|0,_fA,_fw);}}),_fz+_fA|0):E(_fs);},_fC=function(_fD,_fE){var _fF=E(_fD),_fG=B(_ft(_fF.a,_fF.b,_fF.c,E(_fE)));return new T2(0,_fG.a,_fG.b);},_fH=new T2(0,_dK,_fC),_fI=function(_fJ){return E(_dJ);},_fK=function(_fL){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_bZ(9,_fL,_4));}))));});},_fM=function(_fN,_fO,_fP,_fQ){var _fR=B(_fc(_fN,_fO,_fP,_fQ)),_fS=_fR.b,_fT=E(_fR.a)&4294967295;if(_fT>=128){if(_fT>=224){if(_fT>=240){var _fU=B(_fc(_fN,_fO,_fP,E(_fS))),_fV=B(_fc(_fN,_fO,_fP,E(_fU.b))),_fW=B(_fc(_fN,_fO,_fP,E(_fV.b))),_fX=128^E(_fW.a)&4294967295|(128^E(_fV.a)&4294967295|(128^E(_fU.a)&4294967295|(240^_fT)<<6)<<6)<<6;if(_fX>>>0>1114111){return new F(function(){return _fK(_fX);});}else{return new T2(0,_fX,_fW.b);}}else{var _fY=B(_fc(_fN,_fO,_fP,E(_fS))),_fZ=B(_fc(_fN,_fO,_fP,E(_fY.b))),_g0=128^E(_fZ.a)&4294967295|(128^E(_fY.a)&4294967295|(224^_fT)<<6)<<6;if(_g0>>>0>1114111){return new F(function(){return _fK(_g0);});}else{return new T2(0,_g0,_fZ.b);}}}else{var _g1=B(_fc(_fN,_fO,_fP,E(_fS))),_g2=128^E(_g1.a)&4294967295|(192^_fT)<<6;if(_g2>>>0>1114111){return new F(function(){return _fK(_g2);});}else{return new T2(0,_g2,_g1.b);}}}else{if(_fT>>>0>1114111){return new F(function(){return _fK(_fT);});}else{return new T2(0,_fT,_fS);}}},_g3=function(_g4,_g5){var _g6=E(_g4),_g7=B(_fM(_g6.a,_g6.b,_g6.c,E(_g5)));return new T2(0,_g7.a,_g7.b);},_g8=function(_g9,_ga,_gb){var _gc=E(_g9);if(!_gc._){return new T2(0,_4,_gb);}else{var _gd=new T(function(){return B(A2(_gc.a,_ga,_gb));}),_ge=B(_g8(_gc.b,_ga,new T(function(){return E(E(_gd).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_gd).a);}),_ge.a),_ge.b);}},_gf=function(_gg,_gh,_gi,_gj){if(0>=_gg){return new F(function(){return _g8(_4,_gi,_gj);});}else{var _gk=function(_gl){var _gm=E(_gl);return (_gm==1)?E(new T2(1,_gh,_4)):new T2(1,_gh,new T(function(){return B(_gk(_gm-1|0));}));};return new F(function(){return _g8(B(_gk(_gg)),_gi,_gj);});}},_gn=function(_go,_gp,_gq,_gr){var _gs=B(_fi(_go,_gp,_gq,_gr));return new F(function(){return _gf(E(_gs.a)&4294967295,_g3,new T3(0,_go,_gp,_gq),_gs.b);});},_gt=function(_gu,_gv){var _gw=E(_gu),_gx=B(_gn(_gw.a,_gw.b,_gw.c,E(_gv)));return new T2(0,_gx.a,_gx.b);},_gy=new T2(0,_fI,_gt),_gz=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_gA=new T(function(){return B(err(_gz));}),_gB=function(_gC,_gD,_gE){var _gF=function(_){var _gG=E(_gD),_gH=_gG.c,_gI=newArr(_gH,_gA),_gJ=_gI,_gK=function(_gL,_){while(1){if(_gL!=_gH){var _=_gJ[_gL]=_gG.d[_gL],_gM=_gL+1|0;_gL=_gM;continue;}else{return E(_);}}},_=B(_gK(0,_)),_gN=function(_gO,_){while(1){var _gP=E(_gO);if(!_gP._){return new T4(0,E(_gG.a),E(_gG.b),_gH,_gJ);}else{var _gQ=E(_gP.a),_=_gJ[E(_gQ.a)]=_gQ.b;_gO=_gP.b;continue;}}};return new F(function(){return _gN(_gE,_);});};return new F(function(){return _8O(_gF);});},_gR=function(_gS,_gT,_gU){return new F(function(){return _gB(_gS,_gT,_gU);});},_gV=function(_gW,_gX,_gY){return E(E(_gX).d[E(_gY)]);},_gZ=function(_h0,_h1,_h2){return new F(function(){return _gV(_h0,_h1,_h2);});},_h3=function(_h4,_h5,_h6){var _h7=E(_h5),_h8=B(A2(_9a,_h4,_h7)),_h9=function(_){var _ha=newArr(_h8,_gA),_hb=_ha,_hc=function(_hd,_){while(1){var _he=B((function(_hf,_){var _hg=E(_hf);if(!_hg._){return new T(function(){return new T4(0,E(_h7.a),E(_h7.b),_h8,_hb);});}else{var _hh=E(_hg.a),_=_hb[E(_hh.a)]=_hh.b;_hd=_hg.b;return __continue;}})(_hd,_));if(_he!=__continue){return _he;}}};return new F(function(){return _hc(_h6,_);});};return new F(function(){return _8O(_h9);});},_hi=function(_hj,_hk,_hl){return new F(function(){return _h3(_hj,_hk,_hl);});},_hm=function(_hn,_ho){return E(_ho).c;},_hp=function(_hq,_hr){return new F(function(){return _hm(_hq,_hr);});},_hs=function(_ht,_hu){var _hv=E(_hu);return new T2(0,_hv.a,_hv.b);},_hw=function(_hx,_hy){return new F(function(){return _hs(_hx,_hy);});},_hz=function(_hA,_hB,_hC,_hD){var _hE=function(_){var _hF=E(_hC),_hG=_hF.c,_hH=newArr(_hG,_gA),_hI=_hH,_hJ=function(_hK,_){while(1){if(_hK!=_hG){var _=_hI[_hK]=_hF.d[_hK],_hL=_hK+1|0;_hK=_hL;continue;}else{return E(_);}}},_=B(_hJ(0,_)),_hM=function(_hN,_){while(1){var _hO=B((function(_hP,_){var _hQ=E(_hP);if(!_hQ._){return new T4(0,E(_hF.a),E(_hF.b),_hG,_hI);}else{var _hR=E(_hQ.a),_hS=E(_hR.a),_hT=_hI[_hS],_=_hI[_hS]=new T(function(){return B(A2(_hB,_hT,_hR.b));});_hN=_hQ.b;return __continue;}})(_hN,_));if(_hO!=__continue){return _hO;}}};return new F(function(){return _hM(_hD,_);});};return new F(function(){return _8O(_hE);});},_hU=function(_hV,_hW,_hX,_hY,_hZ){var _i0=E(_hY),_i1=B(A2(_9a,_hV,_i0)),_i2=function(_){var _i3=newArr(_i1,_hX),_i4=_i3,_i5=function(_i6,_){while(1){var _i7=B((function(_i8,_){var _i9=E(_i8);if(!_i9._){return new T(function(){return new T4(0,E(_i0.a),E(_i0.b),_i1,_i4);});}else{var _ia=E(_i9.a),_ib=E(_ia.a),_ic=_i4[_ib],_=_i4[_ib]=new T(function(){return B(A2(_hW,_ic,_ia.b));});_i6=_i9.b;return __continue;}})(_i6,_));if(_i7!=__continue){return _i7;}}};return new F(function(){return _i5(_hZ,_);});};return new F(function(){return _8O(_i2);});},_id={_:0,a:_hw,b:_hp,c:_hi,d:_gZ,e:_gR,f:_hz,g:_hU},_ie=new T(function(){return B(unCStr("Negative range size"));}),_if=new T(function(){return B(err(_ie));}),_ig=0,_ih=function(_ii){var _ij=E(_ii);return (E(_ij.b)-E(_ij.a)|0)+1|0;},_ik=function(_il,_im){var _in=E(_il),_io=E(_im);return (E(_in.a)>_io)?false:_io<=E(_in.b);},_ip=new T(function(){return B(unCStr("Int"));}),_iq=function(_ir,_is){return new F(function(){return _eR(_e4,_is,_ir,_ip);});},_it=function(_iu,_iv){var _iw=E(_iu),_ix=E(_iw.a),_iy=E(_iv);if(_ix>_iy){return new F(function(){return _iq(_iy,_iw);});}else{if(_iy>E(_iw.b)){return new F(function(){return _iq(_iy,_iw);});}else{return _iy-_ix|0;}}},_iz=function(_iA,_iB){if(_iA<=_iB){var _iC=function(_iD){return new T2(1,_iD,new T(function(){if(_iD!=_iB){return B(_iC(_iD+1|0));}else{return __Z;}}));};return new F(function(){return _iC(_iA);});}else{return __Z;}},_iE=function(_iF,_iG){return new F(function(){return _iz(E(_iF),E(_iG));});},_iH=function(_iI){var _iJ=E(_iI);return new F(function(){return _iE(_iJ.a,_iJ.b);});},_iK=function(_iL){var _iM=E(_iL),_iN=E(_iM.a),_iO=E(_iM.b);return (_iN>_iO)?E(_e5):(_iO-_iN|0)+1|0;},_iP=function(_iQ,_iR){return E(_iQ)-E(_iR)|0;},_iS=function(_iT,_iU){return new F(function(){return _iP(_iU,E(_iT).a);});},_iV=function(_iW,_iX){return E(_iW)==E(_iX);},_iY=function(_iZ,_j0){return E(_iZ)!=E(_j0);},_j1=new T2(0,_iV,_iY),_j2=function(_j3,_j4){var _j5=E(_j3),_j6=E(_j4);return (_j5>_j6)?E(_j5):E(_j6);},_j7=function(_j8,_j9){var _ja=E(_j8),_jb=E(_j9);return (_ja>_jb)?E(_jb):E(_ja);},_jc=function(_jd,_je){return (_jd>=_je)?(_jd!=_je)?2:1:0;},_jf=function(_jg,_jh){return new F(function(){return _jc(E(_jg),E(_jh));});},_ji=function(_jj,_jk){return E(_jj)>=E(_jk);},_jl=function(_jm,_jn){return E(_jm)>E(_jn);},_jo=function(_jp,_jq){return E(_jp)<=E(_jq);},_jr=function(_js,_jt){return E(_js)<E(_jt);},_ju={_:0,a:_j1,b:_jf,c:_jr,d:_jo,e:_jl,f:_ji,g:_j2,h:_j7},_jv={_:0,a:_ju,b:_iH,c:_it,d:_iS,e:_ik,f:_iK,g:_ih},_jw=function(_jx,_jy,_jz){var _jA=E(_jx);if(!_jA._){return new T2(0,_4,_jz);}else{var _jB=new T(function(){return B(A2(_jA.a,_jy,_jz));}),_jC=B(_jw(_jA.b,_jy,new T(function(){return E(E(_jB).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_jB).a);}),_jC.a),_jC.b);}},_jD=function(_jE,_jF,_jG,_jH){if(0>=_jE){return new F(function(){return _jw(_4,_jG,_jH);});}else{var _jI=function(_jJ){var _jK=E(_jJ);return (_jK==1)?E(new T2(1,_jF,_4)):new T2(1,_jF,new T(function(){return B(_jI(_jK-1|0));}));};return new F(function(){return _jw(B(_jI(_jE)),_jG,_jH);});}},_jL=function(_jM){return E(E(_jM).b);},_jN=function(_jO){return E(E(_jO).c);},_jP=function(_jQ,_jR){var _jS=E(_jQ);if(!_jS._){return __Z;}else{var _jT=E(_jR);return (_jT._==0)?__Z:new T2(1,new T2(0,_jS.a,_jT.a),new T(function(){return B(_jP(_jS.b,_jT.b));}));}},_jU=function(_jV,_jW,_jX,_jY,_jZ,_k0){var _k1=B(_fi(_jX,_jY,_jZ,_k0)),_k2=E(_k1.a)&4294967295,_k3=B(_jD(_k2,new T(function(){return B(_jL(_jV));}),new T3(0,_jX,_jY,_jZ),_k1.b)),_k4=_k3.a,_k5=new T(function(){var _k6=_k2-1|0;return B(A(_jN,[_jW,_jv,new T2(0,_ig,_k6),new T(function(){if(0>_k6){return B(_jP(B(_iz(0,-1)),_k4));}else{var _k7=_k6+1|0;if(_k7>=0){return B(_jP(B(_iz(0,_k7-1|0)),_k4));}else{return E(_if);}}})]));});return new T2(0,_k5,_k3.b);},_k8=function(_k9,_ka,_kb,_kc){var _kd=B(_fi(_k9,_ka,_kb,_kc)),_ke=B(_fi(_k9,_ka,_kb,E(_kd.b))),_kf=B(_jU(_gy,_id,_k9,_ka,_kb,E(_ke.b)));return new T2(0,new T(function(){var _kg=E(_kf.a);return new T6(0,E(_kd.a)&4294967295,E(_ke.a)&4294967295,E(_kg.a),E(_kg.b),_kg.c,_kg.d);}),_kf.b);},_kh=function(_ki,_kj){var _kk=E(_ki),_kl=B(_k8(_kk.a,_kk.b,_kk.c,E(_kj)));return new T2(0,_kl.a,_kl.b);},_km=function(_kn){return E(_dJ);},_ko=new T2(0,_km,_kh),_kp=function(_kq,_kr){var _ks=E(_kq),_kt=B(_fi(_ks.a,_ks.b,_ks.c,E(_kr)));return new T2(0,new T(function(){return E(_kt.a)&4294967295;}),_kt.b);},_ku=new T(function(){return B(_dH("Data/Binary.hs:56:10-20|put"));}),_kv=function(_kw){return E(_ku);},_kx=new T2(0,_kv,_kp),_ky=function(_kz,_kA){var _kB=E(_kA);return new T2(0,_kB.a,_kB.b);},_kC=function(_kD,_kE){return E(_kE).c;},_kF=function(_kG,_kH,_kI,_kJ){var _kK=function(_){var _kL=E(_kI),_kM=_kL.d,_kN=_kM["byteLength"],_kO=newByteArr(_kN),_kP=_kO,_kQ=memcpy(_kP,_kM,_kN>>>0),_kR=function(_kS,_){while(1){var _kT=E(_kS);if(!_kT._){return _5;}else{var _kU=E(_kT.a),_kV=E(_kU.a),_kW=_kP["v"]["i32"][_kV],_=_kP["v"]["i32"][_kV]=B(A2(_kH,_kW,_kU.b));_kS=_kT.b;continue;}}},_kX=B(_kR(_kJ,_));return new T4(0,E(_kL.a),E(_kL.b),_kL.c,_kP);};return new F(function(){return _8O(_kK);});},_kY=function(_kZ,_l0,_l1,_l2,_l3){var _l4=E(_l2),_l5=function(_){var _l6=B(A2(_9a,_kZ,_l4)),_l7=newByteArr(imul(4,_l6)|0),_l8=_l7;if(_l6>=0){var _l9=_l6-1|0,_la=function(_){var _lb=function(_lc,_){while(1){var _ld=E(_lc);if(!_ld._){return _5;}else{var _le=E(_ld.a),_lf=E(_le.a),_lg=_l8["v"]["i32"][_lf],_=_l8["v"]["i32"][_lf]=B(A2(_l0,_lg,_le.b));_lc=_ld.b;continue;}}},_lh=B(_lb(_l3,_));return new T4(0,E(_l4.a),E(_l4.b),_l6,_l8);};if(0<=_l9){var _li=function(_lj,_){while(1){var _=_l8["v"]["i32"][_lj]=E(_l1);if(_lj!=_l9){var _lk=_lj+1|0;_lj=_lk;continue;}else{return _5;}}},_ll=B(_li(0,_));return new F(function(){return _la(_);});}else{return new F(function(){return _la(_);});}}else{return E(_9d);}},_lm=E(_l5);return new F(function(){return _8O(_lm);});},_ln=function(_lo,_lp,_lq){var _lr=E(_lp),_ls=function(_){var _lt=B(A2(_9a,_lo,_lr)),_lu=newByteArr(imul(4,_lt)|0),_lv=_lu;if(_lt>=0){var _lw=_lt-1|0,_lx=function(_){var _ly=function(_lz,_){while(1){var _lA=E(_lz);if(!_lA._){return _5;}else{var _lB=E(_lA.a),_=_lv["v"]["i32"][E(_lB.a)]=E(_lB.b);_lz=_lA.b;continue;}}},_lC=B(_ly(_lq,_));return new T4(0,E(_lr.a),E(_lr.b),_lt,_lv);};if(0<=_lw){var _lD=function(_lE,_){while(1){var _=_lv["v"]["i32"][_lE]=0;if(_lE!=_lw){var _lF=_lE+1|0;_lE=_lF;continue;}else{return _5;}}},_lG=B(_lD(0,_));return new F(function(){return _lx(_);});}else{return new F(function(){return _lx(_);});}}else{return E(_9d);}},_lH=E(_ls);return new F(function(){return _8O(_lH);});},_lI=function(_lJ,_lK,_lL){return E(_lK).d["v"]["i32"][E(_lL)];},_lM=function(_lN,_lO,_lP){var _lQ=function(_){var _lR=E(_lO),_lS=_lR.d,_lT=_lS["byteLength"],_lU=newByteArr(_lT),_lV=_lU,_lW=memcpy(_lV,_lS,_lT>>>0),_lX=function(_lY,_){while(1){var _lZ=E(_lY);if(!_lZ._){return _5;}else{var _m0=E(_lZ.a),_=_lV["v"]["i32"][E(_m0.a)]=E(_m0.b);_lY=_lZ.b;continue;}}},_m1=B(_lX(_lP,_));return new T4(0,E(_lR.a),E(_lR.b),_lR.c,_lV);};return new F(function(){return _8O(_lQ);});},_m2={_:0,a:_ky,b:_kC,c:_ln,d:_lI,e:_lM,f:_kF,g:_kY},_m3=function(_m4,_m5,_m6,_m7){var _m8=B(_ft(_m4,_m5,_m6,_m7)),_m9=B(_jU(_kx,_m2,_m4,_m5,_m6,E(_m8.b)));return new T2(0,new T(function(){var _ma=E(_m9.a);return new T5(0,_m8.a,E(_ma.a),E(_ma.b),_ma.c,_ma.d);}),_m9.b);},_mb=function(_mc,_md){var _me=E(_mc),_mf=B(_m3(_me.a,_me.b,_me.c,E(_md)));return new T2(0,_mf.a,_mf.b);},_mg=function(_mh){return E(_dJ);},_mi=new T2(0,_mg,_mb),_mj=function(_mk){return new F(function(){return _iz(E(_mk),2147483647);});},_ml=function(_mm,_mn,_mo){if(_mo<=_mn){var _mp=new T(function(){var _mq=_mn-_mm|0,_mr=function(_ms){return (_ms>=(_mo-_mq|0))?new T2(1,_ms,new T(function(){return B(_mr(_ms+_mq|0));})):new T2(1,_ms,_4);};return B(_mr(_mn));});return new T2(1,_mm,_mp);}else{return (_mo<=_mm)?new T2(1,_mm,_4):__Z;}},_mt=function(_mu,_mv,_mw){if(_mw>=_mv){var _mx=new T(function(){var _my=_mv-_mu|0,_mz=function(_mA){return (_mA<=(_mw-_my|0))?new T2(1,_mA,new T(function(){return B(_mz(_mA+_my|0));})):new T2(1,_mA,_4);};return B(_mz(_mv));});return new T2(1,_mu,_mx);}else{return (_mw>=_mu)?new T2(1,_mu,_4):__Z;}},_mB=function(_mC,_mD){if(_mD<_mC){return new F(function(){return _ml(_mC,_mD,-2147483648);});}else{return new F(function(){return _mt(_mC,_mD,2147483647);});}},_mE=function(_mF,_mG){return new F(function(){return _mB(E(_mF),E(_mG));});},_mH=function(_mI,_mJ,_mK){if(_mJ<_mI){return new F(function(){return _ml(_mI,_mJ,_mK);});}else{return new F(function(){return _mt(_mI,_mJ,_mK);});}},_mL=function(_mM,_mN,_mO){return new F(function(){return _mH(E(_mM),E(_mN),E(_mO));});},_mP=function(_mQ){return E(_mQ);},_mR=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_mS=new T(function(){return B(err(_mR));}),_mT=function(_mU){var _mV=E(_mU);return (_mV==(-2147483648))?E(_mS):_mV-1|0;},_mW=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_mX=new T(function(){return B(err(_mW));}),_mY=function(_mZ){var _n0=E(_mZ);return (_n0==2147483647)?E(_mX):_n0+1|0;},_n1={_:0,a:_mY,b:_mT,c:_mP,d:_mP,e:_mj,f:_mE,g:_iE,h:_mL},_n2=function(_n3,_n4){if(_n3<=0){if(_n3>=0){return new F(function(){return quot(_n3,_n4);});}else{if(_n4<=0){return new F(function(){return quot(_n3,_n4);});}else{return quot(_n3+1|0,_n4)-1|0;}}}else{if(_n4>=0){if(_n3>=0){return new F(function(){return quot(_n3,_n4);});}else{if(_n4<=0){return new F(function(){return quot(_n3,_n4);});}else{return quot(_n3+1|0,_n4)-1|0;}}}else{return quot(_n3-1|0,_n4)-1|0;}}},_n5=new T(function(){return B(unCStr("base"));}),_n6=new T(function(){return B(unCStr("GHC.Exception"));}),_n7=new T(function(){return B(unCStr("ArithException"));}),_n8=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_n5,_n6,_n7),_n9=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_n8,_4,_4),_na=function(_nb){return E(_n9);},_nc=function(_nd){var _ne=E(_nd);return new F(function(){return _2M(B(_2K(_ne.a)),_na,_ne.b);});},_nf=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_ng=new T(function(){return B(unCStr("denormal"));}),_nh=new T(function(){return B(unCStr("divide by zero"));}),_ni=new T(function(){return B(unCStr("loss of precision"));}),_nj=new T(function(){return B(unCStr("arithmetic underflow"));}),_nk=new T(function(){return B(unCStr("arithmetic overflow"));}),_nl=function(_nm,_nn){switch(E(_nm)){case 0:return new F(function(){return _0(_nk,_nn);});break;case 1:return new F(function(){return _0(_nj,_nn);});break;case 2:return new F(function(){return _0(_ni,_nn);});break;case 3:return new F(function(){return _0(_nh,_nn);});break;case 4:return new F(function(){return _0(_ng,_nn);});break;default:return new F(function(){return _0(_nf,_nn);});}},_no=function(_np){return new F(function(){return _nl(_np,_4);});},_nq=function(_nr,_ns,_nt){return new F(function(){return _nl(_ns,_nt);});},_nu=function(_nv,_nw){return new F(function(){return _3X(_nl,_nv,_nw);});},_nx=new T3(0,_nq,_no,_nu),_ny=new T(function(){return new T5(0,_na,_nx,_nz,_nc,_no);}),_nz=function(_6S){return new T2(0,_ny,_6S);},_nA=3,_nB=new T(function(){return B(_nz(_nA));}),_nC=new T(function(){return die(_nB);}),_nD=0,_nE=new T(function(){return B(_nz(_nD));}),_nF=new T(function(){return die(_nE);}),_nG=function(_nH,_nI){var _nJ=E(_nI);switch(_nJ){case -1:var _nK=E(_nH);if(_nK==(-2147483648)){return E(_nF);}else{return new F(function(){return _n2(_nK,-1);});}break;case 0:return E(_nC);default:return new F(function(){return _n2(_nH,_nJ);});}},_nL=function(_nM,_nN){return new F(function(){return _nG(E(_nM),E(_nN));});},_nO=0,_nP=new T2(0,_nF,_nO),_nQ=function(_nR,_nS){var _nT=E(_nR),_nU=E(_nS);switch(_nU){case -1:var _nV=E(_nT);if(_nV==(-2147483648)){return E(_nP);}else{if(_nV<=0){if(_nV>=0){var _nW=quotRemI(_nV,-1);return new T2(0,_nW.a,_nW.b);}else{var _nX=quotRemI(_nV,-1);return new T2(0,_nX.a,_nX.b);}}else{var _nY=quotRemI(_nV-1|0,-1);return new T2(0,_nY.a-1|0,(_nY.b+(-1)|0)+1|0);}}break;case 0:return E(_nC);default:if(_nT<=0){if(_nT>=0){var _nZ=quotRemI(_nT,_nU);return new T2(0,_nZ.a,_nZ.b);}else{if(_nU<=0){var _o0=quotRemI(_nT,_nU);return new T2(0,_o0.a,_o0.b);}else{var _o1=quotRemI(_nT+1|0,_nU);return new T2(0,_o1.a-1|0,(_o1.b+_nU|0)-1|0);}}}else{if(_nU>=0){if(_nT>=0){var _o2=quotRemI(_nT,_nU);return new T2(0,_o2.a,_o2.b);}else{if(_nU<=0){var _o3=quotRemI(_nT,_nU);return new T2(0,_o3.a,_o3.b);}else{var _o4=quotRemI(_nT+1|0,_nU);return new T2(0,_o4.a-1|0,(_o4.b+_nU|0)-1|0);}}}else{var _o5=quotRemI(_nT-1|0,_nU);return new T2(0,_o5.a-1|0,(_o5.b+_nU|0)+1|0);}}}},_o6=function(_o7,_o8){var _o9=_o7%_o8;if(_o7<=0){if(_o7>=0){return E(_o9);}else{if(_o8<=0){return E(_o9);}else{var _oa=E(_o9);return (_oa==0)?0:_oa+_o8|0;}}}else{if(_o8>=0){if(_o7>=0){return E(_o9);}else{if(_o8<=0){return E(_o9);}else{var _ob=E(_o9);return (_ob==0)?0:_ob+_o8|0;}}}else{var _oc=E(_o9);return (_oc==0)?0:_oc+_o8|0;}}},_od=function(_oe,_of){var _og=E(_of);switch(_og){case -1:return E(_nO);case 0:return E(_nC);default:return new F(function(){return _o6(E(_oe),_og);});}},_oh=function(_oi,_oj){var _ok=E(_oi),_ol=E(_oj);switch(_ol){case -1:var _om=E(_ok);if(_om==(-2147483648)){return E(_nF);}else{return new F(function(){return quot(_om,-1);});}break;case 0:return E(_nC);default:return new F(function(){return quot(_ok,_ol);});}},_on=function(_oo,_op){var _oq=E(_oo),_or=E(_op);switch(_or){case -1:var _os=E(_oq);if(_os==(-2147483648)){return E(_nP);}else{var _ot=quotRemI(_os,-1);return new T2(0,_ot.a,_ot.b);}break;case 0:return E(_nC);default:var _ou=quotRemI(_oq,_or);return new T2(0,_ou.a,_ou.b);}},_ov=function(_ow,_ox){var _oy=E(_ox);switch(_oy){case -1:return E(_nO);case 0:return E(_nC);default:return E(_ow)%_oy;}},_oz=function(_oA){return new T1(0,_oA);},_oB=function(_oC){return new F(function(){return _oz(E(_oC));});},_oD=new T1(0,1),_oE=function(_oF){return new T2(0,E(B(_oz(E(_oF)))),E(_oD));},_oG=function(_oH,_oI){return imul(E(_oH),E(_oI))|0;},_oJ=function(_oK,_oL){return E(_oK)+E(_oL)|0;},_oM=function(_oN){var _oO=E(_oN);return (_oO<0)? -_oO:E(_oO);},_oP=function(_oQ){var _oR=E(_oQ);if(!_oR._){return E(_oR.a);}else{return new F(function(){return I_toInt(_oR.a);});}},_oS=function(_oT){return new F(function(){return _oP(_oT);});},_oU=function(_oV){return  -E(_oV);},_oW=-1,_oX=0,_oY=1,_oZ=function(_p0){var _p1=E(_p0);return (_p1>=0)?(E(_p1)==0)?E(_oX):E(_oY):E(_oW);},_p2={_:0,a:_oJ,b:_iP,c:_oG,d:_oU,e:_oM,f:_oZ,g:_oS},_p3=new T2(0,_iV,_iY),_p4={_:0,a:_p3,b:_jf,c:_jr,d:_jo,e:_jl,f:_ji,g:_j2,h:_j7},_p5=new T3(0,_p2,_p4,_oE),_p6={_:0,a:_p5,b:_n1,c:_oh,d:_ov,e:_nL,f:_od,g:_on,h:_nQ,i:_oB},_p7={_:0,a:_mY,b:_mT,c:_mP,d:_mP,e:_mj,f:_mE,g:_iE,h:_mL},_p8={_:0,a:_oJ,b:_iP,c:_oG,d:_oU,e:_oM,f:_oZ,g:_oS},_p9=new T3(0,_p8,_ju,_oE),_pa={_:0,a:_p9,b:_p7,c:_oh,d:_ov,e:_nL,f:_od,g:_on,h:_nQ,i:_oB},_pb=new T1(0,2),_pc=function(_pd){return E(E(_pd).a);},_pe=function(_pf){return E(E(_pf).a);},_pg=function(_ph,_pi){while(1){var _pj=E(_ph);if(!_pj._){var _pk=_pj.a,_pl=E(_pi);if(!_pl._){var _pm=_pl.a;if(!(imul(_pk,_pm)|0)){return new T1(0,imul(_pk,_pm)|0);}else{_ph=new T1(1,I_fromInt(_pk));_pi=new T1(1,I_fromInt(_pm));continue;}}else{_ph=new T1(1,I_fromInt(_pk));_pi=_pl;continue;}}else{var _pn=E(_pi);if(!_pn._){_ph=_pj;_pi=new T1(1,I_fromInt(_pn.a));continue;}else{return new T1(1,I_mul(_pj.a,_pn.a));}}}},_po=function(_pp,_pq,_pr){while(1){if(!(_pq%2)){var _ps=B(_pg(_pp,_pp)),_pt=quot(_pq,2);_pp=_ps;_pq=_pt;continue;}else{var _pu=E(_pq);if(_pu==1){return new F(function(){return _pg(_pp,_pr);});}else{var _ps=B(_pg(_pp,_pp)),_pv=B(_pg(_pp,_pr));_pp=_ps;_pq=quot(_pu-1|0,2);_pr=_pv;continue;}}}},_pw=function(_px,_py){while(1){if(!(_py%2)){var _pz=B(_pg(_px,_px)),_pA=quot(_py,2);_px=_pz;_py=_pA;continue;}else{var _pB=E(_py);if(_pB==1){return E(_px);}else{return new F(function(){return _po(B(_pg(_px,_px)),quot(_pB-1|0,2),_px);});}}}},_pC=function(_pD){return E(E(_pD).c);},_pE=function(_pF){return E(E(_pF).a);},_pG=function(_pH){return E(E(_pH).b);},_pI=function(_pJ){return E(E(_pJ).b);},_pK=function(_pL){return E(E(_pL).c);},_pM=function(_pN){return E(E(_pN).a);},_pO=new T1(0,0),_pP=new T1(0,2),_pQ=function(_pR){return E(E(_pR).g);},_pS=function(_pT){return E(E(_pT).d);},_pU=function(_pV,_pW){var _pX=B(_pc(_pV)),_pY=new T(function(){return B(_pe(_pX));}),_pZ=new T(function(){return B(A3(_pS,_pV,_pW,new T(function(){return B(A2(_pQ,_pY,_pP));})));});return new F(function(){return A3(_pM,B(_pE(B(_pG(_pX)))),_pZ,new T(function(){return B(A2(_pQ,_pY,_pO));}));});},_q0=new T(function(){return B(unCStr("Negative exponent"));}),_q1=new T(function(){return B(err(_q0));}),_q2=function(_q3){return E(E(_q3).c);},_q4=function(_q5,_q6,_q7,_q8){var _q9=B(_pc(_q6)),_qa=new T(function(){return B(_pe(_q9));}),_qb=B(_pG(_q9));if(!B(A3(_pK,_qb,_q8,new T(function(){return B(A2(_pQ,_qa,_pO));})))){if(!B(A3(_pM,B(_pE(_qb)),_q8,new T(function(){return B(A2(_pQ,_qa,_pO));})))){var _qc=new T(function(){return B(A2(_pQ,_qa,_pP));}),_qd=new T(function(){return B(A2(_pQ,_qa,_oD));}),_qe=B(_pE(_qb)),_qf=function(_qg,_qh,_qi){while(1){var _qj=B((function(_qk,_ql,_qm){if(!B(_pU(_q6,_ql))){if(!B(A3(_pM,_qe,_ql,_qd))){var _qn=new T(function(){return B(A3(_q2,_q6,new T(function(){return B(A3(_pI,_qa,_ql,_qd));}),_qc));});_qg=new T(function(){return B(A3(_pC,_q5,_qk,_qk));});_qh=_qn;_qi=new T(function(){return B(A3(_pC,_q5,_qk,_qm));});return __continue;}else{return new F(function(){return A3(_pC,_q5,_qk,_qm);});}}else{var _qo=_qm;_qg=new T(function(){return B(A3(_pC,_q5,_qk,_qk));});_qh=new T(function(){return B(A3(_q2,_q6,_ql,_qc));});_qi=_qo;return __continue;}})(_qg,_qh,_qi));if(_qj!=__continue){return _qj;}}},_qp=function(_qq,_qr){while(1){var _qs=B((function(_qt,_qu){if(!B(_pU(_q6,_qu))){if(!B(A3(_pM,_qe,_qu,_qd))){var _qv=new T(function(){return B(A3(_q2,_q6,new T(function(){return B(A3(_pI,_qa,_qu,_qd));}),_qc));});return new F(function(){return _qf(new T(function(){return B(A3(_pC,_q5,_qt,_qt));}),_qv,_qt);});}else{return E(_qt);}}else{_qq=new T(function(){return B(A3(_pC,_q5,_qt,_qt));});_qr=new T(function(){return B(A3(_q2,_q6,_qu,_qc));});return __continue;}})(_qq,_qr));if(_qs!=__continue){return _qs;}}};return new F(function(){return _qp(_q7,_q8);});}else{return new F(function(){return A2(_pQ,_q5,_oD);});}}else{return E(_q1);}},_qw=new T(function(){return B(err(_q0));}),_qx=function(_qy){var _qz=I_decodeDouble(_qy);return new T2(0,new T1(1,_qz.b),_qz.a);},_qA=function(_qB,_qC){var _qD=E(_qB);return (_qD._==0)?_qD.a*Math.pow(2,_qC):I_toNumber(_qD.a)*Math.pow(2,_qC);},_qE=function(_qF,_qG){var _qH=E(_qF);if(!_qH._){var _qI=_qH.a,_qJ=E(_qG);return (_qJ._==0)?_qI==_qJ.a:(I_compareInt(_qJ.a,_qI)==0)?true:false;}else{var _qK=_qH.a,_qL=E(_qG);return (_qL._==0)?(I_compareInt(_qK,_qL.a)==0)?true:false:(I_compare(_qK,_qL.a)==0)?true:false;}},_qM=function(_qN,_qO){while(1){var _qP=E(_qN);if(!_qP._){var _qQ=E(_qP.a);if(_qQ==(-2147483648)){_qN=new T1(1,I_fromInt(-2147483648));continue;}else{var _qR=E(_qO);if(!_qR._){var _qS=_qR.a;return new T2(0,new T1(0,quot(_qQ,_qS)),new T1(0,_qQ%_qS));}else{_qN=new T1(1,I_fromInt(_qQ));_qO=_qR;continue;}}}else{var _qT=E(_qO);if(!_qT._){_qN=_qP;_qO=new T1(1,I_fromInt(_qT.a));continue;}else{var _qU=I_quotRem(_qP.a,_qT.a);return new T2(0,new T1(1,_qU.a),new T1(1,_qU.b));}}}},_qV=0,_qW=new T1(0,0),_qX=function(_qY,_qZ){var _r0=B(_qx(_qZ)),_r1=_r0.a,_r2=_r0.b,_r3=new T(function(){return B(_pe(new T(function(){return B(_pc(_qY));})));});if(_r2<0){var _r4= -_r2;if(_r4>=0){var _r5=E(_r4);if(!_r5){var _r6=E(_oD);}else{var _r6=B(_pw(_pb,_r5));}if(!B(_qE(_r6,_qW))){var _r7=B(_qM(_r1,_r6));return new T2(0,new T(function(){return B(A2(_pQ,_r3,_r7.a));}),new T(function(){return B(_qA(_r7.b,_r2));}));}else{return E(_nC);}}else{return E(_qw);}}else{var _r8=new T(function(){var _r9=new T(function(){return B(_q4(_r3,_pa,new T(function(){return B(A2(_pQ,_r3,_pb));}),_r2));});return B(A3(_pC,_r3,new T(function(){return B(A2(_pQ,_r3,_r1));}),_r9));});return new T2(0,_r8,_qV);}},_ra=function(_rb){var _rc=E(_rb);if(!_rc._){return _rc.a;}else{return new F(function(){return I_toNumber(_rc.a);});}},_rd=function(_re,_rf){var _rg=B(_qX(_p6,Math.pow(B(_ra(_re)),_rf))),_rh=_rg.a;return (E(_rg.b)>=0)?E(_rh):E(_rh)-1|0;},_ri=new T1(0,1),_rj=new T1(0,0),_rk=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_rl=new T(function(){return B(err(_rk));}),_rm=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_rn=new T(function(){return B(err(_rm));}),_ro=new T1(0,2),_rp=new T(function(){return B(unCStr("NaN"));}),_rq=new T(function(){return B(_7f("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_rr=function(_rs,_rt){while(1){var _ru=B((function(_rv,_rw){var _rx=E(_rv);switch(_rx._){case 0:var _ry=E(_rw);if(!_ry._){return __Z;}else{_rs=B(A1(_rx.a,_ry.a));_rt=_ry.b;return __continue;}break;case 1:var _rz=B(A1(_rx.a,_rw)),_rA=_rw;_rs=_rz;_rt=_rA;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_rx.a,_rw),new T(function(){return B(_rr(_rx.b,_rw));}));default:return E(_rx.a);}})(_rs,_rt));if(_ru!=__continue){return _ru;}}},_rB=function(_rC,_rD){var _rE=function(_rF){var _rG=E(_rD);if(_rG._==3){return new T2(3,_rG.a,new T(function(){return B(_rB(_rC,_rG.b));}));}else{var _rH=E(_rC);if(_rH._==2){return E(_rG);}else{var _rI=E(_rG);if(_rI._==2){return E(_rH);}else{var _rJ=function(_rK){var _rL=E(_rI);if(_rL._==4){var _rM=function(_rN){return new T1(4,new T(function(){return B(_0(B(_rr(_rH,_rN)),_rL.a));}));};return new T1(1,_rM);}else{var _rO=E(_rH);if(_rO._==1){var _rP=_rO.a,_rQ=E(_rL);if(!_rQ._){return new T1(1,function(_rR){return new F(function(){return _rB(B(A1(_rP,_rR)),_rQ);});});}else{var _rS=function(_rT){return new F(function(){return _rB(B(A1(_rP,_rT)),new T(function(){return B(A1(_rQ.a,_rT));}));});};return new T1(1,_rS);}}else{var _rU=E(_rL);if(!_rU._){return E(_rq);}else{var _rV=function(_rW){return new F(function(){return _rB(_rO,new T(function(){return B(A1(_rU.a,_rW));}));});};return new T1(1,_rV);}}}},_rX=E(_rH);switch(_rX._){case 1:var _rY=E(_rI);if(_rY._==4){var _rZ=function(_s0){return new T1(4,new T(function(){return B(_0(B(_rr(B(A1(_rX.a,_s0)),_s0)),_rY.a));}));};return new T1(1,_rZ);}else{return new F(function(){return _rJ(_);});}break;case 4:var _s1=_rX.a,_s2=E(_rI);switch(_s2._){case 0:var _s3=function(_s4){var _s5=new T(function(){return B(_0(_s1,new T(function(){return B(_rr(_s2,_s4));},1)));});return new T1(4,_s5);};return new T1(1,_s3);case 1:var _s6=function(_s7){var _s8=new T(function(){return B(_0(_s1,new T(function(){return B(_rr(B(A1(_s2.a,_s7)),_s7));},1)));});return new T1(4,_s8);};return new T1(1,_s6);default:return new T1(4,new T(function(){return B(_0(_s1,_s2.a));}));}break;default:return new F(function(){return _rJ(_);});}}}}},_s9=E(_rC);switch(_s9._){case 0:var _sa=E(_rD);if(!_sa._){var _sb=function(_sc){return new F(function(){return _rB(B(A1(_s9.a,_sc)),new T(function(){return B(A1(_sa.a,_sc));}));});};return new T1(0,_sb);}else{return new F(function(){return _rE(_);});}break;case 3:return new T2(3,_s9.a,new T(function(){return B(_rB(_s9.b,_rD));}));default:return new F(function(){return _rE(_);});}},_sd=new T(function(){return B(unCStr("("));}),_se=new T(function(){return B(unCStr(")"));}),_sf=function(_sg,_sh){while(1){var _si=E(_sg);if(!_si._){return (E(_sh)._==0)?true:false;}else{var _sj=E(_sh);if(!_sj._){return false;}else{if(E(_si.a)!=E(_sj.a)){return false;}else{_sg=_si.b;_sh=_sj.b;continue;}}}}},_sk=function(_sl,_sm){return E(_sl)!=E(_sm);},_sn=function(_so,_sp){return E(_so)==E(_sp);},_sq=new T2(0,_sn,_sk),_sr=function(_ss,_st){while(1){var _su=E(_ss);if(!_su._){return (E(_st)._==0)?true:false;}else{var _sv=E(_st);if(!_sv._){return false;}else{if(E(_su.a)!=E(_sv.a)){return false;}else{_ss=_su.b;_st=_sv.b;continue;}}}}},_sw=function(_sx,_sy){return (!B(_sr(_sx,_sy)))?true:false;},_sz=new T2(0,_sr,_sw),_sA=function(_sB,_sC){var _sD=E(_sB);switch(_sD._){case 0:return new T1(0,function(_sE){return new F(function(){return _sA(B(A1(_sD.a,_sE)),_sC);});});case 1:return new T1(1,function(_sF){return new F(function(){return _sA(B(A1(_sD.a,_sF)),_sC);});});case 2:return new T0(2);case 3:return new F(function(){return _rB(B(A1(_sC,_sD.a)),new T(function(){return B(_sA(_sD.b,_sC));}));});break;default:var _sG=function(_sH){var _sI=E(_sH);if(!_sI._){return __Z;}else{var _sJ=E(_sI.a);return new F(function(){return _0(B(_rr(B(A1(_sC,_sJ.a)),_sJ.b)),new T(function(){return B(_sG(_sI.b));},1));});}},_sK=B(_sG(_sD.a));return (_sK._==0)?new T0(2):new T1(4,_sK);}},_sL=new T0(2),_sM=function(_sN){return new T2(3,_sN,_sL);},_sO=function(_sP,_sQ){var _sR=E(_sP);if(!_sR){return new F(function(){return A1(_sQ,_5);});}else{var _sS=new T(function(){return B(_sO(_sR-1|0,_sQ));});return new T1(0,function(_sT){return E(_sS);});}},_sU=function(_sV,_sW,_sX){var _sY=new T(function(){return B(A1(_sV,_sM));}),_sZ=function(_t0,_t1,_t2,_t3){while(1){var _t4=B((function(_t5,_t6,_t7,_t8){var _t9=E(_t5);switch(_t9._){case 0:var _ta=E(_t6);if(!_ta._){return new F(function(){return A1(_sW,_t8);});}else{var _tb=_t7+1|0,_tc=_t8;_t0=B(A1(_t9.a,_ta.a));_t1=_ta.b;_t2=_tb;_t3=_tc;return __continue;}break;case 1:var _td=B(A1(_t9.a,_t6)),_te=_t6,_tb=_t7,_tc=_t8;_t0=_td;_t1=_te;_t2=_tb;_t3=_tc;return __continue;case 2:return new F(function(){return A1(_sW,_t8);});break;case 3:var _tf=new T(function(){return B(_sA(_t9,_t8));});return new F(function(){return _sO(_t7,function(_tg){return E(_tf);});});break;default:return new F(function(){return _sA(_t9,_t8);});}})(_t0,_t1,_t2,_t3));if(_t4!=__continue){return _t4;}}};return function(_th){return new F(function(){return _sZ(_sY,_th,0,_sX);});};},_ti=function(_tj){return new F(function(){return A1(_tj,_4);});},_tk=function(_tl,_tm){var _tn=function(_to){var _tp=E(_to);if(!_tp._){return E(_ti);}else{var _tq=_tp.a;if(!B(A1(_tl,_tq))){return E(_ti);}else{var _tr=new T(function(){return B(_tn(_tp.b));}),_ts=function(_tt){var _tu=new T(function(){return B(A1(_tr,function(_tv){return new F(function(){return A1(_tt,new T2(1,_tq,_tv));});}));});return new T1(0,function(_tw){return E(_tu);});};return E(_ts);}}};return function(_tx){return new F(function(){return A2(_tn,_tx,_tm);});};},_ty=new T0(6),_tz=new T(function(){return B(unCStr("valDig: Bad base"));}),_tA=new T(function(){return B(err(_tz));}),_tB=function(_tC,_tD){var _tE=function(_tF,_tG){var _tH=E(_tF);if(!_tH._){var _tI=new T(function(){return B(A1(_tG,_4));});return function(_tJ){return new F(function(){return A1(_tJ,_tI);});};}else{var _tK=E(_tH.a),_tL=function(_tM){var _tN=new T(function(){return B(_tE(_tH.b,function(_tO){return new F(function(){return A1(_tG,new T2(1,_tM,_tO));});}));}),_tP=function(_tQ){var _tR=new T(function(){return B(A1(_tN,_tQ));});return new T1(0,function(_tS){return E(_tR);});};return E(_tP);};switch(E(_tC)){case 8:if(48>_tK){var _tT=new T(function(){return B(A1(_tG,_4));});return function(_tU){return new F(function(){return A1(_tU,_tT);});};}else{if(_tK>55){var _tV=new T(function(){return B(A1(_tG,_4));});return function(_tW){return new F(function(){return A1(_tW,_tV);});};}else{return new F(function(){return _tL(_tK-48|0);});}}break;case 10:if(48>_tK){var _tX=new T(function(){return B(A1(_tG,_4));});return function(_tY){return new F(function(){return A1(_tY,_tX);});};}else{if(_tK>57){var _tZ=new T(function(){return B(A1(_tG,_4));});return function(_u0){return new F(function(){return A1(_u0,_tZ);});};}else{return new F(function(){return _tL(_tK-48|0);});}}break;case 16:if(48>_tK){if(97>_tK){if(65>_tK){var _u1=new T(function(){return B(A1(_tG,_4));});return function(_u2){return new F(function(){return A1(_u2,_u1);});};}else{if(_tK>70){var _u3=new T(function(){return B(A1(_tG,_4));});return function(_u4){return new F(function(){return A1(_u4,_u3);});};}else{return new F(function(){return _tL((_tK-65|0)+10|0);});}}}else{if(_tK>102){if(65>_tK){var _u5=new T(function(){return B(A1(_tG,_4));});return function(_u6){return new F(function(){return A1(_u6,_u5);});};}else{if(_tK>70){var _u7=new T(function(){return B(A1(_tG,_4));});return function(_u8){return new F(function(){return A1(_u8,_u7);});};}else{return new F(function(){return _tL((_tK-65|0)+10|0);});}}}else{return new F(function(){return _tL((_tK-97|0)+10|0);});}}}else{if(_tK>57){if(97>_tK){if(65>_tK){var _u9=new T(function(){return B(A1(_tG,_4));});return function(_ua){return new F(function(){return A1(_ua,_u9);});};}else{if(_tK>70){var _ub=new T(function(){return B(A1(_tG,_4));});return function(_uc){return new F(function(){return A1(_uc,_ub);});};}else{return new F(function(){return _tL((_tK-65|0)+10|0);});}}}else{if(_tK>102){if(65>_tK){var _ud=new T(function(){return B(A1(_tG,_4));});return function(_ue){return new F(function(){return A1(_ue,_ud);});};}else{if(_tK>70){var _uf=new T(function(){return B(A1(_tG,_4));});return function(_ug){return new F(function(){return A1(_ug,_uf);});};}else{return new F(function(){return _tL((_tK-65|0)+10|0);});}}}else{return new F(function(){return _tL((_tK-97|0)+10|0);});}}}else{return new F(function(){return _tL(_tK-48|0);});}}break;default:return E(_tA);}}},_uh=function(_ui){var _uj=E(_ui);if(!_uj._){return new T0(2);}else{return new F(function(){return A1(_tD,_uj);});}};return function(_uk){return new F(function(){return A3(_tE,_uk,_2j,_uh);});};},_ul=16,_um=8,_un=function(_uo){var _up=function(_uq){return new F(function(){return A1(_uo,new T1(5,new T2(0,_um,_uq)));});},_ur=function(_us){return new F(function(){return A1(_uo,new T1(5,new T2(0,_ul,_us)));});},_ut=function(_uu){switch(E(_uu)){case 79:return new T1(1,B(_tB(_um,_up)));case 88:return new T1(1,B(_tB(_ul,_ur)));case 111:return new T1(1,B(_tB(_um,_up)));case 120:return new T1(1,B(_tB(_ul,_ur)));default:return new T0(2);}};return function(_uv){return (E(_uv)==48)?E(new T1(0,_ut)):new T0(2);};},_uw=function(_ux){return new T1(0,B(_un(_ux)));},_uy=function(_uz){return new F(function(){return A1(_uz,_4l);});},_uA=function(_uB){return new F(function(){return A1(_uB,_4l);});},_uC=10,_uD=new T1(0,1),_uE=new T1(0,2147483647),_uF=function(_uG,_uH){while(1){var _uI=E(_uG);if(!_uI._){var _uJ=_uI.a,_uK=E(_uH);if(!_uK._){var _uL=_uK.a,_uM=addC(_uJ,_uL);if(!E(_uM.b)){return new T1(0,_uM.a);}else{_uG=new T1(1,I_fromInt(_uJ));_uH=new T1(1,I_fromInt(_uL));continue;}}else{_uG=new T1(1,I_fromInt(_uJ));_uH=_uK;continue;}}else{var _uN=E(_uH);if(!_uN._){_uG=_uI;_uH=new T1(1,I_fromInt(_uN.a));continue;}else{return new T1(1,I_add(_uI.a,_uN.a));}}}},_uO=new T(function(){return B(_uF(_uE,_uD));}),_uP=function(_uQ){var _uR=E(_uQ);if(!_uR._){var _uS=E(_uR.a);return (_uS==(-2147483648))?E(_uO):new T1(0, -_uS);}else{return new T1(1,I_negate(_uR.a));}},_uT=new T1(0,10),_uU=function(_uV,_uW){while(1){var _uX=E(_uV);if(!_uX._){return E(_uW);}else{var _uY=_uW+1|0;_uV=_uX.b;_uW=_uY;continue;}}},_uZ=function(_v0){return new F(function(){return _oz(E(_v0));});},_v1=new T(function(){return B(unCStr("this should not happen"));}),_v2=new T(function(){return B(err(_v1));}),_v3=function(_v4,_v5){var _v6=E(_v5);if(!_v6._){return __Z;}else{var _v7=E(_v6.b);return (_v7._==0)?E(_v2):new T2(1,B(_uF(B(_pg(_v6.a,_v4)),_v7.a)),new T(function(){return B(_v3(_v4,_v7.b));}));}},_v8=new T1(0,0),_v9=function(_va,_vb,_vc){while(1){var _vd=B((function(_ve,_vf,_vg){var _vh=E(_vg);if(!_vh._){return E(_v8);}else{if(!E(_vh.b)._){return E(_vh.a);}else{var _vi=E(_vf);if(_vi<=40){var _vj=function(_vk,_vl){while(1){var _vm=E(_vl);if(!_vm._){return E(_vk);}else{var _vn=B(_uF(B(_pg(_vk,_ve)),_vm.a));_vk=_vn;_vl=_vm.b;continue;}}};return new F(function(){return _vj(_v8,_vh);});}else{var _vo=B(_pg(_ve,_ve));if(!(_vi%2)){var _vp=B(_v3(_ve,_vh));_va=_vo;_vb=quot(_vi+1|0,2);_vc=_vp;return __continue;}else{var _vp=B(_v3(_ve,new T2(1,_v8,_vh)));_va=_vo;_vb=quot(_vi+1|0,2);_vc=_vp;return __continue;}}}}})(_va,_vb,_vc));if(_vd!=__continue){return _vd;}}},_vq=function(_vr,_vs){return new F(function(){return _v9(_vr,new T(function(){return B(_uU(_vs,0));},1),B(_G(_uZ,_vs)));});},_vt=function(_vu){var _vv=new T(function(){var _vw=new T(function(){var _vx=function(_vy){return new F(function(){return A1(_vu,new T1(1,new T(function(){return B(_vq(_uT,_vy));})));});};return new T1(1,B(_tB(_uC,_vx)));}),_vz=function(_vA){if(E(_vA)==43){var _vB=function(_vC){return new F(function(){return A1(_vu,new T1(1,new T(function(){return B(_vq(_uT,_vC));})));});};return new T1(1,B(_tB(_uC,_vB)));}else{return new T0(2);}},_vD=function(_vE){if(E(_vE)==45){var _vF=function(_vG){return new F(function(){return A1(_vu,new T1(1,new T(function(){return B(_uP(B(_vq(_uT,_vG))));})));});};return new T1(1,B(_tB(_uC,_vF)));}else{return new T0(2);}};return B(_rB(B(_rB(new T1(0,_vD),new T1(0,_vz))),_vw));});return new F(function(){return _rB(new T1(0,function(_vH){return (E(_vH)==101)?E(_vv):new T0(2);}),new T1(0,function(_vI){return (E(_vI)==69)?E(_vv):new T0(2);}));});},_vJ=function(_vK){var _vL=function(_vM){return new F(function(){return A1(_vK,new T1(1,_vM));});};return function(_vN){return (E(_vN)==46)?new T1(1,B(_tB(_uC,_vL))):new T0(2);};},_vO=function(_vP){return new T1(0,B(_vJ(_vP)));},_vQ=function(_vR){var _vS=function(_vT){var _vU=function(_vV){return new T1(1,B(_sU(_vt,_uy,function(_vW){return new F(function(){return A1(_vR,new T1(5,new T3(1,_vT,_vV,_vW)));});})));};return new T1(1,B(_sU(_vO,_uA,_vU)));};return new F(function(){return _tB(_uC,_vS);});},_vX=function(_vY){return new T1(1,B(_vQ(_vY)));},_vZ=function(_w0,_w1,_w2){while(1){var _w3=E(_w2);if(!_w3._){return false;}else{if(!B(A3(_pM,_w0,_w1,_w3.a))){_w2=_w3.b;continue;}else{return true;}}}},_w4=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_w5=function(_w6){return new F(function(){return _vZ(_sq,_w6,_w4);});},_w7=false,_w8=true,_w9=function(_wa){var _wb=new T(function(){return B(A1(_wa,_um));}),_wc=new T(function(){return B(A1(_wa,_ul));});return function(_wd){switch(E(_wd)){case 79:return E(_wb);case 88:return E(_wc);case 111:return E(_wb);case 120:return E(_wc);default:return new T0(2);}};},_we=function(_wf){return new T1(0,B(_w9(_wf)));},_wg=function(_wh){return new F(function(){return A1(_wh,_uC);});},_wi=function(_wj,_wk){var _wl=E(_wj);if(!_wl._){var _wm=_wl.a,_wn=E(_wk);return (_wn._==0)?_wm<=_wn.a:I_compareInt(_wn.a,_wm)>=0;}else{var _wo=_wl.a,_wp=E(_wk);return (_wp._==0)?I_compareInt(_wo,_wp.a)<=0:I_compare(_wo,_wp.a)<=0;}},_wq=function(_wr){return new T0(2);},_ws=function(_wt){var _wu=E(_wt);if(!_wu._){return E(_wq);}else{var _wv=_wu.a,_ww=E(_wu.b);if(!_ww._){return E(_wv);}else{var _wx=new T(function(){return B(_ws(_ww));}),_wy=function(_wz){return new F(function(){return _rB(B(A1(_wv,_wz)),new T(function(){return B(A1(_wx,_wz));}));});};return E(_wy);}}},_wA=function(_wB,_wC){var _wD=function(_wE,_wF,_wG){var _wH=E(_wE);if(!_wH._){return new F(function(){return A1(_wG,_wB);});}else{var _wI=E(_wF);if(!_wI._){return new T0(2);}else{if(E(_wH.a)!=E(_wI.a)){return new T0(2);}else{var _wJ=new T(function(){return B(_wD(_wH.b,_wI.b,_wG));});return new T1(0,function(_wK){return E(_wJ);});}}}};return function(_wL){return new F(function(){return _wD(_wB,_wL,_wC);});};},_wM=new T(function(){return B(unCStr("SO"));}),_wN=14,_wO=function(_wP){var _wQ=new T(function(){return B(A1(_wP,_wN));});return new T1(1,B(_wA(_wM,function(_wR){return E(_wQ);})));},_wS=new T(function(){return B(unCStr("SOH"));}),_wT=1,_wU=function(_wV){var _wW=new T(function(){return B(A1(_wV,_wT));});return new T1(1,B(_wA(_wS,function(_wX){return E(_wW);})));},_wY=function(_wZ){return new T1(1,B(_sU(_wU,_wO,_wZ)));},_x0=new T(function(){return B(unCStr("NUL"));}),_x1=0,_x2=function(_x3){var _x4=new T(function(){return B(A1(_x3,_x1));});return new T1(1,B(_wA(_x0,function(_x5){return E(_x4);})));},_x6=new T(function(){return B(unCStr("STX"));}),_x7=2,_x8=function(_x9){var _xa=new T(function(){return B(A1(_x9,_x7));});return new T1(1,B(_wA(_x6,function(_xb){return E(_xa);})));},_xc=new T(function(){return B(unCStr("ETX"));}),_xd=3,_xe=function(_xf){var _xg=new T(function(){return B(A1(_xf,_xd));});return new T1(1,B(_wA(_xc,function(_xh){return E(_xg);})));},_xi=new T(function(){return B(unCStr("EOT"));}),_xj=4,_xk=function(_xl){var _xm=new T(function(){return B(A1(_xl,_xj));});return new T1(1,B(_wA(_xi,function(_xn){return E(_xm);})));},_xo=new T(function(){return B(unCStr("ENQ"));}),_xp=5,_xq=function(_xr){var _xs=new T(function(){return B(A1(_xr,_xp));});return new T1(1,B(_wA(_xo,function(_xt){return E(_xs);})));},_xu=new T(function(){return B(unCStr("ACK"));}),_xv=6,_xw=function(_xx){var _xy=new T(function(){return B(A1(_xx,_xv));});return new T1(1,B(_wA(_xu,function(_xz){return E(_xy);})));},_xA=new T(function(){return B(unCStr("BEL"));}),_xB=7,_xC=function(_xD){var _xE=new T(function(){return B(A1(_xD,_xB));});return new T1(1,B(_wA(_xA,function(_xF){return E(_xE);})));},_xG=new T(function(){return B(unCStr("BS"));}),_xH=8,_xI=function(_xJ){var _xK=new T(function(){return B(A1(_xJ,_xH));});return new T1(1,B(_wA(_xG,function(_xL){return E(_xK);})));},_xM=new T(function(){return B(unCStr("HT"));}),_xN=9,_xO=function(_xP){var _xQ=new T(function(){return B(A1(_xP,_xN));});return new T1(1,B(_wA(_xM,function(_xR){return E(_xQ);})));},_xS=new T(function(){return B(unCStr("LF"));}),_xT=10,_xU=function(_xV){var _xW=new T(function(){return B(A1(_xV,_xT));});return new T1(1,B(_wA(_xS,function(_xX){return E(_xW);})));},_xY=new T(function(){return B(unCStr("VT"));}),_xZ=11,_y0=function(_y1){var _y2=new T(function(){return B(A1(_y1,_xZ));});return new T1(1,B(_wA(_xY,function(_y3){return E(_y2);})));},_y4=new T(function(){return B(unCStr("FF"));}),_y5=12,_y6=function(_y7){var _y8=new T(function(){return B(A1(_y7,_y5));});return new T1(1,B(_wA(_y4,function(_y9){return E(_y8);})));},_ya=new T(function(){return B(unCStr("CR"));}),_yb=13,_yc=function(_yd){var _ye=new T(function(){return B(A1(_yd,_yb));});return new T1(1,B(_wA(_ya,function(_yf){return E(_ye);})));},_yg=new T(function(){return B(unCStr("SI"));}),_yh=15,_yi=function(_yj){var _yk=new T(function(){return B(A1(_yj,_yh));});return new T1(1,B(_wA(_yg,function(_yl){return E(_yk);})));},_ym=new T(function(){return B(unCStr("DLE"));}),_yn=16,_yo=function(_yp){var _yq=new T(function(){return B(A1(_yp,_yn));});return new T1(1,B(_wA(_ym,function(_yr){return E(_yq);})));},_ys=new T(function(){return B(unCStr("DC1"));}),_yt=17,_yu=function(_yv){var _yw=new T(function(){return B(A1(_yv,_yt));});return new T1(1,B(_wA(_ys,function(_yx){return E(_yw);})));},_yy=new T(function(){return B(unCStr("DC2"));}),_yz=18,_yA=function(_yB){var _yC=new T(function(){return B(A1(_yB,_yz));});return new T1(1,B(_wA(_yy,function(_yD){return E(_yC);})));},_yE=new T(function(){return B(unCStr("DC3"));}),_yF=19,_yG=function(_yH){var _yI=new T(function(){return B(A1(_yH,_yF));});return new T1(1,B(_wA(_yE,function(_yJ){return E(_yI);})));},_yK=new T(function(){return B(unCStr("DC4"));}),_yL=20,_yM=function(_yN){var _yO=new T(function(){return B(A1(_yN,_yL));});return new T1(1,B(_wA(_yK,function(_yP){return E(_yO);})));},_yQ=new T(function(){return B(unCStr("NAK"));}),_yR=21,_yS=function(_yT){var _yU=new T(function(){return B(A1(_yT,_yR));});return new T1(1,B(_wA(_yQ,function(_yV){return E(_yU);})));},_yW=new T(function(){return B(unCStr("SYN"));}),_yX=22,_yY=function(_yZ){var _z0=new T(function(){return B(A1(_yZ,_yX));});return new T1(1,B(_wA(_yW,function(_z1){return E(_z0);})));},_z2=new T(function(){return B(unCStr("ETB"));}),_z3=23,_z4=function(_z5){var _z6=new T(function(){return B(A1(_z5,_z3));});return new T1(1,B(_wA(_z2,function(_z7){return E(_z6);})));},_z8=new T(function(){return B(unCStr("CAN"));}),_z9=24,_za=function(_zb){var _zc=new T(function(){return B(A1(_zb,_z9));});return new T1(1,B(_wA(_z8,function(_zd){return E(_zc);})));},_ze=new T(function(){return B(unCStr("EM"));}),_zf=25,_zg=function(_zh){var _zi=new T(function(){return B(A1(_zh,_zf));});return new T1(1,B(_wA(_ze,function(_zj){return E(_zi);})));},_zk=new T(function(){return B(unCStr("SUB"));}),_zl=26,_zm=function(_zn){var _zo=new T(function(){return B(A1(_zn,_zl));});return new T1(1,B(_wA(_zk,function(_zp){return E(_zo);})));},_zq=new T(function(){return B(unCStr("ESC"));}),_zr=27,_zs=function(_zt){var _zu=new T(function(){return B(A1(_zt,_zr));});return new T1(1,B(_wA(_zq,function(_zv){return E(_zu);})));},_zw=new T(function(){return B(unCStr("FS"));}),_zx=28,_zy=function(_zz){var _zA=new T(function(){return B(A1(_zz,_zx));});return new T1(1,B(_wA(_zw,function(_zB){return E(_zA);})));},_zC=new T(function(){return B(unCStr("GS"));}),_zD=29,_zE=function(_zF){var _zG=new T(function(){return B(A1(_zF,_zD));});return new T1(1,B(_wA(_zC,function(_zH){return E(_zG);})));},_zI=new T(function(){return B(unCStr("RS"));}),_zJ=30,_zK=function(_zL){var _zM=new T(function(){return B(A1(_zL,_zJ));});return new T1(1,B(_wA(_zI,function(_zN){return E(_zM);})));},_zO=new T(function(){return B(unCStr("US"));}),_zP=31,_zQ=function(_zR){var _zS=new T(function(){return B(A1(_zR,_zP));});return new T1(1,B(_wA(_zO,function(_zT){return E(_zS);})));},_zU=new T(function(){return B(unCStr("SP"));}),_zV=32,_zW=function(_zX){var _zY=new T(function(){return B(A1(_zX,_zV));});return new T1(1,B(_wA(_zU,function(_zZ){return E(_zY);})));},_A0=new T(function(){return B(unCStr("DEL"));}),_A1=127,_A2=function(_A3){var _A4=new T(function(){return B(A1(_A3,_A1));});return new T1(1,B(_wA(_A0,function(_A5){return E(_A4);})));},_A6=new T2(1,_A2,_4),_A7=new T2(1,_zW,_A6),_A8=new T2(1,_zQ,_A7),_A9=new T2(1,_zK,_A8),_Aa=new T2(1,_zE,_A9),_Ab=new T2(1,_zy,_Aa),_Ac=new T2(1,_zs,_Ab),_Ad=new T2(1,_zm,_Ac),_Ae=new T2(1,_zg,_Ad),_Af=new T2(1,_za,_Ae),_Ag=new T2(1,_z4,_Af),_Ah=new T2(1,_yY,_Ag),_Ai=new T2(1,_yS,_Ah),_Aj=new T2(1,_yM,_Ai),_Ak=new T2(1,_yG,_Aj),_Al=new T2(1,_yA,_Ak),_Am=new T2(1,_yu,_Al),_An=new T2(1,_yo,_Am),_Ao=new T2(1,_yi,_An),_Ap=new T2(1,_yc,_Ao),_Aq=new T2(1,_y6,_Ap),_Ar=new T2(1,_y0,_Aq),_As=new T2(1,_xU,_Ar),_At=new T2(1,_xO,_As),_Au=new T2(1,_xI,_At),_Av=new T2(1,_xC,_Au),_Aw=new T2(1,_xw,_Av),_Ax=new T2(1,_xq,_Aw),_Ay=new T2(1,_xk,_Ax),_Az=new T2(1,_xe,_Ay),_AA=new T2(1,_x8,_Az),_AB=new T2(1,_x2,_AA),_AC=new T2(1,_wY,_AB),_AD=new T(function(){return B(_ws(_AC));}),_AE=34,_AF=new T1(0,1114111),_AG=92,_AH=39,_AI=function(_AJ){var _AK=new T(function(){return B(A1(_AJ,_xB));}),_AL=new T(function(){return B(A1(_AJ,_xH));}),_AM=new T(function(){return B(A1(_AJ,_xN));}),_AN=new T(function(){return B(A1(_AJ,_xT));}),_AO=new T(function(){return B(A1(_AJ,_xZ));}),_AP=new T(function(){return B(A1(_AJ,_y5));}),_AQ=new T(function(){return B(A1(_AJ,_yb));}),_AR=new T(function(){return B(A1(_AJ,_AG));}),_AS=new T(function(){return B(A1(_AJ,_AH));}),_AT=new T(function(){return B(A1(_AJ,_AE));}),_AU=new T(function(){var _AV=function(_AW){var _AX=new T(function(){return B(_oz(E(_AW)));}),_AY=function(_AZ){var _B0=B(_vq(_AX,_AZ));if(!B(_wi(_B0,_AF))){return new T0(2);}else{return new F(function(){return A1(_AJ,new T(function(){var _B1=B(_oP(_B0));if(_B1>>>0>1114111){return B(_fK(_B1));}else{return _B1;}}));});}};return new T1(1,B(_tB(_AW,_AY)));},_B2=new T(function(){var _B3=new T(function(){return B(A1(_AJ,_zP));}),_B4=new T(function(){return B(A1(_AJ,_zJ));}),_B5=new T(function(){return B(A1(_AJ,_zD));}),_B6=new T(function(){return B(A1(_AJ,_zx));}),_B7=new T(function(){return B(A1(_AJ,_zr));}),_B8=new T(function(){return B(A1(_AJ,_zl));}),_B9=new T(function(){return B(A1(_AJ,_zf));}),_Ba=new T(function(){return B(A1(_AJ,_z9));}),_Bb=new T(function(){return B(A1(_AJ,_z3));}),_Bc=new T(function(){return B(A1(_AJ,_yX));}),_Bd=new T(function(){return B(A1(_AJ,_yR));}),_Be=new T(function(){return B(A1(_AJ,_yL));}),_Bf=new T(function(){return B(A1(_AJ,_yF));}),_Bg=new T(function(){return B(A1(_AJ,_yz));}),_Bh=new T(function(){return B(A1(_AJ,_yt));}),_Bi=new T(function(){return B(A1(_AJ,_yn));}),_Bj=new T(function(){return B(A1(_AJ,_yh));}),_Bk=new T(function(){return B(A1(_AJ,_wN));}),_Bl=new T(function(){return B(A1(_AJ,_xv));}),_Bm=new T(function(){return B(A1(_AJ,_xp));}),_Bn=new T(function(){return B(A1(_AJ,_xj));}),_Bo=new T(function(){return B(A1(_AJ,_xd));}),_Bp=new T(function(){return B(A1(_AJ,_x7));}),_Bq=new T(function(){return B(A1(_AJ,_wT));}),_Br=new T(function(){return B(A1(_AJ,_x1));}),_Bs=function(_Bt){switch(E(_Bt)){case 64:return E(_Br);case 65:return E(_Bq);case 66:return E(_Bp);case 67:return E(_Bo);case 68:return E(_Bn);case 69:return E(_Bm);case 70:return E(_Bl);case 71:return E(_AK);case 72:return E(_AL);case 73:return E(_AM);case 74:return E(_AN);case 75:return E(_AO);case 76:return E(_AP);case 77:return E(_AQ);case 78:return E(_Bk);case 79:return E(_Bj);case 80:return E(_Bi);case 81:return E(_Bh);case 82:return E(_Bg);case 83:return E(_Bf);case 84:return E(_Be);case 85:return E(_Bd);case 86:return E(_Bc);case 87:return E(_Bb);case 88:return E(_Ba);case 89:return E(_B9);case 90:return E(_B8);case 91:return E(_B7);case 92:return E(_B6);case 93:return E(_B5);case 94:return E(_B4);case 95:return E(_B3);default:return new T0(2);}};return B(_rB(new T1(0,function(_Bu){return (E(_Bu)==94)?E(new T1(0,_Bs)):new T0(2);}),new T(function(){return B(A1(_AD,_AJ));})));});return B(_rB(new T1(1,B(_sU(_we,_wg,_AV))),_B2));});return new F(function(){return _rB(new T1(0,function(_Bv){switch(E(_Bv)){case 34:return E(_AT);case 39:return E(_AS);case 92:return E(_AR);case 97:return E(_AK);case 98:return E(_AL);case 102:return E(_AP);case 110:return E(_AN);case 114:return E(_AQ);case 116:return E(_AM);case 118:return E(_AO);default:return new T0(2);}}),_AU);});},_Bw=function(_Bx){return new F(function(){return A1(_Bx,_5);});},_By=function(_Bz){var _BA=E(_Bz);if(!_BA._){return E(_Bw);}else{var _BB=E(_BA.a),_BC=_BB>>>0,_BD=new T(function(){return B(_By(_BA.b));});if(_BC>887){var _BE=u_iswspace(_BB);if(!E(_BE)){return E(_Bw);}else{var _BF=function(_BG){var _BH=new T(function(){return B(A1(_BD,_BG));});return new T1(0,function(_BI){return E(_BH);});};return E(_BF);}}else{var _BJ=E(_BC);if(_BJ==32){var _BK=function(_BL){var _BM=new T(function(){return B(A1(_BD,_BL));});return new T1(0,function(_BN){return E(_BM);});};return E(_BK);}else{if(_BJ-9>>>0>4){if(E(_BJ)==160){var _BO=function(_BP){var _BQ=new T(function(){return B(A1(_BD,_BP));});return new T1(0,function(_BR){return E(_BQ);});};return E(_BO);}else{return E(_Bw);}}else{var _BS=function(_BT){var _BU=new T(function(){return B(A1(_BD,_BT));});return new T1(0,function(_BV){return E(_BU);});};return E(_BS);}}}}},_BW=function(_BX){var _BY=new T(function(){return B(_BW(_BX));}),_BZ=function(_C0){return (E(_C0)==92)?E(_BY):new T0(2);},_C1=function(_C2){return E(new T1(0,_BZ));},_C3=new T1(1,function(_C4){return new F(function(){return A2(_By,_C4,_C1);});}),_C5=new T(function(){return B(_AI(function(_C6){return new F(function(){return A1(_BX,new T2(0,_C6,_w8));});}));}),_C7=function(_C8){var _C9=E(_C8);if(_C9==38){return E(_BY);}else{var _Ca=_C9>>>0;if(_Ca>887){var _Cb=u_iswspace(_C9);return (E(_Cb)==0)?new T0(2):E(_C3);}else{var _Cc=E(_Ca);return (_Cc==32)?E(_C3):(_Cc-9>>>0>4)?(E(_Cc)==160)?E(_C3):new T0(2):E(_C3);}}};return new F(function(){return _rB(new T1(0,function(_Cd){return (E(_Cd)==92)?E(new T1(0,_C7)):new T0(2);}),new T1(0,function(_Ce){var _Cf=E(_Ce);if(E(_Cf)==92){return E(_C5);}else{return new F(function(){return A1(_BX,new T2(0,_Cf,_w7));});}}));});},_Cg=function(_Ch,_Ci){var _Cj=new T(function(){return B(A1(_Ci,new T1(1,new T(function(){return B(A1(_Ch,_4));}))));}),_Ck=function(_Cl){var _Cm=E(_Cl),_Cn=E(_Cm.a);if(E(_Cn)==34){if(!E(_Cm.b)){return E(_Cj);}else{return new F(function(){return _Cg(function(_Co){return new F(function(){return A1(_Ch,new T2(1,_Cn,_Co));});},_Ci);});}}else{return new F(function(){return _Cg(function(_Cp){return new F(function(){return A1(_Ch,new T2(1,_Cn,_Cp));});},_Ci);});}};return new F(function(){return _BW(_Ck);});},_Cq=new T(function(){return B(unCStr("_\'"));}),_Cr=function(_Cs){var _Ct=u_iswalnum(_Cs);if(!E(_Ct)){return new F(function(){return _vZ(_sq,_Cs,_Cq);});}else{return true;}},_Cu=function(_Cv){return new F(function(){return _Cr(E(_Cv));});},_Cw=new T(function(){return B(unCStr(",;()[]{}`"));}),_Cx=new T(function(){return B(unCStr("=>"));}),_Cy=new T2(1,_Cx,_4),_Cz=new T(function(){return B(unCStr("~"));}),_CA=new T2(1,_Cz,_Cy),_CB=new T(function(){return B(unCStr("@"));}),_CC=new T2(1,_CB,_CA),_CD=new T(function(){return B(unCStr("->"));}),_CE=new T2(1,_CD,_CC),_CF=new T(function(){return B(unCStr("<-"));}),_CG=new T2(1,_CF,_CE),_CH=new T(function(){return B(unCStr("|"));}),_CI=new T2(1,_CH,_CG),_CJ=new T(function(){return B(unCStr("\\"));}),_CK=new T2(1,_CJ,_CI),_CL=new T(function(){return B(unCStr("="));}),_CM=new T2(1,_CL,_CK),_CN=new T(function(){return B(unCStr("::"));}),_CO=new T2(1,_CN,_CM),_CP=new T(function(){return B(unCStr(".."));}),_CQ=new T2(1,_CP,_CO),_CR=function(_CS){var _CT=new T(function(){return B(A1(_CS,_ty));}),_CU=new T(function(){var _CV=new T(function(){var _CW=function(_CX){var _CY=new T(function(){return B(A1(_CS,new T1(0,_CX)));});return new T1(0,function(_CZ){return (E(_CZ)==39)?E(_CY):new T0(2);});};return B(_AI(_CW));}),_D0=function(_D1){var _D2=E(_D1);switch(E(_D2)){case 39:return new T0(2);case 92:return E(_CV);default:var _D3=new T(function(){return B(A1(_CS,new T1(0,_D2)));});return new T1(0,function(_D4){return (E(_D4)==39)?E(_D3):new T0(2);});}},_D5=new T(function(){var _D6=new T(function(){return B(_Cg(_2j,_CS));}),_D7=new T(function(){var _D8=new T(function(){var _D9=new T(function(){var _Da=function(_Db){var _Dc=E(_Db),_Dd=u_iswalpha(_Dc);return (E(_Dd)==0)?(E(_Dc)==95)?new T1(1,B(_tk(_Cu,function(_De){return new F(function(){return A1(_CS,new T1(3,new T2(1,_Dc,_De)));});}))):new T0(2):new T1(1,B(_tk(_Cu,function(_Df){return new F(function(){return A1(_CS,new T1(3,new T2(1,_Dc,_Df)));});})));};return B(_rB(new T1(0,_Da),new T(function(){return new T1(1,B(_sU(_uw,_vX,_CS)));})));}),_Dg=function(_Dh){return (!B(_vZ(_sq,_Dh,_w4)))?new T0(2):new T1(1,B(_tk(_w5,function(_Di){var _Dj=new T2(1,_Dh,_Di);if(!B(_vZ(_sz,_Dj,_CQ))){return new F(function(){return A1(_CS,new T1(4,_Dj));});}else{return new F(function(){return A1(_CS,new T1(2,_Dj));});}})));};return B(_rB(new T1(0,_Dg),_D9));});return B(_rB(new T1(0,function(_Dk){if(!B(_vZ(_sq,_Dk,_Cw))){return new T0(2);}else{return new F(function(){return A1(_CS,new T1(2,new T2(1,_Dk,_4)));});}}),_D8));});return B(_rB(new T1(0,function(_Dl){return (E(_Dl)==34)?E(_D6):new T0(2);}),_D7));});return B(_rB(new T1(0,function(_Dm){return (E(_Dm)==39)?E(new T1(0,_D0)):new T0(2);}),_D5));});return new F(function(){return _rB(new T1(1,function(_Dn){return (E(_Dn)._==0)?E(_CT):new T0(2);}),_CU);});},_Do=0,_Dp=function(_Dq,_Dr){var _Ds=new T(function(){var _Dt=new T(function(){var _Du=function(_Dv){var _Dw=new T(function(){var _Dx=new T(function(){return B(A1(_Dr,_Dv));});return B(_CR(function(_Dy){var _Dz=E(_Dy);return (_Dz._==2)?(!B(_sf(_Dz.a,_se)))?new T0(2):E(_Dx):new T0(2);}));}),_DA=function(_DB){return E(_Dw);};return new T1(1,function(_DC){return new F(function(){return A2(_By,_DC,_DA);});});};return B(A2(_Dq,_Do,_Du));});return B(_CR(function(_DD){var _DE=E(_DD);return (_DE._==2)?(!B(_sf(_DE.a,_sd)))?new T0(2):E(_Dt):new T0(2);}));}),_DF=function(_DG){return E(_Ds);};return function(_DH){return new F(function(){return A2(_By,_DH,_DF);});};},_DI=function(_DJ,_DK){var _DL=function(_DM){var _DN=new T(function(){return B(A1(_DJ,_DM));}),_DO=function(_DP){return new F(function(){return _rB(B(A1(_DN,_DP)),new T(function(){return new T1(1,B(_Dp(_DL,_DP)));}));});};return E(_DO);},_DQ=new T(function(){return B(A1(_DJ,_DK));}),_DR=function(_DS){return new F(function(){return _rB(B(A1(_DQ,_DS)),new T(function(){return new T1(1,B(_Dp(_DL,_DS)));}));});};return E(_DR);},_DT=function(_DU,_DV){var _DW=function(_DX,_DY){var _DZ=function(_E0){return new F(function(){return A1(_DY,new T(function(){return  -E(_E0);}));});},_E1=new T(function(){return B(_CR(function(_E2){return new F(function(){return A3(_DU,_E2,_DX,_DZ);});}));}),_E3=function(_E4){return E(_E1);},_E5=function(_E6){return new F(function(){return A2(_By,_E6,_E3);});},_E7=new T(function(){return B(_CR(function(_E8){var _E9=E(_E8);if(_E9._==4){var _Ea=E(_E9.a);if(!_Ea._){return new F(function(){return A3(_DU,_E9,_DX,_DY);});}else{if(E(_Ea.a)==45){if(!E(_Ea.b)._){return E(new T1(1,_E5));}else{return new F(function(){return A3(_DU,_E9,_DX,_DY);});}}else{return new F(function(){return A3(_DU,_E9,_DX,_DY);});}}}else{return new F(function(){return A3(_DU,_E9,_DX,_DY);});}}));}),_Eb=function(_Ec){return E(_E7);};return new T1(1,function(_Ed){return new F(function(){return A2(_By,_Ed,_Eb);});});};return new F(function(){return _DI(_DW,_DV);});},_Ee=new T(function(){return 1/0;}),_Ef=function(_Eg,_Eh){return new F(function(){return A1(_Eh,_Ee);});},_Ei=new T(function(){return 0/0;}),_Ej=function(_Ek,_El){return new F(function(){return A1(_El,_Ei);});},_Em=new T(function(){return B(unCStr("NaN"));}),_En=new T(function(){return B(unCStr("Infinity"));}),_Eo=1024,_Ep=-1021,_Eq=function(_Er,_Es){while(1){var _Et=E(_Er);if(!_Et._){var _Eu=E(_Et.a);if(_Eu==(-2147483648)){_Er=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ev=E(_Es);if(!_Ev._){return new T1(0,_Eu%_Ev.a);}else{_Er=new T1(1,I_fromInt(_Eu));_Es=_Ev;continue;}}}else{var _Ew=_Et.a,_Ex=E(_Es);return (_Ex._==0)?new T1(1,I_rem(_Ew,I_fromInt(_Ex.a))):new T1(1,I_rem(_Ew,_Ex.a));}}},_Ey=function(_Ez,_EA){if(!B(_qE(_EA,_pO))){return new F(function(){return _Eq(_Ez,_EA);});}else{return E(_nC);}},_EB=function(_EC,_ED){while(1){if(!B(_qE(_ED,_pO))){var _EE=_ED,_EF=B(_Ey(_EC,_ED));_EC=_EE;_ED=_EF;continue;}else{return E(_EC);}}},_EG=function(_EH){var _EI=E(_EH);if(!_EI._){var _EJ=E(_EI.a);return (_EJ==(-2147483648))?E(_uO):(_EJ<0)?new T1(0, -_EJ):E(_EI);}else{var _EK=_EI.a;return (I_compareInt(_EK,0)>=0)?E(_EI):new T1(1,I_negate(_EK));}},_EL=function(_EM,_EN){while(1){var _EO=E(_EM);if(!_EO._){var _EP=E(_EO.a);if(_EP==(-2147483648)){_EM=new T1(1,I_fromInt(-2147483648));continue;}else{var _EQ=E(_EN);if(!_EQ._){return new T1(0,quot(_EP,_EQ.a));}else{_EM=new T1(1,I_fromInt(_EP));_EN=_EQ;continue;}}}else{var _ER=_EO.a,_ES=E(_EN);return (_ES._==0)?new T1(0,I_toInt(I_quot(_ER,I_fromInt(_ES.a)))):new T1(1,I_quot(_ER,_ES.a));}}},_ET=5,_EU=new T(function(){return B(_nz(_ET));}),_EV=new T(function(){return die(_EU);}),_EW=function(_EX,_EY){if(!B(_qE(_EY,_pO))){var _EZ=B(_EB(B(_EG(_EX)),B(_EG(_EY))));return (!B(_qE(_EZ,_pO)))?new T2(0,B(_EL(_EX,_EZ)),B(_EL(_EY,_EZ))):E(_nC);}else{return E(_EV);}},_F0=new T(function(){return B(_qE(_pP,_pO));}),_F1=function(_F2,_F3){while(1){var _F4=E(_F2);if(!_F4._){var _F5=_F4.a,_F6=E(_F3);if(!_F6._){var _F7=_F6.a,_F8=subC(_F5,_F7);if(!E(_F8.b)){return new T1(0,_F8.a);}else{_F2=new T1(1,I_fromInt(_F5));_F3=new T1(1,I_fromInt(_F7));continue;}}else{_F2=new T1(1,I_fromInt(_F5));_F3=_F6;continue;}}else{var _F9=E(_F3);if(!_F9._){_F2=_F4;_F3=new T1(1,I_fromInt(_F9.a));continue;}else{return new T1(1,I_sub(_F4.a,_F9.a));}}}},_Fa=function(_Fb,_Fc,_Fd){while(1){if(!E(_F0)){if(!B(_qE(B(_Eq(_Fc,_pP)),_pO))){if(!B(_qE(_Fc,_oD))){var _Fe=B(_pg(_Fb,_Fb)),_Ff=B(_EL(B(_F1(_Fc,_oD)),_pP)),_Fg=B(_pg(_Fb,_Fd));_Fb=_Fe;_Fc=_Ff;_Fd=_Fg;continue;}else{return new F(function(){return _pg(_Fb,_Fd);});}}else{var _Fe=B(_pg(_Fb,_Fb)),_Ff=B(_EL(_Fc,_pP));_Fb=_Fe;_Fc=_Ff;continue;}}else{return E(_nC);}}},_Fh=function(_Fi,_Fj){while(1){if(!E(_F0)){if(!B(_qE(B(_Eq(_Fj,_pP)),_pO))){if(!B(_qE(_Fj,_oD))){return new F(function(){return _Fa(B(_pg(_Fi,_Fi)),B(_EL(B(_F1(_Fj,_oD)),_pP)),_Fi);});}else{return E(_Fi);}}else{var _Fk=B(_pg(_Fi,_Fi)),_Fl=B(_EL(_Fj,_pP));_Fi=_Fk;_Fj=_Fl;continue;}}else{return E(_nC);}}},_Fm=function(_Fn,_Fo){var _Fp=E(_Fn);if(!_Fp._){var _Fq=_Fp.a,_Fr=E(_Fo);return (_Fr._==0)?_Fq<_Fr.a:I_compareInt(_Fr.a,_Fq)>0;}else{var _Fs=_Fp.a,_Ft=E(_Fo);return (_Ft._==0)?I_compareInt(_Fs,_Ft.a)<0:I_compare(_Fs,_Ft.a)<0;}},_Fu=function(_Fv,_Fw){if(!B(_Fm(_Fw,_pO))){if(!B(_qE(_Fw,_pO))){return new F(function(){return _Fh(_Fv,_Fw);});}else{return E(_oD);}}else{return E(_qw);}},_Fx=new T1(0,1),_Fy=new T1(0,0),_Fz=new T1(0,-1),_FA=function(_FB){var _FC=E(_FB);if(!_FC._){var _FD=_FC.a;return (_FD>=0)?(E(_FD)==0)?E(_Fy):E(_uD):E(_Fz);}else{var _FE=I_compareInt(_FC.a,0);return (_FE<=0)?(E(_FE)==0)?E(_Fy):E(_Fz):E(_uD);}},_FF=function(_FG,_FH,_FI){while(1){var _FJ=E(_FI);if(!_FJ._){if(!B(_Fm(_FG,_v8))){return new T2(0,B(_pg(_FH,B(_Fu(_uT,_FG)))),_oD);}else{var _FK=B(_Fu(_uT,B(_uP(_FG))));return new F(function(){return _EW(B(_pg(_FH,B(_FA(_FK)))),B(_EG(_FK)));});}}else{var _FL=B(_F1(_FG,_Fx)),_FM=B(_uF(B(_pg(_FH,_uT)),B(_oz(E(_FJ.a)))));_FG=_FL;_FH=_FM;_FI=_FJ.b;continue;}}},_FN=function(_FO,_FP){var _FQ=E(_FO);if(!_FQ._){var _FR=_FQ.a,_FS=E(_FP);return (_FS._==0)?_FR>=_FS.a:I_compareInt(_FS.a,_FR)<=0;}else{var _FT=_FQ.a,_FU=E(_FP);return (_FU._==0)?I_compareInt(_FT,_FU.a)>=0:I_compare(_FT,_FU.a)>=0;}},_FV=function(_FW){var _FX=E(_FW);if(!_FX._){var _FY=_FX.b;return new F(function(){return _EW(B(_pg(B(_v9(new T(function(){return B(_oz(E(_FX.a)));}),new T(function(){return B(_uU(_FY,0));},1),B(_G(_uZ,_FY)))),_Fx)),_Fx);});}else{var _FZ=_FX.a,_G0=_FX.c,_G1=E(_FX.b);if(!_G1._){var _G2=E(_G0);if(!_G2._){return new F(function(){return _EW(B(_pg(B(_vq(_uT,_FZ)),_Fx)),_Fx);});}else{var _G3=_G2.a;if(!B(_FN(_G3,_v8))){var _G4=B(_Fu(_uT,B(_uP(_G3))));return new F(function(){return _EW(B(_pg(B(_vq(_uT,_FZ)),B(_FA(_G4)))),B(_EG(_G4)));});}else{return new F(function(){return _EW(B(_pg(B(_pg(B(_vq(_uT,_FZ)),B(_Fu(_uT,_G3)))),_Fx)),_Fx);});}}}else{var _G5=_G1.a,_G6=E(_G0);if(!_G6._){return new F(function(){return _FF(_v8,B(_vq(_uT,_FZ)),_G5);});}else{return new F(function(){return _FF(_G6.a,B(_vq(_uT,_FZ)),_G5);});}}}},_G7=function(_G8,_G9){while(1){var _Ga=E(_G9);if(!_Ga._){return __Z;}else{if(!B(A1(_G8,_Ga.a))){return E(_Ga);}else{_G9=_Ga.b;continue;}}}},_Gb=function(_Gc,_Gd){var _Ge=E(_Gc);if(!_Ge._){var _Gf=_Ge.a,_Gg=E(_Gd);return (_Gg._==0)?_Gf>_Gg.a:I_compareInt(_Gg.a,_Gf)<0;}else{var _Gh=_Ge.a,_Gi=E(_Gd);return (_Gi._==0)?I_compareInt(_Gh,_Gi.a)>0:I_compare(_Gh,_Gi.a)>0;}},_Gj=0,_Gk=function(_Gl){return new F(function(){return _iV(_Gj,_Gl);});},_Gm=new T2(0,E(_v8),E(_oD)),_Gn=new T1(1,_Gm),_Go=new T1(0,-2147483648),_Gp=new T1(0,2147483647),_Gq=function(_Gr,_Gs,_Gt){var _Gu=E(_Gt);if(!_Gu._){return new T1(1,new T(function(){var _Gv=B(_FV(_Gu));return new T2(0,E(_Gv.a),E(_Gv.b));}));}else{var _Gw=E(_Gu.c);if(!_Gw._){return new T1(1,new T(function(){var _Gx=B(_FV(_Gu));return new T2(0,E(_Gx.a),E(_Gx.b));}));}else{var _Gy=_Gw.a;if(!B(_Gb(_Gy,_Gp))){if(!B(_Fm(_Gy,_Go))){var _Gz=function(_GA){var _GB=_GA+B(_oP(_Gy))|0;return (_GB<=(E(_Gs)+3|0))?(_GB>=(E(_Gr)-3|0))?new T1(1,new T(function(){var _GC=B(_FV(_Gu));return new T2(0,E(_GC.a),E(_GC.b));})):E(_Gn):__Z;},_GD=B(_G7(_Gk,_Gu.a));if(!_GD._){var _GE=E(_Gu.b);if(!_GE._){return E(_Gn);}else{var _GF=B(_6T(_Gk,_GE.a));if(!E(_GF.b)._){return E(_Gn);}else{return new F(function(){return _Gz( -B(_uU(_GF.a,0)));});}}}else{return new F(function(){return _Gz(B(_uU(_GD,0)));});}}else{return __Z;}}else{return __Z;}}}},_GG=function(_GH,_GI){return new T0(2);},_GJ=new T1(0,1),_GK=function(_GL,_GM){var _GN=E(_GL);if(!_GN._){var _GO=_GN.a,_GP=E(_GM);if(!_GP._){var _GQ=_GP.a;return (_GO!=_GQ)?(_GO>_GQ)?2:0:1;}else{var _GR=I_compareInt(_GP.a,_GO);return (_GR<=0)?(_GR>=0)?1:2:0;}}else{var _GS=_GN.a,_GT=E(_GM);if(!_GT._){var _GU=I_compareInt(_GS,_GT.a);return (_GU>=0)?(_GU<=0)?1:2:0;}else{var _GV=I_compare(_GS,_GT.a);return (_GV>=0)?(_GV<=0)?1:2:0;}}},_GW=function(_GX,_GY){while(1){var _GZ=E(_GX);if(!_GZ._){_GX=new T1(1,I_fromInt(_GZ.a));continue;}else{return new T1(1,I_shiftLeft(_GZ.a,_GY));}}},_H0=function(_H1,_H2,_H3){if(!B(_qE(_H3,_qW))){var _H4=B(_qM(_H2,_H3)),_H5=_H4.a;switch(B(_GK(B(_GW(_H4.b,1)),_H3))){case 0:return new F(function(){return _qA(_H5,_H1);});break;case 1:if(!(B(_oP(_H5))&1)){return new F(function(){return _qA(_H5,_H1);});}else{return new F(function(){return _qA(B(_uF(_H5,_GJ)),_H1);});}break;default:return new F(function(){return _qA(B(_uF(_H5,_GJ)),_H1);});}}else{return E(_nC);}},_H6=function(_H7){var _H8=function(_H9,_Ha){while(1){if(!B(_Fm(_H9,_H7))){if(!B(_Gb(_H9,_H7))){if(!B(_qE(_H9,_H7))){return new F(function(){return _7f("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_Ha);}}else{return _Ha-1|0;}}else{var _Hb=B(_GW(_H9,1)),_Hc=_Ha+1|0;_H9=_Hb;_Ha=_Hc;continue;}}};return new F(function(){return _H8(_uD,0);});},_Hd=function(_He){var _Hf=E(_He);if(!_Hf._){var _Hg=_Hf.a>>>0;if(!_Hg){return -1;}else{var _Hh=function(_Hi,_Hj){while(1){if(_Hi>=_Hg){if(_Hi<=_Hg){if(_Hi!=_Hg){return new F(function(){return _7f("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_Hj);}}else{return _Hj-1|0;}}else{var _Hk=imul(_Hi,2)>>>0,_Hl=_Hj+1|0;_Hi=_Hk;_Hj=_Hl;continue;}}};return new F(function(){return _Hh(1,0);});}}else{return new F(function(){return _H6(_Hf);});}},_Hm=function(_Hn){var _Ho=E(_Hn);if(!_Ho._){var _Hp=_Ho.a>>>0;if(!_Hp){return new T2(0,-1,0);}else{var _Hq=function(_Hr,_Hs){while(1){if(_Hr>=_Hp){if(_Hr<=_Hp){if(_Hr!=_Hp){return new F(function(){return _7f("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_Hs);}}else{return _Hs-1|0;}}else{var _Ht=imul(_Hr,2)>>>0,_Hu=_Hs+1|0;_Hr=_Ht;_Hs=_Hu;continue;}}};return new T2(0,B(_Hq(1,0)),(_Hp&_Hp-1>>>0)>>>0&4294967295);}}else{var _Hv=_Ho.a;return new T2(0,B(_Hd(_Ho)),I_compareInt(I_and(_Hv,I_sub(_Hv,I_fromInt(1))),0));}},_Hw=function(_Hx,_Hy){while(1){var _Hz=E(_Hx);if(!_Hz._){var _HA=_Hz.a,_HB=E(_Hy);if(!_HB._){return new T1(0,(_HA>>>0&_HB.a>>>0)>>>0&4294967295);}else{_Hx=new T1(1,I_fromInt(_HA));_Hy=_HB;continue;}}else{var _HC=E(_Hy);if(!_HC._){_Hx=_Hz;_Hy=new T1(1,I_fromInt(_HC.a));continue;}else{return new T1(1,I_and(_Hz.a,_HC.a));}}}},_HD=new T1(0,2),_HE=function(_HF,_HG){var _HH=E(_HF);if(!_HH._){var _HI=(_HH.a>>>0&(2<<_HG>>>0)-1>>>0)>>>0,_HJ=1<<_HG>>>0;return (_HJ<=_HI)?(_HJ>=_HI)?1:2:0;}else{var _HK=B(_Hw(_HH,B(_F1(B(_GW(_HD,_HG)),_uD)))),_HL=B(_GW(_uD,_HG));return (!B(_Gb(_HL,_HK)))?(!B(_Fm(_HL,_HK)))?1:2:0;}},_HM=function(_HN,_HO){while(1){var _HP=E(_HN);if(!_HP._){_HN=new T1(1,I_fromInt(_HP.a));continue;}else{return new T1(1,I_shiftRight(_HP.a,_HO));}}},_HQ=function(_HR,_HS,_HT,_HU){var _HV=B(_Hm(_HU)),_HW=_HV.a;if(!E(_HV.b)){var _HX=B(_Hd(_HT));if(_HX<((_HW+_HR|0)-1|0)){var _HY=_HW+(_HR-_HS|0)|0;if(_HY>0){if(_HY>_HX){if(_HY<=(_HX+1|0)){if(!E(B(_Hm(_HT)).b)){return 0;}else{return new F(function(){return _qA(_GJ,_HR-_HS|0);});}}else{return 0;}}else{var _HZ=B(_HM(_HT,_HY));switch(B(_HE(_HT,_HY-1|0))){case 0:return new F(function(){return _qA(_HZ,_HR-_HS|0);});break;case 1:if(!(B(_oP(_HZ))&1)){return new F(function(){return _qA(_HZ,_HR-_HS|0);});}else{return new F(function(){return _qA(B(_uF(_HZ,_GJ)),_HR-_HS|0);});}break;default:return new F(function(){return _qA(B(_uF(_HZ,_GJ)),_HR-_HS|0);});}}}else{return new F(function(){return _qA(_HT,(_HR-_HS|0)-_HY|0);});}}else{if(_HX>=_HS){var _I0=B(_HM(_HT,(_HX+1|0)-_HS|0));switch(B(_HE(_HT,_HX-_HS|0))){case 0:return new F(function(){return _qA(_I0,((_HX-_HW|0)+1|0)-_HS|0);});break;case 2:return new F(function(){return _qA(B(_uF(_I0,_GJ)),((_HX-_HW|0)+1|0)-_HS|0);});break;default:if(!(B(_oP(_I0))&1)){return new F(function(){return _qA(_I0,((_HX-_HW|0)+1|0)-_HS|0);});}else{return new F(function(){return _qA(B(_uF(_I0,_GJ)),((_HX-_HW|0)+1|0)-_HS|0);});}}}else{return new F(function(){return _qA(_HT, -_HW);});}}}else{var _I1=B(_Hd(_HT))-_HW|0,_I2=function(_I3){var _I4=function(_I5,_I6){if(!B(_wi(B(_GW(_I6,_HS)),_I5))){return new F(function(){return _H0(_I3-_HS|0,_I5,_I6);});}else{return new F(function(){return _H0((_I3-_HS|0)+1|0,_I5,B(_GW(_I6,1)));});}};if(_I3>=_HS){if(_I3!=_HS){return new F(function(){return _I4(_HT,new T(function(){return B(_GW(_HU,_I3-_HS|0));}));});}else{return new F(function(){return _I4(_HT,_HU);});}}else{return new F(function(){return _I4(new T(function(){return B(_GW(_HT,_HS-_I3|0));}),_HU);});}};if(_HR>_I1){return new F(function(){return _I2(_HR);});}else{return new F(function(){return _I2(_I1);});}}},_I7=new T(function(){return 0/0;}),_I8=new T(function(){return -1/0;}),_I9=new T(function(){return 1/0;}),_Ia=function(_Ib,_Ic){if(!B(_qE(_Ic,_qW))){if(!B(_qE(_Ib,_qW))){if(!B(_Fm(_Ib,_qW))){return new F(function(){return _HQ(-1021,53,_Ib,_Ic);});}else{return  -B(_HQ(-1021,53,B(_uP(_Ib)),_Ic));}}else{return E(_qV);}}else{return (!B(_qE(_Ib,_qW)))?(!B(_Fm(_Ib,_qW)))?E(_I9):E(_I8):E(_I7);}},_Id=function(_Ie){var _If=E(_Ie);switch(_If._){case 3:var _Ig=_If.a;return (!B(_sf(_Ig,_En)))?(!B(_sf(_Ig,_Em)))?E(_GG):E(_Ej):E(_Ef);case 5:var _Ih=B(_Gq(_Ep,_Eo,_If.a));if(!_Ih._){return E(_Ef);}else{var _Ii=new T(function(){var _Ij=E(_Ih.a);return B(_Ia(_Ij.a,_Ij.b));});return function(_Ik,_Il){return new F(function(){return A1(_Il,_Ii);});};}break;default:return E(_GG);}},_Im=function(_In){var _Io=function(_Ip){return E(new T2(3,_In,_sL));};return new T1(1,function(_Iq){return new F(function(){return A2(_By,_Iq,_Io);});});},_Ir=new T(function(){return B(A3(_DT,_Id,_Do,_Im));}),_Is=new T(function(){return B(_rr(_Ir,_rp));}),_It=function(_Iu){while(1){var _Iv=B((function(_Iw){var _Ix=E(_Iw);if(!_Ix._){return __Z;}else{var _Iy=_Ix.b,_Iz=E(_Ix.a);if(!E(_Iz.b)._){return new T2(1,_Iz.a,new T(function(){return B(_It(_Iy));}));}else{_Iu=_Iy;return __continue;}}})(_Iu));if(_Iv!=__continue){return _Iv;}}},_IA=new T(function(){return B(_It(_Is));}),_IB=new T(function(){return B(unCStr("Infinity"));}),_IC=new T(function(){return B(_rr(_Ir,_IB));}),_ID=new T(function(){return B(_It(_IC));}),_IE=0,_IF=function(_IG,_IH,_II){return new F(function(){return _eR(_e4,new T2(0,_IH,_II),_IG,_eW);});},_IJ=function(_IK,_IL,_IM){var _IN=(_IK+_IL|0)-1|0;if(_IK<=_IN){var _IO=function(_IP){return new T2(1,new T(function(){var _IQ=E(_IM),_IR=_IQ.c,_IS=E(_IQ.a),_IT=E(_IQ.b);if(_IS>_IP){return B(_IF(_IP,_IS,_IT));}else{if(_IP>_IT){return B(_IF(_IP,_IS,_IT));}else{var _IU=_IP-_IS|0;if(0>_IU){return B(_dN(_IU,_IR));}else{if(_IU>=_IR){return B(_dN(_IU,_IR));}else{return _IQ.d["v"]["w8"][_IU];}}}}}),new T(function(){if(_IP!=_IN){return B(_IO(_IP+1|0));}else{return __Z;}}));};return new F(function(){return _IO(_IK);});}else{return __Z;}},_IV=function(_IW){var _IX=E(_IW);return new F(function(){return _IJ(_IX.a,_IX.b,_IX.c);});},_IY=function(_IZ,_J0,_J1,_J2){var _J3=new T(function(){var _J4=E(_IZ),_J5=E(_J1),_J6=_J5.a,_J7=_J5.b,_J8=_J5.c,_J9=E(_J2);if((_J9+_J4|0)<=_J7){return new T2(0,new T(function(){var _Ja=_J7-_J9|0;if(_J4>_Ja){return new T3(0,_J6+_J9|0,_Ja,_J8);}else{return new T3(0,_J6+_J9|0,_J4,_J8);}}),_J9+_J4|0);}else{return E(_fs);}}),_Jb=new T(function(){return B(A1(_J0,new T(function(){return B(_IV(E(_J3).a));})));}),_Jc=new T(function(){var _Jd=E(_Jb),_Je=_Jd.d,_Jf=_Jd.e,_Jg=_Jd.f,_Jh=E(_Jd.c);if(!_Jh){if(!B(_qE(_Je,_rj))){var _Ji=B(_qX(_p6,Math.pow(2,E(_Jf)-1|0))),_Jj=_Ji.a;if(E(_Ji.b)>=0){return B(_qA(_Je,((1-E(_Jj)|0)-E(_Jg)|0)+1|0));}else{return B(_qA(_Je,((1-(E(_Jj)-1|0)|0)-E(_Jg)|0)+1|0));}}else{return E(_IE);}}else{var _Jk=E(_Jf);if(_Jh!=(B(_rd(_ro,_Jk))-1|0)){var _Jl=B(_qX(_p6,Math.pow(2,_Jk-1|0))),_Jm=_Jl.a;if(E(_Jl.b)>=0){var _Jn=E(_Jg);return B(_qA(B(_uF(_Je,B(_GW(_ri,_Jn)))),((_Jh+1|0)-E(_Jm)|0)-_Jn|0));}else{var _Jo=E(_Jg);return B(_qA(B(_uF(_Je,B(_GW(_ri,_Jo)))),((_Jh+1|0)-(E(_Jm)-1|0)|0)-_Jo|0));}}else{if(!B(_qE(_Je,_rj))){var _Jp=E(_IA);if(!_Jp._){return E(_rl);}else{if(!E(_Jp.b)._){return E(_Jp.a);}else{return E(_rn);}}}else{var _Jq=E(_ID);if(!_Jq._){return E(_rl);}else{if(!E(_Jq.b)._){return E(_Jq.a);}else{return E(_rn);}}}}}});return new T2(0,new T(function(){if(!E(E(_Jb).b)){return E(_Jc);}else{return  -E(_Jc);}}),new T(function(){return E(E(_J3).b);}));},_Jr=new T(function(){return B(unCStr("This file was compiled with different version of GF"));}),_Js=new T(function(){return B(err(_Jr));}),_Jt=8,_Ju={_:0,a:_mY,b:_mT,c:_mP,d:_mP,e:_mj,f:_mE,g:_iE,h:_mL},_Jv={_:0,a:_oJ,b:_iP,c:_oG,d:_oU,e:_oM,f:_oZ,g:_oS},_Jw=new T2(0,_iV,_iY),_Jx={_:0,a:_Jw,b:_jf,c:_jr,d:_jo,e:_jl,f:_ji,g:_j2,h:_j7},_Jy=new T3(0,_Jv,_Jx,_oE),_Jz={_:0,a:_Jy,b:_Ju,c:_oh,d:_ov,e:_nL,f:_od,g:_on,h:_nQ,i:_oB},_JA=new T1(0,1),_JB=function(_JC,_JD){var _JE=E(_JC);return new T2(0,_JE,new T(function(){var _JF=B(_JB(B(_uF(_JE,_JD)),_JD));return new T2(1,_JF.a,_JF.b);}));},_JG=function(_JH){var _JI=B(_JB(_JH,_JA));return new T2(1,_JI.a,_JI.b);},_JJ=function(_JK,_JL){var _JM=B(_JB(_JK,new T(function(){return B(_F1(_JL,_JK));})));return new T2(1,_JM.a,_JM.b);},_JN=new T1(0,0),_JO=function(_JP,_JQ,_JR){if(!B(_FN(_JQ,_JN))){var _JS=function(_JT){return (!B(_Fm(_JT,_JR)))?new T2(1,_JT,new T(function(){return B(_JS(B(_uF(_JT,_JQ))));})):__Z;};return new F(function(){return _JS(_JP);});}else{var _JU=function(_JV){return (!B(_Gb(_JV,_JR)))?new T2(1,_JV,new T(function(){return B(_JU(B(_uF(_JV,_JQ))));})):__Z;};return new F(function(){return _JU(_JP);});}},_JW=function(_JX,_JY,_JZ){return new F(function(){return _JO(_JX,B(_F1(_JY,_JX)),_JZ);});},_K0=function(_K1,_K2){return new F(function(){return _JO(_K1,_JA,_K2);});},_K3=function(_K4){return new F(function(){return _oP(_K4);});},_K5=function(_K6){return new F(function(){return _F1(_K6,_JA);});},_K7=function(_K8){return new F(function(){return _uF(_K8,_JA);});},_K9=function(_Ka){return new F(function(){return _oz(E(_Ka));});},_Kb={_:0,a:_K7,b:_K5,c:_K9,d:_K3,e:_JG,f:_JJ,g:_K0,h:_JW},_Kc=function(_Kd,_Ke){while(1){var _Kf=E(_Kd);if(!_Kf._){var _Kg=E(_Kf.a);if(_Kg==(-2147483648)){_Kd=new T1(1,I_fromInt(-2147483648));continue;}else{var _Kh=E(_Ke);if(!_Kh._){return new T1(0,B(_n2(_Kg,_Kh.a)));}else{_Kd=new T1(1,I_fromInt(_Kg));_Ke=_Kh;continue;}}}else{var _Ki=_Kf.a,_Kj=E(_Ke);return (_Kj._==0)?new T1(1,I_div(_Ki,I_fromInt(_Kj.a))):new T1(1,I_div(_Ki,_Kj.a));}}},_Kk=function(_Kl,_Km){if(!B(_qE(_Km,_pO))){return new F(function(){return _Kc(_Kl,_Km);});}else{return E(_nC);}},_Kn=function(_Ko,_Kp){while(1){var _Kq=E(_Ko);if(!_Kq._){var _Kr=E(_Kq.a);if(_Kr==(-2147483648)){_Ko=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ks=E(_Kp);if(!_Ks._){var _Kt=_Ks.a;return new T2(0,new T1(0,B(_n2(_Kr,_Kt))),new T1(0,B(_o6(_Kr,_Kt))));}else{_Ko=new T1(1,I_fromInt(_Kr));_Kp=_Ks;continue;}}}else{var _Ku=E(_Kp);if(!_Ku._){_Ko=_Kq;_Kp=new T1(1,I_fromInt(_Ku.a));continue;}else{var _Kv=I_divMod(_Kq.a,_Ku.a);return new T2(0,new T1(1,_Kv.a),new T1(1,_Kv.b));}}}},_Kw=function(_Kx,_Ky){if(!B(_qE(_Ky,_pO))){var _Kz=B(_Kn(_Kx,_Ky));return new T2(0,_Kz.a,_Kz.b);}else{return E(_nC);}},_KA=function(_KB,_KC){while(1){var _KD=E(_KB);if(!_KD._){var _KE=E(_KD.a);if(_KE==(-2147483648)){_KB=new T1(1,I_fromInt(-2147483648));continue;}else{var _KF=E(_KC);if(!_KF._){return new T1(0,B(_o6(_KE,_KF.a)));}else{_KB=new T1(1,I_fromInt(_KE));_KC=_KF;continue;}}}else{var _KG=_KD.a,_KH=E(_KC);return (_KH._==0)?new T1(1,I_mod(_KG,I_fromInt(_KH.a))):new T1(1,I_mod(_KG,_KH.a));}}},_KI=function(_KJ,_KK){if(!B(_qE(_KK,_pO))){return new F(function(){return _KA(_KJ,_KK);});}else{return E(_nC);}},_KL=function(_KM,_KN){if(!B(_qE(_KN,_pO))){return new F(function(){return _EL(_KM,_KN);});}else{return E(_nC);}},_KO=function(_KP,_KQ){if(!B(_qE(_KQ,_pO))){var _KR=B(_qM(_KP,_KQ));return new T2(0,_KR.a,_KR.b);}else{return E(_nC);}},_KS=function(_KT){return E(_KT);},_KU=function(_KV){return E(_KV);},_KW={_:0,a:_uF,b:_F1,c:_pg,d:_uP,e:_EG,f:_FA,g:_KU},_KX=function(_KY,_KZ){var _L0=E(_KY);if(!_L0._){var _L1=_L0.a,_L2=E(_KZ);return (_L2._==0)?_L1!=_L2.a:(I_compareInt(_L2.a,_L1)==0)?false:true;}else{var _L3=_L0.a,_L4=E(_KZ);return (_L4._==0)?(I_compareInt(_L3,_L4.a)==0)?false:true:(I_compare(_L3,_L4.a)==0)?false:true;}},_L5=new T2(0,_qE,_KX),_L6=function(_L7,_L8){return (!B(_wi(_L7,_L8)))?E(_L7):E(_L8);},_L9=function(_La,_Lb){return (!B(_wi(_La,_Lb)))?E(_Lb):E(_La);},_Lc={_:0,a:_L5,b:_GK,c:_Fm,d:_wi,e:_Gb,f:_FN,g:_L6,h:_L9},_Ld=function(_Le){return new T2(0,E(_Le),E(_oD));},_Lf=new T3(0,_KW,_Lc,_Ld),_Lg={_:0,a:_Lf,b:_Kb,c:_KL,d:_Ey,e:_Kk,f:_KI,g:_KO,h:_Kw,i:_KS},_Lh=function(_Li,_Lj){while(1){var _Lk=E(_Li);if(!_Lk._){return E(_Lj);}else{var _Ll=B(_uF(B(_GW(_Lj,8)),B(_oz(E(_Lk.a)&4294967295))));_Li=_Lk.b;_Lj=_Ll;continue;}}},_Lm=function(_Ln,_Lo,_Lp){var _Lq=imul(B(_uU(_Ln,0)),8)|0,_Lr=B(_qX(_Lg,Math.pow(2,_Lq-_Lo|0))),_Ls=_Lr.a;return (E(_Lr.b)>=0)?E(B(_HM(B(_Hw(B(_Lh(_Ln,_rj)),B(_F1(_Ls,_ri)))),_Lq-_Lp|0)).a):E(B(_HM(B(_Hw(B(_Lh(_Ln,_rj)),B(_F1(B(_F1(_Ls,_ri)),_ri)))),_Lq-_Lp|0)).a);},_Lt=new T(function(){return B(unCStr("head"));}),_Lu=new T(function(){return B(_ec(_Lt));}),_Lv=function(_Lw,_Lx,_Ly){return new T1(1,B(_Lm(_Lw,E(_Lx),E(_Ly))));},_Lz=5,_LA=new T(function(){return B(unCStr("Invalid length of floating-point value"));}),_LB=new T(function(){return B(err(_LA));}),_LC=function(_LD){var _LE=new T(function(){return imul(B(_uU(_LD,0)),8)|0;}),_LF=new T(function(){var _LG=E(_LE);switch(_LG){case 16:return E(_Lz);break;case 32:return E(_Jt);break;default:if(!B(_o6(_LG,32))){var _LH=B(_qX(_Jz,4*(Math.log(_LG)/Math.log(2)))),_LI=_LH.a;if(E(_LH.b)<=0){return E(_LI)-13|0;}else{return (E(_LI)+1|0)-13|0;}}else{return E(_LB);}}}),_LJ=new T(function(){return 1+E(_LF)|0;});return new T6(0,new T(function(){return B(_uU(_LD,0));}),new T(function(){var _LK=E(_LD);if(!_LK._){return E(_Lu);}else{if((E(_LK.a)&128)>>>0==128){return 1;}else{return 0;}}}),new T(function(){return B(_oP(new T1(1,B(_Lm(_LD,1,E(_LJ))))));}),new T(function(){return B(_Lv(_LD,_LJ,_LE));}),_LF,new T(function(){return B(_iP(_LE,_LJ));}));},_LL=function(_LM){var _LN=B(_LC(_LM));return new T6(0,_LN.a,_LN.b,_LN.c,_LN.d,_LN.e,_LN.f);},_LO=function(_LP,_LQ,_LR,_LS){var _LT=B(_fc(_LP,_LQ,_LR,_LS)),_LU=_LT.b;switch(E(_LT.a)){case 0:var _LV=B(_fi(_LP,_LQ,_LR,E(_LU))),_LW=B(_gf(E(_LV.a)&4294967295,_g3,new T3(0,_LP,_LQ,_LR),_LV.b));return new T2(0,new T1(0,_LW.a),_LW.b);case 1:var _LX=B(_fi(_LP,_LQ,_LR,E(_LU)));return new T2(0,new T1(1,new T(function(){return E(_LX.a)&4294967295;})),_LX.b);case 2:var _LY=B(_IY(_Jt,_LL,new T3(0,_LP,_LQ,_LR),_LU));return new T2(0,new T1(2,_LY.a),_LY.b);default:return E(_Js);}},_LZ=function(_M0,_M1){var _M2=E(_M0),_M3=B(_LO(_M2.a,_M2.b,_M2.c,E(_M1)));return new T2(0,_M3.a,_M3.b);},_M4=function(_M5){switch(E(_M5)._){case 0:return E(_dJ);case 1:return E(_dJ);default:return E(_dJ);}},_M6=new T2(0,_M4,_LZ),_M7=function(_M8){return E(_dJ);},_M9=-4,_Ma=function(_Mb){var _Mc=E(_Mb);return (_Mc._==0)?__Z:new T2(1,new T2(0,_M9,_Mc.a),new T(function(){return B(_Ma(_Mc.b));}));},_Md=function(_Me,_Mf,_Mg,_Mh){var _Mi=B(_fi(_Me,_Mf,_Mg,_Mh)),_Mj=B(_gf(E(_Mi.a)&4294967295,_kp,new T3(0,_Me,_Mf,_Mg),_Mi.b)),_Mk=B(_fi(_Me,_Mf,_Mg,E(_Mj.b))),_Ml=new T(function(){return new T2(0,new T(function(){return B(_Ma(_Mj.a));}),E(_Mk.a)&4294967295);});return new T2(0,_Ml,_Mk.b);},_Mm=function(_Mn,_Mo){var _Mp=E(_Mn),_Mq=B(_Md(_Mp.a,_Mp.b,_Mp.c,E(_Mo)));return new T2(0,_Mq.a,_Mq.b);},_Mr=function(_Ms,_Mt,_Mu,_Mv){var _Mw=B(_fc(_Ms,_Mt,_Mu,_Mv)),_Mx=_Mw.b;switch(E(_Mw.a)){case 0:var _My=B(_fi(_Ms,_Mt,_Mu,E(_Mx))),_Mz=B(_fi(_Ms,_Mt,_Mu,E(_My.b))),_MA=B(_gf(E(_Mz.a)&4294967295,_Mm,new T3(0,_Ms,_Mt,_Mu),_Mz.b));return new T2(0,new T(function(){return new T2(0,E(_My.a)&4294967295,_MA.a);}),_MA.b);case 1:var _MB=B(_fi(_Ms,_Mt,_Mu,E(_Mx)));return new T2(0,new T(function(){return new T1(1,E(_MB.a)&4294967295);}),_MB.b);default:return E(_Js);}},_MC=function(_MD,_ME){var _MF=E(_MD),_MG=B(_Mr(_MF.a,_MF.b,_MF.c,E(_ME)));return new T2(0,_MG.a,_MG.b);},_MH=new T(function(){return B(_7f("pgf/PGF/Binary.hs:(243,3)-(244,51)|function put"));}),_MI=function(_MJ){switch(E(_MJ)._){case 0:return E(_dJ);case 1:return E(_dJ);default:return E(_MH);}},_MK=new T2(0,_MI,_MC),_ML=new T0(1),_MM=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_MN=function(_MO){return new F(function(){return err(_MM);});},_MP=new T(function(){return B(_MN(_));}),_MQ=function(_MR,_MS,_MT){var _MU=E(_MT);if(!_MU._){var _MV=_MU.a,_MW=E(_MS);if(!_MW._){var _MX=_MW.a,_MY=_MW.b;if(_MX<=(imul(3,_MV)|0)){return new T4(0,(1+_MX|0)+_MV|0,E(_MR),E(_MW),E(_MU));}else{var _MZ=E(_MW.c);if(!_MZ._){var _N0=_MZ.a,_N1=E(_MW.d);if(!_N1._){var _N2=_N1.a,_N3=_N1.b,_N4=_N1.c;if(_N2>=(imul(2,_N0)|0)){var _N5=function(_N6){var _N7=E(_N1.d);return (_N7._==0)?new T4(0,(1+_MX|0)+_MV|0,E(_N3),E(new T4(0,(1+_N0|0)+_N6|0,E(_MY),E(_MZ),E(_N4))),E(new T4(0,(1+_MV|0)+_N7.a|0,E(_MR),E(_N7),E(_MU)))):new T4(0,(1+_MX|0)+_MV|0,E(_N3),E(new T4(0,(1+_N0|0)+_N6|0,E(_MY),E(_MZ),E(_N4))),E(new T4(0,1+_MV|0,E(_MR),E(_ML),E(_MU))));},_N8=E(_N4);if(!_N8._){return new F(function(){return _N5(_N8.a);});}else{return new F(function(){return _N5(0);});}}else{return new T4(0,(1+_MX|0)+_MV|0,E(_MY),E(_MZ),E(new T4(0,(1+_MV|0)+_N2|0,E(_MR),E(_N1),E(_MU))));}}else{return E(_MP);}}else{return E(_MP);}}}else{return new T4(0,1+_MV|0,E(_MR),E(_ML),E(_MU));}}else{var _N9=E(_MS);if(!_N9._){var _Na=_N9.a,_Nb=_N9.b,_Nc=_N9.d,_Nd=E(_N9.c);if(!_Nd._){var _Ne=_Nd.a,_Nf=E(_Nc);if(!_Nf._){var _Ng=_Nf.a,_Nh=_Nf.b,_Ni=_Nf.c;if(_Ng>=(imul(2,_Ne)|0)){var _Nj=function(_Nk){var _Nl=E(_Nf.d);return (_Nl._==0)?new T4(0,1+_Na|0,E(_Nh),E(new T4(0,(1+_Ne|0)+_Nk|0,E(_Nb),E(_Nd),E(_Ni))),E(new T4(0,1+_Nl.a|0,E(_MR),E(_Nl),E(_ML)))):new T4(0,1+_Na|0,E(_Nh),E(new T4(0,(1+_Ne|0)+_Nk|0,E(_Nb),E(_Nd),E(_Ni))),E(new T4(0,1,E(_MR),E(_ML),E(_ML))));},_Nm=E(_Ni);if(!_Nm._){return new F(function(){return _Nj(_Nm.a);});}else{return new F(function(){return _Nj(0);});}}else{return new T4(0,1+_Na|0,E(_Nb),E(_Nd),E(new T4(0,1+_Ng|0,E(_MR),E(_Nf),E(_ML))));}}else{return new T4(0,3,E(_Nb),E(_Nd),E(new T4(0,1,E(_MR),E(_ML),E(_ML))));}}else{var _Nn=E(_Nc);return (_Nn._==0)?new T4(0,3,E(_Nn.b),E(new T4(0,1,E(_Nb),E(_ML),E(_ML))),E(new T4(0,1,E(_MR),E(_ML),E(_ML)))):new T4(0,2,E(_MR),E(_N9),E(_ML));}}else{return new T4(0,1,E(_MR),E(_ML),E(_ML));}}},_No=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_Np=function(_Nq){return new F(function(){return err(_No);});},_Nr=new T(function(){return B(_Np(_));}),_Ns=function(_Nt,_Nu,_Nv){var _Nw=E(_Nu);if(!_Nw._){var _Nx=_Nw.a,_Ny=E(_Nv);if(!_Ny._){var _Nz=_Ny.a,_NA=_Ny.b;if(_Nz<=(imul(3,_Nx)|0)){return new T4(0,(1+_Nx|0)+_Nz|0,E(_Nt),E(_Nw),E(_Ny));}else{var _NB=E(_Ny.c);if(!_NB._){var _NC=_NB.a,_ND=_NB.b,_NE=_NB.c,_NF=E(_Ny.d);if(!_NF._){var _NG=_NF.a;if(_NC>=(imul(2,_NG)|0)){var _NH=function(_NI){var _NJ=E(_Nt),_NK=E(_NB.d);return (_NK._==0)?new T4(0,(1+_Nx|0)+_Nz|0,E(_ND),E(new T4(0,(1+_Nx|0)+_NI|0,E(_NJ),E(_Nw),E(_NE))),E(new T4(0,(1+_NG|0)+_NK.a|0,E(_NA),E(_NK),E(_NF)))):new T4(0,(1+_Nx|0)+_Nz|0,E(_ND),E(new T4(0,(1+_Nx|0)+_NI|0,E(_NJ),E(_Nw),E(_NE))),E(new T4(0,1+_NG|0,E(_NA),E(_ML),E(_NF))));},_NL=E(_NE);if(!_NL._){return new F(function(){return _NH(_NL.a);});}else{return new F(function(){return _NH(0);});}}else{return new T4(0,(1+_Nx|0)+_Nz|0,E(_NA),E(new T4(0,(1+_Nx|0)+_NC|0,E(_Nt),E(_Nw),E(_NB))),E(_NF));}}else{return E(_Nr);}}else{return E(_Nr);}}}else{return new T4(0,1+_Nx|0,E(_Nt),E(_Nw),E(_ML));}}else{var _NM=E(_Nv);if(!_NM._){var _NN=_NM.a,_NO=_NM.b,_NP=_NM.d,_NQ=E(_NM.c);if(!_NQ._){var _NR=_NQ.a,_NS=_NQ.b,_NT=_NQ.c,_NU=E(_NP);if(!_NU._){var _NV=_NU.a;if(_NR>=(imul(2,_NV)|0)){var _NW=function(_NX){var _NY=E(_Nt),_NZ=E(_NQ.d);return (_NZ._==0)?new T4(0,1+_NN|0,E(_NS),E(new T4(0,1+_NX|0,E(_NY),E(_ML),E(_NT))),E(new T4(0,(1+_NV|0)+_NZ.a|0,E(_NO),E(_NZ),E(_NU)))):new T4(0,1+_NN|0,E(_NS),E(new T4(0,1+_NX|0,E(_NY),E(_ML),E(_NT))),E(new T4(0,1+_NV|0,E(_NO),E(_ML),E(_NU))));},_O0=E(_NT);if(!_O0._){return new F(function(){return _NW(_O0.a);});}else{return new F(function(){return _NW(0);});}}else{return new T4(0,1+_NN|0,E(_NO),E(new T4(0,1+_NR|0,E(_Nt),E(_ML),E(_NQ))),E(_NU));}}else{return new T4(0,3,E(_NS),E(new T4(0,1,E(_Nt),E(_ML),E(_ML))),E(new T4(0,1,E(_NO),E(_ML),E(_ML))));}}else{var _O1=E(_NP);return (_O1._==0)?new T4(0,3,E(_NO),E(new T4(0,1,E(_Nt),E(_ML),E(_ML))),E(_O1)):new T4(0,2,E(_Nt),E(_ML),E(_NM));}}else{return new T4(0,1,E(_Nt),E(_ML),E(_ML));}}},_O2=function(_O3){return new T4(0,1,E(_O3),E(_ML),E(_ML));},_O4=function(_O5,_O6){var _O7=E(_O6);if(!_O7._){return new F(function(){return _MQ(_O7.b,B(_O4(_O5,_O7.c)),_O7.d);});}else{return new F(function(){return _O2(_O5);});}},_O8=function(_O9,_Oa){var _Ob=E(_Oa);if(!_Ob._){return new F(function(){return _Ns(_Ob.b,_Ob.c,B(_O8(_O9,_Ob.d)));});}else{return new F(function(){return _O2(_O9);});}},_Oc=function(_Od,_Oe,_Of,_Og,_Oh){return new F(function(){return _Ns(_Of,_Og,B(_O8(_Od,_Oh)));});},_Oi=function(_Oj,_Ok,_Ol,_Om,_On){return new F(function(){return _MQ(_Ol,B(_O4(_Oj,_Om)),_On);});},_Oo=function(_Op,_Oq,_Or,_Os,_Ot,_Ou){var _Ov=E(_Oq);if(!_Ov._){var _Ow=_Ov.a,_Ox=_Ov.b,_Oy=_Ov.c,_Oz=_Ov.d;if((imul(3,_Ow)|0)>=_Or){if((imul(3,_Or)|0)>=_Ow){return new T4(0,(_Ow+_Or|0)+1|0,E(_Op),E(_Ov),E(new T4(0,_Or,E(_Os),E(_Ot),E(_Ou))));}else{return new F(function(){return _Ns(_Ox,_Oy,B(_Oo(_Op,_Oz,_Or,_Os,_Ot,_Ou)));});}}else{return new F(function(){return _MQ(_Os,B(_OA(_Op,_Ow,_Ox,_Oy,_Oz,_Ot)),_Ou);});}}else{return new F(function(){return _Oi(_Op,_Or,_Os,_Ot,_Ou);});}},_OA=function(_OB,_OC,_OD,_OE,_OF,_OG){var _OH=E(_OG);if(!_OH._){var _OI=_OH.a,_OJ=_OH.b,_OK=_OH.c,_OL=_OH.d;if((imul(3,_OC)|0)>=_OI){if((imul(3,_OI)|0)>=_OC){return new T4(0,(_OC+_OI|0)+1|0,E(_OB),E(new T4(0,_OC,E(_OD),E(_OE),E(_OF))),E(_OH));}else{return new F(function(){return _Ns(_OD,_OE,B(_Oo(_OB,_OF,_OI,_OJ,_OK,_OL)));});}}else{return new F(function(){return _MQ(_OJ,B(_OA(_OB,_OC,_OD,_OE,_OF,_OK)),_OL);});}}else{return new F(function(){return _Oc(_OB,_OC,_OD,_OE,_OF);});}},_OM=function(_ON,_OO,_OP){var _OQ=E(_OO);if(!_OQ._){var _OR=_OQ.a,_OS=_OQ.b,_OT=_OQ.c,_OU=_OQ.d,_OV=E(_OP);if(!_OV._){var _OW=_OV.a,_OX=_OV.b,_OY=_OV.c,_OZ=_OV.d;if((imul(3,_OR)|0)>=_OW){if((imul(3,_OW)|0)>=_OR){return new T4(0,(_OR+_OW|0)+1|0,E(_ON),E(_OQ),E(_OV));}else{return new F(function(){return _Ns(_OS,_OT,B(_Oo(_ON,_OU,_OW,_OX,_OY,_OZ)));});}}else{return new F(function(){return _MQ(_OX,B(_OA(_ON,_OR,_OS,_OT,_OU,_OY)),_OZ);});}}else{return new F(function(){return _Oc(_ON,_OR,_OS,_OT,_OU);});}}else{return new F(function(){return _O4(_ON,_OP);});}},_P0=function(_P1,_P2,_P3){var _P4=E(_P1);if(_P4==1){return new T2(0,new T(function(){return new T4(0,1,E(_P2),E(_ML),E(_ML));}),_P3);}else{var _P5=B(_P0(_P4>>1,_P2,_P3)),_P6=_P5.a,_P7=E(_P5.b);if(!_P7._){return new T2(0,_P6,_4);}else{var _P8=B(_P9(_P4>>1,_P7.b));return new T2(0,new T(function(){return B(_OM(_P7.a,_P6,_P8.a));}),_P8.b);}}},_P9=function(_Pa,_Pb){var _Pc=E(_Pb);if(!_Pc._){return new T2(0,_ML,_4);}else{var _Pd=_Pc.a,_Pe=_Pc.b,_Pf=E(_Pa);if(_Pf==1){return new T2(0,new T(function(){return new T4(0,1,E(_Pd),E(_ML),E(_ML));}),_Pe);}else{var _Pg=B(_P0(_Pf>>1,_Pd,_Pe)),_Ph=_Pg.a,_Pi=E(_Pg.b);if(!_Pi._){return new T2(0,_Ph,_4);}else{var _Pj=B(_P9(_Pf>>1,_Pi.b));return new T2(0,new T(function(){return B(_OM(_Pi.a,_Ph,_Pj.a));}),_Pj.b);}}}},_Pk=function(_Pl,_Pm,_Pn){while(1){var _Po=E(_Pn);if(!_Po._){return E(_Pm);}else{var _Pp=B(_P9(_Pl,_Po.b)),_Pq=_Pl<<1,_Pr=B(_OM(_Po.a,_Pm,_Pp.a));_Pl=_Pq;_Pm=_Pr;_Pn=_Pp.b;continue;}}},_Ps=function(_Pt,_Pu,_Pv,_Pw,_Px){var _Py=B(_fi(_Pu,_Pv,_Pw,_Px)),_Pz=B(_gf(E(_Py.a)&4294967295,new T(function(){return B(_jL(_Pt));}),new T3(0,_Pu,_Pv,_Pw),_Py.b));return new T2(0,new T(function(){var _PA=E(_Pz.a);if(!_PA._){return new T0(1);}else{return B(_Pk(1,new T4(0,1,E(_PA.a),E(_ML),E(_ML)),_PA.b));}}),_Pz.b);},_PB=function(_PC,_PD){var _PE=E(_PC),_PF=B(_Ps(_MK,_PE.a,_PE.b,_PE.c,E(_PD)));return new T2(0,_PF.a,_PF.b);},_PG=new T2(0,_M7,_PB),_PH=function(_PI){return E(_dJ);},_PJ=function(_PK,_PL,_PM,_PN){var _PO=B(_fi(_PK,_PL,_PM,_PN));return new F(function(){return _gf(E(_PO.a)&4294967295,_kp,new T3(0,_PK,_PL,_PM),_PO.b);});},_PP=function(_PQ,_PR){var _PS=E(_PQ),_PT=B(_PJ(_PS.a,_PS.b,_PS.c,E(_PR)));return new T2(0,_PT.a,_PT.b);},_PU=new T2(0,_PH,_PP),_PV=new T0(1),_PW=function(_PX,_PY,_PZ,_Q0,_Q1,_Q2,_Q3){while(1){var _Q4=E(_Q3);if(!_Q4._){var _Q5=(_Q1>>>0^_Q4.a>>>0)>>>0,_Q6=(_Q5|_Q5>>>1)>>>0,_Q7=(_Q6|_Q6>>>2)>>>0,_Q8=(_Q7|_Q7>>>4)>>>0,_Q9=(_Q8|_Q8>>>8)>>>0,_Qa=(_Q9|_Q9>>>16)>>>0,_Qb=(_Qa^_Qa>>>1)>>>0&4294967295;if(_Q0>>>0<=_Qb>>>0){return new F(function(){return _Qc(_PX,_PY,_PZ,new T3(0,_Q1,E(_Q2),E(_Q4)));});}else{var _Qd=_Qb>>>0,_Qe=(_Q1>>>0&((_Qd-1>>>0^4294967295)>>>0^_Qd)>>>0)>>>0&4294967295,_Qf=new T4(0,_Qe,_Qb,E(_Q4.b),E(_Q2));_Q1=_Qe;_Q2=_Qf;_Q3=_Q4.c;continue;}}else{return new F(function(){return _Qc(_PX,_PY,_PZ,new T3(0,_Q1,E(_Q2),E(_PV)));});}}},_Qg=function(_Qh,_Qi,_Qj){while(1){var _Qk=E(_Qj);if(!_Qk._){var _Ql=_Qk.a,_Qm=_Qk.b,_Qn=_Qk.c,_Qo=(_Ql>>>0^_Qh>>>0)>>>0,_Qp=(_Qo|_Qo>>>1)>>>0,_Qq=(_Qp|_Qp>>>2)>>>0,_Qr=(_Qq|_Qq>>>4)>>>0,_Qs=(_Qr|_Qr>>>8)>>>0,_Qt=(_Qs|_Qs>>>16)>>>0,_Qu=(_Qt^_Qt>>>1)>>>0&4294967295,_Qv=(_Qh>>>0^_Ql>>>0)>>>0,_Qw=(_Qv|_Qv>>>1)>>>0,_Qx=(_Qw|_Qw>>>2)>>>0,_Qy=(_Qx|_Qx>>>4)>>>0,_Qz=(_Qy|_Qy>>>8)>>>0,_QA=(_Qz|_Qz>>>16)>>>0,_QB=(_QA^_QA>>>1)>>>0;if(!((_Ql>>>0&_Qu>>>0)>>>0)){var _QC=_Qu>>>0,_QD=(_Qh>>>0&((_QB-1>>>0^4294967295)>>>0^_QB)>>>0)>>>0&4294967295,_QE=new T4(0,(_Ql>>>0&((_QC-1>>>0^4294967295)>>>0^_QC)>>>0)>>>0&4294967295,_Qu,E(_Qm),E(_Qi));_Qh=_QD;_Qi=_QE;_Qj=_Qn;continue;}else{var _QF=_Qu>>>0,_QD=(_Qh>>>0&((_QB-1>>>0^4294967295)>>>0^_QB)>>>0)>>>0&4294967295,_QE=new T4(0,(_Ql>>>0&((_QF-1>>>0^4294967295)>>>0^_QF)>>>0)>>>0&4294967295,_Qu,E(_Qi),E(_Qm));_Qh=_QD;_Qi=_QE;_Qj=_Qn;continue;}}else{return E(_Qi);}}},_Qc=function(_QG,_QH,_QI,_QJ){var _QK=E(_QI);if(!_QK._){return new F(function(){return _Qg(_QG,new T2(1,_QG,_QH),_QJ);});}else{var _QL=E(_QK.a),_QM=E(_QL.a),_QN=(_QG>>>0^_QM>>>0)>>>0,_QO=(_QN|_QN>>>1)>>>0,_QP=(_QO|_QO>>>2)>>>0,_QQ=(_QP|_QP>>>4)>>>0,_QR=(_QQ|_QQ>>>8)>>>0,_QS=(_QR|_QR>>>16)>>>0;return new F(function(){return _PW(_QM,_QL.b,_QK.b,(_QS^_QS>>>1)>>>0&4294967295,_QG,new T2(1,_QG,_QH),_QJ);});}},_QT=function(_QU,_QV,_QW,_QX,_QY){var _QZ=B(_fi(_QV,_QW,_QX,_QY)),_R0=function(_R1,_R2){var _R3=E(_R1),_R4=B(_fi(_R3.a,_R3.b,_R3.c,E(_R2))),_R5=B(A3(_jL,_QU,_R3,_R4.b));return new T2(0,new T2(0,new T(function(){return E(_R4.a)&4294967295;}),_R5.a),_R5.b);},_R6=B(_gf(E(_QZ.a)&4294967295,_R0,new T3(0,_QV,_QW,_QX),_QZ.b));return new T2(0,new T(function(){var _R7=E(_R6.a);if(!_R7._){return new T0(2);}else{var _R8=E(_R7.a);return B(_Qc(E(_R8.a),_R8.b,_R7.b,_PV));}}),_R6.b);},_R9=function(_Ra,_Rb,_Rc,_Rd){var _Re=B(A3(_jL,_Ra,_Rc,_Rd)),_Rf=B(A3(_jL,_Rb,_Rc,_Re.b));return new T2(0,new T2(0,_Re.a,_Rf.a),_Rf.b);},_Rg=new T0(1),_Rh=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_Ri=function(_Rj){return new F(function(){return err(_Rh);});},_Rk=new T(function(){return B(_Ri(_));}),_Rl=function(_Rm,_Rn,_Ro,_Rp){var _Rq=E(_Rp);if(!_Rq._){var _Rr=_Rq.a,_Rs=E(_Ro);if(!_Rs._){var _Rt=_Rs.a,_Ru=_Rs.b,_Rv=_Rs.c;if(_Rt<=(imul(3,_Rr)|0)){return new T5(0,(1+_Rt|0)+_Rr|0,E(_Rm),_Rn,E(_Rs),E(_Rq));}else{var _Rw=E(_Rs.d);if(!_Rw._){var _Rx=_Rw.a,_Ry=E(_Rs.e);if(!_Ry._){var _Rz=_Ry.a,_RA=_Ry.b,_RB=_Ry.c,_RC=_Ry.d;if(_Rz>=(imul(2,_Rx)|0)){var _RD=function(_RE){var _RF=E(_Ry.e);return (_RF._==0)?new T5(0,(1+_Rt|0)+_Rr|0,E(_RA),_RB,E(new T5(0,(1+_Rx|0)+_RE|0,E(_Ru),_Rv,E(_Rw),E(_RC))),E(new T5(0,(1+_Rr|0)+_RF.a|0,E(_Rm),_Rn,E(_RF),E(_Rq)))):new T5(0,(1+_Rt|0)+_Rr|0,E(_RA),_RB,E(new T5(0,(1+_Rx|0)+_RE|0,E(_Ru),_Rv,E(_Rw),E(_RC))),E(new T5(0,1+_Rr|0,E(_Rm),_Rn,E(_Rg),E(_Rq))));},_RG=E(_RC);if(!_RG._){return new F(function(){return _RD(_RG.a);});}else{return new F(function(){return _RD(0);});}}else{return new T5(0,(1+_Rt|0)+_Rr|0,E(_Ru),_Rv,E(_Rw),E(new T5(0,(1+_Rr|0)+_Rz|0,E(_Rm),_Rn,E(_Ry),E(_Rq))));}}else{return E(_Rk);}}else{return E(_Rk);}}}else{return new T5(0,1+_Rr|0,E(_Rm),_Rn,E(_Rg),E(_Rq));}}else{var _RH=E(_Ro);if(!_RH._){var _RI=_RH.a,_RJ=_RH.b,_RK=_RH.c,_RL=_RH.e,_RM=E(_RH.d);if(!_RM._){var _RN=_RM.a,_RO=E(_RL);if(!_RO._){var _RP=_RO.a,_RQ=_RO.b,_RR=_RO.c,_RS=_RO.d;if(_RP>=(imul(2,_RN)|0)){var _RT=function(_RU){var _RV=E(_RO.e);return (_RV._==0)?new T5(0,1+_RI|0,E(_RQ),_RR,E(new T5(0,(1+_RN|0)+_RU|0,E(_RJ),_RK,E(_RM),E(_RS))),E(new T5(0,1+_RV.a|0,E(_Rm),_Rn,E(_RV),E(_Rg)))):new T5(0,1+_RI|0,E(_RQ),_RR,E(new T5(0,(1+_RN|0)+_RU|0,E(_RJ),_RK,E(_RM),E(_RS))),E(new T5(0,1,E(_Rm),_Rn,E(_Rg),E(_Rg))));},_RW=E(_RS);if(!_RW._){return new F(function(){return _RT(_RW.a);});}else{return new F(function(){return _RT(0);});}}else{return new T5(0,1+_RI|0,E(_RJ),_RK,E(_RM),E(new T5(0,1+_RP|0,E(_Rm),_Rn,E(_RO),E(_Rg))));}}else{return new T5(0,3,E(_RJ),_RK,E(_RM),E(new T5(0,1,E(_Rm),_Rn,E(_Rg),E(_Rg))));}}else{var _RX=E(_RL);return (_RX._==0)?new T5(0,3,E(_RX.b),_RX.c,E(new T5(0,1,E(_RJ),_RK,E(_Rg),E(_Rg))),E(new T5(0,1,E(_Rm),_Rn,E(_Rg),E(_Rg)))):new T5(0,2,E(_Rm),_Rn,E(_RH),E(_Rg));}}else{return new T5(0,1,E(_Rm),_Rn,E(_Rg),E(_Rg));}}},_RY=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_RZ=function(_S0){return new F(function(){return err(_RY);});},_S1=new T(function(){return B(_RZ(_));}),_S2=function(_S3,_S4,_S5,_S6){var _S7=E(_S5);if(!_S7._){var _S8=_S7.a,_S9=E(_S6);if(!_S9._){var _Sa=_S9.a,_Sb=_S9.b,_Sc=_S9.c;if(_Sa<=(imul(3,_S8)|0)){return new T5(0,(1+_S8|0)+_Sa|0,E(_S3),_S4,E(_S7),E(_S9));}else{var _Sd=E(_S9.d);if(!_Sd._){var _Se=_Sd.a,_Sf=_Sd.b,_Sg=_Sd.c,_Sh=_Sd.d,_Si=E(_S9.e);if(!_Si._){var _Sj=_Si.a;if(_Se>=(imul(2,_Sj)|0)){var _Sk=function(_Sl){var _Sm=E(_S3),_Sn=E(_Sd.e);return (_Sn._==0)?new T5(0,(1+_S8|0)+_Sa|0,E(_Sf),_Sg,E(new T5(0,(1+_S8|0)+_Sl|0,E(_Sm),_S4,E(_S7),E(_Sh))),E(new T5(0,(1+_Sj|0)+_Sn.a|0,E(_Sb),_Sc,E(_Sn),E(_Si)))):new T5(0,(1+_S8|0)+_Sa|0,E(_Sf),_Sg,E(new T5(0,(1+_S8|0)+_Sl|0,E(_Sm),_S4,E(_S7),E(_Sh))),E(new T5(0,1+_Sj|0,E(_Sb),_Sc,E(_Rg),E(_Si))));},_So=E(_Sh);if(!_So._){return new F(function(){return _Sk(_So.a);});}else{return new F(function(){return _Sk(0);});}}else{return new T5(0,(1+_S8|0)+_Sa|0,E(_Sb),_Sc,E(new T5(0,(1+_S8|0)+_Se|0,E(_S3),_S4,E(_S7),E(_Sd))),E(_Si));}}else{return E(_S1);}}else{return E(_S1);}}}else{return new T5(0,1+_S8|0,E(_S3),_S4,E(_S7),E(_Rg));}}else{var _Sp=E(_S6);if(!_Sp._){var _Sq=_Sp.a,_Sr=_Sp.b,_Ss=_Sp.c,_St=_Sp.e,_Su=E(_Sp.d);if(!_Su._){var _Sv=_Su.a,_Sw=_Su.b,_Sx=_Su.c,_Sy=_Su.d,_Sz=E(_St);if(!_Sz._){var _SA=_Sz.a;if(_Sv>=(imul(2,_SA)|0)){var _SB=function(_SC){var _SD=E(_S3),_SE=E(_Su.e);return (_SE._==0)?new T5(0,1+_Sq|0,E(_Sw),_Sx,E(new T5(0,1+_SC|0,E(_SD),_S4,E(_Rg),E(_Sy))),E(new T5(0,(1+_SA|0)+_SE.a|0,E(_Sr),_Ss,E(_SE),E(_Sz)))):new T5(0,1+_Sq|0,E(_Sw),_Sx,E(new T5(0,1+_SC|0,E(_SD),_S4,E(_Rg),E(_Sy))),E(new T5(0,1+_SA|0,E(_Sr),_Ss,E(_Rg),E(_Sz))));},_SF=E(_Sy);if(!_SF._){return new F(function(){return _SB(_SF.a);});}else{return new F(function(){return _SB(0);});}}else{return new T5(0,1+_Sq|0,E(_Sr),_Ss,E(new T5(0,1+_Sv|0,E(_S3),_S4,E(_Rg),E(_Su))),E(_Sz));}}else{return new T5(0,3,E(_Sw),_Sx,E(new T5(0,1,E(_S3),_S4,E(_Rg),E(_Rg))),E(new T5(0,1,E(_Sr),_Ss,E(_Rg),E(_Rg))));}}else{var _SG=E(_St);return (_SG._==0)?new T5(0,3,E(_Sr),_Ss,E(new T5(0,1,E(_S3),_S4,E(_Rg),E(_Rg))),E(_SG)):new T5(0,2,E(_S3),_S4,E(_Rg),E(_Sp));}}else{return new T5(0,1,E(_S3),_S4,E(_Rg),E(_Rg));}}},_SH=function(_SI,_SJ){return new T5(0,1,E(_SI),_SJ,E(_Rg),E(_Rg));},_SK=function(_SL,_SM,_SN){var _SO=E(_SN);if(!_SO._){return new F(function(){return _S2(_SO.b,_SO.c,_SO.d,B(_SK(_SL,_SM,_SO.e)));});}else{return new F(function(){return _SH(_SL,_SM);});}},_SP=function(_SQ,_SR,_SS){var _ST=E(_SS);if(!_ST._){return new F(function(){return _Rl(_ST.b,_ST.c,B(_SP(_SQ,_SR,_ST.d)),_ST.e);});}else{return new F(function(){return _SH(_SQ,_SR);});}},_SU=function(_SV,_SW,_SX,_SY,_SZ,_T0,_T1){return new F(function(){return _Rl(_SY,_SZ,B(_SP(_SV,_SW,_T0)),_T1);});},_T2=function(_T3,_T4,_T5,_T6,_T7,_T8,_T9,_Ta){var _Tb=E(_T5);if(!_Tb._){var _Tc=_Tb.a,_Td=_Tb.b,_Te=_Tb.c,_Tf=_Tb.d,_Tg=_Tb.e;if((imul(3,_Tc)|0)>=_T6){if((imul(3,_T6)|0)>=_Tc){return new T5(0,(_Tc+_T6|0)+1|0,E(_T3),_T4,E(_Tb),E(new T5(0,_T6,E(_T7),_T8,E(_T9),E(_Ta))));}else{return new F(function(){return _S2(_Td,_Te,_Tf,B(_T2(_T3,_T4,_Tg,_T6,_T7,_T8,_T9,_Ta)));});}}else{return new F(function(){return _Rl(_T7,_T8,B(_Th(_T3,_T4,_Tc,_Td,_Te,_Tf,_Tg,_T9)),_Ta);});}}else{return new F(function(){return _SU(_T3,_T4,_T6,_T7,_T8,_T9,_Ta);});}},_Th=function(_Ti,_Tj,_Tk,_Tl,_Tm,_Tn,_To,_Tp){var _Tq=E(_Tp);if(!_Tq._){var _Tr=_Tq.a,_Ts=_Tq.b,_Tt=_Tq.c,_Tu=_Tq.d,_Tv=_Tq.e;if((imul(3,_Tk)|0)>=_Tr){if((imul(3,_Tr)|0)>=_Tk){return new T5(0,(_Tk+_Tr|0)+1|0,E(_Ti),_Tj,E(new T5(0,_Tk,E(_Tl),_Tm,E(_Tn),E(_To))),E(_Tq));}else{return new F(function(){return _S2(_Tl,_Tm,_Tn,B(_T2(_Ti,_Tj,_To,_Tr,_Ts,_Tt,_Tu,_Tv)));});}}else{return new F(function(){return _Rl(_Ts,_Tt,B(_Th(_Ti,_Tj,_Tk,_Tl,_Tm,_Tn,_To,_Tu)),_Tv);});}}else{return new F(function(){return _SK(_Ti,_Tj,new T5(0,_Tk,E(_Tl),_Tm,E(_Tn),E(_To)));});}},_Tw=function(_Tx,_Ty,_Tz,_TA){var _TB=E(_Tz);if(!_TB._){var _TC=_TB.a,_TD=_TB.b,_TE=_TB.c,_TF=_TB.d,_TG=_TB.e,_TH=E(_TA);if(!_TH._){var _TI=_TH.a,_TJ=_TH.b,_TK=_TH.c,_TL=_TH.d,_TM=_TH.e;if((imul(3,_TC)|0)>=_TI){if((imul(3,_TI)|0)>=_TC){return new T5(0,(_TC+_TI|0)+1|0,E(_Tx),_Ty,E(_TB),E(_TH));}else{return new F(function(){return _S2(_TD,_TE,_TF,B(_T2(_Tx,_Ty,_TG,_TI,_TJ,_TK,_TL,_TM)));});}}else{return new F(function(){return _Rl(_TJ,_TK,B(_Th(_Tx,_Ty,_TC,_TD,_TE,_TF,_TG,_TL)),_TM);});}}else{return new F(function(){return _SK(_Tx,_Ty,_TB);});}}else{return new F(function(){return _SP(_Tx,_Ty,_TA);});}},_TN=function(_TO,_TP,_TQ){var _TR=E(_TO);if(_TR==1){var _TS=E(_TP);return new T2(0,new T(function(){return new T5(0,1,E(_TS.a),_TS.b,E(_Rg),E(_Rg));}),_TQ);}else{var _TT=B(_TN(_TR>>1,_TP,_TQ)),_TU=_TT.a,_TV=E(_TT.b);if(!_TV._){return new T2(0,_TU,_4);}else{var _TW=E(_TV.a),_TX=B(_TY(_TR>>1,_TV.b));return new T2(0,new T(function(){return B(_Tw(_TW.a,_TW.b,_TU,_TX.a));}),_TX.b);}}},_TY=function(_TZ,_U0){var _U1=E(_U0);if(!_U1._){return new T2(0,_Rg,_4);}else{var _U2=_U1.a,_U3=_U1.b,_U4=E(_TZ);if(_U4==1){var _U5=E(_U2);return new T2(0,new T(function(){return new T5(0,1,E(_U5.a),_U5.b,E(_Rg),E(_Rg));}),_U3);}else{var _U6=B(_TN(_U4>>1,_U2,_U3)),_U7=_U6.a,_U8=E(_U6.b);if(!_U8._){return new T2(0,_U7,_4);}else{var _U9=E(_U8.a),_Ua=B(_TY(_U4>>1,_U8.b));return new T2(0,new T(function(){return B(_Tw(_U9.a,_U9.b,_U7,_Ua.a));}),_Ua.b);}}}},_Ub=function(_Uc,_Ud,_Ue){while(1){var _Uf=E(_Ue);if(!_Uf._){return E(_Ud);}else{var _Ug=E(_Uf.a),_Uh=B(_TY(_Uc,_Uf.b)),_Ui=_Uc<<1,_Uj=B(_Tw(_Ug.a,_Ug.b,_Ud,_Uh.a));_Uc=_Ui;_Ud=_Uj;_Ue=_Uh.b;continue;}}},_Uk=function(_Ul,_Um,_Un,_Uo,_Up,_Uq){var _Ur=B(_fi(_Un,_Uo,_Up,_Uq)),_Us=B(_gf(E(_Ur.a)&4294967295,function(_Ut,_Uu){return new F(function(){return _R9(_Ul,_Um,_Ut,_Uu);});},new T3(0,_Un,_Uo,_Up),_Ur.b));return new T2(0,new T(function(){var _Uv=E(_Us.a);if(!_Uv._){return new T0(1);}else{var _Uw=E(_Uv.a);return B(_Ub(1,new T5(0,1,E(_Uw.a),_Uw.b,E(_Rg),E(_Rg)),_Uv.b));}}),_Us.b);},_Ux=new T0(2),_Uy=new T0(10),_Uz=new T0(5),_UA=new T0(9),_UB=new T0(6),_UC=new T0(7),_UD=new T0(8),_UE=function(_UF,_UG){var _UH=E(_UF),_UI=B(_fi(_UH.a,_UH.b,_UH.c,E(_UG))),_UJ=B(_gf(E(_UI.a)&4294967295,_g3,_UH,_UI.b));return new T2(0,_UJ.a,_UJ.b);},_UK=function(_UL,_UM){var _UN=E(_UL),_UO=_UN.a,_UP=_UN.b,_UQ=_UN.c,_UR=B(_fi(_UO,_UP,_UQ,E(_UM))),_US=B(_gf(E(_UR.a)&4294967295,_UT,_UN,_UR.b)),_UU=B(_fi(_UO,_UP,_UQ,E(_US.b))),_UV=B(_gf(E(_UU.a)&4294967295,_UE,_UN,_UU.b));return new T2(0,new T2(0,_US.a,_UV.a),_UV.b);},_UW=function(_UX,_UY,_UZ,_V0){var _V1=B(_fc(_UX,_UY,_UZ,_V0)),_V2=_V1.b;switch(E(_V1.a)){case 0:var _V3=B(_fi(_UX,_UY,_UZ,E(_V2))),_V4=B(_fi(_UX,_UY,_UZ,E(_V3.b)));return new T2(0,new T(function(){return new T2(0,E(_V3.a)&4294967295,E(_V4.a)&4294967295);}),_V4.b);case 1:var _V5=B(_fi(_UX,_UY,_UZ,E(_V2))),_V6=B(_fi(_UX,_UY,_UZ,E(_V5.b)));return new T2(0,new T(function(){return new T2(1,E(_V5.a)&4294967295,E(_V6.a)&4294967295);}),_V6.b);case 2:var _V7=B(_fi(_UX,_UY,_UZ,E(_V2))),_V8=B(_fi(_UX,_UY,_UZ,E(_V7.b)));return new T2(0,new T(function(){return new T2(2,E(_V7.a)&4294967295,E(_V8.a)&4294967295);}),_V8.b);case 3:var _V9=B(_fi(_UX,_UY,_UZ,E(_V2))),_Va=B(_gf(E(_V9.a)&4294967295,_g3,new T3(0,_UX,_UY,_UZ),_V9.b));return new T2(0,new T1(3,_Va.a),_Va.b);case 4:var _Vb=B(_fi(_UX,_UY,_UZ,E(_V2))),_Vc=B(_gf(E(_Vb.a)&4294967295,_UT,new T3(0,_UX,_UY,_UZ),_Vb.b)),_Vd=B(_fi(_UX,_UY,_UZ,E(_Vc.b))),_Ve=B(_gf(E(_Vd.a)&4294967295,_UK,new T3(0,_UX,_UY,_UZ),_Vd.b));return new T2(0,new T2(4,_Vc.a,_Ve.a),_Ve.b);case 5:return new T2(0,_Uz,_V2);case 6:return new T2(0,_UC,_V2);case 7:return new T2(0,_UB,_V2);case 8:return new T2(0,_UD,_V2);case 9:return new T2(0,_UA,_V2);case 10:return new T2(0,_Uy,_V2);default:return E(_Js);}},_UT=function(_Vf,_Vg){var _Vh=E(_Vf),_Vi=B(_UW(_Vh.a,_Vh.b,_Vh.c,E(_Vg)));return new T2(0,_Vi.a,_Vi.b);},_Vj=new T(function(){return B(unCStr("putWord8 not implemented"));}),_Vk=new T(function(){return B(err(_Vj));}),_Vl=function(_Vm){switch(E(_Vm)._){case 0:return E(_dJ);case 1:return E(_dJ);case 2:return E(_dJ);case 3:return E(_dJ);case 4:return E(_dJ);case 5:return E(_Vk);case 6:return E(_Vk);case 7:return E(_Vk);case 8:return E(_Vk);case 9:return E(_Vk);default:return E(_Vk);}},_Vn=new T2(0,_Vl,_UT),_Vo=function(_Vp,_Vq){var _Vr=E(_Vp),_Vs=B(_jU(_Vn,_id,_Vr.a,_Vr.b,_Vr.c,E(_Vq)));return new T2(0,_Vs.a,_Vs.b);},_Vt=new T(function(){return B(unCStr("MArray: undefined array element"));}),_Vu=new T(function(){return B(err(_Vt));}),_Vv=new T(function(){return B(unCStr("Negative range size"));}),_Vw=new T(function(){return B(err(_Vv));}),_Vx=function(_Vy,_Vz,_VA,_VB){var _VC=B(_Uk(_fH,_M6,_Vy,_Vz,_VA,_VB)),_VD=B(_Uk(_fH,_gy,_Vy,_Vz,_VA,E(_VC.b))),_VE=B(_fi(_Vy,_Vz,_VA,E(_VD.b))),_VF=E(_VE.a)&4294967295,_VG=B(_jD(_VF,_Vo,new T3(0,_Vy,_Vz,_VA),_VE.b)),_VH=B(_jU(_mi,_id,_Vy,_Vz,_VA,E(_VG.b))),_VI=B(_QT(_PU,_Vy,_Vz,_VA,E(_VH.b))),_VJ=B(_QT(_PU,_Vy,_Vz,_VA,E(_VI.b))),_VK=B(_QT(_PG,_Vy,_Vz,_VA,E(_VJ.b))),_VL=B(_Uk(_fH,_ko,_Vy,_Vz,_VA,E(_VK.b))),_VM=B(_fi(_Vy,_Vz,_VA,E(_VL.b))),_VN=new T(function(){var _VO=new T(function(){var _VP=function(_){var _VQ=_VF-1|0,_VR=function(_VS){if(_VS>=0){var _VT=newArr(_VS,_Vu),_VU=_VT,_VV=function(_VW){var _VX=function(_VY,_VZ,_){while(1){if(_VY!=_VW){var _W0=E(_VZ);if(!_W0._){return _5;}else{var _=_VU[_VY]=_W0.a,_W1=_VY+1|0;_VY=_W1;_VZ=_W0.b;continue;}}else{return _5;}}},_W2=B(_VX(0,_VG.a,_));return new T4(0,E(_ig),E(_VQ),_VS,_VU);};if(0>_VQ){return new F(function(){return _VV(0);});}else{var _W3=_VQ+1|0;if(_W3>=0){return new F(function(){return _VV(_W3);});}else{return E(_if);}}}else{return E(_Vw);}};if(0>_VQ){return new F(function(){return _VR(0);});}else{return new F(function(){return _VR(_VQ+1|0);});}};return B(_8O(_VP));});return {_:0,a:_VC.a,b:_VD.a,c:_VH.a,d:_VI.a,e:_VJ.a,f:_VO,g:_VK.a,h:_Ux,i:_Rg,j:_VL.a,k:_Ux,l:E(_VM.a)&4294967295};});return new T2(0,_VN,_VM.b);},_W4=function(_W5,_W6){var _W7=E(_W5),_W8=B(_Vx(_W7.a,_W7.b,_W7.c,E(_W6)));return new T2(0,_W8.a,_W8.b);},_W9=function(_Wa){return E(_dJ);},_Wb=new T2(0,_W9,_W4),_Wc=new T2(1,_bX,_4),_Wd=function(_We,_Wf){var _Wg=new T(function(){return B(A3(_eg,_e6,new T2(1,function(_Wh){return new F(function(){return _bZ(0,_Wf&4294967295,_Wh);});},new T2(1,function(_Wi){return new F(function(){return _bZ(0,E(_We)&4294967295,_Wi);});},_4)),_Wc));});return new F(function(){return err(B(unAppCStr("Unsupported PGF version ",new T2(1,_bY,_Wg))));});},_Wj=function(_Wk,_Wl){var _Wm=new T(function(){var _Wn=E(_Wk),_Wo=B(_fc(_Wn.a,_Wn.b,_Wn.c,E(_Wl)));return new T2(0,_Wo.a,_Wo.b);}),_Wp=new T(function(){var _Wq=E(_Wk),_Wr=B(_fc(_Wq.a,_Wq.b,_Wq.c,E(E(_Wm).b)));return new T2(0,_Wr.a,_Wr.b);});return new T2(0,new T(function(){return (E(E(_Wm).a)<<8>>>0&65535|E(E(_Wp).a))>>>0;}),new T(function(){return E(E(_Wp).b);}));},_Ws=function(_Wt){var _Wu=E(_Wt);return new T4(0,_Wu.a,_Wu.b,new T(function(){var _Wv=E(_Wu.c);if(!_Wv._){return __Z;}else{return new T1(1,new T2(0,_Wv.a,_4));}}),_Wu.d);},_Ww=function(_Wx){return E(_dJ);},_Wy=0,_Wz=1,_WA=function(_WB,_WC,_WD,_WE){var _WF=B(_fc(_WB,_WC,_WD,_WE)),_WG=_WF.b;switch(E(_WF.a)){case 0:var _WH=B(_fc(_WB,_WC,_WD,E(_WG))),_WI=_WH.b;switch(E(_WH.a)){case 0:var _WJ=B(_ft(_WB,_WC,_WD,E(_WI))),_WK=B(_WA(_WB,_WC,_WD,E(_WJ.b)));return new T2(0,new T3(0,_Wy,_WJ.a,_WK.a),_WK.b);case 1:var _WL=B(_ft(_WB,_WC,_WD,E(_WI))),_WM=B(_WA(_WB,_WC,_WD,E(_WL.b)));return new T2(0,new T3(0,_Wz,_WL.a,_WM.a),_WM.b);default:return E(_Js);}break;case 1:var _WN=B(_WA(_WB,_WC,_WD,E(_WG))),_WO=B(_WA(_WB,_WC,_WD,E(_WN.b)));return new T2(0,new T2(1,_WN.a,_WO.a),_WO.b);case 2:var _WP=B(_LO(_WB,_WC,_WD,E(_WG)));return new T2(0,new T1(2,_WP.a),_WP.b);case 3:var _WQ=B(_fi(_WB,_WC,_WD,E(_WG)));return new T2(0,new T(function(){return new T1(3,E(_WQ.a)&4294967295);}),_WQ.b);case 4:var _WR=B(_ft(_WB,_WC,_WD,E(_WG)));return new T2(0,new T1(4,_WR.a),_WR.b);case 5:var _WS=B(_fi(_WB,_WC,_WD,E(_WG)));return new T2(0,new T(function(){return new T1(5,E(_WS.a)&4294967295);}),_WS.b);case 6:var _WT=B(_WA(_WB,_WC,_WD,E(_WG))),_WU=B(_WV(_WB,_WC,_WD,E(_WT.b)));return new T2(0,new T2(6,_WT.a,_WU.a),_WU.b);case 7:var _WW=B(_WA(_WB,_WC,_WD,E(_WG)));return new T2(0,new T1(7,_WW.a),_WW.b);default:return E(_Js);}},_WX=function(_WY,_WZ){var _X0=E(_WY),_X1=B(_WA(_X0.a,_X0.b,_X0.c,E(_WZ)));return new T2(0,_X1.a,_X1.b);},_X2=function(_X3,_X4){var _X5=E(_X3),_X6=_X5.a,_X7=_X5.b,_X8=_X5.c,_X9=B(_fc(_X6,_X7,_X8,E(_X4))),_Xa=_X9.b,_Xb=function(_Xc,_Xd){var _Xe=B(_ft(_X6,_X7,_X8,_Xd)),_Xf=B(_WV(_X6,_X7,_X8,E(_Xe.b)));return new T2(0,new T3(0,_Xc,_Xe.a,_Xf.a),_Xf.b);};switch(E(_X9.a)){case 0:var _Xg=B(_Xb(_Wy,E(_Xa)));return new T2(0,_Xg.a,_Xg.b);case 1:var _Xh=B(_Xb(_Wz,E(_Xa)));return new T2(0,_Xh.a,_Xh.b);default:return E(_Js);}},_WV=function(_Xi,_Xj,_Xk,_Xl){var _Xm=B(_fi(_Xi,_Xj,_Xk,_Xl)),_Xn=B(_gf(E(_Xm.a)&4294967295,_X2,new T3(0,_Xi,_Xj,_Xk),_Xm.b)),_Xo=B(_ft(_Xi,_Xj,_Xk,E(_Xn.b))),_Xp=B(_fi(_Xi,_Xj,_Xk,E(_Xo.b))),_Xq=B(_gf(E(_Xp.a)&4294967295,_WX,new T3(0,_Xi,_Xj,_Xk),_Xp.b));return new T2(0,new T3(0,_Xn.a,_Xo.a,_Xq.a),_Xq.b);},_Xr=function(_Xs,_Xt){var _Xu=E(_Xs),_Xv=_Xu.a,_Xw=_Xu.b,_Xx=_Xu.c,_Xy=B(_fc(_Xv,_Xw,_Xx,E(_Xt))),_Xz=_Xy.b,_XA=function(_XB,_XC){var _XD=B(_ft(_Xv,_Xw,_Xx,_XC)),_XE=B(_WV(_Xv,_Xw,_Xx,E(_XD.b)));return new T2(0,new T3(0,_XB,_XD.a,_XE.a),_XE.b);};switch(E(_Xy.a)){case 0:var _XF=B(_XA(_Wy,E(_Xz)));return new T2(0,_XF.a,_XF.b);case 1:var _XG=B(_XA(_Wz,E(_Xz)));return new T2(0,_XG.a,_XG.b);default:return E(_Js);}},_XH=function(_XI,_XJ){var _XK=B(_IY(_Jt,_LL,_XI,_XJ)),_XL=E(_XI),_XM=B(_ft(_XL.a,_XL.b,_XL.c,E(_XK.b)));return new T2(0,new T2(0,_XK.a,_XM.a),_XM.b);},_XN=function(_XO,_XP,_XQ,_XR){var _XS=B(_fi(_XO,_XP,_XQ,_XR)),_XT=B(_gf(E(_XS.a)&4294967295,_Xr,new T3(0,_XO,_XP,_XQ),_XS.b)),_XU=B(_fi(_XO,_XP,_XQ,E(_XT.b))),_XV=B(_gf(E(_XU.a)&4294967295,_XH,new T3(0,_XO,_XP,_XQ),_XU.b)),_XW=B(_IY(_Jt,_LL,new T3(0,_XO,_XP,_XQ),_XV.b));return new T2(0,new T3(0,_XT.a,_XV.a,_XW.a),_XW.b);},_XX=function(_XY,_XZ){var _Y0=E(_XY),_Y1=B(_XN(_Y0.a,_Y0.b,_Y0.c,E(_XZ)));return new T2(0,_Y1.a,_Y1.b);},_Y2=new T2(0,_Ww,_XX),_Y3=function(_Y4){return E(_dJ);},_Y5=new T0(4),_Y6=function(_Y7,_Y8,_Y9){switch(E(_Y7)){case 0:var _Ya=E(_Y8),_Yb=_Ya.a,_Yc=_Ya.b,_Yd=_Ya.c,_Ye=B(_ft(_Yb,_Yc,_Yd,E(_Y9))),_Yf=B(_fi(_Yb,_Yc,_Yd,E(_Ye.b))),_Yg=B(_gf(E(_Yf.a)&4294967295,_Yh,_Ya,_Yf.b));return new T2(0,new T2(0,_Ye.a,_Yg.a),_Yg.b);case 1:var _Yi=E(_Y8),_Yj=B(_ft(_Yi.a,_Yi.b,_Yi.c,E(_Y9)));return new T2(0,new T1(2,_Yj.a),_Yj.b);case 2:var _Yk=E(_Y8),_Yl=_Yk.a,_Ym=_Yk.b,_Yn=_Yk.c,_Yo=B(_ft(_Yl,_Ym,_Yn,E(_Y9))),_Yp=B(_fc(_Yl,_Ym,_Yn,E(_Yo.b))),_Yq=B(_Y6(E(_Yp.a),_Yk,_Yp.b));return new T2(0,new T2(3,_Yo.a,_Yq.a),_Yq.b);case 3:return new T2(0,_Y5,_Y9);case 4:var _Yr=E(_Y8),_Ys=B(_LO(_Yr.a,_Yr.b,_Yr.c,E(_Y9)));return new T2(0,new T1(1,_Ys.a),_Ys.b);case 5:var _Yt=E(_Y8),_Yu=B(_fc(_Yt.a,_Yt.b,_Yt.c,E(_Y9))),_Yv=B(_Y6(E(_Yu.a),_Yt,_Yu.b));return new T2(0,new T1(5,_Yv.a),_Yv.b);case 6:var _Yw=E(_Y8),_Yx=B(_WA(_Yw.a,_Yw.b,_Yw.c,E(_Y9)));return new T2(0,new T1(6,_Yx.a),_Yx.b);default:return E(_Js);}},_Yy=function(_Yz,_YA,_YB,_YC){var _YD=B(_fc(_Yz,_YA,_YB,_YC));return new F(function(){return _Y6(E(_YD.a),new T3(0,_Yz,_YA,_YB),_YD.b);});},_Yh=function(_YE,_YF){var _YG=E(_YE),_YH=B(_Yy(_YG.a,_YG.b,_YG.c,E(_YF)));return new T2(0,_YH.a,_YH.b);},_YI=function(_YJ,_YK,_YL,_YM){var _YN=B(_fi(_YJ,_YK,_YL,_YM)),_YO=B(_gf(E(_YN.a)&4294967295,_Yh,new T3(0,_YJ,_YK,_YL),_YN.b)),_YP=B(_WA(_YJ,_YK,_YL,E(_YO.b)));return new T2(0,new T2(0,_YO.a,_YP.a),_YP.b);},_YQ=function(_YR,_YS){var _YT=E(_YR),_YU=B(_YI(_YT.a,_YT.b,_YT.c,E(_YS)));return new T2(0,_YU.a,_YU.b);},_YV=function(_YW,_YX,_YY,_YZ){var _Z0=B(_WV(_YW,_YX,_YY,_YZ)),_Z1=_Z0.a,_Z2=B(_fi(_YW,_YX,_YY,E(_Z0.b))),_Z3=_Z2.a,_Z4=B(_fc(_YW,_YX,_YY,E(_Z2.b))),_Z5=_Z4.b;if(!E(_Z4.a)){var _Z6=B(_IY(_Jt,_LL,new T3(0,_YW,_YX,_YY),_Z5));return new T2(0,new T4(0,_Z1,new T(function(){return E(_Z3)&4294967295;}),_4l,_Z6.a),_Z6.b);}else{var _Z7=B(_fi(_YW,_YX,_YY,E(_Z5))),_Z8=B(_gf(E(_Z7.a)&4294967295,_YQ,new T3(0,_YW,_YX,_YY),_Z7.b)),_Z9=B(_IY(_Jt,_LL,new T3(0,_YW,_YX,_YY),_Z8.b));return new T2(0,new T4(0,_Z1,new T(function(){return E(_Z3)&4294967295;}),new T1(1,_Z8.a),_Z9.a),_Z9.b);}},_Za=function(_Zb,_Zc){var _Zd=E(_Zb),_Ze=B(_YV(_Zd.a,_Zd.b,_Zd.c,E(_Zc)));return new T2(0,_Ze.a,_Ze.b);},_Zf=new T2(0,_Y3,_Za),_Zg=function(_Zh,_Zi){var _Zj=E(_Zi);return (_Zj._==0)?new T5(0,_Zj.a,E(_Zj.b),new T(function(){return B(A1(_Zh,_Zj.c));}),E(B(_Zg(_Zh,_Zj.d))),E(B(_Zg(_Zh,_Zj.e)))):new T0(1);},_Zk=function(_Zl,_Zm,_Zn,_Zo){var _Zp=B(_Uk(_fH,_M6,_Zl,_Zm,_Zn,_Zo)),_Zq=B(_Uk(_fH,_Zf,_Zl,_Zm,_Zn,E(_Zp.b))),_Zr=B(_Uk(_fH,_Y2,_Zl,_Zm,_Zn,E(_Zq.b)));return new T2(0,new T3(0,_Zp.a,new T(function(){return B(_Zg(_Ws,_Zq.a));}),_Zr.a),_Zr.b);},_Zs=function(_Zt,_Zu,_Zv){var _Zw=E(_Zt);if(!_Zw._){return new T2(0,_4,_Zv);}else{var _Zx=new T(function(){return B(A2(_Zw.a,_Zu,_Zv));}),_Zy=B(_Zs(_Zw.b,_Zu,new T(function(){return E(E(_Zx).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_Zx).a);}),_Zy.a),_Zy.b);}},_Zz=function(_ZA,_ZB,_ZC,_ZD){if(0>=_ZA){return new F(function(){return _Zs(_4,_ZC,_ZD);});}else{var _ZE=function(_ZF){var _ZG=E(_ZF);return (_ZG==1)?E(new T2(1,_ZB,_4)):new T2(1,_ZB,new T(function(){return B(_ZE(_ZG-1|0));}));};return new F(function(){return _Zs(B(_ZE(_ZA)),_ZC,_ZD);});}},_ZH=function(_ZI,_ZJ,_ZK){var _ZL=new T(function(){var _ZM=E(_ZJ),_ZN=B(_fi(_ZM.a,_ZM.b,_ZM.c,E(_ZK))),_ZO=E(_ZN.a)&4294967295,_ZP=B(_Zz(_ZO,_ZI,_ZM,_ZN.b));return new T2(0,new T2(0,_ZO,_ZP.a),_ZP.b);});return new T2(0,new T(function(){return E(E(E(_ZL).a).b);}),new T(function(){return E(E(_ZL).b);}));},_ZQ=function(_ZR,_ZS,_ZT,_ZU){var _ZV=new T(function(){var _ZW=function(_ZX,_ZY){var _ZZ=new T(function(){return B(A2(_ZR,_ZX,_ZY));}),_100=B(A2(_ZS,_ZX,new T(function(){return E(E(_ZZ).b);})));return new T2(0,new T2(0,new T(function(){return E(E(_ZZ).a);}),_100.a),_100.b);},_101=B(_ZH(_ZW,_ZT,_ZU));return new T2(0,_101.a,_101.b);});return new T2(0,new T(function(){var _102=E(E(_ZV).a);if(!_102._){return new T0(1);}else{var _103=E(_102.a);return B(_Ub(1,new T5(0,1,E(_103.a),_103.b,E(_Rg),E(_Rg)),_102.b));}}),new T(function(){return E(E(_ZV).b);}));},_104=new T(function(){return B(unCStr("Prelude.Enum.Bool.toEnum: bad argument"));}),_105=new T(function(){return B(err(_104));}),_106=new T(function(){return B(unCStr(")"));}),_107=function(_108){return new F(function(){return err(B(unAppCStr("Unable to read PGF file (",new T(function(){return B(_0(_108,_106));}))));});},_109=new T(function(){return B(unCStr("getLiteral"));}),_10a=new T(function(){return B(_107(_109));}),_10b=function(_10c,_10d,_10e,_10f){var _10g=B(_fc(_10c,_10d,_10e,_10f)),_10h=_10g.b;switch(E(_10g.a)){case 0:var _10i=B(_fi(_10c,_10d,_10e,E(_10h))),_10j=B(_gf(E(_10i.a)&4294967295,_g3,new T3(0,_10c,_10d,_10e),_10i.b));return new T2(0,new T1(0,_10j.a),_10j.b);case 1:var _10k=B(_fi(_10c,_10d,_10e,E(_10h)));return new T2(0,new T1(1,new T(function(){return E(_10k.a)&4294967295;})),_10k.b);case 2:var _10l=B(_IY(_Jt,_LL,new T3(0,_10c,_10d,_10e),_10h));return new T2(0,new T1(2,_10l.a),_10l.b);default:return E(_10a);}},_10m=new T(function(){return B(unCStr("getBindType"));}),_10n=new T(function(){return B(_107(_10m));}),_10o=new T(function(){return B(unCStr("getExpr"));}),_10p=new T(function(){return B(_107(_10o));}),_10q=function(_10r,_10s,_10t,_10u){var _10v=B(_fc(_10r,_10s,_10t,_10u)),_10w=_10v.b;switch(E(_10v.a)){case 0:var _10x=B(_fc(_10r,_10s,_10t,E(_10w))),_10y=_10x.b;switch(E(_10x.a)){case 0:var _10z=B(_ft(_10r,_10s,_10t,E(_10y))),_10A=B(_10q(_10r,_10s,_10t,E(_10z.b)));return new T2(0,new T3(0,_Wy,_10z.a,_10A.a),_10A.b);case 1:var _10B=B(_ft(_10r,_10s,_10t,E(_10y))),_10C=B(_10q(_10r,_10s,_10t,E(_10B.b)));return new T2(0,new T3(0,_Wz,_10B.a,_10C.a),_10C.b);default:return E(_10n);}break;case 1:var _10D=B(_10q(_10r,_10s,_10t,E(_10w))),_10E=B(_10q(_10r,_10s,_10t,E(_10D.b)));return new T2(0,new T2(1,_10D.a,_10E.a),_10E.b);case 2:var _10F=B(_10b(_10r,_10s,_10t,E(_10w)));return new T2(0,new T1(2,_10F.a),_10F.b);case 3:var _10G=B(_fi(_10r,_10s,_10t,E(_10w)));return new T2(0,new T(function(){return new T1(3,E(_10G.a)&4294967295);}),_10G.b);case 4:var _10H=B(_ft(_10r,_10s,_10t,E(_10w)));return new T2(0,new T1(4,_10H.a),_10H.b);case 5:var _10I=B(_fi(_10r,_10s,_10t,E(_10w)));return new T2(0,new T(function(){return new T1(5,E(_10I.a)&4294967295);}),_10I.b);case 6:var _10J=B(_10q(_10r,_10s,_10t,E(_10w))),_10K=B(_10L(_10r,_10s,_10t,_10J.b));return new T2(0,new T2(6,_10J.a,_10K.a),_10K.b);case 7:var _10M=B(_10q(_10r,_10s,_10t,E(_10w)));return new T2(0,new T1(7,_10M.a),_10M.b);default:return E(_10p);}},_10N=function(_10O,_10P){var _10Q=E(_10O),_10R=B(_10q(_10Q.a,_10Q.b,_10Q.c,E(_10P)));return new T2(0,_10R.a,_10R.b);},_10S=function(_10T,_10U,_10V,_10W){var _10X=B(_fc(_10T,_10U,_10V,_10W)),_10Y=_10X.b;switch(E(_10X.a)){case 0:var _10Z=B(_ft(_10T,_10U,_10V,E(_10Y))),_110=B(_10L(_10T,_10U,_10V,_10Z.b));return new T2(0,new T3(0,_Wy,_10Z.a,_110.a),_110.b);case 1:var _111=B(_ft(_10T,_10U,_10V,E(_10Y))),_112=B(_10L(_10T,_10U,_10V,_111.b));return new T2(0,new T3(0,_Wz,_111.a,_112.a),_112.b);default:return E(_10n);}},_113=function(_114,_115){var _116=E(_114),_117=B(_10S(_116.a,_116.b,_116.c,E(_115)));return new T2(0,_117.a,_117.b);},_10L=function(_118,_119,_11a,_11b){var _11c=new T3(0,_118,_119,_11a),_11d=B(_ZH(_113,_11c,_11b)),_11e=B(_ft(_118,_119,_11a,E(_11d.b))),_11f=B(_ZH(_10N,_11c,_11e.b));return new T2(0,new T3(0,_11d.a,_11e.a,_11f.a),_11f.b);},_11g=new T(function(){return B(unCStr("getPatt"));}),_11h=new T(function(){return B(_107(_11g));}),_11i=function(_11j,_11k,_11l,_11m){var _11n=B(_fc(_11j,_11k,_11l,_11m)),_11o=_11n.b;switch(E(_11n.a)){case 0:var _11p=B(_ft(_11j,_11k,_11l,E(_11o))),_11q=B(_ZH(_11r,new T3(0,_11j,_11k,_11l),_11p.b));return new T2(0,new T2(0,_11p.a,_11q.a),_11q.b);case 1:var _11s=B(_ft(_11j,_11k,_11l,E(_11o)));return new T2(0,new T1(2,_11s.a),_11s.b);case 2:var _11t=B(_ft(_11j,_11k,_11l,E(_11o))),_11u=B(_11i(_11j,_11k,_11l,E(_11t.b)));return new T2(0,new T2(3,_11t.a,_11u.a),_11u.b);case 3:return new T2(0,_Y5,_11o);case 4:var _11v=B(_10b(_11j,_11k,_11l,E(_11o)));return new T2(0,new T1(1,_11v.a),_11v.b);case 5:var _11w=B(_11i(_11j,_11k,_11l,E(_11o)));return new T2(0,new T1(5,_11w.a),_11w.b);case 6:var _11x=B(_10q(_11j,_11k,_11l,E(_11o)));return new T2(0,new T1(6,_11x.a),_11x.b);default:return E(_11h);}},_11r=function(_11y,_11z){var _11A=E(_11y),_11B=B(_11i(_11A.a,_11A.b,_11A.c,E(_11z)));return new T2(0,_11B.a,_11B.b);},_11C=function(_11D,_11E){var _11F=E(_11D),_11G=B(_ZH(_11r,_11F,_11E)),_11H=B(_10q(_11F.a,_11F.b,_11F.c,E(_11G.b)));return new T2(0,new T2(0,_11G.a,_11H.a),_11H.b);},_11I=function(_11J,_11K,_11L,_11M){var _11N=B(_10L(_11J,_11K,_11L,_11M)),_11O=_11N.a,_11P=B(_fi(_11J,_11K,_11L,E(_11N.b))),_11Q=_11P.a,_11R=B(_fc(_11J,_11K,_11L,E(_11P.b))),_11S=_11R.b;switch(E(_11R.a)&4294967295){case 0:var _11T=B(_IY(_Jt,_LL,new T3(0,_11J,_11K,_11L),_11S));return new T2(0,new T4(0,_11O,new T(function(){return E(_11Q)&4294967295;}),_4l,_11T.a),_11T.b);case 1:var _11U=new T3(0,_11J,_11K,_11L),_11V=new T(function(){var _11W=B(_ZH(_11C,_11U,_11S));return new T2(0,_11W.a,_11W.b);}),_11X=B(_IY(_Jt,_LL,_11U,new T(function(){return E(E(_11V).b);},1)));return new T2(0,new T4(0,_11O,new T(function(){return E(_11Q)&4294967295;}),new T1(1,new T(function(){return E(E(_11V).a);})),_11X.a),_11X.b);default:return E(_105);}},_11Y=function(_11Z,_120){var _121=E(_11Z),_122=B(_11I(_121.a,_121.b,_121.c,_120));return new T2(0,_122.a,_122.b);},_123=function(_124,_125){var _126=E(_124),_127=B(_10b(_126.a,_126.b,_126.c,E(_125)));return new T2(0,_127.a,_127.b);},_128=function(_129,_12a){var _12b=E(_129),_12c=B(_ft(_12b.a,_12b.b,_12b.c,E(_12a)));return new T2(0,_12c.a,_12c.b);},_12d=function(_12e,_12f){while(1){var _12g=E(_12e);if(!_12g._){return (E(_12f)._==0)?1:0;}else{var _12h=E(_12f);if(!_12h._){return 2;}else{var _12i=E(_12g.a),_12j=E(_12h.a);if(_12i!=_12j){return (_12i>_12j)?2:0;}else{_12e=_12g.b;_12f=_12h.b;continue;}}}}},_12k=function(_12l,_12m){return (B(_12d(_12l,_12m))==0)?true:false;},_12n=function(_12o,_12p){return (B(_12d(_12o,_12p))==2)?false:true;},_12q=function(_12r,_12s){return (B(_12d(_12r,_12s))==2)?true:false;},_12t=function(_12u,_12v){return (B(_12d(_12u,_12v))==0)?false:true;},_12w=function(_12x,_12y){return (B(_12d(_12x,_12y))==2)?E(_12x):E(_12y);},_12z=function(_12A,_12B){return (B(_12d(_12A,_12B))==2)?E(_12B):E(_12A);},_12C={_:0,a:_sz,b:_12d,c:_12k,d:_12n,e:_12q,f:_12t,g:_12w,h:_12z},_12D=function(_12E){var _12F=E(_12E)&4294967295;if(_12F>>>0>1114111){return new F(function(){return _fK(_12F);});}else{return _12F;}},_12G=function(_12H){var _12I=E(_12H);return (_12I._==0)?__Z:new T2(1,new T(function(){return B(_12D(_12I.a));}),new T(function(){return B(_12G(_12I.b));}));},_12J=function(_12K){var _12L=E(_12K);return (_12L._==0)?__Z:new T2(1,new T(function(){return B(_12D(_12L.a));}),new T(function(){return B(_12J(_12L.b));}));},_12M=function(_12N,_12O,_12P,_12Q,_12R,_12S){return new F(function(){return _sf(B(_G(_12D,B(_IJ(_12N,_12O,_12P)))),B(_G(_12D,B(_IJ(_12Q,_12R,_12S)))));});},_12T=function(_12U,_12V,_12W,_12X,_12Y,_12Z){return (!B(_12M(_12U,_12V,_12W,_12X,_12Y,_12Z)))?(B(_12d(B(_12J(new T(function(){return B(_IJ(_12U,_12V,_12W));}))),B(_12G(new T(function(){return B(_IJ(_12X,_12Y,_12Z));})))))==2)?2:0:1;},_130=function(_131,_132,_133,_134,_135,_136){var _137=new T3(0,_132,_133,_134),_138=E(_136);if(!_138._){var _139=_138.c,_13a=_138.d,_13b=_138.e,_13c=E(_138.b);switch(B(_12T(_132,_133,_134,_13c.a,_13c.b,_13c.c))){case 0:return new F(function(){return _Rl(_13c,_139,B(_130(_131,_132,_133,_134,_135,_13a)),_13b);});break;case 1:return new T5(0,_138.a,E(_137),new T(function(){return B(A3(_131,_137,_135,_139));}),E(_13a),E(_13b));default:return new F(function(){return _S2(_13c,_139,_13a,B(_130(_131,_132,_133,_134,_135,_13b)));});}}else{return new T5(0,1,E(_137),_135,E(_Rg),E(_Rg));}},_13d=function(_13e,_13f){var _13g=function(_13h,_13i){while(1){var _13j=E(_13i);if(!_13j._){return E(_13h);}else{var _13k=E(_13j.a),_13l=E(_13k.a),_13m=B(_130(_13e,_13l.a,_13l.b,_13l.c,_13k.b,_13h));_13h=_13m;_13i=_13j.b;continue;}}};return new F(function(){return _13g(_Rg,_13f);});},_13n=function(_13o){return E(E(_13o).b);},_13p=function(_13q,_13r,_13s,_13t){var _13u=E(_13r),_13v=E(_13t);if(!_13v._){var _13w=_13v.b,_13x=_13v.c,_13y=_13v.d,_13z=_13v.e;switch(B(A3(_13n,_13q,_13u,_13w))){case 0:return new F(function(){return _Rl(_13w,_13x,B(_13p(_13q,_13u,_13s,_13y)),_13z);});break;case 1:return new T5(0,_13v.a,E(_13u),_13s,E(_13y),E(_13z));default:return new F(function(){return _S2(_13w,_13x,_13y,B(_13p(_13q,_13u,_13s,_13z)));});}}else{return new T5(0,1,E(_13u),_13s,E(_Rg),E(_Rg));}},_13A=function(_13B,_13C,_13D,_13E){return new F(function(){return _13p(_13B,_13C,_13D,_13E);});},_13F=function(_13G,_13H,_13I,_13J,_13K){var _13L=E(_13K),_13M=B(_13N(_13G,_13H,_13I,_13J,_13L.a,_13L.b));return new T2(0,_13M.a,_13M.b);},_13O=function(_13P,_13Q,_13R){var _13S=function(_13T,_13U){while(1){var _13V=E(_13T),_13W=E(_13U);if(!_13W._){switch(B(A3(_13n,_13P,_13V,_13W.b))){case 0:_13T=_13V;_13U=_13W.d;continue;case 1:return new T1(1,_13W.c);default:_13T=_13V;_13U=_13W.e;continue;}}else{return __Z;}}};return new F(function(){return _13S(_13Q,_13R);});},_13X=function(_13Y,_13Z){var _140=E(_13Y);if(!_140._){return new T2(0,new T1(1,_13Z),_Rg);}else{var _141=new T(function(){return new T5(0,1,E(_140.a),new T(function(){return B(_142(_140.b,_13Z));}),E(_Rg),E(_Rg));});return new T2(0,_4l,_141);}},_142=function(_143,_144){var _145=B(_13X(_143,_144));return new T2(0,_145.a,_145.b);},_13N=function(_146,_147,_148,_149,_14a,_14b){var _14c=E(_148);if(!_14c._){var _14d=E(_14a);return (_14d._==0)?new T2(0,new T1(1,_149),_14b):new T2(0,new T1(1,new T(function(){return B(A2(_147,_149,_14d.a));})),_14b);}else{var _14e=_14c.a,_14f=_14c.b,_14g=B(_13O(_146,_14e,_14b));if(!_14g._){var _14h=new T(function(){return B(_13A(_146,_14e,new T(function(){return B(_142(_14f,_149));}),_14b));});return new T2(0,_14a,_14h);}else{var _14i=new T(function(){return B(_13A(_146,_14e,new T(function(){return B(_13F(_146,_147,_14f,_149,_14g.a));}),_14b));});return new T2(0,_14a,_14i);}}},_14j=function(_14k,_14l,_14m){var _14n=function(_14o,_14p,_14q){while(1){var _14r=E(_14o);if(!_14r._){return new T2(0,_14p,_14q);}else{var _14s=E(_14r.a),_14t=B(_13N(_14k,_14l,_14s.a,_14s.b,_14p,_14q));_14o=_14r.b;_14p=_14t.a;_14q=_14t.b;continue;}}};return new F(function(){return _14n(_14m,_4l,_Rg);});},_14u=function(_14v,_14w,_14x){var _14y=E(_14x);switch(_14y._){case 0:var _14z=_14y.a,_14A=_14y.b,_14B=_14y.c,_14C=_14y.d,_14D=_14A>>>0;if(((_14v>>>0&((_14D-1>>>0^4294967295)>>>0^_14D)>>>0)>>>0&4294967295)==_14z){return ((_14v>>>0&_14D)>>>0==0)?new T4(0,_14z,_14A,E(B(_14u(_14v,_14w,_14B))),E(_14C)):new T4(0,_14z,_14A,E(_14B),E(B(_14u(_14v,_14w,_14C))));}else{var _14E=(_14v>>>0^_14z>>>0)>>>0,_14F=(_14E|_14E>>>1)>>>0,_14G=(_14F|_14F>>>2)>>>0,_14H=(_14G|_14G>>>4)>>>0,_14I=(_14H|_14H>>>8)>>>0,_14J=(_14I|_14I>>>16)>>>0,_14K=(_14J^_14J>>>1)>>>0&4294967295,_14L=_14K>>>0;return ((_14v>>>0&_14L)>>>0==0)?new T4(0,(_14v>>>0&((_14L-1>>>0^4294967295)>>>0^_14L)>>>0)>>>0&4294967295,_14K,E(new T2(1,_14v,_14w)),E(_14y)):new T4(0,(_14v>>>0&((_14L-1>>>0^4294967295)>>>0^_14L)>>>0)>>>0&4294967295,_14K,E(_14y),E(new T2(1,_14v,_14w)));}break;case 1:var _14M=_14y.a;if(_14v!=_14M){var _14N=(_14v>>>0^_14M>>>0)>>>0,_14O=(_14N|_14N>>>1)>>>0,_14P=(_14O|_14O>>>2)>>>0,_14Q=(_14P|_14P>>>4)>>>0,_14R=(_14Q|_14Q>>>8)>>>0,_14S=(_14R|_14R>>>16)>>>0,_14T=(_14S^_14S>>>1)>>>0&4294967295,_14U=_14T>>>0;return ((_14v>>>0&_14U)>>>0==0)?new T4(0,(_14v>>>0&((_14U-1>>>0^4294967295)>>>0^_14U)>>>0)>>>0&4294967295,_14T,E(new T2(1,_14v,_14w)),E(_14y)):new T4(0,(_14v>>>0&((_14U-1>>>0^4294967295)>>>0^_14U)>>>0)>>>0&4294967295,_14T,E(_14y),E(new T2(1,_14v,_14w)));}else{return new T2(1,_14v,_14w);}break;default:return new T2(1,_14v,_14w);}},_14V=function(_14W,_14X){var _14Y=function(_14Z){while(1){var _150=E(_14Z);switch(_150._){case 0:var _151=_150.b>>>0;if(((_14W>>>0&((_151-1>>>0^4294967295)>>>0^_151)>>>0)>>>0&4294967295)==_150.a){if(!((_14W>>>0&_151)>>>0)){_14Z=_150.c;continue;}else{_14Z=_150.d;continue;}}else{return __Z;}break;case 1:return (_14W!=_150.a)?__Z:new T1(1,_150.b);default:return __Z;}}};return new F(function(){return _14Y(_14X);});},_152=function(_153,_154,_155,_156){var _157=E(_156);if(!_157._){var _158=new T(function(){var _159=B(_152(_157.a,_157.b,_157.c,_157.d));return new T2(0,_159.a,_159.b);});return new T2(0,new T(function(){return E(E(_158).a);}),new T(function(){return B(_MQ(_154,_155,E(_158).b));}));}else{return new T2(0,_154,_155);}},_15a=function(_15b,_15c,_15d,_15e){var _15f=E(_15d);if(!_15f._){var _15g=new T(function(){var _15h=B(_15a(_15f.a,_15f.b,_15f.c,_15f.d));return new T2(0,_15h.a,_15h.b);});return new T2(0,new T(function(){return E(E(_15g).a);}),new T(function(){return B(_Ns(_15c,E(_15g).b,_15e));}));}else{return new T2(0,_15c,_15e);}},_15i=function(_15j,_15k){var _15l=E(_15j);if(!_15l._){var _15m=_15l.a,_15n=E(_15k);if(!_15n._){var _15o=_15n.a;if(_15m<=_15o){var _15p=B(_15a(_15o,_15n.b,_15n.c,_15n.d));return new F(function(){return _MQ(_15p.a,_15l,_15p.b);});}else{var _15q=B(_152(_15m,_15l.b,_15l.c,_15l.d));return new F(function(){return _Ns(_15q.a,_15q.b,_15n);});}}else{return E(_15l);}}else{return E(_15k);}},_15r=function(_15s,_15t,_15u,_15v,_15w){var _15x=E(_15s);if(!_15x._){var _15y=_15x.a,_15z=_15x.b,_15A=_15x.c,_15B=_15x.d;if((imul(3,_15y)|0)>=_15t){if((imul(3,_15t)|0)>=_15y){return new F(function(){return _15i(_15x,new T4(0,_15t,E(_15u),E(_15v),E(_15w)));});}else{return new F(function(){return _Ns(_15z,_15A,B(_15r(_15B,_15t,_15u,_15v,_15w)));});}}else{return new F(function(){return _MQ(_15u,B(_15C(_15y,_15z,_15A,_15B,_15v)),_15w);});}}else{return new T4(0,_15t,E(_15u),E(_15v),E(_15w));}},_15C=function(_15D,_15E,_15F,_15G,_15H){var _15I=E(_15H);if(!_15I._){var _15J=_15I.a,_15K=_15I.b,_15L=_15I.c,_15M=_15I.d;if((imul(3,_15D)|0)>=_15J){if((imul(3,_15J)|0)>=_15D){return new F(function(){return _15i(new T4(0,_15D,E(_15E),E(_15F),E(_15G)),_15I);});}else{return new F(function(){return _Ns(_15E,_15F,B(_15r(_15G,_15J,_15K,_15L,_15M)));});}}else{return new F(function(){return _MQ(_15K,B(_15C(_15D,_15E,_15F,_15G,_15L)),_15M);});}}else{return new T4(0,_15D,E(_15E),E(_15F),E(_15G));}},_15N=function(_15O,_15P){var _15Q=E(_15O);if(!_15Q._){var _15R=_15Q.a,_15S=_15Q.b,_15T=_15Q.c,_15U=_15Q.d,_15V=E(_15P);if(!_15V._){var _15W=_15V.a,_15X=_15V.b,_15Y=_15V.c,_15Z=_15V.d;if((imul(3,_15R)|0)>=_15W){if((imul(3,_15W)|0)>=_15R){return new F(function(){return _15i(_15Q,_15V);});}else{return new F(function(){return _Ns(_15S,_15T,B(_15r(_15U,_15W,_15X,_15Y,_15Z)));});}}else{return new F(function(){return _MQ(_15X,B(_15C(_15R,_15S,_15T,_15U,_15Y)),_15Z);});}}else{return E(_15Q);}}else{return E(_15P);}},_160=function(_161,_162){var _163=E(_162);if(!_163._){var _164=_163.b,_165=B(_160(_161,_163.c)),_166=_165.a,_167=_165.b,_168=B(_160(_161,_163.d)),_169=_168.a,_16a=_168.b;return (!B(A1(_161,_164)))?new T2(0,B(_15N(_166,_169)),B(_OM(_164,_167,_16a))):new T2(0,B(_OM(_164,_166,_169)),B(_15N(_167,_16a)));}else{return new T2(0,_ML,_ML);}},_16b=function(_16c,_16d,_16e,_16f){var _16g=E(_16e),_16h=B(_16i(_16c,_16d,_16g.a,_16g.b,_16f));return new T2(0,_16h.a,_16h.b);},_16j=function(_16k,_16l,_16m){while(1){var _16n=E(_16m);if(!_16n._){var _16o=_16n.e;switch(B(A3(_13n,_16k,_16l,_16n.b))){case 0:return new T2(0,B(_13O(_16k,_16l,_16n.d)),_16n);case 1:return new T2(0,new T1(1,_16n.c),_16o);default:_16m=_16o;continue;}}else{return new T2(0,_4l,_Rg);}}},_16p=function(_16q){return E(E(_16q).f);},_16r=function(_16s,_16t,_16u){while(1){var _16v=E(_16u);if(!_16v._){if(!B(A3(_16p,_16s,_16v.b,_16t))){return E(_16v);}else{_16u=_16v.d;continue;}}else{return new T0(1);}}},_16w=function(_16x,_16y,_16z,_16A){while(1){var _16B=E(_16A);if(!_16B._){var _16C=_16B.b,_16D=_16B.d,_16E=_16B.e;switch(B(A3(_13n,_16x,_16y,_16C))){case 0:if(!B(A3(_pK,_16x,_16C,_16z))){_16A=_16D;continue;}else{return new T2(0,B(_13O(_16x,_16y,_16D)),_16B);}break;case 1:return new T2(0,new T1(1,_16B.c),B(_16r(_16x,_16z,_16E)));default:_16A=_16E;continue;}}else{return new T2(0,_4l,_Rg);}}},_16F=function(_16G,_16H,_16I,_16J){var _16K=E(_16I);if(!_16K._){return new F(function(){return _16j(_16G,_16H,_16J);});}else{return new F(function(){return _16w(_16G,_16H,_16K.a,_16J);});}},_16L=__Z,_16M=function(_16N,_16O,_16P){var _16Q=E(_16O);if(!_16Q._){return E(_16P);}else{var _16R=function(_16S,_16T){while(1){var _16U=E(_16T);if(!_16U._){var _16V=_16U.b,_16W=_16U.e;switch(B(A3(_13n,_16N,_16S,_16V))){case 0:return new F(function(){return _Tw(_16V,_16U.c,B(_16R(_16S,_16U.d)),_16W);});break;case 1:return E(_16W);default:_16T=_16W;continue;}}else{return new T0(1);}}};return new F(function(){return _16R(_16Q.a,_16P);});}},_16X=function(_16Y,_16Z,_170){var _171=E(_16Z);if(!_171._){return E(_170);}else{var _172=function(_173,_174){while(1){var _175=E(_174);if(!_175._){var _176=_175.b,_177=_175.d;switch(B(A3(_13n,_16Y,_176,_173))){case 0:return new F(function(){return _Tw(_176,_175.c,_177,B(_172(_173,_175.e)));});break;case 1:return E(_177);default:_174=_177;continue;}}else{return new T0(1);}}};return new F(function(){return _172(_171.a,_170);});}},_178=function(_179){return E(E(_179).d);},_17a=function(_17b,_17c,_17d,_17e){var _17f=E(_17c);if(!_17f._){var _17g=E(_17d);if(!_17g._){return E(_17e);}else{var _17h=function(_17i,_17j){while(1){var _17k=E(_17j);if(!_17k._){if(!B(A3(_16p,_17b,_17k.b,_17i))){return E(_17k);}else{_17j=_17k.d;continue;}}else{return new T0(1);}}};return new F(function(){return _17h(_17g.a,_17e);});}}else{var _17l=_17f.a,_17m=E(_17d);if(!_17m._){var _17n=function(_17o,_17p){while(1){var _17q=E(_17p);if(!_17q._){if(!B(A3(_178,_17b,_17q.b,_17o))){return E(_17q);}else{_17p=_17q.e;continue;}}else{return new T0(1);}}};return new F(function(){return _17n(_17l,_17e);});}else{var _17r=function(_17s,_17t,_17u){while(1){var _17v=E(_17u);if(!_17v._){var _17w=_17v.b;if(!B(A3(_178,_17b,_17w,_17s))){if(!B(A3(_16p,_17b,_17w,_17t))){return E(_17v);}else{_17u=_17v.d;continue;}}else{_17u=_17v.e;continue;}}else{return new T0(1);}}};return new F(function(){return _17r(_17l,_17m.a,_17e);});}}},_17x=function(_17y,_17z,_17A,_17B){var _17C=E(_17A);if(!_17C._){var _17D=E(_17B);if(!_17D._){var _17E=function(_17F,_17G,_17H,_17I){var _17J=E(_17I);if(!_17J._){var _17K=E(_17H);if(!_17K._){var _17L=_17K.b,_17M=_17K.c,_17N=_17K.e,_17O=B(_16F(_17y,_17L,_17G,_17J)),_17P=_17O.b,_17Q=new T1(1,E(_17L)),_17R=B(_17E(_17F,_17Q,_17K.d,B(_17a(_17y,_17F,_17Q,_17J)))),_17S=E(_17O.a);if(!_17S._){return new F(function(){return _Tw(_17L,_17M,_17R,B(_17E(_17Q,_17G,_17N,_17P)));});}else{return new F(function(){return _Tw(_17L,new T(function(){return B(A3(_17z,_17L,_17M,_17S.a));}),_17R,B(_17E(_17Q,_17G,_17N,_17P)));});}}else{return new F(function(){return _Tw(_17J.b,_17J.c,B(_16M(_17y,_17F,_17J.d)),B(_16X(_17y,_17G,_17J.e)));});}}else{return E(_17H);}},_17T=_16L,_17U=_16L,_17V=_17C.a,_17W=_17C.b,_17X=_17C.c,_17Y=_17C.d,_17Z=_17C.e,_180=_17D.a,_181=_17D.b,_182=_17D.c,_183=_17D.d,_184=_17D.e,_185=B(_16F(_17y,_17W,_17U,new T5(0,_180,E(_181),_182,E(_183),E(_184)))),_186=_185.b,_187=new T1(1,E(_17W)),_188=B(_17E(_17T,_187,_17Y,B(_17a(_17y,_17T,_187,new T5(0,_180,E(_181),_182,E(_183),E(_184)))))),_189=E(_185.a);if(!_189._){return new F(function(){return _Tw(_17W,_17X,_188,B(_17E(_187,_17U,_17Z,_186)));});}else{return new F(function(){return _Tw(_17W,new T(function(){return B(A3(_17z,_17W,_17X,_189.a));}),_188,B(_17E(_187,_17U,_17Z,_186)));});}}else{return E(_17C);}}else{return E(_17B);}},_16i=function(_18a,_18b,_18c,_18d,_18e){var _18f=E(_18e),_18g=_18f.a,_18h=new T(function(){return B(_17x(_18a,function(_18i,_18j,_18k){return new F(function(){return _16b(_18a,_18b,_18j,_18k);});},_18d,_18f.b));}),_18l=new T(function(){var _18m=E(_18c);if(!_18m._){return E(_18g);}else{var _18n=E(_18g);if(!_18n._){return E(_18m);}else{return new T1(1,new T(function(){return B(A2(_18b,_18m.a,_18n.a));}));}}});return new T2(0,_18l,_18h);},_18o=function(_18p,_18q,_18r){var _18s=function(_18t,_18u,_18v){while(1){var _18w=E(_18t);if(!_18w._){return new T2(0,_18u,_18v);}else{var _18x=B(_16i(_18p,_18q,_18u,_18v,_18w.a));_18t=_18w.b;_18u=_18x.a;_18v=_18x.b;continue;}}};return new F(function(){return _18s(_18r,_4l,_Rg);});},_18y=new T0(2),_18z=function(_18A,_18B){var _18C=E(_18A),_18D=E(_18B);return new F(function(){return _12M(_18C.a,_18C.b,_18C.c,_18D.a,_18D.b,_18D.c);});},_18E=function(_18F,_18G){return E(_18F)==E(_18G);},_18H=function(_18I,_18J){var _18K=E(_18I);switch(_18K._){case 0:var _18L=E(_18J);if(!_18L._){return new F(function(){return _sf(_18K.a,_18L.a);});}else{return false;}break;case 1:var _18M=E(_18J);if(_18M._==1){return new F(function(){return _iV(_18K.a,_18M.a);});}else{return false;}break;default:var _18N=E(_18J);if(_18N._==2){return new F(function(){return _18E(_18K.a,_18N.a);});}else{return false;}}},_18O=function(_18P,_18Q,_18R){while(1){var _18S=E(_18Q);if(!_18S._){return (E(_18R)._==0)?true:false;}else{var _18T=E(_18R);if(!_18T._){return false;}else{if(!B(A3(_pM,_18P,_18S.a,_18T.a))){return false;}else{_18Q=_18S.b;_18R=_18T.b;continue;}}}}},_18U=function(_18V,_18W){return (!B(_18X(_18V,_18W)))?true:false;},_18Y=new T2(0,_18X,_18U),_18Z=new T(function(){return E(_18Y);}),_190=function(_191,_192){return (E(_191)==0)?(E(_192)==0)?false:true:(E(_192)==0)?true:false;},_193=function(_194,_195){return (E(_194)==0)?(E(_195)==0)?true:false:(E(_195)==0)?false:true;},_196=new T2(0,_193,_190),_197=new T(function(){return E(_196);}),_198=function(_199,_19a,_19b,_19c,_19d,_19e){if(!B(A3(_pM,_197,_199,_19c))){return false;}else{var _19f=E(_19a),_19g=E(_19d);if(!B(_12M(_19f.a,_19f.b,_19f.c,_19g.a,_19g.b,_19g.c))){return false;}else{return new F(function(){return _19h(_19b,_19e);});}}},_19i=function(_19j,_19k){var _19l=E(_19j),_19m=E(_19k);return new F(function(){return _198(_19l.a,_19l.b,_19l.c,_19m.a,_19m.b,_19m.c);});},_19n=function(_19o,_19p,_19q,_19r,_19s,_19t){if(!B(A3(_pM,_197,_19o,_19r))){return true;}else{var _19u=E(_19p),_19v=E(_19s);if(!B(_12M(_19u.a,_19u.b,_19u.c,_19v.a,_19v.b,_19v.c))){return true;}else{var _19w=E(_19q);return (!B(_19x(_19w.a,_19w.b,_19w.c,_19t)))?true:false;}}},_19y=function(_19z,_19A){var _19B=E(_19z),_19C=E(_19A);return new F(function(){return _19n(_19B.a,_19B.b,_19B.c,_19C.a,_19C.b,_19C.c);});},_19D=new T(function(){return new T2(0,_19i,_19y);}),_19x=function(_19E,_19F,_19G,_19H){var _19I=E(_19H);if(!B(_18O(_19D,_19E,_19I.a))){return false;}else{var _19J=E(_19F),_19K=E(_19I.b);if(!B(_12M(_19J.a,_19J.b,_19J.c,_19K.a,_19K.b,_19K.c))){return false;}else{return new F(function(){return _18O(_18Z,_19G,_19I.c);});}}},_19h=function(_19L,_19M){var _19N=E(_19L);return new F(function(){return _19x(_19N.a,_19N.b,_19N.c,_19M);});},_18X=function(_19O,_19P){while(1){var _19Q=E(_19O);switch(_19Q._){case 0:var _19R=_19Q.b,_19S=_19Q.c,_19T=E(_19P);if(!_19T._){var _19U=_19T.a,_19V=_19T.b,_19W=_19T.c;if(!E(_19Q.a)){if(!E(_19U)){var _19X=E(_19R),_19Y=E(_19V);if(!B(_12M(_19X.a,_19X.b,_19X.c,_19Y.a,_19Y.b,_19Y.c))){return false;}else{_19O=_19S;_19P=_19W;continue;}}else{return false;}}else{if(!E(_19U)){return false;}else{var _19Z=E(_19R),_1a0=E(_19V);if(!B(_12M(_19Z.a,_19Z.b,_19Z.c,_1a0.a,_1a0.b,_1a0.c))){return false;}else{_19O=_19S;_19P=_19W;continue;}}}}else{return false;}break;case 1:var _1a1=E(_19P);if(_1a1._==1){if(!B(_18X(_19Q.a,_1a1.a))){return false;}else{_19O=_19Q.b;_19P=_1a1.b;continue;}}else{return false;}break;case 2:var _1a2=E(_19P);if(_1a2._==2){return new F(function(){return _18H(_19Q.a,_1a2.a);});}else{return false;}break;case 3:var _1a3=E(_19P);return (_1a3._==3)?_19Q.a==_1a3.a:false;case 4:var _1a4=E(_19P);if(_1a4._==4){return new F(function(){return _18z(_19Q.a,_1a4.a);});}else{return false;}break;case 5:var _1a5=E(_19P);return (_1a5._==5)?_19Q.a==_1a5.a:false;case 6:var _1a6=E(_19P);if(_1a6._==6){if(!B(_18X(_19Q.a,_1a6.a))){return false;}else{return new F(function(){return _19h(_19Q.b,_1a6.b);});}}else{return false;}break;default:var _1a7=E(_19P);if(_1a7._==7){_19O=_19Q.a;_19P=_1a7.a;continue;}else{return false;}}}},_1a8=function(_1a9,_1aa,_1ab,_1ac){return (_1a9!=_1ab)?true:(E(_1aa)!=E(_1ac))?true:false;},_1ad=function(_1ae,_1af){var _1ag=E(_1ae),_1ah=E(_1af);return new F(function(){return _1a8(E(_1ag.a),_1ag.b,E(_1ah.a),_1ah.b);});},_1ai=function(_1aj,_1ak,_1al,_1am){if(_1aj!=_1al){return false;}else{return new F(function(){return _iV(_1ak,_1am);});}},_1an=function(_1ao,_1ap){var _1aq=E(_1ao),_1ar=E(_1ap);return new F(function(){return _1ai(E(_1aq.a),_1aq.b,E(_1ar.a),_1ar.b);});},_1as=new T2(0,_1an,_1ad),_1at=function(_1au,_1av,_1aw,_1ax){return (!B(_18O(_1as,_1au,_1aw)))?true:(_1av!=_1ax)?true:false;},_1ay=function(_1az,_1aA){var _1aB=E(_1az),_1aC=E(_1aA);return new F(function(){return _1at(_1aB.a,_1aB.b,_1aC.a,_1aC.b);});},_1aD=function(_1aE,_1aF){var _1aG=E(_1aE),_1aH=E(_1aF);return (!B(_18O(_1as,_1aG.a,_1aH.a)))?false:_1aG.b==_1aH.b;},_1aI=new T2(0,_1aD,_1ay),_1aJ=function(_1aK,_1aL){while(1){var _1aM=E(_1aK);if(!_1aM._){return (E(_1aL)._==0)?true:false;}else{var _1aN=E(_1aL);if(!_1aN._){return false;}else{if(!B(_sr(_1aM.a,_1aN.a))){return false;}else{_1aK=_1aM.b;_1aL=_1aN.b;continue;}}}}},_1aO=function(_1aP,_1aQ){var _1aR=E(_1aP);switch(_1aR._){case 0:var _1aS=E(_1aQ);if(!_1aS._){if(_1aR.a!=_1aS.a){return false;}else{return new F(function(){return _18O(_1aI,_1aR.b,_1aS.b);});}}else{return false;}break;case 1:var _1aT=E(_1aQ);return (_1aT._==1)?_1aR.a==_1aT.a:false;default:var _1aU=E(_1aQ);if(_1aU._==2){var _1aV=E(_1aR.a),_1aW=E(_1aU.a);if(!B(_12M(_1aV.a,_1aV.b,_1aV.c,_1aW.a,_1aW.b,_1aW.c))){return false;}else{if(!B(_18X(_1aR.b,_1aU.b))){return false;}else{return new F(function(){return _1aJ(_1aR.c,_1aU.c);});}}}else{return false;}}},_1aX=function(_1aY,_1aZ){return (!B(_1aO(_1aY,_1aZ)))?true:false;},_1b0=new T2(0,_1aO,_1aX),_1b1=function(_1b2,_1b3){var _1b4=E(_1b2),_1b5=E(_1b3);return new F(function(){return _12T(_1b4.a,_1b4.b,_1b4.c,_1b5.a,_1b5.b,_1b5.c);});},_1b6=function(_1b7,_1b8){var _1b9=E(_1b7),_1ba=E(_1b8);return (_1b9>=_1ba)?(_1b9!=_1ba)?2:1:0;},_1bb=function(_1bc,_1bd){var _1be=E(_1bc);switch(_1be._){case 0:var _1bf=E(_1bd);if(!_1bf._){return new F(function(){return _12d(_1be.a,_1bf.a);});}else{return 0;}break;case 1:var _1bg=E(_1bd);switch(_1bg._){case 0:return 2;case 1:return new F(function(){return _jf(_1be.a,_1bg.a);});break;default:return 0;}break;default:var _1bh=E(_1bd);if(_1bh._==2){return new F(function(){return _1b6(_1be.a,_1bh.a);});}else{return 2;}}},_1bi=function(_1bj,_1bk){return (B(_1bl(_1bj,_1bk))==0)?true:false;},_1bm=function(_1bn,_1bo){return (B(_1bl(_1bn,_1bo))==2)?false:true;},_1bp=function(_1bq,_1br){return (B(_1bl(_1bq,_1br))==2)?true:false;},_1bs=function(_1bt,_1bu){return (B(_1bl(_1bt,_1bu))==0)?false:true;},_1bv=function(_1bw,_1bx){return (B(_1bl(_1bw,_1bx))==2)?E(_1bw):E(_1bx);},_1by=function(_1bz,_1bA){return (B(_1bl(_1bz,_1bA))==2)?E(_1bA):E(_1bz);},_1bB={_:0,a:_18Y,b:_1bl,c:_1bi,d:_1bm,e:_1bp,f:_1bs,g:_1bv,h:_1by},_1bC=new T(function(){return E(_1bB);}),_1bD=function(_1bE,_1bF,_1bG){while(1){var _1bH=E(_1bF);if(!_1bH._){return (E(_1bG)._==0)?1:0;}else{var _1bI=E(_1bG);if(!_1bI._){return 2;}else{var _1bJ=B(A3(_13n,_1bE,_1bH.a,_1bI.a));if(_1bJ==1){_1bF=_1bH.b;_1bG=_1bI.b;continue;}else{return E(_1bJ);}}}}},_1bK=function(_1bL,_1bM,_1bN,_1bO){var _1bP=E(_1bO);switch(B(_1bD(_1bQ,_1bL,_1bP.a))){case 0:return false;case 1:var _1bR=E(_1bM),_1bS=E(_1bP.b);switch(B(_12T(_1bR.a,_1bR.b,_1bR.c,_1bS.a,_1bS.b,_1bS.c))){case 0:return false;case 1:return (B(_1bD(_1bC,_1bN,_1bP.c))==0)?false:true;default:return true;}break;default:return true;}},_1bT=function(_1bU,_1bV){var _1bW=E(_1bU);return new F(function(){return _1bK(_1bW.a,_1bW.b,_1bW.c,_1bV);});},_1bX=function(_1bY,_1bZ){if(!E(_1bY)){return (E(_1bZ)==0)?false:true;}else{var _1c0=E(_1bZ);return false;}},_1c1=function(_1c2,_1c3){if(!E(_1c2)){var _1c4=E(_1c3);return true;}else{return (E(_1c3)==0)?false:true;}},_1c5=function(_1c6,_1c7){if(!E(_1c6)){var _1c8=E(_1c7);return false;}else{return (E(_1c7)==0)?true:false;}},_1c9=function(_1ca,_1cb){if(!E(_1ca)){return (E(_1cb)==0)?true:false;}else{var _1cc=E(_1cb);return true;}},_1cd=function(_1ce,_1cf){return (E(_1ce)==0)?(E(_1cf)==0)?1:0:(E(_1cf)==0)?2:1;},_1cg=function(_1ch,_1ci){if(!E(_1ch)){return E(_1ci);}else{var _1cj=E(_1ci);return 1;}},_1ck=function(_1cl,_1cm){if(!E(_1cl)){var _1cn=E(_1cm);return 0;}else{return E(_1cm);}},_1co={_:0,a:_196,b:_1cd,c:_1bX,d:_1c1,e:_1c5,f:_1c9,g:_1cg,h:_1ck},_1cp=new T(function(){return E(_1co);}),_1cq=function(_1cr,_1cs,_1ct,_1cu,_1cv,_1cw){switch(B(A3(_13n,_1cp,_1cr,_1cu))){case 0:return false;case 1:var _1cx=E(_1cs),_1cy=E(_1cv);switch(B(_12T(_1cx.a,_1cx.b,_1cx.c,_1cy.a,_1cy.b,_1cy.c))){case 0:return false;case 1:return new F(function(){return _1bT(_1ct,_1cw);});break;default:return true;}break;default:return true;}},_1cz=function(_1cA,_1cB){var _1cC=E(_1cA),_1cD=E(_1cB);return new F(function(){return _1cq(_1cC.a,_1cC.b,_1cC.c,_1cD.a,_1cD.b,_1cD.c);});},_1cE=function(_1cF,_1cG,_1cH,_1cI){var _1cJ=E(_1cI);switch(B(_1bD(_1bQ,_1cF,_1cJ.a))){case 0:return false;case 1:var _1cK=E(_1cG),_1cL=E(_1cJ.b);switch(B(_12T(_1cK.a,_1cK.b,_1cK.c,_1cL.a,_1cL.b,_1cL.c))){case 0:return false;case 1:return (B(_1bD(_1bC,_1cH,_1cJ.c))==2)?true:false;default:return true;}break;default:return true;}},_1cM=function(_1cN,_1cO){var _1cP=E(_1cN);return new F(function(){return _1cE(_1cP.a,_1cP.b,_1cP.c,_1cO);});},_1cQ=function(_1cR,_1cS,_1cT,_1cU,_1cV,_1cW){switch(B(A3(_13n,_1cp,_1cR,_1cU))){case 0:return false;case 1:var _1cX=E(_1cS),_1cY=E(_1cV);switch(B(_12T(_1cX.a,_1cX.b,_1cX.c,_1cY.a,_1cY.b,_1cY.c))){case 0:return false;case 1:return new F(function(){return _1cM(_1cT,_1cW);});break;default:return true;}break;default:return true;}},_1cZ=function(_1d0,_1d1){var _1d2=E(_1d0),_1d3=E(_1d1);return new F(function(){return _1cQ(_1d2.a,_1d2.b,_1d2.c,_1d3.a,_1d3.b,_1d3.c);});},_1d4=function(_1d5,_1d6,_1d7,_1d8){var _1d9=E(_1d8);switch(B(_1bD(_1bQ,_1d5,_1d9.a))){case 0:return true;case 1:var _1da=E(_1d6),_1db=E(_1d9.b);switch(B(_12T(_1da.a,_1da.b,_1da.c,_1db.a,_1db.b,_1db.c))){case 0:return true;case 1:return (B(_1bD(_1bC,_1d7,_1d9.c))==2)?false:true;default:return false;}break;default:return false;}},_1dc=function(_1dd,_1de){var _1df=E(_1dd);return new F(function(){return _1d4(_1df.a,_1df.b,_1df.c,_1de);});},_1dg=function(_1dh,_1di,_1dj,_1dk,_1dl,_1dm){switch(B(A3(_13n,_1cp,_1dh,_1dk))){case 0:return true;case 1:var _1dn=E(_1di),_1do=E(_1dl);switch(B(_12T(_1dn.a,_1dn.b,_1dn.c,_1do.a,_1do.b,_1do.c))){case 0:return true;case 1:return new F(function(){return _1dc(_1dj,_1dm);});break;default:return false;}break;default:return false;}},_1dp=function(_1dq,_1dr){var _1ds=E(_1dq),_1dt=E(_1dr);return new F(function(){return _1dg(_1ds.a,_1ds.b,_1ds.c,_1dt.a,_1dt.b,_1dt.c);});},_1du=function(_1dv,_1dw){var _1dx=E(_1dv),_1dy=_1dx.a,_1dz=_1dx.c,_1dA=E(_1dw),_1dB=_1dA.a,_1dC=_1dA.c;switch(B(A3(_13n,_1cp,_1dy,_1dB))){case 0:return E(_1dA);case 1:var _1dD=E(_1dx.b),_1dE=E(_1dA.b);switch(B(_12T(_1dD.a,_1dD.b,_1dD.c,_1dE.a,_1dE.b,_1dE.c))){case 0:return new T3(0,_1dB,_1dE,_1dC);case 1:var _1dF=E(_1dz);return (!B(_1d4(_1dF.a,_1dF.b,_1dF.c,_1dC)))?new T3(0,_1dy,_1dD,_1dF):new T3(0,_1dB,_1dE,_1dC);default:return new T3(0,_1dy,_1dD,_1dz);}break;default:return E(_1dx);}},_1dG=function(_1dH,_1dI){var _1dJ=E(_1dH),_1dK=_1dJ.a,_1dL=_1dJ.c,_1dM=E(_1dI),_1dN=_1dM.a,_1dO=_1dM.c;switch(B(A3(_13n,_1cp,_1dK,_1dN))){case 0:return E(_1dJ);case 1:var _1dP=E(_1dJ.b),_1dQ=E(_1dM.b);switch(B(_12T(_1dP.a,_1dP.b,_1dP.c,_1dQ.a,_1dQ.b,_1dQ.c))){case 0:return new T3(0,_1dK,_1dP,_1dL);case 1:var _1dR=E(_1dL);return (!B(_1d4(_1dR.a,_1dR.b,_1dR.c,_1dO)))?new T3(0,_1dN,_1dQ,_1dO):new T3(0,_1dK,_1dP,_1dR);default:return new T3(0,_1dN,_1dQ,_1dO);}break;default:return E(_1dM);}},_1dS=function(_1dT,_1dU,_1dV,_1dW){var _1dX=E(_1dW);switch(B(_1bD(_1bQ,_1dT,_1dX.a))){case 0:return true;case 1:var _1dY=E(_1dU),_1dZ=E(_1dX.b);switch(B(_12T(_1dY.a,_1dY.b,_1dY.c,_1dZ.a,_1dZ.b,_1dZ.c))){case 0:return true;case 1:return (B(_1bD(_1bC,_1dV,_1dX.c))==0)?true:false;default:return false;}break;default:return false;}},_1e0=function(_1e1,_1e2){var _1e3=E(_1e1);return new F(function(){return _1dS(_1e3.a,_1e3.b,_1e3.c,_1e2);});},_1e4=function(_1e5,_1e6,_1e7,_1e8,_1e9,_1ea){switch(B(A3(_13n,_1cp,_1e5,_1e8))){case 0:return true;case 1:var _1eb=E(_1e6),_1ec=E(_1e9);switch(B(_12T(_1eb.a,_1eb.b,_1eb.c,_1ec.a,_1ec.b,_1ec.c))){case 0:return true;case 1:return new F(function(){return _1e0(_1e7,_1ea);});break;default:return false;}break;default:return false;}},_1ed=function(_1ee,_1ef){var _1eg=E(_1ee),_1eh=E(_1ef);return new F(function(){return _1e4(_1eg.a,_1eg.b,_1eg.c,_1eh.a,_1eh.b,_1eh.c);});},_1ei=function(_1ej,_1ek,_1el,_1em,_1en,_1eo){switch(B(A3(_13n,_1cp,_1ej,_1em))){case 0:return 0;case 1:var _1ep=E(_1ek),_1eq=E(_1en);switch(B(_12T(_1ep.a,_1ep.b,_1ep.c,_1eq.a,_1eq.b,_1eq.c))){case 0:return 0;case 1:return new F(function(){return _1er(_1el,_1eo);});break;default:return 2;}break;default:return 2;}},_1es=function(_1et,_1eu){var _1ev=E(_1et),_1ew=E(_1eu);return new F(function(){return _1ei(_1ev.a,_1ev.b,_1ev.c,_1ew.a,_1ew.b,_1ew.c);});},_1bQ=new T(function(){return {_:0,a:_19D,b:_1es,c:_1ed,d:_1dp,e:_1cZ,f:_1cz,g:_1du,h:_1dG};}),_1ex=function(_1ey,_1ez,_1eA,_1eB){var _1eC=E(_1eB);switch(B(_1bD(_1bQ,_1ey,_1eC.a))){case 0:return 0;case 1:var _1eD=E(_1ez),_1eE=E(_1eC.b);switch(B(_12T(_1eD.a,_1eD.b,_1eD.c,_1eE.a,_1eE.b,_1eE.c))){case 0:return 0;case 1:return new F(function(){return _1bD(_1bC,_1eA,_1eC.c);});break;default:return 2;}break;default:return 2;}},_1er=function(_1eF,_1eG){var _1eH=E(_1eF);return new F(function(){return _1ex(_1eH.a,_1eH.b,_1eH.c,_1eG);});},_1bl=function(_1eI,_1eJ){while(1){var _1eK=B((function(_1eL,_1eM){var _1eN=E(_1eL);switch(_1eN._){case 0:var _1eO=E(_1eM);if(!_1eO._){var _1eP=_1eO.a,_1eQ=function(_1eR){var _1eS=E(_1eN.b),_1eT=E(_1eO.b);switch(B(_12T(_1eS.a,_1eS.b,_1eS.c,_1eT.a,_1eT.b,_1eT.c))){case 0:return 0;case 1:return new F(function(){return _1bl(_1eN.c,_1eO.c);});break;default:return 2;}};if(!E(_1eN.a)){if(!E(_1eP)){return new F(function(){return _1eQ(_);});}else{return 0;}}else{if(!E(_1eP)){return 2;}else{return new F(function(){return _1eQ(_);});}}}else{return 0;}break;case 1:var _1eU=E(_1eM);switch(_1eU._){case 0:return 2;case 1:switch(B(_1bl(_1eN.a,_1eU.a))){case 0:return 0;case 1:_1eI=_1eN.b;_1eJ=_1eU.b;return __continue;default:return 2;}break;default:return 0;}break;case 2:var _1eV=E(_1eM);switch(_1eV._){case 2:return new F(function(){return _1bb(_1eN.a,_1eV.a);});break;case 3:return 0;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 3:var _1eW=E(_1eM);switch(_1eW._){case 3:return new F(function(){return _jc(_1eN.a,_1eW.a);});break;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 4:var _1eX=E(_1eM);switch(_1eX._){case 4:return new F(function(){return _1b1(_1eN.a,_1eX.a);});break;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 5:var _1eY=E(_1eM);switch(_1eY._){case 5:return new F(function(){return _jc(_1eN.a,_1eY.a);});break;case 6:return 0;case 7:return 0;default:return 2;}break;case 6:var _1eZ=E(_1eM);switch(_1eZ._){case 6:switch(B(_1bl(_1eN.a,_1eZ.a))){case 0:return 0;case 1:return new F(function(){return _1er(_1eN.b,_1eZ.b);});break;default:return 2;}break;case 7:return 0;default:return 2;}break;default:var _1f0=E(_1eM);if(_1f0._==7){_1eI=_1eN.a;_1eJ=_1f0.a;return __continue;}else{return 2;}}})(_1eI,_1eJ));if(_1eK!=__continue){return _1eK;}}},_1f1=function(_1f2,_1f3,_1f4,_1f5){if(_1f2>=_1f4){if(_1f2!=_1f4){return 2;}else{return new F(function(){return _jf(_1f3,_1f5);});}}else{return 0;}},_1f6=function(_1f7,_1f8){var _1f9=E(_1f7),_1fa=E(_1f8);return new F(function(){return _1f1(E(_1f9.a),_1f9.b,E(_1fa.a),_1fa.b);});},_1fb=function(_1fc,_1fd,_1fe,_1ff){if(_1fc>=_1fe){if(_1fc!=_1fe){return false;}else{return new F(function(){return _jr(_1fd,_1ff);});}}else{return true;}},_1fg=function(_1fh,_1fi){var _1fj=E(_1fh),_1fk=E(_1fi);return new F(function(){return _1fb(E(_1fj.a),_1fj.b,E(_1fk.a),_1fk.b);});},_1fl=function(_1fm,_1fn,_1fo,_1fp){if(_1fm>=_1fo){if(_1fm!=_1fo){return false;}else{return new F(function(){return _jo(_1fn,_1fp);});}}else{return true;}},_1fq=function(_1fr,_1fs){var _1ft=E(_1fr),_1fu=E(_1fs);return new F(function(){return _1fl(E(_1ft.a),_1ft.b,E(_1fu.a),_1fu.b);});},_1fv=function(_1fw,_1fx,_1fy,_1fz){if(_1fw>=_1fy){if(_1fw!=_1fy){return true;}else{return new F(function(){return _jl(_1fx,_1fz);});}}else{return false;}},_1fA=function(_1fB,_1fC){var _1fD=E(_1fB),_1fE=E(_1fC);return new F(function(){return _1fv(E(_1fD.a),_1fD.b,E(_1fE.a),_1fE.b);});},_1fF=function(_1fG,_1fH,_1fI,_1fJ){if(_1fG>=_1fI){if(_1fG!=_1fI){return true;}else{return new F(function(){return _ji(_1fH,_1fJ);});}}else{return false;}},_1fK=function(_1fL,_1fM){var _1fN=E(_1fL),_1fO=E(_1fM);return new F(function(){return _1fF(E(_1fN.a),_1fN.b,E(_1fO.a),_1fO.b);});},_1fP=function(_1fQ,_1fR){var _1fS=E(_1fQ),_1fT=E(_1fS.a),_1fU=E(_1fR),_1fV=E(_1fU.a);return (_1fT>=_1fV)?(_1fT!=_1fV)?E(_1fS):(E(_1fS.b)>E(_1fU.b))?E(_1fS):E(_1fU):E(_1fU);},_1fW=function(_1fX,_1fY){var _1fZ=E(_1fX),_1g0=E(_1fZ.a),_1g1=E(_1fY),_1g2=E(_1g1.a);return (_1g0>=_1g2)?(_1g0!=_1g2)?E(_1g1):(E(_1fZ.b)>E(_1g1.b))?E(_1g1):E(_1fZ):E(_1fZ);},_1g3={_:0,a:_1as,b:_1f6,c:_1fg,d:_1fq,e:_1fA,f:_1fK,g:_1fP,h:_1fW},_1g4=function(_1g5,_1g6,_1g7,_1g8){switch(B(_1bD(_1g3,_1g5,_1g7))){case 0:return true;case 1:return _1g6<_1g8;default:return false;}},_1g9=function(_1ga,_1gb){var _1gc=E(_1ga),_1gd=E(_1gb);return new F(function(){return _1g4(_1gc.a,_1gc.b,_1gd.a,_1gd.b);});},_1ge=function(_1gf,_1gg,_1gh,_1gi){switch(B(_1bD(_1g3,_1gf,_1gh))){case 0:return true;case 1:return _1gg<=_1gi;default:return false;}},_1gj=function(_1gk,_1gl){var _1gm=E(_1gk),_1gn=E(_1gl);return new F(function(){return _1ge(_1gm.a,_1gm.b,_1gn.a,_1gn.b);});},_1go=function(_1gp,_1gq,_1gr,_1gs){switch(B(_1bD(_1g3,_1gp,_1gr))){case 0:return false;case 1:return _1gq>_1gs;default:return true;}},_1gt=function(_1gu,_1gv){var _1gw=E(_1gu),_1gx=E(_1gv);return new F(function(){return _1go(_1gw.a,_1gw.b,_1gx.a,_1gx.b);});},_1gy=function(_1gz,_1gA,_1gB,_1gC){switch(B(_1bD(_1g3,_1gz,_1gB))){case 0:return false;case 1:return _1gA>=_1gC;default:return true;}},_1gD=function(_1gE,_1gF){var _1gG=E(_1gE),_1gH=E(_1gF);return new F(function(){return _1gy(_1gG.a,_1gG.b,_1gH.a,_1gH.b);});},_1gI=function(_1gJ,_1gK,_1gL,_1gM){switch(B(_1bD(_1g3,_1gJ,_1gL))){case 0:return 0;case 1:return new F(function(){return _jc(_1gK,_1gM);});break;default:return 2;}},_1gN=function(_1gO,_1gP){var _1gQ=E(_1gO),_1gR=E(_1gP);return new F(function(){return _1gI(_1gQ.a,_1gQ.b,_1gR.a,_1gR.b);});},_1gS=function(_1gT,_1gU){var _1gV=E(_1gT),_1gW=E(_1gU);switch(B(_1bD(_1g3,_1gV.a,_1gW.a))){case 0:return E(_1gW);case 1:return (_1gV.b>_1gW.b)?E(_1gV):E(_1gW);default:return E(_1gV);}},_1gX=function(_1gY,_1gZ){var _1h0=E(_1gY),_1h1=E(_1gZ);switch(B(_1bD(_1g3,_1h0.a,_1h1.a))){case 0:return E(_1h0);case 1:return (_1h0.b>_1h1.b)?E(_1h1):E(_1h0);default:return E(_1h1);}},_1h2={_:0,a:_1aI,b:_1gN,c:_1g9,d:_1gj,e:_1gt,f:_1gD,g:_1gS,h:_1gX},_1h3=function(_1h4,_1h5){while(1){var _1h6=E(_1h4);if(!_1h6._){return (E(_1h5)._==0)?1:0;}else{var _1h7=E(_1h5);if(!_1h7._){return 2;}else{var _1h8=B(_12d(_1h6.a,_1h7.a));if(_1h8==1){_1h4=_1h6.b;_1h5=_1h7.b;continue;}else{return E(_1h8);}}}}},_1h9=function(_1ha,_1hb){return (B(_1h3(_1ha,_1hb))==0)?true:false;},_1hc=function(_1hd,_1he){var _1hf=E(_1hd);switch(_1hf._){case 0:var _1hg=_1hf.a,_1hh=E(_1he);if(!_1hh._){var _1hi=_1hh.a;return (_1hg>=_1hi)?(_1hg!=_1hi)?false:(B(_1bD(_1h2,_1hf.b,_1hh.b))==0)?true:false:true;}else{return true;}break;case 1:var _1hj=E(_1he);switch(_1hj._){case 0:return false;case 1:return _1hf.a<_1hj.a;default:return true;}break;default:var _1hk=E(_1he);if(_1hk._==2){var _1hl=E(_1hf.a),_1hm=E(_1hk.a);switch(B(_12T(_1hl.a,_1hl.b,_1hl.c,_1hm.a,_1hm.b,_1hm.c))){case 0:return true;case 1:switch(B(_1bl(_1hf.b,_1hk.b))){case 0:return true;case 1:return new F(function(){return _1h9(_1hf.c,_1hk.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1hn=function(_1ho,_1hp){return (B(_1h3(_1ho,_1hp))==2)?false:true;},_1hq=function(_1hr,_1hs){var _1ht=E(_1hr);switch(_1ht._){case 0:var _1hu=_1ht.a,_1hv=E(_1hs);if(!_1hv._){var _1hw=_1hv.a;return (_1hu>=_1hw)?(_1hu!=_1hw)?false:(B(_1bD(_1h2,_1ht.b,_1hv.b))==2)?false:true:true;}else{return true;}break;case 1:var _1hx=E(_1hs);switch(_1hx._){case 0:return false;case 1:return _1ht.a<=_1hx.a;default:return true;}break;default:var _1hy=E(_1hs);if(_1hy._==2){var _1hz=E(_1ht.a),_1hA=E(_1hy.a);switch(B(_12T(_1hz.a,_1hz.b,_1hz.c,_1hA.a,_1hA.b,_1hA.c))){case 0:return true;case 1:switch(B(_1bl(_1ht.b,_1hy.b))){case 0:return true;case 1:return new F(function(){return _1hn(_1ht.c,_1hy.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1hB=function(_1hC,_1hD){return (B(_1h3(_1hC,_1hD))==2)?true:false;},_1hE=function(_1hF,_1hG){var _1hH=E(_1hF);switch(_1hH._){case 0:var _1hI=_1hH.a,_1hJ=E(_1hG);if(!_1hJ._){var _1hK=_1hJ.a;return (_1hI>=_1hK)?(_1hI!=_1hK)?true:(B(_1bD(_1h2,_1hH.b,_1hJ.b))==2)?true:false:false;}else{return false;}break;case 1:var _1hL=E(_1hG);switch(_1hL._){case 0:return true;case 1:return _1hH.a>_1hL.a;default:return false;}break;default:var _1hM=E(_1hG);if(_1hM._==2){var _1hN=E(_1hH.a),_1hO=E(_1hM.a);switch(B(_12T(_1hN.a,_1hN.b,_1hN.c,_1hO.a,_1hO.b,_1hO.c))){case 0:return false;case 1:switch(B(_1bl(_1hH.b,_1hM.b))){case 0:return false;case 1:return new F(function(){return _1hB(_1hH.c,_1hM.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1hP=function(_1hQ,_1hR){return (B(_1h3(_1hQ,_1hR))==0)?false:true;},_1hS=function(_1hT,_1hU){var _1hV=E(_1hT);switch(_1hV._){case 0:var _1hW=_1hV.a,_1hX=E(_1hU);if(!_1hX._){var _1hY=_1hX.a;return (_1hW>=_1hY)?(_1hW!=_1hY)?true:(B(_1bD(_1h2,_1hV.b,_1hX.b))==0)?false:true:false;}else{return false;}break;case 1:var _1hZ=E(_1hU);switch(_1hZ._){case 0:return true;case 1:return _1hV.a>=_1hZ.a;default:return false;}break;default:var _1i0=E(_1hU);if(_1i0._==2){var _1i1=E(_1hV.a),_1i2=E(_1i0.a);switch(B(_12T(_1i1.a,_1i1.b,_1i1.c,_1i2.a,_1i2.b,_1i2.c))){case 0:return false;case 1:switch(B(_1bl(_1hV.b,_1i0.b))){case 0:return false;case 1:return new F(function(){return _1hP(_1hV.c,_1i0.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1i3=function(_1i4,_1i5){var _1i6=E(_1i4);switch(_1i6._){case 0:var _1i7=_1i6.a,_1i8=E(_1i5);if(!_1i8._){var _1i9=_1i8.a;if(_1i7>=_1i9){if(_1i7!=_1i9){return 2;}else{return new F(function(){return _1bD(_1h2,_1i6.b,_1i8.b);});}}else{return 0;}}else{return 0;}break;case 1:var _1ia=E(_1i5);switch(_1ia._){case 0:return 2;case 1:return new F(function(){return _jc(_1i6.a,_1ia.a);});break;default:return 0;}break;default:var _1ib=E(_1i5);if(_1ib._==2){var _1ic=E(_1i6.a),_1id=E(_1ib.a);switch(B(_12T(_1ic.a,_1ic.b,_1ic.c,_1id.a,_1id.b,_1id.c))){case 0:return 0;case 1:switch(B(_1bl(_1i6.b,_1ib.b))){case 0:return 0;case 1:return new F(function(){return _1h3(_1i6.c,_1ib.c);});break;default:return 2;}break;default:return 2;}}else{return 2;}}},_1ie=function(_1if,_1ig){return (!B(_1hq(_1if,_1ig)))?E(_1if):E(_1ig);},_1ih=function(_1ii,_1ij){return (!B(_1hq(_1ii,_1ij)))?E(_1ij):E(_1ii);},_1ik={_:0,a:_1b0,b:_1i3,c:_1hc,d:_1hq,e:_1hE,f:_1hS,g:_1ie,h:_1ih},_1il=__Z,_1im=function(_1in,_1io,_1ip){var _1iq=E(_1io);if(!_1iq._){return E(_1ip);}else{var _1ir=function(_1is,_1it){while(1){var _1iu=E(_1it);if(!_1iu._){var _1iv=_1iu.b,_1iw=_1iu.d;switch(B(A3(_13n,_1in,_1is,_1iv))){case 0:return new F(function(){return _OM(_1iv,B(_1ir(_1is,_1iu.c)),_1iw);});break;case 1:return E(_1iw);default:_1it=_1iw;continue;}}else{return new T0(1);}}};return new F(function(){return _1ir(_1iq.a,_1ip);});}},_1ix=function(_1iy,_1iz,_1iA){var _1iB=E(_1iz);if(!_1iB._){return E(_1iA);}else{var _1iC=function(_1iD,_1iE){while(1){var _1iF=E(_1iE);if(!_1iF._){var _1iG=_1iF.b,_1iH=_1iF.c;switch(B(A3(_13n,_1iy,_1iG,_1iD))){case 0:return new F(function(){return _OM(_1iG,_1iH,B(_1iC(_1iD,_1iF.d)));});break;case 1:return E(_1iH);default:_1iE=_1iH;continue;}}else{return new T0(1);}}};return new F(function(){return _1iC(_1iB.a,_1iA);});}},_1iI=function(_1iJ,_1iK,_1iL){var _1iM=E(_1iK),_1iN=E(_1iL);if(!_1iN._){var _1iO=_1iN.b,_1iP=_1iN.c,_1iQ=_1iN.d;switch(B(A3(_13n,_1iJ,_1iM,_1iO))){case 0:return new F(function(){return _MQ(_1iO,B(_1iI(_1iJ,_1iM,_1iP)),_1iQ);});break;case 1:return E(_1iN);default:return new F(function(){return _Ns(_1iO,_1iP,B(_1iI(_1iJ,_1iM,_1iQ)));});}}else{return new T4(0,1,E(_1iM),E(_ML),E(_ML));}},_1iR=function(_1iS,_1iT,_1iU){return new F(function(){return _1iI(_1iS,_1iT,_1iU);});},_1iV=function(_1iW,_1iX,_1iY,_1iZ){var _1j0=E(_1iX);if(!_1j0._){var _1j1=E(_1iY);if(!_1j1._){return E(_1iZ);}else{var _1j2=function(_1j3,_1j4){while(1){var _1j5=E(_1j4);if(!_1j5._){if(!B(A3(_16p,_1iW,_1j5.b,_1j3))){return E(_1j5);}else{_1j4=_1j5.c;continue;}}else{return new T0(1);}}};return new F(function(){return _1j2(_1j1.a,_1iZ);});}}else{var _1j6=_1j0.a,_1j7=E(_1iY);if(!_1j7._){var _1j8=function(_1j9,_1ja){while(1){var _1jb=E(_1ja);if(!_1jb._){if(!B(A3(_178,_1iW,_1jb.b,_1j9))){return E(_1jb);}else{_1ja=_1jb.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1j8(_1j6,_1iZ);});}else{var _1jc=function(_1jd,_1je,_1jf){while(1){var _1jg=E(_1jf);if(!_1jg._){var _1jh=_1jg.b;if(!B(A3(_178,_1iW,_1jh,_1jd))){if(!B(A3(_16p,_1iW,_1jh,_1je))){return E(_1jg);}else{_1jf=_1jg.c;continue;}}else{_1jf=_1jg.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1jc(_1j6,_1j7.a,_1iZ);});}}},_1ji=function(_1jj,_1jk,_1jl,_1jm,_1jn){var _1jo=E(_1jn);if(!_1jo._){var _1jp=_1jo.b,_1jq=_1jo.c,_1jr=_1jo.d,_1js=E(_1jm);if(!_1js._){var _1jt=_1js.b,_1ju=function(_1jv){var _1jw=new T1(1,E(_1jt));return new F(function(){return _OM(_1jt,B(_1ji(_1jj,_1jk,_1jw,_1js.c,B(_1iV(_1jj,_1jk,_1jw,_1jo)))),B(_1ji(_1jj,_1jw,_1jl,_1js.d,B(_1iV(_1jj,_1jw,_1jl,_1jo)))));});};if(!E(_1jq)._){return new F(function(){return _1ju(_);});}else{if(!E(_1jr)._){return new F(function(){return _1ju(_);});}else{return new F(function(){return _1iR(_1jj,_1jp,_1js);});}}}else{return new F(function(){return _OM(_1jp,B(_1im(_1jj,_1jk,_1jq)),B(_1ix(_1jj,_1jl,_1jr)));});}}else{return E(_1jm);}},_1jx=function(_1jy,_1jz,_1jA,_1jB,_1jC,_1jD,_1jE,_1jF,_1jG,_1jH,_1jI){var _1jJ=function(_1jK){var _1jL=new T1(1,E(_1jC));return new F(function(){return _OM(_1jC,B(_1ji(_1jy,_1jz,_1jL,_1jD,B(_1iV(_1jy,_1jz,_1jL,new T4(0,_1jF,E(_1jG),E(_1jH),E(_1jI)))))),B(_1ji(_1jy,_1jL,_1jA,_1jE,B(_1iV(_1jy,_1jL,_1jA,new T4(0,_1jF,E(_1jG),E(_1jH),E(_1jI)))))));});};if(!E(_1jH)._){return new F(function(){return _1jJ(_);});}else{if(!E(_1jI)._){return new F(function(){return _1jJ(_);});}else{return new F(function(){return _1iR(_1jy,_1jG,new T4(0,_1jB,E(_1jC),E(_1jD),E(_1jE)));});}}},_1jM=function(_1jN,_1jO,_1jP){var _1jQ=E(_1jO);if(!_1jQ._){var _1jR=E(_1jP);if(!_1jR._){return new F(function(){return _1jx(_1ik,_1il,_1il,_1jQ.a,_1jQ.b,_1jQ.c,_1jQ.d,_1jR.a,_1jR.b,_1jR.c,_1jR.d);});}else{return E(_1jQ);}}else{return E(_1jP);}},_1jS=function(_1jT,_1jU,_1jV){var _1jW=function(_1jX,_1jY,_1jZ,_1k0){var _1k1=E(_1k0);switch(_1k1._){case 0:var _1k2=_1k1.a,_1k3=_1k1.b,_1k4=_1k1.c,_1k5=_1k1.d,_1k6=_1k3>>>0;if(((_1jZ>>>0&((_1k6-1>>>0^4294967295)>>>0^_1k6)>>>0)>>>0&4294967295)==_1k2){return ((_1jZ>>>0&_1k6)>>>0==0)?new T4(0,_1k2,_1k3,E(B(_1jW(_1jX,_1jY,_1jZ,_1k4))),E(_1k5)):new T4(0,_1k2,_1k3,E(_1k4),E(B(_1jW(_1jX,_1jY,_1jZ,_1k5))));}else{var _1k7=(_1jZ>>>0^_1k2>>>0)>>>0,_1k8=(_1k7|_1k7>>>1)>>>0,_1k9=(_1k8|_1k8>>>2)>>>0,_1ka=(_1k9|_1k9>>>4)>>>0,_1kb=(_1ka|_1ka>>>8)>>>0,_1kc=(_1kb|_1kb>>>16)>>>0,_1kd=(_1kc^_1kc>>>1)>>>0&4294967295,_1ke=_1kd>>>0;return ((_1jZ>>>0&_1ke)>>>0==0)?new T4(0,(_1jZ>>>0&((_1ke-1>>>0^4294967295)>>>0^_1ke)>>>0)>>>0&4294967295,_1kd,E(new T2(1,_1jX,_1jY)),E(_1k1)):new T4(0,(_1jZ>>>0&((_1ke-1>>>0^4294967295)>>>0^_1ke)>>>0)>>>0&4294967295,_1kd,E(_1k1),E(new T2(1,_1jX,_1jY)));}break;case 1:var _1kf=_1k1.a;if(_1jZ!=_1kf){var _1kg=(_1jZ>>>0^_1kf>>>0)>>>0,_1kh=(_1kg|_1kg>>>1)>>>0,_1ki=(_1kh|_1kh>>>2)>>>0,_1kj=(_1ki|_1ki>>>4)>>>0,_1kk=(_1kj|_1kj>>>8)>>>0,_1kl=(_1kk|_1kk>>>16)>>>0,_1km=(_1kl^_1kl>>>1)>>>0&4294967295,_1kn=_1km>>>0;return ((_1jZ>>>0&_1kn)>>>0==0)?new T4(0,(_1jZ>>>0&((_1kn-1>>>0^4294967295)>>>0^_1kn)>>>0)>>>0&4294967295,_1km,E(new T2(1,_1jX,_1jY)),E(_1k1)):new T4(0,(_1jZ>>>0&((_1kn-1>>>0^4294967295)>>>0^_1kn)>>>0)>>>0&4294967295,_1km,E(_1k1),E(new T2(1,_1jX,_1jY)));}else{return new T2(1,_1jX,new T(function(){return B(A3(_1jT,_1jX,_1jY,_1k1.b));}));}break;default:return new T2(1,_1jX,_1jY);}},_1ko=function(_1kp,_1kq,_1kr,_1ks){var _1kt=E(_1ks);switch(_1kt._){case 0:var _1ku=_1kt.a,_1kv=_1kt.b,_1kw=_1kt.c,_1kx=_1kt.d,_1ky=_1kv>>>0;if(((_1kr>>>0&((_1ky-1>>>0^4294967295)>>>0^_1ky)>>>0)>>>0&4294967295)==_1ku){return ((_1kr>>>0&_1ky)>>>0==0)?new T4(0,_1ku,_1kv,E(B(_1ko(_1kp,_1kq,_1kr,_1kw))),E(_1kx)):new T4(0,_1ku,_1kv,E(_1kw),E(B(_1ko(_1kp,_1kq,_1kr,_1kx))));}else{var _1kz=(_1ku>>>0^_1kr>>>0)>>>0,_1kA=(_1kz|_1kz>>>1)>>>0,_1kB=(_1kA|_1kA>>>2)>>>0,_1kC=(_1kB|_1kB>>>4)>>>0,_1kD=(_1kC|_1kC>>>8)>>>0,_1kE=(_1kD|_1kD>>>16)>>>0,_1kF=(_1kE^_1kE>>>1)>>>0&4294967295,_1kG=_1kF>>>0;return ((_1ku>>>0&_1kG)>>>0==0)?new T4(0,(_1ku>>>0&((_1kG-1>>>0^4294967295)>>>0^_1kG)>>>0)>>>0&4294967295,_1kF,E(_1kt),E(new T2(1,_1kp,_1kq))):new T4(0,(_1ku>>>0&((_1kG-1>>>0^4294967295)>>>0^_1kG)>>>0)>>>0&4294967295,_1kF,E(new T2(1,_1kp,_1kq)),E(_1kt));}break;case 1:var _1kH=_1kt.a;if(_1kH!=_1kr){var _1kI=(_1kH>>>0^_1kr>>>0)>>>0,_1kJ=(_1kI|_1kI>>>1)>>>0,_1kK=(_1kJ|_1kJ>>>2)>>>0,_1kL=(_1kK|_1kK>>>4)>>>0,_1kM=(_1kL|_1kL>>>8)>>>0,_1kN=(_1kM|_1kM>>>16)>>>0,_1kO=(_1kN^_1kN>>>1)>>>0&4294967295,_1kP=_1kO>>>0;return ((_1kH>>>0&_1kP)>>>0==0)?new T4(0,(_1kH>>>0&((_1kP-1>>>0^4294967295)>>>0^_1kP)>>>0)>>>0&4294967295,_1kO,E(_1kt),E(new T2(1,_1kp,_1kq))):new T4(0,(_1kH>>>0&((_1kP-1>>>0^4294967295)>>>0^_1kP)>>>0)>>>0&4294967295,_1kO,E(new T2(1,_1kp,_1kq)),E(_1kt));}else{return new T2(1,_1kH,new T(function(){return B(A3(_1jT,_1kH,_1kt.b,_1kq));}));}break;default:return new T2(1,_1kp,_1kq);}},_1kQ=function(_1kR,_1kS,_1kT,_1kU,_1kV,_1kW,_1kX){var _1kY=_1kV>>>0;if(((_1kT>>>0&((_1kY-1>>>0^4294967295)>>>0^_1kY)>>>0)>>>0&4294967295)==_1kU){return ((_1kT>>>0&_1kY)>>>0==0)?new T4(0,_1kU,_1kV,E(B(_1ko(_1kR,_1kS,_1kT,_1kW))),E(_1kX)):new T4(0,_1kU,_1kV,E(_1kW),E(B(_1ko(_1kR,_1kS,_1kT,_1kX))));}else{var _1kZ=(_1kU>>>0^_1kT>>>0)>>>0,_1l0=(_1kZ|_1kZ>>>1)>>>0,_1l1=(_1l0|_1l0>>>2)>>>0,_1l2=(_1l1|_1l1>>>4)>>>0,_1l3=(_1l2|_1l2>>>8)>>>0,_1l4=(_1l3|_1l3>>>16)>>>0,_1l5=(_1l4^_1l4>>>1)>>>0&4294967295,_1l6=_1l5>>>0;return ((_1kU>>>0&_1l6)>>>0==0)?new T4(0,(_1kU>>>0&((_1l6-1>>>0^4294967295)>>>0^_1l6)>>>0)>>>0&4294967295,_1l5,E(new T4(0,_1kU,_1kV,E(_1kW),E(_1kX))),E(new T2(1,_1kR,_1kS))):new T4(0,(_1kU>>>0&((_1l6-1>>>0^4294967295)>>>0^_1l6)>>>0)>>>0&4294967295,_1l5,E(new T2(1,_1kR,_1kS)),E(new T4(0,_1kU,_1kV,E(_1kW),E(_1kX))));}},_1l7=function(_1l8,_1l9){var _1la=E(_1l8);switch(_1la._){case 0:var _1lb=_1la.a,_1lc=_1la.b,_1ld=_1la.c,_1le=_1la.d,_1lf=E(_1l9);switch(_1lf._){case 0:var _1lg=_1lf.a,_1lh=_1lf.b,_1li=_1lf.c,_1lj=_1lf.d;if(_1lc>>>0<=_1lh>>>0){if(_1lh>>>0<=_1lc>>>0){if(_1lb!=_1lg){var _1lk=(_1lb>>>0^_1lg>>>0)>>>0,_1ll=(_1lk|_1lk>>>1)>>>0,_1lm=(_1ll|_1ll>>>2)>>>0,_1ln=(_1lm|_1lm>>>4)>>>0,_1lo=(_1ln|_1ln>>>8)>>>0,_1lp=(_1lo|_1lo>>>16)>>>0,_1lq=(_1lp^_1lp>>>1)>>>0&4294967295,_1lr=_1lq>>>0;return ((_1lb>>>0&_1lr)>>>0==0)?new T4(0,(_1lb>>>0&((_1lr-1>>>0^4294967295)>>>0^_1lr)>>>0)>>>0&4294967295,_1lq,E(_1la),E(_1lf)):new T4(0,(_1lb>>>0&((_1lr-1>>>0^4294967295)>>>0^_1lr)>>>0)>>>0&4294967295,_1lq,E(_1lf),E(_1la));}else{return new T4(0,_1lb,_1lc,E(B(_1l7(_1ld,_1li))),E(B(_1l7(_1le,_1lj))));}}else{var _1ls=_1lh>>>0;if(((_1lb>>>0&((_1ls-1>>>0^4294967295)>>>0^_1ls)>>>0)>>>0&4294967295)==_1lg){return ((_1lb>>>0&_1ls)>>>0==0)?new T4(0,_1lg,_1lh,E(B(_1lt(_1lb,_1lc,_1ld,_1le,_1li))),E(_1lj)):new T4(0,_1lg,_1lh,E(_1li),E(B(_1lt(_1lb,_1lc,_1ld,_1le,_1lj))));}else{var _1lu=(_1lb>>>0^_1lg>>>0)>>>0,_1lv=(_1lu|_1lu>>>1)>>>0,_1lw=(_1lv|_1lv>>>2)>>>0,_1lx=(_1lw|_1lw>>>4)>>>0,_1ly=(_1lx|_1lx>>>8)>>>0,_1lz=(_1ly|_1ly>>>16)>>>0,_1lA=(_1lz^_1lz>>>1)>>>0&4294967295,_1lB=_1lA>>>0;return ((_1lb>>>0&_1lB)>>>0==0)?new T4(0,(_1lb>>>0&((_1lB-1>>>0^4294967295)>>>0^_1lB)>>>0)>>>0&4294967295,_1lA,E(_1la),E(_1lf)):new T4(0,(_1lb>>>0&((_1lB-1>>>0^4294967295)>>>0^_1lB)>>>0)>>>0&4294967295,_1lA,E(_1lf),E(_1la));}}}else{var _1lC=_1lc>>>0;if(((_1lg>>>0&((_1lC-1>>>0^4294967295)>>>0^_1lC)>>>0)>>>0&4294967295)==_1lb){return ((_1lg>>>0&_1lC)>>>0==0)?new T4(0,_1lb,_1lc,E(B(_1lD(_1ld,_1lg,_1lh,_1li,_1lj))),E(_1le)):new T4(0,_1lb,_1lc,E(_1ld),E(B(_1lD(_1le,_1lg,_1lh,_1li,_1lj))));}else{var _1lE=(_1lb>>>0^_1lg>>>0)>>>0,_1lF=(_1lE|_1lE>>>1)>>>0,_1lG=(_1lF|_1lF>>>2)>>>0,_1lH=(_1lG|_1lG>>>4)>>>0,_1lI=(_1lH|_1lH>>>8)>>>0,_1lJ=(_1lI|_1lI>>>16)>>>0,_1lK=(_1lJ^_1lJ>>>1)>>>0&4294967295,_1lL=_1lK>>>0;return ((_1lb>>>0&_1lL)>>>0==0)?new T4(0,(_1lb>>>0&((_1lL-1>>>0^4294967295)>>>0^_1lL)>>>0)>>>0&4294967295,_1lK,E(_1la),E(_1lf)):new T4(0,(_1lb>>>0&((_1lL-1>>>0^4294967295)>>>0^_1lL)>>>0)>>>0&4294967295,_1lK,E(_1lf),E(_1la));}}break;case 1:var _1lM=_1lf.a;return new F(function(){return _1kQ(_1lM,_1lf.b,_1lM,_1lb,_1lc,_1ld,_1le);});break;default:return E(_1la);}break;case 1:var _1lN=_1la.a;return new F(function(){return _1jW(_1lN,_1la.b,_1lN,_1l9);});break;default:return E(_1l9);}},_1lt=function(_1lO,_1lP,_1lQ,_1lR,_1lS){var _1lT=E(_1lS);switch(_1lT._){case 0:var _1lU=_1lT.a,_1lV=_1lT.b,_1lW=_1lT.c,_1lX=_1lT.d;if(_1lP>>>0<=_1lV>>>0){if(_1lV>>>0<=_1lP>>>0){if(_1lO!=_1lU){var _1lY=(_1lO>>>0^_1lU>>>0)>>>0,_1lZ=(_1lY|_1lY>>>1)>>>0,_1m0=(_1lZ|_1lZ>>>2)>>>0,_1m1=(_1m0|_1m0>>>4)>>>0,_1m2=(_1m1|_1m1>>>8)>>>0,_1m3=(_1m2|_1m2>>>16)>>>0,_1m4=(_1m3^_1m3>>>1)>>>0&4294967295,_1m5=_1m4>>>0;return ((_1lO>>>0&_1m5)>>>0==0)?new T4(0,(_1lO>>>0&((_1m5-1>>>0^4294967295)>>>0^_1m5)>>>0)>>>0&4294967295,_1m4,E(new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR))),E(_1lT)):new T4(0,(_1lO>>>0&((_1m5-1>>>0^4294967295)>>>0^_1m5)>>>0)>>>0&4294967295,_1m4,E(_1lT),E(new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR))));}else{return new T4(0,_1lO,_1lP,E(B(_1l7(_1lQ,_1lW))),E(B(_1l7(_1lR,_1lX))));}}else{var _1m6=_1lV>>>0;if(((_1lO>>>0&((_1m6-1>>>0^4294967295)>>>0^_1m6)>>>0)>>>0&4294967295)==_1lU){return ((_1lO>>>0&_1m6)>>>0==0)?new T4(0,_1lU,_1lV,E(B(_1lt(_1lO,_1lP,_1lQ,_1lR,_1lW))),E(_1lX)):new T4(0,_1lU,_1lV,E(_1lW),E(B(_1lt(_1lO,_1lP,_1lQ,_1lR,_1lX))));}else{var _1m7=(_1lO>>>0^_1lU>>>0)>>>0,_1m8=(_1m7|_1m7>>>1)>>>0,_1m9=(_1m8|_1m8>>>2)>>>0,_1ma=(_1m9|_1m9>>>4)>>>0,_1mb=(_1ma|_1ma>>>8)>>>0,_1mc=(_1mb|_1mb>>>16)>>>0,_1md=(_1mc^_1mc>>>1)>>>0&4294967295,_1me=_1md>>>0;return ((_1lO>>>0&_1me)>>>0==0)?new T4(0,(_1lO>>>0&((_1me-1>>>0^4294967295)>>>0^_1me)>>>0)>>>0&4294967295,_1md,E(new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR))),E(_1lT)):new T4(0,(_1lO>>>0&((_1me-1>>>0^4294967295)>>>0^_1me)>>>0)>>>0&4294967295,_1md,E(_1lT),E(new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR))));}}}else{var _1mf=_1lP>>>0;if(((_1lU>>>0&((_1mf-1>>>0^4294967295)>>>0^_1mf)>>>0)>>>0&4294967295)==_1lO){return ((_1lU>>>0&_1mf)>>>0==0)?new T4(0,_1lO,_1lP,E(B(_1lD(_1lQ,_1lU,_1lV,_1lW,_1lX))),E(_1lR)):new T4(0,_1lO,_1lP,E(_1lQ),E(B(_1lD(_1lR,_1lU,_1lV,_1lW,_1lX))));}else{var _1mg=(_1lO>>>0^_1lU>>>0)>>>0,_1mh=(_1mg|_1mg>>>1)>>>0,_1mi=(_1mh|_1mh>>>2)>>>0,_1mj=(_1mi|_1mi>>>4)>>>0,_1mk=(_1mj|_1mj>>>8)>>>0,_1ml=(_1mk|_1mk>>>16)>>>0,_1mm=(_1ml^_1ml>>>1)>>>0&4294967295,_1mn=_1mm>>>0;return ((_1lO>>>0&_1mn)>>>0==0)?new T4(0,(_1lO>>>0&((_1mn-1>>>0^4294967295)>>>0^_1mn)>>>0)>>>0&4294967295,_1mm,E(new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR))),E(_1lT)):new T4(0,(_1lO>>>0&((_1mn-1>>>0^4294967295)>>>0^_1mn)>>>0)>>>0&4294967295,_1mm,E(_1lT),E(new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR))));}}break;case 1:var _1mo=_1lT.a;return new F(function(){return _1kQ(_1mo,_1lT.b,_1mo,_1lO,_1lP,_1lQ,_1lR);});break;default:return new T4(0,_1lO,_1lP,E(_1lQ),E(_1lR));}},_1lD=function(_1mp,_1mq,_1mr,_1ms,_1mt){var _1mu=E(_1mp);switch(_1mu._){case 0:var _1mv=_1mu.a,_1mw=_1mu.b,_1mx=_1mu.c,_1my=_1mu.d;if(_1mw>>>0<=_1mr>>>0){if(_1mr>>>0<=_1mw>>>0){if(_1mv!=_1mq){var _1mz=(_1mv>>>0^_1mq>>>0)>>>0,_1mA=(_1mz|_1mz>>>1)>>>0,_1mB=(_1mA|_1mA>>>2)>>>0,_1mC=(_1mB|_1mB>>>4)>>>0,_1mD=(_1mC|_1mC>>>8)>>>0,_1mE=(_1mD|_1mD>>>16)>>>0,_1mF=(_1mE^_1mE>>>1)>>>0&4294967295,_1mG=_1mF>>>0;return ((_1mv>>>0&_1mG)>>>0==0)?new T4(0,(_1mv>>>0&((_1mG-1>>>0^4294967295)>>>0^_1mG)>>>0)>>>0&4294967295,_1mF,E(_1mu),E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt)))):new T4(0,(_1mv>>>0&((_1mG-1>>>0^4294967295)>>>0^_1mG)>>>0)>>>0&4294967295,_1mF,E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt))),E(_1mu));}else{return new T4(0,_1mv,_1mw,E(B(_1l7(_1mx,_1ms))),E(B(_1l7(_1my,_1mt))));}}else{var _1mH=_1mr>>>0;if(((_1mv>>>0&((_1mH-1>>>0^4294967295)>>>0^_1mH)>>>0)>>>0&4294967295)==_1mq){return ((_1mv>>>0&_1mH)>>>0==0)?new T4(0,_1mq,_1mr,E(B(_1lt(_1mv,_1mw,_1mx,_1my,_1ms))),E(_1mt)):new T4(0,_1mq,_1mr,E(_1ms),E(B(_1lt(_1mv,_1mw,_1mx,_1my,_1mt))));}else{var _1mI=(_1mv>>>0^_1mq>>>0)>>>0,_1mJ=(_1mI|_1mI>>>1)>>>0,_1mK=(_1mJ|_1mJ>>>2)>>>0,_1mL=(_1mK|_1mK>>>4)>>>0,_1mM=(_1mL|_1mL>>>8)>>>0,_1mN=(_1mM|_1mM>>>16)>>>0,_1mO=(_1mN^_1mN>>>1)>>>0&4294967295,_1mP=_1mO>>>0;return ((_1mv>>>0&_1mP)>>>0==0)?new T4(0,(_1mv>>>0&((_1mP-1>>>0^4294967295)>>>0^_1mP)>>>0)>>>0&4294967295,_1mO,E(_1mu),E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt)))):new T4(0,(_1mv>>>0&((_1mP-1>>>0^4294967295)>>>0^_1mP)>>>0)>>>0&4294967295,_1mO,E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt))),E(_1mu));}}}else{var _1mQ=_1mw>>>0;if(((_1mq>>>0&((_1mQ-1>>>0^4294967295)>>>0^_1mQ)>>>0)>>>0&4294967295)==_1mv){return ((_1mq>>>0&_1mQ)>>>0==0)?new T4(0,_1mv,_1mw,E(B(_1lD(_1mx,_1mq,_1mr,_1ms,_1mt))),E(_1my)):new T4(0,_1mv,_1mw,E(_1mx),E(B(_1lD(_1my,_1mq,_1mr,_1ms,_1mt))));}else{var _1mR=(_1mv>>>0^_1mq>>>0)>>>0,_1mS=(_1mR|_1mR>>>1)>>>0,_1mT=(_1mS|_1mS>>>2)>>>0,_1mU=(_1mT|_1mT>>>4)>>>0,_1mV=(_1mU|_1mU>>>8)>>>0,_1mW=(_1mV|_1mV>>>16)>>>0,_1mX=(_1mW^_1mW>>>1)>>>0&4294967295,_1mY=_1mX>>>0;return ((_1mv>>>0&_1mY)>>>0==0)?new T4(0,(_1mv>>>0&((_1mY-1>>>0^4294967295)>>>0^_1mY)>>>0)>>>0&4294967295,_1mX,E(_1mu),E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt)))):new T4(0,(_1mv>>>0&((_1mY-1>>>0^4294967295)>>>0^_1mY)>>>0)>>>0&4294967295,_1mX,E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt))),E(_1mu));}}break;case 1:var _1mZ=_1mu.a,_1n0=_1mu.b,_1n1=_1mr>>>0;if(((_1mZ>>>0&((_1n1-1>>>0^4294967295)>>>0^_1n1)>>>0)>>>0&4294967295)==_1mq){return ((_1mZ>>>0&_1n1)>>>0==0)?new T4(0,_1mq,_1mr,E(B(_1jW(_1mZ,_1n0,_1mZ,_1ms))),E(_1mt)):new T4(0,_1mq,_1mr,E(_1ms),E(B(_1jW(_1mZ,_1n0,_1mZ,_1mt))));}else{var _1n2=(_1mZ>>>0^_1mq>>>0)>>>0,_1n3=(_1n2|_1n2>>>1)>>>0,_1n4=(_1n3|_1n3>>>2)>>>0,_1n5=(_1n4|_1n4>>>4)>>>0,_1n6=(_1n5|_1n5>>>8)>>>0,_1n7=(_1n6|_1n6>>>16)>>>0,_1n8=(_1n7^_1n7>>>1)>>>0&4294967295,_1n9=_1n8>>>0;return ((_1mZ>>>0&_1n9)>>>0==0)?new T4(0,(_1mZ>>>0&((_1n9-1>>>0^4294967295)>>>0^_1n9)>>>0)>>>0&4294967295,_1n8,E(new T2(1,_1mZ,_1n0)),E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt)))):new T4(0,(_1mZ>>>0&((_1n9-1>>>0^4294967295)>>>0^_1n9)>>>0)>>>0&4294967295,_1n8,E(new T4(0,_1mq,_1mr,E(_1ms),E(_1mt))),E(new T2(1,_1mZ,_1n0)));}break;default:return new T4(0,_1mq,_1mr,E(_1ms),E(_1mt));}};return new F(function(){return _1l7(_1jU,_1jV);});},_1na=function(_1nb,_1nc,_1nd){return new F(function(){return _1jS(_1jM,_1nc,_1nd);});},_1ne=function(_1nf,_1ng){return E(_1nf);},_1nh=new T2(0,_4l,_Rg),_1ni=function(_1nj,_1nk){while(1){var _1nl=B((function(_1nm,_1nn){var _1no=E(_1nn);if(!_1no._){_1nj=new T2(1,_1no.b,new T(function(){return B(_1ni(_1nm,_1no.d));}));_1nk=_1no.c;return __continue;}else{return E(_1nm);}})(_1nj,_1nk));if(_1nl!=__continue){return _1nl;}}},_1np=function(_1nq,_1nr,_1ns){var _1nt=function(_1nu){var _1nv=function(_1nw){if(_1nu!=_1nw){return false;}else{return new F(function(){return _18O(_1nq,B(_1ni(_4,_1nr)),B(_1ni(_4,_1ns)));});}},_1nx=E(_1ns);if(!_1nx._){return new F(function(){return _1nv(_1nx.a);});}else{return new F(function(){return _1nv(0);});}},_1ny=E(_1nr);if(!_1ny._){return new F(function(){return _1nt(_1ny.a);});}else{return new F(function(){return _1nt(0);});}},_1nz=function(_1nA,_1nB){return (!B(_1np(_1b0,_1nA,_1nB)))?true:false;},_1nC=function(_1nD,_1nE){return new F(function(){return _1np(_1b0,_1nD,_1nE);});},_1nF=new T2(0,_1nC,_1nz),_1nG=function(_1nH,_1nI){var _1nJ=function(_1nK){while(1){var _1nL=E(_1nK);switch(_1nL._){case 0:var _1nM=_1nL.b>>>0;if(((_1nH>>>0&((_1nM-1>>>0^4294967295)>>>0^_1nM)>>>0)>>>0&4294967295)==_1nL.a){if(!((_1nH>>>0&_1nM)>>>0)){_1nK=_1nL.c;continue;}else{_1nK=_1nL.d;continue;}}else{return false;}break;case 1:return _1nH==_1nL.a;default:return false;}}};return new F(function(){return _1nJ(_1nI);});},_1nN=function(_1nO,_1nP){var _1nQ=function(_1nR){while(1){var _1nS=E(_1nR);switch(_1nS._){case 0:var _1nT=_1nS.b>>>0;if(((_1nO>>>0&((_1nT-1>>>0^4294967295)>>>0^_1nT)>>>0)>>>0&4294967295)==_1nS.a){if(!((_1nO>>>0&_1nT)>>>0)){_1nR=_1nS.c;continue;}else{_1nR=_1nS.d;continue;}}else{return false;}break;case 1:return ((_1nO&(-32))!=_1nS.a)?false:((1<<(_1nO&31)>>>0&_1nS.b)>>>0==0)?false:true;default:return false;}}};return new F(function(){return _1nQ(_1nP);});},_1nU=function(_1nV,_1nW,_1nX){while(1){var _1nY=E(_1nW);switch(_1nY._){case 0:var _1nZ=E(_1nX);if(!_1nZ._){if(_1nY.b!=_1nZ.b){return false;}else{if(_1nY.a!=_1nZ.a){return false;}else{if(!B(_1nU(_1nV,_1nY.c,_1nZ.c))){return false;}else{_1nW=_1nY.d;_1nX=_1nZ.d;continue;}}}}else{return false;}break;case 1:var _1o0=E(_1nX);if(_1o0._==1){if(_1nY.a!=_1o0.a){return false;}else{return new F(function(){return A3(_pM,_1nV,_1nY.b,_1o0.b);});}}else{return false;}break;default:return (E(_1nX)._==2)?true:false;}}},_1o1=function(_1o2,_1o3){var _1o4=E(_1o3);if(!_1o4._){var _1o5=_1o4.b,_1o6=_1o4.c,_1o7=_1o4.d;if(!B(A1(_1o2,_1o5))){return new F(function(){return _15N(B(_1o1(_1o2,_1o6)),B(_1o1(_1o2,_1o7)));});}else{return new F(function(){return _OM(_1o5,B(_1o1(_1o2,_1o6)),B(_1o1(_1o2,_1o7)));});}}else{return new T0(1);}},_1o8=function(_1o9,_1oa,_1ob){var _1oc=E(_1ob);switch(_1oc._){case 0:var _1od=_1oc.a,_1oe=_1oc.b,_1of=_1oc.c,_1og=_1oc.d,_1oh=_1oe>>>0;if(((_1o9>>>0&((_1oh-1>>>0^4294967295)>>>0^_1oh)>>>0)>>>0&4294967295)==_1od){return ((_1o9>>>0&_1oh)>>>0==0)?new T4(0,_1od,_1oe,E(B(_1o8(_1o9,_1oa,_1of))),E(_1og)):new T4(0,_1od,_1oe,E(_1of),E(B(_1o8(_1o9,_1oa,_1og))));}else{var _1oi=(_1o9>>>0^_1od>>>0)>>>0,_1oj=(_1oi|_1oi>>>1)>>>0,_1ok=(_1oj|_1oj>>>2)>>>0,_1ol=(_1ok|_1ok>>>4)>>>0,_1om=(_1ol|_1ol>>>8)>>>0,_1on=(_1om|_1om>>>16)>>>0,_1oo=(_1on^_1on>>>1)>>>0&4294967295,_1op=_1oo>>>0;return ((_1o9>>>0&_1op)>>>0==0)?new T4(0,(_1o9>>>0&((_1op-1>>>0^4294967295)>>>0^_1op)>>>0)>>>0&4294967295,_1oo,E(new T2(1,_1o9,_1oa)),E(_1oc)):new T4(0,(_1o9>>>0&((_1op-1>>>0^4294967295)>>>0^_1op)>>>0)>>>0&4294967295,_1oo,E(_1oc),E(new T2(1,_1o9,_1oa)));}break;case 1:var _1oq=_1oc.a;if(_1oq!=_1o9){var _1or=(_1o9>>>0^_1oq>>>0)>>>0,_1os=(_1or|_1or>>>1)>>>0,_1ot=(_1os|_1os>>>2)>>>0,_1ou=(_1ot|_1ot>>>4)>>>0,_1ov=(_1ou|_1ou>>>8)>>>0,_1ow=(_1ov|_1ov>>>16)>>>0,_1ox=(_1ow^_1ow>>>1)>>>0&4294967295,_1oy=_1ox>>>0;return ((_1o9>>>0&_1oy)>>>0==0)?new T4(0,(_1o9>>>0&((_1oy-1>>>0^4294967295)>>>0^_1oy)>>>0)>>>0&4294967295,_1ox,E(new T2(1,_1o9,_1oa)),E(_1oc)):new T4(0,(_1o9>>>0&((_1oy-1>>>0^4294967295)>>>0^_1oy)>>>0)>>>0&4294967295,_1ox,E(_1oc),E(new T2(1,_1o9,_1oa)));}else{return new T2(1,_1oq,(_1oa|_1oc.b)>>>0);}break;default:return new T2(1,_1o9,_1oa);}},_1oz=function(_1oA,_1oB){while(1){var _1oC=E(_1oA);if(!_1oC._){return E(_1oB);}else{var _1oD=E(E(_1oC.a).b),_1oE=B(_1o8(_1oD&(-32),1<<(_1oD&31)>>>0,_1oB));_1oA=_1oC.b;_1oB=_1oE;continue;}}},_1oF=function(_1oG,_1oH){while(1){var _1oI=E(_1oG);if(!_1oI._){return E(_1oH);}else{var _1oJ=B(_1oz(E(_1oI.a).a,_1oH));_1oG=_1oI.b;_1oH=_1oJ;continue;}}},_1oK=function(_1oL,_1oM){while(1){var _1oN=E(_1oM);if(!_1oN._){var _1oO=_1oN.c,_1oP=_1oN.d,_1oQ=E(_1oN.b);if(!_1oQ._){var _1oR=B(_1oF(_1oQ.b,B(_1oK(_1oL,_1oP))));_1oL=_1oR;_1oM=_1oO;continue;}else{var _1oR=B(_1oK(_1oL,_1oP));_1oL=_1oR;_1oM=_1oO;continue;}}else{return E(_1oL);}}},_1oS=-1,_1oT=-2,_1oU=-3,_1oV=new T2(1,_M9,_4),_1oW=new T2(1,_1oU,_1oV),_1oX=new T2(1,_1oT,_1oW),_1oY=new T2(1,_1oS,_1oX),_1oZ=function(_1p0,_1p1,_1p2){var _1p3=function(_1p4,_1p5){if(!B(_1nU(_1nF,_1p0,_1p4))){return new F(function(){return _1oZ(_1p4,_1p5,_1p2);});}else{return E(_1p0);}},_1p6=function(_1p7){if(!B(_vZ(_j1,_1p7,_1oY))){var _1p8=E(_1p7);if(!B(_1nG(_1p8,_1p0))){return new F(function(){return _1nN(_1p8,_1p1);});}else{return true;}}else{return true;}},_1p9=function(_1pa){while(1){var _1pb=E(_1pa);if(!_1pb._){return true;}else{if(!B(_1p6(E(_1pb.a).b))){return false;}else{_1pa=_1pb.b;continue;}}}},_1pc=function(_1pd){var _1pe=E(_1pd);switch(_1pe._){case 0:return new F(function(){return _1p9(_1pe.b);});break;case 1:return new F(function(){return _1p6(_1pe.a);});break;default:return true;}},_1pf=function(_1pg,_1ph,_1pi){while(1){var _1pj=B((function(_1pk,_1pl,_1pm){var _1pn=E(_1pm);switch(_1pn._){case 0:var _1po=B(_1pf(_1pk,_1pl,_1pn.d));_1pg=_1po.a;_1ph=_1po.b;_1pi=_1pn.c;return __continue;case 1:var _1pp=E(_1pk),_1pq=E(_1pl),_1pr=B(_1o1(_1pc,_1pn.b));return (_1pr._==0)?new T2(0,new T(function(){return B(_14u(_1pn.a,_1pr,_1pp));}),new T(function(){return B(_1oK(_1pq,_1pr));})):new T2(0,_1pp,_1pq);default:return new T2(0,_1pk,_1pl);}})(_1pg,_1ph,_1pi));if(_1pj!=__continue){return _1pj;}}},_1ps=E(_1p2);if(!_1ps._){var _1pt=_1ps.c,_1pu=_1ps.d;if(_1ps.b>=0){var _1pv=B(_1pf(_Ux,_18y,_1pu)),_1pw=B(_1pf(_1pv.a,_1pv.b,_1pt));return new F(function(){return _1p3(_1pw.a,_1pw.b);});}else{var _1px=B(_1pf(_Ux,_18y,_1pt)),_1py=B(_1pf(_1px.a,_1px.b,_1pu));return new F(function(){return _1p3(_1py.a,_1py.b);});}}else{var _1pz=B(_1pf(_Ux,_18y,_1ps));return new F(function(){return _1p3(_1pz.a,_1pz.b);});}},_1pA=function(_1pB,_1pC){while(1){var _1pD=E(_1pC);if(!_1pD._){return E(_1pB);}else{var _1pE=E(_1pD.a),_1pF=B(_14u(E(_1pE.a),_1pE.b,_1pB));_1pB=_1pF;_1pC=_1pD.b;continue;}}},_1pG=function(_1pH){var _1pI=E(_1pH);return (_1pI._==0)?(E(_1pI.b)._==0)?true:false:false;},_1pJ=new T(function(){return B(unCStr(")"));}),_1pK=function(_1pL,_1pM){var _1pN=new T(function(){var _1pO=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_1pM,_4)),_1pJ));})));},1);return B(_0(B(_bZ(0,_1pL,_4)),_1pO));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1pN)));});},_1pP=new T(function(){return B(_7f("pgf/PGF/Optimize.hs:(259,9)-(262,117)|function getFunctions"));}),_1pQ=new T(function(){return B(unCStr("&|"));}),_1pR=new T2(1,_1pQ,_4),_1pS=new T(function(){return B(unCStr("&+"));}),_1pT=new T2(1,_1pS,_4),_1pU=new T(function(){return B(_7f("pgf/PGF/Optimize.hs:(235,9)-(245,73)|function seq2prefix"));}),_1pV=function(_1pW,_1pX,_1pY,_1pZ,_1q0,_1q1){var _1q2=_1pZ>>>0;if(((_1pW>>>0&((_1q2-1>>>0^4294967295)>>>0^_1q2)>>>0)>>>0&4294967295)==_1pY){return ((_1pW>>>0&_1q2)>>>0==0)?new T4(0,_1pY,_1pZ,E(B(_1o8(_1pW,_1pX,_1q0))),E(_1q1)):new T4(0,_1pY,_1pZ,E(_1q0),E(B(_1o8(_1pW,_1pX,_1q1))));}else{var _1q3=(_1pW>>>0^_1pY>>>0)>>>0,_1q4=(_1q3|_1q3>>>1)>>>0,_1q5=(_1q4|_1q4>>>2)>>>0,_1q6=(_1q5|_1q5>>>4)>>>0,_1q7=(_1q6|_1q6>>>8)>>>0,_1q8=(_1q7|_1q7>>>16)>>>0,_1q9=(_1q8^_1q8>>>1)>>>0&4294967295,_1qa=_1q9>>>0;return ((_1pW>>>0&_1qa)>>>0==0)?new T4(0,(_1pW>>>0&((_1qa-1>>>0^4294967295)>>>0^_1qa)>>>0)>>>0&4294967295,_1q9,E(new T2(1,_1pW,_1pX)),E(new T4(0,_1pY,_1pZ,E(_1q0),E(_1q1)))):new T4(0,(_1pW>>>0&((_1qa-1>>>0^4294967295)>>>0^_1qa)>>>0)>>>0&4294967295,_1q9,E(new T4(0,_1pY,_1pZ,E(_1q0),E(_1q1))),E(new T2(1,_1pW,_1pX)));}},_1qb=function(_1qc,_1qd,_1qe,_1qf,_1qg){var _1qh=E(_1qg);switch(_1qh._){case 0:var _1qi=_1qh.a,_1qj=_1qh.b,_1qk=_1qh.c,_1ql=_1qh.d;if(_1qd>>>0<=_1qj>>>0){if(_1qj>>>0<=_1qd>>>0){if(_1qc!=_1qi){var _1qm=(_1qc>>>0^_1qi>>>0)>>>0,_1qn=(_1qm|_1qm>>>1)>>>0,_1qo=(_1qn|_1qn>>>2)>>>0,_1qp=(_1qo|_1qo>>>4)>>>0,_1qq=(_1qp|_1qp>>>8)>>>0,_1qr=(_1qq|_1qq>>>16)>>>0,_1qs=(_1qr^_1qr>>>1)>>>0&4294967295,_1qt=_1qs>>>0;return ((_1qc>>>0&_1qt)>>>0==0)?new T4(0,(_1qc>>>0&((_1qt-1>>>0^4294967295)>>>0^_1qt)>>>0)>>>0&4294967295,_1qs,E(new T4(0,_1qc,_1qd,E(_1qe),E(_1qf))),E(_1qh)):new T4(0,(_1qc>>>0&((_1qt-1>>>0^4294967295)>>>0^_1qt)>>>0)>>>0&4294967295,_1qs,E(_1qh),E(new T4(0,_1qc,_1qd,E(_1qe),E(_1qf))));}else{return new T4(0,_1qc,_1qd,E(B(_1qu(_1qe,_1qk))),E(B(_1qu(_1qf,_1ql))));}}else{var _1qv=_1qj>>>0;if(((_1qc>>>0&((_1qv-1>>>0^4294967295)>>>0^_1qv)>>>0)>>>0&4294967295)==_1qi){return ((_1qc>>>0&_1qv)>>>0==0)?new T4(0,_1qi,_1qj,E(B(_1qb(_1qc,_1qd,_1qe,_1qf,_1qk))),E(_1ql)):new T4(0,_1qi,_1qj,E(_1qk),E(B(_1qb(_1qc,_1qd,_1qe,_1qf,_1ql))));}else{var _1qw=(_1qc>>>0^_1qi>>>0)>>>0,_1qx=(_1qw|_1qw>>>1)>>>0,_1qy=(_1qx|_1qx>>>2)>>>0,_1qz=(_1qy|_1qy>>>4)>>>0,_1qA=(_1qz|_1qz>>>8)>>>0,_1qB=(_1qA|_1qA>>>16)>>>0,_1qC=(_1qB^_1qB>>>1)>>>0&4294967295,_1qD=_1qC>>>0;return ((_1qc>>>0&_1qD)>>>0==0)?new T4(0,(_1qc>>>0&((_1qD-1>>>0^4294967295)>>>0^_1qD)>>>0)>>>0&4294967295,_1qC,E(new T4(0,_1qc,_1qd,E(_1qe),E(_1qf))),E(_1qh)):new T4(0,(_1qc>>>0&((_1qD-1>>>0^4294967295)>>>0^_1qD)>>>0)>>>0&4294967295,_1qC,E(_1qh),E(new T4(0,_1qc,_1qd,E(_1qe),E(_1qf))));}}}else{var _1qE=_1qd>>>0;if(((_1qi>>>0&((_1qE-1>>>0^4294967295)>>>0^_1qE)>>>0)>>>0&4294967295)==_1qc){return ((_1qi>>>0&_1qE)>>>0==0)?new T4(0,_1qc,_1qd,E(B(_1qF(_1qe,_1qi,_1qj,_1qk,_1ql))),E(_1qf)):new T4(0,_1qc,_1qd,E(_1qe),E(B(_1qF(_1qf,_1qi,_1qj,_1qk,_1ql))));}else{var _1qG=(_1qc>>>0^_1qi>>>0)>>>0,_1qH=(_1qG|_1qG>>>1)>>>0,_1qI=(_1qH|_1qH>>>2)>>>0,_1qJ=(_1qI|_1qI>>>4)>>>0,_1qK=(_1qJ|_1qJ>>>8)>>>0,_1qL=(_1qK|_1qK>>>16)>>>0,_1qM=(_1qL^_1qL>>>1)>>>0&4294967295,_1qN=_1qM>>>0;return ((_1qc>>>0&_1qN)>>>0==0)?new T4(0,(_1qc>>>0&((_1qN-1>>>0^4294967295)>>>0^_1qN)>>>0)>>>0&4294967295,_1qM,E(new T4(0,_1qc,_1qd,E(_1qe),E(_1qf))),E(_1qh)):new T4(0,(_1qc>>>0&((_1qN-1>>>0^4294967295)>>>0^_1qN)>>>0)>>>0&4294967295,_1qM,E(_1qh),E(new T4(0,_1qc,_1qd,E(_1qe),E(_1qf))));}}break;case 1:return new F(function(){return _1pV(_1qh.a,_1qh.b,_1qc,_1qd,_1qe,_1qf);});break;default:return new T4(0,_1qc,_1qd,E(_1qe),E(_1qf));}},_1qF=function(_1qO,_1qP,_1qQ,_1qR,_1qS){var _1qT=E(_1qO);switch(_1qT._){case 0:var _1qU=_1qT.a,_1qV=_1qT.b,_1qW=_1qT.c,_1qX=_1qT.d;if(_1qV>>>0<=_1qQ>>>0){if(_1qQ>>>0<=_1qV>>>0){if(_1qU!=_1qP){var _1qY=(_1qU>>>0^_1qP>>>0)>>>0,_1qZ=(_1qY|_1qY>>>1)>>>0,_1r0=(_1qZ|_1qZ>>>2)>>>0,_1r1=(_1r0|_1r0>>>4)>>>0,_1r2=(_1r1|_1r1>>>8)>>>0,_1r3=(_1r2|_1r2>>>16)>>>0,_1r4=(_1r3^_1r3>>>1)>>>0&4294967295,_1r5=_1r4>>>0;return ((_1qU>>>0&_1r5)>>>0==0)?new T4(0,(_1qU>>>0&((_1r5-1>>>0^4294967295)>>>0^_1r5)>>>0)>>>0&4294967295,_1r4,E(_1qT),E(new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS)))):new T4(0,(_1qU>>>0&((_1r5-1>>>0^4294967295)>>>0^_1r5)>>>0)>>>0&4294967295,_1r4,E(new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS))),E(_1qT));}else{return new T4(0,_1qU,_1qV,E(B(_1qu(_1qW,_1qR))),E(B(_1qu(_1qX,_1qS))));}}else{var _1r6=_1qQ>>>0;if(((_1qU>>>0&((_1r6-1>>>0^4294967295)>>>0^_1r6)>>>0)>>>0&4294967295)==_1qP){return ((_1qU>>>0&_1r6)>>>0==0)?new T4(0,_1qP,_1qQ,E(B(_1qb(_1qU,_1qV,_1qW,_1qX,_1qR))),E(_1qS)):new T4(0,_1qP,_1qQ,E(_1qR),E(B(_1qb(_1qU,_1qV,_1qW,_1qX,_1qS))));}else{var _1r7=(_1qU>>>0^_1qP>>>0)>>>0,_1r8=(_1r7|_1r7>>>1)>>>0,_1r9=(_1r8|_1r8>>>2)>>>0,_1ra=(_1r9|_1r9>>>4)>>>0,_1rb=(_1ra|_1ra>>>8)>>>0,_1rc=(_1rb|_1rb>>>16)>>>0,_1rd=(_1rc^_1rc>>>1)>>>0&4294967295,_1re=_1rd>>>0;return ((_1qU>>>0&_1re)>>>0==0)?new T4(0,(_1qU>>>0&((_1re-1>>>0^4294967295)>>>0^_1re)>>>0)>>>0&4294967295,_1rd,E(_1qT),E(new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS)))):new T4(0,(_1qU>>>0&((_1re-1>>>0^4294967295)>>>0^_1re)>>>0)>>>0&4294967295,_1rd,E(new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS))),E(_1qT));}}}else{var _1rf=_1qV>>>0;if(((_1qP>>>0&((_1rf-1>>>0^4294967295)>>>0^_1rf)>>>0)>>>0&4294967295)==_1qU){return ((_1qP>>>0&_1rf)>>>0==0)?new T4(0,_1qU,_1qV,E(B(_1qF(_1qW,_1qP,_1qQ,_1qR,_1qS))),E(_1qX)):new T4(0,_1qU,_1qV,E(_1qW),E(B(_1qF(_1qX,_1qP,_1qQ,_1qR,_1qS))));}else{var _1rg=(_1qU>>>0^_1qP>>>0)>>>0,_1rh=(_1rg|_1rg>>>1)>>>0,_1ri=(_1rh|_1rh>>>2)>>>0,_1rj=(_1ri|_1ri>>>4)>>>0,_1rk=(_1rj|_1rj>>>8)>>>0,_1rl=(_1rk|_1rk>>>16)>>>0,_1rm=(_1rl^_1rl>>>1)>>>0&4294967295,_1rn=_1rm>>>0;return ((_1qU>>>0&_1rn)>>>0==0)?new T4(0,(_1qU>>>0&((_1rn-1>>>0^4294967295)>>>0^_1rn)>>>0)>>>0&4294967295,_1rm,E(_1qT),E(new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS)))):new T4(0,(_1qU>>>0&((_1rn-1>>>0^4294967295)>>>0^_1rn)>>>0)>>>0&4294967295,_1rm,E(new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS))),E(_1qT));}}break;case 1:return new F(function(){return _1pV(_1qT.a,_1qT.b,_1qP,_1qQ,_1qR,_1qS);});break;default:return new T4(0,_1qP,_1qQ,E(_1qR),E(_1qS));}},_1qu=function(_1ro,_1rp){var _1rq=E(_1ro);switch(_1rq._){case 0:var _1rr=_1rq.a,_1rs=_1rq.b,_1rt=_1rq.c,_1ru=_1rq.d,_1rv=E(_1rp);switch(_1rv._){case 0:var _1rw=_1rv.a,_1rx=_1rv.b,_1ry=_1rv.c,_1rz=_1rv.d;if(_1rs>>>0<=_1rx>>>0){if(_1rx>>>0<=_1rs>>>0){if(_1rr!=_1rw){var _1rA=(_1rr>>>0^_1rw>>>0)>>>0,_1rB=(_1rA|_1rA>>>1)>>>0,_1rC=(_1rB|_1rB>>>2)>>>0,_1rD=(_1rC|_1rC>>>4)>>>0,_1rE=(_1rD|_1rD>>>8)>>>0,_1rF=(_1rE|_1rE>>>16)>>>0,_1rG=(_1rF^_1rF>>>1)>>>0&4294967295,_1rH=_1rG>>>0;return ((_1rr>>>0&_1rH)>>>0==0)?new T4(0,(_1rr>>>0&((_1rH-1>>>0^4294967295)>>>0^_1rH)>>>0)>>>0&4294967295,_1rG,E(_1rq),E(_1rv)):new T4(0,(_1rr>>>0&((_1rH-1>>>0^4294967295)>>>0^_1rH)>>>0)>>>0&4294967295,_1rG,E(_1rv),E(_1rq));}else{return new T4(0,_1rr,_1rs,E(B(_1qu(_1rt,_1ry))),E(B(_1qu(_1ru,_1rz))));}}else{var _1rI=_1rx>>>0;if(((_1rr>>>0&((_1rI-1>>>0^4294967295)>>>0^_1rI)>>>0)>>>0&4294967295)==_1rw){return ((_1rr>>>0&_1rI)>>>0==0)?new T4(0,_1rw,_1rx,E(B(_1qb(_1rr,_1rs,_1rt,_1ru,_1ry))),E(_1rz)):new T4(0,_1rw,_1rx,E(_1ry),E(B(_1qb(_1rr,_1rs,_1rt,_1ru,_1rz))));}else{var _1rJ=(_1rr>>>0^_1rw>>>0)>>>0,_1rK=(_1rJ|_1rJ>>>1)>>>0,_1rL=(_1rK|_1rK>>>2)>>>0,_1rM=(_1rL|_1rL>>>4)>>>0,_1rN=(_1rM|_1rM>>>8)>>>0,_1rO=(_1rN|_1rN>>>16)>>>0,_1rP=(_1rO^_1rO>>>1)>>>0&4294967295,_1rQ=_1rP>>>0;return ((_1rr>>>0&_1rQ)>>>0==0)?new T4(0,(_1rr>>>0&((_1rQ-1>>>0^4294967295)>>>0^_1rQ)>>>0)>>>0&4294967295,_1rP,E(_1rq),E(_1rv)):new T4(0,(_1rr>>>0&((_1rQ-1>>>0^4294967295)>>>0^_1rQ)>>>0)>>>0&4294967295,_1rP,E(_1rv),E(_1rq));}}}else{var _1rR=_1rs>>>0;if(((_1rw>>>0&((_1rR-1>>>0^4294967295)>>>0^_1rR)>>>0)>>>0&4294967295)==_1rr){return ((_1rw>>>0&_1rR)>>>0==0)?new T4(0,_1rr,_1rs,E(B(_1qF(_1rt,_1rw,_1rx,_1ry,_1rz))),E(_1ru)):new T4(0,_1rr,_1rs,E(_1rt),E(B(_1qF(_1ru,_1rw,_1rx,_1ry,_1rz))));}else{var _1rS=(_1rr>>>0^_1rw>>>0)>>>0,_1rT=(_1rS|_1rS>>>1)>>>0,_1rU=(_1rT|_1rT>>>2)>>>0,_1rV=(_1rU|_1rU>>>4)>>>0,_1rW=(_1rV|_1rV>>>8)>>>0,_1rX=(_1rW|_1rW>>>16)>>>0,_1rY=(_1rX^_1rX>>>1)>>>0&4294967295,_1rZ=_1rY>>>0;return ((_1rr>>>0&_1rZ)>>>0==0)?new T4(0,(_1rr>>>0&((_1rZ-1>>>0^4294967295)>>>0^_1rZ)>>>0)>>>0&4294967295,_1rY,E(_1rq),E(_1rv)):new T4(0,(_1rr>>>0&((_1rZ-1>>>0^4294967295)>>>0^_1rZ)>>>0)>>>0&4294967295,_1rY,E(_1rv),E(_1rq));}}break;case 1:return new F(function(){return _1pV(_1rv.a,_1rv.b,_1rr,_1rs,_1rt,_1ru);});break;default:return E(_1rq);}break;case 1:return new F(function(){return _1o8(_1rq.a,_1rq.b,_1rp);});break;default:return E(_1rp);}},_1s0=function(_1s1,_1s2){var _1s3=E(_1s1),_1s4=B(_16i(_12C,_1qu,_1s3.a,_1s3.b,_1s2));return new T2(0,_1s4.a,_1s4.b);},_1s5=new T(function(){return B(unCStr("Int"));}),_1s6=function(_1s7,_1s8,_1s9){return new F(function(){return _eR(_e4,new T2(0,_1s8,_1s9),_1s7,_1s5);});},_1sa=function(_1sb,_1sc,_1sd){return new F(function(){return _eR(_e4,new T2(0,_1sb,_1sc),_1sd,_1s5);});},_1se=new T(function(){return B(_1pA(_Ux,_4));}),_1sf=function(_1sg,_1sh){var _1si=function(_1sj,_1sk,_1sl){return new F(function(){return A2(_1sg,_1sk,_1sl);});},_1sm=function(_1sn,_1so){while(1){var _1sp=E(_1so);if(!_1sp._){return E(_1sn);}else{var _1sq=B(_1jS(_1si,_1sn,_1sp.a));_1sn=_1sq;_1so=_1sp.b;continue;}}};return new F(function(){return _1sm(_Ux,_1sh);});},_1sr=function(_1ss,_1st,_1su,_1sv,_1sw,_1sx,_1sy,_1sz,_1sA){var _1sB=new T(function(){return B(_1oZ(_Ux,_18y,_1sy));}),_1sC=new T(function(){var _1sD=function(_1sE,_1sF){while(1){var _1sG=B((function(_1sH,_1sI){var _1sJ=E(_1sI);if(!_1sJ._){var _1sK=_1sJ.d,_1sL=new T(function(){var _1sM=E(_1sJ.b);if(!_1sM._){var _1sN=_1sM.a;if(!E(_1sM.b)._){var _1sO=new T(function(){var _1sP=E(_1su),_1sQ=_1sP.c,_1sR=E(_1sP.a),_1sS=E(_1sP.b);if(_1sR>_1sN){return B(_1s6(_1sN,_1sR,_1sS));}else{if(_1sN>_1sS){return B(_1s6(_1sN,_1sR,_1sS));}else{var _1sT=_1sN-_1sR|0;if(0>_1sT){return B(_1pK(_1sT,_1sQ));}else{if(_1sT>=_1sQ){return B(_1pK(_1sT,_1sQ));}else{var _1sU=E(_1sP.d[_1sT]),_1sV=_1sU.d,_1sW=E(_1sU.b),_1sX=E(_1sU.c);if(_1sW<=_1sX){var _1sY=new T(function(){var _1sZ=B(_14j(_12C,_1ne,new T2(1,new T2(0,_1pR,new T2(1,_1sN&(-32),1<<(_1sN&31)>>>0)),_4)));return new T2(0,_1sZ.a,_1sZ.b);}),_1t0=new T(function(){var _1t1=B(_14j(_12C,_1ne,new T2(1,new T2(0,_4,new T2(1,_1sN&(-32),1<<(_1sN&31)>>>0)),_4)));return new T2(0,_1t1.a,_1t1.b);}),_1t2=new T2(1,_1sN&(-32),1<<(_1sN&31)>>>0),_1t3=new T(function(){var _1t4=B(_14j(_12C,_1ne,new T2(1,new T2(0,_4,_1t2),_4)));return new T2(0,_1t4.a,_1t4.b);}),_1t5=new T(function(){var _1t6=B(_14j(_12C,_1ne,new T2(1,new T2(0,_1pT,new T2(1,_1sN&(-32),1<<(_1sN&31)>>>0)),_4)));return new T2(0,_1t6.a,_1t6.b);}),_1t7=function(_1t8){var _1t9=E(_1t8);if(!_1t9._){return E(_1t3);}else{var _1ta=_1t9.b,_1tb=E(_1t9.a);switch(_1tb._){case 3:var _1tc=B(_14j(_12C,_1ne,new T2(1,new T2(0,new T2(1,_1tb.a,_4),_1t2),_4)));return new T2(0,_1tc.a,_1tc.b);case 4:var _1td=new T(function(){var _1te=function(_1tf){var _1tg=E(_1tf);return (_1tg._==0)?__Z:new T2(1,new T(function(){return B(_1t7(B(_0(E(_1tg.a).a,_1ta))));}),new T(function(){return B(_1te(_1tg.b));}));};return B(_1te(_1tb.b));}),_1th=B(_18o(_12C,_1qu,new T2(1,new T(function(){return B(_1t7(B(_0(_1tb.a,_1ta))));}),_1td)));return new T2(0,_1th.a,_1th.b);case 5:return E(_1t5);case 6:return E(_1nh);case 7:return E(_1t0);case 8:return E(_1t0);case 9:return E(_1sY);case 10:return E(_1sY);default:return E(_1pU);}}},_1ti=new T(function(){return B(_1t7(_4));}),_1tj=function(_1tk){var _1tl=new T(function(){var _1tm=E(_1sx),_1tn=_1tm.c,_1to=E(_1tm.a),_1tp=E(_1tm.b);if(_1sW>_1tk){return B(_1sa(_1sW,_1sX,_1tk));}else{if(_1tk>_1sX){return B(_1sa(_1sW,_1sX,_1tk));}else{var _1tq=_1tk-_1sW|0;if(0>_1tq){return B(_1pK(_1tq,_1sV));}else{if(_1tq>=_1sV){return B(_1pK(_1tq,_1sV));}else{var _1tr=_1sU.e["v"]["i32"][_1tq];if(_1to>_1tr){return B(_1s6(_1tr,_1to,_1tp));}else{if(_1tr>_1tp){return B(_1s6(_1tr,_1to,_1tp));}else{var _1ts=_1tr-_1to|0;if(0>_1ts){return B(_1pK(_1ts,_1tn));}else{if(_1ts>=_1tn){return B(_1pK(_1ts,_1tn));}else{var _1tt=E(_1tm.d[_1ts]),_1tu=_1tt.c-1|0;if(0<=_1tu){var _1tv=function(_1tw){return new T2(1,new T(function(){return E(_1tt.d[_1tw]);}),new T(function(){if(_1tw!=_1tu){return B(_1tv(_1tw+1|0));}else{return __Z;}}));};return B(_1t7(B(_1tv(0))));}else{return E(_1ti);}}}}}}}}}});return new T2(1,new T2(0,_1tk,_1tl),new T(function(){if(_1tk!=_1sX){return B(_1tj(_1tk+1|0));}else{return __Z;}}));};return B(_1pA(_Ux,B(_1tj(_1sW))));}else{return E(_1se);}}}}}});return new T2(1,_1sO,new T(function(){return B(_1sD(_1sH,_1sK));}));}else{return B(_1sD(_1sH,_1sK));}}else{return B(_1sD(_1sH,_1sK));}},1);_1sE=_1sL;_1sF=_1sJ.c;return __continue;}else{return E(_1sH);}})(_1sE,_1sF));if(_1sG!=__continue){return _1sG;}}},_1tx=function(_1ty,_1tz,_1tA){while(1){var _1tB=E(_1tA);switch(_1tB._){case 0:var _1tC=B(_1tx(_1ty,_1tz,_1tB.d));_1ty=_1tC.a;_1tz=_1tC.b;_1tA=_1tB.c;continue;case 1:var _1tD=_1tB.a,_1tE=B(_160(_1pG,_1tB.b)),_1tF=E(_1tE.a);if(!_1tF._){var _1tG=B(_14u(_1tD,B(_1sf(_1s0,B(_1sD(_4,_1tF)))),_1ty));}else{var _1tG=E(_1ty);}var _1tH=E(_1tE.b);if(!_1tH._){var _1tI=B(_14u(_1tD,_1tH,_1tz));}else{var _1tI=E(_1tz);}return new T2(0,_1tG,_1tI);default:return new T2(0,_1ty,_1tz);}}},_1tJ=E(_1sB);if(!_1tJ._){var _1tK=_1tJ.c,_1tL=_1tJ.d;if(_1tJ.b>=0){var _1tM=B(_1tx(_Ux,_Ux,_1tL)),_1tN=B(_1tx(_1tM.a,_1tM.b,_1tK));return new T2(0,_1tN.a,_1tN.b);}else{var _1tO=B(_1tx(_Ux,_Ux,_1tK)),_1tP=B(_1tx(_1tO.a,_1tO.b,_1tL));return new T2(0,_1tP.a,_1tP.b);}}else{var _1tQ=B(_1tx(_Ux,_Ux,_1tJ));return new T2(0,_1tQ.a,_1tQ.b);}}),_1tR=new T(function(){var _1tS=function(_1tT){var _1tU=E(_1tT);switch(_1tU._){case 0:var _1tV=_1tU.a;return new T2(1,new T(function(){var _1tW=E(_1su),_1tX=_1tW.c,_1tY=E(_1tW.a),_1tZ=E(_1tW.b);if(_1tY>_1tV){return B(_1s6(_1tV,_1tY,_1tZ));}else{if(_1tV>_1tZ){return B(_1s6(_1tV,_1tY,_1tZ));}else{var _1u0=_1tV-_1tY|0;if(0>_1u0){return B(_1pK(_1u0,_1tX));}else{if(_1u0>=_1tX){return B(_1pK(_1u0,_1tX));}else{return E(E(_1tW.d[_1u0]).a);}}}}}),_4);case 1:var _1u1=B(_14V(_1tU.a,_1sB));if(!_1u1._){return __Z;}else{return new F(function(){return _1u2(_4,_1u1.a);});}break;default:return E(_1pP);}},_1u2=function(_1u3,_1u4){while(1){var _1u5=B((function(_1u6,_1u7){var _1u8=E(_1u7);if(!_1u8._){var _1u9=new T(function(){return B(_0(B(_1tS(_1u8.b)),new T(function(){return B(_1u2(_1u6,_1u8.d));},1)));},1);_1u3=_1u9;_1u4=_1u8.c;return __continue;}else{return E(_1u6);}})(_1u3,_1u4));if(_1u5!=__continue){return _1u5;}}},_1ua=function(_1ub,_1uc){while(1){var _1ud=B((function(_1ue,_1uf){var _1ug=E(_1uf);switch(_1ug._){case 0:_1ub=new T(function(){return B(_1ua(_1ue,_1ug.d));},1);_1uc=_1ug.c;return __continue;case 1:var _1uh=function(_1ui,_1uj){while(1){var _1uk=B((function(_1ul,_1um){var _1un=E(_1um);if(!_1un._){var _1uo=_1un.b,_1up=new T(function(){var _1uq=new T(function(){return B(_1uh(_1ul,_1un.d));}),_1ur=function(_1us){var _1ut=E(_1us);return (_1ut._==0)?E(_1uq):new T2(1,new T2(0,_1ut.a,new T2(1,_1ug.a,new T4(0,1,E(_1uo),E(_ML),E(_ML)))),new T(function(){return B(_1ur(_1ut.b));}));};return B(_1ur(B(_1tS(_1uo))));},1);_1ui=_1up;_1uj=_1un.c;return __continue;}else{return E(_1ul);}})(_1ui,_1uj));if(_1uk!=__continue){return _1uk;}}};return new F(function(){return _1uh(_1ue,_1ug.b);});break;default:return E(_1ue);}})(_1ub,_1uc));if(_1ud!=__continue){return _1ud;}}},_1uu=E(_1sB);if(!_1uu._){var _1uv=_1uu.c,_1uw=_1uu.d;if(_1uu.b>=0){return B(_13d(_1na,B(_1ua(new T(function(){return B(_1ua(_4,_1uw));},1),_1uv))));}else{return B(_13d(_1na,B(_1ua(new T(function(){return B(_1ua(_4,_1uv));},1),_1uw))));}}else{return B(_13d(_1na,B(_1ua(_4,_1uu))));}});return {_:0,a:_1ss,b:_1st,c:_1su,d:_1sv,e:_1sw,f:_1sx,g:_1sy,h:new T(function(){return E(E(_1sC).b);}),i:_1tR,j:_1sz,k:new T(function(){return E(E(_1sC).a);}),l:_1sA};},_1ux=function(_1uy){var _1uz=E(_1uy);return new F(function(){return _1sr(_1uz.a,_1uz.b,_1uz.c,_1uz.d,_1uz.e,_1uz.f,_1uz.g,_1uz.j,_1uz.l);});},_1uA=0,_1uB=function(_1uC){var _1uD=E(_1uC);return new T3(0,_1uD.a,_1uD.b,_1uA);},_1uE=function(_1uF){var _1uG=E(_1uF);return new T4(0,_1uG.a,_1uG.b,new T(function(){var _1uH=E(_1uG.c);if(!_1uH._){return __Z;}else{return new T1(1,new T2(0,_1uH.a,_4));}}),_1uG.d);},_1uI=0,_1uJ=new T(function(){return B(unCStr("Negative range size"));}),_1uK=function(_1uL){var _1uM=function(_){var _1uN=B(_uU(_1uL,0))-1|0,_1uO=function(_1uP){if(_1uP>=0){var _1uQ=newArr(_1uP,_Vu),_1uR=_1uQ,_1uS=function(_1uT){var _1uU=function(_1uV,_1uW,_){while(1){if(_1uV!=_1uT){var _1uX=E(_1uW);if(!_1uX._){return _5;}else{var _=_1uR[_1uV]=_1uX.a,_1uY=_1uV+1|0;_1uV=_1uY;_1uW=_1uX.b;continue;}}else{return _5;}}},_1uZ=B(_1uU(0,_1uL,_));return new T4(0,E(_1uI),E(_1uN),_1uP,_1uR);};if(0>_1uN){return new F(function(){return _1uS(0);});}else{var _1v0=_1uN+1|0;if(_1v0>=0){return new F(function(){return _1uS(_1v0);});}else{return new F(function(){return err(_1uJ);});}}}else{return E(_Vw);}};if(0>_1uN){var _1v1=B(_1uO(0)),_1v2=E(_1v1),_1v3=_1v2.d;return new T4(0,E(_1v2.a),E(_1v2.b),_1v2.c,_1v3);}else{var _1v4=B(_1uO(_1uN+1|0)),_1v5=E(_1v4),_1v6=_1v5.d;return new T4(0,E(_1v5.a),E(_1v5.b),_1v5.c,_1v6);}};return new F(function(){return _8O(_1uM);});},_1v7=function(_1v8){return new T1(3,_1v8);},_1v9=function(_1va,_1vb){var _1vc=new T(function(){var _1vd=E(_1va),_1ve=B(_fi(_1vd.a,_1vd.b,_1vd.c,E(_1vb))),_1vf=B(_gf(E(_1ve.a)&4294967295,_g3,_1vd,_1ve.b));return new T2(0,_1vf.a,_1vf.b);});return new T2(0,new T1(3,new T(function(){return E(E(_1vc).a);})),new T(function(){return E(E(_1vc).b);}));},_1vg=function(_1vh,_1vi){var _1vj=B(_1v9(_1vh,_1vi));return new T2(0,_1vj.a,_1vj.b);},_1vk=function(_1vl,_1vm){var _1vn=E(_1vl),_1vo=B(_fi(_1vn.a,_1vn.b,_1vn.c,E(_1vm))),_1vp=B(_gf(E(_1vo.a)&4294967295,_g3,_1vn,_1vo.b));return new T2(0,_1vp.a,_1vp.b);},_1vq=function(_1vr,_1vs,_1vt,_1vu){var _1vv=B(_ZH(_1vg,new T3(0,_1vr,_1vs,_1vt),_1vu)),_1vw=B(_fi(_1vr,_1vs,_1vt,E(_1vv.b))),_1vx=B(_gf(E(_1vw.a)&4294967295,_1vk,new T3(0,_1vr,_1vs,_1vt),_1vw.b));return new T2(0,new T2(0,_1vv.a,_1vx.a),_1vx.b);},_1vy=function(_1vz,_1vA){var _1vB=E(_1vz),_1vC=B(_1vq(_1vB.a,_1vB.b,_1vB.c,_1vA));return new T2(0,_1vC.a,_1vC.b);},_1vD=function(_1vE){var _1vF=new T(function(){return B(unAppCStr("getSymbol ",new T(function(){return B(_bZ(0,_1vE&4294967295,_4));})));});return new F(function(){return _107(_1vF);});},_1vG=function(_1vH,_1vI,_1vJ,_1vK){var _1vL=B(_fc(_1vH,_1vI,_1vJ,_1vK)),_1vM=_1vL.b,_1vN=E(_1vL.a);switch(_1vN){case 0:var _1vO=new T(function(){var _1vP=B(_fi(_1vH,_1vI,_1vJ,E(_1vM))),_1vQ=B(_fi(_1vH,_1vI,_1vJ,E(_1vP.b)));return new T2(0,new T(function(){return new T2(0,E(_1vP.a)&4294967295,E(_1vQ.a)&4294967295);}),_1vQ.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1vO).a);}),_4),new T(function(){return E(E(_1vO).b);}));case 1:var _1vR=new T(function(){var _1vS=B(_fi(_1vH,_1vI,_1vJ,E(_1vM))),_1vT=B(_fi(_1vH,_1vI,_1vJ,E(_1vS.b)));return new T2(0,new T(function(){return new T2(1,E(_1vS.a)&4294967295,E(_1vT.a)&4294967295);}),_1vT.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1vR).a);}),_4),new T(function(){return E(E(_1vR).b);}));case 2:var _1vU=new T(function(){var _1vV=B(_fi(_1vH,_1vI,_1vJ,E(_1vM))),_1vW=B(_fi(_1vH,_1vI,_1vJ,E(_1vV.b)));return new T2(0,new T(function(){return new T2(2,E(_1vV.a)&4294967295,E(_1vW.a)&4294967295);}),_1vW.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1vU).a);}),_4),new T(function(){return E(E(_1vU).b);}));case 3:var _1vX=B(_fi(_1vH,_1vI,_1vJ,E(_1vM))),_1vY=B(_gf(E(_1vX.a)&4294967295,_1vk,new T3(0,_1vH,_1vI,_1vJ),_1vX.b));return new T2(0,new T(function(){return B(_G(_1v7,_1vY.a));}),_1vY.b);case 4:var _1vZ=new T(function(){var _1w0=new T3(0,_1vH,_1vI,_1vJ),_1w1=B(_ZH(_1vg,_1w0,_1vM)),_1w2=B(_ZH(_1vy,_1w0,_1w1.b));return new T2(0,new T2(4,_1w1.a,_1w2.a),_1w2.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1vZ).a);}),_4),new T(function(){return E(E(_1vZ).b);}));default:return new F(function(){return _1vD(_1vN);});}},_1w3=function(_1w4,_1w5){var _1w6=E(_1w4),_1w7=B(_1vG(_1w6.a,_1w6.b,_1w6.c,E(_1w5)));return new T2(0,_1w7.a,_1w7.b);},_1w8=function(_1w9){var _1wa=E(_1w9);if(!_1wa._){return __Z;}else{return new F(function(){return _0(_1wa.a,new T(function(){return B(_1w8(_1wa.b));},1));});}},_1wb=function(_1wc,_1wd){var _1we=new T(function(){var _1wf=B(_ZH(_1w3,_1wc,_1wd));return new T2(0,_1wf.a,_1wf.b);});return new T2(0,new T(function(){return B(_1uK(B(_1w8(E(_1we).a))));}),new T(function(){return E(E(_1we).b);}));},_1wg=function(_1wh,_1wi,_1wj,_1wk){var _1wl=B(_fi(_1wh,_1wi,_1wj,_1wk));return new F(function(){return _gf(E(_1wl.a)&4294967295,_g3,new T3(0,_1wh,_1wi,_1wj),_1wl.b);});},_1wm=function(_1wn,_1wo){var _1wp=E(_1wn),_1wq=B(_1wg(_1wp.a,_1wp.b,_1wp.c,E(_1wo)));return new T2(0,_1wq.a,_1wq.b);},_1wr=function(_1ws){var _1wt=E(_1ws);return (_1wt._==0)?__Z:new T2(1,new T2(0,_M9,_1wt.a),new T(function(){return B(_1wr(_1wt.b));}));},_1wu=function(_1wv,_1ww,_1wx,_1wy){var _1wz=B(_fi(_1wv,_1ww,_1wx,_1wy)),_1wA=B(_gf(E(_1wz.a)&4294967295,_kp,new T3(0,_1wv,_1ww,_1wx),_1wz.b)),_1wB=B(_fi(_1wv,_1ww,_1wx,E(_1wA.b))),_1wC=new T(function(){return new T2(0,new T(function(){return B(_1wr(_1wA.a));}),E(_1wB.a)&4294967295);});return new T2(0,_1wC,_1wB.b);},_1wD=function(_1wE,_1wF){var _1wG=E(_1wE),_1wH=B(_1wu(_1wG.a,_1wG.b,_1wG.c,E(_1wF)));return new T2(0,_1wH.a,_1wH.b);},_1wI=new T(function(){return B(unCStr("getProduction"));}),_1wJ=new T(function(){return B(_107(_1wI));}),_1wK=function(_1wL,_1wM,_1wN,_1wO){var _1wP=B(_fc(_1wL,_1wM,_1wN,_1wO)),_1wQ=_1wP.b;switch(E(_1wP.a)){case 0:var _1wR=B(_fi(_1wL,_1wM,_1wN,E(_1wQ))),_1wS=B(_ZH(_1wD,new T3(0,_1wL,_1wM,_1wN),_1wR.b));return new T2(0,new T(function(){return new T2(0,E(_1wR.a)&4294967295,_1wS.a);}),_1wS.b);case 1:var _1wT=B(_fi(_1wL,_1wM,_1wN,E(_1wQ)));return new T2(0,new T(function(){return new T1(1,E(_1wT.a)&4294967295);}),_1wT.b);default:return E(_1wJ);}},_1wU=function(_1wV,_1wW){var _1wX=E(_1wV),_1wY=B(_1wK(_1wX.a,_1wX.b,_1wX.c,E(_1wW)));return new T2(0,_1wY.a,_1wY.b);},_1wZ=function(_1x0,_1x1){var _1x2=new T(function(){var _1x3=E(_1x0),_1x4=B(_fi(_1x3.a,_1x3.b,_1x3.c,E(_1x1)));return new T2(0,new T(function(){return E(_1x4.a)&4294967295;}),_1x4.b);}),_1x5=new T(function(){var _1x6=B(_ZH(_1wU,_1x0,new T(function(){return E(E(_1x2).b);},1)));return new T2(0,_1x6.a,_1x6.b);});return new T2(0,new T2(0,new T(function(){return E(E(_1x2).a);}),new T(function(){var _1x7=E(E(_1x5).a);if(!_1x7._){return new T0(1);}else{return B(_Pk(1,new T4(0,1,E(_1x7.a),E(_ML),E(_ML)),_1x7.b));}})),new T(function(){return E(E(_1x5).b);}));},_1x8=function(_1x9,_1xa){var _1xb=B(_1wZ(_1x9,_1xa));return new T2(0,_1xb.a,_1xb.b);},_1xc=new T(function(){return B(err(_1uJ));}),_1xd=function(_1xe,_1xf,_1xg,_1xh){var _1xi=new T(function(){var _1xj=E(_1xg),_1xk=B(_fi(_1xj.a,_1xj.b,_1xj.c,E(_1xh))),_1xl=E(_1xk.a)&4294967295,_1xm=B(_Zz(_1xl,_1xf,_1xj,_1xk.b));return new T2(0,new T2(0,_1xl,_1xm.a),_1xm.b);}),_1xn=new T(function(){var _1xo=E(E(_1xi).a),_1xp=_1xo.b,_1xq=new T(function(){return E(_1xo.a)-1|0;});return B(A(_jN,[_1xe,_jv,new T2(0,_1uI,_1xq),new T(function(){var _1xr=E(_1xq);if(0>_1xr){return B(_jP(B(_iz(0,-1)),_1xp));}else{var _1xs=_1xr+1|0;if(_1xs>=0){return B(_jP(B(_iz(0,_1xs-1|0)),_1xp));}else{return E(_1xc);}}})]));});return new T2(0,_1xn,new T(function(){return E(E(_1xi).b);}));},_1xt=function(_1xu,_1xv,_1xw,_1xx){var _1xy=B(_fi(_1xu,_1xv,_1xw,_1xx));return new F(function(){return _gf(E(_1xy.a)&4294967295,_g3,new T3(0,_1xu,_1xv,_1xw),_1xy.b);});},_1xz=function(_1xA,_1xB){var _1xC=E(_1xA),_1xD=B(_1xt(_1xC.a,_1xC.b,_1xC.c,E(_1xB)));return new T2(0,_1xD.a,_1xD.b);},_1xE=function(_1xF,_1xG,_1xH,_1xI){var _1xJ=B(_fi(_1xF,_1xG,_1xH,_1xI)),_1xK=B(_fi(_1xF,_1xG,_1xH,E(_1xJ.b))),_1xL=B(_1xd(_id,_1xz,new T3(0,_1xF,_1xG,_1xH),_1xK.b));return new T2(0,new T(function(){var _1xM=E(_1xL.a);return new T6(0,E(_1xJ.a)&4294967295,E(_1xK.a)&4294967295,E(_1xM.a),E(_1xM.b),_1xM.c,_1xM.d);}),_1xL.b);},_1xN=function(_1xO,_1xP){var _1xQ=E(_1xO),_1xR=B(_1xE(_1xQ.a,_1xQ.b,_1xQ.c,E(_1xP)));return new T2(0,_1xR.a,_1xR.b);},_1xS=0,_1xT=new T(function(){return B(unCStr("Negative range size"));}),_1xU=function(_1xV){var _1xW=B(_uU(_1xV,0)),_1xX=new T(function(){var _1xY=function(_){var _1xZ=_1xW-1|0,_1y0=function(_,_1y1){var _1y2=function(_1y3){var _1y4=_1y3-1|0;if(0<=_1y4){var _1y5=function(_1y6,_){while(1){var _=E(_1y1).d["v"]["w8"][_1y6]=0;if(_1y6!=_1y4){var _1y7=_1y6+1|0;_1y6=_1y7;continue;}else{return _5;}}},_1y8=B(_1y5(0,_));return _1y1;}else{return _1y1;}};if(0>_1xZ){return new F(function(){return _1y2(0);});}else{var _1y9=_1xZ+1|0;if(_1y9>=0){return new F(function(){return _1y2(_1y9);});}else{return new F(function(){return err(_1xT);});}}},_1ya=function(_,_1yb,_1yc,_1yd,_1ye){var _1yf=function(_1yg){var _1yh=function(_1yi,_1yj,_){while(1){if(_1yi!=_1yg){var _1yk=E(_1yj);if(!_1yk._){return _5;}else{var _=_1ye["v"]["w8"][_1yi]=E(_1yk.a),_1yl=_1yi+1|0;_1yi=_1yl;_1yj=_1yk.b;continue;}}else{return _5;}}},_1ym=B(_1yh(0,_1xV,_));return new T4(0,E(_1yb),E(_1yc),_1yd,_1ye);};if(0>_1xZ){return new F(function(){return _1yf(0);});}else{var _1yn=_1xZ+1|0;if(_1yn>=0){return new F(function(){return _1yf(_1yn);});}else{return new F(function(){return err(_1xT);});}}};if(0>_1xZ){var _1yo=newByteArr(0),_1yp=B(_1y0(_,new T4(0,E(_1xS),E(_1xZ),0,_1yo))),_1yq=E(_1yp);return new F(function(){return _1ya(_,_1yq.a,_1yq.b,_1yq.c,_1yq.d);});}else{var _1yr=_1xZ+1|0,_1ys=newByteArr(_1yr),_1yt=B(_1y0(_,new T4(0,E(_1xS),E(_1xZ),_1yr,_1ys))),_1yu=E(_1yt);return new F(function(){return _1ya(_,_1yu.a,_1yu.b,_1yu.c,_1yu.d);});}};return B(_8O(_1xY));});return new T3(0,0,_1xW,_1xX);},_1yv=function(_1yw){return new F(function(){return _bZ(0,E(_1yw)&4294967295,_4);});},_1yx=function(_1yy,_1yz){return new F(function(){return _bZ(0,E(_1yy)&4294967295,_1yz);});},_1yA=function(_1yB,_1yC){return new F(function(){return _3X(_1yx,_1yB,_1yC);});},_1yD=function(_1yE,_1yF,_1yG){return new F(function(){return _bZ(E(_1yE),E(_1yF)&4294967295,_1yG);});},_1yH=new T3(0,_1yD,_1yv,_1yA),_1yI=new T(function(){return B(unCStr("Word8"));}),_1yJ=0,_1yK=255,_1yL=new T2(0,_1yJ,_1yK),_1yM=new T2(1,_bX,_4),_1yN=function(_1yO,_1yP,_1yQ,_1yR){var _1yS=new T(function(){var _1yT=new T(function(){var _1yU=new T(function(){var _1yV=new T(function(){var _1yW=new T(function(){var _1yX=E(_1yQ),_1yY=new T(function(){return B(A3(_eg,_e6,new T2(1,new T(function(){return B(A3(_es,_1yR,_er,_1yX.a));}),new T2(1,new T(function(){return B(A3(_es,_1yR,_er,_1yX.b));}),_4)),_1yM));});return new T2(1,_bY,_1yY);});return B(unAppCStr(") is outside of bounds ",_1yW));},1);return B(_0(B(_bZ(0,E(_1yP),_4)),_1yV));});return B(unAppCStr("}: tag (",_1yU));},1);return B(_0(_1yO,_1yT));});return new F(function(){return err(B(unAppCStr("Enum.toEnum{",_1yS)));});},_1yZ=function(_1z0,_1z1,_1z2,_1z3){return new F(function(){return _1yN(_1z1,_1z2,_1z3,_1z0);});},_1z4=function(_1z5){return new F(function(){return _1yZ(_1yH,_1yI,_1z5,_1yL);});},_1z6=function(_1z7){if(_1z7<0){return new F(function(){return _1z4(_1z7);});}else{if(_1z7>255){return new F(function(){return _1z4(_1z7);});}else{return _1z7>>>0;}}},_1z8=function(_1z9){return new F(function(){return _1z6(E(_1z9));});},_1za=function(_1zb){var _1zc=E(_1zb);if(!_1zc._){return __Z;}else{var _1zd=_1zc.b,_1ze=E(_1zc.a),_1zf=function(_1zg){return (_1ze>=2048)?new T2(1,new T(function(){var _1zh=224+B(_n2(_1ze,4096))|0;if(_1zh>>>0>1114111){return B(_fK(_1zh));}else{return _1zh;}}),new T2(1,new T(function(){var _1zi=128+B(_n2(B(_o6(_1ze,4096)),64))|0;if(_1zi>>>0>1114111){return B(_fK(_1zi));}else{return _1zi;}}),new T2(1,new T(function(){var _1zj=128+B(_o6(_1ze,64))|0;if(_1zj>>>0>1114111){return B(_fK(_1zj));}else{return _1zj;}}),new T(function(){return B(_1za(_1zd));})))):new T2(1,new T(function(){var _1zk=192+B(_n2(_1ze,64))|0;if(_1zk>>>0>1114111){return B(_fK(_1zk));}else{return _1zk;}}),new T2(1,new T(function(){var _1zl=128+B(_o6(_1ze,64))|0;if(_1zl>>>0>1114111){return B(_fK(_1zl));}else{return _1zl;}}),new T(function(){return B(_1za(_1zd));})));};if(_1ze<=0){return new F(function(){return _1zf(_);});}else{if(_1ze>=128){return new F(function(){return _1zf(_);});}else{return new T2(1,_1ze,new T(function(){return B(_1za(_1zd));}));}}}},_1zm=new T(function(){return B(unCStr("linref"));}),_1zn=new T(function(){return B(_1za(_1zm));}),_1zo=new T(function(){return B(_G(_1z8,_1zn));}),_1zp=new T(function(){var _1zq=B(_1xU(_1zo));return new T3(0,_1zq.a,_1zq.b,_1zq.c);}),_1zr=function(_1zs,_1zt){var _1zu=E(_1zs),_1zv=B(_ft(_1zu.a,_1zu.b,_1zu.c,E(_1zt))),_1zw=B(_1xd(_m2,_kp,_1zu,_1zv.b));return new T2(0,new T(function(){var _1zx=E(_1zw.a);return new T5(0,_1zv.a,E(_1zx.a),E(_1zx.b),_1zx.c,_1zx.d);}),_1zw.b);},_1zy=new T(function(){return B(_1pA(_Ux,_4));}),_1zz=new T2(0,0,0),_1zA=new T2(1,_1zz,_4),_1zB=new T(function(){return B(_1uK(_1zA));}),_1zC=new T2(1,_1zB,_4),_1zD=function(_1zE,_1zF,_1zG,_1zH){var _1zI=new T3(0,_1zE,_1zF,_1zG),_1zJ=B(_ZQ(_128,_123,_1zI,_1zH)),_1zK=B(_ZQ(_128,_1wm,_1zI,_1zJ.b)),_1zL=B(_fi(_1zE,_1zF,_1zG,E(_1zK.b))),_1zM=E(_1zL.a)&4294967295,_1zN=B(_Zz(_1zM,_1wb,_1zI,_1zL.b)),_1zO=B(_fi(_1zE,_1zF,_1zG,E(_1zN.b))),_1zP=E(_1zO.a)&4294967295,_1zQ=B(_Zz(_1zP,_1zr,_1zI,_1zO.b)),_1zR=B(_QT(_PU,_1zE,_1zF,_1zG,E(_1zQ.b))),_1zS=new T(function(){var _1zT=B(_ZH(_1x8,_1zI,_1zR.b));return new T2(0,_1zT.a,_1zT.b);}),_1zU=B(_ZQ(_128,_1xN,_1zI,new T(function(){return E(E(_1zS).b);},1))),_1zV=B(_fi(_1zE,_1zF,_1zG,E(_1zU.b))),_1zW=new T(function(){var _1zX=E(_1zV.a)&4294967295,_1zY=new T(function(){var _1zZ=function(_){var _1A0=(_1zM+1|0)-1|0,_1A1=function(_1A2){if(_1A2>=0){var _1A3=newArr(_1A2,_Vu),_1A4=_1A3,_1A5=function(_1A6){var _1A7=function(_1A8,_1A9,_){while(1){if(_1A8!=_1A6){var _1Aa=E(_1A9);if(!_1Aa._){return _5;}else{var _=_1A4[_1A8]=_1Aa.a,_1Ab=_1A8+1|0;_1A8=_1Ab;_1A9=_1Aa.b;continue;}}else{return _5;}}},_1Ac=B(_1A7(0,new T(function(){return B(_0(_1zN.a,_1zC));},1),_));return new T4(0,E(_1uI),E(_1A0),_1A2,_1A4);};if(0>_1A0){return new F(function(){return _1A5(0);});}else{var _1Ad=_1A0+1|0;if(_1Ad>=0){return new F(function(){return _1A5(_1Ad);});}else{return E(_1xc);}}}else{return E(_Vw);}};if(0>_1A0){var _1Ae=B(_1A1(0)),_1Af=E(_1Ae),_1Ag=_1Af.d;return new T4(0,E(_1Af.a),E(_1Af.b),_1Af.c,_1Ag);}else{var _1Ah=B(_1A1(_1A0+1|0)),_1Ai=E(_1Ah),_1Aj=_1Ai.d;return new T4(0,E(_1Ai.a),E(_1Ai.b),_1Ai.c,_1Aj);}};return B(_8O(_1zZ));}),_1Ak=new T(function(){var _1Al=_1zX-1|0;if(0<=_1Al){var _1Am=function(_1An){return new T2(1,new T2(0,_1An,new T2(1,_1zP,_4)),new T(function(){if(_1An!=_1Al){return B(_1Am(_1An+1|0));}else{return __Z;}}));};return B(_1pA(_Ux,B(_1Am(0))));}else{return E(_1zy);}}),_1Ao=new T(function(){var _1Ap=function(_){var _1Aq=(_1zP+1|0)-1|0,_1Ar=function(_1As){if(_1As>=0){var _1At=newArr(_1As,_Vu),_1Au=_1At,_1Av=function(_1Aw){var _1Ax=function(_1Ay,_1Az,_){while(1){if(_1Ay!=_1Aw){var _1AA=E(_1Az);if(!_1AA._){return _5;}else{var _=_1Au[_1Ay]=_1AA.a,_1AB=_1Ay+1|0;_1Ay=_1AB;_1Az=_1AA.b;continue;}}else{return _5;}}},_1AC=new T(function(){var _1AD=new T(function(){var _1AE=function(_){var _1AF=newByteArr(4),_1AG=_1AF,_1AH=function(_1AI,_){while(1){var _=_1AG["v"]["i32"][_1AI]=0,_1AJ=E(_1AI);if(!_1AJ){return _5;}else{_1AI=_1AJ+1|0;continue;}}},_1AK=B(_1AH(0,_)),_1AL=function(_1AM,_1AN,_){while(1){var _1AO=E(_1AM);if(_1AO==1){return _5;}else{var _1AP=E(_1AN);if(!_1AP._){return _5;}else{var _=_1AG["v"]["i32"][_1AO]=E(_1AP.a);_1AM=_1AO+1|0;_1AN=_1AP.b;continue;}}}},_1AQ=B(_1AL(0,new T2(1,_1zM,_4),_));return new T4(0,E(_1uI),E(_1uI),1,_1AG);},_1AR=B(_8O(_1AE));return new T5(0,_1zp,E(_1AR.a),E(_1AR.b),_1AR.c,_1AR.d);});return B(_0(_1zQ.a,new T2(1,_1AD,_4)));},1),_1AS=B(_1Ax(0,_1AC,_));return new T4(0,E(_1uI),E(_1Aq),_1As,_1Au);};if(0>_1Aq){return new F(function(){return _1Av(0);});}else{var _1AT=_1Aq+1|0;if(_1AT>=0){return new F(function(){return _1Av(_1AT);});}else{return E(_1xc);}}}else{return E(_Vw);}};if(0>_1Aq){var _1AU=B(_1Ar(0)),_1AV=E(_1AU),_1AW=_1AV.d;return new T4(0,E(_1AV.a),E(_1AV.b),_1AV.c,_1AW);}else{var _1AX=B(_1Ar(_1Aq+1|0)),_1AY=E(_1AX),_1AZ=_1AY.d;return new T4(0,E(_1AY.a),E(_1AY.b),_1AY.c,_1AZ);}};return B(_8O(_1Ap));});return {_:0,a:_1zJ.a,b:_1zK.a,c:_1Ao,d:_1zR.a,e:_1Ak,f:_1zY,g:new T(function(){var _1B0=E(E(_1zS).a);if(!_1B0._){return new T0(2);}else{var _1B1=E(_1B0.a);return B(_Qc(E(_1B1.a),_1B1.b,_1B0.b,_PV));}}),h:_Ux,i:_Rg,j:_1zU.a,k:_Ux,l:_1zX};});return new T2(0,_1zW,_1zV.b);},_1B2=function(_1B3,_1B4){var _1B5=E(_1B3),_1B6=B(_1zD(_1B5.a,_1B5.b,_1B5.c,_1B4));return new T2(0,_1B6.a,_1B6.b);},_1B7=function(_1B8,_1B9){var _1Ba=E(_1B8),_1Bb=B(_IY(_Jt,_LL,_1Ba,_1B9)),_1Bc=B(_ft(_1Ba.a,_1Ba.b,_1Ba.c,E(_1Bb.b)));return new T2(0,new T2(0,_1Bb.a,_1Bc.a),_1Bc.b);},_1Bd=function(_1Be,_1Bf){var _1Bg=new T(function(){var _1Bh=B(_ZH(_113,_1Be,_1Bf));return new T2(0,_1Bh.a,_1Bh.b);}),_1Bi=B(_ZH(_1B7,_1Be,new T(function(){return E(E(_1Bg).b);},1)));return new T2(0,new T2(0,new T(function(){return E(E(_1Bg).a);}),_1Bi.a),_1Bi.b);},_1Bj=function(_1Bk,_1Bl){var _1Bm=B(_1Bd(_1Bk,_1Bl));return new T2(0,_1Bm.a,_1Bm.b);},_1Bn=function(_1Bo,_1Bp,_1Bq,_1Br,_1Bs){var _1Bt=B(_ft(_1Bp,_1Bq,_1Br,_1Bs)),_1Bu=new T3(0,_1Bp,_1Bq,_1Br),_1Bv=B(_ZQ(_128,_123,_1Bu,_1Bt.b)),_1Bw=B(_ZQ(_128,_11Y,_1Bu,_1Bv.b)),_1Bx=B(_ZQ(_128,_1Bj,_1Bu,_1Bw.b)),_1By=B(_ZQ(_128,_1B2,_1Bu,_1Bx.b));return new T2(0,new T4(0,_1Bo,_1Bt.a,new T3(0,_1Bv.a,new T(function(){return B(_Zg(_1uE,_1Bw.a));}),new T(function(){return B(_Zg(_1uB,_1Bx.a));})),new T(function(){return B(_Zg(_1ux,_1By.a));})),_1By.b);},_1Bz=function(_1BA,_1BB,_1BC,_1BD){var _1BE=B(_ZQ(_128,_123,new T3(0,_1BA,_1BB,_1BC),_1BD));return new F(function(){return _1Bn(_1BE.a,_1BA,_1BB,_1BC,E(_1BE.b));});},_1BF=function(_1BG,_1BH){var _1BI=E(_1BH);return new F(function(){return _1sr(_1BI.a,_1BI.b,_1BI.c,_1BI.d,_1BI.e,_1BI.f,_1BI.g,_1BI.j,_1BI.l);});},_1BJ=function(_1BK,_1BL,_1BM,_1BN){var _1BO=new T3(0,_1BK,_1BL,_1BM),_1BP=B(_Wj(_1BO,_1BN)),_1BQ=B(_Wj(_1BO,_1BP.b)),_1BR=_1BQ.a,_1BS=_1BQ.b,_1BT=E(_1BP.a),_1BU=function(_1BV){var _1BW=E(_1BT);if(_1BW==1){var _1BX=E(_1BR);if(!E(_1BX)){return new F(function(){return _1Bz(_1BK,_1BL,_1BM,_1BS);});}else{return new F(function(){return _Wd(_1BX,1);});}}else{return new F(function(){return _Wd(_1BR,_1BW);});}};if(E(_1BT)==2){if(E(_1BR)>1){return new F(function(){return _1BU(_);});}else{var _1BY=B(_Uk(_fH,_M6,_1BK,_1BL,_1BM,E(_1BS))),_1BZ=B(_ft(_1BK,_1BL,_1BM,E(_1BY.b))),_1C0=B(_Zk(_1BK,_1BL,_1BM,E(_1BZ.b))),_1C1=_1C0.a,_1C2=B(_Uk(_fH,_Wb,_1BK,_1BL,_1BM,E(_1C0.b))),_1C3=new T(function(){return B(_Zg(function(_1C4){return new F(function(){return _1BF(_1C1,_1C4);});},_1C2.a));});return new T2(0,new T4(0,_1BY.a,_1BZ.a,_1C1,_1C3),_1C2.b);}}else{return new F(function(){return _1BU(_);});}},_1C5=function(_1C6,_1C7,_1C8,_1C9){while(1){var _1Ca=E(_1C9);if(!_1Ca._){var _1Cb=E(_1Ca.b);switch(B(_12T(_1C6,_1C7,_1C8,_1Cb.a,_1Cb.b,_1Cb.c))){case 0:_1C9=_1Ca.d;continue;case 1:return new T1(1,_1Ca.c);default:_1C9=_1Ca.e;continue;}}else{return __Z;}}},_1Cc=function(_1Cd){return E(E(E(_1Cd).c).b);},_1Ce=new T(function(){return B(_1z6(95));}),_1Cf=new T2(1,_1Ce,_4),_1Cg=new T(function(){var _1Ch=B(_1xU(_1Cf));return new T3(0,_1Ch.a,_1Ch.b,_1Ch.c);}),_1Ci=function(_1Cj,_1Ck,_1Cl,_1Cm,_1Cn){var _1Co=E(_1Cg);if(!B(_12M(_1Cj,_1Ck,_1Cl,_1Co.a,_1Co.b,_1Co.c))){var _1Cp=E(_1Cn),_1Cq=B(_1C5(_1Cp.a,_1Cp.b,_1Cp.c,E(_1Cm).b));if(!_1Cq._){return new T0(1);}else{var _1Cr=new T(function(){var _1Cs=E(E(_1Cq.a).a);return new T3(0,_1Cs.a,_1Cs.b,_1Cs.c);});return new T2(0,new T(function(){return E(E(_1Cr).b);}),new T(function(){return B(_G(_1Cc,E(_1Cr).a));}));}}else{return new T0(1);}},_1Ct=function(_1Cu,_1Cv,_1Cw,_1Cx){while(1){var _1Cy=E(_1Cx);if(!_1Cy._){var _1Cz=E(_1Cy.b);switch(B(_12T(_1Cu,_1Cv,_1Cw,_1Cz.a,_1Cz.b,_1Cz.c))){case 0:_1Cx=_1Cy.d;continue;case 1:return new T1(1,_1Cy.c);default:_1Cx=_1Cy.e;continue;}}else{return __Z;}}},_1CA=new T(function(){return B(unCStr("S"));}),_1CB=new T(function(){return B(_1za(_1CA));}),_1CC=new T(function(){return B(_G(_1z8,_1CB));}),_1CD=new T(function(){return B(unCStr("startcat"));}),_1CE=new T(function(){return B(_1za(_1CD));}),_1CF=new T(function(){return B(_G(_1z8,_1CE));}),_1CG=new T(function(){var _1CH=B(_1xU(_1CF));return new T3(0,_1CH.a,_1CH.b,_1CH.c);}),_1CI=function(_1CJ,_1CK){var _1CL=E(_1CG),_1CM=_1CL.a,_1CN=_1CL.b,_1CO=_1CL.c,_1CP=B(_1Ct(_1CM,_1CN,_1CO,_1CJ));if(!_1CP._){var _1CQ=B(_1Ct(_1CM,_1CN,_1CO,E(_1CK).a));if(!_1CQ._){return new F(function(){return _1xU(_1CC);});}else{var _1CR=E(_1CQ.a);if(!_1CR._){return new F(function(){return _1xU(B(_G(_1z8,B(_1za(_1CR.a)))));});}else{return new F(function(){return _1xU(_1CC);});}}}else{var _1CS=E(_1CP.a);if(!_1CS._){return new F(function(){return _1xU(B(_G(_1z8,B(_1za(_1CS.a)))));});}else{return new F(function(){return _1xU(_1CC);});}}},_1CT=function(_1CU,_1CV){return new T2(0,_1CU,_1CV);},_1CW=new T(function(){return B(unCStr("empty grammar, no abstract"));}),_1CX=new T(function(){return B(err(_1CW));}),_1CY=new T4(0,_Rg,_1Cg,_1CX,_Rg),_1CZ=function(_1D0,_1D1){while(1){var _1D2=B((function(_1D3,_1D4){var _1D5=E(_1D4);if(!_1D5._){_1D0=new T2(1,_1D5.b,new T(function(){return B(_1CZ(_1D3,_1D5.e));}));_1D1=_1D5.d;return __continue;}else{return E(_1D3);}})(_1D0,_1D1));if(_1D2!=__continue){return _1D2;}}},_1D6=function(_1D7,_1D8,_1D9){var _1Da=E(_1D8);if(!_1Da._){return __Z;}else{var _1Db=E(_1D9);return (_1Db._==0)?__Z:new T2(1,new T(function(){return B(A2(_1D7,_1Da.a,_1Db.a));}),new T(function(){return B(_1D6(_1D7,_1Da.b,_1Db.b));}));}},_1Dc=function(_1Dd,_1De,_1Df,_1Dg,_1Dh,_1Di){var _1Dj=E(_1Cg);if(!B(_12M(_1De,_1Df,_1Dg,_1Dj.a,_1Dj.b,_1Dj.c))){var _1Dk=new T(function(){var _1Dl=E(_1Dh),_1Dm=B(_1CZ(_4,_1Dl.b)),_1Dn=new T(function(){return B(_G(function(_1Do){return new F(function(){return _1Ci(_1De,_1Df,_1Dg,_1Dl,_1Do);});},_1Dm));},1);return B(_1D6(_1CT,_1Dm,_1Dn));});return new T3(0,new T(function(){var _1Dp=B(_1CI(_1Dd,_1Dh));return new T3(0,_1Dp.a,_1Dp.b,_1Dp.c);}),_1Dk,new T4(0,_1Dd,new T3(0,_1De,_1Df,_1Dg),_1Dh,_1Di));}else{return new T3(0,_1Dj,_4,_1CY);}},_1Dq=new T(function(){return eval("(function(a){var arr = new ByteArray(new a.constructor(a[\'buffer\']));return new T4(0,0,a[\'length\']-1,a[\'length\'],arr);})");}),_1Dr=function(_1Ds){return E(_1Ds);},_1Dt=function(_1Du){return E(E(_1Du).a);},_1Dv=function(_1Dw){return E(E(_1Dw).a);},_1Dx=function(_1Dy){return E(E(_1Dy).a);},_1Dz=function(_1DA){return E(E(_1DA).b);},_1DB=function(_1DC){return E(E(_1DC).a);},_1DD=function(_1DE){var _1DF=new T(function(){return B(A2(_1DB,B(_1Dt(B(_1Dx(B(_1Dv(B(_1Dz(_1DE)))))))),_1Dr));}),_1DG=function(_1DH){var _1DI=function(_){return new F(function(){return __app1(E(_1Dq),E(_1DH));});};return new F(function(){return A1(_1DF,_1DI);});};return E(_1DG);},_1DJ="(function(from, to, buf){return new Uint8Array(buf.buffer.slice(from, to+from));})",_1DK=function(_1DL,_1DM,_1DN,_1DO){var _1DP=function(_){var _1DQ=eval(E(_1DJ)),_1DR=__app3(E(_1DQ),E(_1DM),E(_1DN),E(_1DO));return new F(function(){return A3(_1DD,_1DL,_1DR,0);});};return new F(function(){return _z(_1DP);});},_1DS=0,_1DT=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1DU=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_1DV=new T(function(){return eval("(function(e){while(e.firstChild){e.removeChild(e.firstChild);}})");}),_1DW=new T(function(){return eval("(function(c,p){p.removeChild(c);})");}),_1DX=3,_1DY=new T(function(){return eval("document.body");}),_1DZ=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1E0=new T(function(){return B(unCStr("!!: negative index"));}),_1E1=new T(function(){return B(_0(_eb,_1E0));}),_1E2=new T(function(){return B(err(_1E1));}),_1E3=new T(function(){return B(unCStr("!!: index too large"));}),_1E4=new T(function(){return B(_0(_eb,_1E3));}),_1E5=new T(function(){return B(err(_1E4));}),_1E6=function(_1E7,_1E8){while(1){var _1E9=E(_1E7);if(!_1E9._){return E(_1E5);}else{var _1Ea=E(_1E8);if(!_1Ea){return E(_1E9.a);}else{_1E7=_1E9.b;_1E8=_1Ea-1|0;continue;}}}},_1Eb=function(_1Ec,_1Ed){if(_1Ed>=0){return new F(function(){return _1E6(_1Ec,_1Ed);});}else{return E(_1E2);}},_1Ee=function(_1Ef,_1Eg){var _1Eh=E(_1Ef);if(!_1Eh._){var _1Ei=E(_1Eh.c);if(!_1Ei._){return __Z;}else{var _1Ej=E(_1Eg);return (_1Ej>=0)?(_1Ej<B(_uU(_1Ei,0)))?new T1(1,new T(function(){return B(_1Eb(_1Ei,_1Ej));})):__Z:__Z;}}else{return __Z;}},_1Ek=function(_1El,_1Em){while(1){var _1En=B((function(_1Eo,_1Ep){var _1Eq=E(_1Ep);if(!_1Eq._){return new T1(1,_1Eo);}else{var _1Er=_1Eq.a,_1Es=E(_1Eq.b);if(!_1Es._){return new F(function(){return _1Ee(_1Eo,_1Er);});}else{var _1Et=E(_1Eo);if(!_1Et._){var _1Eu=E(_1Et.c);if(!_1Eu._){return __Z;}else{var _1Ev=E(_1Er);if(_1Ev>=0){if(_1Ev<B(_uU(_1Eu,0))){_1El=new T(function(){return B(_1Eb(_1Eu,_1Ev));});_1Em=_1Es;return __continue;}else{return __Z;}}else{return __Z;}}}else{return __Z;}}}})(_1El,_1Em));if(_1En!=__continue){return _1En;}}},_1Ew=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1Ex=new T(function(){return B(err(_1Ew));}),_1Ey=new T(function(){return new T2(0,_18z,_1Ez);}),_1Ez=function(_1EA,_1EB){return (!B(A3(_pM,_1Ey,_1EA,_1EB)))?true:false;},_1EC=new T2(0,_18z,_1Ez),_1ED=function(_1EE,_1EF){var _1EG=E(_1EE);if(!_1EG._){var _1EH=E(_1EF);if(!_1EH._){var _1EI=E(_1EG.a),_1EJ=E(_1EH.a);if(!B(_12M(_1EI.a,_1EI.b,_1EI.c,_1EJ.a,_1EJ.b,_1EJ.c))){return false;}else{return new F(function(){return _18O(_1EC,_1EG.b,_1EH.b);});}}else{return false;}}else{return (E(_1EF)._==0)?false:true;}},_1EK=function(_1EL,_1EM){return (!B(_1EN(_1EL,_1EM)))?true:false;},_1EO=new T(function(){return new T2(0,_1EN,_1EK);}),_1EN=function(_1EP,_1EQ){var _1ER=E(_1EP);if(!_1ER._){var _1ES=E(_1EQ);if(!_1ES._){var _1ET=E(_1ER.a),_1EU=E(_1ES.a);if(!B(_12M(_1ET.a,_1ET.b,_1ET.c,_1EU.a,_1EU.b,_1EU.c))){return false;}else{if(!B(_1ED(_1ER.b,_1ES.b))){return false;}else{return new F(function(){return _18O(_1EO,_1ER.c,_1ES.c);});}}}else{return false;}}else{var _1EV=E(_1EQ);if(!_1EV._){return false;}else{return new F(function(){return _18z(_1ER.a,_1EV.a);});}}},_1EW=function(_1EX,_1EY){while(1){var _1EZ=E(_1EX);if(!_1EZ._){return (E(_1EY)._==0)?true:false;}else{var _1F0=E(_1EY);if(!_1F0._){return false;}else{if(E(_1EZ.a)!=E(_1F0.a)){return false;}else{_1EX=_1EZ.b;_1EY=_1F0.b;continue;}}}}},_1F1=function(_1F2,_1F3,_1F4,_1F5){if(!B(_1EW(_1F2,_1F4))){return false;}else{return new F(function(){return _1EN(_1F3,_1F5);});}},_1F6=function(_1F7,_1F8){var _1F9=E(_1F7),_1Fa=E(_1F8);return new F(function(){return _1F1(_1F9.a,_1F9.b,_1Fa.a,_1Fa.b);});},_1Fb=function(_1Fc,_1Fd,_1Fe,_1Ff){return (!B(_1EW(_1Fc,_1Fe)))?true:(!B(_1EN(_1Fd,_1Ff)))?true:false;},_1Fg=function(_1Fh,_1Fi){var _1Fj=E(_1Fh),_1Fk=E(_1Fi);return new F(function(){return _1Fb(_1Fj.a,_1Fj.b,_1Fk.a,_1Fk.b);});},_1Fl=new T2(0,_1F6,_1Fg),_1Fm=function(_1Fn,_1Fo){var _1Fp=E(_1Fn),_1Fq=E(_1Fo);return (!B(_1EN(_1Fp.a,_1Fq.a)))?true:(!B(_1np(_1Fl,_1Fp.b,_1Fq.b)))?true:false;},_1Fr=function(_1Fs,_1Ft,_1Fu,_1Fv){if(!B(_1EN(_1Fs,_1Fu))){return false;}else{return new F(function(){return _1np(_1Fl,_1Ft,_1Fv);});}},_1Fw=function(_1Fx,_1Fy){var _1Fz=E(_1Fx),_1FA=E(_1Fy);return new F(function(){return _1Fr(_1Fz.a,_1Fz.b,_1FA.a,_1FA.b);});},_1FB=new T2(0,_1Fw,_1Fm),_1FC=function(_1FD,_1FE){var _1FF=E(_1FD),_1FG=E(_1FE);return (B(_12T(_1FF.a,_1FF.b,_1FF.c,_1FG.a,_1FG.b,_1FG.c))==0)?true:false;},_1FH=function(_1FI){var _1FJ=E(_1FI);return new F(function(){return _G(_12D,B(_IJ(_1FJ.a,_1FJ.b,_1FJ.c)));});},_1FK=function(_1FL,_1FM){return (B(_12d(B(_1FH(_1FL)),B(_1FH(_1FM))))==2)?false:true;},_1FN=function(_1FO,_1FP){var _1FQ=E(_1FO),_1FR=E(_1FP);return (B(_12T(_1FQ.a,_1FQ.b,_1FQ.c,_1FR.a,_1FR.b,_1FR.c))==2)?true:false;},_1FS=function(_1FT,_1FU){var _1FV=E(_1FT),_1FW=E(_1FU);return (B(_12T(_1FV.a,_1FV.b,_1FV.c,_1FW.a,_1FW.b,_1FW.c))==0)?false:true;},_1FX=function(_1FY,_1FZ){return (B(_12d(B(_1FH(_1FY)),B(_1FH(_1FZ))))==2)?E(_1FY):E(_1FZ);},_1G0=function(_1G1,_1G2){return (B(_12d(B(_1FH(_1G1)),B(_1FH(_1G2))))==2)?E(_1G2):E(_1G1);},_1G3={_:0,a:_1EC,b:_1b1,c:_1FC,d:_1FK,e:_1FN,f:_1FS,g:_1FX,h:_1G0},_1G4=function(_1G5,_1G6){var _1G7=E(_1G5);if(!_1G7._){var _1G8=E(_1G6);if(!_1G8._){var _1G9=E(_1G7.a),_1Ga=E(_1G8.a);switch(B(_12T(_1G9.a,_1G9.b,_1G9.c,_1Ga.a,_1Ga.b,_1Ga.c))){case 0:return 0;case 1:return new F(function(){return _1bD(_1G3,_1G7.b,_1G8.b);});break;default:return 2;}}else{return 0;}}else{return (E(_1G6)._==0)?2:1;}},_1Gb=function(_1Gc,_1Gd){var _1Ge=E(_1Gc);if(!_1Ge._){var _1Gf=E(_1Gd);if(!_1Gf._){var _1Gg=E(_1Ge.a),_1Gh=E(_1Gf.a);switch(B(_12T(_1Gg.a,_1Gg.b,_1Gg.c,_1Gh.a,_1Gh.b,_1Gh.c))){case 0:return true;case 1:switch(B(_1G4(_1Ge.b,_1Gf.b))){case 0:return true;case 1:return (B(_1bD(_1Gi,_1Ge.c,_1Gf.c))==0)?true:false;default:return false;}break;default:return false;}}else{return true;}}else{var _1Gj=E(_1Gd);if(!_1Gj._){return false;}else{return new F(function(){return _1FC(_1Ge.a,_1Gj.a);});}}},_1Gk=function(_1Gl,_1Gm){var _1Gn=E(_1Gl);if(!_1Gn._){var _1Go=E(_1Gm);if(!_1Go._){var _1Gp=E(_1Gn.a),_1Gq=E(_1Go.a);switch(B(_12T(_1Gp.a,_1Gp.b,_1Gp.c,_1Gq.a,_1Gq.b,_1Gq.c))){case 0:return true;case 1:switch(B(_1G4(_1Gn.b,_1Go.b))){case 0:return true;case 1:return (B(_1bD(_1Gi,_1Gn.c,_1Go.c))==2)?false:true;default:return false;}break;default:return false;}}else{return true;}}else{var _1Gr=E(_1Gm);if(!_1Gr._){return false;}else{return new F(function(){return _1FK(_1Gn.a,_1Gr.a);});}}},_1Gs=function(_1Gt,_1Gu){var _1Gv=E(_1Gt);if(!_1Gv._){var _1Gw=E(_1Gu);if(!_1Gw._){var _1Gx=E(_1Gv.a),_1Gy=E(_1Gw.a);switch(B(_12T(_1Gx.a,_1Gx.b,_1Gx.c,_1Gy.a,_1Gy.b,_1Gy.c))){case 0:return false;case 1:switch(B(_1G4(_1Gv.b,_1Gw.b))){case 0:return false;case 1:return (B(_1bD(_1Gi,_1Gv.c,_1Gw.c))==2)?true:false;default:return true;}break;default:return true;}}else{return false;}}else{var _1Gz=E(_1Gu);if(!_1Gz._){return true;}else{return new F(function(){return _1FN(_1Gv.a,_1Gz.a);});}}},_1GA=function(_1GB,_1GC){var _1GD=E(_1GB);if(!_1GD._){var _1GE=E(_1GC);if(!_1GE._){var _1GF=E(_1GD.a),_1GG=E(_1GE.a);switch(B(_12T(_1GF.a,_1GF.b,_1GF.c,_1GG.a,_1GG.b,_1GG.c))){case 0:return false;case 1:switch(B(_1G4(_1GD.b,_1GE.b))){case 0:return false;case 1:return (B(_1bD(_1Gi,_1GD.c,_1GE.c))==0)?false:true;default:return true;}break;default:return true;}}else{return false;}}else{var _1GH=E(_1GC);if(!_1GH._){return true;}else{return new F(function(){return _1FS(_1GD.a,_1GH.a);});}}},_1GI=function(_1GJ,_1GK){return (!B(_1Gk(_1GJ,_1GK)))?E(_1GJ):E(_1GK);},_1GL=function(_1GM,_1GN){return (!B(_1Gk(_1GM,_1GN)))?E(_1GN):E(_1GM);},_1Gi=new T(function(){return {_:0,a:_1EO,b:_1GO,c:_1Gb,d:_1Gk,e:_1Gs,f:_1GA,g:_1GI,h:_1GL};}),_1GO=function(_1GP,_1GQ){var _1GR=E(_1GP);if(!_1GR._){var _1GS=E(_1GQ);if(!_1GS._){var _1GT=E(_1GR.a),_1GU=E(_1GS.a);switch(B(_12T(_1GT.a,_1GT.b,_1GT.c,_1GU.a,_1GU.b,_1GU.c))){case 0:return 0;case 1:switch(B(_1G4(_1GR.b,_1GS.b))){case 0:return 0;case 1:return new F(function(){return _1bD(_1Gi,_1GR.c,_1GS.c);});break;default:return 2;}break;default:return 2;}}else{return 0;}}else{var _1GV=E(_1GQ);if(!_1GV._){return 2;}else{return new F(function(){return _1b1(_1GR.a,_1GV.a);});}}},_1GW=function(_1GX,_1GY){while(1){var _1GZ=E(_1GX);if(!_1GZ._){return (E(_1GY)._==0)?1:0;}else{var _1H0=E(_1GY);if(!_1H0._){return 2;}else{var _1H1=E(_1GZ.a),_1H2=E(_1H0.a);if(_1H1>=_1H2){if(_1H1!=_1H2){return 2;}else{_1GX=_1GZ.b;_1GY=_1H0.b;continue;}}else{return 0;}}}}},_1H3=function(_1H4,_1H5,_1H6,_1H7){switch(B(_1GW(_1H4,_1H6))){case 0:return 0;case 1:return new F(function(){return _1GO(_1H5,_1H7);});break;default:return 2;}},_1H8=function(_1H9,_1Ha){var _1Hb=E(_1H9),_1Hc=E(_1Ha);return new F(function(){return _1H3(_1Hb.a,_1Hb.b,_1Hc.a,_1Hc.b);});},_1Hd=function(_1He,_1Hf,_1Hg,_1Hh){switch(B(_1GW(_1He,_1Hg))){case 0:return true;case 1:return new F(function(){return _1Gb(_1Hf,_1Hh);});break;default:return false;}},_1Hi=function(_1Hj,_1Hk){var _1Hl=E(_1Hj),_1Hm=E(_1Hk);return new F(function(){return _1Hd(_1Hl.a,_1Hl.b,_1Hm.a,_1Hm.b);});},_1Hn=function(_1Ho,_1Hp,_1Hq,_1Hr){switch(B(_1GW(_1Ho,_1Hq))){case 0:return true;case 1:return new F(function(){return _1Gk(_1Hp,_1Hr);});break;default:return false;}},_1Hs=function(_1Ht,_1Hu){var _1Hv=E(_1Ht),_1Hw=E(_1Hu);return new F(function(){return _1Hn(_1Hv.a,_1Hv.b,_1Hw.a,_1Hw.b);});},_1Hx=function(_1Hy,_1Hz,_1HA,_1HB){switch(B(_1GW(_1Hy,_1HA))){case 0:return false;case 1:return new F(function(){return _1Gs(_1Hz,_1HB);});break;default:return true;}},_1HC=function(_1HD,_1HE){var _1HF=E(_1HD),_1HG=E(_1HE);return new F(function(){return _1Hx(_1HF.a,_1HF.b,_1HG.a,_1HG.b);});},_1HH=function(_1HI,_1HJ,_1HK,_1HL){switch(B(_1GW(_1HI,_1HK))){case 0:return false;case 1:return new F(function(){return _1GA(_1HJ,_1HL);});break;default:return true;}},_1HM=function(_1HN,_1HO){var _1HP=E(_1HN),_1HQ=E(_1HO);return new F(function(){return _1HH(_1HP.a,_1HP.b,_1HQ.a,_1HQ.b);});},_1HR=function(_1HS,_1HT){var _1HU=E(_1HS),_1HV=E(_1HT);switch(B(_1GW(_1HU.a,_1HV.a))){case 0:return E(_1HV);case 1:return (!B(_1Gk(_1HU.b,_1HV.b)))?E(_1HU):E(_1HV);default:return E(_1HU);}},_1HW=function(_1HX,_1HY){var _1HZ=E(_1HX),_1I0=E(_1HY);switch(B(_1GW(_1HZ.a,_1I0.a))){case 0:return E(_1HZ);case 1:return (!B(_1Gk(_1HZ.b,_1I0.b)))?E(_1I0):E(_1HZ);default:return E(_1I0);}},_1I1={_:0,a:_1Fl,b:_1H8,c:_1Hi,d:_1Hs,e:_1HC,f:_1HM,g:_1HR,h:_1HW},_1I2=function(_1I3){return new F(function(){return _1ni(_4,_1I3);});},_1I4=function(_1I5,_1I6,_1I7,_1I8){switch(B(_1GO(_1I5,_1I7))){case 0:return true;case 1:return (B(_1bD(_1I1,B(_1I2(_1I6)),B(_1I2(_1I8))))==0)?true:false;default:return false;}},_1I9=function(_1Ia,_1Ib){var _1Ic=E(_1Ia),_1Id=E(_1Ib);return new F(function(){return _1I4(_1Ic.a,_1Ic.b,_1Id.a,_1Id.b);});},_1Ie=function(_1If,_1Ig,_1Ih,_1Ii){switch(B(_1GO(_1If,_1Ih))){case 0:return true;case 1:return (B(_1bD(_1I1,B(_1I2(_1Ig)),B(_1I2(_1Ii))))==2)?false:true;default:return false;}},_1Ij=function(_1Ik,_1Il){var _1Im=E(_1Ik),_1In=E(_1Il);return new F(function(){return _1Ie(_1Im.a,_1Im.b,_1In.a,_1In.b);});},_1Io=function(_1Ip,_1Iq,_1Ir,_1Is){switch(B(_1GO(_1Ip,_1Ir))){case 0:return false;case 1:return (B(_1bD(_1I1,B(_1I2(_1Iq)),B(_1I2(_1Is))))==2)?true:false;default:return true;}},_1It=function(_1Iu,_1Iv){var _1Iw=E(_1Iu),_1Ix=E(_1Iv);return new F(function(){return _1Io(_1Iw.a,_1Iw.b,_1Ix.a,_1Ix.b);});},_1Iy=function(_1Iz,_1IA,_1IB,_1IC){switch(B(_1GO(_1Iz,_1IB))){case 0:return false;case 1:return (B(_1bD(_1I1,B(_1I2(_1IA)),B(_1I2(_1IC))))==0)?false:true;default:return true;}},_1ID=function(_1IE,_1IF){var _1IG=E(_1IE),_1IH=E(_1IF);return new F(function(){return _1Iy(_1IG.a,_1IG.b,_1IH.a,_1IH.b);});},_1II=function(_1IJ,_1IK,_1IL,_1IM){switch(B(_1GO(_1IJ,_1IL))){case 0:return 0;case 1:return new F(function(){return _1bD(_1I1,B(_1I2(_1IK)),B(_1I2(_1IM)));});break;default:return 2;}},_1IN=function(_1IO,_1IP){var _1IQ=E(_1IO),_1IR=E(_1IP);return new F(function(){return _1II(_1IQ.a,_1IQ.b,_1IR.a,_1IR.b);});},_1IS=function(_1IT,_1IU){var _1IV=E(_1IT),_1IW=E(_1IU);switch(B(_1GO(_1IV.a,_1IW.a))){case 0:return E(_1IW);case 1:return (B(_1bD(_1I1,B(_1I2(_1IV.b)),B(_1I2(_1IW.b))))==2)?E(_1IV):E(_1IW);default:return E(_1IV);}},_1IX=function(_1IY,_1IZ){var _1J0=E(_1IY),_1J1=E(_1IZ);switch(B(_1GO(_1J0.a,_1J1.a))){case 0:return E(_1J0);case 1:return (B(_1bD(_1I1,B(_1I2(_1J0.b)),B(_1I2(_1J1.b))))==2)?E(_1J1):E(_1J0);default:return E(_1J1);}},_1J2={_:0,a:_1FB,b:_1IN,c:_1I9,d:_1Ij,e:_1It,f:_1ID,g:_1IS,h:_1IX},_1J3=function(_1J4,_1J5,_1J6){var _1J7=E(_1J6);if(!_1J7._){var _1J8=_1J7.c,_1J9=_1J7.d,_1Ja=E(_1J7.b);switch(B(_1GO(_1J4,_1Ja.a))){case 0:return new F(function(){return _Ns(_1Ja,B(_1J3(_1J4,_1J5,_1J8)),_1J9);});break;case 1:switch(B(_1bD(_1I1,B(_1I2(_1J5)),B(_1I2(_1Ja.b))))){case 0:return new F(function(){return _Ns(_1Ja,B(_1J3(_1J4,_1J5,_1J8)),_1J9);});break;case 1:return new F(function(){return _15i(_1J8,_1J9);});break;default:return new F(function(){return _MQ(_1Ja,_1J8,B(_1J3(_1J4,_1J5,_1J9)));});}break;default:return new F(function(){return _MQ(_1Ja,_1J8,B(_1J3(_1J4,_1J5,_1J9)));});}}else{return new T0(1);}},_1Jb=function(_1Jc,_1Jd){var _1Je=E(_1Jc),_1Jf=E(_1Jd);if(!_1Jf._){var _1Jg=_1Jf.b,_1Jh=_1Jf.c,_1Ji=_1Jf.d;switch(B(_1bD(_1J2,B(_1ni(_4,_1Je)),B(_1ni(_4,_1Jg))))){case 0:return new F(function(){return _MQ(_1Jg,B(_1Jb(_1Je,_1Jh)),_1Ji);});break;case 1:return new T4(0,_1Jf.a,E(_1Je),E(_1Jh),E(_1Ji));default:return new F(function(){return _Ns(_1Jg,_1Jh,B(_1Jb(_1Je,_1Ji)));});}}else{return new T4(0,1,E(_1Je),E(_ML),E(_ML));}},_1Jj=function(_1Jk,_1Jl){while(1){var _1Jm=E(_1Jl);if(!_1Jm._){return E(_1Jk);}else{var _1Jn=B(_1Jb(_1Jm.a,_1Jk));_1Jk=_1Jn;_1Jl=_1Jm.b;continue;}}},_1Jo=function(_1Jp,_1Jq){var _1Jr=E(_1Jq);if(!_1Jr._){return new T3(0,_ML,_4,_4);}else{var _1Js=_1Jr.a,_1Jt=E(_1Jp);if(_1Jt==1){var _1Ju=E(_1Jr.b);return (_1Ju._==0)?new T3(0,new T(function(){return new T4(0,1,E(_1Js),E(_ML),E(_ML));}),_4,_4):(B(_1bD(_1J2,B(_1I2(_1Js)),B(_1I2(_1Ju.a))))==0)?new T3(0,new T(function(){return new T4(0,1,E(_1Js),E(_ML),E(_ML));}),_1Ju,_4):new T3(0,new T(function(){return new T4(0,1,E(_1Js),E(_ML),E(_ML));}),_4,_1Ju);}else{var _1Jv=B(_1Jo(_1Jt>>1,_1Jr)),_1Jw=_1Jv.a,_1Jx=_1Jv.c,_1Jy=E(_1Jv.b);if(!_1Jy._){return new T3(0,_1Jw,_4,_1Jx);}else{var _1Jz=_1Jy.a,_1JA=E(_1Jy.b);if(!_1JA._){return new T3(0,new T(function(){return B(_O8(_1Jz,_1Jw));}),_4,_1Jx);}else{if(!B(_1bD(_1J2,B(_1I2(_1Jz)),B(_1I2(_1JA.a))))){var _1JB=B(_1Jo(_1Jt>>1,_1JA));return new T3(0,new T(function(){return B(_OM(_1Jz,_1Jw,_1JB.a));}),_1JB.b,_1JB.c);}else{return new T3(0,_1Jw,_4,_1Jy);}}}}}},_1JC=function(_1JD,_1JE,_1JF){while(1){var _1JG=E(_1JF);if(!_1JG._){return E(_1JE);}else{var _1JH=_1JG.a,_1JI=E(_1JG.b);if(!_1JI._){return new F(function(){return _O8(_1JH,_1JE);});}else{if(!B(_1bD(_1J2,B(_1I2(_1JH)),B(_1I2(_1JI.a))))){var _1JJ=B(_1Jo(_1JD,_1JI)),_1JK=_1JJ.a,_1JL=E(_1JJ.c);if(!_1JL._){var _1JM=_1JD<<1,_1JN=B(_OM(_1JH,_1JE,_1JK));_1JD=_1JM;_1JE=_1JN;_1JF=_1JJ.b;continue;}else{return new F(function(){return _1Jj(B(_OM(_1JH,_1JE,_1JK)),_1JL);});}}else{return new F(function(){return _1Jj(_1JE,_1JG);});}}}}},_1JO=function(_1JP){var _1JQ=E(_1JP);if(!_1JQ._){return new T0(1);}else{var _1JR=_1JQ.a,_1JS=E(_1JQ.b);if(!_1JS._){return new T4(0,1,E(_1JR),E(_ML),E(_ML));}else{if(!B(_1bD(_1J2,B(_1I2(_1JR)),B(_1I2(_1JS.a))))){return new F(function(){return _1JC(1,new T4(0,1,E(_1JR),E(_ML),E(_ML)),_1JS);});}else{return new F(function(){return _1Jj(new T4(0,1,E(_1JR),E(_ML),E(_ML)),_1JS);});}}}},_1JT=function(_1JU,_1JV){while(1){var _1JW=E(_1JV);if(!_1JW._){return E(_1JU);}else{var _1JX=_1JW.a,_1JY=E(_1JU);if(!_1JY._){var _1JZ=E(_1JX);if(!_1JZ._){var _1K0=B(_1jx(_1J2,_1il,_1il,_1JY.a,_1JY.b,_1JY.c,_1JY.d,_1JZ.a,_1JZ.b,_1JZ.c,_1JZ.d));}else{var _1K0=E(_1JY);}var _1K1=_1K0;}else{var _1K1=E(_1JX);}_1JU=_1K1;_1JV=_1JW.b;continue;}}},_1K2=function(_1K3,_1K4,_1K5){var _1K6=E(_1K5);if(!_1K6._){var _1K7=_1K6.c,_1K8=_1K6.d,_1K9=E(_1K6.b);switch(B(_1GO(_1K3,_1K9.a))){case 0:return new F(function(){return _MQ(_1K9,B(_1K2(_1K3,_1K4,_1K7)),_1K8);});break;case 1:switch(B(_1bD(_1I1,B(_1I2(_1K4)),B(_1I2(_1K9.b))))){case 0:return new F(function(){return _MQ(_1K9,B(_1K2(_1K3,_1K4,_1K7)),_1K8);});break;case 1:return new T4(0,_1K6.a,E(new T2(0,_1K3,_1K4)),E(_1K7),E(_1K8));default:return new F(function(){return _Ns(_1K9,_1K7,B(_1K2(_1K3,_1K4,_1K8)));});}break;default:return new F(function(){return _Ns(_1K9,_1K7,B(_1K2(_1K3,_1K4,_1K8)));});}}else{return new T4(0,1,E(new T2(0,_1K3,_1K4)),E(_ML),E(_ML));}},_1Ka=function(_1Kb,_1Kc){while(1){var _1Kd=E(_1Kc);if(!_1Kd._){return E(_1Kb);}else{var _1Ke=E(_1Kd.a),_1Kf=B(_1K2(_1Ke.a,_1Ke.b,_1Kb));_1Kb=_1Kf;_1Kc=_1Kd.b;continue;}}},_1Kg=function(_1Kh,_1Ki){var _1Kj=E(_1Ki);if(!_1Kj._){return new T3(0,_ML,_4,_4);}else{var _1Kk=_1Kj.a,_1Kl=E(_1Kh);if(_1Kl==1){var _1Km=E(_1Kj.b);if(!_1Km._){return new T3(0,new T(function(){return new T4(0,1,E(_1Kk),E(_ML),E(_ML));}),_4,_4);}else{var _1Kn=E(_1Kk),_1Ko=E(_1Km.a);switch(B(_1GO(_1Kn.a,_1Ko.a))){case 0:return new T3(0,new T4(0,1,E(_1Kn),E(_ML),E(_ML)),_1Km,_4);case 1:return (B(_1bD(_1I1,B(_1I2(_1Kn.b)),B(_1I2(_1Ko.b))))==0)?new T3(0,new T4(0,1,E(_1Kn),E(_ML),E(_ML)),_1Km,_4):new T3(0,new T4(0,1,E(_1Kn),E(_ML),E(_ML)),_4,_1Km);default:return new T3(0,new T4(0,1,E(_1Kn),E(_ML),E(_ML)),_4,_1Km);}}}else{var _1Kp=B(_1Kg(_1Kl>>1,_1Kj)),_1Kq=_1Kp.a,_1Kr=_1Kp.c,_1Ks=E(_1Kp.b);if(!_1Ks._){return new T3(0,_1Kq,_4,_1Kr);}else{var _1Kt=_1Ks.a,_1Ku=E(_1Ks.b);if(!_1Ku._){return new T3(0,new T(function(){return B(_O8(_1Kt,_1Kq));}),_4,_1Kr);}else{var _1Kv=E(_1Kt),_1Kw=E(_1Ku.a),_1Kx=function(_1Ky){var _1Kz=B(_1Kg(_1Kl>>1,_1Ku));return new T3(0,new T(function(){return B(_OM(_1Kv,_1Kq,_1Kz.a));}),_1Kz.b,_1Kz.c);};switch(B(_1GO(_1Kv.a,_1Kw.a))){case 0:return new F(function(){return _1Kx(_);});break;case 1:if(!B(_1bD(_1I1,B(_1I2(_1Kv.b)),B(_1I2(_1Kw.b))))){return new F(function(){return _1Kx(_);});}else{return new T3(0,_1Kq,_4,_1Ks);}break;default:return new T3(0,_1Kq,_4,_1Ks);}}}}}},_1KA=function(_1KB,_1KC,_1KD){var _1KE=E(_1KD);if(!_1KE._){return E(_1KC);}else{var _1KF=_1KE.a,_1KG=E(_1KE.b);if(!_1KG._){return new F(function(){return _O8(_1KF,_1KC);});}else{var _1KH=E(_1KF),_1KI=E(_1KG.a),_1KJ=function(_1KK){var _1KL=B(_1Kg(_1KB,_1KG)),_1KM=_1KL.a,_1KN=E(_1KL.c);if(!_1KN._){return new F(function(){return _1KA(_1KB<<1,B(_OM(_1KH,_1KC,_1KM)),_1KL.b);});}else{return new F(function(){return _1Ka(B(_OM(_1KH,_1KC,_1KM)),_1KN);});}};switch(B(_1GO(_1KH.a,_1KI.a))){case 0:return new F(function(){return _1KJ(_);});break;case 1:if(!B(_1bD(_1I1,B(_1I2(_1KH.b)),B(_1I2(_1KI.b))))){return new F(function(){return _1KJ(_);});}else{return new F(function(){return _1Ka(_1KC,_1KE);});}break;default:return new F(function(){return _1Ka(_1KC,_1KE);});}}}},_1KO=function(_1KP){var _1KQ=E(_1KP);if(!_1KQ._){return new T0(1);}else{var _1KR=_1KQ.a,_1KS=E(_1KQ.b);if(!_1KS._){return new T4(0,1,E(_1KR),E(_ML),E(_ML));}else{var _1KT=E(_1KR),_1KU=E(_1KS.a);switch(B(_1GO(_1KT.a,_1KU.a))){case 0:return new F(function(){return _1KA(1,new T4(0,1,E(_1KT),E(_ML),E(_ML)),_1KS);});break;case 1:if(!B(_1bD(_1I1,B(_1I2(_1KT.b)),B(_1I2(_1KU.b))))){return new F(function(){return _1KA(1,new T4(0,1,E(_1KT),E(_ML),E(_ML)),_1KS);});}else{return new F(function(){return _1Ka(new T4(0,1,E(_1KT),E(_ML),E(_ML)),_1KS);});}break;default:return new F(function(){return _1Ka(new T4(0,1,E(_1KT),E(_ML),E(_ML)),_1KS);});}}}},_1KV=function(_1KW,_1KX,_1KY){var _1KZ=E(_1KY);if(!_1KZ._){var _1L0=_1KZ.c,_1L1=_1KZ.d,_1L2=E(_1KZ.b);switch(B(_1GW(_1KW,_1L2.a))){case 0:return new F(function(){return _MQ(_1L2,B(_1KV(_1KW,_1KX,_1L0)),_1L1);});break;case 1:switch(B(_1GO(_1KX,_1L2.b))){case 0:return new F(function(){return _MQ(_1L2,B(_1KV(_1KW,_1KX,_1L0)),_1L1);});break;case 1:return new T4(0,_1KZ.a,E(new T2(0,_1KW,_1KX)),E(_1L0),E(_1L1));default:return new F(function(){return _Ns(_1L2,_1L0,B(_1KV(_1KW,_1KX,_1L1)));});}break;default:return new F(function(){return _Ns(_1L2,_1L0,B(_1KV(_1KW,_1KX,_1L1)));});}}else{return new T4(0,1,E(new T2(0,_1KW,_1KX)),E(_ML),E(_ML));}},_1L3=function(_1L4,_1L5){while(1){var _1L6=E(_1L5);if(!_1L6._){return E(_1L4);}else{var _1L7=E(_1L6.a),_1L8=B(_1KV(_1L7.a,_1L7.b,_1L4));_1L4=_1L8;_1L5=_1L6.b;continue;}}},_1L9=function(_1La,_1Lb){var _1Lc=E(_1Lb);if(!_1Lc._){return new T3(0,_ML,_4,_4);}else{var _1Ld=_1Lc.a,_1Le=E(_1La);if(_1Le==1){var _1Lf=E(_1Lc.b);if(!_1Lf._){return new T3(0,new T(function(){return new T4(0,1,E(_1Ld),E(_ML),E(_ML));}),_4,_4);}else{var _1Lg=E(_1Ld),_1Lh=E(_1Lf.a);switch(B(_1GW(_1Lg.a,_1Lh.a))){case 0:return new T3(0,new T4(0,1,E(_1Lg),E(_ML),E(_ML)),_1Lf,_4);case 1:return (!B(_1GA(_1Lg.b,_1Lh.b)))?new T3(0,new T4(0,1,E(_1Lg),E(_ML),E(_ML)),_1Lf,_4):new T3(0,new T4(0,1,E(_1Lg),E(_ML),E(_ML)),_4,_1Lf);default:return new T3(0,new T4(0,1,E(_1Lg),E(_ML),E(_ML)),_4,_1Lf);}}}else{var _1Li=B(_1L9(_1Le>>1,_1Lc)),_1Lj=_1Li.a,_1Lk=_1Li.c,_1Ll=E(_1Li.b);if(!_1Ll._){return new T3(0,_1Lj,_4,_1Lk);}else{var _1Lm=_1Ll.a,_1Ln=E(_1Ll.b);if(!_1Ln._){return new T3(0,new T(function(){return B(_O8(_1Lm,_1Lj));}),_4,_1Lk);}else{var _1Lo=E(_1Lm),_1Lp=E(_1Ln.a);switch(B(_1GW(_1Lo.a,_1Lp.a))){case 0:var _1Lq=B(_1L9(_1Le>>1,_1Ln));return new T3(0,new T(function(){return B(_OM(_1Lo,_1Lj,_1Lq.a));}),_1Lq.b,_1Lq.c);case 1:if(!B(_1GA(_1Lo.b,_1Lp.b))){var _1Lr=B(_1L9(_1Le>>1,_1Ln));return new T3(0,new T(function(){return B(_OM(_1Lo,_1Lj,_1Lr.a));}),_1Lr.b,_1Lr.c);}else{return new T3(0,_1Lj,_4,_1Ll);}break;default:return new T3(0,_1Lj,_4,_1Ll);}}}}}},_1Ls=function(_1Lt,_1Lu,_1Lv){var _1Lw=E(_1Lv);if(!_1Lw._){return E(_1Lu);}else{var _1Lx=_1Lw.a,_1Ly=E(_1Lw.b);if(!_1Ly._){return new F(function(){return _O8(_1Lx,_1Lu);});}else{var _1Lz=E(_1Lx),_1LA=E(_1Ly.a),_1LB=function(_1LC){var _1LD=B(_1L9(_1Lt,_1Ly)),_1LE=_1LD.a,_1LF=E(_1LD.c);if(!_1LF._){return new F(function(){return _1Ls(_1Lt<<1,B(_OM(_1Lz,_1Lu,_1LE)),_1LD.b);});}else{return new F(function(){return _1L3(B(_OM(_1Lz,_1Lu,_1LE)),_1LF);});}};switch(B(_1GW(_1Lz.a,_1LA.a))){case 0:return new F(function(){return _1LB(_);});break;case 1:if(!B(_1GA(_1Lz.b,_1LA.b))){return new F(function(){return _1LB(_);});}else{return new F(function(){return _1L3(_1Lu,_1Lw);});}break;default:return new F(function(){return _1L3(_1Lu,_1Lw);});}}}},_1LG=function(_1LH){var _1LI=E(_1LH);if(!_1LI._){return new T0(1);}else{var _1LJ=_1LI.a,_1LK=E(_1LI.b);if(!_1LK._){return new T4(0,1,E(_1LJ),E(_ML),E(_ML));}else{var _1LL=E(_1LJ),_1LM=E(_1LK.a);switch(B(_1GW(_1LL.a,_1LM.a))){case 0:return new F(function(){return _1Ls(1,new T4(0,1,E(_1LL),E(_ML),E(_ML)),_1LK);});break;case 1:if(!B(_1GA(_1LL.b,_1LM.b))){return new F(function(){return _1Ls(1,new T4(0,1,E(_1LL),E(_ML),E(_ML)),_1LK);});}else{return new F(function(){return _1L3(new T4(0,1,E(_1LL),E(_ML),E(_ML)),_1LK);});}break;default:return new F(function(){return _1L3(new T4(0,1,E(_1LL),E(_ML),E(_ML)),_1LK);});}}}},_1LN=function(_1LO){return new T1(1,_1LO);},_1LP=function(_1LQ){return E(E(_1LQ).a);},_1LR=function(_1LS,_1LT){var _1LU=E(_1LS);if(!_1LU._){var _1LV=_1LU.c,_1LW=B(_uU(_1LV,0));if(0<=_1LW){var _1LX=function(_1LY,_1LZ){var _1M0=E(_1LZ);if(!_1M0._){return __Z;}else{return new F(function(){return _0(B(_1LR(_1M0.a,new T(function(){return B(_0(_1LT,new T2(1,_1LY,_4)));}))),new T(function(){if(_1LY!=_1LW){return B(_1LX(_1LY+1|0,_1M0.b));}else{return __Z;}},1));});}};return new F(function(){return _1LX(0,_1LV);});}else{return __Z;}}else{return new T2(1,new T2(0,_1LT,_1LU.a),_4);}},_1M1=function(_1M2,_1M3){var _1M4=E(_1M3);if(!_1M4._){return new T2(0,_4,_4);}else{var _1M5=_1M4.a,_1M6=_1M4.b,_1M7=E(_1M2);if(_1M7==1){return new T2(0,new T2(1,_1M5,_4),_1M6);}else{var _1M8=new T(function(){var _1M9=B(_1M1(_1M7-1|0,_1M6));return new T2(0,_1M9.a,_1M9.b);});return new T2(0,new T2(1,_1M5,new T(function(){return E(E(_1M8).a);})),new T(function(){return E(E(_1M8).b);}));}}},_1Ma=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_1Mb=function(_1Mc){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_1Mc,_1Ma));})),_6y);});},_1Md=new T(function(){return B(_1Mb("Muste/Tree/Internal.hs:217:9-39|(pre, _ : post)"));}),_1Me=function(_1Mf,_1Mg,_1Mh){if(0>_1Mg){return E(_1Mf);}else{if(_1Mg>=B(_uU(_1Mf,0))){return E(_1Mf);}else{if(_1Mg>0){var _1Mi=B(_1M1(_1Mg,_1Mf)),_1Mj=E(_1Mi.b);if(!_1Mj._){return E(_1Md);}else{return new F(function(){return _0(_1Mi.a,new T2(1,_1Mh,_1Mj.b));});}}else{var _1Mk=E(_1Mf);if(!_1Mk._){return E(_1Md);}else{return new F(function(){return _0(_4,new T2(1,_1Mh,_1Mk.b));});}}}}},_1Ml=function(_1Mm,_1Mn,_1Mo){var _1Mp=E(_1Mm);if(!_1Mp._){var _1Mq=_1Mp.c,_1Mr=E(_1Mn);if(!_1Mr._){return E(_1Mo);}else{var _1Ms=E(_1Mr.a);if(_1Ms<0){return E(_1Mp);}else{var _1Mt=B(_uU(_1Mq,0));if(_1Ms>=_1Mt){return E(_1Mp);}else{var _1Mu=new T(function(){return B(_1Me(_1Mq,_1Ms,new T(function(){var _1Mv=E(_1Mq);if(!_1Mv._){return E(_1Ex);}else{if(_1Ms>=0){if(_1Ms<_1Mt){return B(_1Ml(B(_1Eb(_1Mv,_1Ms)),_1Mr.b,_1Mo));}else{return E(_1Ex);}}else{return E(_1Ex);}}})));});return new T3(0,_1Mp.a,_1Mp.b,_1Mu);}}}}else{return (E(_1Mn)._==0)?E(_1Mo):E(_1Mp);}},_1Mw=function(_1Mx,_1My,_1Mz,_1MA,_1MB){while(1){var _1MC=B((function(_1MD,_1ME,_1MF,_1MG,_1MH){var _1MI=E(_1MG);if(!_1MI._){var _1MJ=E(_1MH);if(!_1MJ._){return new T2(0,_1MD,_1ME);}else{var _1MK=_1MJ.a,_1ML=new T3(0,_1MF,_1MI,new T(function(){return B(_G(_1LN,_1MI.b));})),_1MM=new T(function(){var _1MN=function(_1MO){var _1MP=E(_1MO);return new T2(0,new T(function(){return B(_0(_1MK,_1MP.a));}),new T1(1,_1MP.b));},_1MQ=B(_1LG(B(_G(_1MN,B(_1LR(_1ML,_4)))))),_1MR=B(_1o1(function(_1MS){return (!B(_1EW(_1MK,B(_1LP(_1MS)))))?true:false;},_1ME));if(!_1MR._){var _1MT=E(_1MQ);if(!_1MT._){return B(_1jx(_1I1,_1il,_1il,_1MR.a,_1MR.b,_1MR.c,_1MR.d,_1MT.a,_1MT.b,_1MT.c,_1MT.d));}else{return E(_1MR);}}else{return E(_1MQ);}}),_1MU=_1MF;_1Mx=new T(function(){return B(_1Ml(_1MD,_1MK,_1ML));});_1My=_1MM;_1Mz=_1MU;_1MA=_1MI;_1MB=_1MJ.b;return __continue;}}else{return new T2(0,_1MD,_1ME);}})(_1Mx,_1My,_1Mz,_1MA,_1MB));if(_1MC!=__continue){return _1MC;}}},_1MV=new T2(1,_4,_4),_1MW=function(_1MX){var _1MY=E(_1MX);if(!_1MY._){return E(_1MV);}else{var _1MZ=_1MY.b,_1N0=new T(function(){return B(_G(function(_1LO){return new T2(1,_1MY.a,_1LO);},B(_1MW(_1MZ))));},1);return new F(function(){return _0(B(_1MW(_1MZ)),_1N0);});}},_1N1=function(_1N2,_1N3,_1N4,_1N5){var _1N6=new T(function(){return E(_1N4)-1|0;}),_1N7=function(_1N8){var _1N9=E(_1N8);if(!_1N9._){return __Z;}else{var _1Na=_1N9.b,_1Nb=E(_1N9.a),_1Nc=_1Nb.a,_1Nd=function(_1Ne,_1Nf,_1Ng){var _1Nh=E(_1Nb.b);if(!B(_12M(_1Ne,_1Nf,_1Ng,_1Nh.a,_1Nh.b,_1Nh.c))){return new F(function(){return _1N7(_1Na);});}else{if(B(_uU(_1Nc,0))>E(_1N6)){return new F(function(){return _1N7(_1Na);});}else{return new T2(1,_1Nc,new T(function(){return B(_1N7(_1Na));}));}}},_1Ni=E(E(_1N5).b);if(!_1Ni._){var _1Nj=E(_1Ni.a);return new F(function(){return _1Nd(_1Nj.a,_1Nj.b,_1Nj.c);});}else{var _1Nk=E(_1Cg);return new F(function(){return _1Nd(_1Nk.a,_1Nk.b,_1Nk.c);});}}},_1Nl=function(_1Nm){var _1Nn=new T(function(){var _1No=E(_1N5),_1Np=B(_1Mw(_1N2,_1N3,_1No.a,_1No.b,_1Nm));return new T2(0,_1Np.a,_1Np.b);}),_1Nq=new T(function(){return E(E(_1Nn).a);}),_1Nr=new T(function(){var _1Ns=function(_1Nt){var _1Nu=B(_1Ek(_1Nq,E(_1Nt).a));return (_1Nu._==0)?false:(E(_1Nu.a)._==0)?false:true;},_1Nv=E(E(_1Nn).b);if(!_1Nv._){var _1Nw=E(_1N3);if(!_1Nw._){return B(_1o1(_1Ns,B(_1jx(_1I1,_1il,_1il,_1Nv.a,_1Nv.b,_1Nv.c,_1Nv.d,_1Nw.a,_1Nw.b,_1Nw.c,_1Nw.d))));}else{return B(_1o1(_1Ns,_1Nv));}}else{return B(_1o1(_1Ns,_1N3));}});return new T2(0,_1Nq,_1Nr);};return new F(function(){return _1KO(B(_G(_1Nl,B(_1MW(B(_1N7(B(_1LR(_1N2,_4)))))))));});},_1Nx=function(_1Ny,_1Nz){while(1){var _1NA=E(_1Nz);if(!_1NA._){return E(_1Ny);}else{var _1NB=_1NA.a,_1NC=E(_1Ny);if(!_1NC._){var _1ND=E(_1NB);if(!_1ND._){var _1NE=B(_1jx(_1G3,_1il,_1il,_1NC.a,_1NC.b,_1NC.c,_1NC.d,_1ND.a,_1ND.b,_1ND.c,_1ND.d));}else{var _1NE=E(_1NC);}var _1NF=_1NE;}else{var _1NF=E(_1NB);}_1Ny=_1NF;_1Nz=_1NA.b;continue;}}},_1NG=function(_1NH){var _1NI=E(_1NH);if(!_1NI._){return new F(function(){return _1Nx(_ML,B(_G(_1NG,_1NI.c)));});}else{return new F(function(){return _O2(_1NI.a);});}},_1NJ=function(_1NK,_1NL,_1NM){var _1NN=E(_1NM);if(!_1NN._){var _1NO=_1NN.c,_1NP=_1NN.d,_1NQ=E(_1NN.b),_1NR=E(_1NK),_1NS=E(_1NQ.a);switch(B(_12T(_1NR.a,_1NR.b,_1NR.c,_1NS.a,_1NS.b,_1NS.c))){case 0:return new F(function(){return _MQ(_1NQ,B(_1NJ(_1NR,_1NL,_1NO)),_1NP);});break;case 1:switch(B(_1G4(_1NL,_1NQ.b))){case 0:return new F(function(){return _MQ(_1NQ,B(_1NJ(_1NR,_1NL,_1NO)),_1NP);});break;case 1:return new T4(0,_1NN.a,E(new T2(0,_1NR,_1NL)),E(_1NO),E(_1NP));default:return new F(function(){return _Ns(_1NQ,_1NO,B(_1NJ(_1NR,_1NL,_1NP)));});}break;default:return new F(function(){return _Ns(_1NQ,_1NO,B(_1NJ(_1NR,_1NL,_1NP)));});}}else{return new T4(0,1,E(new T2(0,_1NK,_1NL)),E(_ML),E(_ML));}},_1NT=function(_1NU,_1NV){while(1){var _1NW=E(_1NV);if(!_1NW._){return E(_1NU);}else{var _1NX=E(_1NW.a),_1NY=B(_1NJ(_1NX.a,_1NX.b,_1NU));_1NU=_1NY;_1NV=_1NW.b;continue;}}},_1NZ=function(_1O0,_1O1){var _1O2=E(_1O1);if(!_1O2._){return new T3(0,_ML,_4,_4);}else{var _1O3=_1O2.a,_1O4=E(_1O0);if(_1O4==1){var _1O5=E(_1O2.b);if(!_1O5._){return new T3(0,new T(function(){return new T4(0,1,E(_1O3),E(_ML),E(_ML));}),_4,_4);}else{var _1O6=E(_1O3),_1O7=E(_1O5.a),_1O8=_1O7.b,_1O9=E(_1O6.a),_1Oa=E(_1O7.a);switch(B(_12T(_1O9.a,_1O9.b,_1O9.c,_1Oa.a,_1Oa.b,_1Oa.c))){case 0:return new T3(0,new T4(0,1,E(_1O6),E(_ML),E(_ML)),_1O5,_4);case 1:var _1Ob=E(_1O6.b);if(!_1Ob._){var _1Oc=E(_1O8);if(!_1Oc._){var _1Od=E(_1Ob.a),_1Oe=E(_1Oc.a);switch(B(_12T(_1Od.a,_1Od.b,_1Od.c,_1Oe.a,_1Oe.b,_1Oe.c))){case 0:return new T3(0,new T4(0,1,E(_1O6),E(_ML),E(_ML)),_1O5,_4);case 1:return (B(_1bD(_1G3,_1Ob.b,_1Oc.b))==0)?new T3(0,new T4(0,1,E(_1O6),E(_ML),E(_ML)),_1O5,_4):new T3(0,new T4(0,1,E(_1O6),E(_ML),E(_ML)),_4,_1O5);default:return new T3(0,new T4(0,1,E(_1O6),E(_ML),E(_ML)),_4,_1O5);}}else{return new T3(0,new T4(0,1,E(_1O6),E(_ML),E(_ML)),_1O5,_4);}}else{var _1Of=E(_1O8);return new T3(0,new T4(0,1,E(_1O6),E(_ML),E(_ML)),_4,_1O5);}break;default:return new T3(0,new T4(0,1,E(_1O6),E(_ML),E(_ML)),_4,_1O5);}}}else{var _1Og=B(_1NZ(_1O4>>1,_1O2)),_1Oh=_1Og.a,_1Oi=_1Og.c,_1Oj=E(_1Og.b);if(!_1Oj._){return new T3(0,_1Oh,_4,_1Oi);}else{var _1Ok=_1Oj.a,_1Ol=E(_1Oj.b);if(!_1Ol._){return new T3(0,new T(function(){return B(_O8(_1Ok,_1Oh));}),_4,_1Oi);}else{var _1Om=E(_1Ok),_1On=E(_1Ol.a),_1Oo=_1On.b,_1Op=E(_1Om.a),_1Oq=E(_1On.a);switch(B(_12T(_1Op.a,_1Op.b,_1Op.c,_1Oq.a,_1Oq.b,_1Oq.c))){case 0:var _1Or=B(_1NZ(_1O4>>1,_1Ol));return new T3(0,new T(function(){return B(_OM(_1Om,_1Oh,_1Or.a));}),_1Or.b,_1Or.c);case 1:var _1Os=E(_1Om.b);if(!_1Os._){var _1Ot=E(_1Oo);if(!_1Ot._){var _1Ou=E(_1Os.a),_1Ov=E(_1Ot.a);switch(B(_12T(_1Ou.a,_1Ou.b,_1Ou.c,_1Ov.a,_1Ov.b,_1Ov.c))){case 0:var _1Ow=B(_1NZ(_1O4>>1,_1Ol));return new T3(0,new T(function(){return B(_OM(_1Om,_1Oh,_1Ow.a));}),_1Ow.b,_1Ow.c);case 1:if(!B(_1bD(_1G3,_1Os.b,_1Ot.b))){var _1Ox=B(_1NZ(_1O4>>1,_1Ol));return new T3(0,new T(function(){return B(_OM(_1Om,_1Oh,_1Ox.a));}),_1Ox.b,_1Ox.c);}else{return new T3(0,_1Oh,_4,_1Oj);}break;default:return new T3(0,_1Oh,_4,_1Oj);}}else{var _1Oy=B(_1NZ(_1O4>>1,_1Ol));return new T3(0,new T(function(){return B(_OM(_1Om,_1Oh,_1Oy.a));}),_1Oy.b,_1Oy.c);}}else{var _1Oz=E(_1Oo);return new T3(0,_1Oh,_4,_1Oj);}break;default:return new T3(0,_1Oh,_4,_1Oj);}}}}}},_1OA=function(_1OB,_1OC,_1OD){var _1OE=E(_1OD);if(!_1OE._){return E(_1OC);}else{var _1OF=_1OE.a,_1OG=E(_1OE.b);if(!_1OG._){return new F(function(){return _O8(_1OF,_1OC);});}else{var _1OH=E(_1OF),_1OI=E(_1OG.a),_1OJ=_1OI.b,_1OK=E(_1OH.a),_1OL=E(_1OI.a),_1OM=function(_1ON){var _1OO=B(_1NZ(_1OB,_1OG)),_1OP=_1OO.a,_1OQ=E(_1OO.c);if(!_1OQ._){return new F(function(){return _1OA(_1OB<<1,B(_OM(_1OH,_1OC,_1OP)),_1OO.b);});}else{return new F(function(){return _1NT(B(_OM(_1OH,_1OC,_1OP)),_1OQ);});}};switch(B(_12T(_1OK.a,_1OK.b,_1OK.c,_1OL.a,_1OL.b,_1OL.c))){case 0:return new F(function(){return _1OM(_);});break;case 1:var _1OR=E(_1OH.b);if(!_1OR._){var _1OS=E(_1OJ);if(!_1OS._){var _1OT=E(_1OR.a),_1OU=E(_1OS.a);switch(B(_12T(_1OT.a,_1OT.b,_1OT.c,_1OU.a,_1OU.b,_1OU.c))){case 0:return new F(function(){return _1OM(_);});break;case 1:if(!B(_1bD(_1G3,_1OR.b,_1OS.b))){return new F(function(){return _1OM(_);});}else{return new F(function(){return _1NT(_1OC,_1OE);});}break;default:return new F(function(){return _1NT(_1OC,_1OE);});}}else{return new F(function(){return _1OM(_);});}}else{var _1OV=E(_1OJ);return new F(function(){return _1NT(_1OC,_1OE);});}break;default:return new F(function(){return _1NT(_1OC,_1OE);});}}}},_1OW=function(_1OX){var _1OY=E(_1OX);if(!_1OY._){return new T0(1);}else{var _1OZ=_1OY.a,_1P0=E(_1OY.b);if(!_1P0._){return new T4(0,1,E(_1OZ),E(_ML),E(_ML));}else{var _1P1=E(_1OZ),_1P2=E(_1P0.a),_1P3=_1P2.b,_1P4=E(_1P1.a),_1P5=E(_1P2.a);switch(B(_12T(_1P4.a,_1P4.b,_1P4.c,_1P5.a,_1P5.b,_1P5.c))){case 0:return new F(function(){return _1OA(1,new T4(0,1,E(_1P1),E(_ML),E(_ML)),_1P0);});break;case 1:var _1P6=E(_1P1.b);if(!_1P6._){var _1P7=E(_1P3);if(!_1P7._){var _1P8=E(_1P6.a),_1P9=E(_1P7.a);switch(B(_12T(_1P8.a,_1P8.b,_1P8.c,_1P9.a,_1P9.b,_1P9.c))){case 0:return new F(function(){return _1OA(1,new T4(0,1,E(_1P1),E(_ML),E(_ML)),_1P0);});break;case 1:if(!B(_1bD(_1G3,_1P6.b,_1P7.b))){return new F(function(){return _1OA(1,new T4(0,1,E(_1P1),E(_ML),E(_ML)),_1P0);});}else{return new F(function(){return _1NT(new T4(0,1,E(_1P1),E(_ML),E(_ML)),_1P0);});}break;default:return new F(function(){return _1NT(new T4(0,1,E(_1P1),E(_ML),E(_ML)),_1P0);});}}else{return new F(function(){return _1OA(1,new T4(0,1,E(_1P1),E(_ML),E(_ML)),_1P0);});}}else{var _1Pa=E(_1P3);return new F(function(){return _1NT(new T4(0,1,E(_1P1),E(_ML),E(_ML)),_1P0);});}break;default:return new F(function(){return _1NT(new T4(0,1,E(_1P1),E(_ML),E(_ML)),_1P0);});}}}},_1Pb=new T(function(){return B(_7f("Muste/Grammar/Internal.hs:151:43-81|lambda"));}),_1Pc=function(_1Pd,_1Pe){var _1Pf=new T(function(){return E(E(_1Pd).b);}),_1Pg=function(_1Ph){var _1Pi=E(_1Ph);if(!_1Pi._){return __Z;}else{var _1Pj=new T(function(){return B(_1Pg(_1Pi.b));}),_1Pk=function(_1Pl){while(1){var _1Pm=B((function(_1Pn){var _1Po=E(_1Pn);if(!_1Po._){return E(_1Pj);}else{var _1Pp=_1Po.b,_1Pq=E(_1Po.a),_1Pr=E(_1Pq.b);if(!_1Pr._){var _1Ps=E(_1Pr.a),_1Pt=E(_1Pi.a);if(!B(_12M(_1Ps.a,_1Ps.b,_1Ps.c,_1Pt.a,_1Pt.b,_1Pt.c))){_1Pl=_1Pp;return __continue;}else{return new T2(1,_1Pq,new T(function(){return B(_1Pk(_1Pp));}));}}else{return E(_1Pb);}}})(_1Pl));if(_1Pm!=__continue){return _1Pm;}}};return new F(function(){return _1Pk(_1Pf);});}};return new F(function(){return _1OW(B(_1Pg(_1Pe)));});},_1Pu=function(_1Pv,_1Pw,_1Px,_1Py){var _1Pz=function(_1PA,_1PB){while(1){var _1PC=B((function(_1PD,_1PE){var _1PF=E(_1PE);if(!_1PF._){_1PA=new T2(1,new T(function(){return B(_1N1(_1Pw,_1Px,_1Py,_1PF.b));}),new T(function(){return B(_1Pz(_1PD,_1PF.d));}));_1PB=_1PF.c;return __continue;}else{return E(_1PD);}})(_1PA,_1PB));if(_1PC!=__continue){return _1PC;}}};return new F(function(){return _1JT(_ML,B(_1ni(_4,B(_1JO(B(_1Pz(_4,B(_1Pc(_1Pv,B(_1ni(_4,B(_1NG(_1Pw)))))))))))));});},_1PG=function(_1PH,_1PI,_1PJ){var _1PK=E(_1PI);return new F(function(){return _1Pu(_1PH,_1PK.a,_1PK.b,_1PJ);});},_1PL=function(_1PM,_1PN){while(1){var _1PO=B((function(_1PP,_1PQ){var _1PR=E(_1PQ);if(!_1PR._){return __Z;}else{var _1PS=_1PR.a,_1PT=_1PR.b;if(!B(A1(_1PP,_1PS))){var _1PU=_1PP;_1PM=_1PU;_1PN=_1PT;return __continue;}else{return new T2(1,_1PS,new T(function(){return B(_1PL(_1PP,_1PT));}));}}})(_1PM,_1PN));if(_1PO!=__continue){return _1PO;}}},_1PV=function(_1PW,_1PX,_1PY){var _1PZ=new T(function(){return E(_1PY)-1|0;}),_1Q0=function(_1Q1){return B(_uU(E(_1Q1).a,0))<=E(_1PZ);},_1Q2=function(_1Q3,_1Q4){while(1){var _1Q5=B((function(_1Q6,_1Q7){var _1Q8=E(_1Q7);if(!_1Q8._){var _1Q9=_1Q8.d,_1Qa=E(_1Q8.b),_1Qb=new T(function(){if(!B(_1PL(_1Q0,B(_1LR(_1Qa.a,_4))))._){return B(_1Q2(_1Q6,_1Q9));}else{return new T2(1,_1Qa,new T(function(){return B(_1Q2(_1Q6,_1Q9));}));}},1);_1Q3=_1Qb;_1Q4=_1Q8.c;return __continue;}else{return E(_1Q6);}})(_1Q3,_1Q4));if(_1Q5!=__continue){return _1Q5;}}},_1Qc=function(_1Qd){var _1Qe=E(_1Qd);if(!_1Qe._){return new T0(1);}else{var _1Qf=_1Qe.a,_1Qg=B(_1PG(_1PW,_1Qf,_1PY)),_1Qh=B(_1Qc(B(_0(_1Qe.b,new T(function(){var _1Qi=E(_1Qf);return B(_1Q2(_4,B(_1J3(_1Qi.a,_1Qi.b,_1Qg))));},1))))),_1Qj=function(_1Qk,_1Ql,_1Qm,_1Qn){return new F(function(){return _1jx(_1J2,_1il,_1il,1,_1Qf,_ML,_ML,_1Qk,_1Ql,_1Qm,_1Qn);});},_1Qo=E(_1Qg);if(!_1Qo._){var _1Qp=_1Qo.a,_1Qq=_1Qo.b,_1Qr=_1Qo.c,_1Qs=_1Qo.d,_1Qt=E(_1Qh);if(!_1Qt._){var _1Qu=B(_1jx(_1J2,_1il,_1il,_1Qp,_1Qq,_1Qr,_1Qs,_1Qt.a,_1Qt.b,_1Qt.c,_1Qt.d));if(!_1Qu._){return new F(function(){return _1Qj(_1Qu.a,_1Qu.b,_1Qu.c,_1Qu.d);});}else{return new T4(0,1,E(_1Qf),E(_ML),E(_ML));}}else{return new F(function(){return _1Qj(_1Qp,_1Qq,_1Qr,_1Qs);});}}else{var _1Qv=E(_1Qh);if(!_1Qv._){return new F(function(){return _1Qj(_1Qv.a,_1Qv.b,_1Qv.c,_1Qv.d);});}else{return new T4(0,1,E(_1Qf),E(_ML),E(_ML));}}}};return new F(function(){return _1Qc(new T2(1,new T2(0,new T1(1,_1PX),new T4(0,1,E(new T2(0,_4,new T1(1,_1PX))),E(_ML),E(_ML))),_4));});},_1Qw=function(_1Qx){return E(E(_1Qx).a);},_1Qy=function(_1Qz,_1QA,_1QB,_1QC){var _1QD=new T(function(){var _1QE=B(_1Ek(new T(function(){return B(_1Qw(_1QA));}),_1QB));if(!_1QE._){return E(_1Ex);}else{var _1QF=E(_1QE.a);if(!_1QF._){var _1QG=E(_1QF.b);if(!_1QG._){return E(_1QG.a);}else{return E(_1Cg);}}else{return E(_1QF.a);}}});return new F(function(){return _1PV(_1Qz,_1QD,_1QC);});},_1QH=function(_1QI,_1QJ,_1QK,_1QL){while(1){var _1QM=E(_1QJ);if(!_1QM._){return E(_1QL);}else{var _1QN=_1QM.a,_1QO=E(_1QK);if(!_1QO._){return E(_1QL);}else{if(!B(A3(_pM,_1QI,_1QN,_1QO.a))){return E(_1QL);}else{var _1QP=new T2(1,_1QN,_1QL);_1QJ=_1QM.b;_1QK=_1QO.b;_1QL=_1QP;continue;}}}}},_1QQ=function(_1QR,_1QS){while(1){var _1QT=E(_1QR);if(!_1QT._){return E(_1QS);}else{var _1QU=new T2(1,_1QT.a,_1QS);_1QR=_1QT.b;_1QS=_1QU;continue;}}},_1QV=function(_1QW,_1QX,_1QY,_1QZ,_1R0){while(1){var _1R1=B((function(_1R2,_1R3,_1R4,_1R5,_1R6){var _1R7=E(_1R3);if(!_1R7._){return new T2(0,_1R5,_1R6);}else{var _1R8=_1R7.a,_1R9=_1R7.b,_1Ra=E(_1R4);if(!_1Ra._){return new T2(0,_1R5,_1R6);}else{var _1Rb=_1Ra.b;if(!B(A3(_pM,_1R2,_1R8,_1Ra.a))){var _1Rc=new T(function(){return B(_1QH(_1R2,B(_1QQ(_1R7,_4)),new T(function(){return B(_1QQ(_1Ra,_4));},1),_4));}),_1Rd=_1R2,_1Re=_1R5;_1QW=_1Rd;_1QX=_1R9;_1QY=_1Rb;_1QZ=_1Re;_1R0=_1Rc;return __continue;}else{var _1Rd=_1R2,_1Rf=_1R6;_1QW=_1Rd;_1QX=_1R9;_1QY=_1Rb;_1QZ=new T(function(){return B(_0(_1R5,new T2(1,_1R8,_4)));});_1R0=_1Rf;return __continue;}}}})(_1QW,_1QX,_1QY,_1QZ,_1R0));if(_1R1!=__continue){return _1R1;}}},_1Rg=function(_1Rh,_1Ri,_1Rj,_1Rk){return (!B(_1EW(_1Rh,_1Rj)))?true:(!B(_sf(_1Ri,_1Rk)))?true:false;},_1Rl=function(_1Rm,_1Rn){var _1Ro=E(_1Rm),_1Rp=E(_1Rn);return new F(function(){return _1Rg(_1Ro.a,_1Ro.b,_1Rp.a,_1Rp.b);});},_1Rq=function(_1Rr,_1Rs,_1Rt,_1Ru){if(!B(_1EW(_1Rr,_1Rt))){return false;}else{return new F(function(){return _sf(_1Rs,_1Ru);});}},_1Rv=function(_1Rw,_1Rx){var _1Ry=E(_1Rw),_1Rz=E(_1Rx);return new F(function(){return _1Rq(_1Ry.a,_1Ry.b,_1Rz.a,_1Rz.b);});},_1RA=new T2(0,_1Rv,_1Rl),_1RB=function(_1RC,_1RD,_1RE,_1RF){switch(B(_1GW(_1RC,_1RE))){case 0:return false;case 1:return new F(function(){return _12t(_1RD,_1RF);});break;default:return true;}},_1RG=function(_1RH,_1RI){var _1RJ=E(_1RH),_1RK=E(_1RI);return new F(function(){return _1RB(_1RJ.a,_1RJ.b,_1RK.a,_1RK.b);});},_1RL=function(_1RM,_1RN){var _1RO=E(_1RM),_1RP=E(_1RN);switch(B(_1GW(_1RO.a,_1RP.a))){case 0:return E(_1RP);case 1:return (B(_12d(_1RO.b,_1RP.b))==2)?E(_1RO):E(_1RP);default:return E(_1RO);}},_1RQ=function(_1RR,_1RS){var _1RT=E(_1RR),_1RU=E(_1RS);switch(B(_1GW(_1RT.a,_1RU.a))){case 0:return E(_1RT);case 1:return (B(_12d(_1RT.b,_1RU.b))==2)?E(_1RU):E(_1RT);default:return E(_1RU);}},_1RV=function(_1RW,_1RX,_1RY,_1RZ){switch(B(_1GW(_1RW,_1RY))){case 0:return 0;case 1:return new F(function(){return _12d(_1RX,_1RZ);});break;default:return 2;}},_1S0=function(_1S1,_1S2){var _1S3=E(_1S1),_1S4=E(_1S2);return new F(function(){return _1RV(_1S3.a,_1S3.b,_1S4.a,_1S4.b);});},_1S5=function(_1S6,_1S7,_1S8,_1S9){switch(B(_1GW(_1S6,_1S8))){case 0:return true;case 1:return new F(function(){return _12k(_1S7,_1S9);});break;default:return false;}},_1Sa=function(_1Sb,_1Sc){var _1Sd=E(_1Sb),_1Se=E(_1Sc);return new F(function(){return _1S5(_1Sd.a,_1Sd.b,_1Se.a,_1Se.b);});},_1Sf=function(_1Sg,_1Sh,_1Si,_1Sj){switch(B(_1GW(_1Sg,_1Si))){case 0:return true;case 1:return new F(function(){return _12n(_1Sh,_1Sj);});break;default:return false;}},_1Sk=function(_1Sl,_1Sm){var _1Sn=E(_1Sl),_1So=E(_1Sm);return new F(function(){return _1Sf(_1Sn.a,_1Sn.b,_1So.a,_1So.b);});},_1Sp=function(_1Sq,_1Sr,_1Ss,_1St){switch(B(_1GW(_1Sq,_1Ss))){case 0:return false;case 1:return new F(function(){return _12q(_1Sr,_1St);});break;default:return true;}},_1Su=function(_1Sv,_1Sw){var _1Sx=E(_1Sv),_1Sy=E(_1Sw);return new F(function(){return _1Sp(_1Sx.a,_1Sx.b,_1Sy.a,_1Sy.b);});},_1Sz={_:0,a:_1RA,b:_1S0,c:_1Sa,d:_1Sk,e:_1Su,f:_1RG,g:_1RL,h:_1RQ},_1SA=function(_1SB){var _1SC=E(_1SB);if(!_1SC._){return __Z;}else{return new F(function(){return _0(_1SC.a,new T(function(){return B(_1SA(_1SC.b));},1));});}},_1SD=new T1(1,_4),_1SE=function(_1SF){var _1SG=E(_1SF);if(!_1SG._){return E(_1SD);}else{var _1SH=E(_1SG.a);if(!_1SH._){return __Z;}else{var _1SI=B(_1SE(_1SG.b));return (_1SI._==0)?__Z:new T1(1,new T2(1,_1SH.a,_1SI.a));}}},_1SJ=function(_1SK,_1SL){var _1SM=B(_1SE(_1SL));return (_1SM._==0)?new T2(0,_4l,_4l):new T2(0,_1SK,new T1(1,new T(function(){return B(_1SA(_1SM.a));})));},_1SN=function(_1SO,_1SP){var _1SQ=E(_1SO);if(!_1SQ._){return new T2(0,_1SP,_4);}else{var _1SR=new T(function(){var _1SS=B(_1SN(_1SQ.b,_1SP));return new T2(0,_1SS.a,_1SS.b);}),_1ST=new T(function(){var _1SU=B(_1SV(new T(function(){return E(E(_1SR).a);}),_1SQ.a));return new T2(0,_1SU.a,_1SU.b);});return new T2(0,new T(function(){return E(E(_1ST).a);}),new T2(1,new T(function(){return E(E(_1ST).b);}),new T(function(){return E(E(_1SR).b);})));}},_1SW=function(_1SX,_1SY){var _1SZ=E(_1SX);if(!_1SZ._){return new T2(0,_1SY,_4);}else{var _1T0=new T(function(){var _1T1=B(_1SW(_1SZ.b,_1SY));return new T2(0,_1T1.a,_1T1.b);}),_1T2=new T(function(){var _1T3=B(_1SV(new T(function(){return E(E(_1T0).a);}),_1SZ.a));return new T2(0,_1T3.a,_1T3.b);});return new T2(0,new T(function(){return E(E(_1T2).a);}),new T2(1,new T(function(){return E(E(_1T2).b);}),new T(function(){return E(E(_1T0).b);})));}},_1T4=function(_1T5,_1T6){var _1T7=E(_1T5);if(!_1T7._){return new T2(0,_1T6,_4);}else{var _1T8=new T(function(){var _1T9=B(_1T4(_1T7.b,_1T6));return new T2(0,_1T9.a,_1T9.b);}),_1Ta=new T(function(){var _1Tb=B(_1SV(new T(function(){return E(E(_1T8).a);}),_1T7.a));return new T2(0,_1Tb.a,_1Tb.b);});return new T2(0,new T(function(){return E(E(_1Ta).a);}),new T2(1,new T(function(){return E(E(_1Ta).b);}),new T(function(){return E(E(_1T8).b);})));}},_1Tc=function(_1Td,_1Te){var _1Tf=E(_1Td);if(!_1Tf._){return new T2(0,_1Te,_4);}else{var _1Tg=new T(function(){var _1Th=B(_1Tc(_1Tf.b,_1Te));return new T2(0,_1Th.a,_1Th.b);}),_1Ti=new T(function(){var _1Tj=B(_1SV(new T(function(){return E(E(_1Tg).a);}),_1Tf.a));return new T2(0,_1Tj.a,_1Tj.b);});return new T2(0,new T(function(){return E(E(_1Ti).a);}),new T2(1,new T(function(){return E(E(_1Ti).b);}),new T(function(){return E(E(_1Tg).b);})));}},_1Tk=function(_1Tl){var _1Tm=E(_1Tl);if(!_1Tm._){return __Z;}else{return new F(function(){return _0(_1Tm.a,new T(function(){return B(_1Tk(_1Tm.b));},1));});}},_1Tn=function(_1To){var _1Tp=E(_1To);if(!_1Tp._){return E(_1SD);}else{var _1Tq=E(_1Tp.a);if(!_1Tq._){return __Z;}else{var _1Tr=B(_1Tn(_1Tp.b));return (_1Tr._==0)?__Z:new T1(1,new T2(1,_1Tq.a,_1Tr.a));}}},_1Ts=function(_1Tt,_1Tu,_1Tv){while(1){var _1Tw=E(_1Tu);if(!_1Tw._){return true;}else{var _1Tx=E(_1Tv);if(!_1Tx._){return false;}else{if(!B(A3(_pM,_1Tt,_1Tw.a,_1Tx.a))){return false;}else{_1Tu=_1Tw.b;_1Tv=_1Tx.b;continue;}}}}},_1Ty=new T1(1,_4),_1Tz=new T(function(){return B(_7f("pgf/PGF/Macros.hs:(186,5)-(204,44)|function untokn"));}),_1SV=function(_1TA,_1TB){var _1TC=E(_1TB);switch(_1TC._){case 0:var _1TD=B(_1Tc(_1TC.f,_1TA)),_1TE=B(_1Tn(_1TD.b));return (_1TE._==0)?new T2(0,_4l,_4l):new T2(0,_1TD.a,new T1(1,new T2(1,new T6(1,_1TC.a,_1TC.b,_1TC.c,_1TC.d,_1TC.e,new T(function(){return B(_1Tk(_1TE.a));})),_4)));case 1:var _1TF=E(_1TC.a);return (_1TF._==0)?new T2(0,_1TA,_1Ty):new T2(0,new T1(1,_1TF),new T1(1,new T2(1,new T1(0,_1TF),_4)));case 2:return new T2(0,_4l,_4l);case 6:var _1TG=_1TC.a,_1TH=E(_1TA);if(!_1TH._){var _1TI=B(_1T4(_1TG,_4l));return new F(function(){return _1SJ(_1TI.a,_1TI.b);});}else{var _1TJ=function(_1TK){while(1){var _1TL=E(_1TK);if(!_1TL._){return false;}else{if(!B(_1Ts(_sq,_1TL.a,_1TH.a))){_1TK=_1TL.b;continue;}else{return true;}}}},_1TM=function(_1TN){while(1){var _1TO=B((function(_1TP){var _1TQ=E(_1TP);if(!_1TQ._){return __Z;}else{var _1TR=_1TQ.b,_1TS=E(_1TQ.a);if(!B(_1TJ(_1TS.b))){_1TN=_1TR;return __continue;}else{return new T2(1,_1TS.a,new T(function(){return B(_1TM(_1TR));}));}}})(_1TN));if(_1TO!=__continue){return _1TO;}}},_1TT=B(_1TM(_1TC.b));if(!_1TT._){var _1TU=B(_1SW(_1TG,_1TH));return new F(function(){return _1SJ(_1TU.a,_1TU.b);});}else{var _1TV=B(_1SN(_1TT.a,_1TH));return new F(function(){return _1SJ(_1TV.a,_1TV.b);});}}break;default:return E(_1Tz);}},_1TW=function(_1TX,_1TY){var _1TZ=E(_1TX);if(!_1TZ._){return new T2(0,_1TY,_4);}else{var _1U0=new T(function(){var _1U1=B(_1TW(_1TZ.b,_1TY));return new T2(0,_1U1.a,_1U1.b);}),_1U2=new T(function(){var _1U3=B(_1SV(new T(function(){return E(E(_1U0).a);}),_1TZ.a));return new T2(0,_1U3.a,_1U3.b);});return new T2(0,new T(function(){return E(E(_1U2).a);}),new T2(1,new T(function(){return E(E(_1U2).b);}),new T(function(){return E(E(_1U0).b);})));}},_1U4=function(_1U5){var _1U6=E(_1U5);if(_1U6==95){return true;}else{var _1U7=function(_1U8){if(_1U6<65){if(_1U6<192){return false;}else{if(_1U6>255){return false;}else{switch(E(_1U6)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1U6>90){if(_1U6<192){return false;}else{if(_1U6>255){return false;}else{switch(E(_1U6)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1U6<97){return new F(function(){return _1U7(_);});}else{if(_1U6>122){return new F(function(){return _1U7(_);});}else{return true;}}}},_1U9=new T(function(){return B(unCStr("UTF8.decodeUTF8: bad data"));}),_1Ua=function(_1Ub){return new F(function(){return err(_1U9);});},_1Uc=new T(function(){return B(_1Ua(_));}),_1Ud=function(_1Ue){var _1Uf=E(_1Ue);if(!_1Uf._){return __Z;}else{var _1Ug=_1Uf.b,_1Uh=E(_1Uf.a);if(_1Uh>=128){var _1Ui=E(_1Ug);if(!_1Ui._){return E(_1Uc);}else{var _1Uj=_1Ui.a,_1Uk=_1Ui.b,_1Ul=function(_1Um){var _1Un=E(_1Uk);if(!_1Un._){return E(_1Uc);}else{if(224>_1Uh){return E(_1Uc);}else{if(_1Uh>239){return E(_1Uc);}else{var _1Uo=E(_1Uj);if(128>_1Uo){return E(_1Uc);}else{if(_1Uo>191){return E(_1Uc);}else{var _1Up=E(_1Un.a);return (128>_1Up)?E(_1Uc):(_1Up>191)?E(_1Uc):new T2(1,new T(function(){var _1Uq=((imul(B(_o6(_1Uh,16)),4096)|0)+(imul(B(_o6(_1Uo,64)),64)|0)|0)+B(_o6(_1Up,64))|0;if(_1Uq>>>0>1114111){return B(_fK(_1Uq));}else{return _1Uq;}}),new T(function(){return B(_1Ud(_1Un.b));}));}}}}}};if(192>_1Uh){return new F(function(){return _1Ul(_);});}else{if(_1Uh>223){return new F(function(){return _1Ul(_);});}else{var _1Ur=E(_1Uj);if(128>_1Ur){return new F(function(){return _1Ul(_);});}else{if(_1Ur>191){return new F(function(){return _1Ul(_);});}else{return new T2(1,new T(function(){var _1Us=(imul(B(_o6(_1Uh,32)),64)|0)+B(_o6(_1Ur,64))|0;if(_1Us>>>0>1114111){return B(_fK(_1Us));}else{return _1Us;}}),new T(function(){return B(_1Ud(_1Uk));}));}}}}}}else{return new T2(1,_1Uh,new T(function(){return B(_1Ud(_1Ug));}));}}},_1Ut=function(_1Uu){var _1Uv=E(_1Uu);switch(_1Uv){case 39:return true;case 95:return true;default:var _1Uw=function(_1Ux){var _1Uy=function(_1Uz){if(_1Uv<65){if(_1Uv<192){return false;}else{if(_1Uv>255){return false;}else{switch(E(_1Uv)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1Uv>90){if(_1Uv<192){return false;}else{if(_1Uv>255){return false;}else{switch(E(_1Uv)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1Uv<97){return new F(function(){return _1Uy(_);});}else{if(_1Uv>122){return new F(function(){return _1Uy(_);});}else{return true;}}};if(_1Uv<48){return new F(function(){return _1Uw(_);});}else{if(_1Uv>57){return new F(function(){return _1Uw(_);});}else{return true;}}}},_1UA=function(_1UB){while(1){var _1UC=E(_1UB);if(!_1UC._){return true;}else{if(!B(_1Ut(E(_1UC.a)))){return false;}else{_1UB=_1UC.b;continue;}}}},_1UD=new T(function(){return B(unCStr("\\\\"));}),_1UE=new T(function(){return B(unCStr("\\\'"));}),_1UF=new T(function(){return B(unCStr("\'"));}),_1UG=function(_1UH){var _1UI=E(_1UH);if(!_1UI._){return E(_1UF);}else{var _1UJ=_1UI.b,_1UK=E(_1UI.a);switch(E(_1UK)){case 39:return new F(function(){return _0(_1UE,new T(function(){return B(_1UG(_1UJ));},1));});break;case 92:return new F(function(){return _0(_1UD,new T(function(){return B(_1UG(_1UJ));},1));});break;default:return new T2(1,_1UK,new T(function(){return B(_1UG(_1UJ));}));}}},_1UL=function(_1UM){var _1UN=E(_1UM);return (_1UN._==0)?__Z:new T2(1,new T(function(){return B(_12D(_1UN.a));}),new T(function(){return B(_1UL(_1UN.b));}));},_1UO=function(_1UP,_1UQ,_1UR){var _1US=B(_1Ud(B(_1UL(new T(function(){return B(_IJ(_1UP,_1UQ,_1UR));})))));if(!_1US._){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1UG(_4));}));});}else{if(!B(_1U4(E(_1US.a)))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1UG(_1US));}));});}else{if(!B(_1UA(_1US.b))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1UG(_1US));}));});}else{return E(_1US);}}}},_1UT=new T(function(){return B(unCStr(")"));}),_1UU=function(_1UV,_1UW){var _1UX=new T(function(){var _1UY=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_1UW,_4)),_1UT));})));},1);return B(_0(B(_bZ(0,_1UV,_4)),_1UY));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1UX)));});},_1UZ=new T(function(){return B(unCStr("Int"));}),_1V0=function(_1V1,_1V2,_1V3){return new F(function(){return _eR(_e4,new T2(0,_1V2,_1V3),_1V1,_1UZ);});},_1V4=new T(function(){return B(unCStr("&|"));}),_1V5=new T1(1,_1V4),_1V6=new T2(1,_1V5,_4),_1V7=new T0(2),_1V8=new T2(1,_1V7,_4),_1V9=new T(function(){return B(unCStr("&+"));}),_1Va=new T1(1,_1V9),_1Vb=new T2(1,_1Va,_4),_1Vc=function(_1Vd,_1Ve,_1Vf){var _1Vg=function(_1Vh,_1Vi){var _1Vj=B(_1Eb(_1Vf,_1Vh)),_1Vk=E(_1Vj.a),_1Vl=E(E(_1Vj.e).b),_1Vm=_1Vl.c,_1Vn=E(_1Vl.a),_1Vo=E(_1Vl.b);if(_1Vn>_1Vi){return new F(function(){return _1V0(_1Vi,_1Vn,_1Vo);});}else{if(_1Vi>_1Vo){return new F(function(){return _1V0(_1Vi,_1Vn,_1Vo);});}else{var _1Vp=_1Vi-_1Vn|0;if(0>_1Vp){return new F(function(){return _1UU(_1Vp,_1Vm);});}else{if(_1Vp>=_1Vm){return new F(function(){return _1UU(_1Vp,_1Vm);});}else{var _1Vq=E(_1Vl.d[_1Vp]);return (_1Vq._==0)?__Z:(!B(A1(_1Vd,_1Vk)))?E(_1Vq):new T2(1,new T(function(){return new T6(0,_1Vk.a,E(_1Vk.b),_1Vi,_1Vj.c,_1Vj.d,_1Vq);}),_4);}}}}},_1Vr=function(_1Vs){var _1Vt=E(_1Vs);if(!_1Vt._){return __Z;}else{var _1Vu=E(_1Vt.a);return new T2(1,new T2(0,new T(function(){return B(_1Vv(_1Vu.a));}),_1Vu.b),new T(function(){return B(_1Vr(_1Vt.b));}));}},_1Vw=function(_1Vx){var _1Vy=E(_1Vx);if(!_1Vy._){return __Z;}else{return new F(function(){return _0(B(_1Vz(_1Vy.a)),new T(function(){return B(_1Vw(_1Vy.b));},1));});}},_1Vz=function(_1VA){var _1VB=E(_1VA);switch(_1VB._){case 0:return new F(function(){return _1Vg(_1VB.a,_1VB.b);});break;case 1:return new F(function(){return _1Vg(_1VB.a,_1VB.b);});break;case 2:return new T2(1,new T1(1,new T(function(){var _1VC=B(_1Eb(E(B(_1Eb(_1Vf,_1VB.a)).e).a,_1VB.b));return B(_1UO(_1VC.a,_1VC.b,_1VC.c));})),_4);case 3:return new T2(1,new T1(1,_1VB.a),_4);case 4:return new T2(1,new T2(6,new T(function(){return B(_1Vw(_1VB.a));}),new T(function(){return B(_1Vr(_1VB.b));})),_4);case 5:return E(_1Vb);case 6:return E(_1V8);case 7:return __Z;case 8:return __Z;case 9:return E(_1V6);default:return E(_1V6);}},_1Vv=function(_1VD){var _1VE=E(_1VD);if(!_1VE._){return __Z;}else{return new F(function(){return _0(B(_1Vz(_1VE.a)),new T(function(){return B(_1Vv(_1VE.b));},1));});}},_1VF=function(_1VG){var _1VH=E(_1VG);if(!_1VH._){return __Z;}else{return new F(function(){return _0(B(_1Vz(_1VH.a)),new T(function(){return B(_1VF(_1VH.b));},1));});}};return new F(function(){return _1VF(_1Ve);});},_1VI=function(_1VJ,_1VK,_1VL){return new F(function(){return _eR(_e4,new T2(0,_1VK,_1VL),_1VJ,_1UZ);});},_1VM=new T(function(){return B(unCStr("Negative range size"));}),_1VN=function(_1VO,_1VP,_1VQ,_1VR,_1VS){var _1VT=new T(function(){var _1VU=function(_){var _1VV=E(_1VO),_1VW=E(_1VV.c),_1VX=_1VW.c,_1VY=E(_1VW.a),_1VZ=E(_1VW.b),_1W0=E(_1VR);if(_1VY>_1W0){return new F(function(){return _1VI(_1W0,_1VY,_1VZ);});}else{if(_1W0>_1VZ){return new F(function(){return _1VI(_1W0,_1VY,_1VZ);});}else{var _1W1=_1W0-_1VY|0;if(0>_1W1){return new F(function(){return _1UU(_1W1,_1VX);});}else{if(_1W1>=_1VX){return new F(function(){return _1UU(_1W1,_1VX);});}else{var _1W2=E(_1VW.d[_1W1]),_1W3=E(_1W2.b),_1W4=E(_1W2.c),_1W5=function(_1W6){if(_1W6>=0){var _1W7=newArr(_1W6,_Vu),_1W8=_1W7,_1W9=function(_1Wa){var _1Wb=function(_1Wc,_1Wd,_){while(1){if(_1Wc!=_1Wa){var _1We=E(_1Wd);if(!_1We._){return _5;}else{var _=_1W8[_1Wc]=_1We.a,_1Wf=_1Wc+1|0;_1Wc=_1Wf;_1Wd=_1We.b;continue;}}else{return _5;}}},_1Wg=new T(function(){var _1Wh=_1W2.d-1|0;if(0<=_1Wh){var _1Wi=new T(function(){return B(_1Vc(_1VP,_4,_1VS));}),_1Wj=function(_1Wk){var _1Wl=new T(function(){var _1Wm=E(_1VV.f),_1Wn=_1Wm.c,_1Wo=E(_1Wm.a),_1Wp=E(_1Wm.b),_1Wq=_1W2.e["v"]["i32"][_1Wk];if(_1Wo>_1Wq){return B(_1V0(_1Wq,_1Wo,_1Wp));}else{if(_1Wq>_1Wp){return B(_1V0(_1Wq,_1Wo,_1Wp));}else{var _1Wr=_1Wq-_1Wo|0;if(0>_1Wr){return B(_1UU(_1Wr,_1Wn));}else{if(_1Wr>=_1Wn){return B(_1UU(_1Wr,_1Wn));}else{var _1Ws=E(_1Wm.d[_1Wr]),_1Wt=_1Ws.c-1|0;if(0<=_1Wt){var _1Wu=function(_1Wv){return new T2(1,new T(function(){return E(_1Ws.d[_1Wv]);}),new T(function(){if(_1Wv!=_1Wt){return B(_1Wu(_1Wv+1|0));}else{return __Z;}}));};return B(_1Vc(_1VP,B(_1Wu(0)),_1VS));}else{return E(_1Wi);}}}}}});return new T2(1,_1Wl,new T(function(){if(_1Wk!=_1Wh){return B(_1Wj(_1Wk+1|0));}else{return __Z;}}));};return B(_1Wj(0));}else{return __Z;}},1),_1Ww=B(_1Wb(0,_1Wg,_));return new T4(0,E(_1W3),E(_1W4),_1W6,_1W8);};if(_1W3>_1W4){return new F(function(){return _1W9(0);});}else{var _1Wx=(_1W4-_1W3|0)+1|0;if(_1Wx>=0){return new F(function(){return _1W9(_1Wx);});}else{return new F(function(){return err(_1VM);});}}}else{return E(_Vw);}};if(_1W3>_1W4){return new F(function(){return _1W5(0);});}else{return new F(function(){return _1W5((_1W4-_1W3|0)+1|0);});}}}}}};return B(_8O(_1VU));});return new T2(0,_1VQ,_1VT);},_1Wy=new T(function(){return B(unCStr(")"));}),_1Wz=function(_1WA,_1WB){var _1WC=new T(function(){var _1WD=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_1WB,_4)),_1Wy));})));},1);return B(_0(B(_bZ(0,_1WA,_4)),_1WD));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1WC)));});},_1WE=function(_1WF){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_1WF));}))));});},_1WG=new T(function(){return B(_1WE("ww_sZJc Map CId String"));}),_1WH=new T(function(){return B(_1WE("ww_sZJb Map CId Literal"));}),_1WI=new T1(1,_4),_1WJ=new T2(1,_1WI,_4),_1WK=0,_1WL=new T(function(){return B(unCStr("Int"));}),_1WM=function(_1WN,_1WO){return new F(function(){return _eR(_e4,new T2(0,_1WN,_1WO),_1WK,_1WL);});},_1WP=function(_1WQ){return true;},_1WR=new T(function(){return B(_1WE("ww_sZJl IntMap (IntMap (TrieMap Token IntSet))"));}),_1WS=new T(function(){return B(_1WE("ww_sZJk Map CId CncCat"));}),_1WT=new T(function(){return B(_1WE("ww_sZJj Map CId (IntMap (Set Production))"));}),_1WU=new T(function(){return B(_1WE("ww_sZJi IntMap (Set Production)"));}),_1WV=new T(function(){return B(_1WE("ww_sZJh IntMap (Set Production)"));}),_1WW=new T(function(){return B(_1WE("ww_sZJe IntMap [FunId]"));}),_1WX=function(_1WY,_1WZ,_1X0,_1X1,_1X2,_1X3,_1X4,_1X5){var _1X6=B(_14V(_1X2,_1WZ));if(!_1X6._){return E(_1WJ);}else{var _1X7=E(_1X6.a);if(!_1X7._){return E(_1WJ);}else{var _1X8=E(B(_1VN({_:0,a:_1WH,b:_1WG,c:_1WY,d:_1WW,e:_1WZ,f:_1X0,g:_1WV,h:_1WU,i:_1WT,j:_1WS,k:_1WR,l:0},_1WP,_4,_1X7.a,new T2(1,new T5(0,E(_1X1),_1X2,_1X3,_1X4,E(_1X5)),_4))).b),_1X9=_1X8.c,_1Xa=E(_1X8.a),_1Xb=E(_1X8.b);if(_1Xa>0){return new F(function(){return _1WM(_1Xa,_1Xb);});}else{if(0>_1Xb){return new F(function(){return _1WM(_1Xa,_1Xb);});}else{var _1Xc= -_1Xa|0;if(0>_1Xc){return new F(function(){return _1Wz(_1Xc,_1X9);});}else{if(_1Xc>=_1X9){return new F(function(){return _1Wz(_1Xc,_1X9);});}else{return E(_1X8.d[_1Xc]);}}}}}}},_1Xd=new T(function(){return B(unCStr("no lang"));}),_1Xe=new T(function(){return B(err(_1Xd));}),_1Xf=function(_1Xg){return E(E(_1Xg).d);},_1Xh=function(_1Xi,_1Xj,_1Xk,_1Xl){var _1Xm=function(_1Xn,_1Xo,_1Xp){while(1){var _1Xq=E(_1Xo),_1Xr=E(_1Xp);if(!_1Xr._){switch(B(A3(_13n,_1Xi,_1Xq,_1Xr.b))){case 0:_1Xo=_1Xq;_1Xp=_1Xr.d;continue;case 1:return E(_1Xr.c);default:_1Xo=_1Xq;_1Xp=_1Xr.e;continue;}}else{return E(_1Xn);}}};return new F(function(){return _1Xm(_1Xj,_1Xk,_1Xl);});},_1Xs=function(_1Xt){var _1Xu=function(_){var _1Xv=newArr(1,_Vu),_1Xw=_1Xv,_1Xx=function(_1Xy,_1Xz,_){while(1){var _1XA=E(_1Xy);if(_1XA==1){return _5;}else{var _1XB=E(_1Xz);if(!_1XB._){return _5;}else{var _=_1Xw[_1XA]=_1XB.a;_1Xy=_1XA+1|0;_1Xz=_1XB.b;continue;}}}},_1XC=B(_1Xx(0,new T2(1,new T2(1,new T1(1,_1Xt),_4),_4),_));return new T4(0,E(_1WK),E(_1WK),1,_1Xw);};return new F(function(){return _8O(_1Xu);});},_1XD=function(_1XE,_1XF,_1XG,_1XH){while(1){var _1XI=E(_1XH);if(!_1XI._){var _1XJ=E(_1XI.b);switch(B(_12T(_1XE,_1XF,_1XG,_1XJ.a,_1XJ.b,_1XJ.c))){case 0:_1XH=_1XI.d;continue;case 1:return new T1(1,_1XI.c);default:_1XH=_1XI.e;continue;}}else{return __Z;}}},_1XK=new T(function(){return B(unCStr("Float"));}),_1XL=new T(function(){return B(_1za(_1XK));}),_1XM=new T(function(){return B(_G(_1z8,_1XL));}),_1XN=new T(function(){var _1XO=B(_1xU(_1XM));return new T3(0,_1XO.a,_1XO.b,_1XO.c);}),_1XP=new T(function(){return B(_1za(_1UZ));}),_1XQ=new T(function(){return B(_G(_1z8,_1XP));}),_1XR=new T(function(){var _1XS=B(_1xU(_1XQ));return new T3(0,_1XS.a,_1XS.b,_1XS.c);}),_1XT=new T(function(){return B(unCStr("String"));}),_1XU=new T(function(){return B(_1za(_1XT));}),_1XV=new T(function(){return B(_G(_1z8,_1XU));}),_1XW=new T(function(){var _1XX=B(_1xU(_1XV));return new T3(0,_1XX.a,_1XX.b,_1XX.c);}),_1XY=function(_1XZ){var _1Y0=E(_1XZ);return (_1Y0._==0)?__Z:new T2(1,E(_1Y0.a).b,new T(function(){return B(_1XY(_1Y0.b));}));},_1Y1=function(_1Y2){var _1Y3=E(_1Y2);return (_1Y3._==0)?__Z:new T2(1,new T(function(){return E(E(E(_1Y3.a).c).b);}),new T(function(){return B(_1Y1(_1Y3.b));}));},_1Y4=new T(function(){return B(_7f("pgf/PGF/Linearize.hs:(77,5)-(87,137)|function lin"));}),_1Y5=63,_1Y6=new T(function(){return B(_1Mb("pgf/PGF/Linearize.hs:105:19-70|Just (ty, _, _, _)"));}),_1Y7=new T(function(){return B(_7f("pgf/PGF/Linearize.hs:(104,13)-(109,85)|function toApp"));}),_1Y8=new T(function(){return B(unCStr("]"));}),_1Y9=function(_1Ya,_1Yb,_1Yc,_1Yd){if(!B(_18O(_1Ye,_1Ya,_1Yc))){return false;}else{return new F(function(){return _1aJ(_1Yb,_1Yd);});}},_1Yf=function(_1Yg,_1Yh){var _1Yi=E(_1Yg),_1Yj=E(_1Yh);return new F(function(){return _1Y9(_1Yi.a,_1Yi.b,_1Yj.a,_1Yj.b);});},_1Yk=function(_1Yl,_1Ym,_1Yn,_1Yo){return (!B(_18O(_1Ye,_1Yl,_1Yn)))?true:(!B(_1aJ(_1Ym,_1Yo)))?true:false;},_1Yp=function(_1Yq,_1Yr){var _1Ys=E(_1Yq),_1Yt=E(_1Yr);return new F(function(){return _1Yk(_1Ys.a,_1Ys.b,_1Yt.a,_1Yt.b);});},_1Yu=new T(function(){return new T2(0,_1Yf,_1Yp);}),_1Yv=function(_1Yw,_1Yx){var _1Yy=E(_1Yw);switch(_1Yy._){case 0:var _1Yz=E(_1Yx);if(!_1Yz._){var _1YA=E(_1Yy.a),_1YB=E(_1Yz.a);if(!B(_12M(_1YA.a,_1YA.b,_1YA.c,_1YB.a,_1YB.b,_1YB.c))){return false;}else{if(_1Yy.b!=_1Yz.b){return false;}else{if(_1Yy.c!=_1Yz.c){return false;}else{var _1YC=E(_1Yy.d),_1YD=E(_1Yz.d);if(!B(_12M(_1YC.a,_1YC.b,_1YC.c,_1YD.a,_1YD.b,_1YD.c))){return false;}else{if(!B(_18O(_18Y,_1Yy.e,_1Yz.e))){return false;}else{return new F(function(){return _18O(_1Ye,_1Yy.f,_1Yz.f);});}}}}}}else{return false;}break;case 1:var _1YE=E(_1Yx);if(_1YE._==1){return new F(function(){return _sf(_1Yy.a,_1YE.a);});}else{return false;}break;case 2:return (E(_1Yx)._==2)?true:false;case 3:return (E(_1Yx)._==3)?true:false;case 4:return (E(_1Yx)._==4)?true:false;case 5:return (E(_1Yx)._==5)?true:false;default:var _1YF=E(_1Yx);if(_1YF._==6){if(!B(_18O(_1Ye,_1Yy.a,_1YF.a))){return false;}else{return new F(function(){return _18O(_1Yu,_1Yy.b,_1YF.b);});}}else{return false;}}},_1YG=function(_1YH,_1YI){return (!B(_1Yv(_1YH,_1YI)))?true:false;},_1Ye=new T(function(){return new T2(0,_1Yv,_1YG);}),_1YJ=function(_1YK,_1YL){var _1YM=E(_1YK),_1YN=E(_1YL),_1YO=E(_1YM.c);if(!_1YO){return (E(_1YN.c)==0)?true:false;}else{if(E(_1YM.a)!=E(_1YN.a)){return false;}else{if(E(_1YM.b)!=E(_1YN.b)){return false;}else{var _1YP=_1YO-1|0;if(0<=_1YP){var _1YQ=function(_1YR){while(1){if(!B(_18O(_1Ye,_1YM.d[_1YR],_1YN.d[_1YR]))){return false;}else{if(_1YR!=_1YP){var _1YS=_1YR+1|0;_1YR=_1YS;continue;}else{return true;}}}};return new F(function(){return _1YQ(0);});}else{return true;}}}}},_1YT=function(_1YU,_1YV){var _1YW=E(_1YU),_1YX=E(_1YV),_1YY=E(_1YW.a),_1YZ=E(_1YX.a),_1Z0=E(_1YY.a),_1Z1=E(_1YZ.a);if(!B(_12M(_1Z0.a,_1Z0.b,_1Z0.c,_1Z1.a,_1Z1.b,_1Z1.c))){return false;}else{if(E(_1YY.b)!=E(_1YZ.b)){return false;}else{if(E(_1YW.b)!=E(_1YX.b)){return false;}else{var _1Z2=E(_1YW.c),_1Z3=E(_1YX.c);if(!B(_12M(_1Z2.a,_1Z2.b,_1Z2.c,_1Z3.a,_1Z3.b,_1Z3.c))){return false;}else{if(!B(_18O(_18Y,_1YW.d,_1YX.d))){return false;}else{var _1Z4=E(_1YW.e),_1Z5=E(_1YX.e);if(!B(_18O(_1EC,_1Z4.a,_1Z5.a))){return false;}else{return new F(function(){return _1YJ(_1Z4.b,_1Z5.b);});}}}}}}},_1Z6=function(_1Z7,_1Z8,_1Z9){while(1){var _1Za=E(_1Z9);if(!_1Za._){return false;}else{if(!B(A2(_1Z7,_1Za.a,_1Z8))){_1Z9=_1Za.b;continue;}else{return true;}}}},_1Zb=function(_1Zc,_1Zd){var _1Ze=function(_1Zf,_1Zg){while(1){var _1Zh=B((function(_1Zi,_1Zj){var _1Zk=E(_1Zi);if(!_1Zk._){return __Z;}else{var _1Zl=_1Zk.a,_1Zm=_1Zk.b;if(!B(_1Z6(_1Zc,_1Zl,_1Zj))){return new T2(1,_1Zl,new T(function(){return B(_1Ze(_1Zm,new T2(1,_1Zl,_1Zj)));}));}else{var _1Zn=_1Zj;_1Zf=_1Zm;_1Zg=_1Zn;return __continue;}}})(_1Zf,_1Zg));if(_1Zh!=__continue){return _1Zh;}}};return new F(function(){return _1Ze(_1Zd,_4);});},_1Zo=function(_1Zp){return E(E(_1Zp).b);},_1Zq=function(_1Zr,_1Zs,_1Zt){var _1Zu=new T(function(){return E(E(E(_1Zr).c).b);}),_1Zv=new T(function(){return E(E(_1Zs).h);}),_1Zw=new T(function(){return E(E(_1Zs).d);}),_1Zx=function(_1Zy,_1Zz,_1ZA,_1ZB,_1ZC){var _1ZD=E(_1Zy);if(!_1ZD._){return __Z;}else{var _1ZE=E(_1ZD.a),_1ZF=_1ZE.a,_1ZG=E(_1ZE.b),_1ZH=B(_14V(_1ZG,_1Zw));if(!_1ZH._){if(!B(_vZ(_j1,_1ZG,_1oY))){var _1ZI=B(_14V(_1ZG,_1Zv));if(!_1ZI._){return __Z;}else{var _1ZJ=function(_1ZK,_1ZL){while(1){var _1ZM=B((function(_1ZN,_1ZO){var _1ZP=E(_1ZO);if(!_1ZP._){var _1ZQ=_1ZP.d,_1ZR=new T(function(){var _1ZS=E(_1ZP.b);if(_1ZS._==1){return B(_0(B(_1Zx(new T1(1,new T2(0,_1ZF,_1ZS.a)),_1Zz,_1ZA,_1ZB,_1ZC)),new T(function(){return B(_1ZJ(_1ZN,_1ZQ));},1)));}else{return B(_1ZJ(_1ZN,_1ZQ));}},1);_1ZK=_1ZR;_1ZL=_1ZP.c;return __continue;}else{return E(_1ZN);}})(_1ZK,_1ZL));if(_1ZM!=__continue){return _1ZM;}}};return new F(function(){return _1ZJ(_4,_1ZI.a);});}}else{var _1ZT=new T(function(){var _1ZU=function(_){var _1ZV=newArr(1,_Vu),_1ZW=_1ZV,_1ZX=function(_1ZY,_1ZZ,_){while(1){var _200=E(_1ZY);if(_200==1){return _5;}else{var _201=E(_1ZZ);if(!_201._){return _5;}else{var _=_1ZW[_200]=_201.a;_1ZY=_200+1|0;_1ZZ=_201.b;continue;}}}},_202=B(_1ZX(0,new T2(1,new T2(1,new T1(1,_1ZC),_4),_4),_));return new T4(0,E(_1WK),E(_1WK),1,_1ZW);};return B(_8O(_1ZU));});return new T2(1,new T2(0,new T(function(){return E(_1Zz)+2|0;}),new T5(0,new T2(0,_1ZF,new T(function(){return E(_1Zz)+1|0;})),_1ZG,_1Cg,new T2(1,_1ZA,_4),new T2(0,_1ZB,_1ZT))),_4);}}else{var _203=new T2(1,_1ZA,_4),_204=new T(function(){return E(_1Zz)+2|0;}),_205=new T(function(){return B(_1Xs(_1ZC));}),_206=new T(function(){return E(_1Zz)+1|0;}),_207=function(_208){var _209=E(_208);return (_209._==0)?__Z:new T2(1,new T2(0,_204,new T5(0,new T2(0,_1ZF,_206),_1ZG,_1Cg,_203,new T(function(){var _20a=B(_1VN(_1Zs,_1WP,_1ZB,_209.a,new T2(1,new T5(0,new T2(0,_1Cg,_1Zz),_1oS,_1Cg,_203,new T2(0,_4,_205)),_4)));return new T2(0,_20a.a,_20a.b);}))),new T(function(){return B(_207(_209.b));}));};return new F(function(){return _207(_1ZH.a);});}}},_20b=new T(function(){return E(E(_1Zs).i);}),_20c=function(_20d,_20e,_20f,_20g,_20h,_20i,_20j){while(1){var _20k=B((function(_20l,_20m,_20n,_20o,_20p,_20q,_20r){var _20s=E(_20q);switch(_20s._){case 0:var _20t=_20l,_20u=_20m,_20v=_20n,_20w=_20o,_20x=new T2(1,_20s.b,_20p),_20y=_20r;_20d=_20t;_20e=_20u;_20f=_20v;_20g=_20w;_20h=_20x;_20i=_20s.c;_20j=_20y;return __continue;case 1:var _20t=_20l,_20u=_20m,_20v=_20n,_20w=_20o,_20x=_20p,_20y=new T2(1,_20s.b,_20r);_20d=_20t;_20e=_20u;_20f=_20v;_20g=_20w;_20h=_20x;_20i=_20s.a;_20j=_20y;return __continue;case 2:if(!E(_20r)._){var _20z=E(_20s.a);switch(_20z._){case 0:return new T2(1,new T2(0,new T(function(){return E(_20m)+1|0;}),new T5(0,new T2(0,_1XW,_20m),_1oS,_1Cg,new T2(1,_20n,_4),new T2(0,_4,new T(function(){return B(_1Xs(_20z.a));})))),_4);case 1:var _20A=new T(function(){return B(_1Xs(new T(function(){return B(_bZ(0,E(_20z.a),_4));})));});return new T2(1,new T2(0,new T(function(){return E(_20m)+1|0;}),new T5(0,new T2(0,_1XR,_20m),_1oT,_1Cg,new T2(1,_20n,_4),new T2(0,_4,_20A))),_4);default:var _20B=new T(function(){return B(_1Xs(new T(function(){var _20C=jsShow(E(_20z.a));return fromJSStr(_20C);})));});return new T2(1,new T2(0,new T(function(){return E(_20m)+1|0;}),new T5(0,new T2(0,_1XN,_20m),_1oU,_1Cg,new T2(1,_20n,_4),new T2(0,_4,_20B))),_4);}}else{return E(_1Y4);}break;case 3:return new F(function(){return _1Zx(_20l,_20m,_20n,_20p,new T2(1,_1Y5,new T(function(){return B(_bZ(0,_20s.a,_4));})));});break;case 4:var _20D=E(_20s.a),_20E=_20D.a,_20F=_20D.b,_20G=_20D.c,_20H=B(_1XD(_20E,_20F,_20G,_20b));if(!_20H._){var _20I=new T(function(){return B(unAppCStr("[",new T(function(){return B(_0(B(_1UO(_20E,_20F,_20G)),_1Y8));})));});return new F(function(){return _1Zx(_20l,_20m,_20n,_20p,_20I);});}else{var _20J=_20H.a,_20K=new T(function(){var _20L=B(_1XD(_20E,_20F,_20G,_1Zu));if(!_20L._){return E(_1Y6);}else{var _20M=E(E(_20L.a).a);return new T2(0,new T(function(){return B(_1Y1(_20M.a));}),_20M.b);}}),_20N=new T(function(){return E(E(_20K).b);}),_20O=new T(function(){return E(E(_20K).a);}),_20P=function(_20Q,_20R){var _20S=E(_20R);switch(_20S._){case 0:var _20T=new T(function(){return B(_jP(_20O,new T(function(){return B(_1XY(_20S.b));},1)));});return new T2(1,new T3(0,_20S.a,new T2(0,_20N,_20Q),_20T),_4);case 1:var _20U=_20S.a,_20V=B(_14V(_20U,_20J));if(!_20V._){return __Z;}else{var _20W=function(_20X,_20Y){while(1){var _20Z=B((function(_210,_211){var _212=E(_211);if(!_212._){var _213=new T(function(){return B(_0(B(_20P(_20U,_212.b)),new T(function(){return B(_20W(_210,_212.d));},1)));},1);_20X=_213;_20Y=_212.c;return __continue;}else{return E(_210);}})(_20X,_20Y));if(_20Z!=__continue){return _20Z;}}};return new F(function(){return _20W(_4,_20V.a);});}break;default:return E(_1Y7);}},_214=new T(function(){return B(_0(_20p,_20o));}),_215=function(_216,_217){var _218=E(_217);if(!_218._){return new T2(1,new T2(0,_216,_4),_4);}else{var _219=E(_218.a),_21a=_219.b,_21b=function(_21c){var _21d=E(_21c);if(!_21d._){return __Z;}else{var _21e=E(_21d.a),_21f=new T(function(){return B(_21b(_21d.b));}),_21g=function(_21h){var _21i=E(_21h);if(!_21i._){return E(_21f);}else{var _21j=E(_21i.a);return new T2(1,new T2(0,_21j.a,new T2(1,_21e.b,_21j.b)),new T(function(){return B(_21g(_21i.b));}));}};return new F(function(){return _21g(B(_215(_21e.a,_218.b)));});}};return new F(function(){return _21b(B(_20c(new T1(1,_219.a),_216,_21a,_214,_4,_21a,_4)));});}},_21k=function(_21l,_21m,_21n,_21o,_21p){var _21q=function(_21r){var _21s=E(_21r);if(!_21s._){return E(_21p);}else{var _21t=E(_21s.a),_21u=_21t.a;return new T2(1,new T2(0,new T(function(){return E(_21u)+1|0;}),new T5(0,new T2(0,_21m,_21u),_21n,_20D,new T2(1,_20n,_4),new T(function(){var _21v=B(_1VN(_1Zs,_1WP,_20p,_21l,_21t.b));return new T2(0,_21v.a,_21v.b);}))),new T(function(){return B(_21q(_21s.b));}));}};return new F(function(){return _21q(B(_215(_20m,B(_jP(_21o,_20r)))));});},_21w=E(_20l);if(!_21w._){var _21x=function(_21y,_21z){while(1){var _21A=B((function(_21B,_21C){var _21D=E(_21C);switch(_21D._){case 0:_21y=new T(function(){return B(_21x(_21B,_21D.d));},1);_21z=_21D.c;return __continue;case 1:var _21E=function(_21F,_21G){while(1){var _21H=B((function(_21I,_21J){var _21K=E(_21J);if(!_21K._){var _21L=new T(function(){var _21M=new T(function(){return B(_21E(_21I,_21K.d));}),_21N=function(_21O){var _21P=E(_21O);if(!_21P._){return E(_21M);}else{var _21Q=E(_21P.a),_21R=E(_21Q.b);return new F(function(){return _21k(_21Q.a,_21R.a,_21R.b,_21Q.c,new T(function(){return B(_21N(_21P.b));}));});}};return B(_21N(B(_20P(_21D.a,_21K.b))));},1);_21F=_21L;_21G=_21K.c;return __continue;}else{return E(_21I);}})(_21F,_21G));if(_21H!=__continue){return _21H;}}};return new F(function(){return _21E(_21B,_21D.b);});break;default:return E(_21B);}})(_21y,_21z));if(_21A!=__continue){return _21A;}}},_21S=E(_20J);if(!_21S._){var _21T=_21S.c,_21U=_21S.d;if(_21S.b>=0){return new F(function(){return _21x(new T(function(){return B(_21x(_4,_21U));},1),_21T);});}else{return new F(function(){return _21x(new T(function(){return B(_21x(_4,_21T));},1),_21U);});}}else{return new F(function(){return _21x(_4,_21S);});}}else{var _21V=E(E(_21w.a).b),_21W=B(_14V(_21V,_20J));if(!_21W._){return __Z;}else{var _21X=function(_21Y,_21Z){while(1){var _220=B((function(_221,_222){var _223=E(_222);if(!_223._){var _224=new T(function(){var _225=new T(function(){return B(_21X(_221,_223.d));}),_226=function(_227){var _228=E(_227);if(!_228._){return E(_225);}else{var _229=E(_228.a),_22a=E(_229.b);return new F(function(){return _21k(_229.a,_22a.a,_22a.b,_229.c,new T(function(){return B(_226(_228.b));}));});}};return B(_226(B(_20P(_21V,_223.b))));},1);_21Y=_224;_21Z=_223.c;return __continue;}else{return E(_221);}})(_21Y,_21Z));if(_220!=__continue){return _220;}}};return new F(function(){return _21X(_4,_21W.a);});}}}break;case 5:return new F(function(){return _1Zx(_20l,_20m,_20n,_20p,new T(function(){var _22b=B(_1Eb(B(_0(_20p,_20o)),_20s.a));return B(_1UO(_22b.a,_22b.b,_22b.c));}));});break;case 6:var _20t=_20l,_20u=_20m,_20v=_20n,_20w=_20o,_20x=_20p,_20y=_20r;_20d=_20t;_20e=_20u;_20f=_20v;_20g=_20w;_20h=_20x;_20i=_20s.a;_20j=_20y;return __continue;default:var _20t=_20l,_20u=_20m,_20v=_20n,_20w=_20o,_20x=_20p,_20y=_20r;_20d=_20t;_20e=_20u;_20f=_20v;_20g=_20w;_20h=_20x;_20i=_20s.a;_20j=_20y;return __continue;}})(_20d,_20e,_20f,_20g,_20h,_20i,_20j));if(_20k!=__continue){return _20k;}}};return new F(function(){return _1Zb(_1YT,B(_G(_1Zo,B(_20c(_4l,_1WK,_1Zt,_4,_4,_1Zt,_4)))));});},_22c=function(_22d){var _22e=E(_22d);if(!_22e._){return __Z;}else{return new F(function(){return _0(_22e.a,new T(function(){return B(_22c(_22e.b));},1));});}},_22f=function(_22g){var _22h=E(_22g);if(!_22h._){return E(_1SD);}else{var _22i=E(_22h.a);if(!_22i._){return __Z;}else{var _22j=B(_22f(_22h.b));return (_22j._==0)?__Z:new T1(1,new T2(1,_22i.a,_22j.a));}}},_22k=function(_22l,_22m){var _22n=new T(function(){return B(_1Xh(_1G3,_1Xe,_22m,B(_1Xf(_22l))));}),_22o=function(_22p,_22q,_22r,_22s,_22t){var _22u=E(_22n),_22v=B(_22f(B(_1TW(B(_1WX(_22u.c,_22u.e,_22u.f,_22p,_22q,_22r,_22s,_22t)),_4l)).b));if(!_22v._){return __Z;}else{return new F(function(){return _22c(_22v.a);});}},_22w=function(_22x){var _22y=E(_22x);return new F(function(){return _22o(_22y.a,E(_22y.b),_22y.c,_22y.d,_22y.e);});};return function(_22z){var _22A=B(_G(_22w,B(_1Zq(_22l,_22n,_22z))));return (_22A._==0)?__Z:E(_22A.a);};},_22B=new T(function(){return B(unCStr("?0"));}),_22C=new T2(0,_4,_22B),_22D=new T2(1,_22C,_4),_22E=0,_22F=new T(function(){return B(_1QQ(_4,_4));}),_22G=function(_22H,_22I,_22J,_22K){while(1){var _22L=B((function(_22M,_22N,_22O,_22P){var _22Q=E(_22M);if(!_22Q._){return __Z;}else{var _22R=_22Q.b,_22S=E(_22Q.a);if(!_22S._){var _22T=E(_22N);if(E(_22S.b)!=_22T){var _22U=B(_22G(_22S.c,_22T,new T2(1,_22P,_22O),_22E));if(!_22U._){var _22V=_22O;_22H=_22R;_22I=_22T;_22J=_22V;_22K=new T(function(){return E(_22P)+1|0;});return __continue;}else{return E(_22U);}}else{return new T2(1,_22P,_22O);}}else{var _22W=_22N,_22V=_22O;_22H=_22R;_22I=_22W;_22J=_22V;_22K=new T(function(){return E(_22P)+1|0;});return __continue;}}})(_22H,_22I,_22J,_22K));if(_22L!=__continue){return _22L;}}},_22X=function(_22Y,_22Z){var _230=E(_22Y);if(!_230._){var _231=E(_22Z);if(E(_230.b)!=_231){return new F(function(){return _1QQ(B(_22G(_230.c,_231,_4,_22E)),_4);});}else{return E(_22F);}}else{return E(_22F);}},_232=new T(function(){return B(_7f("Muste.hs:(45,9)-(54,31)|function deep"));}),_233=function(_234,_235,_236,_237){var _238=E(_236);if(!_238._){return E(_237);}else{var _239=_238.b,_23a=E(_238.a);if(!_23a._){return new T2(1,new T2(0,new T(function(){return B(_22X(_234,_235));}),_23a.a),new T(function(){return B(_233(_234,_235,_239,_237));}));}else{return new F(function(){return _0(B(_23b(_234,_23a)),new T(function(){return B(_233(_234,_235,_239,_237));},1));});}}},_23b=function(_23c,_23d){var _23e=E(_23d);if(!_23e._){return E(_232);}else{var _23f=_23e.b,_23g=E(_23e.f);if(!_23g._){return __Z;}else{var _23h=function(_23i){var _23j=E(_23e.e);if(!_23j._){return new F(function(){return _233(_23c,_23f,_23g,_4);});}else{var _23k=E(_23j.a);if(_23k._==3){if(!E(_23j.b)._){var _23l=new T(function(){return B(unAppCStr("?",new T(function(){return B(_bZ(0,_23k.a,_4));})));});return new T2(1,new T2(0,new T(function(){return B(_22X(_23c,_23f));}),_23l),_4);}else{return new F(function(){return _233(_23c,_23f,_23g,_4);});}}else{return new F(function(){return _233(_23c,_23f,_23g,_4);});}}},_23m=E(_23g.a);if(!_23m._){if(!E(_23g.b)._){return new T2(1,new T2(0,new T(function(){return B(_22X(_23c,_23f));}),_23m.a),_4);}else{return new F(function(){return _23h(_);});}}else{return new F(function(){return _23h(_);});}}}},_23n=function(_23o){return E(E(_23o).c);},_23p=function(_23q){return new T1(3,E(_23q));},_23r=function(_23s,_23t){while(1){var _23u=E(_23s);if(!_23u._){return E(_23t);}else{var _23v=new T2(1,_23t,_23u.a);_23s=_23u.b;_23t=_23v;continue;}}},_23w=function(_23x,_23y){var _23z=E(_23x);if(!_23z._){var _23A=new T(function(){var _23B=B(_23C(_23z.c,_23y));return new T2(0,_23B.a,_23B.b);});return new T2(0,new T(function(){return E(E(_23A).a);}),new T(function(){return B(_23r(E(_23A).b,new T1(4,_23z.a)));}));}else{return new T2(0,new T(function(){return E(_23y)+1|0;}),new T(function(){return B(_23p(_23y));}));}},_23C=function(_23D,_23E){var _23F=E(_23D);if(!_23F._){return new T2(0,_23E,_4);}else{var _23G=new T(function(){var _23H=B(_23w(_23F.a,_23E));return new T2(0,_23H.a,_23H.b);}),_23I=new T(function(){var _23J=B(_23C(_23F.b,new T(function(){return E(E(_23G).a);})));return new T2(0,_23J.a,_23J.b);});return new T2(0,new T(function(){return E(E(_23I).a);}),new T2(1,new T(function(){return E(E(_23G).b);}),new T(function(){return E(E(_23I).b);})));}},_23K=new T1(3,0),_23L=function(_23M){var _23N=E(_23M);if(!_23N._){return new F(function(){return _23r(B(_23C(_23N.c,_22E)).b,new T1(4,_23N.a));});}else{return E(_23K);}},_23O=-1,_23P=function(_23Q){var _23R=B(_23S(_23Q));return new T3(0,_23R.a,_23R.b,_23R.c);},_23T=new T(function(){return B(unCStr("_"));}),_23U=new T(function(){return B(_1za(_23T));}),_23V=new T(function(){return B(_G(_1z8,_23U));}),_23W=new T(function(){var _23X=B(_1xU(_23V));return new T3(0,_23X.a,_23X.b,_23X.c);}),_23Y=new T0(1),_23Z=new T2(1,_23Y,_4),_240=new T3(0,_23W,_23O,_23Z),_241=new T2(1,_240,_4),_242=new T(function(){return B(_7f("Muste/Tree/Internal.hs:(285,5)-(287,70)|function convert"));}),_23S=function(_243){var _244=E(_243);if(!_244._){var _245=E(_244.b);if(!_245._){var _246=_245.a,_247=E(_244.c);return (_247._==0)?new T3(0,_246,_23O,_4):new T3(0,_246,_23O,new T(function(){return B(_G(_23P,_247));}));}else{return E(_242);}}else{return new T3(0,_244.a,_23O,_241);}},_248=function(_249,_24a){var _24b=E(_24a);if(!_24b._){return new T2(0,_249,_4);}else{var _24c=new T(function(){var _24d=E(_24b.a);if(!_24d._){var _24e=_24d.a,_24f=E(_24d.c);if(!_24f._){return new T2(0,new T(function(){return E(_249)+1|0;}),new T3(0,_24e,_249,_4));}else{var _24g=new T(function(){var _24h=B(_248(_249,_24f));return new T2(0,_24h.a,_24h.b);}),_24i=new T(function(){return E(E(_24g).a);});return new T2(0,new T(function(){return E(_24i)+1|0;}),new T3(0,_24e,_24i,new T(function(){return E(E(_24g).b);})));}}else{return new T2(0,_249,_23Y);}}),_24j=new T(function(){var _24k=B(_248(new T(function(){return E(E(_24c).a);}),_24b.b));return new T2(0,_24k.a,_24k.b);});return new T2(0,new T(function(){return E(E(_24j).a);}),new T2(1,new T(function(){return E(E(_24c).b);}),new T(function(){return E(E(_24j).b);})));}},_24l=function(_24m){var _24n=B(_23S(_24m)),_24o=_24n.a,_24p=E(_24n.c);if(!_24p._){return new T3(0,_24o,_22E,_4);}else{var _24q=new T(function(){var _24r=B(_248(_22E,_24p));return new T2(0,_24r.a,_24r.b);});return new T3(0,_24o,new T(function(){return E(E(_24q).a);}),new T(function(){return E(E(_24q).b);}));}},_24s=function(_24t,_24u,_24v){var _24w=new T(function(){return E(E(_24v).a);}),_24x=B(A3(_22k,new T(function(){return B(_23n(_24t));}),_24u,new T(function(){return B(_23L(_24w));})));if(!_24x._){return E(_22D);}else{return new F(function(){return _23b(new T(function(){return B(_24l(_24w));}),_24x.a);});}},_24y=new T2(1,_4,_4),_24z=function(_24A,_24B){var _24C=function(_24D,_24E){var _24F=E(_24D);if(!_24F._){return E(_24E);}else{var _24G=_24F.a,_24H=E(_24E);if(!_24H._){return E(_24F);}else{var _24I=_24H.a;return (B(A2(_24A,_24G,_24I))==2)?new T2(1,_24I,new T(function(){return B(_24C(_24F,_24H.b));})):new T2(1,_24G,new T(function(){return B(_24C(_24F.b,_24H));}));}}},_24J=function(_24K){var _24L=E(_24K);if(!_24L._){return __Z;}else{var _24M=E(_24L.b);return (_24M._==0)?E(_24L):new T2(1,new T(function(){return B(_24C(_24L.a,_24M.a));}),new T(function(){return B(_24J(_24M.b));}));}},_24N=new T(function(){return B(_24O(B(_24J(_4))));}),_24O=function(_24P){while(1){var _24Q=E(_24P);if(!_24Q._){return E(_24N);}else{if(!E(_24Q.b)._){return E(_24Q.a);}else{_24P=B(_24J(_24Q));continue;}}}},_24R=new T(function(){return B(_24S(_4));}),_24T=function(_24U,_24V,_24W){while(1){var _24X=B((function(_24Y,_24Z,_250){var _251=E(_250);if(!_251._){return new T2(1,new T2(1,_24Y,_24Z),_24R);}else{var _252=_251.a;if(B(A2(_24A,_24Y,_252))==2){var _253=new T2(1,_24Y,_24Z);_24U=_252;_24V=_253;_24W=_251.b;return __continue;}else{return new T2(1,new T2(1,_24Y,_24Z),new T(function(){return B(_24S(_251));}));}}})(_24U,_24V,_24W));if(_24X!=__continue){return _24X;}}},_254=function(_255,_256,_257){while(1){var _258=B((function(_259,_25a,_25b){var _25c=E(_25b);if(!_25c._){return new T2(1,new T(function(){return B(A1(_25a,new T2(1,_259,_4)));}),_24R);}else{var _25d=_25c.a,_25e=_25c.b;switch(B(A2(_24A,_259,_25d))){case 0:_255=_25d;_256=function(_25f){return new F(function(){return A1(_25a,new T2(1,_259,_25f));});};_257=_25e;return __continue;case 1:_255=_25d;_256=function(_25g){return new F(function(){return A1(_25a,new T2(1,_259,_25g));});};_257=_25e;return __continue;default:return new T2(1,new T(function(){return B(A1(_25a,new T2(1,_259,_4)));}),new T(function(){return B(_24S(_25c));}));}}})(_255,_256,_257));if(_258!=__continue){return _258;}}},_24S=function(_25h){var _25i=E(_25h);if(!_25i._){return E(_24y);}else{var _25j=_25i.a,_25k=E(_25i.b);if(!_25k._){return new T2(1,_25i,_4);}else{var _25l=_25k.a,_25m=_25k.b;if(B(A2(_24A,_25j,_25l))==2){return new F(function(){return _24T(_25l,new T2(1,_25j,_4),_25m);});}else{return new F(function(){return _254(_25l,function(_25n){return new T2(1,_25j,_25n);},_25m);});}}}};return new F(function(){return _24O(B(_24S(_24B)));});},_25o=function(_25p,_25q,_25r,_25s){var _25t=B(_1ni(_4,_25s)),_25u=new T(function(){return B(_G(_1Zo,B(_24s(_25p,_25q,_25r))));}),_25v=function(_25w,_25x){var _25y=E(_25w);if(!_25y._){return __Z;}else{var _25z=E(_25x);return (_25z._==0)?__Z:new T2(1,new T2(0,new T(function(){var _25A=E(_25u);if(!_25A._){var _25B=B(_uU(_4,0));return _25B+_25B|0;}else{var _25C=B(_G(_1Zo,B(_24s(_25p,_25q,_25y.a))));if(!_25C._){var _25D=B(_uU(_4,0));return _25D+_25D|0;}else{var _25E=B(_1QV(_sz,_25A,_25C,_4,_4));return B(_uU(_25E.a,0))+B(_uU(_25E.b,0))|0;}}}),_25z.a),new T(function(){return B(_25v(_25y.b,_25z.b));}));}};return new F(function(){return _G(_1Zo,B(_24z(function(_25F,_25G){var _25H=E(_25F),_25I=E(_25G),_25J=E(_25I.a),_25K=E(_25H.a);if(_25J>=_25K){if(_25J!=_25K){return 2;}else{var _25L=B(_24s(_25p,_25q,_25H.b)),_25M=B(_uU(_25L,0)),_25N=B(_24s(_25p,_25q,_25I.b)),_25O=B(_uU(_25N,0));if(_25M>=_25O){if(_25M!=_25O){return 2;}else{return new F(function(){return _1bD(_1Sz,_25L,_25N);});}}else{return 0;}}}else{return 0;}},B(_25v(_25t,_25t)))));});},_25P=function(_25Q){while(1){var _25R=E(_25Q);if(!_25R._){return false;}else{if(!E(_25R.a)){_25Q=_25R.b;continue;}else{return true;}}}},_25S=function(_25T){var _25U=E(_25T);if(!_25U._){return new F(function(){return _25P(B(_G(_25S,_25U.c)));});}else{return true;}},_25V=function(_25W){return (!B(_25S(B(_1Qw(_25W)))))?true:false;},_25X=function(_25Y){while(1){var _25Z=E(_25Y);if(!_25Z._){_25Y=new T1(1,I_fromInt(_25Z.a));continue;}else{return new F(function(){return I_toString(_25Z.a);});}}},_260=function(_261,_262){return new F(function(){return _0(fromJSStr(B(_25X(_261))),_262);});},_263=new T1(0,0),_264=function(_265,_266,_267){if(_265<=6){return new F(function(){return _260(_266,_267);});}else{if(!B(_Fm(_266,_263))){return new F(function(){return _260(_266,_267);});}else{return new T2(1,_bY,new T(function(){return B(_0(fromJSStr(B(_25X(_266))),new T2(1,_bX,_267)));}));}}},_268=new T1(0,1),_269=new T1(0,0),_26a=new T(function(){var _26b=B(_JB(_269,_268));return new T2(1,_26b.a,_26b.b);}),_26c=32,_26d=new T(function(){return B(unCStr(" "));}),_26e=new T2(0,_4,_26d),_26f=new T2(1,_26e,_4),_26g=function(_26h){var _26i=E(_26h);if(!_26i._){return E(_26f);}else{var _26j=E(_26i.a);return new T2(1,new T2(0,_26j.a,_26d),new T2(1,_26j,new T(function(){return B(_26g(_26i.b));})));}},_26k=function(_26l,_26m,_26n){var _26o=function(_26p,_26q){var _26r=E(_26p);if(!_26r._){return __Z;}else{var _26s=_26r.b,_26t=E(_26q);if(!_26t._){return __Z;}else{var _26u=_26t.b,_26v=new T(function(){var _26w=E(_26t.a),_26x=new T(function(){var _26y=new T(function(){if(!E(_26l)){return __Z;}else{return B(unAppCStr(" ",new T(function(){return B(_3X(_dY,_26w.a,_4));})));}},1);return B(_0(_26w.b,_26y));});if(!E(_26m)){return B(_0(_26x,new T(function(){return B(_26o(_26s,_26u));},1)));}else{var _26z=new T(function(){return B(_0(B(_264(0,_26r.a,_4)),new T(function(){return B(unAppCStr(") ",_26x));},1)));});return B(_0(B(unAppCStr("(",_26z)),new T(function(){return B(_26o(_26s,_26u));},1)));}});return new T2(1,_26c,_26v);}}},_26A=B(_26o(_26a,new T(function(){return B(_26g(_26n));},1)));return (_26A._==0)?__Z:E(_26A.b);},_26B=function(_26C,_26D,_26E){var _26F=function(_26G){return new F(function(){return _26k(_w7,_w7,new T(function(){return B(_24s(_26C,_26D,_26G));},1));});};return new F(function(){return _G(_26F,_26E);});},_26H=function(_26I,_26J){var _26K=E(_26J);if(!_26K._){return new T2(0,_4,_4);}else{var _26L=_26K.a;if(!B(A1(_26I,_26L))){var _26M=new T(function(){var _26N=B(_26H(_26I,_26K.b));return new T2(0,_26N.a,_26N.b);});return new T2(0,new T2(1,_26L,new T(function(){return E(E(_26M).a);})),new T(function(){return E(E(_26M).b);}));}else{return new T2(0,_4,_26K);}}},_26O=function(_26P){var _26Q=_26P>>>0;if(_26Q>887){var _26R=u_iswspace(_26P);return (E(_26R)==0)?false:true;}else{var _26S=E(_26Q);return (_26S==32)?true:(_26S-9>>>0>4)?(E(_26S)==160)?true:false:true;}},_26T=function(_26U){return new F(function(){return _26O(E(_26U));});},_26V=function(_26W){var _26X=B(_G7(_26T,_26W));if(!_26X._){return __Z;}else{var _26Y=new T(function(){var _26Z=B(_26H(_26T,_26X));return new T2(0,_26Z.a,_26Z.b);});return new T2(1,new T(function(){return E(E(_26Y).a);}),new T(function(){return B(_26V(E(_26Y).b));}));}},_270=function(_271,_272,_273,_274,_275,_276){var _277=new T(function(){var _278=B(_1Ek(new T(function(){return B(_1Qw(_273));}),_274));if(!_278._){return E(_1Ex);}else{return E(_278.a);}}),_279=new T2(0,_277,_ML),_27a=new T(function(){return B(_G(_1Zo,B(_24s(_271,_272,_279))));}),_27b=new T(function(){return B(_uU(_27a,0));}),_27c=new T(function(){var _27d=B(_uU(B(_24s(_271,_272,_279)),0));if(!E(_275)){return _27d;}else{return _27d+1|0;}}),_27e=B(_1PL(function(_27f){return E(_27c)>=B(_uU(B(_24s(_271,_272,_27f)),0));},B(_25o(_271,_272,_279,B(_1o1(_25V,B(_1Qy(_271,_273,_274,_276)))))))),_27g=function(_27h,_27i){while(1){var _27j=B((function(_27k,_27l){var _27m=E(_27k);if(!_27m._){return __Z;}else{var _27n=_27m.a,_27o=_27m.b,_27p=E(_27l);if(!_27p._){return __Z;}else{var _27q=_27p.a,_27r=_27p.b,_27s=B(_26V(_27n));if(!B(_1aJ(_27s,_27a))){var _27t=B(_uU(_27s,0)),_27u=E(_27b);if(_27t!=_27u){if(_27t<=_27u){_27h=_27o;_27i=_27r;return __continue;}else{var _27v=E(_27s);if(!_27v._){var _27w=B(_uU(_4,0));if(!(_27w+_27w|0)){_27h=_27o;_27i=_27r;return __continue;}else{return new T2(1,new T2(0,_27n,_27q),new T(function(){return B(_27g(_27o,_27r));}));}}else{var _27x=E(_27a);if(!_27x._){var _27y=B(_uU(_4,0));if(!(_27y+_27y|0)){_27h=_27o;_27i=_27r;return __continue;}else{return new T2(1,new T2(0,_27n,_27q),new T(function(){return B(_27g(_27o,_27r));}));}}else{var _27z=B(_1QV(_sz,_27v,_27x,_4,_4));if(!(B(_uU(_27z.a,0))+B(_uU(_27z.b,0))|0)){_27h=_27o;_27i=_27r;return __continue;}else{return new T2(1,new T2(0,_27n,_27q),new T(function(){return B(_27g(_27o,_27r));}));}}}}}else{return new T2(1,new T2(0,_27n,_27q),new T(function(){return B(_27g(_27o,_27r));}));}}else{_27h=_27o;_27i=_27r;return __continue;}}}})(_27h,_27i));if(_27j!=__continue){return _27j;}}};return new F(function(){return _27g(B(_26B(_271,_272,_27e)),_27e);});},_27A=function(_27B){return E(E(_27B).d);},_27C=function(_27D,_27E){return new F(function(){return A2(_27A,B(_2z(_27D)),new T1(1,_27E));});},_27F=new T2(0,_2j,_27C),_27G=function(_){return new F(function(){return __app1(E(_1DT),"div");});},_27H=new T(function(){return new T2(0,E(new T1(2,"id")),"suggestionList");}),_27I=new T2(1,_27H,_4),_27J=function(_27K){return E(E(_27K).a);},_27L=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_27M=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_27N=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_27O=function(_27P,_27Q,_27R,_27S){var _27T=new T(function(){return B(A2(_27J,_27P,_27R));}),_27U=function(_27V,_){var _27W=E(_27V);if(!_27W._){return _5;}else{var _27X=E(_27T),_27Y=E(_1DU),_27Z=__app2(_27Y,E(_27W.a),_27X),_280=function(_281,_){while(1){var _282=E(_281);if(!_282._){return _5;}else{var _283=__app2(_27Y,E(_282.a),_27X);_281=_282.b;continue;}}};return new F(function(){return _280(_27W.b,_);});}},_284=function(_285,_){while(1){var _286=B((function(_287,_){var _288=E(_287);if(!_288._){return _5;}else{var _289=_288.b,_28a=E(_288.a);if(!_28a._){var _28b=_28a.b,_28c=E(_28a.a);switch(_28c._){case 0:var _28d=E(_27T),_28e=E(_27N),_28f=__app3(_28e,_28d,_28c.a,_28b),_28g=function(_28h,_){while(1){var _28i=E(_28h);if(!_28i._){return _5;}else{var _28j=_28i.b,_28k=E(_28i.a);if(!_28k._){var _28l=_28k.b,_28m=E(_28k.a);switch(_28m._){case 0:var _28n=__app3(_28e,_28d,_28m.a,_28l);_28h=_28j;continue;case 1:var _28o=__app3(E(_27M),_28d,_28m.a,_28l);_28h=_28j;continue;default:var _28p=__app3(E(_27L),_28d,_28m.a,_28l);_28h=_28j;continue;}}else{var _28q=B(_27U(_28k.a,_));_28h=_28j;continue;}}}};return new F(function(){return _28g(_289,_);});break;case 1:var _28r=E(_27T),_28s=E(_27M),_28t=__app3(_28s,_28r,_28c.a,_28b),_28u=function(_28v,_){while(1){var _28w=E(_28v);if(!_28w._){return _5;}else{var _28x=_28w.b,_28y=E(_28w.a);if(!_28y._){var _28z=_28y.b,_28A=E(_28y.a);switch(_28A._){case 0:var _28B=__app3(E(_27N),_28r,_28A.a,_28z);_28v=_28x;continue;case 1:var _28C=__app3(_28s,_28r,_28A.a,_28z);_28v=_28x;continue;default:var _28D=__app3(E(_27L),_28r,_28A.a,_28z);_28v=_28x;continue;}}else{var _28E=B(_27U(_28y.a,_));_28v=_28x;continue;}}}};return new F(function(){return _28u(_289,_);});break;default:var _28F=E(_27T),_28G=E(_27L),_28H=__app3(_28G,_28F,_28c.a,_28b),_28I=function(_28J,_){while(1){var _28K=E(_28J);if(!_28K._){return _5;}else{var _28L=_28K.b,_28M=E(_28K.a);if(!_28M._){var _28N=_28M.b,_28O=E(_28M.a);switch(_28O._){case 0:var _28P=__app3(E(_27N),_28F,_28O.a,_28N);_28J=_28L;continue;case 1:var _28Q=__app3(E(_27M),_28F,_28O.a,_28N);_28J=_28L;continue;default:var _28R=__app3(_28G,_28F,_28O.a,_28N);_28J=_28L;continue;}}else{var _28S=B(_27U(_28M.a,_));_28J=_28L;continue;}}}};return new F(function(){return _28I(_289,_);});}}else{var _28T=B(_27U(_28a.a,_));_285=_289;return __continue;}}})(_285,_));if(_286!=__continue){return _286;}}};return new F(function(){return A2(_6i,_27Q,function(_){return new F(function(){return _284(_27S,_);});});});},_28U=function(_28V,_28W,_28X,_28Y){var _28Z=B(_2z(_28W)),_290=function(_291){return new F(function(){return A3(_6c,_28Z,new T(function(){return B(_27O(_28V,_28W,_291,_28Y));}),new T(function(){return B(A2(_27A,_28Z,_291));}));});};return new F(function(){return A3(_1V,_28Z,_28X,_290);});},_292=new T(function(){return B(_28U(_27F,_dh,_27G,_27I));}),_293=new T(function(){return B(unCStr("div"));}),_294=new T(function(){return B(unCStr("suggestionList"));}),_295=new T(function(){return B(unCStr(")"));}),_296=new T(function(){return eval("(function(s){return document.createTextNode(s);})");}),_297=new T(function(){return eval("(function(x){console.log(x);})");}),_298=function(_299,_29a,_29b,_29c,_29d,_29e,_){var _29f=new T(function(){var _29g=E(E(_29e).a),_29h=new T(function(){return B(unAppCStr(",",new T(function(){return B(_0(B(_bZ(0,E(_29g.b),_4)),_295));})));},1);return B(_0(B(_bZ(0,E(_29g.a),_4)),_29h));}),_29i=__app1(E(_297),toJSStr(B(unAppCStr("Click on (",_29f)))),_29j=__app1(E(_1DZ),toJSStr(E(_294))),_29k=__eq(_29j,E(_D)),_29l=function(_,_29m){var _29n=function(_){var _29o=B(A1(_292,_)),_29p=_29o,_29q=function(_29r,_){while(1){var _29s=E(_29r);if(!_29s._){return _5;}else{var _29t=__app1(E(_296),toJSStr(E(E(_29s.a).a))),_29u=__app1(E(_1DT),toJSStr(E(_293))),_29v=E(_1DU),_29w=__app2(_29v,_29t,_29u),_29x=__app2(_29v,_29u,E(_29p));_29r=_29s.b;continue;}}},_29y=B(_29q(B(_270(_299,_29a,_29b,_29c,_29d,_1DX)),_)),_29z=__app2(E(_1DU),E(_29p),E(_1DY));return _5;},_29A=E(_29m);if(!_29A._){return new F(function(){return _29n(_);});}else{var _29B=E(_29A.a),_29C=__app1(E(_1DV),_29B),_29D=__app2(E(_1DW),_29B,E(_1DY));return new F(function(){return _29n(_);});}};if(!E(_29k)){var _29E=__isUndef(_29j);if(!E(_29E)){return new F(function(){return _29l(_,new T1(1,_29j));});}else{return new F(function(){return _29l(_,_4l);});}}else{return new F(function(){return _29l(_,_4l);});}},_29F=new T(function(){return eval("(function(b){return b.size;})");}),_29G=function(_29H){return new F(function(){return _z(function(_){var _29I=__app1(E(_29F),E(_29H));return new F(function(){return _cr(_29I,0);});});});},_29J=0,_29K=new T1(1,_4),_29L=new T(function(){return eval("(function(b,cb){var r=new FileReader();r.onload=function(){cb(new DataView(r.result));};r.readAsArrayBuffer(b);})");}),_29M=function(_29N,_29O){var _29P=new T(function(){return B(_29G(_29O));}),_29Q=function(_29R){var _29S=function(_){var _29T=nMV(_29K),_29U=_29T,_29V=function(_){var _29W=function(_29X,_){var _29Y=B(_c(new T(function(){return B(A(_7r,[_2l,_29U,new T3(0,_29J,_29P,_29X),_2c]));}),_4,_));return _D;},_29Z=__createJSFunc(2,E(_29W)),_2a0=__app2(E(_29L),E(_29O),_29Z);return new T(function(){return B(A3(_7H,_2l,_29U,_29R));});};return new T1(0,_29V);};return new T1(0,_29S);};return new F(function(){return A2(_6g,_29N,_29Q);});},_2a1=function(_2a2,_2a3){while(1){var _2a4=E(_2a3);if(!_2a4._){_2a2=_2a4.b;_2a3=_2a4.d;continue;}else{return E(_2a2);}}},_2a5=new T(function(){return B(unCStr("AjaxError"));}),_2a6=new T(function(){return B(err(_2a5));}),_2a7=new T(function(){return B(unCStr("ACK"));}),_2a8=new T(function(){return B(unCStr("BEL"));}),_2a9=new T(function(){return B(unCStr("BS"));}),_2aa=new T(function(){return B(unCStr("SP"));}),_2ab=new T2(1,_2aa,_4),_2ac=new T(function(){return B(unCStr("US"));}),_2ad=new T2(1,_2ac,_2ab),_2ae=new T(function(){return B(unCStr("RS"));}),_2af=new T2(1,_2ae,_2ad),_2ag=new T(function(){return B(unCStr("GS"));}),_2ah=new T2(1,_2ag,_2af),_2ai=new T(function(){return B(unCStr("FS"));}),_2aj=new T2(1,_2ai,_2ah),_2ak=new T(function(){return B(unCStr("ESC"));}),_2al=new T2(1,_2ak,_2aj),_2am=new T(function(){return B(unCStr("SUB"));}),_2an=new T2(1,_2am,_2al),_2ao=new T(function(){return B(unCStr("EM"));}),_2ap=new T2(1,_2ao,_2an),_2aq=new T(function(){return B(unCStr("CAN"));}),_2ar=new T2(1,_2aq,_2ap),_2as=new T(function(){return B(unCStr("ETB"));}),_2at=new T2(1,_2as,_2ar),_2au=new T(function(){return B(unCStr("SYN"));}),_2av=new T2(1,_2au,_2at),_2aw=new T(function(){return B(unCStr("NAK"));}),_2ax=new T2(1,_2aw,_2av),_2ay=new T(function(){return B(unCStr("DC4"));}),_2az=new T2(1,_2ay,_2ax),_2aA=new T(function(){return B(unCStr("DC3"));}),_2aB=new T2(1,_2aA,_2az),_2aC=new T(function(){return B(unCStr("DC2"));}),_2aD=new T2(1,_2aC,_2aB),_2aE=new T(function(){return B(unCStr("DC1"));}),_2aF=new T2(1,_2aE,_2aD),_2aG=new T(function(){return B(unCStr("DLE"));}),_2aH=new T2(1,_2aG,_2aF),_2aI=new T(function(){return B(unCStr("SI"));}),_2aJ=new T2(1,_2aI,_2aH),_2aK=new T(function(){return B(unCStr("SO"));}),_2aL=new T2(1,_2aK,_2aJ),_2aM=new T(function(){return B(unCStr("CR"));}),_2aN=new T2(1,_2aM,_2aL),_2aO=new T(function(){return B(unCStr("FF"));}),_2aP=new T2(1,_2aO,_2aN),_2aQ=new T(function(){return B(unCStr("VT"));}),_2aR=new T2(1,_2aQ,_2aP),_2aS=new T(function(){return B(unCStr("LF"));}),_2aT=new T2(1,_2aS,_2aR),_2aU=new T(function(){return B(unCStr("HT"));}),_2aV=new T2(1,_2aU,_2aT),_2aW=new T2(1,_2a9,_2aV),_2aX=new T2(1,_2a8,_2aW),_2aY=new T2(1,_2a7,_2aX),_2aZ=new T(function(){return B(unCStr("ENQ"));}),_2b0=new T2(1,_2aZ,_2aY),_2b1=new T(function(){return B(unCStr("EOT"));}),_2b2=new T2(1,_2b1,_2b0),_2b3=new T(function(){return B(unCStr("ETX"));}),_2b4=new T2(1,_2b3,_2b2),_2b5=new T(function(){return B(unCStr("STX"));}),_2b6=new T2(1,_2b5,_2b4),_2b7=new T(function(){return B(unCStr("SOH"));}),_2b8=new T2(1,_2b7,_2b6),_2b9=new T(function(){return B(unCStr("NUL"));}),_2ba=new T2(1,_2b9,_2b8),_2bb=92,_2bc=new T(function(){return B(unCStr("\\DEL"));}),_2bd=new T(function(){return B(unCStr("\\a"));}),_2be=new T(function(){return B(unCStr("\\\\"));}),_2bf=new T(function(){return B(unCStr("\\SO"));}),_2bg=new T(function(){return B(unCStr("\\r"));}),_2bh=new T(function(){return B(unCStr("\\f"));}),_2bi=new T(function(){return B(unCStr("\\v"));}),_2bj=new T(function(){return B(unCStr("\\n"));}),_2bk=new T(function(){return B(unCStr("\\t"));}),_2bl=new T(function(){return B(unCStr("\\b"));}),_2bm=function(_2bn,_2bo){if(_2bn<=127){var _2bp=E(_2bn);switch(_2bp){case 92:return new F(function(){return _0(_2be,_2bo);});break;case 127:return new F(function(){return _0(_2bc,_2bo);});break;default:if(_2bp<32){var _2bq=E(_2bp);switch(_2bq){case 7:return new F(function(){return _0(_2bd,_2bo);});break;case 8:return new F(function(){return _0(_2bl,_2bo);});break;case 9:return new F(function(){return _0(_2bk,_2bo);});break;case 10:return new F(function(){return _0(_2bj,_2bo);});break;case 11:return new F(function(){return _0(_2bi,_2bo);});break;case 12:return new F(function(){return _0(_2bh,_2bo);});break;case 13:return new F(function(){return _0(_2bg,_2bo);});break;case 14:return new F(function(){return _0(_2bf,new T(function(){var _2br=E(_2bo);if(!_2br._){return __Z;}else{if(E(_2br.a)==72){return B(unAppCStr("\\&",_2br));}else{return E(_2br);}}},1));});break;default:return new F(function(){return _0(new T2(1,_2bb,new T(function(){return B(_1Eb(_2ba,_2bq));})),_2bo);});}}else{return new T2(1,_2bp,_2bo);}}}else{var _2bs=new T(function(){var _2bt=jsShowI(_2bn);return B(_0(fromJSStr(_2bt),new T(function(){var _2bu=E(_2bo);if(!_2bu._){return __Z;}else{var _2bv=E(_2bu.a);if(_2bv<48){return E(_2bu);}else{if(_2bv>57){return E(_2bu);}else{return B(unAppCStr("\\&",_2bu));}}}},1)));});return new T2(1,_2bb,_2bs);}},_2bw=new T(function(){return B(unCStr("\\\""));}),_2bx=function(_2by,_2bz){var _2bA=E(_2by);if(!_2bA._){return E(_2bz);}else{var _2bB=_2bA.b,_2bC=E(_2bA.a);if(_2bC==34){return new F(function(){return _0(_2bw,new T(function(){return B(_2bx(_2bB,_2bz));},1));});}else{return new F(function(){return _2bm(_2bC,new T(function(){return B(_2bx(_2bB,_2bz));}));});}}},_2bD=34,_2bE=function(_2bF,_2bG){return new T2(1,_2bD,new T(function(){return B(_2bx(_2bF,new T2(1,_2bD,_2bG)));}));},_2bH=function(_2bI,_2bJ){var _2bK=E(_2bI),_2bL=new T(function(){return B(A3(_eg,_e6,new T2(1,function(_2bM){return new F(function(){return _e1(_2bK.a,_2bM);});},new T2(1,function(_2bN){return new F(function(){return _2bE(_2bK.b,_2bN);});},_4)),new T2(1,_bX,_2bJ)));});return new T2(1,_bY,_2bL);},_2bO=function(_){return new F(function(){return __app1(E(_1DT),"span");});},_2bP=new T(function(){return new T2(0,E(new T1(2,"class")),"path");}),_2bQ=new T2(1,_2bP,_4),_2bR=new T(function(){return B(_28U(_27F,_dh,_2bO,_2bQ));}),_2bS=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:81:7-21"));}),_2bT=new T6(0,_4l,_4m,_4,_2bS,_4l,_4l),_2bU=new T(function(){return B(_4d(_2bT));}),_2bV=new T(function(){return B(unCStr(" "));}),_2bW=new T(function(){return B(unCStr("linTree"));}),_2bX=new T(function(){return B(unCStr("Got blobdata"));}),_2bY=new T(function(){return B(unCStr("Foods.pgf"));}),_2bZ=new T(function(){return B(unAppCStr("Loaded pgf as Blob ",_2bY));}),_2c0=new T(function(){return new T2(0,E(new T1(2,"class")),"word");}),_2c1=new T2(1,_2c0,_4),_2c2=new T(function(){return B(_28U(_27F,_dh,_2bO,_2c1));}),_2c3=new T(function(){return new T2(0,E(new T1(2,"class")),"gap");}),_2c4=new T2(1,_2c3,_4),_2c5=new T(function(){return B(_28U(_27F,_dh,_2bO,_2c4));}),_2c6=function(_2c7){return E(E(_2c7).a);},_2c8=function(_2c9){return E(E(_2c9).b);},_2ca=function(_2cb){return E(E(_2cb).a);},_2cc=function(_){return new F(function(){return nMV(_4l);});},_2cd=new T(function(){return B(_z(_2cc));}),_2ce=function(_2cf){return E(E(_2cf).b);},_2cg=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_2ch=function(_2ci,_2cj,_2ck,_2cl,_2cm,_2cn){var _2co=B(_2c6(_2ci)),_2cp=B(_2z(_2co)),_2cq=new T(function(){return B(_6i(_2co));}),_2cr=new T(function(){return B(_27A(_2cp));}),_2cs=new T(function(){return B(A1(_2cj,_2cl));}),_2ct=new T(function(){return B(A2(_2ca,_2ck,_2cm));}),_2cu=function(_2cv){return new F(function(){return A1(_2cr,new T3(0,_2ct,_2cs,_2cv));});},_2cw=function(_2cx){var _2cy=new T(function(){var _2cz=new T(function(){var _2cA=__createJSFunc(2,function(_2cB,_){var _2cC=B(A2(E(_2cx),_2cB,_));return _D;}),_2cD=_2cA;return function(_){return new F(function(){return __app3(E(_2cg),E(_2cs),E(_2ct),_2cD);});};});return B(A1(_2cq,_2cz));});return new F(function(){return A3(_1V,_2cp,_2cy,_2cu);});},_2cE=new T(function(){var _2cF=new T(function(){return B(_6i(_2co));}),_2cG=function(_2cH){var _2cI=new T(function(){return B(A1(_2cF,function(_){var _=wMV(E(_2cd),new T1(1,_2cH));return new F(function(){return A(_2c8,[_2ck,_2cm,_2cH,_]);});}));});return new F(function(){return A3(_1V,_2cp,_2cI,_2cn);});};return B(A2(_2ce,_2ci,_2cG));});return new F(function(){return A3(_1V,_2cp,_2cE,_2cw);});},_2cJ=0,_2cK=function(_2cL){var _2cM=E(_2cL);return new F(function(){return _1UO(_2cM.a,_2cM.b,_2cM.c);});},_2cN=new T(function(){return B(err(_rk));}),_2cO=new T(function(){return B(err(_rm));}),_2cP=new T(function(){return B(unCStr("_"));}),_2cQ=92,_2cR=39,_2cS=function(_2cT){var _2cU=E(_2cT);if(!_2cU._){return __Z;}else{var _2cV=_2cU.b,_2cW=E(_2cU.a);switch(E(_2cW)){case 39:return __Z;case 92:var _2cX=E(_2cV);if(!_2cX._){return __Z;}else{var _2cY=_2cX.b;switch(E(_2cX.a)){case 39:return new T2(1,new T2(0,_2cR,_2cY),_4);case 92:return new T2(1,new T2(0,_2cQ,_2cY),_4);default:return __Z;}}break;default:return new T2(1,new T2(0,_2cW,_2cV),_4);}}},_2cZ=function(_2d0,_2d1){var _2d2=function(_2d3){var _2d4=E(_2d3);if(!_2d4._){return __Z;}else{var _2d5=E(_2d4.a);return new F(function(){return _0(B(_rr(B(A1(_2d1,_2d5.a)),_2d5.b)),new T(function(){return B(_2d2(_2d4.b));},1));});}};return function(_2d6){var _2d7=B(_2d2(B(A1(_2d0,_2d6))));return (_2d7._==0)?new T0(2):new T1(4,_2d7);};},_2d8=function(_2d9){return new T1(1,B(_2cZ(_2cS,_2d9)));},_2da=function(_2db,_2dc){var _2dd=new T(function(){var _2de=function(_2df){return new F(function(){return _2da(_2db,function(_2dg){return new F(function(){return A1(_2dc,new T2(1,_2df,_2dg));});});});};return B(A1(_2db,_2de));});return new F(function(){return _rB(B(A1(_2dc,_4)),_2dd);});},_2dh=function(_2di){var _2dj=function(_2dk){var _2dl=E(_2dk);if(!_2dl._){return __Z;}else{var _2dm=E(_2dl.a),_2dn=function(_2do){var _2dp=new T(function(){return B(A1(_2di,new T2(1,_2dm.a,_2do)));});return new T1(0,function(_2dq){return (E(_2dq)==39)?E(_2dp):new T0(2);});};return new F(function(){return _0(B(_rr(B(_2da(_2d8,_2dn)),_2dm.b)),new T(function(){return B(_2dj(_2dl.b));},1));});}},_2dr=function(_2ds){var _2dt=B(_2dj(B(_2cS(_2ds))));return (_2dt._==0)?new T0(2):new T1(4,_2dt);};return function(_2du){return (E(_2du)==39)?E(new T1(1,_2dr)):new T0(2);};},_2dv=function(_2dw){var _2dx=B(_1xU(B(_G(_1z8,B(_1za(_2dw))))));return new T3(0,_2dx.a,_2dx.b,_2dx.c);},_2dy=function(_2dz){return new F(function(){return _1Ut(E(_2dz));});},_2dA=function(_2dB){var _2dC=function(_2dD){if(!B(_sf(_2dD,_2cP))){return new F(function(){return A1(_2dB,new T(function(){return B(_2dv(_2dD));}));});}else{return new T0(2);}},_2dE=function(_2dF){var _2dG=E(_2dF);return (!B(_1U4(_2dG)))?new T0(2):new T1(1,B(_tk(_2dy,function(_2dH){return new F(function(){return _2dC(new T2(1,_2dG,_2dH));});})));};return new F(function(){return _rB(new T1(0,_2dE),new T(function(){return new T1(0,B(_2dh(_2dC)));}));});},_2dI=new T(function(){return B(_2dA(_sM));}),_2dJ=function(_2dK,_2dL){while(1){var _2dM=E(_2dK);if(!_2dM._){return E(_2dL);}else{_2dK=_2dM.b;_2dL=_2dM.a;continue;}}},_2dN=function(_2dO,_2dP){var _2dQ=new T(function(){var _2dR=B(_2dS(B(_1Zo(_2dO))));return new T2(0,_2dR.a,_2dR.b);});return new T2(0,new T2(1,new T(function(){return B(_1LP(_2dO));}),new T(function(){return B(_1LP(_2dQ));})),new T(function(){return B(_1Zo(_2dQ));}));},_2dS=function(_2dT){var _2dU=E(_2dT);if(!_2dU._){return new T2(0,_4,_4);}else{if(E(_2dU.a)==32){var _2dV=B(_2dW(_2dU.b));if(!_2dV._){return new T2(0,_4,_2dU);}else{return new F(function(){return _2dN(_2dV.a,_2dV.b);});}}else{var _2dX=B(_2dW(_2dU));if(!_2dX._){return new T2(0,_4,_2dU);}else{return new F(function(){return _2dN(_2dX.a,_2dX.b);});}}}},_2dY=new T(function(){return B(unCStr("?"));}),_2dZ=new T(function(){return B(_1za(_2dY));}),_2e0=new T(function(){return B(_G(_1z8,_2dZ));}),_2e1=new T(function(){var _2e2=B(_1xU(_2e0));return new T3(0,_2e2.a,_2e2.b,_2e2.c);}),_2e3=new T2(0,_2e1,_4),_2e4=new T1(1,_2e3),_2e5=new T(function(){return B(_rr(_2dI,_4));}),_2e6=function(_2e7){var _2e8=E(_2e7);if(!_2e8._){var _2e9=E(_2e5);return (_2e9._==0)?__Z:new T1(1,_2e9.a);}else{if(E(_2e8.a)==63){var _2ea=B(_2e6(_2e8.b));if(!_2ea._){return E(_2e4);}else{var _2eb=E(_2ea.a),_2ec=new T(function(){var _2ed=B(_1xU(B(_G(_1z8,B(_1za(B(unAppCStr("?",new T(function(){var _2ee=E(_2eb.a);return B(_1UO(_2ee.a,_2ee.b,_2ee.c));})))))))));return new T3(0,_2ed.a,_2ed.b,_2ed.c);});return new T1(1,new T2(0,_2ec,_2eb.b));}}else{var _2ef=B(_rr(_2dI,_2e8));return (_2ef._==0)?__Z:new T1(1,_2ef.a);}}},_2eg=function(_2eh){while(1){var _2ei=B((function(_2ej){var _2ek=E(_2ej);if(!_2ek._){return new T2(0,_4,_4);}else{var _2el=_2ek.b,_2em=function(_2en){var _2eo=B(_2e6(_2ek));if(!_2eo._){return new T2(0,_4,_2ek);}else{var _2ep=_2eo.a,_2eq=new T(function(){var _2er=B(_2eg(B(_1Zo(_2ep))));return new T2(0,_2er.a,_2er.b);});return new T2(0,new T2(1,new T(function(){return B(_1LP(_2ep));}),new T(function(){return B(_1LP(_2eq));})),new T(function(){return B(_1Zo(_2eq));}));}};switch(E(_2ek.a)){case 32:_2eh=_2el;return __continue;case 40:_2eh=_2el;return __continue;case 41:return new T2(0,_4,_2el);case 45:var _2es=E(_2el);if(!_2es._){return new F(function(){return _2em(_);});}else{if(E(_2es.a)==62){_2eh=_2es.b;return __continue;}else{return new F(function(){return _2em(_);});}}break;default:return new F(function(){return _2em(_);});}}})(_2eh));if(_2ei!=__continue){return _2ei;}}},_2et=new T(function(){return B(unCStr("?"));}),_2eu=function(_2ev){var _2ew=E(_2ev);if(!_2ew._){var _2ex=E(_2ew.b);if(!_2ex._){return E(_2ex.a);}else{return new F(function(){return _2dv(_2et);});}}else{return E(_2ew.a);}},_2ey=new T(function(){return B(_1za(_2et));}),_2ez=new T(function(){return B(_G(_1z8,_2ey));}),_2eA=new T(function(){var _2eB=B(_1xU(_2ez));return new T3(0,_2eB.a,_2eB.b,_2eB.c);}),_2eC=new T2(0,_2eA,_4),_2eD=function(_2eE){var _2eF=E(_2eE);if(!_2eF._){var _2eG=_2eF.c,_2eH=new T(function(){var _2eI=E(_2eF.b);if(!_2eI._){if(!E(_2eI.b)._){return new T2(0,_2eI.a,new T(function(){return B(_G(_2eu,_2eG));}));}else{return E(_2eI);}}else{return E(_2eC);}});return new T3(0,_2eF.a,_2eH,new T(function(){return B(_G(_2eD,_2eG));}));}else{return E(_2eF);}},_2eJ=function(_2eK,_2eL){var _2eM=E(_2eL);return (_2eM._==0)?__Z:new T2(1,_2eK,new T(function(){return B(_2eJ(_2eM.a,_2eM.b));}));},_2eN=new T(function(){return B(unCStr("last"));}),_2eO=new T(function(){return B(_ec(_2eN));}),_2eP=function(_2eQ){var _2eR=E(_2eQ);return new T2(0,new T1(1,_2eR.a),new T(function(){var _2eS=E(_2eR.b);if(!_2eS._){return __Z;}else{if(E(_2eS.a)==125){return E(_2eS.b);}else{return E(_2eS);}}}));},_2dW=function(_2eT){var _2eU=E(_2eT);if(!_2eU._){var _2eV=__Z;}else{if(E(_2eU.a)==123){var _2eW=E(_2eU.b);}else{var _2eW=E(_2eU);}var _2eV=_2eW;}var _2eX=function(_2eY){var _2eZ=B(_2e6(_2eV));if(!_2eZ._){return __Z;}else{var _2f0=E(_2eZ.a),_2f1=function(_2f2){var _2f3=new T(function(){var _2f4=E(E(_2f2).b);if(!_2f4._){var _2f5=B(_2dS(_4));return new T2(0,_2f5.a,_2f5.b);}else{var _2f6=_2f4.b;switch(E(_2f4.a)){case 32:var _2f7=E(_2f6);if(!_2f7._){var _2f8=B(_2dS(_4));return new T2(0,_2f8.a,_2f8.b);}else{if(E(_2f7.a)==123){var _2f9=B(_2dS(_2f7.b));return new T2(0,_2f9.a,_2f9.b);}else{var _2fa=B(_2dS(_2f7));return new T2(0,_2fa.a,_2fa.b);}}break;case 123:var _2fb=B(_2dS(_2f6));return new T2(0,_2fb.a,_2fb.b);break;default:var _2fc=B(_2dS(_2f4));return new T2(0,_2fc.a,_2fc.b);}}}),_2fd=new T(function(){return B(_2eD(new T3(0,_2f0.a,new T(function(){return B(_1LP(_2f2));}),new T(function(){return B(_1LP(_2f3));}))));});return new T2(1,new T2(0,_2fd,new T(function(){var _2fe=E(E(_2f3).b);if(!_2fe._){return __Z;}else{if(E(_2fe.a)==125){return E(_2fe.b);}else{return E(_2fe);}}})),_4);},_2ff=E(_2f0.b);if(!_2ff._){var _2fg=B(_2eg(_4)),_2fh=E(_2fg.a);if(!_2fh._){return __Z;}else{return new F(function(){return _2f1(new T2(0,new T2(0,new T(function(){return B(_2dJ(_2fh,_2eO));}),new T(function(){return B(_2eJ(_2fh.a,_2fh.b));})),_2fg.b));});}}else{if(E(_2ff.a)==58){var _2fi=B(_2eg(_2ff.b)),_2fj=E(_2fi.a);if(!_2fj._){return __Z;}else{return new F(function(){return _2f1(new T2(0,new T2(0,new T(function(){return B(_2dJ(_2fj,_2eO));}),new T(function(){return B(_2eJ(_2fj.a,_2fj.b));})),_2fi.b));});}}else{var _2fk=B(_2eg(_2ff)),_2fl=E(_2fk.a);if(!_2fl._){return __Z;}else{return new F(function(){return _2f1(new T2(0,new T2(0,new T(function(){return B(_2dJ(_2fl,_2eO));}),new T(function(){return B(_2eJ(_2fl.a,_2fl.b));})),_2fk.b));});}}}}},_2fm=E(_2eV);if(!_2fm._){return new F(function(){return _2eX(_);});}else{if(E(_2fm.a)==63){return new F(function(){return _G(_2eP,B(_rr(_2dI,_2fm.b)));});}else{return new F(function(){return _2eX(_);});}}},_2fn=function(_2fo){var _2fp=E(_2fo);if(!_2fp._){return __Z;}else{var _2fq=E(_2fp.a),_2fr=function(_2fs){return E(new T2(3,_2fq.a,_sL));};return new F(function(){return _0(B(_rr(new T1(1,function(_2ft){return new F(function(){return A2(_By,_2ft,_2fr);});}),_2fq.b)),new T(function(){return B(_2fn(_2fp.b));},1));});}},_2fu=function(_2fv){var _2fw=B(_2fn(B(_2dW(_2fv))));return (_2fw._==0)?new T0(2):new T1(4,_2fw);},_2fx=new T1(1,_2fu),_2fy=new T(function(){return B(unCStr("{Pred:(Item->Quality->Comment) {This:(Kind->Item) {Pizza:Kind}} {Very:(Quality->Quality) {Italian:Quality}}}"));}),_2fz=new T(function(){return B(_rr(_2fx,_2fy));}),_2fA=new T(function(){var _2fB=B(_It(_2fz));if(!_2fB._){return E(_2cN);}else{if(!E(_2fB.b)._){return E(_2fB.a);}else{return E(_2cO);}}}),_2fC=new T2(0,_2fA,_ML),_2fD=function(_2fE){var _2fF=E(_2fE);if(!_2fF._){return E(_2a6);}else{var _2fG=function(_){var _2fH=E(_297),_2fI=__app1(_2fH,toJSStr(E(_2bZ)));return new T(function(){var _2fJ=function(_2fK){var _2fL=function(_){var _2fM=__app1(_2fH,toJSStr(E(_2bX))),_2fN=new T(function(){var _2fO=E(_2fK),_2fP=B(_1DK(_bP,_2fO.a,_2fO.b,_2fO.c)),_2fQ=E(_2fP.a);return E(B(_1BJ(_2fQ,(E(_2fP.b)-_2fQ|0)+1|0,_2fP,_2cJ)).a);}),_2fR=function(_){var _2fS=__app1(_2fH,toJSStr(B(unAppCStr("Loaded ",new T(function(){return B(_2cK(E(_2fN).b));}))))),_2fT=function(_){var _2fU=new T(function(){var _2fV=E(_2fN),_2fW=E(_2fV.b),_2fX=B(_1Dc(_2fV.a,_2fW.a,_2fW.b,_2fW.c,_2fV.c,_2fV.d));return new T3(0,_2fX.a,_2fX.b,_2fX.c);}),_2fY=new T(function(){return B(_2a1(_Lu,E(_2fN).d));}),_2fZ=B(_24s(_2fU,_2fY,_2fC)),_2g0=__app1(_2fH,toJSStr(B(_3X(_2bH,_2fZ,_4)))),_2g1=__app1(E(_1DZ),toJSStr(E(_2bW))),_2g2=__eq(_2g1,E(_D)),_2g3=function(_,_2g4){var _2g5=E(_2g4);if(!_2g5._){return new F(function(){return die(_2bU);});}else{var _2g6=function(_2g7,_){while(1){var _2g8=B((function(_2g9,_){var _2ga=E(_2g9);if(!_2ga._){return _5;}else{var _2gb=E(_2ga.a),_2gc=_2gb.a,_2gd=B(A1(_2c5,_)),_2ge=E(_296),_2gf=__app1(_2ge,toJSStr(E(_2bV))),_2gg=E(_2gd),_2gh=E(_1DU),_2gi=__app2(_2gh,_2gf,_2gg),_2gj=B(A(_2ch,[_di,_df,_de,_2gg,_1DS,function(_2gk,_){return new F(function(){return _298(_2fU,_2fY,_2fC,_2gc,_w8,_2gk,_);});},_])),_2gl=E(_2g5.a),_2gm=__app2(_2gh,_2gg,_2gl),_2gn=B(A1(_2c2,_)),_2go=__app1(_2ge,toJSStr(E(_2gb.b))),_2gp=E(_2gn),_2gq=__app2(_2gh,_2go,_2gp),_2gr=B(A(_2ch,[_di,_df,_de,_2gp,_1DS,function(_2gk,_){return new F(function(){return _298(_2fU,_2fY,_2fC,_2gc,_w7,_2gk,_);});},_])),_2gs=__app2(_2gh,_2gp,_2gl),_2gt=B(A1(_2bR,_)),_2gu=__app1(_2ge,toJSStr(B(_3X(_dY,_2gc,_4)))),_2gv=E(_2gt),_2gw=__app2(_2gh,_2gu,_2gv),_2gx=__app2(_2gh,_2gv,_2gl);_2g7=_2ga.b;return __continue;}})(_2g7,_));if(_2g8!=__continue){return _2g8;}}},_2gy=B(_2g6(_2fZ,_));return _7q;}};if(!E(_2g2)){var _2gz=__isUndef(_2g1);if(!E(_2gz)){return new F(function(){return _2g3(_,new T1(1,_2g1));});}else{return new F(function(){return _2g3(_,_4l);});}}else{return new F(function(){return _2g3(_,_4l);});}};return new T1(0,_2fT);};return new T1(0,_2fR);};return new T1(0,_2fL);};return B(A3(_29M,_2l,_2fF.a,_2fJ));});};return new T1(0,_2fG);}},_2gA=new T(function(){return toJSStr(E(_2bY));}),_2gB=new T(function(){return B(A(_7Y,[_2l,_N,_1b,_i,_h,_2gA,_2fD]));}),_2gC=function(_){var _2gD=B(_c(_2gB,_4,_));return _5;},_2gE=function(_){return new F(function(){return _2gC(_);});};
var hasteMain = function() {B(A(_2gE, [0]));};window.onload = hasteMain;