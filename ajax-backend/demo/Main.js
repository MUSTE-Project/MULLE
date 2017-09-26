"use strict";
var __haste_prog_id = 'f02691c483e8817598ed533c56a94866a46c9787eb343ce3dd59c94028a38ad7';
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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return _0(_3.b,_2);}));},_4=function(_5,_){while(1){var _6=E(_5);if(!_6._){return 0;}else{var _7=_6.b,_8=E(_6.a);switch(_8._){case 0:var _9=B(A1(_8.a,_));_5=_0(_7,new T2(1,_9,__Z));continue;case 1:_5=_0(_7,_8.a);continue;default:_5=_7;continue;}}}},_a=function(_b,_c,_){var _d=E(_b);switch(_d._){case 0:var _e=B(A1(_d.a,_));return _4(_0(_c,new T2(1,_e,__Z)),_);case 1:return _4(_0(_c,_d.a),_);default:return _4(_c,_);}},_f=new T(function(){return toJSStr(__Z);}),_g=function(_h){return E(_f);},_i=function(_j,_){var _k=E(_j);if(!_k._){return __Z;}else{var _l=_i(_k.b,_);return new T2(1,new T(function(){return String(E(_k.a));}),_l);}},_m=function(_n,_){var _o=__arr2lst(0,_n);return _i(_o,_);},_p=function(_q){return String(E(_q));},_r=function(_s){return _p(_s);},_t=function(_u,_){return new T(function(){return _r(_u);});},_v=new T4(0,new T2(0,function(_w){return E(_w);},function(_x){return __lst2arr(E(_x));}),new T2(0,_t,function(_y,_){return _m(E(_y),_);}),_g,_g),_z=function(_A,_B,_C){var _D=function(_E){var _F=new T(function(){return B(A1(_C,_E));});return C > 19 ? new F(function(){return A1(_B,function(_G){return E(_F);});}) : (++C,A1(_B,function(_G){return E(_F);}));};return C > 19 ? new F(function(){return A1(_A,_D);}) : (++C,A1(_A,_D));},_H=function(_I,_J,_K){var _L=new T(function(){return B(A1(_J,function(_M){return C > 19 ? new F(function(){return A1(_K,_M);}) : (++C,A1(_K,_M));}));});return C > 19 ? new F(function(){return A1(_I,function(_N){return E(_L);});}) : (++C,A1(_I,function(_N){return E(_L);}));},_O=function(_P,_Q,_R){var _S=function(_T){var _U=function(_V){return C > 19 ? new F(function(){return A1(_R,new T(function(){return B(A1(_T,_V));}));}) : (++C,A1(_R,new T(function(){return B(A1(_T,_V));})));};return C > 19 ? new F(function(){return A1(_Q,_U);}) : (++C,A1(_Q,_U));};return C > 19 ? new F(function(){return A1(_P,_S);}) : (++C,A1(_P,_S));},_W=function(_X,_Y){return C > 19 ? new F(function(){return A1(_Y,_X);}) : (++C,A1(_Y,_X));},_Z=function(_10,_11,_12){var _13=new T(function(){return B(A1(_12,_10));});return C > 19 ? new F(function(){return A1(_11,function(_14){return E(_13);});}) : (++C,A1(_11,function(_14){return E(_13);}));},_15=function(_16,_17,_18){var _19=function(_1a){return C > 19 ? new F(function(){return A1(_18,new T(function(){return B(A1(_16,_1a));}));}) : (++C,A1(_18,new T(function(){return B(A1(_16,_1a));})));};return C > 19 ? new F(function(){return A1(_17,_19);}) : (++C,A1(_17,_19));},_1b=function(_1c,_1d,_1e){return C > 19 ? new F(function(){return A1(_1c,function(_1f){return C > 19 ? new F(function(){return A2(_1d,_1f,_1e);}) : (++C,A2(_1d,_1f,_1e));});}) : (++C,A1(_1c,function(_1f){return C > 19 ? new F(function(){return A2(_1d,_1f,_1e);}) : (++C,A2(_1d,_1f,_1e));}));},_1g=function(_1h){return E(E(_1h).b);},_1i=function(_1j,_1k){return C > 19 ? new F(function(){return A3(_1g,_1l,_1j,function(_1m){return E(_1k);});}) : (++C,A3(_1g,_1l,_1j,function(_1m){return E(_1k);}));},_1l=new T(function(){return new T5(0,new T5(0,new T2(0,_15,_Z),_W,_O,_H,_z),_1b,_1i,_W,function(_1n){return err(_1n);});}),_1o=function(_1p,_1q,_){var _1r=B(A1(_1q,_));return new T(function(){return B(A1(_1p,_1r));});},_1s=function(_1t,_1u){return new T1(0,function(_){return _1o(_1u,_1t,_);});},_1v=function(_1w){return new T0(2);},_1x=function(_1y){var _1z=new T(function(){return B(A1(_1y,_1v));}),_1A=function(_1B){return new T1(1,new T2(1,new T(function(){return B(A1(_1B,0));}),new T2(1,_1z,__Z)));};return _1A;},_1C=function(_1D){return E(_1D);},_1E=new T3(0,new T2(0,_1l,_1s),_1C,_1x),_1F=function(_1G){return E(E(_1G).a);},_1H=function(_1I,_1J){var _1K=strEq(E(_1I),E(_1J));return (E(_1K)==0)?false:true;},_1L=new T(function(){return new T2(0,function(_1M,_1N){return _1H(_1M,_1N);},function(_1O,_1P){return (!B(A3(_1F,_1L,_1O,_1P)))?true:false;});}),_1Q=function(_1R,_1S){if(_1R<=_1S){var _1T=function(_1U){return new T2(1,_1U,new T(function(){if(_1U!=_1S){return _1T(_1U+1|0);}else{return __Z;}}));};return _1T(_1R);}else{return __Z;}},_1V=function(_1W,_1X,_1Y){if(_1Y<=_1X){var _1Z=new T(function(){var _20=_1X-_1W|0,_21=function(_22){return (_22>=(_1Y-_20|0))?new T2(1,_22,new T(function(){return _21(_22+_20|0);})):new T2(1,_22,__Z);};return _21(_1X);});return new T2(1,_1W,_1Z);}else{return (_1Y<=_1W)?new T2(1,_1W,__Z):__Z;}},_23=function(_24,_25,_26){if(_26>=_25){var _27=new T(function(){var _28=_25-_24|0,_29=function(_2a){return (_2a<=(_26-_28|0))?new T2(1,_2a,new T(function(){return _29(_2a+_28|0);})):new T2(1,_2a,__Z);};return _29(_25);});return new T2(1,_24,_27);}else{return (_26>=_24)?new T2(1,_24,__Z):__Z;}},_2b=function(_2c,_2d){if(_2d<_2c){return _1V(_2c,_2d,-2147483648);}else{return _23(_2c,_2d,2147483647);}},_2e=function(_2f,_2g,_2h){if(_2g<_2f){return _1V(_2f,_2g,_2h);}else{return _23(_2f,_2g,_2h);}},_2i=function(_2j){return E(_2j);},_2k=new T(function(){return err(new T(function(){return unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound");}));}),_2l=new T(function(){return err(new T(function(){return unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound");}));}),_2m=function(_2n,_2o){if(_2n<=0){if(_2n>=0){return quot(_2n,_2o);}else{if(_2o<=0){return quot(_2n,_2o);}else{return quot(_2n+1|0,_2o)-1|0;}}}else{if(_2o>=0){if(_2n>=0){return quot(_2n,_2o);}else{if(_2o<=0){return quot(_2n,_2o);}else{return quot(_2n+1|0,_2o)-1|0;}}}else{return quot(_2n-1|0,_2o)-1|0;}}},_2p=new T(function(){return unCStr("base");}),_2q=new T(function(){return unCStr("GHC.Exception");}),_2r=new T(function(){return unCStr("ArithException");}),_2s=function(_2t){return E(new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_2p,_2q,_2r),__Z,__Z));},_2u=function(_2v){return E(E(_2v).a);},_2w=function(_2x,_2y,_2z){var _2A=B(A1(_2x,_)),_2B=B(A1(_2y,_)),_2C=hs_eqWord64(_2A.a,_2B.a);if(!_2C){return __Z;}else{var _2D=hs_eqWord64(_2A.b,_2B.b);return (!_2D)?__Z:new T1(1,_2z);}},_2E=new T(function(){return unCStr("Ratio has zero denominator");}),_2F=new T(function(){return unCStr("denormal");}),_2G=new T(function(){return unCStr("divide by zero");}),_2H=new T(function(){return unCStr("loss of precision");}),_2I=new T(function(){return unCStr("arithmetic underflow");}),_2J=new T(function(){return unCStr("arithmetic overflow");}),_2K=function(_2L,_2M){switch(E(_2L)){case 0:return _0(_2J,_2M);case 1:return _0(_2I,_2M);case 2:return _0(_2H,_2M);case 3:return _0(_2G,_2M);case 4:return _0(_2F,_2M);default:return _0(_2E,_2M);}},_2N=function(_2O){return _2K(_2O,__Z);},_2P=function(_2Q,_2R,_2S){var _2T=E(_2R);if(!_2T._){return unAppCStr("[]",_2S);}else{var _2U=new T(function(){var _2V=new T(function(){var _2W=function(_2X){var _2Y=E(_2X);if(!_2Y._){return E(new T2(1,93,_2S));}else{var _2Z=new T(function(){return B(A2(_2Q,_2Y.a,new T(function(){return _2W(_2Y.b);})));});return new T2(1,44,_2Z);}};return _2W(_2T.b);});return B(A2(_2Q,_2T.a,_2V));});return new T2(1,91,_2U);}},_30=new T(function(){return new T5(0,_2s,new T3(0,function(_31,_32,_33){return _2K(_32,_33);},_2N,function(_34,_35){return _2P(_2K,_34,_35);}),_36,function(_37){var _38=E(_37);return _2w(_2u(_38.a),_2s,_38.b);},_2N);}),_36=function(_39){return new T2(0,_30,_39);},_3a=new T(function(){return die(new T(function(){return _36(3);}));}),_3b=new T(function(){return die(new T(function(){return _36(0);}));}),_3c=function(_3d,_3e){var _3f=E(_3e);switch(_3f){case -1:var _3g=E(_3d);if(_3g==(-2147483648)){return E(_3b);}else{return _2m(_3g,-1);}break;case 0:return E(_3a);default:return _2m(_3d,_3f);}},_3h=new T2(0,_3b,0),_3i=function(_3j,_3k){var _3l=_3j%_3k;if(_3j<=0){if(_3j>=0){return _3l;}else{if(_3k<=0){return _3l;}else{return (_3l==0)?0:_3l+_3k|0;}}}else{if(_3k>=0){if(_3j>=0){return _3l;}else{if(_3k<=0){return _3l;}else{return (_3l==0)?0:_3l+_3k|0;}}}else{return (_3l==0)?0:_3l+_3k|0;}}},_3m=function(_3n){return new T1(0,_3n);},_3o=new T1(0,1),_3p=function(_3q){var _3r=E(_3q);if(!_3r._){return E(_3r.a);}else{return I_toInt(_3r.a);}},_3s=new T2(0,function(_3t,_3u){return E(_3t)==E(_3u);},function(_3v,_3w){return E(_3v)!=E(_3w);}),_3x=function(_3y,_3z){return (_3y>=_3z)?(_3y!=_3z)?2:1:0;},_3A={_:0,a:new T3(0,{_:0,a:function(_3B,_3C){return E(_3B)+E(_3C)|0;},b:function(_3D,_3E){return E(_3D)-E(_3E)|0;},c:function(_3F,_3G){return imul(E(_3F),E(_3G))|0;},d:function(_3H){return  -E(_3H);},e:function(_3I){var _3J=E(_3I);return (_3J<0)? -_3J:_3J;},f:function(_3K){var _3L=E(_3K);return (_3L>=0)?(_3L==0)?0:1:-1;},g:function(_3M){return _3p(_3M);}},{_:0,a:_3s,b:function(_3N,_3O){return _3x(E(_3N),E(_3O));},c:function(_3P,_3Q){return E(_3P)<E(_3Q);},d:function(_3R,_3S){return E(_3R)<=E(_3S);},e:function(_3T,_3U){return E(_3T)>E(_3U);},f:function(_3V,_3W){return E(_3V)>=E(_3W);},g:function(_3X,_3Y){var _3Z=E(_3X),_40=E(_3Y);return (_3Z>_40)?_3Z:_40;},h:function(_41,_42){var _43=E(_41),_44=E(_42);return (_43>_44)?_44:_43;}},function(_45){return new T2(0,E(_3m(E(_45))),E(_3o));}),b:{_:0,a:function(_46){var _47=E(_46);return (_47==2147483647)?E(_2l):_47+1|0;},b:function(_48){var _49=E(_48);return (_49==(-2147483648))?E(_2k):_49-1|0;},c:_2i,d:_2i,e:function(_4a){return _1Q(E(_4a),2147483647);},f:function(_4b,_4c){return _2b(E(_4b),E(_4c));},g:function(_4d,_4e){return _1Q(E(_4d),E(_4e));},h:function(_4f,_4g,_4h){return _2e(E(_4f),E(_4g),E(_4h));}},c:function(_4i,_4j){var _4k=E(_4i),_4l=E(_4j);switch(_4l){case -1:if(_4k==(-2147483648)){return E(_3b);}else{return quot(_4k,-1);}break;case 0:return E(_3a);default:return quot(_4k,_4l);}},d:function(_4m,_4n){var _4o=E(_4n);switch(_4o){case -1:return 0;case 0:return E(_3a);default:return E(_4m)%_4o;}},e:function(_4p,_4q){return _3c(E(_4p),E(_4q));},f:function(_4r,_4s){var _4t=E(_4s);switch(_4t){case -1:return 0;case 0:return E(_3a);default:return _3i(E(_4r),_4t);}},g:function(_4u,_4v){var _4w=E(_4u),_4x=E(_4v);switch(_4x){case -1:if(_4w==(-2147483648)){return E(_3h);}else{var _4y=quotRemI(_4w,-1);return new T2(0,_4y.a,_4y.b);}break;case 0:return E(_3a);default:var _4z=quotRemI(_4w,_4x);return new T2(0,_4z.a,_4z.b);}},h:function(_4A,_4B){var _4C=E(_4A),_4D=E(_4B);switch(_4D){case -1:if(_4C==(-2147483648)){return E(_3h);}else{if(_4C<=0){if(_4C>=0){var _4E=quotRemI(_4C,-1);return new T2(0,_4E.a,_4E.b);}else{var _4F=quotRemI(_4C,-1);return new T2(0,_4F.a,_4F.b);}}else{var _4G=quotRemI(_4C-1|0,-1);return new T2(0,_4G.a-1|0,(_4G.b+(-1)|0)+1|0);}}break;case 0:return E(_3a);default:if(_4C<=0){if(_4C>=0){var _4H=quotRemI(_4C,_4D);return new T2(0,_4H.a,_4H.b);}else{if(_4D<=0){var _4I=quotRemI(_4C,_4D);return new T2(0,_4I.a,_4I.b);}else{var _4J=quotRemI(_4C+1|0,_4D);return new T2(0,_4J.a-1|0,(_4J.b+_4D|0)-1|0);}}}else{if(_4D>=0){if(_4C>=0){var _4K=quotRemI(_4C,_4D);return new T2(0,_4K.a,_4K.b);}else{if(_4D<=0){var _4L=quotRemI(_4C,_4D);return new T2(0,_4L.a,_4L.b);}else{var _4M=quotRemI(_4C+1|0,_4D);return new T2(0,_4M.a-1|0,(_4M.b+_4D|0)-1|0);}}}else{var _4N=quotRemI(_4C-1|0,_4D);return new T2(0,_4N.a-1|0,(_4N.b+_4D|0)+1|0);}}}},i:function(_4O){return _3m(E(_4O));}},_4P=new T1(0,2),_4Q=function(_4R){return E(E(_4R).a);},_4S=function(_4T){return E(E(_4T).a);},_4U=function(_4V,_4W){while(1){var _4X=E(_4V);if(!_4X._){var _4Y=_4X.a,_4Z=E(_4W);if(!_4Z._){var _50=_4Z.a;if(!(imul(_4Y,_50)|0)){return new T1(0,imul(_4Y,_50)|0);}else{_4V=new T1(1,I_fromInt(_4Y));_4W=new T1(1,I_fromInt(_50));continue;}}else{_4V=new T1(1,I_fromInt(_4Y));_4W=_4Z;continue;}}else{var _51=E(_4W);if(!_51._){_4V=_4X;_4W=new T1(1,I_fromInt(_51.a));continue;}else{return new T1(1,I_mul(_4X.a,_51.a));}}}},_52=function(_53,_54,_55){while(1){if(!(_54%2)){var _56=_4U(_53,_53),_57=quot(_54,2);_53=_56;_54=_57;continue;}else{var _58=E(_54);if(_58==1){return _4U(_53,_55);}else{var _56=_4U(_53,_53),_59=_4U(_53,_55);_53=_56;_54=quot(_58-1|0,2);_55=_59;continue;}}}},_5a=function(_5b,_5c){while(1){if(!(_5c%2)){var _5d=_4U(_5b,_5b),_5e=quot(_5c,2);_5b=_5d;_5c=_5e;continue;}else{var _5f=E(_5c);if(_5f==1){return E(_5b);}else{return _52(_4U(_5b,_5b),quot(_5f-1|0,2),_5b);}}}},_5g=function(_5h){return E(E(_5h).c);},_5i=function(_5j){return E(E(_5j).a);},_5k=function(_5l){return E(E(_5l).b);},_5m=function(_5n){return E(E(_5n).b);},_5o=function(_5p){return E(E(_5p).c);},_5q=new T1(0,0),_5r=new T1(0,2),_5s=function(_5t){return E(E(_5t).g);},_5u=function(_5v){return E(E(_5v).d);},_5w=function(_5x,_5y){var _5z=_4Q(_5x),_5A=new T(function(){return _4S(_5z);}),_5B=new T(function(){return B(A3(_5u,_5x,_5y,new T(function(){return B(A2(_5s,_5A,_5r));})));});return C > 19 ? new F(function(){return A3(_1F,_5i(_5k(_5z)),_5B,new T(function(){return B(A2(_5s,_5A,_5q));}));}) : (++C,A3(_1F,_5i(_5k(_5z)),_5B,new T(function(){return B(A2(_5s,_5A,_5q));})));},_5C=new T(function(){return unCStr("Negative exponent");}),_5D=new T(function(){return err(_5C);}),_5E=function(_5F){return E(E(_5F).c);},_5G=function(_5H,_5I,_5J,_5K){var _5L=_4Q(_5I),_5M=new T(function(){return _4S(_5L);}),_5N=_5k(_5L);if(!B(A3(_5o,_5N,_5K,new T(function(){return B(A2(_5s,_5M,_5q));})))){if(!B(A3(_1F,_5i(_5N),_5K,new T(function(){return B(A2(_5s,_5M,_5q));})))){var _5O=new T(function(){return B(A2(_5s,_5M,_5r));}),_5P=new T(function(){return B(A2(_5s,_5M,_3o));}),_5Q=_5i(_5N),_5R=function(_5S,_5T,_5U){while(1){var _5V=B((function(_5W,_5X,_5Y){if(!B(_5w(_5I,_5X))){if(!B(A3(_1F,_5Q,_5X,_5P))){var _5Z=new T(function(){return B(A3(_5E,_5I,new T(function(){return B(A3(_5m,_5M,_5X,_5P));}),_5O));});_5S=new T(function(){return B(A3(_5g,_5H,_5W,_5W));});_5T=_5Z;_5U=new T(function(){return B(A3(_5g,_5H,_5W,_5Y));});return __continue;}else{return C > 19 ? new F(function(){return A3(_5g,_5H,_5W,_5Y);}) : (++C,A3(_5g,_5H,_5W,_5Y));}}else{var _60=_5Y;_5S=new T(function(){return B(A3(_5g,_5H,_5W,_5W));});_5T=new T(function(){return B(A3(_5E,_5I,_5X,_5O));});_5U=_60;return __continue;}})(_5S,_5T,_5U));if(_5V!=__continue){return _5V;}}},_61=function(_62,_63){while(1){var _64=(function(_65,_66){if(!B(_5w(_5I,_66))){if(!B(A3(_1F,_5Q,_66,_5P))){var _67=new T(function(){return B(A3(_5E,_5I,new T(function(){return B(A3(_5m,_5M,_66,_5P));}),_5O));});return _5R(new T(function(){return B(A3(_5g,_5H,_65,_65));}),_67,_65);}else{return E(_65);}}else{_62=new T(function(){return B(A3(_5g,_5H,_65,_65));});_63=new T(function(){return B(A3(_5E,_5I,_66,_5O));});return __continue;}})(_62,_63);if(_64!=__continue){return _64;}}};return _61(_5J,_5K);}else{return C > 19 ? new F(function(){return A2(_5s,_5H,_3o);}) : (++C,A2(_5s,_5H,_3o));}}else{return E(_5D);}},_68=new T(function(){return err(_5C);}),_69=function(_6a){var _6b=I_decodeDouble(_6a);return new T2(0,new T1(1,_6b.b),_6b.a);},_6c=function(_6d,_6e){var _6f=E(_6d);return (_6f._==0)?_6f.a*Math.pow(2,_6e):I_toNumber(_6f.a)*Math.pow(2,_6e);},_6g=function(_6h,_6i){var _6j=E(_6h);if(!_6j._){var _6k=_6j.a,_6l=E(_6i);return (_6l._==0)?_6k==_6l.a:(I_compareInt(_6l.a,_6k)==0)?true:false;}else{var _6m=_6j.a,_6n=E(_6i);return (_6n._==0)?(I_compareInt(_6m,_6n.a)==0)?true:false:(I_compare(_6m,_6n.a)==0)?true:false;}},_6o=function(_6p,_6q){while(1){var _6r=E(_6p);if(!_6r._){var _6s=E(_6r.a);if(_6s==(-2147483648)){_6p=new T1(1,I_fromInt(-2147483648));continue;}else{var _6t=E(_6q);if(!_6t._){var _6u=_6t.a;return new T2(0,new T1(0,quot(_6s,_6u)),new T1(0,_6s%_6u));}else{_6p=new T1(1,I_fromInt(_6s));_6q=_6t;continue;}}}else{var _6v=E(_6q);if(!_6v._){_6p=_6r;_6q=new T1(1,I_fromInt(_6v.a));continue;}else{var _6w=I_quotRem(_6r.a,_6v.a);return new T2(0,new T1(1,_6w.a),new T1(1,_6w.b));}}}},_6x=function(_6y,_6z){var _6A=_69(_6z),_6B=_6A.a,_6C=_6A.b,_6D=new T(function(){return _4S(new T(function(){return _4Q(_6y);}));});if(_6C<0){var _6E= -_6C;if(_6E>=0){if(!_6E){var _6F=E(_3o);}else{var _6F=_5a(_4P,_6E);}if(!_6g(_6F,new T1(0,0))){var _6G=_6o(_6B,_6F);return new T2(0,new T(function(){return B(A2(_5s,_6D,_6G.a));}),new T(function(){return _6c(_6G.b,_6C);}));}else{return E(_3a);}}else{return E(_68);}}else{var _6H=new T(function(){var _6I=new T(function(){return B(_5G(_6D,_3A,new T(function(){return B(A2(_5s,_6D,_4P));}),_6C));});return B(A3(_5g,_6D,new T(function(){return B(A2(_5s,_6D,_6B));}),_6I));});return new T2(0,_6H,0);}},_6J=function(_){return 0;},_6K=(function(x){console.log(x);}),_6L=function(_){var _6M=_6K("Error decoding message data");return _6J(_);},_6N=function(_6O,_6P){while(1){var _6Q=E(_6O);if(!_6Q._){return (E(_6P)._==0)?1:0;}else{var _6R=E(_6P);if(!_6R._){return 2;}else{var _6S=E(_6Q.a),_6T=E(_6R.a);if(_6S>=_6T){if(_6S!=_6T){return 2;}else{_6O=_6Q.b;_6P=_6R.b;continue;}}else{return 0;}}}}},_6U=new T0(1),_6V=new T(function(){return unCStr("Failure in Data.Map.balanceL");}),_6W=new T(function(){var _6X=_;return err(_6V);}),_6Y=function(_6Z,_70,_71,_72){var _73=E(_72);if(!_73._){var _74=_73.a,_75=E(_71);if(!_75._){var _76=_75.a,_77=_75.b,_78=_75.c;if(_76<=(imul(3,_74)|0)){return new T5(0,(1+_76|0)+_74|0,E(_6Z),_70,_75,_73);}else{var _79=E(_75.d);if(!_79._){var _7a=_79.a,_7b=E(_75.e);if(!_7b._){var _7c=_7b.a,_7d=_7b.b,_7e=_7b.c,_7f=_7b.d;if(_7c>=(imul(2,_7a)|0)){var _7g=function(_7h){var _7i=E(_7b.e);return (_7i._==0)?new T5(0,(1+_76|0)+_74|0,E(_7d),_7e,E(new T5(0,(1+_7a|0)+_7h|0,E(_77),_78,_79,E(_7f))),E(new T5(0,(1+_74|0)+_7i.a|0,E(_6Z),_70,_7i,_73))):new T5(0,(1+_76|0)+_74|0,E(_7d),_7e,E(new T5(0,(1+_7a|0)+_7h|0,E(_77),_78,_79,E(_7f))),E(new T5(0,1+_74|0,E(_6Z),_70,E(_6U),_73)));},_7j=E(_7f);if(!_7j._){return _7g(_7j.a);}else{return _7g(0);}}else{return new T5(0,(1+_76|0)+_74|0,E(_77),_78,_79,E(new T5(0,(1+_74|0)+_7c|0,E(_6Z),_70,_7b,_73)));}}else{return E(_6W);}}else{return E(_6W);}}}else{return new T5(0,1+_74|0,E(_6Z),_70,E(_6U),_73);}}else{var _7k=E(_71);if(!_7k._){var _7l=_7k.a,_7m=_7k.b,_7n=_7k.c,_7o=_7k.e,_7p=E(_7k.d);if(!_7p._){var _7q=_7p.a,_7r=E(_7o);if(!_7r._){var _7s=_7r.a,_7t=_7r.b,_7u=_7r.c,_7v=_7r.d;if(_7s>=(imul(2,_7q)|0)){var _7w=function(_7x){var _7y=E(_7r.e);return (_7y._==0)?new T5(0,1+_7l|0,E(_7t),_7u,E(new T5(0,(1+_7q|0)+_7x|0,E(_7m),_7n,_7p,E(_7v))),E(new T5(0,1+_7y.a|0,E(_6Z),_70,_7y,E(_6U)))):new T5(0,1+_7l|0,E(_7t),_7u,E(new T5(0,(1+_7q|0)+_7x|0,E(_7m),_7n,_7p,E(_7v))),E(new T5(0,1,E(_6Z),_70,E(_6U),E(_6U))));},_7z=E(_7v);if(!_7z._){return _7w(_7z.a);}else{return _7w(0);}}else{return new T5(0,1+_7l|0,E(_7m),_7n,_7p,E(new T5(0,1+_7s|0,E(_6Z),_70,_7r,E(_6U))));}}else{return new T5(0,3,E(_7m),_7n,_7p,E(new T5(0,1,E(_6Z),_70,E(_6U),E(_6U))));}}else{var _7A=E(_7o);return (_7A._==0)?new T5(0,3,E(_7A.b),_7A.c,E(new T5(0,1,E(_7m),_7n,E(_6U),E(_6U))),E(new T5(0,1,E(_6Z),_70,E(_6U),E(_6U)))):new T5(0,2,E(_6Z),_70,_7k,E(_6U));}}else{return new T5(0,1,E(_6Z),_70,E(_6U),E(_6U));}}},_7B=new T(function(){return unCStr("Failure in Data.Map.balanceR");}),_7C=new T(function(){var _7D=_;return err(_7B);}),_7E=function(_7F,_7G,_7H,_7I){var _7J=E(_7H);if(!_7J._){var _7K=_7J.a,_7L=E(_7I);if(!_7L._){var _7M=_7L.a,_7N=_7L.b,_7O=_7L.c;if(_7M<=(imul(3,_7K)|0)){return new T5(0,(1+_7K|0)+_7M|0,E(_7F),_7G,_7J,_7L);}else{var _7P=E(_7L.d);if(!_7P._){var _7Q=_7P.a,_7R=_7P.b,_7S=_7P.c,_7T=_7P.d,_7U=E(_7L.e);if(!_7U._){var _7V=_7U.a;if(_7Q>=(imul(2,_7V)|0)){var _7W=function(_7X){var _7Y=E(_7F),_7Z=E(_7P.e);return (_7Z._==0)?new T5(0,(1+_7K|0)+_7M|0,E(_7R),_7S,E(new T5(0,(1+_7K|0)+_7X|0,_7Y,_7G,_7J,E(_7T))),E(new T5(0,(1+_7V|0)+_7Z.a|0,E(_7N),_7O,_7Z,_7U))):new T5(0,(1+_7K|0)+_7M|0,E(_7R),_7S,E(new T5(0,(1+_7K|0)+_7X|0,_7Y,_7G,_7J,E(_7T))),E(new T5(0,1+_7V|0,E(_7N),_7O,E(_6U),_7U)));},_80=E(_7T);if(!_80._){return _7W(_80.a);}else{return _7W(0);}}else{return new T5(0,(1+_7K|0)+_7M|0,E(_7N),_7O,E(new T5(0,(1+_7K|0)+_7Q|0,E(_7F),_7G,_7J,_7P)),_7U);}}else{return E(_7C);}}else{return E(_7C);}}}else{return new T5(0,1+_7K|0,E(_7F),_7G,_7J,E(_6U));}}else{var _81=E(_7I);if(!_81._){var _82=_81.a,_83=_81.b,_84=_81.c,_85=_81.e,_86=E(_81.d);if(!_86._){var _87=_86.a,_88=_86.b,_89=_86.c,_8a=_86.d,_8b=E(_85);if(!_8b._){var _8c=_8b.a;if(_87>=(imul(2,_8c)|0)){var _8d=function(_8e){var _8f=E(_7F),_8g=E(_86.e);return (_8g._==0)?new T5(0,1+_82|0,E(_88),_89,E(new T5(0,1+_8e|0,_8f,_7G,E(_6U),E(_8a))),E(new T5(0,(1+_8c|0)+_8g.a|0,E(_83),_84,_8g,_8b))):new T5(0,1+_82|0,E(_88),_89,E(new T5(0,1+_8e|0,_8f,_7G,E(_6U),E(_8a))),E(new T5(0,1+_8c|0,E(_83),_84,E(_6U),_8b)));},_8h=E(_8a);if(!_8h._){return _8d(_8h.a);}else{return _8d(0);}}else{return new T5(0,1+_82|0,E(_83),_84,E(new T5(0,1+_87|0,E(_7F),_7G,E(_6U),_86)),_8b);}}else{return new T5(0,3,E(_88),_89,E(new T5(0,1,E(_7F),_7G,E(_6U),E(_6U))),E(new T5(0,1,E(_83),_84,E(_6U),E(_6U))));}}else{var _8i=E(_85);return (_8i._==0)?new T5(0,3,E(_83),_84,E(new T5(0,1,E(_7F),_7G,E(_6U),E(_6U))),_8i):new T5(0,2,E(_7F),_7G,E(_6U),_81);}}else{return new T5(0,1,E(_7F),_7G,E(_6U),E(_6U));}}},_8j=function(_8k,_8l,_8m){var _8n=E(_8k),_8o=E(_8l),_8p=E(_8m);if(!_8p._){var _8q=_8p.b,_8r=_8p.c,_8s=_8p.d,_8t=_8p.e;switch(_6N(_8n,_8q)){case 0:return _6Y(_8q,_8r,_8j(_8n,_8o,_8s),_8t);case 1:return new T5(0,_8p.a,_8n,_8o,E(_8s),E(_8t));default:return _7E(_8q,_8r,_8s,_8j(_8n,_8o,_8t));}}else{return new T5(0,1,_8n,_8o,E(_6U),E(_6U));}},_8u=function(_8v,_8w){while(1){var _8x=E(_8w);if(!_8x._){return E(_8v);}else{var _8y=E(_8x.a),_8z=_8j(_8y.a,_8y.b,_8v);_8v=_8z;_8w=_8x.b;continue;}}},_8A=function(_8B,_8C){return new T5(0,1,E(_8B),_8C,E(_6U),E(_6U));},_8D=function(_8E,_8F,_8G){var _8H=E(_8G);if(!_8H._){return _7E(_8H.b,_8H.c,_8H.d,_8D(_8E,_8F,_8H.e));}else{return _8A(_8E,_8F);}},_8I=function(_8J,_8K,_8L){var _8M=E(_8L);if(!_8M._){return _6Y(_8M.b,_8M.c,_8I(_8J,_8K,_8M.d),_8M.e);}else{return _8A(_8J,_8K);}},_8N=function(_8O,_8P,_8Q,_8R,_8S,_8T,_8U){return _6Y(_8R,_8S,_8I(_8O,_8P,_8T),_8U);},_8V=function(_8W,_8X,_8Y,_8Z,_90,_91,_92,_93){var _94=E(_8Y);if(!_94._){var _95=_94.a,_96=_94.b,_97=_94.c,_98=_94.d,_99=_94.e;if((imul(3,_95)|0)>=_8Z){if((imul(3,_8Z)|0)>=_95){return new T5(0,(_95+_8Z|0)+1|0,E(_8W),_8X,_94,E(new T5(0,_8Z,E(_90),_91,E(_92),E(_93))));}else{return _7E(_96,_97,_98,B(_8V(_8W,_8X,_99,_8Z,_90,_91,_92,_93)));}}else{return _6Y(_90,_91,B(_9a(_8W,_8X,_95,_96,_97,_98,_99,_92)),_93);}}else{return _8N(_8W,_8X,_8Z,_90,_91,_92,_93);}},_9a=function(_9b,_9c,_9d,_9e,_9f,_9g,_9h,_9i){var _9j=E(_9i);if(!_9j._){var _9k=_9j.a,_9l=_9j.b,_9m=_9j.c,_9n=_9j.d,_9o=_9j.e;if((imul(3,_9d)|0)>=_9k){if((imul(3,_9k)|0)>=_9d){return new T5(0,(_9d+_9k|0)+1|0,E(_9b),_9c,E(new T5(0,_9d,E(_9e),_9f,E(_9g),E(_9h))),_9j);}else{return _7E(_9e,_9f,_9g,B(_8V(_9b,_9c,_9h,_9k,_9l,_9m,_9n,_9o)));}}else{return _6Y(_9l,_9m,B(_9a(_9b,_9c,_9d,_9e,_9f,_9g,_9h,_9n)),_9o);}}else{return _8D(_9b,_9c,new T5(0,_9d,E(_9e),_9f,E(_9g),E(_9h)));}},_9p=function(_9q,_9r,_9s,_9t){var _9u=E(_9s);if(!_9u._){var _9v=_9u.a,_9w=_9u.b,_9x=_9u.c,_9y=_9u.d,_9z=_9u.e,_9A=E(_9t);if(!_9A._){var _9B=_9A.a,_9C=_9A.b,_9D=_9A.c,_9E=_9A.d,_9F=_9A.e;if((imul(3,_9v)|0)>=_9B){if((imul(3,_9B)|0)>=_9v){return new T5(0,(_9v+_9B|0)+1|0,E(_9q),_9r,_9u,_9A);}else{return _7E(_9w,_9x,_9y,B(_8V(_9q,_9r,_9z,_9B,_9C,_9D,_9E,_9F)));}}else{return _6Y(_9C,_9D,B(_9a(_9q,_9r,_9v,_9w,_9x,_9y,_9z,_9E)),_9F);}}else{return _8D(_9q,_9r,_9u);}}else{return _8I(_9q,_9r,_9t);}},_9G=function(_9H,_9I){var _9J=E(_9I);if(!_9J._){return new T3(0,_6U,__Z,__Z);}else{var _9K=E(_9H);if(_9K==1){var _9L=E(_9J.a),_9M=_9L.a,_9N=_9L.b,_9O=E(_9J.b);return (_9O._==0)?new T3(0,new T(function(){return new T5(0,1,E(_9M),E(_9N),E(_6U),E(_6U));}),__Z,__Z):(_6N(_9M,E(_9O.a).a)==0)?new T3(0,new T(function(){return new T5(0,1,E(_9M),E(_9N),E(_6U),E(_6U));}),_9O,__Z):new T3(0,new T(function(){return new T5(0,1,E(_9M),E(_9N),E(_6U),E(_6U));}),__Z,_9O);}else{var _9P=_9G(_9K>>1,_9J),_9Q=_9P.a,_9R=_9P.c,_9S=E(_9P.b);if(!_9S._){return new T3(0,_9Q,__Z,_9R);}else{var _9T=E(_9S.a),_9U=_9T.a,_9V=_9T.b,_9W=E(_9S.b);if(!_9W._){return new T3(0,new T(function(){return _8D(_9U,E(_9V),_9Q);}),__Z,_9R);}else{if(!_6N(_9U,E(_9W.a).a)){var _9X=_9G(_9K>>1,_9W);return new T3(0,new T(function(){return B(_9p(_9U,E(_9V),_9Q,_9X.a));}),_9X.b,_9X.c);}else{return new T3(0,_9Q,__Z,_9S);}}}}}},_9Y=function(_9Z,_a0,_a1){while(1){var _a2=E(_a1);if(!_a2._){return E(_a0);}else{var _a3=E(_a2.a),_a4=_a3.a,_a5=_a3.b,_a6=E(_a2.b);if(!_a6._){return _8D(_a4,E(_a5),_a0);}else{if(!_6N(_a4,E(_a6.a).a)){var _a7=_9G(_9Z,_a6),_a8=_a7.a,_a9=E(_a7.c);if(!_a9._){var _aa=_9Z<<1,_ab=B(_9p(_a4,E(_a5),_a0,_a8));_9Z=_aa;_a0=_ab;_a1=_a7.b;continue;}else{return _8u(B(_9p(_a4,E(_a5),_a0,_a8)),_a9);}}else{return _8u(_a0,_a2);}}}}},_ac=function(_ad){var _ae=E(_ad);if(!_ae._){return new T0(1);}else{var _af=E(_ae.a),_ag=_af.a,_ah=_af.b,_ai=E(_ae.b);if(!_ai._){return new T5(0,1,E(_ag),E(_ah),E(_6U),E(_6U));}else{if(!_6N(_ag,E(_ai.a).a)){return C > 19 ? new F(function(){return _9Y(1,new T5(0,1,E(_ag),E(_ah),E(_6U),E(_6U)),_ai);}) : (++C,_9Y(1,new T5(0,1,E(_ag),E(_ah),E(_6U),E(_6U)),_ai));}else{return _8u(new T5(0,1,E(_ag),E(_ah),E(_6U),E(_6U)),_ai);}}}},_aj=function(_){var _ak=_6K("Other");return __Z;},_al=function(_am,_){var _an=E(_am);if(!_an._){return __Z;}else{var _ao=B(A1(_an.a,_)),_ap=_al(_an.b,_);return new T2(1,_ao,_ap);}},_aq=new T(function(){return JSON.stringify;}),_ar=function(_as,_at){var _au=E(_at);switch(_au._){case 0:return new T2(0,new T(function(){return jsShow(_au.a);}),_as);case 1:return new T2(0,new T(function(){var _av=E(_aq)(_au.a);return String(_av);}),_as);case 2:return (!E(_au.a))?new T2(0,"false",_as):new T2(0,"true",_as);case 3:var _aw=E(_au.a);if(!_aw._){return new T2(0,"[",new T2(1,"]",_as));}else{var _ax=new T(function(){var _ay=new T(function(){var _az=function(_aA){var _aB=E(_aA);if(!_aB._){return E(new T2(1,"]",_as));}else{var _aC=new T(function(){var _aD=_ar(new T(function(){return _az(_aB.b);}),_aB.a);return new T2(1,_aD.a,_aD.b);});return new T2(1,",",_aC);}};return _az(_aw.b);}),_aE=_ar(_ay,_aw.a);return new T2(1,_aE.a,_aE.b);});return new T2(0,"[",_ax);}break;case 4:var _aF=E(_au.a);if(!_aF._){return new T2(0,"{",new T2(1,"}",_as));}else{var _aG=E(_aF.a),_aH=new T(function(){var _aI=new T(function(){var _aJ=function(_aK){var _aL=E(_aK);if(!_aL._){return E(new T2(1,"}",_as));}else{var _aM=E(_aL.a),_aN=new T(function(){var _aO=_ar(new T(function(){return _aJ(_aL.b);}),_aM.b);return new T2(1,_aO.a,_aO.b);});return new T2(1,",",new T2(1,"\"",new T2(1,_aM.a,new T2(1,"\"",new T2(1,":",_aN)))));}};return _aJ(_aF.b);}),_aP=_ar(_aI,_aG.b);return new T2(1,_aP.a,_aP.b);});return new T2(0,"{",new T2(1,new T(function(){var _aQ=E(_aq)(E(_aG.a));return String(_aQ);}),new T2(1,":",_aH)));}break;default:return new T2(0,"null",_as);}},_aR=new T(function(){return toJSStr(__Z);}),_aS=function(_aT){var _aU=_ar(__Z,_aT),_aV=jsCat(new T2(1,_aU.a,_aU.b),E(_aR));return fromJSStr(_aV);},_aW=function(_){var _aX=_6K("Error decoding cost tree data");return _6J(_);},_aY=new T(function(){return err(new T(function(){return unCStr("Maybe.fromJust: Nothing");}));}),_aZ=function(_b0,_b1,_b2){while(1){var _b3=E(_b2);if(!_b3._){return __Z;}else{var _b4=E(_b3.a);if(!B(A3(_1F,_b0,_b1,_b4.a))){_b2=_b3.b;continue;}else{return new T1(1,_b4.b);}}}},_b5=new T(function(){return unCStr("main");}),_b6=new T(function(){return unCStr("Ajax");}),_b7=new T(function(){return unCStr("ServerMessageException");}),_b8=function(_b9){return E(new T5(0,new Long(2796709153,857663197,true),new Long(2290229150,2001624562,true),new T5(0,new Long(2796709153,857663197,true),new Long(2290229150,2001624562,true),_b5,_b6,_b7),__Z,__Z));},_ba=new T(function(){return unCStr("SME ");}),_bb=new T(function(){return unCStr("Prelude.");}),_bc=new T(function(){return err(new T(function(){return _0(_bb,new T(function(){return unCStr("!!: negative index");}));}));}),_bd=new T(function(){return err(new T(function(){return _0(_bb,new T(function(){return unCStr("!!: index too large");}));}));}),_be=function(_bf,_bg){while(1){var _bh=E(_bf);if(!_bh._){return E(_bd);}else{var _bi=E(_bg);if(!_bi){return E(_bh.a);}else{_bf=_bh.b;_bg=_bi-1|0;continue;}}}},_bj=function(_bk,_bl){if(_bl>=0){return _be(_bk,_bl);}else{return E(_bc);}},_bm=new T(function(){return unCStr("ACK");}),_bn=new T(function(){return unCStr("BEL");}),_bo=new T(function(){return unCStr("BS");}),_bp=new T(function(){return unCStr("SP");}),_bq=new T(function(){return unCStr("US");}),_br=new T(function(){return unCStr("RS");}),_bs=new T(function(){return unCStr("GS");}),_bt=new T(function(){return unCStr("FS");}),_bu=new T(function(){return unCStr("ESC");}),_bv=new T(function(){return unCStr("SUB");}),_bw=new T(function(){return unCStr("EM");}),_bx=new T(function(){return unCStr("CAN");}),_by=new T(function(){return unCStr("ETB");}),_bz=new T(function(){return unCStr("SYN");}),_bA=new T(function(){return unCStr("NAK");}),_bB=new T(function(){return unCStr("DC4");}),_bC=new T(function(){return unCStr("DC3");}),_bD=new T(function(){return unCStr("DC2");}),_bE=new T(function(){return unCStr("DC1");}),_bF=new T(function(){return unCStr("DLE");}),_bG=new T(function(){return unCStr("SI");}),_bH=new T(function(){return unCStr("SO");}),_bI=new T(function(){return unCStr("CR");}),_bJ=new T(function(){return unCStr("FF");}),_bK=new T(function(){return unCStr("VT");}),_bL=new T(function(){return unCStr("LF");}),_bM=new T(function(){return unCStr("HT");}),_bN=new T(function(){return unCStr("ENQ");}),_bO=new T(function(){return unCStr("EOT");}),_bP=new T(function(){return unCStr("ETX");}),_bQ=new T(function(){return unCStr("STX");}),_bR=new T(function(){return unCStr("SOH");}),_bS=new T(function(){return unCStr("NUL");}),_bT=new T(function(){return unCStr("\\DEL");}),_bU=new T(function(){return unCStr("\\a");}),_bV=new T(function(){return unCStr("\\\\");}),_bW=new T(function(){return unCStr("\\SO");}),_bX=new T(function(){return unCStr("\\r");}),_bY=new T(function(){return unCStr("\\f");}),_bZ=new T(function(){return unCStr("\\v");}),_c0=new T(function(){return unCStr("\\n");}),_c1=new T(function(){return unCStr("\\t");}),_c2=new T(function(){return unCStr("\\b");}),_c3=function(_c4,_c5){if(_c4<=127){var _c6=E(_c4);switch(_c6){case 92:return _0(_bV,_c5);case 127:return _0(_bT,_c5);default:if(_c6<32){switch(_c6){case 7:return _0(_bU,_c5);case 8:return _0(_c2,_c5);case 9:return _0(_c1,_c5);case 10:return _0(_c0,_c5);case 11:return _0(_bZ,_c5);case 12:return _0(_bY,_c5);case 13:return _0(_bX,_c5);case 14:return _0(_bW,new T(function(){var _c7=E(_c5);if(!_c7._){return __Z;}else{if(E(_c7.a)==72){return unAppCStr("\\&",_c7);}else{return _c7;}}},1));default:return _0(new T2(1,92,new T(function(){return _bj(new T2(1,_bS,new T2(1,_bR,new T2(1,_bQ,new T2(1,_bP,new T2(1,_bO,new T2(1,_bN,new T2(1,_bm,new T2(1,_bn,new T2(1,_bo,new T2(1,_bM,new T2(1,_bL,new T2(1,_bK,new T2(1,_bJ,new T2(1,_bI,new T2(1,_bH,new T2(1,_bG,new T2(1,_bF,new T2(1,_bE,new T2(1,_bD,new T2(1,_bC,new T2(1,_bB,new T2(1,_bA,new T2(1,_bz,new T2(1,_by,new T2(1,_bx,new T2(1,_bw,new T2(1,_bv,new T2(1,_bu,new T2(1,_bt,new T2(1,_bs,new T2(1,_br,new T2(1,_bq,new T2(1,_bp,__Z))))))))))))))))))))))))))))))))),_c6);})),_c5);}}else{return new T2(1,_c6,_c5);}}}else{var _c8=new T(function(){var _c9=jsShowI(_c4);return _0(fromJSStr(_c9),new T(function(){var _ca=E(_c5);if(!_ca._){return __Z;}else{var _cb=E(_ca.a);if(_cb<48){return _ca;}else{if(_cb>57){return _ca;}else{return unAppCStr("\\&",_ca);}}}},1));});return new T2(1,92,_c8);}},_cc=new T(function(){return unCStr("\\\"");}),_cd=function(_ce,_cf){var _cg=E(_ce);if(!_cg._){return E(_cf);}else{var _ch=_cg.b,_ci=E(_cg.a);if(_ci==34){return _0(_cc,new T(function(){return _cd(_ch,_cf);},1));}else{return _c3(_ci,new T(function(){return _cd(_ch,_cf);}));}}},_cj=function(_ck,_cl,_cm){if(_ck<11){return _0(_ba,new T2(1,34,new T(function(){return _cd(_cl,new T2(1,34,_cm));})));}else{var _cn=new T(function(){return _0(_ba,new T2(1,34,new T(function(){return _cd(_cl,new T2(1,34,new T2(1,41,_cm)));})));});return new T2(1,40,_cn);}},_co=function(_cp){return _cj(0,E(_cp).a,__Z);},_cq=function(_cr,_cs){return _cj(0,E(_cr).a,_cs);},_ct=new T(function(){return new T5(0,_b8,new T3(0,function(_cu,_cv,_cw){return _cj(E(_cu),E(_cv).a,_cw);},_co,function(_cx,_cy){return _2P(_cq,_cx,_cy);}),function(_cy){return new T2(0,_ct,_cy);},function(_cz){var _cA=E(_cz);return _2w(_2u(_cA.a),_b8,_cA.b);},_co);}),_cB=function(_cC){return E(E(_cC).c);},_cD=function(_cE,_cF){return die(new T(function(){return B(A2(_cB,_cF,_cE));}));},_cG=function(_cH,_39){return _cD(_cH,_39);},_cI=new T(function(){return _cG(new T1(0,new T(function(){return unCStr("Error decoding cost tree data");})),_ct);}),_cJ=new T(function(){return unCStr("base");}),_cK=new T(function(){return unCStr("Control.Exception.Base");}),_cL=new T(function(){return unCStr("PatternMatchFail");}),_cM=function(_cN){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_cJ,_cK,_cL),__Z,__Z));},_cO=function(_cP){return E(E(_cP).a);},_cQ=function(_cR,_cS){return _0(E(_cR).a,_cS);},_cT=new T(function(){return new T5(0,_cM,new T3(0,function(_cU,_cV,_cW){return _0(E(_cV).a,_cW);},_cO,function(_cX,_cY){return _2P(_cQ,_cX,_cY);}),function(_cZ){return new T2(0,_cT,_cZ);},function(_d0){var _d1=E(_d0);return _2w(_2u(_d1.a),_cM,_d1.b);},_cO);}),_d2=new T(function(){return unCStr("Non-exhaustive patterns in");}),_d3=function(_d4,_d5){var _d6=E(_d5);if(!_d6._){return new T2(0,__Z,__Z);}else{var _d7=_d6.a;if(!B(A1(_d4,_d7))){return new T2(0,__Z,_d6);}else{var _d8=new T(function(){var _d9=_d3(_d4,_d6.b);return new T2(0,_d9.a,_d9.b);});return new T2(0,new T2(1,_d7,new T(function(){return E(E(_d8).a);})),new T(function(){return E(E(_d8).b);}));}}},_da=new T(function(){return unCStr("\n");}),_db=function(_dc){return (E(_dc)==124)?false:true;},_dd=function(_de,_df){var _dg=_d3(_db,unCStr(_de)),_dh=_dg.a,_di=function(_dj,_dk){var _dl=new T(function(){var _dm=new T(function(){return _0(_df,new T(function(){return _0(_dk,_da);},1));});return unAppCStr(": ",_dm);},1);return _0(_dj,_dl);},_dn=E(_dg.b);if(!_dn._){return _di(_dh,__Z);}else{if(E(_dn.a)==124){return _di(_dh,new T2(1,32,_dn.b));}else{return _di(_dh,__Z);}}},_do=function(_dp){return _cG(new T1(0,new T(function(){return _dd(_dp,_d2);})),_cT);},_dq=function(_dr){return C > 19 ? new F(function(){return _do("Ajax.hs:94:21-91|lambda");}) : (++C,_do("Ajax.hs:94:21-91|lambda"));},_ds=function(_dt){var _du=E(_dt);if(!_du._){var _dv=_du.a,_dw=_dv&4294967295;return (_dv>=_dw)?_dw:_dw-1|0;}else{return C > 19 ? new F(function(){return _do("Ajax.hs:94:56-74|lambda");}) : (++C,_do("Ajax.hs:94:56-74|lambda"));}},_dx=function(_dy){return C > 19 ? new F(function(){return _ds(_dy);}) : (++C,_ds(_dy));},_dz=function(_dA,_dB){var _dC=E(_dB);return (_dC._==0)?__Z:new T2(1,new T(function(){return B(A1(_dA,_dC.a));}),new T(function(){return _dz(_dA,_dC.b);}));},_dD=function(_dE){var _dF=E(_dE);if(_dF._==3){var _dG=E(_dF.a);if(!_dG._){return C > 19 ? new F(function(){return _dq(_);}) : (++C,_dq(_));}else{var _dH=E(_dG.a);if(_dH._==3){var _dI=E(_dG.b);if(!_dI._){return C > 19 ? new F(function(){return _dq(_);}) : (++C,_dq(_));}else{var _dJ=E(_dI.a);if(_dJ._==1){if(!E(_dI.b)._){return new T2(0,new T(function(){return _dz(_dx,_dH.a);}),new T(function(){return fromJSStr(_dJ.a);}));}else{return C > 19 ? new F(function(){return _dq(_);}) : (++C,_dq(_));}}else{return C > 19 ? new F(function(){return _dq(_);}) : (++C,_dq(_));}}}else{return C > 19 ? new F(function(){return _dq(_);}) : (++C,_dq(_));}}}else{return C > 19 ? new F(function(){return _dq(_);}) : (++C,_dq(_));}},_dK=function(_dL){var _dM=B(_dD(_dL));return new T2(0,_dM.a,_dM.b);},_dN=new T(function(){return B(_do("Ajax.hs:132:5-39|function getJustNum"));}),_dO=new T(function(){return B(_do("Ajax.hs:133:5-42|function getJustStr"));}),_dP=function(_dQ,_){var _dR=_6K(toJSStr(unAppCStr("Trying to decode cost tree ",new T(function(){return _aS(_dQ);})))),_dS=E(_dQ);if(_dS._==4){var _dT=_dS.a,_dU=_aZ(_1L,"lin",_dT);if(!_dU._){return E(_aY);}else{var _dV=function(_,_dW){var _dX=_aZ(_1L,"score",_dT);if(!_dX._){var _dY=_aW(_);return E(_cI);}else{var _dZ=_aZ(_1L,"tree",_dT);if(!_dZ._){var _e0=_aW(_);return E(_cI);}else{return new T3(0,new T(function(){var _e1=E(_dX.a);if(!_e1._){var _e2=_6x(_3A,_e1.a),_e3=_e2.a;if(E(_e2.b)>=0){return E(_e3);}else{return E(_e3)-1|0;}}else{return E(_dN);}}),_dW,new T(function(){var _e4=E(_dZ.a);if(_e4._==1){return fromJSStr(_e4.a);}else{return E(_dO);}}));}}},_e5=E(_dU.a);if(_e5._==3){return _dV(_,new T(function(){return _dz(_dK,_e5.a);}));}else{return _dV(_,__Z);}}}else{return E(_aY);}},_e6=new T(function(){return B(_do("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_e7=function(_e8,_e9){while(1){var _ea=(function(_eb,_ec){var _ed=E(_eb);switch(_ed._){case 0:var _ee=E(_ec);if(!_ee._){return __Z;}else{_e8=B(A1(_ed.a,_ee.a));_e9=_ee.b;return __continue;}break;case 1:var _ef=B(A1(_ed.a,_ec)),_eg=_ec;_e8=_ef;_e9=_eg;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_ed.a,_ec),new T(function(){return _e7(_ed.b,_ec);}));default:return E(_ed.a);}})(_e8,_e9);if(_ea!=__continue){return _ea;}}},_eh=function(_ei,_ej){var _ek=function(_el){var _em=E(_ej);if(_em._==3){return new T2(3,_em.a,new T(function(){return _eh(_ei,_em.b);}));}else{var _en=E(_ei);if(_en._==2){return _em;}else{if(_em._==2){return _en;}else{var _eo=function(_ep){if(_em._==4){var _eq=function(_er){return new T1(4,new T(function(){return _0(_e7(_en,_er),_em.a);}));};return new T1(1,_eq);}else{if(_en._==1){var _es=_en.a;if(!_em._){return new T1(1,function(_et){return _eh(B(A1(_es,_et)),_em);});}else{var _eu=function(_ev){return _eh(B(A1(_es,_ev)),new T(function(){return B(A1(_em.a,_ev));}));};return new T1(1,_eu);}}else{if(!_em._){return E(_e6);}else{var _ew=function(_ex){return _eh(_en,new T(function(){return B(A1(_em.a,_ex));}));};return new T1(1,_ew);}}}};switch(_en._){case 1:if(_em._==4){var _ey=function(_ez){return new T1(4,new T(function(){return _0(_e7(B(A1(_en.a,_ez)),_ez),_em.a);}));};return new T1(1,_ey);}else{return _eo(_);}break;case 4:var _eA=_en.a;switch(_em._){case 0:var _eB=function(_eC){var _eD=new T(function(){return _0(_eA,new T(function(){return _e7(_em,_eC);},1));});return new T1(4,_eD);};return new T1(1,_eB);case 1:var _eE=function(_eF){var _eG=new T(function(){return _0(_eA,new T(function(){return _e7(B(A1(_em.a,_eF)),_eF);},1));});return new T1(4,_eG);};return new T1(1,_eE);default:return new T1(4,new T(function(){return _0(_eA,_em.a);}));}break;default:return _eo(_);}}}}},_eH=E(_ei);switch(_eH._){case 0:var _eI=E(_ej);if(!_eI._){var _eJ=function(_eK){return _eh(B(A1(_eH.a,_eK)),new T(function(){return B(A1(_eI.a,_eK));}));};return new T1(0,_eJ);}else{return _ek(_);}break;case 3:return new T2(3,_eH.a,new T(function(){return _eh(_eH.b,_ej);}));default:return _ek(_);}},_eL=new T(function(){return unCStr("(");}),_eM=new T(function(){return unCStr(")");}),_eN=function(_eO,_eP){while(1){var _eQ=E(_eO);if(!_eQ._){return (E(_eP)._==0)?true:false;}else{var _eR=E(_eP);if(!_eR._){return false;}else{if(E(_eQ.a)!=E(_eR.a)){return false;}else{_eO=_eQ.b;_eP=_eR.b;continue;}}}}},_eS=new T2(0,function(_eT,_eU){return E(_eT)==E(_eU);},function(_eV,_eW){return E(_eV)!=E(_eW);}),_eX=function(_eY,_eZ){while(1){var _f0=E(_eY);if(!_f0._){return (E(_eZ)._==0)?true:false;}else{var _f1=E(_eZ);if(!_f1._){return false;}else{if(E(_f0.a)!=E(_f1.a)){return false;}else{_eY=_f0.b;_eZ=_f1.b;continue;}}}}},_f2=function(_f3,_f4){return (!_eX(_f3,_f4))?true:false;},_f5=function(_f6,_f7){var _f8=E(_f6);switch(_f8._){case 0:return new T1(0,function(_f9){return C > 19 ? new F(function(){return _f5(B(A1(_f8.a,_f9)),_f7);}) : (++C,_f5(B(A1(_f8.a,_f9)),_f7));});case 1:return new T1(1,function(_fa){return C > 19 ? new F(function(){return _f5(B(A1(_f8.a,_fa)),_f7);}) : (++C,_f5(B(A1(_f8.a,_fa)),_f7));});case 2:return new T0(2);case 3:return _eh(B(A1(_f7,_f8.a)),new T(function(){return B(_f5(_f8.b,_f7));}));default:var _fb=function(_fc){var _fd=E(_fc);if(!_fd._){return __Z;}else{var _fe=E(_fd.a);return _0(_e7(B(A1(_f7,_fe.a)),_fe.b),new T(function(){return _fb(_fd.b);},1));}},_ff=_fb(_f8.a);return (_ff._==0)?new T0(2):new T1(4,_ff);}},_fg=new T0(2),_fh=function(_fi){return new T2(3,_fi,_fg);},_fj=function(_fk,_fl){var _fm=E(_fk);if(!_fm){return C > 19 ? new F(function(){return A1(_fl,0);}) : (++C,A1(_fl,0));}else{var _fn=new T(function(){return B(_fj(_fm-1|0,_fl));});return new T1(0,function(_fo){return E(_fn);});}},_fp=function(_fq,_fr,_fs){var _ft=new T(function(){return B(A1(_fq,_fh));}),_fu=function(_fv,_fw,_fx,_fy){while(1){var _fz=B((function(_fA,_fB,_fC,_fD){var _fE=E(_fA);switch(_fE._){case 0:var _fF=E(_fB);if(!_fF._){return C > 19 ? new F(function(){return A1(_fr,_fD);}) : (++C,A1(_fr,_fD));}else{var _fG=_fC+1|0,_fH=_fD;_fv=B(A1(_fE.a,_fF.a));_fw=_fF.b;_fx=_fG;_fy=_fH;return __continue;}break;case 1:var _fI=B(A1(_fE.a,_fB)),_fJ=_fB,_fG=_fC,_fH=_fD;_fv=_fI;_fw=_fJ;_fx=_fG;_fy=_fH;return __continue;case 2:return C > 19 ? new F(function(){return A1(_fr,_fD);}) : (++C,A1(_fr,_fD));break;case 3:var _fK=new T(function(){return B(_f5(_fE,_fD));});return C > 19 ? new F(function(){return _fj(_fC,function(_fL){return E(_fK);});}) : (++C,_fj(_fC,function(_fL){return E(_fK);}));break;default:return C > 19 ? new F(function(){return _f5(_fE,_fD);}) : (++C,_f5(_fE,_fD));}})(_fv,_fw,_fx,_fy));if(_fz!=__continue){return _fz;}}};return function(_fM){return _fu(_ft,_fM,0,_fs);};},_fN=function(_fO){return C > 19 ? new F(function(){return A1(_fO,__Z);}) : (++C,A1(_fO,__Z));},_fP=function(_fQ,_fR){var _fS=function(_fT){var _fU=E(_fT);if(!_fU._){return _fN;}else{var _fV=_fU.a;if(!B(A1(_fQ,_fV))){return _fN;}else{var _fW=new T(function(){return _fS(_fU.b);}),_fX=function(_fY){var _fZ=new T(function(){return B(A1(_fW,function(_g0){return C > 19 ? new F(function(){return A1(_fY,new T2(1,_fV,_g0));}) : (++C,A1(_fY,new T2(1,_fV,_g0)));}));});return new T1(0,function(_g1){return E(_fZ);});};return _fX;}}};return function(_g2){return C > 19 ? new F(function(){return A2(_fS,_g2,_fR);}) : (++C,A2(_fS,_g2,_fR));};},_g3=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_g4=function(_g5,_g6){var _g7=function(_g8,_g9){var _ga=E(_g8);if(!_ga._){var _gb=new T(function(){return B(A1(_g9,__Z));});return function(_gc){return C > 19 ? new F(function(){return A1(_gc,_gb);}) : (++C,A1(_gc,_gb));};}else{var _gd=E(_ga.a),_ge=function(_gf){var _gg=new T(function(){return _g7(_ga.b,function(_gh){return C > 19 ? new F(function(){return A1(_g9,new T2(1,_gf,_gh));}) : (++C,A1(_g9,new T2(1,_gf,_gh)));});}),_gi=function(_gj){var _gk=new T(function(){return B(A1(_gg,_gj));});return new T1(0,function(_gl){return E(_gk);});};return _gi;};switch(E(_g5)){case 8:if(48>_gd){var _gm=new T(function(){return B(A1(_g9,__Z));});return function(_gn){return C > 19 ? new F(function(){return A1(_gn,_gm);}) : (++C,A1(_gn,_gm));};}else{if(_gd>55){var _go=new T(function(){return B(A1(_g9,__Z));});return function(_gp){return C > 19 ? new F(function(){return A1(_gp,_go);}) : (++C,A1(_gp,_go));};}else{return _ge(_gd-48|0);}}break;case 10:if(48>_gd){var _gq=new T(function(){return B(A1(_g9,__Z));});return function(_gr){return C > 19 ? new F(function(){return A1(_gr,_gq);}) : (++C,A1(_gr,_gq));};}else{if(_gd>57){var _gs=new T(function(){return B(A1(_g9,__Z));});return function(_gt){return C > 19 ? new F(function(){return A1(_gt,_gs);}) : (++C,A1(_gt,_gs));};}else{return _ge(_gd-48|0);}}break;case 16:if(48>_gd){if(97>_gd){if(65>_gd){var _gu=new T(function(){return B(A1(_g9,__Z));});return function(_gv){return C > 19 ? new F(function(){return A1(_gv,_gu);}) : (++C,A1(_gv,_gu));};}else{if(_gd>70){var _gw=new T(function(){return B(A1(_g9,__Z));});return function(_gx){return C > 19 ? new F(function(){return A1(_gx,_gw);}) : (++C,A1(_gx,_gw));};}else{return _ge((_gd-65|0)+10|0);}}}else{if(_gd>102){if(65>_gd){var _gy=new T(function(){return B(A1(_g9,__Z));});return function(_gz){return C > 19 ? new F(function(){return A1(_gz,_gy);}) : (++C,A1(_gz,_gy));};}else{if(_gd>70){var _gA=new T(function(){return B(A1(_g9,__Z));});return function(_gB){return C > 19 ? new F(function(){return A1(_gB,_gA);}) : (++C,A1(_gB,_gA));};}else{return _ge((_gd-65|0)+10|0);}}}else{return _ge((_gd-97|0)+10|0);}}}else{if(_gd>57){if(97>_gd){if(65>_gd){var _gC=new T(function(){return B(A1(_g9,__Z));});return function(_gD){return C > 19 ? new F(function(){return A1(_gD,_gC);}) : (++C,A1(_gD,_gC));};}else{if(_gd>70){var _gE=new T(function(){return B(A1(_g9,__Z));});return function(_gF){return C > 19 ? new F(function(){return A1(_gF,_gE);}) : (++C,A1(_gF,_gE));};}else{return _ge((_gd-65|0)+10|0);}}}else{if(_gd>102){if(65>_gd){var _gG=new T(function(){return B(A1(_g9,__Z));});return function(_gH){return C > 19 ? new F(function(){return A1(_gH,_gG);}) : (++C,A1(_gH,_gG));};}else{if(_gd>70){var _gI=new T(function(){return B(A1(_g9,__Z));});return function(_gJ){return C > 19 ? new F(function(){return A1(_gJ,_gI);}) : (++C,A1(_gJ,_gI));};}else{return _ge((_gd-65|0)+10|0);}}}else{return _ge((_gd-97|0)+10|0);}}}else{return _ge(_gd-48|0);}}break;default:return E(_g3);}}},_gK=function(_gL){var _gM=E(_gL);if(!_gM._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_g6,_gM);}) : (++C,A1(_g6,_gM));}};return function(_gN){return C > 19 ? new F(function(){return A3(_g7,_gN,_1C,_gK);}) : (++C,A3(_g7,_gN,_1C,_gK));};},_gO=function(_gP){var _gQ=function(_gR){return C > 19 ? new F(function(){return A1(_gP,new T1(5,new T2(0,8,_gR)));}) : (++C,A1(_gP,new T1(5,new T2(0,8,_gR))));},_gS=function(_gT){return C > 19 ? new F(function(){return A1(_gP,new T1(5,new T2(0,16,_gT)));}) : (++C,A1(_gP,new T1(5,new T2(0,16,_gT))));},_gU=function(_gV){switch(E(_gV)){case 79:return new T1(1,_g4(8,_gQ));case 88:return new T1(1,_g4(16,_gS));case 111:return new T1(1,_g4(8,_gQ));case 120:return new T1(1,_g4(16,_gS));default:return new T0(2);}};return function(_gW){return (E(_gW)==48)?E(new T1(0,_gU)):new T0(2);};},_gX=function(_gY){return new T1(0,_gO(_gY));},_gZ=function(_h0){return C > 19 ? new F(function(){return A1(_h0,__Z);}) : (++C,A1(_h0,__Z));},_h1=function(_h2){return C > 19 ? new F(function(){return A1(_h2,__Z);}) : (++C,A1(_h2,__Z));},_h3=function(_h4,_h5){while(1){var _h6=E(_h4);if(!_h6._){var _h7=_h6.a,_h8=E(_h5);if(!_h8._){var _h9=_h8.a,_ha=addC(_h7,_h9);if(!E(_ha.b)){return new T1(0,_ha.a);}else{_h4=new T1(1,I_fromInt(_h7));_h5=new T1(1,I_fromInt(_h9));continue;}}else{_h4=new T1(1,I_fromInt(_h7));_h5=_h8;continue;}}else{var _hb=E(_h5);if(!_hb._){_h4=_h6;_h5=new T1(1,I_fromInt(_hb.a));continue;}else{return new T1(1,I_add(_h6.a,_hb.a));}}}},_hc=new T(function(){return _h3(new T1(0,2147483647),new T1(0,1));}),_hd=function(_he){var _hf=E(_he);if(!_hf._){var _hg=E(_hf.a);return (_hg==(-2147483648))?E(_hc):new T1(0, -_hg);}else{return new T1(1,I_negate(_hf.a));}},_hh=new T1(0,10),_hi=function(_hj,_hk){while(1){var _hl=E(_hj);if(!_hl._){return E(_hk);}else{var _hm=_hk+1|0;_hj=_hl.b;_hk=_hm;continue;}}},_hn=function(_ho){return _3m(E(_ho));},_hp=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_hq=function(_hr,_hs){var _ht=E(_hs);if(!_ht._){return __Z;}else{var _hu=E(_ht.b);return (_hu._==0)?E(_hp):new T2(1,_h3(_4U(_ht.a,_hr),_hu.a),new T(function(){return _hq(_hr,_hu.b);}));}},_hv=new T1(0,0),_hw=function(_hx,_hy,_hz){while(1){var _hA=(function(_hB,_hC,_hD){var _hE=E(_hD);if(!_hE._){return E(_hv);}else{if(!E(_hE.b)._){return E(_hE.a);}else{var _hF=E(_hC);if(_hF<=40){var _hG=function(_hH,_hI){while(1){var _hJ=E(_hI);if(!_hJ._){return E(_hH);}else{var _hK=_h3(_4U(_hH,_hB),_hJ.a);_hH=_hK;_hI=_hJ.b;continue;}}};return _hG(_hv,_hE);}else{var _hL=_4U(_hB,_hB);if(!(_hF%2)){var _hM=_hq(_hB,_hE);_hx=_hL;_hy=quot(_hF+1|0,2);_hz=_hM;return __continue;}else{var _hM=_hq(_hB,new T2(1,_hv,_hE));_hx=_hL;_hy=quot(_hF+1|0,2);_hz=_hM;return __continue;}}}}})(_hx,_hy,_hz);if(_hA!=__continue){return _hA;}}},_hN=function(_hO,_hP){return _hw(_hO,new T(function(){return _hi(_hP,0);},1),_dz(_hn,_hP));},_hQ=function(_hR){var _hS=new T(function(){var _hT=new T(function(){var _hU=function(_hV){return C > 19 ? new F(function(){return A1(_hR,new T1(1,new T(function(){return _hN(_hh,_hV);})));}) : (++C,A1(_hR,new T1(1,new T(function(){return _hN(_hh,_hV);}))));};return new T1(1,_g4(10,_hU));}),_hW=function(_hX){if(E(_hX)==43){var _hY=function(_hZ){return C > 19 ? new F(function(){return A1(_hR,new T1(1,new T(function(){return _hN(_hh,_hZ);})));}) : (++C,A1(_hR,new T1(1,new T(function(){return _hN(_hh,_hZ);}))));};return new T1(1,_g4(10,_hY));}else{return new T0(2);}},_i0=function(_i1){if(E(_i1)==45){var _i2=function(_i3){return C > 19 ? new F(function(){return A1(_hR,new T1(1,new T(function(){return _hd(_hN(_hh,_i3));})));}) : (++C,A1(_hR,new T1(1,new T(function(){return _hd(_hN(_hh,_i3));}))));};return new T1(1,_g4(10,_i2));}else{return new T0(2);}};return _eh(_eh(new T1(0,_i0),new T1(0,_hW)),_hT);});return _eh(new T1(0,function(_i4){return (E(_i4)==101)?E(_hS):new T0(2);}),new T1(0,function(_i5){return (E(_i5)==69)?E(_hS):new T0(2);}));},_i6=function(_i7){var _i8=function(_i9){return C > 19 ? new F(function(){return A1(_i7,new T1(1,_i9));}) : (++C,A1(_i7,new T1(1,_i9)));};return function(_ia){return (E(_ia)==46)?new T1(1,_g4(10,_i8)):new T0(2);};},_ib=function(_ic){return new T1(0,_i6(_ic));},_id=function(_ie){var _if=function(_ig){var _ih=function(_ii){return new T1(1,_fp(_hQ,_gZ,function(_ij){return C > 19 ? new F(function(){return A1(_ie,new T1(5,new T3(1,_ig,_ii,_ij)));}) : (++C,A1(_ie,new T1(5,new T3(1,_ig,_ii,_ij))));}));};return new T1(1,_fp(_ib,_h1,_ih));};return _g4(10,_if);},_ik=function(_il){return new T1(1,_id(_il));},_im=function(_in,_io,_ip){while(1){var _iq=E(_ip);if(!_iq._){return false;}else{if(!B(A3(_1F,_in,_io,_iq.a))){_ip=_iq.b;continue;}else{return true;}}}},_ir=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_is=function(_it){return _im(_eS,_it,_ir);},_iu=function(_iv){var _iw=new T(function(){return B(A1(_iv,8));}),_ix=new T(function(){return B(A1(_iv,16));});return function(_iy){switch(E(_iy)){case 79:return E(_iw);case 88:return E(_ix);case 111:return E(_iw);case 120:return E(_ix);default:return new T0(2);}};},_iz=function(_iA){return new T1(0,_iu(_iA));},_iB=function(_iC){return C > 19 ? new F(function(){return A1(_iC,10);}) : (++C,A1(_iC,10));},_iD=function(_iE,_iF){var _iG=jsShowI(_iE);return _0(fromJSStr(_iG),_iF);},_iH=function(_iI,_iJ,_iK){if(_iJ>=0){return _iD(_iJ,_iK);}else{if(_iI<=6){return _iD(_iJ,_iK);}else{return new T2(1,40,new T(function(){var _iL=jsShowI(_iJ);return _0(fromJSStr(_iL),new T2(1,41,_iK));}));}}},_iM=function(_iN){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _iH(9,_iN,__Z);})));},_iO=function(_iP,_iQ){var _iR=E(_iP);if(!_iR._){var _iS=_iR.a,_iT=E(_iQ);return (_iT._==0)?_iS<=_iT.a:I_compareInt(_iT.a,_iS)>=0;}else{var _iU=_iR.a,_iV=E(_iQ);return (_iV._==0)?I_compareInt(_iU,_iV.a)<=0:I_compare(_iU,_iV.a)<=0;}},_iW=function(_iX){return new T0(2);},_iY=function(_iZ){var _j0=E(_iZ);if(!_j0._){return _iW;}else{var _j1=_j0.a,_j2=E(_j0.b);if(!_j2._){return E(_j1);}else{var _j3=new T(function(){return _iY(_j2);}),_j4=function(_j5){return _eh(B(A1(_j1,_j5)),new T(function(){return B(A1(_j3,_j5));}));};return _j4;}}},_j6=function(_j7,_j8){var _j9=function(_ja,_jb,_jc){var _jd=E(_ja);if(!_jd._){return C > 19 ? new F(function(){return A1(_jc,_j7);}) : (++C,A1(_jc,_j7));}else{var _je=E(_jb);if(!_je._){return new T0(2);}else{if(E(_jd.a)!=E(_je.a)){return new T0(2);}else{var _jf=new T(function(){return B(_j9(_jd.b,_je.b,_jc));});return new T1(0,function(_jg){return E(_jf);});}}}};return function(_jh){return C > 19 ? new F(function(){return _j9(_j7,_jh,_j8);}) : (++C,_j9(_j7,_jh,_j8));};},_ji=new T(function(){return unCStr("SO");}),_jj=function(_jk){var _jl=new T(function(){return B(A1(_jk,14));});return new T1(1,_j6(_ji,function(_jm){return E(_jl);}));},_jn=new T(function(){return unCStr("SOH");}),_jo=function(_jp){var _jq=new T(function(){return B(A1(_jp,1));});return new T1(1,_j6(_jn,function(_jr){return E(_jq);}));},_js=new T(function(){return unCStr("NUL");}),_jt=function(_ju){var _jv=new T(function(){return B(A1(_ju,0));});return new T1(1,_j6(_js,function(_jw){return E(_jv);}));},_jx=new T(function(){return unCStr("STX");}),_jy=function(_jz){var _jA=new T(function(){return B(A1(_jz,2));});return new T1(1,_j6(_jx,function(_jB){return E(_jA);}));},_jC=new T(function(){return unCStr("ETX");}),_jD=function(_jE){var _jF=new T(function(){return B(A1(_jE,3));});return new T1(1,_j6(_jC,function(_jG){return E(_jF);}));},_jH=new T(function(){return unCStr("EOT");}),_jI=function(_jJ){var _jK=new T(function(){return B(A1(_jJ,4));});return new T1(1,_j6(_jH,function(_jL){return E(_jK);}));},_jM=new T(function(){return unCStr("ENQ");}),_jN=function(_jO){var _jP=new T(function(){return B(A1(_jO,5));});return new T1(1,_j6(_jM,function(_jQ){return E(_jP);}));},_jR=new T(function(){return unCStr("ACK");}),_jS=function(_jT){var _jU=new T(function(){return B(A1(_jT,6));});return new T1(1,_j6(_jR,function(_jV){return E(_jU);}));},_jW=new T(function(){return unCStr("BEL");}),_jX=function(_jY){var _jZ=new T(function(){return B(A1(_jY,7));});return new T1(1,_j6(_jW,function(_k0){return E(_jZ);}));},_k1=new T(function(){return unCStr("BS");}),_k2=function(_k3){var _k4=new T(function(){return B(A1(_k3,8));});return new T1(1,_j6(_k1,function(_k5){return E(_k4);}));},_k6=new T(function(){return unCStr("HT");}),_k7=function(_k8){var _k9=new T(function(){return B(A1(_k8,9));});return new T1(1,_j6(_k6,function(_ka){return E(_k9);}));},_kb=new T(function(){return unCStr("LF");}),_kc=function(_kd){var _ke=new T(function(){return B(A1(_kd,10));});return new T1(1,_j6(_kb,function(_kf){return E(_ke);}));},_kg=new T(function(){return unCStr("VT");}),_kh=function(_ki){var _kj=new T(function(){return B(A1(_ki,11));});return new T1(1,_j6(_kg,function(_kk){return E(_kj);}));},_kl=new T(function(){return unCStr("FF");}),_km=function(_kn){var _ko=new T(function(){return B(A1(_kn,12));});return new T1(1,_j6(_kl,function(_kp){return E(_ko);}));},_kq=new T(function(){return unCStr("CR");}),_kr=function(_ks){var _kt=new T(function(){return B(A1(_ks,13));});return new T1(1,_j6(_kq,function(_ku){return E(_kt);}));},_kv=new T(function(){return unCStr("SI");}),_kw=function(_kx){var _ky=new T(function(){return B(A1(_kx,15));});return new T1(1,_j6(_kv,function(_kz){return E(_ky);}));},_kA=new T(function(){return unCStr("DLE");}),_kB=function(_kC){var _kD=new T(function(){return B(A1(_kC,16));});return new T1(1,_j6(_kA,function(_kE){return E(_kD);}));},_kF=new T(function(){return unCStr("DC1");}),_kG=function(_kH){var _kI=new T(function(){return B(A1(_kH,17));});return new T1(1,_j6(_kF,function(_kJ){return E(_kI);}));},_kK=new T(function(){return unCStr("DC2");}),_kL=function(_kM){var _kN=new T(function(){return B(A1(_kM,18));});return new T1(1,_j6(_kK,function(_kO){return E(_kN);}));},_kP=new T(function(){return unCStr("DC3");}),_kQ=function(_kR){var _kS=new T(function(){return B(A1(_kR,19));});return new T1(1,_j6(_kP,function(_kT){return E(_kS);}));},_kU=new T(function(){return unCStr("DC4");}),_kV=function(_kW){var _kX=new T(function(){return B(A1(_kW,20));});return new T1(1,_j6(_kU,function(_kY){return E(_kX);}));},_kZ=new T(function(){return unCStr("NAK");}),_l0=function(_l1){var _l2=new T(function(){return B(A1(_l1,21));});return new T1(1,_j6(_kZ,function(_l3){return E(_l2);}));},_l4=new T(function(){return unCStr("SYN");}),_l5=function(_l6){var _l7=new T(function(){return B(A1(_l6,22));});return new T1(1,_j6(_l4,function(_l8){return E(_l7);}));},_l9=new T(function(){return unCStr("ETB");}),_la=function(_lb){var _lc=new T(function(){return B(A1(_lb,23));});return new T1(1,_j6(_l9,function(_ld){return E(_lc);}));},_le=new T(function(){return unCStr("CAN");}),_lf=function(_lg){var _lh=new T(function(){return B(A1(_lg,24));});return new T1(1,_j6(_le,function(_li){return E(_lh);}));},_lj=new T(function(){return unCStr("EM");}),_lk=function(_ll){var _lm=new T(function(){return B(A1(_ll,25));});return new T1(1,_j6(_lj,function(_ln){return E(_lm);}));},_lo=new T(function(){return unCStr("SUB");}),_lp=function(_lq){var _lr=new T(function(){return B(A1(_lq,26));});return new T1(1,_j6(_lo,function(_ls){return E(_lr);}));},_lt=new T(function(){return unCStr("ESC");}),_lu=function(_lv){var _lw=new T(function(){return B(A1(_lv,27));});return new T1(1,_j6(_lt,function(_lx){return E(_lw);}));},_ly=new T(function(){return unCStr("FS");}),_lz=function(_lA){var _lB=new T(function(){return B(A1(_lA,28));});return new T1(1,_j6(_ly,function(_lC){return E(_lB);}));},_lD=new T(function(){return unCStr("GS");}),_lE=function(_lF){var _lG=new T(function(){return B(A1(_lF,29));});return new T1(1,_j6(_lD,function(_lH){return E(_lG);}));},_lI=new T(function(){return unCStr("RS");}),_lJ=function(_lK){var _lL=new T(function(){return B(A1(_lK,30));});return new T1(1,_j6(_lI,function(_lM){return E(_lL);}));},_lN=new T(function(){return unCStr("US");}),_lO=function(_lP){var _lQ=new T(function(){return B(A1(_lP,31));});return new T1(1,_j6(_lN,function(_lR){return E(_lQ);}));},_lS=new T(function(){return unCStr("SP");}),_lT=function(_lU){var _lV=new T(function(){return B(A1(_lU,32));});return new T1(1,_j6(_lS,function(_lW){return E(_lV);}));},_lX=new T(function(){return unCStr("DEL");}),_lY=function(_lZ){var _m0=new T(function(){return B(A1(_lZ,127));});return new T1(1,_j6(_lX,function(_m1){return E(_m0);}));},_m2=new T(function(){return _iY(new T2(1,function(_m3){return new T1(1,_fp(_jo,_jj,_m3));},new T2(1,_jt,new T2(1,_jy,new T2(1,_jD,new T2(1,_jI,new T2(1,_jN,new T2(1,_jS,new T2(1,_jX,new T2(1,_k2,new T2(1,_k7,new T2(1,_kc,new T2(1,_kh,new T2(1,_km,new T2(1,_kr,new T2(1,_kw,new T2(1,_kB,new T2(1,_kG,new T2(1,_kL,new T2(1,_kQ,new T2(1,_kV,new T2(1,_l0,new T2(1,_l5,new T2(1,_la,new T2(1,_lf,new T2(1,_lk,new T2(1,_lp,new T2(1,_lu,new T2(1,_lz,new T2(1,_lE,new T2(1,_lJ,new T2(1,_lO,new T2(1,_lT,new T2(1,_lY,__Z))))))))))))))))))))))))))))))))));}),_m4=function(_m5){var _m6=new T(function(){return B(A1(_m5,7));}),_m7=new T(function(){return B(A1(_m5,8));}),_m8=new T(function(){return B(A1(_m5,9));}),_m9=new T(function(){return B(A1(_m5,10));}),_ma=new T(function(){return B(A1(_m5,11));}),_mb=new T(function(){return B(A1(_m5,12));}),_mc=new T(function(){return B(A1(_m5,13));}),_md=new T(function(){return B(A1(_m5,92));}),_me=new T(function(){return B(A1(_m5,39));}),_mf=new T(function(){return B(A1(_m5,34));}),_mg=new T(function(){var _mh=function(_mi){var _mj=new T(function(){return _3m(E(_mi));}),_mk=function(_ml){var _mm=_hN(_mj,_ml);if(!_iO(_mm,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_m5,new T(function(){var _mn=_3p(_mm);if(_mn>>>0>1114111){return _iM(_mn);}else{return _mn;}}));}) : (++C,A1(_m5,new T(function(){var _mn=_3p(_mm);if(_mn>>>0>1114111){return _iM(_mn);}else{return _mn;}})));}};return new T1(1,_g4(_mi,_mk));},_mo=new T(function(){var _mp=new T(function(){return B(A1(_m5,31));}),_mq=new T(function(){return B(A1(_m5,30));}),_mr=new T(function(){return B(A1(_m5,29));}),_ms=new T(function(){return B(A1(_m5,28));}),_mt=new T(function(){return B(A1(_m5,27));}),_mu=new T(function(){return B(A1(_m5,26));}),_mv=new T(function(){return B(A1(_m5,25));}),_mw=new T(function(){return B(A1(_m5,24));}),_mx=new T(function(){return B(A1(_m5,23));}),_my=new T(function(){return B(A1(_m5,22));}),_mz=new T(function(){return B(A1(_m5,21));}),_mA=new T(function(){return B(A1(_m5,20));}),_mB=new T(function(){return B(A1(_m5,19));}),_mC=new T(function(){return B(A1(_m5,18));}),_mD=new T(function(){return B(A1(_m5,17));}),_mE=new T(function(){return B(A1(_m5,16));}),_mF=new T(function(){return B(A1(_m5,15));}),_mG=new T(function(){return B(A1(_m5,14));}),_mH=new T(function(){return B(A1(_m5,6));}),_mI=new T(function(){return B(A1(_m5,5));}),_mJ=new T(function(){return B(A1(_m5,4));}),_mK=new T(function(){return B(A1(_m5,3));}),_mL=new T(function(){return B(A1(_m5,2));}),_mM=new T(function(){return B(A1(_m5,1));}),_mN=new T(function(){return B(A1(_m5,0));}),_mO=function(_mP){switch(E(_mP)){case 64:return E(_mN);case 65:return E(_mM);case 66:return E(_mL);case 67:return E(_mK);case 68:return E(_mJ);case 69:return E(_mI);case 70:return E(_mH);case 71:return E(_m6);case 72:return E(_m7);case 73:return E(_m8);case 74:return E(_m9);case 75:return E(_ma);case 76:return E(_mb);case 77:return E(_mc);case 78:return E(_mG);case 79:return E(_mF);case 80:return E(_mE);case 81:return E(_mD);case 82:return E(_mC);case 83:return E(_mB);case 84:return E(_mA);case 85:return E(_mz);case 86:return E(_my);case 87:return E(_mx);case 88:return E(_mw);case 89:return E(_mv);case 90:return E(_mu);case 91:return E(_mt);case 92:return E(_ms);case 93:return E(_mr);case 94:return E(_mq);case 95:return E(_mp);default:return new T0(2);}};return _eh(new T1(0,function(_mQ){return (E(_mQ)==94)?E(new T1(0,_mO)):new T0(2);}),new T(function(){return B(A1(_m2,_m5));}));});return _eh(new T1(1,_fp(_iz,_iB,_mh)),_mo);});return _eh(new T1(0,function(_mR){switch(E(_mR)){case 34:return E(_mf);case 39:return E(_me);case 92:return E(_md);case 97:return E(_m6);case 98:return E(_m7);case 102:return E(_mb);case 110:return E(_m9);case 114:return E(_mc);case 116:return E(_m8);case 118:return E(_ma);default:return new T0(2);}}),_mg);},_mS=function(_mT){return C > 19 ? new F(function(){return A1(_mT,0);}) : (++C,A1(_mT,0));},_mU=function(_mV){var _mW=E(_mV);if(!_mW._){return _mS;}else{var _mX=E(_mW.a),_mY=_mX>>>0,_mZ=new T(function(){return _mU(_mW.b);});if(_mY>887){var _n0=u_iswspace(_mX);if(!E(_n0)){return _mS;}else{var _n1=function(_n2){var _n3=new T(function(){return B(A1(_mZ,_n2));});return new T1(0,function(_n4){return E(_n3);});};return _n1;}}else{if(_mY==32){var _n5=function(_n6){var _n7=new T(function(){return B(A1(_mZ,_n6));});return new T1(0,function(_n8){return E(_n7);});};return _n5;}else{if(_mY-9>>>0>4){if(_mY==160){var _n9=function(_na){var _nb=new T(function(){return B(A1(_mZ,_na));});return new T1(0,function(_nc){return E(_nb);});};return _n9;}else{return _mS;}}else{var _nd=function(_ne){var _nf=new T(function(){return B(A1(_mZ,_ne));});return new T1(0,function(_ng){return E(_nf);});};return _nd;}}}}},_nh=function(_ni){var _nj=new T(function(){return B(_nh(_ni));}),_nk=function(_nl){return (E(_nl)==92)?E(_nj):new T0(2);},_nm=function(_nn){return E(new T1(0,_nk));},_no=new T1(1,function(_np){return C > 19 ? new F(function(){return A2(_mU,_np,_nm);}) : (++C,A2(_mU,_np,_nm));}),_nq=new T(function(){return B(_m4(function(_nr){return C > 19 ? new F(function(){return A1(_ni,new T2(0,_nr,true));}) : (++C,A1(_ni,new T2(0,_nr,true)));}));}),_ns=function(_nt){var _nu=E(_nt);if(_nu==38){return E(_nj);}else{var _nv=_nu>>>0;if(_nv>887){var _nw=u_iswspace(_nu);return (E(_nw)==0)?new T0(2):E(_no);}else{return (_nv==32)?E(_no):(_nv-9>>>0>4)?(_nv==160)?E(_no):new T0(2):E(_no);}}};return _eh(new T1(0,function(_nx){return (E(_nx)==92)?E(new T1(0,_ns)):new T0(2);}),new T1(0,function(_ny){var _nz=E(_ny);if(_nz==92){return E(_nq);}else{return C > 19 ? new F(function(){return A1(_ni,new T2(0,_nz,false));}) : (++C,A1(_ni,new T2(0,_nz,false)));}}));},_nA=function(_nB,_nC){var _nD=new T(function(){return B(A1(_nC,new T1(1,new T(function(){return B(A1(_nB,__Z));}))));}),_nE=function(_nF){var _nG=E(_nF),_nH=E(_nG.a);if(_nH==34){if(!E(_nG.b)){return E(_nD);}else{return C > 19 ? new F(function(){return _nA(function(_nI){return C > 19 ? new F(function(){return A1(_nB,new T2(1,_nH,_nI));}) : (++C,A1(_nB,new T2(1,_nH,_nI)));},_nC);}) : (++C,_nA(function(_nI){return C > 19 ? new F(function(){return A1(_nB,new T2(1,_nH,_nI));}) : (++C,A1(_nB,new T2(1,_nH,_nI)));},_nC));}}else{return C > 19 ? new F(function(){return _nA(function(_nJ){return C > 19 ? new F(function(){return A1(_nB,new T2(1,_nH,_nJ));}) : (++C,A1(_nB,new T2(1,_nH,_nJ)));},_nC);}) : (++C,_nA(function(_nJ){return C > 19 ? new F(function(){return A1(_nB,new T2(1,_nH,_nJ));}) : (++C,A1(_nB,new T2(1,_nH,_nJ)));},_nC));}};return C > 19 ? new F(function(){return _nh(_nE);}) : (++C,_nh(_nE));},_nK=new T(function(){return unCStr("_\'");}),_nL=function(_nM){var _nN=u_iswalnum(_nM);if(!E(_nN)){return _im(_eS,_nM,_nK);}else{return true;}},_nO=function(_nP){return _nL(E(_nP));},_nQ=new T(function(){return unCStr(",;()[]{}`");}),_nR=new T(function(){return unCStr("=>");}),_nS=new T(function(){return unCStr("~");}),_nT=new T(function(){return unCStr("@");}),_nU=new T(function(){return unCStr("->");}),_nV=new T(function(){return unCStr("<-");}),_nW=new T(function(){return unCStr("|");}),_nX=new T(function(){return unCStr("\\");}),_nY=new T(function(){return unCStr("=");}),_nZ=new T(function(){return unCStr("::");}),_o0=new T(function(){return unCStr("..");}),_o1=function(_o2){var _o3=new T(function(){return B(A1(_o2,new T0(6)));}),_o4=new T(function(){var _o5=new T(function(){var _o6=function(_o7){var _o8=new T(function(){return B(A1(_o2,new T1(0,_o7)));});return new T1(0,function(_o9){return (E(_o9)==39)?E(_o8):new T0(2);});};return B(_m4(_o6));}),_oa=function(_ob){var _oc=E(_ob);switch(_oc){case 39:return new T0(2);case 92:return E(_o5);default:var _od=new T(function(){return B(A1(_o2,new T1(0,_oc)));});return new T1(0,function(_oe){return (E(_oe)==39)?E(_od):new T0(2);});}},_of=new T(function(){var _og=new T(function(){return B(_nA(_1C,_o2));}),_oh=new T(function(){var _oi=new T(function(){var _oj=new T(function(){var _ok=function(_ol){var _om=E(_ol),_on=u_iswalpha(_om);return (E(_on)==0)?(_om==95)?new T1(1,_fP(_nO,function(_oo){return C > 19 ? new F(function(){return A1(_o2,new T1(3,new T2(1,_om,_oo)));}) : (++C,A1(_o2,new T1(3,new T2(1,_om,_oo))));})):new T0(2):new T1(1,_fP(_nO,function(_op){return C > 19 ? new F(function(){return A1(_o2,new T1(3,new T2(1,_om,_op)));}) : (++C,A1(_o2,new T1(3,new T2(1,_om,_op))));}));};return _eh(new T1(0,_ok),new T(function(){return new T1(1,_fp(_gX,_ik,_o2));}));}),_oq=function(_or){return (!_im(_eS,_or,_ir))?new T0(2):new T1(1,_fP(_is,function(_os){var _ot=new T2(1,_or,_os);if(!_im(new T2(0,_eX,_f2),_ot,new T2(1,_o0,new T2(1,_nZ,new T2(1,_nY,new T2(1,_nX,new T2(1,_nW,new T2(1,_nV,new T2(1,_nU,new T2(1,_nT,new T2(1,_nS,new T2(1,_nR,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_o2,new T1(4,_ot));}) : (++C,A1(_o2,new T1(4,_ot)));}else{return C > 19 ? new F(function(){return A1(_o2,new T1(2,_ot));}) : (++C,A1(_o2,new T1(2,_ot)));}}));};return _eh(new T1(0,_oq),_oj);});return _eh(new T1(0,function(_ou){if(!_im(_eS,_ou,_nQ)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_o2,new T1(2,new T2(1,_ou,__Z)));}) : (++C,A1(_o2,new T1(2,new T2(1,_ou,__Z))));}}),_oi);});return _eh(new T1(0,function(_ov){return (E(_ov)==34)?E(_og):new T0(2);}),_oh);});return _eh(new T1(0,function(_ow){return (E(_ow)==39)?E(new T1(0,_oa)):new T0(2);}),_of);});return _eh(new T1(1,function(_ox){return (E(_ox)._==0)?E(_o3):new T0(2);}),_o4);},_oy=function(_oz,_oA){var _oB=new T(function(){var _oC=new T(function(){var _oD=function(_oE){var _oF=new T(function(){var _oG=new T(function(){return B(A1(_oA,_oE));});return B(_o1(function(_oH){var _oI=E(_oH);return (_oI._==2)?(!_eN(_oI.a,_eM))?new T0(2):E(_oG):new T0(2);}));}),_oJ=function(_oK){return E(_oF);};return new T1(1,function(_oL){return C > 19 ? new F(function(){return A2(_mU,_oL,_oJ);}) : (++C,A2(_mU,_oL,_oJ));});};return B(A2(_oz,0,_oD));});return B(_o1(function(_oM){var _oN=E(_oM);return (_oN._==2)?(!_eN(_oN.a,_eL))?new T0(2):E(_oC):new T0(2);}));}),_oO=function(_oP){return E(_oB);};return function(_oQ){return C > 19 ? new F(function(){return A2(_mU,_oQ,_oO);}) : (++C,A2(_mU,_oQ,_oO));};},_oR=function(_oS,_oT){var _oU=function(_oV){var _oW=new T(function(){return B(A1(_oS,_oV));}),_oX=function(_oY){return _eh(B(A1(_oW,_oY)),new T(function(){return new T1(1,_oy(_oU,_oY));}));};return _oX;},_oZ=new T(function(){return B(A1(_oS,_oT));}),_p0=function(_p1){return _eh(B(A1(_oZ,_p1)),new T(function(){return new T1(1,_oy(_oU,_p1));}));};return _p0;},_p2=function(_p3,_p4){var _p5=function(_p6,_p7){var _p8=function(_p9){return C > 19 ? new F(function(){return A1(_p7,new T(function(){return  -E(_p9);}));}) : (++C,A1(_p7,new T(function(){return  -E(_p9);})));},_pa=new T(function(){return B(_o1(function(_pb){return C > 19 ? new F(function(){return A3(_p3,_pb,_p6,_p8);}) : (++C,A3(_p3,_pb,_p6,_p8));}));}),_pc=function(_pd){return E(_pa);},_pe=function(_pf){return C > 19 ? new F(function(){return A2(_mU,_pf,_pc);}) : (++C,A2(_mU,_pf,_pc));},_pg=new T(function(){return B(_o1(function(_ph){var _pi=E(_ph);if(_pi._==4){var _pj=E(_pi.a);if(!_pj._){return C > 19 ? new F(function(){return A3(_p3,_pi,_p6,_p7);}) : (++C,A3(_p3,_pi,_p6,_p7));}else{if(E(_pj.a)==45){if(!E(_pj.b)._){return E(new T1(1,_pe));}else{return C > 19 ? new F(function(){return A3(_p3,_pi,_p6,_p7);}) : (++C,A3(_p3,_pi,_p6,_p7));}}else{return C > 19 ? new F(function(){return A3(_p3,_pi,_p6,_p7);}) : (++C,A3(_p3,_pi,_p6,_p7));}}}else{return C > 19 ? new F(function(){return A3(_p3,_pi,_p6,_p7);}) : (++C,A3(_p3,_pi,_p6,_p7));}}));}),_pk=function(_pl){return E(_pg);};return new T1(1,function(_pm){return C > 19 ? new F(function(){return A2(_mU,_pm,_pk);}) : (++C,A2(_mU,_pm,_pk));});};return _oR(_p5,_p4);},_pn=function(_po){var _pp=E(_po);if(!_pp._){var _pq=_pp.b,_pr=new T(function(){return _hw(new T(function(){return _3m(E(_pp.a));}),new T(function(){return _hi(_pq,0);},1),_dz(_hn,_pq));});return new T1(1,_pr);}else{return (E(_pp.b)._==0)?(E(_pp.c)._==0)?new T1(1,new T(function(){return _hN(_hh,_pp.a);})):__Z:__Z;}},_ps=function(_pt,_pu){return new T0(2);},_pv=function(_pw){var _px=E(_pw);if(_px._==5){var _py=_pn(_px.a);if(!_py._){return _ps;}else{var _pz=new T(function(){return _3p(_py.a);});return function(_pA,_pB){return C > 19 ? new F(function(){return A1(_pB,_pz);}) : (++C,A1(_pB,_pz));};}}else{return _ps;}},_pC=function(_pD){return _p2(_pv,_pD);},_pE=new T(function(){return unCStr("[");}),_pF=function(_pG,_pH){var _pI=function(_pJ,_pK){var _pL=new T(function(){return B(A1(_pK,__Z));}),_pM=new T(function(){var _pN=function(_pO){return _pI(true,function(_pP){return C > 19 ? new F(function(){return A1(_pK,new T2(1,_pO,_pP));}) : (++C,A1(_pK,new T2(1,_pO,_pP)));});};return B(A2(_pG,0,_pN));}),_pQ=new T(function(){return B(_o1(function(_pR){var _pS=E(_pR);if(_pS._==2){var _pT=E(_pS.a);if(!_pT._){return new T0(2);}else{var _pU=_pT.b;switch(E(_pT.a)){case 44:return (E(_pU)._==0)?(!E(_pJ))?new T0(2):E(_pM):new T0(2);case 93:return (E(_pU)._==0)?E(_pL):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_pV=function(_pW){return E(_pQ);};return new T1(1,function(_pX){return C > 19 ? new F(function(){return A2(_mU,_pX,_pV);}) : (++C,A2(_mU,_pX,_pV));});},_pY=function(_pZ,_q0){return C > 19 ? new F(function(){return _q1(_q0);}) : (++C,_q1(_q0));},_q1=function(_q2){var _q3=new T(function(){var _q4=new T(function(){var _q5=new T(function(){var _q6=function(_q7){return _pI(true,function(_q8){return C > 19 ? new F(function(){return A1(_q2,new T2(1,_q7,_q8));}) : (++C,A1(_q2,new T2(1,_q7,_q8)));});};return B(A2(_pG,0,_q6));});return _eh(_pI(false,_q2),_q5);});return B(_o1(function(_q9){var _qa=E(_q9);return (_qa._==2)?(!_eN(_qa.a,_pE))?new T0(2):E(_q4):new T0(2);}));}),_qb=function(_qc){return E(_q3);};return _eh(new T1(1,function(_qd){return C > 19 ? new F(function(){return A2(_mU,_qd,_qb);}) : (++C,A2(_mU,_qd,_qb));}),new T(function(){return new T1(1,_oy(_pY,_q2));}));};return C > 19 ? new F(function(){return _q1(_pH);}) : (++C,_q1(_pH));},_qe=function(_qf){var _qg=function(_qh){return E(new T2(3,_qf,_fg));};return new T1(1,function(_qi){return C > 19 ? new F(function(){return A2(_mU,_qi,_qg);}) : (++C,A2(_mU,_qi,_qg));});},_qj=new T(function(){return B(_pF(_pC,_qe));}),_qk=new T(function(){return unCStr("Prelude.read: ambiguous parse");}),_ql=new T(function(){return unCStr("Prelude.read: no parse");}),_qm=function(_qn){while(1){var _qo=(function(_qp){var _qq=E(_qp);if(!_qq._){return __Z;}else{var _qr=_qq.b,_qs=E(_qq.a);if(!E(_qs.b)._){return new T2(1,_qs.a,new T(function(){return _qm(_qr);}));}else{_qn=_qr;return __continue;}}})(_qn);if(_qo!=__continue){return _qo;}}},_qt=function(_qu,_qv,_){var _qw=new T(function(){var _qx=_qm(_e7(_qj,new T(function(){return fromJSStr(E(_qu));})));if(!_qx._){return err(_ql);}else{if(!E(_qx.b)._){return E(_qx.a);}else{return err(_qk);}}}),_qy=E(_qv);if(_qy._==3){var _qz=E(_qy.a);if(!_qz._){var _qA=_aj(_);return new T2(0,_qw,_qA);}else{var _qB=E(_qz.a);if(_qB._==3){if(!E(_qz.b)._){var _qC=_6K("Array"),_qD=_al(_dz(_dP,_qB.a),_);return new T2(0,_qw,new T2(1,_qD,__Z));}else{var _qE=_aj(_);return new T2(0,_qw,_qE);}}else{var _qF=_aj(_);return new T2(0,_qw,_qF);}}}else{var _qG=_aj(_);return new T2(0,_qw,_qG);}},_qH=function(_qI,_){var _qJ=E(_qI);return _qt(_qJ.a,_qJ.b,_);},_qK=function(_qL,_qM){var _qN=E(_qL);if(!_qN._){return __Z;}else{var _qO=_qN.a,_qP=E(_qM);return (_qP==1)?new T2(1,function(_){return _qH(_qO,_);},__Z):new T2(1,function(_){return _qH(_qO,_);},new T(function(){return _qK(_qN.b,_qP-1|0);}));}},_qQ=function(_){var _qR=_6K("Error decoding tree data");return _6J(_);},_qS=function(_qT,_){var _qU=E(_qT);if(!_qU._){return __Z;}else{var _qV=B(A1(_qU.a,_)),_qW=_qS(_qU.b,_);return new T2(1,_qV,_qW);}},_qX=new T(function(){return B(_do("Ajax.hs:(97,5)-(101,81)|function decodeMenu"));}),_qY=new T(function(){return _cG(new T1(0,new T(function(){return unCStr("Error decoding tree data");})),_ct);}),_qZ=function(_r0,_r1,_r2){return C > 19 ? new F(function(){return A1(_r0,new T2(1,44,new T(function(){return B(A1(_r1,_r2));})));}) : (++C,A1(_r0,new T2(1,44,new T(function(){return B(A1(_r1,_r2));}))));},_r3=new T(function(){return unCStr("}");}),_r4=new T(function(){return unCStr(", ");}),_r5=new T(function(){return unCStr(": empty list");}),_r6=function(_r7){return err(_0(_bb,new T(function(){return _0(_r7,_r5);},1)));},_r8=new T(function(){return _r6(new T(function(){return unCStr("foldr1");}));}),_r9=function(_ra,_rb){var _rc=E(_rb);if(!_rc._){return E(_r8);}else{var _rd=_rc.a,_re=E(_rc.b);if(!_re._){return E(_rd);}else{return C > 19 ? new F(function(){return A2(_ra,_rd,new T(function(){return B(_r9(_ra,_re));}));}) : (++C,A2(_ra,_rd,new T(function(){return B(_r9(_ra,_re));})));}}},_rf=new T(function(){return unCStr("tree = ");}),_rg=new T(function(){return unCStr("lin = ");}),_rh=new T(function(){return unCStr("cost = ");}),_ri=new T(function(){return unCStr("T {");}),_rj=function(_rk,_rl){return new T2(1,34,new T(function(){return _cd(_rk,new T2(1,34,_rl));}));},_rm=function(_rn,_ro){return _iH(0,E(_rn),_ro);},_rp=function(_rq,_rr){return _2P(_rm,_rq,_rr);},_rs=function(_rt,_ru,_rv,_rw,_rx){var _ry=function(_rz){var _rA=new T(function(){var _rB=new T(function(){var _rC=new T(function(){var _rD=new T(function(){var _rE=new T(function(){var _rF=new T(function(){var _rG=new T(function(){var _rH=new T(function(){return _cd(_rw,new T2(1,34,new T(function(){return _0(_r3,_rz);})));});return _0(_rf,new T2(1,34,_rH));},1);return _0(_r4,_rG);}),_rI=E(_rv);if(!_rI._){return unAppCStr("[]",_rF);}else{var _rJ=new T(function(){var _rK=E(_rI.a),_rL=new T(function(){var _rM=new T(function(){var _rN=function(_rO){var _rP=E(_rO);if(!_rP._){return E(new T2(1,93,_rF));}else{var _rQ=new T(function(){var _rR=E(_rP.a),_rS=new T(function(){return B(A3(_r9,_qZ,new T2(1,function(_rT){return _rp(_rR.a,_rT);},new T2(1,function(_rU){return _rj(_rR.b,_rU);},__Z)),new T2(1,41,new T(function(){return _rN(_rP.b);}))));});return new T2(1,40,_rS);});return new T2(1,44,_rQ);}};return _rN(_rI.b);});return B(A3(_r9,_qZ,new T2(1,function(_rV){return _rp(_rK.a,_rV);},new T2(1,function(_rW){return _rj(_rK.b,_rW);},__Z)),new T2(1,41,_rM)));});return new T2(1,40,_rL);});return new T2(1,91,_rJ);}},1);return _0(_rg,_rE);},1);return _0(_r4,_rD);});return _iH(0,E(_ru),_rC);},1);return _0(_rh,_rB);},1);return _0(_ri,_rA);};if(_rt<11){return _ry(_rx);}else{return new T2(1,40,new T(function(){return _ry(new T2(1,41,_rx));}));}},_rX=function(_rY,_rZ){var _s0=E(_rY);return _rs(0,_s0.a,_s0.b,_s0.c,_rZ);},_s1=function(_cx,_cy){return _2P(_rX,_cx,_cy);},_s2=function(_s3,_s4){return _2P(_s1,_s3,_s4);},_s5=function(_s6,_s7){var _s8=E(_s6),_s9=new T(function(){return B(A3(_r9,_qZ,new T2(1,function(_sa){return _rp(_s8.a,_sa);},new T2(1,function(_sb){return _s2(_s8.b,_sb);},__Z)),new T2(1,41,_s7)));});return new T2(1,40,_s9);},_sc=function(_sd,_){var _se=E(_sd);if(_se._==4){var _sf=_se.a,_sg=_aZ(_1L,"lin",_sf);if(!_sg._){return E(_aY);}else{var _sh=function(_,_si){var _sj=_aZ(_1L,"menu",_sf);if(!_sj._){return E(_aY);}else{var _sk=E(_sj.a);if(_sk._==4){var _sl=_sk.a,_sm=_hi(_sl,0),_sn=function(_,_so){var _sp=_6K(toJSStr(unAppCStr("### ",new T(function(){return _2P(_s5,_so,__Z);})))),_sq=_aZ(_1L,"grammar",_sf);if(!_sq._){var _sr=_qQ(_);return E(_qY);}else{var _ss=_aZ(_1L,"tree",_sf);if(!_ss._){var _st=_qQ(_);return E(_qY);}else{return new T4(0,new T(function(){var _su=E(_sq.a);if(_su._==1){return fromJSStr(_su.a);}else{return E(_dO);}}),new T(function(){var _sv=E(_ss.a);if(_sv._==1){return fromJSStr(_sv.a);}else{return E(_dO);}}),_si,new T1(0,new T(function(){var _sw=E(_so);if(!_sw._){return new T0(1);}else{return B(_ac(_sw));}})));}}};if(0>=_sm){var _sx=_qS(__Z,_);return _sn(_,_sx);}else{var _sy=_qS(_qK(_sl,_sm),_);return _sn(_,_sy);}}else{return E(_qX);}}},_sz=E(_sg.a);if(_sz._==3){return _sh(_,new T(function(){return _dz(_dK,_sz.a);}));}else{return _sh(_,__Z);}}}else{return E(_aY);}},_sA=function(_sB){var _sC=E(_sB);return (_sC._==0)?E(_aY):E(_sC.a);},_sD=new T(function(){return _cG(new T1(0,new T(function(){return unCStr("Error decoding message data");})),_ct);}),_sE=new T(function(){return fromJSStr("Invalid JSON!");}),_sF=new T(function(){return _cG(new T1(0,_sE),_ct);}),_sG=new T(function(){return unAppCStr("Error ",_sE);}),_sH=new T(function(){return B(_do("Ajax.hs:131:5-35|function getJustBool"));}),_sI=function(_sJ,_){var _sK=jsParseJSON(_sJ);if(!_sK._){var _sL=_6K(toJSStr(E(_sG)));return E(_sF);}else{var _sM=_sK.a,_sN=E(_sM);if(_sN._==4){var _sO=_aZ(_1L,"a",_sN.a);}else{var _sO=__Z;}var _sP=_sc(_sA(_sO),_),_sQ=_sP;if(_sM._==4){var _sR=_aZ(_1L,"b",_sM.a);}else{var _sR=__Z;}var _sS=_sc(_sA(_sR),_);if(_sM._==4){var _sT=_sM.a,_sU=_aZ(_1L,"success",_sT);if(!_sU._){var _sV=_6L(_);return E(_sD);}else{var _sW=_aZ(_1L,"score",_sT);if(!_sW._){var _sX=_6L(_);return E(_sD);}else{if(!E(_sO)._){var _sY=_6L(_);return E(_sD);}else{if(!E(_sR)._){var _sZ=_6L(_);return E(_sD);}else{return new T4(0,new T(function(){var _t0=E(_sU.a);if(_t0._==2){return E(_t0.a);}else{return E(_sH);}}),new T(function(){var _t1=E(_sW.a);if(!_t1._){var _t2=_6x(_3A,_t1.a),_t3=_t2.a;if(E(_t2.b)>=0){return E(_t3);}else{return E(_t3)-1|0;}}else{return E(_dN);}}),_sQ,_sS);}}}}}else{var _t4=_6L(_);return E(_sD);}}},_t5=function(_t6){var _t7=_ar(__Z,_t6),_t8=jsCat(new T2(1,_t7.a,_t7.b),E(_aR));return E(_t8);},_t9=function(_ta,_tb){return new T2(1,new T2(0,"grammar",new T(function(){return new T1(1,toJSStr(E(_ta)));})),new T2(1,new T2(0,"tree",new T(function(){return new T1(1,toJSStr(E(_tb)));})),__Z));},_tc=function(_td){var _te=E(_td);return new T1(4,E(_t9(_te.a,_te.b)));},_tf=function(_tg){var _th=E(_tg);if(!_th._){return _t5(new T0(5));}else{return _t5(new T1(4,E(new T2(1,new T2(0,"score",new T(function(){return new T1(0,E(_th.a));})),new T2(1,new T2(0,"a",new T(function(){return _tc(_th.b);})),new T2(1,new T2(0,"b",new T(function(){return _tc(_th.c);})),__Z))))));}},_ti=function(_tj){return E(E(_tj).a);},_tk=function(_tl,_tm,_tn,_to,_tp){return C > 19 ? new F(function(){return A2(_tm,_tn,new T2(1,B(A2(_ti,_tl,E(_tp))),E(_to)));}) : (++C,A2(_tm,_tn,new T2(1,B(A2(_ti,_tl,E(_tp))),E(_to))));},_tq=function(_tr){return E(E(_tr).a);},_ts=function(_tt){return E(E(_tt).a);},_tu=function(_tv){return E(E(_tv).a);},_tw=function(_tx){return E(E(_tx).b);},_ty=new T(function(){return unCStr("base");}),_tz=new T(function(){return unCStr("GHC.IO.Exception");}),_tA=new T(function(){return unCStr("IOException");}),_tB=function(_tC){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_ty,_tz,_tA),__Z,__Z));},_tD=new T(function(){return unCStr(": ");}),_tE=new T(function(){return unCStr(")");}),_tF=new T(function(){return unCStr(" (");}),_tG=new T(function(){return unCStr("interrupted");}),_tH=new T(function(){return unCStr("system error");}),_tI=new T(function(){return unCStr("unsatisified constraints");}),_tJ=new T(function(){return unCStr("user error");}),_tK=new T(function(){return unCStr("permission denied");}),_tL=new T(function(){return unCStr("illegal operation");}),_tM=new T(function(){return unCStr("end of file");}),_tN=new T(function(){return unCStr("resource exhausted");}),_tO=new T(function(){return unCStr("resource busy");}),_tP=new T(function(){return unCStr("does not exist");}),_tQ=new T(function(){return unCStr("already exists");}),_tR=new T(function(){return unCStr("resource vanished");}),_tS=new T(function(){return unCStr("timeout");}),_tT=new T(function(){return unCStr("unsupported operation");}),_tU=new T(function(){return unCStr("hardware fault");}),_tV=new T(function(){return unCStr("inappropriate type");}),_tW=new T(function(){return unCStr("invalid argument");}),_tX=new T(function(){return unCStr("failed");}),_tY=new T(function(){return unCStr("protocol error");}),_tZ=function(_u0,_u1){switch(E(_u0)){case 0:return _0(_tQ,_u1);case 1:return _0(_tP,_u1);case 2:return _0(_tO,_u1);case 3:return _0(_tN,_u1);case 4:return _0(_tM,_u1);case 5:return _0(_tL,_u1);case 6:return _0(_tK,_u1);case 7:return _0(_tJ,_u1);case 8:return _0(_tI,_u1);case 9:return _0(_tH,_u1);case 10:return _0(_tY,_u1);case 11:return _0(_tX,_u1);case 12:return _0(_tW,_u1);case 13:return _0(_tV,_u1);case 14:return _0(_tU,_u1);case 15:return _0(_tT,_u1);case 16:return _0(_tS,_u1);case 17:return _0(_tR,_u1);default:return _0(_tG,_u1);}},_u2=new T(function(){return unCStr("}");}),_u3=new T(function(){return unCStr("{handle: ");}),_u4=function(_u5,_u6,_u7,_u8,_u9,_ua){var _ub=new T(function(){var _uc=new T(function(){var _ud=new T(function(){var _ue=E(_u8);if(!_ue._){return E(_ua);}else{var _uf=new T(function(){return _0(_ue,new T(function(){return _0(_tE,_ua);},1));},1);return _0(_tF,_uf);}},1);return _tZ(_u6,_ud);}),_ug=E(_u7);if(!_ug._){return E(_uc);}else{return _0(_ug,new T(function(){return _0(_tD,_uc);},1));}}),_uh=E(_u9);if(!_uh._){var _ui=E(_u5);if(!_ui._){return E(_ub);}else{var _uj=E(_ui.a);if(!_uj._){var _uk=new T(function(){var _ul=new T(function(){return _0(_u2,new T(function(){return _0(_tD,_ub);},1));},1);return _0(_uj.a,_ul);},1);return _0(_u3,_uk);}else{var _um=new T(function(){var _un=new T(function(){return _0(_u2,new T(function(){return _0(_tD,_ub);},1));},1);return _0(_uj.a,_un);},1);return _0(_u3,_um);}}}else{return _0(_uh.a,new T(function(){return _0(_tD,_ub);},1));}},_uo=function(_up){var _uq=E(_up);return _u4(_uq.a,_uq.b,_uq.c,_uq.d,_uq.f,__Z);},_ur=function(_us,_ut){var _uu=E(_us);return _u4(_uu.a,_uu.b,_uu.c,_uu.d,_uu.f,_ut);},_uv=new T(function(){return new T5(0,_tB,new T3(0,function(_uw,_ux,_uy){var _uz=E(_ux);return _u4(_uz.a,_uz.b,_uz.c,_uz.d,_uz.f,_uy);},_uo,function(_uA,_uB){return _2P(_ur,_uA,_uB);}),_uC,function(_uD){var _uE=E(_uD);return _2w(_2u(_uE.a),_tB,_uE.b);},_uo);}),_uC=function(_uF){return new T2(0,_uv,_uF);},_uG=function(_uH,_){var _uI=_uH["type"],_uJ=String(_uI),_uK=strEq(_uJ,"network");if(!E(_uK)){var _uL=strEq(_uJ,"http");if(!E(_uL)){var _uM=new T(function(){var _uN=new T(function(){return unAppCStr("unknown type of ajax error: ",new T(function(){return fromJSStr(_uJ);}));});return _uC(new T6(0,__Z,7,__Z,_uN,__Z,__Z));});return die(_uM);}else{var _uO=_uH["status"],_uP=_uH["status-text"];return new T2(1,new T(function(){var _uQ=Number(_uO);return jsTrunc(_uQ);}),new T(function(){return String(_uP);}));}}else{return __Z;}},_uR=function(_uS,_){var _uT=E(_uS);if(!_uT._){return __Z;}else{var _uU=_uG(E(_uT.a),_),_uV=_uR(_uT.b,_);return new T2(1,_uU,_uV);}},_uW=function(_uX,_){var _uY=__arr2lst(0,_uX);return _uR(_uY,_);},_uZ=new T2(0,function(_v0,_){return _uG(E(_v0),_);},function(_v1,_){return _uW(E(_v1),_);}),_v2=function(_v3){return E(E(_v3).a);},_v4=function(_v5){var _v6=B(A1(_v5,_));return E(_v6);},_v7=new T(function(){return _v4(function(_){return __jsNull();});}),_v8=function(_v9,_va,_){var _vb=__eq(_va,E(_v7));if(!E(_vb)){var _vc=__isUndef(_va);if(!E(_vc)){var _vd=B(A3(_v2,_v9,_va,_));return new T1(1,_vd);}else{return __Z;}}else{return __Z;}},_ve=function(_vf,_vg,_){var _vh=__arr2lst(0,_vg),_vi=function(_vj,_){var _vk=E(_vj);if(!_vk._){return __Z;}else{var _vl=_vk.b,_vm=E(_vk.a),_vn=__eq(_vm,E(_v7));if(!E(_vn)){var _vo=__isUndef(_vm);if(!E(_vo)){var _vp=B(A3(_v2,_vf,_vm,_)),_vq=_vi(_vl,_);return new T2(1,new T1(1,_vp),_vq);}else{var _vr=_vi(_vl,_);return new T2(1,__Z,_vr);}}else{var _vs=_vi(_vl,_);return new T2(1,__Z,_vs);}}};return _vi(_vh,_);},_vt=new T2(0,function(_vu,_){return _v8(_uZ,E(_vu),_);},function(_vv,_){return _ve(_uZ,E(_vv),_);}),_vw=function(_vx,_vy,_){var _vz=B(A2(_vx,new T(function(){var _vA=E(_vy),_vB=__eq(_vA,E(_v7));if(!E(_vB)){var _vC=__isUndef(_vA);if(!E(_vC)){return new T1(1,_vA);}else{return __Z;}}else{return __Z;}}),_));return _v7;},_vD=new T2(0,_vw,function(_vE){return 2;}),_vF=function(_vG){return E(E(_vG).a);},_vH=function(_vI,_vJ,_vK,_vL){var _vM=new T(function(){return B(A1(_vK,new T(function(){var _vN=B(A3(_v2,_vI,_vL,_));return E(_vN);})));});return C > 19 ? new F(function(){return A2(_vF,_vJ,_vM);}) : (++C,A2(_vF,_vJ,_vM));},_vO=function(_vP){return E(E(_vP).b);},_vQ=new T(function(){return err(new T(function(){return unCStr("Prelude.undefined");}));}),_vR=function(_vS,_vT,_vU){var _vV=__createJSFunc(1+B(A2(_vO,_vT,new T(function(){return B(A1(_vU,_vQ));})))|0,function(_vW){return C > 19 ? new F(function(){return _vH(_vS,_vT,_vU,_vW);}) : (++C,_vH(_vS,_vT,_vU,_vW));});return E(_vV);},_vX=function(_vY,_vZ,_w0){return _vR(_vY,_vZ,_w0);},_w1=function(_w2,_w3,_w4){var _w5=__lst2arr(_dz(function(_w6){return _vX(_w2,_w3,_w6);},_w4));return E(_w5);},_w7=new T2(0,function(_w8){return _vR(_vt,_vD,_w8);},function(_w9){return _w1(_vt,_vD,_w9);}),_wa=function(_wb,_){var _wc=E(_wb);if(!_wc._){return __Z;}else{var _wd=_wa(_wc.b,_);return new T2(1,0,_wd);}},_we=function(_wf,_){var _wg=__arr2lst(0,_wf);return _wa(_wg,_);},_wh=function(_wi,_){return _we(E(_wi),_);},_wj=function(_wk,_){return _6J(_);},_wl=function(_wm,_wn,_wo,_){var _wp=__apply(_wn,E(_wo));return C > 19 ? new F(function(){return A3(_v2,_wm,_wp,_);}) : (++C,A3(_v2,_wm,_wp,_));},_wq=function(_wr,_ws,_wt,_){return C > 19 ? new F(function(){return _wl(_wr,E(_ws),_wt,_);}) : (++C,_wl(_wr,E(_ws),_wt,_));},_wu=function(_wv,_ww,_wx,_){return C > 19 ? new F(function(){return _wq(_wv,_ww,_wx,_);}) : (++C,_wq(_wv,_ww,_wx,_));},_wy=function(_wz,_wA,_){return C > 19 ? new F(function(){return _wu(new T2(0,_wj,_wh),_wz,_wA,_);}) : (++C,_wu(new T2(0,_wj,_wh),_wz,_wA,_));},_wB=function(_wC){return E(E(_wC).c);},_wD=(function(method, uri, mimeout, responseType, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, uri);xhr.responseType = responseType;if(mimeout != '') {xhr.setRequestHeader('Content-type', mimeout);}xhr.addEventListener('load', function() {if(xhr.status < 400) {cb(null, xhr.response);}else {cb({'type':'http', 'status':xhr.status, 'status-text': xhr.statusText}, null);}});xhr.addEventListener('error', function() {if(xhr.status != 0) {cb({'type':'http', 'status':xhr.status, 'status-text': xhr.statusText}, null);} else {cb({'type':'network'}, null);}});xhr.send(postdata);}),_wE=function(_wF){return E(E(_wF).b);},_wG=function(_wH){return E(E(_wH).b);},_wI=new T(function(){return B(_do("src/Haste/Ajax.hs:(61,7)-(63,60)|case"));}),_wJ=function(_wK){return E(E(_wK).c);},_wL=new T1(1,__Z),_wM=function(_){return nMV(_wL);},_wN=new T0(2),_wO=function(_wP,_wQ,_wR){var _wS=function(_wT){var _wU=function(_){var _wV=E(_wQ),_wW=rMV(_wV),_wX=E(_wW);if(!_wX._){var _wY=new T(function(){var _wZ=new T(function(){return B(A1(_wT,0));});return _0(_wX.b,new T2(1,new T2(0,_wR,function(_x0){return E(_wZ);}),__Z));}),_=wMV(_wV,new T2(0,_wX.a,_wY));return _wN;}else{var _x1=E(_wX.a);if(!_x1._){var _=wMV(_wV,new T2(0,_wR,__Z));return new T(function(){return B(A1(_wT,0));});}else{var _=wMV(_wV,new T1(1,_x1.b));return new T1(1,new T2(1,new T(function(){return B(A1(_wT,0));}),new T2(1,new T(function(){return B(A2(_x1.a,_wR,_1v));}),__Z)));}}};return new T1(0,_wU);};return C > 19 ? new F(function(){return A2(_wE,_wP,_wS);}) : (++C,A2(_wE,_wP,_wS));},_x2=function(_x3){return E(E(_x3).d);},_x4=function(_x5,_x6){var _x7=function(_x8){var _x9=function(_){var _xa=E(_x6),_xb=rMV(_xa),_xc=E(_xb);if(!_xc._){var _xd=_xc.a,_xe=E(_xc.b);if(!_xe._){var _=wMV(_xa,_wL);return new T(function(){return B(A1(_x8,_xd));});}else{var _xf=E(_xe.a),_=wMV(_xa,new T2(0,_xf.a,_xe.b));return new T1(1,new T2(1,new T(function(){return B(A1(_x8,_xd));}),new T2(1,new T(function(){return B(A1(_xf.b,_1v));}),__Z)));}}else{var _xg=new T(function(){var _xh=function(_xi){var _xj=new T(function(){return B(A1(_x8,_xi));});return function(_xk){return E(_xj);};};return _0(_xc.a,new T2(1,_xh,__Z));}),_=wMV(_xa,new T1(1,_xg));return _wN;}};return new T1(0,_x9);};return C > 19 ? new F(function(){return A2(_wE,_x5,_x7);}) : (++C,A2(_wE,_x5,_x7));},_xl=function(_xm,_xn,_xo,_xp,_xq,_xr){var _xs=_ts(_xm),_xt=new T(function(){return _wE(_xm);}),_xu=new T(function(){return _wG(_xs);}),_xv=_tu(_xs),_xw=new T(function(){return _tw(_xo);}),_xx=new T(function(){var _xy=function(_xz){var _xA=E(_xp),_xB=strEq(E(_f),_xA);if(!E(_xB)){var _xC=_xA;}else{var _xC=B(A2(_wJ,_xn,0));}return function(_vW){return C > 19 ? new F(function(){return _tk(_w7,_wy,_wD,new T2(1,E(_v7),new T2(1,B(A2(_x2,_xo,0)),new T2(1,_xC,new T2(1,E(_xr),new T2(1,_xz,__Z))))),_vW);}) : (++C,_tk(_w7,_wy,_wD,new T2(1,E(_v7),new T2(1,B(A2(_x2,_xo,0)),new T2(1,_xC,new T2(1,E(_xr),new T2(1,_xz,__Z))))),_vW));};},_xD=function(_xE,_xF){var _xG=E(_xp),_xH=strEq(E(_f),_xG);if(!E(_xH)){var _xI=_xG;}else{var _xI=B(A2(_wJ,_xn,0));}return function(_vW){return C > 19 ? new F(function(){return _tk(_w7,_wy,_wD,new T2(1,E(_xE),new T2(1,B(A2(_x2,_xo,0)),new T2(1,_xI,new T2(1,E(_xr),new T2(1,_xF,__Z))))),_vW);}) : (++C,_tk(_w7,_wy,_wD,new T2(1,E(_xE),new T2(1,B(A2(_x2,_xo,0)),new T2(1,_xI,new T2(1,E(_xr),new T2(1,_xF,__Z))))),_vW));};},_xJ=E(_xq);switch(_xJ._){case 0:return _xy("GET");break;case 1:return _xy("DELETE");break;case 2:return _xD(new T(function(){return B(A2(_ti,_tq(_xn),_xJ.a));}),"POST");break;default:return _xD(new T(function(){return B(A2(_ti,_tq(_xn),_xJ.a));}),"PUT");}}),_xK=function(_xL){var _xM=new T(function(){return B(A1(_xt,new T(function(){return B(_x4(_1E,_xL));})));}),_xN=new T(function(){var _xO=new T(function(){var _xP=function(_xQ,_xR,_){var _xS=E(_xR);if(!_xS._){var _xT=E(_xQ);if(!_xT._){return E(_wI);}else{return _a(new T(function(){return B(A(_wO,[_1E,_xL,new T1(0,_xT.a),_1v]));}),__Z,_);}}else{var _xU=B(A3(_v2,_xw,_xS.a,_));return _a(new T(function(){return B(A(_wO,[_1E,_xL,new T1(1,_xU),_1v]));}),__Z,_);}};return B(A1(_xx,_xP));});return B(A1(_xu,_xO));});return C > 19 ? new F(function(){return A3(_wB,_xv,_xN,_xM);}) : (++C,A3(_wB,_xv,_xN,_xM));};return C > 19 ? new F(function(){return A3(_1g,_xv,new T(function(){return B(A2(_wG,_xs,_wM));}),_xK);}) : (++C,A3(_1g,_xv,new T(function(){return B(A2(_wG,_xs,_wM));}),_xK));},_xV=new T(function(){return err(new T(function(){return unCStr("AjaxError");}));}),_xW=function(_xX){var _xY=new T(function(){return _tf(_xX);}),_xZ=new T(function(){return toJSStr(unAppCStr("Send client message ",new T(function(){return fromJSStr(E(_xY));})));}),_y0=new T(function(){return B(_xl(_1E,_v,_v,_f,new T1(2,_xY),"http://localhost:8080/cgi"));}),_y1=function(_y2){var _y3=function(_){var _y4=_6K(E(_xZ));return new T(function(){var _y5=function(_y6){var _y7=E(_y6);if(!_y7._){return E(_xV);}else{var _y8=_y7.a,_y9=function(_){var _ya=_6K(toJSStr(unAppCStr("Got server response ",new T(function(){return fromJSStr(E(_y8));})))),_yb=function(_){var _yc=_sI(E(_y8),_);return new T(function(){return B(A1(_y2,_yc));});};return new T1(0,_yb);};return new T1(0,_y9);}};return B(A1(_y0,_y5));});};return new T1(0,_y3);};return _y1;},_yd=new T(function(){return unAppCStr(") is outside of enumeration\'s range (0,",new T(function(){return _iH(0,2,new T(function(){return unCStr(")");}));}));}),_ye=function(_yf){return err(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return _iH(0,_yf,_yd);})));},_yg=function(_yh,_){return new T(function(){var _yi=Number(E(_yh)),_yj=jsTrunc(_yi);if(_yj<0){return _ye(_yj);}else{if(_yj>2){return _ye(_yj);}else{return _yj;}}});},_yk=new T3(0,0,0,0),_yl=new T(function(){return jsGetMouseCoords;}),_ym=function(_yn,_){var _yo=E(_yn);if(!_yo._){return __Z;}else{var _yp=_ym(_yo.b,_);return new T2(1,new T(function(){var _yq=Number(E(_yo.a));return jsTrunc(_yq);}),_yp);}},_yr=function(_ys,_){var _yt=__arr2lst(0,_ys);return _ym(_yt,_);},_yu=function(_yv,_){return new T(function(){var _yw=Number(E(_yv));return jsTrunc(_yw);});},_yx=new T2(0,_yu,function(_yy,_){return _yr(E(_yy),_);}),_yz=function(_yA,_){var _yB=E(_yA);if(!_yB._){return __Z;}else{var _yC=_yz(_yB.b,_);return new T2(1,_yB.a,_yC);}},_yD=new T(function(){return _uC(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9");}),__Z,__Z));}),_yE=function(_){return die(_yD);},_yF=function(_yG,_yH,_yI,_){var _yJ=__arr2lst(0,_yI),_yK=_yz(_yJ,_),_yL=E(_yK);if(!_yL._){return _yE(_);}else{var _yM=E(_yL.b);if(!_yM._){return _yE(_);}else{if(!E(_yM.b)._){var _yN=B(A3(_v2,_yG,_yL.a,_)),_yO=B(A3(_v2,_yH,_yM.a,_));return new T2(0,_yN,_yO);}else{return _yE(_);}}}},_yP=function(_yQ,_yR,_){if(E(_yQ)==7){var _yS=E(_yl)(_yR),_yT=_yF(_yx,_yx,_yS,_),_yU=_yR["deltaX"],_yV=_yR["deltaY"],_yW=_yR["deltaZ"];return new T(function(){return new T3(0,E(_yT),E(__Z),E(new T3(0,_yU,_yV,_yW)));});}else{var _yX=E(_yl)(_yR),_yY=_yF(_yx,_yx,_yX,_),_yZ=_yR["button"],_z0=__eq(_yZ,E(_v7));if(!E(_z0)){var _z1=__isUndef(_yZ);if(!E(_z1)){var _z2=_yg(_yZ,_);return new T(function(){return new T3(0,E(_yY),E(new T1(1,_z2)),E(_yk));});}else{return new T(function(){return new T3(0,E(_yY),E(__Z),E(_yk));});}}else{return new T(function(){return new T3(0,E(_yY),E(__Z),E(_yk));});}}},_z3=new T2(0,function(_z4){switch(E(_z4)){case 0:return "click";case 1:return "dblclick";case 2:return "mousedown";case 3:return "mouseup";case 4:return "mousemove";case 5:return "mouseover";case 6:return "mouseout";default:return "wheel";}},function(_z5,_z6,_){return _yP(_z5,E(_z6),_);}),_z7=function(_z8){return E(_z8);},_z9=function(_za,_zb,_){var _zc=B(A1(_za,_)),_zd=B(A1(_zb,_));return new T(function(){return B(A1(_zc,_zd));});},_ze=function(_zf,_){return _zf;},_zg=function(_zh,_zi,_){var _zj=B(A1(_zh,_));return C > 19 ? new F(function(){return A1(_zi,_);}) : (++C,A1(_zi,_));},_zk=new T(function(){return E(_uv);}),_zl=function(_zm){return new T6(0,__Z,7,__Z,_zm,__Z,__Z);},_zn=function(_zo,_){var _zp=new T(function(){return B(A2(_cB,_zk,new T(function(){return B(A1(_zl,_zo));})));});return die(_zp);},_zq=function(_zr,_){return _zn(_zr,_);},_zs=new T2(0,new T5(0,new T5(0,new T2(0,_1o,function(_zt,_zu,_){var _zv=B(A1(_zu,_));return _zt;}),_ze,_z9,_zg,function(_zw,_zx,_){var _zy=B(A1(_zw,_)),_zz=B(A1(_zx,_));return _zy;}),function(_zA,_zB,_){var _zC=B(A1(_zA,_));return C > 19 ? new F(function(){return A2(_zB,_zC,_);}) : (++C,A2(_zB,_zC,_));},_zg,_ze,function(_zD){return C > 19 ? new F(function(){return A1(_zq,_zD);}) : (++C,A1(_zq,_zD));}),_1C),_zE=new T2(0,_zs,_ze),_zF=function(_zG){return E(E(_zG).d);},_zH=new T2(0,_1C,function(_zI,_zJ){return C > 19 ? new F(function(){return A2(_zF,_tu(_zI),new T1(1,_zJ));}) : (++C,A2(_zF,_tu(_zI),new T1(1,_zJ)));}),_zK=(function(t){return document.createElement(t);}),_zL=function(_){return _zK("div");},_zM=(function(c,p){p.appendChild(c);}),_zN=(function(e){while(e.firstChild){e.removeChild(e.firstChild);}}),_zO=(function(c,p){p.removeChild(c);}),_zP=new T(function(){return document.body;}),_zQ=function(_,_zR){var _zS=E(_zR);if(!_zS._){return 0;}else{var _zT=E(_zS.a),_zU=_zN(_zT),_zV=_zO(_zT,E(_zP));return _6J(_);}},_zW=(function(id){return document.getElementById(id);}),_zX=function(_zY,_){var _zZ=_zW(toJSStr(E(_zY))),_A0=__eq(_zZ,E(_v7));if(!E(_A0)){var _A1=__isUndef(_zZ);if(!E(_A1)){return _zQ(_,new T1(1,_zZ));}else{return _zQ(_,__Z);}}else{return _zQ(_,__Z);}},_A2=function(_A3,_A4,_A5){while(1){var _A6=E(_A4);if(!_A6._){return (E(_A5)._==0)?true:false;}else{var _A7=E(_A5);if(!_A7._){return false;}else{if(!B(A3(_1F,_A3,_A6.a,_A7.a))){return false;}else{_A4=_A6.b;_A5=_A7.b;continue;}}}}},_A8=function(_A9,_){var _Aa=E(_A9);if(!_Aa._){return __Z;}else{var _Ab=_A8(_Aa.b,_);return new T2(1,_Aa.a,_Ab);}},_Ac=new T(function(){return err(new T(function(){return unCStr("Map.!: given key is not an element in the map");}));}),_Ad=function(_Ae,_Af){while(1){var _Ag=E(_Af);if(!_Ag._){switch(_6N(_Ae,_Ag.b)){case 0:_Af=_Ag.d;continue;case 1:return E(_Ag.c);default:_Af=_Ag.e;continue;}}else{return E(_Ac);}}},_Ah=function(_Ai,_Aj){while(1){var _Ak=E(_Ai);if(!_Ak._){return (E(_Aj)._==0)?true:false;}else{var _Al=E(_Aj);if(!_Al._){return false;}else{if(E(_Ak.a)!=E(_Al.a)){return false;}else{_Ai=_Ak.b;_Aj=_Al.b;continue;}}}}},_Am=function(_An,_Ao,_Ap,_Aq){return (!_Ah(_An,_Ap))?true:(!_eN(_Ao,_Aq))?true:false;},_Ar=function(_As,_At){var _Au=E(_As),_Av=E(_At);return _Am(_Au.a,_Au.b,_Av.a,_Av.b);},_Aw=function(_Ax,_Ay,_Az,_AA){if(!_Ah(_Ax,_Az)){return false;}else{return _eN(_Ay,_AA);}},_AB=function(_AC,_AD){var _AE=E(_AC),_AF=E(_AD);return _Aw(_AE.a,_AE.b,_AF.a,_AF.b);},_AG=function(_AH){return fromJSStr(E(_AH));},_AI=function(_AJ){return E(E(_AJ).a);},_AK=(function(e,p){return e.hasAttribute(p) ? e.getAttribute(p) : '';}),_AL=function(_AM,_AN,_AO,_AP){var _AQ=new T(function(){var _AR=function(_){var _AS=_AK(B(A2(_AI,_AM,_AO)),E(_AP));return new T(function(){return String(_AS);});};return _AR;});return C > 19 ? new F(function(){return A2(_wG,_AN,_AQ);}) : (++C,A2(_wG,_AN,_AQ));},_AT=function(_AU,_AV,_AW,_AX){var _AY=_tu(_AV),_AZ=new T(function(){return _zF(_AY);}),_B0=function(_B1){return C > 19 ? new F(function(){return A1(_AZ,new T(function(){return _AG(_B1);}));}) : (++C,A1(_AZ,new T(function(){return _AG(_B1);})));},_B2=new T(function(){return B(_AL(_AU,_AV,_AW,new T(function(){return toJSStr(E(_AX));},1)));});return C > 19 ? new F(function(){return A3(_1g,_AY,_B2,_B0);}) : (++C,A3(_1g,_AY,_B2,_B0));},_B3=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_B4=function(_B5,_B6,_B7,_B8){var _B9=new T(function(){var _Ba=function(_){var _Bb=_B3(B(A2(_AI,_B5,_B7)),E(_B8));return new T(function(){return String(_Bb);});};return _Ba;});return C > 19 ? new F(function(){return A2(_wG,_B6,_B9);}) : (++C,A2(_wG,_B6,_B9));},_Bc=function(_Bd,_Be,_Bf,_Bg){var _Bh=_tu(_Be),_Bi=new T(function(){return _zF(_Bh);}),_Bj=function(_Bk){return C > 19 ? new F(function(){return A1(_Bi,new T(function(){return _AG(_Bk);}));}) : (++C,A1(_Bi,new T(function(){return _AG(_Bk);})));},_Bl=new T(function(){return B(_B4(_Bd,_Be,_Bf,new T(function(){return toJSStr(E(_Bg));},1)));});return C > 19 ? new F(function(){return A3(_1g,_Bh,_Bl,_Bj);}) : (++C,A3(_1g,_Bh,_Bl,_Bj));},_Bm=new T(function(){return unCStr("suggestionList");}),_Bn=new T2(0,new T(function(){return unCStr("PrimaEng");}),new T(function(){return unCStr("(useS (useCl (simpleCl (usePron he_PP) (complA Romanus_A))))");})),_Bo=new T(function(){return _v4(function(_){return nMV(__Z);});}),_Bp=(function(e){if(e){e.stopPropagation();}}),_Bq=function(_){var _Br=rMV(E(_Bo)),_Bs=E(_Br);if(!_Bs._){var _Bt=_Bp(E(_v7));return _6J(_);}else{var _Bu=_Bp(E(_Bs.a));return _6J(_);}},_Bv=new T(function(){return unCStr("lang");}),_Bw=new T(function(){return err(_qk);}),_Bx=new T(function(){return err(_ql);}),_By=new T(function(){return B(A3(_p2,_pv,0,_qe));}),_Bz=new T(function(){return unCStr("textContent");}),_BA=new T(function(){return _uC(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:281:5-16");}),__Z,__Z));}),_BB=new T(function(){return unCStr("score");}),_BC=function(_BD,_BE,_){var _BF=_Bq(_),_BG=_zX(_Bm,_),_BH=B(A(_AT,[_zH,_zs,_BD,_Bv,_])),_BI=_BH,_BJ=_zW(toJSStr(E(_BB))),_BK=__eq(_BJ,E(_v7)),_BL=function(_,_BM){var _BN=E(_BM);if(!_BN._){return die(_BA);}else{var _BO=B(A(_Bc,[_zH,_zs,_BN.a,_Bz,_])),_BP=new T(function(){return B(A2(_xW,new T3(1,new T(function(){var _BQ=_qm(_e7(_By,_BO));if(!_BQ._){return E(_Bx);}else{if(!E(_BQ.b)._){return E(_BQ.a);}else{return E(_Bw);}}}),_Bn,new T2(0,_BI,_BE)),_BR));});return _a(_BP,__Z,_);}};if(!E(_BK)){var _BS=__isUndef(_BJ);if(!E(_BS)){return _BL(_,new T1(1,_BJ));}else{return _BL(_,__Z);}}else{return _BL(_,__Z);}},_BT=function(_BU,_BV){var _BW=E(_BV);if(!_BW._){return __Z;}else{var _BX=_BW.a,_BY=E(_BU);return (_BY==1)?new T2(1,_BX,__Z):new T2(1,_BX,new T(function(){return _BT(_BY-1|0,_BW.b);}));}},_BZ=(function(e,p,v){e.setAttribute(p, v);}),_C0=(function(e,p){e.removeAttribute(p);}),_C1=new T(function(){return unCStr("clickCount");}),_C2=new T(function(){return unCStr("clicked");}),_C3=new T(function(){return unCStr("False");}),_C4=function(_C5,_){while(1){var _C6=E(_C5);if(!_C6._){return 0;}else{var _C7=E(_C6.a),_C8=_BZ(_C7,toJSStr(E(_C2)),toJSStr(E(_C3))),_C9=_C0(_C7,toJSStr(E(_C1)));_C5=_C6.b;continue;}}},_Ca=new T(function(){return _r6(new T(function(){return unCStr("head");}));}),_Cb=new T(function(){return _Cc(__Z);}),_Cc=function(_Cd){while(1){var _Ce=(function(_Cf){var _Cg=E(_Cf);if(!_Cg._){return __Z;}else{var _Ch=_Cg.b,_Ci=E(_Cg.a);if(_Ci==32){var _Cj=E(_Ch);if(!_Cj._){return new T2(1,_Ci,_Cb);}else{if(E(_Cj.a)==38){var _Ck=E(_Cj.b);if(!_Ck._){return new T2(1,_Ci,new T(function(){return _Cc(_Cj);}));}else{if(E(_Ck.a)==43){var _Cl=E(_Ck.b);if(!_Cl._){return new T2(1,_Ci,new T(function(){return _Cc(_Cj);}));}else{if(E(_Cl.a)==32){_Cd=_Cl.b;return __continue;}else{return new T2(1,_Ci,new T(function(){return _Cc(_Cj);}));}}}else{return new T2(1,_Ci,new T(function(){return _Cc(_Cj);}));}}}else{return new T2(1,_Ci,new T(function(){return _Cc(_Cj);}));}}}else{return new T2(1,_Ci,new T(function(){return _Cc(_Ch);}));}}})(_Cd);if(_Ce!=__continue){return _Ce;}}},_Cm=(function(e){var ch = [];for(e = e.firstChild; e != null; e = e.nextSibling)  {if(e instanceof HTMLElement) {ch.push(e);}}return ch;}),_Cn=function(_Co,_Cp,_Cq){while(1){var _Cr=E(_Cp);if(!_Cr._){return true;}else{var _Cs=E(_Cq);if(!_Cs._){return false;}else{if(!B(A3(_1F,_Co,_Cr.a,_Cs.a))){return false;}else{_Cp=_Cr.b;_Cq=_Cs.b;continue;}}}}},_Ct=new T(function(){return unCStr("\u2205");}),_Cu=new T(function(){return new T1(1,"left");}),_Cv=new T(function(){return unCStr("offsetTop");}),_Cw=new T(function(){return unCStr("offsetLeft");}),_Cx=new T(function(){return new T1(1,"top");}),_Cy=new T(function(){return new T2(0,E(new T1(2,"class")),"menu");}),_Cz=new T(function(){return new T2(0,E(new T1(2,"id")),"suggestionList");}),_CA=new T(function(){return err(_ql);}),_CB=new T(function(){return err(_qk);}),_CC=function(_CD,_CE){return C > 19 ? new F(function(){return _CF(_CE);}) : (++C,_CF(_CE));},_CG=new T(function(){return unCStr("True");}),_CH=new T(function(){return unCStr("False");}),_CF=function(_CI){var _CJ=new T(function(){return B(A1(_CI,false));}),_CK=new T(function(){return B(A1(_CI,true));}),_CL=new T(function(){return B(_o1(function(_CM){var _CN=E(_CM);if(_CN._==3){var _CO=_CN.a;return (!_eN(_CO,_CH))?(!_eN(_CO,_CG))?new T0(2):E(_CK):E(_CJ);}else{return new T0(2);}}));}),_CP=function(_CQ){return E(_CL);};return _eh(new T1(1,function(_CR){return C > 19 ? new F(function(){return A2(_mU,_CR,_CP);}) : (++C,A2(_mU,_CR,_CP));}),new T(function(){return new T1(1,_oy(_CC,_CI));}));},_CS=new T(function(){return B(_CF(_qe));}),_CT=new T(function(){return unCStr("lin");}),_CU=new T(function(){return err(_qk);}),_CV=new T(function(){return err(_ql);}),_CW=function(_CX,_CY){return C > 19 ? new F(function(){return _pF(_pC,_CY);}) : (++C,_pF(_pC,_CY));},_CZ=function(_D0,_D1){return C > 19 ? new F(function(){return _pF(_CW,_D1);}) : (++C,_pF(_CW,_D1));},_D2=new T(function(){return B(_pF(_CW,_fh));}),_D3=function(_pD){return _e7(_D2,_pD);},_D4=new T(function(){return B(_pF(_pC,_fh));}),_D5=function(_pD){return _e7(_D4,_pD);},_D6=function(_D7,_pD){return _D5(_pD);},_D8=function(_D9,_Da){return C > 19 ? new F(function(){return _Db(_Da);}) : (++C,_Db(_Da));},_Db=function(_Dc){var _Dd=new T(function(){return B(_o1(function(_De){var _Df=E(_De);if(!_Df._){return C > 19 ? new F(function(){return A1(_Dc,_Df.a);}) : (++C,A1(_Dc,_Df.a));}else{return new T0(2);}}));}),_Dg=function(_Dh){return E(_Dd);};return _eh(new T1(1,function(_Di){return C > 19 ? new F(function(){return A2(_mU,_Di,_Dg);}) : (++C,A2(_mU,_Di,_Dg));}),new T(function(){return new T1(1,_oy(_D8,_Dc));}));},_Dj=function(_Dk,_Dl){return C > 19 ? new F(function(){return _Db(_Dl);}) : (++C,_Db(_Dl));},_Dm=function(_Dn,_Do){return C > 19 ? new F(function(){return _Dp(_Do);}) : (++C,_Dp(_Do));},_Dp=function(_Dq){var _Dr=new T(function(){return B(_o1(function(_Ds){var _Dt=E(_Ds);if(_Dt._==1){return C > 19 ? new F(function(){return A1(_Dq,_Dt.a);}) : (++C,A1(_Dq,_Dt.a));}else{return new T0(2);}}));}),_Du=function(_Dv){return E(_Dr);};return _eh(_eh(new T1(1,function(_Dw){return C > 19 ? new F(function(){return A2(_mU,_Dw,_Du);}) : (++C,A2(_mU,_Dw,_Du));}),new T(function(){return B(_pF(_Dj,_Dq));})),new T(function(){return new T1(1,_oy(_Dm,_Dq));}));},_Dx=function(_Dy,_Dz){return C > 19 ? new F(function(){return _Dp(_Dz);}) : (++C,_Dp(_Dz));},_DA=function(_DB,_DC){return C > 19 ? new F(function(){return _pF(_Dx,_DC);}) : (++C,_pF(_Dx,_DC));},_DD=new T(function(){return B(_pF(_Dx,_fh));}),_DE=function(_pD){return _e7(_DD,_pD);},_DF=new T(function(){return B(_Dp(_fh));}),_DG=function(_pD){return _e7(_DF,_pD);},_DH=function(_DI,_pD){return _DG(_pD);},_DJ=new T(function(){return unCStr(",");}),_DK=function(_DL){return E(E(_DL).c);},_DM=function(_DN,_DO,_DP){var _DQ=new T(function(){return _DK(_DO);}),_DR=new T(function(){return B(A2(_DK,_DN,_DP));}),_DS=function(_DT){var _DU=function(_DV){var _DW=new T(function(){var _DX=new T(function(){return B(A2(_DQ,_DP,function(_DY){return C > 19 ? new F(function(){return A1(_DT,new T2(0,_DV,_DY));}) : (++C,A1(_DT,new T2(0,_DV,_DY)));}));});return B(_o1(function(_DZ){var _E0=E(_DZ);return (_E0._==2)?(!_eN(_E0.a,_DJ))?new T0(2):E(_DX):new T0(2);}));}),_E1=function(_E2){return E(_DW);};return new T1(1,function(_E3){return C > 19 ? new F(function(){return A2(_mU,_E3,_E1);}) : (++C,A2(_mU,_E3,_E1));});};return C > 19 ? new F(function(){return A1(_DR,_DU);}) : (++C,A1(_DR,_DU));};return _DS;},_E4=function(_E5,_E6,_E7){var _E8=function(_pD){return _DM(_E5,_E6,_pD);},_E9=function(_Ea,_Eb){return C > 19 ? new F(function(){return _Ec(_Eb);}) : (++C,_Ec(_Eb));},_Ec=function(_Ed){return _eh(new T1(1,_oy(_E8,_Ed)),new T(function(){return new T1(1,_oy(_E9,_Ed));}));};return C > 19 ? new F(function(){return _Ec(_E7);}) : (++C,_Ec(_E7));},_Ee=new T(function(){return B(_pF(function(_Ef,_Eg){return C > 19 ? new F(function(){return _E4(new T4(0,_D6,_D3,_CW,_CZ),new T4(0,_DH,_DE,_Dx,_DA),_Eg);}) : (++C,_E4(new T4(0,_D6,_D3,_CW,_CZ),new T4(0,_DH,_DE,_Dx,_DA),_Eg));},_qe));}),_Eh=new T(function(){return unCStr("path");}),_Ei=new T(function(){return err(_qk);}),_Ej=new T(function(){return err(_ql);}),_Ek=new T(function(){return B(_pF(_pC,_qe));}),_El=new T(function(){return _uC(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:192:5-15");}),__Z,__Z));}),_Em=new T(function(){return unCStr("px");}),_En=new T(function(){return unCStr("parentid");}),_Eo=new T(function(){return unCStr("menuHover");}),_Ep=(function(e,c) {e.classList.toggle(c);}),_Eq=function(_Er,_){var _Es=_Ep(_Er,toJSStr(E(_Eo)));return _6J(_);},_Et=new T(function(){return unCStr("div");}),_Eu=(function(s){return document.createTextNode(s);}),_Ev=function(_Ew){return E(E(_Ew).a);},_Ex=function(_Ey){return E(E(_Ey).b);},_Ez=function(_EA){return E(E(_EA).a);},_EB=function(_EC){return E(E(_EC).b);},_ED=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_EE=function(_EF,_EG,_EH,_EI,_EJ,_EK){var _EL=_Ev(_EF),_EM=_tu(_EL),_EN=new T(function(){return _wG(_EL);}),_EO=new T(function(){return _zF(_EM);}),_EP=new T(function(){return B(A1(_EG,_EI));}),_EQ=new T(function(){return B(A2(_Ez,_EH,_EJ));}),_ER=function(_ES){return C > 19 ? new F(function(){return A1(_EO,new T3(0,_EQ,_EP,_ES));}) : (++C,A1(_EO,new T3(0,_EQ,_EP,_ES)));},_ET=function(_EU){var _EV=new T(function(){var _EW=new T(function(){var _EX=__createJSFunc(2,function(_EY,_){var _EZ=B(A2(E(_EU),_EY,_));return _v7;}),_F0=_EX;return function(_){return _ED(E(_EP),E(_EQ),_F0);};});return B(A1(_EN,_EW));});return C > 19 ? new F(function(){return A3(_1g,_EM,_EV,_ER);}) : (++C,A3(_1g,_EM,_EV,_ER));},_F1=new T(function(){var _F2=new T(function(){return _wG(_EL);}),_F3=function(_F4){var _F5=new T(function(){return B(A1(_F2,function(_){var _=wMV(E(_Bo),new T1(1,_F4));return C > 19 ? new F(function(){return A(_Ex,[_EH,_EJ,_F4,_]);}) : (++C,A(_Ex,[_EH,_EJ,_F4,_]));}));});return C > 19 ? new F(function(){return A3(_1g,_EM,_F5,_EK);}) : (++C,A3(_1g,_EM,_F5,_EK));};return B(A2(_EB,_EF,_F3));});return C > 19 ? new F(function(){return A3(_1g,_EM,_F1,_ET);}) : (++C,A3(_1g,_EM,_F1,_ET));},_F6=function(_F7,_F8,_F9,_){var _Fa=_Eu(toJSStr(E(_F8))),_Fb=_zK(toJSStr(E(_Et))),_Fc=_Fb,_Fd=B(A(_EE,[_zE,_z7,_z3,_Fc,5,function(_Fe,_){return _Eq(_Fc,_);},_])),_Ff=B(A(_EE,[_zE,_z7,_z3,_Fc,6,function(_Fg,_){return _Eq(_Fc,_);},_])),_Fh=B(A(_EE,[_zE,_z7,_z3,_Fc,0,_F9,_])),_Fi=_zM(_Fa,_Fc),_Fj=_zM(_Fc,E(_F7));return 0;},_Fk=new T(function(){return unCStr("True");}),_Fl=(function(e,p,v){e.style[p] = v;}),_Fm=(function(e,p,v){e[p] = v;}),_Fn=function(_Fo,_Fp,_Fq,_Fr){var _Fs=new T(function(){return B(A2(_AI,_Fo,_Fq));}),_Ft=function(_Fu,_){var _Fv=E(_Fu);if(!_Fv._){return 0;}else{var _Fw=E(_Fs),_Fx=_zM(E(_Fv.a),_Fw),_Fy=function(_Fz,_){while(1){var _FA=E(_Fz);if(!_FA._){return 0;}else{var _FB=_zM(E(_FA.a),_Fw);_Fz=_FA.b;continue;}}};return _Fy(_Fv.b,_);}},_FC=function(_FD,_){while(1){var _FE=(function(_FF,_){var _FG=E(_FF);if(!_FG._){return 0;}else{var _FH=_FG.b,_FI=E(_FG.a);if(!_FI._){var _FJ=_FI.b,_FK=E(_FI.a);switch(_FK._){case 0:var _FL=E(_Fs),_FM=_Fm(_FL,_FK.a,_FJ),_FN=function(_FO,_){while(1){var _FP=E(_FO);if(!_FP._){return 0;}else{var _FQ=_FP.b,_FR=E(_FP.a);if(!_FR._){var _FS=_FR.b,_FT=E(_FR.a);switch(_FT._){case 0:var _FU=_Fm(_FL,_FT.a,_FS);_FO=_FQ;continue;case 1:var _FV=_Fl(_FL,_FT.a,_FS);_FO=_FQ;continue;default:var _FW=_BZ(_FL,_FT.a,_FS);_FO=_FQ;continue;}}else{var _FX=_Ft(_FR.a,_);_FO=_FQ;continue;}}}};return _FN(_FH,_);case 1:var _FY=E(_Fs),_FZ=_Fl(_FY,_FK.a,_FJ),_G0=function(_G1,_){while(1){var _G2=E(_G1);if(!_G2._){return 0;}else{var _G3=_G2.b,_G4=E(_G2.a);if(!_G4._){var _G5=_G4.b,_G6=E(_G4.a);switch(_G6._){case 0:var _G7=_Fm(_FY,_G6.a,_G5);_G1=_G3;continue;case 1:var _G8=_Fl(_FY,_G6.a,_G5);_G1=_G3;continue;default:var _G9=_BZ(_FY,_G6.a,_G5);_G1=_G3;continue;}}else{var _Ga=_Ft(_G4.a,_);_G1=_G3;continue;}}}};return _G0(_FH,_);default:var _Gb=E(_Fs),_Gc=_BZ(_Gb,_FK.a,_FJ),_Gd=function(_Ge,_){while(1){var _Gf=E(_Ge);if(!_Gf._){return 0;}else{var _Gg=_Gf.b,_Gh=E(_Gf.a);if(!_Gh._){var _Gi=_Gh.b,_Gj=E(_Gh.a);switch(_Gj._){case 0:var _Gk=_Fm(_Gb,_Gj.a,_Gi);_Ge=_Gg;continue;case 1:var _Gl=_Fl(_Gb,_Gj.a,_Gi);_Ge=_Gg;continue;default:var _Gm=_BZ(_Gb,_Gj.a,_Gi);_Ge=_Gg;continue;}}else{var _Gn=_Ft(_Gh.a,_);_Ge=_Gg;continue;}}}};return _Gd(_FH,_);}}else{var _Go=_Ft(_FI.a,_);_FD=_FH;return __continue;}}})(_FD,_);if(_FE!=__continue){return _FE;}}};return C > 19 ? new F(function(){return A2(_wG,_Fp,function(_){return _FC(_Fr,_);});}) : (++C,A2(_wG,_Fp,function(_){return _FC(_Fr,_);}));},_Gp=function(_Gq,_Gr,_Gs,_Gt){var _Gu=_tu(_Gr),_Gv=function(_Gw){return C > 19 ? new F(function(){return A3(_wB,_Gu,new T(function(){return B(_Fn(_Gq,_Gr,_Gw,_Gt));}),new T(function(){return B(A2(_zF,_Gu,_Gw));}));}) : (++C,A3(_wB,_Gu,new T(function(){return B(_Fn(_Gq,_Gr,_Gw,_Gt));}),new T(function(){return B(A2(_zF,_Gu,_Gw));})));};return C > 19 ? new F(function(){return A3(_1g,_Gu,_Gs,_Gv);}) : (++C,A3(_1g,_Gu,_Gs,_Gv));},_Gx=function(_Gy,_Gz,_GA,_){var _GB=_Bq(_),_GC=B(A(_Bc,[_zH,_zs,_Gy,_Cw,_])),_GD=_GC,_GE=B(A(_Bc,[_zH,_zs,_Gy,_Cv,_])),_GF=_GE,_GG=_zX(_Bm,_),_GH=B(A(_AT,[_zH,_zs,_Gy,_C2,_])),_GI=_qm(_e7(_CS,_GH));if(!_GI._){return E(_CA);}else{if(!E(_GI.b)._){var _GJ=function(_,_GK){var _GL=B(A(_AT,[_zH,_zs,_Gy,_En,_])),_GM=_zW(toJSStr(E(_GL))),_GN=__eq(_GM,E(_v7)),_GO=function(_,_GP){var _GQ=E(_GP);if(!_GQ._){return die(_El);}else{var _GR=E(_GQ.a),_GS=_Cm(_GR),_GT=__arr2lst(0,_GS),_GU=_A8(_GT,_),_GV=_C4(_GU,_),_GW=E(_Gy),_GX=_BZ(_GW,toJSStr(E(_C2)),toJSStr(E(_Fk))),_GY=E(_GK),_GZ=_BZ(_GW,toJSStr(E(_C1)),toJSStr(_iH(0,_GY+1|0,__Z))),_H0=B(A(_AT,[_zH,_zs,_GW,_Eh,_])),_H1=B(A(_AT,[_zH,_zs,_GR,_CT,_])),_H2=new T(function(){var _H3=_qm(_e7(_Ek,_H0));if(!_H3._){return E(_Ej);}else{var _H4=_H3.a;if(!E(_H3.b)._){var _H5=_hi(_H4,0)-_GY|0;if(0>=_H5){return __Z;}else{return _BT(_H5,_H4);}}else{return E(_Ei);}}}),_H6=new T(function(){var _H7=_Ad(_H2,_Gz);if(!_H7._){return E(_Ca);}else{return E(_H7.a);}}),_H8=new T(function(){var _H9=new T(function(){return unAppCStr(": ",new T(function(){return _2P(_rX,_H6,__Z);}));},1);return _0(_2P(_rm,_H2,__Z),_H9);}),_Ha=_6K(toJSStr(unAppCStr("Suggestions for path ",_H8))),_Hb=new T(function(){return E(E(_GA).a);}),_Hc=B(A(_Gp,[_zH,_zs,_zL,new T2(1,_Cz,new T2(1,_Cy,new T2(1,new T(function(){var _Hd=_qm(_e7(_By,_GF));if(!_Hd._){return E(_Bx);}else{if(!E(_Hd.b)._){return new T2(0,E(_Cx),toJSStr(_0(_iH(0,E(E(_Hb).b)+E(_Hd.a)|0,__Z),_Em)));}else{return E(_Bw);}}}),new T2(1,new T(function(){var _He=_qm(_e7(_By,_GD));if(!_He._){return E(_Bx);}else{if(!E(_He.b)._){return new T2(0,E(_Cu),toJSStr(_0(_iH(0,E(E(_Hb).a)+E(_He.a)|0,__Z),_Em)));}else{return E(_Bw);}}}),__Z)))),_])),_Hf=_Hc,_Hg=new T(function(){var _Hh=_qm(_e7(_Ee,_H1));if(!_Hh._){return E(_CV);}else{if(!E(_Hh.b)._){return E(_Hh.a);}else{return E(_CU);}}}),_Hi=function(_Hj){while(1){var _Hk=(function(_Hl){var _Hm=E(_Hl);if(!_Hm._){return __Z;}else{var _Hn=_Hm.b,_Ho=E(_Hm.a);if(!_Cn(_3s,_H2,_Ho.a)){_Hj=_Hn;return __continue;}else{var _Hp=new T(function(){return _0(_Ho.b,new T(function(){return _Hi(_Hn);},1));});return new T2(1,32,_Hp);}}})(_Hj);if(_Hk!=__continue){return _Hk;}}},_Hq=function(_Hr,_){while(1){var _Hs=(function(_Ht,_){var _Hu=E(_Ht);if(!_Hu._){return 0;}else{var _Hv=_Hu.b,_Hw=E(_Hu.a),_Hx=_Hw.b;if(!_A2(new T2(0,_AB,_Ar),_Hx,_Hg)){var _Hy=function(_Hz,_){return C > 19 ? new F(function(){return _BC(_GR,_Hw.c,_);}) : (++C,_BC(_GR,_Hw.c,_));},_HA=_Hi(_Hx);if(!_HA._){var _HB=E(_Cb);if(!_HB._){var _HC=_F6(_Hf,_Ct,_Hy,_);_Hr=_Hv;return __continue;}else{var _HD=_F6(_Hf,_HB,_Hy,_);_Hr=_Hv;return __continue;}}else{var _HE=_Cc(_HA.b);if(!_HE._){var _HF=_F6(_Hf,_Ct,_Hy,_);_Hr=_Hv;return __continue;}else{var _HG=_F6(_Hf,_HE,_Hy,_);_Hr=_Hv;return __continue;}}}else{_Hr=_Hv;return __continue;}}})(_Hr,_);if(_Hs!=__continue){return _Hs;}}},_HH=_Hq(_H6,_),_HI=_zM(E(_Hf),E(_zP));return 0;}};if(!E(_GN)){var _HJ=__isUndef(_GM);if(!E(_HJ)){return _GO(_,new T1(1,_GM));}else{return _GO(_,__Z);}}else{return _GO(_,__Z);}};if(!E(_GI.a)){return _GJ(_,0);}else{var _HK=B(A(_AT,[_zH,_zs,_Gy,_C1,_]));return _GJ(_,new T(function(){var _HL=_qm(_e7(_By,_HK));if(!_HL._){return E(_Bx);}else{if(!E(_HL.b)._){return E(_HL.a);}else{return E(_Bw);}}},1));}}else{return E(_CB);}}},_HM=function(_HN,_HO){return new T2(0,E(_HN),toJSStr(E(_HO)));},_HP=function(_){return _zK("span");},_HQ=new T(function(){return B(_Gp(_zH,_zs,function(_){return _zK("span");},new T2(1,new T(function(){return new T2(0,E(new T1(2,"class")),"path");}),__Z)));}),_HR=new T(function(){return new T1(2,"parentId");}),_HS=new T(function(){return new T1(2,"path");}),_HT=new T(function(){return new T2(0,E(new T1(2,"class")),"word");}),_HU=new T(function(){return new T2(0,E(new T1(2,"class")),"gap");}),_HV=new T(function(){return unCStr("id");}),_HW=new T(function(){return unCStr(" ");}),_HX=new T2(1,new T(function(){return new T2(0,E(new T1(2,"clicked")),toJSStr(E(_C3)));}),__Z),_HY=new T(function(){return unCStr("wordHover");}),_HZ=function(_I0,_){var _I1=_Ep(_I0,toJSStr(E(_HY)));return _6J(_);},_I2=function(_I3,_I4,_){return _HZ(E(_I3),_);},_I5=function(_I6,_I7,_I8,_I9,_Ia,_Ib,_Ic,_){var _Id=B(A(_AT,[_zH,_zs,_I6,_HV,_])),_Ie=_Id,_If=function(_){var _Ig=B(A(_Gp,[_zH,_zs,_HP,new T2(1,_HT,new T2(1,new T(function(){return new T2(0,E(_HS),toJSStr(_2P(_rm,_I7,__Z)));}),new T2(1,new T(function(){return _HM(_HR,_Ie);}),_HX))),_])),_Ih=_Ig,_Ii=_Eu(toJSStr(E(_I8))),_Ij=B(A(_EE,[_zE,_z7,_z3,_Ih,5,function(_Ik,_){return _I2(_Ih,_Ik,_);},_])),_Il=B(A(_EE,[_zE,_z7,_z3,_Ih,6,function(_Ik,_){return _I2(_Ih,_Ik,_);},_])),_Im=E(_Ih),_In=_zM(_Ii,_Im),_Io=E(_I6),_Ip=_zM(_Im,_Io),_Iq=function(_){if(!E(_Ia)){return 0;}else{var _Ir=B(A1(_HQ,_)),_Is=_Eu(toJSStr(_2P(_rm,_I7,__Z))),_It=E(_Ir),_Iu=_zM(_Is,_It),_Iv=_zM(_It,_Io);return _6J(_);}};if(!E(_Ic)){return _Iq(_);}else{var _Iw=B(A(_EE,[_zE,_z7,_z3,_Im,0,function(_Ix,_){return C > 19 ? new F(function(){return _Gx(_Im,E(_I9).a,_Ix,_);}) : (++C,_Gx(_Im,E(_I9).a,_Ix,_));},_]));return _Iq(_);}};if(!E(_Ib)){return _If(_);}else{var _Iy=B(A(_Gp,[_zH,_zs,_HP,new T2(1,_HU,new T2(1,new T(function(){return new T2(0,E(_HS),toJSStr(_2P(_rm,_I7,__Z)));}),new T2(1,new T(function(){return _HM(_HR,_Ie);}),_HX))),_])),_Iz=_Iy,_IA=_Eu(toJSStr(E(_HW))),_IB=B(A(_EE,[_zE,_z7,_z3,_Iz,5,function(_Ik,_){return _I2(_Iz,_Ik,_);},_])),_IC=B(A(_EE,[_zE,_z7,_z3,_Iz,6,function(_Ik,_){return _I2(_Iz,_Ik,_);},_])),_ID=E(_Iz),_IE=_zM(_IA,_ID),_IF=_zM(_ID,E(_I6));if(!E(_Ic)){return _If(_);}else{var _IG=B(A(_EE,[_zE,_z7,_z3,_ID,0,function(_IH,_){return C > 19 ? new F(function(){return _Gx(_ID,E(_I9).a,_IH,_);}) : (++C,_Gx(_ID,E(_I9).a,_IH,_));},_]));return _If(_);}}},_II=(function(e,c) {return e.classList.contains(c);}),_IJ=new T(function(){return unCStr("debug");}),_IK=function(_IL,_IM){var _IN=E(_IL),_IO=new T(function(){return B(A3(_r9,_qZ,new T2(1,function(_IP){return _rp(_IN.a,_IP);},new T2(1,function(_IQ){return _rj(_IN.b,_IQ);},__Z)),new T2(1,41,_IM)));});return new T2(1,40,_IO);},_IR=new T(function(){return _uC(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:67:5-23");}),__Z,__Z));}),_IS=new T(function(){return unCStr("exampleTree");}),_IT=function(_IU,_IV,_IW,_){var _IX=_zW(toJSStr(E(_IS))),_IY=__eq(_IX,E(_v7)),_IZ=function(_,_J0){var _J1=E(_J0);if(!_J1._){return die(_IR);}else{var _J2=E(_J1.a),_J3=_zN(_J2),_J4=_II(_J2,toJSStr(E(_IJ))),_J5=_J4,_J6=_BZ(_J2,toJSStr(E(_CT)),toJSStr(_2P(_IK,_IV,__Z))),_J7=_BZ(_J2,toJSStr(E(_Bv)),toJSStr(E(_IU))),_J8=function(_J9,_){while(1){var _Ja=E(_J9);if(!_Ja._){return 0;}else{var _Jb=E(_Ja.a),_Jc=B(_I5(_J2,_Jb.a,_Jb.b,_IW,_J5,false,false,_));_J9=_Ja.b;continue;}}},_Jd=_J8(_IV,_);return 0;}};if(!E(_IY)){var _Je=__isUndef(_IX);if(!E(_Je)){return _IZ(_,new T1(1,_IX));}else{return _IZ(_,__Z);}}else{return _IZ(_,__Z);}},_Jf=new T(function(){return _uC(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:84:5-24");}),__Z,__Z));}),_Jg=new T(function(){return unCStr("exerciseTree");}),_Jh=function(_Ji,_Jj,_Jk,_){var _Jl=_zW(toJSStr(E(_Jg))),_Jm=__eq(_Jl,E(_v7)),_Jn=function(_,_Jo){var _Jp=E(_Jo);if(!_Jp._){return die(_Jf);}else{var _Jq=E(_Jp.a),_Jr=_zN(_Jq),_Js=_II(_Jq,toJSStr(E(_IJ))),_Jt=_Js,_Ju=_BZ(_Jq,toJSStr(E(_CT)),toJSStr(_2P(_IK,_Jj,__Z))),_Jv=_BZ(_Jq,toJSStr(E(_Bv)),toJSStr(E(_Ji))),_Jw=function(_Jx,_){while(1){var _Jy=E(_Jx);if(!_Jy._){return 0;}else{var _Jz=E(_Jy.a),_JA=B(_I5(_Jq,_Jz.a,_Jz.b,_Jk,_Jt,true,true,_));_Jx=_Jy.b;continue;}}},_JB=_Jw(_Jj,_);return 0;}};if(!E(_Jm)){var _JC=__isUndef(_Jl);if(!E(_JC)){return _Jn(_,new T1(1,_Jl));}else{return _Jn(_,__Z);}}else{return _Jn(_,__Z);}},_JD=new T(function(){return alert;}),_JE=new T(function(){return unCStr("won");}),_JF=new T(function(){return _uC(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:53:5-16");}),__Z,__Z));}),_JG=new T(function(){return unCStr(" Clicks");}),_JH=function(_JI,_JJ,_){var _JK=_zW(toJSStr(E(_BB))),_JL=__eq(_JK,E(_v7)),_JM=function(_,_JN){var _JO=E(_JN);if(!_JO._){return die(_JF);}else{var _JP=E(_JO.a),_JQ=_zN(_JP),_JR=E(_JI),_JS=_Eu(toJSStr(_iH(0,_JR,__Z)));if(!E(_JJ)){var _JT=_zM(_JS,_JP);return _6J(_);}else{var _JU=_Ep(_JP,toJSStr(E(_JE))),_JV=E(_JD)(toJSStr(unAppCStr("Congratulations! You won after ",new T(function(){return _0(_iH(0,_JR,__Z),_JG);})))),_JW=_zM(_JS,_JP);return _6J(_);}}};if(!E(_JL)){var _JX=__isUndef(_JK);if(!E(_JX)){return _JM(_,new T1(1,_JK));}else{return _JM(_,__Z);}}else{return _JM(_,__Z);}},_JY=new T(function(){return unCStr("laetus");}),_JZ=new T2(1,0,__Z),_K0=new T(function(){return unCStr("est");}),_K1=new T(function(){return unCStr("Augustus");}),_K2=new T(function(){return unCStr("menuList");}),_K3=new T(function(){return unCStr("Reset");}),_K4=new T(function(){return unCStr("Toggle Debug");}),_K5=new T(function(){return new T2(0,E(new T1(2,"id")),"menuList");}),_K6=new T(function(){return _uC(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:266:87-93");}),__Z,__Z));}),_K7=new T(function(){return _uC(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:266:51-57");}),__Z,__Z));}),_K8=function(_K9,_Ka,_){var _Kb=new T(function(){return E(E(E(_Ka).d).a);}),_Kc=new T(function(){return E(E(E(_Ka).d).d);}),_Kd=_Bq(_),_Ke=B(A(_Bc,[_zH,_zs,_K9,_Cw,_])),_Kf=B(A(_Bc,[_zH,_zs,_K9,_Cv,_])),_Kg=_zX(_K2,_),_Kh=B(A(_Gp,[_zH,_zs,_zL,new T2(1,_K5,new T2(1,_Cy,new T2(1,new T(function(){return new T2(0,E(_Cx),toJSStr(_0(_Kf,_Em)));}),new T2(1,new T(function(){var _Ki=_qm(_e7(_By,_Ke));if(!_Ki._){return E(_Bx);}else{if(!E(_Ki.b)._){return new T2(0,E(_Cu),toJSStr(_0(_iH(0,E(_Ki.a)-200|0,__Z),_Em)));}else{return E(_Bw);}}}),__Z)))),_])),_Kj=new T(function(){return E(E(E(_Ka).d).c);}),_Kk=new T(function(){return E(E(E(_Ka).c).d);}),_Kl=new T(function(){return E(E(E(_Ka).c).c);}),_Km=new T(function(){return E(E(E(_Ka).c).a);}),_Kn=function(_Ko,_){var _Kp=_zW(toJSStr(E(_IS))),_Kq=E(_v7),_Kr=__eq(_Kp,_Kq),_Ks=function(_,_Kt){var _Ku=E(_Kt);if(!_Ku._){return die(_K7);}else{var _Kv=_zW(toJSStr(E(_Jg))),_Kw=__eq(_Kv,_Kq),_Kx=function(_,_Ky){var _Kz=E(_Ky);if(!_Kz._){return die(_K6);}else{var _KA=toJSStr(E(_IJ)),_KB=_Ep(E(_Ku.a),_KA),_KC=_Ep(E(_Kz.a),_KA),_KD=_Jh(_Kb,_Kj,_Kc,_);return _IT(_Km,_Kl,_Kk,_);}};if(!E(_Kw)){var _KE=__isUndef(_Kv);if(!E(_KE)){return C > 19 ? new F(function(){return _Kx(_,new T1(1,_Kv));}) : (++C,_Kx(_,new T1(1,_Kv)));}else{return C > 19 ? new F(function(){return _Kx(_,__Z);}) : (++C,_Kx(_,__Z));}}else{return C > 19 ? new F(function(){return _Kx(_,__Z);}) : (++C,_Kx(_,__Z));}}};if(!E(_Kr)){var _KF=__isUndef(_Kp);if(!E(_KF)){return C > 19 ? new F(function(){return _Ks(_,new T1(1,_Kp));}) : (++C,_Ks(_,new T1(1,_Kp)));}else{return C > 19 ? new F(function(){return _Ks(_,__Z);}) : (++C,_Ks(_,__Z));}}else{return C > 19 ? new F(function(){return _Ks(_,__Z);}) : (++C,_Ks(_,__Z));}},_KG=_F6(_Kh,_K4,_Kn,_),_KH=_F6(_Kh,_K3,function(_KI,_){var _KJ=_Jh(_Kb,new T2(1,new T2(0,new T2(1,0,new T2(1,0,new T2(1,0,_JZ))),_K1),new T2(1,new T2(0,new T2(1,0,new T2(1,0,new T2(1,1,_JZ))),_JY),new T2(1,new T2(0,new T2(1,0,new T2(1,0,new T2(1,1,__Z))),_K0),__Z))),_Kc,_);return _JH(0,false,_);},_),_KK=_zM(E(_Kh),E(_zP));return 0;},_KL=function(_){var _KM=_zX(_Bm,_);return _zX(_K2,_);},_KN=new T(function(){return B(_EE(_zE,_z7,_z3,_zP,0,function(_KO,_){return C > 19 ? new F(function(){return _KL(_);}) : (++C,_KL(_));}));}),_KP=new T(function(){return _uC(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:40:5-13");}),__Z,__Z));}),_KQ=new T(function(){return unCStr("menuButton");}),_KR=function(_KS){return E(E(_KS).b);},_KT=function(_KU){return E(E(_KU).a);},_KV=function(_KW,_){var _KX=B(A1(_KN,_)),_KY=_zW(toJSStr(E(_KQ))),_KZ=__eq(_KY,E(_v7)),_L0=function(_,_L1){var _L2=E(_L1);if(!_L2._){return die(_KP);}else{var _L3=_L2.a,_L4=B(A(_EE,[_zE,_z7,_z3,_L3,0,function(_L5,_){return _K8(_L3,_KW,_);},_])),_L6=_IT(new T(function(){return E(E(E(_KW).c).a);},1),new T(function(){return E(E(E(_KW).c).c);}),new T(function(){return E(E(E(_KW).c).d);}),_),_L7=_Jh(new T(function(){return E(E(E(_KW).d).a);},1),new T(function(){return E(E(E(_KW).d).c);}),new T(function(){return E(E(E(_KW).d).d);}),_),_L8=_JH(new T(function(){return _KR(_KW);},1),new T(function(){return _KT(_KW);},1),_);return 0;}};if(!E(_KZ)){var _L9=__isUndef(_KY);if(!E(_L9)){return _L0(_,new T1(1,_KY));}else{return _L0(_,__Z);}}else{return _L0(_,__Z);}},_BR=function(_La){return new T1(0,function(_){var _Lb=_KV(_La,_);return _wN;});},_Lc=new T(function(){return B(A2(_xW,new T3(1,-1,_Bn,new T2(0,new T(function(){return unCStr("PrimaLat");}),new T(function(){return unCStr("useS (useCl (simpleCl (usePN Augustus_PN) (complA laetus_A)))");}))),_BR));}),_Ld=function(_){var _Le=_a(_Lc,__Z,_);return 0;},_Lf=function(_){return _Ld(_);};
var hasteMain = function() {B(A(_Lf, [0]));};window.onload = hasteMain;