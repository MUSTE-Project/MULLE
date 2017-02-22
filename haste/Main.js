"use strict";
var __haste_prog_id = '82751e65eb35d4a1eabf07153c2050436a84c1bbd3504bd56d325191df9b0c16';
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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=new T1(0,_),_i=new T(function(){return toJSStr(_4);}),_j=function(_k){return E(_i);},_l=function(_m,_){var _n=E(_m);if(!_n._){return _4;}else{var _o=B(_l(_n.b,_));return new T2(1,_5,_o);}},_p=function(_q,_){var _r=__arr2lst(0,_q);return new F(function(){return _l(_r,_);});},_s=function(_t,_){return new F(function(){return _p(E(_t),_);});},_u=function(_){return _5;},_v=function(_w,_){return new F(function(){return _u(_);});},_x=new T2(0,_v,_s),_y=function(_){return new F(function(){return __jsNull();});},_z=function(_A){var _B=B(A1(_A,_));return E(_B);},_C=new T(function(){return B(_z(_y));}),_D=new T(function(){return E(_C);}),_E=function(_F){return E(_D);},_G=function(_H,_I){var _J=E(_I);return (_J._==0)?__Z:new T2(1,new T(function(){return B(A1(_H,_J.a));}),new T(function(){return B(_G(_H,_J.b));}));},_K=function(_L){return new F(function(){return __lst2arr(B(_G(_E,_L)));});},_M=new T2(0,_E,_K),_N=new T4(0,_M,_x,_j,_j),_O="application/octet-stream",_P=function(_Q){return E(_O);},_R="blob",_S=function(_T){return E(_R);},_U=function(_V,_){var _W=E(_V);if(!_W._){return _4;}else{var _X=B(_U(_W.b,_));return new T2(1,_W.a,_X);}},_Y=function(_Z,_){var _10=__arr2lst(0,_Z);return new F(function(){return _U(_10,_);});},_11=function(_12,_){return new F(function(){return _Y(E(_12),_);});},_13=function(_14,_){return _14;},_15=new T2(0,_13,_11),_16=function(_17){return E(_17);},_18=function(_19){return new F(function(){return __lst2arr(B(_G(_16,_19)));});},_1a=new T2(0,_16,_18),_1b=new T4(0,_1a,_15,_P,_S),_1c=function(_1d,_1e,_1f){var _1g=function(_1h){var _1i=new T(function(){return B(A1(_1f,_1h));});return new F(function(){return A1(_1e,function(_1j){return E(_1i);});});};return new F(function(){return A1(_1d,_1g);});},_1k=function(_1l,_1m,_1n){var _1o=new T(function(){return B(A1(_1m,function(_1p){return new F(function(){return A1(_1n,_1p);});}));});return new F(function(){return A1(_1l,function(_1q){return E(_1o);});});},_1r=function(_1s,_1t,_1u){var _1v=function(_1w){var _1x=function(_1y){return new F(function(){return A1(_1u,new T(function(){return B(A1(_1w,_1y));}));});};return new F(function(){return A1(_1t,_1x);});};return new F(function(){return A1(_1s,_1v);});},_1z=function(_1A,_1B){return new F(function(){return A1(_1B,_1A);});},_1C=function(_1D,_1E,_1F){var _1G=new T(function(){return B(A1(_1F,_1D));});return new F(function(){return A1(_1E,function(_1H){return E(_1G);});});},_1I=function(_1J,_1K,_1L){var _1M=function(_1N){return new F(function(){return A1(_1L,new T(function(){return B(A1(_1J,_1N));}));});};return new F(function(){return A1(_1K,_1M);});},_1O=new T2(0,_1I,_1C),_1P=new T5(0,_1O,_1z,_1r,_1k,_1c),_1Q=function(_1R,_1S,_1T){return new F(function(){return A1(_1R,function(_1U){return new F(function(){return A2(_1S,_1U,_1T);});});});},_1V=function(_1W){return E(E(_1W).b);},_1X=function(_1Y,_1Z){return new F(function(){return A3(_1V,_20,_1Y,function(_21){return E(_1Z);});});},_22=function(_23){return new F(function(){return err(_23);});},_20=new T(function(){return new T5(0,_1P,_1Q,_1X,_1z,_22);}),_24=function(_25,_26,_){var _27=B(A1(_26,_));return new T(function(){return B(A1(_25,_27));});},_28=function(_29,_2a){return new T1(0,function(_){return new F(function(){return _24(_2a,_29,_);});});},_2b=new T2(0,_20,_28),_2c=function(_2d){return new T0(2);},_2e=function(_2f){var _2g=new T(function(){return B(A1(_2f,_2c));}),_2h=function(_2i){return new T1(1,new T2(1,new T(function(){return B(A1(_2i,_5));}),new T2(1,_2g,_4)));};return E(_2h);},_2j=function(_2k){return E(_2k);},_2l=new T3(0,_2b,_2j,_2e),_2m=function(_2n){return E(E(_2n).a);},_2o=function(_2p,_2q,_2r,_2s,_2t){var _2u=B(A2(_2m,_2p,E(_2t)));return new F(function(){return A2(_2q,_2r,new T2(1,_2u,E(_2s)));});},_2v=function(_2w){return E(E(_2w).a);},_2x=function(_2y){return E(E(_2y).a);},_2z=function(_2A){return E(E(_2A).a);},_2B=function(_2C){return E(E(_2C).b);},_2D=new T(function(){return B(unCStr("base"));}),_2E=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_2F=new T(function(){return B(unCStr("IOException"));}),_2G=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_2D,_2E,_2F),_2H=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_2G,_4,_4),_2I=function(_2J){return E(_2H);},_2K=function(_2L){return E(E(_2L).a);},_2M=function(_2N,_2O,_2P){var _2Q=B(A1(_2N,_)),_2R=B(A1(_2O,_)),_2S=hs_eqWord64(_2Q.a,_2R.a);if(!_2S){return __Z;}else{var _2T=hs_eqWord64(_2Q.b,_2R.b);return (!_2T)?__Z:new T1(1,_2P);}},_2U=function(_2V){var _2W=E(_2V);return new F(function(){return _2M(B(_2K(_2W.a)),_2I,_2W.b);});},_2X=new T(function(){return B(unCStr(": "));}),_2Y=new T(function(){return B(unCStr(")"));}),_2Z=new T(function(){return B(unCStr(" ("));}),_30=new T(function(){return B(unCStr("interrupted"));}),_31=new T(function(){return B(unCStr("system error"));}),_32=new T(function(){return B(unCStr("unsatisified constraints"));}),_33=new T(function(){return B(unCStr("user error"));}),_34=new T(function(){return B(unCStr("permission denied"));}),_35=new T(function(){return B(unCStr("illegal operation"));}),_36=new T(function(){return B(unCStr("end of file"));}),_37=new T(function(){return B(unCStr("resource exhausted"));}),_38=new T(function(){return B(unCStr("resource busy"));}),_39=new T(function(){return B(unCStr("does not exist"));}),_3a=new T(function(){return B(unCStr("already exists"));}),_3b=new T(function(){return B(unCStr("resource vanished"));}),_3c=new T(function(){return B(unCStr("timeout"));}),_3d=new T(function(){return B(unCStr("unsupported operation"));}),_3e=new T(function(){return B(unCStr("hardware fault"));}),_3f=new T(function(){return B(unCStr("inappropriate type"));}),_3g=new T(function(){return B(unCStr("invalid argument"));}),_3h=new T(function(){return B(unCStr("failed"));}),_3i=new T(function(){return B(unCStr("protocol error"));}),_3j=function(_3k,_3l){switch(E(_3k)){case 0:return new F(function(){return _0(_3a,_3l);});break;case 1:return new F(function(){return _0(_39,_3l);});break;case 2:return new F(function(){return _0(_38,_3l);});break;case 3:return new F(function(){return _0(_37,_3l);});break;case 4:return new F(function(){return _0(_36,_3l);});break;case 5:return new F(function(){return _0(_35,_3l);});break;case 6:return new F(function(){return _0(_34,_3l);});break;case 7:return new F(function(){return _0(_33,_3l);});break;case 8:return new F(function(){return _0(_32,_3l);});break;case 9:return new F(function(){return _0(_31,_3l);});break;case 10:return new F(function(){return _0(_3i,_3l);});break;case 11:return new F(function(){return _0(_3h,_3l);});break;case 12:return new F(function(){return _0(_3g,_3l);});break;case 13:return new F(function(){return _0(_3f,_3l);});break;case 14:return new F(function(){return _0(_3e,_3l);});break;case 15:return new F(function(){return _0(_3d,_3l);});break;case 16:return new F(function(){return _0(_3c,_3l);});break;case 17:return new F(function(){return _0(_3b,_3l);});break;default:return new F(function(){return _0(_30,_3l);});}},_3m=new T(function(){return B(unCStr("}"));}),_3n=new T(function(){return B(unCStr("{handle: "));}),_3o=function(_3p,_3q,_3r,_3s,_3t,_3u){var _3v=new T(function(){var _3w=new T(function(){var _3x=new T(function(){var _3y=E(_3s);if(!_3y._){return E(_3u);}else{var _3z=new T(function(){return B(_0(_3y,new T(function(){return B(_0(_2Y,_3u));},1)));},1);return B(_0(_2Z,_3z));}},1);return B(_3j(_3q,_3x));}),_3A=E(_3r);if(!_3A._){return E(_3w);}else{return B(_0(_3A,new T(function(){return B(_0(_2X,_3w));},1)));}}),_3B=E(_3t);if(!_3B._){var _3C=E(_3p);if(!_3C._){return E(_3v);}else{var _3D=E(_3C.a);if(!_3D._){var _3E=new T(function(){var _3F=new T(function(){return B(_0(_3m,new T(function(){return B(_0(_2X,_3v));},1)));},1);return B(_0(_3D.a,_3F));},1);return new F(function(){return _0(_3n,_3E);});}else{var _3G=new T(function(){var _3H=new T(function(){return B(_0(_3m,new T(function(){return B(_0(_2X,_3v));},1)));},1);return B(_0(_3D.a,_3H));},1);return new F(function(){return _0(_3n,_3G);});}}}else{return new F(function(){return _0(_3B.a,new T(function(){return B(_0(_2X,_3v));},1));});}},_3I=function(_3J){var _3K=E(_3J);return new F(function(){return _3o(_3K.a,_3K.b,_3K.c,_3K.d,_3K.f,_4);});},_3L=function(_3M,_3N,_3O){var _3P=E(_3N);return new F(function(){return _3o(_3P.a,_3P.b,_3P.c,_3P.d,_3P.f,_3O);});},_3Q=function(_3R,_3S){var _3T=E(_3R);return new F(function(){return _3o(_3T.a,_3T.b,_3T.c,_3T.d,_3T.f,_3S);});},_3U=44,_3V=93,_3W=91,_3X=function(_3Y,_3Z,_40){var _41=E(_3Z);if(!_41._){return new F(function(){return unAppCStr("[]",_40);});}else{var _42=new T(function(){var _43=new T(function(){var _44=function(_45){var _46=E(_45);if(!_46._){return E(new T2(1,_3V,_40));}else{var _47=new T(function(){return B(A2(_3Y,_46.a,new T(function(){return B(_44(_46.b));})));});return new T2(1,_3U,_47);}};return B(_44(_41.b));});return B(A2(_3Y,_41.a,_43));});return new T2(1,_3W,_42);}},_48=function(_49,_4a){return new F(function(){return _3X(_3Q,_49,_4a);});},_4b=new T3(0,_3L,_3I,_48),_4c=new T(function(){return new T5(0,_2I,_4b,_4d,_2U,_3I);}),_4d=function(_4e){return new T2(0,_4c,_4e);},_4f="status-text",_4g="status",_4h="http",_4i="network",_4j="type",_4k=__Z,_4l=__Z,_4m=7,_4n=function(_4o,_){var _4p=__get(_4o,E(_4j)),_4q=String(_4p),_4r=strEq(_4q,E(_4i));if(!E(_4r)){var _4s=strEq(_4q,E(_4h));if(!E(_4s)){var _4t=new T(function(){var _4u=new T(function(){return B(unAppCStr("unknown type of ajax error: ",new T(function(){return fromJSStr(_4q);})));});return B(_4d(new T6(0,_4l,_4m,_4,_4u,_4l,_4l)));});return new F(function(){return die(_4t);});}else{var _4v=__get(_4o,E(_4g)),_4w=__get(_4o,E(_4f));return new T2(1,new T(function(){var _4x=Number(_4v);return jsTrunc(_4x);}),new T(function(){return String(_4w);}));}}else{return _4k;}},_4y=function(_4z,_){var _4A=E(_4z);if(!_4A._){return _4;}else{var _4B=B(_4n(E(_4A.a),_)),_4C=B(_4y(_4A.b,_));return new T2(1,_4B,_4C);}},_4D=function(_4E,_){var _4F=__arr2lst(0,_4E);return new F(function(){return _4y(_4F,_);});},_4G=function(_4H,_){return new F(function(){return _4D(E(_4H),_);});},_4I=function(_4J,_){return new F(function(){return _4n(E(_4J),_);});},_4K=new T2(0,_4I,_4G),_4L=function(_4M){return E(E(_4M).a);},_4N=function(_4O,_4P,_){var _4Q=__eq(_4P,E(_D));if(!E(_4Q)){var _4R=__isUndef(_4P);if(!E(_4R)){var _4S=B(A3(_4L,_4O,_4P,_));return new T1(1,_4S);}else{return _4l;}}else{return _4l;}},_4T=function(_4U,_){return new F(function(){return _4N(_4K,E(_4U),_);});},_4V=function(_4W,_4X,_){var _4Y=__arr2lst(0,_4X),_4Z=function(_50,_){var _51=E(_50);if(!_51._){return _4;}else{var _52=_51.b,_53=E(_51.a),_54=__eq(_53,E(_D));if(!E(_54)){var _55=__isUndef(_53);if(!E(_55)){var _56=B(A3(_4L,_4W,_53,_)),_57=B(_4Z(_52,_));return new T2(1,new T1(1,_56),_57);}else{var _58=B(_4Z(_52,_));return new T2(1,_4l,_58);}}else{var _59=B(_4Z(_52,_));return new T2(1,_4l,_59);}}};return new F(function(){return _4Z(_4Y,_);});},_5a=function(_5b,_){return new F(function(){return _4V(_4K,E(_5b),_);});},_5c=new T2(0,_4T,_5a),_5d=2,_5e=function(_5f){return E(_5d);},_5g=function(_5h,_5i,_){var _5j=B(A2(_5h,new T(function(){var _5k=E(_5i),_5l=__eq(_5k,E(_D));if(!E(_5l)){var _5m=__isUndef(_5k);if(!E(_5m)){return new T1(1,_5k);}else{return __Z;}}else{return __Z;}}),_));return _D;},_5n=new T2(0,_5g,_5e),_5o=function(_5p){return E(E(_5p).a);},_5q=function(_5r,_5s,_5t,_5u){var _5v=new T(function(){return B(A1(_5t,new T(function(){var _5w=B(A3(_4L,_5r,_5u,_));return E(_5w);})));});return new F(function(){return A2(_5o,_5s,_5v);});},_5x=function(_5y){return E(E(_5y).b);},_5z=new T(function(){return B(unCStr("Prelude.undefined"));}),_5A=new T(function(){return B(err(_5z));}),_5B=function(_5C,_5D,_5E){var _5F=__createJSFunc(1+B(A2(_5x,_5D,new T(function(){return B(A1(_5E,_5A));})))|0,function(_5G){return new F(function(){return _5q(_5C,_5D,_5E,_5G);});});return E(_5F);},_5H=function(_5I){return new F(function(){return _5B(_5c,_5n,_5I);});},_5J=function(_5K,_5L,_5M){return new F(function(){return _5B(_5K,_5L,_5M);});},_5N=function(_5O,_5P,_5Q){var _5R=__lst2arr(B(_G(function(_5S){return new F(function(){return _5J(_5O,_5P,_5S);});},_5Q)));return E(_5R);},_5T=function(_5U){return new F(function(){return _5N(_5c,_5n,_5U);});},_5V=new T2(0,_5H,_5T),_5W=function(_5X,_5Y,_5Z,_){var _60=__apply(_5Y,E(_5Z));return new F(function(){return A3(_4L,_5X,_60,_);});},_61=function(_62,_63,_64,_){return new F(function(){return _5W(_62,E(_63),_64,_);});},_65=function(_66,_67,_68,_){return new F(function(){return _61(_66,_67,_68,_);});},_69=function(_6a,_6b,_){return new F(function(){return _65(_x,_6a,_6b,_);});},_6c=function(_6d){return E(E(_6d).c);},_6e=0,_6f=new T(function(){return eval("(function(method, uri, mimeout, responseType, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, uri);xhr.responseType = responseType;if(mimeout != \'\') {xhr.setRequestHeader(\'Content-type\', mimeout);}xhr.addEventListener(\'load\', function() {if(xhr.status < 400) {cb(null, xhr.response);}else {cb({\'type\':\'http\', \'status\':xhr.status, \'status-text\': xhr.statusText}, null);}});xhr.addEventListener(\'error\', function() {if(xhr.status != 0) {cb({\'type\':\'http\', \'status\':xhr.status, \'status-text\': xhr.statusText}, null);} else {cb({\'type\':\'network\'}, null);}});xhr.send(postdata);})");}),_6g=function(_6h){return E(E(_6h).b);},_6i=function(_6j){return E(E(_6j).b);},_6k=new T(function(){return B(unCStr("base"));}),_6l=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6m=new T(function(){return B(unCStr("PatternMatchFail"));}),_6n=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6k,_6l,_6m),_6o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6n,_4,_4),_6p=function(_6q){return E(_6o);},_6r=function(_6s){var _6t=E(_6s);return new F(function(){return _2M(B(_2K(_6t.a)),_6p,_6t.b);});},_6u=function(_6v){return E(E(_6v).a);},_6w=function(_6x){return new T2(0,_6y,_6x);},_6z=function(_6A,_6B){return new F(function(){return _0(E(_6A).a,_6B);});},_6C=function(_6D,_6E){return new F(function(){return _3X(_6z,_6D,_6E);});},_6F=function(_6G,_6H,_6I){return new F(function(){return _0(E(_6H).a,_6I);});},_6J=new T3(0,_6F,_6u,_6C),_6y=new T(function(){return new T5(0,_6p,_6J,_6w,_6r,_6u);}),_6K=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_6L=function(_6M){return E(E(_6M).c);},_6N=function(_6O,_6P){return new F(function(){return die(new T(function(){return B(A2(_6L,_6P,_6O));}));});},_6Q=function(_6R,_6S){return new F(function(){return _6N(_6R,_6S);});},_6T=function(_6U,_6V){var _6W=E(_6V);if(!_6W._){return new T2(0,_4,_4);}else{var _6X=_6W.a;if(!B(A1(_6U,_6X))){return new T2(0,_4,_6W);}else{var _6Y=new T(function(){var _6Z=B(_6T(_6U,_6W.b));return new T2(0,_6Z.a,_6Z.b);});return new T2(0,new T2(1,_6X,new T(function(){return E(E(_6Y).a);})),new T(function(){return E(E(_6Y).b);}));}}},_70=32,_71=new T(function(){return B(unCStr("\n"));}),_72=function(_73){return (E(_73)==124)?false:true;},_74=function(_75,_76){var _77=B(_6T(_72,B(unCStr(_75)))),_78=_77.a,_79=function(_7a,_7b){var _7c=new T(function(){var _7d=new T(function(){return B(_0(_76,new T(function(){return B(_0(_7b,_71));},1)));});return B(unAppCStr(": ",_7d));},1);return new F(function(){return _0(_7a,_7c);});},_7e=E(_77.b);if(!_7e._){return new F(function(){return _79(_78,_4);});}else{if(E(_7e.a)==124){return new F(function(){return _79(_78,new T2(1,_70,_7e.b));});}else{return new F(function(){return _79(_78,_4);});}}},_7f=function(_7g){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_7g,_6K));})),_6y);});},_7h=new T(function(){return B(_7f("src/Haste/Ajax.hs:(61,7)-(63,60)|case"));}),_7i="PUT",_7j="POST",_7k="DELETE",_7l="GET",_7m=function(_7n){return E(E(_7n).c);},_7o=new T1(1,_4),_7p=function(_){return new F(function(){return nMV(_7o);});},_7q=new T0(2),_7r=function(_7s,_7t,_7u){var _7v=function(_7w){var _7x=function(_){var _7y=E(_7t),_7z=rMV(_7y),_7A=E(_7z);if(!_7A._){var _7B=new T(function(){var _7C=new T(function(){return B(A1(_7w,_5));});return B(_0(_7A.b,new T2(1,new T2(0,_7u,function(_7D){return E(_7C);}),_4)));}),_=wMV(_7y,new T2(0,_7A.a,_7B));return _7q;}else{var _7E=E(_7A.a);if(!_7E._){var _=wMV(_7y,new T2(0,_7u,_4));return new T(function(){return B(A1(_7w,_5));});}else{var _=wMV(_7y,new T1(1,_7E.b));return new T1(1,new T2(1,new T(function(){return B(A1(_7w,_5));}),new T2(1,new T(function(){return B(A2(_7E.a,_7u,_2c));}),_4)));}}};return new T1(0,_7x);};return new F(function(){return A2(_6g,_7s,_7v);});},_7F=function(_7G){return E(E(_7G).d);},_7H=function(_7I,_7J){var _7K=function(_7L){var _7M=function(_){var _7N=E(_7J),_7O=rMV(_7N),_7P=E(_7O);if(!_7P._){var _7Q=_7P.a,_7R=E(_7P.b);if(!_7R._){var _=wMV(_7N,_7o);return new T(function(){return B(A1(_7L,_7Q));});}else{var _7S=E(_7R.a),_=wMV(_7N,new T2(0,_7S.a,_7R.b));return new T1(1,new T2(1,new T(function(){return B(A1(_7L,_7Q));}),new T2(1,new T(function(){return B(A1(_7S.b,_2c));}),_4)));}}else{var _7T=new T(function(){var _7U=function(_7V){var _7W=new T(function(){return B(A1(_7L,_7V));});return function(_7X){return E(_7W);};};return B(_0(_7P.a,new T2(1,_7U,_4)));}),_=wMV(_7N,new T1(1,_7T));return _7q;}};return new T1(0,_7M);};return new F(function(){return A2(_6g,_7I,_7K);});},_7Y=function(_7Z,_80,_81,_82,_83,_84){var _85=B(_2x(_7Z)),_86=new T(function(){return B(_6g(_7Z));}),_87=new T(function(){return B(_6i(_85));}),_88=B(_2z(_85)),_89=new T(function(){return B(_2B(_81));}),_8a=new T(function(){var _8b=function(_8c){var _8d=E(_84),_8e=E(_82),_8f=strEq(E(_i),_8e);if(!E(_8f)){var _8g=E(_8e);}else{var _8g=B(A2(_7m,_80,_6e));}var _8h=B(A2(_7F,_81,_6e)),_8i=E(_D);return function(_5G){return new F(function(){return _2o(_5V,_69,_6f,new T2(1,_8i,new T2(1,_8h,new T2(1,_8g,new T2(1,_8d,new T2(1,_8c,_4))))),_5G);});};},_8j=function(_8k,_8l){var _8m=E(_84),_8n=E(_82),_8o=strEq(E(_i),_8n);if(!E(_8o)){var _8p=E(_8n);}else{var _8p=B(A2(_7m,_80,_6e));}var _8q=B(A2(_7F,_81,_6e)),_8r=E(_8k);return function(_5G){return new F(function(){return _2o(_5V,_69,_6f,new T2(1,_8r,new T2(1,_8q,new T2(1,_8p,new T2(1,_8m,new T2(1,_8l,_4))))),_5G);});};},_8s=E(_83);switch(_8s._){case 0:return B(_8b(E(_7l)));break;case 1:return B(_8b(E(_7k)));break;case 2:return B(_8j(new T(function(){return B(A2(_2m,B(_2v(_80)),_8s.a));}),E(_7j)));break;default:return B(_8j(new T(function(){return B(A2(_2m,B(_2v(_80)),_8s.a));}),E(_7i)));}}),_8t=function(_8u){var _8v=new T(function(){return B(A1(_86,new T(function(){return B(_7H(_2l,_8u));})));}),_8w=new T(function(){var _8x=new T(function(){var _8y=function(_8z,_8A,_){var _8B=E(_8A);if(!_8B._){var _8C=E(_8z);if(!_8C._){return E(_7h);}else{return new F(function(){return _c(new T(function(){return B(A(_7r,[_2l,_8u,new T1(0,_8C.a),_2c]));}),_4,_);});}}else{var _8D=B(A3(_4L,_89,_8B.a,_));return new F(function(){return _c(new T(function(){return B(A(_7r,[_2l,_8u,new T1(1,_8D),_2c]));}),_4,_);});}};return B(A1(_8a,_8y));});return B(A1(_87,_8x));});return new F(function(){return A3(_6c,_88,_8w,_8v);});};return new F(function(){return A3(_1V,_88,new T(function(){return B(A2(_6i,_85,_7p));}),_8t);});},_8E="w8",_8F=function(_8G){return E(_8E);},_8H=function(_8I,_8J){var _8K=E(_8J);return new T2(0,_8K.a,_8K.b);},_8L=function(_8M,_8N){return E(_8N).c;},_8O=function(_8P){var _8Q=B(A1(_8P,_));return E(_8Q);},_8R=function(_8S,_8T,_8U,_8V){var _8W=function(_){var _8X=E(_8U),_8Y=_8X.d,_8Z=_8Y["byteLength"],_90=newByteArr(_8Z),_91=_90,_92=memcpy(_91,_8Y,_8Z>>>0),_93=function(_94,_){while(1){var _95=E(_94);if(!_95._){return _5;}else{var _96=E(_95.a),_97=E(_96.a),_98=_91["v"]["w8"][_97],_=_91["v"]["w8"][_97]=B(A2(_8T,_98,_96.b));_94=_95.b;continue;}}},_99=B(_93(_8V,_));return new T4(0,E(_8X.a),E(_8X.b),_8X.c,_91);};return new F(function(){return _8O(_8W);});},_9a=function(_9b){return E(E(_9b).f);},_9c=new T(function(){return B(unCStr("Negative range size"));}),_9d=new T(function(){return B(err(_9c));}),_9e=function(_9f,_9g,_9h,_9i,_9j){var _9k=E(_9i),_9l=function(_){var _9m=B(A2(_9a,_9f,_9k)),_9n=newByteArr(_9m),_9o=_9n;if(_9m>=0){var _9p=_9m-1|0,_9q=function(_){var _9r=function(_9s,_){while(1){var _9t=E(_9s);if(!_9t._){return _5;}else{var _9u=E(_9t.a),_9v=E(_9u.a),_9w=_9o["v"]["w8"][_9v],_=_9o["v"]["w8"][_9v]=B(A2(_9g,_9w,_9u.b));_9s=_9t.b;continue;}}},_9x=B(_9r(_9j,_));return new T4(0,E(_9k.a),E(_9k.b),_9m,_9o);};if(0<=_9p){var _9y=function(_9z,_){while(1){var _=_9o["v"]["w8"][_9z]=E(_9h);if(_9z!=_9p){var _9A=_9z+1|0;_9z=_9A;continue;}else{return _5;}}},_9B=B(_9y(0,_));return new F(function(){return _9q(_);});}else{return new F(function(){return _9q(_);});}}else{return E(_9d);}},_9C=E(_9l);return new F(function(){return _8O(_9C);});},_9D=function(_9E,_9F,_9G){var _9H=E(_9F),_9I=function(_){var _9J=B(A2(_9a,_9E,_9H)),_9K=newByteArr(_9J),_9L=_9K;if(_9J>=0){var _9M=_9J-1|0,_9N=function(_){var _9O=function(_9P,_){while(1){var _9Q=E(_9P);if(!_9Q._){return _5;}else{var _9R=E(_9Q.a),_=_9L["v"]["w8"][E(_9R.a)]=E(_9R.b);_9P=_9Q.b;continue;}}},_9S=B(_9O(_9G,_));return new T4(0,E(_9H.a),E(_9H.b),_9J,_9L);};if(0<=_9M){var _9T=function(_9U,_){while(1){var _=_9L["v"]["w8"][_9U]=0;if(_9U!=_9M){var _9V=_9U+1|0;_9U=_9V;continue;}else{return _5;}}},_9W=B(_9T(0,_));return new F(function(){return _9N(_);});}else{return new F(function(){return _9N(_);});}}else{return E(_9d);}},_9X=E(_9I);return new F(function(){return _8O(_9X);});},_9Y=function(_9Z,_a0,_a1){return E(_a0).d["v"]["w8"][E(_a1)];},_a2=function(_a3,_a4,_a5){var _a6=function(_){var _a7=E(_a4),_a8=_a7.d,_a9=_a8["byteLength"],_aa=newByteArr(_a9),_ab=_aa,_ac=memcpy(_ab,_a8,_a9>>>0),_ad=function(_ae,_){while(1){var _af=E(_ae);if(!_af._){return _5;}else{var _ag=E(_af.a),_=_ab["v"]["w8"][E(_ag.a)]=E(_ag.b);_ae=_af.b;continue;}}},_ah=B(_ad(_a5,_));return new T4(0,E(_a7.a),E(_a7.b),_a7.c,_ab);};return new F(function(){return _8O(_a6);});},_ai={_:0,a:_8H,b:_8L,c:_9D,d:_9Y,e:_a2,f:_8R,g:_9e},_aj=function(_ak,_al,_){var _am=E(_al);return new T2(0,_am.a,_am.b);},_an=function(_ao,_ap,_){return new F(function(){return _aj(_ao,_ap,_);});},_aq=function(_ar,_as,_){return E(_as).c;},_at=function(_ao,_ap,_){return new F(function(){return _aq(_ao,_ap,_);});},_au=new T(function(){return B(unCStr("Negative range size"));}),_av=new T(function(){return B(err(_au));}),_aw=function(_ax,_ay,_az,_aA,_){var _aB=B(A2(_9a,_ax,new T2(0,_ay,_az))),_aC=newByteArr(_aB);if(_aB>=0){var _aD=_aB-1|0,_aE=new T(function(){return new T4(0,E(_ay),E(_az),_aB,_aC);});if(0<=_aD){var _aF=function(_aG,_){while(1){var _=E(_aE).d["v"]["w8"][_aG]=E(_aA);if(_aG!=_aD){var _aH=_aG+1|0;_aG=_aH;continue;}else{return _5;}}},_aI=B(_aF(0,_));return _aE;}else{return _aE;}}else{return E(_av);}},_aJ=function(_aK,_aL,_aM,_){var _aN=E(_aL);return new F(function(){return _aw(_aK,_aN.a,_aN.b,_aM,_);});},_aO=function(_aP,_ao,_ap,_){return new F(function(){return _aJ(_aP,_ao,_ap,_);});},_aQ=function(_aR,_aS,_aT,_){var _aU=B(A2(_9a,_aR,new T2(0,_aS,_aT))),_aV=newByteArr(_aU);return new T(function(){return new T4(0,E(_aS),E(_aT),_aU,_aV);});},_aW=function(_aX,_aY,_){var _aZ=E(_aY);return new F(function(){return _aQ(_aX,_aZ.a,_aZ.b,_);});},_b0=function(_ao,_ap,_){return new F(function(){return _aW(_ao,_ap,_);});},_b1=function(_b2,_b3,_b4,_){return E(_b3).d["v"]["w8"][E(_b4)];},_b5=function(_aP,_ao,_ap,_){return new F(function(){return _b1(_aP,_ao,_ap,_);});},_b6=function(_b7,_b8,_b9,_ba,_){var _=E(_b8).d["v"]["w8"][E(_b9)]=E(_ba);return _5;},_bb=function(_bc,_aP,_ao,_ap,_){return new F(function(){return _b6(_bc,_aP,_ao,_ap,_);});},_bd=function(_be,_bf,_){var _bg=B(A1(_be,_)),_bh=B(A1(_bf,_));return _bg;},_bi=function(_bj,_bk,_){var _bl=B(A1(_bj,_)),_bm=B(A1(_bk,_));return new T(function(){return B(A1(_bl,_bm));});},_bn=function(_bo,_bp,_){var _bq=B(A1(_bp,_));return _bo;},_br=new T2(0,_24,_bn),_bs=function(_bt,_){return _bt;},_bu=function(_bv,_bw,_){var _bx=B(A1(_bv,_));return new F(function(){return A1(_bw,_);});},_by=new T5(0,_br,_bs,_bi,_bu,_bd),_bz=new T(function(){return E(_4c);}),_bA=function(_bB){return new T6(0,_4l,_4m,_4,_bB,_4l,_4l);},_bC=function(_bD,_){var _bE=new T(function(){return B(A2(_6L,_bz,new T(function(){return B(A1(_bA,_bD));})));});return new F(function(){return die(_bE);});},_bF=function(_bG,_){return new F(function(){return _bC(_bG,_);});},_bH=function(_bI){return new F(function(){return A1(_bF,_bI);});},_bJ=function(_bK,_bL,_){var _bM=B(A1(_bK,_));return new F(function(){return A2(_bL,_bM,_);});},_bN=new T5(0,_by,_bJ,_bu,_bs,_bH),_bO={_:0,a:_bN,b:_an,c:_at,d:_aO,e:_b0,f:_b0,g:_b5,h:_bb},_bP=new T3(0,_ai,_bO,_8F),_bQ="deltaZ",_bR="deltaY",_bS="deltaX",_bT=function(_bU,_bV){var _bW=jsShowI(_bU);return new F(function(){return _0(fromJSStr(_bW),_bV);});},_bX=41,_bY=40,_bZ=function(_c0,_c1,_c2){if(_c1>=0){return new F(function(){return _bT(_c1,_c2);});}else{if(_c0<=6){return new F(function(){return _bT(_c1,_c2);});}else{return new T2(1,_bY,new T(function(){var _c3=jsShowI(_c1);return B(_0(fromJSStr(_c3),new T2(1,_bX,_c2)));}));}}},_c4=new T(function(){return B(unCStr(")"));}),_c5=new T(function(){return B(_bZ(0,2,_c4));}),_c6=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_c5));}),_c7=function(_c8){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_bZ(0,_c8,_c6));}))));});},_c9=function(_ca,_){return new T(function(){var _cb=Number(E(_ca)),_cc=jsTrunc(_cb);if(_cc<0){return B(_c7(_cc));}else{if(_cc>2){return B(_c7(_cc));}else{return _cc;}}});},_cd=0,_ce=new T3(0,_cd,_cd,_cd),_cf="button",_cg=new T(function(){return eval("jsGetMouseCoords");}),_ch=function(_ci,_){var _cj=E(_ci);if(!_cj._){return _4;}else{var _ck=B(_ch(_cj.b,_));return new T2(1,new T(function(){var _cl=Number(E(_cj.a));return jsTrunc(_cl);}),_ck);}},_cm=function(_cn,_){var _co=__arr2lst(0,_cn);return new F(function(){return _ch(_co,_);});},_cp=function(_cq,_){return new F(function(){return _cm(E(_cq),_);});},_cr=function(_cs,_){return new T(function(){var _ct=Number(E(_cs));return jsTrunc(_ct);});},_cu=new T2(0,_cr,_cp),_cv=function(_cw,_){var _cx=E(_cw);if(!_cx._){return _4;}else{var _cy=B(_cv(_cx.b,_));return new T2(1,_cx.a,_cy);}},_cz=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_cA=new T6(0,_4l,_4m,_4,_cz,_4l,_4l),_cB=new T(function(){return B(_4d(_cA));}),_cC=function(_){return new F(function(){return die(_cB);});},_cD=function(_cE,_cF,_cG,_){var _cH=__arr2lst(0,_cG),_cI=B(_cv(_cH,_)),_cJ=E(_cI);if(!_cJ._){return new F(function(){return _cC(_);});}else{var _cK=E(_cJ.b);if(!_cK._){return new F(function(){return _cC(_);});}else{if(!E(_cK.b)._){var _cL=B(A3(_4L,_cE,_cJ.a,_)),_cM=B(A3(_4L,_cF,_cK.a,_));return new T2(0,_cL,_cM);}else{return new F(function(){return _cC(_);});}}}},_cN=function(_cO,_cP,_){if(E(_cO)==7){var _cQ=__app1(E(_cg),_cP),_cR=B(_cD(_cu,_cu,_cQ,_)),_cS=__get(_cP,E(_bS)),_cT=__get(_cP,E(_bR)),_cU=__get(_cP,E(_bQ));return new T(function(){return new T3(0,E(_cR),E(_4l),E(new T3(0,_cS,_cT,_cU)));});}else{var _cV=__app1(E(_cg),_cP),_cW=B(_cD(_cu,_cu,_cV,_)),_cX=__get(_cP,E(_cf)),_cY=__eq(_cX,E(_D));if(!E(_cY)){var _cZ=__isUndef(_cX);if(!E(_cZ)){var _d0=B(_c9(_cX,_));return new T(function(){return new T3(0,E(_cW),E(new T1(1,_d0)),E(_ce));});}else{return new T(function(){return new T3(0,E(_cW),E(_4l),E(_ce));});}}else{return new T(function(){return new T3(0,E(_cW),E(_4l),E(_ce));});}}},_d1=function(_d2,_d3,_){return new F(function(){return _cN(_d2,E(_d3),_);});},_d4="mouseout",_d5="mouseover",_d6="mousemove",_d7="mouseup",_d8="mousedown",_d9="dblclick",_da="click",_db="wheel",_dc=function(_dd){switch(E(_dd)){case 0:return E(_da);case 1:return E(_d9);case 2:return E(_d8);case 3:return E(_d7);case 4:return E(_d6);case 5:return E(_d5);case 6:return E(_d4);default:return E(_db);}},_de=new T2(0,_dc,_d1),_df=function(_dg){return E(_dg);},_dh=function(_di){return E(E(_di).d);},_dj=function(_dk,_dl){return new F(function(){return A2(_dh,B(_2z(_dk)),new T1(1,_dl));});},_dm=new T2(0,_2j,_dj),_dn=new T2(0,_bN,_2j),_do=new T2(0,_dn,_bs),_dp=new T(function(){return B(unCStr("NoMethodError"));}),_dq=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_6k,_6l,_dp),_dr=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_dq,_4,_4),_ds=function(_dt){return E(_dr);},_du=function(_dv){var _dw=E(_dv);return new F(function(){return _2M(B(_2K(_dw.a)),_ds,_dw.b);});},_dx=function(_dy){return E(E(_dy).a);},_dz=function(_6x){return new T2(0,_dA,_6x);},_dB=function(_dC,_dD){return new F(function(){return _0(E(_dC).a,_dD);});},_dE=function(_dF,_dG){return new F(function(){return _3X(_dB,_dF,_dG);});},_dH=function(_dI,_dJ,_dK){return new F(function(){return _0(E(_dJ).a,_dK);});},_dL=new T3(0,_dH,_dx,_dE),_dA=new T(function(){return new T5(0,_ds,_dL,_dz,_du,_dx);}),_dM=new T(function(){return B(unCStr("No instance nor default method for class operation"));}),_dN=function(_dO){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_dO,_dM));})),_dA);});},_dP=new T(function(){return B(_dN("Data/Binary/Put.hs:17:10-19|>>="));}),_dQ=function(_dR){return E(_dP);},_dS=new T(function(){return B(unCStr(")"));}),_dT=function(_dU,_dV){var _dW=new T(function(){var _dX=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_dV,_4)),_dS));})));},1);return B(_0(B(_bZ(0,_dU,_4)),_dX));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_dW)));});},_dY=function(_dZ){return new F(function(){return _bZ(0,E(_dZ),_4);});},_e0=function(_e1,_e2,_e3){return new F(function(){return _bZ(E(_e1),E(_e2),_e3);});},_e4=function(_e5,_e6){return new F(function(){return _bZ(0,E(_e5),_e6);});},_e7=function(_e8,_e9){return new F(function(){return _3X(_e4,_e8,_e9);});},_ea=new T3(0,_e0,_dY,_e7),_eb=0,_ec=function(_ed,_ee,_ef){return new F(function(){return A1(_ed,new T2(1,_3U,new T(function(){return B(A1(_ee,_ef));})));});},_eg=new T(function(){return B(unCStr(": empty list"));}),_eh=new T(function(){return B(unCStr("Prelude."));}),_ei=function(_ej){return new F(function(){return err(B(_0(_eh,new T(function(){return B(_0(_ej,_eg));},1))));});},_ek=new T(function(){return B(unCStr("foldr1"));}),_el=new T(function(){return B(_ei(_ek));}),_em=function(_en,_eo){var _ep=E(_eo);if(!_ep._){return E(_el);}else{var _eq=_ep.a,_er=E(_ep.b);if(!_er._){return E(_eq);}else{return new F(function(){return A2(_en,_eq,new T(function(){return B(_em(_en,_er));}));});}}},_es=new T(function(){return B(unCStr(" out of range "));}),_et=new T(function(){return B(unCStr("}.index: Index "));}),_eu=new T(function(){return B(unCStr("Ix{"));}),_ev=new T2(1,_bX,_4),_ew=new T2(1,_bX,_ev),_ex=0,_ey=function(_ez){return E(E(_ez).a);},_eA=function(_eB,_eC,_eD,_eE,_eF){var _eG=new T(function(){var _eH=new T(function(){var _eI=new T(function(){var _eJ=new T(function(){var _eK=new T(function(){return B(A3(_em,_ec,new T2(1,new T(function(){return B(A3(_ey,_eD,_ex,_eE));}),new T2(1,new T(function(){return B(A3(_ey,_eD,_ex,_eF));}),_4)),_ew));});return B(_0(_es,new T2(1,_bY,new T2(1,_bY,_eK))));});return B(A(_ey,[_eD,_eb,_eC,new T2(1,_bX,_eJ)]));});return B(_0(_et,new T2(1,_bY,_eI)));},1);return B(_0(_eB,_eH));},1);return new F(function(){return err(B(_0(_eu,_eG)));});},_eL=function(_eM,_eN,_eO,_eP,_eQ){return new F(function(){return _eA(_eM,_eN,_eQ,_eO,_eP);});},_eR=function(_eS,_eT,_eU,_eV){var _eW=E(_eU);return new F(function(){return _eL(_eS,_eT,_eW.a,_eW.b,_eV);});},_eX=function(_eY,_eZ,_f0,_f1){return new F(function(){return _eR(_f1,_f0,_eZ,_eY);});},_f2=new T(function(){return B(unCStr("Int"));}),_f3=function(_f4,_f5,_f6){return new F(function(){return _eX(_ea,new T2(0,_f5,_f6),_f4,_f2);});},_f7=function(_f8,_f9,_fa,_fb,_fc,_fd){var _fe=_f8+_fd|0;if(_f9>_fe){return new F(function(){return _f3(_fe,_f9,_fa);});}else{if(_fe>_fa){return new F(function(){return _f3(_fe,_f9,_fa);});}else{var _ff=_fe-_f9|0;if(0>_ff){return new F(function(){return _dT(_ff,_fb);});}else{if(_ff>=_fb){return new F(function(){return _dT(_ff,_fb);});}else{return _fc["v"]["w8"][_ff];}}}}},_fg=function(_fh){return new F(function(){return err(B(unAppCStr("getWord8: no bytes left at ",new T(function(){return B(_bZ(0,_fh,_4));}))));});},_fi=function(_fj,_fk,_fl,_fm){if(_fm>=_fk){return new F(function(){return _fg(_fm);});}else{return new T2(0,new T(function(){var _fn=E(_fl);return B(_f7(_fj,E(_fn.a),E(_fn.b),_fn.c,_fn.d,_fm));}),_fm+1|0);}},_fo=function(_fp,_fq,_fr,_fs){var _ft=B(_fi(_fp,_fq,_fr,_fs)),_fu=_ft.b,_fv=E(_ft.a);if(_fv>127){var _fw=B(_fo(_fp,_fq,_fr,E(_fu)));return new T2(0,new T(function(){return (E(_fw.a)<<7>>>0|(_fv&127)>>>0)>>>0;}),_fw.b);}else{return new T2(0,_fv,_fu);}},_fx=new T(function(){return B(unCStr("too few bytes"));}),_fy=new T(function(){return B(err(_fx));}),_fz=function(_fA,_fB,_fC,_fD){var _fE=B(_fo(_fA,_fB,_fC,_fD)),_fF=E(_fE.b),_fG=E(_fE.a)&4294967295;return ((_fF+_fG|0)<=_fB)?new T2(0,new T(function(){var _fH=_fB-_fF|0;if(_fG>_fH){return new T3(0,_fA+_fF|0,_fH,_fC);}else{return new T3(0,_fA+_fF|0,_fG,_fC);}}),_fF+_fG|0):E(_fy);},_fI=function(_fJ,_fK){var _fL=E(_fJ),_fM=B(_fz(_fL.a,_fL.b,_fL.c,E(_fK)));return new T2(0,_fM.a,_fM.b);},_fN=new T2(0,_dQ,_fI),_fO=function(_fP){return E(_dP);},_fQ=function(_fR){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_bZ(9,_fR,_4));}))));});},_fS=function(_fT,_fU,_fV,_fW){var _fX=B(_fi(_fT,_fU,_fV,_fW)),_fY=_fX.b,_fZ=E(_fX.a)&4294967295;if(_fZ>=128){if(_fZ>=224){if(_fZ>=240){var _g0=B(_fi(_fT,_fU,_fV,E(_fY))),_g1=B(_fi(_fT,_fU,_fV,E(_g0.b))),_g2=B(_fi(_fT,_fU,_fV,E(_g1.b))),_g3=128^E(_g2.a)&4294967295|(128^E(_g1.a)&4294967295|(128^E(_g0.a)&4294967295|(240^_fZ)<<6)<<6)<<6;if(_g3>>>0>1114111){return new F(function(){return _fQ(_g3);});}else{return new T2(0,_g3,_g2.b);}}else{var _g4=B(_fi(_fT,_fU,_fV,E(_fY))),_g5=B(_fi(_fT,_fU,_fV,E(_g4.b))),_g6=128^E(_g5.a)&4294967295|(128^E(_g4.a)&4294967295|(224^_fZ)<<6)<<6;if(_g6>>>0>1114111){return new F(function(){return _fQ(_g6);});}else{return new T2(0,_g6,_g5.b);}}}else{var _g7=B(_fi(_fT,_fU,_fV,E(_fY))),_g8=128^E(_g7.a)&4294967295|(192^_fZ)<<6;if(_g8>>>0>1114111){return new F(function(){return _fQ(_g8);});}else{return new T2(0,_g8,_g7.b);}}}else{if(_fZ>>>0>1114111){return new F(function(){return _fQ(_fZ);});}else{return new T2(0,_fZ,_fY);}}},_g9=function(_ga,_gb){var _gc=E(_ga),_gd=B(_fS(_gc.a,_gc.b,_gc.c,E(_gb)));return new T2(0,_gd.a,_gd.b);},_ge=function(_gf,_gg,_gh){var _gi=E(_gf);if(!_gi._){return new T2(0,_4,_gh);}else{var _gj=new T(function(){return B(A2(_gi.a,_gg,_gh));}),_gk=B(_ge(_gi.b,_gg,new T(function(){return E(E(_gj).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_gj).a);}),_gk.a),_gk.b);}},_gl=function(_gm,_gn,_go,_gp){if(0>=_gm){return new F(function(){return _ge(_4,_go,_gp);});}else{var _gq=function(_gr){var _gs=E(_gr);return (_gs==1)?E(new T2(1,_gn,_4)):new T2(1,_gn,new T(function(){return B(_gq(_gs-1|0));}));};return new F(function(){return _ge(B(_gq(_gm)),_go,_gp);});}},_gt=function(_gu,_gv,_gw,_gx){var _gy=B(_fo(_gu,_gv,_gw,_gx));return new F(function(){return _gl(E(_gy.a)&4294967295,_g9,new T3(0,_gu,_gv,_gw),_gy.b);});},_gz=function(_gA,_gB){var _gC=E(_gA),_gD=B(_gt(_gC.a,_gC.b,_gC.c,E(_gB)));return new T2(0,_gD.a,_gD.b);},_gE=new T2(0,_fO,_gz),_gF=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_gG=new T(function(){return B(err(_gF));}),_gH=function(_gI,_gJ,_gK){var _gL=function(_){var _gM=E(_gJ),_gN=_gM.c,_gO=newArr(_gN,_gG),_gP=_gO,_gQ=function(_gR,_){while(1){if(_gR!=_gN){var _=_gP[_gR]=_gM.d[_gR],_gS=_gR+1|0;_gR=_gS;continue;}else{return E(_);}}},_=B(_gQ(0,_)),_gT=function(_gU,_){while(1){var _gV=E(_gU);if(!_gV._){return new T4(0,E(_gM.a),E(_gM.b),_gN,_gP);}else{var _gW=E(_gV.a),_=_gP[E(_gW.a)]=_gW.b;_gU=_gV.b;continue;}}};return new F(function(){return _gT(_gK,_);});};return new F(function(){return _8O(_gL);});},_gX=function(_gY,_gZ,_h0){return new F(function(){return _gH(_gY,_gZ,_h0);});},_h1=function(_h2,_h3,_h4){return E(E(_h3).d[E(_h4)]);},_h5=function(_h6,_h7,_h8){return new F(function(){return _h1(_h6,_h7,_h8);});},_h9=function(_ha,_hb,_hc){var _hd=E(_hb),_he=B(A2(_9a,_ha,_hd)),_hf=function(_){var _hg=newArr(_he,_gG),_hh=_hg,_hi=function(_hj,_){while(1){var _hk=B((function(_hl,_){var _hm=E(_hl);if(!_hm._){return new T(function(){return new T4(0,E(_hd.a),E(_hd.b),_he,_hh);});}else{var _hn=E(_hm.a),_=_hh[E(_hn.a)]=_hn.b;_hj=_hm.b;return __continue;}})(_hj,_));if(_hk!=__continue){return _hk;}}};return new F(function(){return _hi(_hc,_);});};return new F(function(){return _8O(_hf);});},_ho=function(_hp,_hq,_hr){return new F(function(){return _h9(_hp,_hq,_hr);});},_hs=function(_ht,_hu){return E(_hu).c;},_hv=function(_hw,_hx){return new F(function(){return _hs(_hw,_hx);});},_hy=function(_hz,_hA){var _hB=E(_hA);return new T2(0,_hB.a,_hB.b);},_hC=function(_hD,_hE){return new F(function(){return _hy(_hD,_hE);});},_hF=function(_hG,_hH,_hI,_hJ){var _hK=function(_){var _hL=E(_hI),_hM=_hL.c,_hN=newArr(_hM,_gG),_hO=_hN,_hP=function(_hQ,_){while(1){if(_hQ!=_hM){var _=_hO[_hQ]=_hL.d[_hQ],_hR=_hQ+1|0;_hQ=_hR;continue;}else{return E(_);}}},_=B(_hP(0,_)),_hS=function(_hT,_){while(1){var _hU=B((function(_hV,_){var _hW=E(_hV);if(!_hW._){return new T4(0,E(_hL.a),E(_hL.b),_hM,_hO);}else{var _hX=E(_hW.a),_hY=E(_hX.a),_hZ=_hO[_hY],_=_hO[_hY]=new T(function(){return B(A2(_hH,_hZ,_hX.b));});_hT=_hW.b;return __continue;}})(_hT,_));if(_hU!=__continue){return _hU;}}};return new F(function(){return _hS(_hJ,_);});};return new F(function(){return _8O(_hK);});},_i0=function(_i1,_i2,_i3,_i4,_i5){var _i6=E(_i4),_i7=B(A2(_9a,_i1,_i6)),_i8=function(_){var _i9=newArr(_i7,_i3),_ia=_i9,_ib=function(_ic,_){while(1){var _id=B((function(_ie,_){var _if=E(_ie);if(!_if._){return new T(function(){return new T4(0,E(_i6.a),E(_i6.b),_i7,_ia);});}else{var _ig=E(_if.a),_ih=E(_ig.a),_ii=_ia[_ih],_=_ia[_ih]=new T(function(){return B(A2(_i2,_ii,_ig.b));});_ic=_if.b;return __continue;}})(_ic,_));if(_id!=__continue){return _id;}}};return new F(function(){return _ib(_i5,_);});};return new F(function(){return _8O(_i8);});},_ij={_:0,a:_hC,b:_hv,c:_ho,d:_h5,e:_gX,f:_hF,g:_i0},_ik=new T(function(){return B(unCStr("Negative range size"));}),_il=new T(function(){return B(err(_ik));}),_im=0,_in=function(_io){var _ip=E(_io);return (E(_ip.b)-E(_ip.a)|0)+1|0;},_iq=function(_ir,_is){var _it=E(_ir),_iu=E(_is);return (E(_it.a)>_iu)?false:_iu<=E(_it.b);},_iv=new T(function(){return B(unCStr("Int"));}),_iw=function(_ix,_iy){return new F(function(){return _eX(_ea,_iy,_ix,_iv);});},_iz=function(_iA,_iB){var _iC=E(_iA),_iD=E(_iC.a),_iE=E(_iB);if(_iD>_iE){return new F(function(){return _iw(_iE,_iC);});}else{if(_iE>E(_iC.b)){return new F(function(){return _iw(_iE,_iC);});}else{return _iE-_iD|0;}}},_iF=function(_iG,_iH){if(_iG<=_iH){var _iI=function(_iJ){return new T2(1,_iJ,new T(function(){if(_iJ!=_iH){return B(_iI(_iJ+1|0));}else{return __Z;}}));};return new F(function(){return _iI(_iG);});}else{return __Z;}},_iK=function(_iL,_iM){return new F(function(){return _iF(E(_iL),E(_iM));});},_iN=function(_iO){var _iP=E(_iO);return new F(function(){return _iK(_iP.a,_iP.b);});},_iQ=function(_iR){var _iS=E(_iR),_iT=E(_iS.a),_iU=E(_iS.b);return (_iT>_iU)?E(_eb):(_iU-_iT|0)+1|0;},_iV=function(_iW,_iX){return E(_iW)-E(_iX)|0;},_iY=function(_iZ,_j0){return new F(function(){return _iV(_j0,E(_iZ).a);});},_j1=function(_j2,_j3){return E(_j2)==E(_j3);},_j4=function(_j5,_j6){return E(_j5)!=E(_j6);},_j7=new T2(0,_j1,_j4),_j8=function(_j9,_ja){var _jb=E(_j9),_jc=E(_ja);return (_jb>_jc)?E(_jb):E(_jc);},_jd=function(_je,_jf){var _jg=E(_je),_jh=E(_jf);return (_jg>_jh)?E(_jh):E(_jg);},_ji=function(_jj,_jk){return (_jj>=_jk)?(_jj!=_jk)?2:1:0;},_jl=function(_jm,_jn){return new F(function(){return _ji(E(_jm),E(_jn));});},_jo=function(_jp,_jq){return E(_jp)>=E(_jq);},_jr=function(_js,_jt){return E(_js)>E(_jt);},_ju=function(_jv,_jw){return E(_jv)<=E(_jw);},_jx=function(_jy,_jz){return E(_jy)<E(_jz);},_jA={_:0,a:_j7,b:_jl,c:_jx,d:_ju,e:_jr,f:_jo,g:_j8,h:_jd},_jB={_:0,a:_jA,b:_iN,c:_iz,d:_iY,e:_iq,f:_iQ,g:_in},_jC=function(_jD,_jE,_jF){var _jG=E(_jD);if(!_jG._){return new T2(0,_4,_jF);}else{var _jH=new T(function(){return B(A2(_jG.a,_jE,_jF));}),_jI=B(_jC(_jG.b,_jE,new T(function(){return E(E(_jH).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_jH).a);}),_jI.a),_jI.b);}},_jJ=function(_jK,_jL,_jM,_jN){if(0>=_jK){return new F(function(){return _jC(_4,_jM,_jN);});}else{var _jO=function(_jP){var _jQ=E(_jP);return (_jQ==1)?E(new T2(1,_jL,_4)):new T2(1,_jL,new T(function(){return B(_jO(_jQ-1|0));}));};return new F(function(){return _jC(B(_jO(_jK)),_jM,_jN);});}},_jR=function(_jS){return E(E(_jS).b);},_jT=function(_jU){return E(E(_jU).c);},_jV=function(_jW,_jX){var _jY=E(_jW);if(!_jY._){return __Z;}else{var _jZ=E(_jX);return (_jZ._==0)?__Z:new T2(1,new T2(0,_jY.a,_jZ.a),new T(function(){return B(_jV(_jY.b,_jZ.b));}));}},_k0=function(_k1,_k2,_k3,_k4,_k5,_k6){var _k7=B(_fo(_k3,_k4,_k5,_k6)),_k8=E(_k7.a)&4294967295,_k9=B(_jJ(_k8,new T(function(){return B(_jR(_k1));}),new T3(0,_k3,_k4,_k5),_k7.b)),_ka=_k9.a,_kb=new T(function(){var _kc=_k8-1|0;return B(A(_jT,[_k2,_jB,new T2(0,_im,_kc),new T(function(){if(0>_kc){return B(_jV(B(_iF(0,-1)),_ka));}else{var _kd=_kc+1|0;if(_kd>=0){return B(_jV(B(_iF(0,_kd-1|0)),_ka));}else{return E(_il);}}})]));});return new T2(0,_kb,_k9.b);},_ke=function(_kf,_kg,_kh,_ki){var _kj=B(_fo(_kf,_kg,_kh,_ki)),_kk=B(_fo(_kf,_kg,_kh,E(_kj.b))),_kl=B(_k0(_gE,_ij,_kf,_kg,_kh,E(_kk.b)));return new T2(0,new T(function(){var _km=E(_kl.a);return new T6(0,E(_kj.a)&4294967295,E(_kk.a)&4294967295,E(_km.a),E(_km.b),_km.c,_km.d);}),_kl.b);},_kn=function(_ko,_kp){var _kq=E(_ko),_kr=B(_ke(_kq.a,_kq.b,_kq.c,E(_kp)));return new T2(0,_kr.a,_kr.b);},_ks=function(_kt){return E(_dP);},_ku=new T2(0,_ks,_kn),_kv=function(_kw,_kx){var _ky=E(_kw),_kz=B(_fo(_ky.a,_ky.b,_ky.c,E(_kx)));return new T2(0,new T(function(){return E(_kz.a)&4294967295;}),_kz.b);},_kA=new T(function(){return B(_dN("Data/Binary.hs:56:10-20|put"));}),_kB=function(_kC){return E(_kA);},_kD=new T2(0,_kB,_kv),_kE=function(_kF,_kG){var _kH=E(_kG);return new T2(0,_kH.a,_kH.b);},_kI=function(_kJ,_kK){return E(_kK).c;},_kL=function(_kM,_kN,_kO,_kP){var _kQ=function(_){var _kR=E(_kO),_kS=_kR.d,_kT=_kS["byteLength"],_kU=newByteArr(_kT),_kV=_kU,_kW=memcpy(_kV,_kS,_kT>>>0),_kX=function(_kY,_){while(1){var _kZ=E(_kY);if(!_kZ._){return _5;}else{var _l0=E(_kZ.a),_l1=E(_l0.a),_l2=_kV["v"]["i32"][_l1],_=_kV["v"]["i32"][_l1]=B(A2(_kN,_l2,_l0.b));_kY=_kZ.b;continue;}}},_l3=B(_kX(_kP,_));return new T4(0,E(_kR.a),E(_kR.b),_kR.c,_kV);};return new F(function(){return _8O(_kQ);});},_l4=function(_l5,_l6,_l7,_l8,_l9){var _la=E(_l8),_lb=function(_){var _lc=B(A2(_9a,_l5,_la)),_ld=newByteArr(imul(4,_lc)|0),_le=_ld;if(_lc>=0){var _lf=_lc-1|0,_lg=function(_){var _lh=function(_li,_){while(1){var _lj=E(_li);if(!_lj._){return _5;}else{var _lk=E(_lj.a),_ll=E(_lk.a),_lm=_le["v"]["i32"][_ll],_=_le["v"]["i32"][_ll]=B(A2(_l6,_lm,_lk.b));_li=_lj.b;continue;}}},_ln=B(_lh(_l9,_));return new T4(0,E(_la.a),E(_la.b),_lc,_le);};if(0<=_lf){var _lo=function(_lp,_){while(1){var _=_le["v"]["i32"][_lp]=E(_l7);if(_lp!=_lf){var _lq=_lp+1|0;_lp=_lq;continue;}else{return _5;}}},_lr=B(_lo(0,_));return new F(function(){return _lg(_);});}else{return new F(function(){return _lg(_);});}}else{return E(_9d);}},_ls=E(_lb);return new F(function(){return _8O(_ls);});},_lt=function(_lu,_lv,_lw){var _lx=E(_lv),_ly=function(_){var _lz=B(A2(_9a,_lu,_lx)),_lA=newByteArr(imul(4,_lz)|0),_lB=_lA;if(_lz>=0){var _lC=_lz-1|0,_lD=function(_){var _lE=function(_lF,_){while(1){var _lG=E(_lF);if(!_lG._){return _5;}else{var _lH=E(_lG.a),_=_lB["v"]["i32"][E(_lH.a)]=E(_lH.b);_lF=_lG.b;continue;}}},_lI=B(_lE(_lw,_));return new T4(0,E(_lx.a),E(_lx.b),_lz,_lB);};if(0<=_lC){var _lJ=function(_lK,_){while(1){var _=_lB["v"]["i32"][_lK]=0;if(_lK!=_lC){var _lL=_lK+1|0;_lK=_lL;continue;}else{return _5;}}},_lM=B(_lJ(0,_));return new F(function(){return _lD(_);});}else{return new F(function(){return _lD(_);});}}else{return E(_9d);}},_lN=E(_ly);return new F(function(){return _8O(_lN);});},_lO=function(_lP,_lQ,_lR){return E(_lQ).d["v"]["i32"][E(_lR)];},_lS=function(_lT,_lU,_lV){var _lW=function(_){var _lX=E(_lU),_lY=_lX.d,_lZ=_lY["byteLength"],_m0=newByteArr(_lZ),_m1=_m0,_m2=memcpy(_m1,_lY,_lZ>>>0),_m3=function(_m4,_){while(1){var _m5=E(_m4);if(!_m5._){return _5;}else{var _m6=E(_m5.a),_=_m1["v"]["i32"][E(_m6.a)]=E(_m6.b);_m4=_m5.b;continue;}}},_m7=B(_m3(_lV,_));return new T4(0,E(_lX.a),E(_lX.b),_lX.c,_m1);};return new F(function(){return _8O(_lW);});},_m8={_:0,a:_kE,b:_kI,c:_lt,d:_lO,e:_lS,f:_kL,g:_l4},_m9=function(_ma,_mb,_mc,_md){var _me=B(_fz(_ma,_mb,_mc,_md)),_mf=B(_k0(_kD,_m8,_ma,_mb,_mc,E(_me.b)));return new T2(0,new T(function(){var _mg=E(_mf.a);return new T5(0,_me.a,E(_mg.a),E(_mg.b),_mg.c,_mg.d);}),_mf.b);},_mh=function(_mi,_mj){var _mk=E(_mi),_ml=B(_m9(_mk.a,_mk.b,_mk.c,E(_mj)));return new T2(0,_ml.a,_ml.b);},_mm=function(_mn){return E(_dP);},_mo=new T2(0,_mm,_mh),_mp=function(_mq){return new F(function(){return _iF(E(_mq),2147483647);});},_mr=function(_ms,_mt,_mu){if(_mu<=_mt){var _mv=new T(function(){var _mw=_mt-_ms|0,_mx=function(_my){return (_my>=(_mu-_mw|0))?new T2(1,_my,new T(function(){return B(_mx(_my+_mw|0));})):new T2(1,_my,_4);};return B(_mx(_mt));});return new T2(1,_ms,_mv);}else{return (_mu<=_ms)?new T2(1,_ms,_4):__Z;}},_mz=function(_mA,_mB,_mC){if(_mC>=_mB){var _mD=new T(function(){var _mE=_mB-_mA|0,_mF=function(_mG){return (_mG<=(_mC-_mE|0))?new T2(1,_mG,new T(function(){return B(_mF(_mG+_mE|0));})):new T2(1,_mG,_4);};return B(_mF(_mB));});return new T2(1,_mA,_mD);}else{return (_mC>=_mA)?new T2(1,_mA,_4):__Z;}},_mH=function(_mI,_mJ){if(_mJ<_mI){return new F(function(){return _mr(_mI,_mJ,-2147483648);});}else{return new F(function(){return _mz(_mI,_mJ,2147483647);});}},_mK=function(_mL,_mM){return new F(function(){return _mH(E(_mL),E(_mM));});},_mN=function(_mO,_mP,_mQ){if(_mP<_mO){return new F(function(){return _mr(_mO,_mP,_mQ);});}else{return new F(function(){return _mz(_mO,_mP,_mQ);});}},_mR=function(_mS,_mT,_mU){return new F(function(){return _mN(E(_mS),E(_mT),E(_mU));});},_mV=function(_mW){return E(_mW);},_mX=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_mY=new T(function(){return B(err(_mX));}),_mZ=function(_n0){var _n1=E(_n0);return (_n1==(-2147483648))?E(_mY):_n1-1|0;},_n2=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_n3=new T(function(){return B(err(_n2));}),_n4=function(_n5){var _n6=E(_n5);return (_n6==2147483647)?E(_n3):_n6+1|0;},_n7={_:0,a:_n4,b:_mZ,c:_mV,d:_mV,e:_mp,f:_mK,g:_iK,h:_mR},_n8=function(_n9,_na){if(_n9<=0){if(_n9>=0){return new F(function(){return quot(_n9,_na);});}else{if(_na<=0){return new F(function(){return quot(_n9,_na);});}else{return quot(_n9+1|0,_na)-1|0;}}}else{if(_na>=0){if(_n9>=0){return new F(function(){return quot(_n9,_na);});}else{if(_na<=0){return new F(function(){return quot(_n9,_na);});}else{return quot(_n9+1|0,_na)-1|0;}}}else{return quot(_n9-1|0,_na)-1|0;}}},_nb=new T(function(){return B(unCStr("base"));}),_nc=new T(function(){return B(unCStr("GHC.Exception"));}),_nd=new T(function(){return B(unCStr("ArithException"));}),_ne=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_nb,_nc,_nd),_nf=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_ne,_4,_4),_ng=function(_nh){return E(_nf);},_ni=function(_nj){var _nk=E(_nj);return new F(function(){return _2M(B(_2K(_nk.a)),_ng,_nk.b);});},_nl=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_nm=new T(function(){return B(unCStr("denormal"));}),_nn=new T(function(){return B(unCStr("divide by zero"));}),_no=new T(function(){return B(unCStr("loss of precision"));}),_np=new T(function(){return B(unCStr("arithmetic underflow"));}),_nq=new T(function(){return B(unCStr("arithmetic overflow"));}),_nr=function(_ns,_nt){switch(E(_ns)){case 0:return new F(function(){return _0(_nq,_nt);});break;case 1:return new F(function(){return _0(_np,_nt);});break;case 2:return new F(function(){return _0(_no,_nt);});break;case 3:return new F(function(){return _0(_nn,_nt);});break;case 4:return new F(function(){return _0(_nm,_nt);});break;default:return new F(function(){return _0(_nl,_nt);});}},_nu=function(_nv){return new F(function(){return _nr(_nv,_4);});},_nw=function(_nx,_ny,_nz){return new F(function(){return _nr(_ny,_nz);});},_nA=function(_nB,_nC){return new F(function(){return _3X(_nr,_nB,_nC);});},_nD=new T3(0,_nw,_nu,_nA),_nE=new T(function(){return new T5(0,_ng,_nD,_nF,_ni,_nu);}),_nF=function(_6S){return new T2(0,_nE,_6S);},_nG=3,_nH=new T(function(){return B(_nF(_nG));}),_nI=new T(function(){return die(_nH);}),_nJ=0,_nK=new T(function(){return B(_nF(_nJ));}),_nL=new T(function(){return die(_nK);}),_nM=function(_nN,_nO){var _nP=E(_nO);switch(_nP){case -1:var _nQ=E(_nN);if(_nQ==(-2147483648)){return E(_nL);}else{return new F(function(){return _n8(_nQ,-1);});}break;case 0:return E(_nI);default:return new F(function(){return _n8(_nN,_nP);});}},_nR=function(_nS,_nT){return new F(function(){return _nM(E(_nS),E(_nT));});},_nU=0,_nV=new T2(0,_nL,_nU),_nW=function(_nX,_nY){var _nZ=E(_nX),_o0=E(_nY);switch(_o0){case -1:var _o1=E(_nZ);if(_o1==(-2147483648)){return E(_nV);}else{if(_o1<=0){if(_o1>=0){var _o2=quotRemI(_o1,-1);return new T2(0,_o2.a,_o2.b);}else{var _o3=quotRemI(_o1,-1);return new T2(0,_o3.a,_o3.b);}}else{var _o4=quotRemI(_o1-1|0,-1);return new T2(0,_o4.a-1|0,(_o4.b+(-1)|0)+1|0);}}break;case 0:return E(_nI);default:if(_nZ<=0){if(_nZ>=0){var _o5=quotRemI(_nZ,_o0);return new T2(0,_o5.a,_o5.b);}else{if(_o0<=0){var _o6=quotRemI(_nZ,_o0);return new T2(0,_o6.a,_o6.b);}else{var _o7=quotRemI(_nZ+1|0,_o0);return new T2(0,_o7.a-1|0,(_o7.b+_o0|0)-1|0);}}}else{if(_o0>=0){if(_nZ>=0){var _o8=quotRemI(_nZ,_o0);return new T2(0,_o8.a,_o8.b);}else{if(_o0<=0){var _o9=quotRemI(_nZ,_o0);return new T2(0,_o9.a,_o9.b);}else{var _oa=quotRemI(_nZ+1|0,_o0);return new T2(0,_oa.a-1|0,(_oa.b+_o0|0)-1|0);}}}else{var _ob=quotRemI(_nZ-1|0,_o0);return new T2(0,_ob.a-1|0,(_ob.b+_o0|0)+1|0);}}}},_oc=function(_od,_oe){var _of=_od%_oe;if(_od<=0){if(_od>=0){return E(_of);}else{if(_oe<=0){return E(_of);}else{var _og=E(_of);return (_og==0)?0:_og+_oe|0;}}}else{if(_oe>=0){if(_od>=0){return E(_of);}else{if(_oe<=0){return E(_of);}else{var _oh=E(_of);return (_oh==0)?0:_oh+_oe|0;}}}else{var _oi=E(_of);return (_oi==0)?0:_oi+_oe|0;}}},_oj=function(_ok,_ol){var _om=E(_ol);switch(_om){case -1:return E(_nU);case 0:return E(_nI);default:return new F(function(){return _oc(E(_ok),_om);});}},_on=function(_oo,_op){var _oq=E(_oo),_or=E(_op);switch(_or){case -1:var _os=E(_oq);if(_os==(-2147483648)){return E(_nL);}else{return new F(function(){return quot(_os,-1);});}break;case 0:return E(_nI);default:return new F(function(){return quot(_oq,_or);});}},_ot=function(_ou,_ov){var _ow=E(_ou),_ox=E(_ov);switch(_ox){case -1:var _oy=E(_ow);if(_oy==(-2147483648)){return E(_nV);}else{var _oz=quotRemI(_oy,-1);return new T2(0,_oz.a,_oz.b);}break;case 0:return E(_nI);default:var _oA=quotRemI(_ow,_ox);return new T2(0,_oA.a,_oA.b);}},_oB=function(_oC,_oD){var _oE=E(_oD);switch(_oE){case -1:return E(_nU);case 0:return E(_nI);default:return E(_oC)%_oE;}},_oF=function(_oG){return new T1(0,_oG);},_oH=function(_oI){return new F(function(){return _oF(E(_oI));});},_oJ=new T1(0,1),_oK=function(_oL){return new T2(0,E(B(_oF(E(_oL)))),E(_oJ));},_oM=function(_oN,_oO){return imul(E(_oN),E(_oO))|0;},_oP=function(_oQ,_oR){return E(_oQ)+E(_oR)|0;},_oS=function(_oT){var _oU=E(_oT);return (_oU<0)? -_oU:E(_oU);},_oV=function(_oW){var _oX=E(_oW);if(!_oX._){return E(_oX.a);}else{return new F(function(){return I_toInt(_oX.a);});}},_oY=function(_oZ){return new F(function(){return _oV(_oZ);});},_p0=function(_p1){return  -E(_p1);},_p2=-1,_p3=0,_p4=1,_p5=function(_p6){var _p7=E(_p6);return (_p7>=0)?(E(_p7)==0)?E(_p3):E(_p4):E(_p2);},_p8={_:0,a:_oP,b:_iV,c:_oM,d:_p0,e:_oS,f:_p5,g:_oY},_p9=new T2(0,_j1,_j4),_pa={_:0,a:_p9,b:_jl,c:_jx,d:_ju,e:_jr,f:_jo,g:_j8,h:_jd},_pb=new T3(0,_p8,_pa,_oK),_pc={_:0,a:_pb,b:_n7,c:_on,d:_oB,e:_nR,f:_oj,g:_ot,h:_nW,i:_oH},_pd={_:0,a:_n4,b:_mZ,c:_mV,d:_mV,e:_mp,f:_mK,g:_iK,h:_mR},_pe={_:0,a:_oP,b:_iV,c:_oM,d:_p0,e:_oS,f:_p5,g:_oY},_pf=new T3(0,_pe,_jA,_oK),_pg={_:0,a:_pf,b:_pd,c:_on,d:_oB,e:_nR,f:_oj,g:_ot,h:_nW,i:_oH},_ph=new T1(0,2),_pi=function(_pj){return E(E(_pj).a);},_pk=function(_pl){return E(E(_pl).a);},_pm=function(_pn,_po){while(1){var _pp=E(_pn);if(!_pp._){var _pq=_pp.a,_pr=E(_po);if(!_pr._){var _ps=_pr.a;if(!(imul(_pq,_ps)|0)){return new T1(0,imul(_pq,_ps)|0);}else{_pn=new T1(1,I_fromInt(_pq));_po=new T1(1,I_fromInt(_ps));continue;}}else{_pn=new T1(1,I_fromInt(_pq));_po=_pr;continue;}}else{var _pt=E(_po);if(!_pt._){_pn=_pp;_po=new T1(1,I_fromInt(_pt.a));continue;}else{return new T1(1,I_mul(_pp.a,_pt.a));}}}},_pu=function(_pv,_pw,_px){while(1){if(!(_pw%2)){var _py=B(_pm(_pv,_pv)),_pz=quot(_pw,2);_pv=_py;_pw=_pz;continue;}else{var _pA=E(_pw);if(_pA==1){return new F(function(){return _pm(_pv,_px);});}else{var _py=B(_pm(_pv,_pv)),_pB=B(_pm(_pv,_px));_pv=_py;_pw=quot(_pA-1|0,2);_px=_pB;continue;}}}},_pC=function(_pD,_pE){while(1){if(!(_pE%2)){var _pF=B(_pm(_pD,_pD)),_pG=quot(_pE,2);_pD=_pF;_pE=_pG;continue;}else{var _pH=E(_pE);if(_pH==1){return E(_pD);}else{return new F(function(){return _pu(B(_pm(_pD,_pD)),quot(_pH-1|0,2),_pD);});}}}},_pI=function(_pJ){return E(E(_pJ).c);},_pK=function(_pL){return E(E(_pL).a);},_pM=function(_pN){return E(E(_pN).b);},_pO=function(_pP){return E(E(_pP).b);},_pQ=function(_pR){return E(E(_pR).c);},_pS=function(_pT){return E(E(_pT).a);},_pU=new T1(0,0),_pV=new T1(0,2),_pW=function(_pX){return E(E(_pX).g);},_pY=function(_pZ){return E(E(_pZ).d);},_q0=function(_q1,_q2){var _q3=B(_pi(_q1)),_q4=new T(function(){return B(_pk(_q3));}),_q5=new T(function(){return B(A3(_pY,_q1,_q2,new T(function(){return B(A2(_pW,_q4,_pV));})));});return new F(function(){return A3(_pS,B(_pK(B(_pM(_q3)))),_q5,new T(function(){return B(A2(_pW,_q4,_pU));}));});},_q6=new T(function(){return B(unCStr("Negative exponent"));}),_q7=new T(function(){return B(err(_q6));}),_q8=function(_q9){return E(E(_q9).c);},_qa=function(_qb,_qc,_qd,_qe){var _qf=B(_pi(_qc)),_qg=new T(function(){return B(_pk(_qf));}),_qh=B(_pM(_qf));if(!B(A3(_pQ,_qh,_qe,new T(function(){return B(A2(_pW,_qg,_pU));})))){if(!B(A3(_pS,B(_pK(_qh)),_qe,new T(function(){return B(A2(_pW,_qg,_pU));})))){var _qi=new T(function(){return B(A2(_pW,_qg,_pV));}),_qj=new T(function(){return B(A2(_pW,_qg,_oJ));}),_qk=B(_pK(_qh)),_ql=function(_qm,_qn,_qo){while(1){var _qp=B((function(_qq,_qr,_qs){if(!B(_q0(_qc,_qr))){if(!B(A3(_pS,_qk,_qr,_qj))){var _qt=new T(function(){return B(A3(_q8,_qc,new T(function(){return B(A3(_pO,_qg,_qr,_qj));}),_qi));});_qm=new T(function(){return B(A3(_pI,_qb,_qq,_qq));});_qn=_qt;_qo=new T(function(){return B(A3(_pI,_qb,_qq,_qs));});return __continue;}else{return new F(function(){return A3(_pI,_qb,_qq,_qs);});}}else{var _qu=_qs;_qm=new T(function(){return B(A3(_pI,_qb,_qq,_qq));});_qn=new T(function(){return B(A3(_q8,_qc,_qr,_qi));});_qo=_qu;return __continue;}})(_qm,_qn,_qo));if(_qp!=__continue){return _qp;}}},_qv=function(_qw,_qx){while(1){var _qy=B((function(_qz,_qA){if(!B(_q0(_qc,_qA))){if(!B(A3(_pS,_qk,_qA,_qj))){var _qB=new T(function(){return B(A3(_q8,_qc,new T(function(){return B(A3(_pO,_qg,_qA,_qj));}),_qi));});return new F(function(){return _ql(new T(function(){return B(A3(_pI,_qb,_qz,_qz));}),_qB,_qz);});}else{return E(_qz);}}else{_qw=new T(function(){return B(A3(_pI,_qb,_qz,_qz));});_qx=new T(function(){return B(A3(_q8,_qc,_qA,_qi));});return __continue;}})(_qw,_qx));if(_qy!=__continue){return _qy;}}};return new F(function(){return _qv(_qd,_qe);});}else{return new F(function(){return A2(_pW,_qb,_oJ);});}}else{return E(_q7);}},_qC=new T(function(){return B(err(_q6));}),_qD=function(_qE){var _qF=I_decodeDouble(_qE);return new T2(0,new T1(1,_qF.b),_qF.a);},_qG=function(_qH,_qI){var _qJ=E(_qH);return (_qJ._==0)?_qJ.a*Math.pow(2,_qI):I_toNumber(_qJ.a)*Math.pow(2,_qI);},_qK=function(_qL,_qM){var _qN=E(_qL);if(!_qN._){var _qO=_qN.a,_qP=E(_qM);return (_qP._==0)?_qO==_qP.a:(I_compareInt(_qP.a,_qO)==0)?true:false;}else{var _qQ=_qN.a,_qR=E(_qM);return (_qR._==0)?(I_compareInt(_qQ,_qR.a)==0)?true:false:(I_compare(_qQ,_qR.a)==0)?true:false;}},_qS=function(_qT,_qU){while(1){var _qV=E(_qT);if(!_qV._){var _qW=E(_qV.a);if(_qW==(-2147483648)){_qT=new T1(1,I_fromInt(-2147483648));continue;}else{var _qX=E(_qU);if(!_qX._){var _qY=_qX.a;return new T2(0,new T1(0,quot(_qW,_qY)),new T1(0,_qW%_qY));}else{_qT=new T1(1,I_fromInt(_qW));_qU=_qX;continue;}}}else{var _qZ=E(_qU);if(!_qZ._){_qT=_qV;_qU=new T1(1,I_fromInt(_qZ.a));continue;}else{var _r0=I_quotRem(_qV.a,_qZ.a);return new T2(0,new T1(1,_r0.a),new T1(1,_r0.b));}}}},_r1=0,_r2=new T1(0,0),_r3=function(_r4,_r5){var _r6=B(_qD(_r5)),_r7=_r6.a,_r8=_r6.b,_r9=new T(function(){return B(_pk(new T(function(){return B(_pi(_r4));})));});if(_r8<0){var _ra= -_r8;if(_ra>=0){var _rb=E(_ra);if(!_rb){var _rc=E(_oJ);}else{var _rc=B(_pC(_ph,_rb));}if(!B(_qK(_rc,_r2))){var _rd=B(_qS(_r7,_rc));return new T2(0,new T(function(){return B(A2(_pW,_r9,_rd.a));}),new T(function(){return B(_qG(_rd.b,_r8));}));}else{return E(_nI);}}else{return E(_qC);}}else{var _re=new T(function(){var _rf=new T(function(){return B(_qa(_r9,_pg,new T(function(){return B(A2(_pW,_r9,_ph));}),_r8));});return B(A3(_pI,_r9,new T(function(){return B(A2(_pW,_r9,_r7));}),_rf));});return new T2(0,_re,_r1);}},_rg=function(_rh){var _ri=E(_rh);if(!_ri._){return _ri.a;}else{return new F(function(){return I_toNumber(_ri.a);});}},_rj=function(_rk,_rl){var _rm=B(_r3(_pc,Math.pow(B(_rg(_rk)),_rl))),_rn=_rm.a;return (E(_rm.b)>=0)?E(_rn):E(_rn)-1|0;},_ro=new T1(0,1),_rp=new T1(0,0),_rq=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_rr=new T(function(){return B(err(_rq));}),_rs=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_rt=new T(function(){return B(err(_rs));}),_ru=new T1(0,2),_rv=new T(function(){return B(unCStr("NaN"));}),_rw=new T(function(){return B(_7f("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_rx=function(_ry,_rz){while(1){var _rA=B((function(_rB,_rC){var _rD=E(_rB);switch(_rD._){case 0:var _rE=E(_rC);if(!_rE._){return __Z;}else{_ry=B(A1(_rD.a,_rE.a));_rz=_rE.b;return __continue;}break;case 1:var _rF=B(A1(_rD.a,_rC)),_rG=_rC;_ry=_rF;_rz=_rG;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_rD.a,_rC),new T(function(){return B(_rx(_rD.b,_rC));}));default:return E(_rD.a);}})(_ry,_rz));if(_rA!=__continue){return _rA;}}},_rH=function(_rI,_rJ){var _rK=function(_rL){var _rM=E(_rJ);if(_rM._==3){return new T2(3,_rM.a,new T(function(){return B(_rH(_rI,_rM.b));}));}else{var _rN=E(_rI);if(_rN._==2){return E(_rM);}else{var _rO=E(_rM);if(_rO._==2){return E(_rN);}else{var _rP=function(_rQ){var _rR=E(_rO);if(_rR._==4){var _rS=function(_rT){return new T1(4,new T(function(){return B(_0(B(_rx(_rN,_rT)),_rR.a));}));};return new T1(1,_rS);}else{var _rU=E(_rN);if(_rU._==1){var _rV=_rU.a,_rW=E(_rR);if(!_rW._){return new T1(1,function(_rX){return new F(function(){return _rH(B(A1(_rV,_rX)),_rW);});});}else{var _rY=function(_rZ){return new F(function(){return _rH(B(A1(_rV,_rZ)),new T(function(){return B(A1(_rW.a,_rZ));}));});};return new T1(1,_rY);}}else{var _s0=E(_rR);if(!_s0._){return E(_rw);}else{var _s1=function(_s2){return new F(function(){return _rH(_rU,new T(function(){return B(A1(_s0.a,_s2));}));});};return new T1(1,_s1);}}}},_s3=E(_rN);switch(_s3._){case 1:var _s4=E(_rO);if(_s4._==4){var _s5=function(_s6){return new T1(4,new T(function(){return B(_0(B(_rx(B(A1(_s3.a,_s6)),_s6)),_s4.a));}));};return new T1(1,_s5);}else{return new F(function(){return _rP(_);});}break;case 4:var _s7=_s3.a,_s8=E(_rO);switch(_s8._){case 0:var _s9=function(_sa){var _sb=new T(function(){return B(_0(_s7,new T(function(){return B(_rx(_s8,_sa));},1)));});return new T1(4,_sb);};return new T1(1,_s9);case 1:var _sc=function(_sd){var _se=new T(function(){return B(_0(_s7,new T(function(){return B(_rx(B(A1(_s8.a,_sd)),_sd));},1)));});return new T1(4,_se);};return new T1(1,_sc);default:return new T1(4,new T(function(){return B(_0(_s7,_s8.a));}));}break;default:return new F(function(){return _rP(_);});}}}}},_sf=E(_rI);switch(_sf._){case 0:var _sg=E(_rJ);if(!_sg._){var _sh=function(_si){return new F(function(){return _rH(B(A1(_sf.a,_si)),new T(function(){return B(A1(_sg.a,_si));}));});};return new T1(0,_sh);}else{return new F(function(){return _rK(_);});}break;case 3:return new T2(3,_sf.a,new T(function(){return B(_rH(_sf.b,_rJ));}));default:return new F(function(){return _rK(_);});}},_sj=new T(function(){return B(unCStr("("));}),_sk=new T(function(){return B(unCStr(")"));}),_sl=function(_sm,_sn){while(1){var _so=E(_sm);if(!_so._){return (E(_sn)._==0)?true:false;}else{var _sp=E(_sn);if(!_sp._){return false;}else{if(E(_so.a)!=E(_sp.a)){return false;}else{_sm=_so.b;_sn=_sp.b;continue;}}}}},_sq=function(_sr,_ss){return E(_sr)!=E(_ss);},_st=function(_su,_sv){return E(_su)==E(_sv);},_sw=new T2(0,_st,_sq),_sx=function(_sy,_sz){while(1){var _sA=E(_sy);if(!_sA._){return (E(_sz)._==0)?true:false;}else{var _sB=E(_sz);if(!_sB._){return false;}else{if(E(_sA.a)!=E(_sB.a)){return false;}else{_sy=_sA.b;_sz=_sB.b;continue;}}}}},_sC=function(_sD,_sE){return (!B(_sx(_sD,_sE)))?true:false;},_sF=new T2(0,_sx,_sC),_sG=function(_sH,_sI){var _sJ=E(_sH);switch(_sJ._){case 0:return new T1(0,function(_sK){return new F(function(){return _sG(B(A1(_sJ.a,_sK)),_sI);});});case 1:return new T1(1,function(_sL){return new F(function(){return _sG(B(A1(_sJ.a,_sL)),_sI);});});case 2:return new T0(2);case 3:return new F(function(){return _rH(B(A1(_sI,_sJ.a)),new T(function(){return B(_sG(_sJ.b,_sI));}));});break;default:var _sM=function(_sN){var _sO=E(_sN);if(!_sO._){return __Z;}else{var _sP=E(_sO.a);return new F(function(){return _0(B(_rx(B(A1(_sI,_sP.a)),_sP.b)),new T(function(){return B(_sM(_sO.b));},1));});}},_sQ=B(_sM(_sJ.a));return (_sQ._==0)?new T0(2):new T1(4,_sQ);}},_sR=new T0(2),_sS=function(_sT){return new T2(3,_sT,_sR);},_sU=function(_sV,_sW){var _sX=E(_sV);if(!_sX){return new F(function(){return A1(_sW,_5);});}else{var _sY=new T(function(){return B(_sU(_sX-1|0,_sW));});return new T1(0,function(_sZ){return E(_sY);});}},_t0=function(_t1,_t2,_t3){var _t4=new T(function(){return B(A1(_t1,_sS));}),_t5=function(_t6,_t7,_t8,_t9){while(1){var _ta=B((function(_tb,_tc,_td,_te){var _tf=E(_tb);switch(_tf._){case 0:var _tg=E(_tc);if(!_tg._){return new F(function(){return A1(_t2,_te);});}else{var _th=_td+1|0,_ti=_te;_t6=B(A1(_tf.a,_tg.a));_t7=_tg.b;_t8=_th;_t9=_ti;return __continue;}break;case 1:var _tj=B(A1(_tf.a,_tc)),_tk=_tc,_th=_td,_ti=_te;_t6=_tj;_t7=_tk;_t8=_th;_t9=_ti;return __continue;case 2:return new F(function(){return A1(_t2,_te);});break;case 3:var _tl=new T(function(){return B(_sG(_tf,_te));});return new F(function(){return _sU(_td,function(_tm){return E(_tl);});});break;default:return new F(function(){return _sG(_tf,_te);});}})(_t6,_t7,_t8,_t9));if(_ta!=__continue){return _ta;}}};return function(_tn){return new F(function(){return _t5(_t4,_tn,0,_t3);});};},_to=function(_tp){return new F(function(){return A1(_tp,_4);});},_tq=function(_tr,_ts){var _tt=function(_tu){var _tv=E(_tu);if(!_tv._){return E(_to);}else{var _tw=_tv.a;if(!B(A1(_tr,_tw))){return E(_to);}else{var _tx=new T(function(){return B(_tt(_tv.b));}),_ty=function(_tz){var _tA=new T(function(){return B(A1(_tx,function(_tB){return new F(function(){return A1(_tz,new T2(1,_tw,_tB));});}));});return new T1(0,function(_tC){return E(_tA);});};return E(_ty);}}};return function(_tD){return new F(function(){return A2(_tt,_tD,_ts);});};},_tE=new T0(6),_tF=new T(function(){return B(unCStr("valDig: Bad base"));}),_tG=new T(function(){return B(err(_tF));}),_tH=function(_tI,_tJ){var _tK=function(_tL,_tM){var _tN=E(_tL);if(!_tN._){var _tO=new T(function(){return B(A1(_tM,_4));});return function(_tP){return new F(function(){return A1(_tP,_tO);});};}else{var _tQ=E(_tN.a),_tR=function(_tS){var _tT=new T(function(){return B(_tK(_tN.b,function(_tU){return new F(function(){return A1(_tM,new T2(1,_tS,_tU));});}));}),_tV=function(_tW){var _tX=new T(function(){return B(A1(_tT,_tW));});return new T1(0,function(_tY){return E(_tX);});};return E(_tV);};switch(E(_tI)){case 8:if(48>_tQ){var _tZ=new T(function(){return B(A1(_tM,_4));});return function(_u0){return new F(function(){return A1(_u0,_tZ);});};}else{if(_tQ>55){var _u1=new T(function(){return B(A1(_tM,_4));});return function(_u2){return new F(function(){return A1(_u2,_u1);});};}else{return new F(function(){return _tR(_tQ-48|0);});}}break;case 10:if(48>_tQ){var _u3=new T(function(){return B(A1(_tM,_4));});return function(_u4){return new F(function(){return A1(_u4,_u3);});};}else{if(_tQ>57){var _u5=new T(function(){return B(A1(_tM,_4));});return function(_u6){return new F(function(){return A1(_u6,_u5);});};}else{return new F(function(){return _tR(_tQ-48|0);});}}break;case 16:if(48>_tQ){if(97>_tQ){if(65>_tQ){var _u7=new T(function(){return B(A1(_tM,_4));});return function(_u8){return new F(function(){return A1(_u8,_u7);});};}else{if(_tQ>70){var _u9=new T(function(){return B(A1(_tM,_4));});return function(_ua){return new F(function(){return A1(_ua,_u9);});};}else{return new F(function(){return _tR((_tQ-65|0)+10|0);});}}}else{if(_tQ>102){if(65>_tQ){var _ub=new T(function(){return B(A1(_tM,_4));});return function(_uc){return new F(function(){return A1(_uc,_ub);});};}else{if(_tQ>70){var _ud=new T(function(){return B(A1(_tM,_4));});return function(_ue){return new F(function(){return A1(_ue,_ud);});};}else{return new F(function(){return _tR((_tQ-65|0)+10|0);});}}}else{return new F(function(){return _tR((_tQ-97|0)+10|0);});}}}else{if(_tQ>57){if(97>_tQ){if(65>_tQ){var _uf=new T(function(){return B(A1(_tM,_4));});return function(_ug){return new F(function(){return A1(_ug,_uf);});};}else{if(_tQ>70){var _uh=new T(function(){return B(A1(_tM,_4));});return function(_ui){return new F(function(){return A1(_ui,_uh);});};}else{return new F(function(){return _tR((_tQ-65|0)+10|0);});}}}else{if(_tQ>102){if(65>_tQ){var _uj=new T(function(){return B(A1(_tM,_4));});return function(_uk){return new F(function(){return A1(_uk,_uj);});};}else{if(_tQ>70){var _ul=new T(function(){return B(A1(_tM,_4));});return function(_um){return new F(function(){return A1(_um,_ul);});};}else{return new F(function(){return _tR((_tQ-65|0)+10|0);});}}}else{return new F(function(){return _tR((_tQ-97|0)+10|0);});}}}else{return new F(function(){return _tR(_tQ-48|0);});}}break;default:return E(_tG);}}},_un=function(_uo){var _up=E(_uo);if(!_up._){return new T0(2);}else{return new F(function(){return A1(_tJ,_up);});}};return function(_uq){return new F(function(){return A3(_tK,_uq,_2j,_un);});};},_ur=16,_us=8,_ut=function(_uu){var _uv=function(_uw){return new F(function(){return A1(_uu,new T1(5,new T2(0,_us,_uw)));});},_ux=function(_uy){return new F(function(){return A1(_uu,new T1(5,new T2(0,_ur,_uy)));});},_uz=function(_uA){switch(E(_uA)){case 79:return new T1(1,B(_tH(_us,_uv)));case 88:return new T1(1,B(_tH(_ur,_ux)));case 111:return new T1(1,B(_tH(_us,_uv)));case 120:return new T1(1,B(_tH(_ur,_ux)));default:return new T0(2);}};return function(_uB){return (E(_uB)==48)?E(new T1(0,_uz)):new T0(2);};},_uC=function(_uD){return new T1(0,B(_ut(_uD)));},_uE=function(_uF){return new F(function(){return A1(_uF,_4l);});},_uG=function(_uH){return new F(function(){return A1(_uH,_4l);});},_uI=10,_uJ=new T1(0,1),_uK=new T1(0,2147483647),_uL=function(_uM,_uN){while(1){var _uO=E(_uM);if(!_uO._){var _uP=_uO.a,_uQ=E(_uN);if(!_uQ._){var _uR=_uQ.a,_uS=addC(_uP,_uR);if(!E(_uS.b)){return new T1(0,_uS.a);}else{_uM=new T1(1,I_fromInt(_uP));_uN=new T1(1,I_fromInt(_uR));continue;}}else{_uM=new T1(1,I_fromInt(_uP));_uN=_uQ;continue;}}else{var _uT=E(_uN);if(!_uT._){_uM=_uO;_uN=new T1(1,I_fromInt(_uT.a));continue;}else{return new T1(1,I_add(_uO.a,_uT.a));}}}},_uU=new T(function(){return B(_uL(_uK,_uJ));}),_uV=function(_uW){var _uX=E(_uW);if(!_uX._){var _uY=E(_uX.a);return (_uY==(-2147483648))?E(_uU):new T1(0, -_uY);}else{return new T1(1,I_negate(_uX.a));}},_uZ=new T1(0,10),_v0=function(_v1,_v2){while(1){var _v3=E(_v1);if(!_v3._){return E(_v2);}else{var _v4=_v2+1|0;_v1=_v3.b;_v2=_v4;continue;}}},_v5=function(_v6){return new F(function(){return _oF(E(_v6));});},_v7=new T(function(){return B(unCStr("this should not happen"));}),_v8=new T(function(){return B(err(_v7));}),_v9=function(_va,_vb){var _vc=E(_vb);if(!_vc._){return __Z;}else{var _vd=E(_vc.b);return (_vd._==0)?E(_v8):new T2(1,B(_uL(B(_pm(_vc.a,_va)),_vd.a)),new T(function(){return B(_v9(_va,_vd.b));}));}},_ve=new T1(0,0),_vf=function(_vg,_vh,_vi){while(1){var _vj=B((function(_vk,_vl,_vm){var _vn=E(_vm);if(!_vn._){return E(_ve);}else{if(!E(_vn.b)._){return E(_vn.a);}else{var _vo=E(_vl);if(_vo<=40){var _vp=function(_vq,_vr){while(1){var _vs=E(_vr);if(!_vs._){return E(_vq);}else{var _vt=B(_uL(B(_pm(_vq,_vk)),_vs.a));_vq=_vt;_vr=_vs.b;continue;}}};return new F(function(){return _vp(_ve,_vn);});}else{var _vu=B(_pm(_vk,_vk));if(!(_vo%2)){var _vv=B(_v9(_vk,_vn));_vg=_vu;_vh=quot(_vo+1|0,2);_vi=_vv;return __continue;}else{var _vv=B(_v9(_vk,new T2(1,_ve,_vn)));_vg=_vu;_vh=quot(_vo+1|0,2);_vi=_vv;return __continue;}}}}})(_vg,_vh,_vi));if(_vj!=__continue){return _vj;}}},_vw=function(_vx,_vy){return new F(function(){return _vf(_vx,new T(function(){return B(_v0(_vy,0));},1),B(_G(_v5,_vy)));});},_vz=function(_vA){var _vB=new T(function(){var _vC=new T(function(){var _vD=function(_vE){return new F(function(){return A1(_vA,new T1(1,new T(function(){return B(_vw(_uZ,_vE));})));});};return new T1(1,B(_tH(_uI,_vD)));}),_vF=function(_vG){if(E(_vG)==43){var _vH=function(_vI){return new F(function(){return A1(_vA,new T1(1,new T(function(){return B(_vw(_uZ,_vI));})));});};return new T1(1,B(_tH(_uI,_vH)));}else{return new T0(2);}},_vJ=function(_vK){if(E(_vK)==45){var _vL=function(_vM){return new F(function(){return A1(_vA,new T1(1,new T(function(){return B(_uV(B(_vw(_uZ,_vM))));})));});};return new T1(1,B(_tH(_uI,_vL)));}else{return new T0(2);}};return B(_rH(B(_rH(new T1(0,_vJ),new T1(0,_vF))),_vC));});return new F(function(){return _rH(new T1(0,function(_vN){return (E(_vN)==101)?E(_vB):new T0(2);}),new T1(0,function(_vO){return (E(_vO)==69)?E(_vB):new T0(2);}));});},_vP=function(_vQ){var _vR=function(_vS){return new F(function(){return A1(_vQ,new T1(1,_vS));});};return function(_vT){return (E(_vT)==46)?new T1(1,B(_tH(_uI,_vR))):new T0(2);};},_vU=function(_vV){return new T1(0,B(_vP(_vV)));},_vW=function(_vX){var _vY=function(_vZ){var _w0=function(_w1){return new T1(1,B(_t0(_vz,_uE,function(_w2){return new F(function(){return A1(_vX,new T1(5,new T3(1,_vZ,_w1,_w2)));});})));};return new T1(1,B(_t0(_vU,_uG,_w0)));};return new F(function(){return _tH(_uI,_vY);});},_w3=function(_w4){return new T1(1,B(_vW(_w4)));},_w5=function(_w6,_w7,_w8){while(1){var _w9=E(_w8);if(!_w9._){return false;}else{if(!B(A3(_pS,_w6,_w7,_w9.a))){_w8=_w9.b;continue;}else{return true;}}}},_wa=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_wb=function(_wc){return new F(function(){return _w5(_sw,_wc,_wa);});},_wd=false,_we=true,_wf=function(_wg){var _wh=new T(function(){return B(A1(_wg,_us));}),_wi=new T(function(){return B(A1(_wg,_ur));});return function(_wj){switch(E(_wj)){case 79:return E(_wh);case 88:return E(_wi);case 111:return E(_wh);case 120:return E(_wi);default:return new T0(2);}};},_wk=function(_wl){return new T1(0,B(_wf(_wl)));},_wm=function(_wn){return new F(function(){return A1(_wn,_uI);});},_wo=function(_wp,_wq){var _wr=E(_wp);if(!_wr._){var _ws=_wr.a,_wt=E(_wq);return (_wt._==0)?_ws<=_wt.a:I_compareInt(_wt.a,_ws)>=0;}else{var _wu=_wr.a,_wv=E(_wq);return (_wv._==0)?I_compareInt(_wu,_wv.a)<=0:I_compare(_wu,_wv.a)<=0;}},_ww=function(_wx){return new T0(2);},_wy=function(_wz){var _wA=E(_wz);if(!_wA._){return E(_ww);}else{var _wB=_wA.a,_wC=E(_wA.b);if(!_wC._){return E(_wB);}else{var _wD=new T(function(){return B(_wy(_wC));}),_wE=function(_wF){return new F(function(){return _rH(B(A1(_wB,_wF)),new T(function(){return B(A1(_wD,_wF));}));});};return E(_wE);}}},_wG=function(_wH,_wI){var _wJ=function(_wK,_wL,_wM){var _wN=E(_wK);if(!_wN._){return new F(function(){return A1(_wM,_wH);});}else{var _wO=E(_wL);if(!_wO._){return new T0(2);}else{if(E(_wN.a)!=E(_wO.a)){return new T0(2);}else{var _wP=new T(function(){return B(_wJ(_wN.b,_wO.b,_wM));});return new T1(0,function(_wQ){return E(_wP);});}}}};return function(_wR){return new F(function(){return _wJ(_wH,_wR,_wI);});};},_wS=new T(function(){return B(unCStr("SO"));}),_wT=14,_wU=function(_wV){var _wW=new T(function(){return B(A1(_wV,_wT));});return new T1(1,B(_wG(_wS,function(_wX){return E(_wW);})));},_wY=new T(function(){return B(unCStr("SOH"));}),_wZ=1,_x0=function(_x1){var _x2=new T(function(){return B(A1(_x1,_wZ));});return new T1(1,B(_wG(_wY,function(_x3){return E(_x2);})));},_x4=function(_x5){return new T1(1,B(_t0(_x0,_wU,_x5)));},_x6=new T(function(){return B(unCStr("NUL"));}),_x7=0,_x8=function(_x9){var _xa=new T(function(){return B(A1(_x9,_x7));});return new T1(1,B(_wG(_x6,function(_xb){return E(_xa);})));},_xc=new T(function(){return B(unCStr("STX"));}),_xd=2,_xe=function(_xf){var _xg=new T(function(){return B(A1(_xf,_xd));});return new T1(1,B(_wG(_xc,function(_xh){return E(_xg);})));},_xi=new T(function(){return B(unCStr("ETX"));}),_xj=3,_xk=function(_xl){var _xm=new T(function(){return B(A1(_xl,_xj));});return new T1(1,B(_wG(_xi,function(_xn){return E(_xm);})));},_xo=new T(function(){return B(unCStr("EOT"));}),_xp=4,_xq=function(_xr){var _xs=new T(function(){return B(A1(_xr,_xp));});return new T1(1,B(_wG(_xo,function(_xt){return E(_xs);})));},_xu=new T(function(){return B(unCStr("ENQ"));}),_xv=5,_xw=function(_xx){var _xy=new T(function(){return B(A1(_xx,_xv));});return new T1(1,B(_wG(_xu,function(_xz){return E(_xy);})));},_xA=new T(function(){return B(unCStr("ACK"));}),_xB=6,_xC=function(_xD){var _xE=new T(function(){return B(A1(_xD,_xB));});return new T1(1,B(_wG(_xA,function(_xF){return E(_xE);})));},_xG=new T(function(){return B(unCStr("BEL"));}),_xH=7,_xI=function(_xJ){var _xK=new T(function(){return B(A1(_xJ,_xH));});return new T1(1,B(_wG(_xG,function(_xL){return E(_xK);})));},_xM=new T(function(){return B(unCStr("BS"));}),_xN=8,_xO=function(_xP){var _xQ=new T(function(){return B(A1(_xP,_xN));});return new T1(1,B(_wG(_xM,function(_xR){return E(_xQ);})));},_xS=new T(function(){return B(unCStr("HT"));}),_xT=9,_xU=function(_xV){var _xW=new T(function(){return B(A1(_xV,_xT));});return new T1(1,B(_wG(_xS,function(_xX){return E(_xW);})));},_xY=new T(function(){return B(unCStr("LF"));}),_xZ=10,_y0=function(_y1){var _y2=new T(function(){return B(A1(_y1,_xZ));});return new T1(1,B(_wG(_xY,function(_y3){return E(_y2);})));},_y4=new T(function(){return B(unCStr("VT"));}),_y5=11,_y6=function(_y7){var _y8=new T(function(){return B(A1(_y7,_y5));});return new T1(1,B(_wG(_y4,function(_y9){return E(_y8);})));},_ya=new T(function(){return B(unCStr("FF"));}),_yb=12,_yc=function(_yd){var _ye=new T(function(){return B(A1(_yd,_yb));});return new T1(1,B(_wG(_ya,function(_yf){return E(_ye);})));},_yg=new T(function(){return B(unCStr("CR"));}),_yh=13,_yi=function(_yj){var _yk=new T(function(){return B(A1(_yj,_yh));});return new T1(1,B(_wG(_yg,function(_yl){return E(_yk);})));},_ym=new T(function(){return B(unCStr("SI"));}),_yn=15,_yo=function(_yp){var _yq=new T(function(){return B(A1(_yp,_yn));});return new T1(1,B(_wG(_ym,function(_yr){return E(_yq);})));},_ys=new T(function(){return B(unCStr("DLE"));}),_yt=16,_yu=function(_yv){var _yw=new T(function(){return B(A1(_yv,_yt));});return new T1(1,B(_wG(_ys,function(_yx){return E(_yw);})));},_yy=new T(function(){return B(unCStr("DC1"));}),_yz=17,_yA=function(_yB){var _yC=new T(function(){return B(A1(_yB,_yz));});return new T1(1,B(_wG(_yy,function(_yD){return E(_yC);})));},_yE=new T(function(){return B(unCStr("DC2"));}),_yF=18,_yG=function(_yH){var _yI=new T(function(){return B(A1(_yH,_yF));});return new T1(1,B(_wG(_yE,function(_yJ){return E(_yI);})));},_yK=new T(function(){return B(unCStr("DC3"));}),_yL=19,_yM=function(_yN){var _yO=new T(function(){return B(A1(_yN,_yL));});return new T1(1,B(_wG(_yK,function(_yP){return E(_yO);})));},_yQ=new T(function(){return B(unCStr("DC4"));}),_yR=20,_yS=function(_yT){var _yU=new T(function(){return B(A1(_yT,_yR));});return new T1(1,B(_wG(_yQ,function(_yV){return E(_yU);})));},_yW=new T(function(){return B(unCStr("NAK"));}),_yX=21,_yY=function(_yZ){var _z0=new T(function(){return B(A1(_yZ,_yX));});return new T1(1,B(_wG(_yW,function(_z1){return E(_z0);})));},_z2=new T(function(){return B(unCStr("SYN"));}),_z3=22,_z4=function(_z5){var _z6=new T(function(){return B(A1(_z5,_z3));});return new T1(1,B(_wG(_z2,function(_z7){return E(_z6);})));},_z8=new T(function(){return B(unCStr("ETB"));}),_z9=23,_za=function(_zb){var _zc=new T(function(){return B(A1(_zb,_z9));});return new T1(1,B(_wG(_z8,function(_zd){return E(_zc);})));},_ze=new T(function(){return B(unCStr("CAN"));}),_zf=24,_zg=function(_zh){var _zi=new T(function(){return B(A1(_zh,_zf));});return new T1(1,B(_wG(_ze,function(_zj){return E(_zi);})));},_zk=new T(function(){return B(unCStr("EM"));}),_zl=25,_zm=function(_zn){var _zo=new T(function(){return B(A1(_zn,_zl));});return new T1(1,B(_wG(_zk,function(_zp){return E(_zo);})));},_zq=new T(function(){return B(unCStr("SUB"));}),_zr=26,_zs=function(_zt){var _zu=new T(function(){return B(A1(_zt,_zr));});return new T1(1,B(_wG(_zq,function(_zv){return E(_zu);})));},_zw=new T(function(){return B(unCStr("ESC"));}),_zx=27,_zy=function(_zz){var _zA=new T(function(){return B(A1(_zz,_zx));});return new T1(1,B(_wG(_zw,function(_zB){return E(_zA);})));},_zC=new T(function(){return B(unCStr("FS"));}),_zD=28,_zE=function(_zF){var _zG=new T(function(){return B(A1(_zF,_zD));});return new T1(1,B(_wG(_zC,function(_zH){return E(_zG);})));},_zI=new T(function(){return B(unCStr("GS"));}),_zJ=29,_zK=function(_zL){var _zM=new T(function(){return B(A1(_zL,_zJ));});return new T1(1,B(_wG(_zI,function(_zN){return E(_zM);})));},_zO=new T(function(){return B(unCStr("RS"));}),_zP=30,_zQ=function(_zR){var _zS=new T(function(){return B(A1(_zR,_zP));});return new T1(1,B(_wG(_zO,function(_zT){return E(_zS);})));},_zU=new T(function(){return B(unCStr("US"));}),_zV=31,_zW=function(_zX){var _zY=new T(function(){return B(A1(_zX,_zV));});return new T1(1,B(_wG(_zU,function(_zZ){return E(_zY);})));},_A0=new T(function(){return B(unCStr("SP"));}),_A1=32,_A2=function(_A3){var _A4=new T(function(){return B(A1(_A3,_A1));});return new T1(1,B(_wG(_A0,function(_A5){return E(_A4);})));},_A6=new T(function(){return B(unCStr("DEL"));}),_A7=127,_A8=function(_A9){var _Aa=new T(function(){return B(A1(_A9,_A7));});return new T1(1,B(_wG(_A6,function(_Ab){return E(_Aa);})));},_Ac=new T2(1,_A8,_4),_Ad=new T2(1,_A2,_Ac),_Ae=new T2(1,_zW,_Ad),_Af=new T2(1,_zQ,_Ae),_Ag=new T2(1,_zK,_Af),_Ah=new T2(1,_zE,_Ag),_Ai=new T2(1,_zy,_Ah),_Aj=new T2(1,_zs,_Ai),_Ak=new T2(1,_zm,_Aj),_Al=new T2(1,_zg,_Ak),_Am=new T2(1,_za,_Al),_An=new T2(1,_z4,_Am),_Ao=new T2(1,_yY,_An),_Ap=new T2(1,_yS,_Ao),_Aq=new T2(1,_yM,_Ap),_Ar=new T2(1,_yG,_Aq),_As=new T2(1,_yA,_Ar),_At=new T2(1,_yu,_As),_Au=new T2(1,_yo,_At),_Av=new T2(1,_yi,_Au),_Aw=new T2(1,_yc,_Av),_Ax=new T2(1,_y6,_Aw),_Ay=new T2(1,_y0,_Ax),_Az=new T2(1,_xU,_Ay),_AA=new T2(1,_xO,_Az),_AB=new T2(1,_xI,_AA),_AC=new T2(1,_xC,_AB),_AD=new T2(1,_xw,_AC),_AE=new T2(1,_xq,_AD),_AF=new T2(1,_xk,_AE),_AG=new T2(1,_xe,_AF),_AH=new T2(1,_x8,_AG),_AI=new T2(1,_x4,_AH),_AJ=new T(function(){return B(_wy(_AI));}),_AK=34,_AL=new T1(0,1114111),_AM=92,_AN=39,_AO=function(_AP){var _AQ=new T(function(){return B(A1(_AP,_xH));}),_AR=new T(function(){return B(A1(_AP,_xN));}),_AS=new T(function(){return B(A1(_AP,_xT));}),_AT=new T(function(){return B(A1(_AP,_xZ));}),_AU=new T(function(){return B(A1(_AP,_y5));}),_AV=new T(function(){return B(A1(_AP,_yb));}),_AW=new T(function(){return B(A1(_AP,_yh));}),_AX=new T(function(){return B(A1(_AP,_AM));}),_AY=new T(function(){return B(A1(_AP,_AN));}),_AZ=new T(function(){return B(A1(_AP,_AK));}),_B0=new T(function(){var _B1=function(_B2){var _B3=new T(function(){return B(_oF(E(_B2)));}),_B4=function(_B5){var _B6=B(_vw(_B3,_B5));if(!B(_wo(_B6,_AL))){return new T0(2);}else{return new F(function(){return A1(_AP,new T(function(){var _B7=B(_oV(_B6));if(_B7>>>0>1114111){return B(_fQ(_B7));}else{return _B7;}}));});}};return new T1(1,B(_tH(_B2,_B4)));},_B8=new T(function(){var _B9=new T(function(){return B(A1(_AP,_zV));}),_Ba=new T(function(){return B(A1(_AP,_zP));}),_Bb=new T(function(){return B(A1(_AP,_zJ));}),_Bc=new T(function(){return B(A1(_AP,_zD));}),_Bd=new T(function(){return B(A1(_AP,_zx));}),_Be=new T(function(){return B(A1(_AP,_zr));}),_Bf=new T(function(){return B(A1(_AP,_zl));}),_Bg=new T(function(){return B(A1(_AP,_zf));}),_Bh=new T(function(){return B(A1(_AP,_z9));}),_Bi=new T(function(){return B(A1(_AP,_z3));}),_Bj=new T(function(){return B(A1(_AP,_yX));}),_Bk=new T(function(){return B(A1(_AP,_yR));}),_Bl=new T(function(){return B(A1(_AP,_yL));}),_Bm=new T(function(){return B(A1(_AP,_yF));}),_Bn=new T(function(){return B(A1(_AP,_yz));}),_Bo=new T(function(){return B(A1(_AP,_yt));}),_Bp=new T(function(){return B(A1(_AP,_yn));}),_Bq=new T(function(){return B(A1(_AP,_wT));}),_Br=new T(function(){return B(A1(_AP,_xB));}),_Bs=new T(function(){return B(A1(_AP,_xv));}),_Bt=new T(function(){return B(A1(_AP,_xp));}),_Bu=new T(function(){return B(A1(_AP,_xj));}),_Bv=new T(function(){return B(A1(_AP,_xd));}),_Bw=new T(function(){return B(A1(_AP,_wZ));}),_Bx=new T(function(){return B(A1(_AP,_x7));}),_By=function(_Bz){switch(E(_Bz)){case 64:return E(_Bx);case 65:return E(_Bw);case 66:return E(_Bv);case 67:return E(_Bu);case 68:return E(_Bt);case 69:return E(_Bs);case 70:return E(_Br);case 71:return E(_AQ);case 72:return E(_AR);case 73:return E(_AS);case 74:return E(_AT);case 75:return E(_AU);case 76:return E(_AV);case 77:return E(_AW);case 78:return E(_Bq);case 79:return E(_Bp);case 80:return E(_Bo);case 81:return E(_Bn);case 82:return E(_Bm);case 83:return E(_Bl);case 84:return E(_Bk);case 85:return E(_Bj);case 86:return E(_Bi);case 87:return E(_Bh);case 88:return E(_Bg);case 89:return E(_Bf);case 90:return E(_Be);case 91:return E(_Bd);case 92:return E(_Bc);case 93:return E(_Bb);case 94:return E(_Ba);case 95:return E(_B9);default:return new T0(2);}};return B(_rH(new T1(0,function(_BA){return (E(_BA)==94)?E(new T1(0,_By)):new T0(2);}),new T(function(){return B(A1(_AJ,_AP));})));});return B(_rH(new T1(1,B(_t0(_wk,_wm,_B1))),_B8));});return new F(function(){return _rH(new T1(0,function(_BB){switch(E(_BB)){case 34:return E(_AZ);case 39:return E(_AY);case 92:return E(_AX);case 97:return E(_AQ);case 98:return E(_AR);case 102:return E(_AV);case 110:return E(_AT);case 114:return E(_AW);case 116:return E(_AS);case 118:return E(_AU);default:return new T0(2);}}),_B0);});},_BC=function(_BD){return new F(function(){return A1(_BD,_5);});},_BE=function(_BF){var _BG=E(_BF);if(!_BG._){return E(_BC);}else{var _BH=E(_BG.a),_BI=_BH>>>0,_BJ=new T(function(){return B(_BE(_BG.b));});if(_BI>887){var _BK=u_iswspace(_BH);if(!E(_BK)){return E(_BC);}else{var _BL=function(_BM){var _BN=new T(function(){return B(A1(_BJ,_BM));});return new T1(0,function(_BO){return E(_BN);});};return E(_BL);}}else{var _BP=E(_BI);if(_BP==32){var _BQ=function(_BR){var _BS=new T(function(){return B(A1(_BJ,_BR));});return new T1(0,function(_BT){return E(_BS);});};return E(_BQ);}else{if(_BP-9>>>0>4){if(E(_BP)==160){var _BU=function(_BV){var _BW=new T(function(){return B(A1(_BJ,_BV));});return new T1(0,function(_BX){return E(_BW);});};return E(_BU);}else{return E(_BC);}}else{var _BY=function(_BZ){var _C0=new T(function(){return B(A1(_BJ,_BZ));});return new T1(0,function(_C1){return E(_C0);});};return E(_BY);}}}}},_C2=function(_C3){var _C4=new T(function(){return B(_C2(_C3));}),_C5=function(_C6){return (E(_C6)==92)?E(_C4):new T0(2);},_C7=function(_C8){return E(new T1(0,_C5));},_C9=new T1(1,function(_Ca){return new F(function(){return A2(_BE,_Ca,_C7);});}),_Cb=new T(function(){return B(_AO(function(_Cc){return new F(function(){return A1(_C3,new T2(0,_Cc,_we));});}));}),_Cd=function(_Ce){var _Cf=E(_Ce);if(_Cf==38){return E(_C4);}else{var _Cg=_Cf>>>0;if(_Cg>887){var _Ch=u_iswspace(_Cf);return (E(_Ch)==0)?new T0(2):E(_C9);}else{var _Ci=E(_Cg);return (_Ci==32)?E(_C9):(_Ci-9>>>0>4)?(E(_Ci)==160)?E(_C9):new T0(2):E(_C9);}}};return new F(function(){return _rH(new T1(0,function(_Cj){return (E(_Cj)==92)?E(new T1(0,_Cd)):new T0(2);}),new T1(0,function(_Ck){var _Cl=E(_Ck);if(E(_Cl)==92){return E(_Cb);}else{return new F(function(){return A1(_C3,new T2(0,_Cl,_wd));});}}));});},_Cm=function(_Cn,_Co){var _Cp=new T(function(){return B(A1(_Co,new T1(1,new T(function(){return B(A1(_Cn,_4));}))));}),_Cq=function(_Cr){var _Cs=E(_Cr),_Ct=E(_Cs.a);if(E(_Ct)==34){if(!E(_Cs.b)){return E(_Cp);}else{return new F(function(){return _Cm(function(_Cu){return new F(function(){return A1(_Cn,new T2(1,_Ct,_Cu));});},_Co);});}}else{return new F(function(){return _Cm(function(_Cv){return new F(function(){return A1(_Cn,new T2(1,_Ct,_Cv));});},_Co);});}};return new F(function(){return _C2(_Cq);});},_Cw=new T(function(){return B(unCStr("_\'"));}),_Cx=function(_Cy){var _Cz=u_iswalnum(_Cy);if(!E(_Cz)){return new F(function(){return _w5(_sw,_Cy,_Cw);});}else{return true;}},_CA=function(_CB){return new F(function(){return _Cx(E(_CB));});},_CC=new T(function(){return B(unCStr(",;()[]{}`"));}),_CD=new T(function(){return B(unCStr("=>"));}),_CE=new T2(1,_CD,_4),_CF=new T(function(){return B(unCStr("~"));}),_CG=new T2(1,_CF,_CE),_CH=new T(function(){return B(unCStr("@"));}),_CI=new T2(1,_CH,_CG),_CJ=new T(function(){return B(unCStr("->"));}),_CK=new T2(1,_CJ,_CI),_CL=new T(function(){return B(unCStr("<-"));}),_CM=new T2(1,_CL,_CK),_CN=new T(function(){return B(unCStr("|"));}),_CO=new T2(1,_CN,_CM),_CP=new T(function(){return B(unCStr("\\"));}),_CQ=new T2(1,_CP,_CO),_CR=new T(function(){return B(unCStr("="));}),_CS=new T2(1,_CR,_CQ),_CT=new T(function(){return B(unCStr("::"));}),_CU=new T2(1,_CT,_CS),_CV=new T(function(){return B(unCStr(".."));}),_CW=new T2(1,_CV,_CU),_CX=function(_CY){var _CZ=new T(function(){return B(A1(_CY,_tE));}),_D0=new T(function(){var _D1=new T(function(){var _D2=function(_D3){var _D4=new T(function(){return B(A1(_CY,new T1(0,_D3)));});return new T1(0,function(_D5){return (E(_D5)==39)?E(_D4):new T0(2);});};return B(_AO(_D2));}),_D6=function(_D7){var _D8=E(_D7);switch(E(_D8)){case 39:return new T0(2);case 92:return E(_D1);default:var _D9=new T(function(){return B(A1(_CY,new T1(0,_D8)));});return new T1(0,function(_Da){return (E(_Da)==39)?E(_D9):new T0(2);});}},_Db=new T(function(){var _Dc=new T(function(){return B(_Cm(_2j,_CY));}),_Dd=new T(function(){var _De=new T(function(){var _Df=new T(function(){var _Dg=function(_Dh){var _Di=E(_Dh),_Dj=u_iswalpha(_Di);return (E(_Dj)==0)?(E(_Di)==95)?new T1(1,B(_tq(_CA,function(_Dk){return new F(function(){return A1(_CY,new T1(3,new T2(1,_Di,_Dk)));});}))):new T0(2):new T1(1,B(_tq(_CA,function(_Dl){return new F(function(){return A1(_CY,new T1(3,new T2(1,_Di,_Dl)));});})));};return B(_rH(new T1(0,_Dg),new T(function(){return new T1(1,B(_t0(_uC,_w3,_CY)));})));}),_Dm=function(_Dn){return (!B(_w5(_sw,_Dn,_wa)))?new T0(2):new T1(1,B(_tq(_wb,function(_Do){var _Dp=new T2(1,_Dn,_Do);if(!B(_w5(_sF,_Dp,_CW))){return new F(function(){return A1(_CY,new T1(4,_Dp));});}else{return new F(function(){return A1(_CY,new T1(2,_Dp));});}})));};return B(_rH(new T1(0,_Dm),_Df));});return B(_rH(new T1(0,function(_Dq){if(!B(_w5(_sw,_Dq,_CC))){return new T0(2);}else{return new F(function(){return A1(_CY,new T1(2,new T2(1,_Dq,_4)));});}}),_De));});return B(_rH(new T1(0,function(_Dr){return (E(_Dr)==34)?E(_Dc):new T0(2);}),_Dd));});return B(_rH(new T1(0,function(_Ds){return (E(_Ds)==39)?E(new T1(0,_D6)):new T0(2);}),_Db));});return new F(function(){return _rH(new T1(1,function(_Dt){return (E(_Dt)._==0)?E(_CZ):new T0(2);}),_D0);});},_Du=0,_Dv=function(_Dw,_Dx){var _Dy=new T(function(){var _Dz=new T(function(){var _DA=function(_DB){var _DC=new T(function(){var _DD=new T(function(){return B(A1(_Dx,_DB));});return B(_CX(function(_DE){var _DF=E(_DE);return (_DF._==2)?(!B(_sl(_DF.a,_sk)))?new T0(2):E(_DD):new T0(2);}));}),_DG=function(_DH){return E(_DC);};return new T1(1,function(_DI){return new F(function(){return A2(_BE,_DI,_DG);});});};return B(A2(_Dw,_Du,_DA));});return B(_CX(function(_DJ){var _DK=E(_DJ);return (_DK._==2)?(!B(_sl(_DK.a,_sj)))?new T0(2):E(_Dz):new T0(2);}));}),_DL=function(_DM){return E(_Dy);};return function(_DN){return new F(function(){return A2(_BE,_DN,_DL);});};},_DO=function(_DP,_DQ){var _DR=function(_DS){var _DT=new T(function(){return B(A1(_DP,_DS));}),_DU=function(_DV){return new F(function(){return _rH(B(A1(_DT,_DV)),new T(function(){return new T1(1,B(_Dv(_DR,_DV)));}));});};return E(_DU);},_DW=new T(function(){return B(A1(_DP,_DQ));}),_DX=function(_DY){return new F(function(){return _rH(B(A1(_DW,_DY)),new T(function(){return new T1(1,B(_Dv(_DR,_DY)));}));});};return E(_DX);},_DZ=function(_E0,_E1){var _E2=function(_E3,_E4){var _E5=function(_E6){return new F(function(){return A1(_E4,new T(function(){return  -E(_E6);}));});},_E7=new T(function(){return B(_CX(function(_E8){return new F(function(){return A3(_E0,_E8,_E3,_E5);});}));}),_E9=function(_Ea){return E(_E7);},_Eb=function(_Ec){return new F(function(){return A2(_BE,_Ec,_E9);});},_Ed=new T(function(){return B(_CX(function(_Ee){var _Ef=E(_Ee);if(_Ef._==4){var _Eg=E(_Ef.a);if(!_Eg._){return new F(function(){return A3(_E0,_Ef,_E3,_E4);});}else{if(E(_Eg.a)==45){if(!E(_Eg.b)._){return E(new T1(1,_Eb));}else{return new F(function(){return A3(_E0,_Ef,_E3,_E4);});}}else{return new F(function(){return A3(_E0,_Ef,_E3,_E4);});}}}else{return new F(function(){return A3(_E0,_Ef,_E3,_E4);});}}));}),_Eh=function(_Ei){return E(_Ed);};return new T1(1,function(_Ej){return new F(function(){return A2(_BE,_Ej,_Eh);});});};return new F(function(){return _DO(_E2,_E1);});},_Ek=new T(function(){return 1/0;}),_El=function(_Em,_En){return new F(function(){return A1(_En,_Ek);});},_Eo=new T(function(){return 0/0;}),_Ep=function(_Eq,_Er){return new F(function(){return A1(_Er,_Eo);});},_Es=new T(function(){return B(unCStr("NaN"));}),_Et=new T(function(){return B(unCStr("Infinity"));}),_Eu=1024,_Ev=-1021,_Ew=function(_Ex,_Ey){while(1){var _Ez=E(_Ex);if(!_Ez._){var _EA=E(_Ez.a);if(_EA==(-2147483648)){_Ex=new T1(1,I_fromInt(-2147483648));continue;}else{var _EB=E(_Ey);if(!_EB._){return new T1(0,_EA%_EB.a);}else{_Ex=new T1(1,I_fromInt(_EA));_Ey=_EB;continue;}}}else{var _EC=_Ez.a,_ED=E(_Ey);return (_ED._==0)?new T1(1,I_rem(_EC,I_fromInt(_ED.a))):new T1(1,I_rem(_EC,_ED.a));}}},_EE=function(_EF,_EG){if(!B(_qK(_EG,_pU))){return new F(function(){return _Ew(_EF,_EG);});}else{return E(_nI);}},_EH=function(_EI,_EJ){while(1){if(!B(_qK(_EJ,_pU))){var _EK=_EJ,_EL=B(_EE(_EI,_EJ));_EI=_EK;_EJ=_EL;continue;}else{return E(_EI);}}},_EM=function(_EN){var _EO=E(_EN);if(!_EO._){var _EP=E(_EO.a);return (_EP==(-2147483648))?E(_uU):(_EP<0)?new T1(0, -_EP):E(_EO);}else{var _EQ=_EO.a;return (I_compareInt(_EQ,0)>=0)?E(_EO):new T1(1,I_negate(_EQ));}},_ER=function(_ES,_ET){while(1){var _EU=E(_ES);if(!_EU._){var _EV=E(_EU.a);if(_EV==(-2147483648)){_ES=new T1(1,I_fromInt(-2147483648));continue;}else{var _EW=E(_ET);if(!_EW._){return new T1(0,quot(_EV,_EW.a));}else{_ES=new T1(1,I_fromInt(_EV));_ET=_EW;continue;}}}else{var _EX=_EU.a,_EY=E(_ET);return (_EY._==0)?new T1(0,I_toInt(I_quot(_EX,I_fromInt(_EY.a)))):new T1(1,I_quot(_EX,_EY.a));}}},_EZ=5,_F0=new T(function(){return B(_nF(_EZ));}),_F1=new T(function(){return die(_F0);}),_F2=function(_F3,_F4){if(!B(_qK(_F4,_pU))){var _F5=B(_EH(B(_EM(_F3)),B(_EM(_F4))));return (!B(_qK(_F5,_pU)))?new T2(0,B(_ER(_F3,_F5)),B(_ER(_F4,_F5))):E(_nI);}else{return E(_F1);}},_F6=new T(function(){return B(_qK(_pV,_pU));}),_F7=function(_F8,_F9){while(1){var _Fa=E(_F8);if(!_Fa._){var _Fb=_Fa.a,_Fc=E(_F9);if(!_Fc._){var _Fd=_Fc.a,_Fe=subC(_Fb,_Fd);if(!E(_Fe.b)){return new T1(0,_Fe.a);}else{_F8=new T1(1,I_fromInt(_Fb));_F9=new T1(1,I_fromInt(_Fd));continue;}}else{_F8=new T1(1,I_fromInt(_Fb));_F9=_Fc;continue;}}else{var _Ff=E(_F9);if(!_Ff._){_F8=_Fa;_F9=new T1(1,I_fromInt(_Ff.a));continue;}else{return new T1(1,I_sub(_Fa.a,_Ff.a));}}}},_Fg=function(_Fh,_Fi,_Fj){while(1){if(!E(_F6)){if(!B(_qK(B(_Ew(_Fi,_pV)),_pU))){if(!B(_qK(_Fi,_oJ))){var _Fk=B(_pm(_Fh,_Fh)),_Fl=B(_ER(B(_F7(_Fi,_oJ)),_pV)),_Fm=B(_pm(_Fh,_Fj));_Fh=_Fk;_Fi=_Fl;_Fj=_Fm;continue;}else{return new F(function(){return _pm(_Fh,_Fj);});}}else{var _Fk=B(_pm(_Fh,_Fh)),_Fl=B(_ER(_Fi,_pV));_Fh=_Fk;_Fi=_Fl;continue;}}else{return E(_nI);}}},_Fn=function(_Fo,_Fp){while(1){if(!E(_F6)){if(!B(_qK(B(_Ew(_Fp,_pV)),_pU))){if(!B(_qK(_Fp,_oJ))){return new F(function(){return _Fg(B(_pm(_Fo,_Fo)),B(_ER(B(_F7(_Fp,_oJ)),_pV)),_Fo);});}else{return E(_Fo);}}else{var _Fq=B(_pm(_Fo,_Fo)),_Fr=B(_ER(_Fp,_pV));_Fo=_Fq;_Fp=_Fr;continue;}}else{return E(_nI);}}},_Fs=function(_Ft,_Fu){var _Fv=E(_Ft);if(!_Fv._){var _Fw=_Fv.a,_Fx=E(_Fu);return (_Fx._==0)?_Fw<_Fx.a:I_compareInt(_Fx.a,_Fw)>0;}else{var _Fy=_Fv.a,_Fz=E(_Fu);return (_Fz._==0)?I_compareInt(_Fy,_Fz.a)<0:I_compare(_Fy,_Fz.a)<0;}},_FA=function(_FB,_FC){if(!B(_Fs(_FC,_pU))){if(!B(_qK(_FC,_pU))){return new F(function(){return _Fn(_FB,_FC);});}else{return E(_oJ);}}else{return E(_qC);}},_FD=new T1(0,1),_FE=new T1(0,0),_FF=new T1(0,-1),_FG=function(_FH){var _FI=E(_FH);if(!_FI._){var _FJ=_FI.a;return (_FJ>=0)?(E(_FJ)==0)?E(_FE):E(_uJ):E(_FF);}else{var _FK=I_compareInt(_FI.a,0);return (_FK<=0)?(E(_FK)==0)?E(_FE):E(_FF):E(_uJ);}},_FL=function(_FM,_FN,_FO){while(1){var _FP=E(_FO);if(!_FP._){if(!B(_Fs(_FM,_ve))){return new T2(0,B(_pm(_FN,B(_FA(_uZ,_FM)))),_oJ);}else{var _FQ=B(_FA(_uZ,B(_uV(_FM))));return new F(function(){return _F2(B(_pm(_FN,B(_FG(_FQ)))),B(_EM(_FQ)));});}}else{var _FR=B(_F7(_FM,_FD)),_FS=B(_uL(B(_pm(_FN,_uZ)),B(_oF(E(_FP.a)))));_FM=_FR;_FN=_FS;_FO=_FP.b;continue;}}},_FT=function(_FU,_FV){var _FW=E(_FU);if(!_FW._){var _FX=_FW.a,_FY=E(_FV);return (_FY._==0)?_FX>=_FY.a:I_compareInt(_FY.a,_FX)<=0;}else{var _FZ=_FW.a,_G0=E(_FV);return (_G0._==0)?I_compareInt(_FZ,_G0.a)>=0:I_compare(_FZ,_G0.a)>=0;}},_G1=function(_G2){var _G3=E(_G2);if(!_G3._){var _G4=_G3.b;return new F(function(){return _F2(B(_pm(B(_vf(new T(function(){return B(_oF(E(_G3.a)));}),new T(function(){return B(_v0(_G4,0));},1),B(_G(_v5,_G4)))),_FD)),_FD);});}else{var _G5=_G3.a,_G6=_G3.c,_G7=E(_G3.b);if(!_G7._){var _G8=E(_G6);if(!_G8._){return new F(function(){return _F2(B(_pm(B(_vw(_uZ,_G5)),_FD)),_FD);});}else{var _G9=_G8.a;if(!B(_FT(_G9,_ve))){var _Ga=B(_FA(_uZ,B(_uV(_G9))));return new F(function(){return _F2(B(_pm(B(_vw(_uZ,_G5)),B(_FG(_Ga)))),B(_EM(_Ga)));});}else{return new F(function(){return _F2(B(_pm(B(_pm(B(_vw(_uZ,_G5)),B(_FA(_uZ,_G9)))),_FD)),_FD);});}}}else{var _Gb=_G7.a,_Gc=E(_G6);if(!_Gc._){return new F(function(){return _FL(_ve,B(_vw(_uZ,_G5)),_Gb);});}else{return new F(function(){return _FL(_Gc.a,B(_vw(_uZ,_G5)),_Gb);});}}}},_Gd=function(_Ge,_Gf){while(1){var _Gg=E(_Gf);if(!_Gg._){return __Z;}else{if(!B(A1(_Ge,_Gg.a))){return E(_Gg);}else{_Gf=_Gg.b;continue;}}}},_Gh=function(_Gi,_Gj){var _Gk=E(_Gi);if(!_Gk._){var _Gl=_Gk.a,_Gm=E(_Gj);return (_Gm._==0)?_Gl>_Gm.a:I_compareInt(_Gm.a,_Gl)<0;}else{var _Gn=_Gk.a,_Go=E(_Gj);return (_Go._==0)?I_compareInt(_Gn,_Go.a)>0:I_compare(_Gn,_Go.a)>0;}},_Gp=0,_Gq=function(_Gr){return new F(function(){return _j1(_Gp,_Gr);});},_Gs=new T2(0,E(_ve),E(_oJ)),_Gt=new T1(1,_Gs),_Gu=new T1(0,-2147483648),_Gv=new T1(0,2147483647),_Gw=function(_Gx,_Gy,_Gz){var _GA=E(_Gz);if(!_GA._){return new T1(1,new T(function(){var _GB=B(_G1(_GA));return new T2(0,E(_GB.a),E(_GB.b));}));}else{var _GC=E(_GA.c);if(!_GC._){return new T1(1,new T(function(){var _GD=B(_G1(_GA));return new T2(0,E(_GD.a),E(_GD.b));}));}else{var _GE=_GC.a;if(!B(_Gh(_GE,_Gv))){if(!B(_Fs(_GE,_Gu))){var _GF=function(_GG){var _GH=_GG+B(_oV(_GE))|0;return (_GH<=(E(_Gy)+3|0))?(_GH>=(E(_Gx)-3|0))?new T1(1,new T(function(){var _GI=B(_G1(_GA));return new T2(0,E(_GI.a),E(_GI.b));})):E(_Gt):__Z;},_GJ=B(_Gd(_Gq,_GA.a));if(!_GJ._){var _GK=E(_GA.b);if(!_GK._){return E(_Gt);}else{var _GL=B(_6T(_Gq,_GK.a));if(!E(_GL.b)._){return E(_Gt);}else{return new F(function(){return _GF( -B(_v0(_GL.a,0)));});}}}else{return new F(function(){return _GF(B(_v0(_GJ,0)));});}}else{return __Z;}}else{return __Z;}}}},_GM=function(_GN,_GO){return new T0(2);},_GP=new T1(0,1),_GQ=function(_GR,_GS){var _GT=E(_GR);if(!_GT._){var _GU=_GT.a,_GV=E(_GS);if(!_GV._){var _GW=_GV.a;return (_GU!=_GW)?(_GU>_GW)?2:0:1;}else{var _GX=I_compareInt(_GV.a,_GU);return (_GX<=0)?(_GX>=0)?1:2:0;}}else{var _GY=_GT.a,_GZ=E(_GS);if(!_GZ._){var _H0=I_compareInt(_GY,_GZ.a);return (_H0>=0)?(_H0<=0)?1:2:0;}else{var _H1=I_compare(_GY,_GZ.a);return (_H1>=0)?(_H1<=0)?1:2:0;}}},_H2=function(_H3,_H4){while(1){var _H5=E(_H3);if(!_H5._){_H3=new T1(1,I_fromInt(_H5.a));continue;}else{return new T1(1,I_shiftLeft(_H5.a,_H4));}}},_H6=function(_H7,_H8,_H9){if(!B(_qK(_H9,_r2))){var _Ha=B(_qS(_H8,_H9)),_Hb=_Ha.a;switch(B(_GQ(B(_H2(_Ha.b,1)),_H9))){case 0:return new F(function(){return _qG(_Hb,_H7);});break;case 1:if(!(B(_oV(_Hb))&1)){return new F(function(){return _qG(_Hb,_H7);});}else{return new F(function(){return _qG(B(_uL(_Hb,_GP)),_H7);});}break;default:return new F(function(){return _qG(B(_uL(_Hb,_GP)),_H7);});}}else{return E(_nI);}},_Hc=function(_Hd){var _He=function(_Hf,_Hg){while(1){if(!B(_Fs(_Hf,_Hd))){if(!B(_Gh(_Hf,_Hd))){if(!B(_qK(_Hf,_Hd))){return new F(function(){return _7f("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_Hg);}}else{return _Hg-1|0;}}else{var _Hh=B(_H2(_Hf,1)),_Hi=_Hg+1|0;_Hf=_Hh;_Hg=_Hi;continue;}}};return new F(function(){return _He(_uJ,0);});},_Hj=function(_Hk){var _Hl=E(_Hk);if(!_Hl._){var _Hm=_Hl.a>>>0;if(!_Hm){return -1;}else{var _Hn=function(_Ho,_Hp){while(1){if(_Ho>=_Hm){if(_Ho<=_Hm){if(_Ho!=_Hm){return new F(function(){return _7f("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_Hp);}}else{return _Hp-1|0;}}else{var _Hq=imul(_Ho,2)>>>0,_Hr=_Hp+1|0;_Ho=_Hq;_Hp=_Hr;continue;}}};return new F(function(){return _Hn(1,0);});}}else{return new F(function(){return _Hc(_Hl);});}},_Hs=function(_Ht){var _Hu=E(_Ht);if(!_Hu._){var _Hv=_Hu.a>>>0;if(!_Hv){return new T2(0,-1,0);}else{var _Hw=function(_Hx,_Hy){while(1){if(_Hx>=_Hv){if(_Hx<=_Hv){if(_Hx!=_Hv){return new F(function(){return _7f("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_Hy);}}else{return _Hy-1|0;}}else{var _Hz=imul(_Hx,2)>>>0,_HA=_Hy+1|0;_Hx=_Hz;_Hy=_HA;continue;}}};return new T2(0,B(_Hw(1,0)),(_Hv&_Hv-1>>>0)>>>0&4294967295);}}else{var _HB=_Hu.a;return new T2(0,B(_Hj(_Hu)),I_compareInt(I_and(_HB,I_sub(_HB,I_fromInt(1))),0));}},_HC=function(_HD,_HE){while(1){var _HF=E(_HD);if(!_HF._){var _HG=_HF.a,_HH=E(_HE);if(!_HH._){return new T1(0,(_HG>>>0&_HH.a>>>0)>>>0&4294967295);}else{_HD=new T1(1,I_fromInt(_HG));_HE=_HH;continue;}}else{var _HI=E(_HE);if(!_HI._){_HD=_HF;_HE=new T1(1,I_fromInt(_HI.a));continue;}else{return new T1(1,I_and(_HF.a,_HI.a));}}}},_HJ=new T1(0,2),_HK=function(_HL,_HM){var _HN=E(_HL);if(!_HN._){var _HO=(_HN.a>>>0&(2<<_HM>>>0)-1>>>0)>>>0,_HP=1<<_HM>>>0;return (_HP<=_HO)?(_HP>=_HO)?1:2:0;}else{var _HQ=B(_HC(_HN,B(_F7(B(_H2(_HJ,_HM)),_uJ)))),_HR=B(_H2(_uJ,_HM));return (!B(_Gh(_HR,_HQ)))?(!B(_Fs(_HR,_HQ)))?1:2:0;}},_HS=function(_HT,_HU){while(1){var _HV=E(_HT);if(!_HV._){_HT=new T1(1,I_fromInt(_HV.a));continue;}else{return new T1(1,I_shiftRight(_HV.a,_HU));}}},_HW=function(_HX,_HY,_HZ,_I0){var _I1=B(_Hs(_I0)),_I2=_I1.a;if(!E(_I1.b)){var _I3=B(_Hj(_HZ));if(_I3<((_I2+_HX|0)-1|0)){var _I4=_I2+(_HX-_HY|0)|0;if(_I4>0){if(_I4>_I3){if(_I4<=(_I3+1|0)){if(!E(B(_Hs(_HZ)).b)){return 0;}else{return new F(function(){return _qG(_GP,_HX-_HY|0);});}}else{return 0;}}else{var _I5=B(_HS(_HZ,_I4));switch(B(_HK(_HZ,_I4-1|0))){case 0:return new F(function(){return _qG(_I5,_HX-_HY|0);});break;case 1:if(!(B(_oV(_I5))&1)){return new F(function(){return _qG(_I5,_HX-_HY|0);});}else{return new F(function(){return _qG(B(_uL(_I5,_GP)),_HX-_HY|0);});}break;default:return new F(function(){return _qG(B(_uL(_I5,_GP)),_HX-_HY|0);});}}}else{return new F(function(){return _qG(_HZ,(_HX-_HY|0)-_I4|0);});}}else{if(_I3>=_HY){var _I6=B(_HS(_HZ,(_I3+1|0)-_HY|0));switch(B(_HK(_HZ,_I3-_HY|0))){case 0:return new F(function(){return _qG(_I6,((_I3-_I2|0)+1|0)-_HY|0);});break;case 2:return new F(function(){return _qG(B(_uL(_I6,_GP)),((_I3-_I2|0)+1|0)-_HY|0);});break;default:if(!(B(_oV(_I6))&1)){return new F(function(){return _qG(_I6,((_I3-_I2|0)+1|0)-_HY|0);});}else{return new F(function(){return _qG(B(_uL(_I6,_GP)),((_I3-_I2|0)+1|0)-_HY|0);});}}}else{return new F(function(){return _qG(_HZ, -_I2);});}}}else{var _I7=B(_Hj(_HZ))-_I2|0,_I8=function(_I9){var _Ia=function(_Ib,_Ic){if(!B(_wo(B(_H2(_Ic,_HY)),_Ib))){return new F(function(){return _H6(_I9-_HY|0,_Ib,_Ic);});}else{return new F(function(){return _H6((_I9-_HY|0)+1|0,_Ib,B(_H2(_Ic,1)));});}};if(_I9>=_HY){if(_I9!=_HY){return new F(function(){return _Ia(_HZ,new T(function(){return B(_H2(_I0,_I9-_HY|0));}));});}else{return new F(function(){return _Ia(_HZ,_I0);});}}else{return new F(function(){return _Ia(new T(function(){return B(_H2(_HZ,_HY-_I9|0));}),_I0);});}};if(_HX>_I7){return new F(function(){return _I8(_HX);});}else{return new F(function(){return _I8(_I7);});}}},_Id=new T(function(){return 0/0;}),_Ie=new T(function(){return -1/0;}),_If=new T(function(){return 1/0;}),_Ig=function(_Ih,_Ii){if(!B(_qK(_Ii,_r2))){if(!B(_qK(_Ih,_r2))){if(!B(_Fs(_Ih,_r2))){return new F(function(){return _HW(-1021,53,_Ih,_Ii);});}else{return  -B(_HW(-1021,53,B(_uV(_Ih)),_Ii));}}else{return E(_r1);}}else{return (!B(_qK(_Ih,_r2)))?(!B(_Fs(_Ih,_r2)))?E(_If):E(_Ie):E(_Id);}},_Ij=function(_Ik){var _Il=E(_Ik);switch(_Il._){case 3:var _Im=_Il.a;return (!B(_sl(_Im,_Et)))?(!B(_sl(_Im,_Es)))?E(_GM):E(_Ep):E(_El);case 5:var _In=B(_Gw(_Ev,_Eu,_Il.a));if(!_In._){return E(_El);}else{var _Io=new T(function(){var _Ip=E(_In.a);return B(_Ig(_Ip.a,_Ip.b));});return function(_Iq,_Ir){return new F(function(){return A1(_Ir,_Io);});};}break;default:return E(_GM);}},_Is=function(_It){var _Iu=function(_Iv){return E(new T2(3,_It,_sR));};return new T1(1,function(_Iw){return new F(function(){return A2(_BE,_Iw,_Iu);});});},_Ix=new T(function(){return B(A3(_DZ,_Ij,_Du,_Is));}),_Iy=new T(function(){return B(_rx(_Ix,_rv));}),_Iz=function(_IA){while(1){var _IB=B((function(_IC){var _ID=E(_IC);if(!_ID._){return __Z;}else{var _IE=_ID.b,_IF=E(_ID.a);if(!E(_IF.b)._){return new T2(1,_IF.a,new T(function(){return B(_Iz(_IE));}));}else{_IA=_IE;return __continue;}}})(_IA));if(_IB!=__continue){return _IB;}}},_IG=new T(function(){return B(_Iz(_Iy));}),_IH=new T(function(){return B(unCStr("Infinity"));}),_II=new T(function(){return B(_rx(_Ix,_IH));}),_IJ=new T(function(){return B(_Iz(_II));}),_IK=0,_IL=function(_IM,_IN,_IO){return new F(function(){return _eX(_ea,new T2(0,_IN,_IO),_IM,_f2);});},_IP=function(_IQ,_IR,_IS){var _IT=(_IQ+_IR|0)-1|0;if(_IQ<=_IT){var _IU=function(_IV){return new T2(1,new T(function(){var _IW=E(_IS),_IX=_IW.c,_IY=E(_IW.a),_IZ=E(_IW.b);if(_IY>_IV){return B(_IL(_IV,_IY,_IZ));}else{if(_IV>_IZ){return B(_IL(_IV,_IY,_IZ));}else{var _J0=_IV-_IY|0;if(0>_J0){return B(_dT(_J0,_IX));}else{if(_J0>=_IX){return B(_dT(_J0,_IX));}else{return _IW.d["v"]["w8"][_J0];}}}}}),new T(function(){if(_IV!=_IT){return B(_IU(_IV+1|0));}else{return __Z;}}));};return new F(function(){return _IU(_IQ);});}else{return __Z;}},_J1=function(_J2){var _J3=E(_J2);return new F(function(){return _IP(_J3.a,_J3.b,_J3.c);});},_J4=function(_J5,_J6,_J7,_J8){var _J9=new T(function(){var _Ja=E(_J5),_Jb=E(_J7),_Jc=_Jb.a,_Jd=_Jb.b,_Je=_Jb.c,_Jf=E(_J8);if((_Jf+_Ja|0)<=_Jd){return new T2(0,new T(function(){var _Jg=_Jd-_Jf|0;if(_Ja>_Jg){return new T3(0,_Jc+_Jf|0,_Jg,_Je);}else{return new T3(0,_Jc+_Jf|0,_Ja,_Je);}}),_Jf+_Ja|0);}else{return E(_fy);}}),_Jh=new T(function(){return B(A1(_J6,new T(function(){return B(_J1(E(_J9).a));})));}),_Ji=new T(function(){var _Jj=E(_Jh),_Jk=_Jj.d,_Jl=_Jj.e,_Jm=_Jj.f,_Jn=E(_Jj.c);if(!_Jn){if(!B(_qK(_Jk,_rp))){var _Jo=B(_r3(_pc,Math.pow(2,E(_Jl)-1|0))),_Jp=_Jo.a;if(E(_Jo.b)>=0){return B(_qG(_Jk,((1-E(_Jp)|0)-E(_Jm)|0)+1|0));}else{return B(_qG(_Jk,((1-(E(_Jp)-1|0)|0)-E(_Jm)|0)+1|0));}}else{return E(_IK);}}else{var _Jq=E(_Jl);if(_Jn!=(B(_rj(_ru,_Jq))-1|0)){var _Jr=B(_r3(_pc,Math.pow(2,_Jq-1|0))),_Js=_Jr.a;if(E(_Jr.b)>=0){var _Jt=E(_Jm);return B(_qG(B(_uL(_Jk,B(_H2(_ro,_Jt)))),((_Jn+1|0)-E(_Js)|0)-_Jt|0));}else{var _Ju=E(_Jm);return B(_qG(B(_uL(_Jk,B(_H2(_ro,_Ju)))),((_Jn+1|0)-(E(_Js)-1|0)|0)-_Ju|0));}}else{if(!B(_qK(_Jk,_rp))){var _Jv=E(_IG);if(!_Jv._){return E(_rr);}else{if(!E(_Jv.b)._){return E(_Jv.a);}else{return E(_rt);}}}else{var _Jw=E(_IJ);if(!_Jw._){return E(_rr);}else{if(!E(_Jw.b)._){return E(_Jw.a);}else{return E(_rt);}}}}}});return new T2(0,new T(function(){if(!E(E(_Jh).b)){return E(_Ji);}else{return  -E(_Ji);}}),new T(function(){return E(E(_J9).b);}));},_Jx=new T(function(){return B(unCStr("This file was compiled with different version of GF"));}),_Jy=new T(function(){return B(err(_Jx));}),_Jz=8,_JA={_:0,a:_n4,b:_mZ,c:_mV,d:_mV,e:_mp,f:_mK,g:_iK,h:_mR},_JB={_:0,a:_oP,b:_iV,c:_oM,d:_p0,e:_oS,f:_p5,g:_oY},_JC=new T2(0,_j1,_j4),_JD={_:0,a:_JC,b:_jl,c:_jx,d:_ju,e:_jr,f:_jo,g:_j8,h:_jd},_JE=new T3(0,_JB,_JD,_oK),_JF={_:0,a:_JE,b:_JA,c:_on,d:_oB,e:_nR,f:_oj,g:_ot,h:_nW,i:_oH},_JG=new T1(0,1),_JH=function(_JI,_JJ){var _JK=E(_JI);return new T2(0,_JK,new T(function(){var _JL=B(_JH(B(_uL(_JK,_JJ)),_JJ));return new T2(1,_JL.a,_JL.b);}));},_JM=function(_JN){var _JO=B(_JH(_JN,_JG));return new T2(1,_JO.a,_JO.b);},_JP=function(_JQ,_JR){var _JS=B(_JH(_JQ,new T(function(){return B(_F7(_JR,_JQ));})));return new T2(1,_JS.a,_JS.b);},_JT=new T1(0,0),_JU=function(_JV,_JW,_JX){if(!B(_FT(_JW,_JT))){var _JY=function(_JZ){return (!B(_Fs(_JZ,_JX)))?new T2(1,_JZ,new T(function(){return B(_JY(B(_uL(_JZ,_JW))));})):__Z;};return new F(function(){return _JY(_JV);});}else{var _K0=function(_K1){return (!B(_Gh(_K1,_JX)))?new T2(1,_K1,new T(function(){return B(_K0(B(_uL(_K1,_JW))));})):__Z;};return new F(function(){return _K0(_JV);});}},_K2=function(_K3,_K4,_K5){return new F(function(){return _JU(_K3,B(_F7(_K4,_K3)),_K5);});},_K6=function(_K7,_K8){return new F(function(){return _JU(_K7,_JG,_K8);});},_K9=function(_Ka){return new F(function(){return _oV(_Ka);});},_Kb=function(_Kc){return new F(function(){return _F7(_Kc,_JG);});},_Kd=function(_Ke){return new F(function(){return _uL(_Ke,_JG);});},_Kf=function(_Kg){return new F(function(){return _oF(E(_Kg));});},_Kh={_:0,a:_Kd,b:_Kb,c:_Kf,d:_K9,e:_JM,f:_JP,g:_K6,h:_K2},_Ki=function(_Kj,_Kk){while(1){var _Kl=E(_Kj);if(!_Kl._){var _Km=E(_Kl.a);if(_Km==(-2147483648)){_Kj=new T1(1,I_fromInt(-2147483648));continue;}else{var _Kn=E(_Kk);if(!_Kn._){return new T1(0,B(_n8(_Km,_Kn.a)));}else{_Kj=new T1(1,I_fromInt(_Km));_Kk=_Kn;continue;}}}else{var _Ko=_Kl.a,_Kp=E(_Kk);return (_Kp._==0)?new T1(1,I_div(_Ko,I_fromInt(_Kp.a))):new T1(1,I_div(_Ko,_Kp.a));}}},_Kq=function(_Kr,_Ks){if(!B(_qK(_Ks,_pU))){return new F(function(){return _Ki(_Kr,_Ks);});}else{return E(_nI);}},_Kt=function(_Ku,_Kv){while(1){var _Kw=E(_Ku);if(!_Kw._){var _Kx=E(_Kw.a);if(_Kx==(-2147483648)){_Ku=new T1(1,I_fromInt(-2147483648));continue;}else{var _Ky=E(_Kv);if(!_Ky._){var _Kz=_Ky.a;return new T2(0,new T1(0,B(_n8(_Kx,_Kz))),new T1(0,B(_oc(_Kx,_Kz))));}else{_Ku=new T1(1,I_fromInt(_Kx));_Kv=_Ky;continue;}}}else{var _KA=E(_Kv);if(!_KA._){_Ku=_Kw;_Kv=new T1(1,I_fromInt(_KA.a));continue;}else{var _KB=I_divMod(_Kw.a,_KA.a);return new T2(0,new T1(1,_KB.a),new T1(1,_KB.b));}}}},_KC=function(_KD,_KE){if(!B(_qK(_KE,_pU))){var _KF=B(_Kt(_KD,_KE));return new T2(0,_KF.a,_KF.b);}else{return E(_nI);}},_KG=function(_KH,_KI){while(1){var _KJ=E(_KH);if(!_KJ._){var _KK=E(_KJ.a);if(_KK==(-2147483648)){_KH=new T1(1,I_fromInt(-2147483648));continue;}else{var _KL=E(_KI);if(!_KL._){return new T1(0,B(_oc(_KK,_KL.a)));}else{_KH=new T1(1,I_fromInt(_KK));_KI=_KL;continue;}}}else{var _KM=_KJ.a,_KN=E(_KI);return (_KN._==0)?new T1(1,I_mod(_KM,I_fromInt(_KN.a))):new T1(1,I_mod(_KM,_KN.a));}}},_KO=function(_KP,_KQ){if(!B(_qK(_KQ,_pU))){return new F(function(){return _KG(_KP,_KQ);});}else{return E(_nI);}},_KR=function(_KS,_KT){if(!B(_qK(_KT,_pU))){return new F(function(){return _ER(_KS,_KT);});}else{return E(_nI);}},_KU=function(_KV,_KW){if(!B(_qK(_KW,_pU))){var _KX=B(_qS(_KV,_KW));return new T2(0,_KX.a,_KX.b);}else{return E(_nI);}},_KY=function(_KZ){return E(_KZ);},_L0=function(_L1){return E(_L1);},_L2={_:0,a:_uL,b:_F7,c:_pm,d:_uV,e:_EM,f:_FG,g:_L0},_L3=function(_L4,_L5){var _L6=E(_L4);if(!_L6._){var _L7=_L6.a,_L8=E(_L5);return (_L8._==0)?_L7!=_L8.a:(I_compareInt(_L8.a,_L7)==0)?false:true;}else{var _L9=_L6.a,_La=E(_L5);return (_La._==0)?(I_compareInt(_L9,_La.a)==0)?false:true:(I_compare(_L9,_La.a)==0)?false:true;}},_Lb=new T2(0,_qK,_L3),_Lc=function(_Ld,_Le){return (!B(_wo(_Ld,_Le)))?E(_Ld):E(_Le);},_Lf=function(_Lg,_Lh){return (!B(_wo(_Lg,_Lh)))?E(_Lh):E(_Lg);},_Li={_:0,a:_Lb,b:_GQ,c:_Fs,d:_wo,e:_Gh,f:_FT,g:_Lc,h:_Lf},_Lj=function(_Lk){return new T2(0,E(_Lk),E(_oJ));},_Ll=new T3(0,_L2,_Li,_Lj),_Lm={_:0,a:_Ll,b:_Kh,c:_KR,d:_EE,e:_Kq,f:_KO,g:_KU,h:_KC,i:_KY},_Ln=function(_Lo,_Lp){while(1){var _Lq=E(_Lo);if(!_Lq._){return E(_Lp);}else{var _Lr=B(_uL(B(_H2(_Lp,8)),B(_oF(E(_Lq.a)&4294967295))));_Lo=_Lq.b;_Lp=_Lr;continue;}}},_Ls=function(_Lt,_Lu,_Lv){var _Lw=imul(B(_v0(_Lt,0)),8)|0,_Lx=B(_r3(_Lm,Math.pow(2,_Lw-_Lu|0))),_Ly=_Lx.a;return (E(_Lx.b)>=0)?E(B(_HS(B(_HC(B(_Ln(_Lt,_rp)),B(_F7(_Ly,_ro)))),_Lw-_Lv|0)).a):E(B(_HS(B(_HC(B(_Ln(_Lt,_rp)),B(_F7(B(_F7(_Ly,_ro)),_ro)))),_Lw-_Lv|0)).a);},_Lz=new T(function(){return B(unCStr("head"));}),_LA=new T(function(){return B(_ei(_Lz));}),_LB=function(_LC,_LD,_LE){return new T1(1,B(_Ls(_LC,E(_LD),E(_LE))));},_LF=5,_LG=new T(function(){return B(unCStr("Invalid length of floating-point value"));}),_LH=new T(function(){return B(err(_LG));}),_LI=function(_LJ){var _LK=new T(function(){return imul(B(_v0(_LJ,0)),8)|0;}),_LL=new T(function(){var _LM=E(_LK);switch(_LM){case 16:return E(_LF);break;case 32:return E(_Jz);break;default:if(!B(_oc(_LM,32))){var _LN=B(_r3(_JF,4*(Math.log(_LM)/Math.log(2)))),_LO=_LN.a;if(E(_LN.b)<=0){return E(_LO)-13|0;}else{return (E(_LO)+1|0)-13|0;}}else{return E(_LH);}}}),_LP=new T(function(){return 1+E(_LL)|0;});return new T6(0,new T(function(){return B(_v0(_LJ,0));}),new T(function(){var _LQ=E(_LJ);if(!_LQ._){return E(_LA);}else{if((E(_LQ.a)&128)>>>0==128){return 1;}else{return 0;}}}),new T(function(){return B(_oV(new T1(1,B(_Ls(_LJ,1,E(_LP))))));}),new T(function(){return B(_LB(_LJ,_LP,_LK));}),_LL,new T(function(){return B(_iV(_LK,_LP));}));},_LR=function(_LS){var _LT=B(_LI(_LS));return new T6(0,_LT.a,_LT.b,_LT.c,_LT.d,_LT.e,_LT.f);},_LU=function(_LV,_LW,_LX,_LY){var _LZ=B(_fi(_LV,_LW,_LX,_LY)),_M0=_LZ.b;switch(E(_LZ.a)){case 0:var _M1=B(_fo(_LV,_LW,_LX,E(_M0))),_M2=B(_gl(E(_M1.a)&4294967295,_g9,new T3(0,_LV,_LW,_LX),_M1.b));return new T2(0,new T1(0,_M2.a),_M2.b);case 1:var _M3=B(_fo(_LV,_LW,_LX,E(_M0)));return new T2(0,new T1(1,new T(function(){return E(_M3.a)&4294967295;})),_M3.b);case 2:var _M4=B(_J4(_Jz,_LR,new T3(0,_LV,_LW,_LX),_M0));return new T2(0,new T1(2,_M4.a),_M4.b);default:return E(_Jy);}},_M5=function(_M6,_M7){var _M8=E(_M6),_M9=B(_LU(_M8.a,_M8.b,_M8.c,E(_M7)));return new T2(0,_M9.a,_M9.b);},_Ma=function(_Mb){switch(E(_Mb)._){case 0:return E(_dP);case 1:return E(_dP);default:return E(_dP);}},_Mc=new T2(0,_Ma,_M5),_Md=function(_Me){return E(_dP);},_Mf=-4,_Mg=function(_Mh){var _Mi=E(_Mh);return (_Mi._==0)?__Z:new T2(1,new T2(0,_Mf,_Mi.a),new T(function(){return B(_Mg(_Mi.b));}));},_Mj=function(_Mk,_Ml,_Mm,_Mn){var _Mo=B(_fo(_Mk,_Ml,_Mm,_Mn)),_Mp=B(_gl(E(_Mo.a)&4294967295,_kv,new T3(0,_Mk,_Ml,_Mm),_Mo.b)),_Mq=B(_fo(_Mk,_Ml,_Mm,E(_Mp.b))),_Mr=new T(function(){return new T2(0,new T(function(){return B(_Mg(_Mp.a));}),E(_Mq.a)&4294967295);});return new T2(0,_Mr,_Mq.b);},_Ms=function(_Mt,_Mu){var _Mv=E(_Mt),_Mw=B(_Mj(_Mv.a,_Mv.b,_Mv.c,E(_Mu)));return new T2(0,_Mw.a,_Mw.b);},_Mx=function(_My,_Mz,_MA,_MB){var _MC=B(_fi(_My,_Mz,_MA,_MB)),_MD=_MC.b;switch(E(_MC.a)){case 0:var _ME=B(_fo(_My,_Mz,_MA,E(_MD))),_MF=B(_fo(_My,_Mz,_MA,E(_ME.b))),_MG=B(_gl(E(_MF.a)&4294967295,_Ms,new T3(0,_My,_Mz,_MA),_MF.b));return new T2(0,new T(function(){return new T2(0,E(_ME.a)&4294967295,_MG.a);}),_MG.b);case 1:var _MH=B(_fo(_My,_Mz,_MA,E(_MD)));return new T2(0,new T(function(){return new T1(1,E(_MH.a)&4294967295);}),_MH.b);default:return E(_Jy);}},_MI=function(_MJ,_MK){var _ML=E(_MJ),_MM=B(_Mx(_ML.a,_ML.b,_ML.c,E(_MK)));return new T2(0,_MM.a,_MM.b);},_MN=new T(function(){return B(_7f("pgf/PGF/Binary.hs:(243,3)-(244,51)|function put"));}),_MO=function(_MP){switch(E(_MP)._){case 0:return E(_dP);case 1:return E(_dP);default:return E(_MN);}},_MQ=new T2(0,_MO,_MI),_MR=new T0(1),_MS=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_MT=function(_MU){return new F(function(){return err(_MS);});},_MV=new T(function(){return B(_MT(_));}),_MW=function(_MX,_MY,_MZ){var _N0=E(_MZ);if(!_N0._){var _N1=_N0.a,_N2=E(_MY);if(!_N2._){var _N3=_N2.a,_N4=_N2.b;if(_N3<=(imul(3,_N1)|0)){return new T4(0,(1+_N3|0)+_N1|0,E(_MX),E(_N2),E(_N0));}else{var _N5=E(_N2.c);if(!_N5._){var _N6=_N5.a,_N7=E(_N2.d);if(!_N7._){var _N8=_N7.a,_N9=_N7.b,_Na=_N7.c;if(_N8>=(imul(2,_N6)|0)){var _Nb=function(_Nc){var _Nd=E(_N7.d);return (_Nd._==0)?new T4(0,(1+_N3|0)+_N1|0,E(_N9),E(new T4(0,(1+_N6|0)+_Nc|0,E(_N4),E(_N5),E(_Na))),E(new T4(0,(1+_N1|0)+_Nd.a|0,E(_MX),E(_Nd),E(_N0)))):new T4(0,(1+_N3|0)+_N1|0,E(_N9),E(new T4(0,(1+_N6|0)+_Nc|0,E(_N4),E(_N5),E(_Na))),E(new T4(0,1+_N1|0,E(_MX),E(_MR),E(_N0))));},_Ne=E(_Na);if(!_Ne._){return new F(function(){return _Nb(_Ne.a);});}else{return new F(function(){return _Nb(0);});}}else{return new T4(0,(1+_N3|0)+_N1|0,E(_N4),E(_N5),E(new T4(0,(1+_N1|0)+_N8|0,E(_MX),E(_N7),E(_N0))));}}else{return E(_MV);}}else{return E(_MV);}}}else{return new T4(0,1+_N1|0,E(_MX),E(_MR),E(_N0));}}else{var _Nf=E(_MY);if(!_Nf._){var _Ng=_Nf.a,_Nh=_Nf.b,_Ni=_Nf.d,_Nj=E(_Nf.c);if(!_Nj._){var _Nk=_Nj.a,_Nl=E(_Ni);if(!_Nl._){var _Nm=_Nl.a,_Nn=_Nl.b,_No=_Nl.c;if(_Nm>=(imul(2,_Nk)|0)){var _Np=function(_Nq){var _Nr=E(_Nl.d);return (_Nr._==0)?new T4(0,1+_Ng|0,E(_Nn),E(new T4(0,(1+_Nk|0)+_Nq|0,E(_Nh),E(_Nj),E(_No))),E(new T4(0,1+_Nr.a|0,E(_MX),E(_Nr),E(_MR)))):new T4(0,1+_Ng|0,E(_Nn),E(new T4(0,(1+_Nk|0)+_Nq|0,E(_Nh),E(_Nj),E(_No))),E(new T4(0,1,E(_MX),E(_MR),E(_MR))));},_Ns=E(_No);if(!_Ns._){return new F(function(){return _Np(_Ns.a);});}else{return new F(function(){return _Np(0);});}}else{return new T4(0,1+_Ng|0,E(_Nh),E(_Nj),E(new T4(0,1+_Nm|0,E(_MX),E(_Nl),E(_MR))));}}else{return new T4(0,3,E(_Nh),E(_Nj),E(new T4(0,1,E(_MX),E(_MR),E(_MR))));}}else{var _Nt=E(_Ni);return (_Nt._==0)?new T4(0,3,E(_Nt.b),E(new T4(0,1,E(_Nh),E(_MR),E(_MR))),E(new T4(0,1,E(_MX),E(_MR),E(_MR)))):new T4(0,2,E(_MX),E(_Nf),E(_MR));}}else{return new T4(0,1,E(_MX),E(_MR),E(_MR));}}},_Nu=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_Nv=function(_Nw){return new F(function(){return err(_Nu);});},_Nx=new T(function(){return B(_Nv(_));}),_Ny=function(_Nz,_NA,_NB){var _NC=E(_NA);if(!_NC._){var _ND=_NC.a,_NE=E(_NB);if(!_NE._){var _NF=_NE.a,_NG=_NE.b;if(_NF<=(imul(3,_ND)|0)){return new T4(0,(1+_ND|0)+_NF|0,E(_Nz),E(_NC),E(_NE));}else{var _NH=E(_NE.c);if(!_NH._){var _NI=_NH.a,_NJ=_NH.b,_NK=_NH.c,_NL=E(_NE.d);if(!_NL._){var _NM=_NL.a;if(_NI>=(imul(2,_NM)|0)){var _NN=function(_NO){var _NP=E(_Nz),_NQ=E(_NH.d);return (_NQ._==0)?new T4(0,(1+_ND|0)+_NF|0,E(_NJ),E(new T4(0,(1+_ND|0)+_NO|0,E(_NP),E(_NC),E(_NK))),E(new T4(0,(1+_NM|0)+_NQ.a|0,E(_NG),E(_NQ),E(_NL)))):new T4(0,(1+_ND|0)+_NF|0,E(_NJ),E(new T4(0,(1+_ND|0)+_NO|0,E(_NP),E(_NC),E(_NK))),E(new T4(0,1+_NM|0,E(_NG),E(_MR),E(_NL))));},_NR=E(_NK);if(!_NR._){return new F(function(){return _NN(_NR.a);});}else{return new F(function(){return _NN(0);});}}else{return new T4(0,(1+_ND|0)+_NF|0,E(_NG),E(new T4(0,(1+_ND|0)+_NI|0,E(_Nz),E(_NC),E(_NH))),E(_NL));}}else{return E(_Nx);}}else{return E(_Nx);}}}else{return new T4(0,1+_ND|0,E(_Nz),E(_NC),E(_MR));}}else{var _NS=E(_NB);if(!_NS._){var _NT=_NS.a,_NU=_NS.b,_NV=_NS.d,_NW=E(_NS.c);if(!_NW._){var _NX=_NW.a,_NY=_NW.b,_NZ=_NW.c,_O0=E(_NV);if(!_O0._){var _O1=_O0.a;if(_NX>=(imul(2,_O1)|0)){var _O2=function(_O3){var _O4=E(_Nz),_O5=E(_NW.d);return (_O5._==0)?new T4(0,1+_NT|0,E(_NY),E(new T4(0,1+_O3|0,E(_O4),E(_MR),E(_NZ))),E(new T4(0,(1+_O1|0)+_O5.a|0,E(_NU),E(_O5),E(_O0)))):new T4(0,1+_NT|0,E(_NY),E(new T4(0,1+_O3|0,E(_O4),E(_MR),E(_NZ))),E(new T4(0,1+_O1|0,E(_NU),E(_MR),E(_O0))));},_O6=E(_NZ);if(!_O6._){return new F(function(){return _O2(_O6.a);});}else{return new F(function(){return _O2(0);});}}else{return new T4(0,1+_NT|0,E(_NU),E(new T4(0,1+_NX|0,E(_Nz),E(_MR),E(_NW))),E(_O0));}}else{return new T4(0,3,E(_NY),E(new T4(0,1,E(_Nz),E(_MR),E(_MR))),E(new T4(0,1,E(_NU),E(_MR),E(_MR))));}}else{var _O7=E(_NV);return (_O7._==0)?new T4(0,3,E(_NU),E(new T4(0,1,E(_Nz),E(_MR),E(_MR))),E(_O7)):new T4(0,2,E(_Nz),E(_MR),E(_NS));}}else{return new T4(0,1,E(_Nz),E(_MR),E(_MR));}}},_O8=function(_O9){return new T4(0,1,E(_O9),E(_MR),E(_MR));},_Oa=function(_Ob,_Oc){var _Od=E(_Oc);if(!_Od._){return new F(function(){return _MW(_Od.b,B(_Oa(_Ob,_Od.c)),_Od.d);});}else{return new F(function(){return _O8(_Ob);});}},_Oe=function(_Of,_Og){var _Oh=E(_Og);if(!_Oh._){return new F(function(){return _Ny(_Oh.b,_Oh.c,B(_Oe(_Of,_Oh.d)));});}else{return new F(function(){return _O8(_Of);});}},_Oi=function(_Oj,_Ok,_Ol,_Om,_On){return new F(function(){return _Ny(_Ol,_Om,B(_Oe(_Oj,_On)));});},_Oo=function(_Op,_Oq,_Or,_Os,_Ot){return new F(function(){return _MW(_Or,B(_Oa(_Op,_Os)),_Ot);});},_Ou=function(_Ov,_Ow,_Ox,_Oy,_Oz,_OA){var _OB=E(_Ow);if(!_OB._){var _OC=_OB.a,_OD=_OB.b,_OE=_OB.c,_OF=_OB.d;if((imul(3,_OC)|0)>=_Ox){if((imul(3,_Ox)|0)>=_OC){return new T4(0,(_OC+_Ox|0)+1|0,E(_Ov),E(_OB),E(new T4(0,_Ox,E(_Oy),E(_Oz),E(_OA))));}else{return new F(function(){return _Ny(_OD,_OE,B(_Ou(_Ov,_OF,_Ox,_Oy,_Oz,_OA)));});}}else{return new F(function(){return _MW(_Oy,B(_OG(_Ov,_OC,_OD,_OE,_OF,_Oz)),_OA);});}}else{return new F(function(){return _Oo(_Ov,_Ox,_Oy,_Oz,_OA);});}},_OG=function(_OH,_OI,_OJ,_OK,_OL,_OM){var _ON=E(_OM);if(!_ON._){var _OO=_ON.a,_OP=_ON.b,_OQ=_ON.c,_OR=_ON.d;if((imul(3,_OI)|0)>=_OO){if((imul(3,_OO)|0)>=_OI){return new T4(0,(_OI+_OO|0)+1|0,E(_OH),E(new T4(0,_OI,E(_OJ),E(_OK),E(_OL))),E(_ON));}else{return new F(function(){return _Ny(_OJ,_OK,B(_Ou(_OH,_OL,_OO,_OP,_OQ,_OR)));});}}else{return new F(function(){return _MW(_OP,B(_OG(_OH,_OI,_OJ,_OK,_OL,_OQ)),_OR);});}}else{return new F(function(){return _Oi(_OH,_OI,_OJ,_OK,_OL);});}},_OS=function(_OT,_OU,_OV){var _OW=E(_OU);if(!_OW._){var _OX=_OW.a,_OY=_OW.b,_OZ=_OW.c,_P0=_OW.d,_P1=E(_OV);if(!_P1._){var _P2=_P1.a,_P3=_P1.b,_P4=_P1.c,_P5=_P1.d;if((imul(3,_OX)|0)>=_P2){if((imul(3,_P2)|0)>=_OX){return new T4(0,(_OX+_P2|0)+1|0,E(_OT),E(_OW),E(_P1));}else{return new F(function(){return _Ny(_OY,_OZ,B(_Ou(_OT,_P0,_P2,_P3,_P4,_P5)));});}}else{return new F(function(){return _MW(_P3,B(_OG(_OT,_OX,_OY,_OZ,_P0,_P4)),_P5);});}}else{return new F(function(){return _Oi(_OT,_OX,_OY,_OZ,_P0);});}}else{return new F(function(){return _Oa(_OT,_OV);});}},_P6=function(_P7,_P8,_P9){var _Pa=E(_P7);if(_Pa==1){return new T2(0,new T(function(){return new T4(0,1,E(_P8),E(_MR),E(_MR));}),_P9);}else{var _Pb=B(_P6(_Pa>>1,_P8,_P9)),_Pc=_Pb.a,_Pd=E(_Pb.b);if(!_Pd._){return new T2(0,_Pc,_4);}else{var _Pe=B(_Pf(_Pa>>1,_Pd.b));return new T2(0,new T(function(){return B(_OS(_Pd.a,_Pc,_Pe.a));}),_Pe.b);}}},_Pf=function(_Pg,_Ph){var _Pi=E(_Ph);if(!_Pi._){return new T2(0,_MR,_4);}else{var _Pj=_Pi.a,_Pk=_Pi.b,_Pl=E(_Pg);if(_Pl==1){return new T2(0,new T(function(){return new T4(0,1,E(_Pj),E(_MR),E(_MR));}),_Pk);}else{var _Pm=B(_P6(_Pl>>1,_Pj,_Pk)),_Pn=_Pm.a,_Po=E(_Pm.b);if(!_Po._){return new T2(0,_Pn,_4);}else{var _Pp=B(_Pf(_Pl>>1,_Po.b));return new T2(0,new T(function(){return B(_OS(_Po.a,_Pn,_Pp.a));}),_Pp.b);}}}},_Pq=function(_Pr,_Ps,_Pt){while(1){var _Pu=E(_Pt);if(!_Pu._){return E(_Ps);}else{var _Pv=B(_Pf(_Pr,_Pu.b)),_Pw=_Pr<<1,_Px=B(_OS(_Pu.a,_Ps,_Pv.a));_Pr=_Pw;_Ps=_Px;_Pt=_Pv.b;continue;}}},_Py=function(_Pz,_PA,_PB,_PC,_PD){var _PE=B(_fo(_PA,_PB,_PC,_PD)),_PF=B(_gl(E(_PE.a)&4294967295,new T(function(){return B(_jR(_Pz));}),new T3(0,_PA,_PB,_PC),_PE.b));return new T2(0,new T(function(){var _PG=E(_PF.a);if(!_PG._){return new T0(1);}else{return B(_Pq(1,new T4(0,1,E(_PG.a),E(_MR),E(_MR)),_PG.b));}}),_PF.b);},_PH=function(_PI,_PJ){var _PK=E(_PI),_PL=B(_Py(_MQ,_PK.a,_PK.b,_PK.c,E(_PJ)));return new T2(0,_PL.a,_PL.b);},_PM=new T2(0,_Md,_PH),_PN=function(_PO){return E(_dP);},_PP=function(_PQ,_PR,_PS,_PT){var _PU=B(_fo(_PQ,_PR,_PS,_PT));return new F(function(){return _gl(E(_PU.a)&4294967295,_kv,new T3(0,_PQ,_PR,_PS),_PU.b);});},_PV=function(_PW,_PX){var _PY=E(_PW),_PZ=B(_PP(_PY.a,_PY.b,_PY.c,E(_PX)));return new T2(0,_PZ.a,_PZ.b);},_Q0=new T2(0,_PN,_PV),_Q1=new T0(1),_Q2=function(_Q3,_Q4,_Q5,_Q6,_Q7,_Q8,_Q9){while(1){var _Qa=E(_Q9);if(!_Qa._){var _Qb=(_Q7>>>0^_Qa.a>>>0)>>>0,_Qc=(_Qb|_Qb>>>1)>>>0,_Qd=(_Qc|_Qc>>>2)>>>0,_Qe=(_Qd|_Qd>>>4)>>>0,_Qf=(_Qe|_Qe>>>8)>>>0,_Qg=(_Qf|_Qf>>>16)>>>0,_Qh=(_Qg^_Qg>>>1)>>>0&4294967295;if(_Q6>>>0<=_Qh>>>0){return new F(function(){return _Qi(_Q3,_Q4,_Q5,new T3(0,_Q7,E(_Q8),E(_Qa)));});}else{var _Qj=_Qh>>>0,_Qk=(_Q7>>>0&((_Qj-1>>>0^4294967295)>>>0^_Qj)>>>0)>>>0&4294967295,_Ql=new T4(0,_Qk,_Qh,E(_Qa.b),E(_Q8));_Q7=_Qk;_Q8=_Ql;_Q9=_Qa.c;continue;}}else{return new F(function(){return _Qi(_Q3,_Q4,_Q5,new T3(0,_Q7,E(_Q8),E(_Q1)));});}}},_Qm=function(_Qn,_Qo,_Qp){while(1){var _Qq=E(_Qp);if(!_Qq._){var _Qr=_Qq.a,_Qs=_Qq.b,_Qt=_Qq.c,_Qu=(_Qr>>>0^_Qn>>>0)>>>0,_Qv=(_Qu|_Qu>>>1)>>>0,_Qw=(_Qv|_Qv>>>2)>>>0,_Qx=(_Qw|_Qw>>>4)>>>0,_Qy=(_Qx|_Qx>>>8)>>>0,_Qz=(_Qy|_Qy>>>16)>>>0,_QA=(_Qz^_Qz>>>1)>>>0&4294967295,_QB=(_Qn>>>0^_Qr>>>0)>>>0,_QC=(_QB|_QB>>>1)>>>0,_QD=(_QC|_QC>>>2)>>>0,_QE=(_QD|_QD>>>4)>>>0,_QF=(_QE|_QE>>>8)>>>0,_QG=(_QF|_QF>>>16)>>>0,_QH=(_QG^_QG>>>1)>>>0;if(!((_Qr>>>0&_QA>>>0)>>>0)){var _QI=_QA>>>0,_QJ=(_Qn>>>0&((_QH-1>>>0^4294967295)>>>0^_QH)>>>0)>>>0&4294967295,_QK=new T4(0,(_Qr>>>0&((_QI-1>>>0^4294967295)>>>0^_QI)>>>0)>>>0&4294967295,_QA,E(_Qs),E(_Qo));_Qn=_QJ;_Qo=_QK;_Qp=_Qt;continue;}else{var _QL=_QA>>>0,_QJ=(_Qn>>>0&((_QH-1>>>0^4294967295)>>>0^_QH)>>>0)>>>0&4294967295,_QK=new T4(0,(_Qr>>>0&((_QL-1>>>0^4294967295)>>>0^_QL)>>>0)>>>0&4294967295,_QA,E(_Qo),E(_Qs));_Qn=_QJ;_Qo=_QK;_Qp=_Qt;continue;}}else{return E(_Qo);}}},_Qi=function(_QM,_QN,_QO,_QP){var _QQ=E(_QO);if(!_QQ._){return new F(function(){return _Qm(_QM,new T2(1,_QM,_QN),_QP);});}else{var _QR=E(_QQ.a),_QS=E(_QR.a),_QT=(_QM>>>0^_QS>>>0)>>>0,_QU=(_QT|_QT>>>1)>>>0,_QV=(_QU|_QU>>>2)>>>0,_QW=(_QV|_QV>>>4)>>>0,_QX=(_QW|_QW>>>8)>>>0,_QY=(_QX|_QX>>>16)>>>0;return new F(function(){return _Q2(_QS,_QR.b,_QQ.b,(_QY^_QY>>>1)>>>0&4294967295,_QM,new T2(1,_QM,_QN),_QP);});}},_QZ=function(_R0,_R1,_R2,_R3,_R4){var _R5=B(_fo(_R1,_R2,_R3,_R4)),_R6=function(_R7,_R8){var _R9=E(_R7),_Ra=B(_fo(_R9.a,_R9.b,_R9.c,E(_R8))),_Rb=B(A3(_jR,_R0,_R9,_Ra.b));return new T2(0,new T2(0,new T(function(){return E(_Ra.a)&4294967295;}),_Rb.a),_Rb.b);},_Rc=B(_gl(E(_R5.a)&4294967295,_R6,new T3(0,_R1,_R2,_R3),_R5.b));return new T2(0,new T(function(){var _Rd=E(_Rc.a);if(!_Rd._){return new T0(2);}else{var _Re=E(_Rd.a);return B(_Qi(E(_Re.a),_Re.b,_Rd.b,_Q1));}}),_Rc.b);},_Rf=function(_Rg,_Rh,_Ri,_Rj){var _Rk=B(A3(_jR,_Rg,_Ri,_Rj)),_Rl=B(A3(_jR,_Rh,_Ri,_Rk.b));return new T2(0,new T2(0,_Rk.a,_Rl.a),_Rl.b);},_Rm=new T0(1),_Rn=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_Ro=function(_Rp){return new F(function(){return err(_Rn);});},_Rq=new T(function(){return B(_Ro(_));}),_Rr=function(_Rs,_Rt,_Ru,_Rv){var _Rw=E(_Rv);if(!_Rw._){var _Rx=_Rw.a,_Ry=E(_Ru);if(!_Ry._){var _Rz=_Ry.a,_RA=_Ry.b,_RB=_Ry.c;if(_Rz<=(imul(3,_Rx)|0)){return new T5(0,(1+_Rz|0)+_Rx|0,E(_Rs),_Rt,E(_Ry),E(_Rw));}else{var _RC=E(_Ry.d);if(!_RC._){var _RD=_RC.a,_RE=E(_Ry.e);if(!_RE._){var _RF=_RE.a,_RG=_RE.b,_RH=_RE.c,_RI=_RE.d;if(_RF>=(imul(2,_RD)|0)){var _RJ=function(_RK){var _RL=E(_RE.e);return (_RL._==0)?new T5(0,(1+_Rz|0)+_Rx|0,E(_RG),_RH,E(new T5(0,(1+_RD|0)+_RK|0,E(_RA),_RB,E(_RC),E(_RI))),E(new T5(0,(1+_Rx|0)+_RL.a|0,E(_Rs),_Rt,E(_RL),E(_Rw)))):new T5(0,(1+_Rz|0)+_Rx|0,E(_RG),_RH,E(new T5(0,(1+_RD|0)+_RK|0,E(_RA),_RB,E(_RC),E(_RI))),E(new T5(0,1+_Rx|0,E(_Rs),_Rt,E(_Rm),E(_Rw))));},_RM=E(_RI);if(!_RM._){return new F(function(){return _RJ(_RM.a);});}else{return new F(function(){return _RJ(0);});}}else{return new T5(0,(1+_Rz|0)+_Rx|0,E(_RA),_RB,E(_RC),E(new T5(0,(1+_Rx|0)+_RF|0,E(_Rs),_Rt,E(_RE),E(_Rw))));}}else{return E(_Rq);}}else{return E(_Rq);}}}else{return new T5(0,1+_Rx|0,E(_Rs),_Rt,E(_Rm),E(_Rw));}}else{var _RN=E(_Ru);if(!_RN._){var _RO=_RN.a,_RP=_RN.b,_RQ=_RN.c,_RR=_RN.e,_RS=E(_RN.d);if(!_RS._){var _RT=_RS.a,_RU=E(_RR);if(!_RU._){var _RV=_RU.a,_RW=_RU.b,_RX=_RU.c,_RY=_RU.d;if(_RV>=(imul(2,_RT)|0)){var _RZ=function(_S0){var _S1=E(_RU.e);return (_S1._==0)?new T5(0,1+_RO|0,E(_RW),_RX,E(new T5(0,(1+_RT|0)+_S0|0,E(_RP),_RQ,E(_RS),E(_RY))),E(new T5(0,1+_S1.a|0,E(_Rs),_Rt,E(_S1),E(_Rm)))):new T5(0,1+_RO|0,E(_RW),_RX,E(new T5(0,(1+_RT|0)+_S0|0,E(_RP),_RQ,E(_RS),E(_RY))),E(new T5(0,1,E(_Rs),_Rt,E(_Rm),E(_Rm))));},_S2=E(_RY);if(!_S2._){return new F(function(){return _RZ(_S2.a);});}else{return new F(function(){return _RZ(0);});}}else{return new T5(0,1+_RO|0,E(_RP),_RQ,E(_RS),E(new T5(0,1+_RV|0,E(_Rs),_Rt,E(_RU),E(_Rm))));}}else{return new T5(0,3,E(_RP),_RQ,E(_RS),E(new T5(0,1,E(_Rs),_Rt,E(_Rm),E(_Rm))));}}else{var _S3=E(_RR);return (_S3._==0)?new T5(0,3,E(_S3.b),_S3.c,E(new T5(0,1,E(_RP),_RQ,E(_Rm),E(_Rm))),E(new T5(0,1,E(_Rs),_Rt,E(_Rm),E(_Rm)))):new T5(0,2,E(_Rs),_Rt,E(_RN),E(_Rm));}}else{return new T5(0,1,E(_Rs),_Rt,E(_Rm),E(_Rm));}}},_S4=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_S5=function(_S6){return new F(function(){return err(_S4);});},_S7=new T(function(){return B(_S5(_));}),_S8=function(_S9,_Sa,_Sb,_Sc){var _Sd=E(_Sb);if(!_Sd._){var _Se=_Sd.a,_Sf=E(_Sc);if(!_Sf._){var _Sg=_Sf.a,_Sh=_Sf.b,_Si=_Sf.c;if(_Sg<=(imul(3,_Se)|0)){return new T5(0,(1+_Se|0)+_Sg|0,E(_S9),_Sa,E(_Sd),E(_Sf));}else{var _Sj=E(_Sf.d);if(!_Sj._){var _Sk=_Sj.a,_Sl=_Sj.b,_Sm=_Sj.c,_Sn=_Sj.d,_So=E(_Sf.e);if(!_So._){var _Sp=_So.a;if(_Sk>=(imul(2,_Sp)|0)){var _Sq=function(_Sr){var _Ss=E(_S9),_St=E(_Sj.e);return (_St._==0)?new T5(0,(1+_Se|0)+_Sg|0,E(_Sl),_Sm,E(new T5(0,(1+_Se|0)+_Sr|0,E(_Ss),_Sa,E(_Sd),E(_Sn))),E(new T5(0,(1+_Sp|0)+_St.a|0,E(_Sh),_Si,E(_St),E(_So)))):new T5(0,(1+_Se|0)+_Sg|0,E(_Sl),_Sm,E(new T5(0,(1+_Se|0)+_Sr|0,E(_Ss),_Sa,E(_Sd),E(_Sn))),E(new T5(0,1+_Sp|0,E(_Sh),_Si,E(_Rm),E(_So))));},_Su=E(_Sn);if(!_Su._){return new F(function(){return _Sq(_Su.a);});}else{return new F(function(){return _Sq(0);});}}else{return new T5(0,(1+_Se|0)+_Sg|0,E(_Sh),_Si,E(new T5(0,(1+_Se|0)+_Sk|0,E(_S9),_Sa,E(_Sd),E(_Sj))),E(_So));}}else{return E(_S7);}}else{return E(_S7);}}}else{return new T5(0,1+_Se|0,E(_S9),_Sa,E(_Sd),E(_Rm));}}else{var _Sv=E(_Sc);if(!_Sv._){var _Sw=_Sv.a,_Sx=_Sv.b,_Sy=_Sv.c,_Sz=_Sv.e,_SA=E(_Sv.d);if(!_SA._){var _SB=_SA.a,_SC=_SA.b,_SD=_SA.c,_SE=_SA.d,_SF=E(_Sz);if(!_SF._){var _SG=_SF.a;if(_SB>=(imul(2,_SG)|0)){var _SH=function(_SI){var _SJ=E(_S9),_SK=E(_SA.e);return (_SK._==0)?new T5(0,1+_Sw|0,E(_SC),_SD,E(new T5(0,1+_SI|0,E(_SJ),_Sa,E(_Rm),E(_SE))),E(new T5(0,(1+_SG|0)+_SK.a|0,E(_Sx),_Sy,E(_SK),E(_SF)))):new T5(0,1+_Sw|0,E(_SC),_SD,E(new T5(0,1+_SI|0,E(_SJ),_Sa,E(_Rm),E(_SE))),E(new T5(0,1+_SG|0,E(_Sx),_Sy,E(_Rm),E(_SF))));},_SL=E(_SE);if(!_SL._){return new F(function(){return _SH(_SL.a);});}else{return new F(function(){return _SH(0);});}}else{return new T5(0,1+_Sw|0,E(_Sx),_Sy,E(new T5(0,1+_SB|0,E(_S9),_Sa,E(_Rm),E(_SA))),E(_SF));}}else{return new T5(0,3,E(_SC),_SD,E(new T5(0,1,E(_S9),_Sa,E(_Rm),E(_Rm))),E(new T5(0,1,E(_Sx),_Sy,E(_Rm),E(_Rm))));}}else{var _SM=E(_Sz);return (_SM._==0)?new T5(0,3,E(_Sx),_Sy,E(new T5(0,1,E(_S9),_Sa,E(_Rm),E(_Rm))),E(_SM)):new T5(0,2,E(_S9),_Sa,E(_Rm),E(_Sv));}}else{return new T5(0,1,E(_S9),_Sa,E(_Rm),E(_Rm));}}},_SN=function(_SO,_SP){return new T5(0,1,E(_SO),_SP,E(_Rm),E(_Rm));},_SQ=function(_SR,_SS,_ST){var _SU=E(_ST);if(!_SU._){return new F(function(){return _S8(_SU.b,_SU.c,_SU.d,B(_SQ(_SR,_SS,_SU.e)));});}else{return new F(function(){return _SN(_SR,_SS);});}},_SV=function(_SW,_SX,_SY){var _SZ=E(_SY);if(!_SZ._){return new F(function(){return _Rr(_SZ.b,_SZ.c,B(_SV(_SW,_SX,_SZ.d)),_SZ.e);});}else{return new F(function(){return _SN(_SW,_SX);});}},_T0=function(_T1,_T2,_T3,_T4,_T5,_T6,_T7){return new F(function(){return _Rr(_T4,_T5,B(_SV(_T1,_T2,_T6)),_T7);});},_T8=function(_T9,_Ta,_Tb,_Tc,_Td,_Te,_Tf,_Tg){var _Th=E(_Tb);if(!_Th._){var _Ti=_Th.a,_Tj=_Th.b,_Tk=_Th.c,_Tl=_Th.d,_Tm=_Th.e;if((imul(3,_Ti)|0)>=_Tc){if((imul(3,_Tc)|0)>=_Ti){return new T5(0,(_Ti+_Tc|0)+1|0,E(_T9),_Ta,E(_Th),E(new T5(0,_Tc,E(_Td),_Te,E(_Tf),E(_Tg))));}else{return new F(function(){return _S8(_Tj,_Tk,_Tl,B(_T8(_T9,_Ta,_Tm,_Tc,_Td,_Te,_Tf,_Tg)));});}}else{return new F(function(){return _Rr(_Td,_Te,B(_Tn(_T9,_Ta,_Ti,_Tj,_Tk,_Tl,_Tm,_Tf)),_Tg);});}}else{return new F(function(){return _T0(_T9,_Ta,_Tc,_Td,_Te,_Tf,_Tg);});}},_Tn=function(_To,_Tp,_Tq,_Tr,_Ts,_Tt,_Tu,_Tv){var _Tw=E(_Tv);if(!_Tw._){var _Tx=_Tw.a,_Ty=_Tw.b,_Tz=_Tw.c,_TA=_Tw.d,_TB=_Tw.e;if((imul(3,_Tq)|0)>=_Tx){if((imul(3,_Tx)|0)>=_Tq){return new T5(0,(_Tq+_Tx|0)+1|0,E(_To),_Tp,E(new T5(0,_Tq,E(_Tr),_Ts,E(_Tt),E(_Tu))),E(_Tw));}else{return new F(function(){return _S8(_Tr,_Ts,_Tt,B(_T8(_To,_Tp,_Tu,_Tx,_Ty,_Tz,_TA,_TB)));});}}else{return new F(function(){return _Rr(_Ty,_Tz,B(_Tn(_To,_Tp,_Tq,_Tr,_Ts,_Tt,_Tu,_TA)),_TB);});}}else{return new F(function(){return _SQ(_To,_Tp,new T5(0,_Tq,E(_Tr),_Ts,E(_Tt),E(_Tu)));});}},_TC=function(_TD,_TE,_TF,_TG){var _TH=E(_TF);if(!_TH._){var _TI=_TH.a,_TJ=_TH.b,_TK=_TH.c,_TL=_TH.d,_TM=_TH.e,_TN=E(_TG);if(!_TN._){var _TO=_TN.a,_TP=_TN.b,_TQ=_TN.c,_TR=_TN.d,_TS=_TN.e;if((imul(3,_TI)|0)>=_TO){if((imul(3,_TO)|0)>=_TI){return new T5(0,(_TI+_TO|0)+1|0,E(_TD),_TE,E(_TH),E(_TN));}else{return new F(function(){return _S8(_TJ,_TK,_TL,B(_T8(_TD,_TE,_TM,_TO,_TP,_TQ,_TR,_TS)));});}}else{return new F(function(){return _Rr(_TP,_TQ,B(_Tn(_TD,_TE,_TI,_TJ,_TK,_TL,_TM,_TR)),_TS);});}}else{return new F(function(){return _SQ(_TD,_TE,_TH);});}}else{return new F(function(){return _SV(_TD,_TE,_TG);});}},_TT=function(_TU,_TV,_TW){var _TX=E(_TU);if(_TX==1){var _TY=E(_TV);return new T2(0,new T(function(){return new T5(0,1,E(_TY.a),_TY.b,E(_Rm),E(_Rm));}),_TW);}else{var _TZ=B(_TT(_TX>>1,_TV,_TW)),_U0=_TZ.a,_U1=E(_TZ.b);if(!_U1._){return new T2(0,_U0,_4);}else{var _U2=E(_U1.a),_U3=B(_U4(_TX>>1,_U1.b));return new T2(0,new T(function(){return B(_TC(_U2.a,_U2.b,_U0,_U3.a));}),_U3.b);}}},_U4=function(_U5,_U6){var _U7=E(_U6);if(!_U7._){return new T2(0,_Rm,_4);}else{var _U8=_U7.a,_U9=_U7.b,_Ua=E(_U5);if(_Ua==1){var _Ub=E(_U8);return new T2(0,new T(function(){return new T5(0,1,E(_Ub.a),_Ub.b,E(_Rm),E(_Rm));}),_U9);}else{var _Uc=B(_TT(_Ua>>1,_U8,_U9)),_Ud=_Uc.a,_Ue=E(_Uc.b);if(!_Ue._){return new T2(0,_Ud,_4);}else{var _Uf=E(_Ue.a),_Ug=B(_U4(_Ua>>1,_Ue.b));return new T2(0,new T(function(){return B(_TC(_Uf.a,_Uf.b,_Ud,_Ug.a));}),_Ug.b);}}}},_Uh=function(_Ui,_Uj,_Uk){while(1){var _Ul=E(_Uk);if(!_Ul._){return E(_Uj);}else{var _Um=E(_Ul.a),_Un=B(_U4(_Ui,_Ul.b)),_Uo=_Ui<<1,_Up=B(_TC(_Um.a,_Um.b,_Uj,_Un.a));_Ui=_Uo;_Uj=_Up;_Uk=_Un.b;continue;}}},_Uq=function(_Ur,_Us,_Ut,_Uu,_Uv,_Uw){var _Ux=B(_fo(_Ut,_Uu,_Uv,_Uw)),_Uy=B(_gl(E(_Ux.a)&4294967295,function(_Uz,_UA){return new F(function(){return _Rf(_Ur,_Us,_Uz,_UA);});},new T3(0,_Ut,_Uu,_Uv),_Ux.b));return new T2(0,new T(function(){var _UB=E(_Uy.a);if(!_UB._){return new T0(1);}else{var _UC=E(_UB.a);return B(_Uh(1,new T5(0,1,E(_UC.a),_UC.b,E(_Rm),E(_Rm)),_UB.b));}}),_Uy.b);},_UD=new T0(2),_UE=new T0(10),_UF=new T0(5),_UG=new T0(9),_UH=new T0(6),_UI=new T0(7),_UJ=new T0(8),_UK=function(_UL,_UM){var _UN=E(_UL),_UO=B(_fo(_UN.a,_UN.b,_UN.c,E(_UM))),_UP=B(_gl(E(_UO.a)&4294967295,_g9,_UN,_UO.b));return new T2(0,_UP.a,_UP.b);},_UQ=function(_UR,_US){var _UT=E(_UR),_UU=_UT.a,_UV=_UT.b,_UW=_UT.c,_UX=B(_fo(_UU,_UV,_UW,E(_US))),_UY=B(_gl(E(_UX.a)&4294967295,_UZ,_UT,_UX.b)),_V0=B(_fo(_UU,_UV,_UW,E(_UY.b))),_V1=B(_gl(E(_V0.a)&4294967295,_UK,_UT,_V0.b));return new T2(0,new T2(0,_UY.a,_V1.a),_V1.b);},_V2=function(_V3,_V4,_V5,_V6){var _V7=B(_fi(_V3,_V4,_V5,_V6)),_V8=_V7.b;switch(E(_V7.a)){case 0:var _V9=B(_fo(_V3,_V4,_V5,E(_V8))),_Va=B(_fo(_V3,_V4,_V5,E(_V9.b)));return new T2(0,new T(function(){return new T2(0,E(_V9.a)&4294967295,E(_Va.a)&4294967295);}),_Va.b);case 1:var _Vb=B(_fo(_V3,_V4,_V5,E(_V8))),_Vc=B(_fo(_V3,_V4,_V5,E(_Vb.b)));return new T2(0,new T(function(){return new T2(1,E(_Vb.a)&4294967295,E(_Vc.a)&4294967295);}),_Vc.b);case 2:var _Vd=B(_fo(_V3,_V4,_V5,E(_V8))),_Ve=B(_fo(_V3,_V4,_V5,E(_Vd.b)));return new T2(0,new T(function(){return new T2(2,E(_Vd.a)&4294967295,E(_Ve.a)&4294967295);}),_Ve.b);case 3:var _Vf=B(_fo(_V3,_V4,_V5,E(_V8))),_Vg=B(_gl(E(_Vf.a)&4294967295,_g9,new T3(0,_V3,_V4,_V5),_Vf.b));return new T2(0,new T1(3,_Vg.a),_Vg.b);case 4:var _Vh=B(_fo(_V3,_V4,_V5,E(_V8))),_Vi=B(_gl(E(_Vh.a)&4294967295,_UZ,new T3(0,_V3,_V4,_V5),_Vh.b)),_Vj=B(_fo(_V3,_V4,_V5,E(_Vi.b))),_Vk=B(_gl(E(_Vj.a)&4294967295,_UQ,new T3(0,_V3,_V4,_V5),_Vj.b));return new T2(0,new T2(4,_Vi.a,_Vk.a),_Vk.b);case 5:return new T2(0,_UF,_V8);case 6:return new T2(0,_UI,_V8);case 7:return new T2(0,_UH,_V8);case 8:return new T2(0,_UJ,_V8);case 9:return new T2(0,_UG,_V8);case 10:return new T2(0,_UE,_V8);default:return E(_Jy);}},_UZ=function(_Vl,_Vm){var _Vn=E(_Vl),_Vo=B(_V2(_Vn.a,_Vn.b,_Vn.c,E(_Vm)));return new T2(0,_Vo.a,_Vo.b);},_Vp=new T(function(){return B(unCStr("putWord8 not implemented"));}),_Vq=new T(function(){return B(err(_Vp));}),_Vr=function(_Vs){switch(E(_Vs)._){case 0:return E(_dP);case 1:return E(_dP);case 2:return E(_dP);case 3:return E(_dP);case 4:return E(_dP);case 5:return E(_Vq);case 6:return E(_Vq);case 7:return E(_Vq);case 8:return E(_Vq);case 9:return E(_Vq);default:return E(_Vq);}},_Vt=new T2(0,_Vr,_UZ),_Vu=function(_Vv,_Vw){var _Vx=E(_Vv),_Vy=B(_k0(_Vt,_ij,_Vx.a,_Vx.b,_Vx.c,E(_Vw)));return new T2(0,_Vy.a,_Vy.b);},_Vz=new T(function(){return B(unCStr("MArray: undefined array element"));}),_VA=new T(function(){return B(err(_Vz));}),_VB=new T(function(){return B(unCStr("Negative range size"));}),_VC=new T(function(){return B(err(_VB));}),_VD=function(_VE,_VF,_VG,_VH){var _VI=B(_Uq(_fN,_Mc,_VE,_VF,_VG,_VH)),_VJ=B(_Uq(_fN,_gE,_VE,_VF,_VG,E(_VI.b))),_VK=B(_fo(_VE,_VF,_VG,E(_VJ.b))),_VL=E(_VK.a)&4294967295,_VM=B(_jJ(_VL,_Vu,new T3(0,_VE,_VF,_VG),_VK.b)),_VN=B(_k0(_mo,_ij,_VE,_VF,_VG,E(_VM.b))),_VO=B(_QZ(_Q0,_VE,_VF,_VG,E(_VN.b))),_VP=B(_QZ(_Q0,_VE,_VF,_VG,E(_VO.b))),_VQ=B(_QZ(_PM,_VE,_VF,_VG,E(_VP.b))),_VR=B(_Uq(_fN,_ku,_VE,_VF,_VG,E(_VQ.b))),_VS=B(_fo(_VE,_VF,_VG,E(_VR.b))),_VT=new T(function(){var _VU=new T(function(){var _VV=function(_){var _VW=_VL-1|0,_VX=function(_VY){if(_VY>=0){var _VZ=newArr(_VY,_VA),_W0=_VZ,_W1=function(_W2){var _W3=function(_W4,_W5,_){while(1){if(_W4!=_W2){var _W6=E(_W5);if(!_W6._){return _5;}else{var _=_W0[_W4]=_W6.a,_W7=_W4+1|0;_W4=_W7;_W5=_W6.b;continue;}}else{return _5;}}},_W8=B(_W3(0,_VM.a,_));return new T4(0,E(_im),E(_VW),_VY,_W0);};if(0>_VW){return new F(function(){return _W1(0);});}else{var _W9=_VW+1|0;if(_W9>=0){return new F(function(){return _W1(_W9);});}else{return E(_il);}}}else{return E(_VC);}};if(0>_VW){return new F(function(){return _VX(0);});}else{return new F(function(){return _VX(_VW+1|0);});}};return B(_8O(_VV));});return {_:0,a:_VI.a,b:_VJ.a,c:_VN.a,d:_VO.a,e:_VP.a,f:_VU,g:_VQ.a,h:_UD,i:_Rm,j:_VR.a,k:_UD,l:E(_VS.a)&4294967295};});return new T2(0,_VT,_VS.b);},_Wa=function(_Wb,_Wc){var _Wd=E(_Wb),_We=B(_VD(_Wd.a,_Wd.b,_Wd.c,E(_Wc)));return new T2(0,_We.a,_We.b);},_Wf=function(_Wg){return E(_dP);},_Wh=new T2(0,_Wf,_Wa),_Wi=new T2(1,_bX,_4),_Wj=function(_Wk,_Wl){var _Wm=new T(function(){return B(A3(_em,_ec,new T2(1,function(_Wn){return new F(function(){return _bZ(0,_Wl&4294967295,_Wn);});},new T2(1,function(_Wo){return new F(function(){return _bZ(0,E(_Wk)&4294967295,_Wo);});},_4)),_Wi));});return new F(function(){return err(B(unAppCStr("Unsupported PGF version ",new T2(1,_bY,_Wm))));});},_Wp=function(_Wq,_Wr){var _Ws=new T(function(){var _Wt=E(_Wq),_Wu=B(_fi(_Wt.a,_Wt.b,_Wt.c,E(_Wr)));return new T2(0,_Wu.a,_Wu.b);}),_Wv=new T(function(){var _Ww=E(_Wq),_Wx=B(_fi(_Ww.a,_Ww.b,_Ww.c,E(E(_Ws).b)));return new T2(0,_Wx.a,_Wx.b);});return new T2(0,new T(function(){return (E(E(_Ws).a)<<8>>>0&65535|E(E(_Wv).a))>>>0;}),new T(function(){return E(E(_Wv).b);}));},_Wy=function(_Wz){var _WA=E(_Wz);return new T4(0,_WA.a,_WA.b,new T(function(){var _WB=E(_WA.c);if(!_WB._){return __Z;}else{return new T1(1,new T2(0,_WB.a,_4));}}),_WA.d);},_WC=function(_WD){return E(_dP);},_WE=0,_WF=1,_WG=function(_WH,_WI,_WJ,_WK){var _WL=B(_fi(_WH,_WI,_WJ,_WK)),_WM=_WL.b;switch(E(_WL.a)){case 0:var _WN=B(_fi(_WH,_WI,_WJ,E(_WM))),_WO=_WN.b;switch(E(_WN.a)){case 0:var _WP=B(_fz(_WH,_WI,_WJ,E(_WO))),_WQ=B(_WG(_WH,_WI,_WJ,E(_WP.b)));return new T2(0,new T3(0,_WE,_WP.a,_WQ.a),_WQ.b);case 1:var _WR=B(_fz(_WH,_WI,_WJ,E(_WO))),_WS=B(_WG(_WH,_WI,_WJ,E(_WR.b)));return new T2(0,new T3(0,_WF,_WR.a,_WS.a),_WS.b);default:return E(_Jy);}break;case 1:var _WT=B(_WG(_WH,_WI,_WJ,E(_WM))),_WU=B(_WG(_WH,_WI,_WJ,E(_WT.b)));return new T2(0,new T2(1,_WT.a,_WU.a),_WU.b);case 2:var _WV=B(_LU(_WH,_WI,_WJ,E(_WM)));return new T2(0,new T1(2,_WV.a),_WV.b);case 3:var _WW=B(_fo(_WH,_WI,_WJ,E(_WM)));return new T2(0,new T(function(){return new T1(3,E(_WW.a)&4294967295);}),_WW.b);case 4:var _WX=B(_fz(_WH,_WI,_WJ,E(_WM)));return new T2(0,new T1(4,_WX.a),_WX.b);case 5:var _WY=B(_fo(_WH,_WI,_WJ,E(_WM)));return new T2(0,new T(function(){return new T1(5,E(_WY.a)&4294967295);}),_WY.b);case 6:var _WZ=B(_WG(_WH,_WI,_WJ,E(_WM))),_X0=B(_X1(_WH,_WI,_WJ,E(_WZ.b)));return new T2(0,new T2(6,_WZ.a,_X0.a),_X0.b);case 7:var _X2=B(_WG(_WH,_WI,_WJ,E(_WM)));return new T2(0,new T1(7,_X2.a),_X2.b);default:return E(_Jy);}},_X3=function(_X4,_X5){var _X6=E(_X4),_X7=B(_WG(_X6.a,_X6.b,_X6.c,E(_X5)));return new T2(0,_X7.a,_X7.b);},_X8=function(_X9,_Xa){var _Xb=E(_X9),_Xc=_Xb.a,_Xd=_Xb.b,_Xe=_Xb.c,_Xf=B(_fi(_Xc,_Xd,_Xe,E(_Xa))),_Xg=_Xf.b,_Xh=function(_Xi,_Xj){var _Xk=B(_fz(_Xc,_Xd,_Xe,_Xj)),_Xl=B(_X1(_Xc,_Xd,_Xe,E(_Xk.b)));return new T2(0,new T3(0,_Xi,_Xk.a,_Xl.a),_Xl.b);};switch(E(_Xf.a)){case 0:var _Xm=B(_Xh(_WE,E(_Xg)));return new T2(0,_Xm.a,_Xm.b);case 1:var _Xn=B(_Xh(_WF,E(_Xg)));return new T2(0,_Xn.a,_Xn.b);default:return E(_Jy);}},_X1=function(_Xo,_Xp,_Xq,_Xr){var _Xs=B(_fo(_Xo,_Xp,_Xq,_Xr)),_Xt=B(_gl(E(_Xs.a)&4294967295,_X8,new T3(0,_Xo,_Xp,_Xq),_Xs.b)),_Xu=B(_fz(_Xo,_Xp,_Xq,E(_Xt.b))),_Xv=B(_fo(_Xo,_Xp,_Xq,E(_Xu.b))),_Xw=B(_gl(E(_Xv.a)&4294967295,_X3,new T3(0,_Xo,_Xp,_Xq),_Xv.b));return new T2(0,new T3(0,_Xt.a,_Xu.a,_Xw.a),_Xw.b);},_Xx=function(_Xy,_Xz){var _XA=E(_Xy),_XB=_XA.a,_XC=_XA.b,_XD=_XA.c,_XE=B(_fi(_XB,_XC,_XD,E(_Xz))),_XF=_XE.b,_XG=function(_XH,_XI){var _XJ=B(_fz(_XB,_XC,_XD,_XI)),_XK=B(_X1(_XB,_XC,_XD,E(_XJ.b)));return new T2(0,new T3(0,_XH,_XJ.a,_XK.a),_XK.b);};switch(E(_XE.a)){case 0:var _XL=B(_XG(_WE,E(_XF)));return new T2(0,_XL.a,_XL.b);case 1:var _XM=B(_XG(_WF,E(_XF)));return new T2(0,_XM.a,_XM.b);default:return E(_Jy);}},_XN=function(_XO,_XP){var _XQ=B(_J4(_Jz,_LR,_XO,_XP)),_XR=E(_XO),_XS=B(_fz(_XR.a,_XR.b,_XR.c,E(_XQ.b)));return new T2(0,new T2(0,_XQ.a,_XS.a),_XS.b);},_XT=function(_XU,_XV,_XW,_XX){var _XY=B(_fo(_XU,_XV,_XW,_XX)),_XZ=B(_gl(E(_XY.a)&4294967295,_Xx,new T3(0,_XU,_XV,_XW),_XY.b)),_Y0=B(_fo(_XU,_XV,_XW,E(_XZ.b))),_Y1=B(_gl(E(_Y0.a)&4294967295,_XN,new T3(0,_XU,_XV,_XW),_Y0.b)),_Y2=B(_J4(_Jz,_LR,new T3(0,_XU,_XV,_XW),_Y1.b));return new T2(0,new T3(0,_XZ.a,_Y1.a,_Y2.a),_Y2.b);},_Y3=function(_Y4,_Y5){var _Y6=E(_Y4),_Y7=B(_XT(_Y6.a,_Y6.b,_Y6.c,E(_Y5)));return new T2(0,_Y7.a,_Y7.b);},_Y8=new T2(0,_WC,_Y3),_Y9=function(_Ya){return E(_dP);},_Yb=new T0(4),_Yc=function(_Yd,_Ye,_Yf){switch(E(_Yd)){case 0:var _Yg=E(_Ye),_Yh=_Yg.a,_Yi=_Yg.b,_Yj=_Yg.c,_Yk=B(_fz(_Yh,_Yi,_Yj,E(_Yf))),_Yl=B(_fo(_Yh,_Yi,_Yj,E(_Yk.b))),_Ym=B(_gl(E(_Yl.a)&4294967295,_Yn,_Yg,_Yl.b));return new T2(0,new T2(0,_Yk.a,_Ym.a),_Ym.b);case 1:var _Yo=E(_Ye),_Yp=B(_fz(_Yo.a,_Yo.b,_Yo.c,E(_Yf)));return new T2(0,new T1(2,_Yp.a),_Yp.b);case 2:var _Yq=E(_Ye),_Yr=_Yq.a,_Ys=_Yq.b,_Yt=_Yq.c,_Yu=B(_fz(_Yr,_Ys,_Yt,E(_Yf))),_Yv=B(_fi(_Yr,_Ys,_Yt,E(_Yu.b))),_Yw=B(_Yc(E(_Yv.a),_Yq,_Yv.b));return new T2(0,new T2(3,_Yu.a,_Yw.a),_Yw.b);case 3:return new T2(0,_Yb,_Yf);case 4:var _Yx=E(_Ye),_Yy=B(_LU(_Yx.a,_Yx.b,_Yx.c,E(_Yf)));return new T2(0,new T1(1,_Yy.a),_Yy.b);case 5:var _Yz=E(_Ye),_YA=B(_fi(_Yz.a,_Yz.b,_Yz.c,E(_Yf))),_YB=B(_Yc(E(_YA.a),_Yz,_YA.b));return new T2(0,new T1(5,_YB.a),_YB.b);case 6:var _YC=E(_Ye),_YD=B(_WG(_YC.a,_YC.b,_YC.c,E(_Yf)));return new T2(0,new T1(6,_YD.a),_YD.b);default:return E(_Jy);}},_YE=function(_YF,_YG,_YH,_YI){var _YJ=B(_fi(_YF,_YG,_YH,_YI));return new F(function(){return _Yc(E(_YJ.a),new T3(0,_YF,_YG,_YH),_YJ.b);});},_Yn=function(_YK,_YL){var _YM=E(_YK),_YN=B(_YE(_YM.a,_YM.b,_YM.c,E(_YL)));return new T2(0,_YN.a,_YN.b);},_YO=function(_YP,_YQ,_YR,_YS){var _YT=B(_fo(_YP,_YQ,_YR,_YS)),_YU=B(_gl(E(_YT.a)&4294967295,_Yn,new T3(0,_YP,_YQ,_YR),_YT.b)),_YV=B(_WG(_YP,_YQ,_YR,E(_YU.b)));return new T2(0,new T2(0,_YU.a,_YV.a),_YV.b);},_YW=function(_YX,_YY){var _YZ=E(_YX),_Z0=B(_YO(_YZ.a,_YZ.b,_YZ.c,E(_YY)));return new T2(0,_Z0.a,_Z0.b);},_Z1=function(_Z2,_Z3,_Z4,_Z5){var _Z6=B(_X1(_Z2,_Z3,_Z4,_Z5)),_Z7=_Z6.a,_Z8=B(_fo(_Z2,_Z3,_Z4,E(_Z6.b))),_Z9=_Z8.a,_Za=B(_fi(_Z2,_Z3,_Z4,E(_Z8.b))),_Zb=_Za.b;if(!E(_Za.a)){var _Zc=B(_J4(_Jz,_LR,new T3(0,_Z2,_Z3,_Z4),_Zb));return new T2(0,new T4(0,_Z7,new T(function(){return E(_Z9)&4294967295;}),_4l,_Zc.a),_Zc.b);}else{var _Zd=B(_fo(_Z2,_Z3,_Z4,E(_Zb))),_Ze=B(_gl(E(_Zd.a)&4294967295,_YW,new T3(0,_Z2,_Z3,_Z4),_Zd.b)),_Zf=B(_J4(_Jz,_LR,new T3(0,_Z2,_Z3,_Z4),_Ze.b));return new T2(0,new T4(0,_Z7,new T(function(){return E(_Z9)&4294967295;}),new T1(1,_Ze.a),_Zf.a),_Zf.b);}},_Zg=function(_Zh,_Zi){var _Zj=E(_Zh),_Zk=B(_Z1(_Zj.a,_Zj.b,_Zj.c,E(_Zi)));return new T2(0,_Zk.a,_Zk.b);},_Zl=new T2(0,_Y9,_Zg),_Zm=function(_Zn,_Zo){var _Zp=E(_Zo);return (_Zp._==0)?new T5(0,_Zp.a,E(_Zp.b),new T(function(){return B(A1(_Zn,_Zp.c));}),E(B(_Zm(_Zn,_Zp.d))),E(B(_Zm(_Zn,_Zp.e)))):new T0(1);},_Zq=function(_Zr,_Zs,_Zt,_Zu){var _Zv=B(_Uq(_fN,_Mc,_Zr,_Zs,_Zt,_Zu)),_Zw=B(_Uq(_fN,_Zl,_Zr,_Zs,_Zt,E(_Zv.b))),_Zx=B(_Uq(_fN,_Y8,_Zr,_Zs,_Zt,E(_Zw.b)));return new T2(0,new T3(0,_Zv.a,new T(function(){return B(_Zm(_Wy,_Zw.a));}),_Zx.a),_Zx.b);},_Zy=function(_Zz,_ZA,_ZB){var _ZC=E(_Zz);if(!_ZC._){return new T2(0,_4,_ZB);}else{var _ZD=new T(function(){return B(A2(_ZC.a,_ZA,_ZB));}),_ZE=B(_Zy(_ZC.b,_ZA,new T(function(){return E(E(_ZD).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_ZD).a);}),_ZE.a),_ZE.b);}},_ZF=function(_ZG,_ZH,_ZI,_ZJ){if(0>=_ZG){return new F(function(){return _Zy(_4,_ZI,_ZJ);});}else{var _ZK=function(_ZL){var _ZM=E(_ZL);return (_ZM==1)?E(new T2(1,_ZH,_4)):new T2(1,_ZH,new T(function(){return B(_ZK(_ZM-1|0));}));};return new F(function(){return _Zy(B(_ZK(_ZG)),_ZI,_ZJ);});}},_ZN=function(_ZO,_ZP,_ZQ){var _ZR=new T(function(){var _ZS=E(_ZP),_ZT=B(_fo(_ZS.a,_ZS.b,_ZS.c,E(_ZQ))),_ZU=E(_ZT.a)&4294967295,_ZV=B(_ZF(_ZU,_ZO,_ZS,_ZT.b));return new T2(0,new T2(0,_ZU,_ZV.a),_ZV.b);});return new T2(0,new T(function(){return E(E(E(_ZR).a).b);}),new T(function(){return E(E(_ZR).b);}));},_ZW=function(_ZX,_ZY,_ZZ,_100){var _101=new T(function(){var _102=function(_103,_104){var _105=new T(function(){return B(A2(_ZX,_103,_104));}),_106=B(A2(_ZY,_103,new T(function(){return E(E(_105).b);})));return new T2(0,new T2(0,new T(function(){return E(E(_105).a);}),_106.a),_106.b);},_107=B(_ZN(_102,_ZZ,_100));return new T2(0,_107.a,_107.b);});return new T2(0,new T(function(){var _108=E(E(_101).a);if(!_108._){return new T0(1);}else{var _109=E(_108.a);return B(_Uh(1,new T5(0,1,E(_109.a),_109.b,E(_Rm),E(_Rm)),_108.b));}}),new T(function(){return E(E(_101).b);}));},_10a=new T(function(){return B(unCStr("Prelude.Enum.Bool.toEnum: bad argument"));}),_10b=new T(function(){return B(err(_10a));}),_10c=new T(function(){return B(unCStr(")"));}),_10d=function(_10e){return new F(function(){return err(B(unAppCStr("Unable to read PGF file (",new T(function(){return B(_0(_10e,_10c));}))));});},_10f=new T(function(){return B(unCStr("getLiteral"));}),_10g=new T(function(){return B(_10d(_10f));}),_10h=function(_10i,_10j,_10k,_10l){var _10m=B(_fi(_10i,_10j,_10k,_10l)),_10n=_10m.b;switch(E(_10m.a)){case 0:var _10o=B(_fo(_10i,_10j,_10k,E(_10n))),_10p=B(_gl(E(_10o.a)&4294967295,_g9,new T3(0,_10i,_10j,_10k),_10o.b));return new T2(0,new T1(0,_10p.a),_10p.b);case 1:var _10q=B(_fo(_10i,_10j,_10k,E(_10n)));return new T2(0,new T1(1,new T(function(){return E(_10q.a)&4294967295;})),_10q.b);case 2:var _10r=B(_J4(_Jz,_LR,new T3(0,_10i,_10j,_10k),_10n));return new T2(0,new T1(2,_10r.a),_10r.b);default:return E(_10g);}},_10s=new T(function(){return B(unCStr("getBindType"));}),_10t=new T(function(){return B(_10d(_10s));}),_10u=new T(function(){return B(unCStr("getExpr"));}),_10v=new T(function(){return B(_10d(_10u));}),_10w=function(_10x,_10y,_10z,_10A){var _10B=B(_fi(_10x,_10y,_10z,_10A)),_10C=_10B.b;switch(E(_10B.a)){case 0:var _10D=B(_fi(_10x,_10y,_10z,E(_10C))),_10E=_10D.b;switch(E(_10D.a)){case 0:var _10F=B(_fz(_10x,_10y,_10z,E(_10E))),_10G=B(_10w(_10x,_10y,_10z,E(_10F.b)));return new T2(0,new T3(0,_WE,_10F.a,_10G.a),_10G.b);case 1:var _10H=B(_fz(_10x,_10y,_10z,E(_10E))),_10I=B(_10w(_10x,_10y,_10z,E(_10H.b)));return new T2(0,new T3(0,_WF,_10H.a,_10I.a),_10I.b);default:return E(_10t);}break;case 1:var _10J=B(_10w(_10x,_10y,_10z,E(_10C))),_10K=B(_10w(_10x,_10y,_10z,E(_10J.b)));return new T2(0,new T2(1,_10J.a,_10K.a),_10K.b);case 2:var _10L=B(_10h(_10x,_10y,_10z,E(_10C)));return new T2(0,new T1(2,_10L.a),_10L.b);case 3:var _10M=B(_fo(_10x,_10y,_10z,E(_10C)));return new T2(0,new T(function(){return new T1(3,E(_10M.a)&4294967295);}),_10M.b);case 4:var _10N=B(_fz(_10x,_10y,_10z,E(_10C)));return new T2(0,new T1(4,_10N.a),_10N.b);case 5:var _10O=B(_fo(_10x,_10y,_10z,E(_10C)));return new T2(0,new T(function(){return new T1(5,E(_10O.a)&4294967295);}),_10O.b);case 6:var _10P=B(_10w(_10x,_10y,_10z,E(_10C))),_10Q=B(_10R(_10x,_10y,_10z,_10P.b));return new T2(0,new T2(6,_10P.a,_10Q.a),_10Q.b);case 7:var _10S=B(_10w(_10x,_10y,_10z,E(_10C)));return new T2(0,new T1(7,_10S.a),_10S.b);default:return E(_10v);}},_10T=function(_10U,_10V){var _10W=E(_10U),_10X=B(_10w(_10W.a,_10W.b,_10W.c,E(_10V)));return new T2(0,_10X.a,_10X.b);},_10Y=function(_10Z,_110,_111,_112){var _113=B(_fi(_10Z,_110,_111,_112)),_114=_113.b;switch(E(_113.a)){case 0:var _115=B(_fz(_10Z,_110,_111,E(_114))),_116=B(_10R(_10Z,_110,_111,_115.b));return new T2(0,new T3(0,_WE,_115.a,_116.a),_116.b);case 1:var _117=B(_fz(_10Z,_110,_111,E(_114))),_118=B(_10R(_10Z,_110,_111,_117.b));return new T2(0,new T3(0,_WF,_117.a,_118.a),_118.b);default:return E(_10t);}},_119=function(_11a,_11b){var _11c=E(_11a),_11d=B(_10Y(_11c.a,_11c.b,_11c.c,E(_11b)));return new T2(0,_11d.a,_11d.b);},_10R=function(_11e,_11f,_11g,_11h){var _11i=new T3(0,_11e,_11f,_11g),_11j=B(_ZN(_119,_11i,_11h)),_11k=B(_fz(_11e,_11f,_11g,E(_11j.b))),_11l=B(_ZN(_10T,_11i,_11k.b));return new T2(0,new T3(0,_11j.a,_11k.a,_11l.a),_11l.b);},_11m=new T(function(){return B(unCStr("getPatt"));}),_11n=new T(function(){return B(_10d(_11m));}),_11o=function(_11p,_11q,_11r,_11s){var _11t=B(_fi(_11p,_11q,_11r,_11s)),_11u=_11t.b;switch(E(_11t.a)){case 0:var _11v=B(_fz(_11p,_11q,_11r,E(_11u))),_11w=B(_ZN(_11x,new T3(0,_11p,_11q,_11r),_11v.b));return new T2(0,new T2(0,_11v.a,_11w.a),_11w.b);case 1:var _11y=B(_fz(_11p,_11q,_11r,E(_11u)));return new T2(0,new T1(2,_11y.a),_11y.b);case 2:var _11z=B(_fz(_11p,_11q,_11r,E(_11u))),_11A=B(_11o(_11p,_11q,_11r,E(_11z.b)));return new T2(0,new T2(3,_11z.a,_11A.a),_11A.b);case 3:return new T2(0,_Yb,_11u);case 4:var _11B=B(_10h(_11p,_11q,_11r,E(_11u)));return new T2(0,new T1(1,_11B.a),_11B.b);case 5:var _11C=B(_11o(_11p,_11q,_11r,E(_11u)));return new T2(0,new T1(5,_11C.a),_11C.b);case 6:var _11D=B(_10w(_11p,_11q,_11r,E(_11u)));return new T2(0,new T1(6,_11D.a),_11D.b);default:return E(_11n);}},_11x=function(_11E,_11F){var _11G=E(_11E),_11H=B(_11o(_11G.a,_11G.b,_11G.c,E(_11F)));return new T2(0,_11H.a,_11H.b);},_11I=function(_11J,_11K){var _11L=E(_11J),_11M=B(_ZN(_11x,_11L,_11K)),_11N=B(_10w(_11L.a,_11L.b,_11L.c,E(_11M.b)));return new T2(0,new T2(0,_11M.a,_11N.a),_11N.b);},_11O=function(_11P,_11Q,_11R,_11S){var _11T=B(_10R(_11P,_11Q,_11R,_11S)),_11U=_11T.a,_11V=B(_fo(_11P,_11Q,_11R,E(_11T.b))),_11W=_11V.a,_11X=B(_fi(_11P,_11Q,_11R,E(_11V.b))),_11Y=_11X.b;switch(E(_11X.a)&4294967295){case 0:var _11Z=B(_J4(_Jz,_LR,new T3(0,_11P,_11Q,_11R),_11Y));return new T2(0,new T4(0,_11U,new T(function(){return E(_11W)&4294967295;}),_4l,_11Z.a),_11Z.b);case 1:var _120=new T3(0,_11P,_11Q,_11R),_121=new T(function(){var _122=B(_ZN(_11I,_120,_11Y));return new T2(0,_122.a,_122.b);}),_123=B(_J4(_Jz,_LR,_120,new T(function(){return E(E(_121).b);},1)));return new T2(0,new T4(0,_11U,new T(function(){return E(_11W)&4294967295;}),new T1(1,new T(function(){return E(E(_121).a);})),_123.a),_123.b);default:return E(_10b);}},_124=function(_125,_126){var _127=E(_125),_128=B(_11O(_127.a,_127.b,_127.c,_126));return new T2(0,_128.a,_128.b);},_129=function(_12a,_12b){var _12c=E(_12a),_12d=B(_10h(_12c.a,_12c.b,_12c.c,E(_12b)));return new T2(0,_12d.a,_12d.b);},_12e=function(_12f,_12g){var _12h=E(_12f),_12i=B(_fz(_12h.a,_12h.b,_12h.c,E(_12g)));return new T2(0,_12i.a,_12i.b);},_12j=function(_12k,_12l){while(1){var _12m=E(_12k);if(!_12m._){return (E(_12l)._==0)?1:0;}else{var _12n=E(_12l);if(!_12n._){return 2;}else{var _12o=E(_12m.a),_12p=E(_12n.a);if(_12o!=_12p){return (_12o>_12p)?2:0;}else{_12k=_12m.b;_12l=_12n.b;continue;}}}}},_12q=function(_12r,_12s){return (B(_12j(_12r,_12s))==0)?true:false;},_12t=function(_12u,_12v){return (B(_12j(_12u,_12v))==2)?false:true;},_12w=function(_12x,_12y){return (B(_12j(_12x,_12y))==2)?true:false;},_12z=function(_12A,_12B){return (B(_12j(_12A,_12B))==0)?false:true;},_12C=function(_12D,_12E){return (B(_12j(_12D,_12E))==2)?E(_12D):E(_12E);},_12F=function(_12G,_12H){return (B(_12j(_12G,_12H))==2)?E(_12H):E(_12G);},_12I={_:0,a:_sF,b:_12j,c:_12q,d:_12t,e:_12w,f:_12z,g:_12C,h:_12F},_12J=function(_12K){var _12L=E(_12K)&4294967295;if(_12L>>>0>1114111){return new F(function(){return _fQ(_12L);});}else{return _12L;}},_12M=function(_12N){var _12O=E(_12N);return (_12O._==0)?__Z:new T2(1,new T(function(){return B(_12J(_12O.a));}),new T(function(){return B(_12M(_12O.b));}));},_12P=function(_12Q){var _12R=E(_12Q);return (_12R._==0)?__Z:new T2(1,new T(function(){return B(_12J(_12R.a));}),new T(function(){return B(_12P(_12R.b));}));},_12S=function(_12T,_12U,_12V,_12W,_12X,_12Y){return new F(function(){return _sl(B(_G(_12J,B(_IP(_12T,_12U,_12V)))),B(_G(_12J,B(_IP(_12W,_12X,_12Y)))));});},_12Z=function(_130,_131,_132,_133,_134,_135){return (!B(_12S(_130,_131,_132,_133,_134,_135)))?(B(_12j(B(_12P(new T(function(){return B(_IP(_130,_131,_132));}))),B(_12M(new T(function(){return B(_IP(_133,_134,_135));})))))==2)?2:0:1;},_136=function(_137,_138,_139,_13a,_13b,_13c){var _13d=new T3(0,_138,_139,_13a),_13e=E(_13c);if(!_13e._){var _13f=_13e.c,_13g=_13e.d,_13h=_13e.e,_13i=E(_13e.b);switch(B(_12Z(_138,_139,_13a,_13i.a,_13i.b,_13i.c))){case 0:return new F(function(){return _Rr(_13i,_13f,B(_136(_137,_138,_139,_13a,_13b,_13g)),_13h);});break;case 1:return new T5(0,_13e.a,E(_13d),new T(function(){return B(A3(_137,_13d,_13b,_13f));}),E(_13g),E(_13h));default:return new F(function(){return _S8(_13i,_13f,_13g,B(_136(_137,_138,_139,_13a,_13b,_13h)));});}}else{return new T5(0,1,E(_13d),_13b,E(_Rm),E(_Rm));}},_13j=function(_13k,_13l){var _13m=function(_13n,_13o){while(1){var _13p=E(_13o);if(!_13p._){return E(_13n);}else{var _13q=E(_13p.a),_13r=E(_13q.a),_13s=B(_136(_13k,_13r.a,_13r.b,_13r.c,_13q.b,_13n));_13n=_13s;_13o=_13p.b;continue;}}};return new F(function(){return _13m(_Rm,_13l);});},_13t=function(_13u){return E(E(_13u).b);},_13v=function(_13w,_13x,_13y,_13z){var _13A=E(_13x),_13B=E(_13z);if(!_13B._){var _13C=_13B.b,_13D=_13B.c,_13E=_13B.d,_13F=_13B.e;switch(B(A3(_13t,_13w,_13A,_13C))){case 0:return new F(function(){return _Rr(_13C,_13D,B(_13v(_13w,_13A,_13y,_13E)),_13F);});break;case 1:return new T5(0,_13B.a,E(_13A),_13y,E(_13E),E(_13F));default:return new F(function(){return _S8(_13C,_13D,_13E,B(_13v(_13w,_13A,_13y,_13F)));});}}else{return new T5(0,1,E(_13A),_13y,E(_Rm),E(_Rm));}},_13G=function(_13H,_13I,_13J,_13K){return new F(function(){return _13v(_13H,_13I,_13J,_13K);});},_13L=function(_13M,_13N,_13O,_13P,_13Q){var _13R=E(_13Q),_13S=B(_13T(_13M,_13N,_13O,_13P,_13R.a,_13R.b));return new T2(0,_13S.a,_13S.b);},_13U=function(_13V,_13W,_13X){var _13Y=function(_13Z,_140){while(1){var _141=E(_13Z),_142=E(_140);if(!_142._){switch(B(A3(_13t,_13V,_141,_142.b))){case 0:_13Z=_141;_140=_142.d;continue;case 1:return new T1(1,_142.c);default:_13Z=_141;_140=_142.e;continue;}}else{return __Z;}}};return new F(function(){return _13Y(_13W,_13X);});},_143=function(_144,_145){var _146=E(_144);if(!_146._){return new T2(0,new T1(1,_145),_Rm);}else{var _147=new T(function(){return new T5(0,1,E(_146.a),new T(function(){return B(_148(_146.b,_145));}),E(_Rm),E(_Rm));});return new T2(0,_4l,_147);}},_148=function(_149,_14a){var _14b=B(_143(_149,_14a));return new T2(0,_14b.a,_14b.b);},_13T=function(_14c,_14d,_14e,_14f,_14g,_14h){var _14i=E(_14e);if(!_14i._){var _14j=E(_14g);return (_14j._==0)?new T2(0,new T1(1,_14f),_14h):new T2(0,new T1(1,new T(function(){return B(A2(_14d,_14f,_14j.a));})),_14h);}else{var _14k=_14i.a,_14l=_14i.b,_14m=B(_13U(_14c,_14k,_14h));if(!_14m._){var _14n=new T(function(){return B(_13G(_14c,_14k,new T(function(){return B(_148(_14l,_14f));}),_14h));});return new T2(0,_14g,_14n);}else{var _14o=new T(function(){return B(_13G(_14c,_14k,new T(function(){return B(_13L(_14c,_14d,_14l,_14f,_14m.a));}),_14h));});return new T2(0,_14g,_14o);}}},_14p=function(_14q,_14r,_14s){var _14t=function(_14u,_14v,_14w){while(1){var _14x=E(_14u);if(!_14x._){return new T2(0,_14v,_14w);}else{var _14y=E(_14x.a),_14z=B(_13T(_14q,_14r,_14y.a,_14y.b,_14v,_14w));_14u=_14x.b;_14v=_14z.a;_14w=_14z.b;continue;}}};return new F(function(){return _14t(_14s,_4l,_Rm);});},_14A=function(_14B,_14C,_14D){var _14E=E(_14D);switch(_14E._){case 0:var _14F=_14E.a,_14G=_14E.b,_14H=_14E.c,_14I=_14E.d,_14J=_14G>>>0;if(((_14B>>>0&((_14J-1>>>0^4294967295)>>>0^_14J)>>>0)>>>0&4294967295)==_14F){return ((_14B>>>0&_14J)>>>0==0)?new T4(0,_14F,_14G,E(B(_14A(_14B,_14C,_14H))),E(_14I)):new T4(0,_14F,_14G,E(_14H),E(B(_14A(_14B,_14C,_14I))));}else{var _14K=(_14B>>>0^_14F>>>0)>>>0,_14L=(_14K|_14K>>>1)>>>0,_14M=(_14L|_14L>>>2)>>>0,_14N=(_14M|_14M>>>4)>>>0,_14O=(_14N|_14N>>>8)>>>0,_14P=(_14O|_14O>>>16)>>>0,_14Q=(_14P^_14P>>>1)>>>0&4294967295,_14R=_14Q>>>0;return ((_14B>>>0&_14R)>>>0==0)?new T4(0,(_14B>>>0&((_14R-1>>>0^4294967295)>>>0^_14R)>>>0)>>>0&4294967295,_14Q,E(new T2(1,_14B,_14C)),E(_14E)):new T4(0,(_14B>>>0&((_14R-1>>>0^4294967295)>>>0^_14R)>>>0)>>>0&4294967295,_14Q,E(_14E),E(new T2(1,_14B,_14C)));}break;case 1:var _14S=_14E.a;if(_14B!=_14S){var _14T=(_14B>>>0^_14S>>>0)>>>0,_14U=(_14T|_14T>>>1)>>>0,_14V=(_14U|_14U>>>2)>>>0,_14W=(_14V|_14V>>>4)>>>0,_14X=(_14W|_14W>>>8)>>>0,_14Y=(_14X|_14X>>>16)>>>0,_14Z=(_14Y^_14Y>>>1)>>>0&4294967295,_150=_14Z>>>0;return ((_14B>>>0&_150)>>>0==0)?new T4(0,(_14B>>>0&((_150-1>>>0^4294967295)>>>0^_150)>>>0)>>>0&4294967295,_14Z,E(new T2(1,_14B,_14C)),E(_14E)):new T4(0,(_14B>>>0&((_150-1>>>0^4294967295)>>>0^_150)>>>0)>>>0&4294967295,_14Z,E(_14E),E(new T2(1,_14B,_14C)));}else{return new T2(1,_14B,_14C);}break;default:return new T2(1,_14B,_14C);}},_151=function(_152,_153){var _154=function(_155){while(1){var _156=E(_155);switch(_156._){case 0:var _157=_156.b>>>0;if(((_152>>>0&((_157-1>>>0^4294967295)>>>0^_157)>>>0)>>>0&4294967295)==_156.a){if(!((_152>>>0&_157)>>>0)){_155=_156.c;continue;}else{_155=_156.d;continue;}}else{return __Z;}break;case 1:return (_152!=_156.a)?__Z:new T1(1,_156.b);default:return __Z;}}};return new F(function(){return _154(_153);});},_158=function(_159,_15a,_15b,_15c){var _15d=E(_15c);if(!_15d._){var _15e=new T(function(){var _15f=B(_158(_15d.a,_15d.b,_15d.c,_15d.d));return new T2(0,_15f.a,_15f.b);});return new T2(0,new T(function(){return E(E(_15e).a);}),new T(function(){return B(_MW(_15a,_15b,E(_15e).b));}));}else{return new T2(0,_15a,_15b);}},_15g=function(_15h,_15i,_15j,_15k){var _15l=E(_15j);if(!_15l._){var _15m=new T(function(){var _15n=B(_15g(_15l.a,_15l.b,_15l.c,_15l.d));return new T2(0,_15n.a,_15n.b);});return new T2(0,new T(function(){return E(E(_15m).a);}),new T(function(){return B(_Ny(_15i,E(_15m).b,_15k));}));}else{return new T2(0,_15i,_15k);}},_15o=function(_15p,_15q){var _15r=E(_15p);if(!_15r._){var _15s=_15r.a,_15t=E(_15q);if(!_15t._){var _15u=_15t.a;if(_15s<=_15u){var _15v=B(_15g(_15u,_15t.b,_15t.c,_15t.d));return new F(function(){return _MW(_15v.a,_15r,_15v.b);});}else{var _15w=B(_158(_15s,_15r.b,_15r.c,_15r.d));return new F(function(){return _Ny(_15w.a,_15w.b,_15t);});}}else{return E(_15r);}}else{return E(_15q);}},_15x=function(_15y,_15z,_15A,_15B,_15C){var _15D=E(_15y);if(!_15D._){var _15E=_15D.a,_15F=_15D.b,_15G=_15D.c,_15H=_15D.d;if((imul(3,_15E)|0)>=_15z){if((imul(3,_15z)|0)>=_15E){return new F(function(){return _15o(_15D,new T4(0,_15z,E(_15A),E(_15B),E(_15C)));});}else{return new F(function(){return _Ny(_15F,_15G,B(_15x(_15H,_15z,_15A,_15B,_15C)));});}}else{return new F(function(){return _MW(_15A,B(_15I(_15E,_15F,_15G,_15H,_15B)),_15C);});}}else{return new T4(0,_15z,E(_15A),E(_15B),E(_15C));}},_15I=function(_15J,_15K,_15L,_15M,_15N){var _15O=E(_15N);if(!_15O._){var _15P=_15O.a,_15Q=_15O.b,_15R=_15O.c,_15S=_15O.d;if((imul(3,_15J)|0)>=_15P){if((imul(3,_15P)|0)>=_15J){return new F(function(){return _15o(new T4(0,_15J,E(_15K),E(_15L),E(_15M)),_15O);});}else{return new F(function(){return _Ny(_15K,_15L,B(_15x(_15M,_15P,_15Q,_15R,_15S)));});}}else{return new F(function(){return _MW(_15Q,B(_15I(_15J,_15K,_15L,_15M,_15R)),_15S);});}}else{return new T4(0,_15J,E(_15K),E(_15L),E(_15M));}},_15T=function(_15U,_15V){var _15W=E(_15U);if(!_15W._){var _15X=_15W.a,_15Y=_15W.b,_15Z=_15W.c,_160=_15W.d,_161=E(_15V);if(!_161._){var _162=_161.a,_163=_161.b,_164=_161.c,_165=_161.d;if((imul(3,_15X)|0)>=_162){if((imul(3,_162)|0)>=_15X){return new F(function(){return _15o(_15W,_161);});}else{return new F(function(){return _Ny(_15Y,_15Z,B(_15x(_160,_162,_163,_164,_165)));});}}else{return new F(function(){return _MW(_163,B(_15I(_15X,_15Y,_15Z,_160,_164)),_165);});}}else{return E(_15W);}}else{return E(_15V);}},_166=function(_167,_168){var _169=E(_168);if(!_169._){var _16a=_169.b,_16b=B(_166(_167,_169.c)),_16c=_16b.a,_16d=_16b.b,_16e=B(_166(_167,_169.d)),_16f=_16e.a,_16g=_16e.b;return (!B(A1(_167,_16a)))?new T2(0,B(_15T(_16c,_16f)),B(_OS(_16a,_16d,_16g))):new T2(0,B(_OS(_16a,_16c,_16f)),B(_15T(_16d,_16g)));}else{return new T2(0,_MR,_MR);}},_16h=function(_16i,_16j,_16k,_16l){var _16m=E(_16k),_16n=B(_16o(_16i,_16j,_16m.a,_16m.b,_16l));return new T2(0,_16n.a,_16n.b);},_16p=function(_16q,_16r,_16s){while(1){var _16t=E(_16s);if(!_16t._){var _16u=_16t.e;switch(B(A3(_13t,_16q,_16r,_16t.b))){case 0:return new T2(0,B(_13U(_16q,_16r,_16t.d)),_16t);case 1:return new T2(0,new T1(1,_16t.c),_16u);default:_16s=_16u;continue;}}else{return new T2(0,_4l,_Rm);}}},_16v=function(_16w){return E(E(_16w).f);},_16x=function(_16y,_16z,_16A){while(1){var _16B=E(_16A);if(!_16B._){if(!B(A3(_16v,_16y,_16B.b,_16z))){return E(_16B);}else{_16A=_16B.d;continue;}}else{return new T0(1);}}},_16C=function(_16D,_16E,_16F,_16G){while(1){var _16H=E(_16G);if(!_16H._){var _16I=_16H.b,_16J=_16H.d,_16K=_16H.e;switch(B(A3(_13t,_16D,_16E,_16I))){case 0:if(!B(A3(_pQ,_16D,_16I,_16F))){_16G=_16J;continue;}else{return new T2(0,B(_13U(_16D,_16E,_16J)),_16H);}break;case 1:return new T2(0,new T1(1,_16H.c),B(_16x(_16D,_16F,_16K)));default:_16G=_16K;continue;}}else{return new T2(0,_4l,_Rm);}}},_16L=function(_16M,_16N,_16O,_16P){var _16Q=E(_16O);if(!_16Q._){return new F(function(){return _16p(_16M,_16N,_16P);});}else{return new F(function(){return _16C(_16M,_16N,_16Q.a,_16P);});}},_16R=__Z,_16S=function(_16T,_16U,_16V){var _16W=E(_16U);if(!_16W._){return E(_16V);}else{var _16X=function(_16Y,_16Z){while(1){var _170=E(_16Z);if(!_170._){var _171=_170.b,_172=_170.e;switch(B(A3(_13t,_16T,_16Y,_171))){case 0:return new F(function(){return _TC(_171,_170.c,B(_16X(_16Y,_170.d)),_172);});break;case 1:return E(_172);default:_16Z=_172;continue;}}else{return new T0(1);}}};return new F(function(){return _16X(_16W.a,_16V);});}},_173=function(_174,_175,_176){var _177=E(_175);if(!_177._){return E(_176);}else{var _178=function(_179,_17a){while(1){var _17b=E(_17a);if(!_17b._){var _17c=_17b.b,_17d=_17b.d;switch(B(A3(_13t,_174,_17c,_179))){case 0:return new F(function(){return _TC(_17c,_17b.c,_17d,B(_178(_179,_17b.e)));});break;case 1:return E(_17d);default:_17a=_17d;continue;}}else{return new T0(1);}}};return new F(function(){return _178(_177.a,_176);});}},_17e=function(_17f){return E(E(_17f).d);},_17g=function(_17h,_17i,_17j,_17k){var _17l=E(_17i);if(!_17l._){var _17m=E(_17j);if(!_17m._){return E(_17k);}else{var _17n=function(_17o,_17p){while(1){var _17q=E(_17p);if(!_17q._){if(!B(A3(_16v,_17h,_17q.b,_17o))){return E(_17q);}else{_17p=_17q.d;continue;}}else{return new T0(1);}}};return new F(function(){return _17n(_17m.a,_17k);});}}else{var _17r=_17l.a,_17s=E(_17j);if(!_17s._){var _17t=function(_17u,_17v){while(1){var _17w=E(_17v);if(!_17w._){if(!B(A3(_17e,_17h,_17w.b,_17u))){return E(_17w);}else{_17v=_17w.e;continue;}}else{return new T0(1);}}};return new F(function(){return _17t(_17r,_17k);});}else{var _17x=function(_17y,_17z,_17A){while(1){var _17B=E(_17A);if(!_17B._){var _17C=_17B.b;if(!B(A3(_17e,_17h,_17C,_17y))){if(!B(A3(_16v,_17h,_17C,_17z))){return E(_17B);}else{_17A=_17B.d;continue;}}else{_17A=_17B.e;continue;}}else{return new T0(1);}}};return new F(function(){return _17x(_17r,_17s.a,_17k);});}}},_17D=function(_17E,_17F,_17G,_17H){var _17I=E(_17G);if(!_17I._){var _17J=E(_17H);if(!_17J._){var _17K=function(_17L,_17M,_17N,_17O){var _17P=E(_17O);if(!_17P._){var _17Q=E(_17N);if(!_17Q._){var _17R=_17Q.b,_17S=_17Q.c,_17T=_17Q.e,_17U=B(_16L(_17E,_17R,_17M,_17P)),_17V=_17U.b,_17W=new T1(1,E(_17R)),_17X=B(_17K(_17L,_17W,_17Q.d,B(_17g(_17E,_17L,_17W,_17P)))),_17Y=E(_17U.a);if(!_17Y._){return new F(function(){return _TC(_17R,_17S,_17X,B(_17K(_17W,_17M,_17T,_17V)));});}else{return new F(function(){return _TC(_17R,new T(function(){return B(A3(_17F,_17R,_17S,_17Y.a));}),_17X,B(_17K(_17W,_17M,_17T,_17V)));});}}else{return new F(function(){return _TC(_17P.b,_17P.c,B(_16S(_17E,_17L,_17P.d)),B(_173(_17E,_17M,_17P.e)));});}}else{return E(_17N);}},_17Z=_16R,_180=_16R,_181=_17I.a,_182=_17I.b,_183=_17I.c,_184=_17I.d,_185=_17I.e,_186=_17J.a,_187=_17J.b,_188=_17J.c,_189=_17J.d,_18a=_17J.e,_18b=B(_16L(_17E,_182,_180,new T5(0,_186,E(_187),_188,E(_189),E(_18a)))),_18c=_18b.b,_18d=new T1(1,E(_182)),_18e=B(_17K(_17Z,_18d,_184,B(_17g(_17E,_17Z,_18d,new T5(0,_186,E(_187),_188,E(_189),E(_18a)))))),_18f=E(_18b.a);if(!_18f._){return new F(function(){return _TC(_182,_183,_18e,B(_17K(_18d,_180,_185,_18c)));});}else{return new F(function(){return _TC(_182,new T(function(){return B(A3(_17F,_182,_183,_18f.a));}),_18e,B(_17K(_18d,_180,_185,_18c)));});}}else{return E(_17I);}}else{return E(_17H);}},_16o=function(_18g,_18h,_18i,_18j,_18k){var _18l=E(_18k),_18m=_18l.a,_18n=new T(function(){return B(_17D(_18g,function(_18o,_18p,_18q){return new F(function(){return _16h(_18g,_18h,_18p,_18q);});},_18j,_18l.b));}),_18r=new T(function(){var _18s=E(_18i);if(!_18s._){return E(_18m);}else{var _18t=E(_18m);if(!_18t._){return E(_18s);}else{return new T1(1,new T(function(){return B(A2(_18h,_18s.a,_18t.a));}));}}});return new T2(0,_18r,_18n);},_18u=function(_18v,_18w,_18x){var _18y=function(_18z,_18A,_18B){while(1){var _18C=E(_18z);if(!_18C._){return new T2(0,_18A,_18B);}else{var _18D=B(_16o(_18v,_18w,_18A,_18B,_18C.a));_18z=_18C.b;_18A=_18D.a;_18B=_18D.b;continue;}}};return new F(function(){return _18y(_18x,_4l,_Rm);});},_18E=new T0(2),_18F=function(_18G,_18H){var _18I=E(_18G),_18J=E(_18H);return new F(function(){return _12S(_18I.a,_18I.b,_18I.c,_18J.a,_18J.b,_18J.c);});},_18K=function(_18L,_18M){return E(_18L)==E(_18M);},_18N=function(_18O,_18P){var _18Q=E(_18O);switch(_18Q._){case 0:var _18R=E(_18P);if(!_18R._){return new F(function(){return _sl(_18Q.a,_18R.a);});}else{return false;}break;case 1:var _18S=E(_18P);if(_18S._==1){return new F(function(){return _j1(_18Q.a,_18S.a);});}else{return false;}break;default:var _18T=E(_18P);if(_18T._==2){return new F(function(){return _18K(_18Q.a,_18T.a);});}else{return false;}}},_18U=function(_18V,_18W,_18X){while(1){var _18Y=E(_18W);if(!_18Y._){return (E(_18X)._==0)?true:false;}else{var _18Z=E(_18X);if(!_18Z._){return false;}else{if(!B(A3(_pS,_18V,_18Y.a,_18Z.a))){return false;}else{_18W=_18Y.b;_18X=_18Z.b;continue;}}}}},_190=function(_191,_192){return (!B(_193(_191,_192)))?true:false;},_194=new T2(0,_193,_190),_195=new T(function(){return E(_194);}),_196=function(_197,_198){return (E(_197)==0)?(E(_198)==0)?false:true:(E(_198)==0)?true:false;},_199=function(_19a,_19b){return (E(_19a)==0)?(E(_19b)==0)?true:false:(E(_19b)==0)?false:true;},_19c=new T2(0,_199,_196),_19d=new T(function(){return E(_19c);}),_19e=function(_19f,_19g,_19h,_19i,_19j,_19k){if(!B(A3(_pS,_19d,_19f,_19i))){return false;}else{var _19l=E(_19g),_19m=E(_19j);if(!B(_12S(_19l.a,_19l.b,_19l.c,_19m.a,_19m.b,_19m.c))){return false;}else{return new F(function(){return _19n(_19h,_19k);});}}},_19o=function(_19p,_19q){var _19r=E(_19p),_19s=E(_19q);return new F(function(){return _19e(_19r.a,_19r.b,_19r.c,_19s.a,_19s.b,_19s.c);});},_19t=function(_19u,_19v,_19w,_19x,_19y,_19z){if(!B(A3(_pS,_19d,_19u,_19x))){return true;}else{var _19A=E(_19v),_19B=E(_19y);if(!B(_12S(_19A.a,_19A.b,_19A.c,_19B.a,_19B.b,_19B.c))){return true;}else{var _19C=E(_19w);return (!B(_19D(_19C.a,_19C.b,_19C.c,_19z)))?true:false;}}},_19E=function(_19F,_19G){var _19H=E(_19F),_19I=E(_19G);return new F(function(){return _19t(_19H.a,_19H.b,_19H.c,_19I.a,_19I.b,_19I.c);});},_19J=new T(function(){return new T2(0,_19o,_19E);}),_19D=function(_19K,_19L,_19M,_19N){var _19O=E(_19N);if(!B(_18U(_19J,_19K,_19O.a))){return false;}else{var _19P=E(_19L),_19Q=E(_19O.b);if(!B(_12S(_19P.a,_19P.b,_19P.c,_19Q.a,_19Q.b,_19Q.c))){return false;}else{return new F(function(){return _18U(_195,_19M,_19O.c);});}}},_19n=function(_19R,_19S){var _19T=E(_19R);return new F(function(){return _19D(_19T.a,_19T.b,_19T.c,_19S);});},_193=function(_19U,_19V){while(1){var _19W=E(_19U);switch(_19W._){case 0:var _19X=_19W.b,_19Y=_19W.c,_19Z=E(_19V);if(!_19Z._){var _1a0=_19Z.a,_1a1=_19Z.b,_1a2=_19Z.c;if(!E(_19W.a)){if(!E(_1a0)){var _1a3=E(_19X),_1a4=E(_1a1);if(!B(_12S(_1a3.a,_1a3.b,_1a3.c,_1a4.a,_1a4.b,_1a4.c))){return false;}else{_19U=_19Y;_19V=_1a2;continue;}}else{return false;}}else{if(!E(_1a0)){return false;}else{var _1a5=E(_19X),_1a6=E(_1a1);if(!B(_12S(_1a5.a,_1a5.b,_1a5.c,_1a6.a,_1a6.b,_1a6.c))){return false;}else{_19U=_19Y;_19V=_1a2;continue;}}}}else{return false;}break;case 1:var _1a7=E(_19V);if(_1a7._==1){if(!B(_193(_19W.a,_1a7.a))){return false;}else{_19U=_19W.b;_19V=_1a7.b;continue;}}else{return false;}break;case 2:var _1a8=E(_19V);if(_1a8._==2){return new F(function(){return _18N(_19W.a,_1a8.a);});}else{return false;}break;case 3:var _1a9=E(_19V);return (_1a9._==3)?_19W.a==_1a9.a:false;case 4:var _1aa=E(_19V);if(_1aa._==4){return new F(function(){return _18F(_19W.a,_1aa.a);});}else{return false;}break;case 5:var _1ab=E(_19V);return (_1ab._==5)?_19W.a==_1ab.a:false;case 6:var _1ac=E(_19V);if(_1ac._==6){if(!B(_193(_19W.a,_1ac.a))){return false;}else{return new F(function(){return _19n(_19W.b,_1ac.b);});}}else{return false;}break;default:var _1ad=E(_19V);if(_1ad._==7){_19U=_19W.a;_19V=_1ad.a;continue;}else{return false;}}}},_1ae=function(_1af,_1ag,_1ah,_1ai){return (_1af!=_1ah)?true:(E(_1ag)!=E(_1ai))?true:false;},_1aj=function(_1ak,_1al){var _1am=E(_1ak),_1an=E(_1al);return new F(function(){return _1ae(E(_1am.a),_1am.b,E(_1an.a),_1an.b);});},_1ao=function(_1ap,_1aq,_1ar,_1as){if(_1ap!=_1ar){return false;}else{return new F(function(){return _j1(_1aq,_1as);});}},_1at=function(_1au,_1av){var _1aw=E(_1au),_1ax=E(_1av);return new F(function(){return _1ao(E(_1aw.a),_1aw.b,E(_1ax.a),_1ax.b);});},_1ay=new T2(0,_1at,_1aj),_1az=function(_1aA,_1aB,_1aC,_1aD){return (!B(_18U(_1ay,_1aA,_1aC)))?true:(_1aB!=_1aD)?true:false;},_1aE=function(_1aF,_1aG){var _1aH=E(_1aF),_1aI=E(_1aG);return new F(function(){return _1az(_1aH.a,_1aH.b,_1aI.a,_1aI.b);});},_1aJ=function(_1aK,_1aL){var _1aM=E(_1aK),_1aN=E(_1aL);return (!B(_18U(_1ay,_1aM.a,_1aN.a)))?false:_1aM.b==_1aN.b;},_1aO=new T2(0,_1aJ,_1aE),_1aP=function(_1aQ,_1aR){while(1){var _1aS=E(_1aQ);if(!_1aS._){return (E(_1aR)._==0)?true:false;}else{var _1aT=E(_1aR);if(!_1aT._){return false;}else{if(!B(_sx(_1aS.a,_1aT.a))){return false;}else{_1aQ=_1aS.b;_1aR=_1aT.b;continue;}}}}},_1aU=function(_1aV,_1aW){var _1aX=E(_1aV);switch(_1aX._){case 0:var _1aY=E(_1aW);if(!_1aY._){if(_1aX.a!=_1aY.a){return false;}else{return new F(function(){return _18U(_1aO,_1aX.b,_1aY.b);});}}else{return false;}break;case 1:var _1aZ=E(_1aW);return (_1aZ._==1)?_1aX.a==_1aZ.a:false;default:var _1b0=E(_1aW);if(_1b0._==2){var _1b1=E(_1aX.a),_1b2=E(_1b0.a);if(!B(_12S(_1b1.a,_1b1.b,_1b1.c,_1b2.a,_1b2.b,_1b2.c))){return false;}else{if(!B(_193(_1aX.b,_1b0.b))){return false;}else{return new F(function(){return _1aP(_1aX.c,_1b0.c);});}}}else{return false;}}},_1b3=function(_1b4,_1b5){return (!B(_1aU(_1b4,_1b5)))?true:false;},_1b6=new T2(0,_1aU,_1b3),_1b7=function(_1b8,_1b9){var _1ba=E(_1b8),_1bb=E(_1b9);return new F(function(){return _12Z(_1ba.a,_1ba.b,_1ba.c,_1bb.a,_1bb.b,_1bb.c);});},_1bc=function(_1bd,_1be){var _1bf=E(_1bd),_1bg=E(_1be);return (_1bf>=_1bg)?(_1bf!=_1bg)?2:1:0;},_1bh=function(_1bi,_1bj){var _1bk=E(_1bi);switch(_1bk._){case 0:var _1bl=E(_1bj);if(!_1bl._){return new F(function(){return _12j(_1bk.a,_1bl.a);});}else{return 0;}break;case 1:var _1bm=E(_1bj);switch(_1bm._){case 0:return 2;case 1:return new F(function(){return _jl(_1bk.a,_1bm.a);});break;default:return 0;}break;default:var _1bn=E(_1bj);if(_1bn._==2){return new F(function(){return _1bc(_1bk.a,_1bn.a);});}else{return 2;}}},_1bo=function(_1bp,_1bq){return (B(_1br(_1bp,_1bq))==0)?true:false;},_1bs=function(_1bt,_1bu){return (B(_1br(_1bt,_1bu))==2)?false:true;},_1bv=function(_1bw,_1bx){return (B(_1br(_1bw,_1bx))==2)?true:false;},_1by=function(_1bz,_1bA){return (B(_1br(_1bz,_1bA))==0)?false:true;},_1bB=function(_1bC,_1bD){return (B(_1br(_1bC,_1bD))==2)?E(_1bC):E(_1bD);},_1bE=function(_1bF,_1bG){return (B(_1br(_1bF,_1bG))==2)?E(_1bG):E(_1bF);},_1bH={_:0,a:_194,b:_1br,c:_1bo,d:_1bs,e:_1bv,f:_1by,g:_1bB,h:_1bE},_1bI=new T(function(){return E(_1bH);}),_1bJ=function(_1bK,_1bL,_1bM){while(1){var _1bN=E(_1bL);if(!_1bN._){return (E(_1bM)._==0)?1:0;}else{var _1bO=E(_1bM);if(!_1bO._){return 2;}else{var _1bP=B(A3(_13t,_1bK,_1bN.a,_1bO.a));if(_1bP==1){_1bL=_1bN.b;_1bM=_1bO.b;continue;}else{return E(_1bP);}}}}},_1bQ=function(_1bR,_1bS,_1bT,_1bU){var _1bV=E(_1bU);switch(B(_1bJ(_1bW,_1bR,_1bV.a))){case 0:return false;case 1:var _1bX=E(_1bS),_1bY=E(_1bV.b);switch(B(_12Z(_1bX.a,_1bX.b,_1bX.c,_1bY.a,_1bY.b,_1bY.c))){case 0:return false;case 1:return (B(_1bJ(_1bI,_1bT,_1bV.c))==0)?false:true;default:return true;}break;default:return true;}},_1bZ=function(_1c0,_1c1){var _1c2=E(_1c0);return new F(function(){return _1bQ(_1c2.a,_1c2.b,_1c2.c,_1c1);});},_1c3=function(_1c4,_1c5){if(!E(_1c4)){return (E(_1c5)==0)?false:true;}else{var _1c6=E(_1c5);return false;}},_1c7=function(_1c8,_1c9){if(!E(_1c8)){var _1ca=E(_1c9);return true;}else{return (E(_1c9)==0)?false:true;}},_1cb=function(_1cc,_1cd){if(!E(_1cc)){var _1ce=E(_1cd);return false;}else{return (E(_1cd)==0)?true:false;}},_1cf=function(_1cg,_1ch){if(!E(_1cg)){return (E(_1ch)==0)?true:false;}else{var _1ci=E(_1ch);return true;}},_1cj=function(_1ck,_1cl){return (E(_1ck)==0)?(E(_1cl)==0)?1:0:(E(_1cl)==0)?2:1;},_1cm=function(_1cn,_1co){if(!E(_1cn)){return E(_1co);}else{var _1cp=E(_1co);return 1;}},_1cq=function(_1cr,_1cs){if(!E(_1cr)){var _1ct=E(_1cs);return 0;}else{return E(_1cs);}},_1cu={_:0,a:_19c,b:_1cj,c:_1c3,d:_1c7,e:_1cb,f:_1cf,g:_1cm,h:_1cq},_1cv=new T(function(){return E(_1cu);}),_1cw=function(_1cx,_1cy,_1cz,_1cA,_1cB,_1cC){switch(B(A3(_13t,_1cv,_1cx,_1cA))){case 0:return false;case 1:var _1cD=E(_1cy),_1cE=E(_1cB);switch(B(_12Z(_1cD.a,_1cD.b,_1cD.c,_1cE.a,_1cE.b,_1cE.c))){case 0:return false;case 1:return new F(function(){return _1bZ(_1cz,_1cC);});break;default:return true;}break;default:return true;}},_1cF=function(_1cG,_1cH){var _1cI=E(_1cG),_1cJ=E(_1cH);return new F(function(){return _1cw(_1cI.a,_1cI.b,_1cI.c,_1cJ.a,_1cJ.b,_1cJ.c);});},_1cK=function(_1cL,_1cM,_1cN,_1cO){var _1cP=E(_1cO);switch(B(_1bJ(_1bW,_1cL,_1cP.a))){case 0:return false;case 1:var _1cQ=E(_1cM),_1cR=E(_1cP.b);switch(B(_12Z(_1cQ.a,_1cQ.b,_1cQ.c,_1cR.a,_1cR.b,_1cR.c))){case 0:return false;case 1:return (B(_1bJ(_1bI,_1cN,_1cP.c))==2)?true:false;default:return true;}break;default:return true;}},_1cS=function(_1cT,_1cU){var _1cV=E(_1cT);return new F(function(){return _1cK(_1cV.a,_1cV.b,_1cV.c,_1cU);});},_1cW=function(_1cX,_1cY,_1cZ,_1d0,_1d1,_1d2){switch(B(A3(_13t,_1cv,_1cX,_1d0))){case 0:return false;case 1:var _1d3=E(_1cY),_1d4=E(_1d1);switch(B(_12Z(_1d3.a,_1d3.b,_1d3.c,_1d4.a,_1d4.b,_1d4.c))){case 0:return false;case 1:return new F(function(){return _1cS(_1cZ,_1d2);});break;default:return true;}break;default:return true;}},_1d5=function(_1d6,_1d7){var _1d8=E(_1d6),_1d9=E(_1d7);return new F(function(){return _1cW(_1d8.a,_1d8.b,_1d8.c,_1d9.a,_1d9.b,_1d9.c);});},_1da=function(_1db,_1dc,_1dd,_1de){var _1df=E(_1de);switch(B(_1bJ(_1bW,_1db,_1df.a))){case 0:return true;case 1:var _1dg=E(_1dc),_1dh=E(_1df.b);switch(B(_12Z(_1dg.a,_1dg.b,_1dg.c,_1dh.a,_1dh.b,_1dh.c))){case 0:return true;case 1:return (B(_1bJ(_1bI,_1dd,_1df.c))==2)?false:true;default:return false;}break;default:return false;}},_1di=function(_1dj,_1dk){var _1dl=E(_1dj);return new F(function(){return _1da(_1dl.a,_1dl.b,_1dl.c,_1dk);});},_1dm=function(_1dn,_1do,_1dp,_1dq,_1dr,_1ds){switch(B(A3(_13t,_1cv,_1dn,_1dq))){case 0:return true;case 1:var _1dt=E(_1do),_1du=E(_1dr);switch(B(_12Z(_1dt.a,_1dt.b,_1dt.c,_1du.a,_1du.b,_1du.c))){case 0:return true;case 1:return new F(function(){return _1di(_1dp,_1ds);});break;default:return false;}break;default:return false;}},_1dv=function(_1dw,_1dx){var _1dy=E(_1dw),_1dz=E(_1dx);return new F(function(){return _1dm(_1dy.a,_1dy.b,_1dy.c,_1dz.a,_1dz.b,_1dz.c);});},_1dA=function(_1dB,_1dC){var _1dD=E(_1dB),_1dE=_1dD.a,_1dF=_1dD.c,_1dG=E(_1dC),_1dH=_1dG.a,_1dI=_1dG.c;switch(B(A3(_13t,_1cv,_1dE,_1dH))){case 0:return E(_1dG);case 1:var _1dJ=E(_1dD.b),_1dK=E(_1dG.b);switch(B(_12Z(_1dJ.a,_1dJ.b,_1dJ.c,_1dK.a,_1dK.b,_1dK.c))){case 0:return new T3(0,_1dH,_1dK,_1dI);case 1:var _1dL=E(_1dF);return (!B(_1da(_1dL.a,_1dL.b,_1dL.c,_1dI)))?new T3(0,_1dE,_1dJ,_1dL):new T3(0,_1dH,_1dK,_1dI);default:return new T3(0,_1dE,_1dJ,_1dF);}break;default:return E(_1dD);}},_1dM=function(_1dN,_1dO){var _1dP=E(_1dN),_1dQ=_1dP.a,_1dR=_1dP.c,_1dS=E(_1dO),_1dT=_1dS.a,_1dU=_1dS.c;switch(B(A3(_13t,_1cv,_1dQ,_1dT))){case 0:return E(_1dP);case 1:var _1dV=E(_1dP.b),_1dW=E(_1dS.b);switch(B(_12Z(_1dV.a,_1dV.b,_1dV.c,_1dW.a,_1dW.b,_1dW.c))){case 0:return new T3(0,_1dQ,_1dV,_1dR);case 1:var _1dX=E(_1dR);return (!B(_1da(_1dX.a,_1dX.b,_1dX.c,_1dU)))?new T3(0,_1dT,_1dW,_1dU):new T3(0,_1dQ,_1dV,_1dX);default:return new T3(0,_1dT,_1dW,_1dU);}break;default:return E(_1dS);}},_1dY=function(_1dZ,_1e0,_1e1,_1e2){var _1e3=E(_1e2);switch(B(_1bJ(_1bW,_1dZ,_1e3.a))){case 0:return true;case 1:var _1e4=E(_1e0),_1e5=E(_1e3.b);switch(B(_12Z(_1e4.a,_1e4.b,_1e4.c,_1e5.a,_1e5.b,_1e5.c))){case 0:return true;case 1:return (B(_1bJ(_1bI,_1e1,_1e3.c))==0)?true:false;default:return false;}break;default:return false;}},_1e6=function(_1e7,_1e8){var _1e9=E(_1e7);return new F(function(){return _1dY(_1e9.a,_1e9.b,_1e9.c,_1e8);});},_1ea=function(_1eb,_1ec,_1ed,_1ee,_1ef,_1eg){switch(B(A3(_13t,_1cv,_1eb,_1ee))){case 0:return true;case 1:var _1eh=E(_1ec),_1ei=E(_1ef);switch(B(_12Z(_1eh.a,_1eh.b,_1eh.c,_1ei.a,_1ei.b,_1ei.c))){case 0:return true;case 1:return new F(function(){return _1e6(_1ed,_1eg);});break;default:return false;}break;default:return false;}},_1ej=function(_1ek,_1el){var _1em=E(_1ek),_1en=E(_1el);return new F(function(){return _1ea(_1em.a,_1em.b,_1em.c,_1en.a,_1en.b,_1en.c);});},_1eo=function(_1ep,_1eq,_1er,_1es,_1et,_1eu){switch(B(A3(_13t,_1cv,_1ep,_1es))){case 0:return 0;case 1:var _1ev=E(_1eq),_1ew=E(_1et);switch(B(_12Z(_1ev.a,_1ev.b,_1ev.c,_1ew.a,_1ew.b,_1ew.c))){case 0:return 0;case 1:return new F(function(){return _1ex(_1er,_1eu);});break;default:return 2;}break;default:return 2;}},_1ey=function(_1ez,_1eA){var _1eB=E(_1ez),_1eC=E(_1eA);return new F(function(){return _1eo(_1eB.a,_1eB.b,_1eB.c,_1eC.a,_1eC.b,_1eC.c);});},_1bW=new T(function(){return {_:0,a:_19J,b:_1ey,c:_1ej,d:_1dv,e:_1d5,f:_1cF,g:_1dA,h:_1dM};}),_1eD=function(_1eE,_1eF,_1eG,_1eH){var _1eI=E(_1eH);switch(B(_1bJ(_1bW,_1eE,_1eI.a))){case 0:return 0;case 1:var _1eJ=E(_1eF),_1eK=E(_1eI.b);switch(B(_12Z(_1eJ.a,_1eJ.b,_1eJ.c,_1eK.a,_1eK.b,_1eK.c))){case 0:return 0;case 1:return new F(function(){return _1bJ(_1bI,_1eG,_1eI.c);});break;default:return 2;}break;default:return 2;}},_1ex=function(_1eL,_1eM){var _1eN=E(_1eL);return new F(function(){return _1eD(_1eN.a,_1eN.b,_1eN.c,_1eM);});},_1br=function(_1eO,_1eP){while(1){var _1eQ=B((function(_1eR,_1eS){var _1eT=E(_1eR);switch(_1eT._){case 0:var _1eU=E(_1eS);if(!_1eU._){var _1eV=_1eU.a,_1eW=function(_1eX){var _1eY=E(_1eT.b),_1eZ=E(_1eU.b);switch(B(_12Z(_1eY.a,_1eY.b,_1eY.c,_1eZ.a,_1eZ.b,_1eZ.c))){case 0:return 0;case 1:return new F(function(){return _1br(_1eT.c,_1eU.c);});break;default:return 2;}};if(!E(_1eT.a)){if(!E(_1eV)){return new F(function(){return _1eW(_);});}else{return 0;}}else{if(!E(_1eV)){return 2;}else{return new F(function(){return _1eW(_);});}}}else{return 0;}break;case 1:var _1f0=E(_1eS);switch(_1f0._){case 0:return 2;case 1:switch(B(_1br(_1eT.a,_1f0.a))){case 0:return 0;case 1:_1eO=_1eT.b;_1eP=_1f0.b;return __continue;default:return 2;}break;default:return 0;}break;case 2:var _1f1=E(_1eS);switch(_1f1._){case 2:return new F(function(){return _1bh(_1eT.a,_1f1.a);});break;case 3:return 0;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 3:var _1f2=E(_1eS);switch(_1f2._){case 3:return new F(function(){return _ji(_1eT.a,_1f2.a);});break;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 4:var _1f3=E(_1eS);switch(_1f3._){case 4:return new F(function(){return _1b7(_1eT.a,_1f3.a);});break;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 5:var _1f4=E(_1eS);switch(_1f4._){case 5:return new F(function(){return _ji(_1eT.a,_1f4.a);});break;case 6:return 0;case 7:return 0;default:return 2;}break;case 6:var _1f5=E(_1eS);switch(_1f5._){case 6:switch(B(_1br(_1eT.a,_1f5.a))){case 0:return 0;case 1:return new F(function(){return _1ex(_1eT.b,_1f5.b);});break;default:return 2;}break;case 7:return 0;default:return 2;}break;default:var _1f6=E(_1eS);if(_1f6._==7){_1eO=_1eT.a;_1eP=_1f6.a;return __continue;}else{return 2;}}})(_1eO,_1eP));if(_1eQ!=__continue){return _1eQ;}}},_1f7=function(_1f8,_1f9,_1fa,_1fb){if(_1f8>=_1fa){if(_1f8!=_1fa){return 2;}else{return new F(function(){return _jl(_1f9,_1fb);});}}else{return 0;}},_1fc=function(_1fd,_1fe){var _1ff=E(_1fd),_1fg=E(_1fe);return new F(function(){return _1f7(E(_1ff.a),_1ff.b,E(_1fg.a),_1fg.b);});},_1fh=function(_1fi,_1fj,_1fk,_1fl){if(_1fi>=_1fk){if(_1fi!=_1fk){return false;}else{return new F(function(){return _jx(_1fj,_1fl);});}}else{return true;}},_1fm=function(_1fn,_1fo){var _1fp=E(_1fn),_1fq=E(_1fo);return new F(function(){return _1fh(E(_1fp.a),_1fp.b,E(_1fq.a),_1fq.b);});},_1fr=function(_1fs,_1ft,_1fu,_1fv){if(_1fs>=_1fu){if(_1fs!=_1fu){return false;}else{return new F(function(){return _ju(_1ft,_1fv);});}}else{return true;}},_1fw=function(_1fx,_1fy){var _1fz=E(_1fx),_1fA=E(_1fy);return new F(function(){return _1fr(E(_1fz.a),_1fz.b,E(_1fA.a),_1fA.b);});},_1fB=function(_1fC,_1fD,_1fE,_1fF){if(_1fC>=_1fE){if(_1fC!=_1fE){return true;}else{return new F(function(){return _jr(_1fD,_1fF);});}}else{return false;}},_1fG=function(_1fH,_1fI){var _1fJ=E(_1fH),_1fK=E(_1fI);return new F(function(){return _1fB(E(_1fJ.a),_1fJ.b,E(_1fK.a),_1fK.b);});},_1fL=function(_1fM,_1fN,_1fO,_1fP){if(_1fM>=_1fO){if(_1fM!=_1fO){return true;}else{return new F(function(){return _jo(_1fN,_1fP);});}}else{return false;}},_1fQ=function(_1fR,_1fS){var _1fT=E(_1fR),_1fU=E(_1fS);return new F(function(){return _1fL(E(_1fT.a),_1fT.b,E(_1fU.a),_1fU.b);});},_1fV=function(_1fW,_1fX){var _1fY=E(_1fW),_1fZ=E(_1fY.a),_1g0=E(_1fX),_1g1=E(_1g0.a);return (_1fZ>=_1g1)?(_1fZ!=_1g1)?E(_1fY):(E(_1fY.b)>E(_1g0.b))?E(_1fY):E(_1g0):E(_1g0);},_1g2=function(_1g3,_1g4){var _1g5=E(_1g3),_1g6=E(_1g5.a),_1g7=E(_1g4),_1g8=E(_1g7.a);return (_1g6>=_1g8)?(_1g6!=_1g8)?E(_1g7):(E(_1g5.b)>E(_1g7.b))?E(_1g7):E(_1g5):E(_1g5);},_1g9={_:0,a:_1ay,b:_1fc,c:_1fm,d:_1fw,e:_1fG,f:_1fQ,g:_1fV,h:_1g2},_1ga=function(_1gb,_1gc,_1gd,_1ge){switch(B(_1bJ(_1g9,_1gb,_1gd))){case 0:return true;case 1:return _1gc<_1ge;default:return false;}},_1gf=function(_1gg,_1gh){var _1gi=E(_1gg),_1gj=E(_1gh);return new F(function(){return _1ga(_1gi.a,_1gi.b,_1gj.a,_1gj.b);});},_1gk=function(_1gl,_1gm,_1gn,_1go){switch(B(_1bJ(_1g9,_1gl,_1gn))){case 0:return true;case 1:return _1gm<=_1go;default:return false;}},_1gp=function(_1gq,_1gr){var _1gs=E(_1gq),_1gt=E(_1gr);return new F(function(){return _1gk(_1gs.a,_1gs.b,_1gt.a,_1gt.b);});},_1gu=function(_1gv,_1gw,_1gx,_1gy){switch(B(_1bJ(_1g9,_1gv,_1gx))){case 0:return false;case 1:return _1gw>_1gy;default:return true;}},_1gz=function(_1gA,_1gB){var _1gC=E(_1gA),_1gD=E(_1gB);return new F(function(){return _1gu(_1gC.a,_1gC.b,_1gD.a,_1gD.b);});},_1gE=function(_1gF,_1gG,_1gH,_1gI){switch(B(_1bJ(_1g9,_1gF,_1gH))){case 0:return false;case 1:return _1gG>=_1gI;default:return true;}},_1gJ=function(_1gK,_1gL){var _1gM=E(_1gK),_1gN=E(_1gL);return new F(function(){return _1gE(_1gM.a,_1gM.b,_1gN.a,_1gN.b);});},_1gO=function(_1gP,_1gQ,_1gR,_1gS){switch(B(_1bJ(_1g9,_1gP,_1gR))){case 0:return 0;case 1:return new F(function(){return _ji(_1gQ,_1gS);});break;default:return 2;}},_1gT=function(_1gU,_1gV){var _1gW=E(_1gU),_1gX=E(_1gV);return new F(function(){return _1gO(_1gW.a,_1gW.b,_1gX.a,_1gX.b);});},_1gY=function(_1gZ,_1h0){var _1h1=E(_1gZ),_1h2=E(_1h0);switch(B(_1bJ(_1g9,_1h1.a,_1h2.a))){case 0:return E(_1h2);case 1:return (_1h1.b>_1h2.b)?E(_1h1):E(_1h2);default:return E(_1h1);}},_1h3=function(_1h4,_1h5){var _1h6=E(_1h4),_1h7=E(_1h5);switch(B(_1bJ(_1g9,_1h6.a,_1h7.a))){case 0:return E(_1h6);case 1:return (_1h6.b>_1h7.b)?E(_1h7):E(_1h6);default:return E(_1h7);}},_1h8={_:0,a:_1aO,b:_1gT,c:_1gf,d:_1gp,e:_1gz,f:_1gJ,g:_1gY,h:_1h3},_1h9=function(_1ha,_1hb){while(1){var _1hc=E(_1ha);if(!_1hc._){return (E(_1hb)._==0)?1:0;}else{var _1hd=E(_1hb);if(!_1hd._){return 2;}else{var _1he=B(_12j(_1hc.a,_1hd.a));if(_1he==1){_1ha=_1hc.b;_1hb=_1hd.b;continue;}else{return E(_1he);}}}}},_1hf=function(_1hg,_1hh){return (B(_1h9(_1hg,_1hh))==0)?true:false;},_1hi=function(_1hj,_1hk){var _1hl=E(_1hj);switch(_1hl._){case 0:var _1hm=_1hl.a,_1hn=E(_1hk);if(!_1hn._){var _1ho=_1hn.a;return (_1hm>=_1ho)?(_1hm!=_1ho)?false:(B(_1bJ(_1h8,_1hl.b,_1hn.b))==0)?true:false:true;}else{return true;}break;case 1:var _1hp=E(_1hk);switch(_1hp._){case 0:return false;case 1:return _1hl.a<_1hp.a;default:return true;}break;default:var _1hq=E(_1hk);if(_1hq._==2){var _1hr=E(_1hl.a),_1hs=E(_1hq.a);switch(B(_12Z(_1hr.a,_1hr.b,_1hr.c,_1hs.a,_1hs.b,_1hs.c))){case 0:return true;case 1:switch(B(_1br(_1hl.b,_1hq.b))){case 0:return true;case 1:return new F(function(){return _1hf(_1hl.c,_1hq.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1ht=function(_1hu,_1hv){return (B(_1h9(_1hu,_1hv))==2)?false:true;},_1hw=function(_1hx,_1hy){var _1hz=E(_1hx);switch(_1hz._){case 0:var _1hA=_1hz.a,_1hB=E(_1hy);if(!_1hB._){var _1hC=_1hB.a;return (_1hA>=_1hC)?(_1hA!=_1hC)?false:(B(_1bJ(_1h8,_1hz.b,_1hB.b))==2)?false:true:true;}else{return true;}break;case 1:var _1hD=E(_1hy);switch(_1hD._){case 0:return false;case 1:return _1hz.a<=_1hD.a;default:return true;}break;default:var _1hE=E(_1hy);if(_1hE._==2){var _1hF=E(_1hz.a),_1hG=E(_1hE.a);switch(B(_12Z(_1hF.a,_1hF.b,_1hF.c,_1hG.a,_1hG.b,_1hG.c))){case 0:return true;case 1:switch(B(_1br(_1hz.b,_1hE.b))){case 0:return true;case 1:return new F(function(){return _1ht(_1hz.c,_1hE.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1hH=function(_1hI,_1hJ){return (B(_1h9(_1hI,_1hJ))==2)?true:false;},_1hK=function(_1hL,_1hM){var _1hN=E(_1hL);switch(_1hN._){case 0:var _1hO=_1hN.a,_1hP=E(_1hM);if(!_1hP._){var _1hQ=_1hP.a;return (_1hO>=_1hQ)?(_1hO!=_1hQ)?true:(B(_1bJ(_1h8,_1hN.b,_1hP.b))==2)?true:false:false;}else{return false;}break;case 1:var _1hR=E(_1hM);switch(_1hR._){case 0:return true;case 1:return _1hN.a>_1hR.a;default:return false;}break;default:var _1hS=E(_1hM);if(_1hS._==2){var _1hT=E(_1hN.a),_1hU=E(_1hS.a);switch(B(_12Z(_1hT.a,_1hT.b,_1hT.c,_1hU.a,_1hU.b,_1hU.c))){case 0:return false;case 1:switch(B(_1br(_1hN.b,_1hS.b))){case 0:return false;case 1:return new F(function(){return _1hH(_1hN.c,_1hS.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1hV=function(_1hW,_1hX){return (B(_1h9(_1hW,_1hX))==0)?false:true;},_1hY=function(_1hZ,_1i0){var _1i1=E(_1hZ);switch(_1i1._){case 0:var _1i2=_1i1.a,_1i3=E(_1i0);if(!_1i3._){var _1i4=_1i3.a;return (_1i2>=_1i4)?(_1i2!=_1i4)?true:(B(_1bJ(_1h8,_1i1.b,_1i3.b))==0)?false:true:false;}else{return false;}break;case 1:var _1i5=E(_1i0);switch(_1i5._){case 0:return true;case 1:return _1i1.a>=_1i5.a;default:return false;}break;default:var _1i6=E(_1i0);if(_1i6._==2){var _1i7=E(_1i1.a),_1i8=E(_1i6.a);switch(B(_12Z(_1i7.a,_1i7.b,_1i7.c,_1i8.a,_1i8.b,_1i8.c))){case 0:return false;case 1:switch(B(_1br(_1i1.b,_1i6.b))){case 0:return false;case 1:return new F(function(){return _1hV(_1i1.c,_1i6.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1i9=function(_1ia,_1ib){var _1ic=E(_1ia);switch(_1ic._){case 0:var _1id=_1ic.a,_1ie=E(_1ib);if(!_1ie._){var _1if=_1ie.a;if(_1id>=_1if){if(_1id!=_1if){return 2;}else{return new F(function(){return _1bJ(_1h8,_1ic.b,_1ie.b);});}}else{return 0;}}else{return 0;}break;case 1:var _1ig=E(_1ib);switch(_1ig._){case 0:return 2;case 1:return new F(function(){return _ji(_1ic.a,_1ig.a);});break;default:return 0;}break;default:var _1ih=E(_1ib);if(_1ih._==2){var _1ii=E(_1ic.a),_1ij=E(_1ih.a);switch(B(_12Z(_1ii.a,_1ii.b,_1ii.c,_1ij.a,_1ij.b,_1ij.c))){case 0:return 0;case 1:switch(B(_1br(_1ic.b,_1ih.b))){case 0:return 0;case 1:return new F(function(){return _1h9(_1ic.c,_1ih.c);});break;default:return 2;}break;default:return 2;}}else{return 2;}}},_1ik=function(_1il,_1im){return (!B(_1hw(_1il,_1im)))?E(_1il):E(_1im);},_1in=function(_1io,_1ip){return (!B(_1hw(_1io,_1ip)))?E(_1ip):E(_1io);},_1iq={_:0,a:_1b6,b:_1i9,c:_1hi,d:_1hw,e:_1hK,f:_1hY,g:_1ik,h:_1in},_1ir=__Z,_1is=function(_1it,_1iu,_1iv){var _1iw=E(_1iu);if(!_1iw._){return E(_1iv);}else{var _1ix=function(_1iy,_1iz){while(1){var _1iA=E(_1iz);if(!_1iA._){var _1iB=_1iA.b,_1iC=_1iA.d;switch(B(A3(_13t,_1it,_1iy,_1iB))){case 0:return new F(function(){return _OS(_1iB,B(_1ix(_1iy,_1iA.c)),_1iC);});break;case 1:return E(_1iC);default:_1iz=_1iC;continue;}}else{return new T0(1);}}};return new F(function(){return _1ix(_1iw.a,_1iv);});}},_1iD=function(_1iE,_1iF,_1iG){var _1iH=E(_1iF);if(!_1iH._){return E(_1iG);}else{var _1iI=function(_1iJ,_1iK){while(1){var _1iL=E(_1iK);if(!_1iL._){var _1iM=_1iL.b,_1iN=_1iL.c;switch(B(A3(_13t,_1iE,_1iM,_1iJ))){case 0:return new F(function(){return _OS(_1iM,_1iN,B(_1iI(_1iJ,_1iL.d)));});break;case 1:return E(_1iN);default:_1iK=_1iN;continue;}}else{return new T0(1);}}};return new F(function(){return _1iI(_1iH.a,_1iG);});}},_1iO=function(_1iP,_1iQ,_1iR){var _1iS=E(_1iQ),_1iT=E(_1iR);if(!_1iT._){var _1iU=_1iT.b,_1iV=_1iT.c,_1iW=_1iT.d;switch(B(A3(_13t,_1iP,_1iS,_1iU))){case 0:return new F(function(){return _MW(_1iU,B(_1iO(_1iP,_1iS,_1iV)),_1iW);});break;case 1:return E(_1iT);default:return new F(function(){return _Ny(_1iU,_1iV,B(_1iO(_1iP,_1iS,_1iW)));});}}else{return new T4(0,1,E(_1iS),E(_MR),E(_MR));}},_1iX=function(_1iY,_1iZ,_1j0){return new F(function(){return _1iO(_1iY,_1iZ,_1j0);});},_1j1=function(_1j2,_1j3,_1j4,_1j5){var _1j6=E(_1j3);if(!_1j6._){var _1j7=E(_1j4);if(!_1j7._){return E(_1j5);}else{var _1j8=function(_1j9,_1ja){while(1){var _1jb=E(_1ja);if(!_1jb._){if(!B(A3(_16v,_1j2,_1jb.b,_1j9))){return E(_1jb);}else{_1ja=_1jb.c;continue;}}else{return new T0(1);}}};return new F(function(){return _1j8(_1j7.a,_1j5);});}}else{var _1jc=_1j6.a,_1jd=E(_1j4);if(!_1jd._){var _1je=function(_1jf,_1jg){while(1){var _1jh=E(_1jg);if(!_1jh._){if(!B(A3(_17e,_1j2,_1jh.b,_1jf))){return E(_1jh);}else{_1jg=_1jh.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1je(_1jc,_1j5);});}else{var _1ji=function(_1jj,_1jk,_1jl){while(1){var _1jm=E(_1jl);if(!_1jm._){var _1jn=_1jm.b;if(!B(A3(_17e,_1j2,_1jn,_1jj))){if(!B(A3(_16v,_1j2,_1jn,_1jk))){return E(_1jm);}else{_1jl=_1jm.c;continue;}}else{_1jl=_1jm.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1ji(_1jc,_1jd.a,_1j5);});}}},_1jo=function(_1jp,_1jq,_1jr,_1js,_1jt){var _1ju=E(_1jt);if(!_1ju._){var _1jv=_1ju.b,_1jw=_1ju.c,_1jx=_1ju.d,_1jy=E(_1js);if(!_1jy._){var _1jz=_1jy.b,_1jA=function(_1jB){var _1jC=new T1(1,E(_1jz));return new F(function(){return _OS(_1jz,B(_1jo(_1jp,_1jq,_1jC,_1jy.c,B(_1j1(_1jp,_1jq,_1jC,_1ju)))),B(_1jo(_1jp,_1jC,_1jr,_1jy.d,B(_1j1(_1jp,_1jC,_1jr,_1ju)))));});};if(!E(_1jw)._){return new F(function(){return _1jA(_);});}else{if(!E(_1jx)._){return new F(function(){return _1jA(_);});}else{return new F(function(){return _1iX(_1jp,_1jv,_1jy);});}}}else{return new F(function(){return _OS(_1jv,B(_1is(_1jp,_1jq,_1jw)),B(_1iD(_1jp,_1jr,_1jx)));});}}else{return E(_1js);}},_1jD=function(_1jE,_1jF,_1jG,_1jH,_1jI,_1jJ,_1jK,_1jL,_1jM,_1jN,_1jO){var _1jP=function(_1jQ){var _1jR=new T1(1,E(_1jI));return new F(function(){return _OS(_1jI,B(_1jo(_1jE,_1jF,_1jR,_1jJ,B(_1j1(_1jE,_1jF,_1jR,new T4(0,_1jL,E(_1jM),E(_1jN),E(_1jO)))))),B(_1jo(_1jE,_1jR,_1jG,_1jK,B(_1j1(_1jE,_1jR,_1jG,new T4(0,_1jL,E(_1jM),E(_1jN),E(_1jO)))))));});};if(!E(_1jN)._){return new F(function(){return _1jP(_);});}else{if(!E(_1jO)._){return new F(function(){return _1jP(_);});}else{return new F(function(){return _1iX(_1jE,_1jM,new T4(0,_1jH,E(_1jI),E(_1jJ),E(_1jK)));});}}},_1jS=function(_1jT,_1jU,_1jV){var _1jW=E(_1jU);if(!_1jW._){var _1jX=E(_1jV);if(!_1jX._){return new F(function(){return _1jD(_1iq,_1ir,_1ir,_1jW.a,_1jW.b,_1jW.c,_1jW.d,_1jX.a,_1jX.b,_1jX.c,_1jX.d);});}else{return E(_1jW);}}else{return E(_1jV);}},_1jY=function(_1jZ,_1k0,_1k1){var _1k2=function(_1k3,_1k4,_1k5,_1k6){var _1k7=E(_1k6);switch(_1k7._){case 0:var _1k8=_1k7.a,_1k9=_1k7.b,_1ka=_1k7.c,_1kb=_1k7.d,_1kc=_1k9>>>0;if(((_1k5>>>0&((_1kc-1>>>0^4294967295)>>>0^_1kc)>>>0)>>>0&4294967295)==_1k8){return ((_1k5>>>0&_1kc)>>>0==0)?new T4(0,_1k8,_1k9,E(B(_1k2(_1k3,_1k4,_1k5,_1ka))),E(_1kb)):new T4(0,_1k8,_1k9,E(_1ka),E(B(_1k2(_1k3,_1k4,_1k5,_1kb))));}else{var _1kd=(_1k5>>>0^_1k8>>>0)>>>0,_1ke=(_1kd|_1kd>>>1)>>>0,_1kf=(_1ke|_1ke>>>2)>>>0,_1kg=(_1kf|_1kf>>>4)>>>0,_1kh=(_1kg|_1kg>>>8)>>>0,_1ki=(_1kh|_1kh>>>16)>>>0,_1kj=(_1ki^_1ki>>>1)>>>0&4294967295,_1kk=_1kj>>>0;return ((_1k5>>>0&_1kk)>>>0==0)?new T4(0,(_1k5>>>0&((_1kk-1>>>0^4294967295)>>>0^_1kk)>>>0)>>>0&4294967295,_1kj,E(new T2(1,_1k3,_1k4)),E(_1k7)):new T4(0,(_1k5>>>0&((_1kk-1>>>0^4294967295)>>>0^_1kk)>>>0)>>>0&4294967295,_1kj,E(_1k7),E(new T2(1,_1k3,_1k4)));}break;case 1:var _1kl=_1k7.a;if(_1k5!=_1kl){var _1km=(_1k5>>>0^_1kl>>>0)>>>0,_1kn=(_1km|_1km>>>1)>>>0,_1ko=(_1kn|_1kn>>>2)>>>0,_1kp=(_1ko|_1ko>>>4)>>>0,_1kq=(_1kp|_1kp>>>8)>>>0,_1kr=(_1kq|_1kq>>>16)>>>0,_1ks=(_1kr^_1kr>>>1)>>>0&4294967295,_1kt=_1ks>>>0;return ((_1k5>>>0&_1kt)>>>0==0)?new T4(0,(_1k5>>>0&((_1kt-1>>>0^4294967295)>>>0^_1kt)>>>0)>>>0&4294967295,_1ks,E(new T2(1,_1k3,_1k4)),E(_1k7)):new T4(0,(_1k5>>>0&((_1kt-1>>>0^4294967295)>>>0^_1kt)>>>0)>>>0&4294967295,_1ks,E(_1k7),E(new T2(1,_1k3,_1k4)));}else{return new T2(1,_1k3,new T(function(){return B(A3(_1jZ,_1k3,_1k4,_1k7.b));}));}break;default:return new T2(1,_1k3,_1k4);}},_1ku=function(_1kv,_1kw,_1kx,_1ky){var _1kz=E(_1ky);switch(_1kz._){case 0:var _1kA=_1kz.a,_1kB=_1kz.b,_1kC=_1kz.c,_1kD=_1kz.d,_1kE=_1kB>>>0;if(((_1kx>>>0&((_1kE-1>>>0^4294967295)>>>0^_1kE)>>>0)>>>0&4294967295)==_1kA){return ((_1kx>>>0&_1kE)>>>0==0)?new T4(0,_1kA,_1kB,E(B(_1ku(_1kv,_1kw,_1kx,_1kC))),E(_1kD)):new T4(0,_1kA,_1kB,E(_1kC),E(B(_1ku(_1kv,_1kw,_1kx,_1kD))));}else{var _1kF=(_1kA>>>0^_1kx>>>0)>>>0,_1kG=(_1kF|_1kF>>>1)>>>0,_1kH=(_1kG|_1kG>>>2)>>>0,_1kI=(_1kH|_1kH>>>4)>>>0,_1kJ=(_1kI|_1kI>>>8)>>>0,_1kK=(_1kJ|_1kJ>>>16)>>>0,_1kL=(_1kK^_1kK>>>1)>>>0&4294967295,_1kM=_1kL>>>0;return ((_1kA>>>0&_1kM)>>>0==0)?new T4(0,(_1kA>>>0&((_1kM-1>>>0^4294967295)>>>0^_1kM)>>>0)>>>0&4294967295,_1kL,E(_1kz),E(new T2(1,_1kv,_1kw))):new T4(0,(_1kA>>>0&((_1kM-1>>>0^4294967295)>>>0^_1kM)>>>0)>>>0&4294967295,_1kL,E(new T2(1,_1kv,_1kw)),E(_1kz));}break;case 1:var _1kN=_1kz.a;if(_1kN!=_1kx){var _1kO=(_1kN>>>0^_1kx>>>0)>>>0,_1kP=(_1kO|_1kO>>>1)>>>0,_1kQ=(_1kP|_1kP>>>2)>>>0,_1kR=(_1kQ|_1kQ>>>4)>>>0,_1kS=(_1kR|_1kR>>>8)>>>0,_1kT=(_1kS|_1kS>>>16)>>>0,_1kU=(_1kT^_1kT>>>1)>>>0&4294967295,_1kV=_1kU>>>0;return ((_1kN>>>0&_1kV)>>>0==0)?new T4(0,(_1kN>>>0&((_1kV-1>>>0^4294967295)>>>0^_1kV)>>>0)>>>0&4294967295,_1kU,E(_1kz),E(new T2(1,_1kv,_1kw))):new T4(0,(_1kN>>>0&((_1kV-1>>>0^4294967295)>>>0^_1kV)>>>0)>>>0&4294967295,_1kU,E(new T2(1,_1kv,_1kw)),E(_1kz));}else{return new T2(1,_1kN,new T(function(){return B(A3(_1jZ,_1kN,_1kz.b,_1kw));}));}break;default:return new T2(1,_1kv,_1kw);}},_1kW=function(_1kX,_1kY,_1kZ,_1l0,_1l1,_1l2,_1l3){var _1l4=_1l1>>>0;if(((_1kZ>>>0&((_1l4-1>>>0^4294967295)>>>0^_1l4)>>>0)>>>0&4294967295)==_1l0){return ((_1kZ>>>0&_1l4)>>>0==0)?new T4(0,_1l0,_1l1,E(B(_1ku(_1kX,_1kY,_1kZ,_1l2))),E(_1l3)):new T4(0,_1l0,_1l1,E(_1l2),E(B(_1ku(_1kX,_1kY,_1kZ,_1l3))));}else{var _1l5=(_1l0>>>0^_1kZ>>>0)>>>0,_1l6=(_1l5|_1l5>>>1)>>>0,_1l7=(_1l6|_1l6>>>2)>>>0,_1l8=(_1l7|_1l7>>>4)>>>0,_1l9=(_1l8|_1l8>>>8)>>>0,_1la=(_1l9|_1l9>>>16)>>>0,_1lb=(_1la^_1la>>>1)>>>0&4294967295,_1lc=_1lb>>>0;return ((_1l0>>>0&_1lc)>>>0==0)?new T4(0,(_1l0>>>0&((_1lc-1>>>0^4294967295)>>>0^_1lc)>>>0)>>>0&4294967295,_1lb,E(new T4(0,_1l0,_1l1,E(_1l2),E(_1l3))),E(new T2(1,_1kX,_1kY))):new T4(0,(_1l0>>>0&((_1lc-1>>>0^4294967295)>>>0^_1lc)>>>0)>>>0&4294967295,_1lb,E(new T2(1,_1kX,_1kY)),E(new T4(0,_1l0,_1l1,E(_1l2),E(_1l3))));}},_1ld=function(_1le,_1lf){var _1lg=E(_1le);switch(_1lg._){case 0:var _1lh=_1lg.a,_1li=_1lg.b,_1lj=_1lg.c,_1lk=_1lg.d,_1ll=E(_1lf);switch(_1ll._){case 0:var _1lm=_1ll.a,_1ln=_1ll.b,_1lo=_1ll.c,_1lp=_1ll.d;if(_1li>>>0<=_1ln>>>0){if(_1ln>>>0<=_1li>>>0){if(_1lh!=_1lm){var _1lq=(_1lh>>>0^_1lm>>>0)>>>0,_1lr=(_1lq|_1lq>>>1)>>>0,_1ls=(_1lr|_1lr>>>2)>>>0,_1lt=(_1ls|_1ls>>>4)>>>0,_1lu=(_1lt|_1lt>>>8)>>>0,_1lv=(_1lu|_1lu>>>16)>>>0,_1lw=(_1lv^_1lv>>>1)>>>0&4294967295,_1lx=_1lw>>>0;return ((_1lh>>>0&_1lx)>>>0==0)?new T4(0,(_1lh>>>0&((_1lx-1>>>0^4294967295)>>>0^_1lx)>>>0)>>>0&4294967295,_1lw,E(_1lg),E(_1ll)):new T4(0,(_1lh>>>0&((_1lx-1>>>0^4294967295)>>>0^_1lx)>>>0)>>>0&4294967295,_1lw,E(_1ll),E(_1lg));}else{return new T4(0,_1lh,_1li,E(B(_1ld(_1lj,_1lo))),E(B(_1ld(_1lk,_1lp))));}}else{var _1ly=_1ln>>>0;if(((_1lh>>>0&((_1ly-1>>>0^4294967295)>>>0^_1ly)>>>0)>>>0&4294967295)==_1lm){return ((_1lh>>>0&_1ly)>>>0==0)?new T4(0,_1lm,_1ln,E(B(_1lz(_1lh,_1li,_1lj,_1lk,_1lo))),E(_1lp)):new T4(0,_1lm,_1ln,E(_1lo),E(B(_1lz(_1lh,_1li,_1lj,_1lk,_1lp))));}else{var _1lA=(_1lh>>>0^_1lm>>>0)>>>0,_1lB=(_1lA|_1lA>>>1)>>>0,_1lC=(_1lB|_1lB>>>2)>>>0,_1lD=(_1lC|_1lC>>>4)>>>0,_1lE=(_1lD|_1lD>>>8)>>>0,_1lF=(_1lE|_1lE>>>16)>>>0,_1lG=(_1lF^_1lF>>>1)>>>0&4294967295,_1lH=_1lG>>>0;return ((_1lh>>>0&_1lH)>>>0==0)?new T4(0,(_1lh>>>0&((_1lH-1>>>0^4294967295)>>>0^_1lH)>>>0)>>>0&4294967295,_1lG,E(_1lg),E(_1ll)):new T4(0,(_1lh>>>0&((_1lH-1>>>0^4294967295)>>>0^_1lH)>>>0)>>>0&4294967295,_1lG,E(_1ll),E(_1lg));}}}else{var _1lI=_1li>>>0;if(((_1lm>>>0&((_1lI-1>>>0^4294967295)>>>0^_1lI)>>>0)>>>0&4294967295)==_1lh){return ((_1lm>>>0&_1lI)>>>0==0)?new T4(0,_1lh,_1li,E(B(_1lJ(_1lj,_1lm,_1ln,_1lo,_1lp))),E(_1lk)):new T4(0,_1lh,_1li,E(_1lj),E(B(_1lJ(_1lk,_1lm,_1ln,_1lo,_1lp))));}else{var _1lK=(_1lh>>>0^_1lm>>>0)>>>0,_1lL=(_1lK|_1lK>>>1)>>>0,_1lM=(_1lL|_1lL>>>2)>>>0,_1lN=(_1lM|_1lM>>>4)>>>0,_1lO=(_1lN|_1lN>>>8)>>>0,_1lP=(_1lO|_1lO>>>16)>>>0,_1lQ=(_1lP^_1lP>>>1)>>>0&4294967295,_1lR=_1lQ>>>0;return ((_1lh>>>0&_1lR)>>>0==0)?new T4(0,(_1lh>>>0&((_1lR-1>>>0^4294967295)>>>0^_1lR)>>>0)>>>0&4294967295,_1lQ,E(_1lg),E(_1ll)):new T4(0,(_1lh>>>0&((_1lR-1>>>0^4294967295)>>>0^_1lR)>>>0)>>>0&4294967295,_1lQ,E(_1ll),E(_1lg));}}break;case 1:var _1lS=_1ll.a;return new F(function(){return _1kW(_1lS,_1ll.b,_1lS,_1lh,_1li,_1lj,_1lk);});break;default:return E(_1lg);}break;case 1:var _1lT=_1lg.a;return new F(function(){return _1k2(_1lT,_1lg.b,_1lT,_1lf);});break;default:return E(_1lf);}},_1lz=function(_1lU,_1lV,_1lW,_1lX,_1lY){var _1lZ=E(_1lY);switch(_1lZ._){case 0:var _1m0=_1lZ.a,_1m1=_1lZ.b,_1m2=_1lZ.c,_1m3=_1lZ.d;if(_1lV>>>0<=_1m1>>>0){if(_1m1>>>0<=_1lV>>>0){if(_1lU!=_1m0){var _1m4=(_1lU>>>0^_1m0>>>0)>>>0,_1m5=(_1m4|_1m4>>>1)>>>0,_1m6=(_1m5|_1m5>>>2)>>>0,_1m7=(_1m6|_1m6>>>4)>>>0,_1m8=(_1m7|_1m7>>>8)>>>0,_1m9=(_1m8|_1m8>>>16)>>>0,_1ma=(_1m9^_1m9>>>1)>>>0&4294967295,_1mb=_1ma>>>0;return ((_1lU>>>0&_1mb)>>>0==0)?new T4(0,(_1lU>>>0&((_1mb-1>>>0^4294967295)>>>0^_1mb)>>>0)>>>0&4294967295,_1ma,E(new T4(0,_1lU,_1lV,E(_1lW),E(_1lX))),E(_1lZ)):new T4(0,(_1lU>>>0&((_1mb-1>>>0^4294967295)>>>0^_1mb)>>>0)>>>0&4294967295,_1ma,E(_1lZ),E(new T4(0,_1lU,_1lV,E(_1lW),E(_1lX))));}else{return new T4(0,_1lU,_1lV,E(B(_1ld(_1lW,_1m2))),E(B(_1ld(_1lX,_1m3))));}}else{var _1mc=_1m1>>>0;if(((_1lU>>>0&((_1mc-1>>>0^4294967295)>>>0^_1mc)>>>0)>>>0&4294967295)==_1m0){return ((_1lU>>>0&_1mc)>>>0==0)?new T4(0,_1m0,_1m1,E(B(_1lz(_1lU,_1lV,_1lW,_1lX,_1m2))),E(_1m3)):new T4(0,_1m0,_1m1,E(_1m2),E(B(_1lz(_1lU,_1lV,_1lW,_1lX,_1m3))));}else{var _1md=(_1lU>>>0^_1m0>>>0)>>>0,_1me=(_1md|_1md>>>1)>>>0,_1mf=(_1me|_1me>>>2)>>>0,_1mg=(_1mf|_1mf>>>4)>>>0,_1mh=(_1mg|_1mg>>>8)>>>0,_1mi=(_1mh|_1mh>>>16)>>>0,_1mj=(_1mi^_1mi>>>1)>>>0&4294967295,_1mk=_1mj>>>0;return ((_1lU>>>0&_1mk)>>>0==0)?new T4(0,(_1lU>>>0&((_1mk-1>>>0^4294967295)>>>0^_1mk)>>>0)>>>0&4294967295,_1mj,E(new T4(0,_1lU,_1lV,E(_1lW),E(_1lX))),E(_1lZ)):new T4(0,(_1lU>>>0&((_1mk-1>>>0^4294967295)>>>0^_1mk)>>>0)>>>0&4294967295,_1mj,E(_1lZ),E(new T4(0,_1lU,_1lV,E(_1lW),E(_1lX))));}}}else{var _1ml=_1lV>>>0;if(((_1m0>>>0&((_1ml-1>>>0^4294967295)>>>0^_1ml)>>>0)>>>0&4294967295)==_1lU){return ((_1m0>>>0&_1ml)>>>0==0)?new T4(0,_1lU,_1lV,E(B(_1lJ(_1lW,_1m0,_1m1,_1m2,_1m3))),E(_1lX)):new T4(0,_1lU,_1lV,E(_1lW),E(B(_1lJ(_1lX,_1m0,_1m1,_1m2,_1m3))));}else{var _1mm=(_1lU>>>0^_1m0>>>0)>>>0,_1mn=(_1mm|_1mm>>>1)>>>0,_1mo=(_1mn|_1mn>>>2)>>>0,_1mp=(_1mo|_1mo>>>4)>>>0,_1mq=(_1mp|_1mp>>>8)>>>0,_1mr=(_1mq|_1mq>>>16)>>>0,_1ms=(_1mr^_1mr>>>1)>>>0&4294967295,_1mt=_1ms>>>0;return ((_1lU>>>0&_1mt)>>>0==0)?new T4(0,(_1lU>>>0&((_1mt-1>>>0^4294967295)>>>0^_1mt)>>>0)>>>0&4294967295,_1ms,E(new T4(0,_1lU,_1lV,E(_1lW),E(_1lX))),E(_1lZ)):new T4(0,(_1lU>>>0&((_1mt-1>>>0^4294967295)>>>0^_1mt)>>>0)>>>0&4294967295,_1ms,E(_1lZ),E(new T4(0,_1lU,_1lV,E(_1lW),E(_1lX))));}}break;case 1:var _1mu=_1lZ.a;return new F(function(){return _1kW(_1mu,_1lZ.b,_1mu,_1lU,_1lV,_1lW,_1lX);});break;default:return new T4(0,_1lU,_1lV,E(_1lW),E(_1lX));}},_1lJ=function(_1mv,_1mw,_1mx,_1my,_1mz){var _1mA=E(_1mv);switch(_1mA._){case 0:var _1mB=_1mA.a,_1mC=_1mA.b,_1mD=_1mA.c,_1mE=_1mA.d;if(_1mC>>>0<=_1mx>>>0){if(_1mx>>>0<=_1mC>>>0){if(_1mB!=_1mw){var _1mF=(_1mB>>>0^_1mw>>>0)>>>0,_1mG=(_1mF|_1mF>>>1)>>>0,_1mH=(_1mG|_1mG>>>2)>>>0,_1mI=(_1mH|_1mH>>>4)>>>0,_1mJ=(_1mI|_1mI>>>8)>>>0,_1mK=(_1mJ|_1mJ>>>16)>>>0,_1mL=(_1mK^_1mK>>>1)>>>0&4294967295,_1mM=_1mL>>>0;return ((_1mB>>>0&_1mM)>>>0==0)?new T4(0,(_1mB>>>0&((_1mM-1>>>0^4294967295)>>>0^_1mM)>>>0)>>>0&4294967295,_1mL,E(_1mA),E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz)))):new T4(0,(_1mB>>>0&((_1mM-1>>>0^4294967295)>>>0^_1mM)>>>0)>>>0&4294967295,_1mL,E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz))),E(_1mA));}else{return new T4(0,_1mB,_1mC,E(B(_1ld(_1mD,_1my))),E(B(_1ld(_1mE,_1mz))));}}else{var _1mN=_1mx>>>0;if(((_1mB>>>0&((_1mN-1>>>0^4294967295)>>>0^_1mN)>>>0)>>>0&4294967295)==_1mw){return ((_1mB>>>0&_1mN)>>>0==0)?new T4(0,_1mw,_1mx,E(B(_1lz(_1mB,_1mC,_1mD,_1mE,_1my))),E(_1mz)):new T4(0,_1mw,_1mx,E(_1my),E(B(_1lz(_1mB,_1mC,_1mD,_1mE,_1mz))));}else{var _1mO=(_1mB>>>0^_1mw>>>0)>>>0,_1mP=(_1mO|_1mO>>>1)>>>0,_1mQ=(_1mP|_1mP>>>2)>>>0,_1mR=(_1mQ|_1mQ>>>4)>>>0,_1mS=(_1mR|_1mR>>>8)>>>0,_1mT=(_1mS|_1mS>>>16)>>>0,_1mU=(_1mT^_1mT>>>1)>>>0&4294967295,_1mV=_1mU>>>0;return ((_1mB>>>0&_1mV)>>>0==0)?new T4(0,(_1mB>>>0&((_1mV-1>>>0^4294967295)>>>0^_1mV)>>>0)>>>0&4294967295,_1mU,E(_1mA),E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz)))):new T4(0,(_1mB>>>0&((_1mV-1>>>0^4294967295)>>>0^_1mV)>>>0)>>>0&4294967295,_1mU,E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz))),E(_1mA));}}}else{var _1mW=_1mC>>>0;if(((_1mw>>>0&((_1mW-1>>>0^4294967295)>>>0^_1mW)>>>0)>>>0&4294967295)==_1mB){return ((_1mw>>>0&_1mW)>>>0==0)?new T4(0,_1mB,_1mC,E(B(_1lJ(_1mD,_1mw,_1mx,_1my,_1mz))),E(_1mE)):new T4(0,_1mB,_1mC,E(_1mD),E(B(_1lJ(_1mE,_1mw,_1mx,_1my,_1mz))));}else{var _1mX=(_1mB>>>0^_1mw>>>0)>>>0,_1mY=(_1mX|_1mX>>>1)>>>0,_1mZ=(_1mY|_1mY>>>2)>>>0,_1n0=(_1mZ|_1mZ>>>4)>>>0,_1n1=(_1n0|_1n0>>>8)>>>0,_1n2=(_1n1|_1n1>>>16)>>>0,_1n3=(_1n2^_1n2>>>1)>>>0&4294967295,_1n4=_1n3>>>0;return ((_1mB>>>0&_1n4)>>>0==0)?new T4(0,(_1mB>>>0&((_1n4-1>>>0^4294967295)>>>0^_1n4)>>>0)>>>0&4294967295,_1n3,E(_1mA),E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz)))):new T4(0,(_1mB>>>0&((_1n4-1>>>0^4294967295)>>>0^_1n4)>>>0)>>>0&4294967295,_1n3,E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz))),E(_1mA));}}break;case 1:var _1n5=_1mA.a,_1n6=_1mA.b,_1n7=_1mx>>>0;if(((_1n5>>>0&((_1n7-1>>>0^4294967295)>>>0^_1n7)>>>0)>>>0&4294967295)==_1mw){return ((_1n5>>>0&_1n7)>>>0==0)?new T4(0,_1mw,_1mx,E(B(_1k2(_1n5,_1n6,_1n5,_1my))),E(_1mz)):new T4(0,_1mw,_1mx,E(_1my),E(B(_1k2(_1n5,_1n6,_1n5,_1mz))));}else{var _1n8=(_1n5>>>0^_1mw>>>0)>>>0,_1n9=(_1n8|_1n8>>>1)>>>0,_1na=(_1n9|_1n9>>>2)>>>0,_1nb=(_1na|_1na>>>4)>>>0,_1nc=(_1nb|_1nb>>>8)>>>0,_1nd=(_1nc|_1nc>>>16)>>>0,_1ne=(_1nd^_1nd>>>1)>>>0&4294967295,_1nf=_1ne>>>0;return ((_1n5>>>0&_1nf)>>>0==0)?new T4(0,(_1n5>>>0&((_1nf-1>>>0^4294967295)>>>0^_1nf)>>>0)>>>0&4294967295,_1ne,E(new T2(1,_1n5,_1n6)),E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz)))):new T4(0,(_1n5>>>0&((_1nf-1>>>0^4294967295)>>>0^_1nf)>>>0)>>>0&4294967295,_1ne,E(new T4(0,_1mw,_1mx,E(_1my),E(_1mz))),E(new T2(1,_1n5,_1n6)));}break;default:return new T4(0,_1mw,_1mx,E(_1my),E(_1mz));}};return new F(function(){return _1ld(_1k0,_1k1);});},_1ng=function(_1nh,_1ni,_1nj){return new F(function(){return _1jY(_1jS,_1ni,_1nj);});},_1nk=function(_1nl,_1nm){return E(_1nl);},_1nn=new T2(0,_4l,_Rm),_1no=function(_1np,_1nq){while(1){var _1nr=B((function(_1ns,_1nt){var _1nu=E(_1nt);if(!_1nu._){_1np=new T2(1,_1nu.b,new T(function(){return B(_1no(_1ns,_1nu.d));}));_1nq=_1nu.c;return __continue;}else{return E(_1ns);}})(_1np,_1nq));if(_1nr!=__continue){return _1nr;}}},_1nv=function(_1nw,_1nx,_1ny){var _1nz=function(_1nA){var _1nB=function(_1nC){if(_1nA!=_1nC){return false;}else{return new F(function(){return _18U(_1nw,B(_1no(_4,_1nx)),B(_1no(_4,_1ny)));});}},_1nD=E(_1ny);if(!_1nD._){return new F(function(){return _1nB(_1nD.a);});}else{return new F(function(){return _1nB(0);});}},_1nE=E(_1nx);if(!_1nE._){return new F(function(){return _1nz(_1nE.a);});}else{return new F(function(){return _1nz(0);});}},_1nF=function(_1nG,_1nH){return (!B(_1nv(_1b6,_1nG,_1nH)))?true:false;},_1nI=function(_1nJ,_1nK){return new F(function(){return _1nv(_1b6,_1nJ,_1nK);});},_1nL=new T2(0,_1nI,_1nF),_1nM=function(_1nN,_1nO){var _1nP=function(_1nQ){while(1){var _1nR=E(_1nQ);switch(_1nR._){case 0:var _1nS=_1nR.b>>>0;if(((_1nN>>>0&((_1nS-1>>>0^4294967295)>>>0^_1nS)>>>0)>>>0&4294967295)==_1nR.a){if(!((_1nN>>>0&_1nS)>>>0)){_1nQ=_1nR.c;continue;}else{_1nQ=_1nR.d;continue;}}else{return false;}break;case 1:return _1nN==_1nR.a;default:return false;}}};return new F(function(){return _1nP(_1nO);});},_1nT=function(_1nU,_1nV){var _1nW=function(_1nX){while(1){var _1nY=E(_1nX);switch(_1nY._){case 0:var _1nZ=_1nY.b>>>0;if(((_1nU>>>0&((_1nZ-1>>>0^4294967295)>>>0^_1nZ)>>>0)>>>0&4294967295)==_1nY.a){if(!((_1nU>>>0&_1nZ)>>>0)){_1nX=_1nY.c;continue;}else{_1nX=_1nY.d;continue;}}else{return false;}break;case 1:return ((_1nU&(-32))!=_1nY.a)?false:((1<<(_1nU&31)>>>0&_1nY.b)>>>0==0)?false:true;default:return false;}}};return new F(function(){return _1nW(_1nV);});},_1o0=function(_1o1,_1o2,_1o3){while(1){var _1o4=E(_1o2);switch(_1o4._){case 0:var _1o5=E(_1o3);if(!_1o5._){if(_1o4.b!=_1o5.b){return false;}else{if(_1o4.a!=_1o5.a){return false;}else{if(!B(_1o0(_1o1,_1o4.c,_1o5.c))){return false;}else{_1o2=_1o4.d;_1o3=_1o5.d;continue;}}}}else{return false;}break;case 1:var _1o6=E(_1o3);if(_1o6._==1){if(_1o4.a!=_1o6.a){return false;}else{return new F(function(){return A3(_pS,_1o1,_1o4.b,_1o6.b);});}}else{return false;}break;default:return (E(_1o3)._==2)?true:false;}}},_1o7=function(_1o8,_1o9){var _1oa=E(_1o9);if(!_1oa._){var _1ob=_1oa.b,_1oc=_1oa.c,_1od=_1oa.d;if(!B(A1(_1o8,_1ob))){return new F(function(){return _15T(B(_1o7(_1o8,_1oc)),B(_1o7(_1o8,_1od)));});}else{return new F(function(){return _OS(_1ob,B(_1o7(_1o8,_1oc)),B(_1o7(_1o8,_1od)));});}}else{return new T0(1);}},_1oe=function(_1of,_1og,_1oh){var _1oi=E(_1oh);switch(_1oi._){case 0:var _1oj=_1oi.a,_1ok=_1oi.b,_1ol=_1oi.c,_1om=_1oi.d,_1on=_1ok>>>0;if(((_1of>>>0&((_1on-1>>>0^4294967295)>>>0^_1on)>>>0)>>>0&4294967295)==_1oj){return ((_1of>>>0&_1on)>>>0==0)?new T4(0,_1oj,_1ok,E(B(_1oe(_1of,_1og,_1ol))),E(_1om)):new T4(0,_1oj,_1ok,E(_1ol),E(B(_1oe(_1of,_1og,_1om))));}else{var _1oo=(_1of>>>0^_1oj>>>0)>>>0,_1op=(_1oo|_1oo>>>1)>>>0,_1oq=(_1op|_1op>>>2)>>>0,_1or=(_1oq|_1oq>>>4)>>>0,_1os=(_1or|_1or>>>8)>>>0,_1ot=(_1os|_1os>>>16)>>>0,_1ou=(_1ot^_1ot>>>1)>>>0&4294967295,_1ov=_1ou>>>0;return ((_1of>>>0&_1ov)>>>0==0)?new T4(0,(_1of>>>0&((_1ov-1>>>0^4294967295)>>>0^_1ov)>>>0)>>>0&4294967295,_1ou,E(new T2(1,_1of,_1og)),E(_1oi)):new T4(0,(_1of>>>0&((_1ov-1>>>0^4294967295)>>>0^_1ov)>>>0)>>>0&4294967295,_1ou,E(_1oi),E(new T2(1,_1of,_1og)));}break;case 1:var _1ow=_1oi.a;if(_1ow!=_1of){var _1ox=(_1of>>>0^_1ow>>>0)>>>0,_1oy=(_1ox|_1ox>>>1)>>>0,_1oz=(_1oy|_1oy>>>2)>>>0,_1oA=(_1oz|_1oz>>>4)>>>0,_1oB=(_1oA|_1oA>>>8)>>>0,_1oC=(_1oB|_1oB>>>16)>>>0,_1oD=(_1oC^_1oC>>>1)>>>0&4294967295,_1oE=_1oD>>>0;return ((_1of>>>0&_1oE)>>>0==0)?new T4(0,(_1of>>>0&((_1oE-1>>>0^4294967295)>>>0^_1oE)>>>0)>>>0&4294967295,_1oD,E(new T2(1,_1of,_1og)),E(_1oi)):new T4(0,(_1of>>>0&((_1oE-1>>>0^4294967295)>>>0^_1oE)>>>0)>>>0&4294967295,_1oD,E(_1oi),E(new T2(1,_1of,_1og)));}else{return new T2(1,_1ow,(_1og|_1oi.b)>>>0);}break;default:return new T2(1,_1of,_1og);}},_1oF=function(_1oG,_1oH){while(1){var _1oI=E(_1oG);if(!_1oI._){return E(_1oH);}else{var _1oJ=E(E(_1oI.a).b),_1oK=B(_1oe(_1oJ&(-32),1<<(_1oJ&31)>>>0,_1oH));_1oG=_1oI.b;_1oH=_1oK;continue;}}},_1oL=function(_1oM,_1oN){while(1){var _1oO=E(_1oM);if(!_1oO._){return E(_1oN);}else{var _1oP=B(_1oF(E(_1oO.a).a,_1oN));_1oM=_1oO.b;_1oN=_1oP;continue;}}},_1oQ=function(_1oR,_1oS){while(1){var _1oT=E(_1oS);if(!_1oT._){var _1oU=_1oT.c,_1oV=_1oT.d,_1oW=E(_1oT.b);if(!_1oW._){var _1oX=B(_1oL(_1oW.b,B(_1oQ(_1oR,_1oV))));_1oR=_1oX;_1oS=_1oU;continue;}else{var _1oX=B(_1oQ(_1oR,_1oV));_1oR=_1oX;_1oS=_1oU;continue;}}else{return E(_1oR);}}},_1oY=-1,_1oZ=-2,_1p0=-3,_1p1=new T2(1,_Mf,_4),_1p2=new T2(1,_1p0,_1p1),_1p3=new T2(1,_1oZ,_1p2),_1p4=new T2(1,_1oY,_1p3),_1p5=function(_1p6,_1p7,_1p8){var _1p9=function(_1pa,_1pb){if(!B(_1o0(_1nL,_1p6,_1pa))){return new F(function(){return _1p5(_1pa,_1pb,_1p8);});}else{return E(_1p6);}},_1pc=function(_1pd){if(!B(_w5(_j7,_1pd,_1p4))){var _1pe=E(_1pd);if(!B(_1nM(_1pe,_1p6))){return new F(function(){return _1nT(_1pe,_1p7);});}else{return true;}}else{return true;}},_1pf=function(_1pg){while(1){var _1ph=E(_1pg);if(!_1ph._){return true;}else{if(!B(_1pc(E(_1ph.a).b))){return false;}else{_1pg=_1ph.b;continue;}}}},_1pi=function(_1pj){var _1pk=E(_1pj);switch(_1pk._){case 0:return new F(function(){return _1pf(_1pk.b);});break;case 1:return new F(function(){return _1pc(_1pk.a);});break;default:return true;}},_1pl=function(_1pm,_1pn,_1po){while(1){var _1pp=B((function(_1pq,_1pr,_1ps){var _1pt=E(_1ps);switch(_1pt._){case 0:var _1pu=B(_1pl(_1pq,_1pr,_1pt.d));_1pm=_1pu.a;_1pn=_1pu.b;_1po=_1pt.c;return __continue;case 1:var _1pv=E(_1pq),_1pw=E(_1pr),_1px=B(_1o7(_1pi,_1pt.b));return (_1px._==0)?new T2(0,new T(function(){return B(_14A(_1pt.a,_1px,_1pv));}),new T(function(){return B(_1oQ(_1pw,_1px));})):new T2(0,_1pv,_1pw);default:return new T2(0,_1pq,_1pr);}})(_1pm,_1pn,_1po));if(_1pp!=__continue){return _1pp;}}},_1py=E(_1p8);if(!_1py._){var _1pz=_1py.c,_1pA=_1py.d;if(_1py.b>=0){var _1pB=B(_1pl(_UD,_18E,_1pA)),_1pC=B(_1pl(_1pB.a,_1pB.b,_1pz));return new F(function(){return _1p9(_1pC.a,_1pC.b);});}else{var _1pD=B(_1pl(_UD,_18E,_1pz)),_1pE=B(_1pl(_1pD.a,_1pD.b,_1pA));return new F(function(){return _1p9(_1pE.a,_1pE.b);});}}else{var _1pF=B(_1pl(_UD,_18E,_1py));return new F(function(){return _1p9(_1pF.a,_1pF.b);});}},_1pG=function(_1pH,_1pI){while(1){var _1pJ=E(_1pI);if(!_1pJ._){return E(_1pH);}else{var _1pK=E(_1pJ.a),_1pL=B(_14A(E(_1pK.a),_1pK.b,_1pH));_1pH=_1pL;_1pI=_1pJ.b;continue;}}},_1pM=function(_1pN){var _1pO=E(_1pN);return (_1pO._==0)?(E(_1pO.b)._==0)?true:false:false;},_1pP=new T(function(){return B(unCStr(")"));}),_1pQ=function(_1pR,_1pS){var _1pT=new T(function(){var _1pU=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_1pS,_4)),_1pP));})));},1);return B(_0(B(_bZ(0,_1pR,_4)),_1pU));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1pT)));});},_1pV=new T(function(){return B(_7f("pgf/PGF/Optimize.hs:(259,9)-(262,117)|function getFunctions"));}),_1pW=new T(function(){return B(unCStr("&|"));}),_1pX=new T2(1,_1pW,_4),_1pY=new T(function(){return B(unCStr("&+"));}),_1pZ=new T2(1,_1pY,_4),_1q0=new T(function(){return B(_7f("pgf/PGF/Optimize.hs:(235,9)-(245,73)|function seq2prefix"));}),_1q1=function(_1q2,_1q3,_1q4,_1q5,_1q6,_1q7){var _1q8=_1q5>>>0;if(((_1q2>>>0&((_1q8-1>>>0^4294967295)>>>0^_1q8)>>>0)>>>0&4294967295)==_1q4){return ((_1q2>>>0&_1q8)>>>0==0)?new T4(0,_1q4,_1q5,E(B(_1oe(_1q2,_1q3,_1q6))),E(_1q7)):new T4(0,_1q4,_1q5,E(_1q6),E(B(_1oe(_1q2,_1q3,_1q7))));}else{var _1q9=(_1q2>>>0^_1q4>>>0)>>>0,_1qa=(_1q9|_1q9>>>1)>>>0,_1qb=(_1qa|_1qa>>>2)>>>0,_1qc=(_1qb|_1qb>>>4)>>>0,_1qd=(_1qc|_1qc>>>8)>>>0,_1qe=(_1qd|_1qd>>>16)>>>0,_1qf=(_1qe^_1qe>>>1)>>>0&4294967295,_1qg=_1qf>>>0;return ((_1q2>>>0&_1qg)>>>0==0)?new T4(0,(_1q2>>>0&((_1qg-1>>>0^4294967295)>>>0^_1qg)>>>0)>>>0&4294967295,_1qf,E(new T2(1,_1q2,_1q3)),E(new T4(0,_1q4,_1q5,E(_1q6),E(_1q7)))):new T4(0,(_1q2>>>0&((_1qg-1>>>0^4294967295)>>>0^_1qg)>>>0)>>>0&4294967295,_1qf,E(new T4(0,_1q4,_1q5,E(_1q6),E(_1q7))),E(new T2(1,_1q2,_1q3)));}},_1qh=function(_1qi,_1qj,_1qk,_1ql,_1qm){var _1qn=E(_1qm);switch(_1qn._){case 0:var _1qo=_1qn.a,_1qp=_1qn.b,_1qq=_1qn.c,_1qr=_1qn.d;if(_1qj>>>0<=_1qp>>>0){if(_1qp>>>0<=_1qj>>>0){if(_1qi!=_1qo){var _1qs=(_1qi>>>0^_1qo>>>0)>>>0,_1qt=(_1qs|_1qs>>>1)>>>0,_1qu=(_1qt|_1qt>>>2)>>>0,_1qv=(_1qu|_1qu>>>4)>>>0,_1qw=(_1qv|_1qv>>>8)>>>0,_1qx=(_1qw|_1qw>>>16)>>>0,_1qy=(_1qx^_1qx>>>1)>>>0&4294967295,_1qz=_1qy>>>0;return ((_1qi>>>0&_1qz)>>>0==0)?new T4(0,(_1qi>>>0&((_1qz-1>>>0^4294967295)>>>0^_1qz)>>>0)>>>0&4294967295,_1qy,E(new T4(0,_1qi,_1qj,E(_1qk),E(_1ql))),E(_1qn)):new T4(0,(_1qi>>>0&((_1qz-1>>>0^4294967295)>>>0^_1qz)>>>0)>>>0&4294967295,_1qy,E(_1qn),E(new T4(0,_1qi,_1qj,E(_1qk),E(_1ql))));}else{return new T4(0,_1qi,_1qj,E(B(_1qA(_1qk,_1qq))),E(B(_1qA(_1ql,_1qr))));}}else{var _1qB=_1qp>>>0;if(((_1qi>>>0&((_1qB-1>>>0^4294967295)>>>0^_1qB)>>>0)>>>0&4294967295)==_1qo){return ((_1qi>>>0&_1qB)>>>0==0)?new T4(0,_1qo,_1qp,E(B(_1qh(_1qi,_1qj,_1qk,_1ql,_1qq))),E(_1qr)):new T4(0,_1qo,_1qp,E(_1qq),E(B(_1qh(_1qi,_1qj,_1qk,_1ql,_1qr))));}else{var _1qC=(_1qi>>>0^_1qo>>>0)>>>0,_1qD=(_1qC|_1qC>>>1)>>>0,_1qE=(_1qD|_1qD>>>2)>>>0,_1qF=(_1qE|_1qE>>>4)>>>0,_1qG=(_1qF|_1qF>>>8)>>>0,_1qH=(_1qG|_1qG>>>16)>>>0,_1qI=(_1qH^_1qH>>>1)>>>0&4294967295,_1qJ=_1qI>>>0;return ((_1qi>>>0&_1qJ)>>>0==0)?new T4(0,(_1qi>>>0&((_1qJ-1>>>0^4294967295)>>>0^_1qJ)>>>0)>>>0&4294967295,_1qI,E(new T4(0,_1qi,_1qj,E(_1qk),E(_1ql))),E(_1qn)):new T4(0,(_1qi>>>0&((_1qJ-1>>>0^4294967295)>>>0^_1qJ)>>>0)>>>0&4294967295,_1qI,E(_1qn),E(new T4(0,_1qi,_1qj,E(_1qk),E(_1ql))));}}}else{var _1qK=_1qj>>>0;if(((_1qo>>>0&((_1qK-1>>>0^4294967295)>>>0^_1qK)>>>0)>>>0&4294967295)==_1qi){return ((_1qo>>>0&_1qK)>>>0==0)?new T4(0,_1qi,_1qj,E(B(_1qL(_1qk,_1qo,_1qp,_1qq,_1qr))),E(_1ql)):new T4(0,_1qi,_1qj,E(_1qk),E(B(_1qL(_1ql,_1qo,_1qp,_1qq,_1qr))));}else{var _1qM=(_1qi>>>0^_1qo>>>0)>>>0,_1qN=(_1qM|_1qM>>>1)>>>0,_1qO=(_1qN|_1qN>>>2)>>>0,_1qP=(_1qO|_1qO>>>4)>>>0,_1qQ=(_1qP|_1qP>>>8)>>>0,_1qR=(_1qQ|_1qQ>>>16)>>>0,_1qS=(_1qR^_1qR>>>1)>>>0&4294967295,_1qT=_1qS>>>0;return ((_1qi>>>0&_1qT)>>>0==0)?new T4(0,(_1qi>>>0&((_1qT-1>>>0^4294967295)>>>0^_1qT)>>>0)>>>0&4294967295,_1qS,E(new T4(0,_1qi,_1qj,E(_1qk),E(_1ql))),E(_1qn)):new T4(0,(_1qi>>>0&((_1qT-1>>>0^4294967295)>>>0^_1qT)>>>0)>>>0&4294967295,_1qS,E(_1qn),E(new T4(0,_1qi,_1qj,E(_1qk),E(_1ql))));}}break;case 1:return new F(function(){return _1q1(_1qn.a,_1qn.b,_1qi,_1qj,_1qk,_1ql);});break;default:return new T4(0,_1qi,_1qj,E(_1qk),E(_1ql));}},_1qL=function(_1qU,_1qV,_1qW,_1qX,_1qY){var _1qZ=E(_1qU);switch(_1qZ._){case 0:var _1r0=_1qZ.a,_1r1=_1qZ.b,_1r2=_1qZ.c,_1r3=_1qZ.d;if(_1r1>>>0<=_1qW>>>0){if(_1qW>>>0<=_1r1>>>0){if(_1r0!=_1qV){var _1r4=(_1r0>>>0^_1qV>>>0)>>>0,_1r5=(_1r4|_1r4>>>1)>>>0,_1r6=(_1r5|_1r5>>>2)>>>0,_1r7=(_1r6|_1r6>>>4)>>>0,_1r8=(_1r7|_1r7>>>8)>>>0,_1r9=(_1r8|_1r8>>>16)>>>0,_1ra=(_1r9^_1r9>>>1)>>>0&4294967295,_1rb=_1ra>>>0;return ((_1r0>>>0&_1rb)>>>0==0)?new T4(0,(_1r0>>>0&((_1rb-1>>>0^4294967295)>>>0^_1rb)>>>0)>>>0&4294967295,_1ra,E(_1qZ),E(new T4(0,_1qV,_1qW,E(_1qX),E(_1qY)))):new T4(0,(_1r0>>>0&((_1rb-1>>>0^4294967295)>>>0^_1rb)>>>0)>>>0&4294967295,_1ra,E(new T4(0,_1qV,_1qW,E(_1qX),E(_1qY))),E(_1qZ));}else{return new T4(0,_1r0,_1r1,E(B(_1qA(_1r2,_1qX))),E(B(_1qA(_1r3,_1qY))));}}else{var _1rc=_1qW>>>0;if(((_1r0>>>0&((_1rc-1>>>0^4294967295)>>>0^_1rc)>>>0)>>>0&4294967295)==_1qV){return ((_1r0>>>0&_1rc)>>>0==0)?new T4(0,_1qV,_1qW,E(B(_1qh(_1r0,_1r1,_1r2,_1r3,_1qX))),E(_1qY)):new T4(0,_1qV,_1qW,E(_1qX),E(B(_1qh(_1r0,_1r1,_1r2,_1r3,_1qY))));}else{var _1rd=(_1r0>>>0^_1qV>>>0)>>>0,_1re=(_1rd|_1rd>>>1)>>>0,_1rf=(_1re|_1re>>>2)>>>0,_1rg=(_1rf|_1rf>>>4)>>>0,_1rh=(_1rg|_1rg>>>8)>>>0,_1ri=(_1rh|_1rh>>>16)>>>0,_1rj=(_1ri^_1ri>>>1)>>>0&4294967295,_1rk=_1rj>>>0;return ((_1r0>>>0&_1rk)>>>0==0)?new T4(0,(_1r0>>>0&((_1rk-1>>>0^4294967295)>>>0^_1rk)>>>0)>>>0&4294967295,_1rj,E(_1qZ),E(new T4(0,_1qV,_1qW,E(_1qX),E(_1qY)))):new T4(0,(_1r0>>>0&((_1rk-1>>>0^4294967295)>>>0^_1rk)>>>0)>>>0&4294967295,_1rj,E(new T4(0,_1qV,_1qW,E(_1qX),E(_1qY))),E(_1qZ));}}}else{var _1rl=_1r1>>>0;if(((_1qV>>>0&((_1rl-1>>>0^4294967295)>>>0^_1rl)>>>0)>>>0&4294967295)==_1r0){return ((_1qV>>>0&_1rl)>>>0==0)?new T4(0,_1r0,_1r1,E(B(_1qL(_1r2,_1qV,_1qW,_1qX,_1qY))),E(_1r3)):new T4(0,_1r0,_1r1,E(_1r2),E(B(_1qL(_1r3,_1qV,_1qW,_1qX,_1qY))));}else{var _1rm=(_1r0>>>0^_1qV>>>0)>>>0,_1rn=(_1rm|_1rm>>>1)>>>0,_1ro=(_1rn|_1rn>>>2)>>>0,_1rp=(_1ro|_1ro>>>4)>>>0,_1rq=(_1rp|_1rp>>>8)>>>0,_1rr=(_1rq|_1rq>>>16)>>>0,_1rs=(_1rr^_1rr>>>1)>>>0&4294967295,_1rt=_1rs>>>0;return ((_1r0>>>0&_1rt)>>>0==0)?new T4(0,(_1r0>>>0&((_1rt-1>>>0^4294967295)>>>0^_1rt)>>>0)>>>0&4294967295,_1rs,E(_1qZ),E(new T4(0,_1qV,_1qW,E(_1qX),E(_1qY)))):new T4(0,(_1r0>>>0&((_1rt-1>>>0^4294967295)>>>0^_1rt)>>>0)>>>0&4294967295,_1rs,E(new T4(0,_1qV,_1qW,E(_1qX),E(_1qY))),E(_1qZ));}}break;case 1:return new F(function(){return _1q1(_1qZ.a,_1qZ.b,_1qV,_1qW,_1qX,_1qY);});break;default:return new T4(0,_1qV,_1qW,E(_1qX),E(_1qY));}},_1qA=function(_1ru,_1rv){var _1rw=E(_1ru);switch(_1rw._){case 0:var _1rx=_1rw.a,_1ry=_1rw.b,_1rz=_1rw.c,_1rA=_1rw.d,_1rB=E(_1rv);switch(_1rB._){case 0:var _1rC=_1rB.a,_1rD=_1rB.b,_1rE=_1rB.c,_1rF=_1rB.d;if(_1ry>>>0<=_1rD>>>0){if(_1rD>>>0<=_1ry>>>0){if(_1rx!=_1rC){var _1rG=(_1rx>>>0^_1rC>>>0)>>>0,_1rH=(_1rG|_1rG>>>1)>>>0,_1rI=(_1rH|_1rH>>>2)>>>0,_1rJ=(_1rI|_1rI>>>4)>>>0,_1rK=(_1rJ|_1rJ>>>8)>>>0,_1rL=(_1rK|_1rK>>>16)>>>0,_1rM=(_1rL^_1rL>>>1)>>>0&4294967295,_1rN=_1rM>>>0;return ((_1rx>>>0&_1rN)>>>0==0)?new T4(0,(_1rx>>>0&((_1rN-1>>>0^4294967295)>>>0^_1rN)>>>0)>>>0&4294967295,_1rM,E(_1rw),E(_1rB)):new T4(0,(_1rx>>>0&((_1rN-1>>>0^4294967295)>>>0^_1rN)>>>0)>>>0&4294967295,_1rM,E(_1rB),E(_1rw));}else{return new T4(0,_1rx,_1ry,E(B(_1qA(_1rz,_1rE))),E(B(_1qA(_1rA,_1rF))));}}else{var _1rO=_1rD>>>0;if(((_1rx>>>0&((_1rO-1>>>0^4294967295)>>>0^_1rO)>>>0)>>>0&4294967295)==_1rC){return ((_1rx>>>0&_1rO)>>>0==0)?new T4(0,_1rC,_1rD,E(B(_1qh(_1rx,_1ry,_1rz,_1rA,_1rE))),E(_1rF)):new T4(0,_1rC,_1rD,E(_1rE),E(B(_1qh(_1rx,_1ry,_1rz,_1rA,_1rF))));}else{var _1rP=(_1rx>>>0^_1rC>>>0)>>>0,_1rQ=(_1rP|_1rP>>>1)>>>0,_1rR=(_1rQ|_1rQ>>>2)>>>0,_1rS=(_1rR|_1rR>>>4)>>>0,_1rT=(_1rS|_1rS>>>8)>>>0,_1rU=(_1rT|_1rT>>>16)>>>0,_1rV=(_1rU^_1rU>>>1)>>>0&4294967295,_1rW=_1rV>>>0;return ((_1rx>>>0&_1rW)>>>0==0)?new T4(0,(_1rx>>>0&((_1rW-1>>>0^4294967295)>>>0^_1rW)>>>0)>>>0&4294967295,_1rV,E(_1rw),E(_1rB)):new T4(0,(_1rx>>>0&((_1rW-1>>>0^4294967295)>>>0^_1rW)>>>0)>>>0&4294967295,_1rV,E(_1rB),E(_1rw));}}}else{var _1rX=_1ry>>>0;if(((_1rC>>>0&((_1rX-1>>>0^4294967295)>>>0^_1rX)>>>0)>>>0&4294967295)==_1rx){return ((_1rC>>>0&_1rX)>>>0==0)?new T4(0,_1rx,_1ry,E(B(_1qL(_1rz,_1rC,_1rD,_1rE,_1rF))),E(_1rA)):new T4(0,_1rx,_1ry,E(_1rz),E(B(_1qL(_1rA,_1rC,_1rD,_1rE,_1rF))));}else{var _1rY=(_1rx>>>0^_1rC>>>0)>>>0,_1rZ=(_1rY|_1rY>>>1)>>>0,_1s0=(_1rZ|_1rZ>>>2)>>>0,_1s1=(_1s0|_1s0>>>4)>>>0,_1s2=(_1s1|_1s1>>>8)>>>0,_1s3=(_1s2|_1s2>>>16)>>>0,_1s4=(_1s3^_1s3>>>1)>>>0&4294967295,_1s5=_1s4>>>0;return ((_1rx>>>0&_1s5)>>>0==0)?new T4(0,(_1rx>>>0&((_1s5-1>>>0^4294967295)>>>0^_1s5)>>>0)>>>0&4294967295,_1s4,E(_1rw),E(_1rB)):new T4(0,(_1rx>>>0&((_1s5-1>>>0^4294967295)>>>0^_1s5)>>>0)>>>0&4294967295,_1s4,E(_1rB),E(_1rw));}}break;case 1:return new F(function(){return _1q1(_1rB.a,_1rB.b,_1rx,_1ry,_1rz,_1rA);});break;default:return E(_1rw);}break;case 1:return new F(function(){return _1oe(_1rw.a,_1rw.b,_1rv);});break;default:return E(_1rv);}},_1s6=function(_1s7,_1s8){var _1s9=E(_1s7),_1sa=B(_16o(_12I,_1qA,_1s9.a,_1s9.b,_1s8));return new T2(0,_1sa.a,_1sa.b);},_1sb=new T(function(){return B(unCStr("Int"));}),_1sc=function(_1sd,_1se,_1sf){return new F(function(){return _eX(_ea,new T2(0,_1se,_1sf),_1sd,_1sb);});},_1sg=function(_1sh,_1si,_1sj){return new F(function(){return _eX(_ea,new T2(0,_1sh,_1si),_1sj,_1sb);});},_1sk=new T(function(){return B(_1pG(_UD,_4));}),_1sl=function(_1sm,_1sn){var _1so=function(_1sp,_1sq,_1sr){return new F(function(){return A2(_1sm,_1sq,_1sr);});},_1ss=function(_1st,_1su){while(1){var _1sv=E(_1su);if(!_1sv._){return E(_1st);}else{var _1sw=B(_1jY(_1so,_1st,_1sv.a));_1st=_1sw;_1su=_1sv.b;continue;}}};return new F(function(){return _1ss(_UD,_1sn);});},_1sx=function(_1sy,_1sz,_1sA,_1sB,_1sC,_1sD,_1sE,_1sF,_1sG){var _1sH=new T(function(){return B(_1p5(_UD,_18E,_1sE));}),_1sI=new T(function(){var _1sJ=function(_1sK,_1sL){while(1){var _1sM=B((function(_1sN,_1sO){var _1sP=E(_1sO);if(!_1sP._){var _1sQ=_1sP.d,_1sR=new T(function(){var _1sS=E(_1sP.b);if(!_1sS._){var _1sT=_1sS.a;if(!E(_1sS.b)._){var _1sU=new T(function(){var _1sV=E(_1sA),_1sW=_1sV.c,_1sX=E(_1sV.a),_1sY=E(_1sV.b);if(_1sX>_1sT){return B(_1sc(_1sT,_1sX,_1sY));}else{if(_1sT>_1sY){return B(_1sc(_1sT,_1sX,_1sY));}else{var _1sZ=_1sT-_1sX|0;if(0>_1sZ){return B(_1pQ(_1sZ,_1sW));}else{if(_1sZ>=_1sW){return B(_1pQ(_1sZ,_1sW));}else{var _1t0=E(_1sV.d[_1sZ]),_1t1=_1t0.d,_1t2=E(_1t0.b),_1t3=E(_1t0.c);if(_1t2<=_1t3){var _1t4=new T(function(){var _1t5=B(_14p(_12I,_1nk,new T2(1,new T2(0,_1pX,new T2(1,_1sT&(-32),1<<(_1sT&31)>>>0)),_4)));return new T2(0,_1t5.a,_1t5.b);}),_1t6=new T(function(){var _1t7=B(_14p(_12I,_1nk,new T2(1,new T2(0,_4,new T2(1,_1sT&(-32),1<<(_1sT&31)>>>0)),_4)));return new T2(0,_1t7.a,_1t7.b);}),_1t8=new T2(1,_1sT&(-32),1<<(_1sT&31)>>>0),_1t9=new T(function(){var _1ta=B(_14p(_12I,_1nk,new T2(1,new T2(0,_4,_1t8),_4)));return new T2(0,_1ta.a,_1ta.b);}),_1tb=new T(function(){var _1tc=B(_14p(_12I,_1nk,new T2(1,new T2(0,_1pZ,new T2(1,_1sT&(-32),1<<(_1sT&31)>>>0)),_4)));return new T2(0,_1tc.a,_1tc.b);}),_1td=function(_1te){var _1tf=E(_1te);if(!_1tf._){return E(_1t9);}else{var _1tg=_1tf.b,_1th=E(_1tf.a);switch(_1th._){case 3:var _1ti=B(_14p(_12I,_1nk,new T2(1,new T2(0,new T2(1,_1th.a,_4),_1t8),_4)));return new T2(0,_1ti.a,_1ti.b);case 4:var _1tj=new T(function(){var _1tk=function(_1tl){var _1tm=E(_1tl);return (_1tm._==0)?__Z:new T2(1,new T(function(){return B(_1td(B(_0(E(_1tm.a).a,_1tg))));}),new T(function(){return B(_1tk(_1tm.b));}));};return B(_1tk(_1th.b));}),_1tn=B(_18u(_12I,_1qA,new T2(1,new T(function(){return B(_1td(B(_0(_1th.a,_1tg))));}),_1tj)));return new T2(0,_1tn.a,_1tn.b);case 5:return E(_1tb);case 6:return E(_1nn);case 7:return E(_1t6);case 8:return E(_1t6);case 9:return E(_1t4);case 10:return E(_1t4);default:return E(_1q0);}}},_1to=new T(function(){return B(_1td(_4));}),_1tp=function(_1tq){var _1tr=new T(function(){var _1ts=E(_1sD),_1tt=_1ts.c,_1tu=E(_1ts.a),_1tv=E(_1ts.b);if(_1t2>_1tq){return B(_1sg(_1t2,_1t3,_1tq));}else{if(_1tq>_1t3){return B(_1sg(_1t2,_1t3,_1tq));}else{var _1tw=_1tq-_1t2|0;if(0>_1tw){return B(_1pQ(_1tw,_1t1));}else{if(_1tw>=_1t1){return B(_1pQ(_1tw,_1t1));}else{var _1tx=_1t0.e["v"]["i32"][_1tw];if(_1tu>_1tx){return B(_1sc(_1tx,_1tu,_1tv));}else{if(_1tx>_1tv){return B(_1sc(_1tx,_1tu,_1tv));}else{var _1ty=_1tx-_1tu|0;if(0>_1ty){return B(_1pQ(_1ty,_1tt));}else{if(_1ty>=_1tt){return B(_1pQ(_1ty,_1tt));}else{var _1tz=E(_1ts.d[_1ty]),_1tA=_1tz.c-1|0;if(0<=_1tA){var _1tB=function(_1tC){return new T2(1,new T(function(){return E(_1tz.d[_1tC]);}),new T(function(){if(_1tC!=_1tA){return B(_1tB(_1tC+1|0));}else{return __Z;}}));};return B(_1td(B(_1tB(0))));}else{return E(_1to);}}}}}}}}}});return new T2(1,new T2(0,_1tq,_1tr),new T(function(){if(_1tq!=_1t3){return B(_1tp(_1tq+1|0));}else{return __Z;}}));};return B(_1pG(_UD,B(_1tp(_1t2))));}else{return E(_1sk);}}}}}});return new T2(1,_1sU,new T(function(){return B(_1sJ(_1sN,_1sQ));}));}else{return B(_1sJ(_1sN,_1sQ));}}else{return B(_1sJ(_1sN,_1sQ));}},1);_1sK=_1sR;_1sL=_1sP.c;return __continue;}else{return E(_1sN);}})(_1sK,_1sL));if(_1sM!=__continue){return _1sM;}}},_1tD=function(_1tE,_1tF,_1tG){while(1){var _1tH=E(_1tG);switch(_1tH._){case 0:var _1tI=B(_1tD(_1tE,_1tF,_1tH.d));_1tE=_1tI.a;_1tF=_1tI.b;_1tG=_1tH.c;continue;case 1:var _1tJ=_1tH.a,_1tK=B(_166(_1pM,_1tH.b)),_1tL=E(_1tK.a);if(!_1tL._){var _1tM=B(_14A(_1tJ,B(_1sl(_1s6,B(_1sJ(_4,_1tL)))),_1tE));}else{var _1tM=E(_1tE);}var _1tN=E(_1tK.b);if(!_1tN._){var _1tO=B(_14A(_1tJ,_1tN,_1tF));}else{var _1tO=E(_1tF);}return new T2(0,_1tM,_1tO);default:return new T2(0,_1tE,_1tF);}}},_1tP=E(_1sH);if(!_1tP._){var _1tQ=_1tP.c,_1tR=_1tP.d;if(_1tP.b>=0){var _1tS=B(_1tD(_UD,_UD,_1tR)),_1tT=B(_1tD(_1tS.a,_1tS.b,_1tQ));return new T2(0,_1tT.a,_1tT.b);}else{var _1tU=B(_1tD(_UD,_UD,_1tQ)),_1tV=B(_1tD(_1tU.a,_1tU.b,_1tR));return new T2(0,_1tV.a,_1tV.b);}}else{var _1tW=B(_1tD(_UD,_UD,_1tP));return new T2(0,_1tW.a,_1tW.b);}}),_1tX=new T(function(){var _1tY=function(_1tZ){var _1u0=E(_1tZ);switch(_1u0._){case 0:var _1u1=_1u0.a;return new T2(1,new T(function(){var _1u2=E(_1sA),_1u3=_1u2.c,_1u4=E(_1u2.a),_1u5=E(_1u2.b);if(_1u4>_1u1){return B(_1sc(_1u1,_1u4,_1u5));}else{if(_1u1>_1u5){return B(_1sc(_1u1,_1u4,_1u5));}else{var _1u6=_1u1-_1u4|0;if(0>_1u6){return B(_1pQ(_1u6,_1u3));}else{if(_1u6>=_1u3){return B(_1pQ(_1u6,_1u3));}else{return E(E(_1u2.d[_1u6]).a);}}}}}),_4);case 1:var _1u7=B(_151(_1u0.a,_1sH));if(!_1u7._){return __Z;}else{return new F(function(){return _1u8(_4,_1u7.a);});}break;default:return E(_1pV);}},_1u8=function(_1u9,_1ua){while(1){var _1ub=B((function(_1uc,_1ud){var _1ue=E(_1ud);if(!_1ue._){var _1uf=new T(function(){return B(_0(B(_1tY(_1ue.b)),new T(function(){return B(_1u8(_1uc,_1ue.d));},1)));},1);_1u9=_1uf;_1ua=_1ue.c;return __continue;}else{return E(_1uc);}})(_1u9,_1ua));if(_1ub!=__continue){return _1ub;}}},_1ug=function(_1uh,_1ui){while(1){var _1uj=B((function(_1uk,_1ul){var _1um=E(_1ul);switch(_1um._){case 0:_1uh=new T(function(){return B(_1ug(_1uk,_1um.d));},1);_1ui=_1um.c;return __continue;case 1:var _1un=function(_1uo,_1up){while(1){var _1uq=B((function(_1ur,_1us){var _1ut=E(_1us);if(!_1ut._){var _1uu=_1ut.b,_1uv=new T(function(){var _1uw=new T(function(){return B(_1un(_1ur,_1ut.d));}),_1ux=function(_1uy){var _1uz=E(_1uy);return (_1uz._==0)?E(_1uw):new T2(1,new T2(0,_1uz.a,new T2(1,_1um.a,new T4(0,1,E(_1uu),E(_MR),E(_MR)))),new T(function(){return B(_1ux(_1uz.b));}));};return B(_1ux(B(_1tY(_1uu))));},1);_1uo=_1uv;_1up=_1ut.c;return __continue;}else{return E(_1ur);}})(_1uo,_1up));if(_1uq!=__continue){return _1uq;}}};return new F(function(){return _1un(_1uk,_1um.b);});break;default:return E(_1uk);}})(_1uh,_1ui));if(_1uj!=__continue){return _1uj;}}},_1uA=E(_1sH);if(!_1uA._){var _1uB=_1uA.c,_1uC=_1uA.d;if(_1uA.b>=0){return B(_13j(_1ng,B(_1ug(new T(function(){return B(_1ug(_4,_1uC));},1),_1uB))));}else{return B(_13j(_1ng,B(_1ug(new T(function(){return B(_1ug(_4,_1uB));},1),_1uC))));}}else{return B(_13j(_1ng,B(_1ug(_4,_1uA))));}});return {_:0,a:_1sy,b:_1sz,c:_1sA,d:_1sB,e:_1sC,f:_1sD,g:_1sE,h:new T(function(){return E(E(_1sI).b);}),i:_1tX,j:_1sF,k:new T(function(){return E(E(_1sI).a);}),l:_1sG};},_1uD=function(_1uE){var _1uF=E(_1uE);return new F(function(){return _1sx(_1uF.a,_1uF.b,_1uF.c,_1uF.d,_1uF.e,_1uF.f,_1uF.g,_1uF.j,_1uF.l);});},_1uG=0,_1uH=function(_1uI){var _1uJ=E(_1uI);return new T3(0,_1uJ.a,_1uJ.b,_1uG);},_1uK=function(_1uL){var _1uM=E(_1uL);return new T4(0,_1uM.a,_1uM.b,new T(function(){var _1uN=E(_1uM.c);if(!_1uN._){return __Z;}else{return new T1(1,new T2(0,_1uN.a,_4));}}),_1uM.d);},_1uO=0,_1uP=new T(function(){return B(unCStr("Negative range size"));}),_1uQ=function(_1uR){var _1uS=function(_){var _1uT=B(_v0(_1uR,0))-1|0,_1uU=function(_1uV){if(_1uV>=0){var _1uW=newArr(_1uV,_VA),_1uX=_1uW,_1uY=function(_1uZ){var _1v0=function(_1v1,_1v2,_){while(1){if(_1v1!=_1uZ){var _1v3=E(_1v2);if(!_1v3._){return _5;}else{var _=_1uX[_1v1]=_1v3.a,_1v4=_1v1+1|0;_1v1=_1v4;_1v2=_1v3.b;continue;}}else{return _5;}}},_1v5=B(_1v0(0,_1uR,_));return new T4(0,E(_1uO),E(_1uT),_1uV,_1uX);};if(0>_1uT){return new F(function(){return _1uY(0);});}else{var _1v6=_1uT+1|0;if(_1v6>=0){return new F(function(){return _1uY(_1v6);});}else{return new F(function(){return err(_1uP);});}}}else{return E(_VC);}};if(0>_1uT){var _1v7=B(_1uU(0)),_1v8=E(_1v7),_1v9=_1v8.d;return new T4(0,E(_1v8.a),E(_1v8.b),_1v8.c,_1v9);}else{var _1va=B(_1uU(_1uT+1|0)),_1vb=E(_1va),_1vc=_1vb.d;return new T4(0,E(_1vb.a),E(_1vb.b),_1vb.c,_1vc);}};return new F(function(){return _8O(_1uS);});},_1vd=function(_1ve){return new T1(3,_1ve);},_1vf=function(_1vg,_1vh){var _1vi=new T(function(){var _1vj=E(_1vg),_1vk=B(_fo(_1vj.a,_1vj.b,_1vj.c,E(_1vh))),_1vl=B(_gl(E(_1vk.a)&4294967295,_g9,_1vj,_1vk.b));return new T2(0,_1vl.a,_1vl.b);});return new T2(0,new T1(3,new T(function(){return E(E(_1vi).a);})),new T(function(){return E(E(_1vi).b);}));},_1vm=function(_1vn,_1vo){var _1vp=B(_1vf(_1vn,_1vo));return new T2(0,_1vp.a,_1vp.b);},_1vq=function(_1vr,_1vs){var _1vt=E(_1vr),_1vu=B(_fo(_1vt.a,_1vt.b,_1vt.c,E(_1vs))),_1vv=B(_gl(E(_1vu.a)&4294967295,_g9,_1vt,_1vu.b));return new T2(0,_1vv.a,_1vv.b);},_1vw=function(_1vx,_1vy,_1vz,_1vA){var _1vB=B(_ZN(_1vm,new T3(0,_1vx,_1vy,_1vz),_1vA)),_1vC=B(_fo(_1vx,_1vy,_1vz,E(_1vB.b))),_1vD=B(_gl(E(_1vC.a)&4294967295,_1vq,new T3(0,_1vx,_1vy,_1vz),_1vC.b));return new T2(0,new T2(0,_1vB.a,_1vD.a),_1vD.b);},_1vE=function(_1vF,_1vG){var _1vH=E(_1vF),_1vI=B(_1vw(_1vH.a,_1vH.b,_1vH.c,_1vG));return new T2(0,_1vI.a,_1vI.b);},_1vJ=function(_1vK){var _1vL=new T(function(){return B(unAppCStr("getSymbol ",new T(function(){return B(_bZ(0,_1vK&4294967295,_4));})));});return new F(function(){return _10d(_1vL);});},_1vM=function(_1vN,_1vO,_1vP,_1vQ){var _1vR=B(_fi(_1vN,_1vO,_1vP,_1vQ)),_1vS=_1vR.b,_1vT=E(_1vR.a);switch(_1vT){case 0:var _1vU=new T(function(){var _1vV=B(_fo(_1vN,_1vO,_1vP,E(_1vS))),_1vW=B(_fo(_1vN,_1vO,_1vP,E(_1vV.b)));return new T2(0,new T(function(){return new T2(0,E(_1vV.a)&4294967295,E(_1vW.a)&4294967295);}),_1vW.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1vU).a);}),_4),new T(function(){return E(E(_1vU).b);}));case 1:var _1vX=new T(function(){var _1vY=B(_fo(_1vN,_1vO,_1vP,E(_1vS))),_1vZ=B(_fo(_1vN,_1vO,_1vP,E(_1vY.b)));return new T2(0,new T(function(){return new T2(1,E(_1vY.a)&4294967295,E(_1vZ.a)&4294967295);}),_1vZ.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1vX).a);}),_4),new T(function(){return E(E(_1vX).b);}));case 2:var _1w0=new T(function(){var _1w1=B(_fo(_1vN,_1vO,_1vP,E(_1vS))),_1w2=B(_fo(_1vN,_1vO,_1vP,E(_1w1.b)));return new T2(0,new T(function(){return new T2(2,E(_1w1.a)&4294967295,E(_1w2.a)&4294967295);}),_1w2.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1w0).a);}),_4),new T(function(){return E(E(_1w0).b);}));case 3:var _1w3=B(_fo(_1vN,_1vO,_1vP,E(_1vS))),_1w4=B(_gl(E(_1w3.a)&4294967295,_1vq,new T3(0,_1vN,_1vO,_1vP),_1w3.b));return new T2(0,new T(function(){return B(_G(_1vd,_1w4.a));}),_1w4.b);case 4:var _1w5=new T(function(){var _1w6=new T3(0,_1vN,_1vO,_1vP),_1w7=B(_ZN(_1vm,_1w6,_1vS)),_1w8=B(_ZN(_1vE,_1w6,_1w7.b));return new T2(0,new T2(4,_1w7.a,_1w8.a),_1w8.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1w5).a);}),_4),new T(function(){return E(E(_1w5).b);}));default:return new F(function(){return _1vJ(_1vT);});}},_1w9=function(_1wa,_1wb){var _1wc=E(_1wa),_1wd=B(_1vM(_1wc.a,_1wc.b,_1wc.c,E(_1wb)));return new T2(0,_1wd.a,_1wd.b);},_1we=function(_1wf){var _1wg=E(_1wf);if(!_1wg._){return __Z;}else{return new F(function(){return _0(_1wg.a,new T(function(){return B(_1we(_1wg.b));},1));});}},_1wh=function(_1wi,_1wj){var _1wk=new T(function(){var _1wl=B(_ZN(_1w9,_1wi,_1wj));return new T2(0,_1wl.a,_1wl.b);});return new T2(0,new T(function(){return B(_1uQ(B(_1we(E(_1wk).a))));}),new T(function(){return E(E(_1wk).b);}));},_1wm=function(_1wn,_1wo,_1wp,_1wq){var _1wr=B(_fo(_1wn,_1wo,_1wp,_1wq));return new F(function(){return _gl(E(_1wr.a)&4294967295,_g9,new T3(0,_1wn,_1wo,_1wp),_1wr.b);});},_1ws=function(_1wt,_1wu){var _1wv=E(_1wt),_1ww=B(_1wm(_1wv.a,_1wv.b,_1wv.c,E(_1wu)));return new T2(0,_1ww.a,_1ww.b);},_1wx=function(_1wy){var _1wz=E(_1wy);return (_1wz._==0)?__Z:new T2(1,new T2(0,_Mf,_1wz.a),new T(function(){return B(_1wx(_1wz.b));}));},_1wA=function(_1wB,_1wC,_1wD,_1wE){var _1wF=B(_fo(_1wB,_1wC,_1wD,_1wE)),_1wG=B(_gl(E(_1wF.a)&4294967295,_kv,new T3(0,_1wB,_1wC,_1wD),_1wF.b)),_1wH=B(_fo(_1wB,_1wC,_1wD,E(_1wG.b))),_1wI=new T(function(){return new T2(0,new T(function(){return B(_1wx(_1wG.a));}),E(_1wH.a)&4294967295);});return new T2(0,_1wI,_1wH.b);},_1wJ=function(_1wK,_1wL){var _1wM=E(_1wK),_1wN=B(_1wA(_1wM.a,_1wM.b,_1wM.c,E(_1wL)));return new T2(0,_1wN.a,_1wN.b);},_1wO=new T(function(){return B(unCStr("getProduction"));}),_1wP=new T(function(){return B(_10d(_1wO));}),_1wQ=function(_1wR,_1wS,_1wT,_1wU){var _1wV=B(_fi(_1wR,_1wS,_1wT,_1wU)),_1wW=_1wV.b;switch(E(_1wV.a)){case 0:var _1wX=B(_fo(_1wR,_1wS,_1wT,E(_1wW))),_1wY=B(_ZN(_1wJ,new T3(0,_1wR,_1wS,_1wT),_1wX.b));return new T2(0,new T(function(){return new T2(0,E(_1wX.a)&4294967295,_1wY.a);}),_1wY.b);case 1:var _1wZ=B(_fo(_1wR,_1wS,_1wT,E(_1wW)));return new T2(0,new T(function(){return new T1(1,E(_1wZ.a)&4294967295);}),_1wZ.b);default:return E(_1wP);}},_1x0=function(_1x1,_1x2){var _1x3=E(_1x1),_1x4=B(_1wQ(_1x3.a,_1x3.b,_1x3.c,E(_1x2)));return new T2(0,_1x4.a,_1x4.b);},_1x5=function(_1x6,_1x7){var _1x8=new T(function(){var _1x9=E(_1x6),_1xa=B(_fo(_1x9.a,_1x9.b,_1x9.c,E(_1x7)));return new T2(0,new T(function(){return E(_1xa.a)&4294967295;}),_1xa.b);}),_1xb=new T(function(){var _1xc=B(_ZN(_1x0,_1x6,new T(function(){return E(E(_1x8).b);},1)));return new T2(0,_1xc.a,_1xc.b);});return new T2(0,new T2(0,new T(function(){return E(E(_1x8).a);}),new T(function(){var _1xd=E(E(_1xb).a);if(!_1xd._){return new T0(1);}else{return B(_Pq(1,new T4(0,1,E(_1xd.a),E(_MR),E(_MR)),_1xd.b));}})),new T(function(){return E(E(_1xb).b);}));},_1xe=function(_1xf,_1xg){var _1xh=B(_1x5(_1xf,_1xg));return new T2(0,_1xh.a,_1xh.b);},_1xi=new T(function(){return B(err(_1uP));}),_1xj=function(_1xk,_1xl,_1xm,_1xn){var _1xo=new T(function(){var _1xp=E(_1xm),_1xq=B(_fo(_1xp.a,_1xp.b,_1xp.c,E(_1xn))),_1xr=E(_1xq.a)&4294967295,_1xs=B(_ZF(_1xr,_1xl,_1xp,_1xq.b));return new T2(0,new T2(0,_1xr,_1xs.a),_1xs.b);}),_1xt=new T(function(){var _1xu=E(E(_1xo).a),_1xv=_1xu.b,_1xw=new T(function(){return E(_1xu.a)-1|0;});return B(A(_jT,[_1xk,_jB,new T2(0,_1uO,_1xw),new T(function(){var _1xx=E(_1xw);if(0>_1xx){return B(_jV(B(_iF(0,-1)),_1xv));}else{var _1xy=_1xx+1|0;if(_1xy>=0){return B(_jV(B(_iF(0,_1xy-1|0)),_1xv));}else{return E(_1xi);}}})]));});return new T2(0,_1xt,new T(function(){return E(E(_1xo).b);}));},_1xz=function(_1xA,_1xB,_1xC,_1xD){var _1xE=B(_fo(_1xA,_1xB,_1xC,_1xD));return new F(function(){return _gl(E(_1xE.a)&4294967295,_g9,new T3(0,_1xA,_1xB,_1xC),_1xE.b);});},_1xF=function(_1xG,_1xH){var _1xI=E(_1xG),_1xJ=B(_1xz(_1xI.a,_1xI.b,_1xI.c,E(_1xH)));return new T2(0,_1xJ.a,_1xJ.b);},_1xK=function(_1xL,_1xM,_1xN,_1xO){var _1xP=B(_fo(_1xL,_1xM,_1xN,_1xO)),_1xQ=B(_fo(_1xL,_1xM,_1xN,E(_1xP.b))),_1xR=B(_1xj(_ij,_1xF,new T3(0,_1xL,_1xM,_1xN),_1xQ.b));return new T2(0,new T(function(){var _1xS=E(_1xR.a);return new T6(0,E(_1xP.a)&4294967295,E(_1xQ.a)&4294967295,E(_1xS.a),E(_1xS.b),_1xS.c,_1xS.d);}),_1xR.b);},_1xT=function(_1xU,_1xV){var _1xW=E(_1xU),_1xX=B(_1xK(_1xW.a,_1xW.b,_1xW.c,E(_1xV)));return new T2(0,_1xX.a,_1xX.b);},_1xY=0,_1xZ=new T(function(){return B(unCStr("Negative range size"));}),_1y0=function(_1y1){var _1y2=B(_v0(_1y1,0)),_1y3=new T(function(){var _1y4=function(_){var _1y5=_1y2-1|0,_1y6=function(_,_1y7){var _1y8=function(_1y9){var _1ya=_1y9-1|0;if(0<=_1ya){var _1yb=function(_1yc,_){while(1){var _=E(_1y7).d["v"]["w8"][_1yc]=0;if(_1yc!=_1ya){var _1yd=_1yc+1|0;_1yc=_1yd;continue;}else{return _5;}}},_1ye=B(_1yb(0,_));return _1y7;}else{return _1y7;}};if(0>_1y5){return new F(function(){return _1y8(0);});}else{var _1yf=_1y5+1|0;if(_1yf>=0){return new F(function(){return _1y8(_1yf);});}else{return new F(function(){return err(_1xZ);});}}},_1yg=function(_,_1yh,_1yi,_1yj,_1yk){var _1yl=function(_1ym){var _1yn=function(_1yo,_1yp,_){while(1){if(_1yo!=_1ym){var _1yq=E(_1yp);if(!_1yq._){return _5;}else{var _=_1yk["v"]["w8"][_1yo]=E(_1yq.a),_1yr=_1yo+1|0;_1yo=_1yr;_1yp=_1yq.b;continue;}}else{return _5;}}},_1ys=B(_1yn(0,_1y1,_));return new T4(0,E(_1yh),E(_1yi),_1yj,_1yk);};if(0>_1y5){return new F(function(){return _1yl(0);});}else{var _1yt=_1y5+1|0;if(_1yt>=0){return new F(function(){return _1yl(_1yt);});}else{return new F(function(){return err(_1xZ);});}}};if(0>_1y5){var _1yu=newByteArr(0),_1yv=B(_1y6(_,new T4(0,E(_1xY),E(_1y5),0,_1yu))),_1yw=E(_1yv);return new F(function(){return _1yg(_,_1yw.a,_1yw.b,_1yw.c,_1yw.d);});}else{var _1yx=_1y5+1|0,_1yy=newByteArr(_1yx),_1yz=B(_1y6(_,new T4(0,E(_1xY),E(_1y5),_1yx,_1yy))),_1yA=E(_1yz);return new F(function(){return _1yg(_,_1yA.a,_1yA.b,_1yA.c,_1yA.d);});}};return B(_8O(_1y4));});return new T3(0,0,_1y2,_1y3);},_1yB=function(_1yC){return new F(function(){return _bZ(0,E(_1yC)&4294967295,_4);});},_1yD=function(_1yE,_1yF){return new F(function(){return _bZ(0,E(_1yE)&4294967295,_1yF);});},_1yG=function(_1yH,_1yI){return new F(function(){return _3X(_1yD,_1yH,_1yI);});},_1yJ=function(_1yK,_1yL,_1yM){return new F(function(){return _bZ(E(_1yK),E(_1yL)&4294967295,_1yM);});},_1yN=new T3(0,_1yJ,_1yB,_1yG),_1yO=new T(function(){return B(unCStr("Word8"));}),_1yP=0,_1yQ=255,_1yR=new T2(0,_1yP,_1yQ),_1yS=new T2(1,_bX,_4),_1yT=function(_1yU,_1yV,_1yW,_1yX){var _1yY=new T(function(){var _1yZ=new T(function(){var _1z0=new T(function(){var _1z1=new T(function(){var _1z2=new T(function(){var _1z3=E(_1yW),_1z4=new T(function(){return B(A3(_em,_ec,new T2(1,new T(function(){return B(A3(_ey,_1yX,_ex,_1z3.a));}),new T2(1,new T(function(){return B(A3(_ey,_1yX,_ex,_1z3.b));}),_4)),_1yS));});return new T2(1,_bY,_1z4);});return B(unAppCStr(") is outside of bounds ",_1z2));},1);return B(_0(B(_bZ(0,E(_1yV),_4)),_1z1));});return B(unAppCStr("}: tag (",_1z0));},1);return B(_0(_1yU,_1yZ));});return new F(function(){return err(B(unAppCStr("Enum.toEnum{",_1yY)));});},_1z5=function(_1z6,_1z7,_1z8,_1z9){return new F(function(){return _1yT(_1z7,_1z8,_1z9,_1z6);});},_1za=function(_1zb){return new F(function(){return _1z5(_1yN,_1yO,_1zb,_1yR);});},_1zc=function(_1zd){if(_1zd<0){return new F(function(){return _1za(_1zd);});}else{if(_1zd>255){return new F(function(){return _1za(_1zd);});}else{return _1zd>>>0;}}},_1ze=function(_1zf){return new F(function(){return _1zc(E(_1zf));});},_1zg=function(_1zh){var _1zi=E(_1zh);if(!_1zi._){return __Z;}else{var _1zj=_1zi.b,_1zk=E(_1zi.a),_1zl=function(_1zm){return (_1zk>=2048)?new T2(1,new T(function(){var _1zn=224+B(_n8(_1zk,4096))|0;if(_1zn>>>0>1114111){return B(_fQ(_1zn));}else{return _1zn;}}),new T2(1,new T(function(){var _1zo=128+B(_n8(B(_oc(_1zk,4096)),64))|0;if(_1zo>>>0>1114111){return B(_fQ(_1zo));}else{return _1zo;}}),new T2(1,new T(function(){var _1zp=128+B(_oc(_1zk,64))|0;if(_1zp>>>0>1114111){return B(_fQ(_1zp));}else{return _1zp;}}),new T(function(){return B(_1zg(_1zj));})))):new T2(1,new T(function(){var _1zq=192+B(_n8(_1zk,64))|0;if(_1zq>>>0>1114111){return B(_fQ(_1zq));}else{return _1zq;}}),new T2(1,new T(function(){var _1zr=128+B(_oc(_1zk,64))|0;if(_1zr>>>0>1114111){return B(_fQ(_1zr));}else{return _1zr;}}),new T(function(){return B(_1zg(_1zj));})));};if(_1zk<=0){return new F(function(){return _1zl(_);});}else{if(_1zk>=128){return new F(function(){return _1zl(_);});}else{return new T2(1,_1zk,new T(function(){return B(_1zg(_1zj));}));}}}},_1zs=new T(function(){return B(unCStr("linref"));}),_1zt=new T(function(){return B(_1zg(_1zs));}),_1zu=new T(function(){return B(_G(_1ze,_1zt));}),_1zv=new T(function(){var _1zw=B(_1y0(_1zu));return new T3(0,_1zw.a,_1zw.b,_1zw.c);}),_1zx=function(_1zy,_1zz){var _1zA=E(_1zy),_1zB=B(_fz(_1zA.a,_1zA.b,_1zA.c,E(_1zz))),_1zC=B(_1xj(_m8,_kv,_1zA,_1zB.b));return new T2(0,new T(function(){var _1zD=E(_1zC.a);return new T5(0,_1zB.a,E(_1zD.a),E(_1zD.b),_1zD.c,_1zD.d);}),_1zC.b);},_1zE=new T(function(){return B(_1pG(_UD,_4));}),_1zF=new T2(0,0,0),_1zG=new T2(1,_1zF,_4),_1zH=new T(function(){return B(_1uQ(_1zG));}),_1zI=new T2(1,_1zH,_4),_1zJ=function(_1zK,_1zL,_1zM,_1zN){var _1zO=new T3(0,_1zK,_1zL,_1zM),_1zP=B(_ZW(_12e,_129,_1zO,_1zN)),_1zQ=B(_ZW(_12e,_1ws,_1zO,_1zP.b)),_1zR=B(_fo(_1zK,_1zL,_1zM,E(_1zQ.b))),_1zS=E(_1zR.a)&4294967295,_1zT=B(_ZF(_1zS,_1wh,_1zO,_1zR.b)),_1zU=B(_fo(_1zK,_1zL,_1zM,E(_1zT.b))),_1zV=E(_1zU.a)&4294967295,_1zW=B(_ZF(_1zV,_1zx,_1zO,_1zU.b)),_1zX=B(_QZ(_Q0,_1zK,_1zL,_1zM,E(_1zW.b))),_1zY=new T(function(){var _1zZ=B(_ZN(_1xe,_1zO,_1zX.b));return new T2(0,_1zZ.a,_1zZ.b);}),_1A0=B(_ZW(_12e,_1xT,_1zO,new T(function(){return E(E(_1zY).b);},1))),_1A1=B(_fo(_1zK,_1zL,_1zM,E(_1A0.b))),_1A2=new T(function(){var _1A3=E(_1A1.a)&4294967295,_1A4=new T(function(){var _1A5=function(_){var _1A6=(_1zS+1|0)-1|0,_1A7=function(_1A8){if(_1A8>=0){var _1A9=newArr(_1A8,_VA),_1Aa=_1A9,_1Ab=function(_1Ac){var _1Ad=function(_1Ae,_1Af,_){while(1){if(_1Ae!=_1Ac){var _1Ag=E(_1Af);if(!_1Ag._){return _5;}else{var _=_1Aa[_1Ae]=_1Ag.a,_1Ah=_1Ae+1|0;_1Ae=_1Ah;_1Af=_1Ag.b;continue;}}else{return _5;}}},_1Ai=B(_1Ad(0,new T(function(){return B(_0(_1zT.a,_1zI));},1),_));return new T4(0,E(_1uO),E(_1A6),_1A8,_1Aa);};if(0>_1A6){return new F(function(){return _1Ab(0);});}else{var _1Aj=_1A6+1|0;if(_1Aj>=0){return new F(function(){return _1Ab(_1Aj);});}else{return E(_1xi);}}}else{return E(_VC);}};if(0>_1A6){var _1Ak=B(_1A7(0)),_1Al=E(_1Ak),_1Am=_1Al.d;return new T4(0,E(_1Al.a),E(_1Al.b),_1Al.c,_1Am);}else{var _1An=B(_1A7(_1A6+1|0)),_1Ao=E(_1An),_1Ap=_1Ao.d;return new T4(0,E(_1Ao.a),E(_1Ao.b),_1Ao.c,_1Ap);}};return B(_8O(_1A5));}),_1Aq=new T(function(){var _1Ar=_1A3-1|0;if(0<=_1Ar){var _1As=function(_1At){return new T2(1,new T2(0,_1At,new T2(1,_1zV,_4)),new T(function(){if(_1At!=_1Ar){return B(_1As(_1At+1|0));}else{return __Z;}}));};return B(_1pG(_UD,B(_1As(0))));}else{return E(_1zE);}}),_1Au=new T(function(){var _1Av=function(_){var _1Aw=(_1zV+1|0)-1|0,_1Ax=function(_1Ay){if(_1Ay>=0){var _1Az=newArr(_1Ay,_VA),_1AA=_1Az,_1AB=function(_1AC){var _1AD=function(_1AE,_1AF,_){while(1){if(_1AE!=_1AC){var _1AG=E(_1AF);if(!_1AG._){return _5;}else{var _=_1AA[_1AE]=_1AG.a,_1AH=_1AE+1|0;_1AE=_1AH;_1AF=_1AG.b;continue;}}else{return _5;}}},_1AI=new T(function(){var _1AJ=new T(function(){var _1AK=function(_){var _1AL=newByteArr(4),_1AM=_1AL,_1AN=function(_1AO,_){while(1){var _=_1AM["v"]["i32"][_1AO]=0,_1AP=E(_1AO);if(!_1AP){return _5;}else{_1AO=_1AP+1|0;continue;}}},_1AQ=B(_1AN(0,_)),_1AR=function(_1AS,_1AT,_){while(1){var _1AU=E(_1AS);if(_1AU==1){return _5;}else{var _1AV=E(_1AT);if(!_1AV._){return _5;}else{var _=_1AM["v"]["i32"][_1AU]=E(_1AV.a);_1AS=_1AU+1|0;_1AT=_1AV.b;continue;}}}},_1AW=B(_1AR(0,new T2(1,_1zS,_4),_));return new T4(0,E(_1uO),E(_1uO),1,_1AM);},_1AX=B(_8O(_1AK));return new T5(0,_1zv,E(_1AX.a),E(_1AX.b),_1AX.c,_1AX.d);});return B(_0(_1zW.a,new T2(1,_1AJ,_4)));},1),_1AY=B(_1AD(0,_1AI,_));return new T4(0,E(_1uO),E(_1Aw),_1Ay,_1AA);};if(0>_1Aw){return new F(function(){return _1AB(0);});}else{var _1AZ=_1Aw+1|0;if(_1AZ>=0){return new F(function(){return _1AB(_1AZ);});}else{return E(_1xi);}}}else{return E(_VC);}};if(0>_1Aw){var _1B0=B(_1Ax(0)),_1B1=E(_1B0),_1B2=_1B1.d;return new T4(0,E(_1B1.a),E(_1B1.b),_1B1.c,_1B2);}else{var _1B3=B(_1Ax(_1Aw+1|0)),_1B4=E(_1B3),_1B5=_1B4.d;return new T4(0,E(_1B4.a),E(_1B4.b),_1B4.c,_1B5);}};return B(_8O(_1Av));});return {_:0,a:_1zP.a,b:_1zQ.a,c:_1Au,d:_1zX.a,e:_1Aq,f:_1A4,g:new T(function(){var _1B6=E(E(_1zY).a);if(!_1B6._){return new T0(2);}else{var _1B7=E(_1B6.a);return B(_Qi(E(_1B7.a),_1B7.b,_1B6.b,_Q1));}}),h:_UD,i:_Rm,j:_1A0.a,k:_UD,l:_1A3};});return new T2(0,_1A2,_1A1.b);},_1B8=function(_1B9,_1Ba){var _1Bb=E(_1B9),_1Bc=B(_1zJ(_1Bb.a,_1Bb.b,_1Bb.c,_1Ba));return new T2(0,_1Bc.a,_1Bc.b);},_1Bd=function(_1Be,_1Bf){var _1Bg=E(_1Be),_1Bh=B(_J4(_Jz,_LR,_1Bg,_1Bf)),_1Bi=B(_fz(_1Bg.a,_1Bg.b,_1Bg.c,E(_1Bh.b)));return new T2(0,new T2(0,_1Bh.a,_1Bi.a),_1Bi.b);},_1Bj=function(_1Bk,_1Bl){var _1Bm=new T(function(){var _1Bn=B(_ZN(_119,_1Bk,_1Bl));return new T2(0,_1Bn.a,_1Bn.b);}),_1Bo=B(_ZN(_1Bd,_1Bk,new T(function(){return E(E(_1Bm).b);},1)));return new T2(0,new T2(0,new T(function(){return E(E(_1Bm).a);}),_1Bo.a),_1Bo.b);},_1Bp=function(_1Bq,_1Br){var _1Bs=B(_1Bj(_1Bq,_1Br));return new T2(0,_1Bs.a,_1Bs.b);},_1Bt=function(_1Bu,_1Bv,_1Bw,_1Bx,_1By){var _1Bz=B(_fz(_1Bv,_1Bw,_1Bx,_1By)),_1BA=new T3(0,_1Bv,_1Bw,_1Bx),_1BB=B(_ZW(_12e,_129,_1BA,_1Bz.b)),_1BC=B(_ZW(_12e,_124,_1BA,_1BB.b)),_1BD=B(_ZW(_12e,_1Bp,_1BA,_1BC.b)),_1BE=B(_ZW(_12e,_1B8,_1BA,_1BD.b));return new T2(0,new T4(0,_1Bu,_1Bz.a,new T3(0,_1BB.a,new T(function(){return B(_Zm(_1uK,_1BC.a));}),new T(function(){return B(_Zm(_1uH,_1BD.a));})),new T(function(){return B(_Zm(_1uD,_1BE.a));})),_1BE.b);},_1BF=function(_1BG,_1BH,_1BI,_1BJ){var _1BK=B(_ZW(_12e,_129,new T3(0,_1BG,_1BH,_1BI),_1BJ));return new F(function(){return _1Bt(_1BK.a,_1BG,_1BH,_1BI,E(_1BK.b));});},_1BL=function(_1BM,_1BN){var _1BO=E(_1BN);return new F(function(){return _1sx(_1BO.a,_1BO.b,_1BO.c,_1BO.d,_1BO.e,_1BO.f,_1BO.g,_1BO.j,_1BO.l);});},_1BP=function(_1BQ,_1BR,_1BS,_1BT){var _1BU=new T3(0,_1BQ,_1BR,_1BS),_1BV=B(_Wp(_1BU,_1BT)),_1BW=B(_Wp(_1BU,_1BV.b)),_1BX=_1BW.a,_1BY=_1BW.b,_1BZ=E(_1BV.a),_1C0=function(_1C1){var _1C2=E(_1BZ);if(_1C2==1){var _1C3=E(_1BX);if(!E(_1C3)){return new F(function(){return _1BF(_1BQ,_1BR,_1BS,_1BY);});}else{return new F(function(){return _Wj(_1C3,1);});}}else{return new F(function(){return _Wj(_1BX,_1C2);});}};if(E(_1BZ)==2){if(E(_1BX)>1){return new F(function(){return _1C0(_);});}else{var _1C4=B(_Uq(_fN,_Mc,_1BQ,_1BR,_1BS,E(_1BY))),_1C5=B(_fz(_1BQ,_1BR,_1BS,E(_1C4.b))),_1C6=B(_Zq(_1BQ,_1BR,_1BS,E(_1C5.b))),_1C7=_1C6.a,_1C8=B(_Uq(_fN,_Wh,_1BQ,_1BR,_1BS,E(_1C6.b))),_1C9=new T(function(){return B(_Zm(function(_1Ca){return new F(function(){return _1BL(_1C7,_1Ca);});},_1C8.a));});return new T2(0,new T4(0,_1C4.a,_1C5.a,_1C7,_1C9),_1C8.b);}}else{return new F(function(){return _1C0(_);});}},_1Cb=0,_1Cc=new T(function(){return B(unCStr("()"));}),_1Cd=new T(function(){return B(unCStr(")"));}),_1Ce=function(_1Cf){var _1Cg=E(_1Cf);if(_1Cg==95){return true;}else{var _1Ch=function(_1Ci){if(_1Cg<65){if(_1Cg<192){return false;}else{if(_1Cg>255){return false;}else{switch(E(_1Cg)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1Cg>90){if(_1Cg<192){return false;}else{if(_1Cg>255){return false;}else{switch(E(_1Cg)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1Cg<97){return new F(function(){return _1Ch(_);});}else{if(_1Cg>122){return new F(function(){return _1Ch(_);});}else{return true;}}}},_1Cj=new T(function(){return B(unCStr("UTF8.decodeUTF8: bad data"));}),_1Ck=function(_1Cl){return new F(function(){return err(_1Cj);});},_1Cm=new T(function(){return B(_1Ck(_));}),_1Cn=function(_1Co){var _1Cp=E(_1Co);if(!_1Cp._){return __Z;}else{var _1Cq=_1Cp.b,_1Cr=E(_1Cp.a);if(_1Cr>=128){var _1Cs=E(_1Cq);if(!_1Cs._){return E(_1Cm);}else{var _1Ct=_1Cs.a,_1Cu=_1Cs.b,_1Cv=function(_1Cw){var _1Cx=E(_1Cu);if(!_1Cx._){return E(_1Cm);}else{if(224>_1Cr){return E(_1Cm);}else{if(_1Cr>239){return E(_1Cm);}else{var _1Cy=E(_1Ct);if(128>_1Cy){return E(_1Cm);}else{if(_1Cy>191){return E(_1Cm);}else{var _1Cz=E(_1Cx.a);return (128>_1Cz)?E(_1Cm):(_1Cz>191)?E(_1Cm):new T2(1,new T(function(){var _1CA=((imul(B(_oc(_1Cr,16)),4096)|0)+(imul(B(_oc(_1Cy,64)),64)|0)|0)+B(_oc(_1Cz,64))|0;if(_1CA>>>0>1114111){return B(_fQ(_1CA));}else{return _1CA;}}),new T(function(){return B(_1Cn(_1Cx.b));}));}}}}}};if(192>_1Cr){return new F(function(){return _1Cv(_);});}else{if(_1Cr>223){return new F(function(){return _1Cv(_);});}else{var _1CB=E(_1Ct);if(128>_1CB){return new F(function(){return _1Cv(_);});}else{if(_1CB>191){return new F(function(){return _1Cv(_);});}else{return new T2(1,new T(function(){var _1CC=(imul(B(_oc(_1Cr,32)),64)|0)+B(_oc(_1CB,64))|0;if(_1CC>>>0>1114111){return B(_fQ(_1CC));}else{return _1CC;}}),new T(function(){return B(_1Cn(_1Cu));}));}}}}}}else{return new T2(1,_1Cr,new T(function(){return B(_1Cn(_1Cq));}));}}},_1CD=function(_1CE){var _1CF=E(_1CE);switch(_1CF){case 39:return true;case 95:return true;default:var _1CG=function(_1CH){var _1CI=function(_1CJ){if(_1CF<65){if(_1CF<192){return false;}else{if(_1CF>255){return false;}else{switch(E(_1CF)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1CF>90){if(_1CF<192){return false;}else{if(_1CF>255){return false;}else{switch(E(_1CF)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1CF<97){return new F(function(){return _1CI(_);});}else{if(_1CF>122){return new F(function(){return _1CI(_);});}else{return true;}}};if(_1CF<48){return new F(function(){return _1CG(_);});}else{if(_1CF>57){return new F(function(){return _1CG(_);});}else{return true;}}}},_1CK=function(_1CL){while(1){var _1CM=E(_1CL);if(!_1CM._){return true;}else{if(!B(_1CD(E(_1CM.a)))){return false;}else{_1CL=_1CM.b;continue;}}}},_1CN=new T(function(){return B(unCStr("\\\\"));}),_1CO=new T(function(){return B(unCStr("\\\'"));}),_1CP=new T(function(){return B(unCStr("\'"));}),_1CQ=function(_1CR){var _1CS=E(_1CR);if(!_1CS._){return E(_1CP);}else{var _1CT=_1CS.b,_1CU=E(_1CS.a);switch(E(_1CU)){case 39:return new F(function(){return _0(_1CO,new T(function(){return B(_1CQ(_1CT));},1));});break;case 92:return new F(function(){return _0(_1CN,new T(function(){return B(_1CQ(_1CT));},1));});break;default:return new T2(1,_1CU,new T(function(){return B(_1CQ(_1CT));}));}}},_1CV=function(_1CW){var _1CX=E(_1CW);return (_1CX._==0)?__Z:new T2(1,new T(function(){return B(_12J(_1CX.a));}),new T(function(){return B(_1CV(_1CX.b));}));},_1CY=function(_1CZ,_1D0,_1D1){var _1D2=B(_1Cn(B(_1CV(new T(function(){return B(_IP(_1CZ,_1D0,_1D1));})))));if(!_1D2._){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1CQ(_4));}));});}else{if(!B(_1Ce(E(_1D2.a)))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1CQ(_1D2));}));});}else{if(!B(_1CK(_1D2.b))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1CQ(_1D2));}));});}else{return E(_1D2);}}}},_1D3=function(_1D4,_1D5){while(1){var _1D6=B((function(_1D7,_1D8){var _1D9=E(_1D7);if(!_1D9._){return E(_1D8);}else{var _1Da=new T(function(){return B(unAppCStr(" -> ",new T(function(){var _1Db=E(_1D9.a);return B(_1CY(_1Db.a,_1Db.b,_1Db.c));})));},1),_1Dc=B(_0(_1D8,_1Da));_1D4=_1D9.b;_1D5=_1Dc;return __continue;}})(_1D4,_1D5));if(_1D6!=__continue){return _1D6;}}},_1Dd=function(_1De){var _1Df=E(_1De);if(!_1Df._){var _1Dg=_1Df.a,_1Dh=E(_1Df.b);if(!_1Dh._){return new F(function(){return unAppCStr("(",new T(function(){var _1Di=E(_1Dg);return B(_0(B(_1CY(_1Di.a,_1Di.b,_1Di.c)),_1Cd));}));});}else{var _1Dj=new T(function(){var _1Dk=E(_1Dh.a),_1Dl=new T(function(){return B(unAppCStr(" -> ",new T(function(){var _1Dm=E(_1Dg);return B(_0(B(_1CY(_1Dm.a,_1Dm.b,_1Dm.c)),_1Cd));})));},1);return B(_0(B(_1D3(_1Dh.b,B(_1CY(_1Dk.a,_1Dk.b,_1Dk.c)))),_1Dl));});return new F(function(){return unAppCStr("(",_1Dj);});}}else{return E(_1Cc);}},_1Dn=32,_1Do=function(_1Dp){var _1Dq=E(_1Dp);if(!_1Dq._){return __Z;}else{var _1Dr=new T(function(){return B(_0(B(_1Ds(_1Dq.a)),new T(function(){return B(_1Do(_1Dq.b));},1)));});return new T2(1,_1Dn,_1Dr);}},_1Dt=new T(function(){return B(unCStr("}"));}),_1Du=new T(function(){return B(_0(_4,_1Dt));}),_1Ds=function(_1Dv){var _1Dw=E(_1Dv);if(!_1Dw._){var _1Dx=_1Dw.a,_1Dy=_1Dw.b,_1Dz=E(_1Dw.c);if(!_1Dz._){var _1DA=new T(function(){var _1DB=E(_1Dx),_1DC=new T(function(){return B(unAppCStr(":",new T(function(){return B(_0(B(_1Dd(_1Dy)),_1Dt));})));},1);return B(_0(B(_1CY(_1DB.a,_1DB.b,_1DB.c)),_1DC));});return new F(function(){return unAppCStr("{",_1DA);});}else{var _1DD=new T(function(){var _1DE=E(_1Dx),_1DF=new T(function(){var _1DG=new T(function(){var _1DH=new T(function(){return B(unAppCStr(" ",new T(function(){var _1DI=B(_1Do(_1Dz));if(!_1DI._){return E(_1Du);}else{return B(_0(_1DI.b,_1Dt));}})));},1);return B(_0(B(_1Dd(_1Dy)),_1DH));});return B(unAppCStr(":",_1DG));},1);return B(_0(B(_1CY(_1DE.a,_1DE.b,_1DE.c)),_1DF));});return new F(function(){return unAppCStr("{",_1DD);});}}else{return new F(function(){return unAppCStr("{?",new T(function(){var _1DJ=E(_1Dw.a);return B(_0(B(_1CY(_1DJ.a,_1DJ.b,_1DJ.c)),_1Dt));}));});}},_1DK=new T(function(){return B(unCStr("!!: negative index"));}),_1DL=new T(function(){return B(_0(_eh,_1DK));}),_1DM=new T(function(){return B(err(_1DL));}),_1DN=new T(function(){return B(unCStr("!!: index too large"));}),_1DO=new T(function(){return B(_0(_eh,_1DN));}),_1DP=new T(function(){return B(err(_1DO));}),_1DQ=function(_1DR,_1DS){while(1){var _1DT=E(_1DR);if(!_1DT._){return E(_1DP);}else{var _1DU=E(_1DS);if(!_1DU){return E(_1DT.a);}else{_1DR=_1DT.b;_1DS=_1DU-1|0;continue;}}}},_1DV=function(_1DW,_1DX){if(_1DX>=0){return new F(function(){return _1DQ(_1DW,_1DX);});}else{return E(_1DM);}},_1DY=function(_1DZ,_1E0){var _1E1=E(_1DZ);if(!_1E1._){var _1E2=E(_1E1.c);if(!_1E2._){return __Z;}else{var _1E3=E(_1E0);return (_1E3>=0)?(_1E3<B(_v0(_1E2,0)))?new T1(1,new T(function(){return B(_1DV(_1E2,_1E3));})):__Z:__Z;}}else{return __Z;}},_1E4=function(_1E5,_1E6){while(1){var _1E7=B((function(_1E8,_1E9){var _1Ea=E(_1E9);if(!_1Ea._){return new T1(1,_1E8);}else{var _1Eb=_1Ea.a,_1Ec=E(_1Ea.b);if(!_1Ec._){return new F(function(){return _1DY(_1E8,_1Eb);});}else{var _1Ed=E(_1E8);if(!_1Ed._){var _1Ee=E(_1Ed.c);if(!_1Ee._){return __Z;}else{var _1Ef=E(_1Eb);if(_1Ef>=0){if(_1Ef<B(_v0(_1Ee,0))){_1E5=new T(function(){return B(_1DV(_1Ee,_1Ef));});_1E6=_1Ec;return __continue;}else{return __Z;}}else{return __Z;}}}else{return __Z;}}}})(_1E5,_1E6));if(_1E7!=__continue){return _1E7;}}},_1Eg=function(_1Eh,_1Ei){var _1Ej=E(_1Ei);if(!_1Ej._){return __Z;}else{var _1Ek=_1Ej.a,_1El=E(_1Eh);return (_1El==1)?new T2(1,_1Ek,_4):new T2(1,_1Ek,new T(function(){return B(_1Eg(_1El-1|0,_1Ej.b));}));}},_1Em=new T(function(){return B(unCStr("suggestionList"));}),_1En=new T(function(){return B(unCStr("hover"));}),_1Eo=new T(function(){return eval("(function(e,c) {e.classList.toggle(c);})");}),_1Ep=function(_1Eq,_){var _1Er=__app2(E(_1Eo),_1Eq,toJSStr(E(_1En)));return new F(function(){return _u(_);});},_1Es=6,_1Et=5,_1Eu=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1Ev=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_1Ew=new T(function(){return B(unCStr("div"));}),_1Ex=new T(function(){return eval("(function(s){return document.createTextNode(s);})");}),_1Ey=function(_1Ez){return E(E(_1Ez).a);},_1EA=function(_1EB){return E(E(_1EB).b);},_1EC=function(_1ED){return E(E(_1ED).a);},_1EE=function(_){return new F(function(){return nMV(_4l);});},_1EF=new T(function(){return B(_z(_1EE));}),_1EG=function(_1EH){return E(E(_1EH).b);},_1EI=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1EJ=function(_1EK,_1EL,_1EM,_1EN,_1EO,_1EP){var _1EQ=B(_1Ey(_1EK)),_1ER=B(_2z(_1EQ)),_1ES=new T(function(){return B(_6i(_1EQ));}),_1ET=new T(function(){return B(_dh(_1ER));}),_1EU=new T(function(){return B(A1(_1EL,_1EN));}),_1EV=new T(function(){return B(A2(_1EC,_1EM,_1EO));}),_1EW=function(_1EX){return new F(function(){return A1(_1ET,new T3(0,_1EV,_1EU,_1EX));});},_1EY=function(_1EZ){var _1F0=new T(function(){var _1F1=new T(function(){var _1F2=__createJSFunc(2,function(_1F3,_){var _1F4=B(A2(E(_1EZ),_1F3,_));return _D;}),_1F5=_1F2;return function(_){return new F(function(){return __app3(E(_1EI),E(_1EU),E(_1EV),_1F5);});};});return B(A1(_1ES,_1F1));});return new F(function(){return A3(_1V,_1ER,_1F0,_1EW);});},_1F6=new T(function(){var _1F7=new T(function(){return B(_6i(_1EQ));}),_1F8=function(_1F9){var _1Fa=new T(function(){return B(A1(_1F7,function(_){var _=wMV(E(_1EF),new T1(1,_1F9));return new F(function(){return A(_1EA,[_1EM,_1EO,_1F9,_]);});}));});return new F(function(){return A3(_1V,_1ER,_1Fa,_1EP);});};return B(A2(_1EG,_1EK,_1F8));});return new F(function(){return A3(_1V,_1ER,_1F6,_1EY);});},_1Fb=function(_1Fc,_1Fd,_1Fe,_){var _1Ff=__app1(E(_1Ex),toJSStr(E(_1Fd))),_1Fg=__app1(E(_1Eu),toJSStr(E(_1Ew))),_1Fh=_1Fg,_1Fi=B(A(_1EJ,[_do,_df,_de,_1Fh,_1Et,function(_1Fj,_){return new F(function(){return _1Ep(_1Fh,_);});},_])),_1Fk=B(A(_1EJ,[_do,_df,_de,_1Fh,_1Es,function(_1Fl,_){return new F(function(){return _1Ep(_1Fh,_);});},_])),_1Fm=B(A(_1EJ,[_do,_df,_de,_1Fh,_1Cb,_1Fe,_])),_1Fn=E(_1Ev),_1Fo=__app2(_1Fn,_1Ff,_1Fh),_1Fp=__app2(_1Fn,_1Fh,E(_1Fc));return _5;},_1Fq=function(_){return new F(function(){return __app1(E(_1Eu),"div");});},_1Fr=new T(function(){return eval("(function(e){while(e.firstChild){e.removeChild(e.firstChild);}})");}),_1Fs=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1Ft=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:68:5-14"));}),_1Fu=new T(function(){return B(unCStr("score"));}),_1Fv=function(_1Fw,_){var _1Fx=__app1(E(_1Fs),toJSStr(E(_1Fu))),_1Fy=__eq(_1Fx,E(_D)),_1Fz=function(_,_1FA){var _1FB=E(_1FA);if(!_1FB._){return new F(function(){return _bC(_1Ft,_);});}else{var _1FC=rMV(E(_1Fw)),_1FD=E(_1FB.a),_1FE=__app1(E(_1Fr),_1FD),_1FF=__app1(E(_1Ex),toJSStr(B(_bZ(0,E(E(_1FC).e),_4)))),_1FG=__app2(E(_1Ev),_1FF,_1FD);return new F(function(){return _u(_);});}};if(!E(_1Fy)){var _1FH=__isUndef(_1Fx);if(!E(_1FH)){return new F(function(){return _1Fz(_,new T1(1,_1Fx));});}else{return new F(function(){return _1Fz(_,_4l);});}}else{return new F(function(){return _1Fz(_,_4l);});}},_1FI=new T(function(){return eval("(function(c,p){p.removeChild(c);})");}),_1FJ=new T(function(){return eval("document.body");}),_1FK=function(_,_1FL){var _1FM=E(_1FL);if(!_1FM._){return _5;}else{var _1FN=E(_1FM.a),_1FO=__app1(E(_1Fr),_1FN),_1FP=__app2(E(_1FI),_1FN,E(_1FJ));return new F(function(){return _u(_);});}},_1FQ=function(_1FR,_){var _1FS=__app1(E(_1Fs),toJSStr(E(_1FR))),_1FT=__eq(_1FS,E(_D));if(!E(_1FT)){var _1FU=__isUndef(_1FS);if(!E(_1FU)){return new F(function(){return _1FK(_,new T1(1,_1FS));});}else{return new F(function(){return _1FK(_,_4l);});}}else{return new F(function(){return _1FK(_,_4l);});}},_1FV=2,_1FW=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1FX=new T(function(){return B(err(_1FW));}),_1FY=function(_1FZ){return new F(function(){return fromJSStr(E(_1FZ));});},_1G0=function(_1G1){return E(E(_1G1).a);},_1G2=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_1G3=function(_1G4,_1G5,_1G6,_1G7){var _1G8=new T(function(){var _1G9=function(_){var _1Ga=__app2(E(_1G2),B(A2(_1G0,_1G4,_1G6)),E(_1G7));return new T(function(){return String(_1Ga);});};return E(_1G9);});return new F(function(){return A2(_6i,_1G5,_1G8);});},_1Gb=function(_1Gc,_1Gd,_1Ge,_1Gf){var _1Gg=B(_2z(_1Gd)),_1Gh=new T(function(){return B(_dh(_1Gg));}),_1Gi=function(_1Gj){return new F(function(){return A1(_1Gh,new T(function(){return B(_1FY(_1Gj));}));});},_1Gk=new T(function(){return B(_1G3(_1Gc,_1Gd,_1Ge,new T(function(){return toJSStr(E(_1Gf));},1)));});return new F(function(){return A3(_1V,_1Gg,_1Gk,_1Gi);});},_1Gl=new T(function(){return new T2(0,_18F,_1Gm);}),_1Gm=function(_1Gn,_1Go){return (!B(A3(_pS,_1Gl,_1Gn,_1Go)))?true:false;},_1Gp=new T2(0,_18F,_1Gm),_1Gq=function(_1Gr,_1Gs){var _1Gt=E(_1Gr);if(!_1Gt._){var _1Gu=E(_1Gs);if(!_1Gu._){var _1Gv=E(_1Gt.a),_1Gw=E(_1Gu.a);if(!B(_12S(_1Gv.a,_1Gv.b,_1Gv.c,_1Gw.a,_1Gw.b,_1Gw.c))){return false;}else{return new F(function(){return _18U(_1Gp,_1Gt.b,_1Gu.b);});}}else{return false;}}else{return (E(_1Gs)._==0)?false:true;}},_1Gx=function(_1Gy,_1Gz){return (!B(_1GA(_1Gy,_1Gz)))?true:false;},_1GB=new T(function(){return new T2(0,_1GA,_1Gx);}),_1GA=function(_1GC,_1GD){var _1GE=E(_1GC);if(!_1GE._){var _1GF=E(_1GD);if(!_1GF._){var _1GG=E(_1GE.a),_1GH=E(_1GF.a);if(!B(_12S(_1GG.a,_1GG.b,_1GG.c,_1GH.a,_1GH.b,_1GH.c))){return false;}else{if(!B(_1Gq(_1GE.b,_1GF.b))){return false;}else{return new F(function(){return _18U(_1GB,_1GE.c,_1GF.c);});}}}else{return false;}}else{var _1GI=E(_1GD);if(!_1GI._){return false;}else{return new F(function(){return _18F(_1GE.a,_1GI.a);});}}},_1GJ=function(_1GK,_1GL){while(1){var _1GM=E(_1GK);if(!_1GM._){return (E(_1GL)._==0)?true:false;}else{var _1GN=E(_1GL);if(!_1GN._){return false;}else{if(E(_1GM.a)!=E(_1GN.a)){return false;}else{_1GK=_1GM.b;_1GL=_1GN.b;continue;}}}}},_1GO=function(_1GP,_1GQ,_1GR,_1GS){if(!B(_1GJ(_1GP,_1GR))){return false;}else{return new F(function(){return _1GA(_1GQ,_1GS);});}},_1GT=function(_1GU,_1GV){var _1GW=E(_1GU),_1GX=E(_1GV);return new F(function(){return _1GO(_1GW.a,_1GW.b,_1GX.a,_1GX.b);});},_1GY=function(_1GZ,_1H0,_1H1,_1H2){return (!B(_1GJ(_1GZ,_1H1)))?true:(!B(_1GA(_1H0,_1H2)))?true:false;},_1H3=function(_1H4,_1H5){var _1H6=E(_1H4),_1H7=E(_1H5);return new F(function(){return _1GY(_1H6.a,_1H6.b,_1H7.a,_1H7.b);});},_1H8=new T2(0,_1GT,_1H3),_1H9=function(_1Ha,_1Hb){var _1Hc=E(_1Ha),_1Hd=E(_1Hb);return (!B(_1GA(_1Hc.a,_1Hd.a)))?true:(!B(_1nv(_1H8,_1Hc.b,_1Hd.b)))?true:false;},_1He=function(_1Hf,_1Hg,_1Hh,_1Hi){if(!B(_1GA(_1Hf,_1Hh))){return false;}else{return new F(function(){return _1nv(_1H8,_1Hg,_1Hi);});}},_1Hj=function(_1Hk,_1Hl){var _1Hm=E(_1Hk),_1Hn=E(_1Hl);return new F(function(){return _1He(_1Hm.a,_1Hm.b,_1Hn.a,_1Hn.b);});},_1Ho=new T2(0,_1Hj,_1H9),_1Hp=function(_1Hq,_1Hr){var _1Hs=E(_1Hq),_1Ht=E(_1Hr);return (B(_12Z(_1Hs.a,_1Hs.b,_1Hs.c,_1Ht.a,_1Ht.b,_1Ht.c))==0)?true:false;},_1Hu=function(_1Hv){var _1Hw=E(_1Hv);return new F(function(){return _G(_12J,B(_IP(_1Hw.a,_1Hw.b,_1Hw.c)));});},_1Hx=function(_1Hy,_1Hz){return (B(_12j(B(_1Hu(_1Hy)),B(_1Hu(_1Hz))))==2)?false:true;},_1HA=function(_1HB,_1HC){var _1HD=E(_1HB),_1HE=E(_1HC);return (B(_12Z(_1HD.a,_1HD.b,_1HD.c,_1HE.a,_1HE.b,_1HE.c))==2)?true:false;},_1HF=function(_1HG,_1HH){var _1HI=E(_1HG),_1HJ=E(_1HH);return (B(_12Z(_1HI.a,_1HI.b,_1HI.c,_1HJ.a,_1HJ.b,_1HJ.c))==0)?false:true;},_1HK=function(_1HL,_1HM){return (B(_12j(B(_1Hu(_1HL)),B(_1Hu(_1HM))))==2)?E(_1HL):E(_1HM);},_1HN=function(_1HO,_1HP){return (B(_12j(B(_1Hu(_1HO)),B(_1Hu(_1HP))))==2)?E(_1HP):E(_1HO);},_1HQ={_:0,a:_1Gp,b:_1b7,c:_1Hp,d:_1Hx,e:_1HA,f:_1HF,g:_1HK,h:_1HN},_1HR=function(_1HS,_1HT){var _1HU=E(_1HS);if(!_1HU._){var _1HV=E(_1HT);if(!_1HV._){var _1HW=E(_1HU.a),_1HX=E(_1HV.a);switch(B(_12Z(_1HW.a,_1HW.b,_1HW.c,_1HX.a,_1HX.b,_1HX.c))){case 0:return 0;case 1:return new F(function(){return _1bJ(_1HQ,_1HU.b,_1HV.b);});break;default:return 2;}}else{return 0;}}else{return (E(_1HT)._==0)?2:1;}},_1HY=function(_1HZ,_1I0){var _1I1=E(_1HZ);if(!_1I1._){var _1I2=E(_1I0);if(!_1I2._){var _1I3=E(_1I1.a),_1I4=E(_1I2.a);switch(B(_12Z(_1I3.a,_1I3.b,_1I3.c,_1I4.a,_1I4.b,_1I4.c))){case 0:return true;case 1:switch(B(_1HR(_1I1.b,_1I2.b))){case 0:return true;case 1:return (B(_1bJ(_1I5,_1I1.c,_1I2.c))==0)?true:false;default:return false;}break;default:return false;}}else{return true;}}else{var _1I6=E(_1I0);if(!_1I6._){return false;}else{return new F(function(){return _1Hp(_1I1.a,_1I6.a);});}}},_1I7=function(_1I8,_1I9){var _1Ia=E(_1I8);if(!_1Ia._){var _1Ib=E(_1I9);if(!_1Ib._){var _1Ic=E(_1Ia.a),_1Id=E(_1Ib.a);switch(B(_12Z(_1Ic.a,_1Ic.b,_1Ic.c,_1Id.a,_1Id.b,_1Id.c))){case 0:return true;case 1:switch(B(_1HR(_1Ia.b,_1Ib.b))){case 0:return true;case 1:return (B(_1bJ(_1I5,_1Ia.c,_1Ib.c))==2)?false:true;default:return false;}break;default:return false;}}else{return true;}}else{var _1Ie=E(_1I9);if(!_1Ie._){return false;}else{return new F(function(){return _1Hx(_1Ia.a,_1Ie.a);});}}},_1If=function(_1Ig,_1Ih){var _1Ii=E(_1Ig);if(!_1Ii._){var _1Ij=E(_1Ih);if(!_1Ij._){var _1Ik=E(_1Ii.a),_1Il=E(_1Ij.a);switch(B(_12Z(_1Ik.a,_1Ik.b,_1Ik.c,_1Il.a,_1Il.b,_1Il.c))){case 0:return false;case 1:switch(B(_1HR(_1Ii.b,_1Ij.b))){case 0:return false;case 1:return (B(_1bJ(_1I5,_1Ii.c,_1Ij.c))==2)?true:false;default:return true;}break;default:return true;}}else{return false;}}else{var _1Im=E(_1Ih);if(!_1Im._){return true;}else{return new F(function(){return _1HA(_1Ii.a,_1Im.a);});}}},_1In=function(_1Io,_1Ip){var _1Iq=E(_1Io);if(!_1Iq._){var _1Ir=E(_1Ip);if(!_1Ir._){var _1Is=E(_1Iq.a),_1It=E(_1Ir.a);switch(B(_12Z(_1Is.a,_1Is.b,_1Is.c,_1It.a,_1It.b,_1It.c))){case 0:return false;case 1:switch(B(_1HR(_1Iq.b,_1Ir.b))){case 0:return false;case 1:return (B(_1bJ(_1I5,_1Iq.c,_1Ir.c))==0)?false:true;default:return true;}break;default:return true;}}else{return false;}}else{var _1Iu=E(_1Ip);if(!_1Iu._){return true;}else{return new F(function(){return _1HF(_1Iq.a,_1Iu.a);});}}},_1Iv=function(_1Iw,_1Ix){return (!B(_1I7(_1Iw,_1Ix)))?E(_1Iw):E(_1Ix);},_1Iy=function(_1Iz,_1IA){return (!B(_1I7(_1Iz,_1IA)))?E(_1IA):E(_1Iz);},_1I5=new T(function(){return {_:0,a:_1GB,b:_1IB,c:_1HY,d:_1I7,e:_1If,f:_1In,g:_1Iv,h:_1Iy};}),_1IB=function(_1IC,_1ID){var _1IE=E(_1IC);if(!_1IE._){var _1IF=E(_1ID);if(!_1IF._){var _1IG=E(_1IE.a),_1IH=E(_1IF.a);switch(B(_12Z(_1IG.a,_1IG.b,_1IG.c,_1IH.a,_1IH.b,_1IH.c))){case 0:return 0;case 1:switch(B(_1HR(_1IE.b,_1IF.b))){case 0:return 0;case 1:return new F(function(){return _1bJ(_1I5,_1IE.c,_1IF.c);});break;default:return 2;}break;default:return 2;}}else{return 0;}}else{var _1II=E(_1ID);if(!_1II._){return 2;}else{return new F(function(){return _1b7(_1IE.a,_1II.a);});}}},_1IJ=function(_1IK,_1IL){while(1){var _1IM=E(_1IK);if(!_1IM._){return (E(_1IL)._==0)?1:0;}else{var _1IN=E(_1IL);if(!_1IN._){return 2;}else{var _1IO=E(_1IM.a),_1IP=E(_1IN.a);if(_1IO>=_1IP){if(_1IO!=_1IP){return 2;}else{_1IK=_1IM.b;_1IL=_1IN.b;continue;}}else{return 0;}}}}},_1IQ=function(_1IR,_1IS,_1IT,_1IU){switch(B(_1IJ(_1IR,_1IT))){case 0:return 0;case 1:return new F(function(){return _1IB(_1IS,_1IU);});break;default:return 2;}},_1IV=function(_1IW,_1IX){var _1IY=E(_1IW),_1IZ=E(_1IX);return new F(function(){return _1IQ(_1IY.a,_1IY.b,_1IZ.a,_1IZ.b);});},_1J0=function(_1J1,_1J2,_1J3,_1J4){switch(B(_1IJ(_1J1,_1J3))){case 0:return true;case 1:return new F(function(){return _1HY(_1J2,_1J4);});break;default:return false;}},_1J5=function(_1J6,_1J7){var _1J8=E(_1J6),_1J9=E(_1J7);return new F(function(){return _1J0(_1J8.a,_1J8.b,_1J9.a,_1J9.b);});},_1Ja=function(_1Jb,_1Jc,_1Jd,_1Je){switch(B(_1IJ(_1Jb,_1Jd))){case 0:return true;case 1:return new F(function(){return _1I7(_1Jc,_1Je);});break;default:return false;}},_1Jf=function(_1Jg,_1Jh){var _1Ji=E(_1Jg),_1Jj=E(_1Jh);return new F(function(){return _1Ja(_1Ji.a,_1Ji.b,_1Jj.a,_1Jj.b);});},_1Jk=function(_1Jl,_1Jm,_1Jn,_1Jo){switch(B(_1IJ(_1Jl,_1Jn))){case 0:return false;case 1:return new F(function(){return _1If(_1Jm,_1Jo);});break;default:return true;}},_1Jp=function(_1Jq,_1Jr){var _1Js=E(_1Jq),_1Jt=E(_1Jr);return new F(function(){return _1Jk(_1Js.a,_1Js.b,_1Jt.a,_1Jt.b);});},_1Ju=function(_1Jv,_1Jw,_1Jx,_1Jy){switch(B(_1IJ(_1Jv,_1Jx))){case 0:return false;case 1:return new F(function(){return _1In(_1Jw,_1Jy);});break;default:return true;}},_1Jz=function(_1JA,_1JB){var _1JC=E(_1JA),_1JD=E(_1JB);return new F(function(){return _1Ju(_1JC.a,_1JC.b,_1JD.a,_1JD.b);});},_1JE=function(_1JF,_1JG){var _1JH=E(_1JF),_1JI=E(_1JG);switch(B(_1IJ(_1JH.a,_1JI.a))){case 0:return E(_1JI);case 1:return (!B(_1I7(_1JH.b,_1JI.b)))?E(_1JH):E(_1JI);default:return E(_1JH);}},_1JJ=function(_1JK,_1JL){var _1JM=E(_1JK),_1JN=E(_1JL);switch(B(_1IJ(_1JM.a,_1JN.a))){case 0:return E(_1JM);case 1:return (!B(_1I7(_1JM.b,_1JN.b)))?E(_1JN):E(_1JM);default:return E(_1JN);}},_1JO={_:0,a:_1H8,b:_1IV,c:_1J5,d:_1Jf,e:_1Jp,f:_1Jz,g:_1JE,h:_1JJ},_1JP=function(_1JQ){return new F(function(){return _1no(_4,_1JQ);});},_1JR=function(_1JS,_1JT,_1JU,_1JV){switch(B(_1IB(_1JS,_1JU))){case 0:return true;case 1:return (B(_1bJ(_1JO,B(_1JP(_1JT)),B(_1JP(_1JV))))==0)?true:false;default:return false;}},_1JW=function(_1JX,_1JY){var _1JZ=E(_1JX),_1K0=E(_1JY);return new F(function(){return _1JR(_1JZ.a,_1JZ.b,_1K0.a,_1K0.b);});},_1K1=function(_1K2,_1K3,_1K4,_1K5){switch(B(_1IB(_1K2,_1K4))){case 0:return true;case 1:return (B(_1bJ(_1JO,B(_1JP(_1K3)),B(_1JP(_1K5))))==2)?false:true;default:return false;}},_1K6=function(_1K7,_1K8){var _1K9=E(_1K7),_1Ka=E(_1K8);return new F(function(){return _1K1(_1K9.a,_1K9.b,_1Ka.a,_1Ka.b);});},_1Kb=function(_1Kc,_1Kd,_1Ke,_1Kf){switch(B(_1IB(_1Kc,_1Ke))){case 0:return false;case 1:return (B(_1bJ(_1JO,B(_1JP(_1Kd)),B(_1JP(_1Kf))))==2)?true:false;default:return true;}},_1Kg=function(_1Kh,_1Ki){var _1Kj=E(_1Kh),_1Kk=E(_1Ki);return new F(function(){return _1Kb(_1Kj.a,_1Kj.b,_1Kk.a,_1Kk.b);});},_1Kl=function(_1Km,_1Kn,_1Ko,_1Kp){switch(B(_1IB(_1Km,_1Ko))){case 0:return false;case 1:return (B(_1bJ(_1JO,B(_1JP(_1Kn)),B(_1JP(_1Kp))))==0)?false:true;default:return true;}},_1Kq=function(_1Kr,_1Ks){var _1Kt=E(_1Kr),_1Ku=E(_1Ks);return new F(function(){return _1Kl(_1Kt.a,_1Kt.b,_1Ku.a,_1Ku.b);});},_1Kv=function(_1Kw,_1Kx,_1Ky,_1Kz){switch(B(_1IB(_1Kw,_1Ky))){case 0:return 0;case 1:return new F(function(){return _1bJ(_1JO,B(_1JP(_1Kx)),B(_1JP(_1Kz)));});break;default:return 2;}},_1KA=function(_1KB,_1KC){var _1KD=E(_1KB),_1KE=E(_1KC);return new F(function(){return _1Kv(_1KD.a,_1KD.b,_1KE.a,_1KE.b);});},_1KF=function(_1KG,_1KH){var _1KI=E(_1KG),_1KJ=E(_1KH);switch(B(_1IB(_1KI.a,_1KJ.a))){case 0:return E(_1KJ);case 1:return (B(_1bJ(_1JO,B(_1JP(_1KI.b)),B(_1JP(_1KJ.b))))==2)?E(_1KI):E(_1KJ);default:return E(_1KI);}},_1KK=function(_1KL,_1KM){var _1KN=E(_1KL),_1KO=E(_1KM);switch(B(_1IB(_1KN.a,_1KO.a))){case 0:return E(_1KN);case 1:return (B(_1bJ(_1JO,B(_1JP(_1KN.b)),B(_1JP(_1KO.b))))==2)?E(_1KO):E(_1KN);default:return E(_1KO);}},_1KP={_:0,a:_1Ho,b:_1KA,c:_1JW,d:_1K6,e:_1Kg,f:_1Kq,g:_1KF,h:_1KK},_1KQ=function(_1KR,_1KS,_1KT){var _1KU=E(_1KT);if(!_1KU._){var _1KV=_1KU.c,_1KW=_1KU.d,_1KX=E(_1KU.b);switch(B(_1IB(_1KR,_1KX.a))){case 0:return new F(function(){return _Ny(_1KX,B(_1KQ(_1KR,_1KS,_1KV)),_1KW);});break;case 1:switch(B(_1bJ(_1JO,B(_1JP(_1KS)),B(_1JP(_1KX.b))))){case 0:return new F(function(){return _Ny(_1KX,B(_1KQ(_1KR,_1KS,_1KV)),_1KW);});break;case 1:return new F(function(){return _15o(_1KV,_1KW);});break;default:return new F(function(){return _MW(_1KX,_1KV,B(_1KQ(_1KR,_1KS,_1KW)));});}break;default:return new F(function(){return _MW(_1KX,_1KV,B(_1KQ(_1KR,_1KS,_1KW)));});}}else{return new T0(1);}},_1KY=function(_1KZ,_1L0){var _1L1=E(_1KZ),_1L2=E(_1L0);if(!_1L2._){var _1L3=_1L2.b,_1L4=_1L2.c,_1L5=_1L2.d;switch(B(_1bJ(_1KP,B(_1no(_4,_1L1)),B(_1no(_4,_1L3))))){case 0:return new F(function(){return _MW(_1L3,B(_1KY(_1L1,_1L4)),_1L5);});break;case 1:return new T4(0,_1L2.a,E(_1L1),E(_1L4),E(_1L5));default:return new F(function(){return _Ny(_1L3,_1L4,B(_1KY(_1L1,_1L5)));});}}else{return new T4(0,1,E(_1L1),E(_MR),E(_MR));}},_1L6=function(_1L7,_1L8){while(1){var _1L9=E(_1L8);if(!_1L9._){return E(_1L7);}else{var _1La=B(_1KY(_1L9.a,_1L7));_1L7=_1La;_1L8=_1L9.b;continue;}}},_1Lb=function(_1Lc,_1Ld){var _1Le=E(_1Ld);if(!_1Le._){return new T3(0,_MR,_4,_4);}else{var _1Lf=_1Le.a,_1Lg=E(_1Lc);if(_1Lg==1){var _1Lh=E(_1Le.b);return (_1Lh._==0)?new T3(0,new T(function(){return new T4(0,1,E(_1Lf),E(_MR),E(_MR));}),_4,_4):(B(_1bJ(_1KP,B(_1JP(_1Lf)),B(_1JP(_1Lh.a))))==0)?new T3(0,new T(function(){return new T4(0,1,E(_1Lf),E(_MR),E(_MR));}),_1Lh,_4):new T3(0,new T(function(){return new T4(0,1,E(_1Lf),E(_MR),E(_MR));}),_4,_1Lh);}else{var _1Li=B(_1Lb(_1Lg>>1,_1Le)),_1Lj=_1Li.a,_1Lk=_1Li.c,_1Ll=E(_1Li.b);if(!_1Ll._){return new T3(0,_1Lj,_4,_1Lk);}else{var _1Lm=_1Ll.a,_1Ln=E(_1Ll.b);if(!_1Ln._){return new T3(0,new T(function(){return B(_Oe(_1Lm,_1Lj));}),_4,_1Lk);}else{if(!B(_1bJ(_1KP,B(_1JP(_1Lm)),B(_1JP(_1Ln.a))))){var _1Lo=B(_1Lb(_1Lg>>1,_1Ln));return new T3(0,new T(function(){return B(_OS(_1Lm,_1Lj,_1Lo.a));}),_1Lo.b,_1Lo.c);}else{return new T3(0,_1Lj,_4,_1Ll);}}}}}},_1Lp=function(_1Lq,_1Lr,_1Ls){while(1){var _1Lt=E(_1Ls);if(!_1Lt._){return E(_1Lr);}else{var _1Lu=_1Lt.a,_1Lv=E(_1Lt.b);if(!_1Lv._){return new F(function(){return _Oe(_1Lu,_1Lr);});}else{if(!B(_1bJ(_1KP,B(_1JP(_1Lu)),B(_1JP(_1Lv.a))))){var _1Lw=B(_1Lb(_1Lq,_1Lv)),_1Lx=_1Lw.a,_1Ly=E(_1Lw.c);if(!_1Ly._){var _1Lz=_1Lq<<1,_1LA=B(_OS(_1Lu,_1Lr,_1Lx));_1Lq=_1Lz;_1Lr=_1LA;_1Ls=_1Lw.b;continue;}else{return new F(function(){return _1L6(B(_OS(_1Lu,_1Lr,_1Lx)),_1Ly);});}}else{return new F(function(){return _1L6(_1Lr,_1Lt);});}}}}},_1LB=function(_1LC){var _1LD=E(_1LC);if(!_1LD._){return new T0(1);}else{var _1LE=_1LD.a,_1LF=E(_1LD.b);if(!_1LF._){return new T4(0,1,E(_1LE),E(_MR),E(_MR));}else{if(!B(_1bJ(_1KP,B(_1JP(_1LE)),B(_1JP(_1LF.a))))){return new F(function(){return _1Lp(1,new T4(0,1,E(_1LE),E(_MR),E(_MR)),_1LF);});}else{return new F(function(){return _1L6(new T4(0,1,E(_1LE),E(_MR),E(_MR)),_1LF);});}}}},_1LG=function(_1LH,_1LI){while(1){var _1LJ=E(_1LI);if(!_1LJ._){return E(_1LH);}else{var _1LK=_1LJ.a,_1LL=E(_1LH);if(!_1LL._){var _1LM=E(_1LK);if(!_1LM._){var _1LN=B(_1jD(_1KP,_1ir,_1ir,_1LL.a,_1LL.b,_1LL.c,_1LL.d,_1LM.a,_1LM.b,_1LM.c,_1LM.d));}else{var _1LN=E(_1LL);}var _1LO=_1LN;}else{var _1LO=E(_1LK);}_1LH=_1LO;_1LI=_1LJ.b;continue;}}},_1LP=function(_1LQ,_1LR,_1LS){var _1LT=E(_1LS);if(!_1LT._){var _1LU=_1LT.c,_1LV=_1LT.d,_1LW=E(_1LT.b);switch(B(_1IB(_1LQ,_1LW.a))){case 0:return new F(function(){return _MW(_1LW,B(_1LP(_1LQ,_1LR,_1LU)),_1LV);});break;case 1:switch(B(_1bJ(_1JO,B(_1JP(_1LR)),B(_1JP(_1LW.b))))){case 0:return new F(function(){return _MW(_1LW,B(_1LP(_1LQ,_1LR,_1LU)),_1LV);});break;case 1:return new T4(0,_1LT.a,E(new T2(0,_1LQ,_1LR)),E(_1LU),E(_1LV));default:return new F(function(){return _Ny(_1LW,_1LU,B(_1LP(_1LQ,_1LR,_1LV)));});}break;default:return new F(function(){return _Ny(_1LW,_1LU,B(_1LP(_1LQ,_1LR,_1LV)));});}}else{return new T4(0,1,E(new T2(0,_1LQ,_1LR)),E(_MR),E(_MR));}},_1LX=function(_1LY,_1LZ){while(1){var _1M0=E(_1LZ);if(!_1M0._){return E(_1LY);}else{var _1M1=E(_1M0.a),_1M2=B(_1LP(_1M1.a,_1M1.b,_1LY));_1LY=_1M2;_1LZ=_1M0.b;continue;}}},_1M3=function(_1M4,_1M5){var _1M6=E(_1M5);if(!_1M6._){return new T3(0,_MR,_4,_4);}else{var _1M7=_1M6.a,_1M8=E(_1M4);if(_1M8==1){var _1M9=E(_1M6.b);if(!_1M9._){return new T3(0,new T(function(){return new T4(0,1,E(_1M7),E(_MR),E(_MR));}),_4,_4);}else{var _1Ma=E(_1M7),_1Mb=E(_1M9.a);switch(B(_1IB(_1Ma.a,_1Mb.a))){case 0:return new T3(0,new T4(0,1,E(_1Ma),E(_MR),E(_MR)),_1M9,_4);case 1:return (B(_1bJ(_1JO,B(_1JP(_1Ma.b)),B(_1JP(_1Mb.b))))==0)?new T3(0,new T4(0,1,E(_1Ma),E(_MR),E(_MR)),_1M9,_4):new T3(0,new T4(0,1,E(_1Ma),E(_MR),E(_MR)),_4,_1M9);default:return new T3(0,new T4(0,1,E(_1Ma),E(_MR),E(_MR)),_4,_1M9);}}}else{var _1Mc=B(_1M3(_1M8>>1,_1M6)),_1Md=_1Mc.a,_1Me=_1Mc.c,_1Mf=E(_1Mc.b);if(!_1Mf._){return new T3(0,_1Md,_4,_1Me);}else{var _1Mg=_1Mf.a,_1Mh=E(_1Mf.b);if(!_1Mh._){return new T3(0,new T(function(){return B(_Oe(_1Mg,_1Md));}),_4,_1Me);}else{var _1Mi=E(_1Mg),_1Mj=E(_1Mh.a),_1Mk=function(_1Ml){var _1Mm=B(_1M3(_1M8>>1,_1Mh));return new T3(0,new T(function(){return B(_OS(_1Mi,_1Md,_1Mm.a));}),_1Mm.b,_1Mm.c);};switch(B(_1IB(_1Mi.a,_1Mj.a))){case 0:return new F(function(){return _1Mk(_);});break;case 1:if(!B(_1bJ(_1JO,B(_1JP(_1Mi.b)),B(_1JP(_1Mj.b))))){return new F(function(){return _1Mk(_);});}else{return new T3(0,_1Md,_4,_1Mf);}break;default:return new T3(0,_1Md,_4,_1Mf);}}}}}},_1Mn=function(_1Mo,_1Mp,_1Mq){var _1Mr=E(_1Mq);if(!_1Mr._){return E(_1Mp);}else{var _1Ms=_1Mr.a,_1Mt=E(_1Mr.b);if(!_1Mt._){return new F(function(){return _Oe(_1Ms,_1Mp);});}else{var _1Mu=E(_1Ms),_1Mv=E(_1Mt.a),_1Mw=function(_1Mx){var _1My=B(_1M3(_1Mo,_1Mt)),_1Mz=_1My.a,_1MA=E(_1My.c);if(!_1MA._){return new F(function(){return _1Mn(_1Mo<<1,B(_OS(_1Mu,_1Mp,_1Mz)),_1My.b);});}else{return new F(function(){return _1LX(B(_OS(_1Mu,_1Mp,_1Mz)),_1MA);});}};switch(B(_1IB(_1Mu.a,_1Mv.a))){case 0:return new F(function(){return _1Mw(_);});break;case 1:if(!B(_1bJ(_1JO,B(_1JP(_1Mu.b)),B(_1JP(_1Mv.b))))){return new F(function(){return _1Mw(_);});}else{return new F(function(){return _1LX(_1Mp,_1Mr);});}break;default:return new F(function(){return _1LX(_1Mp,_1Mr);});}}}},_1MB=function(_1MC){var _1MD=E(_1MC);if(!_1MD._){return new T0(1);}else{var _1ME=_1MD.a,_1MF=E(_1MD.b);if(!_1MF._){return new T4(0,1,E(_1ME),E(_MR),E(_MR));}else{var _1MG=E(_1ME),_1MH=E(_1MF.a);switch(B(_1IB(_1MG.a,_1MH.a))){case 0:return new F(function(){return _1Mn(1,new T4(0,1,E(_1MG),E(_MR),E(_MR)),_1MF);});break;case 1:if(!B(_1bJ(_1JO,B(_1JP(_1MG.b)),B(_1JP(_1MH.b))))){return new F(function(){return _1Mn(1,new T4(0,1,E(_1MG),E(_MR),E(_MR)),_1MF);});}else{return new F(function(){return _1LX(new T4(0,1,E(_1MG),E(_MR),E(_MR)),_1MF);});}break;default:return new F(function(){return _1LX(new T4(0,1,E(_1MG),E(_MR),E(_MR)),_1MF);});}}}},_1MI=function(_1MJ,_1MK,_1ML){var _1MM=E(_1ML);if(!_1MM._){var _1MN=_1MM.c,_1MO=_1MM.d,_1MP=E(_1MM.b);switch(B(_1IJ(_1MJ,_1MP.a))){case 0:return new F(function(){return _MW(_1MP,B(_1MI(_1MJ,_1MK,_1MN)),_1MO);});break;case 1:switch(B(_1IB(_1MK,_1MP.b))){case 0:return new F(function(){return _MW(_1MP,B(_1MI(_1MJ,_1MK,_1MN)),_1MO);});break;case 1:return new T4(0,_1MM.a,E(new T2(0,_1MJ,_1MK)),E(_1MN),E(_1MO));default:return new F(function(){return _Ny(_1MP,_1MN,B(_1MI(_1MJ,_1MK,_1MO)));});}break;default:return new F(function(){return _Ny(_1MP,_1MN,B(_1MI(_1MJ,_1MK,_1MO)));});}}else{return new T4(0,1,E(new T2(0,_1MJ,_1MK)),E(_MR),E(_MR));}},_1MQ=function(_1MR,_1MS){while(1){var _1MT=E(_1MS);if(!_1MT._){return E(_1MR);}else{var _1MU=E(_1MT.a),_1MV=B(_1MI(_1MU.a,_1MU.b,_1MR));_1MR=_1MV;_1MS=_1MT.b;continue;}}},_1MW=function(_1MX,_1MY){var _1MZ=E(_1MY);if(!_1MZ._){return new T3(0,_MR,_4,_4);}else{var _1N0=_1MZ.a,_1N1=E(_1MX);if(_1N1==1){var _1N2=E(_1MZ.b);if(!_1N2._){return new T3(0,new T(function(){return new T4(0,1,E(_1N0),E(_MR),E(_MR));}),_4,_4);}else{var _1N3=E(_1N0),_1N4=E(_1N2.a);switch(B(_1IJ(_1N3.a,_1N4.a))){case 0:return new T3(0,new T4(0,1,E(_1N3),E(_MR),E(_MR)),_1N2,_4);case 1:return (!B(_1In(_1N3.b,_1N4.b)))?new T3(0,new T4(0,1,E(_1N3),E(_MR),E(_MR)),_1N2,_4):new T3(0,new T4(0,1,E(_1N3),E(_MR),E(_MR)),_4,_1N2);default:return new T3(0,new T4(0,1,E(_1N3),E(_MR),E(_MR)),_4,_1N2);}}}else{var _1N5=B(_1MW(_1N1>>1,_1MZ)),_1N6=_1N5.a,_1N7=_1N5.c,_1N8=E(_1N5.b);if(!_1N8._){return new T3(0,_1N6,_4,_1N7);}else{var _1N9=_1N8.a,_1Na=E(_1N8.b);if(!_1Na._){return new T3(0,new T(function(){return B(_Oe(_1N9,_1N6));}),_4,_1N7);}else{var _1Nb=E(_1N9),_1Nc=E(_1Na.a);switch(B(_1IJ(_1Nb.a,_1Nc.a))){case 0:var _1Nd=B(_1MW(_1N1>>1,_1Na));return new T3(0,new T(function(){return B(_OS(_1Nb,_1N6,_1Nd.a));}),_1Nd.b,_1Nd.c);case 1:if(!B(_1In(_1Nb.b,_1Nc.b))){var _1Ne=B(_1MW(_1N1>>1,_1Na));return new T3(0,new T(function(){return B(_OS(_1Nb,_1N6,_1Ne.a));}),_1Ne.b,_1Ne.c);}else{return new T3(0,_1N6,_4,_1N8);}break;default:return new T3(0,_1N6,_4,_1N8);}}}}}},_1Nf=function(_1Ng,_1Nh,_1Ni){var _1Nj=E(_1Ni);if(!_1Nj._){return E(_1Nh);}else{var _1Nk=_1Nj.a,_1Nl=E(_1Nj.b);if(!_1Nl._){return new F(function(){return _Oe(_1Nk,_1Nh);});}else{var _1Nm=E(_1Nk),_1Nn=E(_1Nl.a),_1No=function(_1Np){var _1Nq=B(_1MW(_1Ng,_1Nl)),_1Nr=_1Nq.a,_1Ns=E(_1Nq.c);if(!_1Ns._){return new F(function(){return _1Nf(_1Ng<<1,B(_OS(_1Nm,_1Nh,_1Nr)),_1Nq.b);});}else{return new F(function(){return _1MQ(B(_OS(_1Nm,_1Nh,_1Nr)),_1Ns);});}};switch(B(_1IJ(_1Nm.a,_1Nn.a))){case 0:return new F(function(){return _1No(_);});break;case 1:if(!B(_1In(_1Nm.b,_1Nn.b))){return new F(function(){return _1No(_);});}else{return new F(function(){return _1MQ(_1Nh,_1Nj);});}break;default:return new F(function(){return _1MQ(_1Nh,_1Nj);});}}}},_1Nt=function(_1Nu){var _1Nv=E(_1Nu);if(!_1Nv._){return new T0(1);}else{var _1Nw=_1Nv.a,_1Nx=E(_1Nv.b);if(!_1Nx._){return new T4(0,1,E(_1Nw),E(_MR),E(_MR));}else{var _1Ny=E(_1Nw),_1Nz=E(_1Nx.a);switch(B(_1IJ(_1Ny.a,_1Nz.a))){case 0:return new F(function(){return _1Nf(1,new T4(0,1,E(_1Ny),E(_MR),E(_MR)),_1Nx);});break;case 1:if(!B(_1In(_1Ny.b,_1Nz.b))){return new F(function(){return _1Nf(1,new T4(0,1,E(_1Ny),E(_MR),E(_MR)),_1Nx);});}else{return new F(function(){return _1MQ(new T4(0,1,E(_1Ny),E(_MR),E(_MR)),_1Nx);});}break;default:return new F(function(){return _1MQ(new T4(0,1,E(_1Ny),E(_MR),E(_MR)),_1Nx);});}}}},_1NA=function(_1NB){return new T1(1,_1NB);},_1NC=function(_1ND){return E(E(_1ND).a);},_1NE=function(_1NF,_1NG){var _1NH=E(_1NF);if(!_1NH._){var _1NI=_1NH.c,_1NJ=B(_v0(_1NI,0));if(0<=_1NJ){var _1NK=function(_1NL,_1NM){var _1NN=E(_1NM);if(!_1NN._){return __Z;}else{return new F(function(){return _0(B(_1NE(_1NN.a,new T(function(){return B(_0(_1NG,new T2(1,_1NL,_4)));}))),new T(function(){if(_1NL!=_1NJ){return B(_1NK(_1NL+1|0,_1NN.b));}else{return __Z;}},1));});}};return new F(function(){return _1NK(0,_1NI);});}else{return __Z;}}else{return new T2(1,new T2(0,_1NG,_1NH.a),_4);}},_1NO=function(_1NP,_1NQ){var _1NR=E(_1NQ);if(!_1NR._){return new T2(0,_4,_4);}else{var _1NS=_1NR.a,_1NT=_1NR.b,_1NU=E(_1NP);if(_1NU==1){return new T2(0,new T2(1,_1NS,_4),_1NT);}else{var _1NV=new T(function(){var _1NW=B(_1NO(_1NU-1|0,_1NT));return new T2(0,_1NW.a,_1NW.b);});return new T2(0,new T2(1,_1NS,new T(function(){return E(E(_1NV).a);})),new T(function(){return E(E(_1NV).b);}));}}},_1NX=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_1NY=function(_1NZ){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_1NZ,_1NX));})),_6y);});},_1O0=new T(function(){return B(_1NY("Muste/Tree/Internal.hs:217:9-39|(pre, _ : post)"));}),_1O1=function(_1O2,_1O3,_1O4){if(0>_1O3){return E(_1O2);}else{if(_1O3>=B(_v0(_1O2,0))){return E(_1O2);}else{if(_1O3>0){var _1O5=B(_1NO(_1O3,_1O2)),_1O6=E(_1O5.b);if(!_1O6._){return E(_1O0);}else{return new F(function(){return _0(_1O5.a,new T2(1,_1O4,_1O6.b));});}}else{var _1O7=E(_1O2);if(!_1O7._){return E(_1O0);}else{return new F(function(){return _0(_4,new T2(1,_1O4,_1O7.b));});}}}}},_1O8=function(_1O9,_1Oa,_1Ob){var _1Oc=E(_1O9);if(!_1Oc._){var _1Od=_1Oc.c,_1Oe=E(_1Oa);if(!_1Oe._){return E(_1Ob);}else{var _1Of=E(_1Oe.a);if(_1Of<0){return E(_1Oc);}else{var _1Og=B(_v0(_1Od,0));if(_1Of>=_1Og){return E(_1Oc);}else{var _1Oh=new T(function(){return B(_1O1(_1Od,_1Of,new T(function(){var _1Oi=E(_1Od);if(!_1Oi._){return E(_1FX);}else{if(_1Of>=0){if(_1Of<_1Og){return B(_1O8(B(_1DV(_1Oi,_1Of)),_1Oe.b,_1Ob));}else{return E(_1FX);}}else{return E(_1FX);}}})));});return new T3(0,_1Oc.a,_1Oc.b,_1Oh);}}}}else{return (E(_1Oa)._==0)?E(_1Ob):E(_1Oc);}},_1Oj=function(_1Ok,_1Ol,_1Om,_1On,_1Oo){while(1){var _1Op=B((function(_1Oq,_1Or,_1Os,_1Ot,_1Ou){var _1Ov=E(_1Ot);if(!_1Ov._){var _1Ow=E(_1Ou);if(!_1Ow._){return new T2(0,_1Oq,_1Or);}else{var _1Ox=_1Ow.a,_1Oy=new T3(0,_1Os,_1Ov,new T(function(){return B(_G(_1NA,_1Ov.b));})),_1Oz=new T(function(){var _1OA=function(_1OB){var _1OC=E(_1OB);return new T2(0,new T(function(){return B(_0(_1Ox,_1OC.a));}),new T1(1,_1OC.b));},_1OD=B(_1Nt(B(_G(_1OA,B(_1NE(_1Oy,_4)))))),_1OE=B(_1o7(function(_1OF){return (!B(_1GJ(_1Ox,B(_1NC(_1OF)))))?true:false;},_1Or));if(!_1OE._){var _1OG=E(_1OD);if(!_1OG._){return B(_1jD(_1JO,_1ir,_1ir,_1OE.a,_1OE.b,_1OE.c,_1OE.d,_1OG.a,_1OG.b,_1OG.c,_1OG.d));}else{return E(_1OE);}}else{return E(_1OD);}}),_1OH=_1Os;_1Ok=new T(function(){return B(_1O8(_1Oq,_1Ox,_1Oy));});_1Ol=_1Oz;_1Om=_1OH;_1On=_1Ov;_1Oo=_1Ow.b;return __continue;}}else{return new T2(0,_1Oq,_1Or);}})(_1Ok,_1Ol,_1Om,_1On,_1Oo));if(_1Op!=__continue){return _1Op;}}},_1OI=new T2(1,_4,_4),_1OJ=function(_1OK){var _1OL=E(_1OK);if(!_1OL._){return E(_1OI);}else{var _1OM=_1OL.b,_1ON=new T(function(){return B(_G(function(_1NB){return new T2(1,_1OL.a,_1NB);},B(_1OJ(_1OM))));},1);return new F(function(){return _0(B(_1OJ(_1OM)),_1ON);});}},_1OO=new T(function(){return B(_1zc(95));}),_1OP=new T2(1,_1OO,_4),_1OQ=new T(function(){var _1OR=B(_1y0(_1OP));return new T3(0,_1OR.a,_1OR.b,_1OR.c);}),_1OS=function(_1OT,_1OU,_1OV,_1OW){var _1OX=new T(function(){return E(_1OV)-1|0;}),_1OY=function(_1OZ){var _1P0=E(_1OZ);if(!_1P0._){return __Z;}else{var _1P1=_1P0.b,_1P2=E(_1P0.a),_1P3=_1P2.a,_1P4=function(_1P5,_1P6,_1P7){var _1P8=E(_1P2.b);if(!B(_12S(_1P5,_1P6,_1P7,_1P8.a,_1P8.b,_1P8.c))){return new F(function(){return _1OY(_1P1);});}else{if(B(_v0(_1P3,0))>E(_1OX)){return new F(function(){return _1OY(_1P1);});}else{return new T2(1,_1P3,new T(function(){return B(_1OY(_1P1));}));}}},_1P9=E(E(_1OW).b);if(!_1P9._){var _1Pa=E(_1P9.a);return new F(function(){return _1P4(_1Pa.a,_1Pa.b,_1Pa.c);});}else{var _1Pb=E(_1OQ);return new F(function(){return _1P4(_1Pb.a,_1Pb.b,_1Pb.c);});}}},_1Pc=function(_1Pd){var _1Pe=new T(function(){var _1Pf=E(_1OW),_1Pg=B(_1Oj(_1OT,_1OU,_1Pf.a,_1Pf.b,_1Pd));return new T2(0,_1Pg.a,_1Pg.b);}),_1Ph=new T(function(){return E(E(_1Pe).a);}),_1Pi=new T(function(){var _1Pj=function(_1Pk){var _1Pl=B(_1E4(_1Ph,E(_1Pk).a));return (_1Pl._==0)?false:(E(_1Pl.a)._==0)?false:true;},_1Pm=E(E(_1Pe).b);if(!_1Pm._){var _1Pn=E(_1OU);if(!_1Pn._){return B(_1o7(_1Pj,B(_1jD(_1JO,_1ir,_1ir,_1Pm.a,_1Pm.b,_1Pm.c,_1Pm.d,_1Pn.a,_1Pn.b,_1Pn.c,_1Pn.d))));}else{return B(_1o7(_1Pj,_1Pm));}}else{return B(_1o7(_1Pj,_1OU));}});return new T2(0,_1Ph,_1Pi);};return new F(function(){return _1MB(B(_G(_1Pc,B(_1OJ(B(_1OY(B(_1NE(_1OT,_4)))))))));});},_1Po=function(_1Pp,_1Pq){while(1){var _1Pr=E(_1Pq);if(!_1Pr._){return E(_1Pp);}else{var _1Ps=_1Pr.a,_1Pt=E(_1Pp);if(!_1Pt._){var _1Pu=E(_1Ps);if(!_1Pu._){var _1Pv=B(_1jD(_1HQ,_1ir,_1ir,_1Pt.a,_1Pt.b,_1Pt.c,_1Pt.d,_1Pu.a,_1Pu.b,_1Pu.c,_1Pu.d));}else{var _1Pv=E(_1Pt);}var _1Pw=_1Pv;}else{var _1Pw=E(_1Ps);}_1Pp=_1Pw;_1Pq=_1Pr.b;continue;}}},_1Px=function(_1Py){var _1Pz=E(_1Py);if(!_1Pz._){return new F(function(){return _1Po(_MR,B(_G(_1Px,_1Pz.c)));});}else{return new F(function(){return _O8(_1Pz.a);});}},_1PA=function(_1PB,_1PC,_1PD){var _1PE=E(_1PD);if(!_1PE._){var _1PF=_1PE.c,_1PG=_1PE.d,_1PH=E(_1PE.b),_1PI=E(_1PB),_1PJ=E(_1PH.a);switch(B(_12Z(_1PI.a,_1PI.b,_1PI.c,_1PJ.a,_1PJ.b,_1PJ.c))){case 0:return new F(function(){return _MW(_1PH,B(_1PA(_1PI,_1PC,_1PF)),_1PG);});break;case 1:switch(B(_1HR(_1PC,_1PH.b))){case 0:return new F(function(){return _MW(_1PH,B(_1PA(_1PI,_1PC,_1PF)),_1PG);});break;case 1:return new T4(0,_1PE.a,E(new T2(0,_1PI,_1PC)),E(_1PF),E(_1PG));default:return new F(function(){return _Ny(_1PH,_1PF,B(_1PA(_1PI,_1PC,_1PG)));});}break;default:return new F(function(){return _Ny(_1PH,_1PF,B(_1PA(_1PI,_1PC,_1PG)));});}}else{return new T4(0,1,E(new T2(0,_1PB,_1PC)),E(_MR),E(_MR));}},_1PK=function(_1PL,_1PM){while(1){var _1PN=E(_1PM);if(!_1PN._){return E(_1PL);}else{var _1PO=E(_1PN.a),_1PP=B(_1PA(_1PO.a,_1PO.b,_1PL));_1PL=_1PP;_1PM=_1PN.b;continue;}}},_1PQ=function(_1PR,_1PS){var _1PT=E(_1PS);if(!_1PT._){return new T3(0,_MR,_4,_4);}else{var _1PU=_1PT.a,_1PV=E(_1PR);if(_1PV==1){var _1PW=E(_1PT.b);if(!_1PW._){return new T3(0,new T(function(){return new T4(0,1,E(_1PU),E(_MR),E(_MR));}),_4,_4);}else{var _1PX=E(_1PU),_1PY=E(_1PW.a),_1PZ=_1PY.b,_1Q0=E(_1PX.a),_1Q1=E(_1PY.a);switch(B(_12Z(_1Q0.a,_1Q0.b,_1Q0.c,_1Q1.a,_1Q1.b,_1Q1.c))){case 0:return new T3(0,new T4(0,1,E(_1PX),E(_MR),E(_MR)),_1PW,_4);case 1:var _1Q2=E(_1PX.b);if(!_1Q2._){var _1Q3=E(_1PZ);if(!_1Q3._){var _1Q4=E(_1Q2.a),_1Q5=E(_1Q3.a);switch(B(_12Z(_1Q4.a,_1Q4.b,_1Q4.c,_1Q5.a,_1Q5.b,_1Q5.c))){case 0:return new T3(0,new T4(0,1,E(_1PX),E(_MR),E(_MR)),_1PW,_4);case 1:return (B(_1bJ(_1HQ,_1Q2.b,_1Q3.b))==0)?new T3(0,new T4(0,1,E(_1PX),E(_MR),E(_MR)),_1PW,_4):new T3(0,new T4(0,1,E(_1PX),E(_MR),E(_MR)),_4,_1PW);default:return new T3(0,new T4(0,1,E(_1PX),E(_MR),E(_MR)),_4,_1PW);}}else{return new T3(0,new T4(0,1,E(_1PX),E(_MR),E(_MR)),_1PW,_4);}}else{var _1Q6=E(_1PZ);return new T3(0,new T4(0,1,E(_1PX),E(_MR),E(_MR)),_4,_1PW);}break;default:return new T3(0,new T4(0,1,E(_1PX),E(_MR),E(_MR)),_4,_1PW);}}}else{var _1Q7=B(_1PQ(_1PV>>1,_1PT)),_1Q8=_1Q7.a,_1Q9=_1Q7.c,_1Qa=E(_1Q7.b);if(!_1Qa._){return new T3(0,_1Q8,_4,_1Q9);}else{var _1Qb=_1Qa.a,_1Qc=E(_1Qa.b);if(!_1Qc._){return new T3(0,new T(function(){return B(_Oe(_1Qb,_1Q8));}),_4,_1Q9);}else{var _1Qd=E(_1Qb),_1Qe=E(_1Qc.a),_1Qf=_1Qe.b,_1Qg=E(_1Qd.a),_1Qh=E(_1Qe.a);switch(B(_12Z(_1Qg.a,_1Qg.b,_1Qg.c,_1Qh.a,_1Qh.b,_1Qh.c))){case 0:var _1Qi=B(_1PQ(_1PV>>1,_1Qc));return new T3(0,new T(function(){return B(_OS(_1Qd,_1Q8,_1Qi.a));}),_1Qi.b,_1Qi.c);case 1:var _1Qj=E(_1Qd.b);if(!_1Qj._){var _1Qk=E(_1Qf);if(!_1Qk._){var _1Ql=E(_1Qj.a),_1Qm=E(_1Qk.a);switch(B(_12Z(_1Ql.a,_1Ql.b,_1Ql.c,_1Qm.a,_1Qm.b,_1Qm.c))){case 0:var _1Qn=B(_1PQ(_1PV>>1,_1Qc));return new T3(0,new T(function(){return B(_OS(_1Qd,_1Q8,_1Qn.a));}),_1Qn.b,_1Qn.c);case 1:if(!B(_1bJ(_1HQ,_1Qj.b,_1Qk.b))){var _1Qo=B(_1PQ(_1PV>>1,_1Qc));return new T3(0,new T(function(){return B(_OS(_1Qd,_1Q8,_1Qo.a));}),_1Qo.b,_1Qo.c);}else{return new T3(0,_1Q8,_4,_1Qa);}break;default:return new T3(0,_1Q8,_4,_1Qa);}}else{var _1Qp=B(_1PQ(_1PV>>1,_1Qc));return new T3(0,new T(function(){return B(_OS(_1Qd,_1Q8,_1Qp.a));}),_1Qp.b,_1Qp.c);}}else{var _1Qq=E(_1Qf);return new T3(0,_1Q8,_4,_1Qa);}break;default:return new T3(0,_1Q8,_4,_1Qa);}}}}}},_1Qr=function(_1Qs,_1Qt,_1Qu){var _1Qv=E(_1Qu);if(!_1Qv._){return E(_1Qt);}else{var _1Qw=_1Qv.a,_1Qx=E(_1Qv.b);if(!_1Qx._){return new F(function(){return _Oe(_1Qw,_1Qt);});}else{var _1Qy=E(_1Qw),_1Qz=E(_1Qx.a),_1QA=_1Qz.b,_1QB=E(_1Qy.a),_1QC=E(_1Qz.a),_1QD=function(_1QE){var _1QF=B(_1PQ(_1Qs,_1Qx)),_1QG=_1QF.a,_1QH=E(_1QF.c);if(!_1QH._){return new F(function(){return _1Qr(_1Qs<<1,B(_OS(_1Qy,_1Qt,_1QG)),_1QF.b);});}else{return new F(function(){return _1PK(B(_OS(_1Qy,_1Qt,_1QG)),_1QH);});}};switch(B(_12Z(_1QB.a,_1QB.b,_1QB.c,_1QC.a,_1QC.b,_1QC.c))){case 0:return new F(function(){return _1QD(_);});break;case 1:var _1QI=E(_1Qy.b);if(!_1QI._){var _1QJ=E(_1QA);if(!_1QJ._){var _1QK=E(_1QI.a),_1QL=E(_1QJ.a);switch(B(_12Z(_1QK.a,_1QK.b,_1QK.c,_1QL.a,_1QL.b,_1QL.c))){case 0:return new F(function(){return _1QD(_);});break;case 1:if(!B(_1bJ(_1HQ,_1QI.b,_1QJ.b))){return new F(function(){return _1QD(_);});}else{return new F(function(){return _1PK(_1Qt,_1Qv);});}break;default:return new F(function(){return _1PK(_1Qt,_1Qv);});}}else{return new F(function(){return _1QD(_);});}}else{var _1QM=E(_1QA);return new F(function(){return _1PK(_1Qt,_1Qv);});}break;default:return new F(function(){return _1PK(_1Qt,_1Qv);});}}}},_1QN=function(_1QO){var _1QP=E(_1QO);if(!_1QP._){return new T0(1);}else{var _1QQ=_1QP.a,_1QR=E(_1QP.b);if(!_1QR._){return new T4(0,1,E(_1QQ),E(_MR),E(_MR));}else{var _1QS=E(_1QQ),_1QT=E(_1QR.a),_1QU=_1QT.b,_1QV=E(_1QS.a),_1QW=E(_1QT.a);switch(B(_12Z(_1QV.a,_1QV.b,_1QV.c,_1QW.a,_1QW.b,_1QW.c))){case 0:return new F(function(){return _1Qr(1,new T4(0,1,E(_1QS),E(_MR),E(_MR)),_1QR);});break;case 1:var _1QX=E(_1QS.b);if(!_1QX._){var _1QY=E(_1QU);if(!_1QY._){var _1QZ=E(_1QX.a),_1R0=E(_1QY.a);switch(B(_12Z(_1QZ.a,_1QZ.b,_1QZ.c,_1R0.a,_1R0.b,_1R0.c))){case 0:return new F(function(){return _1Qr(1,new T4(0,1,E(_1QS),E(_MR),E(_MR)),_1QR);});break;case 1:if(!B(_1bJ(_1HQ,_1QX.b,_1QY.b))){return new F(function(){return _1Qr(1,new T4(0,1,E(_1QS),E(_MR),E(_MR)),_1QR);});}else{return new F(function(){return _1PK(new T4(0,1,E(_1QS),E(_MR),E(_MR)),_1QR);});}break;default:return new F(function(){return _1PK(new T4(0,1,E(_1QS),E(_MR),E(_MR)),_1QR);});}}else{return new F(function(){return _1Qr(1,new T4(0,1,E(_1QS),E(_MR),E(_MR)),_1QR);});}}else{var _1R1=E(_1QU);return new F(function(){return _1PK(new T4(0,1,E(_1QS),E(_MR),E(_MR)),_1QR);});}break;default:return new F(function(){return _1PK(new T4(0,1,E(_1QS),E(_MR),E(_MR)),_1QR);});}}}},_1R2=new T(function(){return B(_7f("Muste/Grammar/Internal.hs:151:43-81|lambda"));}),_1R3=function(_1R4,_1R5){var _1R6=new T(function(){return E(E(_1R4).b);}),_1R7=function(_1R8){var _1R9=E(_1R8);if(!_1R9._){return __Z;}else{var _1Ra=new T(function(){return B(_1R7(_1R9.b));}),_1Rb=function(_1Rc){while(1){var _1Rd=B((function(_1Re){var _1Rf=E(_1Re);if(!_1Rf._){return E(_1Ra);}else{var _1Rg=_1Rf.b,_1Rh=E(_1Rf.a),_1Ri=E(_1Rh.b);if(!_1Ri._){var _1Rj=E(_1Ri.a),_1Rk=E(_1R9.a);if(!B(_12S(_1Rj.a,_1Rj.b,_1Rj.c,_1Rk.a,_1Rk.b,_1Rk.c))){_1Rc=_1Rg;return __continue;}else{return new T2(1,_1Rh,new T(function(){return B(_1Rb(_1Rg));}));}}else{return E(_1R2);}}})(_1Rc));if(_1Rd!=__continue){return _1Rd;}}};return new F(function(){return _1Rb(_1R6);});}};return new F(function(){return _1QN(B(_1R7(_1R5)));});},_1Rl=function(_1Rm,_1Rn,_1Ro,_1Rp){var _1Rq=function(_1Rr,_1Rs){while(1){var _1Rt=B((function(_1Ru,_1Rv){var _1Rw=E(_1Rv);if(!_1Rw._){_1Rr=new T2(1,new T(function(){return B(_1OS(_1Rn,_1Ro,_1Rp,_1Rw.b));}),new T(function(){return B(_1Rq(_1Ru,_1Rw.d));}));_1Rs=_1Rw.c;return __continue;}else{return E(_1Ru);}})(_1Rr,_1Rs));if(_1Rt!=__continue){return _1Rt;}}};return new F(function(){return _1LG(_MR,B(_1no(_4,B(_1LB(B(_1Rq(_4,B(_1R3(_1Rm,B(_1no(_4,B(_1Px(_1Rn)))))))))))));});},_1Rx=function(_1Ry,_1Rz,_1RA){var _1RB=E(_1Rz);return new F(function(){return _1Rl(_1Ry,_1RB.a,_1RB.b,_1RA);});},_1RC=function(_1RD,_1RE){while(1){var _1RF=B((function(_1RG,_1RH){var _1RI=E(_1RH);if(!_1RI._){return __Z;}else{var _1RJ=_1RI.a,_1RK=_1RI.b;if(!B(A1(_1RG,_1RJ))){var _1RL=_1RG;_1RD=_1RL;_1RE=_1RK;return __continue;}else{return new T2(1,_1RJ,new T(function(){return B(_1RC(_1RG,_1RK));}));}}})(_1RD,_1RE));if(_1RF!=__continue){return _1RF;}}},_1RM=function(_1RN,_1RO,_1RP){var _1RQ=new T(function(){return E(_1RP)-1|0;}),_1RR=function(_1RS){return B(_v0(E(_1RS).a,0))<=E(_1RQ);},_1RT=function(_1RU,_1RV){while(1){var _1RW=B((function(_1RX,_1RY){var _1RZ=E(_1RY);if(!_1RZ._){var _1S0=_1RZ.d,_1S1=E(_1RZ.b),_1S2=new T(function(){if(!B(_1RC(_1RR,B(_1NE(_1S1.a,_4))))._){return B(_1RT(_1RX,_1S0));}else{return new T2(1,_1S1,new T(function(){return B(_1RT(_1RX,_1S0));}));}},1);_1RU=_1S2;_1RV=_1RZ.c;return __continue;}else{return E(_1RX);}})(_1RU,_1RV));if(_1RW!=__continue){return _1RW;}}},_1S3=function(_1S4){var _1S5=E(_1S4);if(!_1S5._){return new T0(1);}else{var _1S6=_1S5.a,_1S7=B(_1Rx(_1RN,_1S6,_1RP)),_1S8=B(_1S3(B(_0(_1S5.b,new T(function(){var _1S9=E(_1S6);return B(_1RT(_4,B(_1KQ(_1S9.a,_1S9.b,_1S7))));},1))))),_1Sa=function(_1Sb,_1Sc,_1Sd,_1Se){return new F(function(){return _1jD(_1KP,_1ir,_1ir,1,_1S6,_MR,_MR,_1Sb,_1Sc,_1Sd,_1Se);});},_1Sf=E(_1S7);if(!_1Sf._){var _1Sg=_1Sf.a,_1Sh=_1Sf.b,_1Si=_1Sf.c,_1Sj=_1Sf.d,_1Sk=E(_1S8);if(!_1Sk._){var _1Sl=B(_1jD(_1KP,_1ir,_1ir,_1Sg,_1Sh,_1Si,_1Sj,_1Sk.a,_1Sk.b,_1Sk.c,_1Sk.d));if(!_1Sl._){return new F(function(){return _1Sa(_1Sl.a,_1Sl.b,_1Sl.c,_1Sl.d);});}else{return new T4(0,1,E(_1S6),E(_MR),E(_MR));}}else{return new F(function(){return _1Sa(_1Sg,_1Sh,_1Si,_1Sj);});}}else{var _1Sm=E(_1S8);if(!_1Sm._){return new F(function(){return _1Sa(_1Sm.a,_1Sm.b,_1Sm.c,_1Sm.d);});}else{return new T4(0,1,E(_1S6),E(_MR),E(_MR));}}}};return new F(function(){return _1S3(new T2(1,new T2(0,new T1(1,_1RO),new T4(0,1,E(new T2(0,_4,new T1(1,_1RO))),E(_MR),E(_MR))),_4));});},_1Sn=function(_1So){return E(E(_1So).a);},_1Sp=function(_1Sq,_1Sr,_1Ss,_1St){var _1Su=new T(function(){var _1Sv=B(_1E4(new T(function(){return B(_1Sn(_1Sr));}),_1Ss));if(!_1Sv._){return E(_1FX);}else{var _1Sw=E(_1Sv.a);if(!_1Sw._){var _1Sx=E(_1Sw.b);if(!_1Sx._){return E(_1Sx.a);}else{return E(_1OQ);}}else{return E(_1Sw.a);}}});return new F(function(){return _1RM(_1Sq,_1Su,_1St);});},_1Sy=function(_1Sz,_1SA,_1SB,_1SC){while(1){var _1SD=E(_1SA);if(!_1SD._){return E(_1SC);}else{var _1SE=_1SD.a,_1SF=E(_1SB);if(!_1SF._){return E(_1SC);}else{if(!B(A3(_pS,_1Sz,_1SE,_1SF.a))){return E(_1SC);}else{var _1SG=new T2(1,_1SE,_1SC);_1SA=_1SD.b;_1SB=_1SF.b;_1SC=_1SG;continue;}}}}},_1SH=function(_1SI,_1SJ){while(1){var _1SK=E(_1SI);if(!_1SK._){return E(_1SJ);}else{var _1SL=new T2(1,_1SK.a,_1SJ);_1SI=_1SK.b;_1SJ=_1SL;continue;}}},_1SM=function(_1SN,_1SO,_1SP,_1SQ,_1SR){while(1){var _1SS=B((function(_1ST,_1SU,_1SV,_1SW,_1SX){var _1SY=E(_1SU);if(!_1SY._){return new T2(0,_1SW,_1SX);}else{var _1SZ=_1SY.a,_1T0=_1SY.b,_1T1=E(_1SV);if(!_1T1._){return new T2(0,_1SW,_1SX);}else{var _1T2=_1T1.b;if(!B(A3(_pS,_1ST,_1SZ,_1T1.a))){var _1T3=new T(function(){return B(_1Sy(_1ST,B(_1SH(_1SY,_4)),new T(function(){return B(_1SH(_1T1,_4));},1),_4));}),_1T4=_1ST,_1T5=_1SW;_1SN=_1T4;_1SO=_1T0;_1SP=_1T2;_1SQ=_1T5;_1SR=_1T3;return __continue;}else{var _1T4=_1ST,_1T6=_1SX;_1SN=_1T4;_1SO=_1T0;_1SP=_1T2;_1SQ=new T(function(){return B(_0(_1SW,new T2(1,_1SZ,_4)));});_1SR=_1T6;return __continue;}}}})(_1SN,_1SO,_1SP,_1SQ,_1SR));if(_1SS!=__continue){return _1SS;}}},_1T7=function(_1T8,_1T9,_1Ta,_1Tb){return (!B(_1GJ(_1T8,_1Ta)))?true:(!B(_sl(_1T9,_1Tb)))?true:false;},_1Tc=function(_1Td,_1Te){var _1Tf=E(_1Td),_1Tg=E(_1Te);return new F(function(){return _1T7(_1Tf.a,_1Tf.b,_1Tg.a,_1Tg.b);});},_1Th=function(_1Ti,_1Tj,_1Tk,_1Tl){if(!B(_1GJ(_1Ti,_1Tk))){return false;}else{return new F(function(){return _sl(_1Tj,_1Tl);});}},_1Tm=function(_1Tn,_1To){var _1Tp=E(_1Tn),_1Tq=E(_1To);return new F(function(){return _1Th(_1Tp.a,_1Tp.b,_1Tq.a,_1Tq.b);});},_1Tr=new T2(0,_1Tm,_1Tc),_1Ts=function(_1Tt,_1Tu,_1Tv,_1Tw){switch(B(_1IJ(_1Tt,_1Tv))){case 0:return false;case 1:return new F(function(){return _12z(_1Tu,_1Tw);});break;default:return true;}},_1Tx=function(_1Ty,_1Tz){var _1TA=E(_1Ty),_1TB=E(_1Tz);return new F(function(){return _1Ts(_1TA.a,_1TA.b,_1TB.a,_1TB.b);});},_1TC=function(_1TD,_1TE){var _1TF=E(_1TD),_1TG=E(_1TE);switch(B(_1IJ(_1TF.a,_1TG.a))){case 0:return E(_1TG);case 1:return (B(_12j(_1TF.b,_1TG.b))==2)?E(_1TF):E(_1TG);default:return E(_1TF);}},_1TH=function(_1TI,_1TJ){var _1TK=E(_1TI),_1TL=E(_1TJ);switch(B(_1IJ(_1TK.a,_1TL.a))){case 0:return E(_1TK);case 1:return (B(_12j(_1TK.b,_1TL.b))==2)?E(_1TL):E(_1TK);default:return E(_1TL);}},_1TM=function(_1TN,_1TO,_1TP,_1TQ){switch(B(_1IJ(_1TN,_1TP))){case 0:return 0;case 1:return new F(function(){return _12j(_1TO,_1TQ);});break;default:return 2;}},_1TR=function(_1TS,_1TT){var _1TU=E(_1TS),_1TV=E(_1TT);return new F(function(){return _1TM(_1TU.a,_1TU.b,_1TV.a,_1TV.b);});},_1TW=function(_1TX,_1TY,_1TZ,_1U0){switch(B(_1IJ(_1TX,_1TZ))){case 0:return true;case 1:return new F(function(){return _12q(_1TY,_1U0);});break;default:return false;}},_1U1=function(_1U2,_1U3){var _1U4=E(_1U2),_1U5=E(_1U3);return new F(function(){return _1TW(_1U4.a,_1U4.b,_1U5.a,_1U5.b);});},_1U6=function(_1U7,_1U8,_1U9,_1Ua){switch(B(_1IJ(_1U7,_1U9))){case 0:return true;case 1:return new F(function(){return _12t(_1U8,_1Ua);});break;default:return false;}},_1Ub=function(_1Uc,_1Ud){var _1Ue=E(_1Uc),_1Uf=E(_1Ud);return new F(function(){return _1U6(_1Ue.a,_1Ue.b,_1Uf.a,_1Uf.b);});},_1Ug=function(_1Uh,_1Ui,_1Uj,_1Uk){switch(B(_1IJ(_1Uh,_1Uj))){case 0:return false;case 1:return new F(function(){return _12w(_1Ui,_1Uk);});break;default:return true;}},_1Ul=function(_1Um,_1Un){var _1Uo=E(_1Um),_1Up=E(_1Un);return new F(function(){return _1Ug(_1Uo.a,_1Uo.b,_1Up.a,_1Up.b);});},_1Uq={_:0,a:_1Tr,b:_1TR,c:_1U1,d:_1Ub,e:_1Ul,f:_1Tx,g:_1TC,h:_1TH},_1Ur=function(_1Us){var _1Ut=E(_1Us);if(!_1Ut._){return __Z;}else{return new F(function(){return _0(_1Ut.a,new T(function(){return B(_1Ur(_1Ut.b));},1));});}},_1Uu=new T1(1,_4),_1Uv=function(_1Uw){var _1Ux=E(_1Uw);if(!_1Ux._){return E(_1Uu);}else{var _1Uy=E(_1Ux.a);if(!_1Uy._){return __Z;}else{var _1Uz=B(_1Uv(_1Ux.b));return (_1Uz._==0)?__Z:new T1(1,new T2(1,_1Uy.a,_1Uz.a));}}},_1UA=function(_1UB,_1UC){var _1UD=B(_1Uv(_1UC));return (_1UD._==0)?new T2(0,_4l,_4l):new T2(0,_1UB,new T1(1,new T(function(){return B(_1Ur(_1UD.a));})));},_1UE=function(_1UF,_1UG){var _1UH=E(_1UF);if(!_1UH._){return new T2(0,_1UG,_4);}else{var _1UI=new T(function(){var _1UJ=B(_1UE(_1UH.b,_1UG));return new T2(0,_1UJ.a,_1UJ.b);}),_1UK=new T(function(){var _1UL=B(_1UM(new T(function(){return E(E(_1UI).a);}),_1UH.a));return new T2(0,_1UL.a,_1UL.b);});return new T2(0,new T(function(){return E(E(_1UK).a);}),new T2(1,new T(function(){return E(E(_1UK).b);}),new T(function(){return E(E(_1UI).b);})));}},_1UN=function(_1UO,_1UP){var _1UQ=E(_1UO);if(!_1UQ._){return new T2(0,_1UP,_4);}else{var _1UR=new T(function(){var _1US=B(_1UN(_1UQ.b,_1UP));return new T2(0,_1US.a,_1US.b);}),_1UT=new T(function(){var _1UU=B(_1UM(new T(function(){return E(E(_1UR).a);}),_1UQ.a));return new T2(0,_1UU.a,_1UU.b);});return new T2(0,new T(function(){return E(E(_1UT).a);}),new T2(1,new T(function(){return E(E(_1UT).b);}),new T(function(){return E(E(_1UR).b);})));}},_1UV=function(_1UW,_1UX){var _1UY=E(_1UW);if(!_1UY._){return new T2(0,_1UX,_4);}else{var _1UZ=new T(function(){var _1V0=B(_1UV(_1UY.b,_1UX));return new T2(0,_1V0.a,_1V0.b);}),_1V1=new T(function(){var _1V2=B(_1UM(new T(function(){return E(E(_1UZ).a);}),_1UY.a));return new T2(0,_1V2.a,_1V2.b);});return new T2(0,new T(function(){return E(E(_1V1).a);}),new T2(1,new T(function(){return E(E(_1V1).b);}),new T(function(){return E(E(_1UZ).b);})));}},_1V3=function(_1V4,_1V5){var _1V6=E(_1V4);if(!_1V6._){return new T2(0,_1V5,_4);}else{var _1V7=new T(function(){var _1V8=B(_1V3(_1V6.b,_1V5));return new T2(0,_1V8.a,_1V8.b);}),_1V9=new T(function(){var _1Va=B(_1UM(new T(function(){return E(E(_1V7).a);}),_1V6.a));return new T2(0,_1Va.a,_1Va.b);});return new T2(0,new T(function(){return E(E(_1V9).a);}),new T2(1,new T(function(){return E(E(_1V9).b);}),new T(function(){return E(E(_1V7).b);})));}},_1Vb=function(_1Vc){var _1Vd=E(_1Vc);if(!_1Vd._){return __Z;}else{return new F(function(){return _0(_1Vd.a,new T(function(){return B(_1Vb(_1Vd.b));},1));});}},_1Ve=function(_1Vf){var _1Vg=E(_1Vf);if(!_1Vg._){return E(_1Uu);}else{var _1Vh=E(_1Vg.a);if(!_1Vh._){return __Z;}else{var _1Vi=B(_1Ve(_1Vg.b));return (_1Vi._==0)?__Z:new T1(1,new T2(1,_1Vh.a,_1Vi.a));}}},_1Vj=function(_1Vk,_1Vl,_1Vm){while(1){var _1Vn=E(_1Vl);if(!_1Vn._){return true;}else{var _1Vo=E(_1Vm);if(!_1Vo._){return false;}else{if(!B(A3(_pS,_1Vk,_1Vn.a,_1Vo.a))){return false;}else{_1Vl=_1Vn.b;_1Vm=_1Vo.b;continue;}}}}},_1Vp=new T1(1,_4),_1Vq=new T(function(){return B(_7f("pgf/PGF/Macros.hs:(186,5)-(204,44)|function untokn"));}),_1UM=function(_1Vr,_1Vs){var _1Vt=E(_1Vs);switch(_1Vt._){case 0:var _1Vu=B(_1V3(_1Vt.f,_1Vr)),_1Vv=B(_1Ve(_1Vu.b));return (_1Vv._==0)?new T2(0,_4l,_4l):new T2(0,_1Vu.a,new T1(1,new T2(1,new T6(1,_1Vt.a,_1Vt.b,_1Vt.c,_1Vt.d,_1Vt.e,new T(function(){return B(_1Vb(_1Vv.a));})),_4)));case 1:var _1Vw=E(_1Vt.a);return (_1Vw._==0)?new T2(0,_1Vr,_1Vp):new T2(0,new T1(1,_1Vw),new T1(1,new T2(1,new T1(0,_1Vw),_4)));case 2:return new T2(0,_4l,_4l);case 6:var _1Vx=_1Vt.a,_1Vy=E(_1Vr);if(!_1Vy._){var _1Vz=B(_1UV(_1Vx,_4l));return new F(function(){return _1UA(_1Vz.a,_1Vz.b);});}else{var _1VA=function(_1VB){while(1){var _1VC=E(_1VB);if(!_1VC._){return false;}else{if(!B(_1Vj(_sw,_1VC.a,_1Vy.a))){_1VB=_1VC.b;continue;}else{return true;}}}},_1VD=function(_1VE){while(1){var _1VF=B((function(_1VG){var _1VH=E(_1VG);if(!_1VH._){return __Z;}else{var _1VI=_1VH.b,_1VJ=E(_1VH.a);if(!B(_1VA(_1VJ.b))){_1VE=_1VI;return __continue;}else{return new T2(1,_1VJ.a,new T(function(){return B(_1VD(_1VI));}));}}})(_1VE));if(_1VF!=__continue){return _1VF;}}},_1VK=B(_1VD(_1Vt.b));if(!_1VK._){var _1VL=B(_1UN(_1Vx,_1Vy));return new F(function(){return _1UA(_1VL.a,_1VL.b);});}else{var _1VM=B(_1UE(_1VK.a,_1Vy));return new F(function(){return _1UA(_1VM.a,_1VM.b);});}}break;default:return E(_1Vq);}},_1VN=function(_1VO,_1VP){var _1VQ=E(_1VO);if(!_1VQ._){return new T2(0,_1VP,_4);}else{var _1VR=new T(function(){var _1VS=B(_1VN(_1VQ.b,_1VP));return new T2(0,_1VS.a,_1VS.b);}),_1VT=new T(function(){var _1VU=B(_1UM(new T(function(){return E(E(_1VR).a);}),_1VQ.a));return new T2(0,_1VU.a,_1VU.b);});return new T2(0,new T(function(){return E(E(_1VT).a);}),new T2(1,new T(function(){return E(E(_1VT).b);}),new T(function(){return E(E(_1VR).b);})));}},_1VV=new T(function(){return B(unCStr(")"));}),_1VW=function(_1VX,_1VY){var _1VZ=new T(function(){var _1W0=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_1VY,_4)),_1VV));})));},1);return B(_0(B(_bZ(0,_1VX,_4)),_1W0));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1VZ)));});},_1W1=new T(function(){return B(unCStr("Int"));}),_1W2=function(_1W3,_1W4,_1W5){return new F(function(){return _eX(_ea,new T2(0,_1W4,_1W5),_1W3,_1W1);});},_1W6=new T(function(){return B(unCStr("&|"));}),_1W7=new T1(1,_1W6),_1W8=new T2(1,_1W7,_4),_1W9=new T0(2),_1Wa=new T2(1,_1W9,_4),_1Wb=new T(function(){return B(unCStr("&+"));}),_1Wc=new T1(1,_1Wb),_1Wd=new T2(1,_1Wc,_4),_1We=function(_1Wf,_1Wg,_1Wh){var _1Wi=function(_1Wj,_1Wk){var _1Wl=B(_1DV(_1Wh,_1Wj)),_1Wm=E(_1Wl.a),_1Wn=E(E(_1Wl.e).b),_1Wo=_1Wn.c,_1Wp=E(_1Wn.a),_1Wq=E(_1Wn.b);if(_1Wp>_1Wk){return new F(function(){return _1W2(_1Wk,_1Wp,_1Wq);});}else{if(_1Wk>_1Wq){return new F(function(){return _1W2(_1Wk,_1Wp,_1Wq);});}else{var _1Wr=_1Wk-_1Wp|0;if(0>_1Wr){return new F(function(){return _1VW(_1Wr,_1Wo);});}else{if(_1Wr>=_1Wo){return new F(function(){return _1VW(_1Wr,_1Wo);});}else{var _1Ws=E(_1Wn.d[_1Wr]);return (_1Ws._==0)?__Z:(!B(A1(_1Wf,_1Wm)))?E(_1Ws):new T2(1,new T(function(){return new T6(0,_1Wm.a,E(_1Wm.b),_1Wk,_1Wl.c,_1Wl.d,_1Ws);}),_4);}}}}},_1Wt=function(_1Wu){var _1Wv=E(_1Wu);if(!_1Wv._){return __Z;}else{var _1Ww=E(_1Wv.a);return new T2(1,new T2(0,new T(function(){return B(_1Wx(_1Ww.a));}),_1Ww.b),new T(function(){return B(_1Wt(_1Wv.b));}));}},_1Wy=function(_1Wz){var _1WA=E(_1Wz);if(!_1WA._){return __Z;}else{return new F(function(){return _0(B(_1WB(_1WA.a)),new T(function(){return B(_1Wy(_1WA.b));},1));});}},_1WB=function(_1WC){var _1WD=E(_1WC);switch(_1WD._){case 0:return new F(function(){return _1Wi(_1WD.a,_1WD.b);});break;case 1:return new F(function(){return _1Wi(_1WD.a,_1WD.b);});break;case 2:return new T2(1,new T1(1,new T(function(){var _1WE=B(_1DV(E(B(_1DV(_1Wh,_1WD.a)).e).a,_1WD.b));return B(_1CY(_1WE.a,_1WE.b,_1WE.c));})),_4);case 3:return new T2(1,new T1(1,_1WD.a),_4);case 4:return new T2(1,new T2(6,new T(function(){return B(_1Wy(_1WD.a));}),new T(function(){return B(_1Wt(_1WD.b));})),_4);case 5:return E(_1Wd);case 6:return E(_1Wa);case 7:return __Z;case 8:return __Z;case 9:return E(_1W8);default:return E(_1W8);}},_1Wx=function(_1WF){var _1WG=E(_1WF);if(!_1WG._){return __Z;}else{return new F(function(){return _0(B(_1WB(_1WG.a)),new T(function(){return B(_1Wx(_1WG.b));},1));});}},_1WH=function(_1WI){var _1WJ=E(_1WI);if(!_1WJ._){return __Z;}else{return new F(function(){return _0(B(_1WB(_1WJ.a)),new T(function(){return B(_1WH(_1WJ.b));},1));});}};return new F(function(){return _1WH(_1Wg);});},_1WK=function(_1WL,_1WM,_1WN){return new F(function(){return _eX(_ea,new T2(0,_1WM,_1WN),_1WL,_1W1);});},_1WO=new T(function(){return B(unCStr("Negative range size"));}),_1WP=function(_1WQ,_1WR,_1WS,_1WT,_1WU){var _1WV=new T(function(){var _1WW=function(_){var _1WX=E(_1WQ),_1WY=E(_1WX.c),_1WZ=_1WY.c,_1X0=E(_1WY.a),_1X1=E(_1WY.b),_1X2=E(_1WT);if(_1X0>_1X2){return new F(function(){return _1WK(_1X2,_1X0,_1X1);});}else{if(_1X2>_1X1){return new F(function(){return _1WK(_1X2,_1X0,_1X1);});}else{var _1X3=_1X2-_1X0|0;if(0>_1X3){return new F(function(){return _1VW(_1X3,_1WZ);});}else{if(_1X3>=_1WZ){return new F(function(){return _1VW(_1X3,_1WZ);});}else{var _1X4=E(_1WY.d[_1X3]),_1X5=E(_1X4.b),_1X6=E(_1X4.c),_1X7=function(_1X8){if(_1X8>=0){var _1X9=newArr(_1X8,_VA),_1Xa=_1X9,_1Xb=function(_1Xc){var _1Xd=function(_1Xe,_1Xf,_){while(1){if(_1Xe!=_1Xc){var _1Xg=E(_1Xf);if(!_1Xg._){return _5;}else{var _=_1Xa[_1Xe]=_1Xg.a,_1Xh=_1Xe+1|0;_1Xe=_1Xh;_1Xf=_1Xg.b;continue;}}else{return _5;}}},_1Xi=new T(function(){var _1Xj=_1X4.d-1|0;if(0<=_1Xj){var _1Xk=new T(function(){return B(_1We(_1WR,_4,_1WU));}),_1Xl=function(_1Xm){var _1Xn=new T(function(){var _1Xo=E(_1WX.f),_1Xp=_1Xo.c,_1Xq=E(_1Xo.a),_1Xr=E(_1Xo.b),_1Xs=_1X4.e["v"]["i32"][_1Xm];if(_1Xq>_1Xs){return B(_1W2(_1Xs,_1Xq,_1Xr));}else{if(_1Xs>_1Xr){return B(_1W2(_1Xs,_1Xq,_1Xr));}else{var _1Xt=_1Xs-_1Xq|0;if(0>_1Xt){return B(_1VW(_1Xt,_1Xp));}else{if(_1Xt>=_1Xp){return B(_1VW(_1Xt,_1Xp));}else{var _1Xu=E(_1Xo.d[_1Xt]),_1Xv=_1Xu.c-1|0;if(0<=_1Xv){var _1Xw=function(_1Xx){return new T2(1,new T(function(){return E(_1Xu.d[_1Xx]);}),new T(function(){if(_1Xx!=_1Xv){return B(_1Xw(_1Xx+1|0));}else{return __Z;}}));};return B(_1We(_1WR,B(_1Xw(0)),_1WU));}else{return E(_1Xk);}}}}}});return new T2(1,_1Xn,new T(function(){if(_1Xm!=_1Xj){return B(_1Xl(_1Xm+1|0));}else{return __Z;}}));};return B(_1Xl(0));}else{return __Z;}},1),_1Xy=B(_1Xd(0,_1Xi,_));return new T4(0,E(_1X5),E(_1X6),_1X8,_1Xa);};if(_1X5>_1X6){return new F(function(){return _1Xb(0);});}else{var _1Xz=(_1X6-_1X5|0)+1|0;if(_1Xz>=0){return new F(function(){return _1Xb(_1Xz);});}else{return new F(function(){return err(_1WO);});}}}else{return E(_VC);}};if(_1X5>_1X6){return new F(function(){return _1X7(0);});}else{return new F(function(){return _1X7((_1X6-_1X5|0)+1|0);});}}}}}};return B(_8O(_1WW));});return new T2(0,_1WS,_1WV);},_1XA=new T(function(){return B(unCStr(")"));}),_1XB=function(_1XC,_1XD){var _1XE=new T(function(){var _1XF=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_bZ(0,_1XD,_4)),_1XA));})));},1);return B(_0(B(_bZ(0,_1XC,_4)),_1XF));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1XE)));});},_1XG=function(_1XH){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_1XH));}))));});},_1XI=new T(function(){return B(_1XG("ww_sZJc Map CId String"));}),_1XJ=new T(function(){return B(_1XG("ww_sZJb Map CId Literal"));}),_1XK=new T1(1,_4),_1XL=new T2(1,_1XK,_4),_1XM=0,_1XN=new T(function(){return B(unCStr("Int"));}),_1XO=function(_1XP,_1XQ){return new F(function(){return _eX(_ea,new T2(0,_1XP,_1XQ),_1XM,_1XN);});},_1XR=function(_1XS){return true;},_1XT=new T(function(){return B(_1XG("ww_sZJl IntMap (IntMap (TrieMap Token IntSet))"));}),_1XU=new T(function(){return B(_1XG("ww_sZJk Map CId CncCat"));}),_1XV=new T(function(){return B(_1XG("ww_sZJj Map CId (IntMap (Set Production))"));}),_1XW=new T(function(){return B(_1XG("ww_sZJi IntMap (Set Production)"));}),_1XX=new T(function(){return B(_1XG("ww_sZJh IntMap (Set Production)"));}),_1XY=new T(function(){return B(_1XG("ww_sZJe IntMap [FunId]"));}),_1XZ=function(_1Y0,_1Y1,_1Y2,_1Y3,_1Y4,_1Y5,_1Y6,_1Y7){var _1Y8=B(_151(_1Y4,_1Y1));if(!_1Y8._){return E(_1XL);}else{var _1Y9=E(_1Y8.a);if(!_1Y9._){return E(_1XL);}else{var _1Ya=E(B(_1WP({_:0,a:_1XJ,b:_1XI,c:_1Y0,d:_1XY,e:_1Y1,f:_1Y2,g:_1XX,h:_1XW,i:_1XV,j:_1XU,k:_1XT,l:0},_1XR,_4,_1Y9.a,new T2(1,new T5(0,E(_1Y3),_1Y4,_1Y5,_1Y6,E(_1Y7)),_4))).b),_1Yb=_1Ya.c,_1Yc=E(_1Ya.a),_1Yd=E(_1Ya.b);if(_1Yc>0){return new F(function(){return _1XO(_1Yc,_1Yd);});}else{if(0>_1Yd){return new F(function(){return _1XO(_1Yc,_1Yd);});}else{var _1Ye= -_1Yc|0;if(0>_1Ye){return new F(function(){return _1XB(_1Ye,_1Yb);});}else{if(_1Ye>=_1Yb){return new F(function(){return _1XB(_1Ye,_1Yb);});}else{return E(_1Ya.d[_1Ye]);}}}}}}},_1Yf=new T(function(){return B(unCStr("no lang"));}),_1Yg=new T(function(){return B(err(_1Yf));}),_1Yh=function(_1Yi){return E(E(_1Yi).d);},_1Yj=function(_1Yk,_1Yl,_1Ym,_1Yn){var _1Yo=function(_1Yp,_1Yq,_1Yr){while(1){var _1Ys=E(_1Yq),_1Yt=E(_1Yr);if(!_1Yt._){switch(B(A3(_13t,_1Yk,_1Ys,_1Yt.b))){case 0:_1Yq=_1Ys;_1Yr=_1Yt.d;continue;case 1:return E(_1Yt.c);default:_1Yq=_1Ys;_1Yr=_1Yt.e;continue;}}else{return E(_1Yp);}}};return new F(function(){return _1Yo(_1Yl,_1Ym,_1Yn);});},_1Yu=function(_1Yv){var _1Yw=function(_){var _1Yx=newArr(1,_VA),_1Yy=_1Yx,_1Yz=function(_1YA,_1YB,_){while(1){var _1YC=E(_1YA);if(_1YC==1){return _5;}else{var _1YD=E(_1YB);if(!_1YD._){return _5;}else{var _=_1Yy[_1YC]=_1YD.a;_1YA=_1YC+1|0;_1YB=_1YD.b;continue;}}}},_1YE=B(_1Yz(0,new T2(1,new T2(1,new T1(1,_1Yv),_4),_4),_));return new T4(0,E(_1XM),E(_1XM),1,_1Yy);};return new F(function(){return _8O(_1Yw);});},_1YF=function(_1YG,_1YH,_1YI,_1YJ){while(1){var _1YK=E(_1YJ);if(!_1YK._){var _1YL=E(_1YK.b);switch(B(_12Z(_1YG,_1YH,_1YI,_1YL.a,_1YL.b,_1YL.c))){case 0:_1YJ=_1YK.d;continue;case 1:return new T1(1,_1YK.c);default:_1YJ=_1YK.e;continue;}}else{return __Z;}}},_1YM=new T(function(){return B(unCStr("Float"));}),_1YN=new T(function(){return B(_1zg(_1YM));}),_1YO=new T(function(){return B(_G(_1ze,_1YN));}),_1YP=new T(function(){var _1YQ=B(_1y0(_1YO));return new T3(0,_1YQ.a,_1YQ.b,_1YQ.c);}),_1YR=new T(function(){return B(_1zg(_1W1));}),_1YS=new T(function(){return B(_G(_1ze,_1YR));}),_1YT=new T(function(){var _1YU=B(_1y0(_1YS));return new T3(0,_1YU.a,_1YU.b,_1YU.c);}),_1YV=new T(function(){return B(unCStr("String"));}),_1YW=new T(function(){return B(_1zg(_1YV));}),_1YX=new T(function(){return B(_G(_1ze,_1YW));}),_1YY=new T(function(){var _1YZ=B(_1y0(_1YX));return new T3(0,_1YZ.a,_1YZ.b,_1YZ.c);}),_1Z0=function(_1Z1){var _1Z2=E(_1Z1);return (_1Z2._==0)?__Z:new T2(1,E(_1Z2.a).b,new T(function(){return B(_1Z0(_1Z2.b));}));},_1Z3=function(_1Z4){var _1Z5=E(_1Z4);return (_1Z5._==0)?__Z:new T2(1,new T(function(){return E(E(E(_1Z5.a).c).b);}),new T(function(){return B(_1Z3(_1Z5.b));}));},_1Z6=new T(function(){return B(_7f("pgf/PGF/Linearize.hs:(77,5)-(87,137)|function lin"));}),_1Z7=63,_1Z8=new T(function(){return B(_1NY("pgf/PGF/Linearize.hs:105:19-70|Just (ty, _, _, _)"));}),_1Z9=new T(function(){return B(_7f("pgf/PGF/Linearize.hs:(104,13)-(109,85)|function toApp"));}),_1Za=new T(function(){return B(unCStr("]"));}),_1Zb=function(_1Zc,_1Zd,_1Ze,_1Zf){if(!B(_18U(_1Zg,_1Zc,_1Ze))){return false;}else{return new F(function(){return _1aP(_1Zd,_1Zf);});}},_1Zh=function(_1Zi,_1Zj){var _1Zk=E(_1Zi),_1Zl=E(_1Zj);return new F(function(){return _1Zb(_1Zk.a,_1Zk.b,_1Zl.a,_1Zl.b);});},_1Zm=function(_1Zn,_1Zo,_1Zp,_1Zq){return (!B(_18U(_1Zg,_1Zn,_1Zp)))?true:(!B(_1aP(_1Zo,_1Zq)))?true:false;},_1Zr=function(_1Zs,_1Zt){var _1Zu=E(_1Zs),_1Zv=E(_1Zt);return new F(function(){return _1Zm(_1Zu.a,_1Zu.b,_1Zv.a,_1Zv.b);});},_1Zw=new T(function(){return new T2(0,_1Zh,_1Zr);}),_1Zx=function(_1Zy,_1Zz){var _1ZA=E(_1Zy);switch(_1ZA._){case 0:var _1ZB=E(_1Zz);if(!_1ZB._){var _1ZC=E(_1ZA.a),_1ZD=E(_1ZB.a);if(!B(_12S(_1ZC.a,_1ZC.b,_1ZC.c,_1ZD.a,_1ZD.b,_1ZD.c))){return false;}else{if(_1ZA.b!=_1ZB.b){return false;}else{if(_1ZA.c!=_1ZB.c){return false;}else{var _1ZE=E(_1ZA.d),_1ZF=E(_1ZB.d);if(!B(_12S(_1ZE.a,_1ZE.b,_1ZE.c,_1ZF.a,_1ZF.b,_1ZF.c))){return false;}else{if(!B(_18U(_194,_1ZA.e,_1ZB.e))){return false;}else{return new F(function(){return _18U(_1Zg,_1ZA.f,_1ZB.f);});}}}}}}else{return false;}break;case 1:var _1ZG=E(_1Zz);if(_1ZG._==1){return new F(function(){return _sl(_1ZA.a,_1ZG.a);});}else{return false;}break;case 2:return (E(_1Zz)._==2)?true:false;case 3:return (E(_1Zz)._==3)?true:false;case 4:return (E(_1Zz)._==4)?true:false;case 5:return (E(_1Zz)._==5)?true:false;default:var _1ZH=E(_1Zz);if(_1ZH._==6){if(!B(_18U(_1Zg,_1ZA.a,_1ZH.a))){return false;}else{return new F(function(){return _18U(_1Zw,_1ZA.b,_1ZH.b);});}}else{return false;}}},_1ZI=function(_1ZJ,_1ZK){return (!B(_1Zx(_1ZJ,_1ZK)))?true:false;},_1Zg=new T(function(){return new T2(0,_1Zx,_1ZI);}),_1ZL=function(_1ZM,_1ZN){var _1ZO=E(_1ZM),_1ZP=E(_1ZN),_1ZQ=E(_1ZO.c);if(!_1ZQ){return (E(_1ZP.c)==0)?true:false;}else{if(E(_1ZO.a)!=E(_1ZP.a)){return false;}else{if(E(_1ZO.b)!=E(_1ZP.b)){return false;}else{var _1ZR=_1ZQ-1|0;if(0<=_1ZR){var _1ZS=function(_1ZT){while(1){if(!B(_18U(_1Zg,_1ZO.d[_1ZT],_1ZP.d[_1ZT]))){return false;}else{if(_1ZT!=_1ZR){var _1ZU=_1ZT+1|0;_1ZT=_1ZU;continue;}else{return true;}}}};return new F(function(){return _1ZS(0);});}else{return true;}}}}},_1ZV=function(_1ZW,_1ZX){var _1ZY=E(_1ZW),_1ZZ=E(_1ZX),_200=E(_1ZY.a),_201=E(_1ZZ.a),_202=E(_200.a),_203=E(_201.a);if(!B(_12S(_202.a,_202.b,_202.c,_203.a,_203.b,_203.c))){return false;}else{if(E(_200.b)!=E(_201.b)){return false;}else{if(E(_1ZY.b)!=E(_1ZZ.b)){return false;}else{var _204=E(_1ZY.c),_205=E(_1ZZ.c);if(!B(_12S(_204.a,_204.b,_204.c,_205.a,_205.b,_205.c))){return false;}else{if(!B(_18U(_194,_1ZY.d,_1ZZ.d))){return false;}else{var _206=E(_1ZY.e),_207=E(_1ZZ.e);if(!B(_18U(_1Gp,_206.a,_207.a))){return false;}else{return new F(function(){return _1ZL(_206.b,_207.b);});}}}}}}},_208=function(_209,_20a,_20b){while(1){var _20c=E(_20b);if(!_20c._){return false;}else{if(!B(A2(_209,_20c.a,_20a))){_20b=_20c.b;continue;}else{return true;}}}},_20d=function(_20e,_20f){var _20g=function(_20h,_20i){while(1){var _20j=B((function(_20k,_20l){var _20m=E(_20k);if(!_20m._){return __Z;}else{var _20n=_20m.a,_20o=_20m.b;if(!B(_208(_20e,_20n,_20l))){return new T2(1,_20n,new T(function(){return B(_20g(_20o,new T2(1,_20n,_20l)));}));}else{var _20p=_20l;_20h=_20o;_20i=_20p;return __continue;}}})(_20h,_20i));if(_20j!=__continue){return _20j;}}};return new F(function(){return _20g(_20f,_4);});},_20q=function(_20r){return E(E(_20r).b);},_20s=function(_20t,_20u,_20v){var _20w=new T(function(){return E(E(E(_20t).c).b);}),_20x=new T(function(){return E(E(_20u).h);}),_20y=new T(function(){return E(E(_20u).d);}),_20z=function(_20A,_20B,_20C,_20D,_20E){var _20F=E(_20A);if(!_20F._){return __Z;}else{var _20G=E(_20F.a),_20H=_20G.a,_20I=E(_20G.b),_20J=B(_151(_20I,_20y));if(!_20J._){if(!B(_w5(_j7,_20I,_1p4))){var _20K=B(_151(_20I,_20x));if(!_20K._){return __Z;}else{var _20L=function(_20M,_20N){while(1){var _20O=B((function(_20P,_20Q){var _20R=E(_20Q);if(!_20R._){var _20S=_20R.d,_20T=new T(function(){var _20U=E(_20R.b);if(_20U._==1){return B(_0(B(_20z(new T1(1,new T2(0,_20H,_20U.a)),_20B,_20C,_20D,_20E)),new T(function(){return B(_20L(_20P,_20S));},1)));}else{return B(_20L(_20P,_20S));}},1);_20M=_20T;_20N=_20R.c;return __continue;}else{return E(_20P);}})(_20M,_20N));if(_20O!=__continue){return _20O;}}};return new F(function(){return _20L(_4,_20K.a);});}}else{var _20V=new T(function(){var _20W=function(_){var _20X=newArr(1,_VA),_20Y=_20X,_20Z=function(_210,_211,_){while(1){var _212=E(_210);if(_212==1){return _5;}else{var _213=E(_211);if(!_213._){return _5;}else{var _=_20Y[_212]=_213.a;_210=_212+1|0;_211=_213.b;continue;}}}},_214=B(_20Z(0,new T2(1,new T2(1,new T1(1,_20E),_4),_4),_));return new T4(0,E(_1XM),E(_1XM),1,_20Y);};return B(_8O(_20W));});return new T2(1,new T2(0,new T(function(){return E(_20B)+2|0;}),new T5(0,new T2(0,_20H,new T(function(){return E(_20B)+1|0;})),_20I,_1OQ,new T2(1,_20C,_4),new T2(0,_20D,_20V))),_4);}}else{var _215=new T2(1,_20C,_4),_216=new T(function(){return E(_20B)+2|0;}),_217=new T(function(){return B(_1Yu(_20E));}),_218=new T(function(){return E(_20B)+1|0;}),_219=function(_21a){var _21b=E(_21a);return (_21b._==0)?__Z:new T2(1,new T2(0,_216,new T5(0,new T2(0,_20H,_218),_20I,_1OQ,_215,new T(function(){var _21c=B(_1WP(_20u,_1XR,_20D,_21b.a,new T2(1,new T5(0,new T2(0,_1OQ,_20B),_1oY,_1OQ,_215,new T2(0,_4,_217)),_4)));return new T2(0,_21c.a,_21c.b);}))),new T(function(){return B(_219(_21b.b));}));};return new F(function(){return _219(_20J.a);});}}},_21d=new T(function(){return E(E(_20u).i);}),_21e=function(_21f,_21g,_21h,_21i,_21j,_21k,_21l){while(1){var _21m=B((function(_21n,_21o,_21p,_21q,_21r,_21s,_21t){var _21u=E(_21s);switch(_21u._){case 0:var _21v=_21n,_21w=_21o,_21x=_21p,_21y=_21q,_21z=new T2(1,_21u.b,_21r),_21A=_21t;_21f=_21v;_21g=_21w;_21h=_21x;_21i=_21y;_21j=_21z;_21k=_21u.c;_21l=_21A;return __continue;case 1:var _21v=_21n,_21w=_21o,_21x=_21p,_21y=_21q,_21z=_21r,_21A=new T2(1,_21u.b,_21t);_21f=_21v;_21g=_21w;_21h=_21x;_21i=_21y;_21j=_21z;_21k=_21u.a;_21l=_21A;return __continue;case 2:if(!E(_21t)._){var _21B=E(_21u.a);switch(_21B._){case 0:return new T2(1,new T2(0,new T(function(){return E(_21o)+1|0;}),new T5(0,new T2(0,_1YY,_21o),_1oY,_1OQ,new T2(1,_21p,_4),new T2(0,_4,new T(function(){return B(_1Yu(_21B.a));})))),_4);case 1:var _21C=new T(function(){return B(_1Yu(new T(function(){return B(_bZ(0,E(_21B.a),_4));})));});return new T2(1,new T2(0,new T(function(){return E(_21o)+1|0;}),new T5(0,new T2(0,_1YT,_21o),_1oZ,_1OQ,new T2(1,_21p,_4),new T2(0,_4,_21C))),_4);default:var _21D=new T(function(){return B(_1Yu(new T(function(){var _21E=jsShow(E(_21B.a));return fromJSStr(_21E);})));});return new T2(1,new T2(0,new T(function(){return E(_21o)+1|0;}),new T5(0,new T2(0,_1YP,_21o),_1p0,_1OQ,new T2(1,_21p,_4),new T2(0,_4,_21D))),_4);}}else{return E(_1Z6);}break;case 3:return new F(function(){return _20z(_21n,_21o,_21p,_21r,new T2(1,_1Z7,new T(function(){return B(_bZ(0,_21u.a,_4));})));});break;case 4:var _21F=E(_21u.a),_21G=_21F.a,_21H=_21F.b,_21I=_21F.c,_21J=B(_1YF(_21G,_21H,_21I,_21d));if(!_21J._){var _21K=new T(function(){return B(unAppCStr("[",new T(function(){return B(_0(B(_1CY(_21G,_21H,_21I)),_1Za));})));});return new F(function(){return _20z(_21n,_21o,_21p,_21r,_21K);});}else{var _21L=_21J.a,_21M=new T(function(){var _21N=B(_1YF(_21G,_21H,_21I,_20w));if(!_21N._){return E(_1Z8);}else{var _21O=E(E(_21N.a).a);return new T2(0,new T(function(){return B(_1Z3(_21O.a));}),_21O.b);}}),_21P=new T(function(){return E(E(_21M).b);}),_21Q=new T(function(){return E(E(_21M).a);}),_21R=function(_21S,_21T){var _21U=E(_21T);switch(_21U._){case 0:var _21V=new T(function(){return B(_jV(_21Q,new T(function(){return B(_1Z0(_21U.b));},1)));});return new T2(1,new T3(0,_21U.a,new T2(0,_21P,_21S),_21V),_4);case 1:var _21W=_21U.a,_21X=B(_151(_21W,_21L));if(!_21X._){return __Z;}else{var _21Y=function(_21Z,_220){while(1){var _221=B((function(_222,_223){var _224=E(_223);if(!_224._){var _225=new T(function(){return B(_0(B(_21R(_21W,_224.b)),new T(function(){return B(_21Y(_222,_224.d));},1)));},1);_21Z=_225;_220=_224.c;return __continue;}else{return E(_222);}})(_21Z,_220));if(_221!=__continue){return _221;}}};return new F(function(){return _21Y(_4,_21X.a);});}break;default:return E(_1Z9);}},_226=new T(function(){return B(_0(_21r,_21q));}),_227=function(_228,_229){var _22a=E(_229);if(!_22a._){return new T2(1,new T2(0,_228,_4),_4);}else{var _22b=E(_22a.a),_22c=_22b.b,_22d=function(_22e){var _22f=E(_22e);if(!_22f._){return __Z;}else{var _22g=E(_22f.a),_22h=new T(function(){return B(_22d(_22f.b));}),_22i=function(_22j){var _22k=E(_22j);if(!_22k._){return E(_22h);}else{var _22l=E(_22k.a);return new T2(1,new T2(0,_22l.a,new T2(1,_22g.b,_22l.b)),new T(function(){return B(_22i(_22k.b));}));}};return new F(function(){return _22i(B(_227(_22g.a,_22a.b)));});}};return new F(function(){return _22d(B(_21e(new T1(1,_22b.a),_228,_22c,_226,_4,_22c,_4)));});}},_22m=function(_22n,_22o,_22p,_22q,_22r){var _22s=function(_22t){var _22u=E(_22t);if(!_22u._){return E(_22r);}else{var _22v=E(_22u.a),_22w=_22v.a;return new T2(1,new T2(0,new T(function(){return E(_22w)+1|0;}),new T5(0,new T2(0,_22o,_22w),_22p,_21F,new T2(1,_21p,_4),new T(function(){var _22x=B(_1WP(_20u,_1XR,_21r,_22n,_22v.b));return new T2(0,_22x.a,_22x.b);}))),new T(function(){return B(_22s(_22u.b));}));}};return new F(function(){return _22s(B(_227(_21o,B(_jV(_22q,_21t)))));});},_22y=E(_21n);if(!_22y._){var _22z=function(_22A,_22B){while(1){var _22C=B((function(_22D,_22E){var _22F=E(_22E);switch(_22F._){case 0:_22A=new T(function(){return B(_22z(_22D,_22F.d));},1);_22B=_22F.c;return __continue;case 1:var _22G=function(_22H,_22I){while(1){var _22J=B((function(_22K,_22L){var _22M=E(_22L);if(!_22M._){var _22N=new T(function(){var _22O=new T(function(){return B(_22G(_22K,_22M.d));}),_22P=function(_22Q){var _22R=E(_22Q);if(!_22R._){return E(_22O);}else{var _22S=E(_22R.a),_22T=E(_22S.b);return new F(function(){return _22m(_22S.a,_22T.a,_22T.b,_22S.c,new T(function(){return B(_22P(_22R.b));}));});}};return B(_22P(B(_21R(_22F.a,_22M.b))));},1);_22H=_22N;_22I=_22M.c;return __continue;}else{return E(_22K);}})(_22H,_22I));if(_22J!=__continue){return _22J;}}};return new F(function(){return _22G(_22D,_22F.b);});break;default:return E(_22D);}})(_22A,_22B));if(_22C!=__continue){return _22C;}}},_22U=E(_21L);if(!_22U._){var _22V=_22U.c,_22W=_22U.d;if(_22U.b>=0){return new F(function(){return _22z(new T(function(){return B(_22z(_4,_22W));},1),_22V);});}else{return new F(function(){return _22z(new T(function(){return B(_22z(_4,_22V));},1),_22W);});}}else{return new F(function(){return _22z(_4,_22U);});}}else{var _22X=E(E(_22y.a).b),_22Y=B(_151(_22X,_21L));if(!_22Y._){return __Z;}else{var _22Z=function(_230,_231){while(1){var _232=B((function(_233,_234){var _235=E(_234);if(!_235._){var _236=new T(function(){var _237=new T(function(){return B(_22Z(_233,_235.d));}),_238=function(_239){var _23a=E(_239);if(!_23a._){return E(_237);}else{var _23b=E(_23a.a),_23c=E(_23b.b);return new F(function(){return _22m(_23b.a,_23c.a,_23c.b,_23b.c,new T(function(){return B(_238(_23a.b));}));});}};return B(_238(B(_21R(_22X,_235.b))));},1);_230=_236;_231=_235.c;return __continue;}else{return E(_233);}})(_230,_231));if(_232!=__continue){return _232;}}};return new F(function(){return _22Z(_4,_22Y.a);});}}}break;case 5:return new F(function(){return _20z(_21n,_21o,_21p,_21r,new T(function(){var _23d=B(_1DV(B(_0(_21r,_21q)),_21u.a));return B(_1CY(_23d.a,_23d.b,_23d.c));}));});break;case 6:var _21v=_21n,_21w=_21o,_21x=_21p,_21y=_21q,_21z=_21r,_21A=_21t;_21f=_21v;_21g=_21w;_21h=_21x;_21i=_21y;_21j=_21z;_21k=_21u.a;_21l=_21A;return __continue;default:var _21v=_21n,_21w=_21o,_21x=_21p,_21y=_21q,_21z=_21r,_21A=_21t;_21f=_21v;_21g=_21w;_21h=_21x;_21i=_21y;_21j=_21z;_21k=_21u.a;_21l=_21A;return __continue;}})(_21f,_21g,_21h,_21i,_21j,_21k,_21l));if(_21m!=__continue){return _21m;}}};return new F(function(){return _20d(_1ZV,B(_G(_20q,B(_21e(_4l,_1XM,_20v,_4,_4,_20v,_4)))));});},_23e=function(_23f){var _23g=E(_23f);if(!_23g._){return __Z;}else{return new F(function(){return _0(_23g.a,new T(function(){return B(_23e(_23g.b));},1));});}},_23h=function(_23i){var _23j=E(_23i);if(!_23j._){return E(_1Uu);}else{var _23k=E(_23j.a);if(!_23k._){return __Z;}else{var _23l=B(_23h(_23j.b));return (_23l._==0)?__Z:new T1(1,new T2(1,_23k.a,_23l.a));}}},_23m=function(_23n,_23o){var _23p=new T(function(){return B(_1Yj(_1HQ,_1Yg,_23o,B(_1Yh(_23n))));}),_23q=function(_23r,_23s,_23t,_23u,_23v){var _23w=E(_23p),_23x=B(_23h(B(_1VN(B(_1XZ(_23w.c,_23w.e,_23w.f,_23r,_23s,_23t,_23u,_23v)),_4l)).b));if(!_23x._){return __Z;}else{return new F(function(){return _23e(_23x.a);});}},_23y=function(_23z){var _23A=E(_23z);return new F(function(){return _23q(_23A.a,E(_23A.b),_23A.c,_23A.d,_23A.e);});};return function(_23B){var _23C=B(_G(_23y,B(_20s(_23n,_23p,_23B))));return (_23C._==0)?__Z:E(_23C.a);};},_23D=new T(function(){return B(unCStr("?0"));}),_23E=new T2(0,_4,_23D),_23F=new T2(1,_23E,_4),_23G=0,_23H=new T(function(){return B(_1SH(_4,_4));}),_23I=function(_23J,_23K,_23L,_23M){while(1){var _23N=B((function(_23O,_23P,_23Q,_23R){var _23S=E(_23O);if(!_23S._){return __Z;}else{var _23T=_23S.b,_23U=E(_23S.a);if(!_23U._){var _23V=E(_23P);if(E(_23U.b)!=_23V){var _23W=B(_23I(_23U.c,_23V,new T2(1,_23R,_23Q),_23G));if(!_23W._){var _23X=_23Q;_23J=_23T;_23K=_23V;_23L=_23X;_23M=new T(function(){return E(_23R)+1|0;});return __continue;}else{return E(_23W);}}else{return new T2(1,_23R,_23Q);}}else{var _23Y=_23P,_23X=_23Q;_23J=_23T;_23K=_23Y;_23L=_23X;_23M=new T(function(){return E(_23R)+1|0;});return __continue;}}})(_23J,_23K,_23L,_23M));if(_23N!=__continue){return _23N;}}},_23Z=function(_240,_241){var _242=E(_240);if(!_242._){var _243=E(_241);if(E(_242.b)!=_243){return new F(function(){return _1SH(B(_23I(_242.c,_243,_4,_23G)),_4);});}else{return E(_23H);}}else{return E(_23H);}},_244=new T(function(){return B(_7f("Muste.hs:(45,9)-(54,31)|function deep"));}),_245=function(_246,_247,_248,_249){var _24a=E(_248);if(!_24a._){return E(_249);}else{var _24b=_24a.b,_24c=E(_24a.a);if(!_24c._){return new T2(1,new T2(0,new T(function(){return B(_23Z(_246,_247));}),_24c.a),new T(function(){return B(_245(_246,_247,_24b,_249));}));}else{return new F(function(){return _0(B(_24d(_246,_24c)),new T(function(){return B(_245(_246,_247,_24b,_249));},1));});}}},_24d=function(_24e,_24f){var _24g=E(_24f);if(!_24g._){return E(_244);}else{var _24h=_24g.b,_24i=E(_24g.f);if(!_24i._){return __Z;}else{var _24j=function(_24k){var _24l=E(_24g.e);if(!_24l._){return new F(function(){return _245(_24e,_24h,_24i,_4);});}else{var _24m=E(_24l.a);if(_24m._==3){if(!E(_24l.b)._){var _24n=new T(function(){return B(unAppCStr("?",new T(function(){return B(_bZ(0,_24m.a,_4));})));});return new T2(1,new T2(0,new T(function(){return B(_23Z(_24e,_24h));}),_24n),_4);}else{return new F(function(){return _245(_24e,_24h,_24i,_4);});}}else{return new F(function(){return _245(_24e,_24h,_24i,_4);});}}},_24o=E(_24i.a);if(!_24o._){if(!E(_24i.b)._){return new T2(1,new T2(0,new T(function(){return B(_23Z(_24e,_24h));}),_24o.a),_4);}else{return new F(function(){return _24j(_);});}}else{return new F(function(){return _24j(_);});}}}},_24p=function(_24q){return E(E(_24q).c);},_24r=function(_24s){return new T1(3,E(_24s));},_24t=function(_24u,_24v){while(1){var _24w=E(_24u);if(!_24w._){return E(_24v);}else{var _24x=new T2(1,_24v,_24w.a);_24u=_24w.b;_24v=_24x;continue;}}},_24y=function(_24z,_24A){var _24B=E(_24z);if(!_24B._){var _24C=new T(function(){var _24D=B(_24E(_24B.c,_24A));return new T2(0,_24D.a,_24D.b);});return new T2(0,new T(function(){return E(E(_24C).a);}),new T(function(){return B(_24t(E(_24C).b,new T1(4,_24B.a)));}));}else{return new T2(0,new T(function(){return E(_24A)+1|0;}),new T(function(){return B(_24r(_24A));}));}},_24E=function(_24F,_24G){var _24H=E(_24F);if(!_24H._){return new T2(0,_24G,_4);}else{var _24I=new T(function(){var _24J=B(_24y(_24H.a,_24G));return new T2(0,_24J.a,_24J.b);}),_24K=new T(function(){var _24L=B(_24E(_24H.b,new T(function(){return E(E(_24I).a);})));return new T2(0,_24L.a,_24L.b);});return new T2(0,new T(function(){return E(E(_24K).a);}),new T2(1,new T(function(){return E(E(_24I).b);}),new T(function(){return E(E(_24K).b);})));}},_24M=new T1(3,0),_24N=function(_24O){var _24P=E(_24O);if(!_24P._){return new F(function(){return _24t(B(_24E(_24P.c,_23G)).b,new T1(4,_24P.a));});}else{return E(_24M);}},_24Q=-1,_24R=function(_24S){var _24T=B(_24U(_24S));return new T3(0,_24T.a,_24T.b,_24T.c);},_24V=new T(function(){return B(unCStr("_"));}),_24W=new T(function(){return B(_1zg(_24V));}),_24X=new T(function(){return B(_G(_1ze,_24W));}),_24Y=new T(function(){var _24Z=B(_1y0(_24X));return new T3(0,_24Z.a,_24Z.b,_24Z.c);}),_250=new T0(1),_251=new T2(1,_250,_4),_252=new T3(0,_24Y,_24Q,_251),_253=new T2(1,_252,_4),_254=new T(function(){return B(_7f("Muste/Tree/Internal.hs:(285,5)-(287,70)|function convert"));}),_24U=function(_255){var _256=E(_255);if(!_256._){var _257=E(_256.b);if(!_257._){var _258=_257.a,_259=E(_256.c);return (_259._==0)?new T3(0,_258,_24Q,_4):new T3(0,_258,_24Q,new T(function(){return B(_G(_24R,_259));}));}else{return E(_254);}}else{return new T3(0,_256.a,_24Q,_253);}},_25a=function(_25b,_25c){var _25d=E(_25c);if(!_25d._){return new T2(0,_25b,_4);}else{var _25e=new T(function(){var _25f=E(_25d.a);if(!_25f._){var _25g=_25f.a,_25h=E(_25f.c);if(!_25h._){return new T2(0,new T(function(){return E(_25b)+1|0;}),new T3(0,_25g,_25b,_4));}else{var _25i=new T(function(){var _25j=B(_25a(_25b,_25h));return new T2(0,_25j.a,_25j.b);}),_25k=new T(function(){return E(E(_25i).a);});return new T2(0,new T(function(){return E(_25k)+1|0;}),new T3(0,_25g,_25k,new T(function(){return E(E(_25i).b);})));}}else{return new T2(0,_25b,_250);}}),_25l=new T(function(){var _25m=B(_25a(new T(function(){return E(E(_25e).a);}),_25d.b));return new T2(0,_25m.a,_25m.b);});return new T2(0,new T(function(){return E(E(_25l).a);}),new T2(1,new T(function(){return E(E(_25e).b);}),new T(function(){return E(E(_25l).b);})));}},_25n=function(_25o){var _25p=B(_24U(_25o)),_25q=_25p.a,_25r=E(_25p.c);if(!_25r._){return new T3(0,_25q,_23G,_4);}else{var _25s=new T(function(){var _25t=B(_25a(_23G,_25r));return new T2(0,_25t.a,_25t.b);});return new T3(0,_25q,new T(function(){return E(E(_25s).a);}),new T(function(){return E(E(_25s).b);}));}},_25u=function(_25v,_25w,_25x){var _25y=new T(function(){return E(E(_25x).a);}),_25z=B(A3(_23m,new T(function(){return B(_24p(_25v));}),_25w,new T(function(){return B(_24N(_25y));})));if(!_25z._){return E(_23F);}else{return new F(function(){return _24d(new T(function(){return B(_25n(_25y));}),_25z.a);});}},_25A=new T2(1,_4,_4),_25B=function(_25C,_25D){var _25E=function(_25F,_25G){var _25H=E(_25F);if(!_25H._){return E(_25G);}else{var _25I=_25H.a,_25J=E(_25G);if(!_25J._){return E(_25H);}else{var _25K=_25J.a;return (B(A2(_25C,_25I,_25K))==2)?new T2(1,_25K,new T(function(){return B(_25E(_25H,_25J.b));})):new T2(1,_25I,new T(function(){return B(_25E(_25H.b,_25J));}));}}},_25L=function(_25M){var _25N=E(_25M);if(!_25N._){return __Z;}else{var _25O=E(_25N.b);return (_25O._==0)?E(_25N):new T2(1,new T(function(){return B(_25E(_25N.a,_25O.a));}),new T(function(){return B(_25L(_25O.b));}));}},_25P=new T(function(){return B(_25Q(B(_25L(_4))));}),_25Q=function(_25R){while(1){var _25S=E(_25R);if(!_25S._){return E(_25P);}else{if(!E(_25S.b)._){return E(_25S.a);}else{_25R=B(_25L(_25S));continue;}}}},_25T=new T(function(){return B(_25U(_4));}),_25V=function(_25W,_25X,_25Y){while(1){var _25Z=B((function(_260,_261,_262){var _263=E(_262);if(!_263._){return new T2(1,new T2(1,_260,_261),_25T);}else{var _264=_263.a;if(B(A2(_25C,_260,_264))==2){var _265=new T2(1,_260,_261);_25W=_264;_25X=_265;_25Y=_263.b;return __continue;}else{return new T2(1,new T2(1,_260,_261),new T(function(){return B(_25U(_263));}));}}})(_25W,_25X,_25Y));if(_25Z!=__continue){return _25Z;}}},_266=function(_267,_268,_269){while(1){var _26a=B((function(_26b,_26c,_26d){var _26e=E(_26d);if(!_26e._){return new T2(1,new T(function(){return B(A1(_26c,new T2(1,_26b,_4)));}),_25T);}else{var _26f=_26e.a,_26g=_26e.b;switch(B(A2(_25C,_26b,_26f))){case 0:_267=_26f;_268=function(_26h){return new F(function(){return A1(_26c,new T2(1,_26b,_26h));});};_269=_26g;return __continue;case 1:_267=_26f;_268=function(_26i){return new F(function(){return A1(_26c,new T2(1,_26b,_26i));});};_269=_26g;return __continue;default:return new T2(1,new T(function(){return B(A1(_26c,new T2(1,_26b,_4)));}),new T(function(){return B(_25U(_26e));}));}}})(_267,_268,_269));if(_26a!=__continue){return _26a;}}},_25U=function(_26j){var _26k=E(_26j);if(!_26k._){return E(_25A);}else{var _26l=_26k.a,_26m=E(_26k.b);if(!_26m._){return new T2(1,_26k,_4);}else{var _26n=_26m.a,_26o=_26m.b;if(B(A2(_25C,_26l,_26n))==2){return new F(function(){return _25V(_26n,new T2(1,_26l,_4),_26o);});}else{return new F(function(){return _266(_26n,function(_26p){return new T2(1,_26l,_26p);},_26o);});}}}};return new F(function(){return _25Q(B(_25U(_25D)));});},_26q=function(_26r,_26s,_26t,_26u){var _26v=B(_1no(_4,_26u)),_26w=new T(function(){return B(_G(_20q,B(_25u(_26r,_26s,_26t))));}),_26x=function(_26y,_26z){var _26A=E(_26y);if(!_26A._){return __Z;}else{var _26B=E(_26z);return (_26B._==0)?__Z:new T2(1,new T2(0,new T(function(){var _26C=E(_26w);if(!_26C._){var _26D=B(_v0(_4,0));return _26D+_26D|0;}else{var _26E=B(_G(_20q,B(_25u(_26r,_26s,_26A.a))));if(!_26E._){var _26F=B(_v0(_4,0));return _26F+_26F|0;}else{var _26G=B(_1SM(_sF,_26C,_26E,_4,_4));return B(_v0(_26G.a,0))+B(_v0(_26G.b,0))|0;}}}),_26B.a),new T(function(){return B(_26x(_26A.b,_26B.b));}));}};return new F(function(){return _G(_20q,B(_25B(function(_26H,_26I){var _26J=E(_26H),_26K=E(_26I),_26L=E(_26K.a),_26M=E(_26J.a);if(_26L>=_26M){if(_26L!=_26M){return 2;}else{var _26N=B(_25u(_26r,_26s,_26J.b)),_26O=B(_v0(_26N,0)),_26P=B(_25u(_26r,_26s,_26K.b)),_26Q=B(_v0(_26P,0));if(_26O>=_26Q){if(_26O!=_26Q){return 2;}else{return new F(function(){return _1bJ(_1Uq,_26N,_26P);});}}else{return 0;}}}else{return 0;}},B(_26x(_26v,_26v)))));});},_26R=function(_26S){while(1){var _26T=E(_26S);if(!_26T._){return false;}else{if(!E(_26T.a)){_26S=_26T.b;continue;}else{return true;}}}},_26U=function(_26V){var _26W=E(_26V);if(!_26W._){return new F(function(){return _26R(B(_G(_26U,_26W.c)));});}else{return true;}},_26X=function(_26Y){return (!B(_26U(B(_1Sn(_26Y)))))?true:false;},_26Z=function(_270){while(1){var _271=E(_270);if(!_271._){_270=new T1(1,I_fromInt(_271.a));continue;}else{return new F(function(){return I_toString(_271.a);});}}},_272=function(_273,_274){return new F(function(){return _0(fromJSStr(B(_26Z(_273))),_274);});},_275=new T1(0,0),_276=function(_277,_278,_279){if(_277<=6){return new F(function(){return _272(_278,_279);});}else{if(!B(_Fs(_278,_275))){return new F(function(){return _272(_278,_279);});}else{return new T2(1,_bY,new T(function(){return B(_0(fromJSStr(B(_26Z(_278))),new T2(1,_bX,_279)));}));}}},_27a=new T1(0,1),_27b=new T1(0,0),_27c=new T(function(){var _27d=B(_JH(_27b,_27a));return new T2(1,_27d.a,_27d.b);}),_27e=32,_27f=new T(function(){return B(unCStr(" "));}),_27g=new T2(0,_4,_27f),_27h=new T2(1,_27g,_4),_27i=function(_27j){var _27k=E(_27j);if(!_27k._){return E(_27h);}else{var _27l=E(_27k.a);return new T2(1,new T2(0,_27l.a,_27f),new T2(1,_27l,new T(function(){return B(_27i(_27k.b));})));}},_27m=function(_27n,_27o,_27p){var _27q=function(_27r,_27s){var _27t=E(_27r);if(!_27t._){return __Z;}else{var _27u=_27t.b,_27v=E(_27s);if(!_27v._){return __Z;}else{var _27w=_27v.b,_27x=new T(function(){var _27y=E(_27v.a),_27z=new T(function(){var _27A=new T(function(){if(!E(_27n)){return __Z;}else{return B(unAppCStr(" ",new T(function(){return B(_3X(_e4,_27y.a,_4));})));}},1);return B(_0(_27y.b,_27A));});if(!E(_27o)){return B(_0(_27z,new T(function(){return B(_27q(_27u,_27w));},1)));}else{var _27B=new T(function(){return B(_0(B(_276(0,_27t.a,_4)),new T(function(){return B(unAppCStr(") ",_27z));},1)));});return B(_0(B(unAppCStr("(",_27B)),new T(function(){return B(_27q(_27u,_27w));},1)));}});return new T2(1,_27e,_27x);}}},_27C=B(_27q(_27c,new T(function(){return B(_27i(_27p));},1)));return (_27C._==0)?__Z:E(_27C.b);},_27D=function(_27E,_27F,_27G){var _27H=function(_27I){return new F(function(){return _27m(_wd,_wd,new T(function(){return B(_25u(_27E,_27F,_27I));},1));});};return new F(function(){return _G(_27H,_27G);});},_27J=function(_27K,_27L){var _27M=E(_27L);if(!_27M._){return new T2(0,_4,_4);}else{var _27N=_27M.a;if(!B(A1(_27K,_27N))){var _27O=new T(function(){var _27P=B(_27J(_27K,_27M.b));return new T2(0,_27P.a,_27P.b);});return new T2(0,new T2(1,_27N,new T(function(){return E(E(_27O).a);})),new T(function(){return E(E(_27O).b);}));}else{return new T2(0,_4,_27M);}}},_27Q=function(_27R){var _27S=_27R>>>0;if(_27S>887){var _27T=u_iswspace(_27R);return (E(_27T)==0)?false:true;}else{var _27U=E(_27S);return (_27U==32)?true:(_27U-9>>>0>4)?(E(_27U)==160)?true:false:true;}},_27V=function(_27W){return new F(function(){return _27Q(E(_27W));});},_27X=function(_27Y){var _27Z=B(_Gd(_27V,_27Y));if(!_27Z._){return __Z;}else{var _280=new T(function(){var _281=B(_27J(_27V,_27Z));return new T2(0,_281.a,_281.b);});return new T2(1,new T(function(){return E(E(_280).a);}),new T(function(){return B(_27X(E(_280).b));}));}},_282=function(_283,_284,_285,_286,_287,_288){var _289=new T(function(){var _28a=B(_1E4(new T(function(){return B(_1Sn(_285));}),_286));if(!_28a._){return E(_1FX);}else{return E(_28a.a);}}),_28b=new T2(0,_289,_MR),_28c=new T(function(){return B(_G(_20q,B(_25u(_283,_284,_28b))));}),_28d=new T(function(){return B(_v0(_28c,0));}),_28e=new T(function(){var _28f=B(_v0(B(_25u(_283,_284,_28b)),0));if(!E(_287)){return _28f;}else{return _28f+1|0;}}),_28g=B(_1RC(function(_28h){return E(_28e)>=B(_v0(B(_25u(_283,_284,_28h)),0));},B(_26q(_283,_284,_28b,B(_1o7(_26X,B(_1Sp(_283,_285,_286,_288)))))))),_28i=function(_28j,_28k){while(1){var _28l=B((function(_28m,_28n){var _28o=E(_28m);if(!_28o._){return __Z;}else{var _28p=_28o.a,_28q=_28o.b,_28r=E(_28n);if(!_28r._){return __Z;}else{var _28s=_28r.a,_28t=_28r.b,_28u=B(_27X(_28p));if(!B(_1aP(_28u,_28c))){var _28v=B(_v0(_28u,0)),_28w=E(_28d);if(_28v!=_28w){if(_28v<=_28w){_28j=_28q;_28k=_28t;return __continue;}else{var _28x=E(_28u);if(!_28x._){var _28y=B(_v0(_4,0));if(!(_28y+_28y|0)){_28j=_28q;_28k=_28t;return __continue;}else{return new T2(1,new T2(0,_28p,_28s),new T(function(){return B(_28i(_28q,_28t));}));}}else{var _28z=E(_28c);if(!_28z._){var _28A=B(_v0(_4,0));if(!(_28A+_28A|0)){_28j=_28q;_28k=_28t;return __continue;}else{return new T2(1,new T2(0,_28p,_28s),new T(function(){return B(_28i(_28q,_28t));}));}}else{var _28B=B(_1SM(_sF,_28x,_28z,_4,_4));if(!(B(_v0(_28B.a,0))+B(_v0(_28B.b,0))|0)){_28j=_28q;_28k=_28t;return __continue;}else{return new T2(1,new T2(0,_28p,_28s),new T(function(){return B(_28i(_28q,_28t));}));}}}}}else{return new T2(1,new T2(0,_28p,_28s),new T(function(){return B(_28i(_28q,_28t));}));}}else{_28j=_28q;_28k=_28t;return __continue;}}}})(_28j,_28k));if(_28l!=__continue){return _28l;}}};return new F(function(){return _28i(B(_27D(_283,_284,_28g)),_28g);});},_28C=new T(function(){return B(unCStr("offsetLeft"));}),_28D=new T(function(){return new T2(0,E(new T1(2,"id")),"suggestionList");}),_28E=1,_28F=new T(function(){return B(err(_rq));}),_28G=new T(function(){return B(err(_rs));}),_28H=function(_28I,_28J){var _28K=function(_28L,_28M){var _28N=function(_28O){return new F(function(){return A1(_28M,new T(function(){return  -E(_28O);}));});},_28P=new T(function(){return B(_CX(function(_28Q){return new F(function(){return A3(_28I,_28Q,_28L,_28N);});}));}),_28R=function(_28S){return E(_28P);},_28T=function(_28U){return new F(function(){return A2(_BE,_28U,_28R);});},_28V=new T(function(){return B(_CX(function(_28W){var _28X=E(_28W);if(_28X._==4){var _28Y=E(_28X.a);if(!_28Y._){return new F(function(){return A3(_28I,_28X,_28L,_28M);});}else{if(E(_28Y.a)==45){if(!E(_28Y.b)._){return E(new T1(1,_28T));}else{return new F(function(){return A3(_28I,_28X,_28L,_28M);});}}else{return new F(function(){return A3(_28I,_28X,_28L,_28M);});}}}else{return new F(function(){return A3(_28I,_28X,_28L,_28M);});}}));}),_28Z=function(_290){return E(_28V);};return new T1(1,function(_291){return new F(function(){return A2(_BE,_291,_28Z);});});};return new F(function(){return _DO(_28K,_28J);});},_292=function(_293){var _294=E(_293);if(!_294._){var _295=_294.b,_296=new T(function(){return B(_vf(new T(function(){return B(_oF(E(_294.a)));}),new T(function(){return B(_v0(_295,0));},1),B(_G(_v5,_295))));});return new T1(1,_296);}else{return (E(_294.b)._==0)?(E(_294.c)._==0)?new T1(1,new T(function(){return B(_vw(_uZ,_294.a));})):__Z:__Z;}},_297=function(_298){var _299=E(_298);if(_299._==5){var _29a=B(_292(_299.a));if(!_29a._){return E(_GM);}else{var _29b=new T(function(){return B(_oV(_29a.a));});return function(_29c,_29d){return new F(function(){return A1(_29d,_29b);});};}}else{return E(_GM);}},_29e=new T(function(){return B(A3(_28H,_297,_Du,_Is));}),_29f=new T(function(){return B(unCStr("Click on suggestion"));}),_29g=new T(function(){return B(unCStr("px"));}),_29h=new T(function(){return B(unCStr(")"));}),_29i=new T(function(){return new T1(1,"left");}),_29j=new T(function(){return new T1(1,"top");}),_29k=new T(function(){return new T2(0,E(new T1(2,"class")),"menu");}),_29l=new T(function(){return B(unCStr("offsetTop"));}),_29m=new T(function(){return eval("(function(e){if(e){e.stopPropagation();}})");}),_29n=function(_){var _29o=rMV(E(_1EF)),_29p=E(_29o);if(!_29p._){var _29q=__app1(E(_29m),E(_D));return new F(function(){return _u(_);});}else{var _29r=__app1(E(_29m),E(_29p.a));return new F(function(){return _u(_);});}},_29s=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_29t=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_29u=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_29v=function(_29w,_29x,_29y,_29z){var _29A=new T(function(){return B(A2(_1G0,_29w,_29y));}),_29B=function(_29C,_){var _29D=E(_29C);if(!_29D._){return _5;}else{var _29E=E(_29A),_29F=E(_1Ev),_29G=__app2(_29F,E(_29D.a),_29E),_29H=function(_29I,_){while(1){var _29J=E(_29I);if(!_29J._){return _5;}else{var _29K=__app2(_29F,E(_29J.a),_29E);_29I=_29J.b;continue;}}};return new F(function(){return _29H(_29D.b,_);});}},_29L=function(_29M,_){while(1){var _29N=B((function(_29O,_){var _29P=E(_29O);if(!_29P._){return _5;}else{var _29Q=_29P.b,_29R=E(_29P.a);if(!_29R._){var _29S=_29R.b,_29T=E(_29R.a);switch(_29T._){case 0:var _29U=E(_29A),_29V=E(_29u),_29W=__app3(_29V,_29U,_29T.a,_29S),_29X=function(_29Y,_){while(1){var _29Z=E(_29Y);if(!_29Z._){return _5;}else{var _2a0=_29Z.b,_2a1=E(_29Z.a);if(!_2a1._){var _2a2=_2a1.b,_2a3=E(_2a1.a);switch(_2a3._){case 0:var _2a4=__app3(_29V,_29U,_2a3.a,_2a2);_29Y=_2a0;continue;case 1:var _2a5=__app3(E(_29t),_29U,_2a3.a,_2a2);_29Y=_2a0;continue;default:var _2a6=__app3(E(_29s),_29U,_2a3.a,_2a2);_29Y=_2a0;continue;}}else{var _2a7=B(_29B(_2a1.a,_));_29Y=_2a0;continue;}}}};return new F(function(){return _29X(_29Q,_);});break;case 1:var _2a8=E(_29A),_2a9=E(_29t),_2aa=__app3(_2a9,_2a8,_29T.a,_29S),_2ab=function(_2ac,_){while(1){var _2ad=E(_2ac);if(!_2ad._){return _5;}else{var _2ae=_2ad.b,_2af=E(_2ad.a);if(!_2af._){var _2ag=_2af.b,_2ah=E(_2af.a);switch(_2ah._){case 0:var _2ai=__app3(E(_29u),_2a8,_2ah.a,_2ag);_2ac=_2ae;continue;case 1:var _2aj=__app3(_2a9,_2a8,_2ah.a,_2ag);_2ac=_2ae;continue;default:var _2ak=__app3(E(_29s),_2a8,_2ah.a,_2ag);_2ac=_2ae;continue;}}else{var _2al=B(_29B(_2af.a,_));_2ac=_2ae;continue;}}}};return new F(function(){return _2ab(_29Q,_);});break;default:var _2am=E(_29A),_2an=E(_29s),_2ao=__app3(_2an,_2am,_29T.a,_29S),_2ap=function(_2aq,_){while(1){var _2ar=E(_2aq);if(!_2ar._){return _5;}else{var _2as=_2ar.b,_2at=E(_2ar.a);if(!_2at._){var _2au=_2at.b,_2av=E(_2at.a);switch(_2av._){case 0:var _2aw=__app3(E(_29u),_2am,_2av.a,_2au);_2aq=_2as;continue;case 1:var _2ax=__app3(E(_29t),_2am,_2av.a,_2au);_2aq=_2as;continue;default:var _2ay=__app3(_2an,_2am,_2av.a,_2au);_2aq=_2as;continue;}}else{var _2az=B(_29B(_2at.a,_));_2aq=_2as;continue;}}}};return new F(function(){return _2ap(_29Q,_);});}}else{var _2aA=B(_29B(_29R.a,_));_29M=_29Q;return __continue;}}})(_29M,_));if(_29N!=__continue){return _29N;}}};return new F(function(){return A2(_6i,_29x,function(_){return new F(function(){return _29L(_29z,_);});});});},_2aB=function(_2aC,_2aD,_2aE,_2aF){var _2aG=B(_2z(_2aD)),_2aH=function(_2aI){return new F(function(){return A3(_6c,_2aG,new T(function(){return B(_29v(_2aC,_2aD,_2aI,_2aF));}),new T(function(){return B(A2(_dh,_2aG,_2aI));}));});};return new F(function(){return A3(_1V,_2aG,_2aE,_2aH);});},_2aJ=new T(function(){return eval("(function(x){console.log(x);})");}),_2aK=function(_2aL,_2aM,_2aN,_2aO,_2aP,_2aQ,_){var _2aR=B(_29n(_)),_2aS=E(_2aM),_2aT=rMV(_2aS),_2aU=new T(function(){var _2aV=E(E(_2aT).d);if(!_2aV._){return new T2(0,_2aN,_28E);}else{var _2aW=E(_2aV.a),_2aX=E(_2aN);if(E(_2aW.a)!=_2aX){return new T2(0,_2aX,_28E);}else{return new T2(0,_2aX,new T(function(){return E(_2aW.b)+1|0;}));}}}),_=wMV(_2aS,new T5(0,new T(function(){return E(E(_2aT).a);}),new T(function(){return E(E(_2aT).b);}),new T(function(){return E(E(_2aT).c);}),new T1(1,_2aU),new T(function(){return E(E(_2aT).e);}))),_2aY=B(A(_1Gb,[_dm,_dn,_2aL,_28C,_])),_2aZ=B(A(_1Gb,[_dm,_dn,_2aL,_29l,_])),_2b0=new T(function(){return E(E(_2aQ).a);}),_2b1=new T(function(){var _2b2=B(_Iz(B(_rx(_29e,_2aY))));if(!_2b2._){return E(_28F);}else{if(!E(_2b2.b)._){return E(E(_2b0).a)+E(_2b2.a)|0;}else{return E(_28G);}}}),_2b3=new T(function(){var _2b4=B(_Iz(B(_rx(_29e,_2aZ))));if(!_2b4._){return E(_28F);}else{if(!E(_2b4.b)._){return E(E(_2b0).b)+E(_2b4.a)|0;}else{return E(_28G);}}}),_2b5=new T(function(){var _2b6=new T(function(){return B(unAppCStr(",",new T(function(){return B(_0(B(_bZ(0,E(_2b3),_4)),_29h));})));},1);return B(_0(B(_bZ(0,E(_2b1),_4)),_2b6));}),_2b7=E(_2aJ),_2b8=__app1(_2b7,toJSStr(B(unAppCStr("Click on (",_2b5)))),_2b9=B(_1FQ(_1Em,_)),_2ba=new T(function(){var _2bb=(B(_v0(_2aO,0))+1|0)-E(E(_2aU).b)|0;if(0>=_2bb){return __Z;}else{return B(_1Eg(_2bb,_2aO));}}),_2bc=new T(function(){return B(_3X(_e4,_2ba,_4));}),_2bd=new T(function(){return B(_0(B(_3X(_e4,_2aO,_4)),new T(function(){return B(unAppCStr(" with selected path ",_2bc));},1)));}),_2be=__app1(_2b7,toJSStr(B(unAppCStr("Full path ",_2bd)))),_2bf=B(A(_2aB,[_dm,_dn,_1Fq,new T2(1,_28D,new T2(1,_29k,new T2(1,new T(function(){return new T2(0,E(_29j),toJSStr(B(_0(B(_bZ(0,E(_2b3),_4)),_29g))));}),new T2(1,new T(function(){return new T2(0,E(_29i),toJSStr(B(_0(B(_bZ(0,E(_2b1),_4)),_29g))));}),_4)))),_])),_2bg=_2bf,_2bh=function(_2bi,_){while(1){var _2bj=B((function(_2bk,_){var _2bl=E(_2bk);if(!_2bl._){return _5;}else{var _2bm=E(_2bl.a),_2bn=_2bm.b,_2bo=new T(function(){var _2bp=new T(function(){var _2bq=new T(function(){return B(unAppCStr(" with ",new T(function(){return B(_1Ds(E(_2bn).a));})));},1);return B(_0(_2bc,_2bq));});return B(unAppCStr(" at ",_2bp));}),_2br=new T(function(){return E(E(_2bn).a);}),_2bs=function(_2bt,_){var _2bu=B(_29n(_)),_2bv=__app1(_2b7,toJSStr(E(_29f))),_2bw=B(_1FQ(_1Em,_)),_2bx=rMV(_2aS),_2by=new T(function(){return E(E(_2bx).c);}),_2bz=new T(function(){var _2bA=B(_1E4(new T(function(){return B(_1Sn(_2by));}),_2ba));if(!_2bA._){return E(_1FX);}else{var _2bB=new T(function(){return B(unAppCStr(" in ",new T(function(){return B(_0(B(_1Ds(E(_2by).a)),_2bo));})));},1);return B(_0(B(_1Ds(_2bA.a)),_2bB));}}),_2bC=__app1(_2b7,toJSStr(B(unAppCStr("Trying to replace ",_2bz)))),_=wMV(_2aS,new T5(0,new T(function(){return E(E(_2bx).a);}),new T(function(){return E(E(_2bx).b);}),new T2(0,new T(function(){return B(_1O8(B(_1Sn(_2by)),_2ba,_2br));}),_MR),_4l,new T(function(){return E(E(_2bx).e)+1|0;}))),_2bD=B(_1Fv(_2aS,_));return new F(function(){return _2bE(_2aS,_);});},_2bF=B(_1Fb(_2bg,_2bm.a,_2bs,_));_2bi=_2bl.b;return __continue;}})(_2bi,_));if(_2bj!=__continue){return _2bj;}}},_2bG=B(_2bh(B(_282(new T(function(){return E(E(_2aT).a);}),new T(function(){return E(E(_2aT).b);}),new T(function(){return E(E(_2aT).c);}),_2ba,_2aP,_1FV)),_)),_2bH=__app2(E(_1Ev),E(_2bg),E(_1FJ));return _5;},_2bI=new T(function(){return eval("(function(e,c) {return e.classList.contains(c);})");}),_2bJ=new T(function(){return B(_iF(0,2147483647));}),_2bK=function(_){return new F(function(){return __app1(E(_1Eu),"span");});},_2bL=new T(function(){return new T2(0,E(new T1(2,"class")),"path");}),_2bM=new T2(1,_2bL,_4),_2bN=new T(function(){return B(_2aB(_dm,_dn,_2bK,_2bM));}),_2bO=new T(function(){return B(unCStr("debug"));}),_2bP=new T(function(){return new T2(0,E(new T1(2,"class")),"word");}),_2bQ=new T2(1,_2bP,_4),_2bR=new T(function(){return B(_2aB(_dm,_dn,_2bK,_2bQ));}),_2bS=new T(function(){return new T2(0,E(new T1(2,"class")),"gap");}),_2bT=new T2(1,_2bS,_4),_2bU=new T(function(){return B(_2aB(_dm,_dn,_2bK,_2bT));}),_2bV=new T(function(){return B(unCStr("ACK"));}),_2bW=new T(function(){return B(unCStr("BEL"));}),_2bX=new T(function(){return B(unCStr("BS"));}),_2bY=new T(function(){return B(unCStr("SP"));}),_2bZ=new T2(1,_2bY,_4),_2c0=new T(function(){return B(unCStr("US"));}),_2c1=new T2(1,_2c0,_2bZ),_2c2=new T(function(){return B(unCStr("RS"));}),_2c3=new T2(1,_2c2,_2c1),_2c4=new T(function(){return B(unCStr("GS"));}),_2c5=new T2(1,_2c4,_2c3),_2c6=new T(function(){return B(unCStr("FS"));}),_2c7=new T2(1,_2c6,_2c5),_2c8=new T(function(){return B(unCStr("ESC"));}),_2c9=new T2(1,_2c8,_2c7),_2ca=new T(function(){return B(unCStr("SUB"));}),_2cb=new T2(1,_2ca,_2c9),_2cc=new T(function(){return B(unCStr("EM"));}),_2cd=new T2(1,_2cc,_2cb),_2ce=new T(function(){return B(unCStr("CAN"));}),_2cf=new T2(1,_2ce,_2cd),_2cg=new T(function(){return B(unCStr("ETB"));}),_2ch=new T2(1,_2cg,_2cf),_2ci=new T(function(){return B(unCStr("SYN"));}),_2cj=new T2(1,_2ci,_2ch),_2ck=new T(function(){return B(unCStr("NAK"));}),_2cl=new T2(1,_2ck,_2cj),_2cm=new T(function(){return B(unCStr("DC4"));}),_2cn=new T2(1,_2cm,_2cl),_2co=new T(function(){return B(unCStr("DC3"));}),_2cp=new T2(1,_2co,_2cn),_2cq=new T(function(){return B(unCStr("DC2"));}),_2cr=new T2(1,_2cq,_2cp),_2cs=new T(function(){return B(unCStr("DC1"));}),_2ct=new T2(1,_2cs,_2cr),_2cu=new T(function(){return B(unCStr("DLE"));}),_2cv=new T2(1,_2cu,_2ct),_2cw=new T(function(){return B(unCStr("SI"));}),_2cx=new T2(1,_2cw,_2cv),_2cy=new T(function(){return B(unCStr("SO"));}),_2cz=new T2(1,_2cy,_2cx),_2cA=new T(function(){return B(unCStr("CR"));}),_2cB=new T2(1,_2cA,_2cz),_2cC=new T(function(){return B(unCStr("FF"));}),_2cD=new T2(1,_2cC,_2cB),_2cE=new T(function(){return B(unCStr("VT"));}),_2cF=new T2(1,_2cE,_2cD),_2cG=new T(function(){return B(unCStr("LF"));}),_2cH=new T2(1,_2cG,_2cF),_2cI=new T(function(){return B(unCStr("HT"));}),_2cJ=new T2(1,_2cI,_2cH),_2cK=new T2(1,_2bX,_2cJ),_2cL=new T2(1,_2bW,_2cK),_2cM=new T2(1,_2bV,_2cL),_2cN=new T(function(){return B(unCStr("ENQ"));}),_2cO=new T2(1,_2cN,_2cM),_2cP=new T(function(){return B(unCStr("EOT"));}),_2cQ=new T2(1,_2cP,_2cO),_2cR=new T(function(){return B(unCStr("ETX"));}),_2cS=new T2(1,_2cR,_2cQ),_2cT=new T(function(){return B(unCStr("STX"));}),_2cU=new T2(1,_2cT,_2cS),_2cV=new T(function(){return B(unCStr("SOH"));}),_2cW=new T2(1,_2cV,_2cU),_2cX=new T(function(){return B(unCStr("NUL"));}),_2cY=new T2(1,_2cX,_2cW),_2cZ=92,_2d0=new T(function(){return B(unCStr("\\DEL"));}),_2d1=new T(function(){return B(unCStr("\\a"));}),_2d2=new T(function(){return B(unCStr("\\\\"));}),_2d3=new T(function(){return B(unCStr("\\SO"));}),_2d4=new T(function(){return B(unCStr("\\r"));}),_2d5=new T(function(){return B(unCStr("\\f"));}),_2d6=new T(function(){return B(unCStr("\\v"));}),_2d7=new T(function(){return B(unCStr("\\n"));}),_2d8=new T(function(){return B(unCStr("\\t"));}),_2d9=new T(function(){return B(unCStr("\\b"));}),_2da=function(_2db,_2dc){if(_2db<=127){var _2dd=E(_2db);switch(_2dd){case 92:return new F(function(){return _0(_2d2,_2dc);});break;case 127:return new F(function(){return _0(_2d0,_2dc);});break;default:if(_2dd<32){var _2de=E(_2dd);switch(_2de){case 7:return new F(function(){return _0(_2d1,_2dc);});break;case 8:return new F(function(){return _0(_2d9,_2dc);});break;case 9:return new F(function(){return _0(_2d8,_2dc);});break;case 10:return new F(function(){return _0(_2d7,_2dc);});break;case 11:return new F(function(){return _0(_2d6,_2dc);});break;case 12:return new F(function(){return _0(_2d5,_2dc);});break;case 13:return new F(function(){return _0(_2d4,_2dc);});break;case 14:return new F(function(){return _0(_2d3,new T(function(){var _2df=E(_2dc);if(!_2df._){return __Z;}else{if(E(_2df.a)==72){return B(unAppCStr("\\&",_2df));}else{return E(_2df);}}},1));});break;default:return new F(function(){return _0(new T2(1,_2cZ,new T(function(){return B(_1DV(_2cY,_2de));})),_2dc);});}}else{return new T2(1,_2dd,_2dc);}}}else{var _2dg=new T(function(){var _2dh=jsShowI(_2db);return B(_0(fromJSStr(_2dh),new T(function(){var _2di=E(_2dc);if(!_2di._){return __Z;}else{var _2dj=E(_2di.a);if(_2dj<48){return E(_2di);}else{if(_2dj>57){return E(_2di);}else{return B(unAppCStr("\\&",_2di));}}}},1)));});return new T2(1,_2cZ,_2dg);}},_2dk=new T(function(){return B(unCStr("\\\""));}),_2dl=function(_2dm,_2dn){var _2do=E(_2dm);if(!_2do._){return E(_2dn);}else{var _2dp=_2do.b,_2dq=E(_2do.a);if(_2dq==34){return new F(function(){return _0(_2dk,new T(function(){return B(_2dl(_2dp,_2dn));},1));});}else{return new F(function(){return _2da(_2dq,new T(function(){return B(_2dl(_2dp,_2dn));}));});}}},_2dr=34,_2ds=function(_2dt,_2du){return new T2(1,_2dr,new T(function(){return B(_2dl(_2dt,new T2(1,_2dr,_2du)));}));},_2dv=function(_2dw,_2dx){var _2dy=E(_2dw),_2dz=new T(function(){return B(A3(_em,_ec,new T2(1,function(_2dA){return new F(function(){return _e7(_2dy.a,_2dA);});},new T2(1,function(_2dB){return new F(function(){return _2ds(_2dy.b,_2dB);});},_4)),new T2(1,_bX,_2dx)));});return new T2(1,_bY,_2dz);},_2dC=new T(function(){return B(unCStr(" "));}),_2dD=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:104:7-21"));}),_2dE=new T6(0,_4l,_4m,_4,_2dD,_4l,_4l),_2dF=new T(function(){return B(_4d(_2dE));}),_2dG=new T(function(){return B(unCStr("linTree"));}),_2bE=function(_2dH,_){var _2dI=rMV(_2dH),_2dJ=B(_25u(new T(function(){return E(E(_2dI).a);},1),new T(function(){return E(E(_2dI).b);},1),new T(function(){return E(E(_2dI).c);},1))),_2dK=__app1(E(_2aJ),toJSStr(B(_3X(_2dv,_2dJ,_4)))),_2dL=__app1(E(_1Fs),toJSStr(E(_2dG))),_2dM=__eq(_2dL,E(_D)),_2dN=function(_,_2dO){var _2dP=E(_2dO);if(!_2dP._){return new F(function(){return die(_2dF);});}else{var _2dQ=E(_2dP.a),_2dR=__app1(E(_1Fr),_2dQ),_2dS=__app2(E(_2bI),_2dQ,toJSStr(E(_2bO))),_2dT=_2dS,_2dU=function(_2dV,_2dW,_){while(1){var _2dX=B((function(_2dY,_2dZ,_){var _2e0=E(_2dY);if(!_2e0._){return _5;}else{var _2e1=_2e0.a,_2e2=_2e0.b,_2e3=E(_2dZ);if(!_2e3._){return _5;}else{var _2e4=_2e3.b,_2e5=E(_2e3.a),_2e6=_2e5.a,_2e7=B(A1(_2bU,_)),_2e8=E(_1Ex),_2e9=__app1(_2e8,toJSStr(E(_2dC))),_2ea=E(_2e7),_2eb=E(_1Ev),_2ec=__app2(_2eb,_2e9,_2ea),_2ed=B(A(_1EJ,[_do,_df,_de,_2ea,_1Cb,function(_2ee,_){return new F(function(){return _2aK(_2ea,_2dH,_2e1,_2e6,_we,_2ee,_);});},_])),_2ef=__app2(_2eb,_2ea,_2dQ),_2eg=B(A1(_2bR,_)),_2eh=__app1(_2e8,toJSStr(E(_2e5.b))),_2ei=E(_2eg),_2ej=__app2(_2eb,_2eh,_2ei),_2ek=B(A(_1EJ,[_do,_df,_de,_2ei,_1Cb,function(_2ee,_){return new F(function(){return _2aK(_2ei,_2dH,_2e1,_2e6,_wd,_2ee,_);});},_])),_2el=__app2(_2eb,_2ei,_2dQ);if(!_2dT){_2dV=_2e2;_2dW=_2e4;return __continue;}else{var _2em=B(A1(_2bN,_)),_2en=__app1(_2e8,toJSStr(B(_3X(_e4,_2e6,_4)))),_2eo=E(_2em),_2ep=__app2(_2eb,_2en,_2eo),_2eq=__app2(_2eb,_2eo,_2dQ);_2dV=_2e2;_2dW=_2e4;return __continue;}}}})(_2dV,_2dW,_));if(_2dX!=__continue){return _2dX;}}},_2er=B(_2dU(_2bJ,_2dJ,_));return _5;}};if(!E(_2dM)){var _2es=__isUndef(_2dL);if(!E(_2es)){return new F(function(){return _2dN(_,new T1(1,_2dL));});}else{return new F(function(){return _2dN(_,_4l);});}}else{return new F(function(){return _2dN(_,_4l);});}},_2et=new T(function(){return eval("(function(a){var arr = new ByteArray(new a.constructor(a[\'buffer\']));return new T4(0,0,a[\'length\']-1,a[\'length\'],arr);})");}),_2eu=function(_2ev){return E(_2ev);},_2ew=function(_2ex){return E(E(_2ex).a);},_2ey=function(_2ez){return E(E(_2ez).a);},_2eA=function(_2eB){return E(E(_2eB).a);},_2eC=function(_2eD){return E(E(_2eD).b);},_2eE=function(_2eF){return E(E(_2eF).a);},_2eG=function(_2eH){var _2eI=new T(function(){return B(A2(_2eE,B(_2ew(B(_2eA(B(_2ey(B(_2eC(_2eH)))))))),_2eu));}),_2eJ=function(_2eK){var _2eL=function(_){return new F(function(){return __app1(E(_2et),E(_2eK));});};return new F(function(){return A1(_2eI,_2eL);});};return E(_2eJ);},_2eM="(function(from, to, buf){return new Uint8Array(buf.buffer.slice(from, to+from));})",_2eN=function(_2eO,_2eP,_2eQ,_2eR){var _2eS=function(_){var _2eT=eval(E(_2eM)),_2eU=__app3(E(_2eT),E(_2eP),E(_2eQ),E(_2eR));return new F(function(){return A3(_2eG,_2eO,_2eU,0);});};return new F(function(){return _z(_2eS);});},_2eV=new T(function(){return B(unCStr("menuList"));}),_2eW=new T(function(){return eval("(function(b){return b.size;})");}),_2eX=function(_2eY){return new F(function(){return _z(function(_){var _2eZ=__app1(E(_2eW),E(_2eY));return new F(function(){return _cr(_2eZ,0);});});});},_2f0=0,_2f1=new T1(1,_4),_2f2=new T(function(){return eval("(function(b,cb){var r=new FileReader();r.onload=function(){cb(new DataView(r.result));};r.readAsArrayBuffer(b);})");}),_2f3=function(_2f4,_2f5){var _2f6=new T(function(){return B(_2eX(_2f5));}),_2f7=function(_2f8){var _2f9=function(_){var _2fa=nMV(_2f1),_2fb=_2fa,_2fc=function(_){var _2fd=function(_2fe,_){var _2ff=B(_c(new T(function(){return B(A(_7r,[_2l,_2fb,new T3(0,_2f0,_2f6,_2fe),_2c]));}),_4,_));return _D;},_2fg=__createJSFunc(2,E(_2fd)),_2fh=__app2(E(_2f2),E(_2f5),_2fg);return new T(function(){return B(A3(_7H,_2l,_2fb,_2f8));});};return new T1(0,_2fc);};return new T1(0,_2f9);};return new F(function(){return A2(_6g,_2f4,_2f7);});},_2fi=function(_2fj,_2fk){while(1){var _2fl=E(_2fk);if(!_2fl._){_2fj=_2fl.b;_2fk=_2fl.d;continue;}else{return E(_2fj);}}},_2fm=new T(function(){return B(unCStr("Reset"));}),_2fn=0,_2fo=new T(function(){return B(unCStr("AjaxError"));}),_2fp=new T(function(){return B(err(_2fo));}),_2fq=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:204:51-56"));}),_2fr=new T(function(){return B(unCStr("Toggle Debug"));}),_2fs=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:59:5-13"));}),_2ft=new T6(0,_4l,_4m,_4,_2fs,_4l,_4l),_2fu=new T(function(){return B(_4d(_2ft));}),_2fv=new T(function(){return B(unCStr("Click on menu"));}),_2fw=new T(function(){return B(unCStr("menuButton"));}),_2fx=new T(function(){return B(unCStr("global click"));}),_2fy=new T(function(){return B(unCStr("Got blobdata"));}),_2fz=new T(function(){return B(unCStr("Foods.pgf"));}),_2fA=new T(function(){return B(unAppCStr("Loaded pgf as Blob ",_2fz));}),_2fB=new T(function(){return new T2(0,E(new T1(2,"id")),"menuList");}),_2fC=function(_2fD,_2fE,_2fF,_2fG){while(1){var _2fH=E(_2fG);if(!_2fH._){var _2fI=E(_2fH.b);switch(B(_12Z(_2fD,_2fE,_2fF,_2fI.a,_2fI.b,_2fI.c))){case 0:_2fG=_2fH.d;continue;case 1:return new T1(1,_2fH.c);default:_2fG=_2fH.e;continue;}}else{return __Z;}}},_2fJ=function(_2fK){return E(E(E(_2fK).c).b);},_2fL=function(_2fM,_2fN,_2fO,_2fP,_2fQ){var _2fR=E(_1OQ);if(!B(_12S(_2fM,_2fN,_2fO,_2fR.a,_2fR.b,_2fR.c))){var _2fS=E(_2fQ),_2fT=B(_2fC(_2fS.a,_2fS.b,_2fS.c,E(_2fP).b));if(!_2fT._){return new T0(1);}else{var _2fU=new T(function(){var _2fV=E(E(_2fT.a).a);return new T3(0,_2fV.a,_2fV.b,_2fV.c);});return new T2(0,new T(function(){return E(E(_2fU).b);}),new T(function(){return B(_G(_2fJ,E(_2fU).a));}));}}else{return new T0(1);}},_2fW=function(_2fX,_2fY,_2fZ,_2g0){while(1){var _2g1=E(_2g0);if(!_2g1._){var _2g2=E(_2g1.b);switch(B(_12Z(_2fX,_2fY,_2fZ,_2g2.a,_2g2.b,_2g2.c))){case 0:_2g0=_2g1.d;continue;case 1:return new T1(1,_2g1.c);default:_2g0=_2g1.e;continue;}}else{return __Z;}}},_2g3=new T(function(){return B(unCStr("S"));}),_2g4=new T(function(){return B(_1zg(_2g3));}),_2g5=new T(function(){return B(_G(_1ze,_2g4));}),_2g6=new T(function(){return B(unCStr("startcat"));}),_2g7=new T(function(){return B(_1zg(_2g6));}),_2g8=new T(function(){return B(_G(_1ze,_2g7));}),_2g9=new T(function(){var _2ga=B(_1y0(_2g8));return new T3(0,_2ga.a,_2ga.b,_2ga.c);}),_2gb=function(_2gc,_2gd){var _2ge=E(_2g9),_2gf=_2ge.a,_2gg=_2ge.b,_2gh=_2ge.c,_2gi=B(_2fW(_2gf,_2gg,_2gh,_2gc));if(!_2gi._){var _2gj=B(_2fW(_2gf,_2gg,_2gh,E(_2gd).a));if(!_2gj._){return new F(function(){return _1y0(_2g5);});}else{var _2gk=E(_2gj.a);if(!_2gk._){return new F(function(){return _1y0(B(_G(_1ze,B(_1zg(_2gk.a)))));});}else{return new F(function(){return _1y0(_2g5);});}}}else{var _2gl=E(_2gi.a);if(!_2gl._){return new F(function(){return _1y0(B(_G(_1ze,B(_1zg(_2gl.a)))));});}else{return new F(function(){return _1y0(_2g5);});}}},_2gm=function(_2gn,_2go){return new T2(0,_2gn,_2go);},_2gp=new T(function(){return B(unCStr("empty grammar, no abstract"));}),_2gq=new T(function(){return B(err(_2gp));}),_2gr=new T4(0,_Rm,_1OQ,_2gq,_Rm),_2gs=function(_2gt,_2gu){while(1){var _2gv=B((function(_2gw,_2gx){var _2gy=E(_2gx);if(!_2gy._){_2gt=new T2(1,_2gy.b,new T(function(){return B(_2gs(_2gw,_2gy.e));}));_2gu=_2gy.d;return __continue;}else{return E(_2gw);}})(_2gt,_2gu));if(_2gv!=__continue){return _2gv;}}},_2gz=function(_2gA,_2gB,_2gC){var _2gD=E(_2gB);if(!_2gD._){return __Z;}else{var _2gE=E(_2gC);return (_2gE._==0)?__Z:new T2(1,new T(function(){return B(A2(_2gA,_2gD.a,_2gE.a));}),new T(function(){return B(_2gz(_2gA,_2gD.b,_2gE.b));}));}},_2gF=function(_2gG,_2gH,_2gI,_2gJ,_2gK,_2gL){var _2gM=E(_1OQ);if(!B(_12S(_2gH,_2gI,_2gJ,_2gM.a,_2gM.b,_2gM.c))){var _2gN=new T(function(){var _2gO=E(_2gK),_2gP=B(_2gs(_4,_2gO.b)),_2gQ=new T(function(){return B(_G(function(_2gR){return new F(function(){return _2fL(_2gH,_2gI,_2gJ,_2gO,_2gR);});},_2gP));},1);return B(_2gz(_2gm,_2gP,_2gQ));});return new T3(0,new T(function(){var _2gS=B(_2gb(_2gG,_2gK));return new T3(0,_2gS.a,_2gS.b,_2gS.c);}),_2gN,new T4(0,_2gG,new T3(0,_2gH,_2gI,_2gJ),_2gK,_2gL));}else{return new T3(0,_2gM,_4,_2gr);}},_2gT=function(_2gU){var _2gV=E(_2gU),_2gW=E(_2gV.b),_2gX=B(_2gF(_2gV.a,_2gW.a,_2gW.b,_2gW.c,_2gV.c,_2gV.d));return new T3(0,_2gX.a,_2gX.b,_2gX.c);},_2gY=0,_2gZ=function(_2h0){var _2h1=E(_2h0);return new F(function(){return _1CY(_2h1.a,_2h1.b,_2h1.c);});},_2h2=new T(function(){return B(err(_rq));}),_2h3=new T(function(){return B(err(_rs));}),_2h4=new T(function(){return B(unCStr("_"));}),_2h5=92,_2h6=39,_2h7=function(_2h8){var _2h9=E(_2h8);if(!_2h9._){return __Z;}else{var _2ha=_2h9.b,_2hb=E(_2h9.a);switch(E(_2hb)){case 39:return __Z;case 92:var _2hc=E(_2ha);if(!_2hc._){return __Z;}else{var _2hd=_2hc.b;switch(E(_2hc.a)){case 39:return new T2(1,new T2(0,_2h6,_2hd),_4);case 92:return new T2(1,new T2(0,_2h5,_2hd),_4);default:return __Z;}}break;default:return new T2(1,new T2(0,_2hb,_2ha),_4);}}},_2he=function(_2hf,_2hg){var _2hh=function(_2hi){var _2hj=E(_2hi);if(!_2hj._){return __Z;}else{var _2hk=E(_2hj.a);return new F(function(){return _0(B(_rx(B(A1(_2hg,_2hk.a)),_2hk.b)),new T(function(){return B(_2hh(_2hj.b));},1));});}};return function(_2hl){var _2hm=B(_2hh(B(A1(_2hf,_2hl))));return (_2hm._==0)?new T0(2):new T1(4,_2hm);};},_2hn=function(_2ho){return new T1(1,B(_2he(_2h7,_2ho)));},_2hp=function(_2hq,_2hr){var _2hs=new T(function(){var _2ht=function(_2hu){return new F(function(){return _2hp(_2hq,function(_2hv){return new F(function(){return A1(_2hr,new T2(1,_2hu,_2hv));});});});};return B(A1(_2hq,_2ht));});return new F(function(){return _rH(B(A1(_2hr,_4)),_2hs);});},_2hw=function(_2hx){var _2hy=function(_2hz){var _2hA=E(_2hz);if(!_2hA._){return __Z;}else{var _2hB=E(_2hA.a),_2hC=function(_2hD){var _2hE=new T(function(){return B(A1(_2hx,new T2(1,_2hB.a,_2hD)));});return new T1(0,function(_2hF){return (E(_2hF)==39)?E(_2hE):new T0(2);});};return new F(function(){return _0(B(_rx(B(_2hp(_2hn,_2hC)),_2hB.b)),new T(function(){return B(_2hy(_2hA.b));},1));});}},_2hG=function(_2hH){var _2hI=B(_2hy(B(_2h7(_2hH))));return (_2hI._==0)?new T0(2):new T1(4,_2hI);};return function(_2hJ){return (E(_2hJ)==39)?E(new T1(1,_2hG)):new T0(2);};},_2hK=function(_2hL){var _2hM=B(_1y0(B(_G(_1ze,B(_1zg(_2hL))))));return new T3(0,_2hM.a,_2hM.b,_2hM.c);},_2hN=function(_2hO){return new F(function(){return _1CD(E(_2hO));});},_2hP=function(_2hQ){var _2hR=function(_2hS){if(!B(_sl(_2hS,_2h4))){return new F(function(){return A1(_2hQ,new T(function(){return B(_2hK(_2hS));}));});}else{return new T0(2);}},_2hT=function(_2hU){var _2hV=E(_2hU);return (!B(_1Ce(_2hV)))?new T0(2):new T1(1,B(_tq(_2hN,function(_2hW){return new F(function(){return _2hR(new T2(1,_2hV,_2hW));});})));};return new F(function(){return _rH(new T1(0,_2hT),new T(function(){return new T1(0,B(_2hw(_2hR)));}));});},_2hX=new T(function(){return B(_2hP(_sS));}),_2hY=function(_2hZ,_2i0){while(1){var _2i1=E(_2hZ);if(!_2i1._){return E(_2i0);}else{_2hZ=_2i1.b;_2i0=_2i1.a;continue;}}},_2i2=function(_2i3,_2i4){var _2i5=new T(function(){var _2i6=B(_2i7(B(_20q(_2i3))));return new T2(0,_2i6.a,_2i6.b);});return new T2(0,new T2(1,new T(function(){return B(_1NC(_2i3));}),new T(function(){return B(_1NC(_2i5));})),new T(function(){return B(_20q(_2i5));}));},_2i7=function(_2i8){var _2i9=E(_2i8);if(!_2i9._){return new T2(0,_4,_4);}else{if(E(_2i9.a)==32){var _2ia=B(_2ib(_2i9.b));if(!_2ia._){return new T2(0,_4,_2i9);}else{return new F(function(){return _2i2(_2ia.a,_2ia.b);});}}else{var _2ic=B(_2ib(_2i9));if(!_2ic._){return new T2(0,_4,_2i9);}else{return new F(function(){return _2i2(_2ic.a,_2ic.b);});}}}},_2id=new T(function(){return B(unCStr("?"));}),_2ie=new T(function(){return B(_1zg(_2id));}),_2if=new T(function(){return B(_G(_1ze,_2ie));}),_2ig=new T(function(){var _2ih=B(_1y0(_2if));return new T3(0,_2ih.a,_2ih.b,_2ih.c);}),_2ii=new T2(0,_2ig,_4),_2ij=new T1(1,_2ii),_2ik=new T(function(){return B(_rx(_2hX,_4));}),_2il=function(_2im){var _2in=E(_2im);if(!_2in._){var _2io=E(_2ik);return (_2io._==0)?__Z:new T1(1,_2io.a);}else{if(E(_2in.a)==63){var _2ip=B(_2il(_2in.b));if(!_2ip._){return E(_2ij);}else{var _2iq=E(_2ip.a),_2ir=new T(function(){var _2is=B(_1y0(B(_G(_1ze,B(_1zg(B(unAppCStr("?",new T(function(){var _2it=E(_2iq.a);return B(_1CY(_2it.a,_2it.b,_2it.c));})))))))));return new T3(0,_2is.a,_2is.b,_2is.c);});return new T1(1,new T2(0,_2ir,_2iq.b));}}else{var _2iu=B(_rx(_2hX,_2in));return (_2iu._==0)?__Z:new T1(1,_2iu.a);}}},_2iv=function(_2iw){while(1){var _2ix=B((function(_2iy){var _2iz=E(_2iy);if(!_2iz._){return new T2(0,_4,_4);}else{var _2iA=_2iz.b,_2iB=function(_2iC){var _2iD=B(_2il(_2iz));if(!_2iD._){return new T2(0,_4,_2iz);}else{var _2iE=_2iD.a,_2iF=new T(function(){var _2iG=B(_2iv(B(_20q(_2iE))));return new T2(0,_2iG.a,_2iG.b);});return new T2(0,new T2(1,new T(function(){return B(_1NC(_2iE));}),new T(function(){return B(_1NC(_2iF));})),new T(function(){return B(_20q(_2iF));}));}};switch(E(_2iz.a)){case 32:_2iw=_2iA;return __continue;case 40:_2iw=_2iA;return __continue;case 41:return new T2(0,_4,_2iA);case 45:var _2iH=E(_2iA);if(!_2iH._){return new F(function(){return _2iB(_);});}else{if(E(_2iH.a)==62){_2iw=_2iH.b;return __continue;}else{return new F(function(){return _2iB(_);});}}break;default:return new F(function(){return _2iB(_);});}}})(_2iw));if(_2ix!=__continue){return _2ix;}}},_2iI=new T(function(){return B(unCStr("?"));}),_2iJ=function(_2iK){var _2iL=E(_2iK);if(!_2iL._){var _2iM=E(_2iL.b);if(!_2iM._){return E(_2iM.a);}else{return new F(function(){return _2hK(_2iI);});}}else{return E(_2iL.a);}},_2iN=new T(function(){return B(_1zg(_2iI));}),_2iO=new T(function(){return B(_G(_1ze,_2iN));}),_2iP=new T(function(){var _2iQ=B(_1y0(_2iO));return new T3(0,_2iQ.a,_2iQ.b,_2iQ.c);}),_2iR=new T2(0,_2iP,_4),_2iS=function(_2iT){var _2iU=E(_2iT);if(!_2iU._){var _2iV=_2iU.c,_2iW=new T(function(){var _2iX=E(_2iU.b);if(!_2iX._){if(!E(_2iX.b)._){return new T2(0,_2iX.a,new T(function(){return B(_G(_2iJ,_2iV));}));}else{return E(_2iX);}}else{return E(_2iR);}});return new T3(0,_2iU.a,_2iW,new T(function(){return B(_G(_2iS,_2iV));}));}else{return E(_2iU);}},_2iY=function(_2iZ,_2j0){var _2j1=E(_2j0);return (_2j1._==0)?__Z:new T2(1,_2iZ,new T(function(){return B(_2iY(_2j1.a,_2j1.b));}));},_2j2=new T(function(){return B(unCStr("last"));}),_2j3=new T(function(){return B(_ei(_2j2));}),_2j4=function(_2j5){var _2j6=E(_2j5);return new T2(0,new T1(1,_2j6.a),new T(function(){var _2j7=E(_2j6.b);if(!_2j7._){return __Z;}else{if(E(_2j7.a)==125){return E(_2j7.b);}else{return E(_2j7);}}}));},_2ib=function(_2j8){var _2j9=E(_2j8);if(!_2j9._){var _2ja=__Z;}else{if(E(_2j9.a)==123){var _2jb=E(_2j9.b);}else{var _2jb=E(_2j9);}var _2ja=_2jb;}var _2jc=function(_2jd){var _2je=B(_2il(_2ja));if(!_2je._){return __Z;}else{var _2jf=E(_2je.a),_2jg=function(_2jh){var _2ji=new T(function(){var _2jj=E(E(_2jh).b);if(!_2jj._){var _2jk=B(_2i7(_4));return new T2(0,_2jk.a,_2jk.b);}else{var _2jl=_2jj.b;switch(E(_2jj.a)){case 32:var _2jm=E(_2jl);if(!_2jm._){var _2jn=B(_2i7(_4));return new T2(0,_2jn.a,_2jn.b);}else{if(E(_2jm.a)==123){var _2jo=B(_2i7(_2jm.b));return new T2(0,_2jo.a,_2jo.b);}else{var _2jp=B(_2i7(_2jm));return new T2(0,_2jp.a,_2jp.b);}}break;case 123:var _2jq=B(_2i7(_2jl));return new T2(0,_2jq.a,_2jq.b);break;default:var _2jr=B(_2i7(_2jj));return new T2(0,_2jr.a,_2jr.b);}}}),_2js=new T(function(){return B(_2iS(new T3(0,_2jf.a,new T(function(){return B(_1NC(_2jh));}),new T(function(){return B(_1NC(_2ji));}))));});return new T2(1,new T2(0,_2js,new T(function(){var _2jt=E(E(_2ji).b);if(!_2jt._){return __Z;}else{if(E(_2jt.a)==125){return E(_2jt.b);}else{return E(_2jt);}}})),_4);},_2ju=E(_2jf.b);if(!_2ju._){var _2jv=B(_2iv(_4)),_2jw=E(_2jv.a);if(!_2jw._){return __Z;}else{return new F(function(){return _2jg(new T2(0,new T2(0,new T(function(){return B(_2hY(_2jw,_2j3));}),new T(function(){return B(_2iY(_2jw.a,_2jw.b));})),_2jv.b));});}}else{if(E(_2ju.a)==58){var _2jx=B(_2iv(_2ju.b)),_2jy=E(_2jx.a);if(!_2jy._){return __Z;}else{return new F(function(){return _2jg(new T2(0,new T2(0,new T(function(){return B(_2hY(_2jy,_2j3));}),new T(function(){return B(_2iY(_2jy.a,_2jy.b));})),_2jx.b));});}}else{var _2jz=B(_2iv(_2ju)),_2jA=E(_2jz.a);if(!_2jA._){return __Z;}else{return new F(function(){return _2jg(new T2(0,new T2(0,new T(function(){return B(_2hY(_2jA,_2j3));}),new T(function(){return B(_2iY(_2jA.a,_2jA.b));})),_2jz.b));});}}}}},_2jB=E(_2ja);if(!_2jB._){return new F(function(){return _2jc(_);});}else{if(E(_2jB.a)==63){return new F(function(){return _G(_2j4,B(_rx(_2hX,_2jB.b)));});}else{return new F(function(){return _2jc(_);});}}},_2jC=function(_2jD){var _2jE=E(_2jD);if(!_2jE._){return __Z;}else{var _2jF=E(_2jE.a),_2jG=function(_2jH){return E(new T2(3,_2jF.a,_sR));};return new F(function(){return _0(B(_rx(new T1(1,function(_2jI){return new F(function(){return A2(_BE,_2jI,_2jG);});}),_2jF.b)),new T(function(){return B(_2jC(_2jE.b));},1));});}},_2jJ=function(_2jK){var _2jL=B(_2jC(B(_2ib(_2jK))));return (_2jL._==0)?new T0(2):new T1(4,_2jL);},_2jM=new T1(1,_2jJ),_2jN=new T(function(){return B(unCStr("{Pred:(Item->Quality->Comment) {This:(Kind->Item) {Pizza:Kind}} {Very:(Quality->Quality) {Italian:Quality}}}"));}),_2jO=new T(function(){return B(_rx(_2jM,_2jN));}),_2jP=new T(function(){var _2jQ=B(_Iz(_2jO));if(!_2jQ._){return E(_2h2);}else{if(!E(_2jQ.b)._){return E(_2jQ.a);}else{return E(_2h3);}}}),_2jR=new T2(0,_2jP,_MR),_2jS=function(_2jT){var _2jU=E(_2jT);if(!_2jU._){return E(_2fp);}else{var _2jV=function(_){var _2jW=E(_2aJ),_2jX=__app1(_2jW,toJSStr(E(_2fA)));return new T(function(){var _2jY=function(_2jZ){var _2k0=function(_){var _2k1=__app1(_2jW,toJSStr(E(_2fy))),_2k2=new T(function(){var _2k3=E(_2jZ),_2k4=B(_2eN(_bP,_2k3.a,_2k3.b,_2k3.c)),_2k5=E(_2k4.a);return E(B(_1BP(_2k5,(E(_2k4.b)-_2k5|0)+1|0,_2k4,_2gY)).a);}),_2k6=function(_){var _2k7=__app1(_2jW,toJSStr(B(unAppCStr("Loaded ",new T(function(){return B(_2gZ(E(_2k2).b));}))))),_2k8=function(_){var _2k9=nMV(new T5(0,new T(function(){return B(_2gT(_2k2));}),new T(function(){return B(_2fi(_LA,E(_2k2).d));}),_2jR,_4l,_2fn)),_2ka=_2k9,_2kb=function(_2kc,_){var _2kd=__app1(_2jW,toJSStr(E(_2fx))),_2ke=B(_1FQ(_1Em,_)),_2kf=B(_1FQ(_2eV,_)),_2kg=rMV(_2ka),_=wMV(_2ka,new T5(0,new T(function(){return E(E(_2kg).a);}),new T(function(){return E(E(_2kg).b);}),new T(function(){return E(E(_2kg).c);}),_4l,new T(function(){return E(E(_2kg).e);})));return _5;},_2kh=B(A(_1EJ,[_do,_df,_de,_1FJ,_1Cb,_2kb,_])),_2ki=E(_1Fs),_2kj=__app1(_2ki,toJSStr(E(_2fw))),_2kk=E(_D),_2kl=__eq(_2kj,_2kk),_2km=function(_,_2kn){var _2ko=E(_2kn);if(!_2ko._){return new F(function(){return die(_2fu);});}else{var _2kp=_2ko.a,_2kq=function(_,_2kr){var _2ks=E(_2kr);if(!_2ks._){return new F(function(){return _bC(_2fq,_);});}else{var _2kt=__app2(E(_1Eo),E(_2ks.a),toJSStr(E(_2bO)));return new F(function(){return _2bE(_2ka,_);});}},_2ku=function(_2kv,_){var _2kw=__app1(_2ki,toJSStr(E(_2dG))),_2kx=__eq(_2kw,_2kk);if(!E(_2kx)){var _2ky=__isUndef(_2kw);if(!E(_2ky)){return new F(function(){return _2kq(_,new T1(1,_2kw));});}else{return new F(function(){return _2kq(_,_4l);});}}else{return new F(function(){return _2kq(_,_4l);});}},_2kz=function(_2kA,_){var _2kB=B(_29n(_)),_2kC=__app1(_2jW,toJSStr(E(_2fv))),_2kD=B(A(_1Gb,[_dm,_dn,_2kp,_28C,_])),_2kE=B(A(_1Gb,[_dm,_dn,_2kp,_29l,_])),_2kF=B(_1FQ(_2eV,_)),_2kG=B(A(_2aB,[_dm,_dn,_1Fq,new T2(1,_2fB,new T2(1,_29k,new T2(1,new T(function(){return new T2(0,E(_29j),toJSStr(B(_0(_2kE,_29g))));}),new T2(1,new T(function(){var _2kH=B(_Iz(B(_rx(_29e,_2kD))));if(!_2kH._){return E(_28F);}else{if(!E(_2kH.b)._){return new T2(0,E(_29i),toJSStr(B(_0(B(_bZ(0,E(_2kH.a)-200|0,_4)),_29g))));}else{return E(_28G);}}}),_4)))),_])),_2kI=B(_1Fb(_2kG,_2fr,_2ku,_)),_2kJ=rMV(_2ka),_2kK=nMV(new T5(0,new T(function(){return E(E(_2kJ).a);}),new T(function(){return E(E(_2kJ).b);}),_2jR,_4l,_2fn)),_2kL=_2kK,_2kM=B(_1Fb(_2kG,_2fm,function(_2kN,_){var _2kO=B(_2bE(_2kL,_)),_2kP=B(_1Fv(_2kL,_)),_2kQ=rMV(_2kL),_=wMV(_2ka,_2kQ);return _5;},_)),_2kR=__app2(E(_1Ev),E(_2kG),E(_1FJ));return _5;},_2kS=B(A(_1EJ,[_do,_df,_de,_2kp,_1Cb,_2kz,_])),_2kT=B(_2bE(_2ka,_));return _7q;}};if(!E(_2kl)){var _2kU=__isUndef(_2kj);if(!E(_2kU)){return new F(function(){return _2km(_,new T1(1,_2kj));});}else{return new F(function(){return _2km(_,_4l);});}}else{return new F(function(){return _2km(_,_4l);});}};return new T1(0,_2k8);};return new T1(0,_2k6);};return new T1(0,_2k0);};return B(A3(_2f3,_2l,_2jU.a,_2jY));});};return new T1(0,_2jV);}},_2kV=new T(function(){return toJSStr(E(_2fz));}),_2kW=new T(function(){return B(A(_7Y,[_2l,_N,_1b,_i,_h,_2kV,_2jS]));}),_2kX=function(_){var _2kY=B(_c(_2kW,_4,_));return _5;},_2kZ=function(_){return new F(function(){return _2kX(_);});};
var hasteMain = function() {B(A(_2kZ, [0]));};window.onload = hasteMain;