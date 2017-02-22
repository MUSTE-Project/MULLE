"use strict";
var __haste_prog_id = '205bad2db8ff4bd65a292979b2b10c62b82fd839ba5179ee3569fc39360a7589';
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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return B(_0(_3.b,_2));}));},_4=__Z,_5=0,_6=function(_7,_){while(1){var _8=E(_7);if(!_8._){return _5;}else{var _9=_8.b,_a=E(_8.a);switch(_a._){case 0:var _b=B(A1(_a.a,_));_7=B(_0(_9,new T2(1,_b,_4)));continue;case 1:_7=B(_0(_9,_a.a));continue;default:_7=_9;continue;}}}},_c=function(_d,_e,_){var _f=E(_d);switch(_f._){case 0:var _g=B(A1(_f.a,_));return new F(function(){return _6(B(_0(_e,new T2(1,_g,_4))),_);});break;case 1:return new F(function(){return _6(B(_0(_e,_f.a)),_);});break;default:return new F(function(){return _6(_e,_);});}},_h=new T1(0,_),_i=new T(function(){return toJSStr(_4);}),_j=function(_k){return E(_i);},_l=function(_m,_){var _n=E(_m);if(!_n._){return _4;}else{var _o=B(_l(_n.b,_));return new T2(1,_5,_o);}},_p=function(_q,_){var _r=__arr2lst(0,_q);return new F(function(){return _l(_r,_);});},_s=function(_t,_){return new F(function(){return _p(E(_t),_);});},_u=function(_){return _5;},_v=function(_w,_){return new F(function(){return _u(_);});},_x=new T2(0,_v,_s),_y=function(_){return new F(function(){return __jsNull();});},_z=function(_A){var _B=B(A1(_A,_));return E(_B);},_C=new T(function(){return B(_z(_y));}),_D=new T(function(){return E(_C);}),_E=function(_F){return E(_D);},_G=function(_H,_I){var _J=E(_I);return (_J._==0)?__Z:new T2(1,new T(function(){return B(A1(_H,_J.a));}),new T(function(){return B(_G(_H,_J.b));}));},_K=function(_L){return new F(function(){return __lst2arr(B(_G(_E,_L)));});},_M=new T2(0,_E,_K),_N=new T4(0,_M,_x,_j,_j),_O="application/octet-stream",_P=function(_Q){return E(_O);},_R="blob",_S=function(_T){return E(_R);},_U=function(_V,_){var _W=E(_V);if(!_W._){return _4;}else{var _X=B(_U(_W.b,_));return new T2(1,_W.a,_X);}},_Y=function(_Z,_){var _10=__arr2lst(0,_Z);return new F(function(){return _U(_10,_);});},_11=function(_12,_){return new F(function(){return _Y(E(_12),_);});},_13=function(_14,_){return _14;},_15=new T2(0,_13,_11),_16=function(_17){return E(_17);},_18=function(_19){return new F(function(){return __lst2arr(B(_G(_16,_19)));});},_1a=new T2(0,_16,_18),_1b=new T4(0,_1a,_15,_P,_S),_1c=function(_1d,_1e,_1f){var _1g=function(_1h){var _1i=new T(function(){return B(A1(_1f,_1h));});return new F(function(){return A1(_1e,function(_1j){return E(_1i);});});};return new F(function(){return A1(_1d,_1g);});},_1k=function(_1l,_1m,_1n){var _1o=new T(function(){return B(A1(_1m,function(_1p){return new F(function(){return A1(_1n,_1p);});}));});return new F(function(){return A1(_1l,function(_1q){return E(_1o);});});},_1r=function(_1s,_1t,_1u){var _1v=function(_1w){var _1x=function(_1y){return new F(function(){return A1(_1u,new T(function(){return B(A1(_1w,_1y));}));});};return new F(function(){return A1(_1t,_1x);});};return new F(function(){return A1(_1s,_1v);});},_1z=function(_1A,_1B){return new F(function(){return A1(_1B,_1A);});},_1C=function(_1D,_1E,_1F){var _1G=new T(function(){return B(A1(_1F,_1D));});return new F(function(){return A1(_1E,function(_1H){return E(_1G);});});},_1I=function(_1J,_1K,_1L){var _1M=function(_1N){return new F(function(){return A1(_1L,new T(function(){return B(A1(_1J,_1N));}));});};return new F(function(){return A1(_1K,_1M);});},_1O=new T2(0,_1I,_1C),_1P=new T5(0,_1O,_1z,_1r,_1k,_1c),_1Q=function(_1R,_1S,_1T){return new F(function(){return A1(_1R,function(_1U){return new F(function(){return A2(_1S,_1U,_1T);});});});},_1V=function(_1W){return E(E(_1W).b);},_1X=function(_1Y,_1Z){return new F(function(){return A3(_1V,_20,_1Y,function(_21){return E(_1Z);});});},_22=function(_23){return new F(function(){return err(_23);});},_20=new T(function(){return new T5(0,_1P,_1Q,_1X,_1z,_22);}),_24=function(_25,_26,_){var _27=B(A1(_26,_));return new T(function(){return B(A1(_25,_27));});},_28=function(_29,_2a){return new T1(0,function(_){return new F(function(){return _24(_2a,_29,_);});});},_2b=new T2(0,_20,_28),_2c=function(_2d){return new T0(2);},_2e=function(_2f){var _2g=new T(function(){return B(A1(_2f,_2c));}),_2h=function(_2i){return new T1(1,new T2(1,new T(function(){return B(A1(_2i,_5));}),new T2(1,_2g,_4)));};return E(_2h);},_2j=function(_2k){return E(_2k);},_2l=new T3(0,_2b,_2j,_2e),_2m=function(_2n){return E(E(_2n).a);},_2o=function(_2p,_2q,_2r,_2s,_2t){var _2u=B(A2(_2m,_2p,E(_2t)));return new F(function(){return A2(_2q,_2r,new T2(1,_2u,E(_2s)));});},_2v=function(_2w){return E(E(_2w).a);},_2x=function(_2y){return E(E(_2y).a);},_2z=function(_2A){return E(E(_2A).a);},_2B=function(_2C){return E(E(_2C).b);},_2D=new T(function(){return B(unCStr("base"));}),_2E=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_2F=new T(function(){return B(unCStr("IOException"));}),_2G=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_2D,_2E,_2F),_2H=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_2G,_4,_4),_2I=function(_2J){return E(_2H);},_2K=function(_2L){return E(E(_2L).a);},_2M=function(_2N,_2O,_2P){var _2Q=B(A1(_2N,_)),_2R=B(A1(_2O,_)),_2S=hs_eqWord64(_2Q.a,_2R.a);if(!_2S){return __Z;}else{var _2T=hs_eqWord64(_2Q.b,_2R.b);return (!_2T)?__Z:new T1(1,_2P);}},_2U=function(_2V){var _2W=E(_2V);return new F(function(){return _2M(B(_2K(_2W.a)),_2I,_2W.b);});},_2X=new T(function(){return B(unCStr(": "));}),_2Y=new T(function(){return B(unCStr(")"));}),_2Z=new T(function(){return B(unCStr(" ("));}),_30=new T(function(){return B(unCStr("interrupted"));}),_31=new T(function(){return B(unCStr("system error"));}),_32=new T(function(){return B(unCStr("unsatisified constraints"));}),_33=new T(function(){return B(unCStr("user error"));}),_34=new T(function(){return B(unCStr("permission denied"));}),_35=new T(function(){return B(unCStr("illegal operation"));}),_36=new T(function(){return B(unCStr("end of file"));}),_37=new T(function(){return B(unCStr("resource exhausted"));}),_38=new T(function(){return B(unCStr("resource busy"));}),_39=new T(function(){return B(unCStr("does not exist"));}),_3a=new T(function(){return B(unCStr("already exists"));}),_3b=new T(function(){return B(unCStr("resource vanished"));}),_3c=new T(function(){return B(unCStr("timeout"));}),_3d=new T(function(){return B(unCStr("unsupported operation"));}),_3e=new T(function(){return B(unCStr("hardware fault"));}),_3f=new T(function(){return B(unCStr("inappropriate type"));}),_3g=new T(function(){return B(unCStr("invalid argument"));}),_3h=new T(function(){return B(unCStr("failed"));}),_3i=new T(function(){return B(unCStr("protocol error"));}),_3j=function(_3k,_3l){switch(E(_3k)){case 0:return new F(function(){return _0(_3a,_3l);});break;case 1:return new F(function(){return _0(_39,_3l);});break;case 2:return new F(function(){return _0(_38,_3l);});break;case 3:return new F(function(){return _0(_37,_3l);});break;case 4:return new F(function(){return _0(_36,_3l);});break;case 5:return new F(function(){return _0(_35,_3l);});break;case 6:return new F(function(){return _0(_34,_3l);});break;case 7:return new F(function(){return _0(_33,_3l);});break;case 8:return new F(function(){return _0(_32,_3l);});break;case 9:return new F(function(){return _0(_31,_3l);});break;case 10:return new F(function(){return _0(_3i,_3l);});break;case 11:return new F(function(){return _0(_3h,_3l);});break;case 12:return new F(function(){return _0(_3g,_3l);});break;case 13:return new F(function(){return _0(_3f,_3l);});break;case 14:return new F(function(){return _0(_3e,_3l);});break;case 15:return new F(function(){return _0(_3d,_3l);});break;case 16:return new F(function(){return _0(_3c,_3l);});break;case 17:return new F(function(){return _0(_3b,_3l);});break;default:return new F(function(){return _0(_30,_3l);});}},_3m=new T(function(){return B(unCStr("}"));}),_3n=new T(function(){return B(unCStr("{handle: "));}),_3o=function(_3p,_3q,_3r,_3s,_3t,_3u){var _3v=new T(function(){var _3w=new T(function(){var _3x=new T(function(){var _3y=E(_3s);if(!_3y._){return E(_3u);}else{var _3z=new T(function(){return B(_0(_3y,new T(function(){return B(_0(_2Y,_3u));},1)));},1);return B(_0(_2Z,_3z));}},1);return B(_3j(_3q,_3x));}),_3A=E(_3r);if(!_3A._){return E(_3w);}else{return B(_0(_3A,new T(function(){return B(_0(_2X,_3w));},1)));}}),_3B=E(_3t);if(!_3B._){var _3C=E(_3p);if(!_3C._){return E(_3v);}else{var _3D=E(_3C.a);if(!_3D._){var _3E=new T(function(){var _3F=new T(function(){return B(_0(_3m,new T(function(){return B(_0(_2X,_3v));},1)));},1);return B(_0(_3D.a,_3F));},1);return new F(function(){return _0(_3n,_3E);});}else{var _3G=new T(function(){var _3H=new T(function(){return B(_0(_3m,new T(function(){return B(_0(_2X,_3v));},1)));},1);return B(_0(_3D.a,_3H));},1);return new F(function(){return _0(_3n,_3G);});}}}else{return new F(function(){return _0(_3B.a,new T(function(){return B(_0(_2X,_3v));},1));});}},_3I=function(_3J){var _3K=E(_3J);return new F(function(){return _3o(_3K.a,_3K.b,_3K.c,_3K.d,_3K.f,_4);});},_3L=function(_3M,_3N,_3O){var _3P=E(_3N);return new F(function(){return _3o(_3P.a,_3P.b,_3P.c,_3P.d,_3P.f,_3O);});},_3Q=function(_3R,_3S){var _3T=E(_3R);return new F(function(){return _3o(_3T.a,_3T.b,_3T.c,_3T.d,_3T.f,_3S);});},_3U=44,_3V=93,_3W=91,_3X=function(_3Y,_3Z,_40){var _41=E(_3Z);if(!_41._){return new F(function(){return unAppCStr("[]",_40);});}else{var _42=new T(function(){var _43=new T(function(){var _44=function(_45){var _46=E(_45);if(!_46._){return E(new T2(1,_3V,_40));}else{var _47=new T(function(){return B(A2(_3Y,_46.a,new T(function(){return B(_44(_46.b));})));});return new T2(1,_3U,_47);}};return B(_44(_41.b));});return B(A2(_3Y,_41.a,_43));});return new T2(1,_3W,_42);}},_48=function(_49,_4a){return new F(function(){return _3X(_3Q,_49,_4a);});},_4b=new T3(0,_3L,_3I,_48),_4c=new T(function(){return new T5(0,_2I,_4b,_4d,_2U,_3I);}),_4d=function(_4e){return new T2(0,_4c,_4e);},_4f="status-text",_4g="status",_4h="http",_4i="network",_4j="type",_4k=__Z,_4l=__Z,_4m=7,_4n=function(_4o,_){var _4p=__get(_4o,E(_4j)),_4q=String(_4p),_4r=strEq(_4q,E(_4i));if(!E(_4r)){var _4s=strEq(_4q,E(_4h));if(!E(_4s)){var _4t=new T(function(){var _4u=new T(function(){return B(unAppCStr("unknown type of ajax error: ",new T(function(){return fromJSStr(_4q);})));});return B(_4d(new T6(0,_4l,_4m,_4,_4u,_4l,_4l)));});return new F(function(){return die(_4t);});}else{var _4v=__get(_4o,E(_4g)),_4w=__get(_4o,E(_4f));return new T2(1,new T(function(){var _4x=Number(_4v);return jsTrunc(_4x);}),new T(function(){return String(_4w);}));}}else{return _4k;}},_4y=function(_4z,_){var _4A=E(_4z);if(!_4A._){return _4;}else{var _4B=B(_4n(E(_4A.a),_)),_4C=B(_4y(_4A.b,_));return new T2(1,_4B,_4C);}},_4D=function(_4E,_){var _4F=__arr2lst(0,_4E);return new F(function(){return _4y(_4F,_);});},_4G=function(_4H,_){return new F(function(){return _4D(E(_4H),_);});},_4I=function(_4J,_){return new F(function(){return _4n(E(_4J),_);});},_4K=new T2(0,_4I,_4G),_4L=function(_4M){return E(E(_4M).a);},_4N=function(_4O,_4P,_){var _4Q=__eq(_4P,E(_D));if(!E(_4Q)){var _4R=__isUndef(_4P);if(!E(_4R)){var _4S=B(A3(_4L,_4O,_4P,_));return new T1(1,_4S);}else{return _4l;}}else{return _4l;}},_4T=function(_4U,_){return new F(function(){return _4N(_4K,E(_4U),_);});},_4V=function(_4W,_4X,_){var _4Y=__arr2lst(0,_4X),_4Z=function(_50,_){var _51=E(_50);if(!_51._){return _4;}else{var _52=_51.b,_53=E(_51.a),_54=__eq(_53,E(_D));if(!E(_54)){var _55=__isUndef(_53);if(!E(_55)){var _56=B(A3(_4L,_4W,_53,_)),_57=B(_4Z(_52,_));return new T2(1,new T1(1,_56),_57);}else{var _58=B(_4Z(_52,_));return new T2(1,_4l,_58);}}else{var _59=B(_4Z(_52,_));return new T2(1,_4l,_59);}}};return new F(function(){return _4Z(_4Y,_);});},_5a=function(_5b,_){return new F(function(){return _4V(_4K,E(_5b),_);});},_5c=new T2(0,_4T,_5a),_5d=2,_5e=function(_5f){return E(_5d);},_5g=function(_5h,_5i,_){var _5j=B(A2(_5h,new T(function(){var _5k=E(_5i),_5l=__eq(_5k,E(_D));if(!E(_5l)){var _5m=__isUndef(_5k);if(!E(_5m)){return new T1(1,_5k);}else{return __Z;}}else{return __Z;}}),_));return _D;},_5n=new T2(0,_5g,_5e),_5o=function(_5p){return E(E(_5p).a);},_5q=function(_5r,_5s,_5t,_5u){var _5v=new T(function(){return B(A1(_5t,new T(function(){var _5w=B(A3(_4L,_5r,_5u,_));return E(_5w);})));});return new F(function(){return A2(_5o,_5s,_5v);});},_5x=function(_5y){return E(E(_5y).b);},_5z=new T(function(){return B(unCStr("Prelude.undefined"));}),_5A=new T(function(){return B(err(_5z));}),_5B=function(_5C,_5D,_5E){var _5F=__createJSFunc(1+B(A2(_5x,_5D,new T(function(){return B(A1(_5E,_5A));})))|0,function(_5G){return new F(function(){return _5q(_5C,_5D,_5E,_5G);});});return E(_5F);},_5H=function(_5I){return new F(function(){return _5B(_5c,_5n,_5I);});},_5J=function(_5K,_5L,_5M){return new F(function(){return _5B(_5K,_5L,_5M);});},_5N=function(_5O,_5P,_5Q){var _5R=__lst2arr(B(_G(function(_5S){return new F(function(){return _5J(_5O,_5P,_5S);});},_5Q)));return E(_5R);},_5T=function(_5U){return new F(function(){return _5N(_5c,_5n,_5U);});},_5V=new T2(0,_5H,_5T),_5W=function(_5X,_5Y,_5Z,_){var _60=__apply(_5Y,E(_5Z));return new F(function(){return A3(_4L,_5X,_60,_);});},_61=function(_62,_63,_64,_){return new F(function(){return _5W(_62,E(_63),_64,_);});},_65=function(_66,_67,_68,_){return new F(function(){return _61(_66,_67,_68,_);});},_69=function(_6a,_6b,_){return new F(function(){return _65(_x,_6a,_6b,_);});},_6c=function(_6d){return E(E(_6d).c);},_6e=0,_6f=new T(function(){return eval("(function(method, uri, mimeout, responseType, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, uri);xhr.responseType = responseType;if(mimeout != \'\') {xhr.setRequestHeader(\'Content-type\', mimeout);}xhr.addEventListener(\'load\', function() {if(xhr.status < 400) {cb(null, xhr.response);}else {cb({\'type\':\'http\', \'status\':xhr.status, \'status-text\': xhr.statusText}, null);}});xhr.addEventListener(\'error\', function() {if(xhr.status != 0) {cb({\'type\':\'http\', \'status\':xhr.status, \'status-text\': xhr.statusText}, null);} else {cb({\'type\':\'network\'}, null);}});xhr.send(postdata);})");}),_6g=function(_6h){return E(E(_6h).b);},_6i=function(_6j){return E(E(_6j).b);},_6k=new T(function(){return B(unCStr("base"));}),_6l=new T(function(){return B(unCStr("Control.Exception.Base"));}),_6m=new T(function(){return B(unCStr("PatternMatchFail"));}),_6n=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6k,_6l,_6m),_6o=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6n,_4,_4),_6p=function(_6q){return E(_6o);},_6r=function(_6s){var _6t=E(_6s);return new F(function(){return _2M(B(_2K(_6t.a)),_6p,_6t.b);});},_6u=function(_6v){return E(E(_6v).a);},_6w=function(_6x){return new T2(0,_6y,_6x);},_6z=function(_6A,_6B){return new F(function(){return _0(E(_6A).a,_6B);});},_6C=function(_6D,_6E){return new F(function(){return _3X(_6z,_6D,_6E);});},_6F=function(_6G,_6H,_6I){return new F(function(){return _0(E(_6H).a,_6I);});},_6J=new T3(0,_6F,_6u,_6C),_6y=new T(function(){return new T5(0,_6p,_6J,_6w,_6r,_6u);}),_6K=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_6L=function(_6M){return E(E(_6M).c);},_6N=function(_6O,_6P){return new F(function(){return die(new T(function(){return B(A2(_6L,_6P,_6O));}));});},_6Q=function(_6R,_6S){return new F(function(){return _6N(_6R,_6S);});},_6T=function(_6U,_6V){var _6W=E(_6V);if(!_6W._){return new T2(0,_4,_4);}else{var _6X=_6W.a;if(!B(A1(_6U,_6X))){return new T2(0,_4,_6W);}else{var _6Y=new T(function(){var _6Z=B(_6T(_6U,_6W.b));return new T2(0,_6Z.a,_6Z.b);});return new T2(0,new T2(1,_6X,new T(function(){return E(E(_6Y).a);})),new T(function(){return E(E(_6Y).b);}));}}},_70=32,_71=new T(function(){return B(unCStr("\n"));}),_72=function(_73){return (E(_73)==124)?false:true;},_74=function(_75,_76){var _77=B(_6T(_72,B(unCStr(_75)))),_78=_77.a,_79=function(_7a,_7b){var _7c=new T(function(){var _7d=new T(function(){return B(_0(_76,new T(function(){return B(_0(_7b,_71));},1)));});return B(unAppCStr(": ",_7d));},1);return new F(function(){return _0(_7a,_7c);});},_7e=E(_77.b);if(!_7e._){return new F(function(){return _79(_78,_4);});}else{if(E(_7e.a)==124){return new F(function(){return _79(_78,new T2(1,_70,_7e.b));});}else{return new F(function(){return _79(_78,_4);});}}},_7f=function(_7g){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_7g,_6K));})),_6y);});},_7h=new T(function(){return B(_7f("src/Haste/Ajax.hs:(61,7)-(63,60)|case"));}),_7i="PUT",_7j="POST",_7k="DELETE",_7l="GET",_7m=function(_7n){return E(E(_7n).c);},_7o=new T1(1,_4),_7p=function(_){return new F(function(){return nMV(_7o);});},_7q=new T0(2),_7r=function(_7s,_7t,_7u){var _7v=function(_7w){var _7x=function(_){var _7y=E(_7t),_7z=rMV(_7y),_7A=E(_7z);if(!_7A._){var _7B=new T(function(){var _7C=new T(function(){return B(A1(_7w,_5));});return B(_0(_7A.b,new T2(1,new T2(0,_7u,function(_7D){return E(_7C);}),_4)));}),_=wMV(_7y,new T2(0,_7A.a,_7B));return _7q;}else{var _7E=E(_7A.a);if(!_7E._){var _=wMV(_7y,new T2(0,_7u,_4));return new T(function(){return B(A1(_7w,_5));});}else{var _=wMV(_7y,new T1(1,_7E.b));return new T1(1,new T2(1,new T(function(){return B(A1(_7w,_5));}),new T2(1,new T(function(){return B(A2(_7E.a,_7u,_2c));}),_4)));}}};return new T1(0,_7x);};return new F(function(){return A2(_6g,_7s,_7v);});},_7F=function(_7G){return E(E(_7G).d);},_7H=function(_7I,_7J){var _7K=function(_7L){var _7M=function(_){var _7N=E(_7J),_7O=rMV(_7N),_7P=E(_7O);if(!_7P._){var _7Q=_7P.a,_7R=E(_7P.b);if(!_7R._){var _=wMV(_7N,_7o);return new T(function(){return B(A1(_7L,_7Q));});}else{var _7S=E(_7R.a),_=wMV(_7N,new T2(0,_7S.a,_7R.b));return new T1(1,new T2(1,new T(function(){return B(A1(_7L,_7Q));}),new T2(1,new T(function(){return B(A1(_7S.b,_2c));}),_4)));}}else{var _7T=new T(function(){var _7U=function(_7V){var _7W=new T(function(){return B(A1(_7L,_7V));});return function(_7X){return E(_7W);};};return B(_0(_7P.a,new T2(1,_7U,_4)));}),_=wMV(_7N,new T1(1,_7T));return _7q;}};return new T1(0,_7M);};return new F(function(){return A2(_6g,_7I,_7K);});},_7Y=function(_7Z,_80,_81,_82,_83,_84){var _85=B(_2x(_7Z)),_86=new T(function(){return B(_6g(_7Z));}),_87=new T(function(){return B(_6i(_85));}),_88=B(_2z(_85)),_89=new T(function(){return B(_2B(_81));}),_8a=new T(function(){var _8b=function(_8c){var _8d=E(_84),_8e=E(_82),_8f=strEq(E(_i),_8e);if(!E(_8f)){var _8g=E(_8e);}else{var _8g=B(A2(_7m,_80,_6e));}var _8h=B(A2(_7F,_81,_6e)),_8i=E(_D);return function(_5G){return new F(function(){return _2o(_5V,_69,_6f,new T2(1,_8i,new T2(1,_8h,new T2(1,_8g,new T2(1,_8d,new T2(1,_8c,_4))))),_5G);});};},_8j=function(_8k,_8l){var _8m=E(_84),_8n=E(_82),_8o=strEq(E(_i),_8n);if(!E(_8o)){var _8p=E(_8n);}else{var _8p=B(A2(_7m,_80,_6e));}var _8q=B(A2(_7F,_81,_6e)),_8r=E(_8k);return function(_5G){return new F(function(){return _2o(_5V,_69,_6f,new T2(1,_8r,new T2(1,_8q,new T2(1,_8p,new T2(1,_8m,new T2(1,_8l,_4))))),_5G);});};},_8s=E(_83);switch(_8s._){case 0:return B(_8b(E(_7l)));break;case 1:return B(_8b(E(_7k)));break;case 2:return B(_8j(new T(function(){return B(A2(_2m,B(_2v(_80)),_8s.a));}),E(_7j)));break;default:return B(_8j(new T(function(){return B(A2(_2m,B(_2v(_80)),_8s.a));}),E(_7i)));}}),_8t=function(_8u){var _8v=new T(function(){return B(A1(_86,new T(function(){return B(_7H(_2l,_8u));})));}),_8w=new T(function(){var _8x=new T(function(){var _8y=function(_8z,_8A,_){var _8B=E(_8A);if(!_8B._){var _8C=E(_8z);if(!_8C._){return E(_7h);}else{return new F(function(){return _c(new T(function(){return B(A(_7r,[_2l,_8u,new T1(0,_8C.a),_2c]));}),_4,_);});}}else{var _8D=B(A3(_4L,_89,_8B.a,_));return new F(function(){return _c(new T(function(){return B(A(_7r,[_2l,_8u,new T1(1,_8D),_2c]));}),_4,_);});}};return B(A1(_8a,_8y));});return B(A1(_87,_8x));});return new F(function(){return A3(_6c,_88,_8w,_8v);});};return new F(function(){return A3(_1V,_88,new T(function(){return B(A2(_6i,_85,_7p));}),_8t);});},_8E=function(_8F,_){return new T(function(){var _8G=Number(E(_8F));return jsTrunc(_8G);});},_8H=new T(function(){return eval("(function(b){return b.size;})");}),_8I=function(_8J){return new F(function(){return _z(function(_){var _8K=__app1(E(_8H),E(_8J));return new F(function(){return _8E(_8K,0);});});});},_8L=0,_8M=new T1(1,_4),_8N=new T(function(){return eval("(function(b,cb){var r=new FileReader();r.onload=function(){cb(new DataView(r.result));};r.readAsArrayBuffer(b);})");}),_8O=function(_8P,_8Q){var _8R=new T(function(){return B(_8I(_8Q));}),_8S=function(_8T){var _8U=function(_){var _8V=nMV(_8M),_8W=_8V,_8X=function(_){var _8Y=function(_8Z,_){var _90=B(_c(new T(function(){return B(A(_7r,[_2l,_8W,new T3(0,_8L,_8R,_8Z),_2c]));}),_4,_));return _D;},_91=__createJSFunc(2,E(_8Y)),_92=__app2(E(_8N),E(_8Q),_91);return new T(function(){return B(A3(_7H,_2l,_8W,_8T));});};return new T1(0,_8X);};return new T1(0,_8U);};return new F(function(){return A2(_6g,_8P,_8S);});},_93="w8",_94=function(_95){return E(_93);},_96=function(_97,_98){var _99=E(_98);return new T2(0,_99.a,_99.b);},_9a=function(_9b,_9c){return E(_9c).c;},_9d=function(_9e){var _9f=B(A1(_9e,_));return E(_9f);},_9g=function(_9h,_9i,_9j,_9k){var _9l=function(_){var _9m=E(_9j),_9n=_9m.d,_9o=_9n["byteLength"],_9p=newByteArr(_9o),_9q=_9p,_9r=memcpy(_9q,_9n,_9o>>>0),_9s=function(_9t,_){while(1){var _9u=E(_9t);if(!_9u._){return _5;}else{var _9v=E(_9u.a),_9w=E(_9v.a),_9x=_9q["v"]["w8"][_9w],_=_9q["v"]["w8"][_9w]=B(A2(_9i,_9x,_9v.b));_9t=_9u.b;continue;}}},_9y=B(_9s(_9k,_));return new T4(0,E(_9m.a),E(_9m.b),_9m.c,_9q);};return new F(function(){return _9d(_9l);});},_9z=function(_9A){return E(E(_9A).f);},_9B=new T(function(){return B(unCStr("Negative range size"));}),_9C=new T(function(){return B(err(_9B));}),_9D=function(_9E,_9F,_9G,_9H,_9I){var _9J=E(_9H),_9K=function(_){var _9L=B(A2(_9z,_9E,_9J)),_9M=newByteArr(_9L),_9N=_9M;if(_9L>=0){var _9O=_9L-1|0,_9P=function(_){var _9Q=function(_9R,_){while(1){var _9S=E(_9R);if(!_9S._){return _5;}else{var _9T=E(_9S.a),_9U=E(_9T.a),_9V=_9N["v"]["w8"][_9U],_=_9N["v"]["w8"][_9U]=B(A2(_9F,_9V,_9T.b));_9R=_9S.b;continue;}}},_9W=B(_9Q(_9I,_));return new T4(0,E(_9J.a),E(_9J.b),_9L,_9N);};if(0<=_9O){var _9X=function(_9Y,_){while(1){var _=_9N["v"]["w8"][_9Y]=E(_9G);if(_9Y!=_9O){var _9Z=_9Y+1|0;_9Y=_9Z;continue;}else{return _5;}}},_a0=B(_9X(0,_));return new F(function(){return _9P(_);});}else{return new F(function(){return _9P(_);});}}else{return E(_9C);}},_a1=E(_9K);return new F(function(){return _9d(_a1);});},_a2=function(_a3,_a4,_a5){var _a6=E(_a4),_a7=function(_){var _a8=B(A2(_9z,_a3,_a6)),_a9=newByteArr(_a8),_aa=_a9;if(_a8>=0){var _ab=_a8-1|0,_ac=function(_){var _ad=function(_ae,_){while(1){var _af=E(_ae);if(!_af._){return _5;}else{var _ag=E(_af.a),_=_aa["v"]["w8"][E(_ag.a)]=E(_ag.b);_ae=_af.b;continue;}}},_ah=B(_ad(_a5,_));return new T4(0,E(_a6.a),E(_a6.b),_a8,_aa);};if(0<=_ab){var _ai=function(_aj,_){while(1){var _=_aa["v"]["w8"][_aj]=0;if(_aj!=_ab){var _ak=_aj+1|0;_aj=_ak;continue;}else{return _5;}}},_al=B(_ai(0,_));return new F(function(){return _ac(_);});}else{return new F(function(){return _ac(_);});}}else{return E(_9C);}},_am=E(_a7);return new F(function(){return _9d(_am);});},_an=function(_ao,_ap,_aq){return E(_ap).d["v"]["w8"][E(_aq)];},_ar=function(_as,_at,_au){var _av=function(_){var _aw=E(_at),_ax=_aw.d,_ay=_ax["byteLength"],_az=newByteArr(_ay),_aA=_az,_aB=memcpy(_aA,_ax,_ay>>>0),_aC=function(_aD,_){while(1){var _aE=E(_aD);if(!_aE._){return _5;}else{var _aF=E(_aE.a),_=_aA["v"]["w8"][E(_aF.a)]=E(_aF.b);_aD=_aE.b;continue;}}},_aG=B(_aC(_au,_));return new T4(0,E(_aw.a),E(_aw.b),_aw.c,_aA);};return new F(function(){return _9d(_av);});},_aH={_:0,a:_96,b:_9a,c:_a2,d:_an,e:_ar,f:_9g,g:_9D},_aI=function(_aJ,_aK,_){var _aL=E(_aK);return new T2(0,_aL.a,_aL.b);},_aM=function(_aN,_aO,_){return new F(function(){return _aI(_aN,_aO,_);});},_aP=function(_aQ,_aR,_){return E(_aR).c;},_aS=function(_aN,_aO,_){return new F(function(){return _aP(_aN,_aO,_);});},_aT=new T(function(){return B(unCStr("Negative range size"));}),_aU=new T(function(){return B(err(_aT));}),_aV=function(_aW,_aX,_aY,_aZ,_){var _b0=B(A2(_9z,_aW,new T2(0,_aX,_aY))),_b1=newByteArr(_b0);if(_b0>=0){var _b2=_b0-1|0,_b3=new T(function(){return new T4(0,E(_aX),E(_aY),_b0,_b1);});if(0<=_b2){var _b4=function(_b5,_){while(1){var _=E(_b3).d["v"]["w8"][_b5]=E(_aZ);if(_b5!=_b2){var _b6=_b5+1|0;_b5=_b6;continue;}else{return _5;}}},_b7=B(_b4(0,_));return _b3;}else{return _b3;}}else{return E(_aU);}},_b8=function(_b9,_ba,_bb,_){var _bc=E(_ba);return new F(function(){return _aV(_b9,_bc.a,_bc.b,_bb,_);});},_bd=function(_be,_aN,_aO,_){return new F(function(){return _b8(_be,_aN,_aO,_);});},_bf=function(_bg,_bh,_bi,_){var _bj=B(A2(_9z,_bg,new T2(0,_bh,_bi))),_bk=newByteArr(_bj);return new T(function(){return new T4(0,E(_bh),E(_bi),_bj,_bk);});},_bl=function(_bm,_bn,_){var _bo=E(_bn);return new F(function(){return _bf(_bm,_bo.a,_bo.b,_);});},_bp=function(_aN,_aO,_){return new F(function(){return _bl(_aN,_aO,_);});},_bq=function(_br,_bs,_bt,_){return E(_bs).d["v"]["w8"][E(_bt)];},_bu=function(_be,_aN,_aO,_){return new F(function(){return _bq(_be,_aN,_aO,_);});},_bv=function(_bw,_bx,_by,_bz,_){var _=E(_bx).d["v"]["w8"][E(_by)]=E(_bz);return _5;},_bA=function(_bB,_be,_aN,_aO,_){return new F(function(){return _bv(_bB,_be,_aN,_aO,_);});},_bC=function(_bD,_bE,_){var _bF=B(A1(_bD,_)),_bG=B(A1(_bE,_));return _bF;},_bH=function(_bI,_bJ,_){var _bK=B(A1(_bI,_)),_bL=B(A1(_bJ,_));return new T(function(){return B(A1(_bK,_bL));});},_bM=function(_bN,_bO,_){var _bP=B(A1(_bO,_));return _bN;},_bQ=new T2(0,_24,_bM),_bR=function(_bS,_){return _bS;},_bT=function(_bU,_bV,_){var _bW=B(A1(_bU,_));return new F(function(){return A1(_bV,_);});},_bX=new T5(0,_bQ,_bR,_bH,_bT,_bC),_bY=new T(function(){return E(_4c);}),_bZ=function(_c0){return new T6(0,_4l,_4m,_4,_c0,_4l,_4l);},_c1=function(_c2,_){var _c3=new T(function(){return B(A2(_6L,_bY,new T(function(){return B(A1(_bZ,_c2));})));});return new F(function(){return die(_c3);});},_c4=function(_c5,_){return new F(function(){return _c1(_c5,_);});},_c6=function(_c7){return new F(function(){return A1(_c4,_c7);});},_c8=function(_c9,_ca,_){var _cb=B(A1(_c9,_));return new F(function(){return A2(_ca,_cb,_);});},_cc=new T5(0,_bX,_c8,_bT,_bR,_c6),_cd={_:0,a:_cc,b:_aM,c:_aS,d:_bd,e:_bp,f:_bp,g:_bu,h:_bA},_ce=new T3(0,_aH,_cd,_94),_cf="deltaZ",_cg="deltaY",_ch="deltaX",_ci=function(_cj,_ck){var _cl=jsShowI(_cj);return new F(function(){return _0(fromJSStr(_cl),_ck);});},_cm=41,_cn=40,_co=function(_cp,_cq,_cr){if(_cq>=0){return new F(function(){return _ci(_cq,_cr);});}else{if(_cp<=6){return new F(function(){return _ci(_cq,_cr);});}else{return new T2(1,_cn,new T(function(){var _cs=jsShowI(_cq);return B(_0(fromJSStr(_cs),new T2(1,_cm,_cr)));}));}}},_ct=new T(function(){return B(unCStr(")"));}),_cu=new T(function(){return B(_co(0,2,_ct));}),_cv=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_cu));}),_cw=function(_cx){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_co(0,_cx,_cv));}))));});},_cy=function(_cz,_){return new T(function(){var _cA=Number(E(_cz)),_cB=jsTrunc(_cA);if(_cB<0){return B(_cw(_cB));}else{if(_cB>2){return B(_cw(_cB));}else{return _cB;}}});},_cC=0,_cD=new T3(0,_cC,_cC,_cC),_cE="button",_cF=new T(function(){return eval("jsGetMouseCoords");}),_cG=function(_cH,_){var _cI=E(_cH);if(!_cI._){return _4;}else{var _cJ=B(_cG(_cI.b,_));return new T2(1,new T(function(){var _cK=Number(E(_cI.a));return jsTrunc(_cK);}),_cJ);}},_cL=function(_cM,_){var _cN=__arr2lst(0,_cM);return new F(function(){return _cG(_cN,_);});},_cO=function(_cP,_){return new F(function(){return _cL(E(_cP),_);});},_cQ=new T2(0,_8E,_cO),_cR=function(_cS,_){var _cT=E(_cS);if(!_cT._){return _4;}else{var _cU=B(_cR(_cT.b,_));return new T2(1,_cT.a,_cU);}},_cV=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9"));}),_cW=new T6(0,_4l,_4m,_4,_cV,_4l,_4l),_cX=new T(function(){return B(_4d(_cW));}),_cY=function(_){return new F(function(){return die(_cX);});},_cZ=function(_d0,_d1,_d2,_){var _d3=__arr2lst(0,_d2),_d4=B(_cR(_d3,_)),_d5=E(_d4);if(!_d5._){return new F(function(){return _cY(_);});}else{var _d6=E(_d5.b);if(!_d6._){return new F(function(){return _cY(_);});}else{if(!E(_d6.b)._){var _d7=B(A3(_4L,_d0,_d5.a,_)),_d8=B(A3(_4L,_d1,_d6.a,_));return new T2(0,_d7,_d8);}else{return new F(function(){return _cY(_);});}}}},_d9=function(_da,_db,_){if(E(_da)==7){var _dc=__app1(E(_cF),_db),_dd=B(_cZ(_cQ,_cQ,_dc,_)),_de=__get(_db,E(_ch)),_df=__get(_db,E(_cg)),_dg=__get(_db,E(_cf));return new T(function(){return new T3(0,E(_dd),E(_4l),E(new T3(0,_de,_df,_dg)));});}else{var _dh=__app1(E(_cF),_db),_di=B(_cZ(_cQ,_cQ,_dh,_)),_dj=__get(_db,E(_cE)),_dk=__eq(_dj,E(_D));if(!E(_dk)){var _dl=__isUndef(_dj);if(!E(_dl)){var _dm=B(_cy(_dj,_));return new T(function(){return new T3(0,E(_di),E(new T1(1,_dm)),E(_cD));});}else{return new T(function(){return new T3(0,E(_di),E(_4l),E(_cD));});}}else{return new T(function(){return new T3(0,E(_di),E(_4l),E(_cD));});}}},_dn=function(_do,_dp,_){return new F(function(){return _d9(_do,E(_dp),_);});},_dq="mouseout",_dr="mouseover",_ds="mousemove",_dt="mouseup",_du="mousedown",_dv="dblclick",_dw="click",_dx="wheel",_dy=function(_dz){switch(E(_dz)){case 0:return E(_dw);case 1:return E(_dv);case 2:return E(_du);case 3:return E(_dt);case 4:return E(_ds);case 5:return E(_dr);case 6:return E(_dq);default:return E(_dx);}},_dA=new T2(0,_dy,_dn),_dB=function(_dC){return E(_dC);},_dD=function(_dE){return E(E(_dE).d);},_dF=function(_dG,_dH){return new F(function(){return A2(_dD,B(_2z(_dG)),new T1(1,_dH));});},_dI=new T2(0,_2j,_dF),_dJ=new T2(0,_cc,_2j),_dK=new T2(0,_dJ,_bR),_dL=new T(function(){return B(unCStr("NoMethodError"));}),_dM=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_6k,_6l,_dL),_dN=new T5(0,new Long(1682668460,2475369181,true),new Long(2653737051,154809188,true),_dM,_4,_4),_dO=function(_dP){return E(_dN);},_dQ=function(_dR){var _dS=E(_dR);return new F(function(){return _2M(B(_2K(_dS.a)),_dO,_dS.b);});},_dT=function(_dU){return E(E(_dU).a);},_dV=function(_6x){return new T2(0,_dW,_6x);},_dX=function(_dY,_dZ){return new F(function(){return _0(E(_dY).a,_dZ);});},_e0=function(_e1,_e2){return new F(function(){return _3X(_dX,_e1,_e2);});},_e3=function(_e4,_e5,_e6){return new F(function(){return _0(E(_e5).a,_e6);});},_e7=new T3(0,_e3,_dT,_e0),_dW=new T(function(){return new T5(0,_dO,_e7,_dV,_dQ,_dT);}),_e8=new T(function(){return B(unCStr("No instance nor default method for class operation"));}),_e9=function(_ea){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_ea,_e8));})),_dW);});},_eb=new T(function(){return B(_e9("Data/Binary/Put.hs:17:10-19|>>="));}),_ec=function(_ed){return E(_eb);},_ee=new T(function(){return B(unCStr(")"));}),_ef=function(_eg,_eh){var _ei=new T(function(){var _ej=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_co(0,_eh,_4)),_ee));})));},1);return B(_0(B(_co(0,_eg,_4)),_ej));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_ei)));});},_ek=function(_el){return new F(function(){return _co(0,E(_el),_4);});},_em=function(_en,_eo,_ep){return new F(function(){return _co(E(_en),E(_eo),_ep);});},_eq=function(_er,_es){return new F(function(){return _co(0,E(_er),_es);});},_et=function(_eu,_ev){return new F(function(){return _3X(_eq,_eu,_ev);});},_ew=new T3(0,_em,_ek,_et),_ex=0,_ey=function(_ez,_eA,_eB){return new F(function(){return A1(_ez,new T2(1,_3U,new T(function(){return B(A1(_eA,_eB));})));});},_eC=new T(function(){return B(unCStr(": empty list"));}),_eD=new T(function(){return B(unCStr("Prelude."));}),_eE=function(_eF){return new F(function(){return err(B(_0(_eD,new T(function(){return B(_0(_eF,_eC));},1))));});},_eG=new T(function(){return B(unCStr("foldr1"));}),_eH=new T(function(){return B(_eE(_eG));}),_eI=function(_eJ,_eK){var _eL=E(_eK);if(!_eL._){return E(_eH);}else{var _eM=_eL.a,_eN=E(_eL.b);if(!_eN._){return E(_eM);}else{return new F(function(){return A2(_eJ,_eM,new T(function(){return B(_eI(_eJ,_eN));}));});}}},_eO=new T(function(){return B(unCStr(" out of range "));}),_eP=new T(function(){return B(unCStr("}.index: Index "));}),_eQ=new T(function(){return B(unCStr("Ix{"));}),_eR=new T2(1,_cm,_4),_eS=new T2(1,_cm,_eR),_eT=0,_eU=function(_eV){return E(E(_eV).a);},_eW=function(_eX,_eY,_eZ,_f0,_f1){var _f2=new T(function(){var _f3=new T(function(){var _f4=new T(function(){var _f5=new T(function(){var _f6=new T(function(){return B(A3(_eI,_ey,new T2(1,new T(function(){return B(A3(_eU,_eZ,_eT,_f0));}),new T2(1,new T(function(){return B(A3(_eU,_eZ,_eT,_f1));}),_4)),_eS));});return B(_0(_eO,new T2(1,_cn,new T2(1,_cn,_f6))));});return B(A(_eU,[_eZ,_ex,_eY,new T2(1,_cm,_f5)]));});return B(_0(_eP,new T2(1,_cn,_f4)));},1);return B(_0(_eX,_f3));},1);return new F(function(){return err(B(_0(_eQ,_f2)));});},_f7=function(_f8,_f9,_fa,_fb,_fc){return new F(function(){return _eW(_f8,_f9,_fc,_fa,_fb);});},_fd=function(_fe,_ff,_fg,_fh){var _fi=E(_fg);return new F(function(){return _f7(_fe,_ff,_fi.a,_fi.b,_fh);});},_fj=function(_fk,_fl,_fm,_fn){return new F(function(){return _fd(_fn,_fm,_fl,_fk);});},_fo=new T(function(){return B(unCStr("Int"));}),_fp=function(_fq,_fr,_fs){return new F(function(){return _fj(_ew,new T2(0,_fr,_fs),_fq,_fo);});},_ft=function(_fu,_fv,_fw,_fx,_fy,_fz){var _fA=_fu+_fz|0;if(_fv>_fA){return new F(function(){return _fp(_fA,_fv,_fw);});}else{if(_fA>_fw){return new F(function(){return _fp(_fA,_fv,_fw);});}else{var _fB=_fA-_fv|0;if(0>_fB){return new F(function(){return _ef(_fB,_fx);});}else{if(_fB>=_fx){return new F(function(){return _ef(_fB,_fx);});}else{return _fy["v"]["w8"][_fB];}}}}},_fC=function(_fD){return new F(function(){return err(B(unAppCStr("getWord8: no bytes left at ",new T(function(){return B(_co(0,_fD,_4));}))));});},_fE=function(_fF,_fG,_fH,_fI){if(_fI>=_fG){return new F(function(){return _fC(_fI);});}else{return new T2(0,new T(function(){var _fJ=E(_fH);return B(_ft(_fF,E(_fJ.a),E(_fJ.b),_fJ.c,_fJ.d,_fI));}),_fI+1|0);}},_fK=function(_fL,_fM,_fN,_fO){var _fP=B(_fE(_fL,_fM,_fN,_fO)),_fQ=_fP.b,_fR=E(_fP.a);if(_fR>127){var _fS=B(_fK(_fL,_fM,_fN,E(_fQ)));return new T2(0,new T(function(){return (E(_fS.a)<<7>>>0|(_fR&127)>>>0)>>>0;}),_fS.b);}else{return new T2(0,_fR,_fQ);}},_fT=new T(function(){return B(unCStr("too few bytes"));}),_fU=new T(function(){return B(err(_fT));}),_fV=function(_fW,_fX,_fY,_fZ){var _g0=B(_fK(_fW,_fX,_fY,_fZ)),_g1=E(_g0.b),_g2=E(_g0.a)&4294967295;return ((_g1+_g2|0)<=_fX)?new T2(0,new T(function(){var _g3=_fX-_g1|0;if(_g2>_g3){return new T3(0,_fW+_g1|0,_g3,_fY);}else{return new T3(0,_fW+_g1|0,_g2,_fY);}}),_g1+_g2|0):E(_fU);},_g4=function(_g5,_g6){var _g7=E(_g5),_g8=B(_fV(_g7.a,_g7.b,_g7.c,E(_g6)));return new T2(0,_g8.a,_g8.b);},_g9=new T2(0,_ec,_g4),_ga=function(_gb){return E(_eb);},_gc=function(_gd){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_co(9,_gd,_4));}))));});},_ge=function(_gf,_gg,_gh,_gi){var _gj=B(_fE(_gf,_gg,_gh,_gi)),_gk=_gj.b,_gl=E(_gj.a)&4294967295;if(_gl>=128){if(_gl>=224){if(_gl>=240){var _gm=B(_fE(_gf,_gg,_gh,E(_gk))),_gn=B(_fE(_gf,_gg,_gh,E(_gm.b))),_go=B(_fE(_gf,_gg,_gh,E(_gn.b))),_gp=128^E(_go.a)&4294967295|(128^E(_gn.a)&4294967295|(128^E(_gm.a)&4294967295|(240^_gl)<<6)<<6)<<6;if(_gp>>>0>1114111){return new F(function(){return _gc(_gp);});}else{return new T2(0,_gp,_go.b);}}else{var _gq=B(_fE(_gf,_gg,_gh,E(_gk))),_gr=B(_fE(_gf,_gg,_gh,E(_gq.b))),_gs=128^E(_gr.a)&4294967295|(128^E(_gq.a)&4294967295|(224^_gl)<<6)<<6;if(_gs>>>0>1114111){return new F(function(){return _gc(_gs);});}else{return new T2(0,_gs,_gr.b);}}}else{var _gt=B(_fE(_gf,_gg,_gh,E(_gk))),_gu=128^E(_gt.a)&4294967295|(192^_gl)<<6;if(_gu>>>0>1114111){return new F(function(){return _gc(_gu);});}else{return new T2(0,_gu,_gt.b);}}}else{if(_gl>>>0>1114111){return new F(function(){return _gc(_gl);});}else{return new T2(0,_gl,_gk);}}},_gv=function(_gw,_gx){var _gy=E(_gw),_gz=B(_ge(_gy.a,_gy.b,_gy.c,E(_gx)));return new T2(0,_gz.a,_gz.b);},_gA=function(_gB,_gC,_gD){var _gE=E(_gB);if(!_gE._){return new T2(0,_4,_gD);}else{var _gF=new T(function(){return B(A2(_gE.a,_gC,_gD));}),_gG=B(_gA(_gE.b,_gC,new T(function(){return E(E(_gF).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_gF).a);}),_gG.a),_gG.b);}},_gH=function(_gI,_gJ,_gK,_gL){if(0>=_gI){return new F(function(){return _gA(_4,_gK,_gL);});}else{var _gM=function(_gN){var _gO=E(_gN);return (_gO==1)?E(new T2(1,_gJ,_4)):new T2(1,_gJ,new T(function(){return B(_gM(_gO-1|0));}));};return new F(function(){return _gA(B(_gM(_gI)),_gK,_gL);});}},_gP=function(_gQ,_gR,_gS,_gT){var _gU=B(_fK(_gQ,_gR,_gS,_gT));return new F(function(){return _gH(E(_gU.a)&4294967295,_gv,new T3(0,_gQ,_gR,_gS),_gU.b);});},_gV=function(_gW,_gX){var _gY=E(_gW),_gZ=B(_gP(_gY.a,_gY.b,_gY.c,E(_gX)));return new T2(0,_gZ.a,_gZ.b);},_h0=new T2(0,_ga,_gV),_h1=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_h2=new T(function(){return B(err(_h1));}),_h3=function(_h4,_h5,_h6){var _h7=function(_){var _h8=E(_h5),_h9=_h8.c,_ha=newArr(_h9,_h2),_hb=_ha,_hc=function(_hd,_){while(1){if(_hd!=_h9){var _=_hb[_hd]=_h8.d[_hd],_he=_hd+1|0;_hd=_he;continue;}else{return E(_);}}},_=B(_hc(0,_)),_hf=function(_hg,_){while(1){var _hh=E(_hg);if(!_hh._){return new T4(0,E(_h8.a),E(_h8.b),_h9,_hb);}else{var _hi=E(_hh.a),_=_hb[E(_hi.a)]=_hi.b;_hg=_hh.b;continue;}}};return new F(function(){return _hf(_h6,_);});};return new F(function(){return _9d(_h7);});},_hj=function(_hk,_hl,_hm){return new F(function(){return _h3(_hk,_hl,_hm);});},_hn=function(_ho,_hp,_hq){return E(E(_hp).d[E(_hq)]);},_hr=function(_hs,_ht,_hu){return new F(function(){return _hn(_hs,_ht,_hu);});},_hv=function(_hw,_hx,_hy){var _hz=E(_hx),_hA=B(A2(_9z,_hw,_hz)),_hB=function(_){var _hC=newArr(_hA,_h2),_hD=_hC,_hE=function(_hF,_){while(1){var _hG=B((function(_hH,_){var _hI=E(_hH);if(!_hI._){return new T(function(){return new T4(0,E(_hz.a),E(_hz.b),_hA,_hD);});}else{var _hJ=E(_hI.a),_=_hD[E(_hJ.a)]=_hJ.b;_hF=_hI.b;return __continue;}})(_hF,_));if(_hG!=__continue){return _hG;}}};return new F(function(){return _hE(_hy,_);});};return new F(function(){return _9d(_hB);});},_hK=function(_hL,_hM,_hN){return new F(function(){return _hv(_hL,_hM,_hN);});},_hO=function(_hP,_hQ){return E(_hQ).c;},_hR=function(_hS,_hT){return new F(function(){return _hO(_hS,_hT);});},_hU=function(_hV,_hW){var _hX=E(_hW);return new T2(0,_hX.a,_hX.b);},_hY=function(_hZ,_i0){return new F(function(){return _hU(_hZ,_i0);});},_i1=function(_i2,_i3,_i4,_i5){var _i6=function(_){var _i7=E(_i4),_i8=_i7.c,_i9=newArr(_i8,_h2),_ia=_i9,_ib=function(_ic,_){while(1){if(_ic!=_i8){var _=_ia[_ic]=_i7.d[_ic],_id=_ic+1|0;_ic=_id;continue;}else{return E(_);}}},_=B(_ib(0,_)),_ie=function(_if,_){while(1){var _ig=B((function(_ih,_){var _ii=E(_ih);if(!_ii._){return new T4(0,E(_i7.a),E(_i7.b),_i8,_ia);}else{var _ij=E(_ii.a),_ik=E(_ij.a),_il=_ia[_ik],_=_ia[_ik]=new T(function(){return B(A2(_i3,_il,_ij.b));});_if=_ii.b;return __continue;}})(_if,_));if(_ig!=__continue){return _ig;}}};return new F(function(){return _ie(_i5,_);});};return new F(function(){return _9d(_i6);});},_im=function(_in,_io,_ip,_iq,_ir){var _is=E(_iq),_it=B(A2(_9z,_in,_is)),_iu=function(_){var _iv=newArr(_it,_ip),_iw=_iv,_ix=function(_iy,_){while(1){var _iz=B((function(_iA,_){var _iB=E(_iA);if(!_iB._){return new T(function(){return new T4(0,E(_is.a),E(_is.b),_it,_iw);});}else{var _iC=E(_iB.a),_iD=E(_iC.a),_iE=_iw[_iD],_=_iw[_iD]=new T(function(){return B(A2(_io,_iE,_iC.b));});_iy=_iB.b;return __continue;}})(_iy,_));if(_iz!=__continue){return _iz;}}};return new F(function(){return _ix(_ir,_);});};return new F(function(){return _9d(_iu);});},_iF={_:0,a:_hY,b:_hR,c:_hK,d:_hr,e:_hj,f:_i1,g:_im},_iG=new T(function(){return B(unCStr("Negative range size"));}),_iH=new T(function(){return B(err(_iG));}),_iI=0,_iJ=function(_iK){var _iL=E(_iK);return (E(_iL.b)-E(_iL.a)|0)+1|0;},_iM=function(_iN,_iO){var _iP=E(_iN),_iQ=E(_iO);return (E(_iP.a)>_iQ)?false:_iQ<=E(_iP.b);},_iR=new T(function(){return B(unCStr("Int"));}),_iS=function(_iT,_iU){return new F(function(){return _fj(_ew,_iU,_iT,_iR);});},_iV=function(_iW,_iX){var _iY=E(_iW),_iZ=E(_iY.a),_j0=E(_iX);if(_iZ>_j0){return new F(function(){return _iS(_j0,_iY);});}else{if(_j0>E(_iY.b)){return new F(function(){return _iS(_j0,_iY);});}else{return _j0-_iZ|0;}}},_j1=function(_j2,_j3){if(_j2<=_j3){var _j4=function(_j5){return new T2(1,_j5,new T(function(){if(_j5!=_j3){return B(_j4(_j5+1|0));}else{return __Z;}}));};return new F(function(){return _j4(_j2);});}else{return __Z;}},_j6=function(_j7,_j8){return new F(function(){return _j1(E(_j7),E(_j8));});},_j9=function(_ja){var _jb=E(_ja);return new F(function(){return _j6(_jb.a,_jb.b);});},_jc=function(_jd){var _je=E(_jd),_jf=E(_je.a),_jg=E(_je.b);return (_jf>_jg)?E(_ex):(_jg-_jf|0)+1|0;},_jh=function(_ji,_jj){return E(_ji)-E(_jj)|0;},_jk=function(_jl,_jm){return new F(function(){return _jh(_jm,E(_jl).a);});},_jn=function(_jo,_jp){return E(_jo)==E(_jp);},_jq=function(_jr,_js){return E(_jr)!=E(_js);},_jt=new T2(0,_jn,_jq),_ju=function(_jv,_jw){var _jx=E(_jv),_jy=E(_jw);return (_jx>_jy)?E(_jx):E(_jy);},_jz=function(_jA,_jB){var _jC=E(_jA),_jD=E(_jB);return (_jC>_jD)?E(_jD):E(_jC);},_jE=function(_jF,_jG){return (_jF>=_jG)?(_jF!=_jG)?2:1:0;},_jH=function(_jI,_jJ){return new F(function(){return _jE(E(_jI),E(_jJ));});},_jK=function(_jL,_jM){return E(_jL)>=E(_jM);},_jN=function(_jO,_jP){return E(_jO)>E(_jP);},_jQ=function(_jR,_jS){return E(_jR)<=E(_jS);},_jT=function(_jU,_jV){return E(_jU)<E(_jV);},_jW={_:0,a:_jt,b:_jH,c:_jT,d:_jQ,e:_jN,f:_jK,g:_ju,h:_jz},_jX={_:0,a:_jW,b:_j9,c:_iV,d:_jk,e:_iM,f:_jc,g:_iJ},_jY=function(_jZ,_k0,_k1){var _k2=E(_jZ);if(!_k2._){return new T2(0,_4,_k1);}else{var _k3=new T(function(){return B(A2(_k2.a,_k0,_k1));}),_k4=B(_jY(_k2.b,_k0,new T(function(){return E(E(_k3).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_k3).a);}),_k4.a),_k4.b);}},_k5=function(_k6,_k7,_k8,_k9){if(0>=_k6){return new F(function(){return _jY(_4,_k8,_k9);});}else{var _ka=function(_kb){var _kc=E(_kb);return (_kc==1)?E(new T2(1,_k7,_4)):new T2(1,_k7,new T(function(){return B(_ka(_kc-1|0));}));};return new F(function(){return _jY(B(_ka(_k6)),_k8,_k9);});}},_kd=function(_ke){return E(E(_ke).b);},_kf=function(_kg){return E(E(_kg).c);},_kh=function(_ki,_kj){var _kk=E(_ki);if(!_kk._){return __Z;}else{var _kl=E(_kj);return (_kl._==0)?__Z:new T2(1,new T2(0,_kk.a,_kl.a),new T(function(){return B(_kh(_kk.b,_kl.b));}));}},_km=function(_kn,_ko,_kp,_kq,_kr,_ks){var _kt=B(_fK(_kp,_kq,_kr,_ks)),_ku=E(_kt.a)&4294967295,_kv=B(_k5(_ku,new T(function(){return B(_kd(_kn));}),new T3(0,_kp,_kq,_kr),_kt.b)),_kw=_kv.a,_kx=new T(function(){var _ky=_ku-1|0;return B(A(_kf,[_ko,_jX,new T2(0,_iI,_ky),new T(function(){if(0>_ky){return B(_kh(B(_j1(0,-1)),_kw));}else{var _kz=_ky+1|0;if(_kz>=0){return B(_kh(B(_j1(0,_kz-1|0)),_kw));}else{return E(_iH);}}})]));});return new T2(0,_kx,_kv.b);},_kA=function(_kB,_kC,_kD,_kE){var _kF=B(_fK(_kB,_kC,_kD,_kE)),_kG=B(_fK(_kB,_kC,_kD,E(_kF.b))),_kH=B(_km(_h0,_iF,_kB,_kC,_kD,E(_kG.b)));return new T2(0,new T(function(){var _kI=E(_kH.a);return new T6(0,E(_kF.a)&4294967295,E(_kG.a)&4294967295,E(_kI.a),E(_kI.b),_kI.c,_kI.d);}),_kH.b);},_kJ=function(_kK,_kL){var _kM=E(_kK),_kN=B(_kA(_kM.a,_kM.b,_kM.c,E(_kL)));return new T2(0,_kN.a,_kN.b);},_kO=function(_kP){return E(_eb);},_kQ=new T2(0,_kO,_kJ),_kR=function(_kS,_kT){var _kU=E(_kS),_kV=B(_fK(_kU.a,_kU.b,_kU.c,E(_kT)));return new T2(0,new T(function(){return E(_kV.a)&4294967295;}),_kV.b);},_kW=new T(function(){return B(_e9("Data/Binary.hs:56:10-20|put"));}),_kX=function(_kY){return E(_kW);},_kZ=new T2(0,_kX,_kR),_l0=function(_l1,_l2){var _l3=E(_l2);return new T2(0,_l3.a,_l3.b);},_l4=function(_l5,_l6){return E(_l6).c;},_l7=function(_l8,_l9,_la,_lb){var _lc=function(_){var _ld=E(_la),_le=_ld.d,_lf=_le["byteLength"],_lg=newByteArr(_lf),_lh=_lg,_li=memcpy(_lh,_le,_lf>>>0),_lj=function(_lk,_){while(1){var _ll=E(_lk);if(!_ll._){return _5;}else{var _lm=E(_ll.a),_ln=E(_lm.a),_lo=_lh["v"]["i32"][_ln],_=_lh["v"]["i32"][_ln]=B(A2(_l9,_lo,_lm.b));_lk=_ll.b;continue;}}},_lp=B(_lj(_lb,_));return new T4(0,E(_ld.a),E(_ld.b),_ld.c,_lh);};return new F(function(){return _9d(_lc);});},_lq=function(_lr,_ls,_lt,_lu,_lv){var _lw=E(_lu),_lx=function(_){var _ly=B(A2(_9z,_lr,_lw)),_lz=newByteArr(imul(4,_ly)|0),_lA=_lz;if(_ly>=0){var _lB=_ly-1|0,_lC=function(_){var _lD=function(_lE,_){while(1){var _lF=E(_lE);if(!_lF._){return _5;}else{var _lG=E(_lF.a),_lH=E(_lG.a),_lI=_lA["v"]["i32"][_lH],_=_lA["v"]["i32"][_lH]=B(A2(_ls,_lI,_lG.b));_lE=_lF.b;continue;}}},_lJ=B(_lD(_lv,_));return new T4(0,E(_lw.a),E(_lw.b),_ly,_lA);};if(0<=_lB){var _lK=function(_lL,_){while(1){var _=_lA["v"]["i32"][_lL]=E(_lt);if(_lL!=_lB){var _lM=_lL+1|0;_lL=_lM;continue;}else{return _5;}}},_lN=B(_lK(0,_));return new F(function(){return _lC(_);});}else{return new F(function(){return _lC(_);});}}else{return E(_9C);}},_lO=E(_lx);return new F(function(){return _9d(_lO);});},_lP=function(_lQ,_lR,_lS){var _lT=E(_lR),_lU=function(_){var _lV=B(A2(_9z,_lQ,_lT)),_lW=newByteArr(imul(4,_lV)|0),_lX=_lW;if(_lV>=0){var _lY=_lV-1|0,_lZ=function(_){var _m0=function(_m1,_){while(1){var _m2=E(_m1);if(!_m2._){return _5;}else{var _m3=E(_m2.a),_=_lX["v"]["i32"][E(_m3.a)]=E(_m3.b);_m1=_m2.b;continue;}}},_m4=B(_m0(_lS,_));return new T4(0,E(_lT.a),E(_lT.b),_lV,_lX);};if(0<=_lY){var _m5=function(_m6,_){while(1){var _=_lX["v"]["i32"][_m6]=0;if(_m6!=_lY){var _m7=_m6+1|0;_m6=_m7;continue;}else{return _5;}}},_m8=B(_m5(0,_));return new F(function(){return _lZ(_);});}else{return new F(function(){return _lZ(_);});}}else{return E(_9C);}},_m9=E(_lU);return new F(function(){return _9d(_m9);});},_ma=function(_mb,_mc,_md){return E(_mc).d["v"]["i32"][E(_md)];},_me=function(_mf,_mg,_mh){var _mi=function(_){var _mj=E(_mg),_mk=_mj.d,_ml=_mk["byteLength"],_mm=newByteArr(_ml),_mn=_mm,_mo=memcpy(_mn,_mk,_ml>>>0),_mp=function(_mq,_){while(1){var _mr=E(_mq);if(!_mr._){return _5;}else{var _ms=E(_mr.a),_=_mn["v"]["i32"][E(_ms.a)]=E(_ms.b);_mq=_mr.b;continue;}}},_mt=B(_mp(_mh,_));return new T4(0,E(_mj.a),E(_mj.b),_mj.c,_mn);};return new F(function(){return _9d(_mi);});},_mu={_:0,a:_l0,b:_l4,c:_lP,d:_ma,e:_me,f:_l7,g:_lq},_mv=function(_mw,_mx,_my,_mz){var _mA=B(_fV(_mw,_mx,_my,_mz)),_mB=B(_km(_kZ,_mu,_mw,_mx,_my,E(_mA.b)));return new T2(0,new T(function(){var _mC=E(_mB.a);return new T5(0,_mA.a,E(_mC.a),E(_mC.b),_mC.c,_mC.d);}),_mB.b);},_mD=function(_mE,_mF){var _mG=E(_mE),_mH=B(_mv(_mG.a,_mG.b,_mG.c,E(_mF)));return new T2(0,_mH.a,_mH.b);},_mI=function(_mJ){return E(_eb);},_mK=new T2(0,_mI,_mD),_mL=function(_mM){return new F(function(){return _j1(E(_mM),2147483647);});},_mN=function(_mO,_mP,_mQ){if(_mQ<=_mP){var _mR=new T(function(){var _mS=_mP-_mO|0,_mT=function(_mU){return (_mU>=(_mQ-_mS|0))?new T2(1,_mU,new T(function(){return B(_mT(_mU+_mS|0));})):new T2(1,_mU,_4);};return B(_mT(_mP));});return new T2(1,_mO,_mR);}else{return (_mQ<=_mO)?new T2(1,_mO,_4):__Z;}},_mV=function(_mW,_mX,_mY){if(_mY>=_mX){var _mZ=new T(function(){var _n0=_mX-_mW|0,_n1=function(_n2){return (_n2<=(_mY-_n0|0))?new T2(1,_n2,new T(function(){return B(_n1(_n2+_n0|0));})):new T2(1,_n2,_4);};return B(_n1(_mX));});return new T2(1,_mW,_mZ);}else{return (_mY>=_mW)?new T2(1,_mW,_4):__Z;}},_n3=function(_n4,_n5){if(_n5<_n4){return new F(function(){return _mN(_n4,_n5,-2147483648);});}else{return new F(function(){return _mV(_n4,_n5,2147483647);});}},_n6=function(_n7,_n8){return new F(function(){return _n3(E(_n7),E(_n8));});},_n9=function(_na,_nb,_nc){if(_nb<_na){return new F(function(){return _mN(_na,_nb,_nc);});}else{return new F(function(){return _mV(_na,_nb,_nc);});}},_nd=function(_ne,_nf,_ng){return new F(function(){return _n9(E(_ne),E(_nf),E(_ng));});},_nh=function(_ni){return E(_ni);},_nj=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_nk=new T(function(){return B(err(_nj));}),_nl=function(_nm){var _nn=E(_nm);return (_nn==(-2147483648))?E(_nk):_nn-1|0;},_no=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_np=new T(function(){return B(err(_no));}),_nq=function(_nr){var _ns=E(_nr);return (_ns==2147483647)?E(_np):_ns+1|0;},_nt={_:0,a:_nq,b:_nl,c:_nh,d:_nh,e:_mL,f:_n6,g:_j6,h:_nd},_nu=function(_nv,_nw){if(_nv<=0){if(_nv>=0){return new F(function(){return quot(_nv,_nw);});}else{if(_nw<=0){return new F(function(){return quot(_nv,_nw);});}else{return quot(_nv+1|0,_nw)-1|0;}}}else{if(_nw>=0){if(_nv>=0){return new F(function(){return quot(_nv,_nw);});}else{if(_nw<=0){return new F(function(){return quot(_nv,_nw);});}else{return quot(_nv+1|0,_nw)-1|0;}}}else{return quot(_nv-1|0,_nw)-1|0;}}},_nx=new T(function(){return B(unCStr("base"));}),_ny=new T(function(){return B(unCStr("GHC.Exception"));}),_nz=new T(function(){return B(unCStr("ArithException"));}),_nA=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_nx,_ny,_nz),_nB=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_nA,_4,_4),_nC=function(_nD){return E(_nB);},_nE=function(_nF){var _nG=E(_nF);return new F(function(){return _2M(B(_2K(_nG.a)),_nC,_nG.b);});},_nH=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_nI=new T(function(){return B(unCStr("denormal"));}),_nJ=new T(function(){return B(unCStr("divide by zero"));}),_nK=new T(function(){return B(unCStr("loss of precision"));}),_nL=new T(function(){return B(unCStr("arithmetic underflow"));}),_nM=new T(function(){return B(unCStr("arithmetic overflow"));}),_nN=function(_nO,_nP){switch(E(_nO)){case 0:return new F(function(){return _0(_nM,_nP);});break;case 1:return new F(function(){return _0(_nL,_nP);});break;case 2:return new F(function(){return _0(_nK,_nP);});break;case 3:return new F(function(){return _0(_nJ,_nP);});break;case 4:return new F(function(){return _0(_nI,_nP);});break;default:return new F(function(){return _0(_nH,_nP);});}},_nQ=function(_nR){return new F(function(){return _nN(_nR,_4);});},_nS=function(_nT,_nU,_nV){return new F(function(){return _nN(_nU,_nV);});},_nW=function(_nX,_nY){return new F(function(){return _3X(_nN,_nX,_nY);});},_nZ=new T3(0,_nS,_nQ,_nW),_o0=new T(function(){return new T5(0,_nC,_nZ,_o1,_nE,_nQ);}),_o1=function(_6S){return new T2(0,_o0,_6S);},_o2=3,_o3=new T(function(){return B(_o1(_o2));}),_o4=new T(function(){return die(_o3);}),_o5=0,_o6=new T(function(){return B(_o1(_o5));}),_o7=new T(function(){return die(_o6);}),_o8=function(_o9,_oa){var _ob=E(_oa);switch(_ob){case -1:var _oc=E(_o9);if(_oc==(-2147483648)){return E(_o7);}else{return new F(function(){return _nu(_oc,-1);});}break;case 0:return E(_o4);default:return new F(function(){return _nu(_o9,_ob);});}},_od=function(_oe,_of){return new F(function(){return _o8(E(_oe),E(_of));});},_og=0,_oh=new T2(0,_o7,_og),_oi=function(_oj,_ok){var _ol=E(_oj),_om=E(_ok);switch(_om){case -1:var _on=E(_ol);if(_on==(-2147483648)){return E(_oh);}else{if(_on<=0){if(_on>=0){var _oo=quotRemI(_on,-1);return new T2(0,_oo.a,_oo.b);}else{var _op=quotRemI(_on,-1);return new T2(0,_op.a,_op.b);}}else{var _oq=quotRemI(_on-1|0,-1);return new T2(0,_oq.a-1|0,(_oq.b+(-1)|0)+1|0);}}break;case 0:return E(_o4);default:if(_ol<=0){if(_ol>=0){var _or=quotRemI(_ol,_om);return new T2(0,_or.a,_or.b);}else{if(_om<=0){var _os=quotRemI(_ol,_om);return new T2(0,_os.a,_os.b);}else{var _ot=quotRemI(_ol+1|0,_om);return new T2(0,_ot.a-1|0,(_ot.b+_om|0)-1|0);}}}else{if(_om>=0){if(_ol>=0){var _ou=quotRemI(_ol,_om);return new T2(0,_ou.a,_ou.b);}else{if(_om<=0){var _ov=quotRemI(_ol,_om);return new T2(0,_ov.a,_ov.b);}else{var _ow=quotRemI(_ol+1|0,_om);return new T2(0,_ow.a-1|0,(_ow.b+_om|0)-1|0);}}}else{var _ox=quotRemI(_ol-1|0,_om);return new T2(0,_ox.a-1|0,(_ox.b+_om|0)+1|0);}}}},_oy=function(_oz,_oA){var _oB=_oz%_oA;if(_oz<=0){if(_oz>=0){return E(_oB);}else{if(_oA<=0){return E(_oB);}else{var _oC=E(_oB);return (_oC==0)?0:_oC+_oA|0;}}}else{if(_oA>=0){if(_oz>=0){return E(_oB);}else{if(_oA<=0){return E(_oB);}else{var _oD=E(_oB);return (_oD==0)?0:_oD+_oA|0;}}}else{var _oE=E(_oB);return (_oE==0)?0:_oE+_oA|0;}}},_oF=function(_oG,_oH){var _oI=E(_oH);switch(_oI){case -1:return E(_og);case 0:return E(_o4);default:return new F(function(){return _oy(E(_oG),_oI);});}},_oJ=function(_oK,_oL){var _oM=E(_oK),_oN=E(_oL);switch(_oN){case -1:var _oO=E(_oM);if(_oO==(-2147483648)){return E(_o7);}else{return new F(function(){return quot(_oO,-1);});}break;case 0:return E(_o4);default:return new F(function(){return quot(_oM,_oN);});}},_oP=function(_oQ,_oR){var _oS=E(_oQ),_oT=E(_oR);switch(_oT){case -1:var _oU=E(_oS);if(_oU==(-2147483648)){return E(_oh);}else{var _oV=quotRemI(_oU,-1);return new T2(0,_oV.a,_oV.b);}break;case 0:return E(_o4);default:var _oW=quotRemI(_oS,_oT);return new T2(0,_oW.a,_oW.b);}},_oX=function(_oY,_oZ){var _p0=E(_oZ);switch(_p0){case -1:return E(_og);case 0:return E(_o4);default:return E(_oY)%_p0;}},_p1=function(_p2){return new T1(0,_p2);},_p3=function(_p4){return new F(function(){return _p1(E(_p4));});},_p5=new T1(0,1),_p6=function(_p7){return new T2(0,E(B(_p1(E(_p7)))),E(_p5));},_p8=function(_p9,_pa){return imul(E(_p9),E(_pa))|0;},_pb=function(_pc,_pd){return E(_pc)+E(_pd)|0;},_pe=function(_pf){var _pg=E(_pf);return (_pg<0)? -_pg:E(_pg);},_ph=function(_pi){var _pj=E(_pi);if(!_pj._){return E(_pj.a);}else{return new F(function(){return I_toInt(_pj.a);});}},_pk=function(_pl){return new F(function(){return _ph(_pl);});},_pm=function(_pn){return  -E(_pn);},_po=-1,_pp=0,_pq=1,_pr=function(_ps){var _pt=E(_ps);return (_pt>=0)?(E(_pt)==0)?E(_pp):E(_pq):E(_po);},_pu={_:0,a:_pb,b:_jh,c:_p8,d:_pm,e:_pe,f:_pr,g:_pk},_pv=new T2(0,_jn,_jq),_pw={_:0,a:_pv,b:_jH,c:_jT,d:_jQ,e:_jN,f:_jK,g:_ju,h:_jz},_px=new T3(0,_pu,_pw,_p6),_py={_:0,a:_px,b:_nt,c:_oJ,d:_oX,e:_od,f:_oF,g:_oP,h:_oi,i:_p3},_pz={_:0,a:_nq,b:_nl,c:_nh,d:_nh,e:_mL,f:_n6,g:_j6,h:_nd},_pA={_:0,a:_pb,b:_jh,c:_p8,d:_pm,e:_pe,f:_pr,g:_pk},_pB=new T3(0,_pA,_jW,_p6),_pC={_:0,a:_pB,b:_pz,c:_oJ,d:_oX,e:_od,f:_oF,g:_oP,h:_oi,i:_p3},_pD=new T1(0,2),_pE=function(_pF){return E(E(_pF).a);},_pG=function(_pH){return E(E(_pH).a);},_pI=function(_pJ,_pK){while(1){var _pL=E(_pJ);if(!_pL._){var _pM=_pL.a,_pN=E(_pK);if(!_pN._){var _pO=_pN.a;if(!(imul(_pM,_pO)|0)){return new T1(0,imul(_pM,_pO)|0);}else{_pJ=new T1(1,I_fromInt(_pM));_pK=new T1(1,I_fromInt(_pO));continue;}}else{_pJ=new T1(1,I_fromInt(_pM));_pK=_pN;continue;}}else{var _pP=E(_pK);if(!_pP._){_pJ=_pL;_pK=new T1(1,I_fromInt(_pP.a));continue;}else{return new T1(1,I_mul(_pL.a,_pP.a));}}}},_pQ=function(_pR,_pS,_pT){while(1){if(!(_pS%2)){var _pU=B(_pI(_pR,_pR)),_pV=quot(_pS,2);_pR=_pU;_pS=_pV;continue;}else{var _pW=E(_pS);if(_pW==1){return new F(function(){return _pI(_pR,_pT);});}else{var _pU=B(_pI(_pR,_pR)),_pX=B(_pI(_pR,_pT));_pR=_pU;_pS=quot(_pW-1|0,2);_pT=_pX;continue;}}}},_pY=function(_pZ,_q0){while(1){if(!(_q0%2)){var _q1=B(_pI(_pZ,_pZ)),_q2=quot(_q0,2);_pZ=_q1;_q0=_q2;continue;}else{var _q3=E(_q0);if(_q3==1){return E(_pZ);}else{return new F(function(){return _pQ(B(_pI(_pZ,_pZ)),quot(_q3-1|0,2),_pZ);});}}}},_q4=function(_q5){return E(E(_q5).c);},_q6=function(_q7){return E(E(_q7).a);},_q8=function(_q9){return E(E(_q9).b);},_qa=function(_qb){return E(E(_qb).b);},_qc=function(_qd){return E(E(_qd).c);},_qe=function(_qf){return E(E(_qf).a);},_qg=new T1(0,0),_qh=new T1(0,2),_qi=function(_qj){return E(E(_qj).g);},_qk=function(_ql){return E(E(_ql).d);},_qm=function(_qn,_qo){var _qp=B(_pE(_qn)),_qq=new T(function(){return B(_pG(_qp));}),_qr=new T(function(){return B(A3(_qk,_qn,_qo,new T(function(){return B(A2(_qi,_qq,_qh));})));});return new F(function(){return A3(_qe,B(_q6(B(_q8(_qp)))),_qr,new T(function(){return B(A2(_qi,_qq,_qg));}));});},_qs=new T(function(){return B(unCStr("Negative exponent"));}),_qt=new T(function(){return B(err(_qs));}),_qu=function(_qv){return E(E(_qv).c);},_qw=function(_qx,_qy,_qz,_qA){var _qB=B(_pE(_qy)),_qC=new T(function(){return B(_pG(_qB));}),_qD=B(_q8(_qB));if(!B(A3(_qc,_qD,_qA,new T(function(){return B(A2(_qi,_qC,_qg));})))){if(!B(A3(_qe,B(_q6(_qD)),_qA,new T(function(){return B(A2(_qi,_qC,_qg));})))){var _qE=new T(function(){return B(A2(_qi,_qC,_qh));}),_qF=new T(function(){return B(A2(_qi,_qC,_p5));}),_qG=B(_q6(_qD)),_qH=function(_qI,_qJ,_qK){while(1){var _qL=B((function(_qM,_qN,_qO){if(!B(_qm(_qy,_qN))){if(!B(A3(_qe,_qG,_qN,_qF))){var _qP=new T(function(){return B(A3(_qu,_qy,new T(function(){return B(A3(_qa,_qC,_qN,_qF));}),_qE));});_qI=new T(function(){return B(A3(_q4,_qx,_qM,_qM));});_qJ=_qP;_qK=new T(function(){return B(A3(_q4,_qx,_qM,_qO));});return __continue;}else{return new F(function(){return A3(_q4,_qx,_qM,_qO);});}}else{var _qQ=_qO;_qI=new T(function(){return B(A3(_q4,_qx,_qM,_qM));});_qJ=new T(function(){return B(A3(_qu,_qy,_qN,_qE));});_qK=_qQ;return __continue;}})(_qI,_qJ,_qK));if(_qL!=__continue){return _qL;}}},_qR=function(_qS,_qT){while(1){var _qU=B((function(_qV,_qW){if(!B(_qm(_qy,_qW))){if(!B(A3(_qe,_qG,_qW,_qF))){var _qX=new T(function(){return B(A3(_qu,_qy,new T(function(){return B(A3(_qa,_qC,_qW,_qF));}),_qE));});return new F(function(){return _qH(new T(function(){return B(A3(_q4,_qx,_qV,_qV));}),_qX,_qV);});}else{return E(_qV);}}else{_qS=new T(function(){return B(A3(_q4,_qx,_qV,_qV));});_qT=new T(function(){return B(A3(_qu,_qy,_qW,_qE));});return __continue;}})(_qS,_qT));if(_qU!=__continue){return _qU;}}};return new F(function(){return _qR(_qz,_qA);});}else{return new F(function(){return A2(_qi,_qx,_p5);});}}else{return E(_qt);}},_qY=new T(function(){return B(err(_qs));}),_qZ=function(_r0){var _r1=I_decodeDouble(_r0);return new T2(0,new T1(1,_r1.b),_r1.a);},_r2=function(_r3,_r4){var _r5=E(_r3);return (_r5._==0)?_r5.a*Math.pow(2,_r4):I_toNumber(_r5.a)*Math.pow(2,_r4);},_r6=function(_r7,_r8){var _r9=E(_r7);if(!_r9._){var _ra=_r9.a,_rb=E(_r8);return (_rb._==0)?_ra==_rb.a:(I_compareInt(_rb.a,_ra)==0)?true:false;}else{var _rc=_r9.a,_rd=E(_r8);return (_rd._==0)?(I_compareInt(_rc,_rd.a)==0)?true:false:(I_compare(_rc,_rd.a)==0)?true:false;}},_re=function(_rf,_rg){while(1){var _rh=E(_rf);if(!_rh._){var _ri=E(_rh.a);if(_ri==(-2147483648)){_rf=new T1(1,I_fromInt(-2147483648));continue;}else{var _rj=E(_rg);if(!_rj._){var _rk=_rj.a;return new T2(0,new T1(0,quot(_ri,_rk)),new T1(0,_ri%_rk));}else{_rf=new T1(1,I_fromInt(_ri));_rg=_rj;continue;}}}else{var _rl=E(_rg);if(!_rl._){_rf=_rh;_rg=new T1(1,I_fromInt(_rl.a));continue;}else{var _rm=I_quotRem(_rh.a,_rl.a);return new T2(0,new T1(1,_rm.a),new T1(1,_rm.b));}}}},_rn=0,_ro=new T1(0,0),_rp=function(_rq,_rr){var _rs=B(_qZ(_rr)),_rt=_rs.a,_ru=_rs.b,_rv=new T(function(){return B(_pG(new T(function(){return B(_pE(_rq));})));});if(_ru<0){var _rw= -_ru;if(_rw>=0){var _rx=E(_rw);if(!_rx){var _ry=E(_p5);}else{var _ry=B(_pY(_pD,_rx));}if(!B(_r6(_ry,_ro))){var _rz=B(_re(_rt,_ry));return new T2(0,new T(function(){return B(A2(_qi,_rv,_rz.a));}),new T(function(){return B(_r2(_rz.b,_ru));}));}else{return E(_o4);}}else{return E(_qY);}}else{var _rA=new T(function(){var _rB=new T(function(){return B(_qw(_rv,_pC,new T(function(){return B(A2(_qi,_rv,_pD));}),_ru));});return B(A3(_q4,_rv,new T(function(){return B(A2(_qi,_rv,_rt));}),_rB));});return new T2(0,_rA,_rn);}},_rC=function(_rD){var _rE=E(_rD);if(!_rE._){return _rE.a;}else{return new F(function(){return I_toNumber(_rE.a);});}},_rF=function(_rG,_rH){var _rI=B(_rp(_py,Math.pow(B(_rC(_rG)),_rH))),_rJ=_rI.a;return (E(_rI.b)>=0)?E(_rJ):E(_rJ)-1|0;},_rK=new T1(0,1),_rL=new T1(0,0),_rM=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_rN=new T(function(){return B(err(_rM));}),_rO=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_rP=new T(function(){return B(err(_rO));}),_rQ=new T1(0,2),_rR=new T(function(){return B(unCStr("NaN"));}),_rS=new T(function(){return B(_7f("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_rT=function(_rU,_rV){while(1){var _rW=B((function(_rX,_rY){var _rZ=E(_rX);switch(_rZ._){case 0:var _s0=E(_rY);if(!_s0._){return __Z;}else{_rU=B(A1(_rZ.a,_s0.a));_rV=_s0.b;return __continue;}break;case 1:var _s1=B(A1(_rZ.a,_rY)),_s2=_rY;_rU=_s1;_rV=_s2;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_rZ.a,_rY),new T(function(){return B(_rT(_rZ.b,_rY));}));default:return E(_rZ.a);}})(_rU,_rV));if(_rW!=__continue){return _rW;}}},_s3=function(_s4,_s5){var _s6=function(_s7){var _s8=E(_s5);if(_s8._==3){return new T2(3,_s8.a,new T(function(){return B(_s3(_s4,_s8.b));}));}else{var _s9=E(_s4);if(_s9._==2){return E(_s8);}else{var _sa=E(_s8);if(_sa._==2){return E(_s9);}else{var _sb=function(_sc){var _sd=E(_sa);if(_sd._==4){var _se=function(_sf){return new T1(4,new T(function(){return B(_0(B(_rT(_s9,_sf)),_sd.a));}));};return new T1(1,_se);}else{var _sg=E(_s9);if(_sg._==1){var _sh=_sg.a,_si=E(_sd);if(!_si._){return new T1(1,function(_sj){return new F(function(){return _s3(B(A1(_sh,_sj)),_si);});});}else{var _sk=function(_sl){return new F(function(){return _s3(B(A1(_sh,_sl)),new T(function(){return B(A1(_si.a,_sl));}));});};return new T1(1,_sk);}}else{var _sm=E(_sd);if(!_sm._){return E(_rS);}else{var _sn=function(_so){return new F(function(){return _s3(_sg,new T(function(){return B(A1(_sm.a,_so));}));});};return new T1(1,_sn);}}}},_sp=E(_s9);switch(_sp._){case 1:var _sq=E(_sa);if(_sq._==4){var _sr=function(_ss){return new T1(4,new T(function(){return B(_0(B(_rT(B(A1(_sp.a,_ss)),_ss)),_sq.a));}));};return new T1(1,_sr);}else{return new F(function(){return _sb(_);});}break;case 4:var _st=_sp.a,_su=E(_sa);switch(_su._){case 0:var _sv=function(_sw){var _sx=new T(function(){return B(_0(_st,new T(function(){return B(_rT(_su,_sw));},1)));});return new T1(4,_sx);};return new T1(1,_sv);case 1:var _sy=function(_sz){var _sA=new T(function(){return B(_0(_st,new T(function(){return B(_rT(B(A1(_su.a,_sz)),_sz));},1)));});return new T1(4,_sA);};return new T1(1,_sy);default:return new T1(4,new T(function(){return B(_0(_st,_su.a));}));}break;default:return new F(function(){return _sb(_);});}}}}},_sB=E(_s4);switch(_sB._){case 0:var _sC=E(_s5);if(!_sC._){var _sD=function(_sE){return new F(function(){return _s3(B(A1(_sB.a,_sE)),new T(function(){return B(A1(_sC.a,_sE));}));});};return new T1(0,_sD);}else{return new F(function(){return _s6(_);});}break;case 3:return new T2(3,_sB.a,new T(function(){return B(_s3(_sB.b,_s5));}));default:return new F(function(){return _s6(_);});}},_sF=new T(function(){return B(unCStr("("));}),_sG=new T(function(){return B(unCStr(")"));}),_sH=function(_sI,_sJ){while(1){var _sK=E(_sI);if(!_sK._){return (E(_sJ)._==0)?true:false;}else{var _sL=E(_sJ);if(!_sL._){return false;}else{if(E(_sK.a)!=E(_sL.a)){return false;}else{_sI=_sK.b;_sJ=_sL.b;continue;}}}}},_sM=function(_sN,_sO){return E(_sN)!=E(_sO);},_sP=function(_sQ,_sR){return E(_sQ)==E(_sR);},_sS=new T2(0,_sP,_sM),_sT=function(_sU,_sV){while(1){var _sW=E(_sU);if(!_sW._){return (E(_sV)._==0)?true:false;}else{var _sX=E(_sV);if(!_sX._){return false;}else{if(E(_sW.a)!=E(_sX.a)){return false;}else{_sU=_sW.b;_sV=_sX.b;continue;}}}}},_sY=function(_sZ,_t0){return (!B(_sT(_sZ,_t0)))?true:false;},_t1=new T2(0,_sT,_sY),_t2=function(_t3,_t4){var _t5=E(_t3);switch(_t5._){case 0:return new T1(0,function(_t6){return new F(function(){return _t2(B(A1(_t5.a,_t6)),_t4);});});case 1:return new T1(1,function(_t7){return new F(function(){return _t2(B(A1(_t5.a,_t7)),_t4);});});case 2:return new T0(2);case 3:return new F(function(){return _s3(B(A1(_t4,_t5.a)),new T(function(){return B(_t2(_t5.b,_t4));}));});break;default:var _t8=function(_t9){var _ta=E(_t9);if(!_ta._){return __Z;}else{var _tb=E(_ta.a);return new F(function(){return _0(B(_rT(B(A1(_t4,_tb.a)),_tb.b)),new T(function(){return B(_t8(_ta.b));},1));});}},_tc=B(_t8(_t5.a));return (_tc._==0)?new T0(2):new T1(4,_tc);}},_td=new T0(2),_te=function(_tf){return new T2(3,_tf,_td);},_tg=function(_th,_ti){var _tj=E(_th);if(!_tj){return new F(function(){return A1(_ti,_5);});}else{var _tk=new T(function(){return B(_tg(_tj-1|0,_ti));});return new T1(0,function(_tl){return E(_tk);});}},_tm=function(_tn,_to,_tp){var _tq=new T(function(){return B(A1(_tn,_te));}),_tr=function(_ts,_tt,_tu,_tv){while(1){var _tw=B((function(_tx,_ty,_tz,_tA){var _tB=E(_tx);switch(_tB._){case 0:var _tC=E(_ty);if(!_tC._){return new F(function(){return A1(_to,_tA);});}else{var _tD=_tz+1|0,_tE=_tA;_ts=B(A1(_tB.a,_tC.a));_tt=_tC.b;_tu=_tD;_tv=_tE;return __continue;}break;case 1:var _tF=B(A1(_tB.a,_ty)),_tG=_ty,_tD=_tz,_tE=_tA;_ts=_tF;_tt=_tG;_tu=_tD;_tv=_tE;return __continue;case 2:return new F(function(){return A1(_to,_tA);});break;case 3:var _tH=new T(function(){return B(_t2(_tB,_tA));});return new F(function(){return _tg(_tz,function(_tI){return E(_tH);});});break;default:return new F(function(){return _t2(_tB,_tA);});}})(_ts,_tt,_tu,_tv));if(_tw!=__continue){return _tw;}}};return function(_tJ){return new F(function(){return _tr(_tq,_tJ,0,_tp);});};},_tK=function(_tL){return new F(function(){return A1(_tL,_4);});},_tM=function(_tN,_tO){var _tP=function(_tQ){var _tR=E(_tQ);if(!_tR._){return E(_tK);}else{var _tS=_tR.a;if(!B(A1(_tN,_tS))){return E(_tK);}else{var _tT=new T(function(){return B(_tP(_tR.b));}),_tU=function(_tV){var _tW=new T(function(){return B(A1(_tT,function(_tX){return new F(function(){return A1(_tV,new T2(1,_tS,_tX));});}));});return new T1(0,function(_tY){return E(_tW);});};return E(_tU);}}};return function(_tZ){return new F(function(){return A2(_tP,_tZ,_tO);});};},_u0=new T0(6),_u1=new T(function(){return B(unCStr("valDig: Bad base"));}),_u2=new T(function(){return B(err(_u1));}),_u3=function(_u4,_u5){var _u6=function(_u7,_u8){var _u9=E(_u7);if(!_u9._){var _ua=new T(function(){return B(A1(_u8,_4));});return function(_ub){return new F(function(){return A1(_ub,_ua);});};}else{var _uc=E(_u9.a),_ud=function(_ue){var _uf=new T(function(){return B(_u6(_u9.b,function(_ug){return new F(function(){return A1(_u8,new T2(1,_ue,_ug));});}));}),_uh=function(_ui){var _uj=new T(function(){return B(A1(_uf,_ui));});return new T1(0,function(_uk){return E(_uj);});};return E(_uh);};switch(E(_u4)){case 8:if(48>_uc){var _ul=new T(function(){return B(A1(_u8,_4));});return function(_um){return new F(function(){return A1(_um,_ul);});};}else{if(_uc>55){var _un=new T(function(){return B(A1(_u8,_4));});return function(_uo){return new F(function(){return A1(_uo,_un);});};}else{return new F(function(){return _ud(_uc-48|0);});}}break;case 10:if(48>_uc){var _up=new T(function(){return B(A1(_u8,_4));});return function(_uq){return new F(function(){return A1(_uq,_up);});};}else{if(_uc>57){var _ur=new T(function(){return B(A1(_u8,_4));});return function(_us){return new F(function(){return A1(_us,_ur);});};}else{return new F(function(){return _ud(_uc-48|0);});}}break;case 16:if(48>_uc){if(97>_uc){if(65>_uc){var _ut=new T(function(){return B(A1(_u8,_4));});return function(_uu){return new F(function(){return A1(_uu,_ut);});};}else{if(_uc>70){var _uv=new T(function(){return B(A1(_u8,_4));});return function(_uw){return new F(function(){return A1(_uw,_uv);});};}else{return new F(function(){return _ud((_uc-65|0)+10|0);});}}}else{if(_uc>102){if(65>_uc){var _ux=new T(function(){return B(A1(_u8,_4));});return function(_uy){return new F(function(){return A1(_uy,_ux);});};}else{if(_uc>70){var _uz=new T(function(){return B(A1(_u8,_4));});return function(_uA){return new F(function(){return A1(_uA,_uz);});};}else{return new F(function(){return _ud((_uc-65|0)+10|0);});}}}else{return new F(function(){return _ud((_uc-97|0)+10|0);});}}}else{if(_uc>57){if(97>_uc){if(65>_uc){var _uB=new T(function(){return B(A1(_u8,_4));});return function(_uC){return new F(function(){return A1(_uC,_uB);});};}else{if(_uc>70){var _uD=new T(function(){return B(A1(_u8,_4));});return function(_uE){return new F(function(){return A1(_uE,_uD);});};}else{return new F(function(){return _ud((_uc-65|0)+10|0);});}}}else{if(_uc>102){if(65>_uc){var _uF=new T(function(){return B(A1(_u8,_4));});return function(_uG){return new F(function(){return A1(_uG,_uF);});};}else{if(_uc>70){var _uH=new T(function(){return B(A1(_u8,_4));});return function(_uI){return new F(function(){return A1(_uI,_uH);});};}else{return new F(function(){return _ud((_uc-65|0)+10|0);});}}}else{return new F(function(){return _ud((_uc-97|0)+10|0);});}}}else{return new F(function(){return _ud(_uc-48|0);});}}break;default:return E(_u2);}}},_uJ=function(_uK){var _uL=E(_uK);if(!_uL._){return new T0(2);}else{return new F(function(){return A1(_u5,_uL);});}};return function(_uM){return new F(function(){return A3(_u6,_uM,_2j,_uJ);});};},_uN=16,_uO=8,_uP=function(_uQ){var _uR=function(_uS){return new F(function(){return A1(_uQ,new T1(5,new T2(0,_uO,_uS)));});},_uT=function(_uU){return new F(function(){return A1(_uQ,new T1(5,new T2(0,_uN,_uU)));});},_uV=function(_uW){switch(E(_uW)){case 79:return new T1(1,B(_u3(_uO,_uR)));case 88:return new T1(1,B(_u3(_uN,_uT)));case 111:return new T1(1,B(_u3(_uO,_uR)));case 120:return new T1(1,B(_u3(_uN,_uT)));default:return new T0(2);}};return function(_uX){return (E(_uX)==48)?E(new T1(0,_uV)):new T0(2);};},_uY=function(_uZ){return new T1(0,B(_uP(_uZ)));},_v0=function(_v1){return new F(function(){return A1(_v1,_4l);});},_v2=function(_v3){return new F(function(){return A1(_v3,_4l);});},_v4=10,_v5=new T1(0,1),_v6=new T1(0,2147483647),_v7=function(_v8,_v9){while(1){var _va=E(_v8);if(!_va._){var _vb=_va.a,_vc=E(_v9);if(!_vc._){var _vd=_vc.a,_ve=addC(_vb,_vd);if(!E(_ve.b)){return new T1(0,_ve.a);}else{_v8=new T1(1,I_fromInt(_vb));_v9=new T1(1,I_fromInt(_vd));continue;}}else{_v8=new T1(1,I_fromInt(_vb));_v9=_vc;continue;}}else{var _vf=E(_v9);if(!_vf._){_v8=_va;_v9=new T1(1,I_fromInt(_vf.a));continue;}else{return new T1(1,I_add(_va.a,_vf.a));}}}},_vg=new T(function(){return B(_v7(_v6,_v5));}),_vh=function(_vi){var _vj=E(_vi);if(!_vj._){var _vk=E(_vj.a);return (_vk==(-2147483648))?E(_vg):new T1(0, -_vk);}else{return new T1(1,I_negate(_vj.a));}},_vl=new T1(0,10),_vm=function(_vn,_vo){while(1){var _vp=E(_vn);if(!_vp._){return E(_vo);}else{var _vq=_vo+1|0;_vn=_vp.b;_vo=_vq;continue;}}},_vr=function(_vs){return new F(function(){return _p1(E(_vs));});},_vt=new T(function(){return B(unCStr("this should not happen"));}),_vu=new T(function(){return B(err(_vt));}),_vv=function(_vw,_vx){var _vy=E(_vx);if(!_vy._){return __Z;}else{var _vz=E(_vy.b);return (_vz._==0)?E(_vu):new T2(1,B(_v7(B(_pI(_vy.a,_vw)),_vz.a)),new T(function(){return B(_vv(_vw,_vz.b));}));}},_vA=new T1(0,0),_vB=function(_vC,_vD,_vE){while(1){var _vF=B((function(_vG,_vH,_vI){var _vJ=E(_vI);if(!_vJ._){return E(_vA);}else{if(!E(_vJ.b)._){return E(_vJ.a);}else{var _vK=E(_vH);if(_vK<=40){var _vL=function(_vM,_vN){while(1){var _vO=E(_vN);if(!_vO._){return E(_vM);}else{var _vP=B(_v7(B(_pI(_vM,_vG)),_vO.a));_vM=_vP;_vN=_vO.b;continue;}}};return new F(function(){return _vL(_vA,_vJ);});}else{var _vQ=B(_pI(_vG,_vG));if(!(_vK%2)){var _vR=B(_vv(_vG,_vJ));_vC=_vQ;_vD=quot(_vK+1|0,2);_vE=_vR;return __continue;}else{var _vR=B(_vv(_vG,new T2(1,_vA,_vJ)));_vC=_vQ;_vD=quot(_vK+1|0,2);_vE=_vR;return __continue;}}}}})(_vC,_vD,_vE));if(_vF!=__continue){return _vF;}}},_vS=function(_vT,_vU){return new F(function(){return _vB(_vT,new T(function(){return B(_vm(_vU,0));},1),B(_G(_vr,_vU)));});},_vV=function(_vW){var _vX=new T(function(){var _vY=new T(function(){var _vZ=function(_w0){return new F(function(){return A1(_vW,new T1(1,new T(function(){return B(_vS(_vl,_w0));})));});};return new T1(1,B(_u3(_v4,_vZ)));}),_w1=function(_w2){if(E(_w2)==43){var _w3=function(_w4){return new F(function(){return A1(_vW,new T1(1,new T(function(){return B(_vS(_vl,_w4));})));});};return new T1(1,B(_u3(_v4,_w3)));}else{return new T0(2);}},_w5=function(_w6){if(E(_w6)==45){var _w7=function(_w8){return new F(function(){return A1(_vW,new T1(1,new T(function(){return B(_vh(B(_vS(_vl,_w8))));})));});};return new T1(1,B(_u3(_v4,_w7)));}else{return new T0(2);}};return B(_s3(B(_s3(new T1(0,_w5),new T1(0,_w1))),_vY));});return new F(function(){return _s3(new T1(0,function(_w9){return (E(_w9)==101)?E(_vX):new T0(2);}),new T1(0,function(_wa){return (E(_wa)==69)?E(_vX):new T0(2);}));});},_wb=function(_wc){var _wd=function(_we){return new F(function(){return A1(_wc,new T1(1,_we));});};return function(_wf){return (E(_wf)==46)?new T1(1,B(_u3(_v4,_wd))):new T0(2);};},_wg=function(_wh){return new T1(0,B(_wb(_wh)));},_wi=function(_wj){var _wk=function(_wl){var _wm=function(_wn){return new T1(1,B(_tm(_vV,_v0,function(_wo){return new F(function(){return A1(_wj,new T1(5,new T3(1,_wl,_wn,_wo)));});})));};return new T1(1,B(_tm(_wg,_v2,_wm)));};return new F(function(){return _u3(_v4,_wk);});},_wp=function(_wq){return new T1(1,B(_wi(_wq)));},_wr=function(_ws,_wt,_wu){while(1){var _wv=E(_wu);if(!_wv._){return false;}else{if(!B(A3(_qe,_ws,_wt,_wv.a))){_wu=_wv.b;continue;}else{return true;}}}},_ww=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_wx=function(_wy){return new F(function(){return _wr(_sS,_wy,_ww);});},_wz=false,_wA=true,_wB=function(_wC){var _wD=new T(function(){return B(A1(_wC,_uO));}),_wE=new T(function(){return B(A1(_wC,_uN));});return function(_wF){switch(E(_wF)){case 79:return E(_wD);case 88:return E(_wE);case 111:return E(_wD);case 120:return E(_wE);default:return new T0(2);}};},_wG=function(_wH){return new T1(0,B(_wB(_wH)));},_wI=function(_wJ){return new F(function(){return A1(_wJ,_v4);});},_wK=function(_wL,_wM){var _wN=E(_wL);if(!_wN._){var _wO=_wN.a,_wP=E(_wM);return (_wP._==0)?_wO<=_wP.a:I_compareInt(_wP.a,_wO)>=0;}else{var _wQ=_wN.a,_wR=E(_wM);return (_wR._==0)?I_compareInt(_wQ,_wR.a)<=0:I_compare(_wQ,_wR.a)<=0;}},_wS=function(_wT){return new T0(2);},_wU=function(_wV){var _wW=E(_wV);if(!_wW._){return E(_wS);}else{var _wX=_wW.a,_wY=E(_wW.b);if(!_wY._){return E(_wX);}else{var _wZ=new T(function(){return B(_wU(_wY));}),_x0=function(_x1){return new F(function(){return _s3(B(A1(_wX,_x1)),new T(function(){return B(A1(_wZ,_x1));}));});};return E(_x0);}}},_x2=function(_x3,_x4){var _x5=function(_x6,_x7,_x8){var _x9=E(_x6);if(!_x9._){return new F(function(){return A1(_x8,_x3);});}else{var _xa=E(_x7);if(!_xa._){return new T0(2);}else{if(E(_x9.a)!=E(_xa.a)){return new T0(2);}else{var _xb=new T(function(){return B(_x5(_x9.b,_xa.b,_x8));});return new T1(0,function(_xc){return E(_xb);});}}}};return function(_xd){return new F(function(){return _x5(_x3,_xd,_x4);});};},_xe=new T(function(){return B(unCStr("SO"));}),_xf=14,_xg=function(_xh){var _xi=new T(function(){return B(A1(_xh,_xf));});return new T1(1,B(_x2(_xe,function(_xj){return E(_xi);})));},_xk=new T(function(){return B(unCStr("SOH"));}),_xl=1,_xm=function(_xn){var _xo=new T(function(){return B(A1(_xn,_xl));});return new T1(1,B(_x2(_xk,function(_xp){return E(_xo);})));},_xq=function(_xr){return new T1(1,B(_tm(_xm,_xg,_xr)));},_xs=new T(function(){return B(unCStr("NUL"));}),_xt=0,_xu=function(_xv){var _xw=new T(function(){return B(A1(_xv,_xt));});return new T1(1,B(_x2(_xs,function(_xx){return E(_xw);})));},_xy=new T(function(){return B(unCStr("STX"));}),_xz=2,_xA=function(_xB){var _xC=new T(function(){return B(A1(_xB,_xz));});return new T1(1,B(_x2(_xy,function(_xD){return E(_xC);})));},_xE=new T(function(){return B(unCStr("ETX"));}),_xF=3,_xG=function(_xH){var _xI=new T(function(){return B(A1(_xH,_xF));});return new T1(1,B(_x2(_xE,function(_xJ){return E(_xI);})));},_xK=new T(function(){return B(unCStr("EOT"));}),_xL=4,_xM=function(_xN){var _xO=new T(function(){return B(A1(_xN,_xL));});return new T1(1,B(_x2(_xK,function(_xP){return E(_xO);})));},_xQ=new T(function(){return B(unCStr("ENQ"));}),_xR=5,_xS=function(_xT){var _xU=new T(function(){return B(A1(_xT,_xR));});return new T1(1,B(_x2(_xQ,function(_xV){return E(_xU);})));},_xW=new T(function(){return B(unCStr("ACK"));}),_xX=6,_xY=function(_xZ){var _y0=new T(function(){return B(A1(_xZ,_xX));});return new T1(1,B(_x2(_xW,function(_y1){return E(_y0);})));},_y2=new T(function(){return B(unCStr("BEL"));}),_y3=7,_y4=function(_y5){var _y6=new T(function(){return B(A1(_y5,_y3));});return new T1(1,B(_x2(_y2,function(_y7){return E(_y6);})));},_y8=new T(function(){return B(unCStr("BS"));}),_y9=8,_ya=function(_yb){var _yc=new T(function(){return B(A1(_yb,_y9));});return new T1(1,B(_x2(_y8,function(_yd){return E(_yc);})));},_ye=new T(function(){return B(unCStr("HT"));}),_yf=9,_yg=function(_yh){var _yi=new T(function(){return B(A1(_yh,_yf));});return new T1(1,B(_x2(_ye,function(_yj){return E(_yi);})));},_yk=new T(function(){return B(unCStr("LF"));}),_yl=10,_ym=function(_yn){var _yo=new T(function(){return B(A1(_yn,_yl));});return new T1(1,B(_x2(_yk,function(_yp){return E(_yo);})));},_yq=new T(function(){return B(unCStr("VT"));}),_yr=11,_ys=function(_yt){var _yu=new T(function(){return B(A1(_yt,_yr));});return new T1(1,B(_x2(_yq,function(_yv){return E(_yu);})));},_yw=new T(function(){return B(unCStr("FF"));}),_yx=12,_yy=function(_yz){var _yA=new T(function(){return B(A1(_yz,_yx));});return new T1(1,B(_x2(_yw,function(_yB){return E(_yA);})));},_yC=new T(function(){return B(unCStr("CR"));}),_yD=13,_yE=function(_yF){var _yG=new T(function(){return B(A1(_yF,_yD));});return new T1(1,B(_x2(_yC,function(_yH){return E(_yG);})));},_yI=new T(function(){return B(unCStr("SI"));}),_yJ=15,_yK=function(_yL){var _yM=new T(function(){return B(A1(_yL,_yJ));});return new T1(1,B(_x2(_yI,function(_yN){return E(_yM);})));},_yO=new T(function(){return B(unCStr("DLE"));}),_yP=16,_yQ=function(_yR){var _yS=new T(function(){return B(A1(_yR,_yP));});return new T1(1,B(_x2(_yO,function(_yT){return E(_yS);})));},_yU=new T(function(){return B(unCStr("DC1"));}),_yV=17,_yW=function(_yX){var _yY=new T(function(){return B(A1(_yX,_yV));});return new T1(1,B(_x2(_yU,function(_yZ){return E(_yY);})));},_z0=new T(function(){return B(unCStr("DC2"));}),_z1=18,_z2=function(_z3){var _z4=new T(function(){return B(A1(_z3,_z1));});return new T1(1,B(_x2(_z0,function(_z5){return E(_z4);})));},_z6=new T(function(){return B(unCStr("DC3"));}),_z7=19,_z8=function(_z9){var _za=new T(function(){return B(A1(_z9,_z7));});return new T1(1,B(_x2(_z6,function(_zb){return E(_za);})));},_zc=new T(function(){return B(unCStr("DC4"));}),_zd=20,_ze=function(_zf){var _zg=new T(function(){return B(A1(_zf,_zd));});return new T1(1,B(_x2(_zc,function(_zh){return E(_zg);})));},_zi=new T(function(){return B(unCStr("NAK"));}),_zj=21,_zk=function(_zl){var _zm=new T(function(){return B(A1(_zl,_zj));});return new T1(1,B(_x2(_zi,function(_zn){return E(_zm);})));},_zo=new T(function(){return B(unCStr("SYN"));}),_zp=22,_zq=function(_zr){var _zs=new T(function(){return B(A1(_zr,_zp));});return new T1(1,B(_x2(_zo,function(_zt){return E(_zs);})));},_zu=new T(function(){return B(unCStr("ETB"));}),_zv=23,_zw=function(_zx){var _zy=new T(function(){return B(A1(_zx,_zv));});return new T1(1,B(_x2(_zu,function(_zz){return E(_zy);})));},_zA=new T(function(){return B(unCStr("CAN"));}),_zB=24,_zC=function(_zD){var _zE=new T(function(){return B(A1(_zD,_zB));});return new T1(1,B(_x2(_zA,function(_zF){return E(_zE);})));},_zG=new T(function(){return B(unCStr("EM"));}),_zH=25,_zI=function(_zJ){var _zK=new T(function(){return B(A1(_zJ,_zH));});return new T1(1,B(_x2(_zG,function(_zL){return E(_zK);})));},_zM=new T(function(){return B(unCStr("SUB"));}),_zN=26,_zO=function(_zP){var _zQ=new T(function(){return B(A1(_zP,_zN));});return new T1(1,B(_x2(_zM,function(_zR){return E(_zQ);})));},_zS=new T(function(){return B(unCStr("ESC"));}),_zT=27,_zU=function(_zV){var _zW=new T(function(){return B(A1(_zV,_zT));});return new T1(1,B(_x2(_zS,function(_zX){return E(_zW);})));},_zY=new T(function(){return B(unCStr("FS"));}),_zZ=28,_A0=function(_A1){var _A2=new T(function(){return B(A1(_A1,_zZ));});return new T1(1,B(_x2(_zY,function(_A3){return E(_A2);})));},_A4=new T(function(){return B(unCStr("GS"));}),_A5=29,_A6=function(_A7){var _A8=new T(function(){return B(A1(_A7,_A5));});return new T1(1,B(_x2(_A4,function(_A9){return E(_A8);})));},_Aa=new T(function(){return B(unCStr("RS"));}),_Ab=30,_Ac=function(_Ad){var _Ae=new T(function(){return B(A1(_Ad,_Ab));});return new T1(1,B(_x2(_Aa,function(_Af){return E(_Ae);})));},_Ag=new T(function(){return B(unCStr("US"));}),_Ah=31,_Ai=function(_Aj){var _Ak=new T(function(){return B(A1(_Aj,_Ah));});return new T1(1,B(_x2(_Ag,function(_Al){return E(_Ak);})));},_Am=new T(function(){return B(unCStr("SP"));}),_An=32,_Ao=function(_Ap){var _Aq=new T(function(){return B(A1(_Ap,_An));});return new T1(1,B(_x2(_Am,function(_Ar){return E(_Aq);})));},_As=new T(function(){return B(unCStr("DEL"));}),_At=127,_Au=function(_Av){var _Aw=new T(function(){return B(A1(_Av,_At));});return new T1(1,B(_x2(_As,function(_Ax){return E(_Aw);})));},_Ay=new T2(1,_Au,_4),_Az=new T2(1,_Ao,_Ay),_AA=new T2(1,_Ai,_Az),_AB=new T2(1,_Ac,_AA),_AC=new T2(1,_A6,_AB),_AD=new T2(1,_A0,_AC),_AE=new T2(1,_zU,_AD),_AF=new T2(1,_zO,_AE),_AG=new T2(1,_zI,_AF),_AH=new T2(1,_zC,_AG),_AI=new T2(1,_zw,_AH),_AJ=new T2(1,_zq,_AI),_AK=new T2(1,_zk,_AJ),_AL=new T2(1,_ze,_AK),_AM=new T2(1,_z8,_AL),_AN=new T2(1,_z2,_AM),_AO=new T2(1,_yW,_AN),_AP=new T2(1,_yQ,_AO),_AQ=new T2(1,_yK,_AP),_AR=new T2(1,_yE,_AQ),_AS=new T2(1,_yy,_AR),_AT=new T2(1,_ys,_AS),_AU=new T2(1,_ym,_AT),_AV=new T2(1,_yg,_AU),_AW=new T2(1,_ya,_AV),_AX=new T2(1,_y4,_AW),_AY=new T2(1,_xY,_AX),_AZ=new T2(1,_xS,_AY),_B0=new T2(1,_xM,_AZ),_B1=new T2(1,_xG,_B0),_B2=new T2(1,_xA,_B1),_B3=new T2(1,_xu,_B2),_B4=new T2(1,_xq,_B3),_B5=new T(function(){return B(_wU(_B4));}),_B6=34,_B7=new T1(0,1114111),_B8=92,_B9=39,_Ba=function(_Bb){var _Bc=new T(function(){return B(A1(_Bb,_y3));}),_Bd=new T(function(){return B(A1(_Bb,_y9));}),_Be=new T(function(){return B(A1(_Bb,_yf));}),_Bf=new T(function(){return B(A1(_Bb,_yl));}),_Bg=new T(function(){return B(A1(_Bb,_yr));}),_Bh=new T(function(){return B(A1(_Bb,_yx));}),_Bi=new T(function(){return B(A1(_Bb,_yD));}),_Bj=new T(function(){return B(A1(_Bb,_B8));}),_Bk=new T(function(){return B(A1(_Bb,_B9));}),_Bl=new T(function(){return B(A1(_Bb,_B6));}),_Bm=new T(function(){var _Bn=function(_Bo){var _Bp=new T(function(){return B(_p1(E(_Bo)));}),_Bq=function(_Br){var _Bs=B(_vS(_Bp,_Br));if(!B(_wK(_Bs,_B7))){return new T0(2);}else{return new F(function(){return A1(_Bb,new T(function(){var _Bt=B(_ph(_Bs));if(_Bt>>>0>1114111){return B(_gc(_Bt));}else{return _Bt;}}));});}};return new T1(1,B(_u3(_Bo,_Bq)));},_Bu=new T(function(){var _Bv=new T(function(){return B(A1(_Bb,_Ah));}),_Bw=new T(function(){return B(A1(_Bb,_Ab));}),_Bx=new T(function(){return B(A1(_Bb,_A5));}),_By=new T(function(){return B(A1(_Bb,_zZ));}),_Bz=new T(function(){return B(A1(_Bb,_zT));}),_BA=new T(function(){return B(A1(_Bb,_zN));}),_BB=new T(function(){return B(A1(_Bb,_zH));}),_BC=new T(function(){return B(A1(_Bb,_zB));}),_BD=new T(function(){return B(A1(_Bb,_zv));}),_BE=new T(function(){return B(A1(_Bb,_zp));}),_BF=new T(function(){return B(A1(_Bb,_zj));}),_BG=new T(function(){return B(A1(_Bb,_zd));}),_BH=new T(function(){return B(A1(_Bb,_z7));}),_BI=new T(function(){return B(A1(_Bb,_z1));}),_BJ=new T(function(){return B(A1(_Bb,_yV));}),_BK=new T(function(){return B(A1(_Bb,_yP));}),_BL=new T(function(){return B(A1(_Bb,_yJ));}),_BM=new T(function(){return B(A1(_Bb,_xf));}),_BN=new T(function(){return B(A1(_Bb,_xX));}),_BO=new T(function(){return B(A1(_Bb,_xR));}),_BP=new T(function(){return B(A1(_Bb,_xL));}),_BQ=new T(function(){return B(A1(_Bb,_xF));}),_BR=new T(function(){return B(A1(_Bb,_xz));}),_BS=new T(function(){return B(A1(_Bb,_xl));}),_BT=new T(function(){return B(A1(_Bb,_xt));}),_BU=function(_BV){switch(E(_BV)){case 64:return E(_BT);case 65:return E(_BS);case 66:return E(_BR);case 67:return E(_BQ);case 68:return E(_BP);case 69:return E(_BO);case 70:return E(_BN);case 71:return E(_Bc);case 72:return E(_Bd);case 73:return E(_Be);case 74:return E(_Bf);case 75:return E(_Bg);case 76:return E(_Bh);case 77:return E(_Bi);case 78:return E(_BM);case 79:return E(_BL);case 80:return E(_BK);case 81:return E(_BJ);case 82:return E(_BI);case 83:return E(_BH);case 84:return E(_BG);case 85:return E(_BF);case 86:return E(_BE);case 87:return E(_BD);case 88:return E(_BC);case 89:return E(_BB);case 90:return E(_BA);case 91:return E(_Bz);case 92:return E(_By);case 93:return E(_Bx);case 94:return E(_Bw);case 95:return E(_Bv);default:return new T0(2);}};return B(_s3(new T1(0,function(_BW){return (E(_BW)==94)?E(new T1(0,_BU)):new T0(2);}),new T(function(){return B(A1(_B5,_Bb));})));});return B(_s3(new T1(1,B(_tm(_wG,_wI,_Bn))),_Bu));});return new F(function(){return _s3(new T1(0,function(_BX){switch(E(_BX)){case 34:return E(_Bl);case 39:return E(_Bk);case 92:return E(_Bj);case 97:return E(_Bc);case 98:return E(_Bd);case 102:return E(_Bh);case 110:return E(_Bf);case 114:return E(_Bi);case 116:return E(_Be);case 118:return E(_Bg);default:return new T0(2);}}),_Bm);});},_BY=function(_BZ){return new F(function(){return A1(_BZ,_5);});},_C0=function(_C1){var _C2=E(_C1);if(!_C2._){return E(_BY);}else{var _C3=E(_C2.a),_C4=_C3>>>0,_C5=new T(function(){return B(_C0(_C2.b));});if(_C4>887){var _C6=u_iswspace(_C3);if(!E(_C6)){return E(_BY);}else{var _C7=function(_C8){var _C9=new T(function(){return B(A1(_C5,_C8));});return new T1(0,function(_Ca){return E(_C9);});};return E(_C7);}}else{var _Cb=E(_C4);if(_Cb==32){var _Cc=function(_Cd){var _Ce=new T(function(){return B(A1(_C5,_Cd));});return new T1(0,function(_Cf){return E(_Ce);});};return E(_Cc);}else{if(_Cb-9>>>0>4){if(E(_Cb)==160){var _Cg=function(_Ch){var _Ci=new T(function(){return B(A1(_C5,_Ch));});return new T1(0,function(_Cj){return E(_Ci);});};return E(_Cg);}else{return E(_BY);}}else{var _Ck=function(_Cl){var _Cm=new T(function(){return B(A1(_C5,_Cl));});return new T1(0,function(_Cn){return E(_Cm);});};return E(_Ck);}}}}},_Co=function(_Cp){var _Cq=new T(function(){return B(_Co(_Cp));}),_Cr=function(_Cs){return (E(_Cs)==92)?E(_Cq):new T0(2);},_Ct=function(_Cu){return E(new T1(0,_Cr));},_Cv=new T1(1,function(_Cw){return new F(function(){return A2(_C0,_Cw,_Ct);});}),_Cx=new T(function(){return B(_Ba(function(_Cy){return new F(function(){return A1(_Cp,new T2(0,_Cy,_wA));});}));}),_Cz=function(_CA){var _CB=E(_CA);if(_CB==38){return E(_Cq);}else{var _CC=_CB>>>0;if(_CC>887){var _CD=u_iswspace(_CB);return (E(_CD)==0)?new T0(2):E(_Cv);}else{var _CE=E(_CC);return (_CE==32)?E(_Cv):(_CE-9>>>0>4)?(E(_CE)==160)?E(_Cv):new T0(2):E(_Cv);}}};return new F(function(){return _s3(new T1(0,function(_CF){return (E(_CF)==92)?E(new T1(0,_Cz)):new T0(2);}),new T1(0,function(_CG){var _CH=E(_CG);if(E(_CH)==92){return E(_Cx);}else{return new F(function(){return A1(_Cp,new T2(0,_CH,_wz));});}}));});},_CI=function(_CJ,_CK){var _CL=new T(function(){return B(A1(_CK,new T1(1,new T(function(){return B(A1(_CJ,_4));}))));}),_CM=function(_CN){var _CO=E(_CN),_CP=E(_CO.a);if(E(_CP)==34){if(!E(_CO.b)){return E(_CL);}else{return new F(function(){return _CI(function(_CQ){return new F(function(){return A1(_CJ,new T2(1,_CP,_CQ));});},_CK);});}}else{return new F(function(){return _CI(function(_CR){return new F(function(){return A1(_CJ,new T2(1,_CP,_CR));});},_CK);});}};return new F(function(){return _Co(_CM);});},_CS=new T(function(){return B(unCStr("_\'"));}),_CT=function(_CU){var _CV=u_iswalnum(_CU);if(!E(_CV)){return new F(function(){return _wr(_sS,_CU,_CS);});}else{return true;}},_CW=function(_CX){return new F(function(){return _CT(E(_CX));});},_CY=new T(function(){return B(unCStr(",;()[]{}`"));}),_CZ=new T(function(){return B(unCStr("=>"));}),_D0=new T2(1,_CZ,_4),_D1=new T(function(){return B(unCStr("~"));}),_D2=new T2(1,_D1,_D0),_D3=new T(function(){return B(unCStr("@"));}),_D4=new T2(1,_D3,_D2),_D5=new T(function(){return B(unCStr("->"));}),_D6=new T2(1,_D5,_D4),_D7=new T(function(){return B(unCStr("<-"));}),_D8=new T2(1,_D7,_D6),_D9=new T(function(){return B(unCStr("|"));}),_Da=new T2(1,_D9,_D8),_Db=new T(function(){return B(unCStr("\\"));}),_Dc=new T2(1,_Db,_Da),_Dd=new T(function(){return B(unCStr("="));}),_De=new T2(1,_Dd,_Dc),_Df=new T(function(){return B(unCStr("::"));}),_Dg=new T2(1,_Df,_De),_Dh=new T(function(){return B(unCStr(".."));}),_Di=new T2(1,_Dh,_Dg),_Dj=function(_Dk){var _Dl=new T(function(){return B(A1(_Dk,_u0));}),_Dm=new T(function(){var _Dn=new T(function(){var _Do=function(_Dp){var _Dq=new T(function(){return B(A1(_Dk,new T1(0,_Dp)));});return new T1(0,function(_Dr){return (E(_Dr)==39)?E(_Dq):new T0(2);});};return B(_Ba(_Do));}),_Ds=function(_Dt){var _Du=E(_Dt);switch(E(_Du)){case 39:return new T0(2);case 92:return E(_Dn);default:var _Dv=new T(function(){return B(A1(_Dk,new T1(0,_Du)));});return new T1(0,function(_Dw){return (E(_Dw)==39)?E(_Dv):new T0(2);});}},_Dx=new T(function(){var _Dy=new T(function(){return B(_CI(_2j,_Dk));}),_Dz=new T(function(){var _DA=new T(function(){var _DB=new T(function(){var _DC=function(_DD){var _DE=E(_DD),_DF=u_iswalpha(_DE);return (E(_DF)==0)?(E(_DE)==95)?new T1(1,B(_tM(_CW,function(_DG){return new F(function(){return A1(_Dk,new T1(3,new T2(1,_DE,_DG)));});}))):new T0(2):new T1(1,B(_tM(_CW,function(_DH){return new F(function(){return A1(_Dk,new T1(3,new T2(1,_DE,_DH)));});})));};return B(_s3(new T1(0,_DC),new T(function(){return new T1(1,B(_tm(_uY,_wp,_Dk)));})));}),_DI=function(_DJ){return (!B(_wr(_sS,_DJ,_ww)))?new T0(2):new T1(1,B(_tM(_wx,function(_DK){var _DL=new T2(1,_DJ,_DK);if(!B(_wr(_t1,_DL,_Di))){return new F(function(){return A1(_Dk,new T1(4,_DL));});}else{return new F(function(){return A1(_Dk,new T1(2,_DL));});}})));};return B(_s3(new T1(0,_DI),_DB));});return B(_s3(new T1(0,function(_DM){if(!B(_wr(_sS,_DM,_CY))){return new T0(2);}else{return new F(function(){return A1(_Dk,new T1(2,new T2(1,_DM,_4)));});}}),_DA));});return B(_s3(new T1(0,function(_DN){return (E(_DN)==34)?E(_Dy):new T0(2);}),_Dz));});return B(_s3(new T1(0,function(_DO){return (E(_DO)==39)?E(new T1(0,_Ds)):new T0(2);}),_Dx));});return new F(function(){return _s3(new T1(1,function(_DP){return (E(_DP)._==0)?E(_Dl):new T0(2);}),_Dm);});},_DQ=0,_DR=function(_DS,_DT){var _DU=new T(function(){var _DV=new T(function(){var _DW=function(_DX){var _DY=new T(function(){var _DZ=new T(function(){return B(A1(_DT,_DX));});return B(_Dj(function(_E0){var _E1=E(_E0);return (_E1._==2)?(!B(_sH(_E1.a,_sG)))?new T0(2):E(_DZ):new T0(2);}));}),_E2=function(_E3){return E(_DY);};return new T1(1,function(_E4){return new F(function(){return A2(_C0,_E4,_E2);});});};return B(A2(_DS,_DQ,_DW));});return B(_Dj(function(_E5){var _E6=E(_E5);return (_E6._==2)?(!B(_sH(_E6.a,_sF)))?new T0(2):E(_DV):new T0(2);}));}),_E7=function(_E8){return E(_DU);};return function(_E9){return new F(function(){return A2(_C0,_E9,_E7);});};},_Ea=function(_Eb,_Ec){var _Ed=function(_Ee){var _Ef=new T(function(){return B(A1(_Eb,_Ee));}),_Eg=function(_Eh){return new F(function(){return _s3(B(A1(_Ef,_Eh)),new T(function(){return new T1(1,B(_DR(_Ed,_Eh)));}));});};return E(_Eg);},_Ei=new T(function(){return B(A1(_Eb,_Ec));}),_Ej=function(_Ek){return new F(function(){return _s3(B(A1(_Ei,_Ek)),new T(function(){return new T1(1,B(_DR(_Ed,_Ek)));}));});};return E(_Ej);},_El=function(_Em,_En){var _Eo=function(_Ep,_Eq){var _Er=function(_Es){return new F(function(){return A1(_Eq,new T(function(){return  -E(_Es);}));});},_Et=new T(function(){return B(_Dj(function(_Eu){return new F(function(){return A3(_Em,_Eu,_Ep,_Er);});}));}),_Ev=function(_Ew){return E(_Et);},_Ex=function(_Ey){return new F(function(){return A2(_C0,_Ey,_Ev);});},_Ez=new T(function(){return B(_Dj(function(_EA){var _EB=E(_EA);if(_EB._==4){var _EC=E(_EB.a);if(!_EC._){return new F(function(){return A3(_Em,_EB,_Ep,_Eq);});}else{if(E(_EC.a)==45){if(!E(_EC.b)._){return E(new T1(1,_Ex));}else{return new F(function(){return A3(_Em,_EB,_Ep,_Eq);});}}else{return new F(function(){return A3(_Em,_EB,_Ep,_Eq);});}}}else{return new F(function(){return A3(_Em,_EB,_Ep,_Eq);});}}));}),_ED=function(_EE){return E(_Ez);};return new T1(1,function(_EF){return new F(function(){return A2(_C0,_EF,_ED);});});};return new F(function(){return _Ea(_Eo,_En);});},_EG=new T(function(){return 1/0;}),_EH=function(_EI,_EJ){return new F(function(){return A1(_EJ,_EG);});},_EK=new T(function(){return 0/0;}),_EL=function(_EM,_EN){return new F(function(){return A1(_EN,_EK);});},_EO=new T(function(){return B(unCStr("NaN"));}),_EP=new T(function(){return B(unCStr("Infinity"));}),_EQ=1024,_ER=-1021,_ES=function(_ET,_EU){while(1){var _EV=E(_ET);if(!_EV._){var _EW=E(_EV.a);if(_EW==(-2147483648)){_ET=new T1(1,I_fromInt(-2147483648));continue;}else{var _EX=E(_EU);if(!_EX._){return new T1(0,_EW%_EX.a);}else{_ET=new T1(1,I_fromInt(_EW));_EU=_EX;continue;}}}else{var _EY=_EV.a,_EZ=E(_EU);return (_EZ._==0)?new T1(1,I_rem(_EY,I_fromInt(_EZ.a))):new T1(1,I_rem(_EY,_EZ.a));}}},_F0=function(_F1,_F2){if(!B(_r6(_F2,_qg))){return new F(function(){return _ES(_F1,_F2);});}else{return E(_o4);}},_F3=function(_F4,_F5){while(1){if(!B(_r6(_F5,_qg))){var _F6=_F5,_F7=B(_F0(_F4,_F5));_F4=_F6;_F5=_F7;continue;}else{return E(_F4);}}},_F8=function(_F9){var _Fa=E(_F9);if(!_Fa._){var _Fb=E(_Fa.a);return (_Fb==(-2147483648))?E(_vg):(_Fb<0)?new T1(0, -_Fb):E(_Fa);}else{var _Fc=_Fa.a;return (I_compareInt(_Fc,0)>=0)?E(_Fa):new T1(1,I_negate(_Fc));}},_Fd=function(_Fe,_Ff){while(1){var _Fg=E(_Fe);if(!_Fg._){var _Fh=E(_Fg.a);if(_Fh==(-2147483648)){_Fe=new T1(1,I_fromInt(-2147483648));continue;}else{var _Fi=E(_Ff);if(!_Fi._){return new T1(0,quot(_Fh,_Fi.a));}else{_Fe=new T1(1,I_fromInt(_Fh));_Ff=_Fi;continue;}}}else{var _Fj=_Fg.a,_Fk=E(_Ff);return (_Fk._==0)?new T1(0,I_toInt(I_quot(_Fj,I_fromInt(_Fk.a)))):new T1(1,I_quot(_Fj,_Fk.a));}}},_Fl=5,_Fm=new T(function(){return B(_o1(_Fl));}),_Fn=new T(function(){return die(_Fm);}),_Fo=function(_Fp,_Fq){if(!B(_r6(_Fq,_qg))){var _Fr=B(_F3(B(_F8(_Fp)),B(_F8(_Fq))));return (!B(_r6(_Fr,_qg)))?new T2(0,B(_Fd(_Fp,_Fr)),B(_Fd(_Fq,_Fr))):E(_o4);}else{return E(_Fn);}},_Fs=new T(function(){return B(_r6(_qh,_qg));}),_Ft=function(_Fu,_Fv){while(1){var _Fw=E(_Fu);if(!_Fw._){var _Fx=_Fw.a,_Fy=E(_Fv);if(!_Fy._){var _Fz=_Fy.a,_FA=subC(_Fx,_Fz);if(!E(_FA.b)){return new T1(0,_FA.a);}else{_Fu=new T1(1,I_fromInt(_Fx));_Fv=new T1(1,I_fromInt(_Fz));continue;}}else{_Fu=new T1(1,I_fromInt(_Fx));_Fv=_Fy;continue;}}else{var _FB=E(_Fv);if(!_FB._){_Fu=_Fw;_Fv=new T1(1,I_fromInt(_FB.a));continue;}else{return new T1(1,I_sub(_Fw.a,_FB.a));}}}},_FC=function(_FD,_FE,_FF){while(1){if(!E(_Fs)){if(!B(_r6(B(_ES(_FE,_qh)),_qg))){if(!B(_r6(_FE,_p5))){var _FG=B(_pI(_FD,_FD)),_FH=B(_Fd(B(_Ft(_FE,_p5)),_qh)),_FI=B(_pI(_FD,_FF));_FD=_FG;_FE=_FH;_FF=_FI;continue;}else{return new F(function(){return _pI(_FD,_FF);});}}else{var _FG=B(_pI(_FD,_FD)),_FH=B(_Fd(_FE,_qh));_FD=_FG;_FE=_FH;continue;}}else{return E(_o4);}}},_FJ=function(_FK,_FL){while(1){if(!E(_Fs)){if(!B(_r6(B(_ES(_FL,_qh)),_qg))){if(!B(_r6(_FL,_p5))){return new F(function(){return _FC(B(_pI(_FK,_FK)),B(_Fd(B(_Ft(_FL,_p5)),_qh)),_FK);});}else{return E(_FK);}}else{var _FM=B(_pI(_FK,_FK)),_FN=B(_Fd(_FL,_qh));_FK=_FM;_FL=_FN;continue;}}else{return E(_o4);}}},_FO=function(_FP,_FQ){var _FR=E(_FP);if(!_FR._){var _FS=_FR.a,_FT=E(_FQ);return (_FT._==0)?_FS<_FT.a:I_compareInt(_FT.a,_FS)>0;}else{var _FU=_FR.a,_FV=E(_FQ);return (_FV._==0)?I_compareInt(_FU,_FV.a)<0:I_compare(_FU,_FV.a)<0;}},_FW=function(_FX,_FY){if(!B(_FO(_FY,_qg))){if(!B(_r6(_FY,_qg))){return new F(function(){return _FJ(_FX,_FY);});}else{return E(_p5);}}else{return E(_qY);}},_FZ=new T1(0,1),_G0=new T1(0,0),_G1=new T1(0,-1),_G2=function(_G3){var _G4=E(_G3);if(!_G4._){var _G5=_G4.a;return (_G5>=0)?(E(_G5)==0)?E(_G0):E(_v5):E(_G1);}else{var _G6=I_compareInt(_G4.a,0);return (_G6<=0)?(E(_G6)==0)?E(_G0):E(_G1):E(_v5);}},_G7=function(_G8,_G9,_Ga){while(1){var _Gb=E(_Ga);if(!_Gb._){if(!B(_FO(_G8,_vA))){return new T2(0,B(_pI(_G9,B(_FW(_vl,_G8)))),_p5);}else{var _Gc=B(_FW(_vl,B(_vh(_G8))));return new F(function(){return _Fo(B(_pI(_G9,B(_G2(_Gc)))),B(_F8(_Gc)));});}}else{var _Gd=B(_Ft(_G8,_FZ)),_Ge=B(_v7(B(_pI(_G9,_vl)),B(_p1(E(_Gb.a)))));_G8=_Gd;_G9=_Ge;_Ga=_Gb.b;continue;}}},_Gf=function(_Gg,_Gh){var _Gi=E(_Gg);if(!_Gi._){var _Gj=_Gi.a,_Gk=E(_Gh);return (_Gk._==0)?_Gj>=_Gk.a:I_compareInt(_Gk.a,_Gj)<=0;}else{var _Gl=_Gi.a,_Gm=E(_Gh);return (_Gm._==0)?I_compareInt(_Gl,_Gm.a)>=0:I_compare(_Gl,_Gm.a)>=0;}},_Gn=function(_Go){var _Gp=E(_Go);if(!_Gp._){var _Gq=_Gp.b;return new F(function(){return _Fo(B(_pI(B(_vB(new T(function(){return B(_p1(E(_Gp.a)));}),new T(function(){return B(_vm(_Gq,0));},1),B(_G(_vr,_Gq)))),_FZ)),_FZ);});}else{var _Gr=_Gp.a,_Gs=_Gp.c,_Gt=E(_Gp.b);if(!_Gt._){var _Gu=E(_Gs);if(!_Gu._){return new F(function(){return _Fo(B(_pI(B(_vS(_vl,_Gr)),_FZ)),_FZ);});}else{var _Gv=_Gu.a;if(!B(_Gf(_Gv,_vA))){var _Gw=B(_FW(_vl,B(_vh(_Gv))));return new F(function(){return _Fo(B(_pI(B(_vS(_vl,_Gr)),B(_G2(_Gw)))),B(_F8(_Gw)));});}else{return new F(function(){return _Fo(B(_pI(B(_pI(B(_vS(_vl,_Gr)),B(_FW(_vl,_Gv)))),_FZ)),_FZ);});}}}else{var _Gx=_Gt.a,_Gy=E(_Gs);if(!_Gy._){return new F(function(){return _G7(_vA,B(_vS(_vl,_Gr)),_Gx);});}else{return new F(function(){return _G7(_Gy.a,B(_vS(_vl,_Gr)),_Gx);});}}}},_Gz=function(_GA,_GB){while(1){var _GC=E(_GB);if(!_GC._){return __Z;}else{if(!B(A1(_GA,_GC.a))){return E(_GC);}else{_GB=_GC.b;continue;}}}},_GD=function(_GE,_GF){var _GG=E(_GE);if(!_GG._){var _GH=_GG.a,_GI=E(_GF);return (_GI._==0)?_GH>_GI.a:I_compareInt(_GI.a,_GH)<0;}else{var _GJ=_GG.a,_GK=E(_GF);return (_GK._==0)?I_compareInt(_GJ,_GK.a)>0:I_compare(_GJ,_GK.a)>0;}},_GL=0,_GM=function(_GN){return new F(function(){return _jn(_GL,_GN);});},_GO=new T2(0,E(_vA),E(_p5)),_GP=new T1(1,_GO),_GQ=new T1(0,-2147483648),_GR=new T1(0,2147483647),_GS=function(_GT,_GU,_GV){var _GW=E(_GV);if(!_GW._){return new T1(1,new T(function(){var _GX=B(_Gn(_GW));return new T2(0,E(_GX.a),E(_GX.b));}));}else{var _GY=E(_GW.c);if(!_GY._){return new T1(1,new T(function(){var _GZ=B(_Gn(_GW));return new T2(0,E(_GZ.a),E(_GZ.b));}));}else{var _H0=_GY.a;if(!B(_GD(_H0,_GR))){if(!B(_FO(_H0,_GQ))){var _H1=function(_H2){var _H3=_H2+B(_ph(_H0))|0;return (_H3<=(E(_GU)+3|0))?(_H3>=(E(_GT)-3|0))?new T1(1,new T(function(){var _H4=B(_Gn(_GW));return new T2(0,E(_H4.a),E(_H4.b));})):E(_GP):__Z;},_H5=B(_Gz(_GM,_GW.a));if(!_H5._){var _H6=E(_GW.b);if(!_H6._){return E(_GP);}else{var _H7=B(_6T(_GM,_H6.a));if(!E(_H7.b)._){return E(_GP);}else{return new F(function(){return _H1( -B(_vm(_H7.a,0)));});}}}else{return new F(function(){return _H1(B(_vm(_H5,0)));});}}else{return __Z;}}else{return __Z;}}}},_H8=function(_H9,_Ha){return new T0(2);},_Hb=new T1(0,1),_Hc=function(_Hd,_He){var _Hf=E(_Hd);if(!_Hf._){var _Hg=_Hf.a,_Hh=E(_He);if(!_Hh._){var _Hi=_Hh.a;return (_Hg!=_Hi)?(_Hg>_Hi)?2:0:1;}else{var _Hj=I_compareInt(_Hh.a,_Hg);return (_Hj<=0)?(_Hj>=0)?1:2:0;}}else{var _Hk=_Hf.a,_Hl=E(_He);if(!_Hl._){var _Hm=I_compareInt(_Hk,_Hl.a);return (_Hm>=0)?(_Hm<=0)?1:2:0;}else{var _Hn=I_compare(_Hk,_Hl.a);return (_Hn>=0)?(_Hn<=0)?1:2:0;}}},_Ho=function(_Hp,_Hq){while(1){var _Hr=E(_Hp);if(!_Hr._){_Hp=new T1(1,I_fromInt(_Hr.a));continue;}else{return new T1(1,I_shiftLeft(_Hr.a,_Hq));}}},_Hs=function(_Ht,_Hu,_Hv){if(!B(_r6(_Hv,_ro))){var _Hw=B(_re(_Hu,_Hv)),_Hx=_Hw.a;switch(B(_Hc(B(_Ho(_Hw.b,1)),_Hv))){case 0:return new F(function(){return _r2(_Hx,_Ht);});break;case 1:if(!(B(_ph(_Hx))&1)){return new F(function(){return _r2(_Hx,_Ht);});}else{return new F(function(){return _r2(B(_v7(_Hx,_Hb)),_Ht);});}break;default:return new F(function(){return _r2(B(_v7(_Hx,_Hb)),_Ht);});}}else{return E(_o4);}},_Hy=function(_Hz){var _HA=function(_HB,_HC){while(1){if(!B(_FO(_HB,_Hz))){if(!B(_GD(_HB,_Hz))){if(!B(_r6(_HB,_Hz))){return new F(function(){return _7f("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_HC);}}else{return _HC-1|0;}}else{var _HD=B(_Ho(_HB,1)),_HE=_HC+1|0;_HB=_HD;_HC=_HE;continue;}}};return new F(function(){return _HA(_v5,0);});},_HF=function(_HG){var _HH=E(_HG);if(!_HH._){var _HI=_HH.a>>>0;if(!_HI){return -1;}else{var _HJ=function(_HK,_HL){while(1){if(_HK>=_HI){if(_HK<=_HI){if(_HK!=_HI){return new F(function(){return _7f("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_HL);}}else{return _HL-1|0;}}else{var _HM=imul(_HK,2)>>>0,_HN=_HL+1|0;_HK=_HM;_HL=_HN;continue;}}};return new F(function(){return _HJ(1,0);});}}else{return new F(function(){return _Hy(_HH);});}},_HO=function(_HP){var _HQ=E(_HP);if(!_HQ._){var _HR=_HQ.a>>>0;if(!_HR){return new T2(0,-1,0);}else{var _HS=function(_HT,_HU){while(1){if(_HT>=_HR){if(_HT<=_HR){if(_HT!=_HR){return new F(function(){return _7f("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_HU);}}else{return _HU-1|0;}}else{var _HV=imul(_HT,2)>>>0,_HW=_HU+1|0;_HT=_HV;_HU=_HW;continue;}}};return new T2(0,B(_HS(1,0)),(_HR&_HR-1>>>0)>>>0&4294967295);}}else{var _HX=_HQ.a;return new T2(0,B(_HF(_HQ)),I_compareInt(I_and(_HX,I_sub(_HX,I_fromInt(1))),0));}},_HY=function(_HZ,_I0){while(1){var _I1=E(_HZ);if(!_I1._){var _I2=_I1.a,_I3=E(_I0);if(!_I3._){return new T1(0,(_I2>>>0&_I3.a>>>0)>>>0&4294967295);}else{_HZ=new T1(1,I_fromInt(_I2));_I0=_I3;continue;}}else{var _I4=E(_I0);if(!_I4._){_HZ=_I1;_I0=new T1(1,I_fromInt(_I4.a));continue;}else{return new T1(1,I_and(_I1.a,_I4.a));}}}},_I5=new T1(0,2),_I6=function(_I7,_I8){var _I9=E(_I7);if(!_I9._){var _Ia=(_I9.a>>>0&(2<<_I8>>>0)-1>>>0)>>>0,_Ib=1<<_I8>>>0;return (_Ib<=_Ia)?(_Ib>=_Ia)?1:2:0;}else{var _Ic=B(_HY(_I9,B(_Ft(B(_Ho(_I5,_I8)),_v5)))),_Id=B(_Ho(_v5,_I8));return (!B(_GD(_Id,_Ic)))?(!B(_FO(_Id,_Ic)))?1:2:0;}},_Ie=function(_If,_Ig){while(1){var _Ih=E(_If);if(!_Ih._){_If=new T1(1,I_fromInt(_Ih.a));continue;}else{return new T1(1,I_shiftRight(_Ih.a,_Ig));}}},_Ii=function(_Ij,_Ik,_Il,_Im){var _In=B(_HO(_Im)),_Io=_In.a;if(!E(_In.b)){var _Ip=B(_HF(_Il));if(_Ip<((_Io+_Ij|0)-1|0)){var _Iq=_Io+(_Ij-_Ik|0)|0;if(_Iq>0){if(_Iq>_Ip){if(_Iq<=(_Ip+1|0)){if(!E(B(_HO(_Il)).b)){return 0;}else{return new F(function(){return _r2(_Hb,_Ij-_Ik|0);});}}else{return 0;}}else{var _Ir=B(_Ie(_Il,_Iq));switch(B(_I6(_Il,_Iq-1|0))){case 0:return new F(function(){return _r2(_Ir,_Ij-_Ik|0);});break;case 1:if(!(B(_ph(_Ir))&1)){return new F(function(){return _r2(_Ir,_Ij-_Ik|0);});}else{return new F(function(){return _r2(B(_v7(_Ir,_Hb)),_Ij-_Ik|0);});}break;default:return new F(function(){return _r2(B(_v7(_Ir,_Hb)),_Ij-_Ik|0);});}}}else{return new F(function(){return _r2(_Il,(_Ij-_Ik|0)-_Iq|0);});}}else{if(_Ip>=_Ik){var _Is=B(_Ie(_Il,(_Ip+1|0)-_Ik|0));switch(B(_I6(_Il,_Ip-_Ik|0))){case 0:return new F(function(){return _r2(_Is,((_Ip-_Io|0)+1|0)-_Ik|0);});break;case 2:return new F(function(){return _r2(B(_v7(_Is,_Hb)),((_Ip-_Io|0)+1|0)-_Ik|0);});break;default:if(!(B(_ph(_Is))&1)){return new F(function(){return _r2(_Is,((_Ip-_Io|0)+1|0)-_Ik|0);});}else{return new F(function(){return _r2(B(_v7(_Is,_Hb)),((_Ip-_Io|0)+1|0)-_Ik|0);});}}}else{return new F(function(){return _r2(_Il, -_Io);});}}}else{var _It=B(_HF(_Il))-_Io|0,_Iu=function(_Iv){var _Iw=function(_Ix,_Iy){if(!B(_wK(B(_Ho(_Iy,_Ik)),_Ix))){return new F(function(){return _Hs(_Iv-_Ik|0,_Ix,_Iy);});}else{return new F(function(){return _Hs((_Iv-_Ik|0)+1|0,_Ix,B(_Ho(_Iy,1)));});}};if(_Iv>=_Ik){if(_Iv!=_Ik){return new F(function(){return _Iw(_Il,new T(function(){return B(_Ho(_Im,_Iv-_Ik|0));}));});}else{return new F(function(){return _Iw(_Il,_Im);});}}else{return new F(function(){return _Iw(new T(function(){return B(_Ho(_Il,_Ik-_Iv|0));}),_Im);});}};if(_Ij>_It){return new F(function(){return _Iu(_Ij);});}else{return new F(function(){return _Iu(_It);});}}},_Iz=new T(function(){return 0/0;}),_IA=new T(function(){return -1/0;}),_IB=new T(function(){return 1/0;}),_IC=function(_ID,_IE){if(!B(_r6(_IE,_ro))){if(!B(_r6(_ID,_ro))){if(!B(_FO(_ID,_ro))){return new F(function(){return _Ii(-1021,53,_ID,_IE);});}else{return  -B(_Ii(-1021,53,B(_vh(_ID)),_IE));}}else{return E(_rn);}}else{return (!B(_r6(_ID,_ro)))?(!B(_FO(_ID,_ro)))?E(_IB):E(_IA):E(_Iz);}},_IF=function(_IG){var _IH=E(_IG);switch(_IH._){case 3:var _II=_IH.a;return (!B(_sH(_II,_EP)))?(!B(_sH(_II,_EO)))?E(_H8):E(_EL):E(_EH);case 5:var _IJ=B(_GS(_ER,_EQ,_IH.a));if(!_IJ._){return E(_EH);}else{var _IK=new T(function(){var _IL=E(_IJ.a);return B(_IC(_IL.a,_IL.b));});return function(_IM,_IN){return new F(function(){return A1(_IN,_IK);});};}break;default:return E(_H8);}},_IO=function(_IP){var _IQ=function(_IR){return E(new T2(3,_IP,_td));};return new T1(1,function(_IS){return new F(function(){return A2(_C0,_IS,_IQ);});});},_IT=new T(function(){return B(A3(_El,_IF,_DQ,_IO));}),_IU=new T(function(){return B(_rT(_IT,_rR));}),_IV=function(_IW){while(1){var _IX=B((function(_IY){var _IZ=E(_IY);if(!_IZ._){return __Z;}else{var _J0=_IZ.b,_J1=E(_IZ.a);if(!E(_J1.b)._){return new T2(1,_J1.a,new T(function(){return B(_IV(_J0));}));}else{_IW=_J0;return __continue;}}})(_IW));if(_IX!=__continue){return _IX;}}},_J2=new T(function(){return B(_IV(_IU));}),_J3=new T(function(){return B(unCStr("Infinity"));}),_J4=new T(function(){return B(_rT(_IT,_J3));}),_J5=new T(function(){return B(_IV(_J4));}),_J6=0,_J7=function(_J8,_J9,_Ja){return new F(function(){return _fj(_ew,new T2(0,_J9,_Ja),_J8,_fo);});},_Jb=function(_Jc,_Jd,_Je){var _Jf=(_Jc+_Jd|0)-1|0;if(_Jc<=_Jf){var _Jg=function(_Jh){return new T2(1,new T(function(){var _Ji=E(_Je),_Jj=_Ji.c,_Jk=E(_Ji.a),_Jl=E(_Ji.b);if(_Jk>_Jh){return B(_J7(_Jh,_Jk,_Jl));}else{if(_Jh>_Jl){return B(_J7(_Jh,_Jk,_Jl));}else{var _Jm=_Jh-_Jk|0;if(0>_Jm){return B(_ef(_Jm,_Jj));}else{if(_Jm>=_Jj){return B(_ef(_Jm,_Jj));}else{return _Ji.d["v"]["w8"][_Jm];}}}}}),new T(function(){if(_Jh!=_Jf){return B(_Jg(_Jh+1|0));}else{return __Z;}}));};return new F(function(){return _Jg(_Jc);});}else{return __Z;}},_Jn=function(_Jo){var _Jp=E(_Jo);return new F(function(){return _Jb(_Jp.a,_Jp.b,_Jp.c);});},_Jq=function(_Jr,_Js,_Jt,_Ju){var _Jv=new T(function(){var _Jw=E(_Jr),_Jx=E(_Jt),_Jy=_Jx.a,_Jz=_Jx.b,_JA=_Jx.c,_JB=E(_Ju);if((_JB+_Jw|0)<=_Jz){return new T2(0,new T(function(){var _JC=_Jz-_JB|0;if(_Jw>_JC){return new T3(0,_Jy+_JB|0,_JC,_JA);}else{return new T3(0,_Jy+_JB|0,_Jw,_JA);}}),_JB+_Jw|0);}else{return E(_fU);}}),_JD=new T(function(){return B(A1(_Js,new T(function(){return B(_Jn(E(_Jv).a));})));}),_JE=new T(function(){var _JF=E(_JD),_JG=_JF.d,_JH=_JF.e,_JI=_JF.f,_JJ=E(_JF.c);if(!_JJ){if(!B(_r6(_JG,_rL))){var _JK=B(_rp(_py,Math.pow(2,E(_JH)-1|0))),_JL=_JK.a;if(E(_JK.b)>=0){return B(_r2(_JG,((1-E(_JL)|0)-E(_JI)|0)+1|0));}else{return B(_r2(_JG,((1-(E(_JL)-1|0)|0)-E(_JI)|0)+1|0));}}else{return E(_J6);}}else{var _JM=E(_JH);if(_JJ!=(B(_rF(_rQ,_JM))-1|0)){var _JN=B(_rp(_py,Math.pow(2,_JM-1|0))),_JO=_JN.a;if(E(_JN.b)>=0){var _JP=E(_JI);return B(_r2(B(_v7(_JG,B(_Ho(_rK,_JP)))),((_JJ+1|0)-E(_JO)|0)-_JP|0));}else{var _JQ=E(_JI);return B(_r2(B(_v7(_JG,B(_Ho(_rK,_JQ)))),((_JJ+1|0)-(E(_JO)-1|0)|0)-_JQ|0));}}else{if(!B(_r6(_JG,_rL))){var _JR=E(_J2);if(!_JR._){return E(_rN);}else{if(!E(_JR.b)._){return E(_JR.a);}else{return E(_rP);}}}else{var _JS=E(_J5);if(!_JS._){return E(_rN);}else{if(!E(_JS.b)._){return E(_JS.a);}else{return E(_rP);}}}}}});return new T2(0,new T(function(){if(!E(E(_JD).b)){return E(_JE);}else{return  -E(_JE);}}),new T(function(){return E(E(_Jv).b);}));},_JT=new T(function(){return B(unCStr("This file was compiled with different version of GF"));}),_JU=new T(function(){return B(err(_JT));}),_JV=8,_JW={_:0,a:_nq,b:_nl,c:_nh,d:_nh,e:_mL,f:_n6,g:_j6,h:_nd},_JX={_:0,a:_pb,b:_jh,c:_p8,d:_pm,e:_pe,f:_pr,g:_pk},_JY=new T2(0,_jn,_jq),_JZ={_:0,a:_JY,b:_jH,c:_jT,d:_jQ,e:_jN,f:_jK,g:_ju,h:_jz},_K0=new T3(0,_JX,_JZ,_p6),_K1={_:0,a:_K0,b:_JW,c:_oJ,d:_oX,e:_od,f:_oF,g:_oP,h:_oi,i:_p3},_K2=new T1(0,1),_K3=function(_K4,_K5){var _K6=E(_K4);return new T2(0,_K6,new T(function(){var _K7=B(_K3(B(_v7(_K6,_K5)),_K5));return new T2(1,_K7.a,_K7.b);}));},_K8=function(_K9){var _Ka=B(_K3(_K9,_K2));return new T2(1,_Ka.a,_Ka.b);},_Kb=function(_Kc,_Kd){var _Ke=B(_K3(_Kc,new T(function(){return B(_Ft(_Kd,_Kc));})));return new T2(1,_Ke.a,_Ke.b);},_Kf=new T1(0,0),_Kg=function(_Kh,_Ki,_Kj){if(!B(_Gf(_Ki,_Kf))){var _Kk=function(_Kl){return (!B(_FO(_Kl,_Kj)))?new T2(1,_Kl,new T(function(){return B(_Kk(B(_v7(_Kl,_Ki))));})):__Z;};return new F(function(){return _Kk(_Kh);});}else{var _Km=function(_Kn){return (!B(_GD(_Kn,_Kj)))?new T2(1,_Kn,new T(function(){return B(_Km(B(_v7(_Kn,_Ki))));})):__Z;};return new F(function(){return _Km(_Kh);});}},_Ko=function(_Kp,_Kq,_Kr){return new F(function(){return _Kg(_Kp,B(_Ft(_Kq,_Kp)),_Kr);});},_Ks=function(_Kt,_Ku){return new F(function(){return _Kg(_Kt,_K2,_Ku);});},_Kv=function(_Kw){return new F(function(){return _ph(_Kw);});},_Kx=function(_Ky){return new F(function(){return _Ft(_Ky,_K2);});},_Kz=function(_KA){return new F(function(){return _v7(_KA,_K2);});},_KB=function(_KC){return new F(function(){return _p1(E(_KC));});},_KD={_:0,a:_Kz,b:_Kx,c:_KB,d:_Kv,e:_K8,f:_Kb,g:_Ks,h:_Ko},_KE=function(_KF,_KG){while(1){var _KH=E(_KF);if(!_KH._){var _KI=E(_KH.a);if(_KI==(-2147483648)){_KF=new T1(1,I_fromInt(-2147483648));continue;}else{var _KJ=E(_KG);if(!_KJ._){return new T1(0,B(_nu(_KI,_KJ.a)));}else{_KF=new T1(1,I_fromInt(_KI));_KG=_KJ;continue;}}}else{var _KK=_KH.a,_KL=E(_KG);return (_KL._==0)?new T1(1,I_div(_KK,I_fromInt(_KL.a))):new T1(1,I_div(_KK,_KL.a));}}},_KM=function(_KN,_KO){if(!B(_r6(_KO,_qg))){return new F(function(){return _KE(_KN,_KO);});}else{return E(_o4);}},_KP=function(_KQ,_KR){while(1){var _KS=E(_KQ);if(!_KS._){var _KT=E(_KS.a);if(_KT==(-2147483648)){_KQ=new T1(1,I_fromInt(-2147483648));continue;}else{var _KU=E(_KR);if(!_KU._){var _KV=_KU.a;return new T2(0,new T1(0,B(_nu(_KT,_KV))),new T1(0,B(_oy(_KT,_KV))));}else{_KQ=new T1(1,I_fromInt(_KT));_KR=_KU;continue;}}}else{var _KW=E(_KR);if(!_KW._){_KQ=_KS;_KR=new T1(1,I_fromInt(_KW.a));continue;}else{var _KX=I_divMod(_KS.a,_KW.a);return new T2(0,new T1(1,_KX.a),new T1(1,_KX.b));}}}},_KY=function(_KZ,_L0){if(!B(_r6(_L0,_qg))){var _L1=B(_KP(_KZ,_L0));return new T2(0,_L1.a,_L1.b);}else{return E(_o4);}},_L2=function(_L3,_L4){while(1){var _L5=E(_L3);if(!_L5._){var _L6=E(_L5.a);if(_L6==(-2147483648)){_L3=new T1(1,I_fromInt(-2147483648));continue;}else{var _L7=E(_L4);if(!_L7._){return new T1(0,B(_oy(_L6,_L7.a)));}else{_L3=new T1(1,I_fromInt(_L6));_L4=_L7;continue;}}}else{var _L8=_L5.a,_L9=E(_L4);return (_L9._==0)?new T1(1,I_mod(_L8,I_fromInt(_L9.a))):new T1(1,I_mod(_L8,_L9.a));}}},_La=function(_Lb,_Lc){if(!B(_r6(_Lc,_qg))){return new F(function(){return _L2(_Lb,_Lc);});}else{return E(_o4);}},_Ld=function(_Le,_Lf){if(!B(_r6(_Lf,_qg))){return new F(function(){return _Fd(_Le,_Lf);});}else{return E(_o4);}},_Lg=function(_Lh,_Li){if(!B(_r6(_Li,_qg))){var _Lj=B(_re(_Lh,_Li));return new T2(0,_Lj.a,_Lj.b);}else{return E(_o4);}},_Lk=function(_Ll){return E(_Ll);},_Lm=function(_Ln){return E(_Ln);},_Lo={_:0,a:_v7,b:_Ft,c:_pI,d:_vh,e:_F8,f:_G2,g:_Lm},_Lp=function(_Lq,_Lr){var _Ls=E(_Lq);if(!_Ls._){var _Lt=_Ls.a,_Lu=E(_Lr);return (_Lu._==0)?_Lt!=_Lu.a:(I_compareInt(_Lu.a,_Lt)==0)?false:true;}else{var _Lv=_Ls.a,_Lw=E(_Lr);return (_Lw._==0)?(I_compareInt(_Lv,_Lw.a)==0)?false:true:(I_compare(_Lv,_Lw.a)==0)?false:true;}},_Lx=new T2(0,_r6,_Lp),_Ly=function(_Lz,_LA){return (!B(_wK(_Lz,_LA)))?E(_Lz):E(_LA);},_LB=function(_LC,_LD){return (!B(_wK(_LC,_LD)))?E(_LD):E(_LC);},_LE={_:0,a:_Lx,b:_Hc,c:_FO,d:_wK,e:_GD,f:_Gf,g:_Ly,h:_LB},_LF=function(_LG){return new T2(0,E(_LG),E(_p5));},_LH=new T3(0,_Lo,_LE,_LF),_LI={_:0,a:_LH,b:_KD,c:_Ld,d:_F0,e:_KM,f:_La,g:_Lg,h:_KY,i:_Lk},_LJ=function(_LK,_LL){while(1){var _LM=E(_LK);if(!_LM._){return E(_LL);}else{var _LN=B(_v7(B(_Ho(_LL,8)),B(_p1(E(_LM.a)&4294967295))));_LK=_LM.b;_LL=_LN;continue;}}},_LO=function(_LP,_LQ,_LR){var _LS=imul(B(_vm(_LP,0)),8)|0,_LT=B(_rp(_LI,Math.pow(2,_LS-_LQ|0))),_LU=_LT.a;return (E(_LT.b)>=0)?E(B(_Ie(B(_HY(B(_LJ(_LP,_rL)),B(_Ft(_LU,_rK)))),_LS-_LR|0)).a):E(B(_Ie(B(_HY(B(_LJ(_LP,_rL)),B(_Ft(B(_Ft(_LU,_rK)),_rK)))),_LS-_LR|0)).a);},_LV=new T(function(){return B(unCStr("head"));}),_LW=new T(function(){return B(_eE(_LV));}),_LX=function(_LY,_LZ,_M0){return new T1(1,B(_LO(_LY,E(_LZ),E(_M0))));},_M1=5,_M2=new T(function(){return B(unCStr("Invalid length of floating-point value"));}),_M3=new T(function(){return B(err(_M2));}),_M4=function(_M5){var _M6=new T(function(){return imul(B(_vm(_M5,0)),8)|0;}),_M7=new T(function(){var _M8=E(_M6);switch(_M8){case 16:return E(_M1);break;case 32:return E(_JV);break;default:if(!B(_oy(_M8,32))){var _M9=B(_rp(_K1,4*(Math.log(_M8)/Math.log(2)))),_Ma=_M9.a;if(E(_M9.b)<=0){return E(_Ma)-13|0;}else{return (E(_Ma)+1|0)-13|0;}}else{return E(_M3);}}}),_Mb=new T(function(){return 1+E(_M7)|0;});return new T6(0,new T(function(){return B(_vm(_M5,0));}),new T(function(){var _Mc=E(_M5);if(!_Mc._){return E(_LW);}else{if((E(_Mc.a)&128)>>>0==128){return 1;}else{return 0;}}}),new T(function(){return B(_ph(new T1(1,B(_LO(_M5,1,E(_Mb))))));}),new T(function(){return B(_LX(_M5,_Mb,_M6));}),_M7,new T(function(){return B(_jh(_M6,_Mb));}));},_Md=function(_Me){var _Mf=B(_M4(_Me));return new T6(0,_Mf.a,_Mf.b,_Mf.c,_Mf.d,_Mf.e,_Mf.f);},_Mg=function(_Mh,_Mi,_Mj,_Mk){var _Ml=B(_fE(_Mh,_Mi,_Mj,_Mk)),_Mm=_Ml.b;switch(E(_Ml.a)){case 0:var _Mn=B(_fK(_Mh,_Mi,_Mj,E(_Mm))),_Mo=B(_gH(E(_Mn.a)&4294967295,_gv,new T3(0,_Mh,_Mi,_Mj),_Mn.b));return new T2(0,new T1(0,_Mo.a),_Mo.b);case 1:var _Mp=B(_fK(_Mh,_Mi,_Mj,E(_Mm)));return new T2(0,new T1(1,new T(function(){return E(_Mp.a)&4294967295;})),_Mp.b);case 2:var _Mq=B(_Jq(_JV,_Md,new T3(0,_Mh,_Mi,_Mj),_Mm));return new T2(0,new T1(2,_Mq.a),_Mq.b);default:return E(_JU);}},_Mr=function(_Ms,_Mt){var _Mu=E(_Ms),_Mv=B(_Mg(_Mu.a,_Mu.b,_Mu.c,E(_Mt)));return new T2(0,_Mv.a,_Mv.b);},_Mw=function(_Mx){switch(E(_Mx)._){case 0:return E(_eb);case 1:return E(_eb);default:return E(_eb);}},_My=new T2(0,_Mw,_Mr),_Mz=function(_MA){return E(_eb);},_MB=-4,_MC=function(_MD){var _ME=E(_MD);return (_ME._==0)?__Z:new T2(1,new T2(0,_MB,_ME.a),new T(function(){return B(_MC(_ME.b));}));},_MF=function(_MG,_MH,_MI,_MJ){var _MK=B(_fK(_MG,_MH,_MI,_MJ)),_ML=B(_gH(E(_MK.a)&4294967295,_kR,new T3(0,_MG,_MH,_MI),_MK.b)),_MM=B(_fK(_MG,_MH,_MI,E(_ML.b))),_MN=new T(function(){return new T2(0,new T(function(){return B(_MC(_ML.a));}),E(_MM.a)&4294967295);});return new T2(0,_MN,_MM.b);},_MO=function(_MP,_MQ){var _MR=E(_MP),_MS=B(_MF(_MR.a,_MR.b,_MR.c,E(_MQ)));return new T2(0,_MS.a,_MS.b);},_MT=function(_MU,_MV,_MW,_MX){var _MY=B(_fE(_MU,_MV,_MW,_MX)),_MZ=_MY.b;switch(E(_MY.a)){case 0:var _N0=B(_fK(_MU,_MV,_MW,E(_MZ))),_N1=B(_fK(_MU,_MV,_MW,E(_N0.b))),_N2=B(_gH(E(_N1.a)&4294967295,_MO,new T3(0,_MU,_MV,_MW),_N1.b));return new T2(0,new T(function(){return new T2(0,E(_N0.a)&4294967295,_N2.a);}),_N2.b);case 1:var _N3=B(_fK(_MU,_MV,_MW,E(_MZ)));return new T2(0,new T(function(){return new T1(1,E(_N3.a)&4294967295);}),_N3.b);default:return E(_JU);}},_N4=function(_N5,_N6){var _N7=E(_N5),_N8=B(_MT(_N7.a,_N7.b,_N7.c,E(_N6)));return new T2(0,_N8.a,_N8.b);},_N9=new T(function(){return B(_7f("pgf/PGF/Binary.hs:(243,3)-(244,51)|function put"));}),_Na=function(_Nb){switch(E(_Nb)._){case 0:return E(_eb);case 1:return E(_eb);default:return E(_N9);}},_Nc=new T2(0,_Na,_N4),_Nd=new T0(1),_Ne=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_Nf=function(_Ng){return new F(function(){return err(_Ne);});},_Nh=new T(function(){return B(_Nf(_));}),_Ni=function(_Nj,_Nk,_Nl){var _Nm=E(_Nl);if(!_Nm._){var _Nn=_Nm.a,_No=E(_Nk);if(!_No._){var _Np=_No.a,_Nq=_No.b;if(_Np<=(imul(3,_Nn)|0)){return new T4(0,(1+_Np|0)+_Nn|0,E(_Nj),E(_No),E(_Nm));}else{var _Nr=E(_No.c);if(!_Nr._){var _Ns=_Nr.a,_Nt=E(_No.d);if(!_Nt._){var _Nu=_Nt.a,_Nv=_Nt.b,_Nw=_Nt.c;if(_Nu>=(imul(2,_Ns)|0)){var _Nx=function(_Ny){var _Nz=E(_Nt.d);return (_Nz._==0)?new T4(0,(1+_Np|0)+_Nn|0,E(_Nv),E(new T4(0,(1+_Ns|0)+_Ny|0,E(_Nq),E(_Nr),E(_Nw))),E(new T4(0,(1+_Nn|0)+_Nz.a|0,E(_Nj),E(_Nz),E(_Nm)))):new T4(0,(1+_Np|0)+_Nn|0,E(_Nv),E(new T4(0,(1+_Ns|0)+_Ny|0,E(_Nq),E(_Nr),E(_Nw))),E(new T4(0,1+_Nn|0,E(_Nj),E(_Nd),E(_Nm))));},_NA=E(_Nw);if(!_NA._){return new F(function(){return _Nx(_NA.a);});}else{return new F(function(){return _Nx(0);});}}else{return new T4(0,(1+_Np|0)+_Nn|0,E(_Nq),E(_Nr),E(new T4(0,(1+_Nn|0)+_Nu|0,E(_Nj),E(_Nt),E(_Nm))));}}else{return E(_Nh);}}else{return E(_Nh);}}}else{return new T4(0,1+_Nn|0,E(_Nj),E(_Nd),E(_Nm));}}else{var _NB=E(_Nk);if(!_NB._){var _NC=_NB.a,_ND=_NB.b,_NE=_NB.d,_NF=E(_NB.c);if(!_NF._){var _NG=_NF.a,_NH=E(_NE);if(!_NH._){var _NI=_NH.a,_NJ=_NH.b,_NK=_NH.c;if(_NI>=(imul(2,_NG)|0)){var _NL=function(_NM){var _NN=E(_NH.d);return (_NN._==0)?new T4(0,1+_NC|0,E(_NJ),E(new T4(0,(1+_NG|0)+_NM|0,E(_ND),E(_NF),E(_NK))),E(new T4(0,1+_NN.a|0,E(_Nj),E(_NN),E(_Nd)))):new T4(0,1+_NC|0,E(_NJ),E(new T4(0,(1+_NG|0)+_NM|0,E(_ND),E(_NF),E(_NK))),E(new T4(0,1,E(_Nj),E(_Nd),E(_Nd))));},_NO=E(_NK);if(!_NO._){return new F(function(){return _NL(_NO.a);});}else{return new F(function(){return _NL(0);});}}else{return new T4(0,1+_NC|0,E(_ND),E(_NF),E(new T4(0,1+_NI|0,E(_Nj),E(_NH),E(_Nd))));}}else{return new T4(0,3,E(_ND),E(_NF),E(new T4(0,1,E(_Nj),E(_Nd),E(_Nd))));}}else{var _NP=E(_NE);return (_NP._==0)?new T4(0,3,E(_NP.b),E(new T4(0,1,E(_ND),E(_Nd),E(_Nd))),E(new T4(0,1,E(_Nj),E(_Nd),E(_Nd)))):new T4(0,2,E(_Nj),E(_NB),E(_Nd));}}else{return new T4(0,1,E(_Nj),E(_Nd),E(_Nd));}}},_NQ=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_NR=function(_NS){return new F(function(){return err(_NQ);});},_NT=new T(function(){return B(_NR(_));}),_NU=function(_NV,_NW,_NX){var _NY=E(_NW);if(!_NY._){var _NZ=_NY.a,_O0=E(_NX);if(!_O0._){var _O1=_O0.a,_O2=_O0.b;if(_O1<=(imul(3,_NZ)|0)){return new T4(0,(1+_NZ|0)+_O1|0,E(_NV),E(_NY),E(_O0));}else{var _O3=E(_O0.c);if(!_O3._){var _O4=_O3.a,_O5=_O3.b,_O6=_O3.c,_O7=E(_O0.d);if(!_O7._){var _O8=_O7.a;if(_O4>=(imul(2,_O8)|0)){var _O9=function(_Oa){var _Ob=E(_NV),_Oc=E(_O3.d);return (_Oc._==0)?new T4(0,(1+_NZ|0)+_O1|0,E(_O5),E(new T4(0,(1+_NZ|0)+_Oa|0,E(_Ob),E(_NY),E(_O6))),E(new T4(0,(1+_O8|0)+_Oc.a|0,E(_O2),E(_Oc),E(_O7)))):new T4(0,(1+_NZ|0)+_O1|0,E(_O5),E(new T4(0,(1+_NZ|0)+_Oa|0,E(_Ob),E(_NY),E(_O6))),E(new T4(0,1+_O8|0,E(_O2),E(_Nd),E(_O7))));},_Od=E(_O6);if(!_Od._){return new F(function(){return _O9(_Od.a);});}else{return new F(function(){return _O9(0);});}}else{return new T4(0,(1+_NZ|0)+_O1|0,E(_O2),E(new T4(0,(1+_NZ|0)+_O4|0,E(_NV),E(_NY),E(_O3))),E(_O7));}}else{return E(_NT);}}else{return E(_NT);}}}else{return new T4(0,1+_NZ|0,E(_NV),E(_NY),E(_Nd));}}else{var _Oe=E(_NX);if(!_Oe._){var _Of=_Oe.a,_Og=_Oe.b,_Oh=_Oe.d,_Oi=E(_Oe.c);if(!_Oi._){var _Oj=_Oi.a,_Ok=_Oi.b,_Ol=_Oi.c,_Om=E(_Oh);if(!_Om._){var _On=_Om.a;if(_Oj>=(imul(2,_On)|0)){var _Oo=function(_Op){var _Oq=E(_NV),_Or=E(_Oi.d);return (_Or._==0)?new T4(0,1+_Of|0,E(_Ok),E(new T4(0,1+_Op|0,E(_Oq),E(_Nd),E(_Ol))),E(new T4(0,(1+_On|0)+_Or.a|0,E(_Og),E(_Or),E(_Om)))):new T4(0,1+_Of|0,E(_Ok),E(new T4(0,1+_Op|0,E(_Oq),E(_Nd),E(_Ol))),E(new T4(0,1+_On|0,E(_Og),E(_Nd),E(_Om))));},_Os=E(_Ol);if(!_Os._){return new F(function(){return _Oo(_Os.a);});}else{return new F(function(){return _Oo(0);});}}else{return new T4(0,1+_Of|0,E(_Og),E(new T4(0,1+_Oj|0,E(_NV),E(_Nd),E(_Oi))),E(_Om));}}else{return new T4(0,3,E(_Ok),E(new T4(0,1,E(_NV),E(_Nd),E(_Nd))),E(new T4(0,1,E(_Og),E(_Nd),E(_Nd))));}}else{var _Ot=E(_Oh);return (_Ot._==0)?new T4(0,3,E(_Og),E(new T4(0,1,E(_NV),E(_Nd),E(_Nd))),E(_Ot)):new T4(0,2,E(_NV),E(_Nd),E(_Oe));}}else{return new T4(0,1,E(_NV),E(_Nd),E(_Nd));}}},_Ou=function(_Ov){return new T4(0,1,E(_Ov),E(_Nd),E(_Nd));},_Ow=function(_Ox,_Oy){var _Oz=E(_Oy);if(!_Oz._){return new F(function(){return _Ni(_Oz.b,B(_Ow(_Ox,_Oz.c)),_Oz.d);});}else{return new F(function(){return _Ou(_Ox);});}},_OA=function(_OB,_OC){var _OD=E(_OC);if(!_OD._){return new F(function(){return _NU(_OD.b,_OD.c,B(_OA(_OB,_OD.d)));});}else{return new F(function(){return _Ou(_OB);});}},_OE=function(_OF,_OG,_OH,_OI,_OJ){return new F(function(){return _NU(_OH,_OI,B(_OA(_OF,_OJ)));});},_OK=function(_OL,_OM,_ON,_OO,_OP){return new F(function(){return _Ni(_ON,B(_Ow(_OL,_OO)),_OP);});},_OQ=function(_OR,_OS,_OT,_OU,_OV,_OW){var _OX=E(_OS);if(!_OX._){var _OY=_OX.a,_OZ=_OX.b,_P0=_OX.c,_P1=_OX.d;if((imul(3,_OY)|0)>=_OT){if((imul(3,_OT)|0)>=_OY){return new T4(0,(_OY+_OT|0)+1|0,E(_OR),E(_OX),E(new T4(0,_OT,E(_OU),E(_OV),E(_OW))));}else{return new F(function(){return _NU(_OZ,_P0,B(_OQ(_OR,_P1,_OT,_OU,_OV,_OW)));});}}else{return new F(function(){return _Ni(_OU,B(_P2(_OR,_OY,_OZ,_P0,_P1,_OV)),_OW);});}}else{return new F(function(){return _OK(_OR,_OT,_OU,_OV,_OW);});}},_P2=function(_P3,_P4,_P5,_P6,_P7,_P8){var _P9=E(_P8);if(!_P9._){var _Pa=_P9.a,_Pb=_P9.b,_Pc=_P9.c,_Pd=_P9.d;if((imul(3,_P4)|0)>=_Pa){if((imul(3,_Pa)|0)>=_P4){return new T4(0,(_P4+_Pa|0)+1|0,E(_P3),E(new T4(0,_P4,E(_P5),E(_P6),E(_P7))),E(_P9));}else{return new F(function(){return _NU(_P5,_P6,B(_OQ(_P3,_P7,_Pa,_Pb,_Pc,_Pd)));});}}else{return new F(function(){return _Ni(_Pb,B(_P2(_P3,_P4,_P5,_P6,_P7,_Pc)),_Pd);});}}else{return new F(function(){return _OE(_P3,_P4,_P5,_P6,_P7);});}},_Pe=function(_Pf,_Pg,_Ph){var _Pi=E(_Pg);if(!_Pi._){var _Pj=_Pi.a,_Pk=_Pi.b,_Pl=_Pi.c,_Pm=_Pi.d,_Pn=E(_Ph);if(!_Pn._){var _Po=_Pn.a,_Pp=_Pn.b,_Pq=_Pn.c,_Pr=_Pn.d;if((imul(3,_Pj)|0)>=_Po){if((imul(3,_Po)|0)>=_Pj){return new T4(0,(_Pj+_Po|0)+1|0,E(_Pf),E(_Pi),E(_Pn));}else{return new F(function(){return _NU(_Pk,_Pl,B(_OQ(_Pf,_Pm,_Po,_Pp,_Pq,_Pr)));});}}else{return new F(function(){return _Ni(_Pp,B(_P2(_Pf,_Pj,_Pk,_Pl,_Pm,_Pq)),_Pr);});}}else{return new F(function(){return _OE(_Pf,_Pj,_Pk,_Pl,_Pm);});}}else{return new F(function(){return _Ow(_Pf,_Ph);});}},_Ps=function(_Pt,_Pu,_Pv){var _Pw=E(_Pt);if(_Pw==1){return new T2(0,new T(function(){return new T4(0,1,E(_Pu),E(_Nd),E(_Nd));}),_Pv);}else{var _Px=B(_Ps(_Pw>>1,_Pu,_Pv)),_Py=_Px.a,_Pz=E(_Px.b);if(!_Pz._){return new T2(0,_Py,_4);}else{var _PA=B(_PB(_Pw>>1,_Pz.b));return new T2(0,new T(function(){return B(_Pe(_Pz.a,_Py,_PA.a));}),_PA.b);}}},_PB=function(_PC,_PD){var _PE=E(_PD);if(!_PE._){return new T2(0,_Nd,_4);}else{var _PF=_PE.a,_PG=_PE.b,_PH=E(_PC);if(_PH==1){return new T2(0,new T(function(){return new T4(0,1,E(_PF),E(_Nd),E(_Nd));}),_PG);}else{var _PI=B(_Ps(_PH>>1,_PF,_PG)),_PJ=_PI.a,_PK=E(_PI.b);if(!_PK._){return new T2(0,_PJ,_4);}else{var _PL=B(_PB(_PH>>1,_PK.b));return new T2(0,new T(function(){return B(_Pe(_PK.a,_PJ,_PL.a));}),_PL.b);}}}},_PM=function(_PN,_PO,_PP){while(1){var _PQ=E(_PP);if(!_PQ._){return E(_PO);}else{var _PR=B(_PB(_PN,_PQ.b)),_PS=_PN<<1,_PT=B(_Pe(_PQ.a,_PO,_PR.a));_PN=_PS;_PO=_PT;_PP=_PR.b;continue;}}},_PU=function(_PV,_PW,_PX,_PY,_PZ){var _Q0=B(_fK(_PW,_PX,_PY,_PZ)),_Q1=B(_gH(E(_Q0.a)&4294967295,new T(function(){return B(_kd(_PV));}),new T3(0,_PW,_PX,_PY),_Q0.b));return new T2(0,new T(function(){var _Q2=E(_Q1.a);if(!_Q2._){return new T0(1);}else{return B(_PM(1,new T4(0,1,E(_Q2.a),E(_Nd),E(_Nd)),_Q2.b));}}),_Q1.b);},_Q3=function(_Q4,_Q5){var _Q6=E(_Q4),_Q7=B(_PU(_Nc,_Q6.a,_Q6.b,_Q6.c,E(_Q5)));return new T2(0,_Q7.a,_Q7.b);},_Q8=new T2(0,_Mz,_Q3),_Q9=function(_Qa){return E(_eb);},_Qb=function(_Qc,_Qd,_Qe,_Qf){var _Qg=B(_fK(_Qc,_Qd,_Qe,_Qf));return new F(function(){return _gH(E(_Qg.a)&4294967295,_kR,new T3(0,_Qc,_Qd,_Qe),_Qg.b);});},_Qh=function(_Qi,_Qj){var _Qk=E(_Qi),_Ql=B(_Qb(_Qk.a,_Qk.b,_Qk.c,E(_Qj)));return new T2(0,_Ql.a,_Ql.b);},_Qm=new T2(0,_Q9,_Qh),_Qn=new T0(1),_Qo=function(_Qp,_Qq,_Qr,_Qs,_Qt,_Qu,_Qv){while(1){var _Qw=E(_Qv);if(!_Qw._){var _Qx=(_Qt>>>0^_Qw.a>>>0)>>>0,_Qy=(_Qx|_Qx>>>1)>>>0,_Qz=(_Qy|_Qy>>>2)>>>0,_QA=(_Qz|_Qz>>>4)>>>0,_QB=(_QA|_QA>>>8)>>>0,_QC=(_QB|_QB>>>16)>>>0,_QD=(_QC^_QC>>>1)>>>0&4294967295;if(_Qs>>>0<=_QD>>>0){return new F(function(){return _QE(_Qp,_Qq,_Qr,new T3(0,_Qt,E(_Qu),E(_Qw)));});}else{var _QF=_QD>>>0,_QG=(_Qt>>>0&((_QF-1>>>0^4294967295)>>>0^_QF)>>>0)>>>0&4294967295,_QH=new T4(0,_QG,_QD,E(_Qw.b),E(_Qu));_Qt=_QG;_Qu=_QH;_Qv=_Qw.c;continue;}}else{return new F(function(){return _QE(_Qp,_Qq,_Qr,new T3(0,_Qt,E(_Qu),E(_Qn)));});}}},_QI=function(_QJ,_QK,_QL){while(1){var _QM=E(_QL);if(!_QM._){var _QN=_QM.a,_QO=_QM.b,_QP=_QM.c,_QQ=(_QN>>>0^_QJ>>>0)>>>0,_QR=(_QQ|_QQ>>>1)>>>0,_QS=(_QR|_QR>>>2)>>>0,_QT=(_QS|_QS>>>4)>>>0,_QU=(_QT|_QT>>>8)>>>0,_QV=(_QU|_QU>>>16)>>>0,_QW=(_QV^_QV>>>1)>>>0&4294967295,_QX=(_QJ>>>0^_QN>>>0)>>>0,_QY=(_QX|_QX>>>1)>>>0,_QZ=(_QY|_QY>>>2)>>>0,_R0=(_QZ|_QZ>>>4)>>>0,_R1=(_R0|_R0>>>8)>>>0,_R2=(_R1|_R1>>>16)>>>0,_R3=(_R2^_R2>>>1)>>>0;if(!((_QN>>>0&_QW>>>0)>>>0)){var _R4=_QW>>>0,_R5=(_QJ>>>0&((_R3-1>>>0^4294967295)>>>0^_R3)>>>0)>>>0&4294967295,_R6=new T4(0,(_QN>>>0&((_R4-1>>>0^4294967295)>>>0^_R4)>>>0)>>>0&4294967295,_QW,E(_QO),E(_QK));_QJ=_R5;_QK=_R6;_QL=_QP;continue;}else{var _R7=_QW>>>0,_R5=(_QJ>>>0&((_R3-1>>>0^4294967295)>>>0^_R3)>>>0)>>>0&4294967295,_R6=new T4(0,(_QN>>>0&((_R7-1>>>0^4294967295)>>>0^_R7)>>>0)>>>0&4294967295,_QW,E(_QK),E(_QO));_QJ=_R5;_QK=_R6;_QL=_QP;continue;}}else{return E(_QK);}}},_QE=function(_R8,_R9,_Ra,_Rb){var _Rc=E(_Ra);if(!_Rc._){return new F(function(){return _QI(_R8,new T2(1,_R8,_R9),_Rb);});}else{var _Rd=E(_Rc.a),_Re=E(_Rd.a),_Rf=(_R8>>>0^_Re>>>0)>>>0,_Rg=(_Rf|_Rf>>>1)>>>0,_Rh=(_Rg|_Rg>>>2)>>>0,_Ri=(_Rh|_Rh>>>4)>>>0,_Rj=(_Ri|_Ri>>>8)>>>0,_Rk=(_Rj|_Rj>>>16)>>>0;return new F(function(){return _Qo(_Re,_Rd.b,_Rc.b,(_Rk^_Rk>>>1)>>>0&4294967295,_R8,new T2(1,_R8,_R9),_Rb);});}},_Rl=function(_Rm,_Rn,_Ro,_Rp,_Rq){var _Rr=B(_fK(_Rn,_Ro,_Rp,_Rq)),_Rs=function(_Rt,_Ru){var _Rv=E(_Rt),_Rw=B(_fK(_Rv.a,_Rv.b,_Rv.c,E(_Ru))),_Rx=B(A3(_kd,_Rm,_Rv,_Rw.b));return new T2(0,new T2(0,new T(function(){return E(_Rw.a)&4294967295;}),_Rx.a),_Rx.b);},_Ry=B(_gH(E(_Rr.a)&4294967295,_Rs,new T3(0,_Rn,_Ro,_Rp),_Rr.b));return new T2(0,new T(function(){var _Rz=E(_Ry.a);if(!_Rz._){return new T0(2);}else{var _RA=E(_Rz.a);return B(_QE(E(_RA.a),_RA.b,_Rz.b,_Qn));}}),_Ry.b);},_RB=function(_RC,_RD,_RE,_RF){var _RG=B(A3(_kd,_RC,_RE,_RF)),_RH=B(A3(_kd,_RD,_RE,_RG.b));return new T2(0,new T2(0,_RG.a,_RH.a),_RH.b);},_RI=new T0(1),_RJ=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_RK=function(_RL){return new F(function(){return err(_RJ);});},_RM=new T(function(){return B(_RK(_));}),_RN=function(_RO,_RP,_RQ,_RR){var _RS=E(_RR);if(!_RS._){var _RT=_RS.a,_RU=E(_RQ);if(!_RU._){var _RV=_RU.a,_RW=_RU.b,_RX=_RU.c;if(_RV<=(imul(3,_RT)|0)){return new T5(0,(1+_RV|0)+_RT|0,E(_RO),_RP,E(_RU),E(_RS));}else{var _RY=E(_RU.d);if(!_RY._){var _RZ=_RY.a,_S0=E(_RU.e);if(!_S0._){var _S1=_S0.a,_S2=_S0.b,_S3=_S0.c,_S4=_S0.d;if(_S1>=(imul(2,_RZ)|0)){var _S5=function(_S6){var _S7=E(_S0.e);return (_S7._==0)?new T5(0,(1+_RV|0)+_RT|0,E(_S2),_S3,E(new T5(0,(1+_RZ|0)+_S6|0,E(_RW),_RX,E(_RY),E(_S4))),E(new T5(0,(1+_RT|0)+_S7.a|0,E(_RO),_RP,E(_S7),E(_RS)))):new T5(0,(1+_RV|0)+_RT|0,E(_S2),_S3,E(new T5(0,(1+_RZ|0)+_S6|0,E(_RW),_RX,E(_RY),E(_S4))),E(new T5(0,1+_RT|0,E(_RO),_RP,E(_RI),E(_RS))));},_S8=E(_S4);if(!_S8._){return new F(function(){return _S5(_S8.a);});}else{return new F(function(){return _S5(0);});}}else{return new T5(0,(1+_RV|0)+_RT|0,E(_RW),_RX,E(_RY),E(new T5(0,(1+_RT|0)+_S1|0,E(_RO),_RP,E(_S0),E(_RS))));}}else{return E(_RM);}}else{return E(_RM);}}}else{return new T5(0,1+_RT|0,E(_RO),_RP,E(_RI),E(_RS));}}else{var _S9=E(_RQ);if(!_S9._){var _Sa=_S9.a,_Sb=_S9.b,_Sc=_S9.c,_Sd=_S9.e,_Se=E(_S9.d);if(!_Se._){var _Sf=_Se.a,_Sg=E(_Sd);if(!_Sg._){var _Sh=_Sg.a,_Si=_Sg.b,_Sj=_Sg.c,_Sk=_Sg.d;if(_Sh>=(imul(2,_Sf)|0)){var _Sl=function(_Sm){var _Sn=E(_Sg.e);return (_Sn._==0)?new T5(0,1+_Sa|0,E(_Si),_Sj,E(new T5(0,(1+_Sf|0)+_Sm|0,E(_Sb),_Sc,E(_Se),E(_Sk))),E(new T5(0,1+_Sn.a|0,E(_RO),_RP,E(_Sn),E(_RI)))):new T5(0,1+_Sa|0,E(_Si),_Sj,E(new T5(0,(1+_Sf|0)+_Sm|0,E(_Sb),_Sc,E(_Se),E(_Sk))),E(new T5(0,1,E(_RO),_RP,E(_RI),E(_RI))));},_So=E(_Sk);if(!_So._){return new F(function(){return _Sl(_So.a);});}else{return new F(function(){return _Sl(0);});}}else{return new T5(0,1+_Sa|0,E(_Sb),_Sc,E(_Se),E(new T5(0,1+_Sh|0,E(_RO),_RP,E(_Sg),E(_RI))));}}else{return new T5(0,3,E(_Sb),_Sc,E(_Se),E(new T5(0,1,E(_RO),_RP,E(_RI),E(_RI))));}}else{var _Sp=E(_Sd);return (_Sp._==0)?new T5(0,3,E(_Sp.b),_Sp.c,E(new T5(0,1,E(_Sb),_Sc,E(_RI),E(_RI))),E(new T5(0,1,E(_RO),_RP,E(_RI),E(_RI)))):new T5(0,2,E(_RO),_RP,E(_S9),E(_RI));}}else{return new T5(0,1,E(_RO),_RP,E(_RI),E(_RI));}}},_Sq=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_Sr=function(_Ss){return new F(function(){return err(_Sq);});},_St=new T(function(){return B(_Sr(_));}),_Su=function(_Sv,_Sw,_Sx,_Sy){var _Sz=E(_Sx);if(!_Sz._){var _SA=_Sz.a,_SB=E(_Sy);if(!_SB._){var _SC=_SB.a,_SD=_SB.b,_SE=_SB.c;if(_SC<=(imul(3,_SA)|0)){return new T5(0,(1+_SA|0)+_SC|0,E(_Sv),_Sw,E(_Sz),E(_SB));}else{var _SF=E(_SB.d);if(!_SF._){var _SG=_SF.a,_SH=_SF.b,_SI=_SF.c,_SJ=_SF.d,_SK=E(_SB.e);if(!_SK._){var _SL=_SK.a;if(_SG>=(imul(2,_SL)|0)){var _SM=function(_SN){var _SO=E(_Sv),_SP=E(_SF.e);return (_SP._==0)?new T5(0,(1+_SA|0)+_SC|0,E(_SH),_SI,E(new T5(0,(1+_SA|0)+_SN|0,E(_SO),_Sw,E(_Sz),E(_SJ))),E(new T5(0,(1+_SL|0)+_SP.a|0,E(_SD),_SE,E(_SP),E(_SK)))):new T5(0,(1+_SA|0)+_SC|0,E(_SH),_SI,E(new T5(0,(1+_SA|0)+_SN|0,E(_SO),_Sw,E(_Sz),E(_SJ))),E(new T5(0,1+_SL|0,E(_SD),_SE,E(_RI),E(_SK))));},_SQ=E(_SJ);if(!_SQ._){return new F(function(){return _SM(_SQ.a);});}else{return new F(function(){return _SM(0);});}}else{return new T5(0,(1+_SA|0)+_SC|0,E(_SD),_SE,E(new T5(0,(1+_SA|0)+_SG|0,E(_Sv),_Sw,E(_Sz),E(_SF))),E(_SK));}}else{return E(_St);}}else{return E(_St);}}}else{return new T5(0,1+_SA|0,E(_Sv),_Sw,E(_Sz),E(_RI));}}else{var _SR=E(_Sy);if(!_SR._){var _SS=_SR.a,_ST=_SR.b,_SU=_SR.c,_SV=_SR.e,_SW=E(_SR.d);if(!_SW._){var _SX=_SW.a,_SY=_SW.b,_SZ=_SW.c,_T0=_SW.d,_T1=E(_SV);if(!_T1._){var _T2=_T1.a;if(_SX>=(imul(2,_T2)|0)){var _T3=function(_T4){var _T5=E(_Sv),_T6=E(_SW.e);return (_T6._==0)?new T5(0,1+_SS|0,E(_SY),_SZ,E(new T5(0,1+_T4|0,E(_T5),_Sw,E(_RI),E(_T0))),E(new T5(0,(1+_T2|0)+_T6.a|0,E(_ST),_SU,E(_T6),E(_T1)))):new T5(0,1+_SS|0,E(_SY),_SZ,E(new T5(0,1+_T4|0,E(_T5),_Sw,E(_RI),E(_T0))),E(new T5(0,1+_T2|0,E(_ST),_SU,E(_RI),E(_T1))));},_T7=E(_T0);if(!_T7._){return new F(function(){return _T3(_T7.a);});}else{return new F(function(){return _T3(0);});}}else{return new T5(0,1+_SS|0,E(_ST),_SU,E(new T5(0,1+_SX|0,E(_Sv),_Sw,E(_RI),E(_SW))),E(_T1));}}else{return new T5(0,3,E(_SY),_SZ,E(new T5(0,1,E(_Sv),_Sw,E(_RI),E(_RI))),E(new T5(0,1,E(_ST),_SU,E(_RI),E(_RI))));}}else{var _T8=E(_SV);return (_T8._==0)?new T5(0,3,E(_ST),_SU,E(new T5(0,1,E(_Sv),_Sw,E(_RI),E(_RI))),E(_T8)):new T5(0,2,E(_Sv),_Sw,E(_RI),E(_SR));}}else{return new T5(0,1,E(_Sv),_Sw,E(_RI),E(_RI));}}},_T9=function(_Ta,_Tb){return new T5(0,1,E(_Ta),_Tb,E(_RI),E(_RI));},_Tc=function(_Td,_Te,_Tf){var _Tg=E(_Tf);if(!_Tg._){return new F(function(){return _Su(_Tg.b,_Tg.c,_Tg.d,B(_Tc(_Td,_Te,_Tg.e)));});}else{return new F(function(){return _T9(_Td,_Te);});}},_Th=function(_Ti,_Tj,_Tk){var _Tl=E(_Tk);if(!_Tl._){return new F(function(){return _RN(_Tl.b,_Tl.c,B(_Th(_Ti,_Tj,_Tl.d)),_Tl.e);});}else{return new F(function(){return _T9(_Ti,_Tj);});}},_Tm=function(_Tn,_To,_Tp,_Tq,_Tr,_Ts,_Tt){return new F(function(){return _RN(_Tq,_Tr,B(_Th(_Tn,_To,_Ts)),_Tt);});},_Tu=function(_Tv,_Tw,_Tx,_Ty,_Tz,_TA,_TB,_TC){var _TD=E(_Tx);if(!_TD._){var _TE=_TD.a,_TF=_TD.b,_TG=_TD.c,_TH=_TD.d,_TI=_TD.e;if((imul(3,_TE)|0)>=_Ty){if((imul(3,_Ty)|0)>=_TE){return new T5(0,(_TE+_Ty|0)+1|0,E(_Tv),_Tw,E(_TD),E(new T5(0,_Ty,E(_Tz),_TA,E(_TB),E(_TC))));}else{return new F(function(){return _Su(_TF,_TG,_TH,B(_Tu(_Tv,_Tw,_TI,_Ty,_Tz,_TA,_TB,_TC)));});}}else{return new F(function(){return _RN(_Tz,_TA,B(_TJ(_Tv,_Tw,_TE,_TF,_TG,_TH,_TI,_TB)),_TC);});}}else{return new F(function(){return _Tm(_Tv,_Tw,_Ty,_Tz,_TA,_TB,_TC);});}},_TJ=function(_TK,_TL,_TM,_TN,_TO,_TP,_TQ,_TR){var _TS=E(_TR);if(!_TS._){var _TT=_TS.a,_TU=_TS.b,_TV=_TS.c,_TW=_TS.d,_TX=_TS.e;if((imul(3,_TM)|0)>=_TT){if((imul(3,_TT)|0)>=_TM){return new T5(0,(_TM+_TT|0)+1|0,E(_TK),_TL,E(new T5(0,_TM,E(_TN),_TO,E(_TP),E(_TQ))),E(_TS));}else{return new F(function(){return _Su(_TN,_TO,_TP,B(_Tu(_TK,_TL,_TQ,_TT,_TU,_TV,_TW,_TX)));});}}else{return new F(function(){return _RN(_TU,_TV,B(_TJ(_TK,_TL,_TM,_TN,_TO,_TP,_TQ,_TW)),_TX);});}}else{return new F(function(){return _Tc(_TK,_TL,new T5(0,_TM,E(_TN),_TO,E(_TP),E(_TQ)));});}},_TY=function(_TZ,_U0,_U1,_U2){var _U3=E(_U1);if(!_U3._){var _U4=_U3.a,_U5=_U3.b,_U6=_U3.c,_U7=_U3.d,_U8=_U3.e,_U9=E(_U2);if(!_U9._){var _Ua=_U9.a,_Ub=_U9.b,_Uc=_U9.c,_Ud=_U9.d,_Ue=_U9.e;if((imul(3,_U4)|0)>=_Ua){if((imul(3,_Ua)|0)>=_U4){return new T5(0,(_U4+_Ua|0)+1|0,E(_TZ),_U0,E(_U3),E(_U9));}else{return new F(function(){return _Su(_U5,_U6,_U7,B(_Tu(_TZ,_U0,_U8,_Ua,_Ub,_Uc,_Ud,_Ue)));});}}else{return new F(function(){return _RN(_Ub,_Uc,B(_TJ(_TZ,_U0,_U4,_U5,_U6,_U7,_U8,_Ud)),_Ue);});}}else{return new F(function(){return _Tc(_TZ,_U0,_U3);});}}else{return new F(function(){return _Th(_TZ,_U0,_U2);});}},_Uf=function(_Ug,_Uh,_Ui){var _Uj=E(_Ug);if(_Uj==1){var _Uk=E(_Uh);return new T2(0,new T(function(){return new T5(0,1,E(_Uk.a),_Uk.b,E(_RI),E(_RI));}),_Ui);}else{var _Ul=B(_Uf(_Uj>>1,_Uh,_Ui)),_Um=_Ul.a,_Un=E(_Ul.b);if(!_Un._){return new T2(0,_Um,_4);}else{var _Uo=E(_Un.a),_Up=B(_Uq(_Uj>>1,_Un.b));return new T2(0,new T(function(){return B(_TY(_Uo.a,_Uo.b,_Um,_Up.a));}),_Up.b);}}},_Uq=function(_Ur,_Us){var _Ut=E(_Us);if(!_Ut._){return new T2(0,_RI,_4);}else{var _Uu=_Ut.a,_Uv=_Ut.b,_Uw=E(_Ur);if(_Uw==1){var _Ux=E(_Uu);return new T2(0,new T(function(){return new T5(0,1,E(_Ux.a),_Ux.b,E(_RI),E(_RI));}),_Uv);}else{var _Uy=B(_Uf(_Uw>>1,_Uu,_Uv)),_Uz=_Uy.a,_UA=E(_Uy.b);if(!_UA._){return new T2(0,_Uz,_4);}else{var _UB=E(_UA.a),_UC=B(_Uq(_Uw>>1,_UA.b));return new T2(0,new T(function(){return B(_TY(_UB.a,_UB.b,_Uz,_UC.a));}),_UC.b);}}}},_UD=function(_UE,_UF,_UG){while(1){var _UH=E(_UG);if(!_UH._){return E(_UF);}else{var _UI=E(_UH.a),_UJ=B(_Uq(_UE,_UH.b)),_UK=_UE<<1,_UL=B(_TY(_UI.a,_UI.b,_UF,_UJ.a));_UE=_UK;_UF=_UL;_UG=_UJ.b;continue;}}},_UM=function(_UN,_UO,_UP,_UQ,_UR,_US){var _UT=B(_fK(_UP,_UQ,_UR,_US)),_UU=B(_gH(E(_UT.a)&4294967295,function(_UV,_UW){return new F(function(){return _RB(_UN,_UO,_UV,_UW);});},new T3(0,_UP,_UQ,_UR),_UT.b));return new T2(0,new T(function(){var _UX=E(_UU.a);if(!_UX._){return new T0(1);}else{var _UY=E(_UX.a);return B(_UD(1,new T5(0,1,E(_UY.a),_UY.b,E(_RI),E(_RI)),_UX.b));}}),_UU.b);},_UZ=new T0(2),_V0=new T0(10),_V1=new T0(5),_V2=new T0(9),_V3=new T0(6),_V4=new T0(7),_V5=new T0(8),_V6=function(_V7,_V8){var _V9=E(_V7),_Va=B(_fK(_V9.a,_V9.b,_V9.c,E(_V8))),_Vb=B(_gH(E(_Va.a)&4294967295,_gv,_V9,_Va.b));return new T2(0,_Vb.a,_Vb.b);},_Vc=function(_Vd,_Ve){var _Vf=E(_Vd),_Vg=_Vf.a,_Vh=_Vf.b,_Vi=_Vf.c,_Vj=B(_fK(_Vg,_Vh,_Vi,E(_Ve))),_Vk=B(_gH(E(_Vj.a)&4294967295,_Vl,_Vf,_Vj.b)),_Vm=B(_fK(_Vg,_Vh,_Vi,E(_Vk.b))),_Vn=B(_gH(E(_Vm.a)&4294967295,_V6,_Vf,_Vm.b));return new T2(0,new T2(0,_Vk.a,_Vn.a),_Vn.b);},_Vo=function(_Vp,_Vq,_Vr,_Vs){var _Vt=B(_fE(_Vp,_Vq,_Vr,_Vs)),_Vu=_Vt.b;switch(E(_Vt.a)){case 0:var _Vv=B(_fK(_Vp,_Vq,_Vr,E(_Vu))),_Vw=B(_fK(_Vp,_Vq,_Vr,E(_Vv.b)));return new T2(0,new T(function(){return new T2(0,E(_Vv.a)&4294967295,E(_Vw.a)&4294967295);}),_Vw.b);case 1:var _Vx=B(_fK(_Vp,_Vq,_Vr,E(_Vu))),_Vy=B(_fK(_Vp,_Vq,_Vr,E(_Vx.b)));return new T2(0,new T(function(){return new T2(1,E(_Vx.a)&4294967295,E(_Vy.a)&4294967295);}),_Vy.b);case 2:var _Vz=B(_fK(_Vp,_Vq,_Vr,E(_Vu))),_VA=B(_fK(_Vp,_Vq,_Vr,E(_Vz.b)));return new T2(0,new T(function(){return new T2(2,E(_Vz.a)&4294967295,E(_VA.a)&4294967295);}),_VA.b);case 3:var _VB=B(_fK(_Vp,_Vq,_Vr,E(_Vu))),_VC=B(_gH(E(_VB.a)&4294967295,_gv,new T3(0,_Vp,_Vq,_Vr),_VB.b));return new T2(0,new T1(3,_VC.a),_VC.b);case 4:var _VD=B(_fK(_Vp,_Vq,_Vr,E(_Vu))),_VE=B(_gH(E(_VD.a)&4294967295,_Vl,new T3(0,_Vp,_Vq,_Vr),_VD.b)),_VF=B(_fK(_Vp,_Vq,_Vr,E(_VE.b))),_VG=B(_gH(E(_VF.a)&4294967295,_Vc,new T3(0,_Vp,_Vq,_Vr),_VF.b));return new T2(0,new T2(4,_VE.a,_VG.a),_VG.b);case 5:return new T2(0,_V1,_Vu);case 6:return new T2(0,_V4,_Vu);case 7:return new T2(0,_V3,_Vu);case 8:return new T2(0,_V5,_Vu);case 9:return new T2(0,_V2,_Vu);case 10:return new T2(0,_V0,_Vu);default:return E(_JU);}},_Vl=function(_VH,_VI){var _VJ=E(_VH),_VK=B(_Vo(_VJ.a,_VJ.b,_VJ.c,E(_VI)));return new T2(0,_VK.a,_VK.b);},_VL=new T(function(){return B(unCStr("putWord8 not implemented"));}),_VM=new T(function(){return B(err(_VL));}),_VN=function(_VO){switch(E(_VO)._){case 0:return E(_eb);case 1:return E(_eb);case 2:return E(_eb);case 3:return E(_eb);case 4:return E(_eb);case 5:return E(_VM);case 6:return E(_VM);case 7:return E(_VM);case 8:return E(_VM);case 9:return E(_VM);default:return E(_VM);}},_VP=new T2(0,_VN,_Vl),_VQ=function(_VR,_VS){var _VT=E(_VR),_VU=B(_km(_VP,_iF,_VT.a,_VT.b,_VT.c,E(_VS)));return new T2(0,_VU.a,_VU.b);},_VV=new T(function(){return B(unCStr("MArray: undefined array element"));}),_VW=new T(function(){return B(err(_VV));}),_VX=new T(function(){return B(unCStr("Negative range size"));}),_VY=new T(function(){return B(err(_VX));}),_VZ=function(_W0,_W1,_W2,_W3){var _W4=B(_UM(_g9,_My,_W0,_W1,_W2,_W3)),_W5=B(_UM(_g9,_h0,_W0,_W1,_W2,E(_W4.b))),_W6=B(_fK(_W0,_W1,_W2,E(_W5.b))),_W7=E(_W6.a)&4294967295,_W8=B(_k5(_W7,_VQ,new T3(0,_W0,_W1,_W2),_W6.b)),_W9=B(_km(_mK,_iF,_W0,_W1,_W2,E(_W8.b))),_Wa=B(_Rl(_Qm,_W0,_W1,_W2,E(_W9.b))),_Wb=B(_Rl(_Qm,_W0,_W1,_W2,E(_Wa.b))),_Wc=B(_Rl(_Q8,_W0,_W1,_W2,E(_Wb.b))),_Wd=B(_UM(_g9,_kQ,_W0,_W1,_W2,E(_Wc.b))),_We=B(_fK(_W0,_W1,_W2,E(_Wd.b))),_Wf=new T(function(){var _Wg=new T(function(){var _Wh=function(_){var _Wi=_W7-1|0,_Wj=function(_Wk){if(_Wk>=0){var _Wl=newArr(_Wk,_VW),_Wm=_Wl,_Wn=function(_Wo){var _Wp=function(_Wq,_Wr,_){while(1){if(_Wq!=_Wo){var _Ws=E(_Wr);if(!_Ws._){return _5;}else{var _=_Wm[_Wq]=_Ws.a,_Wt=_Wq+1|0;_Wq=_Wt;_Wr=_Ws.b;continue;}}else{return _5;}}},_Wu=B(_Wp(0,_W8.a,_));return new T4(0,E(_iI),E(_Wi),_Wk,_Wm);};if(0>_Wi){return new F(function(){return _Wn(0);});}else{var _Wv=_Wi+1|0;if(_Wv>=0){return new F(function(){return _Wn(_Wv);});}else{return E(_iH);}}}else{return E(_VY);}};if(0>_Wi){return new F(function(){return _Wj(0);});}else{return new F(function(){return _Wj(_Wi+1|0);});}};return B(_9d(_Wh));});return {_:0,a:_W4.a,b:_W5.a,c:_W9.a,d:_Wa.a,e:_Wb.a,f:_Wg,g:_Wc.a,h:_UZ,i:_RI,j:_Wd.a,k:_UZ,l:E(_We.a)&4294967295};});return new T2(0,_Wf,_We.b);},_Ww=function(_Wx,_Wy){var _Wz=E(_Wx),_WA=B(_VZ(_Wz.a,_Wz.b,_Wz.c,E(_Wy)));return new T2(0,_WA.a,_WA.b);},_WB=function(_WC){return E(_eb);},_WD=new T2(0,_WB,_Ww),_WE=new T2(1,_cm,_4),_WF=function(_WG,_WH){var _WI=new T(function(){return B(A3(_eI,_ey,new T2(1,function(_WJ){return new F(function(){return _co(0,_WH&4294967295,_WJ);});},new T2(1,function(_WK){return new F(function(){return _co(0,E(_WG)&4294967295,_WK);});},_4)),_WE));});return new F(function(){return err(B(unAppCStr("Unsupported PGF version ",new T2(1,_cn,_WI))));});},_WL=function(_WM,_WN){var _WO=new T(function(){var _WP=E(_WM),_WQ=B(_fE(_WP.a,_WP.b,_WP.c,E(_WN)));return new T2(0,_WQ.a,_WQ.b);}),_WR=new T(function(){var _WS=E(_WM),_WT=B(_fE(_WS.a,_WS.b,_WS.c,E(E(_WO).b)));return new T2(0,_WT.a,_WT.b);});return new T2(0,new T(function(){return (E(E(_WO).a)<<8>>>0&65535|E(E(_WR).a))>>>0;}),new T(function(){return E(E(_WR).b);}));},_WU=function(_WV){var _WW=E(_WV);return new T4(0,_WW.a,_WW.b,new T(function(){var _WX=E(_WW.c);if(!_WX._){return __Z;}else{return new T1(1,new T2(0,_WX.a,_4));}}),_WW.d);},_WY=function(_WZ){return E(_eb);},_X0=0,_X1=1,_X2=function(_X3,_X4,_X5,_X6){var _X7=B(_fE(_X3,_X4,_X5,_X6)),_X8=_X7.b;switch(E(_X7.a)){case 0:var _X9=B(_fE(_X3,_X4,_X5,E(_X8))),_Xa=_X9.b;switch(E(_X9.a)){case 0:var _Xb=B(_fV(_X3,_X4,_X5,E(_Xa))),_Xc=B(_X2(_X3,_X4,_X5,E(_Xb.b)));return new T2(0,new T3(0,_X0,_Xb.a,_Xc.a),_Xc.b);case 1:var _Xd=B(_fV(_X3,_X4,_X5,E(_Xa))),_Xe=B(_X2(_X3,_X4,_X5,E(_Xd.b)));return new T2(0,new T3(0,_X1,_Xd.a,_Xe.a),_Xe.b);default:return E(_JU);}break;case 1:var _Xf=B(_X2(_X3,_X4,_X5,E(_X8))),_Xg=B(_X2(_X3,_X4,_X5,E(_Xf.b)));return new T2(0,new T2(1,_Xf.a,_Xg.a),_Xg.b);case 2:var _Xh=B(_Mg(_X3,_X4,_X5,E(_X8)));return new T2(0,new T1(2,_Xh.a),_Xh.b);case 3:var _Xi=B(_fK(_X3,_X4,_X5,E(_X8)));return new T2(0,new T(function(){return new T1(3,E(_Xi.a)&4294967295);}),_Xi.b);case 4:var _Xj=B(_fV(_X3,_X4,_X5,E(_X8)));return new T2(0,new T1(4,_Xj.a),_Xj.b);case 5:var _Xk=B(_fK(_X3,_X4,_X5,E(_X8)));return new T2(0,new T(function(){return new T1(5,E(_Xk.a)&4294967295);}),_Xk.b);case 6:var _Xl=B(_X2(_X3,_X4,_X5,E(_X8))),_Xm=B(_Xn(_X3,_X4,_X5,E(_Xl.b)));return new T2(0,new T2(6,_Xl.a,_Xm.a),_Xm.b);case 7:var _Xo=B(_X2(_X3,_X4,_X5,E(_X8)));return new T2(0,new T1(7,_Xo.a),_Xo.b);default:return E(_JU);}},_Xp=function(_Xq,_Xr){var _Xs=E(_Xq),_Xt=B(_X2(_Xs.a,_Xs.b,_Xs.c,E(_Xr)));return new T2(0,_Xt.a,_Xt.b);},_Xu=function(_Xv,_Xw){var _Xx=E(_Xv),_Xy=_Xx.a,_Xz=_Xx.b,_XA=_Xx.c,_XB=B(_fE(_Xy,_Xz,_XA,E(_Xw))),_XC=_XB.b,_XD=function(_XE,_XF){var _XG=B(_fV(_Xy,_Xz,_XA,_XF)),_XH=B(_Xn(_Xy,_Xz,_XA,E(_XG.b)));return new T2(0,new T3(0,_XE,_XG.a,_XH.a),_XH.b);};switch(E(_XB.a)){case 0:var _XI=B(_XD(_X0,E(_XC)));return new T2(0,_XI.a,_XI.b);case 1:var _XJ=B(_XD(_X1,E(_XC)));return new T2(0,_XJ.a,_XJ.b);default:return E(_JU);}},_Xn=function(_XK,_XL,_XM,_XN){var _XO=B(_fK(_XK,_XL,_XM,_XN)),_XP=B(_gH(E(_XO.a)&4294967295,_Xu,new T3(0,_XK,_XL,_XM),_XO.b)),_XQ=B(_fV(_XK,_XL,_XM,E(_XP.b))),_XR=B(_fK(_XK,_XL,_XM,E(_XQ.b))),_XS=B(_gH(E(_XR.a)&4294967295,_Xp,new T3(0,_XK,_XL,_XM),_XR.b));return new T2(0,new T3(0,_XP.a,_XQ.a,_XS.a),_XS.b);},_XT=function(_XU,_XV){var _XW=E(_XU),_XX=_XW.a,_XY=_XW.b,_XZ=_XW.c,_Y0=B(_fE(_XX,_XY,_XZ,E(_XV))),_Y1=_Y0.b,_Y2=function(_Y3,_Y4){var _Y5=B(_fV(_XX,_XY,_XZ,_Y4)),_Y6=B(_Xn(_XX,_XY,_XZ,E(_Y5.b)));return new T2(0,new T3(0,_Y3,_Y5.a,_Y6.a),_Y6.b);};switch(E(_Y0.a)){case 0:var _Y7=B(_Y2(_X0,E(_Y1)));return new T2(0,_Y7.a,_Y7.b);case 1:var _Y8=B(_Y2(_X1,E(_Y1)));return new T2(0,_Y8.a,_Y8.b);default:return E(_JU);}},_Y9=function(_Ya,_Yb){var _Yc=B(_Jq(_JV,_Md,_Ya,_Yb)),_Yd=E(_Ya),_Ye=B(_fV(_Yd.a,_Yd.b,_Yd.c,E(_Yc.b)));return new T2(0,new T2(0,_Yc.a,_Ye.a),_Ye.b);},_Yf=function(_Yg,_Yh,_Yi,_Yj){var _Yk=B(_fK(_Yg,_Yh,_Yi,_Yj)),_Yl=B(_gH(E(_Yk.a)&4294967295,_XT,new T3(0,_Yg,_Yh,_Yi),_Yk.b)),_Ym=B(_fK(_Yg,_Yh,_Yi,E(_Yl.b))),_Yn=B(_gH(E(_Ym.a)&4294967295,_Y9,new T3(0,_Yg,_Yh,_Yi),_Ym.b)),_Yo=B(_Jq(_JV,_Md,new T3(0,_Yg,_Yh,_Yi),_Yn.b));return new T2(0,new T3(0,_Yl.a,_Yn.a,_Yo.a),_Yo.b);},_Yp=function(_Yq,_Yr){var _Ys=E(_Yq),_Yt=B(_Yf(_Ys.a,_Ys.b,_Ys.c,E(_Yr)));return new T2(0,_Yt.a,_Yt.b);},_Yu=new T2(0,_WY,_Yp),_Yv=function(_Yw){return E(_eb);},_Yx=new T0(4),_Yy=function(_Yz,_YA,_YB){switch(E(_Yz)){case 0:var _YC=E(_YA),_YD=_YC.a,_YE=_YC.b,_YF=_YC.c,_YG=B(_fV(_YD,_YE,_YF,E(_YB))),_YH=B(_fK(_YD,_YE,_YF,E(_YG.b))),_YI=B(_gH(E(_YH.a)&4294967295,_YJ,_YC,_YH.b));return new T2(0,new T2(0,_YG.a,_YI.a),_YI.b);case 1:var _YK=E(_YA),_YL=B(_fV(_YK.a,_YK.b,_YK.c,E(_YB)));return new T2(0,new T1(2,_YL.a),_YL.b);case 2:var _YM=E(_YA),_YN=_YM.a,_YO=_YM.b,_YP=_YM.c,_YQ=B(_fV(_YN,_YO,_YP,E(_YB))),_YR=B(_fE(_YN,_YO,_YP,E(_YQ.b))),_YS=B(_Yy(E(_YR.a),_YM,_YR.b));return new T2(0,new T2(3,_YQ.a,_YS.a),_YS.b);case 3:return new T2(0,_Yx,_YB);case 4:var _YT=E(_YA),_YU=B(_Mg(_YT.a,_YT.b,_YT.c,E(_YB)));return new T2(0,new T1(1,_YU.a),_YU.b);case 5:var _YV=E(_YA),_YW=B(_fE(_YV.a,_YV.b,_YV.c,E(_YB))),_YX=B(_Yy(E(_YW.a),_YV,_YW.b));return new T2(0,new T1(5,_YX.a),_YX.b);case 6:var _YY=E(_YA),_YZ=B(_X2(_YY.a,_YY.b,_YY.c,E(_YB)));return new T2(0,new T1(6,_YZ.a),_YZ.b);default:return E(_JU);}},_Z0=function(_Z1,_Z2,_Z3,_Z4){var _Z5=B(_fE(_Z1,_Z2,_Z3,_Z4));return new F(function(){return _Yy(E(_Z5.a),new T3(0,_Z1,_Z2,_Z3),_Z5.b);});},_YJ=function(_Z6,_Z7){var _Z8=E(_Z6),_Z9=B(_Z0(_Z8.a,_Z8.b,_Z8.c,E(_Z7)));return new T2(0,_Z9.a,_Z9.b);},_Za=function(_Zb,_Zc,_Zd,_Ze){var _Zf=B(_fK(_Zb,_Zc,_Zd,_Ze)),_Zg=B(_gH(E(_Zf.a)&4294967295,_YJ,new T3(0,_Zb,_Zc,_Zd),_Zf.b)),_Zh=B(_X2(_Zb,_Zc,_Zd,E(_Zg.b)));return new T2(0,new T2(0,_Zg.a,_Zh.a),_Zh.b);},_Zi=function(_Zj,_Zk){var _Zl=E(_Zj),_Zm=B(_Za(_Zl.a,_Zl.b,_Zl.c,E(_Zk)));return new T2(0,_Zm.a,_Zm.b);},_Zn=function(_Zo,_Zp,_Zq,_Zr){var _Zs=B(_Xn(_Zo,_Zp,_Zq,_Zr)),_Zt=_Zs.a,_Zu=B(_fK(_Zo,_Zp,_Zq,E(_Zs.b))),_Zv=_Zu.a,_Zw=B(_fE(_Zo,_Zp,_Zq,E(_Zu.b))),_Zx=_Zw.b;if(!E(_Zw.a)){var _Zy=B(_Jq(_JV,_Md,new T3(0,_Zo,_Zp,_Zq),_Zx));return new T2(0,new T4(0,_Zt,new T(function(){return E(_Zv)&4294967295;}),_4l,_Zy.a),_Zy.b);}else{var _Zz=B(_fK(_Zo,_Zp,_Zq,E(_Zx))),_ZA=B(_gH(E(_Zz.a)&4294967295,_Zi,new T3(0,_Zo,_Zp,_Zq),_Zz.b)),_ZB=B(_Jq(_JV,_Md,new T3(0,_Zo,_Zp,_Zq),_ZA.b));return new T2(0,new T4(0,_Zt,new T(function(){return E(_Zv)&4294967295;}),new T1(1,_ZA.a),_ZB.a),_ZB.b);}},_ZC=function(_ZD,_ZE){var _ZF=E(_ZD),_ZG=B(_Zn(_ZF.a,_ZF.b,_ZF.c,E(_ZE)));return new T2(0,_ZG.a,_ZG.b);},_ZH=new T2(0,_Yv,_ZC),_ZI=function(_ZJ,_ZK){var _ZL=E(_ZK);return (_ZL._==0)?new T5(0,_ZL.a,E(_ZL.b),new T(function(){return B(A1(_ZJ,_ZL.c));}),E(B(_ZI(_ZJ,_ZL.d))),E(B(_ZI(_ZJ,_ZL.e)))):new T0(1);},_ZM=function(_ZN,_ZO,_ZP,_ZQ){var _ZR=B(_UM(_g9,_My,_ZN,_ZO,_ZP,_ZQ)),_ZS=B(_UM(_g9,_ZH,_ZN,_ZO,_ZP,E(_ZR.b))),_ZT=B(_UM(_g9,_Yu,_ZN,_ZO,_ZP,E(_ZS.b)));return new T2(0,new T3(0,_ZR.a,new T(function(){return B(_ZI(_WU,_ZS.a));}),_ZT.a),_ZT.b);},_ZU=function(_ZV,_ZW,_ZX){var _ZY=E(_ZV);if(!_ZY._){return new T2(0,_4,_ZX);}else{var _ZZ=new T(function(){return B(A2(_ZY.a,_ZW,_ZX));}),_100=B(_ZU(_ZY.b,_ZW,new T(function(){return E(E(_ZZ).b);})));return new T2(0,new T2(1,new T(function(){return E(E(_ZZ).a);}),_100.a),_100.b);}},_101=function(_102,_103,_104,_105){if(0>=_102){return new F(function(){return _ZU(_4,_104,_105);});}else{var _106=function(_107){var _108=E(_107);return (_108==1)?E(new T2(1,_103,_4)):new T2(1,_103,new T(function(){return B(_106(_108-1|0));}));};return new F(function(){return _ZU(B(_106(_102)),_104,_105);});}},_109=function(_10a,_10b,_10c){var _10d=new T(function(){var _10e=E(_10b),_10f=B(_fK(_10e.a,_10e.b,_10e.c,E(_10c))),_10g=E(_10f.a)&4294967295,_10h=B(_101(_10g,_10a,_10e,_10f.b));return new T2(0,new T2(0,_10g,_10h.a),_10h.b);});return new T2(0,new T(function(){return E(E(E(_10d).a).b);}),new T(function(){return E(E(_10d).b);}));},_10i=function(_10j,_10k,_10l,_10m){var _10n=new T(function(){var _10o=function(_10p,_10q){var _10r=new T(function(){return B(A2(_10j,_10p,_10q));}),_10s=B(A2(_10k,_10p,new T(function(){return E(E(_10r).b);})));return new T2(0,new T2(0,new T(function(){return E(E(_10r).a);}),_10s.a),_10s.b);},_10t=B(_109(_10o,_10l,_10m));return new T2(0,_10t.a,_10t.b);});return new T2(0,new T(function(){var _10u=E(E(_10n).a);if(!_10u._){return new T0(1);}else{var _10v=E(_10u.a);return B(_UD(1,new T5(0,1,E(_10v.a),_10v.b,E(_RI),E(_RI)),_10u.b));}}),new T(function(){return E(E(_10n).b);}));},_10w=new T(function(){return B(unCStr("Prelude.Enum.Bool.toEnum: bad argument"));}),_10x=new T(function(){return B(err(_10w));}),_10y=new T(function(){return B(unCStr(")"));}),_10z=function(_10A){return new F(function(){return err(B(unAppCStr("Unable to read PGF file (",new T(function(){return B(_0(_10A,_10y));}))));});},_10B=new T(function(){return B(unCStr("getLiteral"));}),_10C=new T(function(){return B(_10z(_10B));}),_10D=function(_10E,_10F,_10G,_10H){var _10I=B(_fE(_10E,_10F,_10G,_10H)),_10J=_10I.b;switch(E(_10I.a)){case 0:var _10K=B(_fK(_10E,_10F,_10G,E(_10J))),_10L=B(_gH(E(_10K.a)&4294967295,_gv,new T3(0,_10E,_10F,_10G),_10K.b));return new T2(0,new T1(0,_10L.a),_10L.b);case 1:var _10M=B(_fK(_10E,_10F,_10G,E(_10J)));return new T2(0,new T1(1,new T(function(){return E(_10M.a)&4294967295;})),_10M.b);case 2:var _10N=B(_Jq(_JV,_Md,new T3(0,_10E,_10F,_10G),_10J));return new T2(0,new T1(2,_10N.a),_10N.b);default:return E(_10C);}},_10O=new T(function(){return B(unCStr("getBindType"));}),_10P=new T(function(){return B(_10z(_10O));}),_10Q=new T(function(){return B(unCStr("getExpr"));}),_10R=new T(function(){return B(_10z(_10Q));}),_10S=function(_10T,_10U,_10V,_10W){var _10X=B(_fE(_10T,_10U,_10V,_10W)),_10Y=_10X.b;switch(E(_10X.a)){case 0:var _10Z=B(_fE(_10T,_10U,_10V,E(_10Y))),_110=_10Z.b;switch(E(_10Z.a)){case 0:var _111=B(_fV(_10T,_10U,_10V,E(_110))),_112=B(_10S(_10T,_10U,_10V,E(_111.b)));return new T2(0,new T3(0,_X0,_111.a,_112.a),_112.b);case 1:var _113=B(_fV(_10T,_10U,_10V,E(_110))),_114=B(_10S(_10T,_10U,_10V,E(_113.b)));return new T2(0,new T3(0,_X1,_113.a,_114.a),_114.b);default:return E(_10P);}break;case 1:var _115=B(_10S(_10T,_10U,_10V,E(_10Y))),_116=B(_10S(_10T,_10U,_10V,E(_115.b)));return new T2(0,new T2(1,_115.a,_116.a),_116.b);case 2:var _117=B(_10D(_10T,_10U,_10V,E(_10Y)));return new T2(0,new T1(2,_117.a),_117.b);case 3:var _118=B(_fK(_10T,_10U,_10V,E(_10Y)));return new T2(0,new T(function(){return new T1(3,E(_118.a)&4294967295);}),_118.b);case 4:var _119=B(_fV(_10T,_10U,_10V,E(_10Y)));return new T2(0,new T1(4,_119.a),_119.b);case 5:var _11a=B(_fK(_10T,_10U,_10V,E(_10Y)));return new T2(0,new T(function(){return new T1(5,E(_11a.a)&4294967295);}),_11a.b);case 6:var _11b=B(_10S(_10T,_10U,_10V,E(_10Y))),_11c=B(_11d(_10T,_10U,_10V,_11b.b));return new T2(0,new T2(6,_11b.a,_11c.a),_11c.b);case 7:var _11e=B(_10S(_10T,_10U,_10V,E(_10Y)));return new T2(0,new T1(7,_11e.a),_11e.b);default:return E(_10R);}},_11f=function(_11g,_11h){var _11i=E(_11g),_11j=B(_10S(_11i.a,_11i.b,_11i.c,E(_11h)));return new T2(0,_11j.a,_11j.b);},_11k=function(_11l,_11m,_11n,_11o){var _11p=B(_fE(_11l,_11m,_11n,_11o)),_11q=_11p.b;switch(E(_11p.a)){case 0:var _11r=B(_fV(_11l,_11m,_11n,E(_11q))),_11s=B(_11d(_11l,_11m,_11n,_11r.b));return new T2(0,new T3(0,_X0,_11r.a,_11s.a),_11s.b);case 1:var _11t=B(_fV(_11l,_11m,_11n,E(_11q))),_11u=B(_11d(_11l,_11m,_11n,_11t.b));return new T2(0,new T3(0,_X1,_11t.a,_11u.a),_11u.b);default:return E(_10P);}},_11v=function(_11w,_11x){var _11y=E(_11w),_11z=B(_11k(_11y.a,_11y.b,_11y.c,E(_11x)));return new T2(0,_11z.a,_11z.b);},_11d=function(_11A,_11B,_11C,_11D){var _11E=new T3(0,_11A,_11B,_11C),_11F=B(_109(_11v,_11E,_11D)),_11G=B(_fV(_11A,_11B,_11C,E(_11F.b))),_11H=B(_109(_11f,_11E,_11G.b));return new T2(0,new T3(0,_11F.a,_11G.a,_11H.a),_11H.b);},_11I=new T(function(){return B(unCStr("getPatt"));}),_11J=new T(function(){return B(_10z(_11I));}),_11K=function(_11L,_11M,_11N,_11O){var _11P=B(_fE(_11L,_11M,_11N,_11O)),_11Q=_11P.b;switch(E(_11P.a)){case 0:var _11R=B(_fV(_11L,_11M,_11N,E(_11Q))),_11S=B(_109(_11T,new T3(0,_11L,_11M,_11N),_11R.b));return new T2(0,new T2(0,_11R.a,_11S.a),_11S.b);case 1:var _11U=B(_fV(_11L,_11M,_11N,E(_11Q)));return new T2(0,new T1(2,_11U.a),_11U.b);case 2:var _11V=B(_fV(_11L,_11M,_11N,E(_11Q))),_11W=B(_11K(_11L,_11M,_11N,E(_11V.b)));return new T2(0,new T2(3,_11V.a,_11W.a),_11W.b);case 3:return new T2(0,_Yx,_11Q);case 4:var _11X=B(_10D(_11L,_11M,_11N,E(_11Q)));return new T2(0,new T1(1,_11X.a),_11X.b);case 5:var _11Y=B(_11K(_11L,_11M,_11N,E(_11Q)));return new T2(0,new T1(5,_11Y.a),_11Y.b);case 6:var _11Z=B(_10S(_11L,_11M,_11N,E(_11Q)));return new T2(0,new T1(6,_11Z.a),_11Z.b);default:return E(_11J);}},_11T=function(_120,_121){var _122=E(_120),_123=B(_11K(_122.a,_122.b,_122.c,E(_121)));return new T2(0,_123.a,_123.b);},_124=function(_125,_126){var _127=E(_125),_128=B(_109(_11T,_127,_126)),_129=B(_10S(_127.a,_127.b,_127.c,E(_128.b)));return new T2(0,new T2(0,_128.a,_129.a),_129.b);},_12a=function(_12b,_12c,_12d,_12e){var _12f=B(_11d(_12b,_12c,_12d,_12e)),_12g=_12f.a,_12h=B(_fK(_12b,_12c,_12d,E(_12f.b))),_12i=_12h.a,_12j=B(_fE(_12b,_12c,_12d,E(_12h.b))),_12k=_12j.b;switch(E(_12j.a)&4294967295){case 0:var _12l=B(_Jq(_JV,_Md,new T3(0,_12b,_12c,_12d),_12k));return new T2(0,new T4(0,_12g,new T(function(){return E(_12i)&4294967295;}),_4l,_12l.a),_12l.b);case 1:var _12m=new T3(0,_12b,_12c,_12d),_12n=new T(function(){var _12o=B(_109(_124,_12m,_12k));return new T2(0,_12o.a,_12o.b);}),_12p=B(_Jq(_JV,_Md,_12m,new T(function(){return E(E(_12n).b);},1)));return new T2(0,new T4(0,_12g,new T(function(){return E(_12i)&4294967295;}),new T1(1,new T(function(){return E(E(_12n).a);})),_12p.a),_12p.b);default:return E(_10x);}},_12q=function(_12r,_12s){var _12t=E(_12r),_12u=B(_12a(_12t.a,_12t.b,_12t.c,_12s));return new T2(0,_12u.a,_12u.b);},_12v=function(_12w,_12x){var _12y=E(_12w),_12z=B(_10D(_12y.a,_12y.b,_12y.c,E(_12x)));return new T2(0,_12z.a,_12z.b);},_12A=function(_12B,_12C){var _12D=E(_12B),_12E=B(_fV(_12D.a,_12D.b,_12D.c,E(_12C)));return new T2(0,_12E.a,_12E.b);},_12F=function(_12G,_12H){while(1){var _12I=E(_12G);if(!_12I._){return (E(_12H)._==0)?1:0;}else{var _12J=E(_12H);if(!_12J._){return 2;}else{var _12K=E(_12I.a),_12L=E(_12J.a);if(_12K!=_12L){return (_12K>_12L)?2:0;}else{_12G=_12I.b;_12H=_12J.b;continue;}}}}},_12M=function(_12N,_12O){return (B(_12F(_12N,_12O))==0)?true:false;},_12P=function(_12Q,_12R){return (B(_12F(_12Q,_12R))==2)?false:true;},_12S=function(_12T,_12U){return (B(_12F(_12T,_12U))==2)?true:false;},_12V=function(_12W,_12X){return (B(_12F(_12W,_12X))==0)?false:true;},_12Y=function(_12Z,_130){return (B(_12F(_12Z,_130))==2)?E(_12Z):E(_130);},_131=function(_132,_133){return (B(_12F(_132,_133))==2)?E(_133):E(_132);},_134={_:0,a:_t1,b:_12F,c:_12M,d:_12P,e:_12S,f:_12V,g:_12Y,h:_131},_135=function(_136){var _137=E(_136)&4294967295;if(_137>>>0>1114111){return new F(function(){return _gc(_137);});}else{return _137;}},_138=function(_139){var _13a=E(_139);return (_13a._==0)?__Z:new T2(1,new T(function(){return B(_135(_13a.a));}),new T(function(){return B(_138(_13a.b));}));},_13b=function(_13c){var _13d=E(_13c);return (_13d._==0)?__Z:new T2(1,new T(function(){return B(_135(_13d.a));}),new T(function(){return B(_13b(_13d.b));}));},_13e=function(_13f,_13g,_13h,_13i,_13j,_13k){return new F(function(){return _sH(B(_G(_135,B(_Jb(_13f,_13g,_13h)))),B(_G(_135,B(_Jb(_13i,_13j,_13k)))));});},_13l=function(_13m,_13n,_13o,_13p,_13q,_13r){return (!B(_13e(_13m,_13n,_13o,_13p,_13q,_13r)))?(B(_12F(B(_13b(new T(function(){return B(_Jb(_13m,_13n,_13o));}))),B(_138(new T(function(){return B(_Jb(_13p,_13q,_13r));})))))==2)?2:0:1;},_13s=function(_13t,_13u,_13v,_13w,_13x,_13y){var _13z=new T3(0,_13u,_13v,_13w),_13A=E(_13y);if(!_13A._){var _13B=_13A.c,_13C=_13A.d,_13D=_13A.e,_13E=E(_13A.b);switch(B(_13l(_13u,_13v,_13w,_13E.a,_13E.b,_13E.c))){case 0:return new F(function(){return _RN(_13E,_13B,B(_13s(_13t,_13u,_13v,_13w,_13x,_13C)),_13D);});break;case 1:return new T5(0,_13A.a,E(_13z),new T(function(){return B(A3(_13t,_13z,_13x,_13B));}),E(_13C),E(_13D));default:return new F(function(){return _Su(_13E,_13B,_13C,B(_13s(_13t,_13u,_13v,_13w,_13x,_13D)));});}}else{return new T5(0,1,E(_13z),_13x,E(_RI),E(_RI));}},_13F=function(_13G,_13H){var _13I=function(_13J,_13K){while(1){var _13L=E(_13K);if(!_13L._){return E(_13J);}else{var _13M=E(_13L.a),_13N=E(_13M.a),_13O=B(_13s(_13G,_13N.a,_13N.b,_13N.c,_13M.b,_13J));_13J=_13O;_13K=_13L.b;continue;}}};return new F(function(){return _13I(_RI,_13H);});},_13P=function(_13Q){return E(E(_13Q).b);},_13R=function(_13S,_13T,_13U,_13V){var _13W=E(_13T),_13X=E(_13V);if(!_13X._){var _13Y=_13X.b,_13Z=_13X.c,_140=_13X.d,_141=_13X.e;switch(B(A3(_13P,_13S,_13W,_13Y))){case 0:return new F(function(){return _RN(_13Y,_13Z,B(_13R(_13S,_13W,_13U,_140)),_141);});break;case 1:return new T5(0,_13X.a,E(_13W),_13U,E(_140),E(_141));default:return new F(function(){return _Su(_13Y,_13Z,_140,B(_13R(_13S,_13W,_13U,_141)));});}}else{return new T5(0,1,E(_13W),_13U,E(_RI),E(_RI));}},_142=function(_143,_144,_145,_146){return new F(function(){return _13R(_143,_144,_145,_146);});},_147=function(_148,_149,_14a,_14b,_14c){var _14d=E(_14c),_14e=B(_14f(_148,_149,_14a,_14b,_14d.a,_14d.b));return new T2(0,_14e.a,_14e.b);},_14g=function(_14h,_14i,_14j){var _14k=function(_14l,_14m){while(1){var _14n=E(_14l),_14o=E(_14m);if(!_14o._){switch(B(A3(_13P,_14h,_14n,_14o.b))){case 0:_14l=_14n;_14m=_14o.d;continue;case 1:return new T1(1,_14o.c);default:_14l=_14n;_14m=_14o.e;continue;}}else{return __Z;}}};return new F(function(){return _14k(_14i,_14j);});},_14p=function(_14q,_14r){var _14s=E(_14q);if(!_14s._){return new T2(0,new T1(1,_14r),_RI);}else{var _14t=new T(function(){return new T5(0,1,E(_14s.a),new T(function(){return B(_14u(_14s.b,_14r));}),E(_RI),E(_RI));});return new T2(0,_4l,_14t);}},_14u=function(_14v,_14w){var _14x=B(_14p(_14v,_14w));return new T2(0,_14x.a,_14x.b);},_14f=function(_14y,_14z,_14A,_14B,_14C,_14D){var _14E=E(_14A);if(!_14E._){var _14F=E(_14C);return (_14F._==0)?new T2(0,new T1(1,_14B),_14D):new T2(0,new T1(1,new T(function(){return B(A2(_14z,_14B,_14F.a));})),_14D);}else{var _14G=_14E.a,_14H=_14E.b,_14I=B(_14g(_14y,_14G,_14D));if(!_14I._){var _14J=new T(function(){return B(_142(_14y,_14G,new T(function(){return B(_14u(_14H,_14B));}),_14D));});return new T2(0,_14C,_14J);}else{var _14K=new T(function(){return B(_142(_14y,_14G,new T(function(){return B(_147(_14y,_14z,_14H,_14B,_14I.a));}),_14D));});return new T2(0,_14C,_14K);}}},_14L=function(_14M,_14N,_14O){var _14P=function(_14Q,_14R,_14S){while(1){var _14T=E(_14Q);if(!_14T._){return new T2(0,_14R,_14S);}else{var _14U=E(_14T.a),_14V=B(_14f(_14M,_14N,_14U.a,_14U.b,_14R,_14S));_14Q=_14T.b;_14R=_14V.a;_14S=_14V.b;continue;}}};return new F(function(){return _14P(_14O,_4l,_RI);});},_14W=function(_14X,_14Y,_14Z){var _150=E(_14Z);switch(_150._){case 0:var _151=_150.a,_152=_150.b,_153=_150.c,_154=_150.d,_155=_152>>>0;if(((_14X>>>0&((_155-1>>>0^4294967295)>>>0^_155)>>>0)>>>0&4294967295)==_151){return ((_14X>>>0&_155)>>>0==0)?new T4(0,_151,_152,E(B(_14W(_14X,_14Y,_153))),E(_154)):new T4(0,_151,_152,E(_153),E(B(_14W(_14X,_14Y,_154))));}else{var _156=(_14X>>>0^_151>>>0)>>>0,_157=(_156|_156>>>1)>>>0,_158=(_157|_157>>>2)>>>0,_159=(_158|_158>>>4)>>>0,_15a=(_159|_159>>>8)>>>0,_15b=(_15a|_15a>>>16)>>>0,_15c=(_15b^_15b>>>1)>>>0&4294967295,_15d=_15c>>>0;return ((_14X>>>0&_15d)>>>0==0)?new T4(0,(_14X>>>0&((_15d-1>>>0^4294967295)>>>0^_15d)>>>0)>>>0&4294967295,_15c,E(new T2(1,_14X,_14Y)),E(_150)):new T4(0,(_14X>>>0&((_15d-1>>>0^4294967295)>>>0^_15d)>>>0)>>>0&4294967295,_15c,E(_150),E(new T2(1,_14X,_14Y)));}break;case 1:var _15e=_150.a;if(_14X!=_15e){var _15f=(_14X>>>0^_15e>>>0)>>>0,_15g=(_15f|_15f>>>1)>>>0,_15h=(_15g|_15g>>>2)>>>0,_15i=(_15h|_15h>>>4)>>>0,_15j=(_15i|_15i>>>8)>>>0,_15k=(_15j|_15j>>>16)>>>0,_15l=(_15k^_15k>>>1)>>>0&4294967295,_15m=_15l>>>0;return ((_14X>>>0&_15m)>>>0==0)?new T4(0,(_14X>>>0&((_15m-1>>>0^4294967295)>>>0^_15m)>>>0)>>>0&4294967295,_15l,E(new T2(1,_14X,_14Y)),E(_150)):new T4(0,(_14X>>>0&((_15m-1>>>0^4294967295)>>>0^_15m)>>>0)>>>0&4294967295,_15l,E(_150),E(new T2(1,_14X,_14Y)));}else{return new T2(1,_14X,_14Y);}break;default:return new T2(1,_14X,_14Y);}},_15n=function(_15o,_15p){var _15q=function(_15r){while(1){var _15s=E(_15r);switch(_15s._){case 0:var _15t=_15s.b>>>0;if(((_15o>>>0&((_15t-1>>>0^4294967295)>>>0^_15t)>>>0)>>>0&4294967295)==_15s.a){if(!((_15o>>>0&_15t)>>>0)){_15r=_15s.c;continue;}else{_15r=_15s.d;continue;}}else{return __Z;}break;case 1:return (_15o!=_15s.a)?__Z:new T1(1,_15s.b);default:return __Z;}}};return new F(function(){return _15q(_15p);});},_15u=function(_15v,_15w,_15x,_15y){var _15z=E(_15y);if(!_15z._){var _15A=new T(function(){var _15B=B(_15u(_15z.a,_15z.b,_15z.c,_15z.d));return new T2(0,_15B.a,_15B.b);});return new T2(0,new T(function(){return E(E(_15A).a);}),new T(function(){return B(_Ni(_15w,_15x,E(_15A).b));}));}else{return new T2(0,_15w,_15x);}},_15C=function(_15D,_15E,_15F,_15G){var _15H=E(_15F);if(!_15H._){var _15I=new T(function(){var _15J=B(_15C(_15H.a,_15H.b,_15H.c,_15H.d));return new T2(0,_15J.a,_15J.b);});return new T2(0,new T(function(){return E(E(_15I).a);}),new T(function(){return B(_NU(_15E,E(_15I).b,_15G));}));}else{return new T2(0,_15E,_15G);}},_15K=function(_15L,_15M){var _15N=E(_15L);if(!_15N._){var _15O=_15N.a,_15P=E(_15M);if(!_15P._){var _15Q=_15P.a;if(_15O<=_15Q){var _15R=B(_15C(_15Q,_15P.b,_15P.c,_15P.d));return new F(function(){return _Ni(_15R.a,_15N,_15R.b);});}else{var _15S=B(_15u(_15O,_15N.b,_15N.c,_15N.d));return new F(function(){return _NU(_15S.a,_15S.b,_15P);});}}else{return E(_15N);}}else{return E(_15M);}},_15T=function(_15U,_15V,_15W,_15X,_15Y){var _15Z=E(_15U);if(!_15Z._){var _160=_15Z.a,_161=_15Z.b,_162=_15Z.c,_163=_15Z.d;if((imul(3,_160)|0)>=_15V){if((imul(3,_15V)|0)>=_160){return new F(function(){return _15K(_15Z,new T4(0,_15V,E(_15W),E(_15X),E(_15Y)));});}else{return new F(function(){return _NU(_161,_162,B(_15T(_163,_15V,_15W,_15X,_15Y)));});}}else{return new F(function(){return _Ni(_15W,B(_164(_160,_161,_162,_163,_15X)),_15Y);});}}else{return new T4(0,_15V,E(_15W),E(_15X),E(_15Y));}},_164=function(_165,_166,_167,_168,_169){var _16a=E(_169);if(!_16a._){var _16b=_16a.a,_16c=_16a.b,_16d=_16a.c,_16e=_16a.d;if((imul(3,_165)|0)>=_16b){if((imul(3,_16b)|0)>=_165){return new F(function(){return _15K(new T4(0,_165,E(_166),E(_167),E(_168)),_16a);});}else{return new F(function(){return _NU(_166,_167,B(_15T(_168,_16b,_16c,_16d,_16e)));});}}else{return new F(function(){return _Ni(_16c,B(_164(_165,_166,_167,_168,_16d)),_16e);});}}else{return new T4(0,_165,E(_166),E(_167),E(_168));}},_16f=function(_16g,_16h){var _16i=E(_16g);if(!_16i._){var _16j=_16i.a,_16k=_16i.b,_16l=_16i.c,_16m=_16i.d,_16n=E(_16h);if(!_16n._){var _16o=_16n.a,_16p=_16n.b,_16q=_16n.c,_16r=_16n.d;if((imul(3,_16j)|0)>=_16o){if((imul(3,_16o)|0)>=_16j){return new F(function(){return _15K(_16i,_16n);});}else{return new F(function(){return _NU(_16k,_16l,B(_15T(_16m,_16o,_16p,_16q,_16r)));});}}else{return new F(function(){return _Ni(_16p,B(_164(_16j,_16k,_16l,_16m,_16q)),_16r);});}}else{return E(_16i);}}else{return E(_16h);}},_16s=function(_16t,_16u){var _16v=E(_16u);if(!_16v._){var _16w=_16v.b,_16x=B(_16s(_16t,_16v.c)),_16y=_16x.a,_16z=_16x.b,_16A=B(_16s(_16t,_16v.d)),_16B=_16A.a,_16C=_16A.b;return (!B(A1(_16t,_16w)))?new T2(0,B(_16f(_16y,_16B)),B(_Pe(_16w,_16z,_16C))):new T2(0,B(_Pe(_16w,_16y,_16B)),B(_16f(_16z,_16C)));}else{return new T2(0,_Nd,_Nd);}},_16D=function(_16E,_16F,_16G,_16H){var _16I=E(_16G),_16J=B(_16K(_16E,_16F,_16I.a,_16I.b,_16H));return new T2(0,_16J.a,_16J.b);},_16L=function(_16M,_16N,_16O){while(1){var _16P=E(_16O);if(!_16P._){var _16Q=_16P.e;switch(B(A3(_13P,_16M,_16N,_16P.b))){case 0:return new T2(0,B(_14g(_16M,_16N,_16P.d)),_16P);case 1:return new T2(0,new T1(1,_16P.c),_16Q);default:_16O=_16Q;continue;}}else{return new T2(0,_4l,_RI);}}},_16R=function(_16S){return E(E(_16S).f);},_16T=function(_16U,_16V,_16W){while(1){var _16X=E(_16W);if(!_16X._){if(!B(A3(_16R,_16U,_16X.b,_16V))){return E(_16X);}else{_16W=_16X.d;continue;}}else{return new T0(1);}}},_16Y=function(_16Z,_170,_171,_172){while(1){var _173=E(_172);if(!_173._){var _174=_173.b,_175=_173.d,_176=_173.e;switch(B(A3(_13P,_16Z,_170,_174))){case 0:if(!B(A3(_qc,_16Z,_174,_171))){_172=_175;continue;}else{return new T2(0,B(_14g(_16Z,_170,_175)),_173);}break;case 1:return new T2(0,new T1(1,_173.c),B(_16T(_16Z,_171,_176)));default:_172=_176;continue;}}else{return new T2(0,_4l,_RI);}}},_177=function(_178,_179,_17a,_17b){var _17c=E(_17a);if(!_17c._){return new F(function(){return _16L(_178,_179,_17b);});}else{return new F(function(){return _16Y(_178,_179,_17c.a,_17b);});}},_17d=__Z,_17e=function(_17f,_17g,_17h){var _17i=E(_17g);if(!_17i._){return E(_17h);}else{var _17j=function(_17k,_17l){while(1){var _17m=E(_17l);if(!_17m._){var _17n=_17m.b,_17o=_17m.e;switch(B(A3(_13P,_17f,_17k,_17n))){case 0:return new F(function(){return _TY(_17n,_17m.c,B(_17j(_17k,_17m.d)),_17o);});break;case 1:return E(_17o);default:_17l=_17o;continue;}}else{return new T0(1);}}};return new F(function(){return _17j(_17i.a,_17h);});}},_17p=function(_17q,_17r,_17s){var _17t=E(_17r);if(!_17t._){return E(_17s);}else{var _17u=function(_17v,_17w){while(1){var _17x=E(_17w);if(!_17x._){var _17y=_17x.b,_17z=_17x.d;switch(B(A3(_13P,_17q,_17y,_17v))){case 0:return new F(function(){return _TY(_17y,_17x.c,_17z,B(_17u(_17v,_17x.e)));});break;case 1:return E(_17z);default:_17w=_17z;continue;}}else{return new T0(1);}}};return new F(function(){return _17u(_17t.a,_17s);});}},_17A=function(_17B){return E(E(_17B).d);},_17C=function(_17D,_17E,_17F,_17G){var _17H=E(_17E);if(!_17H._){var _17I=E(_17F);if(!_17I._){return E(_17G);}else{var _17J=function(_17K,_17L){while(1){var _17M=E(_17L);if(!_17M._){if(!B(A3(_16R,_17D,_17M.b,_17K))){return E(_17M);}else{_17L=_17M.d;continue;}}else{return new T0(1);}}};return new F(function(){return _17J(_17I.a,_17G);});}}else{var _17N=_17H.a,_17O=E(_17F);if(!_17O._){var _17P=function(_17Q,_17R){while(1){var _17S=E(_17R);if(!_17S._){if(!B(A3(_17A,_17D,_17S.b,_17Q))){return E(_17S);}else{_17R=_17S.e;continue;}}else{return new T0(1);}}};return new F(function(){return _17P(_17N,_17G);});}else{var _17T=function(_17U,_17V,_17W){while(1){var _17X=E(_17W);if(!_17X._){var _17Y=_17X.b;if(!B(A3(_17A,_17D,_17Y,_17U))){if(!B(A3(_16R,_17D,_17Y,_17V))){return E(_17X);}else{_17W=_17X.d;continue;}}else{_17W=_17X.e;continue;}}else{return new T0(1);}}};return new F(function(){return _17T(_17N,_17O.a,_17G);});}}},_17Z=function(_180,_181,_182,_183){var _184=E(_182);if(!_184._){var _185=E(_183);if(!_185._){var _186=function(_187,_188,_189,_18a){var _18b=E(_18a);if(!_18b._){var _18c=E(_189);if(!_18c._){var _18d=_18c.b,_18e=_18c.c,_18f=_18c.e,_18g=B(_177(_180,_18d,_188,_18b)),_18h=_18g.b,_18i=new T1(1,E(_18d)),_18j=B(_186(_187,_18i,_18c.d,B(_17C(_180,_187,_18i,_18b)))),_18k=E(_18g.a);if(!_18k._){return new F(function(){return _TY(_18d,_18e,_18j,B(_186(_18i,_188,_18f,_18h)));});}else{return new F(function(){return _TY(_18d,new T(function(){return B(A3(_181,_18d,_18e,_18k.a));}),_18j,B(_186(_18i,_188,_18f,_18h)));});}}else{return new F(function(){return _TY(_18b.b,_18b.c,B(_17e(_180,_187,_18b.d)),B(_17p(_180,_188,_18b.e)));});}}else{return E(_189);}},_18l=_17d,_18m=_17d,_18n=_184.a,_18o=_184.b,_18p=_184.c,_18q=_184.d,_18r=_184.e,_18s=_185.a,_18t=_185.b,_18u=_185.c,_18v=_185.d,_18w=_185.e,_18x=B(_177(_180,_18o,_18m,new T5(0,_18s,E(_18t),_18u,E(_18v),E(_18w)))),_18y=_18x.b,_18z=new T1(1,E(_18o)),_18A=B(_186(_18l,_18z,_18q,B(_17C(_180,_18l,_18z,new T5(0,_18s,E(_18t),_18u,E(_18v),E(_18w)))))),_18B=E(_18x.a);if(!_18B._){return new F(function(){return _TY(_18o,_18p,_18A,B(_186(_18z,_18m,_18r,_18y)));});}else{return new F(function(){return _TY(_18o,new T(function(){return B(A3(_181,_18o,_18p,_18B.a));}),_18A,B(_186(_18z,_18m,_18r,_18y)));});}}else{return E(_184);}}else{return E(_183);}},_16K=function(_18C,_18D,_18E,_18F,_18G){var _18H=E(_18G),_18I=_18H.a,_18J=new T(function(){return B(_17Z(_18C,function(_18K,_18L,_18M){return new F(function(){return _16D(_18C,_18D,_18L,_18M);});},_18F,_18H.b));}),_18N=new T(function(){var _18O=E(_18E);if(!_18O._){return E(_18I);}else{var _18P=E(_18I);if(!_18P._){return E(_18O);}else{return new T1(1,new T(function(){return B(A2(_18D,_18O.a,_18P.a));}));}}});return new T2(0,_18N,_18J);},_18Q=function(_18R,_18S,_18T){var _18U=function(_18V,_18W,_18X){while(1){var _18Y=E(_18V);if(!_18Y._){return new T2(0,_18W,_18X);}else{var _18Z=B(_16K(_18R,_18S,_18W,_18X,_18Y.a));_18V=_18Y.b;_18W=_18Z.a;_18X=_18Z.b;continue;}}};return new F(function(){return _18U(_18T,_4l,_RI);});},_190=new T0(2),_191=function(_192,_193){var _194=E(_192),_195=E(_193);return new F(function(){return _13e(_194.a,_194.b,_194.c,_195.a,_195.b,_195.c);});},_196=function(_197,_198){return E(_197)==E(_198);},_199=function(_19a,_19b){var _19c=E(_19a);switch(_19c._){case 0:var _19d=E(_19b);if(!_19d._){return new F(function(){return _sH(_19c.a,_19d.a);});}else{return false;}break;case 1:var _19e=E(_19b);if(_19e._==1){return new F(function(){return _jn(_19c.a,_19e.a);});}else{return false;}break;default:var _19f=E(_19b);if(_19f._==2){return new F(function(){return _196(_19c.a,_19f.a);});}else{return false;}}},_19g=function(_19h,_19i,_19j){while(1){var _19k=E(_19i);if(!_19k._){return (E(_19j)._==0)?true:false;}else{var _19l=E(_19j);if(!_19l._){return false;}else{if(!B(A3(_qe,_19h,_19k.a,_19l.a))){return false;}else{_19i=_19k.b;_19j=_19l.b;continue;}}}}},_19m=function(_19n,_19o){return (!B(_19p(_19n,_19o)))?true:false;},_19q=new T2(0,_19p,_19m),_19r=new T(function(){return E(_19q);}),_19s=function(_19t,_19u){return (E(_19t)==0)?(E(_19u)==0)?false:true:(E(_19u)==0)?true:false;},_19v=function(_19w,_19x){return (E(_19w)==0)?(E(_19x)==0)?true:false:(E(_19x)==0)?false:true;},_19y=new T2(0,_19v,_19s),_19z=new T(function(){return E(_19y);}),_19A=function(_19B,_19C,_19D,_19E,_19F,_19G){if(!B(A3(_qe,_19z,_19B,_19E))){return false;}else{var _19H=E(_19C),_19I=E(_19F);if(!B(_13e(_19H.a,_19H.b,_19H.c,_19I.a,_19I.b,_19I.c))){return false;}else{return new F(function(){return _19J(_19D,_19G);});}}},_19K=function(_19L,_19M){var _19N=E(_19L),_19O=E(_19M);return new F(function(){return _19A(_19N.a,_19N.b,_19N.c,_19O.a,_19O.b,_19O.c);});},_19P=function(_19Q,_19R,_19S,_19T,_19U,_19V){if(!B(A3(_qe,_19z,_19Q,_19T))){return true;}else{var _19W=E(_19R),_19X=E(_19U);if(!B(_13e(_19W.a,_19W.b,_19W.c,_19X.a,_19X.b,_19X.c))){return true;}else{var _19Y=E(_19S);return (!B(_19Z(_19Y.a,_19Y.b,_19Y.c,_19V)))?true:false;}}},_1a0=function(_1a1,_1a2){var _1a3=E(_1a1),_1a4=E(_1a2);return new F(function(){return _19P(_1a3.a,_1a3.b,_1a3.c,_1a4.a,_1a4.b,_1a4.c);});},_1a5=new T(function(){return new T2(0,_19K,_1a0);}),_19Z=function(_1a6,_1a7,_1a8,_1a9){var _1aa=E(_1a9);if(!B(_19g(_1a5,_1a6,_1aa.a))){return false;}else{var _1ab=E(_1a7),_1ac=E(_1aa.b);if(!B(_13e(_1ab.a,_1ab.b,_1ab.c,_1ac.a,_1ac.b,_1ac.c))){return false;}else{return new F(function(){return _19g(_19r,_1a8,_1aa.c);});}}},_19J=function(_1ad,_1ae){var _1af=E(_1ad);return new F(function(){return _19Z(_1af.a,_1af.b,_1af.c,_1ae);});},_19p=function(_1ag,_1ah){while(1){var _1ai=E(_1ag);switch(_1ai._){case 0:var _1aj=_1ai.b,_1ak=_1ai.c,_1al=E(_1ah);if(!_1al._){var _1am=_1al.a,_1an=_1al.b,_1ao=_1al.c;if(!E(_1ai.a)){if(!E(_1am)){var _1ap=E(_1aj),_1aq=E(_1an);if(!B(_13e(_1ap.a,_1ap.b,_1ap.c,_1aq.a,_1aq.b,_1aq.c))){return false;}else{_1ag=_1ak;_1ah=_1ao;continue;}}else{return false;}}else{if(!E(_1am)){return false;}else{var _1ar=E(_1aj),_1as=E(_1an);if(!B(_13e(_1ar.a,_1ar.b,_1ar.c,_1as.a,_1as.b,_1as.c))){return false;}else{_1ag=_1ak;_1ah=_1ao;continue;}}}}else{return false;}break;case 1:var _1at=E(_1ah);if(_1at._==1){if(!B(_19p(_1ai.a,_1at.a))){return false;}else{_1ag=_1ai.b;_1ah=_1at.b;continue;}}else{return false;}break;case 2:var _1au=E(_1ah);if(_1au._==2){return new F(function(){return _199(_1ai.a,_1au.a);});}else{return false;}break;case 3:var _1av=E(_1ah);return (_1av._==3)?_1ai.a==_1av.a:false;case 4:var _1aw=E(_1ah);if(_1aw._==4){return new F(function(){return _191(_1ai.a,_1aw.a);});}else{return false;}break;case 5:var _1ax=E(_1ah);return (_1ax._==5)?_1ai.a==_1ax.a:false;case 6:var _1ay=E(_1ah);if(_1ay._==6){if(!B(_19p(_1ai.a,_1ay.a))){return false;}else{return new F(function(){return _19J(_1ai.b,_1ay.b);});}}else{return false;}break;default:var _1az=E(_1ah);if(_1az._==7){_1ag=_1ai.a;_1ah=_1az.a;continue;}else{return false;}}}},_1aA=function(_1aB,_1aC,_1aD,_1aE){return (_1aB!=_1aD)?true:(E(_1aC)!=E(_1aE))?true:false;},_1aF=function(_1aG,_1aH){var _1aI=E(_1aG),_1aJ=E(_1aH);return new F(function(){return _1aA(E(_1aI.a),_1aI.b,E(_1aJ.a),_1aJ.b);});},_1aK=function(_1aL,_1aM,_1aN,_1aO){if(_1aL!=_1aN){return false;}else{return new F(function(){return _jn(_1aM,_1aO);});}},_1aP=function(_1aQ,_1aR){var _1aS=E(_1aQ),_1aT=E(_1aR);return new F(function(){return _1aK(E(_1aS.a),_1aS.b,E(_1aT.a),_1aT.b);});},_1aU=new T2(0,_1aP,_1aF),_1aV=function(_1aW,_1aX,_1aY,_1aZ){return (!B(_19g(_1aU,_1aW,_1aY)))?true:(_1aX!=_1aZ)?true:false;},_1b0=function(_1b1,_1b2){var _1b3=E(_1b1),_1b4=E(_1b2);return new F(function(){return _1aV(_1b3.a,_1b3.b,_1b4.a,_1b4.b);});},_1b5=function(_1b6,_1b7){var _1b8=E(_1b6),_1b9=E(_1b7);return (!B(_19g(_1aU,_1b8.a,_1b9.a)))?false:_1b8.b==_1b9.b;},_1ba=new T2(0,_1b5,_1b0),_1bb=function(_1bc,_1bd){while(1){var _1be=E(_1bc);if(!_1be._){return (E(_1bd)._==0)?true:false;}else{var _1bf=E(_1bd);if(!_1bf._){return false;}else{if(!B(_sT(_1be.a,_1bf.a))){return false;}else{_1bc=_1be.b;_1bd=_1bf.b;continue;}}}}},_1bg=function(_1bh,_1bi){var _1bj=E(_1bh);switch(_1bj._){case 0:var _1bk=E(_1bi);if(!_1bk._){if(_1bj.a!=_1bk.a){return false;}else{return new F(function(){return _19g(_1ba,_1bj.b,_1bk.b);});}}else{return false;}break;case 1:var _1bl=E(_1bi);return (_1bl._==1)?_1bj.a==_1bl.a:false;default:var _1bm=E(_1bi);if(_1bm._==2){var _1bn=E(_1bj.a),_1bo=E(_1bm.a);if(!B(_13e(_1bn.a,_1bn.b,_1bn.c,_1bo.a,_1bo.b,_1bo.c))){return false;}else{if(!B(_19p(_1bj.b,_1bm.b))){return false;}else{return new F(function(){return _1bb(_1bj.c,_1bm.c);});}}}else{return false;}}},_1bp=function(_1bq,_1br){return (!B(_1bg(_1bq,_1br)))?true:false;},_1bs=new T2(0,_1bg,_1bp),_1bt=function(_1bu,_1bv){var _1bw=E(_1bu),_1bx=E(_1bv);return new F(function(){return _13l(_1bw.a,_1bw.b,_1bw.c,_1bx.a,_1bx.b,_1bx.c);});},_1by=function(_1bz,_1bA){var _1bB=E(_1bz),_1bC=E(_1bA);return (_1bB>=_1bC)?(_1bB!=_1bC)?2:1:0;},_1bD=function(_1bE,_1bF){var _1bG=E(_1bE);switch(_1bG._){case 0:var _1bH=E(_1bF);if(!_1bH._){return new F(function(){return _12F(_1bG.a,_1bH.a);});}else{return 0;}break;case 1:var _1bI=E(_1bF);switch(_1bI._){case 0:return 2;case 1:return new F(function(){return _jH(_1bG.a,_1bI.a);});break;default:return 0;}break;default:var _1bJ=E(_1bF);if(_1bJ._==2){return new F(function(){return _1by(_1bG.a,_1bJ.a);});}else{return 2;}}},_1bK=function(_1bL,_1bM){return (B(_1bN(_1bL,_1bM))==0)?true:false;},_1bO=function(_1bP,_1bQ){return (B(_1bN(_1bP,_1bQ))==2)?false:true;},_1bR=function(_1bS,_1bT){return (B(_1bN(_1bS,_1bT))==2)?true:false;},_1bU=function(_1bV,_1bW){return (B(_1bN(_1bV,_1bW))==0)?false:true;},_1bX=function(_1bY,_1bZ){return (B(_1bN(_1bY,_1bZ))==2)?E(_1bY):E(_1bZ);},_1c0=function(_1c1,_1c2){return (B(_1bN(_1c1,_1c2))==2)?E(_1c2):E(_1c1);},_1c3={_:0,a:_19q,b:_1bN,c:_1bK,d:_1bO,e:_1bR,f:_1bU,g:_1bX,h:_1c0},_1c4=new T(function(){return E(_1c3);}),_1c5=function(_1c6,_1c7,_1c8){while(1){var _1c9=E(_1c7);if(!_1c9._){return (E(_1c8)._==0)?1:0;}else{var _1ca=E(_1c8);if(!_1ca._){return 2;}else{var _1cb=B(A3(_13P,_1c6,_1c9.a,_1ca.a));if(_1cb==1){_1c7=_1c9.b;_1c8=_1ca.b;continue;}else{return E(_1cb);}}}}},_1cc=function(_1cd,_1ce,_1cf,_1cg){var _1ch=E(_1cg);switch(B(_1c5(_1ci,_1cd,_1ch.a))){case 0:return false;case 1:var _1cj=E(_1ce),_1ck=E(_1ch.b);switch(B(_13l(_1cj.a,_1cj.b,_1cj.c,_1ck.a,_1ck.b,_1ck.c))){case 0:return false;case 1:return (B(_1c5(_1c4,_1cf,_1ch.c))==0)?false:true;default:return true;}break;default:return true;}},_1cl=function(_1cm,_1cn){var _1co=E(_1cm);return new F(function(){return _1cc(_1co.a,_1co.b,_1co.c,_1cn);});},_1cp=function(_1cq,_1cr){if(!E(_1cq)){return (E(_1cr)==0)?false:true;}else{var _1cs=E(_1cr);return false;}},_1ct=function(_1cu,_1cv){if(!E(_1cu)){var _1cw=E(_1cv);return true;}else{return (E(_1cv)==0)?false:true;}},_1cx=function(_1cy,_1cz){if(!E(_1cy)){var _1cA=E(_1cz);return false;}else{return (E(_1cz)==0)?true:false;}},_1cB=function(_1cC,_1cD){if(!E(_1cC)){return (E(_1cD)==0)?true:false;}else{var _1cE=E(_1cD);return true;}},_1cF=function(_1cG,_1cH){return (E(_1cG)==0)?(E(_1cH)==0)?1:0:(E(_1cH)==0)?2:1;},_1cI=function(_1cJ,_1cK){if(!E(_1cJ)){return E(_1cK);}else{var _1cL=E(_1cK);return 1;}},_1cM=function(_1cN,_1cO){if(!E(_1cN)){var _1cP=E(_1cO);return 0;}else{return E(_1cO);}},_1cQ={_:0,a:_19y,b:_1cF,c:_1cp,d:_1ct,e:_1cx,f:_1cB,g:_1cI,h:_1cM},_1cR=new T(function(){return E(_1cQ);}),_1cS=function(_1cT,_1cU,_1cV,_1cW,_1cX,_1cY){switch(B(A3(_13P,_1cR,_1cT,_1cW))){case 0:return false;case 1:var _1cZ=E(_1cU),_1d0=E(_1cX);switch(B(_13l(_1cZ.a,_1cZ.b,_1cZ.c,_1d0.a,_1d0.b,_1d0.c))){case 0:return false;case 1:return new F(function(){return _1cl(_1cV,_1cY);});break;default:return true;}break;default:return true;}},_1d1=function(_1d2,_1d3){var _1d4=E(_1d2),_1d5=E(_1d3);return new F(function(){return _1cS(_1d4.a,_1d4.b,_1d4.c,_1d5.a,_1d5.b,_1d5.c);});},_1d6=function(_1d7,_1d8,_1d9,_1da){var _1db=E(_1da);switch(B(_1c5(_1ci,_1d7,_1db.a))){case 0:return false;case 1:var _1dc=E(_1d8),_1dd=E(_1db.b);switch(B(_13l(_1dc.a,_1dc.b,_1dc.c,_1dd.a,_1dd.b,_1dd.c))){case 0:return false;case 1:return (B(_1c5(_1c4,_1d9,_1db.c))==2)?true:false;default:return true;}break;default:return true;}},_1de=function(_1df,_1dg){var _1dh=E(_1df);return new F(function(){return _1d6(_1dh.a,_1dh.b,_1dh.c,_1dg);});},_1di=function(_1dj,_1dk,_1dl,_1dm,_1dn,_1do){switch(B(A3(_13P,_1cR,_1dj,_1dm))){case 0:return false;case 1:var _1dp=E(_1dk),_1dq=E(_1dn);switch(B(_13l(_1dp.a,_1dp.b,_1dp.c,_1dq.a,_1dq.b,_1dq.c))){case 0:return false;case 1:return new F(function(){return _1de(_1dl,_1do);});break;default:return true;}break;default:return true;}},_1dr=function(_1ds,_1dt){var _1du=E(_1ds),_1dv=E(_1dt);return new F(function(){return _1di(_1du.a,_1du.b,_1du.c,_1dv.a,_1dv.b,_1dv.c);});},_1dw=function(_1dx,_1dy,_1dz,_1dA){var _1dB=E(_1dA);switch(B(_1c5(_1ci,_1dx,_1dB.a))){case 0:return true;case 1:var _1dC=E(_1dy),_1dD=E(_1dB.b);switch(B(_13l(_1dC.a,_1dC.b,_1dC.c,_1dD.a,_1dD.b,_1dD.c))){case 0:return true;case 1:return (B(_1c5(_1c4,_1dz,_1dB.c))==2)?false:true;default:return false;}break;default:return false;}},_1dE=function(_1dF,_1dG){var _1dH=E(_1dF);return new F(function(){return _1dw(_1dH.a,_1dH.b,_1dH.c,_1dG);});},_1dI=function(_1dJ,_1dK,_1dL,_1dM,_1dN,_1dO){switch(B(A3(_13P,_1cR,_1dJ,_1dM))){case 0:return true;case 1:var _1dP=E(_1dK),_1dQ=E(_1dN);switch(B(_13l(_1dP.a,_1dP.b,_1dP.c,_1dQ.a,_1dQ.b,_1dQ.c))){case 0:return true;case 1:return new F(function(){return _1dE(_1dL,_1dO);});break;default:return false;}break;default:return false;}},_1dR=function(_1dS,_1dT){var _1dU=E(_1dS),_1dV=E(_1dT);return new F(function(){return _1dI(_1dU.a,_1dU.b,_1dU.c,_1dV.a,_1dV.b,_1dV.c);});},_1dW=function(_1dX,_1dY){var _1dZ=E(_1dX),_1e0=_1dZ.a,_1e1=_1dZ.c,_1e2=E(_1dY),_1e3=_1e2.a,_1e4=_1e2.c;switch(B(A3(_13P,_1cR,_1e0,_1e3))){case 0:return E(_1e2);case 1:var _1e5=E(_1dZ.b),_1e6=E(_1e2.b);switch(B(_13l(_1e5.a,_1e5.b,_1e5.c,_1e6.a,_1e6.b,_1e6.c))){case 0:return new T3(0,_1e3,_1e6,_1e4);case 1:var _1e7=E(_1e1);return (!B(_1dw(_1e7.a,_1e7.b,_1e7.c,_1e4)))?new T3(0,_1e0,_1e5,_1e7):new T3(0,_1e3,_1e6,_1e4);default:return new T3(0,_1e0,_1e5,_1e1);}break;default:return E(_1dZ);}},_1e8=function(_1e9,_1ea){var _1eb=E(_1e9),_1ec=_1eb.a,_1ed=_1eb.c,_1ee=E(_1ea),_1ef=_1ee.a,_1eg=_1ee.c;switch(B(A3(_13P,_1cR,_1ec,_1ef))){case 0:return E(_1eb);case 1:var _1eh=E(_1eb.b),_1ei=E(_1ee.b);switch(B(_13l(_1eh.a,_1eh.b,_1eh.c,_1ei.a,_1ei.b,_1ei.c))){case 0:return new T3(0,_1ec,_1eh,_1ed);case 1:var _1ej=E(_1ed);return (!B(_1dw(_1ej.a,_1ej.b,_1ej.c,_1eg)))?new T3(0,_1ef,_1ei,_1eg):new T3(0,_1ec,_1eh,_1ej);default:return new T3(0,_1ef,_1ei,_1eg);}break;default:return E(_1ee);}},_1ek=function(_1el,_1em,_1en,_1eo){var _1ep=E(_1eo);switch(B(_1c5(_1ci,_1el,_1ep.a))){case 0:return true;case 1:var _1eq=E(_1em),_1er=E(_1ep.b);switch(B(_13l(_1eq.a,_1eq.b,_1eq.c,_1er.a,_1er.b,_1er.c))){case 0:return true;case 1:return (B(_1c5(_1c4,_1en,_1ep.c))==0)?true:false;default:return false;}break;default:return false;}},_1es=function(_1et,_1eu){var _1ev=E(_1et);return new F(function(){return _1ek(_1ev.a,_1ev.b,_1ev.c,_1eu);});},_1ew=function(_1ex,_1ey,_1ez,_1eA,_1eB,_1eC){switch(B(A3(_13P,_1cR,_1ex,_1eA))){case 0:return true;case 1:var _1eD=E(_1ey),_1eE=E(_1eB);switch(B(_13l(_1eD.a,_1eD.b,_1eD.c,_1eE.a,_1eE.b,_1eE.c))){case 0:return true;case 1:return new F(function(){return _1es(_1ez,_1eC);});break;default:return false;}break;default:return false;}},_1eF=function(_1eG,_1eH){var _1eI=E(_1eG),_1eJ=E(_1eH);return new F(function(){return _1ew(_1eI.a,_1eI.b,_1eI.c,_1eJ.a,_1eJ.b,_1eJ.c);});},_1eK=function(_1eL,_1eM,_1eN,_1eO,_1eP,_1eQ){switch(B(A3(_13P,_1cR,_1eL,_1eO))){case 0:return 0;case 1:var _1eR=E(_1eM),_1eS=E(_1eP);switch(B(_13l(_1eR.a,_1eR.b,_1eR.c,_1eS.a,_1eS.b,_1eS.c))){case 0:return 0;case 1:return new F(function(){return _1eT(_1eN,_1eQ);});break;default:return 2;}break;default:return 2;}},_1eU=function(_1eV,_1eW){var _1eX=E(_1eV),_1eY=E(_1eW);return new F(function(){return _1eK(_1eX.a,_1eX.b,_1eX.c,_1eY.a,_1eY.b,_1eY.c);});},_1ci=new T(function(){return {_:0,a:_1a5,b:_1eU,c:_1eF,d:_1dR,e:_1dr,f:_1d1,g:_1dW,h:_1e8};}),_1eZ=function(_1f0,_1f1,_1f2,_1f3){var _1f4=E(_1f3);switch(B(_1c5(_1ci,_1f0,_1f4.a))){case 0:return 0;case 1:var _1f5=E(_1f1),_1f6=E(_1f4.b);switch(B(_13l(_1f5.a,_1f5.b,_1f5.c,_1f6.a,_1f6.b,_1f6.c))){case 0:return 0;case 1:return new F(function(){return _1c5(_1c4,_1f2,_1f4.c);});break;default:return 2;}break;default:return 2;}},_1eT=function(_1f7,_1f8){var _1f9=E(_1f7);return new F(function(){return _1eZ(_1f9.a,_1f9.b,_1f9.c,_1f8);});},_1bN=function(_1fa,_1fb){while(1){var _1fc=B((function(_1fd,_1fe){var _1ff=E(_1fd);switch(_1ff._){case 0:var _1fg=E(_1fe);if(!_1fg._){var _1fh=_1fg.a,_1fi=function(_1fj){var _1fk=E(_1ff.b),_1fl=E(_1fg.b);switch(B(_13l(_1fk.a,_1fk.b,_1fk.c,_1fl.a,_1fl.b,_1fl.c))){case 0:return 0;case 1:return new F(function(){return _1bN(_1ff.c,_1fg.c);});break;default:return 2;}};if(!E(_1ff.a)){if(!E(_1fh)){return new F(function(){return _1fi(_);});}else{return 0;}}else{if(!E(_1fh)){return 2;}else{return new F(function(){return _1fi(_);});}}}else{return 0;}break;case 1:var _1fm=E(_1fe);switch(_1fm._){case 0:return 2;case 1:switch(B(_1bN(_1ff.a,_1fm.a))){case 0:return 0;case 1:_1fa=_1ff.b;_1fb=_1fm.b;return __continue;default:return 2;}break;default:return 0;}break;case 2:var _1fn=E(_1fe);switch(_1fn._){case 2:return new F(function(){return _1bD(_1ff.a,_1fn.a);});break;case 3:return 0;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 3:var _1fo=E(_1fe);switch(_1fo._){case 3:return new F(function(){return _jE(_1ff.a,_1fo.a);});break;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 4:var _1fp=E(_1fe);switch(_1fp._){case 4:return new F(function(){return _1bt(_1ff.a,_1fp.a);});break;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 5:var _1fq=E(_1fe);switch(_1fq._){case 5:return new F(function(){return _jE(_1ff.a,_1fq.a);});break;case 6:return 0;case 7:return 0;default:return 2;}break;case 6:var _1fr=E(_1fe);switch(_1fr._){case 6:switch(B(_1bN(_1ff.a,_1fr.a))){case 0:return 0;case 1:return new F(function(){return _1eT(_1ff.b,_1fr.b);});break;default:return 2;}break;case 7:return 0;default:return 2;}break;default:var _1fs=E(_1fe);if(_1fs._==7){_1fa=_1ff.a;_1fb=_1fs.a;return __continue;}else{return 2;}}})(_1fa,_1fb));if(_1fc!=__continue){return _1fc;}}},_1ft=function(_1fu,_1fv,_1fw,_1fx){if(_1fu>=_1fw){if(_1fu!=_1fw){return 2;}else{return new F(function(){return _jH(_1fv,_1fx);});}}else{return 0;}},_1fy=function(_1fz,_1fA){var _1fB=E(_1fz),_1fC=E(_1fA);return new F(function(){return _1ft(E(_1fB.a),_1fB.b,E(_1fC.a),_1fC.b);});},_1fD=function(_1fE,_1fF,_1fG,_1fH){if(_1fE>=_1fG){if(_1fE!=_1fG){return false;}else{return new F(function(){return _jT(_1fF,_1fH);});}}else{return true;}},_1fI=function(_1fJ,_1fK){var _1fL=E(_1fJ),_1fM=E(_1fK);return new F(function(){return _1fD(E(_1fL.a),_1fL.b,E(_1fM.a),_1fM.b);});},_1fN=function(_1fO,_1fP,_1fQ,_1fR){if(_1fO>=_1fQ){if(_1fO!=_1fQ){return false;}else{return new F(function(){return _jQ(_1fP,_1fR);});}}else{return true;}},_1fS=function(_1fT,_1fU){var _1fV=E(_1fT),_1fW=E(_1fU);return new F(function(){return _1fN(E(_1fV.a),_1fV.b,E(_1fW.a),_1fW.b);});},_1fX=function(_1fY,_1fZ,_1g0,_1g1){if(_1fY>=_1g0){if(_1fY!=_1g0){return true;}else{return new F(function(){return _jN(_1fZ,_1g1);});}}else{return false;}},_1g2=function(_1g3,_1g4){var _1g5=E(_1g3),_1g6=E(_1g4);return new F(function(){return _1fX(E(_1g5.a),_1g5.b,E(_1g6.a),_1g6.b);});},_1g7=function(_1g8,_1g9,_1ga,_1gb){if(_1g8>=_1ga){if(_1g8!=_1ga){return true;}else{return new F(function(){return _jK(_1g9,_1gb);});}}else{return false;}},_1gc=function(_1gd,_1ge){var _1gf=E(_1gd),_1gg=E(_1ge);return new F(function(){return _1g7(E(_1gf.a),_1gf.b,E(_1gg.a),_1gg.b);});},_1gh=function(_1gi,_1gj){var _1gk=E(_1gi),_1gl=E(_1gk.a),_1gm=E(_1gj),_1gn=E(_1gm.a);return (_1gl>=_1gn)?(_1gl!=_1gn)?E(_1gk):(E(_1gk.b)>E(_1gm.b))?E(_1gk):E(_1gm):E(_1gm);},_1go=function(_1gp,_1gq){var _1gr=E(_1gp),_1gs=E(_1gr.a),_1gt=E(_1gq),_1gu=E(_1gt.a);return (_1gs>=_1gu)?(_1gs!=_1gu)?E(_1gt):(E(_1gr.b)>E(_1gt.b))?E(_1gt):E(_1gr):E(_1gr);},_1gv={_:0,a:_1aU,b:_1fy,c:_1fI,d:_1fS,e:_1g2,f:_1gc,g:_1gh,h:_1go},_1gw=function(_1gx,_1gy,_1gz,_1gA){switch(B(_1c5(_1gv,_1gx,_1gz))){case 0:return true;case 1:return _1gy<_1gA;default:return false;}},_1gB=function(_1gC,_1gD){var _1gE=E(_1gC),_1gF=E(_1gD);return new F(function(){return _1gw(_1gE.a,_1gE.b,_1gF.a,_1gF.b);});},_1gG=function(_1gH,_1gI,_1gJ,_1gK){switch(B(_1c5(_1gv,_1gH,_1gJ))){case 0:return true;case 1:return _1gI<=_1gK;default:return false;}},_1gL=function(_1gM,_1gN){var _1gO=E(_1gM),_1gP=E(_1gN);return new F(function(){return _1gG(_1gO.a,_1gO.b,_1gP.a,_1gP.b);});},_1gQ=function(_1gR,_1gS,_1gT,_1gU){switch(B(_1c5(_1gv,_1gR,_1gT))){case 0:return false;case 1:return _1gS>_1gU;default:return true;}},_1gV=function(_1gW,_1gX){var _1gY=E(_1gW),_1gZ=E(_1gX);return new F(function(){return _1gQ(_1gY.a,_1gY.b,_1gZ.a,_1gZ.b);});},_1h0=function(_1h1,_1h2,_1h3,_1h4){switch(B(_1c5(_1gv,_1h1,_1h3))){case 0:return false;case 1:return _1h2>=_1h4;default:return true;}},_1h5=function(_1h6,_1h7){var _1h8=E(_1h6),_1h9=E(_1h7);return new F(function(){return _1h0(_1h8.a,_1h8.b,_1h9.a,_1h9.b);});},_1ha=function(_1hb,_1hc,_1hd,_1he){switch(B(_1c5(_1gv,_1hb,_1hd))){case 0:return 0;case 1:return new F(function(){return _jE(_1hc,_1he);});break;default:return 2;}},_1hf=function(_1hg,_1hh){var _1hi=E(_1hg),_1hj=E(_1hh);return new F(function(){return _1ha(_1hi.a,_1hi.b,_1hj.a,_1hj.b);});},_1hk=function(_1hl,_1hm){var _1hn=E(_1hl),_1ho=E(_1hm);switch(B(_1c5(_1gv,_1hn.a,_1ho.a))){case 0:return E(_1ho);case 1:return (_1hn.b>_1ho.b)?E(_1hn):E(_1ho);default:return E(_1hn);}},_1hp=function(_1hq,_1hr){var _1hs=E(_1hq),_1ht=E(_1hr);switch(B(_1c5(_1gv,_1hs.a,_1ht.a))){case 0:return E(_1hs);case 1:return (_1hs.b>_1ht.b)?E(_1ht):E(_1hs);default:return E(_1ht);}},_1hu={_:0,a:_1ba,b:_1hf,c:_1gB,d:_1gL,e:_1gV,f:_1h5,g:_1hk,h:_1hp},_1hv=function(_1hw,_1hx){while(1){var _1hy=E(_1hw);if(!_1hy._){return (E(_1hx)._==0)?1:0;}else{var _1hz=E(_1hx);if(!_1hz._){return 2;}else{var _1hA=B(_12F(_1hy.a,_1hz.a));if(_1hA==1){_1hw=_1hy.b;_1hx=_1hz.b;continue;}else{return E(_1hA);}}}}},_1hB=function(_1hC,_1hD){return (B(_1hv(_1hC,_1hD))==0)?true:false;},_1hE=function(_1hF,_1hG){var _1hH=E(_1hF);switch(_1hH._){case 0:var _1hI=_1hH.a,_1hJ=E(_1hG);if(!_1hJ._){var _1hK=_1hJ.a;return (_1hI>=_1hK)?(_1hI!=_1hK)?false:(B(_1c5(_1hu,_1hH.b,_1hJ.b))==0)?true:false:true;}else{return true;}break;case 1:var _1hL=E(_1hG);switch(_1hL._){case 0:return false;case 1:return _1hH.a<_1hL.a;default:return true;}break;default:var _1hM=E(_1hG);if(_1hM._==2){var _1hN=E(_1hH.a),_1hO=E(_1hM.a);switch(B(_13l(_1hN.a,_1hN.b,_1hN.c,_1hO.a,_1hO.b,_1hO.c))){case 0:return true;case 1:switch(B(_1bN(_1hH.b,_1hM.b))){case 0:return true;case 1:return new F(function(){return _1hB(_1hH.c,_1hM.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1hP=function(_1hQ,_1hR){return (B(_1hv(_1hQ,_1hR))==2)?false:true;},_1hS=function(_1hT,_1hU){var _1hV=E(_1hT);switch(_1hV._){case 0:var _1hW=_1hV.a,_1hX=E(_1hU);if(!_1hX._){var _1hY=_1hX.a;return (_1hW>=_1hY)?(_1hW!=_1hY)?false:(B(_1c5(_1hu,_1hV.b,_1hX.b))==2)?false:true:true;}else{return true;}break;case 1:var _1hZ=E(_1hU);switch(_1hZ._){case 0:return false;case 1:return _1hV.a<=_1hZ.a;default:return true;}break;default:var _1i0=E(_1hU);if(_1i0._==2){var _1i1=E(_1hV.a),_1i2=E(_1i0.a);switch(B(_13l(_1i1.a,_1i1.b,_1i1.c,_1i2.a,_1i2.b,_1i2.c))){case 0:return true;case 1:switch(B(_1bN(_1hV.b,_1i0.b))){case 0:return true;case 1:return new F(function(){return _1hP(_1hV.c,_1i0.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1i3=function(_1i4,_1i5){return (B(_1hv(_1i4,_1i5))==2)?true:false;},_1i6=function(_1i7,_1i8){var _1i9=E(_1i7);switch(_1i9._){case 0:var _1ia=_1i9.a,_1ib=E(_1i8);if(!_1ib._){var _1ic=_1ib.a;return (_1ia>=_1ic)?(_1ia!=_1ic)?true:(B(_1c5(_1hu,_1i9.b,_1ib.b))==2)?true:false:false;}else{return false;}break;case 1:var _1id=E(_1i8);switch(_1id._){case 0:return true;case 1:return _1i9.a>_1id.a;default:return false;}break;default:var _1ie=E(_1i8);if(_1ie._==2){var _1if=E(_1i9.a),_1ig=E(_1ie.a);switch(B(_13l(_1if.a,_1if.b,_1if.c,_1ig.a,_1ig.b,_1ig.c))){case 0:return false;case 1:switch(B(_1bN(_1i9.b,_1ie.b))){case 0:return false;case 1:return new F(function(){return _1i3(_1i9.c,_1ie.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1ih=function(_1ii,_1ij){return (B(_1hv(_1ii,_1ij))==0)?false:true;},_1ik=function(_1il,_1im){var _1in=E(_1il);switch(_1in._){case 0:var _1io=_1in.a,_1ip=E(_1im);if(!_1ip._){var _1iq=_1ip.a;return (_1io>=_1iq)?(_1io!=_1iq)?true:(B(_1c5(_1hu,_1in.b,_1ip.b))==0)?false:true:false;}else{return false;}break;case 1:var _1ir=E(_1im);switch(_1ir._){case 0:return true;case 1:return _1in.a>=_1ir.a;default:return false;}break;default:var _1is=E(_1im);if(_1is._==2){var _1it=E(_1in.a),_1iu=E(_1is.a);switch(B(_13l(_1it.a,_1it.b,_1it.c,_1iu.a,_1iu.b,_1iu.c))){case 0:return false;case 1:switch(B(_1bN(_1in.b,_1is.b))){case 0:return false;case 1:return new F(function(){return _1ih(_1in.c,_1is.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1iv=function(_1iw,_1ix){var _1iy=E(_1iw);switch(_1iy._){case 0:var _1iz=_1iy.a,_1iA=E(_1ix);if(!_1iA._){var _1iB=_1iA.a;if(_1iz>=_1iB){if(_1iz!=_1iB){return 2;}else{return new F(function(){return _1c5(_1hu,_1iy.b,_1iA.b);});}}else{return 0;}}else{return 0;}break;case 1:var _1iC=E(_1ix);switch(_1iC._){case 0:return 2;case 1:return new F(function(){return _jE(_1iy.a,_1iC.a);});break;default:return 0;}break;default:var _1iD=E(_1ix);if(_1iD._==2){var _1iE=E(_1iy.a),_1iF=E(_1iD.a);switch(B(_13l(_1iE.a,_1iE.b,_1iE.c,_1iF.a,_1iF.b,_1iF.c))){case 0:return 0;case 1:switch(B(_1bN(_1iy.b,_1iD.b))){case 0:return 0;case 1:return new F(function(){return _1hv(_1iy.c,_1iD.c);});break;default:return 2;}break;default:return 2;}}else{return 2;}}},_1iG=function(_1iH,_1iI){return (!B(_1hS(_1iH,_1iI)))?E(_1iH):E(_1iI);},_1iJ=function(_1iK,_1iL){return (!B(_1hS(_1iK,_1iL)))?E(_1iL):E(_1iK);},_1iM={_:0,a:_1bs,b:_1iv,c:_1hE,d:_1hS,e:_1i6,f:_1ik,g:_1iG,h:_1iJ},_1iN=__Z,_1iO=function(_1iP,_1iQ,_1iR){var _1iS=E(_1iQ);if(!_1iS._){return E(_1iR);}else{var _1iT=function(_1iU,_1iV){while(1){var _1iW=E(_1iV);if(!_1iW._){var _1iX=_1iW.b,_1iY=_1iW.d;switch(B(A3(_13P,_1iP,_1iU,_1iX))){case 0:return new F(function(){return _Pe(_1iX,B(_1iT(_1iU,_1iW.c)),_1iY);});break;case 1:return E(_1iY);default:_1iV=_1iY;continue;}}else{return new T0(1);}}};return new F(function(){return _1iT(_1iS.a,_1iR);});}},_1iZ=function(_1j0,_1j1,_1j2){var _1j3=E(_1j1);if(!_1j3._){return E(_1j2);}else{var _1j4=function(_1j5,_1j6){while(1){var _1j7=E(_1j6);if(!_1j7._){var _1j8=_1j7.b,_1j9=_1j7.c;switch(B(A3(_13P,_1j0,_1j8,_1j5))){case 0:return new F(function(){return _Pe(_1j8,_1j9,B(_1j4(_1j5,_1j7.d)));});break;case 1:return E(_1j9);default:_1j6=_1j9;continue;}}else{return new T0(1);}}};return new F(function(){return _1j4(_1j3.a,_1j2);});}},_1ja=function(_1jb,_1jc,_1jd){var _1je=E(_1jc),_1jf=E(_1jd);if(!_1jf._){var _1jg=_1jf.b,_1jh=_1jf.c,_1ji=_1jf.d;switch(B(A3(_13P,_1jb,_1je,_1jg))){case 0:return new F(function(){return _Ni(_1jg,B(_1ja(_1jb,_1je,_1jh)),_1ji);});break;case 1:return E(_1jf);default:return new F(function(){return _NU(_1jg,_1jh,B(_1ja(_1jb,_1je,_1ji)));});}}else{return new T4(0,1,E(_1je),E(_Nd),E(_Nd));}},_1jj=function(_1jk,_1jl,_1jm){return new F(function(){return _1ja(_1jk,_1jl,_1jm);});},_1jn=function(_1jo,_1jp,_1jq,_1jr){var _1js=E(_1jp);if(!_1js._){var _1jt=E(_1jq);if(!_1jt._){return E(_1jr);}else{var _1ju=function(_1jv,_1jw){while(1){var _1jx=E(_1jw);if(!_1jx._){if(!B(A3(_16R,_1jo,_1jx.b,_1jv))){return E(_1jx);}else{_1jw=_1jx.c;continue;}}else{return new T0(1);}}};return new F(function(){return _1ju(_1jt.a,_1jr);});}}else{var _1jy=_1js.a,_1jz=E(_1jq);if(!_1jz._){var _1jA=function(_1jB,_1jC){while(1){var _1jD=E(_1jC);if(!_1jD._){if(!B(A3(_17A,_1jo,_1jD.b,_1jB))){return E(_1jD);}else{_1jC=_1jD.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1jA(_1jy,_1jr);});}else{var _1jE=function(_1jF,_1jG,_1jH){while(1){var _1jI=E(_1jH);if(!_1jI._){var _1jJ=_1jI.b;if(!B(A3(_17A,_1jo,_1jJ,_1jF))){if(!B(A3(_16R,_1jo,_1jJ,_1jG))){return E(_1jI);}else{_1jH=_1jI.c;continue;}}else{_1jH=_1jI.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1jE(_1jy,_1jz.a,_1jr);});}}},_1jK=function(_1jL,_1jM,_1jN,_1jO,_1jP){var _1jQ=E(_1jP);if(!_1jQ._){var _1jR=_1jQ.b,_1jS=_1jQ.c,_1jT=_1jQ.d,_1jU=E(_1jO);if(!_1jU._){var _1jV=_1jU.b,_1jW=function(_1jX){var _1jY=new T1(1,E(_1jV));return new F(function(){return _Pe(_1jV,B(_1jK(_1jL,_1jM,_1jY,_1jU.c,B(_1jn(_1jL,_1jM,_1jY,_1jQ)))),B(_1jK(_1jL,_1jY,_1jN,_1jU.d,B(_1jn(_1jL,_1jY,_1jN,_1jQ)))));});};if(!E(_1jS)._){return new F(function(){return _1jW(_);});}else{if(!E(_1jT)._){return new F(function(){return _1jW(_);});}else{return new F(function(){return _1jj(_1jL,_1jR,_1jU);});}}}else{return new F(function(){return _Pe(_1jR,B(_1iO(_1jL,_1jM,_1jS)),B(_1iZ(_1jL,_1jN,_1jT)));});}}else{return E(_1jO);}},_1jZ=function(_1k0,_1k1,_1k2,_1k3,_1k4,_1k5,_1k6,_1k7,_1k8,_1k9,_1ka){var _1kb=function(_1kc){var _1kd=new T1(1,E(_1k4));return new F(function(){return _Pe(_1k4,B(_1jK(_1k0,_1k1,_1kd,_1k5,B(_1jn(_1k0,_1k1,_1kd,new T4(0,_1k7,E(_1k8),E(_1k9),E(_1ka)))))),B(_1jK(_1k0,_1kd,_1k2,_1k6,B(_1jn(_1k0,_1kd,_1k2,new T4(0,_1k7,E(_1k8),E(_1k9),E(_1ka)))))));});};if(!E(_1k9)._){return new F(function(){return _1kb(_);});}else{if(!E(_1ka)._){return new F(function(){return _1kb(_);});}else{return new F(function(){return _1jj(_1k0,_1k8,new T4(0,_1k3,E(_1k4),E(_1k5),E(_1k6)));});}}},_1ke=function(_1kf,_1kg,_1kh){var _1ki=E(_1kg);if(!_1ki._){var _1kj=E(_1kh);if(!_1kj._){return new F(function(){return _1jZ(_1iM,_1iN,_1iN,_1ki.a,_1ki.b,_1ki.c,_1ki.d,_1kj.a,_1kj.b,_1kj.c,_1kj.d);});}else{return E(_1ki);}}else{return E(_1kh);}},_1kk=function(_1kl,_1km,_1kn){var _1ko=function(_1kp,_1kq,_1kr,_1ks){var _1kt=E(_1ks);switch(_1kt._){case 0:var _1ku=_1kt.a,_1kv=_1kt.b,_1kw=_1kt.c,_1kx=_1kt.d,_1ky=_1kv>>>0;if(((_1kr>>>0&((_1ky-1>>>0^4294967295)>>>0^_1ky)>>>0)>>>0&4294967295)==_1ku){return ((_1kr>>>0&_1ky)>>>0==0)?new T4(0,_1ku,_1kv,E(B(_1ko(_1kp,_1kq,_1kr,_1kw))),E(_1kx)):new T4(0,_1ku,_1kv,E(_1kw),E(B(_1ko(_1kp,_1kq,_1kr,_1kx))));}else{var _1kz=(_1kr>>>0^_1ku>>>0)>>>0,_1kA=(_1kz|_1kz>>>1)>>>0,_1kB=(_1kA|_1kA>>>2)>>>0,_1kC=(_1kB|_1kB>>>4)>>>0,_1kD=(_1kC|_1kC>>>8)>>>0,_1kE=(_1kD|_1kD>>>16)>>>0,_1kF=(_1kE^_1kE>>>1)>>>0&4294967295,_1kG=_1kF>>>0;return ((_1kr>>>0&_1kG)>>>0==0)?new T4(0,(_1kr>>>0&((_1kG-1>>>0^4294967295)>>>0^_1kG)>>>0)>>>0&4294967295,_1kF,E(new T2(1,_1kp,_1kq)),E(_1kt)):new T4(0,(_1kr>>>0&((_1kG-1>>>0^4294967295)>>>0^_1kG)>>>0)>>>0&4294967295,_1kF,E(_1kt),E(new T2(1,_1kp,_1kq)));}break;case 1:var _1kH=_1kt.a;if(_1kr!=_1kH){var _1kI=(_1kr>>>0^_1kH>>>0)>>>0,_1kJ=(_1kI|_1kI>>>1)>>>0,_1kK=(_1kJ|_1kJ>>>2)>>>0,_1kL=(_1kK|_1kK>>>4)>>>0,_1kM=(_1kL|_1kL>>>8)>>>0,_1kN=(_1kM|_1kM>>>16)>>>0,_1kO=(_1kN^_1kN>>>1)>>>0&4294967295,_1kP=_1kO>>>0;return ((_1kr>>>0&_1kP)>>>0==0)?new T4(0,(_1kr>>>0&((_1kP-1>>>0^4294967295)>>>0^_1kP)>>>0)>>>0&4294967295,_1kO,E(new T2(1,_1kp,_1kq)),E(_1kt)):new T4(0,(_1kr>>>0&((_1kP-1>>>0^4294967295)>>>0^_1kP)>>>0)>>>0&4294967295,_1kO,E(_1kt),E(new T2(1,_1kp,_1kq)));}else{return new T2(1,_1kp,new T(function(){return B(A3(_1kl,_1kp,_1kq,_1kt.b));}));}break;default:return new T2(1,_1kp,_1kq);}},_1kQ=function(_1kR,_1kS,_1kT,_1kU){var _1kV=E(_1kU);switch(_1kV._){case 0:var _1kW=_1kV.a,_1kX=_1kV.b,_1kY=_1kV.c,_1kZ=_1kV.d,_1l0=_1kX>>>0;if(((_1kT>>>0&((_1l0-1>>>0^4294967295)>>>0^_1l0)>>>0)>>>0&4294967295)==_1kW){return ((_1kT>>>0&_1l0)>>>0==0)?new T4(0,_1kW,_1kX,E(B(_1kQ(_1kR,_1kS,_1kT,_1kY))),E(_1kZ)):new T4(0,_1kW,_1kX,E(_1kY),E(B(_1kQ(_1kR,_1kS,_1kT,_1kZ))));}else{var _1l1=(_1kW>>>0^_1kT>>>0)>>>0,_1l2=(_1l1|_1l1>>>1)>>>0,_1l3=(_1l2|_1l2>>>2)>>>0,_1l4=(_1l3|_1l3>>>4)>>>0,_1l5=(_1l4|_1l4>>>8)>>>0,_1l6=(_1l5|_1l5>>>16)>>>0,_1l7=(_1l6^_1l6>>>1)>>>0&4294967295,_1l8=_1l7>>>0;return ((_1kW>>>0&_1l8)>>>0==0)?new T4(0,(_1kW>>>0&((_1l8-1>>>0^4294967295)>>>0^_1l8)>>>0)>>>0&4294967295,_1l7,E(_1kV),E(new T2(1,_1kR,_1kS))):new T4(0,(_1kW>>>0&((_1l8-1>>>0^4294967295)>>>0^_1l8)>>>0)>>>0&4294967295,_1l7,E(new T2(1,_1kR,_1kS)),E(_1kV));}break;case 1:var _1l9=_1kV.a;if(_1l9!=_1kT){var _1la=(_1l9>>>0^_1kT>>>0)>>>0,_1lb=(_1la|_1la>>>1)>>>0,_1lc=(_1lb|_1lb>>>2)>>>0,_1ld=(_1lc|_1lc>>>4)>>>0,_1le=(_1ld|_1ld>>>8)>>>0,_1lf=(_1le|_1le>>>16)>>>0,_1lg=(_1lf^_1lf>>>1)>>>0&4294967295,_1lh=_1lg>>>0;return ((_1l9>>>0&_1lh)>>>0==0)?new T4(0,(_1l9>>>0&((_1lh-1>>>0^4294967295)>>>0^_1lh)>>>0)>>>0&4294967295,_1lg,E(_1kV),E(new T2(1,_1kR,_1kS))):new T4(0,(_1l9>>>0&((_1lh-1>>>0^4294967295)>>>0^_1lh)>>>0)>>>0&4294967295,_1lg,E(new T2(1,_1kR,_1kS)),E(_1kV));}else{return new T2(1,_1l9,new T(function(){return B(A3(_1kl,_1l9,_1kV.b,_1kS));}));}break;default:return new T2(1,_1kR,_1kS);}},_1li=function(_1lj,_1lk,_1ll,_1lm,_1ln,_1lo,_1lp){var _1lq=_1ln>>>0;if(((_1ll>>>0&((_1lq-1>>>0^4294967295)>>>0^_1lq)>>>0)>>>0&4294967295)==_1lm){return ((_1ll>>>0&_1lq)>>>0==0)?new T4(0,_1lm,_1ln,E(B(_1kQ(_1lj,_1lk,_1ll,_1lo))),E(_1lp)):new T4(0,_1lm,_1ln,E(_1lo),E(B(_1kQ(_1lj,_1lk,_1ll,_1lp))));}else{var _1lr=(_1lm>>>0^_1ll>>>0)>>>0,_1ls=(_1lr|_1lr>>>1)>>>0,_1lt=(_1ls|_1ls>>>2)>>>0,_1lu=(_1lt|_1lt>>>4)>>>0,_1lv=(_1lu|_1lu>>>8)>>>0,_1lw=(_1lv|_1lv>>>16)>>>0,_1lx=(_1lw^_1lw>>>1)>>>0&4294967295,_1ly=_1lx>>>0;return ((_1lm>>>0&_1ly)>>>0==0)?new T4(0,(_1lm>>>0&((_1ly-1>>>0^4294967295)>>>0^_1ly)>>>0)>>>0&4294967295,_1lx,E(new T4(0,_1lm,_1ln,E(_1lo),E(_1lp))),E(new T2(1,_1lj,_1lk))):new T4(0,(_1lm>>>0&((_1ly-1>>>0^4294967295)>>>0^_1ly)>>>0)>>>0&4294967295,_1lx,E(new T2(1,_1lj,_1lk)),E(new T4(0,_1lm,_1ln,E(_1lo),E(_1lp))));}},_1lz=function(_1lA,_1lB){var _1lC=E(_1lA);switch(_1lC._){case 0:var _1lD=_1lC.a,_1lE=_1lC.b,_1lF=_1lC.c,_1lG=_1lC.d,_1lH=E(_1lB);switch(_1lH._){case 0:var _1lI=_1lH.a,_1lJ=_1lH.b,_1lK=_1lH.c,_1lL=_1lH.d;if(_1lE>>>0<=_1lJ>>>0){if(_1lJ>>>0<=_1lE>>>0){if(_1lD!=_1lI){var _1lM=(_1lD>>>0^_1lI>>>0)>>>0,_1lN=(_1lM|_1lM>>>1)>>>0,_1lO=(_1lN|_1lN>>>2)>>>0,_1lP=(_1lO|_1lO>>>4)>>>0,_1lQ=(_1lP|_1lP>>>8)>>>0,_1lR=(_1lQ|_1lQ>>>16)>>>0,_1lS=(_1lR^_1lR>>>1)>>>0&4294967295,_1lT=_1lS>>>0;return ((_1lD>>>0&_1lT)>>>0==0)?new T4(0,(_1lD>>>0&((_1lT-1>>>0^4294967295)>>>0^_1lT)>>>0)>>>0&4294967295,_1lS,E(_1lC),E(_1lH)):new T4(0,(_1lD>>>0&((_1lT-1>>>0^4294967295)>>>0^_1lT)>>>0)>>>0&4294967295,_1lS,E(_1lH),E(_1lC));}else{return new T4(0,_1lD,_1lE,E(B(_1lz(_1lF,_1lK))),E(B(_1lz(_1lG,_1lL))));}}else{var _1lU=_1lJ>>>0;if(((_1lD>>>0&((_1lU-1>>>0^4294967295)>>>0^_1lU)>>>0)>>>0&4294967295)==_1lI){return ((_1lD>>>0&_1lU)>>>0==0)?new T4(0,_1lI,_1lJ,E(B(_1lV(_1lD,_1lE,_1lF,_1lG,_1lK))),E(_1lL)):new T4(0,_1lI,_1lJ,E(_1lK),E(B(_1lV(_1lD,_1lE,_1lF,_1lG,_1lL))));}else{var _1lW=(_1lD>>>0^_1lI>>>0)>>>0,_1lX=(_1lW|_1lW>>>1)>>>0,_1lY=(_1lX|_1lX>>>2)>>>0,_1lZ=(_1lY|_1lY>>>4)>>>0,_1m0=(_1lZ|_1lZ>>>8)>>>0,_1m1=(_1m0|_1m0>>>16)>>>0,_1m2=(_1m1^_1m1>>>1)>>>0&4294967295,_1m3=_1m2>>>0;return ((_1lD>>>0&_1m3)>>>0==0)?new T4(0,(_1lD>>>0&((_1m3-1>>>0^4294967295)>>>0^_1m3)>>>0)>>>0&4294967295,_1m2,E(_1lC),E(_1lH)):new T4(0,(_1lD>>>0&((_1m3-1>>>0^4294967295)>>>0^_1m3)>>>0)>>>0&4294967295,_1m2,E(_1lH),E(_1lC));}}}else{var _1m4=_1lE>>>0;if(((_1lI>>>0&((_1m4-1>>>0^4294967295)>>>0^_1m4)>>>0)>>>0&4294967295)==_1lD){return ((_1lI>>>0&_1m4)>>>0==0)?new T4(0,_1lD,_1lE,E(B(_1m5(_1lF,_1lI,_1lJ,_1lK,_1lL))),E(_1lG)):new T4(0,_1lD,_1lE,E(_1lF),E(B(_1m5(_1lG,_1lI,_1lJ,_1lK,_1lL))));}else{var _1m6=(_1lD>>>0^_1lI>>>0)>>>0,_1m7=(_1m6|_1m6>>>1)>>>0,_1m8=(_1m7|_1m7>>>2)>>>0,_1m9=(_1m8|_1m8>>>4)>>>0,_1ma=(_1m9|_1m9>>>8)>>>0,_1mb=(_1ma|_1ma>>>16)>>>0,_1mc=(_1mb^_1mb>>>1)>>>0&4294967295,_1md=_1mc>>>0;return ((_1lD>>>0&_1md)>>>0==0)?new T4(0,(_1lD>>>0&((_1md-1>>>0^4294967295)>>>0^_1md)>>>0)>>>0&4294967295,_1mc,E(_1lC),E(_1lH)):new T4(0,(_1lD>>>0&((_1md-1>>>0^4294967295)>>>0^_1md)>>>0)>>>0&4294967295,_1mc,E(_1lH),E(_1lC));}}break;case 1:var _1me=_1lH.a;return new F(function(){return _1li(_1me,_1lH.b,_1me,_1lD,_1lE,_1lF,_1lG);});break;default:return E(_1lC);}break;case 1:var _1mf=_1lC.a;return new F(function(){return _1ko(_1mf,_1lC.b,_1mf,_1lB);});break;default:return E(_1lB);}},_1lV=function(_1mg,_1mh,_1mi,_1mj,_1mk){var _1ml=E(_1mk);switch(_1ml._){case 0:var _1mm=_1ml.a,_1mn=_1ml.b,_1mo=_1ml.c,_1mp=_1ml.d;if(_1mh>>>0<=_1mn>>>0){if(_1mn>>>0<=_1mh>>>0){if(_1mg!=_1mm){var _1mq=(_1mg>>>0^_1mm>>>0)>>>0,_1mr=(_1mq|_1mq>>>1)>>>0,_1ms=(_1mr|_1mr>>>2)>>>0,_1mt=(_1ms|_1ms>>>4)>>>0,_1mu=(_1mt|_1mt>>>8)>>>0,_1mv=(_1mu|_1mu>>>16)>>>0,_1mw=(_1mv^_1mv>>>1)>>>0&4294967295,_1mx=_1mw>>>0;return ((_1mg>>>0&_1mx)>>>0==0)?new T4(0,(_1mg>>>0&((_1mx-1>>>0^4294967295)>>>0^_1mx)>>>0)>>>0&4294967295,_1mw,E(new T4(0,_1mg,_1mh,E(_1mi),E(_1mj))),E(_1ml)):new T4(0,(_1mg>>>0&((_1mx-1>>>0^4294967295)>>>0^_1mx)>>>0)>>>0&4294967295,_1mw,E(_1ml),E(new T4(0,_1mg,_1mh,E(_1mi),E(_1mj))));}else{return new T4(0,_1mg,_1mh,E(B(_1lz(_1mi,_1mo))),E(B(_1lz(_1mj,_1mp))));}}else{var _1my=_1mn>>>0;if(((_1mg>>>0&((_1my-1>>>0^4294967295)>>>0^_1my)>>>0)>>>0&4294967295)==_1mm){return ((_1mg>>>0&_1my)>>>0==0)?new T4(0,_1mm,_1mn,E(B(_1lV(_1mg,_1mh,_1mi,_1mj,_1mo))),E(_1mp)):new T4(0,_1mm,_1mn,E(_1mo),E(B(_1lV(_1mg,_1mh,_1mi,_1mj,_1mp))));}else{var _1mz=(_1mg>>>0^_1mm>>>0)>>>0,_1mA=(_1mz|_1mz>>>1)>>>0,_1mB=(_1mA|_1mA>>>2)>>>0,_1mC=(_1mB|_1mB>>>4)>>>0,_1mD=(_1mC|_1mC>>>8)>>>0,_1mE=(_1mD|_1mD>>>16)>>>0,_1mF=(_1mE^_1mE>>>1)>>>0&4294967295,_1mG=_1mF>>>0;return ((_1mg>>>0&_1mG)>>>0==0)?new T4(0,(_1mg>>>0&((_1mG-1>>>0^4294967295)>>>0^_1mG)>>>0)>>>0&4294967295,_1mF,E(new T4(0,_1mg,_1mh,E(_1mi),E(_1mj))),E(_1ml)):new T4(0,(_1mg>>>0&((_1mG-1>>>0^4294967295)>>>0^_1mG)>>>0)>>>0&4294967295,_1mF,E(_1ml),E(new T4(0,_1mg,_1mh,E(_1mi),E(_1mj))));}}}else{var _1mH=_1mh>>>0;if(((_1mm>>>0&((_1mH-1>>>0^4294967295)>>>0^_1mH)>>>0)>>>0&4294967295)==_1mg){return ((_1mm>>>0&_1mH)>>>0==0)?new T4(0,_1mg,_1mh,E(B(_1m5(_1mi,_1mm,_1mn,_1mo,_1mp))),E(_1mj)):new T4(0,_1mg,_1mh,E(_1mi),E(B(_1m5(_1mj,_1mm,_1mn,_1mo,_1mp))));}else{var _1mI=(_1mg>>>0^_1mm>>>0)>>>0,_1mJ=(_1mI|_1mI>>>1)>>>0,_1mK=(_1mJ|_1mJ>>>2)>>>0,_1mL=(_1mK|_1mK>>>4)>>>0,_1mM=(_1mL|_1mL>>>8)>>>0,_1mN=(_1mM|_1mM>>>16)>>>0,_1mO=(_1mN^_1mN>>>1)>>>0&4294967295,_1mP=_1mO>>>0;return ((_1mg>>>0&_1mP)>>>0==0)?new T4(0,(_1mg>>>0&((_1mP-1>>>0^4294967295)>>>0^_1mP)>>>0)>>>0&4294967295,_1mO,E(new T4(0,_1mg,_1mh,E(_1mi),E(_1mj))),E(_1ml)):new T4(0,(_1mg>>>0&((_1mP-1>>>0^4294967295)>>>0^_1mP)>>>0)>>>0&4294967295,_1mO,E(_1ml),E(new T4(0,_1mg,_1mh,E(_1mi),E(_1mj))));}}break;case 1:var _1mQ=_1ml.a;return new F(function(){return _1li(_1mQ,_1ml.b,_1mQ,_1mg,_1mh,_1mi,_1mj);});break;default:return new T4(0,_1mg,_1mh,E(_1mi),E(_1mj));}},_1m5=function(_1mR,_1mS,_1mT,_1mU,_1mV){var _1mW=E(_1mR);switch(_1mW._){case 0:var _1mX=_1mW.a,_1mY=_1mW.b,_1mZ=_1mW.c,_1n0=_1mW.d;if(_1mY>>>0<=_1mT>>>0){if(_1mT>>>0<=_1mY>>>0){if(_1mX!=_1mS){var _1n1=(_1mX>>>0^_1mS>>>0)>>>0,_1n2=(_1n1|_1n1>>>1)>>>0,_1n3=(_1n2|_1n2>>>2)>>>0,_1n4=(_1n3|_1n3>>>4)>>>0,_1n5=(_1n4|_1n4>>>8)>>>0,_1n6=(_1n5|_1n5>>>16)>>>0,_1n7=(_1n6^_1n6>>>1)>>>0&4294967295,_1n8=_1n7>>>0;return ((_1mX>>>0&_1n8)>>>0==0)?new T4(0,(_1mX>>>0&((_1n8-1>>>0^4294967295)>>>0^_1n8)>>>0)>>>0&4294967295,_1n7,E(_1mW),E(new T4(0,_1mS,_1mT,E(_1mU),E(_1mV)))):new T4(0,(_1mX>>>0&((_1n8-1>>>0^4294967295)>>>0^_1n8)>>>0)>>>0&4294967295,_1n7,E(new T4(0,_1mS,_1mT,E(_1mU),E(_1mV))),E(_1mW));}else{return new T4(0,_1mX,_1mY,E(B(_1lz(_1mZ,_1mU))),E(B(_1lz(_1n0,_1mV))));}}else{var _1n9=_1mT>>>0;if(((_1mX>>>0&((_1n9-1>>>0^4294967295)>>>0^_1n9)>>>0)>>>0&4294967295)==_1mS){return ((_1mX>>>0&_1n9)>>>0==0)?new T4(0,_1mS,_1mT,E(B(_1lV(_1mX,_1mY,_1mZ,_1n0,_1mU))),E(_1mV)):new T4(0,_1mS,_1mT,E(_1mU),E(B(_1lV(_1mX,_1mY,_1mZ,_1n0,_1mV))));}else{var _1na=(_1mX>>>0^_1mS>>>0)>>>0,_1nb=(_1na|_1na>>>1)>>>0,_1nc=(_1nb|_1nb>>>2)>>>0,_1nd=(_1nc|_1nc>>>4)>>>0,_1ne=(_1nd|_1nd>>>8)>>>0,_1nf=(_1ne|_1ne>>>16)>>>0,_1ng=(_1nf^_1nf>>>1)>>>0&4294967295,_1nh=_1ng>>>0;return ((_1mX>>>0&_1nh)>>>0==0)?new T4(0,(_1mX>>>0&((_1nh-1>>>0^4294967295)>>>0^_1nh)>>>0)>>>0&4294967295,_1ng,E(_1mW),E(new T4(0,_1mS,_1mT,E(_1mU),E(_1mV)))):new T4(0,(_1mX>>>0&((_1nh-1>>>0^4294967295)>>>0^_1nh)>>>0)>>>0&4294967295,_1ng,E(new T4(0,_1mS,_1mT,E(_1mU),E(_1mV))),E(_1mW));}}}else{var _1ni=_1mY>>>0;if(((_1mS>>>0&((_1ni-1>>>0^4294967295)>>>0^_1ni)>>>0)>>>0&4294967295)==_1mX){return ((_1mS>>>0&_1ni)>>>0==0)?new T4(0,_1mX,_1mY,E(B(_1m5(_1mZ,_1mS,_1mT,_1mU,_1mV))),E(_1n0)):new T4(0,_1mX,_1mY,E(_1mZ),E(B(_1m5(_1n0,_1mS,_1mT,_1mU,_1mV))));}else{var _1nj=(_1mX>>>0^_1mS>>>0)>>>0,_1nk=(_1nj|_1nj>>>1)>>>0,_1nl=(_1nk|_1nk>>>2)>>>0,_1nm=(_1nl|_1nl>>>4)>>>0,_1nn=(_1nm|_1nm>>>8)>>>0,_1no=(_1nn|_1nn>>>16)>>>0,_1np=(_1no^_1no>>>1)>>>0&4294967295,_1nq=_1np>>>0;return ((_1mX>>>0&_1nq)>>>0==0)?new T4(0,(_1mX>>>0&((_1nq-1>>>0^4294967295)>>>0^_1nq)>>>0)>>>0&4294967295,_1np,E(_1mW),E(new T4(0,_1mS,_1mT,E(_1mU),E(_1mV)))):new T4(0,(_1mX>>>0&((_1nq-1>>>0^4294967295)>>>0^_1nq)>>>0)>>>0&4294967295,_1np,E(new T4(0,_1mS,_1mT,E(_1mU),E(_1mV))),E(_1mW));}}break;case 1:var _1nr=_1mW.a,_1ns=_1mW.b,_1nt=_1mT>>>0;if(((_1nr>>>0&((_1nt-1>>>0^4294967295)>>>0^_1nt)>>>0)>>>0&4294967295)==_1mS){return ((_1nr>>>0&_1nt)>>>0==0)?new T4(0,_1mS,_1mT,E(B(_1ko(_1nr,_1ns,_1nr,_1mU))),E(_1mV)):new T4(0,_1mS,_1mT,E(_1mU),E(B(_1ko(_1nr,_1ns,_1nr,_1mV))));}else{var _1nu=(_1nr>>>0^_1mS>>>0)>>>0,_1nv=(_1nu|_1nu>>>1)>>>0,_1nw=(_1nv|_1nv>>>2)>>>0,_1nx=(_1nw|_1nw>>>4)>>>0,_1ny=(_1nx|_1nx>>>8)>>>0,_1nz=(_1ny|_1ny>>>16)>>>0,_1nA=(_1nz^_1nz>>>1)>>>0&4294967295,_1nB=_1nA>>>0;return ((_1nr>>>0&_1nB)>>>0==0)?new T4(0,(_1nr>>>0&((_1nB-1>>>0^4294967295)>>>0^_1nB)>>>0)>>>0&4294967295,_1nA,E(new T2(1,_1nr,_1ns)),E(new T4(0,_1mS,_1mT,E(_1mU),E(_1mV)))):new T4(0,(_1nr>>>0&((_1nB-1>>>0^4294967295)>>>0^_1nB)>>>0)>>>0&4294967295,_1nA,E(new T4(0,_1mS,_1mT,E(_1mU),E(_1mV))),E(new T2(1,_1nr,_1ns)));}break;default:return new T4(0,_1mS,_1mT,E(_1mU),E(_1mV));}};return new F(function(){return _1lz(_1km,_1kn);});},_1nC=function(_1nD,_1nE,_1nF){return new F(function(){return _1kk(_1ke,_1nE,_1nF);});},_1nG=function(_1nH,_1nI){return E(_1nH);},_1nJ=new T2(0,_4l,_RI),_1nK=function(_1nL,_1nM){while(1){var _1nN=B((function(_1nO,_1nP){var _1nQ=E(_1nP);if(!_1nQ._){_1nL=new T2(1,_1nQ.b,new T(function(){return B(_1nK(_1nO,_1nQ.d));}));_1nM=_1nQ.c;return __continue;}else{return E(_1nO);}})(_1nL,_1nM));if(_1nN!=__continue){return _1nN;}}},_1nR=function(_1nS,_1nT,_1nU){var _1nV=function(_1nW){var _1nX=function(_1nY){if(_1nW!=_1nY){return false;}else{return new F(function(){return _19g(_1nS,B(_1nK(_4,_1nT)),B(_1nK(_4,_1nU)));});}},_1nZ=E(_1nU);if(!_1nZ._){return new F(function(){return _1nX(_1nZ.a);});}else{return new F(function(){return _1nX(0);});}},_1o0=E(_1nT);if(!_1o0._){return new F(function(){return _1nV(_1o0.a);});}else{return new F(function(){return _1nV(0);});}},_1o1=function(_1o2,_1o3){return (!B(_1nR(_1bs,_1o2,_1o3)))?true:false;},_1o4=function(_1o5,_1o6){return new F(function(){return _1nR(_1bs,_1o5,_1o6);});},_1o7=new T2(0,_1o4,_1o1),_1o8=function(_1o9,_1oa){var _1ob=function(_1oc){while(1){var _1od=E(_1oc);switch(_1od._){case 0:var _1oe=_1od.b>>>0;if(((_1o9>>>0&((_1oe-1>>>0^4294967295)>>>0^_1oe)>>>0)>>>0&4294967295)==_1od.a){if(!((_1o9>>>0&_1oe)>>>0)){_1oc=_1od.c;continue;}else{_1oc=_1od.d;continue;}}else{return false;}break;case 1:return _1o9==_1od.a;default:return false;}}};return new F(function(){return _1ob(_1oa);});},_1of=function(_1og,_1oh){var _1oi=function(_1oj){while(1){var _1ok=E(_1oj);switch(_1ok._){case 0:var _1ol=_1ok.b>>>0;if(((_1og>>>0&((_1ol-1>>>0^4294967295)>>>0^_1ol)>>>0)>>>0&4294967295)==_1ok.a){if(!((_1og>>>0&_1ol)>>>0)){_1oj=_1ok.c;continue;}else{_1oj=_1ok.d;continue;}}else{return false;}break;case 1:return ((_1og&(-32))!=_1ok.a)?false:((1<<(_1og&31)>>>0&_1ok.b)>>>0==0)?false:true;default:return false;}}};return new F(function(){return _1oi(_1oh);});},_1om=function(_1on,_1oo,_1op){while(1){var _1oq=E(_1oo);switch(_1oq._){case 0:var _1or=E(_1op);if(!_1or._){if(_1oq.b!=_1or.b){return false;}else{if(_1oq.a!=_1or.a){return false;}else{if(!B(_1om(_1on,_1oq.c,_1or.c))){return false;}else{_1oo=_1oq.d;_1op=_1or.d;continue;}}}}else{return false;}break;case 1:var _1os=E(_1op);if(_1os._==1){if(_1oq.a!=_1os.a){return false;}else{return new F(function(){return A3(_qe,_1on,_1oq.b,_1os.b);});}}else{return false;}break;default:return (E(_1op)._==2)?true:false;}}},_1ot=function(_1ou,_1ov){var _1ow=E(_1ov);if(!_1ow._){var _1ox=_1ow.b,_1oy=_1ow.c,_1oz=_1ow.d;if(!B(A1(_1ou,_1ox))){return new F(function(){return _16f(B(_1ot(_1ou,_1oy)),B(_1ot(_1ou,_1oz)));});}else{return new F(function(){return _Pe(_1ox,B(_1ot(_1ou,_1oy)),B(_1ot(_1ou,_1oz)));});}}else{return new T0(1);}},_1oA=function(_1oB,_1oC,_1oD){var _1oE=E(_1oD);switch(_1oE._){case 0:var _1oF=_1oE.a,_1oG=_1oE.b,_1oH=_1oE.c,_1oI=_1oE.d,_1oJ=_1oG>>>0;if(((_1oB>>>0&((_1oJ-1>>>0^4294967295)>>>0^_1oJ)>>>0)>>>0&4294967295)==_1oF){return ((_1oB>>>0&_1oJ)>>>0==0)?new T4(0,_1oF,_1oG,E(B(_1oA(_1oB,_1oC,_1oH))),E(_1oI)):new T4(0,_1oF,_1oG,E(_1oH),E(B(_1oA(_1oB,_1oC,_1oI))));}else{var _1oK=(_1oB>>>0^_1oF>>>0)>>>0,_1oL=(_1oK|_1oK>>>1)>>>0,_1oM=(_1oL|_1oL>>>2)>>>0,_1oN=(_1oM|_1oM>>>4)>>>0,_1oO=(_1oN|_1oN>>>8)>>>0,_1oP=(_1oO|_1oO>>>16)>>>0,_1oQ=(_1oP^_1oP>>>1)>>>0&4294967295,_1oR=_1oQ>>>0;return ((_1oB>>>0&_1oR)>>>0==0)?new T4(0,(_1oB>>>0&((_1oR-1>>>0^4294967295)>>>0^_1oR)>>>0)>>>0&4294967295,_1oQ,E(new T2(1,_1oB,_1oC)),E(_1oE)):new T4(0,(_1oB>>>0&((_1oR-1>>>0^4294967295)>>>0^_1oR)>>>0)>>>0&4294967295,_1oQ,E(_1oE),E(new T2(1,_1oB,_1oC)));}break;case 1:var _1oS=_1oE.a;if(_1oS!=_1oB){var _1oT=(_1oB>>>0^_1oS>>>0)>>>0,_1oU=(_1oT|_1oT>>>1)>>>0,_1oV=(_1oU|_1oU>>>2)>>>0,_1oW=(_1oV|_1oV>>>4)>>>0,_1oX=(_1oW|_1oW>>>8)>>>0,_1oY=(_1oX|_1oX>>>16)>>>0,_1oZ=(_1oY^_1oY>>>1)>>>0&4294967295,_1p0=_1oZ>>>0;return ((_1oB>>>0&_1p0)>>>0==0)?new T4(0,(_1oB>>>0&((_1p0-1>>>0^4294967295)>>>0^_1p0)>>>0)>>>0&4294967295,_1oZ,E(new T2(1,_1oB,_1oC)),E(_1oE)):new T4(0,(_1oB>>>0&((_1p0-1>>>0^4294967295)>>>0^_1p0)>>>0)>>>0&4294967295,_1oZ,E(_1oE),E(new T2(1,_1oB,_1oC)));}else{return new T2(1,_1oS,(_1oC|_1oE.b)>>>0);}break;default:return new T2(1,_1oB,_1oC);}},_1p1=function(_1p2,_1p3){while(1){var _1p4=E(_1p2);if(!_1p4._){return E(_1p3);}else{var _1p5=E(E(_1p4.a).b),_1p6=B(_1oA(_1p5&(-32),1<<(_1p5&31)>>>0,_1p3));_1p2=_1p4.b;_1p3=_1p6;continue;}}},_1p7=function(_1p8,_1p9){while(1){var _1pa=E(_1p8);if(!_1pa._){return E(_1p9);}else{var _1pb=B(_1p1(E(_1pa.a).a,_1p9));_1p8=_1pa.b;_1p9=_1pb;continue;}}},_1pc=function(_1pd,_1pe){while(1){var _1pf=E(_1pe);if(!_1pf._){var _1pg=_1pf.c,_1ph=_1pf.d,_1pi=E(_1pf.b);if(!_1pi._){var _1pj=B(_1p7(_1pi.b,B(_1pc(_1pd,_1ph))));_1pd=_1pj;_1pe=_1pg;continue;}else{var _1pj=B(_1pc(_1pd,_1ph));_1pd=_1pj;_1pe=_1pg;continue;}}else{return E(_1pd);}}},_1pk=-1,_1pl=-2,_1pm=-3,_1pn=new T2(1,_MB,_4),_1po=new T2(1,_1pm,_1pn),_1pp=new T2(1,_1pl,_1po),_1pq=new T2(1,_1pk,_1pp),_1pr=function(_1ps,_1pt,_1pu){var _1pv=function(_1pw,_1px){if(!B(_1om(_1o7,_1ps,_1pw))){return new F(function(){return _1pr(_1pw,_1px,_1pu);});}else{return E(_1ps);}},_1py=function(_1pz){if(!B(_wr(_jt,_1pz,_1pq))){var _1pA=E(_1pz);if(!B(_1o8(_1pA,_1ps))){return new F(function(){return _1of(_1pA,_1pt);});}else{return true;}}else{return true;}},_1pB=function(_1pC){while(1){var _1pD=E(_1pC);if(!_1pD._){return true;}else{if(!B(_1py(E(_1pD.a).b))){return false;}else{_1pC=_1pD.b;continue;}}}},_1pE=function(_1pF){var _1pG=E(_1pF);switch(_1pG._){case 0:return new F(function(){return _1pB(_1pG.b);});break;case 1:return new F(function(){return _1py(_1pG.a);});break;default:return true;}},_1pH=function(_1pI,_1pJ,_1pK){while(1){var _1pL=B((function(_1pM,_1pN,_1pO){var _1pP=E(_1pO);switch(_1pP._){case 0:var _1pQ=B(_1pH(_1pM,_1pN,_1pP.d));_1pI=_1pQ.a;_1pJ=_1pQ.b;_1pK=_1pP.c;return __continue;case 1:var _1pR=E(_1pM),_1pS=E(_1pN),_1pT=B(_1ot(_1pE,_1pP.b));return (_1pT._==0)?new T2(0,new T(function(){return B(_14W(_1pP.a,_1pT,_1pR));}),new T(function(){return B(_1pc(_1pS,_1pT));})):new T2(0,_1pR,_1pS);default:return new T2(0,_1pM,_1pN);}})(_1pI,_1pJ,_1pK));if(_1pL!=__continue){return _1pL;}}},_1pU=E(_1pu);if(!_1pU._){var _1pV=_1pU.c,_1pW=_1pU.d;if(_1pU.b>=0){var _1pX=B(_1pH(_UZ,_190,_1pW)),_1pY=B(_1pH(_1pX.a,_1pX.b,_1pV));return new F(function(){return _1pv(_1pY.a,_1pY.b);});}else{var _1pZ=B(_1pH(_UZ,_190,_1pV)),_1q0=B(_1pH(_1pZ.a,_1pZ.b,_1pW));return new F(function(){return _1pv(_1q0.a,_1q0.b);});}}else{var _1q1=B(_1pH(_UZ,_190,_1pU));return new F(function(){return _1pv(_1q1.a,_1q1.b);});}},_1q2=function(_1q3,_1q4){while(1){var _1q5=E(_1q4);if(!_1q5._){return E(_1q3);}else{var _1q6=E(_1q5.a),_1q7=B(_14W(E(_1q6.a),_1q6.b,_1q3));_1q3=_1q7;_1q4=_1q5.b;continue;}}},_1q8=function(_1q9){var _1qa=E(_1q9);return (_1qa._==0)?(E(_1qa.b)._==0)?true:false:false;},_1qb=new T(function(){return B(unCStr(")"));}),_1qc=function(_1qd,_1qe){var _1qf=new T(function(){var _1qg=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_co(0,_1qe,_4)),_1qb));})));},1);return B(_0(B(_co(0,_1qd,_4)),_1qg));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1qf)));});},_1qh=new T(function(){return B(_7f("pgf/PGF/Optimize.hs:(259,9)-(262,117)|function getFunctions"));}),_1qi=new T(function(){return B(unCStr("&|"));}),_1qj=new T2(1,_1qi,_4),_1qk=new T(function(){return B(unCStr("&+"));}),_1ql=new T2(1,_1qk,_4),_1qm=new T(function(){return B(_7f("pgf/PGF/Optimize.hs:(235,9)-(245,73)|function seq2prefix"));}),_1qn=function(_1qo,_1qp,_1qq,_1qr,_1qs,_1qt){var _1qu=_1qr>>>0;if(((_1qo>>>0&((_1qu-1>>>0^4294967295)>>>0^_1qu)>>>0)>>>0&4294967295)==_1qq){return ((_1qo>>>0&_1qu)>>>0==0)?new T4(0,_1qq,_1qr,E(B(_1oA(_1qo,_1qp,_1qs))),E(_1qt)):new T4(0,_1qq,_1qr,E(_1qs),E(B(_1oA(_1qo,_1qp,_1qt))));}else{var _1qv=(_1qo>>>0^_1qq>>>0)>>>0,_1qw=(_1qv|_1qv>>>1)>>>0,_1qx=(_1qw|_1qw>>>2)>>>0,_1qy=(_1qx|_1qx>>>4)>>>0,_1qz=(_1qy|_1qy>>>8)>>>0,_1qA=(_1qz|_1qz>>>16)>>>0,_1qB=(_1qA^_1qA>>>1)>>>0&4294967295,_1qC=_1qB>>>0;return ((_1qo>>>0&_1qC)>>>0==0)?new T4(0,(_1qo>>>0&((_1qC-1>>>0^4294967295)>>>0^_1qC)>>>0)>>>0&4294967295,_1qB,E(new T2(1,_1qo,_1qp)),E(new T4(0,_1qq,_1qr,E(_1qs),E(_1qt)))):new T4(0,(_1qo>>>0&((_1qC-1>>>0^4294967295)>>>0^_1qC)>>>0)>>>0&4294967295,_1qB,E(new T4(0,_1qq,_1qr,E(_1qs),E(_1qt))),E(new T2(1,_1qo,_1qp)));}},_1qD=function(_1qE,_1qF,_1qG,_1qH,_1qI){var _1qJ=E(_1qI);switch(_1qJ._){case 0:var _1qK=_1qJ.a,_1qL=_1qJ.b,_1qM=_1qJ.c,_1qN=_1qJ.d;if(_1qF>>>0<=_1qL>>>0){if(_1qL>>>0<=_1qF>>>0){if(_1qE!=_1qK){var _1qO=(_1qE>>>0^_1qK>>>0)>>>0,_1qP=(_1qO|_1qO>>>1)>>>0,_1qQ=(_1qP|_1qP>>>2)>>>0,_1qR=(_1qQ|_1qQ>>>4)>>>0,_1qS=(_1qR|_1qR>>>8)>>>0,_1qT=(_1qS|_1qS>>>16)>>>0,_1qU=(_1qT^_1qT>>>1)>>>0&4294967295,_1qV=_1qU>>>0;return ((_1qE>>>0&_1qV)>>>0==0)?new T4(0,(_1qE>>>0&((_1qV-1>>>0^4294967295)>>>0^_1qV)>>>0)>>>0&4294967295,_1qU,E(new T4(0,_1qE,_1qF,E(_1qG),E(_1qH))),E(_1qJ)):new T4(0,(_1qE>>>0&((_1qV-1>>>0^4294967295)>>>0^_1qV)>>>0)>>>0&4294967295,_1qU,E(_1qJ),E(new T4(0,_1qE,_1qF,E(_1qG),E(_1qH))));}else{return new T4(0,_1qE,_1qF,E(B(_1qW(_1qG,_1qM))),E(B(_1qW(_1qH,_1qN))));}}else{var _1qX=_1qL>>>0;if(((_1qE>>>0&((_1qX-1>>>0^4294967295)>>>0^_1qX)>>>0)>>>0&4294967295)==_1qK){return ((_1qE>>>0&_1qX)>>>0==0)?new T4(0,_1qK,_1qL,E(B(_1qD(_1qE,_1qF,_1qG,_1qH,_1qM))),E(_1qN)):new T4(0,_1qK,_1qL,E(_1qM),E(B(_1qD(_1qE,_1qF,_1qG,_1qH,_1qN))));}else{var _1qY=(_1qE>>>0^_1qK>>>0)>>>0,_1qZ=(_1qY|_1qY>>>1)>>>0,_1r0=(_1qZ|_1qZ>>>2)>>>0,_1r1=(_1r0|_1r0>>>4)>>>0,_1r2=(_1r1|_1r1>>>8)>>>0,_1r3=(_1r2|_1r2>>>16)>>>0,_1r4=(_1r3^_1r3>>>1)>>>0&4294967295,_1r5=_1r4>>>0;return ((_1qE>>>0&_1r5)>>>0==0)?new T4(0,(_1qE>>>0&((_1r5-1>>>0^4294967295)>>>0^_1r5)>>>0)>>>0&4294967295,_1r4,E(new T4(0,_1qE,_1qF,E(_1qG),E(_1qH))),E(_1qJ)):new T4(0,(_1qE>>>0&((_1r5-1>>>0^4294967295)>>>0^_1r5)>>>0)>>>0&4294967295,_1r4,E(_1qJ),E(new T4(0,_1qE,_1qF,E(_1qG),E(_1qH))));}}}else{var _1r6=_1qF>>>0;if(((_1qK>>>0&((_1r6-1>>>0^4294967295)>>>0^_1r6)>>>0)>>>0&4294967295)==_1qE){return ((_1qK>>>0&_1r6)>>>0==0)?new T4(0,_1qE,_1qF,E(B(_1r7(_1qG,_1qK,_1qL,_1qM,_1qN))),E(_1qH)):new T4(0,_1qE,_1qF,E(_1qG),E(B(_1r7(_1qH,_1qK,_1qL,_1qM,_1qN))));}else{var _1r8=(_1qE>>>0^_1qK>>>0)>>>0,_1r9=(_1r8|_1r8>>>1)>>>0,_1ra=(_1r9|_1r9>>>2)>>>0,_1rb=(_1ra|_1ra>>>4)>>>0,_1rc=(_1rb|_1rb>>>8)>>>0,_1rd=(_1rc|_1rc>>>16)>>>0,_1re=(_1rd^_1rd>>>1)>>>0&4294967295,_1rf=_1re>>>0;return ((_1qE>>>0&_1rf)>>>0==0)?new T4(0,(_1qE>>>0&((_1rf-1>>>0^4294967295)>>>0^_1rf)>>>0)>>>0&4294967295,_1re,E(new T4(0,_1qE,_1qF,E(_1qG),E(_1qH))),E(_1qJ)):new T4(0,(_1qE>>>0&((_1rf-1>>>0^4294967295)>>>0^_1rf)>>>0)>>>0&4294967295,_1re,E(_1qJ),E(new T4(0,_1qE,_1qF,E(_1qG),E(_1qH))));}}break;case 1:return new F(function(){return _1qn(_1qJ.a,_1qJ.b,_1qE,_1qF,_1qG,_1qH);});break;default:return new T4(0,_1qE,_1qF,E(_1qG),E(_1qH));}},_1r7=function(_1rg,_1rh,_1ri,_1rj,_1rk){var _1rl=E(_1rg);switch(_1rl._){case 0:var _1rm=_1rl.a,_1rn=_1rl.b,_1ro=_1rl.c,_1rp=_1rl.d;if(_1rn>>>0<=_1ri>>>0){if(_1ri>>>0<=_1rn>>>0){if(_1rm!=_1rh){var _1rq=(_1rm>>>0^_1rh>>>0)>>>0,_1rr=(_1rq|_1rq>>>1)>>>0,_1rs=(_1rr|_1rr>>>2)>>>0,_1rt=(_1rs|_1rs>>>4)>>>0,_1ru=(_1rt|_1rt>>>8)>>>0,_1rv=(_1ru|_1ru>>>16)>>>0,_1rw=(_1rv^_1rv>>>1)>>>0&4294967295,_1rx=_1rw>>>0;return ((_1rm>>>0&_1rx)>>>0==0)?new T4(0,(_1rm>>>0&((_1rx-1>>>0^4294967295)>>>0^_1rx)>>>0)>>>0&4294967295,_1rw,E(_1rl),E(new T4(0,_1rh,_1ri,E(_1rj),E(_1rk)))):new T4(0,(_1rm>>>0&((_1rx-1>>>0^4294967295)>>>0^_1rx)>>>0)>>>0&4294967295,_1rw,E(new T4(0,_1rh,_1ri,E(_1rj),E(_1rk))),E(_1rl));}else{return new T4(0,_1rm,_1rn,E(B(_1qW(_1ro,_1rj))),E(B(_1qW(_1rp,_1rk))));}}else{var _1ry=_1ri>>>0;if(((_1rm>>>0&((_1ry-1>>>0^4294967295)>>>0^_1ry)>>>0)>>>0&4294967295)==_1rh){return ((_1rm>>>0&_1ry)>>>0==0)?new T4(0,_1rh,_1ri,E(B(_1qD(_1rm,_1rn,_1ro,_1rp,_1rj))),E(_1rk)):new T4(0,_1rh,_1ri,E(_1rj),E(B(_1qD(_1rm,_1rn,_1ro,_1rp,_1rk))));}else{var _1rz=(_1rm>>>0^_1rh>>>0)>>>0,_1rA=(_1rz|_1rz>>>1)>>>0,_1rB=(_1rA|_1rA>>>2)>>>0,_1rC=(_1rB|_1rB>>>4)>>>0,_1rD=(_1rC|_1rC>>>8)>>>0,_1rE=(_1rD|_1rD>>>16)>>>0,_1rF=(_1rE^_1rE>>>1)>>>0&4294967295,_1rG=_1rF>>>0;return ((_1rm>>>0&_1rG)>>>0==0)?new T4(0,(_1rm>>>0&((_1rG-1>>>0^4294967295)>>>0^_1rG)>>>0)>>>0&4294967295,_1rF,E(_1rl),E(new T4(0,_1rh,_1ri,E(_1rj),E(_1rk)))):new T4(0,(_1rm>>>0&((_1rG-1>>>0^4294967295)>>>0^_1rG)>>>0)>>>0&4294967295,_1rF,E(new T4(0,_1rh,_1ri,E(_1rj),E(_1rk))),E(_1rl));}}}else{var _1rH=_1rn>>>0;if(((_1rh>>>0&((_1rH-1>>>0^4294967295)>>>0^_1rH)>>>0)>>>0&4294967295)==_1rm){return ((_1rh>>>0&_1rH)>>>0==0)?new T4(0,_1rm,_1rn,E(B(_1r7(_1ro,_1rh,_1ri,_1rj,_1rk))),E(_1rp)):new T4(0,_1rm,_1rn,E(_1ro),E(B(_1r7(_1rp,_1rh,_1ri,_1rj,_1rk))));}else{var _1rI=(_1rm>>>0^_1rh>>>0)>>>0,_1rJ=(_1rI|_1rI>>>1)>>>0,_1rK=(_1rJ|_1rJ>>>2)>>>0,_1rL=(_1rK|_1rK>>>4)>>>0,_1rM=(_1rL|_1rL>>>8)>>>0,_1rN=(_1rM|_1rM>>>16)>>>0,_1rO=(_1rN^_1rN>>>1)>>>0&4294967295,_1rP=_1rO>>>0;return ((_1rm>>>0&_1rP)>>>0==0)?new T4(0,(_1rm>>>0&((_1rP-1>>>0^4294967295)>>>0^_1rP)>>>0)>>>0&4294967295,_1rO,E(_1rl),E(new T4(0,_1rh,_1ri,E(_1rj),E(_1rk)))):new T4(0,(_1rm>>>0&((_1rP-1>>>0^4294967295)>>>0^_1rP)>>>0)>>>0&4294967295,_1rO,E(new T4(0,_1rh,_1ri,E(_1rj),E(_1rk))),E(_1rl));}}break;case 1:return new F(function(){return _1qn(_1rl.a,_1rl.b,_1rh,_1ri,_1rj,_1rk);});break;default:return new T4(0,_1rh,_1ri,E(_1rj),E(_1rk));}},_1qW=function(_1rQ,_1rR){var _1rS=E(_1rQ);switch(_1rS._){case 0:var _1rT=_1rS.a,_1rU=_1rS.b,_1rV=_1rS.c,_1rW=_1rS.d,_1rX=E(_1rR);switch(_1rX._){case 0:var _1rY=_1rX.a,_1rZ=_1rX.b,_1s0=_1rX.c,_1s1=_1rX.d;if(_1rU>>>0<=_1rZ>>>0){if(_1rZ>>>0<=_1rU>>>0){if(_1rT!=_1rY){var _1s2=(_1rT>>>0^_1rY>>>0)>>>0,_1s3=(_1s2|_1s2>>>1)>>>0,_1s4=(_1s3|_1s3>>>2)>>>0,_1s5=(_1s4|_1s4>>>4)>>>0,_1s6=(_1s5|_1s5>>>8)>>>0,_1s7=(_1s6|_1s6>>>16)>>>0,_1s8=(_1s7^_1s7>>>1)>>>0&4294967295,_1s9=_1s8>>>0;return ((_1rT>>>0&_1s9)>>>0==0)?new T4(0,(_1rT>>>0&((_1s9-1>>>0^4294967295)>>>0^_1s9)>>>0)>>>0&4294967295,_1s8,E(_1rS),E(_1rX)):new T4(0,(_1rT>>>0&((_1s9-1>>>0^4294967295)>>>0^_1s9)>>>0)>>>0&4294967295,_1s8,E(_1rX),E(_1rS));}else{return new T4(0,_1rT,_1rU,E(B(_1qW(_1rV,_1s0))),E(B(_1qW(_1rW,_1s1))));}}else{var _1sa=_1rZ>>>0;if(((_1rT>>>0&((_1sa-1>>>0^4294967295)>>>0^_1sa)>>>0)>>>0&4294967295)==_1rY){return ((_1rT>>>0&_1sa)>>>0==0)?new T4(0,_1rY,_1rZ,E(B(_1qD(_1rT,_1rU,_1rV,_1rW,_1s0))),E(_1s1)):new T4(0,_1rY,_1rZ,E(_1s0),E(B(_1qD(_1rT,_1rU,_1rV,_1rW,_1s1))));}else{var _1sb=(_1rT>>>0^_1rY>>>0)>>>0,_1sc=(_1sb|_1sb>>>1)>>>0,_1sd=(_1sc|_1sc>>>2)>>>0,_1se=(_1sd|_1sd>>>4)>>>0,_1sf=(_1se|_1se>>>8)>>>0,_1sg=(_1sf|_1sf>>>16)>>>0,_1sh=(_1sg^_1sg>>>1)>>>0&4294967295,_1si=_1sh>>>0;return ((_1rT>>>0&_1si)>>>0==0)?new T4(0,(_1rT>>>0&((_1si-1>>>0^4294967295)>>>0^_1si)>>>0)>>>0&4294967295,_1sh,E(_1rS),E(_1rX)):new T4(0,(_1rT>>>0&((_1si-1>>>0^4294967295)>>>0^_1si)>>>0)>>>0&4294967295,_1sh,E(_1rX),E(_1rS));}}}else{var _1sj=_1rU>>>0;if(((_1rY>>>0&((_1sj-1>>>0^4294967295)>>>0^_1sj)>>>0)>>>0&4294967295)==_1rT){return ((_1rY>>>0&_1sj)>>>0==0)?new T4(0,_1rT,_1rU,E(B(_1r7(_1rV,_1rY,_1rZ,_1s0,_1s1))),E(_1rW)):new T4(0,_1rT,_1rU,E(_1rV),E(B(_1r7(_1rW,_1rY,_1rZ,_1s0,_1s1))));}else{var _1sk=(_1rT>>>0^_1rY>>>0)>>>0,_1sl=(_1sk|_1sk>>>1)>>>0,_1sm=(_1sl|_1sl>>>2)>>>0,_1sn=(_1sm|_1sm>>>4)>>>0,_1so=(_1sn|_1sn>>>8)>>>0,_1sp=(_1so|_1so>>>16)>>>0,_1sq=(_1sp^_1sp>>>1)>>>0&4294967295,_1sr=_1sq>>>0;return ((_1rT>>>0&_1sr)>>>0==0)?new T4(0,(_1rT>>>0&((_1sr-1>>>0^4294967295)>>>0^_1sr)>>>0)>>>0&4294967295,_1sq,E(_1rS),E(_1rX)):new T4(0,(_1rT>>>0&((_1sr-1>>>0^4294967295)>>>0^_1sr)>>>0)>>>0&4294967295,_1sq,E(_1rX),E(_1rS));}}break;case 1:return new F(function(){return _1qn(_1rX.a,_1rX.b,_1rT,_1rU,_1rV,_1rW);});break;default:return E(_1rS);}break;case 1:return new F(function(){return _1oA(_1rS.a,_1rS.b,_1rR);});break;default:return E(_1rR);}},_1ss=function(_1st,_1su){var _1sv=E(_1st),_1sw=B(_16K(_134,_1qW,_1sv.a,_1sv.b,_1su));return new T2(0,_1sw.a,_1sw.b);},_1sx=new T(function(){return B(unCStr("Int"));}),_1sy=function(_1sz,_1sA,_1sB){return new F(function(){return _fj(_ew,new T2(0,_1sA,_1sB),_1sz,_1sx);});},_1sC=function(_1sD,_1sE,_1sF){return new F(function(){return _fj(_ew,new T2(0,_1sD,_1sE),_1sF,_1sx);});},_1sG=new T(function(){return B(_1q2(_UZ,_4));}),_1sH=function(_1sI,_1sJ){var _1sK=function(_1sL,_1sM,_1sN){return new F(function(){return A2(_1sI,_1sM,_1sN);});},_1sO=function(_1sP,_1sQ){while(1){var _1sR=E(_1sQ);if(!_1sR._){return E(_1sP);}else{var _1sS=B(_1kk(_1sK,_1sP,_1sR.a));_1sP=_1sS;_1sQ=_1sR.b;continue;}}};return new F(function(){return _1sO(_UZ,_1sJ);});},_1sT=function(_1sU,_1sV,_1sW,_1sX,_1sY,_1sZ,_1t0,_1t1,_1t2){var _1t3=new T(function(){return B(_1pr(_UZ,_190,_1t0));}),_1t4=new T(function(){var _1t5=function(_1t6,_1t7){while(1){var _1t8=B((function(_1t9,_1ta){var _1tb=E(_1ta);if(!_1tb._){var _1tc=_1tb.d,_1td=new T(function(){var _1te=E(_1tb.b);if(!_1te._){var _1tf=_1te.a;if(!E(_1te.b)._){var _1tg=new T(function(){var _1th=E(_1sW),_1ti=_1th.c,_1tj=E(_1th.a),_1tk=E(_1th.b);if(_1tj>_1tf){return B(_1sy(_1tf,_1tj,_1tk));}else{if(_1tf>_1tk){return B(_1sy(_1tf,_1tj,_1tk));}else{var _1tl=_1tf-_1tj|0;if(0>_1tl){return B(_1qc(_1tl,_1ti));}else{if(_1tl>=_1ti){return B(_1qc(_1tl,_1ti));}else{var _1tm=E(_1th.d[_1tl]),_1tn=_1tm.d,_1to=E(_1tm.b),_1tp=E(_1tm.c);if(_1to<=_1tp){var _1tq=new T(function(){var _1tr=B(_14L(_134,_1nG,new T2(1,new T2(0,_1qj,new T2(1,_1tf&(-32),1<<(_1tf&31)>>>0)),_4)));return new T2(0,_1tr.a,_1tr.b);}),_1ts=new T(function(){var _1tt=B(_14L(_134,_1nG,new T2(1,new T2(0,_4,new T2(1,_1tf&(-32),1<<(_1tf&31)>>>0)),_4)));return new T2(0,_1tt.a,_1tt.b);}),_1tu=new T2(1,_1tf&(-32),1<<(_1tf&31)>>>0),_1tv=new T(function(){var _1tw=B(_14L(_134,_1nG,new T2(1,new T2(0,_4,_1tu),_4)));return new T2(0,_1tw.a,_1tw.b);}),_1tx=new T(function(){var _1ty=B(_14L(_134,_1nG,new T2(1,new T2(0,_1ql,new T2(1,_1tf&(-32),1<<(_1tf&31)>>>0)),_4)));return new T2(0,_1ty.a,_1ty.b);}),_1tz=function(_1tA){var _1tB=E(_1tA);if(!_1tB._){return E(_1tv);}else{var _1tC=_1tB.b,_1tD=E(_1tB.a);switch(_1tD._){case 3:var _1tE=B(_14L(_134,_1nG,new T2(1,new T2(0,new T2(1,_1tD.a,_4),_1tu),_4)));return new T2(0,_1tE.a,_1tE.b);case 4:var _1tF=new T(function(){var _1tG=function(_1tH){var _1tI=E(_1tH);return (_1tI._==0)?__Z:new T2(1,new T(function(){return B(_1tz(B(_0(E(_1tI.a).a,_1tC))));}),new T(function(){return B(_1tG(_1tI.b));}));};return B(_1tG(_1tD.b));}),_1tJ=B(_18Q(_134,_1qW,new T2(1,new T(function(){return B(_1tz(B(_0(_1tD.a,_1tC))));}),_1tF)));return new T2(0,_1tJ.a,_1tJ.b);case 5:return E(_1tx);case 6:return E(_1nJ);case 7:return E(_1ts);case 8:return E(_1ts);case 9:return E(_1tq);case 10:return E(_1tq);default:return E(_1qm);}}},_1tK=new T(function(){return B(_1tz(_4));}),_1tL=function(_1tM){var _1tN=new T(function(){var _1tO=E(_1sZ),_1tP=_1tO.c,_1tQ=E(_1tO.a),_1tR=E(_1tO.b);if(_1to>_1tM){return B(_1sC(_1to,_1tp,_1tM));}else{if(_1tM>_1tp){return B(_1sC(_1to,_1tp,_1tM));}else{var _1tS=_1tM-_1to|0;if(0>_1tS){return B(_1qc(_1tS,_1tn));}else{if(_1tS>=_1tn){return B(_1qc(_1tS,_1tn));}else{var _1tT=_1tm.e["v"]["i32"][_1tS];if(_1tQ>_1tT){return B(_1sy(_1tT,_1tQ,_1tR));}else{if(_1tT>_1tR){return B(_1sy(_1tT,_1tQ,_1tR));}else{var _1tU=_1tT-_1tQ|0;if(0>_1tU){return B(_1qc(_1tU,_1tP));}else{if(_1tU>=_1tP){return B(_1qc(_1tU,_1tP));}else{var _1tV=E(_1tO.d[_1tU]),_1tW=_1tV.c-1|0;if(0<=_1tW){var _1tX=function(_1tY){return new T2(1,new T(function(){return E(_1tV.d[_1tY]);}),new T(function(){if(_1tY!=_1tW){return B(_1tX(_1tY+1|0));}else{return __Z;}}));};return B(_1tz(B(_1tX(0))));}else{return E(_1tK);}}}}}}}}}});return new T2(1,new T2(0,_1tM,_1tN),new T(function(){if(_1tM!=_1tp){return B(_1tL(_1tM+1|0));}else{return __Z;}}));};return B(_1q2(_UZ,B(_1tL(_1to))));}else{return E(_1sG);}}}}}});return new T2(1,_1tg,new T(function(){return B(_1t5(_1t9,_1tc));}));}else{return B(_1t5(_1t9,_1tc));}}else{return B(_1t5(_1t9,_1tc));}},1);_1t6=_1td;_1t7=_1tb.c;return __continue;}else{return E(_1t9);}})(_1t6,_1t7));if(_1t8!=__continue){return _1t8;}}},_1tZ=function(_1u0,_1u1,_1u2){while(1){var _1u3=E(_1u2);switch(_1u3._){case 0:var _1u4=B(_1tZ(_1u0,_1u1,_1u3.d));_1u0=_1u4.a;_1u1=_1u4.b;_1u2=_1u3.c;continue;case 1:var _1u5=_1u3.a,_1u6=B(_16s(_1q8,_1u3.b)),_1u7=E(_1u6.a);if(!_1u7._){var _1u8=B(_14W(_1u5,B(_1sH(_1ss,B(_1t5(_4,_1u7)))),_1u0));}else{var _1u8=E(_1u0);}var _1u9=E(_1u6.b);if(!_1u9._){var _1ua=B(_14W(_1u5,_1u9,_1u1));}else{var _1ua=E(_1u1);}return new T2(0,_1u8,_1ua);default:return new T2(0,_1u0,_1u1);}}},_1ub=E(_1t3);if(!_1ub._){var _1uc=_1ub.c,_1ud=_1ub.d;if(_1ub.b>=0){var _1ue=B(_1tZ(_UZ,_UZ,_1ud)),_1uf=B(_1tZ(_1ue.a,_1ue.b,_1uc));return new T2(0,_1uf.a,_1uf.b);}else{var _1ug=B(_1tZ(_UZ,_UZ,_1uc)),_1uh=B(_1tZ(_1ug.a,_1ug.b,_1ud));return new T2(0,_1uh.a,_1uh.b);}}else{var _1ui=B(_1tZ(_UZ,_UZ,_1ub));return new T2(0,_1ui.a,_1ui.b);}}),_1uj=new T(function(){var _1uk=function(_1ul){var _1um=E(_1ul);switch(_1um._){case 0:var _1un=_1um.a;return new T2(1,new T(function(){var _1uo=E(_1sW),_1up=_1uo.c,_1uq=E(_1uo.a),_1ur=E(_1uo.b);if(_1uq>_1un){return B(_1sy(_1un,_1uq,_1ur));}else{if(_1un>_1ur){return B(_1sy(_1un,_1uq,_1ur));}else{var _1us=_1un-_1uq|0;if(0>_1us){return B(_1qc(_1us,_1up));}else{if(_1us>=_1up){return B(_1qc(_1us,_1up));}else{return E(E(_1uo.d[_1us]).a);}}}}}),_4);case 1:var _1ut=B(_15n(_1um.a,_1t3));if(!_1ut._){return __Z;}else{return new F(function(){return _1uu(_4,_1ut.a);});}break;default:return E(_1qh);}},_1uu=function(_1uv,_1uw){while(1){var _1ux=B((function(_1uy,_1uz){var _1uA=E(_1uz);if(!_1uA._){var _1uB=new T(function(){return B(_0(B(_1uk(_1uA.b)),new T(function(){return B(_1uu(_1uy,_1uA.d));},1)));},1);_1uv=_1uB;_1uw=_1uA.c;return __continue;}else{return E(_1uy);}})(_1uv,_1uw));if(_1ux!=__continue){return _1ux;}}},_1uC=function(_1uD,_1uE){while(1){var _1uF=B((function(_1uG,_1uH){var _1uI=E(_1uH);switch(_1uI._){case 0:_1uD=new T(function(){return B(_1uC(_1uG,_1uI.d));},1);_1uE=_1uI.c;return __continue;case 1:var _1uJ=function(_1uK,_1uL){while(1){var _1uM=B((function(_1uN,_1uO){var _1uP=E(_1uO);if(!_1uP._){var _1uQ=_1uP.b,_1uR=new T(function(){var _1uS=new T(function(){return B(_1uJ(_1uN,_1uP.d));}),_1uT=function(_1uU){var _1uV=E(_1uU);return (_1uV._==0)?E(_1uS):new T2(1,new T2(0,_1uV.a,new T2(1,_1uI.a,new T4(0,1,E(_1uQ),E(_Nd),E(_Nd)))),new T(function(){return B(_1uT(_1uV.b));}));};return B(_1uT(B(_1uk(_1uQ))));},1);_1uK=_1uR;_1uL=_1uP.c;return __continue;}else{return E(_1uN);}})(_1uK,_1uL));if(_1uM!=__continue){return _1uM;}}};return new F(function(){return _1uJ(_1uG,_1uI.b);});break;default:return E(_1uG);}})(_1uD,_1uE));if(_1uF!=__continue){return _1uF;}}},_1uW=E(_1t3);if(!_1uW._){var _1uX=_1uW.c,_1uY=_1uW.d;if(_1uW.b>=0){return B(_13F(_1nC,B(_1uC(new T(function(){return B(_1uC(_4,_1uY));},1),_1uX))));}else{return B(_13F(_1nC,B(_1uC(new T(function(){return B(_1uC(_4,_1uX));},1),_1uY))));}}else{return B(_13F(_1nC,B(_1uC(_4,_1uW))));}});return {_:0,a:_1sU,b:_1sV,c:_1sW,d:_1sX,e:_1sY,f:_1sZ,g:_1t0,h:new T(function(){return E(E(_1t4).b);}),i:_1uj,j:_1t1,k:new T(function(){return E(E(_1t4).a);}),l:_1t2};},_1uZ=function(_1v0){var _1v1=E(_1v0);return new F(function(){return _1sT(_1v1.a,_1v1.b,_1v1.c,_1v1.d,_1v1.e,_1v1.f,_1v1.g,_1v1.j,_1v1.l);});},_1v2=0,_1v3=function(_1v4){var _1v5=E(_1v4);return new T3(0,_1v5.a,_1v5.b,_1v2);},_1v6=function(_1v7){var _1v8=E(_1v7);return new T4(0,_1v8.a,_1v8.b,new T(function(){var _1v9=E(_1v8.c);if(!_1v9._){return __Z;}else{return new T1(1,new T2(0,_1v9.a,_4));}}),_1v8.d);},_1va=0,_1vb=new T(function(){return B(unCStr("Negative range size"));}),_1vc=function(_1vd){var _1ve=function(_){var _1vf=B(_vm(_1vd,0))-1|0,_1vg=function(_1vh){if(_1vh>=0){var _1vi=newArr(_1vh,_VW),_1vj=_1vi,_1vk=function(_1vl){var _1vm=function(_1vn,_1vo,_){while(1){if(_1vn!=_1vl){var _1vp=E(_1vo);if(!_1vp._){return _5;}else{var _=_1vj[_1vn]=_1vp.a,_1vq=_1vn+1|0;_1vn=_1vq;_1vo=_1vp.b;continue;}}else{return _5;}}},_1vr=B(_1vm(0,_1vd,_));return new T4(0,E(_1va),E(_1vf),_1vh,_1vj);};if(0>_1vf){return new F(function(){return _1vk(0);});}else{var _1vs=_1vf+1|0;if(_1vs>=0){return new F(function(){return _1vk(_1vs);});}else{return new F(function(){return err(_1vb);});}}}else{return E(_VY);}};if(0>_1vf){var _1vt=B(_1vg(0)),_1vu=E(_1vt),_1vv=_1vu.d;return new T4(0,E(_1vu.a),E(_1vu.b),_1vu.c,_1vv);}else{var _1vw=B(_1vg(_1vf+1|0)),_1vx=E(_1vw),_1vy=_1vx.d;return new T4(0,E(_1vx.a),E(_1vx.b),_1vx.c,_1vy);}};return new F(function(){return _9d(_1ve);});},_1vz=function(_1vA){return new T1(3,_1vA);},_1vB=function(_1vC,_1vD){var _1vE=new T(function(){var _1vF=E(_1vC),_1vG=B(_fK(_1vF.a,_1vF.b,_1vF.c,E(_1vD))),_1vH=B(_gH(E(_1vG.a)&4294967295,_gv,_1vF,_1vG.b));return new T2(0,_1vH.a,_1vH.b);});return new T2(0,new T1(3,new T(function(){return E(E(_1vE).a);})),new T(function(){return E(E(_1vE).b);}));},_1vI=function(_1vJ,_1vK){var _1vL=B(_1vB(_1vJ,_1vK));return new T2(0,_1vL.a,_1vL.b);},_1vM=function(_1vN,_1vO){var _1vP=E(_1vN),_1vQ=B(_fK(_1vP.a,_1vP.b,_1vP.c,E(_1vO))),_1vR=B(_gH(E(_1vQ.a)&4294967295,_gv,_1vP,_1vQ.b));return new T2(0,_1vR.a,_1vR.b);},_1vS=function(_1vT,_1vU,_1vV,_1vW){var _1vX=B(_109(_1vI,new T3(0,_1vT,_1vU,_1vV),_1vW)),_1vY=B(_fK(_1vT,_1vU,_1vV,E(_1vX.b))),_1vZ=B(_gH(E(_1vY.a)&4294967295,_1vM,new T3(0,_1vT,_1vU,_1vV),_1vY.b));return new T2(0,new T2(0,_1vX.a,_1vZ.a),_1vZ.b);},_1w0=function(_1w1,_1w2){var _1w3=E(_1w1),_1w4=B(_1vS(_1w3.a,_1w3.b,_1w3.c,_1w2));return new T2(0,_1w4.a,_1w4.b);},_1w5=function(_1w6){var _1w7=new T(function(){return B(unAppCStr("getSymbol ",new T(function(){return B(_co(0,_1w6&4294967295,_4));})));});return new F(function(){return _10z(_1w7);});},_1w8=function(_1w9,_1wa,_1wb,_1wc){var _1wd=B(_fE(_1w9,_1wa,_1wb,_1wc)),_1we=_1wd.b,_1wf=E(_1wd.a);switch(_1wf){case 0:var _1wg=new T(function(){var _1wh=B(_fK(_1w9,_1wa,_1wb,E(_1we))),_1wi=B(_fK(_1w9,_1wa,_1wb,E(_1wh.b)));return new T2(0,new T(function(){return new T2(0,E(_1wh.a)&4294967295,E(_1wi.a)&4294967295);}),_1wi.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1wg).a);}),_4),new T(function(){return E(E(_1wg).b);}));case 1:var _1wj=new T(function(){var _1wk=B(_fK(_1w9,_1wa,_1wb,E(_1we))),_1wl=B(_fK(_1w9,_1wa,_1wb,E(_1wk.b)));return new T2(0,new T(function(){return new T2(1,E(_1wk.a)&4294967295,E(_1wl.a)&4294967295);}),_1wl.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1wj).a);}),_4),new T(function(){return E(E(_1wj).b);}));case 2:var _1wm=new T(function(){var _1wn=B(_fK(_1w9,_1wa,_1wb,E(_1we))),_1wo=B(_fK(_1w9,_1wa,_1wb,E(_1wn.b)));return new T2(0,new T(function(){return new T2(2,E(_1wn.a)&4294967295,E(_1wo.a)&4294967295);}),_1wo.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1wm).a);}),_4),new T(function(){return E(E(_1wm).b);}));case 3:var _1wp=B(_fK(_1w9,_1wa,_1wb,E(_1we))),_1wq=B(_gH(E(_1wp.a)&4294967295,_1vM,new T3(0,_1w9,_1wa,_1wb),_1wp.b));return new T2(0,new T(function(){return B(_G(_1vz,_1wq.a));}),_1wq.b);case 4:var _1wr=new T(function(){var _1ws=new T3(0,_1w9,_1wa,_1wb),_1wt=B(_109(_1vI,_1ws,_1we)),_1wu=B(_109(_1w0,_1ws,_1wt.b));return new T2(0,new T2(4,_1wt.a,_1wu.a),_1wu.b);});return new T2(0,new T2(1,new T(function(){return E(E(_1wr).a);}),_4),new T(function(){return E(E(_1wr).b);}));default:return new F(function(){return _1w5(_1wf);});}},_1wv=function(_1ww,_1wx){var _1wy=E(_1ww),_1wz=B(_1w8(_1wy.a,_1wy.b,_1wy.c,E(_1wx)));return new T2(0,_1wz.a,_1wz.b);},_1wA=function(_1wB){var _1wC=E(_1wB);if(!_1wC._){return __Z;}else{return new F(function(){return _0(_1wC.a,new T(function(){return B(_1wA(_1wC.b));},1));});}},_1wD=function(_1wE,_1wF){var _1wG=new T(function(){var _1wH=B(_109(_1wv,_1wE,_1wF));return new T2(0,_1wH.a,_1wH.b);});return new T2(0,new T(function(){return B(_1vc(B(_1wA(E(_1wG).a))));}),new T(function(){return E(E(_1wG).b);}));},_1wI=function(_1wJ,_1wK,_1wL,_1wM){var _1wN=B(_fK(_1wJ,_1wK,_1wL,_1wM));return new F(function(){return _gH(E(_1wN.a)&4294967295,_gv,new T3(0,_1wJ,_1wK,_1wL),_1wN.b);});},_1wO=function(_1wP,_1wQ){var _1wR=E(_1wP),_1wS=B(_1wI(_1wR.a,_1wR.b,_1wR.c,E(_1wQ)));return new T2(0,_1wS.a,_1wS.b);},_1wT=function(_1wU){var _1wV=E(_1wU);return (_1wV._==0)?__Z:new T2(1,new T2(0,_MB,_1wV.a),new T(function(){return B(_1wT(_1wV.b));}));},_1wW=function(_1wX,_1wY,_1wZ,_1x0){var _1x1=B(_fK(_1wX,_1wY,_1wZ,_1x0)),_1x2=B(_gH(E(_1x1.a)&4294967295,_kR,new T3(0,_1wX,_1wY,_1wZ),_1x1.b)),_1x3=B(_fK(_1wX,_1wY,_1wZ,E(_1x2.b))),_1x4=new T(function(){return new T2(0,new T(function(){return B(_1wT(_1x2.a));}),E(_1x3.a)&4294967295);});return new T2(0,_1x4,_1x3.b);},_1x5=function(_1x6,_1x7){var _1x8=E(_1x6),_1x9=B(_1wW(_1x8.a,_1x8.b,_1x8.c,E(_1x7)));return new T2(0,_1x9.a,_1x9.b);},_1xa=new T(function(){return B(unCStr("getProduction"));}),_1xb=new T(function(){return B(_10z(_1xa));}),_1xc=function(_1xd,_1xe,_1xf,_1xg){var _1xh=B(_fE(_1xd,_1xe,_1xf,_1xg)),_1xi=_1xh.b;switch(E(_1xh.a)){case 0:var _1xj=B(_fK(_1xd,_1xe,_1xf,E(_1xi))),_1xk=B(_109(_1x5,new T3(0,_1xd,_1xe,_1xf),_1xj.b));return new T2(0,new T(function(){return new T2(0,E(_1xj.a)&4294967295,_1xk.a);}),_1xk.b);case 1:var _1xl=B(_fK(_1xd,_1xe,_1xf,E(_1xi)));return new T2(0,new T(function(){return new T1(1,E(_1xl.a)&4294967295);}),_1xl.b);default:return E(_1xb);}},_1xm=function(_1xn,_1xo){var _1xp=E(_1xn),_1xq=B(_1xc(_1xp.a,_1xp.b,_1xp.c,E(_1xo)));return new T2(0,_1xq.a,_1xq.b);},_1xr=function(_1xs,_1xt){var _1xu=new T(function(){var _1xv=E(_1xs),_1xw=B(_fK(_1xv.a,_1xv.b,_1xv.c,E(_1xt)));return new T2(0,new T(function(){return E(_1xw.a)&4294967295;}),_1xw.b);}),_1xx=new T(function(){var _1xy=B(_109(_1xm,_1xs,new T(function(){return E(E(_1xu).b);},1)));return new T2(0,_1xy.a,_1xy.b);});return new T2(0,new T2(0,new T(function(){return E(E(_1xu).a);}),new T(function(){var _1xz=E(E(_1xx).a);if(!_1xz._){return new T0(1);}else{return B(_PM(1,new T4(0,1,E(_1xz.a),E(_Nd),E(_Nd)),_1xz.b));}})),new T(function(){return E(E(_1xx).b);}));},_1xA=function(_1xB,_1xC){var _1xD=B(_1xr(_1xB,_1xC));return new T2(0,_1xD.a,_1xD.b);},_1xE=new T(function(){return B(err(_1vb));}),_1xF=function(_1xG,_1xH,_1xI,_1xJ){var _1xK=new T(function(){var _1xL=E(_1xI),_1xM=B(_fK(_1xL.a,_1xL.b,_1xL.c,E(_1xJ))),_1xN=E(_1xM.a)&4294967295,_1xO=B(_101(_1xN,_1xH,_1xL,_1xM.b));return new T2(0,new T2(0,_1xN,_1xO.a),_1xO.b);}),_1xP=new T(function(){var _1xQ=E(E(_1xK).a),_1xR=_1xQ.b,_1xS=new T(function(){return E(_1xQ.a)-1|0;});return B(A(_kf,[_1xG,_jX,new T2(0,_1va,_1xS),new T(function(){var _1xT=E(_1xS);if(0>_1xT){return B(_kh(B(_j1(0,-1)),_1xR));}else{var _1xU=_1xT+1|0;if(_1xU>=0){return B(_kh(B(_j1(0,_1xU-1|0)),_1xR));}else{return E(_1xE);}}})]));});return new T2(0,_1xP,new T(function(){return E(E(_1xK).b);}));},_1xV=function(_1xW,_1xX,_1xY,_1xZ){var _1y0=B(_fK(_1xW,_1xX,_1xY,_1xZ));return new F(function(){return _gH(E(_1y0.a)&4294967295,_gv,new T3(0,_1xW,_1xX,_1xY),_1y0.b);});},_1y1=function(_1y2,_1y3){var _1y4=E(_1y2),_1y5=B(_1xV(_1y4.a,_1y4.b,_1y4.c,E(_1y3)));return new T2(0,_1y5.a,_1y5.b);},_1y6=function(_1y7,_1y8,_1y9,_1ya){var _1yb=B(_fK(_1y7,_1y8,_1y9,_1ya)),_1yc=B(_fK(_1y7,_1y8,_1y9,E(_1yb.b))),_1yd=B(_1xF(_iF,_1y1,new T3(0,_1y7,_1y8,_1y9),_1yc.b));return new T2(0,new T(function(){var _1ye=E(_1yd.a);return new T6(0,E(_1yb.a)&4294967295,E(_1yc.a)&4294967295,E(_1ye.a),E(_1ye.b),_1ye.c,_1ye.d);}),_1yd.b);},_1yf=function(_1yg,_1yh){var _1yi=E(_1yg),_1yj=B(_1y6(_1yi.a,_1yi.b,_1yi.c,E(_1yh)));return new T2(0,_1yj.a,_1yj.b);},_1yk=0,_1yl=new T(function(){return B(unCStr("Negative range size"));}),_1ym=function(_1yn){var _1yo=B(_vm(_1yn,0)),_1yp=new T(function(){var _1yq=function(_){var _1yr=_1yo-1|0,_1ys=function(_,_1yt){var _1yu=function(_1yv){var _1yw=_1yv-1|0;if(0<=_1yw){var _1yx=function(_1yy,_){while(1){var _=E(_1yt).d["v"]["w8"][_1yy]=0;if(_1yy!=_1yw){var _1yz=_1yy+1|0;_1yy=_1yz;continue;}else{return _5;}}},_1yA=B(_1yx(0,_));return _1yt;}else{return _1yt;}};if(0>_1yr){return new F(function(){return _1yu(0);});}else{var _1yB=_1yr+1|0;if(_1yB>=0){return new F(function(){return _1yu(_1yB);});}else{return new F(function(){return err(_1yl);});}}},_1yC=function(_,_1yD,_1yE,_1yF,_1yG){var _1yH=function(_1yI){var _1yJ=function(_1yK,_1yL,_){while(1){if(_1yK!=_1yI){var _1yM=E(_1yL);if(!_1yM._){return _5;}else{var _=_1yG["v"]["w8"][_1yK]=E(_1yM.a),_1yN=_1yK+1|0;_1yK=_1yN;_1yL=_1yM.b;continue;}}else{return _5;}}},_1yO=B(_1yJ(0,_1yn,_));return new T4(0,E(_1yD),E(_1yE),_1yF,_1yG);};if(0>_1yr){return new F(function(){return _1yH(0);});}else{var _1yP=_1yr+1|0;if(_1yP>=0){return new F(function(){return _1yH(_1yP);});}else{return new F(function(){return err(_1yl);});}}};if(0>_1yr){var _1yQ=newByteArr(0),_1yR=B(_1ys(_,new T4(0,E(_1yk),E(_1yr),0,_1yQ))),_1yS=E(_1yR);return new F(function(){return _1yC(_,_1yS.a,_1yS.b,_1yS.c,_1yS.d);});}else{var _1yT=_1yr+1|0,_1yU=newByteArr(_1yT),_1yV=B(_1ys(_,new T4(0,E(_1yk),E(_1yr),_1yT,_1yU))),_1yW=E(_1yV);return new F(function(){return _1yC(_,_1yW.a,_1yW.b,_1yW.c,_1yW.d);});}};return B(_9d(_1yq));});return new T3(0,0,_1yo,_1yp);},_1yX=function(_1yY){return new F(function(){return _co(0,E(_1yY)&4294967295,_4);});},_1yZ=function(_1z0,_1z1){return new F(function(){return _co(0,E(_1z0)&4294967295,_1z1);});},_1z2=function(_1z3,_1z4){return new F(function(){return _3X(_1yZ,_1z3,_1z4);});},_1z5=function(_1z6,_1z7,_1z8){return new F(function(){return _co(E(_1z6),E(_1z7)&4294967295,_1z8);});},_1z9=new T3(0,_1z5,_1yX,_1z2),_1za=new T(function(){return B(unCStr("Word8"));}),_1zb=0,_1zc=255,_1zd=new T2(0,_1zb,_1zc),_1ze=new T2(1,_cm,_4),_1zf=function(_1zg,_1zh,_1zi,_1zj){var _1zk=new T(function(){var _1zl=new T(function(){var _1zm=new T(function(){var _1zn=new T(function(){var _1zo=new T(function(){var _1zp=E(_1zi),_1zq=new T(function(){return B(A3(_eI,_ey,new T2(1,new T(function(){return B(A3(_eU,_1zj,_eT,_1zp.a));}),new T2(1,new T(function(){return B(A3(_eU,_1zj,_eT,_1zp.b));}),_4)),_1ze));});return new T2(1,_cn,_1zq);});return B(unAppCStr(") is outside of bounds ",_1zo));},1);return B(_0(B(_co(0,E(_1zh),_4)),_1zn));});return B(unAppCStr("}: tag (",_1zm));},1);return B(_0(_1zg,_1zl));});return new F(function(){return err(B(unAppCStr("Enum.toEnum{",_1zk)));});},_1zr=function(_1zs,_1zt,_1zu,_1zv){return new F(function(){return _1zf(_1zt,_1zu,_1zv,_1zs);});},_1zw=function(_1zx){return new F(function(){return _1zr(_1z9,_1za,_1zx,_1zd);});},_1zy=function(_1zz){if(_1zz<0){return new F(function(){return _1zw(_1zz);});}else{if(_1zz>255){return new F(function(){return _1zw(_1zz);});}else{return _1zz>>>0;}}},_1zA=function(_1zB){return new F(function(){return _1zy(E(_1zB));});},_1zC=function(_1zD){var _1zE=E(_1zD);if(!_1zE._){return __Z;}else{var _1zF=_1zE.b,_1zG=E(_1zE.a),_1zH=function(_1zI){return (_1zG>=2048)?new T2(1,new T(function(){var _1zJ=224+B(_nu(_1zG,4096))|0;if(_1zJ>>>0>1114111){return B(_gc(_1zJ));}else{return _1zJ;}}),new T2(1,new T(function(){var _1zK=128+B(_nu(B(_oy(_1zG,4096)),64))|0;if(_1zK>>>0>1114111){return B(_gc(_1zK));}else{return _1zK;}}),new T2(1,new T(function(){var _1zL=128+B(_oy(_1zG,64))|0;if(_1zL>>>0>1114111){return B(_gc(_1zL));}else{return _1zL;}}),new T(function(){return B(_1zC(_1zF));})))):new T2(1,new T(function(){var _1zM=192+B(_nu(_1zG,64))|0;if(_1zM>>>0>1114111){return B(_gc(_1zM));}else{return _1zM;}}),new T2(1,new T(function(){var _1zN=128+B(_oy(_1zG,64))|0;if(_1zN>>>0>1114111){return B(_gc(_1zN));}else{return _1zN;}}),new T(function(){return B(_1zC(_1zF));})));};if(_1zG<=0){return new F(function(){return _1zH(_);});}else{if(_1zG>=128){return new F(function(){return _1zH(_);});}else{return new T2(1,_1zG,new T(function(){return B(_1zC(_1zF));}));}}}},_1zO=new T(function(){return B(unCStr("linref"));}),_1zP=new T(function(){return B(_1zC(_1zO));}),_1zQ=new T(function(){return B(_G(_1zA,_1zP));}),_1zR=new T(function(){var _1zS=B(_1ym(_1zQ));return new T3(0,_1zS.a,_1zS.b,_1zS.c);}),_1zT=function(_1zU,_1zV){var _1zW=E(_1zU),_1zX=B(_fV(_1zW.a,_1zW.b,_1zW.c,E(_1zV))),_1zY=B(_1xF(_mu,_kR,_1zW,_1zX.b));return new T2(0,new T(function(){var _1zZ=E(_1zY.a);return new T5(0,_1zX.a,E(_1zZ.a),E(_1zZ.b),_1zZ.c,_1zZ.d);}),_1zY.b);},_1A0=new T(function(){return B(_1q2(_UZ,_4));}),_1A1=new T2(0,0,0),_1A2=new T2(1,_1A1,_4),_1A3=new T(function(){return B(_1vc(_1A2));}),_1A4=new T2(1,_1A3,_4),_1A5=function(_1A6,_1A7,_1A8,_1A9){var _1Aa=new T3(0,_1A6,_1A7,_1A8),_1Ab=B(_10i(_12A,_12v,_1Aa,_1A9)),_1Ac=B(_10i(_12A,_1wO,_1Aa,_1Ab.b)),_1Ad=B(_fK(_1A6,_1A7,_1A8,E(_1Ac.b))),_1Ae=E(_1Ad.a)&4294967295,_1Af=B(_101(_1Ae,_1wD,_1Aa,_1Ad.b)),_1Ag=B(_fK(_1A6,_1A7,_1A8,E(_1Af.b))),_1Ah=E(_1Ag.a)&4294967295,_1Ai=B(_101(_1Ah,_1zT,_1Aa,_1Ag.b)),_1Aj=B(_Rl(_Qm,_1A6,_1A7,_1A8,E(_1Ai.b))),_1Ak=new T(function(){var _1Al=B(_109(_1xA,_1Aa,_1Aj.b));return new T2(0,_1Al.a,_1Al.b);}),_1Am=B(_10i(_12A,_1yf,_1Aa,new T(function(){return E(E(_1Ak).b);},1))),_1An=B(_fK(_1A6,_1A7,_1A8,E(_1Am.b))),_1Ao=new T(function(){var _1Ap=E(_1An.a)&4294967295,_1Aq=new T(function(){var _1Ar=function(_){var _1As=(_1Ae+1|0)-1|0,_1At=function(_1Au){if(_1Au>=0){var _1Av=newArr(_1Au,_VW),_1Aw=_1Av,_1Ax=function(_1Ay){var _1Az=function(_1AA,_1AB,_){while(1){if(_1AA!=_1Ay){var _1AC=E(_1AB);if(!_1AC._){return _5;}else{var _=_1Aw[_1AA]=_1AC.a,_1AD=_1AA+1|0;_1AA=_1AD;_1AB=_1AC.b;continue;}}else{return _5;}}},_1AE=B(_1Az(0,new T(function(){return B(_0(_1Af.a,_1A4));},1),_));return new T4(0,E(_1va),E(_1As),_1Au,_1Aw);};if(0>_1As){return new F(function(){return _1Ax(0);});}else{var _1AF=_1As+1|0;if(_1AF>=0){return new F(function(){return _1Ax(_1AF);});}else{return E(_1xE);}}}else{return E(_VY);}};if(0>_1As){var _1AG=B(_1At(0)),_1AH=E(_1AG),_1AI=_1AH.d;return new T4(0,E(_1AH.a),E(_1AH.b),_1AH.c,_1AI);}else{var _1AJ=B(_1At(_1As+1|0)),_1AK=E(_1AJ),_1AL=_1AK.d;return new T4(0,E(_1AK.a),E(_1AK.b),_1AK.c,_1AL);}};return B(_9d(_1Ar));}),_1AM=new T(function(){var _1AN=_1Ap-1|0;if(0<=_1AN){var _1AO=function(_1AP){return new T2(1,new T2(0,_1AP,new T2(1,_1Ah,_4)),new T(function(){if(_1AP!=_1AN){return B(_1AO(_1AP+1|0));}else{return __Z;}}));};return B(_1q2(_UZ,B(_1AO(0))));}else{return E(_1A0);}}),_1AQ=new T(function(){var _1AR=function(_){var _1AS=(_1Ah+1|0)-1|0,_1AT=function(_1AU){if(_1AU>=0){var _1AV=newArr(_1AU,_VW),_1AW=_1AV,_1AX=function(_1AY){var _1AZ=function(_1B0,_1B1,_){while(1){if(_1B0!=_1AY){var _1B2=E(_1B1);if(!_1B2._){return _5;}else{var _=_1AW[_1B0]=_1B2.a,_1B3=_1B0+1|0;_1B0=_1B3;_1B1=_1B2.b;continue;}}else{return _5;}}},_1B4=new T(function(){var _1B5=new T(function(){var _1B6=function(_){var _1B7=newByteArr(4),_1B8=_1B7,_1B9=function(_1Ba,_){while(1){var _=_1B8["v"]["i32"][_1Ba]=0,_1Bb=E(_1Ba);if(!_1Bb){return _5;}else{_1Ba=_1Bb+1|0;continue;}}},_1Bc=B(_1B9(0,_)),_1Bd=function(_1Be,_1Bf,_){while(1){var _1Bg=E(_1Be);if(_1Bg==1){return _5;}else{var _1Bh=E(_1Bf);if(!_1Bh._){return _5;}else{var _=_1B8["v"]["i32"][_1Bg]=E(_1Bh.a);_1Be=_1Bg+1|0;_1Bf=_1Bh.b;continue;}}}},_1Bi=B(_1Bd(0,new T2(1,_1Ae,_4),_));return new T4(0,E(_1va),E(_1va),1,_1B8);},_1Bj=B(_9d(_1B6));return new T5(0,_1zR,E(_1Bj.a),E(_1Bj.b),_1Bj.c,_1Bj.d);});return B(_0(_1Ai.a,new T2(1,_1B5,_4)));},1),_1Bk=B(_1AZ(0,_1B4,_));return new T4(0,E(_1va),E(_1AS),_1AU,_1AW);};if(0>_1AS){return new F(function(){return _1AX(0);});}else{var _1Bl=_1AS+1|0;if(_1Bl>=0){return new F(function(){return _1AX(_1Bl);});}else{return E(_1xE);}}}else{return E(_VY);}};if(0>_1AS){var _1Bm=B(_1AT(0)),_1Bn=E(_1Bm),_1Bo=_1Bn.d;return new T4(0,E(_1Bn.a),E(_1Bn.b),_1Bn.c,_1Bo);}else{var _1Bp=B(_1AT(_1AS+1|0)),_1Bq=E(_1Bp),_1Br=_1Bq.d;return new T4(0,E(_1Bq.a),E(_1Bq.b),_1Bq.c,_1Br);}};return B(_9d(_1AR));});return {_:0,a:_1Ab.a,b:_1Ac.a,c:_1AQ,d:_1Aj.a,e:_1AM,f:_1Aq,g:new T(function(){var _1Bs=E(E(_1Ak).a);if(!_1Bs._){return new T0(2);}else{var _1Bt=E(_1Bs.a);return B(_QE(E(_1Bt.a),_1Bt.b,_1Bs.b,_Qn));}}),h:_UZ,i:_RI,j:_1Am.a,k:_UZ,l:_1Ap};});return new T2(0,_1Ao,_1An.b);},_1Bu=function(_1Bv,_1Bw){var _1Bx=E(_1Bv),_1By=B(_1A5(_1Bx.a,_1Bx.b,_1Bx.c,_1Bw));return new T2(0,_1By.a,_1By.b);},_1Bz=function(_1BA,_1BB){var _1BC=E(_1BA),_1BD=B(_Jq(_JV,_Md,_1BC,_1BB)),_1BE=B(_fV(_1BC.a,_1BC.b,_1BC.c,E(_1BD.b)));return new T2(0,new T2(0,_1BD.a,_1BE.a),_1BE.b);},_1BF=function(_1BG,_1BH){var _1BI=new T(function(){var _1BJ=B(_109(_11v,_1BG,_1BH));return new T2(0,_1BJ.a,_1BJ.b);}),_1BK=B(_109(_1Bz,_1BG,new T(function(){return E(E(_1BI).b);},1)));return new T2(0,new T2(0,new T(function(){return E(E(_1BI).a);}),_1BK.a),_1BK.b);},_1BL=function(_1BM,_1BN){var _1BO=B(_1BF(_1BM,_1BN));return new T2(0,_1BO.a,_1BO.b);},_1BP=function(_1BQ,_1BR,_1BS,_1BT,_1BU){var _1BV=B(_fV(_1BR,_1BS,_1BT,_1BU)),_1BW=new T3(0,_1BR,_1BS,_1BT),_1BX=B(_10i(_12A,_12v,_1BW,_1BV.b)),_1BY=B(_10i(_12A,_12q,_1BW,_1BX.b)),_1BZ=B(_10i(_12A,_1BL,_1BW,_1BY.b)),_1C0=B(_10i(_12A,_1Bu,_1BW,_1BZ.b));return new T2(0,new T4(0,_1BQ,_1BV.a,new T3(0,_1BX.a,new T(function(){return B(_ZI(_1v6,_1BY.a));}),new T(function(){return B(_ZI(_1v3,_1BZ.a));})),new T(function(){return B(_ZI(_1uZ,_1C0.a));})),_1C0.b);},_1C1=function(_1C2,_1C3,_1C4,_1C5){var _1C6=B(_10i(_12A,_12v,new T3(0,_1C2,_1C3,_1C4),_1C5));return new F(function(){return _1BP(_1C6.a,_1C2,_1C3,_1C4,E(_1C6.b));});},_1C7=function(_1C8,_1C9){var _1Ca=E(_1C9);return new F(function(){return _1sT(_1Ca.a,_1Ca.b,_1Ca.c,_1Ca.d,_1Ca.e,_1Ca.f,_1Ca.g,_1Ca.j,_1Ca.l);});},_1Cb=function(_1Cc,_1Cd,_1Ce,_1Cf){var _1Cg=new T3(0,_1Cc,_1Cd,_1Ce),_1Ch=B(_WL(_1Cg,_1Cf)),_1Ci=B(_WL(_1Cg,_1Ch.b)),_1Cj=_1Ci.a,_1Ck=_1Ci.b,_1Cl=E(_1Ch.a),_1Cm=function(_1Cn){var _1Co=E(_1Cl);if(_1Co==1){var _1Cp=E(_1Cj);if(!E(_1Cp)){return new F(function(){return _1C1(_1Cc,_1Cd,_1Ce,_1Ck);});}else{return new F(function(){return _WF(_1Cp,1);});}}else{return new F(function(){return _WF(_1Cj,_1Co);});}};if(E(_1Cl)==2){if(E(_1Cj)>1){return new F(function(){return _1Cm(_);});}else{var _1Cq=B(_UM(_g9,_My,_1Cc,_1Cd,_1Ce,E(_1Ck))),_1Cr=B(_fV(_1Cc,_1Cd,_1Ce,E(_1Cq.b))),_1Cs=B(_ZM(_1Cc,_1Cd,_1Ce,E(_1Cr.b))),_1Ct=_1Cs.a,_1Cu=B(_UM(_g9,_WD,_1Cc,_1Cd,_1Ce,E(_1Cs.b))),_1Cv=new T(function(){return B(_ZI(function(_1Cw){return new F(function(){return _1C7(_1Ct,_1Cw);});},_1Cu.a));});return new T2(0,new T4(0,_1Cq.a,_1Cr.a,_1Ct,_1Cv),_1Cu.b);}}else{return new F(function(){return _1Cm(_);});}},_1Cx=0,_1Cy=new T(function(){return new T2(0,_191,_1Cz);}),_1Cz=function(_1CA,_1CB){return (!B(A3(_qe,_1Cy,_1CA,_1CB)))?true:false;},_1CC=new T2(0,_191,_1Cz),_1CD=function(_1CE,_1CF){var _1CG=E(_1CE);if(!_1CG._){var _1CH=E(_1CF);if(!_1CH._){var _1CI=E(_1CG.a),_1CJ=E(_1CH.a);if(!B(_13e(_1CI.a,_1CI.b,_1CI.c,_1CJ.a,_1CJ.b,_1CJ.c))){return false;}else{return new F(function(){return _19g(_1CC,_1CG.b,_1CH.b);});}}else{return false;}}else{return (E(_1CF)._==0)?false:true;}},_1CK=function(_1CL,_1CM){return (!B(_1CN(_1CL,_1CM)))?true:false;},_1CO=new T(function(){return new T2(0,_1CN,_1CK);}),_1CN=function(_1CP,_1CQ){var _1CR=E(_1CP);if(!_1CR._){var _1CS=E(_1CQ);if(!_1CS._){var _1CT=E(_1CR.a),_1CU=E(_1CS.a);if(!B(_13e(_1CT.a,_1CT.b,_1CT.c,_1CU.a,_1CU.b,_1CU.c))){return false;}else{if(!B(_1CD(_1CR.b,_1CS.b))){return false;}else{return new F(function(){return _19g(_1CO,_1CR.c,_1CS.c);});}}}else{return false;}}else{var _1CV=E(_1CQ);if(!_1CV._){return false;}else{return new F(function(){return _191(_1CR.a,_1CV.a);});}}},_1CW=function(_1CX,_1CY){var _1CZ=E(_1CY);if(!_1CZ._){return __Z;}else{var _1D0=_1CZ.a,_1D1=E(_1CX);return (_1D1==1)?new T2(1,_1D0,_4):new T2(1,_1D0,new T(function(){return B(_1CW(_1D1-1|0,_1CZ.b));}));}},_1D2=new T(function(){return B(unCStr("suggestionList"));}),_1D3=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1D4=function(_){return new F(function(){return __app1(E(_1D3),"div");});},_1D5=new T(function(){return eval("(function(e){while(e.firstChild){e.removeChild(e.firstChild);}})");}),_1D6=new T(function(){return eval("(function(c,p){p.removeChild(c);})");}),_1D7=new T(function(){return eval("document.body");}),_1D8=function(_,_1D9){var _1Da=E(_1D9);if(!_1Da._){return _5;}else{var _1Db=E(_1Da.a),_1Dc=__app1(E(_1D5),_1Db),_1Dd=__app2(E(_1D6),_1Db,E(_1D7));return new F(function(){return _u(_);});}},_1De=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1Df=function(_1Dg,_){var _1Dh=__app1(E(_1De),toJSStr(E(_1Dg))),_1Di=__eq(_1Dh,E(_D));if(!E(_1Di)){var _1Dj=__isUndef(_1Dh);if(!E(_1Dj)){return new F(function(){return _1D8(_,new T1(1,_1Dh));});}else{return new F(function(){return _1D8(_,_4l);});}}else{return new F(function(){return _1D8(_,_4l);});}},_1Dk=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_1Dl=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:77:5-14"));}),_1Dm=new T(function(){return B(unCStr("score"));}),_1Dn=new T(function(){return eval("(function(s){return document.createTextNode(s);})");}),_1Do=function(_1Dp,_){var _1Dq=__app1(E(_1De),toJSStr(E(_1Dm))),_1Dr=__eq(_1Dq,E(_D)),_1Ds=function(_,_1Dt){var _1Du=E(_1Dt);if(!_1Du._){return new F(function(){return _c1(_1Dl,_);});}else{var _1Dv=rMV(E(_1Dp)),_1Dw=E(_1Du.a),_1Dx=__app1(E(_1D5),_1Dw),_1Dy=__app1(E(_1Dn),toJSStr(B(_co(0,E(E(_1Dv).e),_4)))),_1Dz=__app2(E(_1Dk),_1Dy,_1Dw);return new F(function(){return _u(_);});}};if(!E(_1Dr)){var _1DA=__isUndef(_1Dq);if(!E(_1DA)){return new F(function(){return _1Ds(_,new T1(1,_1Dq));});}else{return new F(function(){return _1Ds(_,_4l);});}}else{return new F(function(){return _1Ds(_,_4l);});}},_1DB=new T(function(){return B(unCStr("hover"));}),_1DC=new T(function(){return eval("(function(e,c) {e.classList.toggle(c);})");}),_1DD=function(_1DE,_){var _1DF=__app2(E(_1DC),_1DE,toJSStr(E(_1DB)));return new F(function(){return _u(_);});},_1DG=6,_1DH=5,_1DI=new T(function(){return B(unCStr("div"));}),_1DJ=function(_1DK){return E(E(_1DK).a);},_1DL=function(_1DM){return E(E(_1DM).b);},_1DN=function(_1DO){return E(E(_1DO).a);},_1DP=function(_){return new F(function(){return nMV(_4l);});},_1DQ=new T(function(){return B(_z(_1DP));}),_1DR=function(_1DS){return E(E(_1DS).b);},_1DT=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1DU=function(_1DV,_1DW,_1DX,_1DY,_1DZ,_1E0){var _1E1=B(_1DJ(_1DV)),_1E2=B(_2z(_1E1)),_1E3=new T(function(){return B(_6i(_1E1));}),_1E4=new T(function(){return B(_dD(_1E2));}),_1E5=new T(function(){return B(A1(_1DW,_1DY));}),_1E6=new T(function(){return B(A2(_1DN,_1DX,_1DZ));}),_1E7=function(_1E8){return new F(function(){return A1(_1E4,new T3(0,_1E6,_1E5,_1E8));});},_1E9=function(_1Ea){var _1Eb=new T(function(){var _1Ec=new T(function(){var _1Ed=__createJSFunc(2,function(_1Ee,_){var _1Ef=B(A2(E(_1Ea),_1Ee,_));return _D;}),_1Eg=_1Ed;return function(_){return new F(function(){return __app3(E(_1DT),E(_1E5),E(_1E6),_1Eg);});};});return B(A1(_1E3,_1Ec));});return new F(function(){return A3(_1V,_1E2,_1Eb,_1E7);});},_1Eh=new T(function(){var _1Ei=new T(function(){return B(_6i(_1E1));}),_1Ej=function(_1Ek){var _1El=new T(function(){return B(A1(_1Ei,function(_){var _=wMV(E(_1DQ),new T1(1,_1Ek));return new F(function(){return A(_1DL,[_1DX,_1DZ,_1Ek,_]);});}));});return new F(function(){return A3(_1V,_1E2,_1El,_1E0);});};return B(A2(_1DR,_1DV,_1Ej));});return new F(function(){return A3(_1V,_1E2,_1Eh,_1E9);});},_1Em=function(_1En,_1Eo,_1Ep,_){var _1Eq=__app1(E(_1Dn),toJSStr(E(_1Eo))),_1Er=__app1(E(_1D3),toJSStr(E(_1DI))),_1Es=_1Er,_1Et=B(A(_1DU,[_dK,_dB,_dA,_1Es,_1DH,function(_1Eu,_){return new F(function(){return _1DD(_1Es,_);});},_])),_1Ev=B(A(_1DU,[_dK,_dB,_dA,_1Es,_1DG,function(_1Ew,_){return new F(function(){return _1DD(_1Es,_);});},_])),_1Ex=B(A(_1DU,[_dK,_dB,_dA,_1Es,_1Cx,_1Ep,_])),_1Ey=E(_1Dk),_1Ez=__app2(_1Ey,_1Eq,_1Es),_1EA=__app2(_1Ey,_1Es,E(_1En));return _5;},_1EB=new T(function(){return eval("alert");}),_1EC=3,_1ED=function(_1EE){return new F(function(){return fromJSStr(E(_1EE));});},_1EF=function(_1EG){return E(E(_1EG).a);},_1EH=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_1EI=function(_1EJ,_1EK,_1EL,_1EM){var _1EN=new T(function(){var _1EO=function(_){var _1EP=__app2(E(_1EH),B(A2(_1EF,_1EJ,_1EL)),E(_1EM));return new T(function(){return String(_1EP);});};return E(_1EO);});return new F(function(){return A2(_6i,_1EK,_1EN);});},_1EQ=function(_1ER,_1ES,_1ET,_1EU){var _1EV=B(_2z(_1ES)),_1EW=new T(function(){return B(_dD(_1EV));}),_1EX=function(_1EY){return new F(function(){return A1(_1EW,new T(function(){return B(_1ED(_1EY));}));});},_1EZ=new T(function(){return B(_1EI(_1ER,_1ES,_1ET,new T(function(){return toJSStr(E(_1EU));},1)));});return new F(function(){return A3(_1V,_1EV,_1EZ,_1EX);});},_1F0=new T(function(){return B(unCStr("!!: negative index"));}),_1F1=new T(function(){return B(_0(_eD,_1F0));}),_1F2=new T(function(){return B(err(_1F1));}),_1F3=new T(function(){return B(unCStr("!!: index too large"));}),_1F4=new T(function(){return B(_0(_eD,_1F3));}),_1F5=new T(function(){return B(err(_1F4));}),_1F6=function(_1F7,_1F8){while(1){var _1F9=E(_1F7);if(!_1F9._){return E(_1F5);}else{var _1Fa=E(_1F8);if(!_1Fa){return E(_1F9.a);}else{_1F7=_1F9.b;_1F8=_1Fa-1|0;continue;}}}},_1Fb=function(_1Fc,_1Fd){if(_1Fd>=0){return new F(function(){return _1F6(_1Fc,_1Fd);});}else{return E(_1F2);}},_1Fe=function(_1Ff,_1Fg){var _1Fh=E(_1Ff);if(!_1Fh._){var _1Fi=E(_1Fh.c);if(!_1Fi._){return __Z;}else{var _1Fj=E(_1Fg);return (_1Fj>=0)?(_1Fj<B(_vm(_1Fi,0)))?new T1(1,new T(function(){return B(_1Fb(_1Fi,_1Fj));})):__Z:__Z;}}else{return __Z;}},_1Fk=function(_1Fl,_1Fm){while(1){var _1Fn=B((function(_1Fo,_1Fp){var _1Fq=E(_1Fp);if(!_1Fq._){return new T1(1,_1Fo);}else{var _1Fr=_1Fq.a,_1Fs=E(_1Fq.b);if(!_1Fs._){return new F(function(){return _1Fe(_1Fo,_1Fr);});}else{var _1Ft=E(_1Fo);if(!_1Ft._){var _1Fu=E(_1Ft.c);if(!_1Fu._){return __Z;}else{var _1Fv=E(_1Fr);if(_1Fv>=0){if(_1Fv<B(_vm(_1Fu,0))){_1Fl=new T(function(){return B(_1Fb(_1Fu,_1Fv));});_1Fm=_1Fs;return __continue;}else{return __Z;}}else{return __Z;}}}else{return __Z;}}}})(_1Fl,_1Fm));if(_1Fn!=__continue){return _1Fn;}}},_1Fw=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1Fx=new T(function(){return B(err(_1Fw));}),_1Fy=function(_1Fz,_1FA){var _1FB=E(_1Fz),_1FC=E(_1FA);return (B(_13l(_1FB.a,_1FB.b,_1FB.c,_1FC.a,_1FC.b,_1FC.c))==0)?true:false;},_1FD=function(_1FE){var _1FF=E(_1FE);return new F(function(){return _G(_135,B(_Jb(_1FF.a,_1FF.b,_1FF.c)));});},_1FG=function(_1FH,_1FI){return (B(_12F(B(_1FD(_1FH)),B(_1FD(_1FI))))==2)?false:true;},_1FJ=function(_1FK,_1FL){var _1FM=E(_1FK),_1FN=E(_1FL);return (B(_13l(_1FM.a,_1FM.b,_1FM.c,_1FN.a,_1FN.b,_1FN.c))==2)?true:false;},_1FO=function(_1FP,_1FQ){var _1FR=E(_1FP),_1FS=E(_1FQ);return (B(_13l(_1FR.a,_1FR.b,_1FR.c,_1FS.a,_1FS.b,_1FS.c))==0)?false:true;},_1FT=function(_1FU,_1FV){return (B(_12F(B(_1FD(_1FU)),B(_1FD(_1FV))))==2)?E(_1FU):E(_1FV);},_1FW=function(_1FX,_1FY){return (B(_12F(B(_1FD(_1FX)),B(_1FD(_1FY))))==2)?E(_1FY):E(_1FX);},_1FZ={_:0,a:_1CC,b:_1bt,c:_1Fy,d:_1FG,e:_1FJ,f:_1FO,g:_1FT,h:_1FW},_1G0=function(_1G1,_1G2){var _1G3=E(_1G1);if(!_1G3._){var _1G4=E(_1G2);if(!_1G4._){var _1G5=E(_1G3.a),_1G6=E(_1G4.a);switch(B(_13l(_1G5.a,_1G5.b,_1G5.c,_1G6.a,_1G6.b,_1G6.c))){case 0:return 0;case 1:return new F(function(){return _1c5(_1FZ,_1G3.b,_1G4.b);});break;default:return 2;}}else{return 0;}}else{return (E(_1G2)._==0)?2:1;}},_1G7=function(_1G8,_1G9){var _1Ga=E(_1G8);if(!_1Ga._){var _1Gb=E(_1G9);if(!_1Gb._){var _1Gc=E(_1Ga.a),_1Gd=E(_1Gb.a);switch(B(_13l(_1Gc.a,_1Gc.b,_1Gc.c,_1Gd.a,_1Gd.b,_1Gd.c))){case 0:return true;case 1:switch(B(_1G0(_1Ga.b,_1Gb.b))){case 0:return true;case 1:return (B(_1c5(_1Ge,_1Ga.c,_1Gb.c))==0)?true:false;default:return false;}break;default:return false;}}else{return true;}}else{var _1Gf=E(_1G9);if(!_1Gf._){return false;}else{return new F(function(){return _1Fy(_1Ga.a,_1Gf.a);});}}},_1Gg=function(_1Gh,_1Gi){var _1Gj=E(_1Gh);if(!_1Gj._){var _1Gk=E(_1Gi);if(!_1Gk._){var _1Gl=E(_1Gj.a),_1Gm=E(_1Gk.a);switch(B(_13l(_1Gl.a,_1Gl.b,_1Gl.c,_1Gm.a,_1Gm.b,_1Gm.c))){case 0:return true;case 1:switch(B(_1G0(_1Gj.b,_1Gk.b))){case 0:return true;case 1:return (B(_1c5(_1Ge,_1Gj.c,_1Gk.c))==2)?false:true;default:return false;}break;default:return false;}}else{return true;}}else{var _1Gn=E(_1Gi);if(!_1Gn._){return false;}else{return new F(function(){return _1FG(_1Gj.a,_1Gn.a);});}}},_1Go=function(_1Gp,_1Gq){var _1Gr=E(_1Gp);if(!_1Gr._){var _1Gs=E(_1Gq);if(!_1Gs._){var _1Gt=E(_1Gr.a),_1Gu=E(_1Gs.a);switch(B(_13l(_1Gt.a,_1Gt.b,_1Gt.c,_1Gu.a,_1Gu.b,_1Gu.c))){case 0:return false;case 1:switch(B(_1G0(_1Gr.b,_1Gs.b))){case 0:return false;case 1:return (B(_1c5(_1Ge,_1Gr.c,_1Gs.c))==2)?true:false;default:return true;}break;default:return true;}}else{return false;}}else{var _1Gv=E(_1Gq);if(!_1Gv._){return true;}else{return new F(function(){return _1FJ(_1Gr.a,_1Gv.a);});}}},_1Gw=function(_1Gx,_1Gy){var _1Gz=E(_1Gx);if(!_1Gz._){var _1GA=E(_1Gy);if(!_1GA._){var _1GB=E(_1Gz.a),_1GC=E(_1GA.a);switch(B(_13l(_1GB.a,_1GB.b,_1GB.c,_1GC.a,_1GC.b,_1GC.c))){case 0:return false;case 1:switch(B(_1G0(_1Gz.b,_1GA.b))){case 0:return false;case 1:return (B(_1c5(_1Ge,_1Gz.c,_1GA.c))==0)?false:true;default:return true;}break;default:return true;}}else{return false;}}else{var _1GD=E(_1Gy);if(!_1GD._){return true;}else{return new F(function(){return _1FO(_1Gz.a,_1GD.a);});}}},_1GE=function(_1GF,_1GG){var _1GH=E(_1GF);if(!_1GH._){var _1GI=E(_1GG);if(!_1GI._){var _1GJ=E(_1GH.a),_1GK=E(_1GI.a);switch(B(_13l(_1GJ.a,_1GJ.b,_1GJ.c,_1GK.a,_1GK.b,_1GK.c))){case 0:return 0;case 1:switch(B(_1G0(_1GH.b,_1GI.b))){case 0:return 0;case 1:return new F(function(){return _1c5(_1Ge,_1GH.c,_1GI.c);});break;default:return 2;}break;default:return 2;}}else{return 0;}}else{var _1GL=E(_1GG);if(!_1GL._){return 2;}else{return new F(function(){return _1bt(_1GH.a,_1GL.a);});}}},_1GM=function(_1GN,_1GO){return (!B(_1Gg(_1GN,_1GO)))?E(_1GN):E(_1GO);},_1GP=function(_1GQ,_1GR){return (!B(_1Gg(_1GQ,_1GR)))?E(_1GR):E(_1GQ);},_1Ge=new T(function(){return {_:0,a:_1CO,b:_1GE,c:_1G7,d:_1Gg,e:_1Go,f:_1Gw,g:_1GM,h:_1GP};}),_1GS=function(_1GT,_1GU){var _1GV=E(_1GT),_1GW=E(_1GU);if(!_1GW._){var _1GX=_1GW.b,_1GY=_1GW.c,_1GZ=_1GW.d;switch(B(_1GE(_1GV,_1GX))){case 0:return new F(function(){return _NU(_1GX,B(_1GS(_1GV,_1GY)),_1GZ);});break;case 1:return new F(function(){return _15K(_1GY,_1GZ);});break;default:return new F(function(){return _Ni(_1GX,_1GY,B(_1GS(_1GV,_1GZ)));});}}else{return new T0(1);}},_1H0=function(_1H1,_1H2){var _1H3=E(_1H1);if(!_1H3._){var _1H4=_1H3.c,_1H5=B(_vm(_1H4,0));if(0<=_1H5){var _1H6=function(_1H7,_1H8){var _1H9=E(_1H8);if(!_1H9._){return __Z;}else{return new F(function(){return _0(B(_1H0(_1H9.a,new T(function(){return B(_0(_1H2,new T2(1,_1H7,_4)));}))),new T(function(){if(_1H7!=_1H5){return B(_1H6(_1H7+1|0,_1H9.b));}else{return __Z;}},1));});}};return new F(function(){return _1H6(0,_1H4);});}else{return __Z;}}else{return new T2(1,new T2(0,_1H2,_1H3.a),_4);}},_1Ha=function(_1Hb,_1Hc){var _1Hd=E(_1Hb),_1He=E(_1Hc);if(!_1He._){var _1Hf=_1He.b,_1Hg=_1He.c,_1Hh=_1He.d;switch(B(_1c5(_1Ge,B(_1nK(_4,_1Hd)),B(_1nK(_4,_1Hf))))){case 0:return new F(function(){return _Ni(_1Hf,B(_1Ha(_1Hd,_1Hg)),_1Hh);});break;case 1:return new T4(0,_1He.a,E(_1Hd),E(_1Hg),E(_1Hh));default:return new F(function(){return _NU(_1Hf,_1Hg,B(_1Ha(_1Hd,_1Hh)));});}}else{return new T4(0,1,E(_1Hd),E(_Nd),E(_Nd));}},_1Hi=function(_1Hj,_1Hk){while(1){var _1Hl=E(_1Hk);if(!_1Hl._){return E(_1Hj);}else{var _1Hm=B(_1Ha(_1Hl.a,_1Hj));_1Hj=_1Hm;_1Hk=_1Hl.b;continue;}}},_1Hn=function(_1Ho){return new F(function(){return _1nK(_4,_1Ho);});},_1Hp=function(_1Hq,_1Hr){var _1Hs=E(_1Hr);if(!_1Hs._){return new T3(0,_Nd,_4,_4);}else{var _1Ht=_1Hs.a,_1Hu=E(_1Hq);if(_1Hu==1){var _1Hv=E(_1Hs.b);return (_1Hv._==0)?new T3(0,new T(function(){return new T4(0,1,E(_1Ht),E(_Nd),E(_Nd));}),_4,_4):(B(_1c5(_1Ge,B(_1Hn(_1Ht)),B(_1Hn(_1Hv.a))))==0)?new T3(0,new T(function(){return new T4(0,1,E(_1Ht),E(_Nd),E(_Nd));}),_1Hv,_4):new T3(0,new T(function(){return new T4(0,1,E(_1Ht),E(_Nd),E(_Nd));}),_4,_1Hv);}else{var _1Hw=B(_1Hp(_1Hu>>1,_1Hs)),_1Hx=_1Hw.a,_1Hy=_1Hw.c,_1Hz=E(_1Hw.b);if(!_1Hz._){return new T3(0,_1Hx,_4,_1Hy);}else{var _1HA=_1Hz.a,_1HB=E(_1Hz.b);if(!_1HB._){return new T3(0,new T(function(){return B(_OA(_1HA,_1Hx));}),_4,_1Hy);}else{if(!B(_1c5(_1Ge,B(_1Hn(_1HA)),B(_1Hn(_1HB.a))))){var _1HC=B(_1Hp(_1Hu>>1,_1HB));return new T3(0,new T(function(){return B(_Pe(_1HA,_1Hx,_1HC.a));}),_1HC.b,_1HC.c);}else{return new T3(0,_1Hx,_4,_1Hz);}}}}}},_1HD=function(_1HE,_1HF,_1HG){while(1){var _1HH=E(_1HG);if(!_1HH._){return E(_1HF);}else{var _1HI=_1HH.a,_1HJ=E(_1HH.b);if(!_1HJ._){return new F(function(){return _OA(_1HI,_1HF);});}else{if(!B(_1c5(_1Ge,B(_1Hn(_1HI)),B(_1Hn(_1HJ.a))))){var _1HK=B(_1Hp(_1HE,_1HJ)),_1HL=_1HK.a,_1HM=E(_1HK.c);if(!_1HM._){var _1HN=_1HE<<1,_1HO=B(_Pe(_1HI,_1HF,_1HL));_1HE=_1HN;_1HF=_1HO;_1HG=_1HK.b;continue;}else{return new F(function(){return _1Hi(B(_Pe(_1HI,_1HF,_1HL)),_1HM);});}}else{return new F(function(){return _1Hi(_1HF,_1HH);});}}}}},_1HP=function(_1HQ){var _1HR=E(_1HQ);if(!_1HR._){return new T0(1);}else{var _1HS=_1HR.a,_1HT=E(_1HR.b);if(!_1HT._){return new T4(0,1,E(_1HS),E(_Nd),E(_Nd));}else{if(!B(_1c5(_1Ge,B(_1Hn(_1HS)),B(_1Hn(_1HT.a))))){return new F(function(){return _1HD(1,new T4(0,1,E(_1HS),E(_Nd),E(_Nd)),_1HT);});}else{return new F(function(){return _1Hi(new T4(0,1,E(_1HS),E(_Nd),E(_Nd)),_1HT);});}}}},_1HU=function(_1HV,_1HW){while(1){var _1HX=E(_1HW);if(!_1HX._){return E(_1HV);}else{var _1HY=_1HX.a,_1HZ=E(_1HV);if(!_1HZ._){var _1I0=E(_1HY);if(!_1I0._){var _1I1=B(_1jZ(_1Ge,_1iN,_1iN,_1HZ.a,_1HZ.b,_1HZ.c,_1HZ.d,_1I0.a,_1I0.b,_1I0.c,_1I0.d));}else{var _1I1=E(_1HZ);}var _1I2=_1I1;}else{var _1I2=E(_1HY);}_1HV=_1I2;_1HW=_1HX.b;continue;}}},_1I3=function(_1I4,_1I5){var _1I6=E(_1I4),_1I7=E(_1I5);if(!_1I7._){var _1I8=_1I7.b,_1I9=_1I7.c,_1Ia=_1I7.d;switch(B(_1GE(_1I6,_1I8))){case 0:return new F(function(){return _Ni(_1I8,B(_1I3(_1I6,_1I9)),_1Ia);});break;case 1:return new T4(0,_1I7.a,E(_1I6),E(_1I9),E(_1Ia));default:return new F(function(){return _NU(_1I8,_1I9,B(_1I3(_1I6,_1Ia)));});}}else{return new T4(0,1,E(_1I6),E(_Nd),E(_Nd));}},_1Ib=function(_1Ic,_1Id){while(1){var _1Ie=E(_1Id);if(!_1Ie._){return E(_1Ic);}else{var _1If=B(_1I3(_1Ie.a,_1Ic));_1Ic=_1If;_1Id=_1Ie.b;continue;}}},_1Ig=function(_1Ih,_1Ii){var _1Ij=E(_1Ii);if(!_1Ij._){return new T3(0,_Nd,_4,_4);}else{var _1Ik=_1Ij.a,_1Il=E(_1Ih);if(_1Il==1){var _1Im=E(_1Ij.b);return (_1Im._==0)?new T3(0,new T(function(){return new T4(0,1,E(_1Ik),E(_Nd),E(_Nd));}),_4,_4):(!B(_1Gw(_1Ik,_1Im.a)))?new T3(0,new T(function(){return new T4(0,1,E(_1Ik),E(_Nd),E(_Nd));}),_1Im,_4):new T3(0,new T(function(){return new T4(0,1,E(_1Ik),E(_Nd),E(_Nd));}),_4,_1Im);}else{var _1In=B(_1Ig(_1Il>>1,_1Ij)),_1Io=_1In.a,_1Ip=_1In.c,_1Iq=E(_1In.b);if(!_1Iq._){return new T3(0,_1Io,_4,_1Ip);}else{var _1Ir=_1Iq.a,_1Is=E(_1Iq.b);if(!_1Is._){return new T3(0,new T(function(){return B(_OA(_1Ir,_1Io));}),_4,_1Ip);}else{if(!B(_1Gw(_1Ir,_1Is.a))){var _1It=B(_1Ig(_1Il>>1,_1Is));return new T3(0,new T(function(){return B(_Pe(_1Ir,_1Io,_1It.a));}),_1It.b,_1It.c);}else{return new T3(0,_1Io,_4,_1Iq);}}}}}},_1Iu=function(_1Iv,_1Iw,_1Ix){while(1){var _1Iy=E(_1Ix);if(!_1Iy._){return E(_1Iw);}else{var _1Iz=_1Iy.a,_1IA=E(_1Iy.b);if(!_1IA._){return new F(function(){return _OA(_1Iz,_1Iw);});}else{if(!B(_1Gw(_1Iz,_1IA.a))){var _1IB=B(_1Ig(_1Iv,_1IA)),_1IC=_1IB.a,_1ID=E(_1IB.c);if(!_1ID._){var _1IE=_1Iv<<1,_1IF=B(_Pe(_1Iz,_1Iw,_1IC));_1Iv=_1IE;_1Iw=_1IF;_1Ix=_1IB.b;continue;}else{return new F(function(){return _1Ib(B(_Pe(_1Iz,_1Iw,_1IC)),_1ID);});}}else{return new F(function(){return _1Ib(_1Iw,_1Iy);});}}}}},_1IG=function(_1IH){var _1II=E(_1IH);if(!_1II._){return new T0(1);}else{var _1IJ=_1II.a,_1IK=E(_1II.b);if(!_1IK._){return new T4(0,1,E(_1IJ),E(_Nd),E(_Nd));}else{if(!B(_1Gw(_1IJ,_1IK.a))){return new F(function(){return _1Iu(1,new T4(0,1,E(_1IJ),E(_Nd),E(_Nd)),_1IK);});}else{return new F(function(){return _1Ib(new T4(0,1,E(_1IJ),E(_Nd),E(_Nd)),_1IK);});}}}},_1IL=function(_1IM){return new T1(1,_1IM);},_1IN=function(_1IO,_1IP){var _1IQ=E(_1IP);if(!_1IQ._){return new T2(0,_4,_4);}else{var _1IR=_1IQ.a,_1IS=_1IQ.b,_1IT=E(_1IO);if(_1IT==1){return new T2(0,new T2(1,_1IR,_4),_1IS);}else{var _1IU=new T(function(){var _1IV=B(_1IN(_1IT-1|0,_1IS));return new T2(0,_1IV.a,_1IV.b);});return new T2(0,new T2(1,_1IR,new T(function(){return E(E(_1IU).a);})),new T(function(){return E(E(_1IU).b);}));}}},_1IW=new T(function(){return B(unCStr("Irrefutable pattern failed for pattern"));}),_1IX=function(_1IY){return new F(function(){return _6Q(new T1(0,new T(function(){return B(_74(_1IY,_1IW));})),_6y);});},_1IZ=new T(function(){return B(_1IX("Muste/Tree/Internal.hs:217:9-39|(pre, _ : post)"));}),_1J0=function(_1J1,_1J2,_1J3){if(0>_1J2){return E(_1J1);}else{if(_1J2>=B(_vm(_1J1,0))){return E(_1J1);}else{if(_1J2>0){var _1J4=B(_1IN(_1J2,_1J1)),_1J5=E(_1J4.b);if(!_1J5._){return E(_1IZ);}else{return new F(function(){return _0(_1J4.a,new T2(1,_1J3,_1J5.b));});}}else{var _1J6=E(_1J1);if(!_1J6._){return E(_1IZ);}else{return new F(function(){return _0(_4,new T2(1,_1J3,_1J6.b));});}}}}},_1J7=function(_1J8,_1J9,_1Ja){var _1Jb=E(_1J8);if(!_1Jb._){var _1Jc=_1Jb.c,_1Jd=E(_1J9);if(!_1Jd._){return E(_1Ja);}else{var _1Je=E(_1Jd.a);if(_1Je<0){return E(_1Jb);}else{var _1Jf=B(_vm(_1Jc,0));if(_1Je>=_1Jf){return E(_1Jb);}else{var _1Jg=new T(function(){return B(_1J0(_1Jc,_1Je,new T(function(){var _1Jh=E(_1Jc);if(!_1Jh._){return E(_1Fx);}else{if(_1Je>=0){if(_1Je<_1Jf){return B(_1J7(B(_1Fb(_1Jh,_1Je)),_1Jd.b,_1Ja));}else{return E(_1Fx);}}else{return E(_1Fx);}}})));});return new T3(0,_1Jb.a,_1Jb.b,_1Jg);}}}}else{return (E(_1J9)._==0)?E(_1Ja):E(_1Jb);}},_1Ji=function(_1Jj,_1Jk,_1Jl,_1Jm){while(1){var _1Jn=B((function(_1Jo,_1Jp,_1Jq,_1Jr){var _1Js=E(_1Jq);if(!_1Js._){var _1Jt=E(_1Jr);if(!_1Jt._){return E(_1Jo);}else{var _1Ju=B(_1J7(_1Jo,_1Jt.a,new T3(0,_1Jp,_1Js,new T(function(){return B(_G(_1IL,_1Js.b));})))),_1Jv=_1Jp;_1Jj=_1Ju;_1Jk=_1Jv;_1Jl=_1Js;_1Jm=_1Jt.b;return __continue;}}else{return E(_1Jo);}})(_1Jj,_1Jk,_1Jl,_1Jm));if(_1Jn!=__continue){return _1Jn;}}},_1Jw=function(_1Jx,_1Jy,_1Jz){var _1JA=E(_1Jy);return new F(function(){return _1Ji(_1Jx,_1JA.a,_1JA.b,_1Jz);});},_1JB=new T2(1,_4,_4),_1JC=function(_1JD){var _1JE=E(_1JD);if(!_1JE._){return E(_1JB);}else{var _1JF=_1JE.b,_1JG=new T(function(){return B(_G(function(_1IM){return new T2(1,_1JE.a,_1IM);},B(_1JC(_1JF))));},1);return new F(function(){return _0(B(_1JC(_1JF)),_1JG);});}},_1JH=new T(function(){return B(_1zy(95));}),_1JI=new T2(1,_1JH,_4),_1JJ=new T(function(){var _1JK=B(_1ym(_1JI));return new T3(0,_1JK.a,_1JK.b,_1JK.c);}),_1JL=function(_1JM,_1JN,_1JO){var _1JP=new T(function(){return E(_1JN)-1|0;}),_1JQ=function(_1JR){var _1JS=E(_1JR);if(!_1JS._){return __Z;}else{var _1JT=_1JS.b,_1JU=E(_1JS.a),_1JV=_1JU.a,_1JW=function(_1JX,_1JY,_1JZ){var _1K0=E(_1JU.b);if(!B(_13e(_1JX,_1JY,_1JZ,_1K0.a,_1K0.b,_1K0.c))){return new F(function(){return _1JQ(_1JT);});}else{if(B(_vm(_1JV,0))>E(_1JP)){return new F(function(){return _1JQ(_1JT);});}else{return new T2(1,_1JV,new T(function(){return B(_1JQ(_1JT));}));}}},_1K1=E(E(_1JO).b);if(!_1K1._){var _1K2=E(_1K1.a);return new F(function(){return _1JW(_1K2.a,_1K2.b,_1K2.c);});}else{var _1K3=E(_1JJ);return new F(function(){return _1JW(_1K3.a,_1K3.b,_1K3.c);});}}};return new F(function(){return _1IG(B(_G(function(_1K4){return new F(function(){return _1Jw(_1JM,_1JO,_1K4);});},B(_1JC(B(_1JQ(B(_1H0(_1JM,_4)))))))));});},_1K5=function(_1K6,_1K7){while(1){var _1K8=E(_1K7);if(!_1K8._){return E(_1K6);}else{var _1K9=_1K8.a,_1Ka=E(_1K6);if(!_1Ka._){var _1Kb=E(_1K9);if(!_1Kb._){var _1Kc=B(_1jZ(_1FZ,_1iN,_1iN,_1Ka.a,_1Ka.b,_1Ka.c,_1Ka.d,_1Kb.a,_1Kb.b,_1Kb.c,_1Kb.d));}else{var _1Kc=E(_1Ka);}var _1Kd=_1Kc;}else{var _1Kd=E(_1K9);}_1K6=_1Kd;_1K7=_1K8.b;continue;}}},_1Ke=function(_1Kf){var _1Kg=E(_1Kf);if(!_1Kg._){return new F(function(){return _1K5(_Nd,B(_G(_1Ke,_1Kg.c)));});}else{return new F(function(){return _Ou(_1Kg.a);});}},_1Kh=function(_1Ki,_1Kj,_1Kk){var _1Kl=E(_1Kk);if(!_1Kl._){var _1Km=_1Kl.c,_1Kn=_1Kl.d,_1Ko=E(_1Kl.b),_1Kp=E(_1Ki),_1Kq=E(_1Ko.a);switch(B(_13l(_1Kp.a,_1Kp.b,_1Kp.c,_1Kq.a,_1Kq.b,_1Kq.c))){case 0:return new F(function(){return _Ni(_1Ko,B(_1Kh(_1Kp,_1Kj,_1Km)),_1Kn);});break;case 1:switch(B(_1G0(_1Kj,_1Ko.b))){case 0:return new F(function(){return _Ni(_1Ko,B(_1Kh(_1Kp,_1Kj,_1Km)),_1Kn);});break;case 1:return new T4(0,_1Kl.a,E(new T2(0,_1Kp,_1Kj)),E(_1Km),E(_1Kn));default:return new F(function(){return _NU(_1Ko,_1Km,B(_1Kh(_1Kp,_1Kj,_1Kn)));});}break;default:return new F(function(){return _NU(_1Ko,_1Km,B(_1Kh(_1Kp,_1Kj,_1Kn)));});}}else{return new T4(0,1,E(new T2(0,_1Ki,_1Kj)),E(_Nd),E(_Nd));}},_1Kr=function(_1Ks,_1Kt){while(1){var _1Ku=E(_1Kt);if(!_1Ku._){return E(_1Ks);}else{var _1Kv=E(_1Ku.a),_1Kw=B(_1Kh(_1Kv.a,_1Kv.b,_1Ks));_1Ks=_1Kw;_1Kt=_1Ku.b;continue;}}},_1Kx=function(_1Ky,_1Kz){var _1KA=E(_1Kz);if(!_1KA._){return new T3(0,_Nd,_4,_4);}else{var _1KB=_1KA.a,_1KC=E(_1Ky);if(_1KC==1){var _1KD=E(_1KA.b);if(!_1KD._){return new T3(0,new T(function(){return new T4(0,1,E(_1KB),E(_Nd),E(_Nd));}),_4,_4);}else{var _1KE=E(_1KB),_1KF=E(_1KD.a),_1KG=_1KF.b,_1KH=E(_1KE.a),_1KI=E(_1KF.a);switch(B(_13l(_1KH.a,_1KH.b,_1KH.c,_1KI.a,_1KI.b,_1KI.c))){case 0:return new T3(0,new T4(0,1,E(_1KE),E(_Nd),E(_Nd)),_1KD,_4);case 1:var _1KJ=E(_1KE.b);if(!_1KJ._){var _1KK=E(_1KG);if(!_1KK._){var _1KL=E(_1KJ.a),_1KM=E(_1KK.a);switch(B(_13l(_1KL.a,_1KL.b,_1KL.c,_1KM.a,_1KM.b,_1KM.c))){case 0:return new T3(0,new T4(0,1,E(_1KE),E(_Nd),E(_Nd)),_1KD,_4);case 1:return (B(_1c5(_1FZ,_1KJ.b,_1KK.b))==0)?new T3(0,new T4(0,1,E(_1KE),E(_Nd),E(_Nd)),_1KD,_4):new T3(0,new T4(0,1,E(_1KE),E(_Nd),E(_Nd)),_4,_1KD);default:return new T3(0,new T4(0,1,E(_1KE),E(_Nd),E(_Nd)),_4,_1KD);}}else{return new T3(0,new T4(0,1,E(_1KE),E(_Nd),E(_Nd)),_1KD,_4);}}else{var _1KN=E(_1KG);return new T3(0,new T4(0,1,E(_1KE),E(_Nd),E(_Nd)),_4,_1KD);}break;default:return new T3(0,new T4(0,1,E(_1KE),E(_Nd),E(_Nd)),_4,_1KD);}}}else{var _1KO=B(_1Kx(_1KC>>1,_1KA)),_1KP=_1KO.a,_1KQ=_1KO.c,_1KR=E(_1KO.b);if(!_1KR._){return new T3(0,_1KP,_4,_1KQ);}else{var _1KS=_1KR.a,_1KT=E(_1KR.b);if(!_1KT._){return new T3(0,new T(function(){return B(_OA(_1KS,_1KP));}),_4,_1KQ);}else{var _1KU=E(_1KS),_1KV=E(_1KT.a),_1KW=_1KV.b,_1KX=E(_1KU.a),_1KY=E(_1KV.a);switch(B(_13l(_1KX.a,_1KX.b,_1KX.c,_1KY.a,_1KY.b,_1KY.c))){case 0:var _1KZ=B(_1Kx(_1KC>>1,_1KT));return new T3(0,new T(function(){return B(_Pe(_1KU,_1KP,_1KZ.a));}),_1KZ.b,_1KZ.c);case 1:var _1L0=E(_1KU.b);if(!_1L0._){var _1L1=E(_1KW);if(!_1L1._){var _1L2=E(_1L0.a),_1L3=E(_1L1.a);switch(B(_13l(_1L2.a,_1L2.b,_1L2.c,_1L3.a,_1L3.b,_1L3.c))){case 0:var _1L4=B(_1Kx(_1KC>>1,_1KT));return new T3(0,new T(function(){return B(_Pe(_1KU,_1KP,_1L4.a));}),_1L4.b,_1L4.c);case 1:if(!B(_1c5(_1FZ,_1L0.b,_1L1.b))){var _1L5=B(_1Kx(_1KC>>1,_1KT));return new T3(0,new T(function(){return B(_Pe(_1KU,_1KP,_1L5.a));}),_1L5.b,_1L5.c);}else{return new T3(0,_1KP,_4,_1KR);}break;default:return new T3(0,_1KP,_4,_1KR);}}else{var _1L6=B(_1Kx(_1KC>>1,_1KT));return new T3(0,new T(function(){return B(_Pe(_1KU,_1KP,_1L6.a));}),_1L6.b,_1L6.c);}}else{var _1L7=E(_1KW);return new T3(0,_1KP,_4,_1KR);}break;default:return new T3(0,_1KP,_4,_1KR);}}}}}},_1L8=function(_1L9,_1La,_1Lb){var _1Lc=E(_1Lb);if(!_1Lc._){return E(_1La);}else{var _1Ld=_1Lc.a,_1Le=E(_1Lc.b);if(!_1Le._){return new F(function(){return _OA(_1Ld,_1La);});}else{var _1Lf=E(_1Ld),_1Lg=E(_1Le.a),_1Lh=_1Lg.b,_1Li=E(_1Lf.a),_1Lj=E(_1Lg.a),_1Lk=function(_1Ll){var _1Lm=B(_1Kx(_1L9,_1Le)),_1Ln=_1Lm.a,_1Lo=E(_1Lm.c);if(!_1Lo._){return new F(function(){return _1L8(_1L9<<1,B(_Pe(_1Lf,_1La,_1Ln)),_1Lm.b);});}else{return new F(function(){return _1Kr(B(_Pe(_1Lf,_1La,_1Ln)),_1Lo);});}};switch(B(_13l(_1Li.a,_1Li.b,_1Li.c,_1Lj.a,_1Lj.b,_1Lj.c))){case 0:return new F(function(){return _1Lk(_);});break;case 1:var _1Lp=E(_1Lf.b);if(!_1Lp._){var _1Lq=E(_1Lh);if(!_1Lq._){var _1Lr=E(_1Lp.a),_1Ls=E(_1Lq.a);switch(B(_13l(_1Lr.a,_1Lr.b,_1Lr.c,_1Ls.a,_1Ls.b,_1Ls.c))){case 0:return new F(function(){return _1Lk(_);});break;case 1:if(!B(_1c5(_1FZ,_1Lp.b,_1Lq.b))){return new F(function(){return _1Lk(_);});}else{return new F(function(){return _1Kr(_1La,_1Lc);});}break;default:return new F(function(){return _1Kr(_1La,_1Lc);});}}else{return new F(function(){return _1Lk(_);});}}else{var _1Lt=E(_1Lh);return new F(function(){return _1Kr(_1La,_1Lc);});}break;default:return new F(function(){return _1Kr(_1La,_1Lc);});}}}},_1Lu=function(_1Lv){var _1Lw=E(_1Lv);if(!_1Lw._){return new T0(1);}else{var _1Lx=_1Lw.a,_1Ly=E(_1Lw.b);if(!_1Ly._){return new T4(0,1,E(_1Lx),E(_Nd),E(_Nd));}else{var _1Lz=E(_1Lx),_1LA=E(_1Ly.a),_1LB=_1LA.b,_1LC=E(_1Lz.a),_1LD=E(_1LA.a);switch(B(_13l(_1LC.a,_1LC.b,_1LC.c,_1LD.a,_1LD.b,_1LD.c))){case 0:return new F(function(){return _1L8(1,new T4(0,1,E(_1Lz),E(_Nd),E(_Nd)),_1Ly);});break;case 1:var _1LE=E(_1Lz.b);if(!_1LE._){var _1LF=E(_1LB);if(!_1LF._){var _1LG=E(_1LE.a),_1LH=E(_1LF.a);switch(B(_13l(_1LG.a,_1LG.b,_1LG.c,_1LH.a,_1LH.b,_1LH.c))){case 0:return new F(function(){return _1L8(1,new T4(0,1,E(_1Lz),E(_Nd),E(_Nd)),_1Ly);});break;case 1:if(!B(_1c5(_1FZ,_1LE.b,_1LF.b))){return new F(function(){return _1L8(1,new T4(0,1,E(_1Lz),E(_Nd),E(_Nd)),_1Ly);});}else{return new F(function(){return _1Kr(new T4(0,1,E(_1Lz),E(_Nd),E(_Nd)),_1Ly);});}break;default:return new F(function(){return _1Kr(new T4(0,1,E(_1Lz),E(_Nd),E(_Nd)),_1Ly);});}}else{return new F(function(){return _1L8(1,new T4(0,1,E(_1Lz),E(_Nd),E(_Nd)),_1Ly);});}}else{var _1LI=E(_1LB);return new F(function(){return _1Kr(new T4(0,1,E(_1Lz),E(_Nd),E(_Nd)),_1Ly);});}break;default:return new F(function(){return _1Kr(new T4(0,1,E(_1Lz),E(_Nd),E(_Nd)),_1Ly);});}}}},_1LJ=new T(function(){return B(_7f("Muste/Grammar/Internal.hs:151:43-81|lambda"));}),_1LK=function(_1LL,_1LM){var _1LN=new T(function(){return E(E(_1LL).b);}),_1LO=function(_1LP){var _1LQ=E(_1LP);if(!_1LQ._){return __Z;}else{var _1LR=new T(function(){return B(_1LO(_1LQ.b));}),_1LS=function(_1LT){while(1){var _1LU=B((function(_1LV){var _1LW=E(_1LV);if(!_1LW._){return E(_1LR);}else{var _1LX=_1LW.b,_1LY=E(_1LW.a),_1LZ=E(_1LY.b);if(!_1LZ._){var _1M0=E(_1LZ.a),_1M1=E(_1LQ.a);if(!B(_13e(_1M0.a,_1M0.b,_1M0.c,_1M1.a,_1M1.b,_1M1.c))){_1LT=_1LX;return __continue;}else{return new T2(1,_1LY,new T(function(){return B(_1LS(_1LX));}));}}else{return E(_1LJ);}}})(_1LT));if(_1LU!=__continue){return _1LU;}}};return new F(function(){return _1LS(_1LN);});}};return new F(function(){return _1Lu(B(_1LO(_1LM)));});},_1M2=function(_1M3,_1M4,_1M5){var _1M6=function(_1M7,_1M8){while(1){var _1M9=B((function(_1Ma,_1Mb){var _1Mc=E(_1Mb);if(!_1Mc._){_1M7=new T2(1,new T(function(){return B(_1JL(_1M4,_1M5,_1Mc.b));}),new T(function(){return B(_1M6(_1Ma,_1Mc.d));}));_1M8=_1Mc.c;return __continue;}else{return E(_1Ma);}})(_1M7,_1M8));if(_1M9!=__continue){return _1M9;}}};return new F(function(){return _1HU(_Nd,B(_1nK(_4,B(_1HP(B(_1M6(_4,B(_1LK(_1M3,B(_1nK(_4,B(_1Ke(_1M4)))))))))))));});},_1Md=function(_1Me,_1Mf){while(1){var _1Mg=B((function(_1Mh,_1Mi){var _1Mj=E(_1Mi);if(!_1Mj._){return __Z;}else{var _1Mk=_1Mj.a,_1Ml=_1Mj.b;if(!B(A1(_1Mh,_1Mk))){var _1Mm=_1Mh;_1Me=_1Mm;_1Mf=_1Ml;return __continue;}else{return new T2(1,_1Mk,new T(function(){return B(_1Md(_1Mh,_1Ml));}));}}})(_1Me,_1Mf));if(_1Mg!=__continue){return _1Mg;}}},_1Mn=function(_1Mo,_1Mp,_1Mq){var _1Mr=new T(function(){return E(_1Mq)-1|0;}),_1Ms=function(_1Mt){return B(_vm(E(_1Mt).a,0))<=E(_1Mr);},_1Mu=function(_1Mv,_1Mw){while(1){var _1Mx=B((function(_1My,_1Mz){var _1MA=E(_1Mz);if(!_1MA._){var _1MB=_1MA.b,_1MC=_1MA.d,_1MD=new T(function(){if(!B(_1Md(_1Ms,B(_1H0(_1MB,_4))))._){return B(_1Mu(_1My,_1MC));}else{return new T2(1,_1MB,new T(function(){return B(_1Mu(_1My,_1MC));}));}},1);_1Mv=_1MD;_1Mw=_1MA.c;return __continue;}else{return E(_1My);}})(_1Mv,_1Mw));if(_1Mx!=__continue){return _1Mx;}}},_1ME=function(_1MF){var _1MG=E(_1MF);if(!_1MG._){return new T0(1);}else{var _1MH=_1MG.a,_1MI=B(_1M2(_1Mo,_1MH,_1Mq)),_1MJ=B(_1ME(B(_0(_1MG.b,new T(function(){return B(_1Mu(_4,B(_1GS(_1MH,_1MI))));},1))))),_1MK=function(_1ML,_1MM,_1MN,_1MO){return new F(function(){return _1jZ(_1Ge,_1iN,_1iN,1,_1MH,_Nd,_Nd,_1ML,_1MM,_1MN,_1MO);});},_1MP=E(_1MI);if(!_1MP._){var _1MQ=_1MP.a,_1MR=_1MP.b,_1MS=_1MP.c,_1MT=_1MP.d,_1MU=E(_1MJ);if(!_1MU._){var _1MV=B(_1jZ(_1Ge,_1iN,_1iN,_1MQ,_1MR,_1MS,_1MT,_1MU.a,_1MU.b,_1MU.c,_1MU.d));if(!_1MV._){return new F(function(){return _1MK(_1MV.a,_1MV.b,_1MV.c,_1MV.d);});}else{return new T4(0,1,E(_1MH),E(_Nd),E(_Nd));}}else{return new F(function(){return _1MK(_1MQ,_1MR,_1MS,_1MT);});}}else{var _1MW=E(_1MJ);if(!_1MW._){return new F(function(){return _1MK(_1MW.a,_1MW.b,_1MW.c,_1MW.d);});}else{return new T4(0,1,E(_1MH),E(_Nd),E(_Nd));}}}};return new F(function(){return _1ME(new T2(1,new T1(1,_1Mp),_4));});},_1MX=function(_1MY,_1MZ,_1N0,_1N1){return new F(function(){return _1Mn(_1MY,new T(function(){var _1N2=B(_1Fk(_1MZ,_1N0));if(!_1N2._){return E(_1Fx);}else{var _1N3=E(_1N2.a);if(!_1N3._){var _1N4=E(_1N3.b);if(!_1N4._){return E(_1N4.a);}else{return E(_1JJ);}}else{return E(_1N3.a);}}}),_1N1);});},_1N5=function(_1N6,_1N7,_1N8,_1N9){while(1){var _1Na=E(_1N7);if(!_1Na._){return E(_1N9);}else{var _1Nb=_1Na.a,_1Nc=E(_1N8);if(!_1Nc._){return E(_1N9);}else{if(!B(A3(_qe,_1N6,_1Nb,_1Nc.a))){return E(_1N9);}else{var _1Nd=new T2(1,_1Nb,_1N9);_1N7=_1Na.b;_1N8=_1Nc.b;_1N9=_1Nd;continue;}}}}},_1Ne=function(_1Nf,_1Ng){while(1){var _1Nh=E(_1Nf);if(!_1Nh._){return E(_1Ng);}else{var _1Ni=new T2(1,_1Nh.a,_1Ng);_1Nf=_1Nh.b;_1Ng=_1Ni;continue;}}},_1Nj=function(_1Nk,_1Nl,_1Nm,_1Nn,_1No){while(1){var _1Np=B((function(_1Nq,_1Nr,_1Ns,_1Nt,_1Nu){var _1Nv=E(_1Nr);if(!_1Nv._){return new T2(0,_1Nt,_1Nu);}else{var _1Nw=_1Nv.a,_1Nx=_1Nv.b,_1Ny=E(_1Ns);if(!_1Ny._){return new T2(0,_1Nt,_1Nu);}else{var _1Nz=_1Ny.b;if(!B(A3(_qe,_1Nq,_1Nw,_1Ny.a))){var _1NA=new T(function(){return B(_1N5(_1Nq,B(_1Ne(_1Nv,_4)),new T(function(){return B(_1Ne(_1Ny,_4));},1),_4));}),_1NB=_1Nq,_1NC=_1Nt;_1Nk=_1NB;_1Nl=_1Nx;_1Nm=_1Nz;_1Nn=_1NC;_1No=_1NA;return __continue;}else{var _1NB=_1Nq,_1ND=_1Nu;_1Nk=_1NB;_1Nl=_1Nx;_1Nm=_1Nz;_1Nn=new T(function(){return B(_0(_1Nt,new T2(1,_1Nw,_4)));});_1No=_1ND;return __continue;}}}})(_1Nk,_1Nl,_1Nm,_1Nn,_1No));if(_1Np!=__continue){return _1Np;}}},_1NE=function(_1NF,_1NG){while(1){var _1NH=E(_1NF);if(!_1NH._){return (E(_1NG)._==0)?true:false;}else{var _1NI=E(_1NG);if(!_1NI._){return false;}else{if(E(_1NH.a)!=E(_1NI.a)){return false;}else{_1NF=_1NH.b;_1NG=_1NI.b;continue;}}}}},_1NJ=function(_1NK,_1NL,_1NM,_1NN){return (!B(_1NE(_1NK,_1NM)))?true:(!B(_sH(_1NL,_1NN)))?true:false;},_1NO=function(_1NP,_1NQ){var _1NR=E(_1NP),_1NS=E(_1NQ);return new F(function(){return _1NJ(_1NR.a,_1NR.b,_1NS.a,_1NS.b);});},_1NT=function(_1NU,_1NV,_1NW,_1NX){if(!B(_1NE(_1NU,_1NW))){return false;}else{return new F(function(){return _sH(_1NV,_1NX);});}},_1NY=function(_1NZ,_1O0){var _1O1=E(_1NZ),_1O2=E(_1O0);return new F(function(){return _1NT(_1O1.a,_1O1.b,_1O2.a,_1O2.b);});},_1O3=new T2(0,_1NY,_1NO),_1O4=function(_1O5,_1O6){while(1){var _1O7=E(_1O5);if(!_1O7._){return (E(_1O6)._==0)?1:0;}else{var _1O8=E(_1O6);if(!_1O8._){return 2;}else{var _1O9=E(_1O7.a),_1Oa=E(_1O8.a);if(_1O9>=_1Oa){if(_1O9!=_1Oa){return 2;}else{_1O5=_1O7.b;_1O6=_1O8.b;continue;}}else{return 0;}}}}},_1Ob=function(_1Oc,_1Od,_1Oe,_1Of){switch(B(_1O4(_1Oc,_1Oe))){case 0:return false;case 1:return new F(function(){return _12V(_1Od,_1Of);});break;default:return true;}},_1Og=function(_1Oh,_1Oi){var _1Oj=E(_1Oh),_1Ok=E(_1Oi);return new F(function(){return _1Ob(_1Oj.a,_1Oj.b,_1Ok.a,_1Ok.b);});},_1Ol=function(_1Om,_1On){var _1Oo=E(_1Om),_1Op=E(_1On);switch(B(_1O4(_1Oo.a,_1Op.a))){case 0:return E(_1Op);case 1:return (B(_12F(_1Oo.b,_1Op.b))==2)?E(_1Oo):E(_1Op);default:return E(_1Oo);}},_1Oq=function(_1Or,_1Os){var _1Ot=E(_1Or),_1Ou=E(_1Os);switch(B(_1O4(_1Ot.a,_1Ou.a))){case 0:return E(_1Ot);case 1:return (B(_12F(_1Ot.b,_1Ou.b))==2)?E(_1Ou):E(_1Ot);default:return E(_1Ou);}},_1Ov=function(_1Ow,_1Ox,_1Oy,_1Oz){switch(B(_1O4(_1Ow,_1Oy))){case 0:return 0;case 1:return new F(function(){return _12F(_1Ox,_1Oz);});break;default:return 2;}},_1OA=function(_1OB,_1OC){var _1OD=E(_1OB),_1OE=E(_1OC);return new F(function(){return _1Ov(_1OD.a,_1OD.b,_1OE.a,_1OE.b);});},_1OF=function(_1OG,_1OH,_1OI,_1OJ){switch(B(_1O4(_1OG,_1OI))){case 0:return true;case 1:return new F(function(){return _12M(_1OH,_1OJ);});break;default:return false;}},_1OK=function(_1OL,_1OM){var _1ON=E(_1OL),_1OO=E(_1OM);return new F(function(){return _1OF(_1ON.a,_1ON.b,_1OO.a,_1OO.b);});},_1OP=function(_1OQ,_1OR,_1OS,_1OT){switch(B(_1O4(_1OQ,_1OS))){case 0:return true;case 1:return new F(function(){return _12P(_1OR,_1OT);});break;default:return false;}},_1OU=function(_1OV,_1OW){var _1OX=E(_1OV),_1OY=E(_1OW);return new F(function(){return _1OP(_1OX.a,_1OX.b,_1OY.a,_1OY.b);});},_1OZ=function(_1P0,_1P1,_1P2,_1P3){switch(B(_1O4(_1P0,_1P2))){case 0:return false;case 1:return new F(function(){return _12S(_1P1,_1P3);});break;default:return true;}},_1P4=function(_1P5,_1P6){var _1P7=E(_1P5),_1P8=E(_1P6);return new F(function(){return _1OZ(_1P7.a,_1P7.b,_1P8.a,_1P8.b);});},_1P9={_:0,a:_1O3,b:_1OA,c:_1OK,d:_1OU,e:_1P4,f:_1Og,g:_1Ol,h:_1Oq},_1Pa=function(_1Pb){var _1Pc=E(_1Pb);if(!_1Pc._){return __Z;}else{return new F(function(){return _0(_1Pc.a,new T(function(){return B(_1Pa(_1Pc.b));},1));});}},_1Pd=new T1(1,_4),_1Pe=function(_1Pf){var _1Pg=E(_1Pf);if(!_1Pg._){return E(_1Pd);}else{var _1Ph=E(_1Pg.a);if(!_1Ph._){return __Z;}else{var _1Pi=B(_1Pe(_1Pg.b));return (_1Pi._==0)?__Z:new T1(1,new T2(1,_1Ph.a,_1Pi.a));}}},_1Pj=function(_1Pk,_1Pl){var _1Pm=B(_1Pe(_1Pl));return (_1Pm._==0)?new T2(0,_4l,_4l):new T2(0,_1Pk,new T1(1,new T(function(){return B(_1Pa(_1Pm.a));})));},_1Pn=function(_1Po,_1Pp){var _1Pq=E(_1Po);if(!_1Pq._){return new T2(0,_1Pp,_4);}else{var _1Pr=new T(function(){var _1Ps=B(_1Pn(_1Pq.b,_1Pp));return new T2(0,_1Ps.a,_1Ps.b);}),_1Pt=new T(function(){var _1Pu=B(_1Pv(new T(function(){return E(E(_1Pr).a);}),_1Pq.a));return new T2(0,_1Pu.a,_1Pu.b);});return new T2(0,new T(function(){return E(E(_1Pt).a);}),new T2(1,new T(function(){return E(E(_1Pt).b);}),new T(function(){return E(E(_1Pr).b);})));}},_1Pw=function(_1Px,_1Py){var _1Pz=E(_1Px);if(!_1Pz._){return new T2(0,_1Py,_4);}else{var _1PA=new T(function(){var _1PB=B(_1Pw(_1Pz.b,_1Py));return new T2(0,_1PB.a,_1PB.b);}),_1PC=new T(function(){var _1PD=B(_1Pv(new T(function(){return E(E(_1PA).a);}),_1Pz.a));return new T2(0,_1PD.a,_1PD.b);});return new T2(0,new T(function(){return E(E(_1PC).a);}),new T2(1,new T(function(){return E(E(_1PC).b);}),new T(function(){return E(E(_1PA).b);})));}},_1PE=function(_1PF,_1PG){var _1PH=E(_1PF);if(!_1PH._){return new T2(0,_1PG,_4);}else{var _1PI=new T(function(){var _1PJ=B(_1PE(_1PH.b,_1PG));return new T2(0,_1PJ.a,_1PJ.b);}),_1PK=new T(function(){var _1PL=B(_1Pv(new T(function(){return E(E(_1PI).a);}),_1PH.a));return new T2(0,_1PL.a,_1PL.b);});return new T2(0,new T(function(){return E(E(_1PK).a);}),new T2(1,new T(function(){return E(E(_1PK).b);}),new T(function(){return E(E(_1PI).b);})));}},_1PM=function(_1PN,_1PO){var _1PP=E(_1PN);if(!_1PP._){return new T2(0,_1PO,_4);}else{var _1PQ=new T(function(){var _1PR=B(_1PM(_1PP.b,_1PO));return new T2(0,_1PR.a,_1PR.b);}),_1PS=new T(function(){var _1PT=B(_1Pv(new T(function(){return E(E(_1PQ).a);}),_1PP.a));return new T2(0,_1PT.a,_1PT.b);});return new T2(0,new T(function(){return E(E(_1PS).a);}),new T2(1,new T(function(){return E(E(_1PS).b);}),new T(function(){return E(E(_1PQ).b);})));}},_1PU=function(_1PV){var _1PW=E(_1PV);if(!_1PW._){return __Z;}else{return new F(function(){return _0(_1PW.a,new T(function(){return B(_1PU(_1PW.b));},1));});}},_1PX=function(_1PY){var _1PZ=E(_1PY);if(!_1PZ._){return E(_1Pd);}else{var _1Q0=E(_1PZ.a);if(!_1Q0._){return __Z;}else{var _1Q1=B(_1PX(_1PZ.b));return (_1Q1._==0)?__Z:new T1(1,new T2(1,_1Q0.a,_1Q1.a));}}},_1Q2=function(_1Q3,_1Q4,_1Q5){while(1){var _1Q6=E(_1Q4);if(!_1Q6._){return true;}else{var _1Q7=E(_1Q5);if(!_1Q7._){return false;}else{if(!B(A3(_qe,_1Q3,_1Q6.a,_1Q7.a))){return false;}else{_1Q4=_1Q6.b;_1Q5=_1Q7.b;continue;}}}}},_1Q8=new T1(1,_4),_1Q9=new T(function(){return B(_7f("pgf/PGF/Macros.hs:(186,5)-(204,44)|function untokn"));}),_1Pv=function(_1Qa,_1Qb){var _1Qc=E(_1Qb);switch(_1Qc._){case 0:var _1Qd=B(_1PM(_1Qc.f,_1Qa)),_1Qe=B(_1PX(_1Qd.b));return (_1Qe._==0)?new T2(0,_4l,_4l):new T2(0,_1Qd.a,new T1(1,new T2(1,new T6(1,_1Qc.a,_1Qc.b,_1Qc.c,_1Qc.d,_1Qc.e,new T(function(){return B(_1PU(_1Qe.a));})),_4)));case 1:var _1Qf=E(_1Qc.a);return (_1Qf._==0)?new T2(0,_1Qa,_1Q8):new T2(0,new T1(1,_1Qf),new T1(1,new T2(1,new T1(0,_1Qf),_4)));case 2:return new T2(0,_4l,_4l);case 6:var _1Qg=_1Qc.a,_1Qh=E(_1Qa);if(!_1Qh._){var _1Qi=B(_1PE(_1Qg,_4l));return new F(function(){return _1Pj(_1Qi.a,_1Qi.b);});}else{var _1Qj=function(_1Qk){while(1){var _1Ql=E(_1Qk);if(!_1Ql._){return false;}else{if(!B(_1Q2(_sS,_1Ql.a,_1Qh.a))){_1Qk=_1Ql.b;continue;}else{return true;}}}},_1Qm=function(_1Qn){while(1){var _1Qo=B((function(_1Qp){var _1Qq=E(_1Qp);if(!_1Qq._){return __Z;}else{var _1Qr=_1Qq.b,_1Qs=E(_1Qq.a);if(!B(_1Qj(_1Qs.b))){_1Qn=_1Qr;return __continue;}else{return new T2(1,_1Qs.a,new T(function(){return B(_1Qm(_1Qr));}));}}})(_1Qn));if(_1Qo!=__continue){return _1Qo;}}},_1Qt=B(_1Qm(_1Qc.b));if(!_1Qt._){var _1Qu=B(_1Pw(_1Qg,_1Qh));return new F(function(){return _1Pj(_1Qu.a,_1Qu.b);});}else{var _1Qv=B(_1Pn(_1Qt.a,_1Qh));return new F(function(){return _1Pj(_1Qv.a,_1Qv.b);});}}break;default:return E(_1Q9);}},_1Qw=function(_1Qx,_1Qy){var _1Qz=E(_1Qx);if(!_1Qz._){return new T2(0,_1Qy,_4);}else{var _1QA=new T(function(){var _1QB=B(_1Qw(_1Qz.b,_1Qy));return new T2(0,_1QB.a,_1QB.b);}),_1QC=new T(function(){var _1QD=B(_1Pv(new T(function(){return E(E(_1QA).a);}),_1Qz.a));return new T2(0,_1QD.a,_1QD.b);});return new T2(0,new T(function(){return E(E(_1QC).a);}),new T2(1,new T(function(){return E(E(_1QC).b);}),new T(function(){return E(E(_1QA).b);})));}},_1QE=function(_1QF){var _1QG=E(_1QF);if(_1QG==95){return true;}else{var _1QH=function(_1QI){if(_1QG<65){if(_1QG<192){return false;}else{if(_1QG>255){return false;}else{switch(E(_1QG)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1QG>90){if(_1QG<192){return false;}else{if(_1QG>255){return false;}else{switch(E(_1QG)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1QG<97){return new F(function(){return _1QH(_);});}else{if(_1QG>122){return new F(function(){return _1QH(_);});}else{return true;}}}},_1QJ=new T(function(){return B(unCStr("UTF8.decodeUTF8: bad data"));}),_1QK=function(_1QL){return new F(function(){return err(_1QJ);});},_1QM=new T(function(){return B(_1QK(_));}),_1QN=function(_1QO){var _1QP=E(_1QO);if(!_1QP._){return __Z;}else{var _1QQ=_1QP.b,_1QR=E(_1QP.a);if(_1QR>=128){var _1QS=E(_1QQ);if(!_1QS._){return E(_1QM);}else{var _1QT=_1QS.a,_1QU=_1QS.b,_1QV=function(_1QW){var _1QX=E(_1QU);if(!_1QX._){return E(_1QM);}else{if(224>_1QR){return E(_1QM);}else{if(_1QR>239){return E(_1QM);}else{var _1QY=E(_1QT);if(128>_1QY){return E(_1QM);}else{if(_1QY>191){return E(_1QM);}else{var _1QZ=E(_1QX.a);return (128>_1QZ)?E(_1QM):(_1QZ>191)?E(_1QM):new T2(1,new T(function(){var _1R0=((imul(B(_oy(_1QR,16)),4096)|0)+(imul(B(_oy(_1QY,64)),64)|0)|0)+B(_oy(_1QZ,64))|0;if(_1R0>>>0>1114111){return B(_gc(_1R0));}else{return _1R0;}}),new T(function(){return B(_1QN(_1QX.b));}));}}}}}};if(192>_1QR){return new F(function(){return _1QV(_);});}else{if(_1QR>223){return new F(function(){return _1QV(_);});}else{var _1R1=E(_1QT);if(128>_1R1){return new F(function(){return _1QV(_);});}else{if(_1R1>191){return new F(function(){return _1QV(_);});}else{return new T2(1,new T(function(){var _1R2=(imul(B(_oy(_1QR,32)),64)|0)+B(_oy(_1R1,64))|0;if(_1R2>>>0>1114111){return B(_gc(_1R2));}else{return _1R2;}}),new T(function(){return B(_1QN(_1QU));}));}}}}}}else{return new T2(1,_1QR,new T(function(){return B(_1QN(_1QQ));}));}}},_1R3=function(_1R4){var _1R5=E(_1R4);switch(_1R5){case 39:return true;case 95:return true;default:var _1R6=function(_1R7){var _1R8=function(_1R9){if(_1R5<65){if(_1R5<192){return false;}else{if(_1R5>255){return false;}else{switch(E(_1R5)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1R5>90){if(_1R5<192){return false;}else{if(_1R5>255){return false;}else{switch(E(_1R5)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1R5<97){return new F(function(){return _1R8(_);});}else{if(_1R5>122){return new F(function(){return _1R8(_);});}else{return true;}}};if(_1R5<48){return new F(function(){return _1R6(_);});}else{if(_1R5>57){return new F(function(){return _1R6(_);});}else{return true;}}}},_1Ra=function(_1Rb){while(1){var _1Rc=E(_1Rb);if(!_1Rc._){return true;}else{if(!B(_1R3(E(_1Rc.a)))){return false;}else{_1Rb=_1Rc.b;continue;}}}},_1Rd=new T(function(){return B(unCStr("\\\\"));}),_1Re=new T(function(){return B(unCStr("\\\'"));}),_1Rf=new T(function(){return B(unCStr("\'"));}),_1Rg=function(_1Rh){var _1Ri=E(_1Rh);if(!_1Ri._){return E(_1Rf);}else{var _1Rj=_1Ri.b,_1Rk=E(_1Ri.a);switch(E(_1Rk)){case 39:return new F(function(){return _0(_1Re,new T(function(){return B(_1Rg(_1Rj));},1));});break;case 92:return new F(function(){return _0(_1Rd,new T(function(){return B(_1Rg(_1Rj));},1));});break;default:return new T2(1,_1Rk,new T(function(){return B(_1Rg(_1Rj));}));}}},_1Rl=function(_1Rm){var _1Rn=E(_1Rm);return (_1Rn._==0)?__Z:new T2(1,new T(function(){return B(_135(_1Rn.a));}),new T(function(){return B(_1Rl(_1Rn.b));}));},_1Ro=function(_1Rp,_1Rq,_1Rr){var _1Rs=B(_1QN(B(_1Rl(new T(function(){return B(_Jb(_1Rp,_1Rq,_1Rr));})))));if(!_1Rs._){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1Rg(_4));}));});}else{if(!B(_1QE(E(_1Rs.a)))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1Rg(_1Rs));}));});}else{if(!B(_1Ra(_1Rs.b))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1Rg(_1Rs));}));});}else{return E(_1Rs);}}}},_1Rt=new T(function(){return B(unCStr(")"));}),_1Ru=function(_1Rv,_1Rw){var _1Rx=new T(function(){var _1Ry=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_co(0,_1Rw,_4)),_1Rt));})));},1);return B(_0(B(_co(0,_1Rv,_4)),_1Ry));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1Rx)));});},_1Rz=new T(function(){return B(unCStr("Int"));}),_1RA=function(_1RB,_1RC,_1RD){return new F(function(){return _fj(_ew,new T2(0,_1RC,_1RD),_1RB,_1Rz);});},_1RE=new T(function(){return B(unCStr("&|"));}),_1RF=new T1(1,_1RE),_1RG=new T2(1,_1RF,_4),_1RH=new T0(2),_1RI=new T2(1,_1RH,_4),_1RJ=new T(function(){return B(unCStr("&+"));}),_1RK=new T1(1,_1RJ),_1RL=new T2(1,_1RK,_4),_1RM=function(_1RN,_1RO,_1RP){var _1RQ=function(_1RR,_1RS){var _1RT=B(_1Fb(_1RP,_1RR)),_1RU=E(_1RT.a),_1RV=E(E(_1RT.e).b),_1RW=_1RV.c,_1RX=E(_1RV.a),_1RY=E(_1RV.b);if(_1RX>_1RS){return new F(function(){return _1RA(_1RS,_1RX,_1RY);});}else{if(_1RS>_1RY){return new F(function(){return _1RA(_1RS,_1RX,_1RY);});}else{var _1RZ=_1RS-_1RX|0;if(0>_1RZ){return new F(function(){return _1Ru(_1RZ,_1RW);});}else{if(_1RZ>=_1RW){return new F(function(){return _1Ru(_1RZ,_1RW);});}else{var _1S0=E(_1RV.d[_1RZ]);return (_1S0._==0)?__Z:(!B(A1(_1RN,_1RU)))?E(_1S0):new T2(1,new T(function(){return new T6(0,_1RU.a,E(_1RU.b),_1RS,_1RT.c,_1RT.d,_1S0);}),_4);}}}}},_1S1=function(_1S2){var _1S3=E(_1S2);if(!_1S3._){return __Z;}else{var _1S4=E(_1S3.a);return new T2(1,new T2(0,new T(function(){return B(_1S5(_1S4.a));}),_1S4.b),new T(function(){return B(_1S1(_1S3.b));}));}},_1S6=function(_1S7){var _1S8=E(_1S7);if(!_1S8._){return __Z;}else{return new F(function(){return _0(B(_1S9(_1S8.a)),new T(function(){return B(_1S6(_1S8.b));},1));});}},_1S9=function(_1Sa){var _1Sb=E(_1Sa);switch(_1Sb._){case 0:return new F(function(){return _1RQ(_1Sb.a,_1Sb.b);});break;case 1:return new F(function(){return _1RQ(_1Sb.a,_1Sb.b);});break;case 2:return new T2(1,new T1(1,new T(function(){var _1Sc=B(_1Fb(E(B(_1Fb(_1RP,_1Sb.a)).e).a,_1Sb.b));return B(_1Ro(_1Sc.a,_1Sc.b,_1Sc.c));})),_4);case 3:return new T2(1,new T1(1,_1Sb.a),_4);case 4:return new T2(1,new T2(6,new T(function(){return B(_1S6(_1Sb.a));}),new T(function(){return B(_1S1(_1Sb.b));})),_4);case 5:return E(_1RL);case 6:return E(_1RI);case 7:return __Z;case 8:return __Z;case 9:return E(_1RG);default:return E(_1RG);}},_1S5=function(_1Sd){var _1Se=E(_1Sd);if(!_1Se._){return __Z;}else{return new F(function(){return _0(B(_1S9(_1Se.a)),new T(function(){return B(_1S5(_1Se.b));},1));});}},_1Sf=function(_1Sg){var _1Sh=E(_1Sg);if(!_1Sh._){return __Z;}else{return new F(function(){return _0(B(_1S9(_1Sh.a)),new T(function(){return B(_1Sf(_1Sh.b));},1));});}};return new F(function(){return _1Sf(_1RO);});},_1Si=function(_1Sj,_1Sk,_1Sl){return new F(function(){return _fj(_ew,new T2(0,_1Sk,_1Sl),_1Sj,_1Rz);});},_1Sm=new T(function(){return B(unCStr("Negative range size"));}),_1Sn=function(_1So,_1Sp,_1Sq,_1Sr,_1Ss){var _1St=new T(function(){var _1Su=function(_){var _1Sv=E(_1So),_1Sw=E(_1Sv.c),_1Sx=_1Sw.c,_1Sy=E(_1Sw.a),_1Sz=E(_1Sw.b),_1SA=E(_1Sr);if(_1Sy>_1SA){return new F(function(){return _1Si(_1SA,_1Sy,_1Sz);});}else{if(_1SA>_1Sz){return new F(function(){return _1Si(_1SA,_1Sy,_1Sz);});}else{var _1SB=_1SA-_1Sy|0;if(0>_1SB){return new F(function(){return _1Ru(_1SB,_1Sx);});}else{if(_1SB>=_1Sx){return new F(function(){return _1Ru(_1SB,_1Sx);});}else{var _1SC=E(_1Sw.d[_1SB]),_1SD=E(_1SC.b),_1SE=E(_1SC.c),_1SF=function(_1SG){if(_1SG>=0){var _1SH=newArr(_1SG,_VW),_1SI=_1SH,_1SJ=function(_1SK){var _1SL=function(_1SM,_1SN,_){while(1){if(_1SM!=_1SK){var _1SO=E(_1SN);if(!_1SO._){return _5;}else{var _=_1SI[_1SM]=_1SO.a,_1SP=_1SM+1|0;_1SM=_1SP;_1SN=_1SO.b;continue;}}else{return _5;}}},_1SQ=new T(function(){var _1SR=_1SC.d-1|0;if(0<=_1SR){var _1SS=new T(function(){return B(_1RM(_1Sp,_4,_1Ss));}),_1ST=function(_1SU){var _1SV=new T(function(){var _1SW=E(_1Sv.f),_1SX=_1SW.c,_1SY=E(_1SW.a),_1SZ=E(_1SW.b),_1T0=_1SC.e["v"]["i32"][_1SU];if(_1SY>_1T0){return B(_1RA(_1T0,_1SY,_1SZ));}else{if(_1T0>_1SZ){return B(_1RA(_1T0,_1SY,_1SZ));}else{var _1T1=_1T0-_1SY|0;if(0>_1T1){return B(_1Ru(_1T1,_1SX));}else{if(_1T1>=_1SX){return B(_1Ru(_1T1,_1SX));}else{var _1T2=E(_1SW.d[_1T1]),_1T3=_1T2.c-1|0;if(0<=_1T3){var _1T4=function(_1T5){return new T2(1,new T(function(){return E(_1T2.d[_1T5]);}),new T(function(){if(_1T5!=_1T3){return B(_1T4(_1T5+1|0));}else{return __Z;}}));};return B(_1RM(_1Sp,B(_1T4(0)),_1Ss));}else{return E(_1SS);}}}}}});return new T2(1,_1SV,new T(function(){if(_1SU!=_1SR){return B(_1ST(_1SU+1|0));}else{return __Z;}}));};return B(_1ST(0));}else{return __Z;}},1),_1T6=B(_1SL(0,_1SQ,_));return new T4(0,E(_1SD),E(_1SE),_1SG,_1SI);};if(_1SD>_1SE){return new F(function(){return _1SJ(0);});}else{var _1T7=(_1SE-_1SD|0)+1|0;if(_1T7>=0){return new F(function(){return _1SJ(_1T7);});}else{return new F(function(){return err(_1Sm);});}}}else{return E(_VY);}};if(_1SD>_1SE){return new F(function(){return _1SF(0);});}else{return new F(function(){return _1SF((_1SE-_1SD|0)+1|0);});}}}}}};return B(_9d(_1Su));});return new T2(0,_1Sq,_1St);},_1T8=new T(function(){return B(unCStr(")"));}),_1T9=function(_1Ta,_1Tb){var _1Tc=new T(function(){var _1Td=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_0(B(_co(0,_1Tb,_4)),_1T8));})));},1);return B(_0(B(_co(0,_1Ta,_4)),_1Td));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1Tc)));});},_1Te=function(_1Tf){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_1Tf));}))));});},_1Tg=new T(function(){return B(_1Te("ww_sZJc Map CId String"));}),_1Th=new T(function(){return B(_1Te("ww_sZJb Map CId Literal"));}),_1Ti=new T1(1,_4),_1Tj=new T2(1,_1Ti,_4),_1Tk=0,_1Tl=new T(function(){return B(unCStr("Int"));}),_1Tm=function(_1Tn,_1To){return new F(function(){return _fj(_ew,new T2(0,_1Tn,_1To),_1Tk,_1Tl);});},_1Tp=function(_1Tq){return true;},_1Tr=new T(function(){return B(_1Te("ww_sZJl IntMap (IntMap (TrieMap Token IntSet))"));}),_1Ts=new T(function(){return B(_1Te("ww_sZJk Map CId CncCat"));}),_1Tt=new T(function(){return B(_1Te("ww_sZJj Map CId (IntMap (Set Production))"));}),_1Tu=new T(function(){return B(_1Te("ww_sZJi IntMap (Set Production)"));}),_1Tv=new T(function(){return B(_1Te("ww_sZJh IntMap (Set Production)"));}),_1Tw=new T(function(){return B(_1Te("ww_sZJe IntMap [FunId]"));}),_1Tx=function(_1Ty,_1Tz,_1TA,_1TB,_1TC,_1TD,_1TE,_1TF){var _1TG=B(_15n(_1TC,_1Tz));if(!_1TG._){return E(_1Tj);}else{var _1TH=E(_1TG.a);if(!_1TH._){return E(_1Tj);}else{var _1TI=E(B(_1Sn({_:0,a:_1Th,b:_1Tg,c:_1Ty,d:_1Tw,e:_1Tz,f:_1TA,g:_1Tv,h:_1Tu,i:_1Tt,j:_1Ts,k:_1Tr,l:0},_1Tp,_4,_1TH.a,new T2(1,new T5(0,E(_1TB),_1TC,_1TD,_1TE,E(_1TF)),_4))).b),_1TJ=_1TI.c,_1TK=E(_1TI.a),_1TL=E(_1TI.b);if(_1TK>0){return new F(function(){return _1Tm(_1TK,_1TL);});}else{if(0>_1TL){return new F(function(){return _1Tm(_1TK,_1TL);});}else{var _1TM= -_1TK|0;if(0>_1TM){return new F(function(){return _1T9(_1TM,_1TJ);});}else{if(_1TM>=_1TJ){return new F(function(){return _1T9(_1TM,_1TJ);});}else{return E(_1TI.d[_1TM]);}}}}}}},_1TN=new T(function(){return B(unCStr("no lang"));}),_1TO=new T(function(){return B(err(_1TN));}),_1TP=function(_1TQ){return E(E(_1TQ).d);},_1TR=function(_1TS,_1TT,_1TU,_1TV){var _1TW=function(_1TX,_1TY,_1TZ){while(1){var _1U0=E(_1TY),_1U1=E(_1TZ);if(!_1U1._){switch(B(A3(_13P,_1TS,_1U0,_1U1.b))){case 0:_1TY=_1U0;_1TZ=_1U1.d;continue;case 1:return E(_1U1.c);default:_1TY=_1U0;_1TZ=_1U1.e;continue;}}else{return E(_1TX);}}};return new F(function(){return _1TW(_1TT,_1TU,_1TV);});},_1U2=function(_1U3){var _1U4=function(_){var _1U5=newArr(1,_VW),_1U6=_1U5,_1U7=function(_1U8,_1U9,_){while(1){var _1Ua=E(_1U8);if(_1Ua==1){return _5;}else{var _1Ub=E(_1U9);if(!_1Ub._){return _5;}else{var _=_1U6[_1Ua]=_1Ub.a;_1U8=_1Ua+1|0;_1U9=_1Ub.b;continue;}}}},_1Uc=B(_1U7(0,new T2(1,new T2(1,new T1(1,_1U3),_4),_4),_));return new T4(0,E(_1Tk),E(_1Tk),1,_1U6);};return new F(function(){return _9d(_1U4);});},_1Ud=function(_1Ue,_1Uf,_1Ug,_1Uh){while(1){var _1Ui=E(_1Uh);if(!_1Ui._){var _1Uj=E(_1Ui.b);switch(B(_13l(_1Ue,_1Uf,_1Ug,_1Uj.a,_1Uj.b,_1Uj.c))){case 0:_1Uh=_1Ui.d;continue;case 1:return new T1(1,_1Ui.c);default:_1Uh=_1Ui.e;continue;}}else{return __Z;}}},_1Uk=new T(function(){return B(unCStr("Float"));}),_1Ul=new T(function(){return B(_1zC(_1Uk));}),_1Um=new T(function(){return B(_G(_1zA,_1Ul));}),_1Un=new T(function(){var _1Uo=B(_1ym(_1Um));return new T3(0,_1Uo.a,_1Uo.b,_1Uo.c);}),_1Up=new T(function(){return B(_1zC(_1Rz));}),_1Uq=new T(function(){return B(_G(_1zA,_1Up));}),_1Ur=new T(function(){var _1Us=B(_1ym(_1Uq));return new T3(0,_1Us.a,_1Us.b,_1Us.c);}),_1Ut=new T(function(){return B(unCStr("String"));}),_1Uu=new T(function(){return B(_1zC(_1Ut));}),_1Uv=new T(function(){return B(_G(_1zA,_1Uu));}),_1Uw=new T(function(){var _1Ux=B(_1ym(_1Uv));return new T3(0,_1Ux.a,_1Ux.b,_1Ux.c);}),_1Uy=function(_1Uz){var _1UA=E(_1Uz);return (_1UA._==0)?__Z:new T2(1,E(_1UA.a).b,new T(function(){return B(_1Uy(_1UA.b));}));},_1UB=function(_1UC){var _1UD=E(_1UC);return (_1UD._==0)?__Z:new T2(1,new T(function(){return E(E(E(_1UD.a).c).b);}),new T(function(){return B(_1UB(_1UD.b));}));},_1UE=new T(function(){return B(_7f("pgf/PGF/Linearize.hs:(77,5)-(87,137)|function lin"));}),_1UF=63,_1UG=new T(function(){return B(_1IX("pgf/PGF/Linearize.hs:105:19-70|Just (ty, _, _, _)"));}),_1UH=new T(function(){return B(_7f("pgf/PGF/Linearize.hs:(104,13)-(109,85)|function toApp"));}),_1UI=new T(function(){return B(unCStr("]"));}),_1UJ=function(_1UK,_1UL,_1UM,_1UN){if(!B(_19g(_1UO,_1UK,_1UM))){return false;}else{return new F(function(){return _1bb(_1UL,_1UN);});}},_1UP=function(_1UQ,_1UR){var _1US=E(_1UQ),_1UT=E(_1UR);return new F(function(){return _1UJ(_1US.a,_1US.b,_1UT.a,_1UT.b);});},_1UU=function(_1UV,_1UW,_1UX,_1UY){return (!B(_19g(_1UO,_1UV,_1UX)))?true:(!B(_1bb(_1UW,_1UY)))?true:false;},_1UZ=function(_1V0,_1V1){var _1V2=E(_1V0),_1V3=E(_1V1);return new F(function(){return _1UU(_1V2.a,_1V2.b,_1V3.a,_1V3.b);});},_1V4=new T(function(){return new T2(0,_1UP,_1UZ);}),_1V5=function(_1V6,_1V7){var _1V8=E(_1V6);switch(_1V8._){case 0:var _1V9=E(_1V7);if(!_1V9._){var _1Va=E(_1V8.a),_1Vb=E(_1V9.a);if(!B(_13e(_1Va.a,_1Va.b,_1Va.c,_1Vb.a,_1Vb.b,_1Vb.c))){return false;}else{if(_1V8.b!=_1V9.b){return false;}else{if(_1V8.c!=_1V9.c){return false;}else{var _1Vc=E(_1V8.d),_1Vd=E(_1V9.d);if(!B(_13e(_1Vc.a,_1Vc.b,_1Vc.c,_1Vd.a,_1Vd.b,_1Vd.c))){return false;}else{if(!B(_19g(_19q,_1V8.e,_1V9.e))){return false;}else{return new F(function(){return _19g(_1UO,_1V8.f,_1V9.f);});}}}}}}else{return false;}break;case 1:var _1Ve=E(_1V7);if(_1Ve._==1){return new F(function(){return _sH(_1V8.a,_1Ve.a);});}else{return false;}break;case 2:return (E(_1V7)._==2)?true:false;case 3:return (E(_1V7)._==3)?true:false;case 4:return (E(_1V7)._==4)?true:false;case 5:return (E(_1V7)._==5)?true:false;default:var _1Vf=E(_1V7);if(_1Vf._==6){if(!B(_19g(_1UO,_1V8.a,_1Vf.a))){return false;}else{return new F(function(){return _19g(_1V4,_1V8.b,_1Vf.b);});}}else{return false;}}},_1Vg=function(_1Vh,_1Vi){return (!B(_1V5(_1Vh,_1Vi)))?true:false;},_1UO=new T(function(){return new T2(0,_1V5,_1Vg);}),_1Vj=function(_1Vk,_1Vl){var _1Vm=E(_1Vk),_1Vn=E(_1Vl),_1Vo=E(_1Vm.c);if(!_1Vo){return (E(_1Vn.c)==0)?true:false;}else{if(E(_1Vm.a)!=E(_1Vn.a)){return false;}else{if(E(_1Vm.b)!=E(_1Vn.b)){return false;}else{var _1Vp=_1Vo-1|0;if(0<=_1Vp){var _1Vq=function(_1Vr){while(1){if(!B(_19g(_1UO,_1Vm.d[_1Vr],_1Vn.d[_1Vr]))){return false;}else{if(_1Vr!=_1Vp){var _1Vs=_1Vr+1|0;_1Vr=_1Vs;continue;}else{return true;}}}};return new F(function(){return _1Vq(0);});}else{return true;}}}}},_1Vt=function(_1Vu,_1Vv){var _1Vw=E(_1Vu),_1Vx=E(_1Vv),_1Vy=E(_1Vw.a),_1Vz=E(_1Vx.a),_1VA=E(_1Vy.a),_1VB=E(_1Vz.a);if(!B(_13e(_1VA.a,_1VA.b,_1VA.c,_1VB.a,_1VB.b,_1VB.c))){return false;}else{if(E(_1Vy.b)!=E(_1Vz.b)){return false;}else{if(E(_1Vw.b)!=E(_1Vx.b)){return false;}else{var _1VC=E(_1Vw.c),_1VD=E(_1Vx.c);if(!B(_13e(_1VC.a,_1VC.b,_1VC.c,_1VD.a,_1VD.b,_1VD.c))){return false;}else{if(!B(_19g(_19q,_1Vw.d,_1Vx.d))){return false;}else{var _1VE=E(_1Vw.e),_1VF=E(_1Vx.e);if(!B(_19g(_1CC,_1VE.a,_1VF.a))){return false;}else{return new F(function(){return _1Vj(_1VE.b,_1VF.b);});}}}}}}},_1VG=function(_1VH,_1VI,_1VJ){while(1){var _1VK=E(_1VJ);if(!_1VK._){return false;}else{if(!B(A2(_1VH,_1VK.a,_1VI))){_1VJ=_1VK.b;continue;}else{return true;}}}},_1VL=function(_1VM,_1VN){var _1VO=function(_1VP,_1VQ){while(1){var _1VR=B((function(_1VS,_1VT){var _1VU=E(_1VS);if(!_1VU._){return __Z;}else{var _1VV=_1VU.a,_1VW=_1VU.b;if(!B(_1VG(_1VM,_1VV,_1VT))){return new T2(1,_1VV,new T(function(){return B(_1VO(_1VW,new T2(1,_1VV,_1VT)));}));}else{var _1VX=_1VT;_1VP=_1VW;_1VQ=_1VX;return __continue;}}})(_1VP,_1VQ));if(_1VR!=__continue){return _1VR;}}};return new F(function(){return _1VO(_1VN,_4);});},_1VY=function(_1VZ){return E(E(_1VZ).b);},_1W0=function(_1W1,_1W2,_1W3){var _1W4=new T(function(){return E(E(E(_1W1).c).b);}),_1W5=new T(function(){return E(E(_1W2).h);}),_1W6=new T(function(){return E(E(_1W2).d);}),_1W7=function(_1W8,_1W9,_1Wa,_1Wb,_1Wc){var _1Wd=E(_1W8);if(!_1Wd._){return __Z;}else{var _1We=E(_1Wd.a),_1Wf=_1We.a,_1Wg=E(_1We.b),_1Wh=B(_15n(_1Wg,_1W6));if(!_1Wh._){if(!B(_wr(_jt,_1Wg,_1pq))){var _1Wi=B(_15n(_1Wg,_1W5));if(!_1Wi._){return __Z;}else{var _1Wj=function(_1Wk,_1Wl){while(1){var _1Wm=B((function(_1Wn,_1Wo){var _1Wp=E(_1Wo);if(!_1Wp._){var _1Wq=_1Wp.d,_1Wr=new T(function(){var _1Ws=E(_1Wp.b);if(_1Ws._==1){return B(_0(B(_1W7(new T1(1,new T2(0,_1Wf,_1Ws.a)),_1W9,_1Wa,_1Wb,_1Wc)),new T(function(){return B(_1Wj(_1Wn,_1Wq));},1)));}else{return B(_1Wj(_1Wn,_1Wq));}},1);_1Wk=_1Wr;_1Wl=_1Wp.c;return __continue;}else{return E(_1Wn);}})(_1Wk,_1Wl));if(_1Wm!=__continue){return _1Wm;}}};return new F(function(){return _1Wj(_4,_1Wi.a);});}}else{var _1Wt=new T(function(){var _1Wu=function(_){var _1Wv=newArr(1,_VW),_1Ww=_1Wv,_1Wx=function(_1Wy,_1Wz,_){while(1){var _1WA=E(_1Wy);if(_1WA==1){return _5;}else{var _1WB=E(_1Wz);if(!_1WB._){return _5;}else{var _=_1Ww[_1WA]=_1WB.a;_1Wy=_1WA+1|0;_1Wz=_1WB.b;continue;}}}},_1WC=B(_1Wx(0,new T2(1,new T2(1,new T1(1,_1Wc),_4),_4),_));return new T4(0,E(_1Tk),E(_1Tk),1,_1Ww);};return B(_9d(_1Wu));});return new T2(1,new T2(0,new T(function(){return E(_1W9)+2|0;}),new T5(0,new T2(0,_1Wf,new T(function(){return E(_1W9)+1|0;})),_1Wg,_1JJ,new T2(1,_1Wa,_4),new T2(0,_1Wb,_1Wt))),_4);}}else{var _1WD=new T2(1,_1Wa,_4),_1WE=new T(function(){return E(_1W9)+2|0;}),_1WF=new T(function(){return B(_1U2(_1Wc));}),_1WG=new T(function(){return E(_1W9)+1|0;}),_1WH=function(_1WI){var _1WJ=E(_1WI);return (_1WJ._==0)?__Z:new T2(1,new T2(0,_1WE,new T5(0,new T2(0,_1Wf,_1WG),_1Wg,_1JJ,_1WD,new T(function(){var _1WK=B(_1Sn(_1W2,_1Tp,_1Wb,_1WJ.a,new T2(1,new T5(0,new T2(0,_1JJ,_1W9),_1pk,_1JJ,_1WD,new T2(0,_4,_1WF)),_4)));return new T2(0,_1WK.a,_1WK.b);}))),new T(function(){return B(_1WH(_1WJ.b));}));};return new F(function(){return _1WH(_1Wh.a);});}}},_1WL=new T(function(){return E(E(_1W2).i);}),_1WM=function(_1WN,_1WO,_1WP,_1WQ,_1WR,_1WS,_1WT){while(1){var _1WU=B((function(_1WV,_1WW,_1WX,_1WY,_1WZ,_1X0,_1X1){var _1X2=E(_1X0);switch(_1X2._){case 0:var _1X3=_1WV,_1X4=_1WW,_1X5=_1WX,_1X6=_1WY,_1X7=new T2(1,_1X2.b,_1WZ),_1X8=_1X1;_1WN=_1X3;_1WO=_1X4;_1WP=_1X5;_1WQ=_1X6;_1WR=_1X7;_1WS=_1X2.c;_1WT=_1X8;return __continue;case 1:var _1X3=_1WV,_1X4=_1WW,_1X5=_1WX,_1X6=_1WY,_1X7=_1WZ,_1X8=new T2(1,_1X2.b,_1X1);_1WN=_1X3;_1WO=_1X4;_1WP=_1X5;_1WQ=_1X6;_1WR=_1X7;_1WS=_1X2.a;_1WT=_1X8;return __continue;case 2:if(!E(_1X1)._){var _1X9=E(_1X2.a);switch(_1X9._){case 0:return new T2(1,new T2(0,new T(function(){return E(_1WW)+1|0;}),new T5(0,new T2(0,_1Uw,_1WW),_1pk,_1JJ,new T2(1,_1WX,_4),new T2(0,_4,new T(function(){return B(_1U2(_1X9.a));})))),_4);case 1:var _1Xa=new T(function(){return B(_1U2(new T(function(){return B(_co(0,E(_1X9.a),_4));})));});return new T2(1,new T2(0,new T(function(){return E(_1WW)+1|0;}),new T5(0,new T2(0,_1Ur,_1WW),_1pl,_1JJ,new T2(1,_1WX,_4),new T2(0,_4,_1Xa))),_4);default:var _1Xb=new T(function(){return B(_1U2(new T(function(){var _1Xc=jsShow(E(_1X9.a));return fromJSStr(_1Xc);})));});return new T2(1,new T2(0,new T(function(){return E(_1WW)+1|0;}),new T5(0,new T2(0,_1Un,_1WW),_1pm,_1JJ,new T2(1,_1WX,_4),new T2(0,_4,_1Xb))),_4);}}else{return E(_1UE);}break;case 3:return new F(function(){return _1W7(_1WV,_1WW,_1WX,_1WZ,new T2(1,_1UF,new T(function(){return B(_co(0,_1X2.a,_4));})));});break;case 4:var _1Xd=E(_1X2.a),_1Xe=_1Xd.a,_1Xf=_1Xd.b,_1Xg=_1Xd.c,_1Xh=B(_1Ud(_1Xe,_1Xf,_1Xg,_1WL));if(!_1Xh._){var _1Xi=new T(function(){return B(unAppCStr("[",new T(function(){return B(_0(B(_1Ro(_1Xe,_1Xf,_1Xg)),_1UI));})));});return new F(function(){return _1W7(_1WV,_1WW,_1WX,_1WZ,_1Xi);});}else{var _1Xj=_1Xh.a,_1Xk=new T(function(){var _1Xl=B(_1Ud(_1Xe,_1Xf,_1Xg,_1W4));if(!_1Xl._){return E(_1UG);}else{var _1Xm=E(E(_1Xl.a).a);return new T2(0,new T(function(){return B(_1UB(_1Xm.a));}),_1Xm.b);}}),_1Xn=new T(function(){return E(E(_1Xk).b);}),_1Xo=new T(function(){return E(E(_1Xk).a);}),_1Xp=function(_1Xq,_1Xr){var _1Xs=E(_1Xr);switch(_1Xs._){case 0:var _1Xt=new T(function(){return B(_kh(_1Xo,new T(function(){return B(_1Uy(_1Xs.b));},1)));});return new T2(1,new T3(0,_1Xs.a,new T2(0,_1Xn,_1Xq),_1Xt),_4);case 1:var _1Xu=_1Xs.a,_1Xv=B(_15n(_1Xu,_1Xj));if(!_1Xv._){return __Z;}else{var _1Xw=function(_1Xx,_1Xy){while(1){var _1Xz=B((function(_1XA,_1XB){var _1XC=E(_1XB);if(!_1XC._){var _1XD=new T(function(){return B(_0(B(_1Xp(_1Xu,_1XC.b)),new T(function(){return B(_1Xw(_1XA,_1XC.d));},1)));},1);_1Xx=_1XD;_1Xy=_1XC.c;return __continue;}else{return E(_1XA);}})(_1Xx,_1Xy));if(_1Xz!=__continue){return _1Xz;}}};return new F(function(){return _1Xw(_4,_1Xv.a);});}break;default:return E(_1UH);}},_1XE=new T(function(){return B(_0(_1WZ,_1WY));}),_1XF=function(_1XG,_1XH){var _1XI=E(_1XH);if(!_1XI._){return new T2(1,new T2(0,_1XG,_4),_4);}else{var _1XJ=E(_1XI.a),_1XK=_1XJ.b,_1XL=function(_1XM){var _1XN=E(_1XM);if(!_1XN._){return __Z;}else{var _1XO=E(_1XN.a),_1XP=new T(function(){return B(_1XL(_1XN.b));}),_1XQ=function(_1XR){var _1XS=E(_1XR);if(!_1XS._){return E(_1XP);}else{var _1XT=E(_1XS.a);return new T2(1,new T2(0,_1XT.a,new T2(1,_1XO.b,_1XT.b)),new T(function(){return B(_1XQ(_1XS.b));}));}};return new F(function(){return _1XQ(B(_1XF(_1XO.a,_1XI.b)));});}};return new F(function(){return _1XL(B(_1WM(new T1(1,_1XJ.a),_1XG,_1XK,_1XE,_4,_1XK,_4)));});}},_1XU=function(_1XV,_1XW,_1XX,_1XY,_1XZ){var _1Y0=function(_1Y1){var _1Y2=E(_1Y1);if(!_1Y2._){return E(_1XZ);}else{var _1Y3=E(_1Y2.a),_1Y4=_1Y3.a;return new T2(1,new T2(0,new T(function(){return E(_1Y4)+1|0;}),new T5(0,new T2(0,_1XW,_1Y4),_1XX,_1Xd,new T2(1,_1WX,_4),new T(function(){var _1Y5=B(_1Sn(_1W2,_1Tp,_1WZ,_1XV,_1Y3.b));return new T2(0,_1Y5.a,_1Y5.b);}))),new T(function(){return B(_1Y0(_1Y2.b));}));}};return new F(function(){return _1Y0(B(_1XF(_1WW,B(_kh(_1XY,_1X1)))));});},_1Y6=E(_1WV);if(!_1Y6._){var _1Y7=function(_1Y8,_1Y9){while(1){var _1Ya=B((function(_1Yb,_1Yc){var _1Yd=E(_1Yc);switch(_1Yd._){case 0:_1Y8=new T(function(){return B(_1Y7(_1Yb,_1Yd.d));},1);_1Y9=_1Yd.c;return __continue;case 1:var _1Ye=function(_1Yf,_1Yg){while(1){var _1Yh=B((function(_1Yi,_1Yj){var _1Yk=E(_1Yj);if(!_1Yk._){var _1Yl=new T(function(){var _1Ym=new T(function(){return B(_1Ye(_1Yi,_1Yk.d));}),_1Yn=function(_1Yo){var _1Yp=E(_1Yo);if(!_1Yp._){return E(_1Ym);}else{var _1Yq=E(_1Yp.a),_1Yr=E(_1Yq.b);return new F(function(){return _1XU(_1Yq.a,_1Yr.a,_1Yr.b,_1Yq.c,new T(function(){return B(_1Yn(_1Yp.b));}));});}};return B(_1Yn(B(_1Xp(_1Yd.a,_1Yk.b))));},1);_1Yf=_1Yl;_1Yg=_1Yk.c;return __continue;}else{return E(_1Yi);}})(_1Yf,_1Yg));if(_1Yh!=__continue){return _1Yh;}}};return new F(function(){return _1Ye(_1Yb,_1Yd.b);});break;default:return E(_1Yb);}})(_1Y8,_1Y9));if(_1Ya!=__continue){return _1Ya;}}},_1Ys=E(_1Xj);if(!_1Ys._){var _1Yt=_1Ys.c,_1Yu=_1Ys.d;if(_1Ys.b>=0){return new F(function(){return _1Y7(new T(function(){return B(_1Y7(_4,_1Yu));},1),_1Yt);});}else{return new F(function(){return _1Y7(new T(function(){return B(_1Y7(_4,_1Yt));},1),_1Yu);});}}else{return new F(function(){return _1Y7(_4,_1Ys);});}}else{var _1Yv=E(E(_1Y6.a).b),_1Yw=B(_15n(_1Yv,_1Xj));if(!_1Yw._){return __Z;}else{var _1Yx=function(_1Yy,_1Yz){while(1){var _1YA=B((function(_1YB,_1YC){var _1YD=E(_1YC);if(!_1YD._){var _1YE=new T(function(){var _1YF=new T(function(){return B(_1Yx(_1YB,_1YD.d));}),_1YG=function(_1YH){var _1YI=E(_1YH);if(!_1YI._){return E(_1YF);}else{var _1YJ=E(_1YI.a),_1YK=E(_1YJ.b);return new F(function(){return _1XU(_1YJ.a,_1YK.a,_1YK.b,_1YJ.c,new T(function(){return B(_1YG(_1YI.b));}));});}};return B(_1YG(B(_1Xp(_1Yv,_1YD.b))));},1);_1Yy=_1YE;_1Yz=_1YD.c;return __continue;}else{return E(_1YB);}})(_1Yy,_1Yz));if(_1YA!=__continue){return _1YA;}}};return new F(function(){return _1Yx(_4,_1Yw.a);});}}}break;case 5:return new F(function(){return _1W7(_1WV,_1WW,_1WX,_1WZ,new T(function(){var _1YL=B(_1Fb(B(_0(_1WZ,_1WY)),_1X2.a));return B(_1Ro(_1YL.a,_1YL.b,_1YL.c));}));});break;case 6:var _1X3=_1WV,_1X4=_1WW,_1X5=_1WX,_1X6=_1WY,_1X7=_1WZ,_1X8=_1X1;_1WN=_1X3;_1WO=_1X4;_1WP=_1X5;_1WQ=_1X6;_1WR=_1X7;_1WS=_1X2.a;_1WT=_1X8;return __continue;default:var _1X3=_1WV,_1X4=_1WW,_1X5=_1WX,_1X6=_1WY,_1X7=_1WZ,_1X8=_1X1;_1WN=_1X3;_1WO=_1X4;_1WP=_1X5;_1WQ=_1X6;_1WR=_1X7;_1WS=_1X2.a;_1WT=_1X8;return __continue;}})(_1WN,_1WO,_1WP,_1WQ,_1WR,_1WS,_1WT));if(_1WU!=__continue){return _1WU;}}};return new F(function(){return _1VL(_1Vt,B(_G(_1VY,B(_1WM(_4l,_1Tk,_1W3,_4,_4,_1W3,_4)))));});},_1YM=function(_1YN){var _1YO=E(_1YN);if(!_1YO._){return __Z;}else{return new F(function(){return _0(_1YO.a,new T(function(){return B(_1YM(_1YO.b));},1));});}},_1YP=function(_1YQ){var _1YR=E(_1YQ);if(!_1YR._){return E(_1Pd);}else{var _1YS=E(_1YR.a);if(!_1YS._){return __Z;}else{var _1YT=B(_1YP(_1YR.b));return (_1YT._==0)?__Z:new T1(1,new T2(1,_1YS.a,_1YT.a));}}},_1YU=function(_1YV,_1YW){var _1YX=new T(function(){return B(_1TR(_1FZ,_1TO,_1YW,B(_1TP(_1YV))));}),_1YY=function(_1YZ,_1Z0,_1Z1,_1Z2,_1Z3){var _1Z4=E(_1YX),_1Z5=B(_1YP(B(_1Qw(B(_1Tx(_1Z4.c,_1Z4.e,_1Z4.f,_1YZ,_1Z0,_1Z1,_1Z2,_1Z3)),_4l)).b));if(!_1Z5._){return __Z;}else{return new F(function(){return _1YM(_1Z5.a);});}},_1Z6=function(_1Z7){var _1Z8=E(_1Z7);return new F(function(){return _1YY(_1Z8.a,E(_1Z8.b),_1Z8.c,_1Z8.d,_1Z8.e);});};return function(_1Z9){var _1Za=B(_G(_1Z6,B(_1W0(_1YV,_1YX,_1Z9))));return (_1Za._==0)?__Z:E(_1Za.a);};},_1Zb=new T(function(){return B(unCStr("?0"));}),_1Zc=new T2(0,_4,_1Zb),_1Zd=new T2(1,_1Zc,_4),_1Ze=0,_1Zf=new T(function(){return B(_1Ne(_4,_4));}),_1Zg=function(_1Zh,_1Zi,_1Zj,_1Zk){while(1){var _1Zl=B((function(_1Zm,_1Zn,_1Zo,_1Zp){var _1Zq=E(_1Zm);if(!_1Zq._){return __Z;}else{var _1Zr=_1Zq.b,_1Zs=E(_1Zq.a);if(!_1Zs._){var _1Zt=E(_1Zn);if(E(_1Zs.b)!=_1Zt){var _1Zu=B(_1Zg(_1Zs.c,_1Zt,new T2(1,_1Zp,_1Zo),_1Ze));if(!_1Zu._){var _1Zv=_1Zo;_1Zh=_1Zr;_1Zi=_1Zt;_1Zj=_1Zv;_1Zk=new T(function(){return E(_1Zp)+1|0;});return __continue;}else{return E(_1Zu);}}else{return new T2(1,_1Zp,_1Zo);}}else{var _1Zw=_1Zn,_1Zv=_1Zo;_1Zh=_1Zr;_1Zi=_1Zw;_1Zj=_1Zv;_1Zk=new T(function(){return E(_1Zp)+1|0;});return __continue;}}})(_1Zh,_1Zi,_1Zj,_1Zk));if(_1Zl!=__continue){return _1Zl;}}},_1Zx=function(_1Zy,_1Zz){var _1ZA=E(_1Zy);if(!_1ZA._){var _1ZB=E(_1Zz);if(E(_1ZA.b)!=_1ZB){return new F(function(){return _1Ne(B(_1Zg(_1ZA.c,_1ZB,_4,_1Ze)),_4);});}else{return E(_1Zf);}}else{return E(_1Zf);}},_1ZC=new T(function(){return B(_7f("Muste.hs:(45,9)-(54,31)|function deep"));}),_1ZD=function(_1ZE,_1ZF,_1ZG,_1ZH){var _1ZI=E(_1ZG);if(!_1ZI._){return E(_1ZH);}else{var _1ZJ=_1ZI.b,_1ZK=E(_1ZI.a);if(!_1ZK._){return new T2(1,new T2(0,new T(function(){return B(_1Zx(_1ZE,_1ZF));}),_1ZK.a),new T(function(){return B(_1ZD(_1ZE,_1ZF,_1ZJ,_1ZH));}));}else{return new F(function(){return _0(B(_1ZL(_1ZE,_1ZK)),new T(function(){return B(_1ZD(_1ZE,_1ZF,_1ZJ,_1ZH));},1));});}}},_1ZL=function(_1ZM,_1ZN){var _1ZO=E(_1ZN);if(!_1ZO._){return E(_1ZC);}else{var _1ZP=_1ZO.b,_1ZQ=E(_1ZO.f);if(!_1ZQ._){return __Z;}else{var _1ZR=function(_1ZS){var _1ZT=E(_1ZO.e);if(!_1ZT._){return new F(function(){return _1ZD(_1ZM,_1ZP,_1ZQ,_4);});}else{var _1ZU=E(_1ZT.a);if(_1ZU._==3){if(!E(_1ZT.b)._){var _1ZV=new T(function(){return B(unAppCStr("?",new T(function(){return B(_co(0,_1ZU.a,_4));})));});return new T2(1,new T2(0,new T(function(){return B(_1Zx(_1ZM,_1ZP));}),_1ZV),_4);}else{return new F(function(){return _1ZD(_1ZM,_1ZP,_1ZQ,_4);});}}else{return new F(function(){return _1ZD(_1ZM,_1ZP,_1ZQ,_4);});}}},_1ZW=E(_1ZQ.a);if(!_1ZW._){if(!E(_1ZQ.b)._){return new T2(1,new T2(0,new T(function(){return B(_1Zx(_1ZM,_1ZP));}),_1ZW.a),_4);}else{return new F(function(){return _1ZR(_);});}}else{return new F(function(){return _1ZR(_);});}}}},_1ZX=function(_1ZY){return E(E(_1ZY).c);},_1ZZ=function(_200){return new T1(3,E(_200));},_201=function(_202,_203){while(1){var _204=E(_202);if(!_204._){return E(_203);}else{var _205=new T2(1,_203,_204.a);_202=_204.b;_203=_205;continue;}}},_206=function(_207,_208){var _209=E(_207);if(!_209._){var _20a=new T(function(){var _20b=B(_20c(_209.c,_208));return new T2(0,_20b.a,_20b.b);});return new T2(0,new T(function(){return E(E(_20a).a);}),new T(function(){return B(_201(E(_20a).b,new T1(4,_209.a)));}));}else{return new T2(0,new T(function(){return E(_208)+1|0;}),new T(function(){return B(_1ZZ(_208));}));}},_20c=function(_20d,_20e){var _20f=E(_20d);if(!_20f._){return new T2(0,_20e,_4);}else{var _20g=new T(function(){var _20h=B(_206(_20f.a,_20e));return new T2(0,_20h.a,_20h.b);}),_20i=new T(function(){var _20j=B(_20c(_20f.b,new T(function(){return E(E(_20g).a);})));return new T2(0,_20j.a,_20j.b);});return new T2(0,new T(function(){return E(E(_20i).a);}),new T2(1,new T(function(){return E(E(_20g).b);}),new T(function(){return E(E(_20i).b);})));}},_20k=new T1(3,0),_20l=function(_20m){var _20n=E(_20m);if(!_20n._){return new F(function(){return _201(B(_20c(_20n.c,_1Ze)).b,new T1(4,_20n.a));});}else{return E(_20k);}},_20o=-1,_20p=function(_20q){var _20r=B(_20s(_20q));return new T3(0,_20r.a,_20r.b,_20r.c);},_20t=new T(function(){return B(unCStr("_"));}),_20u=new T(function(){return B(_1zC(_20t));}),_20v=new T(function(){return B(_G(_1zA,_20u));}),_20w=new T(function(){var _20x=B(_1ym(_20v));return new T3(0,_20x.a,_20x.b,_20x.c);}),_20y=new T0(1),_20z=new T2(1,_20y,_4),_20A=new T3(0,_20w,_20o,_20z),_20B=new T2(1,_20A,_4),_20C=new T(function(){return B(_7f("Muste/Tree/Internal.hs:(285,5)-(287,70)|function convert"));}),_20s=function(_20D){var _20E=E(_20D);if(!_20E._){var _20F=E(_20E.b);if(!_20F._){var _20G=_20F.a,_20H=E(_20E.c);return (_20H._==0)?new T3(0,_20G,_20o,_4):new T3(0,_20G,_20o,new T(function(){return B(_G(_20p,_20H));}));}else{return E(_20C);}}else{return new T3(0,_20E.a,_20o,_20B);}},_20I=function(_20J,_20K){var _20L=E(_20K);if(!_20L._){return new T2(0,_20J,_4);}else{var _20M=new T(function(){var _20N=E(_20L.a);if(!_20N._){var _20O=_20N.a,_20P=E(_20N.c);if(!_20P._){return new T2(0,new T(function(){return E(_20J)+1|0;}),new T3(0,_20O,_20J,_4));}else{var _20Q=new T(function(){var _20R=B(_20I(_20J,_20P));return new T2(0,_20R.a,_20R.b);}),_20S=new T(function(){return E(E(_20Q).a);});return new T2(0,new T(function(){return E(_20S)+1|0;}),new T3(0,_20O,_20S,new T(function(){return E(E(_20Q).b);})));}}else{return new T2(0,_20J,_20y);}}),_20T=new T(function(){var _20U=B(_20I(new T(function(){return E(E(_20M).a);}),_20L.b));return new T2(0,_20U.a,_20U.b);});return new T2(0,new T(function(){return E(E(_20T).a);}),new T2(1,new T(function(){return E(E(_20M).b);}),new T(function(){return E(E(_20T).b);})));}},_20V=function(_20W){var _20X=B(_20s(_20W)),_20Y=_20X.a,_20Z=E(_20X.c);if(!_20Z._){return new T3(0,_20Y,_1Ze,_4);}else{var _210=new T(function(){var _211=B(_20I(_1Ze,_20Z));return new T2(0,_211.a,_211.b);});return new T3(0,_20Y,new T(function(){return E(E(_210).a);}),new T(function(){return E(E(_210).b);}));}},_212=function(_213,_214,_215){var _216=B(A3(_1YU,new T(function(){return B(_1ZX(_213));}),_214,new T(function(){return B(_20l(_215));})));if(!_216._){return E(_1Zd);}else{return new F(function(){return _1ZL(new T(function(){return B(_20V(_215));}),_216.a);});}},_217=new T2(1,_4,_4),_218=function(_219,_21a){var _21b=function(_21c,_21d){var _21e=E(_21c);if(!_21e._){return E(_21d);}else{var _21f=_21e.a,_21g=E(_21d);if(!_21g._){return E(_21e);}else{var _21h=_21g.a;return (B(A2(_219,_21f,_21h))==2)?new T2(1,_21h,new T(function(){return B(_21b(_21e,_21g.b));})):new T2(1,_21f,new T(function(){return B(_21b(_21e.b,_21g));}));}}},_21i=function(_21j){var _21k=E(_21j);if(!_21k._){return __Z;}else{var _21l=E(_21k.b);return (_21l._==0)?E(_21k):new T2(1,new T(function(){return B(_21b(_21k.a,_21l.a));}),new T(function(){return B(_21i(_21l.b));}));}},_21m=new T(function(){return B(_21n(B(_21i(_4))));}),_21n=function(_21o){while(1){var _21p=E(_21o);if(!_21p._){return E(_21m);}else{if(!E(_21p.b)._){return E(_21p.a);}else{_21o=B(_21i(_21p));continue;}}}},_21q=new T(function(){return B(_21r(_4));}),_21s=function(_21t,_21u,_21v){while(1){var _21w=B((function(_21x,_21y,_21z){var _21A=E(_21z);if(!_21A._){return new T2(1,new T2(1,_21x,_21y),_21q);}else{var _21B=_21A.a;if(B(A2(_219,_21x,_21B))==2){var _21C=new T2(1,_21x,_21y);_21t=_21B;_21u=_21C;_21v=_21A.b;return __continue;}else{return new T2(1,new T2(1,_21x,_21y),new T(function(){return B(_21r(_21A));}));}}})(_21t,_21u,_21v));if(_21w!=__continue){return _21w;}}},_21D=function(_21E,_21F,_21G){while(1){var _21H=B((function(_21I,_21J,_21K){var _21L=E(_21K);if(!_21L._){return new T2(1,new T(function(){return B(A1(_21J,new T2(1,_21I,_4)));}),_21q);}else{var _21M=_21L.a,_21N=_21L.b;switch(B(A2(_219,_21I,_21M))){case 0:_21E=_21M;_21F=function(_21O){return new F(function(){return A1(_21J,new T2(1,_21I,_21O));});};_21G=_21N;return __continue;case 1:_21E=_21M;_21F=function(_21P){return new F(function(){return A1(_21J,new T2(1,_21I,_21P));});};_21G=_21N;return __continue;default:return new T2(1,new T(function(){return B(A1(_21J,new T2(1,_21I,_4)));}),new T(function(){return B(_21r(_21L));}));}}})(_21E,_21F,_21G));if(_21H!=__continue){return _21H;}}},_21r=function(_21Q){var _21R=E(_21Q);if(!_21R._){return E(_217);}else{var _21S=_21R.a,_21T=E(_21R.b);if(!_21T._){return new T2(1,_21R,_4);}else{var _21U=_21T.a,_21V=_21T.b;if(B(A2(_219,_21S,_21U))==2){return new F(function(){return _21s(_21U,new T2(1,_21S,_4),_21V);});}else{return new F(function(){return _21D(_21U,function(_21W){return new T2(1,_21S,_21W);},_21V);});}}}};return new F(function(){return _21n(B(_21r(_21a)));});},_21X=function(_21Y,_21Z,_220,_221){var _222=B(_1nK(_4,_221)),_223=new T(function(){return B(_G(_1VY,B(_212(_21Y,_21Z,_220))));}),_224=function(_225,_226){var _227=E(_225);if(!_227._){return __Z;}else{var _228=E(_226);return (_228._==0)?__Z:new T2(1,new T2(0,new T(function(){var _229=E(_223);if(!_229._){var _22a=B(_vm(_4,0));return _22a+_22a|0;}else{var _22b=B(_G(_1VY,B(_212(_21Y,_21Z,_227.a))));if(!_22b._){var _22c=B(_vm(_4,0));return _22c+_22c|0;}else{var _22d=B(_1Nj(_t1,_229,_22b,_4,_4));return B(_vm(_22d.a,0))+B(_vm(_22d.b,0))|0;}}}),_228.a),new T(function(){return B(_224(_227.b,_228.b));}));}};return new F(function(){return _G(_1VY,B(_218(function(_22e,_22f){var _22g=E(_22e),_22h=E(_22f),_22i=E(_22h.a),_22j=E(_22g.a);if(_22i>=_22j){if(_22i!=_22j){return 2;}else{var _22k=B(_212(_21Y,_21Z,_22g.b)),_22l=B(_vm(_22k,0)),_22m=B(_212(_21Y,_21Z,_22h.b)),_22n=B(_vm(_22m,0));if(_22l>=_22n){if(_22l!=_22n){return 2;}else{return new F(function(){return _1c5(_1P9,_22k,_22m);});}}else{return 0;}}}else{return 0;}},B(_224(_222,_222)))));});},_22o=function(_22p){while(1){var _22q=E(_22p);if(!_22q._){return false;}else{if(!E(_22q.a)){_22p=_22q.b;continue;}else{return true;}}}},_22r=function(_22s){var _22t=E(_22s);if(!_22t._){return new F(function(){return _22o(B(_G(_22r,_22t.c)));});}else{return true;}},_22u=function(_22v){return (!B(_22r(_22v)))?true:false;},_22w=function(_22x){while(1){var _22y=E(_22x);if(!_22y._){_22x=new T1(1,I_fromInt(_22y.a));continue;}else{return new F(function(){return I_toString(_22y.a);});}}},_22z=function(_22A,_22B){return new F(function(){return _0(fromJSStr(B(_22w(_22A))),_22B);});},_22C=new T1(0,0),_22D=function(_22E,_22F,_22G){if(_22E<=6){return new F(function(){return _22z(_22F,_22G);});}else{if(!B(_FO(_22F,_22C))){return new F(function(){return _22z(_22F,_22G);});}else{return new T2(1,_cn,new T(function(){return B(_0(fromJSStr(B(_22w(_22F))),new T2(1,_cm,_22G)));}));}}},_22H=new T1(0,1),_22I=new T1(0,0),_22J=new T(function(){var _22K=B(_K3(_22I,_22H));return new T2(1,_22K.a,_22K.b);}),_22L=32,_22M=new T(function(){return B(unCStr(" "));}),_22N=new T2(0,_4,_22M),_22O=new T2(1,_22N,_4),_22P=function(_22Q){var _22R=E(_22Q);if(!_22R._){return E(_22O);}else{var _22S=E(_22R.a);return new T2(1,new T2(0,_22S.a,_22M),new T2(1,_22S,new T(function(){return B(_22P(_22R.b));})));}},_22T=function(_22U,_22V,_22W){var _22X=function(_22Y,_22Z){var _230=E(_22Y);if(!_230._){return __Z;}else{var _231=_230.b,_232=E(_22Z);if(!_232._){return __Z;}else{var _233=_232.b,_234=new T(function(){var _235=E(_232.a),_236=new T(function(){var _237=new T(function(){if(!E(_22U)){return __Z;}else{return B(unAppCStr(" ",new T(function(){return B(_3X(_eq,_235.a,_4));})));}},1);return B(_0(_235.b,_237));});if(!E(_22V)){return B(_0(_236,new T(function(){return B(_22X(_231,_233));},1)));}else{var _238=new T(function(){return B(_0(B(_22D(0,_230.a,_4)),new T(function(){return B(unAppCStr(") ",_236));},1)));});return B(_0(B(unAppCStr("(",_238)),new T(function(){return B(_22X(_231,_233));},1)));}});return new T2(1,_22L,_234);}}},_239=B(_22X(_22J,new T(function(){return B(_22P(_22W));},1)));return (_239._==0)?__Z:E(_239.b);},_23a=function(_23b,_23c,_23d){var _23e=function(_23f){return new F(function(){return _22T(_wz,_wz,new T(function(){return B(_212(_23b,_23c,_23f));},1));});};return new F(function(){return _G(_23e,_23d);});},_23g=function(_23h,_23i){var _23j=E(_23i);if(!_23j._){return new T2(0,_4,_4);}else{var _23k=_23j.a;if(!B(A1(_23h,_23k))){var _23l=new T(function(){var _23m=B(_23g(_23h,_23j.b));return new T2(0,_23m.a,_23m.b);});return new T2(0,new T2(1,_23k,new T(function(){return E(E(_23l).a);})),new T(function(){return E(E(_23l).b);}));}else{return new T2(0,_4,_23j);}}},_23n=function(_23o){var _23p=_23o>>>0;if(_23p>887){var _23q=u_iswspace(_23o);return (E(_23q)==0)?false:true;}else{var _23r=E(_23p);return (_23r==32)?true:(_23r-9>>>0>4)?(E(_23r)==160)?true:false:true;}},_23s=function(_23t){return new F(function(){return _23n(E(_23t));});},_23u=function(_23v){var _23w=B(_Gz(_23s,_23v));if(!_23w._){return __Z;}else{var _23x=new T(function(){var _23y=B(_23g(_23s,_23w));return new T2(0,_23y.a,_23y.b);});return new T2(1,new T(function(){return E(E(_23x).a);}),new T(function(){return B(_23u(E(_23x).b));}));}},_23z=function(_23A,_23B,_23C,_23D,_23E,_23F){var _23G=new T(function(){var _23H=B(_1Fk(_23C,_23D));if(!_23H._){return E(_1Fx);}else{return E(_23H.a);}}),_23I=new T(function(){return B(_G(_1VY,B(_212(_23A,_23B,_23G))));}),_23J=new T(function(){return B(_vm(_23I,0));}),_23K=new T(function(){var _23L=B(_vm(B(_212(_23A,_23B,_23G)),0));if(!E(_23E)){return _23L;}else{return _23L+1|0;}}),_23M=B(_1Md(function(_23N){return E(_23K)>=B(_vm(B(_212(_23A,_23B,_23N)),0));},B(_21X(_23A,_23B,_23G,B(_1ot(_22u,B(_1MX(_23A,_23C,_23D,_23F)))))))),_23O=function(_23P,_23Q){while(1){var _23R=B((function(_23S,_23T){var _23U=E(_23S);if(!_23U._){return __Z;}else{var _23V=_23U.a,_23W=_23U.b,_23X=E(_23T);if(!_23X._){return __Z;}else{var _23Y=_23X.a,_23Z=_23X.b,_240=B(_23u(_23V));if(!B(_1bb(_240,_23I))){var _241=B(_vm(_240,0)),_242=E(_23J);if(_241!=_242){if(_241<=_242){_23P=_23W;_23Q=_23Z;return __continue;}else{var _243=E(_240);if(!_243._){var _244=B(_vm(_4,0));if(!(_244+_244|0)){_23P=_23W;_23Q=_23Z;return __continue;}else{return new T2(1,new T2(0,_23V,_23Y),new T(function(){return B(_23O(_23W,_23Z));}));}}else{var _245=E(_23I);if(!_245._){var _246=B(_vm(_4,0));if(!(_246+_246|0)){_23P=_23W;_23Q=_23Z;return __continue;}else{return new T2(1,new T2(0,_23V,_23Y),new T(function(){return B(_23O(_23W,_23Z));}));}}else{var _247=B(_1Nj(_t1,_243,_245,_4,_4));if(!(B(_vm(_247.a,0))+B(_vm(_247.b,0))|0)){_23P=_23W;_23Q=_23Z;return __continue;}else{return new T2(1,new T2(0,_23V,_23Y),new T(function(){return B(_23O(_23W,_23Z));}));}}}}}else{return new T2(1,new T2(0,_23V,_23Y),new T(function(){return B(_23O(_23W,_23Z));}));}}else{_23P=_23W;_23Q=_23Z;return __continue;}}}})(_23P,_23Q));if(_23R!=__continue){return _23R;}}};return new F(function(){return _23O(B(_23a(_23A,_23B,_23M)),_23M);});},_248=new T(function(){return B(unCStr("won"));}),_249=new T(function(){return new T1(1,"left");}),_24a=new T(function(){return new T1(1,"top");}),_24b=new T(function(){return new T2(0,E(new T1(2,"class")),"menu");}),_24c=new T(function(){return new T2(0,E(new T1(2,"id")),"suggestionList");}),_24d=new T(function(){return B(unCStr(" extending"));}),_24e=new T(function(){return B(unCStr("offsetTop"));}),_24f=new T(function(){return B(unCStr("offsetLeft"));}),_24g=1,_24h=new T(function(){return B(unCStr(" Clicks"));}),_24i=new T(function(){return B(err(_rM));}),_24j=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:263:11-20"));}),_24k=new T6(0,_4l,_4m,_4,_24j,_4l,_4l),_24l=new T(function(){return B(_4d(_24k));}),_24m=new T(function(){return B(unCStr("px"));}),_24n=new T(function(){return B(err(_rO));}),_24o=function(_24p,_24q){var _24r=function(_24s,_24t){var _24u=function(_24v){return new F(function(){return A1(_24t,new T(function(){return  -E(_24v);}));});},_24w=new T(function(){return B(_Dj(function(_24x){return new F(function(){return A3(_24p,_24x,_24s,_24u);});}));}),_24y=function(_24z){return E(_24w);},_24A=function(_24B){return new F(function(){return A2(_C0,_24B,_24y);});},_24C=new T(function(){return B(_Dj(function(_24D){var _24E=E(_24D);if(_24E._==4){var _24F=E(_24E.a);if(!_24F._){return new F(function(){return A3(_24p,_24E,_24s,_24t);});}else{if(E(_24F.a)==45){if(!E(_24F.b)._){return E(new T1(1,_24A));}else{return new F(function(){return A3(_24p,_24E,_24s,_24t);});}}else{return new F(function(){return A3(_24p,_24E,_24s,_24t);});}}}else{return new F(function(){return A3(_24p,_24E,_24s,_24t);});}}));}),_24G=function(_24H){return E(_24C);};return new T1(1,function(_24I){return new F(function(){return A2(_C0,_24I,_24G);});});};return new F(function(){return _Ea(_24r,_24q);});},_24J=function(_24K){var _24L=E(_24K);if(!_24L._){var _24M=_24L.b,_24N=new T(function(){return B(_vB(new T(function(){return B(_p1(E(_24L.a)));}),new T(function(){return B(_vm(_24M,0));},1),B(_G(_vr,_24M))));});return new T1(1,_24N);}else{return (E(_24L.b)._==0)?(E(_24L.c)._==0)?new T1(1,new T(function(){return B(_vS(_vl,_24L.a));})):__Z:__Z;}},_24O=function(_24P){var _24Q=E(_24P);if(_24Q._==5){var _24R=B(_24J(_24Q.a));if(!_24R._){return E(_H8);}else{var _24S=new T(function(){return B(_ph(_24R.a));});return function(_24T,_24U){return new F(function(){return A1(_24U,_24S);});};}}else{return E(_H8);}},_24V=new T(function(){return B(A3(_24o,_24O,_DQ,_IO));}),_24W=new T(function(){return B(err(_rM));}),_24X=new T(function(){return B(err(_rO));}),_24Y=new T(function(){return B(unCStr("_"));}),_24Z=92,_250=39,_251=function(_252){var _253=E(_252);if(!_253._){return __Z;}else{var _254=_253.b,_255=E(_253.a);switch(E(_255)){case 39:return __Z;case 92:var _256=E(_254);if(!_256._){return __Z;}else{var _257=_256.b;switch(E(_256.a)){case 39:return new T2(1,new T2(0,_250,_257),_4);case 92:return new T2(1,new T2(0,_24Z,_257),_4);default:return __Z;}}break;default:return new T2(1,new T2(0,_255,_254),_4);}}},_258=function(_259,_25a){var _25b=function(_25c){var _25d=E(_25c);if(!_25d._){return __Z;}else{var _25e=E(_25d.a);return new F(function(){return _0(B(_rT(B(A1(_25a,_25e.a)),_25e.b)),new T(function(){return B(_25b(_25d.b));},1));});}};return function(_25f){var _25g=B(_25b(B(A1(_259,_25f))));return (_25g._==0)?new T0(2):new T1(4,_25g);};},_25h=function(_25i){return new T1(1,B(_258(_251,_25i)));},_25j=function(_25k,_25l){var _25m=new T(function(){var _25n=function(_25o){return new F(function(){return _25j(_25k,function(_25p){return new F(function(){return A1(_25l,new T2(1,_25o,_25p));});});});};return B(A1(_25k,_25n));});return new F(function(){return _s3(B(A1(_25l,_4)),_25m);});},_25q=function(_25r){var _25s=function(_25t){var _25u=E(_25t);if(!_25u._){return __Z;}else{var _25v=E(_25u.a),_25w=function(_25x){var _25y=new T(function(){return B(A1(_25r,new T2(1,_25v.a,_25x)));});return new T1(0,function(_25z){return (E(_25z)==39)?E(_25y):new T0(2);});};return new F(function(){return _0(B(_rT(B(_25j(_25h,_25w)),_25v.b)),new T(function(){return B(_25s(_25u.b));},1));});}},_25A=function(_25B){var _25C=B(_25s(B(_251(_25B))));return (_25C._==0)?new T0(2):new T1(4,_25C);};return function(_25D){return (E(_25D)==39)?E(new T1(1,_25A)):new T0(2);};},_25E=function(_25F){var _25G=B(_1ym(B(_G(_1zA,B(_1zC(_25F))))));return new T3(0,_25G.a,_25G.b,_25G.c);},_25H=function(_25I){return new F(function(){return _1R3(E(_25I));});},_25J=function(_25K){var _25L=function(_25M){if(!B(_sH(_25M,_24Y))){return new F(function(){return A1(_25K,new T(function(){return B(_25E(_25M));}));});}else{return new T0(2);}},_25N=function(_25O){var _25P=E(_25O);return (!B(_1QE(_25P)))?new T0(2):new T1(1,B(_tM(_25H,function(_25Q){return new F(function(){return _25L(new T2(1,_25P,_25Q));});})));};return new F(function(){return _s3(new T1(0,_25N),new T(function(){return new T1(0,B(_25q(_25L)));}));});},_25R=new T(function(){return B(_25J(_te));}),_25S=function(_25T,_25U){while(1){var _25V=E(_25T);if(!_25V._){return E(_25U);}else{_25T=_25V.b;_25U=_25V.a;continue;}}},_25W=function(_25X){return E(E(_25X).a);},_25Y=function(_25Z,_260){var _261=new T(function(){var _262=B(_263(B(_1VY(_25Z))));return new T2(0,_262.a,_262.b);});return new T2(0,new T2(1,new T(function(){return B(_25W(_25Z));}),new T(function(){return B(_25W(_261));})),new T(function(){return B(_1VY(_261));}));},_263=function(_264){var _265=E(_264);if(!_265._){return new T2(0,_4,_4);}else{if(E(_265.a)==32){var _266=B(_267(_265.b));if(!_266._){return new T2(0,_4,_265);}else{return new F(function(){return _25Y(_266.a,_266.b);});}}else{var _268=B(_267(_265));if(!_268._){return new T2(0,_4,_265);}else{return new F(function(){return _25Y(_268.a,_268.b);});}}}},_269=new T(function(){return B(unCStr("?"));}),_26a=new T(function(){return B(_1zC(_269));}),_26b=new T(function(){return B(_G(_1zA,_26a));}),_26c=new T(function(){var _26d=B(_1ym(_26b));return new T3(0,_26d.a,_26d.b,_26d.c);}),_26e=new T2(0,_26c,_4),_26f=new T1(1,_26e),_26g=new T(function(){return B(_rT(_25R,_4));}),_26h=function(_26i){var _26j=E(_26i);if(!_26j._){var _26k=E(_26g);return (_26k._==0)?__Z:new T1(1,_26k.a);}else{if(E(_26j.a)==63){var _26l=B(_26h(_26j.b));if(!_26l._){return E(_26f);}else{var _26m=E(_26l.a),_26n=new T(function(){var _26o=B(_1ym(B(_G(_1zA,B(_1zC(B(unAppCStr("?",new T(function(){var _26p=E(_26m.a);return B(_1Ro(_26p.a,_26p.b,_26p.c));})))))))));return new T3(0,_26o.a,_26o.b,_26o.c);});return new T1(1,new T2(0,_26n,_26m.b));}}else{var _26q=B(_rT(_25R,_26j));return (_26q._==0)?__Z:new T1(1,_26q.a);}}},_26r=function(_26s){while(1){var _26t=B((function(_26u){var _26v=E(_26u);if(!_26v._){return new T2(0,_4,_4);}else{var _26w=_26v.b,_26x=function(_26y){var _26z=B(_26h(_26v));if(!_26z._){return new T2(0,_4,_26v);}else{var _26A=_26z.a,_26B=new T(function(){var _26C=B(_26r(B(_1VY(_26A))));return new T2(0,_26C.a,_26C.b);});return new T2(0,new T2(1,new T(function(){return B(_25W(_26A));}),new T(function(){return B(_25W(_26B));})),new T(function(){return B(_1VY(_26B));}));}};switch(E(_26v.a)){case 32:_26s=_26w;return __continue;case 40:_26s=_26w;return __continue;case 41:return new T2(0,_4,_26w);case 45:var _26D=E(_26w);if(!_26D._){return new F(function(){return _26x(_);});}else{if(E(_26D.a)==62){_26s=_26D.b;return __continue;}else{return new F(function(){return _26x(_);});}}break;default:return new F(function(){return _26x(_);});}}})(_26s));if(_26t!=__continue){return _26t;}}},_26E=new T(function(){return B(unCStr("?"));}),_26F=function(_26G){var _26H=E(_26G);if(!_26H._){var _26I=E(_26H.b);if(!_26I._){return E(_26I.a);}else{return new F(function(){return _25E(_26E);});}}else{return E(_26H.a);}},_26J=new T(function(){return B(_1zC(_26E));}),_26K=new T(function(){return B(_G(_1zA,_26J));}),_26L=new T(function(){var _26M=B(_1ym(_26K));return new T3(0,_26M.a,_26M.b,_26M.c);}),_26N=new T2(0,_26L,_4),_26O=function(_26P){var _26Q=E(_26P);if(!_26Q._){var _26R=_26Q.c,_26S=new T(function(){var _26T=E(_26Q.b);if(!_26T._){if(!E(_26T.b)._){return new T2(0,_26T.a,new T(function(){return B(_G(_26F,_26R));}));}else{return E(_26T);}}else{return E(_26N);}});return new T3(0,_26Q.a,_26S,new T(function(){return B(_G(_26O,_26R));}));}else{return E(_26Q);}},_26U=function(_26V,_26W){var _26X=E(_26W);return (_26X._==0)?__Z:new T2(1,_26V,new T(function(){return B(_26U(_26X.a,_26X.b));}));},_26Y=new T(function(){return B(unCStr("last"));}),_26Z=new T(function(){return B(_eE(_26Y));}),_270=function(_271){var _272=E(_271);return new T2(0,new T1(1,_272.a),new T(function(){var _273=E(_272.b);if(!_273._){return __Z;}else{if(E(_273.a)==125){return E(_273.b);}else{return E(_273);}}}));},_267=function(_274){var _275=E(_274);if(!_275._){var _276=__Z;}else{if(E(_275.a)==123){var _277=E(_275.b);}else{var _277=E(_275);}var _276=_277;}var _278=function(_279){var _27a=B(_26h(_276));if(!_27a._){return __Z;}else{var _27b=E(_27a.a),_27c=function(_27d){var _27e=new T(function(){var _27f=E(E(_27d).b);if(!_27f._){var _27g=B(_263(_4));return new T2(0,_27g.a,_27g.b);}else{var _27h=_27f.b;switch(E(_27f.a)){case 32:var _27i=E(_27h);if(!_27i._){var _27j=B(_263(_4));return new T2(0,_27j.a,_27j.b);}else{if(E(_27i.a)==123){var _27k=B(_263(_27i.b));return new T2(0,_27k.a,_27k.b);}else{var _27l=B(_263(_27i));return new T2(0,_27l.a,_27l.b);}}break;case 123:var _27m=B(_263(_27h));return new T2(0,_27m.a,_27m.b);break;default:var _27n=B(_263(_27f));return new T2(0,_27n.a,_27n.b);}}}),_27o=new T(function(){return B(_26O(new T3(0,_27b.a,new T(function(){return B(_25W(_27d));}),new T(function(){return B(_25W(_27e));}))));});return new T2(1,new T2(0,_27o,new T(function(){var _27p=E(E(_27e).b);if(!_27p._){return __Z;}else{if(E(_27p.a)==125){return E(_27p.b);}else{return E(_27p);}}})),_4);},_27q=E(_27b.b);if(!_27q._){var _27r=B(_26r(_4)),_27s=E(_27r.a);if(!_27s._){return __Z;}else{return new F(function(){return _27c(new T2(0,new T2(0,new T(function(){return B(_25S(_27s,_26Z));}),new T(function(){return B(_26U(_27s.a,_27s.b));})),_27r.b));});}}else{if(E(_27q.a)==58){var _27t=B(_26r(_27q.b)),_27u=E(_27t.a);if(!_27u._){return __Z;}else{return new F(function(){return _27c(new T2(0,new T2(0,new T(function(){return B(_25S(_27u,_26Z));}),new T(function(){return B(_26U(_27u.a,_27u.b));})),_27t.b));});}}else{var _27v=B(_26r(_27q)),_27w=E(_27v.a);if(!_27w._){return __Z;}else{return new F(function(){return _27c(new T2(0,new T2(0,new T(function(){return B(_25S(_27w,_26Z));}),new T(function(){return B(_26U(_27w.a,_27w.b));})),_27v.b));});}}}}},_27x=E(_276);if(!_27x._){return new F(function(){return _278(_);});}else{if(E(_27x.a)==63){return new F(function(){return _G(_270,B(_rT(_25R,_27x.b)));});}else{return new F(function(){return _278(_);});}}},_27y=function(_27z){var _27A=E(_27z);if(!_27A._){return __Z;}else{var _27B=E(_27A.a),_27C=function(_27D){return E(new T2(3,_27B.a,_td));};return new F(function(){return _0(B(_rT(new T1(1,function(_27E){return new F(function(){return A2(_C0,_27E,_27C);});}),_27B.b)),new T(function(){return B(_27y(_27A.b));},1));});}},_27F=function(_27G){var _27H=B(_27y(B(_267(_27G))));return (_27H._==0)?new T0(2):new T1(4,_27H);},_27I=new T1(1,_27F),_27J=new T(function(){return B(unCStr("{Pred:(Item->Quality->Comment) {These:(Kind->Item) {Fish:Kind}} {Boring:Quality}}"));}),_27K=new T(function(){return B(_rT(_27I,_27J));}),_27L=new T(function(){var _27M=B(_IV(_27K));if(!_27M._){return E(_24W);}else{if(!E(_27M.b)._){return E(_27M.a);}else{return E(_24X);}}}),_27N=new T(function(){return eval("(function(e){if(e){e.stopPropagation();}})");}),_27O=function(_){var _27P=rMV(E(_1DQ)),_27Q=E(_27P);if(!_27Q._){var _27R=__app1(E(_27N),E(_D));return new F(function(){return _u(_);});}else{var _27S=__app1(E(_27N),E(_27Q.a));return new F(function(){return _u(_);});}},_27T=new T(function(){return eval("(function(e,p,v){e.setAttribute(p, v);})");}),_27U=new T(function(){return eval("(function(e,p,v){e.style[p] = v;})");}),_27V=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_27W=function(_27X,_27Y,_27Z,_280){var _281=new T(function(){return B(A2(_1EF,_27X,_27Z));}),_282=function(_283,_){var _284=E(_283);if(!_284._){return _5;}else{var _285=E(_281),_286=E(_1Dk),_287=__app2(_286,E(_284.a),_285),_288=function(_289,_){while(1){var _28a=E(_289);if(!_28a._){return _5;}else{var _28b=__app2(_286,E(_28a.a),_285);_289=_28a.b;continue;}}};return new F(function(){return _288(_284.b,_);});}},_28c=function(_28d,_){while(1){var _28e=B((function(_28f,_){var _28g=E(_28f);if(!_28g._){return _5;}else{var _28h=_28g.b,_28i=E(_28g.a);if(!_28i._){var _28j=_28i.b,_28k=E(_28i.a);switch(_28k._){case 0:var _28l=E(_281),_28m=E(_27V),_28n=__app3(_28m,_28l,_28k.a,_28j),_28o=function(_28p,_){while(1){var _28q=E(_28p);if(!_28q._){return _5;}else{var _28r=_28q.b,_28s=E(_28q.a);if(!_28s._){var _28t=_28s.b,_28u=E(_28s.a);switch(_28u._){case 0:var _28v=__app3(_28m,_28l,_28u.a,_28t);_28p=_28r;continue;case 1:var _28w=__app3(E(_27U),_28l,_28u.a,_28t);_28p=_28r;continue;default:var _28x=__app3(E(_27T),_28l,_28u.a,_28t);_28p=_28r;continue;}}else{var _28y=B(_282(_28s.a,_));_28p=_28r;continue;}}}};return new F(function(){return _28o(_28h,_);});break;case 1:var _28z=E(_281),_28A=E(_27U),_28B=__app3(_28A,_28z,_28k.a,_28j),_28C=function(_28D,_){while(1){var _28E=E(_28D);if(!_28E._){return _5;}else{var _28F=_28E.b,_28G=E(_28E.a);if(!_28G._){var _28H=_28G.b,_28I=E(_28G.a);switch(_28I._){case 0:var _28J=__app3(E(_27V),_28z,_28I.a,_28H);_28D=_28F;continue;case 1:var _28K=__app3(_28A,_28z,_28I.a,_28H);_28D=_28F;continue;default:var _28L=__app3(E(_27T),_28z,_28I.a,_28H);_28D=_28F;continue;}}else{var _28M=B(_282(_28G.a,_));_28D=_28F;continue;}}}};return new F(function(){return _28C(_28h,_);});break;default:var _28N=E(_281),_28O=E(_27T),_28P=__app3(_28O,_28N,_28k.a,_28j),_28Q=function(_28R,_){while(1){var _28S=E(_28R);if(!_28S._){return _5;}else{var _28T=_28S.b,_28U=E(_28S.a);if(!_28U._){var _28V=_28U.b,_28W=E(_28U.a);switch(_28W._){case 0:var _28X=__app3(E(_27V),_28N,_28W.a,_28V);_28R=_28T;continue;case 1:var _28Y=__app3(E(_27U),_28N,_28W.a,_28V);_28R=_28T;continue;default:var _28Z=__app3(_28O,_28N,_28W.a,_28V);_28R=_28T;continue;}}else{var _290=B(_282(_28U.a,_));_28R=_28T;continue;}}}};return new F(function(){return _28Q(_28h,_);});}}else{var _291=B(_282(_28i.a,_));_28d=_28h;return __continue;}}})(_28d,_));if(_28e!=__continue){return _28e;}}};return new F(function(){return A2(_6i,_27Y,function(_){return new F(function(){return _28c(_280,_);});});});},_292=function(_293,_294,_295,_296){var _297=B(_2z(_294)),_298=function(_299){return new F(function(){return A3(_6c,_297,new T(function(){return B(_27W(_293,_294,_299,_296));}),new T(function(){return B(A2(_dD,_297,_299));}));});};return new F(function(){return A3(_1V,_297,_295,_298);});},_29a=new T(function(){return eval("(function(x){console.log(x);})");}),_29b=function(_29c,_29d,_29e,_29f,_29g,_29h,_){var _29i=B(_27O(_)),_29j=E(_29d),_29k=rMV(_29j),_29l=new T(function(){var _29m=E(E(_29k).d);if(!_29m._){return new T2(0,_29e,_24g);}else{var _29n=E(_29m.a),_29o=E(_29e);if(E(_29n.a)!=_29o){return new T2(0,_29o,_24g);}else{return new T2(0,_29o,new T(function(){return E(_29n.b)+1|0;}));}}}),_=wMV(_29j,new T5(0,new T(function(){return E(E(_29k).a);}),new T(function(){return E(E(_29k).b);}),new T(function(){return E(E(_29k).c);}),new T1(1,_29l),new T(function(){return E(E(_29k).e);}))),_29p=B(A(_1EQ,[_dI,_dJ,_29c,_24f,_])),_29q=B(A(_1EQ,[_dI,_dJ,_29c,_24e,_])),_29r=B(_1Df(_1D2,_)),_29s=new T(function(){var _29t=(B(_vm(_29f,0))+1|0)-E(E(_29l).b)|0;if(0>=_29t){return __Z;}else{return B(_1CW(_29t,_29f));}}),_29u=new T(function(){return B(_0(B(_3X(_eq,_29s,_4)),new T(function(){if(!E(_29g)){return __Z;}else{return E(_24d);}},1)));}),_29v=__app1(E(_29a),toJSStr(B(unAppCStr("Get suggestions for path ",_29u)))),_29w=new T(function(){return E(E(_29h).a);}),_29x=B(A(_292,[_dI,_dJ,_1D4,new T2(1,_24c,new T2(1,_24b,new T2(1,new T(function(){var _29y=B(_IV(B(_rT(_24V,_29q))));if(!_29y._){return E(_24i);}else{if(!E(_29y.b)._){return new T2(0,E(_24a),toJSStr(B(_0(B(_co(0,E(E(_29w).b)+E(_29y.a)|0,_4)),_24m))));}else{return E(_24n);}}}),new T2(1,new T(function(){var _29z=B(_IV(B(_rT(_24V,_29p))));if(!_29z._){return E(_24i);}else{if(!E(_29z.b)._){return new T2(0,E(_249),toJSStr(B(_0(B(_co(0,E(E(_29w).a)+E(_29z.a)|0,_4)),_24m))));}else{return E(_24n);}}}),_4)))),_])),_29A=_29x,_29B=function(_29C,_){while(1){var _29D=B((function(_29E,_){var _29F=E(_29E);if(!_29F._){return _5;}else{var _29G=E(_29F.a),_29H=function(_29I,_){var _29J=B(_27O(_)),_29K=B(_1Df(_1D2,_)),_29L=rMV(_29j),_29M=E(_29L),_29N=_29M.e,_29O=B(_1J7(_29M.c,_29s,_29G.b)),_=wMV(_29j,new T5(0,_29M.a,_29M.b,_29O,_4l,new T(function(){return E(_29N)+1|0;})));if(!B(_1CN(_29O,_27L))){var _29P=B(_1Do(_29j,_));return new F(function(){return _29Q(_29j,_);});}else{var _29R=__app1(E(_1De),toJSStr(E(_1Dm))),_29S=__eq(_29R,E(_D)),_29T=function(_,_29U){var _29V=E(_29U);if(!_29V._){return new F(function(){return die(_24l);});}else{var _29W=__app2(E(_1DC),E(_29V.a),toJSStr(E(_248))),_29X=__app1(E(_1EB),toJSStr(B(unAppCStr("Congratulations! You won after ",new T(function(){return B(_0(B(_co(0,E(_29N)+1|0,_4)),_24h));}))))),_29Y=B(_1Do(_29j,_));return new F(function(){return _29Q(_29j,_);});}};if(!E(_29S)){var _29Z=__isUndef(_29R);if(!E(_29Z)){return new F(function(){return _29T(_,new T1(1,_29R));});}else{return new F(function(){return _29T(_,_4l);});}}else{return new F(function(){return _29T(_,_4l);});}}},_2a0=B(_1Em(_29A,_29G.a,_29H,_));_29C=_29F.b;return __continue;}})(_29C,_));if(_29D!=__continue){return _29D;}}},_2a1=B(_29B(B(_23z(new T(function(){return E(E(_29k).a);}),new T(function(){return E(E(_29k).b);}),new T(function(){return E(E(_29k).c);}),_29s,_29g,_1EC)),_)),_2a2=__app2(E(_1Dk),E(_29A),E(_1D7));return _5;},_2a3=function(_){return new F(function(){return __app1(E(_1D3),"span");});},_2a4=new T(function(){return new T2(0,E(new T1(2,"class")),"path");}),_2a5=new T2(1,_2a4,_4),_2a6=new T(function(){return B(_292(_dI,_dJ,_2a3,_2a5));}),_2a7=new T(function(){return new T2(0,E(new T1(2,"class")),"word");}),_2a8=new T2(1,_2a7,_4),_2a9=new T(function(){return B(_292(_dI,_dJ,_2a3,_2a8));}),_2aa=new T(function(){return new T2(0,E(new T1(2,"class")),"gap");}),_2ab=new T2(1,_2aa,_4),_2ac=new T(function(){return B(_292(_dI,_dJ,_2a3,_2ab));}),_2ad=new T(function(){return B(unCStr(" "));}),_2ae=function(_2af,_2ag,_2ah,_2ai,_2aj,_2ak,_2al,_2am,_){var _2an=function(_){var _2ao=B(A1(_2a9,_)),_2ap=E(_1Dn),_2aq=__app1(_2ap,toJSStr(E(_2ai))),_2ar=E(_2ao),_2as=E(_1Dk),_2at=__app2(_2as,_2aq,_2ar),_2au=E(_2af),_2av=__app2(_2as,_2ar,_2au),_2aw=function(_){if(!E(_2ak)){return _5;}else{var _2ax=B(A1(_2a6,_)),_2ay=__app1(_2ap,toJSStr(B(_3X(_eq,_2ah,_4)))),_2az=E(_2ax),_2aA=__app2(_2as,_2ay,_2az),_2aB=__app2(_2as,_2az,_2au);return new F(function(){return _u(_);});}};if(!E(_2am)){return new F(function(){return _2aw(_);});}else{var _2aC=B(A(_1DU,[_dK,_dB,_dA,_2ar,_1Cx,function(_2aD,_){return new F(function(){return _29b(_2ar,_2ag,_2aj,_2ah,_wz,_2aD,_);});},_]));return new F(function(){return _2aw(_);});}};if(!E(_2al)){return new F(function(){return _2an(_);});}else{var _2aE=B(A1(_2ac,_)),_2aF=__app1(E(_1Dn),toJSStr(E(_2ad))),_2aG=E(_2aE),_2aH=E(_1Dk),_2aI=__app2(_2aH,_2aF,_2aG),_2aJ=__app2(_2aH,_2aG,E(_2af));if(!E(_2am)){return new F(function(){return _2an(_);});}else{var _2aK=B(A(_1DU,[_dK,_dB,_dA,_2aG,_1Cx,function(_2aD,_){return new F(function(){return _29b(_2aG,_2ag,_2aj,_2ah,_wA,_2aD,_);});},_]));return new F(function(){return _2an(_);});}}},_2aL=new T(function(){return eval("(function(e,c) {return e.classList.contains(c);})");}),_2aM=new T(function(){return B(_j1(0,2147483647));}),_2aN=new T(function(){return B(unCStr("debug"));}),_2aO=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:138:5-20"));}),_2aP=new T6(0,_4l,_4m,_4,_2aO,_4l,_4l),_2aQ=new T(function(){return B(_4d(_2aP));}),_2aR=new T(function(){return B(unCStr("editTree"));}),_29Q=function(_2aS,_){var _2aT=rMV(_2aS),_2aU=_2aT,_2aV=__app1(E(_1De),toJSStr(E(_2aR))),_2aW=__eq(_2aV,E(_D)),_2aX=function(_,_2aY){var _2aZ=E(_2aY);if(!_2aZ._){return new F(function(){return die(_2aQ);});}else{var _2b0=E(_2aZ.a),_2b1=__app1(E(_1D5),_2b0),_2b2=__app2(E(_2aL),_2b0,toJSStr(E(_2aN))),_2b3=_2b2,_2b4=function(_2b5,_2b6,_){while(1){var _2b7=E(_2b5);if(!_2b7._){return _5;}else{var _2b8=E(_2b6);if(!_2b8._){return _5;}else{var _2b9=E(_2b8.a),_2ba=B(_2ae(_2b0,_2aS,_2b9.a,_2b9.b,_2b7.a,_2b3,_wA,_wA,_));_2b5=_2b7.b;_2b6=_2b8.b;continue;}}}},_2bb=new T(function(){return B(_212(new T(function(){return E(E(_2aU).a);},1),new T(function(){return E(E(_2aU).b);},1),new T(function(){return E(E(_2aU).c);})));},1),_2bc=B(_2b4(_2aM,_2bb,_));return _5;}};if(!E(_2aW)){var _2bd=__isUndef(_2aV);if(!E(_2bd)){return new F(function(){return _2aX(_,new T1(1,_2aV));});}else{return new F(function(){return _2aX(_,_4l);});}}else{return new F(function(){return _2aX(_,_4l);});}},_2be=new T(function(){return B(unCStr("FoodsEng"));}),_2bf=new T(function(){return B(_1zC(_2be));}),_2bg=new T(function(){return B(_G(_1zA,_2bf));}),_2bh=new T(function(){var _2bi=B(_1ym(_2bg));return new T3(0,_2bi.a,_2bi.b,_2bi.c);}),_2bj=0,_2bk=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:89:5-22"));}),_2bl=new T6(0,_4l,_4m,_4,_2bk,_4l,_4l),_2bm=new T(function(){return B(_4d(_2bl));}),_2bn=new T(function(){return B(unCStr("sampleTree"));}),_2bo=function(_2bp,_){var _2bq=rMV(_2bp),_2br=_2bq,_2bs=__app1(E(_1De),toJSStr(E(_2bn))),_2bt=__eq(_2bs,E(_D)),_2bu=function(_,_2bv){var _2bw=E(_2bv);if(!_2bw._){return new F(function(){return die(_2bm);});}else{var _2bx=E(_2bw.a),_2by=__app1(E(_1D5),_2bx),_2bz=__app2(E(_2aL),_2bx,toJSStr(E(_2aN))),_2bA=_2bz,_2bB=function(_2bC,_){while(1){var _2bD=E(_2bC);if(!_2bD._){return _5;}else{var _2bE=E(_2bD.a),_2bF=B(_2ae(_2bx,_2bp,_2bE.a,_2bE.b,_2bj,_2bA,_wz,_wz,_));_2bC=_2bD.b;continue;}}},_2bG=B(_2bB(B(_212(new T(function(){return E(E(_2br).a);},1),_2bh,_27L)),_));return _5;}};if(!E(_2bt)){var _2bH=__isUndef(_2bs);if(!E(_2bH)){return new F(function(){return _2bu(_,new T1(1,_2bs));});}else{return new F(function(){return _2bu(_,_4l);});}}else{return new F(function(){return _2bu(_,_4l);});}},_2bI=new T(function(){return eval("(function(a){var arr = new ByteArray(new a.constructor(a[\'buffer\']));return new T4(0,0,a[\'length\']-1,a[\'length\'],arr);})");}),_2bJ=function(_2bK){return E(_2bK);},_2bL=function(_2bM){return E(E(_2bM).a);},_2bN=function(_2bO){return E(E(_2bO).a);},_2bP=function(_2bQ){return E(E(_2bQ).a);},_2bR=function(_2bS){return E(E(_2bS).b);},_2bT=function(_2bU){return E(E(_2bU).a);},_2bV=function(_2bW){var _2bX=new T(function(){return B(A2(_2bT,B(_2bL(B(_2bP(B(_2bN(B(_2bR(_2bW)))))))),_2bJ));}),_2bY=function(_2bZ){var _2c0=function(_){return new F(function(){return __app1(E(_2bI),E(_2bZ));});};return new F(function(){return A1(_2bX,_2c0);});};return E(_2bY);},_2c1="(function(from, to, buf){return new Uint8Array(buf.buffer.slice(from, to+from));})",_2c2=function(_2c3,_2c4,_2c5,_2c6){var _2c7=function(_){var _2c8=eval(E(_2c1)),_2c9=__app3(E(_2c8),E(_2c4),E(_2c5),E(_2c6));return new F(function(){return A3(_2bV,_2c3,_2c9,0);});};return new F(function(){return _z(_2c7);});},_2ca=new T(function(){return B(unCStr("menuList"));}),_2cb=new T(function(){return new T2(0,E(new T1(2,"id")),"menuList");}),_2cc=new T(function(){return B(unCStr("Toggle Debug"));}),_2cd=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:240:51-57"));}),_2ce=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:240:84-90"));}),_2cf=new T(function(){return B(unCStr("Reset"));}),_2cg=new T(function(){return B(unCStr("Pattern match failure in do expression at Main.hs:66:5-13"));}),_2ch=new T6(0,_4l,_4m,_4,_2cg,_4l,_4l),_2ci=new T(function(){return B(_4d(_2ch));}),_2cj=new T(function(){return B(unCStr("menuButton"));}),_2ck=function(_2cl,_2cm,_2cn,_2co){while(1){var _2cp=E(_2co);if(!_2cp._){var _2cq=E(_2cp.b);switch(B(_13l(_2cl,_2cm,_2cn,_2cq.a,_2cq.b,_2cq.c))){case 0:_2co=_2cp.d;continue;case 1:return new T1(1,_2cp.c);default:_2co=_2cp.e;continue;}}else{return __Z;}}},_2cr=function(_2cs){return E(E(E(_2cs).c).b);},_2ct=function(_2cu,_2cv,_2cw,_2cx,_2cy){var _2cz=E(_1JJ);if(!B(_13e(_2cu,_2cv,_2cw,_2cz.a,_2cz.b,_2cz.c))){var _2cA=E(_2cy),_2cB=B(_2ck(_2cA.a,_2cA.b,_2cA.c,E(_2cx).b));if(!_2cB._){return new T0(1);}else{var _2cC=new T(function(){var _2cD=E(E(_2cB.a).a);return new T3(0,_2cD.a,_2cD.b,_2cD.c);});return new T2(0,new T(function(){return E(E(_2cC).b);}),new T(function(){return B(_G(_2cr,E(_2cC).a));}));}}else{return new T0(1);}},_2cE=function(_2cF,_2cG,_2cH,_2cI){while(1){var _2cJ=E(_2cI);if(!_2cJ._){var _2cK=E(_2cJ.b);switch(B(_13l(_2cF,_2cG,_2cH,_2cK.a,_2cK.b,_2cK.c))){case 0:_2cI=_2cJ.d;continue;case 1:return new T1(1,_2cJ.c);default:_2cI=_2cJ.e;continue;}}else{return __Z;}}},_2cL=new T(function(){return B(unCStr("S"));}),_2cM=new T(function(){return B(_1zC(_2cL));}),_2cN=new T(function(){return B(_G(_1zA,_2cM));}),_2cO=new T(function(){return B(unCStr("startcat"));}),_2cP=new T(function(){return B(_1zC(_2cO));}),_2cQ=new T(function(){return B(_G(_1zA,_2cP));}),_2cR=new T(function(){var _2cS=B(_1ym(_2cQ));return new T3(0,_2cS.a,_2cS.b,_2cS.c);}),_2cT=function(_2cU,_2cV){var _2cW=E(_2cR),_2cX=_2cW.a,_2cY=_2cW.b,_2cZ=_2cW.c,_2d0=B(_2cE(_2cX,_2cY,_2cZ,_2cU));if(!_2d0._){var _2d1=B(_2cE(_2cX,_2cY,_2cZ,E(_2cV).a));if(!_2d1._){return new F(function(){return _1ym(_2cN);});}else{var _2d2=E(_2d1.a);if(!_2d2._){return new F(function(){return _1ym(B(_G(_1zA,B(_1zC(_2d2.a)))));});}else{return new F(function(){return _1ym(_2cN);});}}}else{var _2d3=E(_2d0.a);if(!_2d3._){return new F(function(){return _1ym(B(_G(_1zA,B(_1zC(_2d3.a)))));});}else{return new F(function(){return _1ym(_2cN);});}}},_2d4=function(_2d5,_2d6){return new T2(0,_2d5,_2d6);},_2d7=new T(function(){return B(unCStr("empty grammar, no abstract"));}),_2d8=new T(function(){return B(err(_2d7));}),_2d9=new T4(0,_RI,_1JJ,_2d8,_RI),_2da=function(_2db,_2dc){while(1){var _2dd=B((function(_2de,_2df){var _2dg=E(_2df);if(!_2dg._){_2db=new T2(1,_2dg.b,new T(function(){return B(_2da(_2de,_2dg.e));}));_2dc=_2dg.d;return __continue;}else{return E(_2de);}})(_2db,_2dc));if(_2dd!=__continue){return _2dd;}}},_2dh=function(_2di,_2dj,_2dk){var _2dl=E(_2dj);if(!_2dl._){return __Z;}else{var _2dm=E(_2dk);return (_2dm._==0)?__Z:new T2(1,new T(function(){return B(A2(_2di,_2dl.a,_2dm.a));}),new T(function(){return B(_2dh(_2di,_2dl.b,_2dm.b));}));}},_2dn=function(_2do,_2dp,_2dq,_2dr,_2ds,_2dt){var _2du=E(_1JJ);if(!B(_13e(_2dp,_2dq,_2dr,_2du.a,_2du.b,_2du.c))){var _2dv=new T(function(){var _2dw=E(_2ds),_2dx=B(_2da(_4,_2dw.b)),_2dy=new T(function(){return B(_G(function(_2dz){return new F(function(){return _2ct(_2dp,_2dq,_2dr,_2dw,_2dz);});},_2dx));},1);return B(_2dh(_2d4,_2dx,_2dy));});return new T3(0,new T(function(){var _2dA=B(_2cT(_2do,_2ds));return new T3(0,_2dA.a,_2dA.b,_2dA.c);}),_2dv,new T4(0,_2do,new T3(0,_2dp,_2dq,_2dr),_2ds,_2dt));}else{return new T3(0,_2du,_4,_2d9);}},_2dB=function(_2dC){var _2dD=E(_2dC),_2dE=E(_2dD.b),_2dF=B(_2dn(_2dD.a,_2dE.a,_2dE.b,_2dE.c,_2dD.c,_2dD.d));return new T3(0,_2dF.a,_2dF.b,_2dF.c);},_2dG=0,_2dH=function(_2dI){var _2dJ=E(_2dI);if(!_2dJ._){return __Z;}else{var _2dK=E(_2dJ.a),_2dL=function(_2dM){return E(new T2(3,_2dK.a,_td));};return new F(function(){return _0(B(_rT(new T1(1,function(_2dN){return new F(function(){return A2(_C0,_2dN,_2dL);});}),_2dK.b)),new T(function(){return B(_2dH(_2dJ.b));},1));});}},_2dO=function(_2dP){var _2dQ=B(_2dH(B(_267(_2dP))));return (_2dQ._==0)?new T0(2):new T1(4,_2dQ);},_2dR=new T1(1,_2dO),_2dS=new T(function(){return B(unCStr("{Pred:(Item->Quality->Comment) {These:(Kind->Item) {Fish:Kind}} {Italian:Quality}}"));}),_2dT=new T(function(){return B(_rT(_2dR,_2dS));}),_2dU=new T(function(){var _2dV=B(_IV(_2dT));if(!_2dV._){return E(_24W);}else{if(!E(_2dV.b)._){return E(_2dV.a);}else{return E(_24X);}}}),_2dW=function(_2dX){var _2dY=function(_){var _2dZ=nMV(new T5(0,new T(function(){var _2e0=E(_2dX),_2e1=B(_2c2(_ce,_2e0.a,_2e0.b,_2e0.c)),_2e2=E(_2e1.a);return B(_2dB(B(_1Cb(_2e2,(E(_2e1.b)-_2e2|0)+1|0,_2e1,_2dG)).a));}),_2bh,_2dU,_4l,_2bj)),_2e3=_2dZ,_2e4=function(_2e5,_){var _2e6=B(_1Df(_1D2,_)),_2e7=B(_1Df(_2ca,_)),_2e8=rMV(_2e3),_=wMV(_2e3,new T5(0,new T(function(){return E(E(_2e8).a);}),new T(function(){return E(E(_2e8).b);}),new T(function(){return E(E(_2e8).c);}),_4l,new T(function(){return E(E(_2e8).e);})));return _5;},_2e9=B(A(_1DU,[_dK,_dB,_dA,_1D7,_1Cx,_2e4,_])),_2ea=E(_1De),_2eb=__app1(_2ea,toJSStr(E(_2cj))),_2ec=E(_D),_2ed=__eq(_2eb,_2ec),_2ee=function(_,_2ef){var _2eg=E(_2ef);if(!_2eg._){return new F(function(){return die(_2ci);});}else{var _2eh=_2eg.a,_2ei=function(_,_2ej){var _2ek=E(_2ej);if(!_2ek._){return new F(function(){return _c1(_2cd,_);});}else{var _2el=__app1(_2ea,toJSStr(E(_2bn))),_2em=__eq(_2el,_2ec),_2en=function(_,_2eo){var _2ep=E(_2eo);if(!_2ep._){return new F(function(){return _c1(_2ce,_);});}else{var _2eq=toJSStr(E(_2aN)),_2er=E(_1DC),_2es=__app2(_2er,E(_2ek.a),_2eq),_2et=__app2(_2er,E(_2ep.a),_2eq),_2eu=B(_29Q(_2e3,_));return new F(function(){return _2bo(_2e3,_);});}};if(!E(_2em)){var _2ev=__isUndef(_2el);if(!E(_2ev)){return new F(function(){return _2en(_,new T1(1,_2el));});}else{return new F(function(){return _2en(_,_4l);});}}else{return new F(function(){return _2en(_,_4l);});}}},_2ew=function(_2ex,_){var _2ey=__app1(_2ea,toJSStr(E(_2aR))),_2ez=__eq(_2ey,_2ec);if(!E(_2ez)){var _2eA=__isUndef(_2ey);if(!E(_2eA)){return new F(function(){return _2ei(_,new T1(1,_2ey));});}else{return new F(function(){return _2ei(_,_4l);});}}else{return new F(function(){return _2ei(_,_4l);});}},_2eB=function(_2eC,_){var _2eD=B(_27O(_)),_2eE=B(A(_1EQ,[_dI,_dJ,_2eh,_24f,_])),_2eF=B(A(_1EQ,[_dI,_dJ,_2eh,_24e,_])),_2eG=B(_1Df(_2ca,_)),_2eH=B(A(_292,[_dI,_dJ,_1D4,new T2(1,_2cb,new T2(1,_24b,new T2(1,new T(function(){return new T2(0,E(_24a),toJSStr(B(_0(_2eF,_24m))));}),new T2(1,new T(function(){var _2eI=B(_IV(B(_rT(_24V,_2eE))));if(!_2eI._){return E(_24i);}else{if(!E(_2eI.b)._){return new T2(0,E(_249),toJSStr(B(_0(B(_co(0,E(_2eI.a)-200|0,_4)),_24m))));}else{return E(_24n);}}}),_4)))),_])),_2eJ=B(_1Em(_2eH,_2cc,_2ew,_)),_2eK=rMV(_2e3),_2eL=nMV(new T5(0,new T(function(){return E(E(_2eK).a);}),new T(function(){return E(E(_2eK).b);}),_2dU,_4l,_2bj)),_2eM=_2eL,_2eN=B(_1Em(_2eH,_2cf,function(_2eO,_){var _2eP=B(_29Q(_2eM,_)),_2eQ=B(_1Do(_2eM,_)),_2eR=rMV(_2eM),_=wMV(_2e3,_2eR);return _5;},_)),_2eS=__app2(E(_1Dk),E(_2eH),E(_1D7));return _5;},_2eT=B(A(_1DU,[_dK,_dB,_dA,_2eh,_1Cx,_2eB,_])),_2eU=B(_2bo(_2e3,_)),_2eV=B(_29Q(_2e3,_));return _7q;}};if(!E(_2ed)){var _2eW=__isUndef(_2eb);if(!E(_2eW)){return new F(function(){return _2ee(_,new T1(1,_2eb));});}else{return new F(function(){return _2ee(_,_4l);});}}else{return new F(function(){return _2ee(_,_4l);});}};return new T1(0,_2dY);},_2eX=new T(function(){return B(unCStr("AjaxError"));}),_2eY=new T(function(){return B(err(_2eX));}),_2eZ=function(_2f0){var _2f1=E(_2f0);if(!_2f1._){return E(_2eY);}else{return new F(function(){return A3(_8O,_2l,_2f1.a,_2dW);});}},_2f2="Foods.pgf",_2f3=new T(function(){return B(A(_7Y,[_2l,_N,_1b,_i,_h,_2f2,_2eZ]));}),_2f4=function(_){var _2f5=B(_c(_2f3,_4,_));return _5;},_2f6=function(_){return new F(function(){return _2f4(_);});};
var hasteMain = function() {B(A(_2f6, [0]));};window.onload = hasteMain;