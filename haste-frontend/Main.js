"use strict";
var __haste_prog_id = '519443ffa66cd04f028b344b4623f81e6450d110ea371efd2309c8323e7d9092';
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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return _0(_3.b,_2);}));},_4=function(_5,_6){var _7=jsShowI(_5);return _0(fromJSStr(_7),_6);},_8=function(_9,_a,_b){if(_a>=0){return _4(_a,_b);}else{if(_9<=6){return _4(_a,_b);}else{return new T2(1,40,new T(function(){var _c=jsShowI(_a);return _0(fromJSStr(_c),new T2(1,41,_b));}));}}},_d=new T(function(){return unAppCStr(") is outside of enumeration\'s range (0,",new T(function(){return _8(0,2,new T(function(){return unCStr(")");}));}));}),_e=function(_f){return err(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return _8(0,_f,_d);})));},_g=function(_h,_){return new T(function(){var _i=Number(E(_h)),_j=jsTrunc(_i);if(_j<0){return _e(_j);}else{if(_j>2){return _e(_j);}else{return _j;}}});},_k=new T3(0,0,0,0),_l=new T(function(){return jsGetMouseCoords;}),_m=function(_n,_){var _o=E(_n);if(!_o._){return __Z;}else{var _p=_m(_o.b,_);return new T2(1,new T(function(){var _q=Number(E(_o.a));return jsTrunc(_q);}),_p);}},_r=function(_s,_){var _t=__arr2lst(0,_s);return _m(_t,_);},_u=function(_v,_){return new T(function(){var _w=Number(E(_v));return jsTrunc(_w);});},_x=new T2(0,_u,function(_y,_){return _r(E(_y),_);}),_z=function(_A,_){var _B=E(_A);if(!_B._){return __Z;}else{var _C=_z(_B.b,_);return new T2(1,_B.a,_C);}},_D=new T(function(){return unCStr("base");}),_E=new T(function(){return unCStr("GHC.IO.Exception");}),_F=new T(function(){return unCStr("IOException");}),_G=function(_H){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_D,_E,_F),__Z,__Z));},_I=function(_J){return E(E(_J).a);},_K=function(_L,_M,_N){var _O=B(A1(_L,_)),_P=B(A1(_M,_)),_Q=hs_eqWord64(_O.a,_P.a);if(!_Q){return __Z;}else{var _R=hs_eqWord64(_O.b,_P.b);return (!_R)?__Z:new T1(1,_N);}},_S=new T(function(){return unCStr(": ");}),_T=new T(function(){return unCStr(")");}),_U=new T(function(){return unCStr(" (");}),_V=new T(function(){return unCStr("interrupted");}),_W=new T(function(){return unCStr("system error");}),_X=new T(function(){return unCStr("unsatisified constraints");}),_Y=new T(function(){return unCStr("user error");}),_Z=new T(function(){return unCStr("permission denied");}),_10=new T(function(){return unCStr("illegal operation");}),_11=new T(function(){return unCStr("end of file");}),_12=new T(function(){return unCStr("resource exhausted");}),_13=new T(function(){return unCStr("resource busy");}),_14=new T(function(){return unCStr("does not exist");}),_15=new T(function(){return unCStr("already exists");}),_16=new T(function(){return unCStr("resource vanished");}),_17=new T(function(){return unCStr("timeout");}),_18=new T(function(){return unCStr("unsupported operation");}),_19=new T(function(){return unCStr("hardware fault");}),_1a=new T(function(){return unCStr("inappropriate type");}),_1b=new T(function(){return unCStr("invalid argument");}),_1c=new T(function(){return unCStr("failed");}),_1d=new T(function(){return unCStr("protocol error");}),_1e=function(_1f,_1g){switch(E(_1f)){case 0:return _0(_15,_1g);case 1:return _0(_14,_1g);case 2:return _0(_13,_1g);case 3:return _0(_12,_1g);case 4:return _0(_11,_1g);case 5:return _0(_10,_1g);case 6:return _0(_Z,_1g);case 7:return _0(_Y,_1g);case 8:return _0(_X,_1g);case 9:return _0(_W,_1g);case 10:return _0(_1d,_1g);case 11:return _0(_1c,_1g);case 12:return _0(_1b,_1g);case 13:return _0(_1a,_1g);case 14:return _0(_19,_1g);case 15:return _0(_18,_1g);case 16:return _0(_17,_1g);case 17:return _0(_16,_1g);default:return _0(_V,_1g);}},_1h=new T(function(){return unCStr("}");}),_1i=new T(function(){return unCStr("{handle: ");}),_1j=function(_1k,_1l,_1m,_1n,_1o,_1p){var _1q=new T(function(){var _1r=new T(function(){var _1s=new T(function(){var _1t=E(_1n);if(!_1t._){return E(_1p);}else{var _1u=new T(function(){return _0(_1t,new T(function(){return _0(_T,_1p);},1));},1);return _0(_U,_1u);}},1);return _1e(_1l,_1s);}),_1v=E(_1m);if(!_1v._){return E(_1r);}else{return _0(_1v,new T(function(){return _0(_S,_1r);},1));}}),_1w=E(_1o);if(!_1w._){var _1x=E(_1k);if(!_1x._){return E(_1q);}else{var _1y=E(_1x.a);if(!_1y._){var _1z=new T(function(){var _1A=new T(function(){return _0(_1h,new T(function(){return _0(_S,_1q);},1));},1);return _0(_1y.a,_1A);},1);return _0(_1i,_1z);}else{var _1B=new T(function(){var _1C=new T(function(){return _0(_1h,new T(function(){return _0(_S,_1q);},1));},1);return _0(_1y.a,_1C);},1);return _0(_1i,_1B);}}}else{return _0(_1w.a,new T(function(){return _0(_S,_1q);},1));}},_1D=function(_1E){var _1F=E(_1E);return _1j(_1F.a,_1F.b,_1F.c,_1F.d,_1F.f,__Z);},_1G=function(_1H,_1I){var _1J=E(_1H);return _1j(_1J.a,_1J.b,_1J.c,_1J.d,_1J.f,_1I);},_1K=function(_1L,_1M,_1N){var _1O=E(_1M);if(!_1O._){return unAppCStr("[]",_1N);}else{var _1P=new T(function(){var _1Q=new T(function(){var _1R=function(_1S){var _1T=E(_1S);if(!_1T._){return E(new T2(1,93,_1N));}else{var _1U=new T(function(){return B(A2(_1L,_1T.a,new T(function(){return _1R(_1T.b);})));});return new T2(1,44,_1U);}};return _1R(_1O.b);});return B(A2(_1L,_1O.a,_1Q));});return new T2(1,91,_1P);}},_1V=new T(function(){return new T5(0,_G,new T3(0,function(_1W,_1X,_1Y){var _1Z=E(_1X);return _1j(_1Z.a,_1Z.b,_1Z.c,_1Z.d,_1Z.f,_1Y);},_1D,function(_20,_21){return _1K(_1G,_20,_21);}),_22,function(_23){var _24=E(_23);return _K(_I(_24.a),_G,_24.b);},_1D);}),_22=function(_25){return new T2(0,_1V,_25);},_26=new T(function(){return _22(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9");}),__Z,__Z));}),_27=function(_){return die(_26);},_28=function(_29){return E(E(_29).a);},_2a=function(_2b,_2c,_2d,_){var _2e=__arr2lst(0,_2d),_2f=_z(_2e,_),_2g=E(_2f);if(!_2g._){return _27(_);}else{var _2h=E(_2g.b);if(!_2h._){return _27(_);}else{if(!E(_2h.b)._){var _2i=B(A3(_28,_2b,_2g.a,_)),_2j=B(A3(_28,_2c,_2h.a,_));return new T2(0,_2i,_2j);}else{return _27(_);}}}},_2k=function(_2l){var _2m=B(A1(_2l,_));return E(_2m);},_2n=new T(function(){return _2k(function(_){return __jsNull();});}),_2o=function(_2p,_2q,_){if(E(_2p)==7){var _2r=E(_l)(_2q),_2s=_2a(_x,_x,_2r,_),_2t=_2q["deltaX"],_2u=_2q["deltaY"],_2v=_2q["deltaZ"];return new T(function(){return new T3(0,E(_2s),E(__Z),E(new T3(0,_2t,_2u,_2v)));});}else{var _2w=E(_l)(_2q),_2x=_2a(_x,_x,_2w,_),_2y=_2q["button"],_2z=__eq(_2y,E(_2n));if(!E(_2z)){var _2A=__isUndef(_2y);if(!E(_2A)){var _2B=_g(_2y,_);return new T(function(){return new T3(0,E(_2x),E(new T1(1,_2B)),E(_k));});}else{return new T(function(){return new T3(0,E(_2x),E(__Z),E(_k));});}}else{return new T(function(){return new T3(0,E(_2x),E(__Z),E(_k));});}}},_2C=new T2(0,function(_2D){switch(E(_2D)){case 0:return "click";case 1:return "dblclick";case 2:return "mousedown";case 3:return "mouseup";case 4:return "mousemove";case 5:return "mouseover";case 6:return "mouseout";default:return "wheel";}},function(_2E,_2F,_){return _2o(_2E,E(_2F),_);}),_2G=function(_2H){return E(_2H);},_2I=function(_2J,_2K,_){var _2L=B(A1(_2J,_)),_2M=B(A1(_2K,_));return new T(function(){return B(A1(_2L,_2M));});},_2N=function(_2O,_2P,_){var _2Q=B(A1(_2P,_));return new T(function(){return B(A1(_2O,_2Q));});},_2R=function(_2S,_){return _2S;},_2T=function(_2U,_2V,_){var _2W=B(A1(_2U,_));return C > 19 ? new F(function(){return A1(_2V,_);}) : (++C,A1(_2V,_));},_2X=new T(function(){return E(_1V);}),_2Y=function(_2Z){return E(E(_2Z).c);},_30=function(_31){return new T6(0,__Z,7,__Z,_31,__Z,__Z);},_32=function(_33,_){var _34=new T(function(){return B(A2(_2Y,_2X,new T(function(){return B(A1(_30,_33));})));});return die(_34);},_35=function(_36,_){return _32(_36,_);},_37=function(_38){return E(_38);},_39=new T2(0,new T5(0,new T5(0,new T2(0,_2N,function(_3a,_3b,_){var _3c=B(A1(_3b,_));return _3a;}),_2R,_2I,_2T,function(_3d,_3e,_){var _3f=B(A1(_3d,_)),_3g=B(A1(_3e,_));return _3f;}),function(_3h,_3i,_){var _3j=B(A1(_3h,_));return C > 19 ? new F(function(){return A2(_3i,_3j,_);}) : (++C,A2(_3i,_3j,_));},_2T,_2R,function(_3k){return C > 19 ? new F(function(){return A1(_35,_3k);}) : (++C,A1(_35,_3k));}),_37),_3l=new T2(0,_39,_2R),_3m=function(_){return 0;},_3n=(function(e,c) {e.classList.toggle(c);}),_3o=new T(function(){return unCStr("wordHover");}),_3p=new T(function(){return unCStr("Hover word");}),_3q=(function(x){console.log(x);}),_3r=function(_3s,_){var _3t=_3q(toJSStr(E(_3p))),_3u=_3n(E(_3s),toJSStr(E(_3o)));return _3m(_);},_3v=(function(c,p){p.appendChild(c);}),_3w=function(_3x){return E(E(_3x).a);},_3y=function(_3z){return E(E(_3z).d);},_3A=new T2(0,_37,function(_3B,_3C){return C > 19 ? new F(function(){return A2(_3y,_3w(_3B),new T1(1,_3C));}) : (++C,A2(_3y,_3w(_3B),new T1(1,_3C)));}),_3D=(function(t){return document.createElement(t);}),_3E=function(_){return _3D("span");},_3F=function(_3G){return E(E(_3G).c);},_3H=function(_3I){return E(E(_3I).b);},_3J=function(_3K){return E(E(_3K).a);},_3L=(function(e,p,v){e.setAttribute(p, v);}),_3M=(function(e,p,v){e.style[p] = v;}),_3N=(function(e,p,v){e[p] = v;}),_3O=function(_3P){return E(E(_3P).b);},_3Q=function(_3R,_3S,_3T,_3U){var _3V=new T(function(){return B(A2(_3J,_3R,_3T));}),_3W=function(_3X,_){var _3Y=E(_3X);if(!_3Y._){return 0;}else{var _3Z=E(_3V),_40=_3v(E(_3Y.a),_3Z),_41=function(_42,_){while(1){var _43=E(_42);if(!_43._){return 0;}else{var _44=_3v(E(_43.a),_3Z);_42=_43.b;continue;}}};return _41(_3Y.b,_);}},_45=function(_46,_){while(1){var _47=(function(_48,_){var _49=E(_48);if(!_49._){return 0;}else{var _4a=_49.b,_4b=E(_49.a);if(!_4b._){var _4c=_4b.b,_4d=E(_4b.a);switch(_4d._){case 0:var _4e=E(_3V),_4f=_3N(_4e,_4d.a,_4c),_4g=function(_4h,_){while(1){var _4i=E(_4h);if(!_4i._){return 0;}else{var _4j=_4i.b,_4k=E(_4i.a);if(!_4k._){var _4l=_4k.b,_4m=E(_4k.a);switch(_4m._){case 0:var _4n=_3N(_4e,_4m.a,_4l);_4h=_4j;continue;case 1:var _4o=_3M(_4e,_4m.a,_4l);_4h=_4j;continue;default:var _4p=_3L(_4e,_4m.a,_4l);_4h=_4j;continue;}}else{var _4q=_3W(_4k.a,_);_4h=_4j;continue;}}}};return _4g(_4a,_);case 1:var _4r=E(_3V),_4s=_3M(_4r,_4d.a,_4c),_4t=function(_4u,_){while(1){var _4v=E(_4u);if(!_4v._){return 0;}else{var _4w=_4v.b,_4x=E(_4v.a);if(!_4x._){var _4y=_4x.b,_4z=E(_4x.a);switch(_4z._){case 0:var _4A=_3N(_4r,_4z.a,_4y);_4u=_4w;continue;case 1:var _4B=_3M(_4r,_4z.a,_4y);_4u=_4w;continue;default:var _4C=_3L(_4r,_4z.a,_4y);_4u=_4w;continue;}}else{var _4D=_3W(_4x.a,_);_4u=_4w;continue;}}}};return _4t(_4a,_);default:var _4E=E(_3V),_4F=_3L(_4E,_4d.a,_4c),_4G=function(_4H,_){while(1){var _4I=E(_4H);if(!_4I._){return 0;}else{var _4J=_4I.b,_4K=E(_4I.a);if(!_4K._){var _4L=_4K.b,_4M=E(_4K.a);switch(_4M._){case 0:var _4N=_3N(_4E,_4M.a,_4L);_4H=_4J;continue;case 1:var _4O=_3M(_4E,_4M.a,_4L);_4H=_4J;continue;default:var _4P=_3L(_4E,_4M.a,_4L);_4H=_4J;continue;}}else{var _4Q=_3W(_4K.a,_);_4H=_4J;continue;}}}};return _4G(_4a,_);}}else{var _4R=_3W(_4b.a,_);_46=_4a;return __continue;}}})(_46,_);if(_47!=__continue){return _47;}}};return C > 19 ? new F(function(){return A2(_3O,_3S,function(_){return _45(_3U,_);});}) : (++C,A2(_3O,_3S,function(_){return _45(_3U,_);}));},_4S=function(_4T,_4U,_4V,_4W){var _4X=_3w(_4U),_4Y=function(_4Z){return C > 19 ? new F(function(){return A3(_3F,_4X,new T(function(){return B(_3Q(_4T,_4U,_4Z,_4W));}),new T(function(){return B(A2(_3y,_4X,_4Z));}));}) : (++C,A3(_3F,_4X,new T(function(){return B(_3Q(_4T,_4U,_4Z,_4W));}),new T(function(){return B(A2(_3y,_4X,_4Z));})));};return C > 19 ? new F(function(){return A3(_3H,_4X,_4V,_4Y);}) : (++C,A3(_3H,_4X,_4V,_4Y));},_50=new T(function(){return B(_4S(_3A,_39,_3E,new T2(1,new T(function(){return new T2(0,E(new T1(2,"class")),"path");}),__Z)));}),_51=new T(function(){return _2k(function(_){return nMV(__Z);});}),_52=(function(e){if(e){e.stopPropagation();}}),_53=function(_){var _54=rMV(E(_51)),_55=E(_54);if(!_55._){var _56=_52(E(_2n));return _3m(_);}else{var _57=_52(E(_55.a));return _3m(_);}},_58=function(_59,_){var _5a=_53(_);return 0;},_5b=new T(function(){return unCStr(" ");}),_5c=new T(function(){return B(_4S(_3A,_39,_3E,new T2(1,new T(function(){return new T2(0,E(new T1(2,"class")),"gap");}),__Z)));}),_5d=new T(function(){return B(_4S(_3A,_39,_3E,new T2(1,new T(function(){return new T2(0,E(new T1(2,"class")),"word");}),__Z)));}),_5e=(function(s){return document.createTextNode(s);}),_5f=function(_5g){return E(E(_5g).a);},_5h=function(_5i){return E(E(_5i).b);},_5j=function(_5k){return E(E(_5k).a);},_5l=function(_5m){return E(E(_5m).b);},_5n=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_5o=function(_5p,_5q,_5r,_5s,_5t,_5u){var _5v=_5f(_5p),_5w=_3w(_5v),_5x=new T(function(){return _3O(_5v);}),_5y=new T(function(){return _3y(_5w);}),_5z=new T(function(){return B(A1(_5q,_5s));}),_5A=new T(function(){return B(A2(_5j,_5r,_5t));}),_5B=function(_5C){return C > 19 ? new F(function(){return A1(_5y,new T3(0,_5A,_5z,_5C));}) : (++C,A1(_5y,new T3(0,_5A,_5z,_5C)));},_5D=function(_5E){var _5F=new T(function(){var _5G=new T(function(){var _5H=__createJSFunc(2,function(_5I,_){var _5J=B(A2(E(_5E),_5I,_));return _2n;}),_5K=_5H;return function(_){return _5n(E(_5z),E(_5A),_5K);};});return B(A1(_5x,_5G));});return C > 19 ? new F(function(){return A3(_3H,_5w,_5F,_5B);}) : (++C,A3(_3H,_5w,_5F,_5B));},_5L=new T(function(){var _5M=new T(function(){return _3O(_5v);}),_5N=function(_5O){var _5P=new T(function(){return B(A1(_5M,function(_){var _=wMV(E(_51),new T1(1,_5O));return C > 19 ? new F(function(){return A(_5h,[_5r,_5t,_5O,_]);}) : (++C,A(_5h,[_5r,_5t,_5O,_]));}));});return C > 19 ? new F(function(){return A3(_3H,_5w,_5P,_5u);}) : (++C,A3(_3H,_5w,_5P,_5u));};return B(A2(_5l,_5p,_5N));});return C > 19 ? new F(function(){return A3(_3H,_5w,_5L,_5D);}) : (++C,A3(_3H,_5w,_5L,_5D));},_5Q=function(_5R,_5S){return _8(0,E(_5R),_5S);},_5T=function(_5U,_5V,_5W,_5X,_5Y,_5Z,_){var _60=function(_){var _61=B(A1(_5d,_)),_62=_61,_63=_5e(toJSStr(E(_5W))),_64=B(A(_5o,[_3l,_2G,_2C,_62,5,function(_65,_){return _3r(_62,_);},_])),_66=B(A(_5o,[_3l,_2G,_2C,_62,6,function(_67,_){return _3r(_62,_);},_])),_68=E(_62),_69=_3v(_63,_68),_6a=E(_5U),_6b=_3v(_68,_6a),_6c=function(_){if(!E(_5X)){return 0;}else{var _6d=B(A1(_50,_)),_6e=_5e(toJSStr(_1K(_5Q,_5V,__Z))),_6f=E(_6d),_6g=_3v(_6e,_6f),_6h=_3v(_6f,_6a);return _3m(_);}};if(!E(_5Z)){return _6c(_);}else{var _6i=B(A(_5o,[_3l,_2G,_2C,_68,0,_58,_]));return _6c(_);}};if(!E(_5Y)){return _60(_);}else{var _6j=B(A1(_5c,_)),_6k=_6j,_6l=_5e(toJSStr(E(_5b))),_6m=B(A(_5o,[_3l,_2G,_2C,_6k,5,function(_6n,_){return _3r(_6k,_);},_])),_6o=B(A(_5o,[_3l,_2G,_2C,_6k,6,function(_6p,_){return _3r(_6k,_);},_])),_6q=E(_6k),_6r=_3v(_6l,_6q),_6s=_3v(_6q,E(_5U));if(!E(_5Z)){return _60(_);}else{var _6t=B(A(_5o,[_3l,_2G,_2C,_6q,0,_58,_]));return _60(_);}}},_6u=(function(e){while(e.firstChild){e.removeChild(e.firstChild);}}),_6v=new T(function(){return unCStr("debug");}),_6w=new T(function(){return _22(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:63:5-23");}),__Z,__Z));}),_6x=new T(function(){return unCStr("is");}),_6y=new T2(1,0,new T2(1,0,new T2(1,1,__Z))),_6z=new T(function(){return unCStr("Roman");}),_6A=new T2(1,0,__Z),_6B=new T2(1,0,new T2(1,0,new T2(1,1,_6A))),_6C=new T(function(){return unCStr("he");}),_6D=new T2(1,0,new T2(1,0,new T2(1,0,_6A))),_6E=(function(e,c) {return e.classList.contains(c);}),_6F=function(_,_6G){var _6H=E(_6G);if(!_6H._){return die(_6w);}else{var _6I=E(_6H.a),_6J=_6u(_6I),_6K=_6E(_6I,toJSStr(E(_6v))),_6L=_6K,_6M=function(_6N,_){while(1){var _6O=E(_6N);if(!_6O._){return 0;}else{var _6P=E(_6O.a),_6Q=B(_5T(_6I,_6P.a,_6P.b,_6L,false,false,_));_6N=_6O.b;continue;}}},_6R=_6M(new T2(1,new T2(0,_6D,_6C),new T2(1,new T2(0,_6y,_6x),new T2(1,new T2(0,_6B,_6z),__Z))),_);return 0;}},_6S=new T(function(){return unCStr("exampleTree");}),_6T=(function(id){return document.getElementById(id);}),_6U=function(_6V,_){var _6W=rMV(_6V),_6X=_6T(toJSStr(E(_6S))),_6Y=__eq(_6X,E(_2n));if(!E(_6Y)){var _6Z=__isUndef(_6X);if(!E(_6Z)){return _6F(_,new T1(1,_6X));}else{return _6F(_,__Z);}}else{return _6F(_,__Z);}},_70=function(_71,_72){if(_71<=_72){var _73=function(_74){return new T2(1,_74,new T(function(){if(_74!=_72){return _73(_74+1|0);}else{return __Z;}}));};return _73(_71);}else{return __Z;}},_75=new T(function(){return _70(0,2147483647);}),_76=new T(function(){return _22(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:114:5-24");}),__Z,__Z));}),_77=new T(function(){return unCStr("exerciseTree");}),_78=function(_79,_){var _7a=rMV(_79),_7b=_7a,_7c=_6T(toJSStr(E(_77))),_7d=__eq(_7c,E(_2n)),_7e=function(_,_7f){var _7g=E(_7f);if(!_7g._){return die(_76);}else{var _7h=E(_7g.a),_7i=_6u(_7h),_7j=_6E(_7h,toJSStr(E(_6v))),_7k=_7j,_7l=function(_7m,_7n,_){while(1){var _7o=E(_7m);if(!_7o._){return 0;}else{var _7p=E(_7n);if(!_7p._){return 0;}else{var _7q=E(_7p.a),_7r=B(_5T(_7h,_7q.a,_7q.b,_7k,true,true,_));_7m=_7o.b;_7n=_7p.b;continue;}}}},_7s=_7l(_75,new T(function(){return E(E(_7b).c);},1),_);return 0;}};if(!E(_7d)){var _7t=__isUndef(_7c);if(!E(_7t)){return _7e(_,new T1(1,_7c));}else{return _7e(_,__Z);}}else{return _7e(_,__Z);}},_7u=(function(c,p){p.removeChild(c);}),_7v=new T(function(){return document.body;}),_7w=function(_,_7x){var _7y=E(_7x);if(!_7y._){return 0;}else{var _7z=E(_7y.a),_7A=_6u(_7z),_7B=_7u(_7z,E(_7v));return _3m(_);}},_7C=function(_7D,_){var _7E=_6T(toJSStr(E(_7D))),_7F=__eq(_7E,E(_2n));if(!E(_7F)){var _7G=__isUndef(_7E);if(!E(_7G)){return _7w(_,new T1(1,_7E));}else{return _7w(_,__Z);}}else{return _7w(_,__Z);}},_7H=new T(function(){return unCStr("menuList");}),_7I=new T(function(){return unCStr("suggestionList");}),_7J=function(_7K,_){var _7L=_7C(_7I,_),_7M=_7C(_7H,_),_7N=E(_7K),_7O=rMV(_7N),_=wMV(_7N,new T5(0,new T(function(){return E(E(_7O).a);}),new T(function(){return E(E(_7O).b);}),new T(function(){return E(E(_7O).c);}),__Z,new T(function(){return E(E(_7O).e);})));return 0;},_7P=function(_){return _3D("div");},_7Q=new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:51:5-14");}),_7R=new T(function(){return unCStr("score");}),_7S=function(_7T,_){var _7U=_6T(toJSStr(E(_7R))),_7V=__eq(_7U,E(_2n)),_7W=function(_,_7X){var _7Y=E(_7X);if(!_7Y._){return _32(_7Q,_);}else{var _7Z=rMV(E(_7T)),_80=E(_7Y.a),_81=_6u(_80),_82=_5e(toJSStr(_8(0,E(E(_7Z).e),__Z))),_83=_3v(_82,_80);return _3m(_);}};if(!E(_7V)){var _84=__isUndef(_7U);if(!E(_84)){return _7W(_,new T1(1,_7U));}else{return _7W(_,__Z);}}else{return _7W(_,__Z);}},_85=new T2(1,new T2(0,_6D,new T(function(){return unCStr("Augustus");})),new T2(1,new T2(0,_6B,new T(function(){return unCStr("laetus");})),new T2(1,new T2(0,_6y,new T(function(){return unCStr("est");})),__Z))),_86=new T(function(){return unCStr("useS (useCl (simpleCl (usePN Augustus_PN) (complA laetus_A)))");}),_87=function(_88){return fromJSStr(E(_88));},_89=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_8a=function(_8b,_8c,_8d,_8e){var _8f=new T(function(){var _8g=function(_){var _8h=_89(B(A2(_3J,_8b,_8d)),E(_8e));return new T(function(){return String(_8h);});};return _8g;});return C > 19 ? new F(function(){return A2(_3O,_8c,_8f);}) : (++C,A2(_3O,_8c,_8f));},_8i=function(_8j,_8k,_8l,_8m){var _8n=_3w(_8k),_8o=new T(function(){return _3y(_8n);}),_8p=function(_8q){return C > 19 ? new F(function(){return A1(_8o,new T(function(){return _87(_8q);}));}) : (++C,A1(_8o,new T(function(){return _87(_8q);})));},_8r=new T(function(){return B(_8a(_8j,_8k,_8l,new T(function(){return toJSStr(E(_8m));},1)));});return C > 19 ? new F(function(){return A3(_3H,_8n,_8r,_8p);}) : (++C,A3(_3H,_8n,_8r,_8p));},_8s=new T(function(){return err(new T(function(){return unCStr("Prelude.read: no parse");}));}),_8t=new T(function(){return err(new T(function(){return unCStr("Prelude.read: ambiguous parse");}));}),_8u=new T(function(){return unCStr("offsetLeft");}),_8v=new T(function(){return unCStr("base");}),_8w=new T(function(){return unCStr("Control.Exception.Base");}),_8x=new T(function(){return unCStr("PatternMatchFail");}),_8y=function(_8z){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_8v,_8w,_8x),__Z,__Z));},_8A=function(_8B){return E(E(_8B).a);},_8C=function(_8D,_8E){return _0(E(_8D).a,_8E);},_8F=new T(function(){return new T5(0,_8y,new T3(0,function(_8G,_8H,_8I){return _0(E(_8H).a,_8I);},_8A,function(_8J,_8K){return _1K(_8C,_8J,_8K);}),function(_8L){return new T2(0,_8F,_8L);},function(_8M){var _8N=E(_8M);return _K(_I(_8N.a),_8y,_8N.b);},_8A);}),_8O=new T(function(){return unCStr("Non-exhaustive patterns in");}),_8P=function(_8Q,_8R){return die(new T(function(){return B(A2(_2Y,_8R,_8Q));}));},_8S=function(_8T,_8U){return _8P(_8T,_8U);},_8V=function(_8W,_8X){var _8Y=E(_8X);if(!_8Y._){return new T2(0,__Z,__Z);}else{var _8Z=_8Y.a;if(!B(A1(_8W,_8Z))){return new T2(0,__Z,_8Y);}else{var _90=new T(function(){var _91=_8V(_8W,_8Y.b);return new T2(0,_91.a,_91.b);});return new T2(0,new T2(1,_8Z,new T(function(){return E(E(_90).a);})),new T(function(){return E(E(_90).b);}));}}},_92=new T(function(){return unCStr("\n");}),_93=function(_94){return (E(_94)==124)?false:true;},_95=function(_96,_97){var _98=_8V(_93,unCStr(_96)),_99=_98.a,_9a=function(_9b,_9c){var _9d=new T(function(){var _9e=new T(function(){return _0(_97,new T(function(){return _0(_9c,_92);},1));});return unAppCStr(": ",_9e);},1);return _0(_9b,_9d);},_9f=E(_98.b);if(!_9f._){return _9a(_99,__Z);}else{if(E(_9f.a)==124){return _9a(_99,new T2(1,32,_9f.b));}else{return _9a(_99,__Z);}}},_9g=function(_9h){return _8S(new T1(0,new T(function(){return _95(_9h,_8O);})),_8F);},_9i=new T(function(){return B(_9g("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_9j=function(_9k,_9l){while(1){var _9m=(function(_9n,_9o){var _9p=E(_9n);switch(_9p._){case 0:var _9q=E(_9o);if(!_9q._){return __Z;}else{_9k=B(A1(_9p.a,_9q.a));_9l=_9q.b;return __continue;}break;case 1:var _9r=B(A1(_9p.a,_9o)),_9s=_9o;_9k=_9r;_9l=_9s;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_9p.a,_9o),new T(function(){return _9j(_9p.b,_9o);}));default:return E(_9p.a);}})(_9k,_9l);if(_9m!=__continue){return _9m;}}},_9t=function(_9u,_9v){var _9w=function(_9x){var _9y=E(_9v);if(_9y._==3){return new T2(3,_9y.a,new T(function(){return _9t(_9u,_9y.b);}));}else{var _9z=E(_9u);if(_9z._==2){return _9y;}else{if(_9y._==2){return _9z;}else{var _9A=function(_9B){if(_9y._==4){var _9C=function(_9D){return new T1(4,new T(function(){return _0(_9j(_9z,_9D),_9y.a);}));};return new T1(1,_9C);}else{if(_9z._==1){var _9E=_9z.a;if(!_9y._){return new T1(1,function(_9F){return _9t(B(A1(_9E,_9F)),_9y);});}else{var _9G=function(_9H){return _9t(B(A1(_9E,_9H)),new T(function(){return B(A1(_9y.a,_9H));}));};return new T1(1,_9G);}}else{if(!_9y._){return E(_9i);}else{var _9I=function(_9J){return _9t(_9z,new T(function(){return B(A1(_9y.a,_9J));}));};return new T1(1,_9I);}}}};switch(_9z._){case 1:if(_9y._==4){var _9K=function(_9L){return new T1(4,new T(function(){return _0(_9j(B(A1(_9z.a,_9L)),_9L),_9y.a);}));};return new T1(1,_9K);}else{return _9A(_);}break;case 4:var _9M=_9z.a;switch(_9y._){case 0:var _9N=function(_9O){var _9P=new T(function(){return _0(_9M,new T(function(){return _9j(_9y,_9O);},1));});return new T1(4,_9P);};return new T1(1,_9N);case 1:var _9Q=function(_9R){var _9S=new T(function(){return _0(_9M,new T(function(){return _9j(B(A1(_9y.a,_9R)),_9R);},1));});return new T1(4,_9S);};return new T1(1,_9Q);default:return new T1(4,new T(function(){return _0(_9M,_9y.a);}));}break;default:return _9A(_);}}}}},_9T=E(_9u);switch(_9T._){case 0:var _9U=E(_9v);if(!_9U._){var _9V=function(_9W){return _9t(B(A1(_9T.a,_9W)),new T(function(){return B(A1(_9U.a,_9W));}));};return new T1(0,_9V);}else{return _9w(_);}break;case 3:return new T2(3,_9T.a,new T(function(){return _9t(_9T.b,_9v);}));default:return _9w(_);}},_9X=new T(function(){return unCStr("(");}),_9Y=new T(function(){return unCStr(")");}),_9Z=function(_a0,_a1){while(1){var _a2=E(_a0);if(!_a2._){return (E(_a1)._==0)?true:false;}else{var _a3=E(_a1);if(!_a3._){return false;}else{if(E(_a2.a)!=E(_a3.a)){return false;}else{_a0=_a2.b;_a1=_a3.b;continue;}}}}},_a4=new T2(0,function(_a5,_a6){return E(_a5)==E(_a6);},function(_a7,_a8){return E(_a7)!=E(_a8);}),_a9=function(_aa,_ab){while(1){var _ac=E(_aa);if(!_ac._){return (E(_ab)._==0)?true:false;}else{var _ad=E(_ab);if(!_ad._){return false;}else{if(E(_ac.a)!=E(_ad.a)){return false;}else{_aa=_ac.b;_ab=_ad.b;continue;}}}}},_ae=function(_af,_ag){return (!_a9(_af,_ag))?true:false;},_ah=function(_ai,_aj){var _ak=E(_ai);switch(_ak._){case 0:return new T1(0,function(_al){return C > 19 ? new F(function(){return _ah(B(A1(_ak.a,_al)),_aj);}) : (++C,_ah(B(A1(_ak.a,_al)),_aj));});case 1:return new T1(1,function(_am){return C > 19 ? new F(function(){return _ah(B(A1(_ak.a,_am)),_aj);}) : (++C,_ah(B(A1(_ak.a,_am)),_aj));});case 2:return new T0(2);case 3:return _9t(B(A1(_aj,_ak.a)),new T(function(){return B(_ah(_ak.b,_aj));}));default:var _an=function(_ao){var _ap=E(_ao);if(!_ap._){return __Z;}else{var _aq=E(_ap.a);return _0(_9j(B(A1(_aj,_aq.a)),_aq.b),new T(function(){return _an(_ap.b);},1));}},_ar=_an(_ak.a);return (_ar._==0)?new T0(2):new T1(4,_ar);}},_as=new T0(2),_at=function(_au){return new T2(3,_au,_as);},_av=function(_aw,_ax){var _ay=E(_aw);if(!_ay){return C > 19 ? new F(function(){return A1(_ax,0);}) : (++C,A1(_ax,0));}else{var _az=new T(function(){return B(_av(_ay-1|0,_ax));});return new T1(0,function(_aA){return E(_az);});}},_aB=function(_aC,_aD,_aE){var _aF=new T(function(){return B(A1(_aC,_at));}),_aG=function(_aH,_aI,_aJ,_aK){while(1){var _aL=B((function(_aM,_aN,_aO,_aP){var _aQ=E(_aM);switch(_aQ._){case 0:var _aR=E(_aN);if(!_aR._){return C > 19 ? new F(function(){return A1(_aD,_aP);}) : (++C,A1(_aD,_aP));}else{var _aS=_aO+1|0,_aT=_aP;_aH=B(A1(_aQ.a,_aR.a));_aI=_aR.b;_aJ=_aS;_aK=_aT;return __continue;}break;case 1:var _aU=B(A1(_aQ.a,_aN)),_aV=_aN,_aS=_aO,_aT=_aP;_aH=_aU;_aI=_aV;_aJ=_aS;_aK=_aT;return __continue;case 2:return C > 19 ? new F(function(){return A1(_aD,_aP);}) : (++C,A1(_aD,_aP));break;case 3:var _aW=new T(function(){return B(_ah(_aQ,_aP));});return C > 19 ? new F(function(){return _av(_aO,function(_aX){return E(_aW);});}) : (++C,_av(_aO,function(_aX){return E(_aW);}));break;default:return C > 19 ? new F(function(){return _ah(_aQ,_aP);}) : (++C,_ah(_aQ,_aP));}})(_aH,_aI,_aJ,_aK));if(_aL!=__continue){return _aL;}}};return function(_aY){return _aG(_aF,_aY,0,_aE);};},_aZ=function(_b0){return C > 19 ? new F(function(){return A1(_b0,__Z);}) : (++C,A1(_b0,__Z));},_b1=function(_b2,_b3){var _b4=function(_b5){var _b6=E(_b5);if(!_b6._){return _aZ;}else{var _b7=_b6.a;if(!B(A1(_b2,_b7))){return _aZ;}else{var _b8=new T(function(){return _b4(_b6.b);}),_b9=function(_ba){var _bb=new T(function(){return B(A1(_b8,function(_bc){return C > 19 ? new F(function(){return A1(_ba,new T2(1,_b7,_bc));}) : (++C,A1(_ba,new T2(1,_b7,_bc)));}));});return new T1(0,function(_bd){return E(_bb);});};return _b9;}}};return function(_be){return C > 19 ? new F(function(){return A2(_b4,_be,_b3);}) : (++C,A2(_b4,_be,_b3));};},_bf=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_bg=function(_bh,_bi){var _bj=function(_bk,_bl){var _bm=E(_bk);if(!_bm._){var _bn=new T(function(){return B(A1(_bl,__Z));});return function(_bo){return C > 19 ? new F(function(){return A1(_bo,_bn);}) : (++C,A1(_bo,_bn));};}else{var _bp=E(_bm.a),_bq=function(_br){var _bs=new T(function(){return _bj(_bm.b,function(_bt){return C > 19 ? new F(function(){return A1(_bl,new T2(1,_br,_bt));}) : (++C,A1(_bl,new T2(1,_br,_bt)));});}),_bu=function(_bv){var _bw=new T(function(){return B(A1(_bs,_bv));});return new T1(0,function(_bx){return E(_bw);});};return _bu;};switch(E(_bh)){case 8:if(48>_bp){var _by=new T(function(){return B(A1(_bl,__Z));});return function(_bz){return C > 19 ? new F(function(){return A1(_bz,_by);}) : (++C,A1(_bz,_by));};}else{if(_bp>55){var _bA=new T(function(){return B(A1(_bl,__Z));});return function(_bB){return C > 19 ? new F(function(){return A1(_bB,_bA);}) : (++C,A1(_bB,_bA));};}else{return _bq(_bp-48|0);}}break;case 10:if(48>_bp){var _bC=new T(function(){return B(A1(_bl,__Z));});return function(_bD){return C > 19 ? new F(function(){return A1(_bD,_bC);}) : (++C,A1(_bD,_bC));};}else{if(_bp>57){var _bE=new T(function(){return B(A1(_bl,__Z));});return function(_bF){return C > 19 ? new F(function(){return A1(_bF,_bE);}) : (++C,A1(_bF,_bE));};}else{return _bq(_bp-48|0);}}break;case 16:if(48>_bp){if(97>_bp){if(65>_bp){var _bG=new T(function(){return B(A1(_bl,__Z));});return function(_bH){return C > 19 ? new F(function(){return A1(_bH,_bG);}) : (++C,A1(_bH,_bG));};}else{if(_bp>70){var _bI=new T(function(){return B(A1(_bl,__Z));});return function(_bJ){return C > 19 ? new F(function(){return A1(_bJ,_bI);}) : (++C,A1(_bJ,_bI));};}else{return _bq((_bp-65|0)+10|0);}}}else{if(_bp>102){if(65>_bp){var _bK=new T(function(){return B(A1(_bl,__Z));});return function(_bL){return C > 19 ? new F(function(){return A1(_bL,_bK);}) : (++C,A1(_bL,_bK));};}else{if(_bp>70){var _bM=new T(function(){return B(A1(_bl,__Z));});return function(_bN){return C > 19 ? new F(function(){return A1(_bN,_bM);}) : (++C,A1(_bN,_bM));};}else{return _bq((_bp-65|0)+10|0);}}}else{return _bq((_bp-97|0)+10|0);}}}else{if(_bp>57){if(97>_bp){if(65>_bp){var _bO=new T(function(){return B(A1(_bl,__Z));});return function(_bP){return C > 19 ? new F(function(){return A1(_bP,_bO);}) : (++C,A1(_bP,_bO));};}else{if(_bp>70){var _bQ=new T(function(){return B(A1(_bl,__Z));});return function(_bR){return C > 19 ? new F(function(){return A1(_bR,_bQ);}) : (++C,A1(_bR,_bQ));};}else{return _bq((_bp-65|0)+10|0);}}}else{if(_bp>102){if(65>_bp){var _bS=new T(function(){return B(A1(_bl,__Z));});return function(_bT){return C > 19 ? new F(function(){return A1(_bT,_bS);}) : (++C,A1(_bT,_bS));};}else{if(_bp>70){var _bU=new T(function(){return B(A1(_bl,__Z));});return function(_bV){return C > 19 ? new F(function(){return A1(_bV,_bU);}) : (++C,A1(_bV,_bU));};}else{return _bq((_bp-65|0)+10|0);}}}else{return _bq((_bp-97|0)+10|0);}}}else{return _bq(_bp-48|0);}}break;default:return E(_bf);}}},_bW=function(_bX){var _bY=E(_bX);if(!_bY._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_bi,_bY);}) : (++C,A1(_bi,_bY));}};return function(_bZ){return C > 19 ? new F(function(){return A3(_bj,_bZ,_37,_bW);}) : (++C,A3(_bj,_bZ,_37,_bW));};},_c0=function(_c1){var _c2=function(_c3){return C > 19 ? new F(function(){return A1(_c1,new T1(5,new T2(0,8,_c3)));}) : (++C,A1(_c1,new T1(5,new T2(0,8,_c3))));},_c4=function(_c5){return C > 19 ? new F(function(){return A1(_c1,new T1(5,new T2(0,16,_c5)));}) : (++C,A1(_c1,new T1(5,new T2(0,16,_c5))));},_c6=function(_c7){switch(E(_c7)){case 79:return new T1(1,_bg(8,_c2));case 88:return new T1(1,_bg(16,_c4));case 111:return new T1(1,_bg(8,_c2));case 120:return new T1(1,_bg(16,_c4));default:return new T0(2);}};return function(_c8){return (E(_c8)==48)?E(new T1(0,_c6)):new T0(2);};},_c9=function(_ca){return new T1(0,_c0(_ca));},_cb=function(_cc){return C > 19 ? new F(function(){return A1(_cc,__Z);}) : (++C,A1(_cc,__Z));},_cd=function(_ce){return C > 19 ? new F(function(){return A1(_ce,__Z);}) : (++C,A1(_ce,__Z));},_cf=function(_cg,_ch){while(1){var _ci=E(_cg);if(!_ci._){var _cj=_ci.a,_ck=E(_ch);if(!_ck._){var _cl=_ck.a,_cm=addC(_cj,_cl);if(!E(_cm.b)){return new T1(0,_cm.a);}else{_cg=new T1(1,I_fromInt(_cj));_ch=new T1(1,I_fromInt(_cl));continue;}}else{_cg=new T1(1,I_fromInt(_cj));_ch=_ck;continue;}}else{var _cn=E(_ch);if(!_cn._){_cg=_ci;_ch=new T1(1,I_fromInt(_cn.a));continue;}else{return new T1(1,I_add(_ci.a,_cn.a));}}}},_co=new T(function(){return _cf(new T1(0,2147483647),new T1(0,1));}),_cp=function(_cq){var _cr=E(_cq);if(!_cr._){var _cs=E(_cr.a);return (_cs==(-2147483648))?E(_co):new T1(0, -_cs);}else{return new T1(1,I_negate(_cr.a));}},_ct=new T1(0,10),_cu=function(_cv,_cw){while(1){var _cx=E(_cv);if(!_cx._){return E(_cw);}else{var _cy=_cw+1|0;_cv=_cx.b;_cw=_cy;continue;}}},_cz=function(_cA,_cB){var _cC=E(_cB);return (_cC._==0)?__Z:new T2(1,new T(function(){return B(A1(_cA,_cC.a));}),new T(function(){return _cz(_cA,_cC.b);}));},_cD=function(_cE){return new T1(0,_cE);},_cF=function(_cG){return _cD(E(_cG));},_cH=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_cI=function(_cJ,_cK){while(1){var _cL=E(_cJ);if(!_cL._){var _cM=_cL.a,_cN=E(_cK);if(!_cN._){var _cO=_cN.a;if(!(imul(_cM,_cO)|0)){return new T1(0,imul(_cM,_cO)|0);}else{_cJ=new T1(1,I_fromInt(_cM));_cK=new T1(1,I_fromInt(_cO));continue;}}else{_cJ=new T1(1,I_fromInt(_cM));_cK=_cN;continue;}}else{var _cP=E(_cK);if(!_cP._){_cJ=_cL;_cK=new T1(1,I_fromInt(_cP.a));continue;}else{return new T1(1,I_mul(_cL.a,_cP.a));}}}},_cQ=function(_cR,_cS){var _cT=E(_cS);if(!_cT._){return __Z;}else{var _cU=E(_cT.b);return (_cU._==0)?E(_cH):new T2(1,_cf(_cI(_cT.a,_cR),_cU.a),new T(function(){return _cQ(_cR,_cU.b);}));}},_cV=new T1(0,0),_cW=function(_cX,_cY,_cZ){while(1){var _d0=(function(_d1,_d2,_d3){var _d4=E(_d3);if(!_d4._){return E(_cV);}else{if(!E(_d4.b)._){return E(_d4.a);}else{var _d5=E(_d2);if(_d5<=40){var _d6=function(_d7,_d8){while(1){var _d9=E(_d8);if(!_d9._){return E(_d7);}else{var _da=_cf(_cI(_d7,_d1),_d9.a);_d7=_da;_d8=_d9.b;continue;}}};return _d6(_cV,_d4);}else{var _db=_cI(_d1,_d1);if(!(_d5%2)){var _dc=_cQ(_d1,_d4);_cX=_db;_cY=quot(_d5+1|0,2);_cZ=_dc;return __continue;}else{var _dc=_cQ(_d1,new T2(1,_cV,_d4));_cX=_db;_cY=quot(_d5+1|0,2);_cZ=_dc;return __continue;}}}}})(_cX,_cY,_cZ);if(_d0!=__continue){return _d0;}}},_dd=function(_de,_df){return _cW(_de,new T(function(){return _cu(_df,0);},1),_cz(_cF,_df));},_dg=function(_dh){var _di=new T(function(){var _dj=new T(function(){var _dk=function(_dl){return C > 19 ? new F(function(){return A1(_dh,new T1(1,new T(function(){return _dd(_ct,_dl);})));}) : (++C,A1(_dh,new T1(1,new T(function(){return _dd(_ct,_dl);}))));};return new T1(1,_bg(10,_dk));}),_dm=function(_dn){if(E(_dn)==43){var _do=function(_dp){return C > 19 ? new F(function(){return A1(_dh,new T1(1,new T(function(){return _dd(_ct,_dp);})));}) : (++C,A1(_dh,new T1(1,new T(function(){return _dd(_ct,_dp);}))));};return new T1(1,_bg(10,_do));}else{return new T0(2);}},_dq=function(_dr){if(E(_dr)==45){var _ds=function(_dt){return C > 19 ? new F(function(){return A1(_dh,new T1(1,new T(function(){return _cp(_dd(_ct,_dt));})));}) : (++C,A1(_dh,new T1(1,new T(function(){return _cp(_dd(_ct,_dt));}))));};return new T1(1,_bg(10,_ds));}else{return new T0(2);}};return _9t(_9t(new T1(0,_dq),new T1(0,_dm)),_dj);});return _9t(new T1(0,function(_du){return (E(_du)==101)?E(_di):new T0(2);}),new T1(0,function(_dv){return (E(_dv)==69)?E(_di):new T0(2);}));},_dw=function(_dx){var _dy=function(_dz){return C > 19 ? new F(function(){return A1(_dx,new T1(1,_dz));}) : (++C,A1(_dx,new T1(1,_dz)));};return function(_dA){return (E(_dA)==46)?new T1(1,_bg(10,_dy)):new T0(2);};},_dB=function(_dC){return new T1(0,_dw(_dC));},_dD=function(_dE){var _dF=function(_dG){var _dH=function(_dI){return new T1(1,_aB(_dg,_cb,function(_dJ){return C > 19 ? new F(function(){return A1(_dE,new T1(5,new T3(1,_dG,_dI,_dJ)));}) : (++C,A1(_dE,new T1(5,new T3(1,_dG,_dI,_dJ))));}));};return new T1(1,_aB(_dB,_cd,_dH));};return _bg(10,_dF);},_dK=function(_dL){return new T1(1,_dD(_dL));},_dM=function(_dN){return E(E(_dN).a);},_dO=function(_dP,_dQ,_dR){while(1){var _dS=E(_dR);if(!_dS._){return false;}else{if(!B(A3(_dM,_dP,_dQ,_dS.a))){_dR=_dS.b;continue;}else{return true;}}}},_dT=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_dU=function(_dV){return _dO(_a4,_dV,_dT);},_dW=function(_dX){var _dY=new T(function(){return B(A1(_dX,8));}),_dZ=new T(function(){return B(A1(_dX,16));});return function(_e0){switch(E(_e0)){case 79:return E(_dY);case 88:return E(_dZ);case 111:return E(_dY);case 120:return E(_dZ);default:return new T0(2);}};},_e1=function(_e2){return new T1(0,_dW(_e2));},_e3=function(_e4){return C > 19 ? new F(function(){return A1(_e4,10);}) : (++C,A1(_e4,10));},_e5=function(_e6){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _8(9,_e6,__Z);})));},_e7=function(_e8){var _e9=E(_e8);if(!_e9._){return E(_e9.a);}else{return I_toInt(_e9.a);}},_ea=function(_eb,_ec){var _ed=E(_eb);if(!_ed._){var _ee=_ed.a,_ef=E(_ec);return (_ef._==0)?_ee<=_ef.a:I_compareInt(_ef.a,_ee)>=0;}else{var _eg=_ed.a,_eh=E(_ec);return (_eh._==0)?I_compareInt(_eg,_eh.a)<=0:I_compare(_eg,_eh.a)<=0;}},_ei=function(_ej){return new T0(2);},_ek=function(_el){var _em=E(_el);if(!_em._){return _ei;}else{var _en=_em.a,_eo=E(_em.b);if(!_eo._){return E(_en);}else{var _ep=new T(function(){return _ek(_eo);}),_eq=function(_er){return _9t(B(A1(_en,_er)),new T(function(){return B(A1(_ep,_er));}));};return _eq;}}},_es=function(_et,_eu){var _ev=function(_ew,_ex,_ey){var _ez=E(_ew);if(!_ez._){return C > 19 ? new F(function(){return A1(_ey,_et);}) : (++C,A1(_ey,_et));}else{var _eA=E(_ex);if(!_eA._){return new T0(2);}else{if(E(_ez.a)!=E(_eA.a)){return new T0(2);}else{var _eB=new T(function(){return B(_ev(_ez.b,_eA.b,_ey));});return new T1(0,function(_eC){return E(_eB);});}}}};return function(_eD){return C > 19 ? new F(function(){return _ev(_et,_eD,_eu);}) : (++C,_ev(_et,_eD,_eu));};},_eE=new T(function(){return unCStr("SO");}),_eF=function(_eG){var _eH=new T(function(){return B(A1(_eG,14));});return new T1(1,_es(_eE,function(_eI){return E(_eH);}));},_eJ=new T(function(){return unCStr("SOH");}),_eK=function(_eL){var _eM=new T(function(){return B(A1(_eL,1));});return new T1(1,_es(_eJ,function(_eN){return E(_eM);}));},_eO=new T(function(){return unCStr("NUL");}),_eP=function(_eQ){var _eR=new T(function(){return B(A1(_eQ,0));});return new T1(1,_es(_eO,function(_eS){return E(_eR);}));},_eT=new T(function(){return unCStr("STX");}),_eU=function(_eV){var _eW=new T(function(){return B(A1(_eV,2));});return new T1(1,_es(_eT,function(_eX){return E(_eW);}));},_eY=new T(function(){return unCStr("ETX");}),_eZ=function(_f0){var _f1=new T(function(){return B(A1(_f0,3));});return new T1(1,_es(_eY,function(_f2){return E(_f1);}));},_f3=new T(function(){return unCStr("EOT");}),_f4=function(_f5){var _f6=new T(function(){return B(A1(_f5,4));});return new T1(1,_es(_f3,function(_f7){return E(_f6);}));},_f8=new T(function(){return unCStr("ENQ");}),_f9=function(_fa){var _fb=new T(function(){return B(A1(_fa,5));});return new T1(1,_es(_f8,function(_fc){return E(_fb);}));},_fd=new T(function(){return unCStr("ACK");}),_fe=function(_ff){var _fg=new T(function(){return B(A1(_ff,6));});return new T1(1,_es(_fd,function(_fh){return E(_fg);}));},_fi=new T(function(){return unCStr("BEL");}),_fj=function(_fk){var _fl=new T(function(){return B(A1(_fk,7));});return new T1(1,_es(_fi,function(_fm){return E(_fl);}));},_fn=new T(function(){return unCStr("BS");}),_fo=function(_fp){var _fq=new T(function(){return B(A1(_fp,8));});return new T1(1,_es(_fn,function(_fr){return E(_fq);}));},_fs=new T(function(){return unCStr("HT");}),_ft=function(_fu){var _fv=new T(function(){return B(A1(_fu,9));});return new T1(1,_es(_fs,function(_fw){return E(_fv);}));},_fx=new T(function(){return unCStr("LF");}),_fy=function(_fz){var _fA=new T(function(){return B(A1(_fz,10));});return new T1(1,_es(_fx,function(_fB){return E(_fA);}));},_fC=new T(function(){return unCStr("VT");}),_fD=function(_fE){var _fF=new T(function(){return B(A1(_fE,11));});return new T1(1,_es(_fC,function(_fG){return E(_fF);}));},_fH=new T(function(){return unCStr("FF");}),_fI=function(_fJ){var _fK=new T(function(){return B(A1(_fJ,12));});return new T1(1,_es(_fH,function(_fL){return E(_fK);}));},_fM=new T(function(){return unCStr("CR");}),_fN=function(_fO){var _fP=new T(function(){return B(A1(_fO,13));});return new T1(1,_es(_fM,function(_fQ){return E(_fP);}));},_fR=new T(function(){return unCStr("SI");}),_fS=function(_fT){var _fU=new T(function(){return B(A1(_fT,15));});return new T1(1,_es(_fR,function(_fV){return E(_fU);}));},_fW=new T(function(){return unCStr("DLE");}),_fX=function(_fY){var _fZ=new T(function(){return B(A1(_fY,16));});return new T1(1,_es(_fW,function(_g0){return E(_fZ);}));},_g1=new T(function(){return unCStr("DC1");}),_g2=function(_g3){var _g4=new T(function(){return B(A1(_g3,17));});return new T1(1,_es(_g1,function(_g5){return E(_g4);}));},_g6=new T(function(){return unCStr("DC2");}),_g7=function(_g8){var _g9=new T(function(){return B(A1(_g8,18));});return new T1(1,_es(_g6,function(_ga){return E(_g9);}));},_gb=new T(function(){return unCStr("DC3");}),_gc=function(_gd){var _ge=new T(function(){return B(A1(_gd,19));});return new T1(1,_es(_gb,function(_gf){return E(_ge);}));},_gg=new T(function(){return unCStr("DC4");}),_gh=function(_gi){var _gj=new T(function(){return B(A1(_gi,20));});return new T1(1,_es(_gg,function(_gk){return E(_gj);}));},_gl=new T(function(){return unCStr("NAK");}),_gm=function(_gn){var _go=new T(function(){return B(A1(_gn,21));});return new T1(1,_es(_gl,function(_gp){return E(_go);}));},_gq=new T(function(){return unCStr("SYN");}),_gr=function(_gs){var _gt=new T(function(){return B(A1(_gs,22));});return new T1(1,_es(_gq,function(_gu){return E(_gt);}));},_gv=new T(function(){return unCStr("ETB");}),_gw=function(_gx){var _gy=new T(function(){return B(A1(_gx,23));});return new T1(1,_es(_gv,function(_gz){return E(_gy);}));},_gA=new T(function(){return unCStr("CAN");}),_gB=function(_gC){var _gD=new T(function(){return B(A1(_gC,24));});return new T1(1,_es(_gA,function(_gE){return E(_gD);}));},_gF=new T(function(){return unCStr("EM");}),_gG=function(_gH){var _gI=new T(function(){return B(A1(_gH,25));});return new T1(1,_es(_gF,function(_gJ){return E(_gI);}));},_gK=new T(function(){return unCStr("SUB");}),_gL=function(_gM){var _gN=new T(function(){return B(A1(_gM,26));});return new T1(1,_es(_gK,function(_gO){return E(_gN);}));},_gP=new T(function(){return unCStr("ESC");}),_gQ=function(_gR){var _gS=new T(function(){return B(A1(_gR,27));});return new T1(1,_es(_gP,function(_gT){return E(_gS);}));},_gU=new T(function(){return unCStr("FS");}),_gV=function(_gW){var _gX=new T(function(){return B(A1(_gW,28));});return new T1(1,_es(_gU,function(_gY){return E(_gX);}));},_gZ=new T(function(){return unCStr("GS");}),_h0=function(_h1){var _h2=new T(function(){return B(A1(_h1,29));});return new T1(1,_es(_gZ,function(_h3){return E(_h2);}));},_h4=new T(function(){return unCStr("RS");}),_h5=function(_h6){var _h7=new T(function(){return B(A1(_h6,30));});return new T1(1,_es(_h4,function(_h8){return E(_h7);}));},_h9=new T(function(){return unCStr("US");}),_ha=function(_hb){var _hc=new T(function(){return B(A1(_hb,31));});return new T1(1,_es(_h9,function(_hd){return E(_hc);}));},_he=new T(function(){return unCStr("SP");}),_hf=function(_hg){var _hh=new T(function(){return B(A1(_hg,32));});return new T1(1,_es(_he,function(_hi){return E(_hh);}));},_hj=new T(function(){return unCStr("DEL");}),_hk=function(_hl){var _hm=new T(function(){return B(A1(_hl,127));});return new T1(1,_es(_hj,function(_hn){return E(_hm);}));},_ho=new T(function(){return _ek(new T2(1,function(_hp){return new T1(1,_aB(_eK,_eF,_hp));},new T2(1,_eP,new T2(1,_eU,new T2(1,_eZ,new T2(1,_f4,new T2(1,_f9,new T2(1,_fe,new T2(1,_fj,new T2(1,_fo,new T2(1,_ft,new T2(1,_fy,new T2(1,_fD,new T2(1,_fI,new T2(1,_fN,new T2(1,_fS,new T2(1,_fX,new T2(1,_g2,new T2(1,_g7,new T2(1,_gc,new T2(1,_gh,new T2(1,_gm,new T2(1,_gr,new T2(1,_gw,new T2(1,_gB,new T2(1,_gG,new T2(1,_gL,new T2(1,_gQ,new T2(1,_gV,new T2(1,_h0,new T2(1,_h5,new T2(1,_ha,new T2(1,_hf,new T2(1,_hk,__Z))))))))))))))))))))))))))))))))));}),_hq=function(_hr){var _hs=new T(function(){return B(A1(_hr,7));}),_ht=new T(function(){return B(A1(_hr,8));}),_hu=new T(function(){return B(A1(_hr,9));}),_hv=new T(function(){return B(A1(_hr,10));}),_hw=new T(function(){return B(A1(_hr,11));}),_hx=new T(function(){return B(A1(_hr,12));}),_hy=new T(function(){return B(A1(_hr,13));}),_hz=new T(function(){return B(A1(_hr,92));}),_hA=new T(function(){return B(A1(_hr,39));}),_hB=new T(function(){return B(A1(_hr,34));}),_hC=new T(function(){var _hD=function(_hE){var _hF=new T(function(){return _cD(E(_hE));}),_hG=function(_hH){var _hI=_dd(_hF,_hH);if(!_ea(_hI,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_hr,new T(function(){var _hJ=_e7(_hI);if(_hJ>>>0>1114111){return _e5(_hJ);}else{return _hJ;}}));}) : (++C,A1(_hr,new T(function(){var _hJ=_e7(_hI);if(_hJ>>>0>1114111){return _e5(_hJ);}else{return _hJ;}})));}};return new T1(1,_bg(_hE,_hG));},_hK=new T(function(){var _hL=new T(function(){return B(A1(_hr,31));}),_hM=new T(function(){return B(A1(_hr,30));}),_hN=new T(function(){return B(A1(_hr,29));}),_hO=new T(function(){return B(A1(_hr,28));}),_hP=new T(function(){return B(A1(_hr,27));}),_hQ=new T(function(){return B(A1(_hr,26));}),_hR=new T(function(){return B(A1(_hr,25));}),_hS=new T(function(){return B(A1(_hr,24));}),_hT=new T(function(){return B(A1(_hr,23));}),_hU=new T(function(){return B(A1(_hr,22));}),_hV=new T(function(){return B(A1(_hr,21));}),_hW=new T(function(){return B(A1(_hr,20));}),_hX=new T(function(){return B(A1(_hr,19));}),_hY=new T(function(){return B(A1(_hr,18));}),_hZ=new T(function(){return B(A1(_hr,17));}),_i0=new T(function(){return B(A1(_hr,16));}),_i1=new T(function(){return B(A1(_hr,15));}),_i2=new T(function(){return B(A1(_hr,14));}),_i3=new T(function(){return B(A1(_hr,6));}),_i4=new T(function(){return B(A1(_hr,5));}),_i5=new T(function(){return B(A1(_hr,4));}),_i6=new T(function(){return B(A1(_hr,3));}),_i7=new T(function(){return B(A1(_hr,2));}),_i8=new T(function(){return B(A1(_hr,1));}),_i9=new T(function(){return B(A1(_hr,0));}),_ia=function(_ib){switch(E(_ib)){case 64:return E(_i9);case 65:return E(_i8);case 66:return E(_i7);case 67:return E(_i6);case 68:return E(_i5);case 69:return E(_i4);case 70:return E(_i3);case 71:return E(_hs);case 72:return E(_ht);case 73:return E(_hu);case 74:return E(_hv);case 75:return E(_hw);case 76:return E(_hx);case 77:return E(_hy);case 78:return E(_i2);case 79:return E(_i1);case 80:return E(_i0);case 81:return E(_hZ);case 82:return E(_hY);case 83:return E(_hX);case 84:return E(_hW);case 85:return E(_hV);case 86:return E(_hU);case 87:return E(_hT);case 88:return E(_hS);case 89:return E(_hR);case 90:return E(_hQ);case 91:return E(_hP);case 92:return E(_hO);case 93:return E(_hN);case 94:return E(_hM);case 95:return E(_hL);default:return new T0(2);}};return _9t(new T1(0,function(_ic){return (E(_ic)==94)?E(new T1(0,_ia)):new T0(2);}),new T(function(){return B(A1(_ho,_hr));}));});return _9t(new T1(1,_aB(_e1,_e3,_hD)),_hK);});return _9t(new T1(0,function(_id){switch(E(_id)){case 34:return E(_hB);case 39:return E(_hA);case 92:return E(_hz);case 97:return E(_hs);case 98:return E(_ht);case 102:return E(_hx);case 110:return E(_hv);case 114:return E(_hy);case 116:return E(_hu);case 118:return E(_hw);default:return new T0(2);}}),_hC);},_ie=function(_if){return C > 19 ? new F(function(){return A1(_if,0);}) : (++C,A1(_if,0));},_ig=function(_ih){var _ii=E(_ih);if(!_ii._){return _ie;}else{var _ij=E(_ii.a),_ik=_ij>>>0,_il=new T(function(){return _ig(_ii.b);});if(_ik>887){var _im=u_iswspace(_ij);if(!E(_im)){return _ie;}else{var _in=function(_io){var _ip=new T(function(){return B(A1(_il,_io));});return new T1(0,function(_iq){return E(_ip);});};return _in;}}else{if(_ik==32){var _ir=function(_is){var _it=new T(function(){return B(A1(_il,_is));});return new T1(0,function(_iu){return E(_it);});};return _ir;}else{if(_ik-9>>>0>4){if(_ik==160){var _iv=function(_iw){var _ix=new T(function(){return B(A1(_il,_iw));});return new T1(0,function(_iy){return E(_ix);});};return _iv;}else{return _ie;}}else{var _iz=function(_iA){var _iB=new T(function(){return B(A1(_il,_iA));});return new T1(0,function(_iC){return E(_iB);});};return _iz;}}}}},_iD=function(_iE){var _iF=new T(function(){return B(_iD(_iE));}),_iG=function(_iH){return (E(_iH)==92)?E(_iF):new T0(2);},_iI=function(_iJ){return E(new T1(0,_iG));},_iK=new T1(1,function(_iL){return C > 19 ? new F(function(){return A2(_ig,_iL,_iI);}) : (++C,A2(_ig,_iL,_iI));}),_iM=new T(function(){return B(_hq(function(_iN){return C > 19 ? new F(function(){return A1(_iE,new T2(0,_iN,true));}) : (++C,A1(_iE,new T2(0,_iN,true)));}));}),_iO=function(_iP){var _iQ=E(_iP);if(_iQ==38){return E(_iF);}else{var _iR=_iQ>>>0;if(_iR>887){var _iS=u_iswspace(_iQ);return (E(_iS)==0)?new T0(2):E(_iK);}else{return (_iR==32)?E(_iK):(_iR-9>>>0>4)?(_iR==160)?E(_iK):new T0(2):E(_iK);}}};return _9t(new T1(0,function(_iT){return (E(_iT)==92)?E(new T1(0,_iO)):new T0(2);}),new T1(0,function(_iU){var _iV=E(_iU);if(_iV==92){return E(_iM);}else{return C > 19 ? new F(function(){return A1(_iE,new T2(0,_iV,false));}) : (++C,A1(_iE,new T2(0,_iV,false)));}}));},_iW=function(_iX,_iY){var _iZ=new T(function(){return B(A1(_iY,new T1(1,new T(function(){return B(A1(_iX,__Z));}))));}),_j0=function(_j1){var _j2=E(_j1),_j3=E(_j2.a);if(_j3==34){if(!E(_j2.b)){return E(_iZ);}else{return C > 19 ? new F(function(){return _iW(function(_j4){return C > 19 ? new F(function(){return A1(_iX,new T2(1,_j3,_j4));}) : (++C,A1(_iX,new T2(1,_j3,_j4)));},_iY);}) : (++C,_iW(function(_j4){return C > 19 ? new F(function(){return A1(_iX,new T2(1,_j3,_j4));}) : (++C,A1(_iX,new T2(1,_j3,_j4)));},_iY));}}else{return C > 19 ? new F(function(){return _iW(function(_j5){return C > 19 ? new F(function(){return A1(_iX,new T2(1,_j3,_j5));}) : (++C,A1(_iX,new T2(1,_j3,_j5)));},_iY);}) : (++C,_iW(function(_j5){return C > 19 ? new F(function(){return A1(_iX,new T2(1,_j3,_j5));}) : (++C,A1(_iX,new T2(1,_j3,_j5)));},_iY));}};return C > 19 ? new F(function(){return _iD(_j0);}) : (++C,_iD(_j0));},_j6=new T(function(){return unCStr("_\'");}),_j7=function(_j8){var _j9=u_iswalnum(_j8);if(!E(_j9)){return _dO(_a4,_j8,_j6);}else{return true;}},_ja=function(_jb){return _j7(E(_jb));},_jc=new T(function(){return unCStr(",;()[]{}`");}),_jd=new T(function(){return unCStr("=>");}),_je=new T(function(){return unCStr("~");}),_jf=new T(function(){return unCStr("@");}),_jg=new T(function(){return unCStr("->");}),_jh=new T(function(){return unCStr("<-");}),_ji=new T(function(){return unCStr("|");}),_jj=new T(function(){return unCStr("\\");}),_jk=new T(function(){return unCStr("=");}),_jl=new T(function(){return unCStr("::");}),_jm=new T(function(){return unCStr("..");}),_jn=function(_jo){var _jp=new T(function(){return B(A1(_jo,new T0(6)));}),_jq=new T(function(){var _jr=new T(function(){var _js=function(_jt){var _ju=new T(function(){return B(A1(_jo,new T1(0,_jt)));});return new T1(0,function(_jv){return (E(_jv)==39)?E(_ju):new T0(2);});};return B(_hq(_js));}),_jw=function(_jx){var _jy=E(_jx);switch(_jy){case 39:return new T0(2);case 92:return E(_jr);default:var _jz=new T(function(){return B(A1(_jo,new T1(0,_jy)));});return new T1(0,function(_jA){return (E(_jA)==39)?E(_jz):new T0(2);});}},_jB=new T(function(){var _jC=new T(function(){return B(_iW(_37,_jo));}),_jD=new T(function(){var _jE=new T(function(){var _jF=new T(function(){var _jG=function(_jH){var _jI=E(_jH),_jJ=u_iswalpha(_jI);return (E(_jJ)==0)?(_jI==95)?new T1(1,_b1(_ja,function(_jK){return C > 19 ? new F(function(){return A1(_jo,new T1(3,new T2(1,_jI,_jK)));}) : (++C,A1(_jo,new T1(3,new T2(1,_jI,_jK))));})):new T0(2):new T1(1,_b1(_ja,function(_jL){return C > 19 ? new F(function(){return A1(_jo,new T1(3,new T2(1,_jI,_jL)));}) : (++C,A1(_jo,new T1(3,new T2(1,_jI,_jL))));}));};return _9t(new T1(0,_jG),new T(function(){return new T1(1,_aB(_c9,_dK,_jo));}));}),_jM=function(_jN){return (!_dO(_a4,_jN,_dT))?new T0(2):new T1(1,_b1(_dU,function(_jO){var _jP=new T2(1,_jN,_jO);if(!_dO(new T2(0,_a9,_ae),_jP,new T2(1,_jm,new T2(1,_jl,new T2(1,_jk,new T2(1,_jj,new T2(1,_ji,new T2(1,_jh,new T2(1,_jg,new T2(1,_jf,new T2(1,_je,new T2(1,_jd,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_jo,new T1(4,_jP));}) : (++C,A1(_jo,new T1(4,_jP)));}else{return C > 19 ? new F(function(){return A1(_jo,new T1(2,_jP));}) : (++C,A1(_jo,new T1(2,_jP)));}}));};return _9t(new T1(0,_jM),_jF);});return _9t(new T1(0,function(_jQ){if(!_dO(_a4,_jQ,_jc)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_jo,new T1(2,new T2(1,_jQ,__Z)));}) : (++C,A1(_jo,new T1(2,new T2(1,_jQ,__Z))));}}),_jE);});return _9t(new T1(0,function(_jR){return (E(_jR)==34)?E(_jC):new T0(2);}),_jD);});return _9t(new T1(0,function(_jS){return (E(_jS)==39)?E(new T1(0,_jw)):new T0(2);}),_jB);});return _9t(new T1(1,function(_jT){return (E(_jT)._==0)?E(_jp):new T0(2);}),_jq);},_jU=function(_jV,_jW){var _jX=new T(function(){var _jY=new T(function(){var _jZ=function(_k0){var _k1=new T(function(){var _k2=new T(function(){return B(A1(_jW,_k0));});return B(_jn(function(_k3){var _k4=E(_k3);return (_k4._==2)?(!_9Z(_k4.a,_9Y))?new T0(2):E(_k2):new T0(2);}));}),_k5=function(_k6){return E(_k1);};return new T1(1,function(_k7){return C > 19 ? new F(function(){return A2(_ig,_k7,_k5);}) : (++C,A2(_ig,_k7,_k5));});};return B(A2(_jV,0,_jZ));});return B(_jn(function(_k8){var _k9=E(_k8);return (_k9._==2)?(!_9Z(_k9.a,_9X))?new T0(2):E(_jY):new T0(2);}));}),_ka=function(_kb){return E(_jX);};return function(_kc){return C > 19 ? new F(function(){return A2(_ig,_kc,_ka);}) : (++C,A2(_ig,_kc,_ka));};},_kd=function(_ke,_kf){var _kg=function(_kh){var _ki=new T(function(){return B(A1(_ke,_kh));}),_kj=function(_kk){return _9t(B(A1(_ki,_kk)),new T(function(){return new T1(1,_jU(_kg,_kk));}));};return _kj;},_kl=new T(function(){return B(A1(_ke,_kf));}),_km=function(_kn){return _9t(B(A1(_kl,_kn)),new T(function(){return new T1(1,_jU(_kg,_kn));}));};return _km;},_ko=function(_kp,_kq){var _kr=function(_ks,_kt){var _ku=function(_kv){return C > 19 ? new F(function(){return A1(_kt,new T(function(){return  -E(_kv);}));}) : (++C,A1(_kt,new T(function(){return  -E(_kv);})));},_kw=new T(function(){return B(_jn(function(_kx){return C > 19 ? new F(function(){return A3(_kp,_kx,_ks,_ku);}) : (++C,A3(_kp,_kx,_ks,_ku));}));}),_ky=function(_kz){return E(_kw);},_kA=function(_kB){return C > 19 ? new F(function(){return A2(_ig,_kB,_ky);}) : (++C,A2(_ig,_kB,_ky));},_kC=new T(function(){return B(_jn(function(_kD){var _kE=E(_kD);if(_kE._==4){var _kF=E(_kE.a);if(!_kF._){return C > 19 ? new F(function(){return A3(_kp,_kE,_ks,_kt);}) : (++C,A3(_kp,_kE,_ks,_kt));}else{if(E(_kF.a)==45){if(!E(_kF.b)._){return E(new T1(1,_kA));}else{return C > 19 ? new F(function(){return A3(_kp,_kE,_ks,_kt);}) : (++C,A3(_kp,_kE,_ks,_kt));}}else{return C > 19 ? new F(function(){return A3(_kp,_kE,_ks,_kt);}) : (++C,A3(_kp,_kE,_ks,_kt));}}}else{return C > 19 ? new F(function(){return A3(_kp,_kE,_ks,_kt);}) : (++C,A3(_kp,_kE,_ks,_kt));}}));}),_kG=function(_kH){return E(_kC);};return new T1(1,function(_kI){return C > 19 ? new F(function(){return A2(_ig,_kI,_kG);}) : (++C,A2(_ig,_kI,_kG));});};return _kd(_kr,_kq);},_kJ=function(_kK){var _kL=E(_kK);if(!_kL._){var _kM=_kL.b,_kN=new T(function(){return _cW(new T(function(){return _cD(E(_kL.a));}),new T(function(){return _cu(_kM,0);},1),_cz(_cF,_kM));});return new T1(1,_kN);}else{return (E(_kL.b)._==0)?(E(_kL.c)._==0)?new T1(1,new T(function(){return _dd(_ct,_kL.a);})):__Z:__Z;}},_kO=function(_kP,_kQ){return new T0(2);},_kR=function(_kS){var _kT=E(_kS);if(_kT._==5){var _kU=_kJ(_kT.a);if(!_kU._){return _kO;}else{var _kV=new T(function(){return _e7(_kU.a);});return function(_kW,_kX){return C > 19 ? new F(function(){return A1(_kX,_kV);}) : (++C,A1(_kX,_kV));};}}else{return _kO;}},_kY=function(_kZ){var _l0=function(_l1){return E(new T2(3,_kZ,_as));};return new T1(1,function(_l2){return C > 19 ? new F(function(){return A2(_ig,_l2,_l0);}) : (++C,A2(_ig,_l2,_l0));});},_l3=new T(function(){return B(A3(_ko,_kR,0,_kY));}),_l4=new T(function(){return unCStr("offsetTop");}),_l5=new T(function(){return new T2(0,E(new T1(2,"id")),"menuList");}),_l6=new T(function(){return new T2(0,E(new T1(2,"class")),"menu");}),_l7=new T(function(){return new T1(1,"top");}),_l8=new T(function(){return new T1(1,"left");}),_l9=new T(function(){return unCStr("Toggle Debug");}),_la=new T(function(){return unCStr("Reset");}),_lb=new T(function(){return _22(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:201:51-57");}),__Z,__Z));}),_lc=new T(function(){return _22(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:201:87-93");}),__Z,__Z));}),_ld=new T(function(){return unCStr("px");}),_le=new T(function(){return unCStr("menuHover");}),_lf=new T(function(){return unCStr("Hover menu");}),_lg=function(_lh,_){var _li=_3q(toJSStr(E(_lf))),_lj=_3n(E(_lh),toJSStr(E(_le)));return _3m(_);},_lk=new T(function(){return unCStr("div");}),_ll=function(_lm,_ln,_lo,_){var _lp=_5e(toJSStr(E(_ln))),_lq=_3D(toJSStr(E(_lk))),_lr=_lq,_ls=B(A(_5o,[_3l,_2G,_2C,_lr,5,function(_lt,_){return _lg(_lr,_);},_])),_lu=B(A(_5o,[_3l,_2G,_2C,_lr,6,function(_lv,_){return _lg(_lr,_);},_])),_lw=B(A(_5o,[_3l,_2G,_2C,_lr,0,_lo,_])),_lx=_3v(_lp,_lr),_ly=_3v(_lr,E(_lm));return 0;},_lz=function(_lA){while(1){var _lB=(function(_lC){var _lD=E(_lC);if(!_lD._){return __Z;}else{var _lE=_lD.b,_lF=E(_lD.a);if(!E(_lF.b)._){return new T2(1,_lF.a,new T(function(){return _lz(_lE);}));}else{_lA=_lE;return __continue;}}})(_lA);if(_lB!=__continue){return _lB;}}},_lG=function(_lH,_lI,_){var _lJ=_53(_),_lK=B(A(_8i,[_3A,_39,_lH,_8u,_])),_lL=B(A(_8i,[_3A,_39,_lH,_l4,_])),_lM=_7C(_7H,_),_lN=B(A(_4S,[_3A,_39,_7P,new T2(1,_l5,new T2(1,_l6,new T2(1,new T(function(){return new T2(0,E(_l7),toJSStr(_0(_lL,_ld)));}),new T2(1,new T(function(){var _lO=_lz(_9j(_l3,_lK));if(!_lO._){return E(_8s);}else{if(!E(_lO.b)._){return new T2(0,E(_l8),toJSStr(_0(_8(0,E(_lO.a)-200|0,__Z),_ld)));}else{return E(_8t);}}}),__Z)))),_])),_lP=function(_lQ,_){var _lR=_6T(toJSStr(E(_6S))),_lS=E(_2n),_lT=__eq(_lR,_lS),_lU=function(_,_lV){var _lW=E(_lV);if(!_lW._){return die(_lb);}else{var _lX=_6T(toJSStr(E(_77))),_lY=__eq(_lX,_lS),_lZ=function(_,_m0){var _m1=E(_m0);if(!_m1._){return die(_lc);}else{var _m2=toJSStr(E(_6v)),_m3=_3n(E(_lW.a),_m2),_m4=_3n(E(_m1.a),_m2),_m5=E(_lI),_m6=_78(_m5,_);return _6U(_m5,_);}};if(!E(_lY)){var _m7=__isUndef(_lX);if(!E(_m7)){return C > 19 ? new F(function(){return _lZ(_,new T1(1,_lX));}) : (++C,_lZ(_,new T1(1,_lX)));}else{return C > 19 ? new F(function(){return _lZ(_,__Z);}) : (++C,_lZ(_,__Z));}}else{return C > 19 ? new F(function(){return _lZ(_,__Z);}) : (++C,_lZ(_,__Z));}}};if(!E(_lT)){var _m8=__isUndef(_lR);if(!E(_m8)){return C > 19 ? new F(function(){return _lU(_,new T1(1,_lR));}) : (++C,_lU(_,new T1(1,_lR)));}else{return C > 19 ? new F(function(){return _lU(_,__Z);}) : (++C,_lU(_,__Z));}}else{return C > 19 ? new F(function(){return _lU(_,__Z);}) : (++C,_lU(_,__Z));}},_m9=_ll(_lN,_l9,_lP,_),_ma=E(_lI),_mb=rMV(_ma),_mc=nMV(new T5(0,new T(function(){return E(E(_mb).a);}),_86,_85,__Z,0)),_md=_mc,_me=_ll(_lN,_la,function(_mf,_){var _mg=_78(_md,_),_mh=B(_7S(_md,_)),_mi=rMV(_md),_=wMV(_ma,_mi);return 0;},_),_mj=_3v(E(_lN),E(_7v));return 0;},_mk=new T(function(){return _22(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:38:5-13");}),__Z,__Z));}),_ml=new T(function(){return unCStr("Draw exercise tree");}),_mm=new T(function(){return unCStr("Draw example tree");}),_mn=new T(function(){return unCStr("menuButton");}),_mo=function(_mp,_){var _mq=B(A(_5o,[_3l,_2G,_2C,_7v,0,function(_mr,_){return _7J(_mp,_);},_])),_ms=_6T(toJSStr(E(_mn))),_mt=__eq(_ms,E(_2n)),_mu=function(_,_mv){var _mw=E(_mv);if(!_mw._){return die(_mk);}else{var _mx=_mw.a,_my=B(A(_5o,[_3l,_2G,_2C,_mx,0,function(_mz,_){return _lG(_mx,_mp,_);},_])),_mA=_3q(toJSStr(E(_mm))),_mB=E(_mp),_mC=_6U(_mB,_),_mD=_3q(toJSStr(E(_ml))),_mE=_78(_mB,_);return 0;}};if(!E(_mt)){var _mF=__isUndef(_ms);if(!E(_mF)){return _mu(_,new T1(1,_ms));}else{return _mu(_,__Z);}}else{return _mu(_,__Z);}},_mG=new T(function(){return unCStr("PrimaLat");}),_mH=function(_){var _mI=nMV(new T5(0,_mG,_86,_85,__Z,0)),_mJ=_mo(_mI,_);return 0;},_mK=function(_){return _mH(_);};
var hasteMain = function() {B(A(_mK, [0]));};window.onload = hasteMain;