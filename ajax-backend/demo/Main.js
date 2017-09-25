"use strict";
var __haste_prog_id = 'c5053452144f19ba339ca140960e484d67a143c302afff50fb54ba5f153a9c34';
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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return _0(_3.b,_2);}));},_4=function(_5,_){while(1){var _6=E(_5);if(!_6._){return 0;}else{var _7=_6.b,_8=E(_6.a);switch(_8._){case 0:var _9=B(A1(_8.a,_));_5=_0(_7,new T2(1,_9,__Z));continue;case 1:_5=_0(_7,_8.a);continue;default:_5=_7;continue;}}}},_a=function(_b,_c,_){var _d=E(_b);switch(_d._){case 0:var _e=B(A1(_d.a,_));return _4(_0(_c,new T2(1,_e,__Z)),_);case 1:return _4(_0(_c,_d.a),_);default:return _4(_c,_);}},_f=new T(function(){return toJSStr(__Z);}),_g=function(_h){return E(_f);},_i=function(_j,_){var _k=E(_j);if(!_k._){return __Z;}else{var _l=_i(_k.b,_);return new T2(1,new T(function(){return String(E(_k.a));}),_l);}},_m=function(_n,_){var _o=__arr2lst(0,_n);return _i(_o,_);},_p=function(_q){return String(E(_q));},_r=function(_s){return _p(_s);},_t=function(_u,_){return new T(function(){return _r(_u);});},_v=new T4(0,new T2(0,function(_w){return E(_w);},function(_x){return __lst2arr(E(_x));}),new T2(0,_t,function(_y,_){return _m(E(_y),_);}),_g,_g),_z=function(_A,_B,_C){var _D=function(_E){var _F=new T(function(){return B(A1(_C,_E));});return C > 19 ? new F(function(){return A1(_B,function(_G){return E(_F);});}) : (++C,A1(_B,function(_G){return E(_F);}));};return C > 19 ? new F(function(){return A1(_A,_D);}) : (++C,A1(_A,_D));},_H=function(_I,_J,_K){var _L=new T(function(){return B(A1(_J,function(_M){return C > 19 ? new F(function(){return A1(_K,_M);}) : (++C,A1(_K,_M));}));});return C > 19 ? new F(function(){return A1(_I,function(_N){return E(_L);});}) : (++C,A1(_I,function(_N){return E(_L);}));},_O=function(_P,_Q,_R){var _S=function(_T){var _U=function(_V){return C > 19 ? new F(function(){return A1(_R,new T(function(){return B(A1(_T,_V));}));}) : (++C,A1(_R,new T(function(){return B(A1(_T,_V));})));};return C > 19 ? new F(function(){return A1(_Q,_U);}) : (++C,A1(_Q,_U));};return C > 19 ? new F(function(){return A1(_P,_S);}) : (++C,A1(_P,_S));},_W=function(_X,_Y){return C > 19 ? new F(function(){return A1(_Y,_X);}) : (++C,A1(_Y,_X));},_Z=function(_10,_11,_12){var _13=new T(function(){return B(A1(_12,_10));});return C > 19 ? new F(function(){return A1(_11,function(_14){return E(_13);});}) : (++C,A1(_11,function(_14){return E(_13);}));},_15=function(_16,_17,_18){var _19=function(_1a){return C > 19 ? new F(function(){return A1(_18,new T(function(){return B(A1(_16,_1a));}));}) : (++C,A1(_18,new T(function(){return B(A1(_16,_1a));})));};return C > 19 ? new F(function(){return A1(_17,_19);}) : (++C,A1(_17,_19));},_1b=function(_1c,_1d,_1e){return C > 19 ? new F(function(){return A1(_1c,function(_1f){return C > 19 ? new F(function(){return A2(_1d,_1f,_1e);}) : (++C,A2(_1d,_1f,_1e));});}) : (++C,A1(_1c,function(_1f){return C > 19 ? new F(function(){return A2(_1d,_1f,_1e);}) : (++C,A2(_1d,_1f,_1e));}));},_1g=function(_1h){return E(E(_1h).b);},_1i=function(_1j,_1k){return C > 19 ? new F(function(){return A3(_1g,_1l,_1j,function(_1m){return E(_1k);});}) : (++C,A3(_1g,_1l,_1j,function(_1m){return E(_1k);}));},_1l=new T(function(){return new T5(0,new T5(0,new T2(0,_15,_Z),_W,_O,_H,_z),_1b,_1i,_W,function(_1n){return err(_1n);});}),_1o=function(_1p,_1q,_){var _1r=B(A1(_1q,_));return new T(function(){return B(A1(_1p,_1r));});},_1s=function(_1t,_1u){return new T1(0,function(_){return _1o(_1u,_1t,_);});},_1v=function(_1w){return new T0(2);},_1x=function(_1y){var _1z=new T(function(){return B(A1(_1y,_1v));}),_1A=function(_1B){return new T1(1,new T2(1,new T(function(){return B(A1(_1B,0));}),new T2(1,_1z,__Z)));};return _1A;},_1C=function(_1D){return E(_1D);},_1E=new T3(0,new T2(0,_1l,_1s),_1C,_1x),_1F=new T(function(){return unCStr("}");}),_1G=new T(function(){return unCStr(", ");}),_1H=new T(function(){return unCStr("SM {");}),_1I=new T(function(){return unCStr("ssuccess = ");}),_1J=new T(function(){return unCStr("sb = ");}),_1K=new T(function(){return unCStr("sa = ");}),_1L=new T(function(){return unCStr("sscore = ");}),_1M=function(_1N,_1O,_1P){return C > 19 ? new F(function(){return A1(_1N,new T2(1,44,new T(function(){return B(A1(_1O,_1P));})));}) : (++C,A1(_1N,new T2(1,44,new T(function(){return B(A1(_1O,_1P));}))));},_1Q=new T(function(){return unCStr("M ");}),_1R=function(_1S,_1T){var _1U=jsShowI(_1S);return _0(fromJSStr(_1U),_1T);},_1V=function(_1W,_1X,_1Y){if(_1X>=0){return _1R(_1X,_1Y);}else{if(_1W<=6){return _1R(_1X,_1Y);}else{return new T2(1,40,new T(function(){var _1Z=jsShowI(_1X);return _0(fromJSStr(_1Z),new T2(1,41,_1Y));}));}}},_20=new T(function(){return unCStr(": empty list");}),_21=new T(function(){return unCStr("Prelude.");}),_22=function(_23){return err(_0(_21,new T(function(){return _0(_23,_20);},1)));},_24=new T(function(){return _22(new T(function(){return unCStr("foldr1");}));}),_25=function(_26,_27){var _28=E(_27);if(!_28._){return E(_24);}else{var _29=_28.a,_2a=E(_28.b);if(!_2a._){return E(_29);}else{return C > 19 ? new F(function(){return A2(_26,_29,new T(function(){return B(_25(_26,_2a));}));}) : (++C,A2(_26,_29,new T(function(){return B(_25(_26,_2a));})));}}},_2b=new T(function(){return unCStr("tree = ");}),_2c=new T(function(){return unCStr("lin = ");}),_2d=new T(function(){return unCStr("cost = ");}),_2e=new T(function(){return unCStr("T {");}),_2f=new T(function(){return err(new T(function(){return _0(_21,new T(function(){return unCStr("!!: negative index");}));}));}),_2g=new T(function(){return err(new T(function(){return _0(_21,new T(function(){return unCStr("!!: index too large");}));}));}),_2h=function(_2i,_2j){while(1){var _2k=E(_2i);if(!_2k._){return E(_2g);}else{var _2l=E(_2j);if(!_2l){return E(_2k.a);}else{_2i=_2k.b;_2j=_2l-1|0;continue;}}}},_2m=function(_2n,_2o){if(_2o>=0){return _2h(_2n,_2o);}else{return E(_2f);}},_2p=new T(function(){return unCStr("ACK");}),_2q=new T(function(){return unCStr("BEL");}),_2r=new T(function(){return unCStr("BS");}),_2s=new T(function(){return unCStr("SP");}),_2t=new T(function(){return unCStr("US");}),_2u=new T(function(){return unCStr("RS");}),_2v=new T(function(){return unCStr("GS");}),_2w=new T(function(){return unCStr("FS");}),_2x=new T(function(){return unCStr("ESC");}),_2y=new T(function(){return unCStr("SUB");}),_2z=new T(function(){return unCStr("EM");}),_2A=new T(function(){return unCStr("CAN");}),_2B=new T(function(){return unCStr("ETB");}),_2C=new T(function(){return unCStr("SYN");}),_2D=new T(function(){return unCStr("NAK");}),_2E=new T(function(){return unCStr("DC4");}),_2F=new T(function(){return unCStr("DC3");}),_2G=new T(function(){return unCStr("DC2");}),_2H=new T(function(){return unCStr("DC1");}),_2I=new T(function(){return unCStr("DLE");}),_2J=new T(function(){return unCStr("SI");}),_2K=new T(function(){return unCStr("SO");}),_2L=new T(function(){return unCStr("CR");}),_2M=new T(function(){return unCStr("FF");}),_2N=new T(function(){return unCStr("VT");}),_2O=new T(function(){return unCStr("LF");}),_2P=new T(function(){return unCStr("HT");}),_2Q=new T(function(){return unCStr("ENQ");}),_2R=new T(function(){return unCStr("EOT");}),_2S=new T(function(){return unCStr("ETX");}),_2T=new T(function(){return unCStr("STX");}),_2U=new T(function(){return unCStr("SOH");}),_2V=new T(function(){return unCStr("NUL");}),_2W=new T(function(){return unCStr("\\DEL");}),_2X=new T(function(){return unCStr("\\a");}),_2Y=new T(function(){return unCStr("\\\\");}),_2Z=new T(function(){return unCStr("\\SO");}),_30=new T(function(){return unCStr("\\r");}),_31=new T(function(){return unCStr("\\f");}),_32=new T(function(){return unCStr("\\v");}),_33=new T(function(){return unCStr("\\n");}),_34=new T(function(){return unCStr("\\t");}),_35=new T(function(){return unCStr("\\b");}),_36=function(_37,_38){if(_37<=127){var _39=E(_37);switch(_39){case 92:return _0(_2Y,_38);case 127:return _0(_2W,_38);default:if(_39<32){switch(_39){case 7:return _0(_2X,_38);case 8:return _0(_35,_38);case 9:return _0(_34,_38);case 10:return _0(_33,_38);case 11:return _0(_32,_38);case 12:return _0(_31,_38);case 13:return _0(_30,_38);case 14:return _0(_2Z,new T(function(){var _3a=E(_38);if(!_3a._){return __Z;}else{if(E(_3a.a)==72){return unAppCStr("\\&",_3a);}else{return _3a;}}},1));default:return _0(new T2(1,92,new T(function(){return _2m(new T2(1,_2V,new T2(1,_2U,new T2(1,_2T,new T2(1,_2S,new T2(1,_2R,new T2(1,_2Q,new T2(1,_2p,new T2(1,_2q,new T2(1,_2r,new T2(1,_2P,new T2(1,_2O,new T2(1,_2N,new T2(1,_2M,new T2(1,_2L,new T2(1,_2K,new T2(1,_2J,new T2(1,_2I,new T2(1,_2H,new T2(1,_2G,new T2(1,_2F,new T2(1,_2E,new T2(1,_2D,new T2(1,_2C,new T2(1,_2B,new T2(1,_2A,new T2(1,_2z,new T2(1,_2y,new T2(1,_2x,new T2(1,_2w,new T2(1,_2v,new T2(1,_2u,new T2(1,_2t,new T2(1,_2s,__Z))))))))))))))))))))))))))))))))),_39);})),_38);}}else{return new T2(1,_39,_38);}}}else{var _3b=new T(function(){var _3c=jsShowI(_37);return _0(fromJSStr(_3c),new T(function(){var _3d=E(_38);if(!_3d._){return __Z;}else{var _3e=E(_3d.a);if(_3e<48){return _3d;}else{if(_3e>57){return _3d;}else{return unAppCStr("\\&",_3d);}}}},1));});return new T2(1,92,_3b);}},_3f=new T(function(){return unCStr("\\\"");}),_3g=function(_3h,_3i){var _3j=E(_3h);if(!_3j._){return E(_3i);}else{var _3k=_3j.b,_3l=E(_3j.a);if(_3l==34){return _0(_3f,new T(function(){return _3g(_3k,_3i);},1));}else{return _36(_3l,new T(function(){return _3g(_3k,_3i);}));}}},_3m=function(_3n,_3o){return new T2(1,34,new T(function(){return _3g(_3n,new T2(1,34,_3o));}));},_3p=function(_3q,_3r,_3s){var _3t=E(_3r);if(!_3t._){return unAppCStr("[]",_3s);}else{var _3u=new T(function(){var _3v=new T(function(){var _3w=function(_3x){var _3y=E(_3x);if(!_3y._){return E(new T2(1,93,_3s));}else{var _3z=new T(function(){return B(A2(_3q,_3y.a,new T(function(){return _3w(_3y.b);})));});return new T2(1,44,_3z);}};return _3w(_3t.b);});return B(A2(_3q,_3t.a,_3v));});return new T2(1,91,_3u);}},_3A=function(_3B,_3C){return _1V(0,E(_3B),_3C);},_3D=function(_3E,_3F){return _3p(_3A,_3E,_3F);},_3G=function(_3H,_3I,_3J,_3K,_3L){var _3M=function(_3N){var _3O=new T(function(){var _3P=new T(function(){var _3Q=new T(function(){var _3R=new T(function(){var _3S=new T(function(){var _3T=new T(function(){var _3U=new T(function(){var _3V=new T(function(){return _3g(_3K,new T2(1,34,new T(function(){return _0(_1F,_3N);})));});return _0(_2b,new T2(1,34,_3V));},1);return _0(_1G,_3U);}),_3W=E(_3J);if(!_3W._){return unAppCStr("[]",_3T);}else{var _3X=new T(function(){var _3Y=E(_3W.a),_3Z=new T(function(){var _40=new T(function(){var _41=function(_42){var _43=E(_42);if(!_43._){return E(new T2(1,93,_3T));}else{var _44=new T(function(){var _45=E(_43.a),_46=new T(function(){return B(A3(_25,_1M,new T2(1,function(_47){return _3D(_45.a,_47);},new T2(1,function(_48){return _3m(_45.b,_48);},__Z)),new T2(1,41,new T(function(){return _41(_43.b);}))));});return new T2(1,40,_46);});return new T2(1,44,_44);}};return _41(_3W.b);});return B(A3(_25,_1M,new T2(1,function(_49){return _3D(_3Y.a,_49);},new T2(1,function(_4a){return _3m(_3Y.b,_4a);},__Z)),new T2(1,41,_40)));});return new T2(1,40,_3Z);});return new T2(1,91,_3X);}},1);return _0(_2c,_3S);},1);return _0(_1G,_3R);});return _1V(0,E(_3I),_3Q);},1);return _0(_2d,_3P);},1);return _0(_2e,_3O);};if(_3H<11){return _3M(_3L);}else{return new T2(1,40,new T(function(){return _3M(new T2(1,41,_3L));}));}},_4b=function(_4c,_4d){var _4e=E(_4c);return _3G(0,_4e.a,_4e.b,_4e.c,_4d);},_4f=function(_4g,_4h){return _3p(_4b,_4g,_4h);},_4i=function(_4j){return _3p(_4f,_4j,__Z);},_4k=function(_4l,_4m){return _3p(_4f,_4l,_4m);},_4n=function(_4o,_4p){return _3p(_4k,_4o,_4p);},_4q=function(_4r,_4g,_4h){return _4k(_4g,_4h);},_4s=function(_4t){return _3p(_3A,_4t,__Z);},_4u=function(_4v,_4w){return _3p(_3D,_4v,_4w);},_4x=function(_4y,_4z,_4A){return _3D(_4z,_4A);},_4B=function(_4C,_4D){while(1){var _4E=(function(_4F,_4G){var _4H=E(_4G);if(!_4H._){_4C=new T2(1,new T2(0,_4H.b,_4H.c),new T(function(){return _4B(_4F,_4H.e);}));_4D=_4H.d;return __continue;}else{return E(_4F);}})(_4C,_4D);if(_4E!=__continue){return _4E;}}},_4I=new T(function(){return unCStr("fromList ");}),_4J=function(_4K){return E(E(_4K).a);},_4L=function(_4M,_4N,_4O,_4P){var _4Q=new T(function(){return _4B(__Z,_4P);}),_4R=function(_4S,_4T){var _4U=E(_4S),_4V=new T(function(){return B(A3(_25,_1M,new T2(1,new T(function(){return B(A3(_4J,_4M,0,_4U.a));}),new T2(1,new T(function(){return B(A3(_4J,_4N,0,_4U.b));}),__Z)),new T2(1,41,_4T)));});return new T2(1,40,_4V);};if(_4O<=10){var _4W=function(_4X){return _0(_4I,new T(function(){return _3p(_4R,_4Q,_4X);},1));};return _4W;}else{var _4Y=function(_4Z){var _50=new T(function(){return _0(_4I,new T(function(){return _3p(_4R,_4Q,new T2(1,41,_4Z));},1));});return new T2(1,40,_50);};return _4Y;}},_51=function(_52,_53){var _54=new T(function(){return _4L(new T3(0,_4x,_4s,_4u),new T3(0,_4q,_4i,_4n),11,_53);});if(_52<11){var _55=function(_56){return _0(_1Q,new T(function(){return B(A1(_54,_56));},1));};return _55;}else{var _57=function(_58){var _59=new T(function(){return _0(_1Q,new T(function(){return B(A1(_54,new T2(1,41,_58)));},1));});return new T2(1,40,_59);};return _57;}},_5a=new T(function(){return unCStr("smenu = ");}),_5b=new T(function(){return unCStr("slin = ");}),_5c=new T(function(){return unCStr("stree = ");}),_5d=new T(function(){return unCStr("sgrammar = ");}),_5e=new T(function(){return unCStr("ST {");}),_5f=function(_5g,_5h,_5i,_5j,_5k){var _5l=new T(function(){return _51(0,E(_5k).a);}),_5m=function(_5n){var _5o=new T(function(){var _5p=new T(function(){var _5q=new T(function(){var _5r=new T(function(){var _5s=new T(function(){var _5t=new T(function(){var _5u=new T(function(){var _5v=new T(function(){var _5w=new T(function(){var _5x=new T(function(){var _5y=new T(function(){return B(A1(_5l,new T(function(){return _0(_1F,_5n);})));},1);return _0(_5a,_5y);},1);return _0(_1G,_5x);}),_5z=E(_5j);if(!_5z._){return unAppCStr("[]",_5w);}else{var _5A=new T(function(){var _5B=E(_5z.a),_5C=new T(function(){var _5D=new T(function(){var _5E=function(_5F){var _5G=E(_5F);if(!_5G._){return E(new T2(1,93,_5w));}else{var _5H=new T(function(){var _5I=E(_5G.a),_5J=new T(function(){return B(A3(_25,_1M,new T2(1,function(_5K){return _3D(_5I.a,_5K);},new T2(1,function(_5L){return _3m(_5I.b,_5L);},__Z)),new T2(1,41,new T(function(){return _5E(_5G.b);}))));});return new T2(1,40,_5J);});return new T2(1,44,_5H);}};return _5E(_5z.b);});return B(A3(_25,_1M,new T2(1,function(_5M){return _3D(_5B.a,_5M);},new T2(1,function(_5N){return _3m(_5B.b,_5N);},__Z)),new T2(1,41,_5D)));});return new T2(1,40,_5C);});return new T2(1,91,_5A);}},1);return _0(_5b,_5v);},1);return _0(_1G,_5u);});return _3g(_5i,new T2(1,34,_5t));});return _0(_5c,new T2(1,34,_5s));},1);return _0(_1G,_5r);});return _3g(_5h,new T2(1,34,_5q));});return _0(_5d,new T2(1,34,_5p));},1);return _0(_5e,_5o);};if(_5g<11){return _5m;}else{var _5O=function(_5P){return new T2(1,40,new T(function(){return _5m(new T2(1,41,_5P));}));};return _5O;}},_5Q=new T(function(){return unCStr("True");}),_5R=new T(function(){return unCStr("False");}),_5S=function(_5T,_5U,_5V,_5W,_5X){var _5Y=new T(function(){var _5Z=E(_5W);return _5f(0,_5Z.a,_5Z.b,_5Z.c,_5Z.d);}),_60=new T(function(){var _61=E(_5X);return _5f(0,_61.a,_61.b,_61.c,_61.d);}),_62=function(_63){var _64=new T(function(){var _65=new T(function(){var _66=new T(function(){var _67=new T(function(){var _68=new T(function(){var _69=new T(function(){var _6a=new T(function(){var _6b=new T(function(){return B(A1(_60,new T(function(){return _0(_1F,_63);})));},1);return _0(_1J,_6b);},1);return _0(_1G,_6a);});return B(A1(_5Y,_69));},1);return _0(_1K,_68);},1);return _0(_1G,_67);});return _1V(0,E(_5V),_66);},1);return _0(_1L,_65);},1);return _0(_1G,_64);},_6c=function(_6d){var _6e=new T(function(){if(!E(_5U)){return _0(_5R,new T(function(){return _62(_6d);},1));}else{return _0(_5Q,new T(function(){return _62(_6d);},1));}},1);return _0(_1I,_6e);};if(_5T<11){var _6f=function(_6g){return _0(_1H,new T(function(){return _6c(_6g);},1));};return _6f;}else{var _6h=function(_6i){var _6j=new T(function(){return _0(_1H,new T(function(){return _6c(new T2(1,41,_6i));},1));});return new T2(1,40,_6j);};return _6h;}},_6k=function(_6l){return E(E(_6l).a);},_6m=function(_6n,_6o){var _6p=strEq(E(_6n),E(_6o));return (E(_6p)==0)?false:true;},_6q=new T(function(){return new T2(0,function(_6r,_6s){return _6m(_6r,_6s);},function(_6t,_6u){return (!B(A3(_6k,_6q,_6t,_6u)))?true:false;});}),_6v=function(_6w,_6x){if(_6w<=_6x){var _6y=function(_6z){return new T2(1,_6z,new T(function(){if(_6z!=_6x){return _6y(_6z+1|0);}else{return __Z;}}));};return _6y(_6w);}else{return __Z;}},_6A=function(_6B,_6C,_6D){if(_6D<=_6C){var _6E=new T(function(){var _6F=_6C-_6B|0,_6G=function(_6H){return (_6H>=(_6D-_6F|0))?new T2(1,_6H,new T(function(){return _6G(_6H+_6F|0);})):new T2(1,_6H,__Z);};return _6G(_6C);});return new T2(1,_6B,_6E);}else{return (_6D<=_6B)?new T2(1,_6B,__Z):__Z;}},_6I=function(_6J,_6K,_6L){if(_6L>=_6K){var _6M=new T(function(){var _6N=_6K-_6J|0,_6O=function(_6P){return (_6P<=(_6L-_6N|0))?new T2(1,_6P,new T(function(){return _6O(_6P+_6N|0);})):new T2(1,_6P,__Z);};return _6O(_6K);});return new T2(1,_6J,_6M);}else{return (_6L>=_6J)?new T2(1,_6J,__Z):__Z;}},_6Q=function(_6R,_6S){if(_6S<_6R){return _6A(_6R,_6S,-2147483648);}else{return _6I(_6R,_6S,2147483647);}},_6T=function(_6U,_6V,_6W){if(_6V<_6U){return _6A(_6U,_6V,_6W);}else{return _6I(_6U,_6V,_6W);}},_6X=function(_6Y){return E(_6Y);},_6Z=new T(function(){return err(new T(function(){return unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound");}));}),_70=new T(function(){return err(new T(function(){return unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound");}));}),_71=function(_72,_73){if(_72<=0){if(_72>=0){return quot(_72,_73);}else{if(_73<=0){return quot(_72,_73);}else{return quot(_72+1|0,_73)-1|0;}}}else{if(_73>=0){if(_72>=0){return quot(_72,_73);}else{if(_73<=0){return quot(_72,_73);}else{return quot(_72+1|0,_73)-1|0;}}}else{return quot(_72-1|0,_73)-1|0;}}},_74=new T(function(){return unCStr("base");}),_75=new T(function(){return unCStr("GHC.Exception");}),_76=new T(function(){return unCStr("ArithException");}),_77=function(_78){return E(new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_74,_75,_76),__Z,__Z));},_79=function(_7a){return E(E(_7a).a);},_7b=function(_7c,_7d,_7e){var _7f=B(A1(_7c,_)),_7g=B(A1(_7d,_)),_7h=hs_eqWord64(_7f.a,_7g.a);if(!_7h){return __Z;}else{var _7i=hs_eqWord64(_7f.b,_7g.b);return (!_7i)?__Z:new T1(1,_7e);}},_7j=new T(function(){return unCStr("Ratio has zero denominator");}),_7k=new T(function(){return unCStr("denormal");}),_7l=new T(function(){return unCStr("divide by zero");}),_7m=new T(function(){return unCStr("loss of precision");}),_7n=new T(function(){return unCStr("arithmetic underflow");}),_7o=new T(function(){return unCStr("arithmetic overflow");}),_7p=function(_7q,_7r){switch(E(_7q)){case 0:return _0(_7o,_7r);case 1:return _0(_7n,_7r);case 2:return _0(_7m,_7r);case 3:return _0(_7l,_7r);case 4:return _0(_7k,_7r);default:return _0(_7j,_7r);}},_7s=function(_7t){return _7p(_7t,__Z);},_7u=new T(function(){return new T5(0,_77,new T3(0,function(_7v,_7w,_7x){return _7p(_7w,_7x);},_7s,function(_7y,_7z){return _3p(_7p,_7y,_7z);}),_7A,function(_7B){var _7C=E(_7B);return _7b(_79(_7C.a),_77,_7C.b);},_7s);}),_7A=function(_7D){return new T2(0,_7u,_7D);},_7E=new T(function(){return die(new T(function(){return _7A(3);}));}),_7F=new T(function(){return die(new T(function(){return _7A(0);}));}),_7G=function(_7H,_7I){var _7J=E(_7I);switch(_7J){case -1:var _7K=E(_7H);if(_7K==(-2147483648)){return E(_7F);}else{return _71(_7K,-1);}break;case 0:return E(_7E);default:return _71(_7H,_7J);}},_7L=new T2(0,_7F,0),_7M=function(_7N,_7O){var _7P=_7N%_7O;if(_7N<=0){if(_7N>=0){return _7P;}else{if(_7O<=0){return _7P;}else{return (_7P==0)?0:_7P+_7O|0;}}}else{if(_7O>=0){if(_7N>=0){return _7P;}else{if(_7O<=0){return _7P;}else{return (_7P==0)?0:_7P+_7O|0;}}}else{return (_7P==0)?0:_7P+_7O|0;}}},_7Q=function(_7R){return new T1(0,_7R);},_7S=new T1(0,1),_7T=function(_7U){var _7V=E(_7U);if(!_7V._){return E(_7V.a);}else{return I_toInt(_7V.a);}},_7W=function(_7X,_7Y){return (_7X>=_7Y)?(_7X!=_7Y)?2:1:0;},_7Z={_:0,a:new T3(0,{_:0,a:function(_80,_81){return E(_80)+E(_81)|0;},b:function(_82,_83){return E(_82)-E(_83)|0;},c:function(_84,_85){return imul(E(_84),E(_85))|0;},d:function(_86){return  -E(_86);},e:function(_87){var _88=E(_87);return (_88<0)? -_88:_88;},f:function(_89){var _8a=E(_89);return (_8a>=0)?(_8a==0)?0:1:-1;},g:function(_8b){return _7T(_8b);}},{_:0,a:new T2(0,function(_8c,_8d){return E(_8c)==E(_8d);},function(_8e,_8f){return E(_8e)!=E(_8f);}),b:function(_8g,_8h){return _7W(E(_8g),E(_8h));},c:function(_8i,_8j){return E(_8i)<E(_8j);},d:function(_8k,_8l){return E(_8k)<=E(_8l);},e:function(_8m,_8n){return E(_8m)>E(_8n);},f:function(_8o,_8p){return E(_8o)>=E(_8p);},g:function(_8q,_8r){var _8s=E(_8q),_8t=E(_8r);return (_8s>_8t)?_8s:_8t;},h:function(_8u,_8v){var _8w=E(_8u),_8x=E(_8v);return (_8w>_8x)?_8x:_8w;}},function(_8y){return new T2(0,E(_7Q(E(_8y))),E(_7S));}),b:{_:0,a:function(_8z){var _8A=E(_8z);return (_8A==2147483647)?E(_70):_8A+1|0;},b:function(_8B){var _8C=E(_8B);return (_8C==(-2147483648))?E(_6Z):_8C-1|0;},c:_6X,d:_6X,e:function(_8D){return _6v(E(_8D),2147483647);},f:function(_8E,_8F){return _6Q(E(_8E),E(_8F));},g:function(_8G,_8H){return _6v(E(_8G),E(_8H));},h:function(_8I,_8J,_8K){return _6T(E(_8I),E(_8J),E(_8K));}},c:function(_8L,_8M){var _8N=E(_8L),_8O=E(_8M);switch(_8O){case -1:if(_8N==(-2147483648)){return E(_7F);}else{return quot(_8N,-1);}break;case 0:return E(_7E);default:return quot(_8N,_8O);}},d:function(_8P,_8Q){var _8R=E(_8Q);switch(_8R){case -1:return 0;case 0:return E(_7E);default:return E(_8P)%_8R;}},e:function(_8S,_8T){return _7G(E(_8S),E(_8T));},f:function(_8U,_8V){var _8W=E(_8V);switch(_8W){case -1:return 0;case 0:return E(_7E);default:return _7M(E(_8U),_8W);}},g:function(_8X,_8Y){var _8Z=E(_8X),_90=E(_8Y);switch(_90){case -1:if(_8Z==(-2147483648)){return E(_7L);}else{var _91=quotRemI(_8Z,-1);return new T2(0,_91.a,_91.b);}break;case 0:return E(_7E);default:var _92=quotRemI(_8Z,_90);return new T2(0,_92.a,_92.b);}},h:function(_93,_94){var _95=E(_93),_96=E(_94);switch(_96){case -1:if(_95==(-2147483648)){return E(_7L);}else{if(_95<=0){if(_95>=0){var _97=quotRemI(_95,-1);return new T2(0,_97.a,_97.b);}else{var _98=quotRemI(_95,-1);return new T2(0,_98.a,_98.b);}}else{var _99=quotRemI(_95-1|0,-1);return new T2(0,_99.a-1|0,(_99.b+(-1)|0)+1|0);}}break;case 0:return E(_7E);default:if(_95<=0){if(_95>=0){var _9a=quotRemI(_95,_96);return new T2(0,_9a.a,_9a.b);}else{if(_96<=0){var _9b=quotRemI(_95,_96);return new T2(0,_9b.a,_9b.b);}else{var _9c=quotRemI(_95+1|0,_96);return new T2(0,_9c.a-1|0,(_9c.b+_96|0)-1|0);}}}else{if(_96>=0){if(_95>=0){var _9d=quotRemI(_95,_96);return new T2(0,_9d.a,_9d.b);}else{if(_96<=0){var _9e=quotRemI(_95,_96);return new T2(0,_9e.a,_9e.b);}else{var _9f=quotRemI(_95+1|0,_96);return new T2(0,_9f.a-1|0,(_9f.b+_96|0)-1|0);}}}else{var _9g=quotRemI(_95-1|0,_96);return new T2(0,_9g.a-1|0,(_9g.b+_96|0)+1|0);}}}},i:function(_9h){return _7Q(E(_9h));}},_9i=new T1(0,2),_9j=function(_9k){return E(E(_9k).a);},_9l=function(_9m){return E(E(_9m).a);},_9n=function(_9o,_9p){while(1){var _9q=E(_9o);if(!_9q._){var _9r=_9q.a,_9s=E(_9p);if(!_9s._){var _9t=_9s.a;if(!(imul(_9r,_9t)|0)){return new T1(0,imul(_9r,_9t)|0);}else{_9o=new T1(1,I_fromInt(_9r));_9p=new T1(1,I_fromInt(_9t));continue;}}else{_9o=new T1(1,I_fromInt(_9r));_9p=_9s;continue;}}else{var _9u=E(_9p);if(!_9u._){_9o=_9q;_9p=new T1(1,I_fromInt(_9u.a));continue;}else{return new T1(1,I_mul(_9q.a,_9u.a));}}}},_9v=function(_9w,_9x,_9y){while(1){if(!(_9x%2)){var _9z=_9n(_9w,_9w),_9A=quot(_9x,2);_9w=_9z;_9x=_9A;continue;}else{var _9B=E(_9x);if(_9B==1){return _9n(_9w,_9y);}else{var _9z=_9n(_9w,_9w),_9C=_9n(_9w,_9y);_9w=_9z;_9x=quot(_9B-1|0,2);_9y=_9C;continue;}}}},_9D=function(_9E,_9F){while(1){if(!(_9F%2)){var _9G=_9n(_9E,_9E),_9H=quot(_9F,2);_9E=_9G;_9F=_9H;continue;}else{var _9I=E(_9F);if(_9I==1){return E(_9E);}else{return _9v(_9n(_9E,_9E),quot(_9I-1|0,2),_9E);}}}},_9J=function(_9K){return E(E(_9K).c);},_9L=function(_9M){return E(E(_9M).a);},_9N=function(_9O){return E(E(_9O).b);},_9P=function(_9Q){return E(E(_9Q).b);},_9R=function(_9S){return E(E(_9S).c);},_9T=new T1(0,0),_9U=new T1(0,2),_9V=function(_9W){return E(E(_9W).g);},_9X=function(_9Y){return E(E(_9Y).d);},_9Z=function(_a0,_a1){var _a2=_9j(_a0),_a3=new T(function(){return _9l(_a2);}),_a4=new T(function(){return B(A3(_9X,_a0,_a1,new T(function(){return B(A2(_9V,_a3,_9U));})));});return C > 19 ? new F(function(){return A3(_6k,_9L(_9N(_a2)),_a4,new T(function(){return B(A2(_9V,_a3,_9T));}));}) : (++C,A3(_6k,_9L(_9N(_a2)),_a4,new T(function(){return B(A2(_9V,_a3,_9T));})));},_a5=new T(function(){return unCStr("Negative exponent");}),_a6=new T(function(){return err(_a5);}),_a7=function(_a8){return E(E(_a8).c);},_a9=function(_aa,_ab,_ac,_ad){var _ae=_9j(_ab),_af=new T(function(){return _9l(_ae);}),_ag=_9N(_ae);if(!B(A3(_9R,_ag,_ad,new T(function(){return B(A2(_9V,_af,_9T));})))){if(!B(A3(_6k,_9L(_ag),_ad,new T(function(){return B(A2(_9V,_af,_9T));})))){var _ah=new T(function(){return B(A2(_9V,_af,_9U));}),_ai=new T(function(){return B(A2(_9V,_af,_7S));}),_aj=_9L(_ag),_ak=function(_al,_am,_an){while(1){var _ao=B((function(_ap,_aq,_ar){if(!B(_9Z(_ab,_aq))){if(!B(A3(_6k,_aj,_aq,_ai))){var _as=new T(function(){return B(A3(_a7,_ab,new T(function(){return B(A3(_9P,_af,_aq,_ai));}),_ah));});_al=new T(function(){return B(A3(_9J,_aa,_ap,_ap));});_am=_as;_an=new T(function(){return B(A3(_9J,_aa,_ap,_ar));});return __continue;}else{return C > 19 ? new F(function(){return A3(_9J,_aa,_ap,_ar);}) : (++C,A3(_9J,_aa,_ap,_ar));}}else{var _at=_ar;_al=new T(function(){return B(A3(_9J,_aa,_ap,_ap));});_am=new T(function(){return B(A3(_a7,_ab,_aq,_ah));});_an=_at;return __continue;}})(_al,_am,_an));if(_ao!=__continue){return _ao;}}},_au=function(_av,_aw){while(1){var _ax=(function(_ay,_az){if(!B(_9Z(_ab,_az))){if(!B(A3(_6k,_aj,_az,_ai))){var _aA=new T(function(){return B(A3(_a7,_ab,new T(function(){return B(A3(_9P,_af,_az,_ai));}),_ah));});return _ak(new T(function(){return B(A3(_9J,_aa,_ay,_ay));}),_aA,_ay);}else{return E(_ay);}}else{_av=new T(function(){return B(A3(_9J,_aa,_ay,_ay));});_aw=new T(function(){return B(A3(_a7,_ab,_az,_ah));});return __continue;}})(_av,_aw);if(_ax!=__continue){return _ax;}}};return _au(_ac,_ad);}else{return C > 19 ? new F(function(){return A2(_9V,_aa,_7S);}) : (++C,A2(_9V,_aa,_7S));}}else{return E(_a6);}},_aB=new T(function(){return err(_a5);}),_aC=function(_aD){var _aE=I_decodeDouble(_aD);return new T2(0,new T1(1,_aE.b),_aE.a);},_aF=function(_aG,_aH){var _aI=E(_aG);return (_aI._==0)?_aI.a*Math.pow(2,_aH):I_toNumber(_aI.a)*Math.pow(2,_aH);},_aJ=function(_aK,_aL){var _aM=E(_aK);if(!_aM._){var _aN=_aM.a,_aO=E(_aL);return (_aO._==0)?_aN==_aO.a:(I_compareInt(_aO.a,_aN)==0)?true:false;}else{var _aP=_aM.a,_aQ=E(_aL);return (_aQ._==0)?(I_compareInt(_aP,_aQ.a)==0)?true:false:(I_compare(_aP,_aQ.a)==0)?true:false;}},_aR=function(_aS,_aT){while(1){var _aU=E(_aS);if(!_aU._){var _aV=E(_aU.a);if(_aV==(-2147483648)){_aS=new T1(1,I_fromInt(-2147483648));continue;}else{var _aW=E(_aT);if(!_aW._){var _aX=_aW.a;return new T2(0,new T1(0,quot(_aV,_aX)),new T1(0,_aV%_aX));}else{_aS=new T1(1,I_fromInt(_aV));_aT=_aW;continue;}}}else{var _aY=E(_aT);if(!_aY._){_aS=_aU;_aT=new T1(1,I_fromInt(_aY.a));continue;}else{var _aZ=I_quotRem(_aU.a,_aY.a);return new T2(0,new T1(1,_aZ.a),new T1(1,_aZ.b));}}}},_b0=function(_b1,_b2){var _b3=_aC(_b2),_b4=_b3.a,_b5=_b3.b,_b6=new T(function(){return _9l(new T(function(){return _9j(_b1);}));});if(_b5<0){var _b7= -_b5;if(_b7>=0){if(!_b7){var _b8=E(_7S);}else{var _b8=_9D(_9i,_b7);}if(!_aJ(_b8,new T1(0,0))){var _b9=_aR(_b4,_b8);return new T2(0,new T(function(){return B(A2(_9V,_b6,_b9.a));}),new T(function(){return _aF(_b9.b,_b5);}));}else{return E(_7E);}}else{return E(_aB);}}else{var _ba=new T(function(){var _bb=new T(function(){return B(_a9(_b6,_7Z,new T(function(){return B(A2(_9V,_b6,_9i));}),_b5));});return B(A3(_9J,_b6,new T(function(){return B(A2(_9V,_b6,_b4));}),_bb));});return new T2(0,_ba,0);}},_bc=function(_){return 0;},_bd=(function(x){console.log(x);}),_be=function(_){var _bf=_bd("Error decoding message data");return _bc(_);},_bg=function(_bh,_bi){while(1){var _bj=E(_bh);if(!_bj._){return (E(_bi)._==0)?1:0;}else{var _bk=E(_bi);if(!_bk._){return 2;}else{var _bl=E(_bj.a),_bm=E(_bk.a);if(_bl>=_bm){if(_bl!=_bm){return 2;}else{_bh=_bj.b;_bi=_bk.b;continue;}}else{return 0;}}}}},_bn=new T0(1),_bo=new T(function(){return unCStr("Failure in Data.Map.balanceL");}),_bp=new T(function(){var _bq=_;return err(_bo);}),_br=function(_bs,_bt,_bu,_bv){var _bw=E(_bv);if(!_bw._){var _bx=_bw.a,_by=E(_bu);if(!_by._){var _bz=_by.a,_bA=_by.b,_bB=_by.c;if(_bz<=(imul(3,_bx)|0)){return new T5(0,(1+_bz|0)+_bx|0,E(_bs),_bt,_by,_bw);}else{var _bC=E(_by.d);if(!_bC._){var _bD=_bC.a,_bE=E(_by.e);if(!_bE._){var _bF=_bE.a,_bG=_bE.b,_bH=_bE.c,_bI=_bE.d;if(_bF>=(imul(2,_bD)|0)){var _bJ=function(_bK){var _bL=E(_bE.e);return (_bL._==0)?new T5(0,(1+_bz|0)+_bx|0,E(_bG),_bH,E(new T5(0,(1+_bD|0)+_bK|0,E(_bA),_bB,_bC,E(_bI))),E(new T5(0,(1+_bx|0)+_bL.a|0,E(_bs),_bt,_bL,_bw))):new T5(0,(1+_bz|0)+_bx|0,E(_bG),_bH,E(new T5(0,(1+_bD|0)+_bK|0,E(_bA),_bB,_bC,E(_bI))),E(new T5(0,1+_bx|0,E(_bs),_bt,E(_bn),_bw)));},_bM=E(_bI);if(!_bM._){return _bJ(_bM.a);}else{return _bJ(0);}}else{return new T5(0,(1+_bz|0)+_bx|0,E(_bA),_bB,_bC,E(new T5(0,(1+_bx|0)+_bF|0,E(_bs),_bt,_bE,_bw)));}}else{return E(_bp);}}else{return E(_bp);}}}else{return new T5(0,1+_bx|0,E(_bs),_bt,E(_bn),_bw);}}else{var _bN=E(_bu);if(!_bN._){var _bO=_bN.a,_bP=_bN.b,_bQ=_bN.c,_bR=_bN.e,_bS=E(_bN.d);if(!_bS._){var _bT=_bS.a,_bU=E(_bR);if(!_bU._){var _bV=_bU.a,_bW=_bU.b,_bX=_bU.c,_bY=_bU.d;if(_bV>=(imul(2,_bT)|0)){var _bZ=function(_c0){var _c1=E(_bU.e);return (_c1._==0)?new T5(0,1+_bO|0,E(_bW),_bX,E(new T5(0,(1+_bT|0)+_c0|0,E(_bP),_bQ,_bS,E(_bY))),E(new T5(0,1+_c1.a|0,E(_bs),_bt,_c1,E(_bn)))):new T5(0,1+_bO|0,E(_bW),_bX,E(new T5(0,(1+_bT|0)+_c0|0,E(_bP),_bQ,_bS,E(_bY))),E(new T5(0,1,E(_bs),_bt,E(_bn),E(_bn))));},_c2=E(_bY);if(!_c2._){return _bZ(_c2.a);}else{return _bZ(0);}}else{return new T5(0,1+_bO|0,E(_bP),_bQ,_bS,E(new T5(0,1+_bV|0,E(_bs),_bt,_bU,E(_bn))));}}else{return new T5(0,3,E(_bP),_bQ,_bS,E(new T5(0,1,E(_bs),_bt,E(_bn),E(_bn))));}}else{var _c3=E(_bR);return (_c3._==0)?new T5(0,3,E(_c3.b),_c3.c,E(new T5(0,1,E(_bP),_bQ,E(_bn),E(_bn))),E(new T5(0,1,E(_bs),_bt,E(_bn),E(_bn)))):new T5(0,2,E(_bs),_bt,_bN,E(_bn));}}else{return new T5(0,1,E(_bs),_bt,E(_bn),E(_bn));}}},_c4=new T(function(){return unCStr("Failure in Data.Map.balanceR");}),_c5=new T(function(){var _c6=_;return err(_c4);}),_c7=function(_c8,_c9,_ca,_cb){var _cc=E(_ca);if(!_cc._){var _cd=_cc.a,_ce=E(_cb);if(!_ce._){var _cf=_ce.a,_cg=_ce.b,_ch=_ce.c;if(_cf<=(imul(3,_cd)|0)){return new T5(0,(1+_cd|0)+_cf|0,E(_c8),_c9,_cc,_ce);}else{var _ci=E(_ce.d);if(!_ci._){var _cj=_ci.a,_ck=_ci.b,_cl=_ci.c,_cm=_ci.d,_cn=E(_ce.e);if(!_cn._){var _co=_cn.a;if(_cj>=(imul(2,_co)|0)){var _cp=function(_cq){var _cr=E(_c8),_cs=E(_ci.e);return (_cs._==0)?new T5(0,(1+_cd|0)+_cf|0,E(_ck),_cl,E(new T5(0,(1+_cd|0)+_cq|0,_cr,_c9,_cc,E(_cm))),E(new T5(0,(1+_co|0)+_cs.a|0,E(_cg),_ch,_cs,_cn))):new T5(0,(1+_cd|0)+_cf|0,E(_ck),_cl,E(new T5(0,(1+_cd|0)+_cq|0,_cr,_c9,_cc,E(_cm))),E(new T5(0,1+_co|0,E(_cg),_ch,E(_bn),_cn)));},_ct=E(_cm);if(!_ct._){return _cp(_ct.a);}else{return _cp(0);}}else{return new T5(0,(1+_cd|0)+_cf|0,E(_cg),_ch,E(new T5(0,(1+_cd|0)+_cj|0,E(_c8),_c9,_cc,_ci)),_cn);}}else{return E(_c5);}}else{return E(_c5);}}}else{return new T5(0,1+_cd|0,E(_c8),_c9,_cc,E(_bn));}}else{var _cu=E(_cb);if(!_cu._){var _cv=_cu.a,_cw=_cu.b,_cx=_cu.c,_cy=_cu.e,_cz=E(_cu.d);if(!_cz._){var _cA=_cz.a,_cB=_cz.b,_cC=_cz.c,_cD=_cz.d,_cE=E(_cy);if(!_cE._){var _cF=_cE.a;if(_cA>=(imul(2,_cF)|0)){var _cG=function(_cH){var _cI=E(_c8),_cJ=E(_cz.e);return (_cJ._==0)?new T5(0,1+_cv|0,E(_cB),_cC,E(new T5(0,1+_cH|0,_cI,_c9,E(_bn),E(_cD))),E(new T5(0,(1+_cF|0)+_cJ.a|0,E(_cw),_cx,_cJ,_cE))):new T5(0,1+_cv|0,E(_cB),_cC,E(new T5(0,1+_cH|0,_cI,_c9,E(_bn),E(_cD))),E(new T5(0,1+_cF|0,E(_cw),_cx,E(_bn),_cE)));},_cK=E(_cD);if(!_cK._){return _cG(_cK.a);}else{return _cG(0);}}else{return new T5(0,1+_cv|0,E(_cw),_cx,E(new T5(0,1+_cA|0,E(_c8),_c9,E(_bn),_cz)),_cE);}}else{return new T5(0,3,E(_cB),_cC,E(new T5(0,1,E(_c8),_c9,E(_bn),E(_bn))),E(new T5(0,1,E(_cw),_cx,E(_bn),E(_bn))));}}else{var _cL=E(_cy);return (_cL._==0)?new T5(0,3,E(_cw),_cx,E(new T5(0,1,E(_c8),_c9,E(_bn),E(_bn))),_cL):new T5(0,2,E(_c8),_c9,E(_bn),_cu);}}else{return new T5(0,1,E(_c8),_c9,E(_bn),E(_bn));}}},_cM=function(_cN,_cO,_cP){var _cQ=E(_cN),_cR=E(_cO),_cS=E(_cP);if(!_cS._){var _cT=_cS.b,_cU=_cS.c,_cV=_cS.d,_cW=_cS.e;switch(_bg(_cQ,_cT)){case 0:return _br(_cT,_cU,_cM(_cQ,_cR,_cV),_cW);case 1:return new T5(0,_cS.a,_cQ,_cR,E(_cV),E(_cW));default:return _c7(_cT,_cU,_cV,_cM(_cQ,_cR,_cW));}}else{return new T5(0,1,_cQ,_cR,E(_bn),E(_bn));}},_cX=function(_cY,_cZ){while(1){var _d0=E(_cZ);if(!_d0._){return E(_cY);}else{var _d1=E(_d0.a),_d2=_cM(_d1.a,_d1.b,_cY);_cY=_d2;_cZ=_d0.b;continue;}}},_d3=function(_d4,_d5){return new T5(0,1,E(_d4),_d5,E(_bn),E(_bn));},_d6=function(_d7,_d8,_d9){var _da=E(_d9);if(!_da._){return _c7(_da.b,_da.c,_da.d,_d6(_d7,_d8,_da.e));}else{return _d3(_d7,_d8);}},_db=function(_dc,_dd,_de){var _df=E(_de);if(!_df._){return _br(_df.b,_df.c,_db(_dc,_dd,_df.d),_df.e);}else{return _d3(_dc,_dd);}},_dg=function(_dh,_di,_dj,_dk,_dl,_dm,_dn){return _br(_dk,_dl,_db(_dh,_di,_dm),_dn);},_do=function(_dp,_dq,_dr,_ds,_dt,_du,_dv,_dw){var _dx=E(_dr);if(!_dx._){var _dy=_dx.a,_dz=_dx.b,_dA=_dx.c,_dB=_dx.d,_dC=_dx.e;if((imul(3,_dy)|0)>=_ds){if((imul(3,_ds)|0)>=_dy){return new T5(0,(_dy+_ds|0)+1|0,E(_dp),_dq,_dx,E(new T5(0,_ds,E(_dt),_du,E(_dv),E(_dw))));}else{return _c7(_dz,_dA,_dB,B(_do(_dp,_dq,_dC,_ds,_dt,_du,_dv,_dw)));}}else{return _br(_dt,_du,B(_dD(_dp,_dq,_dy,_dz,_dA,_dB,_dC,_dv)),_dw);}}else{return _dg(_dp,_dq,_ds,_dt,_du,_dv,_dw);}},_dD=function(_dE,_dF,_dG,_dH,_dI,_dJ,_dK,_dL){var _dM=E(_dL);if(!_dM._){var _dN=_dM.a,_dO=_dM.b,_dP=_dM.c,_dQ=_dM.d,_dR=_dM.e;if((imul(3,_dG)|0)>=_dN){if((imul(3,_dN)|0)>=_dG){return new T5(0,(_dG+_dN|0)+1|0,E(_dE),_dF,E(new T5(0,_dG,E(_dH),_dI,E(_dJ),E(_dK))),_dM);}else{return _c7(_dH,_dI,_dJ,B(_do(_dE,_dF,_dK,_dN,_dO,_dP,_dQ,_dR)));}}else{return _br(_dO,_dP,B(_dD(_dE,_dF,_dG,_dH,_dI,_dJ,_dK,_dQ)),_dR);}}else{return _d6(_dE,_dF,new T5(0,_dG,E(_dH),_dI,E(_dJ),E(_dK)));}},_dS=function(_dT,_dU,_dV,_dW){var _dX=E(_dV);if(!_dX._){var _dY=_dX.a,_dZ=_dX.b,_e0=_dX.c,_e1=_dX.d,_e2=_dX.e,_e3=E(_dW);if(!_e3._){var _e4=_e3.a,_e5=_e3.b,_e6=_e3.c,_e7=_e3.d,_e8=_e3.e;if((imul(3,_dY)|0)>=_e4){if((imul(3,_e4)|0)>=_dY){return new T5(0,(_dY+_e4|0)+1|0,E(_dT),_dU,_dX,_e3);}else{return _c7(_dZ,_e0,_e1,B(_do(_dT,_dU,_e2,_e4,_e5,_e6,_e7,_e8)));}}else{return _br(_e5,_e6,B(_dD(_dT,_dU,_dY,_dZ,_e0,_e1,_e2,_e7)),_e8);}}else{return _d6(_dT,_dU,_dX);}}else{return _db(_dT,_dU,_dW);}},_e9=function(_ea,_eb){var _ec=E(_eb);if(!_ec._){return new T3(0,_bn,__Z,__Z);}else{var _ed=E(_ea);if(_ed==1){var _ee=E(_ec.a),_ef=_ee.a,_eg=_ee.b,_eh=E(_ec.b);return (_eh._==0)?new T3(0,new T(function(){return new T5(0,1,E(_ef),E(_eg),E(_bn),E(_bn));}),__Z,__Z):(_bg(_ef,E(_eh.a).a)==0)?new T3(0,new T(function(){return new T5(0,1,E(_ef),E(_eg),E(_bn),E(_bn));}),_eh,__Z):new T3(0,new T(function(){return new T5(0,1,E(_ef),E(_eg),E(_bn),E(_bn));}),__Z,_eh);}else{var _ei=_e9(_ed>>1,_ec),_ej=_ei.a,_ek=_ei.c,_el=E(_ei.b);if(!_el._){return new T3(0,_ej,__Z,_ek);}else{var _em=E(_el.a),_en=_em.a,_eo=_em.b,_ep=E(_el.b);if(!_ep._){return new T3(0,new T(function(){return _d6(_en,E(_eo),_ej);}),__Z,_ek);}else{if(!_bg(_en,E(_ep.a).a)){var _eq=_e9(_ed>>1,_ep);return new T3(0,new T(function(){return B(_dS(_en,E(_eo),_ej,_eq.a));}),_eq.b,_eq.c);}else{return new T3(0,_ej,__Z,_el);}}}}}},_er=function(_es,_et,_eu){while(1){var _ev=E(_eu);if(!_ev._){return E(_et);}else{var _ew=E(_ev.a),_ex=_ew.a,_ey=_ew.b,_ez=E(_ev.b);if(!_ez._){return _d6(_ex,E(_ey),_et);}else{if(!_bg(_ex,E(_ez.a).a)){var _eA=_e9(_es,_ez),_eB=_eA.a,_eC=E(_eA.c);if(!_eC._){var _eD=_es<<1,_eE=B(_dS(_ex,E(_ey),_et,_eB));_es=_eD;_et=_eE;_eu=_eA.b;continue;}else{return _cX(B(_dS(_ex,E(_ey),_et,_eB)),_eC);}}else{return _cX(_et,_ev);}}}}},_eF=function(_eG){var _eH=E(_eG);if(!_eH._){return new T0(1);}else{var _eI=E(_eH.a),_eJ=_eI.a,_eK=_eI.b,_eL=E(_eH.b);if(!_eL._){return new T5(0,1,E(_eJ),E(_eK),E(_bn),E(_bn));}else{if(!_bg(_eJ,E(_eL.a).a)){return C > 19 ? new F(function(){return _er(1,new T5(0,1,E(_eJ),E(_eK),E(_bn),E(_bn)),_eL);}) : (++C,_er(1,new T5(0,1,E(_eJ),E(_eK),E(_bn),E(_bn)),_eL));}else{return _cX(new T5(0,1,E(_eJ),E(_eK),E(_bn),E(_bn)),_eL);}}}},_eM=function(_){var _eN=_bd("Other");return __Z;},_eO=function(_eP,_){var _eQ=E(_eP);if(!_eQ._){return __Z;}else{var _eR=B(A1(_eQ.a,_)),_eS=_eO(_eQ.b,_);return new T2(1,_eR,_eS);}},_eT=new T(function(){return JSON.stringify;}),_eU=function(_eV,_eW){var _eX=E(_eW);switch(_eX._){case 0:return new T2(0,new T(function(){return jsShow(_eX.a);}),_eV);case 1:return new T2(0,new T(function(){var _eY=E(_eT)(_eX.a);return String(_eY);}),_eV);case 2:return (!E(_eX.a))?new T2(0,"false",_eV):new T2(0,"true",_eV);case 3:var _eZ=E(_eX.a);if(!_eZ._){return new T2(0,"[",new T2(1,"]",_eV));}else{var _f0=new T(function(){var _f1=new T(function(){var _f2=function(_f3){var _f4=E(_f3);if(!_f4._){return E(new T2(1,"]",_eV));}else{var _f5=new T(function(){var _f6=_eU(new T(function(){return _f2(_f4.b);}),_f4.a);return new T2(1,_f6.a,_f6.b);});return new T2(1,",",_f5);}};return _f2(_eZ.b);}),_f7=_eU(_f1,_eZ.a);return new T2(1,_f7.a,_f7.b);});return new T2(0,"[",_f0);}break;case 4:var _f8=E(_eX.a);if(!_f8._){return new T2(0,"{",new T2(1,"}",_eV));}else{var _f9=E(_f8.a),_fa=new T(function(){var _fb=new T(function(){var _fc=function(_fd){var _fe=E(_fd);if(!_fe._){return E(new T2(1,"}",_eV));}else{var _ff=E(_fe.a),_fg=new T(function(){var _fh=_eU(new T(function(){return _fc(_fe.b);}),_ff.b);return new T2(1,_fh.a,_fh.b);});return new T2(1,",",new T2(1,"\"",new T2(1,_ff.a,new T2(1,"\"",new T2(1,":",_fg)))));}};return _fc(_f8.b);}),_fi=_eU(_fb,_f9.b);return new T2(1,_fi.a,_fi.b);});return new T2(0,"{",new T2(1,new T(function(){var _fj=E(_eT)(E(_f9.a));return String(_fj);}),new T2(1,":",_fa)));}break;default:return new T2(0,"null",_eV);}},_fk=new T(function(){return toJSStr(__Z);}),_fl=function(_fm){var _fn=_eU(__Z,_fm),_fo=jsCat(new T2(1,_fn.a,_fn.b),E(_fk));return fromJSStr(_fo);},_fp=function(_){var _fq=_bd("Error decoding cost tree data");return _bc(_);},_fr=new T(function(){return err(new T(function(){return unCStr("Maybe.fromJust: Nothing");}));}),_fs=function(_ft,_fu,_fv){while(1){var _fw=E(_fv);if(!_fw._){return __Z;}else{var _fx=E(_fw.a);if(!B(A3(_6k,_ft,_fu,_fx.a))){_fv=_fw.b;continue;}else{return new T1(1,_fx.b);}}}},_fy=new T(function(){return unCStr("main");}),_fz=new T(function(){return unCStr("Ajax");}),_fA=new T(function(){return unCStr("ServerMessageException");}),_fB=function(_fC){return E(new T5(0,new Long(2796709153,857663197,true),new Long(2290229150,2001624562,true),new T5(0,new Long(2796709153,857663197,true),new Long(2290229150,2001624562,true),_fy,_fz,_fA),__Z,__Z));},_fD=new T(function(){return unCStr("SME ");}),_fE=function(_fF,_fG,_fH){if(_fF<11){return _0(_fD,new T2(1,34,new T(function(){return _3g(_fG,new T2(1,34,_fH));})));}else{var _fI=new T(function(){return _0(_fD,new T2(1,34,new T(function(){return _3g(_fG,new T2(1,34,new T2(1,41,_fH)));})));});return new T2(1,40,_fI);}},_fJ=function(_fK){return _fE(0,E(_fK).a,__Z);},_fL=function(_fM,_fN){return _fE(0,E(_fM).a,_fN);},_fO=new T(function(){return new T5(0,_fB,new T3(0,function(_fP,_fQ,_fR){return _fE(E(_fP),E(_fQ).a,_fR);},_fJ,function(_4g,_4h){return _3p(_fL,_4g,_4h);}),function(_4h){return new T2(0,_fO,_4h);},function(_fS){var _fT=E(_fS);return _7b(_79(_fT.a),_fB,_fT.b);},_fJ);}),_fU=function(_fV){return E(E(_fV).c);},_fW=function(_fX,_fY){return die(new T(function(){return B(A2(_fU,_fY,_fX));}));},_fZ=function(_g0,_7D){return _fW(_g0,_7D);},_g1=new T(function(){return _fZ(new T1(0,new T(function(){return unCStr("Error decoding cost tree data");})),_fO);}),_g2=new T(function(){return unCStr("base");}),_g3=new T(function(){return unCStr("Control.Exception.Base");}),_g4=new T(function(){return unCStr("PatternMatchFail");}),_g5=function(_g6){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_g2,_g3,_g4),__Z,__Z));},_g7=function(_g8){return E(E(_g8).a);},_g9=function(_ga,_gb){return _0(E(_ga).a,_gb);},_gc=new T(function(){return new T5(0,_g5,new T3(0,function(_gd,_ge,_gf){return _0(E(_ge).a,_gf);},_g7,function(_gg,_gh){return _3p(_g9,_gg,_gh);}),function(_gi){return new T2(0,_gc,_gi);},function(_gj){var _gk=E(_gj);return _7b(_79(_gk.a),_g5,_gk.b);},_g7);}),_gl=new T(function(){return unCStr("Non-exhaustive patterns in");}),_gm=function(_gn,_go){var _gp=E(_go);if(!_gp._){return new T2(0,__Z,__Z);}else{var _gq=_gp.a;if(!B(A1(_gn,_gq))){return new T2(0,__Z,_gp);}else{var _gr=new T(function(){var _gs=_gm(_gn,_gp.b);return new T2(0,_gs.a,_gs.b);});return new T2(0,new T2(1,_gq,new T(function(){return E(E(_gr).a);})),new T(function(){return E(E(_gr).b);}));}}},_gt=new T(function(){return unCStr("\n");}),_gu=function(_gv){return (E(_gv)==124)?false:true;},_gw=function(_gx,_gy){var _gz=_gm(_gu,unCStr(_gx)),_gA=_gz.a,_gB=function(_gC,_gD){var _gE=new T(function(){var _gF=new T(function(){return _0(_gy,new T(function(){return _0(_gD,_gt);},1));});return unAppCStr(": ",_gF);},1);return _0(_gC,_gE);},_gG=E(_gz.b);if(!_gG._){return _gB(_gA,__Z);}else{if(E(_gG.a)==124){return _gB(_gA,new T2(1,32,_gG.b));}else{return _gB(_gA,__Z);}}},_gH=function(_gI){return _fZ(new T1(0,new T(function(){return _gw(_gI,_gl);})),_gc);},_gJ=function(_gK){return C > 19 ? new F(function(){return _gH("Ajax.hs:94:21-91|lambda");}) : (++C,_gH("Ajax.hs:94:21-91|lambda"));},_gL=function(_gM){var _gN=E(_gM);if(!_gN._){var _gO=_gN.a,_gP=_gO&4294967295;return (_gO>=_gP)?_gP:_gP-1|0;}else{return C > 19 ? new F(function(){return _gH("Ajax.hs:94:56-74|lambda");}) : (++C,_gH("Ajax.hs:94:56-74|lambda"));}},_gQ=function(_gR){return C > 19 ? new F(function(){return _gL(_gR);}) : (++C,_gL(_gR));},_gS=function(_gT,_gU){var _gV=E(_gU);return (_gV._==0)?__Z:new T2(1,new T(function(){return B(A1(_gT,_gV.a));}),new T(function(){return _gS(_gT,_gV.b);}));},_gW=function(_gX){var _gY=E(_gX);if(_gY._==3){var _gZ=E(_gY.a);if(!_gZ._){return C > 19 ? new F(function(){return _gJ(_);}) : (++C,_gJ(_));}else{var _h0=E(_gZ.a);if(_h0._==3){var _h1=E(_gZ.b);if(!_h1._){return C > 19 ? new F(function(){return _gJ(_);}) : (++C,_gJ(_));}else{var _h2=E(_h1.a);if(_h2._==1){if(!E(_h1.b)._){return new T2(0,new T(function(){return _gS(_gQ,_h0.a);}),new T(function(){return fromJSStr(_h2.a);}));}else{return C > 19 ? new F(function(){return _gJ(_);}) : (++C,_gJ(_));}}else{return C > 19 ? new F(function(){return _gJ(_);}) : (++C,_gJ(_));}}}else{return C > 19 ? new F(function(){return _gJ(_);}) : (++C,_gJ(_));}}}else{return C > 19 ? new F(function(){return _gJ(_);}) : (++C,_gJ(_));}},_h3=function(_h4){var _h5=B(_gW(_h4));return new T2(0,_h5.a,_h5.b);},_h6=new T(function(){return B(_gH("Ajax.hs:132:5-39|function getJustNum"));}),_h7=new T(function(){return B(_gH("Ajax.hs:133:5-42|function getJustStr"));}),_h8=function(_h9,_){var _ha=_bd(toJSStr(unAppCStr("Trying to decode cost tree ",new T(function(){return _fl(_h9);})))),_hb=E(_h9);if(_hb._==4){var _hc=_hb.a,_hd=_fs(_6q,"lin",_hc);if(!_hd._){return E(_fr);}else{var _he=function(_,_hf){var _hg=_fs(_6q,"score",_hc);if(!_hg._){var _hh=_fp(_);return E(_g1);}else{var _hi=_fs(_6q,"tree",_hc);if(!_hi._){var _hj=_fp(_);return E(_g1);}else{return new T3(0,new T(function(){var _hk=E(_hg.a);if(!_hk._){var _hl=_b0(_7Z,_hk.a),_hm=_hl.a;if(E(_hl.b)>=0){return E(_hm);}else{return E(_hm)-1|0;}}else{return E(_h6);}}),_hf,new T(function(){var _hn=E(_hi.a);if(_hn._==1){return fromJSStr(_hn.a);}else{return E(_h7);}}));}}},_ho=E(_hd.a);if(_ho._==3){return _he(_,new T(function(){return _gS(_h3,_ho.a);}));}else{return _he(_,__Z);}}}else{return E(_fr);}},_hp=new T(function(){return B(_gH("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_hq=function(_hr,_hs){while(1){var _ht=(function(_hu,_hv){var _hw=E(_hu);switch(_hw._){case 0:var _hx=E(_hv);if(!_hx._){return __Z;}else{_hr=B(A1(_hw.a,_hx.a));_hs=_hx.b;return __continue;}break;case 1:var _hy=B(A1(_hw.a,_hv)),_hz=_hv;_hr=_hy;_hs=_hz;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_hw.a,_hv),new T(function(){return _hq(_hw.b,_hv);}));default:return E(_hw.a);}})(_hr,_hs);if(_ht!=__continue){return _ht;}}},_hA=function(_hB,_hC){var _hD=function(_hE){var _hF=E(_hC);if(_hF._==3){return new T2(3,_hF.a,new T(function(){return _hA(_hB,_hF.b);}));}else{var _hG=E(_hB);if(_hG._==2){return _hF;}else{if(_hF._==2){return _hG;}else{var _hH=function(_hI){if(_hF._==4){var _hJ=function(_hK){return new T1(4,new T(function(){return _0(_hq(_hG,_hK),_hF.a);}));};return new T1(1,_hJ);}else{if(_hG._==1){var _hL=_hG.a;if(!_hF._){return new T1(1,function(_hM){return _hA(B(A1(_hL,_hM)),_hF);});}else{var _hN=function(_hO){return _hA(B(A1(_hL,_hO)),new T(function(){return B(A1(_hF.a,_hO));}));};return new T1(1,_hN);}}else{if(!_hF._){return E(_hp);}else{var _hP=function(_hQ){return _hA(_hG,new T(function(){return B(A1(_hF.a,_hQ));}));};return new T1(1,_hP);}}}};switch(_hG._){case 1:if(_hF._==4){var _hR=function(_hS){return new T1(4,new T(function(){return _0(_hq(B(A1(_hG.a,_hS)),_hS),_hF.a);}));};return new T1(1,_hR);}else{return _hH(_);}break;case 4:var _hT=_hG.a;switch(_hF._){case 0:var _hU=function(_hV){var _hW=new T(function(){return _0(_hT,new T(function(){return _hq(_hF,_hV);},1));});return new T1(4,_hW);};return new T1(1,_hU);case 1:var _hX=function(_hY){var _hZ=new T(function(){return _0(_hT,new T(function(){return _hq(B(A1(_hF.a,_hY)),_hY);},1));});return new T1(4,_hZ);};return new T1(1,_hX);default:return new T1(4,new T(function(){return _0(_hT,_hF.a);}));}break;default:return _hH(_);}}}}},_i0=E(_hB);switch(_i0._){case 0:var _i1=E(_hC);if(!_i1._){var _i2=function(_i3){return _hA(B(A1(_i0.a,_i3)),new T(function(){return B(A1(_i1.a,_i3));}));};return new T1(0,_i2);}else{return _hD(_);}break;case 3:return new T2(3,_i0.a,new T(function(){return _hA(_i0.b,_hC);}));default:return _hD(_);}},_i4=new T(function(){return unCStr("(");}),_i5=new T(function(){return unCStr(")");}),_i6=function(_i7,_i8){while(1){var _i9=E(_i7);if(!_i9._){return (E(_i8)._==0)?true:false;}else{var _ia=E(_i8);if(!_ia._){return false;}else{if(E(_i9.a)!=E(_ia.a)){return false;}else{_i7=_i9.b;_i8=_ia.b;continue;}}}}},_ib=new T2(0,function(_ic,_id){return E(_ic)==E(_id);},function(_ie,_if){return E(_ie)!=E(_if);}),_ig=function(_ih,_ii){while(1){var _ij=E(_ih);if(!_ij._){return (E(_ii)._==0)?true:false;}else{var _ik=E(_ii);if(!_ik._){return false;}else{if(E(_ij.a)!=E(_ik.a)){return false;}else{_ih=_ij.b;_ii=_ik.b;continue;}}}}},_il=function(_im,_in){return (!_ig(_im,_in))?true:false;},_io=function(_ip,_iq){var _ir=E(_ip);switch(_ir._){case 0:return new T1(0,function(_is){return C > 19 ? new F(function(){return _io(B(A1(_ir.a,_is)),_iq);}) : (++C,_io(B(A1(_ir.a,_is)),_iq));});case 1:return new T1(1,function(_it){return C > 19 ? new F(function(){return _io(B(A1(_ir.a,_it)),_iq);}) : (++C,_io(B(A1(_ir.a,_it)),_iq));});case 2:return new T0(2);case 3:return _hA(B(A1(_iq,_ir.a)),new T(function(){return B(_io(_ir.b,_iq));}));default:var _iu=function(_iv){var _iw=E(_iv);if(!_iw._){return __Z;}else{var _ix=E(_iw.a);return _0(_hq(B(A1(_iq,_ix.a)),_ix.b),new T(function(){return _iu(_iw.b);},1));}},_iy=_iu(_ir.a);return (_iy._==0)?new T0(2):new T1(4,_iy);}},_iz=new T0(2),_iA=function(_iB){return new T2(3,_iB,_iz);},_iC=function(_iD,_iE){var _iF=E(_iD);if(!_iF){return C > 19 ? new F(function(){return A1(_iE,0);}) : (++C,A1(_iE,0));}else{var _iG=new T(function(){return B(_iC(_iF-1|0,_iE));});return new T1(0,function(_iH){return E(_iG);});}},_iI=function(_iJ,_iK,_iL){var _iM=new T(function(){return B(A1(_iJ,_iA));}),_iN=function(_iO,_iP,_iQ,_iR){while(1){var _iS=B((function(_iT,_iU,_iV,_iW){var _iX=E(_iT);switch(_iX._){case 0:var _iY=E(_iU);if(!_iY._){return C > 19 ? new F(function(){return A1(_iK,_iW);}) : (++C,A1(_iK,_iW));}else{var _iZ=_iV+1|0,_j0=_iW;_iO=B(A1(_iX.a,_iY.a));_iP=_iY.b;_iQ=_iZ;_iR=_j0;return __continue;}break;case 1:var _j1=B(A1(_iX.a,_iU)),_j2=_iU,_iZ=_iV,_j0=_iW;_iO=_j1;_iP=_j2;_iQ=_iZ;_iR=_j0;return __continue;case 2:return C > 19 ? new F(function(){return A1(_iK,_iW);}) : (++C,A1(_iK,_iW));break;case 3:var _j3=new T(function(){return B(_io(_iX,_iW));});return C > 19 ? new F(function(){return _iC(_iV,function(_j4){return E(_j3);});}) : (++C,_iC(_iV,function(_j4){return E(_j3);}));break;default:return C > 19 ? new F(function(){return _io(_iX,_iW);}) : (++C,_io(_iX,_iW));}})(_iO,_iP,_iQ,_iR));if(_iS!=__continue){return _iS;}}};return function(_j5){return _iN(_iM,_j5,0,_iL);};},_j6=function(_j7){return C > 19 ? new F(function(){return A1(_j7,__Z);}) : (++C,A1(_j7,__Z));},_j8=function(_j9,_ja){var _jb=function(_jc){var _jd=E(_jc);if(!_jd._){return _j6;}else{var _je=_jd.a;if(!B(A1(_j9,_je))){return _j6;}else{var _jf=new T(function(){return _jb(_jd.b);}),_jg=function(_jh){var _ji=new T(function(){return B(A1(_jf,function(_jj){return C > 19 ? new F(function(){return A1(_jh,new T2(1,_je,_jj));}) : (++C,A1(_jh,new T2(1,_je,_jj)));}));});return new T1(0,function(_jk){return E(_ji);});};return _jg;}}};return function(_jl){return C > 19 ? new F(function(){return A2(_jb,_jl,_ja);}) : (++C,A2(_jb,_jl,_ja));};},_jm=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_jn=function(_jo,_jp){var _jq=function(_jr,_js){var _jt=E(_jr);if(!_jt._){var _ju=new T(function(){return B(A1(_js,__Z));});return function(_jv){return C > 19 ? new F(function(){return A1(_jv,_ju);}) : (++C,A1(_jv,_ju));};}else{var _jw=E(_jt.a),_jx=function(_jy){var _jz=new T(function(){return _jq(_jt.b,function(_jA){return C > 19 ? new F(function(){return A1(_js,new T2(1,_jy,_jA));}) : (++C,A1(_js,new T2(1,_jy,_jA)));});}),_jB=function(_jC){var _jD=new T(function(){return B(A1(_jz,_jC));});return new T1(0,function(_jE){return E(_jD);});};return _jB;};switch(E(_jo)){case 8:if(48>_jw){var _jF=new T(function(){return B(A1(_js,__Z));});return function(_jG){return C > 19 ? new F(function(){return A1(_jG,_jF);}) : (++C,A1(_jG,_jF));};}else{if(_jw>55){var _jH=new T(function(){return B(A1(_js,__Z));});return function(_jI){return C > 19 ? new F(function(){return A1(_jI,_jH);}) : (++C,A1(_jI,_jH));};}else{return _jx(_jw-48|0);}}break;case 10:if(48>_jw){var _jJ=new T(function(){return B(A1(_js,__Z));});return function(_jK){return C > 19 ? new F(function(){return A1(_jK,_jJ);}) : (++C,A1(_jK,_jJ));};}else{if(_jw>57){var _jL=new T(function(){return B(A1(_js,__Z));});return function(_jM){return C > 19 ? new F(function(){return A1(_jM,_jL);}) : (++C,A1(_jM,_jL));};}else{return _jx(_jw-48|0);}}break;case 16:if(48>_jw){if(97>_jw){if(65>_jw){var _jN=new T(function(){return B(A1(_js,__Z));});return function(_jO){return C > 19 ? new F(function(){return A1(_jO,_jN);}) : (++C,A1(_jO,_jN));};}else{if(_jw>70){var _jP=new T(function(){return B(A1(_js,__Z));});return function(_jQ){return C > 19 ? new F(function(){return A1(_jQ,_jP);}) : (++C,A1(_jQ,_jP));};}else{return _jx((_jw-65|0)+10|0);}}}else{if(_jw>102){if(65>_jw){var _jR=new T(function(){return B(A1(_js,__Z));});return function(_jS){return C > 19 ? new F(function(){return A1(_jS,_jR);}) : (++C,A1(_jS,_jR));};}else{if(_jw>70){var _jT=new T(function(){return B(A1(_js,__Z));});return function(_jU){return C > 19 ? new F(function(){return A1(_jU,_jT);}) : (++C,A1(_jU,_jT));};}else{return _jx((_jw-65|0)+10|0);}}}else{return _jx((_jw-97|0)+10|0);}}}else{if(_jw>57){if(97>_jw){if(65>_jw){var _jV=new T(function(){return B(A1(_js,__Z));});return function(_jW){return C > 19 ? new F(function(){return A1(_jW,_jV);}) : (++C,A1(_jW,_jV));};}else{if(_jw>70){var _jX=new T(function(){return B(A1(_js,__Z));});return function(_jY){return C > 19 ? new F(function(){return A1(_jY,_jX);}) : (++C,A1(_jY,_jX));};}else{return _jx((_jw-65|0)+10|0);}}}else{if(_jw>102){if(65>_jw){var _jZ=new T(function(){return B(A1(_js,__Z));});return function(_k0){return C > 19 ? new F(function(){return A1(_k0,_jZ);}) : (++C,A1(_k0,_jZ));};}else{if(_jw>70){var _k1=new T(function(){return B(A1(_js,__Z));});return function(_k2){return C > 19 ? new F(function(){return A1(_k2,_k1);}) : (++C,A1(_k2,_k1));};}else{return _jx((_jw-65|0)+10|0);}}}else{return _jx((_jw-97|0)+10|0);}}}else{return _jx(_jw-48|0);}}break;default:return E(_jm);}}},_k3=function(_k4){var _k5=E(_k4);if(!_k5._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_jp,_k5);}) : (++C,A1(_jp,_k5));}};return function(_k6){return C > 19 ? new F(function(){return A3(_jq,_k6,_1C,_k3);}) : (++C,A3(_jq,_k6,_1C,_k3));};},_k7=function(_k8){var _k9=function(_ka){return C > 19 ? new F(function(){return A1(_k8,new T1(5,new T2(0,8,_ka)));}) : (++C,A1(_k8,new T1(5,new T2(0,8,_ka))));},_kb=function(_kc){return C > 19 ? new F(function(){return A1(_k8,new T1(5,new T2(0,16,_kc)));}) : (++C,A1(_k8,new T1(5,new T2(0,16,_kc))));},_kd=function(_ke){switch(E(_ke)){case 79:return new T1(1,_jn(8,_k9));case 88:return new T1(1,_jn(16,_kb));case 111:return new T1(1,_jn(8,_k9));case 120:return new T1(1,_jn(16,_kb));default:return new T0(2);}};return function(_kf){return (E(_kf)==48)?E(new T1(0,_kd)):new T0(2);};},_kg=function(_kh){return new T1(0,_k7(_kh));},_ki=function(_kj){return C > 19 ? new F(function(){return A1(_kj,__Z);}) : (++C,A1(_kj,__Z));},_kk=function(_kl){return C > 19 ? new F(function(){return A1(_kl,__Z);}) : (++C,A1(_kl,__Z));},_km=function(_kn,_ko){while(1){var _kp=E(_kn);if(!_kp._){var _kq=_kp.a,_kr=E(_ko);if(!_kr._){var _ks=_kr.a,_kt=addC(_kq,_ks);if(!E(_kt.b)){return new T1(0,_kt.a);}else{_kn=new T1(1,I_fromInt(_kq));_ko=new T1(1,I_fromInt(_ks));continue;}}else{_kn=new T1(1,I_fromInt(_kq));_ko=_kr;continue;}}else{var _ku=E(_ko);if(!_ku._){_kn=_kp;_ko=new T1(1,I_fromInt(_ku.a));continue;}else{return new T1(1,I_add(_kp.a,_ku.a));}}}},_kv=new T(function(){return _km(new T1(0,2147483647),new T1(0,1));}),_kw=function(_kx){var _ky=E(_kx);if(!_ky._){var _kz=E(_ky.a);return (_kz==(-2147483648))?E(_kv):new T1(0, -_kz);}else{return new T1(1,I_negate(_ky.a));}},_kA=new T1(0,10),_kB=function(_kC,_kD){while(1){var _kE=E(_kC);if(!_kE._){return E(_kD);}else{var _kF=_kD+1|0;_kC=_kE.b;_kD=_kF;continue;}}},_kG=function(_kH){return _7Q(E(_kH));},_kI=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_kJ=function(_kK,_kL){var _kM=E(_kL);if(!_kM._){return __Z;}else{var _kN=E(_kM.b);return (_kN._==0)?E(_kI):new T2(1,_km(_9n(_kM.a,_kK),_kN.a),new T(function(){return _kJ(_kK,_kN.b);}));}},_kO=new T1(0,0),_kP=function(_kQ,_kR,_kS){while(1){var _kT=(function(_kU,_kV,_kW){var _kX=E(_kW);if(!_kX._){return E(_kO);}else{if(!E(_kX.b)._){return E(_kX.a);}else{var _kY=E(_kV);if(_kY<=40){var _kZ=function(_l0,_l1){while(1){var _l2=E(_l1);if(!_l2._){return E(_l0);}else{var _l3=_km(_9n(_l0,_kU),_l2.a);_l0=_l3;_l1=_l2.b;continue;}}};return _kZ(_kO,_kX);}else{var _l4=_9n(_kU,_kU);if(!(_kY%2)){var _l5=_kJ(_kU,_kX);_kQ=_l4;_kR=quot(_kY+1|0,2);_kS=_l5;return __continue;}else{var _l5=_kJ(_kU,new T2(1,_kO,_kX));_kQ=_l4;_kR=quot(_kY+1|0,2);_kS=_l5;return __continue;}}}}})(_kQ,_kR,_kS);if(_kT!=__continue){return _kT;}}},_l6=function(_l7,_l8){return _kP(_l7,new T(function(){return _kB(_l8,0);},1),_gS(_kG,_l8));},_l9=function(_la){var _lb=new T(function(){var _lc=new T(function(){var _ld=function(_le){return C > 19 ? new F(function(){return A1(_la,new T1(1,new T(function(){return _l6(_kA,_le);})));}) : (++C,A1(_la,new T1(1,new T(function(){return _l6(_kA,_le);}))));};return new T1(1,_jn(10,_ld));}),_lf=function(_lg){if(E(_lg)==43){var _lh=function(_li){return C > 19 ? new F(function(){return A1(_la,new T1(1,new T(function(){return _l6(_kA,_li);})));}) : (++C,A1(_la,new T1(1,new T(function(){return _l6(_kA,_li);}))));};return new T1(1,_jn(10,_lh));}else{return new T0(2);}},_lj=function(_lk){if(E(_lk)==45){var _ll=function(_lm){return C > 19 ? new F(function(){return A1(_la,new T1(1,new T(function(){return _kw(_l6(_kA,_lm));})));}) : (++C,A1(_la,new T1(1,new T(function(){return _kw(_l6(_kA,_lm));}))));};return new T1(1,_jn(10,_ll));}else{return new T0(2);}};return _hA(_hA(new T1(0,_lj),new T1(0,_lf)),_lc);});return _hA(new T1(0,function(_ln){return (E(_ln)==101)?E(_lb):new T0(2);}),new T1(0,function(_lo){return (E(_lo)==69)?E(_lb):new T0(2);}));},_lp=function(_lq){var _lr=function(_ls){return C > 19 ? new F(function(){return A1(_lq,new T1(1,_ls));}) : (++C,A1(_lq,new T1(1,_ls)));};return function(_lt){return (E(_lt)==46)?new T1(1,_jn(10,_lr)):new T0(2);};},_lu=function(_lv){return new T1(0,_lp(_lv));},_lw=function(_lx){var _ly=function(_lz){var _lA=function(_lB){return new T1(1,_iI(_l9,_ki,function(_lC){return C > 19 ? new F(function(){return A1(_lx,new T1(5,new T3(1,_lz,_lB,_lC)));}) : (++C,A1(_lx,new T1(5,new T3(1,_lz,_lB,_lC))));}));};return new T1(1,_iI(_lu,_kk,_lA));};return _jn(10,_ly);},_lD=function(_lE){return new T1(1,_lw(_lE));},_lF=function(_lG,_lH,_lI){while(1){var _lJ=E(_lI);if(!_lJ._){return false;}else{if(!B(A3(_6k,_lG,_lH,_lJ.a))){_lI=_lJ.b;continue;}else{return true;}}}},_lK=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_lL=function(_lM){return _lF(_ib,_lM,_lK);},_lN=function(_lO){var _lP=new T(function(){return B(A1(_lO,8));}),_lQ=new T(function(){return B(A1(_lO,16));});return function(_lR){switch(E(_lR)){case 79:return E(_lP);case 88:return E(_lQ);case 111:return E(_lP);case 120:return E(_lQ);default:return new T0(2);}};},_lS=function(_lT){return new T1(0,_lN(_lT));},_lU=function(_lV){return C > 19 ? new F(function(){return A1(_lV,10);}) : (++C,A1(_lV,10));},_lW=function(_lX){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _1V(9,_lX,__Z);})));},_lY=function(_lZ,_m0){var _m1=E(_lZ);if(!_m1._){var _m2=_m1.a,_m3=E(_m0);return (_m3._==0)?_m2<=_m3.a:I_compareInt(_m3.a,_m2)>=0;}else{var _m4=_m1.a,_m5=E(_m0);return (_m5._==0)?I_compareInt(_m4,_m5.a)<=0:I_compare(_m4,_m5.a)<=0;}},_m6=function(_m7){return new T0(2);},_m8=function(_m9){var _ma=E(_m9);if(!_ma._){return _m6;}else{var _mb=_ma.a,_mc=E(_ma.b);if(!_mc._){return E(_mb);}else{var _md=new T(function(){return _m8(_mc);}),_me=function(_mf){return _hA(B(A1(_mb,_mf)),new T(function(){return B(A1(_md,_mf));}));};return _me;}}},_mg=function(_mh,_mi){var _mj=function(_mk,_ml,_mm){var _mn=E(_mk);if(!_mn._){return C > 19 ? new F(function(){return A1(_mm,_mh);}) : (++C,A1(_mm,_mh));}else{var _mo=E(_ml);if(!_mo._){return new T0(2);}else{if(E(_mn.a)!=E(_mo.a)){return new T0(2);}else{var _mp=new T(function(){return B(_mj(_mn.b,_mo.b,_mm));});return new T1(0,function(_mq){return E(_mp);});}}}};return function(_mr){return C > 19 ? new F(function(){return _mj(_mh,_mr,_mi);}) : (++C,_mj(_mh,_mr,_mi));};},_ms=new T(function(){return unCStr("SO");}),_mt=function(_mu){var _mv=new T(function(){return B(A1(_mu,14));});return new T1(1,_mg(_ms,function(_mw){return E(_mv);}));},_mx=new T(function(){return unCStr("SOH");}),_my=function(_mz){var _mA=new T(function(){return B(A1(_mz,1));});return new T1(1,_mg(_mx,function(_mB){return E(_mA);}));},_mC=new T(function(){return unCStr("NUL");}),_mD=function(_mE){var _mF=new T(function(){return B(A1(_mE,0));});return new T1(1,_mg(_mC,function(_mG){return E(_mF);}));},_mH=new T(function(){return unCStr("STX");}),_mI=function(_mJ){var _mK=new T(function(){return B(A1(_mJ,2));});return new T1(1,_mg(_mH,function(_mL){return E(_mK);}));},_mM=new T(function(){return unCStr("ETX");}),_mN=function(_mO){var _mP=new T(function(){return B(A1(_mO,3));});return new T1(1,_mg(_mM,function(_mQ){return E(_mP);}));},_mR=new T(function(){return unCStr("EOT");}),_mS=function(_mT){var _mU=new T(function(){return B(A1(_mT,4));});return new T1(1,_mg(_mR,function(_mV){return E(_mU);}));},_mW=new T(function(){return unCStr("ENQ");}),_mX=function(_mY){var _mZ=new T(function(){return B(A1(_mY,5));});return new T1(1,_mg(_mW,function(_n0){return E(_mZ);}));},_n1=new T(function(){return unCStr("ACK");}),_n2=function(_n3){var _n4=new T(function(){return B(A1(_n3,6));});return new T1(1,_mg(_n1,function(_n5){return E(_n4);}));},_n6=new T(function(){return unCStr("BEL");}),_n7=function(_n8){var _n9=new T(function(){return B(A1(_n8,7));});return new T1(1,_mg(_n6,function(_na){return E(_n9);}));},_nb=new T(function(){return unCStr("BS");}),_nc=function(_nd){var _ne=new T(function(){return B(A1(_nd,8));});return new T1(1,_mg(_nb,function(_nf){return E(_ne);}));},_ng=new T(function(){return unCStr("HT");}),_nh=function(_ni){var _nj=new T(function(){return B(A1(_ni,9));});return new T1(1,_mg(_ng,function(_nk){return E(_nj);}));},_nl=new T(function(){return unCStr("LF");}),_nm=function(_nn){var _no=new T(function(){return B(A1(_nn,10));});return new T1(1,_mg(_nl,function(_np){return E(_no);}));},_nq=new T(function(){return unCStr("VT");}),_nr=function(_ns){var _nt=new T(function(){return B(A1(_ns,11));});return new T1(1,_mg(_nq,function(_nu){return E(_nt);}));},_nv=new T(function(){return unCStr("FF");}),_nw=function(_nx){var _ny=new T(function(){return B(A1(_nx,12));});return new T1(1,_mg(_nv,function(_nz){return E(_ny);}));},_nA=new T(function(){return unCStr("CR");}),_nB=function(_nC){var _nD=new T(function(){return B(A1(_nC,13));});return new T1(1,_mg(_nA,function(_nE){return E(_nD);}));},_nF=new T(function(){return unCStr("SI");}),_nG=function(_nH){var _nI=new T(function(){return B(A1(_nH,15));});return new T1(1,_mg(_nF,function(_nJ){return E(_nI);}));},_nK=new T(function(){return unCStr("DLE");}),_nL=function(_nM){var _nN=new T(function(){return B(A1(_nM,16));});return new T1(1,_mg(_nK,function(_nO){return E(_nN);}));},_nP=new T(function(){return unCStr("DC1");}),_nQ=function(_nR){var _nS=new T(function(){return B(A1(_nR,17));});return new T1(1,_mg(_nP,function(_nT){return E(_nS);}));},_nU=new T(function(){return unCStr("DC2");}),_nV=function(_nW){var _nX=new T(function(){return B(A1(_nW,18));});return new T1(1,_mg(_nU,function(_nY){return E(_nX);}));},_nZ=new T(function(){return unCStr("DC3");}),_o0=function(_o1){var _o2=new T(function(){return B(A1(_o1,19));});return new T1(1,_mg(_nZ,function(_o3){return E(_o2);}));},_o4=new T(function(){return unCStr("DC4");}),_o5=function(_o6){var _o7=new T(function(){return B(A1(_o6,20));});return new T1(1,_mg(_o4,function(_o8){return E(_o7);}));},_o9=new T(function(){return unCStr("NAK");}),_oa=function(_ob){var _oc=new T(function(){return B(A1(_ob,21));});return new T1(1,_mg(_o9,function(_od){return E(_oc);}));},_oe=new T(function(){return unCStr("SYN");}),_of=function(_og){var _oh=new T(function(){return B(A1(_og,22));});return new T1(1,_mg(_oe,function(_oi){return E(_oh);}));},_oj=new T(function(){return unCStr("ETB");}),_ok=function(_ol){var _om=new T(function(){return B(A1(_ol,23));});return new T1(1,_mg(_oj,function(_on){return E(_om);}));},_oo=new T(function(){return unCStr("CAN");}),_op=function(_oq){var _or=new T(function(){return B(A1(_oq,24));});return new T1(1,_mg(_oo,function(_os){return E(_or);}));},_ot=new T(function(){return unCStr("EM");}),_ou=function(_ov){var _ow=new T(function(){return B(A1(_ov,25));});return new T1(1,_mg(_ot,function(_ox){return E(_ow);}));},_oy=new T(function(){return unCStr("SUB");}),_oz=function(_oA){var _oB=new T(function(){return B(A1(_oA,26));});return new T1(1,_mg(_oy,function(_oC){return E(_oB);}));},_oD=new T(function(){return unCStr("ESC");}),_oE=function(_oF){var _oG=new T(function(){return B(A1(_oF,27));});return new T1(1,_mg(_oD,function(_oH){return E(_oG);}));},_oI=new T(function(){return unCStr("FS");}),_oJ=function(_oK){var _oL=new T(function(){return B(A1(_oK,28));});return new T1(1,_mg(_oI,function(_oM){return E(_oL);}));},_oN=new T(function(){return unCStr("GS");}),_oO=function(_oP){var _oQ=new T(function(){return B(A1(_oP,29));});return new T1(1,_mg(_oN,function(_oR){return E(_oQ);}));},_oS=new T(function(){return unCStr("RS");}),_oT=function(_oU){var _oV=new T(function(){return B(A1(_oU,30));});return new T1(1,_mg(_oS,function(_oW){return E(_oV);}));},_oX=new T(function(){return unCStr("US");}),_oY=function(_oZ){var _p0=new T(function(){return B(A1(_oZ,31));});return new T1(1,_mg(_oX,function(_p1){return E(_p0);}));},_p2=new T(function(){return unCStr("SP");}),_p3=function(_p4){var _p5=new T(function(){return B(A1(_p4,32));});return new T1(1,_mg(_p2,function(_p6){return E(_p5);}));},_p7=new T(function(){return unCStr("DEL");}),_p8=function(_p9){var _pa=new T(function(){return B(A1(_p9,127));});return new T1(1,_mg(_p7,function(_pb){return E(_pa);}));},_pc=new T(function(){return _m8(new T2(1,function(_pd){return new T1(1,_iI(_my,_mt,_pd));},new T2(1,_mD,new T2(1,_mI,new T2(1,_mN,new T2(1,_mS,new T2(1,_mX,new T2(1,_n2,new T2(1,_n7,new T2(1,_nc,new T2(1,_nh,new T2(1,_nm,new T2(1,_nr,new T2(1,_nw,new T2(1,_nB,new T2(1,_nG,new T2(1,_nL,new T2(1,_nQ,new T2(1,_nV,new T2(1,_o0,new T2(1,_o5,new T2(1,_oa,new T2(1,_of,new T2(1,_ok,new T2(1,_op,new T2(1,_ou,new T2(1,_oz,new T2(1,_oE,new T2(1,_oJ,new T2(1,_oO,new T2(1,_oT,new T2(1,_oY,new T2(1,_p3,new T2(1,_p8,__Z))))))))))))))))))))))))))))))))));}),_pe=function(_pf){var _pg=new T(function(){return B(A1(_pf,7));}),_ph=new T(function(){return B(A1(_pf,8));}),_pi=new T(function(){return B(A1(_pf,9));}),_pj=new T(function(){return B(A1(_pf,10));}),_pk=new T(function(){return B(A1(_pf,11));}),_pl=new T(function(){return B(A1(_pf,12));}),_pm=new T(function(){return B(A1(_pf,13));}),_pn=new T(function(){return B(A1(_pf,92));}),_po=new T(function(){return B(A1(_pf,39));}),_pp=new T(function(){return B(A1(_pf,34));}),_pq=new T(function(){var _pr=function(_ps){var _pt=new T(function(){return _7Q(E(_ps));}),_pu=function(_pv){var _pw=_l6(_pt,_pv);if(!_lY(_pw,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_pf,new T(function(){var _px=_7T(_pw);if(_px>>>0>1114111){return _lW(_px);}else{return _px;}}));}) : (++C,A1(_pf,new T(function(){var _px=_7T(_pw);if(_px>>>0>1114111){return _lW(_px);}else{return _px;}})));}};return new T1(1,_jn(_ps,_pu));},_py=new T(function(){var _pz=new T(function(){return B(A1(_pf,31));}),_pA=new T(function(){return B(A1(_pf,30));}),_pB=new T(function(){return B(A1(_pf,29));}),_pC=new T(function(){return B(A1(_pf,28));}),_pD=new T(function(){return B(A1(_pf,27));}),_pE=new T(function(){return B(A1(_pf,26));}),_pF=new T(function(){return B(A1(_pf,25));}),_pG=new T(function(){return B(A1(_pf,24));}),_pH=new T(function(){return B(A1(_pf,23));}),_pI=new T(function(){return B(A1(_pf,22));}),_pJ=new T(function(){return B(A1(_pf,21));}),_pK=new T(function(){return B(A1(_pf,20));}),_pL=new T(function(){return B(A1(_pf,19));}),_pM=new T(function(){return B(A1(_pf,18));}),_pN=new T(function(){return B(A1(_pf,17));}),_pO=new T(function(){return B(A1(_pf,16));}),_pP=new T(function(){return B(A1(_pf,15));}),_pQ=new T(function(){return B(A1(_pf,14));}),_pR=new T(function(){return B(A1(_pf,6));}),_pS=new T(function(){return B(A1(_pf,5));}),_pT=new T(function(){return B(A1(_pf,4));}),_pU=new T(function(){return B(A1(_pf,3));}),_pV=new T(function(){return B(A1(_pf,2));}),_pW=new T(function(){return B(A1(_pf,1));}),_pX=new T(function(){return B(A1(_pf,0));}),_pY=function(_pZ){switch(E(_pZ)){case 64:return E(_pX);case 65:return E(_pW);case 66:return E(_pV);case 67:return E(_pU);case 68:return E(_pT);case 69:return E(_pS);case 70:return E(_pR);case 71:return E(_pg);case 72:return E(_ph);case 73:return E(_pi);case 74:return E(_pj);case 75:return E(_pk);case 76:return E(_pl);case 77:return E(_pm);case 78:return E(_pQ);case 79:return E(_pP);case 80:return E(_pO);case 81:return E(_pN);case 82:return E(_pM);case 83:return E(_pL);case 84:return E(_pK);case 85:return E(_pJ);case 86:return E(_pI);case 87:return E(_pH);case 88:return E(_pG);case 89:return E(_pF);case 90:return E(_pE);case 91:return E(_pD);case 92:return E(_pC);case 93:return E(_pB);case 94:return E(_pA);case 95:return E(_pz);default:return new T0(2);}};return _hA(new T1(0,function(_q0){return (E(_q0)==94)?E(new T1(0,_pY)):new T0(2);}),new T(function(){return B(A1(_pc,_pf));}));});return _hA(new T1(1,_iI(_lS,_lU,_pr)),_py);});return _hA(new T1(0,function(_q1){switch(E(_q1)){case 34:return E(_pp);case 39:return E(_po);case 92:return E(_pn);case 97:return E(_pg);case 98:return E(_ph);case 102:return E(_pl);case 110:return E(_pj);case 114:return E(_pm);case 116:return E(_pi);case 118:return E(_pk);default:return new T0(2);}}),_pq);},_q2=function(_q3){return C > 19 ? new F(function(){return A1(_q3,0);}) : (++C,A1(_q3,0));},_q4=function(_q5){var _q6=E(_q5);if(!_q6._){return _q2;}else{var _q7=E(_q6.a),_q8=_q7>>>0,_q9=new T(function(){return _q4(_q6.b);});if(_q8>887){var _qa=u_iswspace(_q7);if(!E(_qa)){return _q2;}else{var _qb=function(_qc){var _qd=new T(function(){return B(A1(_q9,_qc));});return new T1(0,function(_qe){return E(_qd);});};return _qb;}}else{if(_q8==32){var _qf=function(_qg){var _qh=new T(function(){return B(A1(_q9,_qg));});return new T1(0,function(_qi){return E(_qh);});};return _qf;}else{if(_q8-9>>>0>4){if(_q8==160){var _qj=function(_qk){var _ql=new T(function(){return B(A1(_q9,_qk));});return new T1(0,function(_qm){return E(_ql);});};return _qj;}else{return _q2;}}else{var _qn=function(_qo){var _qp=new T(function(){return B(A1(_q9,_qo));});return new T1(0,function(_qq){return E(_qp);});};return _qn;}}}}},_qr=function(_qs){var _qt=new T(function(){return B(_qr(_qs));}),_qu=function(_qv){return (E(_qv)==92)?E(_qt):new T0(2);},_qw=function(_qx){return E(new T1(0,_qu));},_qy=new T1(1,function(_qz){return C > 19 ? new F(function(){return A2(_q4,_qz,_qw);}) : (++C,A2(_q4,_qz,_qw));}),_qA=new T(function(){return B(_pe(function(_qB){return C > 19 ? new F(function(){return A1(_qs,new T2(0,_qB,true));}) : (++C,A1(_qs,new T2(0,_qB,true)));}));}),_qC=function(_qD){var _qE=E(_qD);if(_qE==38){return E(_qt);}else{var _qF=_qE>>>0;if(_qF>887){var _qG=u_iswspace(_qE);return (E(_qG)==0)?new T0(2):E(_qy);}else{return (_qF==32)?E(_qy):(_qF-9>>>0>4)?(_qF==160)?E(_qy):new T0(2):E(_qy);}}};return _hA(new T1(0,function(_qH){return (E(_qH)==92)?E(new T1(0,_qC)):new T0(2);}),new T1(0,function(_qI){var _qJ=E(_qI);if(_qJ==92){return E(_qA);}else{return C > 19 ? new F(function(){return A1(_qs,new T2(0,_qJ,false));}) : (++C,A1(_qs,new T2(0,_qJ,false)));}}));},_qK=function(_qL,_qM){var _qN=new T(function(){return B(A1(_qM,new T1(1,new T(function(){return B(A1(_qL,__Z));}))));}),_qO=function(_qP){var _qQ=E(_qP),_qR=E(_qQ.a);if(_qR==34){if(!E(_qQ.b)){return E(_qN);}else{return C > 19 ? new F(function(){return _qK(function(_qS){return C > 19 ? new F(function(){return A1(_qL,new T2(1,_qR,_qS));}) : (++C,A1(_qL,new T2(1,_qR,_qS)));},_qM);}) : (++C,_qK(function(_qS){return C > 19 ? new F(function(){return A1(_qL,new T2(1,_qR,_qS));}) : (++C,A1(_qL,new T2(1,_qR,_qS)));},_qM));}}else{return C > 19 ? new F(function(){return _qK(function(_qT){return C > 19 ? new F(function(){return A1(_qL,new T2(1,_qR,_qT));}) : (++C,A1(_qL,new T2(1,_qR,_qT)));},_qM);}) : (++C,_qK(function(_qT){return C > 19 ? new F(function(){return A1(_qL,new T2(1,_qR,_qT));}) : (++C,A1(_qL,new T2(1,_qR,_qT)));},_qM));}};return C > 19 ? new F(function(){return _qr(_qO);}) : (++C,_qr(_qO));},_qU=new T(function(){return unCStr("_\'");}),_qV=function(_qW){var _qX=u_iswalnum(_qW);if(!E(_qX)){return _lF(_ib,_qW,_qU);}else{return true;}},_qY=function(_qZ){return _qV(E(_qZ));},_r0=new T(function(){return unCStr(",;()[]{}`");}),_r1=new T(function(){return unCStr("=>");}),_r2=new T(function(){return unCStr("~");}),_r3=new T(function(){return unCStr("@");}),_r4=new T(function(){return unCStr("->");}),_r5=new T(function(){return unCStr("<-");}),_r6=new T(function(){return unCStr("|");}),_r7=new T(function(){return unCStr("\\");}),_r8=new T(function(){return unCStr("=");}),_r9=new T(function(){return unCStr("::");}),_ra=new T(function(){return unCStr("..");}),_rb=function(_rc){var _rd=new T(function(){return B(A1(_rc,new T0(6)));}),_re=new T(function(){var _rf=new T(function(){var _rg=function(_rh){var _ri=new T(function(){return B(A1(_rc,new T1(0,_rh)));});return new T1(0,function(_rj){return (E(_rj)==39)?E(_ri):new T0(2);});};return B(_pe(_rg));}),_rk=function(_rl){var _rm=E(_rl);switch(_rm){case 39:return new T0(2);case 92:return E(_rf);default:var _rn=new T(function(){return B(A1(_rc,new T1(0,_rm)));});return new T1(0,function(_ro){return (E(_ro)==39)?E(_rn):new T0(2);});}},_rp=new T(function(){var _rq=new T(function(){return B(_qK(_1C,_rc));}),_rr=new T(function(){var _rs=new T(function(){var _rt=new T(function(){var _ru=function(_rv){var _rw=E(_rv),_rx=u_iswalpha(_rw);return (E(_rx)==0)?(_rw==95)?new T1(1,_j8(_qY,function(_ry){return C > 19 ? new F(function(){return A1(_rc,new T1(3,new T2(1,_rw,_ry)));}) : (++C,A1(_rc,new T1(3,new T2(1,_rw,_ry))));})):new T0(2):new T1(1,_j8(_qY,function(_rz){return C > 19 ? new F(function(){return A1(_rc,new T1(3,new T2(1,_rw,_rz)));}) : (++C,A1(_rc,new T1(3,new T2(1,_rw,_rz))));}));};return _hA(new T1(0,_ru),new T(function(){return new T1(1,_iI(_kg,_lD,_rc));}));}),_rA=function(_rB){return (!_lF(_ib,_rB,_lK))?new T0(2):new T1(1,_j8(_lL,function(_rC){var _rD=new T2(1,_rB,_rC);if(!_lF(new T2(0,_ig,_il),_rD,new T2(1,_ra,new T2(1,_r9,new T2(1,_r8,new T2(1,_r7,new T2(1,_r6,new T2(1,_r5,new T2(1,_r4,new T2(1,_r3,new T2(1,_r2,new T2(1,_r1,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_rc,new T1(4,_rD));}) : (++C,A1(_rc,new T1(4,_rD)));}else{return C > 19 ? new F(function(){return A1(_rc,new T1(2,_rD));}) : (++C,A1(_rc,new T1(2,_rD)));}}));};return _hA(new T1(0,_rA),_rt);});return _hA(new T1(0,function(_rE){if(!_lF(_ib,_rE,_r0)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_rc,new T1(2,new T2(1,_rE,__Z)));}) : (++C,A1(_rc,new T1(2,new T2(1,_rE,__Z))));}}),_rs);});return _hA(new T1(0,function(_rF){return (E(_rF)==34)?E(_rq):new T0(2);}),_rr);});return _hA(new T1(0,function(_rG){return (E(_rG)==39)?E(new T1(0,_rk)):new T0(2);}),_rp);});return _hA(new T1(1,function(_rH){return (E(_rH)._==0)?E(_rd):new T0(2);}),_re);},_rI=function(_rJ,_rK){var _rL=new T(function(){var _rM=new T(function(){var _rN=function(_rO){var _rP=new T(function(){var _rQ=new T(function(){return B(A1(_rK,_rO));});return B(_rb(function(_rR){var _rS=E(_rR);return (_rS._==2)?(!_i6(_rS.a,_i5))?new T0(2):E(_rQ):new T0(2);}));}),_rT=function(_rU){return E(_rP);};return new T1(1,function(_rV){return C > 19 ? new F(function(){return A2(_q4,_rV,_rT);}) : (++C,A2(_q4,_rV,_rT));});};return B(A2(_rJ,0,_rN));});return B(_rb(function(_rW){var _rX=E(_rW);return (_rX._==2)?(!_i6(_rX.a,_i4))?new T0(2):E(_rM):new T0(2);}));}),_rY=function(_rZ){return E(_rL);};return function(_s0){return C > 19 ? new F(function(){return A2(_q4,_s0,_rY);}) : (++C,A2(_q4,_s0,_rY));};},_s1=function(_s2,_s3){var _s4=function(_s5){var _s6=new T(function(){return B(A1(_s2,_s5));}),_s7=function(_s8){return _hA(B(A1(_s6,_s8)),new T(function(){return new T1(1,_rI(_s4,_s8));}));};return _s7;},_s9=new T(function(){return B(A1(_s2,_s3));}),_sa=function(_sb){return _hA(B(A1(_s9,_sb)),new T(function(){return new T1(1,_rI(_s4,_sb));}));};return _sa;},_sc=function(_sd,_se){var _sf=function(_sg,_sh){var _si=function(_sj){return C > 19 ? new F(function(){return A1(_sh,new T(function(){return  -E(_sj);}));}) : (++C,A1(_sh,new T(function(){return  -E(_sj);})));},_sk=new T(function(){return B(_rb(function(_sl){return C > 19 ? new F(function(){return A3(_sd,_sl,_sg,_si);}) : (++C,A3(_sd,_sl,_sg,_si));}));}),_sm=function(_sn){return E(_sk);},_so=function(_sp){return C > 19 ? new F(function(){return A2(_q4,_sp,_sm);}) : (++C,A2(_q4,_sp,_sm));},_sq=new T(function(){return B(_rb(function(_sr){var _ss=E(_sr);if(_ss._==4){var _st=E(_ss.a);if(!_st._){return C > 19 ? new F(function(){return A3(_sd,_ss,_sg,_sh);}) : (++C,A3(_sd,_ss,_sg,_sh));}else{if(E(_st.a)==45){if(!E(_st.b)._){return E(new T1(1,_so));}else{return C > 19 ? new F(function(){return A3(_sd,_ss,_sg,_sh);}) : (++C,A3(_sd,_ss,_sg,_sh));}}else{return C > 19 ? new F(function(){return A3(_sd,_ss,_sg,_sh);}) : (++C,A3(_sd,_ss,_sg,_sh));}}}else{return C > 19 ? new F(function(){return A3(_sd,_ss,_sg,_sh);}) : (++C,A3(_sd,_ss,_sg,_sh));}}));}),_su=function(_sv){return E(_sq);};return new T1(1,function(_sw){return C > 19 ? new F(function(){return A2(_q4,_sw,_su);}) : (++C,A2(_q4,_sw,_su));});};return _s1(_sf,_se);},_sx=function(_sy){var _sz=E(_sy);if(!_sz._){var _sA=_sz.b,_sB=new T(function(){return _kP(new T(function(){return _7Q(E(_sz.a));}),new T(function(){return _kB(_sA,0);},1),_gS(_kG,_sA));});return new T1(1,_sB);}else{return (E(_sz.b)._==0)?(E(_sz.c)._==0)?new T1(1,new T(function(){return _l6(_kA,_sz.a);})):__Z:__Z;}},_sC=function(_sD,_sE){return new T0(2);},_sF=function(_sG){var _sH=E(_sG);if(_sH._==5){var _sI=_sx(_sH.a);if(!_sI._){return _sC;}else{var _sJ=new T(function(){return _7T(_sI.a);});return function(_sK,_sL){return C > 19 ? new F(function(){return A1(_sL,_sJ);}) : (++C,A1(_sL,_sJ));};}}else{return _sC;}},_sM=function(_sN){return _sc(_sF,_sN);},_sO=new T(function(){return unCStr("[");}),_sP=function(_sQ,_sR){var _sS=function(_sT,_sU){var _sV=new T(function(){return B(A1(_sU,__Z));}),_sW=new T(function(){var _sX=function(_sY){return _sS(true,function(_sZ){return C > 19 ? new F(function(){return A1(_sU,new T2(1,_sY,_sZ));}) : (++C,A1(_sU,new T2(1,_sY,_sZ)));});};return B(A2(_sQ,0,_sX));}),_t0=new T(function(){return B(_rb(function(_t1){var _t2=E(_t1);if(_t2._==2){var _t3=E(_t2.a);if(!_t3._){return new T0(2);}else{var _t4=_t3.b;switch(E(_t3.a)){case 44:return (E(_t4)._==0)?(!E(_sT))?new T0(2):E(_sW):new T0(2);case 93:return (E(_t4)._==0)?E(_sV):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_t5=function(_t6){return E(_t0);};return new T1(1,function(_t7){return C > 19 ? new F(function(){return A2(_q4,_t7,_t5);}) : (++C,A2(_q4,_t7,_t5));});},_t8=function(_t9,_ta){return C > 19 ? new F(function(){return _tb(_ta);}) : (++C,_tb(_ta));},_tb=function(_tc){var _td=new T(function(){var _te=new T(function(){var _tf=new T(function(){var _tg=function(_th){return _sS(true,function(_ti){return C > 19 ? new F(function(){return A1(_tc,new T2(1,_th,_ti));}) : (++C,A1(_tc,new T2(1,_th,_ti)));});};return B(A2(_sQ,0,_tg));});return _hA(_sS(false,_tc),_tf);});return B(_rb(function(_tj){var _tk=E(_tj);return (_tk._==2)?(!_i6(_tk.a,_sO))?new T0(2):E(_te):new T0(2);}));}),_tl=function(_tm){return E(_td);};return _hA(new T1(1,function(_tn){return C > 19 ? new F(function(){return A2(_q4,_tn,_tl);}) : (++C,A2(_q4,_tn,_tl));}),new T(function(){return new T1(1,_rI(_t8,_tc));}));};return C > 19 ? new F(function(){return _tb(_sR);}) : (++C,_tb(_sR));},_to=function(_tp){var _tq=function(_tr){return E(new T2(3,_tp,_iz));};return new T1(1,function(_ts){return C > 19 ? new F(function(){return A2(_q4,_ts,_tq);}) : (++C,A2(_q4,_ts,_tq));});},_tt=new T(function(){return B(_sP(_sM,_to));}),_tu=new T(function(){return unCStr("Prelude.read: ambiguous parse");}),_tv=new T(function(){return unCStr("Prelude.read: no parse");}),_tw=function(_tx){while(1){var _ty=(function(_tz){var _tA=E(_tz);if(!_tA._){return __Z;}else{var _tB=_tA.b,_tC=E(_tA.a);if(!E(_tC.b)._){return new T2(1,_tC.a,new T(function(){return _tw(_tB);}));}else{_tx=_tB;return __continue;}}})(_tx);if(_ty!=__continue){return _ty;}}},_tD=function(_tE,_tF,_){var _tG=new T(function(){var _tH=_tw(_hq(_tt,new T(function(){return fromJSStr(E(_tE));})));if(!_tH._){return err(_tv);}else{if(!E(_tH.b)._){return E(_tH.a);}else{return err(_tu);}}}),_tI=E(_tF);if(_tI._==3){var _tJ=E(_tI.a);if(!_tJ._){var _tK=_eM(_);return new T2(0,_tG,_tK);}else{var _tL=E(_tJ.a);if(_tL._==3){if(!E(_tJ.b)._){var _tM=_bd("Array"),_tN=_eO(_gS(_h8,_tL.a),_);return new T2(0,_tG,new T2(1,_tN,__Z));}else{var _tO=_eM(_);return new T2(0,_tG,_tO);}}else{var _tP=_eM(_);return new T2(0,_tG,_tP);}}}else{var _tQ=_eM(_);return new T2(0,_tG,_tQ);}},_tR=function(_tS,_){var _tT=E(_tS);return _tD(_tT.a,_tT.b,_);},_tU=function(_tV,_tW){var _tX=E(_tV);if(!_tX._){return __Z;}else{var _tY=_tX.a,_tZ=E(_tW);return (_tZ==1)?new T2(1,function(_){return _tR(_tY,_);},__Z):new T2(1,function(_){return _tR(_tY,_);},new T(function(){return _tU(_tX.b,_tZ-1|0);}));}},_u0=function(_){var _u1=_bd("Error decoding tree data");return _bc(_);},_u2=function(_u3,_){var _u4=E(_u3);if(!_u4._){return __Z;}else{var _u5=B(A1(_u4.a,_)),_u6=_u2(_u4.b,_);return new T2(1,_u5,_u6);}},_u7=new T(function(){return B(_gH("Ajax.hs:(97,5)-(101,81)|function decodeMenu"));}),_u8=new T(function(){return _fZ(new T1(0,new T(function(){return unCStr("Error decoding tree data");})),_fO);}),_u9=function(_ua,_ub){var _uc=E(_ua),_ud=new T(function(){return B(A3(_25,_1M,new T2(1,function(_ue){return _3D(_uc.a,_ue);},new T2(1,function(_uf){return _4k(_uc.b,_uf);},__Z)),new T2(1,41,_ub)));});return new T2(1,40,_ud);},_ug=function(_uh,_){var _ui=E(_uh);if(_ui._==4){var _uj=_ui.a,_uk=_fs(_6q,"lin",_uj);if(!_uk._){return E(_fr);}else{var _ul=function(_,_um){var _un=_fs(_6q,"menu",_uj);if(!_un._){return E(_fr);}else{var _uo=E(_un.a);if(_uo._==4){var _up=_uo.a,_uq=_kB(_up,0),_ur=function(_,_us){var _ut=_bd(toJSStr(unAppCStr("### ",new T(function(){return _3p(_u9,_us,__Z);})))),_uu=_fs(_6q,"grammar",_uj);if(!_uu._){var _uv=_u0(_);return E(_u8);}else{var _uw=_fs(_6q,"tree",_uj);if(!_uw._){var _ux=_u0(_);return E(_u8);}else{return new T4(0,new T(function(){var _uy=E(_uu.a);if(_uy._==1){return fromJSStr(_uy.a);}else{return E(_h7);}}),new T(function(){var _uz=E(_uw.a);if(_uz._==1){return fromJSStr(_uz.a);}else{return E(_h7);}}),_um,new T1(0,new T(function(){var _uA=E(_us);if(!_uA._){return new T0(1);}else{return B(_eF(_uA));}})));}}};if(0>=_uq){var _uB=_u2(__Z,_);return _ur(_,_uB);}else{var _uC=_u2(_tU(_up,_uq),_);return _ur(_,_uC);}}else{return E(_u7);}}},_uD=E(_uk.a);if(_uD._==3){return _ul(_,new T(function(){return _gS(_h3,_uD.a);}));}else{return _ul(_,__Z);}}}else{return E(_fr);}},_uE=function(_uF){var _uG=E(_uF);return (_uG._==0)?E(_fr):E(_uG.a);},_uH=new T(function(){return _fZ(new T1(0,new T(function(){return unCStr("Error decoding message data");})),_fO);}),_uI=new T(function(){return fromJSStr("Invalid JSON!");}),_uJ=new T(function(){return _fZ(new T1(0,_uI),_fO);}),_uK=new T(function(){return unAppCStr("Error ",_uI);}),_uL=new T(function(){return B(_gH("Ajax.hs:131:5-35|function getJustBool"));}),_uM=function(_uN,_){var _uO=jsParseJSON(_uN);if(!_uO._){var _uP=_bd(toJSStr(E(_uK)));return E(_uJ);}else{var _uQ=_uO.a,_uR=E(_uQ);if(_uR._==4){var _uS=_fs(_6q,"a",_uR.a);}else{var _uS=__Z;}var _uT=_ug(_uE(_uS),_),_uU=_uT;if(_uQ._==4){var _uV=_fs(_6q,"b",_uQ.a);}else{var _uV=__Z;}var _uW=_ug(_uE(_uV),_);if(_uQ._==4){var _uX=_uQ.a,_uY=_fs(_6q,"success",_uX);if(!_uY._){var _uZ=_be(_);return E(_uH);}else{var _v0=_fs(_6q,"score",_uX);if(!_v0._){var _v1=_be(_);return E(_uH);}else{if(!E(_uS)._){var _v2=_be(_);return E(_uH);}else{if(!E(_uV)._){var _v3=_be(_);return E(_uH);}else{return new T4(0,new T(function(){var _v4=E(_uY.a);if(_v4._==2){return E(_v4.a);}else{return E(_uL);}}),new T(function(){var _v5=E(_v0.a);if(!_v5._){var _v6=_b0(_7Z,_v5.a),_v7=_v6.a;if(E(_v6.b)>=0){return E(_v7);}else{return E(_v7)-1|0;}}else{return E(_h6);}}),_uU,_uW);}}}}}else{var _v8=_be(_);return E(_uH);}}},_v9=function(_va){var _vb=_eU(__Z,_va),_vc=jsCat(new T2(1,_vb.a,_vb.b),E(_fk));return E(_vc);},_vd=function(_ve,_vf){return new T2(1,new T2(0,"grammar",new T(function(){return new T1(1,toJSStr(E(_ve)));})),new T2(1,new T2(0,"tree",new T(function(){return new T1(1,toJSStr(E(_vf)));})),__Z));},_vg=function(_vh){var _vi=E(_vh);return new T1(4,E(_vd(_vi.a,_vi.b)));},_vj=function(_vk){var _vl=E(_vk);if(!_vl._){return _v9(new T0(5));}else{return _v9(new T1(4,E(new T2(1,new T2(0,"score",new T(function(){return new T1(0,E(_vl.a));})),new T2(1,new T2(0,"a",new T(function(){return _vg(_vl.b);})),new T2(1,new T2(0,"b",new T(function(){return _vg(_vl.c);})),__Z))))));}},_vm=function(_vn){return E(E(_vn).a);},_vo=function(_vp,_vq,_vr,_vs,_vt){return C > 19 ? new F(function(){return A2(_vq,_vr,new T2(1,B(A2(_vm,_vp,E(_vt))),E(_vs)));}) : (++C,A2(_vq,_vr,new T2(1,B(A2(_vm,_vp,E(_vt))),E(_vs))));},_vu=function(_vv){return E(E(_vv).a);},_vw=function(_vx){return E(E(_vx).a);},_vy=function(_vz){return E(E(_vz).a);},_vA=function(_vB){return E(E(_vB).b);},_vC=new T(function(){return unCStr("base");}),_vD=new T(function(){return unCStr("GHC.IO.Exception");}),_vE=new T(function(){return unCStr("IOException");}),_vF=function(_vG){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_vC,_vD,_vE),__Z,__Z));},_vH=new T(function(){return unCStr(": ");}),_vI=new T(function(){return unCStr(")");}),_vJ=new T(function(){return unCStr(" (");}),_vK=new T(function(){return unCStr("interrupted");}),_vL=new T(function(){return unCStr("system error");}),_vM=new T(function(){return unCStr("unsatisified constraints");}),_vN=new T(function(){return unCStr("user error");}),_vO=new T(function(){return unCStr("permission denied");}),_vP=new T(function(){return unCStr("illegal operation");}),_vQ=new T(function(){return unCStr("end of file");}),_vR=new T(function(){return unCStr("resource exhausted");}),_vS=new T(function(){return unCStr("resource busy");}),_vT=new T(function(){return unCStr("does not exist");}),_vU=new T(function(){return unCStr("already exists");}),_vV=new T(function(){return unCStr("resource vanished");}),_vW=new T(function(){return unCStr("timeout");}),_vX=new T(function(){return unCStr("unsupported operation");}),_vY=new T(function(){return unCStr("hardware fault");}),_vZ=new T(function(){return unCStr("inappropriate type");}),_w0=new T(function(){return unCStr("invalid argument");}),_w1=new T(function(){return unCStr("failed");}),_w2=new T(function(){return unCStr("protocol error");}),_w3=function(_w4,_w5){switch(E(_w4)){case 0:return _0(_vU,_w5);case 1:return _0(_vT,_w5);case 2:return _0(_vS,_w5);case 3:return _0(_vR,_w5);case 4:return _0(_vQ,_w5);case 5:return _0(_vP,_w5);case 6:return _0(_vO,_w5);case 7:return _0(_vN,_w5);case 8:return _0(_vM,_w5);case 9:return _0(_vL,_w5);case 10:return _0(_w2,_w5);case 11:return _0(_w1,_w5);case 12:return _0(_w0,_w5);case 13:return _0(_vZ,_w5);case 14:return _0(_vY,_w5);case 15:return _0(_vX,_w5);case 16:return _0(_vW,_w5);case 17:return _0(_vV,_w5);default:return _0(_vK,_w5);}},_w6=new T(function(){return unCStr("}");}),_w7=new T(function(){return unCStr("{handle: ");}),_w8=function(_w9,_wa,_wb,_wc,_wd,_we){var _wf=new T(function(){var _wg=new T(function(){var _wh=new T(function(){var _wi=E(_wc);if(!_wi._){return E(_we);}else{var _wj=new T(function(){return _0(_wi,new T(function(){return _0(_vI,_we);},1));},1);return _0(_vJ,_wj);}},1);return _w3(_wa,_wh);}),_wk=E(_wb);if(!_wk._){return E(_wg);}else{return _0(_wk,new T(function(){return _0(_vH,_wg);},1));}}),_wl=E(_wd);if(!_wl._){var _wm=E(_w9);if(!_wm._){return E(_wf);}else{var _wn=E(_wm.a);if(!_wn._){var _wo=new T(function(){var _wp=new T(function(){return _0(_w6,new T(function(){return _0(_vH,_wf);},1));},1);return _0(_wn.a,_wp);},1);return _0(_w7,_wo);}else{var _wq=new T(function(){var _wr=new T(function(){return _0(_w6,new T(function(){return _0(_vH,_wf);},1));},1);return _0(_wn.a,_wr);},1);return _0(_w7,_wq);}}}else{return _0(_wl.a,new T(function(){return _0(_vH,_wf);},1));}},_ws=function(_wt){var _wu=E(_wt);return _w8(_wu.a,_wu.b,_wu.c,_wu.d,_wu.f,__Z);},_wv=function(_ww,_wx){var _wy=E(_ww);return _w8(_wy.a,_wy.b,_wy.c,_wy.d,_wy.f,_wx);},_wz=new T(function(){return new T5(0,_vF,new T3(0,function(_wA,_wB,_wC){var _wD=E(_wB);return _w8(_wD.a,_wD.b,_wD.c,_wD.d,_wD.f,_wC);},_ws,function(_wE,_wF){return _3p(_wv,_wE,_wF);}),_wG,function(_wH){var _wI=E(_wH);return _7b(_79(_wI.a),_vF,_wI.b);},_ws);}),_wG=function(_wJ){return new T2(0,_wz,_wJ);},_wK=function(_wL,_){var _wM=_wL["type"],_wN=String(_wM),_wO=strEq(_wN,"network");if(!E(_wO)){var _wP=strEq(_wN,"http");if(!E(_wP)){var _wQ=new T(function(){var _wR=new T(function(){return unAppCStr("unknown type of ajax error: ",new T(function(){return fromJSStr(_wN);}));});return _wG(new T6(0,__Z,7,__Z,_wR,__Z,__Z));});return die(_wQ);}else{var _wS=_wL["status"],_wT=_wL["status-text"];return new T2(1,new T(function(){var _wU=Number(_wS);return jsTrunc(_wU);}),new T(function(){return String(_wT);}));}}else{return __Z;}},_wV=function(_wW,_){var _wX=E(_wW);if(!_wX._){return __Z;}else{var _wY=_wK(E(_wX.a),_),_wZ=_wV(_wX.b,_);return new T2(1,_wY,_wZ);}},_x0=function(_x1,_){var _x2=__arr2lst(0,_x1);return _wV(_x2,_);},_x3=new T2(0,function(_x4,_){return _wK(E(_x4),_);},function(_x5,_){return _x0(E(_x5),_);}),_x6=function(_x7){return E(E(_x7).a);},_x8=function(_x9){var _xa=B(A1(_x9,_));return E(_xa);},_xb=new T(function(){return _x8(function(_){return __jsNull();});}),_xc=function(_xd,_xe,_){var _xf=__eq(_xe,E(_xb));if(!E(_xf)){var _xg=__isUndef(_xe);if(!E(_xg)){var _xh=B(A3(_x6,_xd,_xe,_));return new T1(1,_xh);}else{return __Z;}}else{return __Z;}},_xi=function(_xj,_xk,_){var _xl=__arr2lst(0,_xk),_xm=function(_xn,_){var _xo=E(_xn);if(!_xo._){return __Z;}else{var _xp=_xo.b,_xq=E(_xo.a),_xr=__eq(_xq,E(_xb));if(!E(_xr)){var _xs=__isUndef(_xq);if(!E(_xs)){var _xt=B(A3(_x6,_xj,_xq,_)),_xu=_xm(_xp,_);return new T2(1,new T1(1,_xt),_xu);}else{var _xv=_xm(_xp,_);return new T2(1,__Z,_xv);}}else{var _xw=_xm(_xp,_);return new T2(1,__Z,_xw);}}};return _xm(_xl,_);},_xx=new T2(0,function(_xy,_){return _xc(_x3,E(_xy),_);},function(_xz,_){return _xi(_x3,E(_xz),_);}),_xA=function(_xB,_xC,_){var _xD=B(A2(_xB,new T(function(){var _xE=E(_xC),_xF=__eq(_xE,E(_xb));if(!E(_xF)){var _xG=__isUndef(_xE);if(!E(_xG)){return new T1(1,_xE);}else{return __Z;}}else{return __Z;}}),_));return _xb;},_xH=new T2(0,_xA,function(_xI){return 2;}),_xJ=function(_xK){return E(E(_xK).a);},_xL=function(_xM,_xN,_xO,_xP){var _xQ=new T(function(){return B(A1(_xO,new T(function(){var _xR=B(A3(_x6,_xM,_xP,_));return E(_xR);})));});return C > 19 ? new F(function(){return A2(_xJ,_xN,_xQ);}) : (++C,A2(_xJ,_xN,_xQ));},_xS=function(_xT){return E(E(_xT).b);},_xU=new T(function(){return err(new T(function(){return unCStr("Prelude.undefined");}));}),_xV=function(_xW,_xX,_xY){var _xZ=__createJSFunc(1+B(A2(_xS,_xX,new T(function(){return B(A1(_xY,_xU));})))|0,function(_y0){return C > 19 ? new F(function(){return _xL(_xW,_xX,_xY,_y0);}) : (++C,_xL(_xW,_xX,_xY,_y0));});return E(_xZ);},_y1=function(_y2,_y3,_y4){return _xV(_y2,_y3,_y4);},_y5=function(_y6,_y7,_y8){var _y9=__lst2arr(_gS(function(_ya){return _y1(_y6,_y7,_ya);},_y8));return E(_y9);},_yb=new T2(0,function(_yc){return _xV(_xx,_xH,_yc);},function(_yd){return _y5(_xx,_xH,_yd);}),_ye=function(_yf,_){var _yg=E(_yf);if(!_yg._){return __Z;}else{var _yh=_ye(_yg.b,_);return new T2(1,0,_yh);}},_yi=function(_yj,_){var _yk=__arr2lst(0,_yj);return _ye(_yk,_);},_yl=function(_ym,_){return _yi(E(_ym),_);},_yn=function(_yo,_){return _bc(_);},_yp=function(_yq,_yr,_ys,_){var _yt=__apply(_yr,E(_ys));return C > 19 ? new F(function(){return A3(_x6,_yq,_yt,_);}) : (++C,A3(_x6,_yq,_yt,_));},_yu=function(_yv,_yw,_yx,_){return C > 19 ? new F(function(){return _yp(_yv,E(_yw),_yx,_);}) : (++C,_yp(_yv,E(_yw),_yx,_));},_yy=function(_yz,_yA,_yB,_){return C > 19 ? new F(function(){return _yu(_yz,_yA,_yB,_);}) : (++C,_yu(_yz,_yA,_yB,_));},_yC=function(_yD,_yE,_){return C > 19 ? new F(function(){return _yy(new T2(0,_yn,_yl),_yD,_yE,_);}) : (++C,_yy(new T2(0,_yn,_yl),_yD,_yE,_));},_yF=function(_yG){return E(E(_yG).c);},_yH=(function(method, uri, mimeout, responseType, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, uri);xhr.responseType = responseType;if(mimeout != '') {xhr.setRequestHeader('Content-type', mimeout);}xhr.addEventListener('load', function() {if(xhr.status < 400) {cb(null, xhr.response);}else {cb({'type':'http', 'status':xhr.status, 'status-text': xhr.statusText}, null);}});xhr.addEventListener('error', function() {if(xhr.status != 0) {cb({'type':'http', 'status':xhr.status, 'status-text': xhr.statusText}, null);} else {cb({'type':'network'}, null);}});xhr.send(postdata);}),_yI=function(_yJ){return E(E(_yJ).b);},_yK=function(_yL){return E(E(_yL).b);},_yM=new T(function(){return B(_gH("src/Haste/Ajax.hs:(61,7)-(63,60)|case"));}),_yN=function(_yO){return E(E(_yO).c);},_yP=new T1(1,__Z),_yQ=function(_){return nMV(_yP);},_yR=new T0(2),_yS=function(_yT,_yU,_yV){var _yW=function(_yX){var _yY=function(_){var _yZ=E(_yU),_z0=rMV(_yZ),_z1=E(_z0);if(!_z1._){var _z2=new T(function(){var _z3=new T(function(){return B(A1(_yX,0));});return _0(_z1.b,new T2(1,new T2(0,_yV,function(_z4){return E(_z3);}),__Z));}),_=wMV(_yZ,new T2(0,_z1.a,_z2));return _yR;}else{var _z5=E(_z1.a);if(!_z5._){var _=wMV(_yZ,new T2(0,_yV,__Z));return new T(function(){return B(A1(_yX,0));});}else{var _=wMV(_yZ,new T1(1,_z5.b));return new T1(1,new T2(1,new T(function(){return B(A1(_yX,0));}),new T2(1,new T(function(){return B(A2(_z5.a,_yV,_1v));}),__Z)));}}};return new T1(0,_yY);};return C > 19 ? new F(function(){return A2(_yI,_yT,_yW);}) : (++C,A2(_yI,_yT,_yW));},_z6=function(_z7){return E(E(_z7).d);},_z8=function(_z9,_za){var _zb=function(_zc){var _zd=function(_){var _ze=E(_za),_zf=rMV(_ze),_zg=E(_zf);if(!_zg._){var _zh=_zg.a,_zi=E(_zg.b);if(!_zi._){var _=wMV(_ze,_yP);return new T(function(){return B(A1(_zc,_zh));});}else{var _zj=E(_zi.a),_=wMV(_ze,new T2(0,_zj.a,_zi.b));return new T1(1,new T2(1,new T(function(){return B(A1(_zc,_zh));}),new T2(1,new T(function(){return B(A1(_zj.b,_1v));}),__Z)));}}else{var _zk=new T(function(){var _zl=function(_zm){var _zn=new T(function(){return B(A1(_zc,_zm));});return function(_zo){return E(_zn);};};return _0(_zg.a,new T2(1,_zl,__Z));}),_=wMV(_ze,new T1(1,_zk));return _yR;}};return new T1(0,_zd);};return C > 19 ? new F(function(){return A2(_yI,_z9,_zb);}) : (++C,A2(_yI,_z9,_zb));},_zp=function(_zq,_zr,_zs,_zt,_zu,_zv){var _zw=_vw(_zq),_zx=new T(function(){return _yI(_zq);}),_zy=new T(function(){return _yK(_zw);}),_zz=_vy(_zw),_zA=new T(function(){return _vA(_zs);}),_zB=new T(function(){var _zC=function(_zD){var _zE=E(_zt),_zF=strEq(E(_f),_zE);if(!E(_zF)){var _zG=_zE;}else{var _zG=B(A2(_yN,_zr,0));}return function(_y0){return C > 19 ? new F(function(){return _vo(_yb,_yC,_yH,new T2(1,E(_xb),new T2(1,B(A2(_z6,_zs,0)),new T2(1,_zG,new T2(1,E(_zv),new T2(1,_zD,__Z))))),_y0);}) : (++C,_vo(_yb,_yC,_yH,new T2(1,E(_xb),new T2(1,B(A2(_z6,_zs,0)),new T2(1,_zG,new T2(1,E(_zv),new T2(1,_zD,__Z))))),_y0));};},_zH=function(_zI,_zJ){var _zK=E(_zt),_zL=strEq(E(_f),_zK);if(!E(_zL)){var _zM=_zK;}else{var _zM=B(A2(_yN,_zr,0));}return function(_y0){return C > 19 ? new F(function(){return _vo(_yb,_yC,_yH,new T2(1,E(_zI),new T2(1,B(A2(_z6,_zs,0)),new T2(1,_zM,new T2(1,E(_zv),new T2(1,_zJ,__Z))))),_y0);}) : (++C,_vo(_yb,_yC,_yH,new T2(1,E(_zI),new T2(1,B(A2(_z6,_zs,0)),new T2(1,_zM,new T2(1,E(_zv),new T2(1,_zJ,__Z))))),_y0));};},_zN=E(_zu);switch(_zN._){case 0:return _zC("GET");break;case 1:return _zC("DELETE");break;case 2:return _zH(new T(function(){return B(A2(_vm,_vu(_zr),_zN.a));}),"POST");break;default:return _zH(new T(function(){return B(A2(_vm,_vu(_zr),_zN.a));}),"PUT");}}),_zO=function(_zP){var _zQ=new T(function(){return B(A1(_zx,new T(function(){return B(_z8(_1E,_zP));})));}),_zR=new T(function(){var _zS=new T(function(){var _zT=function(_zU,_zV,_){var _zW=E(_zV);if(!_zW._){var _zX=E(_zU);if(!_zX._){return E(_yM);}else{return _a(new T(function(){return B(A(_yS,[_1E,_zP,new T1(0,_zX.a),_1v]));}),__Z,_);}}else{var _zY=B(A3(_x6,_zA,_zW.a,_));return _a(new T(function(){return B(A(_yS,[_1E,_zP,new T1(1,_zY),_1v]));}),__Z,_);}};return B(A1(_zB,_zT));});return B(A1(_zy,_zS));});return C > 19 ? new F(function(){return A3(_yF,_zz,_zR,_zQ);}) : (++C,A3(_yF,_zz,_zR,_zQ));};return C > 19 ? new F(function(){return A3(_1g,_zz,new T(function(){return B(A2(_yK,_zw,_yQ));}),_zO);}) : (++C,A3(_1g,_zz,new T(function(){return B(A2(_yK,_zw,_yQ));}),_zO));},_zZ=new T(function(){return err(new T(function(){return unCStr("AjaxError");}));}),_A0=function(_A1){var _A2=new T(function(){return _vj(_A1);}),_A3=new T(function(){return toJSStr(unAppCStr("Send client message ",new T(function(){return fromJSStr(E(_A2));})));}),_A4=new T(function(){return B(_zp(_1E,_v,_v,_f,new T1(2,_A2),"http://localhost:8080/cgi"));}),_A5=function(_A6){var _A7=function(_){var _A8=_bd(E(_A3));return new T(function(){var _A9=function(_Aa){var _Ab=E(_Aa);if(!_Ab._){return E(_zZ);}else{var _Ac=_Ab.a,_Ad=function(_){var _Ae=_bd(toJSStr(unAppCStr("Got server response ",new T(function(){return fromJSStr(E(_Ac));})))),_Af=function(_){var _Ag=_uM(E(_Ac),_),_Ah=_Ag,_Ai=function(_){var _Aj=_bd(toJSStr(unAppCStr("Decoded server message ",new T(function(){var _Ak=E(_Ah);return B(A(_5S,[0,_Ak.a,_Ak.b,_Ak.c,_Ak.d,__Z]));}))));return new T(function(){return B(A1(_A6,_Ah));});};return new T1(0,_Ai);};return new T1(0,_Af);};return new T1(0,_Ad);}};return B(A1(_A4,_A9));});};return new T1(0,_A7);};return _A5;},_Al=new T(function(){return unAppCStr(") is outside of enumeration\'s range (0,",new T(function(){return _1V(0,2,new T(function(){return unCStr(")");}));}));}),_Am=function(_An){return err(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return _1V(0,_An,_Al);})));},_Ao=function(_Ap,_){return new T(function(){var _Aq=Number(E(_Ap)),_Ar=jsTrunc(_Aq);if(_Ar<0){return _Am(_Ar);}else{if(_Ar>2){return _Am(_Ar);}else{return _Ar;}}});},_As=new T3(0,0,0,0),_At=new T(function(){return jsGetMouseCoords;}),_Au=function(_Av,_){var _Aw=E(_Av);if(!_Aw._){return __Z;}else{var _Ax=_Au(_Aw.b,_);return new T2(1,new T(function(){var _Ay=Number(E(_Aw.a));return jsTrunc(_Ay);}),_Ax);}},_Az=function(_AA,_){var _AB=__arr2lst(0,_AA);return _Au(_AB,_);},_AC=function(_AD,_){return new T(function(){var _AE=Number(E(_AD));return jsTrunc(_AE);});},_AF=new T2(0,_AC,function(_AG,_){return _Az(E(_AG),_);}),_AH=function(_AI,_){var _AJ=E(_AI);if(!_AJ._){return __Z;}else{var _AK=_AH(_AJ.b,_);return new T2(1,_AJ.a,_AK);}},_AL=new T(function(){return _wG(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9");}),__Z,__Z));}),_AM=function(_){return die(_AL);},_AN=function(_AO,_AP,_AQ,_){var _AR=__arr2lst(0,_AQ),_AS=_AH(_AR,_),_AT=E(_AS);if(!_AT._){return _AM(_);}else{var _AU=E(_AT.b);if(!_AU._){return _AM(_);}else{if(!E(_AU.b)._){var _AV=B(A3(_x6,_AO,_AT.a,_)),_AW=B(A3(_x6,_AP,_AU.a,_));return new T2(0,_AV,_AW);}else{return _AM(_);}}}},_AX=function(_AY,_AZ,_){if(E(_AY)==7){var _B0=E(_At)(_AZ),_B1=_AN(_AF,_AF,_B0,_),_B2=_AZ["deltaX"],_B3=_AZ["deltaY"],_B4=_AZ["deltaZ"];return new T(function(){return new T3(0,E(_B1),E(__Z),E(new T3(0,_B2,_B3,_B4)));});}else{var _B5=E(_At)(_AZ),_B6=_AN(_AF,_AF,_B5,_),_B7=_AZ["button"],_B8=__eq(_B7,E(_xb));if(!E(_B8)){var _B9=__isUndef(_B7);if(!E(_B9)){var _Ba=_Ao(_B7,_);return new T(function(){return new T3(0,E(_B6),E(new T1(1,_Ba)),E(_As));});}else{return new T(function(){return new T3(0,E(_B6),E(__Z),E(_As));});}}else{return new T(function(){return new T3(0,E(_B6),E(__Z),E(_As));});}}},_Bb=new T2(0,function(_Bc){switch(E(_Bc)){case 0:return "click";case 1:return "dblclick";case 2:return "mousedown";case 3:return "mouseup";case 4:return "mousemove";case 5:return "mouseover";case 6:return "mouseout";default:return "wheel";}},function(_Bd,_Be,_){return _AX(_Bd,E(_Be),_);}),_Bf=function(_Bg){return E(_Bg);},_Bh=function(_Bi,_Bj,_){var _Bk=B(A1(_Bi,_)),_Bl=B(A1(_Bj,_));return new T(function(){return B(A1(_Bk,_Bl));});},_Bm=function(_Bn,_){return _Bn;},_Bo=function(_Bp,_Bq,_){var _Br=B(A1(_Bp,_));return C > 19 ? new F(function(){return A1(_Bq,_);}) : (++C,A1(_Bq,_));},_Bs=new T(function(){return E(_wz);}),_Bt=function(_Bu){return new T6(0,__Z,7,__Z,_Bu,__Z,__Z);},_Bv=function(_Bw,_){var _Bx=new T(function(){return B(A2(_fU,_Bs,new T(function(){return B(A1(_Bt,_Bw));})));});return die(_Bx);},_By=function(_Bz,_){return _Bv(_Bz,_);},_BA=new T2(0,new T5(0,new T5(0,new T2(0,_1o,function(_BB,_BC,_){var _BD=B(A1(_BC,_));return _BB;}),_Bm,_Bh,_Bo,function(_BE,_BF,_){var _BG=B(A1(_BE,_)),_BH=B(A1(_BF,_));return _BG;}),function(_BI,_BJ,_){var _BK=B(A1(_BI,_));return C > 19 ? new F(function(){return A2(_BJ,_BK,_);}) : (++C,A2(_BJ,_BK,_));},_Bo,_Bm,function(_BL){return C > 19 ? new F(function(){return A1(_By,_BL);}) : (++C,A1(_By,_BL));}),_1C),_BM=new T2(0,_BA,_Bm),_BN=new T(function(){return err(new T(function(){return unCStr("Map.!: given key is not an element in the map");}));}),_BO=function(_BP,_BQ){while(1){var _BR=E(_BQ);if(!_BR._){switch(_bg(_BP,_BR.b)){case 0:_BQ=_BR.d;continue;case 1:return E(_BR.c);default:_BQ=_BR.e;continue;}}else{return E(_BN);}}},_BS=function(_BT){return E(E(_BT).d);},_BU=new T2(0,_1C,function(_BV,_BW){return C > 19 ? new F(function(){return A2(_BS,_vy(_BV),new T1(1,_BW));}) : (++C,A2(_BS,_vy(_BV),new T1(1,_BW)));}),_BX=(function(t){return document.createElement(t);}),_BY=function(_){return _BX("div");},_BZ=new T(function(){return _x8(function(_){return nMV(__Z);});}),_C0=(function(e){if(e){e.stopPropagation();}}),_C1=function(_){var _C2=rMV(E(_BZ)),_C3=E(_C2);if(!_C3._){var _C4=_C0(E(_xb));return _bc(_);}else{var _C5=_C0(E(_C3.a));return _bc(_);}},_C6=function(_C7,_){var _C8=_C1(_);return 0;},_C9=(function(c,p){p.appendChild(c);}),_Ca=new T(function(){return _22(new T(function(){return unCStr("head");}));}),_Cb=(function(e){while(e.firstChild){e.removeChild(e.firstChild);}}),_Cc=(function(c,p){p.removeChild(c);}),_Cd=new T(function(){return document.body;}),_Ce=function(_,_Cf){var _Cg=E(_Cf);if(!_Cg._){return 0;}else{var _Ch=E(_Cg.a),_Ci=_Cb(_Ch),_Cj=_Cc(_Ch,E(_Cd));return _bc(_);}},_Ck=(function(id){return document.getElementById(id);}),_Cl=function(_Cm,_){var _Cn=_Ck(toJSStr(E(_Cm))),_Co=__eq(_Cn,E(_xb));if(!E(_Co)){var _Cp=__isUndef(_Cn);if(!E(_Cp)){return _Ce(_,new T1(1,_Cn));}else{return _Ce(_,__Z);}}else{return _Ce(_,__Z);}},_Cq=function(_Cr){return fromJSStr(E(_Cr));},_Cs=function(_Ct){return E(E(_Ct).a);},_Cu=(function(e,p){return e.hasAttribute(p) ? e.getAttribute(p) : '';}),_Cv=function(_Cw,_Cx,_Cy,_Cz){var _CA=new T(function(){var _CB=function(_){var _CC=_Cu(B(A2(_Cs,_Cw,_Cy)),E(_Cz));return new T(function(){return String(_CC);});};return _CB;});return C > 19 ? new F(function(){return A2(_yK,_Cx,_CA);}) : (++C,A2(_yK,_Cx,_CA));},_CD=function(_CE,_CF,_CG,_CH){var _CI=_vy(_CF),_CJ=new T(function(){return _BS(_CI);}),_CK=function(_CL){return C > 19 ? new F(function(){return A1(_CJ,new T(function(){return _Cq(_CL);}));}) : (++C,A1(_CJ,new T(function(){return _Cq(_CL);})));},_CM=new T(function(){return B(_Cv(_CE,_CF,_CG,new T(function(){return toJSStr(E(_CH));},1)));});return C > 19 ? new F(function(){return A3(_1g,_CI,_CM,_CK);}) : (++C,A3(_1g,_CI,_CM,_CK));},_CN=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_CO=function(_CP,_CQ,_CR,_CS){var _CT=new T(function(){var _CU=function(_){var _CV=_CN(B(A2(_Cs,_CP,_CR)),E(_CS));return new T(function(){return String(_CV);});};return _CU;});return C > 19 ? new F(function(){return A2(_yK,_CQ,_CT);}) : (++C,A2(_yK,_CQ,_CT));},_CW=function(_CX,_CY,_CZ,_D0){var _D1=_vy(_CY),_D2=new T(function(){return _BS(_D1);}),_D3=function(_D4){return C > 19 ? new F(function(){return A1(_D2,new T(function(){return _Cq(_D4);}));}) : (++C,A1(_D2,new T(function(){return _Cq(_D4);})));},_D5=new T(function(){return B(_CO(_CX,_CY,_CZ,new T(function(){return toJSStr(E(_D0));},1)));});return C > 19 ? new F(function(){return A3(_1g,_D1,_D5,_D3);}) : (++C,A3(_1g,_D1,_D5,_D3));},_D6=new T(function(){return unCStr("suggestionList");}),_D7=function(_D8){var _D9=E(_D8);if(!_D9._){return __Z;}else{var _Da=new T(function(){return _0(E(_D9.a).b,new T(function(){return _D7(_D9.b);},1));});return new T2(1,32,_Da);}},_Db=new T(function(){return new T2(0,E(new T1(2,"id")),"suggestionList");}),_Dc=new T(function(){return unCStr("path");}),_Dd=new T(function(){return err(_tv);}),_De=new T(function(){return err(_tu);}),_Df=new T(function(){return B(A3(_sc,_sF,0,_to));}),_Dg=new T(function(){return new T1(1,"left");}),_Dh=new T(function(){return unCStr("px");}),_Di=new T(function(){return err(_tv);}),_Dj=new T(function(){return unAppCStr("[]",__Z);}),_Dk=new T(function(){return err(_tu);}),_Dl=new T(function(){return B(_sP(_sM,_to));}),_Dm=new T(function(){return new T1(1,"top");}),_Dn=new T(function(){return new T2(0,E(new T1(2,"class")),"menu");}),_Do=new T(function(){return unCStr("offsetTop");}),_Dp=new T(function(){return unCStr("offsetLeft");}),_Dq=new T(function(){return unCStr("menuHover");}),_Dr=(function(e,c) {e.classList.toggle(c);}),_Ds=function(_Dt,_){var _Du=_Dr(_Dt,toJSStr(E(_Dq)));return _bc(_);},_Dv=new T(function(){return unCStr("div");}),_Dw=(function(s){return document.createTextNode(s);}),_Dx=function(_Dy){return E(E(_Dy).a);},_Dz=function(_DA){return E(E(_DA).b);},_DB=function(_DC){return E(E(_DC).a);},_DD=function(_DE){return E(E(_DE).b);},_DF=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_DG=function(_DH,_DI,_DJ,_DK,_DL,_DM){var _DN=_Dx(_DH),_DO=_vy(_DN),_DP=new T(function(){return _yK(_DN);}),_DQ=new T(function(){return _BS(_DO);}),_DR=new T(function(){return B(A1(_DI,_DK));}),_DS=new T(function(){return B(A2(_DB,_DJ,_DL));}),_DT=function(_DU){return C > 19 ? new F(function(){return A1(_DQ,new T3(0,_DS,_DR,_DU));}) : (++C,A1(_DQ,new T3(0,_DS,_DR,_DU)));},_DV=function(_DW){var _DX=new T(function(){var _DY=new T(function(){var _DZ=__createJSFunc(2,function(_E0,_){var _E1=B(A2(E(_DW),_E0,_));return _xb;}),_E2=_DZ;return function(_){return _DF(E(_DR),E(_DS),_E2);};});return B(A1(_DP,_DY));});return C > 19 ? new F(function(){return A3(_1g,_DO,_DX,_DT);}) : (++C,A3(_1g,_DO,_DX,_DT));},_E3=new T(function(){var _E4=new T(function(){return _yK(_DN);}),_E5=function(_E6){var _E7=new T(function(){return B(A1(_E4,function(_){var _=wMV(E(_BZ),new T1(1,_E6));return C > 19 ? new F(function(){return A(_Dz,[_DJ,_DL,_E6,_]);}) : (++C,A(_Dz,[_DJ,_DL,_E6,_]));}));});return C > 19 ? new F(function(){return A3(_1g,_DO,_E7,_DM);}) : (++C,A3(_1g,_DO,_E7,_DM));};return B(A2(_DD,_DH,_E5));});return C > 19 ? new F(function(){return A3(_1g,_DO,_E3,_DV);}) : (++C,A3(_1g,_DO,_E3,_DV));},_E8=function(_E9,_Ea,_Eb,_){var _Ec=_Dw(toJSStr(E(_Ea))),_Ed=_BX(toJSStr(E(_Dv))),_Ee=_Ed,_Ef=B(A(_DG,[_BM,_Bf,_Bb,_Ee,5,function(_Eg,_){return _Ds(_Ee,_);},_])),_Eh=B(A(_DG,[_BM,_Bf,_Bb,_Ee,6,function(_Ei,_){return _Ds(_Ee,_);},_])),_Ej=B(A(_DG,[_BM,_Bf,_Bb,_Ee,0,_Eb,_])),_Ek=_C9(_Ec,_Ee),_El=_C9(_Ee,E(_E9));return 0;},_Em=function(_En){var _Eo=E(_En);if(!_Eo._){return E(new T2(1,93,__Z));}else{var _Ep=new T(function(){return _1V(0,E(_Eo.a),new T(function(){return _Em(_Eo.b);}));});return new T2(1,44,_Ep);}},_Eq=(function(e,p,v){e.setAttribute(p, v);}),_Er=(function(e,p,v){e.style[p] = v;}),_Es=(function(e,p,v){e[p] = v;}),_Et=function(_Eu,_Ev,_Ew,_Ex){var _Ey=new T(function(){return B(A2(_Cs,_Eu,_Ew));}),_Ez=function(_EA,_){var _EB=E(_EA);if(!_EB._){return 0;}else{var _EC=E(_Ey),_ED=_C9(E(_EB.a),_EC),_EE=function(_EF,_){while(1){var _EG=E(_EF);if(!_EG._){return 0;}else{var _EH=_C9(E(_EG.a),_EC);_EF=_EG.b;continue;}}};return _EE(_EB.b,_);}},_EI=function(_EJ,_){while(1){var _EK=(function(_EL,_){var _EM=E(_EL);if(!_EM._){return 0;}else{var _EN=_EM.b,_EO=E(_EM.a);if(!_EO._){var _EP=_EO.b,_EQ=E(_EO.a);switch(_EQ._){case 0:var _ER=E(_Ey),_ES=_Es(_ER,_EQ.a,_EP),_ET=function(_EU,_){while(1){var _EV=E(_EU);if(!_EV._){return 0;}else{var _EW=_EV.b,_EX=E(_EV.a);if(!_EX._){var _EY=_EX.b,_EZ=E(_EX.a);switch(_EZ._){case 0:var _F0=_Es(_ER,_EZ.a,_EY);_EU=_EW;continue;case 1:var _F1=_Er(_ER,_EZ.a,_EY);_EU=_EW;continue;default:var _F2=_Eq(_ER,_EZ.a,_EY);_EU=_EW;continue;}}else{var _F3=_Ez(_EX.a,_);_EU=_EW;continue;}}}};return _ET(_EN,_);case 1:var _F4=E(_Ey),_F5=_Er(_F4,_EQ.a,_EP),_F6=function(_F7,_){while(1){var _F8=E(_F7);if(!_F8._){return 0;}else{var _F9=_F8.b,_Fa=E(_F8.a);if(!_Fa._){var _Fb=_Fa.b,_Fc=E(_Fa.a);switch(_Fc._){case 0:var _Fd=_Es(_F4,_Fc.a,_Fb);_F7=_F9;continue;case 1:var _Fe=_Er(_F4,_Fc.a,_Fb);_F7=_F9;continue;default:var _Ff=_Eq(_F4,_Fc.a,_Fb);_F7=_F9;continue;}}else{var _Fg=_Ez(_Fa.a,_);_F7=_F9;continue;}}}};return _F6(_EN,_);default:var _Fh=E(_Ey),_Fi=_Eq(_Fh,_EQ.a,_EP),_Fj=function(_Fk,_){while(1){var _Fl=E(_Fk);if(!_Fl._){return 0;}else{var _Fm=_Fl.b,_Fn=E(_Fl.a);if(!_Fn._){var _Fo=_Fn.b,_Fp=E(_Fn.a);switch(_Fp._){case 0:var _Fq=_Es(_Fh,_Fp.a,_Fo);_Fk=_Fm;continue;case 1:var _Fr=_Er(_Fh,_Fp.a,_Fo);_Fk=_Fm;continue;default:var _Fs=_Eq(_Fh,_Fp.a,_Fo);_Fk=_Fm;continue;}}else{var _Ft=_Ez(_Fn.a,_);_Fk=_Fm;continue;}}}};return _Fj(_EN,_);}}else{var _Fu=_Ez(_EO.a,_);_EJ=_EN;return __continue;}}})(_EJ,_);if(_EK!=__continue){return _EK;}}};return C > 19 ? new F(function(){return A2(_yK,_Ev,function(_){return _EI(_Ex,_);});}) : (++C,A2(_yK,_Ev,function(_){return _EI(_Ex,_);}));},_Fv=function(_Fw,_Fx,_Fy,_Fz){var _FA=_vy(_Fx),_FB=function(_FC){return C > 19 ? new F(function(){return A3(_yF,_FA,new T(function(){return B(_Et(_Fw,_Fx,_FC,_Fz));}),new T(function(){return B(A2(_BS,_FA,_FC));}));}) : (++C,A3(_yF,_FA,new T(function(){return B(_Et(_Fw,_Fx,_FC,_Fz));}),new T(function(){return B(A2(_BS,_FA,_FC));})));};return C > 19 ? new F(function(){return A3(_1g,_FA,_Fy,_FB);}) : (++C,A3(_1g,_FA,_Fy,_FB));},_FD=function(_FE,_FF,_FG,_){var _FH=_C1(_),_FI=B(A(_CW,[_BU,_BA,_FE,_Dp,_])),_FJ=B(A(_CW,[_BU,_BA,_FE,_Do,_])),_FK=_Cl(_D6,_),_FL=B(A(_CD,[_BU,_BA,_FE,_Dc,_])),_FM=new T(function(){var _FN=_tw(_hq(_Dl,_FL));if(!_FN._){return E(_Di);}else{if(!E(_FN.b)._){var _FO=E(_FN.a);if(!_FO._){return E(_Dj);}else{var _FP=new T(function(){return _1V(0,E(_FO.a),new T(function(){return _Em(_FO.b);}));});return new T2(1,91,_FP);}}else{return E(_Dk);}}}),_FQ=_bd(toJSStr(unAppCStr("Selected Path ",_FM))),_FR=new T(function(){return E(E(_FG).a);}),_FS=B(A(_Fv,[_BU,_BA,_BY,new T2(1,_Db,new T2(1,_Dn,new T2(1,new T(function(){var _FT=_tw(_hq(_Df,_FJ));if(!_FT._){return E(_Dd);}else{if(!E(_FT.b)._){return new T2(0,E(_Dm),toJSStr(_0(_1V(0,E(E(_FR).b)+E(_FT.a)|0,__Z),_Dh)));}else{return E(_De);}}}),new T2(1,new T(function(){var _FU=_tw(_hq(_Df,_FI));if(!_FU._){return E(_Dd);}else{if(!E(_FU.b)._){return new T2(0,E(_Dg),toJSStr(_0(_1V(0,E(E(_FR).a)+E(_FU.a)|0,__Z),_Dh)));}else{return E(_De);}}}),__Z)))),_])),_FV=_FS,_FW=E(_FF);if(!_FW._){return E(_Ca);}else{var _FX=function(_FY,_){while(1){var _FZ=E(_FY);if(!_FZ._){return 0;}else{var _G0=_FZ.b,_G1=_D7(E(_FZ.a).b);if(!_G1._){var _G2=_E8(_FV,__Z,_C6,_);_FY=_G0;continue;}else{var _G3=_E8(_FV,_G1.b,_C6,_);_FY=_G0;continue;}}}},_G4=_FX(_FW.a,_),_G5=_C9(E(_FV),E(_Cd));return 0;}},_G6=function(_){return _BX("span");},_G7=new T(function(){return B(_Fv(_BU,_BA,function(_){return _BX("span");},new T2(1,new T(function(){return new T2(0,E(new T1(2,"class")),"path");}),__Z)));}),_G8=new T(function(){return new T1(2,"path");}),_G9=new T(function(){return new T2(0,E(new T1(2,"class")),"word");}),_Ga=new T(function(){return new T2(0,E(new T1(2,"class")),"gap");}),_Gb=new T(function(){return unCStr(" ");}),_Gc=new T(function(){return unCStr("wordHover");}),_Gd=function(_Ge,_){var _Gf=_Dr(_Ge,toJSStr(E(_Gc)));return _bc(_);},_Gg=function(_Gh,_Gi,_){return _Gd(E(_Gh),_);},_Gj=function(_Gk,_Gl,_Gm,_Gn,_Go,_Gp,_Gq,_){var _Gr=function(_){var _Gs=B(A(_Fv,[_BU,_BA,_G6,new T2(1,_G9,new T2(1,new T(function(){return new T2(0,E(_G8),toJSStr(_3p(_3A,_Gl,__Z)));}),__Z)),_])),_Gt=_Gs,_Gu=_Dw(toJSStr(E(_Gm))),_Gv=B(A(_DG,[_BM,_Bf,_Bb,_Gt,5,function(_Gw,_){return _Gg(_Gt,_Gw,_);},_])),_Gx=B(A(_DG,[_BM,_Bf,_Bb,_Gt,6,function(_Gw,_){return _Gg(_Gt,_Gw,_);},_])),_Gy=E(_Gt),_Gz=_C9(_Gu,_Gy),_GA=E(_Gk),_GB=_C9(_Gy,_GA),_GC=function(_){if(!E(_Go)){return 0;}else{var _GD=B(A1(_G7,_)),_GE=_Dw(toJSStr(_3p(_3A,_Gl,__Z))),_GF=E(_GD),_GG=_C9(_GE,_GF),_GH=_C9(_GF,_GA);return _bc(_);}};if(!E(_Gq)){return _GC(_);}else{var _GI=B(A(_DG,[_BM,_Bf,_Bb,_Gy,0,function(_GJ,_){return _FD(_Gy,_Gn,_GJ,_);},_]));return _GC(_);}};if(!E(_Gp)){return _Gr(_);}else{var _GK=B(A(_Fv,[_BU,_BA,_G6,new T2(1,_Ga,new T2(1,new T(function(){return new T2(0,E(_G8),toJSStr(_3p(_3A,_Gl,__Z)));}),__Z)),_])),_GL=_GK,_GM=_Dw(toJSStr(E(_Gb))),_GN=B(A(_DG,[_BM,_Bf,_Bb,_GL,5,function(_Gw,_){return _Gg(_GL,_Gw,_);},_])),_GO=B(A(_DG,[_BM,_Bf,_Bb,_GL,6,function(_Gw,_){return _Gg(_GL,_Gw,_);},_])),_GP=E(_GL),_GQ=_C9(_GM,_GP),_GR=_C9(_GP,E(_Gk));if(!E(_Gq)){return _Gr(_);}else{var _GS=B(A(_DG,[_BM,_Bf,_Bb,_GP,0,function(_GT,_){return _FD(_GP,_Gn,_GT,_);},_]));return _Gr(_);}}},_GU=(function(e,c) {return e.classList.contains(c);}),_GV=new T(function(){return unCStr("debug");}),_GW=new T(function(){return _wG(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:63:5-23");}),__Z,__Z));}),_GX=new T(function(){return unCStr("exampleTree");}),_GY=function(_GZ,_H0,_){var _H1=_Ck(toJSStr(E(_GX))),_H2=__eq(_H1,E(_xb)),_H3=function(_,_H4){var _H5=E(_H4);if(!_H5._){return die(_GW);}else{var _H6=E(_H5.a),_H7=_Cb(_H6),_H8=_GU(_H6,toJSStr(E(_GV))),_H9=_H8,_Ha=function(_Hb,_){while(1){var _Hc=(function(_Hd,_){var _He=E(_Hd);if(!_He._){return 0;}else{var _Hf=E(_He.a),_Hg=_Hf.a,_Hh=B(_Gj(_H6,_Hg,_Hf.b,new T(function(){return _BO(_Hg,_H0);}),_H9,false,false,_));_Hb=_He.b;return __continue;}})(_Hb,_);if(_Hc!=__continue){return _Hc;}}},_Hi=_Ha(_GZ,_);return 0;}};if(!E(_H2)){var _Hj=__isUndef(_H1);if(!E(_Hj)){return _H3(_,new T1(1,_H1));}else{return _H3(_,__Z);}}else{return _H3(_,__Z);}},_Hk=new T(function(){return _wG(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:116:5-24");}),__Z,__Z));}),_Hl=new T(function(){return unCStr("exerciseTree");}),_Hm=function(_Hn,_Ho,_){var _Hp=_Ck(toJSStr(E(_Hl))),_Hq=__eq(_Hp,E(_xb)),_Hr=function(_,_Hs){var _Ht=E(_Hs);if(!_Ht._){return die(_Hk);}else{var _Hu=E(_Ht.a),_Hv=_Cb(_Hu),_Hw=_GU(_Hu,toJSStr(E(_GV))),_Hx=_Hw,_Hy=function(_Hz,_){while(1){var _HA=(function(_HB,_){var _HC=E(_HB);if(!_HC._){return 0;}else{var _HD=E(_HC.a),_HE=_HD.a,_HF=B(_Gj(_Hu,_HE,_HD.b,new T(function(){return _BO(_HE,_Ho);}),_Hx,true,true,_));_Hz=_HC.b;return __continue;}})(_Hz,_);if(_HA!=__continue){return _HA;}}},_HG=_Hy(_Hn,_);return 0;}};if(!E(_Hq)){var _HH=__isUndef(_Hp);if(!E(_HH)){return _Hr(_,new T1(1,_Hp));}else{return _Hr(_,__Z);}}else{return _Hr(_,__Z);}},_HI=new T(function(){return unCStr("won");}),_HJ=new T(function(){return _wG(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:53:5-16");}),__Z,__Z));}),_HK=new T(function(){return unCStr("score");}),_HL=(function(e,c,x){x?e.classList.add(c):e.classList.remove(c);}),_HM=function(_HN,_HO,_){var _HP=_Ck(toJSStr(E(_HK))),_HQ=__eq(_HP,E(_xb)),_HR=function(_,_HS){var _HT=E(_HS);if(!_HT._){return die(_HJ);}else{var _HU=E(_HT.a),_HV=_Cb(_HU),_HW=_Dw(toJSStr(_1V(0,E(_HN),__Z))),_HX=_HL(_HU,toJSStr(E(_HI)),E(_HO)),_HY=_C9(_HW,_HU);return _bc(_);}};if(!E(_HQ)){var _HZ=__isUndef(_HP);if(!E(_HZ)){return _HR(_,new T1(1,_HP));}else{return _HR(_,__Z);}}else{return _HR(_,__Z);}},_I0=new T(function(){return unCStr("laetus");}),_I1=new T2(1,0,__Z),_I2=new T(function(){return unCStr("est");}),_I3=new T(function(){return unCStr("Augustus");}),_I4=new T(function(){return unCStr("menuList");}),_I5=new T(function(){return unCStr("Reset");}),_I6=new T(function(){return unCStr("Toggle Debug");}),_I7=new T(function(){return _wG(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:198:51-57");}),__Z,__Z));}),_I8=new T(function(){return _wG(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:198:87-93");}),__Z,__Z));}),_I9=new T(function(){return new T2(0,E(new T1(2,"id")),"menuList");}),_Ia=function(_Ib,_Ic,_){var _Id=_C1(_),_Ie=B(A(_CW,[_BU,_BA,_Ib,_Dp,_])),_If=B(A(_CW,[_BU,_BA,_Ib,_Do,_])),_Ig=_Cl(_I4,_),_Ih=B(A(_Fv,[_BU,_BA,_BY,new T2(1,_I9,new T2(1,_Dn,new T2(1,new T(function(){return new T2(0,E(_Dm),toJSStr(_0(_If,_Dh)));}),new T2(1,new T(function(){var _Ii=_tw(_hq(_Df,_Ie));if(!_Ii._){return E(_Dd);}else{if(!E(_Ii.b)._){return new T2(0,E(_Dg),toJSStr(_0(_1V(0,E(_Ii.a)-200|0,__Z),_Dh)));}else{return E(_De);}}}),__Z)))),_])),_Ij=function(_Ik,_){var _Il=_Ck(toJSStr(E(_GX))),_Im=E(_xb),_In=__eq(_Il,_Im),_Io=function(_,_Ip){var _Iq=E(_Ip);if(!_Iq._){return die(_I7);}else{var _Ir=_Ck(toJSStr(E(_Hl))),_Is=__eq(_Ir,_Im),_It=function(_,_Iu){var _Iv=E(_Iu);if(!_Iv._){return die(_I8);}else{var _Iw=toJSStr(E(_GV)),_Ix=_Dr(E(_Iq.a),_Iw),_Iy=_Dr(E(_Iv.a),_Iw),_Iz=E(_Ic),_IA=E(_Iz.c),_IB=_Hm(_IA.c,E(_IA.d).a,_),_IC=E(_Iz.d);return _GY(_IC.c,E(_IC.d).a,_);}};if(!E(_Is)){var _ID=__isUndef(_Ir);if(!E(_ID)){return C > 19 ? new F(function(){return _It(_,new T1(1,_Ir));}) : (++C,_It(_,new T1(1,_Ir)));}else{return C > 19 ? new F(function(){return _It(_,__Z);}) : (++C,_It(_,__Z));}}else{return C > 19 ? new F(function(){return _It(_,__Z);}) : (++C,_It(_,__Z));}}};if(!E(_In)){var _IE=__isUndef(_Il);if(!E(_IE)){return C > 19 ? new F(function(){return _Io(_,new T1(1,_Il));}) : (++C,_Io(_,new T1(1,_Il)));}else{return C > 19 ? new F(function(){return _Io(_,__Z);}) : (++C,_Io(_,__Z));}}else{return C > 19 ? new F(function(){return _Io(_,__Z);}) : (++C,_Io(_,__Z));}},_IF=_E8(_Ih,_I6,_Ij,_),_IG=_E8(_Ih,_I5,function(_IH,_){var _II=_Hm(new T2(1,new T2(0,new T2(1,0,new T2(1,0,new T2(1,0,_I1))),_I3),new T2(1,new T2(0,new T2(1,0,new T2(1,0,new T2(1,1,_I1))),_I0),new T2(1,new T2(0,new T2(1,0,new T2(1,0,new T2(1,1,__Z))),_I2),__Z))),E(E(E(_Ic).d).d).a,_);return _HM(0,false,_);},_),_IJ=_C9(E(_Ih),E(_Cd));return 0;},_IK=function(_){var _IL=_Cl(_D6,_);return _Cl(_I4,_);},_IM=new T(function(){return B(_DG(_BM,_Bf,_Bb,_Cd,0,function(_IN,_){return C > 19 ? new F(function(){return _IK(_);}) : (++C,_IK(_));}));}),_IO=new T(function(){return _wG(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:38:5-13");}),__Z,__Z));}),_IP=new T(function(){return unCStr("Draw exercise tree");}),_IQ=new T(function(){return unCStr("Draw example tree");}),_IR=new T(function(){return unCStr("menuButton");}),_IS=function(_IT,_){var _IU=B(A1(_IM,_)),_IV=_Ck(toJSStr(E(_IR))),_IW=__eq(_IV,E(_xb)),_IX=function(_,_IY){var _IZ=E(_IY);if(!_IZ._){return die(_IO);}else{var _J0=_IZ.a,_J1=B(A(_DG,[_BM,_Bf,_Bb,_J0,0,function(_J2,_){return _Ia(_J0,_IT,_);},_])),_J3=_bd(toJSStr(E(_IQ))),_J4=E(_IT),_J5=E(_J4.c),_J6=_GY(_J5.c,E(_J5.d).a,_),_J7=_bd(toJSStr(E(_IP))),_J8=E(_J4.d),_J9=_Hm(_J8.c,E(_J8.d).a,_),_Ja=_HM(_J4.b,_J4.a,_);return 0;}};if(!E(_IW)){var _Jb=__isUndef(_IV);if(!E(_Jb)){return _IX(_,new T1(1,_IV));}else{return _IX(_,__Z);}}else{return _IX(_,__Z);}},_Jc=function(_Jd){return new T1(0,function(_){var _Je=_IS(_Jd,_);return _yR;});},_Jf=new T(function(){return B(A2(_A0,new T3(1,-1,new T2(0,new T(function(){return unCStr("PrimaEng");}),new T(function(){return unCStr("(useS (useCl (simpleCl (usePron he_PP) (complA Romanus_A))))");})),new T2(0,new T(function(){return unCStr("PrimaLat");}),new T(function(){return unCStr("useS (useCl (simpleCl (usePN Augustus_PN) (complA laetus_A)))");}))),_Jc));}),_Jg=function(_){var _Jh=_a(_Jf,__Z,_);return 0;},_Ji=function(_){return _Jg(_);};
var hasteMain = function() {B(A(_Ji, [0]));};window.onload = hasteMain;