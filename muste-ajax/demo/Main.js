"use strict";
var __haste_prog_id = '32bf27eb647579dbfb4daad14558522302cd52dcf508e9f2a3cff66c15910acb';
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

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return _0(_3.b,_2);}));},_4=function(_5,_){while(1){var _6=E(_5);if(!_6._){return 0;}else{var _7=_6.b,_8=E(_6.a);switch(_8._){case 0:var _9=B(A1(_8.a,_));_5=_0(_7,new T2(1,_9,__Z));continue;case 1:_5=_0(_7,_8.a);continue;default:_5=_7;continue;}}}},_a=function(_b,_c,_){var _d=E(_b);switch(_d._){case 0:var _e=B(A1(_d.a,_));return _4(_0(_c,new T2(1,_e,__Z)),_);case 1:return _4(_0(_c,_d.a),_);default:return _4(_c,_);}},_f=new T(function(){return toJSStr(__Z);}),_g=function(_h){return E(_f);},_i=function(_j,_){var _k=E(_j);if(!_k._){return __Z;}else{var _l=_i(_k.b,_);return new T2(1,new T(function(){return String(E(_k.a));}),_l);}},_m=function(_n,_){var _o=__arr2lst(0,_n);return _i(_o,_);},_p=function(_q){return String(E(_q));},_r=function(_s){return _p(_s);},_t=function(_u,_){return new T(function(){return _r(_u);});},_v=new T4(0,new T2(0,function(_w){return E(_w);},function(_x){return __lst2arr(E(_x));}),new T2(0,_t,function(_y,_){return _m(E(_y),_);}),_g,_g),_z=function(_A,_B,_C){var _D=function(_E){var _F=new T(function(){return B(A1(_C,_E));});return C > 19 ? new F(function(){return A1(_B,function(_G){return E(_F);});}) : (++C,A1(_B,function(_G){return E(_F);}));};return C > 19 ? new F(function(){return A1(_A,_D);}) : (++C,A1(_A,_D));},_H=function(_I,_J,_K){var _L=new T(function(){return B(A1(_J,function(_M){return C > 19 ? new F(function(){return A1(_K,_M);}) : (++C,A1(_K,_M));}));});return C > 19 ? new F(function(){return A1(_I,function(_N){return E(_L);});}) : (++C,A1(_I,function(_N){return E(_L);}));},_O=function(_P,_Q,_R){var _S=function(_T){var _U=function(_V){return C > 19 ? new F(function(){return A1(_R,new T(function(){return B(A1(_T,_V));}));}) : (++C,A1(_R,new T(function(){return B(A1(_T,_V));})));};return C > 19 ? new F(function(){return A1(_Q,_U);}) : (++C,A1(_Q,_U));};return C > 19 ? new F(function(){return A1(_P,_S);}) : (++C,A1(_P,_S));},_W=function(_X,_Y){return C > 19 ? new F(function(){return A1(_Y,_X);}) : (++C,A1(_Y,_X));},_Z=function(_10,_11,_12){var _13=new T(function(){return B(A1(_12,_10));});return C > 19 ? new F(function(){return A1(_11,function(_14){return E(_13);});}) : (++C,A1(_11,function(_14){return E(_13);}));},_15=function(_16,_17,_18){var _19=function(_1a){return C > 19 ? new F(function(){return A1(_18,new T(function(){return B(A1(_16,_1a));}));}) : (++C,A1(_18,new T(function(){return B(A1(_16,_1a));})));};return C > 19 ? new F(function(){return A1(_17,_19);}) : (++C,A1(_17,_19));},_1b=function(_1c,_1d,_1e){return C > 19 ? new F(function(){return A1(_1c,function(_1f){return C > 19 ? new F(function(){return A2(_1d,_1f,_1e);}) : (++C,A2(_1d,_1f,_1e));});}) : (++C,A1(_1c,function(_1f){return C > 19 ? new F(function(){return A2(_1d,_1f,_1e);}) : (++C,A2(_1d,_1f,_1e));}));},_1g=function(_1h){return E(E(_1h).b);},_1i=function(_1j,_1k){return C > 19 ? new F(function(){return A3(_1g,_1l,_1j,function(_1m){return E(_1k);});}) : (++C,A3(_1g,_1l,_1j,function(_1m){return E(_1k);}));},_1l=new T(function(){return new T5(0,new T5(0,new T2(0,_15,_Z),_W,_O,_H,_z),_1b,_1i,_W,function(_1n){return err(_1n);});}),_1o=function(_1p,_1q,_){var _1r=B(A1(_1q,_));return new T(function(){return B(A1(_1p,_1r));});},_1s=function(_1t,_1u){return new T1(0,function(_){return _1o(_1u,_1t,_);});},_1v=function(_1w){return new T0(2);},_1x=function(_1y){var _1z=new T(function(){return B(A1(_1y,_1v));}),_1A=function(_1B){return new T1(1,new T2(1,new T(function(){return B(A1(_1B,0));}),new T2(1,_1z,__Z)));};return _1A;},_1C=function(_1D){return E(_1D);},_1E=new T3(0,new T2(0,_1l,_1s),_1C,_1x),_1F=new T(function(){return unCStr("}");}),_1G=new T(function(){return unCStr(", ");}),_1H=new T(function(){return unCStr("SM {");}),_1I=new T(function(){return unCStr("ssuccess = ");}),_1J=new T(function(){return unCStr("sb = ");}),_1K=new T(function(){return unCStr("sa = ");}),_1L=new T(function(){return unCStr("sscore = ");}),_1M=function(_1N,_1O,_1P){return C > 19 ? new F(function(){return A1(_1N,new T2(1,44,new T(function(){return B(A1(_1O,_1P));})));}) : (++C,A1(_1N,new T2(1,44,new T(function(){return B(A1(_1O,_1P));}))));},_1Q=new T(function(){return unCStr("M ");}),_1R=function(_1S,_1T){var _1U=jsShowI(_1S);return _0(fromJSStr(_1U),_1T);},_1V=function(_1W,_1X,_1Y){if(_1X>=0){return _1R(_1X,_1Y);}else{if(_1W<=6){return _1R(_1X,_1Y);}else{return new T2(1,40,new T(function(){var _1Z=jsShowI(_1X);return _0(fromJSStr(_1Z),new T2(1,41,_1Y));}));}}},_20=new T(function(){return unCStr(": empty list");}),_21=new T(function(){return unCStr("Prelude.");}),_22=function(_23){return err(_0(_21,new T(function(){return _0(_23,_20);},1)));},_24=new T(function(){return _22(new T(function(){return unCStr("foldr1");}));}),_25=function(_26,_27){var _28=E(_27);if(!_28._){return E(_24);}else{var _29=_28.a,_2a=E(_28.b);if(!_2a._){return E(_29);}else{return C > 19 ? new F(function(){return A2(_26,_29,new T(function(){return B(_25(_26,_2a));}));}) : (++C,A2(_26,_29,new T(function(){return B(_25(_26,_2a));})));}}},_2b=new T(function(){return unCStr("tree = ");}),_2c=new T(function(){return unCStr("lin = ");}),_2d=new T(function(){return unCStr("cost = ");}),_2e=new T(function(){return unCStr("T {");}),_2f=new T(function(){return err(new T(function(){return _0(_21,new T(function(){return unCStr("!!: negative index");}));}));}),_2g=new T(function(){return err(new T(function(){return _0(_21,new T(function(){return unCStr("!!: index too large");}));}));}),_2h=function(_2i,_2j){while(1){var _2k=E(_2i);if(!_2k._){return E(_2g);}else{var _2l=E(_2j);if(!_2l){return E(_2k.a);}else{_2i=_2k.b;_2j=_2l-1|0;continue;}}}},_2m=function(_2n,_2o){if(_2o>=0){return _2h(_2n,_2o);}else{return E(_2f);}},_2p=new T(function(){return unCStr("ACK");}),_2q=new T(function(){return unCStr("BEL");}),_2r=new T(function(){return unCStr("BS");}),_2s=new T(function(){return unCStr("SP");}),_2t=new T(function(){return unCStr("US");}),_2u=new T(function(){return unCStr("RS");}),_2v=new T(function(){return unCStr("GS");}),_2w=new T(function(){return unCStr("FS");}),_2x=new T(function(){return unCStr("ESC");}),_2y=new T(function(){return unCStr("SUB");}),_2z=new T(function(){return unCStr("EM");}),_2A=new T(function(){return unCStr("CAN");}),_2B=new T(function(){return unCStr("ETB");}),_2C=new T(function(){return unCStr("SYN");}),_2D=new T(function(){return unCStr("NAK");}),_2E=new T(function(){return unCStr("DC4");}),_2F=new T(function(){return unCStr("DC3");}),_2G=new T(function(){return unCStr("DC2");}),_2H=new T(function(){return unCStr("DC1");}),_2I=new T(function(){return unCStr("DLE");}),_2J=new T(function(){return unCStr("SI");}),_2K=new T(function(){return unCStr("SO");}),_2L=new T(function(){return unCStr("CR");}),_2M=new T(function(){return unCStr("FF");}),_2N=new T(function(){return unCStr("VT");}),_2O=new T(function(){return unCStr("LF");}),_2P=new T(function(){return unCStr("HT");}),_2Q=new T(function(){return unCStr("ENQ");}),_2R=new T(function(){return unCStr("EOT");}),_2S=new T(function(){return unCStr("ETX");}),_2T=new T(function(){return unCStr("STX");}),_2U=new T(function(){return unCStr("SOH");}),_2V=new T(function(){return unCStr("NUL");}),_2W=new T(function(){return unCStr("\\DEL");}),_2X=new T(function(){return unCStr("\\a");}),_2Y=new T(function(){return unCStr("\\\\");}),_2Z=new T(function(){return unCStr("\\SO");}),_30=new T(function(){return unCStr("\\r");}),_31=new T(function(){return unCStr("\\f");}),_32=new T(function(){return unCStr("\\v");}),_33=new T(function(){return unCStr("\\n");}),_34=new T(function(){return unCStr("\\t");}),_35=new T(function(){return unCStr("\\b");}),_36=function(_37,_38){if(_37<=127){var _39=E(_37);switch(_39){case 92:return _0(_2Y,_38);case 127:return _0(_2W,_38);default:if(_39<32){switch(_39){case 7:return _0(_2X,_38);case 8:return _0(_35,_38);case 9:return _0(_34,_38);case 10:return _0(_33,_38);case 11:return _0(_32,_38);case 12:return _0(_31,_38);case 13:return _0(_30,_38);case 14:return _0(_2Z,new T(function(){var _3a=E(_38);if(!_3a._){return __Z;}else{if(E(_3a.a)==72){return unAppCStr("\\&",_3a);}else{return _3a;}}},1));default:return _0(new T2(1,92,new T(function(){return _2m(new T2(1,_2V,new T2(1,_2U,new T2(1,_2T,new T2(1,_2S,new T2(1,_2R,new T2(1,_2Q,new T2(1,_2p,new T2(1,_2q,new T2(1,_2r,new T2(1,_2P,new T2(1,_2O,new T2(1,_2N,new T2(1,_2M,new T2(1,_2L,new T2(1,_2K,new T2(1,_2J,new T2(1,_2I,new T2(1,_2H,new T2(1,_2G,new T2(1,_2F,new T2(1,_2E,new T2(1,_2D,new T2(1,_2C,new T2(1,_2B,new T2(1,_2A,new T2(1,_2z,new T2(1,_2y,new T2(1,_2x,new T2(1,_2w,new T2(1,_2v,new T2(1,_2u,new T2(1,_2t,new T2(1,_2s,__Z))))))))))))))))))))))))))))))))),_39);})),_38);}}else{return new T2(1,_39,_38);}}}else{var _3b=new T(function(){var _3c=jsShowI(_37);return _0(fromJSStr(_3c),new T(function(){var _3d=E(_38);if(!_3d._){return __Z;}else{var _3e=E(_3d.a);if(_3e<48){return _3d;}else{if(_3e>57){return _3d;}else{return unAppCStr("\\&",_3d);}}}},1));});return new T2(1,92,_3b);}},_3f=new T(function(){return unCStr("\\\"");}),_3g=function(_3h,_3i){var _3j=E(_3h);if(!_3j._){return E(_3i);}else{var _3k=_3j.b,_3l=E(_3j.a);if(_3l==34){return _0(_3f,new T(function(){return _3g(_3k,_3i);},1));}else{return _36(_3l,new T(function(){return _3g(_3k,_3i);}));}}},_3m=function(_3n,_3o){return new T2(1,34,new T(function(){return _3g(_3n,new T2(1,34,_3o));}));},_3p=function(_3q,_3r,_3s){var _3t=E(_3r);if(!_3t._){return unAppCStr("[]",_3s);}else{var _3u=new T(function(){var _3v=new T(function(){var _3w=function(_3x){var _3y=E(_3x);if(!_3y._){return E(new T2(1,93,_3s));}else{var _3z=new T(function(){return B(A2(_3q,_3y.a,new T(function(){return _3w(_3y.b);})));});return new T2(1,44,_3z);}};return _3w(_3t.b);});return B(A2(_3q,_3t.a,_3v));});return new T2(1,91,_3u);}},_3A=function(_3B,_3C){return _1V(0,E(_3B),_3C);},_3D=function(_3E,_3F){return _3p(_3A,_3E,_3F);},_3G=function(_3H,_3I,_3J,_3K,_3L){var _3M=function(_3N){var _3O=new T(function(){var _3P=new T(function(){var _3Q=new T(function(){var _3R=new T(function(){var _3S=new T(function(){var _3T=new T(function(){var _3U=new T(function(){var _3V=new T(function(){return _3g(_3K,new T2(1,34,new T(function(){return _0(_1F,_3N);})));});return _0(_2b,new T2(1,34,_3V));},1);return _0(_1G,_3U);}),_3W=E(_3J);if(!_3W._){return unAppCStr("[]",_3T);}else{var _3X=new T(function(){var _3Y=E(_3W.a),_3Z=new T(function(){var _40=new T(function(){var _41=function(_42){var _43=E(_42);if(!_43._){return E(new T2(1,93,_3T));}else{var _44=new T(function(){var _45=E(_43.a),_46=new T(function(){return B(A3(_25,_1M,new T2(1,function(_47){return _3D(_45.a,_47);},new T2(1,function(_48){return _3m(_45.b,_48);},__Z)),new T2(1,41,new T(function(){return _41(_43.b);}))));});return new T2(1,40,_46);});return new T2(1,44,_44);}};return _41(_3W.b);});return B(A3(_25,_1M,new T2(1,function(_49){return _3D(_3Y.a,_49);},new T2(1,function(_4a){return _3m(_3Y.b,_4a);},__Z)),new T2(1,41,_40)));});return new T2(1,40,_3Z);});return new T2(1,91,_3X);}},1);return _0(_2c,_3S);},1);return _0(_1G,_3R);});return _1V(0,E(_3I),_3Q);},1);return _0(_2d,_3P);},1);return _0(_2e,_3O);};if(_3H<11){return _3M(_3L);}else{return new T2(1,40,new T(function(){return _3M(new T2(1,41,_3L));}));}},_4b=function(_4c,_4d){var _4e=E(_4c);return _3G(0,_4e.a,_4e.b,_4e.c,_4d);},_4f=function(_4g,_4h){return _3p(_4b,_4g,_4h);},_4i=function(_4j){return _3p(_4f,_4j,__Z);},_4k=function(_4l,_4m){return _3p(_4f,_4l,_4m);},_4n=function(_4o,_4p){return _3p(_4k,_4o,_4p);},_4q=function(_4r,_4g,_4h){return _4k(_4g,_4h);},_4s=function(_4t){return _3p(_3A,_4t,__Z);},_4u=function(_4v,_4w){return _3p(_3D,_4v,_4w);},_4x=function(_4y,_4z,_4A){return _3D(_4z,_4A);},_4B=function(_4C,_4D){while(1){var _4E=(function(_4F,_4G){var _4H=E(_4G);if(!_4H._){_4C=new T2(1,new T2(0,_4H.b,_4H.c),new T(function(){return _4B(_4F,_4H.e);}));_4D=_4H.d;return __continue;}else{return E(_4F);}})(_4C,_4D);if(_4E!=__continue){return _4E;}}},_4I=new T(function(){return unCStr("fromList ");}),_4J=function(_4K){return E(E(_4K).a);},_4L=function(_4M,_4N,_4O,_4P){var _4Q=new T(function(){return _4B(__Z,_4P);}),_4R=function(_4S,_4T){var _4U=E(_4S),_4V=new T(function(){return B(A3(_25,_1M,new T2(1,new T(function(){return B(A3(_4J,_4M,0,_4U.a));}),new T2(1,new T(function(){return B(A3(_4J,_4N,0,_4U.b));}),__Z)),new T2(1,41,_4T)));});return new T2(1,40,_4V);};if(_4O<=10){var _4W=function(_4X){return _0(_4I,new T(function(){return _3p(_4R,_4Q,_4X);},1));};return _4W;}else{var _4Y=function(_4Z){var _50=new T(function(){return _0(_4I,new T(function(){return _3p(_4R,_4Q,new T2(1,41,_4Z));},1));});return new T2(1,40,_50);};return _4Y;}},_51=function(_52,_53){var _54=new T(function(){return _4L(new T3(0,_4x,_4s,_4u),new T3(0,_4q,_4i,_4n),11,_53);});if(_52<11){var _55=function(_56){return _0(_1Q,new T(function(){return B(A1(_54,_56));},1));};return _55;}else{var _57=function(_58){var _59=new T(function(){return _0(_1Q,new T(function(){return B(A1(_54,new T2(1,41,_58)));},1));});return new T2(1,40,_59);};return _57;}},_5a=new T(function(){return unCStr("smenu = ");}),_5b=new T(function(){return unCStr("slin = ");}),_5c=new T(function(){return unCStr("stree = ");}),_5d=new T(function(){return unCStr("sgrammar = ");}),_5e=new T(function(){return unCStr("ST {");}),_5f=function(_5g,_5h,_5i,_5j,_5k){var _5l=new T(function(){return _51(0,E(_5k).a);}),_5m=function(_5n){var _5o=new T(function(){var _5p=new T(function(){var _5q=new T(function(){var _5r=new T(function(){var _5s=new T(function(){var _5t=new T(function(){var _5u=new T(function(){var _5v=new T(function(){var _5w=new T(function(){var _5x=new T(function(){var _5y=new T(function(){return B(A1(_5l,new T(function(){return _0(_1F,_5n);})));},1);return _0(_5a,_5y);},1);return _0(_1G,_5x);}),_5z=E(_5j);if(!_5z._){return unAppCStr("[]",_5w);}else{var _5A=new T(function(){var _5B=E(_5z.a),_5C=new T(function(){var _5D=new T(function(){var _5E=function(_5F){var _5G=E(_5F);if(!_5G._){return E(new T2(1,93,_5w));}else{var _5H=new T(function(){var _5I=E(_5G.a),_5J=new T(function(){return B(A3(_25,_1M,new T2(1,function(_5K){return _3D(_5I.a,_5K);},new T2(1,function(_5L){return _3m(_5I.b,_5L);},__Z)),new T2(1,41,new T(function(){return _5E(_5G.b);}))));});return new T2(1,40,_5J);});return new T2(1,44,_5H);}};return _5E(_5z.b);});return B(A3(_25,_1M,new T2(1,function(_5M){return _3D(_5B.a,_5M);},new T2(1,function(_5N){return _3m(_5B.b,_5N);},__Z)),new T2(1,41,_5D)));});return new T2(1,40,_5C);});return new T2(1,91,_5A);}},1);return _0(_5b,_5v);},1);return _0(_1G,_5u);});return _3g(_5i,new T2(1,34,_5t));});return _0(_5c,new T2(1,34,_5s));},1);return _0(_1G,_5r);});return _3g(_5h,new T2(1,34,_5q));});return _0(_5d,new T2(1,34,_5p));},1);return _0(_5e,_5o);};if(_5g<11){return _5m;}else{var _5O=function(_5P){return new T2(1,40,new T(function(){return _5m(new T2(1,41,_5P));}));};return _5O;}},_5Q=new T(function(){return unCStr("True");}),_5R=new T(function(){return unCStr("False");}),_5S=function(_5T,_5U,_5V,_5W,_5X){var _5Y=new T(function(){var _5Z=E(_5W);return _5f(0,_5Z.a,_5Z.b,_5Z.c,_5Z.d);}),_60=new T(function(){var _61=E(_5X);return _5f(0,_61.a,_61.b,_61.c,_61.d);}),_62=function(_63){var _64=new T(function(){var _65=new T(function(){var _66=new T(function(){var _67=new T(function(){var _68=new T(function(){var _69=new T(function(){var _6a=new T(function(){var _6b=new T(function(){return B(A1(_60,new T(function(){return _0(_1F,_63);})));},1);return _0(_1J,_6b);},1);return _0(_1G,_6a);});return B(A1(_5Y,_69));},1);return _0(_1K,_68);},1);return _0(_1G,_67);});return _1V(0,E(_5V),_66);},1);return _0(_1L,_65);},1);return _0(_1G,_64);},_6c=function(_6d){var _6e=new T(function(){if(!E(_5U)){return _0(_5R,new T(function(){return _62(_6d);},1));}else{return _0(_5Q,new T(function(){return _62(_6d);},1));}},1);return _0(_1I,_6e);};if(_5T<11){var _6f=function(_6g){return _0(_1H,new T(function(){return _6c(_6g);},1));};return _6f;}else{var _6h=function(_6i){var _6j=new T(function(){return _0(_1H,new T(function(){return _6c(new T2(1,41,_6i));},1));});return new T2(1,40,_6j);};return _6h;}},_6k=function(_6l){return E(E(_6l).a);},_6m=function(_6n,_6o){var _6p=strEq(E(_6n),E(_6o));return (E(_6p)==0)?false:true;},_6q=new T(function(){return new T2(0,function(_6r,_6s){return _6m(_6r,_6s);},function(_6t,_6u){return (!B(A3(_6k,_6q,_6t,_6u)))?true:false;});}),_6v=function(_6w,_6x){if(_6w<=_6x){var _6y=function(_6z){return new T2(1,_6z,new T(function(){if(_6z!=_6x){return _6y(_6z+1|0);}else{return __Z;}}));};return _6y(_6w);}else{return __Z;}},_6A=function(_6B,_6C,_6D){if(_6D<=_6C){var _6E=new T(function(){var _6F=_6C-_6B|0,_6G=function(_6H){return (_6H>=(_6D-_6F|0))?new T2(1,_6H,new T(function(){return _6G(_6H+_6F|0);})):new T2(1,_6H,__Z);};return _6G(_6C);});return new T2(1,_6B,_6E);}else{return (_6D<=_6B)?new T2(1,_6B,__Z):__Z;}},_6I=function(_6J,_6K,_6L){if(_6L>=_6K){var _6M=new T(function(){var _6N=_6K-_6J|0,_6O=function(_6P){return (_6P<=(_6L-_6N|0))?new T2(1,_6P,new T(function(){return _6O(_6P+_6N|0);})):new T2(1,_6P,__Z);};return _6O(_6K);});return new T2(1,_6J,_6M);}else{return (_6L>=_6J)?new T2(1,_6J,__Z):__Z;}},_6Q=function(_6R,_6S){if(_6S<_6R){return _6A(_6R,_6S,-2147483648);}else{return _6I(_6R,_6S,2147483647);}},_6T=function(_6U,_6V,_6W){if(_6V<_6U){return _6A(_6U,_6V,_6W);}else{return _6I(_6U,_6V,_6W);}},_6X=function(_6Y){return E(_6Y);},_6Z=new T(function(){return err(new T(function(){return unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound");}));}),_70=new T(function(){return err(new T(function(){return unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound");}));}),_71=function(_72,_73){if(_72<=0){if(_72>=0){return quot(_72,_73);}else{if(_73<=0){return quot(_72,_73);}else{return quot(_72+1|0,_73)-1|0;}}}else{if(_73>=0){if(_72>=0){return quot(_72,_73);}else{if(_73<=0){return quot(_72,_73);}else{return quot(_72+1|0,_73)-1|0;}}}else{return quot(_72-1|0,_73)-1|0;}}},_74=new T(function(){return unCStr("base");}),_75=new T(function(){return unCStr("GHC.Exception");}),_76=new T(function(){return unCStr("ArithException");}),_77=function(_78){return E(new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_74,_75,_76),__Z,__Z));},_79=function(_7a){return E(E(_7a).a);},_7b=function(_7c,_7d,_7e){var _7f=B(A1(_7c,_)),_7g=B(A1(_7d,_)),_7h=hs_eqWord64(_7f.a,_7g.a);if(!_7h){return __Z;}else{var _7i=hs_eqWord64(_7f.b,_7g.b);return (!_7i)?__Z:new T1(1,_7e);}},_7j=new T(function(){return unCStr("Ratio has zero denominator");}),_7k=new T(function(){return unCStr("denormal");}),_7l=new T(function(){return unCStr("divide by zero");}),_7m=new T(function(){return unCStr("loss of precision");}),_7n=new T(function(){return unCStr("arithmetic underflow");}),_7o=new T(function(){return unCStr("arithmetic overflow");}),_7p=function(_7q,_7r){switch(E(_7q)){case 0:return _0(_7o,_7r);case 1:return _0(_7n,_7r);case 2:return _0(_7m,_7r);case 3:return _0(_7l,_7r);case 4:return _0(_7k,_7r);default:return _0(_7j,_7r);}},_7s=function(_7t){return _7p(_7t,__Z);},_7u=new T(function(){return new T5(0,_77,new T3(0,function(_7v,_7w,_7x){return _7p(_7w,_7x);},_7s,function(_7y,_7z){return _3p(_7p,_7y,_7z);}),_7A,function(_7B){var _7C=E(_7B);return _7b(_79(_7C.a),_77,_7C.b);},_7s);}),_7A=function(_7D){return new T2(0,_7u,_7D);},_7E=new T(function(){return die(new T(function(){return _7A(3);}));}),_7F=new T(function(){return die(new T(function(){return _7A(0);}));}),_7G=function(_7H,_7I){var _7J=E(_7I);switch(_7J){case -1:var _7K=E(_7H);if(_7K==(-2147483648)){return E(_7F);}else{return _71(_7K,-1);}break;case 0:return E(_7E);default:return _71(_7H,_7J);}},_7L=new T2(0,_7F,0),_7M=function(_7N,_7O){var _7P=_7N%_7O;if(_7N<=0){if(_7N>=0){return _7P;}else{if(_7O<=0){return _7P;}else{return (_7P==0)?0:_7P+_7O|0;}}}else{if(_7O>=0){if(_7N>=0){return _7P;}else{if(_7O<=0){return _7P;}else{return (_7P==0)?0:_7P+_7O|0;}}}else{return (_7P==0)?0:_7P+_7O|0;}}},_7Q=function(_7R){return new T1(0,_7R);},_7S=new T1(0,1),_7T=function(_7U){var _7V=E(_7U);if(!_7V._){return E(_7V.a);}else{return I_toInt(_7V.a);}},_7W=new T2(0,function(_7X,_7Y){return E(_7X)==E(_7Y);},function(_7Z,_80){return E(_7Z)!=E(_80);}),_81=function(_82,_83){return (_82>=_83)?(_82!=_83)?2:1:0;},_84={_:0,a:new T3(0,{_:0,a:function(_85,_86){return E(_85)+E(_86)|0;},b:function(_87,_88){return E(_87)-E(_88)|0;},c:function(_89,_8a){return imul(E(_89),E(_8a))|0;},d:function(_8b){return  -E(_8b);},e:function(_8c){var _8d=E(_8c);return (_8d<0)? -_8d:_8d;},f:function(_8e){var _8f=E(_8e);return (_8f>=0)?(_8f==0)?0:1:-1;},g:function(_8g){return _7T(_8g);}},{_:0,a:_7W,b:function(_8h,_8i){return _81(E(_8h),E(_8i));},c:function(_8j,_8k){return E(_8j)<E(_8k);},d:function(_8l,_8m){return E(_8l)<=E(_8m);},e:function(_8n,_8o){return E(_8n)>E(_8o);},f:function(_8p,_8q){return E(_8p)>=E(_8q);},g:function(_8r,_8s){var _8t=E(_8r),_8u=E(_8s);return (_8t>_8u)?_8t:_8u;},h:function(_8v,_8w){var _8x=E(_8v),_8y=E(_8w);return (_8x>_8y)?_8y:_8x;}},function(_8z){return new T2(0,E(_7Q(E(_8z))),E(_7S));}),b:{_:0,a:function(_8A){var _8B=E(_8A);return (_8B==2147483647)?E(_70):_8B+1|0;},b:function(_8C){var _8D=E(_8C);return (_8D==(-2147483648))?E(_6Z):_8D-1|0;},c:_6X,d:_6X,e:function(_8E){return _6v(E(_8E),2147483647);},f:function(_8F,_8G){return _6Q(E(_8F),E(_8G));},g:function(_8H,_8I){return _6v(E(_8H),E(_8I));},h:function(_8J,_8K,_8L){return _6T(E(_8J),E(_8K),E(_8L));}},c:function(_8M,_8N){var _8O=E(_8M),_8P=E(_8N);switch(_8P){case -1:if(_8O==(-2147483648)){return E(_7F);}else{return quot(_8O,-1);}break;case 0:return E(_7E);default:return quot(_8O,_8P);}},d:function(_8Q,_8R){var _8S=E(_8R);switch(_8S){case -1:return 0;case 0:return E(_7E);default:return E(_8Q)%_8S;}},e:function(_8T,_8U){return _7G(E(_8T),E(_8U));},f:function(_8V,_8W){var _8X=E(_8W);switch(_8X){case -1:return 0;case 0:return E(_7E);default:return _7M(E(_8V),_8X);}},g:function(_8Y,_8Z){var _90=E(_8Y),_91=E(_8Z);switch(_91){case -1:if(_90==(-2147483648)){return E(_7L);}else{var _92=quotRemI(_90,-1);return new T2(0,_92.a,_92.b);}break;case 0:return E(_7E);default:var _93=quotRemI(_90,_91);return new T2(0,_93.a,_93.b);}},h:function(_94,_95){var _96=E(_94),_97=E(_95);switch(_97){case -1:if(_96==(-2147483648)){return E(_7L);}else{if(_96<=0){if(_96>=0){var _98=quotRemI(_96,-1);return new T2(0,_98.a,_98.b);}else{var _99=quotRemI(_96,-1);return new T2(0,_99.a,_99.b);}}else{var _9a=quotRemI(_96-1|0,-1);return new T2(0,_9a.a-1|0,(_9a.b+(-1)|0)+1|0);}}break;case 0:return E(_7E);default:if(_96<=0){if(_96>=0){var _9b=quotRemI(_96,_97);return new T2(0,_9b.a,_9b.b);}else{if(_97<=0){var _9c=quotRemI(_96,_97);return new T2(0,_9c.a,_9c.b);}else{var _9d=quotRemI(_96+1|0,_97);return new T2(0,_9d.a-1|0,(_9d.b+_97|0)-1|0);}}}else{if(_97>=0){if(_96>=0){var _9e=quotRemI(_96,_97);return new T2(0,_9e.a,_9e.b);}else{if(_97<=0){var _9f=quotRemI(_96,_97);return new T2(0,_9f.a,_9f.b);}else{var _9g=quotRemI(_96+1|0,_97);return new T2(0,_9g.a-1|0,(_9g.b+_97|0)-1|0);}}}else{var _9h=quotRemI(_96-1|0,_97);return new T2(0,_9h.a-1|0,(_9h.b+_97|0)+1|0);}}}},i:function(_9i){return _7Q(E(_9i));}},_9j=new T1(0,2),_9k=function(_9l){return E(E(_9l).a);},_9m=function(_9n){return E(E(_9n).a);},_9o=function(_9p,_9q){while(1){var _9r=E(_9p);if(!_9r._){var _9s=_9r.a,_9t=E(_9q);if(!_9t._){var _9u=_9t.a;if(!(imul(_9s,_9u)|0)){return new T1(0,imul(_9s,_9u)|0);}else{_9p=new T1(1,I_fromInt(_9s));_9q=new T1(1,I_fromInt(_9u));continue;}}else{_9p=new T1(1,I_fromInt(_9s));_9q=_9t;continue;}}else{var _9v=E(_9q);if(!_9v._){_9p=_9r;_9q=new T1(1,I_fromInt(_9v.a));continue;}else{return new T1(1,I_mul(_9r.a,_9v.a));}}}},_9w=function(_9x,_9y,_9z){while(1){if(!(_9y%2)){var _9A=_9o(_9x,_9x),_9B=quot(_9y,2);_9x=_9A;_9y=_9B;continue;}else{var _9C=E(_9y);if(_9C==1){return _9o(_9x,_9z);}else{var _9A=_9o(_9x,_9x),_9D=_9o(_9x,_9z);_9x=_9A;_9y=quot(_9C-1|0,2);_9z=_9D;continue;}}}},_9E=function(_9F,_9G){while(1){if(!(_9G%2)){var _9H=_9o(_9F,_9F),_9I=quot(_9G,2);_9F=_9H;_9G=_9I;continue;}else{var _9J=E(_9G);if(_9J==1){return E(_9F);}else{return _9w(_9o(_9F,_9F),quot(_9J-1|0,2),_9F);}}}},_9K=function(_9L){return E(E(_9L).c);},_9M=function(_9N){return E(E(_9N).a);},_9O=function(_9P){return E(E(_9P).b);},_9Q=function(_9R){return E(E(_9R).b);},_9S=function(_9T){return E(E(_9T).c);},_9U=new T1(0,0),_9V=new T1(0,2),_9W=function(_9X){return E(E(_9X).g);},_9Y=function(_9Z){return E(E(_9Z).d);},_a0=function(_a1,_a2){var _a3=_9k(_a1),_a4=new T(function(){return _9m(_a3);}),_a5=new T(function(){return B(A3(_9Y,_a1,_a2,new T(function(){return B(A2(_9W,_a4,_9V));})));});return C > 19 ? new F(function(){return A3(_6k,_9M(_9O(_a3)),_a5,new T(function(){return B(A2(_9W,_a4,_9U));}));}) : (++C,A3(_6k,_9M(_9O(_a3)),_a5,new T(function(){return B(A2(_9W,_a4,_9U));})));},_a6=new T(function(){return unCStr("Negative exponent");}),_a7=new T(function(){return err(_a6);}),_a8=function(_a9){return E(E(_a9).c);},_aa=function(_ab,_ac,_ad,_ae){var _af=_9k(_ac),_ag=new T(function(){return _9m(_af);}),_ah=_9O(_af);if(!B(A3(_9S,_ah,_ae,new T(function(){return B(A2(_9W,_ag,_9U));})))){if(!B(A3(_6k,_9M(_ah),_ae,new T(function(){return B(A2(_9W,_ag,_9U));})))){var _ai=new T(function(){return B(A2(_9W,_ag,_9V));}),_aj=new T(function(){return B(A2(_9W,_ag,_7S));}),_ak=_9M(_ah),_al=function(_am,_an,_ao){while(1){var _ap=B((function(_aq,_ar,_as){if(!B(_a0(_ac,_ar))){if(!B(A3(_6k,_ak,_ar,_aj))){var _at=new T(function(){return B(A3(_a8,_ac,new T(function(){return B(A3(_9Q,_ag,_ar,_aj));}),_ai));});_am=new T(function(){return B(A3(_9K,_ab,_aq,_aq));});_an=_at;_ao=new T(function(){return B(A3(_9K,_ab,_aq,_as));});return __continue;}else{return C > 19 ? new F(function(){return A3(_9K,_ab,_aq,_as);}) : (++C,A3(_9K,_ab,_aq,_as));}}else{var _au=_as;_am=new T(function(){return B(A3(_9K,_ab,_aq,_aq));});_an=new T(function(){return B(A3(_a8,_ac,_ar,_ai));});_ao=_au;return __continue;}})(_am,_an,_ao));if(_ap!=__continue){return _ap;}}},_av=function(_aw,_ax){while(1){var _ay=(function(_az,_aA){if(!B(_a0(_ac,_aA))){if(!B(A3(_6k,_ak,_aA,_aj))){var _aB=new T(function(){return B(A3(_a8,_ac,new T(function(){return B(A3(_9Q,_ag,_aA,_aj));}),_ai));});return _al(new T(function(){return B(A3(_9K,_ab,_az,_az));}),_aB,_az);}else{return E(_az);}}else{_aw=new T(function(){return B(A3(_9K,_ab,_az,_az));});_ax=new T(function(){return B(A3(_a8,_ac,_aA,_ai));});return __continue;}})(_aw,_ax);if(_ay!=__continue){return _ay;}}};return _av(_ad,_ae);}else{return C > 19 ? new F(function(){return A2(_9W,_ab,_7S);}) : (++C,A2(_9W,_ab,_7S));}}else{return E(_a7);}},_aC=new T(function(){return err(_a6);}),_aD=function(_aE){var _aF=I_decodeDouble(_aE);return new T2(0,new T1(1,_aF.b),_aF.a);},_aG=function(_aH,_aI){var _aJ=E(_aH);return (_aJ._==0)?_aJ.a*Math.pow(2,_aI):I_toNumber(_aJ.a)*Math.pow(2,_aI);},_aK=function(_aL,_aM){var _aN=E(_aL);if(!_aN._){var _aO=_aN.a,_aP=E(_aM);return (_aP._==0)?_aO==_aP.a:(I_compareInt(_aP.a,_aO)==0)?true:false;}else{var _aQ=_aN.a,_aR=E(_aM);return (_aR._==0)?(I_compareInt(_aQ,_aR.a)==0)?true:false:(I_compare(_aQ,_aR.a)==0)?true:false;}},_aS=function(_aT,_aU){while(1){var _aV=E(_aT);if(!_aV._){var _aW=E(_aV.a);if(_aW==(-2147483648)){_aT=new T1(1,I_fromInt(-2147483648));continue;}else{var _aX=E(_aU);if(!_aX._){var _aY=_aX.a;return new T2(0,new T1(0,quot(_aW,_aY)),new T1(0,_aW%_aY));}else{_aT=new T1(1,I_fromInt(_aW));_aU=_aX;continue;}}}else{var _aZ=E(_aU);if(!_aZ._){_aT=_aV;_aU=new T1(1,I_fromInt(_aZ.a));continue;}else{var _b0=I_quotRem(_aV.a,_aZ.a);return new T2(0,new T1(1,_b0.a),new T1(1,_b0.b));}}}},_b1=function(_b2,_b3){var _b4=_aD(_b3),_b5=_b4.a,_b6=_b4.b,_b7=new T(function(){return _9m(new T(function(){return _9k(_b2);}));});if(_b6<0){var _b8= -_b6;if(_b8>=0){if(!_b8){var _b9=E(_7S);}else{var _b9=_9E(_9j,_b8);}if(!_aK(_b9,new T1(0,0))){var _ba=_aS(_b5,_b9);return new T2(0,new T(function(){return B(A2(_9W,_b7,_ba.a));}),new T(function(){return _aG(_ba.b,_b6);}));}else{return E(_7E);}}else{return E(_aC);}}else{var _bb=new T(function(){var _bc=new T(function(){return B(_aa(_b7,_84,new T(function(){return B(A2(_9W,_b7,_9j));}),_b6));});return B(A3(_9K,_b7,new T(function(){return B(A2(_9W,_b7,_b5));}),_bc));});return new T2(0,_bb,0);}},_bd=function(_){return 0;},_be=(function(x){console.log(x);}),_bf=function(_){var _bg=_be("Error decoding message data");return _bd(_);},_bh=function(_bi,_bj){while(1){var _bk=E(_bi);if(!_bk._){return (E(_bj)._==0)?1:0;}else{var _bl=E(_bj);if(!_bl._){return 2;}else{var _bm=E(_bk.a),_bn=E(_bl.a);if(_bm>=_bn){if(_bm!=_bn){return 2;}else{_bi=_bk.b;_bj=_bl.b;continue;}}else{return 0;}}}}},_bo=new T0(1),_bp=new T(function(){return unCStr("Failure in Data.Map.balanceL");}),_bq=new T(function(){var _br=_;return err(_bp);}),_bs=function(_bt,_bu,_bv,_bw){var _bx=E(_bw);if(!_bx._){var _by=_bx.a,_bz=E(_bv);if(!_bz._){var _bA=_bz.a,_bB=_bz.b,_bC=_bz.c;if(_bA<=(imul(3,_by)|0)){return new T5(0,(1+_bA|0)+_by|0,E(_bt),_bu,_bz,_bx);}else{var _bD=E(_bz.d);if(!_bD._){var _bE=_bD.a,_bF=E(_bz.e);if(!_bF._){var _bG=_bF.a,_bH=_bF.b,_bI=_bF.c,_bJ=_bF.d;if(_bG>=(imul(2,_bE)|0)){var _bK=function(_bL){var _bM=E(_bF.e);return (_bM._==0)?new T5(0,(1+_bA|0)+_by|0,E(_bH),_bI,E(new T5(0,(1+_bE|0)+_bL|0,E(_bB),_bC,_bD,E(_bJ))),E(new T5(0,(1+_by|0)+_bM.a|0,E(_bt),_bu,_bM,_bx))):new T5(0,(1+_bA|0)+_by|0,E(_bH),_bI,E(new T5(0,(1+_bE|0)+_bL|0,E(_bB),_bC,_bD,E(_bJ))),E(new T5(0,1+_by|0,E(_bt),_bu,E(_bo),_bx)));},_bN=E(_bJ);if(!_bN._){return _bK(_bN.a);}else{return _bK(0);}}else{return new T5(0,(1+_bA|0)+_by|0,E(_bB),_bC,_bD,E(new T5(0,(1+_by|0)+_bG|0,E(_bt),_bu,_bF,_bx)));}}else{return E(_bq);}}else{return E(_bq);}}}else{return new T5(0,1+_by|0,E(_bt),_bu,E(_bo),_bx);}}else{var _bO=E(_bv);if(!_bO._){var _bP=_bO.a,_bQ=_bO.b,_bR=_bO.c,_bS=_bO.e,_bT=E(_bO.d);if(!_bT._){var _bU=_bT.a,_bV=E(_bS);if(!_bV._){var _bW=_bV.a,_bX=_bV.b,_bY=_bV.c,_bZ=_bV.d;if(_bW>=(imul(2,_bU)|0)){var _c0=function(_c1){var _c2=E(_bV.e);return (_c2._==0)?new T5(0,1+_bP|0,E(_bX),_bY,E(new T5(0,(1+_bU|0)+_c1|0,E(_bQ),_bR,_bT,E(_bZ))),E(new T5(0,1+_c2.a|0,E(_bt),_bu,_c2,E(_bo)))):new T5(0,1+_bP|0,E(_bX),_bY,E(new T5(0,(1+_bU|0)+_c1|0,E(_bQ),_bR,_bT,E(_bZ))),E(new T5(0,1,E(_bt),_bu,E(_bo),E(_bo))));},_c3=E(_bZ);if(!_c3._){return _c0(_c3.a);}else{return _c0(0);}}else{return new T5(0,1+_bP|0,E(_bQ),_bR,_bT,E(new T5(0,1+_bW|0,E(_bt),_bu,_bV,E(_bo))));}}else{return new T5(0,3,E(_bQ),_bR,_bT,E(new T5(0,1,E(_bt),_bu,E(_bo),E(_bo))));}}else{var _c4=E(_bS);return (_c4._==0)?new T5(0,3,E(_c4.b),_c4.c,E(new T5(0,1,E(_bQ),_bR,E(_bo),E(_bo))),E(new T5(0,1,E(_bt),_bu,E(_bo),E(_bo)))):new T5(0,2,E(_bt),_bu,_bO,E(_bo));}}else{return new T5(0,1,E(_bt),_bu,E(_bo),E(_bo));}}},_c5=new T(function(){return unCStr("Failure in Data.Map.balanceR");}),_c6=new T(function(){var _c7=_;return err(_c5);}),_c8=function(_c9,_ca,_cb,_cc){var _cd=E(_cb);if(!_cd._){var _ce=_cd.a,_cf=E(_cc);if(!_cf._){var _cg=_cf.a,_ch=_cf.b,_ci=_cf.c;if(_cg<=(imul(3,_ce)|0)){return new T5(0,(1+_ce|0)+_cg|0,E(_c9),_ca,_cd,_cf);}else{var _cj=E(_cf.d);if(!_cj._){var _ck=_cj.a,_cl=_cj.b,_cm=_cj.c,_cn=_cj.d,_co=E(_cf.e);if(!_co._){var _cp=_co.a;if(_ck>=(imul(2,_cp)|0)){var _cq=function(_cr){var _cs=E(_c9),_ct=E(_cj.e);return (_ct._==0)?new T5(0,(1+_ce|0)+_cg|0,E(_cl),_cm,E(new T5(0,(1+_ce|0)+_cr|0,_cs,_ca,_cd,E(_cn))),E(new T5(0,(1+_cp|0)+_ct.a|0,E(_ch),_ci,_ct,_co))):new T5(0,(1+_ce|0)+_cg|0,E(_cl),_cm,E(new T5(0,(1+_ce|0)+_cr|0,_cs,_ca,_cd,E(_cn))),E(new T5(0,1+_cp|0,E(_ch),_ci,E(_bo),_co)));},_cu=E(_cn);if(!_cu._){return _cq(_cu.a);}else{return _cq(0);}}else{return new T5(0,(1+_ce|0)+_cg|0,E(_ch),_ci,E(new T5(0,(1+_ce|0)+_ck|0,E(_c9),_ca,_cd,_cj)),_co);}}else{return E(_c6);}}else{return E(_c6);}}}else{return new T5(0,1+_ce|0,E(_c9),_ca,_cd,E(_bo));}}else{var _cv=E(_cc);if(!_cv._){var _cw=_cv.a,_cx=_cv.b,_cy=_cv.c,_cz=_cv.e,_cA=E(_cv.d);if(!_cA._){var _cB=_cA.a,_cC=_cA.b,_cD=_cA.c,_cE=_cA.d,_cF=E(_cz);if(!_cF._){var _cG=_cF.a;if(_cB>=(imul(2,_cG)|0)){var _cH=function(_cI){var _cJ=E(_c9),_cK=E(_cA.e);return (_cK._==0)?new T5(0,1+_cw|0,E(_cC),_cD,E(new T5(0,1+_cI|0,_cJ,_ca,E(_bo),E(_cE))),E(new T5(0,(1+_cG|0)+_cK.a|0,E(_cx),_cy,_cK,_cF))):new T5(0,1+_cw|0,E(_cC),_cD,E(new T5(0,1+_cI|0,_cJ,_ca,E(_bo),E(_cE))),E(new T5(0,1+_cG|0,E(_cx),_cy,E(_bo),_cF)));},_cL=E(_cE);if(!_cL._){return _cH(_cL.a);}else{return _cH(0);}}else{return new T5(0,1+_cw|0,E(_cx),_cy,E(new T5(0,1+_cB|0,E(_c9),_ca,E(_bo),_cA)),_cF);}}else{return new T5(0,3,E(_cC),_cD,E(new T5(0,1,E(_c9),_ca,E(_bo),E(_bo))),E(new T5(0,1,E(_cx),_cy,E(_bo),E(_bo))));}}else{var _cM=E(_cz);return (_cM._==0)?new T5(0,3,E(_cx),_cy,E(new T5(0,1,E(_c9),_ca,E(_bo),E(_bo))),_cM):new T5(0,2,E(_c9),_ca,E(_bo),_cv);}}else{return new T5(0,1,E(_c9),_ca,E(_bo),E(_bo));}}},_cN=function(_cO,_cP,_cQ){var _cR=E(_cO),_cS=E(_cP),_cT=E(_cQ);if(!_cT._){var _cU=_cT.b,_cV=_cT.c,_cW=_cT.d,_cX=_cT.e;switch(_bh(_cR,_cU)){case 0:return _bs(_cU,_cV,_cN(_cR,_cS,_cW),_cX);case 1:return new T5(0,_cT.a,_cR,_cS,E(_cW),E(_cX));default:return _c8(_cU,_cV,_cW,_cN(_cR,_cS,_cX));}}else{return new T5(0,1,_cR,_cS,E(_bo),E(_bo));}},_cY=function(_cZ,_d0){while(1){var _d1=E(_d0);if(!_d1._){return E(_cZ);}else{var _d2=E(_d1.a),_d3=_cN(_d2.a,_d2.b,_cZ);_cZ=_d3;_d0=_d1.b;continue;}}},_d4=function(_d5,_d6){return new T5(0,1,E(_d5),_d6,E(_bo),E(_bo));},_d7=function(_d8,_d9,_da){var _db=E(_da);if(!_db._){return _c8(_db.b,_db.c,_db.d,_d7(_d8,_d9,_db.e));}else{return _d4(_d8,_d9);}},_dc=function(_dd,_de,_df){var _dg=E(_df);if(!_dg._){return _bs(_dg.b,_dg.c,_dc(_dd,_de,_dg.d),_dg.e);}else{return _d4(_dd,_de);}},_dh=function(_di,_dj,_dk,_dl,_dm,_dn,_do){return _bs(_dl,_dm,_dc(_di,_dj,_dn),_do);},_dp=function(_dq,_dr,_ds,_dt,_du,_dv,_dw,_dx){var _dy=E(_ds);if(!_dy._){var _dz=_dy.a,_dA=_dy.b,_dB=_dy.c,_dC=_dy.d,_dD=_dy.e;if((imul(3,_dz)|0)>=_dt){if((imul(3,_dt)|0)>=_dz){return new T5(0,(_dz+_dt|0)+1|0,E(_dq),_dr,_dy,E(new T5(0,_dt,E(_du),_dv,E(_dw),E(_dx))));}else{return _c8(_dA,_dB,_dC,B(_dp(_dq,_dr,_dD,_dt,_du,_dv,_dw,_dx)));}}else{return _bs(_du,_dv,B(_dE(_dq,_dr,_dz,_dA,_dB,_dC,_dD,_dw)),_dx);}}else{return _dh(_dq,_dr,_dt,_du,_dv,_dw,_dx);}},_dE=function(_dF,_dG,_dH,_dI,_dJ,_dK,_dL,_dM){var _dN=E(_dM);if(!_dN._){var _dO=_dN.a,_dP=_dN.b,_dQ=_dN.c,_dR=_dN.d,_dS=_dN.e;if((imul(3,_dH)|0)>=_dO){if((imul(3,_dO)|0)>=_dH){return new T5(0,(_dH+_dO|0)+1|0,E(_dF),_dG,E(new T5(0,_dH,E(_dI),_dJ,E(_dK),E(_dL))),_dN);}else{return _c8(_dI,_dJ,_dK,B(_dp(_dF,_dG,_dL,_dO,_dP,_dQ,_dR,_dS)));}}else{return _bs(_dP,_dQ,B(_dE(_dF,_dG,_dH,_dI,_dJ,_dK,_dL,_dR)),_dS);}}else{return _d7(_dF,_dG,new T5(0,_dH,E(_dI),_dJ,E(_dK),E(_dL)));}},_dT=function(_dU,_dV,_dW,_dX){var _dY=E(_dW);if(!_dY._){var _dZ=_dY.a,_e0=_dY.b,_e1=_dY.c,_e2=_dY.d,_e3=_dY.e,_e4=E(_dX);if(!_e4._){var _e5=_e4.a,_e6=_e4.b,_e7=_e4.c,_e8=_e4.d,_e9=_e4.e;if((imul(3,_dZ)|0)>=_e5){if((imul(3,_e5)|0)>=_dZ){return new T5(0,(_dZ+_e5|0)+1|0,E(_dU),_dV,_dY,_e4);}else{return _c8(_e0,_e1,_e2,B(_dp(_dU,_dV,_e3,_e5,_e6,_e7,_e8,_e9)));}}else{return _bs(_e6,_e7,B(_dE(_dU,_dV,_dZ,_e0,_e1,_e2,_e3,_e8)),_e9);}}else{return _d7(_dU,_dV,_dY);}}else{return _dc(_dU,_dV,_dX);}},_ea=function(_eb,_ec){var _ed=E(_ec);if(!_ed._){return new T3(0,_bo,__Z,__Z);}else{var _ee=E(_eb);if(_ee==1){var _ef=E(_ed.a),_eg=_ef.a,_eh=_ef.b,_ei=E(_ed.b);return (_ei._==0)?new T3(0,new T(function(){return new T5(0,1,E(_eg),E(_eh),E(_bo),E(_bo));}),__Z,__Z):(_bh(_eg,E(_ei.a).a)==0)?new T3(0,new T(function(){return new T5(0,1,E(_eg),E(_eh),E(_bo),E(_bo));}),_ei,__Z):new T3(0,new T(function(){return new T5(0,1,E(_eg),E(_eh),E(_bo),E(_bo));}),__Z,_ei);}else{var _ej=_ea(_ee>>1,_ed),_ek=_ej.a,_el=_ej.c,_em=E(_ej.b);if(!_em._){return new T3(0,_ek,__Z,_el);}else{var _en=E(_em.a),_eo=_en.a,_ep=_en.b,_eq=E(_em.b);if(!_eq._){return new T3(0,new T(function(){return _d7(_eo,E(_ep),_ek);}),__Z,_el);}else{if(!_bh(_eo,E(_eq.a).a)){var _er=_ea(_ee>>1,_eq);return new T3(0,new T(function(){return B(_dT(_eo,E(_ep),_ek,_er.a));}),_er.b,_er.c);}else{return new T3(0,_ek,__Z,_em);}}}}}},_es=function(_et,_eu,_ev){while(1){var _ew=E(_ev);if(!_ew._){return E(_eu);}else{var _ex=E(_ew.a),_ey=_ex.a,_ez=_ex.b,_eA=E(_ew.b);if(!_eA._){return _d7(_ey,E(_ez),_eu);}else{if(!_bh(_ey,E(_eA.a).a)){var _eB=_ea(_et,_eA),_eC=_eB.a,_eD=E(_eB.c);if(!_eD._){var _eE=_et<<1,_eF=B(_dT(_ey,E(_ez),_eu,_eC));_et=_eE;_eu=_eF;_ev=_eB.b;continue;}else{return _cY(B(_dT(_ey,E(_ez),_eu,_eC)),_eD);}}else{return _cY(_eu,_ew);}}}}},_eG=function(_eH){var _eI=E(_eH);if(!_eI._){return new T0(1);}else{var _eJ=E(_eI.a),_eK=_eJ.a,_eL=_eJ.b,_eM=E(_eI.b);if(!_eM._){return new T5(0,1,E(_eK),E(_eL),E(_bo),E(_bo));}else{if(!_bh(_eK,E(_eM.a).a)){return C > 19 ? new F(function(){return _es(1,new T5(0,1,E(_eK),E(_eL),E(_bo),E(_bo)),_eM);}) : (++C,_es(1,new T5(0,1,E(_eK),E(_eL),E(_bo),E(_bo)),_eM));}else{return _cY(new T5(0,1,E(_eK),E(_eL),E(_bo),E(_bo)),_eM);}}}},_eN=function(_eO,_){var _eP=E(_eO);if(!_eP._){return __Z;}else{var _eQ=B(A1(_eP.a,_)),_eR=_eN(_eP.b,_);return new T2(1,_eQ,_eR);}},_eS=function(_){var _eT=_be("Error decoding cost tree data");return _bd(_);},_eU=new T(function(){return err(new T(function(){return unCStr("Maybe.fromJust: Nothing");}));}),_eV=function(_eW,_eX,_eY){while(1){var _eZ=E(_eY);if(!_eZ._){return __Z;}else{var _f0=E(_eZ.a);if(!B(A3(_6k,_eW,_eX,_f0.a))){_eY=_eZ.b;continue;}else{return new T1(1,_f0.b);}}}},_f1=new T(function(){return unCStr("main");}),_f2=new T(function(){return unCStr("Ajax");}),_f3=new T(function(){return unCStr("ServerMessageException");}),_f4=function(_f5){return E(new T5(0,new Long(2796709153,857663197,true),new Long(2290229150,2001624562,true),new T5(0,new Long(2796709153,857663197,true),new Long(2290229150,2001624562,true),_f1,_f2,_f3),__Z,__Z));},_f6=new T(function(){return unCStr("SME ");}),_f7=function(_f8,_f9,_fa){if(_f8<11){return _0(_f6,new T2(1,34,new T(function(){return _3g(_f9,new T2(1,34,_fa));})));}else{var _fb=new T(function(){return _0(_f6,new T2(1,34,new T(function(){return _3g(_f9,new T2(1,34,new T2(1,41,_fa)));})));});return new T2(1,40,_fb);}},_fc=function(_fd){return _f7(0,E(_fd).a,__Z);},_fe=function(_ff,_fg){return _f7(0,E(_ff).a,_fg);},_fh=new T(function(){return new T5(0,_f4,new T3(0,function(_fi,_fj,_fk){return _f7(E(_fi),E(_fj).a,_fk);},_fc,function(_4g,_4h){return _3p(_fe,_4g,_4h);}),function(_4h){return new T2(0,_fh,_4h);},function(_fl){var _fm=E(_fl);return _7b(_79(_fm.a),_f4,_fm.b);},_fc);}),_fn=function(_fo){return E(E(_fo).c);},_fp=function(_fq,_fr){return die(new T(function(){return B(A2(_fn,_fr,_fq));}));},_fs=function(_ft,_7D){return _fp(_ft,_7D);},_fu=new T(function(){return _fs(new T1(0,new T(function(){return unCStr("Error decoding cost tree data");})),_fh);}),_fv=new T(function(){return unCStr("base");}),_fw=new T(function(){return unCStr("Control.Exception.Base");}),_fx=new T(function(){return unCStr("PatternMatchFail");}),_fy=function(_fz){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_fv,_fw,_fx),__Z,__Z));},_fA=function(_fB){return E(E(_fB).a);},_fC=function(_fD,_fE){return _0(E(_fD).a,_fE);},_fF=new T(function(){return new T5(0,_fy,new T3(0,function(_fG,_fH,_fI){return _0(E(_fH).a,_fI);},_fA,function(_fJ,_fK){return _3p(_fC,_fJ,_fK);}),function(_fL){return new T2(0,_fF,_fL);},function(_fM){var _fN=E(_fM);return _7b(_79(_fN.a),_fy,_fN.b);},_fA);}),_fO=new T(function(){return unCStr("Non-exhaustive patterns in");}),_fP=function(_fQ,_fR){var _fS=E(_fR);if(!_fS._){return new T2(0,__Z,__Z);}else{var _fT=_fS.a;if(!B(A1(_fQ,_fT))){return new T2(0,__Z,_fS);}else{var _fU=new T(function(){var _fV=_fP(_fQ,_fS.b);return new T2(0,_fV.a,_fV.b);});return new T2(0,new T2(1,_fT,new T(function(){return E(E(_fU).a);})),new T(function(){return E(E(_fU).b);}));}}},_fW=new T(function(){return unCStr("\n");}),_fX=function(_fY){return (E(_fY)==124)?false:true;},_fZ=function(_g0,_g1){var _g2=_fP(_fX,unCStr(_g0)),_g3=_g2.a,_g4=function(_g5,_g6){var _g7=new T(function(){var _g8=new T(function(){return _0(_g1,new T(function(){return _0(_g6,_fW);},1));});return unAppCStr(": ",_g8);},1);return _0(_g5,_g7);},_g9=E(_g2.b);if(!_g9._){return _g4(_g3,__Z);}else{if(E(_g9.a)==124){return _g4(_g3,new T2(1,32,_g9.b));}else{return _g4(_g3,__Z);}}},_ga=function(_gb){return _fs(new T1(0,new T(function(){return _fZ(_gb,_fO);})),_fF);},_gc=function(_gd){return C > 19 ? new F(function(){return _ga("Ajax.hs:94:21-91|lambda");}) : (++C,_ga("Ajax.hs:94:21-91|lambda"));},_ge=function(_gf){var _gg=E(_gf);if(!_gg._){var _gh=_gg.a,_gi=_gh&4294967295;return (_gh>=_gi)?_gi:_gi-1|0;}else{return C > 19 ? new F(function(){return _ga("Ajax.hs:94:56-74|lambda");}) : (++C,_ga("Ajax.hs:94:56-74|lambda"));}},_gj=function(_gk){return C > 19 ? new F(function(){return _ge(_gk);}) : (++C,_ge(_gk));},_gl=function(_gm,_gn){var _go=E(_gn);return (_go._==0)?__Z:new T2(1,new T(function(){return B(A1(_gm,_go.a));}),new T(function(){return _gl(_gm,_go.b);}));},_gp=function(_gq){var _gr=E(_gq);if(_gr._==3){var _gs=E(_gr.a);if(!_gs._){return C > 19 ? new F(function(){return _gc(_);}) : (++C,_gc(_));}else{var _gt=E(_gs.a);if(_gt._==3){var _gu=E(_gs.b);if(!_gu._){return C > 19 ? new F(function(){return _gc(_);}) : (++C,_gc(_));}else{var _gv=E(_gu.a);if(_gv._==1){if(!E(_gu.b)._){return new T2(0,new T(function(){return _gl(_gj,_gt.a);}),new T(function(){return fromJSStr(_gv.a);}));}else{return C > 19 ? new F(function(){return _gc(_);}) : (++C,_gc(_));}}else{return C > 19 ? new F(function(){return _gc(_);}) : (++C,_gc(_));}}}else{return C > 19 ? new F(function(){return _gc(_);}) : (++C,_gc(_));}}}else{return C > 19 ? new F(function(){return _gc(_);}) : (++C,_gc(_));}},_gw=function(_gx){var _gy=B(_gp(_gx));return new T2(0,_gy.a,_gy.b);},_gz=new T(function(){return B(_ga("Ajax.hs:132:5-39|function getJustNum"));}),_gA=new T(function(){return B(_ga("Ajax.hs:133:5-42|function getJustStr"));}),_gB=function(_gC,_){var _gD=E(_gC);if(_gD._==4){var _gE=_gD.a,_gF=_eV(_6q,"lin",_gE);if(!_gF._){return E(_eU);}else{var _gG=function(_,_gH){var _gI=_eV(_6q,"score",_gE);if(!_gI._){var _gJ=_eS(_);return E(_fu);}else{var _gK=_eV(_6q,"tree",_gE);if(!_gK._){var _gL=_eS(_);return E(_fu);}else{return new T3(0,new T(function(){var _gM=E(_gI.a);if(!_gM._){var _gN=_b1(_84,_gM.a),_gO=_gN.a;if(E(_gN.b)>=0){return E(_gO);}else{return E(_gO)-1|0;}}else{return E(_gz);}}),_gH,new T(function(){var _gP=E(_gK.a);if(_gP._==1){return fromJSStr(_gP.a);}else{return E(_gA);}}));}}},_gQ=E(_gF.a);if(_gQ._==3){return _gG(_,new T(function(){return _gl(_gw,_gQ.a);}));}else{return _gG(_,__Z);}}}else{return E(_eU);}},_gR=new T(function(){return B(_ga("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_gS=function(_gT,_gU){while(1){var _gV=(function(_gW,_gX){var _gY=E(_gW);switch(_gY._){case 0:var _gZ=E(_gX);if(!_gZ._){return __Z;}else{_gT=B(A1(_gY.a,_gZ.a));_gU=_gZ.b;return __continue;}break;case 1:var _h0=B(A1(_gY.a,_gX)),_h1=_gX;_gT=_h0;_gU=_h1;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_gY.a,_gX),new T(function(){return _gS(_gY.b,_gX);}));default:return E(_gY.a);}})(_gT,_gU);if(_gV!=__continue){return _gV;}}},_h2=function(_h3,_h4){var _h5=function(_h6){var _h7=E(_h4);if(_h7._==3){return new T2(3,_h7.a,new T(function(){return _h2(_h3,_h7.b);}));}else{var _h8=E(_h3);if(_h8._==2){return _h7;}else{if(_h7._==2){return _h8;}else{var _h9=function(_ha){if(_h7._==4){var _hb=function(_hc){return new T1(4,new T(function(){return _0(_gS(_h8,_hc),_h7.a);}));};return new T1(1,_hb);}else{if(_h8._==1){var _hd=_h8.a;if(!_h7._){return new T1(1,function(_he){return _h2(B(A1(_hd,_he)),_h7);});}else{var _hf=function(_hg){return _h2(B(A1(_hd,_hg)),new T(function(){return B(A1(_h7.a,_hg));}));};return new T1(1,_hf);}}else{if(!_h7._){return E(_gR);}else{var _hh=function(_hi){return _h2(_h8,new T(function(){return B(A1(_h7.a,_hi));}));};return new T1(1,_hh);}}}};switch(_h8._){case 1:if(_h7._==4){var _hj=function(_hk){return new T1(4,new T(function(){return _0(_gS(B(A1(_h8.a,_hk)),_hk),_h7.a);}));};return new T1(1,_hj);}else{return _h9(_);}break;case 4:var _hl=_h8.a;switch(_h7._){case 0:var _hm=function(_hn){var _ho=new T(function(){return _0(_hl,new T(function(){return _gS(_h7,_hn);},1));});return new T1(4,_ho);};return new T1(1,_hm);case 1:var _hp=function(_hq){var _hr=new T(function(){return _0(_hl,new T(function(){return _gS(B(A1(_h7.a,_hq)),_hq);},1));});return new T1(4,_hr);};return new T1(1,_hp);default:return new T1(4,new T(function(){return _0(_hl,_h7.a);}));}break;default:return _h9(_);}}}}},_hs=E(_h3);switch(_hs._){case 0:var _ht=E(_h4);if(!_ht._){var _hu=function(_hv){return _h2(B(A1(_hs.a,_hv)),new T(function(){return B(A1(_ht.a,_hv));}));};return new T1(0,_hu);}else{return _h5(_);}break;case 3:return new T2(3,_hs.a,new T(function(){return _h2(_hs.b,_h4);}));default:return _h5(_);}},_hw=new T(function(){return unCStr("(");}),_hx=new T(function(){return unCStr(")");}),_hy=function(_hz,_hA){while(1){var _hB=E(_hz);if(!_hB._){return (E(_hA)._==0)?true:false;}else{var _hC=E(_hA);if(!_hC._){return false;}else{if(E(_hB.a)!=E(_hC.a)){return false;}else{_hz=_hB.b;_hA=_hC.b;continue;}}}}},_hD=new T2(0,function(_hE,_hF){return E(_hE)==E(_hF);},function(_hG,_hH){return E(_hG)!=E(_hH);}),_hI=function(_hJ,_hK){while(1){var _hL=E(_hJ);if(!_hL._){return (E(_hK)._==0)?true:false;}else{var _hM=E(_hK);if(!_hM._){return false;}else{if(E(_hL.a)!=E(_hM.a)){return false;}else{_hJ=_hL.b;_hK=_hM.b;continue;}}}}},_hN=function(_hO,_hP){return (!_hI(_hO,_hP))?true:false;},_hQ=function(_hR,_hS){var _hT=E(_hR);switch(_hT._){case 0:return new T1(0,function(_hU){return C > 19 ? new F(function(){return _hQ(B(A1(_hT.a,_hU)),_hS);}) : (++C,_hQ(B(A1(_hT.a,_hU)),_hS));});case 1:return new T1(1,function(_hV){return C > 19 ? new F(function(){return _hQ(B(A1(_hT.a,_hV)),_hS);}) : (++C,_hQ(B(A1(_hT.a,_hV)),_hS));});case 2:return new T0(2);case 3:return _h2(B(A1(_hS,_hT.a)),new T(function(){return B(_hQ(_hT.b,_hS));}));default:var _hW=function(_hX){var _hY=E(_hX);if(!_hY._){return __Z;}else{var _hZ=E(_hY.a);return _0(_gS(B(A1(_hS,_hZ.a)),_hZ.b),new T(function(){return _hW(_hY.b);},1));}},_i0=_hW(_hT.a);return (_i0._==0)?new T0(2):new T1(4,_i0);}},_i1=new T0(2),_i2=function(_i3){return new T2(3,_i3,_i1);},_i4=function(_i5,_i6){var _i7=E(_i5);if(!_i7){return C > 19 ? new F(function(){return A1(_i6,0);}) : (++C,A1(_i6,0));}else{var _i8=new T(function(){return B(_i4(_i7-1|0,_i6));});return new T1(0,function(_i9){return E(_i8);});}},_ia=function(_ib,_ic,_id){var _ie=new T(function(){return B(A1(_ib,_i2));}),_if=function(_ig,_ih,_ii,_ij){while(1){var _ik=B((function(_il,_im,_in,_io){var _ip=E(_il);switch(_ip._){case 0:var _iq=E(_im);if(!_iq._){return C > 19 ? new F(function(){return A1(_ic,_io);}) : (++C,A1(_ic,_io));}else{var _ir=_in+1|0,_is=_io;_ig=B(A1(_ip.a,_iq.a));_ih=_iq.b;_ii=_ir;_ij=_is;return __continue;}break;case 1:var _it=B(A1(_ip.a,_im)),_iu=_im,_ir=_in,_is=_io;_ig=_it;_ih=_iu;_ii=_ir;_ij=_is;return __continue;case 2:return C > 19 ? new F(function(){return A1(_ic,_io);}) : (++C,A1(_ic,_io));break;case 3:var _iv=new T(function(){return B(_hQ(_ip,_io));});return C > 19 ? new F(function(){return _i4(_in,function(_iw){return E(_iv);});}) : (++C,_i4(_in,function(_iw){return E(_iv);}));break;default:return C > 19 ? new F(function(){return _hQ(_ip,_io);}) : (++C,_hQ(_ip,_io));}})(_ig,_ih,_ii,_ij));if(_ik!=__continue){return _ik;}}};return function(_ix){return _if(_ie,_ix,0,_id);};},_iy=function(_iz){return C > 19 ? new F(function(){return A1(_iz,__Z);}) : (++C,A1(_iz,__Z));},_iA=function(_iB,_iC){var _iD=function(_iE){var _iF=E(_iE);if(!_iF._){return _iy;}else{var _iG=_iF.a;if(!B(A1(_iB,_iG))){return _iy;}else{var _iH=new T(function(){return _iD(_iF.b);}),_iI=function(_iJ){var _iK=new T(function(){return B(A1(_iH,function(_iL){return C > 19 ? new F(function(){return A1(_iJ,new T2(1,_iG,_iL));}) : (++C,A1(_iJ,new T2(1,_iG,_iL)));}));});return new T1(0,function(_iM){return E(_iK);});};return _iI;}}};return function(_iN){return C > 19 ? new F(function(){return A2(_iD,_iN,_iC);}) : (++C,A2(_iD,_iN,_iC));};},_iO=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_iP=function(_iQ,_iR){var _iS=function(_iT,_iU){var _iV=E(_iT);if(!_iV._){var _iW=new T(function(){return B(A1(_iU,__Z));});return function(_iX){return C > 19 ? new F(function(){return A1(_iX,_iW);}) : (++C,A1(_iX,_iW));};}else{var _iY=E(_iV.a),_iZ=function(_j0){var _j1=new T(function(){return _iS(_iV.b,function(_j2){return C > 19 ? new F(function(){return A1(_iU,new T2(1,_j0,_j2));}) : (++C,A1(_iU,new T2(1,_j0,_j2)));});}),_j3=function(_j4){var _j5=new T(function(){return B(A1(_j1,_j4));});return new T1(0,function(_j6){return E(_j5);});};return _j3;};switch(E(_iQ)){case 8:if(48>_iY){var _j7=new T(function(){return B(A1(_iU,__Z));});return function(_j8){return C > 19 ? new F(function(){return A1(_j8,_j7);}) : (++C,A1(_j8,_j7));};}else{if(_iY>55){var _j9=new T(function(){return B(A1(_iU,__Z));});return function(_ja){return C > 19 ? new F(function(){return A1(_ja,_j9);}) : (++C,A1(_ja,_j9));};}else{return _iZ(_iY-48|0);}}break;case 10:if(48>_iY){var _jb=new T(function(){return B(A1(_iU,__Z));});return function(_jc){return C > 19 ? new F(function(){return A1(_jc,_jb);}) : (++C,A1(_jc,_jb));};}else{if(_iY>57){var _jd=new T(function(){return B(A1(_iU,__Z));});return function(_je){return C > 19 ? new F(function(){return A1(_je,_jd);}) : (++C,A1(_je,_jd));};}else{return _iZ(_iY-48|0);}}break;case 16:if(48>_iY){if(97>_iY){if(65>_iY){var _jf=new T(function(){return B(A1(_iU,__Z));});return function(_jg){return C > 19 ? new F(function(){return A1(_jg,_jf);}) : (++C,A1(_jg,_jf));};}else{if(_iY>70){var _jh=new T(function(){return B(A1(_iU,__Z));});return function(_ji){return C > 19 ? new F(function(){return A1(_ji,_jh);}) : (++C,A1(_ji,_jh));};}else{return _iZ((_iY-65|0)+10|0);}}}else{if(_iY>102){if(65>_iY){var _jj=new T(function(){return B(A1(_iU,__Z));});return function(_jk){return C > 19 ? new F(function(){return A1(_jk,_jj);}) : (++C,A1(_jk,_jj));};}else{if(_iY>70){var _jl=new T(function(){return B(A1(_iU,__Z));});return function(_jm){return C > 19 ? new F(function(){return A1(_jm,_jl);}) : (++C,A1(_jm,_jl));};}else{return _iZ((_iY-65|0)+10|0);}}}else{return _iZ((_iY-97|0)+10|0);}}}else{if(_iY>57){if(97>_iY){if(65>_iY){var _jn=new T(function(){return B(A1(_iU,__Z));});return function(_jo){return C > 19 ? new F(function(){return A1(_jo,_jn);}) : (++C,A1(_jo,_jn));};}else{if(_iY>70){var _jp=new T(function(){return B(A1(_iU,__Z));});return function(_jq){return C > 19 ? new F(function(){return A1(_jq,_jp);}) : (++C,A1(_jq,_jp));};}else{return _iZ((_iY-65|0)+10|0);}}}else{if(_iY>102){if(65>_iY){var _jr=new T(function(){return B(A1(_iU,__Z));});return function(_js){return C > 19 ? new F(function(){return A1(_js,_jr);}) : (++C,A1(_js,_jr));};}else{if(_iY>70){var _jt=new T(function(){return B(A1(_iU,__Z));});return function(_ju){return C > 19 ? new F(function(){return A1(_ju,_jt);}) : (++C,A1(_ju,_jt));};}else{return _iZ((_iY-65|0)+10|0);}}}else{return _iZ((_iY-97|0)+10|0);}}}else{return _iZ(_iY-48|0);}}break;default:return E(_iO);}}},_jv=function(_jw){var _jx=E(_jw);if(!_jx._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_iR,_jx);}) : (++C,A1(_iR,_jx));}};return function(_jy){return C > 19 ? new F(function(){return A3(_iS,_jy,_1C,_jv);}) : (++C,A3(_iS,_jy,_1C,_jv));};},_jz=function(_jA){var _jB=function(_jC){return C > 19 ? new F(function(){return A1(_jA,new T1(5,new T2(0,8,_jC)));}) : (++C,A1(_jA,new T1(5,new T2(0,8,_jC))));},_jD=function(_jE){return C > 19 ? new F(function(){return A1(_jA,new T1(5,new T2(0,16,_jE)));}) : (++C,A1(_jA,new T1(5,new T2(0,16,_jE))));},_jF=function(_jG){switch(E(_jG)){case 79:return new T1(1,_iP(8,_jB));case 88:return new T1(1,_iP(16,_jD));case 111:return new T1(1,_iP(8,_jB));case 120:return new T1(1,_iP(16,_jD));default:return new T0(2);}};return function(_jH){return (E(_jH)==48)?E(new T1(0,_jF)):new T0(2);};},_jI=function(_jJ){return new T1(0,_jz(_jJ));},_jK=function(_jL){return C > 19 ? new F(function(){return A1(_jL,__Z);}) : (++C,A1(_jL,__Z));},_jM=function(_jN){return C > 19 ? new F(function(){return A1(_jN,__Z);}) : (++C,A1(_jN,__Z));},_jO=function(_jP,_jQ){while(1){var _jR=E(_jP);if(!_jR._){var _jS=_jR.a,_jT=E(_jQ);if(!_jT._){var _jU=_jT.a,_jV=addC(_jS,_jU);if(!E(_jV.b)){return new T1(0,_jV.a);}else{_jP=new T1(1,I_fromInt(_jS));_jQ=new T1(1,I_fromInt(_jU));continue;}}else{_jP=new T1(1,I_fromInt(_jS));_jQ=_jT;continue;}}else{var _jW=E(_jQ);if(!_jW._){_jP=_jR;_jQ=new T1(1,I_fromInt(_jW.a));continue;}else{return new T1(1,I_add(_jR.a,_jW.a));}}}},_jX=new T(function(){return _jO(new T1(0,2147483647),new T1(0,1));}),_jY=function(_jZ){var _k0=E(_jZ);if(!_k0._){var _k1=E(_k0.a);return (_k1==(-2147483648))?E(_jX):new T1(0, -_k1);}else{return new T1(1,I_negate(_k0.a));}},_k2=new T1(0,10),_k3=function(_k4,_k5){while(1){var _k6=E(_k4);if(!_k6._){return E(_k5);}else{var _k7=_k5+1|0;_k4=_k6.b;_k5=_k7;continue;}}},_k8=function(_k9){return _7Q(E(_k9));},_ka=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_kb=function(_kc,_kd){var _ke=E(_kd);if(!_ke._){return __Z;}else{var _kf=E(_ke.b);return (_kf._==0)?E(_ka):new T2(1,_jO(_9o(_ke.a,_kc),_kf.a),new T(function(){return _kb(_kc,_kf.b);}));}},_kg=new T1(0,0),_kh=function(_ki,_kj,_kk){while(1){var _kl=(function(_km,_kn,_ko){var _kp=E(_ko);if(!_kp._){return E(_kg);}else{if(!E(_kp.b)._){return E(_kp.a);}else{var _kq=E(_kn);if(_kq<=40){var _kr=function(_ks,_kt){while(1){var _ku=E(_kt);if(!_ku._){return E(_ks);}else{var _kv=_jO(_9o(_ks,_km),_ku.a);_ks=_kv;_kt=_ku.b;continue;}}};return _kr(_kg,_kp);}else{var _kw=_9o(_km,_km);if(!(_kq%2)){var _kx=_kb(_km,_kp);_ki=_kw;_kj=quot(_kq+1|0,2);_kk=_kx;return __continue;}else{var _kx=_kb(_km,new T2(1,_kg,_kp));_ki=_kw;_kj=quot(_kq+1|0,2);_kk=_kx;return __continue;}}}}})(_ki,_kj,_kk);if(_kl!=__continue){return _kl;}}},_ky=function(_kz,_kA){return _kh(_kz,new T(function(){return _k3(_kA,0);},1),_gl(_k8,_kA));},_kB=function(_kC){var _kD=new T(function(){var _kE=new T(function(){var _kF=function(_kG){return C > 19 ? new F(function(){return A1(_kC,new T1(1,new T(function(){return _ky(_k2,_kG);})));}) : (++C,A1(_kC,new T1(1,new T(function(){return _ky(_k2,_kG);}))));};return new T1(1,_iP(10,_kF));}),_kH=function(_kI){if(E(_kI)==43){var _kJ=function(_kK){return C > 19 ? new F(function(){return A1(_kC,new T1(1,new T(function(){return _ky(_k2,_kK);})));}) : (++C,A1(_kC,new T1(1,new T(function(){return _ky(_k2,_kK);}))));};return new T1(1,_iP(10,_kJ));}else{return new T0(2);}},_kL=function(_kM){if(E(_kM)==45){var _kN=function(_kO){return C > 19 ? new F(function(){return A1(_kC,new T1(1,new T(function(){return _jY(_ky(_k2,_kO));})));}) : (++C,A1(_kC,new T1(1,new T(function(){return _jY(_ky(_k2,_kO));}))));};return new T1(1,_iP(10,_kN));}else{return new T0(2);}};return _h2(_h2(new T1(0,_kL),new T1(0,_kH)),_kE);});return _h2(new T1(0,function(_kP){return (E(_kP)==101)?E(_kD):new T0(2);}),new T1(0,function(_kQ){return (E(_kQ)==69)?E(_kD):new T0(2);}));},_kR=function(_kS){var _kT=function(_kU){return C > 19 ? new F(function(){return A1(_kS,new T1(1,_kU));}) : (++C,A1(_kS,new T1(1,_kU)));};return function(_kV){return (E(_kV)==46)?new T1(1,_iP(10,_kT)):new T0(2);};},_kW=function(_kX){return new T1(0,_kR(_kX));},_kY=function(_kZ){var _l0=function(_l1){var _l2=function(_l3){return new T1(1,_ia(_kB,_jK,function(_l4){return C > 19 ? new F(function(){return A1(_kZ,new T1(5,new T3(1,_l1,_l3,_l4)));}) : (++C,A1(_kZ,new T1(5,new T3(1,_l1,_l3,_l4))));}));};return new T1(1,_ia(_kW,_jM,_l2));};return _iP(10,_l0);},_l5=function(_l6){return new T1(1,_kY(_l6));},_l7=function(_l8,_l9,_la){while(1){var _lb=E(_la);if(!_lb._){return false;}else{if(!B(A3(_6k,_l8,_l9,_lb.a))){_la=_lb.b;continue;}else{return true;}}}},_lc=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_ld=function(_le){return _l7(_hD,_le,_lc);},_lf=function(_lg){var _lh=new T(function(){return B(A1(_lg,8));}),_li=new T(function(){return B(A1(_lg,16));});return function(_lj){switch(E(_lj)){case 79:return E(_lh);case 88:return E(_li);case 111:return E(_lh);case 120:return E(_li);default:return new T0(2);}};},_lk=function(_ll){return new T1(0,_lf(_ll));},_lm=function(_ln){return C > 19 ? new F(function(){return A1(_ln,10);}) : (++C,A1(_ln,10));},_lo=function(_lp){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _1V(9,_lp,__Z);})));},_lq=function(_lr,_ls){var _lt=E(_lr);if(!_lt._){var _lu=_lt.a,_lv=E(_ls);return (_lv._==0)?_lu<=_lv.a:I_compareInt(_lv.a,_lu)>=0;}else{var _lw=_lt.a,_lx=E(_ls);return (_lx._==0)?I_compareInt(_lw,_lx.a)<=0:I_compare(_lw,_lx.a)<=0;}},_ly=function(_lz){return new T0(2);},_lA=function(_lB){var _lC=E(_lB);if(!_lC._){return _ly;}else{var _lD=_lC.a,_lE=E(_lC.b);if(!_lE._){return E(_lD);}else{var _lF=new T(function(){return _lA(_lE);}),_lG=function(_lH){return _h2(B(A1(_lD,_lH)),new T(function(){return B(A1(_lF,_lH));}));};return _lG;}}},_lI=function(_lJ,_lK){var _lL=function(_lM,_lN,_lO){var _lP=E(_lM);if(!_lP._){return C > 19 ? new F(function(){return A1(_lO,_lJ);}) : (++C,A1(_lO,_lJ));}else{var _lQ=E(_lN);if(!_lQ._){return new T0(2);}else{if(E(_lP.a)!=E(_lQ.a)){return new T0(2);}else{var _lR=new T(function(){return B(_lL(_lP.b,_lQ.b,_lO));});return new T1(0,function(_lS){return E(_lR);});}}}};return function(_lT){return C > 19 ? new F(function(){return _lL(_lJ,_lT,_lK);}) : (++C,_lL(_lJ,_lT,_lK));};},_lU=new T(function(){return unCStr("SO");}),_lV=function(_lW){var _lX=new T(function(){return B(A1(_lW,14));});return new T1(1,_lI(_lU,function(_lY){return E(_lX);}));},_lZ=new T(function(){return unCStr("SOH");}),_m0=function(_m1){var _m2=new T(function(){return B(A1(_m1,1));});return new T1(1,_lI(_lZ,function(_m3){return E(_m2);}));},_m4=new T(function(){return unCStr("NUL");}),_m5=function(_m6){var _m7=new T(function(){return B(A1(_m6,0));});return new T1(1,_lI(_m4,function(_m8){return E(_m7);}));},_m9=new T(function(){return unCStr("STX");}),_ma=function(_mb){var _mc=new T(function(){return B(A1(_mb,2));});return new T1(1,_lI(_m9,function(_md){return E(_mc);}));},_me=new T(function(){return unCStr("ETX");}),_mf=function(_mg){var _mh=new T(function(){return B(A1(_mg,3));});return new T1(1,_lI(_me,function(_mi){return E(_mh);}));},_mj=new T(function(){return unCStr("EOT");}),_mk=function(_ml){var _mm=new T(function(){return B(A1(_ml,4));});return new T1(1,_lI(_mj,function(_mn){return E(_mm);}));},_mo=new T(function(){return unCStr("ENQ");}),_mp=function(_mq){var _mr=new T(function(){return B(A1(_mq,5));});return new T1(1,_lI(_mo,function(_ms){return E(_mr);}));},_mt=new T(function(){return unCStr("ACK");}),_mu=function(_mv){var _mw=new T(function(){return B(A1(_mv,6));});return new T1(1,_lI(_mt,function(_mx){return E(_mw);}));},_my=new T(function(){return unCStr("BEL");}),_mz=function(_mA){var _mB=new T(function(){return B(A1(_mA,7));});return new T1(1,_lI(_my,function(_mC){return E(_mB);}));},_mD=new T(function(){return unCStr("BS");}),_mE=function(_mF){var _mG=new T(function(){return B(A1(_mF,8));});return new T1(1,_lI(_mD,function(_mH){return E(_mG);}));},_mI=new T(function(){return unCStr("HT");}),_mJ=function(_mK){var _mL=new T(function(){return B(A1(_mK,9));});return new T1(1,_lI(_mI,function(_mM){return E(_mL);}));},_mN=new T(function(){return unCStr("LF");}),_mO=function(_mP){var _mQ=new T(function(){return B(A1(_mP,10));});return new T1(1,_lI(_mN,function(_mR){return E(_mQ);}));},_mS=new T(function(){return unCStr("VT");}),_mT=function(_mU){var _mV=new T(function(){return B(A1(_mU,11));});return new T1(1,_lI(_mS,function(_mW){return E(_mV);}));},_mX=new T(function(){return unCStr("FF");}),_mY=function(_mZ){var _n0=new T(function(){return B(A1(_mZ,12));});return new T1(1,_lI(_mX,function(_n1){return E(_n0);}));},_n2=new T(function(){return unCStr("CR");}),_n3=function(_n4){var _n5=new T(function(){return B(A1(_n4,13));});return new T1(1,_lI(_n2,function(_n6){return E(_n5);}));},_n7=new T(function(){return unCStr("SI");}),_n8=function(_n9){var _na=new T(function(){return B(A1(_n9,15));});return new T1(1,_lI(_n7,function(_nb){return E(_na);}));},_nc=new T(function(){return unCStr("DLE");}),_nd=function(_ne){var _nf=new T(function(){return B(A1(_ne,16));});return new T1(1,_lI(_nc,function(_ng){return E(_nf);}));},_nh=new T(function(){return unCStr("DC1");}),_ni=function(_nj){var _nk=new T(function(){return B(A1(_nj,17));});return new T1(1,_lI(_nh,function(_nl){return E(_nk);}));},_nm=new T(function(){return unCStr("DC2");}),_nn=function(_no){var _np=new T(function(){return B(A1(_no,18));});return new T1(1,_lI(_nm,function(_nq){return E(_np);}));},_nr=new T(function(){return unCStr("DC3");}),_ns=function(_nt){var _nu=new T(function(){return B(A1(_nt,19));});return new T1(1,_lI(_nr,function(_nv){return E(_nu);}));},_nw=new T(function(){return unCStr("DC4");}),_nx=function(_ny){var _nz=new T(function(){return B(A1(_ny,20));});return new T1(1,_lI(_nw,function(_nA){return E(_nz);}));},_nB=new T(function(){return unCStr("NAK");}),_nC=function(_nD){var _nE=new T(function(){return B(A1(_nD,21));});return new T1(1,_lI(_nB,function(_nF){return E(_nE);}));},_nG=new T(function(){return unCStr("SYN");}),_nH=function(_nI){var _nJ=new T(function(){return B(A1(_nI,22));});return new T1(1,_lI(_nG,function(_nK){return E(_nJ);}));},_nL=new T(function(){return unCStr("ETB");}),_nM=function(_nN){var _nO=new T(function(){return B(A1(_nN,23));});return new T1(1,_lI(_nL,function(_nP){return E(_nO);}));},_nQ=new T(function(){return unCStr("CAN");}),_nR=function(_nS){var _nT=new T(function(){return B(A1(_nS,24));});return new T1(1,_lI(_nQ,function(_nU){return E(_nT);}));},_nV=new T(function(){return unCStr("EM");}),_nW=function(_nX){var _nY=new T(function(){return B(A1(_nX,25));});return new T1(1,_lI(_nV,function(_nZ){return E(_nY);}));},_o0=new T(function(){return unCStr("SUB");}),_o1=function(_o2){var _o3=new T(function(){return B(A1(_o2,26));});return new T1(1,_lI(_o0,function(_o4){return E(_o3);}));},_o5=new T(function(){return unCStr("ESC");}),_o6=function(_o7){var _o8=new T(function(){return B(A1(_o7,27));});return new T1(1,_lI(_o5,function(_o9){return E(_o8);}));},_oa=new T(function(){return unCStr("FS");}),_ob=function(_oc){var _od=new T(function(){return B(A1(_oc,28));});return new T1(1,_lI(_oa,function(_oe){return E(_od);}));},_of=new T(function(){return unCStr("GS");}),_og=function(_oh){var _oi=new T(function(){return B(A1(_oh,29));});return new T1(1,_lI(_of,function(_oj){return E(_oi);}));},_ok=new T(function(){return unCStr("RS");}),_ol=function(_om){var _on=new T(function(){return B(A1(_om,30));});return new T1(1,_lI(_ok,function(_oo){return E(_on);}));},_op=new T(function(){return unCStr("US");}),_oq=function(_or){var _os=new T(function(){return B(A1(_or,31));});return new T1(1,_lI(_op,function(_ot){return E(_os);}));},_ou=new T(function(){return unCStr("SP");}),_ov=function(_ow){var _ox=new T(function(){return B(A1(_ow,32));});return new T1(1,_lI(_ou,function(_oy){return E(_ox);}));},_oz=new T(function(){return unCStr("DEL");}),_oA=function(_oB){var _oC=new T(function(){return B(A1(_oB,127));});return new T1(1,_lI(_oz,function(_oD){return E(_oC);}));},_oE=new T(function(){return _lA(new T2(1,function(_oF){return new T1(1,_ia(_m0,_lV,_oF));},new T2(1,_m5,new T2(1,_ma,new T2(1,_mf,new T2(1,_mk,new T2(1,_mp,new T2(1,_mu,new T2(1,_mz,new T2(1,_mE,new T2(1,_mJ,new T2(1,_mO,new T2(1,_mT,new T2(1,_mY,new T2(1,_n3,new T2(1,_n8,new T2(1,_nd,new T2(1,_ni,new T2(1,_nn,new T2(1,_ns,new T2(1,_nx,new T2(1,_nC,new T2(1,_nH,new T2(1,_nM,new T2(1,_nR,new T2(1,_nW,new T2(1,_o1,new T2(1,_o6,new T2(1,_ob,new T2(1,_og,new T2(1,_ol,new T2(1,_oq,new T2(1,_ov,new T2(1,_oA,__Z))))))))))))))))))))))))))))))))));}),_oG=function(_oH){var _oI=new T(function(){return B(A1(_oH,7));}),_oJ=new T(function(){return B(A1(_oH,8));}),_oK=new T(function(){return B(A1(_oH,9));}),_oL=new T(function(){return B(A1(_oH,10));}),_oM=new T(function(){return B(A1(_oH,11));}),_oN=new T(function(){return B(A1(_oH,12));}),_oO=new T(function(){return B(A1(_oH,13));}),_oP=new T(function(){return B(A1(_oH,92));}),_oQ=new T(function(){return B(A1(_oH,39));}),_oR=new T(function(){return B(A1(_oH,34));}),_oS=new T(function(){var _oT=function(_oU){var _oV=new T(function(){return _7Q(E(_oU));}),_oW=function(_oX){var _oY=_ky(_oV,_oX);if(!_lq(_oY,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_oH,new T(function(){var _oZ=_7T(_oY);if(_oZ>>>0>1114111){return _lo(_oZ);}else{return _oZ;}}));}) : (++C,A1(_oH,new T(function(){var _oZ=_7T(_oY);if(_oZ>>>0>1114111){return _lo(_oZ);}else{return _oZ;}})));}};return new T1(1,_iP(_oU,_oW));},_p0=new T(function(){var _p1=new T(function(){return B(A1(_oH,31));}),_p2=new T(function(){return B(A1(_oH,30));}),_p3=new T(function(){return B(A1(_oH,29));}),_p4=new T(function(){return B(A1(_oH,28));}),_p5=new T(function(){return B(A1(_oH,27));}),_p6=new T(function(){return B(A1(_oH,26));}),_p7=new T(function(){return B(A1(_oH,25));}),_p8=new T(function(){return B(A1(_oH,24));}),_p9=new T(function(){return B(A1(_oH,23));}),_pa=new T(function(){return B(A1(_oH,22));}),_pb=new T(function(){return B(A1(_oH,21));}),_pc=new T(function(){return B(A1(_oH,20));}),_pd=new T(function(){return B(A1(_oH,19));}),_pe=new T(function(){return B(A1(_oH,18));}),_pf=new T(function(){return B(A1(_oH,17));}),_pg=new T(function(){return B(A1(_oH,16));}),_ph=new T(function(){return B(A1(_oH,15));}),_pi=new T(function(){return B(A1(_oH,14));}),_pj=new T(function(){return B(A1(_oH,6));}),_pk=new T(function(){return B(A1(_oH,5));}),_pl=new T(function(){return B(A1(_oH,4));}),_pm=new T(function(){return B(A1(_oH,3));}),_pn=new T(function(){return B(A1(_oH,2));}),_po=new T(function(){return B(A1(_oH,1));}),_pp=new T(function(){return B(A1(_oH,0));}),_pq=function(_pr){switch(E(_pr)){case 64:return E(_pp);case 65:return E(_po);case 66:return E(_pn);case 67:return E(_pm);case 68:return E(_pl);case 69:return E(_pk);case 70:return E(_pj);case 71:return E(_oI);case 72:return E(_oJ);case 73:return E(_oK);case 74:return E(_oL);case 75:return E(_oM);case 76:return E(_oN);case 77:return E(_oO);case 78:return E(_pi);case 79:return E(_ph);case 80:return E(_pg);case 81:return E(_pf);case 82:return E(_pe);case 83:return E(_pd);case 84:return E(_pc);case 85:return E(_pb);case 86:return E(_pa);case 87:return E(_p9);case 88:return E(_p8);case 89:return E(_p7);case 90:return E(_p6);case 91:return E(_p5);case 92:return E(_p4);case 93:return E(_p3);case 94:return E(_p2);case 95:return E(_p1);default:return new T0(2);}};return _h2(new T1(0,function(_ps){return (E(_ps)==94)?E(new T1(0,_pq)):new T0(2);}),new T(function(){return B(A1(_oE,_oH));}));});return _h2(new T1(1,_ia(_lk,_lm,_oT)),_p0);});return _h2(new T1(0,function(_pt){switch(E(_pt)){case 34:return E(_oR);case 39:return E(_oQ);case 92:return E(_oP);case 97:return E(_oI);case 98:return E(_oJ);case 102:return E(_oN);case 110:return E(_oL);case 114:return E(_oO);case 116:return E(_oK);case 118:return E(_oM);default:return new T0(2);}}),_oS);},_pu=function(_pv){return C > 19 ? new F(function(){return A1(_pv,0);}) : (++C,A1(_pv,0));},_pw=function(_px){var _py=E(_px);if(!_py._){return _pu;}else{var _pz=E(_py.a),_pA=_pz>>>0,_pB=new T(function(){return _pw(_py.b);});if(_pA>887){var _pC=u_iswspace(_pz);if(!E(_pC)){return _pu;}else{var _pD=function(_pE){var _pF=new T(function(){return B(A1(_pB,_pE));});return new T1(0,function(_pG){return E(_pF);});};return _pD;}}else{if(_pA==32){var _pH=function(_pI){var _pJ=new T(function(){return B(A1(_pB,_pI));});return new T1(0,function(_pK){return E(_pJ);});};return _pH;}else{if(_pA-9>>>0>4){if(_pA==160){var _pL=function(_pM){var _pN=new T(function(){return B(A1(_pB,_pM));});return new T1(0,function(_pO){return E(_pN);});};return _pL;}else{return _pu;}}else{var _pP=function(_pQ){var _pR=new T(function(){return B(A1(_pB,_pQ));});return new T1(0,function(_pS){return E(_pR);});};return _pP;}}}}},_pT=function(_pU){var _pV=new T(function(){return B(_pT(_pU));}),_pW=function(_pX){return (E(_pX)==92)?E(_pV):new T0(2);},_pY=function(_pZ){return E(new T1(0,_pW));},_q0=new T1(1,function(_q1){return C > 19 ? new F(function(){return A2(_pw,_q1,_pY);}) : (++C,A2(_pw,_q1,_pY));}),_q2=new T(function(){return B(_oG(function(_q3){return C > 19 ? new F(function(){return A1(_pU,new T2(0,_q3,true));}) : (++C,A1(_pU,new T2(0,_q3,true)));}));}),_q4=function(_q5){var _q6=E(_q5);if(_q6==38){return E(_pV);}else{var _q7=_q6>>>0;if(_q7>887){var _q8=u_iswspace(_q6);return (E(_q8)==0)?new T0(2):E(_q0);}else{return (_q7==32)?E(_q0):(_q7-9>>>0>4)?(_q7==160)?E(_q0):new T0(2):E(_q0);}}};return _h2(new T1(0,function(_q9){return (E(_q9)==92)?E(new T1(0,_q4)):new T0(2);}),new T1(0,function(_qa){var _qb=E(_qa);if(_qb==92){return E(_q2);}else{return C > 19 ? new F(function(){return A1(_pU,new T2(0,_qb,false));}) : (++C,A1(_pU,new T2(0,_qb,false)));}}));},_qc=function(_qd,_qe){var _qf=new T(function(){return B(A1(_qe,new T1(1,new T(function(){return B(A1(_qd,__Z));}))));}),_qg=function(_qh){var _qi=E(_qh),_qj=E(_qi.a);if(_qj==34){if(!E(_qi.b)){return E(_qf);}else{return C > 19 ? new F(function(){return _qc(function(_qk){return C > 19 ? new F(function(){return A1(_qd,new T2(1,_qj,_qk));}) : (++C,A1(_qd,new T2(1,_qj,_qk)));},_qe);}) : (++C,_qc(function(_qk){return C > 19 ? new F(function(){return A1(_qd,new T2(1,_qj,_qk));}) : (++C,A1(_qd,new T2(1,_qj,_qk)));},_qe));}}else{return C > 19 ? new F(function(){return _qc(function(_ql){return C > 19 ? new F(function(){return A1(_qd,new T2(1,_qj,_ql));}) : (++C,A1(_qd,new T2(1,_qj,_ql)));},_qe);}) : (++C,_qc(function(_ql){return C > 19 ? new F(function(){return A1(_qd,new T2(1,_qj,_ql));}) : (++C,A1(_qd,new T2(1,_qj,_ql)));},_qe));}};return C > 19 ? new F(function(){return _pT(_qg);}) : (++C,_pT(_qg));},_qm=new T(function(){return unCStr("_\'");}),_qn=function(_qo){var _qp=u_iswalnum(_qo);if(!E(_qp)){return _l7(_hD,_qo,_qm);}else{return true;}},_qq=function(_qr){return _qn(E(_qr));},_qs=new T(function(){return unCStr(",;()[]{}`");}),_qt=new T(function(){return unCStr("=>");}),_qu=new T(function(){return unCStr("~");}),_qv=new T(function(){return unCStr("@");}),_qw=new T(function(){return unCStr("->");}),_qx=new T(function(){return unCStr("<-");}),_qy=new T(function(){return unCStr("|");}),_qz=new T(function(){return unCStr("\\");}),_qA=new T(function(){return unCStr("=");}),_qB=new T(function(){return unCStr("::");}),_qC=new T(function(){return unCStr("..");}),_qD=function(_qE){var _qF=new T(function(){return B(A1(_qE,new T0(6)));}),_qG=new T(function(){var _qH=new T(function(){var _qI=function(_qJ){var _qK=new T(function(){return B(A1(_qE,new T1(0,_qJ)));});return new T1(0,function(_qL){return (E(_qL)==39)?E(_qK):new T0(2);});};return B(_oG(_qI));}),_qM=function(_qN){var _qO=E(_qN);switch(_qO){case 39:return new T0(2);case 92:return E(_qH);default:var _qP=new T(function(){return B(A1(_qE,new T1(0,_qO)));});return new T1(0,function(_qQ){return (E(_qQ)==39)?E(_qP):new T0(2);});}},_qR=new T(function(){var _qS=new T(function(){return B(_qc(_1C,_qE));}),_qT=new T(function(){var _qU=new T(function(){var _qV=new T(function(){var _qW=function(_qX){var _qY=E(_qX),_qZ=u_iswalpha(_qY);return (E(_qZ)==0)?(_qY==95)?new T1(1,_iA(_qq,function(_r0){return C > 19 ? new F(function(){return A1(_qE,new T1(3,new T2(1,_qY,_r0)));}) : (++C,A1(_qE,new T1(3,new T2(1,_qY,_r0))));})):new T0(2):new T1(1,_iA(_qq,function(_r1){return C > 19 ? new F(function(){return A1(_qE,new T1(3,new T2(1,_qY,_r1)));}) : (++C,A1(_qE,new T1(3,new T2(1,_qY,_r1))));}));};return _h2(new T1(0,_qW),new T(function(){return new T1(1,_ia(_jI,_l5,_qE));}));}),_r2=function(_r3){return (!_l7(_hD,_r3,_lc))?new T0(2):new T1(1,_iA(_ld,function(_r4){var _r5=new T2(1,_r3,_r4);if(!_l7(new T2(0,_hI,_hN),_r5,new T2(1,_qC,new T2(1,_qB,new T2(1,_qA,new T2(1,_qz,new T2(1,_qy,new T2(1,_qx,new T2(1,_qw,new T2(1,_qv,new T2(1,_qu,new T2(1,_qt,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_qE,new T1(4,_r5));}) : (++C,A1(_qE,new T1(4,_r5)));}else{return C > 19 ? new F(function(){return A1(_qE,new T1(2,_r5));}) : (++C,A1(_qE,new T1(2,_r5)));}}));};return _h2(new T1(0,_r2),_qV);});return _h2(new T1(0,function(_r6){if(!_l7(_hD,_r6,_qs)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_qE,new T1(2,new T2(1,_r6,__Z)));}) : (++C,A1(_qE,new T1(2,new T2(1,_r6,__Z))));}}),_qU);});return _h2(new T1(0,function(_r7){return (E(_r7)==34)?E(_qS):new T0(2);}),_qT);});return _h2(new T1(0,function(_r8){return (E(_r8)==39)?E(new T1(0,_qM)):new T0(2);}),_qR);});return _h2(new T1(1,function(_r9){return (E(_r9)._==0)?E(_qF):new T0(2);}),_qG);},_ra=function(_rb,_rc){var _rd=new T(function(){var _re=new T(function(){var _rf=function(_rg){var _rh=new T(function(){var _ri=new T(function(){return B(A1(_rc,_rg));});return B(_qD(function(_rj){var _rk=E(_rj);return (_rk._==2)?(!_hy(_rk.a,_hx))?new T0(2):E(_ri):new T0(2);}));}),_rl=function(_rm){return E(_rh);};return new T1(1,function(_rn){return C > 19 ? new F(function(){return A2(_pw,_rn,_rl);}) : (++C,A2(_pw,_rn,_rl));});};return B(A2(_rb,0,_rf));});return B(_qD(function(_ro){var _rp=E(_ro);return (_rp._==2)?(!_hy(_rp.a,_hw))?new T0(2):E(_re):new T0(2);}));}),_rq=function(_rr){return E(_rd);};return function(_rs){return C > 19 ? new F(function(){return A2(_pw,_rs,_rq);}) : (++C,A2(_pw,_rs,_rq));};},_rt=function(_ru,_rv){var _rw=function(_rx){var _ry=new T(function(){return B(A1(_ru,_rx));}),_rz=function(_rA){return _h2(B(A1(_ry,_rA)),new T(function(){return new T1(1,_ra(_rw,_rA));}));};return _rz;},_rB=new T(function(){return B(A1(_ru,_rv));}),_rC=function(_rD){return _h2(B(A1(_rB,_rD)),new T(function(){return new T1(1,_ra(_rw,_rD));}));};return _rC;},_rE=function(_rF,_rG){var _rH=function(_rI,_rJ){var _rK=function(_rL){return C > 19 ? new F(function(){return A1(_rJ,new T(function(){return  -E(_rL);}));}) : (++C,A1(_rJ,new T(function(){return  -E(_rL);})));},_rM=new T(function(){return B(_qD(function(_rN){return C > 19 ? new F(function(){return A3(_rF,_rN,_rI,_rK);}) : (++C,A3(_rF,_rN,_rI,_rK));}));}),_rO=function(_rP){return E(_rM);},_rQ=function(_rR){return C > 19 ? new F(function(){return A2(_pw,_rR,_rO);}) : (++C,A2(_pw,_rR,_rO));},_rS=new T(function(){return B(_qD(function(_rT){var _rU=E(_rT);if(_rU._==4){var _rV=E(_rU.a);if(!_rV._){return C > 19 ? new F(function(){return A3(_rF,_rU,_rI,_rJ);}) : (++C,A3(_rF,_rU,_rI,_rJ));}else{if(E(_rV.a)==45){if(!E(_rV.b)._){return E(new T1(1,_rQ));}else{return C > 19 ? new F(function(){return A3(_rF,_rU,_rI,_rJ);}) : (++C,A3(_rF,_rU,_rI,_rJ));}}else{return C > 19 ? new F(function(){return A3(_rF,_rU,_rI,_rJ);}) : (++C,A3(_rF,_rU,_rI,_rJ));}}}else{return C > 19 ? new F(function(){return A3(_rF,_rU,_rI,_rJ);}) : (++C,A3(_rF,_rU,_rI,_rJ));}}));}),_rW=function(_rX){return E(_rS);};return new T1(1,function(_rY){return C > 19 ? new F(function(){return A2(_pw,_rY,_rW);}) : (++C,A2(_pw,_rY,_rW));});};return _rt(_rH,_rG);},_rZ=function(_s0){var _s1=E(_s0);if(!_s1._){var _s2=_s1.b,_s3=new T(function(){return _kh(new T(function(){return _7Q(E(_s1.a));}),new T(function(){return _k3(_s2,0);},1),_gl(_k8,_s2));});return new T1(1,_s3);}else{return (E(_s1.b)._==0)?(E(_s1.c)._==0)?new T1(1,new T(function(){return _ky(_k2,_s1.a);})):__Z:__Z;}},_s4=function(_s5,_s6){return new T0(2);},_s7=function(_s8){var _s9=E(_s8);if(_s9._==5){var _sa=_rZ(_s9.a);if(!_sa._){return _s4;}else{var _sb=new T(function(){return _7T(_sa.a);});return function(_sc,_sd){return C > 19 ? new F(function(){return A1(_sd,_sb);}) : (++C,A1(_sd,_sb));};}}else{return _s4;}},_se=function(_sf){return _rE(_s7,_sf);},_sg=new T(function(){return unCStr("[");}),_sh=function(_si,_sj){var _sk=function(_sl,_sm){var _sn=new T(function(){return B(A1(_sm,__Z));}),_so=new T(function(){var _sp=function(_sq){return _sk(true,function(_sr){return C > 19 ? new F(function(){return A1(_sm,new T2(1,_sq,_sr));}) : (++C,A1(_sm,new T2(1,_sq,_sr)));});};return B(A2(_si,0,_sp));}),_ss=new T(function(){return B(_qD(function(_st){var _su=E(_st);if(_su._==2){var _sv=E(_su.a);if(!_sv._){return new T0(2);}else{var _sw=_sv.b;switch(E(_sv.a)){case 44:return (E(_sw)._==0)?(!E(_sl))?new T0(2):E(_so):new T0(2);case 93:return (E(_sw)._==0)?E(_sn):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_sx=function(_sy){return E(_ss);};return new T1(1,function(_sz){return C > 19 ? new F(function(){return A2(_pw,_sz,_sx);}) : (++C,A2(_pw,_sz,_sx));});},_sA=function(_sB,_sC){return C > 19 ? new F(function(){return _sD(_sC);}) : (++C,_sD(_sC));},_sD=function(_sE){var _sF=new T(function(){var _sG=new T(function(){var _sH=new T(function(){var _sI=function(_sJ){return _sk(true,function(_sK){return C > 19 ? new F(function(){return A1(_sE,new T2(1,_sJ,_sK));}) : (++C,A1(_sE,new T2(1,_sJ,_sK)));});};return B(A2(_si,0,_sI));});return _h2(_sk(false,_sE),_sH);});return B(_qD(function(_sL){var _sM=E(_sL);return (_sM._==2)?(!_hy(_sM.a,_sg))?new T0(2):E(_sG):new T0(2);}));}),_sN=function(_sO){return E(_sF);};return _h2(new T1(1,function(_sP){return C > 19 ? new F(function(){return A2(_pw,_sP,_sN);}) : (++C,A2(_pw,_sP,_sN));}),new T(function(){return new T1(1,_ra(_sA,_sE));}));};return C > 19 ? new F(function(){return _sD(_sj);}) : (++C,_sD(_sj));},_sQ=function(_sR){var _sS=function(_sT){return E(new T2(3,_sR,_i1));};return new T1(1,function(_sU){return C > 19 ? new F(function(){return A2(_pw,_sU,_sS);}) : (++C,A2(_pw,_sU,_sS));});},_sV=new T(function(){return B(_sh(_se,_sQ));}),_sW=new T(function(){return unCStr("Prelude.read: ambiguous parse");}),_sX=new T(function(){return unCStr("Prelude.read: no parse");}),_sY=function(_sZ){while(1){var _t0=(function(_t1){var _t2=E(_t1);if(!_t2._){return __Z;}else{var _t3=_t2.b,_t4=E(_t2.a);if(!E(_t4.b)._){return new T2(1,_t4.a,new T(function(){return _sY(_t3);}));}else{_sZ=_t3;return __continue;}}})(_sZ);if(_t0!=__continue){return _t0;}}},_t5=function(_t6,_t7,_){var _t8=new T(function(){var _t9=_sY(_gS(_sV,new T(function(){return fromJSStr(E(_t6));})));if(!_t9._){return err(_sX);}else{if(!E(_t9.b)._){return E(_t9.a);}else{return err(_sW);}}}),_ta=E(_t7);if(_ta._==3){var _tb=E(_ta.a);if(!_tb._){return new T2(0,_t8,__Z);}else{var _tc=E(_tb.a);if(_tc._==3){if(!E(_tb.b)._){var _td=_eN(_gl(_gB,_tc.a),_);return new T2(0,_t8,new T2(1,_td,__Z));}else{return new T2(0,_t8,__Z);}}else{return new T2(0,_t8,__Z);}}}else{return new T2(0,_t8,__Z);}},_te=function(_tf,_){var _tg=E(_tf);return _t5(_tg.a,_tg.b,_);},_th=function(_ti,_tj){var _tk=E(_ti);if(!_tk._){return __Z;}else{var _tl=_tk.a,_tm=E(_tj);return (_tm==1)?new T2(1,function(_){return _te(_tl,_);},__Z):new T2(1,function(_){return _te(_tl,_);},new T(function(){return _th(_tk.b,_tm-1|0);}));}},_tn=function(_){var _to=_be("Error decoding tree data");return _bd(_);},_tp=function(_tq,_){var _tr=E(_tq);if(!_tr._){return __Z;}else{var _ts=B(A1(_tr.a,_)),_tt=_tp(_tr.b,_);return new T2(1,_ts,_tt);}},_tu=new T(function(){return B(_ga("Ajax.hs:(97,5)-(101,81)|function decodeMenu"));}),_tv=new T(function(){return _fs(new T1(0,new T(function(){return unCStr("Error decoding tree data");})),_fh);}),_tw=function(_tx,_){var _ty=E(_tx);if(_ty._==4){var _tz=_ty.a,_tA=_eV(_6q,"lin",_tz);if(!_tA._){return E(_eU);}else{var _tB=function(_,_tC){var _tD=_eV(_6q,"menu",_tz);if(!_tD._){return E(_eU);}else{var _tE=E(_tD.a);if(_tE._==4){var _tF=_tE.a,_tG=_k3(_tF,0),_tH=function(_,_tI){var _tJ=_eV(_6q,"grammar",_tz);if(!_tJ._){var _tK=_tn(_);return E(_tv);}else{var _tL=_eV(_6q,"tree",_tz);if(!_tL._){var _tM=_tn(_);return E(_tv);}else{return new T4(0,new T(function(){var _tN=E(_tJ.a);if(_tN._==1){return fromJSStr(_tN.a);}else{return E(_gA);}}),new T(function(){var _tO=E(_tL.a);if(_tO._==1){return fromJSStr(_tO.a);}else{return E(_gA);}}),_tC,new T1(0,new T(function(){var _tP=E(_tI);if(!_tP._){return new T0(1);}else{return B(_eG(_tP));}})));}}};if(0>=_tG){var _tQ=_tp(__Z,_);return _tH(_,_tQ);}else{var _tR=_tp(_th(_tF,_tG),_);return _tH(_,_tR);}}else{return E(_tu);}}},_tS=E(_tA.a);if(_tS._==3){return _tB(_,new T(function(){return _gl(_gw,_tS.a);}));}else{return _tB(_,__Z);}}}else{return E(_eU);}},_tT=function(_tU){var _tV=E(_tU);return (_tV._==0)?E(_eU):E(_tV.a);},_tW=new T(function(){return _fs(new T1(0,new T(function(){return unCStr("Error decoding message data");})),_fh);}),_tX=new T(function(){return fromJSStr("Invalid JSON!");}),_tY=new T(function(){return _fs(new T1(0,_tX),_fh);}),_tZ=new T(function(){return unAppCStr("Error ",_tX);}),_u0=new T(function(){return B(_ga("Ajax.hs:131:5-35|function getJustBool"));}),_u1=function(_u2,_){var _u3=jsParseJSON(_u2);if(!_u3._){var _u4=_be(toJSStr(E(_tZ)));return E(_tY);}else{var _u5=_u3.a,_u6=E(_u5);if(_u6._==4){var _u7=_eV(_6q,"a",_u6.a);}else{var _u7=__Z;}var _u8=_tw(_tT(_u7),_),_u9=_u8;if(_u5._==4){var _ua=_eV(_6q,"b",_u5.a);}else{var _ua=__Z;}var _ub=_tw(_tT(_ua),_);if(_u5._==4){var _uc=_u5.a,_ud=_eV(_6q,"success",_uc);if(!_ud._){var _ue=_bf(_);return E(_tW);}else{var _uf=_eV(_6q,"score",_uc);if(!_uf._){var _ug=_bf(_);return E(_tW);}else{if(!E(_u7)._){var _uh=_bf(_);return E(_tW);}else{if(!E(_ua)._){var _ui=_bf(_);return E(_tW);}else{return new T4(0,new T(function(){var _uj=E(_ud.a);if(_uj._==2){return E(_uj.a);}else{return E(_u0);}}),new T(function(){var _uk=E(_uf.a);if(!_uk._){var _ul=_b1(_84,_uk.a),_um=_ul.a;if(E(_ul.b)>=0){return E(_um);}else{return E(_um)-1|0;}}else{return E(_gz);}}),_u9,_ub);}}}}}else{var _un=_bf(_);return E(_tW);}}},_uo=new T(function(){return JSON.stringify;}),_up=function(_uq,_ur){var _us=E(_ur);switch(_us._){case 0:return new T2(0,new T(function(){return jsShow(_us.a);}),_uq);case 1:return new T2(0,new T(function(){var _ut=E(_uo)(_us.a);return String(_ut);}),_uq);case 2:return (!E(_us.a))?new T2(0,"false",_uq):new T2(0,"true",_uq);case 3:var _uu=E(_us.a);if(!_uu._){return new T2(0,"[",new T2(1,"]",_uq));}else{var _uv=new T(function(){var _uw=new T(function(){var _ux=function(_uy){var _uz=E(_uy);if(!_uz._){return E(new T2(1,"]",_uq));}else{var _uA=new T(function(){var _uB=_up(new T(function(){return _ux(_uz.b);}),_uz.a);return new T2(1,_uB.a,_uB.b);});return new T2(1,",",_uA);}};return _ux(_uu.b);}),_uC=_up(_uw,_uu.a);return new T2(1,_uC.a,_uC.b);});return new T2(0,"[",_uv);}break;case 4:var _uD=E(_us.a);if(!_uD._){return new T2(0,"{",new T2(1,"}",_uq));}else{var _uE=E(_uD.a),_uF=new T(function(){var _uG=new T(function(){var _uH=function(_uI){var _uJ=E(_uI);if(!_uJ._){return E(new T2(1,"}",_uq));}else{var _uK=E(_uJ.a),_uL=new T(function(){var _uM=_up(new T(function(){return _uH(_uJ.b);}),_uK.b);return new T2(1,_uM.a,_uM.b);});return new T2(1,",",new T2(1,"\"",new T2(1,_uK.a,new T2(1,"\"",new T2(1,":",_uL)))));}};return _uH(_uD.b);}),_uN=_up(_uG,_uE.b);return new T2(1,_uN.a,_uN.b);});return new T2(0,"{",new T2(1,new T(function(){var _uO=E(_uo)(E(_uE.a));return String(_uO);}),new T2(1,":",_uF)));}break;default:return new T2(0,"null",_uq);}},_uP=new T(function(){return toJSStr(__Z);}),_uQ=function(_uR){var _uS=_up(__Z,_uR),_uT=jsCat(new T2(1,_uS.a,_uS.b),E(_uP));return E(_uT);},_uU=function(_uV,_uW){return new T2(1,new T2(0,"grammar",new T(function(){return new T1(1,toJSStr(E(_uV)));})),new T2(1,new T2(0,"tree",new T(function(){return new T1(1,toJSStr(E(_uW)));})),__Z));},_uX=function(_uY){var _uZ=E(_uY);return new T1(4,E(_uU(_uZ.a,_uZ.b)));},_v0=function(_v1){var _v2=E(_v1);if(!_v2._){return _uQ(new T0(5));}else{return _uQ(new T1(4,E(new T2(1,new T2(0,"score",new T(function(){return new T1(0,E(_v2.a));})),new T2(1,new T2(0,"a",new T(function(){return _uX(_v2.b);})),new T2(1,new T2(0,"b",new T(function(){return _uX(_v2.c);})),__Z))))));}},_v3=function(_v4){return E(E(_v4).a);},_v5=function(_v6,_v7,_v8,_v9,_va){return C > 19 ? new F(function(){return A2(_v7,_v8,new T2(1,B(A2(_v3,_v6,E(_va))),E(_v9)));}) : (++C,A2(_v7,_v8,new T2(1,B(A2(_v3,_v6,E(_va))),E(_v9))));},_vb=function(_vc){return E(E(_vc).a);},_vd=function(_ve){return E(E(_ve).a);},_vf=function(_vg){return E(E(_vg).a);},_vh=function(_vi){return E(E(_vi).b);},_vj=new T(function(){return unCStr("base");}),_vk=new T(function(){return unCStr("GHC.IO.Exception");}),_vl=new T(function(){return unCStr("IOException");}),_vm=function(_vn){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_vj,_vk,_vl),__Z,__Z));},_vo=new T(function(){return unCStr(": ");}),_vp=new T(function(){return unCStr(")");}),_vq=new T(function(){return unCStr(" (");}),_vr=new T(function(){return unCStr("interrupted");}),_vs=new T(function(){return unCStr("system error");}),_vt=new T(function(){return unCStr("unsatisified constraints");}),_vu=new T(function(){return unCStr("user error");}),_vv=new T(function(){return unCStr("permission denied");}),_vw=new T(function(){return unCStr("illegal operation");}),_vx=new T(function(){return unCStr("end of file");}),_vy=new T(function(){return unCStr("resource exhausted");}),_vz=new T(function(){return unCStr("resource busy");}),_vA=new T(function(){return unCStr("does not exist");}),_vB=new T(function(){return unCStr("already exists");}),_vC=new T(function(){return unCStr("resource vanished");}),_vD=new T(function(){return unCStr("timeout");}),_vE=new T(function(){return unCStr("unsupported operation");}),_vF=new T(function(){return unCStr("hardware fault");}),_vG=new T(function(){return unCStr("inappropriate type");}),_vH=new T(function(){return unCStr("invalid argument");}),_vI=new T(function(){return unCStr("failed");}),_vJ=new T(function(){return unCStr("protocol error");}),_vK=function(_vL,_vM){switch(E(_vL)){case 0:return _0(_vB,_vM);case 1:return _0(_vA,_vM);case 2:return _0(_vz,_vM);case 3:return _0(_vy,_vM);case 4:return _0(_vx,_vM);case 5:return _0(_vw,_vM);case 6:return _0(_vv,_vM);case 7:return _0(_vu,_vM);case 8:return _0(_vt,_vM);case 9:return _0(_vs,_vM);case 10:return _0(_vJ,_vM);case 11:return _0(_vI,_vM);case 12:return _0(_vH,_vM);case 13:return _0(_vG,_vM);case 14:return _0(_vF,_vM);case 15:return _0(_vE,_vM);case 16:return _0(_vD,_vM);case 17:return _0(_vC,_vM);default:return _0(_vr,_vM);}},_vN=new T(function(){return unCStr("}");}),_vO=new T(function(){return unCStr("{handle: ");}),_vP=function(_vQ,_vR,_vS,_vT,_vU,_vV){var _vW=new T(function(){var _vX=new T(function(){var _vY=new T(function(){var _vZ=E(_vT);if(!_vZ._){return E(_vV);}else{var _w0=new T(function(){return _0(_vZ,new T(function(){return _0(_vp,_vV);},1));},1);return _0(_vq,_w0);}},1);return _vK(_vR,_vY);}),_w1=E(_vS);if(!_w1._){return E(_vX);}else{return _0(_w1,new T(function(){return _0(_vo,_vX);},1));}}),_w2=E(_vU);if(!_w2._){var _w3=E(_vQ);if(!_w3._){return E(_vW);}else{var _w4=E(_w3.a);if(!_w4._){var _w5=new T(function(){var _w6=new T(function(){return _0(_vN,new T(function(){return _0(_vo,_vW);},1));},1);return _0(_w4.a,_w6);},1);return _0(_vO,_w5);}else{var _w7=new T(function(){var _w8=new T(function(){return _0(_vN,new T(function(){return _0(_vo,_vW);},1));},1);return _0(_w4.a,_w8);},1);return _0(_vO,_w7);}}}else{return _0(_w2.a,new T(function(){return _0(_vo,_vW);},1));}},_w9=function(_wa){var _wb=E(_wa);return _vP(_wb.a,_wb.b,_wb.c,_wb.d,_wb.f,__Z);},_wc=function(_wd,_we){var _wf=E(_wd);return _vP(_wf.a,_wf.b,_wf.c,_wf.d,_wf.f,_we);},_wg=new T(function(){return new T5(0,_vm,new T3(0,function(_wh,_wi,_wj){var _wk=E(_wi);return _vP(_wk.a,_wk.b,_wk.c,_wk.d,_wk.f,_wj);},_w9,function(_wl,_wm){return _3p(_wc,_wl,_wm);}),_wn,function(_wo){var _wp=E(_wo);return _7b(_79(_wp.a),_vm,_wp.b);},_w9);}),_wn=function(_wq){return new T2(0,_wg,_wq);},_wr=function(_ws,_){var _wt=_ws["type"],_wu=String(_wt),_wv=strEq(_wu,"network");if(!E(_wv)){var _ww=strEq(_wu,"http");if(!E(_ww)){var _wx=new T(function(){var _wy=new T(function(){return unAppCStr("unknown type of ajax error: ",new T(function(){return fromJSStr(_wu);}));});return _wn(new T6(0,__Z,7,__Z,_wy,__Z,__Z));});return die(_wx);}else{var _wz=_ws["status"],_wA=_ws["status-text"];return new T2(1,new T(function(){var _wB=Number(_wz);return jsTrunc(_wB);}),new T(function(){return String(_wA);}));}}else{return __Z;}},_wC=function(_wD,_){var _wE=E(_wD);if(!_wE._){return __Z;}else{var _wF=_wr(E(_wE.a),_),_wG=_wC(_wE.b,_);return new T2(1,_wF,_wG);}},_wH=function(_wI,_){var _wJ=__arr2lst(0,_wI);return _wC(_wJ,_);},_wK=new T2(0,function(_wL,_){return _wr(E(_wL),_);},function(_wM,_){return _wH(E(_wM),_);}),_wN=function(_wO){return E(E(_wO).a);},_wP=function(_wQ){var _wR=B(A1(_wQ,_));return E(_wR);},_wS=new T(function(){return _wP(function(_){return __jsNull();});}),_wT=function(_wU,_wV,_){var _wW=__eq(_wV,E(_wS));if(!E(_wW)){var _wX=__isUndef(_wV);if(!E(_wX)){var _wY=B(A3(_wN,_wU,_wV,_));return new T1(1,_wY);}else{return __Z;}}else{return __Z;}},_wZ=function(_x0,_x1,_){var _x2=__arr2lst(0,_x1),_x3=function(_x4,_){var _x5=E(_x4);if(!_x5._){return __Z;}else{var _x6=_x5.b,_x7=E(_x5.a),_x8=__eq(_x7,E(_wS));if(!E(_x8)){var _x9=__isUndef(_x7);if(!E(_x9)){var _xa=B(A3(_wN,_x0,_x7,_)),_xb=_x3(_x6,_);return new T2(1,new T1(1,_xa),_xb);}else{var _xc=_x3(_x6,_);return new T2(1,__Z,_xc);}}else{var _xd=_x3(_x6,_);return new T2(1,__Z,_xd);}}};return _x3(_x2,_);},_xe=new T2(0,function(_xf,_){return _wT(_wK,E(_xf),_);},function(_xg,_){return _wZ(_wK,E(_xg),_);}),_xh=function(_xi,_xj,_){var _xk=B(A2(_xi,new T(function(){var _xl=E(_xj),_xm=__eq(_xl,E(_wS));if(!E(_xm)){var _xn=__isUndef(_xl);if(!E(_xn)){return new T1(1,_xl);}else{return __Z;}}else{return __Z;}}),_));return _wS;},_xo=new T2(0,_xh,function(_xp){return 2;}),_xq=function(_xr){return E(E(_xr).a);},_xs=function(_xt,_xu,_xv,_xw){var _xx=new T(function(){return B(A1(_xv,new T(function(){var _xy=B(A3(_wN,_xt,_xw,_));return E(_xy);})));});return C > 19 ? new F(function(){return A2(_xq,_xu,_xx);}) : (++C,A2(_xq,_xu,_xx));},_xz=function(_xA){return E(E(_xA).b);},_xB=new T(function(){return err(new T(function(){return unCStr("Prelude.undefined");}));}),_xC=function(_xD,_xE,_xF){var _xG=__createJSFunc(1+B(A2(_xz,_xE,new T(function(){return B(A1(_xF,_xB));})))|0,function(_xH){return C > 19 ? new F(function(){return _xs(_xD,_xE,_xF,_xH);}) : (++C,_xs(_xD,_xE,_xF,_xH));});return E(_xG);},_xI=function(_xJ,_xK,_xL){return _xC(_xJ,_xK,_xL);},_xM=function(_xN,_xO,_xP){var _xQ=__lst2arr(_gl(function(_xR){return _xI(_xN,_xO,_xR);},_xP));return E(_xQ);},_xS=new T2(0,function(_xT){return _xC(_xe,_xo,_xT);},function(_xU){return _xM(_xe,_xo,_xU);}),_xV=function(_xW,_){var _xX=E(_xW);if(!_xX._){return __Z;}else{var _xY=_xV(_xX.b,_);return new T2(1,0,_xY);}},_xZ=function(_y0,_){var _y1=__arr2lst(0,_y0);return _xV(_y1,_);},_y2=function(_y3,_){return _xZ(E(_y3),_);},_y4=function(_y5,_){return _bd(_);},_y6=function(_y7,_y8,_y9,_){var _ya=__apply(_y8,E(_y9));return C > 19 ? new F(function(){return A3(_wN,_y7,_ya,_);}) : (++C,A3(_wN,_y7,_ya,_));},_yb=function(_yc,_yd,_ye,_){return C > 19 ? new F(function(){return _y6(_yc,E(_yd),_ye,_);}) : (++C,_y6(_yc,E(_yd),_ye,_));},_yf=function(_yg,_yh,_yi,_){return C > 19 ? new F(function(){return _yb(_yg,_yh,_yi,_);}) : (++C,_yb(_yg,_yh,_yi,_));},_yj=function(_yk,_yl,_){return C > 19 ? new F(function(){return _yf(new T2(0,_y4,_y2),_yk,_yl,_);}) : (++C,_yf(new T2(0,_y4,_y2),_yk,_yl,_));},_ym=function(_yn){return E(E(_yn).c);},_yo=(function(method, uri, mimeout, responseType, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, uri);xhr.responseType = responseType;if(mimeout != '') {xhr.setRequestHeader('Content-type', mimeout);}xhr.addEventListener('load', function() {if(xhr.status < 400) {cb(null, xhr.response);}else {cb({'type':'http', 'status':xhr.status, 'status-text': xhr.statusText}, null);}});xhr.addEventListener('error', function() {if(xhr.status != 0) {cb({'type':'http', 'status':xhr.status, 'status-text': xhr.statusText}, null);} else {cb({'type':'network'}, null);}});xhr.send(postdata);}),_yp=function(_yq){return E(E(_yq).b);},_yr=function(_ys){return E(E(_ys).b);},_yt=new T(function(){return B(_ga("src/Haste/Ajax.hs:(61,7)-(63,60)|case"));}),_yu=function(_yv){return E(E(_yv).c);},_yw=new T1(1,__Z),_yx=function(_){return nMV(_yw);},_yy=new T0(2),_yz=function(_yA,_yB,_yC){var _yD=function(_yE){var _yF=function(_){var _yG=E(_yB),_yH=rMV(_yG),_yI=E(_yH);if(!_yI._){var _yJ=new T(function(){var _yK=new T(function(){return B(A1(_yE,0));});return _0(_yI.b,new T2(1,new T2(0,_yC,function(_yL){return E(_yK);}),__Z));}),_=wMV(_yG,new T2(0,_yI.a,_yJ));return _yy;}else{var _yM=E(_yI.a);if(!_yM._){var _=wMV(_yG,new T2(0,_yC,__Z));return new T(function(){return B(A1(_yE,0));});}else{var _=wMV(_yG,new T1(1,_yM.b));return new T1(1,new T2(1,new T(function(){return B(A1(_yE,0));}),new T2(1,new T(function(){return B(A2(_yM.a,_yC,_1v));}),__Z)));}}};return new T1(0,_yF);};return C > 19 ? new F(function(){return A2(_yp,_yA,_yD);}) : (++C,A2(_yp,_yA,_yD));},_yN=function(_yO){return E(E(_yO).d);},_yP=function(_yQ,_yR){var _yS=function(_yT){var _yU=function(_){var _yV=E(_yR),_yW=rMV(_yV),_yX=E(_yW);if(!_yX._){var _yY=_yX.a,_yZ=E(_yX.b);if(!_yZ._){var _=wMV(_yV,_yw);return new T(function(){return B(A1(_yT,_yY));});}else{var _z0=E(_yZ.a),_=wMV(_yV,new T2(0,_z0.a,_yZ.b));return new T1(1,new T2(1,new T(function(){return B(A1(_yT,_yY));}),new T2(1,new T(function(){return B(A1(_z0.b,_1v));}),__Z)));}}else{var _z1=new T(function(){var _z2=function(_z3){var _z4=new T(function(){return B(A1(_yT,_z3));});return function(_z5){return E(_z4);};};return _0(_yX.a,new T2(1,_z2,__Z));}),_=wMV(_yV,new T1(1,_z1));return _yy;}};return new T1(0,_yU);};return C > 19 ? new F(function(){return A2(_yp,_yQ,_yS);}) : (++C,A2(_yp,_yQ,_yS));},_z6=function(_z7,_z8,_z9,_za,_zb,_zc){var _zd=_vd(_z7),_ze=new T(function(){return _yp(_z7);}),_zf=new T(function(){return _yr(_zd);}),_zg=_vf(_zd),_zh=new T(function(){return _vh(_z9);}),_zi=new T(function(){var _zj=function(_zk){var _zl=E(_za),_zm=strEq(E(_f),_zl);if(!E(_zm)){var _zn=_zl;}else{var _zn=B(A2(_yu,_z8,0));}return function(_xH){return C > 19 ? new F(function(){return _v5(_xS,_yj,_yo,new T2(1,E(_wS),new T2(1,B(A2(_yN,_z9,0)),new T2(1,_zn,new T2(1,E(_zc),new T2(1,_zk,__Z))))),_xH);}) : (++C,_v5(_xS,_yj,_yo,new T2(1,E(_wS),new T2(1,B(A2(_yN,_z9,0)),new T2(1,_zn,new T2(1,E(_zc),new T2(1,_zk,__Z))))),_xH));};},_zo=function(_zp,_zq){var _zr=E(_za),_zs=strEq(E(_f),_zr);if(!E(_zs)){var _zt=_zr;}else{var _zt=B(A2(_yu,_z8,0));}return function(_xH){return C > 19 ? new F(function(){return _v5(_xS,_yj,_yo,new T2(1,E(_zp),new T2(1,B(A2(_yN,_z9,0)),new T2(1,_zt,new T2(1,E(_zc),new T2(1,_zq,__Z))))),_xH);}) : (++C,_v5(_xS,_yj,_yo,new T2(1,E(_zp),new T2(1,B(A2(_yN,_z9,0)),new T2(1,_zt,new T2(1,E(_zc),new T2(1,_zq,__Z))))),_xH));};},_zu=E(_zb);switch(_zu._){case 0:return _zj("GET");break;case 1:return _zj("DELETE");break;case 2:return _zo(new T(function(){return B(A2(_v3,_vb(_z8),_zu.a));}),"POST");break;default:return _zo(new T(function(){return B(A2(_v3,_vb(_z8),_zu.a));}),"PUT");}}),_zv=function(_zw){var _zx=new T(function(){return B(A1(_ze,new T(function(){return B(_yP(_1E,_zw));})));}),_zy=new T(function(){var _zz=new T(function(){var _zA=function(_zB,_zC,_){var _zD=E(_zC);if(!_zD._){var _zE=E(_zB);if(!_zE._){return E(_yt);}else{return _a(new T(function(){return B(A(_yz,[_1E,_zw,new T1(0,_zE.a),_1v]));}),__Z,_);}}else{var _zF=B(A3(_wN,_zh,_zD.a,_));return _a(new T(function(){return B(A(_yz,[_1E,_zw,new T1(1,_zF),_1v]));}),__Z,_);}};return B(A1(_zi,_zA));});return B(A1(_zf,_zz));});return C > 19 ? new F(function(){return A3(_ym,_zg,_zy,_zx);}) : (++C,A3(_ym,_zg,_zy,_zx));};return C > 19 ? new F(function(){return A3(_1g,_zg,new T(function(){return B(A2(_yr,_zd,_yx));}),_zv);}) : (++C,A3(_1g,_zg,new T(function(){return B(A2(_yr,_zd,_yx));}),_zv));},_zG=new T(function(){return err(new T(function(){return unCStr("AjaxError");}));}),_zH=function(_zI){var _zJ=new T(function(){return _v0(_zI);}),_zK=new T(function(){return toJSStr(unAppCStr("Send client message ",new T(function(){return fromJSStr(E(_zJ));})));}),_zL=new T(function(){return B(_z6(_1E,_v,_v,_f,new T1(2,_zJ),"http://localhost:8080/cgi"));}),_zM=function(_zN){var _zO=function(_){var _zP=_be(E(_zK));return new T(function(){var _zQ=function(_zR){var _zS=E(_zR);if(!_zS._){return E(_zG);}else{var _zT=function(_){var _zU=_u1(E(_zS.a),_),_zV=_zU,_zW=function(_){var _zX=_be(toJSStr(unAppCStr("Got server message ",new T(function(){var _zY=E(_zV);return B(A(_5S,[0,_zY.a,_zY.b,_zY.c,_zY.d,__Z]));}))));return new T(function(){return B(A1(_zN,_zV));});};return new T1(0,_zW);};return new T1(0,_zT);}};return B(A1(_zL,_zQ));});};return new T1(0,_zO);};return _zM;},_zZ=new T(function(){return unAppCStr(") is outside of enumeration\'s range (0,",new T(function(){return _1V(0,2,new T(function(){return unCStr(")");}));}));}),_A0=function(_A1){return err(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return _1V(0,_A1,_zZ);})));},_A2=function(_A3,_){return new T(function(){var _A4=Number(E(_A3)),_A5=jsTrunc(_A4);if(_A5<0){return _A0(_A5);}else{if(_A5>2){return _A0(_A5);}else{return _A5;}}});},_A6=new T3(0,0,0,0),_A7=new T(function(){return jsGetMouseCoords;}),_A8=function(_A9,_){var _Aa=E(_A9);if(!_Aa._){return __Z;}else{var _Ab=_A8(_Aa.b,_);return new T2(1,new T(function(){var _Ac=Number(E(_Aa.a));return jsTrunc(_Ac);}),_Ab);}},_Ad=function(_Ae,_){var _Af=__arr2lst(0,_Ae);return _A8(_Af,_);},_Ag=function(_Ah,_){return new T(function(){var _Ai=Number(E(_Ah));return jsTrunc(_Ai);});},_Aj=new T2(0,_Ag,function(_Ak,_){return _Ad(E(_Ak),_);}),_Al=function(_Am,_){var _An=E(_Am);if(!_An._){return __Z;}else{var _Ao=_Al(_An.b,_);return new T2(1,_An.a,_Ao);}},_Ap=new T(function(){return _wn(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9");}),__Z,__Z));}),_Aq=function(_){return die(_Ap);},_Ar=function(_As,_At,_Au,_){var _Av=__arr2lst(0,_Au),_Aw=_Al(_Av,_),_Ax=E(_Aw);if(!_Ax._){return _Aq(_);}else{var _Ay=E(_Ax.b);if(!_Ay._){return _Aq(_);}else{if(!E(_Ay.b)._){var _Az=B(A3(_wN,_As,_Ax.a,_)),_AA=B(A3(_wN,_At,_Ay.a,_));return new T2(0,_Az,_AA);}else{return _Aq(_);}}}},_AB=function(_AC,_AD,_){if(E(_AC)==7){var _AE=E(_A7)(_AD),_AF=_Ar(_Aj,_Aj,_AE,_),_AG=_AD["deltaX"],_AH=_AD["deltaY"],_AI=_AD["deltaZ"];return new T(function(){return new T3(0,E(_AF),E(__Z),E(new T3(0,_AG,_AH,_AI)));});}else{var _AJ=E(_A7)(_AD),_AK=_Ar(_Aj,_Aj,_AJ,_),_AL=_AD["button"],_AM=__eq(_AL,E(_wS));if(!E(_AM)){var _AN=__isUndef(_AL);if(!E(_AN)){var _AO=_A2(_AL,_);return new T(function(){return new T3(0,E(_AK),E(new T1(1,_AO)),E(_A6));});}else{return new T(function(){return new T3(0,E(_AK),E(__Z),E(_A6));});}}else{return new T(function(){return new T3(0,E(_AK),E(__Z),E(_A6));});}}},_AP=new T2(0,function(_AQ){switch(E(_AQ)){case 0:return "click";case 1:return "dblclick";case 2:return "mousedown";case 3:return "mouseup";case 4:return "mousemove";case 5:return "mouseover";case 6:return "mouseout";default:return "wheel";}},function(_AR,_AS,_){return _AB(_AR,E(_AS),_);}),_AT=function(_AU){return E(_AU);},_AV=function(_AW,_AX,_){var _AY=B(A1(_AW,_)),_AZ=B(A1(_AX,_));return new T(function(){return B(A1(_AY,_AZ));});},_B0=function(_B1,_){return _B1;},_B2=function(_B3,_B4,_){var _B5=B(A1(_B3,_));return C > 19 ? new F(function(){return A1(_B4,_);}) : (++C,A1(_B4,_));},_B6=new T(function(){return E(_wg);}),_B7=function(_B8){return new T6(0,__Z,7,__Z,_B8,__Z,__Z);},_B9=function(_Ba,_){var _Bb=new T(function(){return B(A2(_fn,_B6,new T(function(){return B(A1(_B7,_Ba));})));});return die(_Bb);},_Bc=function(_Bd,_){return _B9(_Bd,_);},_Be=new T2(0,new T5(0,new T5(0,new T2(0,_1o,function(_Bf,_Bg,_){var _Bh=B(A1(_Bg,_));return _Bf;}),_B0,_AV,_B2,function(_Bi,_Bj,_){var _Bk=B(A1(_Bi,_)),_Bl=B(A1(_Bj,_));return _Bk;}),function(_Bm,_Bn,_){var _Bo=B(A1(_Bm,_));return C > 19 ? new F(function(){return A2(_Bn,_Bo,_);}) : (++C,A2(_Bn,_Bo,_));},_B2,_B0,function(_Bp){return C > 19 ? new F(function(){return A1(_Bc,_Bp);}) : (++C,A1(_Bc,_Bp));}),_1C),_Bq=new T2(0,_Be,_B0),_Br=function(_Bs){return E(E(_Bs).d);},_Bt=new T2(0,_1C,function(_Bu,_Bv){return C > 19 ? new F(function(){return A2(_Br,_vf(_Bu),new T1(1,_Bv));}) : (++C,A2(_Br,_vf(_Bu),new T1(1,_Bv)));}),_Bw=(function(t){return document.createElement(t);}),_Bx=function(_){return _Bw("div");},_By=(function(c,p){p.appendChild(c);}),_Bz=(function(e){while(e.firstChild){e.removeChild(e.firstChild);}}),_BA=(function(c,p){p.removeChild(c);}),_BB=new T(function(){return document.body;}),_BC=function(_,_BD){var _BE=E(_BD);if(!_BE._){return 0;}else{var _BF=E(_BE.a),_BG=_Bz(_BF),_BH=_BA(_BF,E(_BB));return _bd(_);}},_BI=(function(id){return document.getElementById(id);}),_BJ=function(_BK,_){var _BL=_BI(toJSStr(E(_BK))),_BM=__eq(_BL,E(_wS));if(!E(_BM)){var _BN=__isUndef(_BL);if(!E(_BN)){return _BC(_,new T1(1,_BL));}else{return _BC(_,__Z);}}else{return _BC(_,__Z);}},_BO=function(_BP,_BQ,_BR){while(1){var _BS=E(_BQ);if(!_BS._){return (E(_BR)._==0)?true:false;}else{var _BT=E(_BR);if(!_BT._){return false;}else{if(!B(A3(_6k,_BP,_BS.a,_BT.a))){return false;}else{_BQ=_BS.b;_BR=_BT.b;continue;}}}}},_BU=function(_BV,_){var _BW=E(_BV);if(!_BW._){return __Z;}else{var _BX=_BU(_BW.b,_);return new T2(1,_BW.a,_BX);}},_BY=new T(function(){return err(new T(function(){return unCStr("Map.!: given key is not an element in the map");}));}),_BZ=function(_C0,_C1){while(1){var _C2=E(_C1);if(!_C2._){switch(_bh(_C0,_C2.b)){case 0:_C1=_C2.d;continue;case 1:return E(_C2.c);default:_C1=_C2.e;continue;}}else{return E(_BY);}}},_C3=function(_C4,_C5){while(1){var _C6=E(_C4);if(!_C6._){return (E(_C5)._==0)?true:false;}else{var _C7=E(_C5);if(!_C7._){return false;}else{if(E(_C6.a)!=E(_C7.a)){return false;}else{_C4=_C6.b;_C5=_C7.b;continue;}}}}},_C8=function(_C9,_Ca,_Cb,_Cc){return (!_C3(_C9,_Cb))?true:(!_hy(_Ca,_Cc))?true:false;},_Cd=function(_Ce,_Cf){var _Cg=E(_Ce),_Ch=E(_Cf);return _C8(_Cg.a,_Cg.b,_Ch.a,_Ch.b);},_Ci=function(_Cj,_Ck,_Cl,_Cm){if(!_C3(_Cj,_Cl)){return false;}else{return _hy(_Ck,_Cm);}},_Cn=function(_Co,_Cp){var _Cq=E(_Co),_Cr=E(_Cp);return _Ci(_Cq.a,_Cq.b,_Cr.a,_Cr.b);},_Cs=function(_Ct){return fromJSStr(E(_Ct));},_Cu=function(_Cv){return E(E(_Cv).a);},_Cw=(function(e,p){return e.hasAttribute(p) ? e.getAttribute(p) : '';}),_Cx=function(_Cy,_Cz,_CA,_CB){var _CC=new T(function(){var _CD=function(_){var _CE=_Cw(B(A2(_Cu,_Cy,_CA)),E(_CB));return new T(function(){return String(_CE);});};return _CD;});return C > 19 ? new F(function(){return A2(_yr,_Cz,_CC);}) : (++C,A2(_yr,_Cz,_CC));},_CF=function(_CG,_CH,_CI,_CJ){var _CK=_vf(_CH),_CL=new T(function(){return _Br(_CK);}),_CM=function(_CN){return C > 19 ? new F(function(){return A1(_CL,new T(function(){return _Cs(_CN);}));}) : (++C,A1(_CL,new T(function(){return _Cs(_CN);})));},_CO=new T(function(){return B(_Cx(_CG,_CH,_CI,new T(function(){return toJSStr(E(_CJ));},1)));});return C > 19 ? new F(function(){return A3(_1g,_CK,_CO,_CM);}) : (++C,A3(_1g,_CK,_CO,_CM));},_CP=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_CQ=function(_CR,_CS,_CT,_CU){var _CV=new T(function(){var _CW=function(_){var _CX=_CP(B(A2(_Cu,_CR,_CT)),E(_CU));return new T(function(){return String(_CX);});};return _CW;});return C > 19 ? new F(function(){return A2(_yr,_CS,_CV);}) : (++C,A2(_yr,_CS,_CV));},_CY=function(_CZ,_D0,_D1,_D2){var _D3=_vf(_D0),_D4=new T(function(){return _Br(_D3);}),_D5=function(_D6){return C > 19 ? new F(function(){return A1(_D4,new T(function(){return _Cs(_D6);}));}) : (++C,A1(_D4,new T(function(){return _Cs(_D6);})));},_D7=new T(function(){return B(_CQ(_CZ,_D0,_D1,new T(function(){return toJSStr(E(_D2));},1)));});return C > 19 ? new F(function(){return A3(_1g,_D3,_D7,_D5);}) : (++C,A3(_1g,_D3,_D7,_D5));},_D8=new T(function(){return unCStr("suggestionList");}),_D9=new T2(0,new T(function(){return unCStr("PrimaEng");}),new T(function(){return unCStr("useS (useCl (simpleCl (usePron he_PP) (complA Romanus_A)))");})),_Da=new T(function(){return _wP(function(_){return nMV(__Z);});}),_Db=(function(e){if(e){e.stopPropagation();}}),_Dc=function(_){var _Dd=rMV(E(_Da)),_De=E(_Dd);if(!_De._){var _Df=_Db(E(_wS));return _bd(_);}else{var _Dg=_Db(E(_De.a));return _bd(_);}},_Dh=new T(function(){return unCStr("lang");}),_Di=new T(function(){return err(_sW);}),_Dj=new T(function(){return err(_sX);}),_Dk=new T(function(){return B(A3(_rE,_s7,0,_sQ));}),_Dl=new T(function(){return unCStr("textContent");}),_Dm=new T(function(){return _wn(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:298:5-16");}),__Z,__Z));}),_Dn=new T(function(){return unCStr("score");}),_Do=function(_Dp,_Dq,_){var _Dr=_Dc(_),_Ds=_BJ(_D8,_),_Dt=B(A(_CF,[_Bt,_Be,_Dp,_Dh,_])),_Du=_Dt,_Dv=_BI(toJSStr(E(_Dn))),_Dw=__eq(_Dv,E(_wS)),_Dx=function(_,_Dy){var _Dz=E(_Dy);if(!_Dz._){return die(_Dm);}else{var _DA=B(A(_CY,[_Bt,_Be,_Dz.a,_Dl,_])),_DB=new T(function(){return B(A2(_zH,new T3(1,new T(function(){var _DC=_sY(_gS(_Dk,_DA));if(!_DC._){return E(_Dj);}else{if(!E(_DC.b)._){return E(_DC.a);}else{return E(_Di);}}}),_D9,new T2(0,_Du,_Dq)),_DD));});return _a(_DB,__Z,_);}};if(!E(_Dw)){var _DE=__isUndef(_Dv);if(!E(_DE)){return _Dx(_,new T1(1,_Dv));}else{return _Dx(_,__Z);}}else{return _Dx(_,__Z);}},_DF=function(_DG,_DH){var _DI=E(_DH);if(!_DI._){return __Z;}else{var _DJ=_DI.a,_DK=E(_DG);return (_DK==1)?new T2(1,_DJ,__Z):new T2(1,_DJ,new T(function(){return _DF(_DK-1|0,_DI.b);}));}},_DL=(function(e,c,x){x?e.classList.add(c):e.classList.remove(c);}),_DM=new T(function(){return unCStr("wordHover");}),_DN=function(_DO,_){while(1){var _DP=E(_DO);if(!_DP._){return 0;}else{var _DQ=_DL(E(_DP.a),toJSStr(E(_DM)),true);_DO=_DP.b;continue;}}},_DR=(function(e,p,v){e.setAttribute(p, v);}),_DS=(function(e,p){e.removeAttribute(p);}),_DT=new T(function(){return unCStr("clickCount");}),_DU=new T(function(){return unCStr("clicked");}),_DV=function(_DW,_){while(1){var _DX=E(_DW);if(!_DX._){return 0;}else{var _DY=E(_DX.a),_DZ=_DR(_DY,toJSStr(E(_DU)),toJSStr(E(_5R))),_E0=_DS(_DY,toJSStr(E(_DT)));_DW=_DX.b;continue;}}},_E1=new T(function(){return _22(new T(function(){return unCStr("head");}));}),_E2=new T(function(){return _E3(__Z);}),_E3=function(_E4){while(1){var _E5=(function(_E6){var _E7=E(_E6);if(!_E7._){return __Z;}else{var _E8=_E7.b,_E9=E(_E7.a);if(_E9==32){var _Ea=E(_E8);if(!_Ea._){return new T2(1,_E9,_E2);}else{if(E(_Ea.a)==38){var _Eb=E(_Ea.b);if(!_Eb._){return new T2(1,_E9,new T(function(){return _E3(_Ea);}));}else{if(E(_Eb.a)==43){var _Ec=E(_Eb.b);if(!_Ec._){return new T2(1,_E9,new T(function(){return _E3(_Ea);}));}else{if(E(_Ec.a)==32){_E4=_Ec.b;return __continue;}else{return new T2(1,_E9,new T(function(){return _E3(_Ea);}));}}}else{return new T2(1,_E9,new T(function(){return _E3(_Ea);}));}}}else{return new T2(1,_E9,new T(function(){return _E3(_Ea);}));}}}else{return new T2(1,_E9,new T(function(){return _E3(_E8);}));}}})(_E4);if(_E5!=__continue){return _E5;}}},_Ed=(function(e){var ch = [];for(e = e.firstChild; e != null; e = e.nextSibling)  {if(e instanceof HTMLElement) {ch.push(e);}}return ch;}),_Ee=function(_Ef,_Eg,_Eh){while(1){var _Ei=E(_Eg);if(!_Ei._){return true;}else{var _Ej=E(_Eh);if(!_Ej._){return false;}else{if(!B(A3(_6k,_Ef,_Ei.a,_Ej.a))){return false;}else{_Eg=_Ei.b;_Eh=_Ej.b;continue;}}}}},_Ek=new T(function(){return unCStr("path");}),_El=new T(function(){return unCStr("\u2205");}),_Em=new T(function(){return unCStr("offsetTop");}),_En=new T(function(){return unCStr("offsetLeft");}),_Eo=new T(function(){return new T1(1,"left");}),_Ep=new T(function(){return new T1(1,"top");}),_Eq=new T(function(){return new T2(0,E(new T1(2,"class")),"menu");}),_Er=new T(function(){return err(_sX);}),_Es=new T(function(){return err(_sW);}),_Et=function(_Eu,_Ev){return C > 19 ? new F(function(){return _Ew(_Ev);}) : (++C,_Ew(_Ev));},_Ex=new T(function(){return unCStr("True");}),_Ey=new T(function(){return unCStr("False");}),_Ew=function(_Ez){var _EA=new T(function(){return B(A1(_Ez,false));}),_EB=new T(function(){return B(A1(_Ez,true));}),_EC=new T(function(){return B(_qD(function(_ED){var _EE=E(_ED);if(_EE._==3){var _EF=_EE.a;return (!_hy(_EF,_Ey))?(!_hy(_EF,_Ex))?new T0(2):E(_EB):E(_EA);}else{return new T0(2);}}));}),_EG=function(_EH){return E(_EC);};return _h2(new T1(1,function(_EI){return C > 19 ? new F(function(){return A2(_pw,_EI,_EG);}) : (++C,A2(_pw,_EI,_EG));}),new T(function(){return new T1(1,_ra(_Et,_Ez));}));},_EJ=new T(function(){return B(_Ew(_sQ));}),_EK=new T(function(){return new T2(0,E(new T1(2,"id")),"suggestionList");}),_EL=new T(function(){return err(_sW);}),_EM=new T(function(){return B(_sh(_se,_sQ));}),_EN=new T(function(){return unCStr("lin");}),_EO=new T(function(){return err(_sW);}),_EP=new T(function(){return err(_sX);}),_EQ=function(_ER,_ES){return C > 19 ? new F(function(){return _sh(_se,_ES);}) : (++C,_sh(_se,_ES));},_ET=function(_EU,_EV){return C > 19 ? new F(function(){return _sh(_EQ,_EV);}) : (++C,_sh(_EQ,_EV));},_EW=new T(function(){return B(_sh(_EQ,_i2));}),_EX=function(_sf){return _gS(_EW,_sf);},_EY=new T(function(){return B(_sh(_se,_i2));}),_EZ=function(_sf){return _gS(_EY,_sf);},_F0=function(_F1,_sf){return _EZ(_sf);},_F2=function(_F3,_F4){return C > 19 ? new F(function(){return _F5(_F4);}) : (++C,_F5(_F4));},_F5=function(_F6){var _F7=new T(function(){return B(_qD(function(_F8){var _F9=E(_F8);if(!_F9._){return C > 19 ? new F(function(){return A1(_F6,_F9.a);}) : (++C,A1(_F6,_F9.a));}else{return new T0(2);}}));}),_Fa=function(_Fb){return E(_F7);};return _h2(new T1(1,function(_Fc){return C > 19 ? new F(function(){return A2(_pw,_Fc,_Fa);}) : (++C,A2(_pw,_Fc,_Fa));}),new T(function(){return new T1(1,_ra(_F2,_F6));}));},_Fd=function(_Fe,_Ff){return C > 19 ? new F(function(){return _F5(_Ff);}) : (++C,_F5(_Ff));},_Fg=function(_Fh,_Fi){return C > 19 ? new F(function(){return _Fj(_Fi);}) : (++C,_Fj(_Fi));},_Fj=function(_Fk){var _Fl=new T(function(){return B(_qD(function(_Fm){var _Fn=E(_Fm);if(_Fn._==1){return C > 19 ? new F(function(){return A1(_Fk,_Fn.a);}) : (++C,A1(_Fk,_Fn.a));}else{return new T0(2);}}));}),_Fo=function(_Fp){return E(_Fl);};return _h2(_h2(new T1(1,function(_Fq){return C > 19 ? new F(function(){return A2(_pw,_Fq,_Fo);}) : (++C,A2(_pw,_Fq,_Fo));}),new T(function(){return B(_sh(_Fd,_Fk));})),new T(function(){return new T1(1,_ra(_Fg,_Fk));}));},_Fr=function(_Fs,_Ft){return C > 19 ? new F(function(){return _Fj(_Ft);}) : (++C,_Fj(_Ft));},_Fu=function(_Fv,_Fw){return C > 19 ? new F(function(){return _sh(_Fr,_Fw);}) : (++C,_sh(_Fr,_Fw));},_Fx=new T(function(){return B(_sh(_Fr,_i2));}),_Fy=function(_sf){return _gS(_Fx,_sf);},_Fz=new T(function(){return B(_Fj(_i2));}),_FA=function(_sf){return _gS(_Fz,_sf);},_FB=function(_FC,_sf){return _FA(_sf);},_FD=new T(function(){return unCStr(",");}),_FE=function(_FF){return E(E(_FF).c);},_FG=function(_FH,_FI,_FJ){var _FK=new T(function(){return _FE(_FI);}),_FL=new T(function(){return B(A2(_FE,_FH,_FJ));}),_FM=function(_FN){var _FO=function(_FP){var _FQ=new T(function(){var _FR=new T(function(){return B(A2(_FK,_FJ,function(_FS){return C > 19 ? new F(function(){return A1(_FN,new T2(0,_FP,_FS));}) : (++C,A1(_FN,new T2(0,_FP,_FS)));}));});return B(_qD(function(_FT){var _FU=E(_FT);return (_FU._==2)?(!_hy(_FU.a,_FD))?new T0(2):E(_FR):new T0(2);}));}),_FV=function(_FW){return E(_FQ);};return new T1(1,function(_FX){return C > 19 ? new F(function(){return A2(_pw,_FX,_FV);}) : (++C,A2(_pw,_FX,_FV));});};return C > 19 ? new F(function(){return A1(_FL,_FO);}) : (++C,A1(_FL,_FO));};return _FM;},_FY=function(_FZ,_G0,_G1){var _G2=function(_sf){return _FG(_FZ,_G0,_sf);},_G3=function(_G4,_G5){return C > 19 ? new F(function(){return _G6(_G5);}) : (++C,_G6(_G5));},_G6=function(_G7){return _h2(new T1(1,_ra(_G2,_G7)),new T(function(){return new T1(1,_ra(_G3,_G7));}));};return C > 19 ? new F(function(){return _G6(_G1);}) : (++C,_G6(_G1));},_G8=new T(function(){return B(_sh(function(_G9,_Ga){return C > 19 ? new F(function(){return _FY(new T4(0,_F0,_EX,_EQ,_ET),new T4(0,_FB,_Fy,_Fr,_Fu),_Ga);}) : (++C,_FY(new T4(0,_F0,_EX,_EQ,_ET),new T4(0,_FB,_Fy,_Fr,_Fu),_Ga));},_sQ));}),_Gb=new T(function(){return err(_sX);}),_Gc=new T(function(){return _wn(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:202:5-15");}),__Z,__Z));}),_Gd=new T(function(){return unCStr("px");}),_Ge=new T(function(){return unCStr("parentid");}),_Gf=new T(function(){return unCStr("menuHover");}),_Gg=(function(e,c) {e.classList.toggle(c);}),_Gh=function(_Gi,_){var _Gj=_Gg(_Gi,toJSStr(E(_Gf)));return _bd(_);},_Gk=new T(function(){return unCStr("div");}),_Gl=(function(s){return document.createTextNode(s);}),_Gm=function(_Gn){return E(E(_Gn).a);},_Go=function(_Gp){return E(E(_Gp).b);},_Gq=function(_Gr){return E(E(_Gr).a);},_Gs=function(_Gt){return E(E(_Gt).b);},_Gu=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_Gv=function(_Gw,_Gx,_Gy,_Gz,_GA,_GB){var _GC=_Gm(_Gw),_GD=_vf(_GC),_GE=new T(function(){return _yr(_GC);}),_GF=new T(function(){return _Br(_GD);}),_GG=new T(function(){return B(A1(_Gx,_Gz));}),_GH=new T(function(){return B(A2(_Gq,_Gy,_GA));}),_GI=function(_GJ){return C > 19 ? new F(function(){return A1(_GF,new T3(0,_GH,_GG,_GJ));}) : (++C,A1(_GF,new T3(0,_GH,_GG,_GJ)));},_GK=function(_GL){var _GM=new T(function(){var _GN=new T(function(){var _GO=__createJSFunc(2,function(_GP,_){var _GQ=B(A2(E(_GL),_GP,_));return _wS;}),_GR=_GO;return function(_){return _Gu(E(_GG),E(_GH),_GR);};});return B(A1(_GE,_GN));});return C > 19 ? new F(function(){return A3(_1g,_GD,_GM,_GI);}) : (++C,A3(_1g,_GD,_GM,_GI));},_GS=new T(function(){var _GT=new T(function(){return _yr(_GC);}),_GU=function(_GV){var _GW=new T(function(){return B(A1(_GT,function(_){var _=wMV(E(_Da),new T1(1,_GV));return C > 19 ? new F(function(){return A(_Go,[_Gy,_GA,_GV,_]);}) : (++C,A(_Go,[_Gy,_GA,_GV,_]));}));});return C > 19 ? new F(function(){return A3(_1g,_GD,_GW,_GB);}) : (++C,A3(_1g,_GD,_GW,_GB));};return B(A2(_Gs,_Gw,_GU));});return C > 19 ? new F(function(){return A3(_1g,_GD,_GS,_GK);}) : (++C,A3(_1g,_GD,_GS,_GK));},_GX=function(_GY,_GZ,_H0,_){var _H1=_Gl(toJSStr(E(_GZ))),_H2=_Bw(toJSStr(E(_Gk))),_H3=_H2,_H4=B(A(_Gv,[_Bq,_AT,_AP,_H3,5,function(_H5,_){return _Gh(_H3,_);},_])),_H6=B(A(_Gv,[_Bq,_AT,_AP,_H3,6,function(_H7,_){return _Gh(_H3,_);},_])),_H8=B(A(_Gv,[_Bq,_AT,_AP,_H3,0,_H0,_])),_H9=_By(_H1,_H3),_Ha=_By(_H3,E(_GY));return 0;},_Hb=(function(e,p,v){e.style[p] = v;}),_Hc=(function(e,p,v){e[p] = v;}),_Hd=function(_He,_Hf,_Hg,_Hh){var _Hi=new T(function(){return B(A2(_Cu,_He,_Hg));}),_Hj=function(_Hk,_){var _Hl=E(_Hk);if(!_Hl._){return 0;}else{var _Hm=E(_Hi),_Hn=_By(E(_Hl.a),_Hm),_Ho=function(_Hp,_){while(1){var _Hq=E(_Hp);if(!_Hq._){return 0;}else{var _Hr=_By(E(_Hq.a),_Hm);_Hp=_Hq.b;continue;}}};return _Ho(_Hl.b,_);}},_Hs=function(_Ht,_){while(1){var _Hu=(function(_Hv,_){var _Hw=E(_Hv);if(!_Hw._){return 0;}else{var _Hx=_Hw.b,_Hy=E(_Hw.a);if(!_Hy._){var _Hz=_Hy.b,_HA=E(_Hy.a);switch(_HA._){case 0:var _HB=E(_Hi),_HC=_Hc(_HB,_HA.a,_Hz),_HD=function(_HE,_){while(1){var _HF=E(_HE);if(!_HF._){return 0;}else{var _HG=_HF.b,_HH=E(_HF.a);if(!_HH._){var _HI=_HH.b,_HJ=E(_HH.a);switch(_HJ._){case 0:var _HK=_Hc(_HB,_HJ.a,_HI);_HE=_HG;continue;case 1:var _HL=_Hb(_HB,_HJ.a,_HI);_HE=_HG;continue;default:var _HM=_DR(_HB,_HJ.a,_HI);_HE=_HG;continue;}}else{var _HN=_Hj(_HH.a,_);_HE=_HG;continue;}}}};return _HD(_Hx,_);case 1:var _HO=E(_Hi),_HP=_Hb(_HO,_HA.a,_Hz),_HQ=function(_HR,_){while(1){var _HS=E(_HR);if(!_HS._){return 0;}else{var _HT=_HS.b,_HU=E(_HS.a);if(!_HU._){var _HV=_HU.b,_HW=E(_HU.a);switch(_HW._){case 0:var _HX=_Hc(_HO,_HW.a,_HV);_HR=_HT;continue;case 1:var _HY=_Hb(_HO,_HW.a,_HV);_HR=_HT;continue;default:var _HZ=_DR(_HO,_HW.a,_HV);_HR=_HT;continue;}}else{var _I0=_Hj(_HU.a,_);_HR=_HT;continue;}}}};return _HQ(_Hx,_);default:var _I1=E(_Hi),_I2=_DR(_I1,_HA.a,_Hz),_I3=function(_I4,_){while(1){var _I5=E(_I4);if(!_I5._){return 0;}else{var _I6=_I5.b,_I7=E(_I5.a);if(!_I7._){var _I8=_I7.b,_I9=E(_I7.a);switch(_I9._){case 0:var _Ia=_Hc(_I1,_I9.a,_I8);_I4=_I6;continue;case 1:var _Ib=_Hb(_I1,_I9.a,_I8);_I4=_I6;continue;default:var _Ic=_DR(_I1,_I9.a,_I8);_I4=_I6;continue;}}else{var _Id=_Hj(_I7.a,_);_I4=_I6;continue;}}}};return _I3(_Hx,_);}}else{var _Ie=_Hj(_Hy.a,_);_Ht=_Hx;return __continue;}}})(_Ht,_);if(_Hu!=__continue){return _Hu;}}};return C > 19 ? new F(function(){return A2(_yr,_Hf,function(_){return _Hs(_Hh,_);});}) : (++C,A2(_yr,_Hf,function(_){return _Hs(_Hh,_);}));},_If=function(_Ig,_Ih,_Ii,_Ij){var _Ik=_vf(_Ih),_Il=function(_Im){return C > 19 ? new F(function(){return A3(_ym,_Ik,new T(function(){return B(_Hd(_Ig,_Ih,_Im,_Ij));}),new T(function(){return B(A2(_Br,_Ik,_Im));}));}) : (++C,A3(_ym,_Ik,new T(function(){return B(_Hd(_Ig,_Ih,_Im,_Ij));}),new T(function(){return B(A2(_Br,_Ik,_Im));})));};return C > 19 ? new F(function(){return A3(_1g,_Ik,_Ii,_Il);}) : (++C,A3(_1g,_Ik,_Ii,_Il));},_In=function(_Io,_Ip,_Iq,_){var _Ir=_Dc(_),_Is=B(A(_CY,[_Bt,_Be,_Io,_En,_])),_It=_Is,_Iu=B(A(_CY,[_Bt,_Be,_Io,_Em,_])),_Iv=_Iu,_Iw=_BJ(_D8,_),_Ix=B(A(_CF,[_Bt,_Be,_Io,_DU,_])),_Iy=_sY(_gS(_EJ,_Ix));if(!_Iy._){return E(_Er);}else{if(!E(_Iy.b)._){var _Iz=function(_,_IA){var _IB=B(A(_CF,[_Bt,_Be,_Io,_Ge,_])),_IC=_BI(toJSStr(E(_IB))),_ID=__eq(_IC,E(_wS)),_IE=function(_,_IF){var _IG=E(_IF);if(!_IG._){return die(_Gc);}else{var _IH=E(_IG.a),_II=_Ed(_IH),_IJ=__arr2lst(0,_II),_IK=_BU(_IJ,_),_IL=_IK,_IM=_DV(_IL,_),_IN=E(_Io),_IO=_DR(_IN,toJSStr(E(_DU)),toJSStr(E(_5Q))),_IP=E(_IA),_IQ=_DR(_IN,toJSStr(E(_DT)),toJSStr(_1V(0,_IP+1|0,__Z))),_IR=B(A(_CF,[_Bt,_Be,_IN,_Ek,_])),_IS=B(A(_CF,[_Bt,_Be,_IH,_EN,_])),_IT=_IS,_IU=new T(function(){return E(E(_Iq).a);}),_IV=B(A(_If,[_Bt,_Be,_Bx,new T2(1,_EK,new T2(1,_Eq,new T2(1,new T(function(){var _IW=_sY(_gS(_Dk,_Iv));if(!_IW._){return E(_Dj);}else{if(!E(_IW.b)._){return new T2(0,E(_Ep),toJSStr(_0(_1V(0,E(E(_IU).b)+E(_IW.a)|0,__Z),_Gd)));}else{return E(_Di);}}}),new T2(1,new T(function(){var _IX=_sY(_gS(_Dk,_It));if(!_IX._){return E(_Dj);}else{if(!E(_IX.b)._){return new T2(0,E(_Eo),toJSStr(_0(_1V(0,E(E(_IU).a)+E(_IX.a)|0,__Z),_Gd)));}else{return E(_Di);}}}),__Z)))),_])),_IY=_IV,_IZ=_sY(_gS(_EM,_IR));if(!_IZ._){return E(_Gb);}else{var _J0=_IZ.a;if(!E(_IZ.b)._){var _J1=_k3(_J0,0)-_IP|0;if(0>=_J1){var _J2=__Z;}else{var _J2=_DF(_J1,_J0);}var _J3=_BZ(_J2,_Ip);if(!_J3._){return E(_E1);}else{var _J4=new T(function(){var _J5=_sY(_gS(_G8,_IT));if(!_J5._){return E(_EP);}else{if(!E(_J5.b)._){return E(_J5.a);}else{return E(_EO);}}}),_J6=function(_J7){while(1){var _J8=(function(_J9){var _Ja=E(_J9);if(!_Ja._){return __Z;}else{var _Jb=_Ja.b,_Jc=E(_Ja.a);if(!_Ee(_7W,_J2,_Jc.a)){_J7=_Jb;return __continue;}else{var _Jd=new T(function(){return _0(_Jc.b,new T(function(){return _J6(_Jb);},1));});return new T2(1,32,_Jd);}}})(_J7);if(_J8!=__continue){return _J8;}}},_Je=function(_Jf,_){while(1){var _Jg=(function(_Jh,_){var _Ji=E(_Jh);if(!_Ji._){return 0;}else{var _Jj=_Ji.b,_Jk=E(_Ji.a),_Jl=_Jk.b;if(!_BO(new T2(0,_Cn,_Cd),_Jl,_J4)){var _Jm=function(_Jn,_){return C > 19 ? new F(function(){return _Do(_IH,_Jk.c,_);}) : (++C,_Do(_IH,_Jk.c,_));},_Jo=_J6(_Jl);if(!_Jo._){var _Jp=E(_E2);if(!_Jp._){var _Jq=_GX(_IY,_El,_Jm,_);_Jf=_Jj;return __continue;}else{var _Jr=_GX(_IY,_Jp,_Jm,_);_Jf=_Jj;return __continue;}}else{var _Js=_E3(_Jo.b);if(!_Js._){var _Jt=_GX(_IY,_El,_Jm,_);_Jf=_Jj;return __continue;}else{var _Ju=_GX(_IY,_Js,_Jm,_);_Jf=_Jj;return __continue;}}}else{_Jf=_Jj;return __continue;}}})(_Jf,_);if(_Jg!=__continue){return _Jg;}}},_Jv=_Je(_J3.a,_),_Jw=_By(E(_IY),E(_BB)),_Jx=function(_Jy,_){var _Jz=E(_Jy);if(!_Jz._){return __Z;}else{var _JA=_Jz.a,_JB=B(A(_CF,[_Bt,_Be,_JA,_Ek,_])),_JC=_Jx(_Jz.b,_);return new T(function(){if(!_Ee(_7W,_J2,new T(function(){var _JD=_sY(_gS(_EM,_JB));if(!_JD._){return E(_Gb);}else{if(!E(_JD.b)._){return E(_JD.a);}else{return E(_EL);}}},1))){return E(_JC);}else{return new T2(1,_JA,_JC);}});}},_JE=_Jx(_IL,_),_JF=_DN(_JE,_);return 0;}}else{return E(_EL);}}}};if(!E(_ID)){var _JG=__isUndef(_IC);if(!E(_JG)){return _IE(_,new T1(1,_IC));}else{return _IE(_,__Z);}}else{return _IE(_,__Z);}};if(!E(_Iy.a)){return _Iz(_,0);}else{var _JH=B(A(_CF,[_Bt,_Be,_Io,_DT,_]));return _Iz(_,new T(function(){var _JI=_sY(_gS(_Dk,_JH));if(!_JI._){return E(_Dj);}else{if(!E(_JI.b)._){return E(_JI.a);}else{return E(_Di);}}},1));}}else{return E(_Es);}}},_JJ=function(_JK,_JL){return new T2(0,E(_JK),toJSStr(E(_JL)));},_JM=function(_){return _Bw("span");},_JN=new T(function(){return B(_If(_Bt,_Be,function(_){return _Bw("span");},new T2(1,new T(function(){return new T2(0,E(new T1(2,"class")),"path");}),__Z)));}),_JO=new T(function(){return new T1(2,"parentId");}),_JP=new T(function(){return new T1(2,"path");}),_JQ=new T(function(){return new T2(0,E(new T1(2,"class")),"word");}),_JR=new T(function(){return new T2(0,E(new T1(2,"class")),"gap");}),_JS=new T(function(){return unCStr("id");}),_JT=new T(function(){return unCStr(" ");}),_JU=new T2(1,new T(function(){return new T2(0,E(new T1(2,"clicked")),toJSStr(E(_5R)));}),__Z),_JV=function(_JW,_){var _JX=_Gg(_JW,toJSStr(E(_DM)));return _bd(_);},_JY=function(_JZ,_K0,_){return _JV(E(_JZ),_);},_K1=function(_K2,_K3,_K4,_K5,_K6,_K7,_K8,_){var _K9=B(A(_CF,[_Bt,_Be,_K2,_JS,_])),_Ka=_K9,_Kb=function(_){var _Kc=B(A(_If,[_Bt,_Be,_JM,new T2(1,_JQ,new T2(1,new T(function(){return new T2(0,E(_JP),toJSStr(_3p(_3A,_K3,__Z)));}),new T2(1,new T(function(){return _JJ(_JO,_Ka);}),_JU))),_])),_Kd=_Kc,_Ke=_Gl(toJSStr(E(_K4))),_Kf=B(A(_Gv,[_Bq,_AT,_AP,_Kd,5,function(_Kg,_){return _JY(_Kd,_Kg,_);},_])),_Kh=B(A(_Gv,[_Bq,_AT,_AP,_Kd,6,function(_Kg,_){return _JY(_Kd,_Kg,_);},_])),_Ki=E(_Kd),_Kj=_By(_Ke,_Ki),_Kk=E(_K2),_Kl=_By(_Ki,_Kk),_Km=function(_){if(!E(_K6)){return 0;}else{var _Kn=B(A1(_JN,_)),_Ko=_Gl(toJSStr(_3p(_3A,_K3,__Z))),_Kp=E(_Kn),_Kq=_By(_Ko,_Kp),_Kr=_By(_Kp,_Kk);return _bd(_);}};if(!E(_K8)){return _Km(_);}else{var _Ks=B(A(_Gv,[_Bq,_AT,_AP,_Ki,0,function(_Kt,_){return C > 19 ? new F(function(){return _In(_Ki,E(_K5).a,_Kt,_);}) : (++C,_In(_Ki,E(_K5).a,_Kt,_));},_]));return _Km(_);}};if(!E(_K7)){return _Kb(_);}else{var _Ku=B(A(_If,[_Bt,_Be,_JM,new T2(1,_JR,new T2(1,new T(function(){return new T2(0,E(_JP),toJSStr(_3p(_3A,_K3,__Z)));}),new T2(1,new T(function(){return _JJ(_JO,_Ka);}),_JU))),_])),_Kv=_Ku,_Kw=_Gl(toJSStr(E(_JT))),_Kx=B(A(_Gv,[_Bq,_AT,_AP,_Kv,5,function(_Kg,_){return _JY(_Kv,_Kg,_);},_])),_Ky=B(A(_Gv,[_Bq,_AT,_AP,_Kv,6,function(_Kg,_){return _JY(_Kv,_Kg,_);},_])),_Kz=E(_Kv),_KA=_By(_Kw,_Kz),_KB=_By(_Kz,E(_K2));if(!E(_K8)){return _Kb(_);}else{var _KC=B(A(_Gv,[_Bq,_AT,_AP,_Kz,0,function(_KD,_){return C > 19 ? new F(function(){return _In(_Kz,E(_K5).a,_KD,_);}) : (++C,_In(_Kz,E(_K5).a,_KD,_));},_]));return _Kb(_);}}},_KE=(function(e,c) {return e.classList.contains(c);}),_KF=new T(function(){return unCStr("debug");}),_KG=function(_KH,_KI){var _KJ=E(_KH),_KK=new T(function(){return B(A3(_25,_1M,new T2(1,function(_KL){return _3D(_KJ.a,_KL);},new T2(1,function(_KM){return _3m(_KJ.b,_KM);},__Z)),new T2(1,41,_KI)));});return new T2(1,40,_KK);},_KN=new T(function(){return _wn(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:69:5-23");}),__Z,__Z));}),_KO=new T(function(){return unCStr("exampleTree");}),_KP=function(_KQ,_KR,_KS,_){var _KT=_BI(toJSStr(E(_KO))),_KU=__eq(_KT,E(_wS)),_KV=function(_,_KW){var _KX=E(_KW);if(!_KX._){return die(_KN);}else{var _KY=E(_KX.a),_KZ=_Bz(_KY),_L0=_KE(_KY,toJSStr(E(_KF))),_L1=_L0,_L2=_DR(_KY,toJSStr(E(_EN)),toJSStr(_3p(_KG,_KR,__Z))),_L3=_DR(_KY,toJSStr(E(_Dh)),toJSStr(E(_KQ))),_L4=function(_L5,_){while(1){var _L6=E(_L5);if(!_L6._){return 0;}else{var _L7=E(_L6.a),_L8=B(_K1(_KY,_L7.a,_L7.b,_KS,_L1,false,false,_));_L5=_L6.b;continue;}}},_L9=_L4(_KR,_);return 0;}};if(!E(_KU)){var _La=__isUndef(_KT);if(!E(_La)){return _KV(_,new T1(1,_KT));}else{return _KV(_,__Z);}}else{return _KV(_,__Z);}},_Lb=new T(function(){return _wn(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:86:5-24");}),__Z,__Z));}),_Lc=new T(function(){return unCStr("exerciseTree");}),_Ld=function(_Le,_Lf,_Lg,_){var _Lh=_BI(toJSStr(E(_Lc))),_Li=__eq(_Lh,E(_wS)),_Lj=function(_,_Lk){var _Ll=E(_Lk);if(!_Ll._){return die(_Lb);}else{var _Lm=E(_Ll.a),_Ln=_Bz(_Lm),_Lo=_KE(_Lm,toJSStr(E(_KF))),_Lp=_Lo,_Lq=_DR(_Lm,toJSStr(E(_EN)),toJSStr(_3p(_KG,_Lf,__Z))),_Lr=_DR(_Lm,toJSStr(E(_Dh)),toJSStr(E(_Le))),_Ls=function(_Lt,_){while(1){var _Lu=E(_Lt);if(!_Lu._){return 0;}else{var _Lv=E(_Lu.a),_Lw=B(_K1(_Lm,_Lv.a,_Lv.b,_Lg,_Lp,true,true,_));_Lt=_Lu.b;continue;}}},_Lx=_Ls(_Lf,_);return 0;}};if(!E(_Li)){var _Ly=__isUndef(_Lh);if(!E(_Ly)){return _Lj(_,new T1(1,_Lh));}else{return _Lj(_,__Z);}}else{return _Lj(_,__Z);}},_Lz=(function(t,f){return window.setInterval(f,t);}),_LA=(function(t,f){return window.setTimeout(f,t);}),_LB=function(_LC,_LD,_LE){var _LF=_Gm(_LC),_LG=new T(function(){return _yr(_LF);}),_LH=function(_LI){var _LJ=function(_){var _LK=E(_LD);if(!_LK._){var _LL=B(A1(_LI,0)),_LM=__createJSFunc(0,function(_){var _LN=B(A1(_LL,_));return _wS;}),_LO=_LA(_LK.a,_LM);return new T(function(){var _LP=Number(_LO),_LQ=jsTrunc(_LP);return new T2(0,_LQ,_LK);});}else{var _LR=B(A1(_LI,0)),_LS=__createJSFunc(0,function(_){var _LT=B(A1(_LR,_));return _wS;}),_LU=_Lz(_LK.a,_LS);return new T(function(){var _LV=Number(_LU),_LW=jsTrunc(_LV);return new T2(0,_LW,_LK);});}};return C > 19 ? new F(function(){return A1(_LG,_LJ);}) : (++C,A1(_LG,_LJ));},_LX=new T(function(){return B(A2(_Gs,_LC,function(_LY){return E(_LE);}));});return C > 19 ? new F(function(){return A3(_1g,_vf(_LF),_LX,_LH);}) : (++C,A3(_1g,_vf(_LF),_LX,_LH));},_LZ=function(_M0,_M1){return function(_){var _M2=nMV(new T1(1,__Z)),_M3=_M2,_M4=function(_){var _M5=function(_){return _a(new T(function(){return B(A(_yz,[_1E,_M3,0,_1v]));}),__Z,_);},_M6=B(A(_LB,[_Bq,new T(function(){return new T1(0,E(_M0));}),_M5,_]));return new T(function(){return B(A3(_yP,_1E,_M3,_M1));});};return new T1(0,_M4);};},_M7=new T(function(){return alert;}),_M8=new T(function(){return unCStr("won");}),_M9=new T(function(){return _wn(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:54:5-16");}),__Z,__Z));}),_Ma=new T(function(){return unCStr(" Clicks");}),_Mb=function(_Mc,_Md,_){var _Me=new T(function(){var _Mf=new T(function(){return unAppCStr(" and Success ",new T(function(){if(!E(_Md)){return E(_5R);}else{return E(_5Q);}}));},1);return _0(_1V(0,E(_Mc),__Z),_Mf);}),_Mg=_be(toJSStr(unAppCStr("Score ",_Me))),_Mh=_BI(toJSStr(E(_Dn))),_Mi=__eq(_Mh,E(_wS)),_Mj=function(_,_Mk){var _Ml=E(_Mk);if(!_Ml._){return die(_M9);}else{var _Mm=E(_Ml.a),_Mn=_Bz(_Mm),_Mo=E(_Mc),_Mp=_Gl(toJSStr(_1V(0,_Mo,__Z))),_Mq=E(_Md),_Mr=_DL(_Mm,toJSStr(E(_M8)),_Mq);if(!_Mq){var _Ms=_By(_Mp,_Mm);return _bd(_);}else{var _Mt=new T(function(){var _Mu=function(_){var _Mv=E(_M7)(toJSStr(unAppCStr("Congratulations! You won after ",new T(function(){return _0(_1V(0,_Mo,__Z),_Ma);}))));return _yy;};return new T1(0,_LZ(200,function(_Mw){return E(new T1(0,_Mu));}));}),_Mx=_a(_Mt,__Z,_),_My=_By(_Mp,_Mm);return _bd(_);}}};if(!E(_Mi)){var _Mz=__isUndef(_Mh);if(!E(_Mz)){return _Mj(_,new T1(1,_Mh));}else{return _Mj(_,__Z);}}else{return _Mj(_,__Z);}},_MA=new T(function(){return unCStr("laetus");}),_MB=new T2(1,0,__Z),_MC=new T(function(){return unCStr("est");}),_MD=new T(function(){return unCStr("Augustus");}),_ME=new T(function(){return unCStr("menuList");}),_MF=new T(function(){return unCStr("Reset");}),_MG=new T(function(){return unCStr("Toggle Debug");}),_MH=new T(function(){return new T2(0,E(new T1(2,"id")),"menuList");}),_MI=new T(function(){return _wn(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:283:87-93");}),__Z,__Z));}),_MJ=new T(function(){return _wn(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:283:51-57");}),__Z,__Z));}),_MK=function(_ML,_MM,_){var _MN=new T(function(){return E(E(E(_MM).d).a);}),_MO=new T(function(){return E(E(E(_MM).d).d);}),_MP=_Dc(_),_MQ=B(A(_CY,[_Bt,_Be,_ML,_En,_])),_MR=B(A(_CY,[_Bt,_Be,_ML,_Em,_])),_MS=_BJ(_ME,_),_MT=B(A(_If,[_Bt,_Be,_Bx,new T2(1,_MH,new T2(1,_Eq,new T2(1,new T(function(){return new T2(0,E(_Ep),toJSStr(_0(_MR,_Gd)));}),new T2(1,new T(function(){var _MU=_sY(_gS(_Dk,_MQ));if(!_MU._){return E(_Dj);}else{if(!E(_MU.b)._){return new T2(0,E(_Eo),toJSStr(_0(_1V(0,E(_MU.a)-200|0,__Z),_Gd)));}else{return E(_Di);}}}),__Z)))),_])),_MV=new T(function(){return E(E(E(_MM).d).c);}),_MW=new T(function(){return E(E(E(_MM).c).d);}),_MX=new T(function(){return E(E(E(_MM).c).c);}),_MY=new T(function(){return E(E(E(_MM).c).a);}),_MZ=function(_N0,_){var _N1=_BI(toJSStr(E(_KO))),_N2=E(_wS),_N3=__eq(_N1,_N2),_N4=function(_,_N5){var _N6=E(_N5);if(!_N6._){return die(_MJ);}else{var _N7=_BI(toJSStr(E(_Lc))),_N8=__eq(_N7,_N2),_N9=function(_,_Na){var _Nb=E(_Na);if(!_Nb._){return die(_MI);}else{var _Nc=toJSStr(E(_KF)),_Nd=_Gg(E(_N6.a),_Nc),_Ne=_Gg(E(_Nb.a),_Nc),_Nf=_Ld(_MN,_MV,_MO,_);return _KP(_MY,_MX,_MW,_);}};if(!E(_N8)){var _Ng=__isUndef(_N7);if(!E(_Ng)){return C > 19 ? new F(function(){return _N9(_,new T1(1,_N7));}) : (++C,_N9(_,new T1(1,_N7)));}else{return C > 19 ? new F(function(){return _N9(_,__Z);}) : (++C,_N9(_,__Z));}}else{return C > 19 ? new F(function(){return _N9(_,__Z);}) : (++C,_N9(_,__Z));}}};if(!E(_N3)){var _Nh=__isUndef(_N1);if(!E(_Nh)){return C > 19 ? new F(function(){return _N4(_,new T1(1,_N1));}) : (++C,_N4(_,new T1(1,_N1)));}else{return C > 19 ? new F(function(){return _N4(_,__Z);}) : (++C,_N4(_,__Z));}}else{return C > 19 ? new F(function(){return _N4(_,__Z);}) : (++C,_N4(_,__Z));}},_Ni=_GX(_MT,_MG,_MZ,_),_Nj=_GX(_MT,_MF,function(_Nk,_){var _Nl=_Ld(_MN,new T2(1,new T2(0,new T2(1,0,new T2(1,0,new T2(1,0,_MB))),_MD),new T2(1,new T2(0,new T2(1,0,new T2(1,0,new T2(1,1,_MB))),_MA),new T2(1,new T2(0,new T2(1,0,new T2(1,0,new T2(1,1,__Z))),_MC),__Z))),_MO,_);return _Mb(0,false,_);},_),_Nm=_By(E(_MT),E(_BB));return 0;},_Nn=new T(function(){return unCStr("clickcount");}),_No=function(_Np,_){while(1){var _Nq=E(_Np);if(!_Nq._){return 0;}else{var _Nr=_DS(E(_Nq.a),toJSStr(E(_Nn)));_Np=_Nq.b;continue;}}},_Ns=function(_Nt,_){while(1){var _Nu=E(_Nt);if(!_Nu._){return 0;}else{var _Nv=_DR(E(_Nu.a),toJSStr(E(_DU)),toJSStr(E(_5R)));_Nt=_Nu.b;continue;}}},_Nw=function(_Nx,_){while(1){var _Ny=E(_Nx);if(!_Ny._){return 0;}else{var _Nz=_DL(E(_Ny.a),toJSStr(E(_DM)),false);_Nx=_Ny.b;continue;}}},_NA=new T(function(){return _wn(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:160:5-15");}),__Z,__Z));}),_NB=function(_,_NC){var _ND=E(_NC);if(!_ND._){return die(_NA);}else{var _NE=_Ed(E(_ND.a)),_NF=__arr2lst(0,_NE),_NG=_BU(_NF,_),_NH=_Nw(_NG,_),_NI=_Ns(_NG,_);return _No(_NG,_);}},_NJ=function(_){var _NK=_BJ(_D8,_),_NL=_BJ(_ME,_),_NM=_BI("exerciseTree"),_NN=__eq(_NM,E(_wS));if(!E(_NN)){var _NO=__isUndef(_NM);if(!E(_NO)){return _NB(_,new T1(1,_NM));}else{return _NB(_,__Z);}}else{return _NB(_,__Z);}},_NP=new T(function(){return B(_Gv(_Bq,_AT,_AP,_BB,0,function(_NQ,_){return _NJ(_);}));}),_NR=new T(function(){return _wn(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at Main.hs:40:5-13");}),__Z,__Z));}),_NS=new T(function(){return unCStr("menuButton");}),_NT=function(_NU){return E(E(_NU).b);},_NV=function(_NW){return E(E(_NW).a);},_NX=function(_NY,_){var _NZ=B(A1(_NP,_)),_O0=_BI(toJSStr(E(_NS))),_O1=__eq(_O0,E(_wS)),_O2=function(_,_O3){var _O4=E(_O3);if(!_O4._){return die(_NR);}else{var _O5=_O4.a,_O6=B(A(_Gv,[_Bq,_AT,_AP,_O5,0,function(_O7,_){return _MK(_O5,_NY,_);},_])),_O8=_KP(new T(function(){return E(E(E(_NY).c).a);},1),new T(function(){return E(E(E(_NY).c).c);}),new T(function(){return E(E(E(_NY).c).d);}),_),_O9=_Ld(new T(function(){return E(E(E(_NY).d).a);},1),new T(function(){return E(E(E(_NY).d).c);}),new T(function(){return E(E(E(_NY).d).d);}),_),_Oa=_Mb(new T(function(){return _NT(_NY);}),new T(function(){return _NV(_NY);}),_);return 0;}};if(!E(_O1)){var _Ob=__isUndef(_O0);if(!E(_Ob)){return _O2(_,new T1(1,_O0));}else{return _O2(_,__Z);}}else{return _O2(_,__Z);}},_DD=function(_Oc){return new T1(0,function(_){var _Od=_NX(_Oc,_);return _yy;});},_Oe=new T(function(){return B(A2(_zH,new T3(1,-1,_D9,new T2(0,new T(function(){return unCStr("PrimaLat");}),new T(function(){return unCStr("useS (useCl (simpleCl (usePN Augustus_PN) (complA laetus_A)))");}))),_DD));}),_Of=function(_){var _Og=_a(_Oe,__Z,_);return 0;},_Oh=function(_){return _Of(_);};
var hasteMain = function() {B(A(_Oh, [0]));};window.onload = hasteMain;