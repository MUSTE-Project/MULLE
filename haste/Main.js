"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

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
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
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
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
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
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
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

var _0=0,_1=new T1(1,_0),_2="()",_3=function(_4){var _5=strEq(_4,E(_2));return (E(_5)==0)?__Z:E(_1);},_6=function(_7){return new F(function(){return _3(E(_7));});},_8=function(_9){return E(_2);},_a=new T2(0,_8,_6),_b=function(_c){return new F(function(){return fromJSStr(E(_c));});},_d=function(_e){return new T1(1,new T(function(){return B(_b(_e));}));},_f=function(_g){return new F(function(){return toJSStr(E(_g));});},_h=new T2(0,_f,_d),_i=function(_j,_k,_){var _l=B(A1(_j,_)),_m=B(A1(_k,_));return _l;},_n=function(_o,_p,_){var _q=B(A1(_o,_)),_r=B(A1(_p,_));return new T(function(){return B(A1(_q,_r));});},_s=function(_t,_u,_){var _v=B(A1(_u,_));return _t;},_w=function(_x,_y,_){var _z=B(A1(_y,_));return new T(function(){return B(A1(_x,_z));});},_A=new T2(0,_w,_s),_B=function(_C,_){return _C;},_D=function(_E,_F,_){var _G=B(A1(_E,_));return new F(function(){return A1(_F,_);});},_H=new T5(0,_A,_B,_n,_D,_i),_I=new T(function(){return B(unCStr("base"));}),_J=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_K=new T(function(){return B(unCStr("IOException"));}),_L=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_I,_J,_K),_M=__Z,_N=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_L,_M,_M),_O=function(_P){return E(_N);},_Q=function(_R){return E(E(_R).a);},_S=function(_T,_U,_V){var _W=B(A1(_T,_)),_X=B(A1(_U,_)),_Y=hs_eqWord64(_W.a,_X.a);if(!_Y){return __Z;}else{var _Z=hs_eqWord64(_W.b,_X.b);return (!_Z)?__Z:new T1(1,_V);}},_10=function(_11){var _12=E(_11);return new F(function(){return _S(B(_Q(_12.a)),_O,_12.b);});},_13=new T(function(){return B(unCStr(": "));}),_14=new T(function(){return B(unCStr(")"));}),_15=new T(function(){return B(unCStr(" ("));}),_16=function(_17,_18){var _19=E(_17);return (_19._==0)?E(_18):new T2(1,_19.a,new T(function(){return B(_16(_19.b,_18));}));},_1a=new T(function(){return B(unCStr("interrupted"));}),_1b=new T(function(){return B(unCStr("system error"));}),_1c=new T(function(){return B(unCStr("unsatisified constraints"));}),_1d=new T(function(){return B(unCStr("user error"));}),_1e=new T(function(){return B(unCStr("permission denied"));}),_1f=new T(function(){return B(unCStr("illegal operation"));}),_1g=new T(function(){return B(unCStr("end of file"));}),_1h=new T(function(){return B(unCStr("resource exhausted"));}),_1i=new T(function(){return B(unCStr("resource busy"));}),_1j=new T(function(){return B(unCStr("does not exist"));}),_1k=new T(function(){return B(unCStr("already exists"));}),_1l=new T(function(){return B(unCStr("resource vanished"));}),_1m=new T(function(){return B(unCStr("timeout"));}),_1n=new T(function(){return B(unCStr("unsupported operation"));}),_1o=new T(function(){return B(unCStr("hardware fault"));}),_1p=new T(function(){return B(unCStr("inappropriate type"));}),_1q=new T(function(){return B(unCStr("invalid argument"));}),_1r=new T(function(){return B(unCStr("failed"));}),_1s=new T(function(){return B(unCStr("protocol error"));}),_1t=function(_1u,_1v){switch(E(_1u)){case 0:return new F(function(){return _16(_1k,_1v);});break;case 1:return new F(function(){return _16(_1j,_1v);});break;case 2:return new F(function(){return _16(_1i,_1v);});break;case 3:return new F(function(){return _16(_1h,_1v);});break;case 4:return new F(function(){return _16(_1g,_1v);});break;case 5:return new F(function(){return _16(_1f,_1v);});break;case 6:return new F(function(){return _16(_1e,_1v);});break;case 7:return new F(function(){return _16(_1d,_1v);});break;case 8:return new F(function(){return _16(_1c,_1v);});break;case 9:return new F(function(){return _16(_1b,_1v);});break;case 10:return new F(function(){return _16(_1s,_1v);});break;case 11:return new F(function(){return _16(_1r,_1v);});break;case 12:return new F(function(){return _16(_1q,_1v);});break;case 13:return new F(function(){return _16(_1p,_1v);});break;case 14:return new F(function(){return _16(_1o,_1v);});break;case 15:return new F(function(){return _16(_1n,_1v);});break;case 16:return new F(function(){return _16(_1m,_1v);});break;case 17:return new F(function(){return _16(_1l,_1v);});break;default:return new F(function(){return _16(_1a,_1v);});}},_1w=new T(function(){return B(unCStr("}"));}),_1x=new T(function(){return B(unCStr("{handle: "));}),_1y=function(_1z,_1A,_1B,_1C,_1D,_1E){var _1F=new T(function(){var _1G=new T(function(){var _1H=new T(function(){var _1I=E(_1C);if(!_1I._){return E(_1E);}else{var _1J=new T(function(){return B(_16(_1I,new T(function(){return B(_16(_14,_1E));},1)));},1);return B(_16(_15,_1J));}},1);return B(_1t(_1A,_1H));}),_1K=E(_1B);if(!_1K._){return E(_1G);}else{return B(_16(_1K,new T(function(){return B(_16(_13,_1G));},1)));}}),_1L=E(_1D);if(!_1L._){var _1M=E(_1z);if(!_1M._){return E(_1F);}else{var _1N=E(_1M.a);if(!_1N._){var _1O=new T(function(){var _1P=new T(function(){return B(_16(_1w,new T(function(){return B(_16(_13,_1F));},1)));},1);return B(_16(_1N.a,_1P));},1);return new F(function(){return _16(_1x,_1O);});}else{var _1Q=new T(function(){var _1R=new T(function(){return B(_16(_1w,new T(function(){return B(_16(_13,_1F));},1)));},1);return B(_16(_1N.a,_1R));},1);return new F(function(){return _16(_1x,_1Q);});}}}else{return new F(function(){return _16(_1L.a,new T(function(){return B(_16(_13,_1F));},1));});}},_1S=function(_1T){var _1U=E(_1T);return new F(function(){return _1y(_1U.a,_1U.b,_1U.c,_1U.d,_1U.f,_M);});},_1V=function(_1W){return new T2(0,_1X,_1W);},_1Y=function(_1Z,_20,_21){var _22=E(_20);return new F(function(){return _1y(_22.a,_22.b,_22.c,_22.d,_22.f,_21);});},_23=function(_24,_25){var _26=E(_24);return new F(function(){return _1y(_26.a,_26.b,_26.c,_26.d,_26.f,_25);});},_27=44,_28=93,_29=91,_2a=function(_2b,_2c,_2d){var _2e=E(_2c);if(!_2e._){return new F(function(){return unAppCStr("[]",_2d);});}else{var _2f=new T(function(){var _2g=new T(function(){var _2h=function(_2i){var _2j=E(_2i);if(!_2j._){return E(new T2(1,_28,_2d));}else{var _2k=new T(function(){return B(A2(_2b,_2j.a,new T(function(){return B(_2h(_2j.b));})));});return new T2(1,_27,_2k);}};return B(_2h(_2e.b));});return B(A2(_2b,_2e.a,_2g));});return new T2(1,_29,_2f);}},_2l=function(_2m,_2n){return new F(function(){return _2a(_23,_2m,_2n);});},_2o=new T3(0,_1Y,_1S,_2l),_1X=new T(function(){return new T5(0,_O,_2o,_1V,_10,_1S);}),_2p=new T(function(){return E(_1X);}),_2q=function(_2r){return E(E(_2r).c);},_2s=__Z,_2t=7,_2u=function(_2v){return new T6(0,_2s,_2t,_M,_2v,_2s,_2s);},_2w=function(_2x,_){var _2y=new T(function(){return B(A2(_2q,_2p,new T(function(){return B(A1(_2u,_2x));})));});return new F(function(){return die(_2y);});},_2z=function(_2A,_){return new F(function(){return _2w(_2A,_);});},_2B=function(_2C){return new F(function(){return A1(_2z,_2C);});},_2D=function(_2E,_2F,_){var _2G=B(A1(_2E,_));return new F(function(){return A2(_2F,_2G,_);});},_2H=new T5(0,_H,_2D,_D,_B,_2B),_2I=function(_2J){return E(_2J);},_2K=new T2(0,_2H,_2I),_2L=0,_2M="POST",_2N="GET",_2O="=",_2P="&",_2Q=function(_2R,_2S){var _2T=E(_2S);return (_2T._==0)?__Z:new T2(1,new T(function(){return B(A1(_2R,_2T.a));}),new T(function(){return B(_2Q(_2R,_2T.b));}));},_2U=function(_2V){return E(E(_2V).a);},_2W=function(_2X,_2Y,_2Z){var _30=function(_31){var _32=E(_31);return new F(function(){return jsCat(new T2(1,new T(function(){return B(A2(_2U,_2X,_32.a));}),new T2(1,new T(function(){return B(A2(_2U,_2Y,_32.b));}),_M)),E(_2O));});},_33=jsCat(B(_2Q(_30,_2Z)),E(_2P));return E(_33);},_34=new T(function(){return eval("(function(method, url, async, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, url, async);if(method == \'POST\') {xhr.setRequestHeader(\'Content-type\',\'application/x-www-form-urlencoded\');}xhr.onreadystatechange = function() {if(xhr.readyState == 4) {cb(xhr.status == 200 ? xhr.responseText : null);}};xhr.send(postdata);})");}),_35=function(_36){return E(E(_36).b);},_37=function(_){return new F(function(){return __jsNull();});},_38=function(_39){var _3a=B(A1(_39,_));return E(_3a);},_3b=new T(function(){return B(_38(_37));}),_3c=new T(function(){return E(_3b);}),_3d=function(_3e){return E(E(_3e).b);},_3f=new T(function(){return toJSStr(_M);}),_3g="?",_3h=function(_3i,_3j,_3k,_3l,_3m,_3n,_3o,_3p){var _3q=new T(function(){return B(_2W(_3j,_3k,_3o));}),_3r=new T(function(){return B(_f(_3n));}),_3s=function(_){var _3t=function(_3u){var _3v=function(_3w){var _3x=function(_3y){var _3z=new T(function(){return B(_35(_3l));}),_3A=function(_3B,_){var _3C=new T(function(){var _3D=E(_3B),_3E=__eq(_3D,E(_3c));if(!E(_3E)){return B(A1(_3z,new T(function(){return String(_3D);})));}else{return __Z;}}),_3F=B(A2(_3p,_3C,_));return _3c;},_3G=__createJSFunc(2,E(_3A)),_3H=__app5(E(_34),_3u,_3w,true,_3y,_3G);return _0;};if(!E(_3m)){return new F(function(){return _3x(E(_3f));});}else{var _3I=E(_3o);if(!_3I._){return new F(function(){return _3x(E(_3f));});}else{return new F(function(){return _3x(B(_2W(_3j,_3k,_3I)));});}}};if(!E(_3m)){if(!E(_3o)._){return new F(function(){return _3v(toJSStr(E(_3n)));});}else{var _3J=jsCat(new T2(1,_3r,new T2(1,_3q,_M)),E(_3g));return new F(function(){return _3v(_3J);});}}else{return new F(function(){return _3v(toJSStr(E(_3n)));});}};if(!E(_3m)){return new F(function(){return _3t(E(_2N));});}else{return new F(function(){return _3t(E(_2M));});}};return new F(function(){return A2(_3d,_3i,_3s);});},_3K=new T(function(){return B(unCStr("nullForeignPtr"));}),_3L=new T(function(){return B(err(_3K));}),_3M=function(_3N){if(_3N>127){if(_3N>16383){if(_3N>2097151){if(_3N>268435455){var _3O=(_3N>>>28&127)>>>0&255,_3P=function(_3Q,_3R){var _3S=E(_3R),_3T=_3S.a,_3U=_3S.b,_3V=_3S.c,_3W=_3S.d,_3X=_3S.e,_3Y=function(_3Z,_40,_41,_42,_43){var _=writeOffAddr("w8",1,plusAddr(_3Z,_41+_42|0),0,((_3N&127)>>>0&255|128)>>>0),_44=_43-1|0,_45=function(_46,_47,_48,_49,_4a){var _=writeOffAddr("w8",1,plusAddr(_46,_48+_49|0),0,((_3N>>>7&127)>>>0&255|128)>>>0),_4b=_4a-1|0,_4c=function(_4d,_4e,_4f,_4g,_4h){var _=writeOffAddr("w8",1,plusAddr(_4d,_4f+_4g|0),0,((_3N>>>14&127)>>>0&255|128)>>>0),_4i=_4h-1|0,_4j=function(_4k,_4l,_4m,_4n,_4o){var _=writeOffAddr("w8",1,plusAddr(_4k,_4m+_4n|0),0,((_3N>>>21&127)>>>0&255|128)>>>0),_4p=_4o-1|0,_4q=_4n+1|0;if(1>_4p){var _4r=E(_4q);if(!_4r){var _4s=newByteArr(32760),_=writeOffAddr("w8",1,_4s,0,_3O);return new F(function(){return A1(_3Q,new T5(0,_4s,new T1(2,_4s),0,1,32759));});}else{return new T2(1,new T4(0,_4k,_4l,_4m,_4r),new T(function(){var _4t=newByteArr(32760),_=writeOffAddr("w8",1,_4t,0,_3O);return B(A1(_3Q,new T5(0,_4t,new T1(2,_4t),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_4k,_4m+_4q|0),0,_3O);return new F(function(){return A1(_3Q,new T5(0,_4k,_4l,_4m,_4q+1|0,_4p-1|0));});}};if(1>_4i){var _4u=_4g+1|0;if(!_4u){var _4v=newByteArr(32760);return new F(function(){return _4j(_4v,new T1(2,_4v),0,0,32760);});}else{return new T2(1,new T4(0,_4d,_4e,_4f,_4u),new T(function(){var _4w=newByteArr(32760);return B(_4j(_4w,new T1(2,_4w),0,0,32760));}));}}else{return new F(function(){return _4j(_4d,_4e,_4f,_4g+1|0,_4i);});}};if(1>_4b){var _4x=_49+1|0;if(!_4x){var _4y=newByteArr(32760);return new F(function(){return _4c(_4y,new T1(2,_4y),0,0,32760);});}else{return new T2(1,new T4(0,_46,_47,_48,_4x),new T(function(){var _4z=newByteArr(32760);return B(_4c(_4z,new T1(2,_4z),0,0,32760));}));}}else{return new F(function(){return _4c(_46,_47,_48,_49+1|0,_4b);});}};if(1>_44){var _4A=_42+1|0;if(!_4A){var _4B=newByteArr(32760);return new F(function(){return _45(_4B,new T1(2,_4B),0,0,32760);});}else{return new T2(1,new T4(0,_3Z,_40,_41,_4A),new T(function(){var _4C=newByteArr(32760);return B(_45(_4C,new T1(2,_4C),0,0,32760));}));}}else{return new F(function(){return _45(_3Z,_40,_41,_42+1|0,_44);});}};if(1>_3X){var _4D=E(_3W);if(!_4D){var _4E=newByteArr(32760);return new F(function(){return _3Y(_4E,new T1(2,_4E),0,0,32760);});}else{return new T2(1,new T4(0,_3T,_3U,_3V,_4D),new T(function(){var _4F=newByteArr(32760);return B(_3Y(_4F,new T1(2,_4F),0,0,32760));}));}}else{return new F(function(){return _3Y(_3T,_3U,_3V,_3W,_3X);});}};return new T2(0,_0,_3P);}else{var _4G=(_3N>>>21&127)>>>0&255,_4H=function(_4I,_4J){var _4K=E(_4J),_4L=_4K.a,_4M=_4K.b,_4N=_4K.c,_4O=_4K.d,_4P=_4K.e,_4Q=function(_4R,_4S,_4T,_4U,_4V){var _=writeOffAddr("w8",1,plusAddr(_4R,_4T+_4U|0),0,((_3N&127)>>>0&255|128)>>>0),_4W=_4V-1|0,_4X=function(_4Y,_4Z,_50,_51,_52){var _=writeOffAddr("w8",1,plusAddr(_4Y,_50+_51|0),0,((_3N>>>7&127)>>>0&255|128)>>>0),_53=_52-1|0,_54=function(_55,_56,_57,_58,_59){var _=writeOffAddr("w8",1,plusAddr(_55,_57+_58|0),0,((_3N>>>14&127)>>>0&255|128)>>>0),_5a=_59-1|0,_5b=_58+1|0;if(1>_5a){var _5c=E(_5b);if(!_5c){var _5d=newByteArr(32760),_=writeOffAddr("w8",1,_5d,0,_4G);return new F(function(){return A1(_4I,new T5(0,_5d,new T1(2,_5d),0,1,32759));});}else{return new T2(1,new T4(0,_55,_56,_57,_5c),new T(function(){var _5e=newByteArr(32760),_=writeOffAddr("w8",1,_5e,0,_4G);return B(A1(_4I,new T5(0,_5e,new T1(2,_5e),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_55,_57+_5b|0),0,_4G);return new F(function(){return A1(_4I,new T5(0,_55,_56,_57,_5b+1|0,_5a-1|0));});}};if(1>_53){var _5f=_51+1|0;if(!_5f){var _5g=newByteArr(32760);return new F(function(){return _54(_5g,new T1(2,_5g),0,0,32760);});}else{return new T2(1,new T4(0,_4Y,_4Z,_50,_5f),new T(function(){var _5h=newByteArr(32760);return B(_54(_5h,new T1(2,_5h),0,0,32760));}));}}else{return new F(function(){return _54(_4Y,_4Z,_50,_51+1|0,_53);});}};if(1>_4W){var _5i=_4U+1|0;if(!_5i){var _5j=newByteArr(32760);return new F(function(){return _4X(_5j,new T1(2,_5j),0,0,32760);});}else{return new T2(1,new T4(0,_4R,_4S,_4T,_5i),new T(function(){var _5k=newByteArr(32760);return B(_4X(_5k,new T1(2,_5k),0,0,32760));}));}}else{return new F(function(){return _4X(_4R,_4S,_4T,_4U+1|0,_4W);});}};if(1>_4P){var _5l=E(_4O);if(!_5l){var _5m=newByteArr(32760);return new F(function(){return _4Q(_5m,new T1(2,_5m),0,0,32760);});}else{return new T2(1,new T4(0,_4L,_4M,_4N,_5l),new T(function(){var _5n=newByteArr(32760);return B(_4Q(_5n,new T1(2,_5n),0,0,32760));}));}}else{return new F(function(){return _4Q(_4L,_4M,_4N,_4O,_4P);});}};return new T2(0,_0,_4H);}}else{var _5o=(_3N>>>14&127)>>>0&255,_5p=function(_5q,_5r){var _5s=E(_5r),_5t=_5s.a,_5u=_5s.b,_5v=_5s.c,_5w=_5s.d,_5x=_5s.e,_5y=function(_5z,_5A,_5B,_5C,_5D){var _=writeOffAddr("w8",1,plusAddr(_5z,_5B+_5C|0),0,((_3N&127)>>>0&255|128)>>>0),_5E=_5D-1|0,_5F=function(_5G,_5H,_5I,_5J,_5K){var _=writeOffAddr("w8",1,plusAddr(_5G,_5I+_5J|0),0,((_3N>>>7&127)>>>0&255|128)>>>0),_5L=_5K-1|0,_5M=_5J+1|0;if(1>_5L){var _5N=E(_5M);if(!_5N){var _5O=newByteArr(32760),_=writeOffAddr("w8",1,_5O,0,_5o);return new F(function(){return A1(_5q,new T5(0,_5O,new T1(2,_5O),0,1,32759));});}else{return new T2(1,new T4(0,_5G,_5H,_5I,_5N),new T(function(){var _5P=newByteArr(32760),_=writeOffAddr("w8",1,_5P,0,_5o);return B(A1(_5q,new T5(0,_5P,new T1(2,_5P),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_5G,_5I+_5M|0),0,_5o);return new F(function(){return A1(_5q,new T5(0,_5G,_5H,_5I,_5M+1|0,_5L-1|0));});}};if(1>_5E){var _5Q=_5C+1|0;if(!_5Q){var _5R=newByteArr(32760);return new F(function(){return _5F(_5R,new T1(2,_5R),0,0,32760);});}else{return new T2(1,new T4(0,_5z,_5A,_5B,_5Q),new T(function(){var _5S=newByteArr(32760);return B(_5F(_5S,new T1(2,_5S),0,0,32760));}));}}else{return new F(function(){return _5F(_5z,_5A,_5B,_5C+1|0,_5E);});}};if(1>_5x){var _5T=E(_5w);if(!_5T){var _5U=newByteArr(32760);return new F(function(){return _5y(_5U,new T1(2,_5U),0,0,32760);});}else{return new T2(1,new T4(0,_5t,_5u,_5v,_5T),new T(function(){var _5V=newByteArr(32760);return B(_5y(_5V,new T1(2,_5V),0,0,32760));}));}}else{return new F(function(){return _5y(_5t,_5u,_5v,_5w,_5x);});}};return new T2(0,_0,_5p);}}else{var _5W=(_3N>>>7&127)>>>0&255,_5X=function(_5Y,_5Z){var _60=E(_5Z),_61=_60.a,_62=_60.b,_63=_60.c,_64=_60.d,_65=_60.e,_66=function(_67,_68,_69,_6a,_6b){var _=writeOffAddr("w8",1,plusAddr(_67,_69+_6a|0),0,((_3N&127)>>>0&255|128)>>>0),_6c=_6b-1|0,_6d=_6a+1|0;if(1>_6c){var _6e=E(_6d);if(!_6e){var _6f=newByteArr(32760),_=writeOffAddr("w8",1,_6f,0,_5W);return new F(function(){return A1(_5Y,new T5(0,_6f,new T1(2,_6f),0,1,32759));});}else{return new T2(1,new T4(0,_67,_68,_69,_6e),new T(function(){var _6g=newByteArr(32760),_=writeOffAddr("w8",1,_6g,0,_5W);return B(A1(_5Y,new T5(0,_6g,new T1(2,_6g),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_67,_69+_6d|0),0,_5W);return new F(function(){return A1(_5Y,new T5(0,_67,_68,_69,_6d+1|0,_6c-1|0));});}};if(1>_65){var _6h=E(_64);if(!_6h){var _6i=newByteArr(32760);return new F(function(){return _66(_6i,new T1(2,_6i),0,0,32760);});}else{return new T2(1,new T4(0,_61,_62,_63,_6h),new T(function(){var _6j=newByteArr(32760);return B(_66(_6j,new T1(2,_6j),0,0,32760));}));}}else{return new F(function(){return _66(_61,_62,_63,_64,_65);});}};return new T2(0,_0,_5X);}}else{var _6k=(_3N&127)>>>0&255,_6l=function(_6m,_6n){var _6o=E(_6n),_6p=_6o.a,_6q=_6o.b,_6r=_6o.c,_6s=_6o.d,_6t=_6o.e;if(1>_6t){var _6u=E(_6s);if(!_6u){var _6v=newByteArr(32760),_=writeOffAddr("w8",1,_6v,0,_6k);return new F(function(){return A1(_6m,new T5(0,_6v,new T1(2,_6v),0,1,32759));});}else{return new T2(1,new T4(0,_6p,_6q,_6r,_6u),new T(function(){var _6w=newByteArr(32760),_=writeOffAddr("w8",1,_6w,0,_6k);return B(A1(_6m,new T5(0,_6w,new T1(2,_6w),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_6p,_6r+_6s|0),0,_6k);return new F(function(){return A1(_6m,new T5(0,_6p,_6q,_6r,_6s+1|0,_6t-1|0));});}};return new T2(0,_0,_6l);}},_6x=function(_6y){var _6z=new T(function(){var _6A=E(_6y);if(_6A.d>0){var _6B=function(_6C,_6D){var _6E=E(_6D),_6F=_6E.a,_6G=_6E.b,_6H=_6E.c,_6I=_6E.e,_6J=E(_6E.d);return (_6J==0)?new T2(1,_6A,new T(function(){return B(A1(_6C,new T5(0,_6F,_6G,_6H,0,_6I)));})):new T2(1,new T4(0,_6F,_6G,_6H,_6J),new T2(1,_6A,new T(function(){return B(A1(_6C,new T5(0,_6F,_6G,_6H+_6J|0,0,_6I)));})));},_6K=E(_6B);}else{var _6K=E(_2I);}return new T2(0,_0,E(_6K));}),_6L=new T(function(){return E(B(_3M(E(_6y).d>>>0)).b);}),_6M=function(_6N){return new F(function(){return A1(_6L,new T(function(){return B(A1(E(_6z).b,_6N));}));});};return new T2(0,new T(function(){return E(E(_6z).a);}),_6M);},_6O=function(_6P){var _6Q=B(_6x(_6P));return new T2(0,_6Q.a,E(_6Q.b));},_6R=new T(function(){return B(unCStr("concat"));}),_6S=new T4(0,0,_3L,0,0),_6T=function(_6U,_6V,_){while(1){var _6W=E(_6U);if(!_6W._){return _0;}else{var _6X=E(_6W.a),_6Y=_6X.b,_6Z=_6X.d,_70=memcpy(_6V,plusAddr(_6X.a,_6X.c),_6Z>>>0),_71=plusAddr(_6V,_6Z);_6U=_6W.b;_6V=_71;_=0;continue;}}},_72=function(_73,_74,_75,_){var _76=E(_73),_77=_76.b,_78=_76.d,_79=memcpy(_75,plusAddr(_76.a,_76.c),_78>>>0);return new F(function(){return _6T(_74,plusAddr(_75,_78),0);});},_7a=function(_7b){var _7c=E(_7b);return (_7c._==0)?__Z:new T2(1,E(_7c.a).d,new T(function(){return B(_7a(_7c.b));}));},_7d=function(_7e,_7f){return new T2(1,E(_7e).d,new T(function(){return B(_7a(_7f));}));},_7g=new T(function(){return B(unCStr(": size overflow"));}),_7h=function(_7i){return new F(function(){return err(B(unAppCStr("Data.ByteString.",new T(function(){return B(_16(_7i,_7g));}))));});},_7j=function(_7k,_7l){var _7m=function(_7n,_7o){while(1){var _7p=E(_7o);if(!_7p._){return E(_7n);}else{var _7q=_7n+E(_7p.a)|0;if(_7q<0){return new F(function(){return _7h(_7k);});}else{_7n=_7q;_7o=_7p.b;continue;}}}};return new F(function(){return _7m(0,_7l);});},_7r=new T(function(){return B(unCStr("mallocPlainForeignPtrBytes: size must be >= 0"));}),_7s=new T(function(){return B(err(_7r));}),_7t=function(_7u){var _7v=E(_7u);if(!_7v._){return E(_6S);}else{var _7w=_7v.a,_7x=E(_7v.b);if(!_7x._){return E(_7w);}else{return new F(function(){return _38(function(_){var _7y=B(_7j(_6R,B(_7d(_7w,_7x))));if(_7y>=0){var _7z=newByteArr(_7y),_7A=B(_72(_7w,_7x,_7z,_));return new T4(0,_7z,new T1(2,_7z),0,_7y);}else{return E(_7s);}});});}}},_7B=__Z,_7C=new T5(1,0,_3L,0,0,_7B),_7D=function(_7E,_7F){var _7G=hs_eqInt64(_7E,new Long(0,0));if(!_7G){var _7H=E(_7F);if(!_7H._){return new T2(0,_7B,_7B);}else{var _7I=_7H.a,_7J=_7H.b,_7K=_7H.c,_7L=_7H.d,_7M=_7H.e,_7N=hs_intToInt64(_7L),_7O=hs_ltInt64(_7E,_7N);if(!_7O){var _7P=new T(function(){var _7Q=hs_minusInt64(_7E,_7N),_7R=B(_7D(_7Q,_7M));return new T2(0,_7R.a,_7R.b);});return new T2(0,new T5(1,_7I,_7J,_7K,_7L,new T(function(){return E(E(_7P).a);})),new T(function(){return E(E(_7P).b);}));}else{return new T2(0,new T(function(){var _7S=hs_int64ToInt(_7E);if(_7S>0){if(_7S<_7L){return new T5(1,_7I,_7J,_7K,_7S,_7B);}else{return new T5(1,_7I,_7J,_7K,_7L,_7B);}}else{return E(_7C);}}),new T(function(){var _7T=hs_int64ToInt(_7E);if(_7T>0){if(_7T<_7L){return new T5(1,_7I,_7J,_7K+_7T|0,_7L-_7T|0,_7M);}else{return new T5(1,0,_3L,0,0,_7M);}}else{return E(_7H);}}));}}}else{return new T2(0,_7B,_7F);}},_7U=new T4(0,0,_3L,0,0),_7V=new T(function(){return B(unCStr("too few bytes"));}),_7W=function(_7X){while(1){var _7Y=E(_7X);if(!_7Y._){_7X=new T1(1,I_fromInt(_7Y.a));continue;}else{return new F(function(){return I_toString(_7Y.a);});}}},_7Z=function(_80,_81){return new F(function(){return _16(fromJSStr(B(_7W(_80))),_81);});},_82=function(_83,_84){var _85=E(_83);if(!_85._){var _86=_85.a,_87=E(_84);return (_87._==0)?_86<_87.a:I_compareInt(_87.a,_86)>0;}else{var _88=_85.a,_89=E(_84);return (_89._==0)?I_compareInt(_88,_89.a)<0:I_compare(_88,_89.a)<0;}},_8a=41,_8b=40,_8c=new T1(0,0),_8d=function(_8e,_8f,_8g){if(_8e<=6){return new F(function(){return _7Z(_8f,_8g);});}else{if(!B(_82(_8f,_8c))){return new F(function(){return _7Z(_8f,_8g);});}else{return new T2(1,_8b,new T(function(){return B(_16(fromJSStr(B(_7W(_8f))),new T2(1,_8a,_8g)));}));}}},_8h=function(_8i){return new T1(0,_8i);},_8j=function(_8k){var _8l=hs_intToInt64(2147483647),_8m=hs_leInt64(_8k,_8l);if(!_8m){return new T1(1,I_fromInt64(_8k));}else{var _8n=hs_intToInt64(-2147483648),_8o=hs_geInt64(_8k,_8n);if(!_8o){return new T1(1,I_fromInt64(_8k));}else{var _8p=hs_int64ToInt(_8k);return new F(function(){return _8h(_8p);});}}},_8q=function(_8r,_8s){var _8t=new T(function(){return B(unAppCStr(". Failed reading at byte position ",new T(function(){return B(_8d(0,B(_8j(_8s)),_M));})));},1);return new F(function(){return err(B(_16(_8r,_8t)));});},_8u=function(_8v){return new F(function(){return _8q(_7V,_8v);});},_8w=function(_8x){var _8y=E(_8x);return (_8y._==0)?__Z:new T2(1,new T4(0,_8y.a,_8y.b,_8y.c,_8y.d),new T(function(){return B(_8w(_8y.e));}));},_8z=new T(function(){return B(_8w(_7B));}),_8A=new T(function(){return B(_7t(_8z));}),_8B=function(_8C,_8D,_8E,_8F,_8G,_8H,_8I){if(_8C>_8G){var _8J=hs_intToInt64(_8C),_8K=_8J,_8L=hs_leInt64(_8K,new Long(0,0)),_8M=function(_8N,_8O){var _8P=E(_8O);if(!_8P._){var _8Q=hs_plusInt64(_8I,_8K),_8R=B(_7t(B(_8w(_8N))));if(_8R.d>=_8C){return new T2(0,_8R,new T6(0,0,_3L,0,0,_7B,_8Q));}else{return new F(function(){return _8u(_8Q);});}}else{var _8S=hs_plusInt64(_8I,_8K),_8T=B(_7t(B(_8w(_8N))));if(_8T.d>=_8C){return new T2(0,_8T,new T6(0,_8P.a,_8P.b,_8P.c,_8P.d,_8P.e,_8S));}else{return new F(function(){return _8u(_8S);});}}};if(!_8L){var _8U=B(_7D(_8K,new T(function(){if(_8G>0){return new T5(1,_8D,_8E,_8F,_8G,_8H);}else{return E(_8H);}})));return new F(function(){return _8M(_8U.a,_8U.b);});}else{if(_8G>0){var _8V=hs_plusInt64(_8I,_8K),_8W=E(_8A);if(_8W.d>=_8C){return new T2(0,_8W,new T6(0,_8D,_8E,_8F,_8G,_8H,_8V));}else{return new F(function(){return _8u(_8V);});}}else{return new F(function(){return _8M(_7B,_8H);});}}}else{if(_8C>0){if(_8C<_8G){var _8X=hs_intToInt64(_8C),_8Y=hs_plusInt64(_8I,_8X);return new T2(0,new T4(0,_8D,_8E,_8F,_8C),new T6(0,_8D,_8E,_8F+_8C|0,_8G-_8C|0,_8H,_8Y));}else{var _8Z=hs_intToInt64(_8C),_90=hs_plusInt64(_8I,_8Z);return new T2(0,new T4(0,_8D,_8E,_8F,_8G),new T6(0,0,_3L,0,0,_8H,_90));}}else{var _91=hs_intToInt64(_8C),_92=hs_plusInt64(_8I,_91);return new T2(0,_7U,new T6(0,_8D,_8E,_8F,_8G,_8H,_92));}}},_93=function(_94,_95,_96,_97,_98,_99){var _9a=B(_8B(1,_94,_95,_96,_97,_98,_99)),_9b=_9a.b,_9c=E(_9a.a),_9d=_9c.b,_9e=readOffAddr("w8",1,plusAddr(_9c.a,_9c.c),0);if(_9e>127){var _9f=E(_9b),_9g=B(_93(_9f.a,_9f.b,_9f.c,_9f.d,_9f.e,_9f.f));return new T2(0,new T(function(){return (E(_9g.a)<<7>>>0|(_9e&127)>>>0)>>>0;}),_9g.b);}else{return new T2(0,_9e,_9b);}},_9h=function(_9i,_9j,_9k,_9l,_9m,_9n){var _9o=B(_93(_9i,_9j,_9k,_9l,_9m,_9n)),_9p=E(_9o.b);return new F(function(){return _8B(E(_9o.a)&4294967295,_9p.a,_9p.b,_9p.c,_9p.d,_9p.e,_9p.f);});},_9q=function(_9r){var _9s=E(_9r),_9t=B(_9h(_9s.a,_9s.b,_9s.c,_9s.d,_9s.e,_9s.f));return new T2(0,_9t.a,_9t.b);},_9u=new T2(0,_6O,_9q),_9v=function(_9w,_9x){var _9y=jsShowI(_9w);return new F(function(){return _16(fromJSStr(_9y),_9x);});},_9z=function(_9A,_9B,_9C){if(_9B>=0){return new F(function(){return _9v(_9B,_9C);});}else{if(_9A<=6){return new F(function(){return _9v(_9B,_9C);});}else{return new T2(1,_8b,new T(function(){var _9D=jsShowI(_9B);return B(_16(fromJSStr(_9D),new T2(1,_8a,_9C)));}));}}},_9E=function(_9F){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_9z(9,_9F,_M));}))));});},_9G=function(_9H,_9I,_9J,_9K,_9L,_9M){var _9N=B(_8B(1,_9H,_9I,_9J,_9K,_9L,_9M)),_9O=_9N.b,_9P=E(_9N.a),_9Q=_9P.b,_9R=readOffAddr("w8",1,plusAddr(_9P.a,_9P.c),0),_9S=_9R&4294967295;if(_9S>=128){if(_9S>=224){if(_9S>=240){var _9T=E(_9O),_9U=B(_8B(1,_9T.a,_9T.b,_9T.c,_9T.d,_9T.e,_9T.f)),_9V=E(_9U.a),_9W=_9V.b,_9X=E(_9U.b),_9Y=B(_8B(1,_9X.a,_9X.b,_9X.c,_9X.d,_9X.e,_9X.f)),_9Z=E(_9Y.a),_a0=_9Z.b,_a1=E(_9Y.b),_a2=B(_8B(1,_a1.a,_a1.b,_a1.c,_a1.d,_a1.e,_a1.f)),_a3=E(_a2.a),_a4=_a3.b,_a5=readOffAddr("w8",1,plusAddr(_a3.a,_a3.c),0),_a6=readOffAddr("w8",1,plusAddr(_9Z.a,_9Z.c),0),_a7=readOffAddr("w8",1,plusAddr(_9V.a,_9V.c),0),_a8=128^_a5&4294967295|(128^_a6&4294967295|(128^_a7&4294967295|(240^_9S)<<6)<<6)<<6;if(_a8>>>0>1114111){return new F(function(){return _9E(_a8);});}else{return new T2(0,_a8,_a2.b);}}else{var _a9=E(_9O),_aa=B(_8B(1,_a9.a,_a9.b,_a9.c,_a9.d,_a9.e,_a9.f)),_ab=E(_aa.a),_ac=_ab.b,_ad=E(_aa.b),_ae=B(_8B(1,_ad.a,_ad.b,_ad.c,_ad.d,_ad.e,_ad.f)),_af=E(_ae.a),_ag=_af.b,_ah=readOffAddr("w8",1,plusAddr(_af.a,_af.c),0),_ai=readOffAddr("w8",1,plusAddr(_ab.a,_ab.c),0),_aj=128^_ah&4294967295|(128^_ai&4294967295|(224^_9S)<<6)<<6;if(_aj>>>0>1114111){return new F(function(){return _9E(_aj);});}else{return new T2(0,_aj,_ae.b);}}}else{var _ak=E(_9O),_al=B(_8B(1,_ak.a,_ak.b,_ak.c,_ak.d,_ak.e,_ak.f)),_am=E(_al.a),_an=_am.b,_ao=readOffAddr("w8",1,plusAddr(_am.a,_am.c),0),_ap=128^_ao&4294967295|(192^_9S)<<6;if(_ap>>>0>1114111){return new F(function(){return _9E(_ap);});}else{return new T2(0,_ap,_al.b);}}}else{if(_9S>>>0>1114111){return new F(function(){return _9E(_9S);});}else{return new T2(0,_9S,_9O);}}},_aq=function(_ar){var _as=E(_ar),_at=B(_9G(_as.a,_as.b,_as.c,_as.d,_as.e,_as.f));return new T2(0,_at.a,_at.b);},_au=function(_av,_aw){var _ax=E(_av);if(!_ax._){return new T2(0,_M,_aw);}else{var _ay=B(A1(_ax.a,_aw)),_az=B(_au(_ax.b,_ay.b));return new T2(0,new T2(1,_ay.a,_az.a),_az.b);}},_aA=function(_aB,_aC,_aD){if(0>=_aB){return new F(function(){return _au(_M,_aD);});}else{var _aE=function(_aF){var _aG=E(_aF);return (_aG==1)?E(new T2(1,_aC,_M)):new T2(1,_aC,new T(function(){return B(_aE(_aG-1|0));}));};return new F(function(){return _au(B(_aE(_aB)),_aD);});}},_aH=function(_aI){var _aJ=E(_aI),_aK=B(_93(_aJ.a,_aJ.b,_aJ.c,_aJ.d,_aJ.e,_aJ.f)),_aL=B(_aA(E(_aK.a)&4294967295,_aq,_aK.b));return new T2(0,_aL.a,_aL.b);},_aM=new T(function(){return B(unCStr("Not a valid Unicode code point"));}),_aN=new T(function(){return B(err(_aM));}),_aO=function(_aP){if(_aP>127){if(_aP>2047){if(_aP>65535){if(_aP>1114111){return E(_aN);}else{var _aQ=(128|(_aP&63)>>>0&255)>>>0,_aR=function(_aS,_aT){var _aU=E(_aT),_aV=_aU.a,_aW=_aU.b,_aX=_aU.c,_aY=_aU.d,_aZ=_aU.e,_b0=function(_b1,_b2,_b3,_b4,_b5){var _=writeOffAddr("w8",1,plusAddr(_b1,_b3+_b4|0),0,(240|(_aP>>18&7)>>>0&255)>>>0),_b6=_b5-1|0,_b7=function(_b8,_b9,_ba,_bb,_bc){var _=writeOffAddr("w8",1,plusAddr(_b8,_ba+_bb|0),0,(128|(_aP>>12&63)>>>0&255)>>>0),_bd=_bc-1|0,_be=function(_bf,_bg,_bh,_bi,_bj){var _=writeOffAddr("w8",1,plusAddr(_bf,_bh+_bi|0),0,(128|(_aP>>6&63)>>>0&255)>>>0),_bk=_bj-1|0,_bl=_bi+1|0;if(1>_bk){var _bm=E(_bl);if(!_bm){var _bn=newByteArr(32760),_=writeOffAddr("w8",1,_bn,0,_aQ);return new F(function(){return A1(_aS,new T5(0,_bn,new T1(2,_bn),0,1,32759));});}else{return new T2(1,new T4(0,_bf,_bg,_bh,_bm),new T(function(){var _bo=newByteArr(32760),_=writeOffAddr("w8",1,_bo,0,_aQ);return B(A1(_aS,new T5(0,_bo,new T1(2,_bo),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_bf,_bh+_bl|0),0,_aQ);return new F(function(){return A1(_aS,new T5(0,_bf,_bg,_bh,_bl+1|0,_bk-1|0));});}};if(1>_bd){var _bp=_bb+1|0;if(!_bp){var _bq=newByteArr(32760);return new F(function(){return _be(_bq,new T1(2,_bq),0,0,32760);});}else{return new T2(1,new T4(0,_b8,_b9,_ba,_bp),new T(function(){var _br=newByteArr(32760);return B(_be(_br,new T1(2,_br),0,0,32760));}));}}else{return new F(function(){return _be(_b8,_b9,_ba,_bb+1|0,_bd);});}};if(1>_b6){var _bs=_b4+1|0;if(!_bs){var _bt=newByteArr(32760);return new F(function(){return _b7(_bt,new T1(2,_bt),0,0,32760);});}else{return new T2(1,new T4(0,_b1,_b2,_b3,_bs),new T(function(){var _bu=newByteArr(32760);return B(_b7(_bu,new T1(2,_bu),0,0,32760));}));}}else{return new F(function(){return _b7(_b1,_b2,_b3,_b4+1|0,_b6);});}};if(1>_aZ){var _bv=E(_aY);if(!_bv){var _bw=newByteArr(32760);return new F(function(){return _b0(_bw,new T1(2,_bw),0,0,32760);});}else{return new T2(1,new T4(0,_aV,_aW,_aX,_bv),new T(function(){var _bx=newByteArr(32760);return B(_b0(_bx,new T1(2,_bx),0,0,32760));}));}}else{return new F(function(){return _b0(_aV,_aW,_aX,_aY,_aZ);});}};return new T2(0,_0,_aR);}}else{var _by=(128|(_aP&63)>>>0&255)>>>0,_bz=function(_bA,_bB){var _bC=E(_bB),_bD=_bC.a,_bE=_bC.b,_bF=_bC.c,_bG=_bC.d,_bH=_bC.e,_bI=function(_bJ,_bK,_bL,_bM,_bN){var _=writeOffAddr("w8",1,plusAddr(_bJ,_bL+_bM|0),0,(224|(_aP>>12&63)>>>0&255)>>>0),_bO=_bN-1|0,_bP=function(_bQ,_bR,_bS,_bT,_bU){var _=writeOffAddr("w8",1,plusAddr(_bQ,_bS+_bT|0),0,(128|(_aP>>6&63)>>>0&255)>>>0),_bV=_bU-1|0,_bW=_bT+1|0;if(1>_bV){var _bX=E(_bW);if(!_bX){var _bY=newByteArr(32760),_=writeOffAddr("w8",1,_bY,0,_by);return new F(function(){return A1(_bA,new T5(0,_bY,new T1(2,_bY),0,1,32759));});}else{return new T2(1,new T4(0,_bQ,_bR,_bS,_bX),new T(function(){var _bZ=newByteArr(32760),_=writeOffAddr("w8",1,_bZ,0,_by);return B(A1(_bA,new T5(0,_bZ,new T1(2,_bZ),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_bQ,_bS+_bW|0),0,_by);return new F(function(){return A1(_bA,new T5(0,_bQ,_bR,_bS,_bW+1|0,_bV-1|0));});}};if(1>_bO){var _c0=_bM+1|0;if(!_c0){var _c1=newByteArr(32760);return new F(function(){return _bP(_c1,new T1(2,_c1),0,0,32760);});}else{return new T2(1,new T4(0,_bJ,_bK,_bL,_c0),new T(function(){var _c2=newByteArr(32760);return B(_bP(_c2,new T1(2,_c2),0,0,32760));}));}}else{return new F(function(){return _bP(_bJ,_bK,_bL,_bM+1|0,_bO);});}};if(1>_bH){var _c3=E(_bG);if(!_c3){var _c4=newByteArr(32760);return new F(function(){return _bI(_c4,new T1(2,_c4),0,0,32760);});}else{return new T2(1,new T4(0,_bD,_bE,_bF,_c3),new T(function(){var _c5=newByteArr(32760);return B(_bI(_c5,new T1(2,_c5),0,0,32760));}));}}else{return new F(function(){return _bI(_bD,_bE,_bF,_bG,_bH);});}};return new T2(0,_0,_bz);}}else{var _c6=(128|(_aP&63)>>>0&255)>>>0,_c7=function(_c8,_c9){var _ca=E(_c9),_cb=_ca.a,_cc=_ca.b,_cd=_ca.c,_ce=_ca.d,_cf=_ca.e,_cg=function(_ch,_ci,_cj,_ck,_cl){var _=writeOffAddr("w8",1,plusAddr(_ch,_cj+_ck|0),0,(192|(_aP>>6&63)>>>0&255)>>>0),_cm=_cl-1|0,_cn=_ck+1|0;if(1>_cm){var _co=E(_cn);if(!_co){var _cp=newByteArr(32760),_=writeOffAddr("w8",1,_cp,0,_c6);return new F(function(){return A1(_c8,new T5(0,_cp,new T1(2,_cp),0,1,32759));});}else{return new T2(1,new T4(0,_ch,_ci,_cj,_co),new T(function(){var _cq=newByteArr(32760),_=writeOffAddr("w8",1,_cq,0,_c6);return B(A1(_c8,new T5(0,_cq,new T1(2,_cq),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_ch,_cj+_cn|0),0,_c6);return new F(function(){return A1(_c8,new T5(0,_ch,_ci,_cj,_cn+1|0,_cm-1|0));});}};if(1>_cf){var _cr=E(_ce);if(!_cr){var _cs=newByteArr(32760);return new F(function(){return _cg(_cs,new T1(2,_cs),0,0,32760);});}else{return new T2(1,new T4(0,_cb,_cc,_cd,_cr),new T(function(){var _ct=newByteArr(32760);return B(_cg(_ct,new T1(2,_ct),0,0,32760));}));}}else{return new F(function(){return _cg(_cb,_cc,_cd,_ce,_cf);});}};return new T2(0,_0,_c7);}}else{var _cu=_aP>>>0&255,_cv=function(_cw,_cx){var _cy=E(_cx),_cz=_cy.a,_cA=_cy.b,_cB=_cy.c,_cC=_cy.d,_cD=_cy.e;if(1>_cD){var _cE=E(_cC);if(!_cE){var _cF=newByteArr(32760),_=writeOffAddr("w8",1,_cF,0,_cu);return new F(function(){return A1(_cw,new T5(0,_cF,new T1(2,_cF),0,1,32759));});}else{return new T2(1,new T4(0,_cz,_cA,_cB,_cE),new T(function(){var _cG=newByteArr(32760),_=writeOffAddr("w8",1,_cG,0,_cu);return B(A1(_cw,new T5(0,_cG,new T1(2,_cG),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_cz,_cB+_cC|0),0,_cu);return new F(function(){return A1(_cw,new T5(0,_cz,_cA,_cB,_cC+1|0,_cD-1|0));});}};return new T2(0,_0,_cv);}},_cH=function(_cI){var _cJ=B(_aO(E(_cI)));return new T2(0,_cJ.a,E(_cJ.b));},_cK=new T2(0,_cH,_aq),_cL=function(_cM,_cN){while(1){var _cO=E(_cM);if(!_cO._){return E(_cN);}else{var _cP=_cN+1|0;_cM=_cO.b;_cN=_cP;continue;}}},_cQ=function(_cR){return E(E(_cR).a);},_cS=function(_cT,_cU){var _cV=new T(function(){var _cW=new T(function(){return B(_cQ(_cT));}),_cX=function(_cY){var _cZ=E(_cY);if(!_cZ._){return new T2(0,_0,_2I);}else{var _d0=new T(function(){var _d1=B(_cX(_cZ.b));return new T2(0,_d1.a,E(_d1.b));}),_d2=new T(function(){return E(B(A1(_cW,_cZ.a)).b);}),_d3=function(_d4){return new F(function(){return A1(_d2,new T(function(){return B(A1(E(_d0).b,_d4));}));});};return new T2(0,new T(function(){return E(E(_d0).a);}),_d3);}},_d5=B(_cX(_cU));return new T2(0,_d5.a,E(_d5.b));}),_d6=new T(function(){return E(B(_3M(B(_cL(_cU,0))>>>0)).b);}),_d7=function(_d8){return new F(function(){return A1(_d6,new T(function(){return B(A1(E(_cV).b,_d8));}));});};return new T2(0,new T(function(){return E(E(_cV).a);}),_d7);},_d9=function(_da){var _db=B(_cS(_cK,_da));return new T2(0,_db.a,E(_db.b));},_dc=new T2(0,_d9,_aH),_dd=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_de=new T(function(){return B(err(_dd));}),_df=function(_dg){var _dh=B(A1(_dg,_));return E(_dh);},_di=function(_dj,_dk,_dl){var _dm=function(_){var _dn=E(_dk),_do=_dn.c,_dp=newArr(_do,_de),_dq=_dp,_dr=function(_ds,_){while(1){if(_ds!=_do){var _=_dq[_ds]=_dn.d[_ds],_dt=_ds+1|0;_ds=_dt;continue;}else{return E(_);}}},_=B(_dr(0,_)),_du=function(_dv,_){while(1){var _dw=E(_dv);if(!_dw._){return new T4(0,E(_dn.a),E(_dn.b),_do,_dq);}else{var _dx=E(_dw.a),_=_dq[E(_dx.a)]=_dx.b;_dv=_dw.b;continue;}}};return new F(function(){return _du(_dl,_);});};return new F(function(){return _df(_dm);});},_dy=function(_dz,_dA,_dB){return new F(function(){return _di(_dz,_dA,_dB);});},_dC=function(_dD,_dE,_dF){return E(E(_dE).d[E(_dF)]);},_dG=function(_dH,_dI,_dJ){return new F(function(){return _dC(_dH,_dI,_dJ);});},_dK=function(_dL){return E(E(_dL).f);},_dM=function(_dN,_dO,_dP){var _dQ=E(_dO),_dR=B(A2(_dK,_dN,_dQ)),_dS=function(_){var _dT=newArr(_dR,_de),_dU=_dT,_dV=function(_dW,_){while(1){var _dX=B((function(_dY,_){var _dZ=E(_dY);if(!_dZ._){return new T(function(){return new T4(0,E(_dQ.a),E(_dQ.b),_dR,_dU);});}else{var _e0=E(_dZ.a),_=_dU[E(_e0.a)]=_e0.b;_dW=_dZ.b;return __continue;}})(_dW,_));if(_dX!=__continue){return _dX;}}};return new F(function(){return _dV(_dP,_);});};return new F(function(){return _df(_dS);});},_e1=function(_e2,_e3,_e4){return new F(function(){return _dM(_e2,_e3,_e4);});},_e5=function(_e6,_e7){return E(_e7).c;},_e8=function(_e9,_ea){return new F(function(){return _e5(_e9,_ea);});},_eb=function(_ec,_ed){var _ee=E(_ed);return new T2(0,_ee.a,_ee.b);},_ef=function(_eg,_eh){return new F(function(){return _eb(_eg,_eh);});},_ei=function(_ej,_ek,_el,_em){var _en=function(_){var _eo=E(_el),_ep=_eo.c,_eq=newArr(_ep,_de),_er=_eq,_es=function(_et,_){while(1){if(_et!=_ep){var _=_er[_et]=_eo.d[_et],_eu=_et+1|0;_et=_eu;continue;}else{return E(_);}}},_=B(_es(0,_)),_ev=function(_ew,_){while(1){var _ex=B((function(_ey,_){var _ez=E(_ey);if(!_ez._){return new T4(0,E(_eo.a),E(_eo.b),_ep,_er);}else{var _eA=E(_ez.a),_eB=E(_eA.a),_eC=_er[_eB],_=_er[_eB]=new T(function(){return B(A2(_ek,_eC,_eA.b));});_ew=_ez.b;return __continue;}})(_ew,_));if(_ex!=__continue){return _ex;}}};return new F(function(){return _ev(_em,_);});};return new F(function(){return _df(_en);});},_eD=function(_eE,_eF,_eG,_eH,_eI){var _eJ=E(_eH),_eK=B(A2(_dK,_eE,_eJ)),_eL=function(_){var _eM=newArr(_eK,_eG),_eN=_eM,_eO=function(_eP,_){while(1){var _eQ=B((function(_eR,_){var _eS=E(_eR);if(!_eS._){return new T(function(){return new T4(0,E(_eJ.a),E(_eJ.b),_eK,_eN);});}else{var _eT=E(_eS.a),_eU=E(_eT.a),_eV=_eN[_eU],_=_eN[_eU]=new T(function(){return B(A2(_eF,_eV,_eT.b));});_eP=_eS.b;return __continue;}})(_eP,_));if(_eQ!=__continue){return _eQ;}}};return new F(function(){return _eO(_eI,_);});};return new F(function(){return _df(_eL);});},_eW={_:0,a:_ef,b:_e8,c:_e1,d:_dG,e:_dy,f:_ei,g:_eD},_eX=new T(function(){return B(unCStr("Negative range size"));}),_eY=new T(function(){return B(err(_eX));}),_eZ=0,_f0=function(_f1){var _f2=E(_f1);return (E(_f2.b)-E(_f2.a)|0)+1|0;},_f3=function(_f4,_f5){var _f6=E(_f4),_f7=E(_f5);return (E(_f6.a)>_f7)?false:_f7<=E(_f6.b);},_f8=function(_f9){return new F(function(){return _9z(0,E(_f9),_M);});},_fa=function(_fb,_fc,_fd){return new F(function(){return _9z(E(_fb),E(_fc),_fd);});},_fe=function(_ff,_fg){return new F(function(){return _9z(0,E(_ff),_fg);});},_fh=function(_fi,_fj){return new F(function(){return _2a(_fe,_fi,_fj);});},_fk=new T3(0,_fa,_f8,_fh),_fl=0,_fm=function(_fn,_fo,_fp){return new F(function(){return A1(_fn,new T2(1,_27,new T(function(){return B(A1(_fo,_fp));})));});},_fq=new T(function(){return B(unCStr(": empty list"));}),_fr=new T(function(){return B(unCStr("Prelude."));}),_fs=function(_ft){return new F(function(){return err(B(_16(_fr,new T(function(){return B(_16(_ft,_fq));},1))));});},_fu=new T(function(){return B(unCStr("foldr1"));}),_fv=new T(function(){return B(_fs(_fu));}),_fw=function(_fx,_fy){var _fz=E(_fy);if(!_fz._){return E(_fv);}else{var _fA=_fz.a,_fB=E(_fz.b);if(!_fB._){return E(_fA);}else{return new F(function(){return A2(_fx,_fA,new T(function(){return B(_fw(_fx,_fB));}));});}}},_fC=new T(function(){return B(unCStr(" out of range "));}),_fD=new T(function(){return B(unCStr("}.index: Index "));}),_fE=new T(function(){return B(unCStr("Ix{"));}),_fF=new T2(1,_8a,_M),_fG=new T2(1,_8a,_fF),_fH=0,_fI=function(_fJ){return E(E(_fJ).a);},_fK=function(_fL,_fM,_fN,_fO,_fP){var _fQ=new T(function(){var _fR=new T(function(){var _fS=new T(function(){var _fT=new T(function(){var _fU=new T(function(){return B(A3(_fw,_fm,new T2(1,new T(function(){return B(A3(_fI,_fN,_fH,_fO));}),new T2(1,new T(function(){return B(A3(_fI,_fN,_fH,_fP));}),_M)),_fG));});return B(_16(_fC,new T2(1,_8b,new T2(1,_8b,_fU))));});return B(A(_fI,[_fN,_fl,_fM,new T2(1,_8a,_fT)]));});return B(_16(_fD,new T2(1,_8b,_fS)));},1);return B(_16(_fL,_fR));},1);return new F(function(){return err(B(_16(_fE,_fQ)));});},_fV=function(_fW,_fX,_fY,_fZ,_g0){return new F(function(){return _fK(_fW,_fX,_g0,_fY,_fZ);});},_g1=function(_g2,_g3,_g4,_g5){var _g6=E(_g4);return new F(function(){return _fV(_g2,_g3,_g6.a,_g6.b,_g5);});},_g7=function(_g8,_g9,_ga,_gb){return new F(function(){return _g1(_gb,_ga,_g9,_g8);});},_gc=new T(function(){return B(unCStr("Int"));}),_gd=function(_ge,_gf){return new F(function(){return _g7(_fk,_gf,_ge,_gc);});},_gg=function(_gh,_gi){var _gj=E(_gh),_gk=E(_gj.a),_gl=E(_gi);if(_gk>_gl){return new F(function(){return _gd(_gl,_gj);});}else{if(_gl>E(_gj.b)){return new F(function(){return _gd(_gl,_gj);});}else{return _gl-_gk|0;}}},_gm=function(_gn,_go){if(_gn<=_go){var _gp=function(_gq){return new T2(1,_gq,new T(function(){if(_gq!=_go){return B(_gp(_gq+1|0));}else{return __Z;}}));};return new F(function(){return _gp(_gn);});}else{return __Z;}},_gr=function(_gs,_gt){return new F(function(){return _gm(E(_gs),E(_gt));});},_gu=function(_gv){var _gw=E(_gv);return new F(function(){return _gr(_gw.a,_gw.b);});},_gx=function(_gy){var _gz=E(_gy),_gA=E(_gz.a),_gB=E(_gz.b);return (_gA>_gB)?E(_fl):(_gB-_gA|0)+1|0;},_gC=function(_gD,_gE){return E(_gD)-E(_gE)|0;},_gF=function(_gG,_gH){return new F(function(){return _gC(_gH,E(_gG).a);});},_gI=function(_gJ,_gK){return E(_gJ)==E(_gK);},_gL=function(_gM,_gN){return E(_gM)!=E(_gN);},_gO=new T2(0,_gI,_gL),_gP=function(_gQ,_gR){var _gS=E(_gQ),_gT=E(_gR);return (_gS>_gT)?E(_gS):E(_gT);},_gU=function(_gV,_gW){var _gX=E(_gV),_gY=E(_gW);return (_gX>_gY)?E(_gY):E(_gX);},_gZ=function(_h0,_h1){return (_h0>=_h1)?(_h0!=_h1)?2:1:0;},_h2=function(_h3,_h4){return new F(function(){return _gZ(E(_h3),E(_h4));});},_h5=function(_h6,_h7){return E(_h6)>=E(_h7);},_h8=function(_h9,_ha){return E(_h9)>E(_ha);},_hb=function(_hc,_hd){return E(_hc)<=E(_hd);},_he=function(_hf,_hg){return E(_hf)<E(_hg);},_hh={_:0,a:_gO,b:_h2,c:_he,d:_hb,e:_h8,f:_h5,g:_gP,h:_gU},_hi={_:0,a:_hh,b:_gu,c:_gg,d:_gF,e:_f3,f:_gx,g:_f0},_hj=function(_hk,_hl){var _hm=E(_hk);if(!_hm._){return new T2(0,_M,_hl);}else{var _hn=B(A1(_hm.a,_hl)),_ho=B(_hj(_hm.b,_hn.b));return new T2(0,new T2(1,_hn.a,_ho.a),_ho.b);}},_hp=function(_hq,_hr,_hs){if(0>=_hq){return new F(function(){return _hj(_M,_hs);});}else{var _ht=function(_hu){var _hv=E(_hu);return (_hv==1)?E(new T2(1,_hr,_M)):new T2(1,_hr,new T(function(){return B(_ht(_hv-1|0));}));};return new F(function(){return _hj(B(_ht(_hq)),_hs);});}},_hw=function(_hx){return E(E(_hx).b);},_hy=function(_hz){return E(E(_hz).c);},_hA=function(_hB,_hC){var _hD=E(_hB);if(!_hD._){return __Z;}else{var _hE=E(_hC);return (_hE._==0)?__Z:new T2(1,new T2(0,_hD.a,_hE.a),new T(function(){return B(_hA(_hD.b,_hE.b));}));}},_hF=function(_hG,_hH,_hI,_hJ,_hK,_hL,_hM,_hN){var _hO=B(_93(_hI,_hJ,_hK,_hL,_hM,_hN)),_hP=E(_hO.a)&4294967295,_hQ=B(_hp(_hP,new T(function(){return B(_hw(_hG));}),_hO.b)),_hR=_hQ.a,_hS=new T(function(){var _hT=_hP-1|0;return B(A(_hy,[_hH,_hi,new T2(0,_eZ,_hT),new T(function(){if(0>_hT){return B(_hA(B(_gm(0,-1)),_hR));}else{var _hU=_hT+1|0;if(_hU>=0){return B(_hA(B(_gm(0,_hU-1|0)),_hR));}else{return E(_eY);}}})]));});return new T2(0,_hS,_hQ.b);},_hV=function(_hW,_hX,_hY,_hZ,_i0,_i1){var _i2=B(_93(_hW,_hX,_hY,_hZ,_i0,_i1)),_i3=E(_i2.b),_i4=B(_93(_i3.a,_i3.b,_i3.c,_i3.d,_i3.e,_i3.f)),_i5=E(_i4.b),_i6=B(_hF(_dc,_eW,_i5.a,_i5.b,_i5.c,_i5.d,_i5.e,_i5.f));return new T2(0,new T(function(){var _i7=E(_i6.a);return new T6(0,E(_i2.a)&4294967295,E(_i4.a)&4294967295,E(_i7.a),E(_i7.b),_i7.c,_i7.d);}),_i6.b);},_i8=function(_i9){var _ia=E(_i9),_ib=B(_hV(_ia.a,_ia.b,_ia.c,_ia.d,_ia.e,_ia.f));return new T2(0,_ib.a,_ib.b);},_ic=new T2(0,_0,E(_2I)),_id=function(_ie,_if,_ig,_ih,_ii,_ij){var _ik=new T(function(){var _il=_ii-1|0;if(0<=_il){var _im=function(_in){var _io=new T(function(){if(_in!=_il){var _ip=B(_im(_in+1|0));return new T2(0,_ip.a,E(_ip.b));}else{return E(_ic);}}),_iq=new T(function(){return E(B(_cS(_cK,new T(function(){return E(_ij[_in]);}))).b);}),_ir=function(_is){return new F(function(){return A1(_iq,new T(function(){return B(A1(E(_io).b,_is));}));});};return new T2(0,new T(function(){return E(E(_io).a);}),_ir);},_it=B(_im(0));return new T2(0,_it.a,E(_it.b));}else{return E(_ic);}}),_iu=new T(function(){if(_ig>_ih){return E(B(_3M(0)).b);}else{return E(B(_3M(((_ih-_ig|0)+1|0)>>>0)).b);}}),_iv=new T(function(){return E(B(_3M(_ie>>>0)).b);}),_iw=new T(function(){var _ix=B(_3M(_if>>>0));return new T2(0,_ix.a,E(_ix.b));}),_iy=function(_iz){var _iA=new T(function(){var _iB=new T(function(){return B(A1(_iu,new T(function(){return B(A1(E(_ik).b,_iz));})));});return B(A1(E(_iw).b,_iB));});return new F(function(){return A1(_iv,_iA);});};return new T2(0,new T(function(){return E(E(_ik).a);}),_iy);},_iC=function(_iD){var _iE=E(_iD),_iF=B(_id(_iE.a,_iE.b,E(_iE.c),E(_iE.d),_iE.e,_iE.f));return new T2(0,_iF.a,E(_iF.b));},_iG=new T2(0,_iC,_i8),_iH=function(_iI){var _iJ=E(_iI),_iK=B(_93(_iJ.a,_iJ.b,_iJ.c,_iJ.d,_iJ.e,_iJ.f));return new T2(0,new T(function(){return E(_iK.a)&4294967295;}),_iK.b);},_iL=function(_iM){var _iN=B(_3M(E(_iM)>>>0));return new T2(0,_iN.a,E(_iN.b));},_iO=new T2(0,_iL,_iH),_iP=function(_iQ,_iR){var _iS=E(_iR);return new T2(0,_iS.a,_iS.b);},_iT=function(_iU,_iV){return E(_iV).c;},_iW=function(_iX,_iY,_iZ,_j0){var _j1=function(_){var _j2=E(_iZ),_j3=_j2.d,_j4=_j3["byteLength"],_j5=newByteArr(_j4),_j6=_j5,_j7=memcpy(_j6,_j3,_j4>>>0),_j8=function(_j9,_){while(1){var _ja=E(_j9);if(!_ja._){return _0;}else{var _jb=E(_ja.a),_jc=E(_jb.a),_jd=_j6["v"]["i32"][_jc],_=_j6["v"]["i32"][_jc]=B(A2(_iY,_jd,_jb.b));_j9=_ja.b;continue;}}},_je=B(_j8(_j0,_));return new T4(0,E(_j2.a),E(_j2.b),_j2.c,_j6);};return new F(function(){return _df(_j1);});},_jf=new T(function(){return B(unCStr("Negative range size"));}),_jg=new T(function(){return B(err(_jf));}),_jh=function(_ji,_jj,_jk,_jl,_jm){var _jn=E(_jl),_jo=function(_){var _jp=B(A2(_dK,_ji,_jn)),_jq=newByteArr(imul(4,_jp)|0),_jr=_jq;if(_jp>=0){var _js=_jp-1|0,_jt=function(_){var _ju=function(_jv,_){while(1){var _jw=E(_jv);if(!_jw._){return _0;}else{var _jx=E(_jw.a),_jy=E(_jx.a),_jz=_jr["v"]["i32"][_jy],_=_jr["v"]["i32"][_jy]=B(A2(_jj,_jz,_jx.b));_jv=_jw.b;continue;}}},_jA=B(_ju(_jm,_));return new T4(0,E(_jn.a),E(_jn.b),_jp,_jr);};if(0<=_js){var _jB=function(_jC,_){while(1){var _=_jr["v"]["i32"][_jC]=E(_jk);if(_jC!=_js){var _jD=_jC+1|0;_jC=_jD;continue;}else{return _0;}}},_jE=B(_jB(0,_));return new F(function(){return _jt(_);});}else{return new F(function(){return _jt(_);});}}else{return E(_jg);}},_jF=E(_jo);return new F(function(){return _df(_jF);});},_jG=function(_jH,_jI,_jJ){var _jK=E(_jI),_jL=function(_){var _jM=B(A2(_dK,_jH,_jK)),_jN=newByteArr(imul(4,_jM)|0),_jO=_jN;if(_jM>=0){var _jP=_jM-1|0,_jQ=function(_){var _jR=function(_jS,_){while(1){var _jT=E(_jS);if(!_jT._){return _0;}else{var _jU=E(_jT.a),_=_jO["v"]["i32"][E(_jU.a)]=E(_jU.b);_jS=_jT.b;continue;}}},_jV=B(_jR(_jJ,_));return new T4(0,E(_jK.a),E(_jK.b),_jM,_jO);};if(0<=_jP){var _jW=function(_jX,_){while(1){var _=_jO["v"]["i32"][_jX]=0;if(_jX!=_jP){var _jY=_jX+1|0;_jX=_jY;continue;}else{return _0;}}},_jZ=B(_jW(0,_));return new F(function(){return _jQ(_);});}else{return new F(function(){return _jQ(_);});}}else{return E(_jg);}},_k0=E(_jL);return new F(function(){return _df(_k0);});},_k1=function(_k2,_k3,_k4){return E(_k3).d["v"]["i32"][E(_k4)];},_k5=function(_k6,_k7,_k8){var _k9=function(_){var _ka=E(_k7),_kb=_ka.d,_kc=_kb["byteLength"],_kd=newByteArr(_kc),_ke=_kd,_kf=memcpy(_ke,_kb,_kc>>>0),_kg=function(_kh,_){while(1){var _ki=E(_kh);if(!_ki._){return _0;}else{var _kj=E(_ki.a),_=_ke["v"]["i32"][E(_kj.a)]=E(_kj.b);_kh=_ki.b;continue;}}},_kk=B(_kg(_k8,_));return new T4(0,E(_ka.a),E(_ka.b),_ka.c,_ke);};return new F(function(){return _df(_k9);});},_kl={_:0,a:_iP,b:_iT,c:_jG,d:_k1,e:_k5,f:_iW,g:_jh},_km=function(_kn,_ko,_kp,_kq,_kr,_ks){var _kt=B(_9h(_kn,_ko,_kp,_kq,_kr,_ks)),_ku=E(_kt.b),_kv=B(_hF(_iO,_kl,_ku.a,_ku.b,_ku.c,_ku.d,_ku.e,_ku.f));return new T2(0,new T(function(){var _kw=E(_kv.a);return new T5(0,_kt.a,E(_kw.a),E(_kw.b),_kw.c,_kw.d);}),_kv.b);},_kx=function(_ky){var _kz=E(_ky),_kA=B(_km(_kz.a,_kz.b,_kz.c,_kz.d,_kz.e,_kz.f));return new T2(0,_kA.a,_kA.b);},_kB=function(_kC,_kD,_kE,_kF,_kG){var _kH=new T(function(){var _kI=_kF-1|0;if(0<=_kI){var _kJ=function(_kK){var _kL=new T(function(){if(_kK!=_kI){var _kM=B(_kJ(_kK+1|0));return new T2(0,_kM.a,E(_kM.b));}else{return E(_ic);}}),_kN=new T(function(){return E(B(_3M(_kG["v"]["i32"][_kK]>>>0)).b);}),_kO=function(_kP){return new F(function(){return A1(_kN,new T(function(){return B(A1(E(_kL).b,_kP));}));});};return new T2(0,new T(function(){return E(E(_kL).a);}),_kO);},_kQ=B(_kJ(0));return new T2(0,_kQ.a,E(_kQ.b));}else{return E(_ic);}}),_kR=new T(function(){if(_kD>_kE){return E(B(_3M(0)).b);}else{return E(B(_3M(((_kE-_kD|0)+1|0)>>>0)).b);}}),_kS=new T(function(){return E(B(_6x(_kC)).b);}),_kT=function(_kU){var _kV=new T(function(){return B(A1(_kR,new T(function(){return B(A1(E(_kH).b,_kU));})));});return new F(function(){return A1(_kS,_kV);});};return new T2(0,new T(function(){return E(E(_kH).a);}),_kT);},_kW=function(_kX){var _kY=E(_kX),_kZ=B(_kB(_kY.a,E(_kY.b),E(_kY.c),_kY.d,_kY.e));return new T2(0,_kZ.a,E(_kZ.b));},_l0=new T2(0,_kW,_kx),_l1=new T(function(){return B(unCStr("This file was compiled with different version of GF"));}),_l2=function(_l3,_l4){return new F(function(){return _8q(_l3,_l4);});},_l5=function(_l6){return new F(function(){return _l2(_l1,_l6);});},_l7=function(_l8){return new F(function(){return _gm(E(_l8),2147483647);});},_l9=function(_la,_lb,_lc){if(_lc<=_lb){var _ld=new T(function(){var _le=_lb-_la|0,_lf=function(_lg){return (_lg>=(_lc-_le|0))?new T2(1,_lg,new T(function(){return B(_lf(_lg+_le|0));})):new T2(1,_lg,_M);};return B(_lf(_lb));});return new T2(1,_la,_ld);}else{return (_lc<=_la)?new T2(1,_la,_M):__Z;}},_lh=function(_li,_lj,_lk){if(_lk>=_lj){var _ll=new T(function(){var _lm=_lj-_li|0,_ln=function(_lo){return (_lo<=(_lk-_lm|0))?new T2(1,_lo,new T(function(){return B(_ln(_lo+_lm|0));})):new T2(1,_lo,_M);};return B(_ln(_lj));});return new T2(1,_li,_ll);}else{return (_lk>=_li)?new T2(1,_li,_M):__Z;}},_lp=function(_lq,_lr){if(_lr<_lq){return new F(function(){return _l9(_lq,_lr,-2147483648);});}else{return new F(function(){return _lh(_lq,_lr,2147483647);});}},_ls=function(_lt,_lu){return new F(function(){return _lp(E(_lt),E(_lu));});},_lv=function(_lw,_lx,_ly){if(_lx<_lw){return new F(function(){return _l9(_lw,_lx,_ly);});}else{return new F(function(){return _lh(_lw,_lx,_ly);});}},_lz=function(_lA,_lB,_lC){return new F(function(){return _lv(E(_lA),E(_lB),E(_lC));});},_lD=function(_lE){return E(_lE);},_lF=new T(function(){return B(unCStr("Prelude.Enum.pred{Int}: tried to take `pred\' of minBound"));}),_lG=new T(function(){return B(err(_lF));}),_lH=function(_lI){var _lJ=E(_lI);return (_lJ==(-2147483648))?E(_lG):_lJ-1|0;},_lK=new T(function(){return B(unCStr("Prelude.Enum.succ{Int}: tried to take `succ\' of maxBound"));}),_lL=new T(function(){return B(err(_lK));}),_lM=function(_lN){var _lO=E(_lN);return (_lO==2147483647)?E(_lL):_lO+1|0;},_lP={_:0,a:_lM,b:_lH,c:_lD,d:_lD,e:_l7,f:_ls,g:_gr,h:_lz},_lQ=function(_lR,_lS){if(_lR<=0){if(_lR>=0){return new F(function(){return quot(_lR,_lS);});}else{if(_lS<=0){return new F(function(){return quot(_lR,_lS);});}else{return quot(_lR+1|0,_lS)-1|0;}}}else{if(_lS>=0){if(_lR>=0){return new F(function(){return quot(_lR,_lS);});}else{if(_lS<=0){return new F(function(){return quot(_lR,_lS);});}else{return quot(_lR+1|0,_lS)-1|0;}}}else{return quot(_lR-1|0,_lS)-1|0;}}},_lT=new T(function(){return B(unCStr("base"));}),_lU=new T(function(){return B(unCStr("GHC.Exception"));}),_lV=new T(function(){return B(unCStr("ArithException"));}),_lW=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_lT,_lU,_lV),_lX=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_lW,_M,_M),_lY=function(_lZ){return E(_lX);},_m0=function(_m1){var _m2=E(_m1);return new F(function(){return _S(B(_Q(_m2.a)),_lY,_m2.b);});},_m3=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_m4=new T(function(){return B(unCStr("denormal"));}),_m5=new T(function(){return B(unCStr("divide by zero"));}),_m6=new T(function(){return B(unCStr("loss of precision"));}),_m7=new T(function(){return B(unCStr("arithmetic underflow"));}),_m8=new T(function(){return B(unCStr("arithmetic overflow"));}),_m9=function(_ma,_mb){switch(E(_ma)){case 0:return new F(function(){return _16(_m8,_mb);});break;case 1:return new F(function(){return _16(_m7,_mb);});break;case 2:return new F(function(){return _16(_m6,_mb);});break;case 3:return new F(function(){return _16(_m5,_mb);});break;case 4:return new F(function(){return _16(_m4,_mb);});break;default:return new F(function(){return _16(_m3,_mb);});}},_mc=function(_md){return new F(function(){return _m9(_md,_M);});},_me=function(_mf,_mg,_mh){return new F(function(){return _m9(_mg,_mh);});},_mi=function(_mj,_mk){return new F(function(){return _2a(_m9,_mj,_mk);});},_ml=new T3(0,_me,_mc,_mi),_mm=new T(function(){return new T5(0,_lY,_ml,_mn,_m0,_mc);}),_mn=function(_mo){return new T2(0,_mm,_mo);},_mp=3,_mq=new T(function(){return B(_mn(_mp));}),_mr=new T(function(){return die(_mq);}),_ms=0,_mt=new T(function(){return B(_mn(_ms));}),_mu=new T(function(){return die(_mt);}),_mv=function(_mw,_mx){var _my=E(_mx);switch(_my){case -1:var _mz=E(_mw);if(_mz==(-2147483648)){return E(_mu);}else{return new F(function(){return _lQ(_mz,-1);});}break;case 0:return E(_mr);default:return new F(function(){return _lQ(_mw,_my);});}},_mA=function(_mB,_mC){return new F(function(){return _mv(E(_mB),E(_mC));});},_mD=0,_mE=new T2(0,_mu,_mD),_mF=function(_mG,_mH){var _mI=E(_mG),_mJ=E(_mH);switch(_mJ){case -1:var _mK=E(_mI);if(_mK==(-2147483648)){return E(_mE);}else{if(_mK<=0){if(_mK>=0){var _mL=quotRemI(_mK,-1);return new T2(0,_mL.a,_mL.b);}else{var _mM=quotRemI(_mK,-1);return new T2(0,_mM.a,_mM.b);}}else{var _mN=quotRemI(_mK-1|0,-1);return new T2(0,_mN.a-1|0,(_mN.b+(-1)|0)+1|0);}}break;case 0:return E(_mr);default:if(_mI<=0){if(_mI>=0){var _mO=quotRemI(_mI,_mJ);return new T2(0,_mO.a,_mO.b);}else{if(_mJ<=0){var _mP=quotRemI(_mI,_mJ);return new T2(0,_mP.a,_mP.b);}else{var _mQ=quotRemI(_mI+1|0,_mJ);return new T2(0,_mQ.a-1|0,(_mQ.b+_mJ|0)-1|0);}}}else{if(_mJ>=0){if(_mI>=0){var _mR=quotRemI(_mI,_mJ);return new T2(0,_mR.a,_mR.b);}else{if(_mJ<=0){var _mS=quotRemI(_mI,_mJ);return new T2(0,_mS.a,_mS.b);}else{var _mT=quotRemI(_mI+1|0,_mJ);return new T2(0,_mT.a-1|0,(_mT.b+_mJ|0)-1|0);}}}else{var _mU=quotRemI(_mI-1|0,_mJ);return new T2(0,_mU.a-1|0,(_mU.b+_mJ|0)+1|0);}}}},_mV=function(_mW,_mX){var _mY=_mW%_mX;if(_mW<=0){if(_mW>=0){return E(_mY);}else{if(_mX<=0){return E(_mY);}else{var _mZ=E(_mY);return (_mZ==0)?0:_mZ+_mX|0;}}}else{if(_mX>=0){if(_mW>=0){return E(_mY);}else{if(_mX<=0){return E(_mY);}else{var _n0=E(_mY);return (_n0==0)?0:_n0+_mX|0;}}}else{var _n1=E(_mY);return (_n1==0)?0:_n1+_mX|0;}}},_n2=function(_n3,_n4){var _n5=E(_n4);switch(_n5){case -1:return E(_mD);case 0:return E(_mr);default:return new F(function(){return _mV(E(_n3),_n5);});}},_n6=function(_n7,_n8){var _n9=E(_n7),_na=E(_n8);switch(_na){case -1:var _nb=E(_n9);if(_nb==(-2147483648)){return E(_mu);}else{return new F(function(){return quot(_nb,-1);});}break;case 0:return E(_mr);default:return new F(function(){return quot(_n9,_na);});}},_nc=function(_nd,_ne){var _nf=E(_nd),_ng=E(_ne);switch(_ng){case -1:var _nh=E(_nf);if(_nh==(-2147483648)){return E(_mE);}else{var _ni=quotRemI(_nh,-1);return new T2(0,_ni.a,_ni.b);}break;case 0:return E(_mr);default:var _nj=quotRemI(_nf,_ng);return new T2(0,_nj.a,_nj.b);}},_nk=function(_nl,_nm){var _nn=E(_nm);switch(_nn){case -1:return E(_mD);case 0:return E(_mr);default:return E(_nl)%_nn;}},_no=function(_np){return new F(function(){return _8h(E(_np));});},_nq=new T1(0,1),_nr=function(_ns){return new T2(0,E(B(_8h(E(_ns)))),E(_nq));},_nt=function(_nu,_nv){return imul(E(_nu),E(_nv))|0;},_nw=function(_nx,_ny){return E(_nx)+E(_ny)|0;},_nz=function(_nA){var _nB=E(_nA);return (_nB<0)? -_nB:E(_nB);},_nC=function(_nD){var _nE=E(_nD);if(!_nE._){return E(_nE.a);}else{return new F(function(){return I_toInt(_nE.a);});}},_nF=function(_nG){return new F(function(){return _nC(_nG);});},_nH=function(_nI){return  -E(_nI);},_nJ=-1,_nK=0,_nL=1,_nM=function(_nN){var _nO=E(_nN);return (_nO>=0)?(E(_nO)==0)?E(_nK):E(_nL):E(_nJ);},_nP={_:0,a:_nw,b:_gC,c:_nt,d:_nH,e:_nz,f:_nM,g:_nF},_nQ=new T2(0,_gI,_gL),_nR={_:0,a:_nQ,b:_h2,c:_he,d:_hb,e:_h8,f:_h5,g:_gP,h:_gU},_nS=new T3(0,_nP,_nR,_nr),_nT={_:0,a:_nS,b:_lP,c:_n6,d:_nk,e:_mA,f:_n2,g:_nc,h:_mF,i:_no},_nU={_:0,a:_lM,b:_lH,c:_lD,d:_lD,e:_l7,f:_ls,g:_gr,h:_lz},_nV={_:0,a:_nw,b:_gC,c:_nt,d:_nH,e:_nz,f:_nM,g:_nF},_nW=new T3(0,_nV,_hh,_nr),_nX={_:0,a:_nW,b:_nU,c:_n6,d:_nk,e:_mA,f:_n2,g:_nc,h:_mF,i:_no},_nY=new T1(0,2),_nZ=function(_o0){return E(E(_o0).a);},_o1=function(_o2){return E(E(_o2).a);},_o3=function(_o4,_o5){while(1){var _o6=E(_o4);if(!_o6._){var _o7=_o6.a,_o8=E(_o5);if(!_o8._){var _o9=_o8.a;if(!(imul(_o7,_o9)|0)){return new T1(0,imul(_o7,_o9)|0);}else{_o4=new T1(1,I_fromInt(_o7));_o5=new T1(1,I_fromInt(_o9));continue;}}else{_o4=new T1(1,I_fromInt(_o7));_o5=_o8;continue;}}else{var _oa=E(_o5);if(!_oa._){_o4=_o6;_o5=new T1(1,I_fromInt(_oa.a));continue;}else{return new T1(1,I_mul(_o6.a,_oa.a));}}}},_ob=function(_oc,_od,_oe){while(1){if(!(_od%2)){var _of=B(_o3(_oc,_oc)),_og=quot(_od,2);_oc=_of;_od=_og;continue;}else{var _oh=E(_od);if(_oh==1){return new F(function(){return _o3(_oc,_oe);});}else{var _of=B(_o3(_oc,_oc)),_oi=B(_o3(_oc,_oe));_oc=_of;_od=quot(_oh-1|0,2);_oe=_oi;continue;}}}},_oj=function(_ok,_ol){while(1){if(!(_ol%2)){var _om=B(_o3(_ok,_ok)),_on=quot(_ol,2);_ok=_om;_ol=_on;continue;}else{var _oo=E(_ol);if(_oo==1){return E(_ok);}else{return new F(function(){return _ob(B(_o3(_ok,_ok)),quot(_oo-1|0,2),_ok);});}}}},_op=function(_oq){return E(E(_oq).c);},_or=function(_os){return E(E(_os).a);},_ot=function(_ou){return E(E(_ou).b);},_ov=function(_ow){return E(E(_ow).b);},_ox=function(_oy){return E(E(_oy).c);},_oz=function(_oA){return E(E(_oA).a);},_oB=new T1(0,0),_oC=new T1(0,2),_oD=function(_oE){return E(E(_oE).g);},_oF=function(_oG){return E(E(_oG).d);},_oH=function(_oI,_oJ){var _oK=B(_nZ(_oI)),_oL=new T(function(){return B(_o1(_oK));}),_oM=new T(function(){return B(A3(_oF,_oI,_oJ,new T(function(){return B(A2(_oD,_oL,_oC));})));});return new F(function(){return A3(_oz,B(_or(B(_ot(_oK)))),_oM,new T(function(){return B(A2(_oD,_oL,_oB));}));});},_oN=new T(function(){return B(unCStr("Negative exponent"));}),_oO=new T(function(){return B(err(_oN));}),_oP=function(_oQ){return E(E(_oQ).c);},_oR=function(_oS,_oT,_oU,_oV){var _oW=B(_nZ(_oT)),_oX=new T(function(){return B(_o1(_oW));}),_oY=B(_ot(_oW));if(!B(A3(_ox,_oY,_oV,new T(function(){return B(A2(_oD,_oX,_oB));})))){if(!B(A3(_oz,B(_or(_oY)),_oV,new T(function(){return B(A2(_oD,_oX,_oB));})))){var _oZ=new T(function(){return B(A2(_oD,_oX,_oC));}),_p0=new T(function(){return B(A2(_oD,_oX,_nq));}),_p1=B(_or(_oY)),_p2=function(_p3,_p4,_p5){while(1){var _p6=B((function(_p7,_p8,_p9){if(!B(_oH(_oT,_p8))){if(!B(A3(_oz,_p1,_p8,_p0))){var _pa=new T(function(){return B(A3(_oP,_oT,new T(function(){return B(A3(_ov,_oX,_p8,_p0));}),_oZ));});_p3=new T(function(){return B(A3(_op,_oS,_p7,_p7));});_p4=_pa;_p5=new T(function(){return B(A3(_op,_oS,_p7,_p9));});return __continue;}else{return new F(function(){return A3(_op,_oS,_p7,_p9);});}}else{var _pb=_p9;_p3=new T(function(){return B(A3(_op,_oS,_p7,_p7));});_p4=new T(function(){return B(A3(_oP,_oT,_p8,_oZ));});_p5=_pb;return __continue;}})(_p3,_p4,_p5));if(_p6!=__continue){return _p6;}}},_pc=function(_pd,_pe){while(1){var _pf=B((function(_pg,_ph){if(!B(_oH(_oT,_ph))){if(!B(A3(_oz,_p1,_ph,_p0))){var _pi=new T(function(){return B(A3(_oP,_oT,new T(function(){return B(A3(_ov,_oX,_ph,_p0));}),_oZ));});return new F(function(){return _p2(new T(function(){return B(A3(_op,_oS,_pg,_pg));}),_pi,_pg);});}else{return E(_pg);}}else{_pd=new T(function(){return B(A3(_op,_oS,_pg,_pg));});_pe=new T(function(){return B(A3(_oP,_oT,_ph,_oZ));});return __continue;}})(_pd,_pe));if(_pf!=__continue){return _pf;}}};return new F(function(){return _pc(_oU,_oV);});}else{return new F(function(){return A2(_oD,_oS,_nq);});}}else{return E(_oO);}},_pj=new T(function(){return B(err(_oN));}),_pk=function(_pl){var _pm=I_decodeDouble(_pl);return new T2(0,new T1(1,_pm.b),_pm.a);},_pn=function(_po,_pp){var _pq=E(_po);return (_pq._==0)?_pq.a*Math.pow(2,_pp):I_toNumber(_pq.a)*Math.pow(2,_pp);},_pr=function(_ps,_pt){var _pu=E(_ps);if(!_pu._){var _pv=_pu.a,_pw=E(_pt);return (_pw._==0)?_pv==_pw.a:(I_compareInt(_pw.a,_pv)==0)?true:false;}else{var _px=_pu.a,_py=E(_pt);return (_py._==0)?(I_compareInt(_px,_py.a)==0)?true:false:(I_compare(_px,_py.a)==0)?true:false;}},_pz=function(_pA,_pB){while(1){var _pC=E(_pA);if(!_pC._){var _pD=E(_pC.a);if(_pD==(-2147483648)){_pA=new T1(1,I_fromInt(-2147483648));continue;}else{var _pE=E(_pB);if(!_pE._){var _pF=_pE.a;return new T2(0,new T1(0,quot(_pD,_pF)),new T1(0,_pD%_pF));}else{_pA=new T1(1,I_fromInt(_pD));_pB=_pE;continue;}}}else{var _pG=E(_pB);if(!_pG._){_pA=_pC;_pB=new T1(1,I_fromInt(_pG.a));continue;}else{var _pH=I_quotRem(_pC.a,_pG.a);return new T2(0,new T1(1,_pH.a),new T1(1,_pH.b));}}}},_pI=0,_pJ=new T1(0,0),_pK=function(_pL,_pM){var _pN=B(_pk(_pM)),_pO=_pN.a,_pP=_pN.b,_pQ=new T(function(){return B(_o1(new T(function(){return B(_nZ(_pL));})));});if(_pP<0){var _pR= -_pP;if(_pR>=0){var _pS=E(_pR);if(!_pS){var _pT=E(_nq);}else{var _pT=B(_oj(_nY,_pS));}if(!B(_pr(_pT,_pJ))){var _pU=B(_pz(_pO,_pT));return new T2(0,new T(function(){return B(A2(_oD,_pQ,_pU.a));}),new T(function(){return B(_pn(_pU.b,_pP));}));}else{return E(_mr);}}else{return E(_pj);}}else{var _pV=new T(function(){var _pW=new T(function(){return B(_oR(_pQ,_nX,new T(function(){return B(A2(_oD,_pQ,_nY));}),_pP));});return B(A3(_op,_pQ,new T(function(){return B(A2(_oD,_pQ,_pO));}),_pW));});return new T2(0,_pV,_pI);}},_pX=function(_pY){var _pZ=E(_pY);if(!_pZ._){return _pZ.a;}else{return new F(function(){return I_toNumber(_pZ.a);});}},_q0=function(_q1,_q2){var _q3=B(_pK(_nT,Math.pow(B(_pX(_q1)),_q2))),_q4=_q3.a;return (E(_q3.b)>=0)?E(_q4):E(_q4)-1|0;},_q5=new T1(0,1),_q6=new T1(0,0),_q7=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_q8=new T(function(){return B(err(_q7));}),_q9=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_qa=new T(function(){return B(err(_q9));}),_qb=new T(function(){return B(unCStr("base"));}),_qc=new T(function(){return B(unCStr("Control.Exception.Base"));}),_qd=new T(function(){return B(unCStr("PatternMatchFail"));}),_qe=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_qb,_qc,_qd),_qf=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_qe,_M,_M),_qg=function(_qh){return E(_qf);},_qi=function(_qj){var _qk=E(_qj);return new F(function(){return _S(B(_Q(_qk.a)),_qg,_qk.b);});},_ql=function(_qm){return E(E(_qm).a);},_qn=function(_qo){return new T2(0,_qp,_qo);},_qq=function(_qr,_qs){return new F(function(){return _16(E(_qr).a,_qs);});},_qt=function(_qu,_qv){return new F(function(){return _2a(_qq,_qu,_qv);});},_qw=function(_qx,_qy,_qz){return new F(function(){return _16(E(_qy).a,_qz);});},_qA=new T3(0,_qw,_ql,_qt),_qp=new T(function(){return new T5(0,_qg,_qA,_qn,_qi,_ql);}),_qB=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_qC=function(_qD,_qE){return new F(function(){return die(new T(function(){return B(A2(_2q,_qE,_qD));}));});},_qF=function(_qG,_mo){return new F(function(){return _qC(_qG,_mo);});},_qH=function(_qI,_qJ){var _qK=E(_qJ);if(!_qK._){return new T2(0,_M,_M);}else{var _qL=_qK.a;if(!B(A1(_qI,_qL))){return new T2(0,_M,_qK);}else{var _qM=new T(function(){var _qN=B(_qH(_qI,_qK.b));return new T2(0,_qN.a,_qN.b);});return new T2(0,new T2(1,_qL,new T(function(){return E(E(_qM).a);})),new T(function(){return E(E(_qM).b);}));}}},_qO=32,_qP=new T(function(){return B(unCStr("\n"));}),_qQ=function(_qR){return (E(_qR)==124)?false:true;},_qS=function(_qT,_qU){var _qV=B(_qH(_qQ,B(unCStr(_qT)))),_qW=_qV.a,_qX=function(_qY,_qZ){var _r0=new T(function(){var _r1=new T(function(){return B(_16(_qU,new T(function(){return B(_16(_qZ,_qP));},1)));});return B(unAppCStr(": ",_r1));},1);return new F(function(){return _16(_qY,_r0);});},_r2=E(_qV.b);if(!_r2._){return new F(function(){return _qX(_qW,_M);});}else{if(E(_r2.a)==124){return new F(function(){return _qX(_qW,new T2(1,_qO,_r2.b));});}else{return new F(function(){return _qX(_qW,_M);});}}},_r3=function(_r4){return new F(function(){return _qF(new T1(0,new T(function(){return B(_qS(_r4,_qB));})),_qp);});},_r5=new T(function(){return B(_r3("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_r6=function(_r7,_r8){while(1){var _r9=B((function(_ra,_rb){var _rc=E(_ra);switch(_rc._){case 0:var _rd=E(_rb);if(!_rd._){return __Z;}else{_r7=B(A1(_rc.a,_rd.a));_r8=_rd.b;return __continue;}break;case 1:var _re=B(A1(_rc.a,_rb)),_rf=_rb;_r7=_re;_r8=_rf;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_rc.a,_rb),new T(function(){return B(_r6(_rc.b,_rb));}));default:return E(_rc.a);}})(_r7,_r8));if(_r9!=__continue){return _r9;}}},_rg=function(_rh,_ri){var _rj=function(_rk){var _rl=E(_ri);if(_rl._==3){return new T2(3,_rl.a,new T(function(){return B(_rg(_rh,_rl.b));}));}else{var _rm=E(_rh);if(_rm._==2){return E(_rl);}else{var _rn=E(_rl);if(_rn._==2){return E(_rm);}else{var _ro=function(_rp){var _rq=E(_rn);if(_rq._==4){var _rr=function(_rs){return new T1(4,new T(function(){return B(_16(B(_r6(_rm,_rs)),_rq.a));}));};return new T1(1,_rr);}else{var _rt=E(_rm);if(_rt._==1){var _ru=_rt.a,_rv=E(_rq);if(!_rv._){return new T1(1,function(_rw){return new F(function(){return _rg(B(A1(_ru,_rw)),_rv);});});}else{var _rx=function(_ry){return new F(function(){return _rg(B(A1(_ru,_ry)),new T(function(){return B(A1(_rv.a,_ry));}));});};return new T1(1,_rx);}}else{var _rz=E(_rq);if(!_rz._){return E(_r5);}else{var _rA=function(_rB){return new F(function(){return _rg(_rt,new T(function(){return B(A1(_rz.a,_rB));}));});};return new T1(1,_rA);}}}},_rC=E(_rm);switch(_rC._){case 1:var _rD=E(_rn);if(_rD._==4){var _rE=function(_rF){return new T1(4,new T(function(){return B(_16(B(_r6(B(A1(_rC.a,_rF)),_rF)),_rD.a));}));};return new T1(1,_rE);}else{return new F(function(){return _ro(_);});}break;case 4:var _rG=_rC.a,_rH=E(_rn);switch(_rH._){case 0:var _rI=function(_rJ){var _rK=new T(function(){return B(_16(_rG,new T(function(){return B(_r6(_rH,_rJ));},1)));});return new T1(4,_rK);};return new T1(1,_rI);case 1:var _rL=function(_rM){var _rN=new T(function(){return B(_16(_rG,new T(function(){return B(_r6(B(A1(_rH.a,_rM)),_rM));},1)));});return new T1(4,_rN);};return new T1(1,_rL);default:return new T1(4,new T(function(){return B(_16(_rG,_rH.a));}));}break;default:return new F(function(){return _ro(_);});}}}}},_rO=E(_rh);switch(_rO._){case 0:var _rP=E(_ri);if(!_rP._){var _rQ=function(_rR){return new F(function(){return _rg(B(A1(_rO.a,_rR)),new T(function(){return B(A1(_rP.a,_rR));}));});};return new T1(0,_rQ);}else{return new F(function(){return _rj(_);});}break;case 3:return new T2(3,_rO.a,new T(function(){return B(_rg(_rO.b,_ri));}));default:return new F(function(){return _rj(_);});}},_rS=new T(function(){return B(unCStr("("));}),_rT=new T(function(){return B(unCStr(")"));}),_rU=function(_rV,_rW){while(1){var _rX=E(_rV);if(!_rX._){return (E(_rW)._==0)?true:false;}else{var _rY=E(_rW);if(!_rY._){return false;}else{if(E(_rX.a)!=E(_rY.a)){return false;}else{_rV=_rX.b;_rW=_rY.b;continue;}}}}},_rZ=function(_s0,_s1){return E(_s0)!=E(_s1);},_s2=function(_s3,_s4){return E(_s3)==E(_s4);},_s5=new T2(0,_s2,_rZ),_s6=function(_s7,_s8){while(1){var _s9=E(_s7);if(!_s9._){return (E(_s8)._==0)?true:false;}else{var _sa=E(_s8);if(!_sa._){return false;}else{if(E(_s9.a)!=E(_sa.a)){return false;}else{_s7=_s9.b;_s8=_sa.b;continue;}}}}},_sb=function(_sc,_sd){return (!B(_s6(_sc,_sd)))?true:false;},_se=new T2(0,_s6,_sb),_sf=function(_sg,_sh){var _si=E(_sg);switch(_si._){case 0:return new T1(0,function(_sj){return new F(function(){return _sf(B(A1(_si.a,_sj)),_sh);});});case 1:return new T1(1,function(_sk){return new F(function(){return _sf(B(A1(_si.a,_sk)),_sh);});});case 2:return new T0(2);case 3:return new F(function(){return _rg(B(A1(_sh,_si.a)),new T(function(){return B(_sf(_si.b,_sh));}));});break;default:var _sl=function(_sm){var _sn=E(_sm);if(!_sn._){return __Z;}else{var _so=E(_sn.a);return new F(function(){return _16(B(_r6(B(A1(_sh,_so.a)),_so.b)),new T(function(){return B(_sl(_sn.b));},1));});}},_sp=B(_sl(_si.a));return (_sp._==0)?new T0(2):new T1(4,_sp);}},_sq=new T0(2),_sr=function(_ss){return new T2(3,_ss,_sq);},_st=function(_su,_sv){var _sw=E(_su);if(!_sw){return new F(function(){return A1(_sv,_0);});}else{var _sx=new T(function(){return B(_st(_sw-1|0,_sv));});return new T1(0,function(_sy){return E(_sx);});}},_sz=function(_sA,_sB,_sC){var _sD=new T(function(){return B(A1(_sA,_sr));}),_sE=function(_sF,_sG,_sH,_sI){while(1){var _sJ=B((function(_sK,_sL,_sM,_sN){var _sO=E(_sK);switch(_sO._){case 0:var _sP=E(_sL);if(!_sP._){return new F(function(){return A1(_sB,_sN);});}else{var _sQ=_sM+1|0,_sR=_sN;_sF=B(A1(_sO.a,_sP.a));_sG=_sP.b;_sH=_sQ;_sI=_sR;return __continue;}break;case 1:var _sS=B(A1(_sO.a,_sL)),_sT=_sL,_sQ=_sM,_sR=_sN;_sF=_sS;_sG=_sT;_sH=_sQ;_sI=_sR;return __continue;case 2:return new F(function(){return A1(_sB,_sN);});break;case 3:var _sU=new T(function(){return B(_sf(_sO,_sN));});return new F(function(){return _st(_sM,function(_sV){return E(_sU);});});break;default:return new F(function(){return _sf(_sO,_sN);});}})(_sF,_sG,_sH,_sI));if(_sJ!=__continue){return _sJ;}}};return function(_sW){return new F(function(){return _sE(_sD,_sW,0,_sC);});};},_sX=function(_sY){return new F(function(){return A1(_sY,_M);});},_sZ=function(_t0,_t1){var _t2=function(_t3){var _t4=E(_t3);if(!_t4._){return E(_sX);}else{var _t5=_t4.a;if(!B(A1(_t0,_t5))){return E(_sX);}else{var _t6=new T(function(){return B(_t2(_t4.b));}),_t7=function(_t8){var _t9=new T(function(){return B(A1(_t6,function(_ta){return new F(function(){return A1(_t8,new T2(1,_t5,_ta));});}));});return new T1(0,function(_tb){return E(_t9);});};return E(_t7);}}};return function(_tc){return new F(function(){return A2(_t2,_tc,_t1);});};},_td=new T0(6),_te=new T(function(){return B(unCStr("valDig: Bad base"));}),_tf=new T(function(){return B(err(_te));}),_tg=function(_th,_ti){var _tj=function(_tk,_tl){var _tm=E(_tk);if(!_tm._){var _tn=new T(function(){return B(A1(_tl,_M));});return function(_to){return new F(function(){return A1(_to,_tn);});};}else{var _tp=E(_tm.a),_tq=function(_tr){var _ts=new T(function(){return B(_tj(_tm.b,function(_tt){return new F(function(){return A1(_tl,new T2(1,_tr,_tt));});}));}),_tu=function(_tv){var _tw=new T(function(){return B(A1(_ts,_tv));});return new T1(0,function(_tx){return E(_tw);});};return E(_tu);};switch(E(_th)){case 8:if(48>_tp){var _ty=new T(function(){return B(A1(_tl,_M));});return function(_tz){return new F(function(){return A1(_tz,_ty);});};}else{if(_tp>55){var _tA=new T(function(){return B(A1(_tl,_M));});return function(_tB){return new F(function(){return A1(_tB,_tA);});};}else{return new F(function(){return _tq(_tp-48|0);});}}break;case 10:if(48>_tp){var _tC=new T(function(){return B(A1(_tl,_M));});return function(_tD){return new F(function(){return A1(_tD,_tC);});};}else{if(_tp>57){var _tE=new T(function(){return B(A1(_tl,_M));});return function(_tF){return new F(function(){return A1(_tF,_tE);});};}else{return new F(function(){return _tq(_tp-48|0);});}}break;case 16:if(48>_tp){if(97>_tp){if(65>_tp){var _tG=new T(function(){return B(A1(_tl,_M));});return function(_tH){return new F(function(){return A1(_tH,_tG);});};}else{if(_tp>70){var _tI=new T(function(){return B(A1(_tl,_M));});return function(_tJ){return new F(function(){return A1(_tJ,_tI);});};}else{return new F(function(){return _tq((_tp-65|0)+10|0);});}}}else{if(_tp>102){if(65>_tp){var _tK=new T(function(){return B(A1(_tl,_M));});return function(_tL){return new F(function(){return A1(_tL,_tK);});};}else{if(_tp>70){var _tM=new T(function(){return B(A1(_tl,_M));});return function(_tN){return new F(function(){return A1(_tN,_tM);});};}else{return new F(function(){return _tq((_tp-65|0)+10|0);});}}}else{return new F(function(){return _tq((_tp-97|0)+10|0);});}}}else{if(_tp>57){if(97>_tp){if(65>_tp){var _tO=new T(function(){return B(A1(_tl,_M));});return function(_tP){return new F(function(){return A1(_tP,_tO);});};}else{if(_tp>70){var _tQ=new T(function(){return B(A1(_tl,_M));});return function(_tR){return new F(function(){return A1(_tR,_tQ);});};}else{return new F(function(){return _tq((_tp-65|0)+10|0);});}}}else{if(_tp>102){if(65>_tp){var _tS=new T(function(){return B(A1(_tl,_M));});return function(_tT){return new F(function(){return A1(_tT,_tS);});};}else{if(_tp>70){var _tU=new T(function(){return B(A1(_tl,_M));});return function(_tV){return new F(function(){return A1(_tV,_tU);});};}else{return new F(function(){return _tq((_tp-65|0)+10|0);});}}}else{return new F(function(){return _tq((_tp-97|0)+10|0);});}}}else{return new F(function(){return _tq(_tp-48|0);});}}break;default:return E(_tf);}}},_tW=function(_tX){var _tY=E(_tX);if(!_tY._){return new T0(2);}else{return new F(function(){return A1(_ti,_tY);});}};return function(_tZ){return new F(function(){return A3(_tj,_tZ,_2I,_tW);});};},_u0=16,_u1=8,_u2=function(_u3){var _u4=function(_u5){return new F(function(){return A1(_u3,new T1(5,new T2(0,_u1,_u5)));});},_u6=function(_u7){return new F(function(){return A1(_u3,new T1(5,new T2(0,_u0,_u7)));});},_u8=function(_u9){switch(E(_u9)){case 79:return new T1(1,B(_tg(_u1,_u4)));case 88:return new T1(1,B(_tg(_u0,_u6)));case 111:return new T1(1,B(_tg(_u1,_u4)));case 120:return new T1(1,B(_tg(_u0,_u6)));default:return new T0(2);}};return function(_ua){return (E(_ua)==48)?E(new T1(0,_u8)):new T0(2);};},_ub=function(_uc){return new T1(0,B(_u2(_uc)));},_ud=function(_ue){return new F(function(){return A1(_ue,_2s);});},_uf=function(_ug){return new F(function(){return A1(_ug,_2s);});},_uh=10,_ui=new T1(0,1),_uj=new T1(0,2147483647),_uk=function(_ul,_um){while(1){var _un=E(_ul);if(!_un._){var _uo=_un.a,_up=E(_um);if(!_up._){var _uq=_up.a,_ur=addC(_uo,_uq);if(!E(_ur.b)){return new T1(0,_ur.a);}else{_ul=new T1(1,I_fromInt(_uo));_um=new T1(1,I_fromInt(_uq));continue;}}else{_ul=new T1(1,I_fromInt(_uo));_um=_up;continue;}}else{var _us=E(_um);if(!_us._){_ul=_un;_um=new T1(1,I_fromInt(_us.a));continue;}else{return new T1(1,I_add(_un.a,_us.a));}}}},_ut=new T(function(){return B(_uk(_uj,_ui));}),_uu=function(_uv){var _uw=E(_uv);if(!_uw._){var _ux=E(_uw.a);return (_ux==(-2147483648))?E(_ut):new T1(0, -_ux);}else{return new T1(1,I_negate(_uw.a));}},_uy=new T1(0,10),_uz=function(_uA){return new F(function(){return _8h(E(_uA));});},_uB=new T(function(){return B(unCStr("this should not happen"));}),_uC=new T(function(){return B(err(_uB));}),_uD=function(_uE,_uF){var _uG=E(_uF);if(!_uG._){return __Z;}else{var _uH=E(_uG.b);return (_uH._==0)?E(_uC):new T2(1,B(_uk(B(_o3(_uG.a,_uE)),_uH.a)),new T(function(){return B(_uD(_uE,_uH.b));}));}},_uI=new T1(0,0),_uJ=function(_uK,_uL,_uM){while(1){var _uN=B((function(_uO,_uP,_uQ){var _uR=E(_uQ);if(!_uR._){return E(_uI);}else{if(!E(_uR.b)._){return E(_uR.a);}else{var _uS=E(_uP);if(_uS<=40){var _uT=function(_uU,_uV){while(1){var _uW=E(_uV);if(!_uW._){return E(_uU);}else{var _uX=B(_uk(B(_o3(_uU,_uO)),_uW.a));_uU=_uX;_uV=_uW.b;continue;}}};return new F(function(){return _uT(_uI,_uR);});}else{var _uY=B(_o3(_uO,_uO));if(!(_uS%2)){var _uZ=B(_uD(_uO,_uR));_uK=_uY;_uL=quot(_uS+1|0,2);_uM=_uZ;return __continue;}else{var _uZ=B(_uD(_uO,new T2(1,_uI,_uR)));_uK=_uY;_uL=quot(_uS+1|0,2);_uM=_uZ;return __continue;}}}}})(_uK,_uL,_uM));if(_uN!=__continue){return _uN;}}},_v0=function(_v1,_v2){return new F(function(){return _uJ(_v1,new T(function(){return B(_cL(_v2,0));},1),B(_2Q(_uz,_v2)));});},_v3=function(_v4){var _v5=new T(function(){var _v6=new T(function(){var _v7=function(_v8){return new F(function(){return A1(_v4,new T1(1,new T(function(){return B(_v0(_uy,_v8));})));});};return new T1(1,B(_tg(_uh,_v7)));}),_v9=function(_va){if(E(_va)==43){var _vb=function(_vc){return new F(function(){return A1(_v4,new T1(1,new T(function(){return B(_v0(_uy,_vc));})));});};return new T1(1,B(_tg(_uh,_vb)));}else{return new T0(2);}},_vd=function(_ve){if(E(_ve)==45){var _vf=function(_vg){return new F(function(){return A1(_v4,new T1(1,new T(function(){return B(_uu(B(_v0(_uy,_vg))));})));});};return new T1(1,B(_tg(_uh,_vf)));}else{return new T0(2);}};return B(_rg(B(_rg(new T1(0,_vd),new T1(0,_v9))),_v6));});return new F(function(){return _rg(new T1(0,function(_vh){return (E(_vh)==101)?E(_v5):new T0(2);}),new T1(0,function(_vi){return (E(_vi)==69)?E(_v5):new T0(2);}));});},_vj=function(_vk){var _vl=function(_vm){return new F(function(){return A1(_vk,new T1(1,_vm));});};return function(_vn){return (E(_vn)==46)?new T1(1,B(_tg(_uh,_vl))):new T0(2);};},_vo=function(_vp){return new T1(0,B(_vj(_vp)));},_vq=function(_vr){var _vs=function(_vt){var _vu=function(_vv){return new T1(1,B(_sz(_v3,_ud,function(_vw){return new F(function(){return A1(_vr,new T1(5,new T3(1,_vt,_vv,_vw)));});})));};return new T1(1,B(_sz(_vo,_uf,_vu)));};return new F(function(){return _tg(_uh,_vs);});},_vx=function(_vy){return new T1(1,B(_vq(_vy)));},_vz=function(_vA,_vB,_vC){while(1){var _vD=E(_vC);if(!_vD._){return false;}else{if(!B(A3(_oz,_vA,_vB,_vD.a))){_vC=_vD.b;continue;}else{return true;}}}},_vE=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_vF=function(_vG){return new F(function(){return _vz(_s5,_vG,_vE);});},_vH=false,_vI=true,_vJ=function(_vK){var _vL=new T(function(){return B(A1(_vK,_u1));}),_vM=new T(function(){return B(A1(_vK,_u0));});return function(_vN){switch(E(_vN)){case 79:return E(_vL);case 88:return E(_vM);case 111:return E(_vL);case 120:return E(_vM);default:return new T0(2);}};},_vO=function(_vP){return new T1(0,B(_vJ(_vP)));},_vQ=function(_vR){return new F(function(){return A1(_vR,_uh);});},_vS=function(_vT,_vU){var _vV=E(_vT);if(!_vV._){var _vW=_vV.a,_vX=E(_vU);return (_vX._==0)?_vW<=_vX.a:I_compareInt(_vX.a,_vW)>=0;}else{var _vY=_vV.a,_vZ=E(_vU);return (_vZ._==0)?I_compareInt(_vY,_vZ.a)<=0:I_compare(_vY,_vZ.a)<=0;}},_w0=function(_w1){return new T0(2);},_w2=function(_w3){var _w4=E(_w3);if(!_w4._){return E(_w0);}else{var _w5=_w4.a,_w6=E(_w4.b);if(!_w6._){return E(_w5);}else{var _w7=new T(function(){return B(_w2(_w6));}),_w8=function(_w9){return new F(function(){return _rg(B(A1(_w5,_w9)),new T(function(){return B(A1(_w7,_w9));}));});};return E(_w8);}}},_wa=function(_wb,_wc){var _wd=function(_we,_wf,_wg){var _wh=E(_we);if(!_wh._){return new F(function(){return A1(_wg,_wb);});}else{var _wi=E(_wf);if(!_wi._){return new T0(2);}else{if(E(_wh.a)!=E(_wi.a)){return new T0(2);}else{var _wj=new T(function(){return B(_wd(_wh.b,_wi.b,_wg));});return new T1(0,function(_wk){return E(_wj);});}}}};return function(_wl){return new F(function(){return _wd(_wb,_wl,_wc);});};},_wm=new T(function(){return B(unCStr("SO"));}),_wn=14,_wo=function(_wp){var _wq=new T(function(){return B(A1(_wp,_wn));});return new T1(1,B(_wa(_wm,function(_wr){return E(_wq);})));},_ws=new T(function(){return B(unCStr("SOH"));}),_wt=1,_wu=function(_wv){var _ww=new T(function(){return B(A1(_wv,_wt));});return new T1(1,B(_wa(_ws,function(_wx){return E(_ww);})));},_wy=function(_wz){return new T1(1,B(_sz(_wu,_wo,_wz)));},_wA=new T(function(){return B(unCStr("NUL"));}),_wB=0,_wC=function(_wD){var _wE=new T(function(){return B(A1(_wD,_wB));});return new T1(1,B(_wa(_wA,function(_wF){return E(_wE);})));},_wG=new T(function(){return B(unCStr("STX"));}),_wH=2,_wI=function(_wJ){var _wK=new T(function(){return B(A1(_wJ,_wH));});return new T1(1,B(_wa(_wG,function(_wL){return E(_wK);})));},_wM=new T(function(){return B(unCStr("ETX"));}),_wN=3,_wO=function(_wP){var _wQ=new T(function(){return B(A1(_wP,_wN));});return new T1(1,B(_wa(_wM,function(_wR){return E(_wQ);})));},_wS=new T(function(){return B(unCStr("EOT"));}),_wT=4,_wU=function(_wV){var _wW=new T(function(){return B(A1(_wV,_wT));});return new T1(1,B(_wa(_wS,function(_wX){return E(_wW);})));},_wY=new T(function(){return B(unCStr("ENQ"));}),_wZ=5,_x0=function(_x1){var _x2=new T(function(){return B(A1(_x1,_wZ));});return new T1(1,B(_wa(_wY,function(_x3){return E(_x2);})));},_x4=new T(function(){return B(unCStr("ACK"));}),_x5=6,_x6=function(_x7){var _x8=new T(function(){return B(A1(_x7,_x5));});return new T1(1,B(_wa(_x4,function(_x9){return E(_x8);})));},_xa=new T(function(){return B(unCStr("BEL"));}),_xb=7,_xc=function(_xd){var _xe=new T(function(){return B(A1(_xd,_xb));});return new T1(1,B(_wa(_xa,function(_xf){return E(_xe);})));},_xg=new T(function(){return B(unCStr("BS"));}),_xh=8,_xi=function(_xj){var _xk=new T(function(){return B(A1(_xj,_xh));});return new T1(1,B(_wa(_xg,function(_xl){return E(_xk);})));},_xm=new T(function(){return B(unCStr("HT"));}),_xn=9,_xo=function(_xp){var _xq=new T(function(){return B(A1(_xp,_xn));});return new T1(1,B(_wa(_xm,function(_xr){return E(_xq);})));},_xs=new T(function(){return B(unCStr("LF"));}),_xt=10,_xu=function(_xv){var _xw=new T(function(){return B(A1(_xv,_xt));});return new T1(1,B(_wa(_xs,function(_xx){return E(_xw);})));},_xy=new T(function(){return B(unCStr("VT"));}),_xz=11,_xA=function(_xB){var _xC=new T(function(){return B(A1(_xB,_xz));});return new T1(1,B(_wa(_xy,function(_xD){return E(_xC);})));},_xE=new T(function(){return B(unCStr("FF"));}),_xF=12,_xG=function(_xH){var _xI=new T(function(){return B(A1(_xH,_xF));});return new T1(1,B(_wa(_xE,function(_xJ){return E(_xI);})));},_xK=new T(function(){return B(unCStr("CR"));}),_xL=13,_xM=function(_xN){var _xO=new T(function(){return B(A1(_xN,_xL));});return new T1(1,B(_wa(_xK,function(_xP){return E(_xO);})));},_xQ=new T(function(){return B(unCStr("SI"));}),_xR=15,_xS=function(_xT){var _xU=new T(function(){return B(A1(_xT,_xR));});return new T1(1,B(_wa(_xQ,function(_xV){return E(_xU);})));},_xW=new T(function(){return B(unCStr("DLE"));}),_xX=16,_xY=function(_xZ){var _y0=new T(function(){return B(A1(_xZ,_xX));});return new T1(1,B(_wa(_xW,function(_y1){return E(_y0);})));},_y2=new T(function(){return B(unCStr("DC1"));}),_y3=17,_y4=function(_y5){var _y6=new T(function(){return B(A1(_y5,_y3));});return new T1(1,B(_wa(_y2,function(_y7){return E(_y6);})));},_y8=new T(function(){return B(unCStr("DC2"));}),_y9=18,_ya=function(_yb){var _yc=new T(function(){return B(A1(_yb,_y9));});return new T1(1,B(_wa(_y8,function(_yd){return E(_yc);})));},_ye=new T(function(){return B(unCStr("DC3"));}),_yf=19,_yg=function(_yh){var _yi=new T(function(){return B(A1(_yh,_yf));});return new T1(1,B(_wa(_ye,function(_yj){return E(_yi);})));},_yk=new T(function(){return B(unCStr("DC4"));}),_yl=20,_ym=function(_yn){var _yo=new T(function(){return B(A1(_yn,_yl));});return new T1(1,B(_wa(_yk,function(_yp){return E(_yo);})));},_yq=new T(function(){return B(unCStr("NAK"));}),_yr=21,_ys=function(_yt){var _yu=new T(function(){return B(A1(_yt,_yr));});return new T1(1,B(_wa(_yq,function(_yv){return E(_yu);})));},_yw=new T(function(){return B(unCStr("SYN"));}),_yx=22,_yy=function(_yz){var _yA=new T(function(){return B(A1(_yz,_yx));});return new T1(1,B(_wa(_yw,function(_yB){return E(_yA);})));},_yC=new T(function(){return B(unCStr("ETB"));}),_yD=23,_yE=function(_yF){var _yG=new T(function(){return B(A1(_yF,_yD));});return new T1(1,B(_wa(_yC,function(_yH){return E(_yG);})));},_yI=new T(function(){return B(unCStr("CAN"));}),_yJ=24,_yK=function(_yL){var _yM=new T(function(){return B(A1(_yL,_yJ));});return new T1(1,B(_wa(_yI,function(_yN){return E(_yM);})));},_yO=new T(function(){return B(unCStr("EM"));}),_yP=25,_yQ=function(_yR){var _yS=new T(function(){return B(A1(_yR,_yP));});return new T1(1,B(_wa(_yO,function(_yT){return E(_yS);})));},_yU=new T(function(){return B(unCStr("SUB"));}),_yV=26,_yW=function(_yX){var _yY=new T(function(){return B(A1(_yX,_yV));});return new T1(1,B(_wa(_yU,function(_yZ){return E(_yY);})));},_z0=new T(function(){return B(unCStr("ESC"));}),_z1=27,_z2=function(_z3){var _z4=new T(function(){return B(A1(_z3,_z1));});return new T1(1,B(_wa(_z0,function(_z5){return E(_z4);})));},_z6=new T(function(){return B(unCStr("FS"));}),_z7=28,_z8=function(_z9){var _za=new T(function(){return B(A1(_z9,_z7));});return new T1(1,B(_wa(_z6,function(_zb){return E(_za);})));},_zc=new T(function(){return B(unCStr("GS"));}),_zd=29,_ze=function(_zf){var _zg=new T(function(){return B(A1(_zf,_zd));});return new T1(1,B(_wa(_zc,function(_zh){return E(_zg);})));},_zi=new T(function(){return B(unCStr("RS"));}),_zj=30,_zk=function(_zl){var _zm=new T(function(){return B(A1(_zl,_zj));});return new T1(1,B(_wa(_zi,function(_zn){return E(_zm);})));},_zo=new T(function(){return B(unCStr("US"));}),_zp=31,_zq=function(_zr){var _zs=new T(function(){return B(A1(_zr,_zp));});return new T1(1,B(_wa(_zo,function(_zt){return E(_zs);})));},_zu=new T(function(){return B(unCStr("SP"));}),_zv=32,_zw=function(_zx){var _zy=new T(function(){return B(A1(_zx,_zv));});return new T1(1,B(_wa(_zu,function(_zz){return E(_zy);})));},_zA=new T(function(){return B(unCStr("DEL"));}),_zB=127,_zC=function(_zD){var _zE=new T(function(){return B(A1(_zD,_zB));});return new T1(1,B(_wa(_zA,function(_zF){return E(_zE);})));},_zG=new T2(1,_zC,_M),_zH=new T2(1,_zw,_zG),_zI=new T2(1,_zq,_zH),_zJ=new T2(1,_zk,_zI),_zK=new T2(1,_ze,_zJ),_zL=new T2(1,_z8,_zK),_zM=new T2(1,_z2,_zL),_zN=new T2(1,_yW,_zM),_zO=new T2(1,_yQ,_zN),_zP=new T2(1,_yK,_zO),_zQ=new T2(1,_yE,_zP),_zR=new T2(1,_yy,_zQ),_zS=new T2(1,_ys,_zR),_zT=new T2(1,_ym,_zS),_zU=new T2(1,_yg,_zT),_zV=new T2(1,_ya,_zU),_zW=new T2(1,_y4,_zV),_zX=new T2(1,_xY,_zW),_zY=new T2(1,_xS,_zX),_zZ=new T2(1,_xM,_zY),_A0=new T2(1,_xG,_zZ),_A1=new T2(1,_xA,_A0),_A2=new T2(1,_xu,_A1),_A3=new T2(1,_xo,_A2),_A4=new T2(1,_xi,_A3),_A5=new T2(1,_xc,_A4),_A6=new T2(1,_x6,_A5),_A7=new T2(1,_x0,_A6),_A8=new T2(1,_wU,_A7),_A9=new T2(1,_wO,_A8),_Aa=new T2(1,_wI,_A9),_Ab=new T2(1,_wC,_Aa),_Ac=new T2(1,_wy,_Ab),_Ad=new T(function(){return B(_w2(_Ac));}),_Ae=34,_Af=new T1(0,1114111),_Ag=92,_Ah=39,_Ai=function(_Aj){var _Ak=new T(function(){return B(A1(_Aj,_xb));}),_Al=new T(function(){return B(A1(_Aj,_xh));}),_Am=new T(function(){return B(A1(_Aj,_xn));}),_An=new T(function(){return B(A1(_Aj,_xt));}),_Ao=new T(function(){return B(A1(_Aj,_xz));}),_Ap=new T(function(){return B(A1(_Aj,_xF));}),_Aq=new T(function(){return B(A1(_Aj,_xL));}),_Ar=new T(function(){return B(A1(_Aj,_Ag));}),_As=new T(function(){return B(A1(_Aj,_Ah));}),_At=new T(function(){return B(A1(_Aj,_Ae));}),_Au=new T(function(){var _Av=function(_Aw){var _Ax=new T(function(){return B(_8h(E(_Aw)));}),_Ay=function(_Az){var _AA=B(_v0(_Ax,_Az));if(!B(_vS(_AA,_Af))){return new T0(2);}else{return new F(function(){return A1(_Aj,new T(function(){var _AB=B(_nC(_AA));if(_AB>>>0>1114111){return B(_9E(_AB));}else{return _AB;}}));});}};return new T1(1,B(_tg(_Aw,_Ay)));},_AC=new T(function(){var _AD=new T(function(){return B(A1(_Aj,_zp));}),_AE=new T(function(){return B(A1(_Aj,_zj));}),_AF=new T(function(){return B(A1(_Aj,_zd));}),_AG=new T(function(){return B(A1(_Aj,_z7));}),_AH=new T(function(){return B(A1(_Aj,_z1));}),_AI=new T(function(){return B(A1(_Aj,_yV));}),_AJ=new T(function(){return B(A1(_Aj,_yP));}),_AK=new T(function(){return B(A1(_Aj,_yJ));}),_AL=new T(function(){return B(A1(_Aj,_yD));}),_AM=new T(function(){return B(A1(_Aj,_yx));}),_AN=new T(function(){return B(A1(_Aj,_yr));}),_AO=new T(function(){return B(A1(_Aj,_yl));}),_AP=new T(function(){return B(A1(_Aj,_yf));}),_AQ=new T(function(){return B(A1(_Aj,_y9));}),_AR=new T(function(){return B(A1(_Aj,_y3));}),_AS=new T(function(){return B(A1(_Aj,_xX));}),_AT=new T(function(){return B(A1(_Aj,_xR));}),_AU=new T(function(){return B(A1(_Aj,_wn));}),_AV=new T(function(){return B(A1(_Aj,_x5));}),_AW=new T(function(){return B(A1(_Aj,_wZ));}),_AX=new T(function(){return B(A1(_Aj,_wT));}),_AY=new T(function(){return B(A1(_Aj,_wN));}),_AZ=new T(function(){return B(A1(_Aj,_wH));}),_B0=new T(function(){return B(A1(_Aj,_wt));}),_B1=new T(function(){return B(A1(_Aj,_wB));}),_B2=function(_B3){switch(E(_B3)){case 64:return E(_B1);case 65:return E(_B0);case 66:return E(_AZ);case 67:return E(_AY);case 68:return E(_AX);case 69:return E(_AW);case 70:return E(_AV);case 71:return E(_Ak);case 72:return E(_Al);case 73:return E(_Am);case 74:return E(_An);case 75:return E(_Ao);case 76:return E(_Ap);case 77:return E(_Aq);case 78:return E(_AU);case 79:return E(_AT);case 80:return E(_AS);case 81:return E(_AR);case 82:return E(_AQ);case 83:return E(_AP);case 84:return E(_AO);case 85:return E(_AN);case 86:return E(_AM);case 87:return E(_AL);case 88:return E(_AK);case 89:return E(_AJ);case 90:return E(_AI);case 91:return E(_AH);case 92:return E(_AG);case 93:return E(_AF);case 94:return E(_AE);case 95:return E(_AD);default:return new T0(2);}};return B(_rg(new T1(0,function(_B4){return (E(_B4)==94)?E(new T1(0,_B2)):new T0(2);}),new T(function(){return B(A1(_Ad,_Aj));})));});return B(_rg(new T1(1,B(_sz(_vO,_vQ,_Av))),_AC));});return new F(function(){return _rg(new T1(0,function(_B5){switch(E(_B5)){case 34:return E(_At);case 39:return E(_As);case 92:return E(_Ar);case 97:return E(_Ak);case 98:return E(_Al);case 102:return E(_Ap);case 110:return E(_An);case 114:return E(_Aq);case 116:return E(_Am);case 118:return E(_Ao);default:return new T0(2);}}),_Au);});},_B6=function(_B7){return new F(function(){return A1(_B7,_0);});},_B8=function(_B9){var _Ba=E(_B9);if(!_Ba._){return E(_B6);}else{var _Bb=E(_Ba.a),_Bc=_Bb>>>0,_Bd=new T(function(){return B(_B8(_Ba.b));});if(_Bc>887){var _Be=u_iswspace(_Bb);if(!E(_Be)){return E(_B6);}else{var _Bf=function(_Bg){var _Bh=new T(function(){return B(A1(_Bd,_Bg));});return new T1(0,function(_Bi){return E(_Bh);});};return E(_Bf);}}else{var _Bj=E(_Bc);if(_Bj==32){var _Bk=function(_Bl){var _Bm=new T(function(){return B(A1(_Bd,_Bl));});return new T1(0,function(_Bn){return E(_Bm);});};return E(_Bk);}else{if(_Bj-9>>>0>4){if(E(_Bj)==160){var _Bo=function(_Bp){var _Bq=new T(function(){return B(A1(_Bd,_Bp));});return new T1(0,function(_Br){return E(_Bq);});};return E(_Bo);}else{return E(_B6);}}else{var _Bs=function(_Bt){var _Bu=new T(function(){return B(A1(_Bd,_Bt));});return new T1(0,function(_Bv){return E(_Bu);});};return E(_Bs);}}}}},_Bw=function(_Bx){var _By=new T(function(){return B(_Bw(_Bx));}),_Bz=function(_BA){return (E(_BA)==92)?E(_By):new T0(2);},_BB=function(_BC){return E(new T1(0,_Bz));},_BD=new T1(1,function(_BE){return new F(function(){return A2(_B8,_BE,_BB);});}),_BF=new T(function(){return B(_Ai(function(_BG){return new F(function(){return A1(_Bx,new T2(0,_BG,_vI));});}));}),_BH=function(_BI){var _BJ=E(_BI);if(_BJ==38){return E(_By);}else{var _BK=_BJ>>>0;if(_BK>887){var _BL=u_iswspace(_BJ);return (E(_BL)==0)?new T0(2):E(_BD);}else{var _BM=E(_BK);return (_BM==32)?E(_BD):(_BM-9>>>0>4)?(E(_BM)==160)?E(_BD):new T0(2):E(_BD);}}};return new F(function(){return _rg(new T1(0,function(_BN){return (E(_BN)==92)?E(new T1(0,_BH)):new T0(2);}),new T1(0,function(_BO){var _BP=E(_BO);if(E(_BP)==92){return E(_BF);}else{return new F(function(){return A1(_Bx,new T2(0,_BP,_vH));});}}));});},_BQ=function(_BR,_BS){var _BT=new T(function(){return B(A1(_BS,new T1(1,new T(function(){return B(A1(_BR,_M));}))));}),_BU=function(_BV){var _BW=E(_BV),_BX=E(_BW.a);if(E(_BX)==34){if(!E(_BW.b)){return E(_BT);}else{return new F(function(){return _BQ(function(_BY){return new F(function(){return A1(_BR,new T2(1,_BX,_BY));});},_BS);});}}else{return new F(function(){return _BQ(function(_BZ){return new F(function(){return A1(_BR,new T2(1,_BX,_BZ));});},_BS);});}};return new F(function(){return _Bw(_BU);});},_C0=new T(function(){return B(unCStr("_\'"));}),_C1=function(_C2){var _C3=u_iswalnum(_C2);if(!E(_C3)){return new F(function(){return _vz(_s5,_C2,_C0);});}else{return true;}},_C4=function(_C5){return new F(function(){return _C1(E(_C5));});},_C6=new T(function(){return B(unCStr(",;()[]{}`"));}),_C7=new T(function(){return B(unCStr("=>"));}),_C8=new T2(1,_C7,_M),_C9=new T(function(){return B(unCStr("~"));}),_Ca=new T2(1,_C9,_C8),_Cb=new T(function(){return B(unCStr("@"));}),_Cc=new T2(1,_Cb,_Ca),_Cd=new T(function(){return B(unCStr("->"));}),_Ce=new T2(1,_Cd,_Cc),_Cf=new T(function(){return B(unCStr("<-"));}),_Cg=new T2(1,_Cf,_Ce),_Ch=new T(function(){return B(unCStr("|"));}),_Ci=new T2(1,_Ch,_Cg),_Cj=new T(function(){return B(unCStr("\\"));}),_Ck=new T2(1,_Cj,_Ci),_Cl=new T(function(){return B(unCStr("="));}),_Cm=new T2(1,_Cl,_Ck),_Cn=new T(function(){return B(unCStr("::"));}),_Co=new T2(1,_Cn,_Cm),_Cp=new T(function(){return B(unCStr(".."));}),_Cq=new T2(1,_Cp,_Co),_Cr=function(_Cs){var _Ct=new T(function(){return B(A1(_Cs,_td));}),_Cu=new T(function(){var _Cv=new T(function(){var _Cw=function(_Cx){var _Cy=new T(function(){return B(A1(_Cs,new T1(0,_Cx)));});return new T1(0,function(_Cz){return (E(_Cz)==39)?E(_Cy):new T0(2);});};return B(_Ai(_Cw));}),_CA=function(_CB){var _CC=E(_CB);switch(E(_CC)){case 39:return new T0(2);case 92:return E(_Cv);default:var _CD=new T(function(){return B(A1(_Cs,new T1(0,_CC)));});return new T1(0,function(_CE){return (E(_CE)==39)?E(_CD):new T0(2);});}},_CF=new T(function(){var _CG=new T(function(){return B(_BQ(_2I,_Cs));}),_CH=new T(function(){var _CI=new T(function(){var _CJ=new T(function(){var _CK=function(_CL){var _CM=E(_CL),_CN=u_iswalpha(_CM);return (E(_CN)==0)?(E(_CM)==95)?new T1(1,B(_sZ(_C4,function(_CO){return new F(function(){return A1(_Cs,new T1(3,new T2(1,_CM,_CO)));});}))):new T0(2):new T1(1,B(_sZ(_C4,function(_CP){return new F(function(){return A1(_Cs,new T1(3,new T2(1,_CM,_CP)));});})));};return B(_rg(new T1(0,_CK),new T(function(){return new T1(1,B(_sz(_ub,_vx,_Cs)));})));}),_CQ=function(_CR){return (!B(_vz(_s5,_CR,_vE)))?new T0(2):new T1(1,B(_sZ(_vF,function(_CS){var _CT=new T2(1,_CR,_CS);if(!B(_vz(_se,_CT,_Cq))){return new F(function(){return A1(_Cs,new T1(4,_CT));});}else{return new F(function(){return A1(_Cs,new T1(2,_CT));});}})));};return B(_rg(new T1(0,_CQ),_CJ));});return B(_rg(new T1(0,function(_CU){if(!B(_vz(_s5,_CU,_C6))){return new T0(2);}else{return new F(function(){return A1(_Cs,new T1(2,new T2(1,_CU,_M)));});}}),_CI));});return B(_rg(new T1(0,function(_CV){return (E(_CV)==34)?E(_CG):new T0(2);}),_CH));});return B(_rg(new T1(0,function(_CW){return (E(_CW)==39)?E(new T1(0,_CA)):new T0(2);}),_CF));});return new F(function(){return _rg(new T1(1,function(_CX){return (E(_CX)._==0)?E(_Ct):new T0(2);}),_Cu);});},_CY=0,_CZ=function(_D0,_D1){var _D2=new T(function(){var _D3=new T(function(){var _D4=function(_D5){var _D6=new T(function(){var _D7=new T(function(){return B(A1(_D1,_D5));});return B(_Cr(function(_D8){var _D9=E(_D8);return (_D9._==2)?(!B(_rU(_D9.a,_rT)))?new T0(2):E(_D7):new T0(2);}));}),_Da=function(_Db){return E(_D6);};return new T1(1,function(_Dc){return new F(function(){return A2(_B8,_Dc,_Da);});});};return B(A2(_D0,_CY,_D4));});return B(_Cr(function(_Dd){var _De=E(_Dd);return (_De._==2)?(!B(_rU(_De.a,_rS)))?new T0(2):E(_D3):new T0(2);}));}),_Df=function(_Dg){return E(_D2);};return function(_Dh){return new F(function(){return A2(_B8,_Dh,_Df);});};},_Di=function(_Dj,_Dk){var _Dl=function(_Dm){var _Dn=new T(function(){return B(A1(_Dj,_Dm));}),_Do=function(_Dp){return new F(function(){return _rg(B(A1(_Dn,_Dp)),new T(function(){return new T1(1,B(_CZ(_Dl,_Dp)));}));});};return E(_Do);},_Dq=new T(function(){return B(A1(_Dj,_Dk));}),_Dr=function(_Ds){return new F(function(){return _rg(B(A1(_Dq,_Ds)),new T(function(){return new T1(1,B(_CZ(_Dl,_Ds)));}));});};return E(_Dr);},_Dt=function(_Du,_Dv){var _Dw=function(_Dx,_Dy){var _Dz=function(_DA){return new F(function(){return A1(_Dy,new T(function(){return  -E(_DA);}));});},_DB=new T(function(){return B(_Cr(function(_DC){return new F(function(){return A3(_Du,_DC,_Dx,_Dz);});}));}),_DD=function(_DE){return E(_DB);},_DF=function(_DG){return new F(function(){return A2(_B8,_DG,_DD);});},_DH=new T(function(){return B(_Cr(function(_DI){var _DJ=E(_DI);if(_DJ._==4){var _DK=E(_DJ.a);if(!_DK._){return new F(function(){return A3(_Du,_DJ,_Dx,_Dy);});}else{if(E(_DK.a)==45){if(!E(_DK.b)._){return E(new T1(1,_DF));}else{return new F(function(){return A3(_Du,_DJ,_Dx,_Dy);});}}else{return new F(function(){return A3(_Du,_DJ,_Dx,_Dy);});}}}else{return new F(function(){return A3(_Du,_DJ,_Dx,_Dy);});}}));}),_DL=function(_DM){return E(_DH);};return new T1(1,function(_DN){return new F(function(){return A2(_B8,_DN,_DL);});});};return new F(function(){return _Di(_Dw,_Dv);});},_DO=new T(function(){return 1/0;}),_DP=function(_DQ,_DR){return new F(function(){return A1(_DR,_DO);});},_DS=new T(function(){return 0/0;}),_DT=function(_DU,_DV){return new F(function(){return A1(_DV,_DS);});},_DW=new T(function(){return B(unCStr("NaN"));}),_DX=new T(function(){return B(unCStr("Infinity"));}),_DY=1024,_DZ=-1021,_E0=function(_E1,_E2){while(1){var _E3=E(_E1);if(!_E3._){var _E4=E(_E3.a);if(_E4==(-2147483648)){_E1=new T1(1,I_fromInt(-2147483648));continue;}else{var _E5=E(_E2);if(!_E5._){return new T1(0,_E4%_E5.a);}else{_E1=new T1(1,I_fromInt(_E4));_E2=_E5;continue;}}}else{var _E6=_E3.a,_E7=E(_E2);return (_E7._==0)?new T1(1,I_rem(_E6,I_fromInt(_E7.a))):new T1(1,I_rem(_E6,_E7.a));}}},_E8=function(_E9,_Ea){if(!B(_pr(_Ea,_oB))){return new F(function(){return _E0(_E9,_Ea);});}else{return E(_mr);}},_Eb=function(_Ec,_Ed){while(1){if(!B(_pr(_Ed,_oB))){var _Ee=_Ed,_Ef=B(_E8(_Ec,_Ed));_Ec=_Ee;_Ed=_Ef;continue;}else{return E(_Ec);}}},_Eg=function(_Eh){var _Ei=E(_Eh);if(!_Ei._){var _Ej=E(_Ei.a);return (_Ej==(-2147483648))?E(_ut):(_Ej<0)?new T1(0, -_Ej):E(_Ei);}else{var _Ek=_Ei.a;return (I_compareInt(_Ek,0)>=0)?E(_Ei):new T1(1,I_negate(_Ek));}},_El=function(_Em,_En){while(1){var _Eo=E(_Em);if(!_Eo._){var _Ep=E(_Eo.a);if(_Ep==(-2147483648)){_Em=new T1(1,I_fromInt(-2147483648));continue;}else{var _Eq=E(_En);if(!_Eq._){return new T1(0,quot(_Ep,_Eq.a));}else{_Em=new T1(1,I_fromInt(_Ep));_En=_Eq;continue;}}}else{var _Er=_Eo.a,_Es=E(_En);return (_Es._==0)?new T1(0,I_toInt(I_quot(_Er,I_fromInt(_Es.a)))):new T1(1,I_quot(_Er,_Es.a));}}},_Et=5,_Eu=new T(function(){return B(_mn(_Et));}),_Ev=new T(function(){return die(_Eu);}),_Ew=function(_Ex,_Ey){if(!B(_pr(_Ey,_oB))){var _Ez=B(_Eb(B(_Eg(_Ex)),B(_Eg(_Ey))));return (!B(_pr(_Ez,_oB)))?new T2(0,B(_El(_Ex,_Ez)),B(_El(_Ey,_Ez))):E(_mr);}else{return E(_Ev);}},_EA=new T(function(){return B(_pr(_oC,_oB));}),_EB=function(_EC,_ED){while(1){var _EE=E(_EC);if(!_EE._){var _EF=_EE.a,_EG=E(_ED);if(!_EG._){var _EH=_EG.a,_EI=subC(_EF,_EH);if(!E(_EI.b)){return new T1(0,_EI.a);}else{_EC=new T1(1,I_fromInt(_EF));_ED=new T1(1,I_fromInt(_EH));continue;}}else{_EC=new T1(1,I_fromInt(_EF));_ED=_EG;continue;}}else{var _EJ=E(_ED);if(!_EJ._){_EC=_EE;_ED=new T1(1,I_fromInt(_EJ.a));continue;}else{return new T1(1,I_sub(_EE.a,_EJ.a));}}}},_EK=function(_EL,_EM,_EN){while(1){if(!E(_EA)){if(!B(_pr(B(_E0(_EM,_oC)),_oB))){if(!B(_pr(_EM,_nq))){var _EO=B(_o3(_EL,_EL)),_EP=B(_El(B(_EB(_EM,_nq)),_oC)),_EQ=B(_o3(_EL,_EN));_EL=_EO;_EM=_EP;_EN=_EQ;continue;}else{return new F(function(){return _o3(_EL,_EN);});}}else{var _EO=B(_o3(_EL,_EL)),_EP=B(_El(_EM,_oC));_EL=_EO;_EM=_EP;continue;}}else{return E(_mr);}}},_ER=function(_ES,_ET){while(1){if(!E(_EA)){if(!B(_pr(B(_E0(_ET,_oC)),_oB))){if(!B(_pr(_ET,_nq))){return new F(function(){return _EK(B(_o3(_ES,_ES)),B(_El(B(_EB(_ET,_nq)),_oC)),_ES);});}else{return E(_ES);}}else{var _EU=B(_o3(_ES,_ES)),_EV=B(_El(_ET,_oC));_ES=_EU;_ET=_EV;continue;}}else{return E(_mr);}}},_EW=function(_EX,_EY){if(!B(_82(_EY,_oB))){if(!B(_pr(_EY,_oB))){return new F(function(){return _ER(_EX,_EY);});}else{return E(_nq);}}else{return E(_pj);}},_EZ=new T1(0,1),_F0=new T1(0,0),_F1=new T1(0,-1),_F2=function(_F3){var _F4=E(_F3);if(!_F4._){var _F5=_F4.a;return (_F5>=0)?(E(_F5)==0)?E(_F0):E(_ui):E(_F1);}else{var _F6=I_compareInt(_F4.a,0);return (_F6<=0)?(E(_F6)==0)?E(_F0):E(_F1):E(_ui);}},_F7=function(_F8,_F9,_Fa){while(1){var _Fb=E(_Fa);if(!_Fb._){if(!B(_82(_F8,_uI))){return new T2(0,B(_o3(_F9,B(_EW(_uy,_F8)))),_nq);}else{var _Fc=B(_EW(_uy,B(_uu(_F8))));return new F(function(){return _Ew(B(_o3(_F9,B(_F2(_Fc)))),B(_Eg(_Fc)));});}}else{var _Fd=B(_EB(_F8,_EZ)),_Fe=B(_uk(B(_o3(_F9,_uy)),B(_8h(E(_Fb.a)))));_F8=_Fd;_F9=_Fe;_Fa=_Fb.b;continue;}}},_Ff=function(_Fg,_Fh){var _Fi=E(_Fg);if(!_Fi._){var _Fj=_Fi.a,_Fk=E(_Fh);return (_Fk._==0)?_Fj>=_Fk.a:I_compareInt(_Fk.a,_Fj)<=0;}else{var _Fl=_Fi.a,_Fm=E(_Fh);return (_Fm._==0)?I_compareInt(_Fl,_Fm.a)>=0:I_compare(_Fl,_Fm.a)>=0;}},_Fn=function(_Fo){var _Fp=E(_Fo);if(!_Fp._){var _Fq=_Fp.b;return new F(function(){return _Ew(B(_o3(B(_uJ(new T(function(){return B(_8h(E(_Fp.a)));}),new T(function(){return B(_cL(_Fq,0));},1),B(_2Q(_uz,_Fq)))),_EZ)),_EZ);});}else{var _Fr=_Fp.a,_Fs=_Fp.c,_Ft=E(_Fp.b);if(!_Ft._){var _Fu=E(_Fs);if(!_Fu._){return new F(function(){return _Ew(B(_o3(B(_v0(_uy,_Fr)),_EZ)),_EZ);});}else{var _Fv=_Fu.a;if(!B(_Ff(_Fv,_uI))){var _Fw=B(_EW(_uy,B(_uu(_Fv))));return new F(function(){return _Ew(B(_o3(B(_v0(_uy,_Fr)),B(_F2(_Fw)))),B(_Eg(_Fw)));});}else{return new F(function(){return _Ew(B(_o3(B(_o3(B(_v0(_uy,_Fr)),B(_EW(_uy,_Fv)))),_EZ)),_EZ);});}}}else{var _Fx=_Ft.a,_Fy=E(_Fs);if(!_Fy._){return new F(function(){return _F7(_uI,B(_v0(_uy,_Fr)),_Fx);});}else{return new F(function(){return _F7(_Fy.a,B(_v0(_uy,_Fr)),_Fx);});}}}},_Fz=function(_FA,_FB){while(1){var _FC=E(_FB);if(!_FC._){return __Z;}else{if(!B(A1(_FA,_FC.a))){return E(_FC);}else{_FB=_FC.b;continue;}}}},_FD=function(_FE,_FF){var _FG=E(_FE);if(!_FG._){var _FH=_FG.a,_FI=E(_FF);return (_FI._==0)?_FH>_FI.a:I_compareInt(_FI.a,_FH)<0;}else{var _FJ=_FG.a,_FK=E(_FF);return (_FK._==0)?I_compareInt(_FJ,_FK.a)>0:I_compare(_FJ,_FK.a)>0;}},_FL=0,_FM=function(_FN){return new F(function(){return _gI(_FL,_FN);});},_FO=new T2(0,E(_uI),E(_nq)),_FP=new T1(1,_FO),_FQ=new T1(0,-2147483648),_FR=new T1(0,2147483647),_FS=function(_FT,_FU,_FV){var _FW=E(_FV);if(!_FW._){return new T1(1,new T(function(){var _FX=B(_Fn(_FW));return new T2(0,E(_FX.a),E(_FX.b));}));}else{var _FY=E(_FW.c);if(!_FY._){return new T1(1,new T(function(){var _FZ=B(_Fn(_FW));return new T2(0,E(_FZ.a),E(_FZ.b));}));}else{var _G0=_FY.a;if(!B(_FD(_G0,_FR))){if(!B(_82(_G0,_FQ))){var _G1=function(_G2){var _G3=_G2+B(_nC(_G0))|0;return (_G3<=(E(_FU)+3|0))?(_G3>=(E(_FT)-3|0))?new T1(1,new T(function(){var _G4=B(_Fn(_FW));return new T2(0,E(_G4.a),E(_G4.b));})):E(_FP):__Z;},_G5=B(_Fz(_FM,_FW.a));if(!_G5._){var _G6=E(_FW.b);if(!_G6._){return E(_FP);}else{var _G7=B(_qH(_FM,_G6.a));if(!E(_G7.b)._){return E(_FP);}else{return new F(function(){return _G1( -B(_cL(_G7.a,0)));});}}}else{return new F(function(){return _G1(B(_cL(_G5,0)));});}}else{return __Z;}}else{return __Z;}}}},_G8=function(_G9,_Ga){return new T0(2);},_Gb=new T1(0,1),_Gc=function(_Gd,_Ge){var _Gf=E(_Gd);if(!_Gf._){var _Gg=_Gf.a,_Gh=E(_Ge);if(!_Gh._){var _Gi=_Gh.a;return (_Gg!=_Gi)?(_Gg>_Gi)?2:0:1;}else{var _Gj=I_compareInt(_Gh.a,_Gg);return (_Gj<=0)?(_Gj>=0)?1:2:0;}}else{var _Gk=_Gf.a,_Gl=E(_Ge);if(!_Gl._){var _Gm=I_compareInt(_Gk,_Gl.a);return (_Gm>=0)?(_Gm<=0)?1:2:0;}else{var _Gn=I_compare(_Gk,_Gl.a);return (_Gn>=0)?(_Gn<=0)?1:2:0;}}},_Go=function(_Gp,_Gq){while(1){var _Gr=E(_Gp);if(!_Gr._){_Gp=new T1(1,I_fromInt(_Gr.a));continue;}else{return new T1(1,I_shiftLeft(_Gr.a,_Gq));}}},_Gs=function(_Gt,_Gu,_Gv){if(!B(_pr(_Gv,_pJ))){var _Gw=B(_pz(_Gu,_Gv)),_Gx=_Gw.a;switch(B(_Gc(B(_Go(_Gw.b,1)),_Gv))){case 0:return new F(function(){return _pn(_Gx,_Gt);});break;case 1:if(!(B(_nC(_Gx))&1)){return new F(function(){return _pn(_Gx,_Gt);});}else{return new F(function(){return _pn(B(_uk(_Gx,_Gb)),_Gt);});}break;default:return new F(function(){return _pn(B(_uk(_Gx,_Gb)),_Gt);});}}else{return E(_mr);}},_Gy=function(_Gz){var _GA=function(_GB,_GC){while(1){if(!B(_82(_GB,_Gz))){if(!B(_FD(_GB,_Gz))){if(!B(_pr(_GB,_Gz))){return new F(function(){return _r3("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});}else{return E(_GC);}}else{return _GC-1|0;}}else{var _GD=B(_Go(_GB,1)),_GE=_GC+1|0;_GB=_GD;_GC=_GE;continue;}}};return new F(function(){return _GA(_ui,0);});},_GF=function(_GG){var _GH=E(_GG);if(!_GH._){var _GI=_GH.a>>>0;if(!_GI){return -1;}else{var _GJ=function(_GK,_GL){while(1){if(_GK>=_GI){if(_GK<=_GI){if(_GK!=_GI){return new F(function(){return _r3("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_GL);}}else{return _GL-1|0;}}else{var _GM=imul(_GK,2)>>>0,_GN=_GL+1|0;_GK=_GM;_GL=_GN;continue;}}};return new F(function(){return _GJ(1,0);});}}else{return new F(function(){return _Gy(_GH);});}},_GO=function(_GP){var _GQ=E(_GP);if(!_GQ._){var _GR=_GQ.a>>>0;if(!_GR){return new T2(0,-1,0);}else{var _GS=function(_GT,_GU){while(1){if(_GT>=_GR){if(_GT<=_GR){if(_GT!=_GR){return new F(function(){return _r3("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});}else{return E(_GU);}}else{return _GU-1|0;}}else{var _GV=imul(_GT,2)>>>0,_GW=_GU+1|0;_GT=_GV;_GU=_GW;continue;}}};return new T2(0,B(_GS(1,0)),(_GR&_GR-1>>>0)>>>0&4294967295);}}else{var _GX=_GQ.a;return new T2(0,B(_GF(_GQ)),I_compareInt(I_and(_GX,I_sub(_GX,I_fromInt(1))),0));}},_GY=function(_GZ,_H0){while(1){var _H1=E(_GZ);if(!_H1._){var _H2=_H1.a,_H3=E(_H0);if(!_H3._){return new T1(0,(_H2>>>0&_H3.a>>>0)>>>0&4294967295);}else{_GZ=new T1(1,I_fromInt(_H2));_H0=_H3;continue;}}else{var _H4=E(_H0);if(!_H4._){_GZ=_H1;_H0=new T1(1,I_fromInt(_H4.a));continue;}else{return new T1(1,I_and(_H1.a,_H4.a));}}}},_H5=new T1(0,2),_H6=function(_H7,_H8){var _H9=E(_H7);if(!_H9._){var _Ha=(_H9.a>>>0&(2<<_H8>>>0)-1>>>0)>>>0,_Hb=1<<_H8>>>0;return (_Hb<=_Ha)?(_Hb>=_Ha)?1:2:0;}else{var _Hc=B(_GY(_H9,B(_EB(B(_Go(_H5,_H8)),_ui)))),_Hd=B(_Go(_ui,_H8));return (!B(_FD(_Hd,_Hc)))?(!B(_82(_Hd,_Hc)))?1:2:0;}},_He=function(_Hf,_Hg){while(1){var _Hh=E(_Hf);if(!_Hh._){_Hf=new T1(1,I_fromInt(_Hh.a));continue;}else{return new T1(1,I_shiftRight(_Hh.a,_Hg));}}},_Hi=function(_Hj,_Hk,_Hl,_Hm){var _Hn=B(_GO(_Hm)),_Ho=_Hn.a;if(!E(_Hn.b)){var _Hp=B(_GF(_Hl));if(_Hp<((_Ho+_Hj|0)-1|0)){var _Hq=_Ho+(_Hj-_Hk|0)|0;if(_Hq>0){if(_Hq>_Hp){if(_Hq<=(_Hp+1|0)){if(!E(B(_GO(_Hl)).b)){return 0;}else{return new F(function(){return _pn(_Gb,_Hj-_Hk|0);});}}else{return 0;}}else{var _Hr=B(_He(_Hl,_Hq));switch(B(_H6(_Hl,_Hq-1|0))){case 0:return new F(function(){return _pn(_Hr,_Hj-_Hk|0);});break;case 1:if(!(B(_nC(_Hr))&1)){return new F(function(){return _pn(_Hr,_Hj-_Hk|0);});}else{return new F(function(){return _pn(B(_uk(_Hr,_Gb)),_Hj-_Hk|0);});}break;default:return new F(function(){return _pn(B(_uk(_Hr,_Gb)),_Hj-_Hk|0);});}}}else{return new F(function(){return _pn(_Hl,(_Hj-_Hk|0)-_Hq|0);});}}else{if(_Hp>=_Hk){var _Hs=B(_He(_Hl,(_Hp+1|0)-_Hk|0));switch(B(_H6(_Hl,_Hp-_Hk|0))){case 0:return new F(function(){return _pn(_Hs,((_Hp-_Ho|0)+1|0)-_Hk|0);});break;case 2:return new F(function(){return _pn(B(_uk(_Hs,_Gb)),((_Hp-_Ho|0)+1|0)-_Hk|0);});break;default:if(!(B(_nC(_Hs))&1)){return new F(function(){return _pn(_Hs,((_Hp-_Ho|0)+1|0)-_Hk|0);});}else{return new F(function(){return _pn(B(_uk(_Hs,_Gb)),((_Hp-_Ho|0)+1|0)-_Hk|0);});}}}else{return new F(function(){return _pn(_Hl, -_Ho);});}}}else{var _Ht=B(_GF(_Hl))-_Ho|0,_Hu=function(_Hv){var _Hw=function(_Hx,_Hy){if(!B(_vS(B(_Go(_Hy,_Hk)),_Hx))){return new F(function(){return _Gs(_Hv-_Hk|0,_Hx,_Hy);});}else{return new F(function(){return _Gs((_Hv-_Hk|0)+1|0,_Hx,B(_Go(_Hy,1)));});}};if(_Hv>=_Hk){if(_Hv!=_Hk){return new F(function(){return _Hw(_Hl,new T(function(){return B(_Go(_Hm,_Hv-_Hk|0));}));});}else{return new F(function(){return _Hw(_Hl,_Hm);});}}else{return new F(function(){return _Hw(new T(function(){return B(_Go(_Hl,_Hk-_Hv|0));}),_Hm);});}};if(_Hj>_Ht){return new F(function(){return _Hu(_Hj);});}else{return new F(function(){return _Hu(_Ht);});}}},_Hz=new T(function(){return 0/0;}),_HA=new T(function(){return -1/0;}),_HB=new T(function(){return 1/0;}),_HC=function(_HD,_HE){if(!B(_pr(_HE,_pJ))){if(!B(_pr(_HD,_pJ))){if(!B(_82(_HD,_pJ))){return new F(function(){return _Hi(-1021,53,_HD,_HE);});}else{return  -B(_Hi(-1021,53,B(_uu(_HD)),_HE));}}else{return E(_pI);}}else{return (!B(_pr(_HD,_pJ)))?(!B(_82(_HD,_pJ)))?E(_HB):E(_HA):E(_Hz);}},_HF=function(_HG){var _HH=E(_HG);switch(_HH._){case 3:var _HI=_HH.a;return (!B(_rU(_HI,_DX)))?(!B(_rU(_HI,_DW)))?E(_G8):E(_DT):E(_DP);case 5:var _HJ=B(_FS(_DZ,_DY,_HH.a));if(!_HJ._){return E(_DP);}else{var _HK=new T(function(){var _HL=E(_HJ.a);return B(_HC(_HL.a,_HL.b));});return function(_HM,_HN){return new F(function(){return A1(_HN,_HK);});};}break;default:return E(_G8);}},_HO=function(_HP){var _HQ=function(_HR){return E(new T2(3,_HP,_sq));};return new T1(1,function(_HS){return new F(function(){return A2(_B8,_HS,_HQ);});});},_HT=new T(function(){return B(A3(_Dt,_HF,_CY,_HO));}),_HU=new T(function(){return B(unCStr("NaN"));}),_HV=new T(function(){return B(_r6(_HT,_HU));}),_HW=function(_HX){while(1){var _HY=B((function(_HZ){var _I0=E(_HZ);if(!_I0._){return __Z;}else{var _I1=_I0.b,_I2=E(_I0.a);if(!E(_I2.b)._){return new T2(1,_I2.a,new T(function(){return B(_HW(_I1));}));}else{_HX=_I1;return __continue;}}})(_HX));if(_HY!=__continue){return _HY;}}},_I3=new T(function(){return B(_HW(_HV));}),_I4=new T(function(){return B(unCStr("Infinity"));}),_I5=new T(function(){return B(_r6(_HT,_I4));}),_I6=new T(function(){return B(_HW(_I5));}),_I7=0,_I8=new T1(0,2),_I9=function(_Ia,_Ib,_Ic,_){while(1){if(!addrEq(_Ib,_Ia)){var _Id=readOffAddr("w8",1,_Ib,0),_Ie=plusAddr(_Ib,-1),_If=new T2(1,_Id,_Ic);_Ib=_Ie;_Ic=_If;continue;}else{return _Ic;}}},_Ig=function(_Ih,_Ii,_Ij,_Ik,_Il){if(_Ik>100){var _Im=B(_I9(plusAddr(_Ih,_Ij-1|0),plusAddr(_Ih,(_Ij-1|0)+100|0),new T(function(){return B(_Ig(_Ih,_Ii,_Ij+100|0,_Ik-100|0,_Il));}),_));return E(_Im);}else{var _In=B(_I9(plusAddr(_Ih,_Ij-1|0),plusAddr(_Ih,(_Ij-1|0)+_Ik|0),_Il,_));return E(_In);}},_Io=function(_Ip){var _Iq=E(_Ip);return new F(function(){return _Ig(_Iq.a,_Iq.b,_Iq.c,_Iq.d,_M);});},_Ir=function(_Is){return new F(function(){return _Io(_Is);});},_It=function(_Iu,_Iv,_Iw,_Ix,_Iy,_Iz,_IA,_IB){var _IC=B(_8B(_Iu,_Iw,_Ix,_Iy,_Iz,_IA,_IB)),_ID=new T(function(){return B(A1(_Iv,new T(function(){return B(_Ir(_IC.a));})));}),_IE=new T(function(){var _IF=E(_ID),_IG=_IF.d,_IH=_IF.e,_II=_IF.f,_IJ=E(_IF.c);if(!_IJ){if(!B(_pr(_IG,_q6))){var _IK=B(_pK(_nT,Math.pow(2,E(_IH)-1|0))),_IL=_IK.a;if(E(_IK.b)>=0){return B(_pn(_IG,((1-E(_IL)|0)-E(_II)|0)+1|0));}else{return B(_pn(_IG,((1-(E(_IL)-1|0)|0)-E(_II)|0)+1|0));}}else{return E(_I7);}}else{var _IM=E(_IH);if(_IJ!=(B(_q0(_I8,_IM))-1|0)){var _IN=B(_pK(_nT,Math.pow(2,_IM-1|0))),_IO=_IN.a;if(E(_IN.b)>=0){var _IP=E(_II);return B(_pn(B(_uk(_IG,B(_Go(_q5,_IP)))),((_IJ+1|0)-E(_IO)|0)-_IP|0));}else{var _IQ=E(_II);return B(_pn(B(_uk(_IG,B(_Go(_q5,_IQ)))),((_IJ+1|0)-(E(_IO)-1|0)|0)-_IQ|0));}}else{if(!B(_pr(_IG,_q6))){var _IR=E(_I3);if(!_IR._){return E(_q8);}else{if(!E(_IR.b)._){return E(_IR.a);}else{return E(_qa);}}}else{var _IS=E(_I6);if(!_IS._){return E(_q8);}else{if(!E(_IS.b)._){return E(_IS.a);}else{return E(_qa);}}}}}});return new T2(0,new T(function(){if(!E(E(_ID).b)){return E(_IE);}else{return  -E(_IE);}}),_IC.b);},_IT=new T1(0,1),_IU=function(_IV,_IW){var _IX=E(_IV);return new T2(0,_IX,new T(function(){var _IY=B(_IU(B(_uk(_IX,_IW)),_IW));return new T2(1,_IY.a,_IY.b);}));},_IZ=function(_J0){var _J1=B(_IU(_J0,_IT));return new T2(1,_J1.a,_J1.b);},_J2=function(_J3,_J4){var _J5=B(_IU(_J3,new T(function(){return B(_EB(_J4,_J3));})));return new T2(1,_J5.a,_J5.b);},_J6=new T1(0,0),_J7=function(_J8,_J9,_Ja){if(!B(_Ff(_J9,_J6))){var _Jb=function(_Jc){return (!B(_82(_Jc,_Ja)))?new T2(1,_Jc,new T(function(){return B(_Jb(B(_uk(_Jc,_J9))));})):__Z;};return new F(function(){return _Jb(_J8);});}else{var _Jd=function(_Je){return (!B(_FD(_Je,_Ja)))?new T2(1,_Je,new T(function(){return B(_Jd(B(_uk(_Je,_J9))));})):__Z;};return new F(function(){return _Jd(_J8);});}},_Jf=function(_Jg,_Jh,_Ji){return new F(function(){return _J7(_Jg,B(_EB(_Jh,_Jg)),_Ji);});},_Jj=function(_Jk,_Jl){return new F(function(){return _J7(_Jk,_IT,_Jl);});},_Jm=function(_Jn){return new F(function(){return _nC(_Jn);});},_Jo=function(_Jp){return new F(function(){return _EB(_Jp,_IT);});},_Jq=function(_Jr){return new F(function(){return _uk(_Jr,_IT);});},_Js=function(_Jt){return new F(function(){return _8h(E(_Jt));});},_Ju={_:0,a:_Jq,b:_Jo,c:_Js,d:_Jm,e:_IZ,f:_J2,g:_Jj,h:_Jf},_Jv=function(_Jw,_Jx){while(1){var _Jy=E(_Jw);if(!_Jy._){var _Jz=E(_Jy.a);if(_Jz==(-2147483648)){_Jw=new T1(1,I_fromInt(-2147483648));continue;}else{var _JA=E(_Jx);if(!_JA._){return new T1(0,B(_lQ(_Jz,_JA.a)));}else{_Jw=new T1(1,I_fromInt(_Jz));_Jx=_JA;continue;}}}else{var _JB=_Jy.a,_JC=E(_Jx);return (_JC._==0)?new T1(1,I_div(_JB,I_fromInt(_JC.a))):new T1(1,I_div(_JB,_JC.a));}}},_JD=function(_JE,_JF){if(!B(_pr(_JF,_oB))){return new F(function(){return _Jv(_JE,_JF);});}else{return E(_mr);}},_JG=function(_JH,_JI){while(1){var _JJ=E(_JH);if(!_JJ._){var _JK=E(_JJ.a);if(_JK==(-2147483648)){_JH=new T1(1,I_fromInt(-2147483648));continue;}else{var _JL=E(_JI);if(!_JL._){var _JM=_JL.a;return new T2(0,new T1(0,B(_lQ(_JK,_JM))),new T1(0,B(_mV(_JK,_JM))));}else{_JH=new T1(1,I_fromInt(_JK));_JI=_JL;continue;}}}else{var _JN=E(_JI);if(!_JN._){_JH=_JJ;_JI=new T1(1,I_fromInt(_JN.a));continue;}else{var _JO=I_divMod(_JJ.a,_JN.a);return new T2(0,new T1(1,_JO.a),new T1(1,_JO.b));}}}},_JP=function(_JQ,_JR){if(!B(_pr(_JR,_oB))){var _JS=B(_JG(_JQ,_JR));return new T2(0,_JS.a,_JS.b);}else{return E(_mr);}},_JT=function(_JU,_JV){while(1){var _JW=E(_JU);if(!_JW._){var _JX=E(_JW.a);if(_JX==(-2147483648)){_JU=new T1(1,I_fromInt(-2147483648));continue;}else{var _JY=E(_JV);if(!_JY._){return new T1(0,B(_mV(_JX,_JY.a)));}else{_JU=new T1(1,I_fromInt(_JX));_JV=_JY;continue;}}}else{var _JZ=_JW.a,_K0=E(_JV);return (_K0._==0)?new T1(1,I_mod(_JZ,I_fromInt(_K0.a))):new T1(1,I_mod(_JZ,_K0.a));}}},_K1=function(_K2,_K3){if(!B(_pr(_K3,_oB))){return new F(function(){return _JT(_K2,_K3);});}else{return E(_mr);}},_K4=function(_K5,_K6){if(!B(_pr(_K6,_oB))){return new F(function(){return _El(_K5,_K6);});}else{return E(_mr);}},_K7=function(_K8,_K9){if(!B(_pr(_K9,_oB))){var _Ka=B(_pz(_K8,_K9));return new T2(0,_Ka.a,_Ka.b);}else{return E(_mr);}},_Kb=function(_Kc){return E(_Kc);},_Kd=function(_Ke){return E(_Ke);},_Kf={_:0,a:_uk,b:_EB,c:_o3,d:_uu,e:_Eg,f:_F2,g:_Kd},_Kg=function(_Kh,_Ki){var _Kj=E(_Kh);if(!_Kj._){var _Kk=_Kj.a,_Kl=E(_Ki);return (_Kl._==0)?_Kk!=_Kl.a:(I_compareInt(_Kl.a,_Kk)==0)?false:true;}else{var _Km=_Kj.a,_Kn=E(_Ki);return (_Kn._==0)?(I_compareInt(_Km,_Kn.a)==0)?false:true:(I_compare(_Km,_Kn.a)==0)?false:true;}},_Ko=new T2(0,_pr,_Kg),_Kp=function(_Kq,_Kr){return (!B(_vS(_Kq,_Kr)))?E(_Kq):E(_Kr);},_Ks=function(_Kt,_Ku){return (!B(_vS(_Kt,_Ku)))?E(_Ku):E(_Kt);},_Kv={_:0,a:_Ko,b:_Gc,c:_82,d:_vS,e:_FD,f:_Ff,g:_Kp,h:_Ks},_Kw=function(_Kx){return new T2(0,E(_Kx),E(_nq));},_Ky=new T3(0,_Kf,_Kv,_Kw),_Kz={_:0,a:_Ky,b:_Ju,c:_K4,d:_E8,e:_JD,f:_K1,g:_K7,h:_JP,i:_Kb},_KA=function(_KB,_KC){while(1){var _KD=E(_KB);if(!_KD._){return E(_KC);}else{var _KE=B(_uk(B(_Go(_KC,8)),B(_8h(E(_KD.a)&4294967295))));_KB=_KD.b;_KC=_KE;continue;}}},_KF=function(_KG,_KH,_KI){var _KJ=imul(B(_cL(_KG,0)),8)|0,_KK=B(_pK(_Kz,Math.pow(2,_KJ-_KH|0))),_KL=_KK.a;return (E(_KK.b)>=0)?E(B(_He(B(_GY(B(_KA(_KG,_q6)),B(_EB(_KL,_q5)))),_KJ-_KI|0)).a):E(B(_He(B(_GY(B(_KA(_KG,_q6)),B(_EB(B(_EB(_KL,_q5)),_q5)))),_KJ-_KI|0)).a);},_KM={_:0,a:_lM,b:_lH,c:_lD,d:_lD,e:_l7,f:_ls,g:_gr,h:_lz},_KN={_:0,a:_nw,b:_gC,c:_nt,d:_nH,e:_nz,f:_nM,g:_nF},_KO=new T2(0,_gI,_gL),_KP={_:0,a:_KO,b:_h2,c:_he,d:_hb,e:_h8,f:_h5,g:_gP,h:_gU},_KQ=new T3(0,_KN,_KP,_nr),_KR={_:0,a:_KQ,b:_KM,c:_n6,d:_nk,e:_mA,f:_n2,g:_nc,h:_mF,i:_no},_KS=new T(function(){return B(unCStr("Invalid length of floating-point value"));}),_KT=new T(function(){return B(err(_KS));}),_KU=function(_KV){var _KW=E(_KV);switch(_KW){case 16:return 5;case 32:return 8;default:if(!B(_mV(_KW,32))){var _KX=B(_pK(_KR,4*(Math.log(_KW)/Math.log(2)))),_KY=_KX.a;return (E(_KX.b)<=0)?E(_KY)-13|0:(E(_KY)+1|0)-13|0;}else{return E(_KT);}}},_KZ=new T(function(){return B(unCStr("head"));}),_L0=new T(function(){return B(_fs(_KZ));}),_L1=function(_L2,_L3,_L4){return new T1(1,B(_KF(_L2,E(_L3),E(_L4))));},_L5=function(_L6){var _L7=new T(function(){return imul(B(_cL(_L6,0)),8)|0;}),_L8=new T(function(){return B(_KU(E(_L7)));}),_L9=new T(function(){return 1+E(_L8)|0;});return new T6(0,new T(function(){return B(_cL(_L6,0));}),new T(function(){var _La=E(_L6);if(!_La._){return E(_L0);}else{if((E(_La.a)&128)>>>0==128){return 1;}else{return 0;}}}),new T(function(){return B(_nC(new T1(1,B(_KF(_L6,1,E(_L9))))));}),new T(function(){return B(_L1(_L6,_L9,_L7));}),_L8,new T(function(){return B(_gC(_L7,_L9));}));},_Lb=function(_Lc){var _Ld=B(_L5(_Lc));return new T6(0,_Ld.a,_Ld.b,_Ld.c,_Ld.d,_Ld.e,_Ld.f);},_Le=function(_Lf,_Lg,_Lh,_Li,_Lj,_Lk){var _Ll=B(_8B(1,_Lf,_Lg,_Lh,_Li,_Lj,_Lk)),_Lm=_Ll.b,_Ln=E(_Ll.a),_Lo=_Ln.b,_Lp=readOffAddr("w8",1,plusAddr(_Ln.a,_Ln.c),0);switch(E(_Lp)){case 0:var _Lq=E(_Lm),_Lr=B(_93(_Lq.a,_Lq.b,_Lq.c,_Lq.d,_Lq.e,_Lq.f)),_Ls=B(_aA(E(_Lr.a)&4294967295,_aq,_Lr.b));return new T2(0,new T1(0,_Ls.a),_Ls.b);case 1:var _Lt=E(_Lm),_Lu=B(_93(_Lt.a,_Lt.b,_Lt.c,_Lt.d,_Lt.e,_Lt.f));return new T2(0,new T1(1,new T(function(){return E(_Lu.a)&4294967295;})),_Lu.b);case 2:var _Lv=E(_Lm),_Lw=B(_It(8,_Lb,_Lv.a,_Lv.b,_Lv.c,_Lv.d,_Lv.e,_Lv.f));return new T2(0,new T1(2,_Lw.a),_Lw.b);default:return new F(function(){return _l5(E(_Lm).f);});}},_Lx=function(_Ly){var _Lz=E(_Ly),_LA=B(_Le(_Lz.a,_Lz.b,_Lz.c,_Lz.d,_Lz.e,_Lz.f));return new T2(0,_LA.a,_LA.b);},_LB=new T(function(){return B(unCStr("Prelude.undefined"));}),_LC=new T(function(){return B(err(_LB));}),_LD=function(_LE){var _LF=E(_LE);return (_LF==1)?1:(_LF<=1)?E(_LC):(B(_LD(_LF-1|0))<<1)+1|0;},_LG=function(_LH){var _LI=E(_LH);if(_LI==1){return E(_q5);}else{if(_LI<=1){return E(_LC);}else{return new F(function(){return _uk(B(_Go(B(_LG(_LI-1|0)),1)),_q5);});}}},_LJ=function(_LK){return I_toInt(_LK)>>>0;},_LL=function(_LM){var _LN=E(_LM);if(!_LN._){return _LN.a>>>0;}else{return new F(function(){return _LJ(_LN.a);});}},_LO=function(_LP,_LQ){var _LR=E(_LQ);if(!_LR){return __Z;}else{return new F(function(){return _16(B(_LO(new T(function(){return B(_He(_LP,8));}),_LR-1|0)),new T2(1,new T(function(){return (B(_LL(_LP))&255&255)>>>0;}),_M));});}},_LS=function(_LT,_LU){while(1){var _LV=E(_LT);if(!_LV._){var _LW=_LV.a,_LX=E(_LU);if(!_LX._){return new T1(0,(_LW>>>0|_LX.a>>>0)>>>0&4294967295);}else{_LT=new T1(1,I_fromInt(_LW));_LU=_LX;continue;}}else{var _LY=E(_LU);if(!_LY._){_LT=_LV;_LU=new T1(1,I_fromInt(_LY.a));continue;}else{return new T1(1,I_or(_LV.a,_LY.a));}}}},_LZ=function(_M0,_M1,_M2,_M3,_M4,_M5){return new F(function(){return _LO(new T(function(){var _M6=E(_M4);if(!_M6){if(!E(_M1)){var _M7=E(_q6);}else{var _M7=E(_q5);}var _M8=_M7;}else{var _M9=E(_M2);if(!E(_M1)){var _Ma=B(_LS(B(_Go(_q6,_M6)),B(_8h(_M9))));}else{var _Ma=B(_LS(B(_Go(_q5,_M6)),B(_8h(_M9))));}var _M8=_Ma;}var _Mb=E(_M5);if(!_Mb){return E(_M8);}else{return B(_LS(B(_Go(_M8,_Mb)),_M3));}}),_M0);});},_Mc=0,_Md=function(_Me){var _Mf=hs_intToInt64(_Me);return E(_Mf);},_Mg=function(_Mh){var _Mi=E(_Mh);if(!_Mi._){return new F(function(){return _Md(_Mi.a);});}else{return new F(function(){return I_toInt64(_Mi.a);});}},_Mj=new T2(0,_Mc,_q6),_Mk=new T(function(){return B(_FD(_q6,_q6));}),_Ml=new T1(0,-1),_Mm=new T(function(){return B(_FD(_Ml,_q6));}),_Mn=function(_Mo,_Mp,_){while(1){var _Mq=E(_Mp);if(!_Mq._){return _0;}else{var _=writeOffAddr("w8",1,_Mo,0,E(_Mq.a)),_Mr=plusAddr(_Mo,1);_Mo=_Mr;_Mp=_Mq.b;continue;}}},_Ms=function(_Mt,_Mu){return new F(function(){return _38(function(_){var _Mv=E(_Mt);if(_Mv>=0){var _Mw=newByteArr(_Mv),_Mx=B(_Mn(_Mw,_Mu,_));return new T4(0,_Mw,new T1(2,_Mw),0,_Mv);}else{return E(_7s);}});});},_My=function(_Mz,_MA,_MB){var _MC=new T(function(){var _MD=new T(function(){var _ME=E(_Mz),_MF=new T(function(){return B(_KU(imul(_ME,8)|0));}),_MG=new T(function(){return ((imul(_ME,8)|0)-E(_MF)|0)-1|0;}),_MH=new T(function(){var _MI=B(_pk(E(_MB))),_MJ=_MI.a,_MK=_MI.b,_ML=new T(function(){return B(_EB(B(_Eg(_MJ)),B(_Go(_q5,E(_MG)))));}),_MM=new T(function(){var _MN=E(_MG),_MO=B(_pK(_nT,Math.pow(2,E(_MF)-1|0))),_MP=_MO.a;if(E(_MO.b)>=0){return (_MK+_MN|0)-(1-E(_MP)|0)|0;}else{return (_MK+_MN|0)-(1-(E(_MP)-1|0)|0)|0;}});if(!B(_pr(_MJ,_q6))){var _MQ=E(_MM);if(!E(_MQ)){return new T2(0,_Mc,new T(function(){return B(_uk(_ML,_q5));}));}else{return new T2(0,_MQ,_ML);}}else{if(!E(_MK)){return E(_Mj);}else{var _MR=E(_MM);if(!E(_MR)){return new T2(0,_Mc,new T(function(){return B(_uk(_ML,_q5));}));}else{return new T2(0,_MR,_ML);}}}});return B(_LZ(_ME,new T(function(){var _MS=E(_MB),_MT=isDoubleNaN(_MS);if(!E(_MT)){var _MU=isDoubleNegativeZero(_MS);if(!E(_MU)){if(_MS>=0){return 0;}else{return 1;}}else{return 1;}}else{var _MV=B(_pk(_MS)),_MW=_MV.a,_MX=_MV.b;if(_MX>=0){if(!B(_FD(B(_Go(_MW,_MX)),_q6))){var _MY=isDoubleNegativeZero(_MS);if(!E(_MY)){if(_MS>=0){return 0;}else{return 1;}}else{return 1;}}else{return 1;}}else{var _MZ= -_MX;if(_MZ<=52){var _N0=hs_uncheckedIShiftRA64(B(_Mg(_MW)),_MZ);if(!B(_FD(B(_8j(_N0)),_q6))){var _N1=isDoubleNegativeZero(_MS);if(!E(_N1)){if(_MS>=0){return 0;}else{return 1;}}else{return 1;}}else{return 1;}}else{if(!B(_82(_MW,_q6))){if(!E(_Mk)){var _N2=isDoubleNegativeZero(_MS);if(!E(_N2)){if(_MS>=0){return 0;}else{return 1;}}else{return 1;}}else{return 1;}}else{if(!E(_Mm)){var _N3=isDoubleNegativeZero(_MS);if(!E(_N3)){if(_MS>=0){return 0;}else{return 1;}}else{return 1;}}else{return 1;}}}}}},1),new T(function(){return B(_LD(E(_MF)))&E(E(_MH).a);},1),new T(function(){return B(_GY(B(_LG(E(_MG))),E(_MH).b));},1),_MF,_MG));});return B(A1(_MA,_MD));}),_N4=B(_Ms(new T(function(){return B(_cL(_MC,0));},1),_MC));if(_N4.d>0){var _N5=function(_N6,_N7){var _N8=E(_N7),_N9=_N8.a,_Na=_N8.b,_Nb=_N8.c,_Nc=_N8.e,_Nd=E(_N8.d);return (_Nd==0)?new T2(1,_N4,new T(function(){return B(A1(_N6,new T5(0,_N9,_Na,_Nb,0,_Nc)));})):new T2(1,new T4(0,_N9,_Na,_Nb,_Nd),new T2(1,_N4,new T(function(){return B(A1(_N6,new T5(0,_N9,_Na,_Nb+_Nd|0,0,_Nc)));})));},_Ne=E(_N5);}else{var _Ne=E(_2I);}return new T2(0,_0,_Ne);},_Nf=8,_Ng=function(_Nh){var _Ni=E(_Nh);switch(_Ni._){case 0:var _Nj=new T(function(){var _Nk=B(_cS(_cK,_Ni.a));return new T2(0,_Nk.a,E(_Nk.b));}),_Nl=function(_Nm){var _Nn=new T(function(){return B(A1(E(_Nj).b,_Nm));}),_No=new T(function(){var _Np=newByteArr(32760),_=writeOffAddr("w8",1,_Np,0,0);return B(A1(_Nn,new T5(0,_Np,new T1(2,_Np),0,1,32759)));});return function(_Nq){var _Nr=E(_Nq),_Ns=_Nr.a,_Nt=_Nr.b,_Nu=_Nr.c,_Nv=_Nr.d,_Nw=_Nr.e;if(1>_Nw){var _Nx=E(_Nv);if(!_Nx){var _Ny=newByteArr(32760),_=writeOffAddr("w8",1,_Ny,0,0);return new F(function(){return A1(_Nn,new T5(0,_Ny,new T1(2,_Ny),0,1,32759));});}else{return new T2(1,new T4(0,_Ns,_Nt,_Nu,_Nx),_No);}}else{var _=writeOffAddr("w8",1,plusAddr(_Ns,_Nu+_Nv|0),0,0);return new F(function(){return A1(_Nn,new T5(0,_Ns,_Nt,_Nu,_Nv+1|0,_Nw-1|0));});}};};return new T2(0,new T(function(){return E(E(_Nj).a);}),_Nl);case 1:var _Nz=new T(function(){var _NA=B(_3M(E(_Ni.a)>>>0));return new T2(0,_NA.a,E(_NA.b));}),_NB=function(_NC){var _ND=new T(function(){return B(A1(E(_Nz).b,_NC));}),_NE=new T(function(){var _NF=newByteArr(32760),_=writeOffAddr("w8",1,_NF,0,1);return B(A1(_ND,new T5(0,_NF,new T1(2,_NF),0,1,32759)));});return function(_NG){var _NH=E(_NG),_NI=_NH.a,_NJ=_NH.b,_NK=_NH.c,_NL=_NH.d,_NM=_NH.e;if(1>_NM){var _NN=E(_NL);if(!_NN){var _NO=newByteArr(32760),_=writeOffAddr("w8",1,_NO,0,1);return new F(function(){return A1(_ND,new T5(0,_NO,new T1(2,_NO),0,1,32759));});}else{return new T2(1,new T4(0,_NI,_NJ,_NK,_NN),_NE);}}else{var _=writeOffAddr("w8",1,plusAddr(_NI,_NK+_NL|0),0,1);return new F(function(){return A1(_ND,new T5(0,_NI,_NJ,_NK,_NL+1|0,_NM-1|0));});}};};return new T2(0,new T(function(){return E(E(_Nz).a);}),_NB);default:var _NP=new T(function(){var _NQ=B(_My(_Nf,_2I,_Ni.a));return new T2(0,_NQ.a,E(_NQ.b));}),_NR=function(_NS){var _NT=new T(function(){return B(A1(E(_NP).b,_NS));}),_NU=new T(function(){var _NV=newByteArr(32760),_=writeOffAddr("w8",1,_NV,0,2);return B(A1(_NT,new T5(0,_NV,new T1(2,_NV),0,1,32759)));});return function(_NW){var _NX=E(_NW),_NY=_NX.a,_NZ=_NX.b,_O0=_NX.c,_O1=_NX.d,_O2=_NX.e;if(1>_O2){var _O3=E(_O1);if(!_O3){var _O4=newByteArr(32760),_=writeOffAddr("w8",1,_O4,0,2);return new F(function(){return A1(_NT,new T5(0,_O4,new T1(2,_O4),0,1,32759));});}else{return new T2(1,new T4(0,_NY,_NZ,_O0,_O3),_NU);}}else{var _=writeOffAddr("w8",1,plusAddr(_NY,_O0+_O1|0),0,2);return new F(function(){return A1(_NT,new T5(0,_NY,_NZ,_O0,_O1+1|0,_O2-1|0));});}};};return new T2(0,new T(function(){return E(E(_NP).a);}),_NR);}},_O5=function(_O6){var _O7=B(_Ng(_O6));return new T2(0,_O7.a,E(_O7.b));},_O8=new T2(0,_O5,_Lx),_O9=-4,_Oa=function(_Ob){var _Oc=E(_Ob);return (_Oc._==0)?__Z:new T2(1,new T2(0,_O9,_Oc.a),new T(function(){return B(_Oa(_Oc.b));}));},_Od=function(_Oe,_Of,_Og,_Oh,_Oi,_Oj){var _Ok=B(_93(_Oe,_Of,_Og,_Oh,_Oi,_Oj)),_Ol=B(_aA(E(_Ok.a)&4294967295,_iH,_Ok.b)),_Om=E(_Ol.b),_On=B(_93(_Om.a,_Om.b,_Om.c,_Om.d,_Om.e,_Om.f)),_Oo=new T(function(){return new T2(0,new T(function(){return B(_Oa(_Ol.a));}),E(_On.a)&4294967295);});return new T2(0,_Oo,_On.b);},_Op=function(_Oq){var _Or=E(_Oq),_Os=B(_Od(_Or.a,_Or.b,_Or.c,_Or.d,_Or.e,_Or.f));return new T2(0,_Os.a,_Os.b);},_Ot=function(_Ou){return new F(function(){return _l2(_l1,_Ou);});},_Ov=function(_Ow,_Ox,_Oy,_Oz,_OA,_OB){var _OC=B(_8B(1,_Ow,_Ox,_Oy,_Oz,_OA,_OB)),_OD=_OC.b,_OE=E(_OC.a),_OF=_OE.b,_OG=readOffAddr("w8",1,plusAddr(_OE.a,_OE.c),0);switch(E(_OG)){case 0:var _OH=E(_OD),_OI=B(_93(_OH.a,_OH.b,_OH.c,_OH.d,_OH.e,_OH.f)),_OJ=E(_OI.b),_OK=B(_93(_OJ.a,_OJ.b,_OJ.c,_OJ.d,_OJ.e,_OJ.f)),_OL=B(_aA(E(_OK.a)&4294967295,_Op,_OK.b));return new T2(0,new T(function(){return new T2(0,E(_OI.a)&4294967295,_OL.a);}),_OL.b);case 1:var _OM=E(_OD),_ON=B(_93(_OM.a,_OM.b,_OM.c,_OM.d,_OM.e,_OM.f));return new T2(0,new T(function(){return new T1(1,E(_ON.a)&4294967295);}),_ON.b);default:return new F(function(){return _Ot(E(_OD).f);});}},_OO=function(_OP){var _OQ=E(_OP),_OR=B(_Ov(_OQ.a,_OQ.b,_OQ.c,_OQ.d,_OQ.e,_OQ.f));return new T2(0,_OR.a,_OR.b);},_OS=function(_OT){return E(E(_OT).b);},_OU=function(_OV,_OW){var _OX=new T(function(){return E(B(_cS(_iO,new T(function(){return B(_2Q(_OS,_OV));}))).b);}),_OY=new T(function(){var _OZ=B(_3M(_OW>>>0));return new T2(0,_OZ.a,E(_OZ.b));}),_P0=function(_P1){return new F(function(){return A1(_OX,new T(function(){return B(A1(E(_OY).b,_P1));}));});};return new T2(0,new T(function(){return E(E(_OY).a);}),_P0);},_P2=function(_P3){var _P4=E(_P3),_P5=B(_OU(_P4.a,_P4.b));return new T2(0,_P5.a,E(_P5.b));},_P6=new T2(0,_P2,_Op),_P7=new T(function(){return B(_r3("src/runtime/haskell/PGF/Binary.hs:(243,3)-(244,51)|function put"));}),_P8=function(_P9){var _Pa=E(_P9);switch(_Pa._){case 0:var _Pb=new T(function(){return E(B(_3M(_Pa.a>>>0)).b);}),_Pc=new T(function(){var _Pd=B(_cS(_P6,_Pa.b));return new T2(0,_Pd.a,E(_Pd.b));}),_Pe=function(_Pf){var _Pg=new T(function(){return B(A1(_Pb,new T(function(){return B(A1(E(_Pc).b,_Pf));})));}),_Ph=new T(function(){var _Pi=newByteArr(32760),_=writeOffAddr("w8",1,_Pi,0,0);return B(A1(_Pg,new T5(0,_Pi,new T1(2,_Pi),0,1,32759)));});return function(_Pj){var _Pk=E(_Pj),_Pl=_Pk.a,_Pm=_Pk.b,_Pn=_Pk.c,_Po=_Pk.d,_Pp=_Pk.e;if(1>_Pp){var _Pq=E(_Po);if(!_Pq){var _Pr=newByteArr(32760),_=writeOffAddr("w8",1,_Pr,0,0);return new F(function(){return A1(_Pg,new T5(0,_Pr,new T1(2,_Pr),0,1,32759));});}else{return new T2(1,new T4(0,_Pl,_Pm,_Pn,_Pq),_Ph);}}else{var _=writeOffAddr("w8",1,plusAddr(_Pl,_Pn+_Po|0),0,0);return new F(function(){return A1(_Pg,new T5(0,_Pl,_Pm,_Pn,_Po+1|0,_Pp-1|0));});}};};return new T2(0,new T(function(){return E(E(_Pc).a);}),_Pe);case 1:var _Ps=new T(function(){var _Pt=B(_3M(_Pa.a>>>0));return new T2(0,_Pt.a,E(_Pt.b));}),_Pu=function(_Pv){var _Pw=new T(function(){return B(A1(E(_Ps).b,_Pv));}),_Px=new T(function(){var _Py=newByteArr(32760),_=writeOffAddr("w8",1,_Py,0,1);return B(A1(_Pw,new T5(0,_Py,new T1(2,_Py),0,1,32759)));});return function(_Pz){var _PA=E(_Pz),_PB=_PA.a,_PC=_PA.b,_PD=_PA.c,_PE=_PA.d,_PF=_PA.e;if(1>_PF){var _PG=E(_PE);if(!_PG){var _PH=newByteArr(32760),_=writeOffAddr("w8",1,_PH,0,1);return new F(function(){return A1(_Pw,new T5(0,_PH,new T1(2,_PH),0,1,32759));});}else{return new T2(1,new T4(0,_PB,_PC,_PD,_PG),_Px);}}else{var _=writeOffAddr("w8",1,plusAddr(_PB,_PD+_PE|0),0,1);return new F(function(){return A1(_Pw,new T5(0,_PB,_PC,_PD,_PE+1|0,_PF-1|0));});}};};return new T2(0,new T(function(){return E(E(_Ps).a);}),_Pu);default:return E(_P7);}},_PI=function(_PJ){var _PK=B(_P8(_PJ));return new T2(0,_PK.a,E(_PK.b));},_PL=new T2(0,_PI,_OO),_PM=new T0(1),_PN=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_PO=function(_PP){return new F(function(){return err(_PN);});},_PQ=new T(function(){return B(_PO(_));}),_PR=function(_PS,_PT,_PU){var _PV=E(_PU);if(!_PV._){var _PW=_PV.a,_PX=E(_PT);if(!_PX._){var _PY=_PX.a,_PZ=_PX.b;if(_PY<=(imul(3,_PW)|0)){return new T4(0,(1+_PY|0)+_PW|0,E(_PS),E(_PX),E(_PV));}else{var _Q0=E(_PX.c);if(!_Q0._){var _Q1=_Q0.a,_Q2=E(_PX.d);if(!_Q2._){var _Q3=_Q2.a,_Q4=_Q2.b,_Q5=_Q2.c;if(_Q3>=(imul(2,_Q1)|0)){var _Q6=function(_Q7){var _Q8=E(_Q2.d);return (_Q8._==0)?new T4(0,(1+_PY|0)+_PW|0,E(_Q4),E(new T4(0,(1+_Q1|0)+_Q7|0,E(_PZ),E(_Q0),E(_Q5))),E(new T4(0,(1+_PW|0)+_Q8.a|0,E(_PS),E(_Q8),E(_PV)))):new T4(0,(1+_PY|0)+_PW|0,E(_Q4),E(new T4(0,(1+_Q1|0)+_Q7|0,E(_PZ),E(_Q0),E(_Q5))),E(new T4(0,1+_PW|0,E(_PS),E(_PM),E(_PV))));},_Q9=E(_Q5);if(!_Q9._){return new F(function(){return _Q6(_Q9.a);});}else{return new F(function(){return _Q6(0);});}}else{return new T4(0,(1+_PY|0)+_PW|0,E(_PZ),E(_Q0),E(new T4(0,(1+_PW|0)+_Q3|0,E(_PS),E(_Q2),E(_PV))));}}else{return E(_PQ);}}else{return E(_PQ);}}}else{return new T4(0,1+_PW|0,E(_PS),E(_PM),E(_PV));}}else{var _Qa=E(_PT);if(!_Qa._){var _Qb=_Qa.a,_Qc=_Qa.b,_Qd=_Qa.d,_Qe=E(_Qa.c);if(!_Qe._){var _Qf=_Qe.a,_Qg=E(_Qd);if(!_Qg._){var _Qh=_Qg.a,_Qi=_Qg.b,_Qj=_Qg.c;if(_Qh>=(imul(2,_Qf)|0)){var _Qk=function(_Ql){var _Qm=E(_Qg.d);return (_Qm._==0)?new T4(0,1+_Qb|0,E(_Qi),E(new T4(0,(1+_Qf|0)+_Ql|0,E(_Qc),E(_Qe),E(_Qj))),E(new T4(0,1+_Qm.a|0,E(_PS),E(_Qm),E(_PM)))):new T4(0,1+_Qb|0,E(_Qi),E(new T4(0,(1+_Qf|0)+_Ql|0,E(_Qc),E(_Qe),E(_Qj))),E(new T4(0,1,E(_PS),E(_PM),E(_PM))));},_Qn=E(_Qj);if(!_Qn._){return new F(function(){return _Qk(_Qn.a);});}else{return new F(function(){return _Qk(0);});}}else{return new T4(0,1+_Qb|0,E(_Qc),E(_Qe),E(new T4(0,1+_Qh|0,E(_PS),E(_Qg),E(_PM))));}}else{return new T4(0,3,E(_Qc),E(_Qe),E(new T4(0,1,E(_PS),E(_PM),E(_PM))));}}else{var _Qo=E(_Qd);return (_Qo._==0)?new T4(0,3,E(_Qo.b),E(new T4(0,1,E(_Qc),E(_PM),E(_PM))),E(new T4(0,1,E(_PS),E(_PM),E(_PM)))):new T4(0,2,E(_PS),E(_Qa),E(_PM));}}else{return new T4(0,1,E(_PS),E(_PM),E(_PM));}}},_Qp=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_Qq=function(_Qr){return new F(function(){return err(_Qp);});},_Qs=new T(function(){return B(_Qq(_));}),_Qt=function(_Qu,_Qv,_Qw){var _Qx=E(_Qv);if(!_Qx._){var _Qy=_Qx.a,_Qz=E(_Qw);if(!_Qz._){var _QA=_Qz.a,_QB=_Qz.b;if(_QA<=(imul(3,_Qy)|0)){return new T4(0,(1+_Qy|0)+_QA|0,E(_Qu),E(_Qx),E(_Qz));}else{var _QC=E(_Qz.c);if(!_QC._){var _QD=_QC.a,_QE=_QC.b,_QF=_QC.c,_QG=E(_Qz.d);if(!_QG._){var _QH=_QG.a;if(_QD>=(imul(2,_QH)|0)){var _QI=function(_QJ){var _QK=E(_Qu),_QL=E(_QC.d);return (_QL._==0)?new T4(0,(1+_Qy|0)+_QA|0,E(_QE),E(new T4(0,(1+_Qy|0)+_QJ|0,E(_QK),E(_Qx),E(_QF))),E(new T4(0,(1+_QH|0)+_QL.a|0,E(_QB),E(_QL),E(_QG)))):new T4(0,(1+_Qy|0)+_QA|0,E(_QE),E(new T4(0,(1+_Qy|0)+_QJ|0,E(_QK),E(_Qx),E(_QF))),E(new T4(0,1+_QH|0,E(_QB),E(_PM),E(_QG))));},_QM=E(_QF);if(!_QM._){return new F(function(){return _QI(_QM.a);});}else{return new F(function(){return _QI(0);});}}else{return new T4(0,(1+_Qy|0)+_QA|0,E(_QB),E(new T4(0,(1+_Qy|0)+_QD|0,E(_Qu),E(_Qx),E(_QC))),E(_QG));}}else{return E(_Qs);}}else{return E(_Qs);}}}else{return new T4(0,1+_Qy|0,E(_Qu),E(_Qx),E(_PM));}}else{var _QN=E(_Qw);if(!_QN._){var _QO=_QN.a,_QP=_QN.b,_QQ=_QN.d,_QR=E(_QN.c);if(!_QR._){var _QS=_QR.a,_QT=_QR.b,_QU=_QR.c,_QV=E(_QQ);if(!_QV._){var _QW=_QV.a;if(_QS>=(imul(2,_QW)|0)){var _QX=function(_QY){var _QZ=E(_Qu),_R0=E(_QR.d);return (_R0._==0)?new T4(0,1+_QO|0,E(_QT),E(new T4(0,1+_QY|0,E(_QZ),E(_PM),E(_QU))),E(new T4(0,(1+_QW|0)+_R0.a|0,E(_QP),E(_R0),E(_QV)))):new T4(0,1+_QO|0,E(_QT),E(new T4(0,1+_QY|0,E(_QZ),E(_PM),E(_QU))),E(new T4(0,1+_QW|0,E(_QP),E(_PM),E(_QV))));},_R1=E(_QU);if(!_R1._){return new F(function(){return _QX(_R1.a);});}else{return new F(function(){return _QX(0);});}}else{return new T4(0,1+_QO|0,E(_QP),E(new T4(0,1+_QS|0,E(_Qu),E(_PM),E(_QR))),E(_QV));}}else{return new T4(0,3,E(_QT),E(new T4(0,1,E(_Qu),E(_PM),E(_PM))),E(new T4(0,1,E(_QP),E(_PM),E(_PM))));}}else{var _R2=E(_QQ);return (_R2._==0)?new T4(0,3,E(_QP),E(new T4(0,1,E(_Qu),E(_PM),E(_PM))),E(_R2)):new T4(0,2,E(_Qu),E(_PM),E(_QN));}}else{return new T4(0,1,E(_Qu),E(_PM),E(_PM));}}},_R3=function(_R4){return new T4(0,1,E(_R4),E(_PM),E(_PM));},_R5=function(_R6,_R7){var _R8=E(_R7);if(!_R8._){return new F(function(){return _PR(_R8.b,B(_R5(_R6,_R8.c)),_R8.d);});}else{return new F(function(){return _R3(_R6);});}},_R9=function(_Ra,_Rb){var _Rc=E(_Rb);if(!_Rc._){return new F(function(){return _Qt(_Rc.b,_Rc.c,B(_R9(_Ra,_Rc.d)));});}else{return new F(function(){return _R3(_Ra);});}},_Rd=function(_Re,_Rf,_Rg,_Rh,_Ri){return new F(function(){return _Qt(_Rg,_Rh,B(_R9(_Re,_Ri)));});},_Rj=function(_Rk,_Rl,_Rm,_Rn,_Ro){return new F(function(){return _PR(_Rm,B(_R5(_Rk,_Rn)),_Ro);});},_Rp=function(_Rq,_Rr,_Rs,_Rt,_Ru,_Rv){var _Rw=E(_Rr);if(!_Rw._){var _Rx=_Rw.a,_Ry=_Rw.b,_Rz=_Rw.c,_RA=_Rw.d;if((imul(3,_Rx)|0)>=_Rs){if((imul(3,_Rs)|0)>=_Rx){return new T4(0,(_Rx+_Rs|0)+1|0,E(_Rq),E(_Rw),E(new T4(0,_Rs,E(_Rt),E(_Ru),E(_Rv))));}else{return new F(function(){return _Qt(_Ry,_Rz,B(_Rp(_Rq,_RA,_Rs,_Rt,_Ru,_Rv)));});}}else{return new F(function(){return _PR(_Rt,B(_RB(_Rq,_Rx,_Ry,_Rz,_RA,_Ru)),_Rv);});}}else{return new F(function(){return _Rj(_Rq,_Rs,_Rt,_Ru,_Rv);});}},_RB=function(_RC,_RD,_RE,_RF,_RG,_RH){var _RI=E(_RH);if(!_RI._){var _RJ=_RI.a,_RK=_RI.b,_RL=_RI.c,_RM=_RI.d;if((imul(3,_RD)|0)>=_RJ){if((imul(3,_RJ)|0)>=_RD){return new T4(0,(_RD+_RJ|0)+1|0,E(_RC),E(new T4(0,_RD,E(_RE),E(_RF),E(_RG))),E(_RI));}else{return new F(function(){return _Qt(_RE,_RF,B(_Rp(_RC,_RG,_RJ,_RK,_RL,_RM)));});}}else{return new F(function(){return _PR(_RK,B(_RB(_RC,_RD,_RE,_RF,_RG,_RL)),_RM);});}}else{return new F(function(){return _Rd(_RC,_RD,_RE,_RF,_RG);});}},_RN=function(_RO,_RP,_RQ){var _RR=E(_RP);if(!_RR._){var _RS=_RR.a,_RT=_RR.b,_RU=_RR.c,_RV=_RR.d,_RW=E(_RQ);if(!_RW._){var _RX=_RW.a,_RY=_RW.b,_RZ=_RW.c,_S0=_RW.d;if((imul(3,_RS)|0)>=_RX){if((imul(3,_RX)|0)>=_RS){return new T4(0,(_RS+_RX|0)+1|0,E(_RO),E(_RR),E(_RW));}else{return new F(function(){return _Qt(_RT,_RU,B(_Rp(_RO,_RV,_RX,_RY,_RZ,_S0)));});}}else{return new F(function(){return _PR(_RY,B(_RB(_RO,_RS,_RT,_RU,_RV,_RZ)),_S0);});}}else{return new F(function(){return _Rd(_RO,_RS,_RT,_RU,_RV);});}}else{return new F(function(){return _R5(_RO,_RQ);});}},_S1=function(_S2,_S3,_S4){var _S5=E(_S2);if(_S5==1){return new T2(0,new T(function(){return new T4(0,1,E(_S3),E(_PM),E(_PM));}),_S4);}else{var _S6=B(_S1(_S5>>1,_S3,_S4)),_S7=_S6.a,_S8=E(_S6.b);if(!_S8._){return new T2(0,_S7,_M);}else{var _S9=B(_Sa(_S5>>1,_S8.b));return new T2(0,new T(function(){return B(_RN(_S8.a,_S7,_S9.a));}),_S9.b);}}},_Sa=function(_Sb,_Sc){var _Sd=E(_Sc);if(!_Sd._){return new T2(0,_PM,_M);}else{var _Se=_Sd.a,_Sf=_Sd.b,_Sg=E(_Sb);if(_Sg==1){return new T2(0,new T(function(){return new T4(0,1,E(_Se),E(_PM),E(_PM));}),_Sf);}else{var _Sh=B(_S1(_Sg>>1,_Se,_Sf)),_Si=_Sh.a,_Sj=E(_Sh.b);if(!_Sj._){return new T2(0,_Si,_M);}else{var _Sk=B(_Sa(_Sg>>1,_Sj.b));return new T2(0,new T(function(){return B(_RN(_Sj.a,_Si,_Sk.a));}),_Sk.b);}}}},_Sl=function(_Sm,_Sn,_So){while(1){var _Sp=E(_So);if(!_Sp._){return E(_Sn);}else{var _Sq=B(_Sa(_Sm,_Sp.b)),_Sr=_Sm<<1,_Ss=B(_RN(_Sp.a,_Sn,_Sq.a));_Sm=_Sr;_Sn=_Ss;_So=_Sq.b;continue;}}},_St=function(_Su,_Sv,_Sw,_Sx,_Sy,_Sz,_SA){var _SB=B(_93(_Sv,_Sw,_Sx,_Sy,_Sz,_SA)),_SC=B(_aA(E(_SB.a)&4294967295,new T(function(){return B(_hw(_Su));}),_SB.b));return new T2(0,new T(function(){var _SD=E(_SC.a);if(!_SD._){return new T0(1);}else{return B(_Sl(1,new T4(0,1,E(_SD.a),E(_PM),E(_PM)),_SD.b));}}),_SC.b);},_SE=function(_SF){var _SG=E(_SF),_SH=B(_St(_PL,_SG.a,_SG.b,_SG.c,_SG.d,_SG.e,_SG.f));return new T2(0,_SH.a,_SH.b);},_SI=new T2(0,_0,E(_2I)),_SJ=function(_SK,_SL){var _SM=new T(function(){var _SN=new T(function(){return B(_cQ(_SK));}),_SO=function(_SP,_SQ){while(1){var _SR=B((function(_SS,_ST){var _SU=E(_ST);if(!_SU._){var _SV=new T(function(){return B(_SO(_SS,_SU.d));}),_SW=new T(function(){return E(B(A1(_SN,_SU.b)).b);}),_SX=function(_SY){return new F(function(){return A1(_SW,new T(function(){return B(A1(E(_SV).b,_SY));}));});};_SP=new T2(0,new T(function(){return E(E(_SV).a);}),E(_SX));_SQ=_SU.c;return __continue;}else{return E(_SS);}})(_SP,_SQ));if(_SR!=__continue){return _SR;}}};return B(_SO(_SI,_SL));}),_SZ=new T(function(){var _T0=E(_SL);if(!_T0._){return E(B(_3M(_T0.a>>>0)).b);}else{return E(B(_3M(0)).b);}}),_T1=function(_T2){return new F(function(){return A1(_SZ,new T(function(){return B(A1(E(_SM).b,_T2));}));});};return new T2(0,new T(function(){return E(E(_SM).a);}),_T1);},_T3=function(_T4){var _T5=B(_SJ(_PL,_T4));return new T2(0,_T5.a,E(_T5.b));},_T6=new T2(0,_T3,_SE),_T7=function(_T8){var _T9=E(_T8),_Ta=B(_93(_T9.a,_T9.b,_T9.c,_T9.d,_T9.e,_T9.f)),_Tb=B(_aA(E(_Ta.a)&4294967295,_iH,_Ta.b));return new T2(0,_Tb.a,_Tb.b);},_Tc=function(_Td){var _Te=B(_cS(_iO,_Td));return new T2(0,_Te.a,E(_Te.b));},_Tf=new T2(0,_Tc,_T7),_Tg=new T0(1),_Th=function(_Ti,_Tj,_Tk,_Tl,_Tm,_Tn,_To){while(1){var _Tp=E(_To);if(!_Tp._){var _Tq=(_Tm>>>0^_Tp.a>>>0)>>>0,_Tr=(_Tq|_Tq>>>1)>>>0,_Ts=(_Tr|_Tr>>>2)>>>0,_Tt=(_Ts|_Ts>>>4)>>>0,_Tu=(_Tt|_Tt>>>8)>>>0,_Tv=(_Tu|_Tu>>>16)>>>0,_Tw=(_Tv^_Tv>>>1)>>>0&4294967295;if(_Tl>>>0<=_Tw>>>0){return new F(function(){return _Tx(_Ti,_Tj,_Tk,new T3(0,_Tm,E(_Tn),E(_Tp)));});}else{var _Ty=_Tw>>>0,_Tz=(_Tm>>>0&((_Ty-1>>>0^4294967295)>>>0^_Ty)>>>0)>>>0&4294967295,_TA=new T4(0,_Tz,_Tw,E(_Tp.b),E(_Tn));_Tm=_Tz;_Tn=_TA;_To=_Tp.c;continue;}}else{return new F(function(){return _Tx(_Ti,_Tj,_Tk,new T3(0,_Tm,E(_Tn),E(_Tg)));});}}},_TB=function(_TC,_TD,_TE){while(1){var _TF=E(_TE);if(!_TF._){var _TG=_TF.a,_TH=_TF.b,_TI=_TF.c,_TJ=(_TG>>>0^_TC>>>0)>>>0,_TK=(_TJ|_TJ>>>1)>>>0,_TL=(_TK|_TK>>>2)>>>0,_TM=(_TL|_TL>>>4)>>>0,_TN=(_TM|_TM>>>8)>>>0,_TO=(_TN|_TN>>>16)>>>0,_TP=(_TO^_TO>>>1)>>>0&4294967295,_TQ=(_TC>>>0^_TG>>>0)>>>0,_TR=(_TQ|_TQ>>>1)>>>0,_TS=(_TR|_TR>>>2)>>>0,_TT=(_TS|_TS>>>4)>>>0,_TU=(_TT|_TT>>>8)>>>0,_TV=(_TU|_TU>>>16)>>>0,_TW=(_TV^_TV>>>1)>>>0;if(!((_TG>>>0&_TP>>>0)>>>0)){var _TX=_TP>>>0,_TY=(_TC>>>0&((_TW-1>>>0^4294967295)>>>0^_TW)>>>0)>>>0&4294967295,_TZ=new T4(0,(_TG>>>0&((_TX-1>>>0^4294967295)>>>0^_TX)>>>0)>>>0&4294967295,_TP,E(_TH),E(_TD));_TC=_TY;_TD=_TZ;_TE=_TI;continue;}else{var _U0=_TP>>>0,_TY=(_TC>>>0&((_TW-1>>>0^4294967295)>>>0^_TW)>>>0)>>>0&4294967295,_TZ=new T4(0,(_TG>>>0&((_U0-1>>>0^4294967295)>>>0^_U0)>>>0)>>>0&4294967295,_TP,E(_TD),E(_TH));_TC=_TY;_TD=_TZ;_TE=_TI;continue;}}else{return E(_TD);}}},_Tx=function(_U1,_U2,_U3,_U4){var _U5=E(_U3);if(!_U5._){return new F(function(){return _TB(_U1,new T2(1,_U1,_U2),_U4);});}else{var _U6=E(_U5.a),_U7=E(_U6.a),_U8=(_U1>>>0^_U7>>>0)>>>0,_U9=(_U8|_U8>>>1)>>>0,_Ua=(_U9|_U9>>>2)>>>0,_Ub=(_Ua|_Ua>>>4)>>>0,_Uc=(_Ub|_Ub>>>8)>>>0,_Ud=(_Uc|_Uc>>>16)>>>0;return new F(function(){return _Th(_U7,_U6.b,_U5.b,(_Ud^_Ud>>>1)>>>0&4294967295,_U1,new T2(1,_U1,_U2),_U4);});}},_Ue=function(_Uf,_Ug,_Uh,_Ui,_Uj,_Uk,_Ul){var _Um=B(_93(_Ug,_Uh,_Ui,_Uj,_Uk,_Ul)),_Un=function(_Uo){var _Up=E(_Uo),_Uq=B(_93(_Up.a,_Up.b,_Up.c,_Up.d,_Up.e,_Up.f)),_Ur=B(A2(_hw,_Uf,_Uq.b));return new T2(0,new T2(0,new T(function(){return E(_Uq.a)&4294967295;}),_Ur.a),_Ur.b);},_Us=B(_aA(E(_Um.a)&4294967295,_Un,_Um.b));return new T2(0,new T(function(){var _Ut=E(_Us.a);if(!_Ut._){return new T0(2);}else{var _Uu=E(_Ut.a);return B(_Tx(E(_Uu.a),_Uu.b,_Ut.b,_Tg));}}),_Us.b);},_Uv=function(_Uw,_Ux,_Uy){var _Uz=B(A2(_hw,_Uw,_Uy)),_UA=B(A2(_hw,_Ux,_Uz.b));return new T2(0,new T2(0,_Uz.a,_UA.a),_UA.b);},_UB=new T0(1),_UC=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_UD=function(_UE){return new F(function(){return err(_UC);});},_UF=new T(function(){return B(_UD(_));}),_UG=function(_UH,_UI,_UJ,_UK){var _UL=E(_UK);if(!_UL._){var _UM=_UL.a,_UN=E(_UJ);if(!_UN._){var _UO=_UN.a,_UP=_UN.b,_UQ=_UN.c;if(_UO<=(imul(3,_UM)|0)){return new T5(0,(1+_UO|0)+_UM|0,E(_UH),_UI,E(_UN),E(_UL));}else{var _UR=E(_UN.d);if(!_UR._){var _US=_UR.a,_UT=E(_UN.e);if(!_UT._){var _UU=_UT.a,_UV=_UT.b,_UW=_UT.c,_UX=_UT.d;if(_UU>=(imul(2,_US)|0)){var _UY=function(_UZ){var _V0=E(_UT.e);return (_V0._==0)?new T5(0,(1+_UO|0)+_UM|0,E(_UV),_UW,E(new T5(0,(1+_US|0)+_UZ|0,E(_UP),_UQ,E(_UR),E(_UX))),E(new T5(0,(1+_UM|0)+_V0.a|0,E(_UH),_UI,E(_V0),E(_UL)))):new T5(0,(1+_UO|0)+_UM|0,E(_UV),_UW,E(new T5(0,(1+_US|0)+_UZ|0,E(_UP),_UQ,E(_UR),E(_UX))),E(new T5(0,1+_UM|0,E(_UH),_UI,E(_UB),E(_UL))));},_V1=E(_UX);if(!_V1._){return new F(function(){return _UY(_V1.a);});}else{return new F(function(){return _UY(0);});}}else{return new T5(0,(1+_UO|0)+_UM|0,E(_UP),_UQ,E(_UR),E(new T5(0,(1+_UM|0)+_UU|0,E(_UH),_UI,E(_UT),E(_UL))));}}else{return E(_UF);}}else{return E(_UF);}}}else{return new T5(0,1+_UM|0,E(_UH),_UI,E(_UB),E(_UL));}}else{var _V2=E(_UJ);if(!_V2._){var _V3=_V2.a,_V4=_V2.b,_V5=_V2.c,_V6=_V2.e,_V7=E(_V2.d);if(!_V7._){var _V8=_V7.a,_V9=E(_V6);if(!_V9._){var _Va=_V9.a,_Vb=_V9.b,_Vc=_V9.c,_Vd=_V9.d;if(_Va>=(imul(2,_V8)|0)){var _Ve=function(_Vf){var _Vg=E(_V9.e);return (_Vg._==0)?new T5(0,1+_V3|0,E(_Vb),_Vc,E(new T5(0,(1+_V8|0)+_Vf|0,E(_V4),_V5,E(_V7),E(_Vd))),E(new T5(0,1+_Vg.a|0,E(_UH),_UI,E(_Vg),E(_UB)))):new T5(0,1+_V3|0,E(_Vb),_Vc,E(new T5(0,(1+_V8|0)+_Vf|0,E(_V4),_V5,E(_V7),E(_Vd))),E(new T5(0,1,E(_UH),_UI,E(_UB),E(_UB))));},_Vh=E(_Vd);if(!_Vh._){return new F(function(){return _Ve(_Vh.a);});}else{return new F(function(){return _Ve(0);});}}else{return new T5(0,1+_V3|0,E(_V4),_V5,E(_V7),E(new T5(0,1+_Va|0,E(_UH),_UI,E(_V9),E(_UB))));}}else{return new T5(0,3,E(_V4),_V5,E(_V7),E(new T5(0,1,E(_UH),_UI,E(_UB),E(_UB))));}}else{var _Vi=E(_V6);return (_Vi._==0)?new T5(0,3,E(_Vi.b),_Vi.c,E(new T5(0,1,E(_V4),_V5,E(_UB),E(_UB))),E(new T5(0,1,E(_UH),_UI,E(_UB),E(_UB)))):new T5(0,2,E(_UH),_UI,E(_V2),E(_UB));}}else{return new T5(0,1,E(_UH),_UI,E(_UB),E(_UB));}}},_Vj=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_Vk=function(_Vl){return new F(function(){return err(_Vj);});},_Vm=new T(function(){return B(_Vk(_));}),_Vn=function(_Vo,_Vp,_Vq,_Vr){var _Vs=E(_Vq);if(!_Vs._){var _Vt=_Vs.a,_Vu=E(_Vr);if(!_Vu._){var _Vv=_Vu.a,_Vw=_Vu.b,_Vx=_Vu.c;if(_Vv<=(imul(3,_Vt)|0)){return new T5(0,(1+_Vt|0)+_Vv|0,E(_Vo),_Vp,E(_Vs),E(_Vu));}else{var _Vy=E(_Vu.d);if(!_Vy._){var _Vz=_Vy.a,_VA=_Vy.b,_VB=_Vy.c,_VC=_Vy.d,_VD=E(_Vu.e);if(!_VD._){var _VE=_VD.a;if(_Vz>=(imul(2,_VE)|0)){var _VF=function(_VG){var _VH=E(_Vo),_VI=E(_Vy.e);return (_VI._==0)?new T5(0,(1+_Vt|0)+_Vv|0,E(_VA),_VB,E(new T5(0,(1+_Vt|0)+_VG|0,E(_VH),_Vp,E(_Vs),E(_VC))),E(new T5(0,(1+_VE|0)+_VI.a|0,E(_Vw),_Vx,E(_VI),E(_VD)))):new T5(0,(1+_Vt|0)+_Vv|0,E(_VA),_VB,E(new T5(0,(1+_Vt|0)+_VG|0,E(_VH),_Vp,E(_Vs),E(_VC))),E(new T5(0,1+_VE|0,E(_Vw),_Vx,E(_UB),E(_VD))));},_VJ=E(_VC);if(!_VJ._){return new F(function(){return _VF(_VJ.a);});}else{return new F(function(){return _VF(0);});}}else{return new T5(0,(1+_Vt|0)+_Vv|0,E(_Vw),_Vx,E(new T5(0,(1+_Vt|0)+_Vz|0,E(_Vo),_Vp,E(_Vs),E(_Vy))),E(_VD));}}else{return E(_Vm);}}else{return E(_Vm);}}}else{return new T5(0,1+_Vt|0,E(_Vo),_Vp,E(_Vs),E(_UB));}}else{var _VK=E(_Vr);if(!_VK._){var _VL=_VK.a,_VM=_VK.b,_VN=_VK.c,_VO=_VK.e,_VP=E(_VK.d);if(!_VP._){var _VQ=_VP.a,_VR=_VP.b,_VS=_VP.c,_VT=_VP.d,_VU=E(_VO);if(!_VU._){var _VV=_VU.a;if(_VQ>=(imul(2,_VV)|0)){var _VW=function(_VX){var _VY=E(_Vo),_VZ=E(_VP.e);return (_VZ._==0)?new T5(0,1+_VL|0,E(_VR),_VS,E(new T5(0,1+_VX|0,E(_VY),_Vp,E(_UB),E(_VT))),E(new T5(0,(1+_VV|0)+_VZ.a|0,E(_VM),_VN,E(_VZ),E(_VU)))):new T5(0,1+_VL|0,E(_VR),_VS,E(new T5(0,1+_VX|0,E(_VY),_Vp,E(_UB),E(_VT))),E(new T5(0,1+_VV|0,E(_VM),_VN,E(_UB),E(_VU))));},_W0=E(_VT);if(!_W0._){return new F(function(){return _VW(_W0.a);});}else{return new F(function(){return _VW(0);});}}else{return new T5(0,1+_VL|0,E(_VM),_VN,E(new T5(0,1+_VQ|0,E(_Vo),_Vp,E(_UB),E(_VP))),E(_VU));}}else{return new T5(0,3,E(_VR),_VS,E(new T5(0,1,E(_Vo),_Vp,E(_UB),E(_UB))),E(new T5(0,1,E(_VM),_VN,E(_UB),E(_UB))));}}else{var _W1=E(_VO);return (_W1._==0)?new T5(0,3,E(_VM),_VN,E(new T5(0,1,E(_Vo),_Vp,E(_UB),E(_UB))),E(_W1)):new T5(0,2,E(_Vo),_Vp,E(_UB),E(_VK));}}else{return new T5(0,1,E(_Vo),_Vp,E(_UB),E(_UB));}}},_W2=function(_W3,_W4){return new T5(0,1,E(_W3),_W4,E(_UB),E(_UB));},_W5=function(_W6,_W7,_W8){var _W9=E(_W8);if(!_W9._){return new F(function(){return _Vn(_W9.b,_W9.c,_W9.d,B(_W5(_W6,_W7,_W9.e)));});}else{return new F(function(){return _W2(_W6,_W7);});}},_Wa=function(_Wb,_Wc,_Wd){var _We=E(_Wd);if(!_We._){return new F(function(){return _UG(_We.b,_We.c,B(_Wa(_Wb,_Wc,_We.d)),_We.e);});}else{return new F(function(){return _W2(_Wb,_Wc);});}},_Wf=function(_Wg,_Wh,_Wi,_Wj,_Wk,_Wl,_Wm){return new F(function(){return _UG(_Wj,_Wk,B(_Wa(_Wg,_Wh,_Wl)),_Wm);});},_Wn=function(_Wo,_Wp,_Wq,_Wr,_Ws,_Wt,_Wu,_Wv){var _Ww=E(_Wq);if(!_Ww._){var _Wx=_Ww.a,_Wy=_Ww.b,_Wz=_Ww.c,_WA=_Ww.d,_WB=_Ww.e;if((imul(3,_Wx)|0)>=_Wr){if((imul(3,_Wr)|0)>=_Wx){return new T5(0,(_Wx+_Wr|0)+1|0,E(_Wo),_Wp,E(_Ww),E(new T5(0,_Wr,E(_Ws),_Wt,E(_Wu),E(_Wv))));}else{return new F(function(){return _Vn(_Wy,_Wz,_WA,B(_Wn(_Wo,_Wp,_WB,_Wr,_Ws,_Wt,_Wu,_Wv)));});}}else{return new F(function(){return _UG(_Ws,_Wt,B(_WC(_Wo,_Wp,_Wx,_Wy,_Wz,_WA,_WB,_Wu)),_Wv);});}}else{return new F(function(){return _Wf(_Wo,_Wp,_Wr,_Ws,_Wt,_Wu,_Wv);});}},_WC=function(_WD,_WE,_WF,_WG,_WH,_WI,_WJ,_WK){var _WL=E(_WK);if(!_WL._){var _WM=_WL.a,_WN=_WL.b,_WO=_WL.c,_WP=_WL.d,_WQ=_WL.e;if((imul(3,_WF)|0)>=_WM){if((imul(3,_WM)|0)>=_WF){return new T5(0,(_WF+_WM|0)+1|0,E(_WD),_WE,E(new T5(0,_WF,E(_WG),_WH,E(_WI),E(_WJ))),E(_WL));}else{return new F(function(){return _Vn(_WG,_WH,_WI,B(_Wn(_WD,_WE,_WJ,_WM,_WN,_WO,_WP,_WQ)));});}}else{return new F(function(){return _UG(_WN,_WO,B(_WC(_WD,_WE,_WF,_WG,_WH,_WI,_WJ,_WP)),_WQ);});}}else{return new F(function(){return _W5(_WD,_WE,new T5(0,_WF,E(_WG),_WH,E(_WI),E(_WJ)));});}},_WR=function(_WS,_WT,_WU,_WV){var _WW=E(_WU);if(!_WW._){var _WX=_WW.a,_WY=_WW.b,_WZ=_WW.c,_X0=_WW.d,_X1=_WW.e,_X2=E(_WV);if(!_X2._){var _X3=_X2.a,_X4=_X2.b,_X5=_X2.c,_X6=_X2.d,_X7=_X2.e;if((imul(3,_WX)|0)>=_X3){if((imul(3,_X3)|0)>=_WX){return new T5(0,(_WX+_X3|0)+1|0,E(_WS),_WT,E(_WW),E(_X2));}else{return new F(function(){return _Vn(_WY,_WZ,_X0,B(_Wn(_WS,_WT,_X1,_X3,_X4,_X5,_X6,_X7)));});}}else{return new F(function(){return _UG(_X4,_X5,B(_WC(_WS,_WT,_WX,_WY,_WZ,_X0,_X1,_X6)),_X7);});}}else{return new F(function(){return _W5(_WS,_WT,_WW);});}}else{return new F(function(){return _Wa(_WS,_WT,_WV);});}},_X8=function(_X9,_Xa,_Xb){var _Xc=E(_X9);if(_Xc==1){var _Xd=E(_Xa);return new T2(0,new T(function(){return new T5(0,1,E(_Xd.a),_Xd.b,E(_UB),E(_UB));}),_Xb);}else{var _Xe=B(_X8(_Xc>>1,_Xa,_Xb)),_Xf=_Xe.a,_Xg=E(_Xe.b);if(!_Xg._){return new T2(0,_Xf,_M);}else{var _Xh=E(_Xg.a),_Xi=B(_Xj(_Xc>>1,_Xg.b));return new T2(0,new T(function(){return B(_WR(_Xh.a,_Xh.b,_Xf,_Xi.a));}),_Xi.b);}}},_Xj=function(_Xk,_Xl){var _Xm=E(_Xl);if(!_Xm._){return new T2(0,_UB,_M);}else{var _Xn=_Xm.a,_Xo=_Xm.b,_Xp=E(_Xk);if(_Xp==1){var _Xq=E(_Xn);return new T2(0,new T(function(){return new T5(0,1,E(_Xq.a),_Xq.b,E(_UB),E(_UB));}),_Xo);}else{var _Xr=B(_X8(_Xp>>1,_Xn,_Xo)),_Xs=_Xr.a,_Xt=E(_Xr.b);if(!_Xt._){return new T2(0,_Xs,_M);}else{var _Xu=E(_Xt.a),_Xv=B(_Xj(_Xp>>1,_Xt.b));return new T2(0,new T(function(){return B(_WR(_Xu.a,_Xu.b,_Xs,_Xv.a));}),_Xv.b);}}}},_Xw=function(_Xx,_Xy,_Xz){while(1){var _XA=E(_Xz);if(!_XA._){return E(_Xy);}else{var _XB=E(_XA.a),_XC=B(_Xj(_Xx,_XA.b)),_XD=_Xx<<1,_XE=B(_WR(_XB.a,_XB.b,_Xy,_XC.a));_Xx=_XD;_Xy=_XE;_Xz=_XC.b;continue;}}},_XF=function(_XG,_XH,_XI,_XJ,_XK,_XL,_XM,_XN){var _XO=B(_93(_XI,_XJ,_XK,_XL,_XM,_XN)),_XP=B(_aA(E(_XO.a)&4294967295,function(_XQ){return new F(function(){return _Uv(_XG,_XH,_XQ);});},_XO.b));return new T2(0,new T(function(){var _XR=E(_XP.a);if(!_XR._){return new T0(1);}else{var _XS=E(_XR.a);return B(_Xw(1,new T5(0,1,E(_XS.a),_XS.b,E(_UB),E(_UB)),_XR.b));}}),_XP.b);},_XT=new T0(2),_XU=new T0(10),_XV=new T0(5),_XW=new T0(9),_XX=new T0(6),_XY=new T0(7),_XZ=new T0(8),_Y0=function(_Y1){return new F(function(){return _l2(_l1,_Y1);});},_Y2=function(_Y3){var _Y4=E(_Y3),_Y5=B(_93(_Y4.a,_Y4.b,_Y4.c,_Y4.d,_Y4.e,_Y4.f)),_Y6=B(_aA(E(_Y5.a)&4294967295,_aq,_Y5.b));return new T2(0,_Y6.a,_Y6.b);},_Y7=function(_Y8){var _Y9=E(_Y8),_Ya=B(_93(_Y9.a,_Y9.b,_Y9.c,_Y9.d,_Y9.e,_Y9.f)),_Yb=B(_aA(E(_Ya.a)&4294967295,_Yc,_Ya.b)),_Yd=E(_Yb.b),_Ye=B(_93(_Yd.a,_Yd.b,_Yd.c,_Yd.d,_Yd.e,_Yd.f)),_Yf=B(_aA(E(_Ye.a)&4294967295,_Y2,_Ye.b));return new T2(0,new T2(0,_Yb.a,_Yf.a),_Yf.b);},_Yg=function(_Yh,_Yi,_Yj,_Yk,_Yl,_Ym){var _Yn=B(_8B(1,_Yh,_Yi,_Yj,_Yk,_Yl,_Ym)),_Yo=_Yn.b,_Yp=E(_Yn.a),_Yq=_Yp.b,_Yr=readOffAddr("w8",1,plusAddr(_Yp.a,_Yp.c),0);switch(E(_Yr)){case 0:var _Ys=E(_Yo),_Yt=B(_93(_Ys.a,_Ys.b,_Ys.c,_Ys.d,_Ys.e,_Ys.f)),_Yu=E(_Yt.b),_Yv=B(_93(_Yu.a,_Yu.b,_Yu.c,_Yu.d,_Yu.e,_Yu.f));return new T2(0,new T(function(){return new T2(0,E(_Yt.a)&4294967295,E(_Yv.a)&4294967295);}),_Yv.b);case 1:var _Yw=E(_Yo),_Yx=B(_93(_Yw.a,_Yw.b,_Yw.c,_Yw.d,_Yw.e,_Yw.f)),_Yy=E(_Yx.b),_Yz=B(_93(_Yy.a,_Yy.b,_Yy.c,_Yy.d,_Yy.e,_Yy.f));return new T2(0,new T(function(){return new T2(1,E(_Yx.a)&4294967295,E(_Yz.a)&4294967295);}),_Yz.b);case 2:var _YA=E(_Yo),_YB=B(_93(_YA.a,_YA.b,_YA.c,_YA.d,_YA.e,_YA.f)),_YC=E(_YB.b),_YD=B(_93(_YC.a,_YC.b,_YC.c,_YC.d,_YC.e,_YC.f));return new T2(0,new T(function(){return new T2(2,E(_YB.a)&4294967295,E(_YD.a)&4294967295);}),_YD.b);case 3:var _YE=E(_Yo),_YF=B(_93(_YE.a,_YE.b,_YE.c,_YE.d,_YE.e,_YE.f)),_YG=B(_aA(E(_YF.a)&4294967295,_aq,_YF.b));return new T2(0,new T1(3,_YG.a),_YG.b);case 4:var _YH=E(_Yo),_YI=B(_93(_YH.a,_YH.b,_YH.c,_YH.d,_YH.e,_YH.f)),_YJ=B(_aA(E(_YI.a)&4294967295,_Yc,_YI.b)),_YK=E(_YJ.b),_YL=B(_93(_YK.a,_YK.b,_YK.c,_YK.d,_YK.e,_YK.f)),_YM=B(_aA(E(_YL.a)&4294967295,_Y7,_YL.b));return new T2(0,new T2(4,_YJ.a,_YM.a),_YM.b);case 5:return new T2(0,_XV,_Yo);case 6:return new T2(0,_XY,_Yo);case 7:return new T2(0,_XX,_Yo);case 8:return new T2(0,_XZ,_Yo);case 9:return new T2(0,_XW,_Yo);case 10:return new T2(0,_XU,_Yo);default:return new F(function(){return _Y0(E(_Yo).f);});}},_Yc=function(_YN){var _YO=E(_YN),_YP=B(_Yg(_YO.a,_YO.b,_YO.c,_YO.d,_YO.e,_YO.f));return new T2(0,_YP.a,_YP.b);},_YQ=function(_YR,_YS,_YT,_YU,_YV,_YW){var _YX=B(_93(_YR,_YS,_YT,_YU,_YV,_YW)),_YY=B(_aA(E(_YX.a)&4294967295,_Yc,_YX.b)),_YZ=E(_YY.b),_Z0=B(_93(_YZ.a,_YZ.b,_YZ.c,_YZ.d,_YZ.e,_YZ.f)),_Z1=B(_aA(E(_Z0.a)&4294967295,_Y2,_Z0.b));return new T2(0,new T2(0,_YY.a,_Z1.a),_Z1.b);},_Z2=function(_Z3){var _Z4=E(_Z3),_Z5=B(_YQ(_Z4.a,_Z4.b,_Z4.c,_Z4.d,_Z4.e,_Z4.f));return new T2(0,_Z5.a,_Z5.b);},_Z6=function(_Z7,_Z8){var _Z9=new T(function(){return E(B(_cS(_Za,_Z7)).b);}),_Zb=new T(function(){var _Zc=B(_cS(_dc,_Z8));return new T2(0,_Zc.a,E(_Zc.b));}),_Zd=function(_Ze){return new F(function(){return A1(_Z9,new T(function(){return B(A1(E(_Zb).b,_Ze));}));});};return new T2(0,new T(function(){return E(E(_Zb).a);}),_Zd);},_Zf=function(_Zg){var _Zh=E(_Zg),_Zi=B(_Z6(_Zh.a,_Zh.b));return new T2(0,_Zi.a,E(_Zi.b));},_Zj=new T(function(){return new T2(0,_Zf,_Z2);}),_Zk=function(_Zl,_Zm,_Zn,_Zo,_Zp,_Zq){if(1>_Zq){var _Zr=E(_Zp);if(!_Zr){var _Zs=newByteArr(32760),_=writeOffAddr("w8",1,_Zs,0,5);return new F(function(){return A1(_Zl,new T5(0,_Zs,new T1(2,_Zs),0,1,32759));});}else{return new T2(1,new T4(0,_Zm,_Zn,_Zo,_Zr),new T(function(){var _Zt=newByteArr(32760),_=writeOffAddr("w8",1,_Zt,0,5);return B(A1(_Zl,new T5(0,_Zt,new T1(2,_Zt),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_Zm,_Zo+_Zp|0),0,5);return new F(function(){return A1(_Zl,new T5(0,_Zm,_Zn,_Zo,_Zp+1|0,_Zq-1|0));});}},_Zu=function(_Zv,_Zw){var _Zx=E(_Zw);return new F(function(){return _Zk(_Zv,_Zx.a,_Zx.b,_Zx.c,_Zx.d,_Zx.e);});},_Zy=function(_Zz,_ZA,_ZB,_ZC,_ZD,_ZE){if(1>_ZE){var _ZF=E(_ZD);if(!_ZF){var _ZG=newByteArr(32760),_=writeOffAddr("w8",1,_ZG,0,7);return new F(function(){return A1(_Zz,new T5(0,_ZG,new T1(2,_ZG),0,1,32759));});}else{return new T2(1,new T4(0,_ZA,_ZB,_ZC,_ZF),new T(function(){var _ZH=newByteArr(32760),_=writeOffAddr("w8",1,_ZH,0,7);return B(A1(_Zz,new T5(0,_ZH,new T1(2,_ZH),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_ZA,_ZC+_ZD|0),0,7);return new F(function(){return A1(_Zz,new T5(0,_ZA,_ZB,_ZC,_ZD+1|0,_ZE-1|0));});}},_ZI=function(_ZJ,_ZK){var _ZL=E(_ZK);return new F(function(){return _Zy(_ZJ,_ZL.a,_ZL.b,_ZL.c,_ZL.d,_ZL.e);});},_ZM=function(_ZN,_ZO,_ZP,_ZQ,_ZR,_ZS){if(1>_ZS){var _ZT=E(_ZR);if(!_ZT){var _ZU=newByteArr(32760),_=writeOffAddr("w8",1,_ZU,0,6);return new F(function(){return A1(_ZN,new T5(0,_ZU,new T1(2,_ZU),0,1,32759));});}else{return new T2(1,new T4(0,_ZO,_ZP,_ZQ,_ZT),new T(function(){var _ZV=newByteArr(32760),_=writeOffAddr("w8",1,_ZV,0,6);return B(A1(_ZN,new T5(0,_ZV,new T1(2,_ZV),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_ZO,_ZQ+_ZR|0),0,6);return new F(function(){return A1(_ZN,new T5(0,_ZO,_ZP,_ZQ,_ZR+1|0,_ZS-1|0));});}},_ZW=function(_ZX,_ZY){var _ZZ=E(_ZY);return new F(function(){return _ZM(_ZX,_ZZ.a,_ZZ.b,_ZZ.c,_ZZ.d,_ZZ.e);});},_100=function(_101,_102,_103,_104,_105,_106){if(1>_106){var _107=E(_105);if(!_107){var _108=newByteArr(32760),_=writeOffAddr("w8",1,_108,0,8);return new F(function(){return A1(_101,new T5(0,_108,new T1(2,_108),0,1,32759));});}else{return new T2(1,new T4(0,_102,_103,_104,_107),new T(function(){var _109=newByteArr(32760),_=writeOffAddr("w8",1,_109,0,8);return B(A1(_101,new T5(0,_109,new T1(2,_109),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_102,_104+_105|0),0,8);return new F(function(){return A1(_101,new T5(0,_102,_103,_104,_105+1|0,_106-1|0));});}},_10a=function(_10b,_10c){var _10d=E(_10c);return new F(function(){return _100(_10b,_10d.a,_10d.b,_10d.c,_10d.d,_10d.e);});},_10e=function(_10f,_10g,_10h,_10i,_10j,_10k){if(1>_10k){var _10l=E(_10j);if(!_10l){var _10m=newByteArr(32760),_=writeOffAddr("w8",1,_10m,0,9);return new F(function(){return A1(_10f,new T5(0,_10m,new T1(2,_10m),0,1,32759));});}else{return new T2(1,new T4(0,_10g,_10h,_10i,_10l),new T(function(){var _10n=newByteArr(32760),_=writeOffAddr("w8",1,_10n,0,9);return B(A1(_10f,new T5(0,_10n,new T1(2,_10n),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_10g,_10i+_10j|0),0,9);return new F(function(){return A1(_10f,new T5(0,_10g,_10h,_10i,_10j+1|0,_10k-1|0));});}},_10o=function(_10p,_10q){var _10r=E(_10q);return new F(function(){return _10e(_10p,_10r.a,_10r.b,_10r.c,_10r.d,_10r.e);});},_10s=function(_10t,_10u,_10v,_10w,_10x,_10y){if(1>_10y){var _10z=E(_10x);if(!_10z){var _10A=newByteArr(32760),_=writeOffAddr("w8",1,_10A,0,10);return new F(function(){return A1(_10t,new T5(0,_10A,new T1(2,_10A),0,1,32759));});}else{return new T2(1,new T4(0,_10u,_10v,_10w,_10z),new T(function(){var _10B=newByteArr(32760),_=writeOffAddr("w8",1,_10B,0,10);return B(A1(_10t,new T5(0,_10B,new T1(2,_10B),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_10u,_10w+_10x|0),0,10);return new F(function(){return A1(_10t,new T5(0,_10u,_10v,_10w,_10x+1|0,_10y-1|0));});}},_10C=function(_10D,_10E){var _10F=E(_10E);return new F(function(){return _10s(_10D,_10F.a,_10F.b,_10F.c,_10F.d,_10F.e);});},_10G=function(_10H){var _10I=E(_10H);switch(_10I._){case 0:var _10J=new T(function(){return E(B(_3M(_10I.a>>>0)).b);}),_10K=new T(function(){var _10L=B(_3M(_10I.b>>>0));return new T2(0,_10L.a,E(_10L.b));}),_10M=function(_10N){var _10O=new T(function(){return B(A1(_10J,new T(function(){return B(A1(E(_10K).b,_10N));})));}),_10P=new T(function(){var _10Q=newByteArr(32760),_=writeOffAddr("w8",1,_10Q,0,0);return B(A1(_10O,new T5(0,_10Q,new T1(2,_10Q),0,1,32759)));});return function(_10R){var _10S=E(_10R),_10T=_10S.a,_10U=_10S.b,_10V=_10S.c,_10W=_10S.d,_10X=_10S.e;if(1>_10X){var _10Y=E(_10W);if(!_10Y){var _10Z=newByteArr(32760),_=writeOffAddr("w8",1,_10Z,0,0);return new F(function(){return A1(_10O,new T5(0,_10Z,new T1(2,_10Z),0,1,32759));});}else{return new T2(1,new T4(0,_10T,_10U,_10V,_10Y),_10P);}}else{var _=writeOffAddr("w8",1,plusAddr(_10T,_10V+_10W|0),0,0);return new F(function(){return A1(_10O,new T5(0,_10T,_10U,_10V,_10W+1|0,_10X-1|0));});}};};return new T2(0,new T(function(){return E(E(_10K).a);}),_10M);case 1:var _110=new T(function(){return E(B(_3M(_10I.a>>>0)).b);}),_111=new T(function(){var _112=B(_3M(_10I.b>>>0));return new T2(0,_112.a,E(_112.b));}),_113=function(_114){var _115=new T(function(){return B(A1(_110,new T(function(){return B(A1(E(_111).b,_114));})));}),_116=new T(function(){var _117=newByteArr(32760),_=writeOffAddr("w8",1,_117,0,1);return B(A1(_115,new T5(0,_117,new T1(2,_117),0,1,32759)));});return function(_118){var _119=E(_118),_11a=_119.a,_11b=_119.b,_11c=_119.c,_11d=_119.d,_11e=_119.e;if(1>_11e){var _11f=E(_11d);if(!_11f){var _11g=newByteArr(32760),_=writeOffAddr("w8",1,_11g,0,1);return new F(function(){return A1(_115,new T5(0,_11g,new T1(2,_11g),0,1,32759));});}else{return new T2(1,new T4(0,_11a,_11b,_11c,_11f),_116);}}else{var _=writeOffAddr("w8",1,plusAddr(_11a,_11c+_11d|0),0,1);return new F(function(){return A1(_115,new T5(0,_11a,_11b,_11c,_11d+1|0,_11e-1|0));});}};};return new T2(0,new T(function(){return E(E(_111).a);}),_113);case 2:var _11h=new T(function(){return E(B(_3M(_10I.a>>>0)).b);}),_11i=new T(function(){var _11j=B(_3M(_10I.b>>>0));return new T2(0,_11j.a,E(_11j.b));}),_11k=function(_11l){var _11m=new T(function(){return B(A1(_11h,new T(function(){return B(A1(E(_11i).b,_11l));})));}),_11n=new T(function(){var _11o=newByteArr(32760),_=writeOffAddr("w8",1,_11o,0,2);return B(A1(_11m,new T5(0,_11o,new T1(2,_11o),0,1,32759)));});return function(_11p){var _11q=E(_11p),_11r=_11q.a,_11s=_11q.b,_11t=_11q.c,_11u=_11q.d,_11v=_11q.e;if(1>_11v){var _11w=E(_11u);if(!_11w){var _11x=newByteArr(32760),_=writeOffAddr("w8",1,_11x,0,2);return new F(function(){return A1(_11m,new T5(0,_11x,new T1(2,_11x),0,1,32759));});}else{return new T2(1,new T4(0,_11r,_11s,_11t,_11w),_11n);}}else{var _=writeOffAddr("w8",1,plusAddr(_11r,_11t+_11u|0),0,2);return new F(function(){return A1(_11m,new T5(0,_11r,_11s,_11t,_11u+1|0,_11v-1|0));});}};};return new T2(0,new T(function(){return E(E(_11i).a);}),_11k);case 3:var _11y=new T(function(){var _11z=B(_cS(_cK,_10I.a));return new T2(0,_11z.a,E(_11z.b));}),_11A=function(_11B){var _11C=new T(function(){return B(A1(E(_11y).b,_11B));}),_11D=new T(function(){var _11E=newByteArr(32760),_=writeOffAddr("w8",1,_11E,0,3);return B(A1(_11C,new T5(0,_11E,new T1(2,_11E),0,1,32759)));});return function(_11F){var _11G=E(_11F),_11H=_11G.a,_11I=_11G.b,_11J=_11G.c,_11K=_11G.d,_11L=_11G.e;if(1>_11L){var _11M=E(_11K);if(!_11M){var _11N=newByteArr(32760),_=writeOffAddr("w8",1,_11N,0,3);return new F(function(){return A1(_11C,new T5(0,_11N,new T1(2,_11N),0,1,32759));});}else{return new T2(1,new T4(0,_11H,_11I,_11J,_11M),_11D);}}else{var _=writeOffAddr("w8",1,plusAddr(_11H,_11J+_11K|0),0,3);return new F(function(){return A1(_11C,new T5(0,_11H,_11I,_11J,_11K+1|0,_11L-1|0));});}};};return new T2(0,new T(function(){return E(E(_11y).a);}),_11A);case 4:var _11O=new T(function(){return E(B(_cS(_Za,_10I.a)).b);}),_11P=new T(function(){var _11Q=B(_cS(_Zj,_10I.b));return new T2(0,_11Q.a,E(_11Q.b));}),_11R=function(_11S){var _11T=new T(function(){return B(A1(_11O,new T(function(){return B(A1(E(_11P).b,_11S));})));}),_11U=new T(function(){var _11V=newByteArr(32760),_=writeOffAddr("w8",1,_11V,0,4);return B(A1(_11T,new T5(0,_11V,new T1(2,_11V),0,1,32759)));});return function(_11W){var _11X=E(_11W),_11Y=_11X.a,_11Z=_11X.b,_120=_11X.c,_121=_11X.d,_122=_11X.e;if(1>_122){var _123=E(_121);if(!_123){var _124=newByteArr(32760),_=writeOffAddr("w8",1,_124,0,4);return new F(function(){return A1(_11T,new T5(0,_124,new T1(2,_124),0,1,32759));});}else{return new T2(1,new T4(0,_11Y,_11Z,_120,_123),_11U);}}else{var _=writeOffAddr("w8",1,plusAddr(_11Y,_120+_121|0),0,4);return new F(function(){return A1(_11T,new T5(0,_11Y,_11Z,_120,_121+1|0,_122-1|0));});}};};return new T2(0,new T(function(){return E(E(_11P).a);}),_11R);case 5:return new T2(0,_0,_Zu);case 6:return new T2(0,_0,_ZI);case 7:return new T2(0,_0,_ZW);case 8:return new T2(0,_0,_10a);case 9:return new T2(0,_0,_10o);default:return new T2(0,_0,_10C);}},_125=function(_126){var _127=B(_10G(_126));return new T2(0,_127.a,E(_127.b));},_Za=new T(function(){return new T2(0,_125,_Yc);}),_128=function(_129){var _12a=E(_129),_12b=B(_hF(_Za,_eW,_12a.a,_12a.b,_12a.c,_12a.d,_12a.e,_12a.f));return new T2(0,_12b.a,_12b.b);},_12c=new T(function(){return B(unCStr("MArray: undefined array element"));}),_12d=new T(function(){return B(err(_12c));}),_12e=new T(function(){return B(unCStr("Negative range size"));}),_12f=new T(function(){return B(err(_12e));}),_12g=function(_12h,_12i,_12j,_12k,_12l,_12m){var _12n=B(_XF(_9u,_O8,_12h,_12i,_12j,_12k,_12l,_12m)),_12o=E(_12n.b),_12p=B(_XF(_9u,_dc,_12o.a,_12o.b,_12o.c,_12o.d,_12o.e,_12o.f)),_12q=E(_12p.b),_12r=B(_93(_12q.a,_12q.b,_12q.c,_12q.d,_12q.e,_12q.f)),_12s=E(_12r.a)&4294967295,_12t=B(_hp(_12s,_128,_12r.b)),_12u=E(_12t.b),_12v=B(_hF(_l0,_eW,_12u.a,_12u.b,_12u.c,_12u.d,_12u.e,_12u.f)),_12w=E(_12v.b),_12x=B(_Ue(_Tf,_12w.a,_12w.b,_12w.c,_12w.d,_12w.e,_12w.f)),_12y=E(_12x.b),_12z=B(_Ue(_Tf,_12y.a,_12y.b,_12y.c,_12y.d,_12y.e,_12y.f)),_12A=E(_12z.b),_12B=B(_Ue(_T6,_12A.a,_12A.b,_12A.c,_12A.d,_12A.e,_12A.f)),_12C=E(_12B.b),_12D=B(_XF(_9u,_iG,_12C.a,_12C.b,_12C.c,_12C.d,_12C.e,_12C.f)),_12E=E(_12D.b),_12F=B(_93(_12E.a,_12E.b,_12E.c,_12E.d,_12E.e,_12E.f)),_12G=new T(function(){var _12H=new T(function(){var _12I=function(_){var _12J=_12s-1|0,_12K=function(_12L){if(_12L>=0){var _12M=newArr(_12L,_12d),_12N=_12M,_12O=function(_12P){var _12Q=function(_12R,_12S,_){while(1){if(_12R!=_12P){var _12T=E(_12S);if(!_12T._){return _0;}else{var _=_12N[_12R]=_12T.a,_12U=_12R+1|0;_12R=_12U;_12S=_12T.b;continue;}}else{return _0;}}},_12V=B(_12Q(0,_12t.a,_));return new T4(0,E(_eZ),E(_12J),_12L,_12N);};if(0>_12J){return new F(function(){return _12O(0);});}else{var _12W=_12J+1|0;if(_12W>=0){return new F(function(){return _12O(_12W);});}else{return E(_eY);}}}else{return E(_12f);}};if(0>_12J){return new F(function(){return _12K(0);});}else{return new F(function(){return _12K(_12J+1|0);});}};return B(_df(_12I));});return {_:0,a:_12n.a,b:_12p.a,c:_12v.a,d:_12x.a,e:_12z.a,f:_12H,g:_12B.a,h:_XT,i:_UB,j:_12D.a,k:_XT,l:E(_12F.a)&4294967295};});return new T2(0,_12G,_12F.b);},_12X=function(_12Y){var _12Z=E(_12Y),_130=B(_12g(_12Z.a,_12Z.b,_12Z.c,_12Z.d,_12Z.e,_12Z.f));return new T2(0,_130.a,_130.b);},_131=function(_132){var _133=E(_132);switch(_133._){case 0:return B(_131(_133.c))+B(_131(_133.d))|0;case 1:return 1;default:return 0;}},_134=function(_135,_136){var _137=new T(function(){var _138=function(_139,_13a){while(1){var _13b=B((function(_13c,_13d){var _13e=E(_13d);switch(_13e._){case 0:_139=new T(function(){return B(_138(_13c,_13e.d));});_13a=_13e.c;return __continue;case 1:var _13f=new T(function(){return B(A2(_cQ,_135,_13e.b));}),_13g=new T(function(){return E(B(_3M(_13e.a>>>0)).b);}),_13h=function(_13i){var _13j=new T(function(){return B(A1(E(_13f).b,new T(function(){return B(A1(E(_13c).b,_13i));})));});return new F(function(){return A1(_13g,_13j);});};return new T2(0,new T(function(){return E(E(_13c).a);}),E(_13h));default:return E(_13c);}})(_139,_13a));if(_13b!=__continue){return _13b;}}},_13k=E(_136);if(!_13k._){var _13l=_13k.c,_13m=_13k.d;if(_13k.b>=0){return B(_138(new T(function(){return B(_138(_SI,_13m));}),_13l));}else{return B(_138(new T(function(){return B(_138(_SI,_13l));}),_13m));}}else{return B(_138(_SI,_13k));}}),_13n=new T(function(){return E(B(_3M(B(_131(_136))>>>0)).b);}),_13o=function(_13p){return new F(function(){return A1(_13n,new T(function(){return B(A1(E(_137).b,_13p));}));});};return new T2(0,new T(function(){return E(E(_137).a);}),_13o);},_13q=function(_13r,_13s,_13t){var _13u=new T(function(){var _13v=function(_13w,_13x){while(1){var _13y=B((function(_13z,_13A){var _13B=E(_13A);if(!_13B._){var _13C=new T(function(){return B(_13v(_13z,_13B.e));}),_13D=new T(function(){return B(A2(_cQ,_13s,_13B.c));}),_13E=new T(function(){return E(B(A2(_cQ,_13r,_13B.b)).b);}),_13F=function(_13G){var _13H=new T(function(){return B(A1(E(_13D).b,new T(function(){return B(A1(E(_13C).b,_13G));})));});return new F(function(){return A1(_13E,_13H);});};_13w=new T2(0,new T(function(){return E(E(_13C).a);}),E(_13F));_13x=_13B.d;return __continue;}else{return E(_13z);}})(_13w,_13x));if(_13y!=__continue){return _13y;}}};return B(_13v(_SI,_13t));}),_13I=new T(function(){var _13J=E(_13t);if(!_13J._){return E(B(_3M(_13J.a>>>0)).b);}else{return E(B(_3M(0)).b);}}),_13K=function(_13L){return new F(function(){return A1(_13I,new T(function(){return B(A1(E(_13u).b,_13L));}));});};return new T2(0,new T(function(){return E(E(_13u).a);}),_13K);},_13M=function(_13N){var _13O=new T(function(){var _13P=B(_3M(E(_13N).l>>>0));return new T2(0,_13P.a,E(_13P.b));}),_13Q=new T(function(){return E(B(_13q(_9u,_iG,new T(function(){return E(E(_13N).j);}))).b);}),_13R=new T(function(){return E(B(_134(_T6,new T(function(){return E(E(_13N).g);}))).b);}),_13S=new T(function(){return E(B(_134(_Tf,new T(function(){return E(E(_13N).e);}))).b);}),_13T=new T(function(){return E(B(_134(_Tf,new T(function(){return E(E(_13N).d);}))).b);}),_13U=new T(function(){return E(E(_13N).c);}),_13V=new T(function(){var _13W=E(_13U),_13X=_13W.c-1|0;if(0<=_13X){var _13Y=function(_13Z){var _140=new T(function(){if(_13Z!=_13X){var _141=B(_13Y(_13Z+1|0));return new T2(0,_141.a,E(_141.b));}else{return E(_ic);}}),_142=new T(function(){var _143=E(_13W.d[_13Z]);return E(B(_kB(_143.a,E(_143.b),E(_143.c),_143.d,_143.e)).b);}),_144=function(_145){return new F(function(){return A1(_142,new T(function(){return B(A1(E(_140).b,_145));}));});};return new T2(0,new T(function(){return E(E(_140).a);}),_144);},_146=B(_13Y(0));return new T2(0,_146.a,E(_146.b));}else{return E(_ic);}}),_147=new T(function(){var _148=E(_13U),_149=E(_148.a),_14a=E(_148.b);if(_149>_14a){return E(B(_3M(0)).b);}else{return E(B(_3M(((_14a-_149|0)+1|0)>>>0)).b);}}),_14b=new T(function(){return E(E(_13N).f);}),_14c=new T(function(){var _14d=E(_14b),_14e=_14d.c-1|0;if(0<=_14e){var _14f=function(_14g){var _14h=new T(function(){if(_14g!=_14e){var _14i=B(_14f(_14g+1|0));return new T2(0,_14i.a,E(_14i.b));}else{return E(_ic);}}),_14j=new T(function(){return E(_14d.d[_14g]);}),_14k=new T(function(){var _14l=E(_14j),_14m=_14l.c-1|0;if(0<=_14m){var _14n=function(_14o){var _14p=new T(function(){if(_14o!=_14m){var _14q=B(_14n(_14o+1|0));return new T2(0,_14q.a,E(_14q.b));}else{return E(_ic);}}),_14r=new T(function(){return E(B(_10G(_14l.d[_14o])).b);}),_14s=function(_14t){return new F(function(){return A1(_14r,new T(function(){return B(A1(E(_14p).b,_14t));}));});};return new T2(0,new T(function(){return E(E(_14p).a);}),_14s);},_14u=B(_14n(0));return new T2(0,_14u.a,E(_14u.b));}else{return E(_ic);}}),_14v=new T(function(){var _14w=E(_14j),_14x=E(_14w.a),_14y=E(_14w.b);if(_14x>_14y){return E(B(_3M(0)).b);}else{return E(B(_3M(((_14y-_14x|0)+1|0)>>>0)).b);}}),_14z=function(_14A){var _14B=new T(function(){return B(A1(E(_14k).b,new T(function(){return B(A1(E(_14h).b,_14A));})));});return new F(function(){return A1(_14v,_14B);});};return new T2(0,new T(function(){return E(E(_14h).a);}),_14z);},_14C=B(_14f(0));return new T2(0,_14C.a,E(_14C.b));}else{return E(_ic);}}),_14D=new T(function(){var _14E=E(_14b),_14F=E(_14E.a),_14G=E(_14E.b);if(_14F>_14G){return E(B(_3M(0)).b);}else{return E(B(_3M(((_14G-_14F|0)+1|0)>>>0)).b);}}),_14H=new T(function(){return E(B(_13q(_9u,_dc,new T(function(){return E(E(_13N).b);}))).b);}),_14I=new T(function(){return E(B(_13q(_9u,_O8,new T(function(){return E(E(_13N).a);}))).b);}),_14J=function(_14K){var _14L=new T(function(){var _14M=new T(function(){var _14N=new T(function(){var _14O=new T(function(){var _14P=new T(function(){var _14Q=new T(function(){var _14R=new T(function(){var _14S=new T(function(){var _14T=new T(function(){return B(A1(_13Q,new T(function(){return B(A1(E(_13O).b,_14K));})));});return B(A1(_13R,_14T));});return B(A1(_13S,_14S));});return B(A1(_13T,_14R));});return B(A1(E(_13V).b,_14Q));});return B(A1(_147,_14P));});return B(A1(E(_14c).b,_14O));});return B(A1(_14D,_14N));});return B(A1(_14H,_14M));});return new F(function(){return A1(_14I,_14L);});};return new T2(0,new T(function(){return E(E(_13O).a);}),_14J);},_14U=function(_14V){var _14W=B(_13M(_14V));return new T2(0,_14W.a,E(_14W.b));},_14X=new T2(0,_14U,_12X),_14Y=function(_14Z){var _150=E(_14Z);return new T4(0,_150.a,_150.b,new T(function(){var _151=E(_150.c);if(!_151._){return __Z;}else{return new T1(1,new T2(0,_151.a,_M));}}),_150.d);},_152=function(_153){var _154=E(_153),_155=B(_It(8,_Lb,_154.a,_154.b,_154.c,_154.d,_154.e,_154.f)),_156=E(_155.b),_157=B(_9h(_156.a,_156.b,_156.c,_156.d,_156.e,_156.f));return new T2(0,new T2(0,_155.a,_157.a),_157.b);},_158=0,_159=1,_15a=function(_15b){return new F(function(){return _l2(_l1,_15b);});},_15c=function(_15d){return new F(function(){return _l2(_l1,_15d);});},_15e=function(_15f,_15g,_15h,_15i,_15j,_15k){var _15l=B(_8B(1,_15f,_15g,_15h,_15i,_15j,_15k)),_15m=_15l.b,_15n=E(_15l.a),_15o=_15n.b,_15p=readOffAddr("w8",1,plusAddr(_15n.a,_15n.c),0);switch(E(_15p)){case 0:var _15q=E(_15m),_15r=B(_8B(1,_15q.a,_15q.b,_15q.c,_15q.d,_15q.e,_15q.f)),_15s=_15r.b,_15t=E(_15r.a),_15u=_15t.b,_15v=readOffAddr("w8",1,plusAddr(_15t.a,_15t.c),0);switch(E(_15v)){case 0:var _15w=E(_15s),_15x=B(_9h(_15w.a,_15w.b,_15w.c,_15w.d,_15w.e,_15w.f)),_15y=E(_15x.b),_15z=B(_15e(_15y.a,_15y.b,_15y.c,_15y.d,_15y.e,_15y.f));return new T2(0,new T3(0,_158,_15x.a,_15z.a),_15z.b);case 1:var _15A=E(_15s),_15B=B(_9h(_15A.a,_15A.b,_15A.c,_15A.d,_15A.e,_15A.f)),_15C=E(_15B.b),_15D=B(_15e(_15C.a,_15C.b,_15C.c,_15C.d,_15C.e,_15C.f));return new T2(0,new T3(0,_159,_15B.a,_15D.a),_15D.b);default:return new F(function(){return _15c(E(_15s).f);});}break;case 1:var _15E=E(_15m),_15F=B(_15e(_15E.a,_15E.b,_15E.c,_15E.d,_15E.e,_15E.f)),_15G=E(_15F.b),_15H=B(_15e(_15G.a,_15G.b,_15G.c,_15G.d,_15G.e,_15G.f));return new T2(0,new T2(1,_15F.a,_15H.a),_15H.b);case 2:var _15I=E(_15m),_15J=B(_Le(_15I.a,_15I.b,_15I.c,_15I.d,_15I.e,_15I.f));return new T2(0,new T1(2,_15J.a),_15J.b);case 3:var _15K=E(_15m),_15L=B(_93(_15K.a,_15K.b,_15K.c,_15K.d,_15K.e,_15K.f));return new T2(0,new T(function(){return new T1(3,E(_15L.a)&4294967295);}),_15L.b);case 4:var _15M=E(_15m),_15N=B(_9h(_15M.a,_15M.b,_15M.c,_15M.d,_15M.e,_15M.f));return new T2(0,new T1(4,_15N.a),_15N.b);case 5:var _15O=E(_15m),_15P=B(_93(_15O.a,_15O.b,_15O.c,_15O.d,_15O.e,_15O.f));return new T2(0,new T(function(){return new T1(5,E(_15P.a)&4294967295);}),_15P.b);case 6:var _15Q=E(_15m),_15R=B(_15e(_15Q.a,_15Q.b,_15Q.c,_15Q.d,_15Q.e,_15Q.f)),_15S=E(_15R.b),_15T=B(_15U(_15S.a,_15S.b,_15S.c,_15S.d,_15S.e,_15S.f));return new T2(0,new T2(6,_15R.a,_15T.a),_15T.b);case 7:var _15V=E(_15m),_15W=B(_15e(_15V.a,_15V.b,_15V.c,_15V.d,_15V.e,_15V.f));return new T2(0,new T1(7,_15W.a),_15W.b);default:return new F(function(){return _15a(E(_15m).f);});}},_15X=function(_15Y){var _15Z=E(_15Y),_160=B(_15e(_15Z.a,_15Z.b,_15Z.c,_15Z.d,_15Z.e,_15Z.f));return new T2(0,_160.a,_160.b);},_15U=function(_161,_162,_163,_164,_165,_166){var _167=B(_93(_161,_162,_163,_164,_165,_166)),_168=B(_aA(E(_167.a)&4294967295,_169,_167.b)),_16a=E(_168.b),_16b=B(_9h(_16a.a,_16a.b,_16a.c,_16a.d,_16a.e,_16a.f)),_16c=E(_16b.b),_16d=B(_93(_16c.a,_16c.b,_16c.c,_16c.d,_16c.e,_16c.f)),_16e=B(_aA(E(_16d.a)&4294967295,_15X,_16d.b));return new T2(0,new T3(0,_168.a,_16b.a,_16e.a),_16e.b);},_16f=function(_16g,_16h){var _16i=E(_16h),_16j=B(_9h(_16i.a,_16i.b,_16i.c,_16i.d,_16i.e,_16i.f)),_16k=E(_16j.b),_16l=B(_15U(_16k.a,_16k.b,_16k.c,_16k.d,_16k.e,_16k.f));return new T2(0,new T3(0,_16g,_16j.a,_16l.a),_16l.b);},_169=function(_16m){var _16n=E(_16m),_16o=B(_8B(1,_16n.a,_16n.b,_16n.c,_16n.d,_16n.e,_16n.f)),_16p=_16o.b,_16q=E(_16o.a),_16r=_16q.b,_16s=readOffAddr("w8",1,plusAddr(_16q.a,_16q.c),0);switch(E(_16s)){case 0:return new F(function(){return _16f(_158,_16p);});break;case 1:return new F(function(){return _16f(_159,_16p);});break;default:return new F(function(){return _15c(E(_16p).f);});}},_16t=function(_16u,_16v,_16w,_16x,_16y,_16z){var _16A=B(_93(_16u,_16v,_16w,_16x,_16y,_16z)),_16B=B(_aA(E(_16A.a)&4294967295,_169,_16A.b)),_16C=E(_16B.b),_16D=B(_93(_16C.a,_16C.b,_16C.c,_16C.d,_16C.e,_16C.f)),_16E=B(_aA(E(_16D.a)&4294967295,_152,_16D.b)),_16F=E(_16E.b),_16G=B(_It(8,_Lb,_16F.a,_16F.b,_16F.c,_16F.d,_16F.e,_16F.f));return new T2(0,new T3(0,_16B.a,_16E.a,_16G.a),_16G.b);},_16H=function(_16I){var _16J=E(_16I),_16K=B(_16t(_16J.a,_16J.b,_16J.c,_16J.d,_16J.e,_16J.f));return new T2(0,_16K.a,_16K.b);},_16L=function(_16M,_16N,_16O,_16P,_16Q,_16R){var _16S=B(_It(8,_Lb,_16M,_16N,_16O,_16P,_16Q,_16R)),_16T=E(_16S.b),_16U=B(_9h(_16T.a,_16T.b,_16T.c,_16T.d,_16T.e,_16T.f));return new T2(0,new T2(0,_16S.a,_16U.a),_16U.b);},_16V=function(_16W){var _16X=E(_16W),_16Y=B(_16L(_16X.a,_16X.b,_16X.c,_16X.d,_16X.e,_16X.f));return new T2(0,_16Y.a,_16Y.b);},_16Z=function(_170,_171){var _172=new T(function(){return E(B(_My(_Nf,_2I,_170)).b);}),_173=new T(function(){var _174=B(_6x(_171));return new T2(0,_174.a,E(_174.b));}),_175=function(_176){return new F(function(){return A1(_172,new T(function(){return B(A1(E(_173).b,_176));}));});};return new T2(0,new T(function(){return E(E(_173).a);}),_175);},_177=function(_178){var _179=E(_178),_17a=B(_16Z(_179.a,_179.b));return new T2(0,_17a.a,E(_17a.b));},_17b=new T2(0,_177,_16V),_17c=function(_17d,_17e){var _17f=E(_17e),_17g=B(_9h(_17f.a,_17f.b,_17f.c,_17f.d,_17f.e,_17f.f)),_17h=E(_17g.b),_17i=B(_15U(_17h.a,_17h.b,_17h.c,_17h.d,_17h.e,_17h.f));return new T2(0,new T3(0,_17d,_17g.a,_17i.a),_17i.b);},_17j=function(_17k,_17l,_17m,_17n,_17o,_17p){var _17q=B(_8B(1,_17k,_17l,_17m,_17n,_17o,_17p)),_17r=_17q.b,_17s=E(_17q.a),_17t=_17s.b,_17u=readOffAddr("w8",1,plusAddr(_17s.a,_17s.c),0);switch(E(_17u)){case 0:return new F(function(){return _17c(_158,_17r);});break;case 1:return new F(function(){return _17c(_159,_17r);});break;default:return new F(function(){return _15c(E(_17r).f);});}},_17v=function(_17w){var _17x=E(_17w),_17y=B(_17j(_17x.a,_17x.b,_17x.c,_17x.d,_17x.e,_17x.f));return new T2(0,_17y.a,_17y.b);},_17z=function(_17A,_17B,_17C,_17D,_17E,_17F){if(1>_17F){var _17G=E(_17E);if(!_17G){var _17H=newByteArr(32760),_=writeOffAddr("w8",1,_17H,0,1);return new F(function(){return A1(_17A,new T5(0,_17H,new T1(2,_17H),0,1,32759));});}else{return new T2(1,new T4(0,_17B,_17C,_17D,_17G),new T(function(){var _17I=newByteArr(32760),_=writeOffAddr("w8",1,_17I,0,1);return B(A1(_17A,new T5(0,_17I,new T1(2,_17I),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_17B,_17D+_17E|0),0,1);return new F(function(){return A1(_17A,new T5(0,_17B,_17C,_17D,_17E+1|0,_17F-1|0));});}},_17J=function(_17K,_17L,_17M,_17N,_17O,_17P){if(1>_17P){var _17Q=E(_17O);if(!_17Q){var _17R=newByteArr(32760),_=writeOffAddr("w8",1,_17R,0,0);return new F(function(){return A1(_17K,new T5(0,_17R,new T1(2,_17R),0,1,32759));});}else{return new T2(1,new T4(0,_17L,_17M,_17N,_17Q),new T(function(){var _17S=newByteArr(32760),_=writeOffAddr("w8",1,_17S,0,0);return B(A1(_17K,new T5(0,_17S,new T1(2,_17S),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_17L,_17N+_17O|0),0,0);return new F(function(){return A1(_17K,new T5(0,_17L,_17M,_17N,_17O+1|0,_17P-1|0));});}},_17T=function(_17U){var _17V=E(_17U);switch(_17V._){case 0:var _17W=new T(function(){var _17X=B(_6x(_17V.b));return new T2(0,_17X.a,E(_17X.b));}),_17Y=new T(function(){var _17Z=B(_17T(_17V.c));return new T2(0,_17Z.a,E(_17Z.b));}),_180=function(_181){var _182=new T(function(){if(!E(_17V.a)){var _183=new T(function(){return B(A1(E(_17W).b,new T(function(){return B(A1(E(_17Y).b,_181));})));});return function(_184){var _185=E(_184);return new F(function(){return _17J(_183,_185.a,_185.b,_185.c,_185.d,_185.e);});};}else{var _186=new T(function(){return B(A1(E(_17W).b,new T(function(){return B(A1(E(_17Y).b,_181));})));});return function(_187){var _188=E(_187);return new F(function(){return _17z(_186,_188.a,_188.b,_188.c,_188.d,_188.e);});};}}),_189=new T(function(){var _18a=newByteArr(32760),_=writeOffAddr("w8",1,_18a,0,0);return B(A1(_182,new T5(0,_18a,new T1(2,_18a),0,1,32759)));});return function(_18b){var _18c=E(_18b),_18d=_18c.a,_18e=_18c.b,_18f=_18c.c,_18g=_18c.d,_18h=_18c.e;if(1>_18h){var _18i=E(_18g);if(!_18i){var _18j=newByteArr(32760),_=writeOffAddr("w8",1,_18j,0,0);return new F(function(){return A1(_182,new T5(0,_18j,new T1(2,_18j),0,1,32759));});}else{return new T2(1,new T4(0,_18d,_18e,_18f,_18i),_189);}}else{var _=writeOffAddr("w8",1,plusAddr(_18d,_18f+_18g|0),0,0);return new F(function(){return A1(_182,new T5(0,_18d,_18e,_18f,_18g+1|0,_18h-1|0));});}};};return new T2(0,new T(function(){return E(E(_17Y).a);}),_180);case 1:var _18k=new T(function(){return E(B(_17T(_17V.a)).b);}),_18l=new T(function(){var _18m=B(_17T(_17V.b));return new T2(0,_18m.a,E(_18m.b));}),_18n=function(_18o){var _18p=new T(function(){return B(A1(_18k,new T(function(){return B(A1(E(_18l).b,_18o));})));}),_18q=new T(function(){var _18r=newByteArr(32760),_=writeOffAddr("w8",1,_18r,0,1);return B(A1(_18p,new T5(0,_18r,new T1(2,_18r),0,1,32759)));});return function(_18s){var _18t=E(_18s),_18u=_18t.a,_18v=_18t.b,_18w=_18t.c,_18x=_18t.d,_18y=_18t.e;if(1>_18y){var _18z=E(_18x);if(!_18z){var _18A=newByteArr(32760),_=writeOffAddr("w8",1,_18A,0,1);return new F(function(){return A1(_18p,new T5(0,_18A,new T1(2,_18A),0,1,32759));});}else{return new T2(1,new T4(0,_18u,_18v,_18w,_18z),_18q);}}else{var _=writeOffAddr("w8",1,plusAddr(_18u,_18w+_18x|0),0,1);return new F(function(){return A1(_18p,new T5(0,_18u,_18v,_18w,_18x+1|0,_18y-1|0));});}};};return new T2(0,new T(function(){return E(E(_18l).a);}),_18n);case 2:var _18B=new T(function(){var _18C=B(_Ng(_17V.a));return new T2(0,_18C.a,E(_18C.b));}),_18D=function(_18E){var _18F=new T(function(){return B(A1(E(_18B).b,_18E));}),_18G=new T(function(){var _18H=newByteArr(32760),_=writeOffAddr("w8",1,_18H,0,2);return B(A1(_18F,new T5(0,_18H,new T1(2,_18H),0,1,32759)));});return function(_18I){var _18J=E(_18I),_18K=_18J.a,_18L=_18J.b,_18M=_18J.c,_18N=_18J.d,_18O=_18J.e;if(1>_18O){var _18P=E(_18N);if(!_18P){var _18Q=newByteArr(32760),_=writeOffAddr("w8",1,_18Q,0,2);return new F(function(){return A1(_18F,new T5(0,_18Q,new T1(2,_18Q),0,1,32759));});}else{return new T2(1,new T4(0,_18K,_18L,_18M,_18P),_18G);}}else{var _=writeOffAddr("w8",1,plusAddr(_18K,_18M+_18N|0),0,2);return new F(function(){return A1(_18F,new T5(0,_18K,_18L,_18M,_18N+1|0,_18O-1|0));});}};};return new T2(0,new T(function(){return E(E(_18B).a);}),_18D);case 3:var _18R=new T(function(){var _18S=B(_3M(_17V.a>>>0));return new T2(0,_18S.a,E(_18S.b));}),_18T=function(_18U){var _18V=new T(function(){return B(A1(E(_18R).b,_18U));}),_18W=new T(function(){var _18X=newByteArr(32760),_=writeOffAddr("w8",1,_18X,0,3);return B(A1(_18V,new T5(0,_18X,new T1(2,_18X),0,1,32759)));});return function(_18Y){var _18Z=E(_18Y),_190=_18Z.a,_191=_18Z.b,_192=_18Z.c,_193=_18Z.d,_194=_18Z.e;if(1>_194){var _195=E(_193);if(!_195){var _196=newByteArr(32760),_=writeOffAddr("w8",1,_196,0,3);return new F(function(){return A1(_18V,new T5(0,_196,new T1(2,_196),0,1,32759));});}else{return new T2(1,new T4(0,_190,_191,_192,_195),_18W);}}else{var _=writeOffAddr("w8",1,plusAddr(_190,_192+_193|0),0,3);return new F(function(){return A1(_18V,new T5(0,_190,_191,_192,_193+1|0,_194-1|0));});}};};return new T2(0,new T(function(){return E(E(_18R).a);}),_18T);case 4:var _197=new T(function(){var _198=B(_6x(_17V.a));return new T2(0,_198.a,E(_198.b));}),_199=function(_19a){var _19b=new T(function(){return B(A1(E(_197).b,_19a));}),_19c=new T(function(){var _19d=newByteArr(32760),_=writeOffAddr("w8",1,_19d,0,4);return B(A1(_19b,new T5(0,_19d,new T1(2,_19d),0,1,32759)));});return function(_19e){var _19f=E(_19e),_19g=_19f.a,_19h=_19f.b,_19i=_19f.c,_19j=_19f.d,_19k=_19f.e;if(1>_19k){var _19l=E(_19j);if(!_19l){var _19m=newByteArr(32760),_=writeOffAddr("w8",1,_19m,0,4);return new F(function(){return A1(_19b,new T5(0,_19m,new T1(2,_19m),0,1,32759));});}else{return new T2(1,new T4(0,_19g,_19h,_19i,_19l),_19c);}}else{var _=writeOffAddr("w8",1,plusAddr(_19g,_19i+_19j|0),0,4);return new F(function(){return A1(_19b,new T5(0,_19g,_19h,_19i,_19j+1|0,_19k-1|0));});}};};return new T2(0,new T(function(){return E(E(_197).a);}),_199);case 5:var _19n=new T(function(){var _19o=B(_3M(_17V.a>>>0));return new T2(0,_19o.a,E(_19o.b));}),_19p=function(_19q){var _19r=new T(function(){return B(A1(E(_19n).b,_19q));}),_19s=new T(function(){var _19t=newByteArr(32760),_=writeOffAddr("w8",1,_19t,0,5);return B(A1(_19r,new T5(0,_19t,new T1(2,_19t),0,1,32759)));});return function(_19u){var _19v=E(_19u),_19w=_19v.a,_19x=_19v.b,_19y=_19v.c,_19z=_19v.d,_19A=_19v.e;if(1>_19A){var _19B=E(_19z);if(!_19B){var _19C=newByteArr(32760),_=writeOffAddr("w8",1,_19C,0,5);return new F(function(){return A1(_19r,new T5(0,_19C,new T1(2,_19C),0,1,32759));});}else{return new T2(1,new T4(0,_19w,_19x,_19y,_19B),_19s);}}else{var _=writeOffAddr("w8",1,plusAddr(_19w,_19y+_19z|0),0,5);return new F(function(){return A1(_19r,new T5(0,_19w,_19x,_19y,_19z+1|0,_19A-1|0));});}};};return new T2(0,new T(function(){return E(E(_19n).a);}),_19p);case 6:var _19D=new T(function(){return E(B(_17T(_17V.a)).b);}),_19E=new T(function(){var _19F=E(_17V.b),_19G=B(_19H(_19F.a,_19F.b,_19F.c));return new T2(0,_19G.a,E(_19G.b));}),_19I=function(_19J){var _19K=new T(function(){return B(A1(_19D,new T(function(){return B(A1(E(_19E).b,_19J));})));}),_19L=new T(function(){var _19M=newByteArr(32760),_=writeOffAddr("w8",1,_19M,0,6);return B(A1(_19K,new T5(0,_19M,new T1(2,_19M),0,1,32759)));});return function(_19N){var _19O=E(_19N),_19P=_19O.a,_19Q=_19O.b,_19R=_19O.c,_19S=_19O.d,_19T=_19O.e;if(1>_19T){var _19U=E(_19S);if(!_19U){var _19V=newByteArr(32760),_=writeOffAddr("w8",1,_19V,0,6);return new F(function(){return A1(_19K,new T5(0,_19V,new T1(2,_19V),0,1,32759));});}else{return new T2(1,new T4(0,_19P,_19Q,_19R,_19U),_19L);}}else{var _=writeOffAddr("w8",1,plusAddr(_19P,_19R+_19S|0),0,6);return new F(function(){return A1(_19K,new T5(0,_19P,_19Q,_19R,_19S+1|0,_19T-1|0));});}};};return new T2(0,new T(function(){return E(E(_19E).a);}),_19I);default:var _19W=new T(function(){var _19X=B(_17T(_17V.a));return new T2(0,_19X.a,E(_19X.b));}),_19Y=function(_19Z){var _1a0=new T(function(){return B(A1(E(_19W).b,_19Z));}),_1a1=new T(function(){var _1a2=newByteArr(32760),_=writeOffAddr("w8",1,_1a2,0,7);return B(A1(_1a0,new T5(0,_1a2,new T1(2,_1a2),0,1,32759)));});return function(_1a3){var _1a4=E(_1a3),_1a5=_1a4.a,_1a6=_1a4.b,_1a7=_1a4.c,_1a8=_1a4.d,_1a9=_1a4.e;if(1>_1a9){var _1aa=E(_1a8);if(!_1aa){var _1ab=newByteArr(32760),_=writeOffAddr("w8",1,_1ab,0,7);return new F(function(){return A1(_1a0,new T5(0,_1ab,new T1(2,_1ab),0,1,32759));});}else{return new T2(1,new T4(0,_1a5,_1a6,_1a7,_1aa),_1a1);}}else{var _=writeOffAddr("w8",1,plusAddr(_1a5,_1a7+_1a8|0),0,7);return new F(function(){return A1(_1a0,new T5(0,_1a5,_1a6,_1a7,_1a8+1|0,_1a9-1|0));});}};};return new T2(0,new T(function(){return E(E(_19W).a);}),_19Y);}},_1ac=function(_1ad){var _1ae=B(_17T(_1ad));return new T2(0,_1ae.a,E(_1ae.b));},_1af=new T(function(){return new T2(0,_1ac,_15X);}),_19H=function(_1ag,_1ah,_1ai){var _1aj=new T(function(){return E(B(_cS(_1ak,_1ag)).b);}),_1al=new T(function(){var _1am=B(_6x(_1ah));return new T2(0,_1am.a,E(_1am.b));}),_1an=new T(function(){var _1ao=B(_cS(_1af,_1ai));return new T2(0,_1ao.a,E(_1ao.b));}),_1ap=function(_1aq){var _1ar=new T(function(){return B(A1(E(_1al).b,new T(function(){return B(A1(E(_1an).b,_1aq));})));});return new F(function(){return A1(_1aj,_1ar);});};return new T2(0,new T(function(){return E(E(_1an).a);}),_1ap);},_1as=function(_1at,_1au,_1av){var _1aw=new T(function(){var _1ax=B(_6x(_1au));return new T2(0,_1ax.a,E(_1ax.b));}),_1ay=new T(function(){var _1az=E(_1av),_1aA=B(_19H(_1az.a,_1az.b,_1az.c));return new T2(0,_1aA.a,E(_1aA.b));}),_1aB=function(_1aC){if(!E(_1at)){var _1aD=new T(function(){return B(A1(E(_1aw).b,new T(function(){return B(A1(E(_1ay).b,_1aC));})));});return function(_1aE){var _1aF=E(_1aE);return new F(function(){return _17J(_1aD,_1aF.a,_1aF.b,_1aF.c,_1aF.d,_1aF.e);});};}else{var _1aG=new T(function(){return B(A1(E(_1aw).b,new T(function(){return B(A1(E(_1ay).b,_1aC));})));});return function(_1aH){var _1aI=E(_1aH);return new F(function(){return _17z(_1aG,_1aI.a,_1aI.b,_1aI.c,_1aI.d,_1aI.e);});};}};return new T2(0,new T(function(){return E(E(_1ay).a);}),_1aB);},_1aJ=function(_1aK){var _1aL=E(_1aK),_1aM=B(_1as(_1aL.a,_1aL.b,_1aL.c));return new T2(0,_1aM.a,E(_1aM.b));},_1ak=new T(function(){return new T2(0,_1aJ,_17v);}),_1aN=function(_1aO,_1aP,_1aQ){var _1aR=new T(function(){return E(B(_cS(_1ak,_1aO)).b);}),_1aS=new T(function(){var _1aT=B(_cS(_17b,_1aP));return new T2(0,_1aT.a,E(_1aT.b));}),_1aU=new T(function(){var _1aV=B(_My(_Nf,_2I,_1aQ));return new T2(0,_1aV.a,E(_1aV.b));}),_1aW=function(_1aX){var _1aY=new T(function(){return B(A1(E(_1aS).b,new T(function(){return B(A1(E(_1aU).b,_1aX));})));});return new F(function(){return A1(_1aR,_1aY);});};return new T2(0,new T(function(){return E(E(_1aU).a);}),_1aW);},_1aZ=function(_1b0){var _1b1=E(_1b0),_1b2=B(_1aN(_1b1.a,_1b1.b,_1b1.c));return new T2(0,_1b2.a,E(_1b2.b));},_1b3=new T2(0,_1aZ,_16H),_1b4=new T0(4),_1b5=function(_1b6){return new F(function(){return _l2(_l1,_1b6);});},_1b7=function(_1b8,_1b9,_1ba,_1bb,_1bc,_1bd){var _1be=B(_8B(1,_1b8,_1b9,_1ba,_1bb,_1bc,_1bd)),_1bf=_1be.b,_1bg=E(_1be.a),_1bh=_1bg.b,_1bi=readOffAddr("w8",1,plusAddr(_1bg.a,_1bg.c),0);switch(E(_1bi)){case 0:var _1bj=E(_1bf),_1bk=B(_9h(_1bj.a,_1bj.b,_1bj.c,_1bj.d,_1bj.e,_1bj.f)),_1bl=E(_1bk.b),_1bm=B(_93(_1bl.a,_1bl.b,_1bl.c,_1bl.d,_1bl.e,_1bl.f)),_1bn=B(_aA(E(_1bm.a)&4294967295,_1bo,_1bm.b));return new T2(0,new T2(0,_1bk.a,_1bn.a),_1bn.b);case 1:var _1bp=E(_1bf),_1bq=B(_9h(_1bp.a,_1bp.b,_1bp.c,_1bp.d,_1bp.e,_1bp.f));return new T2(0,new T1(2,_1bq.a),_1bq.b);case 2:var _1br=E(_1bf),_1bs=B(_9h(_1br.a,_1br.b,_1br.c,_1br.d,_1br.e,_1br.f)),_1bt=E(_1bs.b),_1bu=B(_1b7(_1bt.a,_1bt.b,_1bt.c,_1bt.d,_1bt.e,_1bt.f));return new T2(0,new T2(3,_1bs.a,_1bu.a),_1bu.b);case 3:return new T2(0,_1b4,_1bf);case 4:var _1bv=E(_1bf),_1bw=B(_Le(_1bv.a,_1bv.b,_1bv.c,_1bv.d,_1bv.e,_1bv.f));return new T2(0,new T1(1,_1bw.a),_1bw.b);case 5:var _1bx=E(_1bf),_1by=B(_1b7(_1bx.a,_1bx.b,_1bx.c,_1bx.d,_1bx.e,_1bx.f));return new T2(0,new T1(5,_1by.a),_1by.b);case 6:var _1bz=E(_1bf),_1bA=B(_15e(_1bz.a,_1bz.b,_1bz.c,_1bz.d,_1bz.e,_1bz.f));return new T2(0,new T1(6,_1bA.a),_1bA.b);default:return new F(function(){return _1b5(E(_1bf).f);});}},_1bo=function(_1bB){var _1bC=E(_1bB),_1bD=B(_1b7(_1bC.a,_1bC.b,_1bC.c,_1bC.d,_1bC.e,_1bC.f));return new T2(0,_1bD.a,_1bD.b);},_1bE=function(_1bF,_1bG,_1bH,_1bI,_1bJ,_1bK){var _1bL=B(_93(_1bF,_1bG,_1bH,_1bI,_1bJ,_1bK)),_1bM=B(_aA(E(_1bL.a)&4294967295,_1bo,_1bL.b)),_1bN=E(_1bM.b),_1bO=B(_15e(_1bN.a,_1bN.b,_1bN.c,_1bN.d,_1bN.e,_1bN.f));return new T2(0,new T2(0,_1bM.a,_1bO.a),_1bO.b);},_1bP=function(_1bQ){var _1bR=E(_1bQ),_1bS=B(_1bE(_1bR.a,_1bR.b,_1bR.c,_1bR.d,_1bR.e,_1bR.f));return new T2(0,_1bS.a,_1bS.b);},_1bT=function(_1bU,_1bV,_1bW,_1bX,_1bY,_1bZ){var _1c0=B(_15U(_1bU,_1bV,_1bW,_1bX,_1bY,_1bZ)),_1c1=_1c0.a,_1c2=E(_1c0.b),_1c3=B(_93(_1c2.a,_1c2.b,_1c2.c,_1c2.d,_1c2.e,_1c2.f)),_1c4=_1c3.a,_1c5=E(_1c3.b),_1c6=B(_8B(1,_1c5.a,_1c5.b,_1c5.c,_1c5.d,_1c5.e,_1c5.f)),_1c7=_1c6.b,_1c8=E(_1c6.a),_1c9=_1c8.b,_1ca=readOffAddr("w8",1,plusAddr(_1c8.a,_1c8.c),0);if(!E(_1ca)){var _1cb=E(_1c7),_1cc=B(_It(8,_Lb,_1cb.a,_1cb.b,_1cb.c,_1cb.d,_1cb.e,_1cb.f));return new T2(0,new T4(0,_1c1,new T(function(){return E(_1c4)&4294967295;}),_2s,_1cc.a),_1cc.b);}else{var _1cd=E(_1c7),_1ce=B(_93(_1cd.a,_1cd.b,_1cd.c,_1cd.d,_1cd.e,_1cd.f)),_1cf=B(_aA(E(_1ce.a)&4294967295,_1bP,_1ce.b)),_1cg=E(_1cf.b),_1ch=B(_It(8,_Lb,_1cg.a,_1cg.b,_1cg.c,_1cg.d,_1cg.e,_1cg.f));return new T2(0,new T4(0,_1c1,new T(function(){return E(_1c4)&4294967295;}),new T1(1,_1cf.a),_1ch.a),_1ch.b);}},_1ci=function(_1cj){var _1ck=E(_1cj),_1cl=B(_1bT(_1ck.a,_1ck.b,_1ck.c,_1ck.d,_1ck.e,_1ck.f));return new T2(0,_1cl.a,_1cl.b);},_1cm=function(_1cn){var _1co=E(_1cn),_1cp=B(_93(_1co.a,_1co.b,_1co.c,_1co.d,_1co.e,_1co.f)),_1cq=B(_aA(E(_1cp.a)&4294967295,_1bP,_1cp.b));return new T2(0,_1cq.a,_1cq.b);},_1cr=function(_1cs,_1ct,_1cu,_1cv,_1cw,_1cx){if(1>_1cx){var _1cy=E(_1cw);if(!_1cy){var _1cz=newByteArr(32760),_=writeOffAddr("w8",1,_1cz,0,3);return new F(function(){return A1(_1cs,new T5(0,_1cz,new T1(2,_1cz),0,1,32759));});}else{return new T2(1,new T4(0,_1ct,_1cu,_1cv,_1cy),new T(function(){var _1cA=newByteArr(32760),_=writeOffAddr("w8",1,_1cA,0,3);return B(A1(_1cs,new T5(0,_1cA,new T1(2,_1cA),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_1ct,_1cv+_1cw|0),0,3);return new F(function(){return A1(_1cs,new T5(0,_1ct,_1cu,_1cv,_1cw+1|0,_1cx-1|0));});}},_1cB=function(_1cC,_1cD){var _1cE=E(_1cD);return new F(function(){return _1cr(_1cC,_1cE.a,_1cE.b,_1cE.c,_1cE.d,_1cE.e);});},_1cF=function(_1cG){var _1cH=E(_1cG);switch(_1cH._){case 0:var _1cI=new T(function(){return E(B(_6x(_1cH.a)).b);}),_1cJ=new T(function(){var _1cK=B(_cS(_1cL,_1cH.b));return new T2(0,_1cK.a,E(_1cK.b));}),_1cM=function(_1cN){var _1cO=new T(function(){return B(A1(_1cI,new T(function(){return B(A1(E(_1cJ).b,_1cN));})));}),_1cP=new T(function(){var _1cQ=newByteArr(32760),_=writeOffAddr("w8",1,_1cQ,0,0);return B(A1(_1cO,new T5(0,_1cQ,new T1(2,_1cQ),0,1,32759)));});return function(_1cR){var _1cS=E(_1cR),_1cT=_1cS.a,_1cU=_1cS.b,_1cV=_1cS.c,_1cW=_1cS.d,_1cX=_1cS.e;if(1>_1cX){var _1cY=E(_1cW);if(!_1cY){var _1cZ=newByteArr(32760),_=writeOffAddr("w8",1,_1cZ,0,0);return new F(function(){return A1(_1cO,new T5(0,_1cZ,new T1(2,_1cZ),0,1,32759));});}else{return new T2(1,new T4(0,_1cT,_1cU,_1cV,_1cY),_1cP);}}else{var _=writeOffAddr("w8",1,plusAddr(_1cT,_1cV+_1cW|0),0,0);return new F(function(){return A1(_1cO,new T5(0,_1cT,_1cU,_1cV,_1cW+1|0,_1cX-1|0));});}};};return new T2(0,new T(function(){return E(E(_1cJ).a);}),_1cM);case 1:var _1d0=new T(function(){var _1d1=B(_Ng(_1cH.a));return new T2(0,_1d1.a,E(_1d1.b));}),_1d2=function(_1d3){var _1d4=new T(function(){return B(A1(E(_1d0).b,_1d3));}),_1d5=new T(function(){var _1d6=newByteArr(32760),_=writeOffAddr("w8",1,_1d6,0,4);return B(A1(_1d4,new T5(0,_1d6,new T1(2,_1d6),0,1,32759)));});return function(_1d7){var _1d8=E(_1d7),_1d9=_1d8.a,_1da=_1d8.b,_1db=_1d8.c,_1dc=_1d8.d,_1dd=_1d8.e;if(1>_1dd){var _1de=E(_1dc);if(!_1de){var _1df=newByteArr(32760),_=writeOffAddr("w8",1,_1df,0,4);return new F(function(){return A1(_1d4,new T5(0,_1df,new T1(2,_1df),0,1,32759));});}else{return new T2(1,new T4(0,_1d9,_1da,_1db,_1de),_1d5);}}else{var _=writeOffAddr("w8",1,plusAddr(_1d9,_1db+_1dc|0),0,4);return new F(function(){return A1(_1d4,new T5(0,_1d9,_1da,_1db,_1dc+1|0,_1dd-1|0));});}};};return new T2(0,new T(function(){return E(E(_1d0).a);}),_1d2);case 2:var _1dg=new T(function(){var _1dh=B(_6x(_1cH.a));return new T2(0,_1dh.a,E(_1dh.b));}),_1di=function(_1dj){var _1dk=new T(function(){return B(A1(E(_1dg).b,_1dj));}),_1dl=new T(function(){var _1dm=newByteArr(32760),_=writeOffAddr("w8",1,_1dm,0,1);return B(A1(_1dk,new T5(0,_1dm,new T1(2,_1dm),0,1,32759)));});return function(_1dn){var _1do=E(_1dn),_1dp=_1do.a,_1dq=_1do.b,_1dr=_1do.c,_1ds=_1do.d,_1dt=_1do.e;if(1>_1dt){var _1du=E(_1ds);if(!_1du){var _1dv=newByteArr(32760),_=writeOffAddr("w8",1,_1dv,0,1);return new F(function(){return A1(_1dk,new T5(0,_1dv,new T1(2,_1dv),0,1,32759));});}else{return new T2(1,new T4(0,_1dp,_1dq,_1dr,_1du),_1dl);}}else{var _=writeOffAddr("w8",1,plusAddr(_1dp,_1dr+_1ds|0),0,1);return new F(function(){return A1(_1dk,new T5(0,_1dp,_1dq,_1dr,_1ds+1|0,_1dt-1|0));});}};};return new T2(0,new T(function(){return E(E(_1dg).a);}),_1di);case 3:var _1dw=new T(function(){return E(B(_6x(_1cH.a)).b);}),_1dx=new T(function(){var _1dy=B(_1cF(_1cH.b));return new T2(0,_1dy.a,E(_1dy.b));}),_1dz=function(_1dA){var _1dB=new T(function(){return B(A1(_1dw,new T(function(){return B(A1(E(_1dx).b,_1dA));})));}),_1dC=new T(function(){var _1dD=newByteArr(32760),_=writeOffAddr("w8",1,_1dD,0,2);return B(A1(_1dB,new T5(0,_1dD,new T1(2,_1dD),0,1,32759)));});return function(_1dE){var _1dF=E(_1dE),_1dG=_1dF.a,_1dH=_1dF.b,_1dI=_1dF.c,_1dJ=_1dF.d,_1dK=_1dF.e;if(1>_1dK){var _1dL=E(_1dJ);if(!_1dL){var _1dM=newByteArr(32760),_=writeOffAddr("w8",1,_1dM,0,2);return new F(function(){return A1(_1dB,new T5(0,_1dM,new T1(2,_1dM),0,1,32759));});}else{return new T2(1,new T4(0,_1dG,_1dH,_1dI,_1dL),_1dC);}}else{var _=writeOffAddr("w8",1,plusAddr(_1dG,_1dI+_1dJ|0),0,2);return new F(function(){return A1(_1dB,new T5(0,_1dG,_1dH,_1dI,_1dJ+1|0,_1dK-1|0));});}};};return new T2(0,new T(function(){return E(E(_1dx).a);}),_1dz);case 4:return new T2(0,_0,_1cB);case 5:var _1dN=new T(function(){var _1dO=B(_1cF(_1cH.a));return new T2(0,_1dO.a,E(_1dO.b));}),_1dP=function(_1dQ){var _1dR=new T(function(){return B(A1(E(_1dN).b,_1dQ));}),_1dS=new T(function(){var _1dT=newByteArr(32760),_=writeOffAddr("w8",1,_1dT,0,5);return B(A1(_1dR,new T5(0,_1dT,new T1(2,_1dT),0,1,32759)));});return function(_1dU){var _1dV=E(_1dU),_1dW=_1dV.a,_1dX=_1dV.b,_1dY=_1dV.c,_1dZ=_1dV.d,_1e0=_1dV.e;if(1>_1e0){var _1e1=E(_1dZ);if(!_1e1){var _1e2=newByteArr(32760),_=writeOffAddr("w8",1,_1e2,0,5);return new F(function(){return A1(_1dR,new T5(0,_1e2,new T1(2,_1e2),0,1,32759));});}else{return new T2(1,new T4(0,_1dW,_1dX,_1dY,_1e1),_1dS);}}else{var _=writeOffAddr("w8",1,plusAddr(_1dW,_1dY+_1dZ|0),0,5);return new F(function(){return A1(_1dR,new T5(0,_1dW,_1dX,_1dY,_1dZ+1|0,_1e0-1|0));});}};};return new T2(0,new T(function(){return E(E(_1dN).a);}),_1dP);default:var _1e3=new T(function(){var _1e4=B(_17T(_1cH.a));return new T2(0,_1e4.a,E(_1e4.b));}),_1e5=function(_1e6){var _1e7=new T(function(){return B(A1(E(_1e3).b,_1e6));}),_1e8=new T(function(){var _1e9=newByteArr(32760),_=writeOffAddr("w8",1,_1e9,0,6);return B(A1(_1e7,new T5(0,_1e9,new T1(2,_1e9),0,1,32759)));});return function(_1ea){var _1eb=E(_1ea),_1ec=_1eb.a,_1ed=_1eb.b,_1ee=_1eb.c,_1ef=_1eb.d,_1eg=_1eb.e;if(1>_1eg){var _1eh=E(_1ef);if(!_1eh){var _1ei=newByteArr(32760),_=writeOffAddr("w8",1,_1ei,0,6);return new F(function(){return A1(_1e7,new T5(0,_1ei,new T1(2,_1ei),0,1,32759));});}else{return new T2(1,new T4(0,_1ec,_1ed,_1ee,_1eh),_1e8);}}else{var _=writeOffAddr("w8",1,plusAddr(_1ec,_1ee+_1ef|0),0,6);return new F(function(){return A1(_1e7,new T5(0,_1ec,_1ed,_1ee,_1ef+1|0,_1eg-1|0));});}};};return new T2(0,new T(function(){return E(E(_1e3).a);}),_1e5);}},_1ej=function(_1ek){var _1el=B(_1cF(_1ek));return new T2(0,_1el.a,E(_1el.b));},_1cL=new T(function(){return new T2(0,_1ej,_1bo);}),_1em=function(_1en){var _1eo=E(_1en),_1ep=new T(function(){return E(B(_cS(_1cL,_1eo.a)).b);}),_1eq=new T(function(){var _1er=B(_17T(_1eo.b));return new T2(0,_1er.a,E(_1er.b));}),_1es=function(_1et){return new F(function(){return A1(_1ep,new T(function(){return B(A1(E(_1eq).b,_1et));}));});};return new T2(0,new T(function(){return E(E(_1eq).a);}),E(_1es));},_1eu=new T2(0,_1em,_1bP),_1ev=function(_1ew){var _1ex=B(_cS(_1eu,_1ew));return new T2(0,_1ex.a,E(_1ex.b));},_1ey=new T2(0,_1ev,_1cm),_1ez=function(_1eA,_1eB,_1eC,_1eD,_1eE,_1eF){if(1>_1eF){var _1eG=E(_1eE);if(!_1eG){var _1eH=newByteArr(32760),_=writeOffAddr("w8",1,_1eH,0,0);return new F(function(){return A1(_1eA,new T5(0,_1eH,new T1(2,_1eH),0,1,32759));});}else{return new T2(1,new T4(0,_1eB,_1eC,_1eD,_1eG),new T(function(){var _1eI=newByteArr(32760),_=writeOffAddr("w8",1,_1eI,0,0);return B(A1(_1eA,new T5(0,_1eI,new T1(2,_1eI),0,1,32759)));}));}}else{var _=writeOffAddr("w8",1,plusAddr(_1eB,_1eD+_1eE|0),0,0);return new F(function(){return A1(_1eA,new T5(0,_1eB,_1eC,_1eD,_1eE+1|0,_1eF-1|0));});}},_1eJ=function(_1eK,_1eL){var _1eM=E(_1eL);return new F(function(){return _1ez(_1eK,_1eM.a,_1eM.b,_1eM.c,_1eM.d,_1eM.e);});},_1eN=function(_1eO,_1eP){var _1eQ=E(_1eP);if(!_1eQ._){return new T2(0,_0,_1eJ);}else{var _1eR=new T(function(){return B(A2(_cQ,_1eO,_1eQ.a));}),_1eS=function(_1eT){var _1eU=new T(function(){return B(A1(E(_1eR).b,_1eT));}),_1eV=new T(function(){var _1eW=newByteArr(32760),_=writeOffAddr("w8",1,_1eW,0,1);return B(A1(_1eU,new T5(0,_1eW,new T1(2,_1eW),0,1,32759)));});return function(_1eX){var _1eY=E(_1eX),_1eZ=_1eY.a,_1f0=_1eY.b,_1f1=_1eY.c,_1f2=_1eY.d,_1f3=_1eY.e;if(1>_1f3){var _1f4=E(_1f2);if(!_1f4){var _1f5=newByteArr(32760),_=writeOffAddr("w8",1,_1f5,0,1);return new F(function(){return A1(_1eU,new T5(0,_1f5,new T1(2,_1f5),0,1,32759));});}else{return new T2(1,new T4(0,_1eZ,_1f0,_1f1,_1f4),_1eV);}}else{var _=writeOffAddr("w8",1,plusAddr(_1eZ,_1f1+_1f2|0),0,1);return new F(function(){return A1(_1eU,new T5(0,_1eZ,_1f0,_1f1,_1f2+1|0,_1f3-1|0));});}};};return new T2(0,new T(function(){return E(E(_1eR).a);}),_1eS);}},_1f6=function(_1f7,_1f8,_1f9,_1fa){var _1fb=new T(function(){var _1fc=B(_My(_Nf,_2I,_1fa));return new T2(0,_1fc.a,E(_1fc.b));}),_1fd=new T(function(){var _1fe=B(_1eN(_1ey,_1f9));return new T2(0,_1fe.a,E(_1fe.b));}),_1ff=new T(function(){var _1fg=B(_3M(E(_1f8)>>>0));return new T2(0,_1fg.a,E(_1fg.b));}),_1fh=new T(function(){var _1fi=E(_1f7);return E(B(_19H(_1fi.a,_1fi.b,_1fi.c)).b);}),_1fj=function(_1fk){var _1fl=new T(function(){var _1fm=new T(function(){return B(A1(E(_1fd).b,new T(function(){return B(A1(E(_1fb).b,_1fk));})));});return B(A1(E(_1ff).b,_1fm));});return new F(function(){return A1(_1fh,_1fl);});};return new T2(0,new T(function(){return E(E(_1fb).a);}),_1fj);},_1fn=function(_1fo){var _1fp=E(_1fo),_1fq=B(_1f6(_1fp.a,_1fp.b,_1fp.c,_1fp.d));return new T2(0,_1fq.a,E(_1fq.b));},_1fr=new T2(0,_1fn,_1ci),_1fs=function(_1ft,_1fu){var _1fv=E(_1fu);return (_1fv._==0)?new T5(0,_1fv.a,E(_1fv.b),new T(function(){return B(A1(_1ft,_1fv.c));}),E(B(_1fs(_1ft,_1fv.d))),E(B(_1fs(_1ft,_1fv.e)))):new T0(1);},_1fw=function(_1fx,_1fy,_1fz,_1fA,_1fB,_1fC){var _1fD=B(_XF(_9u,_O8,_1fx,_1fy,_1fz,_1fA,_1fB,_1fC)),_1fE=E(_1fD.b),_1fF=B(_XF(_9u,_1fr,_1fE.a,_1fE.b,_1fE.c,_1fE.d,_1fE.e,_1fE.f)),_1fG=E(_1fF.b),_1fH=B(_XF(_9u,_1b3,_1fG.a,_1fG.b,_1fG.c,_1fG.d,_1fG.e,_1fG.f));return new T2(0,new T3(0,_1fD.a,new T(function(){return B(_1fs(_14Y,_1fF.a));}),_1fH.a),_1fH.b);},_1fI=function(_1fJ,_1fK){var _1fL=E(_1fJ);if(!_1fL._){return new T2(0,_M,_1fK);}else{var _1fM=B(A1(_1fL.a,_1fK)),_1fN=B(_1fI(_1fL.b,_1fM.b));return new T2(0,new T2(1,_1fM.a,_1fN.a),_1fN.b);}},_1fO=function(_1fP,_1fQ,_1fR){if(0>=_1fP){return new F(function(){return _1fI(_M,_1fR);});}else{var _1fS=function(_1fT){var _1fU=E(_1fT);return (_1fU==1)?E(new T2(1,_1fQ,_M)):new T2(1,_1fQ,new T(function(){return B(_1fS(_1fU-1|0));}));};return new F(function(){return _1fI(B(_1fS(_1fP)),_1fR);});}},_1fV=function(_1fW){var _1fX=E(_1fW);if(!_1fX._){return new T0(1);}else{var _1fY=E(_1fX.a);return new F(function(){return _Xw(1,new T5(0,1,E(_1fY.a),_1fY.b,E(_UB),E(_UB)),_1fX.b);});}},_1fZ=function(_1g0,_1g1,_1g2,_1g3,_1g4,_1g5,_1g6,_1g7){var _1g8=B(_93(_1g2,_1g3,_1g4,_1g5,_1g6,_1g7)),_1g9=B(_1fO(E(_1g8.a)&4294967295,function(_1ga){var _1gb=B(A1(_1g0,_1ga)),_1gc=B(A1(_1g1,_1gb.b));return new T2(0,new T2(0,_1gb.a,_1gc.a),_1gc.b);},_1g8.b));return new T2(0,new T(function(){return B(_1fV(_1g9.a));}),_1g9.b);},_1gd=new T(function(){return B(_9z(0,0,_M));}),_1ge=new T(function(){return B(unCStr("index"));}),_1gf=58,_1gg=32,_1gh=function(_1gi,_1gj){return new F(function(){return unAppCStr("Data.ByteString.",new T(function(){return B(_16(_1gi,new T2(1,_1gf,new T2(1,_1gg,_1gj))));}));});},_1gk=function(_1gl,_1gm){return new F(function(){return err(B(_1gh(_1gl,_1gm)));});},_1gn=function(_1go,_Is){return new F(function(){return _1gk(_1go,_Is);});},_1gp=function(_1gq){var _1gr=new T(function(){var _1gs=new T(function(){return B(unAppCStr(", length = ",new T(function(){return B(_9z(0,_1gq,_M));})));},1);return B(_16(_1gd,_1gs));});return new F(function(){return _1gn(_1ge,B(unAppCStr("index too large: ",_1gr)));});},_1gt=new T(function(){return B(_9z(0,1,_M));}),_1gu=function(_1gv){var _1gw=new T(function(){var _1gx=new T(function(){return B(unAppCStr(", length = ",new T(function(){return B(_9z(0,_1gv,_M));})));},1);return B(_16(_1gt,_1gx));});return new F(function(){return _1gn(_1ge,B(unAppCStr("index too large: ",_1gw)));});},_1gy=function(_1gz,_1gA,_1gB,_1gC,_1gD,_1gE){var _1gF=B(_8B(2,_1gz,_1gA,_1gB,_1gC,_1gD,_1gE)),_1gG=E(_1gF.a),_1gH=_1gG.a,_1gI=_1gG.b,_1gJ=_1gG.c,_1gK=_1gG.d;if(0<_1gK){var _1gL=readOffAddr("w8",1,plusAddr(_1gH,_1gJ),0);if(1<_1gK){var _1gM=readOffAddr("w8",1,plusAddr(_1gH,_1gJ+1|0),0);return new T2(0,(_1gL<<8>>>0|_1gM)>>>0,_1gF.b);}else{return new F(function(){return _1gu(_1gK);});}}else{return new F(function(){return _1gp(_1gK);});}},_1gN=new T(function(){return B(unCStr("Prelude.Enum.Bool.toEnum: bad argument"));}),_1gO=new T(function(){return B(err(_1gN));}),_1gP=new T(function(){return B(unCStr(")"));}),_1gQ=function(_1gR,_1gS){return new F(function(){return _l2(B(unAppCStr("Unable to read PGF file (",new T(function(){return B(_16(_1gR,_1gP));}))),_1gS);});},_1gT=function(_1gU,_1gV){return new F(function(){return _1gQ(_1gU,_1gV);});},_1gW=new T(function(){return B(unCStr("getLiteral"));}),_1gX=function(_1gY){return new F(function(){return _1gT(_1gW,_1gY);});},_1gZ=function(_1h0,_1h1,_1h2,_1h3,_1h4,_1h5){var _1h6=B(_8B(1,_1h0,_1h1,_1h2,_1h3,_1h4,_1h5)),_1h7=_1h6.b,_1h8=E(_1h6.a),_1h9=_1h8.b,_1ha=readOffAddr("w8",1,plusAddr(_1h8.a,_1h8.c),0);switch(E(_1ha)){case 0:var _1hb=E(_1h7),_1hc=B(_93(_1hb.a,_1hb.b,_1hb.c,_1hb.d,_1hb.e,_1hb.f)),_1hd=B(_aA(E(_1hc.a)&4294967295,_aq,_1hc.b));return new T2(0,new T1(0,_1hd.a),_1hd.b);case 1:var _1he=E(_1h7),_1hf=B(_93(_1he.a,_1he.b,_1he.c,_1he.d,_1he.e,_1he.f));return new T2(0,new T1(1,new T(function(){return E(_1hf.a)&4294967295;})),_1hf.b);case 2:var _1hg=E(_1h7),_1hh=B(_It(8,_Lb,_1hg.a,_1hg.b,_1hg.c,_1hg.d,_1hg.e,_1hg.f));return new T2(0,new T1(2,_1hh.a),_1hh.b);default:return new F(function(){return _1gX(E(_1h7).f);});}},_1hi=new T(function(){return B(unCStr("getBindType"));}),_1hj=function(_1hk){return new F(function(){return _1gT(_1hi,_1hk);});},_1hl=new T(function(){return B(unCStr("getExpr"));}),_1hm=function(_1hn){return new F(function(){return _1gT(_1hl,_1hn);});},_1ho=function(_1hp,_1hq,_1hr,_1hs,_1ht,_1hu){var _1hv=B(_8B(1,_1hp,_1hq,_1hr,_1hs,_1ht,_1hu)),_1hw=_1hv.b,_1hx=E(_1hv.a),_1hy=_1hx.b,_1hz=readOffAddr("w8",1,plusAddr(_1hx.a,_1hx.c),0);switch(E(_1hz)){case 0:var _1hA=E(_1hw),_1hB=B(_8B(1,_1hA.a,_1hA.b,_1hA.c,_1hA.d,_1hA.e,_1hA.f)),_1hC=_1hB.b,_1hD=E(_1hB.a),_1hE=_1hD.b,_1hF=readOffAddr("w8",1,plusAddr(_1hD.a,_1hD.c),0);switch(E(_1hF)){case 0:var _1hG=E(_1hC),_1hH=B(_9h(_1hG.a,_1hG.b,_1hG.c,_1hG.d,_1hG.e,_1hG.f)),_1hI=E(_1hH.b),_1hJ=B(_1ho(_1hI.a,_1hI.b,_1hI.c,_1hI.d,_1hI.e,_1hI.f));return new T2(0,new T3(0,_158,_1hH.a,_1hJ.a),_1hJ.b);case 1:var _1hK=E(_1hC),_1hL=B(_9h(_1hK.a,_1hK.b,_1hK.c,_1hK.d,_1hK.e,_1hK.f)),_1hM=E(_1hL.b),_1hN=B(_1ho(_1hM.a,_1hM.b,_1hM.c,_1hM.d,_1hM.e,_1hM.f));return new T2(0,new T3(0,_159,_1hL.a,_1hN.a),_1hN.b);default:return new F(function(){return _1hj(E(_1hC).f);});}break;case 1:var _1hO=E(_1hw),_1hP=B(_1ho(_1hO.a,_1hO.b,_1hO.c,_1hO.d,_1hO.e,_1hO.f)),_1hQ=E(_1hP.b),_1hR=B(_1ho(_1hQ.a,_1hQ.b,_1hQ.c,_1hQ.d,_1hQ.e,_1hQ.f));return new T2(0,new T2(1,_1hP.a,_1hR.a),_1hR.b);case 2:var _1hS=E(_1hw),_1hT=B(_1gZ(_1hS.a,_1hS.b,_1hS.c,_1hS.d,_1hS.e,_1hS.f));return new T2(0,new T1(2,_1hT.a),_1hT.b);case 3:var _1hU=E(_1hw),_1hV=B(_93(_1hU.a,_1hU.b,_1hU.c,_1hU.d,_1hU.e,_1hU.f));return new T2(0,new T(function(){return new T1(3,E(_1hV.a)&4294967295);}),_1hV.b);case 4:var _1hW=E(_1hw),_1hX=B(_9h(_1hW.a,_1hW.b,_1hW.c,_1hW.d,_1hW.e,_1hW.f));return new T2(0,new T1(4,_1hX.a),_1hX.b);case 5:var _1hY=E(_1hw),_1hZ=B(_93(_1hY.a,_1hY.b,_1hY.c,_1hY.d,_1hY.e,_1hY.f));return new T2(0,new T(function(){return new T1(5,E(_1hZ.a)&4294967295);}),_1hZ.b);case 6:var _1i0=E(_1hw),_1i1=B(_1ho(_1i0.a,_1i0.b,_1i0.c,_1i0.d,_1i0.e,_1i0.f)),_1i2=E(_1i1.b),_1i3=B(_1i4(_1i2.a,_1i2.b,_1i2.c,_1i2.d,_1i2.e,_1i2.f));return new T2(0,new T2(6,_1i1.a,_1i3.a),_1i3.b);case 7:var _1i5=E(_1hw),_1i6=B(_1ho(_1i5.a,_1i5.b,_1i5.c,_1i5.d,_1i5.e,_1i5.f));return new T2(0,new T1(7,_1i6.a),_1i6.b);default:return new F(function(){return _1hm(E(_1hw).f);});}},_1i7=function(_1i8){var _1i9=E(_1i8),_1ia=B(_1ho(_1i9.a,_1i9.b,_1i9.c,_1i9.d,_1i9.e,_1i9.f));return new T2(0,_1ia.a,_1ia.b);},_1ib=function(_1ic,_1id,_1ie,_1if,_1ig,_1ih){var _1ii=B(_8B(1,_1ic,_1id,_1ie,_1if,_1ig,_1ih)),_1ij=_1ii.b,_1ik=E(_1ii.a),_1il=_1ik.b,_1im=readOffAddr("w8",1,plusAddr(_1ik.a,_1ik.c),0);switch(E(_1im)){case 0:var _1in=E(_1ij),_1io=B(_9h(_1in.a,_1in.b,_1in.c,_1in.d,_1in.e,_1in.f)),_1ip=E(_1io.b),_1iq=B(_1i4(_1ip.a,_1ip.b,_1ip.c,_1ip.d,_1ip.e,_1ip.f));return new T2(0,new T3(0,_158,_1io.a,_1iq.a),_1iq.b);case 1:var _1ir=E(_1ij),_1is=B(_9h(_1ir.a,_1ir.b,_1ir.c,_1ir.d,_1ir.e,_1ir.f)),_1it=E(_1is.b),_1iu=B(_1i4(_1it.a,_1it.b,_1it.c,_1it.d,_1it.e,_1it.f));return new T2(0,new T3(0,_159,_1is.a,_1iu.a),_1iu.b);default:return new F(function(){return _1hj(E(_1ij).f);});}},_1iv=function(_1iw){var _1ix=E(_1iw),_1iy=B(_1ib(_1ix.a,_1ix.b,_1ix.c,_1ix.d,_1ix.e,_1ix.f));return new T2(0,_1iy.a,_1iy.b);},_1i4=function(_1iz,_1iA,_1iB,_1iC,_1iD,_1iE){var _1iF=B(_93(_1iz,_1iA,_1iB,_1iC,_1iD,_1iE)),_1iG=B(_1fO(E(_1iF.a)&4294967295,_1iv,_1iF.b)),_1iH=E(_1iG.b),_1iI=B(_9h(_1iH.a,_1iH.b,_1iH.c,_1iH.d,_1iH.e,_1iH.f)),_1iJ=E(_1iI.b),_1iK=B(_93(_1iJ.a,_1iJ.b,_1iJ.c,_1iJ.d,_1iJ.e,_1iJ.f)),_1iL=B(_1fO(E(_1iK.a)&4294967295,_1i7,_1iK.b));return new T2(0,new T3(0,_1iG.a,_1iI.a,_1iL.a),_1iL.b);},_1iM=new T(function(){return B(unCStr("getPatt"));}),_1iN=function(_1iO){return new F(function(){return _1gT(_1iM,_1iO);});},_1iP=function(_1iQ,_1iR,_1iS,_1iT,_1iU,_1iV){var _1iW=B(_8B(1,_1iQ,_1iR,_1iS,_1iT,_1iU,_1iV)),_1iX=_1iW.b,_1iY=E(_1iW.a),_1iZ=_1iY.b,_1j0=readOffAddr("w8",1,plusAddr(_1iY.a,_1iY.c),0);switch(E(_1j0)){case 0:var _1j1=E(_1iX),_1j2=B(_9h(_1j1.a,_1j1.b,_1j1.c,_1j1.d,_1j1.e,_1j1.f)),_1j3=E(_1j2.b),_1j4=B(_93(_1j3.a,_1j3.b,_1j3.c,_1j3.d,_1j3.e,_1j3.f)),_1j5=B(_1fO(E(_1j4.a)&4294967295,_1j6,_1j4.b));return new T2(0,new T2(0,_1j2.a,_1j5.a),_1j5.b);case 1:var _1j7=E(_1iX),_1j8=B(_9h(_1j7.a,_1j7.b,_1j7.c,_1j7.d,_1j7.e,_1j7.f));return new T2(0,new T1(2,_1j8.a),_1j8.b);case 2:var _1j9=E(_1iX),_1ja=B(_9h(_1j9.a,_1j9.b,_1j9.c,_1j9.d,_1j9.e,_1j9.f)),_1jb=E(_1ja.b),_1jc=B(_1iP(_1jb.a,_1jb.b,_1jb.c,_1jb.d,_1jb.e,_1jb.f));return new T2(0,new T2(3,_1ja.a,_1jc.a),_1jc.b);case 3:return new T2(0,_1b4,_1iX);case 4:var _1jd=E(_1iX),_1je=B(_1gZ(_1jd.a,_1jd.b,_1jd.c,_1jd.d,_1jd.e,_1jd.f));return new T2(0,new T1(1,_1je.a),_1je.b);case 5:var _1jf=E(_1iX),_1jg=B(_1iP(_1jf.a,_1jf.b,_1jf.c,_1jf.d,_1jf.e,_1jf.f));return new T2(0,new T1(5,_1jg.a),_1jg.b);case 6:var _1jh=E(_1iX),_1ji=B(_1ho(_1jh.a,_1jh.b,_1jh.c,_1jh.d,_1jh.e,_1jh.f));return new T2(0,new T1(6,_1ji.a),_1ji.b);default:return new F(function(){return _1iN(E(_1iX).f);});}},_1j6=function(_1jj){var _1jk=E(_1jj),_1jl=B(_1iP(_1jk.a,_1jk.b,_1jk.c,_1jk.d,_1jk.e,_1jk.f));return new T2(0,_1jl.a,_1jl.b);},_1jm=function(_1jn,_1jo,_1jp,_1jq,_1jr,_1js){var _1jt=B(_93(_1jn,_1jo,_1jp,_1jq,_1jr,_1js)),_1ju=B(_1fO(E(_1jt.a)&4294967295,_1j6,_1jt.b)),_1jv=E(_1ju.b),_1jw=B(_1ho(_1jv.a,_1jv.b,_1jv.c,_1jv.d,_1jv.e,_1jv.f));return new T2(0,new T2(0,_1ju.a,_1jw.a),_1jw.b);},_1jx=function(_1jy){var _1jz=E(_1jy),_1jA=B(_1jm(_1jz.a,_1jz.b,_1jz.c,_1jz.d,_1jz.e,_1jz.f));return new T2(0,_1jA.a,_1jA.b);},_1jB=function(_1jC,_1jD,_1jE,_1jF,_1jG,_1jH){var _1jI=B(_1i4(_1jC,_1jD,_1jE,_1jF,_1jG,_1jH)),_1jJ=_1jI.a,_1jK=E(_1jI.b),_1jL=B(_93(_1jK.a,_1jK.b,_1jK.c,_1jK.d,_1jK.e,_1jK.f)),_1jM=_1jL.a,_1jN=E(_1jL.b),_1jO=B(_8B(1,_1jN.a,_1jN.b,_1jN.c,_1jN.d,_1jN.e,_1jN.f)),_1jP=_1jO.b,_1jQ=E(_1jO.a),_1jR=_1jQ.b,_1jS=readOffAddr("w8",1,plusAddr(_1jQ.a,_1jQ.c),0);switch(_1jS&4294967295){case 0:var _1jT=E(_1jP),_1jU=B(_It(8,_Lb,_1jT.a,_1jT.b,_1jT.c,_1jT.d,_1jT.e,_1jT.f));return new T2(0,new T4(0,_1jJ,new T(function(){return E(_1jM)&4294967295;}),_2s,_1jU.a),_1jU.b);case 1:var _1jV=E(_1jP),_1jW=B(_93(_1jV.a,_1jV.b,_1jV.c,_1jV.d,_1jV.e,_1jV.f)),_1jX=B(_1fO(E(_1jW.a)&4294967295,_1jx,_1jW.b)),_1jY=E(_1jX.b),_1jZ=B(_It(8,_Lb,_1jY.a,_1jY.b,_1jY.c,_1jY.d,_1jY.e,_1jY.f));return new T2(0,new T4(0,_1jJ,new T(function(){return E(_1jM)&4294967295;}),new T1(1,_1jX.a),_1jZ.a),_1jZ.b);default:return E(_1gO);}},_1k0=function(_1k1){var _1k2=E(_1k1),_1k3=B(_1jB(_1k2.a,_1k2.b,_1k2.c,_1k2.d,_1k2.e,_1k2.f));return new T2(0,_1k3.a,_1k3.b);},_1k4=function(_1k5){var _1k6=E(_1k5),_1k7=B(_1gZ(_1k6.a,_1k6.b,_1k6.c,_1k6.d,_1k6.e,_1k6.f));return new T2(0,_1k7.a,_1k7.b);},_1k8=function(_1k9){var _1ka=E(_1k9),_1kb=B(_9h(_1ka.a,_1ka.b,_1ka.c,_1ka.d,_1ka.e,_1ka.f));return new T2(0,_1kb.a,_1kb.b);},_1kc=function(_1kd,_1ke){while(1){var _1kf=E(_1kd);if(!_1kf._){return (E(_1ke)._==0)?1:0;}else{var _1kg=E(_1ke);if(!_1kg._){return 2;}else{var _1kh=E(_1kf.a),_1ki=E(_1kg.a);if(_1kh!=_1ki){return (_1kh>_1ki)?2:0;}else{_1kd=_1kf.b;_1ke=_1kg.b;continue;}}}}},_1kj=function(_1kk,_1kl){return (B(_1kc(_1kk,_1kl))==0)?true:false;},_1km=function(_1kn,_1ko){return (B(_1kc(_1kn,_1ko))==2)?false:true;},_1kp=function(_1kq,_1kr){return (B(_1kc(_1kq,_1kr))==2)?true:false;},_1ks=function(_1kt,_1ku){return (B(_1kc(_1kt,_1ku))==0)?false:true;},_1kv=function(_1kw,_1kx){return (B(_1kc(_1kw,_1kx))==2)?E(_1kw):E(_1kx);},_1ky=function(_1kz,_1kA){return (B(_1kc(_1kz,_1kA))==2)?E(_1kA):E(_1kz);},_1kB={_:0,a:_se,b:_1kc,c:_1kj,d:_1km,e:_1kp,f:_1ks,g:_1kv,h:_1ky},_1kC=function(_1kD,_1kE,_1kF,_1kG,_1kH,_1kI,_1kJ,_1kK){var _1kL=function(_1kM){var _1kN=function(_1kO){var _1kP=memcmp(plusAddr(_1kD,_1kF),plusAddr(_1kH,_1kJ),_1kO>>>0);if(_1kP>=0){if(!E(_1kP)){var _1kQ=B(_gZ(_1kG,_1kK));}else{var _1kQ=2;}var _1kR=_1kQ;}else{var _1kR=0;}return E(_1kR);};if(_1kG>_1kK){return new F(function(){return _1kN(_1kK);});}else{return new F(function(){return _1kN(_1kG);});}};if(!E(_1kG)){if(!E(_1kK)){return 1;}else{return new F(function(){return _1kL(_);});}}else{return new F(function(){return _1kL(_);});}},_1kS=function(_1kT,_1kU,_1kV,_1kW,_1kX,_1kY,_1kZ){var _1l0=new T4(0,_1kU,_1kV,_1kW,_1kX),_1l1=E(_1kZ);if(!_1l1._){var _1l2=_1l1.c,_1l3=_1l1.d,_1l4=_1l1.e,_1l5=E(_1l1.b);switch(B(_1kC(_1kU,_1kV,_1kW,_1kX,_1l5.a,_1l5.b,_1l5.c,_1l5.d))){case 0:return new F(function(){return _UG(_1l5,_1l2,B(_1kS(_1kT,_1kU,_1kV,_1kW,_1kX,_1kY,_1l3)),_1l4);});break;case 1:return new T5(0,_1l1.a,E(_1l0),new T(function(){return B(A3(_1kT,_1l0,_1kY,_1l2));}),E(_1l3),E(_1l4));default:return new F(function(){return _Vn(_1l5,_1l2,_1l3,B(_1kS(_1kT,_1kU,_1kV,_1kW,_1kX,_1kY,_1l4)));});}}else{return new T5(0,1,E(_1l0),_1kY,E(_UB),E(_UB));}},_1l6=function(_1l7,_1l8){var _1l9=function(_1la,_1lb){while(1){var _1lc=E(_1lb);if(!_1lc._){return E(_1la);}else{var _1ld=E(_1lc.a),_1le=E(_1ld.a),_1lf=B(_1kS(_1l7,_1le.a,_1le.b,_1le.c,_1le.d,_1ld.b,_1la));_1la=_1lf;_1lb=_1lc.b;continue;}}};return new F(function(){return _1l9(_UB,_1l8);});},_1lg=function(_1lh){return E(E(_1lh).b);},_1li=function(_1lj,_1lk,_1ll,_1lm){var _1ln=E(_1lk),_1lo=E(_1lm);if(!_1lo._){var _1lp=_1lo.b,_1lq=_1lo.c,_1lr=_1lo.d,_1ls=_1lo.e;switch(B(A3(_1lg,_1lj,_1ln,_1lp))){case 0:return new F(function(){return _UG(_1lp,_1lq,B(_1li(_1lj,_1ln,_1ll,_1lr)),_1ls);});break;case 1:return new T5(0,_1lo.a,E(_1ln),_1ll,E(_1lr),E(_1ls));default:return new F(function(){return _Vn(_1lp,_1lq,_1lr,B(_1li(_1lj,_1ln,_1ll,_1ls)));});}}else{return new T5(0,1,E(_1ln),_1ll,E(_UB),E(_UB));}},_1lt=function(_1lu,_1lv,_1lw,_1lx){return new F(function(){return _1li(_1lu,_1lv,_1lw,_1lx);});},_1ly=function(_1lz,_1lA,_1lB,_1lC,_1lD){var _1lE=E(_1lD),_1lF=B(_1lG(_1lz,_1lA,_1lB,_1lC,_1lE.a,_1lE.b));return new T2(0,_1lF.a,_1lF.b);},_1lH=function(_1lI,_1lJ,_1lK){var _1lL=function(_1lM,_1lN){while(1){var _1lO=E(_1lM),_1lP=E(_1lN);if(!_1lP._){switch(B(A3(_1lg,_1lI,_1lO,_1lP.b))){case 0:_1lM=_1lO;_1lN=_1lP.d;continue;case 1:return new T1(1,_1lP.c);default:_1lM=_1lO;_1lN=_1lP.e;continue;}}else{return __Z;}}};return new F(function(){return _1lL(_1lJ,_1lK);});},_1lQ=function(_1lR,_1lS){var _1lT=E(_1lR);if(!_1lT._){return new T2(0,new T1(1,_1lS),_UB);}else{var _1lU=new T(function(){return new T5(0,1,E(_1lT.a),new T(function(){return B(_1lV(_1lT.b,_1lS));}),E(_UB),E(_UB));});return new T2(0,_2s,_1lU);}},_1lV=function(_1lW,_1lX){var _1lY=B(_1lQ(_1lW,_1lX));return new T2(0,_1lY.a,_1lY.b);},_1lG=function(_1lZ,_1m0,_1m1,_1m2,_1m3,_1m4){var _1m5=E(_1m1);if(!_1m5._){var _1m6=E(_1m3);return (_1m6._==0)?new T2(0,new T1(1,_1m2),_1m4):new T2(0,new T1(1,new T(function(){return B(A2(_1m0,_1m2,_1m6.a));})),_1m4);}else{var _1m7=_1m5.a,_1m8=_1m5.b,_1m9=B(_1lH(_1lZ,_1m7,_1m4));if(!_1m9._){var _1ma=new T(function(){return B(_1lt(_1lZ,_1m7,new T(function(){return B(_1lV(_1m8,_1m2));}),_1m4));});return new T2(0,_1m3,_1ma);}else{var _1mb=new T(function(){return B(_1lt(_1lZ,_1m7,new T(function(){return B(_1ly(_1lZ,_1m0,_1m8,_1m2,_1m9.a));}),_1m4));});return new T2(0,_1m3,_1mb);}}},_1mc=function(_1md,_1me,_1mf){var _1mg=function(_1mh,_1mi,_1mj){while(1){var _1mk=E(_1mh);if(!_1mk._){return new T2(0,_1mi,_1mj);}else{var _1ml=E(_1mk.a),_1mm=B(_1lG(_1md,_1me,_1ml.a,_1ml.b,_1mi,_1mj));_1mh=_1mk.b;_1mi=_1mm.a;_1mj=_1mm.b;continue;}}};return new F(function(){return _1mg(_1mf,_2s,_UB);});},_1mn=function(_1mo,_1mp,_1mq){var _1mr=E(_1mq);switch(_1mr._){case 0:var _1ms=_1mr.a,_1mt=_1mr.b,_1mu=_1mr.c,_1mv=_1mr.d,_1mw=_1mt>>>0;if(((_1mo>>>0&((_1mw-1>>>0^4294967295)>>>0^_1mw)>>>0)>>>0&4294967295)==_1ms){return ((_1mo>>>0&_1mw)>>>0==0)?new T4(0,_1ms,_1mt,E(B(_1mn(_1mo,_1mp,_1mu))),E(_1mv)):new T4(0,_1ms,_1mt,E(_1mu),E(B(_1mn(_1mo,_1mp,_1mv))));}else{var _1mx=(_1mo>>>0^_1ms>>>0)>>>0,_1my=(_1mx|_1mx>>>1)>>>0,_1mz=(_1my|_1my>>>2)>>>0,_1mA=(_1mz|_1mz>>>4)>>>0,_1mB=(_1mA|_1mA>>>8)>>>0,_1mC=(_1mB|_1mB>>>16)>>>0,_1mD=(_1mC^_1mC>>>1)>>>0&4294967295,_1mE=_1mD>>>0;return ((_1mo>>>0&_1mE)>>>0==0)?new T4(0,(_1mo>>>0&((_1mE-1>>>0^4294967295)>>>0^_1mE)>>>0)>>>0&4294967295,_1mD,E(new T2(1,_1mo,_1mp)),E(_1mr)):new T4(0,(_1mo>>>0&((_1mE-1>>>0^4294967295)>>>0^_1mE)>>>0)>>>0&4294967295,_1mD,E(_1mr),E(new T2(1,_1mo,_1mp)));}break;case 1:var _1mF=_1mr.a;if(_1mo!=_1mF){var _1mG=(_1mo>>>0^_1mF>>>0)>>>0,_1mH=(_1mG|_1mG>>>1)>>>0,_1mI=(_1mH|_1mH>>>2)>>>0,_1mJ=(_1mI|_1mI>>>4)>>>0,_1mK=(_1mJ|_1mJ>>>8)>>>0,_1mL=(_1mK|_1mK>>>16)>>>0,_1mM=(_1mL^_1mL>>>1)>>>0&4294967295,_1mN=_1mM>>>0;return ((_1mo>>>0&_1mN)>>>0==0)?new T4(0,(_1mo>>>0&((_1mN-1>>>0^4294967295)>>>0^_1mN)>>>0)>>>0&4294967295,_1mM,E(new T2(1,_1mo,_1mp)),E(_1mr)):new T4(0,(_1mo>>>0&((_1mN-1>>>0^4294967295)>>>0^_1mN)>>>0)>>>0&4294967295,_1mM,E(_1mr),E(new T2(1,_1mo,_1mp)));}else{return new T2(1,_1mo,_1mp);}break;default:return new T2(1,_1mo,_1mp);}},_1mO=function(_1mP,_1mQ){var _1mR=function(_1mS){while(1){var _1mT=E(_1mS);switch(_1mT._){case 0:var _1mU=_1mT.b>>>0;if(((_1mP>>>0&((_1mU-1>>>0^4294967295)>>>0^_1mU)>>>0)>>>0&4294967295)==_1mT.a){if(!((_1mP>>>0&_1mU)>>>0)){_1mS=_1mT.c;continue;}else{_1mS=_1mT.d;continue;}}else{return __Z;}break;case 1:return (_1mP!=_1mT.a)?__Z:new T1(1,_1mT.b);default:return __Z;}}};return new F(function(){return _1mR(_1mQ);});},_1mV=function(_1mW,_1mX,_1mY,_1mZ){var _1n0=E(_1mZ);if(!_1n0._){var _1n1=new T(function(){var _1n2=B(_1mV(_1n0.a,_1n0.b,_1n0.c,_1n0.d));return new T2(0,_1n2.a,_1n2.b);});return new T2(0,new T(function(){return E(E(_1n1).a);}),new T(function(){return B(_PR(_1mX,_1mY,E(_1n1).b));}));}else{return new T2(0,_1mX,_1mY);}},_1n3=function(_1n4,_1n5,_1n6,_1n7){var _1n8=E(_1n6);if(!_1n8._){var _1n9=new T(function(){var _1na=B(_1n3(_1n8.a,_1n8.b,_1n8.c,_1n8.d));return new T2(0,_1na.a,_1na.b);});return new T2(0,new T(function(){return E(E(_1n9).a);}),new T(function(){return B(_Qt(_1n5,E(_1n9).b,_1n7));}));}else{return new T2(0,_1n5,_1n7);}},_1nb=function(_1nc,_1nd){var _1ne=E(_1nc);if(!_1ne._){var _1nf=_1ne.a,_1ng=E(_1nd);if(!_1ng._){var _1nh=_1ng.a;if(_1nf<=_1nh){var _1ni=B(_1n3(_1nh,_1ng.b,_1ng.c,_1ng.d));return new F(function(){return _PR(_1ni.a,_1ne,_1ni.b);});}else{var _1nj=B(_1mV(_1nf,_1ne.b,_1ne.c,_1ne.d));return new F(function(){return _Qt(_1nj.a,_1nj.b,_1ng);});}}else{return E(_1ne);}}else{return E(_1nd);}},_1nk=function(_1nl,_1nm,_1nn,_1no,_1np){var _1nq=E(_1nl);if(!_1nq._){var _1nr=_1nq.a,_1ns=_1nq.b,_1nt=_1nq.c,_1nu=_1nq.d;if((imul(3,_1nr)|0)>=_1nm){if((imul(3,_1nm)|0)>=_1nr){return new F(function(){return _1nb(_1nq,new T4(0,_1nm,E(_1nn),E(_1no),E(_1np)));});}else{return new F(function(){return _Qt(_1ns,_1nt,B(_1nk(_1nu,_1nm,_1nn,_1no,_1np)));});}}else{return new F(function(){return _PR(_1nn,B(_1nv(_1nr,_1ns,_1nt,_1nu,_1no)),_1np);});}}else{return new T4(0,_1nm,E(_1nn),E(_1no),E(_1np));}},_1nv=function(_1nw,_1nx,_1ny,_1nz,_1nA){var _1nB=E(_1nA);if(!_1nB._){var _1nC=_1nB.a,_1nD=_1nB.b,_1nE=_1nB.c,_1nF=_1nB.d;if((imul(3,_1nw)|0)>=_1nC){if((imul(3,_1nC)|0)>=_1nw){return new F(function(){return _1nb(new T4(0,_1nw,E(_1nx),E(_1ny),E(_1nz)),_1nB);});}else{return new F(function(){return _Qt(_1nx,_1ny,B(_1nk(_1nz,_1nC,_1nD,_1nE,_1nF)));});}}else{return new F(function(){return _PR(_1nD,B(_1nv(_1nw,_1nx,_1ny,_1nz,_1nE)),_1nF);});}}else{return new T4(0,_1nw,E(_1nx),E(_1ny),E(_1nz));}},_1nG=function(_1nH,_1nI){var _1nJ=E(_1nH);if(!_1nJ._){var _1nK=_1nJ.a,_1nL=_1nJ.b,_1nM=_1nJ.c,_1nN=_1nJ.d,_1nO=E(_1nI);if(!_1nO._){var _1nP=_1nO.a,_1nQ=_1nO.b,_1nR=_1nO.c,_1nS=_1nO.d;if((imul(3,_1nK)|0)>=_1nP){if((imul(3,_1nP)|0)>=_1nK){return new F(function(){return _1nb(_1nJ,_1nO);});}else{return new F(function(){return _Qt(_1nL,_1nM,B(_1nk(_1nN,_1nP,_1nQ,_1nR,_1nS)));});}}else{return new F(function(){return _PR(_1nQ,B(_1nv(_1nK,_1nL,_1nM,_1nN,_1nR)),_1nS);});}}else{return E(_1nJ);}}else{return E(_1nI);}},_1nT=function(_1nU,_1nV){var _1nW=E(_1nV);if(!_1nW._){var _1nX=_1nW.b,_1nY=B(_1nT(_1nU,_1nW.c)),_1nZ=_1nY.a,_1o0=_1nY.b,_1o1=B(_1nT(_1nU,_1nW.d)),_1o2=_1o1.a,_1o3=_1o1.b;return (!B(A1(_1nU,_1nX)))?new T2(0,B(_1nG(_1nZ,_1o2)),B(_RN(_1nX,_1o0,_1o3))):new T2(0,B(_RN(_1nX,_1nZ,_1o2)),B(_1nG(_1o0,_1o3)));}else{return new T2(0,_PM,_PM);}},_1o4=function(_1o5,_1o6,_1o7,_1o8){var _1o9=E(_1o7),_1oa=B(_1ob(_1o5,_1o6,_1o9.a,_1o9.b,_1o8));return new T2(0,_1oa.a,_1oa.b);},_1oc=function(_1od,_1oe,_1of){while(1){var _1og=E(_1of);if(!_1og._){var _1oh=_1og.e;switch(B(A3(_1lg,_1od,_1oe,_1og.b))){case 0:return new T2(0,B(_1lH(_1od,_1oe,_1og.d)),_1og);case 1:return new T2(0,new T1(1,_1og.c),_1oh);default:_1of=_1oh;continue;}}else{return new T2(0,_2s,_UB);}}},_1oi=function(_1oj){return E(E(_1oj).f);},_1ok=function(_1ol,_1om,_1on){while(1){var _1oo=E(_1on);if(!_1oo._){if(!B(A3(_1oi,_1ol,_1oo.b,_1om))){return E(_1oo);}else{_1on=_1oo.d;continue;}}else{return new T0(1);}}},_1op=function(_1oq,_1or,_1os,_1ot){while(1){var _1ou=E(_1ot);if(!_1ou._){var _1ov=_1ou.b,_1ow=_1ou.d,_1ox=_1ou.e;switch(B(A3(_1lg,_1oq,_1or,_1ov))){case 0:if(!B(A3(_ox,_1oq,_1ov,_1os))){_1ot=_1ow;continue;}else{return new T2(0,B(_1lH(_1oq,_1or,_1ow)),_1ou);}break;case 1:return new T2(0,new T1(1,_1ou.c),B(_1ok(_1oq,_1os,_1ox)));default:_1ot=_1ox;continue;}}else{return new T2(0,_2s,_UB);}}},_1oy=function(_1oz,_1oA,_1oB,_1oC){var _1oD=E(_1oB);if(!_1oD._){return new F(function(){return _1oc(_1oz,_1oA,_1oC);});}else{return new F(function(){return _1op(_1oz,_1oA,_1oD.a,_1oC);});}},_1oE=__Z,_1oF=function(_1oG,_1oH,_1oI){var _1oJ=E(_1oH);if(!_1oJ._){return E(_1oI);}else{var _1oK=function(_1oL,_1oM){while(1){var _1oN=E(_1oM);if(!_1oN._){var _1oO=_1oN.b,_1oP=_1oN.e;switch(B(A3(_1lg,_1oG,_1oL,_1oO))){case 0:return new F(function(){return _WR(_1oO,_1oN.c,B(_1oK(_1oL,_1oN.d)),_1oP);});break;case 1:return E(_1oP);default:_1oM=_1oP;continue;}}else{return new T0(1);}}};return new F(function(){return _1oK(_1oJ.a,_1oI);});}},_1oQ=function(_1oR,_1oS,_1oT){var _1oU=E(_1oS);if(!_1oU._){return E(_1oT);}else{var _1oV=function(_1oW,_1oX){while(1){var _1oY=E(_1oX);if(!_1oY._){var _1oZ=_1oY.b,_1p0=_1oY.d;switch(B(A3(_1lg,_1oR,_1oZ,_1oW))){case 0:return new F(function(){return _WR(_1oZ,_1oY.c,_1p0,B(_1oV(_1oW,_1oY.e)));});break;case 1:return E(_1p0);default:_1oX=_1p0;continue;}}else{return new T0(1);}}};return new F(function(){return _1oV(_1oU.a,_1oT);});}},_1p1=function(_1p2){return E(E(_1p2).d);},_1p3=function(_1p4,_1p5,_1p6,_1p7){var _1p8=E(_1p5);if(!_1p8._){var _1p9=E(_1p6);if(!_1p9._){return E(_1p7);}else{var _1pa=function(_1pb,_1pc){while(1){var _1pd=E(_1pc);if(!_1pd._){if(!B(A3(_1oi,_1p4,_1pd.b,_1pb))){return E(_1pd);}else{_1pc=_1pd.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1pa(_1p9.a,_1p7);});}}else{var _1pe=_1p8.a,_1pf=E(_1p6);if(!_1pf._){var _1pg=function(_1ph,_1pi){while(1){var _1pj=E(_1pi);if(!_1pj._){if(!B(A3(_1p1,_1p4,_1pj.b,_1ph))){return E(_1pj);}else{_1pi=_1pj.e;continue;}}else{return new T0(1);}}};return new F(function(){return _1pg(_1pe,_1p7);});}else{var _1pk=function(_1pl,_1pm,_1pn){while(1){var _1po=E(_1pn);if(!_1po._){var _1pp=_1po.b;if(!B(A3(_1p1,_1p4,_1pp,_1pl))){if(!B(A3(_1oi,_1p4,_1pp,_1pm))){return E(_1po);}else{_1pn=_1po.d;continue;}}else{_1pn=_1po.e;continue;}}else{return new T0(1);}}};return new F(function(){return _1pk(_1pe,_1pf.a,_1p7);});}}},_1pq=function(_1pr,_1ps,_1pt,_1pu){var _1pv=E(_1pt);if(!_1pv._){var _1pw=E(_1pu);if(!_1pw._){var _1px=function(_1py,_1pz,_1pA,_1pB){var _1pC=E(_1pB);if(!_1pC._){var _1pD=E(_1pA);if(!_1pD._){var _1pE=_1pD.b,_1pF=_1pD.c,_1pG=_1pD.e,_1pH=B(_1oy(_1pr,_1pE,_1pz,_1pC)),_1pI=_1pH.b,_1pJ=new T1(1,E(_1pE)),_1pK=B(_1px(_1py,_1pJ,_1pD.d,B(_1p3(_1pr,_1py,_1pJ,_1pC)))),_1pL=E(_1pH.a);if(!_1pL._){return new F(function(){return _WR(_1pE,_1pF,_1pK,B(_1px(_1pJ,_1pz,_1pG,_1pI)));});}else{return new F(function(){return _WR(_1pE,new T(function(){return B(A3(_1ps,_1pE,_1pF,_1pL.a));}),_1pK,B(_1px(_1pJ,_1pz,_1pG,_1pI)));});}}else{return new F(function(){return _WR(_1pC.b,_1pC.c,B(_1oF(_1pr,_1py,_1pC.d)),B(_1oQ(_1pr,_1pz,_1pC.e)));});}}else{return E(_1pA);}},_1pM=_1oE,_1pN=_1oE,_1pO=_1pv.a,_1pP=_1pv.b,_1pQ=_1pv.c,_1pR=_1pv.d,_1pS=_1pv.e,_1pT=_1pw.a,_1pU=_1pw.b,_1pV=_1pw.c,_1pW=_1pw.d,_1pX=_1pw.e,_1pY=B(_1oy(_1pr,_1pP,_1pN,new T5(0,_1pT,E(_1pU),_1pV,E(_1pW),E(_1pX)))),_1pZ=_1pY.b,_1q0=new T1(1,E(_1pP)),_1q1=B(_1px(_1pM,_1q0,_1pR,B(_1p3(_1pr,_1pM,_1q0,new T5(0,_1pT,E(_1pU),_1pV,E(_1pW),E(_1pX)))))),_1q2=E(_1pY.a);if(!_1q2._){return new F(function(){return _WR(_1pP,_1pQ,_1q1,B(_1px(_1q0,_1pN,_1pS,_1pZ)));});}else{return new F(function(){return _WR(_1pP,new T(function(){return B(A3(_1ps,_1pP,_1pQ,_1q2.a));}),_1q1,B(_1px(_1q0,_1pN,_1pS,_1pZ)));});}}else{return E(_1pv);}}else{return E(_1pu);}},_1ob=function(_1q3,_1q4,_1q5,_1q6,_1q7){var _1q8=E(_1q7),_1q9=_1q8.a,_1qa=new T(function(){return B(_1pq(_1q3,function(_1qb,_1qc,_1qd){return new F(function(){return _1o4(_1q3,_1q4,_1qc,_1qd);});},_1q6,_1q8.b));}),_1qe=new T(function(){var _1qf=E(_1q5);if(!_1qf._){return E(_1q9);}else{var _1qg=E(_1q9);if(!_1qg._){return E(_1qf);}else{return new T1(1,new T(function(){return B(A2(_1q4,_1qf.a,_1qg.a));}));}}});return new T2(0,_1qe,_1qa);},_1qh=function(_1qi,_1qj,_1qk){var _1ql=function(_1qm,_1qn,_1qo){while(1){var _1qp=E(_1qm);if(!_1qp._){return new T2(0,_1qn,_1qo);}else{var _1qq=B(_1ob(_1qi,_1qj,_1qn,_1qo,_1qp.a));_1qm=_1qp.b;_1qn=_1qq.a;_1qo=_1qq.b;continue;}}};return new F(function(){return _1ql(_1qk,_2s,_UB);});},_1qr=new T0(2),_1qs=function(_1qt,_1qu){return E(_1qt)==E(_1qu);},_1qv=function(_1qw,_1qx){var _1qy=E(_1qw);switch(_1qy._){case 0:var _1qz=E(_1qx);if(!_1qz._){return new F(function(){return _rU(_1qy.a,_1qz.a);});}else{return false;}break;case 1:var _1qA=E(_1qx);if(_1qA._==1){return new F(function(){return _gI(_1qy.a,_1qA.a);});}else{return false;}break;default:var _1qB=E(_1qx);if(_1qB._==2){return new F(function(){return _1qs(_1qy.a,_1qB.a);});}else{return false;}}},_1qC=function(_1qD,_1qE,_1qF){while(1){var _1qG=E(_1qE);if(!_1qG._){return (E(_1qF)._==0)?true:false;}else{var _1qH=E(_1qF);if(!_1qH._){return false;}else{if(!B(A3(_oz,_1qD,_1qG.a,_1qH.a))){return false;}else{_1qE=_1qG.b;_1qF=_1qH.b;continue;}}}}},_1qI=function(_1qJ,_1qK){return (!B(_1qL(_1qJ,_1qK)))?true:false;},_1qM=new T2(0,_1qL,_1qI),_1qN=new T(function(){return E(_1qM);}),_1qO=function(_1qP,_1qQ){return (E(_1qP)==0)?(E(_1qQ)==0)?false:true:(E(_1qQ)==0)?true:false;},_1qR=function(_1qS,_1qT){return (E(_1qS)==0)?(E(_1qT)==0)?true:false:(E(_1qT)==0)?false:true;},_1qU=new T2(0,_1qR,_1qO),_1qV=new T(function(){return E(_1qU);}),_1qW=function(_1qX,_1qY,_1qZ,_1r0,_1r1,_1r2){if(!B(A3(_oz,_1qV,_1qX,_1r0))){return false;}else{var _1r3=E(_1qY),_1r4=_1r3.a,_1r5=_1r3.c,_1r6=_1r3.d,_1r7=E(_1r1),_1r8=_1r7.a,_1r9=_1r7.c,_1ra=_1r7.d;if(_1r6==_1ra){var _1rb=function(_1rc){if(B(_1kC(_1r4,_1r3.b,_1r5,_1r6,_1r8,_1r7.b,_1r9,_1ra))==1){return new F(function(){return _1rd(_1qZ,_1r2);});}else{return false;}};if(!addrEq(_1r4,_1r8)){return new F(function(){return _1rb(_);});}else{if(_1r5!=_1r9){return new F(function(){return _1rb(_);});}else{return new F(function(){return _1rd(_1qZ,_1r2);});}}}else{return false;}}},_1re=function(_1rf,_1rg){var _1rh=E(_1rf),_1ri=E(_1rg);return new F(function(){return _1qW(_1rh.a,_1rh.b,_1rh.c,_1ri.a,_1ri.b,_1ri.c);});},_1rj=function(_1rk,_1rl,_1rm,_1rn,_1ro,_1rp){if(!B(A3(_oz,_1qV,_1rk,_1rn))){return true;}else{var _1rq=E(_1rl),_1rr=_1rq.a,_1rs=_1rq.c,_1rt=_1rq.d,_1ru=E(_1ro),_1rv=_1ru.a,_1rw=_1ru.c,_1rx=_1ru.d;if(_1rt==_1rx){var _1ry=function(_1rz){if(B(_1kC(_1rr,_1rq.b,_1rs,_1rt,_1rv,_1ru.b,_1rw,_1rx))==1){var _1rA=E(_1rm);return (!B(_1rB(_1rA.a,_1rA.b,_1rA.c,_1rp)))?true:false;}else{return true;}};if(!addrEq(_1rr,_1rv)){return new F(function(){return _1ry(_);});}else{if(_1rs!=_1rw){return new F(function(){return _1ry(_);});}else{var _1rC=E(_1rm);return (!B(_1rB(_1rC.a,_1rC.b,_1rC.c,_1rp)))?true:false;}}}else{return true;}}},_1rD=function(_1rE,_1rF){var _1rG=E(_1rE),_1rH=E(_1rF);return new F(function(){return _1rj(_1rG.a,_1rG.b,_1rG.c,_1rH.a,_1rH.b,_1rH.c);});},_1rI=new T(function(){return new T2(0,_1re,_1rD);}),_1rB=function(_1rJ,_1rK,_1rL,_1rM){var _1rN=E(_1rM),_1rO=_1rN.c;if(!B(_1qC(_1rI,_1rJ,_1rN.a))){return false;}else{var _1rP=E(_1rK),_1rQ=_1rP.a,_1rR=_1rP.c,_1rS=_1rP.d,_1rT=E(_1rN.b),_1rU=_1rT.a,_1rV=_1rT.c,_1rW=_1rT.d;if(_1rS==_1rW){var _1rX=function(_1rY){if(B(_1kC(_1rQ,_1rP.b,_1rR,_1rS,_1rU,_1rT.b,_1rV,_1rW))==1){return new F(function(){return _1qC(_1qN,_1rL,_1rO);});}else{return false;}};if(!addrEq(_1rQ,_1rU)){return new F(function(){return _1rX(_);});}else{if(_1rR!=_1rV){return new F(function(){return _1rX(_);});}else{return new F(function(){return _1qC(_1qN,_1rL,_1rO);});}}}else{return false;}}},_1rd=function(_1rZ,_1s0){var _1s1=E(_1rZ);return new F(function(){return _1rB(_1s1.a,_1s1.b,_1s1.c,_1s0);});},_1s2=function(_1s3,_1s4){var _1s5=E(_1s3),_1s6=_1s5.a,_1s7=_1s5.b,_1s8=_1s5.c,_1s9=_1s5.d,_1sa=E(_1s4),_1sb=_1sa.a,_1sc=_1sa.b,_1sd=_1sa.c,_1se=_1sa.d;return (_1s9==_1se)?(!addrEq(_1s6,_1sb))?(B(_1kC(_1s6,_1s7,_1s8,_1s9,_1sb,_1sc,_1sd,_1se))==1)?true:false:(_1s8!=_1sd)?(B(_1kC(_1s6,_1s7,_1s8,_1s9,_1sb,_1sc,_1sd,_1se))==1)?true:false:true:false;},_1qL=function(_1sf,_1sg){while(1){var _1sh=B((function(_1si,_1sj){var _1sk=E(_1si);switch(_1sk._){case 0:var _1sl=_1sk.c,_1sm=E(_1sj);if(!_1sm._){var _1sn=_1sm.a,_1so=_1sm.c,_1sp=function(_1sq){var _1sr=E(_1sk.b),_1ss=_1sr.a,_1st=_1sr.b,_1su=_1sr.c,_1sv=_1sr.d,_1sw=E(_1sm.b),_1sx=_1sw.a,_1sy=_1sw.b,_1sz=_1sw.c,_1sA=_1sw.d;if(_1sv==_1sA){if(!addrEq(_1ss,_1sx)){if(B(_1kC(_1ss,_1st,_1su,_1sv,_1sx,_1sy,_1sz,_1sA))==1){return new F(function(){return _1qL(_1sl,_1so);});}else{return false;}}else{if(_1su!=_1sz){if(B(_1kC(_1ss,_1st,_1su,_1sv,_1sx,_1sy,_1sz,_1sA))==1){return new F(function(){return _1qL(_1sl,_1so);});}else{return false;}}else{return new F(function(){return _1qL(_1sl,_1so);});}}}else{return false;}};if(!E(_1sk.a)){if(!E(_1sn)){return new F(function(){return _1sp(_);});}else{return false;}}else{if(!E(_1sn)){return false;}else{return new F(function(){return _1sp(_);});}}}else{return false;}break;case 1:var _1sB=E(_1sj);if(_1sB._==1){if(!B(_1qL(_1sk.a,_1sB.a))){return false;}else{_1sf=_1sk.b;_1sg=_1sB.b;return __continue;}}else{return false;}break;case 2:var _1sC=E(_1sj);if(_1sC._==2){return new F(function(){return _1qv(_1sk.a,_1sC.a);});}else{return false;}break;case 3:var _1sD=E(_1sj);return (_1sD._==3)?_1sk.a==_1sD.a:false;case 4:var _1sE=E(_1sj);if(_1sE._==4){return new F(function(){return _1s2(_1sk.a,_1sE.a);});}else{return false;}break;case 5:var _1sF=E(_1sj);return (_1sF._==5)?_1sk.a==_1sF.a:false;case 6:var _1sG=E(_1sj);if(_1sG._==6){if(!B(_1qL(_1sk.a,_1sG.a))){return false;}else{return new F(function(){return _1rd(_1sk.b,_1sG.b);});}}else{return false;}break;default:var _1sH=E(_1sj);if(_1sH._==7){_1sf=_1sk.a;_1sg=_1sH.a;return __continue;}else{return false;}}})(_1sf,_1sg));if(_1sh!=__continue){return _1sh;}}},_1sI=function(_1sJ,_1sK,_1sL,_1sM){return (_1sJ!=_1sL)?true:(E(_1sK)!=E(_1sM))?true:false;},_1sN=function(_1sO,_1sP){var _1sQ=E(_1sO),_1sR=E(_1sP);return new F(function(){return _1sI(E(_1sQ.a),_1sQ.b,E(_1sR.a),_1sR.b);});},_1sS=function(_1sT,_1sU,_1sV,_1sW){if(_1sT!=_1sV){return false;}else{return new F(function(){return _gI(_1sU,_1sW);});}},_1sX=function(_1sY,_1sZ){var _1t0=E(_1sY),_1t1=E(_1sZ);return new F(function(){return _1sS(E(_1t0.a),_1t0.b,E(_1t1.a),_1t1.b);});},_1t2=new T2(0,_1sX,_1sN),_1t3=function(_1t4,_1t5,_1t6,_1t7){return (!B(_1qC(_1t2,_1t4,_1t6)))?true:(_1t5!=_1t7)?true:false;},_1t8=function(_1t9,_1ta){var _1tb=E(_1t9),_1tc=E(_1ta);return new F(function(){return _1t3(_1tb.a,_1tb.b,_1tc.a,_1tc.b);});},_1td=function(_1te,_1tf){var _1tg=E(_1te),_1th=E(_1tf);return (!B(_1qC(_1t2,_1tg.a,_1th.a)))?false:_1tg.b==_1th.b;},_1ti=new T2(0,_1td,_1t8),_1tj=function(_1tk,_1tl){while(1){var _1tm=E(_1tk);if(!_1tm._){return (E(_1tl)._==0)?true:false;}else{var _1tn=E(_1tl);if(!_1tn._){return false;}else{if(!B(_s6(_1tm.a,_1tn.a))){return false;}else{_1tk=_1tm.b;_1tl=_1tn.b;continue;}}}}},_1to=function(_1tp,_1tq){var _1tr=E(_1tp);switch(_1tr._){case 0:var _1ts=E(_1tq);if(!_1ts._){if(_1tr.a!=_1ts.a){return false;}else{return new F(function(){return _1qC(_1ti,_1tr.b,_1ts.b);});}}else{return false;}break;case 1:var _1tt=E(_1tq);return (_1tt._==1)?_1tr.a==_1tt.a:false;default:var _1tu=_1tr.b,_1tv=_1tr.c,_1tw=E(_1tq);if(_1tw._==2){var _1tx=_1tw.b,_1ty=_1tw.c,_1tz=E(_1tr.a),_1tA=_1tz.a,_1tB=_1tz.c,_1tC=_1tz.d,_1tD=E(_1tw.a),_1tE=_1tD.a,_1tF=_1tD.c,_1tG=_1tD.d;if(_1tC==_1tG){var _1tH=function(_1tI){if(B(_1kC(_1tA,_1tz.b,_1tB,_1tC,_1tE,_1tD.b,_1tF,_1tG))==1){if(!B(_1qL(_1tu,_1tx))){return false;}else{return new F(function(){return _1tj(_1tv,_1ty);});}}else{return false;}};if(!addrEq(_1tA,_1tE)){return new F(function(){return _1tH(_);});}else{if(_1tB!=_1tF){return new F(function(){return _1tH(_);});}else{if(!B(_1qL(_1tu,_1tx))){return false;}else{return new F(function(){return _1tj(_1tv,_1ty);});}}}}else{return false;}}else{return false;}}},_1tJ=function(_1tK,_1tL){return (!B(_1to(_1tK,_1tL)))?true:false;},_1tM=new T2(0,_1to,_1tJ),_1tN=function(_1tO,_1tP){var _1tQ=E(_1tO),_1tR=E(_1tP);return (_1tQ>=_1tR)?(_1tQ!=_1tR)?2:1:0;},_1tS=function(_1tT,_1tU){var _1tV=E(_1tT);switch(_1tV._){case 0:var _1tW=E(_1tU);if(!_1tW._){return new F(function(){return _1kc(_1tV.a,_1tW.a);});}else{return 0;}break;case 1:var _1tX=E(_1tU);switch(_1tX._){case 0:return 2;case 1:return new F(function(){return _h2(_1tV.a,_1tX.a);});break;default:return 0;}break;default:var _1tY=E(_1tU);if(_1tY._==2){return new F(function(){return _1tN(_1tV.a,_1tY.a);});}else{return 2;}}},_1tZ=function(_1u0,_1u1){return (B(_1u2(_1u0,_1u1))==0)?true:false;},_1u3=function(_1u4,_1u5){return (B(_1u2(_1u4,_1u5))==2)?false:true;},_1u6=function(_1u7,_1u8){return (B(_1u2(_1u7,_1u8))==2)?true:false;},_1u9=function(_1ua,_1ub){return (B(_1u2(_1ua,_1ub))==0)?false:true;},_1uc=function(_1ud,_1ue){return (B(_1u2(_1ud,_1ue))==2)?E(_1ud):E(_1ue);},_1uf=function(_1ug,_1uh){return (B(_1u2(_1ug,_1uh))==2)?E(_1uh):E(_1ug);},_1ui={_:0,a:_1qM,b:_1u2,c:_1tZ,d:_1u3,e:_1u6,f:_1u9,g:_1uc,h:_1uf},_1uj=new T(function(){return E(_1ui);}),_1uk=function(_1ul,_1um,_1un){while(1){var _1uo=E(_1um);if(!_1uo._){return (E(_1un)._==0)?1:0;}else{var _1up=E(_1un);if(!_1up._){return 2;}else{var _1uq=B(A3(_1lg,_1ul,_1uo.a,_1up.a));if(_1uq==1){_1um=_1uo.b;_1un=_1up.b;continue;}else{return E(_1uq);}}}}},_1ur=function(_1us,_1ut,_1uu,_1uv){var _1uw=E(_1uv);switch(B(_1uk(_1ux,_1us,_1uw.a))){case 0:return false;case 1:var _1uy=E(_1ut),_1uz=E(_1uw.b);switch(B(_1kC(_1uy.a,_1uy.b,_1uy.c,_1uy.d,_1uz.a,_1uz.b,_1uz.c,_1uz.d))){case 0:return false;case 1:return (B(_1uk(_1uj,_1uu,_1uw.c))==0)?false:true;default:return true;}break;default:return true;}},_1uA=function(_1uB,_1uC){var _1uD=E(_1uB);return new F(function(){return _1ur(_1uD.a,_1uD.b,_1uD.c,_1uC);});},_1uE=function(_1uF,_1uG){if(!E(_1uF)){return (E(_1uG)==0)?false:true;}else{var _1uH=E(_1uG);return false;}},_1uI=function(_1uJ,_1uK){if(!E(_1uJ)){var _1uL=E(_1uK);return true;}else{return (E(_1uK)==0)?false:true;}},_1uM=function(_1uN,_1uO){if(!E(_1uN)){var _1uP=E(_1uO);return false;}else{return (E(_1uO)==0)?true:false;}},_1uQ=function(_1uR,_1uS){if(!E(_1uR)){return (E(_1uS)==0)?true:false;}else{var _1uT=E(_1uS);return true;}},_1uU=function(_1uV,_1uW){return (E(_1uV)==0)?(E(_1uW)==0)?1:0:(E(_1uW)==0)?2:1;},_1uX=function(_1uY,_1uZ){if(!E(_1uY)){return E(_1uZ);}else{var _1v0=E(_1uZ);return 1;}},_1v1=function(_1v2,_1v3){if(!E(_1v2)){var _1v4=E(_1v3);return 0;}else{return E(_1v3);}},_1v5={_:0,a:_1qU,b:_1uU,c:_1uE,d:_1uI,e:_1uM,f:_1uQ,g:_1uX,h:_1v1},_1v6=new T(function(){return E(_1v5);}),_1v7=function(_1v8,_1v9,_1va,_1vb,_1vc,_1vd){switch(B(A3(_1lg,_1v6,_1v8,_1vb))){case 0:return false;case 1:var _1ve=E(_1v9),_1vf=E(_1vc);switch(B(_1kC(_1ve.a,_1ve.b,_1ve.c,_1ve.d,_1vf.a,_1vf.b,_1vf.c,_1vf.d))){case 0:return false;case 1:return new F(function(){return _1uA(_1va,_1vd);});break;default:return true;}break;default:return true;}},_1vg=function(_1vh,_1vi){var _1vj=E(_1vh),_1vk=E(_1vi);return new F(function(){return _1v7(_1vj.a,_1vj.b,_1vj.c,_1vk.a,_1vk.b,_1vk.c);});},_1vl=function(_1vm,_1vn,_1vo,_1vp){var _1vq=E(_1vp);switch(B(_1uk(_1ux,_1vm,_1vq.a))){case 0:return false;case 1:var _1vr=E(_1vn),_1vs=E(_1vq.b);switch(B(_1kC(_1vr.a,_1vr.b,_1vr.c,_1vr.d,_1vs.a,_1vs.b,_1vs.c,_1vs.d))){case 0:return false;case 1:return (B(_1uk(_1uj,_1vo,_1vq.c))==2)?true:false;default:return true;}break;default:return true;}},_1vt=function(_1vu,_1vv){var _1vw=E(_1vu);return new F(function(){return _1vl(_1vw.a,_1vw.b,_1vw.c,_1vv);});},_1vx=function(_1vy,_1vz,_1vA,_1vB,_1vC,_1vD){switch(B(A3(_1lg,_1v6,_1vy,_1vB))){case 0:return false;case 1:var _1vE=E(_1vz),_1vF=E(_1vC);switch(B(_1kC(_1vE.a,_1vE.b,_1vE.c,_1vE.d,_1vF.a,_1vF.b,_1vF.c,_1vF.d))){case 0:return false;case 1:return new F(function(){return _1vt(_1vA,_1vD);});break;default:return true;}break;default:return true;}},_1vG=function(_1vH,_1vI){var _1vJ=E(_1vH),_1vK=E(_1vI);return new F(function(){return _1vx(_1vJ.a,_1vJ.b,_1vJ.c,_1vK.a,_1vK.b,_1vK.c);});},_1vL=function(_1vM,_1vN,_1vO,_1vP){var _1vQ=E(_1vP);switch(B(_1uk(_1ux,_1vM,_1vQ.a))){case 0:return true;case 1:var _1vR=E(_1vN),_1vS=E(_1vQ.b);switch(B(_1kC(_1vR.a,_1vR.b,_1vR.c,_1vR.d,_1vS.a,_1vS.b,_1vS.c,_1vS.d))){case 0:return true;case 1:return (B(_1uk(_1uj,_1vO,_1vQ.c))==2)?false:true;default:return false;}break;default:return false;}},_1vT=function(_1vU,_1vV){var _1vW=E(_1vU);return new F(function(){return _1vL(_1vW.a,_1vW.b,_1vW.c,_1vV);});},_1vX=function(_1vY,_1vZ,_1w0,_1w1,_1w2,_1w3){switch(B(A3(_1lg,_1v6,_1vY,_1w1))){case 0:return true;case 1:var _1w4=E(_1vZ),_1w5=E(_1w2);switch(B(_1kC(_1w4.a,_1w4.b,_1w4.c,_1w4.d,_1w5.a,_1w5.b,_1w5.c,_1w5.d))){case 0:return true;case 1:return new F(function(){return _1vT(_1w0,_1w3);});break;default:return false;}break;default:return false;}},_1w6=function(_1w7,_1w8){var _1w9=E(_1w7),_1wa=E(_1w8);return new F(function(){return _1vX(_1w9.a,_1w9.b,_1w9.c,_1wa.a,_1wa.b,_1wa.c);});},_1wb=function(_1wc,_1wd){var _1we=E(_1wc),_1wf=_1we.a,_1wg=_1we.c,_1wh=E(_1wd),_1wi=_1wh.a,_1wj=_1wh.c;switch(B(A3(_1lg,_1v6,_1wf,_1wi))){case 0:return E(_1wh);case 1:var _1wk=E(_1we.b),_1wl=E(_1wh.b);switch(B(_1kC(_1wk.a,_1wk.b,_1wk.c,_1wk.d,_1wl.a,_1wl.b,_1wl.c,_1wl.d))){case 0:return new T3(0,_1wi,_1wl,_1wj);case 1:var _1wm=E(_1wg);return (!B(_1vL(_1wm.a,_1wm.b,_1wm.c,_1wj)))?new T3(0,_1wf,_1wk,_1wm):new T3(0,_1wi,_1wl,_1wj);default:return new T3(0,_1wf,_1wk,_1wg);}break;default:return E(_1we);}},_1wn=function(_1wo,_1wp){var _1wq=E(_1wo),_1wr=_1wq.a,_1ws=_1wq.c,_1wt=E(_1wp),_1wu=_1wt.a,_1wv=_1wt.c;switch(B(A3(_1lg,_1v6,_1wr,_1wu))){case 0:return E(_1wq);case 1:var _1ww=E(_1wq.b),_1wx=E(_1wt.b);switch(B(_1kC(_1ww.a,_1ww.b,_1ww.c,_1ww.d,_1wx.a,_1wx.b,_1wx.c,_1wx.d))){case 0:return new T3(0,_1wr,_1ww,_1ws);case 1:var _1wy=E(_1ws);return (!B(_1vL(_1wy.a,_1wy.b,_1wy.c,_1wv)))?new T3(0,_1wu,_1wx,_1wv):new T3(0,_1wr,_1ww,_1wy);default:return new T3(0,_1wu,_1wx,_1wv);}break;default:return E(_1wt);}},_1wz=function(_1wA,_1wB,_1wC,_1wD){var _1wE=E(_1wD);switch(B(_1uk(_1ux,_1wA,_1wE.a))){case 0:return true;case 1:var _1wF=E(_1wB),_1wG=E(_1wE.b);switch(B(_1kC(_1wF.a,_1wF.b,_1wF.c,_1wF.d,_1wG.a,_1wG.b,_1wG.c,_1wG.d))){case 0:return true;case 1:return (B(_1uk(_1uj,_1wC,_1wE.c))==0)?true:false;default:return false;}break;default:return false;}},_1wH=function(_1wI,_1wJ){var _1wK=E(_1wI);return new F(function(){return _1wz(_1wK.a,_1wK.b,_1wK.c,_1wJ);});},_1wL=function(_1wM,_1wN,_1wO,_1wP,_1wQ,_1wR){switch(B(A3(_1lg,_1v6,_1wM,_1wP))){case 0:return true;case 1:var _1wS=E(_1wN),_1wT=E(_1wQ);switch(B(_1kC(_1wS.a,_1wS.b,_1wS.c,_1wS.d,_1wT.a,_1wT.b,_1wT.c,_1wT.d))){case 0:return true;case 1:return new F(function(){return _1wH(_1wO,_1wR);});break;default:return false;}break;default:return false;}},_1wU=function(_1wV,_1wW){var _1wX=E(_1wV),_1wY=E(_1wW);return new F(function(){return _1wL(_1wX.a,_1wX.b,_1wX.c,_1wY.a,_1wY.b,_1wY.c);});},_1wZ=function(_1x0,_1x1,_1x2,_1x3,_1x4,_1x5){switch(B(A3(_1lg,_1v6,_1x0,_1x3))){case 0:return 0;case 1:var _1x6=E(_1x1),_1x7=E(_1x4);switch(B(_1kC(_1x6.a,_1x6.b,_1x6.c,_1x6.d,_1x7.a,_1x7.b,_1x7.c,_1x7.d))){case 0:return 0;case 1:return new F(function(){return _1x8(_1x2,_1x5);});break;default:return 2;}break;default:return 2;}},_1x9=function(_1xa,_1xb){var _1xc=E(_1xa),_1xd=E(_1xb);return new F(function(){return _1wZ(_1xc.a,_1xc.b,_1xc.c,_1xd.a,_1xd.b,_1xd.c);});},_1ux=new T(function(){return {_:0,a:_1rI,b:_1x9,c:_1wU,d:_1w6,e:_1vG,f:_1vg,g:_1wb,h:_1wn};}),_1xe=function(_1xf,_1xg,_1xh,_1xi){var _1xj=E(_1xi);switch(B(_1uk(_1ux,_1xf,_1xj.a))){case 0:return 0;case 1:var _1xk=E(_1xg),_1xl=E(_1xj.b);switch(B(_1kC(_1xk.a,_1xk.b,_1xk.c,_1xk.d,_1xl.a,_1xl.b,_1xl.c,_1xl.d))){case 0:return 0;case 1:return new F(function(){return _1uk(_1uj,_1xh,_1xj.c);});break;default:return 2;}break;default:return 2;}},_1x8=function(_1xm,_1xn){var _1xo=E(_1xm);return new F(function(){return _1xe(_1xo.a,_1xo.b,_1xo.c,_1xn);});},_1xp=function(_1xq,_1xr){var _1xs=E(_1xq),_1xt=E(_1xr);return new F(function(){return _1kC(_1xs.a,_1xs.b,_1xs.c,_1xs.d,_1xt.a,_1xt.b,_1xt.c,_1xt.d);});},_1u2=function(_1xu,_1xv){while(1){var _1xw=B((function(_1xx,_1xy){var _1xz=E(_1xx);switch(_1xz._){case 0:var _1xA=E(_1xy);if(!_1xA._){var _1xB=_1xA.a,_1xC=function(_1xD){var _1xE=E(_1xz.b),_1xF=E(_1xA.b);switch(B(_1kC(_1xE.a,_1xE.b,_1xE.c,_1xE.d,_1xF.a,_1xF.b,_1xF.c,_1xF.d))){case 0:return 0;case 1:return new F(function(){return _1u2(_1xz.c,_1xA.c);});break;default:return 2;}};if(!E(_1xz.a)){if(!E(_1xB)){return new F(function(){return _1xC(_);});}else{return 0;}}else{if(!E(_1xB)){return 2;}else{return new F(function(){return _1xC(_);});}}}else{return 0;}break;case 1:var _1xG=E(_1xy);switch(_1xG._){case 0:return 2;case 1:switch(B(_1u2(_1xz.a,_1xG.a))){case 0:return 0;case 1:_1xu=_1xz.b;_1xv=_1xG.b;return __continue;default:return 2;}break;default:return 0;}break;case 2:var _1xH=E(_1xy);switch(_1xH._){case 2:return new F(function(){return _1tS(_1xz.a,_1xH.a);});break;case 3:return 0;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 3:var _1xI=E(_1xy);switch(_1xI._){case 3:return new F(function(){return _gZ(_1xz.a,_1xI.a);});break;case 4:return 0;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 4:var _1xJ=E(_1xy);switch(_1xJ._){case 4:return new F(function(){return _1xp(_1xz.a,_1xJ.a);});break;case 5:return 0;case 6:return 0;case 7:return 0;default:return 2;}break;case 5:var _1xK=E(_1xy);switch(_1xK._){case 5:return new F(function(){return _gZ(_1xz.a,_1xK.a);});break;case 6:return 0;case 7:return 0;default:return 2;}break;case 6:var _1xL=E(_1xy);switch(_1xL._){case 6:switch(B(_1u2(_1xz.a,_1xL.a))){case 0:return 0;case 1:return new F(function(){return _1x8(_1xz.b,_1xL.b);});break;default:return 2;}break;case 7:return 0;default:return 2;}break;default:var _1xM=E(_1xy);if(_1xM._==7){_1xu=_1xz.a;_1xv=_1xM.a;return __continue;}else{return 2;}}})(_1xu,_1xv));if(_1xw!=__continue){return _1xw;}}},_1xN=function(_1xO,_1xP,_1xQ,_1xR){if(_1xO>=_1xQ){if(_1xO!=_1xQ){return 2;}else{return new F(function(){return _h2(_1xP,_1xR);});}}else{return 0;}},_1xS=function(_1xT,_1xU){var _1xV=E(_1xT),_1xW=E(_1xU);return new F(function(){return _1xN(E(_1xV.a),_1xV.b,E(_1xW.a),_1xW.b);});},_1xX=function(_1xY,_1xZ,_1y0,_1y1){if(_1xY>=_1y0){if(_1xY!=_1y0){return false;}else{return new F(function(){return _he(_1xZ,_1y1);});}}else{return true;}},_1y2=function(_1y3,_1y4){var _1y5=E(_1y3),_1y6=E(_1y4);return new F(function(){return _1xX(E(_1y5.a),_1y5.b,E(_1y6.a),_1y6.b);});},_1y7=function(_1y8,_1y9,_1ya,_1yb){if(_1y8>=_1ya){if(_1y8!=_1ya){return false;}else{return new F(function(){return _hb(_1y9,_1yb);});}}else{return true;}},_1yc=function(_1yd,_1ye){var _1yf=E(_1yd),_1yg=E(_1ye);return new F(function(){return _1y7(E(_1yf.a),_1yf.b,E(_1yg.a),_1yg.b);});},_1yh=function(_1yi,_1yj,_1yk,_1yl){if(_1yi>=_1yk){if(_1yi!=_1yk){return true;}else{return new F(function(){return _h8(_1yj,_1yl);});}}else{return false;}},_1ym=function(_1yn,_1yo){var _1yp=E(_1yn),_1yq=E(_1yo);return new F(function(){return _1yh(E(_1yp.a),_1yp.b,E(_1yq.a),_1yq.b);});},_1yr=function(_1ys,_1yt,_1yu,_1yv){if(_1ys>=_1yu){if(_1ys!=_1yu){return true;}else{return new F(function(){return _h5(_1yt,_1yv);});}}else{return false;}},_1yw=function(_1yx,_1yy){var _1yz=E(_1yx),_1yA=E(_1yy);return new F(function(){return _1yr(E(_1yz.a),_1yz.b,E(_1yA.a),_1yA.b);});},_1yB=function(_1yC,_1yD){var _1yE=E(_1yC),_1yF=E(_1yE.a),_1yG=E(_1yD),_1yH=E(_1yG.a);return (_1yF>=_1yH)?(_1yF!=_1yH)?E(_1yE):(E(_1yE.b)>E(_1yG.b))?E(_1yE):E(_1yG):E(_1yG);},_1yI=function(_1yJ,_1yK){var _1yL=E(_1yJ),_1yM=E(_1yL.a),_1yN=E(_1yK),_1yO=E(_1yN.a);return (_1yM>=_1yO)?(_1yM!=_1yO)?E(_1yN):(E(_1yL.b)>E(_1yN.b))?E(_1yN):E(_1yL):E(_1yL);},_1yP={_:0,a:_1t2,b:_1xS,c:_1y2,d:_1yc,e:_1ym,f:_1yw,g:_1yB,h:_1yI},_1yQ=function(_1yR,_1yS,_1yT,_1yU){switch(B(_1uk(_1yP,_1yR,_1yT))){case 0:return true;case 1:return _1yS<_1yU;default:return false;}},_1yV=function(_1yW,_1yX){var _1yY=E(_1yW),_1yZ=E(_1yX);return new F(function(){return _1yQ(_1yY.a,_1yY.b,_1yZ.a,_1yZ.b);});},_1z0=function(_1z1,_1z2,_1z3,_1z4){switch(B(_1uk(_1yP,_1z1,_1z3))){case 0:return true;case 1:return _1z2<=_1z4;default:return false;}},_1z5=function(_1z6,_1z7){var _1z8=E(_1z6),_1z9=E(_1z7);return new F(function(){return _1z0(_1z8.a,_1z8.b,_1z9.a,_1z9.b);});},_1za=function(_1zb,_1zc,_1zd,_1ze){switch(B(_1uk(_1yP,_1zb,_1zd))){case 0:return false;case 1:return _1zc>_1ze;default:return true;}},_1zf=function(_1zg,_1zh){var _1zi=E(_1zg),_1zj=E(_1zh);return new F(function(){return _1za(_1zi.a,_1zi.b,_1zj.a,_1zj.b);});},_1zk=function(_1zl,_1zm,_1zn,_1zo){switch(B(_1uk(_1yP,_1zl,_1zn))){case 0:return false;case 1:return _1zm>=_1zo;default:return true;}},_1zp=function(_1zq,_1zr){var _1zs=E(_1zq),_1zt=E(_1zr);return new F(function(){return _1zk(_1zs.a,_1zs.b,_1zt.a,_1zt.b);});},_1zu=function(_1zv,_1zw,_1zx,_1zy){switch(B(_1uk(_1yP,_1zv,_1zx))){case 0:return 0;case 1:return new F(function(){return _gZ(_1zw,_1zy);});break;default:return 2;}},_1zz=function(_1zA,_1zB){var _1zC=E(_1zA),_1zD=E(_1zB);return new F(function(){return _1zu(_1zC.a,_1zC.b,_1zD.a,_1zD.b);});},_1zE=function(_1zF,_1zG){var _1zH=E(_1zF),_1zI=E(_1zG);switch(B(_1uk(_1yP,_1zH.a,_1zI.a))){case 0:return E(_1zI);case 1:return (_1zH.b>_1zI.b)?E(_1zH):E(_1zI);default:return E(_1zH);}},_1zJ=function(_1zK,_1zL){var _1zM=E(_1zK),_1zN=E(_1zL);switch(B(_1uk(_1yP,_1zM.a,_1zN.a))){case 0:return E(_1zM);case 1:return (_1zM.b>_1zN.b)?E(_1zN):E(_1zM);default:return E(_1zN);}},_1zO={_:0,a:_1ti,b:_1zz,c:_1yV,d:_1z5,e:_1zf,f:_1zp,g:_1zE,h:_1zJ},_1zP=function(_1zQ,_1zR){while(1){var _1zS=E(_1zQ);if(!_1zS._){return (E(_1zR)._==0)?1:0;}else{var _1zT=E(_1zR);if(!_1zT._){return 2;}else{var _1zU=B(_1kc(_1zS.a,_1zT.a));if(_1zU==1){_1zQ=_1zS.b;_1zR=_1zT.b;continue;}else{return E(_1zU);}}}}},_1zV=function(_1zW,_1zX){return (B(_1zP(_1zW,_1zX))==0)?true:false;},_1zY=function(_1zZ,_1A0){var _1A1=E(_1zZ);switch(_1A1._){case 0:var _1A2=_1A1.a,_1A3=E(_1A0);if(!_1A3._){var _1A4=_1A3.a;return (_1A2>=_1A4)?(_1A2!=_1A4)?false:(B(_1uk(_1zO,_1A1.b,_1A3.b))==0)?true:false:true;}else{return true;}break;case 1:var _1A5=E(_1A0);switch(_1A5._){case 0:return false;case 1:return _1A1.a<_1A5.a;default:return true;}break;default:var _1A6=E(_1A0);if(_1A6._==2){var _1A7=E(_1A1.a),_1A8=E(_1A6.a);switch(B(_1kC(_1A7.a,_1A7.b,_1A7.c,_1A7.d,_1A8.a,_1A8.b,_1A8.c,_1A8.d))){case 0:return true;case 1:switch(B(_1u2(_1A1.b,_1A6.b))){case 0:return true;case 1:return new F(function(){return _1zV(_1A1.c,_1A6.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1A9=function(_1Aa,_1Ab){return (B(_1zP(_1Aa,_1Ab))==2)?false:true;},_1Ac=function(_1Ad,_1Ae){var _1Af=E(_1Ad);switch(_1Af._){case 0:var _1Ag=_1Af.a,_1Ah=E(_1Ae);if(!_1Ah._){var _1Ai=_1Ah.a;return (_1Ag>=_1Ai)?(_1Ag!=_1Ai)?false:(B(_1uk(_1zO,_1Af.b,_1Ah.b))==2)?false:true:true;}else{return true;}break;case 1:var _1Aj=E(_1Ae);switch(_1Aj._){case 0:return false;case 1:return _1Af.a<=_1Aj.a;default:return true;}break;default:var _1Ak=E(_1Ae);if(_1Ak._==2){var _1Al=E(_1Af.a),_1Am=E(_1Ak.a);switch(B(_1kC(_1Al.a,_1Al.b,_1Al.c,_1Al.d,_1Am.a,_1Am.b,_1Am.c,_1Am.d))){case 0:return true;case 1:switch(B(_1u2(_1Af.b,_1Ak.b))){case 0:return true;case 1:return new F(function(){return _1A9(_1Af.c,_1Ak.c);});break;default:return false;}break;default:return false;}}else{return false;}}},_1An=function(_1Ao,_1Ap){return (B(_1zP(_1Ao,_1Ap))==2)?true:false;},_1Aq=function(_1Ar,_1As){var _1At=E(_1Ar);switch(_1At._){case 0:var _1Au=_1At.a,_1Av=E(_1As);if(!_1Av._){var _1Aw=_1Av.a;return (_1Au>=_1Aw)?(_1Au!=_1Aw)?true:(B(_1uk(_1zO,_1At.b,_1Av.b))==2)?true:false:false;}else{return false;}break;case 1:var _1Ax=E(_1As);switch(_1Ax._){case 0:return true;case 1:return _1At.a>_1Ax.a;default:return false;}break;default:var _1Ay=E(_1As);if(_1Ay._==2){var _1Az=E(_1At.a),_1AA=E(_1Ay.a);switch(B(_1kC(_1Az.a,_1Az.b,_1Az.c,_1Az.d,_1AA.a,_1AA.b,_1AA.c,_1AA.d))){case 0:return false;case 1:switch(B(_1u2(_1At.b,_1Ay.b))){case 0:return false;case 1:return new F(function(){return _1An(_1At.c,_1Ay.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1AB=function(_1AC,_1AD){return (B(_1zP(_1AC,_1AD))==0)?false:true;},_1AE=function(_1AF,_1AG){var _1AH=E(_1AF);switch(_1AH._){case 0:var _1AI=_1AH.a,_1AJ=E(_1AG);if(!_1AJ._){var _1AK=_1AJ.a;return (_1AI>=_1AK)?(_1AI!=_1AK)?true:(B(_1uk(_1zO,_1AH.b,_1AJ.b))==0)?false:true:false;}else{return false;}break;case 1:var _1AL=E(_1AG);switch(_1AL._){case 0:return true;case 1:return _1AH.a>=_1AL.a;default:return false;}break;default:var _1AM=E(_1AG);if(_1AM._==2){var _1AN=E(_1AH.a),_1AO=E(_1AM.a);switch(B(_1kC(_1AN.a,_1AN.b,_1AN.c,_1AN.d,_1AO.a,_1AO.b,_1AO.c,_1AO.d))){case 0:return false;case 1:switch(B(_1u2(_1AH.b,_1AM.b))){case 0:return false;case 1:return new F(function(){return _1AB(_1AH.c,_1AM.c);});break;default:return true;}break;default:return true;}}else{return true;}}},_1AP=function(_1AQ,_1AR){var _1AS=E(_1AQ);switch(_1AS._){case 0:var _1AT=_1AS.a,_1AU=E(_1AR);if(!_1AU._){var _1AV=_1AU.a;if(_1AT>=_1AV){if(_1AT!=_1AV){return 2;}else{return new F(function(){return _1uk(_1zO,_1AS.b,_1AU.b);});}}else{return 0;}}else{return 0;}break;case 1:var _1AW=E(_1AR);switch(_1AW._){case 0:return 2;case 1:return new F(function(){return _gZ(_1AS.a,_1AW.a);});break;default:return 0;}break;default:var _1AX=E(_1AR);if(_1AX._==2){var _1AY=E(_1AS.a),_1AZ=E(_1AX.a);switch(B(_1kC(_1AY.a,_1AY.b,_1AY.c,_1AY.d,_1AZ.a,_1AZ.b,_1AZ.c,_1AZ.d))){case 0:return 0;case 1:switch(B(_1u2(_1AS.b,_1AX.b))){case 0:return 0;case 1:return new F(function(){return _1zP(_1AS.c,_1AX.c);});break;default:return 2;}break;default:return 2;}}else{return 2;}}},_1B0=function(_1B1,_1B2){return (!B(_1Ac(_1B1,_1B2)))?E(_1B1):E(_1B2);},_1B3=function(_1B4,_1B5){return (!B(_1Ac(_1B4,_1B5)))?E(_1B5):E(_1B4);},_1B6={_:0,a:_1tM,b:_1AP,c:_1zY,d:_1Ac,e:_1Aq,f:_1AE,g:_1B0,h:_1B3},_1B7=__Z,_1B8=function(_1B9,_1Ba,_1Bb){var _1Bc=E(_1Ba);if(!_1Bc._){return E(_1Bb);}else{var _1Bd=function(_1Be,_1Bf){while(1){var _1Bg=E(_1Bf);if(!_1Bg._){var _1Bh=_1Bg.b,_1Bi=_1Bg.d;switch(B(A3(_1lg,_1B9,_1Be,_1Bh))){case 0:return new F(function(){return _RN(_1Bh,B(_1Bd(_1Be,_1Bg.c)),_1Bi);});break;case 1:return E(_1Bi);default:_1Bf=_1Bi;continue;}}else{return new T0(1);}}};return new F(function(){return _1Bd(_1Bc.a,_1Bb);});}},_1Bj=function(_1Bk,_1Bl,_1Bm){var _1Bn=E(_1Bl);if(!_1Bn._){return E(_1Bm);}else{var _1Bo=function(_1Bp,_1Bq){while(1){var _1Br=E(_1Bq);if(!_1Br._){var _1Bs=_1Br.b,_1Bt=_1Br.c;switch(B(A3(_1lg,_1Bk,_1Bs,_1Bp))){case 0:return new F(function(){return _RN(_1Bs,_1Bt,B(_1Bo(_1Bp,_1Br.d)));});break;case 1:return E(_1Bt);default:_1Bq=_1Bt;continue;}}else{return new T0(1);}}};return new F(function(){return _1Bo(_1Bn.a,_1Bm);});}},_1Bu=function(_1Bv,_1Bw,_1Bx){var _1By=E(_1Bw),_1Bz=E(_1Bx);if(!_1Bz._){var _1BA=_1Bz.b,_1BB=_1Bz.c,_1BC=_1Bz.d;switch(B(A3(_1lg,_1Bv,_1By,_1BA))){case 0:return new F(function(){return _PR(_1BA,B(_1Bu(_1Bv,_1By,_1BB)),_1BC);});break;case 1:return E(_1Bz);default:return new F(function(){return _Qt(_1BA,_1BB,B(_1Bu(_1Bv,_1By,_1BC)));});}}else{return new T4(0,1,E(_1By),E(_PM),E(_PM));}},_1BD=function(_1BE,_1BF,_1BG){return new F(function(){return _1Bu(_1BE,_1BF,_1BG);});},_1BH=function(_1BI,_1BJ,_1BK,_1BL){var _1BM=E(_1BJ);if(!_1BM._){var _1BN=E(_1BK);if(!_1BN._){return E(_1BL);}else{var _1BO=function(_1BP,_1BQ){while(1){var _1BR=E(_1BQ);if(!_1BR._){if(!B(A3(_1oi,_1BI,_1BR.b,_1BP))){return E(_1BR);}else{_1BQ=_1BR.c;continue;}}else{return new T0(1);}}};return new F(function(){return _1BO(_1BN.a,_1BL);});}}else{var _1BS=_1BM.a,_1BT=E(_1BK);if(!_1BT._){var _1BU=function(_1BV,_1BW){while(1){var _1BX=E(_1BW);if(!_1BX._){if(!B(A3(_1p1,_1BI,_1BX.b,_1BV))){return E(_1BX);}else{_1BW=_1BX.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1BU(_1BS,_1BL);});}else{var _1BY=function(_1BZ,_1C0,_1C1){while(1){var _1C2=E(_1C1);if(!_1C2._){var _1C3=_1C2.b;if(!B(A3(_1p1,_1BI,_1C3,_1BZ))){if(!B(A3(_1oi,_1BI,_1C3,_1C0))){return E(_1C2);}else{_1C1=_1C2.c;continue;}}else{_1C1=_1C2.d;continue;}}else{return new T0(1);}}};return new F(function(){return _1BY(_1BS,_1BT.a,_1BL);});}}},_1C4=function(_1C5,_1C6,_1C7,_1C8,_1C9){var _1Ca=E(_1C9);if(!_1Ca._){var _1Cb=_1Ca.b,_1Cc=_1Ca.c,_1Cd=_1Ca.d,_1Ce=E(_1C8);if(!_1Ce._){var _1Cf=_1Ce.b,_1Cg=function(_1Ch){var _1Ci=new T1(1,E(_1Cf));return new F(function(){return _RN(_1Cf,B(_1C4(_1C5,_1C6,_1Ci,_1Ce.c,B(_1BH(_1C5,_1C6,_1Ci,_1Ca)))),B(_1C4(_1C5,_1Ci,_1C7,_1Ce.d,B(_1BH(_1C5,_1Ci,_1C7,_1Ca)))));});};if(!E(_1Cc)._){return new F(function(){return _1Cg(_);});}else{if(!E(_1Cd)._){return new F(function(){return _1Cg(_);});}else{return new F(function(){return _1BD(_1C5,_1Cb,_1Ce);});}}}else{return new F(function(){return _RN(_1Cb,B(_1B8(_1C5,_1C6,_1Cc)),B(_1Bj(_1C5,_1C7,_1Cd)));});}}else{return E(_1C8);}},_1Cj=function(_1Ck,_1Cl,_1Cm,_1Cn,_1Co,_1Cp,_1Cq,_1Cr,_1Cs,_1Ct,_1Cu){var _1Cv=function(_1Cw){var _1Cx=new T1(1,E(_1Co));return new F(function(){return _RN(_1Co,B(_1C4(_1Ck,_1Cl,_1Cx,_1Cp,B(_1BH(_1Ck,_1Cl,_1Cx,new T4(0,_1Cr,E(_1Cs),E(_1Ct),E(_1Cu)))))),B(_1C4(_1Ck,_1Cx,_1Cm,_1Cq,B(_1BH(_1Ck,_1Cx,_1Cm,new T4(0,_1Cr,E(_1Cs),E(_1Ct),E(_1Cu)))))));});};if(!E(_1Ct)._){return new F(function(){return _1Cv(_);});}else{if(!E(_1Cu)._){return new F(function(){return _1Cv(_);});}else{return new F(function(){return _1BD(_1Ck,_1Cs,new T4(0,_1Cn,E(_1Co),E(_1Cp),E(_1Cq)));});}}},_1Cy=function(_1Cz,_1CA,_1CB){var _1CC=E(_1CA);if(!_1CC._){var _1CD=E(_1CB);if(!_1CD._){return new F(function(){return _1Cj(_1B6,_1B7,_1B7,_1CC.a,_1CC.b,_1CC.c,_1CC.d,_1CD.a,_1CD.b,_1CD.c,_1CD.d);});}else{return E(_1CC);}}else{return E(_1CB);}},_1CE=function(_1CF,_1CG,_1CH){var _1CI=function(_1CJ,_1CK,_1CL,_1CM){var _1CN=E(_1CM);switch(_1CN._){case 0:var _1CO=_1CN.a,_1CP=_1CN.b,_1CQ=_1CN.c,_1CR=_1CN.d,_1CS=_1CP>>>0;if(((_1CL>>>0&((_1CS-1>>>0^4294967295)>>>0^_1CS)>>>0)>>>0&4294967295)==_1CO){return ((_1CL>>>0&_1CS)>>>0==0)?new T4(0,_1CO,_1CP,E(B(_1CI(_1CJ,_1CK,_1CL,_1CQ))),E(_1CR)):new T4(0,_1CO,_1CP,E(_1CQ),E(B(_1CI(_1CJ,_1CK,_1CL,_1CR))));}else{var _1CT=(_1CL>>>0^_1CO>>>0)>>>0,_1CU=(_1CT|_1CT>>>1)>>>0,_1CV=(_1CU|_1CU>>>2)>>>0,_1CW=(_1CV|_1CV>>>4)>>>0,_1CX=(_1CW|_1CW>>>8)>>>0,_1CY=(_1CX|_1CX>>>16)>>>0,_1CZ=(_1CY^_1CY>>>1)>>>0&4294967295,_1D0=_1CZ>>>0;return ((_1CL>>>0&_1D0)>>>0==0)?new T4(0,(_1CL>>>0&((_1D0-1>>>0^4294967295)>>>0^_1D0)>>>0)>>>0&4294967295,_1CZ,E(new T2(1,_1CJ,_1CK)),E(_1CN)):new T4(0,(_1CL>>>0&((_1D0-1>>>0^4294967295)>>>0^_1D0)>>>0)>>>0&4294967295,_1CZ,E(_1CN),E(new T2(1,_1CJ,_1CK)));}break;case 1:var _1D1=_1CN.a;if(_1CL!=_1D1){var _1D2=(_1CL>>>0^_1D1>>>0)>>>0,_1D3=(_1D2|_1D2>>>1)>>>0,_1D4=(_1D3|_1D3>>>2)>>>0,_1D5=(_1D4|_1D4>>>4)>>>0,_1D6=(_1D5|_1D5>>>8)>>>0,_1D7=(_1D6|_1D6>>>16)>>>0,_1D8=(_1D7^_1D7>>>1)>>>0&4294967295,_1D9=_1D8>>>0;return ((_1CL>>>0&_1D9)>>>0==0)?new T4(0,(_1CL>>>0&((_1D9-1>>>0^4294967295)>>>0^_1D9)>>>0)>>>0&4294967295,_1D8,E(new T2(1,_1CJ,_1CK)),E(_1CN)):new T4(0,(_1CL>>>0&((_1D9-1>>>0^4294967295)>>>0^_1D9)>>>0)>>>0&4294967295,_1D8,E(_1CN),E(new T2(1,_1CJ,_1CK)));}else{return new T2(1,_1CJ,new T(function(){return B(A3(_1CF,_1CJ,_1CK,_1CN.b));}));}break;default:return new T2(1,_1CJ,_1CK);}},_1Da=function(_1Db,_1Dc,_1Dd,_1De){var _1Df=E(_1De);switch(_1Df._){case 0:var _1Dg=_1Df.a,_1Dh=_1Df.b,_1Di=_1Df.c,_1Dj=_1Df.d,_1Dk=_1Dh>>>0;if(((_1Dd>>>0&((_1Dk-1>>>0^4294967295)>>>0^_1Dk)>>>0)>>>0&4294967295)==_1Dg){return ((_1Dd>>>0&_1Dk)>>>0==0)?new T4(0,_1Dg,_1Dh,E(B(_1Da(_1Db,_1Dc,_1Dd,_1Di))),E(_1Dj)):new T4(0,_1Dg,_1Dh,E(_1Di),E(B(_1Da(_1Db,_1Dc,_1Dd,_1Dj))));}else{var _1Dl=(_1Dg>>>0^_1Dd>>>0)>>>0,_1Dm=(_1Dl|_1Dl>>>1)>>>0,_1Dn=(_1Dm|_1Dm>>>2)>>>0,_1Do=(_1Dn|_1Dn>>>4)>>>0,_1Dp=(_1Do|_1Do>>>8)>>>0,_1Dq=(_1Dp|_1Dp>>>16)>>>0,_1Dr=(_1Dq^_1Dq>>>1)>>>0&4294967295,_1Ds=_1Dr>>>0;return ((_1Dg>>>0&_1Ds)>>>0==0)?new T4(0,(_1Dg>>>0&((_1Ds-1>>>0^4294967295)>>>0^_1Ds)>>>0)>>>0&4294967295,_1Dr,E(_1Df),E(new T2(1,_1Db,_1Dc))):new T4(0,(_1Dg>>>0&((_1Ds-1>>>0^4294967295)>>>0^_1Ds)>>>0)>>>0&4294967295,_1Dr,E(new T2(1,_1Db,_1Dc)),E(_1Df));}break;case 1:var _1Dt=_1Df.a;if(_1Dt!=_1Dd){var _1Du=(_1Dt>>>0^_1Dd>>>0)>>>0,_1Dv=(_1Du|_1Du>>>1)>>>0,_1Dw=(_1Dv|_1Dv>>>2)>>>0,_1Dx=(_1Dw|_1Dw>>>4)>>>0,_1Dy=(_1Dx|_1Dx>>>8)>>>0,_1Dz=(_1Dy|_1Dy>>>16)>>>0,_1DA=(_1Dz^_1Dz>>>1)>>>0&4294967295,_1DB=_1DA>>>0;return ((_1Dt>>>0&_1DB)>>>0==0)?new T4(0,(_1Dt>>>0&((_1DB-1>>>0^4294967295)>>>0^_1DB)>>>0)>>>0&4294967295,_1DA,E(_1Df),E(new T2(1,_1Db,_1Dc))):new T4(0,(_1Dt>>>0&((_1DB-1>>>0^4294967295)>>>0^_1DB)>>>0)>>>0&4294967295,_1DA,E(new T2(1,_1Db,_1Dc)),E(_1Df));}else{return new T2(1,_1Dt,new T(function(){return B(A3(_1CF,_1Dt,_1Df.b,_1Dc));}));}break;default:return new T2(1,_1Db,_1Dc);}},_1DC=function(_1DD,_1DE,_1DF,_1DG,_1DH,_1DI,_1DJ){var _1DK=_1DH>>>0;if(((_1DF>>>0&((_1DK-1>>>0^4294967295)>>>0^_1DK)>>>0)>>>0&4294967295)==_1DG){return ((_1DF>>>0&_1DK)>>>0==0)?new T4(0,_1DG,_1DH,E(B(_1Da(_1DD,_1DE,_1DF,_1DI))),E(_1DJ)):new T4(0,_1DG,_1DH,E(_1DI),E(B(_1Da(_1DD,_1DE,_1DF,_1DJ))));}else{var _1DL=(_1DG>>>0^_1DF>>>0)>>>0,_1DM=(_1DL|_1DL>>>1)>>>0,_1DN=(_1DM|_1DM>>>2)>>>0,_1DO=(_1DN|_1DN>>>4)>>>0,_1DP=(_1DO|_1DO>>>8)>>>0,_1DQ=(_1DP|_1DP>>>16)>>>0,_1DR=(_1DQ^_1DQ>>>1)>>>0&4294967295,_1DS=_1DR>>>0;return ((_1DG>>>0&_1DS)>>>0==0)?new T4(0,(_1DG>>>0&((_1DS-1>>>0^4294967295)>>>0^_1DS)>>>0)>>>0&4294967295,_1DR,E(new T4(0,_1DG,_1DH,E(_1DI),E(_1DJ))),E(new T2(1,_1DD,_1DE))):new T4(0,(_1DG>>>0&((_1DS-1>>>0^4294967295)>>>0^_1DS)>>>0)>>>0&4294967295,_1DR,E(new T2(1,_1DD,_1DE)),E(new T4(0,_1DG,_1DH,E(_1DI),E(_1DJ))));}},_1DT=function(_1DU,_1DV){var _1DW=E(_1DU);switch(_1DW._){case 0:var _1DX=_1DW.a,_1DY=_1DW.b,_1DZ=_1DW.c,_1E0=_1DW.d,_1E1=E(_1DV);switch(_1E1._){case 0:var _1E2=_1E1.a,_1E3=_1E1.b,_1E4=_1E1.c,_1E5=_1E1.d;if(_1DY>>>0<=_1E3>>>0){if(_1E3>>>0<=_1DY>>>0){if(_1DX!=_1E2){var _1E6=(_1DX>>>0^_1E2>>>0)>>>0,_1E7=(_1E6|_1E6>>>1)>>>0,_1E8=(_1E7|_1E7>>>2)>>>0,_1E9=(_1E8|_1E8>>>4)>>>0,_1Ea=(_1E9|_1E9>>>8)>>>0,_1Eb=(_1Ea|_1Ea>>>16)>>>0,_1Ec=(_1Eb^_1Eb>>>1)>>>0&4294967295,_1Ed=_1Ec>>>0;return ((_1DX>>>0&_1Ed)>>>0==0)?new T4(0,(_1DX>>>0&((_1Ed-1>>>0^4294967295)>>>0^_1Ed)>>>0)>>>0&4294967295,_1Ec,E(_1DW),E(_1E1)):new T4(0,(_1DX>>>0&((_1Ed-1>>>0^4294967295)>>>0^_1Ed)>>>0)>>>0&4294967295,_1Ec,E(_1E1),E(_1DW));}else{return new T4(0,_1DX,_1DY,E(B(_1DT(_1DZ,_1E4))),E(B(_1DT(_1E0,_1E5))));}}else{var _1Ee=_1E3>>>0;if(((_1DX>>>0&((_1Ee-1>>>0^4294967295)>>>0^_1Ee)>>>0)>>>0&4294967295)==_1E2){return ((_1DX>>>0&_1Ee)>>>0==0)?new T4(0,_1E2,_1E3,E(B(_1Ef(_1DX,_1DY,_1DZ,_1E0,_1E4))),E(_1E5)):new T4(0,_1E2,_1E3,E(_1E4),E(B(_1Ef(_1DX,_1DY,_1DZ,_1E0,_1E5))));}else{var _1Eg=(_1DX>>>0^_1E2>>>0)>>>0,_1Eh=(_1Eg|_1Eg>>>1)>>>0,_1Ei=(_1Eh|_1Eh>>>2)>>>0,_1Ej=(_1Ei|_1Ei>>>4)>>>0,_1Ek=(_1Ej|_1Ej>>>8)>>>0,_1El=(_1Ek|_1Ek>>>16)>>>0,_1Em=(_1El^_1El>>>1)>>>0&4294967295,_1En=_1Em>>>0;return ((_1DX>>>0&_1En)>>>0==0)?new T4(0,(_1DX>>>0&((_1En-1>>>0^4294967295)>>>0^_1En)>>>0)>>>0&4294967295,_1Em,E(_1DW),E(_1E1)):new T4(0,(_1DX>>>0&((_1En-1>>>0^4294967295)>>>0^_1En)>>>0)>>>0&4294967295,_1Em,E(_1E1),E(_1DW));}}}else{var _1Eo=_1DY>>>0;if(((_1E2>>>0&((_1Eo-1>>>0^4294967295)>>>0^_1Eo)>>>0)>>>0&4294967295)==_1DX){return ((_1E2>>>0&_1Eo)>>>0==0)?new T4(0,_1DX,_1DY,E(B(_1Ep(_1DZ,_1E2,_1E3,_1E4,_1E5))),E(_1E0)):new T4(0,_1DX,_1DY,E(_1DZ),E(B(_1Ep(_1E0,_1E2,_1E3,_1E4,_1E5))));}else{var _1Eq=(_1DX>>>0^_1E2>>>0)>>>0,_1Er=(_1Eq|_1Eq>>>1)>>>0,_1Es=(_1Er|_1Er>>>2)>>>0,_1Et=(_1Es|_1Es>>>4)>>>0,_1Eu=(_1Et|_1Et>>>8)>>>0,_1Ev=(_1Eu|_1Eu>>>16)>>>0,_1Ew=(_1Ev^_1Ev>>>1)>>>0&4294967295,_1Ex=_1Ew>>>0;return ((_1DX>>>0&_1Ex)>>>0==0)?new T4(0,(_1DX>>>0&((_1Ex-1>>>0^4294967295)>>>0^_1Ex)>>>0)>>>0&4294967295,_1Ew,E(_1DW),E(_1E1)):new T4(0,(_1DX>>>0&((_1Ex-1>>>0^4294967295)>>>0^_1Ex)>>>0)>>>0&4294967295,_1Ew,E(_1E1),E(_1DW));}}break;case 1:var _1Ey=_1E1.a;return new F(function(){return _1DC(_1Ey,_1E1.b,_1Ey,_1DX,_1DY,_1DZ,_1E0);});break;default:return E(_1DW);}break;case 1:var _1Ez=_1DW.a;return new F(function(){return _1CI(_1Ez,_1DW.b,_1Ez,_1DV);});break;default:return E(_1DV);}},_1Ef=function(_1EA,_1EB,_1EC,_1ED,_1EE){var _1EF=E(_1EE);switch(_1EF._){case 0:var _1EG=_1EF.a,_1EH=_1EF.b,_1EI=_1EF.c,_1EJ=_1EF.d;if(_1EB>>>0<=_1EH>>>0){if(_1EH>>>0<=_1EB>>>0){if(_1EA!=_1EG){var _1EK=(_1EA>>>0^_1EG>>>0)>>>0,_1EL=(_1EK|_1EK>>>1)>>>0,_1EM=(_1EL|_1EL>>>2)>>>0,_1EN=(_1EM|_1EM>>>4)>>>0,_1EO=(_1EN|_1EN>>>8)>>>0,_1EP=(_1EO|_1EO>>>16)>>>0,_1EQ=(_1EP^_1EP>>>1)>>>0&4294967295,_1ER=_1EQ>>>0;return ((_1EA>>>0&_1ER)>>>0==0)?new T4(0,(_1EA>>>0&((_1ER-1>>>0^4294967295)>>>0^_1ER)>>>0)>>>0&4294967295,_1EQ,E(new T4(0,_1EA,_1EB,E(_1EC),E(_1ED))),E(_1EF)):new T4(0,(_1EA>>>0&((_1ER-1>>>0^4294967295)>>>0^_1ER)>>>0)>>>0&4294967295,_1EQ,E(_1EF),E(new T4(0,_1EA,_1EB,E(_1EC),E(_1ED))));}else{return new T4(0,_1EA,_1EB,E(B(_1DT(_1EC,_1EI))),E(B(_1DT(_1ED,_1EJ))));}}else{var _1ES=_1EH>>>0;if(((_1EA>>>0&((_1ES-1>>>0^4294967295)>>>0^_1ES)>>>0)>>>0&4294967295)==_1EG){return ((_1EA>>>0&_1ES)>>>0==0)?new T4(0,_1EG,_1EH,E(B(_1Ef(_1EA,_1EB,_1EC,_1ED,_1EI))),E(_1EJ)):new T4(0,_1EG,_1EH,E(_1EI),E(B(_1Ef(_1EA,_1EB,_1EC,_1ED,_1EJ))));}else{var _1ET=(_1EA>>>0^_1EG>>>0)>>>0,_1EU=(_1ET|_1ET>>>1)>>>0,_1EV=(_1EU|_1EU>>>2)>>>0,_1EW=(_1EV|_1EV>>>4)>>>0,_1EX=(_1EW|_1EW>>>8)>>>0,_1EY=(_1EX|_1EX>>>16)>>>0,_1EZ=(_1EY^_1EY>>>1)>>>0&4294967295,_1F0=_1EZ>>>0;return ((_1EA>>>0&_1F0)>>>0==0)?new T4(0,(_1EA>>>0&((_1F0-1>>>0^4294967295)>>>0^_1F0)>>>0)>>>0&4294967295,_1EZ,E(new T4(0,_1EA,_1EB,E(_1EC),E(_1ED))),E(_1EF)):new T4(0,(_1EA>>>0&((_1F0-1>>>0^4294967295)>>>0^_1F0)>>>0)>>>0&4294967295,_1EZ,E(_1EF),E(new T4(0,_1EA,_1EB,E(_1EC),E(_1ED))));}}}else{var _1F1=_1EB>>>0;if(((_1EG>>>0&((_1F1-1>>>0^4294967295)>>>0^_1F1)>>>0)>>>0&4294967295)==_1EA){return ((_1EG>>>0&_1F1)>>>0==0)?new T4(0,_1EA,_1EB,E(B(_1Ep(_1EC,_1EG,_1EH,_1EI,_1EJ))),E(_1ED)):new T4(0,_1EA,_1EB,E(_1EC),E(B(_1Ep(_1ED,_1EG,_1EH,_1EI,_1EJ))));}else{var _1F2=(_1EA>>>0^_1EG>>>0)>>>0,_1F3=(_1F2|_1F2>>>1)>>>0,_1F4=(_1F3|_1F3>>>2)>>>0,_1F5=(_1F4|_1F4>>>4)>>>0,_1F6=(_1F5|_1F5>>>8)>>>0,_1F7=(_1F6|_1F6>>>16)>>>0,_1F8=(_1F7^_1F7>>>1)>>>0&4294967295,_1F9=_1F8>>>0;return ((_1EA>>>0&_1F9)>>>0==0)?new T4(0,(_1EA>>>0&((_1F9-1>>>0^4294967295)>>>0^_1F9)>>>0)>>>0&4294967295,_1F8,E(new T4(0,_1EA,_1EB,E(_1EC),E(_1ED))),E(_1EF)):new T4(0,(_1EA>>>0&((_1F9-1>>>0^4294967295)>>>0^_1F9)>>>0)>>>0&4294967295,_1F8,E(_1EF),E(new T4(0,_1EA,_1EB,E(_1EC),E(_1ED))));}}break;case 1:var _1Fa=_1EF.a;return new F(function(){return _1DC(_1Fa,_1EF.b,_1Fa,_1EA,_1EB,_1EC,_1ED);});break;default:return new T4(0,_1EA,_1EB,E(_1EC),E(_1ED));}},_1Ep=function(_1Fb,_1Fc,_1Fd,_1Fe,_1Ff){var _1Fg=E(_1Fb);switch(_1Fg._){case 0:var _1Fh=_1Fg.a,_1Fi=_1Fg.b,_1Fj=_1Fg.c,_1Fk=_1Fg.d;if(_1Fi>>>0<=_1Fd>>>0){if(_1Fd>>>0<=_1Fi>>>0){if(_1Fh!=_1Fc){var _1Fl=(_1Fh>>>0^_1Fc>>>0)>>>0,_1Fm=(_1Fl|_1Fl>>>1)>>>0,_1Fn=(_1Fm|_1Fm>>>2)>>>0,_1Fo=(_1Fn|_1Fn>>>4)>>>0,_1Fp=(_1Fo|_1Fo>>>8)>>>0,_1Fq=(_1Fp|_1Fp>>>16)>>>0,_1Fr=(_1Fq^_1Fq>>>1)>>>0&4294967295,_1Fs=_1Fr>>>0;return ((_1Fh>>>0&_1Fs)>>>0==0)?new T4(0,(_1Fh>>>0&((_1Fs-1>>>0^4294967295)>>>0^_1Fs)>>>0)>>>0&4294967295,_1Fr,E(_1Fg),E(new T4(0,_1Fc,_1Fd,E(_1Fe),E(_1Ff)))):new T4(0,(_1Fh>>>0&((_1Fs-1>>>0^4294967295)>>>0^_1Fs)>>>0)>>>0&4294967295,_1Fr,E(new T4(0,_1Fc,_1Fd,E(_1Fe),E(_1Ff))),E(_1Fg));}else{return new T4(0,_1Fh,_1Fi,E(B(_1DT(_1Fj,_1Fe))),E(B(_1DT(_1Fk,_1Ff))));}}else{var _1Ft=_1Fd>>>0;if(((_1Fh>>>0&((_1Ft-1>>>0^4294967295)>>>0^_1Ft)>>>0)>>>0&4294967295)==_1Fc){return ((_1Fh>>>0&_1Ft)>>>0==0)?new T4(0,_1Fc,_1Fd,E(B(_1Ef(_1Fh,_1Fi,_1Fj,_1Fk,_1Fe))),E(_1Ff)):new T4(0,_1Fc,_1Fd,E(_1Fe),E(B(_1Ef(_1Fh,_1Fi,_1Fj,_1Fk,_1Ff))));}else{var _1Fu=(_1Fh>>>0^_1Fc>>>0)>>>0,_1Fv=(_1Fu|_1Fu>>>1)>>>0,_1Fw=(_1Fv|_1Fv>>>2)>>>0,_1Fx=(_1Fw|_1Fw>>>4)>>>0,_1Fy=(_1Fx|_1Fx>>>8)>>>0,_1Fz=(_1Fy|_1Fy>>>16)>>>0,_1FA=(_1Fz^_1Fz>>>1)>>>0&4294967295,_1FB=_1FA>>>0;return ((_1Fh>>>0&_1FB)>>>0==0)?new T4(0,(_1Fh>>>0&((_1FB-1>>>0^4294967295)>>>0^_1FB)>>>0)>>>0&4294967295,_1FA,E(_1Fg),E(new T4(0,_1Fc,_1Fd,E(_1Fe),E(_1Ff)))):new T4(0,(_1Fh>>>0&((_1FB-1>>>0^4294967295)>>>0^_1FB)>>>0)>>>0&4294967295,_1FA,E(new T4(0,_1Fc,_1Fd,E(_1Fe),E(_1Ff))),E(_1Fg));}}}else{var _1FC=_1Fi>>>0;if(((_1Fc>>>0&((_1FC-1>>>0^4294967295)>>>0^_1FC)>>>0)>>>0&4294967295)==_1Fh){return ((_1Fc>>>0&_1FC)>>>0==0)?new T4(0,_1Fh,_1Fi,E(B(_1Ep(_1Fj,_1Fc,_1Fd,_1Fe,_1Ff))),E(_1Fk)):new T4(0,_1Fh,_1Fi,E(_1Fj),E(B(_1Ep(_1Fk,_1Fc,_1Fd,_1Fe,_1Ff))));}else{var _1FD=(_1Fh>>>0^_1Fc>>>0)>>>0,_1FE=(_1FD|_1FD>>>1)>>>0,_1FF=(_1FE|_1FE>>>2)>>>0,_1FG=(_1FF|_1FF>>>4)>>>0,_1FH=(_1FG|_1FG>>>8)>>>0,_1FI=(_1FH|_1FH>>>16)>>>0,_1FJ=(_1FI^_1FI>>>1)>>>0&4294967295,_1FK=_1FJ>>>0;return ((_1Fh>>>0&_1FK)>>>0==0)?new T4(0,(_1Fh>>>0&((_1FK-1>>>0^4294967295)>>>0^_1FK)>>>0)>>>0&4294967295,_1FJ,E(_1Fg),E(new T4(0,_1Fc,_1Fd,E(_1Fe),E(_1Ff)))):new T4(0,(_1Fh>>>0&((_1FK-1>>>0^4294967295)>>>0^_1FK)>>>0)>>>0&4294967295,_1FJ,E(new T4(0,_1Fc,_1Fd,E(_1Fe),E(_1Ff))),E(_1Fg));}}break;case 1:var _1FL=_1Fg.a,_1FM=_1Fg.b,_1FN=_1Fd>>>0;if(((_1FL>>>0&((_1FN-1>>>0^4294967295)>>>0^_1FN)>>>0)>>>0&4294967295)==_1Fc){return ((_1FL>>>0&_1FN)>>>0==0)?new T4(0,_1Fc,_1Fd,E(B(_1CI(_1FL,_1FM,_1FL,_1Fe))),E(_1Ff)):new T4(0,_1Fc,_1Fd,E(_1Fe),E(B(_1CI(_1FL,_1FM,_1FL,_1Ff))));}else{var _1FO=(_1FL>>>0^_1Fc>>>0)>>>0,_1FP=(_1FO|_1FO>>>1)>>>0,_1FQ=(_1FP|_1FP>>>2)>>>0,_1FR=(_1FQ|_1FQ>>>4)>>>0,_1FS=(_1FR|_1FR>>>8)>>>0,_1FT=(_1FS|_1FS>>>16)>>>0,_1FU=(_1FT^_1FT>>>1)>>>0&4294967295,_1FV=_1FU>>>0;return ((_1FL>>>0&_1FV)>>>0==0)?new T4(0,(_1FL>>>0&((_1FV-1>>>0^4294967295)>>>0^_1FV)>>>0)>>>0&4294967295,_1FU,E(new T2(1,_1FL,_1FM)),E(new T4(0,_1Fc,_1Fd,E(_1Fe),E(_1Ff)))):new T4(0,(_1FL>>>0&((_1FV-1>>>0^4294967295)>>>0^_1FV)>>>0)>>>0&4294967295,_1FU,E(new T4(0,_1Fc,_1Fd,E(_1Fe),E(_1Ff))),E(new T2(1,_1FL,_1FM)));}break;default:return new T4(0,_1Fc,_1Fd,E(_1Fe),E(_1Ff));}};return new F(function(){return _1DT(_1CG,_1CH);});},_1FW=function(_1FX,_1FY,_1FZ){return new F(function(){return _1CE(_1Cy,_1FY,_1FZ);});},_1G0=function(_1G1,_1G2){return E(_1G1);},_1G3=new T2(0,_2s,_UB),_1G4=function(_1G5,_1G6){while(1){var _1G7=B((function(_1G8,_1G9){var _1Ga=E(_1G9);if(!_1Ga._){_1G5=new T2(1,_1Ga.b,new T(function(){return B(_1G4(_1G8,_1Ga.d));}));_1G6=_1Ga.c;return __continue;}else{return E(_1G8);}})(_1G5,_1G6));if(_1G7!=__continue){return _1G7;}}},_1Gb=function(_1Gc,_1Gd,_1Ge){var _1Gf=function(_1Gg){var _1Gh=function(_1Gi){if(_1Gg!=_1Gi){return false;}else{return new F(function(){return _1qC(_1Gc,B(_1G4(_M,_1Gd)),B(_1G4(_M,_1Ge)));});}},_1Gj=E(_1Ge);if(!_1Gj._){return new F(function(){return _1Gh(_1Gj.a);});}else{return new F(function(){return _1Gh(0);});}},_1Gk=E(_1Gd);if(!_1Gk._){return new F(function(){return _1Gf(_1Gk.a);});}else{return new F(function(){return _1Gf(0);});}},_1Gl=function(_1Gm,_1Gn){return (!B(_1Gb(_1tM,_1Gm,_1Gn)))?true:false;},_1Go=function(_1Gp,_1Gq){return new F(function(){return _1Gb(_1tM,_1Gp,_1Gq);});},_1Gr=new T2(0,_1Go,_1Gl),_1Gs=function(_1Gt,_1Gu){var _1Gv=function(_1Gw){while(1){var _1Gx=E(_1Gw);switch(_1Gx._){case 0:var _1Gy=_1Gx.b>>>0;if(((_1Gt>>>0&((_1Gy-1>>>0^4294967295)>>>0^_1Gy)>>>0)>>>0&4294967295)==_1Gx.a){if(!((_1Gt>>>0&_1Gy)>>>0)){_1Gw=_1Gx.c;continue;}else{_1Gw=_1Gx.d;continue;}}else{return false;}break;case 1:return _1Gt==_1Gx.a;default:return false;}}};return new F(function(){return _1Gv(_1Gu);});},_1Gz=function(_1GA,_1GB){var _1GC=function(_1GD){while(1){var _1GE=E(_1GD);switch(_1GE._){case 0:var _1GF=_1GE.b>>>0;if(((_1GA>>>0&((_1GF-1>>>0^4294967295)>>>0^_1GF)>>>0)>>>0&4294967295)==_1GE.a){if(!((_1GA>>>0&_1GF)>>>0)){_1GD=_1GE.c;continue;}else{_1GD=_1GE.d;continue;}}else{return false;}break;case 1:return ((_1GA&(-32))!=_1GE.a)?false:((1<<(_1GA&31)>>>0&_1GE.b)>>>0==0)?false:true;default:return false;}}};return new F(function(){return _1GC(_1GB);});},_1GG=function(_1GH,_1GI,_1GJ){while(1){var _1GK=E(_1GI);switch(_1GK._){case 0:var _1GL=E(_1GJ);if(!_1GL._){if(_1GK.b!=_1GL.b){return false;}else{if(_1GK.a!=_1GL.a){return false;}else{if(!B(_1GG(_1GH,_1GK.c,_1GL.c))){return false;}else{_1GI=_1GK.d;_1GJ=_1GL.d;continue;}}}}else{return false;}break;case 1:var _1GM=E(_1GJ);if(_1GM._==1){if(_1GK.a!=_1GM.a){return false;}else{return new F(function(){return A3(_oz,_1GH,_1GK.b,_1GM.b);});}}else{return false;}break;default:return (E(_1GJ)._==2)?true:false;}}},_1GN=function(_1GO,_1GP){var _1GQ=E(_1GP);if(!_1GQ._){var _1GR=_1GQ.b,_1GS=_1GQ.c,_1GT=_1GQ.d;if(!B(A1(_1GO,_1GR))){return new F(function(){return _1nG(B(_1GN(_1GO,_1GS)),B(_1GN(_1GO,_1GT)));});}else{return new F(function(){return _RN(_1GR,B(_1GN(_1GO,_1GS)),B(_1GN(_1GO,_1GT)));});}}else{return new T0(1);}},_1GU=function(_1GV,_1GW,_1GX){var _1GY=E(_1GX);switch(_1GY._){case 0:var _1GZ=_1GY.a,_1H0=_1GY.b,_1H1=_1GY.c,_1H2=_1GY.d,_1H3=_1H0>>>0;if(((_1GV>>>0&((_1H3-1>>>0^4294967295)>>>0^_1H3)>>>0)>>>0&4294967295)==_1GZ){return ((_1GV>>>0&_1H3)>>>0==0)?new T4(0,_1GZ,_1H0,E(B(_1GU(_1GV,_1GW,_1H1))),E(_1H2)):new T4(0,_1GZ,_1H0,E(_1H1),E(B(_1GU(_1GV,_1GW,_1H2))));}else{var _1H4=(_1GV>>>0^_1GZ>>>0)>>>0,_1H5=(_1H4|_1H4>>>1)>>>0,_1H6=(_1H5|_1H5>>>2)>>>0,_1H7=(_1H6|_1H6>>>4)>>>0,_1H8=(_1H7|_1H7>>>8)>>>0,_1H9=(_1H8|_1H8>>>16)>>>0,_1Ha=(_1H9^_1H9>>>1)>>>0&4294967295,_1Hb=_1Ha>>>0;return ((_1GV>>>0&_1Hb)>>>0==0)?new T4(0,(_1GV>>>0&((_1Hb-1>>>0^4294967295)>>>0^_1Hb)>>>0)>>>0&4294967295,_1Ha,E(new T2(1,_1GV,_1GW)),E(_1GY)):new T4(0,(_1GV>>>0&((_1Hb-1>>>0^4294967295)>>>0^_1Hb)>>>0)>>>0&4294967295,_1Ha,E(_1GY),E(new T2(1,_1GV,_1GW)));}break;case 1:var _1Hc=_1GY.a;if(_1Hc!=_1GV){var _1Hd=(_1GV>>>0^_1Hc>>>0)>>>0,_1He=(_1Hd|_1Hd>>>1)>>>0,_1Hf=(_1He|_1He>>>2)>>>0,_1Hg=(_1Hf|_1Hf>>>4)>>>0,_1Hh=(_1Hg|_1Hg>>>8)>>>0,_1Hi=(_1Hh|_1Hh>>>16)>>>0,_1Hj=(_1Hi^_1Hi>>>1)>>>0&4294967295,_1Hk=_1Hj>>>0;return ((_1GV>>>0&_1Hk)>>>0==0)?new T4(0,(_1GV>>>0&((_1Hk-1>>>0^4294967295)>>>0^_1Hk)>>>0)>>>0&4294967295,_1Hj,E(new T2(1,_1GV,_1GW)),E(_1GY)):new T4(0,(_1GV>>>0&((_1Hk-1>>>0^4294967295)>>>0^_1Hk)>>>0)>>>0&4294967295,_1Hj,E(_1GY),E(new T2(1,_1GV,_1GW)));}else{return new T2(1,_1Hc,(_1GW|_1GY.b)>>>0);}break;default:return new T2(1,_1GV,_1GW);}},_1Hl=function(_1Hm,_1Hn){while(1){var _1Ho=E(_1Hm);if(!_1Ho._){return E(_1Hn);}else{var _1Hp=E(E(_1Ho.a).b),_1Hq=B(_1GU(_1Hp&(-32),1<<(_1Hp&31)>>>0,_1Hn));_1Hm=_1Ho.b;_1Hn=_1Hq;continue;}}},_1Hr=function(_1Hs,_1Ht){while(1){var _1Hu=E(_1Hs);if(!_1Hu._){return E(_1Ht);}else{var _1Hv=B(_1Hl(E(_1Hu.a).a,_1Ht));_1Hs=_1Hu.b;_1Ht=_1Hv;continue;}}},_1Hw=function(_1Hx,_1Hy){while(1){var _1Hz=E(_1Hy);if(!_1Hz._){var _1HA=_1Hz.c,_1HB=_1Hz.d,_1HC=E(_1Hz.b);if(!_1HC._){var _1HD=B(_1Hr(_1HC.b,B(_1Hw(_1Hx,_1HB))));_1Hx=_1HD;_1Hy=_1HA;continue;}else{var _1HD=B(_1Hw(_1Hx,_1HB));_1Hx=_1HD;_1Hy=_1HA;continue;}}else{return E(_1Hx);}}},_1HE=-1,_1HF=-2,_1HG=-3,_1HH=new T2(1,_O9,_M),_1HI=new T2(1,_1HG,_1HH),_1HJ=new T2(1,_1HF,_1HI),_1HK=new T2(1,_1HE,_1HJ),_1HL=function(_1HM,_1HN,_1HO){var _1HP=function(_1HQ,_1HR){if(!B(_1GG(_1Gr,_1HM,_1HQ))){return new F(function(){return _1HL(_1HQ,_1HR,_1HO);});}else{return E(_1HM);}},_1HS=function(_1HT){if(!B(_vz(_gO,_1HT,_1HK))){var _1HU=E(_1HT);if(!B(_1Gs(_1HU,_1HM))){return new F(function(){return _1Gz(_1HU,_1HN);});}else{return true;}}else{return true;}},_1HV=function(_1HW){while(1){var _1HX=E(_1HW);if(!_1HX._){return true;}else{if(!B(_1HS(E(_1HX.a).b))){return false;}else{_1HW=_1HX.b;continue;}}}},_1HY=function(_1HZ){var _1I0=E(_1HZ);switch(_1I0._){case 0:return new F(function(){return _1HV(_1I0.b);});break;case 1:return new F(function(){return _1HS(_1I0.a);});break;default:return true;}},_1I1=function(_1I2,_1I3,_1I4){while(1){var _1I5=B((function(_1I6,_1I7,_1I8){var _1I9=E(_1I8);switch(_1I9._){case 0:var _1Ia=B(_1I1(_1I6,_1I7,_1I9.d));_1I2=_1Ia.a;_1I3=_1Ia.b;_1I4=_1I9.c;return __continue;case 1:var _1Ib=E(_1I6),_1Ic=E(_1I7),_1Id=B(_1GN(_1HY,_1I9.b));return (_1Id._==0)?new T2(0,new T(function(){return B(_1mn(_1I9.a,_1Id,_1Ib));}),new T(function(){return B(_1Hw(_1Ic,_1Id));})):new T2(0,_1Ib,_1Ic);default:return new T2(0,_1I6,_1I7);}})(_1I2,_1I3,_1I4));if(_1I5!=__continue){return _1I5;}}},_1Ie=E(_1HO);if(!_1Ie._){var _1If=_1Ie.c,_1Ig=_1Ie.d;if(_1Ie.b>=0){var _1Ih=B(_1I1(_XT,_1qr,_1Ig)),_1Ii=B(_1I1(_1Ih.a,_1Ih.b,_1If));return new F(function(){return _1HP(_1Ii.a,_1Ii.b);});}else{var _1Ij=B(_1I1(_XT,_1qr,_1If)),_1Ik=B(_1I1(_1Ij.a,_1Ij.b,_1Ig));return new F(function(){return _1HP(_1Ik.a,_1Ik.b);});}}else{var _1Il=B(_1I1(_XT,_1qr,_1Ie));return new F(function(){return _1HP(_1Il.a,_1Il.b);});}},_1Im=function(_1In,_1Io){while(1){var _1Ip=E(_1Io);if(!_1Ip._){return E(_1In);}else{var _1Iq=E(_1Ip.a),_1Ir=B(_1mn(E(_1Iq.a),_1Iq.b,_1In));_1In=_1Ir;_1Io=_1Ip.b;continue;}}},_1Is=function(_1It){var _1Iu=E(_1It);return (_1Iu._==0)?(E(_1Iu.b)._==0)?true:false:false;},_1Iv=new T(function(){return B(unCStr(")"));}),_1Iw=function(_1Ix,_1Iy){var _1Iz=new T(function(){var _1IA=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_16(B(_9z(0,_1Iy,_M)),_1Iv));})));},1);return B(_16(B(_9z(0,_1Ix,_M)),_1IA));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1Iz)));});},_1IB=new T(function(){return B(_r3("src/runtime/haskell/PGF/Optimize.hs:(259,9)-(262,117)|function getFunctions"));}),_1IC=new T(function(){return B(unCStr("&|"));}),_1ID=new T2(1,_1IC,_M),_1IE=new T(function(){return B(unCStr("&+"));}),_1IF=new T2(1,_1IE,_M),_1IG=new T(function(){return B(_r3("src/runtime/haskell/PGF/Optimize.hs:(235,9)-(245,73)|function seq2prefix"));}),_1IH=function(_1II,_1IJ,_1IK,_1IL,_1IM,_1IN){var _1IO=_1IL>>>0;if(((_1II>>>0&((_1IO-1>>>0^4294967295)>>>0^_1IO)>>>0)>>>0&4294967295)==_1IK){return ((_1II>>>0&_1IO)>>>0==0)?new T4(0,_1IK,_1IL,E(B(_1GU(_1II,_1IJ,_1IM))),E(_1IN)):new T4(0,_1IK,_1IL,E(_1IM),E(B(_1GU(_1II,_1IJ,_1IN))));}else{var _1IP=(_1II>>>0^_1IK>>>0)>>>0,_1IQ=(_1IP|_1IP>>>1)>>>0,_1IR=(_1IQ|_1IQ>>>2)>>>0,_1IS=(_1IR|_1IR>>>4)>>>0,_1IT=(_1IS|_1IS>>>8)>>>0,_1IU=(_1IT|_1IT>>>16)>>>0,_1IV=(_1IU^_1IU>>>1)>>>0&4294967295,_1IW=_1IV>>>0;return ((_1II>>>0&_1IW)>>>0==0)?new T4(0,(_1II>>>0&((_1IW-1>>>0^4294967295)>>>0^_1IW)>>>0)>>>0&4294967295,_1IV,E(new T2(1,_1II,_1IJ)),E(new T4(0,_1IK,_1IL,E(_1IM),E(_1IN)))):new T4(0,(_1II>>>0&((_1IW-1>>>0^4294967295)>>>0^_1IW)>>>0)>>>0&4294967295,_1IV,E(new T4(0,_1IK,_1IL,E(_1IM),E(_1IN))),E(new T2(1,_1II,_1IJ)));}},_1IX=function(_1IY,_1IZ,_1J0,_1J1,_1J2){var _1J3=E(_1J2);switch(_1J3._){case 0:var _1J4=_1J3.a,_1J5=_1J3.b,_1J6=_1J3.c,_1J7=_1J3.d;if(_1IZ>>>0<=_1J5>>>0){if(_1J5>>>0<=_1IZ>>>0){if(_1IY!=_1J4){var _1J8=(_1IY>>>0^_1J4>>>0)>>>0,_1J9=(_1J8|_1J8>>>1)>>>0,_1Ja=(_1J9|_1J9>>>2)>>>0,_1Jb=(_1Ja|_1Ja>>>4)>>>0,_1Jc=(_1Jb|_1Jb>>>8)>>>0,_1Jd=(_1Jc|_1Jc>>>16)>>>0,_1Je=(_1Jd^_1Jd>>>1)>>>0&4294967295,_1Jf=_1Je>>>0;return ((_1IY>>>0&_1Jf)>>>0==0)?new T4(0,(_1IY>>>0&((_1Jf-1>>>0^4294967295)>>>0^_1Jf)>>>0)>>>0&4294967295,_1Je,E(new T4(0,_1IY,_1IZ,E(_1J0),E(_1J1))),E(_1J3)):new T4(0,(_1IY>>>0&((_1Jf-1>>>0^4294967295)>>>0^_1Jf)>>>0)>>>0&4294967295,_1Je,E(_1J3),E(new T4(0,_1IY,_1IZ,E(_1J0),E(_1J1))));}else{return new T4(0,_1IY,_1IZ,E(B(_1Jg(_1J0,_1J6))),E(B(_1Jg(_1J1,_1J7))));}}else{var _1Jh=_1J5>>>0;if(((_1IY>>>0&((_1Jh-1>>>0^4294967295)>>>0^_1Jh)>>>0)>>>0&4294967295)==_1J4){return ((_1IY>>>0&_1Jh)>>>0==0)?new T4(0,_1J4,_1J5,E(B(_1IX(_1IY,_1IZ,_1J0,_1J1,_1J6))),E(_1J7)):new T4(0,_1J4,_1J5,E(_1J6),E(B(_1IX(_1IY,_1IZ,_1J0,_1J1,_1J7))));}else{var _1Ji=(_1IY>>>0^_1J4>>>0)>>>0,_1Jj=(_1Ji|_1Ji>>>1)>>>0,_1Jk=(_1Jj|_1Jj>>>2)>>>0,_1Jl=(_1Jk|_1Jk>>>4)>>>0,_1Jm=(_1Jl|_1Jl>>>8)>>>0,_1Jn=(_1Jm|_1Jm>>>16)>>>0,_1Jo=(_1Jn^_1Jn>>>1)>>>0&4294967295,_1Jp=_1Jo>>>0;return ((_1IY>>>0&_1Jp)>>>0==0)?new T4(0,(_1IY>>>0&((_1Jp-1>>>0^4294967295)>>>0^_1Jp)>>>0)>>>0&4294967295,_1Jo,E(new T4(0,_1IY,_1IZ,E(_1J0),E(_1J1))),E(_1J3)):new T4(0,(_1IY>>>0&((_1Jp-1>>>0^4294967295)>>>0^_1Jp)>>>0)>>>0&4294967295,_1Jo,E(_1J3),E(new T4(0,_1IY,_1IZ,E(_1J0),E(_1J1))));}}}else{var _1Jq=_1IZ>>>0;if(((_1J4>>>0&((_1Jq-1>>>0^4294967295)>>>0^_1Jq)>>>0)>>>0&4294967295)==_1IY){return ((_1J4>>>0&_1Jq)>>>0==0)?new T4(0,_1IY,_1IZ,E(B(_1Jr(_1J0,_1J4,_1J5,_1J6,_1J7))),E(_1J1)):new T4(0,_1IY,_1IZ,E(_1J0),E(B(_1Jr(_1J1,_1J4,_1J5,_1J6,_1J7))));}else{var _1Js=(_1IY>>>0^_1J4>>>0)>>>0,_1Jt=(_1Js|_1Js>>>1)>>>0,_1Ju=(_1Jt|_1Jt>>>2)>>>0,_1Jv=(_1Ju|_1Ju>>>4)>>>0,_1Jw=(_1Jv|_1Jv>>>8)>>>0,_1Jx=(_1Jw|_1Jw>>>16)>>>0,_1Jy=(_1Jx^_1Jx>>>1)>>>0&4294967295,_1Jz=_1Jy>>>0;return ((_1IY>>>0&_1Jz)>>>0==0)?new T4(0,(_1IY>>>0&((_1Jz-1>>>0^4294967295)>>>0^_1Jz)>>>0)>>>0&4294967295,_1Jy,E(new T4(0,_1IY,_1IZ,E(_1J0),E(_1J1))),E(_1J3)):new T4(0,(_1IY>>>0&((_1Jz-1>>>0^4294967295)>>>0^_1Jz)>>>0)>>>0&4294967295,_1Jy,E(_1J3),E(new T4(0,_1IY,_1IZ,E(_1J0),E(_1J1))));}}break;case 1:return new F(function(){return _1IH(_1J3.a,_1J3.b,_1IY,_1IZ,_1J0,_1J1);});break;default:return new T4(0,_1IY,_1IZ,E(_1J0),E(_1J1));}},_1Jr=function(_1JA,_1JB,_1JC,_1JD,_1JE){var _1JF=E(_1JA);switch(_1JF._){case 0:var _1JG=_1JF.a,_1JH=_1JF.b,_1JI=_1JF.c,_1JJ=_1JF.d;if(_1JH>>>0<=_1JC>>>0){if(_1JC>>>0<=_1JH>>>0){if(_1JG!=_1JB){var _1JK=(_1JG>>>0^_1JB>>>0)>>>0,_1JL=(_1JK|_1JK>>>1)>>>0,_1JM=(_1JL|_1JL>>>2)>>>0,_1JN=(_1JM|_1JM>>>4)>>>0,_1JO=(_1JN|_1JN>>>8)>>>0,_1JP=(_1JO|_1JO>>>16)>>>0,_1JQ=(_1JP^_1JP>>>1)>>>0&4294967295,_1JR=_1JQ>>>0;return ((_1JG>>>0&_1JR)>>>0==0)?new T4(0,(_1JG>>>0&((_1JR-1>>>0^4294967295)>>>0^_1JR)>>>0)>>>0&4294967295,_1JQ,E(_1JF),E(new T4(0,_1JB,_1JC,E(_1JD),E(_1JE)))):new T4(0,(_1JG>>>0&((_1JR-1>>>0^4294967295)>>>0^_1JR)>>>0)>>>0&4294967295,_1JQ,E(new T4(0,_1JB,_1JC,E(_1JD),E(_1JE))),E(_1JF));}else{return new T4(0,_1JG,_1JH,E(B(_1Jg(_1JI,_1JD))),E(B(_1Jg(_1JJ,_1JE))));}}else{var _1JS=_1JC>>>0;if(((_1JG>>>0&((_1JS-1>>>0^4294967295)>>>0^_1JS)>>>0)>>>0&4294967295)==_1JB){return ((_1JG>>>0&_1JS)>>>0==0)?new T4(0,_1JB,_1JC,E(B(_1IX(_1JG,_1JH,_1JI,_1JJ,_1JD))),E(_1JE)):new T4(0,_1JB,_1JC,E(_1JD),E(B(_1IX(_1JG,_1JH,_1JI,_1JJ,_1JE))));}else{var _1JT=(_1JG>>>0^_1JB>>>0)>>>0,_1JU=(_1JT|_1JT>>>1)>>>0,_1JV=(_1JU|_1JU>>>2)>>>0,_1JW=(_1JV|_1JV>>>4)>>>0,_1JX=(_1JW|_1JW>>>8)>>>0,_1JY=(_1JX|_1JX>>>16)>>>0,_1JZ=(_1JY^_1JY>>>1)>>>0&4294967295,_1K0=_1JZ>>>0;return ((_1JG>>>0&_1K0)>>>0==0)?new T4(0,(_1JG>>>0&((_1K0-1>>>0^4294967295)>>>0^_1K0)>>>0)>>>0&4294967295,_1JZ,E(_1JF),E(new T4(0,_1JB,_1JC,E(_1JD),E(_1JE)))):new T4(0,(_1JG>>>0&((_1K0-1>>>0^4294967295)>>>0^_1K0)>>>0)>>>0&4294967295,_1JZ,E(new T4(0,_1JB,_1JC,E(_1JD),E(_1JE))),E(_1JF));}}}else{var _1K1=_1JH>>>0;if(((_1JB>>>0&((_1K1-1>>>0^4294967295)>>>0^_1K1)>>>0)>>>0&4294967295)==_1JG){return ((_1JB>>>0&_1K1)>>>0==0)?new T4(0,_1JG,_1JH,E(B(_1Jr(_1JI,_1JB,_1JC,_1JD,_1JE))),E(_1JJ)):new T4(0,_1JG,_1JH,E(_1JI),E(B(_1Jr(_1JJ,_1JB,_1JC,_1JD,_1JE))));}else{var _1K2=(_1JG>>>0^_1JB>>>0)>>>0,_1K3=(_1K2|_1K2>>>1)>>>0,_1K4=(_1K3|_1K3>>>2)>>>0,_1K5=(_1K4|_1K4>>>4)>>>0,_1K6=(_1K5|_1K5>>>8)>>>0,_1K7=(_1K6|_1K6>>>16)>>>0,_1K8=(_1K7^_1K7>>>1)>>>0&4294967295,_1K9=_1K8>>>0;return ((_1JG>>>0&_1K9)>>>0==0)?new T4(0,(_1JG>>>0&((_1K9-1>>>0^4294967295)>>>0^_1K9)>>>0)>>>0&4294967295,_1K8,E(_1JF),E(new T4(0,_1JB,_1JC,E(_1JD),E(_1JE)))):new T4(0,(_1JG>>>0&((_1K9-1>>>0^4294967295)>>>0^_1K9)>>>0)>>>0&4294967295,_1K8,E(new T4(0,_1JB,_1JC,E(_1JD),E(_1JE))),E(_1JF));}}break;case 1:return new F(function(){return _1IH(_1JF.a,_1JF.b,_1JB,_1JC,_1JD,_1JE);});break;default:return new T4(0,_1JB,_1JC,E(_1JD),E(_1JE));}},_1Jg=function(_1Ka,_1Kb){var _1Kc=E(_1Ka);switch(_1Kc._){case 0:var _1Kd=_1Kc.a,_1Ke=_1Kc.b,_1Kf=_1Kc.c,_1Kg=_1Kc.d,_1Kh=E(_1Kb);switch(_1Kh._){case 0:var _1Ki=_1Kh.a,_1Kj=_1Kh.b,_1Kk=_1Kh.c,_1Kl=_1Kh.d;if(_1Ke>>>0<=_1Kj>>>0){if(_1Kj>>>0<=_1Ke>>>0){if(_1Kd!=_1Ki){var _1Km=(_1Kd>>>0^_1Ki>>>0)>>>0,_1Kn=(_1Km|_1Km>>>1)>>>0,_1Ko=(_1Kn|_1Kn>>>2)>>>0,_1Kp=(_1Ko|_1Ko>>>4)>>>0,_1Kq=(_1Kp|_1Kp>>>8)>>>0,_1Kr=(_1Kq|_1Kq>>>16)>>>0,_1Ks=(_1Kr^_1Kr>>>1)>>>0&4294967295,_1Kt=_1Ks>>>0;return ((_1Kd>>>0&_1Kt)>>>0==0)?new T4(0,(_1Kd>>>0&((_1Kt-1>>>0^4294967295)>>>0^_1Kt)>>>0)>>>0&4294967295,_1Ks,E(_1Kc),E(_1Kh)):new T4(0,(_1Kd>>>0&((_1Kt-1>>>0^4294967295)>>>0^_1Kt)>>>0)>>>0&4294967295,_1Ks,E(_1Kh),E(_1Kc));}else{return new T4(0,_1Kd,_1Ke,E(B(_1Jg(_1Kf,_1Kk))),E(B(_1Jg(_1Kg,_1Kl))));}}else{var _1Ku=_1Kj>>>0;if(((_1Kd>>>0&((_1Ku-1>>>0^4294967295)>>>0^_1Ku)>>>0)>>>0&4294967295)==_1Ki){return ((_1Kd>>>0&_1Ku)>>>0==0)?new T4(0,_1Ki,_1Kj,E(B(_1IX(_1Kd,_1Ke,_1Kf,_1Kg,_1Kk))),E(_1Kl)):new T4(0,_1Ki,_1Kj,E(_1Kk),E(B(_1IX(_1Kd,_1Ke,_1Kf,_1Kg,_1Kl))));}else{var _1Kv=(_1Kd>>>0^_1Ki>>>0)>>>0,_1Kw=(_1Kv|_1Kv>>>1)>>>0,_1Kx=(_1Kw|_1Kw>>>2)>>>0,_1Ky=(_1Kx|_1Kx>>>4)>>>0,_1Kz=(_1Ky|_1Ky>>>8)>>>0,_1KA=(_1Kz|_1Kz>>>16)>>>0,_1KB=(_1KA^_1KA>>>1)>>>0&4294967295,_1KC=_1KB>>>0;return ((_1Kd>>>0&_1KC)>>>0==0)?new T4(0,(_1Kd>>>0&((_1KC-1>>>0^4294967295)>>>0^_1KC)>>>0)>>>0&4294967295,_1KB,E(_1Kc),E(_1Kh)):new T4(0,(_1Kd>>>0&((_1KC-1>>>0^4294967295)>>>0^_1KC)>>>0)>>>0&4294967295,_1KB,E(_1Kh),E(_1Kc));}}}else{var _1KD=_1Ke>>>0;if(((_1Ki>>>0&((_1KD-1>>>0^4294967295)>>>0^_1KD)>>>0)>>>0&4294967295)==_1Kd){return ((_1Ki>>>0&_1KD)>>>0==0)?new T4(0,_1Kd,_1Ke,E(B(_1Jr(_1Kf,_1Ki,_1Kj,_1Kk,_1Kl))),E(_1Kg)):new T4(0,_1Kd,_1Ke,E(_1Kf),E(B(_1Jr(_1Kg,_1Ki,_1Kj,_1Kk,_1Kl))));}else{var _1KE=(_1Kd>>>0^_1Ki>>>0)>>>0,_1KF=(_1KE|_1KE>>>1)>>>0,_1KG=(_1KF|_1KF>>>2)>>>0,_1KH=(_1KG|_1KG>>>4)>>>0,_1KI=(_1KH|_1KH>>>8)>>>0,_1KJ=(_1KI|_1KI>>>16)>>>0,_1KK=(_1KJ^_1KJ>>>1)>>>0&4294967295,_1KL=_1KK>>>0;return ((_1Kd>>>0&_1KL)>>>0==0)?new T4(0,(_1Kd>>>0&((_1KL-1>>>0^4294967295)>>>0^_1KL)>>>0)>>>0&4294967295,_1KK,E(_1Kc),E(_1Kh)):new T4(0,(_1Kd>>>0&((_1KL-1>>>0^4294967295)>>>0^_1KL)>>>0)>>>0&4294967295,_1KK,E(_1Kh),E(_1Kc));}}break;case 1:return new F(function(){return _1IH(_1Kh.a,_1Kh.b,_1Kd,_1Ke,_1Kf,_1Kg);});break;default:return E(_1Kc);}break;case 1:return new F(function(){return _1GU(_1Kc.a,_1Kc.b,_1Kb);});break;default:return E(_1Kb);}},_1KM=function(_1KN,_1KO){var _1KP=E(_1KN),_1KQ=B(_1ob(_1kB,_1Jg,_1KP.a,_1KP.b,_1KO));return new T2(0,_1KQ.a,_1KQ.b);},_1KR=function(_1KS,_1KT){var _1KU=new T(function(){var _1KV=new T(function(){return B(unAppCStr(" not in range [0..",new T(function(){return B(_16(B(_9z(0,_1KS,_M)),_1Iv));})));},1);return B(_16(B(_9z(0,_1KT,_M)),_1KV));});return new F(function(){return err(B(unAppCStr("Error in array index; ",_1KU)));});},_1KW=new T(function(){return B(unCStr("Int"));}),_1KX=function(_1KY,_1KZ,_1L0){return new F(function(){return _g7(_fk,new T2(0,_1KZ,_1L0),_1KY,_1KW);});},_1L1=function(_1L2,_1L3,_1L4){return new F(function(){return _g7(_fk,new T2(0,_1L2,_1L3),_1L4,_1KW);});},_1L5=new T(function(){return B(_1Im(_XT,_M));}),_1L6=function(_1L7,_1L8){var _1L9=function(_1La,_1Lb,_1Lc){return new F(function(){return A2(_1L7,_1Lb,_1Lc);});},_1Ld=function(_1Le,_1Lf){while(1){var _1Lg=E(_1Lf);if(!_1Lg._){return E(_1Le);}else{var _1Lh=B(_1CE(_1L9,_1Le,_1Lg.a));_1Le=_1Lh;_1Lf=_1Lg.b;continue;}}};return new F(function(){return _1Ld(_XT,_1L8);});},_1Li=function(_1Lj,_1Lk,_1Ll,_1Lm,_1Ln,_1Lo,_1Lp,_1Lq,_1Lr){var _1Ls=new T(function(){return B(_1HL(_XT,_1qr,_1Lp));}),_1Lt=new T(function(){var _1Lu=function(_1Lv,_1Lw){while(1){var _1Lx=B((function(_1Ly,_1Lz){var _1LA=E(_1Lz);if(!_1LA._){var _1LB=_1LA.d,_1LC=new T(function(){var _1LD=E(_1LA.b);if(!_1LD._){var _1LE=_1LD.a;if(!E(_1LD.b)._){var _1LF=new T(function(){var _1LG=E(_1Ll),_1LH=_1LG.c,_1LI=E(_1LG.a),_1LJ=E(_1LG.b);if(_1LI>_1LE){return B(_1KX(_1LE,_1LI,_1LJ));}else{if(_1LE>_1LJ){return B(_1KX(_1LE,_1LI,_1LJ));}else{var _1LK=_1LE-_1LI|0;if(0>_1LK){return B(_1KR(_1LH,_1LK));}else{if(_1LK>=_1LH){return B(_1KR(_1LH,_1LK));}else{var _1LL=E(_1LG.d[_1LK]),_1LM=_1LL.d,_1LN=E(_1LL.b),_1LO=E(_1LL.c);if(_1LN<=_1LO){var _1LP=new T(function(){var _1LQ=B(_1mc(_1kB,_1G0,new T2(1,new T2(0,_1ID,new T2(1,_1LE&(-32),1<<(_1LE&31)>>>0)),_M)));return new T2(0,_1LQ.a,_1LQ.b);}),_1LR=new T(function(){var _1LS=B(_1mc(_1kB,_1G0,new T2(1,new T2(0,_M,new T2(1,_1LE&(-32),1<<(_1LE&31)>>>0)),_M)));return new T2(0,_1LS.a,_1LS.b);}),_1LT=new T2(1,_1LE&(-32),1<<(_1LE&31)>>>0),_1LU=new T(function(){var _1LV=B(_1mc(_1kB,_1G0,new T2(1,new T2(0,_M,_1LT),_M)));return new T2(0,_1LV.a,_1LV.b);}),_1LW=new T(function(){var _1LX=B(_1mc(_1kB,_1G0,new T2(1,new T2(0,_1IF,new T2(1,_1LE&(-32),1<<(_1LE&31)>>>0)),_M)));return new T2(0,_1LX.a,_1LX.b);}),_1LY=function(_1LZ){var _1M0=E(_1LZ);if(!_1M0._){return E(_1LU);}else{var _1M1=_1M0.b,_1M2=E(_1M0.a);switch(_1M2._){case 3:var _1M3=B(_1mc(_1kB,_1G0,new T2(1,new T2(0,new T2(1,_1M2.a,_M),_1LT),_M)));return new T2(0,_1M3.a,_1M3.b);case 4:var _1M4=new T(function(){var _1M5=function(_1M6){var _1M7=E(_1M6);return (_1M7._==0)?__Z:new T2(1,new T(function(){return B(_1LY(B(_16(E(_1M7.a).a,_1M1))));}),new T(function(){return B(_1M5(_1M7.b));}));};return B(_1M5(_1M2.b));}),_1M8=B(_1qh(_1kB,_1Jg,new T2(1,new T(function(){return B(_1LY(B(_16(_1M2.a,_1M1))));}),_1M4)));return new T2(0,_1M8.a,_1M8.b);case 5:return E(_1LW);case 6:return E(_1G3);case 7:return E(_1LR);case 8:return E(_1LR);case 9:return E(_1LP);case 10:return E(_1LP);default:return E(_1IG);}}},_1M9=new T(function(){return B(_1LY(_M));}),_1Ma=function(_1Mb){var _1Mc=new T(function(){var _1Md=E(_1Lo),_1Me=_1Md.c,_1Mf=E(_1Md.a),_1Mg=E(_1Md.b);if(_1LN>_1Mb){return B(_1L1(_1LN,_1LO,_1Mb));}else{if(_1Mb>_1LO){return B(_1L1(_1LN,_1LO,_1Mb));}else{var _1Mh=_1Mb-_1LN|0;if(0>_1Mh){return B(_1Iw(_1Mh,_1LM));}else{if(_1Mh>=_1LM){return B(_1Iw(_1Mh,_1LM));}else{var _1Mi=_1LL.e["v"]["i32"][_1Mh];if(_1Mf>_1Mi){return B(_1KX(_1Mi,_1Mf,_1Mg));}else{if(_1Mi>_1Mg){return B(_1KX(_1Mi,_1Mf,_1Mg));}else{var _1Mj=_1Mi-_1Mf|0;if(0>_1Mj){return B(_1KR(_1Me,_1Mj));}else{if(_1Mj>=_1Me){return B(_1KR(_1Me,_1Mj));}else{var _1Mk=E(_1Md.d[_1Mj]),_1Ml=_1Mk.c-1|0;if(0<=_1Ml){var _1Mm=function(_1Mn){return new T2(1,new T(function(){return E(_1Mk.d[_1Mn]);}),new T(function(){if(_1Mn!=_1Ml){return B(_1Mm(_1Mn+1|0));}else{return __Z;}}));};return B(_1LY(B(_1Mm(0))));}else{return E(_1M9);}}}}}}}}}});return new T2(1,new T2(0,_1Mb,_1Mc),new T(function(){if(_1Mb!=_1LO){return B(_1Ma(_1Mb+1|0));}else{return __Z;}}));};return B(_1Im(_XT,B(_1Ma(_1LN))));}else{return E(_1L5);}}}}}});return new T2(1,_1LF,new T(function(){return B(_1Lu(_1Ly,_1LB));}));}else{return B(_1Lu(_1Ly,_1LB));}}else{return B(_1Lu(_1Ly,_1LB));}},1);_1Lv=_1LC;_1Lw=_1LA.c;return __continue;}else{return E(_1Ly);}})(_1Lv,_1Lw));if(_1Lx!=__continue){return _1Lx;}}},_1Mo=function(_1Mp,_1Mq,_1Mr){while(1){var _1Ms=E(_1Mr);switch(_1Ms._){case 0:var _1Mt=B(_1Mo(_1Mp,_1Mq,_1Ms.d));_1Mp=_1Mt.a;_1Mq=_1Mt.b;_1Mr=_1Ms.c;continue;case 1:var _1Mu=_1Ms.a,_1Mv=B(_1nT(_1Is,_1Ms.b)),_1Mw=E(_1Mv.a);if(!_1Mw._){var _1Mx=B(_1mn(_1Mu,B(_1L6(_1KM,B(_1Lu(_M,_1Mw)))),_1Mp));}else{var _1Mx=E(_1Mp);}var _1My=E(_1Mv.b);if(!_1My._){var _1Mz=B(_1mn(_1Mu,_1My,_1Mq));}else{var _1Mz=E(_1Mq);}return new T2(0,_1Mx,_1Mz);default:return new T2(0,_1Mp,_1Mq);}}},_1MA=E(_1Ls);if(!_1MA._){var _1MB=_1MA.c,_1MC=_1MA.d;if(_1MA.b>=0){var _1MD=B(_1Mo(_XT,_XT,_1MC)),_1ME=B(_1Mo(_1MD.a,_1MD.b,_1MB));return new T2(0,_1ME.a,_1ME.b);}else{var _1MF=B(_1Mo(_XT,_XT,_1MB)),_1MG=B(_1Mo(_1MF.a,_1MF.b,_1MC));return new T2(0,_1MG.a,_1MG.b);}}else{var _1MH=B(_1Mo(_XT,_XT,_1MA));return new T2(0,_1MH.a,_1MH.b);}}),_1MI=new T(function(){var _1MJ=function(_1MK){var _1ML=E(_1MK);switch(_1ML._){case 0:var _1MM=_1ML.a;return new T2(1,new T(function(){var _1MN=E(_1Ll),_1MO=_1MN.c,_1MP=E(_1MN.a),_1MQ=E(_1MN.b);if(_1MP>_1MM){return B(_1KX(_1MM,_1MP,_1MQ));}else{if(_1MM>_1MQ){return B(_1KX(_1MM,_1MP,_1MQ));}else{var _1MR=_1MM-_1MP|0;if(0>_1MR){return B(_1KR(_1MO,_1MR));}else{if(_1MR>=_1MO){return B(_1KR(_1MO,_1MR));}else{return E(E(_1MN.d[_1MR]).a);}}}}}),_M);case 1:var _1MS=B(_1mO(_1ML.a,_1Ls));if(!_1MS._){return __Z;}else{return new F(function(){return _1MT(_M,_1MS.a);});}break;default:return E(_1IB);}},_1MT=function(_1MU,_1MV){while(1){var _1MW=B((function(_1MX,_1MY){var _1MZ=E(_1MY);if(!_1MZ._){var _1N0=new T(function(){return B(_16(B(_1MJ(_1MZ.b)),new T(function(){return B(_1MT(_1MX,_1MZ.d));},1)));},1);_1MU=_1N0;_1MV=_1MZ.c;return __continue;}else{return E(_1MX);}})(_1MU,_1MV));if(_1MW!=__continue){return _1MW;}}},_1N1=function(_1N2,_1N3){while(1){var _1N4=B((function(_1N5,_1N6){var _1N7=E(_1N6);switch(_1N7._){case 0:_1N2=new T(function(){return B(_1N1(_1N5,_1N7.d));},1);_1N3=_1N7.c;return __continue;case 1:var _1N8=function(_1N9,_1Na){while(1){var _1Nb=B((function(_1Nc,_1Nd){var _1Ne=E(_1Nd);if(!_1Ne._){var _1Nf=_1Ne.b,_1Ng=new T(function(){var _1Nh=new T(function(){return B(_1N8(_1Nc,_1Ne.d));}),_1Ni=function(_1Nj){var _1Nk=E(_1Nj);return (_1Nk._==0)?E(_1Nh):new T2(1,new T2(0,_1Nk.a,new T2(1,_1N7.a,new T4(0,1,E(_1Nf),E(_PM),E(_PM)))),new T(function(){return B(_1Ni(_1Nk.b));}));};return B(_1Ni(B(_1MJ(_1Nf))));},1);_1N9=_1Ng;_1Na=_1Ne.c;return __continue;}else{return E(_1Nc);}})(_1N9,_1Na));if(_1Nb!=__continue){return _1Nb;}}};return new F(function(){return _1N8(_1N5,_1N7.b);});break;default:return E(_1N5);}})(_1N2,_1N3));if(_1N4!=__continue){return _1N4;}}},_1Nl=E(_1Ls);if(!_1Nl._){var _1Nm=_1Nl.c,_1Nn=_1Nl.d;if(_1Nl.b>=0){return B(_1l6(_1FW,B(_1N1(new T(function(){return B(_1N1(_M,_1Nn));},1),_1Nm))));}else{return B(_1l6(_1FW,B(_1N1(new T(function(){return B(_1N1(_M,_1Nm));},1),_1Nn))));}}else{return B(_1l6(_1FW,B(_1N1(_M,_1Nl))));}});return {_:0,a:_1Lj,b:_1Lk,c:_1Ll,d:_1Lm,e:_1Ln,f:_1Lo,g:_1Lp,h:new T(function(){return E(E(_1Lt).b);}),i:_1MI,j:_1Lq,k:new T(function(){return E(E(_1Lt).a);}),l:_1Lr};},_1No=function(_1Np){var _1Nq=E(_1Np);return new F(function(){return _1Li(_1Nq.a,_1Nq.b,_1Nq.c,_1Nq.d,_1Nq.e,_1Nq.f,_1Nq.g,_1Nq.j,_1Nq.l);});},_1Nr=0,_1Ns=function(_1Nt){var _1Nu=E(_1Nt);return new T3(0,_1Nu.a,_1Nu.b,_1Nr);},_1Nv=function(_1Nw){var _1Nx=E(_1Nw);return new T4(0,_1Nx.a,_1Nx.b,new T(function(){var _1Ny=E(_1Nx.c);if(!_1Ny._){return __Z;}else{return new T1(1,new T2(0,_1Ny.a,_M));}}),_1Nx.d);},_1Nz=0,_1NA=new T(function(){return B(unCStr("Negative range size"));}),_1NB=new T(function(){return B(err(_1NA));}),_1NC=function(_1ND,_1NE,_1NF,_1NG,_1NH,_1NI,_1NJ,_1NK){var _1NL=B(_93(_1NF,_1NG,_1NH,_1NI,_1NJ,_1NK)),_1NM=E(_1NL.a)&4294967295,_1NN=B(_1fO(_1NM,_1NE,_1NL.b)),_1NO=_1NN.a,_1NP=new T(function(){var _1NQ=_1NM-1|0;return B(A(_hy,[_1ND,_hi,new T2(0,_1Nz,_1NQ),new T(function(){if(0>_1NQ){return B(_hA(B(_gm(0,-1)),_1NO));}else{var _1NR=_1NQ+1|0;if(_1NR>=0){return B(_hA(B(_gm(0,_1NR-1|0)),_1NO));}else{return E(_1NB);}}})]));});return new T2(0,_1NP,_1NN.b);},_1NS=function(_1NT,_1NU,_1NV,_1NW,_1NX,_1NY){var _1NZ=B(_9h(_1NT,_1NU,_1NV,_1NW,_1NX,_1NY)),_1O0=E(_1NZ.b),_1O1=B(_1NC(_kl,_iH,_1O0.a,_1O0.b,_1O0.c,_1O0.d,_1O0.e,_1O0.f));return new T2(0,new T(function(){var _1O2=E(_1O1.a);return new T5(0,_1NZ.a,E(_1O2.a),E(_1O2.b),_1O2.c,_1O2.d);}),_1O1.b);},_1O3=function(_1O4){var _1O5=E(_1O4),_1O6=B(_1NS(_1O5.a,_1O5.b,_1O5.c,_1O5.d,_1O5.e,_1O5.f));return new T2(0,_1O6.a,_1O6.b);},_1O7=function(_1O8){var _1O9=E(_1O8);if(!_1O9._){return __Z;}else{return new F(function(){return _16(_1O9.a,new T(function(){return B(_1O7(_1O9.b));},1));});}},_1Oa=function(_1Ob){return new F(function(){return _1O7(_1Ob);});},_1Oc=function(_1Od){var _1Oe=function(_){var _1Of=B(_cL(_1Od,0))-1|0,_1Og=function(_1Oh){if(_1Oh>=0){var _1Oi=newArr(_1Oh,_12d),_1Oj=_1Oi,_1Ok=function(_1Ol){var _1Om=function(_1On,_1Oo,_){while(1){if(_1On!=_1Ol){var _1Op=E(_1Oo);if(!_1Op._){return _0;}else{var _=_1Oj[_1On]=_1Op.a,_1Oq=_1On+1|0;_1On=_1Oq;_1Oo=_1Op.b;continue;}}else{return _0;}}},_1Or=B(_1Om(0,_1Od,_));return new T4(0,E(_1Nz),E(_1Of),_1Oh,_1Oj);};if(0>_1Of){return new F(function(){return _1Ok(0);});}else{var _1Os=_1Of+1|0;if(_1Os>=0){return new F(function(){return _1Ok(_1Os);});}else{return new F(function(){return err(_1NA);});}}}else{return E(_12f);}};if(0>_1Of){var _1Ot=B(_1Og(0)),_1Ou=E(_1Ot),_1Ov=_1Ou.d;return new T4(0,E(_1Ou.a),E(_1Ou.b),_1Ou.c,_1Ov);}else{var _1Ow=B(_1Og(_1Of+1|0)),_1Ox=E(_1Ow),_1Oy=_1Ox.d;return new T4(0,E(_1Ox.a),E(_1Ox.b),_1Ox.c,_1Oy);}};return new F(function(){return _df(_1Oe);});},_1Oz=function(_1OA){return new T1(3,_1OA);},_1OB=function(_1OC){var _1OD=E(_1OC),_1OE=B(_93(_1OD.a,_1OD.b,_1OD.c,_1OD.d,_1OD.e,_1OD.f)),_1OF=B(_aA(E(_1OE.a)&4294967295,_aq,_1OE.b));return new T2(0,new T1(3,_1OF.a),_1OF.b);},_1OG=function(_1OH){var _1OI=E(_1OH),_1OJ=B(_93(_1OI.a,_1OI.b,_1OI.c,_1OI.d,_1OI.e,_1OI.f)),_1OK=B(_aA(E(_1OJ.a)&4294967295,_aq,_1OJ.b));return new T2(0,_1OK.a,_1OK.b);},_1OL=function(_1OM,_1ON,_1OO,_1OP,_1OQ,_1OR){var _1OS=B(_93(_1OM,_1ON,_1OO,_1OP,_1OQ,_1OR)),_1OT=B(_1fO(E(_1OS.a)&4294967295,_1OB,_1OS.b)),_1OU=E(_1OT.b),_1OV=B(_93(_1OU.a,_1OU.b,_1OU.c,_1OU.d,_1OU.e,_1OU.f)),_1OW=B(_aA(E(_1OV.a)&4294967295,_1OG,_1OV.b));return new T2(0,new T2(0,_1OT.a,_1OW.a),_1OW.b);},_1OX=function(_1OY){var _1OZ=E(_1OY),_1P0=B(_1OL(_1OZ.a,_1OZ.b,_1OZ.c,_1OZ.d,_1OZ.e,_1OZ.f));return new T2(0,_1P0.a,_1P0.b);},_1P1=function(_1P2,_1P3){return new F(function(){return _1gT(B(unAppCStr("getSymbol ",new T(function(){return B(_9z(0,_1P2&4294967295,_M));}))),_1P3);});},_1P4=function(_1P5,_1P6,_1P7,_1P8,_1P9,_1Pa){var _1Pb=B(_8B(1,_1P5,_1P6,_1P7,_1P8,_1P9,_1Pa)),_1Pc=_1Pb.b,_1Pd=E(_1Pb.a),_1Pe=_1Pd.b,_1Pf=readOffAddr("w8",1,plusAddr(_1Pd.a,_1Pd.c),0),_1Pg=E(_1Pf);switch(_1Pg){case 0:var _1Ph=E(_1Pc),_1Pi=B(_93(_1Ph.a,_1Ph.b,_1Ph.c,_1Ph.d,_1Ph.e,_1Ph.f)),_1Pj=E(_1Pi.b),_1Pk=B(_93(_1Pj.a,_1Pj.b,_1Pj.c,_1Pj.d,_1Pj.e,_1Pj.f));return new T2(0,new T2(1,new T(function(){return new T2(0,E(_1Pi.a)&4294967295,E(_1Pk.a)&4294967295);}),_M),_1Pk.b);case 1:var _1Pl=E(_1Pc),_1Pm=B(_93(_1Pl.a,_1Pl.b,_1Pl.c,_1Pl.d,_1Pl.e,_1Pl.f)),_1Pn=E(_1Pm.b),_1Po=B(_93(_1Pn.a,_1Pn.b,_1Pn.c,_1Pn.d,_1Pn.e,_1Pn.f));return new T2(0,new T2(1,new T(function(){return new T2(1,E(_1Pm.a)&4294967295,E(_1Po.a)&4294967295);}),_M),_1Po.b);case 2:var _1Pp=E(_1Pc),_1Pq=B(_93(_1Pp.a,_1Pp.b,_1Pp.c,_1Pp.d,_1Pp.e,_1Pp.f)),_1Pr=E(_1Pq.b),_1Ps=B(_93(_1Pr.a,_1Pr.b,_1Pr.c,_1Pr.d,_1Pr.e,_1Pr.f));return new T2(0,new T2(1,new T(function(){return new T2(2,E(_1Pq.a)&4294967295,E(_1Ps.a)&4294967295);}),_M),_1Ps.b);case 3:var _1Pt=E(_1Pc),_1Pu=B(_93(_1Pt.a,_1Pt.b,_1Pt.c,_1Pt.d,_1Pt.e,_1Pt.f)),_1Pv=B(_aA(E(_1Pu.a)&4294967295,_1OG,_1Pu.b));return new T2(0,new T(function(){return B(_2Q(_1Oz,_1Pv.a));}),_1Pv.b);case 4:var _1Pw=E(_1Pc),_1Px=B(_93(_1Pw.a,_1Pw.b,_1Pw.c,_1Pw.d,_1Pw.e,_1Pw.f)),_1Py=B(_1fO(E(_1Px.a)&4294967295,_1OB,_1Px.b)),_1Pz=E(_1Py.b),_1PA=B(_93(_1Pz.a,_1Pz.b,_1Pz.c,_1Pz.d,_1Pz.e,_1Pz.f)),_1PB=B(_1fO(E(_1PA.a)&4294967295,_1OX,_1PA.b));return new T2(0,new T2(1,new T2(4,_1Py.a,_1PB.a),_M),_1PB.b);default:return new F(function(){return _1P1(_1Pg,E(_1Pc).f);});}},_1PC=function(_1PD){var _1PE=E(_1PD),_1PF=B(_1P4(_1PE.a,_1PE.b,_1PE.c,_1PE.d,_1PE.e,_1PE.f));return new T2(0,_1PF.a,_1PF.b);},_1PG=function(_1PH,_1PI,_1PJ,_1PK,_1PL,_1PM){var _1PN=B(_93(_1PH,_1PI,_1PJ,_1PK,_1PL,_1PM)),_1PO=B(_1fO(E(_1PN.a)&4294967295,_1PC,_1PN.b));return new T2(0,new T(function(){return B(_1Oc(B(_1Oa(_1PO.a))));}),_1PO.b);},_1PP=function(_1PQ){var _1PR=E(_1PQ),_1PS=B(_1PG(_1PR.a,_1PR.b,_1PR.c,_1PR.d,_1PR.e,_1PR.f));return new T2(0,_1PS.a,_1PS.b);},_1PT=function(_1PU){return new F(function(){return _1OG(_1PU);});},_1PV=function(_1PW){var _1PX=E(_1PW);return (_1PX._==0)?__Z:new T2(1,new T2(0,_O9,_1PX.a),new T(function(){return B(_1PV(_1PX.b));}));},_1PY=function(_1PZ,_1Q0,_1Q1,_1Q2,_1Q3,_1Q4){var _1Q5=B(_93(_1PZ,_1Q0,_1Q1,_1Q2,_1Q3,_1Q4)),_1Q6=B(_aA(E(_1Q5.a)&4294967295,_iH,_1Q5.b)),_1Q7=E(_1Q6.b),_1Q8=B(_93(_1Q7.a,_1Q7.b,_1Q7.c,_1Q7.d,_1Q7.e,_1Q7.f)),_1Q9=new T(function(){return new T2(0,new T(function(){return B(_1PV(_1Q6.a));}),E(_1Q8.a)&4294967295);});return new T2(0,_1Q9,_1Q8.b);},_1Qa=function(_1Qb){var _1Qc=E(_1Qb),_1Qd=B(_1PY(_1Qc.a,_1Qc.b,_1Qc.c,_1Qc.d,_1Qc.e,_1Qc.f));return new T2(0,_1Qd.a,_1Qd.b);},_1Qe=new T(function(){return B(unCStr("getProduction"));}),_1Qf=function(_1Qg){return new F(function(){return _1gT(_1Qe,_1Qg);});},_1Qh=function(_1Qi,_1Qj,_1Qk,_1Ql,_1Qm,_1Qn){var _1Qo=B(_8B(1,_1Qi,_1Qj,_1Qk,_1Ql,_1Qm,_1Qn)),_1Qp=_1Qo.b,_1Qq=E(_1Qo.a),_1Qr=_1Qq.b,_1Qs=readOffAddr("w8",1,plusAddr(_1Qq.a,_1Qq.c),0);switch(E(_1Qs)){case 0:var _1Qt=E(_1Qp),_1Qu=B(_93(_1Qt.a,_1Qt.b,_1Qt.c,_1Qt.d,_1Qt.e,_1Qt.f)),_1Qv=E(_1Qu.b),_1Qw=B(_93(_1Qv.a,_1Qv.b,_1Qv.c,_1Qv.d,_1Qv.e,_1Qv.f)),_1Qx=B(_1fO(E(_1Qw.a)&4294967295,_1Qa,_1Qw.b));return new T2(0,new T(function(){return new T2(0,E(_1Qu.a)&4294967295,_1Qx.a);}),_1Qx.b);case 1:var _1Qy=E(_1Qp),_1Qz=B(_93(_1Qy.a,_1Qy.b,_1Qy.c,_1Qy.d,_1Qy.e,_1Qy.f));return new T2(0,new T(function(){return new T1(1,E(_1Qz.a)&4294967295);}),_1Qz.b);default:return new F(function(){return _1Qf(E(_1Qp).f);});}},_1QA=function(_1QB){var _1QC=E(_1QB),_1QD=B(_1Qh(_1QC.a,_1QC.b,_1QC.c,_1QC.d,_1QC.e,_1QC.f));return new T2(0,_1QD.a,_1QD.b);},_1QE=function(_1QF,_1QG,_1QH,_1QI,_1QJ,_1QK){var _1QL=B(_93(_1QF,_1QG,_1QH,_1QI,_1QJ,_1QK)),_1QM=E(_1QL.b),_1QN=B(_93(_1QM.a,_1QM.b,_1QM.c,_1QM.d,_1QM.e,_1QM.f)),_1QO=B(_1fO(E(_1QN.a)&4294967295,_1QA,_1QN.b));return new T2(0,new T2(0,new T(function(){return E(_1QL.a)&4294967295;}),new T(function(){var _1QP=E(_1QO.a);if(!_1QP._){return new T0(1);}else{return B(_Sl(1,new T4(0,1,E(_1QP.a),E(_PM),E(_PM)),_1QP.b));}})),_1QO.b);},_1QQ=function(_1QR){var _1QS=E(_1QR),_1QT=B(_1QE(_1QS.a,_1QS.b,_1QS.c,_1QS.d,_1QS.e,_1QS.f));return new T2(0,_1QT.a,_1QT.b);},_1QU=function(_1PU){return new F(function(){return _1OG(_1PU);});},_1QV=function(_1QW,_1QX,_1QY,_1QZ,_1R0,_1R1){var _1R2=B(_93(_1QW,_1QX,_1QY,_1QZ,_1R0,_1R1)),_1R3=E(_1R2.b),_1R4=B(_93(_1R3.a,_1R3.b,_1R3.c,_1R3.d,_1R3.e,_1R3.f)),_1R5=E(_1R4.b),_1R6=B(_1NC(_eW,_1QU,_1R5.a,_1R5.b,_1R5.c,_1R5.d,_1R5.e,_1R5.f));return new T2(0,new T(function(){var _1R7=E(_1R6.a);return new T6(0,E(_1R2.a)&4294967295,E(_1R4.a)&4294967295,E(_1R7.a),E(_1R7.b),_1R7.c,_1R7.d);}),_1R6.b);},_1R8=function(_1R9){var _1Ra=E(_1R9),_1Rb=B(_1QV(_1Ra.a,_1Ra.b,_1Ra.c,_1Ra.d,_1Ra.e,_1Ra.f));return new T2(0,_1Rb.a,_1Rb.b);},_1Rc=function(_1Rd){return E(_1Rd)>>>0&255;},_1Re=function(_1Rf){var _1Rg=E(_1Rf);if(!_1Rg._){return __Z;}else{var _1Rh=E(_1Rg.a),_1Ri=new T(function(){return B(_1Re(_1Rg.b));}),_1Rj=function(_1Rk){var _1Rl=E(_1Rk);return (_1Rl._==0)?E(_1Ri):new T2(1,new T(function(){return B(_1Rc(_1Rl.a));}),new T(function(){return B(_1Rj(_1Rl.b));}));},_1Rm=function(_1Rn,_1Ro){return new T2(1,new T(function(){return B(_1Rc(_1Rn));}),new T(function(){return B(_1Rj(_1Ro));}));};if(_1Rh>127){if(_1Rh>2047){if(_1Rh>65535){return new F(function(){return _1Rm(240+(_1Rh>>18)|0,new T2(1,128+(_1Rh>>12&63)|0,new T2(1,128+(_1Rh>>6&63)|0,new T2(1,128+(_1Rh&63)|0,_M))));});}else{return new F(function(){return _1Rm(224+(_1Rh>>12)|0,new T2(1,128+(_1Rh>>6&63)|0,new T2(1,128+(_1Rh&63)|0,_M)));});}}else{return new F(function(){return _1Rm(192+(_1Rh>>6)|0,new T2(1,128+(_1Rh&63)|0,_M));});}}else{return new F(function(){return _1Rm(_1Rh,_M);});}}},_1Rp=function(_1Rq){var _1Rr=new T(function(){return B(_1Re(_1Rq));});return new F(function(){return _Ms(new T(function(){return B(_cL(_1Rr,0));},1),_1Rr);});},_1Rs=new T(function(){return B(unCStr("linref"));}),_1Rt=new T(function(){return B(_1Rp(_1Rs));}),_1Ru=new T(function(){return B(_1Im(_XT,_M));}),_1Rv=new T2(0,0,0),_1Rw=new T2(1,_1Rv,_M),_1Rx=new T(function(){return B(_1Oc(_1Rw));}),_1Ry=new T2(1,_1Rx,_M),_1Rz=function(_1RA,_1RB,_1RC,_1RD,_1RE,_1RF){var _1RG=B(_1fZ(_1k8,_1k4,_1RA,_1RB,_1RC,_1RD,_1RE,_1RF)),_1RH=E(_1RG.b),_1RI=B(_1fZ(_1k8,_1PT,_1RH.a,_1RH.b,_1RH.c,_1RH.d,_1RH.e,_1RH.f)),_1RJ=E(_1RI.b),_1RK=B(_93(_1RJ.a,_1RJ.b,_1RJ.c,_1RJ.d,_1RJ.e,_1RJ.f)),_1RL=E(_1RK.a)&4294967295,_1RM=B(_1fO(_1RL,_1PP,_1RK.b)),_1RN=E(_1RM.b),_1RO=B(_93(_1RN.a,_1RN.b,_1RN.c,_1RN.d,_1RN.e,_1RN.f)),_1RP=E(_1RO.a)&4294967295,_1RQ=B(_1fO(_1RP,_1O3,_1RO.b)),_1RR=E(_1RQ.b),_1RS=B(_Ue(_Tf,_1RR.a,_1RR.b,_1RR.c,_1RR.d,_1RR.e,_1RR.f)),_1RT=E(_1RS.b),_1RU=B(_93(_1RT.a,_1RT.b,_1RT.c,_1RT.d,_1RT.e,_1RT.f)),_1RV=B(_1fO(E(_1RU.a)&4294967295,_1QQ,_1RU.b)),_1RW=E(_1RV.b),_1RX=B(_1fZ(_1k8,_1R8,_1RW.a,_1RW.b,_1RW.c,_1RW.d,_1RW.e,_1RW.f)),_1RY=E(_1RX.b),_1RZ=B(_93(_1RY.a,_1RY.b,_1RY.c,_1RY.d,_1RY.e,_1RY.f)),_1S0=new T(function(){var _1S1=E(_1RZ.a)&4294967295,_1S2=new T(function(){var _1S3=function(_){var _1S4=(_1RL+1|0)-1|0,_1S5=function(_1S6){if(_1S6>=0){var _1S7=newArr(_1S6,_12d),_1S8=_1S7,_1S9=function(_1Sa){var _1Sb=function(_1Sc,_1Sd,_){while(1){if(_1Sc!=_1Sa){var _1Se=E(_1Sd);if(!_1Se._){return _0;}else{var _=_1S8[_1Sc]=_1Se.a,_1Sf=_1Sc+1|0;_1Sc=_1Sf;_1Sd=_1Se.b;continue;}}else{return _0;}}},_1Sg=B(_1Sb(0,new T(function(){return B(_16(_1RM.a,_1Ry));},1),_));return new T4(0,E(_1Nz),E(_1S4),_1S6,_1S8);};if(0>_1S4){return new F(function(){return _1S9(0);});}else{var _1Sh=_1S4+1|0;if(_1Sh>=0){return new F(function(){return _1S9(_1Sh);});}else{return E(_1NB);}}}else{return E(_12f);}};if(0>_1S4){var _1Si=B(_1S5(0)),_1Sj=E(_1Si),_1Sk=_1Sj.d;return new T4(0,E(_1Sj.a),E(_1Sj.b),_1Sj.c,_1Sk);}else{var _1Sl=B(_1S5(_1S4+1|0)),_1Sm=E(_1Sl),_1Sn=_1Sm.d;return new T4(0,E(_1Sm.a),E(_1Sm.b),_1Sm.c,_1Sn);}};return B(_df(_1S3));}),_1So=new T(function(){var _1Sp=_1S1-1|0;if(0<=_1Sp){var _1Sq=function(_1Sr){return new T2(1,new T2(0,_1Sr,new T2(1,_1RP,_M)),new T(function(){if(_1Sr!=_1Sp){return B(_1Sq(_1Sr+1|0));}else{return __Z;}}));};return B(_1Im(_XT,B(_1Sq(0))));}else{return E(_1Ru);}}),_1Ss=new T(function(){var _1St=function(_){var _1Su=(_1RP+1|0)-1|0,_1Sv=function(_1Sw){if(_1Sw>=0){var _1Sx=newArr(_1Sw,_12d),_1Sy=_1Sx,_1Sz=function(_1SA){var _1SB=function(_1SC,_1SD,_){while(1){if(_1SC!=_1SA){var _1SE=E(_1SD);if(!_1SE._){return _0;}else{var _=_1Sy[_1SC]=_1SE.a,_1SF=_1SC+1|0;_1SC=_1SF;_1SD=_1SE.b;continue;}}else{return _0;}}},_1SG=new T(function(){var _1SH=new T(function(){var _1SI=function(_){var _1SJ=newByteArr(4),_1SK=_1SJ,_1SL=function(_1SM,_){while(1){var _=_1SK["v"]["i32"][_1SM]=0,_1SN=E(_1SM);if(!_1SN){return _0;}else{_1SM=_1SN+1|0;continue;}}},_1SO=B(_1SL(0,_)),_1SP=function(_1SQ,_1SR,_){while(1){var _1SS=E(_1SQ);if(_1SS==1){return _0;}else{var _1ST=E(_1SR);if(!_1ST._){return _0;}else{var _=_1SK["v"]["i32"][_1SS]=E(_1ST.a);_1SQ=_1SS+1|0;_1SR=_1ST.b;continue;}}}},_1SU=B(_1SP(0,new T2(1,_1RL,_M),_));return new T4(0,E(_1Nz),E(_1Nz),1,_1SK);},_1SV=B(_df(_1SI));return new T5(0,_1Rt,E(_1SV.a),E(_1SV.b),_1SV.c,_1SV.d);});return B(_16(_1RQ.a,new T2(1,_1SH,_M)));},1),_1SW=B(_1SB(0,_1SG,_));return new T4(0,E(_1Nz),E(_1Su),_1Sw,_1Sy);};if(0>_1Su){return new F(function(){return _1Sz(0);});}else{var _1SX=_1Su+1|0;if(_1SX>=0){return new F(function(){return _1Sz(_1SX);});}else{return E(_1NB);}}}else{return E(_12f);}};if(0>_1Su){var _1SY=B(_1Sv(0)),_1SZ=E(_1SY),_1T0=_1SZ.d;return new T4(0,E(_1SZ.a),E(_1SZ.b),_1SZ.c,_1T0);}else{var _1T1=B(_1Sv(_1Su+1|0)),_1T2=E(_1T1),_1T3=_1T2.d;return new T4(0,E(_1T2.a),E(_1T2.b),_1T2.c,_1T3);}};return B(_df(_1St));});return {_:0,a:_1RG.a,b:_1RI.a,c:_1Ss,d:_1RS.a,e:_1So,f:_1S2,g:new T(function(){var _1T4=E(_1RV.a);if(!_1T4._){return new T0(2);}else{var _1T5=E(_1T4.a);return B(_Tx(E(_1T5.a),_1T5.b,_1T4.b,_Tg));}}),h:_XT,i:_UB,j:_1RX.a,k:_XT,l:_1S1};});return new T2(0,_1S0,_1RZ.b);},_1T6=function(_1T7){var _1T8=E(_1T7),_1T9=B(_1Rz(_1T8.a,_1T8.b,_1T8.c,_1T8.d,_1T8.e,_1T8.f));return new T2(0,_1T9.a,_1T9.b);},_1Ta=function(_1Tb,_1Tc,_1Td,_1Te,_1Tf,_1Tg){var _1Th=B(_It(8,_Lb,_1Tb,_1Tc,_1Td,_1Te,_1Tf,_1Tg)),_1Ti=E(_1Th.b),_1Tj=B(_9h(_1Ti.a,_1Ti.b,_1Ti.c,_1Ti.d,_1Ti.e,_1Ti.f));return new T2(0,new T2(0,_1Th.a,_1Tj.a),_1Tj.b);},_1Tk=function(_1Tl){var _1Tm=E(_1Tl),_1Tn=B(_1Ta(_1Tm.a,_1Tm.b,_1Tm.c,_1Tm.d,_1Tm.e,_1Tm.f));return new T2(0,_1Tn.a,_1Tn.b);},_1To=function(_1Tp,_1Tq,_1Tr,_1Ts,_1Tt,_1Tu){var _1Tv=B(_93(_1Tp,_1Tq,_1Tr,_1Ts,_1Tt,_1Tu)),_1Tw=B(_1fO(E(_1Tv.a)&4294967295,_1iv,_1Tv.b)),_1Tx=E(_1Tw.b),_1Ty=B(_93(_1Tx.a,_1Tx.b,_1Tx.c,_1Tx.d,_1Tx.e,_1Tx.f)),_1Tz=B(_1fO(E(_1Ty.a)&4294967295,_1Tk,_1Ty.b));return new T2(0,new T2(0,_1Tw.a,_1Tz.a),_1Tz.b);},_1TA=function(_1TB){var _1TC=E(_1TB),_1TD=B(_1To(_1TC.a,_1TC.b,_1TC.c,_1TC.d,_1TC.e,_1TC.f));return new T2(0,_1TD.a,_1TD.b);},_1TE=function(_1TF,_1TG,_1TH,_1TI,_1TJ,_1TK,_1TL){var _1TM=B(_9h(_1TG,_1TH,_1TI,_1TJ,_1TK,_1TL)),_1TN=E(_1TM.b),_1TO=B(_1fZ(_1k8,_1k4,_1TN.a,_1TN.b,_1TN.c,_1TN.d,_1TN.e,_1TN.f)),_1TP=E(_1TO.b),_1TQ=B(_1fZ(_1k8,_1k0,_1TP.a,_1TP.b,_1TP.c,_1TP.d,_1TP.e,_1TP.f)),_1TR=E(_1TQ.b),_1TS=B(_1fZ(_1k8,_1TA,_1TR.a,_1TR.b,_1TR.c,_1TR.d,_1TR.e,_1TR.f)),_1TT=E(_1TS.b),_1TU=B(_1fZ(_1k8,_1T6,_1TT.a,_1TT.b,_1TT.c,_1TT.d,_1TT.e,_1TT.f));return new T2(0,new T4(0,_1TF,_1TM.a,new T3(0,_1TO.a,new T(function(){return B(_1fs(_1Nv,_1TQ.a));}),new T(function(){return B(_1fs(_1Ns,_1TS.a));})),new T(function(){return B(_1fs(_1No,_1TU.a));})),_1TU.b);},_1TV=new T2(1,_8a,_M),_1TW=function(_1TX,_1TY,_1TZ){var _1U0=new T(function(){return B(A3(_fw,_fm,new T2(1,function(_1U1){return new F(function(){return _9z(0,_1TY&4294967295,_1U1);});},new T2(1,function(_1U2){return new F(function(){return _9z(0,E(_1TX)&4294967295,_1U2);});},_M)),_1TV));});return new F(function(){return _l2(B(unAppCStr("Unsupported PGF version ",new T2(1,_8b,_1U0))),_1TZ);});},_1U3=function(_1U4,_1U5){var _1U6=E(_1U5);return new F(function(){return _1Li(_1U6.a,_1U6.b,_1U6.c,_1U6.d,_1U6.e,_1U6.f,_1U6.g,_1U6.j,_1U6.l);});},_1U7=function(_1U8,_1U9,_1Ua,_1Ub,_1Uc,_1Ud){var _1Ue=B(_1gy(_1U8,_1U9,_1Ua,_1Ub,_1Uc,_1Ud)),_1Uf=E(_1Ue.b),_1Ug=B(_1gy(_1Uf.a,_1Uf.b,_1Uf.c,_1Uf.d,_1Uf.e,_1Uf.f)),_1Uh=_1Ug.a,_1Ui=_1Ug.b,_1Uj=E(_1Ue.a),_1Uk=function(_1Ul){var _1Um=E(_1Uj);if(_1Um==1){var _1Un=E(_1Uh);if(!E(_1Un)){var _1Uo=E(_1Ui),_1Up=B(_1fZ(_1k8,_1k4,_1Uo.a,_1Uo.b,_1Uo.c,_1Uo.d,_1Uo.e,_1Uo.f)),_1Uq=E(_1Up.b);return new F(function(){return _1TE(_1Up.a,_1Uq.a,_1Uq.b,_1Uq.c,_1Uq.d,_1Uq.e,_1Uq.f);});}else{return new F(function(){return _1TW(_1Un,1,E(_1Ui).f);});}}else{return new F(function(){return _1TW(_1Uh,_1Um,E(_1Ui).f);});}};if(E(_1Uj)==2){if(E(_1Uh)>1){return new F(function(){return _1Uk(_);});}else{var _1Ur=E(_1Ui),_1Us=B(_XF(_9u,_O8,_1Ur.a,_1Ur.b,_1Ur.c,_1Ur.d,_1Ur.e,_1Ur.f)),_1Ut=E(_1Us.b),_1Uu=B(_9h(_1Ut.a,_1Ut.b,_1Ut.c,_1Ut.d,_1Ut.e,_1Ut.f)),_1Uv=E(_1Uu.b),_1Uw=B(_1fw(_1Uv.a,_1Uv.b,_1Uv.c,_1Uv.d,_1Uv.e,_1Uv.f)),_1Ux=_1Uw.a,_1Uy=E(_1Uw.b),_1Uz=B(_XF(_9u,_14X,_1Uy.a,_1Uy.b,_1Uy.c,_1Uy.d,_1Uy.e,_1Uy.f)),_1UA=new T(function(){return B(_1fs(function(_1UB){return new F(function(){return _1U3(_1Ux,_1UB);});},_1Uz.a));});return new T2(0,new T4(0,_1Us.a,_1Uu.a,_1Ux,_1UA),_1Uz.b);}}else{return new F(function(){return _1Uk(_);});}},_1UC=new T(function(){return eval("(function(t){return document.createElement(t);})");}),_1UD=function(_){return new F(function(){return __app1(E(_1UC),"ul");});},_1UE=new T(function(){return eval("(function(c,p){p.appendChild(c);})");}),_1UF=new T(function(){return eval("document.body");}),_1UG=1,_1UH=65533,_1UI=new T2(0,_1UH,_1UG),_1UJ=2,_1UK=new T2(0,_1UH,_1UJ),_1UL=3,_1UM=new T2(0,_1UH,_1UL),_1UN=4,_1UO=new T2(0,_1UH,_1UN),_1UP=function(_1UQ,_1UR,_1US,_1UT){if(_1UT>0){var _1UU=new T(function(){var _1UV=readOffAddr("w8",1,plusAddr(_1UQ,_1US),0),_1UW=_1UV&4294967295;if(_1UW>=128){if(_1UW>=192){var _1UX=_1US+1|0,_1UY=_1UT-1|0;if(_1UW>=224){if(_1UW>=240){if(_1UW>=248){return E(_1UI);}else{if(_1UY>0){var _1UZ=readOffAddr("w8",1,plusAddr(_1UQ,_1UX),0);if((_1UZ&192)>>>0==128){var _1V0=_1UY-1|0;if(_1V0>0){var _1V1=_1UX+1|0,_1V2=readOffAddr("w8",1,plusAddr(_1UQ,_1V1),0);if((_1V2&192)>>>0==128){if((_1V0-1|0)>0){var _1V3=readOffAddr("w8",1,plusAddr(_1UQ,_1V1+1|0),0);if((_1V3&192)>>>0==128){var _1V4=(((_1UW&7)<<6|(_1UZ&63)>>>0&4294967295)<<6|(_1V2&63)>>>0&4294967295)<<6|(_1V3&63)>>>0&4294967295;if(_1V4<65536){return E(_1UO);}else{if(_1V4>=1114112){return E(_1UO);}else{return new T2(0,new T(function(){if(_1V4>>>0>1114111){return B(_9E(_1V4));}else{return _1V4;}}),_1UN);}}}else{return E(_1UM);}}else{return E(_1UM);}}else{return E(_1UK);}}else{return E(_1UK);}}else{return E(_1UI);}}else{return E(_1UI);}}}else{if(_1UY>0){var _1V5=readOffAddr("w8",1,plusAddr(_1UQ,_1UX),0);if((_1V5&192)>>>0==128){if((_1UY-1|0)>0){var _1V6=readOffAddr("w8",1,plusAddr(_1UQ,_1UX+1|0),0);if((_1V6&192)>>>0==128){var _1V7=((_1UW&15)<<6|(_1V5&63)>>>0&4294967295)<<6|(_1V6&63)>>>0&4294967295;if(_1V7<2048){if(_1V7<=57343){return E(_1UM);}else{if(_1V7>=65534){return E(_1UM);}else{return new T2(0,new T(function(){if(_1V7>>>0>1114111){return B(_9E(_1V7));}else{return _1V7;}}),_1UL);}}}else{if(_1V7>=55296){if(_1V7<=57343){return E(_1UM);}else{if(_1V7>=65534){return E(_1UM);}else{return new T2(0,new T(function(){if(_1V7>>>0>1114111){return B(_9E(_1V7));}else{return _1V7;}}),_1UL);}}}else{return new T2(0,new T(function(){if(_1V7>>>0>1114111){return B(_9E(_1V7));}else{return _1V7;}}),_1UL);}}}else{return E(_1UK);}}else{return E(_1UK);}}else{return E(_1UI);}}else{return E(_1UI);}}}else{if(_1UY>0){var _1V8=readOffAddr("w8",1,plusAddr(_1UQ,_1UX),0);if((_1V8&192)>>>0==128){var _1V9=(_1UW&31)<<6|(_1V8&63)>>>0&4294967295;if(_1V9<128){return E(_1UI);}else{return new T2(0,new T(function(){if(_1V9>>>0>1114111){return B(_9E(_1V9));}else{return _1V9;}}),_1UJ);}}else{return E(_1UI);}}else{return E(_1UI);}}}else{return E(_1UI);}}else{return new T2(0,new T(function(){if(_1UW>>>0>1114111){return B(_9E(_1UW));}else{return _1UW;}}),_1UG);}});return new T1(1,_1UU);}else{return __Z;}},_1Va=function(_1Vb,_1Vc,_1Vd,_1Ve,_1Vf,_1Vg){var _1Vh=B(_1UP(_1Vd,_1Ve,_1Vf,_1Vg));if(!_1Vh._){return E(_1Vc);}else{var _1Vi=E(_1Vh.a);return new F(function(){return A2(_1Vb,_1Vi.a,new T(function(){var _1Vj=E(_1Vi.b);if(_1Vj>0){if(_1Vj<_1Vg){return B(_1Va(_1Vb,_1Vc,_1Vd,_1Ve,_1Vf+_1Vj|0,_1Vg-_1Vj|0));}else{return B(_1Va(_1Vb,_1Vc,0,_3L,0,0));}}else{return B(_1Va(_1Vb,_1Vc,_1Vd,_1Ve,_1Vf,_1Vg));}}));});}},_1Vk=function(_1Vl){var _1Vm=E(_1Vl);if(_1Vm==95){return true;}else{var _1Vn=function(_1Vo){if(_1Vm<65){if(_1Vm<192){return false;}else{if(_1Vm>255){return false;}else{switch(E(_1Vm)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1Vm>90){if(_1Vm<192){return false;}else{if(_1Vm>255){return false;}else{switch(E(_1Vm)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1Vm<97){return new F(function(){return _1Vn(_);});}else{if(_1Vm>122){return new F(function(){return _1Vn(_);});}else{return true;}}}},_1Vp=function(_1Vq,_1Vr){return new T2(1,_1Vq,_1Vr);},_1Vs=function(_1Vt){var _1Vu=E(_1Vt);switch(_1Vu){case 39:return true;case 95:return true;default:var _1Vv=function(_1Vw){var _1Vx=function(_1Vy){if(_1Vu<65){if(_1Vu<192){return false;}else{if(_1Vu>255){return false;}else{switch(E(_1Vu)){case 215:return false;case 247:return false;default:return true;}}}}else{if(_1Vu>90){if(_1Vu<192){return false;}else{if(_1Vu>255){return false;}else{switch(E(_1Vu)){case 215:return false;case 247:return false;default:return true;}}}}else{return true;}}};if(_1Vu<97){return new F(function(){return _1Vx(_);});}else{if(_1Vu>122){return new F(function(){return _1Vx(_);});}else{return true;}}};if(_1Vu<48){return new F(function(){return _1Vv(_);});}else{if(_1Vu>57){return new F(function(){return _1Vv(_);});}else{return true;}}}},_1Vz=function(_1VA){while(1){var _1VB=E(_1VA);if(!_1VB._){return true;}else{if(!B(_1Vs(E(_1VB.a)))){return false;}else{_1VA=_1VB.b;continue;}}}},_1VC=new T(function(){return B(unCStr("\\\\"));}),_1VD=new T(function(){return B(unCStr("\\\'"));}),_1VE=new T(function(){return B(unCStr("\'"));}),_1VF=function(_1VG){var _1VH=E(_1VG);if(!_1VH._){return E(_1VE);}else{var _1VI=_1VH.b,_1VJ=E(_1VH.a);switch(E(_1VJ)){case 39:return new F(function(){return _16(_1VD,new T(function(){return B(_1VF(_1VI));},1));});break;case 92:return new F(function(){return _16(_1VC,new T(function(){return B(_1VF(_1VI));},1));});break;default:return new T2(1,_1VJ,new T(function(){return B(_1VF(_1VI));}));}}},_1VK=function(_1VL,_1VM,_1VN,_1VO){var _1VP=B(_1Va(_1Vp,_M,_1VL,_1VM,_1VN,_1VO));if(!_1VP._){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1VF(_M));}));});}else{if(!B(_1Vk(E(_1VP.a)))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1VF(_1VP));}));});}else{if(!B(_1Vz(_1VP.b))){return new F(function(){return unAppCStr("\'",new T(function(){return B(_1VF(_1VP));}));});}else{return E(_1VP);}}}},_1VQ=new T(function(){return B(unCStr("li"));}),_1VR=new T(function(){return eval("(function(s){return document.createTextNode(s);})");}),_1VS=function(_1VT,_1VU,_1VV){while(1){var _1VW=B((function(_1VX,_1VY,_1VZ){var _1W0=E(_1VY);if(!_1W0._){var _1W1=E(_1W0.b),_1W2=function(_1W3){return new F(function(){return _1VS(_1VX,_1W0.e,function(_){var _1W4=__app1(E(_1UC),toJSStr(E(_1VQ))),_1W5=__app1(E(_1VR),toJSStr(B(_1VK(_1W1.a,_1W1.b,_1W1.c,_1W1.d)))),_1W6=E(_1UE),_1W7=__app2(_1W6,_1W5,_1W4),_1W8=B(A1(_1W3,_)),_1W9=__app2(_1W6,_1W4,E(_1W8));return new F(function(){return A1(_1W3,_);});});});},_1Wa=_1VZ;_1VT=_1W2;_1VU=_1W0.d;_1VV=_1Wa;return __continue;}else{return new F(function(){return A1(_1VX,_1VZ);});}})(_1VT,_1VU,_1VV));if(_1VW!=__continue){return _1VW;}}},_1Wb=new T(function(){return B(unCStr("No result"));}),_1Wc=new T(function(){return B(unCStr("h1"));}),_1Wd=new T(function(){return B(unCStr("Languages"));}),_1We=function(_1Wf,_1Wg){var _1Wh=function(_1Wi,_1Wj,_1Wk,_){while(1){var _1Wl=B((function(_1Wm,_1Wn,_1Wo,_){var _1Wp=E(_1Wo);if(!_1Wp._){return new T2(0,new T(function(){return E(_1Wf)-_1Wn|0;}),_M);}else{var _1Wq=E(_1Wn);if(!_1Wq){return new T2(0,_1Wf,_1Wp);}else{var _=writeOffAddr("w8",1,_1Wm,0,E(_1Wp.a)>>>0&255),_1Wr=plusAddr(_1Wm,1);_1Wi=_1Wr;_1Wj=_1Wq-1|0;_1Wk=_1Wp.b;return __continue;}}})(_1Wi,_1Wj,_1Wk,_));if(_1Wl!=__continue){return _1Wl;}}},_1Ws=function(_){var _1Wt=E(_1Wf);if(_1Wt>=0){var _1Wu=newByteArr(_1Wt),_1Wv=B(_1Wh(_1Wu,_1Wt,_1Wg,_)),_1Ww=E(_1Wv);return new T2(0,new T(function(){return new T4(0,_1Wu,new T1(2,_1Wu),0,E(_1Ww.a));}),_1Ww.b);}else{return E(_7s);}};return new F(function(){return _38(_1Ws);});},_1Wx=4088,_1Wy=function(_1Wz,_1WA){var _1WB=B(_1We(_1Wz,_1WA)),_1WC=_1WB.a,_1WD=E(_1WB.b);if(!_1WD._){var _1WE=E(_1WC),_1WF=E(_1WE.d);return (_1WF==0)?__Z:new T5(1,_1WE.a,_1WE.b,_1WE.c,_1WF,_7B);}else{var _1WG=E(_1WC),_1WH=new T(function(){return B(_1Wy(new T(function(){var _1WI=imul(E(_1Wz),2)|0;if(_1WI>4088){return E(_1Wx);}else{return _1WI;}}),_1WD));});return new T5(1,_1WG.a,_1WG.b,_1WG.c,_1WG.d,_1WH);}},_1WJ=function(_1WK,_1WL){var _1WM=B(_1We(_1WK,_1WL)),_1WN=_1WM.a,_1WO=E(_1WM.b);if(!_1WO._){var _1WP=E(_1WN),_1WQ=E(_1WP.d);return (_1WQ==0)?__Z:new T5(1,_1WP.a,_1WP.b,_1WP.c,_1WQ,_7B);}else{var _1WR=E(_1WN),_1WS=new T(function(){return B(_1Wy(new T(function(){var _1WT=imul(_1WK,2)|0;if(_1WT>4088){return E(_1Wx);}else{return _1WT;}}),_1WO));});return new T5(1,_1WR.a,_1WR.b,_1WR.c,_1WR.d,_1WS);}},_1WU=function(_1WV,_){var _1WW=E(_1WV);if(!_1WW._){var _1WX=__app1(E(_1UC),toJSStr(E(_1Wc))),_1WY=__app1(E(_1VR),toJSStr(E(_1Wb))),_1WZ=E(_1UE),_1X0=__app2(_1WZ,_1WY,_1WX),_1X1=__app2(_1WZ,_1WX,E(_1UF));return _0;}else{var _1X2=function(_1X3){var _1X4=B(A(_1VS,[_2I,_1X3,_1UD,_])),_1X5=__app1(E(_1UC),toJSStr(E(_1Wc))),_1X6=__app1(E(_1VR),toJSStr(E(_1Wd))),_1X7=E(_1UE),_1X8=__app2(_1X7,_1X6,_1X5),_1X9=E(_1UF),_1Xa=__app2(_1X7,_1X5,_1X9),_1Xb=__app2(_1X7,E(_1X4),_1X9);return _0;},_1Xc=B(_1WJ(32,_1WW.a));if(!_1Xc._){return new F(function(){return _1X2(E(B(_1U7(0,_3L,0,0,_7B,new Long(0,0))).a).d);});}else{return new F(function(){return _1X2(E(B(_1U7(_1Xc.a,_1Xc.b,_1Xc.c,_1Xc.d,_1Xc.e,new Long(0,0))).a).d);});}}},_1Xd=new T(function(){return B(unCStr("http://hackerbrau.se/haste/Foods.pgf"));}),_1Xe=new T(function(){return B(_3h(_2K,_a,_a,_h,_2L,_1Xd,_M,_1WU));});
var hasteMain = function() {B(A(_1Xe, [0]));};window.onload = hasteMain;