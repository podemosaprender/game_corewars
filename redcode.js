"use strict";
window.emulator_function;
window.emulator_timer;
window.emulator_speed=1000;
function mySetInterval(f) { 
	window.emulator_function= f;
	window.emulator_timer= window.setInterval(f, window.emulator_speed); 
	return window.emulator_timer
}

function emulatorChangeSpeed(factor) {
	window.clearInterval(window.emulator_timer);
	window.emulator_speed= window.emulator_speed / factor;
	console.log("emulator_speed",window.emulator_speed);
	mySetInterval(window.emulator_function);
}

window.addEventListener('load', function () {
	document.getElementById('slowerB').onclick= function () { emulatorChangeSpeed(.1) }
	document.getElementById('fasterB').onclick= function () { emulatorChangeSpeed(10) }
});

var __haste_prog_id = 'ef66e794dba273379210281d944210d9817417a565c3efb3022b18593e4af683';
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

var _0=function(_1,_2,_){var _3=B(A1(_1,_)),_4=B(A1(_2,_));return new T(function(){return B(A1(_3,_4));});},_5=function(_6,_7,_){var _8=B(A1(_7,_));return new T(function(){return B(A1(_6,_8));});},_9=function(_a,_){return _a;},_b=function(_c,_d,_){var _e=B(A1(_c,_));return C > 19 ? new F(function(){return A1(_d,_);}) : (++C,A1(_d,_));},_f=new T(function(){return unCStr("base");}),_g=new T(function(){return unCStr("GHC.IO.Exception");}),_h=new T(function(){return unCStr("IOException");}),_i=function(_j){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_f,_g,_h),__Z,__Z));},_k=function(_l){return E(E(_l).a);},_m=function(_n,_o,_p){var _q=B(A1(_n,_)),_r=B(A1(_o,_)),_s=hs_eqWord64(_q.a,_r.a);if(!_s){return __Z;}else{var _t=hs_eqWord64(_q.b,_r.b);return (!_t)?__Z:new T1(1,_p);}},_u=new T(function(){return unCStr(": ");}),_v=new T(function(){return unCStr(")");}),_w=new T(function(){return unCStr(" (");}),_x=function(_y,_z){var _A=E(_y);return (_A._==0)?E(_z):new T2(1,_A.a,new T(function(){return _x(_A.b,_z);}));},_B=new T(function(){return unCStr("interrupted");}),_C=new T(function(){return unCStr("system error");}),_D=new T(function(){return unCStr("unsatisified constraints");}),_E=new T(function(){return unCStr("user error");}),_F=new T(function(){return unCStr("permission denied");}),_G=new T(function(){return unCStr("illegal operation");}),_H=new T(function(){return unCStr("end of file");}),_I=new T(function(){return unCStr("resource exhausted");}),_J=new T(function(){return unCStr("resource busy");}),_K=new T(function(){return unCStr("does not exist");}),_L=new T(function(){return unCStr("already exists");}),_M=new T(function(){return unCStr("resource vanished");}),_N=new T(function(){return unCStr("timeout");}),_O=new T(function(){return unCStr("unsupported operation");}),_P=new T(function(){return unCStr("hardware fault");}),_Q=new T(function(){return unCStr("inappropriate type");}),_R=new T(function(){return unCStr("invalid argument");}),_S=new T(function(){return unCStr("failed");}),_T=new T(function(){return unCStr("protocol error");}),_U=function(_V,_W){switch(E(_V)){case 0:return _x(_L,_W);case 1:return _x(_K,_W);case 2:return _x(_J,_W);case 3:return _x(_I,_W);case 4:return _x(_H,_W);case 5:return _x(_G,_W);case 6:return _x(_F,_W);case 7:return _x(_E,_W);case 8:return _x(_D,_W);case 9:return _x(_C,_W);case 10:return _x(_T,_W);case 11:return _x(_S,_W);case 12:return _x(_R,_W);case 13:return _x(_Q,_W);case 14:return _x(_P,_W);case 15:return _x(_O,_W);case 16:return _x(_N,_W);case 17:return _x(_M,_W);default:return _x(_B,_W);}},_X=new T(function(){return unCStr("}");}),_Y=new T(function(){return unCStr("{handle: ");}),_Z=function(_10,_11,_12,_13,_14,_15){var _16=new T(function(){var _17=new T(function(){var _18=new T(function(){var _19=E(_13);if(!_19._){return E(_15);}else{var _1a=new T(function(){return _x(_19,new T(function(){return _x(_v,_15);},1));},1);return _x(_w,_1a);}},1);return _U(_11,_18);}),_1b=E(_12);if(!_1b._){return E(_17);}else{return _x(_1b,new T(function(){return _x(_u,_17);},1));}}),_1c=E(_14);if(!_1c._){var _1d=E(_10);if(!_1d._){return E(_16);}else{var _1e=E(_1d.a);if(!_1e._){var _1f=new T(function(){var _1g=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1g);},1);return _x(_Y,_1f);}else{var _1h=new T(function(){var _1i=new T(function(){return _x(_X,new T(function(){return _x(_u,_16);},1));},1);return _x(_1e.a,_1i);},1);return _x(_Y,_1h);}}}else{return _x(_1c.a,new T(function(){return _x(_u,_16);},1));}},_1j=function(_1k){var _1l=E(_1k);return _Z(_1l.a,_1l.b,_1l.c,_1l.d,_1l.f,__Z);},_1m=function(_1n){return new T2(0,_1o,_1n);},_1p=function(_1q,_1r){var _1s=E(_1q);return _Z(_1s.a,_1s.b,_1s.c,_1s.d,_1s.f,_1r);},_1t=function(_1u,_1v,_1w){var _1x=E(_1v);if(!_1x._){return unAppCStr("[]",_1w);}else{var _1y=new T(function(){var _1z=new T(function(){var _1A=function(_1B){var _1C=E(_1B);if(!_1C._){return E(new T2(1,93,_1w));}else{var _1D=new T(function(){return B(A2(_1u,_1C.a,new T(function(){return _1A(_1C.b);})));});return new T2(1,44,_1D);}};return _1A(_1x.b);});return B(A2(_1u,_1x.a,_1z));});return new T2(1,91,_1y);}},_1o=new T(function(){return new T5(0,_i,new T3(0,function(_1E,_1F,_1G){var _1H=E(_1F);return _Z(_1H.a,_1H.b,_1H.c,_1H.d,_1H.f,_1G);},_1j,function(_1I,_1J){return _1t(_1p,_1I,_1J);}),_1m,function(_1K){var _1L=E(_1K);return _m(_k(_1L.a),_i,_1L.b);},_1j);}),_1M=new T(function(){return E(_1o);}),_1N=function(_1O){return E(E(_1O).c);},_1P=function(_1Q){return new T6(0,__Z,7,__Z,_1Q,__Z,__Z);},_1R=function(_1S,_){var _1T=new T(function(){return B(A2(_1N,_1M,new T(function(){return B(A1(_1P,_1S));})));});return die(_1T);},_1U=function(_1V,_){return _1R(_1V,_);},_1W=function(_1X){return E(_1X);},_1Y=new T2(0,new T5(0,new T5(0,new T2(0,_5,function(_1Z,_20,_){var _21=B(A1(_20,_));return _1Z;}),_9,_0,_b,function(_22,_23,_){var _24=B(A1(_22,_)),_25=B(A1(_23,_));return _24;}),function(_26,_27,_){var _28=B(A1(_26,_));return C > 19 ? new F(function(){return A2(_27,_28,_);}) : (++C,A2(_27,_28,_));},_b,_9,function(_29){return C > 19 ? new F(function(){return A1(_1U,_29);}) : (++C,A1(_1U,_29));}),_1W),_2a=function(_2b,_2c){var _2d=jsShowI(_2b);return _x(fromJSStr(_2d),_2c);},_2e=function(_2f,_2g,_2h){if(_2g>=0){return _2a(_2g,_2h);}else{if(_2f<=6){return _2a(_2g,_2h);}else{return new T2(1,40,new T(function(){var _2i=jsShowI(_2g);return _x(fromJSStr(_2i),new T2(1,41,_2h));}));}}},_2j=new T(function(){return unAppCStr(") is outside of enumeration\'s range (0,",new T(function(){return _2e(0,2,new T(function(){return unCStr(")");}));}));}),_2k=function(_2l){return err(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return _2e(0,_2l,_2j);})));},_2m=function(_2n,_){return new T(function(){var _2o=Number(E(_2n)),_2p=jsTrunc(_2o);if(_2p<0){return _2k(_2p);}else{if(_2p>2){return _2k(_2p);}else{return _2p;}}});},_2q=new T3(0,0,0,0),_2r=new T(function(){return jsGetMouseCoords;}),_2s=function(_2t,_){var _2u=E(_2t);if(!_2u._){return __Z;}else{var _2v=_2s(_2u.b,_);return new T2(1,new T(function(){var _2w=Number(E(_2u.a));return jsTrunc(_2w);}),_2v);}},_2x=function(_2y,_){var _2z=__arr2lst(0,_2y);return _2s(_2z,_);},_2A=function(_2B,_){return new T(function(){var _2C=Number(E(_2B));return jsTrunc(_2C);});},_2D=new T2(0,_2A,function(_2E,_){return _2x(E(_2E),_);}),_2F=function(_2G,_){var _2H=E(_2G);if(!_2H._){return __Z;}else{var _2I=_2F(_2H.b,_);return new T2(1,_2H.a,_2I);}},_2J=new T(function(){return _1m(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9");}),__Z,__Z));}),_2K=function(_){return die(_2J);},_2L=function(_2M){return E(E(_2M).a);},_2N=function(_2O,_2P,_2Q,_){var _2R=__arr2lst(0,_2Q),_2S=_2F(_2R,_),_2T=E(_2S);if(!_2T._){return _2K(_);}else{var _2U=E(_2T.b);if(!_2U._){return _2K(_);}else{if(!E(_2U.b)._){var _2V=B(A3(_2L,_2O,_2T.a,_)),_2W=B(A3(_2L,_2P,_2U.a,_));return new T2(0,_2V,_2W);}else{return _2K(_);}}}},_2X=function(_2Y){var _2Z=B(A1(_2Y,_));return E(_2Z);},_30=new T(function(){return _2X(function(_){return __jsNull();});}),_31=function(_32,_33,_){if(E(_32)==7){var _34=E(_2r)(_33),_35=_2N(_2D,_2D,_34,_),_36=_33["deltaX"],_37=_33["deltaY"],_38=_33["deltaZ"];return new T(function(){return new T3(0,E(_35),E(__Z),E(new T3(0,_36,_37,_38)));});}else{var _39=E(_2r)(_33),_3a=_2N(_2D,_2D,_39,_),_3b=_33["button"],_3c=__eq(_3b,E(_30));if(!E(_3c)){var _3d=__isUndef(_3b);if(!E(_3d)){var _3e=_2m(_3b,_);return new T(function(){return new T3(0,E(_3a),E(new T1(1,_3e)),E(_2q));});}else{return new T(function(){return new T3(0,E(_3a),E(__Z),E(_2q));});}}else{return new T(function(){return new T3(0,E(_3a),E(__Z),E(_2q));});}}},_3f=new T2(0,function(_3g){switch(E(_3g)){case 0:return "click";case 1:return "dblclick";case 2:return "mousedown";case 3:return "mouseup";case 4:return "mousemove";case 5:return "mouseover";case 6:return "mouseout";default:return "wheel";}},function(_3h,_3i,_){return _31(_3h,E(_3i),_);}),_3j=function(_3k){return E(_3k);},_3l=function(_){return 0;},_3m=function(_3n){return E(E(_3n).a);},_3o=function(_3p){return E(E(_3p).d);},_3q=new T2(0,_1W,function(_3r,_3s){return C > 19 ? new F(function(){return A2(_3o,_3m(_3r),new T1(1,_3s));}) : (++C,A2(_3o,_3m(_3r),new T1(1,_3s)));}),_3t=new T2(0,_1Y,_9),_3u=new T(function(){return err(new T(function(){return unCStr("Map.!: given key is not an element in the map");}));}),_3v=function(_3w,_3x){while(1){var _3y=E(_3x);if(!_3y._){var _3z=E(_3y.b);if(_3w>=_3z){if(_3w!=_3z){_3x=_3y.e;continue;}else{return E(_3y.c);}}else{_3x=_3y.d;continue;}}else{return E(_3u);}}},_3A=function(_3B,_3C){return _3v(E(_3B),_3C);},_3D=new T(function(){return unCStr("Prelude.");}),_3E=new T(function(){return err(new T(function(){return _x(_3D,new T(function(){return unCStr("!!: negative index");}));}));}),_3F=new T(function(){return err(new T(function(){return _x(_3D,new T(function(){return unCStr("!!: index too large");}));}));}),_3G=function(_3H,_3I){while(1){var _3J=E(_3H);if(!_3J._){return E(_3F);}else{var _3K=E(_3I);if(!_3K){return E(_3J.a);}else{_3H=_3J.b;_3I=_3K-1|0;continue;}}}},_3L=function(_3M,_3N){if(_3N>=0){return _3G(_3M,_3N);}else{return E(_3E);}},_3O=function(_3P,_3Q){return E(_3P)==E(_3Q);},_3R=function(_3S,_3T){while(1){var _3U=E(_3S);if(!_3U._){return (E(_3T)._==0)?true:false;}else{var _3V=E(_3T);if(!_3V._){return false;}else{if(E(_3U.a)!=E(_3V.a)){return false;}else{_3S=_3U.b;_3T=_3V.b;continue;}}}}},_3W=function(_3X,_3Y,_3Z,_40,_41,_42){if(!_3R(_3X,_40)){return false;}else{var _43=E(_3Y),_44=E(_41);if(E(_43.a)!=E(_44.a)){return false;}else{if(E(_43.b)!=E(_44.b)){return false;}else{var _45=E(_3Z),_46=E(_42);if(E(_45.a)!=E(_46.a)){return false;}else{return _3O(_45.b,_46.b);}}}}},_47=function(_48,_49){switch(E(_48)._){case 0:switch(E(_49)._){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_49)._){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_49)._){case 2:return 1;case 3:return 0;default:return 2;}break;default:return (E(_49)._==3)?1:2;}},_4a=new T(function(){return unCStr("end of input");}),_4b=new T(function(){return unCStr("unexpected");}),_4c=new T(function(){return unCStr("expecting");}),_4d=new T(function(){return unCStr("unknown parse error");}),_4e=new T(function(){return unCStr("or");}),_4f=new T(function(){return unCStr(")");}),_4g=function(_4h,_4i,_4j){var _4k=new T(function(){var _4l=new T(function(){var _4m=new T(function(){return unAppCStr(", column ",new T(function(){return _x(_2e(0,_4j,__Z),_4f);}));},1);return _x(_2e(0,_4i,__Z),_4m);});return unAppCStr("(line ",_4l);}),_4n=E(_4h);if(!_4n._){return E(_4k);}else{var _4o=new T(function(){return _x(_4n,new T(function(){return unAppCStr("\" ",_4k);},1));});return unAppCStr("\"",_4o);}},_4p=function(_4q,_4r){var _4s=E(_4r);if(!_4s._){return new T2(0,__Z,__Z);}else{var _4t=_4s.a;if(!B(A1(_4q,_4t))){return new T2(0,__Z,_4s);}else{var _4u=new T(function(){var _4v=_4p(_4q,_4s.b);return new T2(0,_4v.a,_4v.b);});return new T2(0,new T2(1,_4t,new T(function(){return E(E(_4u).a);})),new T(function(){return E(E(_4u).b);}));}}},_4w=new T(function(){return unCStr(", ");}),_4x=function(_4y){return (E(_4y)._==0)?false:true;},_4z=function(_4A,_4B){while(1){var _4C=(function(_4D,_4E){var _4F=E(_4E);if(!_4F._){return __Z;}else{var _4G=_4F.a,_4H=_4F.b;if(!B(A1(_4D,_4G))){var _4I=_4D;_4A=_4I;_4B=_4H;return __continue;}else{return new T2(1,_4G,new T(function(){return _4z(_4D,_4H);}));}}})(_4A,_4B);if(_4C!=__continue){return _4C;}}},_4J=new T(function(){return unCStr("\n");}),_4K=function(_4L){var _4M=E(_4L);if(!_4M._){return __Z;}else{return _x(_x(_4J,_4M.a),new T(function(){return _4K(_4M.b);},1));}},_4N=function(_4O,_4P){while(1){var _4Q=E(_4O);if(!_4Q._){return E(_4P);}else{_4O=_4Q.b;_4P=_4Q.a;continue;}}},_4R=function(_4S,_4T){var _4U=E(_4T);return (_4U._==0)?__Z:new T2(1,_4S,new T(function(){return _4R(_4U.a,_4U.b);}));},_4V=new T(function(){return unCStr(": empty list");}),_4W=function(_4X){return err(_x(_3D,new T(function(){return _x(_4X,_4V);},1)));},_4Y=new T(function(){return _4W(new T(function(){return unCStr("last");}));}),_4Z=function(_50){switch(E(_50)._){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_51=function(_52){return (E(_52)._==1)?true:false;},_53=function(_54){return (E(_54)._==2)?true:false;},_55=function(_56,_57){var _58=E(_57);return (_58._==0)?__Z:new T2(1,new T(function(){return B(A1(_56,_58.a));}),new T(function(){return _55(_56,_58.b);}));},_59=function(_5a){var _5b=E(_5a);switch(_5b._){case 0:return E(_5b.a);case 1:return E(_5b.a);case 2:return E(_5b.a);default:return E(_5b.a);}},_5c=function(_5d,_5e,_5f){while(1){var _5g=E(_5f);if(!_5g._){return false;}else{if(!B(A2(_5d,_5g.a,_5e))){_5f=_5g.b;continue;}else{return true;}}}},_5h=function(_5i,_5j){var _5k=function(_5l,_5m){while(1){var _5n=(function(_5o,_5p){var _5q=E(_5o);if(!_5q._){return __Z;}else{var _5r=_5q.a,_5s=_5q.b;if(!_5c(_5i,_5r,_5p)){return new T2(1,_5r,new T(function(){return _5k(_5s,new T2(1,_5r,_5p));}));}else{var _5t=_5p;_5l=_5s;_5m=_5t;return __continue;}}})(_5l,_5m);if(_5n!=__continue){return _5n;}}};return _5k(_5j,__Z);},_5u=function(_5v,_5w){var _5x=E(_5w);if(!_5x._){return __Z;}else{var _5y=_5x.a,_5z=E(_5x.b);if(!_5z._){return E(_5y);}else{var _5A=new T(function(){return _x(_5v,new T(function(){return _5u(_5v,_5z);},1));},1);return _x(_5y,_5A);}}},_5B=function(_5C,_5D,_5E,_5F,_5G,_5H){var _5I=E(_5H);if(!_5I._){return E(_5D);}else{var _5J=new T(function(){var _5K=_4p(_4Z,_5I);return new T2(0,_5K.a,_5K.b);}),_5L=new T(function(){var _5M=_4p(_51,E(_5J).b);return new T2(0,_5M.a,_5M.b);}),_5N=new T(function(){return E(E(_5L).a);}),_5O=function(_5P){var _5Q=E(_5P);if(!_5Q._){return __Z;}else{var _5R=_5Q.a,_5S=E(_5Q.b);if(!_5S._){return E(_5R);}else{var _5T=new T(function(){var _5U=new T(function(){var _5V=new T(function(){return unAppCStr(" ",new T(function(){return _4N(_5Q,_4Y);}));},1);return _x(_5C,_5V);});return unAppCStr(" ",_5U);},1);return _x(_5u(_4w,_5h(_3R,_4z(_4x,_4R(_5R,_5S)))),_5T);}}},_5W=function(_5X,_5Y){var _5Z=_5h(_3R,_4z(_4x,_55(_59,_5Y)));if(!_5Z._){return __Z;}else{var _60=E(_5X);if(!_60._){return _5O(_5Z);}else{var _61=new T(function(){return unAppCStr(" ",new T(function(){return _5O(_5Z);}));},1);return _x(_60,_61);}}},_62=new T(function(){var _63=_4p(_53,E(_5L).b);return new T2(0,_63.a,_63.b);}),_64=new T(function(){if(!E(_5N)._){var _65=E(E(_5J).a);if(!_65._){return __Z;}else{var _66=E(_65.a);switch(_66._){case 0:var _67=E(_66.a);if(!_67._){return _x(_5F,new T(function(){return unAppCStr(" ",_5G);},1));}else{return _x(_5F,new T(function(){return unAppCStr(" ",_67);},1));}break;case 1:var _68=E(_66.a);if(!_68._){return _x(_5F,new T(function(){return unAppCStr(" ",_5G);},1));}else{return _x(_5F,new T(function(){return unAppCStr(" ",_68);},1));}break;case 2:var _69=E(_66.a);if(!_69._){return _x(_5F,new T(function(){return unAppCStr(" ",_5G);},1));}else{return _x(_5F,new T(function(){return unAppCStr(" ",_69);},1));}break;default:var _6a=E(_66.a);if(!_6a._){return _x(_5F,new T(function(){return unAppCStr(" ",_5G);},1));}else{return _x(_5F,new T(function(){return unAppCStr(" ",_6a);},1));}}}}else{return __Z;}});return _4K(_5h(_3R,_4z(_4x,new T2(1,_64,new T2(1,new T(function(){return _5W(_5F,_5N);}),new T2(1,new T(function(){return _5W(_5E,E(_62).a);}),new T2(1,new T(function(){return _5W(__Z,E(_62).b);}),__Z)))))));}},_6b=function(_6c,_6d){var _6e=function(_6f,_6g){var _6h=E(_6f);if(!_6h._){return E(_6g);}else{var _6i=_6h.a,_6j=E(_6g);if(!_6j._){return _6h;}else{var _6k=_6j.a;return (B(A2(_6c,_6i,_6k))==2)?new T2(1,_6k,new T(function(){return _6e(_6h,_6j.b);})):new T2(1,_6i,new T(function(){return _6e(_6h.b,_6j);}));}}},_6l=function(_6m){var _6n=E(_6m);if(!_6n._){return __Z;}else{var _6o=E(_6n.b);return (_6o._==0)?_6n:new T2(1,new T(function(){return _6e(_6n.a,_6o.a);}),new T(function(){return _6l(_6o.b);}));}},_6p=new T(function(){return _6q(_6l(__Z));}),_6q=function(_6r){while(1){var _6s=E(_6r);if(!_6s._){return E(_6p);}else{if(!E(_6s.b)._){return E(_6s.a);}else{_6r=_6l(_6s);continue;}}}},_6t=new T(function(){return _6u(__Z);}),_6v=function(_6w,_6x,_6y){while(1){var _6z=(function(_6A,_6B,_6C){var _6D=E(_6C);if(!_6D._){return new T2(1,new T2(1,_6A,_6B),_6t);}else{var _6E=_6D.a;if(B(A2(_6c,_6A,_6E))==2){var _6F=new T2(1,_6A,_6B);_6w=_6E;_6x=_6F;_6y=_6D.b;return __continue;}else{return new T2(1,new T2(1,_6A,_6B),new T(function(){return _6u(_6D);}));}}})(_6w,_6x,_6y);if(_6z!=__continue){return _6z;}}},_6G=function(_6H,_6I,_6J){while(1){var _6K=(function(_6L,_6M,_6N){var _6O=E(_6N);if(!_6O._){return new T2(1,new T(function(){return B(A1(_6M,new T2(1,_6L,__Z)));}),_6t);}else{var _6P=_6O.a,_6Q=_6O.b;switch(B(A2(_6c,_6L,_6P))){case 0:_6H=_6P;_6I=function(_6R){return C > 19 ? new F(function(){return A1(_6M,new T2(1,_6L,_6R));}) : (++C,A1(_6M,new T2(1,_6L,_6R)));};_6J=_6Q;return __continue;case 1:_6H=_6P;_6I=function(_6S){return C > 19 ? new F(function(){return A1(_6M,new T2(1,_6L,_6S));}) : (++C,A1(_6M,new T2(1,_6L,_6S)));};_6J=_6Q;return __continue;default:return new T2(1,new T(function(){return B(A1(_6M,new T2(1,_6L,__Z)));}),new T(function(){return _6u(_6O);}));}}})(_6H,_6I,_6J);if(_6K!=__continue){return _6K;}}},_6u=function(_6T){var _6U=E(_6T);if(!_6U._){return E(new T2(1,__Z,__Z));}else{var _6V=_6U.a,_6W=E(_6U.b);if(!_6W._){return new T2(1,_6U,__Z);}else{var _6X=_6W.a,_6Y=_6W.b;if(B(A2(_6c,_6V,_6X))==2){return _6v(_6X,new T2(1,_6V,__Z),_6Y);}else{return _6G(_6X,function(_6Z){return new T2(1,_6V,_6Z);},_6Y);}}}};return _6q(_6u(_6d));},_70=function(_71,_72,_73,_74){var _75=new T(function(){return unAppCStr(":",new T(function(){return _5B(_4e,_4d,_4c,_4b,_4a,_6b(_47,_74));}));},1);return _x(_4g(_71,_72,_73),_75);},_76=function(_77,_78,_){if(0>=_77){return 0;}else{var _79=function(_7a,_){while(1){var _7b=E(_7a);if(_7b==1){var _7c=B(A1(_78,_));return 0;}else{var _7d=B(A1(_78,_));_7a=_7b-1|0;continue;}}};return _79(_77,_);}},_7e=(function(ctx){ctx.beginPath();}),_7f=(function(ctx){ctx.fill();}),_7g=function(_7h,_7i,_){var _7j=_7e(_7i),_7k=B(A2(_7h,_7i,_)),_7l=_7f(_7i);return _3l(_);},_7m=(function(ctx,x,y){ctx.moveTo(x,y);}),_7n=(function(ctx,x,y){ctx.lineTo(x,y);}),_7o=function(_7p,_7q,_){var _7r=E(_7p);if(!_7r._){return 0;}else{var _7s=E(_7r.a),_7t=E(_7q),_7u=_7m(_7t,E(_7s.a),E(_7s.b)),_7v=E(_7r.b);if(!_7v._){return 0;}else{var _7w=E(_7v.a),_7x=_7n(_7t,E(_7w.a),E(_7w.b)),_7y=function(_7z,_){while(1){var _7A=E(_7z);if(!_7A._){return 0;}else{var _7B=E(_7A.a),_7C=_7n(_7t,E(_7B.a),E(_7B.b));_7z=_7A.b;continue;}}};return _7y(_7v.b,_);}}},_7D=function(_7E,_7F,_7G,_7H,_7I,_){return _7o(new T2(1,new T2(0,_7E,_7F),new T2(1,new T2(0,_7G,_7F),new T2(1,new T2(0,_7G,_7H),new T2(1,new T2(0,_7E,_7H),new T2(1,new T2(0,_7E,_7F),__Z))))),_7I,_);},_7J=function(_7K,_7L){while(1){var _7M=E(_7K);if(!_7M._){return E(_7L);}else{var _7N=_7L+1|0;_7K=_7M.b;_7L=_7N;continue;}}},_7O=new T(function(){return unCStr("base");}),_7P=new T(function(){return unCStr("Control.Exception.Base");}),_7Q=new T(function(){return unCStr("PatternMatchFail");}),_7R=function(_7S){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_7O,_7P,_7Q),__Z,__Z));},_7T=function(_7U){return E(E(_7U).a);},_7V=function(_7W,_7X){return _x(E(_7W).a,_7X);},_7Y=new T(function(){return new T5(0,_7R,new T3(0,function(_7Z,_80,_81){return _x(E(_80).a,_81);},_7T,function(_82,_83){return _1t(_7V,_82,_83);}),function(_84){return new T2(0,_7Y,_84);},function(_85){var _86=E(_85);return _m(_k(_86.a),_7R,_86.b);},_7T);}),_87=new T(function(){return unCStr("Non-exhaustive patterns in");}),_88=function(_89,_8a){return die(new T(function(){return B(A2(_1N,_8a,_89));}));},_8b=function(_8c,_8d){return _88(_8c,_8d);},_8e=new T(function(){return unCStr("\n");}),_8f=function(_8g){return (E(_8g)==124)?false:true;},_8h=function(_8i,_8j){var _8k=_4p(_8f,unCStr(_8i)),_8l=_8k.a,_8m=function(_8n,_8o){var _8p=new T(function(){var _8q=new T(function(){return _x(_8j,new T(function(){return _x(_8o,_8e);},1));});return unAppCStr(": ",_8q);},1);return _x(_8n,_8p);},_8r=E(_8k.b);if(!_8r._){return _8m(_8l,__Z);}else{if(E(_8r.a)==124){return _8m(_8l,new T2(1,32,_8r.b));}else{return _8m(_8l,__Z);}}},_8s=function(_8t){return _8b(new T1(0,new T(function(){return _8h(_8t,_87);})),_7Y);},_8u=new T(function(){return B(_8s("redcode.lhs:(208,1)-(218,45)|function resolve"));}),_8v=function(_8w,_8x){var _8y=_8w%_8x;if(_8w<=0){if(_8w>=0){return _8y;}else{if(_8x<=0){return _8y;}else{return (_8y==0)?0:_8y+_8x|0;}}}else{if(_8x>=0){if(_8w>=0){return _8y;}else{if(_8x<=0){return _8y;}else{return (_8y==0)?0:_8y+_8x|0;}}}else{return (_8y==0)?0:_8y+_8x|0;}}},_8z=function(_8A,_8B,_8C,_8D){while(1){switch(E(_8C)){case 35:return E(_8B);case 36:return _8v(_8B+E(_8D)|0,8000);case 60:_8C=64;continue;case 64:var _8E=_8v(_8B+E(_8D)|0,8000);return _8v(_8E+E(E(_3v(_8E,_8A).c).b)|0,8000);default:return E(_8u);}}},_8F=function(_8G,_8H){var _8I=E(_8H);if(!_8I._){return __Z;}else{var _8J=_8I.a,_8K=E(_8G);return (_8K==1)?new T2(1,_8J,__Z):new T2(1,_8J,new T(function(){return _8F(_8K-1|0,_8I.b);}));}},_8L=function(_8M,_8N){var _8O=E(_8N);switch(_8O._){case 0:return new T1(1,_8M);case 1:var _8P=function(_8Q){var _8R=E(_8O.a);return (_8R._==0)?new T4(2,_8Q+_8R.a|0,E(new T1(0,_8M)),__Z,E(new T1(0,_8R))):new T4(2,_8Q+_8R.a|0,E(new T1(0,_8M)),__Z,E(new T1(0,_8R)));},_8S=E(_8M);if(!_8S._){return _8P(_8S.a);}else{return _8P(_8S.a);}break;default:var _8T=_8O.a,_8U=_8O.c,_8V=_8O.d,_8W=E(_8O.b);switch(_8W._){case 0:var _8X=_8W.a,_8Y=E(_8M);return (_8Y._==0)?new T4(2,_8Y.a+_8T|0,E(new T2(1,_8Y,_8X)),_8U,E(_8V)):new T4(2,_8Y.a+_8T|0,E(new T2(1,_8Y,_8X)),_8U,E(_8V));case 1:var _8Z=_8W.a,_90=_8W.b,_91=E(_8M);return (_91._==0)?new T4(2,_91.a+_8T|0,E(new T3(2,_91,_8Z,_90)),_8U,E(_8V)):new T4(2,_91.a+_8T|0,E(new T3(2,_91,_8Z,_90)),_8U,E(_8V));case 2:var _92=_8W.a,_93=_8W.b,_94=_8W.c,_95=E(_8M);return (_95._==0)?new T4(2,_95.a+_8T|0,E(new T4(3,_95,_92,_93,_94)),_8U,E(_8V)):new T4(2,_95.a+_8T|0,E(new T4(3,_95,_92,_93,_94)),_8U,E(_8V));default:var _96=_8W.c,_97=_8W.d,_98=function(_99){var _9a=new T(function(){return _8L(new T(function(){var _9b=E(_8W.b);if(!_9b._){var _9c=_9b.a,_9d=E(_96);if(!_9d._){var _9e=_9d.a,_9f=E(_97);if(!_9f._){return new T4(1,(_9c+_9e|0)+_9f.a|0,_9b,_9d,_9f);}else{return new T4(1,(_9c+_9e|0)+_9f.a|0,_9b,_9d,_9f);}}else{var _9g=_9d.a,_9h=E(_97);if(!_9h._){return new T4(1,(_9c+_9g|0)+_9h.a|0,_9b,_9d,_9h);}else{return new T4(1,(_9c+_9g|0)+_9h.a|0,_9b,_9d,_9h);}}}else{var _9i=_9b.a,_9j=E(_96);if(!_9j._){var _9k=_9j.a,_9l=E(_97);if(!_9l._){return new T4(1,(_9i+_9k|0)+_9l.a|0,_9b,_9j,_9l);}else{return new T4(1,(_9i+_9k|0)+_9l.a|0,_9b,_9j,_9l);}}else{var _9m=_9j.a,_9n=E(_97);if(!_9n._){return new T4(1,(_9i+_9m|0)+_9n.a|0,_9b,_9j,_9n);}else{return new T4(1,(_9i+_9m|0)+_9n.a|0,_9b,_9j,_9n);}}}}),E(_8U));});return new T4(2,_99+_8T|0,E(new T2(1,_8M,_8W.a)),_9a,E(_8V));},_9o=E(_8M);if(!_9o._){return _98(_9o.a);}else{return _98(_9o.a);}}}},_9p=function(_9q,_9r,_9s,_9t,_9u){var _9v=E(_9u);switch(_9v._){case 0:return new T1(1,new T4(1,_9q,_9r,_9s,_9t));case 1:var _9w=E(_9v.a);return (_9w._==0)?new T4(2,_9q+_9w.a|0,E(new T1(0,new T4(1,_9q,_9r,_9s,_9t))),__Z,E(new T1(0,_9w))):new T4(2,_9q+_9w.a|0,E(new T1(0,new T4(1,_9q,_9r,_9s,_9t))),__Z,E(new T1(0,_9w)));default:var _9x=_9v.a,_9y=_9v.c,_9z=_9v.d,_9A=E(_9v.b);switch(_9A._){case 0:return new T4(2,_9q+_9x|0,E(new T2(1,new T4(1,_9q,_9r,_9s,_9t),_9A.a)),_9y,E(_9z));case 1:return new T4(2,_9q+_9x|0,E(new T3(2,new T4(1,_9q,_9r,_9s,_9t),_9A.a,_9A.b)),_9y,E(_9z));case 2:return new T4(2,_9q+_9x|0,E(new T4(3,new T4(1,_9q,_9r,_9s,_9t),_9A.a,_9A.b,_9A.c)),_9y,E(_9z));default:var _9B=_9A.c,_9C=_9A.d,_9D=new T(function(){return _8L(new T(function(){var _9E=E(_9A.b);if(!_9E._){var _9F=_9E.a,_9G=E(_9B);if(!_9G._){var _9H=_9G.a,_9I=E(_9C);if(!_9I._){return new T4(1,(_9F+_9H|0)+_9I.a|0,_9E,_9G,_9I);}else{return new T4(1,(_9F+_9H|0)+_9I.a|0,_9E,_9G,_9I);}}else{var _9J=_9G.a,_9K=E(_9C);if(!_9K._){return new T4(1,(_9F+_9J|0)+_9K.a|0,_9E,_9G,_9K);}else{return new T4(1,(_9F+_9J|0)+_9K.a|0,_9E,_9G,_9K);}}}else{var _9L=_9E.a,_9M=E(_9B);if(!_9M._){var _9N=_9M.a,_9O=E(_9C);if(!_9O._){return new T4(1,(_9L+_9N|0)+_9O.a|0,_9E,_9M,_9O);}else{return new T4(1,(_9L+_9N|0)+_9O.a|0,_9E,_9M,_9O);}}else{var _9P=_9M.a,_9Q=E(_9C);if(!_9Q._){return new T4(1,(_9L+_9P|0)+_9Q.a|0,_9E,_9M,_9Q);}else{return new T4(1,(_9L+_9P|0)+_9Q.a|0,_9E,_9M,_9Q);}}}}),E(_9y));});return new T4(2,_9q+_9x|0,E(new T2(1,new T4(1,_9q,_9r,_9s,_9t),_9A.a)),_9D,E(_9z));}}},_9R=function(_9S,_9T){var _9U=E(_9T);switch(_9U._){case 0:return new T1(1,_9S);case 1:return new T4(2,2,E(new T1(0,_9S)),__Z,E(new T1(0,_9U.a)));default:var _9V=_9U.a,_9W=_9U.c,_9X=_9U.d,_9Y=E(_9U.b);switch(_9Y._){case 0:return new T4(2,1+_9V|0,E(new T2(1,_9S,_9Y.a)),_9W,E(_9X));case 1:return new T4(2,1+_9V|0,E(new T3(2,_9S,_9Y.a,_9Y.b)),_9W,E(_9X));case 2:return new T4(2,1+_9V|0,E(new T4(3,_9S,_9Y.a,_9Y.b,_9Y.c)),_9W,E(_9X));default:return new T4(2,1+_9V|0,E(new T2(1,_9S,_9Y.a)),new T(function(){return _9p(3,_9Y.b,_9Y.c,_9Y.d,E(_9W));}),E(_9X));}}},_9Z=function(_a0,_a1){var _a2=E(_a0);switch(_a2._){case 0:return new T1(1,_a1);case 1:var _a3=_a2.a,_a4=function(_a5){var _a6=E(_a1);return (_a6._==0)?new T4(2,_a5+_a6.a|0,E(new T1(0,_a3)),__Z,E(new T1(0,_a6))):new T4(2,_a5+_a6.a|0,E(new T1(0,_a3)),__Z,E(new T1(0,_a6)));},_a7=E(_a3);if(!_a7._){return _a4(_a7.a);}else{return _a4(_a7.a);}break;default:var _a8=_a2.a,_a9=_a2.b,_aa=_a2.c,_ab=E(_a2.d);switch(_ab._){case 0:var _ac=_ab.a,_ad=E(_a1);return (_ad._==0)?new T4(2,_a8+_ad.a|0,E(_a9),_aa,E(new T2(1,_ac,_ad))):new T4(2,_a8+_ad.a|0,E(_a9),_aa,E(new T2(1,_ac,_ad)));case 1:var _ae=_ab.a,_af=_ab.b,_ag=E(_a1);return (_ag._==0)?new T4(2,_a8+_ag.a|0,E(_a9),_aa,E(new T3(2,_ae,_af,_ag))):new T4(2,_a8+_ag.a|0,E(_a9),_aa,E(new T3(2,_ae,_af,_ag)));case 2:var _ah=_ab.a,_ai=_ab.b,_aj=_ab.c,_ak=E(_a1);return (_ak._==0)?new T4(2,_a8+_ak.a|0,E(_a9),_aa,E(new T4(3,_ah,_ai,_aj,_ak))):new T4(2,_a8+_ak.a|0,E(_a9),_aa,E(new T4(3,_ah,_ai,_aj,_ak)));default:var _al=_ab.b,_am=_ab.c,_an=function(_ao){var _ap=new T(function(){return _9Z(E(_aa),new T(function(){var _aq=E(_ab.a);if(!_aq._){var _ar=_aq.a,_as=E(_al);if(!_as._){var _at=_as.a,_au=E(_am);if(!_au._){return new T4(1,(_ar+_at|0)+_au.a|0,_aq,_as,_au);}else{return new T4(1,(_ar+_at|0)+_au.a|0,_aq,_as,_au);}}else{var _av=_as.a,_aw=E(_am);if(!_aw._){return new T4(1,(_ar+_av|0)+_aw.a|0,_aq,_as,_aw);}else{return new T4(1,(_ar+_av|0)+_aw.a|0,_aq,_as,_aw);}}}else{var _ax=_aq.a,_ay=E(_al);if(!_ay._){var _az=_ay.a,_aA=E(_am);if(!_aA._){return new T4(1,(_ax+_az|0)+_aA.a|0,_aq,_ay,_aA);}else{return new T4(1,(_ax+_az|0)+_aA.a|0,_aq,_ay,_aA);}}else{var _aB=_ay.a,_aC=E(_am);if(!_aC._){return new T4(1,(_ax+_aB|0)+_aC.a|0,_aq,_ay,_aC);}else{return new T4(1,(_ax+_aB|0)+_aC.a|0,_aq,_ay,_aC);}}}}));});return new T4(2,_a8+_ao|0,E(_a9),_ap,E(new T2(1,_ab.d,_a1)));},_aD=E(_a1);if(!_aD._){return _an(_aD.a);}else{return _an(_aD.a);}}}},_aE=function(_aF,_aG,_aH,_aI,_aJ){var _aK=E(_aI);switch(_aK._){case 0:var _aL=_aK.a,_aM=E(_aJ);return (_aM._==0)?new T4(2,_aF+_aM.a|0,E(_aG),_aH,E(new T2(1,_aL,_aM))):new T4(2,_aF+_aM.a|0,E(_aG),_aH,E(new T2(1,_aL,_aM)));case 1:var _aN=_aK.a,_aO=_aK.b,_aP=E(_aJ);return (_aP._==0)?new T4(2,_aF+_aP.a|0,E(_aG),_aH,E(new T3(2,_aN,_aO,_aP))):new T4(2,_aF+_aP.a|0,E(_aG),_aH,E(new T3(2,_aN,_aO,_aP)));case 2:var _aQ=_aK.a,_aR=_aK.b,_aS=_aK.c,_aT=E(_aJ);return (_aT._==0)?new T4(2,_aF+_aT.a|0,E(_aG),_aH,E(new T4(3,_aQ,_aR,_aS,_aT))):new T4(2,_aF+_aT.a|0,E(_aG),_aH,E(new T4(3,_aQ,_aR,_aS,_aT)));default:var _aU=_aK.b,_aV=_aK.c,_aW=function(_aX){var _aY=new T(function(){return _9Z(E(_aH),new T(function(){var _aZ=E(_aK.a);if(!_aZ._){var _b0=_aZ.a,_b1=E(_aU);if(!_b1._){var _b2=_b1.a,_b3=E(_aV);if(!_b3._){return new T4(1,(_b0+_b2|0)+_b3.a|0,_aZ,_b1,_b3);}else{return new T4(1,(_b0+_b2|0)+_b3.a|0,_aZ,_b1,_b3);}}else{var _b4=_b1.a,_b5=E(_aV);if(!_b5._){return new T4(1,(_b0+_b4|0)+_b5.a|0,_aZ,_b1,_b5);}else{return new T4(1,(_b0+_b4|0)+_b5.a|0,_aZ,_b1,_b5);}}}else{var _b6=_aZ.a,_b7=E(_aU);if(!_b7._){var _b8=_b7.a,_b9=E(_aV);if(!_b9._){return new T4(1,(_b6+_b8|0)+_b9.a|0,_aZ,_b7,_b9);}else{return new T4(1,(_b6+_b8|0)+_b9.a|0,_aZ,_b7,_b9);}}else{var _ba=_b7.a,_bb=E(_aV);if(!_bb._){return new T4(1,(_b6+_ba|0)+_bb.a|0,_aZ,_b7,_bb);}else{return new T4(1,(_b6+_ba|0)+_bb.a|0,_aZ,_b7,_bb);}}}}));});return new T4(2,_aF+_aX|0,E(_aG),_aY,E(new T2(1,_aK.d,_aJ)));},_bc=E(_aJ);if(!_bc._){return _aW(_bc.a);}else{return _aW(_bc.a);}}},_bd=function(_be,_bf,_bg,_bh,_bi,_bj){var _bk=E(_be);if(!_bk._){return _8L(_bf,_8L(_bg,_8L(_bh,_8L(_bi,_bj))));}else{var _bl=E(_bj);if(!_bl._){return _9Z(_9Z(_9Z(_9Z(_bk,_bf),_bg),_bh),_bi);}else{if(_bk._==1){return _8L(_bk.a,_8L(_bf,_8L(_bg,_8L(_bh,_8L(_bi,_bl)))));}else{var _bm=_bk.a,_bn=_bk.b,_bo=_bk.c,_bp=_bk.d;if(_bl._==1){return _9Z(_9Z(_9Z(_9Z(_aE(_bm,_bn,_bo,_bp,_bf),_bg),_bh),_bi),_bl.a);}else{var _bq=_bl.b,_br=_bl.c,_bs=function(_bt){var _bu=function(_bv){var _bw=function(_bx){var _by=function(_bz){var _bA=new T(function(){var _bB=E(_bp);switch(_bB._){case 0:var _bC=_bB.a,_bD=E(_bq);switch(_bD._){case 0:var _bE=_bD.a,_bF=new T(function(){var _bG=function(_bH){var _bI=E(_bi);if(!_bI._){var _bJ=_bI.a,_bK=E(_bE);return (_bK._==0)?new T4(1,(_bH+_bJ|0)+_bK.a|0,_bh,_bI,_bK):new T4(1,(_bH+_bJ|0)+_bK.a|0,_bh,_bI,_bK);}else{var _bL=_bI.a,_bM=E(_bE);return (_bM._==0)?new T4(1,(_bH+_bL|0)+_bM.a|0,_bh,_bI,_bM):new T4(1,(_bH+_bL|0)+_bM.a|0,_bh,_bI,_bM);}},_bN=E(_bh);if(!_bN._){return _bG(_bN.a);}else{return _bG(_bN.a);}}),_bO=new T(function(){var _bP=function(_bQ){var _bR=E(_bf);if(!_bR._){var _bS=_bR.a,_bT=E(_bg);return (_bT._==0)?new T4(1,(_bQ+_bS|0)+_bT.a|0,_bC,_bR,_bT):new T4(1,(_bQ+_bS|0)+_bT.a|0,_bC,_bR,_bT);}else{var _bU=_bR.a,_bV=E(_bg);return (_bV._==0)?new T4(1,(_bQ+_bU|0)+_bV.a|0,_bC,_bR,_bV):new T4(1,(_bQ+_bU|0)+_bV.a|0,_bC,_bR,_bV);}},_bW=E(_bC);if(!_bW._){return _bP(_bW.a);}else{return _bP(_bW.a);}});return _bX(_bo,_bO,_bF,_br);break;case 1:var _bY=_bD.b,_bZ=new T(function(){var _c0=function(_c1){var _c2=E(_bf);if(!_c2._){var _c3=_c2.a,_c4=E(_bg);return (_c4._==0)?new T4(1,(_c1+_c3|0)+_c4.a|0,_bC,_c2,_c4):new T4(1,(_c1+_c3|0)+_c4.a|0,_bC,_c2,_c4);}else{var _c5=_c2.a,_c6=E(_bg);return (_c6._==0)?new T4(1,(_c1+_c5|0)+_c6.a|0,_bC,_c2,_c6):new T4(1,(_c1+_c5|0)+_c6.a|0,_bC,_c2,_c6);}},_c7=E(_bC);if(!_c7._){return _c0(_c7.a);}else{return _c0(_c7.a);}});return B(_c8(_bo,_bZ,new T(function(){var _c9=E(_bh);if(!_c9._){var _ca=_c9.a,_cb=E(_bi);if(!_cb._){return new T3(0,_ca+_cb.a|0,_c9,_cb);}else{return new T3(0,_ca+_cb.a|0,_c9,_cb);}}else{var _cc=_c9.a,_cd=E(_bi);if(!_cd._){return new T3(0,_cc+_cd.a|0,_c9,_cd);}else{return new T3(0,_cc+_cd.a|0,_c9,_cd);}}}),new T(function(){var _ce=E(_bD.a);if(!_ce._){var _cf=_ce.a,_cg=E(_bY);if(!_cg._){return new T3(0,_cf+_cg.a|0,_ce,_cg);}else{return new T3(0,_cf+_cg.a|0,_ce,_cg);}}else{var _ch=_ce.a,_ci=E(_bY);if(!_ci._){return new T3(0,_ch+_ci.a|0,_ce,_ci);}else{return new T3(0,_ch+_ci.a|0,_ce,_ci);}}}),_br));break;case 2:var _cj=_bD.a,_ck=_bD.c,_cl=new T(function(){var _cm=function(_cn){var _co=E(_bi);if(!_co._){var _cp=_co.a,_cq=E(_cj);return (_cq._==0)?new T4(1,(_cn+_cp|0)+_cq.a|0,_bh,_co,_cq):new T4(1,(_cn+_cp|0)+_cq.a|0,_bh,_co,_cq);}else{var _cr=_co.a,_cs=E(_cj);return (_cs._==0)?new T4(1,(_cn+_cr|0)+_cs.a|0,_bh,_co,_cs):new T4(1,(_cn+_cr|0)+_cs.a|0,_bh,_co,_cs);}},_ct=E(_bh);if(!_ct._){return _cm(_ct.a);}else{return _cm(_ct.a);}}),_cu=new T(function(){var _cv=function(_cw){var _cx=E(_bf);if(!_cx._){var _cy=_cx.a,_cz=E(_bg);return (_cz._==0)?new T4(1,(_cw+_cy|0)+_cz.a|0,_bC,_cx,_cz):new T4(1,(_cw+_cy|0)+_cz.a|0,_bC,_cx,_cz);}else{var _cA=_cx.a,_cB=E(_bg);return (_cB._==0)?new T4(1,(_cw+_cA|0)+_cB.a|0,_bC,_cx,_cB):new T4(1,(_cw+_cA|0)+_cB.a|0,_bC,_cx,_cB);}},_cC=E(_bC);if(!_cC._){return _cv(_cC.a);}else{return _cv(_cC.a);}});return B(_c8(_bo,_cu,_cl,new T(function(){var _cD=E(_bD.b);if(!_cD._){var _cE=_cD.a,_cF=E(_ck);if(!_cF._){return new T3(0,_cE+_cF.a|0,_cD,_cF);}else{return new T3(0,_cE+_cF.a|0,_cD,_cF);}}else{var _cG=_cD.a,_cH=E(_ck);if(!_cH._){return new T3(0,_cG+_cH.a|0,_cD,_cH);}else{return new T3(0,_cG+_cH.a|0,_cD,_cH);}}}),_br));break;default:var _cI=_bD.a,_cJ=_bD.b,_cK=_bD.d,_cL=new T(function(){var _cM=function(_cN){var _cO=E(_bD.c);if(!_cO._){var _cP=_cO.a,_cQ=E(_cK);return (_cQ._==0)?new T4(1,(_cN+_cP|0)+_cQ.a|0,_cJ,_cO,_cQ):new T4(1,(_cN+_cP|0)+_cQ.a|0,_cJ,_cO,_cQ);}else{var _cR=_cO.a,_cS=E(_cK);return (_cS._==0)?new T4(1,(_cN+_cR|0)+_cS.a|0,_cJ,_cO,_cS):new T4(1,(_cN+_cR|0)+_cS.a|0,_cJ,_cO,_cS);}},_cT=E(_cJ);if(!_cT._){return _cM(_cT.a);}else{return _cM(_cT.a);}}),_cU=new T(function(){var _cV=function(_cW){var _cX=E(_bi);if(!_cX._){var _cY=_cX.a,_cZ=E(_cI);return (_cZ._==0)?new T4(1,(_cW+_cY|0)+_cZ.a|0,_bh,_cX,_cZ):new T4(1,(_cW+_cY|0)+_cZ.a|0,_bh,_cX,_cZ);}else{var _d0=_cX.a,_d1=E(_cI);return (_d1._==0)?new T4(1,(_cW+_d0|0)+_d1.a|0,_bh,_cX,_d1):new T4(1,(_cW+_d0|0)+_d1.a|0,_bh,_cX,_d1);}},_d2=E(_bh);if(!_d2._){return _cV(_d2.a);}else{return _cV(_d2.a);}}),_d3=new T(function(){var _d4=function(_d5){var _d6=E(_bf);if(!_d6._){var _d7=_d6.a,_d8=E(_bg);return (_d8._==0)?new T4(1,(_d5+_d7|0)+_d8.a|0,_bC,_d6,_d8):new T4(1,(_d5+_d7|0)+_d8.a|0,_bC,_d6,_d8);}else{var _d9=_d6.a,_da=E(_bg);return (_da._==0)?new T4(1,(_d5+_d9|0)+_da.a|0,_bC,_d6,_da):new T4(1,(_d5+_d9|0)+_da.a|0,_bC,_d6,_da);}},_db=E(_bC);if(!_db._){return _d4(_db.a);}else{return _d4(_db.a);}});return B(_c8(_bo,_d3,_cU,_cL,_br));}break;case 1:var _dc=_bB.a,_dd=_bB.b,_de=E(_bq);switch(_de._){case 0:var _df=_de.a,_dg=new T(function(){var _dh=function(_di){var _dj=E(_dd);if(!_dj._){var _dk=_dj.a,_dl=E(_bf);return (_dl._==0)?new T4(1,(_di+_dk|0)+_dl.a|0,_dc,_dj,_dl):new T4(1,(_di+_dk|0)+_dl.a|0,_dc,_dj,_dl);}else{var _dm=_dj.a,_dn=E(_bf);return (_dn._==0)?new T4(1,(_di+_dm|0)+_dn.a|0,_dc,_dj,_dn):new T4(1,(_di+_dm|0)+_dn.a|0,_dc,_dj,_dn);}},_do=E(_dc);if(!_do._){return _dh(_do.a);}else{return _dh(_do.a);}});return B(_c8(_bo,_dg,new T(function(){var _dp=E(_bg);if(!_dp._){var _dq=_dp.a,_dr=E(_bh);if(!_dr._){return new T3(0,_dq+_dr.a|0,_dp,_dr);}else{return new T3(0,_dq+_dr.a|0,_dp,_dr);}}else{var _ds=_dp.a,_dt=E(_bh);if(!_dt._){return new T3(0,_ds+_dt.a|0,_dp,_dt);}else{return new T3(0,_ds+_dt.a|0,_dp,_dt);}}}),new T(function(){var _du=E(_bi);if(!_du._){var _dv=_du.a,_dw=E(_df);if(!_dw._){return new T3(0,_dv+_dw.a|0,_du,_dw);}else{return new T3(0,_dv+_dw.a|0,_du,_dw);}}else{var _dx=_du.a,_dy=E(_df);if(!_dy._){return new T3(0,_dx+_dy.a|0,_du,_dy);}else{return new T3(0,_dx+_dy.a|0,_du,_dy);}}}),_br));break;case 1:var _dz=_de.b,_dA=new T(function(){var _dB=function(_dC){var _dD=E(_bh);if(!_dD._){var _dE=_dD.a,_dF=E(_bi);return (_dF._==0)?new T4(1,(_dC+_dE|0)+_dF.a|0,_bg,_dD,_dF):new T4(1,(_dC+_dE|0)+_dF.a|0,_bg,_dD,_dF);}else{var _dG=_dD.a,_dH=E(_bi);return (_dH._==0)?new T4(1,(_dC+_dG|0)+_dH.a|0,_bg,_dD,_dH):new T4(1,(_dC+_dG|0)+_dH.a|0,_bg,_dD,_dH);}},_dI=E(_bg);if(!_dI._){return _dB(_dI.a);}else{return _dB(_dI.a);}}),_dJ=new T(function(){var _dK=function(_dL){var _dM=E(_dd);if(!_dM._){var _dN=_dM.a,_dO=E(_bf);return (_dO._==0)?new T4(1,(_dL+_dN|0)+_dO.a|0,_dc,_dM,_dO):new T4(1,(_dL+_dN|0)+_dO.a|0,_dc,_dM,_dO);}else{var _dP=_dM.a,_dQ=E(_bf);return (_dQ._==0)?new T4(1,(_dL+_dP|0)+_dQ.a|0,_dc,_dM,_dQ):new T4(1,(_dL+_dP|0)+_dQ.a|0,_dc,_dM,_dQ);}},_dR=E(_dc);if(!_dR._){return _dK(_dR.a);}else{return _dK(_dR.a);}});return B(_c8(_bo,_dJ,_dA,new T(function(){var _dS=E(_de.a);if(!_dS._){var _dT=_dS.a,_dU=E(_dz);if(!_dU._){return new T3(0,_dT+_dU.a|0,_dS,_dU);}else{return new T3(0,_dT+_dU.a|0,_dS,_dU);}}else{var _dV=_dS.a,_dW=E(_dz);if(!_dW._){return new T3(0,_dV+_dW.a|0,_dS,_dW);}else{return new T3(0,_dV+_dW.a|0,_dS,_dW);}}}),_br));break;case 2:var _dX=_de.a,_dY=_de.c,_dZ=new T(function(){var _e0=function(_e1){var _e2=E(_de.b);if(!_e2._){var _e3=_e2.a,_e4=E(_dY);return (_e4._==0)?new T4(1,(_e1+_e3|0)+_e4.a|0,_dX,_e2,_e4):new T4(1,(_e1+_e3|0)+_e4.a|0,_dX,_e2,_e4);}else{var _e5=_e2.a,_e6=E(_dY);return (_e6._==0)?new T4(1,(_e1+_e5|0)+_e6.a|0,_dX,_e2,_e6):new T4(1,(_e1+_e5|0)+_e6.a|0,_dX,_e2,_e6);}},_e7=E(_dX);if(!_e7._){return _e0(_e7.a);}else{return _e0(_e7.a);}}),_e8=new T(function(){var _e9=function(_ea){var _eb=E(_bh);if(!_eb._){var _ec=_eb.a,_ed=E(_bi);return (_ed._==0)?new T4(1,(_ea+_ec|0)+_ed.a|0,_bg,_eb,_ed):new T4(1,(_ea+_ec|0)+_ed.a|0,_bg,_eb,_ed);}else{var _ee=_eb.a,_ef=E(_bi);return (_ef._==0)?new T4(1,(_ea+_ee|0)+_ef.a|0,_bg,_eb,_ef):new T4(1,(_ea+_ee|0)+_ef.a|0,_bg,_eb,_ef);}},_eg=E(_bg);if(!_eg._){return _e9(_eg.a);}else{return _e9(_eg.a);}}),_eh=new T(function(){var _ei=function(_ej){var _ek=E(_dd);if(!_ek._){var _el=_ek.a,_em=E(_bf);return (_em._==0)?new T4(1,(_ej+_el|0)+_em.a|0,_dc,_ek,_em):new T4(1,(_ej+_el|0)+_em.a|0,_dc,_ek,_em);}else{var _en=_ek.a,_eo=E(_bf);return (_eo._==0)?new T4(1,(_ej+_en|0)+_eo.a|0,_dc,_ek,_eo):new T4(1,(_ej+_en|0)+_eo.a|0,_dc,_ek,_eo);}},_ep=E(_dc);if(!_ep._){return _ei(_ep.a);}else{return _ei(_ep.a);}});return B(_c8(_bo,_eh,_e8,_dZ,_br));break;default:var _eq=_de.b,_er=_de.d,_es=new T(function(){var _et=function(_eu){var _ev=E(_bh);if(!_ev._){var _ew=_ev.a,_ex=E(_bi);return (_ex._==0)?new T4(1,(_eu+_ew|0)+_ex.a|0,_bg,_ev,_ex):new T4(1,(_eu+_ew|0)+_ex.a|0,_bg,_ev,_ex);}else{var _ey=_ev.a,_ez=E(_bi);return (_ez._==0)?new T4(1,(_eu+_ey|0)+_ez.a|0,_bg,_ev,_ez):new T4(1,(_eu+_ey|0)+_ez.a|0,_bg,_ev,_ez);}},_eA=E(_bg);if(!_eA._){return _et(_eA.a);}else{return _et(_eA.a);}}),_eB=new T(function(){var _eC=function(_eD){var _eE=E(_dd);if(!_eE._){var _eF=_eE.a,_eG=E(_bf);return (_eG._==0)?new T4(1,(_eD+_eF|0)+_eG.a|0,_dc,_eE,_eG):new T4(1,(_eD+_eF|0)+_eG.a|0,_dc,_eE,_eG);}else{var _eH=_eE.a,_eI=E(_bf);return (_eI._==0)?new T4(1,(_eD+_eH|0)+_eI.a|0,_dc,_eE,_eI):new T4(1,(_eD+_eH|0)+_eI.a|0,_dc,_eE,_eI);}},_eJ=E(_dc);if(!_eJ._){return _eC(_eJ.a);}else{return _eC(_eJ.a);}});return B(_bd(_bo,_eB,_es,new T(function(){var _eK=E(_de.a);if(!_eK._){var _eL=_eK.a,_eM=E(_eq);if(!_eM._){return new T3(0,_eL+_eM.a|0,_eK,_eM);}else{return new T3(0,_eL+_eM.a|0,_eK,_eM);}}else{var _eN=_eK.a,_eO=E(_eq);if(!_eO._){return new T3(0,_eN+_eO.a|0,_eK,_eO);}else{return new T3(0,_eN+_eO.a|0,_eK,_eO);}}}),new T(function(){var _eP=E(_de.c);if(!_eP._){var _eQ=_eP.a,_eR=E(_er);if(!_eR._){return new T3(0,_eQ+_eR.a|0,_eP,_eR);}else{return new T3(0,_eQ+_eR.a|0,_eP,_eR);}}else{var _eS=_eP.a,_eT=E(_er);if(!_eT._){return new T3(0,_eS+_eT.a|0,_eP,_eT);}else{return new T3(0,_eS+_eT.a|0,_eP,_eT);}}}),_br));}break;case 2:var _eU=_bB.a,_eV=_bB.b,_eW=_bB.c,_eX=E(_bq);switch(_eX._){case 0:var _eY=_eX.a,_eZ=new T(function(){var _f0=function(_f1){var _f2=E(_bg);if(!_f2._){var _f3=_f2.a,_f4=E(_bh);return (_f4._==0)?new T4(1,(_f1+_f3|0)+_f4.a|0,_bf,_f2,_f4):new T4(1,(_f1+_f3|0)+_f4.a|0,_bf,_f2,_f4);}else{var _f5=_f2.a,_f6=E(_bh);return (_f6._==0)?new T4(1,(_f1+_f5|0)+_f6.a|0,_bf,_f2,_f6):new T4(1,(_f1+_f5|0)+_f6.a|0,_bf,_f2,_f6);}},_f7=E(_bf);if(!_f7._){return _f0(_f7.a);}else{return _f0(_f7.a);}}),_f8=new T(function(){var _f9=function(_fa){var _fb=E(_eV);if(!_fb._){var _fc=_fb.a,_fd=E(_eW);return (_fd._==0)?new T4(1,(_fa+_fc|0)+_fd.a|0,_eU,_fb,_fd):new T4(1,(_fa+_fc|0)+_fd.a|0,_eU,_fb,_fd);}else{var _fe=_fb.a,_ff=E(_eW);return (_ff._==0)?new T4(1,(_fa+_fe|0)+_ff.a|0,_eU,_fb,_ff):new T4(1,(_fa+_fe|0)+_ff.a|0,_eU,_fb,_ff);}},_fg=E(_eU);if(!_fg._){return _f9(_fg.a);}else{return _f9(_fg.a);}});return B(_c8(_bo,_f8,_eZ,new T(function(){var _fh=E(_bi);if(!_fh._){var _fi=_fh.a,_fj=E(_eY);if(!_fj._){return new T3(0,_fi+_fj.a|0,_fh,_fj);}else{return new T3(0,_fi+_fj.a|0,_fh,_fj);}}else{var _fk=_fh.a,_fl=E(_eY);if(!_fl._){return new T3(0,_fk+_fl.a|0,_fh,_fl);}else{return new T3(0,_fk+_fl.a|0,_fh,_fl);}}}),_br));break;case 1:var _fm=_eX.b,_fn=new T(function(){var _fo=function(_fp){var _fq=E(_eX.a);if(!_fq._){var _fr=_fq.a,_fs=E(_fm);return (_fs._==0)?new T4(1,(_fp+_fr|0)+_fs.a|0,_bi,_fq,_fs):new T4(1,(_fp+_fr|0)+_fs.a|0,_bi,_fq,_fs);}else{var _ft=_fq.a,_fu=E(_fm);return (_fu._==0)?new T4(1,(_fp+_ft|0)+_fu.a|0,_bi,_fq,_fu):new T4(1,(_fp+_ft|0)+_fu.a|0,_bi,_fq,_fu);}},_fv=E(_bi);if(!_fv._){return _fo(_fv.a);}else{return _fo(_fv.a);}}),_fw=new T(function(){var _fx=function(_fy){var _fz=E(_bg);if(!_fz._){var _fA=_fz.a,_fB=E(_bh);return (_fB._==0)?new T4(1,(_fy+_fA|0)+_fB.a|0,_bf,_fz,_fB):new T4(1,(_fy+_fA|0)+_fB.a|0,_bf,_fz,_fB);}else{var _fC=_fz.a,_fD=E(_bh);return (_fD._==0)?new T4(1,(_fy+_fC|0)+_fD.a|0,_bf,_fz,_fD):new T4(1,(_fy+_fC|0)+_fD.a|0,_bf,_fz,_fD);}},_fE=E(_bf);if(!_fE._){return _fx(_fE.a);}else{return _fx(_fE.a);}}),_fF=new T(function(){var _fG=function(_fH){var _fI=E(_eV);if(!_fI._){var _fJ=_fI.a,_fK=E(_eW);return (_fK._==0)?new T4(1,(_fH+_fJ|0)+_fK.a|0,_eU,_fI,_fK):new T4(1,(_fH+_fJ|0)+_fK.a|0,_eU,_fI,_fK);}else{var _fL=_fI.a,_fM=E(_eW);return (_fM._==0)?new T4(1,(_fH+_fL|0)+_fM.a|0,_eU,_fI,_fM):new T4(1,(_fH+_fL|0)+_fM.a|0,_eU,_fI,_fM);}},_fN=E(_eU);if(!_fN._){return _fG(_fN.a);}else{return _fG(_fN.a);}});return B(_c8(_bo,_fF,_fw,_fn,_br));break;case 2:var _fO=_eX.a,_fP=_eX.c,_fQ=new T(function(){var _fR=function(_fS){var _fT=E(_bg);if(!_fT._){var _fU=_fT.a,_fV=E(_bh);return (_fV._==0)?new T4(1,(_fS+_fU|0)+_fV.a|0,_bf,_fT,_fV):new T4(1,(_fS+_fU|0)+_fV.a|0,_bf,_fT,_fV);}else{var _fW=_fT.a,_fX=E(_bh);return (_fX._==0)?new T4(1,(_fS+_fW|0)+_fX.a|0,_bf,_fT,_fX):new T4(1,(_fS+_fW|0)+_fX.a|0,_bf,_fT,_fX);}},_fY=E(_bf);if(!_fY._){return _fR(_fY.a);}else{return _fR(_fY.a);}}),_fZ=new T(function(){var _g0=function(_g1){var _g2=E(_eV);if(!_g2._){var _g3=_g2.a,_g4=E(_eW);return (_g4._==0)?new T4(1,(_g1+_g3|0)+_g4.a|0,_eU,_g2,_g4):new T4(1,(_g1+_g3|0)+_g4.a|0,_eU,_g2,_g4);}else{var _g5=_g2.a,_g6=E(_eW);return (_g6._==0)?new T4(1,(_g1+_g5|0)+_g6.a|0,_eU,_g2,_g6):new T4(1,(_g1+_g5|0)+_g6.a|0,_eU,_g2,_g6);}},_g7=E(_eU);if(!_g7._){return _g0(_g7.a);}else{return _g0(_g7.a);}});return B(_bd(_bo,_fZ,_fQ,new T(function(){var _g8=E(_bi);if(!_g8._){var _g9=_g8.a,_ga=E(_fO);if(!_ga._){return new T3(0,_g9+_ga.a|0,_g8,_ga);}else{return new T3(0,_g9+_ga.a|0,_g8,_ga);}}else{var _gb=_g8.a,_gc=E(_fO);if(!_gc._){return new T3(0,_gb+_gc.a|0,_g8,_gc);}else{return new T3(0,_gb+_gc.a|0,_g8,_gc);}}}),new T(function(){var _gd=E(_eX.b);if(!_gd._){var _ge=_gd.a,_gf=E(_fP);if(!_gf._){return new T3(0,_ge+_gf.a|0,_gd,_gf);}else{return new T3(0,_ge+_gf.a|0,_gd,_gf);}}else{var _gg=_gd.a,_gh=E(_fP);if(!_gh._){return new T3(0,_gg+_gh.a|0,_gd,_gh);}else{return new T3(0,_gg+_gh.a|0,_gd,_gh);}}}),_br));break;default:var _gi=_eX.b,_gj=_eX.d,_gk=new T(function(){var _gl=function(_gm){var _gn=E(_eX.a);if(!_gn._){var _go=_gn.a,_gp=E(_gi);return (_gp._==0)?new T4(1,(_gm+_go|0)+_gp.a|0,_bi,_gn,_gp):new T4(1,(_gm+_go|0)+_gp.a|0,_bi,_gn,_gp);}else{var _gq=_gn.a,_gr=E(_gi);return (_gr._==0)?new T4(1,(_gm+_gq|0)+_gr.a|0,_bi,_gn,_gr):new T4(1,(_gm+_gq|0)+_gr.a|0,_bi,_gn,_gr);}},_gs=E(_bi);if(!_gs._){return _gl(_gs.a);}else{return _gl(_gs.a);}}),_gt=new T(function(){var _gu=function(_gv){var _gw=E(_bg);if(!_gw._){var _gx=_gw.a,_gy=E(_bh);return (_gy._==0)?new T4(1,(_gv+_gx|0)+_gy.a|0,_bf,_gw,_gy):new T4(1,(_gv+_gx|0)+_gy.a|0,_bf,_gw,_gy);}else{var _gz=_gw.a,_gA=E(_bh);return (_gA._==0)?new T4(1,(_gv+_gz|0)+_gA.a|0,_bf,_gw,_gA):new T4(1,(_gv+_gz|0)+_gA.a|0,_bf,_gw,_gA);}},_gB=E(_bf);if(!_gB._){return _gu(_gB.a);}else{return _gu(_gB.a);}}),_gC=new T(function(){var _gD=function(_gE){var _gF=E(_eV);if(!_gF._){var _gG=_gF.a,_gH=E(_eW);return (_gH._==0)?new T4(1,(_gE+_gG|0)+_gH.a|0,_eU,_gF,_gH):new T4(1,(_gE+_gG|0)+_gH.a|0,_eU,_gF,_gH);}else{var _gI=_gF.a,_gJ=E(_eW);return (_gJ._==0)?new T4(1,(_gE+_gI|0)+_gJ.a|0,_eU,_gF,_gJ):new T4(1,(_gE+_gI|0)+_gJ.a|0,_eU,_gF,_gJ);}},_gK=E(_eU);if(!_gK._){return _gD(_gK.a);}else{return _gD(_gK.a);}});return B(_bd(_bo,_gC,_gt,_gk,new T(function(){var _gL=E(_eX.c);if(!_gL._){var _gM=_gL.a,_gN=E(_gj);if(!_gN._){return new T3(0,_gM+_gN.a|0,_gL,_gN);}else{return new T3(0,_gM+_gN.a|0,_gL,_gN);}}else{var _gO=_gL.a,_gP=E(_gj);if(!_gP._){return new T3(0,_gO+_gP.a|0,_gL,_gP);}else{return new T3(0,_gO+_gP.a|0,_gL,_gP);}}}),_br));}break;default:var _gQ=_bB.a,_gR=_bB.b,_gS=_bB.c,_gT=_bB.d,_gU=E(_bq);switch(_gU._){case 0:var _gV=_gU.a,_gW=new T(function(){var _gX=function(_gY){var _gZ=E(_bi);if(!_gZ._){var _h0=_gZ.a,_h1=E(_gV);return (_h1._==0)?new T4(1,(_gY+_h0|0)+_h1.a|0,_bh,_gZ,_h1):new T4(1,(_gY+_h0|0)+_h1.a|0,_bh,_gZ,_h1);}else{var _h2=_gZ.a,_h3=E(_gV);return (_h3._==0)?new T4(1,(_gY+_h2|0)+_h3.a|0,_bh,_gZ,_h3):new T4(1,(_gY+_h2|0)+_h3.a|0,_bh,_gZ,_h3);}},_h4=E(_bh);if(!_h4._){return _gX(_h4.a);}else{return _gX(_h4.a);}}),_h5=new T(function(){var _h6=function(_h7){var _h8=E(_bf);if(!_h8._){var _h9=_h8.a,_ha=E(_bg);return (_ha._==0)?new T4(1,(_h7+_h9|0)+_ha.a|0,_gT,_h8,_ha):new T4(1,(_h7+_h9|0)+_ha.a|0,_gT,_h8,_ha);}else{var _hb=_h8.a,_hc=E(_bg);return (_hc._==0)?new T4(1,(_h7+_hb|0)+_hc.a|0,_gT,_h8,_hc):new T4(1,(_h7+_hb|0)+_hc.a|0,_gT,_h8,_hc);}},_hd=E(_gT);if(!_hd._){return _h6(_hd.a);}else{return _h6(_hd.a);}}),_he=new T(function(){var _hf=function(_hg){var _hh=E(_gR);if(!_hh._){var _hi=_hh.a,_hj=E(_gS);return (_hj._==0)?new T4(1,(_hg+_hi|0)+_hj.a|0,_gQ,_hh,_hj):new T4(1,(_hg+_hi|0)+_hj.a|0,_gQ,_hh,_hj);}else{var _hk=_hh.a,_hl=E(_gS);return (_hl._==0)?new T4(1,(_hg+_hk|0)+_hl.a|0,_gQ,_hh,_hl):new T4(1,(_hg+_hk|0)+_hl.a|0,_gQ,_hh,_hl);}},_hm=E(_gQ);if(!_hm._){return _hf(_hm.a);}else{return _hf(_hm.a);}});return B(_c8(_bo,_he,_h5,_gW,_br));break;case 1:var _hn=_gU.b,_ho=new T(function(){var _hp=function(_hq){var _hr=E(_bf);if(!_hr._){var _hs=_hr.a,_ht=E(_bg);return (_ht._==0)?new T4(1,(_hq+_hs|0)+_ht.a|0,_gT,_hr,_ht):new T4(1,(_hq+_hs|0)+_ht.a|0,_gT,_hr,_ht);}else{var _hu=_hr.a,_hv=E(_bg);return (_hv._==0)?new T4(1,(_hq+_hu|0)+_hv.a|0,_gT,_hr,_hv):new T4(1,(_hq+_hu|0)+_hv.a|0,_gT,_hr,_hv);}},_hw=E(_gT);if(!_hw._){return _hp(_hw.a);}else{return _hp(_hw.a);}}),_hx=new T(function(){var _hy=function(_hz){var _hA=E(_gR);if(!_hA._){var _hB=_hA.a,_hC=E(_gS);return (_hC._==0)?new T4(1,(_hz+_hB|0)+_hC.a|0,_gQ,_hA,_hC):new T4(1,(_hz+_hB|0)+_hC.a|0,_gQ,_hA,_hC);}else{var _hD=_hA.a,_hE=E(_gS);return (_hE._==0)?new T4(1,(_hz+_hD|0)+_hE.a|0,_gQ,_hA,_hE):new T4(1,(_hz+_hD|0)+_hE.a|0,_gQ,_hA,_hE);}},_hF=E(_gQ);if(!_hF._){return _hy(_hF.a);}else{return _hy(_hF.a);}});return B(_bd(_bo,_hx,_ho,new T(function(){var _hG=E(_bh);if(!_hG._){var _hH=_hG.a,_hI=E(_bi);if(!_hI._){return new T3(0,_hH+_hI.a|0,_hG,_hI);}else{return new T3(0,_hH+_hI.a|0,_hG,_hI);}}else{var _hJ=_hG.a,_hK=E(_bi);if(!_hK._){return new T3(0,_hJ+_hK.a|0,_hG,_hK);}else{return new T3(0,_hJ+_hK.a|0,_hG,_hK);}}}),new T(function(){var _hL=E(_gU.a);if(!_hL._){var _hM=_hL.a,_hN=E(_hn);if(!_hN._){return new T3(0,_hM+_hN.a|0,_hL,_hN);}else{return new T3(0,_hM+_hN.a|0,_hL,_hN);}}else{var _hO=_hL.a,_hP=E(_hn);if(!_hP._){return new T3(0,_hO+_hP.a|0,_hL,_hP);}else{return new T3(0,_hO+_hP.a|0,_hL,_hP);}}}),_br));break;case 2:var _hQ=_gU.a,_hR=_gU.c,_hS=new T(function(){var _hT=function(_hU){var _hV=E(_bi);if(!_hV._){var _hW=_hV.a,_hX=E(_hQ);return (_hX._==0)?new T4(1,(_hU+_hW|0)+_hX.a|0,_bh,_hV,_hX):new T4(1,(_hU+_hW|0)+_hX.a|0,_bh,_hV,_hX);}else{var _hY=_hV.a,_hZ=E(_hQ);return (_hZ._==0)?new T4(1,(_hU+_hY|0)+_hZ.a|0,_bh,_hV,_hZ):new T4(1,(_hU+_hY|0)+_hZ.a|0,_bh,_hV,_hZ);}},_i0=E(_bh);if(!_i0._){return _hT(_i0.a);}else{return _hT(_i0.a);}}),_i1=new T(function(){var _i2=function(_i3){var _i4=E(_bf);if(!_i4._){var _i5=_i4.a,_i6=E(_bg);return (_i6._==0)?new T4(1,(_i3+_i5|0)+_i6.a|0,_gT,_i4,_i6):new T4(1,(_i3+_i5|0)+_i6.a|0,_gT,_i4,_i6);}else{var _i7=_i4.a,_i8=E(_bg);return (_i8._==0)?new T4(1,(_i3+_i7|0)+_i8.a|0,_gT,_i4,_i8):new T4(1,(_i3+_i7|0)+_i8.a|0,_gT,_i4,_i8);}},_i9=E(_gT);if(!_i9._){return _i2(_i9.a);}else{return _i2(_i9.a);}}),_ia=new T(function(){var _ib=function(_ic){var _id=E(_gR);if(!_id._){var _ie=_id.a,_if=E(_gS);return (_if._==0)?new T4(1,(_ic+_ie|0)+_if.a|0,_gQ,_id,_if):new T4(1,(_ic+_ie|0)+_if.a|0,_gQ,_id,_if);}else{var _ig=_id.a,_ih=E(_gS);return (_ih._==0)?new T4(1,(_ic+_ig|0)+_ih.a|0,_gQ,_id,_ih):new T4(1,(_ic+_ig|0)+_ih.a|0,_gQ,_id,_ih);}},_ii=E(_gQ);if(!_ii._){return _ib(_ii.a);}else{return _ib(_ii.a);}});return B(_bd(_bo,_ia,_i1,_hS,new T(function(){var _ij=E(_gU.b);if(!_ij._){var _ik=_ij.a,_il=E(_hR);if(!_il._){return new T3(0,_ik+_il.a|0,_ij,_il);}else{return new T3(0,_ik+_il.a|0,_ij,_il);}}else{var _im=_ij.a,_in=E(_hR);if(!_in._){return new T3(0,_im+_in.a|0,_ij,_in);}else{return new T3(0,_im+_in.a|0,_ij,_in);}}}),_br));break;default:var _io=_gU.a,_ip=_gU.b,_iq=_gU.d,_ir=new T(function(){var _is=function(_it){var _iu=E(_gU.c);if(!_iu._){var _iv=_iu.a,_iw=E(_iq);return (_iw._==0)?new T4(1,(_it+_iv|0)+_iw.a|0,_ip,_iu,_iw):new T4(1,(_it+_iv|0)+_iw.a|0,_ip,_iu,_iw);}else{var _ix=_iu.a,_iy=E(_iq);return (_iy._==0)?new T4(1,(_it+_ix|0)+_iy.a|0,_ip,_iu,_iy):new T4(1,(_it+_ix|0)+_iy.a|0,_ip,_iu,_iy);}},_iz=E(_ip);if(!_iz._){return _is(_iz.a);}else{return _is(_iz.a);}}),_iA=new T(function(){var _iB=function(_iC){var _iD=E(_bi);if(!_iD._){var _iE=_iD.a,_iF=E(_io);return (_iF._==0)?new T4(1,(_iC+_iE|0)+_iF.a|0,_bh,_iD,_iF):new T4(1,(_iC+_iE|0)+_iF.a|0,_bh,_iD,_iF);}else{var _iG=_iD.a,_iH=E(_io);return (_iH._==0)?new T4(1,(_iC+_iG|0)+_iH.a|0,_bh,_iD,_iH):new T4(1,(_iC+_iG|0)+_iH.a|0,_bh,_iD,_iH);}},_iI=E(_bh);if(!_iI._){return _iB(_iI.a);}else{return _iB(_iI.a);}}),_iJ=new T(function(){var _iK=function(_iL){var _iM=E(_bf);if(!_iM._){var _iN=_iM.a,_iO=E(_bg);return (_iO._==0)?new T4(1,(_iL+_iN|0)+_iO.a|0,_gT,_iM,_iO):new T4(1,(_iL+_iN|0)+_iO.a|0,_gT,_iM,_iO);}else{var _iP=_iM.a,_iQ=E(_bg);return (_iQ._==0)?new T4(1,(_iL+_iP|0)+_iQ.a|0,_gT,_iM,_iQ):new T4(1,(_iL+_iP|0)+_iQ.a|0,_gT,_iM,_iQ);}},_iR=E(_gT);if(!_iR._){return _iK(_iR.a);}else{return _iK(_iR.a);}}),_iS=new T(function(){var _iT=function(_iU){var _iV=E(_gR);if(!_iV._){var _iW=_iV.a,_iX=E(_gS);return (_iX._==0)?new T4(1,(_iU+_iW|0)+_iX.a|0,_gQ,_iV,_iX):new T4(1,(_iU+_iW|0)+_iX.a|0,_gQ,_iV,_iX);}else{var _iY=_iV.a,_iZ=E(_gS);return (_iZ._==0)?new T4(1,(_iU+_iY|0)+_iZ.a|0,_gQ,_iV,_iZ):new T4(1,(_iU+_iY|0)+_iZ.a|0,_gQ,_iV,_iZ);}},_j0=E(_gQ);if(!_j0._){return _iT(_j0.a);}else{return _iT(_j0.a);}});return B(_bd(_bo,_iS,_iJ,_iA,_ir,_br));}}});return new T4(2,((((_bm+_bt|0)+_bv|0)+_bx|0)+_bz|0)+_bl.a|0,E(_bn),_bA,E(_bl.d));},_j1=E(_bi);if(!_j1._){return _by(_j1.a);}else{return _by(_j1.a);}},_j2=E(_bh);if(!_j2._){return _bw(_j2.a);}else{return _bw(_j2.a);}},_j3=E(_bg);if(!_j3._){return _bu(_j3.a);}else{return _bu(_j3.a);}},_j4=E(_bf);if(!_j4._){return C > 19 ? new F(function(){return _bs(_j4.a);}) : (++C,_bs(_j4.a));}else{return C > 19 ? new F(function(){return _bs(_j4.a);}) : (++C,_bs(_j4.a));}}}}}},_c8=function(_j5,_j6,_j7,_j8,_j9){var _ja=E(_j5);if(!_ja._){return _8L(_j6,_8L(_j7,_8L(_j8,_j9)));}else{var _jb=E(_j9);if(!_jb._){return _9Z(_9Z(_9Z(_ja,_j6),_j7),_j8);}else{if(_ja._==1){return _8L(_ja.a,_8L(_j6,_8L(_j7,_8L(_j8,_jb))));}else{var _jc=_ja.a,_jd=_ja.b,_je=_ja.c,_jf=_ja.d;if(_jb._==1){return _9Z(_9Z(_9Z(_aE(_jc,_jd,_je,_jf,_j6),_j7),_j8),_jb.a);}else{var _jg=_jb.b,_jh=_jb.c,_ji=function(_jj){var _jk=function(_jl){var _jm=function(_jn){var _jo=new T(function(){var _jp=E(_jf);switch(_jp._){case 0:var _jq=_jp.a,_jr=E(_jg);switch(_jr._){case 0:var _js=_jr.a,_jt=new T(function(){var _ju=function(_jv){var _jw=E(_j6);if(!_jw._){var _jx=_jw.a,_jy=E(_j7);return (_jy._==0)?new T4(1,(_jv+_jx|0)+_jy.a|0,_jq,_jw,_jy):new T4(1,(_jv+_jx|0)+_jy.a|0,_jq,_jw,_jy);}else{var _jz=_jw.a,_jA=E(_j7);return (_jA._==0)?new T4(1,(_jv+_jz|0)+_jA.a|0,_jq,_jw,_jA):new T4(1,(_jv+_jz|0)+_jA.a|0,_jq,_jw,_jA);}},_jB=E(_jq);if(!_jB._){return _ju(_jB.a);}else{return _ju(_jB.a);}});return _bX(_je,_jt,new T(function(){var _jC=E(_j8);if(!_jC._){var _jD=_jC.a,_jE=E(_js);if(!_jE._){return new T3(0,_jD+_jE.a|0,_jC,_jE);}else{return new T3(0,_jD+_jE.a|0,_jC,_jE);}}else{var _jF=_jC.a,_jG=E(_js);if(!_jG._){return new T3(0,_jF+_jG.a|0,_jC,_jG);}else{return new T3(0,_jF+_jG.a|0,_jC,_jG);}}}),_jh);break;case 1:var _jH=_jr.b,_jI=new T(function(){var _jJ=function(_jK){var _jL=E(_jr.a);if(!_jL._){var _jM=_jL.a,_jN=E(_jH);return (_jN._==0)?new T4(1,(_jK+_jM|0)+_jN.a|0,_j8,_jL,_jN):new T4(1,(_jK+_jM|0)+_jN.a|0,_j8,_jL,_jN);}else{var _jO=_jL.a,_jP=E(_jH);return (_jP._==0)?new T4(1,(_jK+_jO|0)+_jP.a|0,_j8,_jL,_jP):new T4(1,(_jK+_jO|0)+_jP.a|0,_j8,_jL,_jP);}},_jQ=E(_j8);if(!_jQ._){return _jJ(_jQ.a);}else{return _jJ(_jQ.a);}}),_jR=new T(function(){var _jS=function(_jT){var _jU=E(_j6);if(!_jU._){var _jV=_jU.a,_jW=E(_j7);return (_jW._==0)?new T4(1,(_jT+_jV|0)+_jW.a|0,_jq,_jU,_jW):new T4(1,(_jT+_jV|0)+_jW.a|0,_jq,_jU,_jW);}else{var _jX=_jU.a,_jY=E(_j7);return (_jY._==0)?new T4(1,(_jT+_jX|0)+_jY.a|0,_jq,_jU,_jY):new T4(1,(_jT+_jX|0)+_jY.a|0,_jq,_jU,_jY);}},_jZ=E(_jq);if(!_jZ._){return _jS(_jZ.a);}else{return _jS(_jZ.a);}});return _bX(_je,_jR,_jI,_jh);break;case 2:var _k0=_jr.a,_k1=_jr.c,_k2=new T(function(){var _k3=function(_k4){var _k5=E(_j6);if(!_k5._){var _k6=_k5.a,_k7=E(_j7);return (_k7._==0)?new T4(1,(_k4+_k6|0)+_k7.a|0,_jq,_k5,_k7):new T4(1,(_k4+_k6|0)+_k7.a|0,_jq,_k5,_k7);}else{var _k8=_k5.a,_k9=E(_j7);return (_k9._==0)?new T4(1,(_k4+_k8|0)+_k9.a|0,_jq,_k5,_k9):new T4(1,(_k4+_k8|0)+_k9.a|0,_jq,_k5,_k9);}},_ka=E(_jq);if(!_ka._){return _k3(_ka.a);}else{return _k3(_ka.a);}});return B(_c8(_je,_k2,new T(function(){var _kb=E(_j8);if(!_kb._){var _kc=_kb.a,_kd=E(_k0);if(!_kd._){return new T3(0,_kc+_kd.a|0,_kb,_kd);}else{return new T3(0,_kc+_kd.a|0,_kb,_kd);}}else{var _ke=_kb.a,_kf=E(_k0);if(!_kf._){return new T3(0,_ke+_kf.a|0,_kb,_kf);}else{return new T3(0,_ke+_kf.a|0,_kb,_kf);}}}),new T(function(){var _kg=E(_jr.b);if(!_kg._){var _kh=_kg.a,_ki=E(_k1);if(!_ki._){return new T3(0,_kh+_ki.a|0,_kg,_ki);}else{return new T3(0,_kh+_ki.a|0,_kg,_ki);}}else{var _kj=_kg.a,_kk=E(_k1);if(!_kk._){return new T3(0,_kj+_kk.a|0,_kg,_kk);}else{return new T3(0,_kj+_kk.a|0,_kg,_kk);}}}),_jh));break;default:var _kl=_jr.b,_km=_jr.d,_kn=new T(function(){var _ko=function(_kp){var _kq=E(_jr.a);if(!_kq._){var _kr=_kq.a,_ks=E(_kl);return (_ks._==0)?new T4(1,(_kp+_kr|0)+_ks.a|0,_j8,_kq,_ks):new T4(1,(_kp+_kr|0)+_ks.a|0,_j8,_kq,_ks);}else{var _kt=_kq.a,_ku=E(_kl);return (_ku._==0)?new T4(1,(_kp+_kt|0)+_ku.a|0,_j8,_kq,_ku):new T4(1,(_kp+_kt|0)+_ku.a|0,_j8,_kq,_ku);}},_kv=E(_j8);if(!_kv._){return _ko(_kv.a);}else{return _ko(_kv.a);}}),_kw=new T(function(){var _kx=function(_ky){var _kz=E(_j6);if(!_kz._){var _kA=_kz.a,_kB=E(_j7);return (_kB._==0)?new T4(1,(_ky+_kA|0)+_kB.a|0,_jq,_kz,_kB):new T4(1,(_ky+_kA|0)+_kB.a|0,_jq,_kz,_kB);}else{var _kC=_kz.a,_kD=E(_j7);return (_kD._==0)?new T4(1,(_ky+_kC|0)+_kD.a|0,_jq,_kz,_kD):new T4(1,(_ky+_kC|0)+_kD.a|0,_jq,_kz,_kD);}},_kE=E(_jq);if(!_kE._){return _kx(_kE.a);}else{return _kx(_kE.a);}});return B(_c8(_je,_kw,_kn,new T(function(){var _kF=E(_jr.c);if(!_kF._){var _kG=_kF.a,_kH=E(_km);if(!_kH._){return new T3(0,_kG+_kH.a|0,_kF,_kH);}else{return new T3(0,_kG+_kH.a|0,_kF,_kH);}}else{var _kI=_kF.a,_kJ=E(_km);if(!_kJ._){return new T3(0,_kI+_kJ.a|0,_kF,_kJ);}else{return new T3(0,_kI+_kJ.a|0,_kF,_kJ);}}}),_jh));}break;case 1:var _kK=_jp.a,_kL=_jp.b,_kM=E(_jg);switch(_kM._){case 0:var _kN=_kM.a,_kO=new T(function(){var _kP=function(_kQ){var _kR=E(_j8);if(!_kR._){var _kS=_kR.a,_kT=E(_kN);return (_kT._==0)?new T4(1,(_kQ+_kS|0)+_kT.a|0,_j7,_kR,_kT):new T4(1,(_kQ+_kS|0)+_kT.a|0,_j7,_kR,_kT);}else{var _kU=_kR.a,_kV=E(_kN);return (_kV._==0)?new T4(1,(_kQ+_kU|0)+_kV.a|0,_j7,_kR,_kV):new T4(1,(_kQ+_kU|0)+_kV.a|0,_j7,_kR,_kV);}},_kW=E(_j7);if(!_kW._){return _kP(_kW.a);}else{return _kP(_kW.a);}}),_kX=new T(function(){var _kY=function(_kZ){var _l0=E(_kL);if(!_l0._){var _l1=_l0.a,_l2=E(_j6);return (_l2._==0)?new T4(1,(_kZ+_l1|0)+_l2.a|0,_kK,_l0,_l2):new T4(1,(_kZ+_l1|0)+_l2.a|0,_kK,_l0,_l2);}else{var _l3=_l0.a,_l4=E(_j6);return (_l4._==0)?new T4(1,(_kZ+_l3|0)+_l4.a|0,_kK,_l0,_l4):new T4(1,(_kZ+_l3|0)+_l4.a|0,_kK,_l0,_l4);}},_l5=E(_kK);if(!_l5._){return _kY(_l5.a);}else{return _kY(_l5.a);}});return _bX(_je,_kX,_kO,_jh);break;case 1:var _l6=_kM.b,_l7=new T(function(){var _l8=function(_l9){var _la=E(_kL);if(!_la._){var _lb=_la.a,_lc=E(_j6);return (_lc._==0)?new T4(1,(_l9+_lb|0)+_lc.a|0,_kK,_la,_lc):new T4(1,(_l9+_lb|0)+_lc.a|0,_kK,_la,_lc);}else{var _ld=_la.a,_le=E(_j6);return (_le._==0)?new T4(1,(_l9+_ld|0)+_le.a|0,_kK,_la,_le):new T4(1,(_l9+_ld|0)+_le.a|0,_kK,_la,_le);}},_lf=E(_kK);if(!_lf._){return _l8(_lf.a);}else{return _l8(_lf.a);}});return B(_c8(_je,_l7,new T(function(){var _lg=E(_j7);if(!_lg._){var _lh=_lg.a,_li=E(_j8);if(!_li._){return new T3(0,_lh+_li.a|0,_lg,_li);}else{return new T3(0,_lh+_li.a|0,_lg,_li);}}else{var _lj=_lg.a,_lk=E(_j8);if(!_lk._){return new T3(0,_lj+_lk.a|0,_lg,_lk);}else{return new T3(0,_lj+_lk.a|0,_lg,_lk);}}}),new T(function(){var _ll=E(_kM.a);if(!_ll._){var _lm=_ll.a,_ln=E(_l6);if(!_ln._){return new T3(0,_lm+_ln.a|0,_ll,_ln);}else{return new T3(0,_lm+_ln.a|0,_ll,_ln);}}else{var _lo=_ll.a,_lp=E(_l6);if(!_lp._){return new T3(0,_lo+_lp.a|0,_ll,_lp);}else{return new T3(0,_lo+_lp.a|0,_ll,_lp);}}}),_jh));break;case 2:var _lq=_kM.a,_lr=_kM.c,_ls=new T(function(){var _lt=function(_lu){var _lv=E(_j8);if(!_lv._){var _lw=_lv.a,_lx=E(_lq);return (_lx._==0)?new T4(1,(_lu+_lw|0)+_lx.a|0,_j7,_lv,_lx):new T4(1,(_lu+_lw|0)+_lx.a|0,_j7,_lv,_lx);}else{var _ly=_lv.a,_lz=E(_lq);return (_lz._==0)?new T4(1,(_lu+_ly|0)+_lz.a|0,_j7,_lv,_lz):new T4(1,(_lu+_ly|0)+_lz.a|0,_j7,_lv,_lz);}},_lA=E(_j7);if(!_lA._){return _lt(_lA.a);}else{return _lt(_lA.a);}}),_lB=new T(function(){var _lC=function(_lD){var _lE=E(_kL);if(!_lE._){var _lF=_lE.a,_lG=E(_j6);return (_lG._==0)?new T4(1,(_lD+_lF|0)+_lG.a|0,_kK,_lE,_lG):new T4(1,(_lD+_lF|0)+_lG.a|0,_kK,_lE,_lG);}else{var _lH=_lE.a,_lI=E(_j6);return (_lI._==0)?new T4(1,(_lD+_lH|0)+_lI.a|0,_kK,_lE,_lI):new T4(1,(_lD+_lH|0)+_lI.a|0,_kK,_lE,_lI);}},_lJ=E(_kK);if(!_lJ._){return _lC(_lJ.a);}else{return _lC(_lJ.a);}});return B(_c8(_je,_lB,_ls,new T(function(){var _lK=E(_kM.b);if(!_lK._){var _lL=_lK.a,_lM=E(_lr);if(!_lM._){return new T3(0,_lL+_lM.a|0,_lK,_lM);}else{return new T3(0,_lL+_lM.a|0,_lK,_lM);}}else{var _lN=_lK.a,_lO=E(_lr);if(!_lO._){return new T3(0,_lN+_lO.a|0,_lK,_lO);}else{return new T3(0,_lN+_lO.a|0,_lK,_lO);}}}),_jh));break;default:var _lP=_kM.a,_lQ=_kM.b,_lR=_kM.d,_lS=new T(function(){var _lT=function(_lU){var _lV=E(_kM.c);if(!_lV._){var _lW=_lV.a,_lX=E(_lR);return (_lX._==0)?new T4(1,(_lU+_lW|0)+_lX.a|0,_lQ,_lV,_lX):new T4(1,(_lU+_lW|0)+_lX.a|0,_lQ,_lV,_lX);}else{var _lY=_lV.a,_lZ=E(_lR);return (_lZ._==0)?new T4(1,(_lU+_lY|0)+_lZ.a|0,_lQ,_lV,_lZ):new T4(1,(_lU+_lY|0)+_lZ.a|0,_lQ,_lV,_lZ);}},_m0=E(_lQ);if(!_m0._){return _lT(_m0.a);}else{return _lT(_m0.a);}}),_m1=new T(function(){var _m2=function(_m3){var _m4=E(_j8);if(!_m4._){var _m5=_m4.a,_m6=E(_lP);return (_m6._==0)?new T4(1,(_m3+_m5|0)+_m6.a|0,_j7,_m4,_m6):new T4(1,(_m3+_m5|0)+_m6.a|0,_j7,_m4,_m6);}else{var _m7=_m4.a,_m8=E(_lP);return (_m8._==0)?new T4(1,(_m3+_m7|0)+_m8.a|0,_j7,_m4,_m8):new T4(1,(_m3+_m7|0)+_m8.a|0,_j7,_m4,_m8);}},_m9=E(_j7);if(!_m9._){return _m2(_m9.a);}else{return _m2(_m9.a);}}),_ma=new T(function(){var _mb=function(_mc){var _md=E(_kL);if(!_md._){var _me=_md.a,_mf=E(_j6);return (_mf._==0)?new T4(1,(_mc+_me|0)+_mf.a|0,_kK,_md,_mf):new T4(1,(_mc+_me|0)+_mf.a|0,_kK,_md,_mf);}else{var _mg=_md.a,_mh=E(_j6);return (_mh._==0)?new T4(1,(_mc+_mg|0)+_mh.a|0,_kK,_md,_mh):new T4(1,(_mc+_mg|0)+_mh.a|0,_kK,_md,_mh);}},_mi=E(_kK);if(!_mi._){return _mb(_mi.a);}else{return _mb(_mi.a);}});return B(_c8(_je,_ma,_m1,_lS,_jh));}break;case 2:var _mj=_jp.a,_mk=_jp.b,_ml=_jp.c,_mm=E(_jg);switch(_mm._){case 0:var _mn=_mm.a,_mo=new T(function(){var _mp=function(_mq){var _mr=E(_mk);if(!_mr._){var _ms=_mr.a,_mt=E(_ml);return (_mt._==0)?new T4(1,(_mq+_ms|0)+_mt.a|0,_mj,_mr,_mt):new T4(1,(_mq+_ms|0)+_mt.a|0,_mj,_mr,_mt);}else{var _mu=_mr.a,_mv=E(_ml);return (_mv._==0)?new T4(1,(_mq+_mu|0)+_mv.a|0,_mj,_mr,_mv):new T4(1,(_mq+_mu|0)+_mv.a|0,_mj,_mr,_mv);}},_mw=E(_mj);if(!_mw._){return _mp(_mw.a);}else{return _mp(_mw.a);}});return B(_c8(_je,_mo,new T(function(){var _mx=E(_j6);if(!_mx._){var _my=_mx.a,_mz=E(_j7);if(!_mz._){return new T3(0,_my+_mz.a|0,_mx,_mz);}else{return new T3(0,_my+_mz.a|0,_mx,_mz);}}else{var _mA=_mx.a,_mB=E(_j7);if(!_mB._){return new T3(0,_mA+_mB.a|0,_mx,_mB);}else{return new T3(0,_mA+_mB.a|0,_mx,_mB);}}}),new T(function(){var _mC=E(_j8);if(!_mC._){var _mD=_mC.a,_mE=E(_mn);if(!_mE._){return new T3(0,_mD+_mE.a|0,_mC,_mE);}else{return new T3(0,_mD+_mE.a|0,_mC,_mE);}}else{var _mF=_mC.a,_mG=E(_mn);if(!_mG._){return new T3(0,_mF+_mG.a|0,_mC,_mG);}else{return new T3(0,_mF+_mG.a|0,_mC,_mG);}}}),_jh));break;case 1:var _mH=_mm.b,_mI=new T(function(){var _mJ=function(_mK){var _mL=E(_j7);if(!_mL._){var _mM=_mL.a,_mN=E(_j8);return (_mN._==0)?new T4(1,(_mK+_mM|0)+_mN.a|0,_j6,_mL,_mN):new T4(1,(_mK+_mM|0)+_mN.a|0,_j6,_mL,_mN);}else{var _mO=_mL.a,_mP=E(_j8);return (_mP._==0)?new T4(1,(_mK+_mO|0)+_mP.a|0,_j6,_mL,_mP):new T4(1,(_mK+_mO|0)+_mP.a|0,_j6,_mL,_mP);}},_mQ=E(_j6);if(!_mQ._){return _mJ(_mQ.a);}else{return _mJ(_mQ.a);}}),_mR=new T(function(){var _mS=function(_mT){var _mU=E(_mk);if(!_mU._){var _mV=_mU.a,_mW=E(_ml);return (_mW._==0)?new T4(1,(_mT+_mV|0)+_mW.a|0,_mj,_mU,_mW):new T4(1,(_mT+_mV|0)+_mW.a|0,_mj,_mU,_mW);}else{var _mX=_mU.a,_mY=E(_ml);return (_mY._==0)?new T4(1,(_mT+_mX|0)+_mY.a|0,_mj,_mU,_mY):new T4(1,(_mT+_mX|0)+_mY.a|0,_mj,_mU,_mY);}},_mZ=E(_mj);if(!_mZ._){return _mS(_mZ.a);}else{return _mS(_mZ.a);}});return B(_c8(_je,_mR,_mI,new T(function(){var _n0=E(_mm.a);if(!_n0._){var _n1=_n0.a,_n2=E(_mH);if(!_n2._){return new T3(0,_n1+_n2.a|0,_n0,_n2);}else{return new T3(0,_n1+_n2.a|0,_n0,_n2);}}else{var _n3=_n0.a,_n4=E(_mH);if(!_n4._){return new T3(0,_n3+_n4.a|0,_n0,_n4);}else{return new T3(0,_n3+_n4.a|0,_n0,_n4);}}}),_jh));break;case 2:var _n5=_mm.a,_n6=_mm.c,_n7=new T(function(){var _n8=function(_n9){var _na=E(_mm.b);if(!_na._){var _nb=_na.a,_nc=E(_n6);return (_nc._==0)?new T4(1,(_n9+_nb|0)+_nc.a|0,_n5,_na,_nc):new T4(1,(_n9+_nb|0)+_nc.a|0,_n5,_na,_nc);}else{var _nd=_na.a,_ne=E(_n6);return (_ne._==0)?new T4(1,(_n9+_nd|0)+_ne.a|0,_n5,_na,_ne):new T4(1,(_n9+_nd|0)+_ne.a|0,_n5,_na,_ne);}},_nf=E(_n5);if(!_nf._){return _n8(_nf.a);}else{return _n8(_nf.a);}}),_ng=new T(function(){var _nh=function(_ni){var _nj=E(_j7);if(!_nj._){var _nk=_nj.a,_nl=E(_j8);return (_nl._==0)?new T4(1,(_ni+_nk|0)+_nl.a|0,_j6,_nj,_nl):new T4(1,(_ni+_nk|0)+_nl.a|0,_j6,_nj,_nl);}else{var _nm=_nj.a,_nn=E(_j8);return (_nn._==0)?new T4(1,(_ni+_nm|0)+_nn.a|0,_j6,_nj,_nn):new T4(1,(_ni+_nm|0)+_nn.a|0,_j6,_nj,_nn);}},_no=E(_j6);if(!_no._){return _nh(_no.a);}else{return _nh(_no.a);}}),_np=new T(function(){var _nq=function(_nr){var _ns=E(_mk);if(!_ns._){var _nt=_ns.a,_nu=E(_ml);return (_nu._==0)?new T4(1,(_nr+_nt|0)+_nu.a|0,_mj,_ns,_nu):new T4(1,(_nr+_nt|0)+_nu.a|0,_mj,_ns,_nu);}else{var _nv=_ns.a,_nw=E(_ml);return (_nw._==0)?new T4(1,(_nr+_nv|0)+_nw.a|0,_mj,_ns,_nw):new T4(1,(_nr+_nv|0)+_nw.a|0,_mj,_ns,_nw);}},_nx=E(_mj);if(!_nx._){return _nq(_nx.a);}else{return _nq(_nx.a);}});return B(_c8(_je,_np,_ng,_n7,_jh));break;default:var _ny=_mm.b,_nz=_mm.d,_nA=new T(function(){var _nB=function(_nC){var _nD=E(_j7);if(!_nD._){var _nE=_nD.a,_nF=E(_j8);return (_nF._==0)?new T4(1,(_nC+_nE|0)+_nF.a|0,_j6,_nD,_nF):new T4(1,(_nC+_nE|0)+_nF.a|0,_j6,_nD,_nF);}else{var _nG=_nD.a,_nH=E(_j8);return (_nH._==0)?new T4(1,(_nC+_nG|0)+_nH.a|0,_j6,_nD,_nH):new T4(1,(_nC+_nG|0)+_nH.a|0,_j6,_nD,_nH);}},_nI=E(_j6);if(!_nI._){return _nB(_nI.a);}else{return _nB(_nI.a);}}),_nJ=new T(function(){var _nK=function(_nL){var _nM=E(_mk);if(!_nM._){var _nN=_nM.a,_nO=E(_ml);return (_nO._==0)?new T4(1,(_nL+_nN|0)+_nO.a|0,_mj,_nM,_nO):new T4(1,(_nL+_nN|0)+_nO.a|0,_mj,_nM,_nO);}else{var _nP=_nM.a,_nQ=E(_ml);return (_nQ._==0)?new T4(1,(_nL+_nP|0)+_nQ.a|0,_mj,_nM,_nQ):new T4(1,(_nL+_nP|0)+_nQ.a|0,_mj,_nM,_nQ);}},_nR=E(_mj);if(!_nR._){return _nK(_nR.a);}else{return _nK(_nR.a);}});return B(_bd(_je,_nJ,_nA,new T(function(){var _nS=E(_mm.a);if(!_nS._){var _nT=_nS.a,_nU=E(_ny);if(!_nU._){return new T3(0,_nT+_nU.a|0,_nS,_nU);}else{return new T3(0,_nT+_nU.a|0,_nS,_nU);}}else{var _nV=_nS.a,_nW=E(_ny);if(!_nW._){return new T3(0,_nV+_nW.a|0,_nS,_nW);}else{return new T3(0,_nV+_nW.a|0,_nS,_nW);}}}),new T(function(){var _nX=E(_mm.c);if(!_nX._){var _nY=_nX.a,_nZ=E(_nz);if(!_nZ._){return new T3(0,_nY+_nZ.a|0,_nX,_nZ);}else{return new T3(0,_nY+_nZ.a|0,_nX,_nZ);}}else{var _o0=_nX.a,_o1=E(_nz);if(!_o1._){return new T3(0,_o0+_o1.a|0,_nX,_o1);}else{return new T3(0,_o0+_o1.a|0,_nX,_o1);}}}),_jh));}break;default:var _o2=_jp.a,_o3=_jp.b,_o4=_jp.c,_o5=_jp.d,_o6=E(_jg);switch(_o6._){case 0:var _o7=_o6.a,_o8=new T(function(){var _o9=function(_oa){var _ob=E(_j6);if(!_ob._){var _oc=_ob.a,_od=E(_j7);return (_od._==0)?new T4(1,(_oa+_oc|0)+_od.a|0,_o5,_ob,_od):new T4(1,(_oa+_oc|0)+_od.a|0,_o5,_ob,_od);}else{var _oe=_ob.a,_of=E(_j7);return (_of._==0)?new T4(1,(_oa+_oe|0)+_of.a|0,_o5,_ob,_of):new T4(1,(_oa+_oe|0)+_of.a|0,_o5,_ob,_of);}},_og=E(_o5);if(!_og._){return _o9(_og.a);}else{return _o9(_og.a);}}),_oh=new T(function(){var _oi=function(_oj){var _ok=E(_o3);if(!_ok._){var _ol=_ok.a,_om=E(_o4);return (_om._==0)?new T4(1,(_oj+_ol|0)+_om.a|0,_o2,_ok,_om):new T4(1,(_oj+_ol|0)+_om.a|0,_o2,_ok,_om);}else{var _on=_ok.a,_oo=E(_o4);return (_oo._==0)?new T4(1,(_oj+_on|0)+_oo.a|0,_o2,_ok,_oo):new T4(1,(_oj+_on|0)+_oo.a|0,_o2,_ok,_oo);}},_op=E(_o2);if(!_op._){return _oi(_op.a);}else{return _oi(_op.a);}});return B(_c8(_je,_oh,_o8,new T(function(){var _oq=E(_j8);if(!_oq._){var _or=_oq.a,_os=E(_o7);if(!_os._){return new T3(0,_or+_os.a|0,_oq,_os);}else{return new T3(0,_or+_os.a|0,_oq,_os);}}else{var _ot=_oq.a,_ou=E(_o7);if(!_ou._){return new T3(0,_ot+_ou.a|0,_oq,_ou);}else{return new T3(0,_ot+_ou.a|0,_oq,_ou);}}}),_jh));break;case 1:var _ov=_o6.b,_ow=new T(function(){var _ox=function(_oy){var _oz=E(_o6.a);if(!_oz._){var _oA=_oz.a,_oB=E(_ov);return (_oB._==0)?new T4(1,(_oy+_oA|0)+_oB.a|0,_j8,_oz,_oB):new T4(1,(_oy+_oA|0)+_oB.a|0,_j8,_oz,_oB);}else{var _oC=_oz.a,_oD=E(_ov);return (_oD._==0)?new T4(1,(_oy+_oC|0)+_oD.a|0,_j8,_oz,_oD):new T4(1,(_oy+_oC|0)+_oD.a|0,_j8,_oz,_oD);}},_oE=E(_j8);if(!_oE._){return _ox(_oE.a);}else{return _ox(_oE.a);}}),_oF=new T(function(){var _oG=function(_oH){var _oI=E(_j6);if(!_oI._){var _oJ=_oI.a,_oK=E(_j7);return (_oK._==0)?new T4(1,(_oH+_oJ|0)+_oK.a|0,_o5,_oI,_oK):new T4(1,(_oH+_oJ|0)+_oK.a|0,_o5,_oI,_oK);}else{var _oL=_oI.a,_oM=E(_j7);return (_oM._==0)?new T4(1,(_oH+_oL|0)+_oM.a|0,_o5,_oI,_oM):new T4(1,(_oH+_oL|0)+_oM.a|0,_o5,_oI,_oM);}},_oN=E(_o5);if(!_oN._){return _oG(_oN.a);}else{return _oG(_oN.a);}}),_oO=new T(function(){var _oP=function(_oQ){var _oR=E(_o3);if(!_oR._){var _oS=_oR.a,_oT=E(_o4);return (_oT._==0)?new T4(1,(_oQ+_oS|0)+_oT.a|0,_o2,_oR,_oT):new T4(1,(_oQ+_oS|0)+_oT.a|0,_o2,_oR,_oT);}else{var _oU=_oR.a,_oV=E(_o4);return (_oV._==0)?new T4(1,(_oQ+_oU|0)+_oV.a|0,_o2,_oR,_oV):new T4(1,(_oQ+_oU|0)+_oV.a|0,_o2,_oR,_oV);}},_oW=E(_o2);if(!_oW._){return _oP(_oW.a);}else{return _oP(_oW.a);}});return B(_c8(_je,_oO,_oF,_ow,_jh));break;case 2:var _oX=_o6.a,_oY=_o6.c,_oZ=new T(function(){var _p0=function(_p1){var _p2=E(_j6);if(!_p2._){var _p3=_p2.a,_p4=E(_j7);return (_p4._==0)?new T4(1,(_p1+_p3|0)+_p4.a|0,_o5,_p2,_p4):new T4(1,(_p1+_p3|0)+_p4.a|0,_o5,_p2,_p4);}else{var _p5=_p2.a,_p6=E(_j7);return (_p6._==0)?new T4(1,(_p1+_p5|0)+_p6.a|0,_o5,_p2,_p6):new T4(1,(_p1+_p5|0)+_p6.a|0,_o5,_p2,_p6);}},_p7=E(_o5);if(!_p7._){return _p0(_p7.a);}else{return _p0(_p7.a);}}),_p8=new T(function(){var _p9=function(_pa){var _pb=E(_o3);if(!_pb._){var _pc=_pb.a,_pd=E(_o4);return (_pd._==0)?new T4(1,(_pa+_pc|0)+_pd.a|0,_o2,_pb,_pd):new T4(1,(_pa+_pc|0)+_pd.a|0,_o2,_pb,_pd);}else{var _pe=_pb.a,_pf=E(_o4);return (_pf._==0)?new T4(1,(_pa+_pe|0)+_pf.a|0,_o2,_pb,_pf):new T4(1,(_pa+_pe|0)+_pf.a|0,_o2,_pb,_pf);}},_pg=E(_o2);if(!_pg._){return _p9(_pg.a);}else{return _p9(_pg.a);}});return B(_bd(_je,_p8,_oZ,new T(function(){var _ph=E(_j8);if(!_ph._){var _pi=_ph.a,_pj=E(_oX);if(!_pj._){return new T3(0,_pi+_pj.a|0,_ph,_pj);}else{return new T3(0,_pi+_pj.a|0,_ph,_pj);}}else{var _pk=_ph.a,_pl=E(_oX);if(!_pl._){return new T3(0,_pk+_pl.a|0,_ph,_pl);}else{return new T3(0,_pk+_pl.a|0,_ph,_pl);}}}),new T(function(){var _pm=E(_o6.b);if(!_pm._){var _pn=_pm.a,_po=E(_oY);if(!_po._){return new T3(0,_pn+_po.a|0,_pm,_po);}else{return new T3(0,_pn+_po.a|0,_pm,_po);}}else{var _pp=_pm.a,_pq=E(_oY);if(!_pq._){return new T3(0,_pp+_pq.a|0,_pm,_pq);}else{return new T3(0,_pp+_pq.a|0,_pm,_pq);}}}),_jh));break;default:var _pr=_o6.b,_ps=_o6.d,_pt=new T(function(){var _pu=function(_pv){var _pw=E(_o6.a);if(!_pw._){var _px=_pw.a,_py=E(_pr);return (_py._==0)?new T4(1,(_pv+_px|0)+_py.a|0,_j8,_pw,_py):new T4(1,(_pv+_px|0)+_py.a|0,_j8,_pw,_py);}else{var _pz=_pw.a,_pA=E(_pr);return (_pA._==0)?new T4(1,(_pv+_pz|0)+_pA.a|0,_j8,_pw,_pA):new T4(1,(_pv+_pz|0)+_pA.a|0,_j8,_pw,_pA);}},_pB=E(_j8);if(!_pB._){return _pu(_pB.a);}else{return _pu(_pB.a);}}),_pC=new T(function(){var _pD=function(_pE){var _pF=E(_j6);if(!_pF._){var _pG=_pF.a,_pH=E(_j7);return (_pH._==0)?new T4(1,(_pE+_pG|0)+_pH.a|0,_o5,_pF,_pH):new T4(1,(_pE+_pG|0)+_pH.a|0,_o5,_pF,_pH);}else{var _pI=_pF.a,_pJ=E(_j7);return (_pJ._==0)?new T4(1,(_pE+_pI|0)+_pJ.a|0,_o5,_pF,_pJ):new T4(1,(_pE+_pI|0)+_pJ.a|0,_o5,_pF,_pJ);}},_pK=E(_o5);if(!_pK._){return _pD(_pK.a);}else{return _pD(_pK.a);}}),_pL=new T(function(){var _pM=function(_pN){var _pO=E(_o3);if(!_pO._){var _pP=_pO.a,_pQ=E(_o4);return (_pQ._==0)?new T4(1,(_pN+_pP|0)+_pQ.a|0,_o2,_pO,_pQ):new T4(1,(_pN+_pP|0)+_pQ.a|0,_o2,_pO,_pQ);}else{var _pR=_pO.a,_pS=E(_o4);return (_pS._==0)?new T4(1,(_pN+_pR|0)+_pS.a|0,_o2,_pO,_pS):new T4(1,(_pN+_pR|0)+_pS.a|0,_o2,_pO,_pS);}},_pT=E(_o2);if(!_pT._){return _pM(_pT.a);}else{return _pM(_pT.a);}});return B(_bd(_je,_pL,_pC,_pt,new T(function(){var _pU=E(_o6.c);if(!_pU._){var _pV=_pU.a,_pW=E(_ps);if(!_pW._){return new T3(0,_pV+_pW.a|0,_pU,_pW);}else{return new T3(0,_pV+_pW.a|0,_pU,_pW);}}else{var _pX=_pU.a,_pY=E(_ps);if(!_pY._){return new T3(0,_pX+_pY.a|0,_pU,_pY);}else{return new T3(0,_pX+_pY.a|0,_pU,_pY);}}}),_jh));}}});return new T4(2,(((_jc+_jj|0)+_jl|0)+_jn|0)+_jb.a|0,E(_jd),_jo,E(_jb.d));},_pZ=E(_j8);if(!_pZ._){return _jm(_pZ.a);}else{return _jm(_pZ.a);}},_q0=E(_j7);if(!_q0._){return _jk(_q0.a);}else{return _jk(_q0.a);}},_q1=E(_j6);if(!_q1._){return _ji(_q1.a);}else{return _ji(_q1.a);}}}}}},_bX=function(_q2,_q3,_q4,_q5){var _q6=E(_q2);if(!_q6._){return _8L(_q3,_8L(_q4,_q5));}else{var _q7=E(_q5);if(!_q7._){return _9Z(_9Z(_q6,_q3),_q4);}else{if(_q6._==1){return _8L(_q6.a,_8L(_q3,_8L(_q4,_q7)));}else{var _q8=_q6.a,_q9=_q6.b,_qa=_q6.c,_qb=_q6.d;if(_q7._==1){return _9Z(_9Z(_aE(_q8,_q9,_qa,_qb,_q3),_q4),_q7.a);}else{var _qc=_q7.b,_qd=_q7.c,_qe=function(_qf){var _qg=function(_qh){var _qi=new T(function(){var _qj=E(_qb);switch(_qj._){case 0:var _qk=_qj.a,_ql=E(_qc);switch(_ql._){case 0:var _qm=_ql.a;return _bX(_qa,new T(function(){var _qn=E(_qk);if(!_qn._){var _qo=_qn.a,_qp=E(_q3);if(!_qp._){return new T3(0,_qo+_qp.a|0,_qn,_qp);}else{return new T3(0,_qo+_qp.a|0,_qn,_qp);}}else{var _qq=_qn.a,_qr=E(_q3);if(!_qr._){return new T3(0,_qq+_qr.a|0,_qn,_qr);}else{return new T3(0,_qq+_qr.a|0,_qn,_qr);}}}),new T(function(){var _qs=E(_q4);if(!_qs._){var _qt=_qs.a,_qu=E(_qm);if(!_qu._){return new T3(0,_qt+_qu.a|0,_qs,_qu);}else{return new T3(0,_qt+_qu.a|0,_qs,_qu);}}else{var _qv=_qs.a,_qw=E(_qm);if(!_qw._){return new T3(0,_qv+_qw.a|0,_qs,_qw);}else{return new T3(0,_qv+_qw.a|0,_qs,_qw);}}}),_qd);break;case 1:var _qx=_ql.b,_qy=new T(function(){var _qz=function(_qA){var _qB=E(_q3);if(!_qB._){var _qC=_qB.a,_qD=E(_q4);return (_qD._==0)?new T4(1,(_qA+_qC|0)+_qD.a|0,_qk,_qB,_qD):new T4(1,(_qA+_qC|0)+_qD.a|0,_qk,_qB,_qD);}else{var _qE=_qB.a,_qF=E(_q4);return (_qF._==0)?new T4(1,(_qA+_qE|0)+_qF.a|0,_qk,_qB,_qF):new T4(1,(_qA+_qE|0)+_qF.a|0,_qk,_qB,_qF);}},_qG=E(_qk);if(!_qG._){return _qz(_qG.a);}else{return _qz(_qG.a);}});return _bX(_qa,_qy,new T(function(){var _qH=E(_ql.a);if(!_qH._){var _qI=_qH.a,_qJ=E(_qx);if(!_qJ._){return new T3(0,_qI+_qJ.a|0,_qH,_qJ);}else{return new T3(0,_qI+_qJ.a|0,_qH,_qJ);}}else{var _qK=_qH.a,_qL=E(_qx);if(!_qL._){return new T3(0,_qK+_qL.a|0,_qH,_qL);}else{return new T3(0,_qK+_qL.a|0,_qH,_qL);}}}),_qd);break;case 2:var _qM=_ql.a,_qN=_ql.c,_qO=new T(function(){var _qP=function(_qQ){var _qR=E(_ql.b);if(!_qR._){var _qS=_qR.a,_qT=E(_qN);return (_qT._==0)?new T4(1,(_qQ+_qS|0)+_qT.a|0,_qM,_qR,_qT):new T4(1,(_qQ+_qS|0)+_qT.a|0,_qM,_qR,_qT);}else{var _qU=_qR.a,_qV=E(_qN);return (_qV._==0)?new T4(1,(_qQ+_qU|0)+_qV.a|0,_qM,_qR,_qV):new T4(1,(_qQ+_qU|0)+_qV.a|0,_qM,_qR,_qV);}},_qW=E(_qM);if(!_qW._){return _qP(_qW.a);}else{return _qP(_qW.a);}}),_qX=new T(function(){var _qY=function(_qZ){var _r0=E(_q3);if(!_r0._){var _r1=_r0.a,_r2=E(_q4);return (_r2._==0)?new T4(1,(_qZ+_r1|0)+_r2.a|0,_qk,_r0,_r2):new T4(1,(_qZ+_r1|0)+_r2.a|0,_qk,_r0,_r2);}else{var _r3=_r0.a,_r4=E(_q4);return (_r4._==0)?new T4(1,(_qZ+_r3|0)+_r4.a|0,_qk,_r0,_r4):new T4(1,(_qZ+_r3|0)+_r4.a|0,_qk,_r0,_r4);}},_r5=E(_qk);if(!_r5._){return _qY(_r5.a);}else{return _qY(_r5.a);}});return _bX(_qa,_qX,_qO,_qd);break;default:var _r6=_ql.b,_r7=_ql.d,_r8=new T(function(){var _r9=function(_ra){var _rb=E(_q3);if(!_rb._){var _rc=_rb.a,_rd=E(_q4);return (_rd._==0)?new T4(1,(_ra+_rc|0)+_rd.a|0,_qk,_rb,_rd):new T4(1,(_ra+_rc|0)+_rd.a|0,_qk,_rb,_rd);}else{var _re=_rb.a,_rf=E(_q4);return (_rf._==0)?new T4(1,(_ra+_re|0)+_rf.a|0,_qk,_rb,_rf):new T4(1,(_ra+_re|0)+_rf.a|0,_qk,_rb,_rf);}},_rg=E(_qk);if(!_rg._){return _r9(_rg.a);}else{return _r9(_rg.a);}});return B(_c8(_qa,_r8,new T(function(){var _rh=E(_ql.a);if(!_rh._){var _ri=_rh.a,_rj=E(_r6);if(!_rj._){return new T3(0,_ri+_rj.a|0,_rh,_rj);}else{return new T3(0,_ri+_rj.a|0,_rh,_rj);}}else{var _rk=_rh.a,_rl=E(_r6);if(!_rl._){return new T3(0,_rk+_rl.a|0,_rh,_rl);}else{return new T3(0,_rk+_rl.a|0,_rh,_rl);}}}),new T(function(){var _rm=E(_ql.c);if(!_rm._){var _rn=_rm.a,_ro=E(_r7);if(!_ro._){return new T3(0,_rn+_ro.a|0,_rm,_ro);}else{return new T3(0,_rn+_ro.a|0,_rm,_ro);}}else{var _rp=_rm.a,_rq=E(_r7);if(!_rq._){return new T3(0,_rp+_rq.a|0,_rm,_rq);}else{return new T3(0,_rp+_rq.a|0,_rm,_rq);}}}),_qd));}break;case 1:var _rr=_qj.a,_rs=_qj.b,_rt=E(_qc);switch(_rt._){case 0:var _ru=_rt.a,_rv=new T(function(){var _rw=function(_rx){var _ry=E(_rs);if(!_ry._){var _rz=_ry.a,_rA=E(_q3);return (_rA._==0)?new T4(1,(_rx+_rz|0)+_rA.a|0,_rr,_ry,_rA):new T4(1,(_rx+_rz|0)+_rA.a|0,_rr,_ry,_rA);}else{var _rB=_ry.a,_rC=E(_q3);return (_rC._==0)?new T4(1,(_rx+_rB|0)+_rC.a|0,_rr,_ry,_rC):new T4(1,(_rx+_rB|0)+_rC.a|0,_rr,_ry,_rC);}},_rD=E(_rr);if(!_rD._){return _rw(_rD.a);}else{return _rw(_rD.a);}});return _bX(_qa,_rv,new T(function(){var _rE=E(_q4);if(!_rE._){var _rF=_rE.a,_rG=E(_ru);if(!_rG._){return new T3(0,_rF+_rG.a|0,_rE,_rG);}else{return new T3(0,_rF+_rG.a|0,_rE,_rG);}}else{var _rH=_rE.a,_rI=E(_ru);if(!_rI._){return new T3(0,_rH+_rI.a|0,_rE,_rI);}else{return new T3(0,_rH+_rI.a|0,_rE,_rI);}}}),_qd);break;case 1:var _rJ=_rt.b,_rK=new T(function(){var _rL=function(_rM){var _rN=E(_rt.a);if(!_rN._){var _rO=_rN.a,_rP=E(_rJ);return (_rP._==0)?new T4(1,(_rM+_rO|0)+_rP.a|0,_q4,_rN,_rP):new T4(1,(_rM+_rO|0)+_rP.a|0,_q4,_rN,_rP);}else{var _rQ=_rN.a,_rR=E(_rJ);return (_rR._==0)?new T4(1,(_rM+_rQ|0)+_rR.a|0,_q4,_rN,_rR):new T4(1,(_rM+_rQ|0)+_rR.a|0,_q4,_rN,_rR);}},_rS=E(_q4);if(!_rS._){return _rL(_rS.a);}else{return _rL(_rS.a);}}),_rT=new T(function(){var _rU=function(_rV){var _rW=E(_rs);if(!_rW._){var _rX=_rW.a,_rY=E(_q3);return (_rY._==0)?new T4(1,(_rV+_rX|0)+_rY.a|0,_rr,_rW,_rY):new T4(1,(_rV+_rX|0)+_rY.a|0,_rr,_rW,_rY);}else{var _rZ=_rW.a,_s0=E(_q3);return (_s0._==0)?new T4(1,(_rV+_rZ|0)+_s0.a|0,_rr,_rW,_s0):new T4(1,(_rV+_rZ|0)+_s0.a|0,_rr,_rW,_s0);}},_s1=E(_rr);if(!_s1._){return _rU(_s1.a);}else{return _rU(_s1.a);}});return _bX(_qa,_rT,_rK,_qd);break;case 2:var _s2=_rt.a,_s3=_rt.c,_s4=new T(function(){var _s5=function(_s6){var _s7=E(_rs);if(!_s7._){var _s8=_s7.a,_s9=E(_q3);return (_s9._==0)?new T4(1,(_s6+_s8|0)+_s9.a|0,_rr,_s7,_s9):new T4(1,(_s6+_s8|0)+_s9.a|0,_rr,_s7,_s9);}else{var _sa=_s7.a,_sb=E(_q3);return (_sb._==0)?new T4(1,(_s6+_sa|0)+_sb.a|0,_rr,_s7,_sb):new T4(1,(_s6+_sa|0)+_sb.a|0,_rr,_s7,_sb);}},_sc=E(_rr);if(!_sc._){return _s5(_sc.a);}else{return _s5(_sc.a);}});return B(_c8(_qa,_s4,new T(function(){var _sd=E(_q4);if(!_sd._){var _se=_sd.a,_sf=E(_s2);if(!_sf._){return new T3(0,_se+_sf.a|0,_sd,_sf);}else{return new T3(0,_se+_sf.a|0,_sd,_sf);}}else{var _sg=_sd.a,_sh=E(_s2);if(!_sh._){return new T3(0,_sg+_sh.a|0,_sd,_sh);}else{return new T3(0,_sg+_sh.a|0,_sd,_sh);}}}),new T(function(){var _si=E(_rt.b);if(!_si._){var _sj=_si.a,_sk=E(_s3);if(!_sk._){return new T3(0,_sj+_sk.a|0,_si,_sk);}else{return new T3(0,_sj+_sk.a|0,_si,_sk);}}else{var _sl=_si.a,_sm=E(_s3);if(!_sm._){return new T3(0,_sl+_sm.a|0,_si,_sm);}else{return new T3(0,_sl+_sm.a|0,_si,_sm);}}}),_qd));break;default:var _sn=_rt.b,_so=_rt.d,_sp=new T(function(){var _sq=function(_sr){var _ss=E(_rt.a);if(!_ss._){var _st=_ss.a,_su=E(_sn);return (_su._==0)?new T4(1,(_sr+_st|0)+_su.a|0,_q4,_ss,_su):new T4(1,(_sr+_st|0)+_su.a|0,_q4,_ss,_su);}else{var _sv=_ss.a,_sw=E(_sn);return (_sw._==0)?new T4(1,(_sr+_sv|0)+_sw.a|0,_q4,_ss,_sw):new T4(1,(_sr+_sv|0)+_sw.a|0,_q4,_ss,_sw);}},_sx=E(_q4);if(!_sx._){return _sq(_sx.a);}else{return _sq(_sx.a);}}),_sy=new T(function(){var _sz=function(_sA){var _sB=E(_rs);if(!_sB._){var _sC=_sB.a,_sD=E(_q3);return (_sD._==0)?new T4(1,(_sA+_sC|0)+_sD.a|0,_rr,_sB,_sD):new T4(1,(_sA+_sC|0)+_sD.a|0,_rr,_sB,_sD);}else{var _sE=_sB.a,_sF=E(_q3);return (_sF._==0)?new T4(1,(_sA+_sE|0)+_sF.a|0,_rr,_sB,_sF):new T4(1,(_sA+_sE|0)+_sF.a|0,_rr,_sB,_sF);}},_sG=E(_rr);if(!_sG._){return _sz(_sG.a);}else{return _sz(_sG.a);}});return B(_c8(_qa,_sy,_sp,new T(function(){var _sH=E(_rt.c);if(!_sH._){var _sI=_sH.a,_sJ=E(_so);if(!_sJ._){return new T3(0,_sI+_sJ.a|0,_sH,_sJ);}else{return new T3(0,_sI+_sJ.a|0,_sH,_sJ);}}else{var _sK=_sH.a,_sL=E(_so);if(!_sL._){return new T3(0,_sK+_sL.a|0,_sH,_sL);}else{return new T3(0,_sK+_sL.a|0,_sH,_sL);}}}),_qd));}break;case 2:var _sM=_qj.a,_sN=_qj.b,_sO=_qj.c,_sP=E(_qc);switch(_sP._){case 0:var _sQ=_sP.a,_sR=new T(function(){var _sS=function(_sT){var _sU=E(_q4);if(!_sU._){var _sV=_sU.a,_sW=E(_sQ);return (_sW._==0)?new T4(1,(_sT+_sV|0)+_sW.a|0,_q3,_sU,_sW):new T4(1,(_sT+_sV|0)+_sW.a|0,_q3,_sU,_sW);}else{var _sX=_sU.a,_sY=E(_sQ);return (_sY._==0)?new T4(1,(_sT+_sX|0)+_sY.a|0,_q3,_sU,_sY):new T4(1,(_sT+_sX|0)+_sY.a|0,_q3,_sU,_sY);}},_sZ=E(_q3);if(!_sZ._){return _sS(_sZ.a);}else{return _sS(_sZ.a);}}),_t0=new T(function(){var _t1=function(_t2){var _t3=E(_sN);if(!_t3._){var _t4=_t3.a,_t5=E(_sO);return (_t5._==0)?new T4(1,(_t2+_t4|0)+_t5.a|0,_sM,_t3,_t5):new T4(1,(_t2+_t4|0)+_t5.a|0,_sM,_t3,_t5);}else{var _t6=_t3.a,_t7=E(_sO);return (_t7._==0)?new T4(1,(_t2+_t6|0)+_t7.a|0,_sM,_t3,_t7):new T4(1,(_t2+_t6|0)+_t7.a|0,_sM,_t3,_t7);}},_t8=E(_sM);if(!_t8._){return _t1(_t8.a);}else{return _t1(_t8.a);}});return _bX(_qa,_t0,_sR,_qd);break;case 1:var _t9=_sP.b,_ta=new T(function(){var _tb=function(_tc){var _td=E(_sN);if(!_td._){var _te=_td.a,_tf=E(_sO);return (_tf._==0)?new T4(1,(_tc+_te|0)+_tf.a|0,_sM,_td,_tf):new T4(1,(_tc+_te|0)+_tf.a|0,_sM,_td,_tf);}else{var _tg=_td.a,_th=E(_sO);return (_th._==0)?new T4(1,(_tc+_tg|0)+_th.a|0,_sM,_td,_th):new T4(1,(_tc+_tg|0)+_th.a|0,_sM,_td,_th);}},_ti=E(_sM);if(!_ti._){return _tb(_ti.a);}else{return _tb(_ti.a);}});return B(_c8(_qa,_ta,new T(function(){var _tj=E(_q3);if(!_tj._){var _tk=_tj.a,_tl=E(_q4);if(!_tl._){return new T3(0,_tk+_tl.a|0,_tj,_tl);}else{return new T3(0,_tk+_tl.a|0,_tj,_tl);}}else{var _tm=_tj.a,_tn=E(_q4);if(!_tn._){return new T3(0,_tm+_tn.a|0,_tj,_tn);}else{return new T3(0,_tm+_tn.a|0,_tj,_tn);}}}),new T(function(){var _to=E(_sP.a);if(!_to._){var _tp=_to.a,_tq=E(_t9);if(!_tq._){return new T3(0,_tp+_tq.a|0,_to,_tq);}else{return new T3(0,_tp+_tq.a|0,_to,_tq);}}else{var _tr=_to.a,_ts=E(_t9);if(!_ts._){return new T3(0,_tr+_ts.a|0,_to,_ts);}else{return new T3(0,_tr+_ts.a|0,_to,_ts);}}}),_qd));break;case 2:var _tt=_sP.a,_tu=_sP.c,_tv=new T(function(){var _tw=function(_tx){var _ty=E(_q4);if(!_ty._){var _tz=_ty.a,_tA=E(_tt);return (_tA._==0)?new T4(1,(_tx+_tz|0)+_tA.a|0,_q3,_ty,_tA):new T4(1,(_tx+_tz|0)+_tA.a|0,_q3,_ty,_tA);}else{var _tB=_ty.a,_tC=E(_tt);return (_tC._==0)?new T4(1,(_tx+_tB|0)+_tC.a|0,_q3,_ty,_tC):new T4(1,(_tx+_tB|0)+_tC.a|0,_q3,_ty,_tC);}},_tD=E(_q3);if(!_tD._){return _tw(_tD.a);}else{return _tw(_tD.a);}}),_tE=new T(function(){var _tF=function(_tG){var _tH=E(_sN);if(!_tH._){var _tI=_tH.a,_tJ=E(_sO);return (_tJ._==0)?new T4(1,(_tG+_tI|0)+_tJ.a|0,_sM,_tH,_tJ):new T4(1,(_tG+_tI|0)+_tJ.a|0,_sM,_tH,_tJ);}else{var _tK=_tH.a,_tL=E(_sO);return (_tL._==0)?new T4(1,(_tG+_tK|0)+_tL.a|0,_sM,_tH,_tL):new T4(1,(_tG+_tK|0)+_tL.a|0,_sM,_tH,_tL);}},_tM=E(_sM);if(!_tM._){return _tF(_tM.a);}else{return _tF(_tM.a);}});return B(_c8(_qa,_tE,_tv,new T(function(){var _tN=E(_sP.b);if(!_tN._){var _tO=_tN.a,_tP=E(_tu);if(!_tP._){return new T3(0,_tO+_tP.a|0,_tN,_tP);}else{return new T3(0,_tO+_tP.a|0,_tN,_tP);}}else{var _tQ=_tN.a,_tR=E(_tu);if(!_tR._){return new T3(0,_tQ+_tR.a|0,_tN,_tR);}else{return new T3(0,_tQ+_tR.a|0,_tN,_tR);}}}),_qd));break;default:var _tS=_sP.a,_tT=_sP.b,_tU=_sP.d,_tV=new T(function(){var _tW=function(_tX){var _tY=E(_sP.c);if(!_tY._){var _tZ=_tY.a,_u0=E(_tU);return (_u0._==0)?new T4(1,(_tX+_tZ|0)+_u0.a|0,_tT,_tY,_u0):new T4(1,(_tX+_tZ|0)+_u0.a|0,_tT,_tY,_u0);}else{var _u1=_tY.a,_u2=E(_tU);return (_u2._==0)?new T4(1,(_tX+_u1|0)+_u2.a|0,_tT,_tY,_u2):new T4(1,(_tX+_u1|0)+_u2.a|0,_tT,_tY,_u2);}},_u3=E(_tT);if(!_u3._){return _tW(_u3.a);}else{return _tW(_u3.a);}}),_u4=new T(function(){var _u5=function(_u6){var _u7=E(_q4);if(!_u7._){var _u8=_u7.a,_u9=E(_tS);return (_u9._==0)?new T4(1,(_u6+_u8|0)+_u9.a|0,_q3,_u7,_u9):new T4(1,(_u6+_u8|0)+_u9.a|0,_q3,_u7,_u9);}else{var _ua=_u7.a,_ub=E(_tS);return (_ub._==0)?new T4(1,(_u6+_ua|0)+_ub.a|0,_q3,_u7,_ub):new T4(1,(_u6+_ua|0)+_ub.a|0,_q3,_u7,_ub);}},_uc=E(_q3);if(!_uc._){return _u5(_uc.a);}else{return _u5(_uc.a);}}),_ud=new T(function(){var _ue=function(_uf){var _ug=E(_sN);if(!_ug._){var _uh=_ug.a,_ui=E(_sO);return (_ui._==0)?new T4(1,(_uf+_uh|0)+_ui.a|0,_sM,_ug,_ui):new T4(1,(_uf+_uh|0)+_ui.a|0,_sM,_ug,_ui);}else{var _uj=_ug.a,_uk=E(_sO);return (_uk._==0)?new T4(1,(_uf+_uj|0)+_uk.a|0,_sM,_ug,_uk):new T4(1,(_uf+_uj|0)+_uk.a|0,_sM,_ug,_uk);}},_ul=E(_sM);if(!_ul._){return _ue(_ul.a);}else{return _ue(_ul.a);}});return B(_c8(_qa,_ud,_u4,_tV,_qd));}break;default:var _um=_qj.a,_un=_qj.b,_uo=_qj.c,_up=_qj.d,_uq=E(_qc);switch(_uq._){case 0:var _ur=_uq.a,_us=new T(function(){var _ut=function(_uu){var _uv=E(_un);if(!_uv._){var _uw=_uv.a,_ux=E(_uo);return (_ux._==0)?new T4(1,(_uu+_uw|0)+_ux.a|0,_um,_uv,_ux):new T4(1,(_uu+_uw|0)+_ux.a|0,_um,_uv,_ux);}else{var _uy=_uv.a,_uz=E(_uo);return (_uz._==0)?new T4(1,(_uu+_uy|0)+_uz.a|0,_um,_uv,_uz):new T4(1,(_uu+_uy|0)+_uz.a|0,_um,_uv,_uz);}},_uA=E(_um);if(!_uA._){return _ut(_uA.a);}else{return _ut(_uA.a);}});return B(_c8(_qa,_us,new T(function(){var _uB=E(_up);if(!_uB._){var _uC=_uB.a,_uD=E(_q3);if(!_uD._){return new T3(0,_uC+_uD.a|0,_uB,_uD);}else{return new T3(0,_uC+_uD.a|0,_uB,_uD);}}else{var _uE=_uB.a,_uF=E(_q3);if(!_uF._){return new T3(0,_uE+_uF.a|0,_uB,_uF);}else{return new T3(0,_uE+_uF.a|0,_uB,_uF);}}}),new T(function(){var _uG=E(_q4);if(!_uG._){var _uH=_uG.a,_uI=E(_ur);if(!_uI._){return new T3(0,_uH+_uI.a|0,_uG,_uI);}else{return new T3(0,_uH+_uI.a|0,_uG,_uI);}}else{var _uJ=_uG.a,_uK=E(_ur);if(!_uK._){return new T3(0,_uJ+_uK.a|0,_uG,_uK);}else{return new T3(0,_uJ+_uK.a|0,_uG,_uK);}}}),_qd));break;case 1:var _uL=_uq.b,_uM=new T(function(){var _uN=function(_uO){var _uP=E(_q3);if(!_uP._){var _uQ=_uP.a,_uR=E(_q4);return (_uR._==0)?new T4(1,(_uO+_uQ|0)+_uR.a|0,_up,_uP,_uR):new T4(1,(_uO+_uQ|0)+_uR.a|0,_up,_uP,_uR);}else{var _uS=_uP.a,_uT=E(_q4);return (_uT._==0)?new T4(1,(_uO+_uS|0)+_uT.a|0,_up,_uP,_uT):new T4(1,(_uO+_uS|0)+_uT.a|0,_up,_uP,_uT);}},_uU=E(_up);if(!_uU._){return _uN(_uU.a);}else{return _uN(_uU.a);}}),_uV=new T(function(){var _uW=function(_uX){var _uY=E(_un);if(!_uY._){var _uZ=_uY.a,_v0=E(_uo);return (_v0._==0)?new T4(1,(_uX+_uZ|0)+_v0.a|0,_um,_uY,_v0):new T4(1,(_uX+_uZ|0)+_v0.a|0,_um,_uY,_v0);}else{var _v1=_uY.a,_v2=E(_uo);return (_v2._==0)?new T4(1,(_uX+_v1|0)+_v2.a|0,_um,_uY,_v2):new T4(1,(_uX+_v1|0)+_v2.a|0,_um,_uY,_v2);}},_v3=E(_um);if(!_v3._){return _uW(_v3.a);}else{return _uW(_v3.a);}});return B(_c8(_qa,_uV,_uM,new T(function(){var _v4=E(_uq.a);if(!_v4._){var _v5=_v4.a,_v6=E(_uL);if(!_v6._){return new T3(0,_v5+_v6.a|0,_v4,_v6);}else{return new T3(0,_v5+_v6.a|0,_v4,_v6);}}else{var _v7=_v4.a,_v8=E(_uL);if(!_v8._){return new T3(0,_v7+_v8.a|0,_v4,_v8);}else{return new T3(0,_v7+_v8.a|0,_v4,_v8);}}}),_qd));break;case 2:var _v9=_uq.a,_va=_uq.c,_vb=new T(function(){var _vc=function(_vd){var _ve=E(_uq.b);if(!_ve._){var _vf=_ve.a,_vg=E(_va);return (_vg._==0)?new T4(1,(_vd+_vf|0)+_vg.a|0,_v9,_ve,_vg):new T4(1,(_vd+_vf|0)+_vg.a|0,_v9,_ve,_vg);}else{var _vh=_ve.a,_vi=E(_va);return (_vi._==0)?new T4(1,(_vd+_vh|0)+_vi.a|0,_v9,_ve,_vi):new T4(1,(_vd+_vh|0)+_vi.a|0,_v9,_ve,_vi);}},_vj=E(_v9);if(!_vj._){return _vc(_vj.a);}else{return _vc(_vj.a);}}),_vk=new T(function(){var _vl=function(_vm){var _vn=E(_q3);if(!_vn._){var _vo=_vn.a,_vp=E(_q4);return (_vp._==0)?new T4(1,(_vm+_vo|0)+_vp.a|0,_up,_vn,_vp):new T4(1,(_vm+_vo|0)+_vp.a|0,_up,_vn,_vp);}else{var _vq=_vn.a,_vr=E(_q4);return (_vr._==0)?new T4(1,(_vm+_vq|0)+_vr.a|0,_up,_vn,_vr):new T4(1,(_vm+_vq|0)+_vr.a|0,_up,_vn,_vr);}},_vs=E(_up);if(!_vs._){return _vl(_vs.a);}else{return _vl(_vs.a);}}),_vt=new T(function(){var _vu=function(_vv){var _vw=E(_un);if(!_vw._){var _vx=_vw.a,_vy=E(_uo);return (_vy._==0)?new T4(1,(_vv+_vx|0)+_vy.a|0,_um,_vw,_vy):new T4(1,(_vv+_vx|0)+_vy.a|0,_um,_vw,_vy);}else{var _vz=_vw.a,_vA=E(_uo);return (_vA._==0)?new T4(1,(_vv+_vz|0)+_vA.a|0,_um,_vw,_vA):new T4(1,(_vv+_vz|0)+_vA.a|0,_um,_vw,_vA);}},_vB=E(_um);if(!_vB._){return _vu(_vB.a);}else{return _vu(_vB.a);}});return B(_c8(_qa,_vt,_vk,_vb,_qd));break;default:var _vC=_uq.b,_vD=_uq.d,_vE=new T(function(){var _vF=function(_vG){var _vH=E(_q3);if(!_vH._){var _vI=_vH.a,_vJ=E(_q4);return (_vJ._==0)?new T4(1,(_vG+_vI|0)+_vJ.a|0,_up,_vH,_vJ):new T4(1,(_vG+_vI|0)+_vJ.a|0,_up,_vH,_vJ);}else{var _vK=_vH.a,_vL=E(_q4);return (_vL._==0)?new T4(1,(_vG+_vK|0)+_vL.a|0,_up,_vH,_vL):new T4(1,(_vG+_vK|0)+_vL.a|0,_up,_vH,_vL);}},_vM=E(_up);if(!_vM._){return _vF(_vM.a);}else{return _vF(_vM.a);}}),_vN=new T(function(){var _vO=function(_vP){var _vQ=E(_un);if(!_vQ._){var _vR=_vQ.a,_vS=E(_uo);return (_vS._==0)?new T4(1,(_vP+_vR|0)+_vS.a|0,_um,_vQ,_vS):new T4(1,(_vP+_vR|0)+_vS.a|0,_um,_vQ,_vS);}else{var _vT=_vQ.a,_vU=E(_uo);return (_vU._==0)?new T4(1,(_vP+_vT|0)+_vU.a|0,_um,_vQ,_vU):new T4(1,(_vP+_vT|0)+_vU.a|0,_um,_vQ,_vU);}},_vV=E(_um);if(!_vV._){return _vO(_vV.a);}else{return _vO(_vV.a);}});return B(_bd(_qa,_vN,_vE,new T(function(){var _vW=E(_uq.a);if(!_vW._){var _vX=_vW.a,_vY=E(_vC);if(!_vY._){return new T3(0,_vX+_vY.a|0,_vW,_vY);}else{return new T3(0,_vX+_vY.a|0,_vW,_vY);}}else{var _vZ=_vW.a,_w0=E(_vC);if(!_w0._){return new T3(0,_vZ+_w0.a|0,_vW,_w0);}else{return new T3(0,_vZ+_w0.a|0,_vW,_w0);}}}),new T(function(){var _w1=E(_uq.c);if(!_w1._){var _w2=_w1.a,_w3=E(_vD);if(!_w3._){return new T3(0,_w2+_w3.a|0,_w1,_w3);}else{return new T3(0,_w2+_w3.a|0,_w1,_w3);}}else{var _w4=_w1.a,_w5=E(_vD);if(!_w5._){return new T3(0,_w4+_w5.a|0,_w1,_w5);}else{return new T3(0,_w4+_w5.a|0,_w1,_w5);}}}),_qd));}}});return new T4(2,((_q8+_qf|0)+_qh|0)+_q7.a|0,E(_q9),_qi,E(_q7.d));},_w6=E(_q4);if(!_w6._){return _qg(_w6.a);}else{return _qg(_w6.a);}},_w7=E(_q3);if(!_w7._){return _qe(_w7.a);}else{return _qe(_w7.a);}}}}}},_w8=function(_w9,_wa,_wb){var _wc=E(_w9);if(!_wc._){return _8L(_wa,_wb);}else{var _wd=E(_wb);if(!_wd._){return _9Z(_wc,_wa);}else{if(_wc._==1){return _8L(_wc.a,_8L(_wa,_wd));}else{var _we=_wc.a,_wf=_wc.b,_wg=_wc.c,_wh=_wc.d;if(_wd._==1){return _9Z(_aE(_we,_wf,_wg,_wh,_wa),_wd.a);}else{var _wi=_wd.b,_wj=_wd.c,_wk=function(_wl){var _wm=new T(function(){var _wn=E(_wh);switch(_wn._){case 0:var _wo=_wn.a,_wp=E(_wi);switch(_wp._){case 0:var _wq=_wp.a,_wr=new T(function(){var _ws=function(_wt){var _wu=E(_wa);if(!_wu._){var _wv=_wu.a,_ww=E(_wq);return (_ww._==0)?new T4(1,(_wt+_wv|0)+_ww.a|0,_wo,_wu,_ww):new T4(1,(_wt+_wv|0)+_ww.a|0,_wo,_wu,_ww);}else{var _wx=_wu.a,_wy=E(_wq);return (_wy._==0)?new T4(1,(_wt+_wx|0)+_wy.a|0,_wo,_wu,_wy):new T4(1,(_wt+_wx|0)+_wy.a|0,_wo,_wu,_wy);}},_wz=E(_wo);if(!_wz._){return _ws(_wz.a);}else{return _ws(_wz.a);}});return _w8(_wg,_wr,_wj);break;case 1:var _wA=_wp.b;return _bX(_wg,new T(function(){var _wB=E(_wo);if(!_wB._){var _wC=_wB.a,_wD=E(_wa);if(!_wD._){return new T3(0,_wC+_wD.a|0,_wB,_wD);}else{return new T3(0,_wC+_wD.a|0,_wB,_wD);}}else{var _wE=_wB.a,_wF=E(_wa);if(!_wF._){return new T3(0,_wE+_wF.a|0,_wB,_wF);}else{return new T3(0,_wE+_wF.a|0,_wB,_wF);}}}),new T(function(){var _wG=E(_wp.a);if(!_wG._){var _wH=_wG.a,_wI=E(_wA);if(!_wI._){return new T3(0,_wH+_wI.a|0,_wG,_wI);}else{return new T3(0,_wH+_wI.a|0,_wG,_wI);}}else{var _wJ=_wG.a,_wK=E(_wA);if(!_wK._){return new T3(0,_wJ+_wK.a|0,_wG,_wK);}else{return new T3(0,_wJ+_wK.a|0,_wG,_wK);}}}),_wj);break;case 2:var _wL=_wp.a,_wM=_wp.c,_wN=new T(function(){var _wO=function(_wP){var _wQ=E(_wa);if(!_wQ._){var _wR=_wQ.a,_wS=E(_wL);return (_wS._==0)?new T4(1,(_wP+_wR|0)+_wS.a|0,_wo,_wQ,_wS):new T4(1,(_wP+_wR|0)+_wS.a|0,_wo,_wQ,_wS);}else{var _wT=_wQ.a,_wU=E(_wL);return (_wU._==0)?new T4(1,(_wP+_wT|0)+_wU.a|0,_wo,_wQ,_wU):new T4(1,(_wP+_wT|0)+_wU.a|0,_wo,_wQ,_wU);}},_wV=E(_wo);if(!_wV._){return _wO(_wV.a);}else{return _wO(_wV.a);}});return _bX(_wg,_wN,new T(function(){var _wW=E(_wp.b);if(!_wW._){var _wX=_wW.a,_wY=E(_wM);if(!_wY._){return new T3(0,_wX+_wY.a|0,_wW,_wY);}else{return new T3(0,_wX+_wY.a|0,_wW,_wY);}}else{var _wZ=_wW.a,_x0=E(_wM);if(!_x0._){return new T3(0,_wZ+_x0.a|0,_wW,_x0);}else{return new T3(0,_wZ+_x0.a|0,_wW,_x0);}}}),_wj);break;default:var _x1=_wp.a,_x2=_wp.b,_x3=_wp.d,_x4=new T(function(){var _x5=function(_x6){var _x7=E(_wp.c);if(!_x7._){var _x8=_x7.a,_x9=E(_x3);return (_x9._==0)?new T4(1,(_x6+_x8|0)+_x9.a|0,_x2,_x7,_x9):new T4(1,(_x6+_x8|0)+_x9.a|0,_x2,_x7,_x9);}else{var _xa=_x7.a,_xb=E(_x3);return (_xb._==0)?new T4(1,(_x6+_xa|0)+_xb.a|0,_x2,_x7,_xb):new T4(1,(_x6+_xa|0)+_xb.a|0,_x2,_x7,_xb);}},_xc=E(_x2);if(!_xc._){return _x5(_xc.a);}else{return _x5(_xc.a);}}),_xd=new T(function(){var _xe=function(_xf){var _xg=E(_wa);if(!_xg._){var _xh=_xg.a,_xi=E(_x1);return (_xi._==0)?new T4(1,(_xf+_xh|0)+_xi.a|0,_wo,_xg,_xi):new T4(1,(_xf+_xh|0)+_xi.a|0,_wo,_xg,_xi);}else{var _xj=_xg.a,_xk=E(_x1);return (_xk._==0)?new T4(1,(_xf+_xj|0)+_xk.a|0,_wo,_xg,_xk):new T4(1,(_xf+_xj|0)+_xk.a|0,_wo,_xg,_xk);}},_xl=E(_wo);if(!_xl._){return _xe(_xl.a);}else{return _xe(_xl.a);}});return _bX(_wg,_xd,_x4,_wj);}break;case 1:var _xm=_wn.a,_xn=_wn.b,_xo=E(_wi);switch(_xo._){case 0:var _xp=_xo.a;return _bX(_wg,new T(function(){var _xq=E(_xm);if(!_xq._){var _xr=_xq.a,_xs=E(_xn);if(!_xs._){return new T3(0,_xr+_xs.a|0,_xq,_xs);}else{return new T3(0,_xr+_xs.a|0,_xq,_xs);}}else{var _xt=_xq.a,_xu=E(_xn);if(!_xu._){return new T3(0,_xt+_xu.a|0,_xq,_xu);}else{return new T3(0,_xt+_xu.a|0,_xq,_xu);}}}),new T(function(){var _xv=E(_wa);if(!_xv._){var _xw=_xv.a,_xx=E(_xp);if(!_xx._){return new T3(0,_xw+_xx.a|0,_xv,_xx);}else{return new T3(0,_xw+_xx.a|0,_xv,_xx);}}else{var _xy=_xv.a,_xz=E(_xp);if(!_xz._){return new T3(0,_xy+_xz.a|0,_xv,_xz);}else{return new T3(0,_xy+_xz.a|0,_xv,_xz);}}}),_wj);break;case 1:var _xA=_xo.b,_xB=new T(function(){var _xC=function(_xD){var _xE=E(_xn);if(!_xE._){var _xF=_xE.a,_xG=E(_wa);return (_xG._==0)?new T4(1,(_xD+_xF|0)+_xG.a|0,_xm,_xE,_xG):new T4(1,(_xD+_xF|0)+_xG.a|0,_xm,_xE,_xG);}else{var _xH=_xE.a,_xI=E(_wa);return (_xI._==0)?new T4(1,(_xD+_xH|0)+_xI.a|0,_xm,_xE,_xI):new T4(1,(_xD+_xH|0)+_xI.a|0,_xm,_xE,_xI);}},_xJ=E(_xm);if(!_xJ._){return _xC(_xJ.a);}else{return _xC(_xJ.a);}});return _bX(_wg,_xB,new T(function(){var _xK=E(_xo.a);if(!_xK._){var _xL=_xK.a,_xM=E(_xA);if(!_xM._){return new T3(0,_xL+_xM.a|0,_xK,_xM);}else{return new T3(0,_xL+_xM.a|0,_xK,_xM);}}else{var _xN=_xK.a,_xO=E(_xA);if(!_xO._){return new T3(0,_xN+_xO.a|0,_xK,_xO);}else{return new T3(0,_xN+_xO.a|0,_xK,_xO);}}}),_wj);break;case 2:var _xP=_xo.a,_xQ=_xo.c,_xR=new T(function(){var _xS=function(_xT){var _xU=E(_xo.b);if(!_xU._){var _xV=_xU.a,_xW=E(_xQ);return (_xW._==0)?new T4(1,(_xT+_xV|0)+_xW.a|0,_xP,_xU,_xW):new T4(1,(_xT+_xV|0)+_xW.a|0,_xP,_xU,_xW);}else{var _xX=_xU.a,_xY=E(_xQ);return (_xY._==0)?new T4(1,(_xT+_xX|0)+_xY.a|0,_xP,_xU,_xY):new T4(1,(_xT+_xX|0)+_xY.a|0,_xP,_xU,_xY);}},_xZ=E(_xP);if(!_xZ._){return _xS(_xZ.a);}else{return _xS(_xZ.a);}}),_y0=new T(function(){var _y1=function(_y2){var _y3=E(_xn);if(!_y3._){var _y4=_y3.a,_y5=E(_wa);return (_y5._==0)?new T4(1,(_y2+_y4|0)+_y5.a|0,_xm,_y3,_y5):new T4(1,(_y2+_y4|0)+_y5.a|0,_xm,_y3,_y5);}else{var _y6=_y3.a,_y7=E(_wa);return (_y7._==0)?new T4(1,(_y2+_y6|0)+_y7.a|0,_xm,_y3,_y7):new T4(1,(_y2+_y6|0)+_y7.a|0,_xm,_y3,_y7);}},_y8=E(_xm);if(!_y8._){return _y1(_y8.a);}else{return _y1(_y8.a);}});return _bX(_wg,_y0,_xR,_wj);break;default:var _y9=_xo.b,_ya=_xo.d,_yb=new T(function(){var _yc=function(_yd){var _ye=E(_xn);if(!_ye._){var _yf=_ye.a,_yg=E(_wa);return (_yg._==0)?new T4(1,(_yd+_yf|0)+_yg.a|0,_xm,_ye,_yg):new T4(1,(_yd+_yf|0)+_yg.a|0,_xm,_ye,_yg);}else{var _yh=_ye.a,_yi=E(_wa);return (_yi._==0)?new T4(1,(_yd+_yh|0)+_yi.a|0,_xm,_ye,_yi):new T4(1,(_yd+_yh|0)+_yi.a|0,_xm,_ye,_yi);}},_yj=E(_xm);if(!_yj._){return _yc(_yj.a);}else{return _yc(_yj.a);}});return B(_c8(_wg,_yb,new T(function(){var _yk=E(_xo.a);if(!_yk._){var _yl=_yk.a,_ym=E(_y9);if(!_ym._){return new T3(0,_yl+_ym.a|0,_yk,_ym);}else{return new T3(0,_yl+_ym.a|0,_yk,_ym);}}else{var _yn=_yk.a,_yo=E(_y9);if(!_yo._){return new T3(0,_yn+_yo.a|0,_yk,_yo);}else{return new T3(0,_yn+_yo.a|0,_yk,_yo);}}}),new T(function(){var _yp=E(_xo.c);if(!_yp._){var _yq=_yp.a,_yr=E(_ya);if(!_yr._){return new T3(0,_yq+_yr.a|0,_yp,_yr);}else{return new T3(0,_yq+_yr.a|0,_yp,_yr);}}else{var _ys=_yp.a,_yt=E(_ya);if(!_yt._){return new T3(0,_ys+_yt.a|0,_yp,_yt);}else{return new T3(0,_ys+_yt.a|0,_yp,_yt);}}}),_wj));}break;case 2:var _yu=_wn.a,_yv=_wn.b,_yw=_wn.c,_yx=E(_wi);switch(_yx._){case 0:var _yy=_yx.a,_yz=new T(function(){var _yA=function(_yB){var _yC=E(_yv);if(!_yC._){var _yD=_yC.a,_yE=E(_yw);return (_yE._==0)?new T4(1,(_yB+_yD|0)+_yE.a|0,_yu,_yC,_yE):new T4(1,(_yB+_yD|0)+_yE.a|0,_yu,_yC,_yE);}else{var _yF=_yC.a,_yG=E(_yw);return (_yG._==0)?new T4(1,(_yB+_yF|0)+_yG.a|0,_yu,_yC,_yG):new T4(1,(_yB+_yF|0)+_yG.a|0,_yu,_yC,_yG);}},_yH=E(_yu);if(!_yH._){return _yA(_yH.a);}else{return _yA(_yH.a);}});return _bX(_wg,_yz,new T(function(){var _yI=E(_wa);if(!_yI._){var _yJ=_yI.a,_yK=E(_yy);if(!_yK._){return new T3(0,_yJ+_yK.a|0,_yI,_yK);}else{return new T3(0,_yJ+_yK.a|0,_yI,_yK);}}else{var _yL=_yI.a,_yM=E(_yy);if(!_yM._){return new T3(0,_yL+_yM.a|0,_yI,_yM);}else{return new T3(0,_yL+_yM.a|0,_yI,_yM);}}}),_wj);break;case 1:var _yN=_yx.b,_yO=new T(function(){var _yP=function(_yQ){var _yR=E(_yx.a);if(!_yR._){var _yS=_yR.a,_yT=E(_yN);return (_yT._==0)?new T4(1,(_yQ+_yS|0)+_yT.a|0,_wa,_yR,_yT):new T4(1,(_yQ+_yS|0)+_yT.a|0,_wa,_yR,_yT);}else{var _yU=_yR.a,_yV=E(_yN);return (_yV._==0)?new T4(1,(_yQ+_yU|0)+_yV.a|0,_wa,_yR,_yV):new T4(1,(_yQ+_yU|0)+_yV.a|0,_wa,_yR,_yV);}},_yW=E(_wa);if(!_yW._){return _yP(_yW.a);}else{return _yP(_yW.a);}}),_yX=new T(function(){var _yY=function(_yZ){var _z0=E(_yv);if(!_z0._){var _z1=_z0.a,_z2=E(_yw);return (_z2._==0)?new T4(1,(_yZ+_z1|0)+_z2.a|0,_yu,_z0,_z2):new T4(1,(_yZ+_z1|0)+_z2.a|0,_yu,_z0,_z2);}else{var _z3=_z0.a,_z4=E(_yw);return (_z4._==0)?new T4(1,(_yZ+_z3|0)+_z4.a|0,_yu,_z0,_z4):new T4(1,(_yZ+_z3|0)+_z4.a|0,_yu,_z0,_z4);}},_z5=E(_yu);if(!_z5._){return _yY(_z5.a);}else{return _yY(_z5.a);}});return _bX(_wg,_yX,_yO,_wj);break;case 2:var _z6=_yx.a,_z7=_yx.c,_z8=new T(function(){var _z9=function(_za){var _zb=E(_yv);if(!_zb._){var _zc=_zb.a,_zd=E(_yw);return (_zd._==0)?new T4(1,(_za+_zc|0)+_zd.a|0,_yu,_zb,_zd):new T4(1,(_za+_zc|0)+_zd.a|0,_yu,_zb,_zd);}else{var _ze=_zb.a,_zf=E(_yw);return (_zf._==0)?new T4(1,(_za+_ze|0)+_zf.a|0,_yu,_zb,_zf):new T4(1,(_za+_ze|0)+_zf.a|0,_yu,_zb,_zf);}},_zg=E(_yu);if(!_zg._){return _z9(_zg.a);}else{return _z9(_zg.a);}});return B(_c8(_wg,_z8,new T(function(){var _zh=E(_wa);if(!_zh._){var _zi=_zh.a,_zj=E(_z6);if(!_zj._){return new T3(0,_zi+_zj.a|0,_zh,_zj);}else{return new T3(0,_zi+_zj.a|0,_zh,_zj);}}else{var _zk=_zh.a,_zl=E(_z6);if(!_zl._){return new T3(0,_zk+_zl.a|0,_zh,_zl);}else{return new T3(0,_zk+_zl.a|0,_zh,_zl);}}}),new T(function(){var _zm=E(_yx.b);if(!_zm._){var _zn=_zm.a,_zo=E(_z7);if(!_zo._){return new T3(0,_zn+_zo.a|0,_zm,_zo);}else{return new T3(0,_zn+_zo.a|0,_zm,_zo);}}else{var _zp=_zm.a,_zq=E(_z7);if(!_zq._){return new T3(0,_zp+_zq.a|0,_zm,_zq);}else{return new T3(0,_zp+_zq.a|0,_zm,_zq);}}}),_wj));break;default:var _zr=_yx.b,_zs=_yx.d,_zt=new T(function(){var _zu=function(_zv){var _zw=E(_yx.a);if(!_zw._){var _zx=_zw.a,_zy=E(_zr);return (_zy._==0)?new T4(1,(_zv+_zx|0)+_zy.a|0,_wa,_zw,_zy):new T4(1,(_zv+_zx|0)+_zy.a|0,_wa,_zw,_zy);}else{var _zz=_zw.a,_zA=E(_zr);return (_zA._==0)?new T4(1,(_zv+_zz|0)+_zA.a|0,_wa,_zw,_zA):new T4(1,(_zv+_zz|0)+_zA.a|0,_wa,_zw,_zA);}},_zB=E(_wa);if(!_zB._){return _zu(_zB.a);}else{return _zu(_zB.a);}}),_zC=new T(function(){var _zD=function(_zE){var _zF=E(_yv);if(!_zF._){var _zG=_zF.a,_zH=E(_yw);return (_zH._==0)?new T4(1,(_zE+_zG|0)+_zH.a|0,_yu,_zF,_zH):new T4(1,(_zE+_zG|0)+_zH.a|0,_yu,_zF,_zH);}else{var _zI=_zF.a,_zJ=E(_yw);return (_zJ._==0)?new T4(1,(_zE+_zI|0)+_zJ.a|0,_yu,_zF,_zJ):new T4(1,(_zE+_zI|0)+_zJ.a|0,_yu,_zF,_zJ);}},_zK=E(_yu);if(!_zK._){return _zD(_zK.a);}else{return _zD(_zK.a);}});return B(_c8(_wg,_zC,_zt,new T(function(){var _zL=E(_yx.c);if(!_zL._){var _zM=_zL.a,_zN=E(_zs);if(!_zN._){return new T3(0,_zM+_zN.a|0,_zL,_zN);}else{return new T3(0,_zM+_zN.a|0,_zL,_zN);}}else{var _zO=_zL.a,_zP=E(_zs);if(!_zP._){return new T3(0,_zO+_zP.a|0,_zL,_zP);}else{return new T3(0,_zO+_zP.a|0,_zL,_zP);}}}),_wj));}break;default:var _zQ=_wn.a,_zR=_wn.b,_zS=_wn.c,_zT=_wn.d,_zU=E(_wi);switch(_zU._){case 0:var _zV=_zU.a,_zW=new T(function(){var _zX=function(_zY){var _zZ=E(_wa);if(!_zZ._){var _A0=_zZ.a,_A1=E(_zV);return (_A1._==0)?new T4(1,(_zY+_A0|0)+_A1.a|0,_zT,_zZ,_A1):new T4(1,(_zY+_A0|0)+_A1.a|0,_zT,_zZ,_A1);}else{var _A2=_zZ.a,_A3=E(_zV);return (_A3._==0)?new T4(1,(_zY+_A2|0)+_A3.a|0,_zT,_zZ,_A3):new T4(1,(_zY+_A2|0)+_A3.a|0,_zT,_zZ,_A3);}},_A4=E(_zT);if(!_A4._){return _zX(_A4.a);}else{return _zX(_A4.a);}}),_A5=new T(function(){var _A6=function(_A7){var _A8=E(_zR);if(!_A8._){var _A9=_A8.a,_Aa=E(_zS);return (_Aa._==0)?new T4(1,(_A7+_A9|0)+_Aa.a|0,_zQ,_A8,_Aa):new T4(1,(_A7+_A9|0)+_Aa.a|0,_zQ,_A8,_Aa);}else{var _Ab=_A8.a,_Ac=E(_zS);return (_Ac._==0)?new T4(1,(_A7+_Ab|0)+_Ac.a|0,_zQ,_A8,_Ac):new T4(1,(_A7+_Ab|0)+_Ac.a|0,_zQ,_A8,_Ac);}},_Ad=E(_zQ);if(!_Ad._){return _A6(_Ad.a);}else{return _A6(_Ad.a);}});return _bX(_wg,_A5,_zW,_wj);break;case 1:var _Ae=_zU.b,_Af=new T(function(){var _Ag=function(_Ah){var _Ai=E(_zR);if(!_Ai._){var _Aj=_Ai.a,_Ak=E(_zS);return (_Ak._==0)?new T4(1,(_Ah+_Aj|0)+_Ak.a|0,_zQ,_Ai,_Ak):new T4(1,(_Ah+_Aj|0)+_Ak.a|0,_zQ,_Ai,_Ak);}else{var _Al=_Ai.a,_Am=E(_zS);return (_Am._==0)?new T4(1,(_Ah+_Al|0)+_Am.a|0,_zQ,_Ai,_Am):new T4(1,(_Ah+_Al|0)+_Am.a|0,_zQ,_Ai,_Am);}},_An=E(_zQ);if(!_An._){return _Ag(_An.a);}else{return _Ag(_An.a);}});return B(_c8(_wg,_Af,new T(function(){var _Ao=E(_zT);if(!_Ao._){var _Ap=_Ao.a,_Aq=E(_wa);if(!_Aq._){return new T3(0,_Ap+_Aq.a|0,_Ao,_Aq);}else{return new T3(0,_Ap+_Aq.a|0,_Ao,_Aq);}}else{var _Ar=_Ao.a,_As=E(_wa);if(!_As._){return new T3(0,_Ar+_As.a|0,_Ao,_As);}else{return new T3(0,_Ar+_As.a|0,_Ao,_As);}}}),new T(function(){var _At=E(_zU.a);if(!_At._){var _Au=_At.a,_Av=E(_Ae);if(!_Av._){return new T3(0,_Au+_Av.a|0,_At,_Av);}else{return new T3(0,_Au+_Av.a|0,_At,_Av);}}else{var _Aw=_At.a,_Ax=E(_Ae);if(!_Ax._){return new T3(0,_Aw+_Ax.a|0,_At,_Ax);}else{return new T3(0,_Aw+_Ax.a|0,_At,_Ax);}}}),_wj));break;case 2:var _Ay=_zU.a,_Az=_zU.c,_AA=new T(function(){var _AB=function(_AC){var _AD=E(_wa);if(!_AD._){var _AE=_AD.a,_AF=E(_Ay);return (_AF._==0)?new T4(1,(_AC+_AE|0)+_AF.a|0,_zT,_AD,_AF):new T4(1,(_AC+_AE|0)+_AF.a|0,_zT,_AD,_AF);}else{var _AG=_AD.a,_AH=E(_Ay);return (_AH._==0)?new T4(1,(_AC+_AG|0)+_AH.a|0,_zT,_AD,_AH):new T4(1,(_AC+_AG|0)+_AH.a|0,_zT,_AD,_AH);}},_AI=E(_zT);if(!_AI._){return _AB(_AI.a);}else{return _AB(_AI.a);}}),_AJ=new T(function(){var _AK=function(_AL){var _AM=E(_zR);if(!_AM._){var _AN=_AM.a,_AO=E(_zS);return (_AO._==0)?new T4(1,(_AL+_AN|0)+_AO.a|0,_zQ,_AM,_AO):new T4(1,(_AL+_AN|0)+_AO.a|0,_zQ,_AM,_AO);}else{var _AP=_AM.a,_AQ=E(_zS);return (_AQ._==0)?new T4(1,(_AL+_AP|0)+_AQ.a|0,_zQ,_AM,_AQ):new T4(1,(_AL+_AP|0)+_AQ.a|0,_zQ,_AM,_AQ);}},_AR=E(_zQ);if(!_AR._){return _AK(_AR.a);}else{return _AK(_AR.a);}});return B(_c8(_wg,_AJ,_AA,new T(function(){var _AS=E(_zU.b);if(!_AS._){var _AT=_AS.a,_AU=E(_Az);if(!_AU._){return new T3(0,_AT+_AU.a|0,_AS,_AU);}else{return new T3(0,_AT+_AU.a|0,_AS,_AU);}}else{var _AV=_AS.a,_AW=E(_Az);if(!_AW._){return new T3(0,_AV+_AW.a|0,_AS,_AW);}else{return new T3(0,_AV+_AW.a|0,_AS,_AW);}}}),_wj));break;default:var _AX=_zU.a,_AY=_zU.b,_AZ=_zU.d,_B0=new T(function(){var _B1=function(_B2){var _B3=E(_zU.c);if(!_B3._){var _B4=_B3.a,_B5=E(_AZ);return (_B5._==0)?new T4(1,(_B2+_B4|0)+_B5.a|0,_AY,_B3,_B5):new T4(1,(_B2+_B4|0)+_B5.a|0,_AY,_B3,_B5);}else{var _B6=_B3.a,_B7=E(_AZ);return (_B7._==0)?new T4(1,(_B2+_B6|0)+_B7.a|0,_AY,_B3,_B7):new T4(1,(_B2+_B6|0)+_B7.a|0,_AY,_B3,_B7);}},_B8=E(_AY);if(!_B8._){return _B1(_B8.a);}else{return _B1(_B8.a);}}),_B9=new T(function(){var _Ba=function(_Bb){var _Bc=E(_wa);if(!_Bc._){var _Bd=_Bc.a,_Be=E(_AX);return (_Be._==0)?new T4(1,(_Bb+_Bd|0)+_Be.a|0,_zT,_Bc,_Be):new T4(1,(_Bb+_Bd|0)+_Be.a|0,_zT,_Bc,_Be);}else{var _Bf=_Bc.a,_Bg=E(_AX);return (_Bg._==0)?new T4(1,(_Bb+_Bf|0)+_Bg.a|0,_zT,_Bc,_Bg):new T4(1,(_Bb+_Bf|0)+_Bg.a|0,_zT,_Bc,_Bg);}},_Bh=E(_zT);if(!_Bh._){return _Ba(_Bh.a);}else{return _Ba(_Bh.a);}}),_Bi=new T(function(){var _Bj=function(_Bk){var _Bl=E(_zR);if(!_Bl._){var _Bm=_Bl.a,_Bn=E(_zS);return (_Bn._==0)?new T4(1,(_Bk+_Bm|0)+_Bn.a|0,_zQ,_Bl,_Bn):new T4(1,(_Bk+_Bm|0)+_Bn.a|0,_zQ,_Bl,_Bn);}else{var _Bo=_Bl.a,_Bp=E(_zS);return (_Bp._==0)?new T4(1,(_Bk+_Bo|0)+_Bp.a|0,_zQ,_Bl,_Bp):new T4(1,(_Bk+_Bo|0)+_Bp.a|0,_zQ,_Bl,_Bp);}},_Bq=E(_zQ);if(!_Bq._){return _Bj(_Bq.a);}else{return _Bj(_Bq.a);}});return B(_c8(_wg,_Bi,_B9,_B0,_wj));}}});return new T4(2,(_we+_wl|0)+_wd.a|0,E(_wf),_wm,E(_wd.d));},_Br=E(_wa);if(!_Br._){return _wk(_Br.a);}else{return _wk(_Br.a);}}}}}},_Bs=function(_Bt,_Bu,_Bv,_Bw,_Bx){var _By=E(_Bt);switch(_By._){case 0:return new T1(1,new T4(1,_Bu,_Bv,_Bw,_Bx));case 1:var _Bz=E(_By.a);return (_Bz._==0)?new T4(2,_Bz.a+_Bu|0,E(new T1(0,_Bz)),__Z,E(new T1(0,new T4(1,_Bu,_Bv,_Bw,_Bx)))):new T4(2,_Bz.a+_Bu|0,E(new T1(0,_Bz)),__Z,E(new T1(0,new T4(1,_Bu,_Bv,_Bw,_Bx))));default:var _BA=_By.a,_BB=_By.b,_BC=_By.c,_BD=E(_By.d);switch(_BD._){case 0:return new T4(2,_BA+_Bu|0,E(_BB),_BC,E(new T2(1,_BD.a,new T4(1,_Bu,_Bv,_Bw,_Bx))));case 1:return new T4(2,_BA+_Bu|0,E(_BB),_BC,E(new T3(2,_BD.a,_BD.b,new T4(1,_Bu,_Bv,_Bw,_Bx))));case 2:return new T4(2,_BA+_Bu|0,E(_BB),_BC,E(new T4(3,_BD.a,_BD.b,_BD.c,new T4(1,_Bu,_Bv,_Bw,_Bx))));default:var _BE=_BD.b,_BF=_BD.c,_BG=new T(function(){return _9Z(E(_BC),new T(function(){var _BH=E(_BD.a);if(!_BH._){var _BI=_BH.a,_BJ=E(_BE);if(!_BJ._){var _BK=_BJ.a,_BL=E(_BF);if(!_BL._){return new T4(1,(_BI+_BK|0)+_BL.a|0,_BH,_BJ,_BL);}else{return new T4(1,(_BI+_BK|0)+_BL.a|0,_BH,_BJ,_BL);}}else{var _BM=_BJ.a,_BN=E(_BF);if(!_BN._){return new T4(1,(_BI+_BM|0)+_BN.a|0,_BH,_BJ,_BN);}else{return new T4(1,(_BI+_BM|0)+_BN.a|0,_BH,_BJ,_BN);}}}else{var _BO=_BH.a,_BP=E(_BE);if(!_BP._){var _BQ=_BP.a,_BR=E(_BF);if(!_BR._){return new T4(1,(_BO+_BQ|0)+_BR.a|0,_BH,_BP,_BR);}else{return new T4(1,(_BO+_BQ|0)+_BR.a|0,_BH,_BP,_BR);}}else{var _BS=_BP.a,_BT=E(_BF);if(!_BT._){return new T4(1,(_BO+_BS|0)+_BT.a|0,_BH,_BP,_BT);}else{return new T4(1,(_BO+_BS|0)+_BT.a|0,_BH,_BP,_BT);}}}}));});return new T4(2,_BA+_Bu|0,E(_BB),_BG,E(new T2(1,_BD.d,new T4(1,_Bu,_Bv,_Bw,_Bx))));}}},_BU=function(_BV,_BW){var _BX=E(_BV);switch(_BX._){case 0:return new T1(1,_BW);case 1:return new T4(2,2,E(new T1(0,_BX.a)),__Z,E(new T1(0,_BW)));default:var _BY=_BX.a,_BZ=_BX.b,_C0=_BX.c,_C1=E(_BX.d);switch(_C1._){case 0:return new T4(2,_BY+1|0,E(_BZ),_C0,E(new T2(1,_C1.a,_BW)));case 1:return new T4(2,_BY+1|0,E(_BZ),_C0,E(new T3(2,_C1.a,_C1.b,_BW)));case 2:return new T4(2,_BY+1|0,E(_BZ),_C0,E(new T4(3,_C1.a,_C1.b,_C1.c,_BW)));default:return new T4(2,_BY+1|0,E(_BZ),new T(function(){return _Bs(E(_C0),3,_C1.a,_C1.b,_C1.c);}),E(new T2(1,_C1.d,_BW)));}}},_C2=function(_C3,_C4){var _C5=E(_C3);if(!_C5._){return E(_C4);}else{var _C6=E(_C4);if(!_C6._){return _C5;}else{if(_C5._==1){return _9R(_C5.a,_C6);}else{var _C7=_C5.c;if(_C6._==1){return _BU(_C5,_C6.a);}else{var _C8=_C6.b,_C9=_C6.c;return new T4(2,_C5.a+_C6.a|0,E(_C5.b),new T(function(){var _Ca=E(_C5.d);switch(_Ca._){case 0:var _Cb=_Ca.a,_Cc=E(_C8);switch(_Cc._){case 0:return _w8(_C7,new T3(0,2,_Cb,_Cc.a),_C9);break;case 1:return _w8(_C7,new T4(1,3,_Cb,_Cc.a,_Cc.b),_C9);break;case 2:return _bX(_C7,new T3(0,2,_Cb,_Cc.a),new T3(0,2,_Cc.b,_Cc.c),_C9);break;default:return _bX(_C7,new T4(1,3,_Cb,_Cc.a,_Cc.b),new T3(0,2,_Cc.c,_Cc.d),_C9);}break;case 1:var _Cd=_Ca.a,_Ce=_Ca.b,_Cf=E(_C8);switch(_Cf._){case 0:return _w8(_C7,new T4(1,3,_Cd,_Ce,_Cf.a),_C9);break;case 1:return _bX(_C7,new T3(0,2,_Cd,_Ce),new T3(0,2,_Cf.a,_Cf.b),_C9);break;case 2:return _bX(_C7,new T4(1,3,_Cd,_Ce,_Cf.a),new T3(0,2,_Cf.b,_Cf.c),_C9);break;default:return _bX(_C7,new T4(1,3,_Cd,_Ce,_Cf.a),new T4(1,3,_Cf.b,_Cf.c,_Cf.d),_C9);}break;case 2:var _Cg=_Ca.a,_Ch=_Ca.b,_Ci=_Ca.c,_Cj=E(_C8);switch(_Cj._){case 0:return _bX(_C7,new T3(0,2,_Cg,_Ch),new T3(0,2,_Ci,_Cj.a),_C9);break;case 1:return _bX(_C7,new T4(1,3,_Cg,_Ch,_Ci),new T3(0,2,_Cj.a,_Cj.b),_C9);break;case 2:return _bX(_C7,new T4(1,3,_Cg,_Ch,_Ci),new T4(1,3,_Cj.a,_Cj.b,_Cj.c),_C9);break;default:return B(_c8(_C7,new T4(1,3,_Cg,_Ch,_Ci),new T3(0,2,_Cj.a,_Cj.b),new T3(0,2,_Cj.c,_Cj.d),_C9));}break;default:var _Ck=_Ca.a,_Cl=_Ca.b,_Cm=_Ca.c,_Cn=_Ca.d,_Co=E(_C8);switch(_Co._){case 0:return _bX(_C7,new T4(1,3,_Ck,_Cl,_Cm),new T3(0,2,_Cn,_Co.a),_C9);break;case 1:return _bX(_C7,new T4(1,3,_Ck,_Cl,_Cm),new T4(1,3,_Cn,_Co.a,_Co.b),_C9);break;case 2:return B(_c8(_C7,new T4(1,3,_Ck,_Cl,_Cm),new T3(0,2,_Cn,_Co.a),new T3(0,2,_Co.b,_Co.c),_C9));break;default:return B(_c8(_C7,new T4(1,3,_Ck,_Cl,_Cm),new T4(1,3,_Cn,_Co.a,_Co.b),new T3(0,2,_Co.c,_Co.d),_C9));}}}),E(_C6.d));}}}}},_Cp=new T2(1,new T3(0,127,127,255),new T2(1,new T3(0,255,127,127),__Z)),_Cq=(function(e){e.width = e.width;}),_Cr=new T(function(){return toJSStr(__Z);}),_Cs=new T2(1,")",__Z),_Ct=function(_Cu){var _Cv=E(_Cu);if(!_Cv._){var _Cw=jsCat(new T2(1,"rgb(",new T2(1,new T(function(){return String(_Cv.a);}),new T2(1,",",new T2(1,new T(function(){return String(_Cv.b);}),new T2(1,",",new T2(1,new T(function(){return String(_Cv.c);}),_Cs)))))),E(_Cr));return E(_Cw);}else{var _Cx=jsCat(new T2(1,"rgba(",new T2(1,new T(function(){return String(_Cv.a);}),new T2(1,",",new T2(1,new T(function(){return String(_Cv.b);}),new T2(1,",",new T2(1,new T(function(){return String(_Cv.c);}),new T2(1,",",new T2(1,new T(function(){return String(_Cv.d);}),_Cs)))))))),E(_Cr));return E(_Cx);}},_Cy=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_Cz=(function(e,p,v){e[p] = v;}),_CA=function(_CB,_CC){var _CD=new T(function(){return _Ct(_CB);});return function(_CE,_){var _CF=E(_CE),_CG=_Cy(_CF,"fillStyle"),_CH=_Cy(_CF,"strokeStyle"),_CI=E(_CD),_CJ=_Cz(_CF,"fillStyle",_CI),_CK=_Cz(_CF,"strokeStyle",_CI),_CL=B(A2(_CC,_CF,_)),_CM=String(_CG),_CN=_Cz(_CF,"fillStyle",_CM),_CO=String(_CH),_CP=_Cz(_CF,"strokeStyle",_CO);return _3l(_);};},_CQ=function(_CR,_CS){if(_CR<=0){if(_CR>=0){return quot(_CR,_CS);}else{if(_CS<=0){return quot(_CR,_CS);}else{return quot(_CR+1|0,_CS)-1|0;}}}else{if(_CS>=0){if(_CR>=0){return quot(_CR,_CS);}else{if(_CS<=0){return quot(_CR,_CS);}else{return quot(_CR+1|0,_CS)-1|0;}}}else{return quot(_CR-1|0,_CS)-1|0;}}},_CT=function(_CU,_CV){while(1){var _CW=E(_CU);if(!_CW._){var _CX=E(_CW.a);if(_CX==( -2147483648)){_CU=new T1(1,I_fromInt( -2147483648));continue;}else{var _CY=E(_CV);if(!_CY._){var _CZ=_CY.a;return new T2(0,new T1(0,_CQ(_CX,_CZ)),new T1(0,_8v(_CX,_CZ)));}else{_CU=new T1(1,I_fromInt(_CX));_CV=_CY;continue;}}}else{var _D0=E(_CV);if(!_D0._){_CU=_CW;_CV=new T1(1,I_fromInt(_D0.a));continue;}else{var _D1=I_divMod(_CW.a,_D0.a);return new T2(0,new T1(1,_D1.a),new T1(1,_D1.b));}}}},_D2=new T(function(){return unCStr("base");}),_D3=new T(function(){return unCStr("GHC.Exception");}),_D4=new T(function(){return unCStr("ArithException");}),_D5=function(_D6){return E(new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_D2,_D3,_D4),__Z,__Z));},_D7=new T(function(){return unCStr("Ratio has zero denominator");}),_D8=new T(function(){return unCStr("denormal");}),_D9=new T(function(){return unCStr("divide by zero");}),_Da=new T(function(){return unCStr("loss of precision");}),_Db=new T(function(){return unCStr("arithmetic underflow");}),_Dc=new T(function(){return unCStr("arithmetic overflow");}),_Dd=function(_De,_Df){switch(E(_De)){case 0:return _x(_Dc,_Df);case 1:return _x(_Db,_Df);case 2:return _x(_Da,_Df);case 3:return _x(_D9,_Df);case 4:return _x(_D8,_Df);default:return _x(_D7,_Df);}},_Dg=function(_Dh){return _Dd(_Dh,__Z);},_Di=new T(function(){return new T5(0,_D5,new T3(0,function(_Dj,_Dk,_Dl){return _Dd(_Dk,_Dl);},_Dg,function(_Dm,_Dn){return _1t(_Dd,_Dm,_Dn);}),_Do,function(_Dp){var _Dq=E(_Dp);return _m(_k(_Dq.a),_D5,_Dq.b);},_Dg);}),_Do=function(_8d){return new T2(0,_Di,_8d);},_Dr=new T(function(){return die(new T(function(){return _Do(3);}));}),_Ds=function(_Dt){var _Du=E(_Dt);if(!_Du._){return _Du.a;}else{return I_toNumber(_Du.a);}},_Dv=function(_Dw,_Dx,_Dy){var _Dz=E(_Dy);if(!_Dz._){return new T2(0,__Z,new T1(0,_Dx));}else{var _DA=_Dz.a,_DB=E(_Dz.b);if(!_DB._){return new T2(0,__Z,new T2(1,_Dx,_DA));}else{var _DC=_DB.a,_DD=E(_DB.b);if(!_DD._){return new T2(0,__Z,new T3(2,_Dx,_DA,_DC));}else{var _DE=new T(function(){var _DF=_Dv(_Dw,_DD.a,_DD.b);return new T2(0,_DF.a,_DF.b);});return new T2(0,new T2(1,new T4(1,_Dw,_Dx,_DA,_DC),new T(function(){return E(E(_DE).a);})),new T(function(){return E(E(_DE).b);}));}}}},_DG=function(_DH){var _DI=E(_DH);return (_DI._==0)?_DI.a:_DI.a;},_DJ=function(_DK){var _DL=E(_DK);switch(_DL._){case 0:return _DG(_DL.a);case 1:var _DM=_DL.b,_DN=E(_DL.a);if(!_DN._){var _DO=_DN.a,_DP=E(_DM);return (_DP._==0)?_DO+_DP.a|0:_DO+_DP.a|0;}else{var _DQ=_DN.a,_DR=E(_DM);return (_DR._==0)?_DQ+_DR.a|0:_DQ+_DR.a|0;}break;case 2:var _DS=_DL.c,_DT=function(_DU){var _DV=E(_DL.b);if(!_DV._){var _DW=_DV.a,_DX=E(_DS);return (_DX._==0)?(_DU+_DW|0)+_DX.a|0:(_DU+_DW|0)+_DX.a|0;}else{var _DY=_DV.a,_DZ=E(_DS);return (_DZ._==0)?(_DU+_DY|0)+_DZ.a|0:(_DU+_DY|0)+_DZ.a|0;}},_E0=E(_DL.a);if(!_E0._){return _DT(_E0.a);}else{return _DT(_E0.a);}break;default:var _E1=_DL.d,_E2=function(_E3){var _E4=function(_E5){var _E6=E(_DL.c);if(!_E6._){var _E7=_E6.a,_E8=E(_E1);return (_E8._==0)?((_E3+_E5|0)+_E7|0)+_E8.a|0:((_E3+_E5|0)+_E7|0)+_E8.a|0;}else{var _E9=_E6.a,_Ea=E(_E1);return (_Ea._==0)?((_E3+_E5|0)+_E9|0)+_Ea.a|0:((_E3+_E5|0)+_E9|0)+_Ea.a|0;}},_Eb=E(_DL.b);if(!_Eb._){return _E4(_Eb.a);}else{return _E4(_Eb.a);}},_Ec=E(_DL.a);if(!_Ec._){return _E2(_Ec.a);}else{return _E2(_Ec.a);}}},_Ed=function(_Ee,_Ef){var _Eg=E(_Ef);if(!_Eg._){return __Z;}else{var _Eh=_Eg.a,_Ei=E(_Eg.b);if(!_Ei._){return new T1(1,_Eh);}else{var _Ej=_Ei.a,_Ek=E(_Ei.b);if(!_Ek._){return new T4(2,imul(2,_Ee)|0,E(new T1(0,_Eh)),__Z,E(new T1(0,_Ej)));}else{var _El=_Ek.a,_Em=E(_Ek.b);if(!_Em._){return new T4(2,imul(3,_Ee)|0,E(new T1(0,_Eh)),__Z,E(new T2(1,_Ej,_El)));}else{var _En=_Dv(imul(3,_Ee)|0,_Em.a,_Em.b),_Eo=_En.b,_Ep=function(_Eq){var _Er=E(_Ed(imul(3,_Ee)|0,_En.a));switch(_Er._){case 0:return new T4(2,(imul(3,_Eq)|0)+_DJ(_Eo)|0,E(new T3(2,_Eh,_Ej,_El)),__Z,E(_Eo));case 1:var _Es=E(_Er.a);return (_Es._==0)?new T4(2,((imul(3,_Eq)|0)+_Es.a|0)+_DJ(_Eo)|0,E(new T3(2,_Eh,_Ej,_El)),_Er,E(_Eo)):new T4(2,((imul(3,_Eq)|0)+_Es.a|0)+_DJ(_Eo)|0,E(new T3(2,_Eh,_Ej,_El)),_Er,E(_Eo));default:return new T4(2,((imul(3,_Eq)|0)+_Er.a|0)+_DJ(_Eo)|0,E(new T3(2,_Eh,_Ej,_El)),_Er,E(_Eo));}},_Et=E(_Eh);if(!_Et._){return _Ep(_Et.a);}else{return _Ep(_Et.a);}}}}}},_Eu=function(_Ev){var _Ew=E(_Ev);if(!_Ew._){return __Z;}else{var _Ex=_Ew.a,_Ey=E(_Ew.b);if(!_Ey._){return new T1(1,_Ex);}else{var _Ez=_Ey.a,_EA=E(_Ey.b);if(!_EA._){return new T4(2,2,E(new T1(0,_Ex)),__Z,E(new T1(0,_Ez)));}else{var _EB=_EA.a,_EC=E(_EA.b);if(!_EC._){return new T4(2,3,E(new T1(0,_Ex)),__Z,E(new T2(1,_Ez,_EB)));}else{var _ED=_Dv(3,_EC.a,_EC.b),_EE=_ED.b,_EF=_Ed(3,_ED.a);switch(_EF._){case 0:var _EG=E(_EE);switch(_EG._){case 0:return new T4(2,4,E(new T3(2,_Ex,_Ez,_EB)),__Z,_EG);case 1:return new T4(2,5,E(new T3(2,_Ex,_Ez,_EB)),__Z,_EG);case 2:return new T4(2,6,E(new T3(2,_Ex,_Ez,_EB)),__Z,_EG);default:return new T4(2,7,E(new T3(2,_Ex,_Ez,_EB)),__Z,_EG);}break;case 1:var _EH=E(_EF.a);if(!_EH._){var _EI=_EH.a,_EJ=E(_EE);switch(_EJ._){case 0:return new T4(2,(3+_EI|0)+1|0,E(new T3(2,_Ex,_Ez,_EB)),_EF,_EJ);case 1:return new T4(2,(3+_EI|0)+2|0,E(new T3(2,_Ex,_Ez,_EB)),_EF,_EJ);case 2:return new T4(2,(3+_EI|0)+3|0,E(new T3(2,_Ex,_Ez,_EB)),_EF,_EJ);default:return new T4(2,(3+_EI|0)+4|0,E(new T3(2,_Ex,_Ez,_EB)),_EF,_EJ);}}else{var _EK=_EH.a,_EL=E(_EE);switch(_EL._){case 0:return new T4(2,(3+_EK|0)+1|0,E(new T3(2,_Ex,_Ez,_EB)),_EF,_EL);case 1:return new T4(2,(3+_EK|0)+2|0,E(new T3(2,_Ex,_Ez,_EB)),_EF,_EL);case 2:return new T4(2,(3+_EK|0)+3|0,E(new T3(2,_Ex,_Ez,_EB)),_EF,_EL);default:return new T4(2,(3+_EK|0)+4|0,E(new T3(2,_Ex,_Ez,_EB)),_EF,_EL);}}break;default:var _EM=_EF.a,_EN=E(_EE);switch(_EN._){case 0:return new T4(2,(3+_EM|0)+1|0,E(new T3(2,_Ex,_Ez,_EB)),_EF,_EN);case 1:return new T4(2,(3+_EM|0)+2|0,E(new T3(2,_Ex,_Ez,_EB)),_EF,_EN);case 2:return new T4(2,(3+_EM|0)+3|0,E(new T3(2,_Ex,_Ez,_EB)),_EF,_EN);default:return new T4(2,(3+_EM|0)+4|0,E(new T3(2,_Ex,_Ez,_EB)),_EF,_EN);}}}}}}},_EO=(function(e){return e.getContext('2d');}),_EP=(function(e){return !!e.getContext;}),_EQ=function(_ER){return E(E(_ER).b);},_ES=function(_ET,_EU){return C > 19 ? new F(function(){return A2(_EQ,_ET,function(_){var _EV=E(_EU),_EW=_EP(_EV);if(!_EW){return __Z;}else{var _EX=_EO(_EV);return new T1(1,new T2(0,_EX,_EV));}});}) : (++C,A2(_EQ,_ET,function(_){var _EV=E(_EU),_EW=_EP(_EV);if(!_EW){return __Z;}else{var _EX=_EO(_EV);return new T1(1,new T2(0,_EX,_EV));}}));},_EY=function(_EZ){return E(E(_EZ).b);},_F0=function(_F1){return fromJSStr(E(_F1));},_F2=function(_F3){return E(E(_F3).a);},_F4=function(_F5,_F6,_F7,_F8){var _F9=new T(function(){var _Fa=function(_){var _Fb=_Cy(B(A2(_F2,_F5,_F7)),E(_F8));return new T(function(){return String(_Fb);});};return _Fa;});return C > 19 ? new F(function(){return A2(_EQ,_F6,_F9);}) : (++C,A2(_EQ,_F6,_F9));},_Fc=function(_Fd,_Fe,_Ff,_Fg){var _Fh=_3m(_Fe),_Fi=new T(function(){return _3o(_Fh);}),_Fj=function(_Fk){return C > 19 ? new F(function(){return A1(_Fi,new T(function(){return _F0(_Fk);}));}) : (++C,A1(_Fi,new T(function(){return _F0(_Fk);})));},_Fl=new T(function(){return B(_F4(_Fd,_Fe,_Ff,new T(function(){return toJSStr(E(_Fg));},1)));});return C > 19 ? new F(function(){return A3(_EY,_Fh,_Fl,_Fj);}) : (++C,A3(_EY,_Fh,_Fl,_Fj));},_Fm=function(_Fn){return E(_Fn);},_Fo=function(_Fp,_Fq){return C > 19 ? new F(function(){return A3(_EY,_Fr,_Fp,function(_Fs){return E(_Fq);});}) : (++C,A3(_EY,_Fr,_Fp,function(_Fs){return E(_Fq);}));},_Fr=new T(function(){return new T5(0,new T5(0,new T2(0,function(_Ft){return E(_Ft);},function(_Fu,_Fv){return E(_Fu);}),_Fm,function(_Fw){return E(_Fw);},function(_Fx,_Fy){return E(_Fy);},function(_Fz,_FA){return E(_Fz);}),function(_FB,_FC){return C > 19 ? new F(function(){return A1(_FC,_FB);}) : (++C,A1(_FC,_FB));},_Fo,_Fm,function(_FD){return err(_FD);});}),_FE=new T2(0,_Fr,function(_FF){var _FG=E(_FF);return (_FG._==0)?__Z:new T1(1,new T2(0,_FG.a,_FG.b));}),_FH=new T(function(){return unCStr("ACK");}),_FI=new T(function(){return unCStr("BEL");}),_FJ=new T(function(){return unCStr("BS");}),_FK=new T(function(){return unCStr("SP");}),_FL=new T(function(){return unCStr("US");}),_FM=new T(function(){return unCStr("RS");}),_FN=new T(function(){return unCStr("GS");}),_FO=new T(function(){return unCStr("FS");}),_FP=new T(function(){return unCStr("ESC");}),_FQ=new T(function(){return unCStr("SUB");}),_FR=new T(function(){return unCStr("EM");}),_FS=new T(function(){return unCStr("CAN");}),_FT=new T(function(){return unCStr("ETB");}),_FU=new T(function(){return unCStr("SYN");}),_FV=new T(function(){return unCStr("NAK");}),_FW=new T(function(){return unCStr("DC4");}),_FX=new T(function(){return unCStr("DC3");}),_FY=new T(function(){return unCStr("DC2");}),_FZ=new T(function(){return unCStr("DC1");}),_G0=new T(function(){return unCStr("DLE");}),_G1=new T(function(){return unCStr("SI");}),_G2=new T(function(){return unCStr("SO");}),_G3=new T(function(){return unCStr("CR");}),_G4=new T(function(){return unCStr("FF");}),_G5=new T(function(){return unCStr("VT");}),_G6=new T(function(){return unCStr("LF");}),_G7=new T(function(){return unCStr("HT");}),_G8=new T(function(){return unCStr("ENQ");}),_G9=new T(function(){return unCStr("EOT");}),_Ga=new T(function(){return unCStr("ETX");}),_Gb=new T(function(){return unCStr("STX");}),_Gc=new T(function(){return unCStr("SOH");}),_Gd=new T(function(){return unCStr("NUL");}),_Ge=new T(function(){return unCStr("\\DEL");}),_Gf=new T(function(){return unCStr("\\a");}),_Gg=new T(function(){return unCStr("\\\\");}),_Gh=new T(function(){return unCStr("\\SO");}),_Gi=new T(function(){return unCStr("\\r");}),_Gj=new T(function(){return unCStr("\\f");}),_Gk=new T(function(){return unCStr("\\v");}),_Gl=new T(function(){return unCStr("\\n");}),_Gm=new T(function(){return unCStr("\\t");}),_Gn=new T(function(){return unCStr("\\b");}),_Go=function(_Gp,_Gq){if(_Gp<=127){var _Gr=E(_Gp);switch(_Gr){case 92:return _x(_Gg,_Gq);case 127:return _x(_Ge,_Gq);default:if(_Gr<32){switch(_Gr){case 7:return _x(_Gf,_Gq);case 8:return _x(_Gn,_Gq);case 9:return _x(_Gm,_Gq);case 10:return _x(_Gl,_Gq);case 11:return _x(_Gk,_Gq);case 12:return _x(_Gj,_Gq);case 13:return _x(_Gi,_Gq);case 14:return _x(_Gh,new T(function(){var _Gs=E(_Gq);if(!_Gs._){return __Z;}else{if(E(_Gs.a)==72){return unAppCStr("\\&",_Gs);}else{return _Gs;}}},1));default:return _x(new T2(1,92,new T(function(){return _3L(new T2(1,_Gd,new T2(1,_Gc,new T2(1,_Gb,new T2(1,_Ga,new T2(1,_G9,new T2(1,_G8,new T2(1,_FH,new T2(1,_FI,new T2(1,_FJ,new T2(1,_G7,new T2(1,_G6,new T2(1,_G5,new T2(1,_G4,new T2(1,_G3,new T2(1,_G2,new T2(1,_G1,new T2(1,_G0,new T2(1,_FZ,new T2(1,_FY,new T2(1,_FX,new T2(1,_FW,new T2(1,_FV,new T2(1,_FU,new T2(1,_FT,new T2(1,_FS,new T2(1,_FR,new T2(1,_FQ,new T2(1,_FP,new T2(1,_FO,new T2(1,_FN,new T2(1,_FM,new T2(1,_FL,new T2(1,_FK,__Z))))))))))))))))))))))))))))))))),_Gr);})),_Gq);}}else{return new T2(1,_Gr,_Gq);}}}else{var _Gt=new T(function(){var _Gu=jsShowI(_Gp);return _x(fromJSStr(_Gu),new T(function(){var _Gv=E(_Gq);if(!_Gv._){return __Z;}else{var _Gw=E(_Gv.a);if(_Gw<48){return _Gv;}else{if(_Gw>57){return _Gv;}else{return unAppCStr("\\&",_Gv);}}}},1));});return new T2(1,92,_Gt);}},_Gx=new T(function(){return unCStr("\'\\\'\'");}),_Gy=function(_Gz,_GA){var _GB=E(_Gz);if(_GB==39){return _x(_Gx,_GA);}else{return new T2(1,39,new T(function(){return _Go(_GB,new T2(1,39,_GA));}));}},_GC=function(_GD){return _Gy(E(_GD),__Z);},_GE=function(_GF,_GG,_GH){return _Gy(E(_GG),_GH);},_GI=new T(function(){return unCStr("\\\"");}),_GJ=function(_GK,_GL){var _GM=E(_GK);if(!_GM._){return E(_GL);}else{var _GN=_GM.b,_GO=E(_GM.a);if(_GO==34){return _x(_GI,new T(function(){return _GJ(_GN,_GL);},1));}else{return _Go(_GO,new T(function(){return _GJ(_GN,_GL);}));}}},_GP=function(_GQ,_GR){return new T2(1,34,new T(function(){return _GJ(_GQ,new T2(1,34,_GR));}));},_GS=function(_GT,_GU){while(1){var _GV=E(_GT);if(!_GV._){return (E(_GU)._==0)?1:0;}else{var _GW=E(_GU);if(!_GW._){return 2;}else{var _GX=E(_GV.a),_GY=E(_GW.a);if(_GX!=_GY){return (_GX>_GY)?2:0;}else{_GT=_GV.b;_GU=_GW.b;continue;}}}}},_GZ=function(_H0,_H1){while(1){var _H2=E(_H0),_H3=E(_H1);if(!_H3._){switch(_GS(_H2,_H3.b)){case 0:_H0=_H2;_H1=_H3.c;continue;case 1:return true;default:_H0=_H2;_H1=_H3.d;continue;}}else{return false;}}},_H4=new T(function(){return _x(__Z,__Z);}),_H5=function(_H6,_H7,_H8,_H9,_Ha,_Hb,_Hc,_Hd){var _He=new T3(0,_H6,_H7,_H8),_Hf=function(_Hg){var _Hh=E(_H9);if(!_Hh._){var _Hi=E(_Hd);if(!_Hi._){switch(_GS(_H6,_Ha)){case 0:return new T2(0,new T3(0,_Ha,_Hb,_Hc),__Z);case 1:return (_H7>=_Hb)?(_H7!=_Hb)?new T2(0,_He,__Z):(_H8>=_Hc)?(_H8!=_Hc)?new T2(0,_He,__Z):new T2(0,_He,_H4):new T2(0,new T3(0,_Ha,_Hb,_Hc),__Z):new T2(0,new T3(0,_Ha,_Hb,_Hc),__Z);default:return new T2(0,_He,__Z);}}else{return new T2(0,new T3(0,_Ha,_Hb,_Hc),_Hi);}}else{switch(_GS(_H6,_Ha)){case 0:return new T2(0,new T3(0,_Ha,_Hb,_Hc),_Hd);case 1:return (_H7>=_Hb)?(_H7!=_Hb)?new T2(0,_He,_Hh):(_H8>=_Hc)?(_H8!=_Hc)?new T2(0,_He,_Hh):new T2(0,_He,new T(function(){return _x(_Hh,_Hd);})):new T2(0,new T3(0,_Ha,_Hb,_Hc),_Hd):new T2(0,new T3(0,_Ha,_Hb,_Hc),_Hd);default:return new T2(0,_He,_Hh);}}};if(!E(_Hd)._){var _Hj=E(_H9);if(!_Hj._){return _Hf(_);}else{return new T2(0,_He,_Hj);}}else{return _Hf(_);}},_Hk=function(_Hl,_Hm,_Hn,_Ho,_Hp){var _Hq=function(_Hr){return C > 19 ? new F(function(){return A3(_Hp,__Z,_Hm,new T(function(){var _Hs=E(E(_Hm).b),_Ht=E(_Hr),_Hu=E(_Ht.a),_Hv=_H5(_Hu.a,_Hu.b,_Hu.c,_Ht.b,_Hs.a,_Hs.b,_Hs.c,__Z);return new T2(0,E(_Hv.a),_Hv.b);}));}) : (++C,A3(_Hp,__Z,_Hm,new T(function(){var _Hs=E(E(_Hm).b),_Ht=E(_Hr),_Hu=E(_Ht.a),_Hv=_H5(_Hu.a,_Hu.b,_Hu.c,_Ht.b,_Hs.a,_Hs.b,_Hs.c,__Z);return new T2(0,E(_Hv.a),_Hv.b);})));},_Hw=function(_Hx,_Hy,_Hz){return C > 19 ? new F(function(){return A3(_Hp,new T1(1,_Hx),_Hy,new T(function(){var _HA=E(E(_Hy).b),_HB=E(_Hz),_HC=E(_HB.a),_HD=_H5(_HC.a,_HC.b,_HC.c,_HB.b,_HA.a,_HA.b,_HA.c,__Z);return new T2(0,E(_HD.a),_HD.b);}));}) : (++C,A3(_Hp,new T1(1,_Hx),_Hy,new T(function(){var _HA=E(E(_Hy).b),_HB=E(_Hz),_HC=E(_HB.a),_HD=_H5(_HC.a,_HC.b,_HC.c,_HB.b,_HA.a,_HA.b,_HA.c,__Z);return new T2(0,E(_HD.a),_HD.b);})));},_HE=function(_HF,_HG,_HH){return C > 19 ? new F(function(){return A3(_Hn,new T1(1,_HF),_HG,new T(function(){var _HI=E(E(_HG).b),_HJ=E(_HH),_HK=E(_HJ.a),_HL=_H5(_HK.a,_HK.b,_HK.c,_HJ.b,_HI.a,_HI.b,_HI.c,__Z);return new T2(0,E(_HL.a),_HL.b);}));}) : (++C,A3(_Hn,new T1(1,_HF),_HG,new T(function(){var _HI=E(E(_HG).b),_HJ=E(_HH),_HK=E(_HJ.a),_HL=_H5(_HK.a,_HK.b,_HK.c,_HJ.b,_HI.a,_HI.b,_HI.c,__Z);return new T2(0,E(_HL.a),_HL.b);})));};return C > 19 ? new F(function(){return A(_Hl,[_Hm,_HE,_Ho,_Hw,_Hq]);}) : (++C,A(_Hl,[_Hm,_HE,_Ho,_Hw,_Hq]));},_HM=function(_HN){return E(E(_HN).a);},_HO=new T2(1,34,__Z),_HP=function(_HQ){return E(E(_HQ).b);},_HR=function(_HS,_HT,_HU,_HV,_HW,_HX,_HY,_HZ,_I0){var _I1=new T3(0,_HV,_HW,_HX),_I2=new T(function(){return B(A1(_I0,new T2(0,E(_I1),new T2(1,new T1(0,E(__Z)),__Z))));}),_I3=function(_I4){var _I5=E(_I4);if(!_I5._){return E(_I2);}else{var _I6=E(_I5.a),_I7=_I6.a;if(!B(A1(_HT,_I7))){return C > 19 ? new F(function(){return A1(_I0,new T2(0,E(_I1),new T2(1,new T1(0,E(new T2(1,34,new T(function(){return _GJ(new T2(1,_I7,__Z),_HO);})))),__Z)));}) : (++C,A1(_I0,new T2(0,E(_I1),new T2(1,new T1(0,E(new T2(1,34,new T(function(){return _GJ(new T2(1,_I7,__Z),_HO);})))),__Z))));}else{var _I8=E(_I7);switch(_I8){case 9:var _I9=new T3(0,_HV,_HW,(_HX+8|0)-_8v(_HX-1|0,8)|0);break;case 10:var _I9=E(new T3(0,_HV,_HW+1|0,1));break;default:var _I9=E(new T3(0,_HV,_HW,_HX+1|0));}return C > 19 ? new F(function(){return A3(_HZ,_I8,new T3(0,_I6.b,E(_I9),E(_HY)),new T2(0,E(_I9),__Z));}) : (++C,A3(_HZ,_I8,new T3(0,_I6.b,E(_I9),E(_HY)),new T2(0,E(_I9),__Z)));}}};return C > 19 ? new F(function(){return A3(_EY,_HM(_HS),new T(function(){return B(A2(_HP,_HS,_HU));}),_I3);}) : (++C,A3(_EY,_HM(_HS),new T(function(){return B(A2(_HP,_HS,_HU));}),_I3));},_Ia=function(_Ib){return new T1(2,E(_Ib));},_Ic=new T(function(){return new T2(0,function(_Id,_Ie){switch(E(_Id)._){case 0:switch(E(_Ie)._){case 0:return true;case 1:return false;case 2:return false;default:return false;}break;case 1:return (E(_Ie)._==1)?true:false;case 2:return (E(_Ie)._==2)?true:false;default:return (E(_Ie)._==3)?true:false;}},_If);}),_Ig=function(_Ih){return E(E(_Ih).a);},_If=function(_Ii,_Ij){return (!B(A3(_Ig,_Ic,_Ii,_Ij)))?true:false;},_Ik=new T1(2,E(__Z)),_Il=function(_Im){return _If(_Ik,_Im);},_In=function(_Io,_Ip,_Iq){var _Ir=E(_Iq);if(!_Ir._){return new T2(0,_Io,new T2(1,_Ik,new T(function(){return _4z(_Il,_Ip);})));}else{var _Is=_Ir.a,_It=E(_Ir.b);if(!_It._){var _Iu=new T(function(){return new T1(2,E(_Is));}),_Iv=new T(function(){return _4z(function(_Im){return _If(_Iu,_Im);},_Ip);});return new T2(0,_Io,new T2(1,_Iu,_Iv));}else{var _Iw=new T(function(){return new T1(2,E(_Is));}),_Ix=new T(function(){return _4z(function(_Im){return _If(_Iw,_Im);},_Ip);}),_Iy=function(_Iz){var _IA=E(_Iz);if(!_IA._){return new T2(0,_Io,new T2(1,_Iw,_Ix));}else{var _IB=_Iy(_IA.b);return new T2(0,_IB.a,new T2(1,new T(function(){return _Ia(_IA.a);}),_IB.b));}};return _Iy(_It);}}},_IC=function(_ID,_IE){var _IF=E(_ID),_IG=_In(_IF.a,_IF.b,_IE);return new T2(0,E(_IG.a),_IG.b);},_IH=function(_II,_IJ,_IK,_IL,_IM,_IN,_IO){var _IP=function(_IQ){return C > 19 ? new F(function(){return A1(_IO,new T(function(){return _IC(_IQ,_IJ);}));}) : (++C,A1(_IO,new T(function(){return _IC(_IQ,_IJ);})));},_IR=function(_IS,_IT,_IU){return C > 19 ? new F(function(){return A3(_IN,_IS,_IT,new T(function(){var _IV=E(_IU),_IW=E(_IV.b);if(!_IW._){return _IV;}else{var _IX=_In(_IV.a,_IW,_IJ);return new T2(0,E(_IX.a),_IX.b);}}));}) : (++C,A3(_IN,_IS,_IT,new T(function(){var _IV=E(_IU),_IW=E(_IV.b);if(!_IW._){return _IV;}else{var _IX=_In(_IV.a,_IW,_IJ);return new T2(0,E(_IX.a),_IX.b);}})));};return C > 19 ? new F(function(){return A(_II,[_IK,_IL,_IM,_IR,_IP]);}) : (++C,A(_II,[_IK,_IL,_IM,_IR,_IP]));},_IY=function(_IZ){return (E(_IZ)-48|0)>>>0<=9;},_J0=function(_J1,_J2,_J3,_J4,_J5){var _J6=E(_J1),_J7=E(_J6.b);return C > 19 ? new F(function(){return _HR(_FE,_IY,_J6.a,_J7.a,_J7.b,_J7.c,_J6.c,_J2,_J5);}) : (++C,_HR(_FE,_IY,_J6.a,_J7.a,_J7.b,_J7.c,_J6.c,_J2,_J5));},_J8=new T(function(){return unCStr("digit");}),_J9=function(_Ja,_Jb,_Jc,_Jd,_Je){return C > 19 ? new F(function(){return _IH(_J0,new T2(1,_J8,__Z),_Ja,_Jb,_Jc,_Jd,_Je);}) : (++C,_IH(_J0,new T2(1,_J8,__Z),_Ja,_Jb,_Jc,_Jd,_Je));},_Jf=new T(function(){return err(new T(function(){return unCStr("Prelude.read: no parse");}));}),_Jg=new T(function(){return err(new T(function(){return unCStr("Prelude.read: ambiguous parse");}));}),_Jh=new T(function(){return B(_8s("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_Ji=function(_Jj,_Jk){while(1){var _Jl=(function(_Jm,_Jn){var _Jo=E(_Jm);switch(_Jo._){case 0:var _Jp=E(_Jn);if(!_Jp._){return __Z;}else{_Jj=B(A1(_Jo.a,_Jp.a));_Jk=_Jp.b;return __continue;}break;case 1:var _Jq=B(A1(_Jo.a,_Jn)),_Jr=_Jn;_Jj=_Jq;_Jk=_Jr;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_Jo.a,_Jn),new T(function(){return _Ji(_Jo.b,_Jn);}));default:return E(_Jo.a);}})(_Jj,_Jk);if(_Jl!=__continue){return _Jl;}}},_Js=function(_Jt,_Ju){var _Jv=function(_Jw){var _Jx=E(_Ju);if(_Jx._==3){return new T2(3,_Jx.a,new T(function(){return _Js(_Jt,_Jx.b);}));}else{var _Jy=E(_Jt);if(_Jy._==2){return _Jx;}else{if(_Jx._==2){return _Jy;}else{var _Jz=function(_JA){if(_Jx._==4){var _JB=function(_JC){return new T1(4,new T(function(){return _x(_Ji(_Jy,_JC),_Jx.a);}));};return new T1(1,_JB);}else{if(_Jy._==1){var _JD=_Jy.a;if(!_Jx._){return new T1(1,function(_JE){return _Js(B(A1(_JD,_JE)),_Jx);});}else{var _JF=function(_JG){return _Js(B(A1(_JD,_JG)),new T(function(){return B(A1(_Jx.a,_JG));}));};return new T1(1,_JF);}}else{if(!_Jx._){return E(_Jh);}else{var _JH=function(_JI){return _Js(_Jy,new T(function(){return B(A1(_Jx.a,_JI));}));};return new T1(1,_JH);}}}};switch(_Jy._){case 1:if(_Jx._==4){var _JJ=function(_JK){return new T1(4,new T(function(){return _x(_Ji(B(A1(_Jy.a,_JK)),_JK),_Jx.a);}));};return new T1(1,_JJ);}else{return _Jz(_);}break;case 4:var _JL=_Jy.a;switch(_Jx._){case 0:var _JM=function(_JN){var _JO=new T(function(){return _x(_JL,new T(function(){return _Ji(_Jx,_JN);},1));});return new T1(4,_JO);};return new T1(1,_JM);case 1:var _JP=function(_JQ){var _JR=new T(function(){return _x(_JL,new T(function(){return _Ji(B(A1(_Jx.a,_JQ)),_JQ);},1));});return new T1(4,_JR);};return new T1(1,_JP);default:return new T1(4,new T(function(){return _x(_JL,_Jx.a);}));}break;default:return _Jz(_);}}}}},_JS=E(_Jt);switch(_JS._){case 0:var _JT=E(_Ju);if(!_JT._){var _JU=function(_JV){return _Js(B(A1(_JS.a,_JV)),new T(function(){return B(A1(_JT.a,_JV));}));};return new T1(0,_JU);}else{return _Jv(_);}break;case 3:return new T2(3,_JS.a,new T(function(){return _Js(_JS.b,_Ju);}));default:return _Jv(_);}},_JW=new T(function(){return unCStr("(");}),_JX=new T(function(){return unCStr(")");}),_JY=function(_JZ,_K0){return E(_JZ)==E(_K0);},_K1=new T2(0,_JY,function(_K2,_K3){return E(_K2)!=E(_K3);}),_K4=function(_K5,_K6){while(1){var _K7=E(_K5);if(!_K7._){return (E(_K6)._==0)?true:false;}else{var _K8=E(_K6);if(!_K8._){return false;}else{if(E(_K7.a)!=E(_K8.a)){return false;}else{_K5=_K7.b;_K6=_K8.b;continue;}}}}},_K9=function(_Ka,_Kb){return (!_K4(_Ka,_Kb))?true:false;},_Kc=function(_Kd,_Ke){var _Kf=E(_Kd);switch(_Kf._){case 0:return new T1(0,function(_Kg){return C > 19 ? new F(function(){return _Kc(B(A1(_Kf.a,_Kg)),_Ke);}) : (++C,_Kc(B(A1(_Kf.a,_Kg)),_Ke));});case 1:return new T1(1,function(_Kh){return C > 19 ? new F(function(){return _Kc(B(A1(_Kf.a,_Kh)),_Ke);}) : (++C,_Kc(B(A1(_Kf.a,_Kh)),_Ke));});case 2:return new T0(2);case 3:return _Js(B(A1(_Ke,_Kf.a)),new T(function(){return B(_Kc(_Kf.b,_Ke));}));default:var _Ki=function(_Kj){var _Kk=E(_Kj);if(!_Kk._){return __Z;}else{var _Kl=E(_Kk.a);return _x(_Ji(B(A1(_Ke,_Kl.a)),_Kl.b),new T(function(){return _Ki(_Kk.b);},1));}},_Km=_Ki(_Kf.a);return (_Km._==0)?new T0(2):new T1(4,_Km);}},_Kn=new T0(2),_Ko=function(_Kp){return new T2(3,_Kp,_Kn);},_Kq=function(_Kr,_Ks){var _Kt=E(_Kr);if(!_Kt){return C > 19 ? new F(function(){return A1(_Ks,0);}) : (++C,A1(_Ks,0));}else{var _Ku=new T(function(){return B(_Kq(_Kt-1|0,_Ks));});return new T1(0,function(_Kv){return E(_Ku);});}},_Kw=function(_Kx,_Ky,_Kz){var _KA=new T(function(){return B(A1(_Kx,_Ko));}),_KB=function(_KC,_KD,_KE,_KF){while(1){var _KG=B((function(_KH,_KI,_KJ,_KK){var _KL=E(_KH);switch(_KL._){case 0:var _KM=E(_KI);if(!_KM._){return C > 19 ? new F(function(){return A1(_Ky,_KK);}) : (++C,A1(_Ky,_KK));}else{var _KN=_KJ+1|0,_KO=_KK;_KC=B(A1(_KL.a,_KM.a));_KD=_KM.b;_KE=_KN;_KF=_KO;return __continue;}break;case 1:var _KP=B(A1(_KL.a,_KI)),_KQ=_KI,_KN=_KJ,_KO=_KK;_KC=_KP;_KD=_KQ;_KE=_KN;_KF=_KO;return __continue;case 2:return C > 19 ? new F(function(){return A1(_Ky,_KK);}) : (++C,A1(_Ky,_KK));break;case 3:var _KR=new T(function(){return B(_Kc(_KL,_KK));});return C > 19 ? new F(function(){return _Kq(_KJ,function(_KS){return E(_KR);});}) : (++C,_Kq(_KJ,function(_KS){return E(_KR);}));break;default:return C > 19 ? new F(function(){return _Kc(_KL,_KK);}) : (++C,_Kc(_KL,_KK));}})(_KC,_KD,_KE,_KF));if(_KG!=__continue){return _KG;}}};return function(_KT){return _KB(_KA,_KT,0,_Kz);};},_KU=function(_KV){return C > 19 ? new F(function(){return A1(_KV,__Z);}) : (++C,A1(_KV,__Z));},_KW=function(_KX,_KY){var _KZ=function(_L0){var _L1=E(_L0);if(!_L1._){return _KU;}else{var _L2=_L1.a;if(!B(A1(_KX,_L2))){return _KU;}else{var _L3=new T(function(){return _KZ(_L1.b);}),_L4=function(_L5){var _L6=new T(function(){return B(A1(_L3,function(_L7){return C > 19 ? new F(function(){return A1(_L5,new T2(1,_L2,_L7));}) : (++C,A1(_L5,new T2(1,_L2,_L7)));}));});return new T1(0,function(_L8){return E(_L6);});};return _L4;}}};return function(_L9){return C > 19 ? new F(function(){return A2(_KZ,_L9,_KY);}) : (++C,A2(_KZ,_L9,_KY));};},_La=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_Lb=function(_Lc,_Ld){var _Le=function(_Lf,_Lg){var _Lh=E(_Lf);if(!_Lh._){var _Li=new T(function(){return B(A1(_Lg,__Z));});return function(_Lj){return C > 19 ? new F(function(){return A1(_Lj,_Li);}) : (++C,A1(_Lj,_Li));};}else{var _Lk=E(_Lh.a),_Ll=function(_Lm){var _Ln=new T(function(){return _Le(_Lh.b,function(_Lo){return C > 19 ? new F(function(){return A1(_Lg,new T2(1,_Lm,_Lo));}) : (++C,A1(_Lg,new T2(1,_Lm,_Lo)));});}),_Lp=function(_Lq){var _Lr=new T(function(){return B(A1(_Ln,_Lq));});return new T1(0,function(_Ls){return E(_Lr);});};return _Lp;};switch(E(_Lc)){case 8:if(48>_Lk){var _Lt=new T(function(){return B(A1(_Lg,__Z));});return function(_Lu){return C > 19 ? new F(function(){return A1(_Lu,_Lt);}) : (++C,A1(_Lu,_Lt));};}else{if(_Lk>55){var _Lv=new T(function(){return B(A1(_Lg,__Z));});return function(_Lw){return C > 19 ? new F(function(){return A1(_Lw,_Lv);}) : (++C,A1(_Lw,_Lv));};}else{return _Ll(_Lk-48|0);}}break;case 10:if(48>_Lk){var _Lx=new T(function(){return B(A1(_Lg,__Z));});return function(_Ly){return C > 19 ? new F(function(){return A1(_Ly,_Lx);}) : (++C,A1(_Ly,_Lx));};}else{if(_Lk>57){var _Lz=new T(function(){return B(A1(_Lg,__Z));});return function(_LA){return C > 19 ? new F(function(){return A1(_LA,_Lz);}) : (++C,A1(_LA,_Lz));};}else{return _Ll(_Lk-48|0);}}break;case 16:if(48>_Lk){if(97>_Lk){if(65>_Lk){var _LB=new T(function(){return B(A1(_Lg,__Z));});return function(_LC){return C > 19 ? new F(function(){return A1(_LC,_LB);}) : (++C,A1(_LC,_LB));};}else{if(_Lk>70){var _LD=new T(function(){return B(A1(_Lg,__Z));});return function(_LE){return C > 19 ? new F(function(){return A1(_LE,_LD);}) : (++C,A1(_LE,_LD));};}else{return _Ll((_Lk-65|0)+10|0);}}}else{if(_Lk>102){if(65>_Lk){var _LF=new T(function(){return B(A1(_Lg,__Z));});return function(_LG){return C > 19 ? new F(function(){return A1(_LG,_LF);}) : (++C,A1(_LG,_LF));};}else{if(_Lk>70){var _LH=new T(function(){return B(A1(_Lg,__Z));});return function(_LI){return C > 19 ? new F(function(){return A1(_LI,_LH);}) : (++C,A1(_LI,_LH));};}else{return _Ll((_Lk-65|0)+10|0);}}}else{return _Ll((_Lk-97|0)+10|0);}}}else{if(_Lk>57){if(97>_Lk){if(65>_Lk){var _LJ=new T(function(){return B(A1(_Lg,__Z));});return function(_LK){return C > 19 ? new F(function(){return A1(_LK,_LJ);}) : (++C,A1(_LK,_LJ));};}else{if(_Lk>70){var _LL=new T(function(){return B(A1(_Lg,__Z));});return function(_LM){return C > 19 ? new F(function(){return A1(_LM,_LL);}) : (++C,A1(_LM,_LL));};}else{return _Ll((_Lk-65|0)+10|0);}}}else{if(_Lk>102){if(65>_Lk){var _LN=new T(function(){return B(A1(_Lg,__Z));});return function(_LO){return C > 19 ? new F(function(){return A1(_LO,_LN);}) : (++C,A1(_LO,_LN));};}else{if(_Lk>70){var _LP=new T(function(){return B(A1(_Lg,__Z));});return function(_LQ){return C > 19 ? new F(function(){return A1(_LQ,_LP);}) : (++C,A1(_LQ,_LP));};}else{return _Ll((_Lk-65|0)+10|0);}}}else{return _Ll((_Lk-97|0)+10|0);}}}else{return _Ll(_Lk-48|0);}}break;default:return E(_La);}}},_LR=function(_LS){var _LT=E(_LS);if(!_LT._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_Ld,_LT);}) : (++C,A1(_Ld,_LT));}};return function(_LU){return C > 19 ? new F(function(){return A3(_Le,_LU,_1W,_LR);}) : (++C,A3(_Le,_LU,_1W,_LR));};},_LV=function(_LW){var _LX=function(_LY){return C > 19 ? new F(function(){return A1(_LW,new T1(5,new T2(0,8,_LY)));}) : (++C,A1(_LW,new T1(5,new T2(0,8,_LY))));},_LZ=function(_M0){return C > 19 ? new F(function(){return A1(_LW,new T1(5,new T2(0,16,_M0)));}) : (++C,A1(_LW,new T1(5,new T2(0,16,_M0))));},_M1=function(_M2){switch(E(_M2)){case 79:return new T1(1,_Lb(8,_LX));case 88:return new T1(1,_Lb(16,_LZ));case 111:return new T1(1,_Lb(8,_LX));case 120:return new T1(1,_Lb(16,_LZ));default:return new T0(2);}};return function(_M3){return (E(_M3)==48)?E(new T1(0,_M1)):new T0(2);};},_M4=function(_M5){return new T1(0,_LV(_M5));},_M6=function(_M7){return C > 19 ? new F(function(){return A1(_M7,__Z);}) : (++C,A1(_M7,__Z));},_M8=function(_M9){return C > 19 ? new F(function(){return A1(_M9,__Z);}) : (++C,A1(_M9,__Z));},_Ma=function(_Mb,_Mc){while(1){var _Md=E(_Mb);if(!_Md._){var _Me=_Md.a,_Mf=E(_Mc);if(!_Mf._){var _Mg=_Mf.a,_Mh=addC(_Me,_Mg);if(!E(_Mh.b)){return new T1(0,_Mh.a);}else{_Mb=new T1(1,I_fromInt(_Me));_Mc=new T1(1,I_fromInt(_Mg));continue;}}else{_Mb=new T1(1,I_fromInt(_Me));_Mc=_Mf;continue;}}else{var _Mi=E(_Mc);if(!_Mi._){_Mb=_Md;_Mc=new T1(1,I_fromInt(_Mi.a));continue;}else{return new T1(1,I_add(_Md.a,_Mi.a));}}}},_Mj=new T(function(){return _Ma(new T1(0,2147483647),new T1(0,1));}),_Mk=function(_Ml){var _Mm=E(_Ml);if(!_Mm._){var _Mn=E(_Mm.a);return (_Mn==( -2147483648))?E(_Mj):new T1(0, -_Mn);}else{return new T1(1,I_negate(_Mm.a));}},_Mo=new T1(0,10),_Mp=function(_Mq){return new T1(0,_Mq);},_Mr=function(_Ms){return _Mp(E(_Ms));},_Mt=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_Mu=function(_Mv,_Mw){while(1){var _Mx=E(_Mv);if(!_Mx._){var _My=_Mx.a,_Mz=E(_Mw);if(!_Mz._){var _MA=_Mz.a;if(!(imul(_My,_MA)|0)){return new T1(0,imul(_My,_MA)|0);}else{_Mv=new T1(1,I_fromInt(_My));_Mw=new T1(1,I_fromInt(_MA));continue;}}else{_Mv=new T1(1,I_fromInt(_My));_Mw=_Mz;continue;}}else{var _MB=E(_Mw);if(!_MB._){_Mv=_Mx;_Mw=new T1(1,I_fromInt(_MB.a));continue;}else{return new T1(1,I_mul(_Mx.a,_MB.a));}}}},_MC=function(_MD,_ME){var _MF=E(_ME);if(!_MF._){return __Z;}else{var _MG=E(_MF.b);return (_MG._==0)?E(_Mt):new T2(1,_Ma(_Mu(_MF.a,_MD),_MG.a),new T(function(){return _MC(_MD,_MG.b);}));}},_MH=new T1(0,0),_MI=function(_MJ,_MK,_ML){while(1){var _MM=(function(_MN,_MO,_MP){var _MQ=E(_MP);if(!_MQ._){return E(_MH);}else{if(!E(_MQ.b)._){return E(_MQ.a);}else{var _MR=E(_MO);if(_MR<=40){var _MS=function(_MT,_MU){while(1){var _MV=E(_MU);if(!_MV._){return E(_MT);}else{var _MW=_Ma(_Mu(_MT,_MN),_MV.a);_MT=_MW;_MU=_MV.b;continue;}}};return _MS(_MH,_MQ);}else{var _MX=_Mu(_MN,_MN);if(!(_MR%2)){var _MY=_MC(_MN,_MQ);_MJ=_MX;_MK=quot(_MR+1|0,2);_ML=_MY;return __continue;}else{var _MY=_MC(_MN,new T2(1,_MH,_MQ));_MJ=_MX;_MK=quot(_MR+1|0,2);_ML=_MY;return __continue;}}}}})(_MJ,_MK,_ML);if(_MM!=__continue){return _MM;}}},_MZ=function(_N0,_N1){return _MI(_N0,new T(function(){return _7J(_N1,0);},1),_55(_Mr,_N1));},_N2=function(_N3){var _N4=new T(function(){var _N5=new T(function(){var _N6=function(_N7){return C > 19 ? new F(function(){return A1(_N3,new T1(1,new T(function(){return _MZ(_Mo,_N7);})));}) : (++C,A1(_N3,new T1(1,new T(function(){return _MZ(_Mo,_N7);}))));};return new T1(1,_Lb(10,_N6));}),_N8=function(_N9){if(E(_N9)==43){var _Na=function(_Nb){return C > 19 ? new F(function(){return A1(_N3,new T1(1,new T(function(){return _MZ(_Mo,_Nb);})));}) : (++C,A1(_N3,new T1(1,new T(function(){return _MZ(_Mo,_Nb);}))));};return new T1(1,_Lb(10,_Na));}else{return new T0(2);}},_Nc=function(_Nd){if(E(_Nd)==45){var _Ne=function(_Nf){return C > 19 ? new F(function(){return A1(_N3,new T1(1,new T(function(){return _Mk(_MZ(_Mo,_Nf));})));}) : (++C,A1(_N3,new T1(1,new T(function(){return _Mk(_MZ(_Mo,_Nf));}))));};return new T1(1,_Lb(10,_Ne));}else{return new T0(2);}};return _Js(_Js(new T1(0,_Nc),new T1(0,_N8)),_N5);});return _Js(new T1(0,function(_Ng){return (E(_Ng)==101)?E(_N4):new T0(2);}),new T1(0,function(_Nh){return (E(_Nh)==69)?E(_N4):new T0(2);}));},_Ni=function(_Nj){var _Nk=function(_Nl){return C > 19 ? new F(function(){return A1(_Nj,new T1(1,_Nl));}) : (++C,A1(_Nj,new T1(1,_Nl)));};return function(_Nm){return (E(_Nm)==46)?new T1(1,_Lb(10,_Nk)):new T0(2);};},_Nn=function(_No){return new T1(0,_Ni(_No));},_Np=function(_Nq){var _Nr=function(_Ns){var _Nt=function(_Nu){return new T1(1,_Kw(_N2,_M6,function(_Nv){return C > 19 ? new F(function(){return A1(_Nq,new T1(5,new T3(1,_Ns,_Nu,_Nv)));}) : (++C,A1(_Nq,new T1(5,new T3(1,_Ns,_Nu,_Nv))));}));};return new T1(1,_Kw(_Nn,_M8,_Nt));};return _Lb(10,_Nr);},_Nw=function(_Nx){return new T1(1,_Np(_Nx));},_Ny=function(_Nz,_NA,_NB){while(1){var _NC=E(_NB);if(!_NC._){return false;}else{if(!B(A3(_Ig,_Nz,_NA,_NC.a))){_NB=_NC.b;continue;}else{return true;}}}},_ND=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_NE=function(_NF){return _Ny(_K1,_NF,_ND);},_NG=function(_NH){var _NI=new T(function(){return B(A1(_NH,8));}),_NJ=new T(function(){return B(A1(_NH,16));});return function(_NK){switch(E(_NK)){case 79:return E(_NI);case 88:return E(_NJ);case 111:return E(_NI);case 120:return E(_NJ);default:return new T0(2);}};},_NL=function(_NM){return new T1(0,_NG(_NM));},_NN=function(_NO){return C > 19 ? new F(function(){return A1(_NO,10);}) : (++C,A1(_NO,10));},_NP=function(_NQ){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _2e(9,_NQ,__Z);})));},_NR=function(_NS){var _NT=E(_NS);if(!_NT._){return E(_NT.a);}else{return I_toInt(_NT.a);}},_NU=function(_NV,_NW){var _NX=E(_NV);if(!_NX._){var _NY=_NX.a,_NZ=E(_NW);return (_NZ._==0)?_NY<=_NZ.a:I_compareInt(_NZ.a,_NY)>=0;}else{var _O0=_NX.a,_O1=E(_NW);return (_O1._==0)?I_compareInt(_O0,_O1.a)<=0:I_compare(_O0,_O1.a)<=0;}},_O2=function(_O3){return new T0(2);},_O4=function(_O5){var _O6=E(_O5);if(!_O6._){return _O2;}else{var _O7=_O6.a,_O8=E(_O6.b);if(!_O8._){return E(_O7);}else{var _O9=new T(function(){return _O4(_O8);}),_Oa=function(_Ob){return _Js(B(A1(_O7,_Ob)),new T(function(){return B(A1(_O9,_Ob));}));};return _Oa;}}},_Oc=function(_Od,_Oe){var _Of=function(_Og,_Oh,_Oi){var _Oj=E(_Og);if(!_Oj._){return C > 19 ? new F(function(){return A1(_Oi,_Od);}) : (++C,A1(_Oi,_Od));}else{var _Ok=E(_Oh);if(!_Ok._){return new T0(2);}else{if(E(_Oj.a)!=E(_Ok.a)){return new T0(2);}else{var _Ol=new T(function(){return B(_Of(_Oj.b,_Ok.b,_Oi));});return new T1(0,function(_Om){return E(_Ol);});}}}};return function(_On){return C > 19 ? new F(function(){return _Of(_Od,_On,_Oe);}) : (++C,_Of(_Od,_On,_Oe));};},_Oo=new T(function(){return unCStr("SO");}),_Op=function(_Oq){var _Or=new T(function(){return B(A1(_Oq,14));});return new T1(1,_Oc(_Oo,function(_Os){return E(_Or);}));},_Ot=new T(function(){return unCStr("SOH");}),_Ou=function(_Ov){var _Ow=new T(function(){return B(A1(_Ov,1));});return new T1(1,_Oc(_Ot,function(_Ox){return E(_Ow);}));},_Oy=new T(function(){return unCStr("NUL");}),_Oz=function(_OA){var _OB=new T(function(){return B(A1(_OA,0));});return new T1(1,_Oc(_Oy,function(_OC){return E(_OB);}));},_OD=new T(function(){return unCStr("STX");}),_OE=function(_OF){var _OG=new T(function(){return B(A1(_OF,2));});return new T1(1,_Oc(_OD,function(_OH){return E(_OG);}));},_OI=new T(function(){return unCStr("ETX");}),_OJ=function(_OK){var _OL=new T(function(){return B(A1(_OK,3));});return new T1(1,_Oc(_OI,function(_OM){return E(_OL);}));},_ON=new T(function(){return unCStr("EOT");}),_OO=function(_OP){var _OQ=new T(function(){return B(A1(_OP,4));});return new T1(1,_Oc(_ON,function(_OR){return E(_OQ);}));},_OS=new T(function(){return unCStr("ENQ");}),_OT=function(_OU){var _OV=new T(function(){return B(A1(_OU,5));});return new T1(1,_Oc(_OS,function(_OW){return E(_OV);}));},_OX=new T(function(){return unCStr("ACK");}),_OY=function(_OZ){var _P0=new T(function(){return B(A1(_OZ,6));});return new T1(1,_Oc(_OX,function(_P1){return E(_P0);}));},_P2=new T(function(){return unCStr("BEL");}),_P3=function(_P4){var _P5=new T(function(){return B(A1(_P4,7));});return new T1(1,_Oc(_P2,function(_P6){return E(_P5);}));},_P7=new T(function(){return unCStr("BS");}),_P8=function(_P9){var _Pa=new T(function(){return B(A1(_P9,8));});return new T1(1,_Oc(_P7,function(_Pb){return E(_Pa);}));},_Pc=new T(function(){return unCStr("HT");}),_Pd=function(_Pe){var _Pf=new T(function(){return B(A1(_Pe,9));});return new T1(1,_Oc(_Pc,function(_Pg){return E(_Pf);}));},_Ph=new T(function(){return unCStr("LF");}),_Pi=function(_Pj){var _Pk=new T(function(){return B(A1(_Pj,10));});return new T1(1,_Oc(_Ph,function(_Pl){return E(_Pk);}));},_Pm=new T(function(){return unCStr("VT");}),_Pn=function(_Po){var _Pp=new T(function(){return B(A1(_Po,11));});return new T1(1,_Oc(_Pm,function(_Pq){return E(_Pp);}));},_Pr=new T(function(){return unCStr("FF");}),_Ps=function(_Pt){var _Pu=new T(function(){return B(A1(_Pt,12));});return new T1(1,_Oc(_Pr,function(_Pv){return E(_Pu);}));},_Pw=new T(function(){return unCStr("CR");}),_Px=function(_Py){var _Pz=new T(function(){return B(A1(_Py,13));});return new T1(1,_Oc(_Pw,function(_PA){return E(_Pz);}));},_PB=new T(function(){return unCStr("SI");}),_PC=function(_PD){var _PE=new T(function(){return B(A1(_PD,15));});return new T1(1,_Oc(_PB,function(_PF){return E(_PE);}));},_PG=new T(function(){return unCStr("DLE");}),_PH=function(_PI){var _PJ=new T(function(){return B(A1(_PI,16));});return new T1(1,_Oc(_PG,function(_PK){return E(_PJ);}));},_PL=new T(function(){return unCStr("DC1");}),_PM=function(_PN){var _PO=new T(function(){return B(A1(_PN,17));});return new T1(1,_Oc(_PL,function(_PP){return E(_PO);}));},_PQ=new T(function(){return unCStr("DC2");}),_PR=function(_PS){var _PT=new T(function(){return B(A1(_PS,18));});return new T1(1,_Oc(_PQ,function(_PU){return E(_PT);}));},_PV=new T(function(){return unCStr("DC3");}),_PW=function(_PX){var _PY=new T(function(){return B(A1(_PX,19));});return new T1(1,_Oc(_PV,function(_PZ){return E(_PY);}));},_Q0=new T(function(){return unCStr("DC4");}),_Q1=function(_Q2){var _Q3=new T(function(){return B(A1(_Q2,20));});return new T1(1,_Oc(_Q0,function(_Q4){return E(_Q3);}));},_Q5=new T(function(){return unCStr("NAK");}),_Q6=function(_Q7){var _Q8=new T(function(){return B(A1(_Q7,21));});return new T1(1,_Oc(_Q5,function(_Q9){return E(_Q8);}));},_Qa=new T(function(){return unCStr("SYN");}),_Qb=function(_Qc){var _Qd=new T(function(){return B(A1(_Qc,22));});return new T1(1,_Oc(_Qa,function(_Qe){return E(_Qd);}));},_Qf=new T(function(){return unCStr("ETB");}),_Qg=function(_Qh){var _Qi=new T(function(){return B(A1(_Qh,23));});return new T1(1,_Oc(_Qf,function(_Qj){return E(_Qi);}));},_Qk=new T(function(){return unCStr("CAN");}),_Ql=function(_Qm){var _Qn=new T(function(){return B(A1(_Qm,24));});return new T1(1,_Oc(_Qk,function(_Qo){return E(_Qn);}));},_Qp=new T(function(){return unCStr("EM");}),_Qq=function(_Qr){var _Qs=new T(function(){return B(A1(_Qr,25));});return new T1(1,_Oc(_Qp,function(_Qt){return E(_Qs);}));},_Qu=new T(function(){return unCStr("SUB");}),_Qv=function(_Qw){var _Qx=new T(function(){return B(A1(_Qw,26));});return new T1(1,_Oc(_Qu,function(_Qy){return E(_Qx);}));},_Qz=new T(function(){return unCStr("ESC");}),_QA=function(_QB){var _QC=new T(function(){return B(A1(_QB,27));});return new T1(1,_Oc(_Qz,function(_QD){return E(_QC);}));},_QE=new T(function(){return unCStr("FS");}),_QF=function(_QG){var _QH=new T(function(){return B(A1(_QG,28));});return new T1(1,_Oc(_QE,function(_QI){return E(_QH);}));},_QJ=new T(function(){return unCStr("GS");}),_QK=function(_QL){var _QM=new T(function(){return B(A1(_QL,29));});return new T1(1,_Oc(_QJ,function(_QN){return E(_QM);}));},_QO=new T(function(){return unCStr("RS");}),_QP=function(_QQ){var _QR=new T(function(){return B(A1(_QQ,30));});return new T1(1,_Oc(_QO,function(_QS){return E(_QR);}));},_QT=new T(function(){return unCStr("US");}),_QU=function(_QV){var _QW=new T(function(){return B(A1(_QV,31));});return new T1(1,_Oc(_QT,function(_QX){return E(_QW);}));},_QY=new T(function(){return unCStr("SP");}),_QZ=function(_R0){var _R1=new T(function(){return B(A1(_R0,32));});return new T1(1,_Oc(_QY,function(_R2){return E(_R1);}));},_R3=new T(function(){return unCStr("DEL");}),_R4=function(_R5){var _R6=new T(function(){return B(A1(_R5,127));});return new T1(1,_Oc(_R3,function(_R7){return E(_R6);}));},_R8=new T(function(){return _O4(new T2(1,function(_R9){return new T1(1,_Kw(_Ou,_Op,_R9));},new T2(1,_Oz,new T2(1,_OE,new T2(1,_OJ,new T2(1,_OO,new T2(1,_OT,new T2(1,_OY,new T2(1,_P3,new T2(1,_P8,new T2(1,_Pd,new T2(1,_Pi,new T2(1,_Pn,new T2(1,_Ps,new T2(1,_Px,new T2(1,_PC,new T2(1,_PH,new T2(1,_PM,new T2(1,_PR,new T2(1,_PW,new T2(1,_Q1,new T2(1,_Q6,new T2(1,_Qb,new T2(1,_Qg,new T2(1,_Ql,new T2(1,_Qq,new T2(1,_Qv,new T2(1,_QA,new T2(1,_QF,new T2(1,_QK,new T2(1,_QP,new T2(1,_QU,new T2(1,_QZ,new T2(1,_R4,__Z))))))))))))))))))))))))))))))))));}),_Ra=function(_Rb){var _Rc=new T(function(){return B(A1(_Rb,7));}),_Rd=new T(function(){return B(A1(_Rb,8));}),_Re=new T(function(){return B(A1(_Rb,9));}),_Rf=new T(function(){return B(A1(_Rb,10));}),_Rg=new T(function(){return B(A1(_Rb,11));}),_Rh=new T(function(){return B(A1(_Rb,12));}),_Ri=new T(function(){return B(A1(_Rb,13));}),_Rj=new T(function(){return B(A1(_Rb,92));}),_Rk=new T(function(){return B(A1(_Rb,39));}),_Rl=new T(function(){return B(A1(_Rb,34));}),_Rm=new T(function(){var _Rn=function(_Ro){var _Rp=new T(function(){return _Mp(E(_Ro));}),_Rq=function(_Rr){var _Rs=_MZ(_Rp,_Rr);if(!_NU(_Rs,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_Rb,new T(function(){var _Rt=_NR(_Rs);if(_Rt>>>0>1114111){return _NP(_Rt);}else{return _Rt;}}));}) : (++C,A1(_Rb,new T(function(){var _Rt=_NR(_Rs);if(_Rt>>>0>1114111){return _NP(_Rt);}else{return _Rt;}})));}};return new T1(1,_Lb(_Ro,_Rq));},_Ru=new T(function(){var _Rv=new T(function(){return B(A1(_Rb,31));}),_Rw=new T(function(){return B(A1(_Rb,30));}),_Rx=new T(function(){return B(A1(_Rb,29));}),_Ry=new T(function(){return B(A1(_Rb,28));}),_Rz=new T(function(){return B(A1(_Rb,27));}),_RA=new T(function(){return B(A1(_Rb,26));}),_RB=new T(function(){return B(A1(_Rb,25));}),_RC=new T(function(){return B(A1(_Rb,24));}),_RD=new T(function(){return B(A1(_Rb,23));}),_RE=new T(function(){return B(A1(_Rb,22));}),_RF=new T(function(){return B(A1(_Rb,21));}),_RG=new T(function(){return B(A1(_Rb,20));}),_RH=new T(function(){return B(A1(_Rb,19));}),_RI=new T(function(){return B(A1(_Rb,18));}),_RJ=new T(function(){return B(A1(_Rb,17));}),_RK=new T(function(){return B(A1(_Rb,16));}),_RL=new T(function(){return B(A1(_Rb,15));}),_RM=new T(function(){return B(A1(_Rb,14));}),_RN=new T(function(){return B(A1(_Rb,6));}),_RO=new T(function(){return B(A1(_Rb,5));}),_RP=new T(function(){return B(A1(_Rb,4));}),_RQ=new T(function(){return B(A1(_Rb,3));}),_RR=new T(function(){return B(A1(_Rb,2));}),_RS=new T(function(){return B(A1(_Rb,1));}),_RT=new T(function(){return B(A1(_Rb,0));}),_RU=function(_RV){switch(E(_RV)){case 64:return E(_RT);case 65:return E(_RS);case 66:return E(_RR);case 67:return E(_RQ);case 68:return E(_RP);case 69:return E(_RO);case 70:return E(_RN);case 71:return E(_Rc);case 72:return E(_Rd);case 73:return E(_Re);case 74:return E(_Rf);case 75:return E(_Rg);case 76:return E(_Rh);case 77:return E(_Ri);case 78:return E(_RM);case 79:return E(_RL);case 80:return E(_RK);case 81:return E(_RJ);case 82:return E(_RI);case 83:return E(_RH);case 84:return E(_RG);case 85:return E(_RF);case 86:return E(_RE);case 87:return E(_RD);case 88:return E(_RC);case 89:return E(_RB);case 90:return E(_RA);case 91:return E(_Rz);case 92:return E(_Ry);case 93:return E(_Rx);case 94:return E(_Rw);case 95:return E(_Rv);default:return new T0(2);}};return _Js(new T1(0,function(_RW){return (E(_RW)==94)?E(new T1(0,_RU)):new T0(2);}),new T(function(){return B(A1(_R8,_Rb));}));});return _Js(new T1(1,_Kw(_NL,_NN,_Rn)),_Ru);});return _Js(new T1(0,function(_RX){switch(E(_RX)){case 34:return E(_Rl);case 39:return E(_Rk);case 92:return E(_Rj);case 97:return E(_Rc);case 98:return E(_Rd);case 102:return E(_Rh);case 110:return E(_Rf);case 114:return E(_Ri);case 116:return E(_Re);case 118:return E(_Rg);default:return new T0(2);}}),_Rm);},_RY=function(_RZ){return C > 19 ? new F(function(){return A1(_RZ,0);}) : (++C,A1(_RZ,0));},_S0=function(_S1){var _S2=E(_S1);if(!_S2._){return _RY;}else{var _S3=E(_S2.a),_S4=_S3>>>0,_S5=new T(function(){return _S0(_S2.b);});if(_S4>887){var _S6=u_iswspace(_S3);if(!E(_S6)){return _RY;}else{var _S7=function(_S8){var _S9=new T(function(){return B(A1(_S5,_S8));});return new T1(0,function(_Sa){return E(_S9);});};return _S7;}}else{if(_S4==32){var _Sb=function(_Sc){var _Sd=new T(function(){return B(A1(_S5,_Sc));});return new T1(0,function(_Se){return E(_Sd);});};return _Sb;}else{if(_S4-9>>>0>4){if(_S4==160){var _Sf=function(_Sg){var _Sh=new T(function(){return B(A1(_S5,_Sg));});return new T1(0,function(_Si){return E(_Sh);});};return _Sf;}else{return _RY;}}else{var _Sj=function(_Sk){var _Sl=new T(function(){return B(A1(_S5,_Sk));});return new T1(0,function(_Sm){return E(_Sl);});};return _Sj;}}}}},_Sn=function(_So){var _Sp=new T(function(){return B(_Sn(_So));}),_Sq=function(_Sr){return (E(_Sr)==92)?E(_Sp):new T0(2);},_Ss=function(_St){return E(new T1(0,_Sq));},_Su=new T1(1,function(_Sv){return C > 19 ? new F(function(){return A2(_S0,_Sv,_Ss);}) : (++C,A2(_S0,_Sv,_Ss));}),_Sw=new T(function(){return B(_Ra(function(_Sx){return C > 19 ? new F(function(){return A1(_So,new T2(0,_Sx,true));}) : (++C,A1(_So,new T2(0,_Sx,true)));}));}),_Sy=function(_Sz){var _SA=E(_Sz);if(_SA==38){return E(_Sp);}else{var _SB=_SA>>>0;if(_SB>887){var _SC=u_iswspace(_SA);return (E(_SC)==0)?new T0(2):E(_Su);}else{return (_SB==32)?E(_Su):(_SB-9>>>0>4)?(_SB==160)?E(_Su):new T0(2):E(_Su);}}};return _Js(new T1(0,function(_SD){return (E(_SD)==92)?E(new T1(0,_Sy)):new T0(2);}),new T1(0,function(_SE){var _SF=E(_SE);if(_SF==92){return E(_Sw);}else{return C > 19 ? new F(function(){return A1(_So,new T2(0,_SF,false));}) : (++C,A1(_So,new T2(0,_SF,false)));}}));},_SG=function(_SH,_SI){var _SJ=new T(function(){return B(A1(_SI,new T1(1,new T(function(){return B(A1(_SH,__Z));}))));}),_SK=function(_SL){var _SM=E(_SL),_SN=E(_SM.a);if(_SN==34){if(!E(_SM.b)){return E(_SJ);}else{return C > 19 ? new F(function(){return _SG(function(_SO){return C > 19 ? new F(function(){return A1(_SH,new T2(1,_SN,_SO));}) : (++C,A1(_SH,new T2(1,_SN,_SO)));},_SI);}) : (++C,_SG(function(_SO){return C > 19 ? new F(function(){return A1(_SH,new T2(1,_SN,_SO));}) : (++C,A1(_SH,new T2(1,_SN,_SO)));},_SI));}}else{return C > 19 ? new F(function(){return _SG(function(_SP){return C > 19 ? new F(function(){return A1(_SH,new T2(1,_SN,_SP));}) : (++C,A1(_SH,new T2(1,_SN,_SP)));},_SI);}) : (++C,_SG(function(_SP){return C > 19 ? new F(function(){return A1(_SH,new T2(1,_SN,_SP));}) : (++C,A1(_SH,new T2(1,_SN,_SP)));},_SI));}};return C > 19 ? new F(function(){return _Sn(_SK);}) : (++C,_Sn(_SK));},_SQ=new T(function(){return unCStr("_\'");}),_SR=function(_SS){var _ST=u_iswalnum(_SS);if(!E(_ST)){return _Ny(_K1,_SS,_SQ);}else{return true;}},_SU=function(_SV){return _SR(E(_SV));},_SW=new T(function(){return unCStr(",;()[]{}`");}),_SX=new T(function(){return unCStr("=>");}),_SY=new T(function(){return unCStr("~");}),_SZ=new T(function(){return unCStr("@");}),_T0=new T(function(){return unCStr("->");}),_T1=new T(function(){return unCStr("<-");}),_T2=new T(function(){return unCStr("|");}),_T3=new T(function(){return unCStr("\\");}),_T4=new T(function(){return unCStr("=");}),_T5=new T(function(){return unCStr("::");}),_T6=new T(function(){return unCStr("..");}),_T7=function(_T8){var _T9=new T(function(){return B(A1(_T8,new T0(6)));}),_Ta=new T(function(){var _Tb=new T(function(){var _Tc=function(_Td){var _Te=new T(function(){return B(A1(_T8,new T1(0,_Td)));});return new T1(0,function(_Tf){return (E(_Tf)==39)?E(_Te):new T0(2);});};return B(_Ra(_Tc));}),_Tg=function(_Th){var _Ti=E(_Th);switch(_Ti){case 39:return new T0(2);case 92:return E(_Tb);default:var _Tj=new T(function(){return B(A1(_T8,new T1(0,_Ti)));});return new T1(0,function(_Tk){return (E(_Tk)==39)?E(_Tj):new T0(2);});}},_Tl=new T(function(){var _Tm=new T(function(){return B(_SG(_1W,_T8));}),_Tn=new T(function(){var _To=new T(function(){var _Tp=new T(function(){var _Tq=function(_Tr){var _Ts=E(_Tr),_Tt=u_iswalpha(_Ts);return (E(_Tt)==0)?(_Ts==95)?new T1(1,_KW(_SU,function(_Tu){return C > 19 ? new F(function(){return A1(_T8,new T1(3,new T2(1,_Ts,_Tu)));}) : (++C,A1(_T8,new T1(3,new T2(1,_Ts,_Tu))));})):new T0(2):new T1(1,_KW(_SU,function(_Tv){return C > 19 ? new F(function(){return A1(_T8,new T1(3,new T2(1,_Ts,_Tv)));}) : (++C,A1(_T8,new T1(3,new T2(1,_Ts,_Tv))));}));};return _Js(new T1(0,_Tq),new T(function(){return new T1(1,_Kw(_M4,_Nw,_T8));}));}),_Tw=function(_Tx){return (!_Ny(_K1,_Tx,_ND))?new T0(2):new T1(1,_KW(_NE,function(_Ty){var _Tz=new T2(1,_Tx,_Ty);if(!_Ny(new T2(0,_K4,_K9),_Tz,new T2(1,_T6,new T2(1,_T5,new T2(1,_T4,new T2(1,_T3,new T2(1,_T2,new T2(1,_T1,new T2(1,_T0,new T2(1,_SZ,new T2(1,_SY,new T2(1,_SX,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_T8,new T1(4,_Tz));}) : (++C,A1(_T8,new T1(4,_Tz)));}else{return C > 19 ? new F(function(){return A1(_T8,new T1(2,_Tz));}) : (++C,A1(_T8,new T1(2,_Tz)));}}));};return _Js(new T1(0,_Tw),_Tp);});return _Js(new T1(0,function(_TA){if(!_Ny(_K1,_TA,_SW)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_T8,new T1(2,new T2(1,_TA,__Z)));}) : (++C,A1(_T8,new T1(2,new T2(1,_TA,__Z))));}}),_To);});return _Js(new T1(0,function(_TB){return (E(_TB)==34)?E(_Tm):new T0(2);}),_Tn);});return _Js(new T1(0,function(_TC){return (E(_TC)==39)?E(new T1(0,_Tg)):new T0(2);}),_Tl);});return _Js(new T1(1,function(_TD){return (E(_TD)._==0)?E(_T9):new T0(2);}),_Ta);},_TE=function(_TF,_TG){var _TH=new T(function(){var _TI=new T(function(){var _TJ=function(_TK){var _TL=new T(function(){var _TM=new T(function(){return B(A1(_TG,_TK));});return B(_T7(function(_TN){var _TO=E(_TN);return (_TO._==2)?(!_3R(_TO.a,_JX))?new T0(2):E(_TM):new T0(2);}));}),_TP=function(_TQ){return E(_TL);};return new T1(1,function(_TR){return C > 19 ? new F(function(){return A2(_S0,_TR,_TP);}) : (++C,A2(_S0,_TR,_TP));});};return B(A2(_TF,0,_TJ));});return B(_T7(function(_TS){var _TT=E(_TS);return (_TT._==2)?(!_3R(_TT.a,_JW))?new T0(2):E(_TI):new T0(2);}));}),_TU=function(_TV){return E(_TH);};return function(_TW){return C > 19 ? new F(function(){return A2(_S0,_TW,_TU);}) : (++C,A2(_S0,_TW,_TU));};},_TX=function(_TY,_TZ){var _U0=function(_U1){var _U2=new T(function(){return B(A1(_TY,_U1));}),_U3=function(_U4){return _Js(B(A1(_U2,_U4)),new T(function(){return new T1(1,_TE(_U0,_U4));}));};return _U3;},_U5=new T(function(){return B(A1(_TY,_TZ));}),_U6=function(_U7){return _Js(B(A1(_U5,_U7)),new T(function(){return new T1(1,_TE(_U0,_U7));}));};return _U6;},_U8=function(_U9,_Ua){var _Ub=function(_Uc,_Ud){var _Ue=function(_Uf){return C > 19 ? new F(function(){return A1(_Ud,new T(function(){return  -E(_Uf);}));}) : (++C,A1(_Ud,new T(function(){return  -E(_Uf);})));},_Ug=new T(function(){return B(_T7(function(_Uh){return C > 19 ? new F(function(){return A3(_U9,_Uh,_Uc,_Ue);}) : (++C,A3(_U9,_Uh,_Uc,_Ue));}));}),_Ui=function(_Uj){return E(_Ug);},_Uk=function(_Ul){return C > 19 ? new F(function(){return A2(_S0,_Ul,_Ui);}) : (++C,A2(_S0,_Ul,_Ui));},_Um=new T(function(){return B(_T7(function(_Un){var _Uo=E(_Un);if(_Uo._==4){var _Up=E(_Uo.a);if(!_Up._){return C > 19 ? new F(function(){return A3(_U9,_Uo,_Uc,_Ud);}) : (++C,A3(_U9,_Uo,_Uc,_Ud));}else{if(E(_Up.a)==45){if(!E(_Up.b)._){return E(new T1(1,_Uk));}else{return C > 19 ? new F(function(){return A3(_U9,_Uo,_Uc,_Ud);}) : (++C,A3(_U9,_Uo,_Uc,_Ud));}}else{return C > 19 ? new F(function(){return A3(_U9,_Uo,_Uc,_Ud);}) : (++C,A3(_U9,_Uo,_Uc,_Ud));}}}else{return C > 19 ? new F(function(){return A3(_U9,_Uo,_Uc,_Ud);}) : (++C,A3(_U9,_Uo,_Uc,_Ud));}}));}),_Uq=function(_Ur){return E(_Um);};return new T1(1,function(_Us){return C > 19 ? new F(function(){return A2(_S0,_Us,_Uq);}) : (++C,A2(_S0,_Us,_Uq));});};return _TX(_Ub,_Ua);},_Ut=function(_Uu){var _Uv=E(_Uu);if(!_Uv._){var _Uw=_Uv.b,_Ux=new T(function(){return _MI(new T(function(){return _Mp(E(_Uv.a));}),new T(function(){return _7J(_Uw,0);},1),_55(_Mr,_Uw));});return new T1(1,_Ux);}else{return (E(_Uv.b)._==0)?(E(_Uv.c)._==0)?new T1(1,new T(function(){return _MZ(_Mo,_Uv.a);})):__Z:__Z;}},_Uy=function(_Uz,_UA){return new T0(2);},_UB=function(_UC){var _UD=E(_UC);if(_UD._==5){var _UE=_Ut(_UD.a);if(!_UE._){return _Uy;}else{var _UF=new T(function(){return _NR(_UE.a);});return function(_UG,_UH){return C > 19 ? new F(function(){return A1(_UH,_UF);}) : (++C,A1(_UH,_UF));};}}else{return _Uy;}},_UI=function(_UJ){var _UK=function(_UL){return E(new T2(3,_UJ,_Kn));};return new T1(1,function(_UM){return C > 19 ? new F(function(){return A2(_S0,_UM,_UK);}) : (++C,A2(_S0,_UM,_UK));});},_UN=new T(function(){return B(A3(_U8,_UB,0,_UI));}),_UO=function(_UP){while(1){var _UQ=(function(_UR){var _US=E(_UR);if(!_US._){return __Z;}else{var _UT=_US.b,_UU=E(_US.a);if(!E(_UU.b)._){return new T2(1,_UU.a,new T(function(){return _UO(_UT);}));}else{_UP=_UT;return __continue;}}})(_UP);if(_UQ!=__continue){return _UQ;}}},_UV=function(_UW){var _UX=_UO(_Ji(_UN,_UW));return (_UX._==0)?E(_Jf):(E(_UX.b)._==0)?E(_UX.a):E(_Jg);},_UY=function(_UZ,_V0){while(1){var _V1=E(_UZ);if(!_V1._){return E(_V0);}else{var _V2=new T2(1,_V1.a,_V0);_UZ=_V1.b;_V0=_V2;continue;}}},_V3=new T(function(){return _UY(__Z,__Z);}),_V4=new T(function(){return err(new T(function(){return unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string.");}));}),_V5=function(_V6,_V7,_V8,_V9,_Va){var _Vb=function(_Vc){return C > 19 ? new F(function(){return A3(_Va,_V3,_V7,new T(function(){var _Vd=E(E(_V7).b),_Ve=E(_Vc),_Vf=E(_Ve.a),_Vg=_H5(_Vf.a,_Vf.b,_Vf.c,_Ve.b,_Vd.a,_Vd.b,_Vd.c,__Z);return new T2(0,E(_Vg.a),_Vg.b);}));}) : (++C,A3(_Va,_V3,_V7,new T(function(){var _Vd=E(E(_V7).b),_Ve=E(_Vc),_Vf=E(_Ve.a),_Vg=_H5(_Vf.a,_Vf.b,_Vf.c,_Ve.b,_Vd.a,_Vd.b,_Vd.c,__Z);return new T2(0,E(_Vg.a),_Vg.b);})));},_Vh=function(_Vi,_Vj,_Vk){var _Vl=new T2(1,_Vj,_Vi),_Vm=new T(function(){return _UY(_Vl,__Z);}),_Vn=function(_Vo){return C > 19 ? new F(function(){return A3(_V8,_Vm,_Vk,new T(function(){var _Vp=E(E(_Vk).b),_Vq=E(_Vo),_Vr=E(_Vq.a),_Vs=_H5(_Vr.a,_Vr.b,_Vr.c,_Vq.b,_Vp.a,_Vp.b,_Vp.c,__Z);return new T2(0,E(_Vs.a),_Vs.b);}));}) : (++C,A3(_V8,_Vm,_Vk,new T(function(){var _Vp=E(E(_Vk).b),_Vq=E(_Vo),_Vr=E(_Vq.a),_Vs=_H5(_Vr.a,_Vr.b,_Vr.c,_Vq.b,_Vp.a,_Vp.b,_Vp.c,__Z);return new T2(0,E(_Vs.a),_Vs.b);})));},_Vt=new T(function(){var _Vu=E(_Vi);return function(_Vv,_Vw,_Vx){return C > 19 ? new F(function(){return _Vh(_Vl,_Vv,_Vw);}) : (++C,_Vh(_Vl,_Vv,_Vw));};});return C > 19 ? new F(function(){return A(_V6,[_Vk,_Vt,_V9,_V4,_Vn]);}) : (++C,A(_V6,[_Vk,_Vt,_V9,_V4,_Vn]));};return C > 19 ? new F(function(){return A(_V6,[_V7,function(_Vy,_Vz,_VA){return C > 19 ? new F(function(){return _Vh(__Z,_Vy,_Vz);}) : (++C,_Vh(__Z,_Vy,_Vz));},_V9,_V4,_Vb]);}) : (++C,A(_V6,[_V7,function(_Vy,_Vz,_VA){return C > 19 ? new F(function(){return _Vh(__Z,_Vy,_Vz);}) : (++C,_Vh(__Z,_Vy,_Vz));},_V9,_V4,_Vb]));},_VB=function(_VC,_VD){var _VE=E(_VC),_VF=E(_VE.a),_VG=E(_VD),_VH=E(_VG.a),_VI=_H5(_VF.a,_VF.b,_VF.c,_VE.b,_VH.a,_VH.b,_VH.c,_VG.b);return new T2(0,E(_VI.a),_VI.b);},_VJ=function(_VK,_VL,_VM,_VN,_VO,_VP){var _VQ=function(_VR,_VS,_VT,_VU,_VV){var _VW=function(_VX,_VY,_VZ){return C > 19 ? new F(function(){return A3(_VV,new T2(1,_VR,_VX),_VY,new T(function(){var _W0=E(E(_VY).b),_W1=E(_VZ),_W2=E(_W1.a),_W3=_H5(_W2.a,_W2.b,_W2.c,_W1.b,_W0.a,_W0.b,_W0.c,__Z);return new T2(0,E(_W3.a),_W3.b);}));}) : (++C,A3(_VV,new T2(1,_VR,_VX),_VY,new T(function(){var _W0=E(E(_VY).b),_W1=E(_VZ),_W2=E(_W1.a),_W3=_H5(_W2.a,_W2.b,_W2.c,_W1.b,_W0.a,_W0.b,_W0.c,__Z);return new T2(0,E(_W3.a),_W3.b);})));},_W4=function(_W5,_W6,_W7){return C > 19 ? new F(function(){return A3(_VT,new T2(1,_VR,_W5),_W6,new T(function(){var _W8=E(E(_W6).b),_W9=E(_W7),_Wa=E(_W9.a),_Wb=_H5(_Wa.a,_Wa.b,_Wa.c,_W9.b,_W8.a,_W8.b,_W8.c,__Z);return new T2(0,E(_Wb.a),_Wb.b);}));}) : (++C,A3(_VT,new T2(1,_VR,_W5),_W6,new T(function(){var _W8=E(E(_W6).b),_W9=E(_W7),_Wa=E(_W9.a),_Wb=_H5(_Wa.a,_Wa.b,_Wa.c,_W9.b,_W8.a,_W8.b,_W8.c,__Z);return new T2(0,E(_Wb.a),_Wb.b);})));};return C > 19 ? new F(function(){return _V5(_VK,_VS,_W4,_VU,_VW);}) : (++C,_V5(_VK,_VS,_W4,_VU,_VW));},_Wc=function(_Wd,_We,_Wf){var _Wg=function(_Wh,_Wi,_Wj){return C > 19 ? new F(function(){return A3(_VO,_Wh,_Wi,new T(function(){return _VB(_Wf,_Wj);}));}) : (++C,A3(_VO,_Wh,_Wi,new T(function(){return _VB(_Wf,_Wj);})));};return C > 19 ? new F(function(){return _VQ(_Wd,_We,_VM,_VN,_Wg);}) : (++C,_VQ(_Wd,_We,_VM,_VN,_Wg));},_Wk=function(_Wl,_Wm,_Wn){var _Wo=function(_Wp,_Wq,_Wr){return C > 19 ? new F(function(){return A3(_VM,_Wp,_Wq,new T(function(){return _VB(_Wn,_Wr);}));}) : (++C,A3(_VM,_Wp,_Wq,new T(function(){return _VB(_Wn,_Wr);})));};return C > 19 ? new F(function(){return _VQ(_Wl,_Wm,_VM,_VN,_Wo);}) : (++C,_VQ(_Wl,_Wm,_VM,_VN,_Wo));};return C > 19 ? new F(function(){return A(_VK,[_VL,_Wk,_VN,_Wc,_VP]);}) : (++C,A(_VK,[_VL,_Wk,_VN,_Wc,_VP]));},_Ws=function(_Wt,_Wu){var _Wv=function(_Ww){return _JY(_Ww,_Wu);},_Wx=function(_Wy,_Wz,_WA,_WB,_WC){var _WD=E(_Wy),_WE=E(_WD.b);return C > 19 ? new F(function(){return _HR(_Wt,_Wv,_WD.a,_WE.a,_WE.b,_WE.c,_WD.c,_Wz,_WC);}) : (++C,_HR(_Wt,_Wv,_WD.a,_WE.a,_WE.b,_WE.c,_WD.c,_Wz,_WC));},_WF=new T(function(){return _GJ(new T2(1,_Wu,__Z),_HO);});return function(_WG,_WH,_WI,_WJ,_WK){return C > 19 ? new F(function(){return _IH(_Wx,new T2(1,new T2(1,34,_WF),__Z),_WG,_WH,_WI,_WJ,_WK);}) : (++C,_IH(_Wx,new T2(1,new T2(1,34,_WF),__Z),_WG,_WH,_WI,_WJ,_WK));};},_WL=new T(function(){return _Ws(_FE,45);}),_WM=function(_WN,_WO,_WP,_WQ,_WR,_WS){var _WT=function(_WU,_WV,_WW){return C > 19 ? new F(function(){return A3(_WP,new T2(0,_WN,new T(function(){var _WX=_8v(E(_WU),8000);if(_WX>=0){return _WX;}else{return 8000-_WX|0;}})),_WV,new T(function(){var _WY=E(_WW),_WZ=E(_WY.a),_X0=E(E(_WV).b),_X1=_H5(_WZ.a,_WZ.b,_WZ.c,_WY.b,_X0.a,_X0.b,_X0.c,__Z);return new T2(0,E(_X1.a),_X1.b);}));}) : (++C,A3(_WP,new T2(0,_WN,new T(function(){var _WX=_8v(E(_WU),8000);if(_WX>=0){return _WX;}else{return 8000-_WX|0;}})),_WV,new T(function(){var _WY=E(_WW),_WZ=E(_WY.a),_X0=E(E(_WV).b),_X1=_H5(_WZ.a,_WZ.b,_WZ.c,_WY.b,_X0.a,_X0.b,_X0.c,__Z);return new T2(0,E(_X1.a),_X1.b);})));},_X2=function(_X3){var _X4=new T(function(){return  -_UV(_X3);});return function(_X5,_X6){return C > 19 ? new F(function(){return _WT(_X4,_X5,_X6);}) : (++C,_WT(_X4,_X5,_X6));};},_X7=function(_X8){var _X9=new T(function(){var _Xa=E(E(_WO).b),_Xb=E(_X8),_Xc=E(_Xb.a),_Xd=_H5(_Xc.a,_Xc.b,_Xc.c,_Xb.b,_Xa.a,_Xa.b,_Xa.c,__Z);return new T2(0,E(_Xd.a),_Xd.b);}),_Xe=function(_Xf){return C > 19 ? new F(function(){return A1(_WS,new T(function(){return _VB(_X9,_Xf);}));}) : (++C,A1(_WS,new T(function(){return _VB(_X9,_Xf);})));},_Xg=function(_Xh,_Xi,_Xj){return C > 19 ? new F(function(){return A3(_WR,new T2(0,_WN,new T(function(){var _Xk=_8v(_UV(_Xh),8000);if(_Xk>=0){return _Xk;}else{return 8000-_Xk|0;}})),_Xi,new T(function(){var _Xl=E(_X9),_Xm=E(_Xl.a),_Xn=E(_Xj),_Xo=E(_Xn.a),_Xp=_H5(_Xm.a,_Xm.b,_Xm.c,_Xl.b,_Xo.a,_Xo.b,_Xo.c,_Xn.b),_Xq=E(_Xp.a),_Xr=E(E(_Xi).b),_Xs=_H5(_Xq.a,_Xq.b,_Xq.c,_Xp.b,_Xr.a,_Xr.b,_Xr.c,__Z);return new T2(0,E(_Xs.a),_Xs.b);}));}) : (++C,A3(_WR,new T2(0,_WN,new T(function(){var _Xk=_8v(_UV(_Xh),8000);if(_Xk>=0){return _Xk;}else{return 8000-_Xk|0;}})),_Xi,new T(function(){var _Xl=E(_X9),_Xm=E(_Xl.a),_Xn=E(_Xj),_Xo=E(_Xn.a),_Xp=_H5(_Xm.a,_Xm.b,_Xm.c,_Xl.b,_Xo.a,_Xo.b,_Xo.c,_Xn.b),_Xq=E(_Xp.a),_Xr=E(E(_Xi).b),_Xs=_H5(_Xq.a,_Xq.b,_Xq.c,_Xp.b,_Xr.a,_Xr.b,_Xr.c,__Z);return new T2(0,E(_Xs.a),_Xs.b);})));},_Xt=function(_Xu){var _Xv=new T(function(){return _UV(_Xu);});return function(_X5,_X6){return C > 19 ? new F(function(){return _WT(_Xv,_X5,_X6);}) : (++C,_WT(_Xv,_X5,_X6));};};return C > 19 ? new F(function(){return _VJ(_J9,_WO,_Xt,_WQ,_Xg,_Xe);}) : (++C,_VJ(_J9,_WO,_Xt,_WQ,_Xg,_Xe));},_Xw=function(_Xx,_Xy,_Xz){var _XA=function(_XB){return C > 19 ? new F(function(){return A1(_WS,new T(function(){return _VB(_Xz,_XB);}));}) : (++C,A1(_WS,new T(function(){return _VB(_Xz,_XB);})));},_XC=function(_XD,_XE,_XF){return C > 19 ? new F(function(){return A3(_WR,new T2(0,_WN,new T(function(){var _XG=_8v( -_UV(_XD),8000);if(_XG>=0){return _XG;}else{return 8000-_XG|0;}})),_XE,new T(function(){var _XH=E(_Xz),_XI=E(_XH.a),_XJ=E(_XF),_XK=E(_XJ.a),_XL=_H5(_XI.a,_XI.b,_XI.c,_XH.b,_XK.a,_XK.b,_XK.c,_XJ.b),_XM=E(_XL.a),_XN=E(E(_XE).b),_XO=_H5(_XM.a,_XM.b,_XM.c,_XL.b,_XN.a,_XN.b,_XN.c,__Z);return new T2(0,E(_XO.a),_XO.b);}));}) : (++C,A3(_WR,new T2(0,_WN,new T(function(){var _XG=_8v( -_UV(_XD),8000);if(_XG>=0){return _XG;}else{return 8000-_XG|0;}})),_XE,new T(function(){var _XH=E(_Xz),_XI=E(_XH.a),_XJ=E(_XF),_XK=E(_XJ.a),_XL=_H5(_XI.a,_XI.b,_XI.c,_XH.b,_XK.a,_XK.b,_XK.c,_XJ.b),_XM=E(_XL.a),_XN=E(E(_XE).b),_XO=_H5(_XM.a,_XM.b,_XM.c,_XL.b,_XN.a,_XN.b,_XN.c,__Z);return new T2(0,E(_XO.a),_XO.b);})));},_XP=function(_XQ){var _XR=new T(function(){return  -_UV(_XQ);});return function(_X5,_X6){return C > 19 ? new F(function(){return _WT(_XR,_X5,_X6);}) : (++C,_WT(_XR,_X5,_X6));};};return C > 19 ? new F(function(){return _VJ(_J9,_Xy,_XP,_WQ,_XC,_XA);}) : (++C,_VJ(_J9,_Xy,_XP,_WQ,_XC,_XA));},_XS=function(_XT,_XU,_XV){var _XW=function(_XX){return C > 19 ? new F(function(){return A1(_WQ,new T(function(){return _VB(_XV,_XX);}));}) : (++C,A1(_WQ,new T(function(){return _VB(_XV,_XX);})));},_XY=function(_XZ,_Y0,_Y1){return C > 19 ? new F(function(){return _WT(new T(function(){return  -_UV(_XZ);},1),_Y0,new T(function(){var _Y2=E(_XV),_Y3=E(_Y2.a),_Y4=E(_Y1),_Y5=E(_Y4.a),_Y6=_H5(_Y3.a,_Y3.b,_Y3.c,_Y2.b,_Y5.a,_Y5.b,_Y5.c,_Y4.b);return new T2(0,E(_Y6.a),_Y6.b);},1));}) : (++C,_WT(new T(function(){return  -_UV(_XZ);},1),_Y0,new T(function(){var _Y2=E(_XV),_Y3=E(_Y2.a),_Y4=E(_Y1),_Y5=E(_Y4.a),_Y6=_H5(_Y3.a,_Y3.b,_Y3.c,_Y2.b,_Y5.a,_Y5.b,_Y5.c,_Y4.b);return new T2(0,E(_Y6.a),_Y6.b);},1)));};return C > 19 ? new F(function(){return _VJ(_J9,_XU,_X2,_WQ,_XY,_XW);}) : (++C,_VJ(_J9,_XU,_X2,_WQ,_XY,_XW));};return C > 19 ? new F(function(){return A(_WL,[_WO,_XS,_WQ,_Xw,_X7]);}) : (++C,A(_WL,[_WO,_XS,_WQ,_Xw,_X7]));},_Y7=new T(function(){return unCStr("@#$<");}),_Y8=function(_Y9){return _Ny(_K1,_Y9,_Y7);},_Ya=function(_Yb,_Yc,_Yd,_Ye,_Yf,_Yg,_Yh,_Yi,_Yj){var _Yk=function(_Yl){var _Ym=new T(function(){var _Yn=E(_Yl),_Yo=E(_Yn.a),_Yp=_H5(_Yo.a,_Yo.b,_Yo.c,_Yn.b,_Yc,_Yd,_Ye,__Z);return new T2(0,E(_Yp.a),_Yp.b);}),_Yq=function(_Yr){return C > 19 ? new F(function(){return A1(_Yj,new T(function(){return _VB(_Ym,_Yr);}));}) : (++C,A1(_Yj,new T(function(){return _VB(_Ym,_Yr);})));},_Ys=function(_Yt,_Yu,_Yv){return C > 19 ? new F(function(){return A3(_Yi,_Yt,_Yu,new T(function(){return _VB(_Ym,_Yv);}));}) : (++C,A3(_Yi,_Yt,_Yu,new T(function(){return _VB(_Ym,_Yv);})));};return C > 19 ? new F(function(){return _WM(36,new T3(0,_Yb,E(new T3(0,_Yc,_Yd,_Ye)),E(_Yf)),_Yg,_Yh,_Ys,_Yq);}) : (++C,_WM(36,new T3(0,_Yb,E(new T3(0,_Yc,_Yd,_Ye)),E(_Yf)),_Yg,_Yh,_Ys,_Yq));},_Yw=function(_Yx,_Yy,_Yz){var _YA=function(_YB){return C > 19 ? new F(function(){return A1(_Yh,new T(function(){return _VB(_Yz,_YB);}));}) : (++C,A1(_Yh,new T(function(){return _VB(_Yz,_YB);})));},_YC=function(_YD,_YE,_YF){return C > 19 ? new F(function(){return A3(_Yg,_YD,_YE,new T(function(){return _VB(_Yz,_YF);}));}) : (++C,A3(_Yg,_YD,_YE,new T(function(){return _VB(_Yz,_YF);})));};return C > 19 ? new F(function(){return _WM(_Yx,_Yy,_Yg,_Yh,_YC,_YA);}) : (++C,_WM(_Yx,_Yy,_Yg,_Yh,_YC,_YA));};return C > 19 ? new F(function(){return _HR(_FE,_Y8,_Yb,_Yc,_Yd,_Ye,_Yf,_Yw,_Yk);}) : (++C,_HR(_FE,_Y8,_Yb,_Yc,_Yd,_Ye,_Yf,_Yw,_Yk));},_YG=function(_YH,_YI,_YJ,_YK,_YL){var _YM=function(_YN){return C > 19 ? new F(function(){return A3(_YL,0,_YI,new T(function(){var _YO=E(E(_YI).b),_YP=E(_YN),_YQ=E(_YP.a),_YR=_H5(_YQ.a,_YQ.b,_YQ.c,_YP.b,_YO.a,_YO.b,_YO.c,__Z);return new T2(0,E(_YR.a),_YR.b);}));}) : (++C,A3(_YL,0,_YI,new T(function(){var _YO=E(E(_YI).b),_YP=E(_YN),_YQ=E(_YP.a),_YR=_H5(_YQ.a,_YQ.b,_YQ.c,_YP.b,_YO.a,_YO.b,_YO.c,__Z);return new T2(0,E(_YR.a),_YR.b);})));},_YS=function(_YT,_YU,_YV){return C > 19 ? new F(function(){return _YW(__Z,_YU);}) : (++C,_YW(__Z,_YU));},_YW=function(_YX,_YY){var _YZ=function(_Z0){return C > 19 ? new F(function(){return A3(_YJ,0,_YY,new T(function(){var _Z1=E(E(_YY).b),_Z2=E(_Z0),_Z3=E(_Z2.a),_Z4=_H5(_Z3.a,_Z3.b,_Z3.c,_Z2.b,_Z1.a,_Z1.b,_Z1.c,__Z);return new T2(0,E(_Z4.a),_Z4.b);}));}) : (++C,A3(_YJ,0,_YY,new T(function(){var _Z1=E(E(_YY).b),_Z2=E(_Z0),_Z3=E(_Z2.a),_Z4=_H5(_Z3.a,_Z3.b,_Z3.c,_Z2.b,_Z1.a,_Z1.b,_Z1.c,__Z);return new T2(0,E(_Z4.a),_Z4.b);})));};return C > 19 ? new F(function(){return A(_YH,[_YY,new T(function(){var _Z5=E(_YX);return _YS;}),_YK,_V4,_YZ]);}) : (++C,A(_YH,[_YY,new T(function(){var _Z5=E(_YX);return _YS;}),_YK,_V4,_YZ]));};return C > 19 ? new F(function(){return A(_YH,[_YI,function(_Z6,_Z7,_Z8){return C > 19 ? new F(function(){return _YW(__Z,_Z7);}) : (++C,_YW(__Z,_Z7));},_YK,_V4,_YM]);}) : (++C,A(_YH,[_YI,function(_Z6,_Z7,_Z8){return C > 19 ? new F(function(){return _YW(__Z,_Z7);}) : (++C,_YW(__Z,_Z7));},_YK,_V4,_YM]));},_Z9=function(_Za){var _Zb=_Za>>>0;if(_Zb>887){var _Zc=u_iswspace(_Za);return (E(_Zc)==0)?false:true;}else{return (_Zb==32)?true:(_Zb-9>>>0>4)?(_Zb==160)?true:false:true;}},_Zd=function(_Ze){return _Z9(E(_Ze));},_Zf=new T(function(){return unCStr("space");}),_Zg=function(_Zh,_Zi,_Zj,_Zk,_Zl,_Zm){return C > 19 ? new F(function(){return _IH(function(_Zn,_Zo,_Zp,_Zq,_Zr){var _Zs=E(_Zn),_Zt=E(_Zs.b);return C > 19 ? new F(function(){return _HR(_Zh,_Zd,_Zs.a,_Zt.a,_Zt.b,_Zt.c,_Zs.c,_Zo,_Zr);}) : (++C,_HR(_Zh,_Zd,_Zs.a,_Zt.a,_Zt.b,_Zt.c,_Zs.c,_Zo,_Zr));},new T2(1,_Zf,__Z),_Zi,_Zj,_Zk,_Zl,_Zm);}) : (++C,_IH(function(_Zn,_Zo,_Zp,_Zq,_Zr){var _Zs=E(_Zn),_Zt=E(_Zs.b);return C > 19 ? new F(function(){return _HR(_Zh,_Zd,_Zs.a,_Zt.a,_Zt.b,_Zt.c,_Zs.c,_Zo,_Zr);}) : (++C,_HR(_Zh,_Zd,_Zs.a,_Zt.a,_Zt.b,_Zt.c,_Zs.c,_Zo,_Zr));},new T2(1,_Zf,__Z),_Zi,_Zj,_Zk,_Zl,_Zm));},_Zu=new T(function(){return unCStr("white space");}),_Zv=function(_Zw,_Zx,_Zy,_Zz,_ZA,_ZB){var _ZC=function(_ZD,_ZE,_ZF,_ZG,_ZH){return C > 19 ? new F(function(){return _YG(function(_ZI,_ZJ,_ZK,_ZL,_ZM){return C > 19 ? new F(function(){return _Zg(_Zw,_ZI,_ZJ,_ZK,_ZL,_ZM);}) : (++C,_Zg(_Zw,_ZI,_ZJ,_ZK,_ZL,_ZM));},_ZD,_ZE,_ZF,_ZG);}) : (++C,_YG(function(_ZI,_ZJ,_ZK,_ZL,_ZM){return C > 19 ? new F(function(){return _Zg(_Zw,_ZI,_ZJ,_ZK,_ZL,_ZM);}) : (++C,_Zg(_Zw,_ZI,_ZJ,_ZK,_ZL,_ZM));},_ZD,_ZE,_ZF,_ZG));};return C > 19 ? new F(function(){return _IH(_ZC,new T2(1,_Zu,__Z),_Zx,_Zy,_Zz,_ZA,_ZB);}) : (++C,_IH(_ZC,new T2(1,_Zu,__Z),_Zx,_Zy,_Zz,_ZA,_ZB));},_ZN=function(_ZO,_ZP,_ZQ,_ZR,_ZS){var _ZT=function(_ZU,_ZV,_ZW){var _ZX=E(_ZV),_ZY=E(_ZX.b),_ZZ=function(_100){return C > 19 ? new F(function(){return A1(_ZS,new T(function(){return _VB(_ZW,_100);}));}) : (++C,A1(_ZS,new T(function(){return _VB(_ZW,_100);})));},_101=function(_102,_103,_104){return C > 19 ? new F(function(){return A3(_ZR,_102,_103,new T(function(){return _VB(_ZW,_104);}));}) : (++C,A3(_ZR,_102,_103,new T(function(){return _VB(_ZW,_104);})));};return C > 19 ? new F(function(){return _Ya(_ZX.a,_ZY.a,_ZY.b,_ZY.c,_ZX.c,_ZP,_ZQ,_101,_ZZ);}) : (++C,_Ya(_ZX.a,_ZY.a,_ZY.b,_ZY.c,_ZX.c,_ZP,_ZQ,_101,_ZZ));},_105=function(_106,_107,_108){var _109=E(_107),_10a=E(_109.b),_10b=function(_10c){return C > 19 ? new F(function(){return A1(_ZQ,new T(function(){return _VB(_108,_10c);}));}) : (++C,A1(_ZQ,new T(function(){return _VB(_108,_10c);})));},_10d=function(_10e,_10f,_10g){return C > 19 ? new F(function(){return A3(_ZP,_10e,_10f,new T(function(){return _VB(_108,_10g);}));}) : (++C,A3(_ZP,_10e,_10f,new T(function(){return _VB(_108,_10g);})));};return C > 19 ? new F(function(){return _Ya(_109.a,_10a.a,_10a.b,_10a.c,_109.c,_ZP,_ZQ,_10d,_10b);}) : (++C,_Ya(_109.a,_10a.a,_10a.b,_10a.c,_109.c,_ZP,_ZQ,_10d,_10b));};return C > 19 ? new F(function(){return _Zv(_FE,_ZO,_105,_ZQ,_ZT,_ZS);}) : (++C,_Zv(_FE,_ZO,_105,_ZQ,_ZT,_ZS));},_10h=function(_10i,_10j,_10k,_10l,_10m){var _10n=function(_10o){return C > 19 ? new F(function(){return A3(_10m,0,_10j,new T(function(){var _10p=E(E(_10j).b),_10q=E(_10o),_10r=E(_10q.a),_10s=_H5(_10r.a,_10r.b,_10r.c,_10q.b,_10p.a,_10p.b,_10p.c,__Z);return new T2(0,E(_10s.a),_10s.b);}));}) : (++C,A3(_10m,0,_10j,new T(function(){var _10p=E(E(_10j).b),_10q=E(_10o),_10r=E(_10q.a),_10s=_H5(_10r.a,_10r.b,_10r.c,_10q.b,_10p.a,_10p.b,_10p.c,__Z);return new T2(0,E(_10s.a),_10s.b);})));},_10t=function(_10u,_10v,_10w){return C > 19 ? new F(function(){return A3(_10m,0,_10v,new T(function(){var _10x=E(E(_10v).b),_10y=E(_10w),_10z=E(_10y.a),_10A=_H5(_10z.a,_10z.b,_10z.c,_10y.b,_10x.a,_10x.b,_10x.c,__Z);return new T2(0,E(_10A.a),_10A.b);}));}) : (++C,A3(_10m,0,_10v,new T(function(){var _10x=E(E(_10v).b),_10y=E(_10w),_10z=E(_10y.a),_10A=_H5(_10z.a,_10z.b,_10z.c,_10y.b,_10x.a,_10x.b,_10x.c,__Z);return new T2(0,E(_10A.a),_10A.b);})));},_10B=function(_10C,_10D,_10E){return C > 19 ? new F(function(){return A3(_10k,0,_10D,new T(function(){var _10F=E(E(_10D).b),_10G=E(_10E),_10H=E(_10G.a),_10I=_H5(_10H.a,_10H.b,_10H.c,_10G.b,_10F.a,_10F.b,_10F.c,__Z);return new T2(0,E(_10I.a),_10I.b);}));}) : (++C,A3(_10k,0,_10D,new T(function(){var _10F=E(E(_10D).b),_10G=E(_10E),_10H=E(_10G.a),_10I=_H5(_10H.a,_10H.b,_10H.c,_10G.b,_10F.a,_10F.b,_10F.c,__Z);return new T2(0,E(_10I.a),_10I.b);})));};return C > 19 ? new F(function(){return A(_10i,[_10j,_10B,_10l,_10t,_10n]);}) : (++C,A(_10i,[_10j,_10B,_10l,_10t,_10n]));},_10J=new T(function(){return _Ws(_FE,44);}),_10K=function(_10L,_10M,_10N,_10O){var _10P=function(_10Q,_10R,_10S){var _10T=function(_10U){return C > 19 ? new F(function(){return A1(_10O,new T(function(){return _VB(_10S,_10U);}));}) : (++C,A1(_10O,new T(function(){return _VB(_10S,_10U);})));},_10V=function(_10W,_10X,_10Y){return C > 19 ? new F(function(){return A3(_10N,_10W,_10X,new T(function(){return _VB(_10S,_10Y);}));}) : (++C,A3(_10N,_10W,_10X,new T(function(){return _VB(_10S,_10Y);})));};return C > 19 ? new F(function(){return A(_10J,[_10R,_10M,_10O,_10V,_10T]);}) : (++C,A(_10J,[_10R,_10M,_10O,_10V,_10T]));},_10Z=function(_110,_111,_112){var _113=function(_114){return C > 19 ? new F(function(){return A1(_10O,new T(function(){return _VB(_112,_114);}));}) : (++C,A1(_10O,new T(function(){return _VB(_112,_114);})));},_115=function(_116,_117,_118){return C > 19 ? new F(function(){return A3(_10M,_116,_117,new T(function(){return _VB(_112,_118);}));}) : (++C,A3(_10M,_116,_117,new T(function(){return _VB(_112,_118);})));};return C > 19 ? new F(function(){return A(_10J,[_111,_10M,_10O,_115,_113]);}) : (++C,A(_10J,[_111,_10M,_10O,_115,_113]));};return C > 19 ? new F(function(){return _Zv(_FE,_10L,_10Z,_10O,_10P,_10O);}) : (++C,_Zv(_FE,_10L,_10Z,_10O,_10P,_10O));},_119=function(_11a,_11b,_11c,_11d,_11e){return C > 19 ? new F(function(){return _10K(_11a,_11b,_11d,_11e);}) : (++C,_10K(_11a,_11b,_11d,_11e));},_11f=function(_11g,_11h,_11i,_11j,_11k){var _11l=function(_11m,_11n,_11o){var _11p=function(_11q){return C > 19 ? new F(function(){return A1(_11k,new T(function(){return _VB(_11o,_11q);}));}) : (++C,A1(_11k,new T(function(){return _VB(_11o,_11q);})));},_11r=function(_11s,_11t,_11u){return C > 19 ? new F(function(){return A3(_11j,_11s,_11t,new T(function(){return _VB(_11o,_11u);}));}) : (++C,A3(_11j,_11s,_11t,new T(function(){return _VB(_11o,_11u);})));};return C > 19 ? new F(function(){return _ZN(_11n,_11h,_11i,_11r,_11p);}) : (++C,_ZN(_11n,_11h,_11i,_11r,_11p));},_11v=function(_11w,_11x,_11y){var _11z=function(_11A){return C > 19 ? new F(function(){return A1(_11i,new T(function(){return _VB(_11y,_11A);}));}) : (++C,A1(_11i,new T(function(){return _VB(_11y,_11A);})));},_11B=function(_11C,_11D,_11E){return C > 19 ? new F(function(){return A3(_11h,_11C,_11D,new T(function(){return _VB(_11y,_11E);}));}) : (++C,A3(_11h,_11C,_11D,new T(function(){return _VB(_11y,_11E);})));};return C > 19 ? new F(function(){return _ZN(_11x,_11h,_11i,_11B,_11z);}) : (++C,_ZN(_11x,_11h,_11i,_11B,_11z));};return C > 19 ? new F(function(){return _10h(_119,_11g,_11v,_11i,_11l);}) : (++C,_10h(_119,_11g,_11v,_11i,_11l));},_11F=function(_11G){return E(E(_11G).b);},_11H=function(_11I,_11J,_11K,_11L,_11M){var _11N=function(_11O){return C > 19 ? new F(function(){return A3(_11L,0,_11K,new T(function(){var _11P=E(E(_11K).b),_11Q=E(_11O),_11R=E(_11Q.a),_11S=_H5(_11R.a,_11R.b,_11R.c,_11Q.b,_11P.a,_11P.b,_11P.c,__Z);return new T2(0,E(_11S.a),_11S.b);}));}) : (++C,A3(_11L,0,_11K,new T(function(){var _11P=E(E(_11K).b),_11Q=E(_11O),_11R=E(_11Q.a),_11S=_H5(_11R.a,_11R.b,_11R.c,_11Q.b,_11P.a,_11P.b,_11P.c,__Z);return new T2(0,E(_11S.a),_11S.b);})));},_11T=function(_11U,_11V,_11W){var _11X=new T(function(){var _11Y=E(E(_11K).b),_11Z=E(E(_11V).b),_120=E(_11W),_121=E(_120.a),_122=_H5(_121.a,_121.b,_121.c,_120.b,_11Z.a,_11Z.b,_11Z.c,new T2(1,new T(function(){return new T1(1,E(B(A2(_11F,_11I,_11U))));}),__Z)),_123=E(_122.a),_124=_H5(_123.a,_123.b,_123.c,_122.b,_11Y.a,_11Y.b,_11Y.c,__Z);return new T2(0,E(_124.a),_124.b);});return C > 19 ? new F(function(){return A3(_11L,0,_11K,_11X);}) : (++C,A3(_11L,0,_11K,_11X));},_125=function(_126,_127,_128){var _129=new T(function(){var _12a=E(E(_127).b),_12b=E(_128),_12c=E(_12b.a),_12d=_H5(_12c.a,_12c.b,_12c.c,_12b.b,_12a.a,_12a.b,_12a.c,new T2(1,new T(function(){return new T1(1,E(B(A2(_11F,_11I,_126))));}),__Z));return new T2(0,E(_12d.a),_12d.b);});return C > 19 ? new F(function(){return A1(_11M,_129);}) : (++C,A1(_11M,_129));};return C > 19 ? new F(function(){return A(_11J,[_11K,_125,_11N,_11T,_11N]);}) : (++C,A(_11J,[_11K,_125,_11N,_11T,_11N]));},_12e=function(_12f,_12g,_12h,_12i,_12j,_12k){var _12l=new T(function(){return B(A1(_12k,new T2(0,E(_12h),new T2(1,new T1(0,E(__Z)),__Z))));});return C > 19 ? new F(function(){return A3(_EY,_HM(_12f),new T(function(){return B(A2(_HP,_12f,_12g));}),function(_12m){var _12n=E(_12m);if(!_12n._){return E(_12l);}else{var _12o=E(_12n.a);return C > 19 ? new F(function(){return A3(_12j,_12o.a,new T3(0,_12o.b,E(_12h),E(_12i)),new T2(0,E(_12h),__Z));}) : (++C,A3(_12j,_12o.a,new T3(0,_12o.b,E(_12h),E(_12i)),new T2(0,E(_12h),__Z)));}});}) : (++C,A3(_EY,_HM(_12f),new T(function(){return B(A2(_HP,_12f,_12g));}),function(_12m){var _12n=E(_12m);if(!_12n._){return E(_12l);}else{var _12o=E(_12n.a);return C > 19 ? new F(function(){return A3(_12j,_12o.a,new T3(0,_12o.b,E(_12h),E(_12i)),new T2(0,E(_12h),__Z));}) : (++C,A3(_12j,_12o.a,new T3(0,_12o.b,E(_12h),E(_12i)),new T2(0,E(_12h),__Z)));}}));},_12p=function(_12q,_12r,_12s,_12t,_12u,_12v,_12w){var _12x=E(_12s);return C > 19 ? new F(function(){return _12e(_12q,_12x.a,_12x.b,_12x.c,_12t,_12w);}) : (++C,_12e(_12q,_12x.a,_12x.b,_12x.c,_12t,_12w));},_12y=new T(function(){return unCStr("end of input");}),_12z=function(_12A,_12B,_12C,_12D,_12E,_12F,_12G){var _12H=function(_12I,_12J,_12K,_12L,_12M){return C > 19 ? new F(function(){return _11H(_12B,function(_12N,_12O,_12P,_12Q,_12R){return C > 19 ? new F(function(){return _12p(_12A,_12B,_12N,_12O,_12P,_12Q,_12R);}) : (++C,_12p(_12A,_12B,_12N,_12O,_12P,_12Q,_12R));},_12I,_12L,_12M);}) : (++C,_11H(_12B,function(_12N,_12O,_12P,_12Q,_12R){return C > 19 ? new F(function(){return _12p(_12A,_12B,_12N,_12O,_12P,_12Q,_12R);}) : (++C,_12p(_12A,_12B,_12N,_12O,_12P,_12Q,_12R));},_12I,_12L,_12M));};return C > 19 ? new F(function(){return _IH(_12H,new T2(1,_12y,__Z),_12C,_12D,_12E,_12F,_12G);}) : (++C,_IH(_12H,new T2(1,_12y,__Z),_12C,_12D,_12E,_12F,_12G));},_12S=new T(function(){return unCStr("DAT");}),_12T=new T2(0,35,0),_12U=new T0(1),_12V=new T(function(){return unCStr("Failure in Data.Map.balanceR");}),_12W=new T(function(){var _12X=_;return err(_12V);}),_12Y=function(_12Z,_130,_131){var _132=E(_130);if(!_132._){var _133=_132.a,_134=E(_131);if(!_134._){var _135=_134.a,_136=_134.b;if(_135<=(imul(3,_133)|0)){return new T4(0,(1+_133|0)+_135|0,E(_12Z),_132,_134);}else{var _137=E(_134.c);if(!_137._){var _138=_137.a,_139=_137.b,_13a=_137.c,_13b=E(_134.d);if(!_13b._){var _13c=_13b.a;if(_138>=(imul(2,_13c)|0)){var _13d=function(_13e){var _13f=E(_12Z),_13g=E(_137.d);return (_13g._==0)?new T4(0,(1+_133|0)+_135|0,E(_139),E(new T4(0,(1+_133|0)+_13e|0,_13f,_132,E(_13a))),E(new T4(0,(1+_13c|0)+_13g.a|0,E(_136),_13g,_13b))):new T4(0,(1+_133|0)+_135|0,E(_139),E(new T4(0,(1+_133|0)+_13e|0,_13f,_132,E(_13a))),E(new T4(0,1+_13c|0,E(_136),E(_12U),_13b)));},_13h=E(_13a);if(!_13h._){return _13d(_13h.a);}else{return _13d(0);}}else{return new T4(0,(1+_133|0)+_135|0,E(_136),E(new T4(0,(1+_133|0)+_138|0,E(_12Z),_132,_137)),_13b);}}else{return E(_12W);}}else{return E(_12W);}}}else{return new T4(0,1+_133|0,E(_12Z),_132,E(_12U));}}else{var _13i=E(_131);if(!_13i._){var _13j=_13i.a,_13k=_13i.b,_13l=_13i.d,_13m=E(_13i.c);if(!_13m._){var _13n=_13m.a,_13o=_13m.b,_13p=_13m.c,_13q=E(_13l);if(!_13q._){var _13r=_13q.a;if(_13n>=(imul(2,_13r)|0)){var _13s=function(_13t){var _13u=E(_12Z),_13v=E(_13m.d);return (_13v._==0)?new T4(0,1+_13j|0,E(_13o),E(new T4(0,1+_13t|0,_13u,E(_12U),E(_13p))),E(new T4(0,(1+_13r|0)+_13v.a|0,E(_13k),_13v,_13q))):new T4(0,1+_13j|0,E(_13o),E(new T4(0,1+_13t|0,_13u,E(_12U),E(_13p))),E(new T4(0,1+_13r|0,E(_13k),E(_12U),_13q)));},_13w=E(_13p);if(!_13w._){return _13s(_13w.a);}else{return _13s(0);}}else{return new T4(0,1+_13j|0,E(_13k),E(new T4(0,1+_13n|0,E(_12Z),E(_12U),_13m)),_13q);}}else{return new T4(0,3,E(_13o),E(new T4(0,1,E(_12Z),E(_12U),E(_12U))),E(new T4(0,1,E(_13k),E(_12U),E(_12U))));}}else{var _13x=E(_13l);return (_13x._==0)?new T4(0,3,E(_13k),E(new T4(0,1,E(_12Z),E(_12U),E(_12U))),_13x):new T4(0,2,E(_12Z),E(_12U),_13i);}}else{return new T4(0,1,E(_12Z),E(_12U),E(_12U));}}},_13y=function(_13z){return new T4(0,1,E(_13z),E(_12U),E(_12U));},_13A=function(_13B,_13C){var _13D=E(_13C);if(!_13D._){return _12Y(_13D.b,_13D.c,_13A(_13B,_13D.d));}else{return _13y(_13B);}},_13E=new T(function(){return unCStr("Failure in Data.Map.balanceL");}),_13F=new T(function(){var _13G=_;return err(_13E);}),_13H=function(_13I,_13J,_13K){var _13L=E(_13K);if(!_13L._){var _13M=_13L.a,_13N=E(_13J);if(!_13N._){var _13O=_13N.a,_13P=_13N.b;if(_13O<=(imul(3,_13M)|0)){return new T4(0,(1+_13O|0)+_13M|0,E(_13I),_13N,_13L);}else{var _13Q=E(_13N.c);if(!_13Q._){var _13R=_13Q.a,_13S=E(_13N.d);if(!_13S._){var _13T=_13S.a,_13U=_13S.b,_13V=_13S.c;if(_13T>=(imul(2,_13R)|0)){var _13W=function(_13X){var _13Y=E(_13S.d);return (_13Y._==0)?new T4(0,(1+_13O|0)+_13M|0,E(_13U),E(new T4(0,(1+_13R|0)+_13X|0,E(_13P),_13Q,E(_13V))),E(new T4(0,(1+_13M|0)+_13Y.a|0,E(_13I),_13Y,_13L))):new T4(0,(1+_13O|0)+_13M|0,E(_13U),E(new T4(0,(1+_13R|0)+_13X|0,E(_13P),_13Q,E(_13V))),E(new T4(0,1+_13M|0,E(_13I),E(_12U),_13L)));},_13Z=E(_13V);if(!_13Z._){return _13W(_13Z.a);}else{return _13W(0);}}else{return new T4(0,(1+_13O|0)+_13M|0,E(_13P),_13Q,E(new T4(0,(1+_13M|0)+_13T|0,E(_13I),_13S,_13L)));}}else{return E(_13F);}}else{return E(_13F);}}}else{return new T4(0,1+_13M|0,E(_13I),E(_12U),_13L);}}else{var _140=E(_13J);if(!_140._){var _141=_140.a,_142=_140.b,_143=_140.d,_144=E(_140.c);if(!_144._){var _145=_144.a,_146=E(_143);if(!_146._){var _147=_146.a,_148=_146.b,_149=_146.c;if(_147>=(imul(2,_145)|0)){var _14a=function(_14b){var _14c=E(_146.d);return (_14c._==0)?new T4(0,1+_141|0,E(_148),E(new T4(0,(1+_145|0)+_14b|0,E(_142),_144,E(_149))),E(new T4(0,1+_14c.a|0,E(_13I),_14c,E(_12U)))):new T4(0,1+_141|0,E(_148),E(new T4(0,(1+_145|0)+_14b|0,E(_142),_144,E(_149))),E(new T4(0,1,E(_13I),E(_12U),E(_12U))));},_14d=E(_149);if(!_14d._){return _14a(_14d.a);}else{return _14a(0);}}else{return new T4(0,1+_141|0,E(_142),_144,E(new T4(0,1+_147|0,E(_13I),_146,E(_12U))));}}else{return new T4(0,3,E(_142),_144,E(new T4(0,1,E(_13I),E(_12U),E(_12U))));}}else{var _14e=E(_143);return (_14e._==0)?new T4(0,3,E(_14e.b),E(new T4(0,1,E(_142),E(_12U),E(_12U))),E(new T4(0,1,E(_13I),E(_12U),E(_12U)))):new T4(0,2,E(_13I),_140,E(_12U));}}else{return new T4(0,1,E(_13I),E(_12U),E(_12U));}}},_14f=function(_14g,_14h){var _14i=E(_14h);if(!_14i._){return _13H(_14i.b,_14f(_14g,_14i.c),_14i.d);}else{return _13y(_14g);}},_14j=function(_14k,_14l,_14m,_14n,_14o){return _12Y(_14m,_14n,_13A(_14k,_14o));},_14p=function(_14q,_14r,_14s,_14t,_14u){return _13H(_14s,_14f(_14q,_14t),_14u);},_14v=function(_14w,_14x,_14y,_14z,_14A,_14B){var _14C=E(_14x);if(!_14C._){var _14D=_14C.a,_14E=_14C.b,_14F=_14C.c,_14G=_14C.d;if((imul(3,_14D)|0)>=_14y){if((imul(3,_14y)|0)>=_14D){return new T4(0,(_14D+_14y|0)+1|0,E(_14w),_14C,E(new T4(0,_14y,E(_14z),E(_14A),E(_14B))));}else{return _12Y(_14E,_14F,B(_14v(_14w,_14G,_14y,_14z,_14A,_14B)));}}else{return _13H(_14z,B(_14H(_14w,_14D,_14E,_14F,_14G,_14A)),_14B);}}else{return _14p(_14w,_14y,_14z,_14A,_14B);}},_14H=function(_14I,_14J,_14K,_14L,_14M,_14N){var _14O=E(_14N);if(!_14O._){var _14P=_14O.a,_14Q=_14O.b,_14R=_14O.c,_14S=_14O.d;if((imul(3,_14J)|0)>=_14P){if((imul(3,_14P)|0)>=_14J){return new T4(0,(_14J+_14P|0)+1|0,E(_14I),E(new T4(0,_14J,E(_14K),E(_14L),E(_14M))),_14O);}else{return _12Y(_14K,_14L,B(_14v(_14I,_14M,_14P,_14Q,_14R,_14S)));}}else{return _13H(_14Q,B(_14H(_14I,_14J,_14K,_14L,_14M,_14R)),_14S);}}else{return _14j(_14I,_14J,_14K,_14L,_14M);}},_14T=function(_14U,_14V,_14W){var _14X=E(_14V);if(!_14X._){var _14Y=_14X.a,_14Z=_14X.b,_150=_14X.c,_151=_14X.d,_152=E(_14W);if(!_152._){var _153=_152.a,_154=_152.b,_155=_152.c,_156=_152.d;if((imul(3,_14Y)|0)>=_153){if((imul(3,_153)|0)>=_14Y){return new T4(0,(_14Y+_153|0)+1|0,E(_14U),_14X,_152);}else{return _12Y(_14Z,_150,B(_14v(_14U,_151,_153,_154,_155,_156)));}}else{return _13H(_154,B(_14H(_14U,_14Y,_14Z,_150,_151,_155)),_156);}}else{return _14j(_14U,_14Y,_14Z,_150,_151);}}else{return _14f(_14U,_14W);}},_157=function(_158,_159,_15a){var _15b=E(_158);if(_15b==1){var _15c=E(_15a);return (_15c._==0)?new T3(0,new T(function(){return new T4(0,1,E(_159),E(_12U),E(_12U));}),__Z,__Z):(_GS(_159,_15c.a)==0)?new T3(0,new T(function(){return new T4(0,1,E(_159),E(_12U),E(_12U));}),_15c,__Z):new T3(0,new T(function(){return new T4(0,1,E(_159),E(_12U),E(_12U));}),__Z,_15c);}else{var _15d=_157(_15b>>1,_159,_15a),_15e=_15d.a,_15f=_15d.c,_15g=E(_15d.b);if(!_15g._){return new T3(0,_15e,__Z,_15f);}else{var _15h=_15g.a,_15i=E(_15g.b);if(!_15i._){return new T3(0,new T(function(){return _13A(_15h,_15e);}),__Z,_15f);}else{var _15j=_15i.a;if(!_GS(_15h,_15j)){var _15k=_157(_15b>>1,_15j,_15i.b);return new T3(0,new T(function(){return B(_14T(_15h,_15e,_15k.a));}),_15k.b,_15k.c);}else{return new T3(0,_15e,__Z,_15g);}}}}},_15l=function(_15m,_15n){var _15o=E(_15m),_15p=E(_15n);if(!_15p._){var _15q=_15p.b,_15r=_15p.c,_15s=_15p.d;switch(_GS(_15o,_15q)){case 0:return _13H(_15q,_15l(_15o,_15r),_15s);case 1:return new T4(0,_15p.a,_15o,E(_15r),E(_15s));default:return _12Y(_15q,_15r,_15l(_15o,_15s));}}else{return new T4(0,1,_15o,E(_12U),E(_12U));}},_15t=function(_15u,_15v){while(1){var _15w=E(_15v);if(!_15w._){return E(_15u);}else{var _15x=_15l(_15w.a,_15u);_15u=_15x;_15v=_15w.b;continue;}}},_15y=function(_15z,_15A,_15B){return _15t(_15l(_15A,_15z),_15B);},_15C=function(_15D,_15E,_15F){while(1){var _15G=E(_15F);if(!_15G._){return E(_15E);}else{var _15H=_15G.a,_15I=E(_15G.b);if(!_15I._){return _13A(_15H,_15E);}else{var _15J=_15I.a;if(!_GS(_15H,_15J)){var _15K=_157(_15D,_15J,_15I.b),_15L=_15K.a,_15M=E(_15K.c);if(!_15M._){var _15N=_15D<<1,_15O=B(_14T(_15H,_15E,_15L));_15D=_15N;_15E=_15O;_15F=_15K.b;continue;}else{return _15y(B(_14T(_15H,_15E,_15L)),_15M.a,_15M.b);}}else{return _15y(_15E,_15H,_15I);}}}}},_15P=function(_15Q,_15R,_15S,_15T){var _15U=E(_15T);if(!_15U._){return _13A(_15S,_15R);}else{var _15V=_15U.a;if(!_GS(_15S,_15V)){var _15W=_157(_15Q,_15V,_15U.b),_15X=_15W.a,_15Y=E(_15W.c);if(!_15Y._){return C > 19 ? new F(function(){return _15C(_15Q<<1,B(_14T(_15S,_15R,_15X)),_15W.b);}) : (++C,_15C(_15Q<<1,B(_14T(_15S,_15R,_15X)),_15W.b));}else{return _15y(B(_14T(_15S,_15R,_15X)),_15Y.a,_15Y.b);}}else{return _15y(_15R,_15S,_15U);}}},_15Z=function(_160){var _161=E(_160);if(!_161._){return new T0(1);}else{var _162=_161.a,_163=E(_161.b);if(!_163._){return new T4(0,1,E(_162),E(_12U),E(_12U));}else{var _164=_163.a,_165=_163.b;if(!_GS(_162,_164)){return C > 19 ? new F(function(){return _15P(1,new T4(0,1,E(_162),E(_12U),E(_12U)),_164,_165);}) : (++C,_15P(1,new T4(0,1,E(_162),E(_12U),E(_12U)),_164,_165));}else{return _15y(new T4(0,1,E(_162),E(_12U),E(_12U)),_164,_165);}}}},_166=function(_167,_168){var _169=E(_168);if(!_169._){return new T2(0,__Z,__Z);}else{var _16a=_169.a;if(!B(A1(_167,_16a))){var _16b=new T(function(){var _16c=_166(_167,_169.b);return new T2(0,_16c.a,_16c.b);});return new T2(0,new T2(1,_16a,new T(function(){return E(E(_16b).a);})),new T(function(){return E(E(_16b).b);}));}else{return new T2(0,__Z,_169);}}},_16d=function(_16e,_16f){while(1){var _16g=E(_16f);if(!_16g._){return __Z;}else{if(!B(A1(_16e,_16g.a))){return _16g;}else{_16f=_16g.b;continue;}}}},_16h=function(_16i){var _16j=_16d(_Zd,_16i);if(!_16j._){return __Z;}else{var _16k=new T(function(){var _16l=_166(_Zd,_16j);return new T2(0,_16l.a,_16l.b);});return new T2(1,new T(function(){return E(E(_16k).a);}),new T(function(){return _16h(E(_16k).b);}));}},_16m=new T(function(){return _16h(new T(function(){return unCStr("JMP JMZ JMN DJZ DJN SPL");}));}),_16n=function(_16o,_16p,_16q){var _16r=function(_16s){var _16t=_16d(_Zd,_16s);if(!_16t._){return E(_16p);}else{var _16u=new T(function(){var _16v=_166(_Zd,_16t);return new T2(0,_16v.a,_16v.b);});return C > 19 ? new F(function(){return A2(_16o,new T(function(){return E(E(_16u).a);}),new T(function(){return B(_16r(E(_16u).b));}));}) : (++C,A2(_16o,new T(function(){return E(E(_16u).a);}),new T(function(){return B(_16r(E(_16u).b));})));}};return C > 19 ? new F(function(){return _16r(_16q);}) : (++C,_16r(_16q));},_16w=new T(function(){return B(_15Z(new T(function(){return B(_16n(function(_16x,_16y){return new T2(1,_16x,_16y);},_16m,new T(function(){return unCStr("MOV ADD SUB SEQ SNE DAT ");})));})));}),_16z=new T(function(){return B(_15Z(_16m));}),_16A=function(_16B,_16C,_16D,_16E,_16F,_16G){if(!_GZ(_16B,_16w)){var _16H=new T(function(){return new T2(0,E(E(_16C).b),new T2(1,new T(function(){return new T1(3,E(unAppCStr("unknown: ",_16B)));}),__Z));});return C > 19 ? new F(function(){return A1(_16G,_16H);}) : (++C,A1(_16G,_16H));}else{var _16I=new T(function(){return new T1(3,E(unAppCStr("needs 2 args: ",_16B)));}),_16J=function(_16K,_16L,_16M,_16N,_16O){return C > 19 ? new F(function(){return A1(_16O,new T(function(){return new T2(0,E(E(_16K).b),new T2(1,_16I,__Z));}));}) : (++C,A1(_16O,new T(function(){return new T2(0,E(E(_16K).b),new T2(1,_16I,__Z));})));},_16P=new T(function(){return _3R(_16B,_12S);}),_16Q=new T(function(){return _GZ(_16B,_16z);}),_16R=function(_16S,_16T,_16U,_16V,_16W,_16X){var _16Y=function(_16Z,_170,_171,_172,_173){return C > 19 ? new F(function(){return A3(_172,new T3(0,_16B,_12T,_16S),_16Z,new T(function(){return new T2(0,E(E(_16Z).b),__Z);}));}) : (++C,A3(_172,new T3(0,_16B,_12T,_16S),_16Z,new T(function(){return new T2(0,E(E(_16Z).b),__Z);})));},_174=function(_175,_176,_177,_178,_179){return C > 19 ? new F(function(){return A3(_178,new T3(0,_16B,_16S,_12T),_175,new T(function(){return new T2(0,E(E(_175).b),__Z);}));}) : (++C,A3(_178,new T3(0,_16B,_16S,_12T),_175,new T(function(){return new T2(0,E(E(_175).b),__Z);})));},_17a=function(_17b,_17c,_17d,_17e,_17f,_17g){var _17h=new T(function(){var _17i=E(_17b);if(!_17i._){if(!E(_16Q)){if(!E(_16P)){return _16J;}else{return _16Y;}}else{return _174;}}else{var _17j=function(_17k,_17l,_17m,_17n,_17o){return C > 19 ? new F(function(){return A3(_17n,new T3(0,_16B,_16S,_17i.a),_17k,new T(function(){return new T2(0,E(E(_17k).b),__Z);}));}) : (++C,A3(_17n,new T3(0,_16B,_16S,_17i.a),_17k,new T(function(){return new T2(0,E(E(_17k).b),__Z);})));};return _17j;}}),_17p=function(_17q,_17r,_17s,_17t,_17u){var _17v=function(_17w,_17x,_17y){var _17z=function(_17A){return C > 19 ? new F(function(){return A1(_17u,new T(function(){return _VB(_17y,_17A);}));}) : (++C,A1(_17u,new T(function(){return _VB(_17y,_17A);})));},_17B=function(_17C,_17D,_17E){return C > 19 ? new F(function(){return A3(_17t,_17C,_17D,new T(function(){return _VB(_17y,_17E);}));}) : (++C,A3(_17t,_17C,_17D,new T(function(){return _VB(_17y,_17E);})));};return C > 19 ? new F(function(){return A(_17h,[_17x,_17r,_17s,_17B,_17z]);}) : (++C,A(_17h,[_17x,_17r,_17s,_17B,_17z]));},_17F=function(_17G,_17H,_17I){var _17J=function(_17K){return C > 19 ? new F(function(){return A1(_17s,new T(function(){return _VB(_17I,_17K);}));}) : (++C,A1(_17s,new T(function(){return _VB(_17I,_17K);})));},_17L=function(_17M,_17N,_17O){return C > 19 ? new F(function(){return A3(_17r,_17M,_17N,new T(function(){return _VB(_17I,_17O);}));}) : (++C,A3(_17r,_17M,_17N,new T(function(){return _VB(_17I,_17O);})));};return C > 19 ? new F(function(){return A(_17h,[_17H,_17r,_17s,_17L,_17J]);}) : (++C,A(_17h,[_17H,_17r,_17s,_17L,_17J]));};return C > 19 ? new F(function(){return _12z(_FE,new T3(0,_GE,_GC,_GP),_17q,_17F,_17s,_17v,_17u);}) : (++C,_12z(_FE,new T3(0,_GE,_GC,_GP),_17q,_17F,_17s,_17v,_17u));},_17P=function(_17Q,_17R,_17S){var _17T=function(_17U){return C > 19 ? new F(function(){return A1(_17g,new T(function(){return _VB(_17S,_17U);}));}) : (++C,A1(_17g,new T(function(){return _VB(_17S,_17U);})));},_17V=function(_17W,_17X,_17Y){return C > 19 ? new F(function(){return A3(_17f,_17W,_17X,new T(function(){return _VB(_17S,_17Y);}));}) : (++C,A3(_17f,_17W,_17X,new T(function(){return _VB(_17S,_17Y);})));};return C > 19 ? new F(function(){return _17p(_17R,_17d,_17e,_17V,_17T);}) : (++C,_17p(_17R,_17d,_17e,_17V,_17T));},_17Z=function(_180,_181,_182){var _183=function(_184){return C > 19 ? new F(function(){return A1(_17e,new T(function(){return _VB(_182,_184);}));}) : (++C,A1(_17e,new T(function(){return _VB(_182,_184);})));},_185=function(_186,_187,_188){return C > 19 ? new F(function(){return A3(_17d,_186,_187,new T(function(){return _VB(_182,_188);}));}) : (++C,A3(_17d,_186,_187,new T(function(){return _VB(_182,_188);})));};return C > 19 ? new F(function(){return _17p(_181,_17d,_17e,_185,_183);}) : (++C,_17p(_181,_17d,_17e,_185,_183));};return C > 19 ? new F(function(){return _Zv(_FE,_17c,_17Z,_17e,_17P,_17g);}) : (++C,_Zv(_FE,_17c,_17Z,_17e,_17P,_17g));},_189=function(_18a,_18b,_18c){var _18d=function(_18e){return C > 19 ? new F(function(){return A1(_16X,new T(function(){return _VB(_18c,_18e);}));}) : (++C,A1(_16X,new T(function(){return _VB(_18c,_18e);})));},_18f=function(_18g,_18h,_18i){return C > 19 ? new F(function(){return A3(_16W,_18g,_18h,new T(function(){return _VB(_18c,_18i);}));}) : (++C,A3(_16W,_18g,_18h,new T(function(){return _VB(_18c,_18i);})));};return C > 19 ? new F(function(){return _17a(_18a,_18b,_16U,_16V,_18f,_18d);}) : (++C,_17a(_18a,_18b,_16U,_16V,_18f,_18d));},_18j=function(_18k,_18l,_18m){var _18n=function(_18o){return C > 19 ? new F(function(){return A1(_16V,new T(function(){return _VB(_18m,_18o);}));}) : (++C,A1(_16V,new T(function(){return _VB(_18m,_18o);})));},_18p=function(_18q,_18r,_18s){return C > 19 ? new F(function(){return A3(_16U,_18q,_18r,new T(function(){return _VB(_18m,_18s);}));}) : (++C,A3(_16U,_18q,_18r,new T(function(){return _VB(_18m,_18s);})));};return C > 19 ? new F(function(){return _17a(_18k,_18l,_16U,_16V,_18p,_18n);}) : (++C,_17a(_18k,_18l,_16U,_16V,_18p,_18n));};return C > 19 ? new F(function(){return _Hk(_11f,_16T,_18j,_16V,_189);}) : (++C,_Hk(_11f,_16T,_18j,_16V,_189));},_18t=function(_18u,_18v,_18w){var _18x=function(_18y){return C > 19 ? new F(function(){return A1(_16G,new T(function(){return _VB(_18w,_18y);}));}) : (++C,A1(_16G,new T(function(){return _VB(_18w,_18y);})));},_18z=function(_18A,_18B,_18C){return C > 19 ? new F(function(){return A3(_16F,_18A,_18B,new T(function(){return _VB(_18w,_18C);}));}) : (++C,A3(_16F,_18A,_18B,new T(function(){return _VB(_18w,_18C);})));};return C > 19 ? new F(function(){return _16R(_18u,_18v,_16D,_16E,_18z,_18x);}) : (++C,_16R(_18u,_18v,_16D,_16E,_18z,_18x));},_18D=function(_18E,_18F,_18G){var _18H=function(_18I){return C > 19 ? new F(function(){return A1(_16E,new T(function(){return _VB(_18G,_18I);}));}) : (++C,A1(_16E,new T(function(){return _VB(_18G,_18I);})));},_18J=function(_18K,_18L,_18M){return C > 19 ? new F(function(){return A3(_16D,_18K,_18L,new T(function(){return _VB(_18G,_18M);}));}) : (++C,A3(_16D,_18K,_18L,new T(function(){return _VB(_18G,_18M);})));};return C > 19 ? new F(function(){return _16R(_18E,_18F,_16D,_16E,_18J,_18H);}) : (++C,_16R(_18E,_18F,_16D,_16E,_18J,_18H));};return C > 19 ? new F(function(){return _ZN(_16C,_18D,_16E,_18t,_16G);}) : (++C,_ZN(_16C,_18D,_16E,_18t,_16G));}},_18N=function(_18O){var _18P=u_iswalpha(E(_18O));return (E(_18P)==0)?false:true;},_18Q=function(_18R,_18S,_18T,_18U,_18V){var _18W=E(_18R),_18X=E(_18W.b);return C > 19 ? new F(function(){return _HR(_FE,_18N,_18W.a,_18X.a,_18X.b,_18X.c,_18W.c,_18S,_18V);}) : (++C,_HR(_FE,_18N,_18W.a,_18X.a,_18X.b,_18X.c,_18W.c,_18S,_18V));},_18Y=new T(function(){return unCStr("letter");}),_18Z=function(_190,_191,_192,_193,_194){return C > 19 ? new F(function(){return _IH(_18Q,new T2(1,_18Y,__Z),_190,_191,_192,_193,_194);}) : (++C,_IH(_18Q,new T2(1,_18Y,__Z),_190,_191,_192,_193,_194));},_195=new T(function(){return unCStr("JMN");}),_196=new T(function(){return unCStr("JMG");}),_197=new T(function(){return unCStr("CMP");}),_198=new T(function(){return unCStr("SNE");}),_199=function(_19a){var _19b=u_towupper(E(_19a));if(_19b>>>0>1114111){return _NP(_19b);}else{return _19b;}},_19c=function(_19d){var _19e=_55(_199,_19d);return (!_3R(_19e,_197))?(!_3R(_19e,_196))?E(_19e):E(_195):E(_198);},_19f=function(_19g,_19h,_19i,_19j,_19k){var _19l=function(_19m,_19n,_19o){var _19p=function(_19q){return C > 19 ? new F(function(){return A1(_19k,new T(function(){return _VB(_19o,_19q);}));}) : (++C,A1(_19k,new T(function(){return _VB(_19o,_19q);})));},_19r=function(_19s,_19t,_19u){return C > 19 ? new F(function(){return A3(_19j,_19s,_19t,new T(function(){return _VB(_19o,_19u);}));}) : (++C,A3(_19j,_19s,_19t,new T(function(){return _VB(_19o,_19u);})));};return C > 19 ? new F(function(){return _16A(_19c(_19m),_19n,_19h,_19i,_19r,_19p);}) : (++C,_16A(_19c(_19m),_19n,_19h,_19i,_19r,_19p));},_19v=function(_19w,_19x,_19y){var _19z=function(_19A){return C > 19 ? new F(function(){return A1(_19i,new T(function(){return _VB(_19y,_19A);}));}) : (++C,A1(_19i,new T(function(){return _VB(_19y,_19A);})));},_19B=function(_19C,_19D,_19E){return C > 19 ? new F(function(){return A3(_19h,_19C,_19D,new T(function(){return _VB(_19y,_19E);}));}) : (++C,A3(_19h,_19C,_19D,new T(function(){return _VB(_19y,_19E);})));};return C > 19 ? new F(function(){return _16A(_19c(_19w),_19x,_19h,_19i,_19B,_19z);}) : (++C,_16A(_19c(_19w),_19x,_19h,_19i,_19B,_19z));};return C > 19 ? new F(function(){return _VJ(_18Z,_19g,_19v,_19i,_19l,_19k);}) : (++C,_VJ(_18Z,_19g,_19v,_19i,_19l,_19k));},_19F=function(_19G,_19H,_19I,_19J,_19K){var _19L=function(_19M,_19N,_19O){var _19P=function(_19Q){return C > 19 ? new F(function(){return A1(_19K,new T(function(){return _VB(_19O,_19Q);}));}) : (++C,A1(_19K,new T(function(){return _VB(_19O,_19Q);})));},_19R=function(_19S,_19T,_19U){return C > 19 ? new F(function(){return A3(_19J,_19S,_19T,new T(function(){return _VB(_19O,_19U);}));}) : (++C,A3(_19J,_19S,_19T,new T(function(){return _VB(_19O,_19U);})));};return C > 19 ? new F(function(){return _19f(_19N,_19H,_19I,_19R,_19P);}) : (++C,_19f(_19N,_19H,_19I,_19R,_19P));},_19V=function(_19W,_19X,_19Y){var _19Z=function(_1a0){return C > 19 ? new F(function(){return A1(_19I,new T(function(){return _VB(_19Y,_1a0);}));}) : (++C,A1(_19I,new T(function(){return _VB(_19Y,_1a0);})));},_1a1=function(_1a2,_1a3,_1a4){return C > 19 ? new F(function(){return A3(_19H,_1a2,_1a3,new T(function(){return _VB(_19Y,_1a4);}));}) : (++C,A3(_19H,_1a2,_1a3,new T(function(){return _VB(_19Y,_1a4);})));};return C > 19 ? new F(function(){return _19f(_19X,_19H,_19I,_1a1,_19Z);}) : (++C,_19f(_19X,_19H,_19I,_1a1,_19Z));};return C > 19 ? new F(function(){return _Zv(_FE,_19G,_19V,_19I,_19L,_19K);}) : (++C,_Zv(_FE,_19G,_19V,_19I,_19L,_19K));},_1a5=function(_1a6,_1a7,_1a8){return new T3(0,_1a6,E(_1a7),_1a8);},_1a9=function(_1aa,_1ab,_1ac){var _1ad=new T(function(){return _3o(_1aa);}),_1ae=new T(function(){return _3o(_1aa);}),_1af=function(_1ag){return C > 19 ? new F(function(){return A1(_1ae,new T(function(){return new T1(1,E(B(A1(_1ad,new T1(1,_1ag)))));}));}) : (++C,A1(_1ae,new T(function(){return new T1(1,E(B(A1(_1ad,new T1(1,_1ag)))));})));},_1ah=function(_1ai,_1aj,_1ak){var _1al=new T(function(){return new T1(1,E(B(A1(_1ad,new T(function(){return _1a5(_1ai,_1aj,_1ak);})))));});return C > 19 ? new F(function(){return A1(_1ae,_1al);}) : (++C,A1(_1ae,_1al));},_1am=function(_1an){return C > 19 ? new F(function(){return A1(_1ae,new T1(0,new T(function(){return B(A1(_1ad,new T1(1,_1an)));})));}) : (++C,A1(_1ae,new T1(0,new T(function(){return B(A1(_1ad,new T1(1,_1an)));}))));},_1ao=function(_1ap,_1aq,_1ar){var _1as=new T(function(){return B(A1(_1ad,new T(function(){return _1a5(_1ap,_1aq,_1ar);})));});return C > 19 ? new F(function(){return A1(_1ae,new T1(0,_1as));}) : (++C,A1(_1ae,new T1(0,_1as)));};return C > 19 ? new F(function(){return A(_1ab,[_1ac,_1ao,_1am,_1ah,_1af]);}) : (++C,A(_1ab,[_1ac,_1ao,_1am,_1ah,_1af]));},_1at=function(_1au,_1av,_1aw,_1ax,_1ay){var _1az=_HM(_1au),_1aA=function(_1aB){var _1aC=E(_1aB);if(!_1aC._){return C > 19 ? new F(function(){return A2(_3o,_1az,new T1(1,_1aC.a));}) : (++C,A2(_3o,_1az,new T1(1,_1aC.a)));}else{return C > 19 ? new F(function(){return A2(_3o,_1az,new T1(0,_1aC.a));}) : (++C,A2(_3o,_1az,new T1(0,_1aC.a)));}},_1aD=function(_1aE){return C > 19 ? new F(function(){return A3(_EY,_1az,new T(function(){var _1aF=E(_1aE);if(!_1aF._){return E(_1aF.a);}else{return E(_1aF.a);}}),_1aA);}) : (++C,A3(_EY,_1az,new T(function(){var _1aF=E(_1aE);if(!_1aF._){return E(_1aF.a);}else{return E(_1aF.a);}}),_1aA));},_1aG=new T(function(){return B(_1a9(_1az,_1av,new T(function(){return new T3(0,_1ay,E(new T3(0,_1ax,1,1)),E(_1aw));})));});return C > 19 ? new F(function(){return A3(_EY,_1az,_1aG,_1aD);}) : (++C,A3(_EY,_1az,_1aG,_1aD));},_1aH=new T1(1,__Z),_1aI=function(_1aJ){var _1aK=E(_1aJ);if(!_1aK._){return E(_1aH);}else{var _1aL=B(_1at(_FE,_19F,0,__Z,_1aK.a));if(!_1aL._){return new T1(0,_1aL.a);}else{var _1aM=_1aI(_1aK.b);return (_1aM._==0)?E(_1aM):new T1(1,new T2(1,_1aL.a,_1aM.a));}}},_1aN=function(_1aO){var _1aP=E(_1aO);if(!_1aP._){return E(_1aH);}else{var _1aQ=B(_1at(_FE,_19F,0,__Z,_1aP.a));if(!_1aQ._){return new T1(0,_1aQ.a);}else{var _1aR=_1aN(_1aP.b);return (_1aR._==0)?E(_1aR):new T1(1,new T2(1,_1aQ.a,_1aR.a));}}},_1aS=new T0(1),_1aT=new T(function(){return unCStr("Failure in Data.Map.balanceL");}),_1aU=new T(function(){var _1aV=_;return err(_1aT);}),_1aW=function(_1aX,_1aY,_1aZ,_1b0){var _1b1=E(_1b0);if(!_1b1._){var _1b2=_1b1.a,_1b3=E(_1aZ);if(!_1b3._){var _1b4=_1b3.a,_1b5=_1b3.b,_1b6=_1b3.c;if(_1b4<=(imul(3,_1b2)|0)){return new T5(0,(1+_1b4|0)+_1b2|0,E(_1aX),_1aY,_1b3,_1b1);}else{var _1b7=E(_1b3.d);if(!_1b7._){var _1b8=_1b7.a,_1b9=E(_1b3.e);if(!_1b9._){var _1ba=_1b9.a,_1bb=_1b9.b,_1bc=_1b9.c,_1bd=_1b9.d;if(_1ba>=(imul(2,_1b8)|0)){var _1be=function(_1bf){var _1bg=E(_1b9.e);return (_1bg._==0)?new T5(0,(1+_1b4|0)+_1b2|0,E(_1bb),_1bc,E(new T5(0,(1+_1b8|0)+_1bf|0,E(_1b5),_1b6,_1b7,E(_1bd))),E(new T5(0,(1+_1b2|0)+_1bg.a|0,E(_1aX),_1aY,_1bg,_1b1))):new T5(0,(1+_1b4|0)+_1b2|0,E(_1bb),_1bc,E(new T5(0,(1+_1b8|0)+_1bf|0,E(_1b5),_1b6,_1b7,E(_1bd))),E(new T5(0,1+_1b2|0,E(_1aX),_1aY,E(_1aS),_1b1)));},_1bh=E(_1bd);if(!_1bh._){return _1be(_1bh.a);}else{return _1be(0);}}else{return new T5(0,(1+_1b4|0)+_1b2|0,E(_1b5),_1b6,_1b7,E(new T5(0,(1+_1b2|0)+_1ba|0,E(_1aX),_1aY,_1b9,_1b1)));}}else{return E(_1aU);}}else{return E(_1aU);}}}else{return new T5(0,1+_1b2|0,E(_1aX),_1aY,E(_1aS),_1b1);}}else{var _1bi=E(_1aZ);if(!_1bi._){var _1bj=_1bi.a,_1bk=_1bi.b,_1bl=_1bi.c,_1bm=_1bi.e,_1bn=E(_1bi.d);if(!_1bn._){var _1bo=_1bn.a,_1bp=E(_1bm);if(!_1bp._){var _1bq=_1bp.a,_1br=_1bp.b,_1bs=_1bp.c,_1bt=_1bp.d;if(_1bq>=(imul(2,_1bo)|0)){var _1bu=function(_1bv){var _1bw=E(_1bp.e);return (_1bw._==0)?new T5(0,1+_1bj|0,E(_1br),_1bs,E(new T5(0,(1+_1bo|0)+_1bv|0,E(_1bk),_1bl,_1bn,E(_1bt))),E(new T5(0,1+_1bw.a|0,E(_1aX),_1aY,_1bw,E(_1aS)))):new T5(0,1+_1bj|0,E(_1br),_1bs,E(new T5(0,(1+_1bo|0)+_1bv|0,E(_1bk),_1bl,_1bn,E(_1bt))),E(new T5(0,1,E(_1aX),_1aY,E(_1aS),E(_1aS))));},_1bx=E(_1bt);if(!_1bx._){return _1bu(_1bx.a);}else{return _1bu(0);}}else{return new T5(0,1+_1bj|0,E(_1bk),_1bl,_1bn,E(new T5(0,1+_1bq|0,E(_1aX),_1aY,_1bp,E(_1aS))));}}else{return new T5(0,3,E(_1bk),_1bl,_1bn,E(new T5(0,1,E(_1aX),_1aY,E(_1aS),E(_1aS))));}}else{var _1by=E(_1bm);return (_1by._==0)?new T5(0,3,E(_1by.b),_1by.c,E(new T5(0,1,E(_1bk),_1bl,E(_1aS),E(_1aS))),E(new T5(0,1,E(_1aX),_1aY,E(_1aS),E(_1aS)))):new T5(0,2,E(_1aX),_1aY,_1bi,E(_1aS));}}else{return new T5(0,1,E(_1aX),_1aY,E(_1aS),E(_1aS));}}},_1bz=new T(function(){return unCStr("Failure in Data.Map.balanceR");}),_1bA=new T(function(){var _1bB=_;return err(_1bz);}),_1bC=function(_1bD,_1bE,_1bF,_1bG){var _1bH=E(_1bF);if(!_1bH._){var _1bI=_1bH.a,_1bJ=E(_1bG);if(!_1bJ._){var _1bK=_1bJ.a,_1bL=_1bJ.b,_1bM=_1bJ.c;if(_1bK<=(imul(3,_1bI)|0)){return new T5(0,(1+_1bI|0)+_1bK|0,E(_1bD),_1bE,_1bH,_1bJ);}else{var _1bN=E(_1bJ.d);if(!_1bN._){var _1bO=_1bN.a,_1bP=_1bN.b,_1bQ=_1bN.c,_1bR=_1bN.d,_1bS=E(_1bJ.e);if(!_1bS._){var _1bT=_1bS.a;if(_1bO>=(imul(2,_1bT)|0)){var _1bU=function(_1bV){var _1bW=E(_1bD),_1bX=E(_1bN.e);return (_1bX._==0)?new T5(0,(1+_1bI|0)+_1bK|0,E(_1bP),_1bQ,E(new T5(0,(1+_1bI|0)+_1bV|0,_1bW,_1bE,_1bH,E(_1bR))),E(new T5(0,(1+_1bT|0)+_1bX.a|0,E(_1bL),_1bM,_1bX,_1bS))):new T5(0,(1+_1bI|0)+_1bK|0,E(_1bP),_1bQ,E(new T5(0,(1+_1bI|0)+_1bV|0,_1bW,_1bE,_1bH,E(_1bR))),E(new T5(0,1+_1bT|0,E(_1bL),_1bM,E(_1aS),_1bS)));},_1bY=E(_1bR);if(!_1bY._){return _1bU(_1bY.a);}else{return _1bU(0);}}else{return new T5(0,(1+_1bI|0)+_1bK|0,E(_1bL),_1bM,E(new T5(0,(1+_1bI|0)+_1bO|0,E(_1bD),_1bE,_1bH,_1bN)),_1bS);}}else{return E(_1bA);}}else{return E(_1bA);}}}else{return new T5(0,1+_1bI|0,E(_1bD),_1bE,_1bH,E(_1aS));}}else{var _1bZ=E(_1bG);if(!_1bZ._){var _1c0=_1bZ.a,_1c1=_1bZ.b,_1c2=_1bZ.c,_1c3=_1bZ.e,_1c4=E(_1bZ.d);if(!_1c4._){var _1c5=_1c4.a,_1c6=_1c4.b,_1c7=_1c4.c,_1c8=_1c4.d,_1c9=E(_1c3);if(!_1c9._){var _1ca=_1c9.a;if(_1c5>=(imul(2,_1ca)|0)){var _1cb=function(_1cc){var _1cd=E(_1bD),_1ce=E(_1c4.e);return (_1ce._==0)?new T5(0,1+_1c0|0,E(_1c6),_1c7,E(new T5(0,1+_1cc|0,_1cd,_1bE,E(_1aS),E(_1c8))),E(new T5(0,(1+_1ca|0)+_1ce.a|0,E(_1c1),_1c2,_1ce,_1c9))):new T5(0,1+_1c0|0,E(_1c6),_1c7,E(new T5(0,1+_1cc|0,_1cd,_1bE,E(_1aS),E(_1c8))),E(new T5(0,1+_1ca|0,E(_1c1),_1c2,E(_1aS),_1c9)));},_1cf=E(_1c8);if(!_1cf._){return _1cb(_1cf.a);}else{return _1cb(0);}}else{return new T5(0,1+_1c0|0,E(_1c1),_1c2,E(new T5(0,1+_1c5|0,E(_1bD),_1bE,E(_1aS),_1c4)),_1c9);}}else{return new T5(0,3,E(_1c6),_1c7,E(new T5(0,1,E(_1bD),_1bE,E(_1aS),E(_1aS))),E(new T5(0,1,E(_1c1),_1c2,E(_1aS),E(_1aS))));}}else{var _1cg=E(_1c3);return (_1cg._==0)?new T5(0,3,E(_1c1),_1c2,E(new T5(0,1,E(_1bD),_1bE,E(_1aS),E(_1aS))),_1cg):new T5(0,2,E(_1bD),_1bE,E(_1aS),_1bZ);}}else{return new T5(0,1,E(_1bD),_1bE,E(_1aS),E(_1aS));}}},_1ch=function(_1ci,_1cj,_1ck){var _1cl=E(_1cj),_1cm=E(_1ck);if(!_1cm._){var _1cn=_1cm.c,_1co=_1cm.d,_1cp=_1cm.e,_1cq=E(_1cm.b);if(_1ci>=_1cq){if(_1ci!=_1cq){return _1bC(_1cq,_1cn,_1co,_1ch(_1ci,_1cl,_1cp));}else{return new T5(0,_1cm.a,E(_1ci),_1cl,E(_1co),E(_1cp));}}else{return _1aW(_1cq,_1cn,_1ch(_1ci,_1cl,_1co),_1cp);}}else{return new T5(0,1,E(_1ci),_1cl,E(_1aS),E(_1aS));}},_1cr=function(_1cs,_1ct,_1cu){return _1ch(E(_1cs),_1ct,_1cu);},_1cv=function(_1cw,_1cx){while(1){var _1cy=E(_1cw);if(!_1cy._){return E(_1cx);}else{var _1cz=E(_1cy.a),_1cA=B(_1cr(_1cz.a,_1cz.b,_1cx));_1cw=_1cy.b;_1cx=_1cA;continue;}}},_1cB=function(_1cC,_1cD){while(1){var _1cE=E(_1cC);if(!_1cE._){return E(_1cD);}else{var _1cF=E(_1cE.a),_1cG=B(_1cr(_1cF.a,_1cF.b,_1cD));_1cC=_1cE.b;_1cD=_1cG;continue;}}},_1cH=function(_1cI,_1cJ){while(1){var _1cK=E(_1cI);if(!_1cK._){return E(_1cJ);}else{var _1cL=E(_1cK.a),_1cM=B(_1cr(_1cL.a,_1cL.b,_1cJ));_1cI=_1cK.b;_1cJ=_1cM;continue;}}},_1cN=function(_1cO,_1cP){while(1){var _1cQ=E(_1cO);if(!_1cQ._){return E(_1cP);}else{var _1cR=E(_1cQ.a),_1cS=B(_1cr(_1cR.a,_1cR.b,_1cP));_1cO=_1cQ.b;_1cP=_1cS;continue;}}},_1cT=function(_1cU,_1cV){return new T5(0,1,E(_1cU),_1cV,E(_1aS),E(_1aS));},_1cW=function(_1cX,_1cY,_1cZ){var _1d0=E(_1cZ);if(!_1d0._){return _1bC(_1d0.b,_1d0.c,_1d0.d,_1cW(_1cX,_1cY,_1d0.e));}else{return _1cT(_1cX,_1cY);}},_1d1=function(_1d2,_1d3,_1d4){var _1d5=E(_1d4);if(!_1d5._){return _1aW(_1d5.b,_1d5.c,_1d1(_1d2,_1d3,_1d5.d),_1d5.e);}else{return _1cT(_1d2,_1d3);}},_1d6=function(_1d7,_1d8,_1d9,_1da,_1db,_1dc,_1dd){return _1aW(_1da,_1db,_1d1(_1d7,_1d8,_1dc),_1dd);},_1de=function(_1df,_1dg,_1dh,_1di,_1dj,_1dk,_1dl,_1dm){var _1dn=E(_1dh);if(!_1dn._){var _1do=_1dn.a,_1dp=_1dn.b,_1dq=_1dn.c,_1dr=_1dn.d,_1ds=_1dn.e;if((imul(3,_1do)|0)>=_1di){if((imul(3,_1di)|0)>=_1do){return new T5(0,(_1do+_1di|0)+1|0,E(_1df),_1dg,_1dn,E(new T5(0,_1di,E(_1dj),_1dk,E(_1dl),E(_1dm))));}else{return _1bC(_1dp,_1dq,_1dr,B(_1de(_1df,_1dg,_1ds,_1di,_1dj,_1dk,_1dl,_1dm)));}}else{return _1aW(_1dj,_1dk,B(_1dt(_1df,_1dg,_1do,_1dp,_1dq,_1dr,_1ds,_1dl)),_1dm);}}else{return _1d6(_1df,_1dg,_1di,_1dj,_1dk,_1dl,_1dm);}},_1dt=function(_1du,_1dv,_1dw,_1dx,_1dy,_1dz,_1dA,_1dB){var _1dC=E(_1dB);if(!_1dC._){var _1dD=_1dC.a,_1dE=_1dC.b,_1dF=_1dC.c,_1dG=_1dC.d,_1dH=_1dC.e;if((imul(3,_1dw)|0)>=_1dD){if((imul(3,_1dD)|0)>=_1dw){return new T5(0,(_1dw+_1dD|0)+1|0,E(_1du),_1dv,E(new T5(0,_1dw,E(_1dx),_1dy,E(_1dz),E(_1dA))),_1dC);}else{return _1bC(_1dx,_1dy,_1dz,B(_1de(_1du,_1dv,_1dA,_1dD,_1dE,_1dF,_1dG,_1dH)));}}else{return _1aW(_1dE,_1dF,B(_1dt(_1du,_1dv,_1dw,_1dx,_1dy,_1dz,_1dA,_1dG)),_1dH);}}else{return _1cW(_1du,_1dv,new T5(0,_1dw,E(_1dx),_1dy,E(_1dz),E(_1dA)));}},_1dI=function(_1dJ,_1dK,_1dL,_1dM){var _1dN=E(_1dL);if(!_1dN._){var _1dO=_1dN.a,_1dP=_1dN.b,_1dQ=_1dN.c,_1dR=_1dN.d,_1dS=_1dN.e,_1dT=E(_1dM);if(!_1dT._){var _1dU=_1dT.a,_1dV=_1dT.b,_1dW=_1dT.c,_1dX=_1dT.d,_1dY=_1dT.e;if((imul(3,_1dO)|0)>=_1dU){if((imul(3,_1dU)|0)>=_1dO){return new T5(0,(_1dO+_1dU|0)+1|0,E(_1dJ),_1dK,_1dN,_1dT);}else{return _1bC(_1dP,_1dQ,_1dR,B(_1de(_1dJ,_1dK,_1dS,_1dU,_1dV,_1dW,_1dX,_1dY)));}}else{return _1aW(_1dV,_1dW,B(_1dt(_1dJ,_1dK,_1dO,_1dP,_1dQ,_1dR,_1dS,_1dX)),_1dY);}}else{return _1cW(_1dJ,_1dK,_1dN);}}else{return _1d1(_1dJ,_1dK,_1dM);}},_1dZ=function(_1e0,_1e1,_1e2,_1e3){var _1e4=E(_1e0);if(_1e4==1){var _1e5=E(_1e3);return (_1e5._==0)?new T3(0,new T5(0,1,E(_1e1),E(_1e2),E(_1aS),E(_1aS)),__Z,__Z):(_1e1<E(E(_1e5.a).a))?new T3(0,new T5(0,1,E(_1e1),E(_1e2),E(_1aS),E(_1aS)),_1e5,__Z):new T3(0,new T5(0,1,E(_1e1),E(_1e2),E(_1aS),E(_1aS)),__Z,_1e5);}else{var _1e6=_1dZ(_1e4>>1,_1e1,_1e2,_1e3),_1e7=_1e6.a,_1e8=_1e6.c,_1e9=E(_1e6.b);if(!_1e9._){return new T3(0,_1e7,__Z,_1e8);}else{var _1ea=E(_1e9.a),_1eb=_1ea.a,_1ec=_1ea.b,_1ed=E(_1e9.b);if(!_1ed._){return new T3(0,new T(function(){return _1cW(_1eb,E(_1ec),_1e7);}),__Z,_1e8);}else{var _1ee=E(_1ed.a),_1ef=E(_1eb),_1eg=E(_1ee.a);if(_1ef<_1eg){var _1eh=_1dZ(_1e4>>1,_1eg,_1ee.b,_1ed.b);return new T3(0,new T(function(){return B(_1dI(_1ef,E(_1ec),_1e7,_1eh.a));}),_1eh.b,_1eh.c);}else{return new T3(0,_1e7,__Z,_1e9);}}}}},_1ei=function(_1ej,_1ek){while(1){var _1el=E(_1ek);if(!_1el._){return E(_1ej);}else{var _1em=E(_1el.a),_1en=_1ch(E(_1em.a),_1em.b,_1ej);_1ej=_1en;_1ek=_1el.b;continue;}}},_1eo=function(_1ep,_1eq,_1er,_1es){return _1ei(_1ch(_1eq,_1er,_1ep),_1es);},_1et=function(_1eu,_1ev,_1ew){var _1ex=E(_1ev);return _1ei(_1ch(E(_1ex.a),_1ex.b,_1eu),_1ew);},_1ey=function(_1ez,_1eA,_1eB){while(1){var _1eC=E(_1eB);if(!_1eC._){return E(_1eA);}else{var _1eD=E(_1eC.a),_1eE=_1eD.a,_1eF=_1eD.b,_1eG=E(_1eC.b);if(!_1eG._){return _1cW(_1eE,E(_1eF),_1eA);}else{var _1eH=E(_1eG.a),_1eI=E(_1eE),_1eJ=E(_1eH.a);if(_1eI<_1eJ){var _1eK=_1dZ(_1ez,_1eJ,_1eH.b,_1eG.b),_1eL=_1eK.a,_1eM=E(_1eK.c);if(!_1eM._){var _1eN=_1ez<<1,_1eO=B(_1dI(_1eI,E(_1eF),_1eA,_1eL));_1ez=_1eN;_1eA=_1eO;_1eB=_1eK.b;continue;}else{return _1et(B(_1dI(_1eI,E(_1eF),_1eA,_1eL)),_1eM.a,_1eM.b);}}else{return _1eo(_1eA,_1eI,_1eF,_1eG);}}}}},_1eP=function(_1eQ,_1eR,_1eS,_1eT,_1eU){var _1eV=E(_1eU);if(!_1eV._){return _1cW(_1eS,E(_1eT),_1eR);}else{var _1eW=E(_1eV.a),_1eX=E(_1eW.a);if(_1eS<_1eX){var _1eY=_1dZ(_1eQ,_1eX,_1eW.b,_1eV.b),_1eZ=_1eY.a,_1f0=E(_1eY.c);if(!_1f0._){return C > 19 ? new F(function(){return _1ey(_1eQ<<1,B(_1dI(_1eS,E(_1eT),_1eR,_1eZ)),_1eY.b);}) : (++C,_1ey(_1eQ<<1,B(_1dI(_1eS,E(_1eT),_1eR,_1eZ)),_1eY.b));}else{return _1et(B(_1dI(_1eS,E(_1eT),_1eR,_1eZ)),_1f0.a,_1f0.b);}}else{return _1eo(_1eR,_1eS,_1eT,_1eV);}}},_1f1=function(_1f2,_1f3){var _1f4=E(_1f3);return (_1f4._==0)?__Z:new T2(1,new T2(0,_1f2,_1f4.a),new T(function(){var _1f5=E(_1f2);if(_1f5==7999){return __Z;}else{return _1f1(_1f5+1|0,_1f4.b);}}));},_1f6=new T(function(){return new T2(1,new T3(0,_12S,_12T,_12T),_1f6);}),_1f7=new T(function(){return B((function(_1f8){var _1f9=E(_1f8);if(!_1f9._){return new T0(1);}else{var _1fa=E(_1f9.a),_1fb=_1fa.a,_1fc=_1fa.b,_1fd=E(_1f9.b);if(!_1fd._){return new T5(0,1,E(_1fb),E(_1fc),E(_1aS),E(_1aS));}else{var _1fe=_1fd.b,_1ff=E(_1fd.a),_1fg=_1ff.b,_1fh=E(_1fb),_1fi=E(_1ff.a);if(_1fh<_1fi){return C > 19 ? new F(function(){return _1eP(1,new T5(0,1,_1fh,E(_1fc),E(_1aS),E(_1aS)),_1fi,_1fg,_1fe);}) : (++C,_1eP(1,new T5(0,1,_1fh,E(_1fc),E(_1aS),E(_1aS)),_1fi,_1fg,_1fe));}else{return _1eo(new T5(0,1,_1fh,E(_1fc),E(_1aS),E(_1aS)),_1fi,_1fg,_1fe);}}}})(new T(function(){return _1f1(0,_1f6);})));}),_1fj=function(_1fk){return (E(_1fk)==10)?true:false;},_1fl=function(_1fm){var _1fn=E(_1fm);if(!_1fn._){return __Z;}else{var _1fo=new T(function(){var _1fp=_166(_1fj,_1fn);return new T2(0,_1fp.a,new T(function(){var _1fq=E(_1fp.b);if(!_1fq._){return __Z;}else{return _1fl(_1fq.b);}}));});return new T2(1,new T(function(){return E(E(_1fo).a);}),new T(function(){return E(E(_1fo).b);}));}},_1fr=new T(function(){return unCStr("JMZ");}),_1fs=new T(function(){return unCStr("JMP");}),_1ft=new T(function(){return unCStr("DJZ");}),_1fu=new T(function(){return unCStr("DJN");}),_1fv=new T(function(){return unCStr("ADD");}),_1fw=new T(function(){return B(_8s("redcode.lhs:(314,5)-(329,65)|function step"));}),_1fx=new T(function(){return unCStr("all programs halted");}),_1fy=new T(function(){return unCStr("match halted");}),_1fz=new T(function(){return unCStr("running programs");}),_1fA=new T2(1,new T2(0,0,new T1(1,0)),new T2(1,new T2(0,1,new T1(1,4000)),__Z)),_1fB=new T1(0,0),_1fC=new T(function(){return unCStr("value");}),_1fD=new T(function(){return unCStr("new match: 0 vs 1\n");}),_1fE=new T2(0,0,0),_1fF=function(_1fG,_){return _7o(new T2(1,_1fE,new T2(1,new T2(0,300,0),new T2(1,new T2(0,300,240),new T2(1,new T2(0,0,240),new T2(1,_1fE,__Z))))),_1fG,_);},_1fH=new T(function(){return _CA(new T3(0,0,0,0),function(_1fI,_){return _7g(_1fF,E(_1fI),_);});}),_1fJ=new T1(0,100),_1fK=new T(function(){return unCStr("Pattern match failure in do expression at redcode.lhs:297:3-13");}),_1fL=new T(function(){return B((function(_1fM){return C > 19 ? new F(function(){return _8s("redcode.lhs:(296,6)-(366,54)|lambda");}) : (++C,_8s("redcode.lhs:(296,6)-(366,54)|lambda"));})(_));}),_1fN=new T(function(){return unCStr("SPL");}),_1fO=new T(function(){return unCStr("SEQ");}),_1fP=new T(function(){return _3L(_Cp,0);}),_1fQ=new T(function(){return _3L(_Cp,1);}),_1fR=new T2(1,new T3(0,63,63,191),new T2(1,new T3(0,191,63,63),__Z)),_1fS=new T(function(){return _3L(_1fR,0);}),_1fT=new T(function(){return _3L(_1fR,1);}),_1fU=new T(function(){return unCStr("NOP");}),_1fV=new T(function(){return unCStr("\n");}),_1fW=new T(function(){var _1fX=_1fJ,_1fY=_1fB,_1fZ=E(_1fX);if(!_1fZ._){var _1g0=_1fZ.a,_1g1=E(_1fY);return (_1g1._==0)?_1g0==_1g1.a:(I_compareInt(_1g1.a,_1g0)==0)?true:false;}else{var _1g2=_1fZ.a,_1g3=E(_1fY);return (_1g3._==0)?(I_compareInt(_1g2,_1g3.a)==0)?true:false:(I_compare(_1g2,_1g3.a)==0)?true:false;}}),_1g4=function(_1g5){return err(unAppCStr("huh ",_1g5));},_1g6=new T(function(){return _8v(8000,8000);}),_1g7=new T(function(){return unCStr(" halted\n");}),_1g8=new T(function(){return unCStr("MOV");}),_1g9=function(_1ga){return E(E(_1ga).a);},_1gb=function(_1gc){return E(E(_1gc).b);},_1gd=function(_1ge){return E(E(_1ge).a);},_1gf=new T(function(){return _2X(function(_){return nMV(__Z);});}),_1gg=function(_1gh){return E(E(_1gh).b);},_1gi=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_1gj=function(_1gk,_1gl,_1gm,_1gn,_1go,_1gp){var _1gq=_1g9(_1gk),_1gr=_3m(_1gq),_1gs=new T(function(){return _EQ(_1gq);}),_1gt=new T(function(){return _3o(_1gr);}),_1gu=new T(function(){return B(A1(_1gl,_1gn));}),_1gv=new T(function(){return B(A2(_1gd,_1gm,_1go));}),_1gw=function(_1gx){return C > 19 ? new F(function(){return A1(_1gt,new T3(0,_1gv,_1gu,_1gx));}) : (++C,A1(_1gt,new T3(0,_1gv,_1gu,_1gx)));},_1gy=function(_1gz){var _1gA=new T(function(){var _1gB=new T(function(){var _1gC=__createJSFunc(2,function(_1gD,_){var _1gE=B(A2(E(_1gz),_1gD,_));return _30;}),_1gF=_1gC;return function(_){return _1gi(E(_1gu),E(_1gv),_1gF);};});return B(A1(_1gs,_1gB));});return C > 19 ? new F(function(){return A3(_EY,_1gr,_1gA,_1gw);}) : (++C,A3(_EY,_1gr,_1gA,_1gw));},_1gG=new T(function(){var _1gH=new T(function(){return _EQ(_1gq);}),_1gI=function(_1gJ){var _1gK=new T(function(){return B(A1(_1gH,function(_){var _=wMV(E(_1gf),new T1(1,_1gJ));return C > 19 ? new F(function(){return A(_1gb,[_1gm,_1go,_1gJ,_]);}) : (++C,A(_1gb,[_1gm,_1go,_1gJ,_]));}));});return C > 19 ? new F(function(){return A3(_EY,_1gr,_1gK,_1gp);}) : (++C,A3(_EY,_1gr,_1gK,_1gp));};return B(A2(_1gg,_1gk,_1gI));});return C > 19 ? new F(function(){return A3(_EY,_1gr,_1gG,_1gy);}) : (++C,A3(_EY,_1gr,_1gG,_1gy));},_1gL=function(_1gM,_1gN,_1gO){while(1){var _1gP=E(_1gN);if(!_1gP._){return E(_1gO);}else{var _1gQ=_1gP.a,_1gR=E(_1gM);if(_1gR==2147483647){return _1ch(2147483647,_1gQ,_1gO);}else{var _1gS=_1ch(_1gR,_1gQ,_1gO);_1gM=_1gR+1|0;_1gN=_1gP.b;_1gO=_1gS;continue;}}}},_1gT=(function(t,f){return mySetInterval(f,t);}),_1gU=(function(t,f){return mySetTimeout(f,t);}),_1gV=function(_1gW,_1gX,_1gY){var _1gZ=_1g9(_1gW),_1h0=new T(function(){return _EQ(_1gZ);}),_1h1=function(_1h2){var _1h3=function(_){var _1h4=E(_1gX);if(!_1h4._){var _1h5=B(A1(_1h2,0)),_1h6=__createJSFunc(0,function(_){var _1h7=B(A1(_1h5,_));return _30;}),_1h8=_1gU(_1h4.a,_1h6);return new T(function(){var _1h9=Number(_1h8),_1ha=jsTrunc(_1h9);return new T2(0,_1ha,_1h4);});}else{var _1hb=B(A1(_1h2,0)),_1hc=__createJSFunc(0,function(_){var _1hd=B(A1(_1hb,_));return _30;}),_1he=_1gT(_1h4.a,_1hc);return new T(function(){var _1hf=Number(_1he),_1hg=jsTrunc(_1hf);return new T2(0,_1hg,_1h4);});}};return C > 19 ? new F(function(){return A1(_1h0,_1h3);}) : (++C,A1(_1h0,_1h3));},_1hh=new T(function(){return B(A2(_1gg,_1gW,function(_1hi){return E(_1gY);}));});return C > 19 ? new F(function(){return A3(_EY,_3m(_1gZ),_1hh,_1h1);}) : (++C,A3(_EY,_3m(_1gZ),_1hh,_1h1));},_1hj=function(_1hk){var _1hl=E(_1hk);switch(_1hl._){case 0:return __Z;case 1:return new T2(1,_1hl.a,__Z);default:var _1hm=_1hl.a,_1hn=_1hl.c,_1ho=_1hl.d,_1hp=E(_1hl.b);switch(_1hp._){case 0:var _1hq=_1hp.a;return new T2(1,_1hq,new T(function(){var _1hr=_1hj(_1hn);if(!_1hr._){var _1hs=E(_1ho);switch(_1hs._){case 0:var _1ht=E(_1hq);if(!_1ht._){var _1hu=_1hm-_1ht.a|0;}else{var _1hu=_1hm-_1ht.a|0;}return new T1(1,_1hs.a);break;case 1:var _1hv=_1hs.a,_1hw=_1hs.b,_1hx=E(_1hq);if(!_1hx._){return new T4(2,_1hm-_1hx.a|0,E(new T1(0,_1hv)),__Z,E(new T1(0,_1hw)));}else{return new T4(2,_1hm-_1hx.a|0,E(new T1(0,_1hv)),__Z,E(new T1(0,_1hw)));}break;case 2:var _1hy=_1hs.a,_1hz=_1hs.b,_1hA=_1hs.c,_1hB=E(_1hq);if(!_1hB._){return new T4(2,_1hm-_1hB.a|0,E(new T2(1,_1hy,_1hz)),__Z,E(new T1(0,_1hA)));}else{return new T4(2,_1hm-_1hB.a|0,E(new T2(1,_1hy,_1hz)),__Z,E(new T1(0,_1hA)));}break;default:var _1hC=_1hs.a,_1hD=_1hs.b,_1hE=_1hs.c,_1hF=_1hs.d,_1hG=E(_1hq);if(!_1hG._){return new T4(2,_1hm-_1hG.a|0,E(new T2(1,_1hC,_1hD)),__Z,E(new T2(1,_1hE,_1hF)));}else{return new T4(2,_1hm-_1hG.a|0,E(new T2(1,_1hC,_1hD)),__Z,E(new T2(1,_1hE,_1hF)));}}}else{var _1hH=_1hr.a,_1hI=_1hr.b,_1hJ=E(_1hq);if(!_1hJ._){var _1hK=E(_1hH);if(!_1hK._){var _1hL=new T2(1,_1hK.b,_1hK.c);}else{var _1hL=new T3(2,_1hK.b,_1hK.c,_1hK.d);}return new T4(2,_1hm-_1hJ.a|0,E(_1hL),_1hI,E(_1ho));}else{var _1hM=E(_1hH);if(!_1hM._){var _1hN=new T2(1,_1hM.b,_1hM.c);}else{var _1hN=new T3(2,_1hM.b,_1hM.c,_1hM.d);}return new T4(2,_1hm-_1hJ.a|0,E(_1hN),_1hI,E(_1ho));}}}));case 1:var _1hO=_1hp.a,_1hP=_1hp.b;return new T2(1,_1hO,new T(function(){var _1hQ=E(_1hO);if(!_1hQ._){return new T4(2,_1hm-_1hQ.a|0,E(new T1(0,_1hP)),_1hn,E(_1ho));}else{return new T4(2,_1hm-_1hQ.a|0,E(new T1(0,_1hP)),_1hn,E(_1ho));}}));case 2:var _1hR=_1hp.a,_1hS=_1hp.b,_1hT=_1hp.c;return new T2(1,_1hR,new T(function(){var _1hU=E(_1hR);if(!_1hU._){return new T4(2,_1hm-_1hU.a|0,E(new T2(1,_1hS,_1hT)),_1hn,E(_1ho));}else{return new T4(2,_1hm-_1hU.a|0,E(new T2(1,_1hS,_1hT)),_1hn,E(_1ho));}}));default:var _1hV=_1hp.a,_1hW=_1hp.b,_1hX=_1hp.c,_1hY=_1hp.d;return new T2(1,_1hV,new T(function(){var _1hZ=E(_1hV);if(!_1hZ._){return new T4(2,_1hm-_1hZ.a|0,E(new T3(2,_1hW,_1hX,_1hY)),_1hn,E(_1ho));}else{return new T4(2,_1hm-_1hZ.a|0,E(new T3(2,_1hW,_1hX,_1hY)),_1hn,E(_1ho));}}));}}},_1i0=function(_1i1){var _1i2=E(_1i1);switch(_1i2._){case 0:return __Z;case 1:return new T2(1,_1i2.a,__Z);default:var _1i3=_1i2.a,_1i4=_1i2.c,_1i5=_1i2.d,_1i6=E(_1i2.b);switch(_1i6._){case 0:return new T2(1,_1i6.a,new T(function(){var _1i7=_1hj(_1i4);if(!_1i7._){var _1i8=E(_1i5);switch(_1i8._){case 0:return new T1(1,_1i8.a);break;case 1:return new T4(2,_1i3-1|0,E(new T1(0,_1i8.a)),__Z,E(new T1(0,_1i8.b)));break;case 2:return new T4(2,_1i3-1|0,E(new T2(1,_1i8.a,_1i8.b)),__Z,E(new T1(0,_1i8.c)));break;default:return new T4(2,_1i3-1|0,E(new T2(1,_1i8.a,_1i8.b)),__Z,E(new T2(1,_1i8.c,_1i8.d)));}}else{var _1i9=E(_1i7.a);if(!_1i9._){var _1ia=new T2(1,_1i9.b,_1i9.c);}else{var _1ia=new T3(2,_1i9.b,_1i9.c,_1i9.d);}return new T4(2,_1i3-1|0,E(_1ia),_1i7.b,E(_1i5));}}));case 1:return new T2(1,_1i6.a,new T4(2,_1i3-1|0,E(new T1(0,_1i6.b)),_1i4,E(_1i5)));case 2:return new T2(1,_1i6.a,new T4(2,_1i3-1|0,E(new T2(1,_1i6.b,_1i6.c)),_1i4,E(_1i5)));default:return new T2(1,_1i6.a,new T4(2,_1i3-1|0,E(new T3(2,_1i6.b,_1i6.c,_1i6.d)),_1i4,E(_1i5)));}}},_1ib=function(_1ic,_){var _1id=E(_1ic);if(!_1id._){return E(_1fL);}else{var _1ie=E(_1id.b);if(!_1ie._){return E(_1fL);}else{var _1if=E(_1ie.b);if(!_1if._){return E(_1fL);}else{var _1ig=E(_1if.b);if(!_1ig._){return E(_1fL);}else{var _1ih=_1ig.a,_1ii=E(_1ig.b);if(!_1ii._){return E(_1fL);}else{var _1ij=E(_1ii.b);if(!_1ij._){return E(_1fL);}else{if(!E(_1ij.b)._){var _1ik=B(A3(_ES,_1Y,_1id.a,_)),_1il=E(_1ik);if(!_1il._){return _1R(_1fK,_);}else{var _1im=_1il.a,_1in=newMVar(),_1io=_1in,_=putMVar(_1io,__Z),_1ip=new T(function(){return B(_Fc(_3q,_1Y,_1ih,_1fC));}),_1iq=function(_1ir,_){var _1is=_Cz(E(_1ih),toJSStr(E(_1fC)),toJSStr(E(_1ir)));return _3l(_);},_1it=function(_1iu,_1iv,_){var _1iw=new T(function(){if(_1iv<=0){if(_1iv>=0){var _1ix=quotRemI(_1iv,100);return new T2(0,_1ix.a,_1ix.b);}else{var _1iy=quotRemI(_1iv+1|0,100);return new T2(0,_1iy.a-1|0,(_1iy.b+100|0)-1|0);}}else{if(_1iv>=0){var _1iz=quotRemI(_1iv,100);return new T2(0,_1iz.a,_1iz.b);}else{var _1iA=quotRemI(_1iv+1|0,100);return new T2(0,_1iA.a-1|0,(_1iA.b+100|0)-1|0);}}}),_1iB=new T(function(){return E(E(_1iw).b)*3;}),_1iC=new T(function(){return E(_1iB)+3;}),_1iD=new T(function(){return E(E(_1iw).a)*3;}),_1iE=new T(function(){return E(_1iD)+3;}),_1iF=function(_1iG,_){return _7D(_1iB,_1iD,_1iC,_1iE,_1iG,_);};return C > 19 ? new F(function(){return A(_CA,[_1iu,function(_1iH,_){return _7g(_1iF,E(_1iH),_);},E(_1im).a,_]);}) : (++C,A(_CA,[_1iu,function(_1iH,_){return _7g(_1iF,E(_1iH),_);},E(_1im).a,_]));},_1iI=function(_1iJ,_1iK,_){var _1iL=new T(function(){var _1iM=E(_1iK);if(_1iM<=0){if(_1iM>=0){var _1iN=quotRemI(_1iM,100);return new T2(0,_1iN.a,_1iN.b);}else{var _1iO=quotRemI(_1iM+1|0,100);return new T2(0,_1iO.a-1|0,(_1iO.b+100|0)-1|0);}}else{if(_1iM>=0){var _1iP=quotRemI(_1iM,100);return new T2(0,_1iP.a,_1iP.b);}else{var _1iQ=quotRemI(_1iM+1|0,100);return new T2(0,_1iQ.a-1|0,(_1iQ.b+100|0)-1|0);}}}),_1iR=new T(function(){return E(E(_1iL).b)*3;}),_1iS=new T(function(){return E(_1iR)+3;}),_1iT=new T(function(){return E(E(_1iL).a)*3;}),_1iU=new T(function(){return E(_1iT)+3;}),_1iV=function(_1iW,_){return _7D(_1iR,_1iT,_1iS,_1iU,_1iW,_);};return C > 19 ? new F(function(){return A(_CA,[_1iJ,function(_1iX,_){return _7g(_1iV,E(_1iX),_);},E(_1im).a,_]);}) : (++C,A(_CA,[_1iJ,function(_1iX,_){return _7g(_1iV,E(_1iX),_);},E(_1im).a,_]));},_1iY=function(_){var _1iZ=E(_1im),_1j0=_1iZ.a,_1j1=_Cq(_1iZ.b),_1j2=B(A2(_1fH,_1j0,_)),_1j3=E(_1fC),_1j4=_Cz(E(_1ih),toJSStr(_1j3),toJSStr(E(_1fD))),_1j5=B(A(_Fc,[_3q,_1Y,_1ie.a,_1j3,_])),_1j6=_1aI(_1fl(_1j5));if(!_1j6._){var _1j7=_1j6.a;if(!0){var _1j8=(function(_){var _1j9=takeMVar(_1io),_=putMVar(_1io,__Z);return _1j9;})(),_1ja=B(A1(_1ip,_));return _1iq(_x(_1ja,new T(function(){var _1jb=E(_1j7),_1jc=E(_1jb.a);return _x(_70(_1jc.a,_1jc.b,_1jc.c,_1jb.b),_1fV);},1)),_);}else{var _1jd=takeMVar(_1io),_=putMVar(_1io,__Z),_1je=B(A1(_1ip,_));return _1iq(_x(_1je,new T(function(){var _1jf=E(_1j7),_1jg=E(_1jf.a);return _x(_70(_1jg.a,_1jg.b,_1jg.c,_1jf.b),_1fV);},1)),_);}}else{var _1jh=_1j6.a,_1ji=B(A(_Fc,[_3q,_1Y,_1if.a,_1j3,_])),_1jj=_1aN(_1fl(_1ji));if(!_1jj._){var _1jk=_1jj.a;if(!0){var _1jl=(function(_){var _1jm=takeMVar(_1io),_=putMVar(_1io,__Z);return _1jm;})(),_1jn=B(A1(_1ip,_));return _1iq(_x(_1jn,new T(function(){var _1jo=E(_1jk),_1jp=E(_1jo.a);return _x(_70(_1jp.a,_1jp.b,_1jp.c,_1jo.b),_1fV);},1)),_);}else{var _1jq=takeMVar(_1io),_=putMVar(_1io,__Z),_1jr=B(A1(_1ip,_));return _1iq(_x(_1jr,new T(function(){var _1js=E(_1jk),_1jt=E(_1js.a);return _x(_70(_1jt.a,_1jt.b,_1jt.c,_1js.b),_1fV);},1)),_);}}else{var _1ju=_1jj.a,_1jv=_7J(_1jh,0)-1|0,_1jw=function(_){var _1jx=function(_1jy,_1jz,_){var _1jA=new T(function(){if(!E(_1fW)){var _1jB=_CT(_1jz,_1fJ);return new T2(0,_1jB.a,_1jB.b);}else{return E(_Dr);}}),_1jC=new T(function(){return _Ds(E(_1jA).b)*3;}),_1jD=new T(function(){return E(_1jC)+3;}),_1jE=new T(function(){return _Ds(E(_1jA).a)*3;}),_1jF=new T(function(){return E(_1jE)+3;}),_1jG=function(_1jH,_){return _7D(_1jC,_1jE,_1jD,_1jF,_1jH,_);};return C > 19 ? new F(function(){return A(_CA,[_1jy,function(_1jI,_){return _7g(_1jG,E(_1jI),_);},_1j0,_]);}) : (++C,A(_CA,[_1jy,function(_1jI,_){return _7g(_1jG,E(_1jI),_);},_1j0,_]));},_1jJ=B(_1jx(_1fP,_1fB,_)),_1jK=(4000+_7J(_1ju,0)|0)-1|0,_1jL=function(_){var _1jM=B(_1jx(_1fQ,new T1(0,4000),_)),_1jN=new T(function(){return B(_1gL(4000,_1ju,B(_1gL(0,_1jh,_1f7))));});if(!0){var _1jO=(function(_){var _1jP=takeMVar(_1io),_=putMVar(_1io,new T1(1,new T2(0,_1jN,_1fA)));return _1jP;})(),_1jQ=B(A1(_1ip,_));return _1iq(_x(_1jQ,new T(function(){return _x(_1fz,_1fV);},1)),_);}else{var _1jR=takeMVar(_1io),_=putMVar(_1io,new T1(1,new T2(0,_1jN,_1fA))),_1jS=B(A1(_1ip,_));return _1iq(_x(_1jS,new T(function(){return _x(_1fz,_1fV);},1)),_);}};if(4000<=_1jK){var _1jT=function(_1jU,_){while(1){var _1jV=B(_1it(_1fT,_1jU,_));if(_1jU!=_1jK){var _1jW=_1jU+1|0;_1jU=_1jW;continue;}else{return 0;}}},_1jX=_1jT(4000,_);return _1jL(_);}else{return _1jL(_);}};if(0<=_1jv){var _1jY=function(_1jZ,_){while(1){var _1k0=B(_1it(_1fS,_1jZ,_));if(_1jZ!=_1jv){var _1k1=_1jZ+1|0;_1jZ=_1k1;continue;}else{return 0;}}},_1k2=_1jY(0,_);return C > 19 ? new F(function(){return _1jw(_);}) : (++C,_1jw(_));}else{return C > 19 ? new F(function(){return _1jw(_);}) : (++C,_1jw(_));}}}},_1k3=B(A(_1gj,[_3t,_3j,_3f,_1ii.a,0,function(_1k4,_){return C > 19 ? new F(function(){return _1iY(_);}) : (++C,_1iY(_));},_])),_1k5=function(_1k6,_){var _1k7=takeMVar(_1io);if(!E(_1k7)._){var _=putMVar(_1io,__Z);return 0;}else{var _1k8=B(A1(_1ip,_)),_1k9=_1iq(_x(_1k8,new T(function(){return _x(_1fy,_1fV);},1)),_),_=putMVar(_1io,__Z);return 0;}},_1ka=B(A(_1gj,[_3t,_3j,_3f,_1ij.a,0,_1k5,_])),_1kb=B(_1iY(_)),_1kc=function(_){var _1kd=function(_){var _1ke=takeMVar(_1io),_1kf=E(_1ke);if(!_1kf._){var _=putMVar(_1io,__Z);return 0;}else{var _1kg=E(_1kf.a),_1kh=_1kg.a,_1ki=E(_1kg.b);if(!_1ki._){var _=putMVar(_1io,__Z),_1kj=B(A1(_1ip,_));return _1iq(_x(_1kj,new T(function(){return _x(_1fx,_1fV);},1)),_);}else{var _1kk=_1ki.b,_1kl=E(_1ki.a),_1km=_1kl.a,_1kn=_1i0(_1kl.b);if(!_1kn._){return E(_1fw);}else{var _1ko=_1kn.b,_1kp=E(_1kn.a),_1kq=_3v(_1kp,_1kh),_1kr=E(_1kq.b),_1ks=E(_1kq.c),_1kt=new T(function(){return _3L(_1fR,E(_1km));});if(E(_1ks.a)==60){var _1ku=new T(function(){return _8z(_1kh,_1kp,36,_1ks.b);}),_1kv=new T(function(){var _1kw=_3v(E(_1ku),_1kh),_1kx=E(_1kw.c);return new T3(0,_1kw.a,_1kw.b,new T2(0,_1kx.a,new T(function(){return _8v((E(_1kx.b)+8000|0)-1|0,8000);})));}),_1ky=new T2(1,new T2(0,_1ku,_1kv),__Z);}else{var _1ky=__Z;}var _1kz=new T(function(){return _1cv(_1ky,_1kh);}),_1kA=new T(function(){if(E(_1kr.a)==60){var _1kB=new T(function(){return _8z(_1kz,_1kp,36,_1kr.b);}),_1kC=new T(function(){var _1kD=_3v(E(_1kB),_1kz),_1kE=E(_1kD.c);return new T3(0,_1kD.a,_1kD.b,new T2(0,_1kE.a,new T(function(){return _8v((E(_1kE.b)+8000|0)-1|0,8000);})));});return new T2(1,new T2(0,_1kB,_1kC),__Z);}else{return __Z;}}),_1kF=new T(function(){var _1kG=_1cB(_1kA,_1kz),_1kH=_3v(_1kp,_1kG),_1kI=_1kH.a,_1kJ=E(_1kH.b),_1kK=_1kJ.a,_1kL=_1kJ.b,_1kM=E(_1kH.c),_1kN=_1kM.a,_1kO=new T(function(){return _8z(_1kG,_1kp,E(_1kK),_1kL);}),_1kP=new T(function(){return _3v(E(_1kO),_1kG);}),_1kQ=new T(function(){return _8z(_1kG,_1kp,E(_1kN),_1kM.b);});if(!_3R(_1kI,_1fv)){if(!_3R(_1kI,_12S)){if(!_3R(_1kI,_1fu)){if(!_3R(_1kI,_1ft)){if(!_3R(_1kI,_195)){if(!_3R(_1kI,_1fs)){if(!_3R(_1kI,_1fr)){if(!_3R(_1kI,_1g8)){if(!_3R(_1kI,_1fU)){if(!_3R(_1kI,_1fO)){if(!_3R(_1kI,_198)){if(!_3R(_1kI,_1fN)){return _1g4(_1kI);}else{var _1kR=new T(function(){return _x(new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z),new T2(1,_1kO,__Z));});return new T2(0,__Z,_1kR);}}else{if(E(_1kK)==35){if(E(E(E(_1kP).b).b)==E(E(_3v(E(_1kQ),_1kG).c).b)){return new T2(0,__Z,new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}else{return new T2(0,__Z,new T2(1,new T(function(){return _8v(1+_8v(_1kp+1|0,8000)|0,8000);}),__Z));}}else{if(E(_1kN)==35){if(E(E(E(_1kP).c).b)==E(E(_3v(E(_1kQ),_1kG).c).b)){return new T2(0,__Z,new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}else{return new T2(0,__Z,new T2(1,new T(function(){return _8v(1+_8v(_1kp+1|0,8000)|0,8000);}),__Z));}}else{var _1kS=E(_1kP),_1kT=_3v(E(_1kQ),_1kG);if(!_3W(_1kS.a,_1kS.b,_1kS.c,_1kT.a,_1kT.b,_1kT.c)){return new T2(0,__Z,new T2(1,new T(function(){return _8v(1+_8v(_1kp+1|0,8000)|0,8000);}),__Z));}else{return new T2(0,__Z,new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}}}}}else{if(E(_1kK)==35){if(E(E(E(_1kP).b).b)!=E(E(_3v(E(_1kQ),_1kG).c).b)){return new T2(0,__Z,new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}else{return new T2(0,__Z,new T2(1,new T(function(){return _8v(1+_8v(_1kp+1|0,8000)|0,8000);}),__Z));}}else{if(E(_1kN)==35){if(E(E(E(_1kP).c).b)!=E(E(_3v(E(_1kQ),_1kG).c).b)){return new T2(0,__Z,new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}else{return new T2(0,__Z,new T2(1,new T(function(){return _8v(1+_8v(_1kp+1|0,8000)|0,8000);}),__Z));}}else{var _1kU=E(_1kP),_1kV=_3v(E(_1kQ),_1kG);if(!_3W(_1kU.a,_1kU.b,_1kU.c,_1kV.a,_1kV.b,_1kV.c)){return new T2(0,__Z,new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}else{return new T2(0,__Z,new T2(1,new T(function(){return _8v(1+_8v(_1kp+1|0,8000)|0,8000);}),__Z));}}}}}else{return new T2(0,__Z,new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}}else{if(E(_1kK)==35){var _1kW=new T(function(){var _1kX=_3v(E(_1kQ),_1kG);return new T3(0,_1kX.a,_1kX.b,new T2(0,E(_1kX.c).a,new T(function(){return E(E(E(_1kP).b).b);})));});return new T2(0,new T2(1,new T2(0,_1kQ,_1kW),__Z),new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}else{if(E(_1kN)==35){var _1kY=new T(function(){var _1kZ=_3v(E(_1kQ),_1kG);return new T3(0,_1kZ.a,_1kZ.b,new T2(0,E(_1kZ.c).a,new T(function(){return E(E(E(_1kP).c).b);})));});return new T2(0,new T2(1,new T2(0,_1kQ,_1kY),__Z),new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}else{return new T2(0,new T2(1,new T2(0,_1kQ,new T(function(){return _3A(_1kO,_1kG);})),__Z),new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}}}}else{if(!E(E(_3v(E(_1kQ),_1kG).c).b)){return new T2(0,__Z,new T2(1,_1kO,__Z));}else{return new T2(0,__Z,new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}}}else{return new T2(0,__Z,new T2(1,_1kO,__Z));}}else{if(!E(E(_3v(E(_1kQ),_1kG).c).b)){return new T2(0,__Z,new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}else{return new T2(0,__Z,new T2(1,_1kO,__Z));}}}else{var _1l0=E(_1kQ),_1l1=_3v(_1l0,_1kG),_1l2=_1l1.a,_1l3=_1l1.b,_1l4=E(_1l1.c),_1l5=_1l4.a,_1l6=E(_1l4.b);if(_1l6==1){return new T2(0,new T(function(){return _x(__Z,new T2(1,new T2(0,_1l0,new T3(0,_1l2,_1l3,new T2(0,_1l5,_1g6))),__Z));}),new T2(1,_1kO,__Z));}else{var _1l7=new T(function(){return _x(__Z,new T2(1,new T2(0,_1l0,new T3(0,_1l2,_1l3,new T2(0,_1l5,new T(function(){return _8v((_1l6+8000|0)-1|0,8000);})))),__Z));});return new T2(0,_1l7,new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}}}else{var _1l8=E(_1kQ),_1l9=_3v(_1l8,_1kG),_1la=_1l9.a,_1lb=_1l9.b,_1lc=E(_1l9.c),_1ld=_1lc.a,_1le=E(_1lc.b);if(_1le==1){return new T2(0,new T(function(){return _x(__Z,new T2(1,new T2(0,_1l8,new T3(0,_1la,_1lb,new T2(0,_1ld,_1g6))),__Z));}),new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}else{var _1lf=new T(function(){return _x(__Z,new T2(1,new T2(0,_1l8,new T3(0,_1la,_1lb,new T2(0,_1ld,new T(function(){return _8v((_1le+8000|0)-1|0,8000);})))),__Z));});return new T2(0,_1lf,new T2(1,_1kO,__Z));}}}else{return E(new T2(0,__Z,__Z));}}else{if(E(_1kK)==35){var _1lg=new T(function(){var _1lh=_3v(E(_1kQ),_1kG),_1li=E(_1lh.c);return new T3(0,_1lh.a,_1lh.b,new T2(0,_1li.a,new T(function(){return _8v(E(_1kL)+E(_1li.b)|0,8000);})));});return new T2(0,new T2(1,new T2(0,_1kQ,_1lg),__Z),new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}else{if(E(_1kN)==35){var _1lj=new T(function(){var _1lk=_3v(E(_1kQ),_1kG),_1ll=E(_1lk.c);return new T3(0,_1lk.a,_1lk.b,new T2(0,_1ll.a,new T(function(){return _8v(E(E(E(_1kP).c).b)+E(_1ll.b)|0,8000);})));});return new T2(0,new T2(1,new T2(0,_1kQ,_1lj),__Z),new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}else{var _1lm=new T(function(){var _1ln=_3v(E(_1kQ),_1kG),_1lo=E(_1ln.c),_1lp=E(_1ln.b);return new T3(0,_1ln.a,new T2(0,_1lp.a,new T(function(){return _8v(E(E(E(_1kP).b).b)+E(_1lp.b)|0,8000);})),new T2(0,_1lo.a,new T(function(){return _8v(E(E(E(_1kP).c).b)+E(_1lo.b)|0,8000);})));});return new T2(0,new T2(1,new T2(0,_1kQ,_1lm),__Z),new T2(1,new T(function(){return _8v(_1kp+1|0,8000);}),__Z));}}}}),_1lq=new T(function(){return _x(_1kA,new T(function(){return E(E(_1kF).a);},1));},1),_1lr=_x(_1ky,_1lq),_1ls=function(_1lt,_){while(1){var _1lu=(function(_1lv,_){var _1lw=E(_1lv);if(!_1lw._){return 0;}else{var _1lx=B(_1iI(_1kt,new T(function(){return E(E(_1lw.a).a);},1),_));_1lt=_1lw.b;return __continue;}})(_1lt,_);if(_1lu!=__continue){return _1lu;}}},_1ly=_1ls(_1lr,_),_1lz=B(_1it(_1kt,_1kp,_)),_1lA=E(_1ko);switch(_1lA._){case 0:var _1lB=_8F(32,E(_1kF).b);break;case 1:var _1lB=_8F(31,E(_1kF).b);break;default:var _1lC=32-_1lA.a|0;if(0>=_1lC){var _1lD=__Z;}else{var _1lD=_8F(_1lC,E(_1kF).b);}var _1lB=_1lD;}var _1lE=new T(function(){return _3L(_Cp,E(_1km));}),_1lF=function(_1lG,_){while(1){var _1lH=E(_1lG);if(!_1lH._){return 0;}else{var _1lI=B(_1iI(_1lE,_1lH.a,_));_1lG=_1lH.b;continue;}}},_1lJ=_1lF(_1lB,_),_1lK=_C2(_1ko,_Eu(_1lB));if(!_1i0(_1lK)._){var _1lL=B(A1(_1ip,_)),_1lM=new T(function(){return unAppCStr("program ",new T(function(){return _x(_2e(0,E(_1km),__Z),_1g7);}));},1),_1lN=_1iq(_x(_1lL,_1lM),_),_=putMVar(_1io,new T1(1,new T2(0,new T(function(){return _1cH(_1lr,_1kh);}),_1kk)));return 0;}else{var _=putMVar(_1io,new T1(1,new T2(0,new T(function(){return _1cN(_1lr,_1kh);}),new T(function(){return _x(_1kk,new T2(1,new T2(0,_1km,_1lK),__Z));}))));return 0;}}}}};return _76(64,_1kd,_);},_1lO=B(A(_1gV,[_3t,new T1(1,16),_1kc,_]));return 0;}}else{return E(_1fL);}}}}}}}},_1lP=function(_1lQ,_){var _1lR=E(_1lQ);if(!_1lR._){return __Z;}else{var _1lS=_1lP(_1lR.b,_);return new T2(1,_1lR.a,_1lS);}},_1lT=function(_1lU,_){var _1lV=__arr2lst(0,_1lU);return _1lP(_1lV,_);},_1lW=function(_1lX,_){return _1lT(E(_1lX),_);},_1lY=function(_1lZ,_){return _1lZ;},_1m0=function(_1m1,_1m2,_){var _1m3=__eq(_1m2,E(_30));if(!E(_1m3)){var _1m4=__isUndef(_1m2);if(!E(_1m4)){var _1m5=B(A3(_2L,_1m1,_1m2,_));return new T1(1,_1m5);}else{return __Z;}}else{return __Z;}},_1m6=(function(id){return document.getElementById(id);}),_1m7=new T(function(){return err(new T(function(){return unCStr("Maybe.fromJust: Nothing");}));}),_1m8=function(_1m9){var _1ma=E(_1m9);return (_1ma._==0)?E(_1m7):E(_1ma.a);},_1mb=function(_1mc,_1md){while(1){var _1me=(function(_1mf,_1mg){var _1mh=E(_1mf);if(!_1mh._){return __Z;}else{var _1mi=_1mh.b,_1mj=E(_1mg);if(!_1mj._){return __Z;}else{var _1mk=_1mj.b;if(!E(_1mj.a)._){return new T2(1,_1mh.a,new T(function(){return _1mb(_1mi,_1mk);}));}else{_1mc=_1mi;_1md=_1mk;return __continue;}}}})(_1mc,_1md);if(_1me!=__continue){return _1me;}}},_1ml=new T(function(){return unAppCStr("[]",__Z);}),_1mm=function(_1mn){var _1mo=E(_1mn);if(!_1mo._){return E(new T2(1,93,__Z));}else{var _1mp=new T(function(){return _x(fromJSStr(E(_1mo.a)),new T(function(){return _1mm(_1mo.b);},1));});return new T2(1,44,_1mp);}},_1mq=function(_1mr,_1ms){var _1mt=new T(function(){var _1mu=_1mb(_1mr,_1ms);if(!_1mu._){return E(_1ml);}else{var _1mv=new T(function(){return _x(fromJSStr(E(_1mu.a)),new T(function(){return _1mm(_1mu.b);},1));});return new T2(1,91,_1mv);}});return err(unAppCStr("Elements with the following IDs could not be found: ",_1mt));},_1mw=function(_1mx){while(1){var _1my=E(_1mx);if(!_1my._){return false;}else{if(!E(_1my.a)._){return true;}else{_1mx=_1my.b;continue;}}}},_1mz=function(_1mA,_1mB,_1mC){var _1mD=_3m(_1mA),_1mE=function(_1mF){if(!_1mw(_1mF)){return C > 19 ? new F(function(){return A1(_1mC,new T(function(){return _55(_1m8,_1mF);}));}) : (++C,A1(_1mC,new T(function(){return _55(_1m8,_1mF);})));}else{return _1mq(_1mB,_1mF);}},_1mG=new T(function(){var _1mH=new T(function(){return B(A2(_3o,_1mD,__Z));}),_1mI=function(_1mJ){var _1mK=E(_1mJ);if(!_1mK._){return E(_1mH);}else{var _1mL=new T(function(){return B(_1mI(_1mK.b));}),_1mM=function(_1mN){return C > 19 ? new F(function(){return A3(_EY,_1mD,_1mL,function(_1mO){return C > 19 ? new F(function(){return A2(_3o,_1mD,new T2(1,_1mN,_1mO));}) : (++C,A2(_3o,_1mD,new T2(1,_1mN,_1mO)));});}) : (++C,A3(_EY,_1mD,_1mL,function(_1mO){return C > 19 ? new F(function(){return A2(_3o,_1mD,new T2(1,_1mN,_1mO));}) : (++C,A2(_3o,_1mD,new T2(1,_1mN,_1mO)));}));},_1mP=new T(function(){return B(A2(_EQ,_1mA,function(_){var _1mQ=_1m6(E(_1mK.a));return _1m0(new T2(0,_1lY,_1lW),_1mQ,_);}));});return C > 19 ? new F(function(){return A3(_EY,_1mD,_1mP,_1mM);}) : (++C,A3(_EY,_1mD,_1mP,_1mM));}};return B(_1mI(_1mB));});return C > 19 ? new F(function(){return A3(_EY,_1mD,_1mG,_1mE);}) : (++C,A3(_EY,_1mD,_1mG,_1mE));},_1mR=new T(function(){return B(_1mz(_1Y,new T(function(){return _55(function(_1mS){return toJSStr(E(_1mS));},new T2(1,new T(function(){return unCStr("canvas");}),new T2(1,new T(function(){return unCStr("player1");}),new T2(1,new T(function(){return unCStr("player2");}),new T2(1,new T(function(){return unCStr("con");}),new T2(1,new T(function(){return unCStr("goB");}),new T2(1,new T(function(){return unCStr("stopB");}),__Z)))))));}),_1ib));});
var hasteMain = function() {B(A(_1mR, [0]));};window.onload = hasteMain;
